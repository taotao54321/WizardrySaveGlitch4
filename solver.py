from dataclasses import dataclass

import z3

from checksum import checksums_is_ok
from crc import crc_is_ok
from scramble import scramble
import training
from util import info, bitvec_minmax

@dataclass
class SolverConfig:
    bonuspoint_max: int
    end_i: int
    end_j: int
    end_k: int

@dataclass
class Solution:
    bonuspoint: int
    hero: bytes
    fake: bytes

def solve(config: SolverConfig):
    solver = z3.Solver()

    bp = make_bonuspoint(solver, config.bonuspoint_max)
    hero = make_hero(solver, bp)

    fake = make_fake(solver, hero, config.end_i, config.end_j, config.end_k)

    solver_status = solver.check()
    info(f"status: {solver_status}")
    if solver_status != z3.sat:
        return None

    model = solver.model()

    sol_bonuspoint = model.eval(bp).as_long()
    sol_hero = bytes([model.eval(b).as_long() for b in hero])
    sol_fake = bytes([model.eval(b).as_long() for b in fake])

    return Solution(
        bonuspoint=sol_bonuspoint,
        hero=sol_hero,
        fake=sol_fake,
    )

# ボーナスポイントを表す変数を作る。
def make_bonuspoint(solver, bp_max):
    bp = z3.BitVec("bp", 8)

    solver.add(bp <= bp_max)

    return bp

# 元の平文を表す変数を作る。
def make_hero(solver, bp):
    hero = [z3.BitVec(f"hero{i}", 8) for i in range(0x80)]

    solver.add(training.hero_is_ok(hero, bp))

    # 名前はなるべく短くしたい。
    # また、ひらがなのみだと嬉しい。
    name_len = 7
    solver.add(z3.ULE(hero[0x01], name_len))
    solver.add(z3.And([bitvec_minmax(hero[i], 0x6E, 0x9F) for i in range(0x02, 0x02 + name_len)]))

    return hero

# 偽平文を表す変数を作る。
def make_fake(solver, hero, end_i, end_j, end_k):
    fake = [z3.BitVec(f"fake{i}", 8) for i in range(0x80)]

    conds = []

    # バックアップの末尾バイトは復号前に 0xEF で上書きされるので、
    # 偽平文のシナリオIDは常に 1 となる。
    # また、このことより偽平文の CRC 下位は元の平文のものと 0xEF から任意に選べる。
    conds.append(fake[0x00] == 1)
    conds.append(z3.Or(
        fake[0x7F] == hero[0x7F],
        fake[0x7F] == 0xEF,
    ))

    # 偽平文の構成。
    #
    # * 構成[1..i] は (P,C)
    # * 構成[i..j] は (C,P)
    # * 構成[j..k] は (P,C)
    # * 構成[k..]  は (P,P)
    for i in range(1, end_i):
        conds.append(fake[i]        == hero[i])
        conds.append(fake[0x7F - i] == scramble(hero[i]))
    for i in range(end_i, end_j):
        conds.append(fake[i]        == scramble(hero[0x7F - i]))
        conds.append(fake[0x7F - i] == hero[0x7F - i])
    for i in range(end_j, end_k):
        conds.append(fake[i]        == hero[i])
        conds.append(fake[0x7F - i] == scramble(hero[i]))
    for i in range(end_k, 0x40):
        conds.append(fake[i]        == hero[i])
        conds.append(fake[0x7F - i] == hero[0x7F - i])

    # 偽平文はアイテム個数が 0xFF であり、酒場内にいなければならない。
    conds.append(fake[0x5C] == 0xFF)
    conds.append((fake[0x5D] & 0x80) == 0)

    # 偽平文は名前などに魔除けのアイテムIDを含んでいてほしい。
    conds.append(z3.Or([fake[i] == 0x5E for i in range(0x02, 0x10)]))

    # 偽平文は正当なものでなければならない。
    conds.append(checksums_is_ok(fake))
    conds.append(crc_is_ok(fake))

    solver.add(z3.And(conds))

    return fake
