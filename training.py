# 原作のキャラメイク関連。

import z3

from checksum import checksums_is_ok
from crc import crc_is_ok
from util import bitvec_minmax

# 新規冒険者に関する制約を返す (ボーナスポイント制約付き)。
def hero_is_ok(hero, bp):
    scenario_id   = hero[0x00]
    name_len      = hero[0x01]
    name          = hero[0x02:][:8]
    race          = hero[0x0A]
    clas          = hero[0x0B]
    alignment     = hero[0x0C]
    stats         = hero[0x0D:][:6]
    gold          = hero[0x13:][:6]
    xp            = hero[0x19:][:6]
    hp            = hero[0x1F:][:2]
    maxhp         = hero[0x21:][:2]
    xl            = hero[0x23:][:2]
    status        = hero[0x25]
    year          = hero[0x26]
    week          = hero[0x27]
    ac            = hero[0x28]
    mps           = hero[0x29:][:7 * 2]
    maxmps        = hero[0x37:][:7 * 2]
    spells        = hero[0x45:][:7]
    item_flags    = hero[0x4C:][:8]
    item_ids      = hero[0x54:][:8]
    item_count    = hero[0x5C]
    out_of_tavern = hero[0x5D]
    place_x       = hero[0x5E]
    place_y       = hero[0x5F]
    place_depth   = hero[0x60]
    poison        = hero[0x61]
    badges        = hero[0x62]
    unused        = hero[0x63:][:13]

    conds = []

    conds.append(scenario_id == 1)
    conds.append(name_is_ok(name_len, name))
    conds.append(build_is_ok(race, clas, alignment, stats, bp))
    conds.append(gold_is_ok(gold))
    conds.append(xp_is_ok(xp))
    conds.append(class_hp_is_ok(clas, hp, maxhp))
    conds.append(xl_is_ok(xl))
    conds.append(status == 0) # 状態: OK
    conds.append(age_is_ok(year, week))
    conds.append(ac == 10)
    conds.append(spell_info_is_ok(clas, stats, mps, maxmps, spells))
    conds.append(inventory_is_ok(item_flags, item_ids, item_count))
    conds.append(place_is_ok(out_of_tavern, place_x, place_y, place_depth))
    conds.append(poison == 0)
    conds.append(badges == 0)
    conds.append(z3.And([b == 0 for b in unused])) # 未使用領域はゼロクリアされている
    conds.append(checksums_is_ok(hero))
    conds.append(crc_is_ok(hero))

    return z3.And(conds)

# 冒険者の名前に関する制約を返す。
def name_is_ok(name_len, name):
    SPACE = 0x24

    conds = []

    # 名前長は 1..=8。
    conds.append(bitvec_minmax(name_len, 1, 8))

    # 名前内のバイトは、名前長の範囲内では正しいバイトでなければならず、
    # 範囲外は末尾まで空白文字でパディングされていなければならない。
    conds.append(z3.And([
        z3.If(z3.UGT(name_len, i), name_byte_is_ok(name[i]), name[i] == SPACE) for i in range(8)
    ]))

    return z3.And(conds)

# 冒険者の名前内のバイトに関する制約を返す。
def name_byte_is_ok(b):
    return z3.Or(
        z3.ULE(b, 0x24),
        b == 0x2A,
        b == 0x2B,
        b == 0x2D,
        b == 0x2E,
        b == 0x30,
        b == 0x31,
        b == 0x32,
        bitvec_minmax(b, 0x34, 0x63),
        bitvec_minmax(b, 0x65, 0x9F),
    )

# 新規冒険者のビルドに関する制約を返す (ボーナスポイント制約付き)。
def build_is_ok(race, clas, alignment, stats, bp):
    conds = []

    conds.append(race_is_ok(race))
    conds.append(class_is_ok(clas))
    conds.append(alignment_is_ok(alignment))

    conds.append(bonuspoint_is_ok(bp))

    conds.append(race_stats_is_ok(race, stats))
    conds.append(class_alignment_is_ok(clas, alignment))
    conds.append(class_stats_is_ok(clas, stats))
    conds.append(race_stats_bonuspoint_is_ok(race, stats, bp))

    return z3.And(conds)

# 原作内で出現しうるボーナスポイントに関する制約を返す。
def bonuspoint_is_ok(bp):
    return z3.Or(
        bitvec_minmax(bp,  5,  9),
        bitvec_minmax(bp, 15, 19),
        bp == 25,
        bp == 29,
    )

# 種族に関する制約を返す。
def race_is_ok(race):
    return z3.ULE(race, 4)

# キャラメイク時の職業に関する制約を返す。
# 君主および忍者にはなれないことに注意。
def class_is_ok(clas):
    return z3.ULE(clas, 5)

# 性格に関する制約を返す。
def alignment_is_ok(alignment):
    return z3.ULE(alignment, 2)

# キャラメイク時の職業と性格の組み合わせに関する制約を返す。
def class_alignment_is_ok(clas, alignment):
    return z3.If(clas == 0, z3.BoolVal(True),                      # 戦
           z3.If(clas == 1, z3.BoolVal(True),                      # 魔
           z3.If(clas == 2, z3.Or(alignment == 0, alignment == 2), # 僧
           z3.If(clas == 3, z3.Or(alignment == 1, alignment == 2), # 盗
           z3.If(clas == 4, z3.Or(alignment == 0, alignment == 2), # 司
           z3.If(clas == 5, z3.Or(alignment == 0, alignment == 1), # 侍
           z3.BoolVal(False)))))))

# キャラメイク時の種族と特性値の組み合わせに関する制約を返す。
def race_stats_is_ok(race, stats):
    # 種族の基本特性値を得る。
    stats_min = [race_stat(race, i) for i in range(6)]

    conds = []

    # 特性値上限は一律 18。
    conds.append(z3.And([z3.ULE(stat, 18) for stat in stats]))

    # 全ての特性値は種族の基本値以上でなければならない。
    conds.append(z3.And([z3.UGE(stats[i], stats_min[i]) for i in range(6)]))

    return z3.And(conds)

# 種族の基本特性値を返す。
def race_stat(race, stat_idx):
    def B(value):
        return z3.BitVecVal(value, 8)

    return [
        #            人                     エ                      ド                      ノ                      ホ
        z3.If(race == 0, B(8), z3.If(race == 1, B( 7), z3.If(race == 2, B(10), z3.If(race == 3, B( 7), z3.If(race == 4, B( 5), B(0)))))),
        z3.If(race == 0, B(8), z3.If(race == 1, B(10), z3.If(race == 2, B( 7), z3.If(race == 3, B( 7), z3.If(race == 4, B( 7), B(0)))))),
        z3.If(race == 0, B(5), z3.If(race == 1, B(10), z3.If(race == 2, B(10), z3.If(race == 3, B(10), z3.If(race == 4, B( 7), B(0)))))),
        z3.If(race == 0, B(8), z3.If(race == 1, B( 6), z3.If(race == 2, B(10), z3.If(race == 3, B( 8), z3.If(race == 4, B( 6), B(0)))))),
        z3.If(race == 0, B(8), z3.If(race == 1, B( 9), z3.If(race == 2, B( 5), z3.If(race == 3, B(10), z3.If(race == 4, B(10), B(0)))))),
        z3.If(race == 0, B(9), z3.If(race == 1, B( 6), z3.If(race == 2, B( 6), z3.If(race == 3, B( 7), z3.If(race == 4, B(15), B(0)))))),
    ][stat_idx]

# キャラメイク時の職業と特性値の組み合わせの制約を返す。
def class_stats_is_ok(clas, stats):
    return z3.If(clas == 0, z3.UGE(stats[0], 11),         # 戦
           z3.If(clas == 1, z3.UGE(stats[1], 11),         # 魔
           z3.If(clas == 2, z3.UGE(stats[2], 11),         # 僧
           z3.If(clas == 3, z3.UGE(stats[4], 11),         # 盗
           z3.If(clas == 4, z3.And(z3.UGE(stats[1], 12),  # 司
                                   z3.UGE(stats[2], 12)),
           z3.If(clas == 5, z3.And(z3.UGE(stats[0], 15),  # 侍
                                   z3.UGE(stats[1], 11),
                                   z3.UGE(stats[2], 10),
                                   z3.UGE(stats[3], 14),
                                   z3.UGE(stats[4], 10)),
           z3.BoolVal(False)))))))

# (種族, 特性値) に対するボーナスポイント配分の制約を返す。
def race_stats_bonuspoint_is_ok(race, stats, bp):
    # 種族の基本特性値を得る。
    stats_min = [race_stat(race, i) for i in range(6)]

    # ボーナスポイントをちょうど使い切っていなければならない。
    bp_consume = z3.BitVecVal(0, 8)
    for i in range(6):
        bp_consume += stats[i] - stats_min[i]

    return bp == bp_consume

# キャラメイク時の所持金に関する制約を返す。
def gold_is_ok(gold):
    # 金は 100..=199 でなければならない (12 桁 packed BCD, 上位桁が先)。
    conds = [b == 0 for b in gold[:4]]
    conds.append(gold[4] == 0x01)
    conds.append(is_packed_bcd(gold[5]))

    return z3.And(conds)

# キャラメイク時の経験値に関する制約を返す。
def xp_is_ok(xp):
    # 経験値は 0 でなければならない (12 桁 packed BCD, 上位桁が先)。
    return z3.And([b == 0 for b in xp])

# packed BCD バイトの制約を返す。
def is_packed_bcd(b):
    return z3.And(
        z3.ULE(b & 0x0F,      9),
        z3.ULE(z3.LShR(b, 4), 9),
    )

# キャラメイク時の (職業, HP) に関する制約を返す。
def class_hp_is_ok(clas, hp, maxhp):
    hp_hi    = hp[0]
    hp_lo    = hp[1]
    maxhp_hi = maxhp[0]
    maxhp_lo = maxhp[1]

    conds = []

    # HPの初期値の範囲は職業依存。
    conds.append(hp_hi == 0)
    conds.append(z3.If(clas == 0, bitvec_minmax(hp_lo,  8, 14), # 戦
                 z3.If(clas == 1, bitvec_minmax(hp_lo,  2,  6), # 魔
                 z3.If(clas == 2, bitvec_minmax(hp_lo,  6, 12), # 僧
                 z3.If(clas == 3, bitvec_minmax(hp_lo,  4,  8), # 盗
                 z3.If(clas == 4, bitvec_minmax(hp_lo,  4,  8), # 司
                 z3.If(clas == 5, bitvec_minmax(hp_lo, 12, 18), # 侍
                 z3.BoolVal(False))))))))

    # 現在HPと最大HPは等しい。
    conds.append(z3.And(
        hp_lo == maxhp_lo,
        hp_hi == maxhp_hi,
    ))

    return z3.And(conds)

# キャラメイク時のレベルに関する制約を返す。
def xl_is_ok(xl):
    xl_hi = xl[0]
    xl_lo = xl[1]

    # レベルは 1 固定。
    return z3.And(xl_hi == 0, xl_lo == 1)

# キャラメイク時の年齢に関する制約を返す。
def age_is_ok(year, week):
    # 年齢の初期値は 14..=16 年 24 週。
    return z3.And(
        bitvec_minmax(year, 14, 16),
        week == 24,
    )

# キャラメイク時の呪文能力に関する制約を返す。
def spell_info_is_ok(clas, stats, mps, maxmps, spells):
    iq = stats[1]
    piety = stats[2]
    mag_mps = mps[:7]
    pri_mps = mps[7:]
    mag_maxmps = maxmps[:7]
    pri_maxmps = maxmps[7:]

    conds = []

    # 呪文LV2以上は全て未習得かつMP 0。
    conds.append(z3.And(
        z3.And([value == 0 for value in mag_mps[1:]]),
        z3.And([value == 0 for value in pri_mps[1:]]),
        z3.And(
            spells[1] == 0,
            spells[4] == 0,
            spells[5] == 0,
            spells[6] == 0,
        ),
    ))

    # 初期習得呪文は職業と特性値に依存する。
    conds.append(z3.If(z3.Or(clas == 1, clas == 4), mag_bis_spell_info_is_ok(iq, mag_mps[0], pri_mps[0], spells),
                 z3.If(clas == 2,                   pri_spell_info_is_ok(piety, mag_mps[0], pri_mps[0], spells),
                                                    others_spell_info_is_ok(mag_mps[0], pri_mps[0], spells))))

    # 全ての最大MPは現在MPに等しい。
    conds.append(z3.And(
        z3.And([mag_mps[i] == mag_maxmps[i] for i in range(7)]),
        z3.And([pri_mps[i] == pri_maxmps[i] for i in range(7)]),
    ))

    return z3.And(conds)

# 魔/司の初期呪文能力に関する制約を返す。
def mag_bis_spell_info_is_ok(iq, mag1_mp, pri1_mp, spells):
    conds = []

    # 魔LV1呪文を (知恵)/6 個覚える (KATINO, HALITO, DUMAPIC の順)。
    # 知恵は 11 以上のはずなので、少なくとも 1 個は覚える。
    conds.append(z3.If(iq == 18,       z3.And(mag1_mp == 3, spells[0] == 0b1101),
                 z3.If(z3.UGE(iq, 12), z3.And(mag1_mp == 2, spells[0] == 0b0101),
                                       z3.And(mag1_mp == 1, spells[0] == 0b0100))))

    # 僧LV1呪文は覚えない。
    conds.append(z3.And(pri1_mp == 0, spells[2] == 0, spells[3] == 0))

    return z3.And(conds)

# 僧の初期呪文能力に関する制約を返す。
def pri_spell_info_is_ok(piety, mag1_mp, pri1_mp, spells):
    conds = []

    # 魔LV1呪文は覚えない。
    conds.append(z3.And(mag1_mp == 0, spells[0] == 0))

    # 僧LV1呪文を (信仰心)/6 個覚える (DIOS, KALKI, MILWA の順)。
    conds.append(z3.If(piety == 18,       z3.And(pri1_mp == 3, spells[2] == 0b01100000, spells[3] == 1),
                 z3.If(z3.UGE(piety, 12), z3.And(pri1_mp == 2, spells[2] == 0b01100000, spells[3] == 0),
                                          z3.And(pri1_mp == 1, spells[2] == 0b01000000, spells[3] == 0))))

    return z3.And(conds)

# 初期呪文能力のない職業 (魔/僧/司 以外) に関する制約を返す。
def others_spell_info_is_ok(mag1_mp, pri1_mp, spells):
    conds = []

    # 魔LV1呪文は覚えない。
    conds.append(z3.And(mag1_mp == 0, spells[0] == 0))

    # 僧LV1呪文は覚えない。
    conds.append(z3.And(pri1_mp == 0, spells[2] == 0, spells[3] == 0))

    return z3.And(conds)

# キャラメイク時のインベントリに関する制約を返す。
def inventory_is_ok(item_flags, item_ids, item_count):
    # インベントリは空。
    return z3.And(
        z3.And([item_flag == 0 for item_flag in item_flags]),
        z3.And([item_id == 0 for item_id in item_ids]),
        item_count == 0,
    )

# キャラメイク時の現在位置に関する制約を返す。
def place_is_ok(out_of_tavern, place_x, place_y, place_depth):
    # 酒場内におり、座標は (0, 0, 0) となっている。
    return z3.And(
        out_of_tavern == 0,
        place_x == 0,
        place_y == 0,
        place_depth == 0,
    )
