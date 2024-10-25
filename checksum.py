# 原作のチェックサム関連。

import z3

# 1 つのチャンクに対するチェックサムを求める。
def calc_checksum(chunk):
    assert len(chunk) == 8

    cksum = z3.BitVecVal(8, 8)
    carry = z3.BoolVal(False)

    for b in chunk:
        cksum, carry = adc8(cksum, b, carry)

    return cksum

# 8bit キャリー付き加算 (6502 の adc と同じ)。
def adc8(lhs, rhs, carry):
    sum_ = z3.ZeroExt(1, lhs) + z3.ZeroExt(1, rhs)
    sum_ += z3.If(carry, z3.BitVecVal(1, 9), z3.BitVecVal(0, 9))

    sum_res = z3.Extract(7, 0, sum_)
    carry_res = z3.LShR(sum_, 8) != 0

    return sum_res, carry_res

# 冒険者構造体のチェックサム配列が正しいという制約を返す。
def checksums_is_ok(hero):
    cksums = hero[0x70:][:14]

    return z3.And([calc_checksum(hero[8 * i:][:8]) == cksums[i] for i in range(14)])
