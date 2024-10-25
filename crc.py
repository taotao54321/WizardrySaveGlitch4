# 原作の CRC 関連。

import z3

# 冒険者構造体の CRC を求める。
#
# 保持している CRC も含めて計算する。つまり、この結果が 0 ならば保持している CRC は正しい。
def calc_crc(hero):
    crc = ((z3.ZeroExt(8, hero[0]) << 8) | (z3.ZeroExt(8, hero[1]))) ^ 0xFFFF

    for b in hero[2:]:
        for _ in range(8):
            carry = z3.LShR(crc, 15) != 0
            crc = z3.If(carry, (crc << 1) ^ 0x1021, crc << 1)
        crc ^= z3.ZeroExt(8, b)

    return crc

# 冒険者構造体の CRC が正しいという制約を返す。
def crc_is_ok(hero):
    return calc_crc(hero) == 0
