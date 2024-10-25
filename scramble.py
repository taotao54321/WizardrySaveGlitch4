# 原作の暗号化/復号関連。

import z3

# 原作の暗号化/復号処理におけるバイト変換。
#
# これは対称な変換である。つまり 2 回行うと元に戻る。
def scramble(b):
    return ~z3.RotateLeft(b, 4)
