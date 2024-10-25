import sys

import z3

# 簡易ログ出力。
def info(s):
    print(s, file=sys.stderr)

# BitVec 変数の範囲制約を返す。
def bitvec_minmax(bv: z3.BitVecRef, min_, max_):
    return z3.And(z3.UGE(bv, min_), z3.ULE(bv, max_))

# 指定したファイルにバイト列全体を書き込む。
def fs_write(path, buf):
    open(path, "wb").write(buf)
