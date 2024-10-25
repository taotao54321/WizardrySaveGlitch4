# FC版 Wizardry #1 の save glitch の解を求める。

from solver import SolverConfig, solve
from util import fs_write

def main():
    config = SolverConfig(
        bonuspoint_max=5,
        end_i=0x09,
        end_j=0x10,
        end_k=0x24,
    )

    sol = solve(config)
    if sol is None:
        return

    print(f"{sol.bonuspoint}")

    fs_write("hero.bin", sol.hero)
    fs_write("fake.bin", sol.fake)

if __name__ == "__main__": main()
