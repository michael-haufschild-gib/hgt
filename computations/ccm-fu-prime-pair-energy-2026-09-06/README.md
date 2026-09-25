# Prime-pair energy: numerical guidance

The frozen [research card](../../../5-failed/ccm-fu-prime-pair-energy.md) defines PE1 (successive energy decrease) and PE2 (every stage below the original energy). `screen.py` checks every cutoff 1..1024 and every increasing-prime stage in about 1.3 seconds. `stages.csv` retains every stage; `summary.json` records failures. No experimental value enters Lean.

- PE1 first fails at M=5 when prime 3 follows prime 2: energy rises from .00609689583812863 to .00706214354756525.
- PE2 first fails at M=198,p=43: energy 48.46632844675 exceeds original 48.39472170756, ratio 1.00147963944537.
- The largest stage/original ratio in the screen, excluding the trivial M=2 equality, is 4.10914953517 at M=903,p=223.

`audit.py` independently reconstructs channels from their defining half-order sums and each retained coefficient from its explicit squarefree smooth-factor expansion. At 70-digit precision it confirms the first two failures; exact output is in `direct-audit.json`. These finite values reject the proposed producers numerically, not SD1. The stronger all-scale late-prime obstruction and the unconditional first-prime contraction are independently proved in Lean on the linked card.
