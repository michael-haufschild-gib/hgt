# CCM-FU: contraction throughout the overlapping-label phase

- **Stage:** 5-failed
- **Type:** unconditional local monotonicity obstruction; exact positive survivor formalized
- **Parent:** [PE4 adaptive original-diagonal ceiling](../1-in-progress/ccm-fu-adaptive-prime-ceiling.md)
- **Scope:** this is not PE4 or PE4G and does not refute either ceiling candidate.

## Frozen claim and witness

The diagnostic asks whether every retained state with two distinct unprocessed primes p,q and p*q<M has some nonincreasing next prime merger. An unconditional Lean counterexample is M=11, processed primes P={3,7}. Only 2 and 5 remain, the {2,5} coefficient is the positive actual channel C_10(11), and both next energies strictly increase. The state's energy is about 0.042955; the next energies are about 0.054759 and 0.076458, with final energy about 0.102847 and original diagonal about 0.157441. These values are guidance only.

Existing analytic eleven-channel boxes yield h=C_1+C_3+C_7 in [-0.16,-0.11], a=C_2+C_6 in [-0.08,-0.06], b=C_5 in [-0.15,-0.14], c=C_10 in [0.023,0.025]. Both first gains `2(ha+bc)` and `2(hb+ac)` exceed 1/200 from these rational bounds. Both second gains are also positive because both final group coefficients are negative. The overlap coefficient c is strictly positive. No computational premise enters this proof.

The same saved-data diagnostic along greedy paths first finds an overlapping-state increase at M=16. Its greedy-specific failure is numerical guidance, not a Lean theorem. The frozen PE4G ceiling itself remains unrefuted.

## Strong positive survivor: exact two-coordinate minimax law

For arbitrary signed h,a,b,c on labels empty,{p},{q},{p,q}, let `I=h^2+a^2+b^2+c^2`, `F=(h+a+b+c)^2`, `L=(h+a)^2+(b+c)^2`, `R=(h+b)^2+(a+c)^2`. The two complete orders have peaks `max(I,F,L)` and `max(I,F,R)`. Hence their minimum is

`max(I,F,I+(h+c)(a+b)-abs((h-c)(a-b)))`.

The identity follows from `L-R=2(h-c)(a-b)` and `L+R-2I=2(h+c)(a+b)`. The first coordinate is the better next merger exactly when `(h-c)(a-b)<=0`. A prescribed ceiling B is feasible exactly when I, F and this minimum next energy are all at most B. This classifies the full two-coordinate signed family, including the genuine overlap coefficient c, without assuming endpoint control.

At the literal eleven-cutoff witness, every completion subset has energy at most F. The existing analytic strict SD1 bound at eleven supplies `F+1/100<Q_empty(11)`. Thus both complete remaining orders fit the original diagonal with a fixed positive reserve despite mandatory growth at the overlapping state. This is the positive arithmetic survivor; it does not establish an all-cutoff reserve.

## Lean closure

- `TwoCoordinateMergerCeiling.lean`: one definition and nine public theorems. These give the minimum-peak formula, exact ceiling feasibility, optimal first-coordinate comparison, equivalence for both first steps increasing, removal of processed labels from the energy cube, and the literal four-fibre energy formulas.
- `MobiusDivisorOverlapPhaseObstruction.lean`: six public theorems. These identify the remaining prime pair, prove the analytic fibre boxes and strict gains, certify the stalled state with positive joint fibre, refute universal overlap-state contraction, and prove the original-diagonal reserve for every completion subset.

Both leaves passed scratch checks and foreground `lake env lean <leaf> -o <exact olean>`. All sixteen new public declarations were axiom-audited once and use only `propext`, `Classical.choice` and `Quot.sound`. Both leaves are wired once into `RHTower.lean`. No previously audited declaration was re-audited; no umbrella, full or dependency build ran. Paper proof, exact classification and arithmetic positive survivor are complete. PE4, PE4G, SD1 and RH remain open.

The single global lint run reported two unrelated concurrent modules missing umbrella imports: `ThetaCuspModularEnergyBounds` and `ThetaCuspModularGlobalDriftBarrier`. Neither new CCM-FU leaf was flagged, and no proof-debt error was reported. Those concurrent modules were not changed or built by this work.
