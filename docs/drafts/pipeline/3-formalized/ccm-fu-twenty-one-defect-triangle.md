# CCM-FU: unavoidable nonempty defect at cutoff21

- **Type:** unconditional actual-source obstruction
- **Stage:** 3-formalized
- **Parent:** [head-supported defect paths](../5-failed/ccm-fu-head-supported-defect-path.md)
- **Goal:** identify the source interaction which a complete mixed-field proof must pay; RH remains open.

## Actual-source argument

At cutoff21, consider the last selected prime q among {2,3,5}. Immediately
before it is selected, the other two are processed. The only squarefree
source multiples of these primes below21 have at most two distinct prime
factors. Processing any additional prime can therefore only subtract
another nonnegative unsigned channel from the remaining singleton.

Write K_d for the literal unsigned channel at21. The three possible
remaining singleton bounds are

- q=2: `A_P({2})<=K_2-K_6-K_10`;
- q=3: `A_P({3})<=K_3-K_6-K_15`;
- q=5: `A_P({5})=K_5-K_10-K_15`.

Each right side is strictly below -1/50. For q=3, the already formal
cutoff-seven reflection gives `K_3-K_6<-0.04`. For q=5, the already formal
tail boxes give `K_5-K_10<0.08` and `K_15>0.1`.

For q=2 the proved analytic bounds are `K_2<=0.38`, `K_6>0.23`,
`K_10>0.19`. Exact dilation gives `K_6=sqrt(3)*K_2(7)>0.23`.
The first two quotient blocks give
`K_10=(sqrt(20)-sqrt(10))*D(1)+(sqrt(21)-sqrt(20))*D(2)>0.19`
from analytic lower bounds D(1)>=0.1536, D(2)>=0.0003.
Finally `K_2(22)=sqrt(2)*K_1(11)<=0.27`. The exact last clock step,
`D(10)>=-1` and `sqrt(22)-sqrt(21)<=0.11`, give K_2(21)<=0.38.
The D(10) bound follows from its literal log-factorial formula, the harmonic
lower bound gamma>=0.5768 and log(10!)>=21log2, proved by integer-product
comparison and logarithm monotonicity.

This excludes confinement of all defects to the head for every prime
order at21, independently of an energy budget. The proof is closed in Lean;
the saved numerical path graph supplies no premise.
The positive survivor is the full created-defect decomposition and sharp
head-repair capacity already formalized in
[mixed transverse compensation](ccm-fu-mixed-transverse-compensation.md).
The quantitative obstruction identifies a nonempty coordinate below
-1/50 at an actual proper prefix, retaining the interaction that a complete
source proof must control. No claim that unrestricted reserve extension,
PE4, SD1 or RH fails follows.

## Exact declarations

`MobiusDivisorUnavoidableNonemptyDefect.lean` proves
`mobiusDivisor_twentyOne_last_triangle_negative` for every processed finite
set P and every q in {2,3,5} whose other two primes are processed while q
is unprocessed. No assumption that P contains only source primes is needed.

`mobiusDivisor_every_cover_twentyOne_nonempty_defect` then covers every list
whose finite support contains {2,3,5}, including lists with repetitions.
Choose the triangle prime with largest first-occurrence index. This index
is strictly below the list length; the other two indices are smaller and
the chosen prime is absent from the preceding prefix. Applying the first
theorem yields a singleton below -1/50 at that proper prefix.

Scratch and exact-file `lake env lean` checks pass. Only this new leaf's
olean was emitted; its import is wired once into `RHTower.lean`. No full,
umbrella or dependency build ran. The previous stale-dependency Lake
preflight was not repeated and no dependency-rebuilding Lake audit is claimed.

Both new public theorems were axiom-audited once and use only `propext`,
`Classical.choice`, and `Quot.sound`. No new experiment or numerical premise
was used. The formal index was refreshed. Global lint reported one unrelated
unwired module, `RHTower.RealSphericalComplementaryWeights`; the new source
leaf is wired and was not flagged. That unrelated file was left untouched.
All owned Lean checks completed and owned scratch/audit files were removed.
