# Harmonic tail charge of bounded chronological repair

**[BRIDGE Q], proved on paper and formalized in Lean.** This is a
necessary condition for the unchanged bounded-array target [R], not its proof.

For a finite array with |a_k|≤C, C≥0, put S=Σ_(k≤N)a_k/k and
r(t)=exp(−t)+Σ_(k≤N)a_k h(kt). For every T≥1,

|S| ≤ (T+1)(||r||₂+(1+4C)exp(−T)).

The bound is independent of N. Indeed,
r(t)=S/t+exp(−t)−Σ_(k≤N)a_k/(exp(kt)−1).
For t≥1, q=exp(−t)≤1/2 and
Σ_(k≤N)1/(exp(kt)−1)≤Σ_(k≥1)q^k/(1−q)≤4q.
Thus |S|≤t(|r(t)|+(1+4C)exp(−t)). Integrate over the unit interval
(T,T+1]; Cauchy–Schwarz bounds its integral of |r| by the full L² norm.

Consequently, for every uniformly bounded successful array, S_N→0: first
choose T so (T+1)(1+4C)exp(−T) is small, then take N large with ||r_N||₂
small. No RH, Möbius estimate, numerical input, or unproved uniform bound
is used. The logarithmic loss in the finite estimate is acceptable for this
necessary condition and is not asserted to be sharp.

This closes the harmonic-tail step needed for coefficient recovery. Full
coordinatewise convergence to μ is a separate remaining formal target; it
is not claimed here. Local convergence and vanishing harmonic charge still
do not control concentration near t=0.

**[BRIDGE Q+], strengthened claim frozen independently and now formalized.** For every
η>0, any successful array bounded by C can be replaced by an exactly
zero-charge successful array bounded by C+η. Once |S_N|<η, replace a_(1,N)
by a_(1,N)−S_N and leave the other coefficients unchanged. Choose the finitely
many earlier rows to be zero. The exact residual change is −S_N h(t), whose
L² norm tends to zero because h belongs to L². Thus the same proof closes Q+
on paper. No fixed-prefix or exact-C preservation is asserted; this is a
normalization for the original problem with an unspecified finite budget.


## Lean certificate

Module `GaloisForLFunctions.RHTower.ChronologicalHarmonicCharge`, namespace
`RHTower`. Twelve public declarations cover the charge and Bose sum, exact
residual decomposition, cutoff-independent exponential bound, quantitative
charge estimate, vanishing charge, exact normalization, its charge and residual
identities, norm estimate, convergence, and the C+η normalization theorem.
All proofs are closed; only propext, Classical.choice and Quot.sound occur.
No numerical result, RH premise or additional axiom enters a proof.

Scratch: `lake env lean /tmp/ChronologicalHarmonicCharge.lean`.
Final leaf audit: `LEAN_NUM_THREADS=1 lake build --old
GaloisForLFunctions.RHTower.ChronologicalHarmonicCharge`, exit 0; only that leaf
compiled, in 10 seconds. The umbrella import is wired. No full or umbrella
build ran. Authoritative lint passed with existing file-size warnings.
Audit artifacts:
`/tmp/chronological_charge_{manifest.json,axioms.lean,axioms.txt,axiom_summary.json,build.txt,lint.txt,index.txt}`.

The main normalization theorem is
`chronologicalSuccessfulRepair_zeroCharge_normalization`.
The exact bound is `chronologicalHarmonicCharge_L2_bound` and the necessary
limit is `chronologicalHarmonicCharge_tendsto_zero`.
