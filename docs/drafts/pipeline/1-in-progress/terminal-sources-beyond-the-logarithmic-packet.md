# Terminal sources beyond the logarithmic conductor packet

- **ID:** terminal-sources-beyond-the-logarithmic-packet
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Parent:** [critical-ratio continuation](critical-ratio-continuation.md)

## Exact competing statements

Let L=log N, c_N≥1, c_N⁸/L→R>0, B_N the complete tilted-spline
matrix, E_m its completed conductor energy and v_m its normalized
Ramanujan horizon vector. Fix a compact C² terminal window x_h with
F(x)=h(log x) supported inside (1/2,1). For Q_N=floor(N^(1/64)), test

    Σ_(2≤m≤Q_N) |⟨B_Nv_m,x_h⟩|²/(c_N E_m) → 0.

**[OPEN CORE]** This is stronger than the logarithmic-packet reduction.
The competing statement is a nonzero limit carried by conductors that
escape every fixed cutoff. A counterexample must retain its actual
conductor range, normalized receiving profile and complete energy.

The target concerns mixed sources only. Extending the signed packet
Gram approximation to this range would be a separate obligation before
identifying energy-optimal corrections.

## Why this is the next question

Every fixed nonpolar source is now checked to vanish. Below m≤c_N,
the inverse-energy envelope is O_(h,R)(m⁻⁵). Above overlap, the existing
global residual norm gives a vanishing sum through L^(13/32), but costs
Q² and fails in the proposed range. This failure of a majorant does not
construct a surviving source.

The exact channel decomposition retains a mean-zero Ramanujan sequence
in the Gamma, near-center and near-log rows. Averaging over the long
terminal index, with the short gap fixed, might retain cancellation
uniformly in m without requiring c_N≫m. The full-center and divisor-jet
means are opposite von Mangoldt charges; their finite errors must be
paired before summing inverse energies. A limit theorem with fixed m
cannot perform this task.

The corpus already supplies a quantitative harmonic charge law:
`abs_normalizedRamanujan_harmonic_add_vonMangoldt_le` in
`SuccessorShellArithmetic/TopBand/RamanujanDivisorMoments.lean` bounds
the normalized error by `2m√φ(m)/(N+1)` for every m≥2 and N.
`PeriodMassShellRows.lean` gives interval-sum costs m for the normalized
mode and `2m log m` for the centered normalized divisor jet. These
source proofs have been inspected. The open task is their application
to the complete terminal kernel, not constructing those arithmetic
means or uniform harmonic rates anew.

## Attack

1. Derive a finite signed terminal bound from
   `complete_terminal_conductor_pair_eq_channels`. Keep the jet and full
   center together. Preserve every dependence on m, c and N.
2. For each fixed gap, apply periodic cancellation in the long index.
   Control its moving endpoints and kernel variation. Taking absolute
   values of the conductor sequence first loses the proposed gain.
3. Complete the punctured divisor-jet shell using the exact ratio-prime
   row, as below. Estimating these two channels separately loses a finite
   cancellation before any limiting argument.
4. Test the literal harmonic prime-charge coefficients against the
   resulting bound. Cheap complete energy alone says nothing about their
   terminal receiving response.

The new corpus bounds in `ReceivingCharges/PrimeChargeIntermediateBounds`
and `PrimeChargeUniformGeometry` retain reciprocal-prime mass and supply
geometry uniformly when Q⁶⁴≤N. Their source statements do not yet give
this complete mixed pairing. They have been read, not freshly audited
here. No theorem in this card assumes their unproved consequence.

## Exact finite cancellation exposed by the prime row

Write c_m(n) for the Ramanujan coefficient and j_m(n) for its logarithmic
divisor jet. For N/2<n≤N, the upward ratio-prime sum vanishes: its only
possible multiplier is one, whose von Mangoldt weight is zero. The exact
downward identity therefore gives

    Σ_(j≤N) weilPrimeKernel(n,j)c_m(j)/√j
      =[log(n)c_m(n)−j_m(n)]/√n.

This follows from `sum_weilPrimeKernel_poleProfile` and
`sum_vonMangoldt_mul_ramanujan_eq_log_sub_jet`; no asymptotic estimate is
used. For a terminal F supported above half, its negative contribution
contains `+Σ F(n/N)j_m(n)/n`. The normalized autocorrelation K has K(0)=1,
so this is exactly the missing diagonal of the punctured jet pair:

    Σ_(n,j≤N; 0<|log(j/n)|≤2c/N)
      F(n/N)j_m(j)K(N|log(j/n)|/c)/√(nj)
      +Σ_(n≤N) F(n/N)j_m(n)/n
    =Σ_(n,j≤N; |log(j/n)|≤2c/N)
      F(n/N)j_m(j)K(N|log(j/n)|/c)/√(nj).

Subtracting `(log N−adj_m)v_m` from the prime row changes only its
Ramanujan diagonal to `(log(n/N)+adj_m)c_m(n)`; the jet cancellation is
unchanged. Thus the apparent `−Λ(m)/c` puncture charge must not be treated
as an independent surviving boundary source. Both endpoints in
`TheRatioPrimeRowCompletesTheTerminalJet.lean` pass their actual-path
audit with exactly `[propext, Classical.choice, Quot.sound]`; the module
is wired into its umbrella. The uniform long-index estimate remains a
separate obligation. This finite identity does not prove the large-packet
conjecture.

## A quantitative statement to attack

For each fixed window and positive critical clock, test whether one
constant C gives, eventually and uniformly for `2≤m≤N^(1/64)`,

    |(√L/c_N)⟨B_Nv_m,x_h⟩|
      ≤ C/√φ(m) [Λ(m)/c_N + m⁸c_N⁸L²/√N].

**[OPEN CORE]** The long-index periodic estimate for the complete signed
pairing, with this explicit conductor dependence, is not proved. The
exponents allow substantial slack while keeping the conclusion testable.
The finite jet completion above removes one possible false source; it
does not supply this bound.

The required energy reserve already exists:
`log_conductor_sub_log_overlap_le_completedEnergy` gives
`E_m≥log m−log c_N+min(0,self_φ(1))`. Above a fixed multiple of c_N²,
this is at least half log m. The first proposed error is supported on
prime powers, where φ(m)≥m/2 and Λ(m)≤log m. Its inverse-energy sum is
therefore controlled by `Σ_(m≤Q)Λ(m)/m`, rather than by Q or by an
unweighted prime count. For Q=N^(1/64), its contribution is O(1/c_N).
Between c_N and that quadratic threshold the common energy floor and
`exists_sum_vonMangoldt_sq_div_le` give
O((log c_N)²/(c_N L)). Below overlap use the fifth-power envelope.

The second proposed error contributes at most a fixed multiple of
`c_N¹⁷L³ Q¹⁷/N` above overlap using only φ(m)≥1 and the positive floor;
this tends to zero for the stated Q. Thus this explicit source estimate
would prove the large-packet conjecture. Its crucial content is the
separation of the sparse von Mangoldt mean from the polynomial periodic
error; a generic residual norm does not do that.

## Long-index estimate for the actual near kernel

A checked finite argument gives the following actual-kernel
estimate. Assume F
vanishes on `x≤1/2`, `|F|≤B_F`, and `Lip(F)≤L_F`. Let K vanish on
`[1,∞)`, satisfy `|K|≤B_K`, and have Lipschitz constant L_K. Let p
be q-periodic with zero mean and `|p|≤B`. For c≥1 and `8c≤N`, put

    C_W = 20B_FB_K+64B_FL_K+4B_KL_F,
    C_K = 64L_K+4B_K.

The exact-kernel bound is

    |endpointNearPairSum(K,F,0,2,c/N,N,1,p)/c|
      ≤ [4qB C_W+8B_FB C_K c]/N.

**Proof.** For n<j≤N, `1−n/j≤log(j/n)`. If K at the actual gap is
nonzero, `log(j/n)<c/N`, hence `d=j−n≤c`. Thus only integer gaps
`1≤d≤floor(c)` contribute; no exponential strip loss is needed.
Reindex the two triangles by j=n+d using `sum_sum_ite_lt`.

Set `I(x)=1/max(1/4,x)` and `W_θ(x)=F(x)I(x)K(θI(x))`.
The reciprocal difference identity and the one-Lipschitz clamp give
`0≤I≤4`, `Lip(I)≤16`. The bounded-product rule gives

    ||W_θ||∞≤4B_FB_K,
    Lip(W_θ)≤64B_FL_K+16B_FB_K+4B_KL_F       (|θ|≤1).

At θ=d/c, use the two profiles F(x) and F(x+d/N). Wherever either
is nonzero, n/N≥1/4 because d/N≤1/8. The clamp therefore leaves the
actual row unchanged. Applying the checked
`abs_terminal_shifted_periodic_zero_mean_le` to each reciprocal row
bounds its absolute sum by `2qB C_W/N`, independently of d and c.
The reciprocal-row statement is implemented in
`TerminalReciprocalRowsCancelAlongTheLongIndex.lean`, together with its
moving-interval version at twice the prefix constant. All three capstones
pass their actual-path audit with `[propext, Classical.choice, Quot.sound]`.

For the actual kernel, apply the checked
`abs_sqrt_log_kernel_sub_linear_le` with A=4, B=c, x=n, y=n+d.
Its hypotheses follow from `8c≤N` and the support observation. The
kernel difference is at most `C_K c/N`. The combined two-triangle
coefficient divided by n is at most `8B_FB/N`; summing at most N
indices costs `8B_FB C_K c/N` per gap. There are at most c gaps.
After division by c, the two reciprocal estimates and this error give
the displayed bound. Zero receiver coefficients contribute nothing.
`TerminalNearRowsCancelAlongTheLongIndex.lean` implements the exact
strip, triangle reindexing, kernel error and final bound. All four printed
capstones pass their actual-path audit with exactly
`[propext, Classical.choice, Quot.sound]`. Both long-index modules are
wired into the programme umbrella.

This cancellation uses the long terminal index. It imposes no relation
between q and c. Apply it to the centered divisor jet and retain its
sparse Mangoldt mean separately. The exact prime-row completion removes
the punctured diagonal before that split. The Gamma, center and remaining
complete channels still need their own conductor-uniform estimates;
this near-kernel result alone does not prove the large-packet conjecture.

## A sufficient weaker rate for the Gamma channels

The existing finite theorem `abs_farCross_pair_tail_le` bounds the actual
tail beyond scaled gap T≥2, divided by c, by

    C_φ B²(16/T+32c/N),

for bounded arithmetic weights. Its statement is uniform in T, c and N;
T need not be fixed before the horizon limit. This avoids requiring a
new globally differentiable full Gamma profile.

For the remaining annulus, the source already supplies bounded
Lipschitz near and cross-singular profiles and an entry error O_φ(c/N).
The long-index argument needs polynomial losses
`qB(1+T)²/N + B(1+T)³c/N`. Cancellation on the moving integer interval
selected by the logarithmic gap cutoffs is now checked.
At a fixed integer gap d, `log(1+d/n)` decreases with n, so that selector
is an interval; an interval version of the periodic prefix estimate
pays both endpoints. The [formalized finite bound](../3-formalized/terminal-annular-long-index-cancellation.md)
retains explicit quadratic/cubic T-dependence. Its five endpoints pass
their actual-path audit with `[propext, Classical.choice, Quot.sound]`.
**[OPEN CORE]** Transfer that bound to the literal Gamma profiles and
assemble every complete source channel with its conductor dependence.

Choosing T=N^(1/8) gives a weaker but sufficient candidate complete bound

    |(√L/c_N)⟨B_Nv_m,x_h⟩|
      ≤ C/√φ(m) [Λ(m)(1+log c_N)/c_N + m⁴c_N⁸L²/N^(1/8)].

The logarithm retains the rate already supplied by
`abs_nearPairSum_div_overlap_sub_weighted_row_le`; removing it is not
needed. The sparse mean contributes `O((1+log c_N)²/c_N)→0` above the
quadratic conductor threshold, and the intermediate range gains the
same squared logarithmic factor in its vanishing bound.
The polynomial-error contribution to the inverse-energy sum is at most
`C c_N¹⁷L³Q_N⁹/N^(1/4)`, hence tends to zero when Q_N=N^(1/64):
the remaining horizon power is −7/64. This suffices for the same
large-packet conjecture without proving the earlier, stronger N^(-1/2)
remainder. The complete bound itself is still open; the finite tail
theorem alone does not establish it.

For these interior receivers the boundary-prime channels are already
closed uniformly in every conductor: `eventually_terminal_upward_pairing_eq_zero`
and `eventually_terminal_exteriorDownward_pairing_eq_zero` give one
eventual horizon for all m. The remaining transfer concerns Gamma,
center, the completed divisor jet and replacement errors, not a new
boundary-prime distribution estimate.

## Decision criterion

If the vanishing statement holds, this much larger conductor family
still supplies no independent nonpolar terminal source. A compensation
argument must then identify a more extreme conductor scale, a different
receiver, or a different decomposition. If it fails, the surviving
source and its complete energy become the next explicit correction
problem. Neither outcome alone proves all-R positivity.

**Status:** survives the stated preliminary internal attack; no closed
paper proof, no Lean implementation, no claim of external novelty.
