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
as an independent surviving boundary source. The finite identities have
a closed paper proof; their Lean transfer and the uniform long-index
estimate are pending. This is a structural bridge, not a proof of the
large-packet conjecture.

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

## Decision criterion

If the vanishing statement holds, this much larger conductor family
still supplies no independent nonpolar terminal source. A compensation
argument must then identify a more extreme conductor scale, a different
receiver, or a different decomposition. If it fails, the surviving
source and its complete energy become the next explicit correction
problem. Neither outcome alone proves all-R positivity.

**Status:** survives the stated preliminary internal attack; no closed
paper proof, no Lean implementation, no claim of external novelty.
