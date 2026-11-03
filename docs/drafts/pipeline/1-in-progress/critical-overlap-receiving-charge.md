# Receiving charge in the complete form at critical overlap

- **ID:** Q6-CHARGE
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** `docs/reports/review-0311/fable.md`, §7
- **Statement:** Classify the exact complete Weil energy and its mixed pairing with the complement on harmonic-pole-neutral coherent prime-charge families and their coprime conductor fibres at `c = 2K(log N)^(1/8)`.

## Required conclusion

Determine whether affine successor energy pays the prescribed receiving charge, shell–pole terms cancel it, or a signed residual remains. Retain every Gamma, pole, shell, overlap and finite-horizon term. Formalize the classification and its consequences without unproved analytic premises.

## Established inputs

- `exists_harmonic_neutral_physical_vanishing_charge`: prescribed constant generator charge survives arbitrarily small adjunction energy and normalized physical input, uniformly for `N ≥ Q`.
- `normalizedPrimeModeSource_mul_of_coprime`: generator derivation across coprime conductors.
- `completeWeilEnergy_packetVector_at_every_overlap`: exact complete-form decomposition into dilation and affine energies, diagonal, shell degree, centre, far-cross, pole-error and overlap terms.

## Open proof

Evaluate the decomposition on the explicit normalized coefficients, including harmonic projection and coprime fibres; compute the polarized complement pairing. Neither the vanishing-input theorem nor the general decomposition supplies this evaluation.

## Exact dilation calculation

For `F_b(n) = Σ_(p∈P) b_p(1_(p|n) − 1/p)` and `H_M = Σ_(n≤M) 1/n`,

`J_N(F_b) = Σ_(p∈P) b_p² (log p/p) H_(⌊N/p⌋)`.

Proof: a Mangoldt-supported dilation changes only one prime incidence coordinate, so its squared jump linearizes to the jump with coefficients `b_p²`. For a single integer divisibility indicator `I_d`, the binary increment satisfies `(I_d(kn)−I_d(n))² = I_d(kn)−I_d(n)`. The target divisor sum is `Σ_(d|n≤N) log n/n`; the source sum is `Σ_(d|n≤N) ψ₁(⌊N/n⌋)/n`. Reindex both by `n=dr`. The identity `Σ_(r≤M) ψ₁(⌊M/r⌋)/r = Σ_(r≤M) log r/r` cancels the cofactor terms, leaving `(log d/d)H_(⌊N/d⌋)`.

Constant subtraction preserves every jump. Thus the normalized coherent coefficients, including harmonic centering, give

`J_N = (t/B_Q)² Σ_(p≤Q) (log p/p)H_(⌊N/p⌋)`.

This is the unnormalized dilation term. The physical input in the cited theorem is normalized by `log N`; these quantities cannot be interchanged.

Lean: `jumpEnergy_divisibilityIndicator`, `jumpEnergy_incidencePacket_diagonal` in `ArithmeticCouplingTheory/ReceivingCharges/PrimeIncidenceDilationEnergy.lean`; `harmonicPrimeCharge_jumpEnergy`, `harmonicPrimeCharge_charge_and_adjunction` in `CriticalScaleArithmeticRigidity/ReceivingCharges/FiniteHorizonPrimeCharge.lean`. Individual checks passed, transitive axioms exactly `propext`, `Classical.choice`, `Quot.sound`; both modules integrated. This calculation does not settle cancellation in the complete form.

## Boundary correction

Write `w_p = log p/p`, `B_q = Σ_(p≤q) w_p` and

`R_(Q,N) = Σ_(p≤Q) w_p(H_(⌊N/p⌋) − log N + B_p) − ½Σ_(p≤Q) w_p²`.

The triangular sum identity `2Σ_(p≤Q) w_p B_p = B_Q² + Σ_(p≤Q) w_p²` gives exactly

`J_N − (t²/B_Q)log N = −t²/2 + (t/B_Q)² R_(Q,N)`.

For `N ≥ Q`, the floor-harmonic comparison and prime Mertens bound make
`H_(⌊N/p⌋) − log N + B_p` uniformly bounded. Since `0 ≤ w_p ≤ 1`,
`|R_(Q,N)| ≤ C B_Q` with an absolute constant. Thus the boundary correction
tends uniformly to `−t²/2` as `Q → ∞`; at `N = Q`, `J_Q → t²/2`.
Lean: `harmonicPrimeCharge_jumpEnergy_boundary`,
`harmonicPrimeCharge_boundary_error_le`, `tendsto_harmonicPrimeCharge_boundary`,
`tendsto_harmonicPrimeCharge_cutoff_energy` in
`CriticalScaleArithmeticRigidity/ReceivingCharges/PrimeChargeBoundaryCorrection.lean`.
Individual check passed; transitive axioms exactly `propext`, `Classical.choice`,
`Quot.sound`; module integrated. This is a signed boundary term of dilation
energy alone; complete-form classification remains open.

## Complete-form test at the cutoff horizon

Conjecture: for `Q = N` and `c = 2K(log N)^(1/8)`, the complete energy tends
to `t²/2`. The required arithmetic input is now formalized: the second moment of
`ω_P(n) = Σ_(p∈P) 1_(p|n)`: with `S_P = Σ_(p∈P) 1/p`,
`Σ_(n≤N) ω_P(n)² ≤ N(S_P² + S_P)`. Divisibility counting gives this by
separating equal primes from distinct pairs. The harmonic version has
`H_N` in place of `N`. Harmonic centering subtracts a mean in `[0,S_P]`,
so the centered packet has arithmetic mean square
`O((t/B_N)²(S_P²+S_P))` and harmonic square
`O(H_N(t/B_N)²(S_P²+S_P))`.

Lean: `primeDivisorCount_second_moment_le`,
`primeDivisorCount_harmonic_second_moment_le`,
`harmonicPrimeCharge_packet_eq_centeredCount`,
`harmonicPrimeCharge_ordinary_square_le`, `harmonicPrimeCharge_harmonic_square_le`
in `CriticalScaleArithmeticRigidity/ReceivingCharges/PrimeChargeMoments.lean`.
Individual check passed with standard-only transitive axioms; module integrated.

Existing inputs: `mertensSecond_upper` gives `S_P = O(1+log log N)`;
`norm_separatedCrossErrorMatrix_le` costs `O(c²)` times harmonic square;
`shellDegree_packet_payment_le` costs `O(c)` times harmonic square plus
`O(c(1+log N))` times arithmetic mean square. Both contributions then
vanish at the critical overlap. Remaining verification: near-overlap and
centre bounds with terminal weights, exact pole cancellation, and the
mixed complement pairing. The cutoff test alone does not classify all
horizons or coprime fibres.

## Prime-scale classification to verify

For polynomial cutoffs `Q = ⌊N^θ⌋`, `0 < θ ≤ 1`, the dilation calculation
predicts complete energy `t²(1/θ − 1/2)` if the remaining complete-form
terms vanish. Polarization predicts the kernel

`K(θ,η) = [min(θ,η) − min(θ,η)²/2]/(θη)`.

Its positive representation is
`K(θ,η) = ∫₀¹ (1−u) 1_(u≤θ)1_(u≤η)/(θη) du`.
Thus scalar charge alone need not be controlled: on each of the `M` disjoint
prime-scale bands `[1−2^(−j), 1−2^(−j−1)]`, assign charge `t/M` by normalizing
with that band's actual prime Mertens mass. The predicted complete energy
is exactly `3t²/(2M)` in the horizon limit, while total receiving charge is
exactly `t`. Finite combinations require only fixed-profile moment bounds;
no estimate uniform in `M` is needed. This would distinguish the positive
form on prime-scale charge distributions from the unbounded total-charge
functional. Complete-form convergence and coprime-fibre transport are
unproved; these formulas are conjectures beyond the established dilation identity.

Integer-power realization: take `N = X^d`, cutoffs `X^a < X^b`, and normalize
one band's coefficients by its actual mass `B_(X^b) − B_(X^a)`. The predicted
energy of charge `t` is
`t²[d − (a+b)/2]/(b−a)`. With `d = 2^M`, the bands
`[d−2^(M−j), d−2^(M−j−1)]`, `0 ≤ j < M`, have cost `3t²/2` per unit
band charge. Giving each charge `t/M` yields `3t²/(2M)`. Integer powers
avoid floor-cutoff errors; distinct bands have exactly zero polarized
dilation pairing.

For fixed coprime conductor fibres, the proposed positive limit is the
same weighted prime-scale form tensored with the period Gram of the base
Ramanujan modes. Prime dilation outside the base conductors leaves those
modes unchanged; the finitely many base-prime contributions are bounded
by the vanishing harmonic input square. The remaining arithmetic input is
the uniform bounded remainder of the harmonic sum of each periodic product
`e_m e_l`, whose mean is `δ_(m,l)`. The corpus supplies it as
`ramanujanPoleProfile_gram_error_le`, with error at most `2ml`.

Weighted fibre identity to formalize: for `h(n)=e_m(n)e_l(n)` and `p ∤ ml`,

`Σ_(kn≤N) Λ(k)/(kn) h(n)(I_p(kn)−I_p(n))²
 = (log p/p) Σ_(n≤N/p) h(n)/n`.

On a Mangoldt edge changing `I_p`, multiplication leaves `h` unchanged.
Thus its weighted jump equals the jump of `h I_p` minus `I_p` times the
jump of `h`. Reindexing multiples of `p` in the source-target drift leaves
`(log p/p)H_h(N/p)`; the remaining drift cancels the second jump term
exactly. The fibre pairing then separates into this weighted prime diagonal
and base-prime jumps. This does not yet control pairing with an arbitrary
growing Euclidean complement.

## Mixed receiver to verify

Both normalizations matter. For `Q=N^θ`, let `x_N=F_(Q,N)/√n` and
`v_N=x_N/√log N`. The predicted raw energy is `t²(1/θ−1/2)`;
the normalized energy tends to zero.

Let `D_N` be the matrix of `J_N`, namely the diagonal
`log n+ψ₁(⌊N/n⌋)` minus `fullPrimeMatrix N`. The proposed stronger comparison is
`‖P_(pole⊥)(completeWeilMatrix−D_N)v_N‖→0`. The full quadratic remainder bound
`|R(F)|≤A c² H(F)+B c³(1+log N)V(F)` should imply, by polarization on the
neutral hyperplane, a squared mixed bound of size
`O(c⁶(log log N)²/log N)`. It tends to zero at critical overlap and controls
pairing with every bounded-norm complement vector. No separate row estimate
is needed: in `R(F+sG)−R(F−sG)`, choose `s` equal to the mixed pairing divided
by the uniform quadratic majorant of unit `G`.

For a prime incidence coefficient `b_p`, the exact `D_N` row separates into
the conductor-diagonal packet with eigenvalue `p log p/(p−1)` and

`T_(Q,N)(n)=Σ_(p≤Q) b_p[log p/(p−1)]p^(−⌊log_p(N/n)⌋)(1−1_(p|n))`.

For coherent coefficients, the predicted normalized source is the explicit
logarithmic ramp
`T_(Q,N)(n) = t[(log n/log N+θ−1)/θ]_+ + o_(harmonic L²)(1)`.
The conductor-diagonal part pairs to zero with `(conductorSubspace Q N)ᗮ`.
Thus the proposed mixed residual is pairing with this ramp, divided by
`√(n log N)`; the coprime fibre replaces it by `e_m` times the ramp.
Prime Mertens bounds control the tail `p>N/n`, and Chebyshev controls the
remaining geometric prime-power tails. Operator comparison, ramp convergence,
and a nonzero complementary witness are not yet formalized.

## Gates

- [x] Explicit families, overlap scale and complete-form receiver identified.
- [ ] Dependency-closed paper classification.
- [ ] Lean classification and consequences; individual `lake --old env lean` checks and standard-only axiom audit.
