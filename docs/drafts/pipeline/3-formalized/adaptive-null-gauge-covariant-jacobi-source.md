# Adaptive null-gauge producer and covariant Jacobi source

- **ID:** adaptive-null-gauge-covariant-jacobi-source
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `docs/reports/mass-shifted-spectral-trace-route.md` · §9.3 exact open core
- **Statement:** Full corrected adaptive null-gauge arithmetic producer is positive Jacobi energy at moving admission, and moving odd current has strictly negative covariant derivative.

## Goal

Construct requested admission-sensitive arithmetic producer before reflection aggregation and
identify exact connection defect separating frozen boundary amplitude from moving admission.

## Gates

- [x] 0 → 1  in-progress: source-pure statement and hostile failure loop recorded
- [x] 1 → 2  fully-proven: dependency-closed coefficient/product-rule proof `[PROVED HERE]`
- [x] 2 → 3  formalized: direct Lean checks and targeted builds green; axiom audit PASS
- [ ] 3 → 4  publication-ready: specialist novelty review and standalone exposition

## Exact results `[PROVED HERE]`

Let `L_y` be shifted-Xi real moment functional, `P_n` current monic orthogonal admission,
`h_n=L_y(P_n²)`, and `E_n>0` its completed Jacobi energy.

1. Full corrected inverse-null-gauge producer is

   `C_y(A,N)=2 coeff₂(nullGaugeSourceSeries_y(A,N))-2L_y(lowerResidual(A,N))`.

   For any monic degree-`N` amplitude,

   `C_y(A,N)=(2N+1) S_mix^sharp(y,A)`.

   If `H_(n+2)(y)≻0`, then

   `C_y(P_n,n)=(2n+1)·2h_nE_n>0`.

2. For any differentiable finite coefficient curve `P(v)` through `P_n` with monic tangent
   `V=∂_vP|_y`, `deg V<n`, and odd current `B(v)=L_v(P(v)XP(v))`,

   `B'(y)=-2h_nE_n+2h_n V[n-1]`.

   Therefore intrinsic covariant derivative

   `D B_n := B'(y)-2h_nV[n-1] = -2h_nE_n < 0`.

   For a monic path, `V[n-1]` is derivative of `nextCoeff(P(v))`; this is exact
   Gram--Schmidt connection term.

3. A genuine outgoing crossing forces some transported boundary amplitude `A` and later aperture
   into exact dichotomy

   `not H_(deg A+2)≻0 or A != currentMonicAdmission`.

## Proof skeleton

- Differentiate finite double sum for `L_v(P(v)XP(v))` using unconditional shifted-Xi moment
  derivative `m_k'=-(k+1)m_(k+1)`.
- Fixed-amplitude part is exactly `-2` times adaptive source by existing Euler connection.
- Moving part is `2L_y(VXP_n)`.
- Three-term recurrence and `deg V<n` kill `P_(n+1)` and `P_n`; only `P_(n-1)` remains.
  Since its coefficient in `XP_n` is `beta_n=h_n/h_(n-1)`, result is
  `L_y(VXP_n)=h_nV[n-1]`.
- Finite Jacobi-energy theorem gives fixed source `h_nE_n>0` from `H_(n+2)≻0`.
- Null-gauge arithmetic identity supplies odd-contact factor `2n+1`; outgoing-ray negativity plus
  moving-admission positivity gives dichotomy.

## Hostile review

- **Ordinary monotonicity:** false without connection bound; degree drop does not kill pairing with
  `XP_n`.
- **Naive primitive:** `B_n-2h_na_n` leaves `-2a_nh_n'`; connection one-form is not generally
  exact in multi-parameter moment space.
- **Reporter attack:** producer uses full inverse null-gauge germ and subtracts its intrinsic
  lower-contact residual before rational--Gamma/von Mangoldt formation. No fixed linear map.
- **Global positivity attack:** every sign theorem uses one finite `H_(n+2)` block only.
- **Circularity:** no RH, zero-location, LP, Herglotz, or asymptotic input.

## Lean certificate

- `RHTower.XiShiftedAdaptiveOrthogonalNullGaugeArithmeticProducer`
  - `xiShiftedAdaptiveNullGaugeCorrectedArithmeticProducer_eq_arithmeticSource`
  - `xiShiftedAdaptiveNullGaugeCorrectedArithmeticProducer_monicOrtho_eq_jacobiEnergy_of_hankelPosDef`
  - `xiShiftedAdaptiveNullGaugeCorrectedArithmeticProducer_monicOrtho_pos_of_hankelPosDef`
  - `neg_correctedNullGaugeProducer_forces_hankelFailure_or_admissionMismatch`
  - `genuineCrossing_forces_higherHankelFailure_or_admissionHolonomy`
- `RHTower.XiShiftedAdaptiveAdmissionCovariantSource`
  - `hasDerivAt_xiShiftedMomentInner_movingOddCurrent`
  - `momentInner_velocity_X_monicOrtho_eq_norm_mul_coeff_below`
  - `hasDerivAt_xiShiftedMovingAdmissionOddCurrent_eq_jacobiEnergy`
  - `xiShiftedMovingAdmissionOddCurrent_covariantDerivative_neg`

## Remaining boundary

Covariant dissipation does not imply ordinary monotonicity until admission connection has a local
primitive or a sharp bound.  Exact open core is now sign/effectivity of subleading connection—or an
argument forcing infinite admission holonomy to contradict shifted-Xi structure.

## Log

- 2026-08-11 — paper proof completed; producer, finite positivity, crossing dichotomy, moving
  product rule, recurrence collapse, and covariant negativity formalized without computation.
- 2026-08-11 — producer target build PASS. Canonical successor certificate formalizes actual
  inverse-Hankel curve, cumulative trace cancellation, and strict source dissipation. Axiom audit
  reports only `propext`, `Classical.choice`, `Quot.sound`.
