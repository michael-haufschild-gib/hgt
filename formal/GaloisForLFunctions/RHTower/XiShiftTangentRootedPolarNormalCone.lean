import GaloisForLFunctions.RHTower.GammaJordanXiTangentResponseGap

/-!
# Rooted polar normal cone of the Xi-shift tangent

The normalized completed `+2` Xi-shift tangent Gram is nonstationary in the
absolute prime scale.  Its defect nevertheless has an exact source-to-polar
boundary expansion.

For inverse-prime coordinates `a = p⁻¹`, `b = q⁻¹`, put

`δ = ((a-b)/(1-ab))²`.

The all-depth tangent correlation is exactly

`sqrt(1-δ) * (1-2δ)`.

The defect has the exact second-order normal form

`1 - sqrt(1-δ) * (1-2δ) = (5/2)δ + δ² R(δ)`,

where `R(0) = -7/8`.  Rewriting

`δ = A u / (1-u)²`,

with `u = 1/(pq)` and

`A = (p-q)²/(pq) = 2 cosh(log p - log q) - 2`,

shows that the unique symmetric rooted first blow-up is `(5/2)A`.  This is
exactly `5/2` times the tangent of the critical polar kernel at doubled
prime-log nodes.  The next normal coefficient is

`5A - (7/8)A² = A(40-7A)/8`,

so it has one positive transition at `A = 40/7`, equivalently
`cosh(log p-log q) = 27/7`.

No Xi zero or RH premise is used.
-/

open Filter Set Topology

namespace RHTower

noncomputable section

/-- Pseudohyperbolic separation of two inverse-prime source nodes. -/
def xiShiftTangentBoundaryDelta (p q : Nat.Primes) : ℝ :=
  ((((p : ℝ)⁻¹ - (q : ℝ)⁻¹) /
    (1 - (p : ℝ)⁻¹ * (q : ℝ)⁻¹)) ^ 2)

/-- Universal normalized Xi-shift tangent response at squared separation `δ`. -/
def xiShiftTangentBoundaryResponse (δ : ℝ) : ℝ :=
  Real.sqrt (1 - δ) * (1 - 2 * δ)

/-- Exact second-order remainder of the boundary response defect. -/
def xiShiftTangentBoundaryNormalRemainder (δ : ℝ) : ℝ :=
  1 / (2 * (1 + Real.sqrt (1 - δ)) ^ 2) -
    2 / (1 + Real.sqrt (1 - δ))

/-- Polar lag variable at two positive multiplicative nodes. -/
def xiShiftPolarLag (p q : ℝ) : ℝ :=
  (p - q) ^ 2 / (p * q)

/-- Second rooted normal coefficient after removal of the polar tangent. -/
def xiShiftPolarSecondNormalCoefficient (A : ℝ) : ℝ :=
  5 * A - (7 / 8 : ℝ) * A ^ 2

/-- Continuous extension of the first rooted polar quotient. -/
def xiShiftPolarFirstNormalExtension (A u : ℝ) : ℝ :=
  (5 / 2 : ℝ) * A / (1 - u) ^ 2 +
    A ^ 2 * u / (1 - u) ^ 4 *
      xiShiftTangentBoundaryNormalRemainder
        (A * u / (1 - u) ^ 2)

/-- Continuous extension of the second rooted normal quotient. -/
def xiShiftPolarSecondNormalExtension (A u : ℝ) : ℝ :=
  (5 / 2 : ℝ) * A * (2 - u) / (1 - u) ^ 2 +
    A ^ 2 / (1 - u) ^ 4 *
      xiShiftTangentBoundaryNormalRemainder
        (A * u / (1 - u) ^ 2)

theorem xiShiftTangentBoundaryDelta_nonneg (p q : Nat.Primes) :
    0 ≤ xiShiftTangentBoundaryDelta p q := by
  exact sq_nonneg _

/-- The inverse-prime pseudohyperbolic separation is the rooted rational
prime-pair separation. -/
theorem xiShiftTangentBoundaryDelta_eq_primeRatio
    (p q : Nat.Primes) :
    xiShiftTangentBoundaryDelta p q =
      (((p : ℝ) - q) / ((p : ℝ) * q - 1)) ^ 2 := by
  have hp : (p : ℝ) ≠ 0 := by exact_mod_cast p.2.ne_zero
  have hq : (q : ℝ) ≠ 0 := by exact_mod_cast q.2.ne_zero
  have hpq : (p : ℝ) * q - 1 ≠ 0 := by
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast p.2.two_le
    have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast q.2.two_le
    nlinarith
  unfold xiShiftTangentBoundaryDelta
  field_simp [hp, hq, hpq]
  ring

/-- The all-depth normalized source tangent correlation depends on its
inverse-prime nodes through one exact pseudohyperbolic response. -/
theorem gammaSewnXiShiftEndpointUnitTangentKernel_eq_boundaryResponse
    (p q : Nat.Primes) :
    gammaSewnXiShiftEndpointUnitTangentKernel p q =
      xiShiftTangentBoundaryResponse
        (xiShiftTangentBoundaryDelta p q) := by
  let a := (p : ℝ)⁻¹
  let b := (q : ℝ)⁻¹
  let d := 1 - a * b
  let k := gammaXiFisherBaseCorrelation p q
  let δ := ((a - b) / d) ^ 2
  have hp0 : (0 : ℝ) < p := by exact_mod_cast p.2.pos
  have hq0 : (0 : ℝ) < q := by exact_mod_cast q.2.pos
  have ha0 : 0 < a := by
    dsimp only [a]
    exact inv_pos.mpr hp0
  have hb0 : 0 < b := by
    dsimp only [b]
    exact inv_pos.mpr hq0
  have ha1 : a < 1 := by
    dsimp only [a]
    exact (inv_lt_one₀ hp0).mpr
      (by exact_mod_cast p.2.one_lt)
  have hb1 : b < 1 := by
    dsimp only [b]
    exact (inv_lt_one₀ hq0).mpr
      (by exact_mod_cast q.2.one_lt)
  have hd : 0 < d := by
    dsimp only [d]
    nlinarith [mul_lt_one_of_nonneg_of_lt_one_left ha0.le ha1 hb1.le]
  have hA : 0 ≤ (1 - a ^ 2) * (1 - b ^ 2) := by
    exact mul_nonneg (by nlinarith [sq_nonneg (a - 1)])
      (by nlinarith [sq_nonneg (b - 1)])
  have hkSq : k ^ 2 = 1 - δ := by
    change
      (Real.sqrt ((1 - a ^ 2) * (1 - b ^ 2)) / d) ^ 2 =
        1 - ((a - b) / d) ^ 2
    rw [div_pow, Real.sq_sqrt hA, div_pow]
    field_simp [hd.ne']
    ring
  have hk0 : 0 < k := gammaXiFisherBaseCorrelation_pos p q
  have hsqrt : Real.sqrt (1 - δ) = k := by
    rw [← hkSq, Real.sqrt_sq_eq_abs, abs_of_pos hk0]
  rw [gammaSewnXiShiftEndpointUnitTangentKernel_eq_responseFromBase]
  unfold xiShiftTangentBoundaryResponse xiShiftTangentBoundaryDelta
    xiShiftTangentResponseFromBase
  change k * (2 * k ^ 2 - 1) =
    Real.sqrt (1 - δ) * (1 - 2 * δ)
  rw [hsqrt, hkSq]
  ring

theorem xiShiftTangentBoundaryDelta_lt_one (p q : Nat.Primes) :
    xiShiftTangentBoundaryDelta p q < 1 := by
  let a := (p : ℝ)⁻¹
  let b := (q : ℝ)⁻¹
  let d := 1 - a * b
  have hp0 : (0 : ℝ) < p := by exact_mod_cast p.2.pos
  have hq0 : (0 : ℝ) < q := by exact_mod_cast q.2.pos
  have ha0 : 0 < a := inv_pos.mpr hp0
  have hb0 : 0 < b := inv_pos.mpr hq0
  have ha1 : a < 1 :=
    (inv_lt_one₀ hp0).mpr (by exact_mod_cast p.2.one_lt)
  have hb1 : b < 1 :=
    (inv_lt_one₀ hq0).mpr (by exact_mod_cast q.2.one_lt)
  have hd : 0 < d := by
    dsimp only [d]
    nlinarith [mul_lt_one_of_nonneg_of_lt_one_left ha0.le ha1 hb1.le]
  have hdiff : (a - b) ^ 2 < d ^ 2 := by
    have haSq : 0 < 1 - a ^ 2 := by
      nlinarith [sq_lt_sq₀ ha0.le (by norm_num) |>.2 ha1]
    have hbSq : 0 < 1 - b ^ 2 := by
      nlinarith [sq_lt_sq₀ hb0.le (by norm_num) |>.2 hb1]
    have hprod := mul_pos haSq hbSq
    dsimp only [d]
    nlinarith
  change ((a - b) / d) ^ 2 < 1
  rw [div_pow, div_lt_one (sq_pos_of_pos hd)]
  exact hdiff

/-- Exact second-order normal expansion of the universal response defect. -/
theorem one_sub_xiShiftTangentBoundaryResponse_eq
    {δ : ℝ} (hδ : δ ≤ 1) :
    1 - xiShiftTangentBoundaryResponse δ =
      (5 / 2 : ℝ) * δ +
        δ ^ 2 * xiShiftTangentBoundaryNormalRemainder δ := by
  let s := Real.sqrt (1 - δ)
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hsSq : s ^ 2 = 1 - δ := Real.sq_sqrt (by linarith)
  have hden : 1 + s ≠ 0 := by positivity
  unfold xiShiftTangentBoundaryResponse
    xiShiftTangentBoundaryNormalRemainder
  change 1 - s * (1 - 2 * δ) =
    (5 / 2 : ℝ) * δ +
      δ ^ 2 * (1 / (2 * (1 + s) ^ 2) - 2 / (1 + s))
  rw [show δ = (1 - s) * (1 + s) by nlinarith [hsSq]]
  field_simp [hden]
  ring

@[simp] theorem xiShiftTangentBoundaryNormalRemainder_zero :
    xiShiftTangentBoundaryNormalRemainder 0 = -(7 / 8 : ℝ) := by
  norm_num [xiShiftTangentBoundaryNormalRemainder]

theorem continuousAt_xiShiftTangentBoundaryNormalRemainder_zero :
    ContinuousAt xiShiftTangentBoundaryNormalRemainder 0 := by
  unfold xiShiftTangentBoundaryNormalRemainder
  fun_prop (disch := norm_num)

/-- The polar lag is the stationary hyperbolic tangent kernel. -/
theorem xiShiftPolarLag_eq_cosh
    {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    xiShiftPolarLag p q =
      2 * Real.cosh (Real.log p - Real.log q) - 2 := by
  rw [xiShiftPolarLag, Real.cosh_eq]
  have hplog : Real.exp (Real.log p) = p := Real.exp_log hp
  have hqlog : Real.exp (Real.log q) = q := Real.exp_log hq
  rw [Real.exp_sub, Real.exp_neg, Real.exp_sub, hplog, hqlog]
  field_simp [hp.ne', hq.ne']
  ring

theorem xiShiftPolarLag_nonneg
    {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) :
    0 ≤ xiShiftPolarLag p q := by
  exact div_nonneg (sq_nonneg _) (mul_nonneg hp hq)

/-- Exact conversion from inverse-prime separation to the symmetric rooted
polar variables `A` and `u`. -/
theorem xiShiftTangentBoundaryDelta_eq_polarLag_mul_root
    (p q : Nat.Primes) :
    xiShiftTangentBoundaryDelta p q =
      xiShiftPolarLag (p : ℝ) (q : ℝ) *
          (((p : ℝ) * q)⁻¹) /
        (1 - ((p : ℝ) * q)⁻¹) ^ 2 := by
  have hp : (p : ℝ) ≠ 0 := by exact_mod_cast p.2.ne_zero
  have hq : (q : ℝ) ≠ 0 := by exact_mod_cast q.2.ne_zero
  have hpq : (p : ℝ) * q - 1 ≠ 0 := by
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast p.2.two_le
    have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast q.2.two_le
    nlinarith
  rw [xiShiftTangentBoundaryDelta_eq_primeRatio]
  unfold xiShiftPolarLag
  field_simp [hp, hq, hpq]

/-- Exact second-order response expansion after the rooted substitution
`δ = A u/(1-u)²`. -/
theorem rooted_xiShiftTangentBoundaryResponse_expansion
    {A u : ℝ} (hu : u ≠ 0) (hu1 : u ≠ 1)
    (hδ : A * u / (1 - u) ^ 2 ≤ 1) :
    (1 / u) *
        (1 - xiShiftTangentBoundaryResponse
          (A * u / (1 - u) ^ 2)) =
      (5 / 2 : ℝ) * A / (1 - u) ^ 2 +
        A ^ 2 * u / (1 - u) ^ 4 *
          xiShiftTangentBoundaryNormalRemainder
            (A * u / (1 - u) ^ 2) := by
  rw [one_sub_xiShiftTangentBoundaryResponse_eq hδ]
  field_simp [hu, sub_ne_zero.mpr hu1]

theorem rooted_xiShiftTangentBoundaryResponse_eq_firstNormalExtension
    {A u : ℝ} (hu : u ≠ 0) (hu1 : u ≠ 1)
    (hδ : A * u / (1 - u) ^ 2 ≤ 1) :
    (1 / u) *
        (1 - xiShiftTangentBoundaryResponse
          (A * u / (1 - u) ^ 2)) =
      xiShiftPolarFirstNormalExtension A u := by
  rw [rooted_xiShiftTangentBoundaryResponse_expansion hu hu1 hδ]
  rfl

/-- Exact finite-prime rooted polar expansion of the actual all-depth source
tangent correlation. -/
theorem primeRooted_xiShiftTangentKernel_defect_expansion
    (p q : Nat.Primes) :
    (p : ℝ) * q *
        (1 - gammaSewnXiShiftEndpointUnitTangentKernel p q) =
      (5 / 2 : ℝ) * xiShiftPolarLag (p : ℝ) q /
          (1 - ((p : ℝ) * q)⁻¹) ^ 2 +
        xiShiftPolarLag (p : ℝ) q ^ 2 *
            (((p : ℝ) * q)⁻¹) /
          (1 - ((p : ℝ) * q)⁻¹) ^ 4 *
            xiShiftTangentBoundaryNormalRemainder
              (xiShiftTangentBoundaryDelta p q) := by
  let u := (((p : ℝ) * q)⁻¹)
  let A := xiShiftPolarLag (p : ℝ) q
  have hpq0 : (p : ℝ) * q ≠ 0 := by
    exact mul_ne_zero (by exact_mod_cast p.2.ne_zero)
      (by exact_mod_cast q.2.ne_zero)
  have hu : u ≠ 0 := inv_ne_zero hpq0
  have hu1 : u ≠ 1 := by
    intro h
    have hprod : (p : ℝ) * q = 1 := inv_eq_one.mp h
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast p.2.two_le
    have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast q.2.two_le
    nlinarith
  have hsub :
      xiShiftTangentBoundaryDelta p q = A * u / (1 - u) ^ 2 := by
    simpa only [A, u] using
      xiShiftTangentBoundaryDelta_eq_polarLag_mul_root p q
  have hδ : A * u / (1 - u) ^ 2 ≤ 1 := by
    rw [← hsub]
    exact (xiShiftTangentBoundaryDelta_lt_one p q).le
  have hmain :=
    rooted_xiShiftTangentBoundaryResponse_expansion hu hu1 hδ
  rw [← hsub,
    ← gammaSewnXiShiftEndpointUnitTangentKernel_eq_boundaryResponse] at hmain
  have hone : 1 / u = (p : ℝ) * q := by
    dsimp only [u]
    field_simp [hpq0]
  rw [hone] at hmain
  simpa only [A, u] using hmain

/-- After subtracting the polar tangent and dividing by the next root scale,
the singular quotient equals its explicit continuous extension. -/
theorem rooted_xiShiftTangentBoundaryResponse_secondNormal_eq
    {A u : ℝ} (hu : u ≠ 0) (hu1 : u ≠ 1)
    (hδ : A * u / (1 - u) ^ 2 ≤ 1) :
    (1 / u) *
        ((1 / u) *
            (1 - xiShiftTangentBoundaryResponse
              (A * u / (1 - u) ^ 2)) -
          (5 / 2 : ℝ) * A) =
      xiShiftPolarSecondNormalExtension A u := by
  rw [rooted_xiShiftTangentBoundaryResponse_expansion hu hu1 hδ]
  unfold xiShiftPolarSecondNormalExtension
  field_simp [hu, sub_ne_zero.mpr hu1]
  ring

/-- Actual finite-prime second normal quotient, before passage to the
rooted boundary. -/
theorem primeRooted_xiShiftTangentKernel_secondNormal_eq
    (p q : Nat.Primes) :
    (p : ℝ) * q *
        ((p : ℝ) * q *
            (1 - gammaSewnXiShiftEndpointUnitTangentKernel p q) -
          (5 / 2 : ℝ) * xiShiftPolarLag (p : ℝ) q) =
      xiShiftPolarSecondNormalExtension
        (xiShiftPolarLag (p : ℝ) q) (((p : ℝ) * q)⁻¹) := by
  let u := (((p : ℝ) * q)⁻¹)
  let A := xiShiftPolarLag (p : ℝ) q
  have hpq0 : (p : ℝ) * q ≠ 0 := by
    exact mul_ne_zero (by exact_mod_cast p.2.ne_zero)
      (by exact_mod_cast q.2.ne_zero)
  have hu : u ≠ 0 := inv_ne_zero hpq0
  have hu1 : u ≠ 1 := by
    intro h
    have hprod : (p : ℝ) * q = 1 := inv_eq_one.mp h
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast p.2.two_le
    have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast q.2.two_le
    nlinarith
  have hsub :
      xiShiftTangentBoundaryDelta p q = A * u / (1 - u) ^ 2 := by
    simpa only [A, u] using
      xiShiftTangentBoundaryDelta_eq_polarLag_mul_root p q
  have hδ : A * u / (1 - u) ^ 2 ≤ 1 := by
    rw [← hsub]
    exact (xiShiftTangentBoundaryDelta_lt_one p q).le
  have hmain :=
    rooted_xiShiftTangentBoundaryResponse_secondNormal_eq hu hu1 hδ
  rw [← hsub,
    ← gammaSewnXiShiftEndpointUnitTangentKernel_eq_boundaryResponse] at hmain
  have hone : 1 / u = (p : ℝ) * q := by
    dsimp only [u]
    field_simp [hpq0]
  rw [hone] at hmain
  simpa only [A, u] using hmain

@[simp] theorem xiShiftPolarFirstNormalExtension_zero (A : ℝ) :
    xiShiftPolarFirstNormalExtension A 0 = (5 / 2 : ℝ) * A := by
  simp [xiShiftPolarFirstNormalExtension]

theorem continuousAt_xiShiftPolarFirstNormalExtension_zero (A : ℝ) :
    ContinuousAt (xiShiftPolarFirstNormalExtension A) 0 := by
  unfold xiShiftPolarFirstNormalExtension
  have hinner :
      ContinuousAt (fun u : ℝ => A * u / (1 - u) ^ 2) 0 := by
    fun_prop (disch := norm_num)
  have hrem :
      ContinuousAt
        (fun u : ℝ =>
          xiShiftTangentBoundaryNormalRemainder
            (A * u / (1 - u) ^ 2)) 0 := by
    change ContinuousAt
      (xiShiftTangentBoundaryNormalRemainder ∘
        fun u : ℝ => A * u / (1 - u) ^ 2) 0
    apply ContinuousAt.comp
      (f := fun u : ℝ => A * u / (1 - u) ^ 2)
      (g := xiShiftTangentBoundaryNormalRemainder)
    · simpa using
        continuousAt_xiShiftTangentBoundaryNormalRemainder_zero
    · exact hinner
  have hfirst :
      ContinuousAt
        (fun u : ℝ => (5 / 2 : ℝ) * A / (1 - u) ^ 2) 0 := by
    fun_prop (disch := norm_num)
  have hfactor :
      ContinuousAt (fun u : ℝ => A ^ 2 * u / (1 - u) ^ 4) 0 := by
    fun_prop (disch := norm_num)
  exact hfirst.add (hfactor.mul hrem)

/-- The unique symmetric rooted first quotient converges to the critical
polar tangent with Fisher coefficient `5/2`. -/
theorem tendsto_xiShiftPolarFirstNormalExtension_zero (A : ℝ) :
    Tendsto (xiShiftPolarFirstNormalExtension A) (𝓝 0)
      (𝓝 ((5 / 2 : ℝ) * A)) := by
  simpa using
    (continuousAt_xiShiftPolarFirstNormalExtension_zero A).tendsto

@[simp] theorem xiShiftPolarSecondNormalExtension_zero (A : ℝ) :
    xiShiftPolarSecondNormalExtension A 0 =
      xiShiftPolarSecondNormalCoefficient A := by
  simp [xiShiftPolarSecondNormalExtension,
    xiShiftPolarSecondNormalCoefficient]
  ring

theorem continuousAt_xiShiftPolarSecondNormalExtension_zero (A : ℝ) :
    ContinuousAt (xiShiftPolarSecondNormalExtension A) 0 := by
  unfold xiShiftPolarSecondNormalExtension
  have hinner :
      ContinuousAt (fun u : ℝ => A * u / (1 - u) ^ 2) 0 := by
    fun_prop (disch := norm_num)
  have hrem :
      ContinuousAt
        (fun u : ℝ =>
          xiShiftTangentBoundaryNormalRemainder
            (A * u / (1 - u) ^ 2)) 0 := by
    change ContinuousAt
      (xiShiftTangentBoundaryNormalRemainder ∘
        fun u : ℝ => A * u / (1 - u) ^ 2) 0
    apply ContinuousAt.comp
      (f := fun u : ℝ => A * u / (1 - u) ^ 2)
      (g := xiShiftTangentBoundaryNormalRemainder)
    · simpa using
        continuousAt_xiShiftTangentBoundaryNormalRemainder_zero
    · exact hinner
  have hfirst :
      ContinuousAt
        (fun u : ℝ => (5 / 2 : ℝ) * A * (2 - u) / (1 - u) ^ 2) 0 := by
    fun_prop (disch := norm_num)
  have hfactor :
      ContinuousAt (fun u : ℝ => A ^ 2 / (1 - u) ^ 4) 0 := by
    fun_prop (disch := norm_num)
  exact hfirst.add (hfactor.mul hrem)

/-- The next rooted quotient converges to the one-transition normal
coefficient. -/
theorem tendsto_xiShiftPolarSecondNormalExtension_zero (A : ℝ) :
    Tendsto (xiShiftPolarSecondNormalExtension A) (𝓝 0)
      (𝓝 (xiShiftPolarSecondNormalCoefficient A)) := by
  simpa using
    (continuousAt_xiShiftPolarSecondNormalExtension_zero A).tendsto

theorem xiShiftPolarSecondNormalCoefficient_factor (A : ℝ) :
    xiShiftPolarSecondNormalCoefficient A =
      A * (40 - 7 * A) / 8 := by
  unfold xiShiftPolarSecondNormalCoefficient
  ring

theorem xiShiftPolarSecondNormalCoefficient_pos_iff
    {A : ℝ} (hA : 0 < A) :
    0 < xiShiftPolarSecondNormalCoefficient A ↔ A < 40 / 7 := by
  rw [xiShiftPolarSecondNormalCoefficient_factor]
  constructor
  · intro h
    have h8 : (0 : ℝ) < 8 := by norm_num
    have hfactor : 0 < 40 - 7 * A := by
      by_contra hn
      have : 40 - 7 * A ≤ 0 := le_of_not_gt hn
      have : A * (40 - 7 * A) / 8 ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg
          (mul_nonpos_of_nonneg_of_nonpos hA.le this) (by norm_num)
      linarith
    nlinarith
  · intro h
    have hfactor : 0 < 40 - 7 * A := by nlinarith
    exact div_pos (mul_pos hA hfactor) (by norm_num)

theorem xiShiftPolarSecondNormalCoefficient_eq_zero_iff
    {A : ℝ} (hA : 0 ≤ A) :
    xiShiftPolarSecondNormalCoefficient A = 0 ↔
      A = 0 ∨ A = 40 / 7 := by
  rw [xiShiftPolarSecondNormalCoefficient_factor]
  constructor
  · intro h
    have hprod : A * (40 - 7 * A) = 0 := by
      exact (div_eq_zero_iff).mp h |>.resolve_right (by norm_num)
    rcases mul_eq_zero.mp hprod with hzero | hzero
    · exact Or.inl hzero
    · right
      linarith
  · rintro (rfl | rfl) <;> norm_num

end

end RHTower
