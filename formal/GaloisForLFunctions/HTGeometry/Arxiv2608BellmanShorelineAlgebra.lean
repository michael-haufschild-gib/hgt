import Mathlib

/-!
# Algebraic mechanics from arXiv:2608.29060

This module formalizes reusable exact identities from *Bellman--Shoreline Search in Arbitrary
Dimension: Exponential Vector Oscillators, Active Memory, Precession, and Effective Computability*.
It contains no numerical screening and assumes no optimal-shape ansatz.

The results cover the one-dimensional stationary optimum, equivariant drift cancellation,
exponential supplier memory, orthogonal speed splitting, regular-chamber envelope and pitch laws,
the no-breathing/just-in-time equivalence, and normalized harmonic-tower projection.
-/

noncomputable section

open Filter Topology
open scoped BigOperators NNReal

namespace GaloisForLFunctions.HTGeometry

/-! ## Dimension one: exact stationary minimax algebra -/

/-- Stationary competitive ratio of a multiplicative one-dimensional zigzag. -/
def bellmanShorelineStationaryRatio (rho : ℝ) : ℝ :=
  1 + 2 * rho ^ 2 / (rho - 1)

/-- Exact square decomposition behind the stationary lower bound `9`. -/
theorem bellmanShorelineStationaryRatio_sub_nine (rho : ℝ) (hrho : rho ≠ 1) :
    bellmanShorelineStationaryRatio rho - 9 = 2 * (rho - 2) ^ 2 / (rho - 1) := by
  rw [bellmanShorelineStationaryRatio]
  field_simp
  ring

/-- Every productive stationary multiplicative schedule has ratio at least `9`. -/
theorem nine_le_bellmanShorelineStationaryRatio (rho : ℝ) (hrho : 1 < rho) :
    9 ≤ bellmanShorelineStationaryRatio rho := by
  rw [← sub_nonneg]
  rw [bellmanShorelineStationaryRatio_sub_nine rho (ne_of_gt hrho)]
  positivity

/-- Doubling is the unique productive stationary scale factor attaining ratio `9`. -/
theorem bellmanShorelineStationaryRatio_eq_nine_iff (rho : ℝ) (hrho : 1 < rho) :
    bellmanShorelineStationaryRatio rho = 9 ↔ rho = 2 := by
  constructor
  · intro h
    have hzero : 2 * (rho - 2) ^ 2 / (rho - 1) = 0 := by
      rw [← bellmanShorelineStationaryRatio_sub_nine rho (ne_of_gt hrho), h]
      norm_num
    have hsquare : (rho - 2) ^ 2 = 0 := by
      rcases div_eq_zero_iff.mp hzero with hnum | hden
      · exact (mul_eq_zero.mp hnum).resolve_left (by norm_num)
      · exact absurd hden (sub_ne_zero.mpr (ne_of_gt hrho))
    nlinarith [sq_nonneg (rho - 2)]
  · rintro rfl
    norm_num [bellmanShorelineStationaryRatio]

/-- Positive-side asymptotic ripple for a two-amplitude stationary cell. -/
def bellmanShorelineRipplePlus (A B q : ℝ) : ℝ :=
  1 + 2 * (q * (A + B)) / (A * (q - 1))

/-- Negative-side asymptotic ripple for a two-amplitude stationary cell. -/
def bellmanShorelineRippleMinus (A B q : ℝ) : ℝ :=
  1 + 2 * (q * (A * q + B)) / (B * (q - 1))

/-- Equal ripple is exactly the geometric-mean relation `B² = A²q`. -/
theorem bellmanShorelineRipple_eq_iff (A B q : ℝ)
    (hA : A ≠ 0) (hB : B ≠ 0) (hq : q ≠ 0) (hq1 : q ≠ 1) :
    bellmanShorelineRipplePlus A B q = bellmanShorelineRippleMinus A B q ↔
      B ^ 2 = A ^ 2 * q := by
  constructor
  · intro h
    have h' := h
    simp only [bellmanShorelineRipplePlus, bellmanShorelineRippleMinus] at h'
    field_simp [hA, hB, hq1] at h'
    have hfactor : 2 * q * (B ^ 2 - A ^ 2 * q) = 0 := by
      calc
        2 * q * (B ^ 2 - A ^ 2 * q) =
            B * (A * (q - 1) + 2 * q * (A + B)) -
              A * (B * (q - 1) + 2 * q * (q * A + B)) := by ring
        _ = 0 := sub_eq_zero.mpr h'
    have hdiff : B ^ 2 - A ^ 2 * q = 0 := by
      exact (mul_eq_zero.mp hfactor).resolve_left (mul_ne_zero (by norm_num) hq)
    exact sub_eq_zero.mp hdiff
  · intro h
    simp only [bellmanShorelineRipplePlus, bellmanShorelineRippleMinus]
    field_simp [hA, hB, hq1]
    linear_combination 2 * q * h

/-! ## Equivariant cells and exponential memory -/

/-- Lifted radial/angular data of an equivariant planar cell. -/
structure BellmanShorelineEquivariantCocycle where
  rho : ℝ → ℝ
  theta : ℝ → ℝ
  period : ℝ
  radialDrift : ℝ
  angularDrift : ℝ
  angularDrift_ne : angularDrift ≠ 0
  rho_shift : ∀ s, rho (s + period) = rho s + radialDrift
  theta_shift : ∀ s, theta (s + period) = theta s + angularDrift

/-- Scale-corrected angular profile of an equivariant cell. -/
def BellmanShorelineEquivariantCocycle.secularFree
    (c : BellmanShorelineEquivariantCocycle) (s : ℝ) : ℝ :=
  c.rho s - (c.radialDrift / c.angularDrift) * c.theta s

/-- Removing mean pitch cancels every secular drift over one equivariant cell. -/
theorem BellmanShorelineEquivariantCocycle.secularFree_periodic
    (c : BellmanShorelineEquivariantCocycle) (s : ℝ) :
    c.secularFree (s + c.period) = c.secularFree s := by
  unfold BellmanShorelineEquivariantCocycle.secularFree
  rw [c.rho_shift, c.theta_shift]
  field_simp [c.angularDrift_ne]
  ring

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A historical supplier viewed at present exponential scale. -/
def bellmanShorelineDiscountedSupplier
    (kappa : ℝ) (omega : ℝ → E) (sigma tau : ℝ) : E :=
  Real.exp (-kappa * tau) • omega (sigma - tau)

/-- Aging memory in two stages equals aging once by the total age. -/
theorem bellmanShorelineDiscountedSupplier_add
    (kappa : ℝ) (omega : ℝ → E) (sigma tau age : ℝ) :
    bellmanShorelineDiscountedSupplier kappa omega sigma (tau + age) =
      Real.exp (-kappa * tau) •
        bellmanShorelineDiscountedSupplier kappa omega (sigma - tau) age := by
  rw [bellmanShorelineDiscountedSupplier, bellmanShorelineDiscountedSupplier]
  rw [← mul_smul, ← Real.exp_add]
  congr 1 <;> ring_nf

/-- A sphere-valued supplier has exactly the exponential discount as its norm. -/
theorem norm_bellmanShorelineDiscountedSupplier
    (kappa : ℝ) (omega : ℝ → E) (hunit : ∀ s, ‖omega s‖ = 1) (sigma tau : ℝ) :
    ‖bellmanShorelineDiscountedSupplier kappa omega sigma tau‖ =
      Real.exp (-kappa * tau) := by
  rw [bellmanShorelineDiscountedSupplier, norm_smul, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _), hunit, mul_one]

/-- Positive discount makes every unit-sphere supplier converge to origin at infinite age. -/
theorem bellmanShorelineDiscountedSupplier_tendsto_atTop_zero
    {kappa : ℝ} (hkappa : 0 < kappa) (omega : ℝ → E)
    (hunit : ∀ s, ‖omega s‖ = 1) (sigma : ℝ) :
    Tendsto
      (fun tau : ℝ≥0 => bellmanShorelineDiscountedSupplier kappa omega sigma tau)
      atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simp_rw [norm_bellmanShorelineDiscountedSupplier kappa omega hunit]
  have hcoe : Tendsto (fun tau : ℝ≥0 => (tau : ℝ)) atTop atTop :=
    NNReal.tendsto_coe_atTop.mpr tendsto_id
  apply Real.tendsto_exp_atBot.comp
  simpa [mul_comm] using
    hcoe.const_mul_atTop_of_neg (neg_lt_zero.mpr hkappa)

/-- Historical supplier depends continuously on nonnegative age when directional motion is
continuous. -/
theorem bellmanShorelineDiscountedSupplier_continuous
    (kappa : ℝ) {omega : ℝ → E} (homega : Continuous omega) (sigma : ℝ) :
    Continuous
      (fun tau : ℝ≥0 => bellmanShorelineDiscountedSupplier kappa omega sigma tau) := by
  unfold bellmanShorelineDiscountedSupplier
  fun_prop

/-- One physical exponential orbit produces all scalar directional channels by projection. -/
theorem bellmanShorelineExponential_projection
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (kappa sigma : ℝ) (omega u : F) :
    inner ℝ u (Real.exp (kappa * sigma) • omega) =
      Real.exp (kappa * sigma) * inner ℝ u omega := by
  rw [real_inner_smul_right]

/-! ## Directional kinematics and chamber identities -/

/-- Orthogonal scale and directional velocities satisfy the Pythagorean speed split. -/
theorem bellmanShorelineOrthogonal_speed_sq
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (kappa : ℝ) (omega tangent : F) (horth : inner ℝ omega tangent = 0) :
    ‖kappa • omega + tangent‖ ^ 2 =
      kappa ^ 2 * ‖omega‖ ^ 2 + ‖tangent‖ ^ 2 := by
  rw [norm_add_sq_real, norm_smul, Real.norm_eq_abs]
  rw [real_inner_smul_left, horth, mul_zero, mul_zero, add_zero]
  nlinarith [sq_abs kappa]

/-- Recursive hyperspherical coordinates split latitude and lower-sphere speeds orthogonally. -/
theorem bellmanShorelineHyperspherical_speed_sq
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (phi phi' tau' : ℝ) (omega tangent : F)
    (hunit : ‖omega‖ = 1) (htangent : ‖tangent‖ = 1)
    (horth : inner ℝ omega tangent = 0) :
    ‖(-Real.sin phi * phi') • omega + (Real.cos phi * phi') • (0 : F)‖ ^ 2 +
        ‖(Real.cos phi * phi') • omega + (Real.sin phi * tau') • tangent‖ ^ 2 =
      phi' ^ 2 + Real.sin phi ^ 2 * tau' ^ 2 := by
  simp only [smul_zero, add_zero]
  rw [bellmanShorelineOrthogonal_speed_sq
    (Real.cos phi * phi') omega ((Real.sin phi * tau') • tangent) (by
      rw [real_inner_smul_right, horth, mul_zero])]
  simp only [norm_smul, hunit, htangent, mul_one, Real.norm_eq_abs, mul_pow, sq_abs]
  nlinarith [Real.sin_sq_add_cos_sq phi]

/-- Algebraic balance behind the regular-chamber bottleneck envelope law. -/
theorem bellmanShorelineBottleneckEnvelopeLaw
    (kappa mu mu' beta current radialVelocity : ℝ)
    (hcurrent : current = mu)
    (hbalance : mu' = beta * radialVelocity - (1 - beta) * kappa * mu) :
    mu' + kappa * mu = beta * (kappa * current + radialVelocity) := by
  rw [hcurrent, hbalance]
  ring

/-- Stationarity plus the active-foot envelope derivative forces the barycentric mean age. -/
theorem bellmanShorelinePitchIdentity
    (kappa mu muKappa meanAge : ℝ)
    (hkappa : kappa ≠ 0) (hmu : mu ≠ 0)
    (hstationary : kappa / (1 + kappa ^ 2) - 1 / kappa - muKappa / mu = 0)
    (henvelope : muKappa = -mu * meanAge) :
    meanAge = 1 / (kappa * (1 + kappa ^ 2)) := by
  field_simp [hkappa, hmu, sq_nonneg kappa] at hstationary ⊢
  rw [henvelope] at hstationary
  field_simp [hmu] at hstationary
  nlinarith

/-- Physical time of a unit-speed exponential directional orbit. -/
def bellmanShorelinePhysicalTime (kappa sigma : ℝ) : ℝ :=
  Real.sqrt (1 + kappa ^ 2) / kappa * Real.exp (kappa * sigma)

/-- Physical common margin associated with a normalized bottleneck. -/
def bellmanShorelinePhysicalMargin
    (kappa : ℝ) (mu : ℝ → ℝ) (sigma : ℝ) : ℝ :=
  Real.exp (kappa * sigma) * mu sigma

/-- Constant normalized bottleneck at competitive ratio `C`. -/
def BellmanShorelineNoBreathing (kappa C : ℝ) (mu : ℝ → ℝ) : Prop :=
  ∀ sigma, mu sigma = Real.sqrt (1 + kappa ^ 2) / (kappa * C)

/-- Physical common margin is delivered exactly at its linear deadline. -/
def BellmanShorelineJustInTime (kappa C : ℝ) (mu : ℝ → ℝ) : Prop :=
  ∀ sigma,
    bellmanShorelinePhysicalMargin kappa mu sigma -
      bellmanShorelinePhysicalTime kappa sigma / C = 0

/-- No breathing in normalized scale is equivalent to just-in-time physical saturation. -/
theorem bellmanShorelineNoBreathing_iff_justInTime
    (kappa C : ℝ) (mu : ℝ → ℝ) (hkappa : kappa ≠ 0) (hC : C ≠ 0) :
    BellmanShorelineNoBreathing kappa C mu ↔
      BellmanShorelineJustInTime kappa C mu := by
  constructor
  · intro h sigma
    rw [bellmanShorelinePhysicalMargin, bellmanShorelinePhysicalTime, h sigma]
    field_simp [hkappa, hC]
    ring
  · intro h sigma
    have hs := h sigma
    rw [bellmanShorelinePhysicalMargin, bellmanShorelinePhysicalTime] at hs
    field_simp [hkappa, hC] at hs ⊢
    have hexp := Real.exp_ne_zero (kappa * sigma)
    apply (mul_left_cancel₀ hexp)
    nlinarith

/-! ## Harmonic-tower projection -/

/-- Normalizing after dropping added coordinates recovers the previous normalized direction. -/
theorem bellmanShorelineNormalizedProjection
    {F G : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (w : F) (extra : G) (hw : w ≠ 0) :
    NormedSpace.normalize (NormedSpace.normalize (w, extra)).1 =
      NormedSpace.normalize w := by
  change NormedSpace.normalize (‖(w, extra)‖⁻¹ • w) = NormedSpace.normalize w
  rw [NormedSpace.normalize_smul_of_pos]
  apply inv_pos.mpr
  apply norm_pos_iff.mpr
  intro hpair
  exact hw (congrArg Prod.fst hpair)

/-- `2m+1` is the first possible positive odd frequency after `1,3,…,2m-1`. -/
theorem bellmanShorelineFirstAvailableOddFrequency
    (m k : ℕ) (hk : Odd k) (habsent : ∀ j < m, k ≠ 2 * j + 1) :
    2 * m + 1 ≤ k := by
  obtain ⟨r, rfl⟩ := hk
  by_contra hlt
  have hr : r < m := by omega
  exact habsent r hr rfl

end GaloisForLFunctions.HTGeometry

end
