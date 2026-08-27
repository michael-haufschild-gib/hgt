import GaloisForLFunctions.RHTower.ThetaCuspHawkingParikhWilczekSignedMatrixThreeMomentClassification

/-!
# Parikh--Wilczek quadratic half-line receiver cone

This file classifies exactly when a real quadratic is strictly positive on the open half-line
`(1,∞)`.  The four chambers are determined by leading coefficient, vertex position, boundary
value, and discriminant.  Applying this classifier to the three PW signed matrix moments produces
a complete uniform finite-matrix receiver cone.

Every Xi divisor has PW spectral coordinate strictly greater than one.  Hence any coupling in this
cone has no residual counterfeit roots: its cross-grade energy vanishes exactly on the critical
wall, and universal vanishing is exactly RH.

`[NEW] [CLASSIFICATION] [EXACT RECEIVER CONE] [PAPER-PROVED] [LEAN-PROVED]`
-/

open Complex Filter Topology

namespace RHTower

noncomputable section

/-- Four semialgebraic chambers for strict positivity of `a*x^2+b*x+c` on `x>1`. -/
def quadraticPositiveOnOneCondition (a b c : ℝ) : Prop :=
  (0 < a ∧
    ((-2 * a ≤ b ∧ 0 ≤ a + b + c) ∨
      (b < -2 * a ∧ b ^ 2 < 4 * a * c))) ∨
  (a = 0 ∧
    ((0 < b ∧ 0 ≤ b + c) ∨
      (b = 0 ∧ 0 < c)))

/-- Half-line positivity forces the quadratic leading coefficient to be nonnegative. -/
theorem quadratic_leading_nonneg_of_pos_on_one
    {a b c : ℝ} (h : ∀ x : ℝ, 1 < x → 0 < a * x ^ 2 + b * x + c) :
    0 ≤ a := by
  have ht : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hlim : Tendsto
      (fun n : ℕ => a + b * (1 / ((n : ℝ) + 1)) +
        c * (1 / ((n : ℝ) + 1)) ^ 2) atTop (nhds a) := by
    simpa using (tendsto_const_nhds.add
      (tendsto_const_nhds.mul ht)).add
        (tendsto_const_nhds.mul (ht.pow 2))
  apply ge_of_tendsto hlim
  filter_upwards [eventually_atTop.2 ⟨1, fun n hn => hn⟩] with n hn
  have hx : (1 : ℝ) < (n : ℝ) + 1 := by exact_mod_cast Nat.lt_add_one_iff.mpr hn
  have hden : 0 < ((n : ℝ) + 1) ^ 2 := sq_pos_of_pos (by positivity)
  have hq := (h ((n : ℝ) + 1) hx).le
  have hdiv : 0 ≤ (a * ((n : ℝ) + 1) ^ 2 + b * ((n : ℝ) + 1) + c) /
      ((n : ℝ) + 1) ^ 2 := div_nonneg hq hden.le
  have heq : (a * ((n : ℝ) + 1) ^ 2 + b * ((n : ℝ) + 1) + c) /
      ((n : ℝ) + 1) ^ 2 =
      a + b * (1 / ((n : ℝ) + 1)) + c * (1 / ((n : ℝ) + 1)) ^ 2 := by
    field_simp
  rw [← heq]
  exact hdiv

/-- Half-line positivity of a linear polynomial forces nonnegative slope. -/
theorem quadratic_linear_nonneg_of_pos_on_one
    {b c : ℝ} (h : ∀ x : ℝ, 1 < x → 0 < b * x + c) :
    0 ≤ b := by
  have ht : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hlim : Tendsto
      (fun n : ℕ => b + c * (1 / ((n : ℝ) + 1))) atTop (nhds b) := by
    simpa using tendsto_const_nhds.add (tendsto_const_nhds.mul ht)
  apply ge_of_tendsto hlim
  filter_upwards [eventually_atTop.2 ⟨1, fun n hn => hn⟩] with n hn
  have hx : (1 : ℝ) < (n : ℝ) + 1 := by exact_mod_cast Nat.lt_add_one_iff.mpr hn
  have hden : 0 < (n : ℝ) + 1 := by positivity
  have hq := (h ((n : ℝ) + 1) hx).le
  have hdiv : 0 ≤ (b * ((n : ℝ) + 1) + c) / ((n : ℝ) + 1) :=
    div_nonneg hq hden.le
  have heq : (b * ((n : ℝ) + 1) + c) / ((n : ℝ) + 1) =
      b + c * (1 / ((n : ℝ) + 1)) := by
    field_simp
  rw [← heq]
  exact hdiv

/-- Strict positivity immediately right of one forces nonnegative boundary value at one. -/
theorem quadratic_boundary_nonneg_of_pos_on_one
    {a b c : ℝ} (h : ∀ x : ℝ, 1 < x → 0 < a * x ^ 2 + b * x + c) :
    0 ≤ a + b + c := by
  have ht : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hcont : ContinuousAt
      (fun t : ℝ => a * (1 + t) ^ 2 + b * (1 + t) + c) 0 := by fun_prop
  have hlim : Tendsto
      (fun n : ℕ => a * (1 + 1 / ((n : ℝ) + 1)) ^ 2 +
        b * (1 + 1 / ((n : ℝ) + 1)) + c) atTop (nhds (a + b + c)) := by
    simpa [Function.comp_def] using hcont.tendsto.comp ht
  apply ge_of_tendsto hlim
  apply Filter.Eventually.of_forall
  intro n
  have htpos : 0 < (1 : ℝ) / ((n : ℝ) + 1) := by positivity
  exact (h (1 + 1 / ((n : ℝ) + 1)) (by linarith)).le

/-- Exact semialgebraic classification of strict quadratic positivity on `(1,∞)`. -/
theorem quadratic_pos_on_one_iff (a b c : ℝ) :
    (∀ x : ℝ, 1 < x → 0 < a * x ^ 2 + b * x + c) ↔
      quadraticPositiveOnOneCondition a b c := by
  constructor
  · intro h
    have ha0 := quadratic_leading_nonneg_of_pos_on_one h
    rcases ha0.eq_or_lt with ha | ha
    · right
      have ha' : a = 0 := ha.symm
      refine ⟨ha', ?_⟩
      have hb0 : 0 ≤ b := quadratic_linear_nonneg_of_pos_on_one fun x hx => by
        simpa [ha'] using h x hx
      rcases hb0.eq_or_lt with hb | hb
      · right
        have hb' : b = 0 := hb.symm
        refine ⟨hb', ?_⟩
        simpa [ha', hb'] using h 2 (by norm_num)
      · left
        exact ⟨hb, by simpa [ha'] using quadratic_boundary_nonneg_of_pos_on_one h⟩
    · left
      refine ⟨ha, ?_⟩
      by_cases hb : -2 * a ≤ b
      · left
        exact ⟨hb, quadratic_boundary_nonneg_of_pos_on_one h⟩
      · right
        have hb' : b < -2 * a := lt_of_not_ge hb
        refine ⟨hb', ?_⟩
        let v : ℝ := -b / (2 * a)
        have hv : 1 < v := by
          dsimp [v]
          apply (lt_div_iff₀ (by positivity)).mpr
          linarith
        have hq := h v hv
        have hid : 4 * a * (a * v ^ 2 + b * v + c) = 4 * a * c - b ^ 2 := by
          dsimp [v]
          field_simp
          ring
        nlinarith
  · intro h x hx
    rcases h with ⟨ha, hcase⟩ | ⟨ha, hcase⟩
    · rcases hcase with ⟨hb, hboundary⟩ | ⟨hb, hdisc⟩
      · have hfactor : 0 < (x - 1) * (a * (x + 1) + b) := by
          apply mul_pos (by linarith)
          have : 2 < x + 1 := by linarith
          nlinarith
        nlinarith [hfactor]
      · have hsquare : 0 ≤ (2 * a * x + b) ^ 2 := sq_nonneg _
        have ha4 : 0 < 4 * a := by positivity
        have hid : 4 * a * (a * x ^ 2 + b * x + c) =
            (2 * a * x + b) ^ 2 + (4 * a * c - b ^ 2) := by ring
        nlinarith
    · rcases hcase with ⟨hb, hboundary⟩ | ⟨hb, hc⟩
      · rw [ha, zero_mul, zero_add]
        have : 0 < b * (x - 1) := mul_pos hb (by linarith)
        nlinarith
      · simp [ha, hb, hc]


/-- Complete uniform half-line receiver cone for finite signed PW matrix couplings. -/
def schwarzschildParikhWilczekSignedMatrixReceiverCone
    {N : ℕ} (M : Fin N → Fin N → ℝ) : Prop :=
  quadraticPositiveOnOneCondition
    (schwarzschildParikhWilczekSignedMatrixMomentZero M)
    (schwarzschildParikhWilczekSignedMatrixMomentOne M)
    (schwarzschildParikhWilczekSignedMatrixMomentTwo M)

/-- Receiver-cone membership is exactly positivity of the moment quadratic on `x>1`. -/
theorem schwarzschildParikhWilczekSignedMatrixReceiverCone_iff
    {N : ℕ} (M : Fin N → Fin N → ℝ) :
    schwarzschildParikhWilczekSignedMatrixReceiverCone M ↔
      ∀ x : ℝ, 1 < x →
        0 < schwarzschildParikhWilczekSignedMatrixMomentZero M * x ^ 2 +
          schwarzschildParikhWilczekSignedMatrixMomentOne M * x +
          schwarzschildParikhWilczekSignedMatrixMomentTwo M := by
  exact (quadratic_pos_on_one_iff _ _ _).symm

/-- Every actual Xi divisor has PW spectral coordinate strictly above one. -/
theorem schwarzschildParikhWilczekBorelSpectralCoordinate_gt_one
    (rho : XiDivisorSupport) :
    1 < schwarzschildParikhWilczekBorelSpectralCoordinate (rho : ℂ) := by
  obtain ⟨hre0, hre1⟩ := xi_divisor_support_re_mem_open_unit rho
  have hreprod : 0 < (rho : ℂ).re * (1 - (rho : ℂ).re) :=
    mul_pos hre0 (sub_pos.mpr hre1)
  have himsq : 0 < (rho : ℂ).im ^ 2 :=
    sq_pos_of_ne_zero (xi_divisor_support_im_ne_zero rho)
  rw [schwarzschildParikhWilczekBorelSpectralCoordinate]
  linarith

/-- Couplings in the receiver cone have positive residual at every actual Xi divisor. -/
theorem schwarzschildParikhWilczekSignedMatrixResidualPolynomial_pos
    {N : ℕ} {M : Fin N → Fin N → ℝ}
    (hcone : schwarzschildParikhWilczekSignedMatrixReceiverCone M)
    (rho : XiDivisorSupport) :
    0 < schwarzschildParikhWilczekSignedMatrixResidualPolynomial M (rho : ℂ) := by
  rw [schwarzschildParikhWilczekSignedMatrixResidualPolynomial]
  exact (schwarzschildParikhWilczekSignedMatrixReceiverCone_iff M).mp hcone
    (schwarzschildParikhWilczekBorelSpectralCoordinate (rho : ℂ))
    (schwarzschildParikhWilczekBorelSpectralCoordinate_gt_one rho)

/-- Within the receiver cone, pointwise energy vanishing is exactly critical-wall placement. -/
theorem schwarzschildParikhWilczekMatrixCrossGradeEnergy_eq_zero_iff_of_receiverCone
    {N : ℕ} {M : Fin N → Fin N → ℝ}
    (hcone : schwarzschildParikhWilczekSignedMatrixReceiverCone M)
    (rho : XiDivisorSupport) :
    schwarzschildParikhWilczekMatrixCrossGradeEnergy M (rho : ℂ) = 0 ↔
      (rho : ℂ).re = 1 / 2 := by
  rw [schwarzschildParikhWilczekMatrixCrossGradeEnergy_eq_zero_iff_wall_or_residual]
  have hres :=
    schwarzschildParikhWilczekSignedMatrixResidualPolynomial_pos hcone rho
  constructor
  · rintro (hwall | hzero)
    · exact hwall
    · exact False.elim (hres.ne' hzero)
  · exact Or.inl

/-- Universal vanishing for any signed coupling in the receiver cone is exactly RH. -/
theorem riemannHypothesis_iff_schwarzschildParikhWilczekSignedMatrixCrossGradeEnergy_zero
    {N : ℕ} {M : Fin N → Fin N → ℝ}
    (hcone : schwarzschildParikhWilczekSignedMatrixReceiverCone M) :
    RiemannHypothesis ↔
      ∀ rho : XiDivisorSupport,
        schwarzschildParikhWilczekMatrixCrossGradeEnergy M (rho : ℂ) = 0 := by
  constructor
  · intro hRH rho
    exact (schwarzschildParikhWilczekMatrixCrossGradeEnergy_eq_zero_iff_of_receiverCone
      hcone rho).mpr (xi_divisor_support_re_eq_half_of_rh hRH rho)
  · intro h
    exact riemannHypothesis_of_forall_xiDivisorSupport_re_eq_half fun rho =>
      (schwarzschildParikhWilczekMatrixCrossGradeEnergy_eq_zero_iff_of_receiverCone
        hcone rho).mp (h rho)

end

end RHTower
