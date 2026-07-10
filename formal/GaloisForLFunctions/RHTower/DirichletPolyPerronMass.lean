import GaloisForLFunctions.RHTower.PerronCarrierFlankMass
import GaloisForLFunctions.RHTower.ZetaCarrier

/-!
# Unconditional Perron mass for finite Dirichlet carriers

The finite Dirichlet carrier has no analytic mass hypotheses.  On the negative line `Re s = -M`,
each term has norm `n^M`; on the whole strip `-M ≤ Re s`, the same finite sum is a uniform bound.
The universal weight `(1+t²)⁻¹` therefore supplies both carrier-mass interfaces.  The finite
coefficient sequence is also summable everywhere and its `LSeries` is exactly `dirichletPoly N`, so
the resulting Perron boundary-charge theorem has no Prop-valued interface inputs.
-/

noncomputable section

namespace RHTower

open Complex Real Filter Topology MeasureTheory Set

/-- The exact uniform norm budget for `dirichletPoly N` on `Re s ≥ -M`. -/
noncomputable def dirichletPolyPerronBudget (N M : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (M : ℝ)

/-- On the negative-integer flank, every finite Dirichlet term has norm exactly `n^M`. -/
theorem norm_dirichletPoly_neg_line_le (N M : ℕ) (y : ℝ) :
    ‖dirichletPoly N (↑(-(M : ℝ)) + ↑y * I)‖ ≤ dirichletPolyPerronBudget N M := by
  have hterm : ∀ n ∈ Finset.Icc 1 N,
      ‖(n : ℂ) ^ (-(↑(-(M : ℝ)) + ↑y * I))‖ = (n : ℝ) ^ (M : ℝ) := by
    intro n hn
    have hpos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (Finset.mem_Icc.mp hn).1
    rw [← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hpos]
    congr 1
    simp
  unfold dirichletPoly dirichletPolyPerronBudget
  calc
    ‖∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-(↑(-(M : ℝ)) + ↑y * I))‖
        ≤ ∑ n ∈ Finset.Icc 1 N, ‖(n : ℂ) ^ (-(↑(-(M : ℝ)) + ↑y * I))‖ :=
      norm_sum_le _ _
    _ = ∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (M : ℝ) := Finset.sum_congr rfl hterm

/-- A uniform vertical-line bound constructs the weighted Perron flank-mass interface. -/
theorem hasPerronCarrierFlankMassAt_of_uniform_norm_le
    {F : ℂ → ℂ} {M : ℕ} {C : ℝ}
    (hF : Continuous F)
    (hbound : ∀ y : ℝ, ‖F (↑(-(M : ℝ)) + ↑y * I)‖ ≤ C) :
    HasPerronCarrierFlankMassAt F M (C * Real.pi) := by
  let w : ℝ → ℝ := fun y => (1 + y ^ 2)⁻¹
  have hwInt : Integrable w := by simpa only [w] using integrable_inv_one_add_sq
  have hdomInt : Integrable (fun y : ℝ => C * w y) := hwInt.const_mul C
  have hmassCont : Continuous (perronCarrierFlankWeight F M) := by
    unfold perronCarrierFlankWeight
    exact ((hF.comp (by fun_prop)).norm).div₀ (by fun_prop) (fun y => by positivity)
  have hpoint : ∀ y : ℝ, perronCarrierFlankWeight F M y ≤ C * w y := by
    intro y
    unfold perronCarrierFlankWeight w
    exact div_le_div_of_nonneg_right (hbound y) (by positivity)
  have hmassInt : Integrable (perronCarrierFlankWeight F M) :=
    hdomInt.mono' hmassCont.aestronglyMeasurable (Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by unfold perronCarrierFlankWeight; positivity)]
      exact hpoint y)
  refine ⟨hmassInt, ?_⟩
  calc
    (∫ y : ℝ, perronCarrierFlankWeight F M y) ≤ ∫ y : ℝ, C * w y :=
      integral_mono hmassInt hdomInt hpoint
    _ = C * Real.pi := by rw [integral_const_mul]; simp only [w, integral_univ_inv_one_add_sq]

/-- The weighted left-flank mass of a finite Dirichlet carrier is unconditional. -/
theorem dirichletPoly_hasPerronCarrierFlankMassAt (N M : ℕ) :
    HasPerronCarrierFlankMassAt (dirichletPoly N) M
      (dirichletPolyPerronBudget N M * Real.pi) :=
  hasPerronCarrierFlankMassAt_of_uniform_norm_le
    (dirichletPoly_differentiable N).continuous (norm_dirichletPoly_neg_line_le N M)

/-- The same finite budget controls every vertical line in the half-plane `Re s ≥ -M`. -/
theorem norm_dirichletPoly_vertical_strip_le (N M : ℕ) {x T : ℝ}
    (hx : -(M : ℝ) ≤ x) :
    ‖dirichletPoly N (↑x + ↑T * I)‖ ≤ dirichletPolyPerronBudget N M := by
  have hterm : ∀ n ∈ Finset.Icc 1 N,
      ‖(n : ℂ) ^ (-(↑x + ↑T * I))‖ ≤ (n : ℝ) ^ (M : ℝ) := by
    intro n hn
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hn).1
    have hpos : (0 : ℝ) < (n : ℝ) := lt_of_lt_of_le zero_lt_one hn1
    rw [← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hpos]
    apply Real.rpow_le_rpow_of_exponent_le hn1
    simpa using (neg_le_neg hx)
  unfold dirichletPoly dirichletPolyPerronBudget
  calc
    ‖∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-(↑x + ↑T * I))‖
        ≤ ∑ n ∈ Finset.Icc 1 N, ‖(n : ℂ) ^ (-(↑x + ↑T * I))‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (M : ℝ) := Finset.sum_le_sum hterm

/-- A uniform strip bound constructs the weighted horizontal Perron-mass interface. -/
theorem hasPerronCarrierHorizontalMassAt_of_uniform_strip_norm_le
    {F : ℂ → ℂ} {c C : ℝ} {M : ℕ}
    (hF : Continuous F) (hMc : -(M : ℝ) ≤ c) (hC : 0 ≤ C)
    (hbound : ∀ x ∈ Set.Icc (-(M : ℝ)) c, ∀ T : ℝ,
      ‖F (↑x + ↑T * I)‖ ≤ C) :
    HasPerronCarrierHorizontalMassAt F c M := by
  let K : ℝ := (c + (M : ℝ)) * (2 * C)
  have hlength : 0 ≤ c + (M : ℝ) := by linarith
  have hK : 0 ≤ K := by
    dsimp [K]
    exact mul_nonneg hlength (mul_nonneg (by norm_num) hC)
  have hmassCont : Continuous (perronCarrierHorizontalWeight F c M) := by
    unfold perronCarrierHorizontalWeight
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    have hnum : Continuous (Function.uncurry fun T x : ℝ =>
        ‖F (↑x + ↑T * I)‖ + ‖F (↑x + ↑(-T) * I)‖) := by
      fun_prop
    exact hnum.div₀ (by fun_prop) (fun p => by positivity)
  have hmassNonneg : ∀ T : ℝ, 0 ≤ perronCarrierHorizontalWeight F c M T := by
    intro T
    unfold perronCarrierHorizontalWeight
    exact intervalIntegral.integral_nonneg hMc fun x _ => by positivity
  have hpoint : ∀ T : ℝ,
      perronCarrierHorizontalWeight F c M T ≤ K * (1 + T ^ 2)⁻¹ := by
    intro T
    have hint : IntervalIntegrable
        (fun x : ℝ => (‖F (↑x + ↑T * I)‖ + ‖F (↑x + ↑(-T) * I)‖) / (1 + T ^ 2))
        volume (-(M : ℝ)) c := by
      apply Continuous.intervalIntegrable
      fun_prop
    have hconst : IntervalIntegrable (fun _ : ℝ => (2 * C) / (1 + T ^ 2))
        volume (-(M : ℝ)) c := continuous_const.intervalIntegrable _ _
    calc
      perronCarrierHorizontalWeight F c M T
          ≤ ∫ _x in (-(M : ℝ))..c, (2 * C) / (1 + T ^ 2) := by
        unfold perronCarrierHorizontalWeight
        apply intervalIntegral.integral_mono_on hMc hint hconst
        intro x hx
        apply div_le_div_of_nonneg_right _ (by positivity)
        linarith [hbound x hx T, hbound x hx (-T)]
      _ = K * (1 + T ^ 2)⁻¹ := by
        rw [intervalIntegral.integral_const]
        simp only [smul_eq_mul]
        dsimp [K]
        field_simp
        ring
  have hdomInt : Integrable (fun T : ℝ => K * (1 + T ^ 2)⁻¹) :=
    integrable_inv_one_add_sq.const_mul K
  have hmassInt : Integrable (perronCarrierHorizontalWeight F c M) :=
    hdomInt.mono' hmassCont.aestronglyMeasurable (Eventually.of_forall fun T => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hmassNonneg T)]
      exact hpoint T)
  exact hmassInt.integrableOn

/-- The horizontal strip mass of a finite Dirichlet carrier is unconditional. -/
theorem dirichletPoly_hasPerronCarrierHorizontalMassAt
    (N M : ℕ) {c : ℝ} (hc : -(M : ℝ) ≤ c) :
    HasPerronCarrierHorizontalMassAt (dirichletPoly N) c M := by
  exact hasPerronCarrierHorizontalMassAt_of_uniform_strip_norm_le
    (dirichletPoly_differentiable N).continuous hc
    (Finset.sum_nonneg fun _ _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)
    (fun x hx _T => norm_dirichletPoly_vertical_strip_le N M hx.1)

/-- Coefficients of the length-`N` Dirichlet polynomial. -/
def dirichletPolyCoeff (N n : ℕ) : ℂ :=
  if n ∈ Finset.Icc 1 N then 1 else 0

/-- Finite Dirichlet-polynomial coefficients are summable at every complex argument. -/
theorem dirichletPolyCoeff_lseriesSummable (N : ℕ) (s : ℂ) :
    LSeriesSummable (dirichletPolyCoeff N) s := by
  apply summable_of_ne_finset_zero (s := Finset.Icc 1 N)
  intro n hn
  unfold LSeries.term dirichletPolyCoeff
  split_ifs <;> simp_all

/-- The `LSeries` of the concrete finite coefficient sequence is exactly `dirichletPoly N`. -/
theorem LSeries_dirichletPolyCoeff (N : ℕ) (s : ℂ) :
    LSeries (dirichletPolyCoeff N) s = dirichletPoly N s := by
  have hzero : ∀ n ∉ Finset.Icc 1 N,
      LSeries.term (dirichletPolyCoeff N) s n = 0 := by
    intro n hn
    unfold LSeries.term dirichletPolyCoeff
    split_ifs <;> simp_all
  rw [LSeries, tsum_eq_sum hzero]
  unfold dirichletPoly
  apply Finset.sum_congr rfl
  intro n hn
  rw [LSeries.term_of_ne_zero (Nat.one_le_iff_ne_zero.mp (Finset.mem_Icc.mp hn).1)]
  simp only [dirichletPolyCoeff, if_pos hn, one_div]
  exact (Complex.cpow_neg (n : ℂ) s).symm

/-- The eventual weighted flank-mass interface is concrete for every finite Dirichlet carrier. -/
theorem dirichletPoly_hasPerronCarrierFlankMass (N : ℕ) :
    HasPerronCarrierFlankMass (dirichletPoly N)
      (fun M => 2 * dirichletPolyPerronBudget N M) := by
  refine Eventually.of_forall fun M => ?_
  convert dirichletPoly_hasPerronCarrierFlankMassAt N M using 1
  ring

/-- The eventual horizontal-mass interface is concrete on every positive Perron line. -/
theorem dirichletPoly_hasPerronCarrierHorizontalMass
    (N : ℕ) {c : ℝ} (hc : 0 ≤ c) :
    HasPerronCarrierHorizontalMass (dirichletPoly N) c := by
  refine Eventually.of_forall fun M => dirichletPoly_hasPerronCarrierHorizontalMassAt N M ?_
  exact le_trans (neg_nonpos.mpr (Nat.cast_nonneg M)) hc

/-- **Unconditional finite-carrier Perron boundary charge.**  All mass, escape, summability, and
right-half-plane representation Props are constructed from `dirichletPoly N`. -/
theorem dirichletPoly_hasVariablePerronBoundaryCharge
    (N : ℕ) {c : ℝ} {n : ℕ} (hc : 0 < c) (hn : 1 ≤ n) :
    HasVariablePerronBoundaryCharge (dirichletPoly N) c
      (fun M => 2 * dirichletPolyPerronBudget N M) n := by
  exact (dirichletPoly_hasPerronCarrierFlankMass N).hasVariablePerronBoundaryCharge_of_carrierHorizontalMass
      (dirichletPoly_hasPerronCarrierHorizontalMass N hc.le) hc
      (dirichletPolyCoeff_lseriesSummable N c)
      (dirichletPoly_differentiable N)
      (fun s _ => (LSeries_dirichletPolyCoeff N s).symm) hn

/-- The quiet-flank coefficient-bound interface is likewise hypothesis-free for finite carriers. -/
theorem dirichletPoly_hasVariableQuietFlankCoefficientBound
    (N : ℕ) {c : ℝ} {n : ℕ} (hc : 0 < c) (hn : 1 ≤ n) :
    HasVariableQuietFlankCoefficientBound (dirichletPolyCoeff N)
      (fun M => 2 * dirichletPolyPerronBudget N M) n := by
  exact (dirichletPoly_hasPerronCarrierFlankMass N).hasVariableQuietFlankCoefficientBound_of_carrierHorizontalMass
      (dirichletPoly_hasPerronCarrierHorizontalMass N hc.le) hc
      (dirichletPolyCoeff_lseriesSummable N c)
      (dirichletPoly_differentiable N)
      (fun s _ => (LSeries_dirichletPolyCoeff N s).symm) hn

/-- The original fixed half-knot coefficient interface is also unconditional for finite carriers. -/
theorem dirichletPoly_hasQuietFlankCoefficientBound
    (N : ℕ) {c : ℝ} {n : ℕ} (hc : 0 < c) (hn : 1 ≤ n) :
    HasQuietFlankCoefficientBound (dirichletPolyCoeff N)
      (fun M => 2 * dirichletPolyPerronBudget N M) n :=
  (dirichletPoly_hasVariableQuietFlankCoefficientBound N hc hn).hasQuietFlankCoefficientBound hn

/-- At each admissible contour depth, the concrete finite carrier supplies its own Perron charge. -/
theorem dirichletPoly_hasPerronBoundaryChargeAt
    (N : ℕ) {c δ : ℝ} {n M : ℕ}
    (hc : 0 < c) (hn : 1 ≤ n) (hM : 2 ≤ M) (hδ0 : 0 < δ) (hδn : δ < (n : ℝ)) :
    HasPerronBoundaryChargeAt (dirichletPoly N) c n δ M
      (4 * perronSupportScaleAt n δ ^ (1 - (M : ℝ)) *
        (dirichletPolyPerronBudget N M * Real.pi)) := by
  have hhorizontal := dirichletPoly_hasPerronCarrierHorizontalMassAt N M
    (le_trans (neg_nonpos.mpr (Nat.cast_nonneg M)) hc.le)
  have hescape := hasPerronBoundaryEscapeAt_of_carrierHorizontalMassAt
    hhorizontal hc (dirichletPolyCoeff_lseriesSummable N c)
    (dirichletPoly_differentiable N)
    (fun s _ => (LSeries_dirichletPolyCoeff N s).symm) hn hδ0 hδn
  exact hasPerronBoundaryChargeAt_of_escape_of_carrierFlankMassAt
    (dirichletPoly_differentiable N) hn hM hδ0 hδn hescape
    (dirichletPoly_hasPerronCarrierFlankMassAt N M)

/-- The full right-edge Perron integral bound for a finite carrier has no Prop-valued input. -/
theorem dirichletPoly_perron_right_integral_norm_le
    (N : ℕ) {c δ : ℝ} {n M : ℕ}
    (hc : 0 < c) (hn : 1 ≤ n) (hM : 2 ≤ M) (hδ0 : 0 < δ) (hδn : δ < (n : ℝ)) :
    ‖∫ y : ℝ, perronContourIntegrand (dirichletPoly N) n δ (↑c + ↑y * I)‖ ≤
      4 * perronSupportScaleAt n δ ^ (1 - (M : ℝ)) *
        (dirichletPolyPerronBudget N M * Real.pi) :=
  perron_right_integral_norm_le_of_boundaryChargeAt
    (dirichletPoly_differentiable N) (perronEAt_differentiable hn hδ0 hδn)
    (dirichletPoly_hasPerronBoundaryChargeAt N hc hn hM hδ0 hδn)

end RHTower
