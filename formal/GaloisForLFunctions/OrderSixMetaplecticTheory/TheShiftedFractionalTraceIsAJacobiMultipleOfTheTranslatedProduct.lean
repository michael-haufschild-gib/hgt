import GaloisForLFunctions.OrderSixMetaplecticTheory.TheConstantTermOfTheShiftedFractionalTraceCarriesTheShiftPhase
import GaloisForLFunctions.OrderSixMetaplecticTheory.TheFractionalTraceIsAJacobiMultipleOfThetaSquaresUpToABoundedRemainder
import GaloisForLFunctions.SpectralTheoryOfTheCubicCover.TheTranslatedThetaProductHasOneCuspSubtraction

/-!
# The shifted fractional trace is a Jacobi multiple of the translated product

For an odd primary prime `q` and the shift `ω`, the remainder

`R^ω_q = Tr G^ω − (N² + N + (N − 1)J) F_ω`,   `F_ω(w) = θ_s(T_ωw) θ_s(T_{−ω}w)`   (`PrimaryPrime.shiftRemainder`),

is a bounded remainder of multiplier `κ⁻¹` (the main coefficient is that of the fractional trace):

* on the standard strip every shifted point has height `v`, `N(q)v` or `v/N(q)` and `θ_s(T_{±ω}·) = cv^{2/3} + O(v^{−3})`;
  the constant parts sum as for the fractional trace (`shiftRemainder_decomp`, `norm_shiftRemainder_strip`);
* elsewhere the shift breaks the symmetry `S`, but the column determinant modulo `3` moves by the norm of the
  lower-left entry, `D(a ± ωc, c) = D(a, c) ∓ N(c)` (`colRes_add_omega`): unless the point lies over `∞`, one of the
  two shifted factors of every pair sits at a ramified cusp and decays exponentially, against at most polynomial growth
  of the other.
-/

noncomputable section

open MeasureTheory Filter
open scoped BigOperators Classical MatrixGroups

namespace GaloisForLFunctions.OrderSixMetaplecticTheory

open MetaplecticMobiusDescent MetaplecticMobiusDescent.Eisenstein MetaplecticMobiusDescent.CubicJacobi
  MetaplecticMobiusDescent.CubicEisenstein MetaplecticMobiusDescent.CubicKubota SpectralTheoryOfTheCubicCover
  MetaplecticMobiusDescent.CubicEisenstein.RationalSource

namespace PrimaryPrime

variable (P : PrimaryPrime)

/-- `R^ω_q = Tr G^ω − (N² + N + (N − 1)J) F_ω`. -/
def shiftRemainder (w : HyperbolicSpace) : ℂ :=
  P.sourceShiftTrace omega w - P.fracMain * translatedThetaProduct w

theorem sourceShiftTrace_automorphy (M : levelThree) (w : HyperbolicSpace) :
    P.sourceShiftTrace omega (complexMatrix M • w) = (complexCharacter M)⁻¹ * P.sourceShiftTrace omega w := by
  rw [sourceShiftTrace, P.shiftTrace_automorphy sourceTheta sourceTheta_automorphy, complexCharacter_sq_eq_inv]

theorem shiftRemainder_automorphy (M : levelThree) (w : HyperbolicSpace) :
    P.shiftRemainder (complexMatrix M • w) = (complexCharacter M)⁻¹ * P.shiftRemainder w := by
  rw [shiftRemainder, shiftRemainder, P.sourceShiftTrace_automorphy, translatedThetaProduct_automorphy]
  ring

theorem norm_shiftRemainder_levelThree (M : levelThree) (w : HyperbolicSpace) :
    ‖P.shiftRemainder (complexMatrix M • w)‖ = ‖P.shiftRemainder w‖ := by
  rw [P.shiftRemainder_automorphy, norm_mul, norm_inv, norm_complexCharacter, inv_one, one_mul]

/-! ### The decomposition into shifted points -/

/-- Translations by `3O` fix `θ_s(T_b·)`. -/
theorem sourceTheta_shift_transThree (b r : O) (w : HyperbolicSpace) :
    sourceTheta (integralComplexMatrix (integralTranslation b) • complexMatrix (transThree r) • w) =
      sourceTheta (integralComplexMatrix (integralTranslation b) • w) := by
  rw [conj_smul, sourceTheta_automorphy, complexCharacter_translationConjugate_transThree, one_mul]

/-- **The shifted remainder as a sum over shifted points**, for arbitrary main values. -/
theorem shiftRemainder_decomp (w : HyperbolicSpace) (R0 Rhi Rlo : ℂ) :
    P.shiftRemainder w =
      ∑ x : P.Res, (sourceTheta (integralComplexMatrix (integralTranslation omega) • P.fracShift (P.lift x) • w) *
          sourceTheta (integralComplexMatrix (integralTranslation (-omega)) • P.fracShift (-P.lift x) • w) - R0 * R0) +
        ∑ x : {x : P.Res // x ≠ 0}, ∑ t : P.Res, (P.shiftCorrelation sourceTheta omega (P.lift t)
          (complexMatrix (lowerThree (P.p * P.lift x.1)) • w) - P.middleMain x t (Rhi * R0) (R0 * R0)) +
        P.normC ^ 2 * (translatedThetaProduct w - R0 * R0) +
        ∑ s : P.Res × P.Res, ∑ x : {x : P.Res // x ≠ 0}, P.chi (-9 * x.1 ^ 2) *
          (P.heckeLow (fun y => sourceTheta (integralComplexMatrix (integralTranslation omega) • y))
              (-P.lowBeta (-P.lift x.1)) (P.contraction • complexMatrix (transThree (P.sqLift s)) • w) *
            P.heckeLow (fun y => sourceTheta (integralComplexMatrix (integralTranslation (-omega)) • y))
              (-P.lowBeta (P.lift x.1)) (P.contraction • complexMatrix (transThree (P.sqLift s)) • w) - Rlo * Rlo) -
        P.fracMain * (translatedThetaProduct w - R0 * R0) := by
  have e1 : ∑ x : P.Res, (sourceTheta (integralComplexMatrix (integralTranslation omega) • P.fracShift (P.lift x) • w) *
      sourceTheta (integralComplexMatrix (integralTranslation (-omega)) • P.fracShift (-P.lift x) • w) - R0 * R0) =
      P.shiftSum sourceTheta omega w - P.normC * (R0 * R0) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rfl
  have e2 : ∑ x : {x : P.Res // x ≠ 0}, ∑ t : P.Res, (P.shiftCorrelation sourceTheta omega (P.lift t)
      (complexMatrix (lowerThree (P.p * P.lift x.1)) • w) - P.middleMain x t (Rhi * R0) (R0 * R0)) =
      ∑ x : {x : P.Res // x ≠ 0}, P.shiftSum sourceTheta omega (complexMatrix (lowerThree (P.p * P.lift x.1)) • w) -
        (P.normC - 1) * P.fracJacobi * (R0 * R0) := by
    simp_rw [Finset.sum_sub_distrib]
    rw [P.sum_middleMain]
    rfl
  have e4 : ∑ s : P.Res × P.Res, ∑ x : {x : P.Res // x ≠ 0}, P.chi (-9 * x.1 ^ 2) *
      (P.heckeLow (fun y => sourceTheta (integralComplexMatrix (integralTranslation omega) • y))
          (-P.lowBeta (-P.lift x.1)) (P.contraction • complexMatrix (transThree (P.sqLift s)) • w) *
        P.heckeLow (fun y => sourceTheta (integralComplexMatrix (integralTranslation (-omega)) • y))
          (-P.lowBeta (P.lift x.1)) (P.contraction • complexMatrix (transThree (P.sqLift s)) • w) - Rlo * Rlo) =
      ∑ s : P.Res × P.Res, P.shiftSum sourceTheta omega
        (complexMatrix P.gamma0 • complexMatrix (transThree (P.sqLift s)) • w) -
        P.normC ^ 2 * translatedThetaProduct w := by
    have hpt : ∀ s : P.Res × P.Res, P.shiftSum sourceTheta omega
        (complexMatrix P.gamma0 • complexMatrix (transThree (P.sqLift s)) • w) =
        translatedThetaProduct w + ∑ x : {x : P.Res // x ≠ 0}, P.chi (-9 * x.1 ^ 2) *
          (P.heckeLow (fun y => sourceTheta (integralComplexMatrix (integralTranslation omega) • y))
              (-P.lowBeta (-P.lift x.1)) (P.contraction • complexMatrix (transThree (P.sqLift s)) • w) *
            P.heckeLow (fun y => sourceTheta (integralComplexMatrix (integralTranslation (-omega)) • y))
              (-P.lowBeta (P.lift x.1)) (P.contraction • complexMatrix (transThree (P.sqLift s)) • w)) := by
      intro s
      rw [P.shiftSum_gamma0 sourceTheta sourceTheta_automorphy, sourceTheta_shift_transThree,
        sourceTheta_shift_transThree]
      rfl
    simp_rw [hpt]
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_prod, nsmul_eq_mul]
    have hz : ∀ s : P.Res × P.Res, ∑ x : {x : P.Res // x ≠ 0}, P.chi (-9 * x.1 ^ 2) *
        (P.heckeLow (fun y => sourceTheta (integralComplexMatrix (integralTranslation omega) • y))
            (-P.lowBeta (-P.lift x.1)) (P.contraction • complexMatrix (transThree (P.sqLift s)) • w) *
          P.heckeLow (fun y => sourceTheta (integralComplexMatrix (integralTranslation (-omega)) • y))
            (-P.lowBeta (P.lift x.1)) (P.contraction • complexMatrix (transThree (P.sqLift s)) • w) - Rlo * Rlo) =
        ∑ x : {x : P.Res // x ≠ 0}, P.chi (-9 * x.1 ^ 2) *
          (P.heckeLow (fun y => sourceTheta (integralComplexMatrix (integralTranslation omega) • y))
              (-P.lowBeta (-P.lift x.1)) (P.contraction • complexMatrix (transThree (P.sqLift s)) • w) *
            P.heckeLow (fun y => sourceTheta (integralComplexMatrix (integralTranslation (-omega)) • y))
              (-P.lowBeta (P.lift x.1)) (P.contraction • complexMatrix (transThree (P.sqLift s)) • w)) := by
      intro s
      simp_rw [mul_sub, Finset.sum_sub_distrib]
      rw [← Finset.sum_mul, P.sum_chi_low, zero_mul, sub_zero]
    simp_rw [hz]
    push_cast
    ring
  rw [e1, e2, e4, shiftRemainder, sourceShiftTrace, P.shiftTrace_eq sourceTheta sourceTheta_automorphy, fracMain]
  ring

/-- **The shifted remainder is controlled by the shifted points.** -/
theorem norm_shiftRemainder_le (h2 : (2 : P.Res) ≠ 0) (w : HyperbolicSpace) (R0 Rhi Rlo : ℂ) (M D : ℝ)
    (hR0 : ‖R0‖ ≤ M) (hRhi : ‖Rhi‖ ≤ M) (hRlo : ‖Rlo‖ ≤ M)
    (bfr : ∀ (b u : O), b = omega ∨ b = -omega →
      ‖sourceTheta (integralComplexMatrix (integralTranslation b) • P.fracShift u • w) - R0‖ ≤ D)
    (bhi : ∀ b : O, b = omega ∨ b = -omega →
      ‖sourceTheta (integralComplexMatrix (integralTranslation b) • P.dilation • P.dilation • w) - Rhi‖ ≤ D)
    (b0 : ∀ b : O, b = omega ∨ b = -omega →
      ‖sourceTheta (integralComplexMatrix (integralTranslation b) • w) - R0‖ ≤ D)
    (blo : ∀ (b r : O) (s : P.Res × P.Res), b = omega ∨ b = -omega →
      ‖P.heckeLow (fun y => sourceTheta (integralComplexMatrix (integralTranslation b) • y)) r
        (P.contraction • complexMatrix (transThree (P.sqLift s)) • w) - Rlo‖ ≤ D) :
    ‖P.shiftRemainder w‖ ≤ ((Fintype.card P.Res : ℝ) + (Fintype.card P.Res : ℝ) * (Fintype.card P.Res : ℝ) +
      (Fintype.card P.Res : ℝ) ^ 2 + (Fintype.card P.Res : ℝ) ^ 2 * (Fintype.card P.Res : ℝ) + ‖P.fracMain‖) *
        (2 * M * D + D ^ 2) := by
  have hp : omega = omega ∨ omega = -omega := Or.inl rfl
  have hm : -omega = omega ∨ -omega = -omega := Or.inr rfl
  set N : ℝ := (Fintype.card P.Res : ℝ) with hNdef
  set Eb : ℝ := 2 * M * D + D ^ 2 with hEbdef
  have hEb : ∀ X Y PP QQ : ℂ, ‖PP‖ ≤ M → ‖QQ‖ ≤ M → ‖X - PP‖ ≤ D → ‖Y - QQ‖ ≤ D →
      ‖X * Y - PP * QQ‖ ≤ Eb := fun X Y PP QQ h1 h2 h3 h4 => norm_mul_sub_mul_le h1 h2 h3 h4
  have hEb0 : 0 ≤ Eb := (norm_nonneg _).trans (hEb _ _ _ _ hR0 hR0 (b0 _ hp) (b0 _ hm))
  have hcard : (Fintype.card {x : P.Res // x ≠ 0} : ℝ) ≤ N := by
    rw [hNdef]
    exact_mod_cast Fintype.card_subtype_le _
  have hF : ‖translatedThetaProduct w - R0 * R0‖ ≤ Eb := hEb _ _ _ _ hR0 hR0 (b0 _ hp) (b0 _ hm)
  have hs1 : ‖∑ x : P.Res, (sourceTheta (integralComplexMatrix (integralTranslation omega) • P.fracShift (P.lift x) • w) *
      sourceTheta (integralComplexMatrix (integralTranslation (-omega)) • P.fracShift (-P.lift x) • w) - R0 * R0)‖ ≤
      N * Eb := by
    refine (norm_sum_le _ _).trans ?_
    calc _ ≤ ∑ _x : P.Res, Eb := Finset.sum_le_sum fun x _ => hEb _ _ _ _ hR0 hR0 (bfr _ _ hp) (bfr _ _ hm)
      _ = N * Eb := by simp [hNdef]
  have hterm : ∀ (x : {x : P.Res // x ≠ 0}) (t : P.Res), ‖P.shiftCorrelation sourceTheta omega (P.lift t)
      (complexMatrix (lowerThree (P.p * P.lift x.1)) • w) - P.middleMain x t (Rhi * R0) (R0 * R0)‖ ≤ Eb := by
    intro x t
    rw [P.shiftCorrelation_lowerThree sourceTheta sourceTheta_automorphy h2 omega x t, middleMain]
    split_ifs
    · rw [← mul_sub]
      exact (norm_mul_le _ _).trans ((mul_le_of_le_one_left (norm_nonneg _) (P.norm_highPhase_le x)).trans
        (hEb _ _ _ _ hRhi hR0 (bhi _ hp) (bfr _ _ hm)))
    · rw [← mul_sub, mul_comm Rhi R0]
      exact (norm_mul_le _ _).trans ((mul_le_of_le_one_left (norm_nonneg _) (P.norm_highPhase_le x)).trans
        (hEb _ _ _ _ hR0 hRhi (bfr _ _ hp) (bhi _ hm)))
    · rw [← mul_sub]
      exact (norm_mul_le _ _).trans ((mul_le_of_le_one_left (norm_nonneg _) (P.norm_chi_le _)).trans
        (hEb _ _ _ _ hR0 hR0 (bfr _ _ hp) (bfr _ _ hm)))
  have hs2 : ‖∑ x : {x : P.Res // x ≠ 0}, ∑ t : P.Res, (P.shiftCorrelation sourceTheta omega (P.lift t)
      (complexMatrix (lowerThree (P.p * P.lift x.1)) • w) - P.middleMain x t (Rhi * R0) (R0 * R0))‖ ≤
      N * (N * Eb) := by
    refine (norm_sum_le _ _).trans ?_
    calc _ ≤ ∑ _x : {x : P.Res // x ≠ 0}, N * Eb := by
          refine Finset.sum_le_sum fun x _ => (norm_sum_le _ _).trans ?_
          calc _ ≤ ∑ _t : P.Res, Eb := Finset.sum_le_sum fun t _ => hterm x t
            _ = N * Eb := by simp [hNdef]
      _ = (Fintype.card {x : P.Res // x ≠ 0} : ℝ) * (N * Eb) := by simp
      _ ≤ N * (N * Eb) := mul_le_mul_of_nonneg_right hcard (by positivity)
  have hs3 : ‖P.normC ^ 2 * (translatedThetaProduct w - R0 * R0)‖ ≤ N ^ 2 * Eb := by
    rw [norm_mul, norm_pow, Complex.norm_natCast]
    exact mul_le_mul_of_nonneg_left hF (by positivity)
  have hs4 : ‖∑ s : P.Res × P.Res, ∑ x : {x : P.Res // x ≠ 0}, P.chi (-9 * x.1 ^ 2) *
      (P.heckeLow (fun y => sourceTheta (integralComplexMatrix (integralTranslation omega) • y))
          (-P.lowBeta (-P.lift x.1)) (P.contraction • complexMatrix (transThree (P.sqLift s)) • w) *
        P.heckeLow (fun y => sourceTheta (integralComplexMatrix (integralTranslation (-omega)) • y))
          (-P.lowBeta (P.lift x.1)) (P.contraction • complexMatrix (transThree (P.sqLift s)) • w) - Rlo * Rlo)‖ ≤
      N ^ 2 * (N * Eb) := by
    refine (norm_sum_le _ _).trans ?_
    calc _ ≤ ∑ _s : P.Res × P.Res, N * Eb := by
          refine Finset.sum_le_sum fun s _ => (norm_sum_le _ _).trans ?_
          calc _ ≤ ∑ _x : {x : P.Res // x ≠ 0}, Eb := by
                refine Finset.sum_le_sum fun x _ => (norm_mul_le _ _).trans ?_
                exact (mul_le_of_le_one_left (norm_nonneg _) (P.norm_chi_le _)).trans
                  (hEb _ _ _ _ hRlo hRlo (blo _ _ _ hp) (blo _ _ _ hm))
            _ = (Fintype.card {x : P.Res // x ≠ 0} : ℝ) * Eb := by simp
            _ ≤ N * Eb := mul_le_mul_of_nonneg_right hcard hEb0
      _ = N ^ 2 * (N * Eb) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, nsmul_eq_mul, hNdef]
          push_cast
          ring
  have hs5 : ‖P.fracMain * (translatedThetaProduct w - R0 * R0)‖ ≤ ‖P.fracMain‖ * Eb := by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left hF (norm_nonneg _)
  rw [P.shiftRemainder_decomp w R0 Rhi Rlo]
  calc _ ≤ ‖∑ x : P.Res, (sourceTheta (integralComplexMatrix (integralTranslation omega) • P.fracShift (P.lift x) • w) *
          sourceTheta (integralComplexMatrix (integralTranslation (-omega)) • P.fracShift (-P.lift x) • w) - R0 * R0)‖ +
        ‖∑ x : {x : P.Res // x ≠ 0}, ∑ t : P.Res, (P.shiftCorrelation sourceTheta omega (P.lift t)
          (complexMatrix (lowerThree (P.p * P.lift x.1)) • w) - P.middleMain x t (Rhi * R0) (R0 * R0))‖ +
        ‖P.normC ^ 2 * (translatedThetaProduct w - R0 * R0)‖ +
        ‖∑ s : P.Res × P.Res, ∑ x : {x : P.Res // x ≠ 0}, P.chi (-9 * x.1 ^ 2) *
          (P.heckeLow (fun y => sourceTheta (integralComplexMatrix (integralTranslation omega) • y))
              (-P.lowBeta (-P.lift x.1)) (P.contraction • complexMatrix (transThree (P.sqLift s)) • w) *
            P.heckeLow (fun y => sourceTheta (integralComplexMatrix (integralTranslation (-omega)) • y))
              (-P.lowBeta (P.lift x.1)) (P.contraction • complexMatrix (transThree (P.sqLift s)) • w) - Rlo * Rlo)‖ +
        ‖P.fracMain * (translatedThetaProduct w - R0 * R0)‖ := by
        refine (norm_sub_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans
          (add_le_add (norm_add_le _ _) le_rfl)) le_rfl)) le_rfl)
    _ ≤ N * Eb + N * (N * Eb) + N ^ 2 * Eb + N ^ 2 * (N * Eb) + ‖P.fracMain‖ * Eb := by gcongr
    _ = _ := by ring

/-- The shifted low point at a point of the strip. -/
theorem heckeLow_shift_point (b r : O) (z : ℂ) (v : ℝ) (hv : 0 < v) :
    P.heckeLow (fun y => sourceTheta (integralComplexMatrix (integralTranslation b) • y)) r (upperPoint z v hv) =
      sourceTheta (upperPoint ((z + 3 * ringComplex r) / ringComplex P.p + ringComplex b) (v / ‖ringComplex P.p‖)
        (div_pos hv P.norm_pos)) := by
  simp only [heckeLow]
  rw [transThree_smul_upperPoint, P.contraction_upperPoint, integralTranslation_action]

/-- **`R^ω_q = O(v^{−7/3})` on the standard strip above any fixed height.** -/
theorem norm_shiftRemainder_strip (h2 : (2 : P.Res) ≠ 0) (a : ℝ) (ha : 0 < a) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (z : ℂ) (v : ℝ) (hv : 0 < v), a ≤ v →
      ‖P.shiftRemainder (upperPoint z v hv)‖ ≤ K * v ^ (-(7 : ℝ) / 3) := by
  have hn := P.norm_pos
  have hρ1 := P.one_le_norm
  set ρ := ‖ringComplex P.p‖ with hρdef
  obtain ⟨C₁, hC₁, hdec⟩ := cubicSourceResidualFunction_cusp_decay_from_height (a / ρ / ρ) (div_pos (div_pos ha hn) hn)
  set c : ℂ := 3 * (Real.pi : ℂ) * constantArithmeticResidue with hcdef
  set N : ℝ := (Fintype.card P.Res : ℝ) with hNdef
  set K0 : ℝ := N + N * N + N ^ 2 + N ^ 2 * N + ‖P.fracMain‖ with hK0
  have hK00 : 0 ≤ K0 := by positivity
  refine ⟨K0 * (2 * ‖c‖ * ρ ^ ((4 : ℝ) / 3) * (C₁ * ρ ^ 6) + (C₁ * ρ ^ 6) ^ 2 * a ^ (-(11 : ℝ) / 3)),
    by positivity, fun z v hv hav => ?_⟩
  have hlo : 0 < v / ρ / ρ := div_pos (div_pos hv hn) hn
  have hhi : 0 < ρ * (ρ * v) := mul_pos hn (mul_pos hn hv)
  have hlov : v / ρ / ρ ≤ v := le_trans (div_le_self (div_pos hv hn).le hρ1) (div_le_self hv.le hρ1)
  set M : ℝ := ‖c‖ * ρ ^ ((4 : ℝ) / 3) * v ^ ((2 : ℝ) / 3) with hMdef
  set D : ℝ := C₁ * ρ ^ 6 / v ^ 3 with hDdef
  have hρ43 : 1 ≤ ρ ^ ((4 : ℝ) / 3) := Real.one_le_rpow hρ1 (by norm_num)
  have hcv : ‖c‖ * v ^ ((2 : ℝ) / 3) ≤ M := by
    rw [hMdef]
    have := mul_le_mul_of_nonneg_left hρ43 (mul_nonneg (norm_nonneg c) (by positivity : 0 ≤ v ^ ((2 : ℝ) / 3)))
    nlinarith
  have hR0M : ‖c * (v : ℂ) ^ (2 / 3 : ℂ)‖ ≤ M := by
    rw [norm_mul, norm_cpow_two_thirds hv]
    exact hcv
  have hRhiM : ‖c * ((ρ * (ρ * v) : ℝ) : ℂ) ^ (2 / 3 : ℂ)‖ ≤ M := by
    have e : (ρ * (ρ * v)) ^ ((2 : ℝ) / 3) = ρ ^ ((4 : ℝ) / 3) * v ^ ((2 : ℝ) / 3) := by
      rw [← mul_assoc, Real.mul_rpow (by positivity) hv.le, show ρ * ρ = ρ ^ (2 : ℝ) by rw [Real.rpow_two]; ring,
        ← Real.rpow_mul hn.le]
      norm_num
    rw [norm_mul, norm_cpow_two_thirds hhi, e, hMdef]
    ring_nf
    exact le_rfl
  have hRloM : ‖c * ((v / ρ / ρ : ℝ) : ℂ) ^ (2 / 3 : ℂ)‖ ≤ M := by
    rw [norm_mul, norm_cpow_two_thirds hlo]
    exact le_trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hlo.le hlov (by norm_num)) (norm_nonneg _)) hcv
  have hcube : ∀ (ζ : ℂ) (h : ℝ) (hh : 0 < h), v / ρ / ρ ≤ h →
      ‖sourceTheta (upperPoint ζ h hh) - c * (h : ℂ) ^ (2 / 3 : ℂ)‖ ≤ D := by
    intro ζ h hh hle
    have hd := hdec h hh (le_trans (div_le_div_of_nonneg_right (div_le_div_of_nonneg_right hav hn.le) hn.le) hle) ζ
    refine hd.trans ?_
    rw [hDdef, div_le_div_iff₀ (by positivity) (by positivity)]
    have h3 : (v / ρ / ρ) ^ 3 ≤ h ^ 3 := pow_le_pow_left₀ hlo.le hle 3
    have e : (v / ρ / ρ) ^ 3 * ρ ^ 6 = v ^ 3 := by field_simp
    nlinarith [mul_le_mul_of_nonneg_left h3 (by positivity : (0 : ℝ) ≤ C₁ * ρ ^ 6)]
  have hbound := P.norm_shiftRemainder_le h2 (upperPoint z v hv) (c * (v : ℂ) ^ (2 / 3 : ℂ))
    (c * ((ρ * (ρ * v) : ℝ) : ℂ) ^ (2 / 3 : ℂ)) (c * ((v / ρ / ρ : ℝ) : ℂ) ^ (2 / 3 : ℂ)) M D hR0M hRhiM hRloM
    (fun b u _ => by
      simp only [fracShift, complexTranslation_action, integralTranslation_action]
      exact hcube _ v hv hlov)
    (fun b _ => by
      simp only [P.dilation_upperPoint, integralTranslation_action]
      exact hcube _ _ hhi (le_trans hlov (le_trans (le_mul_of_one_le_left hv.le hρ1)
        (mul_le_mul_of_nonneg_left (le_mul_of_one_le_left hv.le hρ1) hn.le))))
    (fun b _ => by
      rw [integralTranslation_action]
      exact hcube _ v hv hlov)
    (fun b r s _ => by
      simp only [transThree_smul_upperPoint, P.contraction_upperPoint, P.heckeLow_shift_point]
      exact hcube _ _ _ le_rfl)
  refine hbound.trans ?_
  have hv3 : v ^ ((2 : ℝ) / 3) / v ^ 3 = v ^ (-(7 : ℝ) / 3) := by
    rw [← Real.rpow_natCast, ← Real.rpow_sub hv]
    norm_num
  have hv6 : 1 / v ^ 6 ≤ a ^ (-(11 : ℝ) / 3) * v ^ (-(7 : ℝ) / 3) := by
    have hsplit : 1 / v ^ 6 = v ^ (-(11 : ℝ) / 3) * v ^ (-(7 : ℝ) / 3) := by
      rw [← Real.rpow_add hv, one_div, ← Real.rpow_natCast, ← Real.rpow_neg hv.le]
      norm_num
    rw [hsplit]
    exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_nonpos ha hav (by norm_num)) (by positivity)
  have hEbv : 2 * M * D + D ^ 2 = 2 * ‖c‖ * ρ ^ ((4 : ℝ) / 3) * (C₁ * ρ ^ 6) * (v ^ ((2 : ℝ) / 3) / v ^ 3) +
      (C₁ * ρ ^ 6) ^ 2 * (1 / v ^ 6) := by
    rw [hMdef, hDdef]
    field_simp
  rw [← hK0, hEbv, hv3]
  have h6 := mul_le_mul_of_nonneg_left hv6 (by positivity : (0 : ℝ) ≤ (C₁ * ρ ^ 6) ^ 2)
  nlinarith [mul_le_mul_of_nonneg_left h6 hK00, norm_nonneg c, Real.rpow_nonneg hv.le (-(7 : ℝ) / 3),
    Real.rpow_nonneg hn.le ((4 : ℝ) / 3)]

end PrimaryPrime

namespace PrimaryPrime

variable (P : PrimaryPrime)

/-! ### The column determinant under the shift -/

theorem cuspResidue_omega : cuspResidue omega = (0, 1) := by
  have h : omega = Coordinates.eval 0 1 := by simp [Coordinates.eval]
  rw [h, cuspResidue_eval]
  simp

theorem cuspResidue_neg_omega : cuspResidue (-omega) = (0, -1) := by
  have h : -omega = Coordinates.eval 0 (-1) := by simp [Coordinates.eval]
  rw [h, cuspResidue_eval]
  simp

/-- `D(a + ωc, c) = D(a, c) − N(c)` modulo `3`. -/
theorem colRes_add_omega (a c : O) : colRes (a + omega * c) c = colRes a c - normRes c := by
  simp only [colRes, normRes, cuspResidue_add, cuspResidue_mul, cuspResidueMul, cuspResidue_omega]
  ring

/-- `D(a − ωc, c) = D(a, c) + N(c)` modulo `3`. -/
theorem colRes_add_neg_omega (a c : O) : colRes (a + -omega * c) c = colRes a c + normRes c := by
  simp only [colRes, normRes, cuspResidue_add, cuspResidue_mul, cuspResidueMul, cuspResidue_neg_omega]
  ring

/-- The norm modulo `3` is multiplicative. -/
theorem normRes_mul (x y : O) : normRes (x * y) = normRes x * normRes y := by
  simp only [normRes, cuspResidue_mul, cuspResidueMul]
  ring

theorem normRes_ne_zero_of_isUnit {u : O} (hu : IsUnit u) : normRes u ≠ 0 := by
  obtain ⟨v, hv⟩ := hu.exists_right_inv
  intro h
  have h1 := normRes_mul u v
  rw [hv, h, zero_mul] at h1
  have : normRes 1 = 1 := by
    simp only [normRes]
    rw [show (1 : O) = ((1 : ℤ) : O) by simp, cuspResidue_intCast]
    simp
  rw [this] at h1
  exact one_ne_zero h1

/-- The residues of a level-three translate. -/
theorem cuspResidue_levelThree_col (ρ : levelThree) (M : SL(2, O)) (i : Fin 2) :
    cuspResidue (((ρ : SL(2, O)) * M) i 0) = cuspResidue (M i 0) := by
  apply cuspResidue_congr
  have h00 := levelThree_entry ρ 0 0
  have h01 := levelThree_entry ρ 0 1
  have h10 := levelThree_entry ρ 1 0
  have h11 := levelThree_entry ρ 1 1
  simp only [Fin.isValue, if_true, zero_ne_one, one_ne_zero, if_false, sub_zero] at h00 h01 h10 h11
  obtain ⟨a, ha⟩ := h00
  obtain ⟨b, hb⟩ := h01
  obtain ⟨c, hc⟩ := h10
  obtain ⟨d, hd⟩ := h11
  fin_cases i
  · refine ⟨a * M 0 0 + b * M 1 0, ?_⟩
    simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
    linear_combination (M 0 0) * ha + (M 1 0) * hb
  · refine ⟨c * M 0 0 + d * M 1 0, ?_⟩
    simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
    linear_combination (M 0 0) * hc + (M 1 0) * hd

/-- **The column determinant of a shifted level-three translate**: `D(T_s ρ M) = D(M ± ...)`. -/
theorem colRes_shift_levelThree (s : O) (ρ : levelThree) (M : SL(2, O)) :
    colRes ((integralTranslation s * ((ρ : SL(2, O)) * M)) 0 0) ((integralTranslation s * ((ρ : SL(2, O)) * M)) 1 0) =
      colRes (M 0 0 + s * M 1 0) (M 1 0) := by
  have e0 : (integralTranslation s * ((ρ : SL(2, O)) * M)) 0 0 = ((ρ : SL(2, O)) * M) 0 0 + s * ((ρ : SL(2, O)) * M) 1 0 := by
    simp [integralTranslation, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
  have e1 : (integralTranslation s * ((ρ : SL(2, O)) * M)) 1 0 = ((ρ : SL(2, O)) * M) 1 0 := by
    simp [integralTranslation, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
  rw [e0, e1]
  simp only [colRes, cuspResidue_add, cuspResidue_mul, cuspResidue_levelThree_col]

/-- The column determinant of `G · c_j · T`: `N(T₀₀)` times that of the cusp representative. -/
theorem colRes_cuspDecomp (n : levelThree) (r : SL(2, ℤ)) (j : Fin 3) (T : SL(2, O)) (hT : T 1 0 = 0) :
    colRes (((n : SL(2, O)) * rationalEmbedding r * cuspRepresentative j * T) 0 0)
        (((n : SL(2, O)) * rationalEmbedding r * cuspRepresentative j * T) 1 0) =
      normRes (T 0 0) * colRes ((cuspRepresentative j : SL(2, O)) 0 0) ((cuspRepresentative j : SL(2, O)) 1 0) := by
  set X : SL(2, O) := rationalEmbedding r * cuspRepresentative j
  have hcol : ∀ i : Fin 2, ((n : SL(2, O)) * rationalEmbedding r * cuspRepresentative j * T) i 0 =
      T 0 0 * ((n : SL(2, O)) * X) i 0 := by
    intro i
    simp [X, mul_assoc, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, hT, mul_comm]
    ring
  rw [hcol 0, hcol 1, colRes_mul_left]
  congr 1
  simp only [colRes, cuspResidue_levelThree_col]
  have hX : ∀ i : Fin 2, X i 0 = ((r i 0 : ℤ) : O) * (cuspRepresentative j : SL(2, O)) 0 0 +
      ((r i 1 : ℤ) : O) * (cuspRepresentative j : SL(2, O)) 1 0 := by
    intro i
    simp [X, rationalEmbedding, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
  rw [hX 0, hX 1]
  have h := colRes_int_comb (r 0 0) (r 0 1) (r 1 0) (r 1 1) ((cuspRepresentative j : SL(2, O)) 0 0)
    ((cuspRepresentative j : SL(2, O)) 1 0)
  have hdet : r 0 0 * r 1 1 - r 0 1 * r 1 0 = 1 := by rw [← Matrix.det_fin_two]; exact r.det_coe
  rw [hdet] at h
  simpa [colRes] using h


/-! ### Points away from `∞` -/

/-- **Exponential decay at the fractional points of a ramified point.** -/
theorem theta_fracShift_ramified_decay (a : ℝ) (ha : 0 < a) :
    ∃ C β : ℝ, 0 ≤ C ∧ 0 < β ∧ ∀ (t : O) (M : SL(2, O)), colRes (M 0 0) (M 1 0) ≠ 0 →
      ∀ (z : ℂ) (v : ℝ) (hv : 0 < v), a ≤ v →
        ‖sourceTheta (P.fracShift t • integralComplexMatrix M • upperPoint z v hv)‖ ≤
          C * Real.exp (-β * (v / ‖ringComplex P.p‖ / ‖ringComplex P.p‖)) := by
  have hn := P.norm_pos
  obtain ⟨C, β, hC, hβ, hdec⟩ :=
    sourceTheta_ramified_decay (a / ‖ringComplex P.p‖ / ‖ringComplex P.p‖) (div_pos (div_pos ha hn) hn)
  refine ⟨C, β, hC, hβ, fun t M hcol z v hv hav => ?_⟩
  obtain ⟨M₁, z₁, v₁, hv₁, hc₁, hle₁, he₁⟩ := P.dilation_ramified M hcol z v hv
  have hc₁' : colRes (((transThree t : SL(2, O)) * M₁) 0 0) (((transThree t : SL(2, O)) * M₁) 1 0) ≠ 0 := by
    rw [colRes_levelThree_mul]
    exact hc₁
  obtain ⟨M₂, z₂, v₂, hv₂, hc₂, hle₂, he₂⟩ := P.contraction_ramified _ hc₁' z₁ v₁ hv₁
  have hpt : P.fracShift t • integralComplexMatrix M • upperPoint z v hv =
      integralComplexMatrix M₂ • upperPoint z₂ v₂ hv₂ := by
    rw [P.fracShift_eq, mul_smul, mul_smul, he₁, ← mul_smul (complexMatrix (transThree t)), complexMatrix_eq,
      ← map_mul, he₂]
  rw [hpt]
  have hle₂' : v / ‖ringComplex P.p‖ / ‖ringComplex P.p‖ ≤ v₂ := le_trans (div_le_div_of_nonneg_right hle₁ hn.le) hle₂
  have hav₂ : a / ‖ringComplex P.p‖ / ‖ringComplex P.p‖ ≤ v₂ :=
    le_trans (div_le_div_of_nonneg_right (div_le_div_of_nonneg_right hav hn.le) hn.le) hle₂'
  refine (hdec M₂ hc₂ z₂ v₂ hv₂ hav₂).trans ?_
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith)) hC

theorem norm_sq_le_of_dvd {g k : O} (hk : k ≠ 0) (h : g ∣ k) : ‖ringComplex g‖ ^ 2 ≤ ‖ringComplex k‖ ^ 2 := by
  obtain ⟨m, rfl⟩ := h
  have hm : m ≠ 0 := right_ne_zero_of_mul hk
  have h1 := one_le_norm_sq_ringComplex hm
  rw [map_mul, norm_mul, mul_pow]
  nlinarith [sq_nonneg ‖ringComplex g‖]

theorem rpow_two_thirds_le (v : ℝ) (hv : 0 ≤ v) : v ^ ((2 : ℝ) / 3) ≤ 1 + v := by
  rcases le_total v 1 with h | h
  · have := Real.rpow_le_one hv h (by norm_num : (0 : ℝ) ≤ 2 / 3)
    linarith
  · have := Real.rpow_le_rpow_of_exponent_le h (by norm_num : (2 : ℝ) / 3 ≤ 1)
    rw [Real.rpow_one] at this
    linarith

/-- **Polynomial growth at every fractional point of an integral point.** -/
theorem theta_fracShift_growth (a : ℝ) (ha : 0 < a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (t : O) (M : SL(2, O)) (z : ℂ) (v : ℝ) (hv : 0 < v), a ≤ v →
      ‖sourceTheta (P.fracShift t • integralComplexMatrix M • upperPoint z v hv)‖ ≤ C * (1 + v) := by
  have hn := P.norm_pos
  have hρ1 := P.one_le_norm
  set ρ := ‖ringComplex P.p‖ with hρdef
  set a' := a / ρ ^ 2 with ha'def
  have ha' : 0 < a' := div_pos ha (by positivity)
  obtain ⟨C₁, hC₁, hdec⟩ := cubicSourceResidualFunction_cusp_decay_from_height a' ha'
  obtain ⟨C₂, β, hC₂, hβ, hram⟩ := sourceTheta_ramified_decay a' ha'
  set c : ℂ := 3 * (Real.pi : ℂ) * constantArithmeticResidue
  refine ⟨‖c‖ * (1 + ρ ^ 2) + C₁ / a' ^ 3 + C₂, by positivity, fun t M z v hv hav => ?_⟩
  obtain ⟨N', g, hg, hp, hq, U, hU10, hU00, hfac⟩ := P.dilation_factor M
  obtain ⟨z₁, v₁, hv₁, hpt₁⟩ := upperPoint_surjective (U • upperPoint z v hv)
  have hv₁e : v₁ = v * (‖ringComplex g‖ ^ 2 / ρ) := by
    have h := height_upper_triangular_complex U hU10 z v hv
    rw [← hpt₁, hyperbolicHeight_upperPoint, hU00] at h
    exact h
  obtain ⟨N'', g', hg', hp', hq', U', hU10', hU00', hfac'⟩ := P.contraction_factor ((transThree t : SL(2, O)) * N')
  obtain ⟨z₂, v₂, hv₂, hpt₂⟩ := upperPoint_surjective (U' • upperPoint z₁ v₁ hv₁)
  have hv₂e : v₂ = v₁ * (‖ringComplex g'‖ ^ 2 / ρ) := by
    have h := height_upper_triangular_complex U' hU10' z₁ v₁ hv₁
    rw [← hpt₂, hyperbolicHeight_upperPoint, hU00'] at h
    exact h
  have hpt : P.fracShift t • integralComplexMatrix M • upperPoint z v hv =
      integralComplexMatrix N'' • upperPoint z₂ v₂ hv₂ := by
    rw [P.fracShift_eq, mul_smul, mul_smul, ← mul_smul P.dilation, hfac, mul_smul, ← hpt₁,
      ← mul_smul (complexMatrix (transThree t)), complexMatrix_eq, ← map_mul, ← mul_smul, hfac', mul_smul, ← hpt₂]
  have hgp : g ∣ P.p := by
    have hM : M 0 0 * M 1 1 - M 0 1 * M 1 0 = 1 := by rw [← Matrix.det_fin_two]; exact M.det_coe
    exact ⟨N' 0 0 * M 1 1 - P.p * M 0 1 * N' 1 0,
      by linear_combination (-P.p) * hM + M 1 1 * hp - P.p * M 0 1 * hq⟩
  have hgp' : g' ∣ P.p := by
    set A := (transThree t : SL(2, O)) * N'
    have hA : A 0 0 * A 1 1 - A 0 1 * A 1 0 = 1 := by rw [← Matrix.det_fin_two]; exact A.det_coe
    exact ⟨P.p * N'' 0 0 * A 1 1 - A 0 1 * N'' 1 0,
      by linear_combination (-P.p) * hA + P.p * A 1 1 * hp' - A 0 1 * hq'⟩
  have hg1 := one_le_norm_sq_ringComplex hg
  have hg1' := one_le_norm_sq_ringComplex hg'
  have hgle := norm_sq_le_of_dvd P.ne_zero hgp
  have hgle' := norm_sq_le_of_dvd P.ne_zero hgp'
  have hv2 : v₂ = v * (‖ringComplex g‖ ^ 2 * ‖ringComplex g'‖ ^ 2) / ρ ^ 2 := by
    rw [hv₂e, hv₁e]
    field_simp
  have hlo : a' ≤ v₂ := by
    rw [hv2, ha'def]
    apply div_le_div_of_nonneg_right _ (by positivity)
    nlinarith [mul_le_mul hg1 hg1' zero_le_one (by positivity)]
  have hhi : v₂ ≤ ρ ^ 2 * v := by
    rw [hv2, div_le_iff₀ (by positivity)]
    have hprod : ‖ringComplex g‖ ^ 2 * ‖ringComplex g'‖ ^ 2 ≤ ρ ^ 2 * ρ ^ 2 :=
      mul_le_mul hgle hgle' (by positivity) (by positivity)
    nlinarith
  rw [hpt]
  obtain ⟨G, j, T, hT, -, hu1, hdec'⟩ := three_cusp_decomposition N''
  obtain ⟨z₃, v₃, hv₃, hpt₃⟩ := upperPoint_surjective (integralComplexMatrix T • upperPoint z₂ v₂ hv₂)
  have hv₃e : v₃ = v₂ := by
    have h := height_upperTriangular T hT hu1 z₂ v₂ hv₂
    rw [← hpt₃, hyperbolicHeight_upperPoint] at h
    exact h
  subst hv₃e
  rw [hdec', map_mul, map_mul, mul_smul, mul_smul, ← hpt₃]
  change ‖cubicSourceResidualFunction _‖ ≤ _
  rw [cubicSourceResidualFunction_automorphy, norm_mul, norm_extendedComplexCharacter, one_mul]
  have hv1 : 0 ≤ v := hv.le
  by_cases hj : j = 0
  · subst hj
    have hc1 : cuspRepresentative 0 = 1 := by
      ext i k
      fin_cases i <;> fin_cases k <;> simp [cuspRepresentative, cuspParameter, lowerCuspMatrix]
    rw [hc1, map_one, one_smul]
    have hd := hdec v₃ hv₃ hlo z₃
    have hcv : ‖c * (v₃ : ℂ) ^ (2 / 3 : ℂ)‖ ≤ ‖c‖ * (1 + ρ ^ 2 * v) := by
      rw [norm_mul, norm_cpow_two_thirds hv₃]
      exact mul_le_mul_of_nonneg_left ((rpow_two_thirds_le v₃ hv₃.le).trans (by linarith)) (norm_nonneg _)
    have hC1 : C₁ / v₃ ^ 3 ≤ C₁ / a' ^ 3 :=
      div_le_div_of_nonneg_left hC₁ (by positivity) (pow_le_pow_left₀ ha'.le hlo 3)
    have htot : ‖cubicSourceResidualFunction (upperPoint z₃ v₃ hv₃)‖ ≤ ‖c‖ * (1 + ρ ^ 2 * v) + C₁ / a' ^ 3 := by
      have := norm_le_insert' (cubicSourceResidualFunction (upperPoint z₃ v₃ hv₃)) (c * (v₃ : ℂ) ^ (2 / 3 : ℂ))
      linarith
    refine htot.trans ?_
    have hρ2 : 1 ≤ ρ ^ 2 := one_le_pow₀ hρ1
    nlinarith [norm_nonneg c, mul_nonneg (norm_nonneg c) hv1, hC₂, div_nonneg hC₁ (pow_nonneg ha'.le 3)]
  · have hr := hram (cuspRepresentative j) (colRes_cuspRepresentative j hj) z₃ v₃ hv₃ hlo
    have he : Real.exp (-β * v₃) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
    change ‖sourceTheta _‖ ≤ _
    refine hr.trans ((mul_le_of_le_one_right hC₂ he).trans ?_)
    nlinarith [norm_nonneg c, mul_nonneg (norm_nonneg c) hv1, div_nonneg hC₁ (pow_nonneg ha'.le 3),
      mul_nonneg hC₂ hv1, one_le_pow₀ hρ1 (n := 2)]


/-- Integral translations commute with the fractional translations. -/
theorem intShift_mul_fracShift (b u : O) :
    integralComplexMatrix (integralTranslation b) * P.fracShift u =
      P.fracShift u * integralComplexMatrix (integralTranslation b) := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [fracShift, complexTranslation, integralTranslation, integralComplexMatrix, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.mul_apply, Fin.sum_univ_two, Matrix.SpecialLinearGroup.map]
  ring

/-- A shifted point of a level-three translate is a fractional point of an integral point. -/
theorem shift_point (b u : O) (ρ : levelThree) (M : SL(2, O)) (x : HyperbolicSpace) :
    integralComplexMatrix (integralTranslation b) • P.fracShift u • complexMatrix ρ • integralComplexMatrix M • x =
      P.fracShift u • integralComplexMatrix (integralTranslation b * ((ρ : SL(2, O)) * M)) • x := by
  have e : integralComplexMatrix (integralTranslation b * ((ρ : SL(2, O)) * M)) =
      integralComplexMatrix (integralTranslation b) * (complexMatrix ρ * integralComplexMatrix M) := by
    rw [complexMatrix_eq, map_mul, map_mul]
  rw [e, mul_smul, mul_smul, ← mul_smul (integralComplexMatrix (integralTranslation b)) (P.fracShift u),
    P.intShift_mul_fracShift, mul_smul]

theorem one_add_mul_exp_le (γ v : ℝ) (hγ : 0 < γ) (hv : 0 ≤ v) :
    (1 + v) * Real.exp (-γ * v) ≤ 1 + 1 / γ := by
  have he : Real.exp (-γ * v) = (Real.exp (γ * v))⁻¹ := by rw [neg_mul, Real.exp_neg]
  have h1 : γ * v + 1 ≤ Real.exp (γ * v) := Real.add_one_le_exp _
  have hpos := Real.exp_pos (γ * v)
  rw [he, ← div_eq_mul_inv, div_le_iff₀ hpos]
  have hγi : 0 < 1 / γ := by positivity
  have hγv : 0 ≤ γ * v := by positivity
  have : (1 + 1 / γ) * (γ * v + 1) = γ * v + 1 + v + 1 / γ := by field_simp; ring
  nlinarith [mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 1 + 1 / γ)]

theorem zmod3_shift_cases (A n : ZMod 3) (hA : A - n = 0) (hB : A + n = 0) : A = 0 ∧ n = 0 := by
  revert A n
  decide

/-- **Away from `∞` the shifted remainder is bounded**: one factor of every pair is ramified. -/
theorem norm_shiftRemainder_off (a : ℝ) (ha : 0 < a) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (M : SL(2, O)), (colRes (M 0 0) (M 1 0) ≠ 0 ∨ normRes (M 1 0) ≠ 0) →
      ∀ (z : ℂ) (v : ℝ) (hv : 0 < v), a ≤ v →
        ‖P.shiftRemainder (integralComplexMatrix M • upperPoint z v hv)‖ ≤ K := by
  have hn := P.norm_pos
  obtain ⟨C₁, β, hC₁, hβ, hdec⟩ := P.theta_fracShift_ramified_decay a ha
  obtain ⟨C₂, hC₂, hgr⟩ := P.theta_fracShift_growth a ha
  set ρ := ‖ringComplex P.p‖ with hρdef
  set γ := β / ρ / ρ with hγdef
  have hγ : 0 < γ := by positivity
  set N : ℝ := (Fintype.card P.Res : ℝ)
  set I : ℝ := (Fintype.card P.FracIndex : ℝ)
  set E : ℝ := C₁ * C₂ * (1 + 1 / γ) with hEdef
  have hE0 : 0 ≤ E := by positivity
  refine ⟨(I * N + ‖P.fracMain‖) * E, by positivity, fun M hM z v hv hav => ?_⟩
  have hkey := one_add_mul_exp_le γ v hγ hv.le
  have hexp : Real.exp (-β * (v / ρ / ρ)) = Real.exp (-γ * v) := by
    rw [hγdef]
    congr 1
    ring
  -- the bound for one shifted pair of a level-three translate
  have hpair : ∀ (ρ' : levelThree) (u u' : O),
      ‖sourceTheta (P.fracShift u • integralComplexMatrix (integralTranslation omega * ((ρ' : SL(2, O)) * M)) •
          upperPoint z v hv) *
        sourceTheta (P.fracShift u' • integralComplexMatrix (integralTranslation (-omega) * ((ρ' : SL(2, O)) * M)) •
          upperPoint z v hv)‖ ≤ E := by
    intro ρ' u u'
    have hcP := colRes_shift_levelThree omega ρ' M
    have hcN := colRes_shift_levelThree (-omega) ρ' M
    rw [colRes_add_omega] at hcP
    rw [colRes_add_neg_omega] at hcN
    rw [norm_mul]
    by_cases hP0 : colRes (M 0 0) (M 1 0) - normRes (M 1 0) = 0
    · have hN0 : colRes (M 0 0) (M 1 0) + normRes (M 1 0) ≠ 0 := by
        intro hN0
        obtain ⟨hA, hN⟩ := zmod3_shift_cases _ _ hP0 hN0
        rcases hM with hM | hM
        · exact hM hA
        · exact hM hN
      have d := hdec u' (integralTranslation (-omega) * ((ρ' : SL(2, O)) * M)) (by rw [hcN]; exact hN0) z v hv hav
      have g := hgr u (integralTranslation omega * ((ρ' : SL(2, O)) * M)) z v hv hav
      calc _ ≤ (C₂ * (1 + v)) * (C₁ * Real.exp (-β * (v / ρ / ρ))) :=
            mul_le_mul g d (norm_nonneg _) (by positivity)
        _ = C₁ * C₂ * ((1 + v) * Real.exp (-γ * v)) := by rw [hexp]; ring
        _ ≤ E := mul_le_mul_of_nonneg_left hkey (by positivity)
    · have d := hdec u (integralTranslation omega * ((ρ' : SL(2, O)) * M)) (by rw [hcP]; exact hP0) z v hv hav
      have g := hgr u' (integralTranslation (-omega) * ((ρ' : SL(2, O)) * M)) z v hv hav
      calc _ ≤ (C₁ * Real.exp (-β * (v / ρ / ρ))) * (C₂ * (1 + v)) :=
            mul_le_mul d g (norm_nonneg _) (by positivity)
        _ = C₁ * C₂ * ((1 + v) * Real.exp (-γ * v)) := by rw [hexp]; ring
        _ ≤ E := mul_le_mul_of_nonneg_left hkey (by positivity)
  -- the trace
  have hTr : ‖P.sourceShiftTrace omega (integralComplexMatrix M • upperPoint z v hv)‖ ≤ I * N * E := by
    rw [sourceShiftTrace, P.shiftTrace_eq_sum sourceTheta sourceTheta_automorphy]
    refine (norm_sum_le _ _).trans ?_
    calc _ ≤ ∑ _i : P.FracIndex, N * E := by
          refine Finset.sum_le_sum fun i _ => ?_
          unfold shiftSum shiftCorrelation
          refine (norm_sum_le _ _).trans ?_
          calc _ ≤ ∑ _x : P.Res, E := Finset.sum_le_sum fun x _ => by
                rw [P.shift_point, P.shift_point]
                exact hpair _ _ _
            _ = N * E := by simp [N]
      _ = I * N * E := by simp [I]; ring
  -- the translated product
  have hF : ‖translatedThetaProduct (integralComplexMatrix M • upperPoint z v hv)‖ ≤ E := by
    have h := hpair 1 0 0
    simp only [P.fracShift_zero, one_smul, OneMemClass.coe_one, one_mul] at h
    simpa only [translatedThetaProduct, map_mul, mul_smul] using h
  rw [shiftRemainder]
  calc _ ≤ ‖P.sourceShiftTrace omega (integralComplexMatrix M • upperPoint z v hv)‖ +
        ‖P.fracMain‖ * ‖translatedThetaProduct (integralComplexMatrix M • upperPoint z v hv)‖ := by
        refine (norm_sub_le _ _).trans ?_
        rw [norm_mul]
    _ ≤ I * N * E + ‖P.fracMain‖ * E := add_le_add hTr (mul_le_mul_of_nonneg_left hF (norm_nonneg _))
    _ = (I * N + ‖P.fracMain‖) * E := by ring

/-! ### The global bound -/

theorem normRes_intCast (m : ℤ) : normRes (m : O) = (m : ZMod 3) ^ 2 := by
  simp only [normRes, cuspResidue_intCast]
  ring

/-- The rational class over `∞`: an integral point `ι(r)T(z, v)` with `3 ∣ r₁₀` is a level-three translate of a
point of the strip at the same height. -/
theorem exists_strip_of_three_dvd (r : SL(2, ℤ)) (hr : (3 : ℤ) ∣ r 1 0) (T : SL(2, O)) (hT : T 1 0 = 0)
    (hu : IsUnit (T 0 0)) (hu1 : IsUnit (T 1 1)) (z : ℂ) (v : ℝ) (hv : 0 < v) :
    ∃ (n : levelThree) (z' : ℂ), integralComplexMatrix (rationalEmbedding r * T) • upperPoint z v hv =
      complexMatrix n • upperPoint z' v hv := by
  have hdet : r 0 0 * r 1 1 - r 0 1 * r 1 0 = 1 := by rw [← Matrix.det_fin_two]; exact r.det_coe
  have h00 : ¬ (3 : ℤ) ∣ r 0 0 := by
    intro h
    have h1 : (3 : ℤ) ∣ r 0 0 * r 1 1 - r 0 1 * r 1 0 := dvd_sub (h.mul_right _) (hr.mul_left _)
    rw [hdet] at h1
    omega
  obtain ⟨ε, hε, hεr⟩ : ∃ ε : ℤ, ε * ε = 1 ∧ (3 : ℤ) ∣ r 0 0 - ε := by
    rcases (by omega : r 0 0 % 3 = 1 ∨ r 0 0 % 3 = 2) with h | h
    · exact ⟨1, by norm_num, by omega⟩
    · exact ⟨-1, by norm_num, by omega⟩
  let U : SL(2, ℤ) := ⟨!![ε, r 0 1; 0, ε], by rw [Matrix.det_fin_two_of]; linear_combination hε⟩
  let n₀ : SL(2, ℤ) := r * U⁻¹
  have hUinv : ((U⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = !![ε, -r 0 1; 0, ε] := by
    rw [Matrix.SpecialLinearGroup.coe_inv]
    simp [U, Matrix.adjugate_fin_two]
  have hn₀ : ∀ i j, (3 : ℤ) ∣ n₀ i j - if i = j then 1 else 0 := by
    intro i j
    have e : ∀ i j, n₀ i j = ∑ k, r i k * (U⁻¹ : SL(2, ℤ)) k j := fun i j => by
      simp [n₀, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply]
    obtain ⟨m, hm⟩ := hεr
    obtain ⟨m', hm'⟩ := hr
    fin_cases i <;> fin_cases j <;> simp only [e, hUinv, Fin.sum_univ_two] <;>
      simp
    · exact ⟨m * ε, by linear_combination ε * hm + hε⟩
    · exact ⟨-(r 0 1 * m), by linear_combination (-(r 0 1)) * hm⟩
    · exact ⟨m' * ε, by linear_combination ε * hm'⟩
    · exact ⟨-(r 1 1 * m), by linear_combination (-(r 1 1)) * hm + hdet⟩
  have hlev : rationalEmbedding n₀ ∈ levelThree := levelThree_of_entries _ (by
    intro i j
    obtain ⟨k, hk⟩ := hn₀ i j
    refine ⟨(k : O), ?_⟩
    have hk' : ((n₀ i j : ℤ) : O) - ((if i = j then 1 else 0 : ℤ) : O) = 3 * (k : O) := by
      rw [← Int.cast_sub, hk]; push_cast; ring
    simpa [rationalEmbedding, apply_ite] using hk')
  set U' : SL(2, O) := rationalEmbedding U * T
  have hU'10 : U' 1 0 = 0 := by simp [U', U, rationalEmbedding, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply,
    Fin.sum_univ_two, hT]
  have hU'00 : IsUnit (U' 0 0) := by
    have e : U' 0 0 = (ε : O) * T 0 0 := by
      simp [U', U, rationalEmbedding, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, hT]
    rw [e]
    exact (IsUnit.of_mul_eq_one (ε : O) (by exact_mod_cast hε : ((ε : ℤ) : O) * (ε : O) = 1)).mul hu
  have hU'11 : IsUnit (U' 1 1) := by
    have e : U' 1 1 = (ε : O) * T 1 1 := by
      simp [U', U, rationalEmbedding, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
    rw [e]
    exact (IsUnit.of_mul_eq_one (ε : O) (by exact_mod_cast hε : ((ε : ℤ) : O) * (ε : O) = 1)).mul hu1
  obtain ⟨z', v', hv', hp⟩ := upperPoint_surjective (integralComplexMatrix U' • upperPoint z v hv)
  have hvv : v' = v := by
    have h := height_upperTriangular U' hU'10 hU'11 z v hv
    rw [← hp, hyperbolicHeight_upperPoint] at h
    exact h
  subst hvv
  refine ⟨⟨rationalEmbedding n₀, hlev⟩, z', ?_⟩
  rw [hp, complexMatrix_eq, ← mul_smul, ← map_mul]
  congr 2
  simp only [U', n₀, map_mul, map_inv, ← mul_assoc, inv_mul_cancel_right]

/-- **`R^ω_q` is bounded on `ℍ³`.** -/
theorem shiftRemainder_bounded (h2 : (2 : P.Res) ≠ 0) : ∃ B : ℝ, ∀ w : HyperbolicSpace, ‖P.shiftRemainder w‖ ≤ B := by
  set a₀ := Real.sqrt (2 / 3)
  have ha₀ : 0 < a₀ := Real.sqrt_pos.mpr (by norm_num)
  obtain ⟨K₀, hK₀, hstrip⟩ := P.norm_shiftRemainder_strip h2 a₀ ha₀
  obtain ⟨K₁, hK₁, hoff⟩ := P.norm_shiftRemainder_off a₀ ha₀
  refine ⟨K₀ * a₀ ^ (-(7 : ℝ) / 3) + K₁, fun w => ?_⟩
  have hK₀' : 0 ≤ K₀ * a₀ ^ (-(7 : ℝ) / 3) := mul_nonneg hK₀ (Real.rpow_nonneg ha₀.le _)
  obtain ⟨M, z, v, hv, hMw, -, hfloor⟩ := bianchi_reduction_height_floor w
  obtain ⟨G, j, T, hT, hu0, hu1, hdec⟩ := three_cusp_decomposition M⁻¹
  obtain ⟨n, r, hG⟩ := G.2
  set M' : SL(2, O) := rationalEmbedding r * cuspRepresentative j * T with hM'
  have hw : w = complexMatrix n • integralComplexMatrix M' • upperPoint z v hv := by
    have h1 : w = integralComplexMatrix M⁻¹ • upperPoint z v hv := by
      rw [← hMw, ← mul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul]
    rw [h1, hdec, ← hG, complexMatrix_eq, ← mul_smul, ← map_mul, hM']
    congr 2
    simp only [mul_assoc]
  rw [hw, P.norm_shiftRemainder_levelThree]
  by_cases hc : colRes (M' 0 0) (M' 1 0) ≠ 0 ∨ normRes (M' 1 0) ≠ 0
  · exact (hoff M' hc z v hv hfloor).trans (by linarith)
  · simp only [not_or, ne_eq, not_not] at hc
    obtain ⟨hc0, hn0⟩ := hc
    have hdec1 := colRes_cuspDecomp 1 r j T hT
    simp only [OneMemClass.coe_one, one_mul] at hdec1
    have hj : j = 0 := by
      by_contra hj
      rw [← hM'] at hdec1
      rw [hdec1] at hc0
      exact mul_ne_zero (normRes_ne_zero_of_isUnit hu0) (colRes_cuspRepresentative j hj) hc0
    subst hj
    have hc1 : cuspRepresentative 0 = 1 := by
      ext i k
      fin_cases i <;> fin_cases k <;> simp [cuspRepresentative, cuspParameter, lowerCuspMatrix]
    have hM'e : M' = rationalEmbedding r * T := by rw [hM', hc1, mul_one]
    have hr10 : (3 : ℤ) ∣ r 1 0 := by
      have e : M' 1 0 = ((r 1 0 : ℤ) : O) * T 0 0 := by
        rw [hM'e]
        simp [rationalEmbedding, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, hT]
      rw [e, normRes_mul, normRes_intCast] at hn0
      have h0 := (mul_eq_zero.mp hn0).resolve_right (normRes_ne_zero_of_isUnit hu0)
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mp (pow_eq_zero_iff (by norm_num) |>.mp h0)
    obtain ⟨n', z', he⟩ := exists_strip_of_three_dvd r hr10 T hT hu0 hu1 z v hv
    rw [hM'e, he, P.norm_shiftRemainder_levelThree]
    refine (hstrip z' v hv hfloor).trans ?_
    have : v ^ (-(7 : ℝ) / 3) ≤ a₀ ^ (-(7 : ℝ) / 3) := Real.rpow_le_rpow_of_nonpos ha₀ hfloor (by norm_num)
    nlinarith

theorem sourceShiftTrace_continuous : Continuous (P.sourceShiftTrace omega) := by
  have h : P.sourceShiftTrace omega = fun w => ∑ i : P.FracIndex,
      P.shiftSum sourceTheta omega (complexMatrix (P.fracRep i) • w) :=
    funext (P.shiftTrace_eq_sum sourceTheta sourceTheta_automorphy omega)
  rw [h]
  refine continuous_finsetSum _ fun i _ => ?_
  unfold shiftSum shiftCorrelation
  exact (continuous_finsetSum _ fun x _ =>
    ((cubicSourceResidualFunction_continuous.comp (continuous_hyperbolic_action _)).comp
      (continuous_hyperbolic_action _)).mul
    ((cubicSourceResidualFunction_continuous.comp (continuous_hyperbolic_action _)).comp
      (continuous_hyperbolic_action _))).comp (continuous_hyperbolic_action _)

theorem shiftRemainder_continuous : Continuous P.shiftRemainder :=
  P.sourceShiftTrace_continuous.sub (continuous_const.mul translatedThetaProduct_continuous)

theorem shiftRemainder_memLp (h2 : (2 : P.Res) ≠ 0) :
    MemLp P.shiftRemainder 2 (hyperbolicVolume.restrict levelSet) := by
  haveI : IsFiniteMeasure (hyperbolicVolume.restrict levelSet) :=
    isFiniteMeasure_restrict.mpr levelSet_volume_lt_top.ne
  obtain ⟨B, hB⟩ := P.shiftRemainder_bounded h2
  exact MemLp.of_bound P.shiftRemainder_continuous.measurable.aestronglyMeasurable B (Eventually.of_forall hB)

/-- **`R^ω_q` is a bounded remainder.** -/
theorem shiftRemainder_remainderData (h2 : (2 : P.Res) ≠ 0) : RemainderData P.shiftRemainder where
  automorphy := P.shiftRemainder_automorphy
  measurable := P.shiftRemainder_continuous.measurable
  bounded := P.shiftRemainder_bounded h2
  high := by
    obtain ⟨K, hK, h⟩ := P.norm_shiftRemainder_strip h2 2 (by norm_num)
    exact ⟨K, hK, fun z v hv hv2 => h z v hv hv2⟩
  memLp := P.shiftRemainder_memLp h2

end PrimaryPrime

end GaloisForLFunctions.OrderSixMetaplecticTheory
