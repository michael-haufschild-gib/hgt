import GaloisForLFunctions.OrderSixMetaplecticTheory.TheConstantTermOfTheQuadraticFractionalTraceReadsTheSexticTwist

/-!
# The quadratic fractional trace is a bounded remainder

The λ-weighted trace Tr G_λ has no θ² main term: at every fractional point the main values cancel against the
quadratic character (Σ_tλ(t) = 0, Σ_{x,t}λ(t)·(middle main phase) = 0, Σ_xλ(x)χ(−9x²) = 0, λ(0) = 0), so the
decomposition over the projective line modulo q² (`fracTraceW_decomp`) bounds Tr G_λ by products of cusp
deviations of θ. Hence Tr G_λ = O(v^{−7/3}) on the standard strip, is bounded at the ramified cusps, and is a
bounded κ⁻¹-automorphic remainder (`sourceFracTraceW_remainderData`).
-/

noncomputable section

open scoped BigOperators Classical MatrixGroups

open MeasureTheory Filter

namespace GaloisForLFunctions.OrderSixMetaplecticTheory

open MetaplecticMobiusDescent MetaplecticMobiusDescent.Eisenstein MetaplecticMobiusDescent.CubicJacobi
  MetaplecticMobiusDescent.CubicEisenstein MetaplecticMobiusDescent.CubicKubota SpectralTheoryOfTheCubicCover
  MetaplecticMobiusDescent.CubicEisenstein.RationalSource

namespace PrimaryPrime

variable (P : PrimaryPrime)

theorem sourceFracTraceW_automorphy (M : levelThree) (w : HyperbolicSpace) :
    P.sourceFracTraceW (complexMatrix M • w) = complexCharacter M ^ 2 * P.sourceFracTraceW w :=
  P.fracTraceW_automorphy P.lam P.lam_squareInvariant sourceTheta sourceTheta_automorphy M w

theorem sourceFracTraceW_rational (r : SL(2, ℤ)) (w : HyperbolicSpace) :
    P.sourceFracTraceW (integralComplexMatrix (rationalEmbedding r) • w) = P.sourceFracTraceW w :=
  P.fracTraceW_rational sourceTheta sourceTheta_automorphy sourceTheta_rational_inv P.lam P.lam_squareInvariant r w

theorem norm_sourceFracTraceW_rational (G : rationalExtension) (w : HyperbolicSpace) :
    ‖P.sourceFracTraceW (integralComplexMatrix (G : SL(2, O)) • w)‖ = ‖P.sourceFracTraceW w‖ := by
  obtain ⟨n, r, hG⟩ := G.2
  have hρ : extendedComplexCharacter G = complexCharacter n := rationalExtensionValue_of_product G n r hG
  have hw : integralComplexMatrix (G : SL(2, O)) • w =
      complexMatrix n • (integralComplexMatrix (rationalEmbedding r) • w) := by
    rw [← hG, map_mul, mul_smul]
    rfl
  rw [hw, P.sourceFracTraceW_automorphy, P.sourceFracTraceW_rational, norm_mul, norm_pow, ← hρ,
    norm_extendedComplexCharacter, one_pow, one_mul]

/-- **Tr G_λ as a sum over fractional points**, for arbitrary main values R0 (height v), Rhi (height N(q)v),
Rlo (height v/N(q)): every main value cancels against λ. -/
theorem fracTraceW_decomp (h2 : (2 : P.Res) ≠ 0) (w : HyperbolicSpace) (R0 Rhi Rlo : ℂ) :
    P.sourceFracTraceW w =
      ∑ x : P.Res, P.lam x *
          (sourceTheta (P.fracShift (P.lift x) • w) * sourceTheta (P.fracShift (-P.lift x) • w) - R0 * R0) +
        ∑ x : {x : P.Res // x ≠ 0}, ∑ t : P.Res, P.lam t * (P.fracCorrelation sourceTheta (P.lift t)
          (complexMatrix (lowerThree (P.p * P.lift x.1)) • w) - P.middleMain x t (Rhi * R0) (R0 * R0)) +
        ∑ s : P.Res × P.Res, ∑ x : {x : P.Res // x ≠ 0}, P.lam x.1 * (P.chi (-9 * x.1 ^ 2) *
          (P.heckeLow sourceTheta (-P.lowBeta (-P.lift x.1)) (P.contraction • complexMatrix (transThree (P.sqLift s)) • w) *
            P.heckeLow sourceTheta (-P.lowBeta (P.lift x.1)) (P.contraction • complexMatrix (transThree (P.sqLift s)) • w) -
              Rlo * Rlo)) := by
  have e1 : ∑ x : P.Res, P.lam x *
      (sourceTheta (P.fracShift (P.lift x) • w) * sourceTheta (P.fracShift (-P.lift x) • w) - R0 * R0) =
      P.fracSumW P.lam sourceTheta w := by
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, P.sum_lam_eq_zero h2, zero_mul, sub_zero]
    rfl
  have e2 : ∑ x : {x : P.Res // x ≠ 0}, ∑ t : P.Res, P.lam t * (P.fracCorrelation sourceTheta (P.lift t)
      (complexMatrix (lowerThree (P.p * P.lift x.1)) • w) - P.middleMain x t (Rhi * R0) (R0 * R0)) =
      ∑ x : {x : P.Res // x ≠ 0}, P.fracSumW P.lam sourceTheta (complexMatrix (lowerThree (P.p * P.lift x.1)) • w) := by
    simp_rw [mul_sub, Finset.sum_sub_distrib]
    rw [P.sum_lam_middleMain h2, sub_zero]
    rfl
  have e4 : ∑ s : P.Res × P.Res, ∑ x : {x : P.Res // x ≠ 0}, P.lam x.1 * (P.chi (-9 * x.1 ^ 2) *
      (P.heckeLow sourceTheta (-P.lowBeta (-P.lift x.1)) (P.contraction • complexMatrix (transThree (P.sqLift s)) • w) *
        P.heckeLow sourceTheta (-P.lowBeta (P.lift x.1)) (P.contraction • complexMatrix (transThree (P.sqLift s)) • w) -
          Rlo * Rlo)) =
      ∑ s : P.Res × P.Res, P.fracSumW P.lam sourceTheta
        (integralComplexMatrix sO • complexMatrix (transThree (P.sqLift s)) • w) := by
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [P.fracSumW_sO sourceTheta sourceTheta_automorphy sourceTheta_rational_inv, MulChar.map_zero, zero_mul, zero_add]
    have hz : ∑ x : {x : P.Res // x ≠ 0}, P.lam x.1 * (P.chi (-9 * x.1 ^ 2) * (Rlo * Rlo)) = 0 := by
      rw [show (∑ x : {x : P.Res // x ≠ 0}, P.lam x.1 * (P.chi (-9 * x.1 ^ 2) * (Rlo * Rlo))) =
          (∑ x : {x : P.Res // x ≠ 0}, P.lam x.1 * P.chi (-9 * x.1 ^ 2)) * (Rlo * Rlo) by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun x _ => by ring, P.sum_lam_low h2, zero_mul]
    refine Eq.trans ?_ (sub_zero _)
    rw [← hz, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun x _ => by ring
  rw [e1, e2, e4, sourceFracTraceW,
    P.fracTraceW_eq sourceTheta sourceTheta_automorphy sourceTheta_rational_inv _ P.lam_squareInvariant]
  ring

/-- **Tr G_λ is controlled by the fractional points.** -/
theorem norm_sourceFracTraceW_le (h2 : (2 : P.Res) ≠ 0) (w : HyperbolicSpace) (R0 Rhi Rlo : ℂ) (M D : ℝ)
    (hR0 : ‖R0‖ ≤ M) (hRhi : ‖Rhi‖ ≤ M) (hRlo : ‖Rlo‖ ≤ M)
    (bfr : ∀ u : O, ‖sourceTheta (P.fracShift u • w) - R0‖ ≤ D)
    (bhi : ‖sourceTheta (P.dilation • P.dilation • w) - Rhi‖ ≤ D)
    (blo : ∀ (r : O) (s : P.Res × P.Res),
      ‖P.heckeLow sourceTheta r (P.contraction • complexMatrix (transThree (P.sqLift s)) • w) - Rlo‖ ≤ D) :
    ‖P.sourceFracTraceW w‖ ≤ ((Fintype.card P.Res : ℝ) + (Fintype.card P.Res : ℝ) * (Fintype.card P.Res : ℝ) +
      (Fintype.card P.Res : ℝ) ^ 2 * (Fintype.card P.Res : ℝ)) * (2 * M * D + D ^ 2) := by
  set N : ℝ := (Fintype.card P.Res : ℝ) with hNdef
  set Eb : ℝ := 2 * M * D + D ^ 2 with hEbdef
  have hEb : ∀ X Y PP QQ : ℂ, ‖PP‖ ≤ M → ‖QQ‖ ≤ M → ‖X - PP‖ ≤ D → ‖Y - QQ‖ ≤ D →
      ‖X * Y - PP * QQ‖ ≤ Eb := fun X Y PP QQ h1 h2 h3 h4 => norm_mul_sub_mul_le h1 h2 h3 h4
  have hEb0 : 0 ≤ Eb := (norm_nonneg _).trans (hEb _ _ _ _ hR0 hR0 (bfr 0) (bfr 0))
  have hlam : ∀ (t : P.Res) (X : ℂ), ‖X‖ ≤ Eb → ‖P.lam t * X‖ ≤ Eb := fun t X hX =>
    (norm_mul_le _ _).trans ((mul_le_of_le_one_left (norm_nonneg _) (P.norm_lam_le t)).trans hX)
  have hcard : (Fintype.card {x : P.Res // x ≠ 0} : ℝ) ≤ N := by
    rw [hNdef]
    exact_mod_cast Fintype.card_subtype_le _
  have hs1 : ‖∑ x : P.Res, P.lam x * (sourceTheta (P.fracShift (P.lift x) • w) *
      sourceTheta (P.fracShift (-P.lift x) • w) - R0 * R0)‖ ≤ N * Eb := by
    refine (norm_sum_le _ _).trans ?_
    calc _ ≤ ∑ _x : P.Res, Eb := Finset.sum_le_sum fun x _ => hlam _ _ (hEb _ _ _ _ hR0 hR0 (bfr _) (bfr _))
      _ = N * Eb := by simp [hNdef]
  have hterm : ∀ (x : {x : P.Res // x ≠ 0}) (t : P.Res), ‖P.fracCorrelation sourceTheta (P.lift t)
      (complexMatrix (lowerThree (P.p * P.lift x.1)) • w) - P.middleMain x t (Rhi * R0) (R0 * R0)‖ ≤ Eb := by
    intro x t
    rw [P.fracCorrelation_lowerThree sourceTheta sourceTheta_automorphy h2 x t, middleMain]
    split_ifs
    · rw [← mul_sub]
      exact (norm_mul_le _ _).trans ((mul_le_of_le_one_left (norm_nonneg _) (P.norm_highPhase_le x)).trans
        (hEb _ _ _ _ hRhi hR0 bhi (bfr _)))
    · rw [← mul_sub]
      exact (norm_mul_le _ _).trans ((mul_le_of_le_one_left (norm_nonneg _) (P.norm_highPhase_le x)).trans
        (hEb _ _ _ _ hRhi hR0 bhi (bfr _)))
    · rw [← mul_sub]
      exact (norm_mul_le _ _).trans ((mul_le_of_le_one_left (norm_nonneg _) (P.norm_chi_le _)).trans
        (hEb _ _ _ _ hR0 hR0 (bfr _) (bfr _)))
  have hs2 : ‖∑ x : {x : P.Res // x ≠ 0}, ∑ t : P.Res, P.lam t * (P.fracCorrelation sourceTheta (P.lift t)
      (complexMatrix (lowerThree (P.p * P.lift x.1)) • w) - P.middleMain x t (Rhi * R0) (R0 * R0))‖ ≤
      N * (N * Eb) := by
    refine (norm_sum_le _ _).trans ?_
    calc _ ≤ ∑ _x : {x : P.Res // x ≠ 0}, N * Eb := by
          refine Finset.sum_le_sum fun x _ => (norm_sum_le _ _).trans ?_
          calc _ ≤ ∑ _t : P.Res, Eb := Finset.sum_le_sum fun t _ => hlam _ _ (hterm x t)
            _ = N * Eb := by simp [hNdef]
      _ = (Fintype.card {x : P.Res // x ≠ 0} : ℝ) * (N * Eb) := by simp
      _ ≤ N * (N * Eb) := mul_le_mul_of_nonneg_right hcard (by positivity)
  have hs4 : ‖∑ s : P.Res × P.Res, ∑ x : {x : P.Res // x ≠ 0}, P.lam x.1 * (P.chi (-9 * x.1 ^ 2) *
      (P.heckeLow sourceTheta (-P.lowBeta (-P.lift x.1)) (P.contraction • complexMatrix (transThree (P.sqLift s)) • w) *
        P.heckeLow sourceTheta (-P.lowBeta (P.lift x.1)) (P.contraction • complexMatrix (transThree (P.sqLift s)) • w) -
          Rlo * Rlo))‖ ≤ N ^ 2 * (N * Eb) := by
    refine (norm_sum_le _ _).trans ?_
    calc _ ≤ ∑ _s : P.Res × P.Res, N * Eb := by
          refine Finset.sum_le_sum fun s _ => (norm_sum_le _ _).trans ?_
          calc _ ≤ ∑ _x : {x : P.Res // x ≠ 0}, Eb := by
                refine Finset.sum_le_sum fun x _ => hlam _ _ ((norm_mul_le _ _).trans ?_)
                exact (mul_le_of_le_one_left (norm_nonneg _) (P.norm_chi_le _)).trans
                  (hEb _ _ _ _ hRlo hRlo (blo _ _) (blo _ _))
            _ = (Fintype.card {x : P.Res // x ≠ 0} : ℝ) * Eb := by simp
            _ ≤ N * Eb := mul_le_mul_of_nonneg_right hcard hEb0
      _ = N ^ 2 * (N * Eb) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, nsmul_eq_mul, hNdef]
          push_cast
          ring
  rw [P.fracTraceW_decomp h2 w R0 Rhi Rlo]
  calc _ ≤ _ := (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ N * Eb + N * (N * Eb) + N ^ 2 * (N * Eb) := by gcongr
    _ = _ := by ring

/-- **Tr G_λ = O(v^{−7/3}) on the standard strip above any fixed height.** -/
theorem norm_sourceFracTraceW_strip (h2 : (2 : P.Res) ≠ 0) (a : ℝ) (ha : 0 < a) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (z : ℂ) (v : ℝ) (hv : 0 < v), a ≤ v →
      ‖P.sourceFracTraceW (upperPoint z v hv)‖ ≤ K * v ^ (-(7 : ℝ) / 3) := by
  have hn := P.norm_pos
  have hρ1 := P.one_le_norm
  set ρ := ‖ringComplex P.p‖ with hρdef
  obtain ⟨C₁, hC₁, hdec⟩ := cubicSourceResidualFunction_cusp_decay_from_height (a / ρ / ρ) (div_pos (div_pos ha hn) hn)
  set c : ℂ := 3 * (Real.pi : ℂ) * constantArithmeticResidue with hcdef
  set N : ℝ := (Fintype.card P.Res : ℝ) with hNdef
  set K0 : ℝ := N + N * N + N ^ 2 * N with hK0
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
  have hbound := P.norm_sourceFracTraceW_le h2 (upperPoint z v hv) (c * (v : ℂ) ^ (2 / 3 : ℂ))
    (c * ((ρ * (ρ * v) : ℝ) : ℂ) ^ (2 / 3 : ℂ)) (c * ((v / ρ / ρ : ℝ) : ℂ) ^ (2 / 3 : ℂ)) M D hR0M hRhiM hRloM
    (fun u => by
      simp only [fracShift, complexTranslation_action]
      exact hcube _ v hv hlov)
    (by
      simp only [P.dilation_upperPoint]
      exact hcube _ _ hhi (le_trans hlov (le_trans (le_mul_of_one_le_left hv.le hρ1)
        (mul_le_mul_of_nonneg_left (le_mul_of_one_le_left hv.le hρ1) hn.le))))
    (fun r s => by
      simp only [transThree_smul_upperPoint, P.contraction_upperPoint, P.heckeLow_point]
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

/-- **Tr G_λ is bounded at the ramified cusps.** -/
theorem norm_sourceFracTraceW_ramified (a : ℝ) (ha : 0 < a) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (j : Fin 3), j ≠ 0 → ∀ (z : ℂ) (v : ℝ) (hv : 0 < v), a ≤ v →
      ‖P.sourceFracTraceW (integralComplexMatrix (cuspRepresentative j) • upperPoint z v hv)‖ ≤ K := by
  obtain ⟨C, hC, hθ⟩ := P.theta_fracShift_ramified a ha
  set N : ℝ := (Fintype.card P.Res : ℝ)
  set I : ℝ := (Fintype.card P.FracIndex : ℝ)
  refine ⟨I * (N * C ^ 2), by positivity, fun j hj z v hv hav => ?_⟩
  rw [sourceFracTraceW, P.fracTraceW_eq_sum P.lam P.lam_squareInvariant sourceTheta sourceTheta_automorphy]
  have hpt : ∀ (i : P.FracIndex) (t : O), ‖sourceTheta (P.fracShift t • complexMatrix (P.fracRep i) •
      integralComplexMatrix (cuspRepresentative j) • upperPoint z v hv)‖ ≤ C := by
    intro i t
    rw [← mul_smul (complexMatrix (P.fracRep i)) (integralComplexMatrix (cuspRepresentative j)), complexMatrix_eq,
      ← map_mul]
    exact hθ t _ (by rw [colRes_levelThree_mul]; exact colRes_cuspRepresentative j hj) z v hv hav
  have hG : ∀ i : P.FracIndex, ‖P.fracSumW P.lam sourceTheta (complexMatrix (P.fracRep i) •
      integralComplexMatrix (cuspRepresentative j) • upperPoint z v hv)‖ ≤ N * C ^ 2 := by
    intro i
    unfold fracSumW fracCorrelation
    refine (norm_sum_le _ _).trans ?_
    calc ∑ x : P.Res, ‖P.lam x * (sourceTheta (P.fracShift (P.lift x) • complexMatrix (P.fracRep i) •
          integralComplexMatrix (cuspRepresentative j) • upperPoint z v hv) *
          sourceTheta (P.fracShift (-P.lift x) • complexMatrix (P.fracRep i) •
            integralComplexMatrix (cuspRepresentative j) • upperPoint z v hv))‖ ≤ ∑ _x : P.Res, C ^ 2 := by
          refine Finset.sum_le_sum fun x _ => ?_
          refine (norm_mul_le _ _).trans ((mul_le_of_le_one_left (norm_nonneg _) (P.norm_lam_le x)).trans ?_)
          rw [norm_mul, sq]
          exact mul_le_mul (hpt i _) (hpt i _) (norm_nonneg _) hC
      _ = N * C ^ 2 := by simp [N]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ i : P.FracIndex, ‖P.fracSumW P.lam sourceTheta (complexMatrix (P.fracRep i) •
        integralComplexMatrix (cuspRepresentative j) • upperPoint z v hv)‖ ≤ ∑ _i : P.FracIndex, N * C ^ 2 :=
        Finset.sum_le_sum fun i _ => hG i
    _ = I * (N * C ^ 2) := by simp [I]

/-- **Tr G_λ is bounded on ℍ³.** -/
theorem sourceFracTraceW_bounded (h2 : (2 : P.Res) ≠ 0) :
    ∃ B : ℝ, ∀ w : HyperbolicSpace, ‖P.sourceFracTraceW w‖ ≤ B := by
  set a₀ := Real.sqrt (2 / 3)
  have ha₀ : 0 < a₀ := Real.sqrt_pos.mpr (by norm_num)
  obtain ⟨K₀, hK₀, hstrip⟩ := P.norm_sourceFracTraceW_strip h2 a₀ ha₀
  obtain ⟨K₁, hK₁, hram⟩ := P.norm_sourceFracTraceW_ramified a₀ ha₀
  refine ⟨K₀ * a₀ ^ (-(7 : ℝ) / 3) + K₁, fun w => ?_⟩
  obtain ⟨M, z, v, hv, hMw, -, hfloor⟩ := bianchi_reduction_height_floor w
  obtain ⟨G', j, T, hT, -, hu1, hdec'⟩ := three_cusp_decomposition M⁻¹
  have hw : w = integralComplexMatrix (G' : SL(2, O)) •
      (integralComplexMatrix (cuspRepresentative j * T) • upperPoint z v hv) := by
    rw [← mul_smul, ← map_mul, ← mul_assoc, ← hdec', ← hMw, ← mul_smul, ← map_mul, inv_mul_cancel,
      map_one, one_smul]
  rw [hw, P.norm_sourceFracTraceW_rational]
  obtain ⟨z', v', hv', hp⟩ := upperPoint_surjective (integralComplexMatrix T • upperPoint z v hv)
  have hvv : v' = v := by
    have h := height_upperTriangular T hT hu1 z v hv
    rw [← hp, hyperbolicHeight_upperPoint] at h
    exact h
  subst hvv
  rw [map_mul, mul_smul, ← hp]
  by_cases hj : j = 0
  · subst hj
    have hc1 : cuspRepresentative 0 = 1 := by
      ext i k
      fin_cases i <;> fin_cases k <;> simp [cuspRepresentative, cuspParameter, lowerCuspMatrix]
    rw [hc1, map_one, one_smul]
    refine (hstrip z' v' hv' hfloor).trans ?_
    have : v' ^ (-(7 : ℝ) / 3) ≤ a₀ ^ (-(7 : ℝ) / 3) := Real.rpow_le_rpow_of_nonpos ha₀ hfloor (by norm_num)
    nlinarith
  · exact (hram j hj z' v' hv' hfloor).trans (by nlinarith [Real.rpow_nonneg ha₀.le (-(7 : ℝ) / 3)])

theorem sourceFracTraceW_continuous : Continuous P.sourceFracTraceW := by
  have h : P.sourceFracTraceW = fun w => ∑ i : P.FracIndex,
      P.fracSumW P.lam sourceTheta (complexMatrix (P.fracRep i) • w) :=
    funext (P.fracTraceW_eq_sum P.lam P.lam_squareInvariant sourceTheta sourceTheta_automorphy)
  rw [h]
  exact continuous_finsetSum _ fun i _ => P.continuous_fracSumW_source.comp (continuous_hyperbolic_action _)

theorem sourceFracTraceW_memLp (h2 : (2 : P.Res) ≠ 0) :
    MemLp P.sourceFracTraceW 2 (hyperbolicVolume.restrict levelSet) := by
  haveI : IsFiniteMeasure (hyperbolicVolume.restrict levelSet) :=
    isFiniteMeasure_restrict.mpr levelSet_volume_lt_top.ne
  obtain ⟨B, hB⟩ := P.sourceFracTraceW_bounded h2
  exact MemLp.of_bound P.sourceFracTraceW_continuous.measurable.aestronglyMeasurable B (Eventually.of_forall hB)

theorem sourceFracTraceW_automorphy_inv (M : levelThree) (w : HyperbolicSpace) :
    P.sourceFracTraceW (complexMatrix M • w) = (complexCharacter M)⁻¹ * P.sourceFracTraceW w := by
  rw [P.sourceFracTraceW_automorphy, complexCharacter_sq_eq_inv]

/-- **Tr G_λ is a bounded remainder.** -/
theorem sourceFracTraceW_remainderData (h2 : (2 : P.Res) ≠ 0) : RemainderData P.sourceFracTraceW where
  automorphy := P.sourceFracTraceW_automorphy_inv
  measurable := P.sourceFracTraceW_continuous.measurable
  bounded := P.sourceFracTraceW_bounded h2
  high := by
    obtain ⟨K, hK, h⟩ := P.norm_sourceFracTraceW_strip h2 2 (by norm_num)
    exact ⟨K, hK, fun z v hv hv2 => h z v hv hv2⟩
  memLp := P.sourceFracTraceW_memLp h2

end PrimaryPrime

end GaloisForLFunctions.OrderSixMetaplecticTheory
