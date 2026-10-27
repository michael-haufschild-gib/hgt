import GaloisForLFunctions.ArithmeticCorrespondencePositivity.TheReceiverAbelAtomsHaveTheirEffectivePoleOrder
import GaloisForLFunctions.ArithmeticCorrespondencePositivity.ReceiverBoundaryZerosAreLocallyFinite
import GaloisForLFunctions.ArithmeticCorrespondencePositivity.FiniteWindowPoleMassLimits
import GaloisForLFunctions.ArithmeticCorrespondencePositivity.TheReceiverSymbolAtTheClosedZeroFrontier

/-!
# Maximal effective pole order on compact receiver windows

At the zero abscissa, a compact window has only finitely many translated
poles. Its largest effective order determines the exact normalization:
lower orders disappear, and the surviving weights are the squared canonical
Laurent coefficients. The complement of small pole windows stays bounded.
-/

open Complex Set Filter Topology MeasureTheory
open RHTower GaloisForLFunctions.ArithmeticOrientationTheory

noncomputable section

namespace GaloisForLFunctions.ArithmeticCorrespondencePositivity

/-- The mass of a pole at its own Abel scale. -/
def receiverPoleAtomMass (ε : ℝ) (m : ℕ) (ρ : ℂ) : ℝ :=
  poleMassConstant m *
    ‖meromorphicTrailingCoeffAt (centeredReceiverSymbol ε) (ρ - (ε : ℂ))‖ ^ 2

/-- Every surviving pole contributes strictly positive mass. -/
theorem receiverPoleAtomMass_pos {ε : ℝ} (hε : 0 < ε) {ρ : ℂ}
    (hz : riemannZeta ρ = 0) (hmax : ρ.re = zetaZeroAbscissa)
    (hre : 1 / 2 + ε < ρ.re) (hre1 : ρ.re < 1) {m : ℕ}
    (hm : 0 < m) (horder : visibleTranslatedZetaOrder ε ρ = (m : ℕ∞)) :
    0 < receiverPoleAtomMass ε m ρ := by
  have ha := (receiver_pole_coefficient_ne_zero_and_atom hε hz hmax hre hre1 hm horder).1
  exact mul_pos (poleMassConstant_pos hm) (sq_pos_of_pos (norm_pos_iff.mpr ha))

/-- At a prescribed maximal scale, precisely the poles of that order survive. -/
theorem exists_receiver_window_limit_at_higher_order {ε : ℝ} (hε : 0 < ε) {ρ : ℂ}
    (hz : riemannZeta ρ = 0) (hmax : ρ.re = zetaZeroAbscissa)
    (hre : 1 / 2 + ε < ρ.re) (hre1 : ρ.re < 1) {m M : ℕ}
    (hM : 1 ≤ M) (hmM : m ≤ M)
    (horder : visibleTranslatedZetaOrder ε ρ = (m : ℕ∞)) :
    ∃ δ₀ > 0, ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
      ∀ (w : ℝ → ℝ) (W : ℝ), Continuous w → (∀ y, |w y| ≤ W) →
        Tendsto (fun e : ℝ => e ^ (2 * M - 1) *
          ∫ y in Icc (ρ.im - δ) (ρ.im + δ),
            ‖lineSymbol (receiverLogProfile ε) (zetaZeroAbscissa - ε - 1 / 2 + e) y‖ ^ 2 * w y)
          (𝓝[>] 0) (𝓝 ((if visibleTranslatedZetaOrder ε ρ = (M : ℕ∞)
            then receiverPoleAtomMass ε M ρ else 0) * w ρ.im)) := by
  classical
  by_cases hm : m = 0
  · have ho : visibleTranslatedZetaOrder ε ρ = 0 := by simpa only [hm, Nat.cast_zero] using horder
    obtain ⟨δ₀, hδ₀, B, hB, hb⟩ := exists_receiver_regular_window_bound hε hz hmax hre hre1 ho
    refine ⟨δ₀, hδ₀, fun δ hδ hδle w W hw hwW => ?_⟩
    have hne : (0 : ℕ∞) ≠ (M : ℕ∞) := by exact_mod_cast (by omega : (0 : ℕ) ≠ M)
    rw [ho, if_neg hne, zero_mul]
    apply tendsto_scaled_setIntegral_of_bounded (by omega : 0 < 2 * M - 1) hδ
      (C := B ^ 2 * W) isCompact_Icc.measure_lt_top
    intro e he y hy
    have hy' : y ∈ Icc (ρ.im - δ₀) (ρ.im + δ₀) :=
      ⟨by linarith [hy.1], by linarith [hy.2]⟩
    rw [norm_mul, norm_pow, norm_norm, Real.norm_eq_abs]
    exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _)
      (hb e ⟨he.1, he.2.trans_le hδle⟩ y hy') 2) (hwW y) (abs_nonneg _) (sq_nonneg B)
  · have hm0 : 0 < m := Nat.pos_of_ne_zero hm
    obtain ⟨_, δ₀, hδ₀, hatom⟩ :=
      receiver_pole_coefficient_ne_zero_and_atom hε hz hmax hre hre1 hm0 horder
    refine ⟨δ₀, hδ₀, fun δ hδ hδle w W hw hwW => ?_⟩
    by_cases hmEq : m = M
    · subst m
      rw [if_pos horder]
      exact hatom δ hδ hδle w W hw hwW
    · have hmLt : m < M := lt_of_le_of_ne hmM hmEq
      have hne : (m : ℕ∞) ≠ (M : ℕ∞) := by exact_mod_cast hmEq
      rw [horder, if_neg hne, zero_mul]
      exact tendsto_higher_scale_mass_zero (by omega : 2 * m - 1 < 2 * M - 1)
        (hatom δ hδ hδle w W hw hwW)

/-- A compact window, with no pole on its endpoints, is the sum of its
maximal-order local atoms. No hypothesis on mass outside the window is used. -/
theorem tendsto_receiver_compact_window_at_order {ε : ℝ} (hε : 0 < ε)
    (hθ : 0 < zetaZeroAbscissa - ε - 1 / 2) (hΘ1 : zetaZeroAbscissa < 1)
    (a b : ℝ) (Z : Finset ℂ)
    (hZ : ∀ ρ : ℂ, ρ ∈ Z ↔ riemannZeta ρ = 0 ∧
      ρ.re = zetaZeroAbscissa ∧ ρ.im ∈ Icc a b)
    (hends : ∀ ρ ∈ Z, a < ρ.im ∧ ρ.im < b) {M : ℕ} (hM : 1 ≤ M)
    (horders : ∀ ρ ∈ Z,
      analyticOrderNatAt riemannZeta ρ - analyticOrderNatAt riemannZeta (ρ - (ε : ℂ)) ≤ M)
    (w : ℝ → ℝ) (W : ℝ) (hw : Continuous w) (hwW : ∀ y, |w y| ≤ W) :
    Tendsto (fun e : ℝ => e ^ (2 * M - 1) * ∫ y in Icc a b,
      ‖lineSymbol (receiverLogProfile ε) (zetaZeroAbscissa - ε - 1 / 2 + e) y‖ ^ 2 * w y)
      (𝓝[>] 0) (𝓝 (∑ ρ ∈ Z,
        (if visibleTranslatedZetaOrder ε ρ = (M : ℕ∞)
          then receiverPoleAtomMass ε M ρ else 0) * w ρ.im)) := by
  classical
  have hatom : ∀ ρ ∈ Z, ∃ δ₀ > 0, ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
      Tendsto (fun e : ℝ => e ^ (2 * M - 1) * ∫ y in Icc (ρ.im - δ) (ρ.im + δ),
        ‖lineSymbol (receiverLogProfile ε) (zetaZeroAbscissa - ε - 1 / 2 + e) y‖ ^ 2 * w y)
        (𝓝[>] 0) (𝓝 ((if visibleTranslatedZetaOrder ε ρ = (M : ℕ∞)
          then receiverPoleAtomMass ε M ρ else 0) * w ρ.im)) := by
    intro ρ hρ
    obtain ⟨hz, hre, _⟩ := (hZ ρ).mp hρ
    have hr1 : ρ.re < 1 := by rw [hre]; exact hΘ1
    have hρ1 : ρ ≠ 1 := by intro h; rw [h, one_re] at hr1; linarith
    have hs1 : ρ - (ε : ℂ) ≠ 1 := by
      intro h
      have := congrArg Complex.re h
      simp only [sub_re, ofReal_re, one_re] at this
      linarith
    obtain ⟨δ₀, hδ₀, h⟩ := exists_receiver_window_limit_at_higher_order hε hz hre
      (by rw [hre]; linarith) hr1 hM (horders ρ hρ)
      (visibleTranslatedZetaOrder_eq_nat_sub hρ1 hs1)
    exact ⟨δ₀, hδ₀, fun δ hδ hδle => h δ hδ hδle w W hw hwW⟩
  choose! δ₀ hδ₀ hT using hatom
  have hevδ : ∀ᶠ δ in 𝓝[>] (0 : ℝ), 0 < δ ∧
      (∀ ρ ∈ Z, δ ≤ δ₀ ρ ∧ δ < ρ.im - a ∧ δ < b - ρ.im) ∧
      ∀ ρ ∈ Z, ∀ ρ' ∈ Z, ρ ≠ ρ' → 2 * δ < |ρ.im - ρ'.im| := by
    refine eventually_mem_nhdsWithin.and (Filter.Eventually.and ?_ ?_)
    · refine (eventually_all_finset Z).mpr fun ρ hρ => ?_
      filter_upwards [((gt_mem_nhds (hδ₀ ρ hρ)).filter_mono nhdsWithin_le_nhds),
        ((gt_mem_nhds (sub_pos.mpr (hends ρ hρ).1)).filter_mono nhdsWithin_le_nhds),
        ((gt_mem_nhds (sub_pos.mpr (hends ρ hρ).2)).filter_mono nhdsWithin_le_nhds)]
        with δ h₀ ha hb
      exact ⟨h₀.le, ha, hb⟩
    · refine (eventually_all_finset Z).mpr fun ρ hρ =>
        (eventually_all_finset Z).mpr fun ρ' hρ' => ?_
      by_cases hne : ρ = ρ'
      · exact Eventually.of_forall fun δ h => absurd hne h
      · have him : ρ.im ≠ ρ'.im := fun h => hne
          (Complex.ext (by rw [((hZ ρ).mp hρ).2.1, ((hZ ρ').mp hρ').2.1]) h)
        have hpos : 0 < |ρ.im - ρ'.im| := abs_pos.mpr (sub_ne_zero.mpr him)
        exact ((gt_mem_nhds (show (0 : ℝ) < |ρ.im - ρ'.im| / 2 by linarith)).filter_mono
          nhdsWithin_le_nhds).mono fun δ h _ => by linarith
  obtain ⟨δ, hδ, hδle, hgap⟩ := hevδ.exists
  let J : ℂ → Set ℝ := fun ρ => Icc (ρ.im - δ) (ρ.im + δ)
  let U : Set ℝ := ⋃ ρ ∈ Z, J ρ
  have hdisj : (Z : Set ℂ).Pairwise (Function.onFun Disjoint J) := by
    intro ρ hρ ρ' hρ' hne
    refine Set.disjoint_left.mpr fun y hy hy' => ?_
    have hlt := hgap ρ hρ ρ' hρ' hne
    have hle : |ρ.im - ρ'.im| ≤ 2 * δ := abs_le.mpr
      ⟨by linarith only [hy.2, hy'.1], by linarith only [hy.1, hy'.2]⟩
    linarith
  have hsub : U ⊆ Icc a b := by
    intro y hy
    obtain ⟨ρ, hρ, hy⟩ := mem_iUnion₂.mp hy
    exact ⟨by linarith [hy.1, (hδle ρ hρ).2.1],
      by linarith [hy.2, (hδle ρ hρ).2.2]⟩
  obtain ⟨η, hη, B, hB, hb⟩ := exists_receiver_bound_away_boundary_zeros hε hθ hΘ1 a b Z hZ hδ
  let f : ℝ → ℝ → ℝ := fun e y =>
    ‖lineSymbol (receiverLogProfile ε) (zetaZeroAbscissa - ε - 1 / 2 + e) y‖ ^ 2 * w y
  have hrest : Tendsto (fun e : ℝ => e ^ (2 * M - 1) * ∫ y in Icc a b \ U, f e y)
      (𝓝[>] 0) (𝓝 0) := by
    apply tendsto_scaled_setIntegral_of_bounded (by omega : 0 < 2 * M - 1) hη
      (C := B ^ 2 * W)
      (lt_of_le_of_lt (measure_mono sdiff_subset) isCompact_Icc.measure_lt_top)
    intro e he y hy
    have haway : ∀ ρ ∈ Z, δ ≤ |y - ρ.im| := by
      intro ρ hρ
      by_contra h
      have hlt : |y - ρ.im| < δ := lt_of_not_ge h
      have habs := abs_lt.mp hlt
      exact hy.2 (mem_iUnion₂.mpr ⟨ρ, hρ, by
        change ρ.im - δ ≤ y ∧ y ≤ ρ.im + δ
        constructor <;> linarith⟩)
    dsimp only [f]
    rw [norm_mul, norm_pow, norm_norm, Real.norm_eq_abs]
    exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) (hb e he y hy.1 haway) 2)
      (hwW y) (abs_nonneg _) (sq_nonneg B)
  apply tendsto_scaled_integral_of_finite_windows Z
    (fun _ _ => measurableSet_Icc) hdisj hsub ?_
    (fun ρ hρ => hT ρ hρ δ hδ (hδle ρ hρ).1) hrest
  filter_upwards [self_mem_nhdsWithin] with e he
  have hcont := continuous_lineSymbol (receiver_data_at_zeroAbscissa hε hθ he).1
  exact ContinuousOn.integrableOn_compact isCompact_Icc ((hcont.norm.pow 2).mul hw).continuousOn

/-- Every compact interval whose endpoints avoid boundary zeros has an exact
finite atom law at its maximal effective pole order (or scale one if there
are no visible poles). The order and all coefficients are intrinsic. -/
theorem exists_receiver_compact_maximal_order_law_of_abscissa_lt_one {ε : ℝ} (hε : 0 < ε)
    (hθ : 0 < zetaZeroAbscissa - ε - 1 / 2) (hΘ1 : zetaZeroAbscissa < 1)
    (a b : ℝ)
    (hends : ∀ ρ : ℂ, riemannZeta ρ = 0 → ρ.re = zetaZeroAbscissa →
      ρ.im ≠ a ∧ ρ.im ≠ b) :
    ∃ Z : Finset ℂ,
      (∀ ρ : ℂ, ρ ∈ Z ↔ riemannZeta ρ = 0 ∧
        ρ.re = zetaZeroAbscissa ∧ ρ.im ∈ Icc a b) ∧
      let M := max 1 (Z.sup fun ρ =>
        analyticOrderNatAt riemannZeta ρ - analyticOrderNatAt riemannZeta (ρ - (ε : ℂ)))
      ∀ (w : ℝ → ℝ), Continuous w →
        Tendsto (fun e : ℝ => e ^ (2 * M - 1) * ∫ y in Icc a b,
          ‖lineSymbol (receiverLogProfile ε) (zetaZeroAbscissa - ε - 1 / 2 + e) y‖ ^ 2 * w y)
          (𝓝[>] 0) (𝓝 (∑ ρ ∈ Z,
            (if visibleTranslatedZetaOrder ε ρ = (M : ℕ∞)
              then receiverPoleAtomMass ε M ρ else 0) * w ρ.im)) := by
  classical
  obtain ⟨Z, hZ⟩ := exists_receiver_boundary_zero_finset hΘ1 a b
  refine ⟨Z, hZ, fun w hw => ?_⟩
  let M := max 1 (Z.sup fun ρ =>
    analyticOrderNatAt riemannZeta ρ - analyticOrderNatAt riemannZeta (ρ - (ε : ℂ)))
  have hinside : ∀ ρ ∈ Z, a < ρ.im ∧ ρ.im < b := by
    intro ρ hρ
    obtain ⟨hz, hre, hi⟩ := (hZ ρ).mp hρ
    obtain ⟨ha, hb⟩ := hends ρ hz hre
    exact ⟨lt_of_le_of_ne hi.1 ha.symm, lt_of_le_of_ne hi.2 hb⟩
  have horders : ∀ ρ ∈ Z,
      analyticOrderNatAt riemannZeta ρ - analyticOrderNatAt riemannZeta (ρ - (ε : ℂ)) ≤ M := by
    intro ρ hρ
    exact (Finset.le_sup (f := fun ρ =>
      analyticOrderNatAt riemannZeta ρ - analyticOrderNatAt riemannZeta (ρ - (ε : ℂ))) hρ).trans
      (le_max_right _ _)
  obtain ⟨D, hD⟩ := (isCompact_Icc : IsCompact (Icc a b)).exists_bound_of_continuousOn
    hw.continuousOn
  let W : ℝ := max D 0
  have hW : 0 ≤ W := le_max_right _ _
  let v : ℝ → ℝ := fun y => max (-W) (min W (w y))
  have hv : Continuous v := by dsimp only [v]; fun_prop
  have hvW : ∀ y, |v y| ≤ W := by
    intro y
    exact abs_le.mpr ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩
  have hvw : ∀ y ∈ Icc a b, v y = w y := by
    intro y hy
    have hb : |w y| ≤ W := by
      rw [← Real.norm_eq_abs]
      exact (hD y hy).trans (le_max_left _ _)
    dsimp only [v]
    rw [min_eq_right (abs_le.mp hb).2, max_eq_right (abs_le.mp hb).1]
  have hlim := tendsto_receiver_compact_window_at_order hε hθ hΘ1 a b Z hZ
    hinside (show 1 ≤ M from le_max_left _ _) horders v W hv hvW
  have hsum : (∑ ρ ∈ Z, (if visibleTranslatedZetaOrder ε ρ = (M : ℕ∞)
      then receiverPoleAtomMass ε M ρ else 0) * v ρ.im) =
      ∑ ρ ∈ Z, (if visibleTranslatedZetaOrder ε ρ = (M : ℕ∞)
        then receiverPoleAtomMass ε M ρ else 0) * w ρ.im := by
    apply Finset.sum_congr rfl
    intro ρ hρ
    rw [hvw ρ.im ((hZ ρ).mp hρ).2.2]
  rw [hsum] at hlim
  refine hlim.congr' (Eventually.of_forall fun e => ?_)
  congr 1
  apply setIntegral_congr_fun measurableSet_Icc
  intro y hy
  change ‖lineSymbol (receiverLogProfile ε) (zetaZeroAbscissa - ε - 1 / 2 + e) y‖ ^ 2 * v y =
    ‖lineSymbol (receiverLogProfile ε) (zetaZeroAbscissa - ε - 1 / 2 + e) y‖ ^ 2 * w y
  rw [hvw y hy]

/-- The compact maximal-order law needs no zero-free strip assumption.
At abscissa one the boundary zero set is empty and the normalized mass is zero. -/
theorem exists_receiver_compact_maximal_order_law {ε : ℝ} (hε : 0 < ε)
    (hθ : 0 < zetaZeroAbscissa - ε - 1 / 2) (a b : ℝ)
    (hends : ∀ ρ : ℂ, riemannZeta ρ = 0 → ρ.re = zetaZeroAbscissa →
      ρ.im ≠ a ∧ ρ.im ≠ b) :
    ∃ Z : Finset ℂ,
      (∀ ρ : ℂ, ρ ∈ Z ↔ riemannZeta ρ = 0 ∧
        ρ.re = zetaZeroAbscissa ∧ ρ.im ∈ Icc a b) ∧
      let M := max 1 (Z.sup fun ρ =>
        analyticOrderNatAt riemannZeta ρ - analyticOrderNatAt riemannZeta (ρ - (ε : ℂ)))
      ∀ (w : ℝ → ℝ), Continuous w →
        Tendsto (fun e : ℝ => e ^ (2 * M - 1) * ∫ y in Icc a b,
          ‖lineSymbol (receiverLogProfile ε) (zetaZeroAbscissa - ε - 1 / 2 + e) y‖ ^ 2 * w y)
          (𝓝[>] 0) (𝓝 (∑ ρ ∈ Z,
            (if visibleTranslatedZetaOrder ε ρ = (M : ℕ∞)
              then receiverPoleAtomMass ε M ρ else 0) * w ρ.im)) := by
  classical
  by_cases hΘ1 : zetaZeroAbscissa < 1
  · exact exists_receiver_compact_maximal_order_law_of_abscissa_lt_one hε hθ hΘ1 a b hends
  have hΘ : zetaZeroAbscissa = 1 := le_antisymm zetaZeroAbscissa_le_one (le_of_not_gt hΘ1)
  refine ⟨∅, ?_, ?_⟩
  · intro ρ
    constructor
    · intro h
      exact False.elim (by simpa using h)
    · rintro ⟨hz, hre, _⟩
      exact False.elim ((riemannZeta_ne_zero_of_one_le_re
        (by simpa only [hre, hΘ] using (le_refl (1 : ℝ)))) hz)
  · change ∀ w : ℝ → ℝ, Continuous w →
      Tendsto (fun e : ℝ => e ^ (1 : ℕ) * ∫ y in Icc a b,
        ‖lineSymbol (receiverLogProfile ε) (zetaZeroAbscissa - ε - 1 / 2 + e) y‖ ^ 2 * w y)
        (𝓝[>] 0) (𝓝 0)
    intro w hw
    obtain ⟨η, hη, B, _, hb⟩ :=
      exists_receiver_lineSymbol_compact_bound_of_abscissa_one hε hθ hΘ a b
    obtain ⟨D, hD⟩ := (isCompact_Icc : IsCompact (Icc a b)).exists_bound_of_continuousOn
      hw.continuousOn
    apply tendsto_scaled_setIntegral_of_bounded Nat.zero_lt_one hη (C := B ^ 2 * D)
      isCompact_Icc.measure_lt_top
    intro e he y hy
    rw [norm_mul, norm_pow, norm_norm]
    exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) (hb e he y hy) 2)
      (hD y hy) (norm_nonneg _) (sq_nonneg B)

#print axioms exists_receiver_compact_maximal_order_law

end GaloisForLFunctions.ArithmeticCorrespondencePositivity
