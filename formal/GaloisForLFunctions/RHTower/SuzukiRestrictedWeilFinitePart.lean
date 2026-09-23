import GaloisForLFunctions.RHTower.SuzukiRestrictedWeilSourceForm
import GaloisForLFunctions.RHTower.SuzukiHlogCompactEmbedding
import Mathlib.Analysis.Calculus.DSlope

/-!
# Suzuki's finite-part Weil block

This module proves Suzuki's equation (2.3) directly on the literal smooth compactly supported
aperture core. The Hadamard finite part splits into a nonnegative fractional difference energy
and the exact logarithmic potential. Consequently the source finite-part block is semibounded by
an explicit multiple of interval `L²` energy. All public endpoints bundle aperture positivity and
core regularity/support; none has an analytic hypothesis.
-/

open MeasureTheory Set intervalIntegral

noncomputable section

namespace GaloisForLFunctions.RHTower

private theorem finitePart_integral_congr_of_Ioo {a b : ℝ} (hab : a ≤ b) {f g : ℝ → ℝ}
    (h : ∀ t ∈ Ioo a b, f t = g t) : (∫ t in a..b, f t) = ∫ t in a..b, g t := by
  refine intervalIntegral.integral_congr_ae ?_
  have h1 : ({b}ᶜ : Set ℝ) ∈ ae (volume : Measure ℝ) :=
    MeasureTheory.compl_mem_ae_iff.mpr (measure_singleton b)
  filter_upwards [h1] with t ht hmem
  rw [Set.uIoc_of_le hab] at hmem
  exact h t ⟨hmem.1, lt_of_le_of_ne hmem.2 (by simpa using ht)⟩

private theorem finitePart_intervalIntegrable_of_bound_on {f : ℝ → ℝ} (hf : Measurable f)
    {C a b : ℝ} (hab : a ≤ b) (hb : ∀ t ∈ Icc a b, |f t| ≤ C) :
    IntervalIntegrable f volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
  refine MeasureTheory.Measure.integrableOn_of_bounded (M := |C|) (by simp)
    hf.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  rw [Real.norm_eq_abs]
  exact (hb t (Ioc_subset_Icc_self ht)).trans (le_abs_self C)

private theorem finitePart_prefix_eq_indicator {a b u : ℝ} (hab : a ≤ b)
    (hu : u ∈ Icc a b) {f : ℝ → ℝ} (hf : Measurable f) {C : ℝ}
    (hb : ∀ t ∈ Icc a b, |f t| ≤ C) :
    (∫ t in a..u, f t) = ∫ t in a..b, (if t ≤ u then f t else 0) := by
  have hind : Measurable fun t : ℝ => if t ≤ u then f t else 0 :=
    Measurable.ite (measurableSet_le measurable_id measurable_const) hf measurable_const
  have hindb : ∀ t ∈ Icc a b, |if t ≤ u then f t else 0| ≤ |C| := by
    intro t ht
    split_ifs
    · exact (hb t ht).trans (le_abs_self C)
    · simp
  have hleft := finitePart_intervalIntegrable_of_bound_on hind hu.1
    (fun t ht => hindb t ⟨ht.1, ht.2.trans hu.2⟩)
  have hright := finitePart_intervalIntegrable_of_bound_on hind hu.2
    (fun t ht => hindb t ⟨hu.1.trans ht.1, ht.2⟩)
  have hadj := intervalIntegral.integral_add_adjacent_intervals hleft hright
  have h1 : (∫ t in a..u, (if t ≤ u then f t else 0)) = ∫ t in a..u, f t := by
    refine finitePart_integral_congr_of_Ioo hu.1 fun t ht => ?_
    rw [if_pos ht.2.le]
  have h2 : (∫ t in u..b, (if t ≤ u then f t else 0)) = 0 := by
    rw [show (∫ t in u..b, (if t ≤ u then f t else 0)) =
        ∫ _t in u..b, (0 : ℝ) by
      refine finitePart_integral_congr_of_Ioo hu.2 fun t ht => ?_
      rw [if_neg (by linarith [ht.1])], intervalIntegral.integral_zero]
  rw [h1, h2, add_zero] at hadj
  exact hadj

private theorem finitePart_suffix_eq_indicator {a b u : ℝ} (hab : a ≤ b)
    (hu : u ∈ Icc a b) {f : ℝ → ℝ} (hf : Measurable f) {C : ℝ}
    (hb : ∀ t ∈ Icc a b, |f t| ≤ C) :
    (∫ t in u..b, f t) = ∫ t in a..b, (if u ≤ t then f t else 0) := by
  have hind : Measurable fun t : ℝ => if u ≤ t then f t else 0 :=
    Measurable.ite (measurableSet_le measurable_const measurable_id) hf measurable_const
  have hindb : ∀ t ∈ Icc a b, |if u ≤ t then f t else 0| ≤ |C| := by
    intro t ht
    split_ifs
    · exact (hb t ht).trans (le_abs_self C)
    · simp
  have hleft := finitePart_intervalIntegrable_of_bound_on hind hu.1
    (fun t ht => hindb t ⟨ht.1, ht.2.trans hu.2⟩)
  have hright := finitePart_intervalIntegrable_of_bound_on hind hu.2
    (fun t ht => hindb t ⟨hu.1.trans ht.1, ht.2⟩)
  have hadj := intervalIntegral.integral_add_adjacent_intervals hleft hright
  have h1 : (∫ t in a..u, (if u ≤ t then f t else 0)) = 0 := by
    rw [show (∫ t in a..u, (if u ≤ t then f t else 0)) =
        ∫ _t in a..u, (0 : ℝ) by
      refine finitePart_integral_congr_of_Ioo hu.1 fun t ht => ?_
      rw [if_neg (by linarith [ht.2])], intervalIntegral.integral_zero]
  have h2 : (∫ t in u..b, (if u ≤ t then f t else 0)) = ∫ t in u..b, f t := by
    refine finitePart_integral_congr_of_Ioo hu.2 fun t ht => ?_
    rw [if_pos ht.1.le]
  rw [h1, h2, zero_add] at hadj
  exact hadj

private theorem finitePart_integrableOn_prod_of_bound {a b : ℝ} {F : ℝ → ℝ → ℝ}
    (hF : Measurable (Function.uncurry F)) {C : ℝ}
    (hC : ∀ x ∈ uIoc a b, ∀ y ∈ uIoc a b, |F x y| ≤ C) :
    IntegrableOn (Function.uncurry F) (uIoc a b ×ˢ uIoc a b) volume := by
  have hfinite : volume (uIoc a b ×ˢ uIoc a b) ≠ ⊤ :=
    (lt_of_le_of_lt
      (measure_mono (Set.prod_mono uIoc_subset_uIcc uIoc_subset_uIcc))
      (isCompact_uIcc.prod isCompact_uIcc).measure_lt_top).ne
  refine MeasureTheory.Measure.integrableOn_of_bounded (M := C) hfinite hF.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem (measurableSet_uIoc.prod measurableSet_uIoc)] with p hp
  rw [Real.norm_eq_abs]
  exact hC p.1 hp.1 p.2 hp.2

private theorem finitePart_intervalIntegrable_iterated_of_integrableOn {a b : ℝ}
    (hab : a ≤ b) {F : ℝ → ℝ → ℝ}
    (hF : IntegrableOn (Function.uncurry F) (uIoc a b ×ˢ uIoc a b) volume) :
    IntervalIntegrable (fun x => ∫ y in a..b, F x y) volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab, IntegrableOn]
  have hp : Integrable (Function.uncurry F)
      ((volume.restrict (Ioc a b)).prod (volume.restrict (Ioc a b))) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod, ← IntegrableOn]
    simpa [uIoc_of_le hab] using hF
  have hout := hp.integral_prod_left
  simpa [intervalIntegral.integral_of_le hab] using hout

private theorem finitePart_exists_lipschitz_bound {a : ℝ} {u : ℝ → ℝ}
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ x ∈ Icc (-a) a, ∀ y ∈ Icc (-a) a,
      |u y - u x| ≤ D * |y - x| := by
  have hud : Continuous (deriv u) := (contDiff_infty_iff_deriv.mp hu).2.continuous
  obtain ⟨D, hD⟩ := isCompact_Icc.exists_bound_of_continuousOn hud.continuousOn
  refine ⟨max D 0, le_max_right _ _, ?_⟩
  intro x hx y hy
  have hD' : ∀ z ∈ Icc (-a) a, ‖deriv u z‖ ≤ max D 0 :=
    fun z hz => (hD z hz).trans (le_max_left _ _)
  have hmv := Convex.norm_image_sub_le_of_norm_deriv_le
    (fun z _ => (hu.differentiable (by simp)).differentiableAt) hD'
      (convex_Icc (-a) a) hx hy
  simpa [Real.norm_eq_abs] using hmv

private theorem finitePart_left_quotient_bound {a D : ℝ} {u : ℝ → ℝ}
    (hD0 : 0 ≤ D)
    (hlip : ∀ x ∈ Icc (-a) a, ∀ y ∈ Icc (-a) a,
      |u y - u x| ≤ D * |y - x|) :
    ∀ x ∈ Icc (-a) a, ∀ y ∈ Icc (-a) a,
      |(u y - u x) * (x - y)⁻¹| ≤ D := by
  intro x hx y hy
  rcases eq_or_ne x y with rfl | hxy
  · simpa using hD0
  · have hpos : 0 < |x - y| := abs_pos.mpr (sub_ne_zero.mpr hxy)
    have h := hlip x hx y hy
    rw [abs_sub_comm y x] at h
    rw [abs_mul, abs_inv]
    calc
      |u y - u x| * |x - y|⁻¹ ≤ (D * |x - y|) * |x - y|⁻¹ :=
        mul_le_mul_of_nonneg_right h (inv_nonneg.mpr hpos.le)
      _ = D := by field_simp

private theorem finitePart_right_quotient_bound {a D : ℝ} {u : ℝ → ℝ}
    (hD0 : 0 ≤ D)
    (hlip : ∀ x ∈ Icc (-a) a, ∀ y ∈ Icc (-a) a,
      |u y - u x| ≤ D * |y - x|) :
    ∀ x ∈ Icc (-a) a, ∀ y ∈ Icc (-a) a,
      |(u y - u x) * (y - x)⁻¹| ≤ D := by
  intro x hx y hy
  rcases eq_or_ne x y with rfl | hxy
  · simpa using hD0
  · have hpos : 0 < |y - x| := abs_pos.mpr (sub_ne_zero.mpr hxy.symm)
    have h := hlip x hx y hy
    rw [abs_mul, abs_inv]
    calc
      |u y - u x| * |y - x|⁻¹ ≤ (D * |y - x|) * |y - x|⁻¹ :=
        mul_le_mul_of_nonneg_right h (inv_nonneg.mpr hpos.le)
      _ = D := by field_simp

theorem suzukiFinitePartDividedDifference_symmetrization {a : ℝ} (ha : 0 < a) {u : ℝ → ℝ}
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) :
    IntervalIntegrable (fun x =>
      ((∫ y in (-a)..x, (u y - u x) * (x - y)⁻¹) +
        ∫ y in x..a, (u y - u x) * (y - x)⁻¹) * u x) volume (-a) a ∧
      (∫ x in (-a)..a,
        ((∫ y in (-a)..x, (u y - u x) * (x - y)⁻¹) +
          ∫ y in x..a, (u y - u x) * (y - x)⁻¹) * u x) =
        -(1 / 2) * ∫ x in (-a)..a, ∫ y in (-a)..a,
          (u x - u y) ^ (2 : ℕ) * |x - y|⁻¹ ∧
      (∀ x ∈ Icc (-a) a, IntervalIntegrable
        (fun y => (u x - u y) ^ (2 : ℕ) * |x - y|⁻¹) volume (-a) a) ∧
      IntervalIntegrable (fun x => ∫ y in (-a)..a,
        (u x - u y) ^ (2 : ℕ) * |x - y|⁻¹) volume (-a) a := by
  have hab : -a ≤ a := by linarith
  have huc : Continuous u := hu.continuous
  obtain ⟨D, hD0, hlip⟩ := finitePart_exists_lipschitz_bound (a := a) hu
  have hqLbound := finitePart_left_quotient_bound hD0 hlip
  have hqRbound := finitePart_right_quotient_bound hD0 hlip
  have hcompact : IsCompact (Icc (-a) a) := isCompact_Icc
  obtain ⟨U0, hU0⟩ := hcompact.exists_bound_of_continuousOn huc.continuousOn
  let U : ℝ := max U0 0
  have hU0' : 0 ≤ U := le_max_right _ _
  have hU : ∀ x ∈ Icc (-a) a, |u x| ≤ U := by
    intro x hx
    have hxU0 : |u x| ≤ U0 := by simpa [Real.norm_eq_abs] using hU0 x hx
    exact hxU0.trans (le_max_left _ _)
  let qL : ℝ → ℝ → ℝ := fun x y => (u y - u x) * (x - y)⁻¹
  let qR : ℝ → ℝ → ℝ := fun x y => (u y - u x) * (y - x)⁻¹
  let energy : ℝ → ℝ → ℝ := fun x y => (u x - u y) ^ (2 : ℕ) * |x - y|⁻¹
  let K : ℝ → ℝ → ℝ := fun x y => if y ≤ x then qL x y * u x else 0
  let L : ℝ → ℝ → ℝ := fun x y => if x ≤ y then qR x y * u x else 0
  let T : ℝ → ℝ → ℝ := fun x y => if y ≤ x then energy x y else 0
  have hqLmeas : Measurable (Function.uncurry qL) := by
    exact ((huc.measurable.comp measurable_snd).sub
      (huc.measurable.comp measurable_fst)).mul
      ((measurable_fst.sub measurable_snd).inv)
  have hqRmeas : Measurable (Function.uncurry qR) := by
    exact ((huc.measurable.comp measurable_snd).sub
      (huc.measurable.comp measurable_fst)).mul
      ((measurable_snd.sub measurable_fst).inv)
  have henergyMeas : Measurable (Function.uncurry energy) := by
    exact (((huc.measurable.comp measurable_fst).sub
      (huc.measurable.comp measurable_snd)).pow_const 2).mul
      (((measurable_fst.sub measurable_snd).abs).inv)
  have hKmeas : Measurable (Function.uncurry K) := by
    exact Measurable.ite (measurableSet_le measurable_snd measurable_fst)
      (hqLmeas.mul (huc.measurable.comp measurable_fst)) measurable_const
  have hLmeas : Measurable (Function.uncurry L) := by
    exact Measurable.ite (measurableSet_le measurable_fst measurable_snd)
      (hqRmeas.mul (huc.measurable.comp measurable_fst)) measurable_const
  have hTmeas : Measurable (Function.uncurry T) := by
    exact Measurable.ite (measurableSet_le measurable_snd measurable_fst)
      henergyMeas measurable_const
  have hKbound : ∀ x ∈ Icc (-a) a, ∀ y ∈ Icc (-a) a, |K x y| ≤ D * U := by
    intro x hx y hy
    dsimp [K]
    split_ifs
    · rw [abs_mul]
      exact mul_le_mul (by simpa [qL] using hqLbound x hx y hy) (hU x hx)
        (abs_nonneg _) hD0
    · simpa using mul_nonneg hD0 hU0'
  have hLbound : ∀ x ∈ Icc (-a) a, ∀ y ∈ Icc (-a) a, |L x y| ≤ D * U := by
    intro x hx y hy
    dsimp [L]
    split_ifs
    · rw [abs_mul]
      exact mul_le_mul (by simpa [qR] using hqRbound x hx y hy) (hU x hx)
        (abs_nonneg _) hD0
    · simpa using mul_nonneg hD0 hU0'
  have henergyBound : ∀ x ∈ Icc (-a) a, ∀ y ∈ Icc (-a) a,
      |energy x y| ≤ (2 * U) * D := by
    intro x hx y hy
    rcases eq_or_ne x y with rfl | hxy
    · simp [energy]
      exact mul_nonneg (by linarith) hD0
    · have hden : 0 < |x - y| := abs_pos.mpr (sub_ne_zero.mpr hxy)
      have hratio : |u x - u y| * |x - y|⁻¹ ≤ D := by
        have hq := hqLbound x hx y hy
        simpa [qL, abs_mul, abs_inv, abs_sub_comm] using hq
      have hdiff : |u x - u y| ≤ 2 * U := by
        calc
          |u x - u y| ≤ |u x| + |u y| := abs_sub _ _
          _ ≤ 2 * U := by linarith [hU x hx, hU y hy]
      have hnonneg : 0 ≤ energy x y := by
        exact mul_nonneg (sq_nonneg _) (inv_nonneg.mpr (abs_nonneg _))
      rw [abs_of_nonneg hnonneg]
      dsimp [energy]
      calc
        (u x - u y) ^ (2 : ℕ) * |x - y|⁻¹ =
            |u x - u y| * (|u x - u y| * |x - y|⁻¹) := by
              rw [← sq_abs]
              ring
        _ ≤ |u x - u y| * D :=
          mul_le_mul_of_nonneg_left hratio (abs_nonneg _)
        _ ≤ (2 * U) * D := mul_le_mul_of_nonneg_right hdiff hD0
  have hTbound : ∀ x ∈ Icc (-a) a, ∀ y ∈ Icc (-a) a,
      |T x y| ≤ (2 * U) * D := by
    intro x hx y hy
    dsimp [T]
    split_ifs
    · exact henergyBound x hx y hy
    · simpa using mul_nonneg (by linarith : 0 ≤ 2 * U) hD0
  have huIoc : uIoc (-a) a = Ioc (-a) a := uIoc_of_le hab
  have hmemO : ∀ x ∈ uIoc (-a) a, x ∈ Icc (-a) a := by
    intro x hx
    rw [huIoc] at hx
    exact Ioc_subset_Icc_self hx
  have hmemC : ∀ x ∈ uIcc (-a) a, x ∈ Icc (-a) a := by
    simpa [uIcc_of_le hab]
  have hKint : IntegrableOn (Function.uncurry K)
      (uIoc (-a) a ×ˢ uIoc (-a) a) volume :=
    finitePart_integrableOn_prod_of_bound hKmeas
      (fun x hx y hy => hKbound x (hmemO x hx) y (hmemO y hy))
  have hLint : IntegrableOn (Function.uncurry L)
      (uIoc (-a) a ×ˢ uIoc (-a) a) volume :=
    finitePart_integrableOn_prod_of_bound hLmeas
      (fun x hx y hy => hLbound x (hmemO x hx) y (hmemO y hy))
  have hTint : IntegrableOn (Function.uncurry T)
      (uIoc (-a) a ×ˢ uIoc (-a) a) volume :=
    finitePart_integrableOn_prod_of_bound hTmeas
      (fun x hx y hy => hTbound x (hmemO x hx) y (hmemO y hy))
  have henergyInt : IntegrableOn (Function.uncurry energy)
      (uIoc (-a) a ×ˢ uIoc (-a) a) volume :=
    finitePart_integrableOn_prod_of_bound henergyMeas
      (fun x hx y hy => henergyBound x (hmemO x hx) y (hmemO y hy))
  let LS : ℝ → ℝ → ℝ := fun x y => L y x
  have hLSmeas : Measurable (Function.uncurry LS) := by
    exact hLmeas.comp (measurable_snd.prodMk measurable_fst)
  have hLSbound : ∀ x ∈ Icc (-a) a, ∀ y ∈ Icc (-a) a, |LS x y| ≤ D * U := by
    intro x hx y hy
    exact hLbound y hy x hx
  have hLSint : IntegrableOn (Function.uncurry LS)
      (uIoc (-a) a ×ˢ uIoc (-a) a) volume :=
    finitePart_integrableOn_prod_of_bound hLSmeas
      (fun x hx y hy => hLSbound x (hmemO x hx) y (hmemO y hy))
  have hKouter : IntervalIntegrable (fun x => ∫ y in (-a)..a, K x y) volume (-a) a :=
    finitePart_intervalIntegrable_iterated_of_integrableOn hab hKint
  have hLouter : IntervalIntegrable (fun x => ∫ y in (-a)..a, L x y) volume (-a) a :=
    finitePart_intervalIntegrable_iterated_of_integrableOn hab hLint
  have hLSouter : IntervalIntegrable (fun x => ∫ y in (-a)..a, LS x y) volume (-a) a :=
    finitePart_intervalIntegrable_iterated_of_integrableOn hab hLSint
  have hTouter : IntervalIntegrable (fun x => ∫ y in (-a)..a, T x y) volume (-a) a :=
    finitePart_intervalIntegrable_iterated_of_integrableOn hab hTint
  have henergyOuter : IntervalIntegrable
      (fun x => ∫ y in (-a)..a, energy x y) volume (-a) a :=
    finitePart_intervalIntegrable_iterated_of_integrableOn hab henergyInt
  have henergySlices : ∀ x ∈ Icc (-a) a,
      IntervalIntegrable (energy x) volume (-a) a := by
    intro x hx
    exact finitePart_intervalIntegrable_of_bound_on
      (henergyMeas.comp (measurable_const.prodMk measurable_id)) hab
      (fun y hy => henergyBound x hx y hy)
  have hprefix : ∀ x ∈ Icc (-a) a,
      (∫ y in (-a)..x, qL x y) * u x = ∫ y in (-a)..a, K x y := by
    intro x hx
    have hmeas : Measurable (qL x) := by
      exact hqLmeas.comp (measurable_const.prodMk measurable_id)
    have hp := finitePart_prefix_eq_indicator hab hx hmeas
      (fun y hy => by simpa [qL] using hqLbound x hx y hy)
    rw [hp, ← intervalIntegral.integral_mul_const]
    refine intervalIntegral.integral_congr fun y _ => ?_
    simp only [K]
    split_ifs <;> simp
  have hsuffix : ∀ x ∈ Icc (-a) a,
      (∫ y in x..a, qR x y) * u x = ∫ y in (-a)..a, L x y := by
    intro x hx
    have hmeas : Measurable (qR x) := by
      exact hqRmeas.comp (measurable_const.prodMk measurable_id)
    have hp := finitePart_suffix_eq_indicator hab hx hmeas
      (fun y hy => by simpa [qR] using hqRbound x hx y hy)
    rw [hp, ← intervalIntegral.integral_mul_const]
    refine intervalIntegral.integral_congr fun y _ => ?_
    simp only [L]
    split_ifs <;> simp
  have horiginal :
      (∫ x in (-a)..a,
        ((∫ y in (-a)..x, (u y - u x) * (x - y)⁻¹) +
          ∫ y in x..a, (u y - u x) * (y - x)⁻¹) * u x) =
        ∫ x in (-a)..a,
          ((∫ y in (-a)..a, K x y) + ∫ y in (-a)..a, L x y) := by
    refine intervalIntegral.integral_congr fun x hx => ?_
    have hxI := hmemC x hx
    change ((∫ y in (-a)..x, qL x y) + ∫ y in x..a, qR x y) * u x = _
    rw [add_mul, hprefix x hxI, hsuffix x hxI]
  have hdivInt : IntervalIntegrable (fun x =>
      ((∫ y in (-a)..x, (u y - u x) * (x - y)⁻¹) +
        ∫ y in x..a, (u y - u x) * (y - x)⁻¹) * u x) volume (-a) a := by
    refine IntervalIntegrable.congr (f := fun x =>
      (∫ y in (-a)..a, K x y) + ∫ y in (-a)..a, L x y) ?_
      (hKouter.add hLouter)
    intro x hx
    have hxI := hmemO x hx
    change (∫ y in (-a)..a, K x y) + (∫ y in (-a)..a, L x y) =
      ((∫ y in (-a)..x, qL x y) + ∫ y in x..a, qR x y) * u x
    rw [add_mul, hprefix x hxI, hsuffix x hxI]
  refine ⟨hdivInt, ?_, henergySlices, henergyOuter⟩
  rw [horiginal, intervalIntegral.integral_add hKouter hLouter]
  have hswapL :
      (∫ x in (-a)..a, ∫ y in (-a)..a, L x y) =
        ∫ x in (-a)..a, ∫ y in (-a)..a, LS x y := by
    have hs := intervalIntegral_intervalIntegral_swap hLint
    simpa [LS] using hs
  rw [hswapL]
  have hpoint : ∀ x y : ℝ, K x y + LS x y = -T x y := by
    intro x y
    by_cases h : y ≤ x
    · simp only [K, LS, L, T, if_pos h]
      dsimp [qL, qR, energy]
      rw [abs_of_nonneg (sub_nonneg.mpr h)]
      ring
    · simp [K, LS, L, T, h]
  have hsum :
      (∫ x in (-a)..a, ∫ y in (-a)..a, K x y) +
          (∫ x in (-a)..a, ∫ y in (-a)..a, LS x y) =
        -(∫ x in (-a)..a, ∫ y in (-a)..a, T x y) := by
    rw [← intervalIntegral.integral_add hKouter hLSouter]
    rw [← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr fun x hx => ?_
    have hxI := hmemC x hx
    have hKslice : IntervalIntegrable (K x) volume (-a) a :=
      finitePart_intervalIntegrable_of_bound_on
        (hKmeas.comp (measurable_const.prodMk measurable_id)) hab
        (fun y hy => hKbound x hxI y hy)
    have hLSslice : IntervalIntegrable (LS x) volume (-a) a :=
      finitePart_intervalIntegrable_of_bound_on
        (hLSmeas.comp (measurable_const.prodMk measurable_id)) hab
        (fun y hy => hLSbound x hxI y hy)
    rw [← intervalIntegral.integral_add hKslice hLSslice,
      ← intervalIntegral.integral_neg]
    exact intervalIntegral.integral_congr fun y _ => hpoint x y
  rw [hsum]
  let TS : ℝ → ℝ → ℝ := fun x y => T y x
  have hTSmeas : Measurable (Function.uncurry TS) := by
    exact hTmeas.comp (measurable_snd.prodMk measurable_fst)
  have hTSbound : ∀ x ∈ Icc (-a) a, ∀ y ∈ Icc (-a) a,
      |TS x y| ≤ (2 * U) * D := by
    intro x hx y hy
    exact hTbound y hy x hx
  have hTSint : IntegrableOn (Function.uncurry TS)
      (uIoc (-a) a ×ˢ uIoc (-a) a) volume :=
    finitePart_integrableOn_prod_of_bound hTSmeas
      (fun x hx y hy => hTSbound x (hmemO x hx) y (hmemO y hy))
  have hTSouter : IntervalIntegrable (fun x => ∫ y in (-a)..a, TS x y) volume (-a) a :=
    finitePart_intervalIntegrable_iterated_of_integrableOn hab hTSint
  have henergySymm : ∀ x y : ℝ, energy y x = energy x y := by
    intro x y
    dsimp [energy]
    rw [abs_sub_comm x y]
    ring
  have hpointEnergy : ∀ x y : ℝ, T x y + TS x y = energy x y := by
    intro x y
    rcases lt_trichotomy y x with hyx | rfl | hxy
    · simp [T, TS, hyx.le, not_le.mpr hyx]
    · simp [T, TS, energy]
    · simp [T, TS, hxy.le, not_le.mpr hxy, henergySymm]
  have hswapT :
      (∫ x in (-a)..a, ∫ y in (-a)..a, T x y) =
        ∫ x in (-a)..a, ∫ y in (-a)..a, TS x y := by
    have hs := intervalIntegral_intervalIntegral_swap hTint
    simpa [TS] using hs
  have hfull :
      (∫ x in (-a)..a, ∫ y in (-a)..a, energy x y) =
        2 * (∫ x in (-a)..a, ∫ y in (-a)..a, T x y) := by
    calc
      (∫ x in (-a)..a, ∫ y in (-a)..a, energy x y) =
          ∫ x in (-a)..a, ∫ y in (-a)..a, (T x y + TS x y) := by
            refine intervalIntegral.integral_congr fun x _ => ?_
            exact intervalIntegral.integral_congr fun y _ => (hpointEnergy x y).symm
      _ = ∫ x in (-a)..a,
          ((∫ y in (-a)..a, T x y) + ∫ y in (-a)..a, TS x y) := by
            refine intervalIntegral.integral_congr fun x hx => ?_
            have hxI := hmemC x hx
            have hTslice : IntervalIntegrable (T x) volume (-a) a :=
              finitePart_intervalIntegrable_of_bound_on
                (hTmeas.comp (measurable_const.prodMk measurable_id)) hab
                (fun y hy => hTbound x hxI y hy)
            have hTSslice : IntervalIntegrable (TS x) volume (-a) a :=
              finitePart_intervalIntegrable_of_bound_on
                (hTSmeas.comp (measurable_const.prodMk measurable_id)) hab
                (fun y hy => hTSbound x hxI y hy)
            rw [intervalIntegral.integral_add hTslice hTSslice]
      _ = (∫ x in (-a)..a, ∫ y in (-a)..a, T x y) +
          (∫ x in (-a)..a, ∫ y in (-a)..a, TS x y) := by
            rw [intervalIntegral.integral_add hTouter hTSouter]
      _ = 2 * (∫ x in (-a)..a, ∫ y in (-a)..a, T x y) := by
            rw [← hswapT]
            ring
  rw [hfull]
  ring

theorem suzukiFinitePartDifferenceEnergy_intervalIntegrable {a : ℝ} (ha : 0 < a)
    {u : ℝ → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u) :
    (∀ x ∈ Icc (-a) a, IntervalIntegrable
      (fun y => (u x - u y) ^ (2 : ℕ) * |x - y|⁻¹) volume (-a) a) ∧
    IntervalIntegrable (fun x => ∫ y in (-a)..a,
      (u x - u y) ^ (2 : ℕ) * |x - y|⁻¹) volume (-a) a := by
  have h := suzukiFinitePartDividedDifference_symmetrization ha hu
  exact h.2.2

theorem suzukiFinitePartLogPotential_integrable_upper {a r : ℝ} (ha : 0 < a)
    (hr : 0 ≤ r) (hra : r < a) {u : ℝ → ℝ} (hu : Continuous u)
    (hsupp : Function.support u ⊆ Icc (-r) r) :
    IntervalIntegrable (fun x => Real.log (a ^ (2 : ℕ) - x ^ (2 : ℕ)) * u x ^ (2 : ℕ))
        volume (-a) a ∧
      (∫ x in (-a)..a, Real.log (a ^ (2 : ℕ) - x ^ (2 : ℕ)) * u x ^ (2 : ℕ)) ≤
        max (Real.log (a ^ (2 : ℕ))) 0 * ∫ x in (-a)..a, u x ^ (2 : ℕ) := by
  have hab : -a ≤ a := by linarith
  have hargpos : ∀ x ∈ Icc (-r) r, 0 < a ^ (2 : ℕ) - x ^ (2 : ℕ) := by
    intro x hx
    have habsx : |x| ≤ r := (abs_le).2 hx
    have hx2 : x ^ (2 : ℕ) ≤ r ^ (2 : ℕ) := by
      have := (sq_le_sq₀ (abs_nonneg x) hr).2 habsx
      simpa using this
    have hr2 : r ^ (2 : ℕ) < a ^ (2 : ℕ) := (sq_lt_sq₀ hr ha.le).2 hra
    linarith
  have hargcont : Continuous fun x : ℝ => a ^ (2 : ℕ) - x ^ (2 : ℕ) :=
    continuous_const.sub (continuous_id.pow 2)
  have hlogcont : ContinuousOn (fun x => Real.log (a ^ (2 : ℕ) - x ^ (2 : ℕ))) (Icc (-r) r) :=
    hargcont.continuousOn.log (fun x hx => (hargpos x hx).ne')
  have hcompactr : IsCompact (Icc (-r) r) := isCompact_Icc
  obtain ⟨L0, hL0⟩ := hcompactr.exists_bound_of_continuousOn hlogcont
  let L : ℝ := max L0 0
  have hLnonneg : 0 ≤ L := le_max_right _ _
  have hL : ∀ x ∈ Icc (-r) r, |Real.log (a ^ (2 : ℕ) - x ^ (2 : ℕ))| ≤ L := by
    intro x hx
    have hxL0 : |Real.log (a ^ (2 : ℕ) - x ^ (2 : ℕ))| ≤ L0 := by
      simpa [Real.norm_eq_abs] using hL0 x hx
    exact hxL0.trans (le_max_left _ _)
  have hcompacta : IsCompact (Icc (-a) a) := isCompact_Icc
  obtain ⟨U0, hU0⟩ := hcompacta.exists_bound_of_continuousOn hu.continuousOn
  let U : ℝ := max U0 0
  have hUnonneg : 0 ≤ U := le_max_right _ _
  have hU : ∀ x ∈ Icc (-a) a, |u x| ≤ U := by
    intro x hx
    have hxU0 : |u x| ≤ U0 := by simpa [Real.norm_eq_abs] using hU0 x hx
    exact hxU0.trans (le_max_left _ _)
  have hmeas : Measurable (fun x => Real.log (a ^ (2 : ℕ) - x ^ (2 : ℕ)) * u x ^ (2 : ℕ)) :=
    (Real.measurable_log.comp
      ((measurable_const.pow_const 2).sub (measurable_id.pow_const 2))).mul
      (hu.measurable.pow_const 2)
  have hbound : ∀ x ∈ Icc (-a) a,
      |Real.log (a ^ (2 : ℕ) - x ^ (2 : ℕ)) * u x ^ (2 : ℕ)| ≤ L * U ^ (2 : ℕ) := by
    intro x hx
    by_cases hux : u x = 0
    · simpa [hux] using mul_nonneg hLnonneg (sq_nonneg U)
    · have hxr : x ∈ Icc (-r) r := hsupp hux
      have hu2 : |u x| ^ (2 : ℕ) ≤ U ^ (2 : ℕ) :=
        (sq_le_sq₀ (abs_nonneg (u x)) hUnonneg).2 (hU x hx)
      rw [abs_mul, abs_pow]
      exact mul_le_mul (hL x hxr) hu2 (sq_nonneg _) hLnonneg
  have hint := finitePart_intervalIntegrable_of_bound_on hmeas hab hbound
  refine ⟨hint, ?_⟩
  have hpoint : ∀ x ∈ Icc (-a) a,
      Real.log (a ^ (2 : ℕ) - x ^ (2 : ℕ)) * u x ^ (2 : ℕ) ≤
        max (Real.log (a ^ (2 : ℕ))) 0 * u x ^ (2 : ℕ) := by
    intro x hx
    by_cases hux : u x = 0
    · simp [hux]
    · have hxr : x ∈ Icc (-r) r := hsupp hux
      have hpos := hargpos x hxr
      have hargle : a ^ (2 : ℕ) - x ^ (2 : ℕ) ≤ a ^ (2 : ℕ) := by nlinarith [sq_nonneg x]
      have hlogle : Real.log (a ^ (2 : ℕ) - x ^ (2 : ℕ)) ≤ max (Real.log (a ^ (2 : ℕ))) 0 :=
        (Real.log_le_log hpos hargle).trans (le_max_left _ _)
      exact mul_le_mul_of_nonneg_right hlogle (sq_nonneg _)
  have hmono := intervalIntegral.integral_mono_on hab hint
    ((continuous_const.mul (hu.pow 2)).intervalIntegrable (-a) a) hpoint
  change (∫ x in (-a)..a, Real.log (a ^ (2 : ℕ) - x ^ (2 : ℕ)) * u x ^ (2 : ℕ)) ≤
    ∫ x in (-a)..a, max (Real.log (a ^ (2 : ℕ))) 0 * u x ^ (2 : ℕ) at hmono
  rw [intervalIntegral.integral_const_mul] at hmono
  exact hmono

def suzukiFinitePartDifferenceEnergy (a : ℝ) (u : ℝ → ℝ) : ℝ :=
  ∫ x in (-a)..a, ∫ y in (-a)..a, (u x - u y) ^ (2 : ℕ) * |x - y|⁻¹

def suzukiFinitePartLogPotential (a : ℝ) (u : ℝ → ℝ) : ℝ :=
  ∫ x in (-a)..a, Real.log (a ^ (2 : ℕ) - x ^ (2 : ℕ)) * u x ^ (2 : ℕ)

def suzukiFinitePartEnergy (a : ℝ) (u : ℝ → ℝ) : ℝ :=
  (1 / 4) * suzukiFinitePartDifferenceEnergy a u - (1 / 2) * suzukiFinitePartLogPotential a u

theorem suzukiFinitePartDifferenceEnergy_nonneg
    (a : RHTower.SuzukiPositiveAperture) (u : SuzukiRestrictedWeilCore a.1) :
    0 ≤ suzukiFinitePartDifferenceEnergy a.1 u := by
  unfold suzukiFinitePartDifferenceEnergy
  apply intervalIntegral.integral_nonneg (by linarith [a.property])
  intro x _
  apply intervalIntegral.integral_nonneg (by linarith [a.property])
  intro y _
  exact mul_nonneg (sq_nonneg _) (inv_nonneg.mpr (abs_nonneg _))

theorem suzukiWeilFinitePartBlock_eq_energy
    (a : RHTower.SuzukiPositiveAperture) (u : SuzukiRestrictedWeilCore a.1) :
    weilFinitePartBlock a.1 u u = suzukiFinitePartEnergy a.1 u := by
  have hsymm := suzukiFinitePartDividedDifference_symmetrization a.property u.smooth
  have hlog := suzukiFinitePartLogPotential_integrable_upper a.property
    u.supportRadius_nonneg u.supportRadius_lt_aperture u.continuous u.support_subset
  have hsplit :
      (∫ x in (-a.1)..a.1, cauchyFinitePart a.1 x u * u x) =
        (∫ x in (-a.1)..a.1,
          ((∫ y in (-a.1)..x, (u y - u x) * (x - y)⁻¹) +
            ∫ y in x..a.1, (u y - u x) * (y - x)⁻¹) * u x) +
        suzukiFinitePartLogPotential a.1 u := by
    unfold suzukiFinitePartLogPotential
    rw [← intervalIntegral.integral_add hsymm.1 hlog.1]
    refine intervalIntegral.integral_congr fun x _ => ?_
    unfold cauchyFinitePart
    ring
  rw [weilFinitePartBlock, hsplit, hsymm.2.1]
  unfold suzukiFinitePartEnergy suzukiFinitePartDifferenceEnergy
  ring

theorem suzukiWeilFinitePartBlock_lowerBound
    (a : RHTower.SuzukiPositiveAperture) (u : SuzukiRestrictedWeilCore a.1) :
    -(1 / 2 * max (Real.log (a.1 ^ (2 : ℕ))) 0 *
        ∫ x in (-a.1)..a.1, u x ^ (2 : ℕ)) ≤ weilFinitePartBlock a.1 u u := by
  have hlog := suzukiFinitePartLogPotential_integrable_upper a.property
    u.supportRadius_nonneg u.supportRadius_lt_aperture u.continuous u.support_subset
  have henergy := suzukiFinitePartDifferenceEnergy_nonneg a u
  have hlogUpper : suzukiFinitePartLogPotential a.1 u ≤
      max (Real.log (a.1 ^ (2 : ℕ))) 0 * ∫ x in (-a.1)..a.1, u x ^ (2 : ℕ) := by
    simpa [suzukiFinitePartLogPotential] using hlog.2
  rw [suzukiWeilFinitePartBlock_eq_energy]
  unfold suzukiFinitePartEnergy
  nlinarith

end GaloisForLFunctions.RHTower
