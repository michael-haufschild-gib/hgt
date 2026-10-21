import GaloisForLFunctions.ArithmeticIncidencePositivity.OddPlateauFoldedWindowPositivity

/-!
# The even fold of a gauge jump energy

Let `M` be an even gauge, `0 ≤ M ≤ 1`, vanishing outside `(−B, B)`, and `u` an even Lipschitz profile.
A jump of length `t` joins the pair `(x, x + t)`. A crossing pair `(−a, b)`, `a, b > 0`, carries
`(u(a) − u(b))²`: the same squared jump as the same-side pair `(a, b)` of length `|a − b|`. For a
measurable density `κ` with `|κ(t)| ≤ C/t` on `(0, 2B]` the jump energy folds onto the positive
quadrant (`integral_kappa_mul_gaugeJumpProfile_eq_fold`):

    ∫_0^∞ κ(t) I(t) dt = 2 ∫_{x>0} [∫_{s>0} κ(s) J_s(x) ds + ∫_{s>0} κ(s + 2x) J_s(x) ds] dx,
    I(t) = ∫ M(x) M(x+t) (u(x) − u(x+t))² dx,   J_s(x) = M(x) M(x+s) (u(x) − u(x+s))².

The folded conductance `κ(s) + κ(s + 2x)` pairs each jump of length `s` with its reflection, of length
`s + 2x`, and only pairs with `x + s < B` carry mass. A density that is negative at long lags is
therefore harmless on even profiles wherever the folded conductance is nonnegative
(`integral_kappa_mul_gaugeJumpProfile_nonneg_of_fold`). For the Weil density `ω(t) − 2cosh(t/2)` the
binding pair is `(s, x) → (0, B)`, so the fold is cost free up to the plastic threshold `B = log ρ`,
twice the aperture of the unfolded density. Beyond it a lower bound `−G(x + s)` of the folded
conductance by a function of the outer point is paid by a potential
(`integral_kappa_mul_gaugeJumpProfile_ge_foldCost`).
-/

open MeasureTheory Set Filter Topology
open RHTower RHTower.CHMDPolar GaloisForLFunctions.ArithmeticIncidencePositivity

noncomputable section

namespace GaloisForLFunctions.ArithmeticCriticalityTheory

/-! ### Reflection of an even jump -/

theorem signedShiftJump_reflect_of_even {M u : ℝ → ℝ} (hMe : ∀ x, M (-x) = M x)
    (hue : ∀ x, u (-x) = u x) (t x : ℝ) :
    signedShiftJump M u t (-x - t) = signedShiftJump M u t x := by
  unfold signedShiftJump
  rw [show -x - t + t = -x by ring, show -x - t = -(x + t) by ring, hMe, hMe, hue, hue]
  ring

/-- The crossing jump `(−a, t − a)` of an even profile is the difference jump of `(a, t − a)`. -/
theorem signedShiftJump_neg_of_even {M u : ℝ → ℝ} (hMe : ∀ x, M (-x) = M x)
    (hue : ∀ x, u (-x) = u x) (t a : ℝ) :
    signedShiftJump M u t (-a) = crossingDiffJump M u t a := by
  unfold signedShiftJump crossingDiffJump
  rw [show -a + t = t - a by ring, hMe, hue]

/-- A measurable function on `(0, ∞)`, bounded by `A` and vanishing beyond `T`, is integrable. -/
theorem integrableOn_Ioi_of_bound {g : ℝ → ℝ} (hg : Measurable g) {A T : ℝ}
    (hb : ∀ s, 0 < s → |g s| ≤ A) (hz : ∀ s, T < s → g s = 0) : IntegrableOn g (Ioi 0) := by
  have h1 : IntegrableOn g (Ioc 0 T) :=
    Measure.integrableOn_of_bounded measure_Ioc_lt_top.ne hg.aestronglyMeasurable
      ((ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun s hs => by
        rw [Real.norm_eq_abs]; exact hb s hs.1))
  have h2 : IntegrableOn g (Ioi T) :=
    integrableOn_zero.congr_fun (fun s hs => (hz s hs).symm) measurableSet_Ioi
  refine (h1.union h2).mono_set fun s hs => ?_
  by_cases h : s ≤ T
  · exact Or.inl ⟨hs, h⟩
  · exact Or.inr (not_le.mp h)

/-- The folded crossing integrand `κ(t) 1_{0<x<t/2} D_t(x)` on `(0,∞)²`. -/
def foldedKappaCrossing (κ M u : ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  κ p.1 * ({q : ℝ × ℝ | 0 < q.2 ∧ q.2 < q.1 / 2}.indicator
    (fun q => crossingDiffJump M u q.1 q.2) p)

theorem foldedKappaCrossing_apply (κ M u : ℝ → ℝ) (t x : ℝ) :
    foldedKappaCrossing κ M u (t, x) = κ t *
      (Ioo (0 : ℝ) (t / 2)).indicator (fun y => crossingDiffJump M u t y) x := by
  unfold foldedKappaCrossing
  simp only [Set.indicator_apply, mem_setOf_eq, mem_Ioo]

/-- The folded crossing integrand at fixed `x > 0`, as a shift integral. -/
theorem integral_foldedKappaCrossing_eq {κ M u : ℝ → ℝ} {x : ℝ} (hx : 0 < x) :
    (∫ t in Ioi (0 : ℝ), foldedKappaCrossing κ M u (t, x)) =
      ∫ s in Ioi (0 : ℝ), κ (s + 2 * x) * signedShiftJump M u s x := by
  have h1 : (∫ t in Ioi (0 : ℝ), foldedKappaCrossing κ M u (t, x)) =
      ∫ t in Ioi (2 * x), κ t * crossingDiffJump M u t x := by
    rw [← integral_indicator measurableSet_Ioi, ← integral_indicator measurableSet_Ioi]
    congr 1
    funext t
    simp only [Set.indicator_apply, mem_Ioi, foldedKappaCrossing_apply, mem_Ioo]
    by_cases h : 2 * x < t
    · rw [if_pos (by linarith), if_pos ⟨hx, by linarith⟩, if_pos h]
    · rw [if_neg h]
      by_cases h' : 0 < t
      · rw [if_pos h', if_neg (fun hh => h (by linarith [hh.2])), mul_zero]
      · rw [if_neg h']
  rw [h1, setIntegral_Ioi_translate]
  refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
  rw [crossingDiffJump_add_two_mul]

section EvenFold

variable {M u κ : ℝ → ℝ} {B K C : ℝ} (hMc : Continuous M) (huc : Continuous u)
  (hMe : ∀ x, M (-x) = M x) (hue : ∀ x, u (-x) = u x) (hM0 : ∀ x, 0 ≤ M x)
  (hM1 : ∀ x, M x ≤ 1) (hMB : ∀ x, B ≤ |x| → M x = 0)
  (huL : ∀ a b, |u a - u b| ≤ K * |a - b|) (hB0 : 0 < B)
  (hκm : Measurable κ) (hC : 0 ≤ C) (hκ : ∀ t, 0 < t → t ≤ 2 * B → |κ t| ≤ C / t)

include hMc huc hMe hue hMB in
/-- **The per-shift split of an even jump**: twice the same-side profile plus the crossing
difference profile. -/
theorem integral_signedShiftJump_eq_split_of_even {t : ℝ} (ht : 0 < t) :
    (∫ x, signedShiftJump M u t x) =
      2 * (∫ x in Ioi (0 : ℝ), signedShiftJump M u t x) +
        ∫ x in Ioo (0 : ℝ) t, crossingDiffJump M u t x := by
  set g := fun x => signedShiftJump M u t x with hgdef
  have hg : Integrable g := integrable_signedShiftJump hMc huc hMB t
  have h1 : (∫ x, g x) = (∫ x in Ioi (0 : ℝ), g x) + ∫ x in Iic (0 : ℝ), g x := by
    rw [← integral_add_compl measurableSet_Ioi hg, compl_Ioi]
  have h2 : (∫ x in Iic (0 : ℝ), g x) =
      (∫ x in Iic (-t), g x) + ∫ x in Ioc (-t) 0, g x := by
    rw [← setIntegral_union (Iic_disjoint_Ioc le_rfl) measurableSet_Ioc hg.integrableOn
      hg.integrableOn, Iic_union_Ioc_eq_Iic (by linarith)]
  have h3 : (∫ x in Iic (-t), g x) = ∫ x in Ioi (0 : ℝ), g x := by
    have e3 := integral_comp_neg_Iic (-t) (fun y => g (y - t))
    simp only [neg_neg] at e3
    have e : (∫ x in Iic (-t), g x) = ∫ x in Iic (-t), g (-x - t) :=
      setIntegral_congr_fun measurableSet_Iic fun x _ => by
        simp only [hgdef]
        rw [signedShiftJump_reflect_of_even hMe hue]
    rw [e, e3, setIntegral_Ioi_translate]
    simp only [add_sub_cancel_right]
  have h4 : (∫ x in Ioc (-t) 0, g x) = ∫ x in Ioo (0 : ℝ) t, crossingDiffJump M u t x := by
    rw [← integral_indicator measurableSet_Ioc,
      ← integral_neg_eq_self (fun x => (Ioc (-t) 0).indicator g x)]
    have e : (fun x => (Ioc (-t) 0).indicator g (-x)) =
        (Ico (0 : ℝ) t).indicator fun x => crossingDiffJump M u t x := by
      funext x
      by_cases hx : x ∈ Ico (0 : ℝ) t
      · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (show -x ∈ Ioc (-t) 0 from
          ⟨by linarith [hx.2], by linarith [hx.1]⟩)]
        exact signedShiftJump_neg_of_even hMe hue t x
      · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (fun h => hx
          ⟨by linarith [h.2], by linarith [h.1]⟩)]
    rw [e, integral_indicator measurableSet_Ico, integral_Ico_eq_integral_Ioo]
  rw [h1, h2, h3, h4]
  ring

include hMB hB0 in
theorem signedShiftJump_eq_zero_of_le_add {s x : ℝ} (h : B ≤ x + s) :
    signedShiftJump M u s x = 0 := by
  unfold signedShiftJump
  rw [hMB (x + s) (by rw [abs_of_pos (by linarith)]; exact h), mul_zero, zero_mul]

include huL in
theorem lipschitz_const_nonneg : 0 ≤ K := by
  have h := huL 1 0
  rw [show |(1 : ℝ) - 0| = 1 by norm_num, mul_one] at h
  exact (abs_nonneg _).trans h

include hMc huc hM0 hM1 hMB huL hB0 hκm hC hκ in
theorem integrable_kappa_mul_signedShiftJump_prod :
    Integrable (Function.uncurry fun t x => κ t * signedShiftJump M u t x)
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) := by
  have hmeas : Measurable (Function.uncurry fun t x => κ t * signedShiftJump M u t x) := by
    refine (hκm.comp measurable_fst).mul ?_
    have : Continuous (Function.uncurry fun t x => signedShiftJump M u t x) := by
      unfold signedShiftJump; fun_prop
    exact this.measurable
  have hCK : 0 ≤ C * K ^ 2 := mul_nonneg hC (sq_nonneg K)
  refine integrable_quadrant_of_bound hmeas (C := C * K ^ 2 * (2 * B)) (T₁ := 2 * B) (T₂ := B)
    (fun t x ht hx => ?_) (fun t x ht hx h => ?_)
  · simp only [Function.uncurry_apply_pair]
    by_cases hts : t ≤ 2 * B
    · have hk := hκ t ht hts
      have hJ := signedShiftJump_le hM0 hM1 huL t x
      have hJ0 := signedShiftJump_nonneg' hM0 (F := u) t x
      rw [abs_mul, abs_of_nonneg hJ0]
      calc |κ t| * signedShiftJump M u t x ≤ C / t * (K ^ 2 * t ^ 2) :=
            mul_le_mul hk hJ hJ0 (div_nonneg hC ht.le)
        _ = C * K ^ 2 * t := by field_simp
        _ ≤ C * K ^ 2 * (2 * B) := mul_le_mul_of_nonneg_left hts hCK
    · rw [signedShiftJump_eq_zero_of_pos hMB hB0 hx (Or.inl (not_le.mp hts)), mul_zero, abs_zero]
      exact mul_nonneg hCK (by linarith)
  · simp only [Function.uncurry_apply_pair]
    rw [signedShiftJump_eq_zero_of_pos hMB hB0 hx h, mul_zero]

include hMc huc hM0 hM1 hMB huL hB0 hκm hC hκ in
theorem integrable_foldedKappaCrossing :
    Integrable (foldedKappaCrossing κ M u)
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) := by
  have hset : MeasurableSet {q : ℝ × ℝ | 0 < q.2 ∧ q.2 < q.1 / 2} := by
    rw [Set.setOf_and]
    exact (measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_lt measurable_snd (measurable_fst.div_const 2))
  have hc : Continuous fun q : ℝ × ℝ => crossingDiffJump M u q.1 q.2 := by
    unfold crossingDiffJump; fun_prop
  have hmeas : Measurable (foldedKappaCrossing κ M u) :=
    (hκm.comp measurable_fst).mul (hc.measurable.indicator hset)
  have hK : 0 ≤ K := lipschitz_const_nonneg huL
  have hCK : 0 ≤ C * K ^ 2 := mul_nonneg hC (sq_nonneg K)
  refine integrable_quadrant_of_bound hmeas (C := C * K ^ 2 * (2 * B)) (T₁ := 2 * B) (T₂ := B)
    (fun t x ht hx => ?_) (fun t x ht hx h => ?_)
  · rw [foldedKappaCrossing_apply]
    by_cases hxt : x ∈ Ioo (0 : ℝ) (t / 2)
    · rw [Set.indicator_of_mem hxt]
      have hD0 := crossingDiffJump_nonneg hM0 (F := u) t x
      by_cases hts : t ≤ 2 * B
      · have hk := hκ t ht hts
        have hD : crossingDiffJump M u t x ≤ K ^ 2 * t ^ 2 := by
          unfold crossingDiffJump
          have habs : |x - (t - x)| ≤ t := by
            rw [abs_le]; constructor <;> linarith [hxt.1, hxt.2]
          have h2 : |u x - u (t - x)| ≤ K * t :=
            (huL x (t - x)).trans (mul_le_mul_of_nonneg_left habs hK)
          have hsq : (u x - u (t - x)) ^ 2 ≤ K ^ 2 * t ^ 2 := by
            calc (u x - u (t - x)) ^ 2 = |u x - u (t - x)| ^ 2 := (sq_abs _).symm
              _ ≤ (K * t) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h2 2
              _ = K ^ 2 * t ^ 2 := by ring
          calc M x * M (t - x) * (u x - u (t - x)) ^ 2 ≤ 1 * (K ^ 2 * t ^ 2) :=
                mul_le_mul (mul_le_one₀ (hM1 _) (hM0 _) (hM1 _)) hsq (sq_nonneg _) zero_le_one
            _ = _ := one_mul _
        rw [abs_mul, abs_of_nonneg hD0]
        calc |κ t| * crossingDiffJump M u t x ≤ C / t * (K ^ 2 * t ^ 2) :=
              mul_le_mul hk hD hD0 (div_nonneg hC ht.le)
          _ = C * K ^ 2 * t := by field_simp
          _ ≤ C * K ^ 2 * (2 * B) := mul_le_mul_of_nonneg_left hts hCK
      · have hP : M (t - x) = 0 := hMB _ (by
          rw [abs_of_pos (by linarith [hxt.2])]; linarith [hxt.2, not_le.mp hts])
        unfold crossingDiffJump
        rw [hP, mul_zero, zero_mul, mul_zero, abs_zero]
        exact mul_nonneg hCK (by linarith)
    · rw [Set.indicator_of_notMem hxt, mul_zero, abs_zero]
      exact mul_nonneg hCK (by linarith)
  · rw [foldedKappaCrossing_apply]
    by_cases hxt : x ∈ Ioo (0 : ℝ) (t / 2)
    · rw [Set.indicator_of_mem hxt]
      unfold crossingDiffJump
      rcases h with h | h
      · rw [hMB (t - x) (by rw [abs_of_pos (by linarith [hxt.2])]; linarith [hxt.2]),
          mul_zero, zero_mul, mul_zero]
      · rw [hMB x (by rw [abs_of_pos hx]; linarith), zero_mul, zero_mul, mul_zero]
    · rw [Set.indicator_of_notMem hxt, mul_zero]

include hMc huc hM0 hM1 hMB huL hB0 hκm hC hκ in
/-- The crossing energy as a reflected shift integral:
`∫ κ(t) ∫_0^t D_t = 2 ∫_{x>0} ∫_{s>0} κ(s + 2x) J_s(x)`. -/
theorem kappaCrossingEnergy_eq :
    (∫ t in Ioi (0 : ℝ), κ t * ∫ x in Ioo (0 : ℝ) t, crossingDiffJump M u t x) =
      2 * ∫ x in Ioi (0 : ℝ), ∫ s in Ioi (0 : ℝ), κ (s + 2 * x) * signedShiftJump M u s x := by
  have hID := integrable_foldedKappaCrossing hMc huc hM0 hM1 hMB huL hB0 hκm hC hκ
  have h1 : (∫ x in Ioi (0 : ℝ), ∫ s in Ioi (0 : ℝ), κ (s + 2 * x) * signedShiftJump M u s x) =
      ∫ x in Ioi (0 : ℝ), ∫ t in Ioi (0 : ℝ), foldedKappaCrossing κ M u (t, x) :=
    setIntegral_congr_fun measurableSet_Ioi fun x hx =>
      (integral_foldedKappaCrossing_eq (mem_Ioi.mp hx)).symm
  rw [h1, ← integral_integral_swap (f := fun t x => foldedKappaCrossing κ M u (t, x)) hID,
    ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  rw [integral_crossingDiffJump_eq_two_mul_half hMc huc (mem_Ioi.mp ht)]
  have : (∫ x in Ioi (0 : ℝ), foldedKappaCrossing κ M u (t, x)) =
      κ t * ∫ x in Ioo (0 : ℝ) (t / 2), crossingDiffJump M u t x := by
    simp_rw [foldedKappaCrossing_apply]
    rw [integral_const_mul, setIntegral_indicator measurableSet_Ioo,
      Set.inter_eq_right.mpr Ioo_subset_Ioi_self]
  rw [this]
  ring

include hMc huc hM0 hM1 hMB huL hB0 hκm hC hκ in
/-- The same-side energy: `∫ κ(t) ∫_{x>0} J_t(x) = ∫_{x>0} ∫_{s>0} κ(s) J_s(x)`. -/
theorem kappaSameEnergy_eq :
    (∫ t in Ioi (0 : ℝ), κ t * ∫ x in Ioi (0 : ℝ), signedShiftJump M u t x) =
      ∫ x in Ioi (0 : ℝ), ∫ s in Ioi (0 : ℝ), κ s * signedShiftJump M u s x := by
  have hIS := integrable_kappa_mul_signedShiftJump_prod hMc huc hM0 hM1 hMB huL hB0 hκm hC hκ
  rw [← integral_integral_swap (f := fun t x => κ t * signedShiftJump M u t x) hIS]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  rw [integral_const_mul]

include hMc huc hMe hue hM0 hM1 hMB huL hB0 hκm hC hκ in
/-- **The even fold of the jump energy.** -/
theorem integral_kappa_mul_gaugeJumpProfile_eq_fold :
    (∫ t in Ioi (0 : ℝ), κ t * gaugeJumpProfile M u t) =
      2 * ((∫ x in Ioi (0 : ℝ), ∫ s in Ioi (0 : ℝ), κ s * signedShiftJump M u s x) +
        ∫ x in Ioi (0 : ℝ), ∫ s in Ioi (0 : ℝ), κ (s + 2 * x) * signedShiftJump M u s x) := by
  have hIS := integrable_kappa_mul_signedShiftJump_prod hMc huc hM0 hM1 hMB huL hB0 hκm hC hκ
  have hS : IntegrableOn (fun t => κ t * ∫ x in Ioi (0 : ℝ), signedShiftJump M u t x) (Ioi 0) :=
    hIS.integral_prod_left.congr (Eventually.of_forall fun t => by
      simp only [Function.uncurry_apply_pair]
      rw [integral_const_mul])
  have hID := integrable_foldedKappaCrossing hMc huc hM0 hM1 hMB huL hB0 hκm hC hκ
  have hD : IntegrableOn (fun t => κ t * ∫ x in Ioo (0 : ℝ) t, crossingDiffJump M u t x)
      (Ioi 0) := by
    have h2 : IntegrableOn (fun t => 2 * ∫ x in Ioi (0 : ℝ), foldedKappaCrossing κ M u (t, x))
        (Ioi 0) := hID.integral_prod_left.const_mul 2
    refine h2.congr_fun (fun t ht => ?_) measurableSet_Ioi
    have ht0 : 0 < t := ht
    simp only
    simp_rw [foldedKappaCrossing_apply]
    rw [integral_const_mul, setIntegral_indicator measurableSet_Ioo,
      Set.inter_eq_right.mpr Ioo_subset_Ioi_self,
      integral_crossingDiffJump_eq_two_mul_half hMc huc ht0]
    ring
  have hsplit : ∀ t ∈ Ioi (0 : ℝ), κ t * gaugeJumpProfile M u t =
      2 * (κ t * ∫ x in Ioi (0 : ℝ), signedShiftJump M u t x) +
        κ t * ∫ x in Ioo (0 : ℝ) t, crossingDiffJump M u t x := fun t ht => by
    unfold gaugeJumpProfile
    rw [integral_signedShiftJump_eq_split_of_even hMc huc hMe hue hMB ht]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi hsplit,
    integral_add (f := fun t => 2 * (κ t * ∫ x in Ioi (0 : ℝ), signedShiftJump M u t x))
      (g := fun t => κ t * ∫ x in Ioo (0 : ℝ) t, crossingDiffJump M u t x) (hS.const_mul 2) hD,
    integral_const_mul, kappaSameEnergy_eq hMc huc hM0 hM1 hMB huL hB0 hκm hC hκ,
    kappaCrossingEnergy_eq hMc huc hM0 hM1 hMB huL hB0 hκm hC hκ]
  ring

include hMc huc hM0 hM1 hMB huL hB0 hκm hC hκ in
/-- The section `s ↦ κ(s) J_s(x)` is integrable on `(0, ∞)`. -/
theorem integrableOn_kappa_mul_signedShiftJump_section {x : ℝ} (hx0 : 0 < x) :
    IntegrableOn (fun s => κ s * signedShiftJump M u s x) (Ioi 0) := by
  have hK : 0 ≤ K := lipschitz_const_nonneg huL
  have hCK : 0 ≤ C * K ^ 2 := mul_nonneg hC (sq_nonneg K)
  have hJc : Continuous fun s => signedShiftJump M u s x := by unfold signedShiftJump; fun_prop
  refine integrableOn_Ioi_of_bound (hκm.mul hJc.measurable) (A := C * K ^ 2 * (2 * B))
    (T := 2 * B) (fun s hs => ?_) (fun s hs => ?_)
  · by_cases hsB : s ≤ 2 * B
    · have hJ0 := signedShiftJump_nonneg' hM0 (F := u) s x
      rw [abs_mul, abs_of_nonneg hJ0]
      calc |κ s| * signedShiftJump M u s x ≤ C / s * (K ^ 2 * s ^ 2) :=
            mul_le_mul (hκ s hs hsB) (signedShiftJump_le hM0 hM1 huL s x) hJ0
              (div_nonneg hC hs.le)
        _ = C * K ^ 2 * s := by field_simp
        _ ≤ C * K ^ 2 * (2 * B) := mul_le_mul_of_nonneg_left hsB hCK
    · rw [signedShiftJump_eq_zero_of_pos hMB hB0 hx0 (Or.inl (not_le.mp hsB)), mul_zero,
        abs_zero]
      exact mul_nonneg hCK (by linarith)
  · rw [signedShiftJump_eq_zero_of_pos hMB hB0 hx0 (Or.inl hs), mul_zero]

include hMc huc hM0 hM1 hMB huL hB0 hκm hC hκ in
/-- The reflected section `s ↦ κ(s + 2x) J_s(x)` is integrable on `(0, ∞)`. -/
theorem integrableOn_kappa_reflect_mul_signedShiftJump_section {x : ℝ} (hx0 : 0 < x) :
    IntegrableOn (fun s => κ (s + 2 * x) * signedShiftJump M u s x) (Ioi 0) := by
  have hK : 0 ≤ K := lipschitz_const_nonneg huL
  have hCK : 0 ≤ C * K ^ 2 := mul_nonneg hC (sq_nonneg K)
  have hJc : Continuous fun s => signedShiftJump M u s x := by unfold signedShiftJump; fun_prop
  refine integrableOn_Ioi_of_bound ((hκm.comp (measurable_id.add_const _)).mul hJc.measurable)
    (A := C * K ^ 2 * B) (T := B) (fun s hs => ?_) (fun s hs => ?_)
  · by_cases hxs : x + s < B
    · have hJ0 := signedShiftJump_nonneg' hM0 (F := u) s x
      have hk := hκ (s + 2 * x) (by linarith) (by linarith)
      have hk' : C / (s + 2 * x) ≤ C / s := div_le_div_of_nonneg_left hC hs (by linarith)
      rw [abs_mul, abs_of_nonneg hJ0]
      calc |κ (s + 2 * x)| * signedShiftJump M u s x ≤ C / s * (K ^ 2 * s ^ 2) :=
            mul_le_mul (hk.trans hk') (signedShiftJump_le hM0 hM1 huL s x) hJ0
              (div_nonneg hC hs.le)
        _ = C * K ^ 2 * s := by field_simp
        _ ≤ C * K ^ 2 * B := mul_le_mul_of_nonneg_left (by linarith) hCK
    · rw [signedShiftJump_eq_zero_of_le_add hMB hB0 (not_lt.mp hxs), mul_zero, abs_zero]
      exact mul_nonneg hCK hB0.le
  · rw [signedShiftJump_eq_zero_of_le_add hMB hB0 (by linarith), mul_zero]

include hMc huc hMe hue hM0 hM1 hMB huL hB0 hκm hC hκ in
/-- The folded energy as one integral over the positive quadrant:
`∫ κ I = 2 ∫_{x>0} ∫_{s>0} (κ(s) + κ(s + 2x)) J_s(x)`. -/
theorem integral_kappa_mul_gaugeJumpProfile_eq_fold_sum :
    (∫ t in Ioi (0 : ℝ), κ t * gaugeJumpProfile M u t) =
      2 * ∫ x in Ioi (0 : ℝ), ∫ s in Ioi (0 : ℝ),
        (κ s + κ (s + 2 * x)) * signedShiftJump M u s x := by
  rw [integral_kappa_mul_gaugeJumpProfile_eq_fold hMc huc hMe hue hM0 hM1 hMB huL hB0 hκm hC hκ]
  have hIS := integrable_kappa_mul_signedShiftJump_prod hMc huc hM0 hM1 hMB huL hB0 hκm hC hκ
  have hID := integrable_foldedKappaCrossing hMc huc hM0 hM1 hMB huL hB0 hκm hC hκ
  have hA : IntegrableOn (fun x => ∫ s in Ioi (0 : ℝ), κ s * signedShiftJump M u s x) (Ioi 0) :=
    hIS.integral_prod_right
  have hCr : IntegrableOn (fun x => ∫ s in Ioi (0 : ℝ), κ (s + 2 * x) * signedShiftJump M u s x)
      (Ioi 0) :=
    IntegrableOn.congr_fun hID.integral_prod_right
      (fun x hx => integral_foldedKappaCrossing_eq (mem_Ioi.mp hx)) measurableSet_Ioi
  rw [← integral_add hA hCr]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
  have hx0 : 0 < x := hx
  rw [← integral_add (integrableOn_kappa_mul_signedShiftJump_section hMc huc hM0 hM1 hMB huL hB0
      hκm hC hκ hx0)
    (integrableOn_kappa_reflect_mul_signedShiftJump_section hMc huc hM0 hM1 hMB huL hB0 hκm hC hκ
      hx0)]
  refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
  ring

include hMc huc hMe hue hM0 hM1 hMB huL hB0 hκm hC hκ in
/-- **Positivity from a nonnegative folded conductance.** If `κ(s) + κ(s + 2x) ≥ 0` whenever
`s, x > 0` and `x + s < B`, then `∫_0^∞ κ(t) I(t) dt ≥ 0` for every even profile. -/
theorem integral_kappa_mul_gaugeJumpProfile_nonneg_of_fold
    (hfold : ∀ s x, 0 < s → 0 < x → x + s < B → 0 ≤ κ s + κ (s + 2 * x)) :
    0 ≤ ∫ t in Ioi (0 : ℝ), κ t * gaugeJumpProfile M u t := by
  rw [integral_kappa_mul_gaugeJumpProfile_eq_fold_sum hMc huc hMe hue hM0 hM1 hMB huL hB0 hκm hC hκ]
  refine mul_nonneg zero_le_two (setIntegral_nonneg measurableSet_Ioi fun x hx => ?_)
  have hx0 : 0 < x := hx
  refine setIntegral_nonneg measurableSet_Ioi fun s hs => ?_
  have hs0 : 0 < s := hs
  by_cases hxs : x + s < B
  · exact mul_nonneg (hfold s x hs0 hx0 hxs) (signedShiftJump_nonneg' hM0 s x)
  · rw [signedShiftJump_eq_zero_of_le_add hMB hB0 (not_lt.mp hxs), mul_zero]

end EvenFold

/-- **The fold with a cost.** If the folded conductance of an even gauge is bounded below by
`−G(x + s)`, a function of the outer point with `0 ≤ G ≤ G₁`, then
`∫ κ I ≥ −4 (∫_{y>0} G M) ∫_{x>0} u² M − 4B ∫_{y>0} G M u²`: the negative part costs a constant
potential plus the potential `2B G` attached to the outer point. -/
theorem integral_kappa_mul_gaugeJumpProfile_ge_foldCost {M u κ : ℝ → ℝ} {B K C : ℝ}
    (hMc : Continuous M) (huc : Continuous u)
    (hMe : ∀ x, M (-x) = M x) (hue : ∀ x, u (-x) = u x) (hM0 : ∀ x, 0 ≤ M x)
    (hM1 : ∀ x, M x ≤ 1) (hMB : ∀ x, B ≤ |x| → M x = 0)
    (huL : ∀ a b, |u a - u b| ≤ K * |a - b|) (hB0 : 0 < B)
    (hκm : Measurable κ) (hC : 0 ≤ C) (hκ : ∀ t, 0 < t → t ≤ 2 * B → |κ t| ≤ C / t)
    {G : ℝ → ℝ} (hGm : Measurable G) {G₁ : ℝ} (hG0 : ∀ y, 0 ≤ G y) (hG1 : ∀ y, G y ≤ G₁)
    (hfold : ∀ s x, 0 < s → 0 < x → x + s < B → -G (x + s) ≤ κ s + κ (s + 2 * x)) :
    -4 * (∫ y in Ioi (0 : ℝ), G y * M y) * (∫ x in Ioi (0 : ℝ), u x ^ 2 * M x) -
        4 * B * ∫ y in Ioi (0 : ℝ), G y * M y * u y ^ 2 ≤
      ∫ t in Ioi (0 : ℝ), κ t * gaugeJumpProfile M u t := by
  rw [integral_kappa_mul_gaugeJumpProfile_eq_fold_sum hMc huc hMe hue hM0 hM1 hMB huL hB0 hκm hC hκ]
  have hG10 : 0 ≤ G₁ := (hG0 0).trans (hG1 0)
  have hMB' : ∀ y, B ≤ y → M y = 0 := fun y hy => hMB y (by rw [abs_of_pos (by linarith)]; exact hy)
  have hMcs : HasCompactSupport M :=
    HasCompactSupport.intro (isCompact_Icc (a := -B) (b := B)) fun y hy =>
      hMB y (not_le.mp fun h => hy (abs_le.mp h)).le
  have hGMi : Integrable fun y => G y * M y := by
    have h := (hMc.integrable_of_hasCompactSupport (μ := volume) hMcs).bdd_mul (c := G₁)
      hGm.aestronglyMeasurable
      (ae_of_all _ fun y => by rw [Real.norm_eq_abs, abs_of_nonneg (hG0 y)]; exact hG1 y)
    exact h
  have hu2M : Integrable fun x => u x ^ 2 * M x :=
    ((huc.pow 2).mul hMc).integrable_of_hasCompactSupport hMcs.mul_left
  have hGMu : Integrable fun y => G y * M y * u y ^ 2 := by
    have h := hu2M.bdd_mul (c := G₁) hGm.aestronglyMeasurable
      (ae_of_all _ fun y => by rw [Real.norm_eq_abs, abs_of_nonneg (hG0 y)]; exact hG1 y)
    exact h.congr (ae_of_all _ fun y => by ring)
  set Γ := ∫ y in Ioi (0 : ℝ), G y * M y with hΓdef
  set Γ₂ := ∫ y in Ioi (0 : ℝ), G y * M y * u y ^ 2 with hΓ₂def
  have hΓ0 : 0 ≤ Γ := setIntegral_nonneg measurableSet_Ioi fun y _ => mul_nonneg (hG0 y) (hM0 y)
  have hΓ₂0 : 0 ≤ Γ₂ := setIntegral_nonneg measurableSet_Ioi fun y _ =>
    mul_nonneg (mul_nonneg (hG0 y) (hM0 y)) (sq_nonneg _)
  -- the inner integrals are integrable in the outer point
  have hIS := integrable_kappa_mul_signedShiftJump_prod hMc huc hM0 hM1 hMB huL hB0 hκm hC hκ
  have hID := integrable_foldedKappaCrossing hMc huc hM0 hM1 hMB huL hB0 hκm hC hκ
  have hA : IntegrableOn (fun x => ∫ s in Ioi (0 : ℝ), κ s * signedShiftJump M u s x) (Ioi 0) :=
    hIS.integral_prod_right
  have hCr : IntegrableOn (fun x => ∫ s in Ioi (0 : ℝ), κ (s + 2 * x) * signedShiftJump M u s x)
      (Ioi 0) :=
    IntegrableOn.congr_fun hID.integral_prod_right
      (fun x hx => integral_foldedKappaCrossing_eq (mem_Ioi.mp hx)) measurableSet_Ioi
  have hsum : IntegrableOn (fun x => ∫ s in Ioi (0 : ℝ),
      (κ s + κ (s + 2 * x)) * signedShiftJump M u s x) (Ioi 0) := by
    refine IntegrableOn.congr_fun (hA.add hCr) (fun x hx => ?_) measurableSet_Ioi
    have hx0 : 0 < x := hx
    simp only [Pi.add_apply]
    rw [← integral_add (integrableOn_kappa_mul_signedShiftJump_section hMc huc hM0 hM1 hMB huL
        hB0 hκm hC hκ hx0)
      (integrableOn_kappa_reflect_mul_signedShiftJump_section hMc huc hM0 hM1 hMB huL hB0 hκm hC
        hκ hx0)]
    refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
    ring
  -- translation into the outer point
  have htr : ∀ (h : ℝ → ℝ), Integrable h → (∀ y, 0 ≤ h y) → ∀ x, 0 < x →
      IntegrableOn (fun s => h (x + s)) (Ioi 0) ∧
        (∫ s in Ioi (0 : ℝ), h (x + s)) ≤ ∫ y in Ioi (0 : ℝ), h y := by
    intro h hh h0 x hx
    have hc' : Integrable fun s => h (x + s) := hh.comp_add_left x
    refine ⟨hc'.integrableOn, ?_⟩
    have e : (∫ s in Ioi (0 : ℝ), h (x + s)) = ∫ y in Ioi x, h y := by
      rw [setIntegral_Ioi_translate h x]
      refine setIntegral_congr_fun measurableSet_Ioi fun s _ => by rw [add_comm]
    rw [e]
    exact setIntegral_mono_set hh.integrableOn (ae_of_all _ fun y => h0 y)
      (Eventually.of_forall fun y hy => lt_trans hx hy)
  -- the pointwise lower bound of the inner integral
  have hpt : ∀ x ∈ Ioi (0 : ℝ), -2 * Γ * (u x ^ 2 * M x) - 2 * Γ₂ * (Ioc 0 B).indicator 1 x ≤
      ∫ s in Ioi (0 : ℝ), (κ s + κ (s + 2 * x)) * signedShiftJump M u s x := by
    intro x hx
    have hx0 : 0 < x := hx
    by_cases hxB : x < B
    · obtain ⟨i1, b1⟩ := htr (fun y => G y * M y) hGMi (fun y => mul_nonneg (hG0 y) (hM0 y)) x hx0
      obtain ⟨i2, b2⟩ := htr (fun y => G y * M y * u y ^ 2) hGMu
        (fun y => mul_nonneg (mul_nonneg (hG0 y) (hM0 y)) (sq_nonneg _)) x hx0
      have hinner : IntegrableOn (fun s => (κ s + κ (s + 2 * x)) * signedShiftJump M u s x)
          (Ioi 0) := by
        refine IntegrableOn.congr_fun ((integrableOn_kappa_mul_signedShiftJump_section hMc huc hM0
          hM1 hMB huL hB0 hκm hC hκ hx0).add (integrableOn_kappa_reflect_mul_signedShiftJump_section
          hMc huc hM0 hM1 hMB huL hB0 hκm hC hκ hx0)) (fun s _ => ?_) measurableSet_Ioi
        simp only [Pi.add_apply]; ring
      have hcomb : IntegrableOn (fun s => -2 * (u x ^ 2 * M x) * (G (x + s) * M (x + s)) -
          2 * (G (x + s) * M (x + s) * u (x + s) ^ 2)) (Ioi 0) :=
        (i1.const_mul _).sub (i2.const_mul 2)
      have hmono := setIntegral_mono_on hcomb hinner measurableSet_Ioi fun s hs => by
        have hs0 : (0 : ℝ) < s := hs
        have hJ0 := signedShiftJump_nonneg' hM0 (F := u) s x
        by_cases hxs : x + s < B
        · have hk := hfold s x hs0 hx0 hxs
          have hJ : signedShiftJump M u s x ≤ 2 * M x * M (x + s) * u x ^ 2 +
              2 * M (x + s) * u (x + s) ^ 2 := by
            unfold signedShiftJump
            have h1 := hM0 x
            have h2 := hM0 (x + s)
            have h3 := hM1 x
            have hsq : (u x - u (x + s)) ^ 2 ≤ 2 * u x ^ 2 + 2 * u (x + s) ^ 2 := by
              nlinarith [sq_nonneg (u x + u (x + s))]
            have hMM := mul_nonneg h1 h2
            calc M x * M (x + s) * (u x - u (x + s)) ^ 2 ≤
                M x * M (x + s) * (2 * u x ^ 2 + 2 * u (x + s) ^ 2) :=
                  mul_le_mul_of_nonneg_left hsq hMM
              _ = 2 * M x * M (x + s) * u x ^ 2 + 2 * (M x * (M (x + s) * u (x + s) ^ 2)) := by
                  ring
              _ ≤ 2 * M x * M (x + s) * u x ^ 2 + 2 * (1 * (M (x + s) * u (x + s) ^ 2)) := by
                  have := mul_le_mul_of_nonneg_right h3 (mul_nonneg h2 (sq_nonneg (u (x + s))))
                  linarith
              _ = _ := by ring
          have hG := hG0 (x + s)
          have e1 := mul_le_mul_of_nonneg_left hJ hG
          have e2 := mul_le_mul_of_nonneg_right hk hJ0
          nlinarith [e1, e2]
        · have hz := signedShiftJump_eq_zero_of_le_add hMB hB0 (u := u) (not_lt.mp hxs)
          have hMxs : M (x + s) = 0 := hMB' _ (not_lt.mp hxs)
          rw [hz, hMxs]
          simp
      have eL : (∫ s in Ioi (0 : ℝ), (-2 * (u x ^ 2 * M x) * (G (x + s) * M (x + s)) -
          2 * (G (x + s) * M (x + s) * u (x + s) ^ 2))) =
          -2 * (u x ^ 2 * M x) * (∫ s in Ioi (0 : ℝ), G (x + s) * M (x + s)) -
            2 * ∫ s in Ioi (0 : ℝ), G (x + s) * M (x + s) * u (x + s) ^ 2 := by
        rw [integral_sub (i1.const_mul _) (i2.const_mul 2), integral_const_mul, integral_const_mul]
      rw [eL] at hmono
      have hind : (Ioc 0 B).indicator (1 : ℝ → ℝ) x = 1 :=
        Set.indicator_of_mem (show x ∈ Ioc 0 B from ⟨hx0, hxB.le⟩) _
      rw [hind, mul_one]
      have hu2 : 0 ≤ u x ^ 2 * M x := mul_nonneg (sq_nonneg _) (hM0 x)
      have k1 := mul_le_mul_of_nonneg_left b1 hu2
      nlinarith [k1, b2, hmono]
    · have hMx : M x = 0 := hMB x (by rw [abs_of_pos hx0]; exact not_lt.mp hxB)
      have h0 : (∫ s in Ioi (0 : ℝ), (κ s + κ (s + 2 * x)) * signedShiftJump M u s x) = 0 := by
        refine integral_eq_zero_of_ae (Eventually.of_forall fun s => ?_)
        simp only [Pi.zero_apply, signedShiftJump, hMx, zero_mul, mul_zero]
      rw [h0, hMx, mul_zero, mul_zero]
      have : 0 ≤ (Ioc 0 B).indicator (1 : ℝ → ℝ) x := Set.indicator_nonneg (fun _ _ => zero_le_one) x
      nlinarith
  -- integrate over the outer point
  have hind : IntegrableOn (fun x => (Ioc 0 B).indicator (1 : ℝ → ℝ) x) (Ioi 0) :=
    ((integrable_indicator_iff measurableSet_Ioc).mpr (integrableOn_const (by simp))).integrableOn
  have hL : IntegrableOn (fun x => -2 * Γ * (u x ^ 2 * M x) -
      2 * Γ₂ * (Ioc 0 B).indicator 1 x) (Ioi 0) :=
    (hu2M.integrableOn.const_mul _).sub (hind.const_mul _)
  have hmono := setIntegral_mono_on hL hsum measurableSet_Ioi hpt
  have eL : (∫ x in Ioi (0 : ℝ), (-2 * Γ * (u x ^ 2 * M x) - 2 * Γ₂ * (Ioc 0 B).indicator 1 x)) =
      -2 * Γ * (∫ x in Ioi (0 : ℝ), u x ^ 2 * M x) - 2 * Γ₂ * B := by
    rw [integral_sub (hu2M.integrableOn.const_mul _) (hind.const_mul _), integral_const_mul,
      integral_const_mul]
    have hB1 : (∫ x in Ioi (0 : ℝ), (Ioc 0 B).indicator (1 : ℝ → ℝ) x) = B := by
      rw [setIntegral_indicator measurableSet_Ioc, Set.inter_eq_right.mpr Ioc_subset_Ioi_self]
      simp [Real.volume_real_Ioc, hB0.le]
    rw [hB1]
  rw [eL] at hmono
  linarith

end GaloisForLFunctions.ArithmeticCriticalityTheory
