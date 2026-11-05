import GaloisForLFunctions.RHTower.WeilConeUniquenessUnconditional
import GaloisForLFunctions.RHTower.WeilPositivityFiniteLevelExistenceDecidesRH
import GaloisForLFunctions.ArithmeticIncidencePositivity.AnExplicitLargerApertureRetainsAWeilFloor
import GaloisForLFunctions.ArithmeticCriticalityTheory.OddFormCriticality

/-!
# The arithmetic Hardy interval

Write Weil's functional with prime weights `t·Λ` as `H − tP`: `H` is the archimedean–polar part
(weights `0`) and `P(k) = Σ_{n ≥ 2} Λ(n)n^{−1/2}(k(log n) + k(−log n))` the arithmetic part
(`weilFullFunctional_scaledWeights`). On the window `[−c, c]` the **arithmetic Hardy interval** is

  `ℋ(c) = {t : H − tP ≥ 0 on every test supported in [−c, c]}`,

the set of multiples of the arithmetic part that are Hardy terms for the archimedean logarithmic jump
operator with the pole kept. It answers review §2.7 Q1 in exact form:

* `ℋ(c)` is a closed interval, antitone in `c` (`convex_hardyInterval`, `isClosed_hardyInterval`,
  `hardyInterval_anti`).
* Before the first prime it is the whole line: `ℋ(c) = ℝ` for `2c < log 2`
  (`hardyInterval_eq_univ`); from the first entry on it is bounded, `ℋ(c) ⊆ [L, U]` for
  `2c > log 2` (`hardyInterval_bounded`), by two bumps at distance `log 2` of either parity.
* **Scaling optimality, unconditionally**: a multiple admissible on every window is `1`
  (`eq_one_of_forall_mem_hardyInterval`), by uniqueness of the Weil cone.
* **Criticality, unconditionally**: Weil's form admits no Hardy weight on odd tests
  (`not_exists_hardyWeight`), by ACT's null sequences.
* Hence the arithmetic part is an optimal Hardy term iff RH (`isOptimalHardyTerm_iff_RH`), and
  all optimality conditions except admissibility hold unconditionally.
-/

open MeasureTheory Set Filter Topology Complex
open scoped Real

noncomputable section

namespace GaloisForLFunctions.FrustratedArithmeticDirichletForms

open _root_.RHTower _root_.Zeta23

/-! ### The arithmetic part of Weil's functional -/

/-- The prime weight `Λ(n)n^{−1/2}` on `n ≥ 2`. -/
def primeWeight (n : ℕ) : ℝ :=
  if 2 ≤ n then (ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n else 0

/-- The arithmetic part `P(k) = Σ_n Λ(n)n^{−1/2}(k(log n) + k(−log n))`. -/
def primePart (k : ℝ → ℂ) : ℂ :=
  ∑' n : ℕ, (primeWeight n : ℂ) * (k (Real.log n) + k (-Real.log n))

/-- The scaled weights `t·Λ`. -/
def scaledWeights (t : ℝ) : ℕ → ℝ := fun n => t * (ArithmeticFunction.vonMangoldt n : ℝ)

/-- Weil's functional with weights `t·Λ` is `H − tP`. -/
theorem weilFullFunctional_scaledWeights (t : ℝ) (k : ℝ → ℂ) :
    weilFullFunctional (scaledWeights t) k =
      weilFullFunctional (fun _ => 0) k - (t : ℂ) * primePart k := by
  have h1 : ∀ n : ℕ,
      ((if 2 ≤ n then scaledWeights t n / Real.sqrt n else 0 : ℝ) : ℂ) *
          (k (Real.log n) + k (-Real.log n)) =
        (t : ℂ) * ((primeWeight n : ℂ) * (k (Real.log n) + k (-Real.log n))) := by
    intro n
    unfold scaledWeights primeWeight
    split_ifs <;> push_cast <;> ring
  have h0 : ∀ n : ℕ,
      ((if 2 ≤ n then (fun _ : ℕ => (0 : ℝ)) n / Real.sqrt n else 0 : ℝ) : ℂ) *
          (k (Real.log n) + k (-Real.log n)) = 0 := by
    intro n
    split_ifs <;> simp
  unfold weilFullFunctional
  rw [tsum_congr h1, tsum_congr h0, tsum_mul_left, tsum_zero]
  unfold primePart
  ring

/-- The real part of `H − tP`. -/
theorem re_weilFullFunctional_scaledWeights (t : ℝ) (k : ℝ → ℂ) :
    (weilFullFunctional (scaledWeights t) k).re =
      (weilFullFunctional (fun _ => 0) k).re - t * (primePart k).re := by
  rw [weilFullFunctional_scaledWeights, Complex.sub_re, Complex.re_ofReal_mul]

theorem scaledWeights_one : scaledWeights 1 = fun n => (ArithmeticFunction.vonMangoldt n : ℝ) := by
  funext n
  simp [scaledWeights]

/-! ### The Hardy interval of a window -/

/-- The **arithmetic Hardy interval** of the window `[−c, c]`: the multiples `t` of the arithmetic
part for which `H − tP` is nonnegative on every test supported in the window. -/
def hardyInterval (c : ℝ) : Set ℝ := {t | WeilPositiveFullUpTo (scaledWeights t) c}

theorem mem_hardyInterval_iff {c t : ℝ} :
    t ∈ hardyInterval c ↔ ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-c) c →
      t * (primePart (EF.weilTest f f)).re ≤ (weilFullFunctional (fun _ => 0) (EF.weilTest f f)).re := by
  refine forall_congr' fun f => imp_congr_right fun _ => imp_congr_right fun _ => ?_
  rw [re_weilFullFunctional_scaledWeights, sub_nonneg]

theorem one_mem_hardyInterval_iff {c : ℝ} :
    1 ∈ hardyInterval c ↔ WeilPositiveFullUpTo (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) c := by
  rw [hardyInterval, mem_setOf_eq, scaledWeights_one]

theorem hardyInterval_eq_iInter (c : ℝ) :
    hardyInterval c = ⋂ (f : ℝ → ℂ) (_ : ContDiff ℝ 2 f) (_ : tsupport f ⊆ Icc (-c) c),
      {t | t * (primePart (EF.weilTest f f)).re ≤
        (weilFullFunctional (fun _ => 0) (EF.weilTest f f)).re} := by
  ext t
  simp only [mem_iInter, mem_setOf_eq]
  exact mem_hardyInterval_iff

/-- `ℋ(c)` is convex. -/
theorem convex_hardyInterval (c : ℝ) : Convex ℝ (hardyInterval c) := by
  rw [hardyInterval_eq_iInter]
  refine convex_iInter fun f => convex_iInter fun _ => convex_iInter fun _ => ?_
  intro x hx y hy a b ha hb hab
  simp only [mem_setOf_eq, smul_eq_mul] at hx hy ⊢
  have e : (a * x + b * y) * (primePart (EF.weilTest f f)).re =
      a * (x * (primePart (EF.weilTest f f)).re) + b * (y * (primePart (EF.weilTest f f)).re) := by
    ring
  rw [e]
  have h1 := mul_le_mul_of_nonneg_left hx ha
  have h2 := mul_le_mul_of_nonneg_left hy hb
  have h3 : a * (weilFullFunctional (fun _ => 0) (EF.weilTest f f)).re +
      b * (weilFullFunctional (fun _ => 0) (EF.weilTest f f)).re =
        (weilFullFunctional (fun _ => 0) (EF.weilTest f f)).re := by
    rw [← add_mul, hab, one_mul]
  linarith

/-- `ℋ(c)` is closed. -/
theorem isClosed_hardyInterval (c : ℝ) : IsClosed (hardyInterval c) := by
  rw [hardyInterval_eq_iInter]
  exact isClosed_iInter fun f => isClosed_iInter fun _ => isClosed_iInter fun _ =>
    isClosed_le (continuous_id.mul continuous_const) continuous_const

/-- A larger window admits fewer multiples. -/
theorem hardyInterval_anti {c₁ c₂ : ℝ} (h : c₁ ≤ c₂) : hardyInterval c₂ ⊆ hardyInterval c₁ :=
  fun _ ht f hf hfs => ht f hf (hfs.trans (Icc_subset_Icc (by linarith) h))

/-! ### The base: `1 ∈ ℋ(c)` up to the enlarged floor aperture -/

theorem hasCompactSupport_of_tsupport_subset_Icc {f : ℝ → ℂ} {c : ℝ}
    (h : tsupport f ⊆ Icc (-c) c) : HasCompactSupport f :=
  isCompact_Icc.of_isClosed_subset (isClosed_tsupport f) h

/-- `1 ∈ ℋ(c)` for every `c` up to the unconditional floor aperture `> 181/500`. -/
theorem one_mem_hardyInterval_of_le {c : ℝ}
    (hc : c ≤ ArithmeticIncidencePositivity.enlargedWeilFloorAperture) : 1 ∈ hardyInterval c := by
  rw [one_mem_hardyInterval_iff]
  intro f hf hfs
  have hfs' : tsupport f ⊆ Icc (-ArithmeticIncidencePositivity.enlargedWeilFloorAperture)
      ArithmeticIncidencePositivity.enlargedWeilFloorAperture :=
    hfs.trans (Icc_subset_Icc (by linarith) hc)
  have hfloor :=
    ArithmeticIncidencePositivity.zetaZeroConfig_re_W_ge_of_aperture_le_enlargedWeilFloorAperture hf hfs'
  rw [zeta_W_eq_weilFullFunctional hf (hasCompactSupport_of_tsupport_subset_Icc hfs)] at hfloor
  exact le_trans (mul_nonneg (by norm_num) (integral_nonneg fun _ => by positivity)) hfloor

/-! ### Before the first prime: the whole line -/

/-- On a window with `2c < log 2` no prime lag is met. -/
theorem primePart_eq_zero {c : ℝ} {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hfs : tsupport f ⊆ Icc (-c) c)
    (hc : 2 * c < Real.log 2) : primePart (EF.weilTest f f) = 0 := by
  obtain ⟨-, -, hsupp, -⟩ := weilTest_self_data hf hfs
  have hterm : ∀ n : ℕ, (primeWeight n : ℂ) *
      (EF.weilTest f f (Real.log n) + EF.weilTest f f (-Real.log n)) = 0 := by
    intro n
    by_cases hn : 2 ≤ n
    · have hlog : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) (by exact_mod_cast hn)
      have h1 : EF.weilTest f f (Real.log n) = 0 :=
        image_eq_zero_of_notMem_tsupport fun h => by have := (hsupp h).2; linarith
      have h2 : EF.weilTest f f (-Real.log n) = 0 :=
        image_eq_zero_of_notMem_tsupport fun h => by have := (hsupp h).1; linarith
      rw [h1, h2, add_zero, mul_zero]
    · simp [primeWeight, hn]
  unfold primePart
  simp_rw [hterm, tsum_zero]

/-- `181/500 > ½ log 2`: the unconditional base reaches past the first prime. -/
theorem half_log_two_lt_enlarged :
    Real.log 2 / 2 < ArithmeticIncidencePositivity.enlargedWeilFloorAperture := by
  have h := ArithmeticIncidencePositivity.enlargedWeilFloorAperture_bounds.1
  have h2 := Real.log_two_lt_d9
  linarith

/-- **Before the first prime every multiple is admissible**: `ℋ(c) = ℝ` for `2c < log 2`. -/
theorem hardyInterval_eq_univ {c : ℝ} (hc : 2 * c < Real.log 2) : hardyInterval c = univ := by
  refine eq_univ_of_forall fun t => mem_hardyInterval_iff.mpr fun f hf hfs => ?_
  have h1 := mem_hardyInterval_iff.mp
    (one_mem_hardyInterval_of_le (by linarith [half_log_two_lt_enlarged])) f hf hfs
  rw [primePart_eq_zero hf hfs hc, Complex.zero_re, mul_zero] at h1 ⊢
  exact h1

/-! ### From the first entry on: a bounded interval -/

/-- The bump of radius `r` used for two-site tests. -/
def siteBump (r : ℝ) (hr : 0 < r) : ContDiffBump (0 : ℝ) := ⟨r / 2, r, by linarith, by linarith⟩

/-- Two bumps at `±½log 2` with relative sign `ε`. -/
def twoSiteTest (r : ℝ) (hr : 0 < r) (ε : ℝ) (u : ℝ) : ℝ :=
  siteBump r hr (u - Real.log 2 / 2) + ε * siteBump r hr (u + Real.log 2 / 2)

theorem siteBump_eq_zero {r : ℝ} (hr : 0 < r) {x : ℝ} (hx : r ≤ |x|) : siteBump r hr x = 0 :=
  (siteBump r hr).zero_of_le_dist (by rw [Real.dist_eq, sub_zero]; exact hx)

theorem abs_lt_of_siteBump_ne_zero {r : ℝ} (hr : 0 < r) {x : ℝ} (hx : siteBump r hr x ≠ 0) :
    |x| < r := by
  by_contra h
  exact hx (siteBump_eq_zero hr (not_lt.mp h))

theorem contDiff_twoSiteTest {r : ℝ} (hr : 0 < r) (ε : ℝ) : ContDiff ℝ 2 (twoSiteTest r hr ε) :=
  ((siteBump r hr).contDiff.comp (contDiff_id.sub contDiff_const)).add
    (contDiff_const.mul ((siteBump r hr).contDiff.comp (contDiff_id.add contDiff_const)))

theorem twoSiteTest_eq_zero {r : ℝ} (hr : 0 < r) (ε : ℝ) {u : ℝ}
    (hu : Real.log 2 / 2 + r < |u|) : twoSiteTest r hr ε u = 0 := by
  have h1 : r ≤ |u - Real.log 2 / 2| := by
    have := abs_sub_abs_le_abs_sub u (Real.log 2 / 2)
    rw [abs_of_pos (by positivity : (0 : ℝ) < Real.log 2 / 2)] at this
    linarith
  have h2 : r ≤ |u + Real.log 2 / 2| := by
    have := abs_sub_abs_le_abs_sub u (-(Real.log 2 / 2))
    rw [abs_neg, abs_of_pos (by positivity : (0 : ℝ) < Real.log 2 / 2), sub_neg_eq_add] at this
    linarith
  simp [twoSiteTest, siteBump_eq_zero hr h1, siteBump_eq_zero hr h2]

theorem tsupport_twoSiteTest_subset {r c : ℝ} (hr : 0 < r) (ε : ℝ) (hc : Real.log 2 / 2 + r ≤ c) :
    tsupport (fun u => (twoSiteTest r hr ε u : ℂ)) ⊆ Icc (-c) c := by
  have hc0 : 0 < c := by have := Real.log_pos (show (1 : ℝ) < 2 by norm_num); linarith
  refine closure_minimal (fun u hu => ?_) isClosed_Icc
  by_contra h
  have : c < |u| := by
    rcases not_and_or.mp h with h | h
    · have h' := not_le.mp h
      rw [abs_of_neg (by linarith)]; linarith
    · have h' := not_le.mp h
      rw [abs_of_pos (by linarith)]; exact h'
  exact hu (by simp [twoSiteTest_eq_zero hr ε (show Real.log 2 / 2 + r < |u| by linarith)])

/-- The product of two translated bumps vanishes when the centres are `≥ 2r` apart. -/
theorem siteBump_mul_eq_zero {r : ℝ} (hr : 0 < r) {x y : ℝ} (hxy : 2 * r ≤ |x - y|) :
    siteBump r hr x * siteBump r hr y = 0 := by
  by_contra h
  have hx := abs_lt_of_siteBump_ne_zero hr (left_ne_zero_of_mul h)
  have hy := abs_lt_of_siteBump_ne_zero hr (right_ne_zero_of_mul h)
  have := abs_sub (x) (y)
  linarith

/-- The autocorrelation of the two-site test at a lag `y` meeting neither `0` nor `±log 2`. -/
theorem twoSite_mul_shift_eq_zero {r : ℝ} (hr : 0 < r) (ε : ℝ) {y : ℝ} (h0 : 2 * r ≤ |y|)
    (h1 : 2 * r ≤ |y - Real.log 2|) (h2 : 2 * r ≤ |y + Real.log 2|) (t : ℝ) :
    twoSiteTest r hr ε t * twoSiteTest r hr ε (t - y) = 0 := by
  set h := Real.log 2 / 2
  have e1 : siteBump r hr (t - h) * siteBump r hr (t - y - h) = 0 :=
    siteBump_mul_eq_zero hr (by rw [show t - h - (t - y - h) = y by ring]; exact h0)
  have e2 : siteBump r hr (t - h) * siteBump r hr (t - y + h) = 0 :=
    siteBump_mul_eq_zero hr (by
      rw [show t - h - (t - y + h) = y - Real.log 2 by simp only [h]; ring]; exact h1)
  have e3 : siteBump r hr (t + h) * siteBump r hr (t - y - h) = 0 :=
    siteBump_mul_eq_zero hr (by
      rw [show t + h - (t - y - h) = y + Real.log 2 by simp only [h]; ring]; exact h2)
  have e4 : siteBump r hr (t + h) * siteBump r hr (t - y + h) = 0 :=
    siteBump_mul_eq_zero hr (by rw [show t + h - (t - y + h) = y by ring]; exact h0)
  unfold twoSiteTest
  linear_combination e1 + ε * e2 + ε * e3 + ε * ε * e4

/-- At the lag `log 2` the two-site test reads `ε‖φ‖²`. -/
theorem integral_twoSite_mul_shift_log_two {r : ℝ} (hr : 0 < r) (hr' : r ≤ Real.log 2 / 4) (ε : ℝ) :
    ∫ t, twoSiteTest r hr ε t * twoSiteTest r hr ε (t - Real.log 2) =
      ε * ∫ t, siteBump r hr t ^ 2 := by
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hpt : ∀ t, twoSiteTest r hr ε t * twoSiteTest r hr ε (t - Real.log 2) =
      ε * siteBump r hr (t - Real.log 2 / 2) ^ 2 := by
    intro t
    have e1 : siteBump r hr (t - Real.log 2 / 2) * siteBump r hr (t - Real.log 2 - Real.log 2 / 2) = 0 :=
      siteBump_mul_eq_zero hr (by
        rw [show t - Real.log 2 / 2 - (t - Real.log 2 - Real.log 2 / 2) = Real.log 2 by ring,
          abs_of_pos hl]; linarith)
    have e3 : siteBump r hr (t + Real.log 2 / 2) * siteBump r hr (t - Real.log 2 - Real.log 2 / 2) = 0 :=
      siteBump_mul_eq_zero hr (by
        rw [show t + Real.log 2 / 2 - (t - Real.log 2 - Real.log 2 / 2) = 2 * Real.log 2 by ring,
          abs_of_pos (by linarith)]; linarith)
    have e4 : siteBump r hr (t + Real.log 2 / 2) * siteBump r hr (t - Real.log 2 / 2) = 0 :=
      siteBump_mul_eq_zero hr (by
        rw [show t + Real.log 2 / 2 - (t - Real.log 2 / 2) = Real.log 2 by ring, abs_of_pos hl]
        linarith)
    have e2 : t - Real.log 2 + Real.log 2 / 2 = t - Real.log 2 / 2 := by ring
    unfold twoSiteTest
    rw [e2]
    linear_combination e1 + ε * e3 + ε * ε * e4
  simp_rw [hpt]
  rw [integral_const_mul]
  congr 1
  exact integral_sub_right_eq_self (fun t => siteBump r hr t ^ 2) (Real.log 2 / 2)

/-- For a real test the lags `ℓ` and `−ℓ` carry the same correlation. -/
theorem integral_mul_shift_neg (F : ℝ → ℝ) (ℓ : ℝ) :
    ∫ t, F t * F (t - -ℓ) = ∫ t, F t * F (t - ℓ) := by
  have h := integral_sub_right_eq_self (μ := volume) (fun t => F t * F (t + ℓ)) ℓ
  simp only [sub_add_cancel] at h
  simp_rw [sub_neg_eq_add]
  rw [← h]
  exact integral_congr_ae (Eventually.of_forall fun t => by simp only; ring)

/-- The arithmetic part of the two-site test is `2εw₂‖φ‖²`, `w₂ = Λ(2)/√2`. -/
theorem primePart_twoSiteTest {r : ℝ} (hr : 0 < r) (hr' : r ≤ 1 / 20) (ε : ℝ) :
    primePart (EF.weilTest (fun u => (twoSiteTest r hr ε u : ℂ)) (fun u => (twoSiteTest r hr ε u : ℂ))) =
      ((2 * ε * primeWeight 2 * ∫ t, siteBump r hr t ^ 2 : ℝ) : ℂ) := by
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl2 : 1 / 2 < Real.log 2 := by have := Real.log_two_gt_d9; linarith
  have hr4 : r ≤ Real.log 2 / 4 := by linarith
  set F := twoSiteTest r hr ε
  have hk : ∀ y, EF.weilTest (fun u => (F u : ℂ)) (fun u => (F u : ℂ)) y =
      ((∫ t, F t * F (t - y) : ℝ) : ℂ) := weilTest_ofReal_ofReal_eq F F
  have hlag2 : ∫ t, F t * F (t - Real.log 2) = ε * ∫ t, siteBump r hr t ^ 2 :=
    integral_twoSite_mul_shift_log_two hr hr4 ε
  have hlagn : ∀ n : ℕ, 3 ≤ n → (∫ t, F t * F (t - Real.log n)) = 0 ∧
      ∫ t, F t * F (t - -Real.log n) = 0 := by
    intro n hn
    have h3 : Real.log 3 ≤ Real.log n := Real.log_le_log (by norm_num) (by exact_mod_cast hn)
    have hlog32 : 1 / 3 ≤ Real.log 3 - Real.log 2 := by
      rw [← Real.log_div (by norm_num) (by norm_num)]
      have := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 3 / 2 by norm_num)
      norm_num at this ⊢
      linarith
    have hpos : 0 < Real.log n := by linarith
    have z : (∫ t, F t * F (t - Real.log n)) = 0 := by
      refine integral_eq_zero_of_ae (Eventually.of_forall fun t => ?_)
      refine twoSite_mul_shift_eq_zero hr ε ?_ ?_ ?_ t
      · rw [abs_of_pos hpos]; linarith
      · rw [abs_of_pos (by linarith)]; linarith
      · rw [abs_of_pos (by linarith)]; linarith
    exact ⟨z, by rw [integral_mul_shift_neg]; exact z⟩
  have hterm : ∀ n : ℕ, n ≠ 2 → (primeWeight n : ℂ) *
      (EF.weilTest (fun u => (F u : ℂ)) (fun u => (F u : ℂ)) (Real.log n) +
        EF.weilTest (fun u => (F u : ℂ)) (fun u => (F u : ℂ)) (-Real.log n)) = 0 := by
    intro n hn
    by_cases h2 : 2 ≤ n
    · obtain ⟨z1, z2⟩ := hlagn n (by omega)
      rw [hk, hk, z1, z2]
      simp
    · simp [primeWeight, h2]
  unfold primePart
  rw [tsum_eq_single 2 hterm, hk, hk]
  push_cast
  rw [integral_mul_shift_neg, hlag2]
  push_cast
  ring

theorem primeWeight_two_pos : 0 < primeWeight 2 := by
  unfold primeWeight
  rw [if_pos le_rfl, ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
  push_cast
  exact div_pos (Real.log_pos (by norm_num)) (Real.sqrt_pos.mpr (by norm_num))

theorem integral_siteBump_sq_pos {r : ℝ} (hr : 0 < r) : 0 < ∫ t, siteBump r hr t ^ 2 := by
  have hc : Continuous fun t => siteBump r hr t ^ 2 := (siteBump r hr).continuous.pow 2
  have hcs : HasCompactSupport fun t => siteBump r hr t ^ 2 :=
    (siteBump r hr).hasCompactSupport.comp_left (g := fun z : ℝ => z ^ 2) (by norm_num)
  refine hc.integral_pos_of_hasCompactSupport_nonneg_nonzero hcs (fun _ => sq_nonneg _)
    (x := 0) ?_
  have : 0 < siteBump r hr 0 := (siteBump r hr).pos_of_mem_ball (Metric.mem_ball_self hr)
  positivity

/-- **From the first prime on, the Hardy interval is bounded**: for `2c > log 2` there are
`L ≤ U` with `ℋ(c) ⊆ [L, U]`, read by the even and odd two-site tests at distance `log 2`. -/
theorem hardyInterval_bounded {c : ℝ} (hc : Real.log 2 < 2 * c) :
    ∃ L U : ℝ, hardyInterval c ⊆ Icc L U := by
  set r := min (1 / 20) ((c - Real.log 2 / 2) / 2) with hr_def
  have hr : 0 < r := lt_min (by norm_num) (by linarith)
  have hr20 : r ≤ 1 / 20 := min_le_left _ _
  have hrc : Real.log 2 / 2 + r ≤ c := by linarith [min_le_right (1 / 20 : ℝ) ((c - Real.log 2 / 2) / 2)]
  set m := ∫ t, siteBump r hr t ^ 2
  have hm := integral_siteBump_sq_pos hr
  have hw := primeWeight_two_pos
  set B : ℝ := 2 * primeWeight 2 * m
  have hB : 0 < B := by positivity
  let A : ℝ → ℝ := fun ε => (weilFullFunctional (fun _ => 0)
    (EF.weilTest (fun u => (twoSiteTest r hr ε u : ℂ)) (fun u => (twoSiteTest r hr ε u : ℂ)))).re
  refine ⟨-A (-1) / B, A 1 / B, fun t ht => ?_⟩
  have key : ∀ ε : ℝ, t * (2 * ε * primeWeight 2 * m) ≤ A ε := by
    intro ε
    have h := mem_hardyInterval_iff.mp ht (fun u => (twoSiteTest r hr ε u : ℂ))
      (Complex.ofRealCLM.contDiff.comp (contDiff_twoSiteTest hr ε))
      (tsupport_twoSiteTest_subset hr ε hrc)
    rw [primePart_twoSiteTest hr hr20 ε, Complex.ofReal_re] at h
    exact h
  have h1 := key 1
  have h2 := key (-1)
  constructor
  · rw [div_le_iff₀ hB]; nlinarith
  · rw [le_div_iff₀ hB]; nlinarith

/-! ### Scaling optimality and criticality -/

theorem exists_Icc_of_hasCompactSupport {f : ℝ → ℂ} (hf : HasCompactSupport f) :
    ∃ R : ℝ, tsupport f ⊆ Icc (-R) R := by
  obtain ⟨R, hR⟩ := hf.isCompact.isBounded.subset_closedBall 0
  exact ⟨R, fun x hx => by
    have := hR hx
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at this
    exact abs_le.mp this⟩

theorem weilPositiveFull_of_forall_upTo {lam : ℕ → ℝ} (h : ∀ c, WeilPositiveFullUpTo lam c) :
    WeilPositiveFull lam := fun f hf hfc => by
  obtain ⟨R, hR⟩ := exists_Icc_of_hasCompactSupport hfc
  exact h R f hf hR

/-- **Scaling optimality, unconditionally.** A multiple of the arithmetic part that is a Hardy term on
every window is the arithmetic part itself. -/
theorem eq_one_of_forall_mem_hardyInterval {t : ℝ} (h : ∀ c, t ∈ hardyInterval c) : t = 1 := by
  have hW := weilPositiveFull_of_forall_upTo h
  have h2 := WeilSpectral.eq_vonMangoldt_of_weilPositiveFull hW 2 le_rfl
  have hΛ : (ArithmeticFunction.vonMangoldt 2 : ℝ) ≠ 0 := by
    rw [ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
    exact (Real.log_pos (by norm_num)).ne'
  simp only [scaledWeights] at h2
  have := mul_right_cancel₀ hΛ (h2.trans (one_mul _).symm)
  exact this

/-- RH holds iff the arithmetic part is a Hardy term on every window. -/
theorem riemannHypothesis_iff_forall_one_mem_hardyInterval :
    RiemannHypothesis ↔ ∀ c, 1 ∈ hardyInterval c := by
  constructor
  · intro hRH c f hf hfs
    have hW := (WeilSpectral.weilPositiveFull_iff_riemannHypothesis_and_eq_vonMangoldt
      (lam := fun n => (ArithmeticFunction.vonMangoldt n : ℝ))).mpr ⟨hRH, fun _ _ => rfl⟩
    rw [scaledWeights_one]
    exact hW f hf (hasCompactSupport_of_tsupport_subset_Icc hfs)
  · intro h
    have hW : WeilPositiveFull (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) :=
      weilPositiveFull_of_forall_upTo fun c => one_mem_hardyInterval_iff.mp (h c)
    exact ((WeilSpectral.weilPositiveFull_iff_riemannHypothesis_and_eq_vonMangoldt).mp hW).1

/-- RH holds iff the Hardy intervals shrink exactly to `{1}`. -/
theorem riemannHypothesis_iff_iInter_hardyInterval_eq :
    RiemannHypothesis ↔ (⋂ c, hardyInterval c) = {1} := by
  rw [riemannHypothesis_iff_forall_one_mem_hardyInterval]
  constructor
  · intro h
    ext t
    simp only [mem_iInter, mem_singleton_iff]
    exact ⟨eq_one_of_forall_mem_hardyInterval, fun ht => ht ▸ h⟩
  · intro h c
    have : (1 : ℝ) ∈ ⋂ c, hardyInterval c := by rw [h]; rfl
    exact mem_iInter.mp this c

/-- **Criticality, unconditionally.** Weil's form admits no Hardy weight on odd tests: for every
nonnegative locally integrable `W` with positive mass some odd test has `Re W_ζ(F, F) < ∫ W F²`. -/
theorem not_exists_hardyWeight {W : ℝ → ℝ} (hW0 : ∀ x, 0 ≤ W x) (hWi : LocallyIntegrable W)
    (hWpos : 0 < volume {x | 0 < W x}) :
    ∃ F : ℝ → ℝ, ContDiff ℝ 2 F ∧ HasCompactSupport F ∧ (∀ x, F (-x) = -F x) ∧
      (weilFullFunctional (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
        (EF.weilTest (fun u => (F u : ℂ)) (fun u => (F u : ℂ)))).re < ∫ x, W x * F x ^ 2 := by
  obtain ⟨v, hv, hvc, hodd, hlt⟩ :=
    ArithmeticCriticalityTheory.exists_odd_markovEnergy_lt_integral_weight_mul_sq hW0 hWi hWpos
  set F := phiDoobTest v
  have hF := contDiff_phiDoobTest hv
  have hFc := hasCompactSupport_phiDoobTest hvc
  have hFodd : ∀ x, F (-x) = -F x := phiDoobTest_odd hodd
  refine ⟨F, hF, hFc, hFodd, lt_of_le_of_lt ?_ hlt⟩
  have hpole := re_weilPoleTerm_ofReal_eq_two_mul_cosh_sq_sub_sinh_sq hF.continuous hFc
  have hcosh : coshHalfMoment F = 0 := by
    unfold coshHalfMoment
    have h : ∫ x, F (-x) * Real.cosh (-x / 2) = ∫ x, F x * Real.cosh (x / 2) :=
      integral_neg_eq_self (fun x => F x * Real.cosh (x / 2)) volume
    have e : (fun x => F (-x) * Real.cosh (-x / 2)) = fun x => -(F x * Real.cosh (x / 2)) := by
      funext x
      rw [hFodd, show -x / 2 = -(x / 2) by ring, Real.cosh_neg]
      ring
    rw [e, integral_neg] at h
    linarith
  unfold markovEnergy
  rw [Complex.sub_re, hpole, hcosh]
  nlinarith [sq_nonneg (sinhHalfMoment F)]

/-! ### The arithmetic part is an optimal Hardy term iff RH -/

/-- The arithmetic part is an **optimal Hardy term** for the archimedean–polar form: a Hardy term on
every window, no other multiple is one, and no Hardy weight remains. -/
def ArithmeticPartIsOptimalHardyTerm : Prop :=
  (∀ c, 1 ∈ hardyInterval c) ∧ (∀ t, (∀ c, t ∈ hardyInterval c) → t = 1) ∧
    ∀ W : ℝ → ℝ, (∀ x, 0 ≤ W x) → LocallyIntegrable W → 0 < volume {x | 0 < W x} →
      ¬ ∀ F : ℝ → ℝ, ContDiff ℝ 2 F → HasCompactSupport F →
        ∫ x, W x * F x ^ 2 ≤ (weilFullFunctional (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
          (EF.weilTest (fun u => (F u : ℂ)) (fun u => (F u : ℂ)))).re

/-- **Q1.** The arithmetic part of Weil's form is an optimal Hardy term for the archimedean
logarithmic jump operator with the pole kept iff RH; scaling optimality and criticality hold
unconditionally. -/
theorem isOptimalHardyTerm_iff_RH : ArithmeticPartIsOptimalHardyTerm ↔ RiemannHypothesis := by
  rw [riemannHypothesis_iff_forall_one_mem_hardyInterval]
  refine ⟨fun h => h.1, fun h => ⟨h, fun _ => eq_one_of_forall_mem_hardyInterval, ?_⟩⟩
  intro W hW0 hWi hWpos hall
  obtain ⟨F, hF, hFc, -, hlt⟩ := not_exists_hardyWeight hW0 hWi hWpos
  exact absurd (hall F hF hFc) (not_le.mpr hlt)

end GaloisForLFunctions.FrustratedArithmeticDirichletForms
