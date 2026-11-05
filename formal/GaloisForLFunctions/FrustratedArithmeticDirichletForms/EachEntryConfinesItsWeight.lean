import GaloisForLFunctions.FrustratedArithmeticDirichletForms.TheArithmeticHardyInterval
import GaloisForLFunctions.DimensionZeroGeometryOfSpecZ.TheArchimedeanPlaceAloneIsNotWeilPositive

/-!
# Each entry confines its weight

The **calibration space** of the window `[−c, c]` is the finite-level Weil cone

  `𝒜(c) = {λ : ℕ → ℝ : Weil's functional with prime weights λ is ≥ 0 on tests in [−c, c]}`,

the set of arithmetic data (weights at the prime powers, archimedean place and pole fixed) for which
the window form is nonnegative; `ζ`'s point is `Λ`. A window reads only the weights it can see, and
it reads each of them two-sidedly as soon as it sees it:

* **Locality** (DZG `weilPositiveFullUpTo_congr`): `𝒜(c)` is a cylinder over the coordinates
  `n > e^{2c}`.
* **Convexity** (`convex_calibration`): `𝒜(c)` is convex, since the functional is affine in `λ`
  (`weilFullFunctional_eq_sub_weightedPrimePart`).
* **Entry confinement** (`calibration_coord_bounded`): for every `n₀ ≥ 2` with `log n₀ < 2c` there
  are `L ≤ U` with `λ(n₀) ∈ [L, U]` for all `λ ∈ 𝒜(c)`. The witnesses are the two two-site tests at
  distance `log n₀` (bumps at `±½log n₀`, one even, one odd), whose autocorrelation meets the single
  lag `log n₀` (`weightedPrimePart_twoSiteAt`).

So the calibration space acquires exactly one bounded direction at each prime-power entry
`c = ½log n₀`, and before the entry that direction is free. With the full-cone uniqueness
`⋂_c 𝒜(c) = {Λ}` under RH and `= ∅` otherwise (RHTower), the window tower is a nested family of
convex sets, each new direction entering bounded; the arithmetic point must lie in all of them.
-/

open MeasureTheory Set Filter Topology Complex
open scoped Real

noncomputable section

namespace GaloisForLFunctions.FrustratedArithmeticDirichletForms

open _root_.RHTower _root_.Zeta23

/-- The calibration space of the window `[−c, c]`. -/
def calibration (c : ℝ) : Set (ℕ → ℝ) := {lam | WeilPositiveFullUpTo lam c}

/-- The weighted prime part `Σ_{n ≥ 2} λ(n)n^{−1/2}(k(log n) + k(−log n))`. -/
def weightedPrimePart (lam : ℕ → ℝ) (k : ℝ → ℂ) : ℂ :=
  ∑' n : ℕ, ((if 2 ≤ n then lam n / Real.sqrt n else 0 : ℝ) : ℂ) * (k (Real.log n) + k (-Real.log n))

theorem weilFullFunctional_eq_sub_weightedPrimePart (lam : ℕ → ℝ) (k : ℝ → ℂ) :
    weilFullFunctional lam k = weilFullFunctional (fun _ => 0) k - weightedPrimePart lam k := by
  have h0 : ∀ n : ℕ,
      ((if 2 ≤ n then (fun _ : ℕ => (0 : ℝ)) n / Real.sqrt n else 0 : ℝ) : ℂ) *
          (k (Real.log n) + k (-Real.log n)) = 0 := by
    intro n
    split_ifs <;> simp
  unfold weilFullFunctional weightedPrimePart
  rw [tsum_congr h0, tsum_zero]
  ring

/-- On a test with compact support the weighted prime part is linear in the weights. -/
theorem weightedPrimePart_affine {k : ℝ → ℂ} {N : ℕ}
    (hN : ∀ n : ℕ, N ≤ n → k (Real.log n) = 0 ∧ k (-Real.log n) = 0) (lam : ℕ → ℝ) :
    weightedPrimePart lam k = ∑ n ∈ Finset.range N,
      ((if 2 ≤ n then lam n / Real.sqrt n else 0 : ℝ) : ℂ) * (k (Real.log n) + k (-Real.log n)) := by
  unfold weightedPrimePart
  refine tsum_eq_sum fun n hn => ?_
  have h := hN n (by simpa using hn)
  rw [h.1, h.2, add_zero, mul_zero]

/-- **The calibration space is convex.** -/
theorem convex_calibration (c : ℝ) : Convex ℝ (calibration c) := by
  intro lam₁ h₁ lam₂ h₂ a b ha hb hab f hf hfs
  obtain ⟨-, -, hsupp, -⟩ := weilTest_self_data hf hfs
  set k := EF.weilTest f f
  set N := ⌊Real.exp (2 * c)⌋₊ + 1
  have hN : ∀ n : ℕ, N ≤ n → k (Real.log n) = 0 ∧ k (-Real.log n) = 0 := by
    intro n hn
    have hn' : Real.exp (2 * c) < n := by
      have := Nat.lt_floor_add_one (Real.exp (2 * c))
      have h2 : (N : ℝ) ≤ n := by exact_mod_cast hn
      push_cast [N] at h2
      linarith
    have hn0 : (0 : ℝ) < n := (Real.exp_pos _).trans hn'
    have hlog : 2 * c < Real.log n := (Real.lt_log_iff_exp_lt hn0).mpr hn'
    exact ⟨image_eq_zero_of_notMem_tsupport fun h => by have := (hsupp h).2; linarith,
      image_eq_zero_of_notMem_tsupport fun h => by have := (hsupp h).1; linarith⟩
  have e1 := h₁ f hf hfs
  have e2 := h₂ f hf hfs
  rw [weilFullFunctional_eq_sub_weightedPrimePart, Complex.sub_re] at e1 e2 ⊢
  rw [weightedPrimePart_affine hN] at e1 e2 ⊢
  have hlin : (∑ n ∈ Finset.range N, ((if 2 ≤ n then (a • lam₁ + b • lam₂) n / Real.sqrt n
        else 0 : ℝ) : ℂ) * (k (Real.log n) + k (-Real.log n))) =
      (a : ℂ) * (∑ n ∈ Finset.range N, ((if 2 ≤ n then lam₁ n / Real.sqrt n else 0 : ℝ) : ℂ) *
        (k (Real.log n) + k (-Real.log n))) +
      (b : ℂ) * (∑ n ∈ Finset.range N, ((if 2 ≤ n then lam₂ n / Real.sqrt n else 0 : ℝ) : ℂ) *
        (k (Real.log n) + k (-Real.log n))) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    split_ifs <;> push_cast <;> ring
  rw [hlin, Complex.add_re, Complex.re_ofReal_mul, Complex.re_ofReal_mul]
  set A := (weilFullFunctional (fun _ => 0) k).re
  have hA : A = a * A + b * A := by rw [← add_mul, hab, one_mul]
  nlinarith [mul_nonneg ha (sub_nonneg.mpr (sub_nonneg.mp e1)),
    mul_nonneg hb (sub_nonneg.mpr (sub_nonneg.mp e2))]

/-! ### Two-site tests at a general distance -/

/-- Two bumps at `±ℓ/2` with relative sign `ε`. -/
def twoSiteTestAt (ℓ r : ℝ) (hr : 0 < r) (ε : ℝ) (u : ℝ) : ℝ :=
  siteBump r hr (u - ℓ / 2) + ε * siteBump r hr (u + ℓ / 2)

theorem contDiff_twoSiteTestAt (ℓ : ℝ) {r : ℝ} (hr : 0 < r) (ε : ℝ) :
    ContDiff ℝ 2 (twoSiteTestAt ℓ r hr ε) :=
  ((siteBump r hr).contDiff.comp (contDiff_id.sub contDiff_const)).add
    (contDiff_const.mul ((siteBump r hr).contDiff.comp (contDiff_id.add contDiff_const)))

theorem tsupport_twoSiteTestAt_subset {ℓ r c : ℝ} (hℓ : 0 ≤ ℓ) (hr : 0 < r) (ε : ℝ)
    (hc : ℓ / 2 + r ≤ c) :
    tsupport (fun u => (twoSiteTestAt ℓ r hr ε u : ℂ)) ⊆ Icc (-c) c := by
  have hc0 : 0 < c := by linarith
  refine closure_minimal (fun u hu => ?_) isClosed_Icc
  by_contra h
  have hcu : c < |u| := by
    rcases not_and_or.mp h with h | h
    · have h' := not_le.mp h
      rw [abs_of_neg (by linarith)]; linarith
    · have h' := not_le.mp h
      rw [abs_of_pos (by linarith)]; exact h'
  have h1 : r ≤ |u - ℓ / 2| := by
    have := abs_sub_abs_le_abs_sub u (ℓ / 2)
    rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ ℓ / 2)] at this
    linarith
  have h2 : r ≤ |u + ℓ / 2| := by
    have := abs_sub_abs_le_abs_sub u (-(ℓ / 2))
    rw [abs_neg, abs_of_nonneg (by linarith : (0 : ℝ) ≤ ℓ / 2), sub_neg_eq_add] at this
    linarith
  exact hu (by simp [twoSiteTestAt, siteBump_eq_zero hr h1, siteBump_eq_zero hr h2])

/-- The autocorrelation of the two-site test at distance `ℓ` vanishes at lags `y` that meet neither
`0` nor `±ℓ`. -/
theorem twoSiteAt_mul_shift_eq_zero {ℓ r : ℝ} (hr : 0 < r) (ε : ℝ) {y : ℝ} (h0 : 2 * r ≤ |y|)
    (h1 : 2 * r ≤ |y - ℓ|) (h2 : 2 * r ≤ |y + ℓ|) (t : ℝ) :
    twoSiteTestAt ℓ r hr ε t * twoSiteTestAt ℓ r hr ε (t - y) = 0 := by
  have e1 : siteBump r hr (t - ℓ / 2) * siteBump r hr (t - y - ℓ / 2) = 0 :=
    siteBump_mul_eq_zero hr (by rw [show t - ℓ / 2 - (t - y - ℓ / 2) = y by ring]; exact h0)
  have e2 : siteBump r hr (t - ℓ / 2) * siteBump r hr (t - y + ℓ / 2) = 0 :=
    siteBump_mul_eq_zero hr (by rw [show t - ℓ / 2 - (t - y + ℓ / 2) = y - ℓ by ring]; exact h1)
  have e3 : siteBump r hr (t + ℓ / 2) * siteBump r hr (t - y - ℓ / 2) = 0 :=
    siteBump_mul_eq_zero hr (by rw [show t + ℓ / 2 - (t - y - ℓ / 2) = y + ℓ by ring]; exact h2)
  have e4 : siteBump r hr (t + ℓ / 2) * siteBump r hr (t - y + ℓ / 2) = 0 :=
    siteBump_mul_eq_zero hr (by rw [show t + ℓ / 2 - (t - y + ℓ / 2) = y by ring]; exact h0)
  unfold twoSiteTestAt
  linear_combination e1 + ε * e2 + ε * e3 + ε * ε * e4

/-- At its own lag `ℓ` the two-site test reads `ε‖φ‖²`. -/
theorem integral_twoSiteAt_mul_shift {ℓ r : ℝ} (hr : 0 < r) (hrℓ : 2 * r ≤ ℓ) (ε : ℝ) :
    ∫ t, twoSiteTestAt ℓ r hr ε t * twoSiteTestAt ℓ r hr ε (t - ℓ) = ε * ∫ t, siteBump r hr t ^ 2 := by
  have hpt : ∀ t, twoSiteTestAt ℓ r hr ε t * twoSiteTestAt ℓ r hr ε (t - ℓ) =
      ε * siteBump r hr (t - ℓ / 2) ^ 2 := by
    intro t
    have hℓ : 0 ≤ ℓ := by linarith
    have e1 : siteBump r hr (t - ℓ / 2) * siteBump r hr (t - ℓ - ℓ / 2) = 0 :=
      siteBump_mul_eq_zero hr (by
        rw [show t - ℓ / 2 - (t - ℓ - ℓ / 2) = ℓ by ring, abs_of_nonneg hℓ]; exact hrℓ)
    have e3 : siteBump r hr (t + ℓ / 2) * siteBump r hr (t - ℓ - ℓ / 2) = 0 :=
      siteBump_mul_eq_zero hr (by
        rw [show t + ℓ / 2 - (t - ℓ - ℓ / 2) = 2 * ℓ by ring, abs_of_nonneg (by linarith)]
        linarith)
    have e4 : siteBump r hr (t + ℓ / 2) * siteBump r hr (t - ℓ / 2) = 0 :=
      siteBump_mul_eq_zero hr (by
        rw [show t + ℓ / 2 - (t - ℓ / 2) = ℓ by ring, abs_of_nonneg hℓ]; exact hrℓ)
    have e2 : t - ℓ + ℓ / 2 = t - ℓ / 2 := by ring
    unfold twoSiteTestAt
    rw [e2]
    linear_combination e1 + ε * e3 + ε * ε * e4
  simp_rw [hpt]
  rw [integral_const_mul]
  congr 1
  exact integral_sub_right_eq_self (fun t => siteBump r hr t ^ 2) (ℓ / 2)

/-- The gap between `log n₀` and the logarithms of all other integers `≥ 2`. -/
theorem exists_log_gap (n₀ : ℕ) (hn₀ : 2 ≤ n₀) :
    ∃ g : ℝ, 0 < g ∧ ∀ m : ℕ, 2 ≤ m → m ≠ n₀ → g ≤ |Real.log m - Real.log n₀| := by
  have hpos : (0 : ℝ) < n₀ := by exact_mod_cast (by omega : 0 < n₀)
  have hup : 0 < Real.log (n₀ + 1) - Real.log n₀ := by
    have := Real.log_lt_log hpos (by linarith : (n₀ : ℝ) < n₀ + 1)
    linarith
  have hdn : 0 < Real.log n₀ - Real.log (n₀ - 1) := by
    have h1 : (0 : ℝ) < n₀ - 1 := by
      have : (2 : ℝ) ≤ n₀ := by exact_mod_cast hn₀
      linarith
    have := Real.log_lt_log h1 (by linarith : (n₀ : ℝ) - 1 < n₀)
    linarith
  refine ⟨min (Real.log (n₀ + 1) - Real.log n₀) (Real.log n₀ - Real.log (n₀ - 1)),
    lt_min hup hdn, fun m hm hne => ?_⟩
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  rcases lt_or_gt_of_ne hne with h | h
  · have hle : (m : ℝ) ≤ n₀ - 1 := by
      have : m + 1 ≤ n₀ := h
      have : (m : ℝ) + 1 ≤ n₀ := by exact_mod_cast this
      linarith
    have hlog := Real.log_le_log hm0 hle
    rw [abs_of_neg (by linarith [Real.log_lt_log hm0 (by exact_mod_cast h : (m : ℝ) < n₀)])]
    linarith [min_le_right (Real.log (n₀ + 1) - Real.log n₀) (Real.log n₀ - Real.log (n₀ - 1))]
  · have hle : (n₀ : ℝ) + 1 ≤ m := by
      have : n₀ + 1 ≤ m := h
      exact_mod_cast this
    have hlog := Real.log_le_log (by linarith) hle
    rw [abs_of_pos (by linarith [Real.log_lt_log hpos (by exact_mod_cast h : (n₀ : ℝ) < m)])]
    linarith [min_le_left (Real.log (n₀ + 1) - Real.log n₀) (Real.log n₀ - Real.log (n₀ - 1))]

/-- The weighted prime part of the two-site test at distance `log n₀` reads the single weight
`λ(n₀)`: it equals `2ελ(n₀)n₀^{−1/2}‖φ‖²` once `2r` is below every gap at `log n₀` and below
`log 2`. -/
theorem weightedPrimePart_twoSiteAt {n₀ : ℕ} (hn₀ : 2 ≤ n₀) {r g : ℝ} (hr : 0 < r)
    (hg : ∀ m : ℕ, 2 ≤ m → m ≠ n₀ → g ≤ |Real.log m - Real.log n₀|) (hrg : 2 * r ≤ g)
    (hr2 : 2 * r ≤ Real.log 2) (lam : ℕ → ℝ) (ε : ℝ) :
    weightedPrimePart lam (EF.weilTest (fun u => (twoSiteTestAt (Real.log n₀) r hr ε u : ℂ))
        (fun u => (twoSiteTestAt (Real.log n₀) r hr ε u : ℂ))) =
      ((2 * ε * (lam n₀ / Real.sqrt n₀) * ∫ t, siteBump r hr t ^ 2 : ℝ) : ℂ) := by
  set ℓ := Real.log n₀
  set F := twoSiteTestAt ℓ r hr ε
  have hl2 : Real.log 2 ≤ ℓ := Real.log_le_log (by norm_num) (by exact_mod_cast hn₀)
  have hk : ∀ y, EF.weilTest (fun u => (F u : ℂ)) (fun u => (F u : ℂ)) y =
      ((∫ t, F t * F (t - y) : ℝ) : ℂ) := weilTest_ofReal_ofReal_eq F F
  have hlag : ∫ t, F t * F (t - ℓ) = ε * ∫ t, siteBump r hr t ^ 2 :=
    integral_twoSiteAt_mul_shift hr (by linarith) ε
  have hother : ∀ m : ℕ, 2 ≤ m → m ≠ n₀ →
      (∫ t, F t * F (t - Real.log m)) = 0 ∧ ∫ t, F t * F (t - -Real.log m) = 0 := by
    intro m hm hne
    have hlm : Real.log 2 ≤ Real.log m := Real.log_le_log (by norm_num) (by exact_mod_cast hm)
    have hgap := hg m hm hne
    have z : (∫ t, F t * F (t - Real.log m)) = 0 := by
      refine integral_eq_zero_of_ae (Eventually.of_forall fun t => ?_)
      refine twoSiteAt_mul_shift_eq_zero hr ε ?_ (hrg.trans hgap) ?_ t
      · rw [abs_of_pos (by linarith)]; linarith
      · rw [abs_of_pos (by linarith)]; linarith
    exact ⟨z, by rw [integral_mul_shift_neg]; exact z⟩
  have hterm : ∀ m : ℕ, m ≠ n₀ → ((if 2 ≤ m then lam m / Real.sqrt m else 0 : ℝ) : ℂ) *
      (EF.weilTest (fun u => (F u : ℂ)) (fun u => (F u : ℂ)) (Real.log m) +
        EF.weilTest (fun u => (F u : ℂ)) (fun u => (F u : ℂ)) (-Real.log m)) = 0 := by
    intro m hm
    by_cases h2 : 2 ≤ m
    · obtain ⟨z1, z2⟩ := hother m h2 hm
      rw [hk, hk, z1, z2]
      simp
    · simp [h2]
  unfold weightedPrimePart
  rw [tsum_eq_single n₀ hterm, hk, hk, if_pos hn₀]
  push_cast
  rw [integral_mul_shift_neg, hlag]
  push_cast
  ring

/-- **Entry confinement.** Once `n₀` acts on the window (`log n₀ < 2c`), its weight is bounded on the
calibration space: `λ(n₀) ∈ [L, U]` for every `λ ∈ 𝒜(c)`. -/
theorem calibration_coord_bounded {c : ℝ} {n₀ : ℕ} (hn₀ : 2 ≤ n₀) (hc : Real.log n₀ < 2 * c) :
    ∃ L U : ℝ, ∀ lam ∈ calibration c, lam n₀ ∈ Icc L U := by
  obtain ⟨g, hg0, hg⟩ := exists_log_gap n₀ hn₀
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set ℓ := Real.log n₀
  have hℓ : 0 ≤ ℓ := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n₀))
  set r := min (min (g / 2) (Real.log 2 / 2)) ((c - ℓ / 2) / 2) with hr_def
  have hr : 0 < r := lt_min (lt_min (by linarith) (by linarith)) (by linarith)
  have hrg : 2 * r ≤ g := by
    linarith [show r ≤ g / 2 from (min_le_left _ _).trans (min_le_left _ _)]
  have hr2 : 2 * r ≤ Real.log 2 := by
    linarith [show r ≤ Real.log 2 / 2 from (min_le_left _ _).trans (min_le_right _ _)]
  have hrc : ℓ / 2 + r ≤ c := by linarith [show r ≤ (c - ℓ / 2) / 2 from min_le_right _ _]
  set m := ∫ t, siteBump r hr t ^ 2
  have hm := integral_siteBump_sq_pos hr
  have hsq : 0 < Real.sqrt n₀ := Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < n₀))
  let A : ℝ → ℝ := fun ε => (weilFullFunctional (fun _ => 0)
    (EF.weilTest (fun u => (twoSiteTestAt ℓ r hr ε u : ℂ))
      (fun u => (twoSiteTestAt ℓ r hr ε u : ℂ)))).re
  have hB : 0 < 2 * m / Real.sqrt n₀ := div_pos (by linarith) hsq
  refine ⟨-A (-1) / (2 * m / Real.sqrt n₀), A 1 / (2 * m / Real.sqrt n₀), fun lam hlam => ?_⟩
  have key : ∀ ε : ℝ, ε * (lam n₀ * (2 * m / Real.sqrt n₀)) ≤ A ε := by
    intro ε
    have h := hlam (fun u => (twoSiteTestAt ℓ r hr ε u : ℂ))
      (Complex.ofRealCLM.contDiff.comp (contDiff_twoSiteTestAt ℓ hr ε))
      (tsupport_twoSiteTestAt_subset hℓ hr ε hrc)
    rw [weilFullFunctional_eq_sub_weightedPrimePart, Complex.sub_re,
      weightedPrimePart_twoSiteAt hn₀ hr hg hrg hr2 lam ε, Complex.ofReal_re] at h
    have e : 2 * ε * (lam n₀ / Real.sqrt n₀) * m = ε * (lam n₀ * (2 * m / Real.sqrt n₀)) := by
      ring
    linarith
  have h1 := key 1
  have h2 := key (-1)
  constructor
  · rw [div_le_iff₀ hB]; linarith
  · rw [le_div_iff₀ hB]; linarith

/-! ### The stage step is an interval -/

/-- The weight sequence `λ` with its value at `n₀` replaced by `t`. -/
def withWeight (lam : ℕ → ℝ) (n₀ : ℕ) (t : ℝ) : ℕ → ℝ := Function.update lam n₀ t

/-- Changing one weight moves Weil's functional along a line. -/
theorem re_weilFullFunctional_withWeight (lam : ℕ → ℝ) {n₀ : ℕ} (hn₀ : 2 ≤ n₀) (t : ℝ)
    {k : ℝ → ℂ} {N : ℕ} (hN : ∀ n : ℕ, N ≤ n → k (Real.log n) = 0 ∧ k (-Real.log n) = 0) :
    (weilFullFunctional (withWeight lam n₀ t) k).re = (weilFullFunctional lam k).re -
      (t - lam n₀) / Real.sqrt n₀ * (k (Real.log n₀) + k (-Real.log n₀)).re := by
  rw [weilFullFunctional_eq_sub_weightedPrimePart, weilFullFunctional_eq_sub_weightedPrimePart
    lam k, Complex.sub_re, Complex.sub_re, weightedPrimePart_affine hN,
    weightedPrimePart_affine hN]
  by_cases hmem : n₀ ∈ Finset.range N
  · rw [← Finset.add_sum_erase _ _ hmem, ← Finset.add_sum_erase _ _ hmem]
    have hrest : (∑ n ∈ (Finset.range N).erase n₀,
        ((if 2 ≤ n then withWeight lam n₀ t n / Real.sqrt n else 0 : ℝ) : ℂ) *
          (k (Real.log n) + k (-Real.log n))) =
        ∑ n ∈ (Finset.range N).erase n₀,
          ((if 2 ≤ n then lam n / Real.sqrt n else 0 : ℝ) : ℂ) * (k (Real.log n) + k (-Real.log n)) := by
      refine Finset.sum_congr rfl fun n hn => ?_
      rw [withWeight, Function.update_of_ne (Finset.ne_of_mem_erase hn)]
    rw [hrest, withWeight, Function.update_self, if_pos hn₀, if_pos hn₀]
    simp only [Complex.add_re, Complex.re_ofReal_mul]
    ring
  · have h := hN n₀ (by simpa using hmem)
    rw [h.1, h.2]
    have hsum : (∑ n ∈ Finset.range N,
        ((if 2 ≤ n then withWeight lam n₀ t n / Real.sqrt n else 0 : ℝ) : ℂ) *
          (k (Real.log n) + k (-Real.log n))) =
        ∑ n ∈ Finset.range N,
          ((if 2 ≤ n then lam n / Real.sqrt n else 0 : ℝ) : ℂ) * (k (Real.log n) + k (-Real.log n)) := by
      refine Finset.sum_congr rfl fun n hn => ?_
      rw [withWeight, Function.update_of_ne (ne_of_mem_of_not_mem hn hmem)]
    rw [hsum]
    simp

/-- **The stage step is a compact interval.** For fixed older weights, the values `t` of the weight
at an acting `n₀` for which the window stays nonnegative form a closed, convex, bounded set. -/
theorem stageFibre_interval (lam : ℕ → ℝ) {c : ℝ} {n₀ : ℕ} (hn₀ : 2 ≤ n₀)
    (hc : Real.log n₀ < 2 * c) :
    Convex ℝ {t : ℝ | withWeight lam n₀ t ∈ calibration c} ∧
      IsClosed {t : ℝ | withWeight lam n₀ t ∈ calibration c} ∧
        ∃ L U : ℝ, {t : ℝ | withWeight lam n₀ t ∈ calibration c} ⊆ Icc L U := by
  refine ⟨?_, ?_, ?_⟩
  · intro t₁ h₁ t₂ h₂ a b ha hb hab
    have hc' := convex_calibration c h₁ h₂ ha hb hab
    have e : a • withWeight lam n₀ t₁ + b • withWeight lam n₀ t₂ = withWeight lam n₀ (a • t₁ + b • t₂) := by
      funext n
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, withWeight]
      by_cases hn : n = n₀
      · subst hn; simp
      · rw [Function.update_of_ne hn, Function.update_of_ne hn, Function.update_of_ne hn, ← add_mul,
          hab, one_mul]
    simpa [e] using hc'
  · have hset : {t : ℝ | withWeight lam n₀ t ∈ calibration c} =
        ⋂ (f : ℝ → ℂ) (_ : ContDiff ℝ 2 f) (_ : tsupport f ⊆ Icc (-c) c),
          {t | 0 ≤ (weilFullFunctional (withWeight lam n₀ t) (EF.weilTest f f)).re} := by
      ext t; simp only [mem_setOf_eq, mem_iInter]; rfl
    rw [hset]
    refine isClosed_iInter fun f => isClosed_iInter fun hf => isClosed_iInter fun hfs => ?_
    obtain ⟨-, -, hsupp, -⟩ := weilTest_self_data hf hfs
    set N := ⌊Real.exp (2 * c)⌋₊ + 1
    have hN : ∀ n : ℕ, N ≤ n →
        EF.weilTest f f (Real.log n) = 0 ∧ EF.weilTest f f (-Real.log n) = 0 := by
      intro n hn
      have hn' : Real.exp (2 * c) < n := by
        have := Nat.lt_floor_add_one (Real.exp (2 * c))
        have h2 : (N : ℝ) ≤ n := by exact_mod_cast hn
        push_cast [N] at h2
        linarith
      have hn0 : (0 : ℝ) < n := (Real.exp_pos _).trans hn'
      have hlog : 2 * c < Real.log n := (Real.lt_log_iff_exp_lt hn0).mpr hn'
      exact ⟨image_eq_zero_of_notMem_tsupport fun h => by have := (hsupp h).2; linarith,
        image_eq_zero_of_notMem_tsupport fun h => by have := (hsupp h).1; linarith⟩
    simp_rw [fun t => re_weilFullFunctional_withWeight lam hn₀ t hN]
    exact isClosed_le continuous_const (continuous_const.sub
      (((continuous_id.sub continuous_const).div_const _).mul continuous_const))
  · obtain ⟨L, U, hLU⟩ := calibration_coord_bounded hn₀ hc
    refine ⟨L, U, fun t ht => ?_⟩
    have := hLU _ ht
    simpa [withWeight] using this

end GaloisForLFunctions.FrustratedArithmeticDirichletForms
