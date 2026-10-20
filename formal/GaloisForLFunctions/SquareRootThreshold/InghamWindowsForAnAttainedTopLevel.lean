import GaloisForLFunctions.SquareRootThreshold.DepthDeficitTransformReplacesTheGap
import GaloisForLFunctions.SquareRootThreshold.InghamInequalityForSeparatedSpectra

/-!
# An attained top level is seen in every Ingham window

Let `t₀` be a zero right of the critical line with pair weight `q_{t₀} ≠ 0` and with the largest
real part `½ + D` among the zeros of nonzero weight. The top level `Re t = Re t₀` may hold
infinitely many zeros, and the levels below may accumulate at it.

* **Ingham windows** (`exists_ingham_window_lower`). If the heights of a finite set `F ∋ t₀` are
  pairwise at least `g` apart, every interval of length `4π/g` contains a lag with
  `|Σ_{t ∈ F} q_t e^{iγ_t v}| ≥ |q_{t₀}|/2`. On `[−T, T]`, `T = 2π/g`, Ingham's constant is at
  least `6/g` (`inghamConst_two_pi_div_ge`), while a sum below `|q_{t₀}|/2` throughout has mean
  square at most `(π/g)|q_{t₀}|²`.
* **Explicit visibility** (`exists_minor_fails_of_ingham`). Suppose that the level weight outside
  `F` and the depth-deficit transform `G(V)` are both at most `|q_{t₀}|/8`, and that
  `2M_b + 3Σ|q_t| < (|q_{t₀}|/4) e^{DV}`. Then the two-point minor fails at a lag in
  `[V, V + 4π/g]`.
* **Every attained top level** (`eventually_minor_fails_in_every_ingham_window`). Finitely many
  zeros carry all but `|q_{t₀}|/8` of the level weight (`exists_levelTail_le`), and finitely many
  points on one level have separated heights (`exists_height_sep_of_level`). Hence, beyond some
  lag, the minor fails in every window of length `4π/g`, whether the top level is finite or not.

The floor and the window are explicit, and the top level need not be finite.
-/

open MeasureTheory Complex Set Filter Topology
open scoped Real ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.SquareRootThreshold

open Zeta23 _root_.RHTower

/-- At the window `T = 2π/g` the Ingham constant is at least `6/g`. -/
theorem inghamConst_two_pi_div_ge {g : ℝ} (hg : 0 < g) : 6 / g ≤ inghamConst (2 * π / g) g := by
  have hpos : ∀ n : ℕ, 0 < 4 * ((n : ℝ) + 1) ^ 2 - 1 := fun n => by
    nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hterm : ∀ n : ℕ, (2 : ℝ) / (4 ^ 2 * ((n : ℝ) + 1) ^ 2 - 1) ≤
      1 / 4 * (2 / (4 * ((n : ℝ) + 1) ^ 2 - 1)) := fun n => by
    calc (2 : ℝ) / (4 ^ 2 * ((n : ℝ) + 1) ^ 2 - 1) ≤ 2 / (4 * (4 * ((n : ℝ) + 1) ^ 2 - 1)) :=
          div_le_div_of_nonneg_left (by norm_num) (mul_pos four_pos (hpos n)) (by nlinarith)
      _ = 1 / 4 * (2 / (4 * ((n : ℝ) + 1) ^ 2 - 1)) := by field_simp
  have hS := hasSum_two_div_four_sq_sub_one
  have hs : Summable fun n : ℕ => (2 : ℝ) / (4 ^ 2 * ((n : ℝ) + 1) ^ 2 - 1) :=
    Summable.of_nonneg_of_le (fun n => (div_pos two_pos (by nlinarith [hpos n])).le) hterm
      (hS.summable.mul_left _)
  have hle : ∑' n : ℕ, (2 : ℝ) / (4 ^ 2 * ((n : ℝ) + 1) ^ 2 - 1) ≤ 1 / 4 :=
    (Summable.tsum_le_tsum hterm hs (hS.summable.mul_left _)).trans
      (by rw [tsum_mul_left, hS.tsum_eq]; norm_num)
  have hb : 2 * (2 * π / g) * g / π = 4 := by field_simp; ring
  have e : 4 * (2 * π / g) / π = 8 / g := by field_simp; ring
  unfold inghamConst
  rw [hb, e]
  calc 6 / g = 8 / g * (3 / 4) := by ring
    _ ≤ 8 / g * (1 - ∑' n : ℕ, (2 : ℝ) / (4 ^ 2 * ((n : ℝ) + 1) ^ 2 - 1)) := by
        gcongr
        linarith

/-- **A level is seen in every Ingham window.** Let the heights of a finite set `F` be pairwise
at least `g > 0` apart and let `t₀ ∈ F`. Every interval `[V, V + 4π/g]` contains a lag `v` with
`|Σ_{t ∈ F} q_t e^{iγ_t v}| ≥ |q_{t₀}|/2`. -/
theorem exists_ingham_window_lower {F : Finset ℂ} {g : ℝ} (hg : 0 < g)
    (hsep : ∀ t ∈ F, ∀ s ∈ F, t ≠ s → g ≤ |t.im - s.im|) (q : ℂ → ℂ) {t₀ : ℂ} (ht₀ : t₀ ∈ F)
    (V : ℝ) :
    ∃ v : ℝ, V ≤ v ∧ v ≤ V + 4 * π / g ∧
      ‖q t₀‖ / 2 ≤ ‖∑ t ∈ F, q t * cexp (I * t.im * v)‖ := by
  set T := 2 * π / g with hTdef
  have hT : 0 < T := by positivity
  have hTg : π < T * g := by rw [hTdef, div_mul_cancel₀ _ hg.ne']; linarith [Real.pi_pos]
  have h2T : V + T + T = V + 4 * π / g := by rw [hTdef]; ring
  set s := V + T with hs
  set c : F → ℂ := fun r => q r * cexp (I * (r : ℂ).im * s) with hc
  have hI := ingham_inequality (fun r : F => (r : ℂ).im) c hg hT hTg
    fun j l hjl => hsep _ j.2 _ l.2 fun h => hjl (Subtype.ext h)
  have hnc : ∀ r : F, ‖c r‖ = ‖q r‖ := fun r => by
    rw [hc, norm_mul, show I * (((r : ℂ).im : ℝ) : ℂ) * (s : ℂ) = (((r : ℂ).im * s : ℝ) : ℂ) * I by
      push_cast; ring, Complex.norm_exp_ofReal_mul_I, mul_one]
  have hsq : ‖q t₀‖ ^ 2 ≤ ∑ r : F, ‖c r‖ ^ 2 := by
    have := Finset.single_le_sum (f := fun r : F => ‖c r‖ ^ 2) (fun _ _ => sq_nonneg _)
      (Finset.mem_univ ⟨t₀, ht₀⟩)
    simpa [hnc] using this
  have hP : ∀ x : ℝ, ∑ r : F, c r * cexp (I * (r : ℂ).im * x) =
      ∑ t ∈ F, q t * cexp (I * t.im * ((s + x : ℝ) : ℂ)) := fun x => by
    rw [← Finset.sum_coe_sort F]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [hc, mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  by_contra hcon
  push Not at hcon
  have hq0 : 0 < ‖q t₀‖ := by
    by_contra h
    have := hcon V le_rfl (by linarith [show 0 < 4 * π / g by positivity])
    linarith [norm_nonneg (∑ t ∈ F, q t * cexp (I * t.im * V)), norm_nonneg (q t₀)]
  have hlow : ∀ x ∈ Icc (-T) T,
      ‖∑ r : F, c r * cexp (I * (r : ℂ).im * x)‖ ^ 2 ≤ (‖q t₀‖ / 2) ^ 2 := fun x hx => by
    rw [hP]
    exact pow_le_pow_left₀ (norm_nonneg _)
      (hcon (s + x) (by rw [hs]; linarith [hx.1]) (by rw [← h2T, hs]; linarith [hx.2])).le 2
  have hcont : Continuous fun x : ℝ => ‖∑ r : F, c r * cexp (I * (r : ℂ).im * x)‖ ^ 2 := by
    fun_prop
  have hint := intervalIntegral.integral_mono_on (μ := volume) (by linarith : -T ≤ T)
    (hcont.intervalIntegrable _ _) (continuous_const.intervalIntegrable _ _) hlow
  rw [intervalIntegral.integral_const, smul_eq_mul] at hint
  have hC := inghamConst_two_pi_div_ge hg
  have hCpos : 0 ≤ inghamConst T g := (div_pos (by norm_num) hg).le.trans hC
  have h1 : 6 / g * ‖q t₀‖ ^ 2 ≤ inghamConst T g * ∑ r : F, ‖c r‖ ^ 2 :=
    mul_le_mul hC hsq (sq_nonneg _) hCpos
  have h2 : (T - -T) * (‖q t₀‖ / 2) ^ 2 = π / g * ‖q t₀‖ ^ 2 := by rw [hTdef]; ring
  have h3 : π / g * ‖q t₀‖ ^ 2 < 6 / g * ‖q t₀‖ ^ 2 :=
    mul_lt_mul_of_pos_right (div_lt_div_of_pos_right (by linarith [Real.pi_lt_four]) hg)
      (by positivity)
  linarith

/-- **Explicit visibility of an attained top level.** Let every zero of nonzero weight satisfy
`Re t ≤ Re t₀ = ½ + D`, and let `F ∋ t₀` be a finite set of zeros on the top level with heights
pairwise at least `g > 0` apart. If the level weight outside `F` and `G(V)` are at most
`|q_{t₀}|/8` and `2M_b + 3Σ|q_t| < (|q_{t₀}|/4) e^{DV}`, `V ≥ 0`, the two-point minor fails at a
lag in `[V, V + 4π/g]`. -/
theorem exists_minor_fails_of_ingham (Z : ZeroConfig) (hZ : TemperedConfig Z) {b : ℝ → ℂ}
    (hb : ContDiff ℝ 2 b) {w : ℝ} (hbs : ∀ u, b u ≠ 0 → |u| ≤ w) {t₀ : ℂ}
    (ht₀ : t₀ ∈ rightZeros Z)
    (htop : ∀ t ∈ rightZeros Z, offLineWeight b (Z.mult t) t ≠ 0 → t.re ≤ t₀.re)
    {F : Finset ℂ} (hF : ∀ t ∈ F, t ∈ rightZeros Z ∧ t.re = t₀.re) (ht₀F : t₀ ∈ F) {g : ℝ}
    (hg : 0 < g) (hsep : ∀ t ∈ F, ∀ s ∈ F, t ≠ s → g ≤ |t.im - s.im|)
    (htail : levelTail Z b t₀.re F ≤ ‖offLineWeight b (Z.mult t₀) t₀‖ / 8) {V : ℝ} (hV : 0 ≤ V)
    (hG : depthDeficit Z b t₀.re V ≤ ‖offLineWeight b (Z.mult t₀) t₀‖ / 8)
    (hM : 2 * onLineMassOf Z b + 3 * ∑' t : rightZeros Z, ‖offLineWeight b (Z.mult t) t‖ <
      ‖offLineWeight b (Z.mult t₀) t₀‖ / 4 * Real.exp ((t₀.re - 1 / 2) * V)) :
    ∃ v : ℝ, V ≤ v ∧ v ≤ V + 4 * π / g ∧
      2 * (lagStructure Z b 0).re < ‖lagStructure Z b v + conj (lagStructure Z b (-v))‖ := by
  set q : ℂ → ℂ := fun t => offLineWeight b (Z.mult t) t with hq
  obtain ⟨v, hVv, hv4, hlow⟩ := exists_ingham_window_lower hg hsep q ht₀F V
  have hv0 : 0 ≤ v := hV.trans hVv
  set D := t₀.re - 1 / 2 with hD
  have hD0 : 0 < D := by rw [hD]; linarith [ht₀.2]
  refine ⟨v, hVv, hv4, rightZeros_lagStructure_gt Z hZ hb hbs hv0 ?_⟩
  have hlev : ∑ t ∈ F, q t * (Real.exp ((t.re - 1 / 2) * v) : ℂ) * cexp (I * t.im * v) =
      (Real.exp (D * v) : ℂ) * ∑ t ∈ F, q t * cexp (I * t.im * v) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun t ht => ?_
    rw [(hF t ht).2]
    ring
  have hEv := Real.exp_pos (D * v)
  have hlevn : Real.exp (D * v) * (‖q t₀‖ / 2) ≤
      ‖∑ t ∈ F, q t * (Real.exp ((t.re - 1 / 2) * v) : ℂ) * cexp (I * t.im * v)‖ := by
    rw [hlev, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hEv]
    exact mul_le_mul_of_nonneg_left hlow hEv.le
  have hrest := norm_offLineSum_sub_level_le Z hZ hb hbs htop hF hv0
  have hGv := depthDeficit_anti Z hZ hb hbs t₀.re hV hVv
  have hrest' : Real.exp (D * v) * (levelTail Z b t₀.re F + depthDeficit Z b t₀.re v) ≤
      Real.exp (D * v) * (‖q t₀‖ / 4) :=
    mul_le_mul_of_nonneg_left (by linarith) hEv.le
  have hEV : Real.exp (D * V) * (‖q t₀‖ / 4) ≤ Real.exp (D * v) * (‖q t₀‖ / 4) :=
    mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hVv hD0.le))
      (by positivity)
  have htri := norm_sub_norm_le
    (∑ t ∈ F, q t * (Real.exp ((t.re - 1 / 2) * v) : ℂ) * cexp (I * t.im * v))
    (∑ t ∈ F, q t * (Real.exp ((t.re - 1 / 2) * v) : ℂ) * cexp (I * t.im * v) -
      ∑' t : rightZeros Z, q t * (Real.exp (((t : ℂ).re - 1 / 2) * v) : ℂ) *
        cexp (I * (t : ℂ).im * v))
  rw [sub_sub_cancel, norm_sub_rev] at htri
  linarith

/-- **Finitely many zeros carry a level up to `ε`.** For every `ε > 0` there is a finite set
`F ∋ t₀` of zeros on the level `Re t = r` whose complement in the level has weight at most `ε`. -/
theorem exists_levelTail_le (Z : ZeroConfig) (hZ : TemperedConfig Z) {b : ℝ → ℂ}
    (hb : ContDiff ℝ 2 b) {w : ℝ} (hbs : ∀ u, b u ≠ 0 → |u| ≤ w) {t₀ : ℂ}
    (ht₀ : t₀ ∈ rightZeros Z) {ε : ℝ} (hε : 0 < ε) :
    ∃ F : Finset ℂ, (∀ t ∈ F, t ∈ rightZeros Z ∧ t.re = t₀.re) ∧ t₀ ∈ F ∧
      levelTail Z b t₀.re F ≤ ε := by
  classical
  set a : rightZeros Z → ℝ := fun t =>
    if (t : ℂ).re = t₀.re then ‖offLineWeight b (Z.mult t) t‖ else 0 with ha
  have ha0 : ∀ t, 0 ≤ a t := fun t => by simp only [ha]; split_ifs <;> positivity
  have has : Summable a := Summable.of_nonneg_of_le ha0
    (fun t => by simp only [ha]; split_ifs <;> simp) (summable_norm_offLineWeight Z hZ hb hbs)
  obtain ⟨S, hS⟩ := (has.hasSum.eventually (Ioi_mem_nhds (show ∑' t, a t - ε < ∑' t, a t by
    linarith))).exists
  set F : Finset ℂ := insert t₀ ((S.filter fun t : rightZeros Z => (t : ℂ).re = t₀.re).image
    fun t : rightZeros Z => (t : ℂ))
  refine ⟨F, fun t ht => ?_, Finset.mem_insert_self _ _, ?_⟩
  · rcases Finset.mem_insert.mp ht with rfl | ht
    · exact ⟨ht₀, rfl⟩
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp ht
    exact ⟨u.2, (Finset.mem_filter.mp hu).2⟩
  have hin : Summable fun t => if t ∈ S then a t else 0 :=
    Summable.of_nonneg_of_le (fun t => by split_ifs <;> first | exact ha0 t | exact le_rfl)
      (fun t => by split_ifs <;> first | exact le_rfl | exact ha0 t) has
  have hout : Summable fun t => if t ∉ S then a t else 0 :=
    Summable.of_nonneg_of_le (fun t => by split_ifs <;> first | exact ha0 t | exact le_rfl)
      (fun t => by split_ifs <;> first | exact le_rfl | exact ha0 t) has
  have hinS : ∑' t, (if t ∈ S then a t else 0) = ∑ t ∈ S, a t := by
    rw [tsum_eq_sum (s := S) fun t ht => by simp [ht]]
    exact Finset.sum_congr rfl fun t ht => by simp [ht]
  have htot : ∑' t, a t = ∑ t ∈ S, a t + ∑' t, (if t ∉ S then a t else 0) := by
    rw [← hinS, ← hin.tsum_add hout]
    exact tsum_congr fun t => by by_cases h : t ∈ S <;> simp [h]
  have hle : levelTail Z b t₀.re F ≤ ∑' t, (if t ∉ S then a t else 0) := by
    refine Summable.tsum_le_tsum (fun t => ?_) (summable_levelTail Z hZ hb hbs t₀.re F) hout
    by_cases h1 : (t : ℂ).re = t₀.re ∧ (t : ℂ) ∉ F
    · have hS' : t ∉ S := fun hS => h1.2 (Finset.mem_insert_of_mem
        (Finset.mem_image.mpr ⟨t, Finset.mem_filter.mpr ⟨hS, h1.1⟩, rfl⟩))
      rw [if_pos h1, if_pos hS']
      simp [ha, h1.1]
    · rw [if_neg h1]
      split_ifs <;> first | exact ha0 t | exact le_rfl
  linarith

/-- Finitely many points of one level have pairwise separated heights. -/
theorem exists_height_sep_of_level {F : Finset ℂ} {r : ℝ} (hF : ∀ t ∈ F, t.re = r) :
    ∃ g : ℝ, 0 < g ∧ ∀ t ∈ F, ∀ s ∈ F, t ≠ s → g ≤ |t.im - s.im| := by
  classical
  have hne : ∀ t ∈ F, ∀ s ∈ F, t ≠ s → 0 < |t.im - s.im| := fun t ht s hs hts =>
    abs_pos.mpr (sub_ne_zero.mpr fun h => hts (Complex.ext ((hF t ht).trans (hF s hs).symm) h))
  by_cases h : F.offDiag.Nonempty
  · obtain ⟨p, hp, hmin⟩ := F.offDiag.exists_min_image (fun p => |p.1.im - p.2.im|) h
    obtain ⟨hp1, hp2, hp12⟩ := Finset.mem_offDiag.mp hp
    exact ⟨_, hne _ hp1 _ hp2 hp12, fun t ht s hs hts =>
      hmin (t, s) (Finset.mem_offDiag.mpr ⟨ht, hs, hts⟩)⟩
  · exact ⟨1, one_pos, fun t ht s hs hts =>
      absurd ⟨(t, s), Finset.mem_offDiag.mpr ⟨ht, hs, hts⟩⟩ h⟩

/-- **Every attained top level is seen in every Ingham window.** Let `t₀` be a zero right of the
line with `q_{t₀} ≠ 0` and largest real part among the zeros of nonzero weight. There are `g > 0`
and `V₀` such that every window `[V, V + 4π/g]`, `V ≥ V₀`, contains a lag at which the two-point
minor fails. -/
theorem eventually_minor_fails_in_every_ingham_window (Z : ZeroConfig) (hZ : TemperedConfig Z)
    {b : ℝ → ℂ} (hb : ContDiff ℝ 2 b) {w : ℝ} (hbs : ∀ u, b u ≠ 0 → |u| ≤ w) {t₀ : ℂ}
    (ht₀ : t₀ ∈ rightZeros Z) (hq₀ : offLineWeight b (Z.mult t₀) t₀ ≠ 0)
    (htop : ∀ t ∈ rightZeros Z, offLineWeight b (Z.mult t) t ≠ 0 → t.re ≤ t₀.re) :
    ∃ g V₀ : ℝ, 0 < g ∧ ∀ V : ℝ, V₀ ≤ V → ∃ v : ℝ, V ≤ v ∧ v ≤ V + 4 * π / g ∧
      2 * (lagStructure Z b 0).re < ‖lagStructure Z b v + conj (lagStructure Z b (-v))‖ := by
  set Q₀ := ‖offLineWeight b (Z.mult t₀) t₀‖ with hQ₀
  have hQ₀0 : 0 < Q₀ := norm_pos_iff.mpr hq₀
  obtain ⟨F, hF, ht₀F, htail⟩ := exists_levelTail_le Z hZ hb hbs ht₀ (by positivity : 0 < Q₀ / 8)
  obtain ⟨g, hg, hsep⟩ := exists_height_sep_of_level fun t ht => (hF t ht).2
  set K := 2 * onLineMassOf Z b + 3 * ∑' t : rightZeros Z, ‖offLineWeight b (Z.mult t) t‖
  have hD0 : 0 < t₀.re - 1 / 2 := by linarith [ht₀.2]
  have hG := (tendsto_depthDeficit Z hZ hb hbs t₀.re).eventually
    (ge_mem_nhds (by positivity : (0 : ℝ) < Q₀ / 8))
  have hE : ∀ᶠ V : ℝ in atTop, K < Q₀ / 4 * Real.exp ((t₀.re - 1 / 2) * V) :=
    ((Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop hD0)).const_mul_atTop
      (by positivity : (0 : ℝ) < Q₀ / 4)).eventually (eventually_gt_atTop K)
  obtain ⟨V₀, hV₀⟩ := eventually_atTop.mp (hG.and (hE.and (eventually_ge_atTop 0)))
  exact ⟨g, V₀, hg, fun V hV => exists_minor_fails_of_ingham Z hZ hb hbs ht₀ htop hF ht₀F hg hsep
    htail (hV₀ V hV).2.2 (hV₀ V hV).1 (hV₀ V hV).2.1⟩

end GaloisForLFunctions.SquareRootThreshold
