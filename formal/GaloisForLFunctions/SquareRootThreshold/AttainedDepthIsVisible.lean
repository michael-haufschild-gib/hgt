import GaloisForLFunctions.SquareRootThreshold.HodgeClassificationOfFiniteOffLineSets

/-!
# An attained maximal depth is always visible

Let a tempered configuration have zeros right of the critical line, possibly infinitely many, and
let the largest real part `½ + D` be attained at `t₀`. Then the configuration is visible: some
compactly supported `C²` test has `Re W(f, f) < 0`. No depth gap and no finiteness are needed.

* **Splitting** (`lagStructure_split_right`). The lag structure of a bump is its on-line part plus
  the absolutely convergent sum of pair terms over the zeros right of the line.
* **Lag criterion** (`rightZeros_lagStructure_gt`). If
  `|Σ_t q_t e^{δ_t v} e^{iγ_t v}| > 2M_b + 3Σ_t |q_t|`, the two-point minor fails at lag `v`.
* **Abel–Cesàro extraction** (`attainedDepth_visible`). If the configuration were invisible, the
  sum above would stay bounded for `v ≥ 0`. Normalize it by `e^{−(D + iγ₀)v}` along a grid
  `v = kℓ`; the result is `Σ_t q_t w_t^k` with `|w_t| = e^{(δ_t − D)ℓ} ≤ 1`, and it tends to `0`.
  The Cesàro means of `w_t^k` tend to `1` if `w_t = 1` and to `0` otherwise. For a grid avoiding
  the countably many resonances `e^{i(γ_t − γ₀)ℓ} = 1`, the only `w_t = 1` is `w_{t₀}`. Dominated
  convergence then gives `q_{t₀} = 0`, which fails for `κ` modulated to the height `γ₀` of `t₀`.

The argument is elementary: Cesàro means and dominated convergence, no complex analysis. For `ξ`,
`RHTower.exists_pow_integerLag_gt_of_attainedTop` draws the same boundary for the global lag
function. Without an attained maximum the residue at a top pole is extracted by a Laplace
transform instead (`eq_zero_of_norm_tsum_exp_le`, `offLine_visible`).
-/

open MeasureTheory Complex Set Filter Topology
open scoped Real ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.SquareRootThreshold

open Zeta23 _root_.RHTower

/-- The zeros right of the critical line. -/
def rightZeros (Z : ZeroConfig) : Set ℂ := {z | z ∈ Z.carrier ∧ 1 / 2 < z.re}

theorem reflect_mem_iff (Z : ZeroConfig) (z : ℂ) : reflect z ∈ Z.carrier ↔ z ∈ Z.carrier :=
  ⟨fun h => Zeta23.reflect_reflect z ▸ Z.reflect_mem _ h, Z.reflect_mem z⟩

/-- A configuration is countable: each unit window of heights holds finitely many zeros. -/
theorem carrier_countable (Z : ZeroConfig) : Z.carrier.Countable := by
  refine (Set.countable_iUnion fun n : ℤ => (Z.finite_window n (n + 1)).countable).mono
    fun z hz => ?_
  rw [Set.mem_iUnion]
  refine ⟨⌈z.im⌉ - 1, hz, ?_, ?_⟩
  · push_cast; linarith [Int.ceil_lt_add_one z.im]
  · push_cast; linarith [Int.le_ceil z.im]

theorem summable_indicator_of_subset {s t : Set ℂ} (hst : s ⊆ t) {f : ℂ → ℂ}
    (h : Summable (t.indicator f)) : Summable (s.indicator f) :=
  Summable.of_norm_bounded h.norm fun z => by
    by_cases hz : z ∈ s
    · rw [Set.indicator_of_mem hz, Set.indicator_of_mem (hst hz)]
    · rw [Set.indicator_of_notMem hz, norm_zero]; exact norm_nonneg _

/-- A lag summand as weight, growth and phase. -/
theorem lagTerm_eq_weight {b : ℝ → ℂ} (hb : Continuous b) (hbc : HasCompactSupport b)
    (Z : ZeroConfig) (t : ℂ) (v : ℝ) :
    lagTerm Z b v t =
      offLineWeight b (Z.mult t) t * (Real.exp ((t.re - 1 / 2) * v) : ℂ) * cexp (I * t.im * v) := by
  obtain ⟨h1, -⟩ := pair_summand hb hbc t.im (t.re - 1 / 2) v
  rw [← eq_heightPoint t] at h1
  have hI : I * I = -1 := Complex.I_mul_I
  have hexp : cexp (I * ((t.im : ℂ) - I * ((t.re - 1 / 2 : ℝ) : ℂ)) * (v : ℂ)) =
      cexp (((t.re - 1 / 2) * v : ℝ)) * cexp (I * t.im * v) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    linear_combination (-(((t.re : ℂ) - 1 / 2) * (v : ℂ))) * hI
  rw [lagTerm, mul_assoc, h1, hexp, offLineWeight, Complex.ofReal_exp]
  ring

/-- **Splitting the lag structure.** It is the on-line part plus the absolutely convergent sum of
pair terms over the zeros right of the line. -/
theorem lagStructure_split_right (Z : ZeroConfig) (hZ : TemperedConfig Z) {b : ℝ → ℂ}
    (hb : ContDiff ℝ 2 b) {w : ℝ} (hbs : ∀ u, b u ≠ 0 → |u| ≤ w) (v : ℝ) :
    Summable (fun t : rightZeros Z => lagTerm Z b v t + lagTerm Z b v (reflect t)) ∧
    lagStructure Z b v = (∑' ρ : Z.carrier, if (ρ : ℂ).re = 1 / 2 then lagTerm Z b v ρ else 0) +
      ∑' t : rightZeros Z, (lagTerm Z b v t + lagTerm Z b v (reflect t)) := by
  set f := lagTerm Z b v with hf
  have hF : Summable (Z.carrier.indicator f) :=
    summable_subtype_iff_indicator.mp (summable_lagStructure Z hZ hb hbs v)
  set On : Set ℂ := {z | z ∈ Z.carrier ∧ z.re = 1 / 2} with hOn_def
  set Lt : Set ℂ := {z | z ∈ Z.carrier ∧ z.re < 1 / 2} with hLt_def
  have hOn : Summable (On.indicator f) := summable_indicator_of_subset (fun z hz => hz.1) hF
  have hR : Summable ((rightZeros Z).indicator f) :=
    summable_indicator_of_subset (fun z hz => hz.1) hF
  have hL : Summable (Lt.indicator f) := summable_indicator_of_subset (fun z hz => hz.1) hF
  set e := Function.Involutive.toPerm reflect Zeta23.reflect_reflect with he
  have hre : ∀ z : ℂ, (reflect z).re = 1 - z.re := fun z => by simp [reflect]
  have hrefl : ∀ z, Lt.indicator f (e z) = (rightZeros Z).indicator (fun t => f (reflect t)) z := by
    intro z
    have hiff : e z ∈ Lt ↔ z ∈ rightZeros Z := by
      simp only [he, Function.Involutive.coe_toPerm, hLt_def, rightZeros, Set.mem_setOf_eq,
        reflect_mem_iff, hre]
      constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1, by linarith⟩
    by_cases hz : z ∈ rightZeros Z
    · rw [Set.indicator_of_mem (hiff.mpr hz), Set.indicator_of_mem hz]
      rfl
    · rw [Set.indicator_of_notMem (mt hiff.mp hz), Set.indicator_of_notMem hz]
  have hR' : Summable ((rightZeros Z).indicator fun t => f (reflect t)) := by
    rw [← funext hrefl]
    exact (e.summable_iff (f := Lt.indicator f)).mpr hL
  have hLR : ∑' z, Lt.indicator f z = ∑' z, (rightZeros Z).indicator (fun t => f (reflect t)) z := by
    rw [← Equiv.tsum_eq e]
    exact tsum_congr hrefl
  have hsum : Summable ((rightZeros Z).indicator fun t => f t + f (reflect t)) := by
    rw [Set.indicator_add]
    exact hR.add hR'
  refine ⟨summable_subtype_iff_indicator.mpr hsum, ?_⟩
  have hdec : ∀ z, Z.carrier.indicator f z =
      On.indicator f z + ((rightZeros Z).indicator f z + Lt.indicator f z) := by
    intro z
    by_cases hz : z ∈ Z.carrier
    · rcases lt_trichotomy z.re (1 / 2) with h | h | h
      · rw [Set.indicator_of_mem hz, Set.indicator_of_notMem (fun h' => by linarith [h'.2]),
          Set.indicator_of_notMem (fun h' => by linarith [h'.2]),
          Set.indicator_of_mem (show z ∈ Lt from ⟨hz, h⟩)]
        ring
      · rw [Set.indicator_of_mem hz, Set.indicator_of_mem (show z ∈ On from ⟨hz, h⟩),
          Set.indicator_of_notMem (fun h' => by linarith [h'.2]),
          Set.indicator_of_notMem (fun h' => by linarith [h'.2])]
        ring
      · rw [Set.indicator_of_mem hz, Set.indicator_of_notMem (fun h' => by linarith [h'.2]),
          Set.indicator_of_mem (show z ∈ rightZeros Z from ⟨hz, h⟩),
          Set.indicator_of_notMem (fun h' => by linarith [h'.2])]
        ring
    · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem (fun h' => hz h'.1),
        Set.indicator_of_notMem (fun h' => hz h'.1), Set.indicator_of_notMem (fun h' => hz h'.1)]
      ring
  have hOnEq : (∑' ρ : Z.carrier, if (ρ : ℂ).re = 1 / 2 then f ρ else 0) =
      ∑' z, On.indicator f z := by
    rw [tsum_subtype Z.carrier fun z => if z.re = 1 / 2 then f z else 0]
    refine tsum_congr fun z => ?_
    by_cases hz : z ∈ Z.carrier
    · by_cases h : z.re = 1 / 2
      · rw [Set.indicator_of_mem hz, if_pos h, Set.indicator_of_mem (show z ∈ On from ⟨hz, h⟩)]
      · rw [Set.indicator_of_mem hz, if_neg h, Set.indicator_of_notMem (fun h' => h h'.2)]
    · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem (fun h' => hz h'.1)]
  have hRt := tsum_subtype (rightZeros Z) fun t => f t + f (reflect t)
  rw [lagStructure, show (∑' ρ : Z.carrier, (Z.mult ρ : ℂ) * paperFT (EF.weilTest b b)
      (gammaOf ρ) * cexp (I * gammaOf ρ * v)) = ∑' ρ : Z.carrier, f ρ from rfl,
    tsum_subtype Z.carrier f, tsum_congr hdec, Summable.tsum_add hOn (hR.add hL),
    Summable.tsum_add hR hL, hLR, hOnEq, hRt, Set.indicator_add, Summable.tsum_add hR hR']

/-- **Two-sided bounds for the minor.** With `q_t` the pair weights, `A(v) = Σ_t q_t e^{δ_t v} e^{iγ_t v}`
over the zeros right of the line and `M_b` the on-line mass, for `v ≥ 0`:
`2|A(v)| − 2Σ|q_t| − 2M_b ≤ |S(v) + conj S(−v)| ≤ 2|A(v)| + 2Σ|q_t| + 2M_b` and
`|Re S(0) − M_b| ≤ 2Σ|q_t|`. -/
theorem rightZeros_minor_bounds (Z : ZeroConfig) (hZ : TemperedConfig Z) {b : ℝ → ℂ}
    (hb : ContDiff ℝ 2 b) {w : ℝ} (hbs : ∀ u, b u ≠ 0 → |u| ≤ w) {v : ℝ} (hv : 0 ≤ v) :
    2 * ‖∑' t : rightZeros Z, offLineWeight b (Z.mult t) t *
        (Real.exp (((t : ℂ).re - 1 / 2) * v) : ℂ) * cexp (I * (t : ℂ).im * v)‖ -
        2 * ∑' t : rightZeros Z, ‖offLineWeight b (Z.mult t) t‖ - 2 * onLineMassOf Z b ≤
      ‖lagStructure Z b v + conj (lagStructure Z b (-v))‖ ∧
    ‖lagStructure Z b v + conj (lagStructure Z b (-v))‖ ≤
      2 * ‖∑' t : rightZeros Z, offLineWeight b (Z.mult t) t *
        (Real.exp (((t : ℂ).re - 1 / 2) * v) : ℂ) * cexp (I * (t : ℂ).im * v)‖ +
        2 * ∑' t : rightZeros Z, ‖offLineWeight b (Z.mult t) t‖ + 2 * onLineMassOf Z b ∧
    |(lagStructure Z b 0).re - onLineMassOf Z b| ≤
      2 * ∑' t : rightZeros Z, ‖offLineWeight b (Z.mult t) t‖ := by
  have hbc : HasCompactSupport b := hasCompactSupport_of_support_subset_abs hbs
  obtain ⟨hon, hon0⟩ := onLinePart_bounds Z hZ hb hbs v
  set q : ℂ → ℂ := fun t => offLineWeight b (Z.mult t) t with hq
  have hlag : ∀ (v : ℝ) (t : ℂ), lagTerm Z b v t =
      q t * (Real.exp ((t.re - 1 / 2) * v) : ℂ) * cexp (I * t.im * v) :=
    fun v t => lagTerm_eq_weight hb.continuous hbc Z t v
  have hsumR : ∀ v, Summable fun t : rightZeros Z => lagTerm Z b v t := by
    intro v
    have hF : Summable (Z.carrier.indicator (lagTerm Z b v)) :=
      summable_subtype_iff_indicator.mp (summable_lagStructure Z hZ hb hbs v)
    exact summable_subtype_iff_indicator.mpr (summable_indicator_of_subset (fun z hz => hz.1) hF)
  have hqs : Summable fun t : rightZeros Z => ‖q t‖ := by
    refine (hsumR 0).norm.congr fun t => ?_
    rw [hlag, norm_mul, norm_mul]
    simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, Real.exp_zero, Complex.ofReal_one,
      norm_one, mul_one]
  have hE : ∀ t : ℂ, ‖cexp (I * t.im * v)‖ = 1 := fun t => by
    rw [show I * (t.im : ℂ) * (v : ℂ) = ((t.im * v : ℝ) : ℂ) * I by push_cast; ring]
    exact Complex.norm_exp_ofReal_mul_I _
  set Af : rightZeros Z → ℂ := fun t =>
    q t * (Real.exp (((t : ℂ).re - 1 / 2) * v) : ℂ) * cexp (I * (t : ℂ).im * v) with hAf
  set Bf : rightZeros Z → ℂ := fun t => 2 * cexp (I * (t : ℂ).im * v) *
    (conj (q t) * (Real.exp (-(((t : ℂ).re - 1 / 2) * v)) : ℂ)) with hBf
  have hAs : Summable Af := (hsumR v).congr fun t => hlag v t
  have hBb : ∀ t, ‖Bf t‖ ≤ 2 * ‖q t‖ := fun t => by
    have hδ : 0 ≤ (t : ℂ).re - 1 / 2 := by linarith [t.2.2]
    have hle : Real.exp (-(((t : ℂ).re - 1 / 2) * v)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by nlinarith)
    rw [hBf, norm_mul, norm_mul, norm_mul, Complex.norm_two, hE, Complex.norm_conj,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    nlinarith [norm_nonneg (q t)]
  have hBs : Summable Bf := Summable.of_norm_bounded (hqs.mul_left 2) hBb
  obtain ⟨hPs, hSv⟩ := lagStructure_split_right Z hZ hb hbs v
  obtain ⟨hPs', hSv'⟩ := lagStructure_split_right Z hZ hb hbs (-v)
  obtain ⟨hPs0, hS0⟩ := lagStructure_split_right Z hZ hb hbs 0
  have hPc : Summable fun t : rightZeros Z =>
      conj (lagTerm Z b (-v) t + lagTerm Z b (-v) (reflect t)) :=
    hPs'.map (starRingEnd ℂ).toAddMonoidHom Complex.continuous_conj
  set C := (∑' ρ : Z.carrier, if (ρ : ℂ).re = 1 / 2 then lagTerm Z b v ρ else 0) +
    conj (∑' ρ : Z.carrier, if (ρ : ℂ).re = 1 / 2 then lagTerm Z b (-v) ρ else 0) with hC
  have hX : lagStructure Z b v + conj (lagStructure Z b (-v)) =
      C + (2 * ∑' t, Af t + ∑' t, Bf t) := by
    have hcP : conj (∑' t : rightZeros Z, (lagTerm Z b (-v) t + lagTerm Z b (-v) (reflect t))) =
        ∑' t : rightZeros Z, conj (lagTerm Z b (-v) t + lagTerm Z b (-v) (reflect t)) :=
      Complex.conj_tsum _
    rw [hSv, hSv', map_add, hcP,
      show ∀ A B C D : ℂ, (A + B) + (C + D) = (A + C) + (B + D) from fun _ _ _ _ => by ring,
      ← Summable.tsum_add hPs hPc, ← tsum_mul_left, ← Summable.tsum_add (hAs.mul_left 2) hBs]
    congr 1
    refine tsum_congr fun t => ?_
    rw [(pair_lagTerm hb.continuous hbc Z t.2.1 v).1, hAf, hBf]
    ring
  have hre0 : (lagStructure Z b 0).re = onLineMassOf Z b + ∑' t : rightZeros Z, 2 * (q t).re := by
    rw [hS0, Complex.add_re, hon0, Complex.re_tsum hPs0]
    congr 1
    refine tsum_congr fun t => ?_
    rw [(pair_lagTerm hb.continuous hbc Z t.2.1 0).2, Complex.add_re, Complex.conj_re]
    ring
  have h2re : ∑' t : rightZeros Z, 2 * (q t).re ≤ 2 * ∑' t : rightZeros Z, ‖q t‖ := by
    rw [← tsum_mul_left]
    refine Summable.tsum_le_tsum (fun t => by linarith [Complex.re_le_norm (q t)]) ?_
      (hqs.mul_left 2)
    exact Summable.of_norm_bounded (hqs.mul_left 2) fun t => by
      rw [Real.norm_eq_abs, abs_mul, abs_two]
      nlinarith [Complex.abs_re_le_norm (q t)]
  have hBn : ‖∑' t, Bf t‖ ≤ 2 * ∑' t : rightZeros Z, ‖q t‖ := by
    refine (norm_tsum_le_tsum_norm hBs.norm).trans ?_
    rw [← tsum_mul_left]
    exact Summable.tsum_le_tsum hBb hBs.norm (hqs.mul_left 2)
  have hm2re : -(2 * ∑' t : rightZeros Z, ‖q t‖) ≤ ∑' t : rightZeros Z, 2 * (q t).re := by
    rw [← tsum_mul_left, ← tsum_neg]
    refine Summable.tsum_le_tsum (fun t => by linarith [(abs_le.mp (Complex.abs_re_le_norm (q t))).1]) ?_ ?_
    · exact ((hqs.mul_left 2).neg)
    · exact Summable.of_norm_bounded (hqs.mul_left 2) fun t => by
        rw [Real.norm_eq_abs, abs_mul, abs_two]
        nlinarith [Complex.abs_re_le_norm (q t)]
  have hAeq : ‖∑' t : rightZeros Z, offLineWeight b (Z.mult t) t *
      (Real.exp (((t : ℂ).re - 1 / 2) * v) : ℂ) * cexp (I * (t : ℂ).im * v)‖ = ‖∑' t, Af t‖ := rfl
  have hQeq : ∑' t : rightZeros Z, ‖offLineWeight b (Z.mult t) t‖ = ∑' t : rightZeros Z, ‖q t‖ := rfl
  rw [hAeq, hQeq, hX, hre0]
  refine ⟨?_, ?_, ?_⟩
  · have h1 := norm_sub_le (2 * ∑' t, Af t + ∑' t, Bf t) (∑' t, Bf t)
    rw [add_sub_cancel_right, norm_mul, Complex.norm_two] at h1
    have h2 := norm_sub_le (C + (2 * ∑' t, Af t + ∑' t, Bf t)) C
    rw [add_sub_cancel_left] at h2
    linarith
  · have h1 := norm_add_le C (2 * ∑' t, Af t + ∑' t, Bf t)
    have h2 := norm_add_le (2 * ∑' t, Af t) (∑' t, Bf t)
    rw [norm_mul, Complex.norm_two] at h2
    linarith
  · rw [add_sub_cancel_left, abs_le]
    exact ⟨hm2re, h2re⟩

/-- **Lag criterion for the zeros right of the line.** If
`|Σ_t q_t e^{δ_t v} e^{iγ_t v}| > 2M_b + 3Σ_t |q_t|`, the two-point minor fails at lag `v`. -/
theorem rightZeros_lagStructure_gt (Z : ZeroConfig) (hZ : TemperedConfig Z) {b : ℝ → ℂ}
    (hb : ContDiff ℝ 2 b) {w : ℝ} (hbs : ∀ u, b u ≠ 0 → |u| ≤ w) {v : ℝ} (hv : 0 ≤ v)
    (hvis : 2 * onLineMassOf Z b + 3 * ∑' t : rightZeros Z, ‖offLineWeight b (Z.mult t) t‖ <
      ‖∑' t : rightZeros Z, offLineWeight b (Z.mult t) t *
        (Real.exp (((t : ℂ).re - 1 / 2) * v) : ℂ) * cexp (I * (t : ℂ).im * v)‖) :
    2 * (lagStructure Z b 0).re < ‖lagStructure Z b v + conj (lagStructure Z b (-v))‖ := by
  obtain ⟨h1, -, h3⟩ := rightZeros_minor_bounds Z hZ hb hbs hv
  have := (abs_le.mp h3).2
  linarith

/-- The Cesàro means of the powers of `w`, `|w| ≤ 1`, have norm at most `1`. -/
theorem norm_geom_mean_le {w : ℂ} (hw : ‖w‖ ≤ 1) (N : ℕ) :
    ‖(N : ℂ)⁻¹ * ∑ k ∈ Finset.range N, w ^ k‖ ≤ 1 := by
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  have h : ‖∑ k ∈ Finset.range N, w ^ k‖ ≤ N := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ k ∈ Finset.range N, ‖w ^ k‖ ≤ ∑ _k ∈ Finset.range N, (1 : ℝ) :=
          Finset.sum_le_sum fun k _ => by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hw
      _ = N := by simp
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  · rw [inv_mul_le_iff₀ (by exact_mod_cast hN)]
    linarith

/-- For `|w| ≤ 1`, `w ≠ 1`, the Cesàro means of the powers of `w` tend to `0`. -/
theorem tendsto_geom_mean {w : ℂ} (hw : ‖w‖ ≤ 1) (hw1 : w ≠ 1) :
    Tendsto (fun N : ℕ => (N : ℂ)⁻¹ * ∑ k ∈ Finset.range N, w ^ k) atTop (𝓝 0) := by
  have hne : 0 < ‖w - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hw1)
  refine squeeze_zero_norm (a := fun N : ℕ => 2 / ‖w - 1‖ * (N : ℝ)⁻¹) (fun N => ?_) ?_
  · rw [geom_sum_eq hw1, norm_mul, norm_inv, Complex.norm_natCast, norm_div, mul_comm]
    have h2 : ‖w ^ N - 1‖ ≤ 2 := (norm_sub_le _ _).trans (by
      rw [norm_pow, norm_one]; linarith [pow_le_one₀ (norm_nonneg w) hw (n := N)])
    gcongr
  · simpa using (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (2 / ‖w - 1‖)

/-- **An attained maximal depth is visible.** If a tempered configuration has a zero `t₀` right of
the critical line of largest real part, some compactly supported `C²` test has
`Re W(f, f) < 0`. -/
theorem attainedDepth_visible (Z : ZeroConfig) (hZ : TemperedConfig Z) {t₀ : ℂ}
    (ht₀ : t₀ ∈ Z.carrier) (hre : 1 / 2 < t₀.re) (htop : ∀ ρ ∈ Z.carrier, ρ.re ≤ t₀.re) :
    ∃ f : ℝ → ℂ, ContDiff ℝ 2 f ∧ HasCompactSupport f ∧ (Z.W f f).re < 0 := by
  set b := modScaledBump 1 t₀.im with hbdef
  have hb : ContDiff ℝ 2 b := (contDiff_modScaledBump 1 t₀.im).of_le (by norm_num)
  have hbs : ∀ u, b u ≠ 0 → |u| ≤ 1 := fun u hu => by
    by_contra h
    push Not at h
    exact hu (modScaledBump_eq_zero one_pos h.le)
  have hbc : HasCompactSupport b := hasCompactSupport_of_support_subset_abs hbs
  by_contra hcon
  push Not at hcon
  set q : ℂ → ℂ := fun t => offLineWeight b (Z.mult t) t with hq
  set D := t₀.re - 1 / 2 with hD
  have hD0 : 0 < D := by rw [hD]; linarith
  set γ₀ := t₀.im with hγ₀
  set T₀ : rightZeros Z := ⟨t₀, ht₀, hre⟩ with hT₀
  have hq₀ : q t₀ ≠ 0 := by
    have hm := Z.one_le_mult t₀ ht₀
    exact mul_ne_zero (Nat.cast_ne_zero.mpr (by omega)) (pairWeight_modScaledBump_ne_zero one_pos _ _)
  set K := 2 * onLineMassOf Z b + 3 * ∑' t : rightZeros Z, ‖q t‖ with hK
  -- invisibility bounds the off-line exponential sum at every lag `v ≥ 0`
  have hbound : ∀ v : ℝ, 0 ≤ v → ‖∑' t : rightZeros Z, q t *
      (Real.exp (((t : ℂ).re - 1 / 2) * v) : ℂ) * cexp (I * (t : ℂ).im * v)‖ ≤ K := by
    intro v hv
    by_contra hlt
    push Not at hlt
    obtain ⟨f, hf, hfs, hneg⟩ := exists_visible_of_lagStructure Z hZ hb hbs hv
      (rightZeros_lagStructure_gt Z hZ hb hbs hv hlt)
    exact absurd (hcon f hf (isCompact_Icc.of_isClosed_subset (isClosed_tsupport f) hfs))
      (not_le.mpr hneg)
  -- a grid avoiding the resonances `e^{i(γ_t − γ₀)ℓ} = 1`
  set Bad : Set ℝ := ⋃ t ∈ rightZeros Z, Set.range fun n : ℤ => 2 * π * n / (t.im - γ₀) with hBad
  have hBadc : Bad.Countable :=
    ((carrier_countable Z).mono fun z hz => hz.1).biUnion fun t _ => Set.countable_range _
  obtain ⟨ℓ, ⟨hℓ0, -⟩, hℓB⟩ : (Set.Ioo (0 : ℝ) 1 \ Bad).Nonempty := by
    apply MeasureTheory.nonempty_of_measure_ne_zero (μ := MeasureTheory.volume)
    rw [MeasureTheory.measure_sdiff_null (hBadc.measure_zero _), Real.volume_Ioo]
    norm_num
  -- the nodes `w_t = e^{((δ_t − D) + i(γ_t − γ₀))ℓ}`
  set wt : rightZeros Z → ℂ := fun t =>
    cexp ((((t : ℂ).re - 1 / 2 - D : ℝ) + I * ((t : ℂ).im - γ₀ : ℝ)) * ℓ) with hwt
  have hwn : ∀ t, ‖wt t‖ ≤ 1 := fun t => by
    rw [hwt, Complex.norm_exp]
    have : ((((t : ℂ).re - 1 / 2 - D : ℝ) + I * ((t : ℂ).im - γ₀ : ℝ)) * (ℓ : ℂ)).re =
        ((t : ℂ).re - 1 / 2 - D) * ℓ := by simp
    rw [this, Real.exp_le_one_iff]
    have := htop t t.2.1
    nlinarith
  have hw₀ : wt T₀ = 1 := by
    rw [hwt]
    simp [hT₀, hD, hγ₀]
  have hw1 : ∀ t, wt t = 1 → t = T₀ := by
    intro t ht
    have hn : ‖wt t‖ = 1 := by rw [ht, norm_one]
    rw [hwt, Complex.norm_exp] at hn
    have hreq : (t : ℂ).re = t₀.re := by
      have h0 : ((((t : ℂ).re - 1 / 2 - D : ℝ) + I * ((t : ℂ).im - γ₀ : ℝ)) * (ℓ : ℂ)).re = 0 := by
        rw [← Real.exp_eq_one_iff]; exact hn
      simp at h0
      rcases h0 with h0 | h0
      · rw [hD] at h0; linarith
      · linarith
    have hph : cexp (I * (((t : ℂ).im - γ₀ : ℝ) * ℓ : ℝ)) = 1 := by
      rw [← ht, hwt]
      congr 1
      rw [show (t : ℂ).re - 1 / 2 - D = 0 by rw [hD]; linarith]
      push_cast
      ring
    obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp hph
    have hreal : ((t : ℂ).im - γ₀) * ℓ = 2 * π * n := by
      have h0 : I * (((((t : ℂ).im - γ₀) * ℓ - 2 * π * n : ℝ)) : ℂ) = 0 := by
        push_cast
        push_cast at hn
        linear_combination hn
      rcases mul_eq_zero.mp h0 with h | h
      · exact absurd h Complex.I_ne_zero
      · exact sub_eq_zero.mp (Complex.ofReal_eq_zero.mp h)
    have him : (t : ℂ).im = γ₀ := by
      by_contra hne
      have hne' : (t : ℂ).im - γ₀ ≠ 0 := sub_ne_zero.mpr hne
      refine hℓB (Set.mem_biUnion t.2 ⟨n, ?_⟩)
      show 2 * π * n / ((t : ℂ).im - γ₀) = ℓ
      rw [← hreal]
      field_simp
    exact Subtype.ext (Complex.ext hreq him)
  -- the normalized sums along the grid
  have hsum0 : Summable fun t : rightZeros Z => lagTerm Z b 0 t := by
    have hF : Summable (Z.carrier.indicator (lagTerm Z b 0)) :=
      summable_subtype_iff_indicator.mp (summable_lagStructure Z hZ hb hbs 0)
    exact summable_subtype_iff_indicator.mpr (summable_indicator_of_subset (fun z hz => hz.1) hF)
  have hqs : Summable fun t : rightZeros Z => ‖q t‖ := by
    refine hsum0.norm.congr fun t => ?_
    rw [lagTerm_eq_weight hb.continuous hbc, norm_mul, norm_mul]
    simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, Real.exp_zero, Complex.ofReal_one,
      norm_one, mul_one]
    rfl
  have hqw : ∀ k : ℕ, Summable fun t : rightZeros Z => q t * wt t ^ k := fun k =>
    Summable.of_norm_bounded hqs fun t => by
      rw [norm_mul, norm_pow]
      exact mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) (hwn t))
  set a : ℕ → ℂ := fun k => ∑' t : rightZeros Z, q t * wt t ^ k with ha
  have ha_eq : ∀ k : ℕ, a k = cexp (-(((D : ℂ) + I * γ₀) * ((k * ℓ : ℝ) : ℂ))) *
      ∑' t : rightZeros Z, q t * (Real.exp (((t : ℂ).re - 1 / 2) * (k * ℓ)) : ℂ) *
        cexp (I * (t : ℂ).im * ((k * ℓ : ℝ) : ℂ)) := by
    intro k
    rw [ha, ← tsum_mul_left]
    refine tsum_congr fun t => ?_
    rw [hwt, ← Complex.exp_nat_mul, Complex.ofReal_exp, mul_comm (cexp _), mul_assoc, mul_assoc,
      ← Complex.exp_add, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  have ha0 : Tendsto a atTop (𝓝 0) := by
    have hlim : Tendsto (fun k : ℕ => K * Real.exp (-(D * ℓ)) ^ k) atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (Real.exp_pos _).le
        (Real.exp_lt_one_iff.mpr (by nlinarith))).const_mul K
    refine squeeze_zero_norm (fun k => ?_) hlim
    rw [ha_eq, norm_mul, Complex.norm_exp, ← Real.exp_nat_mul]
    have hre' : (-(((D : ℂ) + I * γ₀) * ((k * ℓ : ℝ) : ℂ))).re = (k : ℝ) * -(D * ℓ) := by
      simp; ring
    rw [hre', mul_comm]
    exact mul_le_mul_of_nonneg_right (hbound _ (by positivity)) (Real.exp_pos _).le
  have hc0 : Tendsto (fun N : ℕ => (N : ℂ)⁻¹ * ∑ k ∈ Finset.range N, a k) atTop (𝓝 0) := by
    have := ha0.cesaro_smul
    simp only [Complex.real_smul] at this
    simpa using this
  have hc1 : Tendsto (fun N : ℕ => (N : ℂ)⁻¹ * ∑ k ∈ Finset.range N, a k) atTop (𝓝 (q t₀)) := by
    have hrw : ∀ N : ℕ, (N : ℂ)⁻¹ * ∑ k ∈ Finset.range N, a k =
        ∑' t : rightZeros Z, q t * ((N : ℂ)⁻¹ * ∑ k ∈ Finset.range N, wt t ^ k) := by
      intro N
      rw [ha]
      simp only
      rw [← Summable.tsum_finsetSum fun k _ => hqw k, ← tsum_mul_left]
      refine tsum_congr fun t => ?_
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    simp_rw [hrw]
    have hg : (∑' t : rightZeros Z, if t = T₀ then q t₀ else 0) = q t₀ := tsum_ite_eq T₀ _
    rw [← hg]
    refine tendsto_tsum_of_dominated_convergence hqs (fun t => ?_) (Eventually.of_forall
      fun N t => ?_)
    · by_cases ht : t = T₀
      · rw [if_pos ht]
        have hwt1 : wt t = 1 := ht ▸ hw₀
        have : ∀ᶠ N : ℕ in atTop, q t * ((N : ℂ)⁻¹ * ∑ k ∈ Finset.range N, wt t ^ k) = q t₀ := by
          filter_upwards [eventually_ge_atTop 1] with N hN
          rw [hwt1]
          simp only [one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
          rw [inv_mul_cancel₀ (by exact_mod_cast (show N ≠ 0 by omega)), mul_one, ht]
        exact tendsto_const_nhds.congr' (this.mono fun N h => h.symm)
      · rw [if_neg ht]
        have hw1' : wt t ≠ 1 := fun h => ht (hw1 t h)
        simpa using (tendsto_geom_mean (hwn t) hw1').const_mul (q t)
    · rw [norm_mul]
      exact mul_le_of_le_one_right (norm_nonneg _) (norm_geom_mean_le (hwn t) N)
  exact hq₀ (tendsto_nhds_unique hc1 hc0)

end GaloisForLFunctions.SquareRootThreshold
