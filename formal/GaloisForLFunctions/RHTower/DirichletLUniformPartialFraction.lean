import Zeta23.WeilEF.Landau
import Zeta23.ThmE.LGrowth

/-!
# The conductor-uniform partial fraction for Dirichlet `L`-functions

For a nonprincipal character `χ` modulo `q` the function `L(s, χ)` is entire, at least `1/3` in size
on `Re s = 2`, and at most `8q(|Im s| + 3)` on `Re s ≥ 0.15`. Landau's disc lemma
(`Zeta23.WeilEF.logDeriv_partial_fraction_disk`) then expands `L'/L` around `2 + it` at every height.

* **Partial fraction at every height** (`L_logDeriv_partial_fraction_all`). On the disc of radius
  `3/2` about `2 + it`, `L'/L(s, χ) = Σ_{ρ} m_ρ/(s − ρ) + O(log(q(|t| + 3)))`, the sum over the zeros
  within distance `1.6` of `2 + it`, with an absolute implied constant.
* **Zeros count with multiplicity at least one** (`one_le_analyticOrderNatAt_LFunction`).
* **The zero-sum bound** (`neg_re_logDeriv_LFunction_le`). For `1 < σ ≤ 2` and any finite set `S` of
  zeros near `2 + it`, `−Re L'/L(σ + it, χ) ≤ C log(q(|t| + 3)) − Σ_{ρ ∈ S} Re 1/(σ + it − ρ)`. Every
  zero lies left of `Re s = 1`, so every term of the partial fraction has nonnegative real part and
  any subset of them may be kept.

These are the inputs of the classical `3-4-1` zero-free region, uniformly in the modulus.
-/

noncomputable section

open Complex Metric

namespace RHTower

variable {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}

/-- `log 3 ≤ log(q(|t| + 3))`. -/
theorem log_three_le_log_conductor (t : ℝ) : Real.log 3 ≤ Real.log ((q : ℝ) * (|t| + 3)) := by
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.pos q
  exact Real.log_le_log (by norm_num) (by nlinarith [abs_nonneg t])

/-- The absolute constant of the partial fraction. -/
def pfConst : ℝ := 44795000 / (91/50) * 5

theorem pfConst_pos : 0 < pfConst := by unfold pfConst; positivity

/-- **Partial fraction for `L'/L(s, χ)` at every height**, with the absolute constant `pfConst`. -/
theorem L_logDeriv_partial_fraction_all (hχ1 : χ ≠ 1) (t : ℝ) :
    ∃ Z : Finset ℂ,
      ((Z : Set ℂ) = {ρ ∈ closedBall (2 + t * I) (22/25 * (91/50)) | χ.LFunction ρ = 0}) ∧
      ∀ s ∈ closedBall (2 + t * I) (3/2), χ.LFunction s ≠ 0 →
        ‖logDeriv χ.LFunction s - ∑ ρ ∈ Z, (analyticOrderNatAt χ.LFunction ρ : ℂ) / (s - ρ)‖
          ≤ pfConst * Real.log ((q : ℝ) * (|t| + 3)) := by
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast NeZero.pos q
  set s₀ : ℂ := 2 + t * I with hs₀
  have hs₀re : s₀.re = 2 := by simp [hs₀]
  have hLs₀ : χ.LFunction s₀ ≠ 0 := Zeta23.ThmE.LFunction_ne_zero_of_two_le_re (by rw [hs₀re])
  have hlow : (1/3 : ℝ) ≤ ‖χ.LFunction s₀‖ := Zeta23.ThmE.LFunction_lower_bound_two (by rw [hs₀re])
  have hfa : AnalyticOnNhd ℂ χ.LFunction (closedBall s₀ (91/50)) := fun s _ =>
    (DirichletCharacter.differentiable_LFunction hχ1).analyticAt s
  set B : ℝ := 24 * (q : ℝ) * (|t| + 5) with hB
  have hB2 : 2 ≤ B := by rw [hB]; nlinarith [abs_nonneg t]
  -- The uniform growth bound on the disc, relative to the centre.
  have hfB : ∀ w ∈ closedBall s₀ (24/25 * (91/50)), ‖χ.LFunction w‖ ≤ B * ‖χ.LFunction s₀‖ := by
    intro w hw
    rw [mem_closedBall, Complex.dist_eq] at hw
    have hwre : (0.15 : ℝ) ≤ w.re := by
      have h := Complex.abs_re_le_norm (w - s₀)
      have hre : (w - s₀).re = w.re - 2 := by simp [hs₀]
      rw [hre] at h
      linarith [(abs_le.mp (h.trans hw)).1]
    have hwim : |w.im| ≤ |t| + 2 := by
      have h := Complex.abs_im_le_norm (w - s₀)
      have him : (w - s₀).im = w.im - t := by simp [hs₀]
      rw [him] at h
      have h3 : |w.im| - |t| ≤ |w.im - t| := abs_sub_abs_le_abs_sub w.im t
      linarith [h.trans hw]
    calc ‖χ.LFunction w‖ ≤ 8 * q * (|w.im| + 3) :=
          Zeta23.ThmE.LFunction_growth_right_uniform hχ1 hwre
      _ ≤ 8 * q * (|t| + 5) := by
          have h8q : (0 : ℝ) ≤ 8 * (q : ℝ) := by positivity
          nlinarith [mul_le_mul_of_nonneg_left (show |w.im| + 3 ≤ |t| + 5 by linarith) h8q]
      _ = B * (1/3) := by rw [hB]; ring
      _ ≤ B * ‖χ.LFunction s₀‖ := mul_le_mul_of_nonneg_left hlow (by rw [hB]; positivity)
  obtain ⟨Z, hZset, -, hZpf⟩ := Zeta23.WeilEF.logDeriv_partial_fraction_disk
    (f := χ.LFunction) (by norm_num : (0:ℝ) < 91/50) hfa hLs₀ hB2 hfB
  -- `log B ≤ 5 log(q(|t| + 3))`.
  have hlogB : Real.log B ≤ 5 * Real.log ((q : ℝ) * (|t| + 3)) := by
    have h1 : B ≤ 72 * ((q : ℝ) * (|t| + 3)) := by rw [hB]; nlinarith [abs_nonneg t]
    have h2 : Real.log B ≤ Real.log 72 + Real.log ((q : ℝ) * (|t| + 3)) := by
      calc Real.log B ≤ Real.log (72 * ((q : ℝ) * (|t| + 3))) :=
            Real.log_le_log (by rw [hB]; positivity) h1
        _ = Real.log 72 + Real.log ((q : ℝ) * (|t| + 3)) :=
            Real.log_mul (by norm_num) (by positivity)
    have h3 : Real.log 72 ≤ 4 * Real.log 3 := by
      have h81 : Real.log ((3 : ℝ) ^ 4) = 4 * Real.log 3 := by rw [Real.log_pow]; norm_num
      rw [← h81]
      exact Real.log_le_log (by norm_num) (by norm_num)
    have h4 := log_three_le_log_conductor (q := q) t
    linarith
  refine ⟨Z, hZset, fun s hs hLs => ?_⟩
  have hs' : s ∈ closedBall s₀ (83/100 * (91/50)) := closedBall_subset_closedBall (by norm_num) hs
  refine (hZpf s hs' hLs).trans ?_
  calc 44795000 / (91/50) * Real.log B
      ≤ 44795000 / (91/50) * (5 * Real.log ((q : ℝ) * (|t| + 3))) :=
        mul_le_mul_of_nonneg_left hlogB (by norm_num)
    _ = pfConst * Real.log ((q : ℝ) * (|t| + 3)) := by unfold pfConst; ring

/-- **Zeros count with multiplicity at least one.** -/
theorem one_le_analyticOrderNatAt_LFunction (hχ1 : χ ≠ 1) {ρ : ℂ} (hρ : χ.LFunction ρ = 0) :
    1 ≤ analyticOrderNatAt χ.LFunction ρ := by
  have han : ∀ z, AnalyticAt ℂ χ.LFunction z := fun z =>
    (DirichletCharacter.differentiable_LFunction hχ1).analyticAt z
  have htop : analyticOrderAt χ.LFunction ρ ≠ ⊤ := by
    rw [Ne, AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero ρ han]
    intro h
    have h2 : χ.LFunction 2 = 0 := by rw [h]; rfl
    exact Zeta23.ThmE.LFunction_ne_zero_of_two_le_re (χ := χ) (s := 2) (by norm_num) h2
  have hne : analyticOrderAt χ.LFunction ρ ≠ 0 := (han ρ).analyticOrderAt_ne_zero.mpr hρ
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp htop
  rw [analyticOrderNatAt, ← hn, ENat.toNat_coe]
  rw [← hn] at hne
  exact Nat.one_le_iff_ne_zero.mpr fun h0 => hne (by rw [h0]; rfl)

/-- A zero of `L(s, χ)` lies left of `Re s = 1`. -/
theorem re_lt_one_of_LFunction_eq_zero (hχ1 : χ ≠ 1) {ρ : ℂ} (hρ : χ.LFunction ρ = 0) :
    ρ.re < 1 := by
  by_contra h
  push Not at h
  exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ1) h hρ

/-- **The zero-sum bound.** For `1 < σ ≤ 2` and any finite set of zeros near `2 + it`,
`−Re L'/L(σ + it, χ) ≤ C log(q(|t| + 3)) − Σ_{ρ ∈ S} Re 1/(σ + it − ρ)`. -/
theorem neg_re_logDeriv_LFunction_le (hχ1 : χ ≠ 1) {σ : ℝ} (t : ℝ) (hσ1 : 1 < σ) (hσ2 : σ ≤ 2)
    (S : Finset ℂ)
    (hS : ∀ ρ ∈ S, χ.LFunction ρ = 0 ∧ ρ ∈ closedBall (2 + t * I) (22/25 * (91/50))) :
    -(logDeriv χ.LFunction (σ + t * I)).re ≤
      pfConst * Real.log ((q : ℝ) * (|t| + 3)) - ∑ ρ ∈ S, ((σ + t * I - ρ)⁻¹).re := by
  obtain ⟨Z, hZset, hZpf⟩ := L_logDeriv_partial_fraction_all hχ1 t
  set s : ℂ := σ + t * I with hs
  have hsball : s ∈ closedBall (2 + t * I) (3/2) := by
    rw [mem_closedBall, Complex.dist_eq, hs]
    have : (σ : ℂ) + t * I - (2 + t * I) = ((σ - 2 : ℝ) : ℂ) := by push_cast; ring
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> linarith
  have hLs : χ.LFunction s ≠ 0 :=
    DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ1) (by simp [hs]; linarith)
  have hE := hZpf s hsball hLs
  -- Each zero of `Z` contributes a term of nonnegative real part.
  have hterm : ∀ ρ ∈ Z, 0 ≤ ((s - ρ)⁻¹).re := by
    intro ρ hρ
    have hρ0 : χ.LFunction ρ = 0 := by
      have : ρ ∈ (Z : Set ℂ) := hρ
      rw [hZset] at this
      exact this.2
    have hlt := re_lt_one_of_LFunction_eq_zero hχ1 hρ0
    rw [Complex.inv_re]
    refine div_nonneg ?_ (Complex.normSq_nonneg _)
    simp only [hs, sub_re, add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im]
    linarith
  have hSZ : S ⊆ Z := by
    intro ρ hρ
    have : ρ ∈ (Z : Set ℂ) := by rw [hZset]; exact ⟨(hS ρ hρ).2, (hS ρ hρ).1⟩
    exact this
  have hsum : ∑ ρ ∈ S, ((s - ρ)⁻¹).re ≤
      (∑ ρ ∈ Z, (analyticOrderNatAt χ.LFunction ρ : ℂ) / (s - ρ)).re := by
    rw [Complex.re_sum]
    calc ∑ ρ ∈ S, ((s - ρ)⁻¹).re
        ≤ ∑ ρ ∈ Z, ((s - ρ)⁻¹).re :=
          Finset.sum_le_sum_of_subset_of_nonneg hSZ fun ρ hρ _ => hterm ρ hρ
      _ ≤ ∑ ρ ∈ Z, ((analyticOrderNatAt χ.LFunction ρ : ℂ) / (s - ρ)).re := by
          refine Finset.sum_le_sum fun ρ hρ => ?_
          have hρ0 : χ.LFunction ρ = 0 := by
            have : ρ ∈ (Z : Set ℂ) := hρ
            rw [hZset] at this
            exact this.2
          have hm : (1 : ℝ) ≤ analyticOrderNatAt χ.LFunction ρ := by
            exact_mod_cast one_le_analyticOrderNatAt_LFunction hχ1 hρ0
          rw [div_eq_mul_inv, show ((analyticOrderNatAt χ.LFunction ρ : ℕ) : ℂ) =
            ((analyticOrderNatAt χ.LFunction ρ : ℝ) : ℂ) by norm_cast, Complex.re_ofReal_mul]
          nlinarith [hterm ρ hρ]
  have hre : -(logDeriv χ.LFunction s).re ≤
      ‖logDeriv χ.LFunction s - ∑ ρ ∈ Z, (analyticOrderNatAt χ.LFunction ρ : ℂ) / (s - ρ)‖ -
        (∑ ρ ∈ Z, (analyticOrderNatAt χ.LFunction ρ : ℂ) / (s - ρ)).re := by
    have h := Complex.re_le_norm
      (-(logDeriv χ.LFunction s - ∑ ρ ∈ Z, (analyticOrderNatAt χ.LFunction ρ : ℂ) / (s - ρ)))
    rw [norm_neg, neg_re, sub_re] at h
    linarith
  linarith

end RHTower
