import GaloisForLFunctions.SquareRootThreshold.DirichletLFunctionTwoBumpCriterion

/-!
# The negativity rate of two-bump tests equals the maximal depth

For a bump `b` let `μ_b(v) = 2 Re S_b(0) − |S_b(v) + conj S_b(−v)|`. It is the least value of
`Re W` on the unimodular two-bump tests `b(t + v/2) + τ b(t − v/2)`, `|τ| = 1`
(`minorDeficit_le_re_W`, `exists_unit_re_W_eq_minorDeficit`).

* **Upper rate** (`minorDeficit_ge`). If every zero has depth `Re ρ − ½ ≤ D`, `D ≥ 0`, then
  `μ_b(v) ≥ −C e^{Dv}` for `v ≥ 0`: the off-line pairs contribute at most `|q_t| e^{δ_t v}`.
* **Lower rate** (`exists_minorDeficit_lt`). If some zero has depth `|Re ρ − ½| > σ ≥ 0`, then for
  `κ` modulated to a suitable height, `μ(v) < −K e^{σv}` at some lag `v ≥ 0`, for every `K`. The
  rightmost zero at that height is a pole of the Laplace transform of the off-line sum beyond
  abscissa `σ` (`eq_zero_of_norm_tsum_exp_le_exp`).

So the exponential rate at which unimodular two-bump tests turn negative is exactly the supremum
of the depths. For `ζ` (`zeta_primeSide_twoBump_ge`, `zeta_exists_primeSide_twoBump_lt`) the
prime-side functional at lag `v = log X`, which sees the primes up to `e² X`, is bounded below by
`−C X^{D}` when all zeros have `Re ρ ≤ ½ + D`. It is not `O(X^σ)` for any `σ` below the depth of
a zero. RH is the statement that the negativity does not grow at any exponential rate: the
square-root threshold `X^{Θ − 1/2}` with `Θ = ½`.
-/

open MeasureTheory Complex Set Filter Topology
open scoped Real ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.SquareRootThreshold

open Zeta23 _root_.RHTower

/-- The least value of `Re W` on the unimodular two-bump tests at lag `v`. -/
def minorDeficit (Z : ZeroConfig) (b : ℝ → ℂ) (v : ℝ) : ℝ :=
  2 * (lagStructure Z b 0).re - ‖lagStructure Z b v + conj (lagStructure Z b (-v))‖

theorem re_W_unit_twoBump (Z : ZeroConfig) (hZ : TemperedConfig Z) {b : ℝ → ℂ}
    (hb : ContDiff ℝ 2 b) {w : ℝ} (hbs : ∀ u, b u ≠ 0 → |u| ≤ w) (v : ℝ) {τ : ℂ}
    (hτ : ‖τ‖ = 1) :
    (Z.W (twoBump b v τ) (twoBump b v τ)).re = 2 * (lagStructure Z b 0).re +
      (τ * (lagStructure Z b v + conj (lagStructure Z b (-v)))).re := by
  have h2 : (conj τ * lagStructure Z b (-v)).re = (τ * conj (lagStructure Z b (-v))).re := by
    rw [← Complex.conj_re, map_mul, Complex.conj_conj]
  have hτ2 : (1 + (‖τ‖ : ℂ) ^ 2) = 2 := by rw [hτ]; norm_num
  rw [W_twoBump Z hZ hb hbs v τ, hτ2, Complex.add_re, Complex.add_re, h2, mul_add,
    Complex.add_re]
  simp
  ring

/-- `μ_b(v)` is a lower bound for `Re W` on the unimodular two-bump tests. -/
theorem minorDeficit_le_re_W (Z : ZeroConfig) (hZ : TemperedConfig Z) {b : ℝ → ℂ}
    (hb : ContDiff ℝ 2 b) {w : ℝ} (hbs : ∀ u, b u ≠ 0 → |u| ≤ w) (v : ℝ) {τ : ℂ}
    (hτ : ‖τ‖ = 1) : minorDeficit Z b v ≤ (Z.W (twoBump b v τ) (twoBump b v τ)).re := by
  rw [re_W_unit_twoBump Z hZ hb hbs v hτ, minorDeficit]
  have h := (abs_le.mp (Complex.abs_re_le_norm
    (τ * (lagStructure Z b v + conj (lagStructure Z b (-v)))))).1
  rw [norm_mul, hτ, one_mul] at h
  linarith

/-- `μ_b(v)` is attained on the unimodular two-bump tests. -/
theorem exists_unit_re_W_eq_minorDeficit (Z : ZeroConfig) (hZ : TemperedConfig Z) {b : ℝ → ℂ}
    (hb : ContDiff ℝ 2 b) {w : ℝ} (hbs : ∀ u, b u ≠ 0 → |u| ≤ w) (v : ℝ) :
    ∃ τ : ℂ, ‖τ‖ = 1 ∧ (Z.W (twoBump b v τ) (twoBump b v τ)).re = minorDeficit Z b v := by
  set X := lagStructure Z b v + conj (lagStructure Z b (-v)) with hX
  by_cases hX0 : X = 0
  · refine ⟨1, norm_one, ?_⟩
    rw [re_W_unit_twoBump Z hZ hb hbs v norm_one, minorDeficit, ← hX, hX0]
    simp
  · refine ⟨-(conj X / ‖X‖), ?_, ?_⟩
    · rw [norm_neg, norm_div, Complex.norm_conj, Complex.norm_real, norm_norm,
        div_self (norm_ne_zero_iff.mpr hX0)]
    · have hn : ‖-(conj X / ‖X‖)‖ = 1 := by
        rw [norm_neg, norm_div, Complex.norm_conj, Complex.norm_real, norm_norm,
          div_self (norm_ne_zero_iff.mpr hX0)]
      rw [re_W_unit_twoBump Z hZ hb hbs v hn, minorDeficit, ← hX]
      have hτX : (-(conj X / ‖X‖) * X).re = -‖X‖ := by
        rw [neg_mul, div_mul_eq_mul_div, ← Complex.normSq_eq_conj_mul_self,
          Complex.normSq_eq_norm_sq]
        rw [show ((‖X‖ ^ 2 : ℝ) : ℂ) / (‖X‖ : ℂ) = ((‖X‖ : ℝ) : ℂ) by
          have : (‖X‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hX0
          push_cast; field_simp]
        simp
      rw [hτX]
      ring

/-- **Upper rate.** If every zero has depth at most `D ≥ 0`, then `μ_b(v) ≥ −C e^{Dv}`. -/
theorem minorDeficit_ge (Z : ZeroConfig) (hZ : TemperedConfig Z) {b : ℝ → ℂ}
    (hb : ContDiff ℝ 2 b) {w : ℝ} (hbs : ∀ u, b u ≠ 0 → |u| ≤ w) {D : ℝ} (hD0 : 0 ≤ D)
    (hD : ∀ ρ ∈ Z.carrier, ρ.re - 1 / 2 ≤ D) :
    ∃ C : ℝ, ∀ v : ℝ, 0 ≤ v → -(C * Real.exp (D * v)) ≤ minorDeficit Z b v := by
  have hbc : HasCompactSupport b := hasCompactSupport_of_support_subset_abs hbs
  set q : ℂ → ℂ := fun t => offLineWeight b (Z.mult t) t with hq
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
  set Q := ∑' t : rightZeros Z, ‖q t‖ with hQ
  have hQ0 : 0 ≤ Q := tsum_nonneg fun _ => norm_nonneg _
  refine ⟨8 * Q, fun v hv => ?_⟩
  obtain ⟨-, h2, h3⟩ := rightZeros_minor_bounds Z hZ hb hbs hv
  have hE : ∀ t : ℂ, ‖cexp (I * t.im * v)‖ = 1 := fun t => by
    rw [show I * (t.im : ℂ) * (v : ℂ) = ((t.im * v : ℝ) : ℂ) * I by push_cast; ring]
    exact Complex.norm_exp_ofReal_mul_I _
  have hterm : ∀ t : rightZeros Z, ‖q t * (Real.exp (((t : ℂ).re - 1 / 2) * v) : ℂ) *
      cexp (I * (t : ℂ).im * v)‖ ≤ ‖q t‖ * Real.exp (D * v) := fun t => by
    rw [norm_mul, norm_mul, hE, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_right (hD _ t.2.1) hv)) (norm_nonneg _)
  have hA : ‖∑' t : rightZeros Z, q t * (Real.exp (((t : ℂ).re - 1 / 2) * v) : ℂ) *
      cexp (I * (t : ℂ).im * v)‖ ≤ Q * Real.exp (D * v) := by
    have hs : Summable fun t : rightZeros Z => ‖q t‖ * Real.exp (D * v) := hqs.mul_right _
    refine (norm_tsum_le_tsum_norm (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm hs)).trans
      ?_
    rw [hQ, ← tsum_mul_right]
    exact Summable.tsum_le_tsum hterm (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm hs)
      hs
  have hS0 := (abs_le.mp h3).1
  have hQeq : ∑' t : rightZeros Z, ‖offLineWeight b (Z.mult t) t‖ = Q := rfl
  rw [hQeq] at h2 hS0
  have he : 1 ≤ Real.exp (D * v) := Real.one_le_exp (mul_nonneg hD0 hv)
  have hQe : Q ≤ Q * Real.exp (D * v) := le_mul_of_one_le_right hQ0 he
  rw [minorDeficit]
  linarith

/-- **Lower rate.** If some zero has depth `|Re ρ − ½| > σ ≥ 0`, then for every `K` there are a height
`γ` and a lag `v ≥ 0` with `μ(v) < −K e^{σv}` for `κ` modulated to `γ`. -/
theorem exists_minorDeficit_lt (Z : ZeroConfig) (hZ : TemperedConfig Z) {ρ : ℂ}
    (hρ : ρ ∈ Z.carrier) {σ : ℝ} (hσ0 : 0 ≤ σ) (hσ : σ < |ρ.re - 1 / 2|) (K : ℝ) :
    ∃ γ v : ℝ, 0 ≤ v ∧ minorDeficit Z (modScaledBump 1 γ) v < -(K * Real.exp (σ * v)) := by
  -- a zero right of the line of the same depth
  obtain ⟨t, ht, htd⟩ : ∃ t ∈ rightZeros Z, t.re - 1 / 2 = |ρ.re - 1 / 2| := by
    rcases le_or_gt ρ.re (1 / 2) with h | h
    · refine ⟨reflect ρ, ⟨Z.reflect_mem ρ hρ, ?_⟩, ?_⟩
      · have : ρ.re ≠ 1 / 2 := fun he => by rw [he, sub_self, abs_zero] at hσ; linarith
        simp [reflect]
        linarith [lt_of_le_of_ne h this]
      · rw [abs_of_nonpos (by linarith)]
        simp [reflect]
        ring
    · exact ⟨ρ, ⟨hρ, h⟩, by rw [abs_of_pos (by linarith)]⟩
  have hqne : ∀ t' ∈ rightZeros Z, t'.im = t.im →
      offLineWeight (modScaledBump 1 t.im) (Z.mult t') t' ≠ 0 := fun t' ht' him => by
    have hm := Z.one_le_mult t' ht'.1
    rw [offLineWeight, him]
    exact mul_ne_zero (Nat.cast_ne_zero.mpr (by omega))
      (pairWeight_modScaledBump_ne_zero one_pos _ _)
  obtain ⟨t₀, ht₀, him₀, -, htop⟩ := exists_top_at_height Z ht (fun _ => True) trivial
  have hdeep : σ < t₀.re - 1 / 2 := by
    have := htop t ht rfl trivial
    linarith
  obtain ⟨v, hv, h⟩ := exists_minor_gt_of_top Z hZ (contDiff_modScaledBump_two 1 t.im)
    (modScaledBump_support one_pos t.im) ht₀ (hqne t₀ ht₀ him₀)
    (fun t' ht' him' _ => htop t' ht' (him'.trans him₀) trivial) hσ0 hdeep K
  exact ⟨t.im, v, hv, by rw [minorDeficit]; linarith⟩

/-- **For `ζ`, upper rate.** If every nontrivial zero has `Re ρ ≤ ½ + D`, `D ≥ 0`, then for each
height `γ` the prime-side functional on the unimodular two-bump tests at lag `v` is at least
`−C e^{Dv}`. -/
theorem zeta_primeSide_twoBump_ge {D : ℝ} (hD0 : 0 ≤ D)
    (hD : ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re - 1 / 2 ≤ D) (γ : ℝ) :
    ∃ C : ℝ, ∀ (v : ℝ) (τ : ℂ), 0 ≤ v → ‖τ‖ = 1 → -(C * Real.exp (D * v)) ≤
      (EF.literatureRHS (EF.weilTest (twoBump (modScaledBump 1 γ) v τ)
        (twoBump (modScaledBump 1 γ) v τ))).re := by
  obtain ⟨C, hC⟩ := minorDeficit_ge zetaZeroConfig temperedConfig_zetaZeroConfig
    (contDiff_modScaledBump_two 1 γ) (modScaledBump_support one_pos γ) hD0 hD
  refine ⟨C, fun v τ hv hτ => ?_⟩
  rw [← zeta_W_eq_literatureRHS (f := twoBump (modScaledBump 1 γ) v τ)
    (contDiff_bumpTest (contDiff_modScaledBump_two 1 γ) v ![1, τ])
    (hasCompactSupport_twoBump (hasCompactSupport_of_support_subset_abs
      (modScaledBump_support one_pos γ)) v τ)]
  exact (hC v hv).trans (minorDeficit_le_re_W _ temperedConfig_zetaZeroConfig
    (contDiff_modScaledBump_two 1 γ) (modScaledBump_support one_pos γ) v hτ)

/-- **For `ζ`, lower rate.** If some nontrivial zero has `|Re ρ − ½| > σ ≥ 0`, then for every `K`
some unimodular two-bump test has prime-side value `< −K e^{σv}` at its lag `v`. -/
theorem zeta_exists_primeSide_twoBump_lt {ρ : ℂ} (hρ : ρ ∈ zetaZeroConfig.carrier) {σ : ℝ}
    (hσ0 : 0 ≤ σ) (hσ : σ < |ρ.re - 1 / 2|) (K : ℝ) :
    ∃ (γ v : ℝ) (τ : ℂ), 0 ≤ v ∧ ‖τ‖ = 1 ∧
      (EF.literatureRHS (EF.weilTest (twoBump (modScaledBump 1 γ) v τ)
        (twoBump (modScaledBump 1 γ) v τ))).re < -(K * Real.exp (σ * v)) := by
  obtain ⟨γ, v, hv, hlt⟩ := exists_minorDeficit_lt zetaZeroConfig temperedConfig_zetaZeroConfig
    hρ hσ0 hσ K
  obtain ⟨τ, hτ, heq⟩ := exists_unit_re_W_eq_minorDeficit zetaZeroConfig
    temperedConfig_zetaZeroConfig (contDiff_modScaledBump_two 1 γ)
    (modScaledBump_support one_pos γ) v
  refine ⟨γ, v, τ, hv, hτ, ?_⟩
  rw [← zeta_W_eq_literatureRHS (f := twoBump (modScaledBump 1 γ) v τ)
    (contDiff_bumpTest (contDiff_modScaledBump_two 1 γ) v ![1, τ])
    (hasCompactSupport_twoBump (hasCompactSupport_of_support_subset_abs
      (modScaledBump_support one_pos γ)) v τ), heq]
  exact hlt

end GaloisForLFunctions.SquareRootThreshold
