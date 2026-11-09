import GaloisForLFunctions.SurfaceOfSpecZ.ThePrimesInAResidueClassFromBothSides

/-!
# The lower side sees the sign of the top layer

Let every exponent of a tempered configuration have real part `≤ b`, `b > 0`. The normalized trace
`F(u) = 2 Re S(u) e^{−bu}` splits as `F = F_top + F_low`, with `F_top(u) = Re Σ_{Re z = b} e_z e^{(z−b)u}`
almost periodic and `F_low(u) → 0` (`tendsto_normTrace_sub_topTrace`). A lower bound at a sampling
set sees exactly the sign of `F_top`.

* **Necessity, in Bohr duality** (`re_sum_topCoeff_nonneg_of_bddBelow`). If `2 Re S(log n) ≥ −K` where
  a sampling weight is nonzero, then for every exponential polynomial `P(u) = Σ_k p_k e^{iλ_k u}`
  with `Re P ≥ 0` on `ℝ`: `Re Σ_k p_k e_{b − iλ_k} ≥ 0`, i.e. the Bohr mean of `F_top · Re P` is
  `≥ 0`. The twisted means `Σ w(n) F(log n) n^{iλ−σ} / Σ w(n) n^{−σ}` tend to the top coefficient
  `e_{b−iλ}` (`tendsto_wTwistMean`), and `F · Re P ≥ −|K| n^{−b} Σ_k|p_k|`.
* **Fejér's inequality for the top layer** (`norm_evenCoeff_le_of_bddBelow`): with
  `P = 2 + τe^{iλu} + τ̄e^{−iλu}`, every top coefficient is bounded by the real one,
  `|e_{b+iλ}| ≤ e_b`. A real zero masks only the top zeros it dominates.
* **Sufficiency** (`bddBelow_of_topTrace_ge`). If `F_top ≥ δ > 0` on `u ≥ 0`, the traces are bounded
  below at every `u ≥ 0`, in particular at every degree. `ARealTopKeepsTheLowerSideBounded` is the
  case `F_top = e_b`.

So the blind set of the lower side is the set of configurations whose top layer is a nonnegative
almost periodic function, up to the boundary `inf F_top = 0`.
-/

open Complex Filter Topology
open scoped ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.SurfaceOfSpecZ

open ArithmeticOrientationGeometry ArithmeticCastelnuovoSeveri SquareRootThreshold Zeta23
open ArithmeticFunction

/-! ### Twisted means -/

/-- The twisted weighted mean `Σ w(n) F(log n) n^{iλ − σ}`. -/
def wTwistMean (w : ℕ → ℝ) (Z : ZeroConfig) (b σ lam : ℝ) : ℂ :=
  ∑' j : ℕ, (w j : ℂ) * ((normTrace Z b (Real.log (j + 1)) : ℝ) : ℂ) *
    ((j : ℂ) + 1) ^ (-((σ : ℂ) - lam * I))

/-- `n^{iλ − σ} = n^{−σ} e^{iλ log n}`. -/
theorem cpow_twist (j : ℕ) (σ lam : ℝ) :
    ((j : ℂ) + 1) ^ (-((σ : ℂ) - lam * I)) =
      ((((j : ℝ) + 1) ^ (-σ) : ℝ) : ℂ) * cexp (lam * Real.log (j + 1) * I) := by
  rw [ofReal_add_one_rpow j (-σ), natCast_add_one_cpow_eq, natCast_add_one_cpow_eq,
    ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- If `−K ≤ 2 Re S(log n)` then `−|K| n^{−b} ≤ F(log n)`. -/
theorem neg_le_normTrace_of_le {Z : ZeroConfig} {b K : ℝ} {j : ℕ}
    (h1 : -K ≤ 2 * (lagStructure Z (boxSpline 1 3) (Real.log (j + 1))).re) :
    -(|K| * ((j : ℝ) + 1) ^ (-b)) ≤ normTrace Z b (Real.log ((j : ℝ) + 1)) := by
  have hj0 : (0 : ℝ) < (j : ℝ) + 1 := by positivity
  have hexp : Real.exp (-(b * Real.log ((j : ℝ) + 1))) = ((j : ℝ) + 1) ^ (-b) := by
    rw [Real.rpow_def_of_pos hj0]; ring_nf
  have hpb : 0 < ((j : ℝ) + 1) ^ (-b) := by positivity
  rw [normTrace, hexp]
  have h3 := mul_le_mul_of_nonneg_right h1 hpb.le
  have h4 : K * ((j : ℝ) + 1) ^ (-b) ≤ |K| * ((j : ℝ) + 1) ^ (-b) :=
    mul_le_mul_of_nonneg_right (le_abs_self K) hpb.le
  linarith

section Twist

variable {w : ℕ → ℝ} (hw : SamplingWeight w) {Z : ZeroConfig} {b : ℝ}
include hw

theorem summable_wTwist (hZ : TemperedConfig Z) (h : TopDepth Z b) {σ : ℝ} (hσ : 1 < σ)
    (lam : ℝ) : Summable fun j : ℕ => (w j : ℂ) * ((normTrace Z b (Real.log (j + 1)) : ℝ) : ℂ) *
      ((j : ℂ) + 1) ^ (-((σ : ℂ) - lam * I)) := by
  set E := ∑' z, ‖evenCoeff Z (boxSpline 1 3) z‖
  refine Summable.of_norm_bounded ((hw.summable hσ).mul_left E) fun j => ?_
  rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_nonneg (hw.nonneg j), norm_natCast_add_one_cpow]
  have hre : (-((σ : ℂ) - lam * I)).re = -σ := by simp
  rw [hre]
  have hF := abs_normTrace_le hZ h (log_add_one_nonneg j)
  have hw0 := hw.nonneg j
  have hp : 0 ≤ ((j : ℝ) + 1) ^ (-σ) := by positivity
  nlinarith [mul_nonneg (mul_nonneg hw0 hp) (sub_nonneg.mpr hF)]

/-- **The twisted mean through the exponents.** -/
theorem wTwistMean_eq (hZ : TemperedConfig Z) (h : TopDepth Z b) {σ : ℝ} (hσ : 1 < σ) (lam : ℝ) :
    wTwistMean w Z b σ lam = ∑' z, evenCoeff Z (boxSpline 1 3) z *
      wSeries w ((σ : ℂ) + ((b : ℂ) - z - lam * I)) := by
  set e := evenCoeff Z (boxSpline 1 3) with hedef
  have hE := summable_norm_evenCoeff_spline hZ
  set f : ℕ → ℂ → ℂ := fun j z => (w j : ℂ) *
    (e z * ((j : ℂ) + 1) ^ (-((σ : ℂ) + ((b : ℂ) - z - lam * I)))) with hfdef
  have hfn : ∀ j z, ‖f j z‖ ≤ w j * ((j : ℝ) + 1) ^ (-σ) * ‖e z‖ := by
    intro j z
    by_cases hz : e z = 0
    · simp [hfdef, hz]
    have h1 := h z hz
    simp only [hfdef, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (hw.nonneg j), norm_natCast_add_one_cpow]
    have hexp : ((j : ℝ) + 1) ^ (-((σ : ℂ) + ((b : ℂ) - z - lam * I))).re ≤
        ((j : ℝ) + 1) ^ (-σ) := by
      apply Real.rpow_le_rpow_of_exponent_le (by linarith [Nat.cast_nonneg (α := ℝ) j])
      simp; linarith
    calc w j * (‖e z‖ * ((j : ℝ) + 1) ^ (-((σ : ℂ) + ((b : ℂ) - z - lam * I))).re)
        ≤ w j * (‖e z‖ * ((j : ℝ) + 1) ^ (-σ)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hexp (norm_nonneg _)) (hw.nonneg j)
      _ = _ := by ring
  have hprod : Summable fun p : ℕ × ℂ => w p.1 * ((p.1 : ℝ) + 1) ^ (-σ) * ‖e p.2‖ :=
    (hw.summable hσ).mul_of_nonneg hE
      (fun j => mul_nonneg (hw.nonneg j) (by positivity)) (fun _ => norm_nonneg _)
  have hFsum2 : Summable (Function.uncurry f) := Summable.of_norm_bounded hprod fun p => hfn p.1 p.2
  have hj : ∀ j : ℕ, ∑' z, f j z = (w j : ℂ) * ((normTrace Z b (Real.log (j + 1)) : ℝ) : ℂ) *
      ((j : ℂ) + 1) ^ (-((σ : ℂ) - lam * I)) := by
    intro j
    simp only [hfdef]
    rw [tsum_mul_left, ofReal_normTrace hZ, mul_assoc, ← tsum_mul_right]
    congr 1
    refine tsum_congr fun z => ?_
    rw [natCast_add_one_cpow_eq, natCast_add_one_cpow_eq, mul_assoc, ← Complex.exp_add]
    congr 2
    ring
  have hz : ∀ z : ℂ, ∑' j, f j z = e z * wSeries w ((σ : ℂ) + ((b : ℂ) - z - lam * I)) := by
    intro z
    rw [wSeries, ← tsum_mul_left]
    refine tsum_congr fun j => ?_
    simp only [hfdef]; ring
  rw [wTwistMean, ← tsum_congr hj, hFsum2.tsum_comm.symm, tsum_congr hz]

/-- **The twisted means tend to the top coefficients.** -/
theorem tendsto_wTwistMean (hZ : TemperedConfig Z) (h : TopDepth Z b) (lam : ℝ) :
    Tendsto (fun σ => wTwistMean w Z b σ lam / (wSum w σ : ℂ)) (𝓝[>] 1)
      (𝓝 (evenCoeff Z (boxSpline 1 3) ((b : ℂ) - lam * I))) := by
  set e := evenCoeff Z (boxSpline 1 3) with hedef
  have hE := summable_norm_evenCoeff_spline hZ
  set z₀ : ℂ := (b : ℂ) - lam * I with hz₀
  have hc : Tendsto (fun σ : ℝ => ∑' z, e z * wSeries w ((σ : ℂ) + ((b : ℂ) - z - lam * I)) /
      (wSum w σ : ℂ)) (𝓝[>] 1) (𝓝 (∑' z : ℂ, if z = z₀ then e z else 0)) := by
    refine tendsto_tsum_of_dominated_convergence hE (fun z => ?_) ?_
    · by_cases hzb : z = z₀
      · have hconst : ∀ᶠ σ : ℝ in 𝓝[>] (1 : ℝ),
            e z * wSeries w ((σ : ℂ) + ((b : ℂ) - z - lam * I)) / (wSum w σ : ℂ) = e z := by
          filter_upwards [hw.eventually_pos] with σ hV
          have h0 : (σ : ℂ) + ((b : ℂ) - z - lam * I) = σ := by rw [hzb, hz₀]; ring
          rw [h0, ← ofReal_wSum, mul_div_assoc, div_self (by exact_mod_cast hV.ne'), mul_one]
        simp only [if_pos hzb]
        exact tendsto_const_nhds.congr' (hconst.mono fun σ h => h.symm)
      · simp only [if_neg hzb]
        by_cases hz : e z = 0
        · simp [hz]
        have h1 := h z hz
        have hne : (b : ℂ) - z - lam * I ≠ 0 := fun h0 => hzb (by rw [hz₀]; linear_combination -h0)
        have := (hw.tendsto_off ((b : ℂ) - z - lam * I) hne (by simp; linarith)).const_mul (e z)
        simpa [mul_div_assoc] using this
    · filter_upwards [self_mem_nhdsWithin, hw.eventually_pos] with σ hσ hV
      intro z
      have hσ1 : 1 < σ := hσ
      by_cases hz : e z = 0
      · simp [hz]
      have h1 := h z hz
      have hres : 1 < ((σ : ℂ) + ((b : ℂ) - z - lam * I)).re := by simp; linarith
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hV, norm_mul, div_le_iff₀ hV]
      have hb1 := hw.norm_wSeries_le hres
      have hb2 : wSum w ((σ : ℂ) + ((b : ℂ) - z - lam * I)).re ≤ wSum w σ :=
        hw.antitone hσ1 (by simp; linarith)
      exact mul_le_mul_of_nonneg_left (hb1.trans hb2) (norm_nonneg _)
  rw [tsum_ite_eq] at hc
  refine hc.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with σ hσ
  rw [wTwistMean_eq hw hZ h hσ, tsum_div_const]

end Twist

/-! ### Exponential polynomials -/

/-- `P(u) = Σ_k p_k e^{iλ_k u}`. -/
def expPoly {ι : Type*} (s : Finset ι) (p : ι → ℂ) (lam : ι → ℝ) (u : ℝ) : ℂ :=
  ∑ k ∈ s, p k * cexp (lam k * u * I)

theorem norm_expPoly_le {ι : Type*} (s : Finset ι) (p : ι → ℂ) (lam : ι → ℝ) (u : ℝ) :
    ‖expPoly s p lam u‖ ≤ ∑ k ∈ s, ‖p k‖ := by
  unfold expPoly
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  have : (lam k : ℂ) * u * I = ((lam k * u : ℝ) : ℂ) * I := by push_cast; ring
  rw [norm_mul, this, Complex.norm_exp_ofReal_mul_I, mul_one]

section Pairing

variable {w : ℕ → ℝ} (hw : SamplingWeight w) {Z : ZeroConfig} {b : ℝ}
include hw

/-- The real part of `Σ_k p_k · (twisted mean at λ_k)` is the mean of `F · Re P`. -/
theorem re_sum_wTwistMean (hZ : TemperedConfig Z) (h : TopDepth Z b) {σ : ℝ} (hσ : 1 < σ)
    {ι : Type*} (s : Finset ι) (p : ι → ℂ) (lam : ι → ℝ) :
    (∑ k ∈ s, p k * wTwistMean w Z b σ (lam k)).re =
      ∑' j : ℕ, w j * normTrace Z b (Real.log (j + 1)) *
        (expPoly s p lam (Real.log (j + 1))).re * ((j : ℝ) + 1) ^ (-σ) := by
  have hsum : ∀ k ∈ s, Summable fun j : ℕ => p k * ((w j : ℂ) *
      ((normTrace Z b (Real.log (j + 1)) : ℝ) : ℂ) * ((j : ℂ) + 1) ^ (-((σ : ℂ) - (lam k) * I))) :=
    fun k _ => (summable_wTwist hw hZ h hσ (lam k)).mul_left _
  have hterm : ∀ j : ℕ, (∑ k ∈ s, p k * ((w j : ℂ) *
      ((normTrace Z b (Real.log (j + 1)) : ℝ) : ℂ) * ((j : ℂ) + 1) ^ (-((σ : ℂ) - (lam k) * I)))) =
      ((w j * normTrace Z b (Real.log (j + 1)) * ((j : ℝ) + 1) ^ (-σ) : ℝ) : ℂ) *
        expPoly s p lam (Real.log (j + 1)) := by
    intro j
    simp only [cpow_twist, expPoly, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    push_cast
    ring
  have hmain : (∑ k ∈ s, p k * wTwistMean w Z b σ (lam k)) =
      ∑' j : ℕ, ((w j * normTrace Z b (Real.log (j + 1)) * ((j : ℝ) + 1) ^ (-σ) : ℝ) : ℂ) *
        expPoly s p lam (Real.log (j + 1)) := by
    simp only [wTwistMean, ← tsum_mul_left]
    rw [← Summable.tsum_finsetSum hsum]
    exact tsum_congr hterm
  rw [hmain, Complex.re_tsum ((summable_sum hsum).congr hterm)]
  refine tsum_congr fun j => ?_
  rw [Complex.re_ofReal_mul]
  ring

/-- **A lower bound at a sampling set pairs the top layer nonnegatively with every nonnegative
exponential polynomial.** -/
theorem re_sum_topCoeff_nonneg_of_bddBelow (hZ : TemperedConfig Z) (h : TopDepth Z b)
    (hb0 : 0 < b) {K : ℝ}
    (hK : ∀ j : ℕ, w j ≠ 0 → -K ≤ 2 * (lagStructure Z (boxSpline 1 3) (Real.log (j + 1))).re)
    {ι : Type*} (s : Finset ι) (p : ι → ℂ) (lam : ι → ℝ)
    (hP : ∀ u : ℝ, 0 ≤ (expPoly s p lam u).re) :
    0 ≤ (∑ k ∈ s, p k * evenCoeff Z (boxSpline 1 3) ((b : ℂ) - lam k * I)).re := by
  set M := ∑ k ∈ s, ‖p k‖ with hMdef
  have hM0 : 0 ≤ M := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hlim : Tendsto (fun σ => (∑ k ∈ s, p k * (wTwistMean w Z b σ (lam k) / (wSum w σ : ℂ))).re)
      (𝓝[>] 1) (𝓝 (∑ k ∈ s, p k * evenCoeff Z (boxSpline 1 3) ((b : ℂ) - lam k * I)).re) :=
    (Complex.continuous_re.tendsto _).comp
      (tendsto_finsetSum _ fun k _ => (tendsto_wTwistMean hw hZ h (lam k)).const_mul (p k))
  have hlimε : Tendsto (fun σ => wSum w (σ + b) / wSum w σ) (𝓝[>] 1) (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (tendsto_const_nhds (x := (0 : ℝ)))
      ((tendsto_const_nhds (x := wSum w (1 + b))).div_atTop hw.tendsto_atTop) ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with σ hσ
      exact div_nonneg (hw.wSum_nonneg _) (hw.wSum_nonneg _)
    · filter_upwards [self_mem_nhdsWithin] with σ hσ
      have hσ1 : 1 < σ := hσ
      exact div_le_div_of_nonneg_right (hw.antitone (by linarith) (by linarith))
        (hw.wSum_nonneg _)
  have key := le_of_tendsto_of_tendsto (hlimε.const_mul (-(|K| * M))) hlim (by
    filter_upwards [self_mem_nhdsWithin, hw.eventually_pos] with σ hσ hV
    have hσ1 : 1 < σ := hσ
    have hX : (∑ k ∈ s, p k * (wTwistMean w Z b σ (lam k) / (wSum w σ : ℂ))) =
        (∑ k ∈ s, p k * wTwistMean w Z b σ (lam k)) / (wSum w σ : ℂ) := by
      rw [Finset.sum_div]; exact Finset.sum_congr rfl fun k _ => by ring
    rw [hX, Complex.div_ofReal_re, re_sum_wTwistMean hw hZ h hσ1 s p lam, le_div_iff₀ hV]
    have hrw : -(|K| * M) * (wSum w (σ + b) / wSum w σ) * wSum w σ =
        -(|K| * M) * wSum w (σ + b) := by field_simp
    rw [hrw]
    have hεsum := hw.summable (show 1 < σ + b by linarith)
    set E := ∑' z, ‖evenCoeff Z (boxSpline 1 3) z‖
    have hPsum : Summable fun j : ℕ => w j * normTrace Z b (Real.log (j + 1)) *
        (expPoly s p lam (Real.log (j + 1))).re * ((j : ℝ) + 1) ^ (-σ) := by
      refine Summable.of_norm_bounded ((hw.summable hσ1).mul_left (E * M)) fun j => ?_
      have hF := abs_normTrace_le hZ h (log_add_one_nonneg j)
      have hR : |(expPoly s p lam (Real.log (j + 1))).re| ≤ M :=
        (Complex.abs_re_le_norm _).trans (norm_expPoly_le s p lam _)
      have hw0 := hw.nonneg j
      have hp : 0 ≤ ((j : ℝ) + 1) ^ (-σ) := by positivity
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_of_nonneg hw0, abs_of_nonneg hp]
      have h1 : |normTrace Z b (Real.log ((j : ℝ) + 1))| * |(expPoly s p lam (Real.log (j + 1))).re|
          ≤ E * M := mul_le_mul hF hR (abs_nonneg _) (tsum_nonneg fun _ => norm_nonneg _)
      calc w j * |normTrace Z b (Real.log ((j : ℝ) + 1))| *
            |(expPoly s p lam (Real.log (j + 1))).re| * ((j : ℝ) + 1) ^ (-σ)
          = (|normTrace Z b (Real.log ((j : ℝ) + 1))| *
              |(expPoly s p lam (Real.log (j + 1))).re|) * (w j * ((j : ℝ) + 1) ^ (-σ)) := by ring
        _ ≤ (E * M) * (w j * ((j : ℝ) + 1) ^ (-σ)) :=
            mul_le_mul_of_nonneg_right h1 (mul_nonneg hw0 hp)
    rw [wSum, ← tsum_mul_left]
    refine Summable.tsum_le_tsum (fun j => ?_) (hεsum.mul_left _) hPsum
    have hw0 := hw.nonneg j
    have hj0 : (0 : ℝ) < (j : ℝ) + 1 := by positivity
    have hp : 0 < ((j : ℝ) + 1) ^ (-σ) := by positivity
    have hpb : 0 ≤ ((j : ℝ) + 1) ^ (-b) := by positivity
    have hsplit : ((j : ℝ) + 1) ^ (-(σ + b)) = ((j : ℝ) + 1) ^ (-σ) * ((j : ℝ) + 1) ^ (-b) := by
      rw [← Real.rpow_add hj0]; ring_nf
    rw [hsplit]
    by_cases hw00 : w j = 0
    · rw [hw00]; simp
    have hF := neg_le_normTrace_of_le (b := b) (hK j hw00)
    set f := normTrace Z b (Real.log ((j : ℝ) + 1))
    set r := (expPoly s p lam (Real.log ((j : ℝ) + 1))).re
    have hr0 : 0 ≤ r := hP _
    have hrM : r ≤ M := (Complex.re_le_norm _).trans (norm_expPoly_le s p lam _)
    have h1 : -(|K| * ((j : ℝ) + 1) ^ (-b)) * r ≤ f * r := mul_le_mul_of_nonneg_right hF hr0
    have h2 : |K| * ((j : ℝ) + 1) ^ (-b) * r ≤ |K| * ((j : ℝ) + 1) ^ (-b) * M :=
      mul_le_mul_of_nonneg_left hrM (mul_nonneg (abs_nonneg K) hpb)
    have h3 : -(|K| * M) * ((j : ℝ) + 1) ^ (-b) ≤ f * r := by linarith
    have hwp : 0 ≤ w j * ((j : ℝ) + 1) ^ (-σ) := mul_nonneg hw0 hp.le
    have h4 := mul_le_mul_of_nonneg_right h3 hwp
    calc -(|K| * M) * (w j * (((j : ℝ) + 1) ^ (-σ) * ((j : ℝ) + 1) ^ (-b)))
        = -(|K| * M) * ((j : ℝ) + 1) ^ (-b) * (w j * ((j : ℝ) + 1) ^ (-σ)) := by ring
      _ ≤ f * r * (w j * ((j : ℝ) + 1) ^ (-σ)) := h4
      _ = w j * f * r * ((j : ℝ) + 1) ^ (-σ) := by ring)
  simpa using key

/-- **Fejér's inequality for the top layer.** Under a lower bound at a sampling set every top
coefficient is bounded by the real one. -/
theorem norm_evenCoeff_le_of_bddBelow (hZ : TemperedConfig Z) (h : TopDepth Z b) (hb0 : 0 < b)
    {K : ℝ}
    (hK : ∀ j : ℕ, w j ≠ 0 → -K ≤ 2 * (lagStructure Z (boxSpline 1 3) (Real.log (j + 1))).re)
    (lam : ℝ) :
    ‖evenCoeff Z (boxSpline 1 3) ((b : ℂ) - lam * I)‖ ≤ (evenCoeff Z (boxSpline 1 3) b).re := by
  set e := evenCoeff Z (boxSpline 1 3) with hedef
  set x := e ((b : ℂ) - lam * I) with hxdef
  -- the pairing with `2 + τe^{iλu} + τ̄e^{−iλu}`, `‖τ‖ ≤ 1`
  have hpair : ∀ τ : ℂ, ‖τ‖ ≤ 1 → 0 ≤ 2 * (e b).re + 2 * (τ * x).re := by
    intro τ hτ
    have hP : ∀ u : ℝ, 0 ≤ (expPoly (Finset.univ : Finset (Fin 3)) ![2, τ, conj τ]
        ![0, lam, -lam] u).re := by
      intro u
      simp only [expPoly, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      set E := cexp (lam * u * I) with hEdef
      have hE1 : ‖E‖ = 1 := by
        rw [hEdef, show (lam : ℂ) * u * I = ((lam * u : ℝ) : ℂ) * I by push_cast; ring,
          Complex.norm_exp_ofReal_mul_I]
      have hconjE : cexp (((-lam : ℝ) : ℂ) * u * I) = conj E := by
        rw [hEdef, ← Complex.exp_conj]
        congr 1
        simp
      rw [hconjE, show ((0 : ℝ) : ℂ) * u * I = 0 by simp, Complex.exp_zero, mul_one,
        ← map_mul, Complex.add_re, Complex.add_re, Complex.conj_re]
      have hnorm : ‖τ * E‖ ≤ 1 := by rw [norm_mul, hE1, mul_one]; exact hτ
      have := Complex.abs_re_le_norm (τ * E)
      have h2 : (2 : ℂ).re = 2 := by norm_num
      rw [h2]
      linarith [(abs_le.mp this).1]
    have key := re_sum_topCoeff_nonneg_of_bddBelow hw hZ h hb0 hK (Finset.univ : Finset (Fin 3))
      ![2, τ, conj τ] ![0, lam, -lam] hP
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at key
    have hb : (b : ℂ) - ((0 : ℝ) : ℂ) * I = b := by simp
    have hbc : (b : ℂ) - ((-lam : ℝ) : ℂ) * I = conj ((b : ℂ) - lam * I) := by
      apply Complex.ext <;> simp
    rw [hb, hbc, evenCoeff_conj, ← hedef, ← hxdef, ← map_mul, Complex.add_re, Complex.add_re,
      Complex.conj_re] at key
    have h2 : ((2 : ℂ) * e b).re = 2 * (e b).re := by simp
    rw [h2] at key
    linarith
  by_cases hx : x = 0
  · rw [hx, norm_zero]
    have := hpair 0 (by simp)
    simp at this
    linarith
  · have hxn : 0 < ‖x‖ := norm_pos_iff.mpr hx
    have := hpair (-(conj x) / ‖x‖) (by
      rw [norm_div, norm_neg, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hxn, div_self hxn.ne'])
    have hτx : (-(conj x) / ‖x‖ * x).re = -‖x‖ := by
      have : -(conj x) / (‖x‖ : ℂ) * x = -(((‖x‖ : ℝ) : ℂ)) := by
        rw [div_mul_eq_mul_div, neg_mul, Complex.conj_mul', neg_div]
        congr 1
        rw [sq, mul_div_assoc, div_self (by exact_mod_cast hxn.ne'), mul_one]
      rw [this, Complex.neg_re, Complex.ofReal_re]
    rw [hτx] at this
    linarith

end Pairing

/-! ### Sufficiency -/

/-- The top layer `F_top(u) = Re Σ_{Re z = b} e_z e^{(z−b)u}`. -/
def topTrace (Z : ZeroConfig) (b u : ℝ) : ℝ :=
  (∑' z, if z.re = b then evenCoeff Z (boxSpline 1 3) z * cexp ((z - b) * u) else 0).re

/-- **The lower layers die out**: `F − F_top → 0`. -/
theorem tendsto_normTrace_sub_topTrace {Z : ZeroConfig} (hZ : TemperedConfig Z) {b : ℝ}
    (h : TopDepth Z b) :
    Tendsto (fun u => normTrace Z b u - topTrace Z b u) atTop (𝓝 0) := by
  set e := evenCoeff Z (boxSpline 1 3) with hedef
  have hE := summable_norm_evenCoeff_spline hZ
  have hc : Tendsto (fun u : ℝ => ∑' z, (if z.re = b then (0 : ℂ) else e z * cexp ((z - b) * u)))
      atTop (𝓝 (∑' _z : ℂ, (0 : ℂ))) := by
    refine tendsto_tsum_of_dominated_convergence hE (fun z => ?_) ?_
    · by_cases hzb : z.re = b
      · simp only [if_pos hzb]; exact tendsto_const_nhds
      · simp only [if_neg hzb]
        by_cases hz : e z = 0
        · simp [hz]
        have hlt : z.re < b := lt_of_le_of_ne (h z hz) hzb
        have hexp : Tendsto (fun u : ℝ => cexp ((z - b) * u)) atTop (𝓝 0) := by
          rw [tendsto_zero_iff_norm_tendsto_zero]
          have hn : ∀ u : ℝ, ‖cexp ((z - b) * u)‖ = Real.exp ((z.re - b) * u) := by
            intro u; rw [Complex.norm_exp]; simp
          simp only [hn]
          exact Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (by linarith))
        simpa using hexp.const_mul (e z)
    · filter_upwards [eventually_ge_atTop 0] with u hu
      intro z
      split_ifs
      · simp
      · exact norm_evenCoeff_mul_cexp_le h z hu
  rw [tsum_zero] at hc
  have hc' := (Complex.continuous_re.tendsto _).comp hc
  rw [Complex.zero_re] at hc'
  refine hc'.congr' ?_
  filter_upwards [eventually_ge_atTop 0] with u hu
  have hs1 : Summable fun z => e z * cexp ((z - b) * u) :=
    Summable.of_norm_bounded hE fun z => norm_evenCoeff_mul_cexp_le h z hu
  have hs2 : Summable fun z => if z.re = b then e z * cexp ((z - b) * u) else 0 :=
    Summable.of_norm_bounded hE fun z => by
      split_ifs
      · exact norm_evenCoeff_mul_cexp_le h z hu
      · simp
  have hsplit : (∑' z, if z.re = b then (0 : ℂ) else e z * cexp ((z - b) * u)) =
      (∑' z, e z * cexp ((z - b) * u)) -
        ∑' z, (if z.re = b then e z * cexp ((z - b) * u) else 0) := by
    rw [← hs1.tsum_sub hs2]
    refine tsum_congr fun z => ?_
    split_ifs <;> ring
  simp only [Function.comp_def, topTrace]
  rw [hsplit, Complex.sub_re, ← ofReal_normTrace hZ u, Complex.ofReal_re]

/-- **A positive top layer keeps the lower side bounded.** If `F_top ≥ δ > 0` on `u ≥ 0`, the spline
traces are bounded below on `u ≥ 0`. -/
theorem bddBelow_of_topTrace_ge {Z : ZeroConfig} (hZ : TemperedConfig Z) {b : ℝ}
    (h : TopDepth Z b) (hb0 : 0 ≤ b) {δ : ℝ} (hδ : 0 < δ)
    (htop : ∀ u : ℝ, 0 ≤ u → δ ≤ topTrace Z b u) :
    ∃ K : ℝ, ∀ u : ℝ, 0 ≤ u → -K ≤ 2 * (lagStructure Z (boxSpline 1 3) u).re := by
  obtain ⟨U, hU⟩ := eventually_atTop.mp
    ((tendsto_normTrace_sub_topTrace hZ h).eventually (Ioo_mem_nhds (neg_lt_zero.mpr hδ) hδ))
  set E := ∑' z, ‖evenCoeff Z (boxSpline 1 3) z‖ with hEdef
  have hE0 : 0 ≤ E := tsum_nonneg fun _ => norm_nonneg _
  refine ⟨E * Real.exp (b * max U 0), fun u hu => ?_⟩
  rw [two_re_lagStructure_eq_normTrace_mul Z b u]
  have hK0 : 0 ≤ E * Real.exp (b * max U 0) := mul_nonneg hE0 (Real.exp_pos _).le
  rcases le_total (max U 0) u with hUu | huU
  · have h1 := (hU u ((le_max_left _ _).trans hUu)).1
    have h2 := htop u hu
    have hpos : 0 ≤ normTrace Z b u := by linarith
    have := mul_nonneg hpos (Real.exp_pos (b * u)).le
    linarith
  · have hF := abs_normTrace_le hZ h hu
    have h1 : Real.exp (b * u) ≤ Real.exp (b * max U 0) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left huU hb0)
    have h3 : -E * Real.exp (b * u) ≤ normTrace Z b u * Real.exp (b * u) :=
      mul_le_mul_of_nonneg_right (abs_le.mp hF).1 (Real.exp_pos _).le
    have h4 : E * Real.exp (b * u) ≤ E * Real.exp (b * max U 0) := mul_le_mul_of_nonneg_left h1 hE0
    linarith

end GaloisForLFunctions.SurfaceOfSpecZ
