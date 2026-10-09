import GaloisForLFunctions.RHTower.LaguerrePolyaFirstOrderInterlacing

/-!
# Double zeros of first-order Laguerre–Pólya images

Let `f` be in the Laguerre–Pólya class with a real zero, let `c ≠ 0` be real, and put
`F = f − c f′`.  If `F` has a double zero at a real point `p` (`F(p) = F′(p) = 0`), then `f` has a
double zero at `p` too (`eq_zero_and_deriv_eq_zero_of_sub_smul_deriv`).

From `F(p) = F′(p) = 0` one gets `f′(p)² − f(p)f″(p) = f′(p)·F′(p) − f″(p)·F(p) = 0`.  The strict
Laguerre inequality forbids this off the zeros of `f`.  Its quantitative polynomial form is
`q(x)² ≤ (x − r)² L₁[q](x)` for a real-rooted `q` with root `r` (`sq_eval_le_mul_laguerreL1`),
from the peel identity `L₁[(X − r)Q] = Q² + (X − r)²L₁[Q]`.  It passes to `f` along approximating
polynomials whose roots converge, by Hurwitz, to the real zero of `f`.  This gives
`f(p)² ≤ K(f′(p)² − f(p)f″(p))` with `K < ∞`, so `f(p) = 0`.
-/

open Polynomial Metric Set Filter Topology

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry

/-- **Quantitative strict Laguerre inequality.**  For a real-rooted real polynomial `q ≠ 0` with a
root `r`: `q(x)² ≤ (x − r)²·(q′(x)² − q(x)q″(x))`. -/
theorem sq_eval_le_mul_laguerreL1 {q : ℝ[X]} (hsp : q.Splits) (hq0 : q ≠ 0) {r : ℝ}
    (hr : q.eval r = 0) (x : ℝ) :
    q.eval x ^ 2 ≤ (x - r) ^ 2 * (laguerreL1 q).eval x := by
  have hfact : q = C q.leadingCoeff * (Multiset.map (fun a => X - C a) q.roots).prod :=
    hsp.eq_prod_roots
  have hrm : r ∈ q.roots := (mem_roots hq0).mpr hr
  set Q : ℝ[X] := (Multiset.map (fun a => X - C a) (q.roots.erase r)).prod with hQ
  have hprod : (Multiset.map (fun a => X - C a) q.roots).prod = (X - C r) * Q := by
    rw [← Multiset.cons_erase hrm, Multiset.map_cons, Multiset.prod_cons]
  have hnonneg : 0 ≤ (laguerreL1 Q).eval x := laguerreL1_prod_eval_nonneg _ x
  set lc := q.leadingCoeff
  have hq : q.eval x = lc * ((x - r) * Q.eval x) := by
    conv_lhs => rw [hfact, hprod]
    simp [eval_mul, eval_sub]
  have hL : (laguerreL1 q).eval x = lc ^ 2 * (Q.eval x ^ 2 + (x - r) ^ 2 * (laguerreL1 Q).eval x) := by
    conv_lhs => rw [hfact, hprod]
    rw [laguerreL1_C_mul, laguerreL1_linear_mul]
    simp [eval_mul, eval_add, eval_pow, eval_sub]
  rw [hq, hL]
  have h4 : 0 ≤ lc ^ 2 * ((x - r) ^ 2) ^ 2 * (laguerreL1 Q).eval x := by positivity
  nlinarith

/-- **Double-zero bridge.**  For `f` in the Laguerre–Pólya class with a real zero and real
`c ≠ 0`: if `F = f − c f′` has `F(p) = F′(p) = 0` at a real `p`, then `f(p) = f′(p) = 0`. -/
theorem eq_zero_and_deriv_eq_zero_of_sub_smul_deriv {f : ℂ → ℂ}
    (hf : GaloisForLFunctions.HTGeometry.LaguerrePolya f)
    {x₀ : ℝ} (hx₀ : f x₀ = 0) {c : ℝ} (hc : c ≠ 0) {p : ℝ}
    (h0 : f p - (c : ℂ) * deriv f p = 0)
    (h1 : deriv (fun z => f z - (c : ℂ) * deriv f z) p = 0) :
    f p = 0 ∧ deriv f p = 0 := by
  have hfd : Differentiable ℂ f := GaloisForLFunctions.HTGeometry.LaguerrePolya.differentiable hf
  have hdd : Differentiable ℂ (deriv f) := fun z => ((hfd.analyticAt z).deriv).differentiableAt
  have hcC : (c : ℂ) ≠ 0 := by exact_mod_cast hc
  have h1' : deriv f p - (c : ℂ) * deriv (deriv f) p = 0 := by
    have h : HasDerivAt (fun z => f z - (c : ℂ) * deriv f z)
        (deriv f p - (c : ℂ) * deriv (deriv f) p) p :=
      (hfd p).hasDerivAt.sub ((hdd p).hasDerivAt.const_mul (c : ℂ))
    rw [h.deriv] at h1
    exact h1
  suffices hfp : f p = 0 by
    refine ⟨hfp, ?_⟩
    rw [hfp, zero_sub, neg_eq_zero] at h0
    exact (mul_eq_zero.mp h0).resolve_left hcC
  by_contra hfp
  -- the Laguerre expression vanishes at `p`
  have hL : deriv f p ^ 2 - f p * deriv (deriv f) p = 0 := by
    linear_combination deriv f p * h1' - deriv (deriv f) p * h0
  obtain ⟨P, hsplit, hconv⟩ := hf
  have hPd : ∀ m, Differentiable ℂ (polyEvalC (P m)) := fun m => differentiable_polyEvalC _
  have hder := tendstoLocallyUniformly_iterate_deriv hconv hPd
  -- pointwise convergence of the values and the first two derivatives at real points
  have hval : ∀ (j : ℕ) (x : ℝ), Tendsto
      (fun m => ((((⇑derivative)^[j] (P m)).eval x : ℝ) : ℂ)) atTop (𝓝 (deriv^[j] f x)) := by
    intro j x
    have h := (tendstoLocallyUniformlyOn_univ.mpr (hder j)).tendsto_at (mem_univ (x : ℂ))
    refine h.congr fun m => ?_
    rw [iterate_deriv_polyEvalC, polyEvalC_ofReal]
  have hreal : ∀ (j : ℕ) (x : ℝ), ∃ v : ℝ, deriv^[j] f x = v ∧
      Tendsto (fun m => ((⇑derivative)^[j] (P m)).eval x) atTop (𝓝 v) := by
    intro j x
    have h := hval j x
    have hre := (Complex.continuous_re.tendsto _).comp h
    simp only [Function.comp_def, Complex.ofReal_re] at hre
    refine ⟨(deriv^[j] f x).re, ?_, hre⟩
    have h2 := (Complex.continuous_ofReal.tendsto _).comp hre
    simp only [Function.comp_def] at h2
    exact tendsto_nhds_unique h h2
  obtain ⟨α, hα, hαt⟩ := hreal 0 p
  obtain ⟨β, hβ, hβt⟩ := hreal 1 p
  obtain ⟨δ, hδ, hδt⟩ := hreal 2 p
  simp only [Function.iterate_zero, id_eq, Function.iterate_one] at hα hαt hβ hβt
  have hδ' : deriv (deriv f) p = δ := by simpa [Function.iterate_succ] using hδ
  have hδt' : Tendsto (fun m => (derivative (derivative (P m))).eval p) atTop (𝓝 δ) := by
    simpa [Function.iterate_succ] using hδt
  have hα0 : α ≠ 0 := by
    intro h; apply hfp; rw [hα, h, Complex.ofReal_zero]
  have hLr : β ^ 2 - α * δ = 0 := by
    rw [hα, hβ, hδ'] at hL
    exact_mod_cast hL
  -- an isolated zero of `f` at `x₀`
  obtain ⟨r₀, hr₀, hiso⟩ : ∃ r₀ > 0, ∀ w, w ≠ (x₀ : ℂ) → dist w x₀ < r₀ → f w ≠ 0 := by
    rcases (hfd.analyticAt (x₀ : ℂ)).eventually_eq_zero_or_eventually_ne_zero with h | h
    · exfalso
      have hon : AnalyticOnNhd ℂ f univ := fun z _ => hfd.analyticAt z
      have hfreq : ∃ᶠ z in 𝓝[≠] (x₀ : ℂ), f z = 0 := (h.filter_mono nhdsWithin_le_nhds).frequently
      exact hfp (hon.eqOn_zero_of_preconnected_of_frequently_eq_zero isPreconnected_univ
        (mem_univ _) hfreq (mem_univ _))
    · obtain ⟨U, hU, hUsub⟩ := Filter.eventually_iff_exists_mem.mp h
      obtain ⟨r₀, hr₀, hball⟩ := Metric.mem_nhdsWithin_iff.mp hU
      exact ⟨r₀, hr₀, fun w hw hd => hUsub w (hball ⟨hd, hw⟩)⟩
  set r := r₀ / 2 with hr
  have hr0 : 0 < r := by positivity
  have hsphere : ∀ w ∈ sphere (x₀ : ℂ) r, f w ≠ 0 := by
    intro w hw
    rw [mem_sphere] at hw
    refine hiso w (fun h => ?_) (by rw [hw]; linarith)
    rw [h, dist_self] at hw; linarith
  have hroots := eventually_exists_zero_closedBall_of_tendstoLocallyUniformly hconv hfd
    (Eventually.of_forall hPd) hr0 hx₀ hsphere
  -- eventually `P m ≠ 0`
  have hne : ∀ᶠ m in atTop, P m ≠ 0 := by
    have h := hαt.eventually_ne hα0
    filter_upwards [h] with m hm hP
    apply hm; rw [hP]; simp
  -- the quantitative inequality along the sequence
  set K : ℝ := (|p - x₀| + r) ^ 2 with hK
  have hineq : ∀ᶠ m in atTop, ((P m).eval p) ^ 2 ≤
      K * (((derivative (P m)).eval p) ^ 2 -
        (P m).eval p * (derivative (derivative (P m))).eval p) := by
    filter_upwards [hroots, hne] with m hm hPm
    obtain ⟨w, hw, hw0⟩ := hm
    obtain ⟨y, rfl, hy⟩ := exists_real_of_polyEvalC_eq_zero (hsplit m) hPm hw0
    have hyd : |y - x₀| ≤ r := by
      rw [mem_closedBall, Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real,
        Real.norm_eq_abs] at hw
      exact hw
    have h1 := sq_eval_le_mul_laguerreL1 (hsplit m) hPm hy p
    have hL0 : 0 ≤ (laguerreL1 (P m)).eval p := laguerreL1_eval_nonneg (hsplit m) p
    have hpy : (p - y) ^ 2 ≤ K := by
      rw [hK]
      have : |p - y| ≤ |p - x₀| + r := by
        calc |p - y| = |(p - x₀) - (y - x₀)| := by ring_nf
          _ ≤ |p - x₀| + |y - x₀| := abs_sub _ _
          _ ≤ |p - x₀| + r := by linarith
      calc (p - y) ^ 2 = |p - y| ^ 2 := (sq_abs _).symm
        _ ≤ (|p - x₀| + r) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) this 2
    have hev : (laguerreL1 (P m)).eval p = ((derivative (P m)).eval p) ^ 2 -
        (P m).eval p * (derivative (derivative (P m))).eval p := by
      simp [laguerreL1, eval_sub, eval_pow, eval_mul]
    rw [← hev]
    exact h1.trans (mul_le_mul_of_nonneg_right hpy hL0)
  have hlim : Tendsto (fun m => K * (((derivative (P m)).eval p) ^ 2 -
      (P m).eval p * (derivative (derivative (P m))).eval p) - ((P m).eval p) ^ 2) atTop
      (𝓝 (K * (β ^ 2 - α * δ) - α ^ 2)) :=
    ((tendsto_const_nhds.mul ((hβt.pow 2).sub (hαt.mul hδt'))).sub (hαt.pow 2))
  have hge : 0 ≤ K * (β ^ 2 - α * δ) - α ^ 2 :=
    ge_of_tendsto hlim (hineq.mono fun m hm => by linarith)
  rw [hLr, mul_zero, zero_sub, neg_nonneg] at hge
  exact hα0 (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp (le_antisymm hge (sq_nonneg α)))

end

end RHTower
