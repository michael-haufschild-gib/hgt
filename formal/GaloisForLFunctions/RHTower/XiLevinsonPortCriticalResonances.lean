import GaloisForLFunctions.RHTower.XiCriticalityPortZeros
import GaloisForLFunctions.RHTower.XiCosineShiftMeltingLaw

/-!
# The canonical producer: the Levinson port is lossless iff RH, and then critical

For `λ > 0` let `V_λ(z) = Ξ(z) + iλΞ'(z)` (in `s = ½ + iz`: `ξ(s) − λξ'(s)`). On the real line
`Re V_λ = Ξ`. This is the canonical PTR producer (the Levinson / Hedenmalm port).

* `roots_add_derivative_im_neg`: if all roots of a polynomial `P` have `Im < 0`, so do all roots of
  `P + iλP'`. At a root `r` with `Im r ≥ 0`, `P'(r)/P(r) = i/λ`. But `−Im P'/P(r)` is a sum of
  Poisson terms of depth `Im r − Im ρ > 0`, hence `≥ 0`.
* `tendstoLocallyUniformly_comp_add`: a locally uniform limit survives a vanishing shift of the
  argument.
* `strictLowerPolyaClass_levinsonPort`: under RH, `V_λ` is a locally uniform limit of `p_m + iλp_m'`,
  where `p_m` are the Hadamard ball truncations of `Ξ` shifted by `i/(m+1)`. Their roots `γ − i/(m+1)`
  are strictly below the real axis.
* `riemannHypothesis_iff_strictLowerPolyaClass_levinsonPort`: RH ⟺ `V_λ` is strict lower Pólya.
* `eventually_card_levinson_resonances_ge`: **the canonical producer is critical, uniformly in `λ`.**
  Under RH there is one threshold `T₀` such that for `T ≥ T₀` and *every* `λ > 0`, the zeros of
  `ξ − λξ'` with `½ ≤ Re s ≤ ½ + 2·10⁶⁰/log T` and `3T^{½} − 1 ≤ Im s ≤ T + 1` number at least
  `T log T / 10⁷⁹`.
-/

noncomputable section

open Complex Filter Topology Set Polynomial
open scoped Pointwise
open GaloisForLFunctions.HTGeometry (neg_im_logDeriv_eval_eq_sum poissonTerm)

namespace RHTower

/-- The Levinson port `Ξ + iλΞ'`. -/
def levinsonPort (lam : ℝ) (z : ℂ) : ℂ := XiC z + ((lam : ℂ) * I) * deriv XiC z

/-- `Ξ'` is real on the real line. -/
theorem deriv_XiC_ofReal_im_eq_zero (x : ℝ) : (deriv XiC (x : ℂ)).im = 0 := by
  have h1 : HasDerivAt (fun t : ℝ => XiC (t : ℂ)) (deriv XiC (x : ℂ)) x :=
    (XiC_differentiable (x : ℂ)).hasDerivAt.comp_ofReal
  have h2 : HasDerivAt (fun t : ℝ => (XiC (t : ℂ)).im) (deriv XiC (x : ℂ)).im x :=
    Complex.imCLM.hasFDerivAt.comp_hasDerivAt x h1
  have h3 : (fun t : ℝ => (XiC (t : ℂ)).im) = fun _ => (0 : ℝ) := by
    funext t; rw [XiC_ofReal]; simp
  rw [h3] at h2
  exact h2.unique (hasDerivAt_const x 0)

/-- **`Re V_λ = Ξ` on the real line.** -/
theorem levinsonPort_re (lam t : ℝ) : Xi t = (levinsonPort lam t).re := by
  have hd := deriv_XiC_ofReal_im_eq_zero t
  simp only [levinsonPort, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, hd, XiC_ofReal]
  ring

/-- In the `s`-variable, `V_λ(z) = ξ(s) − λ ξ'(s)` with `s = ½ + iz`. -/
theorem levinsonPort_eq (lam : ℝ) (z : ℂ) :
    levinsonPort lam z = xi (1 / 2 + z * I) - (lam : ℂ) * deriv xi (1 / 2 + z * I) := by
  have hd : deriv XiC z = deriv xi (1 / 2 + z * I) * I := by
    have h1 : HasDerivAt (fun w : ℂ => 1 / 2 + w * I) I z := by
      simpa using ((hasDerivAt_id z).mul_const I).const_add (1 / 2 : ℂ)
    have h2 := (xi_differentiable (1 / 2 + z * I)).hasDerivAt.comp z h1
    exact h2.deriv
  rw [levinsonPort, hd, XiC]
  ring_nf
  rw [Complex.I_sq]
  ring

/-- **Roots of `P + iλP'`.** If every root of `P` has negative imaginary part, so does every root
of `P + iλP'`, `λ > 0`. -/
theorem roots_add_derivative_im_neg {P : ℂ[X]} {lam : ℝ} (hlam : 0 < lam)
    (hP : ∀ r ∈ P.roots, r.im < 0) :
    ∀ r ∈ (P + C ((lam : ℂ) * I) * derivative P).roots, r.im < 0 := by
  intro r hr
  by_contra hge
  push Not at hge
  have hP0 : P ≠ 0 := by
    rintro rfl
    simp at hr
  have hQ := (Polynomial.isRoot_of_mem_roots hr).eq_zero
  simp only [eval_add, eval_mul, eval_C] at hQ
  have hPr : P.eval r ≠ 0 := by
    intro h0
    linarith [hP r ((Polynomial.mem_roots hP0).mpr h0)]
  have hr' : r = ((r.re : ℝ) : ℂ) + (r.im : ℝ) * I := (Complex.re_add_im r).symm
  have hsum := neg_im_logDeriv_eval_eq_sum (p := P) (h := r.im) (t := r.re) (by rwa [← hr'])
  rw [← hr'] at hsum
  have hlam0 : (lam : ℂ) ≠ 0 := by exact_mod_cast hlam.ne'
  have hratio : (derivative P).eval r / P.eval r = I / (lam : ℂ) := by
    rw [div_eq_div_iff hPr hlam0]
    have : (derivative P).eval r * ((lam : ℂ) * I) = -P.eval r := by linear_combination hQ
    have hI : I * I = -1 := Complex.I_mul_I
    linear_combination (-I) * this + ((derivative P).eval r * (lam : ℂ)) * hI
  rw [hratio] at hsum
  have him : (I / (lam : ℂ)).im = 1 / lam := by
    rw [Complex.div_ofReal_im]; simp
  rw [him] at hsum
  have hnn : 0 ≤ (P.roots.map fun ρ => poissonTerm ρ.re (r.im - ρ.im) r.re).sum :=
    Multiset.sum_nonneg fun x hx => by
      obtain ⟨ρ, hρ, rfl⟩ := Multiset.mem_map.mp hx
      have : 0 < r.im - ρ.im := by linarith [hP ρ hρ]
      unfold poissonTerm
      positivity
  have : 0 < 1 / lam := by positivity
  linarith

/-- **Vanishing shifts.** If `F_m → f` locally uniformly, `f` is continuous and `c_m → 0`, then
`F_m(z + c_m) → f(z)` locally uniformly. -/
theorem tendstoLocallyUniformly_comp_add {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ}
    (hF : TendstoLocallyUniformly F f atTop) (hf : Continuous f) {c : ℕ → ℂ}
    (hc : Tendsto c atTop (𝓝 0)) :
    TendstoLocallyUniformly (fun m z => F m (z + c m)) f atTop := by
  rw [tendstoLocallyUniformly_iff_forall_isCompact] at hF ⊢
  intro K hK
  set K' : Set ℂ := K + Metric.closedBall (0 : ℂ) 1 with hK'def
  have hK' : IsCompact K' := hK.add (isCompact_closedBall 0 1)
  have hFK' := Metric.tendstoUniformlyOn_iff.mp (hF K' hK')
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨δ, hδ, hδf⟩ := Metric.uniformContinuousOn_iff.mp
    (hK'.uniformContinuousOn_of_continuous hf.continuousOn) (ε / 2) (by positivity)
  have hsmall : ∀ᶠ m in atTop, ‖c m‖ < min δ 1 := by
    have := hc.eventually (Metric.ball_mem_nhds (0 : ℂ) (lt_min hδ one_pos))
    filter_upwards [this] with m hm
    simpa [Metric.mem_ball, dist_zero_right] using hm
  filter_upwards [hFK' (ε / 2) (by positivity), hsmall] with m hm hcm z hz
  have hzK' : z ∈ K' := by
    have := Set.add_mem_add hz (Metric.mem_closedBall_self (x := (0 : ℂ)) zero_le_one)
    simpa using this
  have hzc : z + c m ∈ K' := by
    refine Set.add_mem_add hz ?_
    rw [Metric.mem_closedBall, dist_zero_right]
    exact (hcm.trans_le (min_le_right _ _)).le
  have hd : dist z (z + c m) < δ := by
    rw [dist_eq_norm, sub_add_cancel_left, norm_neg]
    exact hcm.trans_le (min_le_left _ _)
  calc dist (f z) (F m (z + c m)) ≤ dist (f z) (f (z + c m)) + dist (f (z + c m)) (F m (z + c m)) :=
        dist_triangle _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add (hδf z hzK' (z + c m) hzc hd) (hm _ hzc)
    _ = ε := by ring

/-- The shifted Hadamard ball truncation of `Ξ`, with roots `γ − i/(m+1)`. -/
def levinsonApprox (m : ℕ) : ℂ[X] :=
  C (XiC 0) * ∏ q ∈ xiZeroBall m,
    (1 - C (xiSpectralPoint q)⁻¹ * (X + C (((1 / ((m : ℝ) + 1) : ℝ) : ℂ) * I)))

theorem eval_levinsonApprox (m : ℕ) (z : ℂ) :
    (levinsonApprox m).eval z = XiC 0 * ∏ q ∈ xiZeroBall m,
      (1 - (z + (((1 / ((m : ℝ) + 1) : ℝ) : ℂ) * I)) / xiSpectralPoint q) := by
  simp only [levinsonApprox, eval_mul, eval_C, eval_prod, eval_sub, eval_one, eval_add, eval_X]
  congr 1
  refine Finset.prod_congr rfl fun q _ => ?_
  ring

/-- Under RH the shifted truncations have all roots strictly below the real axis. -/
theorem levinsonApprox_roots_im_neg (hRH : RiemannHypothesis) (m : ℕ) :
    ∀ r ∈ (levinsonApprox m).roots, r.im < 0 := by
  intro r hr
  have hr0 : (levinsonApprox m).eval r = 0 := (Polynomial.isRoot_of_mem_roots hr).eq_zero
  rw [eval_levinsonApprox, mul_eq_zero, Finset.prod_eq_zero_iff] at hr0
  rcases hr0 with h0 | ⟨q, _, hq⟩
  · exact absurd h0 XiC_zero_ne_zero
  · have hγ := xiSpectralPoint_ne_zero q
    have heq : r + (((1 / ((m : ℝ) + 1) : ℝ) : ℂ) * I) = xiSpectralPoint q := by
      rw [sub_eq_zero, eq_comm, div_eq_one_iff_eq hγ] at hq; exact hq
    have him := congrArg Complex.im heq
    simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, mul_one] at him
    rw [xiSpectralPoint_im_eq_zero_of_rh hRH q] at him
    have : 0 < 1 / ((m : ℝ) + 1) := by positivity
    linarith

/-- The shifted truncations converge to `Ξ` locally uniformly. -/
theorem tendstoLocallyUniformly_levinsonApprox :
    TendstoLocallyUniformly (fun (m : ℕ) (z : ℂ) => (levinsonApprox m).eval z) XiC atTop := by
  have hconv := tendstoLocallyUniformly_prod_xiZeroBall
  have hcont : Continuous xiCanonicalProduct :=
    hconv.continuous (Eventually.of_forall fun m => by fun_prop).frequently
  have hc : TendstoLocallyUniformly (fun (_ : ℕ) (_ : ℂ) => XiC 0) (fun _ => XiC 0) atTop :=
    fun u hu x => ⟨univ, univ_mem, Eventually.of_forall fun _ y _ => refl_mem_uniformity hu⟩
  have hmul := hc.mul₀ hconv continuous_const hcont
  have hXi : TendstoLocallyUniformly
      (fun (m : ℕ) (w : ℂ) => XiC 0 * ∏ q ∈ xiZeroBall m, (1 - w / xiSpectralPoint q)) XiC atTop := by
    refine hmul.congr_right fun w => ?_
    have h := congrFun XiC_eq_constant_mul_canonicalProduct w
    simp only [Pi.mul_apply] at h
    exact h.symm
  have hshift : Tendsto (fun m : ℕ => (((1 / ((m : ℝ) + 1) : ℝ) : ℂ) * I)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun m : ℕ => (1 / ((m : ℝ) + 1) : ℝ)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have h2 := (Complex.continuous_ofReal.tendsto 0).comp h1
    simpa using h2.mul_const I
  have := tendstoLocallyUniformly_comp_add hXi XiC_differentiable.continuous hshift
  refine this.congr fun m z => ?_
  exact (eval_levinsonApprox m z).symm

/-- **Under RH the Levinson port is strict lower Pólya.** -/
theorem strictLowerPolyaClass_levinsonPort (hRH : RiemannHypothesis) {lam : ℝ} (hlam : 0 < lam) :
    StrictLowerPolyaClass (levinsonPort lam) := by
  refine ⟨fun m => levinsonApprox m + C ((lam : ℂ) * I) * derivative (levinsonApprox m),
    fun m => roots_add_derivative_im_neg hlam (levinsonApprox_roots_im_neg hRH m), ?_⟩
  have hU := tendstoLocallyUniformlyOn_univ.mpr tendstoLocallyUniformly_levinsonApprox
  have hD := hU.deriv (Eventually.of_forall fun m =>
    (Polynomial.differentiable (levinsonApprox m)).differentiableOn) isOpen_univ
  have hD' : TendstoLocallyUniformly (fun (m : ℕ) (z : ℂ) => (derivative (levinsonApprox m)).eval z)
      (deriv XiC) atTop := by
    refine (tendstoLocallyUniformlyOn_univ.mp hD).congr fun m z => ?_
    simp [Polynomial.deriv]
  have hdc : Continuous (deriv XiC) :=
    continuous_iff_continuousAt.mpr fun z =>
      ((XiC_differentiable.analyticAt z).deriv).continuousAt
  have hc : TendstoLocallyUniformly (fun (_ : ℕ) (_ : ℂ) => (lam : ℂ) * I)
      (fun _ => (lam : ℂ) * I) atTop :=
    fun u hu x => ⟨univ, univ_mem, Eventually.of_forall fun _ y _ => refl_mem_uniformity hu⟩
  have hmul := hc.mul₀ hD' continuous_const hdc
  have hsum := tendstoLocallyUniformly_levinsonApprox.add hmul
  refine (hsum.congr_right fun z => ?_).congr fun m z => ?_
  · simp [levinsonPort]
  · simp [eval_add, eval_mul, eval_C]

/-- **The canonical producer is lossless exactly under RH.** -/
theorem riemannHypothesis_iff_strictLowerPolyaClass_levinsonPort {lam : ℝ} (hlam : 0 < lam) :
    RiemannHypothesis ↔ StrictLowerPolyaClass (levinsonPort lam) :=
  ⟨fun hRH => strictLowerPolyaClass_levinsonPort hRH hlam,
    fun h => riemannHypothesis_of_strictLowerPolya_realization h (levinsonPort_re lam)⟩

/-- **The canonical producer is critical, uniformly in `λ`.** Under RH, for all large `T` and every
`λ > 0`, every finite set containing the zeros of `ξ − λξ'` with `½ ≤ Re s ≤ ½ + 2·10⁶⁰/log T` and
`3T^{½} − 1 ≤ Im s ≤ T + 1` has at least `T log T / 10⁷⁹` elements. -/
theorem eventually_card_levinson_resonances_ge (hRH : RiemannHypothesis) :
    ∀ᶠ T : ℝ in atTop, ∀ lam : ℝ, 0 < lam → ∀ S : Finset ℂ,
      (∀ s : ℂ, xi s - (lam : ℂ) * deriv xi s = 0 → 1 / 2 ≤ s.re →
        s.re ≤ 1 / 2 + 2 * 10 ^ 60 / Real.log T → 3 * T ^ (1 / 2 : ℝ) - 1 ≤ s.im →
          s.im ≤ T + 1 → s ∈ S) →
      T * Real.log T / 10 ^ 79 ≤ S.card := by
  filter_upwards [eventually_card_critical_resonances_ge_of_rh hRH] with T hT lam hlam S hS
  have hE := strictLowerPolyaClass_levinsonPort hRH hlam
  set F : Finset ℂ := S.image fun s => (s - 1 / 2) / I with hF
  have hcard : F.card ≤ S.card := Finset.card_image_le
  refine (hT (levinsonPort lam) hE (levinsonPort_re lam) F ?_).trans (by exact_mod_cast hcard)
  intro z hz h1 h2 h3 h4
  have hs : (1 / 2 + z * I - 1 / 2) / I = z := by
    rw [add_sub_cancel_left, mul_div_assoc, div_self Complex.I_ne_zero, mul_one]
  have hre : (1 / 2 + z * I).re = 1 / 2 - z.im := by simp; ring
  have him : (1 / 2 + z * I).im = z.re := by simp
  rw [hF, Finset.mem_image]
  refine ⟨1 / 2 + z * I, hS _ ?_ ?_ ?_ ?_ ?_, hs⟩
  · rw [← levinsonPort_eq]; exact hz
  · rw [hre]; linarith
  · rw [hre]; linarith
  · rw [him]; exact h1
  · rw [him]; exact h2

end RHTower
