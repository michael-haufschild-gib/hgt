import GaloisForLFunctions.RHTower.RiemannKernelCuspSeries
import GaloisForLFunctions.RHTower.HodgeNyquistExclusion
import GaloisForLFunctions.RHTower.XiEntireReal

/-!
# No local port from the cosine producer to Ξ

For real `h` let `A_h(z) = ∫ Φ(u) cosh(hu) e^{izu} du = (Ξ(z − ih) + Ξ(z + ih))/2`, the cosine
producer `cos(hD)Ξ` (`cosineProducer_eq_average`).

**Theorem** (`not_exists_polynomial_port_cosineProducer`). If `h ∉ 2ℤ`, there are no complex
polynomials `Q₀, …, Q_N` with `Σ_k Q_k(t) A_h^{(k)}(t) = Ξ(t)` for all real `t`. So no finite-order
linear differential operator with polynomial coefficients maps `A_h` to `Ξ`, whether or not it
preserves real zeros.

**Proof.**
* Kernel side. Finite sums of `c u^a e^{βu} Φ^{(j)}(u)` (`KFun`) are closed under `d/du` and under
  multiplication by `u`. On transforms, `D^k` is multiplication by `(iu)^k`
  (`iteratedDeriv_paperFT_kfun`), and multiplication by `z` is `i d/du` (`mul_paperFT_kfun`). So the
  operator becomes a polynomial-coefficient differential operator `L` in `u` applied to
  `Φ cosh(h·)`. Fourier injectivity (`eq_zero_of_paperFT_real_eq_zero`) gives
  `L[Φ cosh(h·)] = Φ`.
* Head and tail. `Φ^{(j)}` is a cusp series. Its `n = 1` term is `e^{−πe^{2u}}` times an
  exponential polynomial, and its terms `n ≥ 2` are `O(e^{Cu} e^{−4πe^{2u}})`
  (`KFun.exists_tail_le`). A vanishing
  kernel function therefore has vanishing leading exponential polynomial
  (`KFun.head_eq_zero_of_eval_eq_zero`), by the leading-term lemma `eq_zero_of_tendsto_mul_cexp`.
* Exponent classes. `d/du` and multiplication by `u` keep `β`, so every exponent of the head of
  `L[Φ cosh(h·)]` lies in `±h + 1/2 + 2ℕ`. The head of `Φ` has the exponent `9/2` with coefficient
  `4π²` (`head_negPhi_nine_halves`), and for `h ∉ 2ℤ` the exponent `9/2` is not of the form
  `±h + 1/2 + 2i`.
-/

open Complex MeasureTheory Filter Topology Set Polynomial
open scoped Real

noncomputable section

namespace RHTower.LocalPort

/-! ## Exponential polynomials -/

abbrev ExpPoly := ℝ →₀ ℂ[X]

/-- `E(u) = Σ_γ p_γ(u) e^{γu}`. -/
def expPolyEval (E : ExpPoly) (u : ℝ) : ℂ := E.sum fun γ p => p.eval (u : ℂ) * cexp (γ * u)

theorem expPolyEval_add (E F : ExpPoly) (u : ℝ) :
    expPolyEval (E + F) u = expPolyEval E u + expPolyEval F u := by
  unfold expPolyEval
  exact Finsupp.sum_add_index' (fun _ => by simp) (fun _ _ _ => by simp [add_mul])

theorem expPolyEval_single (γ : ℝ) (p : ℂ[X]) (u : ℝ) :
    expPolyEval (Finsupp.single γ p) u = p.eval (u : ℂ) * cexp (γ * u) := by
  unfold expPolyEval
  simp [Finsupp.sum_single_index]

theorem tendsto_pow_mul_cexp_neg (i : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun u : ℝ => (u : ℂ) ^ i * cexp (-(δ * u))) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have h := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero i).comp
    (tendsto_id.const_mul_atTop hδ)
  have h2 := h.const_mul (δ ^ i)⁻¹
  rw [mul_zero] at h2
  refine h2.congr' ?_
  filter_upwards [eventually_ge_atTop 0] with u hu
  simp only [Function.comp_def, id]
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hu,
    show -((δ : ℂ) * u) = ((-(δ * u) : ℝ) : ℂ) by push_cast; ring, Complex.norm_exp_ofReal,
    mul_pow]
  field_simp

theorem tendsto_poly_mul_cexp_neg (q : ℂ[X]) {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun u : ℝ => q.eval (u : ℂ) * cexp (-(δ * u))) atTop (𝓝 0) := by
  have h : Tendsto (fun u : ℝ => ∑ i ∈ Finset.range (q.natDegree + 1),
      q.coeff i * ((u : ℂ) ^ i * cexp (-(δ * u)))) atTop (𝓝 0) := by
    have := tendsto_finsetSum (Finset.range (q.natDegree + 1))
      (fun i _ => (tendsto_pow_mul_cexp_neg i hδ).const_mul (q.coeff i))
    simpa using this
  refine h.congr fun u => ?_
  rw [eval_eq_sum_range, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => by ring

theorem eq_zero_of_tendsto_eval (p : ℂ[X])
    (h : Tendsto (fun u : ℝ => p.eval (u : ℂ)) atTop (𝓝 0)) : p = 0 := by
  by_contra hp
  rcases lt_or_ge 0 p.degree with hdeg | hdeg
  · have hz : Tendsto (fun u : ℝ => ‖(u : ℂ)‖) atTop atTop := by
      simpa [Complex.norm_real, Real.norm_eq_abs] using tendsto_abs_atTop_atTop
    have h1 := p.tendsto_norm_atTop hdeg hz
    have h2 := h.norm
    rw [norm_zero] at h2
    exact not_tendsto_nhds_of_tendsto_atTop h1 0 h2
  · rw [eq_C_of_degree_le_zero hdeg] at h hp
    simp only [eval_C] at h
    have := tendsto_nhds_unique tendsto_const_nhds h
    exact hp (by rw [this, C_0])

/-- **Leading-term lemma.** An exponential polynomial that decays faster than every exponential
is zero. -/
theorem eq_zero_of_tendsto_mul_cexp (E : ExpPoly)
    (h : ∀ M : ℝ, Tendsto (fun u : ℝ => expPolyEval E u * cexp (M * u)) atTop (𝓝 0)) : E = 0 := by
  classical
  by_contra hE
  have hs : E.support.Nonempty := Finsupp.support_nonempty_iff.mpr hE
  set γ := E.support.max' hs with hγ
  have hγmem : γ ∈ E.support := Finset.max'_mem _ hs
  have hp : E γ ≠ 0 := Finsupp.mem_support_iff.mp hγmem
  have hsplit : ∀ u : ℝ, expPolyEval E u * cexp (-γ * u) =
      (E γ).eval (u : ℂ) + ∑ β ∈ E.support.erase γ, (E β).eval (u : ℂ) * cexp (-((γ - β) * u)) := by
    intro u
    unfold expPolyEval
    rw [Finsupp.sum, Finset.sum_mul, ← Finset.add_sum_erase _ _ hγmem]
    congr 1
    · rw [mul_assoc, ← Complex.exp_add]
      have : (γ : ℂ) * u + -γ * u = 0 := by ring
      rw [this, Complex.exp_zero, mul_one]
    · refine Finset.sum_congr rfl fun β _ => ?_
      rw [mul_assoc, ← Complex.exp_add]
      congr 2
      ring
  have hrest : Tendsto (fun u : ℝ => ∑ β ∈ E.support.erase γ,
      (E β).eval (u : ℂ) * cexp (-((γ - β) * u))) atTop (𝓝 0) := by
    have := tendsto_finsetSum (E.support.erase γ) (fun β hβ => (show Tendsto
        (fun u : ℝ => (E β).eval (u : ℂ) * cexp (-((γ - β) * u))) atTop (𝓝 0) from by
      have hlt : β < γ := lt_of_le_of_ne (Finset.le_max' _ _ (Finset.mem_of_mem_erase hβ))
        (Finset.ne_of_mem_erase hβ)
      have := tendsto_poly_mul_cexp_neg (E β) (sub_pos.mpr hlt)
      refine this.congr fun u => ?_
      push_cast; ring_nf))
    simpa using this
  have hmain := (h (-γ)).sub hrest
  rw [sub_zero] at hmain
  have hp0 : Tendsto (fun u : ℝ => (E γ).eval (u : ℂ)) atTop (𝓝 0) := by
    refine hmain.congr fun u => ?_
    have := hsplit u
    push_cast at this ⊢
    rw [this]; ring
  exact hp (eq_zero_of_tendsto_eval _ hp0)



/-- A kernel monomial `c · u^a · e^{βu} · Φ^{(j)}(u)`. -/
structure KTerm where
  c : ℂ
  a : ℕ
  β : ℝ
  j : ℕ

def KTerm.eval (t : KTerm) (u : ℝ) : ℂ :=
  t.c * (u : ℂ) ^ t.a * cexp (t.β * u) * riemannKernelDeriv t.j u

/-- Finite sums of kernel monomials. -/
abbrev KFun := List KTerm

def KFun.eval (F : KFun) (u : ℝ) : ℂ := (F.map fun t => t.eval u).sum

@[simp] theorem KFun.eval_nil (u : ℝ) : KFun.eval [] u = 0 := rfl

@[simp] theorem KFun.eval_cons (t : KTerm) (F : KFun) (u : ℝ) :
    KFun.eval (t :: F) u = t.eval u + KFun.eval F u := rfl

theorem KFun.eval_append (F G : KFun) (u : ℝ) :
    KFun.eval (F ++ G) u = KFun.eval F u + KFun.eval G u := by
  unfold KFun.eval; rw [List.map_append, List.sum_append]

/-- Derivative of one monomial. -/
def KTerm.d (t : KTerm) : KFun :=
  [⟨t.c * t.a, t.a - 1, t.β, t.j⟩, ⟨t.c * t.β, t.a, t.β, t.j⟩, ⟨t.c, t.a, t.β, t.j + 1⟩]

def KFun.d (F : KFun) : KFun := F.flatMap KTerm.d

theorem KTerm.hasDerivAt (t : KTerm) (u : ℝ) :
    HasDerivAt t.eval (KFun.eval t.d u) u := by
  have h1 : HasDerivAt (fun x : ℝ => (x : ℂ) ^ t.a) (t.a * (u : ℂ) ^ (t.a - 1)) u := by
    simpa using (hasDerivAt_pow t.a (u : ℂ)).comp_ofReal
  have h2 : HasDerivAt (fun x : ℝ => cexp (t.β * x)) (t.β * cexp (t.β * u)) u := by
    have h := ((hasDerivAt_id (u : ℂ)).const_mul (t.β : ℂ)).cexp.comp_ofReal
    simpa [mul_comm] using h
  have h3 := hasDerivAt_riemannKernelDeriv t.j u
  have h := ((h1.const_mul t.c).mul h2).mul h3
  have hv : KFun.eval (KTerm.d t) u = t.c * (t.a * (u : ℂ) ^ (t.a - 1)) * cexp (t.β * u) *
      riemannKernelDeriv t.j u + t.c * (u : ℂ) ^ t.a * (t.β * cexp (t.β * u)) *
      riemannKernelDeriv t.j u + t.c * (u : ℂ) ^ t.a * cexp (t.β * u) *
      riemannKernelDeriv (t.j + 1) u := by
    simp only [KTerm.d, KFun.eval_cons, KFun.eval_nil, KTerm.eval, add_zero]
    ring
  rw [hv]
  have hf : KTerm.eval t = ((fun y : ℝ => t.c * (y : ℂ) ^ t.a) * fun x : ℝ => cexp (t.β * x)) *
      riemannKernelDeriv t.j := funext fun x => rfl
  rw [hf]
  refine h.congr_deriv ?_
  simp only [Pi.mul_apply]
  ring

theorem KFun.hasDerivAt (F : KFun) (u : ℝ) :
    HasDerivAt (KFun.eval F) (KFun.eval (KFun.d F) u) u := by
  induction F with
  | nil =>
    have h0 : KFun.eval [] = fun _ => (0 : ℂ) := funext fun _ => rfl
    rw [h0]
    exact hasDerivAt_const u (0 : ℂ)
  | cons t F ih =>
    have h := (KTerm.hasDerivAt t u).add ih
    have he : KFun.eval (KFun.d (t :: F)) u = KFun.eval (KTerm.d t) u + KFun.eval (KFun.d F) u := by
      simp only [KFun.d, List.flatMap_cons, KFun.eval_append]
    rw [he]
    have hf : KFun.eval (t :: F) = fun x => KTerm.eval t x + KFun.eval F x := funext fun x => rfl
    rw [hf]; exact h

/-- Each monomial decays faster than every exponential. -/
theorem KTerm.superExpDecay (t : KTerm) : SuperExpDecay t.eval := by
  have hcont : Continuous t.eval := by
    unfold KTerm.eval
    exact ((continuous_const.mul ((Complex.continuous_ofReal).pow t.a)).mul
      (by fun_prop)).mul (continuous_riemannKernelDeriv t.j)
  refine ⟨hcont, fun c => ?_⟩
  have hD := (superExpDecay_riemannKernelDeriv t.j).2 (c + t.a + |t.β|)
  refine (hD.const_mul ‖t.c‖).mono' (hcont.norm.mul (by fun_prop)).aestronglyMeasurable
    (Eventually.of_forall fun u => ?_)
  have hpow : |u| ^ t.a ≤ Real.exp (t.a * |u|) := by
    calc |u| ^ t.a ≤ Real.exp |u| ^ t.a :=
          pow_le_pow_left₀ (abs_nonneg u) (by linarith [Real.add_one_le_exp |u|]) _
      _ = Real.exp (t.a * |u|) := by rw [← Real.exp_nat_mul]
  have hexp : ‖cexp (t.β * u)‖ ≤ Real.exp (|t.β| * |u|) := by
    rw [show (t.β : ℂ) * u = ((t.β * u : ℝ) : ℂ) by push_cast; ring, Complex.norm_exp_ofReal]
    exact Real.exp_le_exp.mpr (by rw [← abs_mul]; exact le_abs_self _)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  unfold KTerm.eval
  rw [norm_mul, norm_mul, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
  calc ‖t.c‖ * |u| ^ t.a * ‖cexp (t.β * u)‖ * ‖riemannKernelDeriv t.j u‖ * Real.exp (c * |u|)
      ≤ ‖t.c‖ * Real.exp (t.a * |u|) * Real.exp (|t.β| * |u|) * ‖riemannKernelDeriv t.j u‖ *
          Real.exp (c * |u|) := by gcongr
    _ = ‖t.c‖ * (‖riemannKernelDeriv t.j u‖ * Real.exp ((c + t.a + |t.β|) * |u|)) := by
        rw [show (c + t.a + |t.β|) * |u| = t.a * |u| + |t.β| * |u| + c * |u| by ring,
          Real.exp_add, Real.exp_add]; ring

theorem KFun.superExpDecay (F : KFun) : SuperExpDecay (KFun.eval F) := by
  induction F with
  | nil =>
    refine ⟨continuous_const, fun c => ?_⟩
    simp [KFun.eval]
  | cons t F ih =>
    have h := (KTerm.superExpDecay t).add ih
    have hf : KFun.eval (t :: F) = fun x => KTerm.eval t x + KFun.eval F x := funext fun x => rfl
    rw [hf]; exact h


/-! ## Transforms -/

open Zeta23 in
/-- The transform of a super-exponentially decaying `g` is entire, with derivative `(iug)^`. -/
theorem hasDerivAt_paperFT_of_superExpDecay {g : ℝ → ℂ} (hg : SuperExpDecay g) (z₀ : ℂ) :
    HasDerivAt (paperFT g) (paperFT (fun u => I * u * g u) z₀) z₀ := by
  set F : ℂ → ℝ → ℂ := fun z u => g u * Complex.exp (I * z * u) with hF
  set F' : ℂ → ℝ → ℂ := fun z u => g u * (I * u * Complex.exp (I * z * u)) with hF'
  set bound : ℝ → ℝ := fun u => ‖g u‖ * Real.exp ((|z₀.im| + 2) * |u|) with hbound
  have hball : Metric.ball z₀ 1 ∈ 𝓝 z₀ := Metric.ball_mem_nhds z₀ one_pos
  have hmeas : ∀ z, AEStronglyMeasurable (F z) volume := fun z =>
    (hg.1.mul (by fun_prop)).aestronglyMeasurable
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume) (F := F) (F' := F')
    (x₀ := z₀) (bound := bound) hball (Eventually.of_forall hmeas) (hg.integrable_mul_cexp z₀)
    ((hg.1.mul (by fun_prop)).aestronglyMeasurable)
    (Eventually.of_forall fun u z hz => ?_) (hg.2 _) (Eventually.of_forall fun u z _ => ?_)
  · have hd := h.2
    unfold paperFT
    refine hd.congr_deriv ?_
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    simp only [hF']
    ring
  · have hzim : |z.im| ≤ |z₀.im| + 1 := by
      have := Metric.mem_ball.mp hz
      rw [dist_eq_norm] at this
      have h1 := Complex.abs_im_le_norm (z - z₀)
      rw [Complex.sub_im] at h1
      have := abs_sub_abs_le_abs_sub z.im z₀.im
      linarith
    simp only [hF', hbound]
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
      Real.norm_eq_abs]
    have he := norm_cexp_I_mul_le_exp hzim u
    have hu : |u| ≤ Real.exp |u| := by
      have := Real.add_one_le_exp |u|; linarith
    calc ‖g u‖ * (|u| * ‖Complex.exp (I * z * u)‖)
        ≤ ‖g u‖ * (Real.exp |u| * Real.exp ((|z₀.im| + 1) * |u|)) := by gcongr
      _ = ‖g u‖ * Real.exp ((|z₀.im| + 2) * |u|) := by
          rw [← Real.exp_add]; congr 2; ring
  · have h1 : HasDerivAt (fun z : ℂ => I * z * (u : ℂ)) (I * u) z := by
      simpa using ((hasDerivAt_id z).const_mul I).mul_const (u : ℂ)
    have h2 := (h1.cexp).const_mul (g u)
    simp only [hF, hF']
    exact h2.congr_deriv (by ring)

/-- Multiplication by `iu`. -/
def KFun.mulIU (F : KFun) : KFun := F.map fun t => ⟨I * t.c, t.a + 1, t.β, t.j⟩

theorem KFun.eval_mulIU (F : KFun) (u : ℝ) :
    KFun.eval (KFun.mulIU F) u = I * u * KFun.eval F u := by
  induction F with
  | nil => simp [KFun.mulIU, KFun.eval]
  | cons t F ih =>
    simp only [KFun.mulIU, List.map_cons, KFun.eval_cons] at ih ⊢
    rw [ih]
    simp only [KTerm.eval]
    ring

/-- Scalar multiples. -/
def KFun.smul (s : ℂ) (F : KFun) : KFun := F.map fun t => ⟨s * t.c, t.a, t.β, t.j⟩

theorem KFun.eval_smul (s : ℂ) (F : KFun) (u : ℝ) :
    KFun.eval (KFun.smul s F) u = s * KFun.eval F u := by
  induction F with
  | nil => simp [KFun.smul, KFun.eval]
  | cons t F ih =>
    simp only [KFun.smul, List.map_cons, KFun.eval_cons] at ih ⊢
    rw [ih]
    simp only [KTerm.eval]
    ring

open Zeta23 in
theorem paperFT_kfun_append (F G : KFun) (z : ℂ) :
    paperFT (KFun.eval (F ++ G)) z = paperFT (KFun.eval F) z + paperFT (KFun.eval G) z := by
  unfold paperFT
  rw [← integral_add ((KFun.superExpDecay F).integrable_mul_cexp z)
    ((KFun.superExpDecay G).integrable_mul_cexp z)]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  simp only [KFun.eval_append]
  ring

open Zeta23 in
theorem paperFT_kfun_smul (s : ℂ) (F : KFun) (z : ℂ) :
    paperFT (KFun.eval (KFun.smul s F)) z = s * paperFT (KFun.eval F) z := by
  unfold paperFT
  rw [← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  simp only [KFun.eval_smul]
  ring

open Zeta23 in
/-- `D^k` on the transform is `(iu)^k` on the kernel. -/
theorem iteratedDeriv_paperFT_kfun (k : ℕ) (F : KFun) :
    iteratedDeriv k (paperFT (KFun.eval F)) = paperFT (KFun.eval (KFun.mulIU^[k] F)) := by
  induction k generalizing F with
  | zero => simp
  | succ k ih =>
    rw [iteratedDeriv_succ', Function.iterate_succ_apply]
    have hd : deriv (paperFT (KFun.eval F)) = paperFT (KFun.eval (KFun.mulIU F)) := by
      funext z
      rw [(hasDerivAt_paperFT_of_superExpDecay (KFun.superExpDecay F) z).deriv]
      congr 1
      funext u
      rw [KFun.eval_mulIU]
    rw [hd, ih]

/-- `i·d/du` on kernels. -/
def KFun.iD (F : KFun) : KFun := KFun.smul I (KFun.d F)

open Zeta23 in
/-- Multiplication by `z` on the transform is `i d/du` on the kernel. -/
theorem mul_paperFT_kfun (F : KFun) (z : ℂ) :
    z * paperFT (KFun.eval F) z = paperFT (KFun.eval (KFun.iD F)) z := by
  unfold KFun.iD
  rw [paperFT_kfun_smul, paperFT_deriv_of_superExpDecay (KFun.superExpDecay F)
    (KFun.superExpDecay (KFun.d F)) (KFun.hasDerivAt F) z]
  ring_nf
  rw [Complex.I_sq]
  ring

/-- A polynomial in `z` acting on the transform. -/
def KFun.opPoly (q : ℂ[X]) (F : KFun) : KFun :=
  (List.range (q.natDegree + 1)).flatMap fun m => KFun.smul (q.coeff m) (KFun.iD^[m] F)

open Zeta23 in
theorem paperFT_kfun_flatMap (L : List ℕ) (G : ℕ → KFun) (z : ℂ) :
    paperFT (KFun.eval (L.flatMap G)) z = (L.map fun m => paperFT (KFun.eval (G m)) z).sum := by
  induction L with
  | nil =>
    simp only [List.flatMap_nil, List.map_nil, List.sum_nil]
    unfold paperFT
    simp [KFun.eval]
  | cons m L ih =>
    rw [List.flatMap_cons, paperFT_kfun_append, ih, List.map_cons, List.sum_cons]

open Zeta23 in
theorem pow_mul_paperFT_kfun (m : ℕ) (F : KFun) (z : ℂ) :
    z ^ m * paperFT (KFun.eval F) z = paperFT (KFun.eval (KFun.iD^[m] F)) z := by
  induction m generalizing F with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, mul_assoc, mul_paperFT_kfun, ih, ← Function.iterate_succ_apply]

open Zeta23 in
theorem polyEval_mul_paperFT_kfun (q : ℂ[X]) (F : KFun) (z : ℂ) :
    q.eval z * paperFT (KFun.eval F) z = paperFT (KFun.eval (KFun.opPoly q F)) z := by
  rw [KFun.opPoly, paperFT_kfun_flatMap, eval_eq_sum_range, Finset.sum_mul,
    ← List.sum_toFinset _ (List.nodup_range), List.toFinset_range]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [paperFT_kfun_smul, ← pow_mul_paperFT_kfun]
  ring


/-! ## Fourier injectivity -/

open Zeta23 FourierTransform in
/-- A super-exponentially decaying function whose transform vanishes on the real line is zero. -/
theorem eq_zero_of_paperFT_real_eq_zero {g : ℝ → ℂ} (hg : SuperExpDecay g)
    (h : ∀ t : ℝ, paperFT g t = 0) : g = 0 := by
  have hint : Integrable g := by
    refine (hg.2 0).mono' hg.1.aestronglyMeasurable (Eventually.of_forall fun u => ?_)
    simp
  have hF : 𝓕 g = 0 := by
    funext w
    rw [Zeta23.fourier_eq_paperFT]
    have := h (-(2 * π * w))
    push_cast at this
    simpa using this
  have hinv := Continuous.fourierInv_fourier_eq hg.1 hint (by rw [hF]; exact integrable_zero _ _ _)
  rw [← hinv, hF]
  funext w
  rw [Real.fourierInv_eq]
  simp

/-! ## The leading cusp term and the tail -/

theorem expPolyEval_zero (u : ℝ) : expPolyEval 0 u = 0 := by
  simp [expPolyEval]

theorem expPolyEval_finset_sum {ι : Type*} (s : Finset ι) (E : ι → ExpPoly) (u : ℝ) :
    expPolyEval (∑ i ∈ s, E i) u = ∑ i ∈ s, expPolyEval (E i) u := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [expPolyEval_zero]
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, expPolyEval_add, ih]

/-- The terms `n ≥ 2` of a cusp series are `O(e^{u/2} e^{2du} e^{-4πe^{2u}})` for `u ≥ 0`. -/
theorem exists_abs_cuspSeries_tail_le (R : ℝ[X]) : ∃ B : ℝ, 0 ≤ B ∧ ∀ u : ℝ, 0 ≤ u →
    |∑' n : ℕ, cuspTerm R (n + 2) u| ≤ B * Real.exp ((1 / 2 + 2 * R.natDegree) * u) *
      Real.exp (-(4 * π) * Real.exp (2 * u)) := by
  set d := R.natDegree with hd
  set f : ℕ → ℝ := fun m => (m : ℝ) ^ (2 * d) * Real.exp (-π * m) with hf
  have hsum : Summable fun n : ℕ => f (n + 2) :=
    (summable_nat_add_iff 2).mpr (Real.summable_pow_mul_exp_neg_nat_mul (2 * d) Real.pi_pos)
  set S := ∑' n : ℕ, f (n + 2) with hS
  have hS0 : 0 ≤ S := tsum_nonneg fun n => by simp only [hf]; positivity
  have hP := polyAbsBound_nonneg R
  refine ⟨polyAbsBound R * 2 ^ d * Real.exp (2 * π) * S, by positivity, fun u hu => ?_⟩
  set Y := Real.exp (2 * u) with hY
  have hY1 : 1 ≤ Y := Real.one_le_exp (by linarith)
  set K := polyAbsBound R * 2 ^ d * Real.exp (2 * π) * Real.exp ((1 / 2 + 2 * d) * u) *
    Real.exp (-(4 * π) * Y) with hK
  have hterm : ∀ n : ℕ, |cuspTerm R (n + 2) u| ≤ K * f (n + 2) := by
    intro n
    set m : ℝ := ((n + 2 : ℕ) : ℝ) with hm
    have hm2 : 2 ≤ m := by rw [hm]; push_cast; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    have hR := abs_eval_le_polyAbsBound R (show 0 ≤ m ^ 2 * Y by positivity)
    have hpoly : (1 + m ^ 2 * Y) ^ d ≤ 2 ^ d * m ^ (2 * d) * Real.exp (2 * d * u) := by
      have h1 : 1 + m ^ 2 * Y ≤ 2 * (m ^ 2 * Y) := by nlinarith
      have h2 : (2 * (m ^ 2 * Y)) ^ d = 2 ^ d * m ^ (2 * d) * Y ^ d := by
        rw [mul_pow, mul_pow, pow_mul]; ring
      have h3 : Y ^ d = Real.exp (2 * d * u) := by
        rw [hY, ← Real.exp_nat_mul]; ring_nf
      calc (1 + m ^ 2 * Y) ^ d ≤ (2 * (m ^ 2 * Y)) ^ d := pow_le_pow_left₀ (by positivity) h1 d
        _ = _ := by rw [h2, h3]
    have hexp : Real.exp (-π * (m ^ 2 * Y)) ≤
        Real.exp (2 * π) * Real.exp (-(4 * π) * Y) * Real.exp (-π * m) := by
      rw [← Real.exp_add, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have h1 : m - 2 ≤ m ^ 2 - 4 := by nlinarith
      have h2 : (m ^ 2 - 4) * 1 ≤ (m ^ 2 - 4) * Y := mul_le_mul_of_nonneg_left hY1 (by nlinarith)
      nlinarith [Real.pi_pos]
    unfold cuspTerm
    rw [abs_mul, abs_mul, abs_of_pos (Real.exp_pos _), abs_of_pos (Real.exp_pos _)]
    have hfm : f (n + 2) = m ^ (2 * d) * Real.exp (-π * m) := by simp only [hf, hm]
    rw [hfm]
    have hsplit : Real.exp ((1 / 2 + 2 * d) * u) = Real.exp (u / 2) * Real.exp (2 * d * u) := by
      rw [← Real.exp_add]; ring_nf
    calc Real.exp (u / 2) * |R.eval (m ^ 2 * Y)| * Real.exp (-π * (m ^ 2 * Y))
        ≤ Real.exp (u / 2) * (polyAbsBound R * (2 ^ d * m ^ (2 * d) * Real.exp (2 * d * u))) *
            (Real.exp (2 * π) * Real.exp (-(4 * π) * Y) * Real.exp (-π * m)) := by
          gcongr
          exact hR.trans (mul_le_mul_of_nonneg_left hpoly hP)
      _ = K * (m ^ (2 * d) * Real.exp (-π * m)) := by rw [hK, hsplit]; ring
  have hsumK : Summable fun n : ℕ => K * f (n + 2) := hsum.mul_left K
  have habs : Summable fun n : ℕ => |cuspTerm R (n + 2) u| :=
    Summable.of_nonneg_of_le (fun n => abs_nonneg _) hterm hsumK
  calc |∑' n : ℕ, cuspTerm R (n + 2) u| ≤ ∑' n : ℕ, |cuspTerm R (n + 2) u| := by
        have := norm_tsum_le_tsum_norm (f := fun n : ℕ => cuspTerm R (n + 2) u) (by
          simpa [Real.norm_eq_abs] using habs)
        simpa [Real.norm_eq_abs] using this
    _ ≤ ∑' n : ℕ, K * f (n + 2) := habs.tsum_le_tsum hterm hsumK
    _ = _ := by rw [tsum_mul_left, hK]; ring

theorem cuspSeries_eq_head_add_tail (R : ℝ[X]) (u : ℝ) :
    cuspSeries R u = Real.exp (u / 2) * R.eval (Real.exp (2 * u)) *
      Real.exp (-π * Real.exp (2 * u)) + ∑' n : ℕ, cuspTerm R (n + 2) u := by
  unfold cuspSeries
  rw [(summable_cuspTerm R u).tsum_eq_zero_add]
  congr 1
  simp [cuspTerm]

/-- The exponential polynomial carried by the leading cusp term of one monomial. -/
def KTerm.head (t : KTerm) : ExpPoly :=
  ∑ i ∈ Finset.range ((cuspDeriv^[t.j] riemannCuspPoly).natDegree + 1),
    Finsupp.single (t.β + 1 / 2 + 2 * i)
      (C (t.c * ((cuspDeriv^[t.j] riemannCuspPoly).coeff i : ℂ)) * X ^ t.a)

theorem KTerm.head_eval (t : KTerm) (u : ℝ) :
    t.c * (u : ℂ) ^ t.a * cexp (t.β * u) *
        ((Real.exp (u / 2) * (cuspDeriv^[t.j] riemannCuspPoly).eval (Real.exp (2 * u)) *
          Real.exp (-π * Real.exp (2 * u)) : ℝ) : ℂ) =
      (Real.exp (-π * Real.exp (2 * u)) : ℂ) * expPolyEval t.head u := by
  unfold KTerm.head
  set R := cuspDeriv^[t.j] riemannCuspPoly with hR
  rw [eval_eq_sum_range, Finset.mul_sum, Finset.sum_mul, Complex.ofReal_sum, Finset.mul_sum,
    expPolyEval_finset_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [expPolyEval_single]
  simp only [eval_mul, eval_C, eval_pow, eval_X]
  push_cast
  have e1 : cexp (2 * (u : ℂ)) ^ i = cexp (2 * i * u) := by
    rw [← Complex.exp_nat_mul]; ring_nf
  have e2 : cexp (t.β * u) * cexp (u / 2) * cexp (2 * i * u) =
      cexp ((t.β + 1 / 2 + 2 * i) * u) := by
    rw [← Complex.exp_add, ← Complex.exp_add]; ring_nf
  rw [e1, ← e2]
  ring

/-- The leading exponential polynomial of a kernel function. -/
def KFun.head (F : KFun) : ExpPoly := (F.map KTerm.head).sum

theorem KFun.head_append (F G : KFun) : KFun.head (F ++ G) = KFun.head F + KFun.head G := by
  unfold KFun.head; rw [List.map_append, List.sum_append]

/-- **Head and tail.** A kernel function is its leading exponential polynomial times
`e^{-πe^{2u}}`, up to `O(e^{Cu}e^{-4πe^{2u}})` for `u ≥ 0`. -/
theorem KFun.exists_tail_le (F : KFun) : ∃ K C : ℝ, 0 ≤ K ∧ 0 ≤ C ∧ ∀ u : ℝ, 0 ≤ u →
    ‖KFun.eval F u - (Real.exp (-π * Real.exp (2 * u)) : ℂ) * expPolyEval (KFun.head F) u‖ ≤
      K * Real.exp (C * u) * Real.exp (-(4 * π) * Real.exp (2 * u)) := by
  induction F with
  | nil => exact ⟨0, 0, le_rfl, le_rfl, fun u _ => by simp [KFun.head, expPolyEval_zero]⟩
  | cons t F ih =>
    obtain ⟨K₁, C₁, hK₁, hC₁, h₁⟩ := ih
    set R := cuspDeriv^[t.j] riemannCuspPoly with hR
    obtain ⟨B, hB, hBle⟩ := exists_abs_cuspSeries_tail_le R
    set C₀ : ℝ := t.a + |t.β| + (1 / 2 + 2 * R.natDegree) with hC₀
    refine ⟨‖t.c‖ * B + K₁, max C₀ C₁, by positivity, le_max_of_le_right hC₁, fun u hu => ?_⟩
    have hterm : ‖KTerm.eval t u - (Real.exp (-π * Real.exp (2 * u)) : ℂ) * expPolyEval t.head u‖ ≤
        ‖t.c‖ * B * Real.exp (C₀ * u) * Real.exp (-(4 * π) * Real.exp (2 * u)) := by
      have hsplit : KTerm.eval t u = t.c * (u : ℂ) ^ t.a * cexp (t.β * u) *
          ((Real.exp (u / 2) * R.eval (Real.exp (2 * u)) *
            Real.exp (-π * Real.exp (2 * u)) : ℝ) : ℂ) +
          t.c * (u : ℂ) ^ t.a * cexp (t.β * u) * ((∑' n : ℕ, cuspTerm R (n + 2) u : ℝ) : ℂ) := by
        unfold KTerm.eval riemannKernelDeriv
        rw [cuspSeries_eq_head_add_tail]
        push_cast; ring
      rw [hsplit, KTerm.head_eval, add_sub_cancel_left, norm_mul, norm_mul, norm_mul, norm_pow,
        Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hu]
      have hpow : u ^ t.a ≤ Real.exp (t.a * u) := by
        calc u ^ t.a ≤ Real.exp u ^ t.a :=
              pow_le_pow_left₀ hu (by linarith [Real.add_one_le_exp u]) _
          _ = Real.exp (t.a * u) := by rw [← Real.exp_nat_mul]
      have hexp : ‖cexp (t.β * u)‖ ≤ Real.exp (|t.β| * u) := by
        rw [show (t.β : ℂ) * u = ((t.β * u : ℝ) : ℂ) by push_cast; ring, Complex.norm_exp_ofReal]
        exact Real.exp_le_exp.mpr (by nlinarith [le_abs_self t.β])
      have ht := hBle u hu
      calc ‖t.c‖ * u ^ t.a * ‖cexp (t.β * u)‖ * |∑' n : ℕ, cuspTerm R (n + 2) u|
          ≤ ‖t.c‖ * Real.exp (t.a * u) * Real.exp (|t.β| * u) *
              (B * Real.exp ((1 / 2 + 2 * R.natDegree) * u) *
                Real.exp (-(4 * π) * Real.exp (2 * u))) := by gcongr
        _ = ‖t.c‖ * B * Real.exp (C₀ * u) * Real.exp (-(4 * π) * Real.exp (2 * u)) := by
            rw [hC₀, show (t.a + |t.β| + (1 / 2 + 2 * R.natDegree)) * u =
              t.a * u + |t.β| * u + (1 / 2 + 2 * R.natDegree) * u by ring,
              Real.exp_add, Real.exp_add]; ring
    have hrest := h₁ u hu
    have hhead : KFun.head (t :: F) = t.head + KFun.head F := by
      simp [KFun.head]
    rw [KFun.eval_cons, hhead, expPolyEval_add]
    have hE0 : 0 ≤ Real.exp (-(4 * π) * Real.exp (2 * u)) := (Real.exp_pos _).le
    have hm1 : Real.exp (C₀ * u) ≤ Real.exp (max C₀ C₁ * u) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_max_left _ _) hu)
    have hm2 : Real.exp (C₁ * u) ≤ Real.exp (max C₀ C₁ * u) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_max_right _ _) hu)
    calc ‖KTerm.eval t u + KFun.eval F u - (Real.exp (-π * Real.exp (2 * u)) : ℂ) *
          (expPolyEval t.head u + expPolyEval (KFun.head F) u)‖
        = ‖(KTerm.eval t u - (Real.exp (-π * Real.exp (2 * u)) : ℂ) * expPolyEval t.head u) +
            (KFun.eval F u - (Real.exp (-π * Real.exp (2 * u)) : ℂ) *
              expPolyEval (KFun.head F) u)‖ := by ring_nf
      _ ≤ ‖t.c‖ * B * Real.exp (C₀ * u) * Real.exp (-(4 * π) * Real.exp (2 * u)) +
            K₁ * Real.exp (C₁ * u) * Real.exp (-(4 * π) * Real.exp (2 * u)) :=
          (norm_add_le _ _).trans (add_le_add hterm hrest)
      _ ≤ (‖t.c‖ * B + K₁) * Real.exp (max C₀ C₁ * u) *
            Real.exp (-(4 * π) * Real.exp (2 * u)) := by
          have := mul_le_mul_of_nonneg_right hm1 (mul_nonneg (mul_nonneg (norm_nonneg t.c) hB) hE0)
          have := mul_le_mul_of_nonneg_right hm2 (mul_nonneg hK₁ hE0)
          nlinarith


/-! ## Exponent classes -/

/-- All monomials of `F` carry an exponential `e^{βu}` with `β ∈ S`. -/
def KFun.BetaIn (S : Set ℝ) (F : KFun) : Prop := ∀ t ∈ F, t.β ∈ S

theorem KFun.BetaIn.append {S : Set ℝ} {F G : KFun} (hF : KFun.BetaIn S F)
    (hG : KFun.BetaIn S G) : KFun.BetaIn S (F ++ G) := by
  intro t ht
  rcases List.mem_append.mp ht with h | h
  · exact hF t h
  · exact hG t h

theorem KFun.BetaIn.flatMap {S : Set ℝ} {L : List ℕ} {G : ℕ → KFun}
    (hG : ∀ m, KFun.BetaIn S (G m)) : KFun.BetaIn S (L.flatMap G) := by
  intro t ht
  obtain ⟨m, -, hm⟩ := List.mem_flatMap.mp ht
  exact hG m t hm

theorem KFun.BetaIn.mulIU {S : Set ℝ} {F : KFun} (hF : KFun.BetaIn S F) :
    KFun.BetaIn S (KFun.mulIU F) := by
  intro t ht
  obtain ⟨t', ht', rfl⟩ := List.mem_map.mp ht
  exact hF t' ht'

theorem KFun.BetaIn.smul {S : Set ℝ} {F : KFun} (hF : KFun.BetaIn S F) (c : ℂ) :
    KFun.BetaIn S (KFun.smul c F) := by
  intro t ht
  obtain ⟨t', ht', rfl⟩ := List.mem_map.mp ht
  exact hF t' ht'

theorem KFun.BetaIn.d {S : Set ℝ} {F : KFun} (hF : KFun.BetaIn S F) :
    KFun.BetaIn S (KFun.d F) := by
  intro t ht
  obtain ⟨t', ht', hm⟩ := List.mem_flatMap.mp ht
  simp only [KTerm.d, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl <;> exact hF t' ht'

theorem KFun.BetaIn.iD {S : Set ℝ} {F : KFun} (hF : KFun.BetaIn S F) :
    KFun.BetaIn S (KFun.iD F) := (hF.d).smul I

theorem KFun.BetaIn.iterate_iD {S : Set ℝ} {F : KFun} (hF : KFun.BetaIn S F) (m : ℕ) :
    KFun.BetaIn S (KFun.iD^[m] F) := by
  induction m with
  | zero => simpa using hF
  | succ m ih => rw [Function.iterate_succ_apply']; exact ih.iD

theorem KFun.BetaIn.iterate_mulIU {S : Set ℝ} {F : KFun} (hF : KFun.BetaIn S F) (k : ℕ) :
    KFun.BetaIn S (KFun.mulIU^[k] F) := by
  induction k with
  | zero => simpa using hF
  | succ k ih => rw [Function.iterate_succ_apply']; exact ih.mulIU

theorem KFun.BetaIn.opPoly {S : Set ℝ} {F : KFun} (hF : KFun.BetaIn S F) (q : ℂ[X]) :
    KFun.BetaIn S (KFun.opPoly q F) :=
  KFun.BetaIn.flatMap fun m => (hF.iterate_iD m).smul _

theorem KTerm.head_apply_eq_zero (t : KTerm) {γ : ℝ} (hγ : ∀ i : ℕ, t.β + 1 / 2 + 2 * i ≠ γ) :
    t.head γ = 0 := by
  unfold KTerm.head
  rw [Finsupp.finsetSum_apply]
  exact Finset.sum_eq_zero fun i _ => Finsupp.single_eq_of_ne (hγ i).symm

theorem KFun.head_apply_eq_zero (F : KFun) {γ : ℝ}
    (hγ : ∀ t ∈ F, ∀ i : ℕ, t.β + 1 / 2 + 2 * i ≠ γ) : KFun.head F γ = 0 := by
  induction F with
  | nil => simp [KFun.head]
  | cons t F ih =>
    have hhead : KFun.head (t :: F) = t.head + KFun.head F := by simp [KFun.head]
    rw [hhead, Finsupp.add_apply,
      KTerm.head_apply_eq_zero t (hγ t List.mem_cons_self),
      ih fun t' ht' => hγ t' (List.mem_cons_of_mem _ ht'), add_zero]

/-- The leading cusp term of `-Φ` has coefficient `-4π²` at the exponent `9/2`. -/
theorem head_negPhi_nine_halves :
    KTerm.head ⟨-1, 0, 0, 0⟩ (9 / 2) = C (-(4 * (π : ℂ) ^ 2)) := by
  unfold KTerm.head
  simp only [Function.iterate_zero, id]
  have hdeg : 2 ≤ riemannCuspPoly.natDegree := by
    refine le_natDegree_of_ne_zero ?_
    rw [coeff_riemannCuspPoly_two]; positivity
  rw [Finsupp.finsetSum_apply, Finset.sum_eq_single 2]
  · rw [Finsupp.single_apply, if_pos (by norm_num), coeff_riemannCuspPoly_two]
    push_cast; simp
  · intro i _ hi
    refine Finsupp.single_eq_of_ne ?_
    intro h
    have : (i : ℝ) = 2 := by linarith
    exact hi (by exact_mod_cast this)
  · intro h
    exact absurd (Finset.mem_range.mpr (by omega)) h

/-! ## Super-exponential decay forces the head to vanish -/

theorem tendsto_exp_linear_sub_exp_two_mul {C c : ℝ} (hc : 0 < c) :
    Tendsto (fun u : ℝ => Real.exp (C * u - c * Real.exp (2 * u))) atTop (𝓝 0) := by
  refine Real.tendsto_exp_atBot.comp ?_
  have hq : ∀ u : ℝ, 0 ≤ u → C * u - c * Real.exp (2 * u) ≤ C * u - 2 * c * u ^ 2 := by
    intro u hu
    have := Real.quadratic_le_exp_of_nonneg (show 0 ≤ 2 * u by linarith)
    nlinarith [sq_nonneg u]
  refine tendsto_atBot_mono' atTop ?_
    (?_ : Tendsto (fun u : ℝ => C * u - 2 * c * u ^ 2) atTop atBot)
  · filter_upwards [eventually_ge_atTop 0] with u hu
    exact hq u hu
  · have h1 : Tendsto (fun u : ℝ => u * (2 * c * u - C)) atTop atTop :=
      tendsto_id.atTop_mul_atTop₀ (tendsto_atTop_add_const_right _ _
        (tendsto_id.const_mul_atTop (by positivity)))
    have h2 := tendsto_neg_atTop_atBot.comp h1
    refine h2.congr fun u => ?_
    simp only [Function.comp_def]
    ring

theorem KFun.head_eq_zero_of_eval_eq_zero (F : KFun) (hF : ∀ u : ℝ, KFun.eval F u = 0) :
    KFun.head F = 0 := by
  obtain ⟨K, C, hK, hC, htail⟩ := KFun.exists_tail_le F
  refine eq_zero_of_tendsto_mul_cexp _ fun M => ?_
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hlim := (tendsto_exp_linear_sub_exp_two_mul (C := C + M) (c := 3 * π)
    (by positivity)).const_mul K
  rw [mul_zero] at hlim
  refine squeeze_zero' (Eventually.of_forall fun u => norm_nonneg _) ?_ hlim
  filter_upwards [eventually_ge_atTop 0] with u hu
  have h := htail u hu
  rw [hF u, zero_sub, norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)] at h
  have hE := Real.exp_pos (-π * Real.exp (2 * u))
  rw [norm_mul, show (M : ℂ) * u = ((M * u : ℝ) : ℂ) by push_cast; ring, Complex.norm_exp_ofReal]
  have hsplit : Real.exp (-(4 * π) * Real.exp (2 * u)) =
      Real.exp (-π * Real.exp (2 * u)) * Real.exp (-(3 * π) * Real.exp (2 * u)) := by
    rw [← Real.exp_add]; ring_nf
  rw [hsplit] at h
  have h2 : Real.exp (-π * Real.exp (2 * u)) * ‖expPolyEval (KFun.head F) u‖ ≤
      Real.exp (-π * Real.exp (2 * u)) *
        (K * Real.exp (C * u) * Real.exp (-(3 * π) * Real.exp (2 * u))) := by
    have e : K * Real.exp (C * u) * (Real.exp (-π * Real.exp (2 * u)) *
        Real.exp (-(3 * π) * Real.exp (2 * u))) = Real.exp (-π * Real.exp (2 * u)) *
        (K * Real.exp (C * u) * Real.exp (-(3 * π) * Real.exp (2 * u))) := by ring
    linarith [h, e]
  have h' := le_of_mul_le_mul_left h2 hE
  calc ‖expPolyEval (KFun.head F) u‖ * Real.exp (M * u)
      ≤ K * Real.exp (C * u) * Real.exp (-(3 * π) * Real.exp (2 * u)) * Real.exp (M * u) :=
        mul_le_mul_of_nonneg_right h' (Real.exp_pos _).le
    _ = K * Real.exp ((C + M) * u - 3 * π * Real.exp (2 * u)) := by
        rw [show (C + M) * u - 3 * π * Real.exp (2 * u) =
          C * u + -(3 * π) * Real.exp (2 * u) + M * u by ring, Real.exp_add, Real.exp_add]; ring

/-! ## The obstruction -/

/-- The cosine producer `cos(hD)Ξ`: the transform of `Φ(u) cosh(hu)`. -/
def cosineProducer (h : ℝ) (z : ℂ) : ℂ :=
  Zeta23.paperFT (fun u => riemannPhiKernel u * (Real.cosh (h * u) : ℂ)) z

/-- `Φ(u) cosh(hu)` as a kernel function. -/
def cosineKernel (h : ℝ) : KFun := [⟨1 / 2, 0, h, 0⟩, ⟨1 / 2, 0, -h, 0⟩]

theorem cosineKernel_eval (h u : ℝ) :
    KFun.eval (cosineKernel h) u = riemannPhiKernel u * (Real.cosh (h * u) : ℂ) := by
  simp only [cosineKernel, KFun.eval_cons, KFun.eval_nil, KTerm.eval, add_zero, pow_zero,
    mul_one, riemannKernelDeriv_zero, Complex.ofReal_cosh, Complex.cosh]
  push_cast
  ring_nf

theorem cosineKernel_betaIn (h : ℝ) : KFun.BetaIn {h, -h} (cosineKernel h) := by
  intro t ht
  simp only [cosineKernel, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl <;> simp

theorem paperFT_kfun_single_zero (c : ℂ) (β : ℝ) (z : ℂ) :
    Zeta23.paperFT (KFun.eval [⟨c, 0, β, 0⟩]) z = c * XiC (z - β * I) := by
  have hPhi : ∀ w : ℂ, Zeta23.paperFT riemannPhiKernel w = XiC w := fun w => by
    rw [paperFT_riemannPhiKernel, riemannPhiTransform_eq_xi, XiC, mul_comm]
  rw [← hPhi]
  unfold Zeta23.paperFT
  rw [← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  simp only [KFun.eval_cons, KFun.eval_nil, KTerm.eval, add_zero, pow_zero, mul_one,
    riemannKernelDeriv_zero]
  have e : cexp (β * u) * cexp (I * z * u) = cexp (I * (z - β * I) * u) := by
    rw [← Complex.exp_add]
    congr 1
    ring_nf
    rw [Complex.I_sq]
    ring
  rw [← e]
  ring

/-- `A_h = cos(hD)Ξ`: the cosine producer is the average of the two imaginary translates of `Ξ`. -/
theorem cosineProducer_eq_average (h : ℝ) (z : ℂ) :
    cosineProducer h z = (XiC (z - h * I) + XiC (z + h * I)) / 2 := by
  have hprod : cosineProducer h z = Zeta23.paperFT (KFun.eval (cosineKernel h)) z := by
    unfold cosineProducer
    congr 1
    funext u
    rw [cosineKernel_eval]
  rw [hprod, show cosineKernel h = [⟨1 / 2, 0, h, 0⟩] ++ [⟨1 / 2, 0, -h, 0⟩] from rfl,
    paperFT_kfun_append, paperFT_kfun_single_zero, paperFT_kfun_single_zero]
  push_cast
  ring_nf

/-- **No local port from the cosine producer to `Ξ`.** For `h ∉ 2ℤ`, no finite-order linear
differential operator with polynomial coefficients maps `cos(hD)Ξ` to `Ξ` on the real line. -/
theorem not_exists_polynomial_port_cosineProducer {h : ℝ} (hh : ∀ k : ℤ, h ≠ 2 * k) (N : ℕ)
    (Q : ℕ → ℂ[X]) :
    ¬ ∀ t : ℝ, ∑ k ∈ Finset.range (N + 1),
        (Q k).eval (t : ℂ) * iteratedDeriv k (cosineProducer h) t = XiC t := by
  intro H
  set LF : KFun := (List.range (N + 1)).flatMap fun k =>
    KFun.opPoly (Q k) (KFun.mulIU^[k] (cosineKernel h)) with hLF
  set t₀ : KTerm := ⟨-1, 0, 0, 0⟩ with ht₀
  set F' : KFun := LF ++ [t₀] with hF'
  have hprod : cosineProducer h = Zeta23.paperFT (KFun.eval (cosineKernel h)) := by
    funext z
    unfold cosineProducer
    congr 1
    funext u
    rw [cosineKernel_eval]
  have hPhi : ∀ z : ℂ, Zeta23.paperFT riemannPhiKernel z = XiC z := fun z => by
    rw [paperFT_riemannPhiKernel, riemannPhiTransform_eq_xi, XiC, mul_comm]
  have heval0 : KFun.eval [t₀] = fun u => -riemannPhiKernel u := funext fun u => by
    simp [KFun.eval, KTerm.eval, ht₀, riemannKernelDeriv_zero]
  have hnegPhi : ∀ z : ℂ, Zeta23.paperFT (KFun.eval [t₀]) z = -XiC z := by
    intro z
    rw [heval0, ← hPhi]
    unfold Zeta23.paperFT
    simp only [neg_mul, MeasureTheory.integral_neg]
  have hLFt : ∀ t : ℝ, Zeta23.paperFT (KFun.eval LF) t = XiC t := by
    intro t
    rw [hLF, paperFT_kfun_flatMap, ← H t, ← List.sum_toFinset _ (List.nodup_range),
      List.toFinset_range]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hprod, iteratedDeriv_paperFT_kfun, polyEval_mul_paperFT_kfun]
  have hF'0 : ∀ t : ℝ, Zeta23.paperFT (KFun.eval F') t = 0 := by
    intro t
    rw [hF', paperFT_kfun_append, hLFt, hnegPhi]
    ring
  have heval : KFun.eval F' = 0 := eq_zero_of_paperFT_real_eq_zero (KFun.superExpDecay F') hF'0
  have hhead := KFun.head_eq_zero_of_eval_eq_zero F' fun u => by rw [heval]; rfl
  rw [hF', KFun.head_append] at hhead
  have hbeta : KFun.BetaIn {h, -h} LF :=
    KFun.BetaIn.flatMap fun k => ((cosineKernel_betaIn h).iterate_mulIU k).opPoly (Q k)
  have h1 : KFun.head LF (9 / 2) = 0 := by
    refine KFun.head_apply_eq_zero LF fun t ht i heq => ?_
    rcases hbeta t ht with hb | hb
    · rw [hb] at heq
      exact hh (2 - i) (by push_cast; linarith)
    · rw [Set.mem_singleton_iff] at hb
      rw [hb] at heq
      exact hh (i - 2) (by push_cast; linarith)
  have h2 : KFun.head [t₀] (9 / 2) = C (-(4 * (π : ℂ) ^ 2)) := by
    simp only [KFun.head, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    exact head_negPhi_nine_halves
  have h3 := congrArg (fun E : ExpPoly => E (9 / 2)) hhead
  simp only [Finsupp.add_apply, h1, h2, zero_add, Finsupp.coe_zero, Pi.zero_apply] at h3
  rw [C_eq_zero, neg_eq_zero] at h3
  have : (4 * (π : ℂ) ^ 2) ≠ 0 := by
    have := Real.pi_pos
    exact_mod_cast (by positivity : (4 * π ^ 2 : ℝ) ≠ 0)
  exact this h3

end RHTower.LocalPort
