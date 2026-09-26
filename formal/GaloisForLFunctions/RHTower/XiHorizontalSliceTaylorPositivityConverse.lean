import GaloisForLFunctions.RHTower.XiHorizontalSliceTaylorPositivity
import GaloisForLFunctions.RHTower.XiHadamardGrowth

/-!
# Under the Riemann hypothesis every slice Taylor coefficient is nonnegative

This is the converse of `riemannHypothesis_of_xiSliceCoeff_nonneg`, so the Riemann hypothesis is
equivalent to Taylor positivity of `x ↦ ξ(½+x+it)·ξ(½−x+it)` at `0` at every height `t`.

In the centred variable `ΞC(z) = ξ(½ + zi)`, the slice product is `ΞC(t − ix)·ΞC(t + ix)`.  The
Hadamard product `ΞC = ΞC(0)·∏ E₁(z/z_q)` is taken over the spectral points `z_q = (ρ − ½)(−i)`,
counted with multiplicity, with `E₁(w) = (1 − w)e^w`, and it converges locally uniformly.  Under the
hypothesis each `z_q = γ` is real and nonzero, and the paired factor is

  `E₁((t − ix)/γ)·E₁((t + ix)/γ) = e^{2t/γ}((γ − t)² + x²)/γ²`,

a polynomial in `x` with nonnegative coefficients.  Nonnegativity of all Taylor coefficients at `0`
(`NonnegTaylorAtZero`) is closed under sums and products by Leibniz's rule, and under locally
uniform limits of entire functions because derivatives converge.  So it passes from the finite
partial products to the slice product.
-/

open Complex Filter Topology
open scoped ComplexOrder

namespace RHTower

noncomputable section

/-- An entire function all of whose Taylor coefficients at `0` lie in the nonnegative cone of `ℂ`
(real and `≥ 0`). -/
def NonnegTaylorAtZero (f : ℂ → ℂ) : Prop :=
  Differentiable ℂ f ∧ ∀ n : ℕ, 0 ≤ iteratedDeriv n f 0

theorem nonnegTaylorAtZero_const {c : ℂ} (hc : 0 ≤ c) : NonnegTaylorAtZero (fun _ => c) := by
  refine ⟨differentiable_const c, fun n => ?_⟩
  rw [iteratedDeriv_const]
  split_ifs
  · exact hc
  · exact le_rfl

theorem nonnegTaylorAtZero_id : NonnegTaylorAtZero (fun x : ℂ => x) := by
  refine ⟨differentiable_id, fun n => ?_⟩
  cases n with
  | zero => simp
  | succ n =>
    rw [iteratedDeriv_succ', show (deriv fun x : ℂ => x) = fun _ => (1 : ℂ) from deriv_id'']
    exact (nonnegTaylorAtZero_const zero_le_one).2 n

theorem NonnegTaylorAtZero.add {f g : ℂ → ℂ} (hf : NonnegTaylorAtZero f)
    (hg : NonnegTaylorAtZero g) : NonnegTaylorAtZero (f + g) := by
  refine ⟨hf.1.add hg.1, fun n => ?_⟩
  rw [iteratedDeriv_add hf.1.contDiff.contDiffAt hg.1.contDiff.contDiffAt]
  exact add_nonneg (hf.2 n) (hg.2 n)

theorem NonnegTaylorAtZero.mul {f g : ℂ → ℂ} (hf : NonnegTaylorAtZero f)
    (hg : NonnegTaylorAtZero g) : NonnegTaylorAtZero (f * g) := by
  refine ⟨hf.1.mul hg.1, fun n => ?_⟩
  rw [iteratedDeriv_mul hf.1.contDiff.contDiffAt hg.1.contDiff.contDiffAt]
  exact Finset.sum_nonneg fun i _ =>
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hf.2 i)) (hg.2 _)

theorem nonnegTaylorAtZero_finsetProd {ι : Type*} (s : Finset ι) {f : ι → ℂ → ℂ}
    (hf : ∀ i ∈ s, NonnegTaylorAtZero (f i)) :
    NonnegTaylorAtZero (fun x => ∏ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using nonnegTaylorAtZero_const (zero_le_one : (0 : ℂ) ≤ 1)
  | insert a s ha ih =>
    have h1 := hf a (Finset.mem_insert_self a s)
    have h2 := ih fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have e : (fun x => ∏ i ∈ insert a s, f i x) = f a * fun x => ∏ i ∈ s, f i x := by
      funext x
      rw [Finset.prod_insert ha]
      rfl
    rw [e]
    exact h1.mul h2

/-- Iterated derivatives of entire functions converge under locally uniform convergence. -/
theorem tendstoLocallyUniformlyOn_iteratedDeriv {ι : Type*} {l : Filter ι} {F : ι → ℂ → ℂ}
    {f : ℂ → ℂ} (hF : ∀ i, Differentiable ℂ (F i))
    (h : TendstoLocallyUniformlyOn F f l Set.univ) (n : ℕ) :
    TendstoLocallyUniformlyOn (fun i => iteratedDeriv n (F i)) (iteratedDeriv n f) l Set.univ := by
  induction n with
  | zero => simpa using h
  | succ n ih =>
    have hd : ∀ᶠ i in l, DifferentiableOn ℂ (iteratedDeriv n (F i)) Set.univ :=
      Eventually.of_forall fun i =>
        (((hF i).contDiff (n := ⊤)).differentiable_iteratedDeriv n
          (WithTop.coe_lt_top _)).differentiableOn
    have := ih.deriv hd isOpen_univ
    rw [show (fun i => iteratedDeriv (n + 1) (F i)) = deriv ∘ fun i => iteratedDeriv n (F i) from
      funext fun i => iteratedDeriv_succ, iteratedDeriv_succ]
    exact this

/-- **Taylor positivity passes to locally uniform limits.** -/
theorem NonnegTaylorAtZero.of_tendstoLocallyUniformlyOn {ι : Type*} {l : Filter ι} [l.NeBot]
    {F : ι → ℂ → ℂ} {f : ℂ → ℂ} (hF : ∀ i, NonnegTaylorAtZero (F i)) (hf : Differentiable ℂ f)
    (h : TendstoLocallyUniformlyOn F f l Set.univ) : NonnegTaylorAtZero f := by
  refine ⟨hf, fun n => ?_⟩
  have ht := (tendstoLocallyUniformlyOn_iteratedDeriv (fun i => (hF i).1) h n).tendsto_at
    (Set.mem_univ (0 : ℂ))
  exact ge_of_tendsto' ht fun i => (hF i).2 n

/-- The paired Weierstrass factor at a real spectral point. -/
theorem weierstrassE1_slice_pair {γ t : ℝ} (hγ : γ ≠ 0) (x : ℂ) :
    weierstrassE1 (((t : ℂ) - I * x) / γ) * weierstrassE1 (((t : ℂ) + I * x) / γ) =
      ((Real.exp (2 * t / γ) * (γ - t) ^ 2 / γ ^ 2 : ℝ) : ℂ) +
        ((Real.exp (2 * t / γ) / γ ^ 2 : ℝ) : ℂ) * x * x := by
  have hγc : (γ : ℂ) ≠ 0 := by exact_mod_cast hγ
  unfold weierstrassE1
  have hexp : cexp (((t : ℂ) - I * x) / γ) * cexp (((t : ℂ) + I * x) / γ) =
      ((Real.exp (2 * t / γ) : ℝ) : ℂ) := by
    rw [← Complex.exp_add, Complex.ofReal_exp]
    congr 1
    push_cast
    field_simp
    ring
  calc (1 - ((t : ℂ) - I * x) / γ) * cexp (((t : ℂ) - I * x) / γ) *
        ((1 - ((t : ℂ) + I * x) / γ) * cexp (((t : ℂ) + I * x) / γ))
      = (1 - ((t : ℂ) - I * x) / γ) * (1 - ((t : ℂ) + I * x) / γ) *
          (cexp (((t : ℂ) - I * x) / γ) * cexp (((t : ℂ) + I * x) / γ)) := by ring
    _ = _ := by
      rw [hexp]
      push_cast
      field_simp
      linear_combination (-(x ^ 2)) * Complex.I_sq

theorem nonnegTaylorAtZero_slice_pair {γ t : ℝ} (hγ : γ ≠ 0) :
    NonnegTaylorAtZero (fun x => weierstrassE1 (((t : ℂ) - I * x) / γ) *
      weierstrassE1 (((t : ℂ) + I * x) / γ)) := by
  have e : (fun x => weierstrassE1 (((t : ℂ) - I * x) / γ) *
      weierstrassE1 (((t : ℂ) + I * x) / γ)) =
      (fun _ => ((Real.exp (2 * t / γ) * (γ - t) ^ 2 / γ ^ 2 : ℝ) : ℂ)) +
        ((fun _ => ((Real.exp (2 * t / γ) / γ ^ 2 : ℝ) : ℂ)) * (fun x : ℂ => x)) *
          (fun x : ℂ => x) := by
    funext x
    rw [weierstrassE1_slice_pair hγ x]
    rfl
  rw [e]
  refine (nonnegTaylorAtZero_const ?_).add
    (((nonnegTaylorAtZero_const ?_).mul nonnegTaylorAtZero_id).mul nonnegTaylorAtZero_id)
  · exact Complex.zero_le_real.mpr (by positivity)
  · exact Complex.zero_le_real.mpr (by positivity)

/-- The slice product in the centred variable. -/
theorem xiSliceProduct_eq_XiC (t : ℝ) (x : ℂ) :
    xiSliceProduct t x = XiC ((t : ℂ) - I * x) * XiC ((t : ℂ) + I * x) := by
  unfold xiSliceProduct XiC
  congr 2 <;> ring_nf <;> simp only [Complex.I_sq] <;> ring

theorem zero_le_XiC_zero_mul_self : 0 ≤ XiC 0 * XiC 0 := by
  have hc := XiC_conj 0
  rw [map_zero] at hc
  have him : (XiC 0).im = 0 := by
    have := congrArg Complex.im hc
    rw [Complex.conj_im] at this
    linarith
  rw [Complex.nonneg_iff]
  constructor
  · simp only [Complex.mul_re, him, mul_zero, sub_zero]
    exact mul_self_nonneg _
  · simp [Complex.mul_im, him]

/-- **Under the Riemann hypothesis the slice product has nonnegative Taylor coefficients.** -/
theorem nonnegTaylorAtZero_xiSliceProduct (hRH : RiemannHypothesis) (t : ℝ) :
    NonnegTaylorAtZero (xiSliceProduct t) := by
  set φm : ℂ → ℂ := fun x => (t : ℂ) - I * x with hφm
  set φp : ℂ → ℂ := fun x => (t : ℂ) + I * x with hφp
  have hcm : Continuous φm := by rw [hφm]; fun_prop
  have hcp : Continuous φp := by rw [hφp]; fun_prop
  have hP : TendstoLocallyUniformlyOn
      (fun S x => ∏ q ∈ S, weierstrassE1 (x / xiSpectralPoint q)) xiCanonicalProduct atTop
      Set.univ := xiCanonicalProduct_hasProdLocallyUniformlyOn
  have hPcont : Continuous xiCanonicalProduct :=
    continuous_iff_continuousAt.mpr fun z => (xiCanonicalProduct_analytic z (Set.mem_univ z)).continuousAt
  have hPdiff : Differentiable ℂ xiCanonicalProduct := fun z =>
    (xiCanonicalProduct_analytic z (Set.mem_univ z)).differentiableAt
  have hm := TendstoLocallyUniformlyOn.comp hP φm (Set.mapsTo_univ φm Set.univ) hcm.continuousOn
  have hp := TendstoLocallyUniformlyOn.comp hP φp (Set.mapsTo_univ φp Set.univ) hcp.continuousOn
  have hmul := hm.mul₀ hp (hPcont.comp hcm).continuousOn (hPcont.comp hcp).continuousOn
  -- finite partial products are pairs of Weierstrass factors
  have hfin : ∀ S : Finset XiZeroCopy, NonnegTaylorAtZero
      (((fun S x => ∏ q ∈ S, weierstrassE1 (x / xiSpectralPoint q)) S ∘ φm) *
        ((fun S x => ∏ q ∈ S, weierstrassE1 (x / xiSpectralPoint q)) S ∘ φp)) := by
    intro S
    have e : (((fun S x => ∏ q ∈ S, weierstrassE1 (x / xiSpectralPoint q)) S ∘ φm) *
        ((fun S x => ∏ q ∈ S, weierstrassE1 (x / xiSpectralPoint q)) S ∘ φp)) =
        fun x => ∏ q ∈ S, (weierstrassE1 (φm x / xiSpectralPoint q) *
          weierstrassE1 (φp x / xiSpectralPoint q)) := by
      funext x
      simp only [Pi.mul_apply, Function.comp_apply]
      rw [Finset.prod_mul_distrib]
    rw [e]
    refine nonnegTaylorAtZero_finsetProd S fun q _ => ?_
    obtain ⟨γ, hγ⟩ := xiSpectralPoint_real_of_rh hRH q
    have hγ0 : γ ≠ 0 := by
      intro h0
      apply xiSpectralPoint_ne_zero q
      rw [hγ, h0, Complex.ofReal_zero]
    simp only [hγ, hφm, hφp]
    exact nonnegTaylorAtZero_slice_pair hγ0
  have hlim : NonnegTaylorAtZero ((xiCanonicalProduct ∘ φm) * (xiCanonicalProduct ∘ φp)) :=
    NonnegTaylorAtZero.of_tendstoLocallyUniformlyOn hfin
      ((hPdiff.comp (by rw [hφm]; fun_prop)).mul (hPdiff.comp (by rw [hφp]; fun_prop))) hmul
  have e : xiSliceProduct t = (fun _ => XiC 0 * XiC 0) *
      ((xiCanonicalProduct ∘ φm) * (xiCanonicalProduct ∘ φp)) := by
    funext x
    rw [xiSliceProduct_eq_XiC]
    have hX : ∀ a, XiC a = XiC 0 * xiCanonicalProduct a := fun a => by
      simpa only [Pi.mul_apply] using congrFun XiC_eq_constant_mul_canonicalProduct a
    simp only [Pi.mul_apply, Function.comp_apply, hφm, hφp]
    rw [hX ((t : ℂ) - I * x), hX ((t : ℂ) + I * x)]
    ring
  rw [e]
  exact (nonnegTaylorAtZero_const zero_le_XiC_zero_mul_self).mul hlim

/-- Under the Riemann hypothesis every slice Taylor coefficient is nonnegative. -/
theorem xiSliceCoeff_nonneg_of_riemannHypothesis (hRH : RiemannHypothesis) (t : ℝ) (n : ℕ) :
    0 ≤ xiSliceCoeff t n := by
  unfold xiSliceCoeff
  have hfac : ((n.factorial : ℂ))⁻¹ = (((n.factorial : ℝ))⁻¹ : ℝ) := by push_cast; rfl
  rw [hfac]
  exact mul_nonneg (Complex.zero_le_real.mpr (by positivity))
    ((nonnegTaylorAtZero_xiSliceProduct hRH t).2 n)

/-- **The Riemann hypothesis is Taylor positivity on every horizontal slice.** -/
theorem riemannHypothesis_iff_xiSliceCoeff_nonneg :
    RiemannHypothesis ↔ ∀ t : ℝ, ∀ n : ℕ, 0 ≤ xiSliceCoeff t n :=
  ⟨fun hRH t n => xiSliceCoeff_nonneg_of_riemannHypothesis hRH t n,
    riemannHypothesis_of_xiSliceCoeff_nonneg⟩

end

end RHTower
