import GaloisForLFunctions.RHTower.SelbergMaassCongruenceTrace

/-!
# Pointwise energy of the actual finite Maass trace

Differentiation of the literal complex squared norm retains both first-derivative
squares and the original second derivative. The actual Maass eigen-equation then
gives the trace Laplacian as twice its full planar gradient density minus spectral
mass. No eigen-equation for the squared trace is assumed.

The quarter-energy density is half this actual Laplacian plus the exact spectral
mass correction. The statements use the source's real C² regularity.
-/

open Complex Set Filter Topology UpperHalfPlane
open scoped ContDiff
namespace GaloisForLFunctions.RHTower.SelbergMaassTraceEnergy
open SelbergMaassCongruenceTrace
noncomputable section

/-- The actual real Fréchet derivative in a complex coordinate direction. -/
def dir {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v : ℂ) (F : ℂ → E) (z : ℂ) : E := fderiv ℝ F z v

/-- One directional derivative of a C² germ is a C¹ germ. -/
theorem dir_contDiffAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : ℂ → E} {z : ℂ} (hf : ContDiffAt ℝ 2 F z) (v : ℂ) :
    ContDiffAt ℝ 1 (dir v F) z :=
  (hf.fderiv_right (by norm_num)).clm_apply contDiffAt_const

private theorem pair_dir {F G : ℂ → ℂ} {z : ℂ}
    (hf : DifferentiableAt ℝ F z) (hg : DifferentiableAt ℝ G z) (v : ℂ) :
    dir v (fun w => (F w * (starRingEnd ℂ) (G w)).re) z =
      (dir v F z * (starRingEnd ℂ) (G z) + F z * (starRingEnd ℂ) (dir v G z)).re := by
  have hc := (Complex.conjCLE : ℂ →L[ℝ] ℂ).hasFDerivAt.comp z hg.hasFDerivAt
  have hp := Complex.reCLM.hasFDerivAt.comp z (hf.hasFDerivAt.mul hc)
  change HasFDerivAt (fun w => (F w * (starRingEnd ℂ) (G w)).re) _ z at hp
  have h := congrArg (fun L => L v) hp.fderiv
  change dir v (fun w => (F w * (starRingEnd ℂ) (G w)).re) z =
    (F z * (starRingEnd ℂ) (dir v G z) + (starRingEnd ℂ) (G z) * dir v F z).re at h
  rw [h]
  congr 1
  ring

/-- The first directional derivative of the literal complex squared norm. -/
theorem normSq_dir {F : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℝ F z) (v : ℂ) :
    dir v (fun w => Complex.normSq (F w)) z =
      2 * (dir v F z * (starRingEnd ℂ) (F z)).re := by
  have he : (fun w => Complex.normSq (F w)) = (fun w => (F w * (starRingEnd ℂ) (F w)).re) := by
    funext w
    rw [Complex.mul_conj, Complex.ofReal_re]
  rw [he, pair_dir hf hf]
  simp only [Complex.add_re, Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

/-- The second directional derivative retains the squared first derivative and the second-derivative pairing. -/
theorem normSq_second_dir {F : ℂ → ℂ} {z : ℂ} (hf : ContDiffAt ℝ 2 F z) (v : ℂ) :
    dir v (dir v (fun w => Complex.normSq (F w))) z =
      2 * (Complex.normSq (dir v F z) +
        (dir v (dir v F) z * (starRingEnd ℂ) (F z)).re) := by
  have he : dir v (fun w => Complex.normSq (F w)) =ᶠ[𝓝 z]
      (fun w => 2 * (dir v F w * (starRingEnd ℂ) (F w)).re) := by
    filter_upwards [hf.eventually (by norm_num)] with w hw
    exact normSq_dir (hw.differentiableAt (by norm_num)) v
  have hd := (dir_contDiffAt hf v).differentiableAt (by norm_num)
  have hp : DifferentiableAt ℝ (fun w => (dir v F w * (starRingEnd ℂ) (F w)).re) z :=
    Complex.reCLM.differentiableAt.comp z (hd.mul
      ((Complex.conjCLE : ℂ →L[ℝ] ℂ).differentiableAt.comp z (hf.differentiableAt (by norm_num))))
  change fderiv ℝ (dir v (fun w => Complex.normSq (F w))) z v = _
  rw [he.fderiv_eq, (hp.hasFDerivAt.const_mul 2).fderiv]
  change 2 * dir v (fun w => (dir v F w * (starRingEnd ℂ) (F w)).re) z = _
  rw [pair_dir hd (hf.differentiableAt (by norm_num)), Complex.mul_conj,
    Complex.add_re, Complex.ofReal_re]
  ring

/-- The sum of the two actual real second directional derivatives of a real chart field. -/
def realLaplacian (F : ℂ → ℝ) (z : ℂ) : ℝ :=
  dir 1 (dir 1 F) z + dir Complex.I (dir Complex.I F) z

/-- Directional differentiation commutes with a finite sum of differentiable fields. -/
theorem dir_sum {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ι : Type*} (s : Finset ι) {F : ι → ℂ → E} {z : ℂ}
    (hf : ∀ i ∈ s, DifferentiableAt ℝ (F i) z) (v : ℂ) :
    dir v (fun w => ∑ i ∈ s, F i w) z = ∑ i ∈ s, dir v (F i) z := by
  rw [dir, fderiv_fun_sum hf]
  simp only [sum_apply, dir]

/-- Two directional differentiations commute with a finite sum of C² fields. -/
theorem second_dir_sum {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ι : Type*} (s : Finset ι) {F : ι → ℂ → E} {z : ℂ}
    (hf : ∀ i ∈ s, ContDiffAt ℝ 2 (F i) z) (v : ℂ) :
    dir v (dir v (fun w => ∑ i ∈ s, F i w)) z =
      ∑ i ∈ s, dir v (dir v (F i)) z := by
  have he : dir v (fun w => ∑ i ∈ s, F i w) =ᶠ[𝓝 z]
      (fun w => ∑ i ∈ s, dir v (F i) w) := by
    have hall : ∀ᶠ w in 𝓝 z, ∀ i ∈ s, ContDiffAt ℝ 2 (F i) w :=
      (Filter.eventually_all_finset s).mpr (fun i hi => (hf i hi).eventually (by norm_num))
    filter_upwards [hall] with w hw
    exact dir_sum s (fun i hi => (hw i hi).differentiableAt (by norm_num)) v
  change fderiv ℝ (dir v (fun w => ∑ i ∈ s, F i w)) z v = _
  rw [he.fderiv_eq]
  exact dir_sum s (fun i hi => (dir_contDiffAt (hf i hi) v).differentiableAt (by norm_num)) v

private theorem normSq_smooth {F : ℂ → ℂ} {z : ℂ} (hf : ContDiffAt ℝ 2 F z) :
    ContDiffAt ℝ 2 (fun w => Complex.normSq (F w)) z := by
  have hr := Complex.reCLM.contDiff.contDiffAt.comp z hf
  have hi := Complex.imCLM.contDiff.contDiffAt.comp z hf
  simpa only [Function.comp_apply, Complex.reCLM_apply, Complex.imCLM_apply,
    Complex.normSq_apply] using (hr.mul hr).add (hi.mul hi)

/-- The actual squared norm satisfies its full Laplacian identity, with gradient energy retained. -/
theorem maass_normSq_laplacian (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam) (z : ℍ) :
    realLaplacian (fun w => Complex.normSq (f.1.1 (ofComplex w))) (z : ℂ) =
      2 * (Complex.normSq (dir 1 (f.1.1 ∘ ofComplex) (z : ℂ)) +
        Complex.normSq (dir Complex.I (f.1.1 ∘ ofComplex) (z : ℂ)) -
          lam / z.im ^ 2 * Complex.normSq (f.1.1 z)) := by
  let F := f.1.1 ∘ ofComplex
  have hf : ContDiffAt ℝ 2 F (z : ℂ) :=
    f.2.2.1.1.contDiffAt (isOpen_upperHalfPlaneSet.mem_nhds z.im_pos)
  have hz : (z.im : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr z.im_pos.ne'
  have he := f.2.2.1.2 z
  change -(z.im : ℂ) ^ 2 * (dir 1 (dir 1 F) (z : ℂ) +
    dir Complex.I (dir Complex.I F) (z : ℂ)) = (lam : ℂ) * f.1.1 z at he
  have hs : dir 1 (dir 1 F) (z : ℂ) + dir Complex.I (dir Complex.I F) (z : ℂ) =
      ((-(lam / z.im ^ 2) : ℝ) : ℂ) * f.1.1 z := by
    apply (mul_left_cancel₀ (pow_ne_zero 2 hz))
    push_cast
    field_simp
    linear_combination -he
  have hr := congrArg (fun c : ℂ => (c * (starRingEnd ℂ) (f.1.1 z)).re) hs
  rw [add_mul, Complex.add_re, mul_assoc, Complex.mul_conj, ← Complex.ofReal_mul,
    Complex.ofReal_re] at hr
  change realLaplacian (fun w => Complex.normSq (F w)) (z : ℂ) = _
  rw [realLaplacian, normSq_second_dir hf, normSq_second_dir hf]
  have hF : F (z : ℂ) = f.1.1 z := by simp only [F, Function.comp_apply, ofComplex_apply]
  rw [hF]
  change 2 * (Complex.normSq (dir 1 F (z : ℂ)) + _) +
    2 * (Complex.normSq (dir Complex.I F (z : ℂ)) + _) = _
  dsimp only [F] at hr ⊢
  linarith

/-- Sum of the actual planar squared gradients over the finite congruence quotient. -/
def gradientDensity (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam) (z : ℂ) : ℝ :=
  ∑ q : Deck N, (Complex.normSq (dir 1 ((quotientForm N f q).1.1 ∘ ofComplex) z) +
    Complex.normSq (dir Complex.I ((quotientForm N f q).1.1 ∘ ofComplex) z))

/-- The actual finite trace Laplacian equals twice full gradient density minus spectral mass. -/
theorem trace_laplacian (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam) (z : ℍ) :
    realLaplacian (density N f ∘ ofComplex) (z : ℂ) =
      2 * (gradientDensity N f (z : ℂ) - lam / z.im ^ 2 * density N f z) := by
  have hq (q : Deck N) : ContDiffAt ℝ 2
      (fun w => Complex.normSq ((quotientForm N f q).1.1 (ofComplex w))) (z : ℂ) :=
    normSq_smooth ((quotientForm N f q).2.2.1.1.contDiffAt (isOpen_upperHalfPlaneSet.mem_nhds z.im_pos))
  unfold realLaplacian
  change dir 1 (dir 1 (fun w => ∑ q : Deck N, Complex.normSq ((quotientForm N f q).1.1 (ofComplex w)))) (z : ℂ) +
    dir Complex.I (dir Complex.I (fun w => ∑ q : Deck N, Complex.normSq ((quotientForm N f q).1.1 (ofComplex w)))) (z : ℂ) = _
  rw [second_dir_sum Finset.univ (fun q _ => hq q), second_dir_sum Finset.univ (fun q _ => hq q),
    ← Finset.sum_add_distrib]
  have he := Finset.sum_congr (s₁ := (Finset.univ : Finset (Deck N))) rfl
    (fun q _ => maass_normSq_laplacian N (quotientForm N f q) z)
  change (∑ q : Deck N, realLaplacian _ _) = _
  rw [he]
  simp only [gradientDensity, density, ← Finset.mul_sum, Finset.sum_sub_distrib]

/-- Each original squared derivative in the trace gradient density is nonnegative. -/
theorem gradientDensity_nonneg (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam) (z : ℂ) :
    0 ≤ gradientDensity N f z :=
  Finset.sum_nonneg (fun _ _ => add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _))

/-- A real chart directional derivative lowers differentiability by one. -/
theorem dir_contDiffOn {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : ℂ → E} {n m : WithTop ℕ∞}
    (hf : ContDiffOn ℝ n F {z : ℂ | 0 < z.im}) (hmn : m + 1 ≤ n) (v : ℂ) :
    ContDiffOn ℝ m (dir v F) {z : ℂ | 0 < z.im} := by
  intro z hz
  exact (((hf.contDiffAt (isOpen_upperHalfPlaneSet.mem_nhds hz)).fderiv_right hmn).clm_apply
    contDiffAt_const).contDiffWithinAt

/-- The actual trace currents have C¹ chart regularity. -/
theorem trace_dir_contDiffOn (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam) (v : ℂ) :
    ContDiffOn ℝ 1 (dir v (density N f ∘ ofComplex)) {z : ℂ | 0 < z.im} :=
  dir_contDiffOn (density_contDiffOn N f) (by norm_num) v

/-- Every second chart derivative of the actual trace is continuous at positive height. -/
theorem trace_second_dir_continuousOn (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam) (v w : ℂ) :
    ContinuousOn (dir v (dir w (density N f ∘ ofComplex))) {z : ℂ | 0 < z.im} :=
  (dir_contDiffOn (trace_dir_contDiffOn N f w) (m := 0) (by norm_num) v).continuousOn

/-- Actual planar gradient density minus quarter hyperbolic mass. -/
def quarterDensity (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam) (z : ℍ) : ℝ :=
  gradientDensity N f (z : ℂ) - density N f z / (4 * z.im ^ 2)

/-- The actual quarter-energy density retains half the trace Laplacian and the exact spectral mass correction. -/
theorem quarterDensity_eq_laplacian_mass (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam) (z : ℍ) :
    quarterDensity N f z = (1 / 2) * realLaplacian (density N f ∘ ofComplex) (z : ℂ) +
      (lam - 1 / 4) * density N f z / z.im ^ 2 := by
  rw [trace_laplacian, quarterDensity]
  ring

end
end GaloisForLFunctions.RHTower.SelbergMaassTraceEnergy
