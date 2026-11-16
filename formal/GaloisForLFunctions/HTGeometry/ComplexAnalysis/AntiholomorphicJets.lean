import GaloisForLFunctions.HTGeometry.ComplexAnalysis.CompensatedSlices
import GaloisForLFunctions.HTGeometry.InterfinityGeometry.ParametricSmoothness

/-!
# Pure antiholomorphic jets and smooth perturbations

A holomorphic multiplier commutes with every power of `∂̄`. Thus a smooth multiple of `|z|²`
has zero pure antiholomorphic jets at the origin. A parameterized Hadamard identity extends
this invariance to smooth compositions with squared-norm perturbations of maps.

Conjugate-affine coordinate changes exchange the two Wirtinger operators at every order.
All these identities are local: equal germs have equal iterated Wirtinger derivatives.
-/

open Complex
open scoped ComplexConjugate ContDiff Topology
namespace HTGeometry
noncomputable section

/-- Repeated holomorphic Wirtinger differentiation of a smooth real function. -/
def iteratedDz : ℕ → (ℂ → ℂ) → ℂ → ℂ
  | 0, f => f
  | n + 1, f => dz (iteratedDz n f)

/-- Repeated antiholomorphic Wirtinger differentiation. -/
def iteratedDzbar : ℕ → (ℂ → ℂ) → ℂ → ℂ
  | 0, f => f
  | n + 1, f => dzbar (iteratedDzbar n f)

/-- Higher holomorphic Wirtinger derivatives depend only on the germ. -/
theorem iteratedDz_eventuallyEq {f g : ℂ → ℂ} {z : ℂ}
    (h : f =ᶠ[nhds z] g) (n : ℕ) : iteratedDz n f =ᶠ[nhds z] iteratedDz n g := by
  induction n with
  | zero => exact h
  | succ n ih =>
      filter_upwards [ih.fderiv (𝕜 := ℝ)] with w hw
      exact congrArg wirtingerHol hw

/-- Higher antiholomorphic Wirtinger derivatives depend only on the germ. -/
theorem iteratedDzbar_eventuallyEq {f g : ℂ → ℂ} {z : ℂ}
    (h : f =ᶠ[nhds z] g) (n : ℕ) : iteratedDzbar n f =ᶠ[nhds z] iteratedDzbar n g := by
  induction n with
  | zero => exact h
  | succ n ih =>
      filter_upwards [ih.fderiv (𝕜 := ℝ)] with w hw
      exact congrArg wirtingerAntihol hw

/-- The Wirtinger operators preserve infinite real smoothness. -/
theorem contDiff_infty_dz {f : ℂ → ℂ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (dz f) := by
  have hd : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (by simp)
  exact ((hd.clm_apply contDiff_const).sub
    (contDiff_const.mul (hd.clm_apply contDiff_const))).div_const 2

theorem contDiff_infty_dzbar {f : ℂ → ℂ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (dzbar f) := by
  have heq : dzbar f = fun z => wirtingerAntiholL (fderiv ℝ f z) :=
    funext fun z => (wirtingerAntiholL_apply _).symm
  rw [heq]
  exact wirtingerAntiholL.contDiff.comp (hf.fderiv_right (m := ∞) (by simp))

theorem contDiff_iteratedDz {f : ℂ → ℂ} (hf : ContDiff ℝ ∞ f) (n : ℕ) :
    ContDiff ℝ ∞ (iteratedDz n f) := by
  induction n with
  | zero => exact hf
  | succ n ih => exact contDiff_infty_dz ih

theorem contDiff_iteratedDzbar {f : ℂ → ℂ} (hf : ContDiff ℝ ∞ f) (n : ℕ) :
    ContDiff ℝ ∞ (iteratedDzbar n f) := by
  induction n with
  | zero => exact hf
  | succ n ih => exact contDiff_infty_dzbar ih

/-- Every pure antiholomorphic derivative commutes with a holomorphic multiplier. -/
theorem iteratedDzbar_holomorphic_mul {h f : ℂ → ℂ}
    (hh : Differentiable ℂ h) (hf : ContDiff ℝ ∞ f) (n : ℕ) :
    iteratedDzbar n (fun z => h z * f z) = fun z => h z * iteratedDzbar n f z := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [iteratedDzbar, ih]
      funext z
      exact dzbar_holomorphic_mul (hh z)
        ((contDiff_iteratedDzbar hf n).differentiable (by simp) z)

/-- A holomorphic zero annihilates every pure antiholomorphic jet of its product. -/
theorem iteratedDzbar_holomorphic_mul_eq_zero {h f : ℂ → ℂ}
    (hh : Differentiable ℂ h) (hf : ContDiff ℝ ∞ f) {z : ℂ} (hz : h z = 0) (n : ℕ) :
    iteratedDzbar n (fun w => h w * f w) z = 0 := by
  simp only [iteratedDzbar_holomorphic_mul hh hf, hz, zero_mul]

/-- Multiples of `|z|²` have zero pure antiholomorphic jets at the origin. -/
theorem iteratedDzbar_normSq_mul_zero {f : ℂ → ℂ} (hf : ContDiff ℝ ∞ f) (n : ℕ) :
    iteratedDzbar n (fun z => (Complex.normSq z : ℂ) * f z) 0 = 0 := by
  have heq : (fun z => (Complex.normSq z : ℂ) * f z) =
      fun z => z * (conj z * f z) := by
    funext z
    rw [← Complex.mul_conj]
    ring
  rw [heq]
  exact iteratedDzbar_holomorphic_mul_eq_zero differentiable_id
    (Complex.conjCLE.contDiff.mul hf) rfl n

/-- Addition commutes with every pure antiholomorphic derivative. -/
theorem iteratedDzbar_add {f g : ℂ → ℂ} (hf : ContDiff ℝ ∞ f)
    (hg : ContDiff ℝ ∞ g) (n : ℕ) :
    iteratedDzbar n (fun z => f z + g z) = fun z => iteratedDzbar n f z + iteratedDzbar n g z := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [iteratedDzbar, ih]
      funext z
      change wirtingerAntihol (fderiv ℝ (iteratedDzbar n f + iteratedDzbar n g) z) = _
      rw [fderiv_add
        ((contDiff_iteratedDzbar hf n).differentiable (by simp) z)
        ((contDiff_iteratedDzbar hg n).differentiable (by simp) z), wirtingerAntihol_add]
      rfl

/-- Adding a smooth multiple of `|z|²` preserves all pure antiholomorphic jets at zero. -/
theorem iteratedDzbar_add_normSq_mul_zero {f g : ℂ → ℂ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (n : ℕ) :
    iteratedDzbar n (fun z => f z + (Complex.normSq z : ℂ) * g z) 0 =
      iteratedDzbar n f 0 := by
  have hq : ContDiff ℝ ∞ (fun z : ℂ => (Complex.normSq z : ℂ) * g z) := by
    have heq : (fun z : ℂ => (Complex.normSq z : ℂ) * g z) =
        fun z => z * conj z * g z := by
      funext z
      rw [Complex.mul_conj]
    rw [heq]
    exact (contDiff_id.mul Complex.conjCLE.contDiff).mul hg
  simp only [iteratedDzbar_add hf hq, iteratedDzbar_normSq_mul_zero hg, add_zero]

/-- Conjugate-affine changes of coordinate exchange the two Wirtinger operators. -/
theorem dzbar_comp_conj_affine {f : ℂ → ℂ} (hf : Differentiable ℝ f)
    (a b z : ℂ) :
    dzbar (fun w => f (b + a * conj w)) z = a * dz f (b + a * conj z) := by
  have hi : HasFDerivAt (fun w : ℂ => b + a * conj w)
      (a • Complex.conjCLE.toContinuousLinearMap) z :=
    (Complex.conjCLE.hasFDerivAt.const_mul a).const_add b
  have hc : HasFDerivAt (fun w => f (b + a * conj w))
      ((fderiv ℝ f (b + a * conj z)).comp (a • Complex.conjCLE.toContinuousLinearMap)) z :=
    (hf _).hasFDerivAt.comp z hi
  rw [dzbar_eq_of_hasFDerivAt hc]
  change ((fderiv ℝ f (b + a * conj z)) (a * conj 1) +
    Complex.I * (fderiv ℝ f (b + a * conj z)) (a * conj Complex.I)) / 2 = _
  simp only [map_one, mul_one, Complex.conj_I, mul_neg]
  rw [map_neg]
  rw [wirtinger_decomp (fderiv ℝ f _) a,
    wirtinger_decomp (fderiv ℝ f _) (a * Complex.I)]
  simp only [map_mul, Complex.conj_I, mul_neg]
  dsimp only [dz]
  linear_combination -(a * wirtingerHol (fderiv ℝ f (b + a * conj z)) -
    conj a * wirtingerAntihol (fderiv ℝ f (b + a * conj z))) / 2 * Complex.I_sq

/-- The exact power law for higher derivatives under a conjugate-affine map. -/
theorem iteratedDzbar_comp_conj_affine {f : ℂ → ℂ} (hf : ContDiff ℝ ∞ f)
    (a b : ℂ) (n : ℕ) :
    iteratedDzbar n (fun w => f (b + a * conj w)) =
      fun w => a ^ n * iteratedDz n f (b + a * conj w) := by
  induction n with
  | zero => simp only [iteratedDzbar, iteratedDz, pow_zero, one_mul]
  | succ n ih =>
      rw [iteratedDzbar, ih]
      funext z
      have hcomp : ContDiff ℝ ∞ (fun w => iteratedDz n f (b + a * conj w)) :=
        (contDiff_iteratedDz hf n).comp
          (contDiff_const.add (contDiff_const.mul Complex.conjCLE.contDiff))
      rw [dzbar_holomorphic_mul (differentiableAt_const _) (hcomp.differentiable (by simp) z),
        dzbar_comp_conj_affine ((contDiff_iteratedDz hf n).differentiable (by simp)),
        pow_succ, iteratedDz, mul_assoc]

open GaloisForLFunctions.HTGeometry.Interfinity

section SmoothRemainder

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The smooth divided difference along a scalar perturbation of a map. -/
def scalarPerturbationRemainder (F : E → ℂ) (g h : ℂ → E) (q : ℂ → ℝ) : ℂ → ℂ :=
  paramAvg fun z t => fderiv ℝ F (g z + t • (q z • h z)) (h z)

/-- Smooth divided differences remain smooth even where the scalar perturbation vanishes. -/
theorem contDiff_scalarPerturbationRemainder {F : E → ℂ} {g h : ℂ → E} {q : ℂ → ℝ}
    (hF : ContDiff ℝ ∞ F) (hg : ContDiff ℝ ∞ g) (hh : ContDiff ℝ ∞ h)
    (hq : ContDiff ℝ ∞ q) : ContDiff ℝ ∞ (scalarPerturbationRemainder F g h q) := by
  have hpath : ContDiff ℝ ∞ (fun p : ℂ × ℝ => g p.1 + p.2 • (q p.1 • h p.1)) :=
    (hg.comp contDiff_fst).add
      (contDiff_snd.smul ((hq.comp contDiff_fst).smul (hh.comp contDiff_fst)))
  have hI : ContDiff ℝ ∞ (fun p : ℂ × ℝ =>
      fderiv ℝ F (g p.1 + p.2 • (q p.1 • h p.1)) (h p.1)) :=
    ((hF.fderiv_right (m := ∞) (by simp)).comp hpath).clm_apply (hh.comp contDiff_fst)
  apply contDiff_infty.2
  intro n
  exact contDiff_paramAvg n (contDiff_infty.1 hI n)

/-- Hadamard's identity for a scalar perturbation, with an explicit smooth remainder. -/
theorem scalarPerturbation_identity {F : E → ℂ} (hF : ContDiff ℝ ∞ F)
    (g h : ℂ → E) (q : ℂ → ℝ) (z : ℂ) :
    F (g z + q z • h z) = F (g z) + (q z : ℂ) * scalarPerturbationRemainder F g h q z := by
  have hd (t : ℝ) : HasDerivAt (fun s : ℝ => F (g z + s • (q z • h z)))
      ((q z : ℂ) * fderiv ℝ F (g z + t • (q z • h z)) (h z)) t := by
    have hi : HasDerivAt (fun s : ℝ => g z + s • (q z • h z)) (q z • h z) t :=
      by simpa only [id_eq, one_smul] using
        ((hasDerivAt_id t).smul_const (q z • h z)).const_add (g z)
    have hc := ((hF.differentiable (by simp)) _).hasFDerivAt.comp_hasDerivAt t hi
    simpa only [Function.comp_def, map_smul, Complex.real_smul] using hc
  have hcont : Continuous (fun t : ℝ =>
      (q z : ℂ) * fderiv ℝ F (g z + t • (q z • h z)) (h z)) :=
    continuous_const.mul (((hF.fderiv_right (m := ∞) (by simp)).continuous.comp
      (continuous_const.add (continuous_id.smul continuous_const))).clm_apply continuous_const)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t (_ : t ∈ Set.uIcc (0 : ℝ) 1) => hd t) (hcont.intervalIntegrable 0 1)
  simp only [one_smul, zero_smul, add_zero, intervalIntegral.integral_const_mul] at hFTC
  exact (eq_add_of_sub_eq hFTC.symm).trans (by rw [add_comm]; rfl)

/-- A squared-norm perturbation of a smooth map is invisible to every pure antiholomorphic jet. -/
theorem iteratedDzbar_normSq_perturbation {F : E → ℂ} {g h : ℂ → E}
    (hF : ContDiff ℝ ∞ F) (hg : ContDiff ℝ ∞ g) (hh : ContDiff ℝ ∞ h) (n : ℕ) :
    iteratedDzbar n (fun z => F (g z + Complex.normSq z • h z)) 0 =
      iteratedDzbar n (fun z => F (g z)) 0 := by
  have hq : ContDiff ℝ ∞ Complex.normSq := by
    change ContDiff ℝ ∞ (fun z : ℂ => z.re * z.re + z.im * z.im)
    exact (Complex.reCLM.contDiff.mul Complex.reCLM.contDiff).add
      (Complex.imCLM.contDiff.mul Complex.imCLM.contDiff)
  have heq : (fun z => F (g z + Complex.normSq z • h z)) =
      fun z => F (g z) + (Complex.normSq z : ℂ) *
        scalarPerturbationRemainder F g h Complex.normSq z := by
    funext z
    exact scalarPerturbation_identity hF g h Complex.normSq z
  rw [heq]
  exact iteratedDzbar_add_normSq_mul_zero (hF.comp hg)
    (contDiff_scalarPerturbationRemainder hF hg hh hq) n

end SmoothRemainder

end
end HTGeometry
