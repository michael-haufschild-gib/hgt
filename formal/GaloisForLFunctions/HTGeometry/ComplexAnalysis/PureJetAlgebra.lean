import GaloisForLFunctions.HTGeometry.ComplexAnalysis.AntiholomorphicJets

/-!
# Algebra of pure Wirtinger jets

Conjugating values exchanges holomorphic and antiholomorphic jets. Complex-affine changes
of argument multiply each pure jet by the corresponding power of the slope. Constant
multiplication commutes with the jets, and their recursive order may be reassociated.
-/

open Complex
open scoped ContDiff ComplexConjugate
namespace HTGeometry
noncomputable section

lemma dz_const_mul_of_differentiable {f : ℂ → ℂ} {z : ℂ}
    (hf : DifferentiableAt ℝ f z) (a : ℂ) :
    dz (fun w => a * f w) z = a * dz f z := by
  rw [dz_eq_of_hasFDerivAt (hf.hasFDerivAt.const_mul a), wirtingerHol_smul]
  rfl

lemma dz_const_add_of_differentiable {f : ℂ → ℂ} {z : ℂ}
    (hf : DifferentiableAt ℝ f z) (a : ℂ) :
    dz (fun w => a + f w) z = dz f z := by
  rw [dz_eq_of_hasFDerivAt (hf.hasFDerivAt.const_add a)]
  rfl

/-- Constant multiplication commutes with every holomorphic jet. -/
theorem iteratedDz_const_mul {f : ℂ → ℂ} (hf : ContDiff ℝ ∞ f) (a : ℂ) (n : ℕ) :
    iteratedDz n (fun z => a * f z) = fun z => a * iteratedDz n f z := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [iteratedDz, ih]
      funext z
      exact dz_const_mul_of_differentiable
        ((contDiff_iteratedDz hf n).differentiable (by simp) z) a

lemma iteratedDz_succ_right (f : ℂ → ℂ) (n : ℕ) :
    iteratedDz (n + 1) f = iteratedDz n (dz f) := by
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg dz ih

lemma iteratedDzbar_succ_right (f : ℂ → ℂ) (n : ℕ) :
    iteratedDzbar (n + 1) f = iteratedDzbar n (dzbar f) := by
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg dzbar ih

lemma dzbar_conjugate_of_differentiable {f : ℂ → ℂ} {z : ℂ}
    (hf : DifferentiableAt ℝ f z) :
    dzbar (fun w => conj (f w)) z = conj (dz f z) := by
  have hd : HasFDerivAt (fun w => conj (f w))
      (Complex.conjCLE.toContinuousLinearMap.comp (fderiv ℝ f z)) z :=
    Complex.conjCLE.hasFDerivAt.comp z hf.hasFDerivAt
  rw [dzbar_eq_of_hasFDerivAt hd]
  change (conj (fderiv ℝ f z 1) + Complex.I * conj (fderiv ℝ f z Complex.I)) / 2 =
    conj ((fderiv ℝ f z 1 - Complex.I * fderiv ℝ f z Complex.I) / 2)
  simp only [map_div₀, map_sub, map_mul, map_ofNat, Complex.conj_I]
  ring

lemma dz_conjugate_of_differentiable {f : ℂ → ℂ} {z : ℂ}
    (hf : DifferentiableAt ℝ f z) :
    dz (fun w => conj (f w)) z = conj (dzbar f z) := by
  have hd : HasFDerivAt (fun w => conj (f w))
      (Complex.conjCLE.toContinuousLinearMap.comp (fderiv ℝ f z)) z :=
    Complex.conjCLE.hasFDerivAt.comp z hf.hasFDerivAt
  rw [dz_eq_of_hasFDerivAt hd]
  change (conj (fderiv ℝ f z 1) - Complex.I * conj (fderiv ℝ f z Complex.I)) / 2 =
    conj ((fderiv ℝ f z 1 + Complex.I * fderiv ℝ f z Complex.I) / 2)
  simp only [map_div₀, map_add, map_mul, map_ofNat, Complex.conj_I]
  ring

/-- Conjugating values exchanges pure jets at every order. -/
theorem iteratedDzbar_conjugate {f : ℂ → ℂ} (hf : ContDiff ℝ ∞ f) (n : ℕ) :
    iteratedDzbar n (fun z => conj (f z)) = fun z => conj (iteratedDz n f z) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [iteratedDzbar, ih]
      funext z
      exact dzbar_conjugate_of_differentiable
        ((contDiff_iteratedDz hf n).differentiable (by simp) z)

theorem iteratedDz_conjugate {f : ℂ → ℂ} (hf : ContDiff ℝ ∞ f) (n : ℕ) :
    iteratedDz n (fun z => conj (f z)) = fun z => conj (iteratedDzbar n f z) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [iteratedDz, ih]
      funext z
      exact dz_conjugate_of_differentiable
        ((contDiff_iteratedDzbar hf n).differentiable (by simp) z)

lemma dz_comp_affine {f : ℂ → ℂ} (hf : Differentiable ℝ f) (a b z : ℂ) :
    dz (fun w => f (b + a * w)) z = a * dz f (b + a * z) := by
  have hi : HasFDerivAt (fun w : ℂ => b + a * w)
      (a • ContinuousLinearMap.id ℝ ℂ) z :=
    ((hasFDerivAt_id z).const_mul a).const_add b
  have hd : HasFDerivAt (fun w => f (b + a * w))
      ((fderiv ℝ f (b + a * z)).comp (a • ContinuousLinearMap.id ℝ ℂ)) z :=
    (hf (b + a * z)).hasFDerivAt.comp z hi
  rw [dz_eq_of_hasFDerivAt hd]
  change (fderiv ℝ f (b + a * z) (a * 1) -
    Complex.I * fderiv ℝ f (b + a * z) (a * Complex.I)) / 2 = _
  rw [mul_one, wirtinger_decomp (fderiv ℝ f _) a,
    wirtinger_decomp (fderiv ℝ f _) (a * Complex.I)]
  simp only [map_mul, Complex.conj_I, mul_neg, dz]
  linear_combination -(a * wirtingerHol (fderiv ℝ f (b + a * z)) -
    conj a * wirtingerAntihol (fderiv ℝ f (b + a * z))) / 2 * Complex.I_sq

/-- Complex-affine pullback multiplies the pure holomorphic jet by the slope power. -/
theorem iteratedDz_comp_affine {f : ℂ → ℂ} (hf : ContDiff ℝ ∞ f)
    (a b : ℂ) (n : ℕ) :
    iteratedDz n (fun z => f (b + a * z)) =
      fun z => a ^ n * iteratedDz n f (b + a * z) := by
  induction n with
  | zero => simp only [iteratedDz, pow_zero, one_mul]
  | succ n ih =>
      rw [iteratedDz, ih]
      funext z
      have hs : ContDiff ℝ ∞ (fun w => iteratedDz n f (b + a * w)) :=
        (contDiff_iteratedDz hf n).comp
          (contDiff_const.add (contDiff_const.mul contDiff_id))
      rw [dz_const_mul_of_differentiable (hs.differentiable (by simp) z),
        dz_comp_affine ((contDiff_iteratedDz hf n).differentiable (by simp))]
      simp only [iteratedDz, pow_succ]
      ring

/-- Complex-affine pullback multiplies the antiholomorphic jet by the conjugate slope power. -/
theorem iteratedDzbar_comp_affine {f : ℂ → ℂ} (hf : ContDiff ℝ ∞ f)
    (a b : ℂ) (n : ℕ) :
    iteratedDzbar n (fun z => f (b + a * z)) =
      fun z => conj a ^ n * iteratedDzbar n f (b + a * z) := by
  have hg : ContDiff ℝ ∞ (fun z => conj (f z)) := Complex.conjCLE.contDiff.comp hf
  have he := iteratedDz_conjugate hf n
  have hs : ContDiff ℝ ∞ (fun z => conj (f (b + a * z))) :=
    hg.comp (contDiff_const.add (contDiff_const.mul contDiff_id))
  have hc := iteratedDzbar_conjugate hs n
  have hcc (z : ℂ) : conj (conj z) = z := star_star z
  simp only [hcc] at hc
  rw [iteratedDz_comp_affine hg a b n, he] at hc
  simpa only [map_mul, map_pow, hcc] using hc

end
end HTGeometry
