import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.LocalErrors.Commutator

/-! # Local replacement of an interaction in a unitary evolution -/
open NormedSpace
namespace GaloisForLFunctions.HTGeometry.LocalPatches
noncomputable section
variable {A : Type*} [CStarAlgebra A]
local instance : NormedAlgebra ℚ A := .restrictScalars ℚ ℂ A

/-- Derivative of the conjugated observable at zero time. -/
def bracketStep (a x : A) := x*a-a*x

private def conjugateFlow (a x : A) (s : ℝ) :=
  exp (s • (-a))*x*exp (s • a)

private theorem flow_mem (a : A) (ha : a ∈ skewAdjoint A) (s : ℝ) :
    exp (s • a) ∈ unitary A := exp_mem_unitary_of_mem_skewAdjoint (skewAdjoint.smul_mem s ha)

private theorem conjugateFlow_norm (a x : A) (ha : a ∈ skewAdjoint A) (s : ℝ) :
    ‖conjugateFlow a x s‖ = ‖x‖ := by
  rw [conjugateFlow,CStarRing.norm_mul_mem_unitary _ (flow_mem _ ha _),
    CStarRing.norm_mem_unitary_mul _ (flow_mem _ ((skewAdjoint A).neg_mem ha) _)]

private theorem conjugateFlow_deriv (a x : A) (s : ℝ) :
    HasDerivAt (conjugateFlow a x) (conjugateFlow a (bracketStep a x) s) s := by
  have h := ((hasDerivAt_exp_smul_const (-a) s).mul_const x).fun_mul
    (hasDerivAt_exp_smul_const' a s)
  change HasDerivAt (fun r : ℝ => exp (r • (-a))*x*exp (r • a))
    (exp (s • (-a))*(x*a-a*x)*exp (s • a)) s
  convert h using 1
  noncomm_ring

/-- Equality of the first nested commutators postpones a boundary error to
order p. Unitarity eliminates any dependence on the norm of the full generator. -/
private theorem conjugate_difference (a b : A) (ha : a ∈ skewAdjoint A) (hb : b ∈ skewAdjoint A)
    (p : ℕ) (x : A) (hsame : ∀ j < p, bracketStep a ((bracketStep b)^[j] x) =
      bracketStep b ((bracketStep b)^[j] x)) (t : ℝ) (ht : 0 ≤ t) :
    ‖conjugateFlow a x t-conjugateFlow b x t‖ ≤ 2*‖(bracketStep b)^[p] x‖*t^p := by
  induction p generalizing x t with
  | zero =>
    simpa [conjugateFlow_norm a x ha,conjugateFlow_norm b x hb,two_mul] using
      norm_sub_le (conjugateFlow a x t) (conjugateFlow b x t)
  | succ p ih =>
    have hx : bracketStep a x = bracketStep b x := hsame 0 (Nat.zero_lt_succ _)
    let f (s : ℝ) := conjugateFlow a x s-conjugateFlow b x s
    let g (s : ℝ) := conjugateFlow a (bracketStep b x) s-conjugateFlow b (bracketStep b x) s
    have hd (s : ℝ) : HasDerivAt f (g s) s := by
      have hd' := (conjugateFlow_deriv a x s).sub (conjugateFlow_deriv b x s)
      rw [hx] at hd'
      exact hd'
    have htail (j : ℕ) (hj : j < p) :
        bracketStep a ((bracketStep b)^[j] (bracketStep b x)) =
        bracketStep b ((bracketStep b)^[j] (bracketStep b x)) := by
      simpa only [Function.iterate_succ_apply] using hsame (j+1) (by omega)
    have hbd (s : ℝ) (hs : s ∈ Set.Ico 0 t) :
        ‖g s‖ ≤ 2*‖(bracketStep b)^[p] (bracketStep b x)‖*t^p :=
      (ih _ htail s hs.1).trans (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ hs.1 hs.2.le _) (by positivity))
    have hh := norm_image_sub_le_of_norm_deriv_le_segment'
      (fun s _ => (hd s).hasDerivWithinAt) hbd t ⟨ht,le_rfl⟩
    simpa [f,conjugateFlow,Function.iterate_succ_apply,pow_succ,mul_assoc] using hh

private theorem exp_cancel (a : A) (s : ℝ) : exp (s • a)*exp (s • (-a))=1 := by
  rw [smul_neg,← exp_add_of_commute (Commute.refl (s • a)).neg_right]
  simp

/-- Replacing the generator preceding an inserted interaction by a nearby
patch costs at most order p+1 if the first p commutators agree. -/
theorem insertion_error (a b x : A) (ha : a ∈ skewAdjoint A) (hb : b ∈ skewAdjoint A)
    (hx : x ∈ skewAdjoint A) (p : ℕ)
    (hsame : ∀ j < p, bracketStep a ((bracketStep b)^[j] x) =
      bracketStep b ((bracketStep b)^[j] x)) (t : ℝ) (ht : 0 ≤ t) :
    ‖exp (t • a)*exp (t • (-b))*exp (t • (b+x))-exp (t • (a+x))‖ ≤
      2*‖(bracketStep b)^[p] x‖*t^(p+1) := by
  let f (s : ℝ) := exp (s • (-(a+x)))*exp (s • a)*exp (s • (-b))*exp (s • (b+x))
  let g (s : ℝ) := exp (s • (-(a+x)))*(exp (s • a)*exp (s • (-b))*x-x*exp (s • a)*exp (s • (-b)))*exp (s • (b+x))
  have hd (s : ℝ) : HasDerivAt f (g s) s := by
    have h := (((hasDerivAt_exp_smul_const (-(a+x)) s).fun_mul
      (hasDerivAt_exp_smul_const' a s)).fun_mul (hasDerivAt_exp_smul_const (-b) s)).fun_mul
      (hasDerivAt_exp_smul_const' (b+x) s)
    convert h using 1
    dsimp [g]
    noncomm_ring
  have han := (skewAdjoint A).neg_mem ((skewAdjoint A).add_mem ha hx)
  have hbn := (skewAdjoint A).neg_mem hb
  have hcd (s : ℝ) :
      exp (s • a)*(conjugateFlow b x s-conjugateFlow a x s)*exp (s • (-b)) =
        exp (s • a)*exp (s • (-b))*x-x*exp (s • a)*exp (s • (-b)) := by
    simp only [conjugateFlow,mul_sub,sub_mul]
    congr 1
    · simp only [mul_assoc,exp_cancel,mul_one]
    · simp only [← mul_assoc,exp_cancel,one_mul]
  have hbd (s : ℝ) (hs : s ∈ Set.Ico 0 t) :
      ‖g s‖ ≤ 2*‖(bracketStep b)^[p] x‖*t^p := by
    dsimp only [g]
    rw [CStarRing.norm_mul_mem_unitary _ (flow_mem _ ((skewAdjoint A).add_mem hb hx) _),
      CStarRing.norm_mem_unitary_mul _ (flow_mem _ han _),← hcd,
      CStarRing.norm_mul_mem_unitary _ (flow_mem _ hbn _),
      CStarRing.norm_mem_unitary_mul _ (flow_mem _ ha _),norm_sub_rev]
    exact (conjugate_difference a b ha hb p x hsame s hs.1).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hs.1 hs.2.le _) (by positivity))
  have he := norm_image_sub_le_of_norm_deriv_le_segment'
    (fun s _ => (hd s).hasDerivWithinAt) hbd t ⟨ht,le_rfl⟩
  have hn := CStarRing.norm_mem_unitary_mul (f t-1) (flow_mem _ ((skewAdjoint A).add_mem ha hx) t)
  have heq : exp (t • (a+x))*(f t-1) =
      exp (t • a)*exp (t • (-b))*exp (t • (b+x))-exp (t • (a+x)) := by
    simp only [f,mul_sub,mul_one,← mul_assoc,exp_cancel,one_mul]
  rw [heq] at hn
  rw [hn]
  simpa [f,pow_succ,mul_assoc] using he

#print axioms insertion_error
end
end GaloisForLFunctions.HTGeometry.LocalPatches
