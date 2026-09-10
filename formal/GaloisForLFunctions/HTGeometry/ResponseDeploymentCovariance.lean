import GaloisForLFunctions.HTGeometry.FormationCloneRigidityCompletion

/-!
# Broadcast versus independent response errors on existing clone kernels

Araújo, arXiv:2609.05560, Proposition 6 distinguishes common and independent errors.
The corpus already constructs the diagonal broadcast kernel and independent product packet.
Their mean-square response laws are derived here by finite-sum identities. Arbitrary signed
weights are allowed in the homogeneous identities; the uniform specialization is a genuine
probability model with no supplied normalization or independence hypotheses.
-/
open scoped BigOperators
namespace GaloisForLFunctions.HTGeometry
noncomputable section

/-- Centering without division makes the weighted first moment vanish even at zero total mass. -/
def responseCenteredSignal {X : Type*} [Fintype X] (p f : X → ℝ) (x : X) : ℝ :=
  (∑ y, p y) * f x - ∑ y, p y * f y

theorem sum_responseCenteredSignal {X : Type*} [Fintype X] (p f : X → ℝ) :
    ∑ x, p x * responseCenteredSignal p f x = 0 := by
  unfold responseCenteredSignal
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
  have h : (∑ x, p x * ((∑ y, p y) * f x)) = (∑ y, p y) * ∑ x, p x * f x := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    ring
  rw [h]
  ring

/-- Split a finite product sample into its first recipient and the remaining recipients. -/
theorem response_sum_cons {X : Type*} [Fintype X] (d : ℕ)
    (H : (Fin (d + 1) → X) → ℝ) :
    ∑ z, H z = ∑ x, ∑ z : Fin d → X, H (Fin.cons x z) := by
  simpa only [Fintype.sum_prod_type, Fin.consEquiv, Equiv.coe_fn_mk] using
    (Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (d + 1) => X)) H).symm

/-- Product-packet first moments are determined by the two marginal moments and masses. -/
theorem response_product_first_moment {X Y : Type*} [Fintype X] [Fintype Y]
    (p f : X → ℝ) (q g : Y → ℝ) :
    (∑ x, ∑ y, p x * q y * (f x + g y)) =
      (∑ x, p x * f x) * (∑ y, q y) + (∑ x, p x) * ∑ y, q y * g y := by
  have ht (x : X) (y : Y) : p x * q y * (f x + g y) =
      (p x * f x) * q y + p x * (q y * g y) := by ring
  simp_rw [ht, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]

/-- The exact product-packet second-moment decomposition. -/
theorem response_product_second_moment {X Y : Type*} [Fintype X] [Fintype Y]
    (p f : X → ℝ) (q g : Y → ℝ) :
    (∑ x, ∑ y, p x * q y * (f x + g y) ^ 2) =
      (∑ x, p x * f x ^ 2) * (∑ y, q y) +
        2 * (∑ x, p x * f x) * (∑ y, q y * g y) +
          (∑ x, p x) * ∑ y, q y * g y ^ 2 := by
  have ht (x : X) (y : Y) : p x * q y * (f x + g y) ^ 2 =
      (p x * f x ^ 2) * q y + (2 * (p x * f x)) * (q y * g y) +
        p x * (q y * g y ^ 2) := by ring
  simp_rw [ht, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
  rw [← Finset.mul_sum]

/-- Independent centered errors have zero aggregate first moment for every product size. -/
theorem finiteIndependentPower_response_first_zero {X : Type*} [Fintype X]
    (p f : X → ℝ) (d : ℕ) :
    ∑ z, finiteIndependentPower p d z * (∑ j, responseCenteredSignal p f (z j)) = 0 := by
  induction d with
  | zero => simp
  | succ d ih =>
      rw [response_sum_cons]
      simp only [finiteIndependentPower, Fin.prod_univ_succ, Fin.sum_univ_succ,
        Fin.cons_zero, Fin.cons_succ]
      change (∑ x, ∑ z : Fin d → X, p x * finiteIndependentPower p d z *
        (responseCenteredSignal p f x + ∑ j, responseCenteredSignal p f (z j))) = 0
      rw [response_product_first_moment, sum_responseCenteredSignal, ih]
      ring

/-- The independent aggregate second moment has exactly one diagonal contribution per recipient. -/
theorem finiteIndependentPower_response_second {X : Type*} [Fintype X]
    (p f : X → ℝ) (d : ℕ) :
    (∑ z, finiteIndependentPower p d z * (∑ j, responseCenteredSignal p f (z j)) ^ 2) =
      (d : ℝ) * (∑ x, p x) ^ (d - 1) * ∑ x, p x * responseCenteredSignal p f x ^ 2 := by
  induction d with
  | zero => simp
  | succ d ih =>
      rw [response_sum_cons]
      simp only [finiteIndependentPower, Fin.prod_univ_succ, Fin.sum_univ_succ,
        Fin.cons_zero, Fin.cons_succ]
      change (∑ x, ∑ z : Fin d → X, p x * finiteIndependentPower p d z *
        (responseCenteredSignal p f x + ∑ j, responseCenteredSignal p f (z j)) ^ 2) = _
      rw [response_product_second_moment, sum_responseCenteredSignal,
        finiteIndependentPower_sum, ih]
      cases d with
      | zero => simp
      | succ d => simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, pow_succ]; ring

/-- A broadcast packet reads any observable only on constant recipient configurations. -/
theorem finiteDiagonalPower_response_expectation {X : Type*} [Fintype X] [DecidableEq X]
    (p : X → ℝ) (d : ℕ) (H : (Fin d → X) → ℝ) :
    ∑ z, finiteDiagonalPower p d z * H z = ∑ x, p x * H (fun _ => x) := by
  classical
  simp_rw [finiteDiagonalPower_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  simp

/-- Averaging arbitrarily many broadcast recipients does not attenuate the source second moment. -/
theorem finiteDiagonalPower_response_average_second {X : Type*} [Fintype X] [DecidableEq X]
    (p f : X → ℝ) (d : ℕ) :
    (∑ z, finiteDiagonalPower p (d + 1) z *
      ((∑ j, f (z j)) / (d + 1 : ℝ)) ^ 2) = ∑ x, p x * f x ^ 2 := by
  rw [finiteDiagonalPower_response_expectation]
  have hd : (d + 1 : ℝ) ≠ 0 := by positivity
  simp [Finset.sum_const, nsmul_eq_mul, hd]

/-- Uniform finite error weights are normalized by construction. -/
def responseUniformWeight (m : ℕ) : Fin (m + 1) → ℝ := fun _ => (m + 1 : ℝ)⁻¹

theorem sum_responseUniformWeight (m : ℕ) : ∑ x, responseUniformWeight m x = 1 := by
  have hm : (m + 1 : ℝ) ≠ 0 := by positivity
  simp [responseUniformWeight, nsmul_eq_mul, hm]

/-- Independent personalized errors self-average with the exact inverse-recipient factor. -/
theorem finiteIndependentPower_uniform_response_average_second (m d : ℕ)
    (f : Fin (m + 1) → ℝ) :
    (∑ z, finiteIndependentPower (responseUniformWeight m) (d + 1) z *
      ((∑ j, responseCenteredSignal (responseUniformWeight m) f (z j)) /
        (d + 1 : ℝ)) ^ 2) =
      (∑ x, responseUniformWeight m x *
        responseCenteredSignal (responseUniformWeight m) f x ^ 2) / (d + 1 : ℝ) := by
  have hd : (d + 1 : ℝ) ≠ 0 := by positivity
  simp_rw [div_pow, ← mul_div_assoc, ← Finset.sum_div]
  rw [finiteIndependentPower_response_second, sum_responseUniformWeight]
  simp only [one_pow, mul_one, Nat.cast_add, Nat.cast_one]
  field_simp

/-- Identical marginal error laws have different collective variance solely because of deployment. -/
theorem response_deployment_dichotomy (m d : ℕ) (f : Fin (m + 1) → ℝ) :
    (∑ z, finiteDiagonalPower (responseUniformWeight m) (d + 1) z *
      ((∑ j, responseCenteredSignal (responseUniformWeight m) f (z j)) /
        (d + 1 : ℝ)) ^ 2) =
      (d + 1 : ℝ) * ∑ z, finiteIndependentPower (responseUniformWeight m) (d + 1) z *
        ((∑ j, responseCenteredSignal (responseUniformWeight m) f (z j)) /
          (d + 1 : ℝ)) ^ 2 := by
  rw [finiteDiagonalPower_response_average_second,
    finiteIndependentPower_uniform_response_average_second]
  have hd : (d + 1 : ℝ) ≠ 0 := by positivity
  field_simp

end
end GaloisForLFunctions.HTGeometry
