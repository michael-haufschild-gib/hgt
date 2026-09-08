import GaloisForLFunctions.HTGeometry.AsymmetricDifferenceTensor

/-!
# Exact obstruction to conjugating only one complex tensor factor

The balancing argument in Gomes, arXiv:2509.25276v7, Section 4.2 and Appendix B,
requires simultaneous conjugation of all factors. The corpus already constructs
compatible semilinear tensor automorphisms. The complementary obstruction is
sharp: a conjugate-linear scalar factor paired with a complex-linear matter
map descends to the complex tensor product exactly when the matter map is zero.
The candidate descent is allowed to be an arbitrary function, so weakening its
linearity cannot repair the obstruction.
-/

open scoped TensorProduct ComplexConjugate
noncomputable section
namespace GaloisForLFunctions.HTGeometry

variable {M N : Type*} [AddCommGroup M] [Module ℂ M]
  [AddCommGroup N] [Module ℂ N]

/-- Mixed conjugation descends through complex balancing exactly in the zero case. -/
theorem mixedConjugation_descent_iff (f : M →ₗ[ℂ] N) :
    (∃ F : (ℂ ⊗[ℂ] M) → N,
      ∀ (z : ℂ) (m : M), F (z ⊗ₜ[ℂ] m) = conj z • f m) ↔ f = 0 := by
  constructor
  · rintro ⟨F, hF⟩
    apply LinearMap.ext
    intro m
    have hb := congrArg F (TensorProduct.smul_tmul (R := ℂ) Complex.I (1 : ℂ) m)
    simp only [smul_eq_mul, mul_one, hF, map_smul, Complex.conj_I, map_one, one_smul] at hb
    have hh : f m = -(f m) := by
      have hi := congrArg (fun x : N => Complex.I • x) hb
      simpa only [smul_smul, mul_neg, Complex.I_mul_I, neg_neg, one_smul,
        neg_one_smul] using hi
    have hz : (2 : ℂ) • f m = 0 := by
      rw [two_smul]
      exact (congrArg (fun x : N => x + f m) hh).trans (neg_add_cancel _)
    exact (smul_eq_zero.mp hz).resolve_left two_ne_zero
  · rintro rfl
    exact ⟨fun _ => 0, by intros; simp⟩

/-- Conjugating one scalar factor cannot induce a map on a nonzero complex line. -/
theorem no_partial_scalar_conjugation :
    ¬ ∃ F : (ℂ ⊗[ℂ] ℂ) → ℂ,
      ∀ z w : ℂ, F (z ⊗ₜ[ℂ] w) = conj z * w := by
  intro h
  have hz : (LinearMap.id : ℂ →ₗ[ℂ] ℂ) = 0 :=
    (mixedConjugation_descent_iff LinearMap.id).mp h
  have h1 : (1 : ℂ) = 0 := LinearMap.congr_fun hz 1
  exact one_ne_zero h1

/-- Conjugating both scalar factors gives a genuine automorphism of the tensor algebra. -/
def simultaneousScalarConjugation : (ℂ ⊗[ℂ] ℂ) ≃+* (ℂ ⊗[ℂ] ℂ) :=
  asymmetricDifferenceTensorEquiv Complex.conjAe.toRingEquiv
    Complex.conjAe.toRingEquiv Complex.conjAe.toRingEquiv
    (fun _ => rfl) (fun _ => rfl)

/-- The repaired map conjugates both factors, not one. -/
theorem simultaneousScalarConjugation_tmul (z w : ℂ) :
    simultaneousScalarConjugation (z ⊗ₜ[ℂ] w) = conj z ⊗ₜ[ℂ] conj w := rfl

/-- After multiplying scalar tensor factors, the repair is ordinary conjugation. -/
theorem simultaneousScalarConjugation_multiply (x : ℂ ⊗[ℂ] ℂ) :
    Algebra.TensorProduct.lmul' ℂ (simultaneousScalarConjugation x) =
      conj (Algebra.TensorProduct.lmul' ℂ x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | tmul z w => simp [simultaneousScalarConjugation_tmul]

/-- The simultaneous repair is an involution on all tensors. -/
theorem simultaneousScalarConjugation_involutive :
    Function.Involutive simultaneousScalarConjugation := by
  intro x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | tmul z w => simp [simultaneousScalarConjugation_tmul]

end GaloisForLFunctions.HTGeometry
