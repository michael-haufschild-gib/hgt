import GaloisForLFunctions.HTGeometry.DifferenceDifferential
import GaloisForLFunctions.HTGeometry.JetHorizonFirstDepthRigidity

/-!
# The gauge of a derivative horizon does not depend on its depth

A differential field whose derivation has no primitive of one has no element killed by a power of
the derivation other than its constants: a tower of primitives collapses one floor at a time.  So in
such a field the displacement produced by a horizon of *any* positive depth is already a constant,
and the depth-one analysis applies verbatim.

The conclusion is the depth-independent reconstruction criterion: for a translation-rigid affine
locus, every derivation commuting with the derivation of the field and killing the `n`-th
derivatives of the coordinates kills the coordinates themselves, and every differential
endomorphism fixing the `n`-th derivatives fixes the coordinates.  The gauge freedom of a
finite-depth horizon is exactly the constant translation stabilizer of the locus, whatever the
depth.
-/

open scoped Differential

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

variable {F : Type*} [Field F] [Differential F]

/-! ### Fields without a primitive of one -/

/-- The inverse of a constant is a constant. -/
theorem deriv_inv_eq_zero {c : F} (hc : c′ = 0) : (c⁻¹)′ = 0 := by
  rcases eq_or_ne c 0 with rfl | hc0
  · simp
  · have h1 : (c * c⁻¹)′ = 0 := by rw [mul_inv_cancel₀ hc0]; exact Derivation.map_one_eq_zero _
    rw [Derivation.leibniz] at h1
    simp only [smul_eq_mul, hc, mul_zero, add_zero] at h1
    exact (mul_eq_zero.mp h1).resolve_left hc0

/-- **One floor of the collapse.**  If the derivation has no primitive of one, an element whose
second derivative vanishes already has vanishing first derivative. -/
theorem deriv_eq_zero_of_deriv_deriv_eq_zero (hprim : ∀ x : F, x′ ≠ 1)
    {x : F} (h : (x′)′ = 0) : x′ = 0 := by
  by_contra hne
  refine hprim (x * (x′)⁻¹) ?_
  rw [Derivation.leibniz]
  simp only [smul_eq_mul, deriv_inv_eq_zero h, mul_zero]
  rw [zero_add]
  exact inv_mul_cancel₀ hne

/-- **The collapse.**  If the derivation has no primitive of one, an element killed by a positive
power of the derivation is a constant. -/
theorem deriv_eq_zero_of_differentialJet_succ_eq_zero (hprim : ∀ x : F, x′ ≠ 1)
    {n : ℕ} {x : F} (h : differentialJet (n + 1) x = 0) : x′ = 0 := by
  induction n generalizing x with
  | zero => simpa [differentialJet_succ] using h
  | succ n ih =>
      have h' : differentialJet (n + 1) x′ = 0 := by
        rw [← differentialJet_succ_apply]
        exact h
      exact deriv_eq_zero_of_deriv_deriv_eq_zero hprim (ih h')

/-- The same statement with the depth written as a positive natural number. -/
theorem deriv_eq_zero_of_differentialJet_eq_zero (hprim : ∀ x : F, x′ ≠ 1)
    {n : ℕ} (hn : 1 ≤ n) {x : F} (h : differentialJet n x = 0) : x′ = 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  exact deriv_eq_zero_of_differentialJet_succ_eq_zero hprim h

/-! ### Depth-independent horizon gauge -/

/-- A derivation commuting with the derivation of the field commutes with all its iterates. -/
theorem derivation_differentialJet {C : Type*} [CommRing C] [Algebra C F]
    (D : Derivation C F F) (hcomm : ∀ x : F, D (x′) = (D x)′) (n : ℕ) (x : F) :
    D (differentialJet n x) = differentialJet n (D x) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [differentialJet_succ, differentialJet_succ, hcomm, ih]

/-- **Depth-independent infinitesimal rigidity.**  In a differential field with no primitive of one
and constants `C`, a derivation commuting with the derivation and killing the `n`-th derivatives of
the coordinates of a translation-rigid point kills the coordinates. -/
theorem derivation_apply_eq_zero_of_translationRigid_depth
    {C ι : Type*} [Field C] [CharZero C] [Finite ι] [Algebra C F]
    (hprim : ∀ x : F, x′ ≠ 1)
    (hconst : ∀ x : F, x′ = 0 → ∃ c : C, algebraMap C F c = x)
    (z : ι → F) (hA : ∀ a : ι → C, IsTranslationSymmetry z a → a = 0)
    (D : Derivation C F F) (hcomm : ∀ x : F, D (x′) = (D x)′)
    {n : ℕ} (hn : 1 ≤ n) (hDz : ∀ i, D (differentialJet n (z i)) = 0) (i : ι) :
    D (z i) = 0 := by
  refine derivation_apply_eq_zero_of_translationRigid hconst z hA D (fun j => ?_) i
  refine deriv_eq_zero_of_differentialJet_eq_zero hprim hn ?_
  rw [← derivation_differentialJet D hcomm n (z j)]
  exact hDz j

/-- **Depth-independent finite rigidity.**  Under the same hypotheses a differential endomorphism
fixing the `n`-th derivatives of the coordinates fixes the coordinates. -/
theorem apply_eq_self_of_translationRigid_depth
    {C ι : Type*} [Field C] [CharZero C] [Finite ι] [Algebra C F]
    (hprim : ∀ x : F, x′ ≠ 1)
    (hconst : ∀ x : F, x′ = 0 → ∃ c : C, algebraMap C F c = x)
    (z : ι → F) (hA : ∀ a : ι → C, IsTranslationSymmetry z a → a = 0)
    (σ : F →ₐ[C] F) (hcomm : ∀ x : F, σ (x′) = (σ x)′)
    {n : ℕ} (hn : 1 ≤ n) (hfix : ∀ i, σ (differentialJet n (z i)) = differentialJet n (z i))
    (i : ι) :
    σ (z i) = z i := by
  classical
  have hjet : ∀ (m : ℕ) (x : F), σ (differentialJet m x) = differentialJet m (σ x) := by
    intro m x
    induction m with
    | zero => rfl
    | succ m ih => rw [differentialJet_succ, differentialJet_succ, hcomm, ih]
  have hker : ∀ j, differentialJet n (σ (z j) - z j) = 0 := by
    intro j
    rw [differentialJet_sub, ← hjet n (z j), hfix j, sub_self]
  have hcst : ∀ j, (σ (z j) - z j)′ = 0 := fun j =>
    deriv_eq_zero_of_differentialJet_eq_zero hprim hn (hker j)
  choose a ha using fun j => hconst _ (hcst j)
  have hsym : IsTranslationSymmetry z a := by
    intro P hP
    have hσ : MvPolynomial.aeval (fun j => σ (z j)) P = σ (MvPolynomial.aeval z P) := by
      have := congrArg (fun f : MvPolynomial ι C →ₐ[C] F => f P)
        (MvPolynomial.algHom_ext (f := σ.comp (MvPolynomial.aeval z))
          (g := MvPolynomial.aeval fun j => σ (z j)) (fun j => by simp))
      simpa using this.symm
    have hzero : MvPolynomial.aeval (fun j => σ (z j)) P = 0 := by
      rw [hσ, hP, map_zero]
    have hpt : (fun j => σ (z j)) = fun j => z j + algebraMap C F (a j) := by
      funext j; rw [ha j]; ring
    rwa [hpt] at hzero
  have hzero : a = 0 := hA a hsym
  have h0 : σ (z i) - z i = 0 := by rw [← ha i, hzero]; simp
  exact sub_eq_zero.mp h0

end

end GaloisForLFunctions.HTGeometry
