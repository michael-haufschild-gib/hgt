import Mathlib.NumberTheory.JacobiSum.Basic
import GaloisForLFunctions.ExponentDynamicsOfTheCriticalStrip.TheShortMoebiusMonomialsPayExactlyHalf

/-!
# The calibration curves are pure by their pairing

The Frobenius eigenvalues of the Kummer and Fermat calibration curves over `𝔽_q` are Jacobi sums
`J(χ, φ) = Σ_x χ(x) φ(1 − x)`, one for each pair of nontrivial characters with `χφ` nontrivial.
Their local systems are abelian (characters of the Galois group of a cyclotomic field), so the
tensor-power argument on them is a ruler (`summable_twistMomentTerm_iff`). Their purity has a
different source: the two pairings of an eigenvalue coincide by an identity.

* **Conjugation pair** (`conj_jacobiSum`): `conj J(χ, φ) = J(χ⁻¹, φ⁻¹)`.
* **Polarization pair** (`jacobiSum_mul_jacobiSum_inv_eq_card`): `J(χ, φ) J(χ⁻¹, φ⁻¹) = q`.
* **Purity** (`norm_jacobiSum_sq`): `‖J(χ, φ)‖² = q`, because the conjugation pair is the
  polarization pair.
* **The same eigenvalues sit on the sign line** (`stickelbergerPrice_jacobiTriple`). Over `ℚ̄_p`
  the Gauss monomial `g(χ) g(φ) g((χφ)⁻¹) = ±p J(χ, φ)` is a Möbius-signed monomial of length
  three, priced exactly `k/2` at every period `k`: half a unit above the Deligne line.

So on the calibration curves monodromy is not needed: purity is an identity between the two
pairings, and the half unit of the sign line is a `p`-adic defect carried by eigenvalues that are
archimedean-pure. Over `Spec ℤ` the corresponding identity for the zeros, `ρ̄ = 1 − ρ`, is RH.
-/

open ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.TensorPowerProgramme

variable {F : Type*} [Field F] [Fintype F]

/-- **The conjugation pair** of a Jacobi sum: `conj J(χ, φ) = J(χ⁻¹, φ⁻¹)`. -/
theorem conj_jacobiSum (χ φ : MulChar F ℂ) : conj (jacobiSum χ φ) = jacobiSum χ⁻¹ φ⁻¹ := by
  simp only [jacobiSum, map_sum, map_mul, starRingEnd_apply, MulChar.star_apply']

/-- **The polarization pair** of a Jacobi sum: `J(χ, φ) J(χ⁻¹, φ⁻¹) = q`. -/
theorem jacobiSum_mul_jacobiSum_inv_eq_card {χ φ : MulChar F ℂ} (hχ : χ ≠ 1) (hφ : φ ≠ 1)
    (hχφ : χ * φ ≠ 1) : jacobiSum χ φ * jacobiSum χ⁻¹ φ⁻¹ = Fintype.card F := by
  have h : ringChar ℂ ≠ ringChar F := by
    rw [ringChar.eq_zero]
    exact (CharP.ringChar_ne_zero_of_finite F).symm
  exact jacobiSum_mul_jacobiSum_inv h hχ hφ hχφ

/-- **The calibration eigenvalues are pure**: `‖J(χ, φ)‖² = q`. -/
theorem norm_jacobiSum_sq {χ φ : MulChar F ℂ} (hχ : χ ≠ 1) (hφ : φ ≠ 1) (hχφ : χ * φ ≠ 1) :
    ‖jacobiSum χ φ‖ ^ 2 = Fintype.card F := by
  have h := jacobiSum_mul_jacobiSum_inv_eq_card hχ hφ hχφ
  rw [← conj_jacobiSum, Complex.mul_conj, Complex.normSq_eq_norm_sq] at h
  exact_mod_cast h

open ExponentDynamicsOfTheCriticalStrip FamilyContinuationTheory in
/-- **The calibration eigenvalues sit on the sign line.** The Gauss monomial
`g(χ) g(φ) g((χφ)⁻¹)` of a Jacobi sum over `ZMod p` has Stickelberger price exactly `k/2`. -/
theorem stickelbergerPrice_jacobiTriple {p : ℕ} [Fact p.Prime] {ζ : PadicAlgCl p}
    (hζ : IsPrimitiveRoot ζ p) (k : ℝ) {χ φ : MulChar (ZMod p) (PadicAlgCl p)}
    (h₁ : 2 ≤ orderOf χ) (h₂ : 2 ≤ orderOf φ) (h₃ : 2 ≤ orderOf (χ * φ)) :
    Stickelberger.stickelbergerPrice hζ k [χ, φ, (χ * φ)⁻¹] = k / 2 := by
  have hprod : [χ, φ, (χ * φ)⁻¹].prod = 1 := by
    simp only [List.prod_cons, List.prod_nil, mul_one]
    rw [← mul_assoc, mul_inv_cancel]
  refine Stickelberger.stickelbergerPrice_eq_half_mul hζ k ⟨by simp, ?_, ?_, ?_⟩ (by simp)
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · exact h₁
    · exact h₂
    · rwa [orderOf_inv]
  · rw [hprod, one_pow]
  · exact Or.inl ⟨hprod, ⟨1, rfl⟩⟩

end GaloisForLFunctions.TensorPowerProgramme
