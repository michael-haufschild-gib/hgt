import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.LocalLanglands.PadicCartan
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.LocalLanglands.PrincipalFixedReduction

/-! The determinant of the first principal congruence subgroup is
unchanged by intersecting it with any of its conjugates. A diagonal
element with a prescribed principal-unit determinant commutes with
the Cartan torus. -/

noncomputable section

open Matrix

namespace GlobalTheory.GLp

variable {p n : ℕ} [Fact p.Prime]

private def singleDiagonal {R : Type*} [CommRing R] (i : Fin n) (u : Rˣ) : GL (Fin n) R :=
  ⟨diagonal (fun j => if j = i then (u : R) else 1),
    diagonal (fun j => if j = i then (u⁻¹ : Rˣ).val else 1),
    by
      rw [diagonal_mul_diagonal, ← diagonal_one]
      congr 1
      funext j
      by_cases h : j = i <;> simp [h],
    by
      rw [diagonal_mul_diagonal, ← diagonal_one]
      congr 1
      funext j
      by_cases h : j = i <;> simp [h]⟩

@[simp] private theorem det_singleDiagonal {R : Type*} [CommRing R] (i : Fin n) (u : Rˣ) :
    GeneralLinearGroup.det (singleDiagonal i u) = u := by
  apply Units.ext
  change (diagonal (fun j : Fin n => if j = i then (u : R) else 1)).det = u.val
  rw [det_diagonal, Finset.prod_eq_single i]
  · simp
  · intro j _ hji
    rw [if_neg hji]
  · simp

private theorem integral_singleDiagonal_mem_principal (i : Fin n) (u : ℤ_[p]ˣ)
    (hu : Units.map (PadicInt.toZMod (p := p)).toMonoidHom u = 1) :
    integralInclusion p (Fin n) (singleDiagonal i u) ∈ principalCongruenceOne p (Fin n) := by
  refine ⟨singleDiagonal i u, Units.ext ?_, rfl⟩
  have hu' : PadicInt.toZMod u.val = 1 := congrArg Units.val hu
  change PadicInt.toZMod.mapMatrix (diagonal fun j : Fin n => if j = i then u.val else 1) = 1
  apply Matrix.ext
  intro j k
  by_cases hjk : j = k
  · subst k
    by_cases hji : j = i <;> simp [Matrix.one_apply, hji, hu']
  · simp [Matrix.one_apply, hjk]

private theorem integral_singleDiagonal_commutes (i : Fin n) (u : ℤ_[p]ˣ) (a : Fin n → ℤ) :
    Commute (integralInclusion p (Fin n) (singleDiagonal i u)) (uniformizerTorus (p := p) a) := by
  apply Units.ext
  change (algebraMap ℤ_[p] ℚ_[p]).mapMatrix (diagonal _) * diagonal (fun j => (p : ℚ_[p]) ^ a j) =
    diagonal (fun j => (p : ℚ_[p]) ^ a j) * (algebraMap ℤ_[p] ℚ_[p]).mapMatrix (diagonal _)
  rw [RingHom.mapMatrix_apply, Matrix.diagonal_map (map_zero (algebraMap ℤ_[p] ℚ_[p])),
    diagonal_mul_diagonal, diagonal_mul_diagonal]
  congr 1
  funext j
  exact mul_comm _ _

theorem determinant_of_mem_principal {x : GL (Fin n) ℚ_[p]}
    (hx : x ∈ principalCongruenceOne p (Fin n)) :
    ∃ u : ℤ_[p]ˣ, Units.map (PadicInt.toZMod (p := p)).toMonoidHom u = 1 ∧
      GeneralLinearGroup.det x = Units.map (algebraMap ℤ_[p] ℚ_[p]).toMonoidHom u := by
  obtain ⟨y, hy, rfl⟩ := hx
  change integralReduction p (Fin n) y = 1 at hy
  refine ⟨GeneralLinearGroup.det y, ?_, GeneralLinearGroup.map_det _ _⟩
  have hs : GeneralLinearGroup.det (integralReduction p (Fin n) y) =
      Units.map (PadicInt.toZMod (p := p)).toMonoidHom (GeneralLinearGroup.det y) :=
    GeneralLinearGroup.map_det _ _
  rw [hy, map_one] at hs
  exact hs.symm

theorem exists_principal_conjugate_of_determinant (i : Fin n) (g : GL (Fin n) ℚ_[p])
    (u : ℤ_[p]ˣ) (hu : Units.map (PadicInt.toZMod (p := p)).toMonoidHom u = 1) :
    ∃ x ∈ principalCongruenceOne p (Fin n),
      g⁻¹ * x * g ∈ principalCongruenceOne p (Fin n) ∧
      GeneralLinearGroup.det x = Units.map (algebraMap ℤ_[p] ℚ_[p]).toMonoidHom u := by
  obtain ⟨a, k, l, -, rfl⟩ := exists_integral_cartan g
  let s := integralInclusion p (Fin n) (singleDiagonal i u)
  let b := integralInclusion p (Fin n) k
  let c := integralInclusion p (Fin n) l
  let t := uniformizerTorus (p := p) a
  have hs : s ∈ principalCongruenceOne p (Fin n) := integral_singleDiagonal_mem_principal i u hu
  refine ⟨b * s * b⁻¹, ?_, ?_, ?_⟩
  · simpa only [map_inv, inv_inv] using (integral_conj_mem_principal k⁻¹ hs)
  · change (b * t * c)⁻¹ * (b * s * b⁻¹) * (b * t * c) ∈ principalCongruenceOne p (Fin n)
    have hts : t⁻¹ * s * t = s := by
      rw [mul_assoc, (integral_singleDiagonal_commutes i u a).eq, ← mul_assoc, inv_mul_cancel, one_mul]
    rw [show (b * t * c)⁻¹ * (b * s * b⁻¹) * (b * t * c) = c⁻¹ * (t⁻¹ * s * t) * c by group, hts]
    exact integral_conj_mem_principal l hs
  · change GeneralLinearGroup.det (b * s * b⁻¹) = _
    rw [map_mul, map_mul, map_inv, mul_comm (GeneralLinearGroup.det b), mul_assoc, mul_inv_cancel, mul_one]
    exact (GeneralLinearGroup.map_det _ _).trans (congrArg _ (det_singleDiagonal i u))

end GlobalTheory.GLp

#print axioms GlobalTheory.GLp.determinant_of_mem_principal
#print axioms GlobalTheory.GLp.exists_principal_conjugate_of_determinant
