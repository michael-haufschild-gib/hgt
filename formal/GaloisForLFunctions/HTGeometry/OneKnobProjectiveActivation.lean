import GaloisForLFunctions.HTGeometry.ComplexAffineLinePolynomialAvoidance
import GaloisForLFunctions.HTGeometry.PolynomialHermitianSpectrumGenericity
import GaloisForLFunctions.HTGeometry.ArbitraryGraphLocalHamiltonianGenericityLaw

/-!
# One coupling knob activates the full projective rank

The obstruction polynomials of a complex characteristic-coefficient family are countably many, and
each is nonzero as soon as one real parameter makes it nonzero.  Restricting a nonzero polynomial to
an affine line gives a nonzero one-variable polynomial for almost every line, so its roots form a
finite set; the union over the countable obstruction family is countable.

Hence for almost every pair of a background and a direction, all but countably many coupling
strengths along the line make every balanced spectral obstruction survive, that is, give a
maximally projective spectrum.
-/

open Filter MeasureTheory Set

namespace GaloisForLFunctions.HTGeometry

noncomputable section

section GenericLine

/-- **Countable exceptional coupling set for complex spectral obstructions.** -/
theorem countable_exceptional_line_complexSpectralCoefficientProjectiveGenericSet
    {m : ℕ} {I : Type*} [Fintype I]
    (coefficient : Fin (Fintype.card I) → MvPolynomial (Fin m) ℂ)
    (hwitness : ∀ k : I → ℤ, SpectralCharacterBalanced k → k ≠ 0 →
      ∃ p : Fin m → ℝ, MvPolynomial.eval₂ (RingHom.id ℂ) (fun t => (p t : ℂ))
        (complexSpectralCoefficientObstructionPullback coefficient k) ≠ 0) :
    ∀ᵐ av : (Fin m → ℝ) × (Fin m → ℝ) ∂(volume.prod volume),
      ∃ C : Set ℝ, C.Countable ∧
        ∀ g ∉ C, (fun i => av.1 i + g * av.2 i) ∈
          complexSpectralCoefficientProjectiveGenericSet coefficient := by
  classical
  let J := {k : I → ℤ // SpectralCharacterBalanced k ∧ k ≠ 0}
  letI : Countable J := by
    dsimp [J]
    infer_instance
  letI : Encodable J := Encodable.ofCountable J
  let P : ℕ → MvPolynomial (Fin m) ℂ := fun n =>
    match (Encodable.decode n : Option J) with
    | none => 1
    | some k => complexSpectralCoefficientObstructionPullback coefficient k.1
  have hPne : ∀ n, P n ≠ 0 := by
    intro n
    unfold P
    split
    · exact one_ne_zero
    · rename_i k _
      obtain ⟨p, hp⟩ := hwitness k.1 k.2.1 k.2.2
      intro hzero
      rw [hzero] at hp
      simp at hp
  filter_upwards [countable_complexMvPolynomialAffineLineAvoidance_ae_pair P hPne] with av hav
  obtain ⟨C, hC, hgC⟩ := hav
  refine ⟨C, hC, fun g hg => ?_⟩
  intro k hbalanced hk
  have hj := hgC g hg (Encodable.encode (⟨k, hbalanced, hk⟩ : J))
  simpa [P, Encodable.encodek] using hj

/-- **Countable exceptional coupling set for a polynomial Hermitian family.** -/
theorem countable_exceptional_line_polynomialMatrixProjectiveGenericSet
    {m : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (M : Matrix I I (MvPolynomial (Fin m) ℂ))
    (p₀ : Fin m → ℝ) (energy : I → ℝ)
    (hmax : MaximallyProjectiveEnergy energy) (hinjective : Function.Injective energy)
    (hroot : ∀ i, matrixCharpolyRelation
      (M.map (MvPolynomial.eval₂Hom (RingHom.id ℂ) (fun t => (p₀ t : ℂ))),
        (energy i : ℂ)) = 0) :
    ∀ᵐ av : (Fin m → ℝ) × (Fin m → ℝ) ∂(volume.prod volume),
      ∃ C : Set ℝ, C.Countable ∧
        ∀ g ∉ C, (fun i => av.1 i + g * av.2 i) ∈
          polynomialMatrixProjectiveGenericSet M := by
  have hcoefficient : ∀ j,
      MvPolynomial.eval₂ (RingHom.id ℂ) (fun t => (p₀ t : ℂ))
          (matrixCharacteristicElementaryPolynomial M j) =
        MvPolynomial.eval₂ (Rat.castHom ℂ) (fun a => (energy a : ℂ))
          (MvPolynomial.esymm I ℚ (j.1 + 1)) := by
    intro j
    rw [eval_matrixCharacteristicElementaryPolynomial]
    exact matrixCharacteristicElementaryCoefficient_eq_rootPacket
      _ (fun i => ((energy i : ℝ) : ℂ))
      (fun a b h => hinjective (Complex.ofReal_injective h)) hroot j
  exact countable_exceptional_line_complexSpectralCoefficientProjectiveGenericSet
    (matrixCharacteristicElementaryPolynomial M)
    fun k hbalanced hk => ⟨p₀,
      complexSpectralCoefficientObstructionPullback_has_real_witness
        (matrixCharacteristicElementaryPolynomial M) p₀ energy hmax hcoefficient k hbalanced hk⟩

/-- **Countable exceptional coupling set for the maximal-rank locus of a polynomial Hermitian
family.** -/
theorem countable_exceptional_line_polynomialHermitianMatrixMaximalSet
    {m : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (M : Matrix I I (MvPolynomial (Fin m) ℂ))
    (hhermitian : ∀ p : Fin m → ℝ,
      (M.map (MvPolynomial.eval₂Hom (RingHom.id ℂ) (fun t => (p t : ℂ)))).IsHermitian)
    (p₀ : Fin m → ℝ)
    (hmax : MaximallyProjectiveEnergy (hhermitian p₀).eigenvalues) :
    ∀ᵐ av : (Fin m → ℝ) × (Fin m → ℝ) ∂(volume.prod volume),
      ∃ C : Set ℝ, C.Countable ∧
        ∀ g ∉ C, (fun i => av.1 i + g * av.2 i) ∈
          polynomialHermitianMatrixMaximalSet M hhermitian := by
  have hline := countable_exceptional_line_polynomialMatrixProjectiveGenericSet M p₀
    (hhermitian p₀).eigenvalues hmax hmax.injective
    (hermitianEigenvalue_matrixCharpolyRelation _ (hhermitian p₀))
  filter_upwards [hline] with av hav
  obtain ⟨C, hC, hgC⟩ := hav
  refine ⟨C, hC, fun g hg => ?_⟩
  exact maximallyProjectiveEnergy_eigenvalues_of_mem_polynomialMatrixGenericSet
    M _ (hgC g hg) (hhermitian _)

/-- **One-knob activation for a real-affine Hermitian family.**  For almost every background and
direction, all but countably many coupling strengths give a maximally projective spectrum. -/
theorem countable_exceptional_line_realAffineHermitianMaximalSet
    {m : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (base : Matrix I I ℂ) (generator : Fin m → Matrix I I ℂ)
    (hbase : base.IsHermitian) (hgenerator : ∀ t, (generator t).IsHermitian)
    (p₀ : Fin m → ℝ)
    (hmax : MaximallyProjectiveEnergy
      (realAffineMatrix_isHermitian base generator hbase hgenerator p₀).eigenvalues) :
    ∀ᵐ av : (Fin m → ℝ) × (Fin m → ℝ) ∂(volume.prod volume),
      ∃ C : Set ℝ, C.Countable ∧
        ∀ g ∉ C, (fun i => av.1 i + g * av.2 i) ∈
          realAffineHermitianMaximalSet base generator hbase hgenerator := by
  have hherm : ∀ p : Fin m → ℝ,
      (((realAffineMatrixPolynomial base generator)).map
        (MvPolynomial.eval₂Hom (RingHom.id ℂ) (fun t => (p t : ℂ)))).IsHermitian := by
    intro p
    rw [eval_realAffineMatrixPolynomial]
    exact realAffineMatrix_isHermitian base generator hbase hgenerator p
  have hmax₀ : MaximallyProjectiveEnergy (hherm p₀).eigenvalues := by
    have heig : (hherm p₀).eigenvalues =
        (realAffineMatrix_isHermitian base generator hbase hgenerator p₀).eigenvalues := by
      apply (Matrix.IsHermitian.eigenvalues_eq_eigenvalues_iff (hherm p₀)
        (realAffineMatrix_isHermitian base generator hbase hgenerator p₀)).2
      rw [eval_realAffineMatrixPolynomial]
    rw [heig]
    exact hmax
  exact countable_exceptional_line_polynomialHermitianMatrixMaximalSet
    (realAffineMatrixPolynomial base generator) hherm p₀ hmax₀

end GenericLine

end

end GaloisForLFunctions.HTGeometry
