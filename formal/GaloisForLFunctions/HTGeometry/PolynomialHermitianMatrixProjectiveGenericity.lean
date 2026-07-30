import GaloisForLFunctions.HTGeometry.ComplexSpectralCoefficientPolynomialGenericity
import GaloisForLFunctions.HTGeometry.HermitianLocalExtensionRelationEscape
import Mathlib.RingTheory.Polynomial.Vieta

/-!
# Projective spectral genericity for polynomial Hermitian matrix families

Characteristic coefficients are polynomial in matrix entries.  A single
real parameter value with a simple maximally projective real root packet
therefore certifies that every balanced integer spectral-relation
obstruction is a nonzero parameter polynomial.  The simultaneous
exceptional set is meagre and Lebesgue null.
-/

open Set Topology MeasureTheory

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Signed characteristic coefficient equal to the corresponding
elementary symmetric function of a full root packet. -/
def matrixCharacteristicElementaryPolynomial
    {θ I : Type*} [Fintype I] [DecidableEq I]
    (M : Matrix I I (MvPolynomial θ ℂ))
    (j : Fin (Fintype.card I)) :
    MvPolynomial θ ℂ :=
  (-1) ^ (j.1 + 1) *
    M.charpoly.coeff
      (Fintype.card I - (j.1 + 1))

/-- Evaluating matrix parameters commutes with extracting signed
characteristic coefficients. -/
theorem eval_matrixCharacteristicElementaryPolynomial
    {θ I : Type*} [Fintype I] [DecidableEq I]
    (M : Matrix I I (MvPolynomial θ ℂ))
    (p : θ → ℝ)
    (j : Fin (Fintype.card I)) :
    MvPolynomial.eval₂ (RingHom.id ℂ)
        (fun t => (p t : ℂ))
        (matrixCharacteristicElementaryPolynomial M j) =
      (-1 : ℂ) ^ (j.1 + 1) *
        (M.map
          (MvPolynomial.eval₂Hom (RingHom.id ℂ)
            (fun t => (p t : ℂ)))).charpoly.coeff
          (Fintype.card I - (j.1 + 1)) := by
  let f :=
    MvPolynomial.eval₂Hom (RingHom.id ℂ)
      (fun t => (p t : ℂ))
  have hcharpoly :
      (M.map f).charpoly =
        Polynomial.map f M.charpoly :=
    Matrix.charpoly_map M f
  unfold matrixCharacteristicElementaryPolynomial
  change
    f
        ((-1) ^ (j.1 + 1) *
          M.charpoly.coeff
            (Fintype.card I - (j.1 + 1))) =
      _
  rw [map_mul, map_pow, map_neg, map_one]
  rw [hcharpoly]
  simp

/-- A simple real root packet exhausts the roots of a complex matrix
characteristic polynomial, so its signed coefficients are exactly the
elementary symmetric functions of that packet. -/
theorem
    matrixCharacteristicElementaryCoefficient_eq_rootPacket
    {I : Type*} [Fintype I] [DecidableEq I]
    (H : Matrix I I ℂ)
    (energy : I → ℝ)
    (hinjective : Function.Injective energy)
    (hroot :
      ∀ i,
        matrixCharpolyRelation
          (H, (energy i : ℂ)) = 0)
    (j : Fin (Fintype.card I)) :
    (-1 : ℂ) ^ (j.1 + 1) *
        H.charpoly.coeff
          (Fintype.card I - (j.1 + 1)) =
      MvPolynomial.eval₂ (Rat.castHom ℂ)
        (fun i => (energy i : ℂ))
        (MvPolynomial.esymm I ℚ (j.1 + 1)) := by
  let energyC : I → ℂ :=
    fun i => (energy i : ℂ)
  have hinjectiveC : Function.Injective energyC := by
    intro i k hik
    exact hinjective (Complex.ofReal_injective hik)
  let rootsPacket : Multiset ℂ :=
    Finset.univ.val.map energyC
  have hpacketNodup : rootsPacket.Nodup := by
    exact Finset.univ.nodup.map hinjectiveC
  have hcharpolyNe : H.charpoly ≠ 0 :=
    H.charpoly_monic.ne_zero
  have hpacketLe : rootsPacket ≤ H.charpoly.roots := by
    rw [Multiset.le_iff_subset hpacketNodup]
    intro z hz
    simp only [rootsPacket, Multiset.mem_map] at hz
    obtain ⟨i, hi, rfl⟩ := hz
    rw [Polynomial.mem_roots hcharpolyNe]
    change H.charpoly.eval (energyC i) = 0
    rw [Matrix.eval_charpoly]
    exact hroot i
  have hrootsCard :
      H.charpoly.roots.card = Fintype.card I := by
    rw [Polynomial.splits_iff_card_roots.mp
      (IsAlgClosed.splits H.charpoly)]
    exact H.charpoly_natDegree_eq_dim
  have hpacketCard :
      rootsPacket.card = Fintype.card I := by
    simp [rootsPacket]
  have hpacketEq :
      rootsPacket = H.charpoly.roots := by
    apply Multiset.eq_of_le_of_card_le hpacketLe
    rw [hrootsCard, hpacketCard]
  have hcoefficientIndex :
      Fintype.card I - (j.1 + 1) ≤
        H.charpoly.natDegree := by
    rw [H.charpoly_natDegree_eq_dim]
    omega
  have hvieta :=
    Polynomial.coeff_eq_esymm_roots_of_splits
      (IsAlgClosed.splits H.charpoly)
      (k := Fintype.card I - (j.1 + 1))
      hcoefficientIndex
  rw [H.charpoly_natDegree_eq_dim] at hvieta
  have hdegreeDifference :
      Fintype.card I -
          (Fintype.card I - (j.1 + 1)) =
        j.1 + 1 := by
    omega
  have hesymm :
      H.charpoly.coeff
          (Fintype.card I - (j.1 + 1)) =
        (-1 : ℂ) ^ (j.1 + 1) *
          rootsPacket.esymm (j.1 + 1) := by
    rw [hpacketEq]
    simpa [H.charpoly_monic.leadingCoeff,
      hdegreeDifference] using hvieta
  rw [hesymm]
  have hsign :
      (-1 : ℂ) ^ (j.1 + 1) *
          ((-1 : ℂ) ^ (j.1 + 1) *
            rootsPacket.esymm (j.1 + 1)) =
        rootsPacket.esymm (j.1 + 1) := by
    rw [← mul_assoc, ← pow_add]
    simp [show (j.1 + 1) + (j.1 + 1) =
        2 * (j.1 + 1) by omega,
      pow_mul]
  rw [hsign]
  change
    (Finset.univ.val.map energyC).esymm
        (j.1 + 1) = _
  rw [←
    MvPolynomial.aeval_esymm_eq_multiset_esymm
      I ℚ (j.1 + 1) energyC]
  simp only [MvPolynomial.aeval_def]
  rfl

/-- Parameter set where every nonzero balanced unordered relation
obstruction of a polynomial matrix family survives. -/
def polynomialMatrixProjectiveGenericSet
    {m : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (M : Matrix I I (MvPolynomial (Fin m) ℂ)) :
    Set (Fin m → ℝ) :=
  complexSpectralCoefficientProjectiveGenericSet
    (matrixCharacteristicElementaryPolynomial M)

/-- **Polynomial Hermitian-family one-witness theorem.** One simple
maximally projective real root packet implies a dense residual
full-measure set of real parameters avoiding every balanced integer
spectral relation. -/
theorem
    polynomialMatrixProjectiveGenericSet_dense_residual_fullMeasure
    {m : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (M : Matrix I I (MvPolynomial (Fin m) ℂ))
    (p₀ : Fin m → ℝ)
    (energy : I → ℝ)
    (hmax : MaximallyProjectiveEnergy energy)
    (hinjective : Function.Injective energy)
    (hroot :
      ∀ i,
        matrixCharpolyRelation
          (M.map
              (MvPolynomial.eval₂Hom (RingHom.id ℂ)
                (fun t => (p₀ t : ℂ))),
            (energy i : ℂ)) = 0) :
    Dense (polynomialMatrixProjectiveGenericSet M) ∧
      polynomialMatrixProjectiveGenericSet M ∈
        residual (Fin m → ℝ) ∧
      volume
        (polynomialMatrixProjectiveGenericSet M)ᶜ = 0 := by
  unfold polynomialMatrixProjectiveGenericSet
  apply
    complexSpectralCoefficientProjectiveGenericSet_dense_residual_fullMeasure
      (matrixCharacteristicElementaryPolynomial M)
      p₀ energy hmax
  intro j
  rw [eval_matrixCharacteristicElementaryPolynomial]
  exact
    matrixCharacteristicElementaryCoefficient_eq_rootPacket
      _ energy hinjective hroot j

end

end GaloisForLFunctions.HTGeometry
