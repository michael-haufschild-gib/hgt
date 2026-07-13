import GaloisForLFunctions.HTGeometry.ScalarExtendedPolynomialProper
import GaloisForLFunctions.HTGeometry.ScalarExtendedHypersurfaceDimension
import Mathlib.Algebra.Category.CommAlgCat.Basic
import Mathlib.RingTheory.KrullDimension.Field

namespace GaloisForLFunctions.HTGeometry

noncomputable section

def iteratedBlockHypersurfaceRing {σ : Type} :
    List (MvPolynomial σ ℂ) → CommAlgCat ℂ
  | [] => CommAlgCat.of ℂ ℂ
  | P :: Ps =>
      let A := iteratedBlockHypersurfaceRing Ps
      CommAlgCat.of ℂ
        ((MvPolynomial σ A) ⧸
          Ideal.span {MvPolynomial.map (algebraMap ℂ A) P})

/-- Iterated disjoint-block quotient rings remain Noetherian when each block is finite. -/
theorem iteratedBlockHypersurfaceRing_isNoetherian
    {σ : Type} [Finite σ] (Ps : List (MvPolynomial σ ℂ)) :
    IsNoetherianRing (iteratedBlockHypersurfaceRing Ps) := by
  induction Ps with
  | nil =>
      change IsNoetherianRing ℂ
      infer_instance
  | cons P Ps ih =>
      letI : IsNoetherianRing (iteratedBlockHypersurfaceRing Ps) := ih
      change IsNoetherianRing
        ((MvPolynomial σ (iteratedBlockHypersurfaceRing Ps)) ⧸
          Ideal.span {MvPolynomial.map
            (algebraMap ℂ (iteratedBlockHypersurfaceRing Ps)) P})
      infer_instance

/-- Successive quotients by nonconstant row-block equations never collapse to the zero ring. -/
theorem iteratedBlockHypersurfaceRing_nontrivial
    {σ : Type} (Ps : List (MvPolynomial σ ℂ))
    (hPs : ∀ P ∈ Ps, ¬ IsConstantMvPolynomial P) :
    Nontrivial (iteratedBlockHypersurfaceRing Ps) := by
  induction Ps with
  | nil =>
      change Nontrivial ℂ
      infer_instance
  | cons P Ps ih =>
      have hP : ¬ IsConstantMvPolynomial P := hPs P (by simp)
      have htail : ∀ Q ∈ Ps, ¬ IsConstantMvPolynomial Q := by
        intro Q hQ
        exact hPs Q (by simp [hQ])
      letI : Nontrivial (iteratedBlockHypersurfaceRing Ps) := ih htail
      change Nontrivial
        ((MvPolynomial σ (iteratedBlockHypersurfaceRing Ps)) ⧸
          Ideal.span {MvPolynomial.map
            (algebraMap ℂ (iteratedBlockHypersurfaceRing Ps)) P})
      exact scalarExtendedPolynomial_quotient_nontrivial_of_not_constant P hP

/-- **Iterated disjoint-block dimension drop.** Quotienting successively by `r` nonconstant
complex equations, each in a fresh finite variable block, lowers Krull dimension by at least
`r` relative to the sum of the block dimensions. -/
theorem iteratedBlockHypersurfaceRing_krullDim_add_length_le
    {σ : Type} [Finite σ] [LinearOrder σ] [WellFoundedGT σ]
    (Ps : List (MvPolynomial σ ℂ))
    (hPs : ∀ P ∈ Ps, ¬ IsConstantMvPolynomial P) :
    ringKrullDim (iteratedBlockHypersurfaceRing Ps) + Ps.length ≤
      Ps.length * Nat.card σ := by
  induction Ps with
  | nil =>
      simp only [List.length_nil, Nat.cast_zero, add_zero, zero_mul]
      exact le_of_eq (ringKrullDim_eq_zero_of_field ℂ)
  | cons P Ps ih =>
      have hP : ¬ IsConstantMvPolynomial P := hPs P (by simp)
      have htail : ∀ Q ∈ Ps, ¬ IsConstantMvPolynomial Q := by
        intro Q hQ
        exact hPs Q (by simp [hQ])
      letI : Nontrivial (iteratedBlockHypersurfaceRing Ps) :=
        iteratedBlockHypersurfaceRing_nontrivial Ps htail
      letI : IsNoetherianRing (iteratedBlockHypersurfaceRing Ps) :=
        iteratedBlockHypersurfaceRing_isNoetherian Ps
      have hP0 : P ≠ 0 := by
        intro hzero
        exact hP ⟨0, by simp [hzero]⟩
      have hstep := scalarExtendedHypersurface_krullDim_add_one_le
        (k := ℂ) (A := iteratedBlockHypersurfaceRing Ps) (σ := σ) P
        hP0
      have htaildim := ih htail
      change ringKrullDim
          ((MvPolynomial σ (iteratedBlockHypersurfaceRing Ps)) ⧸
            Ideal.span {MvPolynomial.map
              (algebraMap ℂ (iteratedBlockHypersurfaceRing Ps)) P}) +
          (Ps.length + 1) ≤
        (Ps.length + 1) * Nat.card σ
      calc
        _ = (ringKrullDim
              ((MvPolynomial σ (iteratedBlockHypersurfaceRing Ps)) ⧸
                Ideal.span {MvPolynomial.map
                  (algebraMap ℂ (iteratedBlockHypersurfaceRing Ps)) P}) + 1) +
              Ps.length := by
                simp [add_assoc, add_comm]
        _ ≤ (ringKrullDim (iteratedBlockHypersurfaceRing Ps) + Nat.card σ) +
              Ps.length := by
                simpa [add_comm] using add_le_add_right hstep Ps.length
        _ = (ringKrullDim (iteratedBlockHypersurfaceRing Ps) + Ps.length) +
              Nat.card σ := by
                simp [add_comm, add_left_comm]
        _ ≤ Ps.length * Nat.card σ + Nat.card σ := by
              simpa [add_comm] using add_le_add_right htaildim (Nat.card σ)
        _ = (Ps.length + 1) * Nat.card σ := by
              norm_num [add_mul]

end
end GaloisForLFunctions.HTGeometry
