import GaloisForLFunctions.HTGeometry.ProjectiveAffineChartIncidenceDimension
import Mathlib.RingTheory.KrullDimension.Basic

namespace GaloisForLFunctions.HTGeometry

noncomputable section

abbrev projectiveChartInactiveRow
    {row κ : Type} [Fintype κ] [DecidableEq κ]
    (q : ℕ) (z : row → ℂ) (j : κ × Fin (q + 1))
    (p : Ideal (MvPolynomial (projectiveChartVar j) ℂ)) :=
  {b : row // ¬ ∃ a, rowCoefficientPolynomialOf q z (projectiveChartCoefficient j) b a ∉ p}

def projectiveChartInactiveBlockPolynomial
    {row κ : Type} [Fintype row] [Fintype κ] [DecidableEq κ]
    (q n : ℕ) (z : row → ℂ) (j : κ × Fin (q + 1))
    (exponent : κ → (Fin n →₀ ℕ))
    (p : Ideal (MvPolynomial (projectiveChartVar j) ℂ)) [p.IsPrime]
    (b : projectiveChartInactiveRow q z j p) :
    MvPolynomial (projectiveChartInactiveRow q z j p × Fin n)
      (projectiveChartActiveBlockRing q n z j exponent p) :=
  MvPolynomial.rename (Prod.mk b)
    (MvPolynomial.map
      (algebraMap (Localization.AtPrime p)
        (projectiveChartActiveBlockRing q n z j exponent p))
      (localizedCoefficientRowPolynomial q n z (projectiveChartCoefficient j) exponent p b.1))

abbrev projectiveChartFullIncidenceAmbient
    {row κ : Type} [Fintype row] [Fintype κ] [DecidableEq κ]
    (q n : ℕ) (z : row → ℂ) (j : κ × Fin (q + 1))
    (exponent : κ → (Fin n →₀ ℕ))
    (p : Ideal (MvPolynomial (projectiveChartVar j) ℂ)) [p.IsPrime] :=
  MvPolynomial (projectiveChartInactiveRow q z j p × Fin n)
    (projectiveChartActiveBlockRing q n z j exponent p)

def projectiveChartFullIncidenceIdeal
    {row κ : Type} [Fintype row] [Fintype κ] [DecidableEq κ]
    (q n : ℕ) (z : row → ℂ) (j : κ × Fin (q + 1))
    (exponent : κ → (Fin n →₀ ℕ))
    (p : Ideal (MvPolynomial (projectiveChartVar j) ℂ)) [p.IsPrime] :
    Ideal (projectiveChartFullIncidenceAmbient q n z j exponent p) :=
  Ideal.span (Set.range
    (projectiveChartInactiveBlockPolynomial q n z j exponent p))

/-- An all-row presentation of the coefficient-prime-localized incidence ring. Active rows have
already been imposed in disjoint blocks; every inactive row equation is imposed in its own
remaining block here. -/
abbrev projectiveChartFullIncidenceRing
    {row κ : Type} [Fintype row] [Fintype κ] [DecidableEq κ]
    (q n : ℕ) (z : row → ℂ) (j : κ × Fin (q + 1))
    (exponent : κ → (Fin n →₀ ℕ))
    (p : Ideal (MvPolynomial (projectiveChartVar j) ℂ)) [p.IsPrime] :=
  projectiveChartFullIncidenceAmbient q n z j exponent p ⧸
    projectiveChartFullIncidenceIdeal q n z j exponent p

theorem natCard_projectiveChartInactiveRow
    {row κ : Type} [Fintype row] [Fintype κ] [DecidableEq κ]
    (q : ℕ) (z : row → ℂ) (j : κ × Fin (q + 1))
    (p : Ideal (MvPolynomial (projectiveChartVar j) ℂ)) :
    Nat.card (projectiveChartInactiveRow q z j p) =
      Fintype.card row - Nat.card (projectiveChartGoodRow q z j p) := by
  classical
  let s : Set row :=
    {b | ∃ a, rowCoefficientPolynomialOf q z (projectiveChartCoefficient j) b a ∉ p}
  change Nat.card (sᶜ : Set row) = Fintype.card row - Nat.card s
  rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq, Set.ncard_compl]
  rw [Nat.card_eq_fintype_card]

theorem projectiveChartFullIncidenceRing_krullDim_le_localModel
    {row κ : Type} [Fintype row] [DecidableEq row]
    [Fintype κ] [DecidableEq κ]
    (q n : ℕ) (z : row → ℂ)
    (j : κ × Fin (q + 1))
    (exponent : κ → (Fin n →₀ ℕ))
    (p : Ideal (MvPolynomial (projectiveChartVar j) ℂ)) [p.IsPrime] :
    ringKrullDim (projectiveChartFullIncidenceRing q n z j exponent p) ≤
      ringKrullDim (projectiveChartLocalIncidenceRing q n z j exponent p) := by
  classical
  letI : IsNoetherianRing (projectiveChartActiveBlockRing q n z j exponent p) :=
    projectiveChartActiveBlockRing_isNoetherian q n z j exponent p
  calc
    ringKrullDim (projectiveChartFullIncidenceRing q n z j exponent p) ≤
        ringKrullDim (projectiveChartFullIncidenceAmbient q n z j exponent p) :=
      ringKrullDim_quotient_le _
    _ = ringKrullDim (projectiveChartActiveBlockRing q n z j exponent p) +
        Nat.card (projectiveChartInactiveRow q z j p × Fin n) :=
      MvPolynomial.ringKrullDim_of_isNoetherianRing
    _ = ringKrullDim (projectiveChartActiveBlockRing q n z j exponent p) +
        (((Fintype.card row - Nat.card (projectiveChartGoodRow q z j p)) * n : ℕ) :
          WithBot ℕ∞) := by
      rw [Nat.card_prod, Nat.card_fin, natCard_projectiveChartInactiveRow]
    _ = ringKrullDim (projectiveChartLocalIncidenceRing q n z j exponent p) := by
      change ringKrullDim (projectiveChartActiveBlockRing q n z j exponent p) +
          (((Fintype.card row - Nat.card (projectiveChartGoodRow q z j p)) * n : ℕ) :
            WithBot ℕ∞) =
        ringKrullDim
          (MvPolynomial
            (Fin ((Fintype.card row - Nat.card (projectiveChartGoodRow q z j p)) * n))
            (projectiveChartActiveBlockRing q n z j exponent p))
      rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, Nat.card_fin]

/-- The exact projective evaluation-codimension threshold for the all-row local incidence
quotient, rather than only for its free inactive-row upper model. -/
theorem projectiveChartFullIncidenceRing_evaluationCodimension
    {row κ : Type} [Fintype row] [DecidableEq row]
    [Fintype κ] [DecidableEq κ]
    (q n : ℕ) (z : row → ℂ) (hz : Function.Injective z)
    (j : κ × Fin (q + 1))
    (exponent : κ → (Fin n →₀ ℕ)) (hexponent : Function.Injective exponent)
    (p : Ideal (MvPolynomial (projectiveChartVar j) ℂ)) [p.IsPrime]
    (hrows : Fintype.card (κ × Fin (q + 1)) + q < Fintype.card row) :
    ringKrullDim (projectiveChartFullIncidenceRing q n z j exponent p) +
        ((Fintype.card row - Fintype.card (κ × Fin (q + 1)) - q + 1 : ℕ) :
          WithBot ℕ∞) ≤
      (Fintype.card row * n : ℕ) := by
  calc
    _ ≤ ringKrullDim (projectiveChartLocalIncidenceRing q n z j exponent p) +
        ((Fintype.card row - Fintype.card (κ × Fin (q + 1)) - q + 1 : ℕ) :
          WithBot ℕ∞) := by
      simpa [add_comm] using add_le_add_right
        (projectiveChartFullIncidenceRing_krullDim_le_localModel q n z j exponent p)
        ((Fintype.card row - Fintype.card (κ × Fin (q + 1)) - q + 1 : ℕ) :
          WithBot ℕ∞)
    _ ≤ _ := projectiveChartLocalIncidenceRing_evaluationCodimension
      q n z hz j exponent hexponent p hrows

end
end GaloisForLFunctions.HTGeometry
