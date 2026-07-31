import GaloisForLFunctions.HTGeometry.CoefficientPrimeLocalIncidenceDimensionGeneral
import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.KrullDimension.Field

namespace GaloisForLFunctions.HTGeometry

noncomputable section

abbrev projectiveChartVar {I : Type} (j : I) := {i : I // i ≠ j}

def projectiveChartCoefficient
    {I : Type} [DecidableEq I] (j : I) (i : I) :
    MvPolynomial (projectiveChartVar j) ℂ :=
  if h : i = j then MvPolynomial.C 1 else MvPolynomial.X ⟨i, h⟩

@[simp] theorem projectiveChartCoefficient_self
    {I : Type} [DecidableEq I] (j : I) :
    projectiveChartCoefficient j j = 1 := by
  simp [projectiveChartCoefficient]

theorem natCard_projectiveChartVar
    {I : Type} [Fintype I] [DecidableEq I] (j : I) :
    Nat.card (projectiveChartVar j) = Fintype.card I - 1 := by
  classical
  rw [Nat.card_eq_fintype_card]
  change Fintype.card {i : I // i ≠ j} = Fintype.card I - 1
  rw [Fintype.card_subtype_compl (fun i : I => i = j)]
  congr 1

/-- The coefficient ring of a projective affine chart has local dimension at most `P - 1`. -/
theorem projectiveChart_localization_krullDim_le
    {I : Type} [Fintype I] [DecidableEq I] (j : I)
    (p : Ideal (MvPolynomial (projectiveChartVar j) ℂ)) [p.IsPrime] :
    ringKrullDim (Localization.AtPrime p) ≤
      ((Fintype.card I - 1 : ℕ) : WithBot ℕ∞) := by
  calc
    ringKrullDim (Localization.AtPrime p) = (p.height : WithBot ℕ∞) :=
      IsLocalization.AtPrime.ringKrullDim_eq_height p (Localization.AtPrime p)
    _ ≤ ringKrullDim (MvPolynomial (projectiveChartVar j) ℂ) :=
      Ideal.height_le_ringKrullDim_of_isPrime
    _ = ringKrullDim ℂ + Nat.card (projectiveChartVar j) :=
      MvPolynomial.ringKrullDim_of_isNoetherianRing
    _ = ((Fintype.card I - 1 : ℕ) : WithBot ℕ∞) := by
      rw [ringKrullDim_eq_zero_of_field, zero_add, natCard_projectiveChartVar]

/-- In every affine projective coefficient chart, the normalized coordinate survives every prime. -/
theorem projectiveChartCoefficient_projective
    {I : Type} [Fintype I] [DecidableEq I] (j : I)
    (p : Ideal (MvPolynomial (projectiveChartVar j) ℂ)) [p.IsPrime] :
    ∃ i, projectiveChartCoefficient j i ∉ p := by
  exact ⟨j, by simpa using Ideal.one_notMem p⟩

abbrev projectiveChartGoodRow
    {row κ : Type} [DecidableEq κ]
    (q : ℕ) (z : row → ℂ) (j : κ × Fin (q + 1))
    (p : Ideal (MvPolynomial (projectiveChartVar j) ℂ)) :=
  coefficientPrimeGoodRow q z (projectiveChartCoefficient j) p

abbrev projectiveChartActiveBlockRing
    {row κ : Type} [Fintype row] [Fintype κ] [DecidableEq κ]
    (q n : ℕ) (z : row → ℂ) (j : κ × Fin (q + 1))
    (exponent : κ → (Fin n →₀ ℕ))
    (p : Ideal (MvPolynomial (projectiveChartVar j) ℂ)) [p.IsPrime] :=
  coefficientPrimeActiveBlockRing q n z (projectiveChartCoefficient j) exponent p

/-- **Affine projective-chart incidence bound.** After normalizing one projective coefficient to
one, every coefficient prime has at least `card row - q` active equations, and the local active
incidence ring has coefficient contribution at most `P - 1`. -/
theorem projectiveChart_activeBlockRing_krullDim
    {row κ : Type} [Fintype row] [DecidableEq row]
    [Fintype κ] [DecidableEq κ]
    (q n : ℕ) (z : row → ℂ) (hz : Function.Injective z)
    (j : κ × Fin (q + 1))
    (exponent : κ → (Fin n →₀ ℕ)) (hexponent : Function.Injective exponent)
    (p : Ideal (MvPolynomial (projectiveChartVar j) ℂ)) [p.IsPrime] :
    Fintype.card row ≤ q + Nat.card (projectiveChartGoodRow q z j p) ∧
      ringKrullDim (projectiveChartActiveBlockRing q n z j exponent p) +
          Nat.card (projectiveChartGoodRow q z j p) ≤
        ((Fintype.card (κ × Fin (q + 1)) - 1 : ℕ) : WithBot ℕ∞) +
          Nat.card (projectiveChartGoodRow q z j p) * n := by
  classical
  have hlocal := coefficientPrime_activeBlockRing_krullDim
    q n z hz (projectiveChartCoefficient j) exponent hexponent p
    (projectiveChartCoefficient_projective j p)
  refine ⟨hlocal.1, hlocal.2.trans ?_⟩
  simpa [add_comm] using add_le_add_right (projectiveChart_localization_krullDim_le j p)
    (Nat.card (projectiveChartGoodRow q z j p) * n)

def projectiveChartLocalIncidenceRing
    {row κ : Type} [Fintype row] [Fintype κ] [DecidableEq κ]
    (q n : ℕ) (z : row → ℂ) (j : κ × Fin (q + 1))
    (exponent : κ → (Fin n →₀ ℕ))
    (p : Ideal (MvPolynomial (projectiveChartVar j) ℂ)) [p.IsPrime] :
    CommAlgCat (Localization.AtPrime p) :=
  CommAlgCat.of (Localization.AtPrime p)
    (MvPolynomial
      (Fin ((Fintype.card row - Nat.card (projectiveChartGoodRow q z j p)) * n))
      (projectiveChartActiveBlockRing q n z j exponent p))

theorem projectiveChartActiveBlockRing_isNoetherian
    {row κ : Type} [Fintype row] [Fintype κ] [DecidableEq κ]
    (q n : ℕ) (z : row → ℂ) (j : κ × Fin (q + 1))
    (exponent : κ → (Fin n →₀ ℕ))
    (p : Ideal (MvPolynomial (projectiveChartVar j) ℂ)) [p.IsPrime] :
    IsNoetherianRing (projectiveChartActiveBlockRing q n z j exponent p) := by
  unfold projectiveChartActiveBlockRing coefficientPrimeActiveBlockRing
  apply iteratedUnitCoefficientBlockRing_isNoetherian

/-- The local chart incidence model includes the inactive rows as free blocks. Its dimension plus
the number of active equations is bounded by the packet dimension plus `P - 1`. -/
theorem projectiveChartLocalIncidenceRing_krullDim_add_active_le
    {row κ : Type} [Fintype row] [DecidableEq row]
    [Fintype κ] [DecidableEq κ]
    (q n : ℕ) (z : row → ℂ) (hz : Function.Injective z)
    (j : κ × Fin (q + 1))
    (exponent : κ → (Fin n →₀ ℕ)) (hexponent : Function.Injective exponent)
    (p : Ideal (MvPolynomial (projectiveChartVar j) ℂ)) [p.IsPrime] :
    ringKrullDim (projectiveChartLocalIncidenceRing q n z j exponent p) +
        Nat.card (projectiveChartGoodRow q z j p) ≤
      ((Fintype.card (κ × Fin (q + 1)) - 1 : ℕ) : WithBot ℕ∞) +
        Fintype.card row * n := by
  classical
  let r := Nat.card (projectiveChartGoodRow q z j p)
  let R := Fintype.card row
  let free := (R - r) * n
  letI : IsNoetherianRing (projectiveChartActiveBlockRing q n z j exponent p) :=
    projectiveChartActiveBlockRing_isNoetherian q n z j exponent p
  have hactive := (projectiveChart_activeBlockRing_krullDim
    q n z hz j exponent hexponent p).2
  have hrR : r ≤ R := by
    dsimp [r, R]
    rw [← Nat.card_eq_fintype_card]
    exact Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
  change ringKrullDim
      (MvPolynomial (Fin free) (projectiveChartActiveBlockRing q n z j exponent p)) + r ≤
    ((Fintype.card (κ × Fin (q + 1)) - 1 : ℕ) : WithBot ℕ∞) + R * n
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing]
  rw [Nat.card_fin]
  calc
    _ = (ringKrullDim (projectiveChartActiveBlockRing q n z j exponent p) + r) +
        free := by ac_rfl
    _ ≤ (((Fintype.card (κ × Fin (q + 1)) - 1 : ℕ) : WithBot ℕ∞) +
        r * n) + free := by
      simpa [add_comm] using add_le_add_right hactive free
    _ = ((Fintype.card (κ × Fin (q + 1)) - 1 : ℕ) : WithBot ℕ∞) +
        R * n := by
      rw [add_assoc]
      congr 1
      norm_cast
      change r * n + (R - r) * n = R * n
      rw [← add_mul, add_comm r (R - r), Nat.sub_add_cancel hrR]

/-- Exact local total-incidence codimension form: after projectivizing coefficients, the chart
incidence dimension loses at least `card row - q` dimensions. -/
theorem projectiveChartLocalIncidenceRing_krullDim_add_row_sub_degree_le
    {row κ : Type} [Fintype row] [DecidableEq row]
    [Fintype κ] [DecidableEq κ]
    (q n : ℕ) (z : row → ℂ) (hz : Function.Injective z)
    (j : κ × Fin (q + 1))
    (exponent : κ → (Fin n →₀ ℕ)) (hexponent : Function.Injective exponent)
    (p : Ideal (MvPolynomial (projectiveChartVar j) ℂ)) [p.IsPrime] :
    ringKrullDim (projectiveChartLocalIncidenceRing q n z j exponent p) +
        ((Fintype.card row - q : ℕ) : WithBot ℕ∞) ≤
      ((Fintype.card (κ × Fin (q + 1)) - 1 : ℕ) : WithBot ℕ∞) +
        Fintype.card row * n := by
  have hcount := (projectiveChart_activeBlockRing_krullDim
    q n z hz j exponent hexponent p).1
  have hsub : Fintype.card row - q ≤ Nat.card (projectiveChartGoodRow q z j p) := by
    omega
  have hcast : ((Fintype.card row - q : ℕ) : WithBot ℕ∞) ≤
      (Nat.card (projectiveChartGoodRow q z j p) : WithBot ℕ∞) := by
    exact_mod_cast hsub
  calc
    _ ≤ ringKrullDim (projectiveChartLocalIncidenceRing q n z j exponent p) +
        Nat.card (projectiveChartGoodRow q z j p) := by
      simpa [add_comm] using add_le_add_left hcast
        (ringKrullDim (projectiveChartLocalIncidenceRing q n z j exponent p))
    _ ≤ _ := projectiveChartLocalIncidenceRing_krullDim_add_active_le
      q n z hz j exponent hexponent p

/-- The manuscript's exact numerical codimension threshold on each projective affine chart. -/
theorem projectiveChartLocalIncidenceRing_evaluationCodimension
    {row κ : Type} [Fintype row] [DecidableEq row]
    [Fintype κ] [DecidableEq κ]
    (q n : ℕ) (z : row → ℂ) (hz : Function.Injective z)
    (j : κ × Fin (q + 1))
    (exponent : κ → (Fin n →₀ ℕ)) (hexponent : Function.Injective exponent)
    (p : Ideal (MvPolynomial (projectiveChartVar j) ℂ)) [p.IsPrime]
    (hrows : Fintype.card (κ × Fin (q + 1)) + q < Fintype.card row) :
    ringKrullDim (projectiveChartLocalIncidenceRing q n z j exponent p) +
        ((Fintype.card row - Fintype.card (κ × Fin (q + 1)) - q + 1 : ℕ) :
          WithBot ℕ∞) ≤
      (Fintype.card row * n : ℕ) := by
  let R := Fintype.card row
  let P := Fintype.card (κ × Fin (q + 1))
  let e := R - P - q + 1
  have hP : 0 < P := by
    dsimp [P]
    exact Fintype.card_pos_iff.mpr ⟨j⟩
  have hid : R - q = e + (P - 1) := by
    dsimp [e]
    omega
  have hbase := projectiveChartLocalIncidenceRing_krullDim_add_row_sub_degree_le
    q n z hz j exponent hexponent p
  change ringKrullDim (projectiveChartLocalIncidenceRing q n z j exponent p) +
      (e : WithBot ℕ∞) ≤ (R * n : ℕ)
  have hcancel :
      (ringKrullDim (projectiveChartLocalIncidenceRing q n z j exponent p) +
        (e : WithBot ℕ∞)) + (P - 1 : ℕ) ≤
      (R * n : WithBot ℕ∞) + (P - 1 : ℕ) := by
    simpa [R, P, hid, add_assoc, add_comm, add_left_comm] using hbase
  exact (ENat.WithBot.add_le_add_natCast_right_iff).mp hcancel

end
end GaloisForLFunctions.HTGeometry
