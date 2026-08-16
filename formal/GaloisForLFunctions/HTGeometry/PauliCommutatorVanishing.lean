import GaloisForLFunctions.HTGeometry.PauliChainLabels

/-!
# Scalar equations from a vanishing Pauli commutator

A vanishing commutator of two Pauli combinations gives, for every Pauli string, one scalar equation
on the index pairs whose label product is that string.  Pairs with disjoint supports drop out, and
if the string is supported on three sites then only pairs of two-site labels overlapping in exactly
one site survive.
-/

open Finset Matrix

noncomputable section

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

/-- The commutator coefficient of an index pair. -/
def pairCoefficient (S : ι → (σ → Option (Fin 3))) (h k : ι → ℂ)
    (R : σ → Option (Fin 3)) (i j : ι) : ℂ :=
  h i * k j * ((optPhaseProd (S i) (S j) - optPhaseProd (S j) (S i)) *
    (if R = optMulLabel (S i) (S j) then 1 else 0))

/-- **A vanishing commutator gives one scalar equation per Pauli string.** -/
theorem sum_pairCoefficient_eq_zero {ι : Type*} [Fintype ι] (S : ι → (σ → Option (Fin 3)))
    (h k : ι → ℂ)
    (hcomm : (∑ i, h i • finitePauliMatrix (S i)) * (∑ j, k j • finitePauliMatrix (S j)) =
      (∑ j, k j • finitePauliMatrix (S j)) * (∑ i, h i • finitePauliMatrix (S i)))
    (R : σ → Option (Fin 3)) :
    (∑ i, ∑ j, pairCoefficient S h k R i j) = 0 := by
  classical
  have hzero := trace_pauli_commutator_sum R S S h k
  rw [hcomm, sub_self, Matrix.mul_zero, Matrix.trace_zero] at hzero
  have hpow : ((2 : ℂ) ^ Fintype.card σ) ≠ 0 := pow_ne_zero _ two_ne_zero
  have hfactor : (∑ i, ∑ j, h i * k j * ((optPhaseProd (S i) (S j) - optPhaseProd (S j) (S i)) *
      (if R = optMulLabel (S i) (S j) then (2 : ℂ) ^ Fintype.card σ else 0))) =
      ((2 : ℂ) ^ Fintype.card σ) * ∑ i, ∑ j, pairCoefficient S h k R i j := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [pairCoefficient]
    by_cases hRij : R = optMulLabel (S i) (S j)
    · rw [if_pos hRij, if_pos hRij]
      ring
    · rw [if_neg hRij, if_neg hRij]
      ring
  rw [hfactor] at hzero
  exact (mul_eq_zero.mp hzero.symm).resolve_left hpow

theorem pairCoefficient_eq_zero_of_disjoint {ι : Type*} (S : ι → (σ → Option (Fin 3)))
    (h k : ι → ℂ) (R : σ → Option (Fin 3)) {i j : ι}
    (hdisj : Disjoint (labelSupport (S i)) (labelSupport (S j))) :
    pairCoefficient S h k R i j = 0 := by
  rw [pairCoefficient, optPhaseProd_sub_eq_zero_of_disjoint hdisj, zero_mul, mul_zero]

theorem pairCoefficient_eq_zero_of_ne {ι : Type*} (S : ι → (σ → Option (Fin 3)))
    (h k : ι → ℂ) (R : σ → Option (Fin 3)) {i j : ι}
    (hne : R ≠ optMulLabel (S i) (S j)) :
    pairCoefficient S h k R i j = 0 := by
  rw [pairCoefficient, if_neg hne, mul_zero, mul_zero]

/-- **Only overlapping two-site pairs survive at a three-site string.** -/
theorem pairCoefficient_eq_zero_of_card {ι : Type*} (S : ι → (σ → Option (Fin 3)))
    (h k : ι → ℂ) (R : σ → Option (Fin 3)) (hR : (labelSupport R).card = 3)
    (hsupp : ∀ i, (labelSupport (S i)).card ≤ 2) {i j : ι}
    (hnot : ¬ ((labelSupport (S i)).card = 2 ∧ (labelSupport (S j)).card = 2 ∧
      (labelSupport (S i) ∩ labelSupport (S j)).card = 1 ∧
      labelSupport (S i) ∪ labelSupport (S j) = labelSupport R)) :
    pairCoefficient S h k R i j = 0 := by
  classical
  by_cases hRij : R = optMulLabel (S i) (S j)
  · by_cases hdisj : Disjoint (labelSupport (S i)) (labelSupport (S j))
    · exact pairCoefficient_eq_zero_of_disjoint S h k R hdisj
    · exact absurd (card_inter_eq_one_of_card_three (hsupp i) (hsupp j) hR hRij hdisj) hnot
  · exact pairCoefficient_eq_zero_of_ne S h k R hRij

/-- **The scalar equation restricted to the surviving pairs.** -/
theorem sum_pairCoefficient_filter_eq_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : ι → (σ → Option (Fin 3))) (h k : ι → ℂ)
    (hcomm : (∑ i, h i • finitePauliMatrix (S i)) * (∑ j, k j • finitePauliMatrix (S j)) =
      (∑ j, k j • finitePauliMatrix (S j)) * (∑ i, h i • finitePauliMatrix (S i)))
    (R : σ → Option (Fin 3)) (hR : (labelSupport R).card = 3)
    (hsupp : ∀ i, (labelSupport (S i)).card ≤ 2)
    (good : ι → ι → Prop) [DecidablePred fun p : ι × ι => good p.1 p.2]
    (hgood : ∀ i j, (labelSupport (S i)).card = 2 → (labelSupport (S j)).card = 2 →
      (labelSupport (S i) ∩ labelSupport (S j)).card = 1 →
      labelSupport (S i) ∪ labelSupport (S j) = labelSupport R → good i j) :
    (∑ p ∈ (Finset.univ : Finset (ι × ι)).filter fun p => good p.1 p.2,
      pairCoefficient S h k R p.1 p.2) = 0 := by
  classical
  have htotal := sum_pairCoefficient_eq_zero S h k hcomm R
  have hprod : (∑ i, ∑ j, pairCoefficient S h k R i j) =
      ∑ p : ι × ι, pairCoefficient S h k R p.1 p.2 :=
    (Fintype.sum_prod_type (fun p : ι × ι => pairCoefficient S h k R p.1 p.2)).symm
  rw [hprod] at htotal
  have hsplit : (∑ p ∈ (Finset.univ : Finset (ι × ι)).filter fun p => good p.1 p.2,
        pairCoefficient S h k R p.1 p.2) +
      (∑ p ∈ (Finset.univ : Finset (ι × ι)).filter fun p => ¬ good p.1 p.2,
        pairCoefficient S h k R p.1 p.2) =
      ∑ p : ι × ι, pairCoefficient S h k R p.1 p.2 :=
    Finset.sum_filter_add_sum_filter_not _ _ _
  have hbad : (∑ p ∈ (Finset.univ : Finset (ι × ι)).filter fun p => ¬ good p.1 p.2,
      pairCoefficient S h k R p.1 p.2) = 0 := by
    refine Finset.sum_eq_zero fun p hp => ?_
    rw [Finset.mem_filter] at hp
    refine pairCoefficient_eq_zero_of_card S h k R hR hsupp ?_
    rintro ⟨h1, h2, h3, h4⟩
    exact hp.2 (hgood p.1 p.2 h1 h2 h3 h4)
  rw [hbad, add_zero, htotal] at hsplit
  exact hsplit

end GaloisForLFunctions.HTGeometry
