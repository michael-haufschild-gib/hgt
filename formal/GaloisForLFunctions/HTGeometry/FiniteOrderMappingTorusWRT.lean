import GaloisForLFunctions.HTGeometry.WittenPhasePolynomialRigidity

/-!
# Finite-order mapping-torus WRT calibration

Andersen, *The Witten--Reshetikhin--Turaev invariants of finite order mapping tori I*,
Remark 1.1, records the exact `SU(2)` WRT value `Zₖ(T²₋Id) = k + 1`.  This file formalizes the
right-hand side and its exact Chern--Simons expansion.  It does not yet derive that formula from
a Lean construction of the non-abelian RT TQFT; that construction is the open infrastructure gap.
-/

open Filter Topology Asymptotics
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

open RHTower

/-- Published exact level formula for the `SU(2)` WRT invariant of the finite-order torus
mapping-torus calibration case. -/
def su2MinusIdentityTorusMappingTorusWRTFormula (k : ℕ) : ℂ :=
  (k : ℂ) + 1

/-- Its unique phase has constant and linear amplitudes. -/
def su2MinusIdentityTorusMappingTorusCoefficient (_ : Fin 1) (j : ℕ) : ℂ :=
  if j = 0 then 1 else if j = 1 then 1 else 0

/-- The published finite-order mapping-torus formula is an exact one-phase degree-one expansion. -/
theorem su2MinusIdentityTorusMappingTorusWRTFormula_exactExpansion :
    HasExactFinitePhasePolynomialExpansion su2MinusIdentityTorusMappingTorusWRTFormula
      Finset.univ (fun _ : Fin 1 => 1)
      su2MinusIdentityTorusMappingTorusCoefficient 1 := by
  funext k
  simp [su2MinusIdentityTorusMappingTorusWRTFormula, finitePhasePolynomial,
    su2MinusIdentityTorusMappingTorusCoefficient]
  norm_num [Finset.sum_range_succ]
  ring

/-- This finite-order mapping-torus formula has zero remainder at every inverse-power order. -/
theorem su2MinusIdentityTorusMappingTorusWRTFormula_hasAllOrdersRemainder :
    HasAllOrdersFinitePhasePolynomialRemainder su2MinusIdentityTorusMappingTorusWRTFormula
      Finset.univ (fun _ : Fin 1 => 1)
      su2MinusIdentityTorusMappingTorusCoefficient 1 :=
  su2MinusIdentityTorusMappingTorusWRTFormula_exactExpansion.hasAllOrdersRemainder

/-- The calibration formula satisfies the degree-one polynomial bound predicted by the
finite-order mapping-torus theorem. -/
theorem su2MinusIdentityTorusMappingTorusWRTFormula_isBigO :
    su2MinusIdentityTorusMappingTorusWRTFormula =O[atTop] fun k : ℕ => (k : ℂ) := by
  simpa using su2MinusIdentityTorusMappingTorusWRTFormula_exactExpansion.isBigO
    (fun _ _ => norm_one)

/-- The published calibration formula is genuinely unbounded; it cannot be compressed into a
degree-zero unit-phase expansion. -/
theorem su2MinusIdentityTorusMappingTorusWRTFormula_not_isBigO_const :
    ¬ su2MinusIdentityTorusMappingTorusWRTFormula =O[atTop] fun _ : ℕ => (1 : ℂ) := by
  intro h
  rcases h.bound with ⟨C, hC⟩
  have hlarge : ∀ᶠ n : ℕ in atTop, C < (n : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually_gt_atTop C
  obtain ⟨n, hn, hgt⟩ := (hC.and hlarge).exists
  simp only [su2MinusIdentityTorusMappingTorusWRTFormula, norm_one] at hn
  have hnorm : ‖(n : ℂ) + 1‖ = (n : ℝ) + 1 := by
    rw [show (n : ℂ) + 1 = ((n + 1 : ℕ) : ℂ) by norm_num]
    rw [Complex.norm_natCast]
    norm_num
  rw [hnorm] at hn
  linarith

/-- In particular, no finite unit-phase degree-zero formula can represent this WRT calibration
sequence exactly.  The linear growth is an unavoidable asymptotic datum. -/
theorem su2MinusIdentityTorusMappingTorusWRTFormula_not_degreeZeroExactExpansion
    {ι : Type*} (s : Finset ι) (phase : ι → ℂ) (coefficient : ι → ℕ → ℂ)
    (hphase : ∀ i ∈ s, ‖phase i‖ = 1) :
    ¬ HasExactFinitePhasePolynomialExpansion su2MinusIdentityTorusMappingTorusWRTFormula
      s phase coefficient 0 := by
  intro h
  apply su2MinusIdentityTorusMappingTorusWRTFormula_not_isBigO_const
  simpa using h.isBigO hphase

/-- The linear WRT contribution survives after aggregating all equal Chern--Simons phases.
Thus its degree-one growth cannot be an artifact of an uncollected phase presentation. -/
theorem su2MinusIdentityTorusMappingTorusWRTFormula_exists_nonzeroLeadingFiber :
    ∃ u ∈ Finset.univ.image (fun _ : Fin 1 => (1 : ℂ)),
      finiteExponentialFiberCoefficient Finset.univ
        (fun i : Fin 1 => su2MinusIdentityTorusMappingTorusCoefficient i 1)
        (fun _ : Fin 1 => (1 : ℂ)) u ≠ 0 := by
  by_contra h
  have hfiber : ∀ u ∈ Finset.univ.image (fun _ : Fin 1 => (1 : ℂ)),
      finiteExponentialFiberCoefficient Finset.univ
        (fun i : Fin 1 => su2MinusIdentityTorusMappingTorusCoefficient i 1)
        (fun _ : Fin 1 => (1 : ℂ)) u = 0 := by
    intro u hu
    by_contra hne
    exact h ⟨u, hu, hne⟩
  have hcollapse := finitePhasePolynomial_degreeOne_eq_degreeZero_of_leadingFiberZero
    Finset.univ (fun _ : Fin 1 => (1 : ℂ))
    su2MinusIdentityTorusMappingTorusCoefficient hfiber
  apply su2MinusIdentityTorusMappingTorusWRTFormula_not_degreeZeroExactExpansion
    Finset.univ (fun _ : Fin 1 => (1 : ℂ))
    su2MinusIdentityTorusMappingTorusCoefficient (fun _ _ => norm_one)
  calc
    su2MinusIdentityTorusMappingTorusWRTFormula =
        finitePhasePolynomial Finset.univ (fun _ : Fin 1 => (1 : ℂ))
          su2MinusIdentityTorusMappingTorusCoefficient 1 :=
      su2MinusIdentityTorusMappingTorusWRTFormula_exactExpansion
    _ = finitePhasePolynomial Finset.univ (fun _ : Fin 1 => (1 : ℂ))
          su2MinusIdentityTorusMappingTorusCoefficient 0 := hcollapse

end GaloisForLFunctions.HTGeometry
