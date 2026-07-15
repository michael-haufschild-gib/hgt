import GaloisForLFunctions.HTGeometry.GammaInversePoleBranchCoefficientFreeness

/-!
# Every Gamma pole tail is Zariski dense in the inverse-branch horizon

The normalized inverse-Gamma branches have a countably algebraically independent coefficient
family in the eventual pole-index germ ring.  This file extracts the exact topological content of
that theorem.

A sequence of coefficient frames is *cofinally Zariski dense* when every nonzero polynomial
observable survives at some index beyond every prescribed horizon.  Algebraic independence in
the `atTop` germ ring is precisely strong enough to force this property: eventual vanishing would
make the corresponding germ zero.

Consequently every representative of the inverse-Gamma branch coefficient germs has a Zariski
dense tail at every finite jet order.  No finite algebraic observable becomes blind after passing
far enough along the negative Gamma poles.
-/

open MvPolynomial

namespace GaloisForLFunctions

noncomputable section

local instance gammaInversePoleCofinalNatGermAlgebra : Algebra ℂ NatGerm :=
  complexNatGerm.toAlgebra

/-- Every nonzero polynomial observable is detected beyond every finite horizon. -/
def CofinallyZariskiDense {ι : Type*} (x : ι → ℕ → ℂ) : Prop :=
  ∀ P : MvPolynomial ι ℂ, P ≠ 0 → ∀ N : ℕ,
    ∃ n : ℕ, N ≤ n ∧ MvPolynomial.eval (fun i => x i n) P ≠ 0

/-- Algebraic independence in the eventual sequence ring forces cofinal Zariski density of every
representative sequence. -/
theorem cofinallyZariskiDense_of_germ_algebraicIndependent
    {ι : Type*} (x : ι → ℕ → ℂ)
    (hx : AlgebraicIndependent ℂ (fun i => (x i : NatGerm))) :
    CofinallyZariskiDense x := by
  intro P hP N
  have hinjective : Function.Injective
      (MvPolynomial.aeval (fun i => (x i : NatGerm))) :=
    algebraicIndependent_iff_injective_aeval.mp hx
  have hgerm :
      MvPolynomial.aeval (fun i => (x i : NatGerm)) P ≠ 0 := by
    intro hzero
    apply hP
    apply hinjective
    simpa using hzero
  have hsequence :
      ((mvPolynomialSequenceEval x P : ℕ → ℂ) : NatGerm) ≠ 0 := by
    rwa [← aeval_sequenceGerm_eq x P]
  by_contra hdetect
  simp only [not_exists, not_and, not_not] at hdetect
  apply hsequence
  rw [← Filter.Germ.coe_zero, Filter.Germ.coe_eq]
  exact Filter.eventually_atTop.2 ⟨N, fun n hn => by
    rw [mvPolynomialSequenceEval_apply]
    exact hdetect n hn⟩

/-- **Cofinal inverse-Gamma horizon.**  Any sequence family representing the normalized
inverse-branch coefficient germs detects every nonzero polynomial observable arbitrarily far out
along the Gamma poles. -/
theorem gammaInversePoleBranchCoefficient_cofinallyZariskiDense
    (b : ℕ → ℕ → ℂ)
    (hb : ∀ j, (b j : NatGerm) = gammaInversePoleBranchCoefficientGerm j) :
    CofinallyZariskiDense b := by
  apply cofinallyZariskiDense_of_germ_algebraicIndependent
  have hfamily :
      (fun j => (b j : NatGerm)) = gammaInversePoleBranchCoefficientGerm := by
    funext j
    exact hb j
  rw [hfamily]
  exact algebraicIndependent_gammaInversePoleBranchCoefficientGerm

/-- Every finite jet truncation of every Gamma pole tail is Zariski dense in its affine
coefficient space, equivalently in the corresponding truncated group of formal diffeomorphisms
tangent to the identity. -/
theorem gammaInversePoleBranchCoefficient_fin_cofinallyZariskiDense
    (m : ℕ) (b : ℕ → ℕ → ℂ)
    (hb : ∀ j, (b j : NatGerm) = gammaInversePoleBranchCoefficientGerm j) :
    CofinallyZariskiDense (fun j : Fin m => b (j : ℕ)) := by
  apply cofinallyZariskiDense_of_germ_algebraicIndependent
  have hprefix := algebraicIndependent_gammaInversePoleBranchCoefficientGerm.comp
    (fun j : Fin m => (j : ℕ)) Fin.val_injective
  have hfamily :
      (fun j : Fin m => ((b (j : ℕ) : ℕ → ℂ) : NatGerm)) =
        fun j : Fin m => gammaInversePoleBranchCoefficientGerm (j : ℕ) := by
    funext j
    exact hb (j : ℕ)
  rw [hfamily]
  exact hprefix

end

end GaloisForLFunctions
