import GaloisForLFunctions.HTGeometry.SzegoConcretePolynomial
import GaloisForLFunctions.HTGeometry.GramDeterminantDistance
import GaloisForLFunctions.HTGeometry.SzegoLowerBoundGeneral
import GaloisForLFunctions.HTGeometry.PureSingularCarrierTrichotomy

/-!
# Szegő upper bound: the extremal minimization

The `≤` half of the first Szegő limit theorem rests on the extremal property of the monic OPUC
element: `‖Φ_N‖²_{L²(μ)}` is the *minimum* of `∫|P|² dμ` over monic degree-`N` polynomials `P`.
Equivalently, by the modulus-preserving reversal `P ↦ P*`, it is the minimum of `∫|Q|² dμ` over
polynomials `Q` of degree `≤ N` with `Q(0) = 1`.  Thus for *any* such polynomial `Q`,
`‖Φ_N‖² ≤ ∫|Q|² dμ`, and choosing `Q` to approximate the reciprocal outer function `D(0)/D` drives
the right-hand side down to the geometric mean.

This module builds the extremal inequality (the minimization side); the approximation input is the
boundary identity `|D|² = w` established in `SzegoOuterBoundary`.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Complex InnerProductSpace
open scoped InnerProductSpace ComplexConjugate

/-- **Extremal inequality for the monic problem.**  The squared monic OPUC norm is a lower bound for
`∫|P|² dμ` over *every* monic degree-`N` polynomial `P = zᴺ - ∑_{i<N} cᵢ zⁱ`. -/
theorem normSq_gramSchmidt_le_integral_monicPoly
    (mu : Measure Circle) [IsFiniteMeasure mu] (N : ℕ) (c : ℕ → ℂ) :
    ‖gramSchmidt ℂ (circleMonomialLp mu) N‖ ^ 2
      ≤ ∫ z : Circle, ‖monicPoly c N (z : ℂ)‖ ^ 2 ∂mu := by
  classical
  set cm := circleMonomialLp mu with hcm
  set w : Lp ℂ 2 mu := ∑ i ∈ Finset.range N, c i • cm i with hw
  have hwmem : w ∈ Submodule.span ℂ (gramSchmidt ℂ cm '' Set.Iio N) := by
    rw [span_gramSchmidt_Iio ℂ cm N, hw]
    refine Submodule.sum_mem _ (fun i hi => ?_)
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, Finset.mem_range.mp hi, rfl⟩)
  have hle := norm_gramSchmidt_le_of_mem_span cm N hwmem
  have hnormsq : ‖cm N - w‖ ^ 2 = ∫ z : Circle, ‖monicPoly c N (z : ℂ)‖ ^ 2 ∂mu := by
    rw [norm_sq_eq_integral_norm_sq]
    refine integral_congr_ae ?_
    filter_upwards [Lp.coeFn_sub (cm N) w, circleMonomialLp_coeFn_ae mu N,
      coeFn_sum_smul_circleMonomialLp mu (Finset.range N) c] with z h1 h2 h3
    rw [h1, Pi.sub_apply, h2, h3, monicPoly]
  calc ‖gramSchmidt ℂ (circleMonomialLp mu) N‖ ^ 2
      ≤ ‖cm N - w‖ ^ 2 := by gcongr
    _ = _ := hnormsq

/-- **Extremal inequality for the reversed problem.**  For *every* value-`1`-at-origin reversed
polynomial `q* = 1 - ∑_{i<N} conj(cᵢ) z^{N-i}`, the squared monic OPUC norm is a lower bound for
`∫|q*|² dμ`.  Together with an approximation `q* → D(0)/D` this yields `⨅ₙ ‖Φₙ‖² ≤ GM`. -/
theorem normSq_gramSchmidt_le_integral_revPoly
    (mu : Measure Circle) [IsFiniteMeasure mu] (N : ℕ) (c : ℕ → ℂ) :
    ‖gramSchmidt ℂ (circleMonomialLp mu) N‖ ^ 2
      ≤ ∫ z : Circle, ‖revPoly c N (z : ℂ)‖ ^ 2 ∂mu := by
  refine (normSq_gramSchmidt_le_integral_monicPoly mu N c).trans_eq ?_
  refine integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
  simp only [norm_revPoly_eq_on_circle]

open Filter Topology

/-- **Reduction of the Szegő upper bound to the outer-function approximation.**  If for every `ε`
there is a value-`1`-at-origin reversed polynomial `q*` with `∫|q*|² dμ ≤ GM + ε` (the reversed
Taylor polynomials of `D(0)/D` supply these), then the infimum of the squared monic OPUC norms is
`≤ GM`.  Combined with the Szegő lower bound this pins the infimum at `GM`. -/
theorem ciInf_normSq_le_of_approx (mu : Measure Circle) [IsFiniteMeasure mu]
    (happrox : ∀ ε > 0, ∃ N c, (∫ z : Circle, ‖revPoly c (N + 1) (z : ℂ)‖ ^ 2 ∂mu)
      ≤ szegoGeometricMean circleLebesgue (mu.rnDeriv circleLebesgue) + ε) :
    (⨅ N, ‖gramSchmidt ℂ (circleMonomialLp mu) (N + 1)‖ ^ 2)
      ≤ szegoGeometricMean circleLebesgue (mu.rnDeriv circleLebesgue) := by
  have hbdd : BddBelow (Set.range (fun N => ‖gramSchmidt ℂ (circleMonomialLp mu) (N + 1)‖ ^ 2)) :=
    ⟨0, by rintro _ ⟨N, rfl⟩; positivity⟩
  refine le_of_forall_pos_le_add (fun ε hε => ?_)
  obtain ⟨N, c, hNc⟩ := happrox ε hε
  calc (⨅ N, ‖gramSchmidt ℂ (circleMonomialLp mu) (N + 1)‖ ^ 2)
      ≤ ‖gramSchmidt ℂ (circleMonomialLp mu) (N + 1)‖ ^ 2 := ciInf_le hbdd N
    _ ≤ ∫ z : Circle, ‖revPoly c (N + 1) (z : ℂ)‖ ^ 2 ∂mu :=
        normSq_gramSchmidt_le_integral_revPoly mu (N + 1) c
    _ ≤ _ := hNc

/-- **The first Szegő limit theorem, reduced to the outer-function approximation.**  For an
infinite-support finite circle measure, the full determinant-ratio conclusion holds as soon as the
reversed-polynomial approximation `∫|q*|² dμ → GM` is available.  This discharges the extremal
minimization (upper bound) and the Szegő lower bound; the residual is exactly the classical outer
approximation `q* → D(0)/D`. -/
theorem hasSzegoFirstLimitConclusion_of_approx (mu : Measure Circle) [IsFiniteMeasure mu]
    (hmu : mu.support.Infinite)
    (happrox : ∀ ε > 0, ∃ N c, (∫ z : Circle, ‖revPoly c (N + 1) (z : ℂ)‖ ^ 2 ∂mu)
      ≤ szegoGeometricMean circleLebesgue (mu.rnDeriv circleLebesgue) + ε) :
    HasSzegoFirstLimitConclusion (circleMeasureGramTower mu) mu circleLebesgue :=
  hasSzegoFirstLimitConclusion_of_ciInf_eq mu hmu circleLebesgue
    (le_antisymm (ciInf_normSq_le_of_approx mu happrox)
      (szegoGeometricMean_le_ciInf_normSq_gramSchmidt mu))

end GaloisForLFunctions.HTGeometry
