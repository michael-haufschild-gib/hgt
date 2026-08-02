import GaloisForLFunctions.HTGeometry.RationalPhaseRankConsequences
import GaloisForLFunctions.HTGeometry.StripAlmostPeriodicExpSum
import GaloisForLFunctions.HTGeometry.ExponentialSumDA
import GaloisForLFunctions.HTGeometry.BohrDerivativeSpectrum

/-!
# The phase rank of an exponential sum is the number of its frequencies

The finite phase law bounds the rational rank of the frequency module of a solution of a relation
with coefficients in `ℂ(s)⟨Γ⟩`, and the bound grows with the order of the relation.  It cannot be
improved to a bound independent of the relation: a sum of `r` exponentials with rationally
independent real frequencies satisfies a constant-coefficient linear differential equation of order
`r` — the most special kind of Gamma-field relation — and the frequency module of its restriction to
a vertical line has rank exactly `r`.
-/

open Filter Set Topology

open scoped BoundedContinuousFunction

namespace GaloisForLFunctions

open _root_.HTGeometry

noncomputable section

open scoped BigOperators

/-- The restriction of an exponential sum to a vertical line is a trigonometric polynomial. -/
theorem expSum_line_eq {r : ℕ} (a : Fin r → ℂ) (μ : Fin r → ℝ) (σ : ℝ) :
    (fun t : ℝ => expSum a μ ((σ : ℂ) + (t : ℂ) * Complex.I))
      = fun t : ℝ => ∑ k : Fin r, (a k * ((Real.exp (μ k * σ) : ℝ) : ℂ)) * expChar (μ k) t := by
  funext t
  rw [expSum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [expChar, Complex.ofReal_exp, mul_assoc, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- **The spectrum of an exponential sum is its frequency set.** -/
theorem bohrSpectrum_expSum_line {r : ℕ} {a : Fin r → ℂ} (ha : ∀ k, a k ≠ 0) {μ : Fin r → ℝ}
    (hμ : Function.Injective μ) (σ : ℝ) :
    bohrSpectrum (fun t : ℝ => expSum a μ ((σ : ℂ) + (t : ℂ) * Complex.I))
      = Set.range μ := by
  classical
  set c : Fin r → ℂ := fun k => a k * ((Real.exp (μ k * σ) : ℝ) : ℂ) with hc
  have hcne : ∀ k, c k ≠ 0 := by
    intro k
    refine mul_ne_zero (ha k) ?_
    have : (0 : ℝ) < Real.exp (μ k * σ) := Real.exp_pos _
    exact_mod_cast ne_of_gt this
  have hfun : (fun t : ℝ => expSum a μ ((σ : ℂ) + (t : ℂ) * Complex.I))
      = fun t : ℝ => ∑ k : Fin r, c k * expChar (μ k) t := expSum_line_eq a μ σ
  have hcoeff : ∀ lam : ℝ,
      bohrCoefficient (fun t : ℝ => expSum a μ ((σ : ℂ) + (t : ℂ) * Complex.I)) lam
        = ∑ k : Fin r, if μ k = lam then c k else 0 := by
    intro lam
    rw [hfun]
    exact bohrCoefficient_sum_expChar Finset.univ c μ lam
  ext lam
  constructor
  · intro hlam
    have hne : bohrCoefficient (fun t : ℝ => expSum a μ ((σ : ℂ) + (t : ℂ) * Complex.I)) lam ≠ 0 :=
      hlam
    rw [hcoeff lam] at hne
    by_contra hnot
    refine hne (Finset.sum_eq_zero fun k _ => ?_)
    have hk : μ k ≠ lam := by
      intro h
      exact hnot ⟨k, h⟩
    rw [if_neg hk]
  · rintro ⟨k, rfl⟩
    show bohrCoefficient (fun t : ℝ => expSum a μ ((σ : ℂ) + (t : ℂ) * Complex.I)) (μ k) ≠ 0
    rw [hcoeff (μ k)]
    have hsingle : (∑ j : Fin r, if μ j = μ k then c j else 0) = c k := by
      rw [Finset.sum_eq_single k]
      · rw [if_pos rfl]
      · intro j _ hj
        have hne : μ j ≠ μ k := fun h => hj (hμ h)
        rw [if_neg hne]
      · intro h
        exact absurd (Finset.mem_univ k) h
    rw [hsingle]
    exact hcne k

/-- **The phase rank of an exponential sum with independent frequencies is the number of its
frequencies.**  So the finite phase law's bound is attained at every rank. -/
theorem rank_bohrFrequencyModule_expSum_line {r : ℕ} {a : Fin r → ℂ} (ha : ∀ k, a k ≠ 0)
    {μ : Fin r → ℝ} (hμ : LinearIndependent ℚ μ) (σ : ℝ) :
    Module.rank ℚ
        (bohrFrequencyModule fun t : ℝ => expSum a μ ((σ : ℂ) + (t : ℂ) * Complex.I))
      = (r : Cardinal) := by
  have hinj : Function.Injective μ := hμ.injective
  rw [bohrFrequencyModule, bohrSpectrum_expSum_line ha hinj σ, rank_span hμ,
    Cardinal.mk_range_eq μ hinj, Cardinal.mk_fin]

end

end GaloisForLFunctions
