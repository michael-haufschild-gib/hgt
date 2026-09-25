import GaloisForLFunctions.RHTower.ZeroNetworkConductance

/-!
# The maximum principle replaces recurrence

Gate **R** of the transverse-equilibrium chain asked for recurrence of the zero network, in order to
run a Liouville argument: a bounded harmonic function on a recurrent network is constant.  That gate
is not needed in the form it was posed.

The zero network is **complete**: every pair of distinct divisor points has strictly positive
conductance, the reciprocal squared distance.  On a complete network the maximum principle does not
have to propagate along paths — it collapses in a single step.  If the displacement attains its
supremum at a point `ρ₀`, then at `ρ₀` every term of the transverse force is nonnegative, and the
force is the sum of those terms; harmonicity makes the sum zero, so **every term vanishes**, so the
real part is constant, so the hypothesis holds.

Neither recurrence, nor boundedness, nor the Liouville property is used.  What remains of the chain
is exactly the attained/non-attained dichotomy already isolated in the ledger: the argument settles
the attained case outright, and the non-attained case is untouched.
-/

open Complex

namespace RHTower

noncomputable section

/-- At a point of maximal real part every transverse force term is nonnegative. -/
theorem transverseForceTerm_nonneg_of_max {ρ₀ : XiDivisorSupport}
    (hmax : ∀ ρ : XiDivisorSupport, (ρ : ℂ).re ≤ (ρ₀ : ℂ).re) (k : XiDivisorSupport) :
    0 ≤ transverseForceTerm ρ₀ k := by
  rw [transverseForceTerm]
  split_ifs with h
  · exact le_refl 0
  · exact div_nonneg (by linarith [hmax k]) (Complex.normSq_nonneg _)

/-- At a point of maximal real part, harmonicity forces every transverse force term to vanish. -/
theorem transverseForceTerm_eq_zero_of_max_of_harmonic {ρ₀ : XiDivisorSupport}
    (hmax : ∀ ρ : XiDivisorSupport, (ρ : ℂ).re ≤ (ρ₀ : ℂ).re)
    (hH : transverseForce ρ₀ = 0) (k : XiDivisorSupport) :
    transverseForceTerm ρ₀ k = 0 := by
  have hsum := summable_transverseForceTerm ρ₀
  have hle : transverseForceTerm ρ₀ k ≤ ∑' m, transverseForceTerm ρ₀ m :=
    hsum.le_tsum k fun m _ => transverseForceTerm_nonneg_of_max hmax m
  rw [← transverseForce, hH] at hle
  exact le_antisymm hle (transverseForceTerm_nonneg_of_max hmax k)

/-- **The maximum principle for the transverse force.**  If the displacement is harmonic at a point
where the real part is maximal, the real part is constant on the whole divisor. -/
theorem re_eq_of_max_of_harmonic {ρ₀ : XiDivisorSupport}
    (hmax : ∀ ρ : XiDivisorSupport, (ρ : ℂ).re ≤ (ρ₀ : ℂ).re)
    (hH : transverseForce ρ₀ = 0) (ρ : XiDivisorSupport) :
    (ρ : ℂ).re = (ρ₀ : ℂ).re := by
  by_cases h : ρ = ρ₀
  · rw [h]
  · have hterm := transverseForceTerm_eq_zero_of_max_of_harmonic hmax hH ρ
    rw [transverseForceTerm, if_neg h] at hterm
    have hne : ((ρ₀ : ℂ)) - ((ρ : ℂ)) ≠ 0 := by
      intro hc
      refine h (Subtype.ext ?_)
      have hEq : ((ρ₀ : ℂ)) = ((ρ : ℂ)) := by linear_combination hc
      exact hEq.symm
    have hpos : 0 < Complex.normSq ((ρ₀ : ℂ) - (ρ : ℂ)) := Complex.normSq_pos.mpr hne
    have hnum : (ρ₀ : ℂ).re - (ρ : ℂ).re = 0 := by
      rcases div_eq_zero_iff.mp hterm with h1 | h2
      · exact h1
      · exact absurd h2 hpos.ne'
    linarith

/-- **Recurrence is not needed in the attained case.**  If the transverse force vanishes at a point
where the real part is maximal, the hypothesis follows — from a single application of the maximum
principle on the complete zero network, with no Liouville argument, no recurrence and no boundedness.
-/
theorem riemannHypothesis_of_harmonic_at_max {ρ₀ : XiDivisorSupport}
    (hmax : ∀ ρ : XiDivisorSupport, (ρ : ℂ).re ≤ (ρ₀ : ℂ).re)
    (hH : transverseForce ρ₀ = 0) :
    RiemannHypothesis :=
  riemannHypothesis_of_forall_re_eq (re_eq_of_max_of_harmonic hmax hH)

/-- Packaged form: harmonicity everywhere plus an attained maximal real part gives the hypothesis. -/
theorem riemannHypothesis_of_transverseForce_zero_of_attained
    (hH : ∀ j : XiDivisorSupport, transverseForce j = 0)
    (hattained : ∃ ρ₀ : XiDivisorSupport, ∀ ρ : XiDivisorSupport,
      (ρ : ℂ).re ≤ (ρ₀ : ℂ).re) :
    RiemannHypothesis := by
  obtain ⟨ρ₀, hmax⟩ := hattained
  exact riemannHypothesis_of_harmonic_at_max hmax (hH ρ₀)

end

end RHTower
