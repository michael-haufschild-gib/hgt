/-
# Recurrence of a unitary orbit to its own seed

The overlap of the evolved state with its seed is the phase average of the occupation
probabilities.  When the spectrum is maximally projective the anchored gap frequencies are
rationally independent, so Kronecker recurrence returns every phase to one at arbitrarily late
times, and the overlap returns to one.

Main results:
* `linearIndependent_rat_projectiveFrequency` — maximal projectivity gives rationally independent
  anchored gaps.
* `exists_late_seed_recurrence` — **the orbit returns to its seed at arbitrarily late times**.
-/
import GaloisForLFunctions.HTGeometry.EvolvedStateBundlePairing
import GaloisForLFunctions.HTGeometry.ClockPhaseEvolutionBridge
import GaloisForLFunctions.HTGeometry.KroneckerApproxRecurrence
import GaloisForLFunctions.HTGeometry.FiniteSpectralHaarRecurrenceLaw

open Matrix Complex UnitAddTorus ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

/-- **Maximal projectivity gives rationally independent anchored gaps.** -/
theorem linearIndependent_rat_projectiveFrequency {I : Type*} [Fintype I] [DecidableEq I]
    (energy : I → ℝ) (hmax : MaximallyProjectiveEnergy energy) (ref : I) :
    LinearIndependent ℚ (projectiveFrequency energy ref) := by
  classical
  refine (LinearIndependent.iff_fractionRing ℤ ℚ).mp ?_
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hzero := maximallyProjectiveEnergy_projectiveFrequency_independent energy hmax ref g ?_
  · exact fun i => congrFun hzero i
  · rw [finiteTorusCharacterDetuning]
    simpa using hg

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- **The orbit returns to its seed at arbitrarily late times.** -/
theorem exists_late_seed_recurrence {H : Matrix α α ℂ} {e : α → α → ℂ} {lam : α → ℝ}
    (heb : IsOrthoEigenBasis H e lam) (hinj : Function.Injective lam)
    (hmax : MaximallyProjectiveEnergy lam) (i₀ : α)
    (Om : α → ℂ) (hOm : finiteComplexInner Om Om = 1)
    {ρ : ℝ} (hρ : 0 < ρ) (A : ℝ) :
    ∃ s : ℝ, A < s ∧ 1 - ρ ≤ ‖finiteComplexInner (unitaryEvolution H s *ᵥ Om) Om‖ := by
  classical
  obtain ⟨t, hA, hclose⟩ := GaloisForLFunctions.kronecker_approx_atTop
    (linearIndependent_rat_projectiveFrequency lam hmax i₀) (fun _ => (0 : ℝ)) hρ A
  refine ⟨t, hA, ?_⟩
  rw [norm_finiteComplexInner_unitaryEvolution_eq heb hinj Om Om i₀ t]
  obtain ⟨p, hpdef⟩ : ∃ p : α → ℝ, p = fun j => ‖finiteComplexInner (e j) Om‖ ^ (2 : ℕ) := ⟨_, rfl⟩
  have hpnn : ∀ j, 0 ≤ p j := by intro j; rw [hpdef]; positivity
  have hpsum : ∑ j, p j = 1 := by
    rw [hpdef]
    exact sum_normSq_eigenCoords heb Om hOm
  have hweight : ∀ j, spectralCrossWeight lam H Om Om j = ((p j : ℝ) : ℂ) := by
    intro j
    rw [spectralCrossWeight_eq heb hinj Om Om j, hpdef, ← Complex.normSq_eq_conj_mul_self]
    show ((Complex.normSq (finiteComplexInner (e j) Om) : ℝ) : ℂ)
      = ((‖finiteComplexInner (e j) Om‖ ^ (2 : ℕ) : ℝ) : ℂ)
    rw [Complex.sq_norm]
  have hphase : ∀ j : α, ‖Complex.exp (Complex.I * ((t : ℂ) * ((lam j : ℂ) - (lam i₀ : ℂ))))
      - 1‖ ≤ ρ := by
    intro j
    by_cases hj : j = i₀
    · subst hj
      simp [le_of_lt hρ]
    · have hk := hclose ⟨j, hj⟩
      have hrw : Complex.exp (Complex.I * ((t : ℂ) * ((lam j : ℂ) - (lam i₀ : ℂ))))
          = GaloisForLFunctions.expChar (projectiveFrequency lam i₀ ⟨j, hj⟩) t := by
        rw [GaloisForLFunctions.expChar, projectiveFrequency]
        congr 1
        push_cast
        ring
      rw [hrw]
      have hone : Complex.exp (((0 : ℝ) : ℂ) * Complex.I) = 1 := by simp
      rw [← hone]
      exact le_of_lt hk
  obtain ⟨c, hcdef⟩ : ∃ c : α → ℂ,
      c = fun j => conj (Complex.exp (Complex.I * ((t : ℂ) * ((lam j : ℂ) - (lam i₀ : ℂ))))) :=
    ⟨_, rfl⟩
  have hcbound : ∀ j, ‖c j - 1‖ ≤ ρ := by
    intro j
    rw [hcdef]
    show ‖conj (Complex.exp (Complex.I * ((t : ℂ) * ((lam j : ℂ) - (lam i₀ : ℂ))))) - 1‖ ≤ ρ
    have hconj : conj (Complex.exp (Complex.I * ((t : ℂ) * ((lam j : ℂ) - (lam i₀ : ℂ)))))
        - 1 = conj (Complex.exp (Complex.I * ((t : ℂ) * ((lam j : ℂ) - (lam i₀ : ℂ)))) - 1) := by
      rw [map_sub, map_one]
    rw [hconj, Complex.norm_conj]
    exact hphase j
  have hpair : bundlePairing (spectralCrossWeight lam H Om Om)
      (torusSection i₀ (evolvedPhasePoint lam i₀ t))
      = ∑ j, c j * ((p j : ℝ) : ℂ) := by
    rw [bundlePairing, hcdef]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mFourier_torusSection_evolvedPhasePoint, hweight j]
  rw [hpair]
  have h1 : ∑ j, ((p j : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_sum, hpsum]
    norm_num
  have hsplit : (∑ j, c j * ((p j : ℝ) : ℂ))
      = 1 + ∑ j, (c j - 1) * ((p j : ℝ) : ℂ) := by
    calc (∑ j, c j * ((p j : ℝ) : ℂ))
        = ∑ j, (((p j : ℝ) : ℂ) + (c j - 1) * ((p j : ℝ) : ℂ)) :=
          Finset.sum_congr rfl fun j _ => by ring
      _ = (∑ j, ((p j : ℝ) : ℂ)) + ∑ j, (c j - 1) * ((p j : ℝ) : ℂ) := Finset.sum_add_distrib
      _ = 1 + ∑ j, (c j - 1) * ((p j : ℝ) : ℂ) := by rw [h1]
  rw [hsplit]
  have hbound : ‖∑ j, (c j - 1) * ((p j : ℝ) : ℂ)‖ ≤ ρ := by
    refine le_trans (norm_sum_le _ _) ?_
    have hterm : ∀ j ∈ (Finset.univ : Finset α),
        ‖(c j - 1) * ((p j : ℝ) : ℂ)‖ ≤ ρ * p j := by
      intro j _
      rw [norm_mul]
      have hpn : ‖((p j : ℝ) : ℂ)‖ = p j := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hpnn j)]
      rw [hpn]
      exact mul_le_mul_of_nonneg_right (hcbound j) (hpnn j)
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [← Finset.mul_sum, hpsum, mul_one]
  have hne := norm_sub_norm_le (1 : ℂ) (-(∑ j, (c j - 1) * ((p j : ℝ) : ℂ)))
  simp only [sub_neg_eq_add, norm_one, norm_neg] at hne
  linarith [hne, hbound]

end GaloisForLFunctions.HTGeometry

end
