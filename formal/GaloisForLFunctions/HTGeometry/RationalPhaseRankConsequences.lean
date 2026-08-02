import GaloisForLFunctions.HTGeometry.GammaFieldRationalPhaseRank
import GaloisForLFunctions.HTGeometry.ObservableFrequencyRank
import GaloisForLFunctions.HTGeometry.BohrProductUniformLimit
import GaloisForLFunctions.HTGeometry.GammaRationalWitness

/-!
# Consequences of the frequency-module form of the law

Two readings of the rational-rank bound.

*Observables.*  A dominated observable of the solution — any continuous, translation-equivariant
reading of it, for instance a Lipschitz function of its values — has no larger frequency group, so
its Bohr–Fourier expansion also carries only finitely many rationally independent frequencies.

*Sharpness.*  A single character has frequency module of rank exactly one, so the bound is attained
and the statement is not vacuous in its rational-rank form.
-/

open Filter Topology

open scoped BoundedContinuousFunction

namespace GaloisForLFunctions

open _root_.HTGeometry

/-- **A dominated observable has finite rational phase rank.** -/
theorem rank_bohrFrequencyModule_le_of_dominated {f g : ℝ →ᵇ ℂ} (h : IsDominatedObservable f g)
    (hg : UniformContinuous fun x => g x) (htbg : HasTotallyBoundedOrbit fun x => g x)
    {K : ℕ} (hK : Module.rank ℤ (bohrHullFrequencies f) ≤ (K : Cardinal)) :
    Module.rank ℚ (bohrFrequencyModule fun x => g x) ≤ (K : Cardinal) :=
  HTGeometry.rank_bohrFrequencyModule_le_of_hull_rank_le hg htbg
    ((rank_le_of_dominated h).trans hK)

/-- The spectrum of a character is its own frequency. -/
theorem bohrSpectrum_expChar (mu : ℝ) : bohrSpectrum (expChar mu) = {mu} := by
  ext lam
  have hfun : expChar mu = bohrExp mu := funext fun t => expChar_eq_bohrExp mu t
  constructor
  · intro hlam
    have hne : bohrCoefficient (expChar mu) lam ≠ 0 := hlam
    rw [hfun, bohrCoefficient_bohrExp] at hne
    by_cases hcase : lam = mu
    · exact hcase
    · rw [if_neg hcase] at hne
      exact absurd rfl hne
  · intro hlam
    have hlam' : lam = mu := hlam
    show bohrCoefficient (expChar mu) lam ≠ 0
    rw [hfun, bohrCoefficient_bohrExp, if_pos hlam']
    exact one_ne_zero

/-- The rational span of a single nonzero real has rank one. -/
theorem rank_span_rat_singleton {mu : ℝ} (hmu : mu ≠ 0) :
    Module.rank ℚ (Submodule.span ℚ ({mu} : Set ℝ)) = 1 := by
  classical
  have hind : LinearIndependent ℚ (fun _ : Fin 1 => mu) := by
    rw [linearIndependent_iff']
    intro s g hsum i hi
    have hsingle : ∑ j ∈ s, g j • mu = g i • mu :=
      Finset.sum_eq_single i (fun j _ hj => absurd (Subsingleton.elim j i) hj)
        (fun h => absurd hi h)
    rw [hsingle, Rat.smul_def] at hsum
    rcases mul_eq_zero.mp hsum with h1 | h2
    · exact_mod_cast h1
    · exact absurd h2 hmu
  have hrange : Set.range (fun _ : Fin 1 => mu) = ({mu} : Set ℝ) := by simp
  have hr := rank_span hind
  rw [hrange] at hr
  rw [hr]
  simp

/-- **Sharpness.**  A nontrivial character has frequency module of rank exactly one. -/
theorem rank_bohrFrequencyModule_expChar {mu : ℝ} (hmu : mu ≠ 0) :
    Module.rank ℚ (bohrFrequencyModule (expChar mu)) = 1 := by
  rw [bohrFrequencyModule, bohrSpectrum_expChar]
  exact rank_span_rat_singleton hmu

/-- The exponential line restricted to a vertical line is a multiple of a character. -/
theorem expLineBC_eq_const_mul_expChar (μ σ : ℝ) :
    (fun x : ℝ => (expLineBC μ σ x : ℂ))
      = fun x : ℝ => ((Real.exp (μ * σ) : ℝ) : ℂ) * expChar μ x := by
  funext x
  show expLine μ ((σ : ℂ) + (x : ℂ) * Complex.I)
      = ((Real.exp (μ * σ) : ℝ) : ℂ) * expChar μ x
  rw [expLine, expChar, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- **The spectrum of the exponential line is its frequency.** -/
theorem bohrSpectrum_expLineBC (μ σ : ℝ) :
    bohrSpectrum (fun x : ℝ => (expLineBC μ σ x : ℂ)) = {μ} := by
  have hc : ((Real.exp (μ * σ) : ℝ) : ℂ) ≠ 0 := by
    have : (0 : ℝ) < Real.exp (μ * σ) := Real.exp_pos _
    exact_mod_cast ne_of_gt this
  ext lam
  have hcoeff : bohrCoefficient (fun x : ℝ => (expLineBC μ σ x : ℂ)) lam
      = ((Real.exp (μ * σ) : ℝ) : ℂ) * bohrCoefficient (expChar μ) lam := by
    rw [expLineBC_eq_const_mul_expChar]
    exact bohrCoefficient_const_mul _ (continuous_expChar μ) (isBohrAlmostPeriodic_expChar μ) lam
  constructor
  · intro hlam
    have hne : bohrCoefficient (fun x : ℝ => (expLineBC μ σ x : ℂ)) lam ≠ 0 := hlam
    rw [hcoeff] at hne
    have hne' : bohrCoefficient (expChar μ) lam ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at hne
      exact hne rfl
    have : lam ∈ bohrSpectrum (expChar μ) := hne'
    rwa [bohrSpectrum_expChar] at this
  · intro hlam
    have hmem : lam ∈ bohrSpectrum (expChar μ) := by
      rw [bohrSpectrum_expChar]
      exact hlam
    show bohrCoefficient (fun x : ℝ => (expLineBC μ σ x : ℂ)) lam ≠ 0
    rw [hcoeff]
    exact mul_ne_zero hc hmem

/-- **The law's rational bound is attained.**  The exponential line — a witness of the finite phase
law over Gamma-jet data — has frequency module of rank exactly one. -/
theorem rank_bohrFrequencyModule_expLineBC {μ : ℝ} (σ : ℝ) (hμ : μ ≠ 0) :
    Module.rank ℚ (bohrFrequencyModule fun x : ℝ => (expLineBC μ σ x : ℂ)) = 1 := by
  rw [bohrFrequencyModule, bohrSpectrum_expLineBC]
  exact rank_span_rat_singleton hμ

end GaloisForLFunctions
