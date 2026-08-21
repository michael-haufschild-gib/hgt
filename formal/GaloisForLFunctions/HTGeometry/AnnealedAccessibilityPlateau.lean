/-
# The annealed accessibility plateau of a fixed shell

The joint angular-phase law of a fixed coefficient shell converges weakly to the shell law times
Haar phase measure, so every bounded upper semicontinuous statistic of the angular-phase pair has
its limiting shell mean bounded by its product integral.  Markov's inequality converts that into a
bound on the limiting shell probability of any event on which the statistic is large; taking the
statistic to be the accessibility potential and the event to be low circuit complexity gives the
all-late-time plateau.

Main results:
* `limsup_integral_anglePhaseLaw_le` — **the annealed bound `(11az)`**.
* `limsup_measureReal_anglePhaseLaw_ge_le` — **`(11ba)`**.
* `limsup_measureReal_anglePhaseLaw_le_of_subset_ge` — **`(11bb)`**.
* `limsup_measureReal_chainAnglePhaseLaw_le_of_subset_ge` — the unconditional chain instance.
-/
import GaloisForLFunctions.HTGeometry.AngularPhasePortmanteau
import GaloisForLFunctions.HTGeometry.AnnealedPortmanteauBound
import GaloisForLFunctions.HTGeometry.PauliChainDephasing

open Filter MeasureTheory Set Topology

noncomputable section

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

section AnglePhase

variable {N D : ℕ} {P : Fin N → Matrix (Fin D) (Fin D) ℂ}

theorem nonempty_coeffSphere (hN : 0 < N) : Nonempty (coeffSphere N) :=
  ⟨⟨EuclideanSpace.single ⟨0, hN⟩ 1, by simp⟩⟩

/-- **`(11az)`.**  The limiting shell mean of an upper semicontinuous angular-phase statistic is at
most its product integral. -/
theorem limsup_integral_anglePhaseLaw_le (hN : 0 < N) (hP : ∀ a, (P a).IsHermitian) (i₀ : Fin D)
    (hRL : ∀ a : Fin D → ℝ, (∑ i, a i = 0) → a ≠ 0 →
      ∀ g : coeffSphere N → ℂ, Measurable g → ∀ C : ℝ, 0 ≤ C → (∀ x, ‖g x‖ ≤ C) →
        Tendsto (fun s : ℝ => ∫ x, g x *
            Complex.exp (-((s * sortedSpectralAction hP a (sphereCoeff x) : ℝ) : ℂ) * Complex.I)
          ∂((volume : Measure (EuclideanSpace ℝ (Fin N))).toSphere)) (cocompact ℝ) (nhds 0))
    {f : coeffSphere N × UnitAddTorus (phaseIndex i₀) → ℝ} (hf : UpperSemicontinuous f)
    (h0 : ∀ x, 0 ≤ f x) {M : ℝ} (hM : ∀ x, f x ≤ M) :
    atTop.limsup (fun t : ℝ => ∫ x, f x ∂(anglePhaseLaw hN hP i₀ t : Measure _))
      ≤ ∫ x, f x ∂(angleProductLaw hN D i₀ : Measure _) := by
  haveI := nonempty_coeffSphere (N := N) hN
  exact limsup_integral_le_of_tendsto_of_upperSemicontinuous
    (tendsto_anglePhaseLaw hN hP i₀ hRL) hf h0 hM

/-- **`(11ba)`.**  The limiting shell probability that the statistic reaches a level is at most its
product integral divided by that level. -/
theorem limsup_measureReal_anglePhaseLaw_ge_le (hN : 0 < N) (hP : ∀ a, (P a).IsHermitian)
    (i₀ : Fin D)
    (hRL : ∀ a : Fin D → ℝ, (∑ i, a i = 0) → a ≠ 0 →
      ∀ g : coeffSphere N → ℂ, Measurable g → ∀ C : ℝ, 0 ≤ C → (∀ x, ‖g x‖ ≤ C) →
        Tendsto (fun s : ℝ => ∫ x, g x *
            Complex.exp (-((s * sortedSpectralAction hP a (sphereCoeff x) : ℝ) : ℂ) * Complex.I)
          ∂((volume : Measure (EuclideanSpace ℝ (Fin N))).toSphere)) (cocompact ℝ) (nhds 0))
    {f : coeffSphere N × UnitAddTorus (phaseIndex i₀) → ℝ} (hf : UpperSemicontinuous f)
    (h0 : ∀ x, 0 ≤ f x) {M : ℝ} (hM : ∀ x, f x ≤ M) {theta : ℝ} (htheta : 0 < theta) :
    atTop.limsup (fun t : ℝ =>
        (anglePhaseLaw hN hP i₀ t : Measure _).real {x | theta ≤ f x})
      ≤ (∫ x, f x ∂(angleProductLaw hN D i₀ : Measure _)) / theta := by
  haveI := nonempty_coeffSphere (N := N) hN
  exact limsup_measureReal_ge_le_of_tendsto
    (tendsto_anglePhaseLaw hN hP i₀ hRL) hf h0 hM htheta

/-- **`(11bb)`.**  The limiting shell probability of an event on which the statistic is at least
`θ` is at most its product integral divided by `θ`.  With `θ = (a/M)^s` and the statistic the
accessibility potential this is the depth-`s` complete-union bound. -/
theorem limsup_measureReal_anglePhaseLaw_le_of_subset_ge (hN : 0 < N)
    (hP : ∀ a, (P a).IsHermitian) (i₀ : Fin D)
    (hRL : ∀ a : Fin D → ℝ, (∑ i, a i = 0) → a ≠ 0 →
      ∀ g : coeffSphere N → ℂ, Measurable g → ∀ C : ℝ, 0 ≤ C → (∀ x, ‖g x‖ ≤ C) →
        Tendsto (fun s : ℝ => ∫ x, g x *
            Complex.exp (-((s * sortedSpectralAction hP a (sphereCoeff x) : ℝ) : ℂ) * Complex.I)
          ∂((volume : Measure (EuclideanSpace ℝ (Fin N))).toSphere)) (cocompact ℝ) (nhds 0))
    {f : coeffSphere N × UnitAddTorus (phaseIndex i₀) → ℝ} (hf : UpperSemicontinuous f)
    (h0 : ∀ x, 0 ≤ f x) {M : ℝ} (hM : ∀ x, f x ≤ M) {theta : ℝ} (htheta : 0 < theta)
    {E : Set (coeffSphere N × UnitAddTorus (phaseIndex i₀))} (hE : ∀ x ∈ E, theta ≤ f x) :
    atTop.limsup (fun t : ℝ => (anglePhaseLaw hN hP i₀ t : Measure _).real E)
      ≤ (∫ x, f x ∂(angleProductLaw hN D i₀ : Measure _)) / theta := by
  haveI := nonempty_coeffSphere (N := N) hN
  exact limsup_measureReal_le_of_subset_ge
    (tendsto_anglePhaseLaw hN hP i₀ hRL) hf h0 hM htheta hE

end AnglePhase


section Chain

/-- **The unconditional chain instance of `(11bb)`.**  For the nearest-neighbour Pauli chain the
dephasing hypothesis is a theorem, so the all-late-time accessibility plateau holds with no
hypothesis on the ensemble. -/
theorem limsup_measureReal_chainAnglePhaseLaw_le_of_subset_ge (k : ℕ)
    (i₀ : Fin (2 ^ (k + 3)))
    (hN : 0 < Fintype.card (ChainLabel (k + 3)))
    {f : coeffSphere (Fintype.card (ChainLabel (k + 3))) × UnitAddTorus (phaseIndex i₀) → ℝ}
    (hf : UpperSemicontinuous f) (h0 : ∀ x, 0 ≤ f x) {M : ℝ} (hM : ∀ x, f x ≤ M)
    {theta : ℝ} (htheta : 0 < theta)
    {E : Set (coeffSphere (Fintype.card (ChainLabel (k + 3))) × UnitAddTorus (phaseIndex i₀))}
    (hE : ∀ x ∈ E, theta ≤ f x) :
    atTop.limsup (fun t : ℝ =>
        (anglePhaseLaw hN (chainPauliFin_isHermitian (k + 3)) i₀ t : Measure _).real E)
      ≤ (∫ x, f x ∂(angleProductLaw hN (2 ^ (k + 3)) i₀ : Measure _)) / theta := by
  refine limsup_measureReal_anglePhaseLaw_le_of_subset_ge hN
    (chainPauliFin_isHermitian (k + 3)) i₀ ?_ hf h0 hM htheta hE
  intro a hsum hne g hg C hC0 hC
  exact tendsto_integral_exp_sortedSpectralAction_zero_pauliChain k a hsum hne g hg hC0 hC

end Chain

end GaloisForLFunctions.HTGeometry

end
