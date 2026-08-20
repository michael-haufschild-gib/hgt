import GaloisForLFunctions.HTGeometry.AllDepthClassDivisor
import GaloisForLFunctions.HTGeometry.AllDepthCompleteness
import GaloisForLFunctions.HTGeometry.TripticBoundaryPoleClasses
import GaloisForLFunctions.HTGeometry.TripticOrbitalDivisorClassFunction

/-!
# The pair-face signature is a finite differential divisor

The pair-face signature of a member of the all-depth mixed-constraint class is a class function on
`ℂ` modulo the period group of its pair, with finitely many nonzero classes and bounded order.  A
member of a smaller class contributes nothing to a pair containing a deleted direction.

* `pairSig` and its invariance, finiteness and order bound;
* **`pairSig_eq_zero_of_mixedConstGermSet_erase`** — a member of `Q_(s\{k})` has trivial signature
  at every pair through `k`.
-/

open Filter Set Topology Complex
open scoped Differential BigOperators

namespace GaloisForLFunctions

open Bottcher HTGeometry

noncomputable section

variable {ι : Type} [DecidableEq ι]

/-- The pair-face signature of a member of the all-depth class, at an ordered pair. -/
def pairSig (τ : ι → ℂ) (s : Finset ι) (f : ℂ → ℂ) (i j : ι) (ℓ : ℤ) (p : ℂ) : ℂ :=
  additiveOrbitalDivisorAt (pairFaceWitnessFun τ s i j f) (τ i) p ℓ

section

variable (τ : ι → ℂ)
  (s : Finset ι) {i j : ι} (hij : i ≠ j) (hi : i ∈ s) (hj : j ∈ s)
  {Cst : ℂ} {f : ℂ → ℂ} (hmero : MeromorphicOn f (Set.univ : Set ℂ))
  (hper : PeriodicOneGerm f) (hmixed : MixedConstGermSet τ s f Cst)

include hij hi hj hmero hper hmixed

/-- **The signature is a class function modulo the pair period group.** -/
theorem divInvariant_pairSig {ℓ : ℤ} (hℓ : ℓ < 0) :
    DivInvariant (tripticPeriodGroup (τ j) (τ i)) (pairSig τ s f i j ℓ) := by
  intro p g hg
  obtain ⟨u, v, w, hg'⟩ := hg
  have hWmero : MeromorphicOn (pairFaceWitnessFun τ s i j f) (Set.univ : Set ℂ) :=
    meromorphicOn_diffCube τ _ hmero
  have hWper : PeriodicOneGerm (pairFaceWitnessFun τ s i j f) :=
    periodicOneGerm_diffCube τ _ hper
  have hcls := additiveOrbitalDivisorAt_classFunction hWmero hWper
    (mixedConstGerm_pairFaceWitnessFun τ s hij hi hj hmixed) p hℓ u v w
  show additiveOrbitalDivisorAt (pairFaceWitnessFun τ s i j f) (τ i) (p + g) ℓ
    = additiveOrbitalDivisorAt (pairFaceWitnessFun τ s i j f) (τ i) p ℓ
  rw [hg', ← hcls]
  congr 1
  ring

/-- **The signature has finitely many nonzero classes.** -/
theorem divFiniteClasses_pairSig (hτj : 0 < (τ j).im) {ℓ : ℤ} (hℓ : ℓ < 0) :
    DivFiniteClasses (tripticPeriodGroup (τ j) (τ i)) (pairSig τ s f i j ℓ) := by
  have hWmero : MeromorphicOn (pairFaceWitnessFun τ s i j f) (Set.univ : Set ℂ) :=
    meromorphicOn_diffCube τ _ hmero
  have hWper : PeriodicOneGerm (pairFaceWitnessFun τ s i j f) :=
    periodicOneGerm_diffCube τ _ hper
  obtain ⟨S, hS⟩ := exists_finset_orbitalDivisor_classes hWmero hWper
    (mixedConstGerm_pairFaceWitnessFun τ s hij hi hj hmixed) hτj hℓ
  exact ⟨S, hS⟩

/-- **The signature has bounded order.** -/
theorem exists_order_bound_pairSig (hτj : 0 < (τ j).im) :
    ∃ N : ℕ, ∀ (ℓ : ℤ), ℓ < -(N : ℤ) → ∀ p : ℂ, pairSig τ s f i j ℓ p = 0 := by
  have hWmero : MeromorphicOn (pairFaceWitnessFun τ s i j f) (Set.univ : Set ℂ) :=
    meromorphicOn_diffCube τ _ hmero
  have hWper : PeriodicOneGerm (pairFaceWitnessFun τ s i j f) :=
    periodicOneGerm_diffCube τ _ hper
  obtain ⟨L, hL⟩ := exists_orderBound_boundary hWmero hWper
    (mixedConstGerm_pairFaceWitnessFun τ s hij hi hj hmixed)
    (linearIndependent_one_of_im_pos hτj)
  refine ⟨(-L).toNat, fun ℓ hℓ p => ?_⟩
  have hbnd : (-L) ≤ (((-L).toNat : ℕ) : ℤ) := Int.self_le_toNat _
  rw [pairSig, additiveOrbitalDivisorAt]
  refine finsum_eq_zero_of_forall_eq_zero fun m => ?_
  exact hL _ _ (by omega)

end

/-! ## A member of a smaller class has no signature through a deleted direction -/

/-- **A member of `Q_(s\{k})` has trivial signature at every pair through `k`.** -/
theorem pairSig_eq_zero_of_mixedConstGermSet_erase (τ : ι → ℂ) (s : Finset ι) {k i : ι}
    (hik : i ≠ k) (hi : i ∈ s) {c₀ : ℂ} {f : ℂ → ℂ}
    (hmero : MeromorphicOn f (Set.univ : Set ℂ))
    (hE : MixedConstGermSet τ (s \ {k}) f c₀) {ℓ : ℤ} (hℓ : ℓ < 0) (p : ℂ) :
    pairSig τ s f i k ℓ p = 0 := by
  classical
  have hstep : HTGeometry.shiftDiffFun (τ i) (pairFaceWitnessFun τ s i k f)
      = bottomWitnessFun τ s k f := shiftDiffFun_pairFaceWitnessFun τ s hik hi f
  have hVmero : MeromorphicOn (bottomWitnessFun τ s k f) (Set.univ : Set ℂ) :=
    meromorphicOn_diffCube τ _ hmero
  have hzero : ∀ q : ℂ, laurentCoeff (bottomWitnessFun τ s k f) q ℓ = 0 := by
    intro q
    have hgerm : bottomWitnessFun τ s k f =ᶠ[𝓝[≠] q] fun _ : ℂ => c₀ := by
      filter_upwards [hE q] with w hw
      exact hw
    rw [laurentCoeff_congr (hVmero q (Set.mem_univ q)) hgerm ℓ]
    exact laurentCoeff_eq_zero_of_analyticAt analyticAt_const hℓ
  rw [pairSig, additiveOrbitalDivisorAt]
  refine finsum_eq_zero_of_forall_eq_zero fun m => ?_
  have := hzero (p + (m : ℂ) * τ i)
  rw [← hstep] at this
  exact this

end

end GaloisForLFunctions
