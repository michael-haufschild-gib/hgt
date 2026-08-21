import GaloisForLFunctions.RHTower.DirichletCharacterPrimitiveZeroDensityTransport
import GaloisForLFunctions.RHTower.DirichletCharacterPrimitiveConductorDivisor

/-!
# Finite primitive-conductor family transport for positive zero-density windows

For a fixed ambient modulus `n + 1`, every nonprincipal character has a
canonical primitive nonprincipal source at a literal divisor conductor.  This
file builds that finite divisor-indexed target family, proves the source map
injective using its closed change-level left inverse, and transports the
positive-window zero count into the family sum.

The resulting inequality is the finite all-characters-to-primitive-divisors
accounting step in Chen--Gupta--Li Section 12.  It deliberately stops before
the subsequent source analytic zero-density estimate.
-/

noncomputable section

namespace RHTower

/-- A primitive nonprincipal Dirichlet character at a literal divisor of the
ambient modulus `n + 1`. -/
structure CGLPrimitiveNonprincipalCharacterAtDivisor
    {n : ℕ} (d : (n + 1).divisors) where
  character : DirichletCharacter ℂ d.1
  nonprincipal : character ≠ 1
  primitive : DirichletCharacter.IsPrimitive character

noncomputable instance cglPrimitiveNonprincipalCharacterAtDivisor_fintype
    {n : ℕ} (d : (n + 1).divisors) :
    Fintype (CGLPrimitiveNonprincipalCharacterAtDivisor d) :=
  Fintype.ofInjective CGLPrimitiveNonprincipalCharacterAtDivisor.character (by
    intro x y hxy
    cases x
    cases y
    cases hxy
    rfl)

/-- The divisor carrier itself proves its value nonzero, so completed
Dirichlet `L`-functions at literal divisor conductors need no caller premise. -/
instance cglNeZero_divisor
    (n : ℕ) (d : (n + 1).divisors) : NeZero d.1 :=
  ⟨by
    intro hdzero
    rcases (Nat.mem_divisors.mp d.2).1 with ⟨k, hk⟩
    have hqzero : n + 1 = 0 := by
      calc
        n + 1 = d.1 * k := hk
        _ = 0 := by rw [hdzero, zero_mul]
    exact (Nat.mem_divisors.mp d.2).2 hqzero⟩

/-- Map an ambient nonprincipal character to its canonical primitive
nonprincipal character at the literal conductor divisor. -/
noncomputable def cglPrimitiveConductorDivisorFamilyIndex
    (n : ℕ) (χ : NonprincipalDirichletCharacter n) :
    Sigma (CGLPrimitiveNonprincipalCharacterAtDivisor (n := n)) :=
  ⟨cglPrimitiveConductorDivisor n χ,
    ⟨cglPrimitiveCharacterAtConductorDivisor n χ,
      cglPrimitiveCharacterAtConductorDivisor_nonprincipal n χ,
      cglPrimitiveCharacterAtConductorDivisor_primitive n χ⟩⟩

/-- Recover an ambient nonprincipal character by changing level from a
primitive divisor-family member. -/
noncomputable def cglInducedNonprincipalCharacterOfDivisorFamilyIndex
    (n : ℕ)
    (x : Sigma (CGLPrimitiveNonprincipalCharacterAtDivisor (n := n))) :
    NonprincipalDirichletCharacter n := by
  refine ⟨DirichletCharacter.changeLevel (Nat.mem_divisors.mp x.1.2).1 x.2.character, ?_⟩
  intro hprincipal
  have hsource : x.2.character = 1 :=
    (DirichletCharacter.changeLevel_eq_one_iff (χ := x.2.character)
      (Nat.mem_divisors.mp x.1.2).1).mp hprincipal
  exact x.2.nonprincipal hsource

/-- Inducing the canonical primitive divisor-family image recovers the
original ambient character exactly. -/
theorem cglInducedNonprincipalCharacterOfDivisorFamilyIndex_apply
    (n : ℕ) (χ : NonprincipalDirichletCharacter n) :
    cglInducedNonprincipalCharacterOfDivisorFamilyIndex n
      (cglPrimitiveConductorDivisorFamilyIndex n χ) = χ := by
  apply Subtype.ext
  simp only [cglInducedNonprincipalCharacterOfDivisorFamilyIndex,
    cglPrimitiveConductorDivisorFamilyIndex,
    cglPrimitiveCharacterAtConductorDivisor]
  exact (cglPrimitiveCharacterReduction n χ).induced_eq

/-- The canonical map from ambient nonprincipal characters to primitive
divisor-family members is injective. -/
theorem cglPrimitiveConductorDivisorFamilyIndex_injective
    (n : ℕ) : Function.Injective (cglPrimitiveConductorDivisorFamilyIndex n) := by
  intro χ₁ χ₂ h
  calc
    χ₁ = cglInducedNonprincipalCharacterOfDivisorFamilyIndex n
        (cglPrimitiveConductorDivisorFamilyIndex n χ₁) :=
      (cglInducedNonprincipalCharacterOfDivisorFamilyIndex_apply n χ₁).symm
    _ = cglInducedNonprincipalCharacterOfDivisorFamilyIndex n
        (cglPrimitiveConductorDivisorFamilyIndex n χ₂) := congrArg _ h
    _ = χ₂ := cglInducedNonprincipalCharacterOfDivisorFamilyIndex_apply n χ₂

/-- The completed-`L` zero count in a certified positive window for one
primitive character at one literal divisor conductor. -/
def cglPrimitiveDivisorCompletedWindowCount
    {n : ℕ} (d : (n + 1).divisors)
    (ψ : CGLPrimitiveNonprincipalCharacterAtDivisor d)
    (W : CGLPositiveZeroDensityVerticalWindow) : ℝ :=
  (↑(∑ᶠ z, MeromorphicOn.divisor (DirichletCharacter.completedLFunction ψ.character)
    W.carrier z) : ℝ)

/-- The canonical primitive completed function used in characterwise
reduction has exactly the divisor-family count of its mapped image. -/
theorem cglPrimitiveConductorDivisorFamilyIndex_count_eq
    (n : ℕ) (χ : NonprincipalDirichletCharacter n)
    (W : CGLPositiveZeroDensityVerticalWindow) :
    cglPrimitiveCompletedLFunctionZeroDensityVerticalWindowCount n χ W =
      cglPrimitiveDivisorCompletedWindowCount
        (cglPrimitiveConductorDivisorFamilyIndex n χ).1
        (cglPrimitiveConductorDivisorFamilyIndex n χ).2 W := by
  unfold cglPrimitiveCompletedLFunctionZeroDensityVerticalWindowCount
    cglPrimitiveCompletedLFunction cglPrimitiveDivisorCompletedWindowCount
    cglPrimitiveConductorDivisorFamilyIndex
    cglPrimitiveCharacterAtConductorDivisor
  rfl

/-- Every literal primitive divisor-family zero count is nonnegative. -/
theorem cglPrimitiveDivisorCompletedWindowCount_nonneg
    {n : ℕ} (d : (n + 1).divisors)
    (ψ : CGLPrimitiveNonprincipalCharacterAtDivisor d)
    (W : CGLPositiveZeroDensityVerticalWindow) :
    0 ≤ cglPrimitiveDivisorCompletedWindowCount d ψ W := by
  unfold cglPrimitiveDivisorCompletedWindowCount
  have hanalytic : AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction ψ.character) Set.univ :=
    (DirichletCharacter.differentiable_completedLFunction ψ.nonprincipal).differentiableOn.analyticOnNhd
      isOpen_univ
  exact_mod_cast finsum_nonneg fun z =>
    MeromorphicOn.AnalyticOnNhd.divisor_nonneg
      (hanalytic.mono (Set.subset_univ W.carrier)) z

/-- The complete finite primitive nonprincipal divisor family at ambient
modulus `n + 1`. -/
abbrev CGLPrimitiveDivisorFamily (n : ℕ) :=
  Sigma (CGLPrimitiveNonprincipalCharacterAtDivisor (n := n))

/-- Aggregate positive-window zero count over every primitive nonprincipal
character at every divisor conductor of the ambient modulus. -/
noncomputable def cglPrimitiveDivisorFamilyWindowCount
    (n : ℕ) (W : CGLPositiveZeroDensityVerticalWindow) : ℝ :=
  ∑ x : CGLPrimitiveDivisorFamily n,
    cglPrimitiveDivisorCompletedWindowCount x.1 x.2 W

/-- The full ambient nonprincipal-family zero count in every certified
positive centered window is bounded by the literal primitive-divisor family
count.  This is a closed finite reindexing inequality; it contains no
zero-density estimate. -/
theorem cgl_nonprincipalFamily_zeroDensityVerticalWindowCount_le_primitiveDivisorFamily
    (n : ℕ) (W : CGLPositiveZeroDensityVerticalWindow) :
    (∑ χ : NonprincipalDirichletCharacter n,
      completedLFunctionZeroDensityVerticalWindowCount n χ W.sigma W.center W.halfWidth) ≤
      cglPrimitiveDivisorFamilyWindowCount n W := by
  classical
  let F : CGLPrimitiveDivisorFamily n → ℝ :=
    fun x => cglPrimitiveDivisorCompletedWindowCount x.1 x.2 W
  let f : NonprincipalDirichletCharacter n → CGLPrimitiveDivisorFamily n :=
    cglPrimitiveConductorDivisorFamilyIndex n
  have hf : Function.Injective f := cglPrimitiveConductorDivisorFamilyIndex_injective n
  calc
    (∑ χ : NonprincipalDirichletCharacter n,
      completedLFunctionZeroDensityVerticalWindowCount n χ W.sigma W.center W.halfWidth) =
        ∑ χ : NonprincipalDirichletCharacter n, F (f χ) := by
      apply Finset.sum_congr rfl
      intro χ hχ
      rw [← cglPrimitiveCompleted_zeroDensityVerticalWindowCount_eq_input n χ W,
        cglPrimitiveConductorDivisorFamilyIndex_count_eq]
    _ = ∑ x ∈ (Finset.univ.image f), F x := by
      symm
      rw [Finset.sum_image]
      intro a ha b hb hab
      exact hf hab
    _ ≤ ∑ x : CGLPrimitiveDivisorFamily n, F x := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro x hx
        exact Finset.mem_univ x
      · intro x hx hnot
        exact cglPrimitiveDivisorCompletedWindowCount_nonneg x.1 x.2 W

end RHTower
