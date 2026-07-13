import GaloisForLFunctions.RHTower.BornTemperatureFactorType

/-!
# The fermionic functional-equation boundary

For an involution `sigma` on a residue index set, the operator `1 + sigma` is injective exactly
when every index is fixed.  A nonfixed two-cycle supplies the explicit anti-invariant kernel vector
`e_i - e_(sigma i)`; if every index is fixed, the operator is multiplication by two on the integral
residue module.

Applied to the functional-equation reflection on the Xi zero set, injectivity is exactly RH.  This
is a consumer theorem.  It does not construct a source complex whose anti-invariant cohomology is
contractible, nor a source determinant proving this boundary injective.
-/

namespace RHTower

noncomputable section

/-- The fermionic boundary `1 + sigma` on an integral residue module. -/
def reflectionFermionBoundary {ι : Type*} (σ : ι → ι)
    (f : ι → ℤ) : ι → ℤ :=
  fun i => f i + f (σ i)

/-- Explicit anti-invariant vector supported on the orbit of `i`. -/
def reflectionAntiInvariantWitness {ι : Type*} [DecidableEq ι]
    (σ : ι → ι) (i : ι) : ι → ℤ :=
  fun j => if j = i then 1 else if j = σ i then -1 else 0

theorem reflectionAntiInvariantWitness_ne_zero {ι : Type*} [DecidableEq ι]
    (σ : ι → ι) (i : ι) :
    reflectionAntiInvariantWitness σ i ≠ 0 := by
  intro h
  have hi := congrFun h i
  simp [reflectionAntiInvariantWitness] at hi

/-- Every nonfixed two-cycle produces a nonzero vector killed by `1 + sigma`. -/
theorem reflectionFermionBoundary_witness_eq_zero
    {ι : Type*} [DecidableEq ι] (σ : ι → ι)
    (hσ : Function.Involutive σ) (i : ι) (hne : σ i ≠ i) :
    reflectionFermionBoundary σ (reflectionAntiInvariantWitness σ i) = 0 := by
  funext j
  by_cases hji : j = i
  · subst j
    simp [reflectionFermionBoundary, reflectionAntiInvariantWitness, hne]
  · by_cases hjs : j = σ i
    · subst j
      simp [reflectionFermionBoundary, reflectionAntiInvariantWitness, hne, hσ i]
    · have hσji : σ j ≠ i := by
        intro h
        apply hjs
        rw [← hσ j, h]
      have hσjs : σ j ≠ σ i := by
        intro h
        apply hji
        rw [← hσ j, h, hσ i]
      simp [reflectionFermionBoundary, reflectionAntiInvariantWitness,
        hji, hjs, hσji, hσjs]

/-- The fermionic boundary of an involution is injective exactly when the involution has no free
two-cycle. -/
theorem reflectionFermionBoundary_injective_iff_fixed
    {ι : Type*} [DecidableEq ι] (σ : ι → ι)
    (hσ : Function.Involutive σ) :
    Function.Injective (reflectionFermionBoundary σ) ↔ ∀ i, σ i = i := by
  constructor
  · intro hinj i
    by_contra hne
    have hker := reflectionFermionBoundary_witness_eq_zero σ hσ i hne
    have hz : reflectionFermionBoundary σ (0 : ι → ℤ) = 0 := by
      funext j
      simp [reflectionFermionBoundary]
    have hw := hinj (hker.trans hz.symm)
    exact reflectionAntiInvariantWitness_ne_zero σ i hw
  · intro hfix f g hfg
    funext i
    have hi := congrFun hfg i
    simp [reflectionFermionBoundary, hfix i] at hi
    omega

/-- Xi zeros, with no choice of enumeration or window. -/
def XiZeroPoint := {ρ : ℂ // xi ρ = 0}

/-- Functional-equation reflection on the Xi zero set. -/
def xiZeroReflection (ρ : XiZeroPoint) : XiZeroPoint :=
  ⟨1 - starRingEnd ℂ ρ.1, by
    rw [xi_one_sub, xi_conj, ρ.2, map_zero]⟩

theorem xiZeroReflection_involutive : Function.Involutive xiZeroReflection := by
  intro ρ
  apply Subtype.ext
  change 1 - starRingEnd ℂ (1 - starRingEnd ℂ ρ.1) = ρ.1
  rw [map_sub, map_one, Complex.conj_conj]
  ring

/-- RH is equivalent to injectivity of `1 + J_FE` on the integral residue module of the complete
Xi zero set.  A hypothetical off-line pair is precisely a nonzero anti-invariant kernel vector. -/
theorem riemannHypothesis_iff_reflectionFermionBoundary_injective :
    RiemannHypothesis ↔
      Function.Injective (reflectionFermionBoundary xiZeroReflection) := by
  classical
  rw [reflectionFermionBoundary_injective_iff_fixed
    xiZeroReflection xiZeroReflection_involutive]
  constructor
  · intro hRH ρ
    apply Subtype.ext
    exact (riemannHypothesis_iff_xiZero_reflection_fixed.mp hRH)
      ρ.1 ρ.2
  · intro hfix
    apply riemannHypothesis_iff_xiZero_reflection_fixed.mpr
    intro ρ hρ
    exact congrArg Subtype.val (hfix ⟨ρ, hρ⟩)

end


end RHTower
