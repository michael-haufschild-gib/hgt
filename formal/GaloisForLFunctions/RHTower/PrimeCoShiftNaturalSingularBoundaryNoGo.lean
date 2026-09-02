import GaloisForLFunctions.RHTower.PrimeCoShiftReflectionOddSingularCohomology

/-!
# Co-shift-natural singular boundary no-go

The singular PCS class requires a genuinely non-square-summable boundary.
This file classifies the remaining source-natural possibility without any
topological, boundedness, closure, or summability assumption.

Off the critical line, the forward and reflected formal ground profiles have
distinct eigenvalues for the multiplicative co-shift by `2`.  Consequently an
invariant boundary submodule containing their difference contains both
profiles separately.  Equivalently, an equivariant source differential cannot
annihilate the reflection-odd class while preserving the forward singular
mode.  Thus every selective co-shift-natural singular PCS boundary is terminal;
a survivor must break co-shift covariance or erase both source modes.
-/

namespace RHTower.PrimeCoShift

open RHTower

noncomputable section

/-- Algebraic multiplicative co-shift on all profiles, with no summability
condition. -/
def primeCoShiftSequence (p : ℕ+) : (ℕ+ → ℂ) →ₗ[ℂ] (ℕ+ → ℂ) where
  toFun x n := x (p * n)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem primeCoShiftSequence_apply
    (p : ℕ+) (x : ℕ+ → ℂ) (n : ℕ+) :
    primeCoShiftSequence p x n = x (p * n) := rfl

/-- Every formal ground profile is an eigenvector for the algebraic co-shift. -/
theorem primeCoShiftSequence_groundFun (p : ℕ+) (s : ℂ) :
    primeCoShiftSequence p (groundFun s) =
      (((p : ℕ) : ℂ) ^ (-s)) • groundFun s := by
  funext n
  simp only [primeCoShiftSequence_apply, groundFun, Pi.smul_apply]
  change ((((p : ℕ) * (n : ℕ) : ℕ) : ℂ) ^ (-s)) = _
  rw [Nat.cast_mul, Complex.natCast_mul_natCast_cpow]
  rfl

/-- The forward and reflected ground profiles have distinct 2-co-shift
eigenvalues away from the critical line. -/
theorem two_groundFun_eigenvalue_ne_reflection
    {s : ℂ} (hline : s.re ≠ 1 / 2) :
    (((2 : ℕ) : ℂ) ^ (-s)) ≠
      (((2 : ℕ) : ℂ) ^ (-(criticalLineReflectionPoint s))) := by
  intro h
  have hnorm := congrArg norm h
  rw [Complex.norm_natCast_cpow_of_pos (by norm_num),
    Complex.norm_natCast_cpow_of_pos (by norm_num)] at hnorm
  simp only [Complex.neg_re] at hnorm
  have hexp : -s.re = -(criticalLineReflectionPoint s).re :=
    (Real.strictMono_rpow_of_base_gt_one
      (by norm_num : (1 : ℝ) < 2)).injective hnorm
  have hweight := criticalLineReflectionPoint_weight s
  apply hline
  linarith

/-- Positive-natural index representing multiplication by `2`. -/
def primeCoShiftTwoIndex : ℕ+ := ⟨2, by omega⟩

/-- A boundary submodule is natural for the 2-co-shift when it is invariant
under the algebraic multiplicative co-shift by `2`. -/
def primeCoShiftTwoNatural (B : Submodule ℂ (ℕ+ → ℂ)) : Prop :=
  ∀ x ∈ B, primeCoShiftSequence primeCoShiftTwoIndex x ∈ B

/-- Off wall, a 2-co-shift-natural boundary containing the reflection-odd
profile must contain the forward profile. -/
theorem groundFun_mem_of_reflectionOdd_mem_of_twoNatural
    (B : Submodule ℂ (ℕ+ → ℂ)) (s : ℂ)
    (hnatural : primeCoShiftTwoNatural B)
    (hline : s.re ≠ 1 / 2)
    (hodd : primeCoShiftReflectionOddGroundFun s ∈ B) :
    groundFun s ∈ B := by
  let a : ℂ := ((2 : ℕ) : ℂ) ^ (-s)
  let b : ℂ := ((2 : ℕ) : ℂ) ^ (-(criticalLineReflectionPoint s))
  have hab : a - b ≠ 0 := sub_ne_zero.mpr
    (two_groundFun_eigenvalue_ne_reflection hline)
  have hshift :
      primeCoShiftSequence primeCoShiftTwoIndex
        (primeCoShiftReflectionOddGroundFun s) ∈ B :=
    hnatural _ hodd
  have hscaled :
      b • primeCoShiftReflectionOddGroundFun s ∈ B := B.smul_mem b hodd
  have hisolate : (a - b) • groundFun s ∈ B := by
    have hsub := B.sub_mem hshift hscaled
    convert hsub using 1
    rw [primeCoShiftReflectionOddGroundFun, map_sub,
      primeCoShiftSequence_groundFun, primeCoShiftSequence_groundFun]
    change (a - b) • groundFun s =
      (a • groundFun s - b • groundFun (criticalLineReflectionPoint s)) -
        b • (groundFun s - groundFun (criticalLineReflectionPoint s))
    module
  have hinv : (a - b)⁻¹ • ((a - b) • groundFun s) ∈ B :=
    B.smul_mem _ hisolate
  simpa [inv_smul_smul₀ hab] using hinv

/-- Off wall, the same boundary also contains the reflected profile. -/
theorem reflectionGroundFun_mem_of_reflectionOdd_mem_of_twoNatural
    (B : Submodule ℂ (ℕ+ → ℂ)) (s : ℂ)
    (hnatural : primeCoShiftTwoNatural B)
    (hline : s.re ≠ 1 / 2)
    (hodd : primeCoShiftReflectionOddGroundFun s ∈ B) :
    groundFun (criticalLineReflectionPoint s) ∈ B := by
  have hs := groundFun_mem_of_reflectionOdd_mem_of_twoNatural
    B s hnatural hline hodd
  have hsub := B.sub_mem hs hodd
  simpa [primeCoShiftReflectionOddGroundFun] using hsub

/-- **Invariant-submodule classification.** Off the critical line, a
2-co-shift-natural boundary absorbs the reflection-odd profile exactly when it
absorbs both distinct singular eigenprofiles. -/
theorem reflectionOdd_mem_twoNatural_iff_both_groundFuns_mem
    (B : Submodule ℂ (ℕ+ → ℂ)) (s : ℂ)
    (hnatural : primeCoShiftTwoNatural B)
    (hline : s.re ≠ 1 / 2) :
    primeCoShiftReflectionOddGroundFun s ∈ B ↔
      groundFun s ∈ B ∧ groundFun (criticalLineReflectionPoint s) ∈ B := by
  constructor
  · intro hodd
    exact
      ⟨groundFun_mem_of_reflectionOdd_mem_of_twoNatural
          B s hnatural hline hodd,
        reflectionGroundFun_mem_of_reflectionOdd_mem_of_twoNatural
          B s hnatural hline hodd⟩
  · rintro ⟨hs, href⟩
    exact B.sub_mem hs href

/-- Equivariance of a source differential makes its range co-shift-natural. -/
theorem range_primeCoShiftTwoNatural_of_equivariant
    {A : Type*} [AddCommGroup A] [Module ℂ A]
    (d0 : A →ₗ[ℂ] (ℕ+ → ℂ)) (U : A →ₗ[ℂ] A)
    (hcov : (primeCoShiftSequence primeCoShiftTwoIndex).comp d0 = d0.comp U) :
    primeCoShiftTwoNatural (LinearMap.range d0) := by
  intro y hy
  obtain ⟨x, rfl⟩ := hy
  refine ⟨U x, ?_⟩
  exact (LinearMap.congr_fun hcov x).symm

/-- **Source-differential classification.** For an arbitrary source module
and arbitrary 2-co-shift-equivariant singular differential, off-wall absorption
of the odd profile is equivalent to absorption of both eigenprofiles. -/
theorem reflectionOdd_mem_sourceNaturalBoundary_iff_both_groundFuns_mem
    {A : Type*} [AddCommGroup A] [Module ℂ A]
    (d0 : A →ₗ[ℂ] (ℕ+ → ℂ)) (U : A →ₗ[ℂ] A)
    (hcov : (primeCoShiftSequence primeCoShiftTwoIndex).comp d0 = d0.comp U)
    (s : ℂ) (hline : s.re ≠ 1 / 2) :
    primeCoShiftReflectionOddGroundFun s ∈ LinearMap.range d0 ↔
      groundFun s ∈ LinearMap.range d0 ∧
        groundFun (criticalLineReflectionPoint s) ∈ LinearMap.range d0 := by
  exact reflectionOdd_mem_twoNatural_iff_both_groundFuns_mem
    (LinearMap.range d0) s
    (range_primeCoShiftTwoNatural_of_equivariant d0 U hcov) hline

/-- **Terminal selective-boundary no-go.** A source-natural singular
differential preserving the forward mode cannot absorb the reflection-odd
profile off the critical line. -/
theorem reflectionOdd_not_mem_sourceNaturalSelectiveBoundary
    {A : Type*} [AddCommGroup A] [Module ℂ A]
    (d0 : A →ₗ[ℂ] (ℕ+ → ℂ)) (U : A →ₗ[ℂ] A)
    (hcov : (primeCoShiftSequence primeCoShiftTwoIndex).comp d0 = d0.comp U)
    (s : ℂ) (hline : s.re ≠ 1 / 2)
    (hselective : groundFun s ∉ LinearMap.range d0) :
    primeCoShiftReflectionOddGroundFun s ∉ LinearMap.range d0 := by
  intro hodd
  exact hselective
    ((reflectionOdd_mem_sourceNaturalBoundary_iff_both_groundFuns_mem
      d0 U hcov s hline).mp hodd).1

/-- Under source covariance and preservation of every forward Xi mode, global
boundary absorption of the reflection-odd PCS profile is exactly RH. -/
theorem forall_xiZero_reflectionOdd_mem_sourceNaturalSelectiveBoundary_iff_RH
    {A : Type*} [AddCommGroup A] [Module ℂ A]
    (d0 : ℂ → A →ₗ[ℂ] (ℕ+ → ℂ)) (U : ℂ → A →ₗ[ℂ] A)
    (hcov : ∀ rho,
      (primeCoShiftSequence primeCoShiftTwoIndex).comp (d0 rho) =
        (d0 rho).comp (U rho))
    (hselective : ∀ rho, xi rho = 0 →
      groundFun rho ∉ LinearMap.range (d0 rho)) :
    (∀ rho, xi rho = 0 →
      primeCoShiftReflectionOddGroundFun rho ∈ LinearMap.range (d0 rho)) ↔
      RiemannHypothesis := by
  rw [riemannHypothesis_iff_xi_zero_re_eq_half]
  constructor
  · intro hboundary rho hrho
    by_contra hline
    exact hselective rho hrho
      (((reflectionOdd_mem_sourceNaturalBoundary_iff_both_groundFuns_mem
        (d0 rho) (U rho) (hcov rho) rho hline).mp
          (hboundary rho hrho)).1)
  · intro hRH rho hrho
    rw [primeCoShiftReflectionOddGroundFun_eq_zero_of_re_eq_half
      (hRH rho hrho)]
    exact Submodule.zero_mem _

end

end RHTower.PrimeCoShift
