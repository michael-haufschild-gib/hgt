import GaloisForLFunctions.RHTower.XiAutomorphicRealCoronaSmoothness
import GaloisForLFunctions.RHTower.ZetaXiZeroCorrespondence

/-!
# Higher-degree completed-zeta powers have nonsmooth Real corona

For every positive integer `d`, the completed function `xi(s)^d` is the degree-`d` isobaric power
of completed zeta.  Its zero divisor has every Xi zero with multiplicity multiplied by `d`, but
its underlying upper and lower sectors are literally the same sets as for Xi.  This supplies
actual higher-degree completed examples for the endpoint-holomorphic P3 classification, without
replacing automorphic data by an abstract zero-set interface.
-/

noncomputable section

open Complex Set

namespace RHTower

open GaloisForLFunctions.RHTower

/-- Positive-degree isobaric power of the completed Riemann Xi function. -/
def xiPowerCompletion (d : ℕ) (s : ℂ) : ℂ := xi s ^ d

theorem xiPowerCompletion_zero_iff {d : ℕ} (hd : d ≠ 0) (s : ℂ) :
    xiPowerCompletion d s = 0 ↔ xi s = 0 := by
  constructor
  · intro hzero
    by_contra hxi
    exact pow_ne_zero d hxi hzero
  · intro hxi
    simp [xiPowerCompletion, hxi, hd]

/-- **The Riemann hypothesis reads off any positive isobaric power.**  Taking a positive power
neither creates nor destroys zeros, so the critical-line statement for `ξ^d` is RH itself, for every
`d ≠ 0`. -/
theorem riemannHypothesis_iff_xiPowerCompletion_zero_re_eq_half {d : ℕ} (hd : d ≠ 0) :
    RiemannHypothesis ↔ ∀ s : ℂ, xiPowerCompletion d s = 0 → s.re = 1 / 2 := by
  rw [riemannHypothesis_iff_xi_zero_re_eq_half]
  constructor
  · intro h s hs
    exact h s ((xiPowerCompletion_zero_iff hd s).mp hs)
  · intro h s hs
    exact h s ((xiPowerCompletion_zero_iff hd s).mpr hs)

theorem xiPowerCompletion_one_sub (d : ℕ) (s : ℂ) :
    xiPowerCompletion d (1 - s) = xiPowerCompletion d s := by
  simp [xiPowerCompletion, xi_one_sub]

/-- Compactified positive-height zero sector of the degree-`d` completed-zeta power. -/
def xiPowerCompactifiedUpperZeroSector (d : ℕ) : Set ℂ :=
  {w | ∃ rho : ℂ, xiPowerCompletion d rho = 0 ∧ 0 < rho.im ∧
    w = xiCenteredReciprocal rho}

/-- Compactified negative-height zero sector of the degree-`d` completed-zeta power. -/
def xiPowerCompactifiedLowerZeroSector (d : ℕ) : Set ℂ :=
  {w | ∃ rho : ℂ, xiPowerCompletion d rho = 0 ∧ rho.im < 0 ∧
    w = xiCenteredReciprocal rho}

theorem xiPowerCompactifiedUpperZeroSector_eq
    {d : ℕ} (hd : d ≠ 0) :
    xiPowerCompactifiedUpperZeroSector d = xiCompactifiedUpperZeroSector := by
  ext w
  constructor
  · rintro ⟨rho, hrho, him, rfl⟩
    exact ⟨rho, (xiPowerCompletion_zero_iff hd rho).mp hrho, him, rfl⟩
  · rintro ⟨rho, hrho, him, rfl⟩
    exact ⟨rho, (xiPowerCompletion_zero_iff hd rho).mpr hrho, him, rfl⟩

theorem xiPowerCompactifiedLowerZeroSector_eq
    {d : ℕ} (hd : d ≠ 0) :
    xiPowerCompactifiedLowerZeroSector d = xiCompactifiedLowerZeroSector := by
  ext w
  constructor
  · rintro ⟨rho, hrho, him, rfl⟩
    exact ⟨rho, (xiPowerCompletion_zero_iff hd rho).mp hrho, him, rfl⟩
  · rintro ⟨rho, hrho, him, rfl⟩
    exact ⟨rho, (xiPowerCompletion_zero_iff hd rho).mpr hrho, him, rfl⟩

@[simp] theorem xiPowerCompactifiedUpperZeroSector_zero :
    xiPowerCompactifiedUpperZeroSector 0 = ∅ := by
  ext w
  simp [xiPowerCompactifiedUpperZeroSector, xiPowerCompletion]

@[simp] theorem xiPowerCompactifiedLowerZeroSector_zero :
    xiPowerCompactifiedLowerZeroSector 0 = ∅ := by
  ext w
  simp [xiPowerCompactifiedLowerZeroSector, xiPowerCompletion]

/-- Negation preserves the compactified divisor for every degree, including the empty degree-zero
divisor. -/
theorem xiPowerCompactifiedZeroSectors_neg_mapsTo_all (d : ℕ) :
    MapsTo (-·)
      (xiPowerCompactifiedUpperZeroSector d ∪
        xiPowerCompactifiedLowerZeroSector d)
      (xiPowerCompactifiedUpperZeroSector d ∪
        xiPowerCompactifiedLowerZeroSector d) := by
  by_cases hd : d = 0
  · subst d
    simp
  · rw [xiPowerCompactifiedUpperZeroSector_eq hd,
      xiPowerCompactifiedLowerZeroSector_eq hd]
    exact xiCompactifiedZeroSectors_neg_mapsTo

/-- Holomorphic reflection for the entire completed-zeta power family, including degree zero. -/
def xiPowerAllDegreeHolomorphicReflection (d : ℕ) :
    HolomorphicDivisorReflection Set.univ
      (xiPowerCompactifiedUpperZeroSector d ∪
        xiPowerCompactifiedLowerZeroSector d) :=
  negationHolomorphicDivisorReflection _
    (xiPowerCompactifiedZeroSectors_neg_mapsTo_all d)

theorem xiPowerCompactifiedZeroSectors_neg_mapsTo
    {d : ℕ} (hd : d ≠ 0) :
    MapsTo (-·)
      (xiPowerCompactifiedUpperZeroSector d ∪
        xiPowerCompactifiedLowerZeroSector d)
      (xiPowerCompactifiedUpperZeroSector d ∪
        xiPowerCompactifiedLowerZeroSector d) := by
  rw [xiPowerCompactifiedUpperZeroSector_eq hd,
    xiPowerCompactifiedLowerZeroSector_eq hd]
  exact xiCompactifiedZeroSectors_neg_mapsTo

/-- Honest order-two holomorphic reflection for every positive completed-zeta power. -/
def xiPowerCompactifiedHolomorphicReflection
    (d : ℕ) (hd : d ≠ 0) :
    HolomorphicDivisorReflection Set.univ
      (xiPowerCompactifiedUpperZeroSector d ∪
        xiPowerCompactifiedLowerZeroSector d) :=
  negationHolomorphicDivisorReflection _
    (xiPowerCompactifiedZeroSectors_neg_mapsTo hd)

/-- Exact smoothness classification for every positive degree `d`: the degree-zero corona term
lifts to the natural endpoint-entire reflection crossed product exactly when both height sectors
are finite. -/
theorem xiPowerCompactifiedCorona_crossedProduct_iff_finite
    (d : ℕ) (hd : d ≠ 0) :
    let R := xiPowerCompactifiedHolomorphicReflection d hd
    letI := R.functionAction
    letI : SMulCommClass ReflectionParity ℂ
        (((xiPowerCompactifiedUpperZeroSector d ∪
          xiPowerCompactifiedLowerZeroSector d : Set ℂ) → ℂ)) :=
      R.functionSmulCommClass
    SkewMonoidAlgebra.single (1 : ReflectionParity)
        (endpointRealCoronaIdempotent
          (xiPowerCompactifiedUpperZeroSector d)
          (xiPowerCompactifiedLowerZeroSector d)) ∈
      Set.range
        (InvariantSubalgebra.crossedProductInclusion
          (endpointHolomorphicInvariantSubalgebra R.endpointInvariant)) ↔
      (xiPowerCompactifiedUpperZeroSector d).Finite ∧
        (xiPowerCompactifiedLowerZeroSector d).Finite := by
  let R := xiPowerCompactifiedHolomorphicReflection d hd
  letI := R.functionAction
  letI : SMulCommClass ReflectionParity ℂ
      (((xiPowerCompactifiedUpperZeroSector d ∪
        xiPowerCompactifiedLowerZeroSector d : Set ℂ) → ℂ)) :=
    R.functionSmulCommClass
  apply HolomorphicDivisorReflection.reflectedEndpointCorona_crossedProduct_iff_finite
    R isPreconnected_univ (Set.subset_univ _) (Set.subset_univ _)
  · rw [xiPowerCompactifiedUpperZeroSector_eq hd]
    exact xiCompactifiedUpperZeroSector_infinite.nonempty
  · rw [xiPowerCompactifiedLowerZeroSector_eq hd]
    exact xiCompactifiedLowerZeroSector_infinite.nonempty
  · exact Set.mem_univ 0
  · exact Set.mem_univ 0
  · intro _
    rw [xiPowerCompactifiedUpperZeroSector_eq hd]
    exact zero_mem_closure_xiCompactifiedUpperZeroSector
  · intro _
    rw [xiPowerCompactifiedLowerZeroSector_eq hd]
    exact zero_mem_closure_xiCompactifiedLowerZeroSector
  · rw [xiPowerCompactifiedUpperZeroSector_eq hd,
      xiPowerCompactifiedLowerZeroSector_eq hd]
    exact xiCompactifiedZeroSectors_disjoint

/-- **P3, actual examples in every positive automorphic degree.**  For each `d > 0`, the
completed-zeta power has a nonsmooth Real-corona idempotent in the natural dense endpoint-entire
reflection crossed product. -/
theorem xiPowerCompactifiedCorona_not_mem_smoothCrossedProductRange
    (d : ℕ) (hd : d ≠ 0) :
    let R := xiPowerCompactifiedHolomorphicReflection d hd
    letI := R.functionAction
    letI : SMulCommClass ReflectionParity ℂ
        (((xiPowerCompactifiedUpperZeroSector d ∪
          xiPowerCompactifiedLowerZeroSector d : Set ℂ) → ℂ)) :=
      R.functionSmulCommClass
    SkewMonoidAlgebra.single (1 : ReflectionParity)
        (endpointRealCoronaIdempotent
          (xiPowerCompactifiedUpperZeroSector d)
          (xiPowerCompactifiedLowerZeroSector d)) ∉
      Set.range
        (InvariantSubalgebra.crossedProductInclusion
          (endpointHolomorphicInvariantSubalgebra R.endpointInvariant)) := by
  dsimp only
  let R := xiPowerCompactifiedHolomorphicReflection d hd
  letI := R.functionAction
  letI : SMulCommClass ReflectionParity ℂ
      (((xiPowerCompactifiedUpperZeroSector d ∪
        xiPowerCompactifiedLowerZeroSector d : Set ℂ) → ℂ)) :=
    R.functionSmulCommClass
  intro hmem
  have hfinite := (xiPowerCompactifiedCorona_crossedProduct_iff_finite d hd).mp hmem
  have hinfinite : (xiPowerCompactifiedUpperZeroSector d).Infinite := by
    rw [xiPowerCompactifiedUpperZeroSector_eq hd]
    exact xiCompactifiedUpperZeroSector_infinite
  exact hinfinite hfinite.1

/-- **Exact degree classification for the completed-zeta powers.**  The Real-corona idempotent is
smooth in the natural dense endpoint-entire reflection crossed product exactly in degree zero.
Every positive degree has the same infinite two-ended divisor as Xi and is nonsmooth. -/
theorem xiPowerAllDegree_corona_mem_smoothCrossedProductRange_iff
    (d : ℕ) :
    let R := xiPowerAllDegreeHolomorphicReflection d
    letI := R.functionAction
    letI : SMulCommClass ReflectionParity ℂ
        (((xiPowerCompactifiedUpperZeroSector d ∪
          xiPowerCompactifiedLowerZeroSector d : Set ℂ) → ℂ)) :=
      R.functionSmulCommClass
    SkewMonoidAlgebra.single (1 : ReflectionParity)
        (endpointRealCoronaIdempotent
          (xiPowerCompactifiedUpperZeroSector d)
          (xiPowerCompactifiedLowerZeroSector d)) ∈
      Set.range
        (InvariantSubalgebra.crossedProductInclusion
          (endpointHolomorphicInvariantSubalgebra R.endpointInvariant)) ↔
      d = 0 := by
  let R := xiPowerAllDegreeHolomorphicReflection d
  letI := R.functionAction
  letI : SMulCommClass ReflectionParity ℂ
      (((xiPowerCompactifiedUpperZeroSector d ∪
        xiPowerCompactifiedLowerZeroSector d : Set ℂ) → ℂ)) :=
    R.functionSmulCommClass
  constructor
  · intro hmem
    by_contra hd
    have hiff :
        SkewMonoidAlgebra.single (1 : ReflectionParity)
            (endpointRealCoronaIdempotent
              (xiPowerCompactifiedUpperZeroSector d)
              (xiPowerCompactifiedLowerZeroSector d)) ∈
          Set.range
            (InvariantSubalgebra.crossedProductInclusion
              (endpointHolomorphicInvariantSubalgebra R.endpointInvariant)) ↔
          (xiPowerCompactifiedUpperZeroSector d).Finite ∧
            (xiPowerCompactifiedLowerZeroSector d).Finite := by
      apply HolomorphicDivisorReflection.reflectedEndpointCorona_crossedProduct_iff_finite
        R isPreconnected_univ (Set.subset_univ _) (Set.subset_univ _)
      · rw [xiPowerCompactifiedUpperZeroSector_eq hd]
        exact xiCompactifiedUpperZeroSector_infinite.nonempty
      · rw [xiPowerCompactifiedLowerZeroSector_eq hd]
        exact xiCompactifiedLowerZeroSector_infinite.nonempty
      · exact Set.mem_univ 0
      · exact Set.mem_univ 0
      · intro _
        rw [xiPowerCompactifiedUpperZeroSector_eq hd]
        exact zero_mem_closure_xiCompactifiedUpperZeroSector
      · intro _
        rw [xiPowerCompactifiedLowerZeroSector_eq hd]
        exact zero_mem_closure_xiCompactifiedLowerZeroSector
      · rw [xiPowerCompactifiedUpperZeroSector_eq hd,
          xiPowerCompactifiedLowerZeroSector_eq hd]
        exact xiCompactifiedZeroSectors_disjoint
    have hfinite := hiff.mp hmem
    have hinfinite : (xiPowerCompactifiedUpperZeroSector d).Infinite := by
      rw [xiPowerCompactifiedUpperZeroSector_eq hd]
      exact xiCompactifiedUpperZeroSector_infinite
    exact hinfinite hfinite.1
  · intro hd
    subst d
    rw [InvariantSubalgebra.degreeZero_mem_crossedProductRange_iff]
    refine ⟨fun _ => 0, analyticOnNhd_const, ?_⟩
    intro z
    exact False.elim (by simpa using z.property)

end RHTower
