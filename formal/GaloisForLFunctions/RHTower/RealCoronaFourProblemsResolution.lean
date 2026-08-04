import GaloisForLFunctions.RHTower.RealCoronaCompleteDivisorOddZetaNoGo
import GaloisForLFunctions.RHTower.CCMRationalClosedKappaLefschetzParityNoGo
import GaloisForLFunctions.RHTower.CompleteStripRealCoronaCompactification
import GaloisForLFunctions.RHTower.XiAutomorphicRealCoronaSmoothness
import GaloisForLFunctions.RHTower.SelfDualDirichletRealCoronaSmoothness
import GaloisForLFunctions.RHTower.PositiveDegreeAutomorphicRealCoronaSmoothness
import GaloisForLFunctions.RHTower.XiPowerAutomorphicRealCoronaSmoothness
import GaloisForLFunctions.RHTower.SelfDualFixedSectorVariation
import GaloisForLFunctions.RHTower.PolynomialSelfDualFixedSectorVariation

/-!
# Resolution facade for the four Real-corona problems

This module contains no new assumption and no compressed surrogate.  It exposes stable theorem
names for the dependency-closed results proved in the analytic, operator, cyclic, and automorphic
modules imported above.  The paper claim trace uses these names as its formal facade.
-/

noncomputable section

open Set

namespace GaloisForLFunctions.RHTower

/-! ## Governing conservation law -/

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

/-- The universal law behind P1--P4: for an unbounded invariant-domain operator, a bounded
orientation commutator is equivalent to bounded detecting odd part together with unbounded
commuting even part. -/
theorem realCorona_smoothnessDetectabilityConservation
    (D : V →ₗ.[ℂ] V) (m : Module.End ℂ V)
    (hdomm : ∀ x : D.domain, m x ∈ D.domain)
    (hm : m * m = 1) (hiso : ∀ y : V, ‖m y‖ = ‖y‖)
    (hD : IsGenuinelyUnboundedLinearPMap D) :
    HasLinearPMapBoundOnDomain
        (linearPMapOrientationCommutator D m hdomm) ↔
      IsGenuinelyUnboundedLinearPMap
          (linearPMapOrientationEven D m hdomm) ∧
        HasLinearPMapBoundOnDomain
          (linearPMapOrientationOdd D m hdomm) :=
  bounded_orientationCommutator_iff_unbounded_even_and_bounded_odd
    D m hdomm hm hiso hD

/-! ## P1: actual odd complete-divisor spectral-triple obstruction -/

/-- P1 on the canonical odd complete-divisor realization.  Its Dirac operator is self-adjoint,
genuinely unbounded, and has a compact two-sided inverse, but the commutator with the exact
Real-corona projector is unbounded.  Thus the projector fails the first spectral-triple axiom
needed before a local index formula can be formed. -/
theorem realCoronaP1_oddCompleteDivisor_zetaNoGo :
    IsSelfAdjoint _root_.RHTower.xiCompleteDivisorOddDirac ∧
      IsGenuinelyUnboundedLinearPMap _root_.RHTower.xiCompleteDivisorOddDirac ∧
      IsCompactOperator _root_.RHTower.xiCompleteDivisorOddInverse ∧
      (∀ x : _root_.RHTower.XiDivisorL2,
        _root_.RHTower.xiCompleteDivisorOddDirac
          ⟨_root_.RHTower.xiCompleteDivisorOddInverse x,
            _root_.RHTower.xiCompleteDivisorOddInverse_mem_domain x⟩ = x) ∧
      (∀ x : _root_.RHTower.xiCompleteDivisorOddDirac.domain,
        _root_.RHTower.xiCompleteDivisorOddInverse
            (_root_.RHTower.xiCompleteDivisorOddDirac x) =
          (x : _root_.RHTower.XiDivisorL2)) ∧
      ¬HasLinearPMapBoundOnDomain
        (linearPMapExchangeCommutator _root_.RHTower.xiCompleteDivisorOddDirac
          _root_.RHTower.xiCompleteDivisorOrientation
          _root_.RHTower.xiCompleteDivisorOrientation_mem_oddDomain) :=
  _root_.RHTower.xiCompleteDivisorOdd_zetaNoGo_certificate

/-! ## P2: literal closed full-adeles parity obstruction, with Clifford survivor -/

private abbrev Section := CCMRationalClassSpaceSection
private abbrev Relative :=
  CCMRationalAdelicClosedNonunitalStrongRelativeCyclicModule
private abbrev RelativeKReal :=
  ccmRationalAdelicClosedNonunitalStrongRelativeCyclicKReal

/-- The literal descended CCM Lefschetz correspondence on the closed nonunital Definition 4.10
recipient is nonzero Real-even and cannot have anti-Real Chern parity. -/
theorem realCoronaP2_lefschetz_not_antiReal (c : Section) :
    ¬ ∀ n (x : Relative.simplicial.degree n),
      (RelativeKReal.real n).sigma
          ((ccmRationalAdelicClosedNonunitalStrongLefschetz c).simplicial.app
            (.op (.mk n)) x) =
        -(ccmRationalAdelicClosedNonunitalStrongLefschetz c).simplicial.app
          (.op (.mk n)) ((RelativeKReal.real n).sigma x) :=
  ccmRationalAdelicClosedNonunitalStrongLefschetz_not_antiReal c

/-- Exact classification of scalar parity corrections: `z L_c` is anti-Real exactly for purely
imaginary `z`.  The choice `z = i` is the positive Clifford generator, not a false uniqueness
claim forced by parity alone. -/
theorem realCoronaP2_scalarShift_antiReal_iff_star_eq_neg
    (c : Section) (z : ℂ) :
    (∀ n (x : Relative.simplicial.degree n),
      (RelativeKReal.real n).sigma
          (((ccmRationalAdelicClosedNonunitalStrongLefschetz c).smul z).simplicial.app
            (.op (.mk n)) x) =
        -((ccmRationalAdelicClosedNonunitalStrongLefschetz c).smul z).simplicial.app
          (.op (.mk n)) ((RelativeKReal.real n).sigma x)) ↔
      (starRingEnd ℂ) z = -z :=
  ccmRationalAdelicClosedNonunitalStrongLefschetz_smul_isAnti_iff_star_eq_neg c z

/-- Theory-independent P2 answer: in every bivariant theory whose realized Chern characters have
the required anti-Real parity, no class can realize to untwisted closed CCM Lefschetz. -/
theorem realCoronaP2_no_bivariantChernRealization_eq_lefschetz
    {BivariantClass : Type*}
    (realizedChern : BivariantClass →
      CyclicModule.KRealAntiHom RelativeKReal RelativeKReal)
    (c : Section) :
    ¬∃ κ : BivariantClass,
      (realizedChern κ).toHom =
        ccmRationalAdelicClosedNonunitalStrongLefschetz c :=
  ccmRationalAdelicClosedNonunitalStrong_no_bivariantChernRealization_eq_lefschetz
    realizedChern c

/-- The maximal exact comparison is the Clifford transgression `i L` on the literal closed CCM
recipient. -/
theorem realCoronaP2_cliffordTransgression_eq_i_lefschetz (c : Section) :
    (ccmRationalAdelicClosedNonunitalStrongCliffordTransgression c).toHom =
      (ccmRationalAdelicClosedNonunitalStrongLefschetz c).smul Complex.I :=
  ccmRationalAdelicClosedNonunitalStrongCliffordTransgression_eq_i_lefschetz c

/-! ## P3: endpoint-holomorphic crossed-product classification -/

/-- P3 for every infinite locally finite complete-strip reflection divisor. -/
theorem realCoronaP3_completeStrip_not_smooth
    (D : CompleteStripReflectionDivisor) :
    let R := D.holomorphicReflection
    letI := R.functionAction
    letI : SMulCommClass ReflectionParity ℂ
        (((D.upperSector ∪ D.lowerSector : Set ℂ) → ℂ)) := R.functionSmulCommClass
    SkewMonoidAlgebra.single (1 : ReflectionParity)
        (endpointRealCoronaIdempotent D.upperSector D.lowerSector) ∉
      Set.range (InvariantSubalgebra.crossedProductInclusion
        (endpointHolomorphicInvariantSubalgebra R.endpointInvariant)) :=
  D.corona_not_mem_smoothCrossedProductRange

/-- P3 without a zero-infinitude premise: standard positive-degree analytic growth derives the
infinite divisor and excludes smoothness. -/
theorem realCoronaP3_positiveDegreeCompletion_not_smooth
    (F : PositiveDegreeSelfDualCompletion) :
    let D := F.toCompleteStripReflectionDivisor
    let R := D.holomorphicReflection
    letI := R.functionAction
    letI : SMulCommClass ReflectionParity ℂ
        (((D.upperSector ∪ D.lowerSector : Set ℂ) → ℂ)) := R.functionSmulCommClass
    SkewMonoidAlgebra.single (1 : ReflectionParity)
        (endpointRealCoronaIdempotent D.upperSector D.lowerSector) ∉
      Set.range (InvariantSubalgebra.crossedProductInclusion
        (endpointHolomorphicInvariantSubalgebra R.endpointInvariant)) :=
  F.corona_not_mem_smoothCrossedProductRange

/-- P3 for the actual completed Riemann Xi divisor. -/
theorem realCoronaP3_riemannXi_not_smooth :
    let R := _root_.RHTower.xiCompactifiedHolomorphicReflection
    letI := R.functionAction
    letI : SMulCommClass ReflectionParity ℂ
        (((_root_.RHTower.xiCompactifiedUpperZeroSector ∪
          _root_.RHTower.xiCompactifiedLowerZeroSector : Set ℂ) → ℂ)) :=
      R.functionSmulCommClass
    SkewMonoidAlgebra.single (1 : ReflectionParity)
        (endpointRealCoronaIdempotent
          _root_.RHTower.xiCompactifiedUpperZeroSector
          _root_.RHTower.xiCompactifiedLowerZeroSector) ∉
      Set.range (InvariantSubalgebra.crossedProductInclusion
        (endpointHolomorphicInvariantSubalgebra R.endpointInvariant)) :=
  _root_.RHTower.xiCompactifiedCorona_not_mem_smoothCrossedProductRange

variable {N : ℕ} [NeZero N]

/-- P3 for every actual nontrivial primitive self-dual Dirichlet completion. -/
theorem realCoronaP3_selfDualPrimitiveDirichlet_not_smooth
    (chi : SelfDualPrimitiveDirichletDatum N) :
    let D := selfDualPrimitiveDirichletCompleteStripDivisor chi
    let R := D.holomorphicReflection
    letI := R.functionAction
    letI : SMulCommClass ReflectionParity ℂ
        (((D.upperSector ∪ D.lowerSector : Set ℂ) → ℂ)) := R.functionSmulCommClass
    SkewMonoidAlgebra.single (1 : ReflectionParity)
        (endpointRealCoronaIdempotent D.upperSector D.lowerSector) ∉
      Set.range (InvariantSubalgebra.crossedProductInclusion
        (endpointHolomorphicInvariantSubalgebra R.endpointInvariant)) :=
  selfDualPrimitiveDirichlet_corona_not_mem_smoothCrossedProductRange chi

/-- Exact P3 degree classification for the actual completed-zeta power family: its Real-corona
idempotent is smooth in the natural endpoint-entire crossed product exactly in degree zero. -/
theorem realCoronaP3_xiPower_smooth_iff_degree_zero (d : ℕ) :
    let R := _root_.RHTower.xiPowerAllDegreeHolomorphicReflection d
    letI := R.functionAction
    letI : SMulCommClass ReflectionParity ℂ
        (((_root_.RHTower.xiPowerCompactifiedUpperZeroSector d ∪
          _root_.RHTower.xiPowerCompactifiedLowerZeroSector d : Set ℂ) → ℂ)) :=
      R.functionSmulCommClass
    SkewMonoidAlgebra.single (1 : ReflectionParity)
        (endpointRealCoronaIdempotent
          (_root_.RHTower.xiPowerCompactifiedUpperZeroSector d)
          (_root_.RHTower.xiPowerCompactifiedLowerZeroSector d)) ∈
      Set.range
        (InvariantSubalgebra.crossedProductInclusion
          (endpointHolomorphicInvariantSubalgebra R.endpointInvariant)) ↔
      d = 0 :=
  _root_.RHTower.xiPowerAllDegree_corona_mem_smoothCrossedProductRange_iff d

/-! ## P4: fixed-sector variation and analytic rank -/

variable {T : Type*}

/-- P4 family law: cyclic fixed-sector variation is analytic-rank variation plus twice the
upper off-central variation. -/
theorem realCoronaP4_fixedSectorVariation
    (F : CompletedSelfDualAnalyticFamily T) (t₀ t₁ : T) :
    F.fixedSectorDefectVariation t₀ t₁ =
      F.analyticRankVariation t₀ t₁ +
        2 * F.upperOffCentralMultiplicityVariation t₀ t₁ :=
  F.fixedSectorDefectVariation_eq t₀ t₁

/-- Ordinary coordinate `K₀` sees only central support; the exact missing analytic-rank change is
the change of central multiplicity excess. -/
theorem realCoronaP4_analyticRankVariation_eq_kZero_add_excess
    (F : CompletedSelfDualAnalyticFamily T) (t₀ t₁ : T) :
    F.analyticRankVariation t₀ t₁ =
      F.centralKZeroVariation t₀ t₁ +
        (centralKZeroMultiplicityExcess
            (F.toSelfDualRealZeroFamily.analyticRank t₁) -
          centralKZeroMultiplicityExcess
            (F.toSelfDualRealZeroFamily.analyticRank t₀)) :=
  F.analyticRankVariation_eq_kZero_add_excess t₀ t₁

/-- Concrete P4 family law: `z^n(z²-1)^k` has central analytic rank `n` and total fixed-sector
defect `n+2k`. -/
theorem realCoronaP4_polynomialFamily_defectRank (n k : ℕ) :
    polynomialSelfDualFamily.toSelfDualRealZeroFamily.defectRank (n, k) = n + 2 * k :=
  polynomialSelfDualFamily_defectRank n k

/-- Concrete P4 `K₀` comparison: central evaluation forgets every multiplicity beyond support. -/
theorem realCoronaP4_polynomialFamily_centralKZeroRank (n k : ℕ) :
    polynomialSelfDualFamily.centralKZeroRankInt (n, k) =
      if n = 0 then 0 else 1 :=
  polynomialSelfDualFamily_centralKZeroRankInt n k

/-- Concrete signed P4 variation with independently moving central and reflected-pair
multiplicities. -/
theorem realCoronaP4_polynomialFamily_defectVariation
    (n₀ k₀ n₁ k₁ : ℕ) :
    polynomialSelfDualFamily.fixedSectorDefectVariation (n₀, k₀) (n₁, k₁) =
      ((n₁ + 2 * k₁ : ℕ) : ℤ) - ((n₀ + 2 * k₀ : ℕ) : ℤ) :=
  polynomialSelfDualFamily_fixedSectorDefectVariation n₀ k₀ n₁ k₁

end GaloisForLFunctions.RHTower
