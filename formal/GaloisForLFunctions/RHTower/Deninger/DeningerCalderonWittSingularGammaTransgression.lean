import GaloisForLFunctions.RHTower.Deninger.DeningerCalderonWittOrientationTransgressionCompleteness
import GaloisForLFunctions.RHTower.CCM.CCMFirstClockPrimitivePromotedExteriorSource

/-!
# Singular Gamma transgression of Calderón--Witt incidence

The all-prime Calderón--Witt cup kills cross-prime exterior products.  Those
products are therefore exact Milnor-incidence relations, not nonexistent
source data.  This file constructs the missing boundary-sensitive operation
on them.

For ordered primes `p,q`, take the Calderón coordinate of the `p` component
and the actual algebraic first-suspension packet of the `q` component.  Their
alternating cross-effect is vector-valued in the degree-two center at `q`.
It is multiplied by the source-derived primitive Gamma modular exterior
coefficient at two valuation depths.  Only after that multiplication is the
normalized Haar orientation read.

The resulting transport retains ordered prime, valuation-depth, suspension,
and rational-Witt packet data.  Its reflection-odd kernel is a concrete
admitted Hodge sector inside global Milnor incidence.  A canonical cross-prime
incidence witness belongs to this sector exactly at zero modular
displacement.  No Xi zero, divisor-indexed coefficient, positivity premise,
or RH hypothesis enters the construction.
-/

namespace RHTower

open scoped DirectSum
open Filter Asymptotics

noncomputable section

/-! ## Source legs of the nonlocal cross-effect -/

/-- Calderón coordinate of one local algebraic degree-one source. -/
def deningerCalderonWittLocalDefectCoordinate
    (p : Nat.Primes) :
    DeningerCalderonWittAlgebraicDegreeOne p →ₗ[ℂ] ℂ :=
  (deningerMeyerPoissonCalderonQuotientEquiv (p : ℝ)).toLinearMap.comp
    (LinearMap.fst ℂ
      (DeningerMeyerPrimeCalderonQuotient p)
      (DeningerPrimeFinitePacketGaugeAlgebraic p))

/-- First suspension of the packet leg, still vector-valued. -/
def deningerCalderonWittLocalPacketFirstMode
    (p : Nat.Primes) :
    DeningerCalderonWittAlgebraicDegreeOne p →ₗ[ℂ]
      DeningerCalderonWittAlgebraicDegreeTwo p :=
  (deningerPrimeFinitePacketGaugeAlgebraicFirstModeEquiv p).toLinearMap.comp
    (LinearMap.snd ℂ
      (DeningerMeyerPrimeCalderonQuotient p)
      (DeningerPrimeFinitePacketGaugeAlgebraic p))

/-- Extract the Calderón coordinate at `p` from the all-prime source. -/
def deningerCalderonWittGlobalDefectCoordinate
    (p : Nat.Primes) :
    DeningerCalderonWittAlgebraicGlobalDegreeOne →ₗ[ℂ] ℂ :=
  (deningerCalderonWittLocalDefectCoordinate p).comp
    (DirectSum.component ℂ Nat.Primes
      DeningerCalderonWittAlgebraicDegreeOne p)

/-- Extract and suspend the packet coordinate at `q` from the all-prime source. -/
def deningerCalderonWittGlobalPacketFirstMode
    (q : Nat.Primes) :
    DeningerCalderonWittAlgebraicGlobalDegreeOne →ₗ[ℂ]
      DeningerCalderonWittAlgebraicDegreeTwo q :=
  (deningerCalderonWittLocalPacketFirstMode q).comp
    (DirectSum.component ℂ Nat.Primes
      DeningerCalderonWittAlgebraicDegreeOne q)

/--
Nonlocal vector-valued Calderón--Witt cross-effect from the defect leg at
`p` to the packet suspension at `q`.
-/
def deningerCalderonWittNonlocalCrossEffect
    (p q : Nat.Primes) :
    DeningerCalderonWittAlgebraicGlobalDegreeOne →ₗ[ℂ]
      DeningerCalderonWittAlgebraicGlobalDegreeOne →ₗ[ℂ]
        DeningerCalderonWittAlgebraicDegreeTwo q where
  toFun x :=
    { toFun := fun y =>
        deningerCalderonWittGlobalDefectCoordinate p x •
            deningerCalderonWittGlobalPacketFirstMode q y -
          deningerCalderonWittGlobalDefectCoordinate p y •
            deningerCalderonWittGlobalPacketFirstMode q x
      map_add' := by
        intro y z
        simp only [map_add, smul_add, add_smul]
        module
      map_smul' := by
        intro c y
        simp only [map_smul, RingHom.id_apply, smul_sub, smul_smul]
        module }
  map_add' x z := by
    apply LinearMap.ext
    intro y
    change
      deningerCalderonWittGlobalDefectCoordinate p (x + z) •
            deningerCalderonWittGlobalPacketFirstMode q y -
          deningerCalderonWittGlobalDefectCoordinate p y •
            deningerCalderonWittGlobalPacketFirstMode q (x + z) =
        (deningerCalderonWittGlobalDefectCoordinate p x •
              deningerCalderonWittGlobalPacketFirstMode q y -
            deningerCalderonWittGlobalDefectCoordinate p y •
              deningerCalderonWittGlobalPacketFirstMode q x) +
          (deningerCalderonWittGlobalDefectCoordinate p z •
              deningerCalderonWittGlobalPacketFirstMode q y -
            deningerCalderonWittGlobalDefectCoordinate p y •
              deningerCalderonWittGlobalPacketFirstMode q z)
    rw [map_add, map_add, add_smul, smul_add]
    abel
  map_smul' c x := by
    apply LinearMap.ext
    intro y
    change
      deningerCalderonWittGlobalDefectCoordinate p (c • x) •
            deningerCalderonWittGlobalPacketFirstMode q y -
          deningerCalderonWittGlobalDefectCoordinate p y •
            deningerCalderonWittGlobalPacketFirstMode q (c • x) =
        c •
          (deningerCalderonWittGlobalDefectCoordinate p x •
              deningerCalderonWittGlobalPacketFirstMode q y -
            deningerCalderonWittGlobalDefectCoordinate p y •
              deningerCalderonWittGlobalPacketFirstMode q x)
    rw [map_smul, map_smul, smul_sub, smul_smul, smul_smul]
    module

@[simp]
theorem deningerCalderonWittNonlocalCrossEffect_self
    (p q : Nat.Primes)
    (x : DeningerCalderonWittAlgebraicGlobalDegreeOne) :
    deningerCalderonWittNonlocalCrossEffect p q x x = 0 := by
  simp [deningerCalderonWittNonlocalCrossEffect]

/-! ## Exterior linearization -/

/-- Scalar weighting is applied after the vector-valued cross-effect. -/
def deningerCalderonWittWeightedNonlocalCrossEffect
    (c : ℂ) (p q : Nat.Primes) :
    DeningerCalderonWittAlgebraicGlobalDegreeOne →ₗ[ℂ]
      DeningerCalderonWittAlgebraicGlobalDegreeOne →ₗ[ℂ]
        DeningerCalderonWittAlgebraicDegreeTwo q :=
  c • deningerCalderonWittNonlocalCrossEffect p q

/-- Alternating form underlying the weighted nonlocal cross-effect. -/
def deningerCalderonWittWeightedNonlocalAlternating
    (c : ℂ) (p q : Nat.Primes) :
    DeningerCalderonWittAlgebraicGlobalDegreeOne
      [⋀^Fin 2]→ₗ[ℂ]
        DeningerCalderonWittAlgebraicDegreeTwo q where
  toFun v :=
    deningerCalderonWittWeightedNonlocalCrossEffect c p q (v 0) (v 1)
  map_update_add' v i x y := by
    fin_cases i <;>
      simp [deningerCalderonWittWeightedNonlocalCrossEffect]
  map_update_smul' v i c' x := by
    fin_cases i <;>
      simp [deningerCalderonWittWeightedNonlocalCrossEffect]
  map_eq_zero_of_eq' v i j hij hne := by
    fin_cases i <;> fin_cases j
    · exact (hne rfl).elim
    · have hij' : v 0 = v 1 := by simpa using hij
      rw [hij']
      simp [deningerCalderonWittWeightedNonlocalCrossEffect]
    · have hij' : v 1 = v 0 := by simpa using hij
      rw [hij']
      simp [deningerCalderonWittWeightedNonlocalCrossEffect]
    · exact (hne rfl).elim

/-- Linearized weighted nonlocal operation on the exterior square. -/
def deningerCalderonWittWeightedNonlocalExterior
    (c : ℂ) (p q : Nat.Primes) :
    (⋀[ℂ]^(2 : ℕ) DeningerCalderonWittAlgebraicGlobalDegreeOne) →ₗ[ℂ]
      DeningerCalderonWittAlgebraicDegreeTwo q :=
  exteriorPower.alternatingMapLinearEquiv
    (deningerCalderonWittWeightedNonlocalAlternating c p q)

theorem deningerCalderonWittWeightedNonlocalAlternating_zero
    (p q : Nat.Primes) :
    deningerCalderonWittWeightedNonlocalAlternating 0 p q = 0 := by
  ext v
  simp [deningerCalderonWittWeightedNonlocalAlternating,
    deningerCalderonWittWeightedNonlocalCrossEffect]

theorem deningerCalderonWittWeightedNonlocalExterior_zero
    (p q : Nat.Primes) :
    deningerCalderonWittWeightedNonlocalExterior 0 p q = 0 := by
  rw [deningerCalderonWittWeightedNonlocalExterior,
    deningerCalderonWittWeightedNonlocalAlternating_zero]
  exact map_zero exteriorPower.alternatingMapLinearEquiv

@[simp]
theorem deningerCalderonWittWeightedNonlocalExterior_ιMulti
    (c : ℂ) (p q : Nat.Primes)
    (v : Fin 2 → DeningerCalderonWittAlgebraicGlobalDegreeOne) :
    deningerCalderonWittWeightedNonlocalExterior c p q
        (exteriorPower.ιMulti ℂ 2 v) =
      deningerCalderonWittWeightedNonlocalCrossEffect c p q
        (v 0) (v 1) := by
  rw [deningerCalderonWittWeightedNonlocalExterior,
    exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
  rfl

/-! ## Canonical exact boundary witness -/

/--
Canonical cross-prime incidence relation: defect unit at `p` wedged with
packet unit at `q`.
-/
def deningerCalderonWittCrossPrimeGammaWitness
    {p q : Nat.Primes} (hpq : p ≠ q) :
    deningerCalderonWittGlobalMilnorIncidence :=
  ⟨exteriorPower.ιMulti ℂ 2
      ![
        DirectSum.lof ℂ Nat.Primes
          DeningerCalderonWittAlgebraicDegreeOne p
          (deningerCalderonWittUnitDefect p, 0),
        DirectSum.lof ℂ Nat.Primes
          DeningerCalderonWittAlgebraicDegreeOne q
          (0, deningerCalderonWittAlgebraicUnitPacket q)],
    deningerCalderonWittGlobalCrossPrime_mem_milnorIncidence
      hpq
      (deningerCalderonWittUnitDefect p, 0)
      (0, deningerCalderonWittAlgebraicUnitPacket q)⟩

/-- The canonical boundary is transported to the actual packet suspension. -/
theorem deningerCalderonWittWeightedNonlocalExterior_crossPrimeWitness
    {p q : Nat.Primes} (hpq : p ≠ q) (c : ℂ) :
    deningerCalderonWittWeightedNonlocalExterior c p q
        (deningerCalderonWittCrossPrimeGammaWitness hpq).1 =
      c • deningerPrimeFinitePacketGaugeAlgebraicFirstMode q
        (deningerCalderonWittAlgebraicUnitPacket q) := by
  rw [deningerCalderonWittCrossPrimeGammaWitness,
    deningerCalderonWittWeightedNonlocalExterior_ιMulti]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  simp [deningerCalderonWittWeightedNonlocalCrossEffect,
    deningerCalderonWittNonlocalCrossEffect,
    deningerCalderonWittGlobalDefectCoordinate,
    deningerCalderonWittGlobalPacketFirstMode,
    deningerCalderonWittLocalDefectCoordinate,
    deningerCalderonWittLocalPacketFirstMode,
    DirectSum.component.of, hpq,
    deningerMeyerPoissonCalderonQuotientEquiv_unitDefect]

/-! ## Depth-resolved singular transports -/

/-- Vector transport retains both prime labels, both depths, and the packet center. -/
abbrev DeningerCalderonWittGammaVectorProfile :=
  (p : Nat.Primes) → (q : Nat.Primes) → ℕ → ℕ →
    DeningerCalderonWittAlgebraicDegreeTwo q

/-- Oriented scalar profile, formed only after vector-valued multiplication. -/
abbrev DeningerCalderonWittGammaScalarProfile :=
  Nat.Primes → Nat.Primes → ℕ → ℕ → ℂ

/-- Source-pointed modular Gamma transport on exact incidence relations. -/
def deningerCalderonWittGammaModularVectorTransport
    (a : ℝ) :
    deningerCalderonWittGlobalMilnorIncidence →ₗ[ℂ]
      DeningerCalderonWittGammaVectorProfile where
  toFun i p q e f :=
    deningerCalderonWittWeightedNonlocalExterior
      (xiGammaEulerPrimitiveModularExterior a (p, e) (q, f) : ℂ)
      p q i.1
  map_add' i j := by
    funext p q e f
    simp
  map_smul' c i := by
    funext p q e f
    simp

/-- Componentwise normalized Haar orientation of a vector profile. -/
def deningerCalderonWittGammaOrientation :
    DeningerCalderonWittGammaVectorProfile →ₗ[ℂ]
      DeningerCalderonWittGammaScalarProfile where
  toFun z p q e f :=
    deningerCalderonWittAlgebraicCenterTrace q (z p q e f)
  map_add' z w := by
    funext p q e f
    simp
  map_smul' c z := by
    funext p q e f
    simp

/-- Oriented modular transport.  Orientation is applied last. -/
def deningerCalderonWittGammaModularScalarTransport
    (a : ℝ) :
    deningerCalderonWittGlobalMilnorIncidence →ₗ[ℂ]
      DeningerCalderonWittGammaScalarProfile :=
  deningerCalderonWittGammaOrientation.comp
    (deningerCalderonWittGammaModularVectorTransport a)

theorem deningerCalderonWittGammaModularVectorTransport_crossPrimeWitness
    {p q : Nat.Primes} (hpq : p ≠ q)
    (a : ℝ) (e f : ℕ) :
    deningerCalderonWittGammaModularVectorTransport a
        (deningerCalderonWittCrossPrimeGammaWitness hpq) p q e f =
      (xiGammaEulerPrimitiveModularExterior a (p, e) (q, f) : ℂ) •
        deningerPrimeFinitePacketGaugeAlgebraicFirstMode q
          (deningerCalderonWittAlgebraicUnitPacket q) :=
  deningerCalderonWittWeightedNonlocalExterior_crossPrimeWitness hpq _

theorem deningerCalderonWittGammaModularScalarTransport_crossPrimeWitness
    {p q : Nat.Primes} (hpq : p ≠ q)
    (a : ℝ) (e f : ℕ) :
    deningerCalderonWittGammaModularScalarTransport a
        (deningerCalderonWittCrossPrimeGammaWitness hpq) p q e f =
      (xiGammaEulerPrimitiveModularExterior a (p, e) (q, f) : ℂ) := by
  rw [deningerCalderonWittGammaModularScalarTransport,
    LinearMap.comp_apply, deningerCalderonWittGammaOrientation]
  change
    deningerCalderonWittAlgebraicCenterTrace q
        (deningerCalderonWittGammaModularVectorTransport a
          (deningerCalderonWittCrossPrimeGammaWitness hpq) p q e f) =
      (xiGammaEulerPrimitiveModularExterior a (p, e) (q, f) : ℂ)
  rw [deningerCalderonWittGammaModularVectorTransport_crossPrimeWitness
    hpq, map_smul]
  have htrace :
      deningerCalderonWittAlgebraicCenterTrace q
          (deningerPrimeFinitePacketGaugeAlgebraicFirstMode q
            (deningerCalderonWittAlgebraicUnitPacket q)) =
        1 := by
    change
      deningerCalderonWittAlgebraicPacketTrace q
          ((deningerPrimeFinitePacketGaugeAlgebraicFirstModeEquiv q).symm
            ((deningerPrimeFinitePacketGaugeAlgebraicFirstModeEquiv q)
              (deningerCalderonWittAlgebraicUnitPacket q))) =
        1
    rw [(deningerPrimeFinitePacketGaugeAlgebraicFirstModeEquiv q).symm_apply_apply,
      deningerCalderonWittAlgebraicPacketTrace_unit]
  rw [htrace, smul_eq_mul, mul_one]

/-! ## Exact singular reflection sewing -/

/--
Reflection sewing cost of a same-depth ordered prime pair.  It is defined
from the two source modular rates, before any scalar target is introduced.
-/
def deningerCalderonWittGammaReflectionSewingCost
    (a : ℝ) (p q : Nat.Primes) (n : ℕ) : ℝ :=
  Real.exp
    (-2 * a *
      (xiGammaEulerPrimitiveModularRate (p, n) +
        xiGammaEulerPrimitiveModularRate (q, n)))

/--
The reflected primitive exterior is exactly obtained by multiplying the
unreflected exterior by the source-defined sewing cost.
-/
theorem xiGammaEulerPrimitiveModularExterior_reflection_eq_sewingCost_mul
    (a : ℝ) (p q : Nat.Primes) (n : ℕ) :
    xiGammaEulerPrimitiveModularExterior (-a) (p, n) (q, n) =
      deningerCalderonWittGammaReflectionSewingCost a p q n *
        xiGammaEulerPrimitiveModularExterior a (p, n) (q, n) := by
  rw [xiGammaEulerPrimitiveModularExterior_eq,
    xiGammaEulerPrimitiveModularExterior_eq]
  unfold deningerCalderonWittGammaReflectionSewingCost
  let S :=
    xiGammaEulerPrimitiveModularRate (p, n) +
      xiGammaEulerPrimitiveModularRate (q, n)
  let A :=
    xiGammaEulerPrimitiveBoundaryAmplitude 0 (p, n) *
      xiGammaEulerPrimitiveBoundaryAmplitude 0 (q, n)
  let D :=
    xiGammaEulerBoundaryHalfHeight p n -
      xiGammaEulerBoundaryHalfHeight q n
  change
    A * Real.exp ((-a) * S) * D =
      Real.exp (-2 * a * S) * (A * Real.exp (a * S) * D)
  rw [show
    Real.exp (-2 * a * S) * (A * Real.exp (a * S) * D) =
      A * (Real.exp (-2 * a * S) * Real.exp (a * S)) * D by ring,
    ← Real.exp_add]
  congr 2
  ring_nf

/--
Distinct primes have distinct source heights at every common valuation
depth.  Hence the cross-prime exterior channel used below is nonzero.
-/
theorem xiGammaEulerBoundaryHalfHeight_ne_of_primes_ne_sameDepth
    {p q : Nat.Primes} (hpq : p ≠ q) (n : ℕ) :
    xiGammaEulerBoundaryHalfHeight p n ≠
      xiGammaEulerBoundaryHalfHeight q n := by
  intro h
  unfold xiGammaEulerBoundaryHalfHeight at h
  have hfactor : (((n : ℝ) + 1) / 2) ≠ 0 := by positivity
  have hlog :
      Real.log (p : ℝ) = Real.log (q : ℝ) :=
    mul_left_cancel₀ hfactor h
  have hpR : (0 : ℝ) < (p : ℝ) := by
    exact_mod_cast p.property.pos
  have hqR : (0 : ℝ) < (q : ℝ) := by
    exact_mod_cast q.property.pos
  have hcast : (p : ℝ) = (q : ℝ) := by
    have hexp := congrArg Real.exp hlog
    rwa [Real.exp_log hpR, Real.exp_log hqR] at hexp
  apply hpq
  apply Subtype.ext
  exact_mod_cast hcast

/-- The same-depth cross-prime primitive exterior never vanishes. -/
theorem xiGammaEulerPrimitiveModularExterior_ne_zero_sameDepth
    {p q : Nat.Primes} (hpq : p ≠ q)
    (a : ℝ) (n : ℕ) :
    xiGammaEulerPrimitiveModularExterior a (p, n) (q, n) ≠ 0 := by
  rw [xiGammaEulerPrimitiveModularExterior_eq]
  exact mul_ne_zero
    (mul_ne_zero
      (mul_ne_zero
        (xiGammaEulerPrimitiveBoundaryAmplitude_pos 0 (p, n)).ne'
        (xiGammaEulerPrimitiveBoundaryAmplitude_pos 0 (q, n)).ne')
      (Real.exp_pos _).ne')
    (sub_ne_zero.mpr
      (xiGammaEulerBoundaryHalfHeight_ne_of_primes_ne_sameDepth hpq n))

/--
Exact singular sewing law on an actual transported Milnor-incidence
witness.  Both sides are values of the constructed source transport.
-/
theorem
    deningerCalderonWittGammaModularScalarTransport_reflection_eq_sewingCost_mul
    {p q : Nat.Primes} (hpq : p ≠ q)
    (a : ℝ) (n : ℕ) :
    deningerCalderonWittGammaModularScalarTransport (-a)
        (deningerCalderonWittCrossPrimeGammaWitness hpq) p q n n =
      (deningerCalderonWittGammaReflectionSewingCost a p q n : ℂ) *
        deningerCalderonWittGammaModularScalarTransport a
          (deningerCalderonWittCrossPrimeGammaWitness hpq) p q n n := by
  rw [deningerCalderonWittGammaModularScalarTransport_crossPrimeWitness,
    deningerCalderonWittGammaModularScalarTransport_crossPrimeWitness]
  exact_mod_cast
    xiGammaEulerPrimitiveModularExterior_reflection_eq_sewingCost_mul
      a p q n

/-- The actual transported witness in the sewing law is nonzero. -/
theorem
    deningerCalderonWittGammaModularScalarTransport_crossPrimeWitness_ne_zero
    {p q : Nat.Primes} (hpq : p ≠ q)
    (a : ℝ) (n : ℕ) :
    deningerCalderonWittGammaModularScalarTransport a
        (deningerCalderonWittCrossPrimeGammaWitness hpq) p q n n ≠ 0 := by
  rw [deningerCalderonWittGammaModularScalarTransport_crossPrimeWitness]
  exact_mod_cast
    xiGammaEulerPrimitiveModularExterior_ne_zero_sameDepth hpq a n

/--
The source rates expose the exact sewing exponent: positive displacement
produces exponential growth in common valuation depth.
-/
theorem deningerCalderonWittGammaReflectionSewingCost_eq_exp
    (a : ℝ) (p q : Nat.Primes) (n : ℕ) :
    deningerCalderonWittGammaReflectionSewingCost a p q n =
      Real.exp
        ((2 * a * (Real.log (p : ℝ) + Real.log (q : ℝ))) *
          ((n : ℝ) + 1)) := by
  rw [deningerCalderonWittGammaReflectionSewingCost,
    xiGammaEulerPrimitiveModularRate_eq_neg_two_halfHeight,
    xiGammaEulerPrimitiveModularRate_eq_neg_two_halfHeight]
  unfold xiGammaEulerBoundaryHalfHeight
  congr 1
  ring_nf

/--
The exact reflection sewing cost dominates every finite Rees order in the
reciprocal depth scale `(n+1)⁻¹`.  This is the required beyond-finite-Rees
singularity, proved on the concrete transported cross-prime witness above.
-/
theorem
    deningerCalderonWittGammaReflectionSewingCost_exceeds_every_finiteReesOrder
    {a : ℝ} (ha : 0 < a) (p q : Nat.Primes) :
    ∀ K : ℕ,
      (fun n : ℕ => ((n : ℝ) + 1) ^ K) =o[atTop]
        fun n : ℕ =>
          deningerCalderonWittGammaReflectionSewingCost a p q n := by
  intro K
  let c : ℝ :=
    2 * a * (Real.log (p : ℝ) + Real.log (q : ℝ))
  have hpLog : 0 < Real.log (p : ℝ) :=
    Real.log_pos (by exact_mod_cast p.property.one_lt)
  have hqLog : 0 < Real.log (q : ℝ) :=
    Real.log_pos (by exact_mod_cast q.property.one_lt)
  have hc : 0 < c := by
    dsimp only [c]
    positivity
  have ht :
      Tendsto (fun n : ℕ => c * ((n : ℝ) + 1)) atTop atTop :=
    (tendsto_natCast_atTop_atTop.atTop_add
      tendsto_const_nhds).const_mul_atTop hc
  have hbase :=
    (Real.isLittleO_pow_exp_atTop (n := K)).comp_tendsto ht
  have hcK : c ^ K ≠ 0 := pow_ne_zero K hc.ne'
  have hscaled := hbase.const_mul_left (c ^ K)⁻¹
  apply hscaled.congr'
  · filter_upwards with n
    simp only [Function.comp_apply, mul_pow]
    field_simp
  · filter_upwards with n
    rw [deningerCalderonWittGammaReflectionSewingCost_eq_exp]
    rfl

/-! ## Reflection-odd transport and admitted sector -/

theorem xiGammaEulerBoundaryHalfHeight_pos
    (i : Nat.Primes × ℕ) :
    0 < xiGammaEulerBoundaryHalfHeight i.1 i.2 := by
  unfold xiGammaEulerBoundaryHalfHeight
  exact mul_pos
    (div_pos (by positivity) (by norm_num))
    (Real.log_pos (by exact_mod_cast i.1.property.one_lt))

/--
The source reflection-odd coefficient detects every nonzero modular
displacement on a pair of distinct source heights.
-/
theorem xiGammaEulerPrimitiveReflectionOddExterior_ne_zero
    {a : ℝ} (ha : a ≠ 0)
    (i j : Nat.Primes × ℕ)
    (hheight :
      xiGammaEulerBoundaryHalfHeight i.1 i.2 ≠
        xiGammaEulerBoundaryHalfHeight j.1 j.2) :
    xiGammaEulerPrimitiveReflectionOddExterior a i j ≠ 0 := by
  let hi := xiGammaEulerBoundaryHalfHeight i.1 i.2
  let hj := xiGammaEulerBoundaryHalfHeight j.1 j.2
  let r :=
    xiGammaEulerPrimitiveModularRate i +
      xiGammaEulerPrimitiveModularRate j
  have hir : 0 < hi := xiGammaEulerBoundaryHalfHeight_pos i
  have hjr : 0 < hj := xiGammaEulerBoundaryHalfHeight_pos j
  have hr : r ≠ 0 := by
    rw [show r = -2 * (hi + hj) by
      dsimp only [r, hi, hj]
      rw [xiGammaEulerPrimitiveModularRate_eq_neg_two_halfHeight,
        xiGammaEulerPrimitiveModularRate_eq_neg_two_halfHeight]
      ring]
    positivity
  have harg : a * r ≠ (-a) * r := by
    intro h
    have htwo : (2 * a) * r = 0 := by
      calc
        (2 * a) * r = a * r - (-a) * r := by ring
        _ = 0 := sub_eq_zero.mpr h
    rcases mul_eq_zero.mp htwo with htwoa | hr0
    · apply ha
      linarith
    · exact hr hr0
  have hexp :
      Real.exp (a * r) ≠ Real.exp ((-a) * r) :=
    Real.exp_injective.ne harg
  have hA :
      xiGammaEulerPrimitiveBoundaryAmplitude 0 i *
          xiGammaEulerPrimitiveBoundaryAmplitude 0 j *
            (hi - hj) ≠ 0 := by
    apply mul_ne_zero
    · exact mul_ne_zero
        (xiGammaEulerPrimitiveBoundaryAmplitude_pos 0 i).ne'
        (xiGammaEulerPrimitiveBoundaryAmplitude_pos 0 j).ne'
    · exact sub_ne_zero.mpr hheight
  rw [xiGammaEulerPrimitiveReflectionOddExterior,
    xiGammaEulerPrimitiveModularExterior_eq,
    xiGammaEulerPrimitiveModularExterior_eq]
  change
    (xiGammaEulerPrimitiveBoundaryAmplitude 0 i *
          xiGammaEulerPrimitiveBoundaryAmplitude 0 j *
            Real.exp (a * r) * (hi - hj) -
        xiGammaEulerPrimitiveBoundaryAmplitude 0 i *
          xiGammaEulerPrimitiveBoundaryAmplitude 0 j *
            Real.exp ((-a) * r) * (hi - hj)) / 2 ≠ 0
  rw [show
    xiGammaEulerPrimitiveBoundaryAmplitude 0 i *
            xiGammaEulerPrimitiveBoundaryAmplitude 0 j *
              Real.exp (a * r) * (hi - hj) -
          xiGammaEulerPrimitiveBoundaryAmplitude 0 i *
            xiGammaEulerPrimitiveBoundaryAmplitude 0 j *
              Real.exp ((-a) * r) * (hi - hj) =
        (xiGammaEulerPrimitiveBoundaryAmplitude 0 i *
            xiGammaEulerPrimitiveBoundaryAmplitude 0 j * (hi - hj)) *
          (Real.exp (a * r) - Real.exp ((-a) * r)) by ring]
  exact div_ne_zero
    (mul_ne_zero hA (sub_ne_zero.mpr hexp))
    (by norm_num)

theorem xiGammaEulerPrimitiveReflectionOddExterior_eq_zero_iff
    (a : ℝ) (i j : Nat.Primes × ℕ)
    (hheight :
      xiGammaEulerBoundaryHalfHeight i.1 i.2 ≠
        xiGammaEulerBoundaryHalfHeight j.1 j.2) :
    xiGammaEulerPrimitiveReflectionOddExterior a i j = 0 ↔
      a = 0 := by
  constructor
  · contrapose!
    exact fun ha =>
      xiGammaEulerPrimitiveReflectionOddExterior_ne_zero
        ha i j hheight
  · rintro rfl
    exact xiGammaEulerPrimitiveReflectionOddExterior_zero i j

/-- Reflection-odd source transport before orientation. -/
def deningerCalderonWittGammaReflectionOddVectorTransport
    (a : ℝ) :
    deningerCalderonWittGlobalMilnorIncidence →ₗ[ℂ]
      DeningerCalderonWittGammaVectorProfile where
  toFun i p q e f :=
    deningerCalderonWittWeightedNonlocalExterior
      (xiGammaEulerPrimitiveReflectionOddExterior a (p, e) (q, f) : ℂ)
      p q i.1
  map_add' i j := by
    funext p q e f
    simp
  map_smul' c i := by
    funext p q e f
    simp

/-- Reflection-odd source transport followed by normalized orientation. -/
def deningerCalderonWittGammaReflectionOddScalarTransport
    (a : ℝ) :
    deningerCalderonWittGlobalMilnorIncidence →ₗ[ℂ]
      DeningerCalderonWittGammaScalarProfile :=
  deningerCalderonWittGammaOrientation.comp
    (deningerCalderonWittGammaReflectionOddVectorTransport a)

/--
Concrete admitted Hodge sector: exact source incidences with zero
reflection-odd primitive Gamma orientation at every ordered prime/depth
coordinate.
-/
def deningerCalderonWittGammaAdmittedHodgeSector
    (a : ℝ) :
    Submodule ℂ deningerCalderonWittGlobalMilnorIncidence :=
  LinearMap.ker (deningerCalderonWittGammaReflectionOddScalarTransport a)

theorem deningerCalderonWittGammaReflectionOddScalarTransport_crossPrimeWitness
    {p q : Nat.Primes} (hpq : p ≠ q)
    (a : ℝ) (e f : ℕ) :
    deningerCalderonWittGammaReflectionOddScalarTransport a
        (deningerCalderonWittCrossPrimeGammaWitness hpq) p q e f =
      (xiGammaEulerPrimitiveReflectionOddExterior
        a (p, e) (q, f) : ℂ) := by
  rw [deningerCalderonWittGammaReflectionOddScalarTransport,
    LinearMap.comp_apply, deningerCalderonWittGammaOrientation]
  change
    deningerCalderonWittAlgebraicCenterTrace q
        (deningerCalderonWittGammaReflectionOddVectorTransport a
          (deningerCalderonWittCrossPrimeGammaWitness hpq) p q e f) =
      (xiGammaEulerPrimitiveReflectionOddExterior a (p, e) (q, f) : ℂ)
  change
    deningerCalderonWittAlgebraicCenterTrace q
        (deningerCalderonWittWeightedNonlocalExterior
          (xiGammaEulerPrimitiveReflectionOddExterior
            a (p, e) (q, f) : ℂ)
          p q (deningerCalderonWittCrossPrimeGammaWitness hpq).1) =
      (xiGammaEulerPrimitiveReflectionOddExterior a (p, e) (q, f) : ℂ)
  rw [deningerCalderonWittWeightedNonlocalExterior_crossPrimeWitness
    hpq, map_smul]
  have htrace :
      deningerCalderonWittAlgebraicCenterTrace q
          (deningerPrimeFinitePacketGaugeAlgebraicFirstMode q
            (deningerCalderonWittAlgebraicUnitPacket q)) =
        1 := by
    change
      deningerCalderonWittAlgebraicPacketTrace q
          ((deningerPrimeFinitePacketGaugeAlgebraicFirstModeEquiv q).symm
            ((deningerPrimeFinitePacketGaugeAlgebraicFirstModeEquiv q)
              (deningerCalderonWittAlgebraicUnitPacket q))) =
        1
    rw [(deningerPrimeFinitePacketGaugeAlgebraicFirstModeEquiv q).symm_apply_apply,
      deningerCalderonWittAlgebraicPacketTrace_unit]
  rw [htrace, smul_eq_mul, mul_one]

/--
Exact sector classification on a canonical source boundary.  Membership is
neither assumed nor installed: it is equivalent to zero modular
displacement.
-/
theorem deningerCalderonWittCrossPrimeGammaWitness_mem_admittedHodgeSector_iff
    {p q : Nat.Primes} (hpq : p ≠ q)
    (a : ℝ) (e f : ℕ)
    (hheight :
      xiGammaEulerBoundaryHalfHeight p e ≠
        xiGammaEulerBoundaryHalfHeight q f) :
    deningerCalderonWittCrossPrimeGammaWitness hpq ∈
        deningerCalderonWittGammaAdmittedHodgeSector a ↔
      a = 0 := by
  constructor
  · intro hmem
    have hzero :
        deningerCalderonWittGammaReflectionOddScalarTransport a
          (deningerCalderonWittCrossPrimeGammaWitness hpq) = 0 :=
      (LinearMap.mem_ker).mp hmem
    have heval :
        deningerCalderonWittGammaReflectionOddScalarTransport a
            (deningerCalderonWittCrossPrimeGammaWitness hpq) p q e f =
          0 := by
      rw [hzero]
      rfl
    rw [
      deningerCalderonWittGammaReflectionOddScalarTransport_crossPrimeWitness
        hpq] at heval
    have hreal :
        xiGammaEulerPrimitiveReflectionOddExterior
            a (p, e) (q, f) = 0 := by
      exact_mod_cast heval
    exact
      (xiGammaEulerPrimitiveReflectionOddExterior_eq_zero_iff
        a (p, e) (q, f) hheight).mp hreal
  · rintro rfl
    rw [deningerCalderonWittGammaAdmittedHodgeSector, LinearMap.mem_ker]
    funext p' q' e' f'
    simp [deningerCalderonWittGammaReflectionOddScalarTransport,
      deningerCalderonWittGammaReflectionOddVectorTransport,
      deningerCalderonWittGammaOrientation,
      deningerCalderonWittWeightedNonlocalExterior_zero,
      xiGammaEulerPrimitiveReflectionOddExterior_zero]

/--
Assumption-free same-depth classification: every canonical cross-prime
incidence lies in the admitted sector exactly at zero modular displacement.
-/
theorem
    deningerCalderonWittCrossPrimeGammaWitness_mem_admittedHodgeSector_sameDepth_iff
    {p q : Nat.Primes} (hpq : p ≠ q)
    (a : ℝ) (n : ℕ) :
    deningerCalderonWittCrossPrimeGammaWitness hpq ∈
        deningerCalderonWittGammaAdmittedHodgeSector a ↔
      a = 0 :=
  deningerCalderonWittCrossPrimeGammaWitness_mem_admittedHodgeSector_iff
    hpq a n n
    (xiGammaEulerBoundaryHalfHeight_ne_of_primes_ne_sameDepth hpq n)

/-! ## Green-relative realization -/

/--
Relative source class for the concrete reflection-balanced Gamma sector.
-/
def deningerCalderonWittGammaRelativeBoundaryClass
    (a : ℝ)
    (w : ⋀[ℂ]^(2 : ℕ) DeningerCalderonWittAlgebraicGlobalDegreeOne) :=
  deningerCalderonWittGlobalRelativeBoundaryClass
    (deningerCalderonWittGammaAdmittedHodgeSector a) w

/--
Green-intertwining law: the relative class vanishes exactly when the
canonical Green primitive has zero singular reflection-odd Gamma transport.
-/
theorem deningerCalderonWittGammaRelativeBoundaryClass_eq_zero_iff
    (a : ℝ)
    (w : ⋀[ℂ]^(2 : ℕ) DeningerCalderonWittAlgebraicGlobalDegreeOne)
    (hcocycle :
      deningerCalderonWittAlgebraicGlobalExteriorCup w = 0) :
    deningerCalderonWittGammaRelativeBoundaryClass a w = 0 ↔
      deningerCalderonWittGammaReflectionOddScalarTransport a
        (deningerCalderonWittGlobalMilnorGreenRetraction w) = 0 := by
  rw [deningerCalderonWittGammaRelativeBoundaryClass,
    deningerCalderonWittGlobalRelativeBoundaryClass_eq_zero_iff
      (deningerCalderonWittGammaAdmittedHodgeSector a) w hcocycle]
  rfl

end

end RHTower
