import GaloisForLFunctions.HTGeometry.QuadraticQuantumDetectorRepresentation
import GaloisForLFunctions.HTGeometry.UniversalPrincipalSymbolCompletion

/-!
# Quadratic-width principal-symbol completion

The universal scalar-preserving construction needs only detector grades zero, one, and two.  This
module couples the quadratic quantum detector to the cyclic clock and proves exact preservation of
an arbitrary represented degree-`d` scalar law.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

universe u v

variable {K : Type u} [Field K] [CharZero K]
  {M : Type v} [AddCommGroup M] [Module K M]
  {d n : ℕ} [NeZero d] [Fact (1 < d)]

/-- Clocked amplitudes on the vacuum, one-event, and two-event detector grades. -/
abbrev QuadraticPrincipalCompletionState (M : Type v) (n d : ℕ) :=
  QuadraticQuantumDetectorIndex n → ZMod d → M

/-- Lift an internal operator through the cyclic clock on the quadratic detector packet. -/
def quadraticCompletionClockLift
    (q : K) (hq : q ^ d = 1) (A : Module.End K M) :
    Module.End K (QuadraticPrincipalCompletionState M n d) where
  toFun f x k := finiteQuantumCharacter d q hq k • A (f x k)
  map_add' f g := by
    funext x k
    simp [smul_add]
  map_smul' c f := by
    funext x k
    simp [smul_smul, mul_comm]

/-- Clock lifting is linear in the internal operator. -/
def quadraticCompletionClockLiftLinear
    (q : K) (hq : q ^ d = 1) :
    Module.End K M →ₗ[K]
      Module.End K (QuadraticPrincipalCompletionState M n d) where
  toFun := quadraticCompletionClockLift (n := n) q hq
  map_add' A B := by
    apply LinearMap.ext
    intro f
    funext x k
    simp [quadraticCompletionClockLift, smul_add]
  map_smul' c A := by
    apply LinearMap.ext
    intro f
    funext x k
    simp [quadraticCompletionClockLift, smul_smul, mul_comm]

/-- The quadratic detector generator, with one simultaneous cyclic clock shift. -/
def quadraticCompletionDetectorGenerator
    (q : K) (i : Fin n) :
    Module.End K (QuadraticPrincipalCompletionState M n d) where
  toFun f x k :=
    quadraticQuantumDetectorGenerator (M := M) q i (fun y ↦ f y (k - 1)) x
  map_add' f g := by
    funext x k
    change quadraticQuantumDetectorGenerator (M := M) q i
        ((fun y ↦ f y (k - 1)) + (fun y ↦ g y (k - 1))) x = _
    rw [map_add]
    rfl
  map_smul' c f := by
    funext x k
    change quadraticQuantumDetectorGenerator (M := M) q i
        (c • (fun y ↦ f y (k - 1))) x = _
    rw [map_smul]
    rfl

/-- Clocked quadratic detector generators retain ordered `q`-commutation. -/
theorem quadraticCompletionDetectorGenerator_mul_of_lt
    (q : K) {i j : Fin n} (hij : i < j) :
    quadraticCompletionDetectorGenerator (M := M) (d := d) q i *
        quadraticCompletionDetectorGenerator (M := M) (d := d) q j =
      q • (quadraticCompletionDetectorGenerator (M := M) (d := d) q j *
        quadraticCompletionDetectorGenerator (M := M) (d := d) q i) := by
  apply LinearMap.ext
  intro f
  funext x k
  let slice : QuadraticQuantumDetectorState M n := fun y ↦ f y (k - 1 - 1)
  have hqcomm := LinearMap.congr_fun
    (quadraticQuantumDetectorGenerator_mul_of_lt (M := M) q hij) slice
  have hx := congrFun hqcomm x
  simpa [quadraticCompletionDetectorGenerator, Module.End.mul_apply, slice] using hx

/-- Every clocked quadratic detector generator remains square-zero. -/
theorem quadraticCompletionDetectorGenerator_sq
    (q : K) (i : Fin n) :
    (quadraticCompletionDetectorGenerator (M := M) (d := d) q i) ^ 2 = 0 := by
  apply LinearMap.ext
  intro f
  funext x k
  let slice : QuadraticQuantumDetectorState M n := fun y ↦ f y (k - 1 - 1)
  have hsq := LinearMap.congr_fun
    (quadraticQuantumDetectorGenerator_sq (M := M) q i) slice
  have hx := congrFun hsq x
  simpa [quadraticCompletionDetectorGenerator, Module.End.mul_apply, pow_two, slice] using hx

/-- Every clocked quadratic detector generator has zero `d`th power. -/
theorem quadraticCompletionDetectorGenerator_pow_degree
    (q : K) (i : Fin n) :
    (quadraticCompletionDetectorGenerator (M := M) (d := d) q i) ^ d = 0 := by
  have hd : 2 ≤ d := Nat.succ_le_iff.mpr Fact.out
  let G := quadraticCompletionDetectorGenerator (M := M) (d := d) q i
  have hdegree : d = 2 + (d - 2) := by omega
  have hpow : G ^ d = G ^ (2 + (d - 2)) :=
    congrArg (fun r : ℕ ↦ G ^ r) hdegree
  rw [show quadraticCompletionDetectorGenerator (M := M) (d := d) q i = G from rfl,
    hpow, pow_add, show G ^ 2 = 0 by
      exact quadraticCompletionDetectorGenerator_sq q i]
  simp

/-- The clocked quadratic detector pencil. -/
def quadraticCompletionDetectorSymbol (q : K) :
    (Fin n → K) →ₗ[K]
      Module.End K (QuadraticPrincipalCompletionState M n d) :=
  quantumGeneratorSymbol
    (fun i : Fin n ↦ quadraticCompletionDetectorGenerator (M := M) (d := d) q i)

/-- Every value of the clocked quadratic detector pencil has zero `d`th power. -/
theorem quadraticCompletionDetectorSymbol_pow_degree_zero
    (q : K) (hq : IsPrimitiveRoot q d) (c : Fin n → K) :
    (quadraticCompletionDetectorSymbol (M := M) (d := d) q c) ^ d = 0 := by
  rw [quadraticCompletionDetectorSymbol, quantumGeneratorSymbol,
    Fintype.linearCombination_apply,
    quantumMultinomial_fin_smul_pow_primitive hq
      (lt_trans Nat.zero_lt_one Fact.out)
      (fun i : Fin n ↦ quadraticCompletionDetectorGenerator (M := M) (d := d) q i) c
      (fun i j hij ↦ quadraticCompletionDetectorGenerator_mul_of_lt q hij)]
  simp [quadraticCompletionDetectorGenerator_pow_degree]

/-- Exact power formula for the quadratic clock lift. -/
theorem quadraticCompletionClockLift_pow_apply
    (q : K) (hq : q ^ d = 1) (A : Module.End K M) :
    ∀ r : ℕ, ∀ f : QuadraticPrincipalCompletionState M n d,
      ∀ x : QuadraticQuantumDetectorIndex n, ∀ k : ZMod d,
      ((quadraticCompletionClockLift (n := n) q hq A) ^ r) f x k =
        (finiteQuantumCharacter d q hq k) ^ r • (A ^ r) (f x k)
  | 0, f, x, k => by simp
  | r + 1, f, x, k => by
      rw [pow_succ, Module.End.mul_apply,
        quadraticCompletionClockLift_pow_apply q hq A r]
      simp only [quadraticCompletionClockLift, LinearMap.coe_mk, AddHom.coe_mk,
        map_smul, smul_smul, pow_succ]
      rfl

/-- The quadratic clock lift preserves a scalar `d`th-power relation. -/
theorem quadraticCompletionClockLift_pow_degree
    (q : K) (hq : q ^ d = 1) (A : Module.End K M) (F : K)
    (hA : A ^ d = F • LinearMap.id) :
    (quadraticCompletionClockLift (n := n) q hq A) ^ d =
      F • LinearMap.id := by
  apply LinearMap.ext
  intro f
  funext x k
  rw [quadraticCompletionClockLift_pow_apply,
    finiteQuantumCharacter_pow_degree, hA]
  simp

/-- Internal endomorphisms commute through the purely coordinatewise quadratic detector action. -/
theorem map_quadraticQuantumDetectorGenerator
    (q : K) (A : Module.End K M) (i : Fin n)
    (f : QuadraticQuantumDetectorState M n) (x : QuadraticQuantumDetectorIndex n) :
    A (quadraticQuantumDetectorGenerator (M := M) q i f x) =
      quadraticQuantumDetectorGenerator (M := M) q i (fun y ↦ A (f y)) x := by
  cases x with
  | root => simp [quadraticQuantumDetectorGenerator]
  | single j =>
      by_cases hji : j = i <;> simp [quadraticQuantumDetectorGenerator, hji]
  | pair p =>
      have hne : p.upper ≠ p.lower := ne_of_gt p.isLt
      by_cases hil : i = p.lower
      · simp [quadraticQuantumDetectorGenerator, hil, map_smul]
      · by_cases hiu : i = p.upper
        · subst i
          simp [quadraticQuantumDetectorGenerator, hil, hne]
        · simp [quadraticQuantumDetectorGenerator, hil, hiu]

/-- The clock sector `q`-commutes with every quadratic detector generator. -/
theorem quadraticCompletionClockLift_mul_detectorGenerator
    (q : K) (hq : q ^ d = 1) (A : Module.End K M) (i : Fin n) :
    quadraticCompletionClockLift (n := n) q hq A *
        quadraticCompletionDetectorGenerator (M := M) (d := d) q i =
      q • (quadraticCompletionDetectorGenerator (M := M) (d := d) q i *
        quadraticCompletionClockLift (n := n) q hq A) := by
  apply LinearMap.ext
  intro f
  funext x k
  rw [show (quadraticCompletionClockLift (n := n) q hq A *
      quadraticCompletionDetectorGenerator (M := M) (d := d) q i) f x k =
      finiteQuantumCharacter d q hq k •
        A (quadraticQuantumDetectorGenerator (M := M) q i
          (fun y ↦ f y (k - 1)) x) by rfl]
  rw [map_quadraticQuantumDetectorGenerator]
  have hclock := finiteQuantumCharacter_sub_one_mul q hq k
  rw [← hclock]
  let χ : K := finiteQuantumCharacter d q hq (k - 1)
  let g : QuadraticQuantumDetectorState M n := fun y ↦ A (f y (k - 1))
  change (χ * q) • quadraticQuantumDetectorGenerator (M := M) q i g x =
    q • quadraticQuantumDetectorGenerator (M := M) q i (χ • g) x
  rw [map_smul]
  simp [smul_smul, mul_comm]

/-- The clock sector `q`-commutes with every quadratic detector-pencil value. -/
theorem quadraticCompletionClockLift_mul_detectorSymbol
    (q : K) (hq : q ^ d = 1) (A : Module.End K M) (c : Fin n → K) :
    quadraticCompletionClockLift (n := n) q hq A *
        quadraticCompletionDetectorSymbol (M := M) (d := d) q c =
      q • (quadraticCompletionDetectorSymbol (M := M) (d := d) q c *
        quadraticCompletionClockLift (n := n) q hq A) := by
  classical
  rw [quadraticCompletionDetectorSymbol, quantumGeneratorSymbol,
    Fintype.linearCombination_apply, Finset.mul_sum, Finset.sum_mul, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  calc
    quadraticCompletionClockLift (n := n) q hq A *
        (c i • quadraticCompletionDetectorGenerator (M := M) (d := d) q i) =
      c i • (quadraticCompletionClockLift (n := n) q hq A *
        quadraticCompletionDetectorGenerator (M := M) (d := d) q i) := by simp
    _ = c i • (q •
        (quadraticCompletionDetectorGenerator (M := M) (d := d) q i *
          quadraticCompletionClockLift (n := n) q hq A)) := by
      rw [quadraticCompletionClockLift_mul_detectorGenerator]
    _ = q • ((c i • quadraticCompletionDetectorGenerator (M := M) (d := d) q i) *
        quadraticCompletionClockLift (n := n) q hq A) := by
      simp [smul_smul]
      congr 1
      ring

/-- Add the quadratic-width detector to an arbitrary scalar pencil. -/
def quadraticWidthPrincipalSymbolCompletion
    (q : K) (hq : q ^ d = 1)
    (A₀ : (Fin n → K) →ₗ[K] Module.End K M) :
    (Fin n → K) →ₗ[K]
      Module.End K (QuadraticPrincipalCompletionState M n d) :=
  (quadraticCompletionClockLiftLinear (n := n) q hq).comp A₀ +
    quadraticCompletionDetectorSymbol (M := M) (d := d) q

/-- **Quadratic-width scalar preservation.**  The three-grade detector changes no scalar law. -/
theorem quadraticWidthPrincipalSymbolCompletion_pow
    (q : K) (hq : IsPrimitiveRoot q d)
    (A₀ : (Fin n → K) →ₗ[K] Module.End K M) (F : (Fin n → K) → K)
    (hA₀ : ∀ c, (A₀ c) ^ d = F c • LinearMap.id) (c : Fin n → K) :
    (quadraticWidthPrincipalSymbolCompletion q hq.pow_eq_one A₀ c) ^ d =
      F c • LinearMap.id := by
  change (quadraticCompletionClockLift (n := n) q hq.pow_eq_one (A₀ c) +
    quadraticCompletionDetectorSymbol (M := M) (d := d) q c) ^ d = _
  rw [quantumBinomial_pow_primitive hq
      (lt_trans Nat.zero_lt_one Fact.out)
      (quadraticCompletionClockLift (n := n) q hq.pow_eq_one (A₀ c))
      (quadraticCompletionDetectorSymbol (M := M) (d := d) q c)
      (quadraticCompletionClockLift_mul_detectorSymbol
        q hq.pow_eq_one (A₀ c) c),
    quadraticCompletionClockLift_pow_degree q hq.pow_eq_one (A₀ c) (F c) (hA₀ c),
    quadraticCompletionDetectorSymbol_pow_degree_zero q hq]
  simp

@[simp]
theorem quadraticWidthPrincipalSymbolCompletion_basisFun
    (q : K) (hq : q ^ d = 1)
    (A₀ : (Fin n → K) →ₗ[K] Module.End K M) (i : Fin n) :
    quadraticWidthPrincipalSymbolCompletion q hq A₀ (Pi.basisFun K (Fin n) i) =
      quadraticCompletionClockLift (n := n) q hq
          (A₀ (Pi.basisFun K (Fin n) i)) +
        quadraticCompletionDetectorGenerator (M := M) (d := d) q i := by
  classical
  simp [quadraticWidthPrincipalSymbolCompletion, quadraticCompletionClockLiftLinear,
    quadraticCompletionDetectorSymbol, quantumGeneratorSymbol]

/-- Completed vacuum at detector grade zero and clock degree zero. -/
def quadraticPrincipalCompletionRoot (m : M) :
    QuadraticPrincipalCompletionState M n d :=
  Pi.single .root (Pi.single 0 m)

theorem quadraticPrincipalCompletionRoot_ne_zero
    (m : M) (hm : m ≠ 0) :
    quadraticPrincipalCompletionRoot (n := n) (d := d) m ≠ 0 := by
  classical
  intro hzero
  have hgrade := congrFun hzero (.root : QuadraticQuantumDetectorIndex n)
  have hclock := congrFun hgrade (0 : ZMod d)
  exact hm (by simpa [quadraticPrincipalCompletionRoot] using hclock)

/-- Two clocked detector shifts send the vacuum to the corresponding pair at clock degree two. -/
theorem quadraticCompletionDetectorPairOperator_root
    (q : K) (m : M) (p : QuantumLawPair (Fin n)) :
    quantumPairOperator
        (fun i : Fin n ↦ quadraticCompletionDetectorGenerator (M := M) (d := d) q i) p
        (quadraticPrincipalCompletionRoot (n := n) (d := d) m) =
      Pi.single (.pair p) (Pi.single (2 : ZMod d) m) := by
  classical
  funext x k
  change quantumPairOperator
      (fun i : Fin n ↦ quadraticQuantumDetectorGenerator (M := M) q i) p
      (fun y ↦ quadraticPrincipalCompletionRoot (n := n) (d := d) m y (k - 1 - 1)) x = _
  by_cases hk : k = 2
  · subst k
    have htwo : (2 : ZMod d) - 1 - 1 = 0 :=
      (zmod_sub_one_sub_one_eq_zero_iff (2 : ZMod d)).2 rfl
    have hslice :
        (fun y ↦ quadraticPrincipalCompletionRoot (n := n) (d := d) m y
          ((2 : ZMod d) - 1 - 1)) =
        quadraticQuantumDetectorRoot (n := n) m := by
      funext y
      by_cases hy : y = (.root : QuadraticQuantumDetectorIndex n)
      · subst y
        simp [quadraticPrincipalCompletionRoot, quadraticQuantumDetectorRoot, htwo]
      · simp [quadraticPrincipalCompletionRoot, quadraticQuantumDetectorRoot,
          Pi.single_apply, htwo, hy]
    rw [hslice, quadraticQuantumDetectorPairOperator_root]
    by_cases hx : x = (.pair p : QuadraticQuantumDetectorIndex n)
    · subst x
      simp [quadraticQuantumDetectorPairState, Pi.single_apply]
    · simp [quadraticQuantumDetectorPairState, Pi.single_apply, hx]
  · have hclock : k - 1 - 1 ≠ 0 := fun h ↦
      hk ((zmod_sub_one_sub_one_eq_zero_iff k).mp h)
    have hslice :
        (fun y ↦ quadraticPrincipalCompletionRoot (n := n) (d := d) m y (k - 1 - 1)) = 0 := by
      funext y
      by_cases hy : y = (.root : QuadraticQuantumDetectorIndex n)
      · subst y
        simp [quadraticPrincipalCompletionRoot, Pi.single_apply, hclock]
      · simp [quadraticPrincipalCompletionRoot, Pi.single_apply, hy]
    rw [hslice, map_zero]
    by_cases hx : x = (.pair p : QuadraticQuantumDetectorIndex n)
    · subst x
      simp [Pi.single_apply, hk]
    · simp [Pi.single_apply, hx]

/-- Read an endomorphism on the completed vacuum at every pair grade and clock degree. -/
def quadraticPrincipalCompletionPairReadout (m : M) :
    Module.End K (QuadraticPrincipalCompletionState M n d) →ₗ[K]
      (QuantumLawPair (Fin n) → ZMod d → M) where
  toFun T p k := T (quadraticPrincipalCompletionRoot (n := n) (d := d) m) (.pair p) k
  map_add' T U := by
    funext p k
    simp
  map_smul' c T := by
    funext p k
    simp

theorem quadraticPrincipalCompletionPairReadout_detectorPair
    (q : K) (m : M) (r : QuantumLawPair (Fin n)) :
    quadraticPrincipalCompletionPairReadout (n := n) (d := d) m
        (quantumPairOperator
          (fun i : Fin n ↦ quadraticCompletionDetectorGenerator (M := M) (d := d) q i) r) =
      Pi.single r (Pi.single (2 : ZMod d) m) := by
  classical
  funext p k
  change (quantumPairOperator
      (fun i : Fin n ↦ quadraticCompletionDetectorGenerator (M := M) (d := d) q i) r)
      (quadraticPrincipalCompletionRoot (n := n) (d := d) m) (.pair p) k = _
  rw [quadraticCompletionDetectorPairOperator_root]
  by_cases hpr : p = r
  · subst p
    simp
  · have hindex :
        (QuadraticQuantumDetectorIndex.pair r : QuadraticQuantumDetectorIndex n) ≠ .pair p := by
      intro h
      apply hpr
      injection h with hrp
      exact hrp.symm
    simp [Pi.single_apply, hpr, hindex.symm]

theorem quadraticPrincipalCompletionPairReadout_clock_mul_clock
    (q : K) (hq : q ^ d = 1) (m : M) (A B : Module.End K M) :
    quadraticPrincipalCompletionPairReadout (n := n) (d := d) m
        (quadraticCompletionClockLift (n := n) q hq A *
          quadraticCompletionClockLift (n := n) q hq B) = 0 := by
  funext p k
  simp [quadraticPrincipalCompletionPairReadout, Module.End.mul_apply,
    quadraticCompletionClockLift, quadraticPrincipalCompletionRoot]

theorem quadraticPrincipalCompletionPairReadout_clock_mul_detector
    (q : K) (hq : q ^ d = 1) (m : M) (A : Module.End K M) (i : Fin n) :
    quadraticPrincipalCompletionPairReadout (n := n) (d := d) m
        (quadraticCompletionClockLift (n := n) q hq A *
          quadraticCompletionDetectorGenerator (M := M) (d := d) q i) = 0 := by
  funext p k
  simp [quadraticPrincipalCompletionPairReadout, Module.End.mul_apply,
    quadraticCompletionClockLift, quadraticCompletionDetectorGenerator,
    quadraticQuantumDetectorGenerator, quadraticPrincipalCompletionRoot]

theorem quadraticPrincipalCompletionPairReadout_detector_mul_clock
    (q : K) (hq : q ^ d = 1) (m : M) (A : Module.End K M) (i : Fin n) :
    quadraticPrincipalCompletionPairReadout (n := n) (d := d) m
        (quadraticCompletionDetectorGenerator (M := M) (d := d) q i *
          quadraticCompletionClockLift (n := n) q hq A) = 0 := by
  funext p k
  simp [quadraticPrincipalCompletionPairReadout, Module.End.mul_apply,
    quadraticCompletionClockLift, quadraticCompletionDetectorGenerator,
    quadraticQuantumDetectorGenerator, quadraticPrincipalCompletionRoot]

theorem quadraticPrincipalCompletionPairReadout_detectorBracket
    (q : K) (m : M) (r : QuantumLawPair (Fin n)) :
    quadraticPrincipalCompletionPairReadout (n := n) (d := d) m
        (quadraticCompletionDetectorGenerator (M := M) (d := d) q r.lower *
            quadraticCompletionDetectorGenerator (M := M) (d := d) q r.upper -
          quadraticCompletionDetectorGenerator (M := M) (d := d) q r.upper *
            quadraticCompletionDetectorGenerator (M := M) (d := d) q r.lower) =
      (q - 1) • Pi.single r (Pi.single (2 : ZMod d) m) := by
  classical
  rw [quadraticCompletionDetectorGenerator_mul_of_lt q r.isLt, map_sub, map_smul]
  change q • quadraticPrincipalCompletionPairReadout (n := n) (d := d) m
      (quantumPairOperator
        (fun i : Fin n ↦ quadraticCompletionDetectorGenerator (M := M) (d := d) q i) r) -
    quadraticPrincipalCompletionPairReadout (n := n) (d := d) m
      (quantumPairOperator
        (fun i : Fin n ↦ quadraticCompletionDetectorGenerator (M := M) (d := d) q i) r) = _
  rw [quadraticPrincipalCompletionPairReadout_detectorPair]
  module

theorem quadraticPrincipalCompletionPairReadout_principalBracketPair
    (q : K) (hq : q ^ d = 1)
    (A₀ : (Fin n → K) →ₗ[K] Module.End K M) (m : M)
    (r : QuantumLawPair (Fin n)) :
    quadraticPrincipalCompletionPairReadout (n := n) (d := d) m
        (principalBracketPair (quadraticWidthPrincipalSymbolCompletion q hq A₀) r) =
      (q - 1) • Pi.single r (Pi.single (2 : ZMod d) m) := by
  classical
  rw [principalBracketPair,
    quadraticWidthPrincipalSymbolCompletion_basisFun,
    quadraticWidthPrincipalSymbolCompletion_basisFun]
  simp only [mul_add, add_mul, map_sub, map_add]
  rw [quadraticPrincipalCompletionPairReadout_clock_mul_clock,
    quadraticPrincipalCompletionPairReadout_clock_mul_detector,
    quadraticPrincipalCompletionPairReadout_detector_mul_clock,
    quadraticPrincipalCompletionPairReadout_clock_mul_clock,
    quadraticPrincipalCompletionPairReadout_clock_mul_detector,
    quadraticPrincipalCompletionPairReadout_detector_mul_clock]
  simpa using quadraticPrincipalCompletionPairReadout_detectorBracket
    (d := d) q m r

theorem quadraticWidthPrincipalSymbolCompletion_principalBracketPair_linearIndependent
    (q : K) (hq : IsPrimitiveRoot q d)
    (A₀ : (Fin n → K) →ₗ[K] Module.End K M)
    (m : M) (hm : m ≠ 0) :
    LinearIndependent K
      (principalBracketPair
        (quadraticWidthPrincipalSymbolCompletion q hq.pow_eq_one A₀)) := by
  classical
  apply LinearIndependent.of_comp
    (quadraticPrincipalCompletionPairReadout (n := n) (d := d) m)
  have hclock : (Pi.single (2 : ZMod d) m : ZMod d → M) ≠ 0 := by
    intro hzero
    apply hm
    simpa using congrFun hzero (2 : ZMod d)
  have hcoefficient : q - 1 ≠ 0 := sub_ne_zero.mpr (hq.ne_one Fact.out)
  have hcoordinate : ∀ _r : QuantumLawPair (Fin n),
      (q - 1) • (Pi.single (2 : ZMod d) m : ZMod d → M) ≠ 0 := by
    intro _r
    exact smul_ne_zero hcoefficient hclock
  have hsingle := Pi.linearIndependent_single_of_ne_zero (R := K) hcoordinate
  have heq :
      (fun r : QuantumLawPair (Fin n) ↦
        (q - 1) • (Pi.single r (Pi.single (2 : ZMod d) m : ZMod d → M) :
          QuantumLawPair (Fin n) → ZMod d → M)) =
      (fun r : QuantumLawPair (Fin n) ↦
        (Pi.single r ((q - 1) • (Pi.single (2 : ZMod d) m : ZMod d → M)) :
          QuantumLawPair (Fin n) → ZMod d → M)) := by
    funext r
    ext p k
    by_cases hpr : p = r <;> simp [Pi.single_apply, hpr]
  have hstandard : LinearIndependent K
      (fun r : QuantumLawPair (Fin n) ↦
        (q - 1) • (Pi.single r (Pi.single (2 : ZMod d) m : ZMod d → M) :
          QuantumLawPair (Fin n) → ZMod d → M)) := by
    rw [heq]
    exact hsingle
  simpa [Function.comp_def,
    quadraticPrincipalCompletionPairReadout_principalBracketPair] using hstandard

/-- **Quadratic-width universal principal-symbol theorem.** -/
theorem quadraticWidthPrincipalSymbolCompletion_endomorphismCommutatorMap_injective
    (q : K) (hq : IsPrimitiveRoot q d)
    (A₀ : (Fin n → K) →ₗ[K] Module.End K M)
    (m : M) (hm : m ≠ 0) :
    Function.Injective
      (endomorphismCommutatorMap
        (quadraticWidthPrincipalSymbolCompletion q hq.pow_eq_one A₀)) :=
  endomorphismCommutatorMap_injective_of_principalBracketPair_linearIndependent
    (quadraticWidthPrincipalSymbolCompletion q hq.pow_eq_one A₀)
    (quadraticWidthPrincipalSymbolCompletion_principalBracketPair_linearIndependent
      q hq A₀ m hm)

/-- **Quadratic-width before-time horizon theorem.**  A three-grade detector preserves the exact
scalar zero-locus horizon and remembers every law-space two-plane. -/
theorem quadraticWidthPrincipalSymbolCompletion_fieldHorizon_and_maximalPrincipalSymbol
    (q : K) (hq : IsPrimitiveRoot q d)
    (A₀ : (Fin n → K) →ₗ[K] Module.End K M)
    (F : (Fin n → K) → K)
    (hA₀ : ∀ c, (A₀ c) ^ d = F c • LinearMap.id)
    (m : M) (hm : m ≠ 0) :
    ({c : Fin n → K | ¬ AlgebraicIndependent K
        (generalizedCliffordShiftFieldJet
          (quadraticWidthPrincipalSymbolCompletion q hq.pow_eq_one A₀ c)
          (quadraticPrincipalCompletionRoot (n := n) (d := d) m))} =
      {c : Fin n → K | F c = 0}) ∧
    Function.Injective
      (derivationCommutatorMap
        (generalizedCliffordShiftFieldDerivationLaw
          (quadraticWidthPrincipalSymbolCompletion q hq.pow_eq_one A₀))) := by
  constructor
  · apply generalizedCliffordShiftField_dependenceHorizon_eq_zeroLocus
      (quadraticWidthPrincipalSymbolCompletion q hq.pow_eq_one A₀) F d
      (Nat.ne_of_gt (lt_trans Nat.zero_lt_one Fact.out))
      (quadraticPrincipalCompletionRoot (n := n) (d := d) m)
      (quadraticPrincipalCompletionRoot_ne_zero m hm)
    exact quadraticWidthPrincipalSymbolCompletion_pow q hq A₀ F hA₀
  · rw [generalizedCliffordField_derivationCommutatorMap_injective_iff]
    exact quadraticWidthPrincipalSymbolCompletion_endomorphismCommutatorMap_injective
      q hq A₀ m hm

end

end GaloisForLFunctions.HTGeometry
