import GaloisForLFunctions.HTGeometry.LinearWidthThreeStepDetector
import GaloisForLFunctions.HTGeometry.UniversalPrincipalSymbolCompletion

/-!
# Linear-width principal-symbol completion above degree two

For scalar laws of degree at least three, the universal principal-symbol completion needs only a
linear number of detector states.  The scalar pencil is clocked by a primitive `d`th root, while a
`2n+1`-coordinate membrane detector is shifted around the same cyclic clock.  The two aggregate
pencils `q`-commute.  The detector pencil cubes to zero, hence has zero `d`th power, so the quantum
binomial theorem preserves the represented scalar law exactly.

The resulting completion has the same exact hypertranscendental dependence horizon and an
injective full exterior commutator symbol.  No pairwise quantum relation among detector generators
is required.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

universe u v

variable {K : Type u} [Field K] [CharZero K]
  {M : Type v} [AddCommGroup M] [Module K M]
  {d n : ℕ} [NeZero d] [Fact (1 < d)]

/-- Clocked amplitudes on the lower/membrane/upper detector boundary. -/
abbrev LinearPrincipalCompletionState (M : Type v) (n d : ℕ) :=
  CyclicClockState M (LinearWidthDetectorIndex n) d

omit [Fact (1 < d)] in
/-- The completed boundary has exactly `d(2n+1)` scalar coordinate slots. -/
theorem linearPrincipalCompletionCoordinate_card :
    Fintype.card (LinearWidthDetectorIndex n × ZMod d) = (2 * n + 1) * d := by
  rw [Fintype.card_prod, linearWidthDetectorIndex_card, ZMod.card]

/-- A membrane generator accompanied by one cyclic clock shift. -/
def linearCompletionDetectorGenerator (i : Fin n) :
    Module.End K (LinearPrincipalCompletionState M n d) where
  toFun f x k :=
    linearWidthDetectorGenerator (K := K) (M := M) i (fun y ↦ f y (k - 1)) x
  map_add' f g := by
    funext x k
    change linearWidthDetectorGenerator (K := K) (M := M) i
        ((fun y ↦ f y (k - 1)) + (fun y ↦ g y (k - 1))) x = _
    rw [map_add]
    rfl
  map_smul' c f := by
    funext x k
    change linearWidthDetectorGenerator (K := K) (M := M) i
        (c • (fun y ↦ f y (k - 1))) x = _
    rw [map_smul]
    rfl

/-- The clocked membrane detector pencil. -/
def linearCompletionDetectorSymbol :
    (Fin n → K) →ₗ[K]
      Module.End K (LinearPrincipalCompletionState M n d) :=
  quantumGeneratorSymbol
    (fun i : Fin n ↦ linearCompletionDetectorGenerator (K := K) (M := M) (d := d) i)

omit [NeZero d] [Fact (1 < d)] in
omit [CharZero K] in
@[simp]
theorem linearCompletionDetectorSymbol_basisFun (i : Fin n) :
    linearCompletionDetectorSymbol (K := K) (M := M) (d := d)
        (Pi.basisFun K (Fin n) i) =
      linearCompletionDetectorGenerator (K := K) (M := M) (d := d) i := by
  exact quantumGeneratorSymbol_basisFun
    (fun j : Fin n ↦ linearCompletionDetectorGenerator (K := K) (M := M) (d := d) j) i

omit [CharZero K] [NeZero d] [Fact (1 < d)] in
/-- A clocked detector value is the unclocked detector applied to the preceding clock slice. -/
theorem linearCompletionDetectorSymbol_apply
    (c : Fin n → K) (f : LinearPrincipalCompletionState M n d)
    (x : LinearWidthDetectorIndex n) (k : ZMod d) :
    linearCompletionDetectorSymbol (K := K) (M := M) (d := d) c f x k =
      linearWidthDetectorSymbol (K := K) (M := M) c
        (fun y ↦ f y (k - 1)) x := by
  classical
  simp [linearCompletionDetectorSymbol, linearWidthDetectorSymbol,
    quantumGeneratorSymbol, Fintype.linearCombination_apply,
    linearCompletionDetectorGenerator]

omit [CharZero K] [NeZero d] [Fact (1 < d)] in
/-- Clock shifting does not alter the three-step nilpotence of the aggregate detector pencil. -/
theorem linearCompletionDetectorSymbol_cube_zero
    (c : Fin n → K) :
    (linearCompletionDetectorSymbol (K := K) (M := M) (d := d) c) ^ 3 = 0 := by
  classical
  apply LinearMap.ext
  intro f
  funext x k
  let slice : LinearWidthDetectorState M n := fun y ↦ f y (k - 1 - 1 - 1)
  have hcube := LinearMap.congr_fun
    (linearWidthDetectorSymbol_cube_zero (K := K) (M := M) c) slice
  have hx := congrFun hcube x
  simpa [pow_succ, Module.End.mul_apply,
    linearCompletionDetectorSymbol_apply, slice] using hx

omit [CharZero K] [NeZero d] [Fact (1 < d)] in
/-- At every degree `d ≥ 3`, the clocked detector contributes zero to the scalar law. -/
theorem linearCompletionDetectorSymbol_pow_degree_zero
    (hd : 3 ≤ d) (c : Fin n → K) :
    (linearCompletionDetectorSymbol (K := K) (M := M) (d := d) c) ^ d = 0 := by
  let D := linearCompletionDetectorSymbol (K := K) (M := M) (d := d) c
  calc
    D ^ d = D ^ (3 + (d - 3)) := by congr 1 ; omega
    _ = D ^ 3 * D ^ (d - 3) := pow_add D 3 (d - 3)
    _ = 0 := by rw [linearCompletionDetectorSymbol_cube_zero]; simp

omit [CharZero K] in
/-- Internal endomorphisms commute through the coordinate-only membrane action. -/
theorem map_linearWidthDetectorGenerator
    (A : Module.End K M) (i : Fin n)
    (f : LinearWidthDetectorState M n) (x : LinearWidthDetectorIndex n) :
    A (linearWidthDetectorGenerator (K := K) (M := M) i f x) =
      linearWidthDetectorGenerator (K := K) (M := M) i
        (fun y ↦ A (f y)) x := by
  cases x with
  | lower j => simp
  | membrane => simp
  | upper j => by_cases hji : j = i <;> simp [hji]

omit [CharZero K] [Fact (1 < d)] in
/-- The scalar clock `q`-commutes with every clocked membrane generator. -/
theorem linearCompletionClockLift_mul_detectorGenerator
    (q : K) (hq : q ^ d = 1) (A : Module.End K M) (i : Fin n) :
    cyclicClockLift (ι := LinearWidthDetectorIndex n) q hq A *
        linearCompletionDetectorGenerator (K := K) (M := M) (d := d) i =
      q • (linearCompletionDetectorGenerator (K := K) (M := M) (d := d) i *
        cyclicClockLift (ι := LinearWidthDetectorIndex n) q hq A) := by
  apply LinearMap.ext
  intro f
  funext x k
  rw [show (cyclicClockLift (ι := LinearWidthDetectorIndex n) q hq A *
      linearCompletionDetectorGenerator (K := K) (M := M) (d := d) i) f x k =
      finiteQuantumCharacter d q hq k •
        A (linearWidthDetectorGenerator (K := K) (M := M) i
          (fun y ↦ f y (k - 1)) x) by rfl]
  rw [map_linearWidthDetectorGenerator]
  have hclock := finiteQuantumCharacter_sub_one_mul q hq k
  rw [← hclock]
  let χ : K := finiteQuantumCharacter d q hq (k - 1)
  let g : LinearWidthDetectorState M n := fun y ↦ A (f y (k - 1))
  change (χ * q) • linearWidthDetectorGenerator (K := K) (M := M) i g x =
    q • linearWidthDetectorGenerator (K := K) (M := M) i (χ • g) x
  rw [map_smul]
  simp [smul_smul, mul_comm]

omit [CharZero K] [Fact (1 < d)] in
/-- The scalar clock `q`-commutes with the entire membrane detector pencil. -/
theorem linearCompletionClockLift_mul_detectorSymbol
    (q : K) (hq : q ^ d = 1) (A : Module.End K M) (c : Fin n → K) :
    cyclicClockLift (ι := LinearWidthDetectorIndex n) q hq A *
        linearCompletionDetectorSymbol (K := K) (M := M) (d := d) c =
      q • (linearCompletionDetectorSymbol (K := K) (M := M) (d := d) c *
        cyclicClockLift (ι := LinearWidthDetectorIndex n) q hq A) := by
  classical
  rw [linearCompletionDetectorSymbol, quantumGeneratorSymbol,
    Fintype.linearCombination_apply, Finset.mul_sum, Finset.sum_mul, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  calc
    cyclicClockLift (ι := LinearWidthDetectorIndex n) q hq A *
        (c i • linearCompletionDetectorGenerator (K := K) (M := M) (d := d) i) =
      c i • (cyclicClockLift (ι := LinearWidthDetectorIndex n) q hq A *
        linearCompletionDetectorGenerator (K := K) (M := M) (d := d) i) := by simp
    _ = c i • (q •
        (linearCompletionDetectorGenerator (K := K) (M := M) (d := d) i *
          cyclicClockLift (ι := LinearWidthDetectorIndex n) q hq A)) := by
      rw [linearCompletionClockLift_mul_detectorGenerator]
    _ = q • ((c i •
        linearCompletionDetectorGenerator (K := K) (M := M) (d := d) i) *
          cyclicClockLift (ι := LinearWidthDetectorIndex n) q hq A) := by
      simp [smul_smul]
      congr 1
      ring

/-- Add the linear-width membrane detector to an arbitrary scalar pencil. -/
def linearWidthPrincipalSymbolCompletion
    (q : K) (hq : q ^ d = 1)
    (A₀ : (Fin n → K) →ₗ[K] Module.End K M) :
    (Fin n → K) →ₗ[K]
      Module.End K (LinearPrincipalCompletionState M n d) :=
  (cyclicClockLiftLinear (ι := LinearWidthDetectorIndex n) q hq).comp A₀ +
    linearCompletionDetectorSymbol (K := K) (M := M) (d := d)

/-- **Linear-width scalar preservation above degree two.** -/
theorem linearWidthPrincipalSymbolCompletion_pow
    (q : K) (hq : IsPrimitiveRoot q d) (hd : 3 ≤ d)
    (A₀ : (Fin n → K) →ₗ[K] Module.End K M) (F : (Fin n → K) → K)
    (hA₀ : ∀ c, (A₀ c) ^ d = F c • LinearMap.id) (c : Fin n → K) :
    (linearWidthPrincipalSymbolCompletion q hq.pow_eq_one A₀ c) ^ d =
      F c • LinearMap.id := by
  change (cyclicClockLift (ι := LinearWidthDetectorIndex n) q hq.pow_eq_one (A₀ c) +
    linearCompletionDetectorSymbol (K := K) (M := M) (d := d) c) ^ d = _
  rw [quantumBinomial_pow_primitive hq
      (lt_trans Nat.zero_lt_one Fact.out)
      (cyclicClockLift (ι := LinearWidthDetectorIndex n) q hq.pow_eq_one (A₀ c))
      (linearCompletionDetectorSymbol (K := K) (M := M) (d := d) c)
      (linearCompletionClockLift_mul_detectorSymbol
        q hq.pow_eq_one (A₀ c) c),
    cyclicClockLift_pow_degree (ι := LinearWidthDetectorIndex n) q hq.pow_eq_one (A₀ c) (F c) (hA₀ c),
    linearCompletionDetectorSymbol_pow_degree_zero hd]
  simp

omit [Fact (1 < d)] in
omit [CharZero K] in
@[simp]
theorem linearWidthPrincipalSymbolCompletion_basisFun
    (q : K) (hq : q ^ d = 1)
    (A₀ : (Fin n → K) →ₗ[K] Module.End K M) (i : Fin n) :
    linearWidthPrincipalSymbolCompletion q hq A₀ (Pi.basisFun K (Fin n) i) =
      cyclicClockLift (ι := LinearWidthDetectorIndex n) q hq
          (A₀ (Pi.basisFun K (Fin n) i)) +
        linearCompletionDetectorGenerator (K := K) (M := M) (d := d) i := by
  change cyclicClockLift (ι := LinearWidthDetectorIndex n) q hq
      (A₀ (Pi.basisFun K (Fin n) i)) +
      linearCompletionDetectorSymbol (K := K) (M := M) (d := d)
        (Pi.basisFun K (Fin n) i) = _
  rw [linearCompletionDetectorSymbol_basisFun]

/-- A fixed nonzero membrane state used to probe the exact scalar horizon. -/
def linearPrincipalCompletionRoot (m : M) :
    LinearPrincipalCompletionState M n d :=
  Pi.single .membrane (Pi.single 0 m)

omit [NeZero d] [Fact (1 < d)] in
theorem linearPrincipalCompletionRoot_ne_zero
    (m : M) (hm : m ≠ 0) :
    linearPrincipalCompletionRoot (n := n) (d := d) m ≠ 0 := by
  classical
  intro hzero
  have hgrade := congrFun hzero (.membrane : LinearWidthDetectorIndex n)
  have hclock := congrFun hgrade (0 : ZMod d)
  exact hm (by simpa [linearPrincipalCompletionRoot] using hclock)

/-- Pair `p` is tested by injecting its upper law coordinate into the lower boundary at clock zero. -/
def linearPrincipalCompletionPairInput
    (p : QuantumLawPair (Fin n)) (m : M) :
    LinearPrincipalCompletionState M n d :=
  Pi.single (.lower p.upper) (Pi.single 0 m)

/-- Read the private lower-to-upper matrix coefficient of every pair at every clock degree. -/
def linearPrincipalCompletionPairReadout (m : M) :
    Module.End K (LinearPrincipalCompletionState M n d) →ₗ[K]
      (QuantumLawPair (Fin n) → ZMod d → M) where
  toFun T p k :=
    T (linearPrincipalCompletionPairInput (d := d) p m) (.upper p.lower) k
  map_add' T U := by
    funext p k
    simp
  map_smul' c T := by
    funext p k
    simp

omit [NeZero d] [Fact (1 < d)] in
omit [CharZero K] in
/-- The clocked detector bracket has one private pair coefficient at clock degree two. -/
theorem linearPrincipalCompletionPairReadout_detectorBracket
    (m : M) (r : QuantumLawPair (Fin n)) :
    linearPrincipalCompletionPairReadout (K := K) (n := n) (d := d) m
        (linearCompletionDetectorGenerator (K := K) (M := M) (d := d) r.lower *
            linearCompletionDetectorGenerator (K := K) (M := M) (d := d) r.upper -
          linearCompletionDetectorGenerator (K := K) (M := M) (d := d) r.upper *
            linearCompletionDetectorGenerator (K := K) (M := M) (d := d) r.lower) =
      Pi.single r (Pi.single (2 : ZMod d) m) := by
  classical
  funext p k
  change
    (linearWidthDetectorGenerator (K := K) (M := M) r.lower *
          linearWidthDetectorGenerator (K := K) (M := M) r.upper -
        linearWidthDetectorGenerator (K := K) (M := M) r.upper *
          linearWidthDetectorGenerator (K := K) (M := M) r.lower)
      (fun y ↦ linearPrincipalCompletionPairInput (d := d) p m y (k - 1 - 1))
      (.upper p.lower) = _
  by_cases hk : k = 2
  · subst k
    have htwo : (2 : ZMod d) - 1 - 1 = 0 :=
      (zmod_sub_one_sub_one_eq_zero_iff (2 : ZMod d)).2 rfl
    have hslice :
        (fun y ↦ linearPrincipalCompletionPairInput (d := d) p m y
          ((2 : ZMod d) - 1 - 1)) =
        linearWidthDetectorLowerState p.upper m := by
      funext y
      by_cases hy : y = (.lower p.upper : LinearWidthDetectorIndex n)
      · subst y
        simp [linearPrincipalCompletionPairInput,
          linearWidthDetectorLowerState, htwo]
      · simp [linearPrincipalCompletionPairInput,
          linearWidthDetectorLowerState, htwo, hy]
    rw [hslice]
    have hbracket :
        (linearWidthDetectorGenerator (K := K) (M := M) r.lower *
              linearWidthDetectorGenerator (K := K) (M := M) r.upper -
            linearWidthDetectorGenerator (K := K) (M := M) r.upper *
              linearWidthDetectorGenerator (K := K) (M := M) r.lower) =
          principalBracketPair
            (linearWidthDetectorSymbol (K := K) (M := M) (n := n)) r := by
      symm
      rw [principalBracketPair,
        linearWidthDetectorSymbol_basisFun,
        linearWidthDetectorSymbol_basisFun]
    rw [hbracket]
    have hread := congrFun
      (linearWidthDetectorPairReadout_principalBracketPair
        (K := K) (n := n) m r) p
    by_cases hpr : p = r
    · subst p
      simpa [linearWidthDetectorPairReadout, Pi.single_apply] using hread
    · simpa [linearWidthDetectorPairReadout, Pi.single_apply, hpr] using hread
  · have hclock : k - 1 - 1 ≠ 0 := fun h ↦
      hk ((zmod_sub_one_sub_one_eq_zero_iff k).mp h)
    have hslice :
        (fun y ↦ linearPrincipalCompletionPairInput (d := d) p m y (k - 1 - 1)) = 0 := by
      funext y
      by_cases hy : y = (.lower p.upper : LinearWidthDetectorIndex n)
      · subst y
        simp [linearPrincipalCompletionPairInput, hclock]
      · simp [linearPrincipalCompletionPairInput, hy]
    rw [hslice]
    by_cases hpr : p = r
    · subst p
      simp [hk]
    · simp [hpr]

omit [CharZero K] [Fact (1 < d)] in
theorem linearPrincipalCompletionPairReadout_clock_mul_clock
    (q : K) (hq : q ^ d = 1) (m : M) (A B : Module.End K M) :
    linearPrincipalCompletionPairReadout (K := K) (n := n) (d := d) m
        (cyclicClockLift (ι := LinearWidthDetectorIndex n) q hq A *
          cyclicClockLift (ι := LinearWidthDetectorIndex n) q hq B) = 0 := by
  funext p k
  simp [linearPrincipalCompletionPairReadout, Module.End.mul_apply,
    cyclicClockLift, linearPrincipalCompletionPairInput]

omit [CharZero K] [Fact (1 < d)] in
theorem linearPrincipalCompletionPairReadout_clock_mul_detector
    (q : K) (hq : q ^ d = 1) (m : M) (A : Module.End K M) (i : Fin n) :
    linearPrincipalCompletionPairReadout (K := K) (n := n) (d := d) m
        (cyclicClockLift (ι := LinearWidthDetectorIndex n) q hq A *
          linearCompletionDetectorGenerator (K := K) (M := M) (d := d) i) = 0 := by
  funext p k
  simp [linearPrincipalCompletionPairReadout, Module.End.mul_apply,
    cyclicClockLift, linearCompletionDetectorGenerator,
    linearWidthDetectorGenerator, linearPrincipalCompletionPairInput]

omit [CharZero K] [Fact (1 < d)] in
theorem linearPrincipalCompletionPairReadout_detector_mul_clock
    (q : K) (hq : q ^ d = 1) (m : M) (A : Module.End K M) (i : Fin n) :
    linearPrincipalCompletionPairReadout (K := K) (n := n) (d := d) m
        (linearCompletionDetectorGenerator (K := K) (M := M) (d := d) i *
          cyclicClockLift (ι := LinearWidthDetectorIndex n) q hq A) = 0 := by
  funext p k
  simp [linearPrincipalCompletionPairReadout, Module.End.mul_apply,
    cyclicClockLift, linearCompletionDetectorGenerator,
    linearWidthDetectorGenerator, linearPrincipalCompletionPairInput]

omit [Fact (1 < d)] in
omit [CharZero K] in
theorem linearPrincipalCompletionPairReadout_principalBracketPair
    (q : K) (hq : q ^ d = 1)
    (A₀ : (Fin n → K) →ₗ[K] Module.End K M) (m : M)
    (r : QuantumLawPair (Fin n)) :
    linearPrincipalCompletionPairReadout (K := K) (n := n) (d := d) m
        (principalBracketPair (linearWidthPrincipalSymbolCompletion q hq A₀) r) =
      Pi.single r (Pi.single (2 : ZMod d) m) := by
  classical
  rw [principalBracketPair,
    linearWidthPrincipalSymbolCompletion_basisFun,
    linearWidthPrincipalSymbolCompletion_basisFun]
  simp only [mul_add, add_mul, map_sub, map_add]
  rw [linearPrincipalCompletionPairReadout_clock_mul_clock,
    linearPrincipalCompletionPairReadout_clock_mul_detector,
    linearPrincipalCompletionPairReadout_detector_mul_clock,
    linearPrincipalCompletionPairReadout_clock_mul_clock,
    linearPrincipalCompletionPairReadout_clock_mul_detector,
    linearPrincipalCompletionPairReadout_detector_mul_clock]
  simpa using linearPrincipalCompletionPairReadout_detectorBracket
    (K := K) (n := n) (d := d) m r

omit [Fact (1 < d)] in
omit [CharZero K] in
theorem linearWidthPrincipalSymbolCompletion_principalBracketPair_linearIndependent
    (q : K) (hq : IsPrimitiveRoot q d)
    (A₀ : (Fin n → K) →ₗ[K] Module.End K M)
    (m : M) (hm : m ≠ 0) :
    LinearIndependent K
      (principalBracketPair
        (linearWidthPrincipalSymbolCompletion q hq.pow_eq_one A₀)) := by
  classical
  apply LinearIndependent.of_comp
    (linearPrincipalCompletionPairReadout (K := K) (n := n) (d := d) m)
  have hclock : (Pi.single (2 : ZMod d) m : ZMod d → M) ≠ 0 := by
    intro hzero
    apply hm
    simpa using congrFun hzero (2 : ZMod d)
  have hsingle : LinearIndependent K
      (fun r : QuantumLawPair (Fin n) ↦
        (Pi.single r (Pi.single (2 : ZMod d) m : ZMod d → M) :
          QuantumLawPair (Fin n) → ZMod d → M)) :=
    Pi.linearIndependent_single_of_ne_zero (R := K) (fun _r ↦ hclock)
  simpa [Function.comp_def,
    linearPrincipalCompletionPairReadout_principalBracketPair] using hsingle

omit [Fact (1 < d)] in
omit [CharZero K] in
/-- **Linear-width universal principal-symbol theorem above degree two.** -/
theorem linearWidthPrincipalSymbolCompletion_endomorphismCommutatorMap_injective
    (q : K) (hq : IsPrimitiveRoot q d)
    (A₀ : (Fin n → K) →ₗ[K] Module.End K M)
    (m : M) (hm : m ≠ 0) :
    Function.Injective
      (endomorphismCommutatorMap
        (linearWidthPrincipalSymbolCompletion q hq.pow_eq_one A₀)) :=
  endomorphismCommutatorMap_injective_of_principalBracketPair_linearIndependent
    (linearWidthPrincipalSymbolCompletion q hq.pow_eq_one A₀)
    (linearWidthPrincipalSymbolCompletion_principalBracketPair_linearIndependent
      q hq A₀ m hm)

/-- **Linear-width before-time horizon theorem above degree two.**  A `2n+1` detector packet
preserves the exact scalar dependence horizon and remembers every law-space two-plane. -/
theorem linearWidthPrincipalSymbolCompletion_fieldHorizon_and_maximalPrincipalSymbol
    (q : K) (hq : IsPrimitiveRoot q d) (hd : 3 ≤ d)
    (A₀ : (Fin n → K) →ₗ[K] Module.End K M)
    (F : (Fin n → K) → K)
    (hA₀ : ∀ c, (A₀ c) ^ d = F c • LinearMap.id)
    (m : M) (hm : m ≠ 0) :
    ({c : Fin n → K | ¬ AlgebraicIndependent K
        (generalizedCliffordShiftFieldJet
          (linearWidthPrincipalSymbolCompletion q hq.pow_eq_one A₀ c)
          (linearPrincipalCompletionRoot (n := n) (d := d) m))} =
      {c : Fin n → K | F c = 0}) ∧
    Function.Injective
      (derivationCommutatorMap
        (generalizedCliffordShiftFieldDerivationLaw
          (linearWidthPrincipalSymbolCompletion q hq.pow_eq_one A₀))) := by
  constructor
  · apply generalizedCliffordShiftField_dependenceHorizon_eq_zeroLocus
      (linearWidthPrincipalSymbolCompletion q hq.pow_eq_one A₀) F d
      (Nat.ne_of_gt (lt_trans Nat.zero_lt_one Fact.out))
      (linearPrincipalCompletionRoot (n := n) (d := d) m)
      (linearPrincipalCompletionRoot_ne_zero m hm)
    exact linearWidthPrincipalSymbolCompletion_pow q hq hd A₀ F hA₀
  · rw [generalizedCliffordField_derivationCommutatorMap_injective_iff]
    exact linearWidthPrincipalSymbolCompletion_endomorphismCommutatorMap_injective
      q hq A₀ m hm

end

end GaloisForLFunctions.HTGeometry
