import GaloisForLFunctions.RHTower.DeningerRelationKernelTransgression
import GaloisForLFunctions.RHTower.DeningerMeyerLogGaussianUniversalOrbitCriterion
import GaloisForLFunctions.RHTower.DeningerMeyerGaussianLineWronskianGreenComparison

/-!
# Meyer--relation-kernel boundary separation

This file constructs the type-correct comparison requested between completed Green orientation,
Calderon--Witt relation-kernel transgression, and the literal Meyer--Poisson collar.  The common
coefficient object is the affine-gauge first-suspension space, so no origin is chosen in the packet
torsor.

Relation-kernel transgression is homogeneous: scaling the Calderon--Witt cup by the unsquared
Green fracture scales its nonzero relation character by exactly that fracture.  Literal Meyer
boundaries, however, map to zero in the same coefficient space.  Hence equality between a literal
boundary and a nonzero calibrated Green ray is equivalent to critical-line placement.  The fixed
reflected Gaussian source is also proved not to lie in the literal boundary range.

Thus the coefficient comparison is unconditional, while placing it in the literal boundary image
would already prove the local RH assertion; it cannot serve as an independent annihilation law.
-/

namespace RHTower

noncomputable section

namespace DeningerNormalizedCocycle

section Scaling

variable {G A : Type} {M : Type*}
  [Group G] [Group A] [AddCommGroup M] [Module ℂ M]

/-- Scalar multiplication of a normalized cocycle. -/
def csmul (c : DeningerNormalizedCocycle A M) (z : ℂ) :
    DeningerNormalizedCocycle A M where
  f x := z • c.f x
  cocycle g h j := by
    simpa only [smul_add] using
      congrArg (fun x => z • x) (c.cocycle g h j)
  one_fst g := by rw [c.one_fst, smul_zero]
  one_snd g := by rw [c.one_snd, smul_zero]

/-- Scaling a cocycle and one pulled-back primitive preserves the primitive identity. -/
theorem pullback_isPrimitive_csmul
    (c : DeningerNormalizedCocycle A M) (pi : G →* A)
    {b : G → M} (hb : (c.pullback pi).IsPrimitive b) (z : ℂ) :
    ((c.csmul z).pullback pi).IsPrimitive (fun g => z • b g) := by
  intro g h
  change z • c.f (pi g, pi h) =
    z • b (g * h) - z • b g - z • b h
  have hprimitive := hb g h
  change c.f (pi g, pi h) = b (g * h) - b g - b h at hprimitive
  rw [hprimitive]
  module

/-- Relation-kernel transgression commutes pointwise with scalar multiplication. -/
theorem kernelTransgression_csmul_apply
    (c : DeningerNormalizedCocycle A M) (pi : G →* A)
    {b : G → M} (hb : (c.pullback pi).IsPrimitive b)
    (z : ℂ) (k : pi.ker) :
    Multiplicative.toAdd
        (kernelTransgression (c.csmul z) pi (fun g => z • b g)
          (pullback_isPrimitive_csmul c pi hb z) k) =
      z • Multiplicative.toAdd (kernelTransgression c pi b hb k) := by
  rfl

/-- A nonzero relation character makes scalar transgression faithful. -/
theorem forall_csmul_relationValue_eq_zero_iff
    {pi : G →* A} {b : G → M}
    (htrans : ¬ ∀ k : pi.ker, b k = 0) (z : ℂ) :
    (∀ k : pi.ker, z • b k = 0) ↔ z = 0 := by
  constructor
  · intro hzero
    by_contra hz
    push Not at htrans
    obtain ⟨k, hk⟩ := htrans
    exact (smul_ne_zero hz hk) (hzero k)
  · rintro rfl
    simp

end Scaling

section Commutator

variable {G A : Type} {M : Type*}
  [Group G] [CommGroup A] [AddCommGroup M]

/-- Relation word comparing the two orders of a source pair. -/
def relationCommutator (g h : G) : G :=
  g * h * (h * g)⁻¹

theorem relationCommutator_mem_ker (pi : G →* A) (g h : G) :
    relationCommutator g h ∈ pi.ker := by
  rw [MonoidHom.mem_ker]
  simp only [relationCommutator, map_mul, map_inv]
  rw [mul_comm (pi h) (pi g), mul_inv_cancel]

/-- A primitive records the skew cocycle on the canonical commutator relation. -/
theorem primitive_relationCommutator_eq_skew
    (c : DeningerNormalizedCocycle A M) (pi : G →* A)
    {b : G → M} (hb : (c.pullback pi).IsPrimitive b) (g h : G) :
    b (relationCommutator g h) =
      c.f (pi g, pi h) - c.f (pi h, pi g) := by
  let k := relationCommutator g h
  have hk : pi k = 1 := MonoidHom.mem_ker.mp
    (relationCommutator_mem_ker pi g h)
  have hprod : k * (h * g) = g * h := by
    dsimp only [k, relationCommutator]
    group
  have hboundary := hb k (h * g)
  change c.f (pi k, pi (h * g)) =
    b (k * (h * g)) - b k - b (h * g) at hboundary
  rw [hk, c.one_fst, hprod] at hboundary
  have hcompare : b k = b (g * h) - b (h * g) := by
    apply eq_sub_iff_add_eq.mpr
    calc
      b k + b (h * g) =
          (b (g * h) - b k - b (h * g)) + b k + b (h * g) := by
            rw [← hboundary]
            simp
      _ = b (g * h) := by abel
  have hgh := hb g h
  have hhg := hb h g
  change c.f (pi g, pi h) = b (g * h) - b g - b h at hgh
  change c.f (pi h, pi g) = b (h * g) - b h - b g at hhg
  calc
    b (relationCommutator g h) = b (g * h) - b (h * g) := hcompare
    _ = c.f (pi g, pi h) - c.f (pi h, pi g) := by
      rw [hgh, hhg]
      abel

/-- The commutator transgression is primitive-independent without any
degree-one descent hypothesis. -/
theorem primitive_relationCommutator_eq_of_primitives
    (c : DeningerNormalizedCocycle A M) (pi : G →* A)
    {b d : G → M}
    (hb : (c.pullback pi).IsPrimitive b)
    (hd : (c.pullback pi).IsPrimitive d) (g h : G) :
    b (relationCommutator g h) = d (relationCommutator g h) := by
  rw [primitive_relationCommutator_eq_skew c pi hb,
    primitive_relationCommutator_eq_skew c pi hd]

/-- For an alternating cocycle, the commutator relation stores two copies of the cup value. -/
theorem primitive_relationCommutator_eq_add_of_alternating
    (c : DeningerNormalizedCocycle A M) (pi : G →* A)
    {b : G → M} (hb : (c.pullback pi).IsPrimitive b)
    (halt : c.IsAlternating) (g h : G) :
    b (relationCommutator g h) =
      c.f (pi g, pi h) + c.f (pi g, pi h) := by
  rw [primitive_relationCommutator_eq_skew c pi hb g h,
    halt (pi h) (pi g)]
  abel

end Commutator

end DeningerNormalizedCocycle

/-- Canonical free-rational cover pointed by every vector of the source. -/
def deningerSourcePointedBauMap
    (V : Type) [AddCommGroup V] [Module ℚ V] :
    DeningerBau (FreeGroup V) →* Multiplicative V :=
  deningerBauFreeMap (fun v : V => v)

/-- Canonical lift of one source vector to its namesake free generator. -/
def deningerSourcePointedBauLift
    {V : Type} [AddCommGroup V] [Module ℚ V] (v : V) :
    DeningerBau (FreeGroup V) :=
  DeningerBau.of (FreeGroup.of v)

@[simp]
theorem deningerSourcePointedBauMap_lift
    {V : Type} [AddCommGroup V] [Module ℚ V] (v : V) :
    deningerSourcePointedBauMap V (deningerSourcePointedBauLift v) =
      Multiplicative.ofAdd v := by
  rw [deningerSourcePointedBauMap, deningerSourcePointedBauLift,
    deningerBauFreeMap, deningerBauLift_of, FreeGroup.lift_apply_of]

/-- The source-pointed free-rational map is an actual quotient cover. -/
theorem deningerSourcePointedBauMap_surjective
    (V : Type) [AddCommGroup V] [Module ℚ V] :
    Function.Surjective (deningerSourcePointedBauMap V) := by
  apply deningerBauFree_surjective (fun v : V => v)
  rw [show Set.range (fun v : V => v) = Set.univ by ext; simp,
    Submodule.span_univ]

/-- Canonical Calderon generator of the source-pointed free cover. -/
def deningerCalderonWittDefectGenerator (p : Nat.Primes) :
    DeningerCalderonWittDegreeOne p :=
  (deningerCalderonWittUnitDefect p, 0)

/-- Canonical rational-Witt generator of the source-pointed free cover. -/
def deningerCalderonWittPacketGenerator (p : Nat.Primes) :
    DeningerCalderonWittDegreeOne p :=
  (0, deningerCalderonWittUnitPacket p)

/-- Presentation-independent commutator transgression calibrator. -/
def deningerCalderonWittSourcePointedTau (p : Nat.Primes) :
    DeningerCalderonWittDegreeTwo p :=
  deningerCalderonWittCup p
      (deningerCalderonWittDefectGenerator p)
      (deningerCalderonWittPacketGenerator p) +
    deningerCalderonWittCup p
      (deningerCalderonWittDefectGenerator p)
      (deningerCalderonWittPacketGenerator p)

theorem deningerCalderonWittSourcePointedTau_ne_zero (p : Nat.Primes) :
    deningerCalderonWittSourcePointedTau p ≠ 0 := by
  have hcross :
      deningerMeyerCalderonGaugePacketCrossEffect p
          (deningerCalderonWittUnitDefect p)
          (deningerCalderonWittUnitPacket p) ≠ 0 := by
    intro hzero
    apply deningerCalderonWittUnitPacket_ne_zero p
    apply deningerMeyerCalderonGaugePacketCrossEffect_unit_injective p
    simpa using hzero
  have hcup :
      deningerCalderonWittCup p
          (deningerCalderonWittDefectGenerator p)
          (deningerCalderonWittPacketGenerator p) ≠ 0 := by
    simpa [deningerCalderonWittDefectGenerator,
      deningerCalderonWittPacketGenerator,
      deningerCalderonWittCup_apply] using hcross
  intro hzero
  have htwo :
      (2 : ℂ) • deningerCalderonWittCup p
          (deningerCalderonWittDefectGenerator p)
          (deningerCalderonWittPacketGenerator p) = 0 := by
    simpa [two_smul, deningerCalderonWittSourcePointedTau] using hzero
  exact (smul_ne_zero (by norm_num) hcup) htwo

/-- The actual cup has a primitive on the canonical source-pointed cover,
and its canonical commutator value is exactly `tau_p`. -/
theorem exists_deningerCalderonWitt_sourcePointedTau_primitive
    (p : Nat.Primes) :
    let pi := deningerSourcePointedBauMap (DeningerCalderonWittDegreeOne p)
    let x := deningerCalderonWittDefectGenerator p
    let y := deningerCalderonWittPacketGenerator p
    let k : pi.ker :=
      ⟨DeningerNormalizedCocycle.relationCommutator
          (deningerSourcePointedBauLift x)
          (deningerSourcePointedBauLift y),
        DeningerNormalizedCocycle.relationCommutator_mem_ker pi _ _⟩
    ∃ (b : DeningerBau (FreeGroup (DeningerCalderonWittDegreeOne p)) →
          DeningerCalderonWittDegreeTwo p)
      (hb : ((deningerCalderonWittCupCocycle p).pullback pi).IsPrimitive b),
      Multiplicative.toAdd
          (DeningerNormalizedCocycle.kernelTransgression
            (deningerCalderonWittCupCocycle p) pi b hb k) =
        deningerCalderonWittSourcePointedTau p := by
  dsimp only
  let pi := deningerSourcePointedBauMap (DeningerCalderonWittDegreeOne p)
  obtain ⟨b, hb⟩ :=
    deningerBauFree_cocycle_trivial
      ((deningerCalderonWittCupCocycle p).pullback pi)
  change ((deningerCalderonWittCupCocycle p).pullback pi).IsPrimitive b at hb
  refine ⟨b, hb, ?_⟩
  change b (DeningerNormalizedCocycle.relationCommutator
      (deningerSourcePointedBauLift (deningerCalderonWittDefectGenerator p))
      (deningerSourcePointedBauLift (deningerCalderonWittPacketGenerator p))) = _
  rw [DeningerNormalizedCocycle.primitive_relationCommutator_eq_add_of_alternating
    (deningerCalderonWittCupCocycle p) pi hb
    (deningerCalderonWittCupCocycle_alternating p),
    deningerSourcePointedBauMap_lift,
    deningerSourcePointedBauMap_lift]
  rfl

/-- **Source-defined comparison.**  On the canonical commutator relation,
transgression of the Green-scaled actual cup is exactly `D_rho tau_p`. -/
theorem exists_deningerCalderonWitt_sourcePointed_greenComparison
    (p : Nat.Primes) (rho : XiDivisorSupport) :
    let pi := deningerSourcePointedBauMap (DeningerCalderonWittDegreeOne p)
    let x := deningerCalderonWittDefectGenerator p
    let y := deningerCalderonWittPacketGenerator p
    let k : pi.ker :=
      ⟨DeningerNormalizedCocycle.relationCommutator
          (deningerSourcePointedBauLift x)
          (deningerSourcePointedBauLift y),
        DeningerNormalizedCocycle.relationCommutator_mem_ker pi _ _⟩
    ∃ (b : DeningerBau (FreeGroup (DeningerCalderonWittDegreeOne p)) →
          DeningerCalderonWittDegreeTwo p)
      (hb : ((deningerCalderonWittCupCocycle p).pullback pi).IsPrimitive b),
      Multiplicative.toAdd
          (DeningerNormalizedCocycle.kernelTransgression
            ((deningerCalderonWittCupCocycle p).csmul
              (xiNearbyPoleDualityAdjunctionFracture (rho : ℂ)))
            pi
            (fun g => xiNearbyPoleDualityAdjunctionFracture (rho : ℂ) • b g)
            (DeningerNormalizedCocycle.pullback_isPrimitive_csmul
              (deningerCalderonWittCupCocycle p) pi hb
              (xiNearbyPoleDualityAdjunctionFracture (rho : ℂ))) k) =
        xiNearbyPoleDualityAdjunctionFracture (rho : ℂ) •
          deningerCalderonWittSourcePointedTau p := by
  dsimp only
  let pi := deningerSourcePointedBauMap (DeningerCalderonWittDegreeOne p)
  obtain ⟨b, hb⟩ :=
    deningerBauFree_cocycle_trivial
      ((deningerCalderonWittCupCocycle p).pullback pi)
  change ((deningerCalderonWittCupCocycle p).pullback pi).IsPrimitive b at hb
  refine ⟨b, ?_, ?_⟩
  · simpa [pi] using hb
  · change xiNearbyPoleDualityAdjunctionFracture (rho : ℂ) •
        b (DeningerNormalizedCocycle.relationCommutator
          (deningerSourcePointedBauLift (deningerCalderonWittDefectGenerator p))
          (deningerSourcePointedBauLift (deningerCalderonWittPacketGenerator p))) =
      xiNearbyPoleDualityAdjunctionFracture (rho : ℂ) •
        deningerCalderonWittSourcePointedTau p
    congr 1
    rw [DeningerNormalizedCocycle.primitive_relationCommutator_eq_add_of_alternating
      (deningerCalderonWittCupCocycle p) pi hb
      (deningerCalderonWittCupCocycle_alternating p),
      deningerSourcePointedBauMap_lift,
      deningerSourcePointedBauMap_lift]
    rfl

/-- **Actual source/Green relation-kernel comparison.**  Scaling the
Calderon--Witt cup by the unsquared completed Green fracture scales its
nonzero relation-kernel character by exactly that coefficient.  Global
vanishing of the scaled character is equivalent to critical-line placement. -/
theorem exists_deningerCalderonWitt_greenFracture_relationKernelTransgression
    (p : Nat.Primes) (rho : XiDivisorSupport) :
    let basis := Module.Free.chooseBasis ℚ (DeningerCalderonWittDegreeOne p)
    let pi := deningerBauFreeMap (⇑basis)
    ∃ (b : DeningerBau (FreeGroup (Module.Free.ChooseBasisIndex ℚ
          (DeningerCalderonWittDegreeOne p))) → DeningerCalderonWittDegreeTwo p)
      (hb : ((deningerCalderonWittCupCocycle p).pullback pi).IsPrimitive b),
      (¬ ∀ k : pi.ker, b k = 0) ∧
      (∀ k : pi.ker,
        Multiplicative.toAdd
            (DeningerNormalizedCocycle.kernelTransgression
              ((deningerCalderonWittCupCocycle p).csmul
                (xiNearbyPoleDualityAdjunctionFracture (rho : ℂ)))
              pi
              (fun g => xiNearbyPoleDualityAdjunctionFracture (rho : ℂ) • b g)
              (DeningerNormalizedCocycle.pullback_isPrimitive_csmul
                (deningerCalderonWittCupCocycle p) pi hb
                (xiNearbyPoleDualityAdjunctionFracture (rho : ℂ))) k) =
          xiNearbyPoleDualityAdjunctionFracture (rho : ℂ) •
            Multiplicative.toAdd
              (DeningerNormalizedCocycle.kernelTransgression
                (deningerCalderonWittCupCocycle p) pi b hb k)) ∧
      ((∀ k : pi.ker,
          Multiplicative.toAdd
              (DeningerNormalizedCocycle.kernelTransgression
                ((deningerCalderonWittCupCocycle p).csmul
                  (xiNearbyPoleDualityAdjunctionFracture (rho : ℂ)))
                pi
                (fun g => xiNearbyPoleDualityAdjunctionFracture (rho : ℂ) • b g)
                (DeningerNormalizedCocycle.pullback_isPrimitive_csmul
                  (deningerCalderonWittCupCocycle p) pi hb
                  (xiNearbyPoleDualityAdjunctionFracture (rho : ℂ))) k) = 0) ↔
        (rho : ℂ).re = 1 / 2) := by
  dsimp only
  obtain ⟨b, hb, htrans⟩ :=
    exists_deningerCalderonWitt_nonzero_relationKernelTransgression p
  refine ⟨b, hb, htrans, ?_, ?_⟩
  · intro k
    exact
      DeningerNormalizedCocycle.kernelTransgression_csmul_apply
        (deningerCalderonWittCupCocycle p)
        (deningerBauFreeMap
          (⇑(Module.Free.chooseBasis ℚ (DeningerCalderonWittDegreeOne p))))
        hb (xiNearbyPoleDualityAdjunctionFracture (rho : ℂ)) k
  · calc
      (∀ k,
          Multiplicative.toAdd
              (DeningerNormalizedCocycle.kernelTransgression
                ((deningerCalderonWittCupCocycle p).csmul
                  (xiNearbyPoleDualityAdjunctionFracture (rho : ℂ)))
                (deningerBauFreeMap
                  (⇑(Module.Free.chooseBasis ℚ
                    (DeningerCalderonWittDegreeOne p))))
                (fun g => xiNearbyPoleDualityAdjunctionFracture (rho : ℂ) • b g)
                (DeningerNormalizedCocycle.pullback_isPrimitive_csmul
                  (deningerCalderonWittCupCocycle p)
                  (deningerBauFreeMap
                    (⇑(Module.Free.chooseBasis ℚ
                      (DeningerCalderonWittDegreeOne p)))) hb
                  (xiNearbyPoleDualityAdjunctionFracture (rho : ℂ))) k) = 0) ↔
          (∀ k : (deningerBauFreeMap
              (⇑(Module.Free.chooseBasis ℚ
                (DeningerCalderonWittDegreeOne p)))).ker,
            xiNearbyPoleDualityAdjunctionFracture (rho : ℂ) • b k = 0) := by
            apply forall_congr'
            intro k
            rfl
      _ ↔ xiNearbyPoleDualityAdjunctionFracture (rho : ℂ) = 0 :=
        DeningerNormalizedCocycle.forall_csmul_relationValue_eq_zero_iff
          htrans (xiNearbyPoleDualityAdjunctionFracture (rho : ℂ))
      _ ↔ (rho : ℂ).re = 1 / 2 :=
        xiNearbyPoleDualityAdjunctionFracture_eq_zero_iff (rho : ℂ)

/-- The literal Meyer collar compared in the affine-gauge first-suspension coefficient space. -/
def deningerMeyerCalderonWittGaugeBoundaryComparison
    (p : Nat.Primes)
    (packet : DeningerPrimeFinitePacketGaugeComplexHaarL2 p) :
    (ℂ × ℂ) →ₗ[ℂ] DeningerCalderonWittDegreeTwo p where
  toFun u :=
    deningerMeyerCalderonGaugePacketCrossEffect p
      (Submodule.Quotient.mk u) packet
  map_add' u v := by simp
  map_smul' z u := by simp

@[simp]
theorem deningerMeyerCalderonWittGaugeBoundaryComparison_apply
    (p : Nat.Primes)
    (packet : DeningerPrimeFinitePacketGaugeComplexHaarL2 p)
    (u : ℂ × ℂ) :
    deningerMeyerCalderonWittGaugeBoundaryComparison p packet u =
      deningerMeyerCalderonGaugePacketCrossEffect p
        (Submodule.Quotient.mk u) packet :=
  rfl

/-- Every literal Meyer--Poisson boundary is zero in the same coefficient space as the cup. -/
theorem deningerMeyerCalderonWittGaugeBoundaryComparison_literalBoundary_zero
    (p : Nat.Primes)
    (packet : DeningerPrimeFinitePacketGaugeComplexHaarL2 p)
    (f : DeningerMeyerCap) :
    deningerMeyerCalderonWittGaugeBoundaryComparison p packet
        (deningerMeyerPoissonCollarTrace (p : ℝ)
          (by exact_mod_cast p.2.pos) f) = 0 := by
  rw [deningerMeyerCalderonWittGaugeBoundaryComparison_apply,
    deningerMeyerPoissonCollarTrace_quotient_zero]
  exact map_zero
    (deningerMeyerCalderonGaugePacketCrossEffect p) |>.symm ▸ rfl

/-- Exact separation: a literal boundary can equal a nonzero calibrated Green ray only on line. -/
theorem deningerMeyer_literalBoundary_eq_greenFracture_smul_iff
    (p : Nat.Primes)
    (packet : DeningerPrimeFinitePacketGaugeComplexHaarL2 p)
    (f : DeningerMeyerCap) (rho : XiDivisorSupport)
    (v : DeningerCalderonWittDegreeTwo p) (hv : v ≠ 0) :
    deningerMeyerCalderonWittGaugeBoundaryComparison p packet
        (deningerMeyerPoissonCollarTrace (p : ℝ)
          (by exact_mod_cast p.2.pos) f) =
        xiNearbyPoleDualityAdjunctionFracture (rho : ℂ) • v ↔
      (rho : ℂ).re = 1 / 2 := by
  rw [deningerMeyerCalderonWittGaugeBoundaryComparison_literalBoundary_zero]
  constructor
  · intro h
    have hz : xiNearbyPoleDualityAdjunctionFracture (rho : ℂ) • v = 0 := h.symm
    have hfracture : xiNearbyPoleDualityAdjunctionFracture (rho : ℂ) = 0 :=
      (smul_eq_zero.mp hz).resolve_right hv
    exact (xiNearbyPoleDualityAdjunctionFracture_eq_zero_iff (rho : ℂ)).mp hfracture
  · intro hline
    rw [(xiNearbyPoleDualityAdjunctionFracture_eq_zero_iff (rho : ℂ)).2 hline,
      zero_smul]

/-- **Literal-kernel verdict for the source-pointed calibrator.**  The actual
Meyer boundary and the source-defined Green-scaled commutator transgression
coincide exactly when the divisor support is on the critical line. -/
theorem deningerMeyer_literalBoundary_eq_sourcePointedGreenTransgression_iff
    (p : Nat.Primes) (f : DeningerMeyerCap) (rho : XiDivisorSupport) :
    deningerMeyerCalderonWittGaugeBoundaryComparison p
        (deningerCalderonWittUnitPacket p)
        (deningerMeyerPoissonCollarTrace (p : ℝ)
          (by exact_mod_cast p.2.pos) f) =
        xiNearbyPoleDualityAdjunctionFracture (rho : ℂ) •
          deningerCalderonWittSourcePointedTau p ↔
      (rho : ℂ).re = 1 / 2 :=
  deningerMeyer_literalBoundary_eq_greenFracture_smul_iff
    p (deningerCalderonWittUnitPacket p) f rho
      (deningerCalderonWittSourcePointedTau p)
      (deningerCalderonWittSourcePointedTau_ne_zero p)

/-- The reflected Gaussian source is a nonzero Meyer class, not a literal Meyer boundary. -/
theorem deningerMeyerReflectedLogGaussianSource_not_mem_literalBoundaryRange
    (rho : XiDivisorSupport) :
    deningerMeyerReflectedLogGaussianSource ∉
      LinearMap.range deningerMeyerStrongLogSumLM := by
  intro hmem
  have hclass :
      (Submodule.Quotient.mk deningerMeyerReflectedLogGaussianSource :
        DeningerMeyerStrongLogCohomology) = 0 :=
    (Submodule.Quotient.mk_eq_zero
      (LinearMap.range deningerMeyerStrongLogSumLM)).2 hmem
  have hne := deningerMeyerReflectedLogGaussianCohomologyClass_evaluation_ne_zero rho
  rw [deningerMeyerReflectedLogGaussianCohomologyClass, hclass, map_zero] at hne
  exact hne rfl

end

end RHTower
