import GaloisForLFunctions.RHTower.Deninger.DeningerArithmeticThreeTermCohomology
import GaloisForLFunctions.RHTower.Deninger.DeningerPrimeDiagonalGreenSummability

/-!
# Rational-Witt packet restriction double obstruction

Two maps that look superficially suitable for Route L cannot be the missing packet comparison.

First, a packet map factored through the degree-one residue differential vanishes on every middle
cocycle.  If its kernel were exactly the middle boundaries, middle cohomology would therefore be
zero.  A faithful Green restriction for nonzero middle cohomology must instead be a secondary
degree-one map which kills boundaries but does not factor through the residue.

Second, one source vector whose packet restrictions retain a cofinite positive norm cannot satisfy
the pointwise square-summability required for Bessel assembly.  Cofinite unit-norm restrictions
also have divergent reciprocal-log-square Green mass.  This is the abstract obstruction met by a
literal global Teichmüller coordinate: local rational-Witt density does not imply global Bessel
summability.

All statements are unconditional.  They use no computation, Xi divisor, zeta zero, or RH premise.
-/

namespace RHTower

open Filter Topology

noncomputable section

section Middle

variable {R A0 A1 A2 K : Type*} [CommRing R]
variable [AddCommGroup A0] [Module R A0]
variable [AddCommGroup A1] [Module R A1]
variable [AddCommGroup A2] [Module R A2]
variable [AddCommGroup K] [Module R K]

/-- A degree-one packet restriction which kills boundaries descends to middle cohomology. -/
def deningerMiddlePacketMap
    (C : DeningerArithmeticThreeTermComplex R A0 A1 A2)
    (restriction : A1 →ₗ[R] K)
    (hboundary : restriction.comp C.d0 = 0) :
    C.H1 →ₗ[R] K :=
  (C.boundaries1.comap C.cycles1.subtype).liftQ
    (restriction.comp C.cycles1.subtype) (by
      rintro x ⟨a, ha⟩
      calc
        restriction (x : A1) = restriction (C.d0 a) := congrArg restriction ha.symm
        _ = 0 := LinearMap.congr_fun hboundary a)

@[simp]
theorem deningerMiddlePacketMap_mk
    (C : DeningerArithmeticThreeTermComplex R A0 A1 A2)
    (restriction : A1 →ₗ[R] K)
    (hboundary : restriction.comp C.d0 = 0)
    (x : C.cycles1) :
    deningerMiddlePacketMap C restriction hboundary
        (Submodule.Quotient.mk x) =
      restriction x := rfl

/-- Exact boundary kernel makes the induced middle packet map injective. -/
theorem deningerMiddlePacketMap_injective
    (C : DeningerArithmeticThreeTermComplex R A0 A1 A2)
    (restriction : A1 →ₗ[R] K)
    (hboundary : restriction.comp C.d0 = 0)
    (hkernel : LinearMap.ker restriction = C.boundaries1) :
    Function.Injective (deningerMiddlePacketMap C restriction hboundary) := by
  apply LinearMap.ker_eq_bot.mp
  rw [Submodule.eq_bot_iff]
  intro z hz
  obtain ⟨x, rfl⟩ :=
    Submodule.Quotient.mk_surjective
      (C.boundaries1.comap C.cycles1.subtype) z
  rw [C.H1_mk_eq_zero_iff]
  rw [← hkernel]
  exact hz

/-- **Residue-factor no-go.**  A packet map factored through the residue differential can classify
middle boundaries only when middle cohomology is trivial. -/
theorem deningerResidueFactoredPacket_kernel_eq_boundaries_forces_middle_subsingleton
    (C : DeningerArithmeticThreeTermComplex R A0 A1 A2)
    (packet : A2 →ₗ[R] K)
    (hkernel : LinearMap.ker (packet.comp C.d1) = C.boundaries1) :
    Subsingleton C.H1 := by
  have hzero : ∀ z : C.H1, z = 0 := by
    intro z
    obtain ⟨x, rfl⟩ :=
      Submodule.Quotient.mk_surjective
        (C.boundaries1.comap C.cycles1.subtype) z
    rw [C.H1_mk_eq_zero_iff]
    rw [← hkernel]
    change packet (C.d1 x) = 0
    rw [x.2, map_zero]
  exact ⟨fun x y => (hzero x).trans (hzero y).symm⟩

end Middle

section Bessel

variable {E : Type*}
variable {Kp : Nat.Primes → Type*}
variable [∀ p, NormedAddCommGroup (Kp p)]

/-- **Cofinite norm-floor no-go.**  A cofinite positive packet-norm floor for one fixed source
vector forbids pointwise square summability, hence any global Bessel assembly containing it. -/
theorem deningerPacket_not_summable_norm_sq_of_cofinite_floor
    (restriction : ∀ p, E → Kp p) (x : E) {ε : ℝ} (hε : 0 < ε)
    (hfloor : ∀ᶠ p in cofinite, ε ≤ ‖restriction p x‖) :
    ¬ Summable (fun p => ‖restriction p x‖ ^ (2 : ℕ)) := by
  intro hsum
  have hzero :
      Tendsto (fun p => ‖restriction p x‖ ^ (2 : ℕ)) cofinite (𝓝 0) :=
    hsum.tendsto_cofinite_zero
  have hsmall : ∀ᶠ p in cofinite, ‖restriction p x‖ ^ (2 : ℕ) < ε ^ (2 : ℕ) :=
    hzero.eventually_lt_const (sq_pos_of_pos hε)
  obtain ⟨p, hp, hp'⟩ := (hfloor.and hsmall).exists
  exact (not_lt_of_ge (sq_le_sq₀ hε.le (norm_nonneg _)|>.2 hp)) hp'

/-- Literal unit-norm packet evaluations also make reciprocal-log-square Green energy diverge. -/
theorem deningerPacket_not_summable_graphGreenEnergy_of_cofinite_unit_norm
    (f : ∀ p, Kp p)
    (hunit : ∀ᶠ p in cofinite, ‖f p‖ = 1) :
    ¬ Summable (fun p =>
      deningerPrimeGraphGreenCoefficient p * ‖f p‖ ^ (2 : ℕ)) := by
  intro hsum
  have heq :
      (fun p => deningerPrimeGraphGreenCoefficient p * ‖f p‖ ^ (2 : ℕ))
        =ᶠ[cofinite] deningerPrimeGraphGreenCoefficient := by
    filter_upwards [hunit] with p hp
    rw [hp, one_pow, mul_one]
  exact not_summable_deningerPrimeGraphGreenCoefficient
    (hsum.congr_cofinite heq)

end Bessel

end

end RHTower
