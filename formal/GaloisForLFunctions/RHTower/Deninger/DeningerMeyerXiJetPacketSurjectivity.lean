import GaloisForLFunctions.RHTower.Deninger.DeningerMeyerXiSpectralInclusion
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Source-native finite Xi jet packets in literal Meyer cohomology

The literal all-weight Meyer quotient does more than carry one nonzero
functional at each Xi divisor.  Its complete multiplicity-bounded evaluation
map onto the corresponding confluent jet packet is surjective.  Hence the
packet is an actual finite quotient of Meyer cohomology, not a postulated
divisor-indexed carrier.

The descended dilation flow is conjugate to the exact lower-triangular
binomial Jordan flow on this quotient.  This isolates, without positivity or
spectral-synthesis assumptions, the finite source packet on which any future
arithmetic Hodge comparison must be faithful.

All statements are unconditional.  No RH, simplicity, positivity, trace,
numerical computation, or inverse-Mellin synthesis premise is used.
-/

open scoped Classical

namespace RHTower

noncomputable section

/--
A finite independent family of scalar linear functionals has a surjective
joint evaluation map.  This vector-space lemma is stated here because the
Meyer source is infinite-dimensional while its Xi jet packet is finite.
-/
theorem piMap_surjective_of_linearIndependent
    {K V ι : Type*}
    [Field K] [AddCommGroup V] [Module K V]
    [Fintype ι]
    (f : ι → V →ₗ[K] K)
    (hf : LinearIndependent K f) :
    Function.Surjective (LinearMap.pi f) := by
  rw [← LinearMap.dualMap_injective_iff]
  intro phi psi hphi
  let theta : Module.Dual K (ι → K) := phi - psi
  have hthetaComp :
      theta.comp (LinearMap.pi f) = 0 := by
    ext v
    change phi (LinearMap.pi f v) - psi (LinearMap.pi f v) = 0
    exact sub_eq_zero.mpr (LinearMap.congr_fun hphi v)
  let c : ι → K := fun i => theta (Pi.basisFun K ι i)
  have hrelation : ∑ i, c i • f i = 0 := by
    ext v
    have hv := LinearMap.congr_fun hthetaComp v
    change theta (LinearMap.pi f v) = 0 at hv
    rw [← (Pi.basisFun K ι).sum_repr (LinearMap.pi f v)] at hv
    simp only [map_sum, map_smul, Pi.basisFun_repr,
      LinearMap.pi_apply, smul_eq_mul] at hv
    simpa only [c, LinearMap.sum_apply, LinearMap.smul_apply,
      LinearMap.zero_apply, smul_eq_mul, mul_comm] using hv
  have hc : ∀ i, c i = 0 :=
    Fintype.linearIndependent_iff.mp hf c hrelation
  have htheta : theta = 0 := by
    apply (Pi.basisFun K ι).ext
    intro i
    change c i = 0
    exact hc i
  exact sub_eq_zero.mp htheta

/-- Full multiplicity-bounded scalar jet packet at one actual Xi divisor. -/
abbrev DeningerMeyerXiJetPacket (rho : XiDivisorSupport) :=
  DeningerArithmeticJetIndex rho → ℂ

/--
Joint evaluation of a literal Meyer class on every jet below the actual Xi
multiplicity.
-/
def deningerMeyerXiJetPacketLM
    (rho : XiDivisorSupport) :
    DeningerMeyerStrongLogCohomology →ₗ[ℂ]
      DeningerMeyerXiJetPacket rho :=
  LinearMap.pi (deningerMeyerXiSupportJetEvaluationLM rho)

@[simp]
theorem deningerMeyerXiJetPacketLM_apply
    (rho : XiDivisorSupport)
    (u : DeningerMeyerStrongLogCohomology)
    (k : DeningerArithmeticJetIndex rho) :
    deningerMeyerXiJetPacketLM rho u k =
      deningerMeyerXiSupportJetEvaluationLM rho k u :=
  rfl

/--
Every finite Xi jet vector has a literal Meyer representative.  This is
source-native finite spectral synthesis; it follows from compactly supported
smooth separation, not from an abstract divisor carrier.
-/
theorem deningerMeyerXiJetPacketLM_surjective
    (rho : XiDivisorSupport) :
    Function.Surjective (deningerMeyerXiJetPacketLM rho) :=
  piMap_surjective_of_linearIndependent
    (deningerMeyerXiSupportJetEvaluationLM rho)
    (deningerMeyerXiSupportJetEvaluationLM_linearIndependent rho)

/-- Exact finite spectral quotient of literal Meyer cohomology at `rho`. -/
def deningerMeyerXiJetPacketQuotEquiv
    (rho : XiDivisorSupport) :
    (DeningerMeyerStrongLogCohomology ⧸
        LinearMap.ker (deningerMeyerXiJetPacketLM rho)) ≃ₗ[ℂ]
      DeningerMeyerXiJetPacket rho :=
  (deningerMeyerXiJetPacketLM rho).quotKerEquivOfSurjective
    (deningerMeyerXiJetPacketLM_surjective rho)

@[simp]
theorem deningerMeyerXiJetPacketQuotEquiv_mk
    (rho : XiDivisorSupport)
    (u : DeningerMeyerStrongLogCohomology) :
  deningerMeyerXiJetPacketQuotEquiv rho
        (Submodule.Quotient.mk u) =
      deningerMeyerXiJetPacketLM rho u :=
  LinearMap.quotKerEquivOfSurjective_apply_mk
    (f := deningerMeyerXiJetPacketLM rho)
    (deningerMeyerXiJetPacketLM_surjective rho) u

/--
Exact confluent Jordan flow on the finite Xi jet packet.  Index `k` mixes
only with indices at most `k`.
-/
def deningerMeyerXiJetPacketFlow
    (rho : XiDivisorSupport) (c : ℝ) :
    DeningerMeyerXiJetPacket rho →ₗ[ℂ]
      DeningerMeyerXiJetPacket rho where
  toFun x k :=
    ∑ i ∈ Finset.range (k.val + 1),
      (k.val.choose i : ℂ) *
        (c : ℂ) ^ i *
        Complex.exp ((c : ℂ) * (rho : ℂ)) *
        x
          (⟨k.val - i,
            lt_of_le_of_lt (Nat.sub_le k.val i) k.isLt⟩ :
              DeningerArithmeticJetIndex rho)
  map_add' x y := by
    funext k
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' a x := by
    funext k
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring

@[simp]
theorem deningerMeyerXiJetPacketFlow_apply
    (rho : XiDivisorSupport) (c : ℝ)
    (x : DeningerMeyerXiJetPacket rho)
    (k : DeningerArithmeticJetIndex rho) :
    deningerMeyerXiJetPacketFlow rho c x k =
      ∑ i ∈ Finset.range (k.val + 1),
        (k.val.choose i : ℂ) *
          (c : ℂ) ^ i *
          Complex.exp ((c : ℂ) * (rho : ℂ)) *
          x
            (⟨k.val - i,
              lt_of_le_of_lt (Nat.sub_le k.val i) k.isLt⟩ :
                DeningerArithmeticJetIndex rho) :=
  rfl

/--
Literal Meyer dilation and the finite confluent Xi packet flow commute
exactly.
-/
theorem deningerMeyerXiJetPacketLM_flow
    (rho : XiDivisorSupport) (c : ℝ)
    (u : DeningerMeyerStrongLogCohomology) :
    deningerMeyerXiJetPacketLM rho
        (deningerMeyerStrongLogCohomologyFlow c u) =
      deningerMeyerXiJetPacketFlow rho c
        (deningerMeyerXiJetPacketLM rho u) := by
  funext k
  exact
    deningerMeyerXiSupportJetEvaluationLM_flow rho k c u

/-- The common jet kernel is invariant under every literal Meyer dilation. -/
theorem deningerMeyerXiJetPacketLM_ker_flow
    (rho : XiDivisorSupport) (c : ℝ)
    {u : DeningerMeyerStrongLogCohomology}
    (hu :
      u ∈ LinearMap.ker (deningerMeyerXiJetPacketLM rho)) :
    deningerMeyerStrongLogCohomologyFlow c u ∈
      LinearMap.ker (deningerMeyerXiJetPacketLM rho) := by
  rw [LinearMap.mem_ker] at hu ⊢
  rw [deningerMeyerXiJetPacketLM_flow, hu, map_zero]

/-- Dilation descended to the exact finite Xi jet quotient. -/
def deningerMeyerXiJetPacketQuotientFlow
    (rho : XiDivisorSupport) (c : ℝ) :
    (DeningerMeyerStrongLogCohomology ⧸
        LinearMap.ker (deningerMeyerXiJetPacketLM rho)) →ₗ[ℂ]
      (DeningerMeyerStrongLogCohomology ⧸
        LinearMap.ker (deningerMeyerXiJetPacketLM rho)) :=
  (LinearMap.ker (deningerMeyerXiJetPacketLM rho)).mapQ
    (LinearMap.ker (deningerMeyerXiJetPacketLM rho))
    (deningerMeyerStrongLogCohomologyFlow c)
    (by
      intro u hu
      exact
        deningerMeyerXiJetPacketLM_ker_flow rho c hu)

/--
The quotient equivalence conjugates descended Meyer dilation to the full
multiplicity-sensitive Jordan packet, with no semisimplicity assumption.
-/
theorem deningerMeyerXiJetPacketQuotEquiv_flow
    (rho : XiDivisorSupport) (c : ℝ)
    (q :
      DeningerMeyerStrongLogCohomology ⧸
        LinearMap.ker (deningerMeyerXiJetPacketLM rho)) :
    deningerMeyerXiJetPacketQuotEquiv rho
        (deningerMeyerXiJetPacketQuotientFlow rho c q) =
      deningerMeyerXiJetPacketFlow rho c
        (deningerMeyerXiJetPacketQuotEquiv rho q) := by
  induction q using Submodule.Quotient.induction_on with
  | _ u =>
      simp only [
        deningerMeyerXiJetPacketQuotientFlow,
        Submodule.mapQ_apply,
        deningerMeyerXiJetPacketQuotEquiv_mk]
      exact deningerMeyerXiJetPacketLM_flow rho c u

end

end RHTower
