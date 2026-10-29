import GaloisForLFunctions.HeckeLFunctions.HeckeFiniteCharactersHavePrimitiveConductors
import GaloisForLFunctions.HeckeLFunctions.HeckeThetaHasAFiniteFourierTransform
import GaloisForLFunctions.HTGeometry.PrimitiveGaussSumsDetectPrimitiveAdditiveCharacters
import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-!
# Actual Hecke Fourier coefficients are Gauss sums

Every frequency in the trace dual of the modulus-product ideal defines
an additive character of the residue ring. Integral traces make this
independent of representatives and identify its kernel with the smaller
ideal's trace dual. Thus the finite theta coefficient is an actual Gauss
sum. At the finite conductor, it scales by the inverse residue character,
and its squared norm is zero or the modulus norm according to additive
primitivity. Primitivity is also expressed as an integral annihilator
condition, ready for arithmetic ideal reindexing.
-/

noncomputable section
open NumberField
open scoped Classical
namespace GaloisForLFunctions.HeckeLFunctions

variable {K : Type*} [Field K] [NumberField K]
local notation "FI" => FractionalIdeal (nonZeroDivisors (𝓞 K)) K

theorem numberFieldTracePhase_eq_exp (x a : K) :
    numberFieldTracePhase x a =
      Complex.exp ((Algebra.trace ℚ K (x * a) : ℂ) * (2 * Real.pi * Complex.I)) := by
  unfold numberFieldTracePhase
  congr 1
  push_cast
  ring

theorem numberFieldTracePhase_zero (a : K) : numberFieldTracePhase 0 a = 1 := by
  simp only [numberFieldTracePhase, zero_mul, map_zero, Rat.cast_zero, mul_zero,
    Complex.ofReal_zero, Complex.exp_zero]

theorem numberFieldTracePhase_add (x y a : K) :
    numberFieldTracePhase (x + y) a = numberFieldTracePhase x a * numberFieldTracePhase y a := by
  simp only [numberFieldTracePhase_eq_exp, add_mul, map_add, Rat.cast_add, Complex.exp_add]

theorem numberFieldTracePhase_mul_left (r x a : K) :
    numberFieldTracePhase (r * x) a = numberFieldTracePhase x (r * a) := by
  unfold numberFieldTracePhase
  rw [show (r * x) * a = x * (r * a) by ring]

/-- The trace phase is trivial exactly on integral rational traces. -/
theorem numberFieldTracePhase_eq_one_iff (x a : K) :
    numberFieldTracePhase x a = 1 ↔ ∃ n : ℤ, (n : ℚ) = Algebra.trace ℚ K (x * a) := by
  rw [numberFieldTracePhase_eq_exp, Complex.exp_eq_one_iff]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have h := mul_right_cancel₀ Complex.two_pi_I_ne_zero hn
    exact_mod_cast h.symm
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    rw [← hn]
    norm_cast

variable (𝔪 : Modulus K) {b : Ideal (𝓞 K)} (hb : b ⊔ 𝔪.fin = ⊤) (hb0 : b ≠ ⊥)

local instance : Finite (𝓞 K ⧸ 𝔪.fin) :=
  𝔪.fin.finiteQuotientOfFreeOfNeBot 𝔪.fin_ne_bot
local instance : Fintype (𝓞 K ⧸ 𝔪.fin) := Fintype.ofFinite _

/-- Multiplication by an algebraic integer preserves the actual trace-dual ideal. -/
def heckeTraceFrequencyMul (r : 𝓞 K)
    (a : FractionalIdeal.dual ℤ ℚ ((𝔪.fin * b : Ideal (𝓞 K)) : FI)) :
    FractionalIdeal.dual ℤ ℚ ((𝔪.fin * b : Ideal (𝓞 K)) : FI) :=
  ⟨(r : K) * (a : K), by
    have h := Submodule.smul_mem
      (FractionalIdeal.dual ℤ ℚ ((𝔪.fin * b : Ideal (𝓞 K)) : FI) : Submodule (𝓞 K) K) r a.2
    simpa only [Algebra.smul_def, ← RingOfIntegers.coe_eq_algebraMap,
      FractionalIdeal.mem_coe] using h⟩

include hb hb0

/-- Equal residues in a coprime ideal have the same phase against its modulus-product dual. -/
theorem numberFieldTracePhase_eq_of_quotient_eq
    (a : FractionalIdeal.dual ℤ ℚ ((𝔪.fin * b : Ideal (𝓞 K)) : FI))
    {x y : 𝓞 K} (hx : x ∈ b) (hy : y ∈ b)
    (hxy : Ideal.Quotient.mk 𝔪.fin x = Ideal.Quotient.mk 𝔪.fin y) :
    numberFieldTracePhase (x : K) (a : K) = numberFieldTracePhase (y : K) (a : K) := by
  have hd : x - y ∈ 𝔪.fin * b := by
    rw [Ideal.mul_eq_inf_of_isCoprime
      (Ideal.isCoprime_iff_sup_eq.mpr (by rw [sup_comm, hb]))]
    exact ⟨Ideal.Quotient.eq.mp hxy, sub_mem hx hy⟩
  have hI : ((𝔪.fin * b : Ideal (𝓞 K)) : FI) ≠ 0 := by
    rw [← coe_idealUnit (mul_ne_zero 𝔪.fin_ne_bot hb0)]
    exact Units.ne_zero _
  obtain ⟨n, hn⟩ := (FractionalIdeal.mem_dual hI).mp a.2 ((x - y : 𝓞 K) : K)
    (FractionalIdeal.mem_coeIdeal_of_mem (nonZeroDivisors (𝓞 K)) hd)
  change (n : ℚ) = Algebra.trace ℚ K ((a : K) * ((x - y : 𝓞 K) : K)) at hn
  have hp : numberFieldTracePhase ((x : K) - (y : K)) (a : K) = 1 := by
    apply (numberFieldTracePhase_eq_one_iff _ _).mpr
    refine ⟨n, ?_⟩
    simpa only [map_sub, mul_comm] using hn
  have h := numberFieldTracePhase_add ((x : K) - (y : K)) (y : K) (a : K)
  rw [sub_add_cancel, hp, one_mul] at h
  exact h

/-- A trace-dual frequency defines an actual additive character of the finite residue ring. -/
def heckeResidueTraceCharacter
    (a : FractionalIdeal.dual ℤ ℚ ((𝔪.fin * b : Ideal (𝓞 K)) : FI)) :
    AddChar (𝓞 K ⧸ 𝔪.fin) ℂ where
  toFun ρ := numberFieldTracePhase (residueRep 𝔪 hb ρ : K) (a : K)
  map_zero_eq_one' := by
    rw [numberFieldTracePhase_eq_of_quotient_eq 𝔪 hb hb0 a
      (residueRep_mem hb _) (Ideal.zero_mem b)
      (by rw [mk_residueRep, map_zero])]
    exact numberFieldTracePhase_zero _
  map_add_eq_mul' := by
    intro ρ σ
    have h := numberFieldTracePhase_eq_of_quotient_eq 𝔪 hb hb0 a
      (residueRep_mem hb (ρ + σ)) (add_mem (residueRep_mem hb ρ) (residueRep_mem hb σ))
      (by rw [mk_residueRep, map_add, mk_residueRep, mk_residueRep])
    rw [h]
    change numberFieldTracePhase ((residueRep 𝔪 hb ρ : K) + (residueRep 𝔪 hb σ : K)) (a : K) = _
    exact numberFieldTracePhase_add _ _ _

theorem heckeResidueTraceCharacter_apply
    (a : FractionalIdeal.dual ℤ ℚ ((𝔪.fin * b : Ideal (𝓞 K)) : FI)) (ρ : 𝓞 K ⧸ 𝔪.fin) :
    heckeResidueTraceCharacter 𝔪 hb hb0 a ρ =
      numberFieldTracePhase (residueRep 𝔪 hb ρ : K) (a : K) := rfl

/-- Multiplication of a trace-dual frequency is the multiplicative shift of its residue character. -/
theorem heckeResidueTraceCharacter_smul
    (a : FractionalIdeal.dual ℤ ℚ ((𝔪.fin * b : Ideal (𝓞 K)) : FI)) (r : 𝓞 K) :
    heckeResidueTraceCharacter 𝔪 hb hb0 (heckeTraceFrequencyMul 𝔪 r a) =
      (heckeResidueTraceCharacter 𝔪 hb hb0 a).mulShift (Ideal.Quotient.mk 𝔪.fin r) := by
  ext ρ
  change numberFieldTracePhase (residueRep 𝔪 hb ρ : K) (((r : 𝓞 K) : K) * (a : K)) =
    numberFieldTracePhase (residueRep 𝔪 hb (Ideal.Quotient.mk 𝔪.fin r * ρ) : K) (a : K)
  rw [← numberFieldTracePhase_mul_left]
  symm
  have h := numberFieldTracePhase_eq_of_quotient_eq 𝔪 hb hb0 a
    (residueRep_mem hb _) (b.mul_mem_left r (residueRep_mem hb ρ))
    (by rw [mk_residueRep, map_mul, mk_residueRep])
  simpa only [map_mul] using h

/-- A residue trace character is trivial exactly when its frequency lies in the smaller ideal dual. -/
theorem heckeResidueTraceCharacter_eq_one_iff
    (a : FractionalIdeal.dual ℤ ℚ ((𝔪.fin * b : Ideal (𝓞 K)) : FI)) :
    heckeResidueTraceCharacter 𝔪 hb hb0 a = 1 ↔
      (a : K) ∈ FractionalIdeal.dual ℤ ℚ (b : FI) := by
  have hbF : (b : FI) ≠ 0 := by
    rw [← coe_idealUnit hb0]
    exact Units.ne_zero _
  constructor
  · intro h
    apply (FractionalIdeal.mem_dual hbF).mpr
    intro x hx
    obtain ⟨r, hr, rfl⟩ := (FractionalIdeal.mem_coeIdeal (nonZeroDivisors (𝓞 K))).mp hx
    have hp := DFunLike.congr_fun h (Ideal.Quotient.mk 𝔪.fin r)
    change numberFieldTracePhase (residueRep 𝔪 hb (Ideal.Quotient.mk 𝔪.fin r) : K) (a : K) = 1 at hp
    rw [numberFieldTracePhase_eq_of_quotient_eq 𝔪 hb hb0 a
      (residueRep_mem hb _) hr (mk_residueRep hb _)] at hp
    obtain ⟨n, hn⟩ := (numberFieldTracePhase_eq_one_iff _ _).mp hp
    refine ⟨n, ?_⟩
    change (n : ℚ) = Algebra.trace ℚ K ((a : K) * (r : K))
    simpa only [mul_comm] using hn
  · intro h
    ext ρ
    change numberFieldTracePhase (residueRep 𝔪 hb ρ : K) (a : K) = 1
    obtain ⟨n, hn⟩ := (FractionalIdeal.mem_dual hbF).mp h (residueRep 𝔪 hb ρ : K)
      (FractionalIdeal.mem_coeIdeal_of_mem (nonZeroDivisors (𝓞 K)) (residueRep_mem hb _))
    apply (numberFieldTracePhase_eq_one_iff _ _).mpr
    refine ⟨n, ?_⟩
    change (n : ℚ) = Algebra.trace ℚ K ((a : K) * (residueRep 𝔪 hb ρ : K)) at hn
    simpa only [mul_comm] using hn

theorem heckeResidueTraceCharacter_mulShift_eq_one_iff
    (a : FractionalIdeal.dual ℤ ℚ ((𝔪.fin * b : Ideal (𝓞 K)) : FI)) (r : 𝓞 K) :
    (heckeResidueTraceCharacter 𝔪 hb hb0 a).mulShift (Ideal.Quotient.mk 𝔪.fin r) = 1 ↔
      (r : K) * (a : K) ∈ FractionalIdeal.dual ℤ ℚ (b : FI) := by
  rw [← heckeResidueTraceCharacter_smul, heckeResidueTraceCharacter_eq_one_iff]
  rfl

/-- Additive primitivity is exactly the absence of a larger integral annihilator than the modulus. -/
theorem heckeResidueTraceCharacter_isPrimitive_iff
    (a : FractionalIdeal.dual ℤ ℚ ((𝔪.fin * b : Ideal (𝓞 K)) : FI)) :
    (heckeResidueTraceCharacter 𝔪 hb hb0 a).IsPrimitive ↔
      ∀ r : 𝓞 K, (r : K) * (a : K) ∈ FractionalIdeal.dual ℤ ℚ (b : FI) → r ∈ 𝔪.fin := by
  constructor
  · intro h r hr
    have hz : Ideal.Quotient.mk 𝔪.fin r = 0 := by
      by_contra hne
      exact h hne ((heckeResidueTraceCharacter_mulShift_eq_one_iff 𝔪 hb hb0 a r).mpr hr)
    exact Ideal.Quotient.eq_zero_iff_mem.mp hz
  · intro h ρ hρ hz
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective ρ
    exact hρ (Ideal.Quotient.eq_zero_iff_mem.mpr
      (h r ((heckeResidueTraceCharacter_mulShift_eq_one_iff 𝔪 hb hb0 a r).mp hz)))

/-- The finite coefficient in arithmetic theta inversion is the actual residue-ring Gauss sum. -/
theorem finiteHeckeFourierCoefficient_eq_gaussSum (ψ : HeckeCharacter 𝔪)
    (a : FractionalIdeal.dual ℤ ℚ ((𝔪.fin * b : Ideal (𝓞 K)) : FI)) :
    finiteHeckeFourierCoefficient 𝔪 hb ψ (a : K) =
      gaussSum (finiteHeckeWeight 𝔪 ψ) (heckeResidueTraceCharacter 𝔪 hb hb0 a) := by
  rw [finiteHeckeFourierCoefficient, tsum_fintype]
  rfl

/-- Primitive Hecke Fourier coefficients transform by the inverse finite character. -/
theorem finiteHeckeFourierCoefficient_smul (ψ : HeckeCharacter 𝔪)
    (hψ : heckeFiniteConductor 𝔪 ψ = 𝔪.fin)
    (a : FractionalIdeal.dual ℤ ℚ ((𝔪.fin * b : Ideal (𝓞 K)) : FI)) (r : 𝓞 K) :
    finiteHeckeFourierCoefficient 𝔪 hb ψ ((r : K) * (a : K)) =
      (finiteHeckeWeight 𝔪 ψ)⁻¹ (Ideal.Quotient.mk 𝔪.fin r) *
        finiteHeckeFourierCoefficient 𝔪 hb ψ (a : K) := by
  change finiteHeckeFourierCoefficient 𝔪 hb ψ (heckeTraceFrequencyMul 𝔪 r a : K) = _
  rw [finiteHeckeFourierCoefficient_eq_gaussSum 𝔪 hb hb0 ψ (heckeTraceFrequencyMul 𝔪 r a),
    finiteHeckeFourierCoefficient_eq_gaussSum 𝔪 hb hb0 ψ a,
    heckeResidueTraceCharacter_smul]
  exact FiniteRing.gaussSum_mulShift_eq_of_isPrimitive
    ((finiteHeckeWeight_isPrimitive_iff 𝔪 ψ).mpr hψ) _ _

/-- Nonzero primitive Hecke Fourier coefficients are exactly the primitive trace characters. -/
theorem finiteHeckeFourierCoefficient_ne_zero_iff (ψ : HeckeCharacter 𝔪)
    (hψ : heckeFiniteConductor 𝔪 ψ = 𝔪.fin)
    (a : FractionalIdeal.dual ℤ ℚ ((𝔪.fin * b : Ideal (𝓞 K)) : FI)) :
    finiteHeckeFourierCoefficient 𝔪 hb ψ (a : K) ≠ 0 ↔
      (heckeResidueTraceCharacter 𝔪 hb hb0 a).IsPrimitive := by
  rw [finiteHeckeFourierCoefficient_eq_gaussSum 𝔪 hb hb0]
  exact FiniteRing.gaussSum_ne_zero_iff_isPrimitive
    ((finiteHeckeWeight_isPrimitive_iff 𝔪 ψ).mpr hψ) _

/-- The exact squared norm of each primitive Hecke Fourier coefficient. -/
theorem norm_finiteHeckeFourierCoefficient_sq (ψ : HeckeCharacter 𝔪)
    (hψ : heckeFiniteConductor 𝔪 ψ = 𝔪.fin)
    (a : FractionalIdeal.dual ℤ ℚ ((𝔪.fin * b : Ideal (𝓞 K)) : FI)) :
    ‖finiteHeckeFourierCoefficient 𝔪 hb ψ (a : K)‖ ^ 2 =
      if (heckeResidueTraceCharacter 𝔪 hb hb0 a).IsPrimitive then
        (Ideal.absNorm 𝔪.fin : ℝ) else 0 := by
  rw [finiteHeckeFourierCoefficient_eq_gaussSum 𝔪 hb hb0]
  have h := FiniteRing.norm_gaussSum_sq_eq_ite
    ((finiteHeckeWeight_isPrimitive_iff 𝔪 ψ).mpr hψ) (heckeResidueTraceCharacter 𝔪 hb hb0 a)
  change ‖gaussSum (finiteHeckeWeight 𝔪 ψ) (heckeResidueTraceCharacter 𝔪 hb hb0 a)‖ ^ 2 =
    if (heckeResidueTraceCharacter 𝔪 hb hb0 a).IsPrimitive then (Nat.card (𝓞 K ⧸ 𝔪.fin) : ℝ) else 0
  simpa only [Nat.card_eq_fintype_card] using h

end GaloisForLFunctions.HeckeLFunctions
