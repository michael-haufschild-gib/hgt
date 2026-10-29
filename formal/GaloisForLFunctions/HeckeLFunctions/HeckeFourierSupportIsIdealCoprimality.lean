import GaloisForLFunctions.HeckeLFunctions.HeckeFiniteFourierCoefficientsAreGaussSums
import GaloisForLFunctions.HTGeometry.DedekindIdealQuotientsDetectCoprimality

/-!
# The arithmetic support of primitive Hecke Fourier coefficients

A trace-dual frequency determines the integral ideal obtained by dividing
its principal ideal by the trace-dual ideal. Its residue trace annihilator
is the quotient of the finite modulus by that integral ideal. Dedekind
ideal cancellation therefore identifies additive primitivity with ideal
coprimality. The actual finite Fourier coefficient has precisely this
support and exact squared norm equal to the modulus norm there.

Coprime ordinary-class representatives also construct nonzero primitive
trace frequencies, including for the unit modulus. A proper finite
conductor forces the dual zero mode to vanish.
-/

noncomputable section
open NumberField
open scoped Classical
namespace GaloisForLFunctions.HeckeLFunctions

variable {K : Type*} [Field K] [NumberField K] (𝔪 : Modulus K)
  {b : Ideal (𝓞 K)} (hb0 : b ≠ ⊥)
local notation "FI" => FractionalIdeal (nonZeroDivisors (𝓞 K)) K
local notation "Jdual" => FractionalIdeal.dual ℤ ℚ ((𝔪.fin * b : Ideal (𝓞 K)) : FI)

include hb0

theorem heckeDualProductIdeal_ne_zero : Jdual ≠ 0 := by
  apply FractionalIdeal.dual_ne_zero ℤ ℚ
  exact FractionalIdeal.coeIdeal_ne_zero.mpr (mul_ne_zero 𝔪.fin_ne_bot hb0)

/-- Dividing a frequency's principal ideal by its trace-dual ideal gives an integral ideal. -/
theorem heckeDualFrequencyFractionalIdeal_le_one (a : Jdual) :
    FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) (a : K) * Jdual⁻¹ ≤ 1 := by
  calc
    FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) (a : K) * Jdual⁻¹ ≤ Jdual * Jdual⁻¹ :=
      mul_le_mul_left (FractionalIdeal.spanSingleton_le_iff_mem.mpr a.2) _
    _ = 1 := mul_inv_cancel₀ (heckeDualProductIdeal_ne_zero 𝔪 hb0)

/-- The actual integral ideal attached to a frequency in the dual theta sum. -/
def heckeDualFrequencyIdeal (a : Jdual) : Ideal (𝓞 K) :=
  Classical.choose (FractionalIdeal.le_one_iff_exists_coeIdeal.mp
    (heckeDualFrequencyFractionalIdeal_le_one 𝔪 hb0 a))

theorem coe_heckeDualFrequencyIdeal (a : Jdual) :
    (heckeDualFrequencyIdeal 𝔪 hb0 a : FI) =
      FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) (a : K) * Jdual⁻¹ :=
  Classical.choose_spec (FractionalIdeal.le_one_iff_exists_coeIdeal.mp
    (heckeDualFrequencyFractionalIdeal_le_one 𝔪 hb0 a))

theorem heckeDualFrequencyIdeal_mul_dual (a : Jdual) :
    (heckeDualFrequencyIdeal 𝔪 hb0 a : FI) * Jdual =
      FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) (a : K) := by
  rw [coe_heckeDualFrequencyIdeal, mul_assoc,
    inv_mul_cancel₀ (heckeDualProductIdeal_ne_zero 𝔪 hb0), mul_one]

theorem heckeDualFrequencyIdeal_eq_bot_iff (a : Jdual) :
    heckeDualFrequencyIdeal 𝔪 hb0 a = ⊥ ↔ (a : K) = 0 := by
  rw [← FractionalIdeal.coeIdeal_eq_zero (K := K), coe_heckeDualFrequencyIdeal,
    mul_eq_zero, inv_eq_zero, or_iff_left (heckeDualProductIdeal_ne_zero 𝔪 hb0),
    FractionalIdeal.spanSingleton_eq_zero_iff]

/-- Every trace-dual ideal has a nonzero frequency whose associated integral ideal is coprime. -/
theorem exists_heckeDualFrequencyIdeal_coprime :
    ∃ a : Jdual, (a : K) ≠ 0 ∧ heckeDualFrequencyIdeal 𝔪 hb0 a ⊔ 𝔪.fin = ⊤ := by
  let J : FIˣ := Units.mk0 Jdual (heckeDualProductIdeal_ne_zero 𝔪 hb0)
  obtain ⟨I, hI0, hIm, hclass⟩ := exists_integral_rep 𝔪 (ClassGroup.mk K J)⁻¹
  have hprincipal :
      (↑((idealUnit hI0 * J : FIˣ) : FI) : Submodule (𝓞 K) K).IsPrincipal := by
    apply (ClassGroup.mk_eq_one_iff).mp
    rw [map_mul, hclass, inv_mul_cancel]
  obtain ⟨a, ha⟩ := hprincipal.principal
  have hspan : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) a = (I : FI) * Jdual := by
    apply FractionalIdeal.coeToSubmodule_injective
    change (↑(FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) a) :
      Submodule (𝓞 K) K) = (↑((I : FI) * Jdual) : Submodule (𝓞 K) K)
    rw [FractionalIdeal.coe_spanSingleton]
    simpa only [Units.val_mul, coe_idealUnit, J, Units.val_mk0] using ha.symm
  have ha0 : a ≠ 0 := by
    apply (FractionalIdeal.spanSingleton_ne_zero_iff (S := nonZeroDivisors (𝓞 K))).mp
    rw [hspan]
    exact mul_ne_zero (FractionalIdeal.coeIdeal_ne_zero.mpr hI0)
      (heckeDualProductIdeal_ne_zero 𝔪 hb0)
  have haJ : a ∈ Jdual := by
    apply FractionalIdeal.spanSingleton_le_iff_mem.mp
    rw [hspan]
    exact (mul_le_mul_left (FractionalIdeal.coeIdeal_le_one (I := I)) Jdual).trans_eq
      (one_mul Jdual)
  let aJ : Jdual := ⟨a, haJ⟩
  have hI : heckeDualFrequencyIdeal 𝔪 hb0 aJ = I := by
    apply FractionalIdeal.coeIdeal_injective (K := K)
    change (heckeDualFrequencyIdeal 𝔪 hb0 aJ : FI) = (I : FI)
    rw [coe_heckeDualFrequencyIdeal]
    change FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) a * Jdual⁻¹ = (I : FI)
    rw [hspan, mul_assoc, mul_inv_cancel₀ (heckeDualProductIdeal_ne_zero 𝔪 hb0), mul_one]
  exact ⟨aJ, ha0, hI ▸ hIm⟩

omit hb0 in
/-- Multiplication by the finite modulus recovers the trace dual of the original ideal. -/
theorem heckeDualProductIdeal_mul_modulus :
    Jdual * (𝔪.fin : FI) = FractionalIdeal.dual ℤ ℚ (b : FI) := by
  have hmF : (𝔪.fin : FI) ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.mpr 𝔪.fin_ne_bot
  rw [FractionalIdeal.dual_eq_mul_inv ℤ ℚ ((𝔪.fin * b : Ideal (𝓞 K)) : FI),
    FractionalIdeal.dual_eq_mul_inv ℤ ℚ (b : FI)]
  simp only [FractionalIdeal.coeIdeal_mul, mul_inv_rev, mul_assoc,
    inv_mul_cancel₀ hmF, mul_one]

/-- The trace-frequency annihilator is precisely the ideal quotient by its associated ideal. -/
theorem mem_colon_heckeDualFrequencyIdeal_iff (a : Jdual) (r : 𝓞 K) :
    r ∈ 𝔪.fin.colon (heckeDualFrequencyIdeal 𝔪 hb0 a : Set (𝓞 K)) ↔
      (r : K) * (a : K) ∈ FractionalIdeal.dual ℤ ℚ (b : FI) := by
  rw [Submodule.mem_colon_iff_le, ← Submodule.span_singleton_mul]
  change Ideal.span {r} * heckeDualFrequencyIdeal 𝔪 hb0 a ≤ 𝔪.fin ↔ _
  rw [← FractionalIdeal.coeIdeal_le_coeIdeal K, FractionalIdeal.coeIdeal_mul,
    FractionalIdeal.coeIdeal_span_singleton, ← RingOfIntegers.coe_eq_algebraMap]
  rw [← mul_le_mul_iff_left₀ (pos_iff_ne_zero.mpr (heckeDualProductIdeal_ne_zero 𝔪 hb0))]
  rw [mul_assoc, heckeDualFrequencyIdeal_mul_dual,
    FractionalIdeal.spanSingleton_mul_spanSingleton,
    mul_comm (𝔪.fin : FI) Jdual, heckeDualProductIdeal_mul_modulus 𝔪,
    FractionalIdeal.spanSingleton_le_iff_mem]

variable (hb : b ⊔ 𝔪.fin = ⊤)

/-- The actual additive trace character is primitive exactly on ideals coprime to the modulus. -/
theorem heckeResidueTraceCharacter_isPrimitive_iff_coprime (a : Jdual) :
    (heckeResidueTraceCharacter 𝔪 hb hb0 a).IsPrimitive ↔
      heckeDualFrequencyIdeal 𝔪 hb0 a ⊔ 𝔪.fin = ⊤ := by
  rw [heckeResidueTraceCharacter_isPrimitive_iff]
  rw [sup_comm, ← HTGeometry.ideal_colon_eq_self_iff_sup_eq_top
    𝔪.fin (heckeDualFrequencyIdeal 𝔪 hb0 a) 𝔪.fin_ne_bot]
  constructor
  · intro h
    apply le_antisymm _ Ideal.le_colon
    intro r hr
    exact h r ((mem_colon_heckeDualFrequencyIdeal_iff 𝔪 hb0 a r).mp hr)
  · intro h r hr
    rw [← h]
    exact (mem_colon_heckeDualFrequencyIdeal_iff 𝔪 hb0 a r).mpr hr

/-- The support of the primitive dual-theta coefficient is the actual coprime ideal condition. -/
theorem finiteHeckeFourierCoefficient_ne_zero_iff_coprime (ψ : HeckeCharacter 𝔪)
    (hψ : heckeFiniteConductor 𝔪 ψ = 𝔪.fin) (a : Jdual) :
    finiteHeckeFourierCoefficient 𝔪 hb ψ (a : K) ≠ 0 ↔
      heckeDualFrequencyIdeal 𝔪 hb0 a ⊔ 𝔪.fin = ⊤ := by
  rw [finiteHeckeFourierCoefficient_ne_zero_iff 𝔪 hb hb0 ψ hψ,
    heckeResidueTraceCharacter_isPrimitive_iff_coprime]

/-- Exact Gauss mass on the arithmetic support of the primitive dual theta sum. -/
theorem norm_finiteHeckeFourierCoefficient_sq_eq_coprime (ψ : HeckeCharacter 𝔪)
    (hψ : heckeFiniteConductor 𝔪 ψ = 𝔪.fin) (a : Jdual) :
    ‖finiteHeckeFourierCoefficient 𝔪 hb ψ (a : K)‖ ^ 2 =
      if heckeDualFrequencyIdeal 𝔪 hb0 a ⊔ 𝔪.fin = ⊤ then
        (Ideal.absNorm 𝔪.fin : ℝ) else 0 := by
  rw [norm_finiteHeckeFourierCoefficient_sq 𝔪 hb hb0 ψ hψ,
    heckeResidueTraceCharacter_isPrimitive_iff_coprime]
  split_ifs <;> rfl

/-- A primitive character with nonunit finite conductor has no dual zero mode. -/
theorem finiteHeckeFourierCoefficient_zero_of_finiteConductor_ne_top (ψ : HeckeCharacter 𝔪)
    (hψ : heckeFiniteConductor 𝔪 ψ = 𝔪.fin) (hm : 𝔪.fin ≠ ⊤) :
    finiteHeckeFourierCoefficient 𝔪 hb ψ 0 = 0 := by
  let a : Jdual := ⟨0, FractionalIdeal.zero_mem _⟩
  have ha : heckeDualFrequencyIdeal 𝔪 hb0 a = ⊥ :=
    (heckeDualFrequencyIdeal_eq_bot_iff 𝔪 hb0 a).mpr rfl
  by_contra h
  have hc := (finiteHeckeFourierCoefficient_ne_zero_iff_coprime 𝔪 hb0 hb ψ hψ a).mp h
  rw [ha, bot_sup_eq] at hc
  exact hm hc

end GaloisForLFunctions.HeckeLFunctions
