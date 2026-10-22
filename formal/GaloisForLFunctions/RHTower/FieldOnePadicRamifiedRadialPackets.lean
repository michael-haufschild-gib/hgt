import GaloisForLFunctions.RHTower.FieldOnePadicBruhatFourierDilation

/-!
# Ramified radial packets on `ℚ_p` and their Fourier transforms

For a primitive Dirichlet character `χ` of conductor exactly `pⁿ`, the angular packet is the
Schwartz–Bruhat function `x ↦ χ(x mod pⁿ)` on `ℤ_p` (zero off `ℤ_p`), and the radial packet of
height `m ∈ ℤ` is its dilate `x ↦ packet(p^{-m} x)`. In the coordinates
`ℚ_p^× ≅ ℤ × ℤ_p^×`, `(k, u) ↦ p^k u`, the module computes both the packet and its Fourier
transform exactly: the radial packet is `χ(ū)` on the shell `k = m` and zero elsewhere, and its
Fourier transform is concentrated on the single shell `k = -m - n`, where it equals
`p^{-m} · p^{-n} · χ⁻¹(-ū) · g(χ)` with `g(χ)` the Gauss sum.

## Main results

- `fieldOnePadicPrimitiveRadialPacket_coordinates`: the radial packet at `p^k u` is
  `χ(ū)` if `k = m` and `0` otherwise.
- `fieldOnePadicPrimitiveAngularPacket_fourier_coordinates`: the Fourier transform of the
  angular packet at `p^k u` is `p^{-n} χ⁻¹(-ū) g(χ)` if `k = -n` and `0` otherwise.
- `fieldOnePadicPrimitiveRadialPacket_fourier_coordinates`: the Fourier transform of the radial
  packet at `p^k u` is `p^{-m} · p^{-n} χ⁻¹(-ū) g(χ)` if `k = -m - n` and `0` otherwise.

## Hypotheses

Unconditional. The coordinate formulas assume `0 < n`, i.e. the character is genuinely ramified.
-/

namespace GaloisForLFunctions.RHTower

noncomputable section

open MeasureTheory Set
open scoped NNReal ENNReal

variable (p : ℕ) [Fact p.Prime]

/-- The inverse `χ⁻¹` of a primitive character of conductor `pⁿ`, again primitive of conductor
`pⁿ`. -/
def fieldOnePadicPrimitiveAngularCharacterInv (n : ℕ)
    (χ : FieldOnePadicPrimitiveAngularCharacter p n) :
    FieldOnePadicPrimitiveAngularCharacter p n :=
  ⟨χ.1⁻¹, by
    rw [DirichletCharacter.isPrimitive_def,
      DirichletCharacter.conductor_inv,
      ← DirichletCharacter.isPrimitive_def]
    exact χ.2⟩

omit [Fact p.Prime] in
@[simp] theorem fieldOnePadicPrimitiveAngularCharacterInv_apply
    (n : ℕ) (χ : FieldOnePadicPrimitiveAngularCharacter p n)
    (x : ZMod (p ^ n)) :
    (fieldOnePadicPrimitiveAngularCharacterInv p n χ).1 x = χ.1⁻¹ x :=
  rfl

/-- Radial packet of height `m`: the dilate `x ↦ packet_χ(p^{-m} x)` of the angular packet,
supported on `p^m ℤ_p`. -/
def fieldOnePadicPrimitiveRadialPacket (n : ℕ)
    (χ : FieldOnePadicPrimitiveAngularCharacter p n) (m : ℤ) :
    compactlySupportedLocallyConstant ℚ_[p] :=
  fieldOnePadicBruhatDilation p
    ((fieldOnePadicPrimeUnit p) ^ (-m))
    (fieldOnePadicPrimitiveAngularPacket p n χ)

@[simp] theorem fieldOnePadicPrimitiveRadialPacket_apply
    (n : ℕ) (χ : FieldOnePadicPrimitiveAngularCharacter p n)
    (m : ℤ) (x : ℚ_[p]) :
    (fieldOnePadicPrimitiveRadialPacket p n χ m).1 x =
      (fieldOnePadicPrimitiveAngularPacket p n χ).1
        (((fieldOnePadicPrimeUnit p) ^ (-m) : ℚ_[p]ˣ) * x) :=
  rfl

/-- For `0 < n`, the residue of `p` is not a unit in `ℤ/pⁿ`. -/
theorem fieldOnePadicPrime_nonunit_zmod_pow
    (n : ℕ) (hn : 0 < n) :
    ¬IsUnit (p : ZMod (p ^ n)) := by
  rw [ZMod.isUnit_iff_coprime]
  rw [Nat.Prime.coprime_iff_not_dvd (Fact.out : Nat.Prime p)]
  exact fun h => h (dvd_pow_self p hn.ne')

/-- For `0 < n` and `r ∈ ℕ`, the angular packet at `p^r u` (`u` a unit) is `χ(ū)` if `r = 0`
and `0` otherwise. -/
theorem fieldOnePadicPrimitiveAngularPacket_primePow_unit
    (n : ℕ) (hn : 0 < n)
    (χ : FieldOnePadicPrimitiveAngularCharacter p n)
    (r : ℕ) (u : ℤ_[p]ˣ) :
    (fieldOnePadicPrimitiveAngularPacket p n χ).1
        ((p : ℚ_[p]) ^ r * ((u : ℤ_[p]) : ℚ_[p])) =
      if r = 0 then χ.1 (fieldOnePadicUnitReduction p n u) else 0 := by
  have hcoe : (p : ℚ_[p]) ^ r * ((u : ℤ_[p]) : ℚ_[p]) =
      (((p : ℤ_[p]) ^ r * (u : ℤ_[p]) : ℤ_[p]) : ℚ_[p]) := by
    norm_cast
  rw [hcoe]
  change fieldOnePadicPrimitiveAngularPacketLC p n χ
    ((((p : ℤ_[p]) ^ r * (u : ℤ_[p]) : ℤ_[p])) : ℚ_[p]) = _
  rw [fieldOnePadicPrimitiveAngularPacketLC_coe]
  unfold fieldOnePadicPrimitiveAngularLift
  rw [map_mul, map_pow, map_natCast]
  by_cases hr : r = 0
  · subst r
    simp [fieldOnePadicUnitReduction]
  · rw [if_neg hr]
    have hpzero : χ.1 (p : ZMod (p ^ n)) = 0 :=
      MulChar.map_nonunit χ.1 (fieldOnePadicPrime_nonunit_zmod_pow p n hn)
    rw [map_mul, map_pow, hpzero, zero_pow hr, zero_mul]

/-- For `0 < n` and `k ∈ ℤ`, the angular packet at `p^k u` (`u` a unit) is `χ(ū)` if `k = 0`
and `0` otherwise; negative `k` lies outside `ℤ_p`. -/
theorem fieldOnePadicPrimitiveAngularPacket_primeZPow_unit
    (n : ℕ) (hn : 0 < n)
    (χ : FieldOnePadicPrimitiveAngularCharacter p n)
    (k : ℤ) (u : ℤ_[p]ˣ) :
    (fieldOnePadicPrimitiveAngularPacket p n χ).1
        ((p : ℚ_[p]) ^ k * ((u : ℤ_[p]) : ℚ_[p])) =
      if k = 0 then χ.1 (fieldOnePadicUnitReduction p n u) else 0 := by
  by_cases hk : 0 ≤ k
  · obtain ⟨r, rfl⟩ := Int.eq_ofNat_of_zero_le hk
    simpa using
      fieldOnePadicPrimitiveAngularPacket_primePow_unit p n hn χ r u
  · have hkneg : k < 0 := lt_of_not_ge hk
    have hout : (p : ℚ_[p]) ^ k * ((u : ℤ_[p]) : ℚ_[p]) ∉
        fieldOnePadicUnitBall p := by
      rintro ⟨z, hz⟩
      have hval := congrArg Padic.valuation hz
      rw [Padic.valuation_mul, Padic.valuation_zpow,
        Padic.valuation_p, fieldOnePadic_valuation_coe_unit,
        PadicInt.valuation_coe] at hval
      · simp only [mul_one, add_zero] at hval
        omega
      · exact zpow_ne_zero _ (by exact_mod_cast
          (Fact.out : Nat.Prime p).ne_zero)
      · exact PadicInt.coe_ne_zero.mpr (Units.ne_zero u)
    change fieldOnePadicPrimitiveAngularPacketLC p n χ
      ((p : ℚ_[p]) ^ k * ((u : ℤ_[p]) : ℚ_[p])) = _
    rw [fieldOnePadicPrimitiveAngularPacketLC_eq_zero_of_notMem p n χ hout]
    rw [if_neg (ne_of_lt hkneg)]

/-- For `0 < n`, the radial packet of height `m` at `p^k u` is `χ(ū)` if `k = m` and `0`
otherwise: it lives on the single shell `p^m ℤ_p^×`. -/
theorem fieldOnePadicPrimitiveRadialPacket_coordinates
    (n : ℕ) (hn : 0 < n)
    (χ : FieldOnePadicPrimitiveAngularCharacter p n)
    (m k : ℤ) (u : ℤ_[p]ˣ) :
    (fieldOnePadicPrimitiveRadialPacket p n χ m).1
        ((fieldOnePadicValuationUnitContinuousMulEquiv p)
          (Multiplicative.ofAdd k, u) : ℚ_[p]ˣ) =
      if k = m then χ.1 (fieldOnePadicUnitReduction p n u) else 0 := by
  rw [fieldOnePadicPrimitiveRadialPacket_apply]
  have hcoord :
      (((fieldOnePadicValuationUnitContinuousMulEquiv p)
          (Multiplicative.ofAdd k, u) : ℚ_[p]ˣ) : ℚ_[p]) =
        (p : ℚ_[p]) ^ k * ((u : ℤ_[p]) : ℚ_[p]) := rfl
  rw [hcoord]
  rw [Units.val_zpow_eq_zpow_val]
  change (fieldOnePadicPrimitiveAngularPacket p n χ).1
    ((p : ℚ_[p]) ^ (-m) *
      ((p : ℚ_[p]) ^ k * ((u : ℤ_[p]) : ℚ_[p]))) = _
  rw [← mul_assoc, ← zpow_add₀]
  · rw [fieldOnePadicPrimitiveAngularPacket_primeZPow_unit p n hn χ]
    by_cases hkm : k = m
    · subst k
      simp
    · have hsub : -m + k ≠ 0 := by omega
      rw [if_neg hsub, if_neg hkm]
  · exact_mod_cast (Fact.out : Nat.Prime p).ne_zero

/-- For `0 < n`, the Fourier transform of the angular packet at `p^k u` equals
`p^{-n} χ⁻¹(-ū) g(χ)` (Gauss sum `g(χ)`) when `k = -n`, and vanishes on every other shell. -/
theorem fieldOnePadicPrimitiveAngularPacket_fourier_coordinates
    (n : ℕ) (hn : 0 < n)
    (χ : FieldOnePadicPrimitiveAngularCharacter p n)
    (k : ℤ) (u : ℤ_[p]ˣ) :
    fieldOnePadicBruhatFourier p
        (fieldOnePadicPrimitiveAngularPacket p n χ)
        (((fieldOnePadicValuationUnitContinuousMulEquiv p)
          (Multiplicative.ofAdd k, u) : ℚ_[p]ˣ) : ℚ_[p]) =
      if k = -(n : ℤ) then
        (((p ^ n : ℕ) : ℂ)⁻¹ *
          χ.1⁻¹ (-(fieldOnePadicUnitReduction p n u :
            (ZMod (p ^ n))ˣ))) *
          gaussSum χ.1 ZMod.stdAddChar
      else 0 := by
  have hycoord :
      (((fieldOnePadicValuationUnitContinuousMulEquiv p)
          (Multiplicative.ofAdd k, u) : ℚ_[p]ˣ) : ℚ_[p]) =
        (p : ℚ_[p]) ^ k * ((u : ℤ_[p]) : ℚ_[p]) := rfl
  rw [hycoord]
  by_cases hk : -(n : ℤ) ≤ k
  · let r : ℕ := (k + n).toNat
    have hrz : (r : ℤ) = k + n := by
      rw [Int.toNat_of_nonneg]
      omega
    let v : ℤ_[p] := (p : ℤ_[p]) ^ r * (u : ℤ_[p])
    have harg :
        fieldOnePadicInvPowIntCoeAddMonoidHom p n v =
          (p : ℚ_[p]) ^ k * ((u : ℤ_[p]) : ℚ_[p]) := by
      change (fieldOnePadicPrimeInvPowUnit p n : ℚ_[p]) *
          (v : ℚ_[p]) = _
      rw [fieldOnePadicPrimeInvPowUnit_val]
      have hvcoe : (v : ℚ_[p]) =
          (p : ℚ_[p]) ^ r * ((u : ℤ_[p]) : ℚ_[p]) := by
        dsimp only [v]
        norm_cast
      rw [hvcoe]
      rw [← zpow_natCast, ← zpow_neg, ← zpow_natCast,
        ← mul_assoc, ← zpow_add₀]
      · rw [show -(n : ℤ) + r = k by omega]
      · exact_mod_cast (Fact.out : Nat.Prime p).ne_zero
    rw [← harg,
      fieldOnePadicPrimitiveAngularPacket_fourier_invPow p n χ v]
    have hvred : PadicInt.toZModPow n v =
        (p : ZMod (p ^ n)) ^ r *
          (fieldOnePadicUnitReduction p n u : (ZMod (p ^ n))ˣ) := by
      dsimp [v]
      rw [map_mul, map_pow, map_natCast]
      rfl
    rw [hvred]
    by_cases hr : r = 0
    · have hkn : k = -(n : ℤ) := by omega
      subst k
      rw [if_pos rfl]
      congr 3
      simp [r, hr]
    · have hpzero : χ.1⁻¹ (p : ZMod (p ^ n)) = 0 :=
        MulChar.map_nonunit χ.1⁻¹
          (fieldOnePadicPrime_nonunit_zmod_pow p n hn)
      have hcharzero :
          χ.1⁻¹ (-((p : ZMod (p ^ n)) ^ r *
            (fieldOnePadicUnitReduction p n u : (ZMod (p ^ n))ˣ))) = 0 := by
        rw [show -((p : ZMod (p ^ n)) ^ r *
            (fieldOnePadicUnitReduction p n u : (ZMod (p ^ n))ˣ)) =
          (-1) * ((p : ZMod (p ^ n)) ^ r) *
            (fieldOnePadicUnitReduction p n u : (ZMod (p ^ n))ˣ) by ring]
        rw [map_mul, map_mul, map_pow, hpzero, zero_pow hr, mul_zero, zero_mul]
      rw [hcharzero]
      simp only [mul_zero, zero_mul]
      rw [if_neg]
      intro hkn
      apply hr
      apply Nat.cast_injective (R := ℤ)
      rw [hrz, hkn]
      simp
  · have hklt : k < -(n : ℤ) := lt_of_not_ge hk
    have hout : (p : ℚ_[p]) ^ k * ((u : ℤ_[p]) : ℚ_[p]) ∉
        fieldOnePadicDenominatorStage p n := by
      intro hstage
      change ‖(p : ℚ_[p]) ^ n *
        ((p : ℚ_[p]) ^ k * ((u : ℤ_[p]) : ℚ_[p]))‖ ≤ 1 at hstage
      rw [← mul_assoc, ← zpow_natCast, ← zpow_add₀] at hstage
      · rw [norm_mul, Padic.norm_p_zpow] at hstage
        have hu : ‖(((u : ℤ_[p]) : ℚ_[p]))‖ = 1 := by
          simpa only [PadicInt.norm_def] using PadicInt.norm_units u
        rw [hu, mul_one] at hstage
        have hpR : (1 : ℝ) < p := by
          exact_mod_cast (Fact.out : Nat.Prime p).one_lt
        rw [zpow_le_one_iff_right₀ hpR] at hstage
        omega
      · exact_mod_cast (Fact.out : Nat.Prime p).ne_zero
    have hzero := fieldOnePadicPrimitiveAngularPacket_fourier_support p n χ
    have hnotSupport :
        (p : ℚ_[p]) ^ k * ((u : ℤ_[p]) : ℚ_[p]) ∉
          Function.support (fieldOnePadicBruhatFourier p
            (fieldOnePadicPrimitiveAngularPacket p n χ)) :=
      fun hs => hout (hzero hs)
    have hzeroVal :
        fieldOnePadicBruhatFourier p
          (fieldOnePadicPrimitiveAngularPacket p n χ)
          ((p : ℚ_[p]) ^ k * ((u : ℤ_[p]) : ℚ_[p])) = 0 :=
      not_ne_iff.mp hnotSupport
    rw [hzeroVal, if_neg hklt.ne]

/-- For `0 < n`, the Fourier transform of the radial packet of height `m` at `p^k u` equals
`p^{-m} · p^{-n} χ⁻¹(-ū) g(χ)` when `k = -m - n`, and vanishes on every other shell. -/
theorem fieldOnePadicPrimitiveRadialPacket_fourier_coordinates
    (n : ℕ) (hn : 0 < n)
    (χ : FieldOnePadicPrimitiveAngularCharacter p n)
    (m k : ℤ) (u : ℤ_[p]ˣ) :
    fieldOnePadicBruhatFourier p
        (fieldOnePadicPrimitiveRadialPacket p n χ m)
        (((fieldOnePadicValuationUnitContinuousMulEquiv p)
          (Multiplicative.ofAdd k, u) : ℚ_[p]ˣ) : ℚ_[p]) =
      if k = -m - n then
        ((p : ℝ≥0) ^ (-m)) •
          ((((p ^ n : ℕ) : ℂ)⁻¹ *
            χ.1⁻¹ (-(fieldOnePadicUnitReduction p n u :
              (ZMod (p ^ n))ˣ))) *
            gaussSum χ.1 ZMod.stdAddChar)
      else 0 := by
  rw [fieldOnePadicPrimitiveRadialPacket,
    fieldOnePadicBruhatFourier_primeZPowDilation]
  have harg :
      (((fieldOnePadicPrimeUnit p) ^ m : ℚ_[p]ˣ) *
        ((fieldOnePadicValuationUnitContinuousMulEquiv p)
          (Multiplicative.ofAdd k, u) : ℚ_[p]ˣ)) =
      (fieldOnePadicValuationUnitContinuousMulEquiv p)
        (Multiplicative.ofAdd (m + k), u) := by
    apply Units.ext
    have hkcoord :
        (((fieldOnePadicValuationUnitContinuousMulEquiv p)
          (Multiplicative.ofAdd k, u) : ℚ_[p]ˣ) : ℚ_[p]) =
          (p : ℚ_[p]) ^ k * ((u : ℤ_[p]) : ℚ_[p]) := rfl
    have hmkcoord :
        (((fieldOnePadicValuationUnitContinuousMulEquiv p)
          (Multiplicative.ofAdd (m + k), u) : ℚ_[p]ˣ) : ℚ_[p]) =
          (p : ℚ_[p]) ^ (m + k) * ((u : ℤ_[p]) : ℚ_[p]) := rfl
    rw [Units.val_mul, Units.val_zpow_eq_zpow_val, hkcoord, hmkcoord]
    change (p : ℚ_[p]) ^ m *
        ((p : ℚ_[p]) ^ k * ((u : ℤ_[p]) : ℚ_[p])) =
      (p : ℚ_[p]) ^ (m + k) * ((u : ℤ_[p]) : ℚ_[p])
    rw [zpow_add₀]
    · ring
    · exact_mod_cast (Fact.out : Nat.Prime p).ne_zero
  simp only [neg_neg]
  have hargval := congrArg Units.val harg
  simp only [Units.val_mul] at hargval
  rw [hargval,
    fieldOnePadicPrimitiveAngularPacket_fourier_coordinates p n hn χ]
  by_cases hk : k = -m - n
  · rw [if_pos hk, if_pos (by omega)]
  · have hmk : m + k ≠ -(n : ℤ) := by omega
    rw [if_neg hmk, if_neg hk, smul_zero]

end
end GaloisForLFunctions.RHTower

