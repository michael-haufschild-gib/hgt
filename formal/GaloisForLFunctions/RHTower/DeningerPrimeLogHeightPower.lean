import GaloisForLFunctions.RHTower.DeningerPrimeLogHeightGreen

/-!
# Power maps and reflection relations on the prime-log height source

For a positive integer `q` the power map `V_q` sends the basis vector at `m` to the basis vector
at `q·m`.  Because the height is homogeneous, `V_q` rescales the seminorm index:

`p_k(V_q a) = p_{qk}(a)`,

and because the frequency is homogeneous of degree one, `V_q` intertwines the generator and the
modulus with a factor `q`, while commuting with the Hodge sign and the Hardy projectors.
Reflection anticommutes with the generator and the Hodge sign, commutes with the modulus, and
exchanges the two Hardy projectors.

* `deningerPower` : the power map, with `deningerHeightSeminorm_power`.
* `deningerPower_generator`, `deningerPower_modulus`, `deningerPower_hodgeSign`,
  `deningerPower_hardyPlus` : the power relations.
* `deningerReflect_generator`, `deningerReflect_modulus`, `deningerReflect_hodgeSign`,
  `deningerReflect_hardy` : the reflection relations.
-/

namespace RHTower

open GaloisForLFunctions

noncomputable section

/-! ## Division of exponent vectors -/

/-- Coordinatewise division of an exponent vector by `q`. -/
def deningerDivExponent (q : ℕ) (n : DeningerPrimeLattice) : DeningerPrimeLattice :=
  n.mapRange (fun z => z / (q : ℤ)) (by simp)

@[simp]
theorem deningerDivExponent_apply (q : ℕ) (n : DeningerPrimeLattice) (p : Nat.Primes) :
    deningerDivExponent q n p = n p / (q : ℤ) := rfl

theorem deningerDivExponent_nsmul {q : ℕ} (hq : 0 < q) (m : DeningerPrimeLattice) :
    deningerDivExponent q (q • m) = m := by
  ext p
  show (q • m) p / (q : ℤ) = m p
  rw [Finsupp.smul_apply, nsmul_eq_mul]
  exact Int.mul_ediv_cancel_left _ (by exact_mod_cast hq.ne')

theorem deningerNsmul_injective {q : ℕ} (hq : 0 < q) :
    Function.Injective (fun m : DeningerPrimeLattice => q • m) := by
  intro m n h
  have hd := congrArg (deningerDivExponent q) h
  rwa [deningerDivExponent_nsmul hq, deningerDivExponent_nsmul hq] at hd

/-! ## The power map -/

/-- The coefficient sequence of the power map `V_q δ_m = δ_{qm}`. -/
def deningerPowerCoe (q : ℕ) (a : DeningerPrimeLattice → ℂ) : DeningerPrimeLattice → ℂ :=
  fun n => if q • deningerDivExponent q n = n then a (deningerDivExponent q n) else 0

theorem deningerPowerCoe_nsmul {q : ℕ} (hq : 0 < q) (a : DeningerPrimeLattice → ℂ)
    (m : DeningerPrimeLattice) : deningerPowerCoe q a (q • m) = a m := by
  rw [deningerPowerCoe]
  rw [deningerDivExponent_nsmul hq]
  rw [if_pos rfl]

theorem deningerPowerCoe_eq_zero_of_notMem {q : ℕ} (a : DeningerPrimeLattice → ℂ)
    {n : DeningerPrimeLattice} (hn : n ∉ Set.range fun m : DeningerPrimeLattice => q • m) :
    deningerPowerCoe q a n = 0 := by
  rw [deningerPowerCoe, if_neg]
  intro hcond
  exact hn ⟨deningerDivExponent q n, hcond⟩

private theorem deningerPower_mem {q : ℕ} (hq : 0 < q) (a : DeningerHeightKothe) :
    deningerPowerCoe q (a : DeningerPrimeLattice → ℂ) ∈ DeningerHeightKothe := by
  intro k
  refine (Function.Injective.summable_iff (f := fun n : DeningerPrimeLattice =>
      deningerHeightKotheData.w k n * ‖deningerPowerCoe q (a : DeningerPrimeLattice → ℂ) n‖)
    (deningerNsmul_injective hq) ?_).mp ?_
  · intro n hn
    rw [deningerPowerCoe_eq_zero_of_notMem _ hn, norm_zero, mul_zero]
  · refine (a.2 (q * k)).congr fun m => ?_
    show deningerHeightKotheData.w (q * k) m * ‖(a : DeningerPrimeLattice → ℂ) m‖
        = deningerHeightKotheData.w k (q • m) *
          ‖deningerPowerCoe q (a : DeningerPrimeLattice → ℂ) (q • m)‖
    rw [deningerPowerCoe_nsmul hq, deningerHeightKotheData_w, deningerHeightKotheData_w,
      deningerHeight_nsmul, ← pow_mul]

/-- **The power map** `V_q` on the prime-log height source. -/
def deningerPower (q : ℕ) (hq : 0 < q) :
    DeningerHeightKothe →ₗ[ℂ] DeningerHeightKothe where
  toFun a := ⟨deningerPowerCoe q (a : DeningerPrimeLattice → ℂ), deningerPower_mem hq a⟩
  map_add' a b := by
    ext n
    show deningerPowerCoe q ((a + b : DeningerHeightKothe) : DeningerPrimeLattice → ℂ) n
        = ((⟨deningerPowerCoe q (a : DeningerPrimeLattice → ℂ), deningerPower_mem hq a⟩ +
            ⟨deningerPowerCoe q (b : DeningerPrimeLattice → ℂ), deningerPower_mem hq b⟩ :
              DeningerHeightKothe) : DeningerPrimeLattice → ℂ) n
    simp only [Submodule.coe_add, Pi.add_apply, deningerPowerCoe]
    by_cases hn : q • deningerDivExponent q n = n
    · simp [hn]
    · simp [hn]
  map_smul' c a := by
    ext n
    show deningerPowerCoe q ((c • a : DeningerHeightKothe) : DeningerPrimeLattice → ℂ) n
        = ((c • (⟨deningerPowerCoe q (a : DeningerPrimeLattice → ℂ),
            deningerPower_mem hq a⟩ : DeningerHeightKothe)) : DeningerPrimeLattice → ℂ) n
    simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, deningerPowerCoe]
    by_cases hn : q • deningerDivExponent q n = n
    · simp [hn]
    · simp [hn]

@[simp]
theorem deningerPower_coe {q : ℕ} (hq : 0 < q) (a : DeningerHeightKothe)
    (n : DeningerPrimeLattice) :
    ((deningerPower q hq a : DeningerHeightKothe) : DeningerPrimeLattice → ℂ) n
      = deningerPowerCoe q (a : DeningerPrimeLattice → ℂ) n := rfl

/-- **The power map rescales the seminorm index**: `p_k(V_q a) = p_{qk}(a)`. -/
theorem deningerHeightSeminorm_power {q : ℕ} (hq : 0 < q) (k : ℕ)
    (a : DeningerHeightKothe) :
    deningerHeightSeminorm k (deningerPower q hq a)
      = deningerHeightSeminorm (q * k) a := by
  rw [deningerHeightSeminorm_apply, deningerHeightSeminorm_apply]
  rw [← Function.Injective.tsum_eq (deningerNsmul_injective hq)
    (f := fun n : DeningerPrimeLattice =>
      deningerHeight n ^ k *
        ‖((deningerPower q hq a : DeningerHeightKothe) : DeningerPrimeLattice → ℂ) n‖) ?_]
  · refine tsum_congr fun m => ?_
    show deningerHeight (q • m) ^ k *
        ‖deningerPowerCoe q (a : DeningerPrimeLattice → ℂ) (q • m)‖
        = deningerHeight m ^ (q * k) * ‖(a : DeningerPrimeLattice → ℂ) m‖
    rw [deningerPowerCoe_nsmul hq, deningerHeight_nsmul, ← pow_mul]
  · intro n hn
    rw [Function.mem_support] at hn
    by_contra hrange
    apply hn
    have hzero : ((deningerPower q hq a : DeningerHeightKothe) : DeningerPrimeLattice → ℂ) n = 0 := by
      rw [deningerPower_coe]
      exact deningerPowerCoe_eq_zero_of_notMem _ hrange
    rw [hzero, norm_zero, mul_zero]

/-! ## Power relations -/

theorem deningerPower_generator {q : ℕ} (hq : 0 < q) (a : DeningerHeightKothe) :
    deningerGenerator (deningerPower q hq a)
      = (q : ℂ) • deningerPower q hq (deningerGenerator a) := by
  ext n
  rw [deningerGenerator_coe, deningerPower_coe]
  show ((deningerFreq n : ℝ) : ℂ) * deningerPowerCoe q (a : DeningerPrimeLattice → ℂ) n
      = (((q : ℂ) • (deningerPower q hq (deningerGenerator a)) :
          DeningerHeightKothe) : DeningerPrimeLattice → ℂ) n
  rw [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, deningerPower_coe]
  simp only [deningerPowerCoe]
  by_cases hn : q • deningerDivExponent q n = n
  · have hfreq : deningerFreq n = q * deningerFreq (deningerDivExponent q n) := by
      conv_lhs => rw [← hn]
      rw [deningerFreq_nsmul]
    rw [if_pos hn, if_pos hn, hfreq, deningerGenerator_coe]
    push_cast
    ring
  · rw [if_neg hn, if_neg hn]
    ring

theorem deningerPower_modulus {q : ℕ} (hq : 0 < q) (a : DeningerHeightKothe) :
    deningerModulus (deningerPower q hq a)
      = (q : ℂ) • deningerPower q hq (deningerModulus a) := by
  ext n
  rw [deningerModulus_coe, deningerPower_coe]
  show ((|deningerFreq n| : ℝ) : ℂ) * deningerPowerCoe q (a : DeningerPrimeLattice → ℂ) n
      = (((q : ℂ) • (deningerPower q hq (deningerModulus a)) :
          DeningerHeightKothe) : DeningerPrimeLattice → ℂ) n
  rw [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, deningerPower_coe]
  simp only [deningerPowerCoe]
  by_cases hn : q • deningerDivExponent q n = n
  · have hfreq : deningerFreq n = q * deningerFreq (deningerDivExponent q n) := by
      conv_lhs => rw [← hn]
      rw [deningerFreq_nsmul]
    have habs : |deningerFreq n| = q * |deningerFreq (deningerDivExponent q n)| := by
      rw [hfreq, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (q : ℝ))]
    rw [if_pos hn, if_pos hn, habs, deningerModulus_coe]
    push_cast
    ring
  · rw [if_neg hn, if_neg hn]
    ring

theorem deningerSign_nsmul {q : ℕ} (hq : 0 < q) (m : DeningerPrimeLattice) :
    deningerSign (q • m) = deningerSign m := by
  have hfreq : deningerFreq (q • m) = q * deningerFreq m := deningerFreq_nsmul q m
  have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  rcases lt_trichotomy (deningerFreq m) 0 with h | h | h
  · have hneg : deningerFreq (q • m) < 0 := by rw [hfreq]; exact mul_neg_of_pos_of_neg hqpos h
    rw [deningerSign_of_neg hneg, deningerSign_of_neg h]
  · have hz : deningerFreq (q • m) = 0 := by rw [hfreq, h, mul_zero]
    rw [deningerSign_of_zero hz, deningerSign_of_zero h]
  · have hpos : 0 < deningerFreq (q • m) := by rw [hfreq]; exact mul_pos hqpos h
    rw [deningerSign_of_pos hpos, deningerSign_of_pos h]

theorem deningerPower_hodgeSign {q : ℕ} (hq : 0 < q) (a : DeningerHeightKothe) :
    deningerHodgeSign (deningerPower q hq a)
      = deningerPower q hq (deningerHodgeSign a) := by
  ext n
  rw [deningerHodgeSign_coe, deningerPower_coe, deningerPower_coe]
  simp only [deningerPowerCoe]
  by_cases hn : q • deningerDivExponent q n = n
  · have hsign : deningerSign n = deningerSign (deningerDivExponent q n) := by
      conv_lhs => rw [← hn]
      rw [deningerSign_nsmul hq]
    rw [if_pos hn, if_pos hn, hsign, deningerHodgeSign_coe]
  · rw [if_neg hn, if_neg hn]
    ring

theorem deningerPower_hardyPlus {q : ℕ} (hq : 0 < q) (a : DeningerHeightKothe) :
    deningerHeightHardyPlus (deningerPower q hq a)
      = deningerPower q hq (deningerHeightHardyPlus a) := by
  ext n
  rw [deningerHardyPlus_coe, deningerPower_coe, deningerPower_coe]
  simp only [deningerPowerCoe]
  by_cases hn : q • deningerDivExponent q n = n
  · have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
    have hfreq : deningerFreq n = q * deningerFreq (deningerDivExponent q n) := by
      conv_lhs => rw [← hn]
      rw [deningerFreq_nsmul]
    have hiff : (0 < deningerFreq n) ↔ (0 < deningerFreq (deningerDivExponent q n)) := by
      rw [hfreq]
      constructor
      · intro h
        by_contra hc
        have hc' : deningerFreq (deningerDivExponent q n) ≤ 0 := not_lt.mp hc
        nlinarith
      · intro h; exact mul_pos hqpos h
    rw [if_pos hn, if_pos hn, deningerHardyPlus_coe]
    by_cases hpos : 0 < deningerFreq n
    · rw [if_pos hpos, if_pos (hiff.mp hpos)]
    · rw [if_neg hpos, if_neg (fun hc => hpos (hiff.mpr hc))]
  · rw [if_neg hn, if_neg hn]
    ring

theorem deningerPower_hardyMinus {q : ℕ} (hq : 0 < q) (a : DeningerHeightKothe) :
    deningerHeightHardyMinus (deningerPower q hq a)
      = deningerPower q hq (deningerHeightHardyMinus a) := by
  ext n
  rw [deningerHardyMinus_coe, deningerPower_coe, deningerPower_coe]
  simp only [deningerPowerCoe]
  by_cases hn : q • deningerDivExponent q n = n
  · have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
    have hfreq : deningerFreq n = q * deningerFreq (deningerDivExponent q n) := by
      conv_lhs => rw [← hn]
      rw [deningerFreq_nsmul]
    have hiff : (deningerFreq n < 0) ↔ (deningerFreq (deningerDivExponent q n) < 0) := by
      rw [hfreq]
      constructor
      · intro h
        by_contra hc
        have hc' : 0 ≤ deningerFreq (deningerDivExponent q n) := not_lt.mp hc
        nlinarith
      · intro h; exact mul_neg_of_pos_of_neg hqpos h
    rw [if_pos hn, if_pos hn, deningerHardyMinus_coe]
    by_cases hneg : deningerFreq n < 0
    · rw [if_pos hneg, if_pos (hiff.mp hneg)]
    · rw [if_neg hneg, if_neg (fun hc => hneg (hiff.mpr hc))]
  · rw [if_neg hn, if_neg hn]
    ring

/-! ## Reflection relations -/

theorem deningerSign_neg (m : DeningerPrimeLattice) :
    deningerSign (-m) = -deningerSign m := by
  have hfreq : deningerFreq (-m) = -deningerFreq m := deningerFreq_neg m
  rcases lt_trichotomy (deningerFreq m) 0 with h | h | h
  · have hpos : 0 < deningerFreq (-m) := by rw [hfreq]; linarith
    rw [deningerSign_of_pos hpos, deningerSign_of_neg h]
    norm_num
  · have hz : deningerFreq (-m) = 0 := by rw [hfreq, h, neg_zero]
    rw [deningerSign_of_zero hz, deningerSign_of_zero h]
    norm_num
  · have hneg : deningerFreq (-m) < 0 := by rw [hfreq]; linarith
    rw [deningerSign_of_neg hneg, deningerSign_of_pos h]

theorem deningerReflect_generator (a : DeningerHeightKothe) :
    deningerGenerator (deningerHeightReflect a)
      = -deningerHeightReflect (deningerGenerator a) := by
  ext m
  rw [deningerGenerator_coe, deningerHeightReflect_coe]
  show ((deningerFreq m : ℝ) : ℂ) * (a : DeningerPrimeLattice → ℂ) (-m)
      = ((-deningerHeightReflect (deningerGenerator a) : DeningerHeightKothe) :
          DeningerPrimeLattice → ℂ) m
  rw [Submodule.coe_neg, Pi.neg_apply, deningerHeightReflect_coe, deningerGenerator_coe,
    deningerFreq_neg]
  push_cast
  ring

theorem deningerReflect_modulus (a : DeningerHeightKothe) :
    deningerModulus (deningerHeightReflect a)
      = deningerHeightReflect (deningerModulus a) := by
  ext m
  rw [deningerModulus_coe, deningerHeightReflect_coe, deningerHeightReflect_coe,
    deningerModulus_coe, deningerFreq_neg, abs_neg]

theorem deningerReflect_hodgeSign (a : DeningerHeightKothe) :
    deningerHodgeSign (deningerHeightReflect a)
      = -deningerHeightReflect (deningerHodgeSign a) := by
  ext m
  rw [deningerHodgeSign_coe, deningerHeightReflect_coe]
  show Complex.I * ((deningerSign m : ℝ) : ℂ) * (a : DeningerPrimeLattice → ℂ) (-m)
      = ((-deningerHeightReflect (deningerHodgeSign a) : DeningerHeightKothe) :
          DeningerPrimeLattice → ℂ) m
  rw [Submodule.coe_neg, Pi.neg_apply, deningerHeightReflect_coe, deningerHodgeSign_coe,
    deningerSign_neg]
  push_cast
  ring

theorem deningerReflect_hardy (a : DeningerHeightKothe) :
    deningerHeightReflect (deningerHeightHardyPlus a)
      = deningerHeightHardyMinus (deningerHeightReflect a) := by
  ext m
  rw [deningerHeightReflect_coe, deningerHardyPlus_coe, deningerHardyMinus_coe,
    deningerHeightReflect_coe]
  by_cases h : deningerFreq m < 0
  · have hpos : 0 < deningerFreq (-m) := by
      rw [deningerFreq_neg]; linarith
    rw [if_pos hpos, if_pos h]
  · have hnot : ¬ (0 : ℝ) < deningerFreq (-m) := by
      rw [deningerFreq_neg]
      intro hc
      exact h (by linarith)
    rw [if_neg hnot, if_neg h]

end

end RHTower
