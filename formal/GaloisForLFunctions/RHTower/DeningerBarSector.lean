import GaloisForLFunctions.RHTower.DeningerBarContraction
import GaloisForLFunctions.RHTower.DeningerPrimeLogHeightGreen

/-!
# Character sectors and the total prime-log calculus on the bar source

A coefficient multiplier that depends only on the total arithmetic character of a word commutes
with every bar face and with the extra degeneracy, because unit insertion and head removal both
preserve the total character.  Such a multiplier is continuous with the seminorm loss dictated by
its growth against the product of the letter heights.

The height of the total character never exceeds the product of the letter heights, so the total
prime-log generator, its Green inverse, the odd Hodge sign and the Hardy projectors are all
multipliers of that kind: the first two of growth one, the last three of growth zero.

Restricting to one character is a multiplier of growth zero, so every arithmetic-character sector
is a closed complemented subcomplex which the same extra degeneracy contracts.

* `deningerBarCharMul` : the character multiplier calculus.
* `deningerBarCharMul_diff`, `deningerBarCharMul_unit` : **commutation with `b` and `s`.**
* `deningerBarSectorProj` : the sector projection, with its own contraction.
* `deningerBarTotalGenerator`, `deningerBarTotalGreen`, `deningerBarTotalHodge`,
  `deningerBarHardyPlus`, `deningerBarHardyMinus` : the total prime-log calculus.
-/

namespace RHTower

open GaloisForLFunctions

noncomputable section

/-! ## Character multipliers -/

/-- Coefficientwise multiplication by a function of the total arithmetic character. -/
def deningerBarCharMulCoe (ψ : DeningerPrimeLattice → ℂ) (c : DeningerBarWord → ℂ) :
    DeningerBarWord → ℂ :=
  fun w => ψ (deningerBarChar w) * c w

theorem deningerBarCharMulCoe_apply (ψ : DeningerPrimeLattice → ℂ) (c : DeningerBarWord → ℂ)
    (w : DeningerBarWord) :
    deningerBarCharMulCoe ψ c w = ψ (deningerBarChar w) * c w := rfl

/-- The total character of a word with a unit inserted is the total character of the word. -/
theorem deningerBarChar_insert {r : ℕ} (t : Fin (r + 2))
    (f : Fin (r + 1) → DeningerPrimeLattice) :
    deningerBarChar (deningerInsertUnitWord t f)
      = deningerBarChar (⟨r, f⟩ : DeningerBarWord) :=
  deningerInsertUnitWord_char t f

/-- Removing a leading unit letter preserves the total character. -/
theorem deningerBarChar_tail {r : ℕ} {f : Fin (r + 2) → DeningerPrimeLattice} (hf : f 0 = 0) :
    deningerBarChar (⟨r + 1, f⟩ : DeningerBarWord)
      = deningerBarChar (⟨r, Fin.tail f⟩ : DeningerBarWord) := by
  show (∑ i, f i) = ∑ j, Fin.tail f j
  rw [Fin.sum_univ_succ, hf, zero_add]
  rfl

/-- **A character multiplier commutes with the bar differential.** -/
theorem deningerBarCharMul_diff (ψ : DeningerPrimeLattice → ℂ) (c : DeningerBarWord → ℂ) :
    deningerBarDiffCoe (deningerBarCharMulCoe ψ c)
      = deningerBarCharMulCoe ψ (deningerBarDiffCoe c) := by
  funext w
  obtain ⟨s, f⟩ := w
  have hfibre : ∀ j : Fin (s + 1),
      deningerBarFibreSum (deningerBarCharMulCoe ψ c) f j
        = ψ (deningerBarChar (⟨s, f⟩ : DeningerBarWord)) *
            deningerBarFibreSum c f j := by
    intro j
    have hcast := deningerBarChar_insert (j.castSucc) f
    have hsucc := deningerBarChar_insert (j.succ) f
    rw [deningerBarFibreSum, deningerBarFibreSum]
    by_cases h : f j = 0
    · rw [if_pos h, if_pos h, deningerBarCharMulCoe_apply, hcast]
    · rw [if_neg h, if_neg h, deningerBarCharMulCoe_apply, deningerBarCharMulCoe_apply,
        hcast, hsucc]
      ring
  show (∑ j : Fin (s + 1), (-1 : ℂ) ^ (j : ℕ) *
      deningerBarFibreSum (deningerBarCharMulCoe ψ c) f j) = _
  rw [deningerBarCharMulCoe_apply]
  show _ = ψ (deningerBarChar (⟨s, f⟩ : DeningerBarWord)) *
    ∑ j : Fin (s + 1), (-1 : ℂ) ^ (j : ℕ) * deningerBarFibreSum c f j
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hfibre j]
  ring

/-- **A character multiplier commutes with the extra degeneracy.** -/
theorem deningerBarCharMul_unit (ψ : DeningerPrimeLattice → ℂ) (c : DeningerBarWord → ℂ) :
    deningerBarUnitCoe (deningerBarCharMulCoe ψ c)
      = deningerBarCharMulCoe ψ (deningerBarUnitCoe c) := by
  funext w
  obtain ⟨r, f⟩ := w
  cases r with
  | zero =>
      rw [deningerBarUnitCoe_one, deningerBarCharMulCoe_apply, deningerBarUnitCoe_one,
        mul_zero]
  | succ r =>
      simp only [deningerBarCharMulCoe_apply, deningerBarUnitCoe_succ]
      by_cases h : f 0 = 0
      · rw [if_pos h, if_pos h, deningerBarChar_tail h]
      · rw [if_neg h, if_neg h, mul_zero]

/-! ## Continuity -/

private theorem deningerBarCharMul_weight_le {ψ : DeningerPrimeLattice → ℂ} {j : ℕ}
    (hψ : ∀ w : DeningerBarWord, ‖ψ (deningerBarChar w)‖ ≤ deningerBarHeight w ^ j)
    (k : ℕ) (w : DeningerBarWord) :
    deningerBarKotheData.w k w * ‖ψ (deningerBarChar w)‖
      ≤ deningerBarKotheData.w (k + j) w := by
  have hHnn : (0 : ℝ) ≤ deningerBarHeight w ^ k :=
    pow_nonneg (deningerBarHeight_pos w).le _
  have hLnn : (0 : ℝ) ≤ ((k : ℝ) + 1) ^ deningerBarLength w :=
    pow_nonneg (by positivity) _
  have hkj : ((k : ℝ) + 1) ^ deningerBarLength w
      ≤ (((k + j : ℕ) : ℝ) + 1) ^ deningerBarLength w := by
    refine pow_le_pow_left₀ (by positivity) ?_ _
    have hle : (k : ℝ) ≤ ((k + j : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_right k j
    linarith
  rw [deningerBarKotheData_w, deningerBarKotheData_w]
  calc deningerBarHeight w ^ k * ((k : ℝ) + 1) ^ deningerBarLength w *
        ‖ψ (deningerBarChar w)‖
      ≤ deningerBarHeight w ^ k * ((k : ℝ) + 1) ^ deningerBarLength w *
          deningerBarHeight w ^ j :=
        mul_le_mul_of_nonneg_left (hψ w) (mul_nonneg hHnn hLnn)
    _ = deningerBarHeight w ^ (k + j) * ((k : ℝ) + 1) ^ deningerBarLength w := by
        rw [pow_add]; ring
    _ ≤ deningerBarHeight w ^ (k + j) * (((k + j : ℕ) : ℝ) + 1) ^ deningerBarLength w :=
        mul_le_mul_of_nonneg_left hkj (pow_nonneg (deningerBarHeight_pos w).le _)

private theorem deningerBarCharMul_mem {ψ : DeningerPrimeLattice → ℂ} {j : ℕ}
    (hψ : ∀ w : DeningerBarWord, ‖ψ (deningerBarChar w)‖ ≤ deningerBarHeight w ^ j)
    (c : DeningerBarKothe) :
    deningerBarCharMulCoe ψ (c : DeningerBarWord → ℂ) ∈ DeningerBarKothe := by
  intro k
  refine Summable.of_nonneg_of_le
    (fun w => mul_nonneg (deningerBarKotheData.pos k w).le (norm_nonneg _))
    (fun w => ?_) (c.2 (k + j))
  rw [deningerBarCharMulCoe_apply, norm_mul, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right (deningerBarCharMul_weight_le hψ k w) (norm_nonneg _)

/-- **The character multiplier calculus** on the bar source. -/
def deningerBarCharMul (ψ : DeningerPrimeLattice → ℂ) (j : ℕ)
    (hψ : ∀ w : DeningerBarWord, ‖ψ (deningerBarChar w)‖ ≤ deningerBarHeight w ^ j) :
    DeningerBarKothe →ₗ[ℂ] DeningerBarKothe where
  toFun c := ⟨deningerBarCharMulCoe ψ (c : DeningerBarWord → ℂ),
    deningerBarCharMul_mem hψ c⟩
  map_add' a b := by
    ext w
    show deningerBarCharMulCoe ψ ((a + b : DeningerBarKothe) : DeningerBarWord → ℂ) w
        = ((⟨deningerBarCharMulCoe ψ (a : DeningerBarWord → ℂ),
              deningerBarCharMul_mem hψ a⟩ +
            ⟨deningerBarCharMulCoe ψ (b : DeningerBarWord → ℂ),
              deningerBarCharMul_mem hψ b⟩ : DeningerBarKothe) : DeningerBarWord → ℂ) w
    simp only [Submodule.coe_add, Pi.add_apply, deningerBarCharMulCoe_apply]
    ring
  map_smul' t a := by
    ext w
    show deningerBarCharMulCoe ψ ((t • a : DeningerBarKothe) : DeningerBarWord → ℂ) w
        = ((t • (⟨deningerBarCharMulCoe ψ (a : DeningerBarWord → ℂ),
            deningerBarCharMul_mem hψ a⟩ : DeningerBarKothe)) : DeningerBarWord → ℂ) w
    simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, deningerBarCharMulCoe_apply]
    ring

@[simp]
theorem deningerBarCharMul_coe {ψ : DeningerPrimeLattice → ℂ} {j : ℕ}
    (hψ : ∀ w : DeningerBarWord, ‖ψ (deningerBarChar w)‖ ≤ deningerBarHeight w ^ j)
    (c : DeningerBarKothe) (w : DeningerBarWord) :
    ((deningerBarCharMul ψ j hψ c : DeningerBarKothe) : DeningerBarWord → ℂ) w
      = ψ (deningerBarChar w) * (c : DeningerBarWord → ℂ) w := rfl

/-- **A character multiplier of growth `j` costs `j` height steps.** -/
theorem deningerBarSeminorm_charMul_le {ψ : DeningerPrimeLattice → ℂ} {j : ℕ}
    (hψ : ∀ w : DeningerBarWord, ‖ψ (deningerBarChar w)‖ ≤ deningerBarHeight w ^ j)
    (k : ℕ) (c : DeningerBarKothe) :
    deningerBarSeminorm k (deningerBarCharMul ψ j hψ c)
      ≤ deningerBarSeminorm (k + j) c := by
  rw [deningerBarSeminorm_apply, deningerBarSeminorm_apply]
  refine Summable.tsum_le_tsum (fun w => ?_)
    ((deningerBarCharMul ψ j hψ c).2 k) (c.2 (k + j))
  rw [deningerBarCharMul_coe, norm_mul, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right (deningerBarCharMul_weight_le hψ k w) (norm_nonneg _)

/-! ## The multipliers -/

private theorem deningerBarChar_height_le (w : DeningerBarWord) :
    deningerHeight (deningerBarChar w) ≤ deningerBarHeight w :=
  deningerHeight_barChar_le w

theorem deningerBarTotalGenerator_bound (w : DeningerBarWord) :
    ‖((deningerFreq (deningerBarChar w) : ℝ) : ℂ)‖ ≤ deningerBarHeight w ^ 1 := by
  rw [Complex.norm_real, Real.norm_eq_abs, pow_one]
  exact le_trans (abs_deningerFreq_le_height _) (deningerBarChar_height_le w)

theorem deningerBarTotalGreen_bound (w : DeningerBarWord) :
    ‖(((|deningerFreq (deningerBarChar w)|)⁻¹ : ℝ) : ℂ)‖ ≤ deningerBarHeight w ^ 1 := by
  have h := deningerModulusGreen_multiplier_bound (deningerBarChar w)
  rw [Complex.norm_real, Real.norm_eq_abs, pow_one] at h ⊢
  exact le_trans h (deningerBarChar_height_le w)

theorem deningerBarTotalHodge_bound (w : DeningerBarWord) :
    ‖Complex.I * ((deningerSign (deningerBarChar w) : ℝ) : ℂ)‖
      ≤ deningerBarHeight w ^ 0 := by
  rw [pow_zero, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
  exact abs_deningerSign_le_one _

theorem deningerBarHardyPlus_bound (w : DeningerBarWord) :
    ‖(if 0 < deningerFreq (deningerBarChar w) then (1 : ℂ) else 0)‖
      ≤ deningerBarHeight w ^ 0 := by
  rw [pow_zero]
  by_cases h : 0 < deningerFreq (deningerBarChar w) <;> simp [h]

theorem deningerBarHardyMinus_bound (w : DeningerBarWord) :
    ‖(if deningerFreq (deningerBarChar w) < 0 then (1 : ℂ) else 0)‖
      ≤ deningerBarHeight w ^ 0 := by
  rw [pow_zero]
  by_cases h : deningerFreq (deningerBarChar w) < 0 <;> simp [h]

theorem deningerBarSector_bound (γ : DeningerPrimeLattice) (w : DeningerBarWord) :
    ‖(if deningerBarChar w = γ then (1 : ℂ) else 0)‖ ≤ deningerBarHeight w ^ 0 := by
  rw [pow_zero]
  by_cases h : deningerBarChar w = γ <;> simp [h]

/-- **The total prime-log generator** `(D_tot c)_w = ℓ(χ(w)) c_w`. -/
def deningerBarTotalGenerator : DeningerBarKothe →ₗ[ℂ] DeningerBarKothe :=
  deningerBarCharMul (fun m => ((deningerFreq m : ℝ) : ℂ)) 1 deningerBarTotalGenerator_bound

/-- **The total Green inverse** `(G_tot c)_w = |ℓ(χ(w))|⁻¹ c_w`. -/
def deningerBarTotalGreen : DeningerBarKothe →ₗ[ℂ] DeningerBarKothe :=
  deningerBarCharMul (fun m => (((|deningerFreq m|)⁻¹ : ℝ) : ℂ)) 1 deningerBarTotalGreen_bound

/-- **The total odd Hodge sign** `(W_tot c)_w = i·sgn(ℓ(χ(w))) c_w`. -/
def deningerBarTotalHodge : DeningerBarKothe →ₗ[ℂ] DeningerBarKothe :=
  deningerBarCharMul (fun m => Complex.I * ((deningerSign m : ℝ) : ℂ)) 0
    deningerBarTotalHodge_bound

/-- **The total positive Hardy projector.** -/
def deningerBarHardyPlus : DeningerBarKothe →ₗ[ℂ] DeningerBarKothe :=
  deningerBarCharMul (fun m => if 0 < deningerFreq m then (1 : ℂ) else 0) 0
    deningerBarHardyPlus_bound

/-- **The total negative Hardy projector.** -/
def deningerBarHardyMinus : DeningerBarKothe →ₗ[ℂ] DeningerBarKothe :=
  deningerBarCharMul (fun m => if deningerFreq m < 0 then (1 : ℂ) else 0) 0
    deningerBarHardyMinus_bound

/-- **The arithmetic-character sector projection** `Q_γ`. -/
def deningerBarSectorProj (γ : DeningerPrimeLattice) : DeningerBarKothe →ₗ[ℂ] DeningerBarKothe :=
  deningerBarCharMul (fun m => if m = γ then (1 : ℂ) else 0) 0 (deningerBarSector_bound γ)

/-! ## The sector decomposition -/

theorem deningerBarSectorProj_idem (γ : DeningerPrimeLattice) (c : DeningerBarKothe) :
    deningerBarSectorProj γ (deningerBarSectorProj γ c) = deningerBarSectorProj γ c := by
  ext w
  simp only [deningerBarSectorProj, deningerBarCharMul_coe]
  by_cases h : deningerBarChar w = γ <;> simp [h]

/-- **Every character sector is a subcomplex**: the sector projection commutes with the bar
differential. -/
theorem deningerBarSectorProj_diff (γ : DeningerPrimeLattice) (c : DeningerBarKothe) :
    deningerBarDiff (deningerBarSectorProj γ c)
      = deningerBarSectorProj γ (deningerBarDiff c) := by
  ext w
  show deningerBarDiffCoe
      ((deningerBarSectorProj γ c : DeningerBarKothe) : DeningerBarWord → ℂ) w = _
  have h := deningerBarCharMul_diff (fun m => if m = γ then (1 : ℂ) else 0)
    (c : DeningerBarWord → ℂ)
  exact congrFun h w

/-- **The extra degeneracy restricts to every character sector.** -/
theorem deningerBarSectorProj_unit (γ : DeningerPrimeLattice) (c : DeningerBarKothe) :
    deningerBarUnit (deningerBarSectorProj γ c)
      = deningerBarSectorProj γ (deningerBarUnit c) := by
  ext w
  show deningerBarUnitCoe
      ((deningerBarSectorProj γ c : DeningerBarKothe) : DeningerBarWord → ℂ) w = _
  have h := deningerBarCharMul_unit (fun m => if m = γ then (1 : ℂ) else 0)
    (c : DeningerBarWord → ℂ)
  exact congrFun h w

/-- **Every character sector, including the balanced sector of total character zero, is split
strictly exact.** -/
theorem deningerBarSector_exact (γ : DeningerPrimeLattice) (c : DeningerBarKothe)
    (hc : deningerBarDiff (deningerBarSectorProj γ c) = 0) :
    deningerBarDiff (deningerBarUnit (deningerBarSectorProj γ c))
      = deningerBarSectorProj γ c :=
  deningerBar_exact (deningerBarSectorProj γ c) hc

/-! ## The total prime-log operators are chain operators -/

theorem deningerBarTotalGenerator_diff (c : DeningerBarKothe) :
    deningerBarDiff (deningerBarTotalGenerator c)
      = deningerBarTotalGenerator (deningerBarDiff c) := by
  ext w
  exact congrFun (deningerBarCharMul_diff (fun m => ((deningerFreq m : ℝ) : ℂ))
    (c : DeningerBarWord → ℂ)) w

theorem deningerBarTotalGreen_diff (c : DeningerBarKothe) :
    deningerBarDiff (deningerBarTotalGreen c)
      = deningerBarTotalGreen (deningerBarDiff c) := by
  ext w
  exact congrFun (deningerBarCharMul_diff (fun m => (((|deningerFreq m|)⁻¹ : ℝ) : ℂ))
    (c : DeningerBarWord → ℂ)) w

theorem deningerBarTotalHodge_diff (c : DeningerBarKothe) :
    deningerBarDiff (deningerBarTotalHodge c)
      = deningerBarTotalHodge (deningerBarDiff c) := by
  ext w
  exact congrFun (deningerBarCharMul_diff
    (fun m => Complex.I * ((deningerSign m : ℝ) : ℂ)) (c : DeningerBarWord → ℂ)) w

theorem deningerBarHardyPlus_diff (c : DeningerBarKothe) :
    deningerBarDiff (deningerBarHardyPlus c)
      = deningerBarHardyPlus (deningerBarDiff c) := by
  ext w
  exact congrFun (deningerBarCharMul_diff
    (fun m => if 0 < deningerFreq m then (1 : ℂ) else 0) (c : DeningerBarWord → ℂ)) w

theorem deningerBarHardyMinus_diff (c : DeningerBarKothe) :
    deningerBarDiff (deningerBarHardyMinus c)
      = deningerBarHardyMinus (deningerBarDiff c) := by
  ext w
  exact congrFun (deningerBarCharMul_diff
    (fun m => if deningerFreq m < 0 then (1 : ℂ) else 0) (c : DeningerBarWord → ℂ)) w

/-- The total generator and its Green inverse lose at most one height seminorm. -/
theorem deningerBarSeminorm_totalGenerator_le (k : ℕ) (c : DeningerBarKothe) :
    deningerBarSeminorm k (deningerBarTotalGenerator c)
      ≤ deningerBarSeminorm (k + 1) c :=
  deningerBarSeminorm_charMul_le (ψ := fun m => ((deningerFreq m : ℝ) : ℂ)) (j := 1)
    deningerBarTotalGenerator_bound k c

theorem deningerBarSeminorm_totalGreen_le (k : ℕ) (c : DeningerBarKothe) :
    deningerBarSeminorm k (deningerBarTotalGreen c) ≤ deningerBarSeminorm (k + 1) c :=
  deningerBarSeminorm_charMul_le (ψ := fun m => (((|deningerFreq m|)⁻¹ : ℝ) : ℂ)) (j := 1)
    deningerBarTotalGreen_bound k c

/-- The Hodge sign, the Hardy projectors and the sector projections decrease every seminorm. -/
theorem deningerBarSeminorm_totalHodge_le (k : ℕ) (c : DeningerBarKothe) :
    deningerBarSeminorm k (deningerBarTotalHodge c) ≤ deningerBarSeminorm k c := by
  have h := deningerBarSeminorm_charMul_le
    (ψ := fun m => Complex.I * ((deningerSign m : ℝ) : ℂ)) (j := 0)
    deningerBarTotalHodge_bound k c
  rwa [Nat.add_zero] at h

theorem deningerBarSeminorm_hardyPlus_le (k : ℕ) (c : DeningerBarKothe) :
    deningerBarSeminorm k (deningerBarHardyPlus c) ≤ deningerBarSeminorm k c := by
  have h := deningerBarSeminorm_charMul_le
    (ψ := fun m => if 0 < deningerFreq m then (1 : ℂ) else 0) (j := 0)
    deningerBarHardyPlus_bound k c
  rwa [Nat.add_zero] at h

theorem deningerBarSeminorm_hardyMinus_le (k : ℕ) (c : DeningerBarKothe) :
    deningerBarSeminorm k (deningerBarHardyMinus c) ≤ deningerBarSeminorm k c := by
  have h := deningerBarSeminorm_charMul_le
    (ψ := fun m => if deningerFreq m < 0 then (1 : ℂ) else 0) (j := 0)
    deningerBarHardyMinus_bound k c
  rwa [Nat.add_zero] at h

theorem deningerBarSeminorm_sectorProj_le (γ : DeningerPrimeLattice) (k : ℕ)
    (c : DeningerBarKothe) :
    deningerBarSeminorm k (deningerBarSectorProj γ c) ≤ deningerBarSeminorm k c := by
  have h := deningerBarSeminorm_charMul_le
    (ψ := fun m => if m = γ then (1 : ℂ) else 0) (j := 0)
    (deningerBarSector_bound γ) k c
  rwa [Nat.add_zero] at h

end

end RHTower
