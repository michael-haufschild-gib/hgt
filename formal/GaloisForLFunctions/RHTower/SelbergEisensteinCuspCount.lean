import GaloisForLFunctions.RHTower.SelbergEisensteinCuspConstant
import GaloisForLFunctions.RHTower.CoprimeClassCount

open scoped MatrixGroups

/-!
# The row count `count_σ(c)` at the cusp `σ∞`

The rows of `Γ(N)σ` are exactly the primitive rows `≡ (σ₁₀, σ₁₁) (mod N)` (`mem_image_congr`: `rowMul σ⁻¹` carries them
to `≡ (0, 1)` using `det σ = 1`). For `c ≢ σ₁₀` there are none; for `c ≡ σ₁₀`, a prime dividing `c`, `N` and `σ₁₁`
would divide `det σ`, so the coprime-class count applies: `count_σ(c) φ(N) = [c ≡ σ₁₀ (N)] φ(|c|N)`
(`countσ_mul_totient`).
-/

namespace GaloisForLFunctions.RHTower.SelbergEisensteinCuspCount
open GaloisForLFunctions.RHTower.SelbergEisensteinCusp GaloisForLFunctions.RHTower.SelbergEisensteinCuspRows
  GaloisForLFunctions.RHTower.SelbergPoincareFourier GaloisForLFunctions.RHTower.SelbergEisensteinCuspSlice
  GaloisForLFunctions.RHTower.CoprimeClassCount

variable (N : ℕ) (σ : SL(2, ℤ))

theorem det_eq : σ 0 0 * σ 1 1 - σ 0 1 * σ 1 0 = 1 := by
  have h := σ.2; rw [Matrix.det_fin_two] at h; exact h

/-- **The rows at `σ∞`** are the primitive rows `≡ (σ₁₀, σ₁₁) (mod N)`. -/
theorem mem_image_congr (p : ℤ × ℤ) :
    p ∈ rowMul σ '' adm N ↔
      ((p.1 : ZMod N) = σ 1 0 ∧ (p.2 : ZMod N) = σ 1 1 ∧ IsCoprime p.1 p.2) := by
  constructor
  · rintro ⟨q, ⟨hq1, hq2, hq3⟩, rfl⟩
    have h0 : (q.1 : ZMod N) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hq1
    refine ⟨?_, ?_, isCoprime_rowMul σ hq3⟩
    · simp only [rowMul]; push_cast; rw [h0, hq2]; ring
    · simp only [rowMul]; push_cast; rw [h0, hq2]; ring
  · rintro ⟨h1, h2, h3⟩
    rw [mem_image_iff]
    have hd : ((σ 0 0 * σ 1 1 - σ 0 1 * σ 1 0 : ℤ) : ZMod N) = 1 := by rw [det_eq]; simp
    push_cast at hd
    refine ⟨?_, ?_, isCoprime_rowMul σ⁻¹ h3⟩
    · rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      simp only [rowMul, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
      simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.empty_val', Matrix.cons_val_fin_one]
      push_cast; rw [h1, h2]; ring
    · simp only [rowMul, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
      simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.empty_val', Matrix.cons_val_fin_one]
      push_cast; rw [h1, h2, ← hd]; ring

variable [NeZero N]

/-- **The count at `σ∞`**: `count_σ(c) φ(N) = [c ≡ σ₁₀ (N)] φ(|c|N)`. -/
theorem countσ_mul_totient {c : ℤ} (hc : c ≠ 0) :
    countσ N σ c * N.totient = if (c : ZMod N) = σ 1 0 then (c.natAbs * N).totient else 0 := by
  classical
  unfold countσ
  split_ifs with hcl
  · set b := ((σ 1 1 : ℤ) : ZMod N).val
    have hbσ : ((b : ℕ) : ZMod N) = ((σ 1 1 : ℤ) : ZMod N) := ZMod.natCast_zmod_val _
    have hfilt : (Finset.range (c.natAbs * N)).filter (fun r : ℕ => (c, (r : ℤ)) ∈ rowMul σ '' adm N) =
        (Finset.range (c.natAbs * N)).filter (fun r => r ≡ b [MOD N] ∧ c.natAbs.Coprime r) := by
      apply Finset.filter_congr
      intro r _
      rw [mem_image_congr, Int.isCoprime_iff_nat_coprime, ← ZMod.natCast_eq_natCast_iff, hbσ]
      simp [hcl]
    rw [hfilt]
    refine card_coprime_class_mul_totient (Int.natAbs_pos.mpr hc) (Nat.pos_of_ne_zero (NeZero.ne N)) ?_
    refine Nat.coprime_of_dvd (fun p hp hpg hpb => ?_)
    have hpc : (p : ℤ) ∣ c := Int.natCast_dvd.mpr (hpg.trans (Nat.gcd_dvd_left _ _))
    have hpN : (p : ℤ) ∣ N := Int.natCast_dvd_natCast.mpr (hpg.trans (Nat.gcd_dvd_right _ _))
    have h10 : (p : ℤ) ∣ σ 1 0 := by
      have := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ N).mp hcl
      have h := dvd_add (hpN.trans this) hpc
      simpa using h
    have h11 : (p : ℤ) ∣ σ 1 1 := by
      have := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ N).mp (by rw [← hbσ]; push_cast; rfl :
        (((b : ℕ) : ℤ) : ZMod N) = ((σ 1 1 : ℤ) : ZMod N))
      have h := dvd_add (Int.natCast_dvd_natCast.mpr hpb) (hpN.trans this)
      simpa using h
    have h1 : (p : ℤ) ∣ 1 := by
      rw [← det_eq σ]
      exact dvd_sub (dvd_mul_of_dvd_right h11 _) (dvd_mul_of_dvd_right h10 _)
    exact hp.one_lt.ne' (by exact_mod_cast Int.eq_one_of_dvd_one (by positivity) h1)
  · rw [Finset.card_eq_zero.mpr, zero_mul]
    rw [Finset.filter_eq_empty_iff]
    intro r _ hm
    exact hcl ((mem_image_congr N σ _).mp hm).1

end GaloisForLFunctions.RHTower.SelbergEisensteinCuspCount
