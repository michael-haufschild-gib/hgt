import GaloisForLFunctions.RHTower.Sieve.TypeIIHybridBlockRoot
import GaloisForLFunctions.RHTower.Sieve.TypeIILongSupport

/-!
# Vaughan-scale form of the hybrid Type II block estimate

Both coefficient support edges are inserted.  A nonzero block has long scale at least `U/2` and
at most `B/V`; these are exactly the scale facts needed by the Babu--Sankaranarayanan estimate.
-/

namespace RHTower.Sieve

noncomputable section

def typeIIHybridVaughanRootEnvelope (T r : ℝ) (A B U V : ℕ) : ℝ :=
  Real.sqrt ((B : ℝ) ^ 2 / V)
    + Real.sqrt (2000 * Real.sqrt (T * r) * (B : ℝ) ^ 2 * Real.sqrt B /
        ((A : ℝ) * U))
    + Real.sqrt (20 * Real.pi * (B : ℝ) ^ 3 / (T * r) * invSum B)
    + Real.sqrt (2 * (B : ℝ) ^ 2 / U)

theorem typeIIHybridVaughanRootEnvelope_nonneg (T r : ℝ) (A B U V : ℕ) :
    0 ≤ typeIIHybridVaughanRootEnvelope T r A B U V := by
  rw [typeIIHybridVaughanRootEnvelope]
  positivity

theorem typeIIHybridBlockRootEnvelope_le_vaughan_of_ne_zero {T r : ℝ}
    (hT : 0 < T) (hr : 0 < r) {A B L U V P Q : ℕ}
    (hA : 1 ≤ A) (hU : 1 ≤ U) (hV : 1 ≤ V) (hP : 1 ≤ P) (hQ : 2 ≤ Q)
    (hQ2P : Q ≤ 2 * P)
    (hne : maskedBlockSum T r A B L P Q (fun d => typeIILong U d)
      (fun m => typeIIShort V m) ≠ 0) :
    typeIIHybridBlockRootEnvelope T r A B P ≤
      typeIIHybridVaughanRootEnvelope T r A B U V := by
  have hU2PNat : U ≤ 2 * P := by
    have hupper := upper_gt_truncation_of_maskedBlockSum_typeIILong_ne_zero hne
    omega
  have hPVNat : P * V ≤ B := by
    have hshort := mul_succ_le_pred_of_maskedBlockSum_ne_zero hP hQ hne
    exact le_trans (Nat.mul_le_mul_left P (Nat.le_succ V))
      (le_trans hshort (Nat.sub_le B 1))
  have hU0 : (0 : ℝ) < U := by exact_mod_cast hU
  have hV0 : (0 : ℝ) < V := by exact_mod_cast hV
  have hP0 : (0 : ℝ) < P := by exact_mod_cast hP
  have hA0 : (0 : ℝ) < A := by exact_mod_cast hA
  have hU2P : (U : ℝ) ≤ 2 * (P : ℝ) := by exact_mod_cast hU2PNat
  have hPV : (P : ℝ) * V ≤ B := by exact_mod_cast hPVNat
  have hPdivV : (P : ℝ) ≤ (B : ℝ) / V := by
    rw [le_div_iff₀ hV0]
    exact hPV
  let N : ℝ := 1000 * Real.sqrt (T * r) * (B : ℝ) ^ 2 * Real.sqrt B
  have hN0 : 0 ≤ N := by dsimp [N]; positivity
  have h1 : (B : ℝ) * P ≤ (B : ℝ) ^ 2 / V := by
    have hB0 : 0 ≤ (B : ℝ) := Nat.cast_nonneg B
    calc
      (B : ℝ) * P ≤ (B : ℝ) * ((B : ℝ) / V) :=
        mul_le_mul_of_nonneg_left hPdivV hB0
      _ = (B : ℝ) ^ 2 / V := by ring
  have h2raw : N / ((A : ℝ) * P) ≤ 2 * N / ((A : ℝ) * U) := by
    rw [div_le_div_iff₀ (mul_pos hA0 hP0) (mul_pos hA0 hU0)]
    have hAU : (A : ℝ) * U ≤ (A : ℝ) * (2 * P) :=
      mul_le_mul_of_nonneg_left hU2P (Nat.cast_nonneg A)
    have hmul := mul_le_mul_of_nonneg_left hAU hN0
    nlinarith
  have h2 : 1000 * Real.sqrt (T * r) * (B : ℝ) ^ 2 * Real.sqrt B /
      ((A : ℝ) * P) ≤
      2000 * Real.sqrt (T * r) * (B : ℝ) ^ 2 * Real.sqrt B / ((A : ℝ) * U) := by
    dsimp [N] at h2raw
    calc
      1000 * Real.sqrt (T * r) * (B : ℝ) ^ 2 * Real.sqrt B / ((A : ℝ) * P)
          ≤ 2 * (1000 * Real.sqrt (T * r) * (B : ℝ) ^ 2 * Real.sqrt B) /
              ((A : ℝ) * U) := h2raw
      _ = 2000 * Real.sqrt (T * r) * (B : ℝ) ^ 2 * Real.sqrt B /
              ((A : ℝ) * U) := by ring
  have h4 : (B : ℝ) ^ 2 / P ≤ 2 * (B : ℝ) ^ 2 / U := by
    rw [div_le_div_iff₀ hP0 hU0]
    have hBsq : 0 ≤ (B : ℝ) ^ 2 := sq_nonneg _
    nlinarith
  rw [typeIIHybridBlockRootEnvelope, typeIIHybridVaughanRootEnvelope]
  have hs1 := Real.sqrt_le_sqrt h1
  have hs2 := Real.sqrt_le_sqrt h2
  have hs4 := Real.sqrt_le_sqrt h4
  exact add_le_add (add_le_add (add_le_add hs1 hs2) le_rfl) hs4

/-- Every block, including support-empty blocks, satisfies the Vaughan-scale root estimate. -/
theorem exists_norm_maskedBlockSum_le_hybrid_vaughan :
    ∃ C : ℝ, 0 < C ∧ ∀ {T r : ℝ} {A B L U V P Q : ℕ},
      0 < T → 0 < r → 1 ≤ A → 1 ≤ B → 1 ≤ L → 1 ≤ U → 1 ≤ V →
      1 ≤ P → 2 ≤ Q → Q ≤ 2 * P → Q ≤ L + 1 → 8 * r ≤ (A : ℝ) →
      ‖maskedBlockSum T r A B L P Q (fun d => typeIILong U d)
          (fun m => typeIIShort V m)‖
        ≤ Real.sqrt (8 * C * Real.log L * typeIIPolylogEnvelope B) *
          typeIIHybridVaughanRootEnvelope T r A B U V := by
  obtain ⟨C, hC0, hmain⟩ := exists_norm_maskedBlockSum_le_hybrid_root
  refine ⟨C, hC0, ?_⟩
  intro T r A B L U V P Q hT hr hA hB hL hU hV hP hQ hQ2P hQL h8
  by_cases hzero : maskedBlockSum T r A B L P Q (fun d => typeIILong U d)
      (fun m => typeIIShort V m) = 0
  · rw [hzero, norm_zero]
    exact mul_nonneg (Real.sqrt_nonneg _)
      (typeIIHybridVaughanRootEnvelope_nonneg T r A B U V)
  · have hblock := hmain (U := U) (V := V) hT hr hA hB hL hP hQ hQ2P hQL h8
    have hscale := typeIIHybridBlockRootEnvelope_le_vaughan_of_ne_zero
      hT hr hA hU hV hP hQ hQ2P hzero
    exact hblock.trans (mul_le_mul_of_nonneg_left hscale (Real.sqrt_nonneg _))

end

end RHTower.Sieve
