/-
# Chen--Gupta--Li dyadic Mellin phase bridge

CGL Lemma 4.5 starts from matrix entries containing the literal phase
`n^{it}` and applies Poisson summation to `h_t(n / N)`.  This module proves
the exact change of variables.  Each edge of a cubic trace acquires a factor
`N^{i(t_r - t_s)`, and the three factors cancel around the cycle.
-/

import GaloisForLFunctions.RHTower.ChenGuptaLiHtReciprocalAllOrder
import GaloisForLFunctions.RHTower.ChenGuptaLiCharacterLargeValues

open Complex

noncomputable section

namespace RHTower

/-- A literal dyadic matrix phase is its scale phase times the Mellin phase at
the normalized index. -/
theorem cglCharacterDyadicPhase_eq_mellinPhase_mul_scaled
    (N : CGLPositiveLength) (t : ℝ) (j : Fin N.value) :
    cglCharacterDyadicPhase N.value t j =
      cglMellinPhase t N.value *
        cglMellinPhase t ((cglCharacterDyadicIndex N.value j : ℝ) / N.value) := by
  have hN : (N.value : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt N.positive
  have hn : (cglCharacterDyadicIndex N.value j : ℝ) ≠ 0 := by
    apply ne_of_gt
    exact_mod_cast (by
      unfold cglCharacterDyadicIndex
      omega : 0 < cglCharacterDyadicIndex N.value j)
  have hscaled : ((cglCharacterDyadicIndex N.value j : ℝ) / N.value) ≠ 0 :=
    div_ne_zero hn hN
  have hlog : Real.log (cglCharacterDyadicIndex N.value j : ℝ) =
      Real.log N.value +
        Real.log ((cglCharacterDyadicIndex N.value j : ℝ) / N.value) := by
    rw [← Real.log_mul hN hscaled]
    congr 1
    field_simp
  unfold cglCharacterDyadicPhase cglMellinPhase
  rw [hlog, ← Complex.exp_add]
  push_cast
  ring

/-- The three scale phases introduced by a cubic trace telescope to one. -/
theorem cglMellinPhase_cyclic_difference_product
    (N : CGLPositiveLength) (t₁ t₂ t₃ : ℝ) :
    cglMellinPhase (t₁ - t₂) N.value *
        cglMellinPhase (t₂ - t₃) N.value *
          cglMellinPhase (t₃ - t₁) N.value = 1 := by
  unfold cglMellinPhase
  rw [← Complex.exp_add, ← Complex.exp_add]
  push_cast
  ring_nf
  simp

/-- The product of literal matrix phases on a cubic trace is precisely the
product of the normalized Mellin phases to which CGL applies Poisson summation. -/
theorem cglCharacterDyadicPhase_cubic_cycle_eq_scaled
    (N : CGLPositiveLength) (t₁ t₂ t₃ : ℝ)
    (j₁ j₂ j₃ : Fin N.value) :
    cglCharacterDyadicPhase N.value (t₁ - t₂) j₁ *
        cglCharacterDyadicPhase N.value (t₂ - t₃) j₂ *
          cglCharacterDyadicPhase N.value (t₃ - t₁) j₃ =
      cglMellinPhase (t₁ - t₂) ((cglCharacterDyadicIndex N.value j₁ : ℝ) / N.value) *
        cglMellinPhase (t₂ - t₃) ((cglCharacterDyadicIndex N.value j₂ : ℝ) / N.value) *
          cglMellinPhase (t₃ - t₁) ((cglCharacterDyadicIndex N.value j₃ : ℝ) / N.value) := by
  have hcycle := cglMellinPhase_cyclic_difference_product N t₁ t₂ t₃
  rw [cglCharacterDyadicPhase_eq_mellinPhase_mul_scaled,
    cglCharacterDyadicPhase_eq_mellinPhase_mul_scaled,
    cglCharacterDyadicPhase_eq_mellinPhase_mul_scaled]
  calc
    _ = (cglMellinPhase (t₁ - t₂) N.value *
          cglMellinPhase (t₂ - t₃) N.value *
            cglMellinPhase (t₃ - t₁) N.value) *
        (cglMellinPhase (t₁ - t₂) ((cglCharacterDyadicIndex N.value j₁ : ℝ) / N.value) *
          cglMellinPhase (t₂ - t₃) ((cglCharacterDyadicIndex N.value j₂ : ℝ) / N.value) *
            cglMellinPhase (t₃ - t₁) ((cglCharacterDyadicIndex N.value j₃ : ℝ) / N.value)) := by ring
    _ = _ := by rw [hcycle]; ring

end RHTower
