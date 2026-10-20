import GaloisForLFunctions.BezoutValuationIncidence.ExactVasyuninReciprocityAsResidueDifferenceEnergy
import GaloisForLFunctions.BezoutValuationIncidence.PronicResidueGapEnergyAndPrimePairDistance

/-!
# Vasyunin reciprocity for nearby moduli

The Vasyunin reciprocity defect is the residue-difference energy, and the residue-difference
energy of moduli `p` and `p + h`, with `h ≤ p`, lies between `h H_K - h` and `h H_K + 4h` for
`K = ⌊p/h⌋`. Hence

`h H_K - 2h ≤ π (V(p+h, p) + V(p, p+h)) ≤ h H_K + 4h`.

The symmetric Vasyunin sum of nearby moduli is therefore of exact order `h log(p/h)`. It is of
order `log p` for consecutive or twin moduli, and of linear order only when the moduli differ in
size.
-/

open Finset
open scoped BigOperators

namespace GaloisForLFunctions.BezoutValuationIncidence
noncomputable section
set_option autoImplicit false

theorem residueDifferenceEnergy_eq_residueGapPronicEnergy (p q : ℕ) :
    residueDifferenceEnergy p q = residueGapPronicEnergy p q := rfl

/-- **Vasyunin reciprocity for nearby moduli.** -/
theorem vasyunin_reciprocity_nearby_moduli (p : ℕ+) (d : Fin (p : ℕ)) :
    let h := d.val + 1
    let K := (p : ℕ) / h
    (h : ℝ) * (harmonic K : ℝ) - 2 * h ≤
        Real.pi * (vasyuninSum ((p : ℕ) + h) p + vasyuninSum p ((p : ℕ) + h)) ∧
      Real.pi * (vasyuninSum ((p : ℕ) + h) p + vasyuninSum p ((p : ℕ) + h)) ≤
        (h : ℝ) * (harmonic K : ℝ) + 4 * h := by
  dsimp only
  have hhp : d.val + 1 ≤ (p : ℕ) := d.isLt
  have hrec := vasyunin_reciprocity_exact (m₁ := p) (m₂ := (p : ℕ) + (d.val + 1)) p.pos (by omega)
  have hlo := residueGapPronicEnergy_ge_harmonic_budget p ⟨d.val + 1, by omega⟩
  have hhi := residueGapPronicEnergy_le_nearby p d
  dsimp only at hlo hhi
  simp only [PNat.mk_coe] at hlo
  rw [residueDifferenceEnergy_eq_residueGapPronicEnergy] at hrec
  have hp0 : (0 : ℝ) < (p : ℕ) := by exact_mod_cast p.pos
  have hh0 : (0 : ℝ) ≤ ((d.val + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hhpR : ((d.val + 1 : ℕ) : ℝ) ≤ (p : ℕ) := by exact_mod_cast hhp
  have hgap : (((p : ℕ) + (d.val + 1) : ℕ) : ℝ) - (p : ℕ) = ((d.val + 1 : ℕ) : ℝ) := by
    push_cast
    ring
  have hlog0 : 0 ≤ Real.log (((p : ℕ) + (d.val + 1) : ℕ) : ℝ) - Real.log (p : ℕ) := by
    rw [sub_nonneg]
    exact Real.log_le_log hp0 (by push_cast; linarith)
  have hlog1 : Real.log (((p : ℕ) + (d.val + 1) : ℕ) : ℝ) - Real.log (p : ℕ) ≤ 1 := by
    rw [← Real.log_div (by positivity) hp0.ne']
    have h1 := Real.log_le_sub_one_of_pos
      (show (0 : ℝ) < (((p : ℕ) + (d.val + 1) : ℕ) : ℝ) / (p : ℕ) by positivity)
    have h2 : (((p : ℕ) + (d.val + 1) : ℕ) : ℝ) / (p : ℕ) - 1 ≤ 1 := by
      rw [div_sub_one hp0.ne', div_le_one hp0, hgap]
      exact hhpR
    linarith
  rw [hgap] at hrec
  have hc0 : 0 ≤ ((d.val + 1 : ℕ) : ℝ) *
      (Real.log (((p : ℕ) + (d.val + 1) : ℕ) : ℝ) - Real.log (p : ℕ)) := mul_nonneg hh0 hlog0
  have hc1 : ((d.val + 1 : ℕ) : ℝ) *
      (Real.log (((p : ℕ) + (d.val + 1) : ℕ) : ℝ) - Real.log (p : ℕ)) ≤ ((d.val + 1 : ℕ) : ℝ) := by
    nlinarith
  push_cast at hrec hlo hhi hc0 hc1 ⊢
  constructor <;> linarith

end

end GaloisForLFunctions.BezoutValuationIncidence
