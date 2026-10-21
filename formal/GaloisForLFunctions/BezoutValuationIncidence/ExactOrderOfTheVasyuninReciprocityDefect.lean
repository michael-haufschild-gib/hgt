import GaloisForLFunctions.BezoutValuationIncidence.LogarithmicReciprocityDefectForNearbyModuli

/-!
# The exact order of the Vasyunin reciprocity defect

The reciprocity defect of the Nyman–Beurling cotangent sums is the residue-difference energy,

`π (V(q, p) + V(p, q)) + (q − p) log(q/p) = E(p, q) = Σ_{M ≥ 1} (M mod p − M mod q)²/(M(M+1))`

(`vasyunin_reciprocity_exact`). With `h = q − p > 0` its exact order is

`h (1 + log⁺(p/h)) / 18 ≤ E(p, p + h) ≤ 12 h (1 + log⁺(p/h))`        (`residueDifferenceEnergy_exact_order`).

So the defect is `o(p + q)` exactly when `h = o(p)`, and then it is `h log(p/h) + O(h)`; for moduli of
different sizes it has order `p + q` and no bound below `O(p + q)` holds. The new input is the lower
bound `E(p, q) ≥ (q − p)/8`: on `[p, q)` the residues differ by `M − (M mod p) ≥ M/2`.
-/

open Finset

namespace GaloisForLFunctions.BezoutValuationIncidence
noncomputable section
set_option autoImplicit false

/-- **The defect is at least `(m₂ − m₁)/8`** for `m₁ < m₂`: on `[m₁, m₂)` the residues differ by at
least `M/2`. -/
theorem residueDifferenceEnergy_ge_gap {m₁ m₂ : ℕ} (h₁ : 0 < m₁) (h₁₂ : m₁ < m₂) :
    ((m₂ : ℝ) - m₁) / 8 ≤ residueDifferenceEnergy m₁ m₂ := by
  have h₂ : 0 < m₂ := lt_trans h₁ h₁₂
  have hS := hasSum_residueDifferenceEnergy h₁ h₂
  have hf0 : ∀ M : ℕ, 0 ≤ (((M % m₁ : ℕ) : ℝ) - ((M % m₂ : ℕ) : ℝ)) ^ 2 /
      ((M : ℝ) * ((M : ℝ) + 1)) := fun M => div_nonneg (sq_nonneg _) (by positivity)
  have hband : ∀ M ∈ Ico m₁ m₂, (1 : ℝ) / 8 ≤
      (((M % m₁ : ℕ) : ℝ) - ((M % m₂ : ℕ) : ℝ)) ^ 2 / ((M : ℝ) * ((M : ℝ) + 1)) := by
    intro M hM
    obtain ⟨hlo, hhi⟩ := mem_Ico.mp hM
    rw [Nat.mod_eq_of_lt hhi]
    have hq : 1 ≤ M / m₁ := (Nat.le_div_iff_mul_le h₁).mpr (by omega)
    have hd := Nat.mod_add_div M m₁
    have hmod : M % m₁ < m₁ := Nat.mod_lt M h₁
    -- `2 (M mod m₁) ≤ M`
    have h2 : 2 * (M % m₁) ≤ M := by
      have : m₁ ≤ m₁ * (M / m₁) := Nat.le_mul_of_pos_right m₁ hq
      omega
    have h2R : 2 * ((M % m₁ : ℕ) : ℝ) ≤ M := by exact_mod_cast h2
    have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast (by omega : 1 ≤ M)
    have hsq : (M : ℝ) ^ 2 / 4 ≤ (((M % m₁ : ℕ) : ℝ) - (M : ℝ)) ^ 2 := by
      have hm0 : (0 : ℝ) ≤ ((M % m₁ : ℕ) : ℝ) := Nat.cast_nonneg _
      nlinarith
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  calc ((m₂ : ℝ) - m₁) / 8 = ∑ _M ∈ Ico m₁ m₂, (1 : ℝ) / 8 := by
        rw [sum_const, Nat.card_Ico, nsmul_eq_mul, Nat.cast_sub h₁₂.le]; ring
    _ ≤ ∑ M ∈ Ico m₁ m₂, (((M % m₁ : ℕ) : ℝ) - ((M % m₂ : ℕ) : ℝ)) ^ 2 /
          ((M : ℝ) * ((M : ℝ) + 1)) := sum_le_sum hband
    _ ≤ residueDifferenceEnergy m₁ m₂ := by
        rw [residueDifferenceEnergy, hS.tsum_eq]
        exact sum_le_hasSum _ (fun M _ => hf0 M) hS

/-- **Exact order of the reciprocity defect.** For moduli `p ≥ 1` and `p + h`, `h ≥ 1`,
`h (1 + log⁺(p/h))/18 ≤ E(p, p + h) ≤ 12 h (1 + log⁺(p/h))`. -/
theorem residueDifferenceEnergy_exact_order {p h : ℕ} (hp : 0 < p) (hh : 0 < h) :
    (h : ℝ) * (1 + max (Real.log ((p : ℝ) / h)) 0) / 18 ≤ residueDifferenceEnergy p (p + h) ∧
      residueDifferenceEnergy p (p + h) ≤ 12 * h * (1 + max (Real.log ((p : ℝ) / h)) 0) := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hhR : (0 : ℝ) < h := by exact_mod_cast hh
  have hgap := residueDifferenceEnergy_ge_gap hp (by omega : p < p + h)
  push_cast at hgap
  rw [show (p : ℝ) + h - p = h by ring] at hgap
  rcases le_or_gt h p with hhp | hhp
  · -- nearby moduli: the harmonic budget of `K = ⌊p/h⌋`
    set K := p / h with hK
    have hK1 : 1 ≤ K := (Nat.le_div_iff_mul_le hh).mpr (by omega)
    have hKR : (K : ℝ) ≤ p / h := by
      rw [le_div_iff₀ hhR]; exact_mod_cast Nat.div_mul_le_self p h
    have hKR' : (p : ℝ) / h < K + 1 := by
      rw [div_lt_iff₀ hhR]
      have := Nat.lt_succ_iff.mpr (le_refl (p / h))
      have hlt : p < (p / h + 1) * h := by
        have := Nat.lt_div_mul_add hh (a := p)
        linarith [Nat.div_add_mod p h, Nat.mod_lt p hh]
      exact_mod_cast hlt
    have hlo := residueGapPronicEnergy_ge_harmonic_budget ⟨p, hp⟩ ⟨h, hh⟩
    have hhi := residueGapPronicEnergy_le_nearby ⟨p, hp⟩ ⟨h - 1, by simp; omega⟩
    simp only [PNat.mk_coe, show h - 1 + 1 = h by omega] at hlo hhi
    rw [← residueDifferenceEnergy_eq_residueGapPronicEnergy] at hlo hhi
    have hL0 : 0 ≤ Real.log ((p : ℝ) / h) :=
      Real.log_nonneg ((one_le_div hhR).mpr (by exact_mod_cast hhp))
    rw [max_eq_left hL0]
    have hH1 := log_add_one_le_harmonic K
    have hH2 := harmonic_le_one_add_log K
    have hlogK : Real.log (K : ℝ) ≤ Real.log ((p : ℝ) / h) :=
      Real.log_le_log (by exact_mod_cast hK1) hKR
    have hlogK1 : Real.log ((p : ℝ) / h) ≤ Real.log ((K + 1 : ℕ) : ℝ) := by
      push_cast; exact Real.log_le_log (by positivity) hKR'.le
    constructor
    · -- `E ≥ max(h/8, h(L − 1))`
      set L := Real.log ((p : ℝ) / h)
      rcases le_or_gt L (5 / 4) with hL | hL
      · nlinarith
      · nlinarith
    · nlinarith
  · -- distant moduli
    have hL : Real.log ((p : ℝ) / h) ≤ 0 :=
      Real.log_nonpos (div_nonneg hpR.le hhR.le) ((div_le_one hhR).mpr (by exact_mod_cast hhp.le))
    rw [max_eq_right hL]
    have hup := residueDifferenceEnergy_le hp (by omega : 0 < p + h)
    push_cast at hup
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp
    have hh1 : (1 : ℝ) ≤ h := by exact_mod_cast hh
    have h1 : ((p : ℝ) - 1) ^ 2 / p ≤ p := by
      rw [div_le_iff₀ hpR]; nlinarith
    have h2 : ((p : ℝ) + h - 1) ^ 2 / (p + h) ≤ p + h := by
      rw [div_le_iff₀ (by positivity)]; nlinarith
    have hph : (p : ℝ) < h := by exact_mod_cast hhp
    constructor <;> nlinarith

/-- **Exact order of Vasyunin reciprocity.** With `h = q − p ≥ 1`,
`h(1 + log⁺(p/h))/18 ≤ π(V(q, p) + V(p, q)) + (q − p) log(q/p) ≤ 12 h(1 + log⁺(p/h))`. -/
theorem vasyunin_reciprocity_exact_order {p h : ℕ} (hp : 0 < p) (hh : 0 < h) :
    (h : ℝ) * (1 + max (Real.log ((p : ℝ) / h)) 0) / 18 ≤
        Real.pi * (vasyuninSum (p + h) p + vasyuninSum p (p + h)) +
          (((p + h : ℕ) : ℝ) - p) * (Real.log ((p + h : ℕ) : ℝ) - Real.log p) ∧
      Real.pi * (vasyuninSum (p + h) p + vasyuninSum p (p + h)) +
          (((p + h : ℕ) : ℝ) - p) * (Real.log ((p + h : ℕ) : ℝ) - Real.log p) ≤
        12 * h * (1 + max (Real.log ((p : ℝ) / h)) 0) := by
  rw [vasyunin_reciprocity_exact hp (by omega)]
  exact residueDifferenceEnergy_exact_order hp hh

end

end GaloisForLFunctions.BezoutValuationIncidence
