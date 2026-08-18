import GaloisForLFunctions.RHTower.Sieve.SlopeQuotientLimit
import GaloisForLFunctions.RHTower.Sieve.BudgetSRate
import GaloisForLFunctions.RHTower.Sieve.TuranKubiliusRange

/-!
# The ladder constant, normalised

The affine constant of the ladder majorant is negligible against the product of the squared fibre
range and the squared harmonic mass.  Three mechanisms combine: the annulus bound against the number
of steps, the twisted Möbius majorant against the disc contribution, and the polynomial cofactor
against the sifting cutoff.
-/

namespace RHTower.Sieve

open Filter Topology

noncomputable section

/-- The annulus group of the normalised ladder constant. -/
theorem const_annulus_le {L B η ρ R h W : ℝ}
    (hη : 0 < η) (hL1 : 1 ≤ L) (hB1 : 1 ≤ B) (hh1 : 1 ≤ h) (hW1 : 1 ≤ W)
    (hρ0 : 0 ≤ ρ) (hρR : ρ ≤ R) (hinvη : 1 / η ≤ 2 * L) :
    4 * (5 * Real.exp 1 / 2) * ρ ^ 2 * (2 * (L * B) ^ 2 + 2 * (h / η) ^ 2) / (B ^ 2 * W ^ 2)
      ≤ 20 * Real.exp 1 * (R * L) ^ 2 * (1 + 4 * (h / B) ^ 2) := by
  have hh0 : (0 : ℝ) < h := by linarith
  have hB0 : (0 : ℝ) < B := by linarith
  have hW0 : (0 : ℝ) < W := by linarith
  have hW2 : (1 : ℝ) ≤ W ^ 2 := by nlinarith [hW1]
  have hid : 4 * (5 * Real.exp 1 / 2) * ρ ^ 2 * (2 * (L * B) ^ 2 + 2 * (h / η) ^ 2)
        / (B ^ 2 * W ^ 2)
      = 20 * Real.exp 1 * (ρ * L) ^ 2 / W ^ 2
        + 20 * Real.exp 1 * (ρ * (1 / η)) ^ 2 * (h / B) ^ 2 / W ^ 2 := by
    field_simp
    try ring
  rw [hid]
  have hE0 : (0 : ℝ) ≤ 20 * Real.exp 1 := by positivity
  have hρL0 : (0 : ℝ) ≤ ρ * L := mul_nonneg hρ0 (by linarith)
  have hρLR : ρ * L ≤ R * L := mul_le_mul_of_nonneg_right hρR (by linarith)
  have hρL : (ρ * L) ^ 2 ≤ (R * L) ^ 2 := pow_le_pow_left₀ hρL0 hρLR 2
  have hη0 : (0 : ℝ) ≤ ρ * (1 / η) := mul_nonneg hρ0 (div_nonneg zero_le_one hη.le)
  have hρη : (ρ * (1 / η)) ^ 2 ≤ 4 * (R * L) ^ 2 := by
    have h1 : ρ * (1 / η) ≤ 2 * (R * L) := by
      have hstep : ρ * (1 / η) ≤ ρ * (2 * L) := mul_le_mul_of_nonneg_left hinvη hρ0
      have he : ρ * (2 * L) = 2 * (ρ * L) := by ring
      linarith [hstep, he, hρLR]
    have h2 := pow_le_pow_left₀ hη0 h1 2
    have h3 : (2 * (R * L)) ^ 2 = 4 * (R * L) ^ 2 := by ring
    linarith [h2, h3]
  have hp1 : 20 * Real.exp 1 * (ρ * L) ^ 2 / W ^ 2 ≤ 20 * Real.exp 1 * (R * L) ^ 2 := by
    have hnum : 20 * Real.exp 1 * (ρ * L) ^ 2 ≤ 20 * Real.exp 1 * (R * L) ^ 2 :=
      mul_le_mul_of_nonneg_left hρL hE0
    have hnn : (0 : ℝ) ≤ 20 * Real.exp 1 * (ρ * L) ^ 2 := mul_nonneg hE0 (sq_nonneg _)
    have hstep : 20 * Real.exp 1 * (ρ * L) ^ 2 / W ^ 2
        ≤ 20 * Real.exp 1 * (ρ * L) ^ 2 / 1 :=
      div_le_div_of_nonneg_left hnn (by norm_num) hW2
    rw [div_one] at hstep
    linarith
  have hp2 : 20 * Real.exp 1 * (ρ * (1 / η)) ^ 2 * (h / B) ^ 2 / W ^ 2
      ≤ 20 * Real.exp 1 * (R * L) ^ 2 * (4 * (h / B) ^ 2) := by
    have hnum : 20 * Real.exp 1 * (ρ * (1 / η)) ^ 2
        ≤ 20 * Real.exp 1 * (4 * (R * L) ^ 2) := mul_le_mul_of_nonneg_left hρη hE0
    have hmul := mul_le_mul_of_nonneg_right hnum (sq_nonneg (h / B))
    have hval : 20 * Real.exp 1 * (4 * (R * L) ^ 2) * (h / B) ^ 2
        = 20 * Real.exp 1 * (R * L) ^ 2 * (4 * (h / B) ^ 2) := by ring
    have hnn : (0 : ℝ) ≤ 20 * Real.exp 1 * (ρ * (1 / η)) ^ 2 * (h / B) ^ 2 :=
      mul_nonneg (mul_nonneg hE0 (sq_nonneg _)) (sq_nonneg _)
    have hstep : 20 * Real.exp 1 * (ρ * (1 / η)) ^ 2 * (h / B) ^ 2 / W ^ 2
        ≤ 20 * Real.exp 1 * (ρ * (1 / η)) ^ 2 * (h / B) ^ 2 / 1 :=
      div_le_div_of_nonneg_left hnn (by norm_num) hW2
    rw [div_one] at hstep
    linarith [hstep, hmul, hval]
  have hrhs : 20 * Real.exp 1 * (R * L) ^ 2 * (1 + 4 * (h / B) ^ 2)
      = 20 * Real.exp 1 * (R * L) ^ 2
        + 20 * Real.exp 1 * (R * L) ^ 2 * (4 * (h / B) ^ 2) := by ring
  linarith [hp1, hp2, hrhs]

/-- The disc group of the normalised ladder constant. -/
theorem const_disc_le {L B Q η h W V s NP SN : ℝ}
    (hQ1 : 1 < Q) (hη : 0 < η) (hη1 : η ≤ 1) (hL1 : 1 ≤ L) (hB1 : 1 ≤ B) (hh1 : 1 ≤ h)
    (hW1 : 1 ≤ W) (hV1 : 1 ≤ V) (hs0 : 0 ≤ s) (hNP0 : 0 ≤ NP) (hNP : NP ≤ 2 * h)
    (hSN0 : 0 ≤ SN) (hSN : SN ≤ L * B / Q) :
    2 * (V * (s * ((1 + η) * B * W) + NP + s * SN + L)) ^ 2 / (B ^ 2 * W ^ 2)
      ≤ 2 * (V * (2 * s + 2 * (h / B) + s * L + L / B)) ^ 2 := by
  have hh0 : (0 : ℝ) < h := by linarith
  have hB0 : (0 : ℝ) < B := by linarith
  have hQ0 : (0 : ℝ) < Q := by linarith
  have hW0 : (0 : ℝ) < W := by linarith
  have hinner0 : (0 : ℝ) ≤ s * ((1 + η) * B * W) + NP + s * SN + L := by
    have h1 : (0 : ℝ) ≤ s * ((1 + η) * B * W) :=
      mul_nonneg hs0 (mul_nonneg (mul_nonneg (by linarith) hB0.le) hW0.le)
    have h2 : (0 : ℝ) ≤ s * SN := mul_nonneg hs0 hSN0
    linarith
  have hid : 2 * (V * (s * ((1 + η) * B * W) + NP + s * SN + L)) ^ 2 / (B ^ 2 * W ^ 2)
      = 2 * (V * ((s * ((1 + η) * B * W) + NP + s * SN + L) / (B * W))) ^ 2 := by
    field_simp
  rw [hid]
  have hquot : (s * ((1 + η) * B * W) + NP + s * SN + L) / (B * W)
      ≤ 2 * s + 2 * (h / B) + s * L + L / B := by
    rw [div_le_iff₀ (mul_pos hB0 hW0)]
    have e1 : (2 * s + 2 * (h / B) + s * L + L / B) * (B * W)
        = 2 * s * (B * W) + 2 * (h / B) * (B * W) + s * L * (B * W) + L / B * (B * W) := by
      ring
    rw [e1]
    have hsBW : (0 : ℝ) ≤ s * (B * W) := mul_nonneg hs0 (mul_pos hB0 hW0).le
    have b1 : s * ((1 + η) * B * W) ≤ 2 * s * (B * W) := by
      have hmul : (s * (B * W)) * (1 + η) ≤ (s * (B * W)) * 2 :=
        mul_le_mul_of_nonneg_left (by linarith) hsBW
      calc s * ((1 + η) * B * W) = (s * (B * W)) * (1 + η) := by ring
        _ ≤ (s * (B * W)) * 2 := hmul
        _ = 2 * s * (B * W) := by ring
    have b2 : NP ≤ 2 * (h / B) * (B * W) := by
      have hval : 2 * (h / B) * (B * W) = 2 * h * W := by field_simp; try ring
      rw [hval]
      have hmul : 2 * h * 1 ≤ 2 * h * W := mul_le_mul_of_nonneg_left hW1 (by linarith)
      linarith [hNP, hmul]
    have b3 : s * SN ≤ s * L * (B * W) := by
      have hLB0 : (0 : ℝ) ≤ L * B := mul_nonneg (by linarith) (by linarith)
      have hSNb : SN ≤ L * B := by
        have hle : L * B / Q ≤ L * B / 1 :=
          div_le_div_of_nonneg_left hLB0 (by norm_num) hQ1.le
        rw [div_one] at hle
        linarith [hSN, hle]
      have hsSN : s * SN ≤ s * (L * B) := mul_le_mul_of_nonneg_left hSNb hs0
      have hsLB : (0 : ℝ) ≤ s * (L * B) := mul_nonneg hs0 hLB0
      have hmulW : (s * (L * B)) * 1 ≤ (s * (L * B)) * W :=
        mul_le_mul_of_nonneg_left hW1 hsLB
      calc s * SN ≤ s * (L * B) := hsSN
        _ = (s * (L * B)) * 1 := by ring
        _ ≤ (s * (L * B)) * W := hmulW
        _ = s * L * (B * W) := by ring
    have b4 : L ≤ L / B * (B * W) := by
      have hval : L / B * (B * W) = L * W := by field_simp; try ring
      rw [hval]
      have hmul : L * 1 ≤ L * W := mul_le_mul_of_nonneg_left hW1 (by linarith)
      linarith [hmul]
    linarith
  have hVq : (0 : ℝ) ≤ V * ((s * ((1 + η) * B * W) + NP + s * SN + L) / (B * W)) :=
    mul_nonneg (by linarith) (div_nonneg hinner0 (mul_pos hB0 hW0).le)
  have hmul : V * ((s * ((1 + η) * B * W) + NP + s * SN + L) / (B * W))
      ≤ V * (2 * s + 2 * (h / B) + s * L + L / B) :=
    mul_le_mul_of_nonneg_left hquot (by linarith)
  have := pow_le_pow_left₀ hVq hmul 2
  linarith

/-- The cofactor group of the normalised ladder constant. -/
theorem const_cofactor_le {L B Q η h W M S MB P1 P2 P3 B' : ℝ}
    (hQ1 : 1 < Q) (hη : 0 < η) (hL1 : 1 ≤ L) (hB1 : 1 ≤ B) (hh1 : 1 ≤ h) (hW1 : 1 ≤ W)
    (hM0 : 0 ≤ M) (hMB : M ≤ MB) (hMB0 : 0 ≤ MB)
    (hLη : L * η ^ 2 ≤ 2 * P1) (hLpoly : L ≤ 2 * P2) (hinvηP : 1 / η ≤ P3)
    (hB' : B' ≤ 2 * B) (hP20 : 0 ≤ P2) (hP30 : 0 ≤ P3)
    (hSdef : S = L * ((1 + B) * η ^ 2 + 5) + 5 * h
      + (η * B + (1 + B) * η) * (2 / (Q * η)) + B * (2 / (Q ^ 2 * η))) :
    2 * (5 * Real.exp 1 / 2 * B') * (M * S) / (B ^ 2 * W ^ 2)
      ≤ 10 * Real.exp 1 * (4 * (MB * P1 / W ^ 2) + 10 * (MB * P2 / B)
        + 5 * (MB * (h / B)) + 6 * (MB / Q) + 2 * (MB * P3 / Q)) := by
  have hh0 : (0 : ℝ) < h := by linarith
  have hB0 : (0 : ℝ) < B := by linarith
  have hQ0 : (0 : ℝ) < Q := by linarith
  have hW0 : (0 : ℝ) < W := by linarith
  have hB2 : (0 : ℝ) < B ^ 2 := pow_pos hB0 2
  have hW2 : (1 : ℝ) ≤ W ^ 2 := by nlinarith [hW1]
  have hW20 : (0 : ℝ) < W ^ 2 := by linarith
  have hden : (0 : ℝ) < B ^ 2 * W ^ 2 := mul_pos hB2 hW20
  have hQη : (0 : ℝ) < Q * η := mul_pos hQ0 hη
  have hQ2η : (0 : ℝ) < Q ^ 2 * η := mul_pos (pow_pos hQ0 2) hη
  have hE : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  have hhB : (0 : ℝ) ≤ h / B := div_nonneg hh0.le hB0.le
  have hS0 : (0 : ℝ) ≤ S := by
    have h1 : (0 : ℝ) ≤ L * ((1 + B) * η ^ 2 + 5) :=
      mul_nonneg (by linarith) (by
        have := mul_nonneg (by linarith : (0:ℝ) ≤ 1 + B) (sq_nonneg η)
        linarith)
    have h2 : (0 : ℝ) ≤ (η * B + (1 + B) * η) * (2 / (Q * η)) :=
      mul_nonneg (add_nonneg (mul_nonneg hη.le (by linarith))
        (mul_nonneg (by linarith) hη.le)) (div_nonneg (by norm_num) hQη.le)
    have h3 : (0 : ℝ) ≤ B * (2 / (Q ^ 2 * η)) :=
      mul_nonneg (by linarith) (div_nonneg (by norm_num) hQ2η.le)
    rw [hSdef]; linarith
  have hMS0 : (0 : ℝ) ≤ M * S := mul_nonneg hM0 hS0
  have hEB : 2 * (5 * Real.exp 1 / 2 * B') ≤ 2 * (5 * Real.exp 1 / 2 * (2 * B)) := by
    have hc : (0 : ℝ) ≤ 5 * Real.exp 1 / 2 := by positivity
    have := mul_le_mul_of_nonneg_left hB' hc
    linarith
  have hstep : 2 * (5 * Real.exp 1 / 2 * B') * (M * S) / (B ^ 2 * W ^ 2)
      ≤ 2 * (5 * Real.exp 1 / 2 * (2 * B)) * (M * S) / (B ^ 2 * W ^ 2) :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hEB hMS0) hden.le
  refine hstep.trans ?_
  have hid : 2 * (5 * Real.exp 1 / 2 * (2 * B)) * (M * S) / (B ^ 2 * W ^ 2)
      = 10 * Real.exp 1 * (M * (S / B)) / W ^ 2 := by
    field_simp
    try ring
  rw [hid]
  have hSle : S ≤ 2 * L * η ^ 2 * B + 5 * L + 5 * h + 6 * B / Q + 2 * B * (1 / η) / Q := by
    have hLη0 : (0 : ℝ) ≤ L * η ^ 2 := mul_nonneg (by linarith) (sq_nonneg η)
    have h1 : L * ((1 + B) * η ^ 2 + 5) ≤ 2 * L * η ^ 2 * B + 5 * L := by
      have hstep2 : (L * η ^ 2) * (1 + B) ≤ (L * η ^ 2) * (2 * B) :=
        mul_le_mul_of_nonneg_left (by linarith) hLη0
      calc L * ((1 + B) * η ^ 2 + 5) = (L * η ^ 2) * (1 + B) + 5 * L := by ring
        _ ≤ (L * η ^ 2) * (2 * B) + 5 * L := by linarith
        _ = 2 * L * η ^ 2 * B + 5 * L := by ring
    have hηB : η ≤ B * η := by
      have := mul_le_mul_of_nonneg_right hB1 hη.le
      linarith [this]
    have h2 : (η * B + (1 + B) * η) * (2 / (Q * η)) ≤ 6 * B / Q := by
      have h3B : η * B + (1 + B) * η ≤ 3 * B * η := by
        calc η * B + (1 + B) * η = 2 * (B * η) + η := by ring
          _ ≤ 2 * (B * η) + B * η := by linarith [hηB]
          _ = 3 * B * η := by ring
      have hq0 : (0 : ℝ) ≤ 2 / (Q * η) := div_nonneg (by norm_num) hQη.le
      have hfin : (η * B + (1 + B) * η) * (2 / (Q * η)) ≤ (3 * B * η) * (2 / (Q * η)) :=
        mul_le_mul_of_nonneg_right h3B hq0
      have hval : (3 * B * η) * (2 / (Q * η)) = 6 * B / Q := by field_simp; try ring
      linarith [hfin, hval]
    have h3 : B * (2 / (Q ^ 2 * η)) ≤ 2 * B * (1 / η) / Q := by
      have hQ2 : Q ≤ Q ^ 2 := by
        have hmulQ := mul_le_mul_of_nonneg_left hQ1.le hQ0.le
        rw [pow_two]
        linarith [hmulQ]
      have hq : (2 : ℝ) / (Q ^ 2 * η) ≤ 2 / (Q * η) := by
        refine div_le_div_of_nonneg_left (by norm_num) hQη ?_
        have := mul_le_mul_of_nonneg_right hQ2 hη.le
        linarith [this]
      have hstep2 : B * (2 / (Q ^ 2 * η)) ≤ B * (2 / (Q * η)) :=
        mul_le_mul_of_nonneg_left hq (by linarith)
      have hval : B * (2 / (Q * η)) = 2 * B * (1 / η) / Q := by field_simp; try ring
      linarith [hstep2, hval]
    rw [hSdef]; linarith
  have hSb : S / B ≤ 2 * (L * η ^ 2) + 5 * (L / B) + 5 * (h / B) + 6 * (1 / Q)
      + 2 * (P3 / Q) := by
    have hdiv : S / B ≤ (2 * L * η ^ 2 * B + 5 * L + 5 * h + 6 * B / Q
        + 2 * B * (1 / η) / Q) / B := div_le_div_of_nonneg_right hSle hB0.le
    refine hdiv.trans ?_
    have hexp : (2 * L * η ^ 2 * B + 5 * L + 5 * h + 6 * B / Q + 2 * B * (1 / η) / Q) / B
        = 2 * (L * η ^ 2) + 5 * (L / B) + 5 * (h / B) + 6 * (1 / Q)
          + 2 * ((1 / η) / Q) := by
      field_simp
      try ring
    rw [hexp]
    have hq4 : 2 * ((1 / η) / Q) ≤ 2 * (P3 / Q) := by
      have : (1 / η) / Q ≤ P3 / Q := div_le_div_of_nonneg_right hinvηP hQ0.le
      linarith
    linarith
  have hpoly : 2 * (L * η ^ 2) + 5 * (L / B) + 5 * (h / B) + 6 * (1 / Q) + 2 * (P3 / Q)
      ≤ 4 * P1 + 10 * (P2 / B) + 5 * (h / B) + 6 * (1 / Q) + 2 * (P3 / Q) := by
    have hq2 : 5 * (L / B) ≤ 10 * (P2 / B) := by
      have hLnum : L / B ≤ (2 * P2) / B := div_le_div_of_nonneg_right hLpoly hB0.le
      have h2 : (2 * P2) / B = 2 * (P2 / B) := by ring
      linarith [hLnum, h2]
    linarith [hLη, hq2]
  have hSb0 : (0 : ℝ) ≤ S / B := div_nonneg hS0 hB0.le
  have hcomb : M * (S / B)
      ≤ MB * (4 * P1 + 10 * (P2 / B) + 5 * (h / B) + 6 * (1 / Q) + 2 * (P3 / Q)) :=
    mul_le_mul hMB (hSb.trans hpoly) hSb0 hMB0
  have hE10 : (0 : ℝ) ≤ 10 * Real.exp 1 := by positivity
  have hnum : 10 * Real.exp 1 * (M * (S / B))
      ≤ 10 * Real.exp 1
        * (MB * (4 * P1 + 10 * (P2 / B) + 5 * (h / B) + 6 * (1 / Q) + 2 * (P3 / Q))) :=
    mul_le_mul_of_nonneg_left hcomb hE10
  refine (div_le_div_of_nonneg_right hnum hW20.le).trans ?_
  have hexpand : 10 * Real.exp 1
        * (MB * (4 * P1 + 10 * (P2 / B) + 5 * (h / B) + 6 * (1 / Q) + 2 * (P3 / Q)))
        / W ^ 2
      = 10 * Real.exp 1 * (4 * (MB * P1 / W ^ 2) + 10 * (MB * P2 / B) / W ^ 2
        + 5 * (MB * (h / B)) / W ^ 2 + 6 * (MB / Q) / W ^ 2
        + 2 * (MB * P3 / Q) / W ^ 2) := by
    field_simp
    try ring
  rw [hexpand]
  refine mul_le_mul_of_nonneg_left ?_ hE10
  have n2 : (0 : ℝ) ≤ 10 * (MB * P2 / B) := by
    have hb : (0 : ℝ) ≤ MB * P2 / B := div_nonneg (mul_nonneg hMB0 hP20) hB0.le
    linarith
  have n3 : (0 : ℝ) ≤ 5 * (MB * (h / B)) := by
    have hb : (0 : ℝ) ≤ MB * (h / B) := mul_nonneg hMB0 hhB
    linarith
  have n4 : (0 : ℝ) ≤ 6 * (MB / Q) := by
    have hb : (0 : ℝ) ≤ MB / Q := div_nonneg hMB0 hQ0.le
    linarith
  have n5 : (0 : ℝ) ≤ 2 * (MB * P3 / Q) := by
    have hb : (0 : ℝ) ≤ MB * P3 / Q := div_nonneg (mul_nonneg hMB0 hP30) hQ0.le
    linarith
  have d2 : 10 * (MB * P2 / B) / W ^ 2 ≤ 10 * (MB * P2 / B) := div_le_self n2 hW2
  have d3 : 5 * (MB * (h / B)) / W ^ 2 ≤ 5 * (MB * (h / B)) := div_le_self n3 hW2
  have d4 : 6 * (MB / Q) / W ^ 2 ≤ 6 * (MB / Q) := div_le_self n4 hW2
  have d5 : 2 * (MB * P3 / Q) / W ^ 2 ≤ 2 * (MB * P3 / Q) := div_le_self n5 hW2
  linarith [d2, d3, d4, d5]

/-- The arithmetic of the normalised ladder constant. -/
theorem const_quotient_arith {L B Q η ρ R h W M S MB P1 P2 P3 B' V s NP SN : ℝ}
    (hQ1 : 1 < Q) (hη : 0 < η) (hη1 : η ≤ 1) (hL1 : 1 ≤ L) (hB1 : 1 ≤ B) (hh1 : 1 ≤ h)
    (hW1 : 1 ≤ W) (hρ0 : 0 ≤ ρ) (hρR : ρ ≤ R) (hinvη : 1 / η ≤ 2 * L)
    (hM0 : 0 ≤ M) (hMB : M ≤ MB) (hMB0 : 0 ≤ MB)
    (hLη : L * η ^ 2 ≤ 2 * P1) (hLpoly : L ≤ 2 * P2) (hinvηP : 1 / η ≤ P3)
    (hB' : B' ≤ 2 * B) (hV1 : 1 ≤ V) (hs0 : 0 ≤ s)
    (hP20 : 0 ≤ P2) (hP30 : 0 ≤ P3)
    (hNP0 : 0 ≤ NP) (hNP : NP ≤ 2 * h) (hSN0 : 0 ≤ SN) (hSN : SN ≤ L * B / Q)
    (hSdef : S = L * ((1 + B) * η ^ 2 + 5) + 5 * h
      + (η * B + (1 + B) * η) * (2 / (Q * η)) + B * (2 / (Q ^ 2 * η))) :
    (4 * (5 * Real.exp 1 / 2) * ρ ^ 2 * (2 * (L * B) ^ 2 + 2 * (h / η) ^ 2)
        + 2 * (V * (s * ((1 + η) * B * W) + NP + s * SN + L)) ^ 2
        + 2 * (5 * Real.exp 1 / 2 * B') * (M * S)) / (B ^ 2 * W ^ 2)
      ≤ 20 * Real.exp 1 * (R * L) ^ 2 * (1 + 4 * (h / B) ^ 2)
        + 2 * (V * (2 * s + 2 * (h / B) + s * L + L / B)) ^ 2
        + 10 * Real.exp 1 * (4 * (MB * P1 / W ^ 2) + 10 * (MB * P2 / B)
          + 5 * (MB * (h / B)) + 6 * (MB / Q) + 2 * (MB * P3 / Q)) := by
  rw [add_div, add_div]
  have hg1 := const_annulus_le (R := R) (W := W) hη hL1 hB1 hh1 hW1 hρ0 hρR hinvη
  have hg2 := const_disc_le (W := W) hQ1 hη hη1 hL1 hB1 hh1 hW1 hV1 hs0 hNP0 hNP hSN0 hSN
  have hg3 := const_cofactor_le (W := W) (MB := MB) (P1 := P1) (P2 := P2) (P3 := P3)
    hQ1 hη hL1 hB1 hh1 hW1 hM0 hMB hMB0 hLη hLpoly hinvηP hB' hP20 hP30 hSdef
  linarith [hg1, hg2, hg3]

end

end RHTower.Sieve

namespace RHTower.Sieve

open Filter Topology

noncomputable section

/-- Replacing the fibre range by the square root of the outer scale. -/
theorem const_bound_mono {L B Q h W V s R MB P1 P2 P3 sx Vm : ℝ}
    (hB1 : 1 ≤ B) (hh1 : 1 ≤ h) (hsx : 0 < sx) (hsxB : sx ≤ B) (hs0 : 0 ≤ s)
    (hL1 : 1 ≤ L) (hV1 : 1 ≤ V) (hVm : V ≤ Vm) (hMB0 : 0 ≤ MB) (hP20 : 0 ≤ P2)
    (hLpoly : L ≤ 2 * P2) :
    20 * Real.exp 1 * (R * L) ^ 2 * (1 + 4 * (h / B) ^ 2)
        + 2 * (V * (2 * s + 2 * (h / B) + s * L + L / B)) ^ 2
        + 10 * Real.exp 1 * (4 * (MB * P1 / W ^ 2) + 10 * (MB * P2 / B)
          + 5 * (MB * (h / B)) + 6 * (MB / Q) + 2 * (MB * P3 / Q))
      ≤ 20 * Real.exp 1 * (R * L) ^ 2 * (1 + 4 * (h / sx) ^ 2)
        + 2 * (Vm * (2 * s + 2 * (h / sx) + s * (2 * P2) + 2 * P2 / sx)) ^ 2
        + 10 * Real.exp 1 * (4 * (MB * P1 / W ^ 2) + 10 * (MB * P2 / sx)
          + 5 * (MB * (h / sx)) + 6 * (MB / Q) + 2 * (MB * P3 / Q)) := by
  have hh0 : (0 : ℝ) < h := by linarith
  have hB0 : (0 : ℝ) < B := by linarith
  have hE0 : (0 : ℝ) ≤ 20 * Real.exp 1 := by positivity
  have hE10 : (0 : ℝ) ≤ 10 * Real.exp 1 := by positivity
  have hhq : h / B ≤ h / sx := div_le_div_of_nonneg_left hh0.le hsx hsxB
  have hhq0 : (0 : ℝ) ≤ h / B := div_nonneg hh0.le hB0.le
  have hLq : L / B ≤ 2 * P2 / sx := by
    have h1 : L / B ≤ L / sx := div_le_div_of_nonneg_left (by linarith) hsx hsxB
    have h2 : L / sx ≤ 2 * P2 / sx := div_le_div_of_nonneg_right hLpoly hsx.le
    linarith
  have hLq0 : (0 : ℝ) ≤ L / B := div_nonneg (by linarith) hB0.le
  have hsL : s * L ≤ s * (2 * P2) := mul_le_mul_of_nonneg_left hLpoly hs0
  -- the annulus group
  have ha : 20 * Real.exp 1 * (R * L) ^ 2 * (1 + 4 * (h / B) ^ 2)
      ≤ 20 * Real.exp 1 * (R * L) ^ 2 * (1 + 4 * (h / sx) ^ 2) := by
    refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hE0 (sq_nonneg _))
    have := pow_le_pow_left₀ hhq0 hhq 2
    linarith
  -- the disc group
  have hd : 2 * (V * (2 * s + 2 * (h / B) + s * L + L / B)) ^ 2
      ≤ 2 * (Vm * (2 * s + 2 * (h / sx) + s * (2 * P2) + 2 * P2 / sx)) ^ 2 := by
    have hin0 : (0 : ℝ) ≤ 2 * s + 2 * (h / B) + s * L + L / B := by
      have : (0 : ℝ) ≤ s * L := mul_nonneg hs0 (by linarith)
      linarith
    have hin : 2 * s + 2 * (h / B) + s * L + L / B
        ≤ 2 * s + 2 * (h / sx) + s * (2 * P2) + 2 * P2 / sx := by linarith
    have hV0 : (0 : ℝ) ≤ V * (2 * s + 2 * (h / B) + s * L + L / B) :=
      mul_nonneg (by linarith) hin0
    have hmul : V * (2 * s + 2 * (h / B) + s * L + L / B)
        ≤ Vm * (2 * s + 2 * (h / sx) + s * (2 * P2) + 2 * P2 / sx) :=
      mul_le_mul hVm hin hin0 (by linarith)
    have := pow_le_pow_left₀ hV0 hmul 2
    linarith
  -- the cofactor group
  have hc : 10 * Real.exp 1 * (4 * (MB * P1 / W ^ 2) + 10 * (MB * P2 / B)
        + 5 * (MB * (h / B)) + 6 * (MB / Q) + 2 * (MB * P3 / Q))
      ≤ 10 * Real.exp 1 * (4 * (MB * P1 / W ^ 2) + 10 * (MB * P2 / sx)
        + 5 * (MB * (h / sx)) + 6 * (MB / Q) + 2 * (MB * P3 / Q)) := by
    refine mul_le_mul_of_nonneg_left ?_ hE10
    have c1 : MB * P2 / B ≤ MB * P2 / sx :=
      div_le_div_of_nonneg_left (mul_nonneg hMB0 hP20) hsx hsxB
    have c2 : MB * (h / B) ≤ MB * (h / sx) := mul_le_mul_of_nonneg_left hhq hMB0
    linarith
  linarith [ha, hd, hc]

end

end RHTower.Sieve

namespace RHTower.Sieve

open Filter Topology

noncomputable section

/-- The inner factor of the disc majorant. -/
def discInner (β γ x : ℝ) : ℝ :=
  6 * ((Real.log x) ^ (13 / 2 : ℝ) * budgetS β x)
    + 6 * ((Real.log x) ^ (13 / 2 : ℝ) * (cardLength β x / Real.sqrt x))
    + 6 * ((Real.log x) ^ (13 / 2 + (2 * β + 5 / 4 - γ * β)) * budgetS β x)
    + 6 * ((Real.log x) ^ (13 / 2 + (2 * β + 5 / 4 - γ * β)) / Real.sqrt x)

/-- The explicit majorant of the normalised ladder constant. -/
def constMajorant (A delta Ctot β γ x : ℝ) : ℝ :=
  20 * Real.exp 1 * (budgetRhoBound A delta Ctot β γ x * ((ladderSteps β γ x : ℕ) : ℝ)) ^ 2
      * (1 + 4 * (cardLength β x / Real.sqrt x) ^ 2)
    + 2 * (discInner β γ x) ^ 2
    + 10 * Real.exp 1
        * (4 * ((Real.log x) ^ (-(1 / 4) : ℝ) / (mertensS (ladderTop β γ x) - mertensS (siftStart (γ * β) x)) ^ 2)
          + 10 * ((Real.log x) ^ (2 * β + 9 / 4 - 2 * (γ * β)) / Real.sqrt x)
          + 5 * ((Real.log x) ^ (1 - γ * β) * (cardLength β x / Real.sqrt x))
          + 6 * ((Real.log x) ^ (1 - γ * β) / ((siftStart (γ * β) x : ℕ) : ℝ))
          + 2 * ((Real.log x) ^ (β + 9 / 4 - 2 * (γ * β)) / ((siftStart (γ * β) x : ℕ) : ℝ)))

/-- The window length is negligible against the square root of the outer scale. -/
theorem tendsto_cardLength_div_sqrt {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    Tendsto (fun x : ℝ => cardLength β x / Real.sqrt x) atTop (𝓝 0) := by
  have := tendsto_rpow_log_mul_cardLength_div_sqrt hβ0 hβ1 0
  simpa using this

/-- **The inner disc factor vanishes.** -/
theorem tendsto_discInner {β γ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    Tendsto (fun x : ℝ => discInner β γ x) atTop (𝓝 0) := by
  have h1 := (tendsto_rpow_log_mul_budgetS (β := β) (c := (13 / 2 : ℝ)) hβ0 hβ1).const_mul
    (6 : ℝ)
  have h2 := (tendsto_rpow_log_mul_cardLength_div_sqrt hβ0 hβ1 (13 / 2 : ℝ)).const_mul (6 : ℝ)
  have h3 := (tendsto_rpow_log_mul_budgetS (β := β)
    (c := (13 / 2 + (2 * β + 5 / 4 - γ * β) : ℝ)) hβ0 hβ1).const_mul (6 : ℝ)
  have h4 := (tendsto_rpow_log_div_sqrt (13 / 2 + (2 * β + 5 / 4 - γ * β))).const_mul (6 : ℝ)
  have := ((h1.add h2).add h3).add h4
  simpa [discInner] using this

/-- **The majorant of the normalised ladder constant vanishes.** -/
theorem tendsto_constMajorant {A delta Ctot β γ : ℝ} (hβ0 : 9 / 10 < β) (hβ1 : β < 1)
    (hγ0 : 0 < γ) (hγ1 : γ < 1) (hγβ0 : 9 / 10 < γ * β) (hγβ1 : γ * β < 1) (hCtot : 0 ≤ Ctot)
    (hdelta : 0 < delta) :
    Tendsto (fun x : ℝ => constMajorant A delta Ctot β γ x) atTop (𝓝 0) := by
  have hβ0' : (0 : ℝ) < β := by linarith
  have hab : (0 : ℝ) < γ * β := by linarith
  have hsq : Tendsto (fun x : ℝ =>
      (budgetRhoBound A delta Ctot β γ x * ((ladderSteps β γ x : ℕ) : ℝ)) ^ 2) atTop (𝓝 0) := by
    have h := tendsto_budgetRho_mul_steps (A := A) (delta := delta) (Ctot := Ctot)
      hβ0 hβ1 hγ0 hγ1 hγβ0 hγβ1 hCtot hdelta
    simpa using h.pow 2
  have hone : Tendsto (fun x : ℝ => 1 + 4 * (cardLength β x / Real.sqrt x) ^ 2) atTop (𝓝 1) := by
    have h := ((tendsto_cardLength_div_sqrt hβ0' hβ1).pow 2).const_mul (4 : ℝ)
    have := (tendsto_const_nhds (x := (1 : ℝ)) (f := atTop)).add h
    simpa using this
  have hfirst : Tendsto (fun x : ℝ =>
      20 * Real.exp 1 * (budgetRhoBound A delta Ctot β γ x * ((ladderSteps β γ x : ℕ) : ℝ)) ^ 2
        * (1 + 4 * (cardLength β x / Real.sqrt x) ^ 2)) atTop (𝓝 0) := by
    have h := (hsq.const_mul (20 * Real.exp 1)).mul hone
    simpa using h
  have hdisc : Tendsto (fun x : ℝ => 2 * (discInner β γ x) ^ 2) atTop (𝓝 0) := by
    have h := ((tendsto_discInner (β := β) (γ := γ) hβ0' hβ1).pow 2).const_mul (2 : ℝ)
    simpa using h
  have hW : Tendsto (fun x : ℝ =>
      1 / (mertensS (ladderTop β γ x) - mertensS (siftStart (γ * β) x)) ^ 2) atTop (𝓝 0) := by
    have hmass := tendsto_ladderMass hβ0' hγ0 hγ1 hγβ1
    have hpow : Tendsto (fun x : ℝ =>
        (mertensS (ladderTop β γ x) - mertensS (siftStart (γ * β) x)) ^ 2) atTop atTop := by
      refine Filter.tendsto_atTop_mono' _ ?_ hmass
      filter_upwards [hmass.eventually_ge_atTop (1 : ℝ)] with x hx
      nlinarith [hx]
    exact hpow.const_div_atTop 1
  have hlogq : Tendsto (fun x : ℝ => (Real.log x) ^ (-(1 / 4) : ℝ)) atTop (𝓝 0) :=
    tendsto_rpow_log_of_neg (by norm_num)
  have hW' : Tendsto (fun x : ℝ =>
      (Real.log x) ^ (-(1 / 4) : ℝ)
        / (mertensS (ladderTop β γ x) - mertensS (siftStart (γ * β) x)) ^ 2) atTop (𝓝 0) := by
    have h := hlogq.mul hW
    simp only [mul_zero] at h
    refine h.congr fun x => ?_
    rw [mul_one_div]
  have hc1 := tendsto_rpow_log_div_sqrt (2 * β + 9 / 4 - 2 * (γ * β))
  have hc2 := tendsto_rpow_log_mul_cardLength_div_sqrt hβ0' hβ1 (1 - γ * β)
  have hc3 := tendsto_rpow_log_div_siftStart hab (1 - γ * β)
  have hc4 := tendsto_rpow_log_div_siftStart hab (β + 9 / 4 - 2 * (γ * β))
  have hcof : Tendsto (fun x : ℝ =>
      10 * Real.exp 1
        * (4 * ((Real.log x) ^ (-(1 / 4) : ℝ) / (mertensS (ladderTop β γ x) - mertensS (siftStart (γ * β) x)) ^ 2)
          + 10 * ((Real.log x) ^ (2 * β + 9 / 4 - 2 * (γ * β)) / Real.sqrt x)
          + 5 * ((Real.log x) ^ (1 - γ * β) * (cardLength β x / Real.sqrt x))
          + 6 * ((Real.log x) ^ (1 - γ * β) / ((siftStart (γ * β) x : ℕ) : ℝ))
          + 2 * ((Real.log x) ^ (β + 9 / 4 - 2 * (γ * β)) / ((siftStart (γ * β) x : ℕ) : ℝ))))
      atTop (𝓝 0) := by
    have hsum := ((((hW'.const_mul (4:ℝ)).add (hc1.const_mul (10:ℝ))).add
      (hc2.const_mul (5:ℝ))).add (hc3.const_mul (6:ℝ))).add (hc4.const_mul (2:ℝ))
    have := hsum.const_mul (10 * Real.exp 1)
    simpa using this
  have := (hfirst.add hdisc).add hcof
  simpa [constMajorant] using this

end

end RHTower.Sieve

namespace RHTower.Sieve

open Filter Topology

noncomputable section

/-- The annulus radius of the ladder is polynomially bounded. -/
theorem annulusStart_sqrt_le {β x : ℝ} (ht1 : 1 ≤ Real.log x) :
    Real.sqrt (2 * annulusStart β x) + 1 ≤ 3 * (Real.log x) ^ (13 / 2 : ℝ) := by
  have hlogx : (0 : ℝ) < Real.log x := by linarith
  have hP : (1 : ℝ) ≤ (Real.log x) ^ (13 / 2 : ℝ) := by
    rw [show (1:ℝ) = (Real.log x) ^ (0:ℝ) by rw [Real.rpow_zero]]
    exact Real.rpow_le_rpow_of_exponent_le ht1 (by norm_num)
  have hP0 : (0 : ℝ) ≤ (Real.log x) ^ (13 / 2 : ℝ) := by linarith
  have h13 : (0 : ℝ) ≤ (Real.log x) ^ (13 : ℝ) := Real.rpow_nonneg hlogx.le _
  have hval : (2 * (Real.log x) ^ (13 / 2 : ℝ)) ^ 2 = 4 * (Real.log x) ^ (13 : ℝ) := by
    rw [mul_pow, ← Real.rpow_natCast ((Real.log x) ^ (13 / 2 : ℝ)) 2, ← Real.rpow_mul hlogx.le]
    norm_num
  have hsq : 2 * (Real.log x) ^ (13 : ℝ) ≤ (2 * (Real.log x) ^ (13 / 2 : ℝ)) ^ 2 := by
    linarith [hval, h13]
  have hstep := Real.sqrt_le_sqrt hsq
  rw [Real.sqrt_sq (by linarith)] at hstep
  rw [annulusStart]
  linarith [hstep, hP]

set_option maxHeartbeats 2000000 in
/-- **The normalised ladder constant is below its majorant.** -/
theorem eventually_const_quotient_le {A delta Ctot β γ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hγ0 : 0 < γ) (hγ1 : γ < 1) (hγβ : γ * β < 1) (hCtot : 0 ≤ Ctot) :
    ∀ᶠ x : ℝ in atTop,
      ladderAffineConst (siftStart (γ * β) x) (ladderTop β γ x) (ladderSteps β γ x)
          (budgetB β x) ((siftStart (γ * β) x : ℕ) : ℝ) (ladderEta β γ x)
          (budgetRho A delta Ctot β γ x) (budgetS β x) (annulusStart β x)
        / (((budgetB β x : ℕ) : ℝ) ^ 2
          * (mertensS (ladderTop β γ x) - mertensS (siftStart (γ * β) x)) ^ 2)
      ≤ constMajorant A delta Ctot β γ x := by
  have hab : (0 : ℝ) < γ * β := mul_pos hγ0 hβ0
  have hzero := tendsto_ladderEta (β := β) (γ := γ) hβ0 hγβ
  filter_upwards [Filter.eventually_gt_atTop (1 : ℝ), eventually_le_siftStart hab 2,
    Tendsto.eventually_le_const (by norm_num : (0:ℝ) < 1) hzero,
    one_le_ladderSteps hβ0 hγ0 hγ1 hγβ, eventually_siftStart_lt_cardLength hβ0 hγ0 hγ1,
    (tendsto_cardLength hβ0).eventually_ge_atTop (1 : ℝ),
    (tendsto_ladderMass hβ0 hγ0 hγ1 hγβ).eventually_ge_atTop (1 : ℝ),
    eventually_budgetRho_nonneg (A := A) (delta := delta) (Ctot := Ctot) (γ := γ) hβ0 hCtot,
    eventually_budgetRho_le (A := A) (delta := delta) (Ctot := Ctot) (γ := γ) hβ0 hβ1 hγ0 hCtot,
    eventually_inv_eta_le_steps hβ0 hγ0 hγ1 hγβ,
    eventually_cofactor_ratio_le (β := β) (γ := γ) hβ0 hβ1 hγ0 hγβ,
    eventually_steps_eta_sq_le hβ0 hγ0 hγ1 hγβ,
    eventually_ladderSteps_poly hβ0 hγ0 hγ1 hγβ,
    eventually_ladderTop_facts hβ0 hγ0 hγ1 hγβ,
    eventually_gallagherCut_ge_exp hβ0 hβ1,
    Real.tendsto_log_atTop.eventually_ge_atTop (1 : ℝ)]
    with x hx1 hQ2 hη1 hL1 h2Q hh1 hW hρ0 hρR hinvη hM hLη hLpoly hfacts hNmin ht1
  obtain ⟨hz2, hzh, hz₀z⟩ := hfacts
  have hlogx : (0 : ℝ) < Real.log x := Real.log_pos hx1
  have hη : 0 < ladderEta β γ x := ladderEta_pos hx1
  have hQ2R : (2 : ℝ) ≤ ((siftStart (γ * β) x : ℕ) : ℝ) := by exact_mod_cast hQ2
  have hQ1 : (1 : ℝ) < ((siftStart (γ * β) x : ℕ) : ℝ) := by linarith
  have hQ0 : (0 : ℝ) < ((siftStart (γ * β) x : ℕ) : ℝ) := by linarith
  have hQh : ((siftStart (γ * β) x : ℕ) : ℝ) ≤ cardLength β x := by linarith
  have hle := ladderPow_le (β := β) (γ := γ) (x := x) (by linarith) hQh hη
  have hL1R : (1 : ℝ) ≤ ((ladderSteps β γ x : ℕ) : ℝ) := by exact_mod_cast hL1
  have hBsx : Real.sqrt x ≤ ((budgetB β x : ℕ) : ℝ) := sqrt_le_budgetB (β := β) x hh1
  have hsx : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.2 (by linarith)
  have hsx1 : (1 : ℝ) ≤ Real.sqrt x := by
    rw [show (1:ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (by linarith)
  have hB1 : (1 : ℝ) ≤ ((budgetB β x : ℕ) : ℝ) := by linarith
  have hB0 : (0 : ℝ) < ((budgetB β x : ℕ) : ℝ) := by linarith
  have hh0 : (0 : ℝ) < cardLength β x := by linarith
  have hs0 : (0 : ℝ) ≤ budgetS β x := by
    rw [budgetS]
    refine relMoebiusSharp_nonneg ?_
    have : (1 : ℝ) ≤ Real.exp (Real.log x / 5) := Real.one_le_exp (by positivity)
    linarith [hNmin, this]
  have hP := primesRange_ladder_bounds (z₀ := siftStart (γ * β) x) (z := ladderTop β γ x)
    (L := ladderSteps β γ x) (Q := ((siftStart (γ * β) x : ℕ) : ℝ))
    (η := ladderEta β γ x) rfl hη.le hQ0.le rfl
  have hconst := ladderAffineConst_le (z₀ := siftStart (γ * β) x) (z := ladderTop β γ x)
    (B₀ := budgetB β x) (Q := ((siftStart (γ * β) x : ℕ) : ℝ)) (η := ladderEta β γ x)
    (hR := cardLength β x) (ρ := budgetRho A delta Ctot β γ x) (s := budgetS β x)
    (w₀ := annulusStart β x) hQ1 hη hη1 (L := ladderSteps β γ x) hle hL1 hs0 hP
  -- the auxiliary quantities
  have hWsum : (∑ p ∈ primesRange (siftStart (γ * β) x) (ladderTop β γ x), 1 / (p : ℝ))
      = mertensS (ladderTop β γ x) - mertensS (siftStart (γ * β) x) :=
    sum_inv_primesRange hz₀z
  have hNP0 : (0 : ℝ)
      ≤ ((primesRange (siftStart (γ * β) x) (ladderTop β γ x)).card : ℝ) := Nat.cast_nonneg _
  have hNP : ((primesRange (siftStart (γ * β) x) (ladderTop β γ x)).card : ℝ)
      ≤ 2 * cardLength β x := by
    have h1 := card_primesRange_le (siftStart (γ * β) x) (ladderTop β γ x)
    linarith [h1, hzh, hh1]
  have hSN0 : (0 : ℝ) ≤ ∑ j ∈ Finset.range (ladderSteps β γ x),
      ((budgetB β x : ℕ) : ℝ) / (((siftStart (γ * β) x : ℕ) : ℝ) * (1 + ladderEta β γ x) ^ j) :=
    Finset.sum_nonneg fun j _ => by
      have : (0 : ℝ) < (1 + ladderEta β γ x) ^ j := pow_pos (by linarith) j
      exact div_nonneg hB0.le (by positivity)
  have hSN : (∑ j ∈ Finset.range (ladderSteps β γ x),
        ((budgetB β x : ℕ) : ℝ)
          / (((siftStart (γ * β) x : ℕ) : ℝ) * (1 + ladderEta β γ x) ^ j))
      ≤ ((ladderSteps β γ x : ℕ) : ℝ) * ((budgetB β x : ℕ) : ℝ)
        / ((siftStart (γ * β) x : ℕ) : ℝ) := by
    have hterm : ∀ j ∈ Finset.range (ladderSteps β γ x),
        ((budgetB β x : ℕ) : ℝ)
            / (((siftStart (γ * β) x : ℕ) : ℝ) * (1 + ladderEta β γ x) ^ j)
          ≤ ((budgetB β x : ℕ) : ℝ) / ((siftStart (γ * β) x : ℕ) : ℝ) := by
      intro j _
      refine div_le_div_of_nonneg_left hB0.le hQ0 ?_
      have hp : (1 : ℝ) ≤ (1 + ladderEta β γ x) ^ j := one_le_pow₀ (by linarith)
      have := mul_le_mul_of_nonneg_left hp hQ0.le
      linarith [this]
    calc (∑ j ∈ Finset.range (ladderSteps β γ x),
            ((budgetB β x : ℕ) : ℝ)
              / (((siftStart (γ * β) x : ℕ) : ℝ) * (1 + ladderEta β γ x) ^ j))
        ≤ ∑ _j ∈ Finset.range (ladderSteps β γ x),
            ((budgetB β x : ℕ) : ℝ) / ((siftStart (γ * β) x : ℕ) : ℝ) :=
          Finset.sum_le_sum hterm
      _ = ((ladderSteps β γ x : ℕ) : ℝ)
            * (((budgetB β x : ℕ) : ℝ) / ((siftStart (γ * β) x : ℕ) : ℝ)) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ = ((ladderSteps β γ x : ℕ) : ℝ) * ((budgetB β x : ℕ) : ℝ)
            / ((siftStart (γ * β) x : ℕ) : ℝ) := by ring
  have hB'0 : (0 : ℝ)
      ≤ ((⌊((budgetB β x : ℕ) : ℝ) * (1 + ladderEta β γ x)⌋₊ : ℕ) : ℝ) := Nat.cast_nonneg _
  have hge1 : (1 : ℝ) ≤ ((budgetB β x : ℕ) : ℝ) * (1 + ladderEta β γ x) := by
    have h := mul_le_mul_of_nonneg_left
      (by linarith : (1:ℝ) ≤ 1 + ladderEta β γ x) hB0.le
    linarith [h, hB1]
  have hle2 : ((budgetB β x : ℕ) : ℝ) * (1 + ladderEta β γ x)
      ≤ 2 * ((budgetB β x : ℕ) : ℝ) := by
    have h := mul_le_mul_of_nonneg_left
      (by linarith : (1 : ℝ) + ladderEta β γ x ≤ 2) hB0.le
    linarith [h]
  have hB' : ((⌊((budgetB β x : ℕ) : ℝ) * (1 + ladderEta β γ x)⌋₊ : ℕ) : ℝ)
      ≤ 2 * ((budgetB β x : ℕ) : ℝ) := by
    have hfl := Nat.floor_le (by linarith : (0:ℝ) ≤ ((budgetB β x : ℕ) : ℝ)
      * (1 + ladderEta β γ x))
    linarith [hfl, hle2]
  have hM0 : (0 : ℝ) ≤ Real.log ((⌊((budgetB β x : ℕ) : ℝ) * (1 + ladderEta β γ x)⌋₊ : ℕ) : ℝ)
      / Real.log ((siftStart (γ * β) x : ℕ) : ℝ) := by
    refine div_nonneg (Real.log_nonneg ?_) (Real.log_nonneg (by linarith))
    have h1 : (1 : ℕ) ≤ ⌊((budgetB β x : ℕ) : ℝ) * (1 + ladderEta β γ x)⌋₊ :=
      Nat.one_le_floor_iff _ |>.2 hge1
    exact_mod_cast h1
  have hden : (0 : ℝ) < ((budgetB β x : ℕ) : ℝ) ^ 2
      * (mertensS (ladderTop β γ x) - mertensS (siftStart (γ * β) x)) ^ 2 :=
    mul_pos (pow_pos hB0 2) (by nlinarith [hW])

  rw [hWsum] at hconst
  refine (div_le_div_of_nonneg_right hconst hden.le).trans ?_
  have harith := const_quotient_arith
    (L := ((ladderSteps β γ x : ℕ) : ℝ)) (B := ((budgetB β x : ℕ) : ℝ))
    (Q := ((siftStart (γ * β) x : ℕ) : ℝ)) (η := ladderEta β γ x)
    (ρ := budgetRho A delta Ctot β γ x) (R := budgetRhoBound A delta Ctot β γ x)
    (h := cardLength β x)
    (W := mertensS (ladderTop β γ x) - mertensS (siftStart (γ * β) x))
    (M := Real.log ((⌊((budgetB β x : ℕ) : ℝ) * (1 + ladderEta β γ x)⌋₊ : ℕ) : ℝ)
      / Real.log ((siftStart (γ * β) x : ℕ) : ℝ))
    (MB := (Real.log x) ^ (1 - γ * β)) (P1 := (Real.log x) ^ (γ * β - 5 / 4))
    (P2 := (Real.log x) ^ (2 * β + 5 / 4 - γ * β)) (P3 := (Real.log x) ^ (β + 5 / 4 - γ * β))
    (B' := ((⌊((budgetB β x : ℕ) : ℝ) * (1 + ladderEta β γ x)⌋₊ : ℕ) : ℝ))
    (V := Real.sqrt (2 * annulusStart β x) + 1) (s := budgetS β x)
    hQ1 hη hη1 hL1R hB1 hh1 hW hρ0 hρR hinvη hM0 hM (Real.rpow_nonneg hlogx.le _)
    hLη hLpoly (le_of_eq (inv_ladderEta_eq (β := β) (γ := γ) hx1)) hB'
    (by linarith [Real.sqrt_nonneg (2 * annulusStart β x)]) hs0
    (Real.rpow_nonneg hlogx.le _) (Real.rpow_nonneg hlogx.le _) hNP0 hNP hSN0 hSN rfl
  refine harith.trans ?_
  have hmono := const_bound_mono
    (L := ((ladderSteps β γ x : ℕ) : ℝ)) (B := ((budgetB β x : ℕ) : ℝ))
    (Q := ((siftStart (γ * β) x : ℕ) : ℝ)) (h := cardLength β x)
    (W := mertensS (ladderTop β γ x) - mertensS (siftStart (γ * β) x))
    (V := Real.sqrt (2 * annulusStart β x) + 1) (s := budgetS β x)
    (R := budgetRhoBound A delta Ctot β γ x)
    (MB := (Real.log x) ^ (1 - γ * β)) (P1 := (Real.log x) ^ (γ * β - 5 / 4))
    (P2 := (Real.log x) ^ (2 * β + 5 / 4 - γ * β)) (P3 := (Real.log x) ^ (β + 5 / 4 - γ * β))
    (sx := Real.sqrt x) (Vm := 3 * (Real.log x) ^ (13 / 2 : ℝ))
    hB1 hh1 hsx hBsx hs0 hL1R
    (by linarith [Real.sqrt_nonneg (2 * annulusStart β x)])
    (annulusStart_sqrt_le (β := β) ht1) (Real.rpow_nonneg hlogx.le _)
    (Real.rpow_nonneg hlogx.le _) hLpoly
  refine hmono.trans (le_of_eq ?_)
  have e1 : (Real.log x) ^ (1 - γ * β) * (Real.log x) ^ (γ * β - 5 / 4)
      = (Real.log x) ^ (-(1 / 4) : ℝ) := by
    rw [← Real.rpow_add hlogx]
    congr 1
    ring
  have e2 : (Real.log x) ^ (1 - γ * β) * (Real.log x) ^ (2 * β + 5 / 4 - γ * β)
      = (Real.log x) ^ (2 * β + 9 / 4 - 2 * (γ * β)) := by
    rw [← Real.rpow_add hlogx]
    congr 1
    ring
  have e3 : (Real.log x) ^ (1 - γ * β) * (Real.log x) ^ (β + 5 / 4 - γ * β)
      = (Real.log x) ^ (β + 9 / 4 - 2 * (γ * β)) := by
    rw [← Real.rpow_add hlogx]
    congr 1
    ring
  have e4 : (3 : ℝ) * (Real.log x) ^ (13 / 2 : ℝ)
        * (2 * budgetS β x + 2 * (cardLength β x / Real.sqrt x)
          + budgetS β x * (2 * (Real.log x) ^ (2 * β + 5 / 4 - γ * β))
          + 2 * (Real.log x) ^ (2 * β + 5 / 4 - γ * β) / Real.sqrt x)
      = discInner β γ x := by
    have e5 : (Real.log x) ^ (13 / 2 : ℝ) * (Real.log x) ^ (2 * β + 5 / 4 - γ * β)
        = (Real.log x) ^ (13 / 2 + (2 * β + 5 / 4 - γ * β)) := by
      rw [← Real.rpow_add hlogx]
    rw [discInner, ← e5]
    ring
  rw [constMajorant, ← e4, e1, e2, e3]

end

end RHTower.Sieve

namespace RHTower.Sieve

open Filter Topology

noncomputable section

/-- **The normalised ladder constant vanishes.** -/
theorem tendsto_const_quotient {A delta Ctot β γ : ℝ} (hβ0 : 9 / 10 < β) (hβ1 : β < 1)
    (hγ0 : 0 < γ) (hγ1 : γ < 1) (hγβ0 : 9 / 10 < γ * β) (hγβ1 : γ * β < 1) (hCtot : 0 ≤ Ctot)
    (hdelta : 0 < delta) :
    Tendsto (fun x : ℝ =>
        ladderAffineConst (siftStart (γ * β) x) (ladderTop β γ x) (ladderSteps β γ x)
            (budgetB β x) ((siftStart (γ * β) x : ℕ) : ℝ) (ladderEta β γ x)
            (budgetRho A delta Ctot β γ x) (budgetS β x) (annulusStart β x)
          / (((budgetB β x : ℕ) : ℝ) ^ 2
            * (mertensS (ladderTop β γ x) - mertensS (siftStart (γ * β) x)) ^ 2))
      atTop (𝓝 0) := by
  have hβ0' : (0 : ℝ) < β := by linarith
  have hab : (0 : ℝ) < γ * β := by linarith
  refine squeeze_zero' ?_ (eventually_const_quotient_le hβ0' hβ1 hγ0 hγ1 hγβ1 hCtot)
    (tendsto_constMajorant hβ0 hβ1 hγ0 hγ1 hγβ0 hγβ1 hCtot hdelta)
  filter_upwards [Filter.eventually_gt_atTop (1 : ℝ), eventually_le_siftStart hab 2,
    (tendsto_cardLength hβ0').eventually_ge_atTop (1 : ℝ)] with x hx1 hQ2 hh1
  have hη : 0 < ladderEta β γ x := ladderEta_pos hx1
  have hQ2R : (2 : ℝ) ≤ ((siftStart (γ * β) x : ℕ) : ℝ) := by exact_mod_cast hQ2
  have hnum : (0 : ℝ) ≤ ladderAffineConst (siftStart (γ * β) x) (ladderTop β γ x)
      (ladderSteps β γ x) (budgetB β x) ((siftStart (γ * β) x : ℕ) : ℝ) (ladderEta β γ x)
      (budgetRho A delta Ctot β γ x) (budgetS β x) (annulusStart β x) :=
    ladderAffineConst_nonneg (by linarith) hη.le
  have hBsx : Real.sqrt x ≤ ((budgetB β x : ℕ) : ℝ) := sqrt_le_budgetB (β := β) x hh1
  have hsx : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.2 (by linarith)
  have hB0 : (0 : ℝ) < ((budgetB β x : ℕ) : ℝ) := by linarith
  exact div_nonneg hnum (by positivity)

end

end RHTower.Sieve
