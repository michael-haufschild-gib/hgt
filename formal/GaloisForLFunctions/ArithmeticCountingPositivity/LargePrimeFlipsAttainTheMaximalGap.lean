import GaloisForLFunctions.ArithmeticCountingPositivity.NearMaximalGapsDoNotForceWeilPositivity
import GaloisForLFunctions.SelectiveMultiscaleArithmeticPositivity.TheSelectiveMarginIsTwoLogTwo

/-!
# Large prime flips attain the maximal gap

No sign gauge has a pole-hyperplane gap above `2 log 2`, the gap of `ζ`
(`isGreatest_signGauge_hyperplaneGap`). This module shows that the maximal gap is **not
rigid**: for every prime `p ≥ 11` the single-prime flip `ω_p(n) = (−1)^{v_p(n)}` has
hyperplane gap exactly `2 log 2` (`primeFlip_hasHyperplaneGap_two_mul_log_two`,
`isGreatest_primeFlip_hyperplaneGap`).

The mechanism is the twisted Poincaré inequality `D_N(z) ≥ (2 log 2 − η)|z|²` on the
hyperplane orthogonal to the flipped pole `ω_p(n)/√n` (`eventually_primeFlip_poleDefect_ge`).
In the two-scale decomposition of `[1, N]` into `Q`-smooth parts and rough fibres, the flipped
pole differs from the pole only inside the `p`-ladders of the smooth box. Efron–Stein on the box,
keeping the `p`-ladders separate, pays the within-`p`-fibre variance with the ladder constant
`log p · W_p(X) ≥ log p (1 + 1/p)` instead of `2 log 2` (`boxGap_mul_boxVar_add_le`); the flipped
pole's pairing with a mean-zero function is controlled by that variance
(`sum_flip_mul_sq_le`). The rotation of the pole costs `(1 − c_p²)/c_p²` of the excess, with
`c_p = (p − 1)/(p + 1)` the harmonic correlation floor of the parity count; the inequality
`4p · 2 log 2 < (p − 1)²(log p − 2 log 2)` holds from `p = 11` on (`numeric_condition`).

Consequence: a completely multiplicative sign twin of `Λ` with the untwisted polar matching,
the maximal selective margin, every Weil coefficient of the same size as `Λ`, and a negative
complete Weil test (`maximal_gap_does_not_select_the_source`). The discrete margin, even at its
maximum, does not select `ζ`.
-/

noncomputable section

open Finset Filter Topology

namespace GaloisForLFunctions.ArithmeticCountingPositivity

open GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
  GaloisForLFunctions.SelectiveMultiscaleArithmeticPositivity
  GaloisForLFunctions.ArithmeticElectrostatics

open _root_.RHTower _root_.RHTower.WeilSpectral _root_.Zeta23

/-! ### 1. Arithmetic of the assembly -/

/-- `(a + b)² ≤ (21/20) a² + 21 b²`. -/
theorem add_sq_le_twenty (a b : ℝ) : (a + b) ^ 2 ≤ 21 / 20 * a ^ 2 + 21 * b ^ 2 := by
  nlinarith [sq_nonneg (a - 20 * b)]

/-- `log x ≥ 2.35` for `x ≥ 11`: `log 11 = 3 log 2 + log (11/8) ≥ 3 log 2 + 3/11`. -/
theorem log_ge_of_eleven_le {x : ℝ} (hx : 11 ≤ x) : 2.35 ≤ Real.log x := by
  have hl2 := Real.log_two_gt_d9
  have h11 : Real.log ((2 : ℝ) ^ 3 * (11 / 8)) = 3 * Real.log 2 + Real.log (11 / 8) := by
    rw [Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    push_cast; ring
  have h11' : (2 : ℝ) ^ 3 * (11 / 8) = 11 := by norm_num
  rw [h11'] at h11
  have h118 : 1 - (11 / 8 : ℝ)⁻¹ ≤ Real.log (11 / 8) := Real.one_sub_inv_le_log_of_pos (by norm_num)
  have hmono : Real.log 11 ≤ Real.log x := Real.log_le_log (by norm_num) hx
  rw [h11] at hmono
  norm_num at h118
  linarith

/-- The numeric condition of the maximal-gap theorem: for `p ≥ 11`, `ℓ ≥ 2.35` and
`lam < 1.3863`, `4p · lam · (21/20)³ ≤ (15/16)(p − 1)²(ℓ − lam)`. -/
theorem numeric_condition {p ℓ lam : ℝ} (hp : 11 ≤ p) (hℓ : 2.35 ≤ ℓ) (hlam : lam < 1.3863) :
    4 * p * lam * (21 / 20) ^ 3 ≤ 15 / 16 * (p - 1) ^ 2 * (ℓ - lam) := by
  have hp0 : 0 ≤ p := by linarith
  have hA : 4 * p * lam * (21 / 20) ^ 3 ≤ 6.42 * p := by
    have : 0 ≤ p * (1.3863 - lam) := mul_nonneg hp0 (by linarith)
    nlinarith
  have hB : 0.9637 ≤ ℓ - lam := by linarith
  have hC : 7.2 * p ≤ (p - 1) ^ 2 := by
    have : 0 ≤ (p - 11) * p := mul_nonneg (by linarith) hp0
    nlinarith
  have hD : 15 / 16 * (p - 1) ^ 2 * 0.9637 ≤ 15 / 16 * (p - 1) ^ 2 * (ℓ - lam) :=
    mul_le_mul_of_nonneg_left hB (by positivity)
  have hE : 15 / 16 * (7.2 * p) * 0.9637 ≤ 15 / 16 * (p - 1) ^ 2 * 0.9637 := by
    have := mul_le_mul_of_nonneg_left hC (show (0 : ℝ) ≤ 15 / 16 by norm_num)
    nlinarith
  nlinarith

/-- Facts about `c_p = (p − 1)/(p + 1)` for `p ≥ 11`. -/
theorem cp_facts {p cp : ℝ} (hp : 11 ≤ p) (hcp : cp = (p - 1) / (p + 1)) :
    5 / 6 ≤ cp ∧ cp ≤ 1 ∧ (1 - cp ^ 2) * (p + 1) ^ 2 = 4 * p ∧
      cp ^ 2 * (p + 1) ^ 2 = (p - 1) ^ 2 := by
  have hp1 : 0 < p + 1 := by linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hcp, le_div_iff₀ hp1]; linarith
  · rw [hcp, div_le_one hp1]; linarith
  · rw [hcp]; field_simp; ring
  · rw [hcp]; field_simp

/-- The main term: the rotation of the flipped pole is paid by the `p`-ladder excess. -/
theorem main_term_le {lam η p ℓ cp lM bG G Vp e₂ : ℝ}
    (hlam1 : 1.386 < lam) (hlam2 : lam < 1.3863) (hη1 : η ≤ 1)
    (hp : 11 ≤ p) (hℓ : 2.35 ≤ ℓ) (hcp : cp = (p - 1) / (p + 1))
    (hlM : 1 ≤ lM) (hbG : bG ≤ lam) (hGVp : 0 ≤ G * Vp) (he₂0 : 0 ≤ e₂) (he₂ : e₂ ≤ 1 / 20) :
    lam * ((21 / 20) ^ 2 * (1 - cp ^ 2) * lM * (G * Vp)) ≤
      (1 - η / 16) * cp ^ 2 * (G * ((ℓ * lM - bG) * Vp / (1 + e₂))) := by
  obtain ⟨hcp_ge, hcp_le, hone_sub, hcp2'⟩ := cp_facts hp hcp
  have hcp_pos : 0 < cp := by linarith
  have hc0 : 0 ≤ 1 - cp ^ 2 := by nlinarith
  have hnum := numeric_condition hp hℓ hlam2
  have hbG' : lM * (ℓ - lam) ≤ ℓ * lM - bG := by nlinarith
  have hscalar : lam * (21 / 20) ^ 2 * (1 - cp ^ 2) * (21 / 20) ≤
      (1 - η / 16) * cp ^ 2 * (ℓ - lam) := by
    have hp1' : 0 < (p + 1) ^ 2 := by positivity
    have h15 : 15 / 16 ≤ 1 - η / 16 := by linarith
    have hℓl : 0 ≤ ℓ - lam := by linarith
    have key : lam * (21 / 20) ^ 2 * (1 - cp ^ 2) * (21 / 20) * (p + 1) ^ 2 ≤
        (1 - η / 16) * cp ^ 2 * (ℓ - lam) * (p + 1) ^ 2 := by
      calc lam * (21 / 20) ^ 2 * (1 - cp ^ 2) * (21 / 20) * (p + 1) ^ 2
          = 4 * p * lam * (21 / 20) ^ 3 := by rw [← hone_sub]; ring
        _ ≤ 15 / 16 * (p - 1) ^ 2 * (ℓ - lam) := hnum
        _ = 15 / 16 * (cp ^ 2 * (p + 1) ^ 2) * (ℓ - lam) := by rw [hcp2']
        _ ≤ (1 - η / 16) * cp ^ 2 * (ℓ - lam) * (p + 1) ^ 2 := by
            have h0 : 0 ≤ cp ^ 2 * (p + 1) ^ 2 * (ℓ - lam) := by positivity
            have := mul_le_mul_of_nonneg_right h15 h0
            linarith
    exact le_of_mul_le_mul_right key hp1'
  have h1e : 0 < 1 + e₂ := by linarith
  have hlhs : lam * ((21 / 20) ^ 2 * (1 - cp ^ 2) * lM * (G * Vp)) * (1 + e₂) ≤
      lam * (21 / 20) ^ 2 * (1 - cp ^ 2) * (21 / 20) * (lM * (G * Vp)) := by
    have h0 : 0 ≤ lam * (21 / 20) ^ 2 * (1 - cp ^ 2) * (lM * (G * Vp)) := by positivity
    have := mul_le_mul_of_nonneg_left he₂ h0
    linarith
  have hrhs : (1 - η / 16) * cp ^ 2 * (ℓ - lam) * (lM * (G * Vp)) ≤
      (1 - η / 16) * cp ^ 2 * (G * ((ℓ * lM - bG) * Vp)) := by
    have h0 : 0 ≤ (1 - η / 16) * cp ^ 2 := by
      have : 0 ≤ 1 - η / 16 := by linarith
      positivity
    have := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hbG' hGVp) h0
    linarith
  have hmul := mul_le_mul_of_nonneg_right hscalar (show 0 ≤ lM * (G * Vp) by positivity)
  have hdiv : (1 - η / 16) * cp ^ 2 * (G * ((ℓ * lM - bG) * Vp / (1 + e₂))) =
      (1 - η / 16) * cp ^ 2 * (G * ((ℓ * lM - bG) * Vp)) / (1 + e₂) := by ring
  rw [hdiv, le_div_iff₀ h1e]
  linarith

/-- The second moment of the harmonic mean: constraint, splittings and Cauchy–Schwarz. -/
theorem moment_bound {p cp G H P Y c S A B Av Ah Bv Bh ZX lM Vp Err : ℝ}
    (hp : 11 ≤ p) (hcp : cp = (p - 1) / (p + 1)) (hG : 0 < G) (hH : 0 < H) (hVp : 0 ≤ Vp)
    (hlM : 1 ≤ lM) (hErr0 : 0 ≤ Err)
    (h3 : Y = c * H + B) (h4 : c * S = -A) (hS : cp * H ≤ S)
    (h5A : A = G * P + Av + Ah) (h5B : B = Bv + Bh)
    (hAerr : Av ^ 2 + Ah ^ 2 ≤ H * Err) (hBerr : Bv ^ 2 + Bh ^ 2 ≤ H * Err)
    (hP : P ^ 2 ≤ (1 - cp ^ 2) * lM * ZX * Vp) (hGZ : G * ZX ≤ H) :
    cp ^ 2 * Y ^ 2 ≤
      (21 / 20) ^ 2 * (1 - cp ^ 2) * lM * (G * Vp) * H + 150 * cp ^ 2 * (H * Err) := by
  obtain ⟨hcp_ge, hcp_le, -, -⟩ := cp_facts hp hcp
  have hcp_pos : 0 < cp := by linarith
  have hcp0 : 0 ≤ cp ^ 2 := sq_nonneg cp
  have hcp2 : 25 / 36 ≤ cp ^ 2 := by nlinarith
  have hc0 : 0 ≤ 1 - cp ^ 2 := by nlinarith
  have hi : Y ^ 2 ≤ 21 / 20 * (c * H) ^ 2 + 21 * B ^ 2 := by
    rw [h3]; exact add_sq_le_twenty _ _
  have hii : cp ^ 2 * (c * H) ^ 2 ≤ A ^ 2 := by
    have hA : (c * S) ^ 2 = A ^ 2 := by rw [h4]; ring
    have hS0 : 0 ≤ cp * H := by positivity
    have hS2 : (cp * H) ^ 2 ≤ S ^ 2 := pow_le_pow_left₀ hS0 hS 2
    calc cp ^ 2 * (c * H) ^ 2 = c ^ 2 * (cp * H) ^ 2 := by ring
      _ ≤ c ^ 2 * S ^ 2 := mul_le_mul_of_nonneg_left hS2 (sq_nonneg c)
      _ = (c * S) ^ 2 := by ring
      _ = A ^ 2 := hA
  have hiii : A ^ 2 ≤ 21 / 20 * (G * P) ^ 2 + 42 * (Av ^ 2 + Ah ^ 2) := by
    rw [h5A, add_assoc]
    have h := add_sq_le_twenty (G * P) (Av + Ah)
    have h' : (Av + Ah) ^ 2 ≤ 2 * (Av ^ 2 + Ah ^ 2) := by nlinarith [sq_nonneg (Av - Ah)]
    linarith
  have hiiiB : B ^ 2 ≤ 2 * (Bv ^ 2 + Bh ^ 2) := by
    rw [h5B]; nlinarith [sq_nonneg (Bv - Bh)]
  have hiv : (G * P) ^ 2 ≤ (1 - cp ^ 2) * lM * (G * Vp) * H := by
    have hpos : 0 ≤ (1 - cp ^ 2) * lM * (G * Vp) := by positivity
    calc (G * P) ^ 2 = G ^ 2 * P ^ 2 := by ring
      _ ≤ G ^ 2 * ((1 - cp ^ 2) * lM * ZX * Vp) :=
          mul_le_mul_of_nonneg_left hP (sq_nonneg G)
      _ = (1 - cp ^ 2) * lM * (G * Vp) * (G * ZX) := by ring
      _ ≤ (1 - cp ^ 2) * lM * (G * Vp) * H := mul_le_mul_of_nonneg_left hGZ hpos
  have e1 : cp ^ 2 * Y ^ 2 ≤ 21 / 20 * (cp ^ 2 * (c * H) ^ 2) + 21 * (cp ^ 2 * B ^ 2) := by
    have := mul_le_mul_of_nonneg_left hi hcp0
    linarith
  have e2 : 21 / 20 * (cp ^ 2 * (c * H) ^ 2) ≤ 21 / 20 * A ^ 2 :=
    mul_le_mul_of_nonneg_left hii (by norm_num)
  have e3 : 21 / 20 * A ^ 2 ≤
      (21 / 20) ^ 2 * (G * P) ^ 2 + 21 / 20 * 42 * (Av ^ 2 + Ah ^ 2) := by
    have := mul_le_mul_of_nonneg_left hiii (show (0 : ℝ) ≤ 21 / 20 by norm_num)
    linarith
  have e4 : (21 / 20) ^ 2 * (G * P) ^ 2 ≤ (21 / 20) ^ 2 * ((1 - cp ^ 2) * lM * (G * Vp) * H) :=
    mul_le_mul_of_nonneg_left hiv (by norm_num)
  have e5 : 21 / 20 * 42 * (Av ^ 2 + Ah ^ 2) ≤ 21 / 20 * 42 * (H * Err) :=
    mul_le_mul_of_nonneg_left hAerr (by norm_num)
  have e6 : 21 * (cp ^ 2 * B ^ 2) ≤ 42 * cp ^ 2 * (H * Err) := by
    have h1' := mul_le_mul_of_nonneg_left hiiiB hcp0
    have h2' := mul_le_mul_of_nonneg_left hBerr hcp0
    linarith
  have e7 : 21 / 20 * 42 * (H * Err) ≤ 108 * cp ^ 2 * (H * Err) := by
    have h0 : 0 ≤ H * Err := by positivity
    have : 21 / 20 * 42 ≤ 108 * cp ^ 2 := by linarith
    exact mul_le_mul_of_nonneg_right this h0
  linarith

/-- The halo and variation errors are small once the horizon and the rough mass are large. -/
theorem error_small {lam η W DS G H L M Err : ℝ} (hW : 0 ≤ W) (hDS : 0 ≤ DS) (hG : 0 < G)
    (hH : 0 < H) (hL : 0 < L)
    (hErr : Err = (1 + L) ^ 3 * W / (G * H) + (2 * DS + 2 * M * W) / L)
    (hbig1 : lam * 150 * ((1 + L) ^ 3 / (G * H)) ≤ η / 4)
    (hbig2 : lam * 150 * (2 * M / L) ≤ η / 4)
    (hbig3 : lam * 150 * (2 / L) ≤ η / 16) :
    lam * (150 * Err) ≤ η / 2 * W + η / 16 * DS := by
  have e : lam * (150 * Err) = lam * 150 * ((1 + L) ^ 3 / (G * H)) * W +
      (lam * 150 * (2 * M / L) * W + lam * 150 * (2 / L) * DS) := by
    rw [hErr]; field_simp; ring
  have f1 : lam * 150 * ((1 + L) ^ 3 / (G * H)) * W ≤ η / 4 * W :=
    mul_le_mul_of_nonneg_right hbig1 hW
  have f2 : lam * 150 * (2 * M / L) * W ≤ η / 4 * W := mul_le_mul_of_nonneg_right hbig2 hW
  have f3 : lam * 150 * (2 / L) * DS ≤ η / 16 * DS := mul_le_mul_of_nonneg_right hbig3 hDS
  rw [e]; linarith

/-- **The assembly of the twisted Poincaré inequality** from the two-scale bound `h1`, the
second-moment identity `h2`, the constraint identities `h3`–`h5`, the error bounds and the
`p`-sector bound `hP`. `lam` stands for `2 log 2`, `cp = (p − 1)/(p + 1)` for the parity floor. -/
theorem twisted_assembly
    {lam η p ℓ W Vp G H DS DL P Y c S A B Av Ah Bv Bh ZX lM bG e₂ L M Zsq : ℝ}
    (hlam1 : 1.386 < lam) (hlam2 : lam < 1.3863)
    (hη : 0 < η) (hη1 : η ≤ 1)
    (hp : 11 ≤ p) (hℓ : 2.35 ≤ ℓ)
    (hW : 0 ≤ W) (hVp : 0 ≤ Vp) (hG : 0 < G) (hH : 0 < H) (hDS : 0 ≤ DS) (hDL : 0 ≤ DL)
    (hL : 0 < L) (hM : 0 ≤ M) (hZX : 0 ≤ ZX) (hlM : 1 ≤ lM) (hbG : bG ≤ lam)
    (he₂0 : 0 ≤ e₂) (he₂ : e₂ ≤ 1 / 20)
    (h1 : (lam - η / 4) * W + G * ((ℓ * lM - bG) * Vp / (1 + e₂)) ≤ DS + DL)
    (h2 : Zsq ≤ W + Y ^ 2 / H)
    (h3 : Y = c * H + B)
    (h4 : c * S = -A) (hS : (p - 1) / (p + 1) * H ≤ S)
    (h5A : A = G * P + Av + Ah) (h5B : B = Bv + Bh)
    (hAv : Av ^ 2 ≤ (1 + L) ^ 3 * W / G) (hBv : Bv ^ 2 ≤ (1 + L) ^ 3 * W / G)
    (hAh : Ah ^ 2 ≤ H * ((2 * DS + 2 * M * W) / L))
    (hBh : Bh ^ 2 ≤ H * ((2 * DS + 2 * M * W) / L))
    (hP : P ^ 2 ≤ (1 - ((p - 1) / (p + 1)) ^ 2) * lM * ZX * Vp)
    (hGZ : G * ZX ≤ H)
    (hbig1 : lam * 150 * ((1 + L) ^ 3 / (G * H)) ≤ η / 4)
    (hbig2 : lam * 150 * (2 * M / L) ≤ η / 4)
    (hbig3 : lam * 150 * (2 / L) ≤ η / 16) :
    (lam - η) * Zsq ≤ DS + DL := by
  obtain ⟨cp, hcp⟩ : ∃ cp : ℝ, cp = (p - 1) / (p + 1) := ⟨_, rfl⟩
  rw [← hcp] at hS hP
  obtain ⟨hcp_ge, -, -, -⟩ := cp_facts hp hcp
  have hcp0 : 0 < cp ^ 2 := by positivity
  obtain ⟨Err, hErr⟩ : ∃ E : ℝ, E = (1 + L) ^ 3 * W / (G * H) + (2 * DS + 2 * M * W) / L :=
    ⟨_, rfl⟩
  have hErr0 : 0 ≤ Err := by rw [hErr]; positivity
  have hHErr : H * Err = (1 + L) ^ 3 * W / G + H * ((2 * DS + 2 * M * W) / L) := by
    rw [hErr]; field_simp
  have hAerr : Av ^ 2 + Ah ^ 2 ≤ H * Err := by rw [hHErr]; linarith
  have hBerr : Bv ^ 2 + Bh ^ 2 ≤ H * Err := by rw [hHErr]; linarith
  have hv := moment_bound hp hcp hG hH hVp hlM hErr0 h3 h4 hS h5A h5B hAerr hBerr hP hGZ
  have hGVp : 0 ≤ G * Vp := by positivity
  have hmain := main_term_le hlam1 hlam2 hη1 hp hℓ hcp hlM hbG hGVp he₂0 he₂
  have herr := error_small hW hDS hG hH hL hErr hbig1 hbig2 hbig3
  obtain ⟨T, hT⟩ : ∃ T : ℝ, T = Y ^ 2 / H := ⟨_, rfl⟩
  rw [← hT] at h2
  have hT0 : 0 ≤ T := by rw [hT]; positivity
  have hTY : Y ^ 2 = H * T := by rw [hT]; field_simp
  have hv' : cp ^ 2 * T ≤
      (21 / 20) ^ 2 * (1 - cp ^ 2) * lM * (G * Vp) + 150 * cp ^ 2 * Err := by
    have h : H * (cp ^ 2 * T) ≤
        H * ((21 / 20) ^ 2 * (1 - cp ^ 2) * lM * (G * Vp) + 150 * cp ^ 2 * Err) := by
      rw [hTY] at hv; linarith [hv]
    exact le_of_mul_le_mul_left h hH
  obtain ⟨Zt, hZt⟩ : ∃ Z : ℝ, Z = G * ((ℓ * lM - bG) * Vp / (1 + e₂)) := ⟨_, rfl⟩
  rw [← hZt] at h1 hmain
  have hfinal : lam * T ≤ (1 - η / 16) * Zt + (η / 2 * W + η / 16 * DS) := by
    have hlam0 : 0 < lam := by linarith
    have h := mul_le_mul_of_nonneg_left hv' hlam0.le
    have h' : cp ^ 2 * (lam * T) ≤
        cp ^ 2 * ((1 - η / 16) * Zt + (η / 2 * W + η / 16 * DS)) := by
      have := mul_le_mul_of_nonneg_left herr hcp0.le
      linarith
    exact le_of_mul_le_mul_left h' hcp0
  have hZ : (lam - η) * Zsq ≤ (lam - η) * W + lam * T := by
    have hle : (lam - η) * Zsq ≤ (lam - η) * (W + T) :=
      mul_le_mul_of_nonneg_left h2 (by linarith)
    have : 0 ≤ η * T := mul_nonneg hη.le hT0
    linarith
  have h1' := mul_le_mul_of_nonneg_left h1 (show 0 ≤ 1 - η / 16 by linarith)
  have hbr : 0 ≤ (η / 4 - η / 16 * lam + η ^ 2 / 64) * W := by
    apply mul_nonneg _ hW
    have : 0 ≤ η / 16 * (4 - lam + η / 4) := mul_nonneg (by linarith) (by linarith)
    linarith
  have hηDL : 0 ≤ η * DL := mul_nonneg hη.le hDL
  linarith

/-- The arithmetic of the two-scale inequality with a variable constant `g`:
`(g − ε/2) W ≤ D_S + D_L` once the parameters are in range for `g ≤ Tmax`. -/
theorem two_scale_arith {g ε τ κ L M W U DS DL ρ cU Tmax : ℝ} (hε : 0 < ε) (hg : ε / 2 < g)
    (hgT : g ≤ Tmax) (hτ0 : 0 < τ) (hτ1 : τ ≤ 1 / 2)
    (hτT : τ * (Tmax ^ 2 + 4 * Tmax) ≤ ε / 2) (hML : 2 * M / L ≤ τ) (h2L : 2 / L ≤ τ)
    (hW0 : 0 ≤ W) (hU0 : 0 ≤ U) (hDS0 : 0 ≤ DS) (hDL0 : 0 ≤ DL) (hρ : ρ ≤ 1 + τ)
    (hc : ρ * cU ≤ g) (hκ : κ * (4 * Tmax) ≤ 1) (hU : U ≤ κ * DL)
    (hcore : g * ((1 - 2 * M / L) * W) ≤ g * U + ρ * ((1 + τ) * DS + cU * U) + 2 * g / L * DS) :
    (g - ε / 2) * W ≤ DS + DL := by
  have hg0 : 0 < g := by linarith
  have hA : g * (1 - τ) * W ≤ 2 * (g * U) + ((1 + τ) ^ 2 + g * τ) * DS := by
    have e1 : g * (1 - τ) * W ≤ g * ((1 - 2 * M / L) * W) := by
      have : (1 - τ) * W ≤ (1 - 2 * M / L) * W :=
        mul_le_mul_of_nonneg_right (by linarith) hW0
      calc g * (1 - τ) * W = g * ((1 - τ) * W) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left this hg0.le
    have e3 : ρ * (1 + τ) * DS ≤ (1 + τ) ^ 2 * DS := by
      rw [sq]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hρ (by linarith)) hDS0
    have e4 : ρ * cU * U ≤ g * U := mul_le_mul_of_nonneg_right hc hU0
    have e5 : 2 * g / L * DS ≤ g * τ * DS := by
      rw [show 2 * g / L = g * (2 / L) by ring]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2L hg0.le) hDS0
    calc g * (1 - τ) * W ≤ g * ((1 - 2 * M / L) * W) := e1
      _ ≤ _ := hcore
      _ = g * U + (ρ * (1 + τ) * DS + ρ * cU * U) + 2 * g / L * DS := by ring
      _ ≤ g * U + ((1 + τ) ^ 2 * DS + g * U) + g * τ * DS :=
          add_le_add (add_le_add le_rfl (add_le_add e3 e4)) e5
      _ = _ := by ring
  have hκ' : 2 * (g - ε / 2) * κ ≤ 1 - τ := by
    rcases le_or_gt κ 0 with h | h
    · have : 2 * (g - ε / 2) * κ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith) h
      linarith
    · have h1 : (g - ε / 2) * κ ≤ Tmax * κ := mul_le_mul_of_nonneg_right (by linarith) h.le
      linarith
  have hUL : 2 * (g * U) * (g - ε / 2) ≤ g * (1 - τ) * DL := by
    have hge : 0 ≤ g - ε / 2 := by linarith
    have h1 := mul_le_mul_of_nonneg_left hU
      (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hg0.le) hge)
    have h2 := mul_le_mul_of_nonneg_right hκ' (show 0 ≤ g * DL by positivity)
    linarith
  have hnum : (g - ε / 2) * ((1 + τ) ^ 2 + g * τ) ≤ g * (1 - τ) := by
    have hb : τ * (g ^ 2 + 4 * g) ≤ ε / 2 := by
      have h1 : g ^ 2 + 4 * g ≤ Tmax ^ 2 + 4 * Tmax := by nlinarith
      have := mul_le_mul_of_nonneg_left h1 hτ0.le
      linarith
    have h3 : (g - ε / 2) * ((1 + τ) ^ 2 + g * τ) =
        g * (1 - τ) + (τ * (3 * g + g * τ + g ^ 2) - ε / 2 * (1 + τ) ^ 2 - ε / 2 * (g * τ)) := by
      ring
    have h4 : τ * (3 * g + g * τ + g ^ 2) ≤ τ * (g ^ 2 + 4 * g) := by
      apply mul_le_mul_of_nonneg_left _ hτ0.le
      nlinarith
    have h5 : ε / 2 ≤ ε / 2 * (1 + τ) ^ 2 := by
      have h1τ : 1 ≤ (1 + τ) ^ 2 := by nlinarith
      have := mul_le_mul_of_nonneg_left h1τ (show 0 ≤ ε / 2 by positivity)
      linarith
    have h6 : 0 ≤ ε / 2 * (g * τ) := by positivity
    rw [h3]; linarith
  have hpos : 0 < g * (1 - τ) := mul_pos hg0 (by linarith)
  refine le_of_mul_le_mul_left ?_ hpos
  calc g * (1 - τ) * ((g - ε / 2) * W) = (g - ε / 2) * (g * (1 - τ) * W) := by ring
    _ ≤ (g - ε / 2) * (2 * (g * U) + ((1 + τ) ^ 2 + g * τ) * DS) :=
        mul_le_mul_of_nonneg_left hA (by linarith)
    _ = 2 * (g * U) * (g - ε / 2) + (g - ε / 2) * ((1 + τ) ^ 2 + g * τ) * DS := by ring
    _ ≤ g * (1 - τ) * DL + g * (1 - τ) * DS :=
        add_le_add hUL (mul_le_mul_of_nonneg_right hnum hDS0)
    _ = g * (1 - τ) * (DS + DL) := by ring

/-! ### 2. The sign ladder -/

theorem one_le_ladderMass {p : ℕ} (J : ℕ) : 1 ≤ ladderMass p J := by
  have := single_le_sum (f := fun i => (1 / (p : ℝ)) ^ i) (fun i _ => by positivity)
    (mem_range.mpr (Nat.succ_pos J))
  simpa [ladderMass] using this

theorem ladderMass_le_two {p : ℕ} (hp : 2 ≤ p) (J : ℕ) : ladderMass p J ≤ 2 := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hq1 : 1 / (p : ℝ) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ hp0 (by norm_num)]; linarith
  have hq0 : 0 ≤ 1 / (p : ℝ) := by positivity
  have := geom_sum_Ico_le_of_lt_one (m := 0) (n := J + 1) hq0 (by linarith)
  rw [← range_eq_Ico, pow_zero] at this
  rw [ladderMass]
  refine this.trans ?_
  rw [div_le_iff₀ (by linarith)]
  linarith

theorem boxGap_le_two_mul_log_two (J : ℕ) : boxGap J ≤ 2 * Real.log 2 := by
  rw [boxGap]
  have : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ (J + 1) := by positivity
  have := Real.log_pos (show (1 : ℝ) < 2 by norm_num)
  nlinarith

/-- The signed ladder mass `Σ (−1/p)^i` dominates `(p − 1)/(p + 1)` times the ladder mass. -/
theorem signMass_ge {p : ℕ} (hp : 2 ≤ p) (J : ℕ) :
    ((p : ℝ) - 1) / ((p : ℝ) + 1) * ladderMass p J ≤
      ∑ i ∈ range (J + 1), (-1 / (p : ℝ)) ^ i := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < p := by linarith
  have hp1' : (p : ℝ) - 1 ≠ 0 := by linarith
  have hp1'' : (p : ℝ) + 1 ≠ 0 := by linarith
  have h1p : (1 : ℝ) - p ≠ 0 := sub_ne_zero.mpr (ne_of_lt hp1)
  have h1p' : (-1 : ℝ) - p ≠ 0 := ne_of_lt (by linarith)
  have hq : (1 / (p : ℝ)) ≠ 1 := by
    rw [Ne, div_eq_one_iff_eq hp0.ne']; intro h; linarith
  have hq' : (-1 / (p : ℝ)) ≠ 1 := by
    rw [Ne, div_eq_one_iff_eq hp0.ne']; intro h; linarith
  rw [ladderMass, geom_sum_eq hq, geom_sum_eq hq']
  set a := (1 / (p : ℝ)) ^ (J + 1) with ha
  set b := (-1 / (p : ℝ)) ^ (J + 1) with hb
  have hab : b ≤ a := by
    calc b ≤ |b| := le_abs_self b
      _ = a := by
        rw [hb, ha, abs_pow, abs_div, abs_neg, abs_one, abs_of_pos hp0]
  have e0 : 1 / (p : ℝ) - 1 = (1 - p) / p := by field_simp
  have e0' : -1 / (p : ℝ) - 1 = (-1 - p) / p := by field_simp
  have e1 : ((p : ℝ) - 1) / ((p : ℝ) + 1) * ((a - 1) / (1 / (p : ℝ) - 1)) =
      (p : ℝ) * (1 - a) / ((p : ℝ) + 1) := by
    rw [e0, div_div_eq_mul_div, div_mul_div_comm, div_eq_div_iff (by positivity) hp1'']
    ring
  have e2 : (b - 1) / (-1 / (p : ℝ) - 1) = (p : ℝ) * (1 - b) / ((p : ℝ) + 1) := by
    rw [e0', div_div_eq_mul_div, div_eq_div_iff h1p' hp1'']
    ring
  rw [e1, e2]
  apply div_le_div_of_nonneg_right _ (by linarith)
  apply mul_le_mul_of_nonneg_left (by linarith) hp0.le

/-- The signed ladder deviates from `c_p = (p − 1)/(p + 1)` by at most `(1 − c_p²)` times its
mass. -/
theorem sum_ladWeight_sign_sub_sq_le {p : ℕ} (hp : 2 ≤ p) (J : ℕ) :
    ∑ i ∈ range (J + 1), (1 / (p : ℝ)) ^ i * ((-1 : ℝ) ^ i - ((p : ℝ) - 1) / ((p : ℝ) + 1)) ^ 2 ≤
      (1 - (((p : ℝ) - 1) / ((p : ℝ) + 1)) ^ 2) * ladderMass p J := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp
  have hκ : 0 ≤ ((p : ℝ) - 1) / ((p : ℝ) + 1) := div_nonneg (by linarith) (by linarith)
  have hσ := signMass_ge hp J
  have hexp : ∀ i ∈ range (J + 1),
      (1 / (p : ℝ)) ^ i * ((-1 : ℝ) ^ i - ((p : ℝ) - 1) / ((p : ℝ) + 1)) ^ 2 =
        (1 + (((p : ℝ) - 1) / ((p : ℝ) + 1)) ^ 2) * (1 / (p : ℝ)) ^ i -
          2 * (((p : ℝ) - 1) / ((p : ℝ) + 1)) * (-1 / (p : ℝ)) ^ i := by
    intro i _
    have h1 : ((-1 : ℝ) ^ i) ^ 2 = 1 := by
      rw [← pow_mul, mul_comm, pow_mul]; simp
    have h2 : (-1 / (p : ℝ)) ^ i = (-1 : ℝ) ^ i * (1 / (p : ℝ)) ^ i := by
      rw [← mul_pow]; congr 1; ring
    rw [h2, sub_sq, h1]; ring
  rw [sum_congr rfl hexp, sum_sub_distrib, ← mul_sum, ← mul_sum,
    show ∑ i ∈ range (J + 1), (1 / (p : ℝ)) ^ i = ladderMass p J from rfl]
  have := mul_le_mul_of_nonneg_left hσ (show 0 ≤ 2 * (((p : ℝ) - 1) / ((p : ℝ) + 1)) by linarith)
  nlinarith

/-! ### 3. The box fibred over one prime -/

theorem mul_pow_mem_smoothBox' {J Q p u i : ℕ} (hp : p ∈ (range Q).filter Nat.Prime)
    (hu : u ∈ (smoothBox J Q).filter (fun u => ¬ p ∣ u)) (hi : i ∈ range (J + 1)) :
    u * p ^ i ∈ smoothBox J Q := by
  obtain ⟨hpQ, hpp⟩ := mem_filter.mp hp
  obtain ⟨hu', hpu⟩ := mem_filter.mp hu
  obtain ⟨h1, h2, h3⟩ := mem_smoothBox.mp hu'
  have hu0 : u ≠ 0 := by omega
  refine mem_smoothBox.mpr ⟨Nat.one_le_iff_ne_zero.mpr
    (mul_ne_zero hu0 (pow_ne_zero _ hpp.ne_zero)), fun q hq => ?_, fun q => ?_⟩
  · rw [Nat.primeFactors_mul hu0 (pow_ne_zero _ hpp.ne_zero), mem_union] at hq
    rcases hq with hq | hq
    · exact h2 q hq
    · have hq' := Nat.mem_primeFactors.mp hq
      rw [(Nat.prime_dvd_prime_iff_eq hq'.1 hpp).mp (hq'.1.dvd_of_dvd_pow hq'.2.1)]
      exact mem_range.mp hpQ
  · rw [Nat.factorization_mul hu0 (pow_ne_zero _ hpp.ne_zero), Finsupp.add_apply,
      hpp.factorization_pow]
    by_cases hqp : q = p
    · subst hqp
      rw [Finsupp.single_eq_same, Nat.factorization_eq_zero_of_not_dvd hpu, zero_add]
      have := mem_range.mp hi; omega
    · rw [Finsupp.single_eq_of_ne hqp, add_zero]; exact h3 q

/-- **The box fibres over its `p`-ladders**: `Box = ⊔_{u ∈ Box, p ∤ u} {u p^i : i ≤ J}`. -/
theorem sum_smoothBox_eq_ladders {J Q p : ℕ} (hp : p ∈ (range Q).filter Nat.Prime) (φ : ℕ → ℝ) :
    ∑ a ∈ smoothBox J Q, φ a =
      ∑ u ∈ (smoothBox J Q).filter (fun u => ¬ p ∣ u), ∑ i ∈ range (J + 1), φ (u * p ^ i) := by
  have hpp := (mem_filter.mp hp).2
  rw [sum_sigma']
  symm
  refine sum_nbij' (fun x => x.1 * p ^ x.2)
    (fun a => ⟨a / p ^ a.factorization p, a.factorization p⟩) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨u, i⟩ h
    rw [mem_sigma] at h
    exact mul_pow_mem_smoothBox' hp h.1 h.2
  · intro a ha
    obtain ⟨h1, h2, h3⟩ := mem_smoothBox.mp ha
    have ha0 : a ≠ 0 := by omega
    rw [mem_sigma, mem_filter, mem_range]
    refine ⟨⟨mem_smoothBox.mpr ⟨Nat.ordCompl_pos p ha0, fun q hq => ?_, fun q => ?_⟩,
      Nat.not_dvd_ordCompl hpp ha0⟩, ?_⟩
    · exact h2 q (Nat.mem_primeFactors.mpr ⟨(Nat.mem_primeFactors.mp hq).1,
        (Nat.mem_primeFactors.mp hq).2.1.trans (Nat.ordCompl_dvd a p), ha0⟩)
    · rw [Nat.factorization_ordCompl]
      by_cases hqp : q = p
      · subst hqp; rw [Finsupp.erase_same]; exact Nat.zero_le _
      · rw [Finsupp.erase_ne hqp]; exact h3 q
    · show a.factorization p < J + 1
      have := h3 p; omega
  · rintro ⟨u, i⟩ h
    rw [mem_sigma, mem_filter] at h
    dsimp only at h
    obtain ⟨⟨hu, hpu⟩, -⟩ := h
    have hu0 : u ≠ 0 := by have := (mem_smoothBox.mp hu).1; omega
    have hfac : (u * p ^ i).factorization p = i := by
      rw [Nat.factorization_mul hu0 (pow_ne_zero _ hpp.ne_zero), Finsupp.add_apply,
        hpp.factorization_pow, Finsupp.single_eq_same, Nat.factorization_eq_zero_of_not_dvd hpu,
        zero_add]
    dsimp only
    rw [hfac, Nat.mul_div_cancel _ (pow_pos hpp.pos i)]
  · intro a _
    dsimp only
    rw [mul_comm, Nat.ordProj_mul_ordCompl_eq_self]
  · intro _ _
    rfl

/-- On a `p`-ladder the flip is the sign of the level. -/
theorem finiteFlip_mul_pow {p u i : ℕ} (hp : p.Prime) (hu : u ≠ 0) (hpu : ¬ p ∣ u) :
    finiteFlip {p} (u * p ^ i) = (-1 : ℝ) ^ i := by
  simp only [finiteFlip, prod_singleton]
  rw [Nat.factorization_mul hu (pow_ne_zero _ hp.ne_zero), Finsupp.add_apply,
    hp.factorization_pow, Finsupp.single_eq_same, Nat.factorization_eq_zero_of_not_dvd hpu,
    zero_add]

theorem one_div_cast_mul_pow (u p i : ℕ) :
    1 / ((u * p ^ i : ℕ) : ℝ) = 1 / (u : ℝ) * (1 / (p : ℝ)) ^ i := by
  push_cast
  rw [one_div_pow, one_div_mul_one_div]

/-! ### 4. The within-fibre variance along `p` -/

/-- The within-fibre variance along the `p`-ladders of the box. -/
def pFibreVar (J Q p : ℕ) (f : ℕ → ℝ) : ℝ :=
  ∑ u ∈ (smoothBox J Q).filter (fun u => ¬ p ∣ u), boxLadderVar p u J f

theorem pFibreVar_nonneg (J Q p : ℕ) (f : ℕ → ℝ) : 0 ≤ pFibreVar J Q p f :=
  sum_nonneg fun _ _ => boxLadderVar_nonneg _ _ _ _

/-- The within-fibre variance is at most the second moment on the box. -/
theorem pFibreVar_le {J Q p : ℕ} (hp : p ∈ (range Q).filter Nat.Prime) (f : ℕ → ℝ) :
    pFibreVar J Q p f ≤ ∑ a ∈ smoothBox J Q, 1 / (a : ℝ) * f a ^ 2 := by
  rw [sum_smoothBox_eq_ladders hp (fun a => 1 / (a : ℝ) * f a ^ 2), pFibreVar]
  refine sum_le_sum fun u _ => ?_
  have := wVar_le (s := range (J + 1)) (w := fun i => 1 / ((u * p ^ i : ℕ) : ℝ))
    (v := fun i => f (u * p ^ i)) (fun i _ => by positivity) 0
  rw [boxLadderVar]
  simpa only [sub_zero] using this

/-- **Twisted Efron–Stein on the box.** Keeping the `p`-ladders separate, the box energy pays the
box variance with constant `g_J` and the within-`p`-fibre variance with the excess
`log p · W_p(J) − g_J`. -/
theorem boxGap_mul_boxVar_add_le {J : ℕ} (hJ : 1 ≤ J) {Q p : ℕ}
    (hp : p ∈ (range Q).filter Nat.Prime) (f : ℕ → ℝ) :
    boxGap J * boxVar J Q f + (Real.log p * ladderMass p J - boxGap J) * pFibreVar J Q p f ≤
      boxEnergy J Q f := by
  have hg : 0 < boxGap J := by
    rw [boxGap]
    have : (1 / 2 : ℝ) ^ (J + 1) < 1 := pow_lt_one₀ (by norm_num) (by norm_num) (by omega)
    have := Real.log_pos (show (1 : ℝ) < 2 by norm_num)
    nlinarith
  have hlad : ∀ q ∈ (range Q).filter Nat.Prime, ∀ u ∈ (smoothBox J Q).filter (fun u => ¬ q ∣ u),
      Real.log q * ladderMass q J * boxLadderVar q u J f ≤ ladderEnergy q u J f := by
    intro q hq u hu
    have hqq := (mem_filter.mp hq).2
    have hu1 := (mem_smoothBox.mp (mem_filter.mp hu).1).1
    have h := boxLadderVar_le (J := J) hqq.two_le hu1 f
    have hlW : 0 < Real.log q * ladderMass q J := hg.trans_le (boxGap_le_ladder hqq hJ)
    have := (le_div_iff₀ hlW).mp h
    linarith
  have hterm : ∀ q ∈ (range Q).filter Nat.Prime,
      0 ≤ ∑ u ∈ (smoothBox J Q).filter (fun u => ¬ q ∣ u),
        (ladderEnergy q u J f - boxGap J * boxLadderVar q u J f) := by
    intro q hq
    refine sum_nonneg fun u hu => ?_
    have hqq := (mem_filter.mp hq).2
    have h1 := hlad q hq u hu
    have h2 := mul_le_mul_of_nonneg_right (boxGap_le_ladder hqq hJ) (boxLadderVar_nonneg q u J f)
    linarith
  have hsingle := single_le_sum hterm hp
  have hp_term : (Real.log p * ladderMass p J - boxGap J) * pFibreVar J Q p f ≤
      ∑ u ∈ (smoothBox J Q).filter (fun u => ¬ p ∣ u),
        (ladderEnergy p u J f - boxGap J * boxLadderVar p u J f) := by
    rw [pFibreVar, mul_sum]
    refine sum_le_sum fun u hu => ?_
    have := hlad p hp u hu
    linarith
  have hES := boxVar_le_boxGlauber J Q f
  have hsplit : boxEnergy J Q f - boxGap J * boxGlauber J Q f =
      ∑ q ∈ (range Q).filter Nat.Prime, ∑ u ∈ (smoothBox J Q).filter (fun u => ¬ q ∣ u),
        (ladderEnergy q u J f - boxGap J * boxLadderVar q u J f) := by
    rw [boxEnergy, boxGlauber, mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun q _ => ?_
    rw [mul_sum, ← sum_sub_distrib]
  have := mul_le_mul_of_nonneg_left hES hg.le
  linarith

/-- **The flipped pole lives in the `p`-sector.** On the box, the pairing of `ω_p g` with the
harmonic weights, for a mean-zero `g` vanishing above `X`, is controlled by the within-fibre
variance along `p`: `⟨ω_p, g⟩² ≤ (1 − c_p²) W_p(J) (Σ_{u ≤ X} 1/u) V_p(g)`. -/
theorem sum_flip_mul_sq_le {J Q p X : ℕ} (hp : p ∈ (range Q).filter Nat.Prime) {g : ℕ → ℝ}
    (hmean : ∑ a ∈ smoothBox J Q, 1 / (a : ℝ) * g a = 0) (hvan : ∀ n, X < n → g n = 0) :
    (∑ a ∈ smoothBox J Q, 1 / (a : ℝ) * (finiteFlip {p} a * g a)) ^ 2 ≤
      (1 - (((p : ℝ) - 1) / ((p : ℝ) + 1)) ^ 2) * ladderMass p J *
        (∑ u ∈ ((smoothBox J Q).filter (fun u => ¬ p ∣ u)).filter (· ≤ X), 1 / (u : ℝ)) *
        pFibreVar J Q p g := by
  have hpp := (mem_filter.mp hp).2
  have hp2 := hpp.two_le
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hpp.one_lt
  set F := (smoothBox J Q).filter (fun u => ¬ p ∣ u) with hF
  set κ := ((p : ℝ) - 1) / ((p : ℝ) + 1) with hκ
  have hκ0 : 0 ≤ κ := div_nonneg (by linarith) (by linarith)
  have hκ1 : κ ≤ 1 := by rw [hκ, div_le_one (by linarith)]; linarith
  have hlM : 0 < ladderMass p J := lt_of_lt_of_le one_pos (one_le_ladderMass J)
  set m : ℕ → ℝ := fun u => wMean (range (J + 1)) (fun i => 1 / ((u * p ^ i : ℕ) : ℝ))
    (fun i => g (u * p ^ i)) with hm
  set Λ : ℕ → ℝ := fun u => ∑ i ∈ range (J + 1),
    (1 / (p : ℝ)) ^ i * (((-1 : ℝ) ^ i - κ) * (g (u * p ^ i) - m u)) with hΛ
  -- the ladder sums of `g`
  have hmean_u : ∀ u ∈ F, ∑ i ∈ range (J + 1), (1 / (p : ℝ)) ^ i * g (u * p ^ i) =
      ladderMass p J * m u := by
    intro u hu
    have hu1 := (mem_smoothBox.mp (mem_filter.mp hu).1).1
    have hu0 : (u : ℝ) ≠ 0 := by exact_mod_cast (show u ≠ 0 by omega)
    have e1 : ∑ i ∈ range (J + 1), 1 / ((u * p ^ i : ℕ) : ℝ) * g (u * p ^ i) =
        1 / (u : ℝ) * ∑ i ∈ range (J + 1), (1 / (p : ℝ)) ^ i * g (u * p ^ i) := by
      rw [mul_sum]
      exact sum_congr rfl fun i _ => by rw [one_div_cast_mul_pow]; ring
    have e2 : ∑ i ∈ range (J + 1), 1 / ((u * p ^ i : ℕ) : ℝ) = 1 / (u : ℝ) * ladderMass p J := by
      rw [ladderMass, mul_sum]
      exact sum_congr rfl fun i _ => by rw [one_div_cast_mul_pow]
    simp only [hm, wMean]
    rw [e1, e2]
    field_simp
  -- the splitting of the signed ladder sum
  have hsplit : ∀ u ∈ F, ∑ i ∈ range (J + 1), (1 / (p : ℝ)) ^ i * ((-1 : ℝ) ^ i * g (u * p ^ i)) =
      Λ u + (∑ i ∈ range (J + 1), (1 / (p : ℝ)) ^ i * (-1 : ℝ) ^ i) * m u := by
    intro u hu
    have h := hmean_u u hu
    simp only [hΛ]
    have e : ∀ i ∈ range (J + 1),
        (1 / (p : ℝ)) ^ i * (((-1 : ℝ) ^ i - κ) * (g (u * p ^ i) - m u)) =
          (1 / (p : ℝ)) ^ i * ((-1 : ℝ) ^ i * g (u * p ^ i)) -
            m u * ((1 / (p : ℝ)) ^ i * (-1 : ℝ) ^ i) -
            κ * ((1 / (p : ℝ)) ^ i * g (u * p ^ i)) + κ * m u * (1 / (p : ℝ)) ^ i :=
      fun i _ => by ring
    rw [sum_congr rfl e, sum_add_distrib, sum_sub_distrib, sum_sub_distrib, ← mul_sum, ← mul_sum,
      ← mul_sum, h, show ∑ i ∈ range (J + 1), (1 / (p : ℝ)) ^ i = ladderMass p J from rfl]
    ring
  -- the means have zero total
  have hm0 : ∑ u ∈ F, 1 / (u : ℝ) * m u = 0 := by
    have h1 : ∑ a ∈ smoothBox J Q, 1 / (a : ℝ) * g a =
        ∑ u ∈ F, 1 / (u : ℝ) * (ladderMass p J * m u) := by
      rw [sum_smoothBox_eq_ladders hp (fun a => 1 / (a : ℝ) * g a)]
      refine sum_congr rfl fun u hu => ?_
      rw [← hmean_u u hu, mul_sum]
      exact sum_congr rfl fun i _ => by rw [one_div_cast_mul_pow]; ring
    have h2 : ∑ u ∈ F, 1 / (u : ℝ) * (ladderMass p J * m u) =
        ladderMass p J * ∑ u ∈ F, 1 / (u : ℝ) * m u := by
      rw [mul_sum]; exact sum_congr rfl fun u _ => by ring
    rw [h1, h2] at hmean
    exact (mul_eq_zero.mp hmean).resolve_left hlM.ne'
  -- ladders above `X` carry nothing
  have hvan_u : ∀ u ∈ F, X < u → Λ u = 0 := by
    intro u hu hXu
    have hg : ∀ i ∈ range (J + 1), g (u * p ^ i) = 0 := fun i _ =>
      hvan _ (lt_of_lt_of_le hXu (Nat.le_mul_of_pos_right u (pow_pos hpp.pos i)))
    have hmu : m u = 0 := by
      simp only [hm, wMean]
      rw [sum_eq_zero (fun i hi => by rw [hg i hi, mul_zero]), zero_div]
    simp only [hΛ]
    exact sum_eq_zero fun i hi => by rw [hg i hi, hmu, sub_zero, mul_zero, mul_zero]
  set T := F.filter (· ≤ X) with hT
  have hrestrict : ∑ u ∈ F, 1 / (u : ℝ) * Λ u = ∑ u ∈ T, 1 / (u : ℝ) * Λ u := by
    symm
    refine sum_subset (filter_subset _ _) fun u hu hu' => ?_
    have hXu : X < u := by
      by_contra hle
      exact hu' (mem_filter.mpr ⟨hu, not_lt.mp hle⟩)
    rw [hvan_u u hu hXu, mul_zero]
  -- the pairing is the restricted sum
  have hLHS : ∑ a ∈ smoothBox J Q, 1 / (a : ℝ) * (finiteFlip {p} a * g a) =
      ∑ u ∈ T, 1 / (u : ℝ) * Λ u := by
    rw [sum_smoothBox_eq_ladders hp (fun a => 1 / (a : ℝ) * (finiteFlip {p} a * g a)),
      ← hrestrict]
    have hfib : ∀ u ∈ F, ∑ i ∈ range (J + 1),
        1 / ((u * p ^ i : ℕ) : ℝ) * (finiteFlip {p} (u * p ^ i) * g (u * p ^ i)) =
          1 / (u : ℝ) * (Λ u + (∑ i ∈ range (J + 1), (1 / (p : ℝ)) ^ i * (-1 : ℝ) ^ i) * m u) := by
      intro u hu
      rw [← hsplit u hu, mul_sum]
      refine sum_congr rfl fun i _ => ?_
      obtain ⟨hu', hpu⟩ := mem_filter.mp hu
      have hu0 : u ≠ 0 := by have := (mem_smoothBox.mp hu').1; omega
      rw [finiteFlip_mul_pow hpp hu0 hpu, one_div_cast_mul_pow]; ring
    rw [sum_congr rfl hfib]
    simp only [mul_add, sum_add_distrib]
    have h2 : ∑ u ∈ F, 1 / (u : ℝ) * ((∑ i ∈ range (J + 1), (1 / (p : ℝ)) ^ i * (-1 : ℝ) ^ i) * m u) =
        (∑ i ∈ range (J + 1), (1 / (p : ℝ)) ^ i * (-1 : ℝ) ^ i) * ∑ u ∈ F, 1 / (u : ℝ) * m u := by
      rw [mul_sum]; exact sum_congr rfl fun u _ => by ring
    rw [h2, hm0, mul_zero, add_zero]
  rw [hLHS]
  -- Cauchy–Schwarz over `u ≤ X`
  have hCS1 : (∑ u ∈ T, 1 / (u : ℝ) * Λ u) ^ 2 ≤
      (∑ u ∈ T, 1 / (u : ℝ)) * ∑ u ∈ T, 1 / (u : ℝ) * Λ u ^ 2 :=
    sum_sq_le_sum_mul_sum_of_sq_le_mul T (fun u _ => by positivity) (fun u _ => by positivity)
      (fun u _ => le_of_eq (by ring))
  -- Cauchy–Schwarz on each ladder
  have hCS2 : ∀ u ∈ T, 1 / (u : ℝ) * Λ u ^ 2 ≤
      (1 - κ ^ 2) * ladderMass p J * boxLadderVar p u J g := by
    intro u hu
    have hu' := (mem_filter.mp hu).1
    obtain ⟨huB, hpu⟩ := mem_filter.mp hu'
    have hu1 := (mem_smoothBox.mp huB).1
    have hu0 : (0 : ℝ) < u := by exact_mod_cast hu1
    have hcs : Λ u ^ 2 ≤ (∑ i ∈ range (J + 1), (1 / (p : ℝ)) ^ i * ((-1 : ℝ) ^ i - κ) ^ 2) *
        ∑ i ∈ range (J + 1), (1 / (p : ℝ)) ^ i * (g (u * p ^ i) - m u) ^ 2 := by
      simp only [hΛ]
      exact sum_sq_le_sum_mul_sum_of_sq_le_mul _ (fun i _ => by positivity)
        (fun i _ => by positivity) (fun i _ => le_of_eq (by ring))
    have hvar : ∑ i ∈ range (J + 1), (1 / (p : ℝ)) ^ i * (g (u * p ^ i) - m u) ^ 2 =
        (u : ℝ) * boxLadderVar p u J g := by
      rw [boxLadderVar, wVar, mul_sum]
      refine sum_congr rfl fun i _ => ?_
      rw [one_div_cast_mul_pow]
      simp only [hm]
      field_simp
    have hsign := sum_ladWeight_sign_sub_sq_le hp2 J
    rw [hvar] at hcs
    have hV0 := boxLadderVar_nonneg p u J g
    have hnn : 0 ≤ (u : ℝ) * boxLadderVar p u J g := by positivity
    have hc0 : 0 ≤ 1 - κ ^ 2 := by nlinarith
    calc 1 / (u : ℝ) * Λ u ^ 2
        ≤ 1 / (u : ℝ) * ((1 - κ ^ 2) * ladderMass p J * ((u : ℝ) * boxLadderVar p u J g)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact hcs.trans (mul_le_mul_of_nonneg_right hsign hnn)
      _ = (1 - κ ^ 2) * ladderMass p J * boxLadderVar p u J g := by
          field_simp
  have hc0 : 0 ≤ 1 - κ ^ 2 := by nlinarith
  have hsumT : ∑ u ∈ T, 1 / (u : ℝ) * Λ u ^ 2 ≤ (1 - κ ^ 2) * ladderMass p J * pFibreVar J Q p g := by
    calc ∑ u ∈ T, 1 / (u : ℝ) * Λ u ^ 2
        ≤ ∑ u ∈ T, (1 - κ ^ 2) * ladderMass p J * boxLadderVar p u J g := sum_le_sum hCS2
      _ = (1 - κ ^ 2) * ladderMass p J * ∑ u ∈ T, boxLadderVar p u J g := by rw [mul_sum]
      _ ≤ (1 - κ ^ 2) * ladderMass p J * pFibreVar J Q p g := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
            fun u _ _ => boxLadderVar_nonneg _ _ _ _
  have hT0 : 0 ≤ ∑ u ∈ T, 1 / (u : ℝ) := sum_nonneg fun u _ => by positivity
  calc _ ≤ _ := hCS1
    _ ≤ (∑ u ∈ T, 1 / (u : ℝ)) * ((1 - κ ^ 2) * ladderMass p J * pFibreVar J Q p g) :=
        mul_le_mul_of_nonneg_left hsumT hT0
    _ = _ := by ring

/-! ### 5. The zero extension -/

theorem sum_smoothBox_zeroExt_mul (Q X : ℕ) (h φ : ℕ → ℝ) :
    ∑ a ∈ smoothBox X Q, 1 / (a : ℝ) * (zeroExt Q X h a * φ a) =
      ∑ a ∈ smoothSet Q X, 1 / (a : ℝ) *
        ((h a - wMean (smoothSet Q X) (fun a => 1 / (a : ℝ)) h) * φ a) := by
  rw [← sum_subset (smoothSet_subset_smoothBox Q X) (fun a ha ha' => ?_)]
  · refine sum_congr rfl fun a ha => ?_
    rw [zeroExt, if_pos (mem_smoothSet.mp ha).2.1]
  · have : ¬ a ≤ X := fun hle => ha' (mem_smoothSet.mpr
      ⟨(mem_smoothBox.mp ha).1, hle, (mem_smoothBox.mp ha).2.1⟩)
    rw [zeroExt, if_neg this, zero_mul, mul_zero]

theorem sum_smoothBox_zeroExt_eq_zero (Q X : ℕ) (h : ℕ → ℝ) :
    ∑ a ∈ smoothBox X Q, 1 / (a : ℝ) * zeroExt Q X h a = 0 := by
  have := sum_smoothBox_zeroExt_mul Q X h (fun _ => 1)
  simp only [mul_one] at this
  rw [this]
  have e : ∀ a ∈ smoothSet Q X,
      1 / (a : ℝ) * (h a - wMean (smoothSet Q X) (fun a => 1 / (a : ℝ)) h) =
        1 / (a : ℝ) * h a - 1 / (a : ℝ) * wMean (smoothSet Q X) (fun a => 1 / (a : ℝ)) h :=
    fun a _ => mul_sub _ _ _
  rw [sum_congr rfl e, sum_sub_distrib, ← sum_mul]
  by_cases hS : ∑ a ∈ smoothSet Q X, 1 / (a : ℝ) = 0
  · have h0 := (sum_eq_zero_iff_of_nonneg (fun a _ => by positivity)).mp hS
    rw [hS, zero_mul, sub_zero]
    exact sum_eq_zero fun a ha => by rw [h0 a ha, zero_mul]
  · simp only [wMean]
    rw [mul_div_cancel₀ _ hS, sub_self]

theorem sum_smoothBox_zeroExt_sq (Q X : ℕ) (h : ℕ → ℝ) :
    ∑ a ∈ smoothBox X Q, 1 / (a : ℝ) * zeroExt Q X h a ^ 2 = smoothVar Q X h := by
  rw [← sum_subset (smoothSet_subset_smoothBox Q X) (fun a ha ha' => ?_)]
  · rw [smoothVar, wVar]
    refine sum_congr rfl fun a ha => ?_
    rw [zeroExt, if_pos (mem_smoothSet.mp ha).2.1]
  · have : ¬ a ≤ X := fun hle => ha' (mem_smoothSet.mpr
      ⟨(mem_smoothBox.mp ha).1, hle, (mem_smoothBox.mp ha).2.1⟩)
    rw [zeroExt, if_neg this]; ring

theorem smoothEnergy_nonneg (Q X : ℕ) (h : ℕ → ℝ) : 0 ≤ smoothEnergy Q X h :=
  sum_nonneg fun _ _ => sum_nonneg fun _ _ => sum_nonneg fun _ _ => sum_nonneg fun _ _ => by
    split_ifs
    · exact mul_nonneg (div_nonneg (Real.log_natCast_nonneg _) (Nat.cast_nonneg _)) (sq_nonneg _)
    · exact le_rfl

theorem boxEnergy_nonneg (J Q : ℕ) (f : ℕ → ℝ) : 0 ≤ boxEnergy J Q f :=
  sum_nonneg fun _ _ => sum_nonneg fun _ _ => ladderEnergy_nonneg _ _ _ _

/-- **The twisted smooth-chain bound**: the smooth energy pays the smooth variance with the box
gap and the within-`p`-fibre variance of the zero extension with the ladder excess, up to the
boundary and halo errors of `smoothVar_mul_le_of_box`. -/
theorem smoothVar_mul_add_le_smoothEnergy {Q X : ℕ} (hX : 2 ≤ X) {p : ℕ}
    (hp : p ∈ (range Q).filter Nat.Prime) (h : ℕ → ℝ) :
    (boxGap X - 4 * logSum Q / Real.sqrt (Real.sqrt X) -
        16 * logSum Q * ladderConstant Q / Real.log X) * smoothVar Q X h +
      (Real.log p * ladderMass p X - boxGap X) * pFibreVar X Q p (zeroExt Q X h) ≤
      (1 + 16 * logSum Q / Real.log X) * smoothEnergy Q X h := by
  have hpp := (mem_filter.mp hp).2
  have hX1 : 1 ≤ X := by omega
  obtain ⟨Z₀, hZ₀⟩ : ∃ Z : ℝ,
      Z = (Real.log p * ladderMass p X - boxGap X) * pFibreVar X Q p (zeroExt Q X h) := ⟨_, rfl⟩
  rw [← hZ₀]
  have hgap : boxGap X ≤ Real.log p * ladderMass p X := boxGap_le_ladder hpp hX1
  have hZ₀0 : 0 ≤ Z₀ := by
    rw [hZ₀]; exact mul_nonneg (by linarith) (pFibreVar_nonneg _ _ _ _)
  have hg : 0 < boxGap X := by
    rw [boxGap]
    have : (1 / 2 : ℝ) ^ (X + 1) < 1 := pow_lt_one₀ (by norm_num) (by norm_num) (by omega)
    have := Real.log_pos (show (1 : ℝ) < 2 by norm_num)
    nlinarith
  have hV0 : 0 ≤ smoothVar Q X h := wVar_nonneg fun _ _ => by positivity
  have hZ₀V : Z₀ ≤ Real.log p * ladderMass p X * smoothVar Q X h := by
    rw [hZ₀, ← sum_smoothBox_zeroExt_sq]
    have h1 := pFibreVar_le (J := X) hp (zeroExt Q X h)
    have h3 : 0 ≤ Real.log p * ladderMass p X := by linarith
    have h4 := pFibreVar_nonneg X Q p (zeroExt Q X h)
    calc (Real.log p * ladderMass p X - boxGap X) * pFibreVar X Q p (zeroExt Q X h)
        ≤ Real.log p * ladderMass p X * pFibreVar X Q p (zeroExt Q X h) :=
          mul_le_mul_of_nonneg_right (by linarith) h4
      _ ≤ _ := mul_le_mul_of_nonneg_left h1 h3
  have hES := boxGap_mul_boxVar_add_le hX1 hp (zeroExt Q X h)
  rw [← hZ₀] at hES
  have hVb := smoothVar_le_boxVar Q X h
  have hbox : (boxGap X + Z₀ / smoothVar Q X h) * smoothVar Q X h ≤
      boxEnergy X Q (zeroExt Q X h) := by
    by_cases hV : smoothVar Q X h = 0
    · rw [hV, mul_zero]; exact boxEnergy_nonneg _ _ _
    · rw [add_mul, div_mul_cancel₀ _ hV]
      have := mul_le_mul_of_nonneg_left hVb hg.le
      linarith
  have key := smoothVar_mul_le_of_box hX h hbox
  by_cases hV : smoothVar Q X h = 0
  · have hZ : Z₀ = 0 := by
      have := hZ₀V; rw [hV, mul_zero] at this; linarith
    rw [hV, hZ, mul_zero, zero_add]
    exact mul_nonneg (add_nonneg zero_le_one (div_nonneg (mul_nonneg (by norm_num)
      (logSum_nonneg Q)) (Real.log_natCast_nonneg X))) (smoothEnergy_nonneg _ _ _)
  · have e : (boxGap X + Z₀ / smoothVar Q X h - 4 * logSum Q / Real.sqrt (Real.sqrt X) -
        16 * logSum Q * ladderConstant Q / Real.log X) * smoothVar Q X h =
        (boxGap X - 4 * logSum Q / Real.sqrt (Real.sqrt X) -
          16 * logSum Q * ladderConstant Q / Real.log X) * smoothVar Q X h + Z₀ := by
      field_simp
      ring
    rw [e] at key
    exact key

/-! ### 6. Fibration identities on `[1, N]` -/

theorem not_dvd_of_mem_roughInterval {Q X p b : ℕ} (hp : p.Prime) (hpQ : p < Q)
    (hb : b ∈ roughInterval Q X) : ¬ p ∣ b := fun hdvd => by
  have := (mem_roughInterval.mp hb).2.2 p hp hdvd
  omega

/-- The flip of a prime below the cutoff is constant along rough fibres. -/
theorem finiteFlip_mul_rough {Q X p a b : ℕ} (hp : p.Prime) (hpQ : p < Q) (ha : a ≠ 0)
    (hb : b ∈ roughInterval Q X) : finiteFlip {p} (a * b) = finiteFlip {p} a := by
  have hb0 : b ≠ 0 := by have := (mem_roughInterval.mp hb).1; omega
  have hb1 : finiteFlip {p} b = 1 := finiteFlip_eq_one_of_coprime fun q hq => by
    rw [mem_singleton] at hq
    subst hq
    exact not_dvd_of_mem_roughInterval hp hpQ hb
  rw [(finiteFlip_isSignGauge {p}).mul ha hb0, hb1, mul_one]

/-- A weight constant along rough fibres factors out of the smooth–rough decomposition. -/
theorem sum_one_div_mul_eq_smooth_rough (Q N : ℕ) (s y : ℕ → ℝ)
    (hs : ∀ a b, a ≠ 0 → b ∈ roughInterval Q (N / a) → s (a * b) = s a) :
    ∑ n ∈ Icc 1 N, 1 / (n : ℝ) * (s n * y n) =
      ∑ a ∈ smoothSet Q N, 1 / (a : ℝ) *
        (s a * ∑ b ∈ roughInterval Q (N / a), 1 / (b : ℝ) * y (a * b)) := by
  rw [sum_Icc_eq_smooth_rough Q N]
  refine sum_congr rfl fun a ha => ?_
  have ha1 := (mem_smoothSet.mp ha).1
  rw [mul_sum, mul_sum]
  refine sum_congr rfl fun b hb => ?_
  rw [hs a b (by omega) hb]
  push_cast
  have ha0 : (a : ℝ) ≠ 0 := by exact_mod_cast (show a ≠ 0 by omega)
  have hb0 : (b : ℝ) ≠ 0 := by exact_mod_cast (show b ≠ 0 by have := (mem_roughInterval.mp hb).1; omega)
  field_simp

/-- The fibre sum of `y` is the rough mass times the fibre mean. -/
theorem sum_fibre_eq_roughHarmonic_mul {Q N a : ℕ} (ha : 1 ≤ a) (haN : a ≤ N) (y : ℕ → ℝ) :
    ∑ b ∈ roughInterval Q (N / a), 1 / (b : ℝ) * y (a * b) =
      roughHarmonic Q (N / a) * fibreMean Q N y a := by
  have hNa : 1 ≤ N / a := (Nat.le_div_iff_mul_le (by omega)).mpr (by omega)
  have hR : roughHarmonic Q (N / a) ≠ 0 := (lt_of_lt_of_le one_pos (one_le_roughHarmonic Q hNa)).ne'
  rw [fibreMean, wMean, roughHarmonic] at *
  rw [mul_div_cancel₀ _ hR]

/-- `Σ_n z_n² = Σ_n (1/n) (√n z_n)²`. -/
theorem sum_sq_eq_sum_one_div_poleGauge_sq (N : ℕ) (z : ℕ → ℝ) :
    ∑ n ∈ Icc 1 N, z n ^ 2 = ∑ n ∈ Icc 1 N, 1 / (n : ℝ) * poleGauge z n ^ 2 := by
  refine sum_congr rfl fun n hn => ?_
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
  rw [poleGauge, mul_pow, Real.sq_sqrt hn0.le]
  field_simp

/-- The flipped pole constraint in the pole gauge. -/
theorem sum_flip_poleGauge_eq (N p : ℕ) (z : ℕ → ℝ) :
    ∑ n ∈ Icc 1 N, finiteFlip {p} n * z n / Real.sqrt n =
      ∑ n ∈ Icc 1 N, 1 / (n : ℝ) * (finiteFlip {p} n * poleGauge z n) := by
  refine sum_congr rfl fun n hn => ?_
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
  rw [poleGauge]
  set s := Real.sqrt n with hsdef
  have hs : s ≠ 0 := (Real.sqrt_pos.mpr hn0).ne'
  have hsq : (n : ℝ) = s * s := (Real.mul_self_sqrt hn0.le).symm
  rw [hsq]
  field_simp

/-- The second moment of the harmonic measure against the squared mean: for `N ≥ 1`,
`Σ (1/n) y_n² ≤ Σ (1/n)(y_n − c)² + (Σ (1/n) y_n)²/H_N`. -/
theorem sum_one_div_mul_sq_le {N : ℕ} (hN : 1 ≤ N) (y : ℕ → ℝ) (c : ℝ) :
    ∑ n ∈ Icc 1 N, 1 / (n : ℝ) * y n ^ 2 ≤ ∑ n ∈ Icc 1 N, 1 / (n : ℝ) * (y n - c) ^ 2 +
      (∑ n ∈ Icc 1 N, 1 / (n : ℝ) * y n) ^ 2 / ∑ n ∈ Icc 1 N, 1 / (n : ℝ) := by
  have hH : 0 < ∑ n ∈ Icc 1 N, 1 / (n : ℝ) := by
    have := single_le_sum (f := fun n : ℕ => 1 / (n : ℝ)) (fun n _ => by positivity)
      (mem_Icc.mpr ⟨le_rfl, hN⟩)
    simp only [Nat.cast_one, div_one] at this
    linarith
  have e : ∀ n ∈ Icc 1 N, 1 / (n : ℝ) * (y n - c) ^ 2 =
      1 / (n : ℝ) * y n ^ 2 - 2 * c * (1 / (n : ℝ) * y n) + c ^ 2 * (1 / (n : ℝ)) :=
    fun n _ => by ring
  rw [sum_congr rfl e, sum_add_distrib, sum_sub_distrib, ← mul_sum, ← mul_sum]
  set Y := ∑ n ∈ Icc 1 N, 1 / (n : ℝ) * y n
  set H := ∑ n ∈ Icc 1 N, 1 / (n : ℝ)
  have : 2 * c * Y - c ^ 2 * H ≤ Y ^ 2 / H := by
    rw [le_div_iff₀ hH]
    nlinarith [sq_nonneg (Y - c * H)]
  linarith

/-- The variation of the rough masses across `a ≤ X` is bounded by `(1 + log X)³` times the
smooth variance. -/
theorem sum_var_sq_le {Q N X : ℕ} (hX1 : 1 ≤ X) (hXN : X ≤ N) (s h : ℕ → ℝ)
    (hs : ∀ a, s a ^ 2 ≤ 1) (c : ℝ) :
    (∑ a ∈ smoothSet Q X, 1 / (a : ℝ) *
        (s a * ((roughHarmonic Q (N / a) - roughHarmonic Q (N / X)) * (h a - c)))) ^ 2 ≤
      (1 + Real.log X) ^ 3 * ∑ a ∈ smoothSet Q X, 1 / (a : ℝ) * (h a - c) ^ 2 := by
  have hL0 : 0 ≤ Real.log X := Real.log_natCast_nonneg X
  have hshell : ∀ a ∈ smoothSet Q X,
      0 ≤ roughHarmonic Q (N / a) - roughHarmonic Q (N / X) ∧
        roughHarmonic Q (N / a) - roughHarmonic Q (N / X) ≤ 1 + Real.log X := by
    intro a ha
    obtain ⟨ha1, haX, -⟩ := mem_smoothSet.mp ha
    have h1 : roughHarmonic Q (N / X) ≤ roughHarmonic Q (N / a) :=
      roughHarmonic_mono (Nat.div_le_div_left haX (by omega))
    have h2 : roughHarmonic Q (N / a) ≤ roughHarmonic Q N := roughHarmonic_mono (Nat.div_le_self N a)
    have h3 := roughHarmonic_sub_div_le Q N hX1
    exact ⟨by linarith, by linarith⟩
  have hCS := sum_sq_le_sum_mul_sum_of_sq_le_mul (smoothSet Q X)
    (r := fun a => 1 / (a : ℝ) *
      (s a * ((roughHarmonic Q (N / a) - roughHarmonic Q (N / X)) * (h a - c))))
    (f := fun a => 1 / (a : ℝ) * (roughHarmonic Q (N / a) - roughHarmonic Q (N / X)) ^ 2)
    (g := fun a => 1 / (a : ℝ) * (h a - c) ^ 2)
    (fun a _ => by positivity) (fun a _ => by positivity)
    (fun a _ => by
      have := hs a
      have h0 : 0 ≤ (1 / (a : ℝ)) ^ 2 * ((roughHarmonic Q (N / a) - roughHarmonic Q (N / X)) ^ 2 *
        (h a - c) ^ 2) := by positivity
      nlinarith)
  have hsum : ∑ a ∈ smoothSet Q X, 1 / (a : ℝ) * (roughHarmonic Q (N / a) - roughHarmonic Q (N / X)) ^ 2 ≤
      (1 + Real.log X) ^ 3 := by
    have hZ : ∑ a ∈ smoothSet Q X, 1 / (a : ℝ) ≤ 1 + Real.log X := by
      have := roughHarmonic_le_one_add_log 0 X
      rw [roughHarmonic, roughInterval_zero] at this
      refine le_trans (sum_le_sum_of_subset_of_nonneg (fun a ha => ?_) fun _ _ _ => by positivity) this
      exact mem_Icc.mpr ⟨(mem_smoothSet.mp ha).1, (mem_smoothSet.mp ha).2.1⟩
    calc ∑ a ∈ smoothSet Q X, 1 / (a : ℝ) * (roughHarmonic Q (N / a) - roughHarmonic Q (N / X)) ^ 2
        ≤ ∑ a ∈ smoothSet Q X, 1 / (a : ℝ) * (1 + Real.log X) ^ 2 := by
          refine sum_le_sum fun a ha => ?_
          obtain ⟨h0, h1⟩ := hshell a ha
          exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h0 h1 2) (by positivity)
      _ = (1 + Real.log X) ^ 2 * ∑ a ∈ smoothSet Q X, 1 / (a : ℝ) := by rw [mul_comm, sum_mul]
      _ ≤ (1 + Real.log X) ^ 2 * (1 + Real.log X) := mul_le_mul_of_nonneg_left hZ (by positivity)
      _ = (1 + Real.log X) ^ 3 := by ring
  refine hCS.trans (mul_le_mul_of_nonneg_right hsum (sum_nonneg fun a _ => by positivity))

/-- The halo above the horizon: the squared pairing over `a > X` is bounded by the total rough
mass times the halo energy. -/
theorem sum_halo_sq_le {Q N X : ℕ} (hX2 : 2 ≤ X) (s y : ℕ → ℝ) (hs : ∀ a, s a ^ 2 ≤ 1) (c : ℝ) :
    (∑ a ∈ (smoothSet Q N).filter (fun a => ¬ a ≤ X), 1 / (a : ℝ) *
        (s a * (roughHarmonic Q (N / a) * (fibreMean Q N y a - c)))) ^ 2 ≤
      (∑ a ∈ smoothSet Q N, 1 / (a : ℝ) * roughHarmonic Q (N / a)) *
        (1 / Real.log X * (2 * walkEnergy N (fun t => t.minFac < Q) y +
          2 * ladderConstant Q * ∑ n ∈ Icc 1 N, 1 / (n : ℝ) * (y n - c) ^ 2)) := by
  have hL : 0 < Real.log X := Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  have hCS := sum_sq_le_sum_mul_sum_of_sq_le_mul ((smoothSet Q N).filter (fun a => ¬ a ≤ X))
    (r := fun a => 1 / (a : ℝ) * (s a * (roughHarmonic Q (N / a) * (fibreMean Q N y a - c))))
    (f := fun a => 1 / (a : ℝ) * roughHarmonic Q (N / a))
    (g := fun a => 1 / (a : ℝ) * (roughHarmonic Q (N / a) * (fibreMean Q N y a - c) ^ 2))
    (fun a _ => by have := roughHarmonic_nonneg Q (N / a); positivity)
    (fun a _ => by have := roughHarmonic_nonneg Q (N / a); positivity)
    (fun a _ => by
      have := hs a
      have h0 : 0 ≤ (1 / (a : ℝ)) ^ 2 * (roughHarmonic Q (N / a) ^ 2 *
        (fibreMean Q N y a - c) ^ 2) := by positivity
      nlinarith)
  have hf : ∑ a ∈ (smoothSet Q N).filter (fun a => ¬ a ≤ X), 1 / (a : ℝ) * roughHarmonic Q (N / a) ≤
      ∑ a ∈ smoothSet Q N, 1 / (a : ℝ) * roughHarmonic Q (N / a) :=
    sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
      fun a _ _ => by have := roughHarmonic_nonneg Q (N / a); positivity
  have hg : ∑ a ∈ (smoothSet Q N).filter (fun a => ¬ a ≤ X),
      1 / (a : ℝ) * (roughHarmonic Q (N / a) * (fibreMean Q N y a - c) ^ 2) ≤
      1 / Real.log X * (2 * walkEnergy N (fun t => t.minFac < Q) y +
        2 * ladderConstant Q * ∑ n ∈ Icc 1 N, 1 / (n : ℝ) * (y n - c) ^ 2) := by
    set S : ℕ → ℝ := fun a => ∑ b ∈ roughInterval Q (N / a), 1 / (b : ℝ) * (y (a * b) - c) ^ 2
    have hS0 : ∀ a, 0 ≤ S a := fun a => sum_nonneg fun b _ => by positivity
    have hhalo := sum_log_mul_fibre_le Q N y c
    calc ∑ a ∈ (smoothSet Q N).filter (fun a => ¬ a ≤ X),
          1 / (a : ℝ) * (roughHarmonic Q (N / a) * (fibreMean Q N y a - c) ^ 2)
        ≤ ∑ a ∈ (smoothSet Q N).filter (fun a => ¬ a ≤ X),
            1 / Real.log X * (1 / (a : ℝ) * Real.log a * S a) := by
          refine sum_le_sum fun a ha => ?_
          have hXa : X < a := not_le.mp (mem_filter.mp ha).2
          have hJ : roughHarmonic Q (N / a) * (fibreMean Q N y a - c) ^ 2 ≤ S a :=
            sum_mul_sq_wMean_sub_le (s := roughInterval Q (N / a))
              (w := fun b : ℕ => 1 / (b : ℝ)) (v := fun b => y (a * b)) (fun b _ => by positivity) c
          have hla : Real.log X ≤ Real.log a :=
            Real.log_le_log (by exact_mod_cast (show 0 < X by omega)) (by exact_mod_cast hXa.le)
          have h1 : S a ≤ Real.log a / Real.log X * S a := by
            have : 1 ≤ Real.log a / Real.log X := by rw [le_div_iff₀ hL]; linarith
            nlinarith [hS0 a]
          calc 1 / (a : ℝ) * (roughHarmonic Q (N / a) * (fibreMean Q N y a - c) ^ 2)
              ≤ 1 / (a : ℝ) * S a := mul_le_mul_of_nonneg_left hJ (by positivity)
            _ ≤ 1 / (a : ℝ) * (Real.log a / Real.log X * S a) :=
                mul_le_mul_of_nonneg_left h1 (by positivity)
            _ = 1 / Real.log X * (1 / (a : ℝ) * Real.log a * S a) := by ring
      _ = 1 / Real.log X * ∑ a ∈ (smoothSet Q N).filter (fun a => ¬ a ≤ X),
            1 / (a : ℝ) * Real.log a * S a := by rw [mul_sum]
      _ ≤ 1 / Real.log X * ∑ a ∈ smoothSet Q N, 1 / (a : ℝ) * Real.log a * S a := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun a _ _ => by
            have := Real.log_natCast_nonneg a
            have := hS0 a
            positivity
      _ ≤ _ := mul_le_mul_of_nonneg_left hhalo (by positivity)
  have hf0 : 0 ≤ ∑ a ∈ (smoothSet Q N).filter (fun a => ¬ a ≤ X),
      1 / (a : ℝ) * roughHarmonic Q (N / a) :=
    sum_nonneg fun a _ => by have := roughHarmonic_nonneg Q (N / a); positivity
  have hg0 : 0 ≤ 1 / Real.log X * (2 * walkEnergy N (fun t => t.minFac < Q) y +
      2 * ladderConstant Q * ∑ n ∈ Icc 1 N, 1 / (n : ℝ) * (y n - c) ^ 2) := by
    have := walkEnergy_nonneg N (fun t => t.minFac < Q) y
    have := ladderConstant_nonneg Q
    have : 0 ≤ ∑ n ∈ Icc 1 N, 1 / (n : ℝ) * (y n - c) ^ 2 := sum_nonneg fun n _ => by positivity
    positivity
  exact hCS.trans (mul_le_mul hf hg (sum_nonneg fun a _ => by
    have := roughHarmonic_nonneg Q (N / a); positivity) (sum_nonneg fun a _ => by
    have := roughHarmonic_nonneg Q (N / a); positivity))

/-- `W ≥ G · V`: the centred second moment dominates the rough mass at the horizon times the
smooth variance of the fibre means. -/
theorem roughHarmonic_mul_smoothVar_le {Q N X : ℕ} (hXN : X ≤ N) (y : ℕ → ℝ) :
    roughHarmonic Q (N / X) * smoothVar Q X (fibreMean Q N y) ≤
      ∑ n ∈ Icc 1 N, 1 / (n : ℝ) *
        (y n - wMean (smoothSet Q X) (fun a => 1 / (a : ℝ)) (fibreMean Q N y)) ^ 2 := by
  set c := wMean (smoothSet Q X) (fun a => 1 / (a : ℝ)) (fibreMean Q N y)
  have hsub : smoothSet Q X ⊆ smoothSet Q N := fun a ha => by
    obtain ⟨h1, h2, h3⟩ := mem_smoothSet.mp ha
    exact mem_smoothSet.mpr ⟨h1, h2.trans hXN, h3⟩
  have hG0 := roughHarmonic_nonneg Q (N / X)
  calc roughHarmonic Q (N / X) * smoothVar Q X (fibreMean Q N y)
      = ∑ a ∈ smoothSet Q X, 1 / (a : ℝ) * (roughHarmonic Q (N / X) * (fibreMean Q N y a - c) ^ 2) := by
        rw [smoothVar, wVar, mul_sum]
        exact sum_congr rfl fun a _ => by ring
    _ ≤ ∑ a ∈ smoothSet Q X, 1 / (a : ℝ) * (roughHarmonic Q (N / a) * (fibreMean Q N y a - c) ^ 2) := by
        refine sum_le_sum fun a ha => ?_
        obtain ⟨ha1, haX, -⟩ := mem_smoothSet.mp ha
        have : roughHarmonic Q (N / X) ≤ roughHarmonic Q (N / a) :=
          roughHarmonic_mono (Nat.div_le_div_left haX (by omega))
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right this (sq_nonneg _)) (by positivity)
    _ ≤ ∑ a ∈ smoothSet Q X, 1 / (a : ℝ) *
          ∑ b ∈ roughInterval Q (N / a), 1 / (b : ℝ) * (y (a * b) - c) ^ 2 := by
        refine sum_le_sum fun a ha => ?_
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact sum_mul_sq_wMean_sub_le (s := roughInterval Q (N / a))
          (w := fun b : ℕ => 1 / (b : ℝ)) (v := fun b => y (a * b)) (fun b _ => by positivity) c
    _ ≤ ∑ a ∈ smoothSet Q N, 1 / (a : ℝ) *
          ∑ b ∈ roughInterval Q (N / a), 1 / (b : ℝ) * (y (a * b) - c) ^ 2 :=
        sum_le_sum_of_subset_of_nonneg hsub fun a _ _ =>
          mul_nonneg (by positivity) (sum_nonneg fun b _ => by positivity)
    _ = _ := by
        rw [sum_Icc_eq_smooth_rough Q N]
        refine sum_congr rfl fun a _ => ?_
        rw [mul_sum]
        refine sum_congr rfl fun b _ => ?_
        push_cast
        ring

/-! ### 7. The twisted Poincaré inequality -/

/-- **The twisted smooth-energy bound in its final form**: with the horizon in range,
`E_X(h) ≥ g₁ V + Z`, where `Z = (log p · W_p(X) − g_X) V_p(h⁰)/(1 + e₂)` is nonnegative and at
most `2 log p · V`. -/
theorem smoothEnergy_ge_twisted {p Q X : ℕ} (hp : p.Prime) (hpmem : p ∈ (range Q).filter Nat.Prime)
    (hX2 : 2 ≤ X) {g₁ : ℝ} (hg₁0 : 0 < g₁)
    (hcoef : g₁ * (1 + 16 * logSum Q / Real.log X) ≤ boxGap X -
      4 * logSum Q / Real.sqrt (Real.sqrt X) - 16 * logSum Q * ladderConstant Q / Real.log X)
    (h : ℕ → ℝ) :
    0 ≤ (Real.log p * ladderMass p X - boxGap X) * pFibreVar X Q p (zeroExt Q X h) /
        (1 + 16 * logSum Q / Real.log X) ∧
      (Real.log p * ladderMass p X - boxGap X) * pFibreVar X Q p (zeroExt Q X h) /
        (1 + 16 * logSum Q / Real.log X) ≤ 2 * Real.log p * smoothVar Q X h ∧
      g₁ * smoothVar Q X h + (Real.log p * ladderMass p X - boxGap X) *
        pFibreVar X Q p (zeroExt Q X h) / (1 + 16 * logSum Q / Real.log X) ≤
          smoothEnergy Q X h := by
  have hlp0 : 0 ≤ Real.log p := Real.log_natCast_nonneg p
  have hX1 : 1 ≤ X := by omega
  have hL0 : 0 < Real.log X := Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  have hV0 : 0 ≤ smoothVar Q X h := wVar_nonneg fun _ _ => by positivity
  have hVp0 := pFibreVar_nonneg X Q p (zeroExt Q X h)
  have hlM2 := ladderMass_le_two hp.two_le X
  have hlM1 := one_le_ladderMass (p := p) X
  have he₂0 : 0 ≤ 16 * logSum Q / Real.log X := by
    have := logSum_nonneg Q; positivity
  have h1e : 0 < 1 + 16 * logSum Q / Real.log X := by linarith
  have hgap := boxGap_le_ladder hp hX1
  have hES := smoothVar_mul_add_le_smoothEnergy hX2 hpmem h
  refine ⟨div_nonneg (mul_nonneg (by linarith) hVp0) h1e.le, ?_, ?_⟩
  · rw [div_le_iff₀ h1e, ← sum_smoothBox_zeroExt_sq]
    have h1 := pFibreVar_le (J := X) hpmem (zeroExt Q X h)
    have hbg : 0 < boxGap X := by
      rw [boxGap]
      have : (1 / 2 : ℝ) ^ (X + 1) < 1 := pow_lt_one₀ (by norm_num) (by norm_num) (by omega)
      have := Real.log_pos (show (1 : ℝ) < 2 by norm_num)
      nlinarith
    have h3 : 0 ≤ Real.log p * ladderMass p X := by positivity
    have hS0 : 0 ≤ ∑ a ∈ smoothBox X Q, 1 / (a : ℝ) * zeroExt Q X h a ^ 2 :=
      sum_nonneg fun a _ => by positivity
    have h4 : Real.log p * ladderMass p X ≤ Real.log p * 2 := mul_le_mul_of_nonneg_left hlM2 hlp0
    calc (Real.log p * ladderMass p X - boxGap X) * pFibreVar X Q p (zeroExt Q X h)
        ≤ Real.log p * ladderMass p X * pFibreVar X Q p (zeroExt Q X h) :=
          mul_le_mul_of_nonneg_right (by linarith) hVp0
      _ ≤ Real.log p * ladderMass p X * ∑ a ∈ smoothBox X Q, 1 / (a : ℝ) * zeroExt Q X h a ^ 2 :=
          mul_le_mul_of_nonneg_left h1 h3
      _ ≤ Real.log p * 2 * ∑ a ∈ smoothBox X Q, 1 / (a : ℝ) * zeroExt Q X h a ^ 2 :=
          mul_le_mul_of_nonneg_right h4 hS0
      _ = 2 * Real.log p * ∑ a ∈ smoothBox X Q, 1 / (a : ℝ) * zeroExt Q X h a ^ 2 := by ring
      _ ≤ 2 * Real.log p * (∑ a ∈ smoothBox X Q, 1 / (a : ℝ) * zeroExt Q X h a ^ 2) *
            (1 + 16 * logSum Q / Real.log X) :=
          le_mul_of_one_le_right (by positivity) (by linarith)
  · have e : (1 + 16 * logSum Q / Real.log X) * (g₁ * smoothVar Q X h +
        (Real.log p * ladderMass p X - boxGap X) * pFibreVar X Q p (zeroExt Q X h) /
          (1 + 16 * logSum Q / Real.log X)) =
        g₁ * (1 + 16 * logSum Q / Real.log X) * smoothVar Q X h +
          (Real.log p * ladderMass p X - boxGap X) * pFibreVar X Q p (zeroExt Q X h) := by
      rw [mul_add, mul_div_cancel₀ _ h1e.ne']; ring
    refine le_of_mul_le_mul_left ?_ h1e
    rw [e]
    have := mul_le_mul_of_nonneg_right hcoef hV0
    linarith

/-- **The two-scale inequality with the `p`-sector term.** With the cutoff `Q > p`, the horizon
`X` and the rough mass at the horizon in range, every `z` satisfies
`(2 log 2 − η/4) W + G Z ≤ D_N(z)`, where `W` is the centred second moment of the pole gauge,
`G` the rough mass at the horizon and `Z` the paid `p`-sector excess. -/
theorem two_scale_twisted {p Q X N : ℕ} (hp : p.Prime) (hpmem : p ∈ (range Q).filter Nat.Prime)
    (hQ2 : 2 ≤ Q) (hX2 : 2 ≤ X) (hXN : X ≤ N) {η ε g₁ Tmax τ K : ℝ} (hη : 0 < η) (hη1 : η ≤ 1)
    (hεdef : ε = η / 4)
    (hg₁def : g₁ = 2 * Real.log 2 - ε / 2) (hTdef : Tmax = 2 * Real.log 2 + 2 * Real.log p)
    (hτ0 : 0 < τ) (hτ1 : τ ≤ 1 / 2) (hτT : τ * (Tmax ^ 2 + 4 * Tmax) ≤ ε / 2)
    (hK : 0 < K) (hKt : ∀ Q X : ℕ, ∀ f : ℕ → ℝ, harmonicVar Q X f ≤ K * glauberForm Q X f)
    (hκ : K / Real.log Q * (4 * Tmax) ≤ 1)
    (hML : 2 * ladderConstant Q / Real.log X ≤ τ) (h2L : 2 / Real.log X ≤ τ)
    (hcoef : g₁ * (1 + 16 * logSum Q / Real.log X) ≤ boxGap X -
      4 * logSum Q / Real.sqrt (Real.sqrt X) - 16 * logSum Q * ladderConstant Q / Real.log X)
    (hGr : (1 + Real.log X) / τ + 16 * (1 + 1 / τ) * logSum Q / g₁ ≤ roughHarmonic Q (N / X))
    (z : ℕ → ℝ) :
    (2 * Real.log 2 - η / 4) * ∑ n ∈ Icc 1 N, 1 / (n : ℝ) * (poleGauge z n -
        wMean (smoothSet Q X) (fun a => 1 / (a : ℝ)) (fibreMean Q N (poleGauge z))) ^ 2 +
      roughHarmonic Q (N / X) * ((Real.log p * ladderMass p X - boxGap X) *
        pFibreVar X Q p (zeroExt Q X (fibreMean Q N (poleGauge z))) /
          (1 + 16 * logSum Q / Real.log X)) ≤ poleDefect N z := by
  have hl2 := Real.log_two_gt_d9
  have hl2' := Real.log_two_lt_d9
  have hlp0 : 0 ≤ Real.log p := Real.log_natCast_nonneg p
  have hε0 : 0 < ε := by rw [hεdef]; positivity
  have hg₁0 : 0 < g₁ := by rw [hg₁def, hεdef]; linarith
  have hX1 : 1 ≤ X := by omega
  have hL0 : 0 < Real.log X := Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  set y := poleGauge z with hy
  set h := fibreMean Q N y with hh
  set c := wMean (smoothSet Q X) (fun a => 1 / (a : ℝ)) h with hc
  have hV0 : 0 ≤ smoothVar Q X h := wVar_nonneg fun _ _ => by positivity
  have hW0 : 0 ≤ ∑ n ∈ Icc 1 N, 1 / (n : ℝ) * (y n - c) ^ 2 := sum_nonneg fun n _ => by positivity
  obtain ⟨hZ0, hZV, hA'⟩ := smoothEnergy_ge_twisted hp hpmem hX2 hg₁0 hcoef h
  obtain ⟨Z, hZdef⟩ : ∃ Z : ℝ, Z =
      (Real.log p * ladderMass p X - boxGap X) * pFibreVar X Q p (zeroExt Q X h) /
        (1 + 16 * logSum Q / Real.log X) := ⟨_, rfl⟩
  rw [← hZdef] at hZ0 hZV hA' ⊢
  -- the two-scale inequality with the shifted constant
  obtain ⟨g₁', hg₁'def⟩ : ∃ g : ℝ, g = g₁ + Z / smoothVar Q X h := ⟨_, rfl⟩
  have hZVdiv : Z / smoothVar Q X h ≤ 2 * Real.log p := by
    by_cases hV : smoothVar Q X h = 0
    · rw [hV, div_zero]; positivity
    · rw [div_le_iff₀ (lt_of_le_of_ne hV0 (Ne.symm hV))]; exact hZV
  have hZVdiv0 : 0 ≤ Z / smoothVar Q X h := div_nonneg hZ0 hV0
  have hg₁'0 : 0 < g₁' := by rw [hg₁'def]; linarith
  have hg₁'T : g₁' ≤ Tmax := by rw [hg₁'def, hTdef, hg₁def]; linarith
  have hA : g₁' * smoothVar Q X h ≤ smoothEnergy Q X h := by
    rw [hg₁'def]
    by_cases hV : smoothVar Q X h = 0
    · rw [hV, mul_zero]; exact smoothEnergy_nonneg _ _ _
    · rw [add_mul, div_mul_cancel₀ _ hV]; exact hA'
  have hcore := two_scale_le hX2 hXN hg₁'0 hτ0 y hA
  rw [← hh, ← hc] at hcore
  have hU := sum_fibreVar_le hK.le hKt hQ2 N y
  have hshell : roughHarmonic Q N ≤ roughHarmonic Q (N / X) + (1 + Real.log X) := by
    have := roughHarmonic_sub_div_le Q N hX1; linarith
  obtain ⟨hρ, hcU⟩ := ratio_bounds hτ0 hg₁0 (logSum_nonneg Q) hL0.le hshell hGr hτ1
  have hcU' : roughHarmonic Q N / roughHarmonic Q (N / X) *
      ((1 + 1 / τ) * (8 * logSum Q / roughHarmonic Q (N / X))) ≤ g₁' := by
    rw [hg₁'def]; linarith
  have hW := two_scale_arith hε0 (by rw [hg₁'def, hg₁def]; linarith) hg₁'T hτ0 hτ1 hτT hML h2L
    hW0 (sum_nonneg fun a _ => mul_nonneg (by positivity) (harmonicVar_nonneg _ _ _))
    (walkEnergy_nonneg _ _ _) (walkEnergy_nonneg _ _ _) hρ hcU' hκ hU hcore
  -- `W ≥ G V`, hence `(Z/V) W ≥ G Z`
  have hWV := roughHarmonic_mul_smoothVar_le (Q := Q) hXN y
  rw [← hh, ← hc] at hWV
  have hGZ : roughHarmonic Q (N / X) * Z ≤ Z / smoothVar Q X h *
      ∑ n ∈ Icc 1 N, 1 / (n : ℝ) * (y n - c) ^ 2 := by
    by_cases hV : smoothVar Q X h = 0
    · have hZ : Z = 0 := by
        have := hZV; rw [hV, mul_zero] at this; linarith
      rw [hZ, zero_div, zero_mul, mul_zero]
    · calc roughHarmonic Q (N / X) * Z = Z / smoothVar Q X h *
            (roughHarmonic Q (N / X) * smoothVar Q X h) := by field_simp; ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hWV hZVdiv0
  rw [← walkEnergy_small_add_large Q N z, ← hy]
  have : g₁' - ε / 2 = 2 * Real.log 2 - η / 4 + Z / smoothVar Q X h := by
    rw [hg₁'def, hg₁def, hεdef]; ring
  rw [this, add_mul] at hW
  linarith

/-- **The constraint data.** For `z` orthogonal to the flipped pole, the harmonic mean `Y` of
the pole gauge, its smooth mean `c`, and the signed count `S_N` are tied by `c S_N = −A`,
`Y = c H_N + B`, with `A`, `B` split at the horizon into a `p`-sector pairing, a variation term
and a halo term, each with its bound. -/
theorem constraint_data {p Q X N : ℕ} (hp : p.Prime) (hp11 : 11 ≤ p) (hpQ : p < Q) (hX2 : 2 ≤ X)
    (hXN : X ≤ N) (z : ℕ → ℝ)
    (hz : ∑ n ∈ Icc 1 N, finiteFlip {p} n * z n / Real.sqrt n = 0) :
    ∃ A B P Av Ah Bv Bh : ℝ,
      ∑ n ∈ Icc 1 N, 1 / (n : ℝ) * poleGauge z n =
          wMean (smoothSet Q X) (fun a => 1 / (a : ℝ)) (fibreMean Q N (poleGauge z)) *
            ∑ n ∈ Icc 1 N, 1 / (n : ℝ) + B ∧
      wMean (smoothSet Q X) (fun a => 1 / (a : ℝ)) (fibreMean Q N (poleGauge z)) *
          ∑ n ∈ Icc 1 N, finiteFlip {p} n / n = -A ∧
      ((p : ℝ) - 1) / ((p : ℝ) + 1) * ∑ n ∈ Icc 1 N, 1 / (n : ℝ) ≤
          ∑ n ∈ Icc 1 N, finiteFlip {p} n / n ∧
      A = roughHarmonic Q (N / X) * P + Av + Ah ∧ B = Bv + Bh ∧
      Av ^ 2 ≤ (1 + Real.log X) ^ 3 * (∑ n ∈ Icc 1 N, 1 / (n : ℝ) * (poleGauge z n -
        wMean (smoothSet Q X) (fun a => 1 / (a : ℝ)) (fibreMean Q N (poleGauge z))) ^ 2) /
          roughHarmonic Q (N / X) ∧
      Bv ^ 2 ≤ (1 + Real.log X) ^ 3 * (∑ n ∈ Icc 1 N, 1 / (n : ℝ) * (poleGauge z n -
        wMean (smoothSet Q X) (fun a => 1 / (a : ℝ)) (fibreMean Q N (poleGauge z))) ^ 2) /
          roughHarmonic Q (N / X) ∧
      Ah ^ 2 ≤ (∑ n ∈ Icc 1 N, 1 / (n : ℝ)) *
        ((2 * walkEnergy N (fun t => t.minFac < Q) (poleGauge z) +
          2 * ladderConstant Q * ∑ n ∈ Icc 1 N, 1 / (n : ℝ) * (poleGauge z n -
            wMean (smoothSet Q X) (fun a => 1 / (a : ℝ)) (fibreMean Q N (poleGauge z))) ^ 2) /
              Real.log X) ∧
      Bh ^ 2 ≤ (∑ n ∈ Icc 1 N, 1 / (n : ℝ)) *
        ((2 * walkEnergy N (fun t => t.minFac < Q) (poleGauge z) +
          2 * ladderConstant Q * ∑ n ∈ Icc 1 N, 1 / (n : ℝ) * (poleGauge z n -
            wMean (smoothSet Q X) (fun a => 1 / (a : ℝ)) (fibreMean Q N (poleGauge z))) ^ 2) /
              Real.log X) ∧
      P ^ 2 ≤ (1 - (((p : ℝ) - 1) / ((p : ℝ) + 1)) ^ 2) * ladderMass p X *
        (∑ a ∈ smoothSet Q X, 1 / (a : ℝ)) *
          pFibreVar X Q p (zeroExt Q X (fibreMean Q N (poleGauge z))) ∧
      roughHarmonic Q (N / X) * ∑ a ∈ smoothSet Q X, 1 / (a : ℝ) ≤
        ∑ n ∈ Icc 1 N, 1 / (n : ℝ) := by
  have hp11' : (11 : ℝ) ≤ p := by exact_mod_cast hp11
  have hX1 : 1 ≤ X := by omega
  have hN1 : 1 ≤ N := le_trans hX1 hXN
  have hL0 : 0 < Real.log X := Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  set y := poleGauge z with hy
  set h := fibreMean Q N y with hh
  set c := wMean (smoothSet Q X) (fun a => 1 / (a : ℝ)) h with hc
  have hG1 : 1 ≤ roughHarmonic Q (N / X) :=
    one_le_roughHarmonic Q ((Nat.le_div_iff_mul_le (by omega)).mpr (by omega))
  have hG0 : 0 < roughHarmonic Q (N / X) := by linarith
  have hVp0 := pFibreVar_nonneg X Q p (zeroExt Q X h)
  -- fibrations
  have hflip : ∀ a b, a ≠ 0 → b ∈ roughInterval Q (N / a) →
      finiteFlip {p} (a * b) = finiteFlip {p} a :=
    fun a b ha hb => finiteFlip_mul_rough hp hpQ ha hb
  have hone : ∀ a b, a ≠ 0 → b ∈ roughInterval Q (N / a) → (fun _ : ℕ => (1 : ℝ)) (a * b) =
      (fun _ : ℕ => (1 : ℝ)) a := fun _ _ _ _ => rfl
  have hfib : ∀ a ∈ smoothSet Q N, ∑ b ∈ roughInterval Q (N / a), 1 / (b : ℝ) * y (a * b) =
      roughHarmonic Q (N / a) * h a := fun a ha =>
    sum_fibre_eq_roughHarmonic_mul (mem_smoothSet.mp ha).1 (mem_smoothSet.mp ha).2.1 y
  have hzero : ∑ a ∈ smoothSet Q N, 1 / (a : ℝ) *
      (finiteFlip {p} a * (roughHarmonic Q (N / a) * h a)) = 0 := by
    rw [sum_flip_poleGauge_eq] at hz
    rw [sum_one_div_mul_eq_smooth_rough Q N (finiteFlip {p}) y hflip] at hz
    rw [← hz]
    exact sum_congr rfl fun a ha => by rw [hfib a ha]
  have hSN : ∑ n ∈ Icc 1 N, finiteFlip {p} n / n =
      ∑ a ∈ smoothSet Q N, 1 / (a : ℝ) * (finiteFlip {p} a * roughHarmonic Q (N / a)) := by
    have := sum_one_div_mul_eq_smooth_rough Q N (finiteFlip {p}) (fun _ => 1) hflip
    simp only [mul_one] at this
    rw [show ∑ n ∈ Icc 1 N, finiteFlip {p} n / n =
      ∑ n ∈ Icc 1 N, 1 / (n : ℝ) * finiteFlip {p} n from sum_congr rfl fun n _ => by ring]
    simpa only [roughHarmonic] using this
  have hHN : ∑ n ∈ Icc 1 N, 1 / (n : ℝ) =
      ∑ a ∈ smoothSet Q N, 1 / (a : ℝ) * roughHarmonic Q (N / a) := by
    have := sum_one_div_mul_eq_smooth_rough Q N (fun _ => 1) (fun _ => 1) hone
    simp only [mul_one, one_mul] at this
    simpa only [roughHarmonic] using this
  have hY : ∑ n ∈ Icc 1 N, 1 / (n : ℝ) * y n =
      ∑ a ∈ smoothSet Q N, 1 / (a : ℝ) * (roughHarmonic Q (N / a) * h a) := by
    have := sum_one_div_mul_eq_smooth_rough Q N (fun _ => 1) y hone
    simp only [one_mul] at this
    rw [this]
    exact sum_congr rfl fun a ha => by rw [hfib a ha]
  -- the centred sums
  obtain ⟨A, hAdef⟩ : ∃ A : ℝ, A = ∑ a ∈ smoothSet Q N, 1 / (a : ℝ) *
    (finiteFlip {p} a * (roughHarmonic Q (N / a) * (h a - c))) := ⟨_, rfl⟩
  obtain ⟨B, hBdef⟩ : ∃ B : ℝ, B = ∑ a ∈ smoothSet Q N, 1 / (a : ℝ) *
    (roughHarmonic Q (N / a) * (h a - c)) := ⟨_, rfl⟩
  have h4 : c * ∑ n ∈ Icc 1 N, finiteFlip {p} n / n = -A := by
    rw [hSN, hAdef, mul_sum]
    have e : ∑ a ∈ smoothSet Q N, 1 / (a : ℝ) * (finiteFlip {p} a * (roughHarmonic Q (N / a) * h a)) =
        ∑ a ∈ smoothSet Q N, (c * (1 / (a : ℝ) * (finiteFlip {p} a * roughHarmonic Q (N / a))) +
          1 / (a : ℝ) * (finiteFlip {p} a * (roughHarmonic Q (N / a) * (h a - c)))) :=
      sum_congr rfl fun a _ => by ring
    rw [e, sum_add_distrib] at hzero
    linarith
  have h3 : ∑ n ∈ Icc 1 N, 1 / (n : ℝ) * y n = c * ∑ n ∈ Icc 1 N, 1 / (n : ℝ) + B := by
    rw [hY, hHN, hBdef, mul_sum, ← sum_add_distrib]
    exact sum_congr rfl fun a _ => by ring
  have hS : ((p : ℝ) - 1) / ((p : ℝ) + 1) * ∑ n ∈ Icc 1 N, 1 / (n : ℝ) ≤
      ∑ n ∈ Icc 1 N, finiteFlip {p} n / n := by
    have := primeFlip_harmonicCorrelation_ge hp hN1
    have hpos := gaugeHarmonicSum_one_pos hN1
    rw [harmonicCorrelation, le_div_iff₀ hpos] at this
    simp only [gaugeHarmonicSum] at this hpos ⊢
    simpa using this
  -- the splittings at the horizon
  have hset : (smoothSet Q N).filter (fun a => a ≤ X) = smoothSet Q X := by
    ext a
    simp only [mem_filter, mem_smoothSet]
    constructor
    · rintro ⟨⟨h1, -, h3⟩, h4⟩; exact ⟨h1, h4, h3⟩
    · rintro ⟨h1, h2, h3⟩; exact ⟨⟨h1, h2.trans hXN, h3⟩, h2⟩
  obtain ⟨P, hPdef⟩ : ∃ P : ℝ, P = ∑ a ∈ smoothBox X Q, 1 / (a : ℝ) *
    (finiteFlip {p} a * zeroExt Q X h a) := ⟨_, rfl⟩
  have hPsmooth : P = ∑ a ∈ smoothSet Q X, 1 / (a : ℝ) * (finiteFlip {p} a * (h a - c)) := by
    rw [hPdef]
    have := sum_smoothBox_zeroExt_mul Q X h (finiteFlip {p})
    rw [← hc] at this
    rw [← this]
    exact sum_congr rfl fun a _ => by ring
  obtain ⟨Av, hAvdef⟩ : ∃ Av : ℝ, Av = ∑ a ∈ smoothSet Q X, 1 / (a : ℝ) *
    (finiteFlip {p} a * ((roughHarmonic Q (N / a) - roughHarmonic Q (N / X)) * (h a - c))) :=
    ⟨_, rfl⟩
  obtain ⟨Ah, hAhdef⟩ : ∃ Ah : ℝ, Ah = ∑ a ∈ (smoothSet Q N).filter (fun a => ¬ a ≤ X),
    1 / (a : ℝ) * (finiteFlip {p} a * (roughHarmonic Q (N / a) * (h a - c))) := ⟨_, rfl⟩
  obtain ⟨Bv, hBvdef⟩ : ∃ Bv : ℝ, Bv = ∑ a ∈ smoothSet Q X, 1 / (a : ℝ) *
    ((fun _ : ℕ => (1 : ℝ)) a * ((roughHarmonic Q (N / a) - roughHarmonic Q (N / X)) * (h a - c))) :=
    ⟨_, rfl⟩
  obtain ⟨Bh, hBhdef⟩ : ∃ Bh : ℝ, Bh = ∑ a ∈ (smoothSet Q N).filter (fun a => ¬ a ≤ X),
    1 / (a : ℝ) * ((fun _ : ℕ => (1 : ℝ)) a * (roughHarmonic Q (N / a) * (h a - c))) := ⟨_, rfl⟩
  have h5A : A = roughHarmonic Q (N / X) * P + Av + Ah := by
    rw [hAdef, ← sum_filter_add_sum_filter_not (smoothSet Q N) (fun a => a ≤ X), hset, hPsmooth,
      hAvdef, hAhdef, mul_sum, ← sum_add_distrib]
    congr 1
    exact sum_congr rfl fun a _ => by ring
  have hmean0 : ∑ a ∈ smoothSet Q X, 1 / (a : ℝ) * (h a - c) = 0 := by
    have := sum_smoothBox_zeroExt_eq_zero Q X h
    rw [sum_smoothBox_zeroExt_mul Q X h (fun _ => 1)] at this
    simpa [← hc] using this
  have h5B : B = Bv + Bh := by
    rw [hBdef, ← sum_filter_add_sum_filter_not (smoothSet Q N) (fun a => a ≤ X), hset, hBvdef,
      hBhdef]
    congr 1
    have e : ∑ a ∈ smoothSet Q X, 1 / (a : ℝ) * (roughHarmonic Q (N / a) * (h a - c)) =
        roughHarmonic Q (N / X) * ∑ a ∈ smoothSet Q X, 1 / (a : ℝ) * (h a - c) +
          ∑ a ∈ smoothSet Q X, 1 / (a : ℝ) *
            ((fun _ : ℕ => (1 : ℝ)) a * ((roughHarmonic Q (N / a) - roughHarmonic Q (N / X)) * (h a - c))) := by
      rw [mul_sum, ← sum_add_distrib]
      exact sum_congr rfl fun a _ => by ring
    rw [e, hmean0, mul_zero, zero_add]
  -- the error bounds
  have hsq1 : ∀ a, finiteFlip {p} a ^ 2 ≤ 1 := fun a => by
    rw [sq, singleFlip_mul_self]
  have hsq2 : ∀ a, (fun _ : ℕ => (1 : ℝ)) a ^ 2 ≤ 1 := fun _ => by norm_num
  have hWV := roughHarmonic_mul_smoothVar_le (Q := Q) hXN y
  rw [← hh, ← hc, smoothVar, wVar, ← hc] at hWV
  have hvar : ∀ s : ℕ → ℝ, (∀ a, s a ^ 2 ≤ 1) →
      (∑ a ∈ smoothSet Q X, 1 / (a : ℝ) *
        (s a * ((roughHarmonic Q (N / a) - roughHarmonic Q (N / X)) * (h a - c)))) ^ 2 ≤
      (1 + Real.log X) ^ 3 * (∑ n ∈ Icc 1 N, 1 / (n : ℝ) * (y n - c) ^ 2) /
        roughHarmonic Q (N / X) := by
    intro s hs
    rw [le_div_iff₀ hG0]
    have := sum_var_sq_le (Q := Q) hX1 hXN s h hs c
    calc _ ≤ (1 + Real.log X) ^ 3 * ∑ a ∈ smoothSet Q X, 1 / (a : ℝ) * (h a - c) ^ 2 := this
      _ = (1 + Real.log X) ^ 3 * (roughHarmonic Q (N / X) *
            ∑ a ∈ smoothSet Q X, 1 / (a : ℝ) * (h a - c) ^ 2) / roughHarmonic Q (N / X) := by
          field_simp
      _ ≤ _ := by
          rw [div_mul_eq_mul_div, mul_div_assoc', le_div_iff₀ hG0, div_mul_cancel₀ _ hG0.ne']
          exact mul_le_mul_of_nonneg_left hWV (by positivity)
  have hhalo : ∀ s : ℕ → ℝ, (∀ a, s a ^ 2 ≤ 1) →
      (∑ a ∈ (smoothSet Q N).filter (fun a => ¬ a ≤ X), 1 / (a : ℝ) *
        (s a * (roughHarmonic Q (N / a) * (h a - c)))) ^ 2 ≤
      (∑ n ∈ Icc 1 N, 1 / (n : ℝ)) * ((2 * walkEnergy N (fun t => t.minFac < Q) y +
        2 * ladderConstant Q * ∑ n ∈ Icc 1 N, 1 / (n : ℝ) * (y n - c) ^ 2) / Real.log X) := by
    intro s hs
    rw [hHN]
    have := sum_halo_sq_le (Q := Q) (N := N) hX2 s y hs c
    rw [← hh] at this
    convert this using 2
    ring
  -- the `p`-sector bound
  have hP : P ^ 2 ≤ (1 - (((p : ℝ) - 1) / ((p : ℝ) + 1)) ^ 2) * ladderMass p X *
      (∑ a ∈ smoothSet Q X, 1 / (a : ℝ)) * pFibreVar X Q p (zeroExt Q X h) := by
    have hmean := sum_smoothBox_zeroExt_eq_zero Q X h
    have hvan : ∀ n, X < n → zeroExt Q X h n = 0 := fun n hn => by
      rw [zeroExt, if_neg (not_le.mpr hn)]
    have hpmem : p ∈ (range Q).filter Nat.Prime := mem_filter.mpr ⟨mem_range.mpr hpQ, hp⟩
    have := sum_flip_mul_sq_le (X := X) hpmem hmean hvan
    rw [← hPdef] at this
    refine this.trans ?_
    have hT : ∑ u ∈ ((smoothBox X Q).filter (fun u => ¬ p ∣ u)).filter (· ≤ X), 1 / (u : ℝ) ≤
        ∑ a ∈ smoothSet Q X, 1 / (a : ℝ) := by
      refine sum_le_sum_of_subset_of_nonneg (fun u hu => ?_) fun _ _ _ => by positivity
      obtain ⟨hu', huX⟩ := mem_filter.mp hu
      obtain ⟨huB, -⟩ := mem_filter.mp hu'
      exact mem_smoothSet.mpr ⟨(mem_smoothBox.mp huB).1, huX, (mem_smoothBox.mp huB).2.1⟩
    have hc0 : 0 ≤ 1 - (((p : ℝ) - 1) / ((p : ℝ) + 1)) ^ 2 := by
      obtain ⟨-, hle, -, -⟩ := cp_facts hp11' rfl
      have h0 : 0 ≤ ((p : ℝ) - 1) / ((p : ℝ) + 1) := div_nonneg (by linarith) (by linarith)
      nlinarith
    have h1 := mul_le_mul_of_nonneg_right hT hVp0
    have h2 := mul_le_mul_of_nonneg_left h1 (show 0 ≤ (1 - (((p : ℝ) - 1) / ((p : ℝ) + 1)) ^ 2) *
      ladderMass p X by have := one_le_ladderMass (p := p) X; positivity)
    linarith
  have hGZX : roughHarmonic Q (N / X) * ∑ a ∈ smoothSet Q X, 1 / (a : ℝ) ≤
      ∑ n ∈ Icc 1 N, 1 / (n : ℝ) := by
    rw [hHN, mul_sum]
    have hsub : smoothSet Q X ⊆ smoothSet Q N := fun a ha => by
      obtain ⟨h1, h2, h3⟩ := mem_smoothSet.mp ha
      exact mem_smoothSet.mpr ⟨h1, h2.trans hXN, h3⟩
    calc ∑ a ∈ smoothSet Q X, roughHarmonic Q (N / X) * (1 / (a : ℝ))
        ≤ ∑ a ∈ smoothSet Q X, 1 / (a : ℝ) * roughHarmonic Q (N / a) := by
          refine sum_le_sum fun a ha => ?_
          obtain ⟨ha1, haX, -⟩ := mem_smoothSet.mp ha
          have : roughHarmonic Q (N / X) ≤ roughHarmonic Q (N / a) :=
            roughHarmonic_mono (Nat.div_le_div_left haX (by omega))
          rw [mul_comm]
          exact mul_le_mul_of_nonneg_left this (by positivity)
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg hsub fun a _ _ => by
          have := roughHarmonic_nonneg Q (N / a); positivity
  exact ⟨A, B, P, Av, Ah, Bv, Bh, h3, h4, hS, h5A, h5B, hvar _ hsq1, hvar _ hsq2, hhalo _ hsq1,
    hhalo _ hsq2, hP, hGZX⟩

/-- **The twisted Poincaré inequality at a horizon.** With all parameters in range, every `z`
orthogonal to the flipped pole satisfies `(2 log 2 − η)|z|² ≤ D_N(z)`. -/
theorem twisted_poincare_at_horizon {p Q X N : ℕ} (hp : p.Prime) (hp11 : 11 ≤ p)
    (hpmem : p ∈ (range Q).filter Nat.Prime) (hQ2 : 2 ≤ Q) (hX2 : 2 ≤ X) (hXN : X ≤ N)
    {η ε g₁ Tmax τ K : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) (hεdef : ε = η / 4)
    (hg₁def : g₁ = 2 * Real.log 2 - ε / 2) (hTdef : Tmax = 2 * Real.log 2 + 2 * Real.log p)
    (hτ0 : 0 < τ) (hτ1 : τ ≤ 1 / 2) (hτT : τ * (Tmax ^ 2 + 4 * Tmax) ≤ ε / 2)
    (hK : 0 < K) (hKt : ∀ Q X : ℕ, ∀ f : ℕ → ℝ, harmonicVar Q X f ≤ K * glauberForm Q X f)
    (hκ : K / Real.log Q * (4 * Tmax) ≤ 1)
    (hML : 2 * ladderConstant Q / Real.log X ≤ τ) (h2L : 2 / Real.log X ≤ τ)
    (hcoef : g₁ * (1 + 16 * logSum Q / Real.log X) ≤ boxGap X -
      4 * logSum Q / Real.sqrt (Real.sqrt X) - 16 * logSum Q * ladderConstant Q / Real.log X)
    (he₂ : 16 * logSum Q / Real.log X ≤ 1 / 20)
    (hGr : (1 + Real.log X) / τ + 16 * (1 + 1 / τ) * logSum Q / g₁ ≤ roughHarmonic Q (N / X))
    (hGbig : 4 * (2 * Real.log 2) * 150 * (1 + Real.log X) ^ 3 / η ≤ roughHarmonic Q (N / X))
    (hbig2 : 2 * Real.log 2 * 150 * (2 * ladderConstant Q / Real.log X) ≤ η / 4)
    (hbig3 : 2 * Real.log 2 * 150 * (2 / Real.log X) ≤ η / 16)
    (z : ℕ → ℝ) (hz : ∑ n ∈ Icc 1 N, finiteFlip {p} n * z n / Real.sqrt n = 0) :
    (2 * Real.log 2 - η) * ∑ n ∈ Icc 1 N, z n ^ 2 ≤ poleDefect N z := by
  have hl2 := Real.log_two_gt_d9
  have hl2' := Real.log_two_lt_d9
  have hp11' : (11 : ℝ) ≤ p := by exact_mod_cast hp11
  have hlp : 2.35 ≤ Real.log p := log_ge_of_eleven_le hp11'
  have hpQ : p < Q := mem_range.mp (mem_filter.mp hpmem).1
  have hX1 : 1 ≤ X := by omega
  have hN1 : 1 ≤ N := le_trans hX1 hXN
  have hL0 : 0 < Real.log X := Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  have h1 := two_scale_twisted hp hpmem hQ2 hX2 hXN hη hη1 hεdef hg₁def hTdef hτ0 hτ1 hτT hK hKt
    hκ hML h2L hcoef hGr z
  obtain ⟨A, B, P, Av, Ah, Bv, Bh, h3, h4, hS, h5A, h5B, hAv, hBv, hAh, hBh, hP, hGZX⟩ :=
    constraint_data (Q := Q) (X := X) hp hp11 hpQ hX2 hXN z hz
  have hH1 : 1 ≤ ∑ n ∈ Icc 1 N, 1 / (n : ℝ) := by
    have := single_le_sum (f := fun n : ℕ => 1 / (n : ℝ)) (fun n _ => by positivity)
      (mem_Icc.mpr ⟨le_rfl, hN1⟩)
    simpa using this
  have hH0 : 0 < ∑ n ∈ Icc 1 N, 1 / (n : ℝ) := by linarith
  have hG1 : 1 ≤ roughHarmonic Q (N / X) :=
    one_le_roughHarmonic Q ((Nat.le_div_iff_mul_le (by omega)).mpr (by omega))
  have hG0 : 0 < roughHarmonic Q (N / X) := by linarith
  have h2 : ∑ n ∈ Icc 1 N, z n ^ 2 ≤ ∑ n ∈ Icc 1 N, 1 / (n : ℝ) * (poleGauge z n -
      wMean (smoothSet Q X) (fun a => 1 / (a : ℝ)) (fibreMean Q N (poleGauge z))) ^ 2 +
      (∑ n ∈ Icc 1 N, 1 / (n : ℝ) * poleGauge z n) ^ 2 / ∑ n ∈ Icc 1 N, 1 / (n : ℝ) := by
    rw [sum_sq_eq_sum_one_div_poleGauge_sq]
    exact sum_one_div_mul_sq_le hN1 (poleGauge z) _
  have hbig1 : 2 * Real.log 2 * 150 * ((1 + Real.log X) ^ 3 / (roughHarmonic Q (N / X) *
      ∑ n ∈ Icc 1 N, 1 / (n : ℝ))) ≤ η / 4 := by
    rw [div_le_iff₀ hη] at hGbig
    have hGH : roughHarmonic Q (N / X) ≤ roughHarmonic Q (N / X) * ∑ n ∈ Icc 1 N, 1 / (n : ℝ) := by
      have := mul_le_mul_of_nonneg_left hH1 hG0.le
      linarith
    rw [mul_div_assoc', div_le_iff₀ (by positivity)]
    have : 0 ≤ η / 4 := by positivity
    nlinarith
  have hW0 : 0 ≤ ∑ n ∈ Icc 1 N, 1 / (n : ℝ) * (poleGauge z n -
      wMean (smoothSet Q X) (fun a => 1 / (a : ℝ)) (fibreMean Q N (poleGauge z))) ^ 2 :=
    sum_nonneg fun n _ => by positivity
  have hZX0 : 0 ≤ ∑ a ∈ smoothSet Q X, 1 / (a : ℝ) := sum_nonneg fun a _ => by positivity
  rw [← walkEnergy_small_add_large Q N z] at h1 ⊢
  exact twisted_assembly (lam := 2 * Real.log 2) (η := η) (p := (p : ℝ)) (ℓ := Real.log p)
    (by linarith) (by linarith) hη hη1 hp11' hlp hW0 (pFibreVar_nonneg _ _ _ _) hG0 hH0
    (walkEnergy_nonneg _ _ _) (walkEnergy_nonneg _ _ _) hL0 (ladderConstant_nonneg Q) hZX0
    (one_le_ladderMass X) (boxGap_le_two_mul_log_two X)
    (by have := logSum_nonneg Q; positivity) he₂ h1 h2 h3 h4 hS h5A h5B hAv hBv hAh hBh hP hGZX
    hbig1 hbig2 hbig3

/-- **The twisted Poincaré inequality.** For a prime `p ≥ 11` and every `0 < η ≤ 1`, eventually
in `N`, every `z` orthogonal to the flipped pole `ω_p(n)/√n` has `D_N(z) ≥ (2 log 2 − η)|z|²`. -/
theorem eventually_primeFlip_poleDefect_ge {p : ℕ} (hp : p.Prime) (hp11 : 11 ≤ p) {η : ℝ}
    (hη : 0 < η) (hη1 : η ≤ 1) :
    ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ∀ z : ℕ → ℝ,
      ∑ n ∈ Icc 1 N, finiteFlip {p} n * z n / Real.sqrt n = 0 →
      (2 * Real.log 2 - η) * ∑ n ∈ Icc 1 N, z n ^ 2 ≤ poleDefect N z := by
  have hl2 := Real.log_two_gt_d9
  have hl2' := Real.log_two_lt_d9
  have hlp0 : 0 ≤ Real.log p := Real.log_natCast_nonneg p
  -- the parameters
  obtain ⟨ε, hεdef⟩ : ∃ ε : ℝ, ε = η / 4 := ⟨_, rfl⟩
  have hε0 : 0 < ε := by rw [hεdef]; positivity
  obtain ⟨g₁, hg₁def⟩ : ∃ g : ℝ, g = 2 * Real.log 2 - ε / 2 := ⟨_, rfl⟩
  have hg₁0 : 0 < g₁ := by rw [hg₁def, hεdef]; linarith
  obtain ⟨Tmax, hTdef⟩ : ∃ T : ℝ, T = 2 * Real.log 2 + 2 * Real.log p := ⟨_, rfl⟩
  have hTmax0 : 0 < Tmax := by rw [hTdef]; linarith
  obtain ⟨τ, hτdef⟩ : ∃ τ : ℝ, τ = min (1 / 2) (ε / (2 * (Tmax ^ 2 + 4 * Tmax))) := ⟨_, rfl⟩
  have hτ0 : 0 < τ := by rw [hτdef]; exact lt_min (by norm_num) (by positivity)
  have hτ1 : τ ≤ 1 / 2 := by rw [hτdef]; exact min_le_left _ _
  have hτT : τ * (Tmax ^ 2 + 4 * Tmax) ≤ ε / 2 := by
    have h := min_le_right (1 / 2 : ℝ) (ε / (2 * (Tmax ^ 2 + 4 * Tmax)))
    rw [← hτdef, le_div_iff₀ (by positivity)] at h
    linarith
  -- the large primes
  obtain ⟨K, hK, hKt⟩ := exists_harmonicVar_le_glauberForm_rough
  obtain ⟨Q₀, hQ₀2, hκ₀⟩ := exists_cutoff_div_log_le (2 * K * Tmax)
  obtain ⟨Q, hQdef⟩ : ∃ Q : ℕ, Q = max Q₀ (p + 1) := ⟨_, rfl⟩
  have hQ2 : 2 ≤ Q := by rw [hQdef]; exact le_trans hQ₀2 (le_max_left _ _)
  have hpQ : p < Q := by rw [hQdef]; exact lt_of_lt_of_le (Nat.lt_succ_self p) (le_max_right _ _)
  have hpmem : p ∈ (range Q).filter Nat.Prime := mem_filter.mpr ⟨mem_range.mpr hpQ, hp⟩
  have hκ : K / Real.log Q * (4 * Tmax) ≤ 1 := by
    have hlQ₀ : 0 < Real.log Q₀ := Real.log_pos (by exact_mod_cast (show 1 < Q₀ by omega))
    have hle : Real.log Q₀ ≤ Real.log Q :=
      Real.log_le_log (by positivity) (by rw [hQdef]; exact_mod_cast le_max_left _ _)
    have hlQ : 0 < Real.log Q := lt_of_lt_of_le hlQ₀ hle
    rw [div_le_iff₀ hlQ₀] at hκ₀
    rw [div_mul_eq_mul_div, div_le_one hlQ]
    linarith
  obtain ⟨M, hMdef⟩ : ∃ M : ℝ, M = ladderConstant Q := ⟨_, rfl⟩
  obtain ⟨LQ, hLQdef⟩ : ∃ L : ℝ, L = logSum Q := ⟨_, rfl⟩
  have hM : 0 ≤ M := by rw [hMdef]; exact ladderConstant_nonneg Q
  have hLQ : 0 ≤ LQ := by rw [hLQdef]; exact logSum_nonneg Q
  -- the horizon
  obtain ⟨L₀, hL₀def⟩ : ∃ L : ℝ, L = 1 + 320 * LQ + 64 * LQ * (2 * Real.log 2) / ε +
      256 * LQ * M / ε + 2400 * (2 * Real.log 2) * M / η + 4800 * (2 * Real.log 2) / η := ⟨_, rfl⟩
  have hlog := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hsq := (Real.tendsto_sqrt_atTop.comp Real.tendsto_sqrt_atTop).comp
    tendsto_natCast_atTop_atTop
  have hpow := tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
  have ev := ((hlog.eventually_ge_atTop L₀).and (hsq.eventually_ge_atTop (64 * LQ / ε + 1))).and
    ((hpow.eventually_le_const (show (0 : ℝ) < ε / (16 * (2 * Real.log 2)) by positivity)).and
      (Filter.eventually_ge_atTop 2))
  obtain ⟨X₁, hX₁⟩ := Filter.eventually_atTop.mp ev
  obtain ⟨X, hXX₁, hX2, hML, h2L, -⟩ := exists_horizon hM hτ0 (hτ1.trans (by norm_num)) X₁
  obtain ⟨⟨hlX, hsX⟩, hpowX, -⟩ := hX₁ X hXX₁
  simp only [Function.comp] at hlX hsX hpowX
  obtain ⟨L, hLdef⟩ : ∃ L : ℝ, L = Real.log X := ⟨_, rfl⟩
  rw [← hLdef] at hlX hML h2L
  have hX1 : 1 ≤ X := by omega
  have hsX0 : 0 < Real.sqrt (Real.sqrt X) := by
    have : 0 ≤ 64 * LQ / ε := by positivity
    linarith
  -- the consequences of the horizon
  have t1 : 0 ≤ 320 * LQ := by positivity
  have t2 : 0 ≤ 64 * LQ * (2 * Real.log 2) / ε := by positivity
  have t3 : 0 ≤ 256 * LQ * M / ε := by positivity
  have t4 : 0 ≤ 2400 * (2 * Real.log 2) * M / η := by positivity
  have t5 : 0 ≤ 4800 * (2 * Real.log 2) / η := by positivity
  rw [hL₀def] at hlX
  have hL1 : 1 ≤ L := by linarith
  have hL0 : 0 < L := by linarith
  have he₂ : 16 * LQ / L ≤ 1 / 20 := by rw [div_le_iff₀ hL0]; linarith
  have he₂log : 16 * LQ / L * (2 * Real.log 2) ≤ ε / 4 := by
    have h64 : 64 * LQ * (2 * Real.log 2) / ε ≤ L := by linarith
    rw [div_le_iff₀ hε0] at h64
    rw [div_mul_eq_mul_div, div_le_iff₀ hL0]
    linarith
  have he₁M : 16 * LQ * M / L ≤ ε / 16 := by
    have h256 : 256 * LQ * M / ε ≤ L := by linarith
    rw [div_le_iff₀ hε0] at h256
    rw [div_le_iff₀ hL0]
    linarith
  have he₁s : 4 * LQ / Real.sqrt (Real.sqrt X) ≤ ε / 16 := by
    have h64 : 64 * LQ / ε ≤ Real.sqrt (Real.sqrt X) := by linarith
    rw [div_le_iff₀ hε0] at h64
    rw [div_le_iff₀ hsX0]
    linarith
  have hboxGap : 2 * Real.log 2 - ε / 8 ≤ boxGap X := by
    rw [boxGap]
    have hpow1 : (1 / 2 : ℝ) ^ (X + 1) ≤ (1 / 2 : ℝ) ^ X :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.le_succ X)
    have h2 : (1 / 2 : ℝ) ^ X * (16 * (2 * Real.log 2)) ≤ ε :=
      (le_div_iff₀ (by positivity)).mp hpowX
    have h3 : 2 * Real.log 2 * (1 / 2 : ℝ) ^ (X + 1) ≤ 2 * Real.log 2 * (1 / 2 : ℝ) ^ X :=
      mul_le_mul_of_nonneg_left hpow1 (by positivity)
    linarith
  have hcoef : g₁ * (1 + 16 * LQ / L) ≤ boxGap X - 4 * LQ / Real.sqrt (Real.sqrt X) -
      16 * LQ * M / L := by
    rw [hg₁def]
    have h0 : 0 ≤ 16 * LQ / L := by positivity
    have := mul_le_mul_of_nonneg_left he₂log (show 0 ≤ (1 : ℝ) by norm_num)
    have hε2 : 0 ≤ ε / 2 * (16 * LQ / L) := by positivity
    nlinarith
  have hbig2 : 2 * Real.log 2 * 150 * (2 * M / L) ≤ η / 4 := by
    have h2400 : 2400 * (2 * Real.log 2) * M / η ≤ L := by linarith
    rw [div_le_iff₀ hη] at h2400
    rw [mul_div_assoc', div_le_iff₀ hL0]
    linarith
  have hbig3 : 2 * Real.log 2 * 150 * (2 / L) ≤ η / 16 := by
    have h4800 : 4800 * (2 * Real.log 2) / η ≤ L := by linarith
    rw [div_le_iff₀ hη] at h4800
    rw [mul_div_assoc', div_le_iff₀ hL0]
    linarith
  -- the rough mass beyond the horizon
  obtain ⟨G₀, hG₀def⟩ : ∃ G : ℝ, G = (1 + L) / τ + 16 * (1 + 1 / τ) * LQ / g₁ +
      4 * (2 * Real.log 2) * 150 * (1 + L) ^ 3 / η := ⟨_, rfl⟩
  obtain ⟨N₀, hXN₀, hN₀⟩ := eventually_le_roughHarmonic_div (show 1 ≤ Q by omega) hX1 G₀
  refine ⟨N₀, fun N hN z hz => ?_⟩
  have hXN : X ≤ N := hXN₀.trans hN
  have hGG₀ : G₀ ≤ roughHarmonic Q (N / X) := hN₀ N hN
  rw [hG₀def] at hGG₀
  have hGr : (1 + L) / τ + 16 * (1 + 1 / τ) * LQ / g₁ ≤ roughHarmonic Q (N / X) := by
    have : 0 ≤ 4 * (2 * Real.log 2) * 150 * (1 + L) ^ 3 / η := by positivity
    linarith
  have hGbig : 4 * (2 * Real.log 2) * 150 * (1 + L) ^ 3 / η ≤ roughHarmonic Q (N / X) := by
    have : 0 ≤ (1 + L) / τ + 16 * (1 + 1 / τ) * LQ / g₁ := by positivity
    linarith
  subst hLdef hMdef hLQdef
  exact twisted_poincare_at_horizon hp hp11 hpmem hQ2 hX2 hXN hη hη1 hεdef hg₁def hTdef hτ0 hτ1
    hτT hK hKt hκ hML h2L hcoef he₂ hGr hGbig hbig2 hbig3 z hz

/-! ### 8. The maximal gap is attained by prime flips -/

/-- **Large prime flips attain the maximal gap.** For every prime `p ≥ 11`, the single-prime flip
has hyperplane gap `2 log 2`. -/
theorem primeFlip_hasHyperplaneGap_two_mul_log_two {p : ℕ} (hp : p.Prime) (hp11 : 11 ≤ p) :
    HasHyperplaneGap (finiteFlip {p}) (2 * Real.log 2) := by
  intro ε hε
  have hl2 := Real.log_two_lt_d9
  have hl2' := Real.log_two_gt_d9
  set ε₁ := min (1 / 2 : ℝ) (ε / 6) with hε₁def
  have hε₁ : 0 < ε₁ := lt_min (by norm_num) (by positivity)
  have hε₁2 : ε₁ ≤ 1 / 2 := min_le_left _ _
  have hε₁6 : ε₁ ≤ ε / 6 := min_le_right _ _
  set η := min 1 (ε / 3) with hηdef
  have hη : 0 < η := lt_min one_pos (by positivity)
  have hη1 : η ≤ 1 := min_le_left _ _
  have hη3 : η ≤ ε / 3 := min_le_right _ _
  obtain ⟨N₁, hN₁⟩ := eventually_atomicWeilForm_add_poleDefect_le hε₁
  obtain ⟨N₂, hN₂⟩ := eventually_primeFlip_poleDefect_ge hp hp11 hη hη1
  refine ⟨max N₁ N₂, fun N hN x hx => ?_⟩
  have h1 := hN₁ N (le_of_max_le_left hN) (fun n => finiteFlip {p} n * x n)
  have hz : ∑ n ∈ Icc 1 N, finiteFlip {p} n * (finiteFlip {p} n * x n) / Real.sqrt n = 0 := by
    rw [← hx]
    exact sum_congr rfl fun n _ => by rw [← mul_assoc, singleFlip_mul_self, one_mul]
  have h2 := hN₂ N (le_of_max_le_right hN) (fun n => finiteFlip {p} n * x n) hz
  have hmass : ∑ n ∈ Icc 1 N, (finiteFlip {p} n * x n) ^ 2 = ∑ n ∈ Icc 1 N, x n ^ 2 :=
    sum_congr rfl fun n _ => by rw [mul_pow, sq, singleFlip_mul_self, one_mul]
  rw [hmass] at h1 h2
  have hS : 0 ≤ ∑ n ∈ Icc 1 N, x n ^ 2 := sum_nonneg fun _ _ => sq_nonneg _
  have h3 := mul_le_mul_of_nonneg_left h2 (show 0 ≤ 1 - ε₁ by linarith)
  have h4 : (ε₁ * (1 + 2 * Real.log 2) + η) * ∑ n ∈ Icc 1 N, x n ^ 2 ≤
      ε * ∑ n ∈ Icc 1 N, x n ^ 2 :=
    mul_le_mul_of_nonneg_right (by nlinarith) hS
  have h5 : 0 ≤ ε₁ * η * ∑ n ∈ Icc 1 N, x n ^ 2 := by positivity
  nlinarith

/-- **The maximal gap is not rigid.** For every prime `p ≥ 11`, `2 log 2` is the greatest
hyperplane gap of the single-prime flip, exactly as for `ζ`. -/
theorem isGreatest_primeFlip_hyperplaneGap {p : ℕ} (hp : p.Prime) (hp11 : 11 ≤ p) :
    IsGreatest {g | HasHyperplaneGap (finiteFlip {p}) g} (2 * Real.log 2) :=
  ⟨primeFlip_hasHyperplaneGap_two_mul_log_two hp hp11, fun _ hg =>
    le_two_mul_log_two_of_hasHyperplaneGap_of_mul_self_eq_one (singleFlip_mul_self p) hg⟩

/-- **The maximal discrete margin does not select the source.** There are infinitely many
completely multiplicative sign gauges `ω ≠ 1`, each with the untwisted polar matching and the
maximal hyperplane gap `2 log 2`, whose weights `ωΛ` have the same size as `Λ` at every integer
and are not Weil-positive. -/
theorem maximal_gap_does_not_select_the_source :
    ∀ P : ℕ, ∃ p : ℕ, p.Prime ∧ P ≤ p ∧ finiteFlip {p} p = -1 ∧
      IsSignGauge (finiteFlip {p}) ∧
      IsGreatest {g | HasHyperplaneGap (finiteFlip {p}) g} (2 * Real.log 2) ∧
      (∀ n : ℕ, |primeFlipWeight p n| = ArithmeticFunction.vonMangoldt n) ∧
      (∀ y : ℕ, 1 ≤ y →
        |gaugeMertensSum (finiteFlip {p}) y - Real.log y| ≤
          Real.log 4 + 4 + 2 * Real.log p / ((p : ℝ) - 1)) ∧
      ¬ WeilPositiveFull (primeFlipWeight p) := by
  intro P
  obtain ⟨p, hPp, hp⟩ := Nat.exists_infinite_primes (max 11 P)
  have hp11 : 11 ≤ p := (le_max_left _ _).trans hPp
  refine ⟨p, hp, (le_max_right _ _).trans hPp, ?_, finiteFlip_isSignGauge {p},
    isGreatest_primeFlip_hyperplaneGap hp hp11, abs_primeFlipWeight p, ?_,
    primeFlip_not_weilPositiveFull hp⟩
  · simp only [finiteFlip, prod_singleton, hp.factorization_self, pow_one]
  · have hF : ∀ q ∈ ({p} : Finset ℕ), q.Prime := by
      intro q hq
      rcases mem_singleton.mp hq with rfl
      exact hp
    intro y hy
    simpa only [one_mul, sum_singleton, mul_div_assoc] using (finiteFlip_matching hF).2 y hy

end GaloisForLFunctions.ArithmeticCountingPositivity
