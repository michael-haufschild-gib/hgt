import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.CompleteWeilSplitCrossBounds
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TwoRegionConductorReserve

/-!
# The conductor complement pays the complete cross term

A logarithmic prefix reserve pays the full prime residual, while the terminal
reserve pays its short-interval version. Logarithmic interpolation keeps every
remaining conductor-dependent error relative to adjunction energy.
-/

set_option autoImplicit false
noncomputable section
open Finset
open scoped Classical RealInnerProductSpace
namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory
open SpacingScaleHarmonicAnalysis
open RenormalizedArithmeticPotentialTheory CompletedArithmeticForms CriticalScaleArithmeticRigidity

private theorem payment_coefficients_small
    {L H B c k J Cp Cn a K r : ℝ}
    (hL : 0 < L) (hH : 0 ≤ H) (hB : 0 ≤ B) (hc : 1 ≤ c)
    (hk : 0 < k) (hJ : 0 < J) (hCp : 0 < Cp) (hCn : 0 < Cn) (ha : 0 < a)
    (hr : 0 ≤ r) (hHk : H ≤ J * k) (hcut : K * c ^ 16 ≤ k)
    (hK : 128 * Cn / a ≤ K)
    (hsmall :
      64 * ((8 * Cp * J + 8 * Cp * J / a) + 16 * Cn * J / a + 1) *
        (H / L + c ^ 7 * (1 + B) / L + c ^ 11 * (1 + Real.log c) / L + c ^ 11 * r) ≤ 1) :
    Cp * H / (L * (k / 8)) + Cp * H / (L * (a * k / (8 * c ^ 7))) ≤ 1 / 64 ∧
    Cp * H ^ 2 / (L * (k / 8)) + Cp * H * B / (L * (a * k / (8 * c ^ 7))) ≤ 1 / 64 ∧
    Cn * (c ^ 2 * H / L + c ^ 4 * H * ((1 + Real.log c) / L + r)) /
      (a * k / (8 * c ^ 7)) ≤ 1 / 64 ∧
    Cn * (c ^ 4 + c ^ 2 * (1 + Real.log c)) / (a * k / (8 * c ^ 7)) ≤ 1 / 8 := by
  let e := H / L + c ^ 7 * (1 + B) / L + c ^ 11 * (1 + Real.log c) / L + c ^ 11 * r
  let A0 := 8 * Cp * J
  let A1 := 8 * Cp * J / a
  let A2 := 16 * Cn * J / a
  have hc0 := zero_lt_one.trans_le hc
  have hlc : 0 ≤ Real.log c := Real.log_nonneg hc
  have he0 : 0 ≤ e := by dsimp only [e]; positivity
  have hA0 : 0 ≤ A0 := by dsimp only [A0]; positivity
  have hA1 : 0 ≤ A1 := by dsimp only [A1]; positivity
  have hA2 : 0 ≤ A2 := by dsimp only [A2]; positivity
  have heH : H / L ≤ e := by
    have hh : 0 ≤ c ^ 7 * (1 + B) / L + c ^ 11 * (1 + Real.log c) / L + c ^ 11 * r := by positivity
    dsimp only [e]
    linarith only [hh]
  have heB : c ^ 7 * (1 + B) / L ≤ e := by
    have hh : 0 ≤ H / L + c ^ 11 * (1 + Real.log c) / L + c ^ 11 * r := by positivity
    dsimp only [e]
    linarith only [hh]
  have heC : c ^ 11 * (1 + Real.log c) / L ≤ e := by
    have hh : 0 ≤ H / L + c ^ 7 * (1 + B) / L + c ^ 11 * r := by positivity
    dsimp only [e]
    linarith only [hh]
  have heCr : c ^ 11 * ((1 + Real.log c) / L + r) ≤ e := by
    have hh : 0 ≤ H / L + c ^ 7 * (1 + B) / L := by positivity
    dsimp only [e]
    simp only [div_eq_mul_inv] at hh ⊢
    nlinarith only [hh]
  have hAe : (A0 + A1) * e ≤ 1 / 64 := by
    have hh : 0 ≤ (A2 + 1) * e := by positivity
    change 64 * ((A0 + A1) + A2 + 1) * e ≤ 1 at hsmall
    nlinarith only [hsmall, hh]
  have hA2e : A2 * e ≤ 1 / 64 := by
    have hh : 0 ≤ (A0 + A1 + 1) * e := by positivity
    change 64 * ((A0 + A1) + A2 + 1) * e ≤ 1 at hsmall
    nlinarith only [hsmall, hh]
  have hratio : H / k ≤ J := (div_le_iff₀ hk).mpr hHk
  have hc7 : 1 ≤ c ^ 7 := one_le_pow₀ hc
  have hone : 1 / L ≤ c ^ 7 * (1 + B) / L := by
    apply div_le_div_of_nonneg_right _ hL.le
    nlinarith only [hc7, mul_nonneg (pow_nonneg hc0.le 7) hB]
  have hcB : c ^ 7 / L ≤ c ^ 7 * (1 + B) / L := by
    apply div_le_div_of_nonneg_right _ hL.le
    nlinarith only [mul_nonneg (pow_nonneg hc0.le 7) hB]
  have hcb : c ^ 7 * B / L ≤ c ^ 7 * (1 + B) / L := by
    apply div_le_div_of_nonneg_right _ hL.le
    nlinarith only [pow_nonneg hc0.le 7]
  have hmass : Cp * H / (L * (k / 8)) + Cp * H / (L * (a * k / (8 * c ^ 7))) ≤
      (A0 + A1) * e := by
    have h0 := mul_le_mul_of_nonneg_right hratio (show 0 ≤ 8 * Cp / L by positivity)
    have h1 := mul_le_mul_of_nonneg_right hratio (show 0 ≤ 8 * Cp / a * c ^ 7 / L by positivity)
    have he0' := mul_le_mul_of_nonneg_left (hone.trans heB) hA0
    have he1' := mul_le_mul_of_nonneg_left (hcB.trans heB) hA1
    have hid : Cp * H / (L * (k / 8)) + Cp * H / (L * (a * k / (8 * c ^ 7))) =
        (H / k) * (8 * Cp / L) + (H / k) * (8 * Cp / a * c ^ 7 / L) := by
      field_simp [hL.ne', hk.ne', ha.ne', hc0.ne']
    rw [hid]
    dsimp only [A0, A1] at he0' he1' ⊢
    simp only [div_eq_mul_inv] at h0 h1 he0' he1' ⊢
    nlinarith only [h0, h1, he0', he1']
  have henergy : Cp * H ^ 2 / (L * (k / 8)) + Cp * H * B / (L * (a * k / (8 * c ^ 7))) ≤
      (A0 + A1) * e := by
    have h0 := mul_le_mul_of_nonneg_right hratio (show 0 ≤ 8 * Cp * H / L by positivity)
    have h1 := mul_le_mul_of_nonneg_right hratio (show 0 ≤ 8 * Cp / a * c ^ 7 * B / L by positivity)
    have he0' := mul_le_mul_of_nonneg_left heH hA0
    have he1' := mul_le_mul_of_nonneg_left (hcb.trans heB) hA1
    have hid : Cp * H ^ 2 / (L * (k / 8)) + Cp * H * B / (L * (a * k / (8 * c ^ 7))) =
        (H / k) * (8 * Cp * H / L) + (H / k) * (8 * Cp / a * c ^ 7 * B / L) := by
      field_simp [hL.ne', hk.ne', ha.ne', hc0.ne']
    rw [hid]
    dsimp only [A0, A1] at he0' he1' ⊢
    simp only [div_eq_mul_inv] at h0 h1 he0' he1' ⊢
    nlinarith only [h0, h1, he0', he1']
  have hweighted : Cn * (c ^ 2 * H / L + c ^ 4 * H * ((1 + Real.log c) / L + r)) /
      (a * k / (8 * c ^ 7)) ≤ A2 * e := by
    have hc9 : c ^ 9 / L ≤ c ^ 11 * (1 + Real.log c) / L := by
      apply div_le_div_of_nonneg_right _ hL.le
      have hh : c ^ 9 ≤ c ^ 11 := pow_le_pow_right₀ hc (by norm_num)
      nlinarith only [hh, mul_nonneg (pow_nonneg hc0.le 11) hlc]
    have hsum : c ^ 9 / L + c ^ 11 * ((1 + Real.log c) / L + r) ≤ 2 * e := by
      linarith only [hc9.trans heC, heCr]
    have h0 := mul_le_mul_of_nonneg_right hratio
      (show 0 ≤ 8 * Cn / a * (c ^ 9 / L + c ^ 11 * ((1 + Real.log c) / L + r)) by positivity)
    have h1 := mul_le_mul_of_nonneg_left hsum (show 0 ≤ 8 * Cn * J / a by positivity)
    have hid : Cn * (c ^ 2 * H / L + c ^ 4 * H * ((1 + Real.log c) / L + r)) /
        (a * k / (8 * c ^ 7)) =
        (H / k) * (8 * Cn / a * (c ^ 9 / L + c ^ 11 * ((1 + Real.log c) / L + r))) := by
      field_simp [hL.ne', hk.ne', ha.ne', hc0.ne']
    rw [hid]
    dsimp only [A2]
    simp only [div_eq_mul_inv] at h0 h1 ⊢
    nlinarith only [h0, h1]
  have hplain : Cn * (c ^ 4 + c ^ 2 * (1 + Real.log c)) / (a * k / (8 * c ^ 7)) ≤ 1 / 8 := by
    have hl : 1 + Real.log c ≤ c := by linarith only [Real.log_le_sub_one_of_pos hc0]
    have hc34 : c ^ 3 ≤ c ^ 4 := pow_le_pow_right₀ hc (by norm_num)
    have hcoef : c ^ 4 + c ^ 2 * (1 + Real.log c) ≤ 2 * c ^ 4 := by
      have hh := mul_le_mul_of_nonneg_left hl (sq_nonneg c)
      nlinarith only [hh, hc34]
    have hK' : 128 * Cn ≤ K * a := (div_le_iff₀ ha).mp hK
    have h1 := mul_le_mul_of_nonneg_right hK' (pow_nonneg hc0.le 16)
    have h2 := mul_le_mul_of_nonneg_left hcut ha.le
    have h3 := mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ hc (by norm_num : 11 ≤ 16)) (show 0 ≤ 128 * Cn by positivity)
    have hpay : 128 * Cn * c ^ 11 ≤ a * k := by nlinarith only [h1, h2, h3]
    calc
      _ ≤ Cn * (2 * c ^ 4) / (a * k / (8 * c ^ 7)) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hcoef hCn.le) (by positivity)
      _ = 16 * Cn * c ^ 11 / (a * k) := by
        field_simp [ha.ne', hk.ne', hc0.ne']
        ring
      _ ≤ 1 / 8 := (div_le_iff₀ (mul_pos ha hk)).mpr (by linarith only [hpay])
  exact ⟨hmass.trans hAe, henergy.trans hAe, hweighted.trans hA2e, hplain⟩

private theorem split_payments_absorbed
    {A E G U P S W z pa pe ng nu s t γ p q : ℝ}
    (hA : 0 ≤ A) (hE : 0 ≤ E) (hG0 : 0 ≤ G) (hU : 0 ≤ U)
    (hP : 0 ≤ P) (hS : 0 ≤ S) (hAU : A ≤ 2 * U) (hG : G ≤ A + E)
    (hpa : pa ≤ 1 / 64) (hpe : pe ≤ 1 / 64) (hng : ng ≤ 1 / 64) (hnu : nu ≤ 1 / 8)
    (hp : s + γ ≤ p) (hq : t + γ ≤ q)
    (hreserve : p * P + q * S ≤ W)
    (hcross : 2 * |z| ≤ pa * A + pe * E + ng * G + nu * U + s * P + t * S + γ * (P + S)) :
    2 * |z| - W ≤ (1 / 8 : ℝ) * E + (1 / 4 : ℝ) * U := by
  have h1 := mul_le_mul_of_nonneg_right hpa hA
  have h2 := mul_le_mul_of_nonneg_right hpe hE
  have h3 := mul_le_mul_of_nonneg_right hng hG0
  have h4 := mul_le_mul_of_nonneg_right hnu hU
  have h5 := mul_le_mul_of_nonneg_right hp hP
  have h6 := mul_le_mul_of_nonneg_right hq hS
  linarith only [h1, h2, h3, h4, h5, h6, hreserve, hcross, hAU, hG, hE, hU]

/-- The two conductor-orthogonal reserves absorb the full cross term with a
fixed adjunction debit and a quarter of packet mass. -/
theorem exists_completeWeil_conductor_cross_absorbed :
    ∃ b K H C : ℝ, 0 < b ∧ b ≤ 1 / 8 ∧ 0 < K ∧ 0 < H ∧ 0 < C ∧
      ∀ {R N : ℕ} {c : ℝ}, 1 ≤ c → 2 ≤ R → R ^ 6 ≤ N →
        H * c ^ 8 ≤ (N : ℝ) → c / N ≤ 1 / 3 →
        R * R ≤ N / growingDefectCutoff c →
        18 * (1 + Real.log R) ≤ Real.log (N / growingDefectCutoff c : ℕ) →
        K * c ^ 16 ≤ Real.log R / explicitConductorCutoffConstant - 1 →
        terminalPacketCost R (N / growingDefectCutoff c) N /
          Real.log (N / growingDefectCutoff c : ℕ) ≤ b / (4 * c ^ 7) →
        ((R * R : ℕ) + 1 : ℝ) * (linearNearRowRadius c + 1) ≤ N →
        ((R * R : ℕ) + 1 : ℝ) * (c * Real.exp 1 + 1) ≤ N →
        C * ((1 + Real.log R) / Real.log N +
          c ^ 7 * (1 + terminalPacketCost R (N / growingDefectCutoff c) N) / Real.log N +
          c ^ 11 * (1 + Real.log c) / Real.log N +
          c ^ 11 * (R : ℝ) ^ 2 * (Real.log N / N)) ≤ 1 →
      ∀ a : ℕ → ℝ,
        (∑ m ∈ Icc 1 R, a m • normalizedRamanujanHorizonVector m N) ∈ (conductorSubspace 1 N)ᗮ →
      ∀ {w : EuclideanSpace ℝ (PrimeHorizonIndex N)}, w ∈ (conductorSubspace R N)ᗮ →
        2 * |⟪Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N)
            (∑ m ∈ Icc 1 R, a m • normalizedRamanujanHorizonVector m N), w⟫| -
          completeWeilEnergy tiltedUnitSpline c N w ≤
        (1 / 8 : ℝ) * primeAdjunctionMass R a +
          (1 / 4 : ℝ) * ‖∑ m ∈ Icc 1 R, a m • normalizedRamanujanHorizonVector m N‖ ^ 2 := by
  obtain ⟨b, K0, H0, hb, hb8, hK0, hH0, hreserve⟩ :=
    exists_completeWeilEnergy_two_region_conductor_reserve
  obtain ⟨Cp, Cn, hCp, hCn, hcross⟩ := exists_completeWeil_cross_le_split_mass_reserves
  let D := explicitConductorCutoffConstant
  let J := 1 + 2 * D
  let K := 1 + K0 + 128 * Cn / b
  let C := 64 * ((8 * Cp * J + 8 * Cp * J / b) + 16 * Cn * J / b + 1)
  have hD : 0 < D := explicitConductorCutoffConstant_pos
  have hJ : 0 < J := by dsimp only [J]; positivity
  have hK1 : 1 ≤ K := by
    have hh : 0 ≤ 128 * Cn / b := by positivity
    dsimp only [K]
    linarith only [hK0, hh]
  have hK : 0 < K := zero_lt_one.trans_le hK1
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨b, K, H0, C, hb, hb8, hK, hH0, hC, ?_⟩
  intro R N c hc hR hR6 hHN hwidth hRM hlogM hcut hleak hsize hsize_up hsmall a hu1 w hw
  let M := N / growingDefectCutoff c
  let L := Real.log N
  let H := 1 + Real.log R
  let B := terminalPacketCost R M N
  let k := Real.log R / D - 1
  let s := k / 8
  let t := b * k / (8 * c ^ 7)
  let u := ∑ m ∈ Icc 1 R, a m • normalizedRamanujanHorizonVector m N
  let A := ∑ m ∈ Icc 1 R, a m ^ 2
  let E := primeAdjunctionMass R a
  let G := ∑ m ∈ Icc 1 R, (1 + Real.log m) * a m ^ 2
  let U := ‖u‖ ^ 2
  let P := ∑ n ∈ Icc 1 M, primeHorizonExtension w n ^ 2
  let S := ∑ n ∈ Ioc M N, primeHorizonExtension w n ^ 2
  let pa := Cp * H / (L * s) + Cp * H / (L * t)
  let pe := Cp * H ^ 2 / (L * s) + Cp * H * B / (L * t)
  let ng := Cn * (c ^ 2 * H / L + c ^ 4 * H * ((1 + Real.log c) / L +
    (R : ℝ) ^ 2 * (L / N))) / t
  let nu := Cn * (c ^ 4 + c ^ 2 * (1 + Real.log c)) / t
  have hc0 := zero_lt_one.trans_le hc
  have hM2 : 2 ≤ M := by have hh := Nat.mul_le_mul hR hR; omega
  have hMN : M ≤ N := Nat.div_le_self N (growingDefectCutoff c)
  have hlogN : 18 * (1 + Real.log R) ≤ Real.log N := hlogM.trans
    (Real.log_le_log (by exact_mod_cast (show 0 < M by omega)) (by exact_mod_cast hMN))
  have hL : 0 < L := by dsimp only [L]; linarith only [hlogN, Real.log_natCast_nonneg R]
  have hH : 0 ≤ H := by dsimp only [H]; positivity
  have hB : 0 ≤ B := terminalPacketCost_nonneg R hMN
  have hk1 : 1 ≤ k := by
    have hh : 1 ≤ K * c ^ 16 := by
      simpa only [one_mul] using mul_le_mul hK1 (one_le_pow₀ hc (n := 16)) zero_le_one hK.le
    exact hh.trans hcut
  have hk : 0 < k := zero_lt_one.trans_le hk1
  have hs : 0 < s := by dsimp only [s]; positivity
  have ht : 0 < t := by dsimp only [t]; positivity
  have hHk : H ≤ J * k := by
    have hid : Real.log R = D * (k + 1) := by
      dsimp only [k]
      field_simp [hD.ne']
      ring
    have hh := mul_le_mul_of_nonneg_left hk1 hD.le
    dsimp only [H, J]
    rw [hid]
    nlinarith only [hh, hk1]
  have hKplain : 128 * Cn / b ≤ K := by dsimp only [K]; linarith only [hK0]
  have hsmall' :
      64 * ((8 * Cp * J + 8 * Cp * J / b) + 16 * Cn * J / b + 1) *
        (H / L + c ^ 7 * (1 + B) / L + c ^ 11 * (1 + Real.log c) / L +
          c ^ 11 * ((R : ℝ) ^ 2 * (L / N))) ≤ 1 := by
    simpa only [C, H, L, B, M, mul_assoc] using hsmall
  obtain ⟨hpa, hpe, hng, hnu⟩ := payment_coefficients_small hL hH hB hc hk hJ hCp hCn hb
    (by positivity : 0 ≤ (R : ℝ) ^ 2 * (L / N)) hHk hcut hKplain hsmall'
  change pa ≤ 1 / 64 at hpa
  change pe ≤ 1 / 64 at hpe
  change ng ≤ 1 / 64 at hng
  change nu ≤ 1 / 8 at hnu
  have hcut0 : K0 * c ^ 16 ≤ k := by
    have hh : K0 ≤ K := by
      have hz : 0 ≤ 128 * Cn / b := by positivity
      dsimp only [K]
      linarith only [hz]
    exact (mul_le_mul_of_nonneg_right hh (pow_nonneg hc0.le 16)).trans hcut
  have hres := hreserve hc hR hHN hRM hlogM hcut0 hleak hw
  change k / 4 * P + b * k / (2 * c ^ 7) * S ≤ completeWeilEnergy tiltedUnitSpline c N w at hres
  have hsplit : ‖w‖ ^ 2 = P + S := by
    rw [← sum_primeHorizonExtension_sq]
    have hf : (Ioc M N : Finset ℕ) = Icc 1 N \ Icc 1 M := by
      ext n
      simp only [Finset.mem_Ioc, Finset.mem_sdiff, Finset.mem_Icc]
      omega
    dsimp only [P, S]
    rw [hf, add_comm]
    exact (sum_sdiff (Icc_subset_Icc le_rfl hMN)).symm
  have hP : 0 ≤ P := sum_nonneg fun _ _ => sq_nonneg _
  have hS : 0 ≤ S := sum_nonneg fun _ _ => sq_nonneg _
  have hA : 0 ≤ A := sum_nonneg fun _ _ => sq_nonneg _
  have hE : 0 ≤ E := primeAdjunctionMass_nonneg R a
  have hG0 : 0 ≤ G := sum_nonneg fun m _ => by have := Real.log_natCast_nonneg m; positivity
  have hAU : A ≤ 2 * U := by
    have hRR : R * R ≤ N := hRM.trans hMN
    have hh := (half_and_three_halves_riesz_of_log_le hR hRR hlogN a).1
    change (1 / 2 : ℝ) * A ≤ U at hh
    linarith only [hh]
  have hG : G ≤ A + E := by
    dsimp only [G, A, E, primeAdjunctionMass]
    rw [← sum_add_distrib]
    apply sum_le_sum
    intro m _
    have hh := mul_nonneg (tameDifferent_nonneg m) (sq_nonneg (a m))
    nlinarith only [hh]
  have ht_s : t ≤ k / 8 := by
    have hb1 : b ≤ 1 := hb8.trans (by norm_num)
    have hbc : b ≤ c ^ 7 := hb1.trans (one_le_pow₀ hc)
    have hh := mul_le_mul_of_nonneg_right hbc hk.le
    dsimp only [t]
    apply (div_le_iff₀ (by positivity : 0 < 8 * c ^ 7)).mpr
    nlinarith only [hh]
  have hprepay : s + t ≤ k / 4 := by dsimp only [s]; linarith only [ht_s]
  have htailpay : t + t ≤ b * k / (2 * c ^ 7) := by
    have he : b * k / (2 * c ^ 7) = 4 * t := by
      dsimp only [t]
      field_simp [hc0.ne']
      ring
    rw [he]
    linarith only [ht]
  have hraw := hcross hR hR6 hMN hlogN hc hwidth hsize hsize_up a hu1 hw s t t hs ht ht
  change 2 * |⟪Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N) u, w⟫| ≤
    Cp * (H * A + H ^ 2 * E) / (L * s) + Cp * (H * A + H * B * E) / (L * t) +
    Cn * ((c ^ 2 * H / L + c ^ 4 * H * ((1 + Real.log c) / L + (R : ℝ) ^ 2 * (L / N))) * G +
      (c ^ 4 + c ^ 2 * (1 + Real.log c)) * U) / t + s * P + t * S + t * ‖w‖ ^ 2 at hraw
  rw [hsplit] at hraw
  have hid : Cp * (H * A + H ^ 2 * E) / (L * s) + Cp * (H * A + H * B * E) / (L * t) +
      Cn * ((c ^ 2 * H / L + c ^ 4 * H * ((1 + Real.log c) / L + (R : ℝ) ^ 2 * (L / N))) * G +
        (c ^ 4 + c ^ 2 * (1 + Real.log c)) * U) / t + s * P + t * S + t * (P + S) =
      pa * A + pe * E + ng * G + nu * U + s * P + t * S + t * (P + S) := by
    dsimp only [pa, pe, ng, nu]
    ring
  rw [hid] at hraw
  exact split_payments_absorbed hA hE hG0 (sq_nonneg ‖u‖) hP hS hAU hG
    hpa hpe hng hnu hprepay htailpay hres hraw

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory

#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.exists_completeWeil_conductor_cross_absorbed
