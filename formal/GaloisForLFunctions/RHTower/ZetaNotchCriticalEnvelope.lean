import GaloisForLFunctions.RHTower.ZetaNotchOffDiagonalShells
import GaloisForLFunctions.RHTower.ZetaNotchDecayingEnvelope

/-!
# The notch main term at the critical endpoint

At the resonance scale `δ = 1/L` every off-diagonal part of the twisted notch moment decays in
the twist. For a mode twist `h/k` of `n` (`k ≤ K₀`, `n ≤ K₀hk`):
* the diagonal envelope is `≤ C L (1 + log n) n^{−1/2}`;
* the near-resonant mass and the detuned direct and dual pairs cost `≤ C K₀³ L √(k/h)
  ≤ C K₀⁵ L n^{−1/2}` (dyadic detuning shells at scale `δ = 1/L`);
* the near-line small dual pairs cost `≤ C k L^{1/2} log L`, and they exist only for `h < 2kL`,
  that is `n < 2K₀³L`. On that range `√n log(2K₀³L) ≤ 4 √(2K₀³L) (1 + log n)`
  (`sqrt_mul_log_le`), so this is also `≤ C K₀³ L (1 + log n) n^{−1/2}`;
* the remaining terms are uniform in `n` and decay like `L^{5/2−K}`.

Hence (`exists_norm_weightedMoment_sub_mainWeight_le_crit`) for the truncated notch weight,
uniformly in `L ≥ 16` and `n ≠ 0`,

`‖M_L(log n) − mainWeight(n) e_P ∫ ω log t‖ ≤ D (L (1 + log n) n^{−1/2} + L^{5/2} ((L/8)^{−K}
  + e^{−L²/128}) + L² e^{−L²/32})`.
-/

noncomputable section

open Complex MeasureTheory Set Filter Topology RHTower GaloisForLFunctions.HTGeometry

namespace RHTower.WeilAbscissa

open RHTower.ZetaNotch RHTower.SmoothNumbers RHTower.WeilFiniteSupport RHTower.WeilLogSummable

variable {P : Finset ℕ}

/-- `√n log X ≤ 4 √X (1 + log n)` for `1 ≤ n ≤ X`. -/
theorem sqrt_mul_log_le {n X : ℝ} (hn : 1 ≤ n) (hnX : n ≤ X) :
    Real.sqrt n * Real.log X ≤ 4 * Real.sqrt X * (1 + Real.log n) := by
  have hX1 : 1 ≤ X := hn.trans hnX
  have hX0 : 0 < X := by linarith
  have hlogn : 0 ≤ Real.log n := Real.log_nonneg hn
  have hlogX : 0 ≤ Real.log X := Real.log_nonneg hX1
  have hsX := Real.sqrt_nonneg X
  rcases le_or_gt (n ^ 2) X with h2 | h2
  · have hl : Real.log X ≤ 4 * X ^ (1 / 4 : ℝ) := by
      have := Real.log_le_rpow_div hX0.le (by norm_num : (0 : ℝ) < 1 / 4)
      rw [div_eq_mul_inv, show ((1 : ℝ) / 4)⁻¹ = 4 by norm_num] at this
      linarith
    have hs : Real.sqrt n ≤ X ^ (1 / 4 : ℝ) := by
      rw [Real.sqrt_eq_rpow]
      calc n ^ (1 / 2 : ℝ) = (n ^ 2) ^ (1 / 4 : ℝ) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]; norm_num
        _ ≤ X ^ (1 / 4 : ℝ) := Real.rpow_le_rpow (by positivity) h2 (by norm_num)
    have hsq : X ^ (1 / 4 : ℝ) * X ^ (1 / 4 : ℝ) = Real.sqrt X := by
      rw [← Real.rpow_add hX0, Real.sqrt_eq_rpow]; norm_num
    calc Real.sqrt n * Real.log X ≤ X ^ (1 / 4 : ℝ) * (4 * X ^ (1 / 4 : ℝ)) :=
          mul_le_mul hs hl hlogX (by positivity)
      _ = 4 * Real.sqrt X := by rw [← hsq]; ring
      _ ≤ 4 * Real.sqrt X * (1 + Real.log n) := by nlinarith
  · have hl : Real.log X ≤ 2 * Real.log n := by
      have e : Real.log (n ^ 2) = 2 * Real.log n := by rw [Real.log_pow]; norm_num
      rw [← e]
      exact Real.log_le_log hX0 h2.le
    have hs : Real.sqrt n ≤ Real.sqrt X := Real.sqrt_le_sqrt hnX
    calc Real.sqrt n * Real.log X ≤ Real.sqrt X * (2 * Real.log n) :=
          mul_le_mul hs hl hlogX hsX
      _ ≤ 4 * Real.sqrt X * (1 + Real.log n) := by nlinarith

/-! ## The twisted moment with the detuning shells -/

/-- **Twisted moment = diagonal + shell-resolved remainder.** For coprime `h, k ≥ 1`, `0 < δ`,
`K ∈ ℕ`, the remainder is bounded by the near-resonant mass, the detuned pairs, the near-line
small dual pairs, and terms uniform in the twist. -/
theorem exists_norm_twistedMoment_sub_diag_le_shell (K : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {L δ : ℝ}, 16 ≤ L → 0 < δ → ∀ {h k : ℕ}, 0 < h → 0 < k →
      Nat.Coprime h k →
      ‖ZetaNotch.twistedMoment L (Real.log h - Real.log k) -
          ((Real.sqrt (h * k) : ℂ))⁻¹ * diagMain L (h * k)‖ ≤
        C * (L * nearMass L h k δ + L * ∑' P, farWeight L δ K h k P +
          L ^ (-(1 / 4 : ℝ)) * ∑' P, smallWeight L δ h k P +
          L ^ (5 / 2 : ℝ) * dualTailFactor L K + L ^ 2 * Real.exp (-(L ^ 2) / 32)) := by
  obtain ⟨C₁, hC₁, h₁⟩ := exists_norm_directOff_le_far K
  obtain ⟨C₂, hC₂, h₂⟩ := exists_norm_dualOff_le_far K
  refine ⟨C₁ + C₂ + 36 * Real.exp 1, by positivity, fun {L δ} hL hδ {h k} hh hk hcop => ?_⟩
  have hL0 : 0 < L := by linarith
  rw [twistedMoment_eq_diag_add hL hh hk hcop]
  have hswap : nearMass L k h δ = nearMass L h k δ := tsum_nearRes_swap_eq hh hk δ L
  have hd := h₁ hL0 hδ hh hk
  have hu := h₂ hL hδ hh hk
  rw [hswap, tsum_farWeight_swap, tsum_smallWeight_swap] at hu
  have hr := norm_residueOsc_le (by linarith : (8 : ℝ) ≤ L) (Real.log h - Real.log k)
  set X : ℝ := L * nearMass L h k δ with hX
  set F : ℝ := L * ∑' P, farWeight L δ K h k P with hF
  set S : ℝ := L ^ (-(1 / 4 : ℝ)) * ∑' P, smallWeight L δ h k P with hS
  set T : ℝ := L ^ (5 / 2 : ℝ) * dualTailFactor L K with hT
  set Z : ℝ := L ^ 2 * Real.exp (-(L ^ 2) / 32) with hZ
  have hX0 : 0 ≤ X := mul_nonneg hL0.le (nearMass_nonneg hL0.le h k δ)
  have hF0 : 0 ≤ F := mul_nonneg hL0.le (tsum_nonneg fun P => farWeight_nonneg hL0.le K h k P)
  have hS0 : 0 ≤ S := mul_nonneg (by positivity) (tsum_nonneg fun P => smallWeight_nonneg L δ h k P)
  have hT0 : 0 ≤ T := mul_nonneg (by positivity) (dualTailFactor_nonneg hL0.le K)
  have hZ0 : 0 ≤ Z := by positivity
  have hres : ‖residueOsc L (Real.log h - Real.log k)‖ ≤ 36 * Real.exp 1 * Z := by
    refine hr.trans ?_
    have hexp : Real.exp (-(L ^ 2) / 4) ≤ Real.exp (-(L ^ 2) / 32) :=
      Real.exp_le_exp.mpr (by nlinarith)
    rw [hZ]
    have : 0 ≤ 36 * Real.exp 1 * L ^ 2 := by positivity
    nlinarith
  have hsplit : ((Real.sqrt (h * k) : ℂ))⁻¹ * diagMain L (h * k) + directOff L h k +
      dualOff L h k - residueOsc L (Real.log h - Real.log k) -
      ((Real.sqrt (h * k) : ℂ))⁻¹ * diagMain L (h * k) =
      directOff L h k + dualOff L h k - residueOsc L (Real.log h - Real.log k) := by ring
  rw [hsplit]
  have htri : ‖directOff L h k + dualOff L h k - residueOsc L (Real.log h - Real.log k)‖ ≤
      ‖directOff L h k‖ + ‖dualOff L h k‖ + ‖residueOsc L (Real.log h - Real.log k)‖ :=
    (norm_sub_le _ _).trans (by linarith [norm_add_le (directOff L h k) (dualOff L h k)])
  refine htri.trans ?_
  have e1 : C₁ * (X + F) ≤ C₁ * (X + F + S + T + Z) :=
    mul_le_mul_of_nonneg_left (by linarith) hC₁
  have e2 : C₂ * (X + F + S + T) ≤ C₂ * (X + F + S + T + Z) :=
    mul_le_mul_of_nonneg_left (by linarith) hC₂
  have e3 : 36 * Real.exp 1 * Z ≤ 36 * Real.exp 1 * (X + F + S + T + Z) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  nlinarith

/-! ## The endpoint envelope of a twist -/

/-- The remainder envelope of a coprime twist `h/k` at the resonance scale `δ = 1/L`. -/
def shellEnvelope (C L : ℝ) (K : ℕ) (h k : ℕ) : ℝ :=
  (Real.sqrt ((h : ℝ) * k))⁻¹ * (2 * L * (C + 2 * Real.log ((h : ℝ) * k))) +
    C * (L * nearMass L h k L⁻¹ + L * ∑' P, farWeight L L⁻¹ K h k P +
      L ^ (-(1 / 4 : ℝ)) * ∑' P, smallWeight L L⁻¹ h k P +
      L ^ (5 / 2 : ℝ) * dualTailFactor L K + L ^ 2 * Real.exp (-(L ^ 2) / 32))

/-- **Main term of a coprime twist, shell form.** -/
theorem exists_norm_twistedMoment_sub_le_shell (K : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {L : ℝ}, 16 ≤ L → ∀ {h k : ℕ}, 0 < h → 0 < k → Nat.Coprime h k →
      ‖ZetaNotch.twistedMoment L (Real.log h - Real.log k) -
          (((Real.sqrt ((h : ℝ) * k))⁻¹ : ℝ) : ℂ) * logWindow L‖ ≤ shellEnvelope C L K h k := by
  obtain ⟨C₁, hC₁, h₁⟩ := exists_norm_twistedMoment_sub_diag_le_shell K
  obtain ⟨C₂, hC₂, h₂⟩ := exists_norm_twistedMoment_sub_logWindow_le
  refine ⟨max C₁ C₂, le_max_of_le_left hC₁, fun {L} hL {h k} hh0 hk0 hcop => ?_⟩
  have hL0 : 0 < L := by linarith
  have hδ : 0 < L⁻¹ := inv_pos.mpr hL0
  have hR0 : 0 ≤ L * nearMass L h k L⁻¹ + L * ∑' P, farWeight L L⁻¹ K h k P +
      L ^ (-(1 / 4 : ℝ)) * ∑' P, smallWeight L L⁻¹ h k P +
      L ^ (5 / 2 : ℝ) * dualTailFactor L K + L ^ 2 * Real.exp (-(L ^ 2) / 32) := by
    have h1 := mul_nonneg hL0.le (nearMass_nonneg hL0.le h k L⁻¹)
    have h2 : 0 ≤ L * ∑' P, farWeight L L⁻¹ K h k P :=
      mul_nonneg hL0.le (tsum_nonneg fun P => farWeight_nonneg (δ := L⁻¹) hL0.le K h k P)
    have h3 : 0 ≤ L ^ (-(1 / 4 : ℝ)) * ∑' P, smallWeight L L⁻¹ h k P :=
      mul_nonneg (by positivity) (tsum_nonneg fun P => smallWeight_nonneg L L⁻¹ h k P)
    have h4 := mul_nonneg (Real.rpow_nonneg hL0.le (5 / 2 : ℝ)) (dualTailFactor_nonneg hL0.le K)
    have h5 : 0 ≤ L ^ 2 * Real.exp (-(L ^ 2) / 32) := by positivity
    linarith
  have hrem := (h₁ hL hδ hh0 hk0 hcop).trans
    (mul_le_mul_of_nonneg_right (le_max_left C₁ C₂) hR0)
  refine (h₂ hL hh0 hk0 _ hrem).trans ?_
  unfold shellEnvelope
  gcongr
  exact le_max_right _ _

/-! ## The endpoint envelope of a mode twist -/

/-- The endpoint error weight `L (1 + log n) n^{−1/2} + L^{5/2} ((L/8)^{−K} + e^{−L²/128})
+ L² e^{−L²/32}`. -/
def critWeight (K : ℕ) (L : ℝ) (n : ℕ) : ℝ :=
  L * ((1 + Real.log n) * (Real.sqrt n)⁻¹) + L ^ (5 / 2 : ℝ) * dualTailFactor L K +
    L ^ 2 * Real.exp (-(L ^ 2) / 32)

theorem critWeight_nonneg (K : ℕ) {L : ℝ} (hL : 0 ≤ L) (n : ℕ) : 0 ≤ critWeight K L n := by
  unfold critWeight
  have := Real.log_natCast_nonneg n
  have := dualTailFactor_nonneg hL K
  positivity

/-- The near-line small dual pairs of a mode twist cost at most `768 K₀³ L (1 + log n) n^{−1/2}`. -/
theorem small_mode_le (hP : ∀ p ∈ P, p.Prime) {L : ℝ} (hL : 16 ≤ L) {n n₀ : ℕ} (hn : n ≠ 0)
    {j : ℤ} (hj : j ∈ bohrModes) {c : P → ℤ} (hc : c ∈ Fintype.piFinset (fun _ : P => bohrModes)) :
    L ^ (-(1 / 4 : ℝ)) * ∑' Q, smallWeight L L⁻¹
        (vecNum (vecOf P n - (j • vecOf P n₀ + c)) * roughPart P n)
        (vecDen (vecOf P n - (j • vecOf P n₀ + c))) Q ≤
      768 * (twistBound P n₀ : ℝ) ^ 3 * (L * ((1 + Real.log n) * (Real.sqrt n)⁻¹)) := by
  set h : ℕ := vecNum (vecOf P n - (j • vecOf P n₀ + c)) * roughPart P n with hh
  set k : ℕ := vecDen (vecOf P n - (j • vecOf P n₀ + c)) with hk
  set K₀ : ℝ := (twistBound P n₀ : ℝ) with hK₀
  have hL0 : 0 < L := by linarith
  have hK1 : 1 ≤ K₀ := by rw [hK₀]; exact_mod_cast twistBound_pos hP n₀
  have hh1 : 1 ≤ h := Nat.mul_pos (vecNum_pos hP _) (roughPart_pos hn)
  have hk1 : 1 ≤ k := vecDen_pos hP _
  have hkK : (k : ℝ) ≤ K₀ := by
    have := vecDen_mode_le hP hj hc (n := n) (n₀ := n₀)
    show ((vecDen (vecOf P n - (j • vecOf P n₀ + c)) : ℕ) : ℝ) ≤ (twistBound P n₀ : ℝ)
    exact_mod_cast this
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk1
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
  have hlogn : 0 ≤ Real.log n := Real.log_nonneg hn1
  have hw0 : 0 ≤ L * ((1 + Real.log n) * (Real.sqrt n)⁻¹) := by positivity
  have hδ : 0 < L⁻¹ := inv_pos.mpr hL0
  rcases le_or_gt (2 * k * L) (h : ℝ) with hbig | hsmall
  · have hz : ∑' Q, smallWeight L L⁻¹ h k Q = 0 := by
      rw [show (fun Q => smallWeight L L⁻¹ h k Q) = fun _ => (0 : ℝ) from
        funext fun Q => smallWeight_eq_zero_of_le hk1 hL0 hbig Q, tsum_zero]
    rw [hz, mul_zero]
    positivity
  · have hJ := shell_count_le_log hδ (by rw [one_div]) (by linarith : (1 : ℝ) < L)
    have hsm := tsum_smallWeight_le (h := h) (k := k) hh1 hk1 hL0 hδ
    set J : ℝ := (Nat.find (exists_shell_count hδ) : ℝ) with hJdef
    have hlog2 : (1 : ℝ) / 2 < Real.log 2 := by
      have := Real.log_two_gt_d9; linarith
    have hJ2 : J ≤ 2 * Real.log L := by
      have hlogL : 0 ≤ Real.log L := Real.log_nonneg (by linarith)
      refine hJ.trans ?_
      rw [div_le_iff₀ (by linarith)]
      nlinarith
    -- `n ≤ K₀ h k < 2 K₀³ L`
    have hnX : (n : ℝ) ≤ 2 * K₀ ^ 3 * L := by
      have h1 := natCast_le_twistBound_mul_mode hP (n₀ := n₀) hn hj hc
      have h2 : (h : ℝ) * k ≤ 2 * K₀ ^ 2 * L := by
        have hk2 : (k : ℝ) * k ≤ K₀ * K₀ := mul_le_mul hkK hkK hk0.le (by linarith)
        calc (h : ℝ) * k ≤ 2 * k * L * k := mul_le_mul_of_nonneg_right hsmall.le hk0.le
          _ = 2 * L * ((k : ℝ) * k) := by ring
          _ ≤ 2 * L * (K₀ * K₀) := mul_le_mul_of_nonneg_left hk2 (by positivity)
          _ = 2 * K₀ ^ 2 * L := by ring
      calc (n : ℝ) ≤ K₀ * ((h : ℝ) * k) := h1
        _ ≤ K₀ * (2 * K₀ ^ 2 * L) := mul_le_mul_of_nonneg_left h2 (by linarith)
        _ = 2 * K₀ ^ 3 * L := by ring
    have hkey := sqrt_mul_log_le hn1 hnX
    have hLX : Real.log L ≤ Real.log (2 * K₀ ^ 3 * L) :=
      Real.log_le_log hL0 (by nlinarith [pow_le_pow_left₀ (by norm_num) hK1 3])
    have hsX : Real.sqrt (2 * K₀ ^ 3 * L) ≤ 2 * K₀ ^ 2 * Real.sqrt L := by
      rw [Real.sqrt_mul (by positivity)]
      refine mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _)
      rw [Real.sqrt_le_left (by positivity)]
      nlinarith [pow_le_pow_right₀ hK1 (by norm_num : 3 ≤ 4)]
    have hsn : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by linarith)
    -- `L^{1/2} log L ≤ 8 K₀² L (1 + log n) n^{−1/2}`
    have hmain : Real.sqrt L * Real.log L ≤
        8 * K₀ ^ 2 * (L * ((1 + Real.log n) * (Real.sqrt n)⁻¹)) := by
      have h1 : Real.sqrt n * Real.log L ≤ 4 * (2 * K₀ ^ 2 * Real.sqrt L) * (1 + Real.log n) := by
        calc Real.sqrt n * Real.log L ≤ Real.sqrt n * Real.log (2 * K₀ ^ 3 * L) :=
              mul_le_mul_of_nonneg_left hLX hsn.le
          _ ≤ 4 * Real.sqrt (2 * K₀ ^ 3 * L) * (1 + Real.log n) := hkey
          _ ≤ 4 * (2 * K₀ ^ 2 * Real.sqrt L) * (1 + Real.log n) := by gcongr
      have hLs : L = Real.sqrt L * Real.sqrt L := (Real.mul_self_sqrt hL0.le).symm
      have h1' : Real.log L ≤ 4 * (2 * K₀ ^ 2 * Real.sqrt L) * (1 + Real.log n) / Real.sqrt n := by
        rw [le_div_iff₀ hsn]; linarith
      calc Real.sqrt L * Real.log L
          ≤ Real.sqrt L * (4 * (2 * K₀ ^ 2 * Real.sqrt L) * (1 + Real.log n) / Real.sqrt n) :=
            mul_le_mul_of_nonneg_left h1' (Real.sqrt_nonneg _)
        _ = 8 * K₀ ^ 2 * ((Real.sqrt L * Real.sqrt L) * ((1 + Real.log n) * (Real.sqrt n)⁻¹)) := by
            rw [div_eq_mul_inv]; ring
        _ = 8 * K₀ ^ 2 * (L * ((1 + Real.log n) * (Real.sqrt n)⁻¹)) := by rw [← hLs]
    have hpow : L ^ (-(1 / 4 : ℝ)) * L ^ (3 / 4 : ℝ) = Real.sqrt L := by
      rw [← Real.rpow_add hL0, Real.sqrt_eq_rpow]; norm_num
    have hlogL : 0 ≤ Real.log L := Real.log_nonneg (by linarith)
    calc L ^ (-(1 / 4 : ℝ)) * ∑' Q, smallWeight L L⁻¹ h k Q
        ≤ L ^ (-(1 / 4 : ℝ)) * (48 * k * L ^ (3 / 4 : ℝ) * J) :=
          mul_le_mul_of_nonneg_left hsm (by positivity)
      _ = 48 * k * J * (L ^ (-(1 / 4 : ℝ)) * L ^ (3 / 4 : ℝ)) := by ring
      _ = 48 * k * J * Real.sqrt L := by rw [hpow]
      _ ≤ 48 * K₀ * (2 * Real.log L) * Real.sqrt L := by
          have hJ0 : 0 ≤ J := Nat.cast_nonneg _
          gcongr
      _ = 96 * K₀ * (Real.sqrt L * Real.log L) := by ring
      _ ≤ 96 * K₀ * (8 * K₀ ^ 2 * (L * ((1 + Real.log n) * (Real.sqrt n)⁻¹))) :=
          mul_le_mul_of_nonneg_left hmain (by positivity)
      _ = 768 * K₀ ^ 3 * (L * ((1 + Real.log n) * (Real.sqrt n)⁻¹)) := by ring

/-- The near-resonant mass at `δ = 1/L`: `L · 𝒩_L(h, k, 1/L) ≤ 16 K₀ L s` when `k ≤ K₀` and
`√(2k/h) ≤ s`. -/
theorem near_crit_le {L K₀ : ℝ} (hL : 16 ≤ L) {h k : ℕ} (hh1 : 1 ≤ h) (hk1 : 1 ≤ k)
    (hkK : (k : ℝ) ≤ K₀) {s : ℝ} (hsq : Real.sqrt (2 * k / h) ≤ s) :
    L * nearMass L h k L⁻¹ ≤ 16 * K₀ * (L * s) := by
  have hL0 : 0 < L := by linarith
  have hδ4 : L⁻¹ ≤ 1 / 4 := by rw [inv_le_comm₀ hL0 (by norm_num)]; linarith
  have hm : nearMass L h k L⁻¹ ≤ 16 * L⁻¹ * k * L * Real.sqrt (2 * k / h) :=
    tsum_nearRes_le' hh1 hk1 (inv_pos.mpr hL0) hδ4 hL0
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hK₀ : 0 ≤ K₀ := hk0.trans hkK
  calc L * nearMass L h k L⁻¹ ≤ L * (16 * L⁻¹ * k * L * Real.sqrt (2 * k / h)) :=
        mul_le_mul_of_nonneg_left hm hL0.le
    _ = 16 * k * (L * L⁻¹) * (L * Real.sqrt (2 * k / h)) := by ring
    _ ≤ 16 * K₀ * 1 * (L * s) := by
        rw [mul_inv_cancel₀ hL0.ne']; gcongr
    _ = 16 * K₀ * (L * s) := by ring

/-- The detuned pairs at `δ = 1/L`: `L Σ farWeight ≤ 64 K₀ L s + ζ₂ L^{5/2} T_K(L)`. -/
theorem far_crit_le {L K₀ : ℝ} (hL : 16 ≤ L) {K : ℕ} (hK : 2 ≤ K) {h k : ℕ} (hh1 : 1 ≤ h)
    (hk1 : 1 ≤ k) (hkK : (k : ℝ) ≤ K₀) {s : ℝ} (hsq : Real.sqrt (2 * k / h) ≤ s) :
    L * ∑' Q, farWeight L L⁻¹ K h k Q ≤
      64 * K₀ * (L * s) + pairZeta * (L ^ (5 / 2 : ℝ) * dualTailFactor L K) := by
  have hL0 : 0 < L := by linarith
  have hf := (tsum_farWeight_le hh1 hk1 hL0 (inv_pos.mpr hL0) hK).2
  rw [mul_inv_cancel₀ hL0.ne', one_pow, inv_one, mul_one] at hf
  have h34 : L * L ^ (3 / 4 : ℝ) ≤ L ^ (5 / 2 : ℝ) := by
    rw [← Real.rpow_one_add' hL0.le (by norm_num)]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  have hq : ((L / 8) ^ K)⁻¹ ≤ dualTailFactor L K := by
    unfold dualTailFactor; have := Real.exp_pos (-(L ^ 2) / 128); linarith
  have hpz := pairZeta_nonneg
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hK₀ : 0 ≤ K₀ := hk0.trans hkK
  calc L * ∑' Q, farWeight L L⁻¹ K h k Q
      ≤ L * (64 * L⁻¹ * k * L * Real.sqrt (2 * k / h) +
          pairZeta * L ^ (3 / 4 : ℝ) * ((L / 8) ^ K)⁻¹) := mul_le_mul_of_nonneg_left hf hL0.le
    _ = 64 * k * (L * L⁻¹) * (L * Real.sqrt (2 * k / h)) +
          pairZeta * (L * L ^ (3 / 4 : ℝ)) * ((L / 8) ^ K)⁻¹ := by ring
    _ ≤ 64 * K₀ * 1 * (L * s) + pairZeta * L ^ (5 / 2 : ℝ) * dualTailFactor L K := by
        rw [mul_inv_cancel₀ hL0.ne']; gcongr
    _ = 64 * K₀ * (L * s) + pairZeta * (L ^ (5 / 2 : ℝ) * dualTailFactor L K) := by ring

/-- **The endpoint envelope of a mode twist**: `shellEnvelope ≤ E · critWeight`. -/
theorem shellEnvelope_mode_le (hP : ∀ p ∈ P, p.Prime) {C L : ℝ} (hC : 0 ≤ C) (hL : 16 ≤ L)
    {K : ℕ} (hK : 2 ≤ K) {n n₀ : ℕ} (hn : n ≠ 0) {j : ℤ} (hj : j ∈ bohrModes) {c : P → ℤ}
    (hc : c ∈ Fintype.piFinset (fun _ : P => bohrModes)) :
    shellEnvelope C L K (vecNum (vecOf P n - (j • vecOf P n₀ + c)) * roughPart P n)
        (vecDen (vecOf P n - (j • vecOf P n₀ + c))) ≤
      (2 * Real.sqrt (twistBound P n₀) * (C + 2 * Real.log (twistBound P n₀) + 2) +
        C * (928 * (twistBound P n₀ : ℝ) ^ 3 + pairZeta + 1)) * critWeight K L n := by
  set h : ℕ := vecNum (vecOf P n - (j • vecOf P n₀ + c)) * roughPart P n with hh
  set k : ℕ := vecDen (vecOf P n - (j • vecOf P n₀ + c)) with hk
  set K₀ : ℝ := (twistBound P n₀ : ℝ) with hK₀
  have hL0 : 0 < L := by linarith
  have hK1 : 1 ≤ K₀ := by rw [hK₀]; exact_mod_cast twistBound_pos hP n₀
  have hh1 : 1 ≤ h := Nat.mul_pos (vecNum_pos hP _) (roughPart_pos hn)
  have hk1 : 1 ≤ k := vecDen_pos hP _
  have hkK : (k : ℝ) ≤ K₀ := by
    have := vecDen_mode_le hP hj hc (n := n) (n₀ := n₀)
    show ((vecDen (vecOf P n - (j • vecOf P n₀ + c)) : ℕ) : ℝ) ≤ (twistBound P n₀ : ℝ)
    exact_mod_cast this
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
  have hlogn : 0 ≤ Real.log n := Real.log_nonneg hn1
  set w : ℝ := L * ((1 + Real.log n) * (Real.sqrt n)⁻¹) with hw
  set T : ℝ := L ^ (5 / 2 : ℝ) * dualTailFactor L K with hT
  set Z : ℝ := L ^ 2 * Real.exp (-(L ^ 2) / 32) with hZ
  have hw0 : 0 ≤ w := by positivity
  have hT0 : 0 ≤ T := mul_nonneg (by positivity) (dualTailFactor_nonneg hL0.le K)
  have hZ0 : 0 ≤ Z := by positivity
  have hsw : L * (2 * K₀ ^ 2 * (Real.sqrt n)⁻¹) ≤ 2 * K₀ ^ 2 * w := by
    have h1 : (Real.sqrt n)⁻¹ ≤ (1 + Real.log n) * (Real.sqrt n)⁻¹ :=
      le_mul_of_one_le_left (by positivity) (by linarith)
    have h2 : L * (Real.sqrt n)⁻¹ ≤ w := mul_le_mul_of_nonneg_left h1 hL0.le
    calc L * (2 * K₀ ^ 2 * (Real.sqrt n)⁻¹) = 2 * K₀ ^ 2 * (L * (Real.sqrt n)⁻¹) := by ring
      _ ≤ 2 * K₀ ^ 2 * w := mul_le_mul_of_nonneg_left h2 (by positivity)
  have hsq := sqrt_two_mul_div_mode_le hP (n₀ := n₀) hn hj hc
  have hnear := near_crit_le hL hh1 hk1 hkK hsq
  have hfar := far_crit_le hL hK hh1 hk1 hkK hsq
  have hsmall := small_mode_le hP hL (n₀ := n₀) hn hj hc
  have hdiag := diag_mode_le hP hC hL0 hn hj hc (n₀ := n₀)
  have hK₀0 : 0 ≤ K₀ := by linarith
  have hnear' : L * nearMass L h k L⁻¹ ≤ 32 * K₀ ^ 3 * w := by
    have := mul_le_mul_of_nonneg_left hsw (by positivity : (0 : ℝ) ≤ 16 * K₀)
    nlinarith
  have hfar' : L * ∑' Q, farWeight L L⁻¹ K h k Q ≤ 128 * K₀ ^ 3 * w + pairZeta * T := by
    have := mul_le_mul_of_nonneg_left hsw (by positivity : (0 : ℝ) ≤ 64 * K₀)
    nlinarith
  set D₁ : ℝ := 2 * Real.sqrt K₀ * (C + 2 * Real.log K₀ + 2) with hD₁
  have hD₁0 : 0 ≤ D₁ := by
    have := Real.log_nonneg hK1
    rw [hD₁]; positivity
  have hdiag' : (Real.sqrt ((h : ℝ) * k))⁻¹ * (2 * L * (C + 2 * Real.log ((h : ℝ) * k))) ≤
      D₁ * w := by
    refine hdiag.trans (le_of_eq ?_)
    rw [hw, hD₁]; ring
  have hcw : critWeight K L n = w + T + Z := by rw [critWeight]
  rw [hcw]
  unfold shellEnvelope
  have hpz := pairZeta_nonneg
  have hK30 : 0 ≤ K₀ ^ 3 := by positivity
  have hsum : L * nearMass L h k L⁻¹ + L * ∑' Q, farWeight L L⁻¹ K h k Q +
      L ^ (-(1 / 4 : ℝ)) * ∑' Q, smallWeight L L⁻¹ h k Q + T + Z ≤
      (928 * K₀ ^ 3 + pairZeta + 1) * (w + T + Z) := by
    have e : (928 * K₀ ^ 3 + pairZeta + 1) * (w + T + Z) =
        928 * K₀ ^ 3 * w + pairZeta * T + T + Z +
          (928 * K₀ ^ 3 * (T + Z) + pairZeta * (w + Z) + w) := by ring
    have h0 : 0 ≤ 928 * K₀ ^ 3 * (T + Z) + pairZeta * (w + Z) + w := by positivity
    rw [e]
    linarith
  calc (Real.sqrt ((h : ℝ) * k))⁻¹ * (2 * L * (C + 2 * Real.log ((h : ℝ) * k))) +
        C * (L * nearMass L h k L⁻¹ + L * ∑' Q, farWeight L L⁻¹ K h k Q +
          L ^ (-(1 / 4 : ℝ)) * ∑' Q, smallWeight L L⁻¹ h k Q + T + Z)
      ≤ D₁ * w + C * ((928 * K₀ ^ 3 + pairZeta + 1) * (w + T + Z)) :=
        add_le_add hdiag' (mul_le_mul_of_nonneg_left hsum hC)
    _ ≤ (D₁ + C * (928 * K₀ ^ 3 + pairZeta + 1)) * (w + T + Z) := by
        have : 0 ≤ D₁ * (T + Z) := mul_nonneg hD₁0 (by linarith)
        have e : (D₁ + C * (928 * K₀ ^ 3 + pairZeta + 1)) * (w + T + Z) =
            D₁ * w + C * ((928 * K₀ ^ 3 + pairZeta + 1) * (w + T + Z)) + D₁ * (T + Z) := by ring
        rw [e]; linarith

/-- **The notch main term at the critical endpoint.** For fixed `P`, `ε`, `n₀` and `K ≥ 2`,
uniformly in `L ≥ 16` and `n ≠ 0`:

`‖M_L(log n) − mainWeight(n) e_P ∫ ω log t‖ ≤ D (L (1 + log n) n^{−1/2}
  + L^{5/2} ((L/8)^{−K} + e^{−L²/128}) + L² e^{−L²/32})`. -/
theorem exists_norm_weightedMoment_sub_mainWeight_le_crit (hP : ∀ p ∈ P, p.Prime) {K : ℕ}
    (hK : 2 ≤ K) (ε : ℝ) {n₀ : ℕ} (hn₀ : IsSmoothOver P n₀) :
    ∃ D, 0 ≤ D ∧ ∀ {L : ℝ}, 16 ≤ L → ∀ {n : ℕ}, n ≠ 0 →
      ‖ZetaNotch.weightedMoment L (notchWeight P ε n₀) (Real.log n) -
          ((mainWeight P ε n₀ n * ∏ p : P, (1 - primeHalf p ^ 2) : ℝ) : ℂ) * logWindow L‖ ≤
        D * critWeight K L n := by
  classical
  obtain ⟨C, hC, hmain⟩ := exists_norm_twistedMoment_sub_le_shell K
  set B : ℝ := ∑ j ∈ bohrModes, ∑ c ∈ Fintype.piFinset (fun _ : P => bohrModes),
    |modeCoeff ε j c| with hB
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun c _ => abs_nonneg _
  set E : ℝ := 2 * Real.sqrt (twistBound P n₀) * (C + 2 * Real.log (twistBound P n₀) + 2) +
    C * (928 * (twistBound P n₀ : ℝ) ^ 3 + pairZeta + 1) with hE
  have hK1 : (1 : ℝ) ≤ twistBound P n₀ := by exact_mod_cast twistBound_pos hP n₀
  have hE0 : 0 ≤ E := by
    have := Real.log_nonneg hK1
    have := pairZeta_nonneg
    rw [hE]; positivity
  refine ⟨B * E, mul_nonneg hB0 hE0, fun {L} hL {n} hn => ?_⟩
  have hL0 : 0 < L := by linarith
  refine (norm_weightedMoment_sub_main_le_of_twist hP hL0 (shellEnvelope C L K)
    (fun _ _ hh hk hcop => hmain hL hh hk hcop) ε hn hn₀).trans ?_
  rw [hB, Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_le_sum fun j hj => ?_
  rw [Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_le_sum fun c hc => ?_
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left (shellEnvelope_mode_le hP hC hL hK hn hj hc) (abs_nonneg _)

end RHTower.WeilAbscissa
