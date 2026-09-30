import GaloisForLFunctions.RHTower.WeilLogSummableRigidity

/-!
# The notch main term with an envelope decaying in the twist

For the truncated notch weight `q = notchWeight P ε n₀` at scale `L ≥ 16`, every `n ≠ 0`, and
`0 < a < 1/2` (`η = 1/2 − a`), the per-twist remainder of the weighted moment decays like `n^{−a}`
up to terms uniform in `n` (`exists_norm_weightedMoment_sub_mainWeight_le_decay`):

`‖M_L(log n) − mainWeight(n) e_P ∫ ω log t‖ ≤ C (L n^{−a} + δ L^{3/2+a} n^{−a} + L²/(Lδ)^K
  + L² e^{−L²/32})`.

The mode twists of `n` are coprime ratios `h/k` with `k ≤ K₀` and `hk ≥ n/K₀`, `K₀ = twistBound`.
The near-resonant mass obeys both `L · nearMass ≤ 24 δ k L^{3/2}` and
`L · nearMass ≤ 16 δ k L² √(2k/h) ≤ 32 δ K₀³ L² n^{−1/2}`. The first is used for `n ≤ L`, the
second for `n > L`, and both are `≤ (24K₀ + 32K₀³) δ L^{3/2+a} n^{−a}` (`mul_nearMass_mode_le`).
The diagonal envelope is `≤ C L (1 + log n) n^{−1/2} ≤ C (1 + 1/η) L n^{−a}`.
-/

noncomputable section

open Complex MeasureTheory Set Filter Topology RHTower GaloisForLFunctions.HTGeometry

namespace RHTower.WeilAbscissa

open RHTower.ZetaNotch RHTower.SmoothNumbers RHTower.WeilFiniteSupport RHTower.WeilLogSummable

variable {P : Finset ℕ}

/-! ## The twist envelope with the near-resonant mass kept -/

/-- The remainder envelope of a coprime twist `h/k`, keeping the near-resonant mass. -/
def nearEnvelope (C L δ : ℝ) (K : ℕ) (h k : ℕ) : ℝ :=
  (Real.sqrt ((h : ℝ) * k))⁻¹ * (2 * L * (C + 2 * Real.log ((h : ℝ) * k)))
    + C * (L * nearMass L h k δ + L ^ 2 / (L * δ) ^ K + L ^ 2 * Real.exp (-(L ^ 2) / 32))

/-- **Main term of a coprime twist from a diagonal remainder.** A bound `R` on the distance of the
twisted moment from its diagonal `(hk)^{−1/2} D_L(hk)` gives the distance from
`(hk)^{−1/2} ∫ ω log t` up to the diagonal envelope `(hk)^{−1/2} · 2L (C + 2 log hk)`. -/
theorem exists_norm_twistedMoment_sub_logWindow_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {L : ℝ}, 16 ≤ L → ∀ {h k : ℕ}, 0 < h → 0 < k → ∀ R : ℝ,
      ‖ZetaNotch.twistedMoment L (Real.log h - Real.log k) -
          ((Real.sqrt (h * k) : ℂ))⁻¹ * diagMain L (h * k)‖ ≤ R →
      ‖ZetaNotch.twistedMoment L (Real.log h - Real.log k) -
          (((Real.sqrt ((h : ℝ) * k))⁻¹ : ℝ) : ℂ) * logWindow L‖ ≤
        (Real.sqrt ((h : ℝ) * k))⁻¹ * (2 * L * (C + 2 * Real.log ((h : ℝ) * k))) + R := by
  obtain ⟨C, hC, hdiag⟩ := exists_norm_diagMain_sub_le
  refine ⟨C, hC, fun {L} hL {h k} hh0 hk0 R hR => ?_⟩
  have hL0 : 0 < L := by linarith
  set N : ℝ := (h : ℝ) * k with hN
  have hN1 : 1 ≤ N := by
    have : (1 : ℝ) ≤ h := by exact_mod_cast hh0
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk0
    nlinarith
  set w : ℝ := (Real.sqrt N)⁻¹ with hw
  have hw0 : 0 ≤ w := inv_nonneg.mpr (Real.sqrt_nonneg _)
  have hwN : ((Real.sqrt N : ℂ))⁻¹ = (w : ℂ) := by rw [hw, Complex.ofReal_inv]
  rw [hwN] at hR
  have hD := hdiag hL hN1
  have hwhat := norm_windowHat_le hL0 0
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg hN1
  set ξ : ℝ := Real.log h - Real.log k with hξ
  have hsplit : ZetaNotch.twistedMoment L ξ - (w : ℂ) * logWindow L =
      (ZetaNotch.twistedMoment L ξ - (w : ℂ) * diagMain L N) +
        (w : ℂ) * (diagMain L N - (logWindow L - windowHat L 0 * (Real.log N : ℂ))) -
        (w : ℂ) * (windowHat L 0 * (Real.log N : ℂ)) := by ring
  rw [hsplit]
  have hA : ‖(w : ℂ) * (diagMain L N - (logWindow L - windowHat L 0 * (Real.log N : ℂ)))‖ ≤
      w * (2 * L * (C + Real.log N)) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hw0]
    exact mul_le_mul_of_nonneg_left hD hw0
  have hB : ‖(w : ℂ) * (windowHat L 0 * (Real.log N : ℂ))‖ ≤ w * (2 * L * Real.log N) := by
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hw0,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlogN]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hwhat hlogN) hw0
  set X := ZetaNotch.twistedMoment L ξ - (w : ℂ) * diagMain L N with hX
  set Y := (w : ℂ) * (diagMain L N - (logWindow L - windowHat L 0 * (Real.log N : ℂ))) with hY
  set Z := (w : ℂ) * (windowHat L 0 * (Real.log N : ℂ)) with hZ
  have htri : ‖X + Y - Z‖ ≤ ‖X‖ + ‖Y‖ + ‖Z‖ := by
    have h1 := norm_sub_le (X + Y) Z
    have h2 := norm_add_le X Y
    linarith
  refine htri.trans ?_
  nlinarith [hA, hB, hR]

/-- **Main term of a coprime twist, near-resonant form.** -/
theorem exists_norm_twistedMoment_sub_le_near (K : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {L δ : ℝ}, 16 ≤ L → 0 < δ → ∀ {h k : ℕ}, 0 < h → 0 < k →
      Nat.Coprime h k →
      ‖ZetaNotch.twistedMoment L (Real.log h - Real.log k) -
          (((Real.sqrt ((h : ℝ) * k))⁻¹ : ℝ) : ℂ) * logWindow L‖ ≤
        nearEnvelope C L δ K h k := by
  obtain ⟨C₁, hC₁, h₁⟩ := exists_norm_twistedMoment_sub_diag_le K
  obtain ⟨C₂, hC₂, h₂⟩ := exists_norm_twistedMoment_sub_logWindow_le
  refine ⟨max C₁ C₂, le_max_of_le_left hC₁, fun {L δ} hL hδ {h k} hh0 hk0 hcop => ?_⟩
  have hL0 : 0 < L := by linarith
  have hN1 : (1 : ℝ) ≤ (h : ℝ) * k := by
    have : (1 : ℝ) ≤ h := by exact_mod_cast hh0
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk0
    nlinarith
  have hrem := (h₁ hL hδ hh0 hk0 hcop).trans (mul_le_mul_of_nonneg_right (le_max_left C₁ C₂)
    (add_nonneg (add_nonneg (mul_nonneg hL0.le (nearMass_nonneg hL0.le h k δ)) (by positivity))
      (by positivity)))
  refine (h₂ hL hh0 hk0 _ hrem).trans ?_
  unfold nearEnvelope
  gcongr
  exact le_max_right _ _

/-- **The weighted moment from coprime twist bounds.** If every coprime twist `h/k` obeys
`‖M_L(log h − log k) − (hk)^{−1/2} ∫ ω log t‖ ≤ Env(h, k)`, the notch-weighted moment at `log n`
deviates from its main term by at most `Σ_{j,c} |m_{j,c}| Env(h_{j,c}, k_{j,c})` over the mode
twists of `n`. -/
theorem norm_weightedMoment_sub_main_le_of_twist (hP : ∀ p ∈ P, p.Prime) {L : ℝ} (hL : 0 < L)
    (Env : ℕ → ℕ → ℝ) (hEnv : ∀ h k : ℕ, 0 < h → 0 < k → Nat.Coprime h k →
      ‖ZetaNotch.twistedMoment L (Real.log h - Real.log k) -
          (((Real.sqrt ((h : ℝ) * k))⁻¹ : ℝ) : ℂ) * logWindow L‖ ≤ Env h k)
    (ε : ℝ) {n n₀ : ℕ} (hn : n ≠ 0) (hn₀ : IsSmoothOver P n₀) :
    ‖ZetaNotch.weightedMoment L (notchWeight P ε n₀) (Real.log n) -
        ((mainWeight P ε n₀ n * ∏ p : P, (1 - primeHalf p ^ 2) : ℝ) : ℂ) * logWindow L‖ ≤
      ∑ j ∈ bohrModes, ∑ c ∈ Fintype.piFinset (fun _ : P => bohrModes),
        |modeCoeff ε j c| * Env (vecNum (vecOf P n - (j • vecOf P n₀ + c)) * roughPart P n)
          (vecDen (vecOf P n - (j • vecOf P n₀ + c))) := by
  classical
  set r := roughPart P n with hr
  have hr0 : 0 < r := roughPart_pos hn
  set b : ℤ → (P → ℤ) → (P → ℤ) := fun j c => vecOf P n - (j • vecOf P n₀ + c) with hb
  have hfreq : ∀ j c, Real.log n - modeFreq n₀ j c =
      Real.log ((vecNum (b j c) * r : ℕ) : ℝ) - Real.log (vecDen (b j c)) := by
    intro j c
    have hnum : (0 : ℝ) < vecNum (b j c) := by exact_mod_cast vecNum_pos hP (b j c)
    have hrr : (0 : ℝ) < r := by exact_mod_cast hr0
    rw [Nat.cast_mul, Real.log_mul hnum.ne' hrr.ne', log_eq_smooth_add_rough hP hn,
      ← vecFreq_vecOf_eq_log_smoothPart hP, modeFreq_eq hn₀.2]
    have := vecFreq_eq hP (b j c)
    rw [hb] at this ⊢
    simp only at this ⊢
    rw [vecFreq_sub] at this
    linarith
  have hweight : ∀ j c, (Real.sqrt (((vecNum (b j c) * r : ℕ) : ℝ) * vecDen (b j c)))⁻¹ =
      (∏ p : P, primeHalf p ^ ((b j c) p).natAbs) * (Real.sqrt r)⁻¹ := by
    intro j c
    rw [← inv_sqrt_vecNum_mul_vecDen (b j c), ← mul_inv, ← Real.sqrt_mul (by positivity)]
    congr 2
    push_cast
    ring
  rw [weightedMoment_notchWeight_eq hL]
  simp_rw [hfreq]
  have hsum := sum_modeCoeff_mul_weight_general (n := n) hn₀ ε
  have hmainC : ((mainWeight P ε n₀ n * ∏ p : P, (1 - primeHalf p ^ 2) : ℝ) : ℂ) * logWindow L =
      ∑ j ∈ bohrModes, ∑ c ∈ Fintype.piFinset (fun _ : P => bohrModes),
        (modeCoeff ε j c : ℂ) *
          ((((Real.sqrt (((vecNum (b j c) * r : ℕ) : ℝ) * vecDen (b j c)))⁻¹ : ℝ) : ℂ) *
            logWindow L) := by
    have e : mainWeight P ε n₀ n * ∏ p : P, (1 - primeHalf p ^ 2) =
        (((1 + ε ^ 2) * (if vecOf P n = 0 then 1 else 0) +
          ε * (if vecOf P n = vecOf P n₀ then 1 else 0)) * ∏ p : P, (1 - primeHalf p ^ 2)) *
            (Real.sqrt r)⁻¹ := by
      unfold mainWeight
      ring
    rw [e, ← hsum]
    simp_rw [hweight]
    push_cast
    rw [Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun c _ => ?_
    ring
  rw [hmainC, ← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun c _ => ?_)
  rw [← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hcop : Nat.Coprime (vecNum (b j c) * r) (vecDen (b j c)) :=
    Nat.Coprime.mul_left (coprime_vecNum_vecDen hP (b j c)) (coprime_roughPart_vecDen hP hn (b j c))
  have h := hEnv _ _ (Nat.mul_pos (vecNum_pos hP (b j c)) hr0) (vecDen_pos hP (b j c)) hcop
  push_cast at h ⊢
  exact mul_le_mul_of_nonneg_left h (abs_nonneg _)

/-- **The weighted moment at a general twist, near-resonant form.** -/
theorem exists_norm_weightedMoment_sub_main_le_near (hP : ∀ p ∈ P, p.Prime) (K : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {L δ : ℝ}, 16 ≤ L → 0 < δ → ∀ (ε : ℝ) {n n₀ : ℕ},
      n ≠ 0 → IsSmoothOver P n₀ →
      ‖ZetaNotch.weightedMoment L (notchWeight P ε n₀) (Real.log n) -
          ((mainWeight P ε n₀ n * ∏ p : P, (1 - primeHalf p ^ 2) : ℝ) : ℂ) * logWindow L‖ ≤
        ∑ j ∈ bohrModes, ∑ c ∈ Fintype.piFinset (fun _ : P => bohrModes),
          |modeCoeff ε j c| * nearEnvelope C L δ K
            (vecNum (vecOf P n - (j • vecOf P n₀ + c)) * roughPart P n)
            (vecDen (vecOf P n - (j • vecOf P n₀ + c))) := by
  obtain ⟨C, hC, hmain⟩ := exists_norm_twistedMoment_sub_le_near K
  exact ⟨C, hC, fun {L δ} hL hδ ε {n n₀} hn hn₀ =>
    norm_weightedMoment_sub_main_le_of_twist hP (by linarith) _
      (fun _ _ hh hk hcop => hmain hL hδ hh hk hcop) ε hn hn₀⟩

/-! ## Envelopes of mode twists -/

/-- `(hk)^{−1/2} ≤ √K₀ n^{−1/2}` for a mode twist of `n`. -/
theorem inv_sqrt_mode_le (hP : ∀ p ∈ P, p.Prime) {n n₀ : ℕ} (hn : n ≠ 0) {j : ℤ}
    (hj : j ∈ bohrModes) {c : P → ℤ} (hc : c ∈ Fintype.piFinset (fun _ : P => bohrModes)) :
    (Real.sqrt (((vecNum (vecOf P n - (j • vecOf P n₀ + c)) * roughPart P n : ℕ) : ℝ) *
        vecDen (vecOf P n - (j • vecOf P n₀ + c))))⁻¹ ≤
      Real.sqrt (twistBound P n₀) * (Real.sqrt n)⁻¹ := by
  set b := vecOf P n - (j • vecOf P n₀ + c) with hb
  set r := roughPart P n with hr
  have hr0 : (0 : ℝ) < r := by exact_mod_cast roughPart_pos hn
  have hw := weight_mode_le_prod hP hj hc (n := n) (n₀ := n₀)
  have hsplitN : (((vecNum b * r : ℕ) : ℝ) * vecDen b) = ((vecNum b : ℝ) * vecDen b) * r := by
    push_cast; ring
  have hwN : (Real.sqrt (((vecNum b * r : ℕ) : ℝ) * vecDen b))⁻¹ =
      (∏ p : P, primeHalf p ^ (b p).natAbs) * (Real.sqrt r)⁻¹ := by
    rw [hsplitN, Real.sqrt_mul (by positivity), mul_inv, inv_sqrt_vecNum_mul_vecDen b]
  rw [hwN, ← sqrt_smooth_mul_rough hn, mul_inv, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right hw (by positivity)

/-- The diagonal envelope of a mode twist. -/
theorem diag_mode_le (hP : ∀ p ∈ P, p.Prime) {C L : ℝ} (hC : 0 ≤ C) (hL : 0 < L) {n n₀ : ℕ}
    (hn : n ≠ 0) {j : ℤ} (hj : j ∈ bohrModes) {c : P → ℤ}
    (hc : c ∈ Fintype.piFinset (fun _ : P => bohrModes)) :
    (Real.sqrt (((vecNum (vecOf P n - (j • vecOf P n₀ + c)) * roughPart P n : ℕ) : ℝ) *
        vecDen (vecOf P n - (j • vecOf P n₀ + c))))⁻¹ *
      (2 * L * (C + 2 * Real.log (((vecNum (vecOf P n - (j • vecOf P n₀ + c)) * roughPart P n :
        ℕ) : ℝ) * vecDen (vecOf P n - (j • vecOf P n₀ + c))))) ≤
      2 * L * Real.sqrt (twistBound P n₀) * (C + 2 * Real.log (twistBound P n₀) + 2) *
        ((1 + Real.log n) * (Real.sqrt n)⁻¹) := by
  set b := vecOf P n - (j • vecOf P n₀ + c) with hb
  set r := roughPart P n with hr
  have hr0 : (0 : ℝ) < r := by exact_mod_cast roughPart_pos hn
  have hs0 : (0 : ℝ) < smoothPart P n := by exact_mod_cast smoothPart_pos hP n
  have hlog := log_mode_norm_le_prod hP hj hc (n := n) (n₀ := n₀)
  have hK1 : (1 : ℝ) ≤ twistBound P n₀ := by exact_mod_cast twistBound_pos hP n₀
  have hlogK : 0 ≤ Real.log (twistBound P n₀) := Real.log_nonneg hK1
  have hlogn : 0 ≤ Real.log n := Real.log_natCast_nonneg n
  have hN1 : (1 : ℝ) ≤ (vecNum b : ℝ) * vecDen b := by
    have h1 : (1 : ℝ) ≤ vecNum b := by exact_mod_cast vecNum_pos hP b
    have h2 : (1 : ℝ) ≤ vecDen b := by exact_mod_cast vecDen_pos hP b
    nlinarith
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast roughPart_pos hn
  have hsplitN : (((vecNum b * r : ℕ) : ℝ) * vecDen b) = ((vecNum b : ℝ) * vecDen b) * r := by
    push_cast; ring
  have hw' := inv_sqrt_mode_le hP (n₀ := n₀) hn hj hc
  have hlog' : Real.log (((vecNum b * r : ℕ) : ℝ) * vecDen b) ≤
      Real.log n + Real.log (twistBound P n₀) := by
    rw [hsplitN, Real.log_mul (by positivity) hr0.ne', log_eq_smooth_add_rough hP hn]
    unfold smoothPart at hs0 ⊢
    linarith
  have hlogN : 0 ≤ Real.log (((vecNum b * r : ℕ) : ℝ) * vecDen b) := by
    rw [hsplitN]
    exact Real.log_nonneg (by nlinarith)
  calc (Real.sqrt (((vecNum b * r : ℕ) : ℝ) * vecDen b))⁻¹ *
        (2 * L * (C + 2 * Real.log (((vecNum b * r : ℕ) : ℝ) * vecDen b)))
      ≤ (Real.sqrt (twistBound P n₀) * (Real.sqrt n)⁻¹) *
          (2 * L * (C + 2 * (Real.log n + Real.log (twistBound P n₀)))) := by
        apply mul_le_mul hw' _ (by positivity) (by positivity)
        gcongr
    _ ≤ 2 * L * Real.sqrt (twistBound P n₀) * (C + 2 * Real.log (twistBound P n₀) + 2) *
          ((1 + Real.log n) * (Real.sqrt n)⁻¹) := by
        have hfac : C + 2 * (Real.log n + Real.log (twistBound P n₀)) ≤
            (C + 2 * Real.log (twistBound P n₀) + 2) * (1 + Real.log n) := by nlinarith
        have hpos : 0 ≤ Real.sqrt (twistBound P n₀) * (Real.sqrt n)⁻¹ * (2 * L) := by
          positivity
        calc (Real.sqrt (twistBound P n₀) * (Real.sqrt n)⁻¹) *
              (2 * L * (C + 2 * (Real.log n + Real.log (twistBound P n₀))))
            = (Real.sqrt (twistBound P n₀) * (Real.sqrt n)⁻¹ * (2 * L)) *
                (C + 2 * (Real.log n + Real.log (twistBound P n₀))) := by ring
          _ ≤ (Real.sqrt (twistBound P n₀) * (Real.sqrt n)⁻¹ * (2 * L)) *
                ((C + 2 * Real.log (twistBound P n₀) + 2) * (1 + Real.log n)) :=
              mul_le_mul_of_nonneg_left hfac hpos
          _ = _ := by ring

/-! ## Power bookkeeping -/

theorem rpow_three_halves_add {L : ℝ} (hL : 0 < L) (a : ℝ) :
    L ^ (3 / 2 + a) = L * Real.sqrt L * L ^ a := by
  rw [Real.rpow_add hL, Real.sqrt_eq_rpow, show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num,
    Real.rpow_add hL, Real.rpow_one]

/-- For `1 ≤ n ≤ L`: `L^{3/2} ≤ L^{3/2+a} n^{−a}`. -/
theorem sqrt_mul_le_of_le {L a : ℝ} (hL : 0 < L) (ha : 0 ≤ a) {n : ℕ} (hn : n ≠ 0)
    (hnL : (n : ℝ) ≤ L) : L * Real.sqrt L ≤ L ^ (3 / 2 + a) * (n : ℝ) ^ (-a) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  rw [rpow_three_halves_add hL, Real.rpow_neg hn0.le]
  have h1 : (n : ℝ) ^ a ≤ L ^ a := Real.rpow_le_rpow hn0.le hnL ha
  have h2 : 0 < (n : ℝ) ^ a := Real.rpow_pos_of_pos hn0 a
  rw [mul_assoc, mul_assoc, ← div_eq_mul_inv]
  have h3 : 1 ≤ L ^ a / (n : ℝ) ^ a := by rw [le_div_iff₀ h2, one_mul]; exact h1
  have h4 : 0 ≤ L * Real.sqrt L := by positivity
  calc L * Real.sqrt L = L * (Real.sqrt L * 1) := by ring
    _ ≤ L * (Real.sqrt L * (L ^ a / (n : ℝ) ^ a)) := by gcongr

/-- For `L < n`: `L² n^{−1/2} ≤ L^{3/2+a} n^{−a}` when `a ≤ 1/2`. -/
theorem sq_mul_inv_sqrt_le_of_lt {L a : ℝ} (hL : 0 < L) (ha : a ≤ 1 / 2) {n : ℕ}
    (hnL : L < (n : ℝ)) : L ^ 2 * (Real.sqrt n)⁻¹ ≤ L ^ (3 / 2 + a) * (n : ℝ) ^ (-a) := by
  have hn0 : (0 : ℝ) < n := by linarith
  have e1 : L ^ 2 = L ^ (3 / 2 + a) * L ^ (1 / 2 - a) := by
    rw [← Real.rpow_add hL, show 3 / 2 + a + (1 / 2 - a) = ((2 : ℕ) : ℝ) by norm_num,
      Real.rpow_natCast]
  have e2 : (Real.sqrt n)⁻¹ = (n : ℝ) ^ (-a) * ((n : ℝ) ^ (1 / 2 - a))⁻¹ := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hn0.le, ← Real.rpow_neg hn0.le, ← Real.rpow_add hn0]
    ring_nf
  rw [e1, e2]
  have h1 : L ^ (1 / 2 - a) ≤ (n : ℝ) ^ (1 / 2 - a) := Real.rpow_le_rpow hL.le hnL.le (by linarith)
  have h2 : 0 < (n : ℝ) ^ (1 / 2 - a) := Real.rpow_pos_of_pos hn0 _
  have h3 : L ^ (1 / 2 - a) * ((n : ℝ) ^ (1 / 2 - a))⁻¹ ≤ 1 := by
    rw [← div_eq_mul_inv, div_le_one h2]; exact h1
  have h4 : 0 ≤ L ^ (3 / 2 + a) * (n : ℝ) ^ (-a) := by positivity
  calc L ^ (3 / 2 + a) * L ^ (1 / 2 - a) * ((n : ℝ) ^ (-a) * ((n : ℝ) ^ (1 / 2 - a))⁻¹)
      = (L ^ (3 / 2 + a) * (n : ℝ) ^ (-a)) * (L ^ (1 / 2 - a) * ((n : ℝ) ^ (1 / 2 - a))⁻¹) := by
        ring
    _ ≤ (L ^ (3 / 2 + a) * (n : ℝ) ^ (-a)) * 1 := mul_le_mul_of_nonneg_left h3 h4
    _ = L ^ (3 / 2 + a) * (n : ℝ) ^ (-a) := mul_one _

/-- `(1 + log n) n^{−1/2} ≤ (1 + 1/η) n^{−a}` with `η = 1/2 − a`. -/
theorem one_add_log_mul_inv_sqrt_le {a : ℝ} (ha : a < 1 / 2) {n : ℕ} (hn : n ≠ 0) :
    (1 + Real.log n) * (Real.sqrt n)⁻¹ ≤ (1 + (1 / 2 - a)⁻¹) * (n : ℝ) ^ (-a) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
  set η : ℝ := 1 / 2 - a with hη
  have hη0 : 0 < η := by rw [hη]; linarith
  have hlog : Real.log n ≤ (n : ℝ) ^ η / η := Real.log_le_rpow_div hn0.le hη0
  have hnη : 1 ≤ (n : ℝ) ^ η := Real.one_le_rpow hn1 hη0.le
  have e2 : (Real.sqrt n)⁻¹ = (n : ℝ) ^ (-a) * ((n : ℝ) ^ η)⁻¹ := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hn0.le, ← Real.rpow_neg hn0.le, ← Real.rpow_add hn0, hη]
    ring_nf
  rw [e2]
  have hpos : 0 < (n : ℝ) ^ η := by linarith
  have h1 : (1 + Real.log n) * ((n : ℝ) ^ η)⁻¹ ≤ 1 + η⁻¹ := by
    rw [← div_eq_mul_inv, div_le_iff₀ hpos]
    have : Real.log n ≤ η⁻¹ * (n : ℝ) ^ η := by rw [inv_mul_eq_div]; exact hlog
    nlinarith [inv_pos.mpr hη0]
  have h2 : 0 ≤ (n : ℝ) ^ (-a) := by positivity
  calc (1 + Real.log n) * ((n : ℝ) ^ (-a) * ((n : ℝ) ^ η)⁻¹)
      = (n : ℝ) ^ (-a) * ((1 + Real.log n) * ((n : ℝ) ^ η)⁻¹) := by ring
    _ ≤ (n : ℝ) ^ (-a) * (1 + η⁻¹) := mul_le_mul_of_nonneg_left h1 h2
    _ = (1 + η⁻¹) * (n : ℝ) ^ (-a) := by ring

/-- A mode twist `h/k` of `n` has `n ≤ K₀ h k`. -/
theorem natCast_le_twistBound_mul_mode (hP : ∀ p ∈ P, p.Prime) {n n₀ : ℕ} (hn : n ≠ 0) {j : ℤ}
    (hj : j ∈ bohrModes) {c : P → ℤ} (hc : c ∈ Fintype.piFinset (fun _ : P => bohrModes)) :
    (n : ℝ) ≤ (twistBound P n₀ : ℝ) *
      (((vecNum (vecOf P n - (j • vecOf P n₀ + c)) * roughPart P n : ℕ) : ℝ) *
        vecDen (vecOf P n - (j • vecOf P n₀ + c))) := by
  set N : ℝ := ((vecNum (vecOf P n - (j • vecOf P n₀ + c)) * roughPart P n : ℕ) : ℝ) *
    vecDen (vecOf P n - (j • vecOf P n₀ + c)) with hN
  set K₀ : ℝ := (twistBound P n₀ : ℝ) with hK₀
  have hK1 : 1 ≤ K₀ := by rw [hK₀]; exact_mod_cast twistBound_pos hP n₀
  have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hN0 : 0 < N := by
    have h1 : (0 : ℝ) < ((vecNum (vecOf P n - (j • vecOf P n₀ + c)) * roughPart P n : ℕ) : ℝ) := by
      exact_mod_cast Nat.mul_pos (vecNum_pos hP _) (roughPart_pos hn)
    have h2 : (0 : ℝ) < vecDen (vecOf P n - (j • vecOf P n₀ + c)) := by
      exact_mod_cast vecDen_pos hP _
    positivity
  have hw : (Real.sqrt N)⁻¹ ≤ Real.sqrt K₀ * (Real.sqrt n)⁻¹ := inv_sqrt_mode_le hP hn hj hc
  have hsq : 0 < Real.sqrt N := Real.sqrt_pos.mpr hN0
  rw [inv_le_comm₀ hsq (by positivity), mul_inv, inv_inv] at hw
  have hsq2 : Real.sqrt n ≤ Real.sqrt K₀ * Real.sqrt N := by
    have := mul_le_mul_of_nonneg_left hw (Real.sqrt_nonneg K₀)
    rwa [← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul] at this
  rw [← Real.sqrt_mul (by linarith)] at hsq2
  exact (Real.sqrt_le_sqrt_iff (by positivity)).mp hsq2

/-- For a mode twist `h/k` of `n`: `√(2k/h) ≤ 2K₀² n^{−1/2}`. -/
theorem sqrt_two_mul_div_mode_le (hP : ∀ p ∈ P, p.Prime) {n n₀ : ℕ} (hn : n ≠ 0) {j : ℤ}
    (hj : j ∈ bohrModes) {c : P → ℤ} (hc : c ∈ Fintype.piFinset (fun _ : P => bohrModes)) :
    Real.sqrt (2 * (vecDen (vecOf P n - (j • vecOf P n₀ + c)) : ℝ) /
        ((vecNum (vecOf P n - (j • vecOf P n₀ + c)) * roughPart P n : ℕ) : ℝ)) ≤
      2 * (twistBound P n₀ : ℝ) ^ 2 * (Real.sqrt n)⁻¹ := by
  set h : ℕ := vecNum (vecOf P n - (j • vecOf P n₀ + c)) * roughPart P n with hh
  set k : ℕ := vecDen (vecOf P n - (j • vecOf P n₀ + c)) with hk
  set K₀ : ℝ := (twistBound P n₀ : ℝ) with hK₀
  have hK1 : 1 ≤ K₀ := by rw [hK₀]; exact_mod_cast twistBound_pos hP n₀
  have hkK : (k : ℝ) ≤ K₀ := by
    have := vecDen_mode_le hP hj hc (n := n) (n₀ := n₀)
    show ((vecDen (vecOf P n - (j • vecOf P n₀ + c)) : ℕ) : ℝ) ≤ (twistBound P n₀ : ℝ)
    exact_mod_cast this
  have hh0 : (0 : ℝ) < h := by exact_mod_cast Nat.mul_pos (vecNum_pos hP _) (roughPart_pos hn)
  have hk0 : (0 : ℝ) < k := by exact_mod_cast vecDen_pos hP _
  have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hhk : (n : ℝ) ≤ K₀ * ((h : ℝ) * k) := natCast_le_twistBound_mul_mode hP hn hj hc
  have hkh : 2 * (k : ℝ) / h ≤ 2 * K₀ ^ 3 / n := by
    rw [div_le_div_iff₀ hh0 hn0]
    have hk2 : (k : ℝ) * k ≤ K₀ * K₀ := by nlinarith
    nlinarith
  calc Real.sqrt (2 * k / h) ≤ Real.sqrt (2 * K₀ ^ 3 / n) := Real.sqrt_le_sqrt hkh
    _ = Real.sqrt (2 * K₀ ^ 3) * (Real.sqrt n)⁻¹ := by
        rw [Real.sqrt_div' _ hn0.le, div_eq_mul_inv]
    _ ≤ 2 * K₀ ^ 2 * (Real.sqrt n)⁻¹ := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        rw [Real.sqrt_le_left (by positivity)]
        nlinarith [pow_le_pow_right₀ hK1 (by norm_num : 3 ≤ 4)]

/-- **The near-resonant mass of a mode twist decays like `n^{−a}`**:
`L · nearMass ≤ (24K₀ + 32K₀³) δ L^{3/2+a} n^{−a}` for `0 ≤ a ≤ 1/2`. -/
theorem mul_nearMass_mode_le (hP : ∀ p ∈ P, p.Prime) {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ)
    (hδ4 : δ ≤ 1 / 4) {n n₀ : ℕ} (hn : n ≠ 0) {j : ℤ} (hj : j ∈ bohrModes) {c : P → ℤ}
    (hc : c ∈ Fintype.piFinset (fun _ : P => bohrModes)) {a : ℝ} (ha0 : 0 ≤ a) (ha : a ≤ 1 / 2) :
    L * nearMass L (vecNum (vecOf P n - (j • vecOf P n₀ + c)) * roughPart P n)
        (vecDen (vecOf P n - (j • vecOf P n₀ + c))) δ ≤
      (24 * (twistBound P n₀ : ℝ) + 32 * (twistBound P n₀ : ℝ) ^ 3) * δ *
        (L ^ (3 / 2 + a) * (n : ℝ) ^ (-a)) := by
  set b := vecOf P n - (j • vecOf P n₀ + c) with hb
  set h : ℕ := vecNum b * roughPart P n with hh
  set k : ℕ := vecDen b with hk
  set K₀ : ℝ := (twistBound P n₀ : ℝ) with hK₀
  have hh1 : 1 ≤ h := Nat.mul_pos (vecNum_pos hP b) (roughPart_pos hn)
  have hk1 : 1 ≤ k := vecDen_pos hP b
  have hkK : (k : ℝ) ≤ K₀ := by
    have := vecDen_mode_le hP hj hc (n := n) (n₀ := n₀)
    show ((vecDen b : ℕ) : ℝ) ≤ (twistBound P n₀ : ℝ)
    exact_mod_cast this
  have hK1 : 1 ≤ K₀ := by rw [hK₀]; exact_mod_cast twistBound_pos hP n₀
  have hnm0 : 0 ≤ nearMass L h k δ := nearMass_nonneg hL.le h k δ
  have hpow0 : 0 ≤ L ^ (3 / 2 + a) * (n : ℝ) ^ (-a) := by positivity
  rcases le_or_gt (n : ℝ) L with hnL | hnL
  · have hm : nearMass L h k δ ≤ 24 * δ * k * Real.sqrt L := tsum_nearRes_le hh1 hk1 hδ hδ4 hL
    have h2 := sqrt_mul_le_of_le hL ha0 hn hnL
    calc L * nearMass L h k δ ≤ L * (24 * δ * k * Real.sqrt L) :=
          mul_le_mul_of_nonneg_left hm hL.le
      _ = 24 * δ * k * (L * Real.sqrt L) := by ring
      _ ≤ 24 * δ * K₀ * (L ^ (3 / 2 + a) * (n : ℝ) ^ (-a)) := by
          gcongr
      _ ≤ (24 * K₀ + 32 * K₀ ^ 3) * δ * (L ^ (3 / 2 + a) * (n : ℝ) ^ (-a)) := by
          have : 0 ≤ 32 * K₀ ^ 3 * δ * (L ^ (3 / 2 + a) * (n : ℝ) ^ (-a)) := by positivity
          nlinarith
  · have hm : nearMass L h k δ ≤ 16 * δ * k * L * Real.sqrt (2 * k / h) :=
      tsum_nearRes_le' hh1 hk1 hδ hδ4 hL
    have hsq : Real.sqrt (2 * k / h) ≤ 2 * K₀ ^ 2 * (Real.sqrt n)⁻¹ :=
      sqrt_two_mul_div_mode_le hP hn hj hc
    have h2 := sq_mul_inv_sqrt_le_of_lt hL ha hnL
    calc L * nearMass L h k δ ≤ L * (16 * δ * k * L * (2 * K₀ ^ 2 * (Real.sqrt n)⁻¹)) := by
          refine mul_le_mul_of_nonneg_left (hm.trans ?_) hL.le
          exact mul_le_mul_of_nonneg_left hsq (by positivity)
      _ = 32 * k * K₀ ^ 2 * δ * (L ^ 2 * (Real.sqrt n)⁻¹) := by ring
      _ ≤ 32 * K₀ * K₀ ^ 2 * δ * (L ^ (3 / 2 + a) * (n : ℝ) ^ (-a)) := by
          gcongr
      _ ≤ (24 * K₀ + 32 * K₀ ^ 3) * δ * (L ^ (3 / 2 + a) * (n : ℝ) ^ (-a)) := by
          have : 0 ≤ 24 * K₀ * δ * (L ^ (3 / 2 + a) * (n : ℝ) ^ (-a)) := by positivity
          nlinarith

/-- The envelope of a mode twist, with the decay `n^{−a}`. -/
theorem nearEnvelope_mode_le (hP : ∀ p ∈ P, p.Prime) {C L δ : ℝ} (hC : 0 ≤ C) (hL : 0 < L)
    (hδ : 0 < δ) (hδ4 : δ ≤ 1 / 4) (K : ℕ) {n n₀ : ℕ} (hn : n ≠ 0) {j : ℤ} (hj : j ∈ bohrModes)
    {c : P → ℤ} (hc : c ∈ Fintype.piFinset (fun _ : P => bohrModes)) {a : ℝ} (ha0 : 0 < a)
    (ha : a < 1 / 2) :
    nearEnvelope C L δ K (vecNum (vecOf P n - (j • vecOf P n₀ + c)) * roughPart P n)
        (vecDen (vecOf P n - (j • vecOf P n₀ + c))) ≤
      (2 * Real.sqrt (twistBound P n₀) * (C + 2 * Real.log (twistBound P n₀) + 2) *
          (1 + (1 / 2 - a)⁻¹) +
        C * (24 * (twistBound P n₀ : ℝ) + 32 * (twistBound P n₀ : ℝ) ^ 3) + C) *
        ((L + δ * L ^ (3 / 2 + a)) * (n : ℝ) ^ (-a) + L ^ 2 / (L * δ) ^ K +
          L ^ 2 * Real.exp (-(L ^ 2) / 32)) := by
  set K₀ : ℝ := (twistBound P n₀ : ℝ) with hK₀
  have hK1 : 1 ≤ K₀ := by rw [hK₀]; exact_mod_cast twistBound_pos hP n₀
  have hlogK : 0 ≤ Real.log K₀ := Real.log_nonneg hK1
  set D₁ : ℝ := 2 * Real.sqrt K₀ * (C + 2 * Real.log K₀ + 2) * (1 + (1 / 2 - a)⁻¹) with hD₁
  set D₂ : ℝ := 24 * K₀ + 32 * K₀ ^ 3 with hD₂
  have hη : 0 < (1 / 2 - a)⁻¹ := inv_pos.mpr (by linarith)
  have hD₁0 : 0 ≤ D₁ := by rw [hD₁]; positivity
  have hD₂0 : 0 ≤ D₂ := by rw [hD₂]; positivity
  have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hna : 0 ≤ (n : ℝ) ^ (-a) := by positivity
  have hdiag := diag_mode_le hP hC hL hn hj hc (n₀ := n₀)
  have hlog := one_add_log_mul_inv_sqrt_le ha hn
  have hdiag' : (Real.sqrt (((vecNum (vecOf P n - (j • vecOf P n₀ + c)) * roughPart P n : ℕ) : ℝ) *
        vecDen (vecOf P n - (j • vecOf P n₀ + c))))⁻¹ *
      (2 * L * (C + 2 * Real.log (((vecNum (vecOf P n - (j • vecOf P n₀ + c)) * roughPart P n :
        ℕ) : ℝ) * vecDen (vecOf P n - (j • vecOf P n₀ + c))))) ≤ D₁ * (L * (n : ℝ) ^ (-a)) := by
    refine hdiag.trans ?_
    rw [hD₁]
    have h0 : 0 ≤ 2 * L * Real.sqrt K₀ * (C + 2 * Real.log K₀ + 2) := by positivity
    calc 2 * L * Real.sqrt K₀ * (C + 2 * Real.log K₀ + 2) * ((1 + Real.log n) * (Real.sqrt n)⁻¹)
        ≤ 2 * L * Real.sqrt K₀ * (C + 2 * Real.log K₀ + 2) *
            ((1 + (1 / 2 - a)⁻¹) * (n : ℝ) ^ (-a)) := mul_le_mul_of_nonneg_left hlog h0
      _ = _ := by ring
  have hnear := mul_nearMass_mode_le hP hL hδ hδ4 hn hj hc (n₀ := n₀) ha0.le ha.le
  have hT0 : 0 ≤ L ^ 2 / (L * δ) ^ K + L ^ 2 * Real.exp (-(L ^ 2) / 32) := by positivity
  have hX0 : 0 ≤ L * (n : ℝ) ^ (-a) := by positivity
  have hY0 : 0 ≤ δ * (L ^ (3 / 2 + a) * (n : ℝ) ^ (-a)) := by positivity
  unfold nearEnvelope
  calc _ + C * (L * nearMass L _ _ δ + L ^ 2 / (L * δ) ^ K + L ^ 2 * Real.exp (-(L ^ 2) / 32))
      ≤ D₁ * (L * (n : ℝ) ^ (-a)) + C * (D₂ * δ * (L ^ (3 / 2 + a) * (n : ℝ) ^ (-a)) +
          (L ^ 2 / (L * δ) ^ K + L ^ 2 * Real.exp (-(L ^ 2) / 32))) := by
        have := mul_le_mul_of_nonneg_left hnear hC
        nlinarith
    _ ≤ (D₁ + C * D₂ + C) * ((L + δ * L ^ (3 / 2 + a)) * (n : ℝ) ^ (-a) + L ^ 2 / (L * δ) ^ K +
          L ^ 2 * Real.exp (-(L ^ 2) / 32)) := by
        have e : (L + δ * L ^ (3 / 2 + a)) * (n : ℝ) ^ (-a) =
            L * (n : ℝ) ^ (-a) + δ * (L ^ (3 / 2 + a) * (n : ℝ) ^ (-a)) := by ring
        rw [e]
        have hCD : 0 ≤ C * D₂ := mul_nonneg hC hD₂0
        nlinarith [mul_nonneg hCD hX0, mul_nonneg hD₁0 hY0, mul_nonneg hD₁0 hT0,
          mul_nonneg hCD hT0, mul_nonneg hC hX0, mul_nonneg hC hY0]

/-- **The notch main term with a decaying envelope.** For fixed `P`, `ε`, `n₀` and `0 < a < 1/2`,
uniformly in `L ≥ 16`, `0 < δ ≤ 1/4` and `n ≠ 0`:

`‖M_L(log n) − mainWeight(n) e_P ∫ ω log t‖ ≤ D ((L + δ L^{3/2+a}) n^{−a} + L²/(Lδ)^K
  + L² e^{−L²/32})`. -/
theorem exists_norm_weightedMoment_sub_mainWeight_le_decay (hP : ∀ p ∈ P, p.Prime) (K : ℕ)
    (ε : ℝ) {n₀ : ℕ} (hn₀ : IsSmoothOver P n₀) {a : ℝ} (ha0 : 0 < a) (ha : a < 1 / 2) :
    ∃ D, 0 ≤ D ∧ ∀ {L δ : ℝ}, 16 ≤ L → 0 < δ → δ ≤ 1 / 4 → ∀ {n : ℕ}, n ≠ 0 →
      ‖ZetaNotch.weightedMoment L (notchWeight P ε n₀) (Real.log n) -
          ((mainWeight P ε n₀ n * ∏ p : P, (1 - primeHalf p ^ 2) : ℝ) : ℂ) * logWindow L‖ ≤
        D * ((L + δ * L ^ (3 / 2 + a)) * (n : ℝ) ^ (-a) + L ^ 2 / (L * δ) ^ K +
          L ^ 2 * Real.exp (-(L ^ 2) / 32)) := by
  classical
  obtain ⟨C, hC, hmain⟩ := exists_norm_weightedMoment_sub_main_le_near hP K
  set B : ℝ := ∑ j ∈ bohrModes, ∑ c ∈ Fintype.piFinset (fun _ : P => bohrModes),
    |modeCoeff ε j c| with hB
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun c _ => abs_nonneg _
  set E : ℝ := 2 * Real.sqrt (twistBound P n₀) * (C + 2 * Real.log (twistBound P n₀) + 2) *
      (1 + (1 / 2 - a)⁻¹) +
    C * (24 * (twistBound P n₀ : ℝ) + 32 * (twistBound P n₀ : ℝ) ^ 3) + C with hE
  have hK1 : (1 : ℝ) ≤ twistBound P n₀ := by exact_mod_cast twistBound_pos hP n₀
  have hE0 : 0 ≤ E := by
    have := Real.log_nonneg hK1
    have : 0 < (1 / 2 - a)⁻¹ := inv_pos.mpr (by linarith)
    rw [hE]; positivity
  refine ⟨B * E, mul_nonneg hB0 hE0, fun {L δ} hL hδ hδ4 {n} hn => ?_⟩
  have hL0 : 0 < L := by linarith
  refine (hmain hL hδ ε hn hn₀).trans ?_
  rw [hB, Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_le_sum fun j hj => ?_
  rw [Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_le_sum fun c hc => ?_
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left (nearEnvelope_mode_le hP hC hL0 hδ hδ4 K hn hj hc ha0 ha)
    (abs_nonneg _)

end RHTower.WeilAbscissa
