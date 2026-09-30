import GaloisForLFunctions.RHTower.ZetaNotchTwistedDiagonal
import GaloisForLFunctions.RHTower.ZetaNotchResonanceCount
import GaloisForLFunctions.RHTower.ZetaNotchDualJets
import GaloisForLFunctions.RHTower.ZetaGateProductAFEBlockBound

/-!
# The off-diagonal of the windowed twisted moment

For coprime `h, k ≥ 1`, a resonance scale `0 < δ ≤ 1/4` and `K ∈ ℕ`, every off-diagonal pair is
either near-resonant (`nearRes`) or has frequency at least `δ` away from the twist. Near-resonant
pairs are bounded trivially by the window mass, the others by `K` integrations by parts:

* direct (`norm_directOff_le`): `‖ω̂(η)‖ ≤ 2L` and `‖ω̂(η)‖ ≤ 2L c_K/(Lδ)^K`;
* dual (`norm_dualOff_le`): `‖J(Y, η)‖ ≤ 2L C min(1, L²/Y)` and the `K`-fold dual-line bound.

With the pair weight `(MN)^{−1/2} min(1, L/(MN))` and its near-resonant mass `𝒩(h,k,δ)`
(`tsum_nearRes_le`), the twisted moment is its diagonal up to (`exists_norm_twistedMoment_sub_diag_le`)

`C (L 𝒩(h,k,δ) + L²/(Lδ)^K + L² e^{−L²/32})`.
-/

noncomputable section

namespace RHTower.ZetaNotch

open Complex MeasureTheory Set Filter Topology RHTower GaloisForLFunctions.HTGeometry

/-! ## Pair weights -/

theorem pairWeight_eq (L : ℝ) (P : ℕ × ℕ) :
    pairWeight L P = pairAmp P * min 1 (L / pairProd P) := by
  rw [pairAmp_eq]
  rfl

/-- `V(y) ≤ C min(1, 1/y)`. -/
theorem exists_norm_smoothAFECutoff_le_min :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {y : ℝ}, 0 < y → ‖smoothAFECutoff y‖ ≤ C * min 1 (1 / y) := by
  obtain ⟨K₁, hK₁, h₁⟩ := exists_norm_smoothAFECutoff_le_neg_rpow (A := 1) one_pos
  obtain ⟨K₂, hK₂, h₂⟩ := exists_norm_smoothAFECutoff_sub_one_le_rpow (δ := 1 / 4) (by norm_num)
  refine ⟨1 + K₁ + K₂, by positivity, fun {y} hy => ?_⟩
  rcases le_or_gt y 1 with hy1 | hy1
  · rw [min_eq_left (by rw [le_div_iff₀ hy]; linarith)]
    have hr : y ^ (1 / 4 : ℝ) ≤ 1 := Real.rpow_le_one hy.le hy1 (by norm_num)
    have := h₂ hy
    calc ‖smoothAFECutoff y‖ ≤ ‖smoothAFECutoff y - 1‖ + ‖(1 : ℂ)‖ := norm_le_norm_sub_add _ _
      _ ≤ K₂ * 1 + 1 := by
          rw [norm_one]
          gcongr
          exact this.trans (mul_le_mul_of_nonneg_left hr hK₂)
      _ ≤ (1 + K₁ + K₂) * 1 := by linarith
  · rw [min_eq_right (by rw [div_le_one hy]; exact hy1.le)]
    have := h₁ hy
    rw [Real.rpow_neg_one, ← one_div] at this
    calc ‖smoothAFECutoff y‖ ≤ K₁ * (1 / y) := this
      _ ≤ (1 + K₁ + K₂) * (1 / y) := by gcongr; linarith

theorem pairWeight_le_rpow {L : ℝ} (hL : 0 ≤ L) (P : ℕ × ℕ) :
    pairWeight L P ≤ L ^ (3 / 4 : ℝ) * pairProd P ^ (-(5 / 4 : ℝ)) := by
  rw [pairWeight_eq]
  have hP := pairProd_pos P
  have hx : 0 ≤ L / pairProd P := by positivity
  have hmin : min 1 (L / pairProd P) ≤ (L / pairProd P) ^ (3 / 4 : ℝ) := by
    rcases le_or_gt (L / pairProd P) 1 with h1 | h1
    · rw [min_eq_right h1]
      calc L / pairProd P = (L / pairProd P) ^ (1 : ℝ) := (Real.rpow_one _).symm
        _ ≤ (L / pairProd P) ^ (3 / 4 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_ge' hx h1 (by norm_num) (by norm_num)
    · rw [min_eq_left h1.le]
      exact Real.one_le_rpow h1.le (by norm_num)
  calc pairAmp P * min 1 (L / pairProd P) ≤ pairAmp P * (L / pairProd P) ^ (3 / 4 : ℝ) :=
        mul_le_mul_of_nonneg_left hmin (pairAmp_pos P).le
    _ = L ^ (3 / 4 : ℝ) * (pairAmp P * pairProd P ^ (-(3 / 4 : ℝ))) := by
        rw [Real.div_rpow hL hP.le, Real.rpow_neg hP.le]
        ring
    _ = L ^ (3 / 4 : ℝ) * pairProd P ^ (-(5 / 4 : ℝ)) := by
        rw [pairAmp_mul_rpow]
        norm_num

theorem summable_pairWeight {L : ℝ} (hL : 0 ≤ L) : Summable (pairWeight L) :=
  Summable.of_nonneg_of_le (pairWeight_nonneg hL) (pairWeight_le_rpow hL)
    ((summable_pairProd_rpow (s := 5 / 4) (by norm_num)).mul_left _)

/-- The zeta constant `Σ_{m,n} (mn)^{−5/4}`. -/
def pairZeta : ℝ := ∑' P : ℕ × ℕ, pairProd P ^ (-(5 / 4 : ℝ))

theorem pairZeta_nonneg : 0 ≤ pairZeta :=
  tsum_nonneg fun P => Real.rpow_nonneg (pairProd_pos P).le _

/-- **Total pair weight**: `Σ_{m,n} (mn)^{−1/2} min(1, L/(mn)) ≤ ζ₂(5/4) L^{3/4}`. -/
theorem tsum_pairWeight_le {L : ℝ} (hL : 0 ≤ L) :
    ∑' P, pairWeight L P ≤ pairZeta * L ^ (3 / 4 : ℝ) := by
  rw [pairZeta, mul_comm, ← tsum_mul_left]
  exact (summable_pairWeight hL).tsum_le_tsum (pairWeight_le_rpow hL)
    ((summable_pairProd_rpow (s := 5 / 4) (by norm_num)).mul_left _)

/-! ## Near-resonance versus separation -/

/-- The near-resonant mass `𝒩_L(h,k,δ) = Σ_{near} (MN)^{−1/2} min(1, L/(MN))`. -/
def nearMass (L : ℝ) (h k : ℕ) (δ : ℝ) : ℝ :=
  ∑' P : ℕ × ℕ, if nearRes h k δ P then pairWeight L P else 0

theorem nearMass_nonneg {L : ℝ} (hL : 0 ≤ L) (h k : ℕ) (δ : ℝ) : 0 ≤ nearMass L h k δ :=
  tsum_nonneg fun P => by
    split_ifs
    · exact pairWeight_nonneg hL P
    · exact le_refl _

/-- An off-diagonal pair is near-resonant, or its frequency is `δ`-separated from the twist. -/
theorem nearRes_or_le {h k : ℕ} (hh : 0 < h) (hk : 0 < k) {δ : ℝ} {P : ℕ × ℕ}
    (hP : (P.2 + 1) * k ≠ (P.1 + 1) * h) :
    nearRes h k δ P ∨ δ ≤ |pairFreq P - (Real.log h - Real.log k)| := by
  by_cases hn : nearRes h k δ P
  · exact Or.inl hn
  · right
    have hh0 : (0 : ℝ) < h := by exact_mod_cast hh
    have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
    have hlt : ¬ |Real.log (((P.2 : ℝ) + 1) / ((P.1 : ℝ) + 1)) - Real.log ((h : ℝ) / k)| < δ :=
      fun hlt => hn ⟨hP, hlt⟩
    push Not at hlt
    rwa [Real.log_div (by positivity) (by positivity), Real.log_div hh0.ne' hk0.ne'] at hlt

/-! ## The direct off-diagonal -/

/-- **Direct off-diagonal bound.** -/
theorem exists_norm_directOff_le (K : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {L δ : ℝ}, 0 < L → 0 < δ → ∀ {h k : ℕ}, 0 < h → 0 < k →
      ‖directOff L h k‖ ≤
        C * (L * nearMass L h k δ + L / (L * δ) ^ K * ∑' P, pairWeight L P) := by
  obtain ⟨CV, hCV, hV⟩ := exists_norm_smoothAFECutoff_le_min
  set A : ℝ := blockWindowConst K * 2 ^ K with hA
  have hA0 : 0 ≤ A := mul_nonneg (blockWindowConst_nonneg K) (by positivity)
  refine ⟨2 * CV * (1 + A), by positivity, fun {L δ} hL hδ {h k} hh hk => ?_⟩
  set ξ : ℝ := Real.log h - Real.log k with hξ
  set f : ℕ × ℕ → ℂ := fun P => (pairAmp P : ℂ) * smoothAFECutoff (pairProd P / L) *
    windowHat L (ξ - pairFreq P) with hf
  set S : Set (ℕ × ℕ) := {P : ℕ × ℕ | (P.1 + 1) * h = (P.2 + 1) * k}ᶜ with hS
  set b : ℕ × ℕ → ℝ := fun P => CV * (2 * L * (if nearRes h k δ P then pairWeight L P else 0) +
    2 * L * A / (L * δ) ^ K * pairWeight L P) with hb
  have hLδ : 0 < L * δ := mul_pos hL hδ
  have hb0 : ∀ P, 0 ≤ b P := fun P => by
    simp only [hb]
    apply mul_nonneg hCV
    apply add_nonneg
    · apply mul_nonneg (by positivity)
      split_ifs
      · exact pairWeight_nonneg hL.le P
      · exact le_refl _
    · exact mul_nonneg (by positivity) (pairWeight_nonneg hL.le P)
  have hbs : Summable b := by
    have h1 : Summable (fun P : ℕ × ℕ => if nearRes h k δ P then pairWeight L P else 0) := by
      refine Summable.of_nonneg_of_le (fun P => ?_) (fun P => ?_) (summable_pairWeight hL.le)
      · split_ifs
        · exact pairWeight_nonneg hL.le P
        · exact le_refl _
      · split_ifs
        · exact le_refl _
        · exact pairWeight_nonneg hL.le P
    exact ((h1.mul_left (2 * L)).add ((summable_pairWeight hL.le).mul_left _)).mul_left CV
  -- the pointwise bound off the diagonal
  have hpt : ∀ P ∈ S, ‖f P‖ ≤ b P := by
    intro P hP
    have hP' : (P.2 + 1) * k ≠ (P.1 + 1) * h := fun he => hP he.symm
    have hVb : pairAmp P * ‖smoothAFECutoff (pairProd P / L)‖ ≤ CV * pairWeight L P := by
      rw [pairWeight_eq]
      have := hV (div_pos (pairProd_pos P) hL)
      rw [one_div_div] at this
      calc pairAmp P * ‖smoothAFECutoff (pairProd P / L)‖
          ≤ pairAmp P * (CV * min 1 (L / pairProd P)) :=
            mul_le_mul_of_nonneg_left this (pairAmp_pos P).le
        _ = CV * (pairAmp P * min 1 (L / pairProd P)) := by ring
    have hfn : ‖f P‖ = pairAmp P * ‖smoothAFECutoff (pairProd P / L)‖ *
        ‖windowHat L (ξ - pairFreq P)‖ := by
      simp only [hf, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (pairAmp_pos P)]
    rw [hfn]
    have hw0 := pairWeight_nonneg hL.le P
    rcases nearRes_or_le hh hk hP' (δ := δ) with hn | hsep
    · have hw := norm_windowHat_le hL (ξ - pairFreq P)
      calc pairAmp P * ‖smoothAFECutoff (pairProd P / L)‖ * ‖windowHat L (ξ - pairFreq P)‖
          ≤ CV * pairWeight L P * (2 * L) :=
            mul_le_mul hVb hw (norm_nonneg _) (by positivity)
        _ ≤ b P := by
            simp only [hb, if_pos hn]
            have : 0 ≤ CV * (2 * L * A / (L * δ) ^ K * pairWeight L P) := by positivity
            nlinarith
    · have hη : δ ≤ |ξ - pairFreq P| := by rw [abs_sub_comm]; exact hsep
      have hη0 : ξ - pairFreq P ≠ 0 := fun h0 => by
        rw [h0, abs_zero] at hη; linarith
      have hw := norm_windowHat_le_pow K hL hη0
      have hw' : ‖windowHat L (ξ - pairFreq P)‖ ≤ 2 * L * A / (L * δ) ^ K := by
        refine hw.trans ?_
        rw [← hA]
        apply div_le_div_of_nonneg_left (by positivity) (by positivity)
        exact pow_le_pow_left₀ hLδ.le (mul_le_mul_of_nonneg_left hη hL.le) K
      calc pairAmp P * ‖smoothAFECutoff (pairProd P / L)‖ * ‖windowHat L (ξ - pairFreq P)‖
          ≤ CV * pairWeight L P * (2 * L * A / (L * δ) ^ K) :=
            mul_le_mul hVb hw' (norm_nonneg _) (by positivity)
        _ ≤ b P := by
            simp only [hb]
            have : 0 ≤ CV * (2 * L * (if nearRes h k δ P then pairWeight L P else 0)) := by
              apply mul_nonneg hCV
              apply mul_nonneg (by positivity)
              split_ifs
              · exact hw0
              · exact le_refl _
            nlinarith
  have hfs : Summable (fun P : S => ‖f P‖) := (summable_directFamily hL ξ).norm.subtype S
  calc ‖directOff L h k‖ ≤ ∑' P : S, ‖f P‖ := norm_tsum_le_tsum_norm hfs
    _ ≤ ∑' P : S, b P := hfs.tsum_le_tsum (fun P => hpt P.1 P.2) (hbs.subtype S)
    _ ≤ ∑' P, b P := Summable.tsum_subtype_le b S hb0 hbs
    _ = CV * (2 * L * nearMass L h k δ + 2 * L * A / (L * δ) ^ K * ∑' P, pairWeight L P) := by
        simp only [hb]
        rw [tsum_mul_left, Summable.tsum_add, tsum_mul_left, tsum_mul_left]
        · rfl
        · refine Summable.mul_left _ (Summable.of_nonneg_of_le (fun P => ?_) (fun P => ?_)
            (summable_pairWeight hL.le))
          · split_ifs
            · exact pairWeight_nonneg hL.le P
            · exact le_refl _
          · split_ifs
            · exact le_refl _
            · exact pairWeight_nonneg hL.le P
        · exact (summable_pairWeight hL.le).mul_left _
    _ ≤ 2 * CV * (1 + A) * (L * nearMass L h k δ + L / (L * δ) ^ K * ∑' P, pairWeight L P) := by
        have hN := nearMass_nonneg hL.le h k δ
        have hW : 0 ≤ ∑' P, pairWeight L P := tsum_nonneg (pairWeight_nonneg hL.le)
        have hq : 0 ≤ L / (L * δ) ^ K := by positivity
        have e1 : CV * (2 * L * nearMass L h k δ + 2 * L * A / (L * δ) ^ K * ∑' P, pairWeight L P)
            = 2 * CV * (L * nearMass L h k δ) + 2 * CV * A * (L / (L * δ) ^ K * ∑' P,
              pairWeight L P) := by ring
        rw [e1]
        have h1 : 0 ≤ 2 * CV * A * (L * nearMass L h k δ) := by positivity
        have h2 : 0 ≤ 2 * CV * (L / (L * δ) ^ K * ∑' P, pairWeight L P) := by positivity
        nlinarith

/-! ## The dual off-diagonal -/

/-- The dual oscillation at a pair, trivially: `‖J(mnL, η)‖ ≤ 2L C min(1, L/(mn))`. -/
theorem exists_norm_dualOsc_pair_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {L : ℝ}, 2 ≤ L → ∀ (P : ℕ × ℕ) (η : ℝ),
      ‖dualOsc L (pairProd P * L) η‖ ≤ 2 * L * (C * min 1 (L / pairProd P)) := by
  obtain ⟨C₁, hC₁, h₁⟩ := exists_norm_critDualWeight_window_le
  obtain ⟨C₂, hC₂, h₂⟩ := exists_norm_critDualWeight_sub_one_le
  refine ⟨C₁ + 1 + 2 * C₂, by positivity, fun {L} hL P η => ?_⟩
  have hL0 : 0 < L := by linarith
  have hP := pairProd_pos P
  have hY : 0 < pairProd P * L := mul_pos hP hL0
  apply norm_integral_notchWindow_mul_cexp_le_trivial hL0 (G := fun t => critDualWeight t (pairProd P * L))
  intro t ht
  have ht1 : 1 ≤ t := by linarith [ht.1]
  have ht0 : 0 < t := by linarith
  rcases le_or_gt (pairProd P) L with hPL | hPL
  · rw [min_eq_left ((one_le_div hP).mpr hPL)]
    have hYt : pairProd P * L ≤ (2 * t) ^ 2 := by nlinarith [ht.1]
    have hr : (pairProd P * L) ^ rightAbscissa ≤ Real.sqrt 2 * Real.sqrt t := by
      rw [← Real.sqrt_mul (by norm_num), Real.sqrt_eq_rpow]
      unfold rightAbscissa
      calc (pairProd P * L) ^ (1 / 4 : ℝ) ≤ ((2 * t) ^ 2) ^ (1 / 4 : ℝ) :=
            Real.rpow_le_rpow hY.le hYt (by norm_num)
        _ = (2 * t) ^ (1 / 2 : ℝ) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
            norm_num
    have hs2 : Real.sqrt 2 ≤ 2 := by
      rw [Real.sqrt_le_left (by norm_num)]
      norm_num
    have hst : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht0
    have hsub := h₂ ht1 hY
    have hq : C₂ * (pairProd P * L) ^ rightAbscissa / Real.sqrt t ≤ 2 * C₂ := by
      rw [div_le_iff₀ hst]
      calc C₂ * (pairProd P * L) ^ rightAbscissa ≤ C₂ * (Real.sqrt 2 * Real.sqrt t) :=
            mul_le_mul_of_nonneg_left hr hC₂
        _ ≤ C₂ * (2 * Real.sqrt t) := by gcongr
        _ = 2 * C₂ * Real.sqrt t := by ring
    calc ‖critDualWeight t (pairProd P * L)‖
        ≤ ‖critDualWeight t (pairProd P * L) - 1‖ + ‖(1 : ℂ)‖ := norm_le_norm_sub_add _ _
      _ ≤ 2 * C₂ + 1 := by rw [norm_one]; linarith
      _ ≤ (C₁ + 1 + 2 * C₂) * 1 := by linarith
  · rw [min_eq_right ((div_le_one hP).mpr hPL.le)]
    calc ‖critDualWeight t (pairProd P * L)‖ ≤ C₁ * L ^ 2 / (pairProd P * L) := h₁ hL ht hY
      _ = C₁ * (L / pairProd P) := by field_simp
      _ ≤ (C₁ + 1 + 2 * C₂) * (L / pairProd P) := by gcongr; linarith

/-- The zeta constant `Σ_{m,n} (mn)^{−3/2}`. -/
def pairZeta32 : ℝ := ∑' P : ℕ × ℕ, pairProd P ^ (-(3 / 2 : ℝ))

/-- **Dual off-diagonal bound.** -/
theorem exists_norm_dualOff_le (K : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {L δ : ℝ}, 16 ≤ L → 0 < δ → ∀ {h k : ℕ}, 0 < h → 0 < k →
      ‖dualOff L h k‖ ≤ C * (L * nearMass L k h δ +
        L ^ 2 * (1 / (L * δ) ^ K + Real.exp (-(L ^ 2) / 32))) := by
  obtain ⟨CW, hCW, hW⟩ := exists_norm_dualOsc_pair_le
  obtain ⟨CK, hCK, hJ⟩ := exists_norm_notchDualOscillation_le_pow K
  have hZ : 0 ≤ pairZeta32 := tsum_nonneg fun P => Real.rpow_nonneg (pairProd_pos P).le _
  have hs32 := summable_pairProd_rpow (s := 3 / 2) (by norm_num)
  refine ⟨2 * CW + CK * pairZeta32, by positivity, fun {L δ} hL hδ {h k} hh hk => ?_⟩
  have hL0 : 0 < L := by linarith
  have hLδ : 0 < L * δ := mul_pos hL0 hδ
  set ξ : ℝ := Real.log h - Real.log k with hξ
  set E : ℝ := 1 / (L * δ) ^ K + Real.exp (-(L ^ 2) / 32) with hE
  have hE0 : 0 ≤ E := by positivity
  set g : ℕ × ℕ → ℂ := fun P => (pairAmp P : ℂ) * dualOsc L (pairProd P * L) (ξ + pairFreq P)
    with hg
  set S : Set (ℕ × ℕ) := {P : ℕ × ℕ | (P.1 + 1) * k = (P.2 + 1) * h}ᶜ with hS
  have hnear : Summable (fun P : ℕ × ℕ => if nearRes k h δ P then pairWeight L P else 0) := by
    refine Summable.of_nonneg_of_le (fun P => ?_) (fun P => ?_) (summable_pairWeight hL0.le)
    · split_ifs
      · exact pairWeight_nonneg hL0.le P
      · exact le_refl _
    · split_ifs
      · exact le_refl _
      · exact pairWeight_nonneg hL0.le P
  set b : ℕ × ℕ → ℝ := fun P => 2 * L * CW * (if nearRes k h δ P then pairWeight L P else 0) +
    CK * L ^ 2 * E * pairProd P ^ (-(3 / 2 : ℝ)) with hb
  have hb0 : ∀ P, 0 ≤ b P := fun P => by
    simp only [hb]
    apply add_nonneg
    · apply mul_nonneg (by positivity)
      split_ifs
      · exact pairWeight_nonneg hL0.le P
      · exact le_refl _
    · exact mul_nonneg (by positivity) (Real.rpow_nonneg (pairProd_pos P).le _)
  have hbs : Summable b := (hnear.mul_left _).add (hs32.mul_left _)
  have hpt : ∀ P ∈ S, ‖g P‖ ≤ b P := by
    intro P hP
    have hP' : (P.2 + 1) * h ≠ (P.1 + 1) * k := fun he => hP he.symm
    have hgn : ‖g P‖ = pairAmp P * ‖dualOsc L (pairProd P * L) (ξ + pairFreq P)‖ := by
      simp only [hg, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (pairAmp_pos P)]
    rw [hgn]
    have hw0 := pairWeight_nonneg hL0.le P
    have hrest : 0 ≤ CK * L ^ 2 * E * pairProd P ^ (-(3 / 2 : ℝ)) :=
      mul_nonneg (by positivity) (Real.rpow_nonneg (pairProd_pos P).le _)
    rcases nearRes_or_le hk hh hP' (δ := δ) with hn | hsep
    · have hw := hW (by linarith : (2 : ℝ) ≤ L) P (ξ + pairFreq P)
      calc pairAmp P * ‖dualOsc L (pairProd P * L) (ξ + pairFreq P)‖
          ≤ pairAmp P * (2 * L * (CW * min 1 (L / pairProd P))) :=
            mul_le_mul_of_nonneg_left hw (pairAmp_pos P).le
        _ = 2 * L * CW * pairWeight L P := by rw [pairWeight_eq]; ring
        _ ≤ b P := by
            simp only [hb, if_pos hn]
            linarith
    · have hη : δ ≤ |ξ + pairFreq P| := by
        have e : pairFreq P - (Real.log k - Real.log h) = ξ + pairFreq P := by rw [hξ]; ring
        rw [← e]; exact hsep
      have hη0 : ξ + pairFreq P ≠ 0 := fun h0 => by
        rw [h0, abs_zero] at hη; linarith
      have hY : 0 < pairProd P * L := mul_pos (pairProd_pos P) hL0
      have hj := hJ hL hY hη0
      have hpow : (L * δ) ^ K ≤ (L * |ξ + pairFreq P|) ^ K :=
        pow_le_pow_left₀ hLδ.le (mul_le_mul_of_nonneg_left hη hL0.le) K
      have hj' : ‖dualOsc L (pairProd P * L) (ξ + pairFreq P)‖ ≤
          CK / (pairProd P * L) * (L ^ 3 * E) := by
        refine hj.trans ?_
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        rw [hE, mul_add, mul_one_div]
        gcongr
      calc pairAmp P * ‖dualOsc L (pairProd P * L) (ξ + pairFreq P)‖
          ≤ pairAmp P * (CK / (pairProd P * L) * (L ^ 3 * E)) :=
            mul_le_mul_of_nonneg_left hj' (pairAmp_pos P).le
        _ = CK * L ^ 2 * E * (pairAmp P * pairProd P ^ (-(1 : ℝ))) := by
            rw [Real.rpow_neg_one]
            field_simp
        _ = CK * L ^ 2 * E * pairProd P ^ (-(3 / 2 : ℝ)) := by
            rw [pairAmp_mul_rpow]
            norm_num
        _ ≤ b P := by
            simp only [hb]
            have : 0 ≤ 2 * L * CW * (if nearRes k h δ P then pairWeight L P else 0) := by
              apply mul_nonneg (by positivity)
              split_ifs
              · exact hw0
              · exact le_refl _
            linarith
  have hgs : Summable (fun P : S => ‖g P‖) :=
    (summable_dualFamily (by linarith) ξ).norm.subtype S
  calc ‖dualOff L h k‖ ≤ ∑' P : S, ‖g P‖ := norm_tsum_le_tsum_norm hgs
    _ ≤ ∑' P : S, b P := hgs.tsum_le_tsum (fun P => hpt P.1 P.2) (hbs.subtype S)
    _ ≤ ∑' P, b P := Summable.tsum_subtype_le b S hb0 hbs
    _ = 2 * L * CW * nearMass L k h δ + CK * L ^ 2 * E * pairZeta32 := by
        simp only [hb]
        rw [Summable.tsum_add (hnear.mul_left _) (hs32.mul_left _), tsum_mul_left, tsum_mul_left]
        rfl
    _ ≤ (2 * CW + CK * pairZeta32) * (L * nearMass L k h δ + L ^ 2 * E) := by
        have hN := nearMass_nonneg hL0.le k h δ
        have h1 : 0 ≤ CK * pairZeta32 * (L * nearMass L k h δ) := by positivity
        have h2 : 0 ≤ 2 * CW * (L ^ 2 * E) := by positivity
        nlinarith

/-! ## The residue part -/

/-- The product-AFE residue on the critical line: `‖R‖ ≤ 9e L e^{−t²}` for `|t| ≥ 4`. -/
theorem norm_productAFEShiftedResidue_line_le {L : ℝ} (hL1 : 1 ≤ L) {t : ℝ} (ht : 4 ≤ |t|) :
    ‖productAFEShiftedResidue (linePt t) (linePt (-t)) L‖ ≤
      9 * Real.exp 1 * L * Real.exp (-(t ^ 2)) := by
  have hL : 0 < L := by linarith
  unfold productAFEShiftedResidue
  have hs1 : (1 : ℂ) - linePt t = ((1 / 2 : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I := by
    unfold linePt
    push_cast
    ring
  have hz : linePt (-t) + (1 - linePt t) = ((1 : ℝ) : ℂ) + ((-2 * t : ℝ) : ℂ) * I := by
    unfold linePt
    push_cast
    ring
  rw [hz, norm_div, norm_mul, norm_mul, hs1]
  have h1 : ‖(L : ℂ) ^ (((1 / 2 : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I)‖ ≤ L := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hL]
    have hre : (((1 / 2 : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I).re = 1 / 2 := by simp
    rw [hre]
    calc L ^ (1 / 2 : ℝ) ≤ L ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
      _ = L := Real.rpow_one L
  have h2 : ‖Complex.exp ((((1 / 2 : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I) ^ 2)‖
      ≤ Real.exp 1 * Real.exp (-(t ^ 2)) := by
    rw [Complex.norm_exp, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have : ((((1 / 2 : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I) ^ 2).re = (1 / 2) ^ 2 - t ^ 2 := by
      simp [sq]
    rw [this]
    nlinarith
  have h3 : ‖riemannZeta (((1 : ℝ) : ℂ) + ((-2 * t : ℝ) : ℂ) * I)‖ ≤ 3 / 2 + 1 / 8 + 8 * |t| := by
    have hσ : (1 : ℝ) ∈ Set.Ioc 0 2 := ⟨by norm_num, by norm_num⟩
    have habs : |(-2 * t : ℝ)| = 2 * |t| := by rw [abs_mul, abs_neg, abs_two]
    have ht2 : 2 ≤ |(-2 * t : ℝ)| := by rw [habs]; linarith
    have h := RHTower.ZetaGateProductAFE.norm_riemannZeta_le_strip' hσ ht2
    have hden : ‖(1 : ℂ) - (((1 : ℝ) : ℂ) + ((-2 * t : ℝ) : ℂ) * I)‖ = 2 * |t| := by
      have : (1 : ℂ) - (((1 : ℝ) : ℂ) + ((-2 * t : ℝ) : ℂ) * I) = ((2 * t : ℝ) : ℂ) * I := by
        push_cast; ring
      rw [this, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_mul, abs_two]
    rw [hden, habs] at h
    have h8 : 1 / (2 * |t|) ≤ 1 / 8 := by
      rw [div_le_div_iff₀ (by linarith) (by norm_num)]
      linarith
    calc ‖riemannZeta (((1 : ℝ) : ℂ) + ((-2 * t : ℝ) : ℂ) * I)‖
        ≤ 3 / 2 + 1 / (2 * |t|) + 2 * (2 * |t|) / 1 := h
      _ ≤ 3 / 2 + 1 / 8 + 8 * |t| := by linarith
  have h4 : |t| ≤ ‖((1 / 2 : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I‖ := by
    have := Complex.abs_im_le_norm (((1 / 2 : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I)
    have him : (((1 / 2 : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I).im = -t := by simp
    rw [him, abs_neg] at this
    exact this
  have hden0 : 0 < ‖((1 / 2 : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I‖ := by linarith
  rw [div_le_iff₀ hden0]
  calc ‖(L : ℂ) ^ (((1 / 2 : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I)‖
        * ‖Complex.exp ((((1 / 2 : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I) ^ 2)‖
        * ‖riemannZeta (((1 : ℝ) : ℂ) + ((-2 * t : ℝ) : ℂ) * I)‖
      ≤ L * (Real.exp 1 * Real.exp (-(t ^ 2))) * (3 / 2 + 1 / 8 + 8 * |t|) :=
        mul_le_mul (mul_le_mul h1 h2 (norm_nonneg _) hL.le) h3 (norm_nonneg _) (by positivity)
    _ ≤ (L * (Real.exp 1 * Real.exp (-(t ^ 2)))) * (9 * |t|) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ = 9 * Real.exp 1 * L * Real.exp (-(t ^ 2)) * |t| := by ring
    _ ≤ 9 * Real.exp 1 * L * Real.exp (-(t ^ 2)) * ‖((1 / 2 : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I‖ :=
        mul_le_mul_of_nonneg_left h4 (by positivity)

theorem norm_residueTerm_le {L : ℝ} (hL1 : 1 ≤ L) {t : ℝ} (ht : 4 ≤ |t|) :
    ‖residueTerm L t‖ ≤ 18 * Real.exp 1 * L * Real.exp (-(t ^ 2)) := by
  unfold residueTerm
  have hr1 := norm_productAFEShiftedResidue_line_le hL1 ht
  have hr2 := norm_productAFEShiftedResidue_line_le hL1 (t := -t) (by rwa [abs_neg])
  rw [neg_neg, neg_sq] at hr2
  calc ‖productAFEShiftedResidue (linePt t) (linePt (-t)) L +
        productAFEShiftedResidue (linePt (-t)) (linePt t) L‖
      ≤ ‖productAFEShiftedResidue (linePt t) (linePt (-t)) L‖ +
        ‖productAFEShiftedResidue (linePt (-t)) (linePt t) L‖ := norm_add_le _ _
    _ ≤ 9 * Real.exp 1 * L * Real.exp (-(t ^ 2)) + 9 * Real.exp 1 * L * Real.exp (-(t ^ 2)) :=
        add_le_add hr1 hr2
    _ = 18 * Real.exp 1 * L * Real.exp (-(t ^ 2)) := by ring

/-- The residue part is Gaussian-small: `‖∫ ω R_L e^{−iξt}‖ ≤ 36e L² e^{−L²/4}`. -/
theorem norm_residueOsc_le {L : ℝ} (hL : 8 ≤ L) (ξ : ℝ) :
    ‖residueOsc L ξ‖ ≤ 36 * Real.exp 1 * L ^ 2 * Real.exp (-(L ^ 2) / 4) := by
  have hL0 : 0 < L := by linarith
  have h := norm_integral_notchWindow_mul_cexp_le_trivial hL0 (G := residueTerm L)
    (A := 18 * Real.exp 1 * L * Real.exp (-(L ^ 2) / 4)) (ξ := ξ) (fun t ht => by
      have ht0 : 0 ≤ t := by linarith [ht.1]
      have ht4 : 4 ≤ |t| := by rw [abs_of_nonneg ht0]; linarith [ht.1]
      refine (norm_residueTerm_le (by linarith) ht4).trans ?_
      gcongr
      nlinarith [ht.1])
  unfold residueOsc
  refine h.trans (le_of_eq ?_)
  ring

/-! ## The twisted moment is its diagonal -/

/-- **Twisted moment = diagonal + small.** For coprime `h, k ≥ 1`, `0 < δ`, `K ∈ ℕ`:
`‖∫ω|ζ|²(k/h)^{it} − (hk)^{−1/2}𝒟_L(hk)‖ ≤ C(L 𝒩_L(h,k,δ) + L²/(Lδ)^K + L² e^{−L²/32})`. -/
theorem exists_norm_twistedMoment_sub_diag_le (K : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {L δ : ℝ}, 16 ≤ L → 0 < δ → ∀ {h k : ℕ}, 0 < h → 0 < k →
      Nat.Coprime h k →
      ‖twistedMoment L (Real.log h - Real.log k) -
          ((Real.sqrt (h * k) : ℂ))⁻¹ * diagMain L (h * k)‖ ≤
        C * (L * nearMass L h k δ + L ^ 2 / (L * δ) ^ K + L ^ 2 * Real.exp (-(L ^ 2) / 32)) := by
  obtain ⟨C₁, hC₁, h₁⟩ := exists_norm_directOff_le K
  obtain ⟨C₂, hC₂, h₂⟩ := exists_norm_dualOff_le K
  have hZ := pairZeta_nonneg
  refine ⟨C₁ * (1 + pairZeta) + C₂ + 36 * Real.exp 1, by positivity,
    fun {L δ} hL hδ {h k} hh hk hcop => ?_⟩
  have hL0 : 0 < L := by linarith
  have hL1 : 1 ≤ L := by linarith
  have hLδ : 0 < L * δ := mul_pos hL0 hδ
  rw [twistedMoment_eq_diag_add hL hh hk hcop]
  have hswap : nearMass L k h δ = nearMass L h k δ := tsum_nearRes_swap_eq hh hk δ L
  have hd := h₁ hL0 hδ hh hk
  have hu := h₂ hL hδ hh hk
  rw [hswap] at hu
  have hr := norm_residueOsc_le (by linarith : (8 : ℝ) ≤ L) (Real.log h - Real.log k)
  have hW := tsum_pairWeight_le hL0.le
  have hN := nearMass_nonneg hL0.le h k δ
  have h34 : L ^ (3 / 4 : ℝ) ≤ L := by
    calc L ^ (3 / 4 : ℝ) ≤ L ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
      _ = L := Real.rpow_one L
  have hq : 0 ≤ L / (L * δ) ^ K := by positivity
  have hdir : ‖directOff L h k‖ ≤ C₁ * (L * nearMass L h k δ + pairZeta * (L ^ 2 / (L * δ) ^ K)) := by
    refine hd.trans (mul_le_mul_of_nonneg_left ?_ hC₁)
    have : L / (L * δ) ^ K * ∑' P, pairWeight L P ≤ pairZeta * (L ^ 2 / (L * δ) ^ K) := by
      calc L / (L * δ) ^ K * ∑' P, pairWeight L P ≤ L / (L * δ) ^ K * (pairZeta * L) :=
            mul_le_mul_of_nonneg_left (hW.trans (mul_le_mul_of_nonneg_left h34 hZ)) hq
        _ = pairZeta * (L ^ 2 / (L * δ) ^ K) := by ring
    linarith
  have hexp : Real.exp (-(L ^ 2) / 4) ≤ Real.exp (-(L ^ 2) / 32) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have hres : ‖residueOsc L (Real.log h - Real.log k)‖ ≤
      36 * Real.exp 1 * (L ^ 2 * Real.exp (-(L ^ 2) / 32)) := by
    refine hr.trans ?_
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
  set X : ℝ := L * nearMass L h k δ with hX
  set Y : ℝ := L ^ 2 / (L * δ) ^ K with hY
  set Z : ℝ := L ^ 2 * Real.exp (-(L ^ 2) / 32) with hZdef
  have hX0 : 0 ≤ X := by positivity
  have hY0 : 0 ≤ Y := by positivity
  have hZ0 : 0 ≤ Z := by positivity
  have hu' : ‖dualOff L h k‖ ≤ C₂ * (X + Y + Z) := by
    refine hu.trans (le_of_eq ?_)
    rw [hX, hY, hZdef]
    ring
  have e1 : C₁ * (X + pairZeta * Y) ≤ C₁ * (1 + pairZeta) * (X + Y + Z) := by
    have : X + pairZeta * Y ≤ (1 + pairZeta) * (X + Y + Z) := by nlinarith
    calc C₁ * (X + pairZeta * Y) ≤ C₁ * ((1 + pairZeta) * (X + Y + Z)) :=
          mul_le_mul_of_nonneg_left this hC₁
      _ = C₁ * (1 + pairZeta) * (X + Y + Z) := by ring
  have e3 : 36 * Real.exp 1 * Z ≤ 36 * Real.exp 1 * (X + Y + Z) := by
    have : 0 ≤ 36 * Real.exp 1 := by positivity
    nlinarith
  calc ‖directOff L h k‖ + ‖dualOff L h k‖ + ‖residueOsc L (Real.log h - Real.log k)‖
      ≤ C₁ * (X + pairZeta * Y) + C₂ * (X + Y + Z) + 36 * Real.exp 1 * Z := by
        rw [hX, hY, hZdef]
        linarith
    _ ≤ (C₁ * (1 + pairZeta) + C₂ + 36 * Real.exp 1) * (X + Y + Z) := by nlinarith

end RHTower.ZetaNotch
