import GaloisForLFunctions.SignedWindowCriticality.TheMarkovPartDiesBeforeTheFirstPrime
import GaloisForLFunctions.SignedWindowCriticality.TheKickIsAPositiveSourceAndANegativeCollarConductance
import GaloisForLFunctions.ArithmeticIncidencePositivity.GlobalIncidenceAllocationCondition

/-!
# The frozen odd form is Markov, and the kick is not

On odd tests the archimedean place and the pole form a light cone: same-side pairs carry
`ω(|x − y|)`, crossing pairs `ω(x + y) ≤ ω(|x − y|)` (AIP's exact fold
`J_P(F) = 2S_P(F) + 4∫F²Π_P`), and the pole contributes `−2(∫F sinh(x/2))²`. The frustration of the
odd sector is the prime anti-diagonal. This file states it as a Beurling–Deny property.

For an odd test `F` let `F̃ = sign(x)|F|` (`oddAbs`): the odd test with the same modulus, positive
on the half-line.

* **The archimedean energy is Markov on odd tests** (`levyEnergy_oddAbs_le`):
  `∫ω(t)‖F̃ − F̃(·+t)‖²dt ≤ ∫ω(t)‖F − F(·+t)‖²dt`. In AIP's fold the crossing potential reads only
  `F²`, and the surplus `S_P` has nonnegative weights `ω(s) − ω(s + 2x)` on same-side jumps, which
  the contraction `|·|` does not raise.
* **The pole is Markov on odd tests** (`sq_sinhPairing_le_oddAbs`): `F̃ sinh(x/2) = |F sinh(x/2)|`.
* **The frozen odd form is Markov** (`frozenOddForm_oddAbs_le`): with no prime acting,
  `M₁(F̃) − ½⟨s, F̃⟩² ≤ M₁(F) − ½⟨s, F⟩²`.
* **The kick is anti-Markov** (`kick_le_kick_oddAbs`): for `F` supported in `[−a, a]`, `a ≤ ℓ`,
  `−2w c_F(ℓ) ≤ −2w c_{F̃}(ℓ)`: on the anti-diagonal `F(s)F(ℓ − s) ≤ |F(s)||F(ℓ − s)|`.
* **The first stage** (`markovForm_two_sub_one`, `firstStage_frustration`). On the first prime stage
  `M₂ = M₁ − 2w₂c(log 2)`: the frozen part decreases and the kick increases under `F ↦ F̃`. The odd
  first-stage form is a Markov form plus an anti-Markov kick; no gauge or sign gauge turns it into
  a Markov form, and its sign is decided by the competition of the two.
-/

open MeasureTheory Set Filter Topology
open scoped Real

noncomputable section

namespace GaloisForLFunctions.SignedWindowCriticality

open _root_.RHTower _root_.RHTower.WeilMarkovPole _root_.RHTower.CHMDPolar
open GaloisForLFunctions.ArithmeticCriticalityTheory GaloisForLFunctions.ArithmeticIncidencePositivity

/-- The positive odd test with the modulus of `F`: `|F|` on `[0, ∞)`, `−|F|` on `(−∞, 0)`. -/
def oddAbs (F : ℝ → ℝ) (x : ℝ) : ℝ := if 0 ≤ x then |F x| else -|F x|

variable {F : ℝ → ℝ}

theorem oddAbs_of_nonneg {x : ℝ} (hx : 0 ≤ x) : oddAbs F x = |F x| := if_pos hx

theorem oddAbs_of_neg {x : ℝ} (hx : x < 0) : oddAbs F x = -|F x| := if_neg (not_le.mpr hx)

theorem oddAbs_sq (x : ℝ) : oddAbs F x ^ 2 = F x ^ 2 := by
  unfold oddAbs; split_ifs <;> simp [sq_abs]

theorem odd_apply_zero' (hFo : ∀ x, F (-x) = -F x) : F 0 = 0 := by
  have h := hFo 0; rw [neg_zero] at h; linarith

theorem oddAbs_eq_zero_iff {x : ℝ} : oddAbs F x = 0 ↔ F x = 0 := by
  unfold oddAbs; split_ifs <;> simp

theorem oddAbs_odd (hFo : ∀ x, F (-x) = -F x) (x : ℝ) : oddAbs F (-x) = -oddAbs F x := by
  rcases lt_trichotomy x 0 with h | h | h
  · rw [oddAbs_of_nonneg (by linarith), oddAbs_of_neg h, hFo, abs_neg, neg_neg]
  · subst h; simp [oddAbs, odd_apply_zero' hFo]
  · rw [oddAbs_of_neg (by linarith), oddAbs_of_nonneg h.le, hFo, abs_neg]

theorem continuous_oddAbs (hF : Continuous F) (hFo : ∀ x, F (-x) = -F x) :
    Continuous (oddAbs F) := by
  unfold oddAbs
  exact Continuous.if_le hF.abs hF.abs.neg continuous_const continuous_id fun x hx => by
    rw [← hx, odd_apply_zero' hFo]; simp

theorem oddAbs_lipschitz (hFo : ∀ x, F (-x) = -F x) {K : ℝ}
    (hFL : ∀ a b, |F a - F b| ≤ K * |a - b|) (a b : ℝ) :
    |oddAbs F a - oddAbs F b| ≤ K * |a - b| := by
  have h0 := odd_apply_zero' hFo
  have hA : ∀ y, |F y| ≤ K * |y| := fun y => by simpa [h0] using hFL y 0
  rcases le_or_gt 0 a with ha | ha <;> rcases le_or_gt 0 b with hb | hb
  · rw [oddAbs_of_nonneg ha, oddAbs_of_nonneg hb]
    exact (abs_abs_sub_abs_le _ _).trans (hFL a b)
  · rw [oddAbs_of_nonneg ha, oddAbs_of_neg hb, sub_neg_eq_add,
      abs_of_nonneg (by positivity), abs_of_pos (by linarith : 0 < a - b)]
    have h1 := hA a; have h2 := hA b
    rw [abs_of_nonneg ha] at h1; rw [abs_of_neg hb] at h2
    linarith
  · rw [oddAbs_of_neg ha, oddAbs_of_nonneg hb, abs_sub_comm, sub_neg_eq_add,
      abs_of_nonneg (by positivity), abs_of_neg (by linarith : a - b < 0)]
    have h1 := hA a; have h2 := hA b
    rw [abs_of_neg ha] at h1; rw [abs_of_nonneg hb] at h2
    linarith
  · rw [oddAbs_of_neg ha, oddAbs_of_neg hb, show -|F a| - -|F b| = -(|F a| - |F b|) by ring,
      abs_neg]
    exact (abs_abs_sub_abs_le _ _).trans (hFL a b)

/-! ### The pole is Markov on odd tests -/

theorem oddAbs_mul_sinh (u : ℝ) :
    oddAbs F u * (2 * Real.sinh (u / 2)) = |F u * (2 * Real.sinh (u / 2))| := by
  rcases le_or_gt 0 u with hu | hu
  · have hs : (0 : ℝ) ≤ 2 * Real.sinh (u / 2) := by
      have : 0 ≤ Real.sinh (u / 2) := Real.sinh_nonneg_iff.mpr (by linarith)
      linarith
    rw [oddAbs_of_nonneg hu, abs_mul, abs_of_nonneg hs]
  · have hs : 2 * Real.sinh (u / 2) < 0 := by
      have : Real.sinh (u / 2) < 0 := Real.sinh_neg_iff.mpr (by linarith)
      linarith
    rw [oddAbs_of_neg hu, abs_mul, abs_of_neg hs]
    ring

theorem sq_sinhPairing_le_oddAbs :
    sinhPairing F ^ 2 ≤ sinhPairing (oddAbs F) ^ 2 := by
  have h : sinhPairing (oddAbs F) = ∫ u, |F u * (2 * Real.sinh (u / 2))| := by
    unfold sinhPairing
    exact integral_congr_ae (Eventually.of_forall fun u => oddAbs_mul_sinh u)
  have habs : |sinhPairing F| ≤ sinhPairing (oddAbs F) := by
    rw [h]; exact abs_integral_le_integral_abs
  have h0 : 0 ≤ sinhPairing (oddAbs F) := (abs_nonneg _).trans habs
  rw [← sq_abs]
  exact pow_le_pow_left₀ (abs_nonneg _) habs 2

/-! ### The archimedean energy is Markov on odd tests -/

section Arch

variable {K r : ℝ}

/-- The gauge of the fold: `1` on `[−r, r]`, `0` beyond `r + 1`. -/
def foldGauge (r : ℝ) : ℝ → ℝ := aperturePlateau r (r + 1)

theorem foldGauge_props (r : ℝ) :
    Continuous (foldGauge r) ∧ (∀ y, foldGauge r (-y) = foldGauge r y) ∧
      (∀ y, 0 ≤ foldGauge r y) ∧ (∀ y, foldGauge r y ≤ 1) ∧
      (∀ y, r + 1 ≤ |y| → foldGauge r y = 0) ∧ (∀ y, |y| ≤ r → foldGauge r y = 1) := by
  have hδ : (0 : ℝ) < r + 1 - r := by linarith
  refine ⟨(contDiff_plateauGauge _ _).continuous, fun y => ?_, fun y => plateauGauge_nonneg _ _ y,
    fun y => plateauGauge_le_one _ _ y, fun y hy => plateauGauge_eq_zero hδ hy,
    fun y hy => plateauGauge_eq_one hδ (by linarith)⟩
  simp only [foldGauge, aperturePlateau, plateauGauge, sub_neg_eq_add, ← sub_eq_add_neg]
  ring

/-- Shift profiles of a Lipschitz test are integrable against the Lévy density. -/
theorem integrableOn_archLevy_shiftSq {G : ℝ → ℝ} (hG : Continuous G) (hGc : HasCompactSupport G)
    (hGL : ∀ a b, |G a - G b| ≤ K * |a - b|) :
    IntegrableOn (fun t => archLevyDensity t * ∫ u, (G u - G (u + t)) ^ 2) (Ioi 0) := by
  have hc : Continuous fun p : ℝ × ℝ => (G p.2 - G (p.2 + p.1)) ^ 2 := by fun_prop
  have hm : StronglyMeasurable fun t : ℝ => ∫ u, (G u - G (u + t)) ^ 2 :=
    hc.stronglyMeasurable.integral_prod_right'
  refine (integrableOn_archLevyDensity_mul_id.const_mul (2 * K * ∫ u, |G u|)).mono'
    (measurable_archLevyDensity.mul hm.measurable).aestronglyMeasurable ?_
  refine ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_
  have ht0 : 0 < t := ht
  have hb := SpacingScaleHarmonicAnalysis.integral_sub_shift_sq_le_lipschitz hG hGc hGL t
  rw [abs_of_pos ht0] at hb
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (archLevyDensity_pos ht0).le
    (integral_nonneg fun u => sq_nonneg _))]
  have hA := (archLevyDensity_pos ht0).le
  nlinarith [mul_le_mul_of_nonneg_left hb hA]

/-- Gauge jump profiles of a Lipschitz test are integrable against the Lévy density. -/
theorem integrableOn_archLevy_gaugeJumpProfile {G P : ℝ → ℝ} (hG : Continuous G)
    (hGc : HasCompactSupport G) (hGL : ∀ a b, |G a - G b| ≤ K * |a - b|) (hPc : Continuous P)
    (hP0 : ∀ y, 0 ≤ P y) (hP1 : ∀ y, P y ≤ 1) :
    IntegrableOn (fun t => archLevyDensity t * gaugeJumpProfile P G t) (Ioi 0) := by
  have hc : Continuous fun p : ℝ × ℝ => signedShiftJump P G p.1 p.2 := by
    unfold signedShiftJump; fun_prop
  have hm : StronglyMeasurable fun t : ℝ => gaugeJumpProfile P G t :=
    hc.stronglyMeasurable.integral_prod_right'
  refine (integrableOn_archLevy_shiftSq hG hGc hGL).mono'
    (measurable_archLevyDensity.mul hm.measurable).aestronglyMeasurable ?_
  refine ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_
  have ht0 : 0 < t := ht
  have hsj : ∀ x, 0 ≤ signedShiftJump P G t x := fun x => by
    unfold signedShiftJump; exact mul_nonneg (mul_nonneg (hP0 x) (hP0 _)) (sq_nonneg _)
  have hle : gaugeJumpProfile P G t ≤ ∫ u, (G u - G (u + t)) ^ 2 := by
    unfold gaugeJumpProfile
    have hcs : HasCompactSupport fun u => (G u - G (u + t)) ^ 2 :=
      ArithmeticCriticalityTheory.hasCompactSupport_sq
        (hGc.sub (hGc.comp_homeomorph (Homeomorph.addRight t)))
    have hcont : Continuous fun u => (G u - G (u + t)) ^ 2 := by fun_prop
    refine integral_mono_of_nonneg (Eventually.of_forall hsj)
      (hcont.integrable_of_hasCompactSupport hcs) (Eventually.of_forall fun x => ?_)
    · unfold signedShiftJump
      have h1 := hP1 x; have h2 := hP1 (x + t); have h3 := hP0 x; have h4 := hP0 (x + t)
      have : P x * P (x + t) ≤ 1 := mul_le_one₀ h1 h4 h2
      nlinarith [sq_nonneg (G x - G (x + t)), mul_nonneg h3 h4]
  have hg0 : 0 ≤ gaugeJumpProfile P G t := integral_nonneg hsj
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (archLevyDensity_pos ht0).le hg0)]
  exact mul_le_mul_of_nonneg_left hle (archLevyDensity_pos ht0).le

/-- Off the gauge's plateau the shift energy reads only the squares. -/
theorem shiftSq_sub_signedShiftJump {G P : ℝ → ℝ} (hGP : ∀ x, G x ≠ 0 → P x = 1) (t x : ℝ) :
    (G x - G (x + t)) ^ 2 - signedShiftJump P G t x =
      (1 - P x * P (x + t)) * (G x ^ 2 + G (x + t) ^ 2) := by
  unfold signedShiftJump
  by_cases h1 : G x = 0
  · rw [h1]; ring
  · by_cases h2 : G (x + t) = 0
    · rw [h2]; ring
    · rw [hGP x h1, hGP _ h2]; ring

end Arch

/-- **The archimedean energy is Markov on odd tests.** -/
theorem levyEnergy_oddAbs_le (hF : Continuous F) (hFo : ∀ x, F (-x) = -F x) {K r : ℝ}
    (hFL : ∀ a b, |F a - F b| ≤ K * |a - b|) (hr : 0 ≤ r) (hsupp : ∀ x, r < |x| → F x = 0) :
    levyEnergy (oddAbs F) ≤ levyEnergy F := by
  obtain ⟨hPc, hPe, hP0, hP1, hPB, hPr⟩ := foldGauge_props r
  set P := foldGauge r
  set G := oddAbs F
  have hB0 : (0 : ℝ) < r + 1 := by linarith
  have hGc : Continuous G := continuous_oddAbs hF hFo
  have hGo : ∀ x, G (-x) = -G x := oddAbs_odd hFo
  have hGL : ∀ a b, |G a - G b| ≤ K * |a - b| := oddAbs_lipschitz hFo hFL
  have hFcs : HasCompactSupport F :=
    HasCompactSupport.intro (isCompact_Icc (a := -r) (b := r)) fun x hx =>
      hsupp x (by by_contra h; exact hx (abs_le.mp (not_lt.mp h)))
  have hGsupp : ∀ x, r < |x| → G x = 0 := fun x hx => oddAbs_eq_zero_iff.mpr (hsupp x hx)
  have hGcs : HasCompactSupport G :=
    HasCompactSupport.intro (isCompact_Icc (a := -r) (b := r)) fun x hx =>
      hGsupp x (by by_contra h; exact hx (abs_le.mp (not_lt.mp h)))
  have hFP : ∀ x, F x ≠ 0 → P x = 1 := fun x hx =>
    hPr x (by by_contra h; exact hx (hsupp x (not_le.mp h)))
  have hGP : ∀ x, G x ≠ 0 → P x = 1 := fun x hx => hFP x (fun h => hx (oddAbs_eq_zero_iff.mpr h))
  have hFB : ∀ x, r + 1 ≤ |x| → F x = 0 := fun x hx => hsupp x (by linarith)
  have hGB : ∀ x, r + 1 ≤ |x| → G x = 0 := fun x hx => hGsupp x (by linarith)
  -- step 1: off the plateau the two energies agree
  have hshift : ∀ t, (∫ u, (F u - F (u + t)) ^ 2) - gaugeJumpProfile P F t =
      (∫ u, (G u - G (u + t)) ^ 2) - gaugeJumpProfile P G t := by
    intro t
    have hint : ∀ {H : ℝ → ℝ}, Continuous H → HasCompactSupport H →
        Integrable (fun u => (H u - H (u + t)) ^ 2) ∧ Integrable (signedShiftJump P H t) := by
      intro H hH hHc
      have hcs : HasCompactSupport fun u => (H u - H (u + t)) ^ 2 :=
        ArithmeticCriticalityTheory.hasCompactSupport_sq
          (hHc.sub (hHc.comp_homeomorph (Homeomorph.addRight t)))
      have hcont : Continuous fun u => (H u - H (u + t)) ^ 2 := by fun_prop
      refine ⟨hcont.integrable_of_hasCompactSupport hcs, ?_⟩
      have hc : Continuous (signedShiftJump P H t) := by unfold signedShiftJump; fun_prop
      refine hc.integrable_of_hasCompactSupport ?_
      refine HasCompactSupport.intro hcs.isCompact fun u hu => ?_
      have h0 : (H u - H (u + t)) ^ 2 = 0 :=
        image_eq_zero_of_notMem_tsupport (f := fun u => (H u - H (u + t)) ^ 2) hu
      unfold signedShiftJump; rw [h0, mul_zero]
    obtain ⟨hF1, hF2⟩ := hint hF hFcs
    obtain ⟨hG1, hG2⟩ := hint hGc hGcs
    unfold gaugeJumpProfile
    rw [← integral_sub hF1 hF2, ← integral_sub hG1 hG2]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only
    rw [shiftSq_sub_signedShiftJump hFP, shiftSq_sub_signedShiftJump hGP, oddAbs_sq, oddAbs_sq]
  have hLF := integrableOn_archLevy_shiftSq hF hFcs hFL
  have hLG := integrableOn_archLevy_shiftSq hGc hGcs hGL
  have hJF := integrableOn_archLevy_gaugeJumpProfile hF hFcs hFL hPc hP0 hP1
  have hJG := integrableOn_archLevy_gaugeJumpProfile hGc hGcs hGL hPc hP0 hP1
  have hstep1 : levyEnergy F - levyEnergy G =
      (∫ t in Ioi (0 : ℝ), archLevyDensity t * gaugeJumpProfile P F t) -
        ∫ t in Ioi (0 : ℝ), archLevyDensity t * gaugeJumpProfile P G t := by
    unfold levyEnergy
    have e1 := integral_sub hLF hJF
    have e2 := integral_sub hLG hJG
    have e3 : (∫ t in Ioi (0 : ℝ), (archLevyDensity t * (∫ u, (F u - F (u + t)) ^ 2) -
        archLevyDensity t * gaugeJumpProfile P F t)) =
        ∫ t in Ioi (0 : ℝ), (archLevyDensity t * (∫ u, (G u - G (u + t)) ^ 2) -
          archLevyDensity t * gaugeJumpProfile P G t) :=
      setIntegral_congr_fun measurableSet_Ioi fun t _ => by
        rw [← mul_sub, ← mul_sub, hshift t]
    beta_reduce at e1 e2
    linarith
  -- step 2: AIP's exact fold
  obtain ⟨-, hfoldF⟩ := archJump_eq_two_mul_surplus_add_crossingPotential (B := r + 1) (K := K)
    hPc hF hPe hFo hP0 hP1 hPB hFB hFL hB0 hFP
  obtain ⟨-, hfoldG⟩ := archJump_eq_two_mul_surplus_add_crossingPotential (B := r + 1) (K := K)
    hPc hGc hPe hGo hP0 hP1 hPB hGB hGL hB0 hGP
  have hcross : (∫ x in Ioi (0 : ℝ), G x ^ 2 * crossingPotential P x) =
      ∫ x in Ioi (0 : ℝ), F x ^ 2 * crossingPotential P x :=
    setIntegral_congr_fun measurableSet_Ioi fun x _ => by simp only [G, oddAbs_sq]
  -- step 3: the surplus decreases under the contraction
  set μ := volume.restrict (Ioi (0 : ℝ))
  have hsurplus : ∀ {H : ℝ → ℝ}, Continuous H → (∀ a b, |H a - H b| ≤ K * |a - b|) →
      Integrable (fun z : ℝ × ℝ => (archLevyDensity z.2 - archLevyDensity (z.2 + 2 * z.1)) *
        signedShiftJump P H z.2 z.1) (μ.prod μ) := by
    intro H hH hHL
    have hIS := integrable_archLevy_mul_signedShiftJump_prod_everyAperture (B := r + 1)
      hPc hH hP0 hP1 hPB hHL hB0
    have hsw := hIS.swap
    have hmeas : Measurable fun z : ℝ × ℝ =>
        (archLevyDensity z.2 - archLevyDensity (z.2 + 2 * z.1)) * signedShiftJump P H z.2 z.1 := by
      have hc : Continuous fun z : ℝ × ℝ => signedShiftJump P H z.2 z.1 := by
        unfold signedShiftJump; fun_prop
      exact ((measurable_archLevyDensity.comp measurable_snd).sub
        (measurable_archLevyDensity.comp (measurable_snd.add
          (measurable_fst.const_mul 2)))).mul hc.measurable
    refine hsw.mono' hmeas.aestronglyMeasurable ?_
    rw [show μ.prod μ = (volume.prod volume).restrict (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) from
      Measure.prod_restrict (Ioi (0 : ℝ)) (Ioi (0 : ℝ))]
    refine ae_restrict_of_forall_mem (measurableSet_Ioi.prod measurableSet_Ioi) fun z hz => ?_
    obtain ⟨hx, hs⟩ := hz
    have hx0 : 0 < z.1 := hx
    have hs0 : 0 < z.2 := hs
    have hω1 := archLevyDensity_pos hs0
    have hω2 := archLevyDensity_pos (show 0 < z.2 + 2 * z.1 by linarith)
    have hanti : archLevyDensity (z.2 + 2 * z.1) ≤ archLevyDensity z.2 :=
      strictAntiOn_archLevyDensity.antitoneOn hs0
        (show (0 : ℝ) < z.2 + 2 * z.1 by linarith) (by linarith)
    have hsj : 0 ≤ signedShiftJump P H z.2 z.1 := by
      unfold signedShiftJump; exact mul_nonneg (mul_nonneg (hP0 _) (hP0 _)) (sq_nonneg _)
    simp only [Function.comp, Function.uncurry_apply_pair, Prod.swap]
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by linarith) hsj)]
    exact mul_le_mul_of_nonneg_right (by linarith) hsj
  have hSF := hsurplus hF hFL
  have hSG := hsurplus hGc hGL
  have hSle : surplusEnergy P G ≤ surplusEnergy P F := by
    unfold surplusEnergy
    rw [← integral_prod _ hSG, ← integral_prod _ hSF]
    refine integral_mono_ae hSG hSF ?_
    rw [show μ.prod μ = (volume.prod volume).restrict (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) from
      Measure.prod_restrict (Ioi (0 : ℝ)) (Ioi (0 : ℝ))]
    refine ae_restrict_of_forall_mem (measurableSet_Ioi.prod measurableSet_Ioi) fun z hz => ?_
    obtain ⟨hx, hs⟩ := hz
    have hx0 : 0 < z.1 := hx
    have hs0 : 0 < z.2 := hs
    have hanti : archLevyDensity (z.2 + 2 * z.1) ≤ archLevyDensity z.2 :=
      strictAntiOn_archLevyDensity.antitoneOn hs0
        (show (0 : ℝ) < z.2 + 2 * z.1 by linarith) (by linarith)
    have e1 : oddAbs F z.1 = |F z.1| := oddAbs_of_nonneg hx0.le
    have e2 : oddAbs F (z.1 + z.2) = |F (z.1 + z.2)| := oddAbs_of_nonneg (by linarith)
    simp only [signedShiftJump, G, e1, e2]
    have hsq : (|F z.1| - |F (z.1 + z.2)|) ^ 2 ≤ (F z.1 - F (z.1 + z.2)) ^ 2 := by
      have h := abs_abs_sub_abs_le (F z.1) (F (z.1 + z.2))
      calc (|F z.1| - |F (z.1 + z.2)|) ^ 2 = |(|F z.1| - |F (z.1 + z.2)|)| ^ 2 := (sq_abs _).symm
        _ ≤ |F z.1 - F (z.1 + z.2)| ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h 2
        _ = (F z.1 - F (z.1 + z.2)) ^ 2 := sq_abs _
    have hw : 0 ≤ (archLevyDensity z.2 - archLevyDensity (z.2 + 2 * z.1)) *
        (P z.1 * P (z.1 + z.2)) := mul_nonneg (by linarith) (mul_nonneg (hP0 _) (hP0 _))
    nlinarith [mul_le_mul_of_nonneg_left hsq hw]
  have hdiff : levyEnergy F - levyEnergy G = 2 * (surplusEnergy P F - surplusEnergy P G) := by
    rw [hstep1, hfoldF, hfoldG, hcross]; ring
  linarith

/-- **The frozen odd form is Markov.** With no prime acting, the contraction `F ↦ F̃` does not
raise the level-one Markov form minus the pole's negative square. -/
theorem frozenOddForm_oddAbs_le (hF : Continuous F) (hFo : ∀ x, F (-x) = -F x) {K r : ℝ}
    (hFL : ∀ a b, |F a - F b| ≤ K * |a - b|) (hr : 0 ≤ r) (hsupp : ∀ x, r < |x| → F x = 0) :
    markovForm 1 (oddAbs F) - sinhPairing (oddAbs F) ^ 2 / 2 ≤
      markovForm 1 F - sinhPairing F ^ 2 / 2 := by
  have hlev := levyEnergy_oddAbs_le hF hFo hFL hr hsupp
  have hsinh := sq_sinhPairing_le_oddAbs (F := F)
  have hsq : (∫ u, oddAbs F u ^ 2) = ∫ u, F u ^ 2 :=
    integral_congr_ae (Eventually.of_forall fun u => oddAbs_sq u)
  rw [markovForm_one, markovForm_one, levyJump_eq_levyEnergy (continuous_oddAbs hF hFo),
    levyJump_eq_levyEnergy hF, hsq]
  linarith

/-- **The kick is anti-Markov.** For an odd test supported in `[−a, a]`, `a ≤ ℓ`, and `w ≥ 0`,
`−2w c_F(ℓ) ≤ −2w c_{F̃}(ℓ)`. -/
theorem kick_le_kick_oddAbs (hF : Continuous F) (hFo : ∀ x, F (-x) = -F x) {a ℓ w : ℝ}
    (hsupp : ∀ x, a < |x| → F x = 0) (haℓ : a ≤ ℓ) (hw : 0 ≤ w) :
    -2 * w * (∫ y, F y * F (y + ℓ)) ≤ -2 * w * ∫ y, oddAbs F y * oddAbs F (y + ℓ) := by
  rw [integral_mul_shift_eq_neg_antidiagonal hFo, integral_mul_shift_eq_neg_antidiagonal
    (oddAbs_odd hFo)]
  have hGc := continuous_oddAbs hF hFo
  have hFcs : HasCompactSupport F :=
    HasCompactSupport.intro (isCompact_Icc (a := -a) (b := a)) fun x hx =>
      hsupp x (by by_contra h; exact hx (abs_le.mp (not_lt.mp h)))
  have hGcs : HasCompactSupport (oddAbs F) :=
    HasCompactSupport.intro (isCompact_Icc (a := -a) (b := a)) fun x hx =>
      oddAbs_eq_zero_iff.mpr (hsupp x (by by_contra h; exact hx (abs_le.mp (not_lt.mp h))))
  have hτ : Continuous fun s : ℝ => ℓ - s := continuous_const.sub continuous_id
  have hi1 : Integrable fun s => F s * F (ℓ - s) :=
    (hF.mul (hF.comp hτ)).integrable_of_hasCompactSupport hFcs.mul_right
  have hi2 : Integrable fun s => oddAbs F s * oddAbs F (ℓ - s) :=
    (hGc.mul (hGc.comp hτ)).integrable_of_hasCompactSupport hGcs.mul_right
  have hle : (∫ s, F s * F (ℓ - s)) ≤ ∫ s, oddAbs F s * oddAbs F (ℓ - s) := by
    refine integral_mono hi1 hi2 fun s => ?_
    simp only
    by_cases hs : 0 ≤ s ∧ s ≤ ℓ
    · rw [oddAbs_of_nonneg hs.1, oddAbs_of_nonneg (by linarith [hs.2]), ← abs_mul]
      exact le_abs_self _
    · have h0 : F s = 0 ∨ F (ℓ - s) = 0 := by
        rcases not_and_or.mp hs with h | h
        · have hs0 : s < 0 := not_le.mp h
          by_cases hsa : a < |s|
          · exact Or.inl (hsupp s hsa)
          · have hsa' : |s| ≤ a := not_lt.mp hsa
            have habs := abs_nonneg s
            refine Or.inr (hsupp _ ?_)
            rw [abs_of_pos (by linarith)]
            linarith
        · have hsl : ℓ < s := not_le.mp h
          exact Or.inl (hsupp s (by linarith [le_abs_self s]))
      rcases h0 with h | h
      · rw [h, oddAbs_eq_zero_iff.mpr h]; simp
      · rw [h, oddAbs_eq_zero_iff.mpr h]; simp
  nlinarith

/-- At the first prime stage the Markov form gains exactly the kick of `2`. -/
theorem markovForm_two_sub_one {g : ℝ → ℝ} (hg : Continuous g) (hgc : HasCompactSupport g) :
    markovForm 2 g - markovForm 1 g =
      -2 * primeJumpWeight 2 * ∫ u, g u * g (u + Real.log 2) := by
  have h1 : Finset.Icc 2 1 = (∅ : Finset ℕ) := by decide
  have h2 : Finset.Icc 2 2 = ({2} : Finset ℕ) := by decide
  have hsh := ArchimedeanAnomaly.integral_sub_shift_sq (x := Real.log 2) hgc hg
  have h0 : ArchimedeanAnomaly.autocorr g 0 = ∫ u, g u ^ 2 := by
    unfold ArchimedeanAnomaly.autocorr; congr 1; funext u; rw [add_zero, sq]
  have hc : ArchimedeanAnomaly.autocorr g (Real.log 2) = ∫ u, g u * g (u + Real.log 2) := rfl
  simp only [markovForm, creationPotential, primeJump, h1, h2, Finset.sum_empty,
    Finset.sum_singleton, Nat.cast_ofNat]
  rw [hsh, h0, hc]
  ring

/-- **Frustration of the first odd stage.** For an odd Lipschitz test supported in `[−a, a]`,
`a ≤ log 2`, the contraction `F ↦ F̃` lowers the frozen form `M₁ − ½⟨s, ·⟩²` and raises the kick
`M₂ − M₁` of the prime `2`. -/
theorem firstStage_frustration (hF : Continuous F) (hFo : ∀ x, F (-x) = -F x) {K a : ℝ}
    (hFL : ∀ a b, |F a - F b| ≤ K * |a - b|) (ha : 0 ≤ a) (ha2 : a ≤ Real.log 2)
    (hsupp : ∀ x, a < |x| → F x = 0) :
    markovForm 1 (oddAbs F) - sinhPairing (oddAbs F) ^ 2 / 2 ≤
        markovForm 1 F - sinhPairing F ^ 2 / 2 ∧
      markovForm 2 F - markovForm 1 F ≤ markovForm 2 (oddAbs F) - markovForm 1 (oddAbs F) := by
  have hFcs : HasCompactSupport F :=
    HasCompactSupport.intro (isCompact_Icc (a := -a) (b := a)) fun x hx =>
      hsupp x (by by_contra h; exact hx (abs_le.mp (not_lt.mp h)))
  have hGcs : HasCompactSupport (oddAbs F) :=
    HasCompactSupport.intro (isCompact_Icc (a := -a) (b := a)) fun x hx =>
      oddAbs_eq_zero_iff.mpr (hsupp x (by by_contra h; exact hx (abs_le.mp (not_lt.mp h))))
  refine ⟨frozenOddForm_oddAbs_le hF hFo hFL ha hsupp, ?_⟩
  rw [markovForm_two_sub_one hF hFcs, markovForm_two_sub_one (continuous_oddAbs hF hFo) hGcs]
  exact kick_le_kick_oddAbs hF hFo hsupp ha2 (primeJumpWeight_nonneg 2)

end GaloisForLFunctions.SignedWindowCriticality

end
