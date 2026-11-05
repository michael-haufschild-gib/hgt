import GaloisForLFunctions.CriticalHardyTheoryOfTheWindowCone.TheMarginLawOfTheWindowCone
import GaloisForLFunctions.RHTower.WeilPoleWeightBelowOneEmpty
import GaloisForLFunctions.RHTower.BlindSymbolSlackPrimePowerPeriodization
import GaloisForLFunctions.RHTower.WeilPositivityPrimeBlindDuality
import GaloisForLFunctions.RHTower.WeilMarkovArchimedeanWideTestNegativity
import GaloisForLFunctions.RHTower.WeilPositivityTwistObstruction
import GaloisForLFunctions.RHTower.WeilArchReLevyPoleForm
import GaloisForLFunctions.RHTower.BlindDecayClassPoleCertificate
import GaloisForLFunctions.RHTower.WeilBlindPoleSignLaw

/-!
# The datum of the window cone: pole and conductor

Weil's form of `ζ` has one Gamma factor, one pole and conductor one. Replace the residue by a pole weight `β`
and the conductor by `q = e^s`: the archimedean symbol becomes `Ω + s`, the pole counts `β` times, and the
energy of a test is (`datumEnergy`)

  `E_{β,s,λ}(f) = W_λ(f) + (β − 1) Re P(k_f) + s ‖f‖²`,

with cones `𝒜_{β,s}(c)` (`datumCone`). The datum `(1, 0)` is the arithmetic one. This module classifies the
datum, for **all** weights, at finite windows.

* **The conductor is the margin** (`mem_datumCone_one_iff`, `datumCone_one_nonempty_iff`). At `β = 1`,
  `λ ∈ 𝒜_{1,s}(c)` iff `λ` has margin `−s`. So `−λ*(c)` is the critical log-conductor of the window.
* **Conductor one is exactly critical.** Below it the cones empty at a finite window, for all weights
  (`exists_datumCone_one_eq_empty`), since the margin law forbids a margin `−s > 0`. At it, nonemptiness on
  every window is RH (`riemannHypothesis_iff_forall_datumCone_one_zero_nonempty`). Above it every cone point
  of `𝒜(c)` carries a ball (`add_mem_datumCone_one`).
* **High conductor without pole has a fat cone** (`forall_zero_mem_datumCone_zero_iff`,
  `exists_ne_mem_forall_datumCone_zero`). `0 ∈ 𝒜_{0,s}(c)` for all `c` iff `s ≥ log π − ψ(¼)`, and past
  the threshold every window's cone contains one fixed ball. So the point cone of `ζ` is a property of the
  datum, not of the weights.
-/

open MeasureTheory Filter Topology Set
open scoped Nat Real ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.CriticalHardyTheoryOfTheWindowCone

open _root_.RHTower _root_.RHTower.WeilSpectral _root_.RHTower.WeilOneSided
open _root_.RHTower.WeilPoleWeight _root_.RHTower.ResonatorProfile _root_.Zeta23

local notation "𝔽" => xiShiftedGammaTest

/-! ### The datum energy -/

/-- The energy of a test for pole weight `β` and log-conductor `s`. -/
def datumEnergy (β s : ℝ) (lam : ℕ → ℝ) (f : ℝ → ℂ) : ℝ :=
  (weilPoleWeightFunctional β lam (EF.weilTest f f)).re + s * ∫ u, ‖f u‖ ^ 2

/-- The window cone of the datum `(β, s)`. -/
def datumCone (β s c : ℝ) : Set (ℕ → ℝ) :=
  {lam | ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-c) c → 0 ≤ datumEnergy β s lam f}

theorem datumEnergy_eq (β s : ℝ) (lam : ℕ → ℝ) (f : ℝ → ℂ) :
    datumEnergy β s lam f = (weilFullFunctional lam (EF.weilTest f f)).re +
      (β - 1) * (weilPoleTerm (EF.weilTest f f)).re + s * ∫ u, ‖f u‖ ^ 2 := by
  unfold datumEnergy weilPoleWeightFunctional weilPoleTerm
  rw [Complex.add_re, show ((β : ℂ) - 1) = ((β - 1 : ℝ) : ℂ) by push_cast; ring,
    Complex.re_ofReal_mul]

theorem datumCone_mono_conductor {β s s' c : ℝ} (h : s ≤ s') :
    datumCone β s c ⊆ datumCone β s' c := fun _ hlam f hf hfs => by
  have h1 := hlam f hf hfs
  unfold datumEnergy at h1 ⊢
  have h2 := mul_le_mul_of_nonneg_right h
    (integral_nonneg fun u => by positivity : (0 : ℝ) ≤ ∫ u, ‖f u‖ ^ 2)
  linarith

theorem datumCone_anti {β s c c' : ℝ} (h : c' ≤ c) : datumCone β s c ⊆ datumCone β s c' :=
  fun _ hlam f hf hfs => hlam f hf (hfs.trans (Icc_subset_Icc (by linarith) h))

/-! ### The conductor is the margin -/

/-- At pole weight one, the conductor is exactly a margin. -/
theorem mem_datumCone_one_iff {s c : ℝ} {lam : ℕ → ℝ} :
    lam ∈ datumCone 1 s c ↔ HasMargin lam c (-s) := by
  refine forall_congr' fun f => forall_congr' fun _ => forall_congr' fun _ => ?_
  rw [datumEnergy_eq, sub_self, zero_mul, add_zero]
  constructor <;> intro h <;> linarith

/-- The window's critical log-conductor is `−λ*(c)`. -/
theorem datumCone_one_nonempty_iff {s c : ℝ} (hc : 3 / 10 ≤ c) :
    (datumCone 1 s c).Nonempty ↔ -s ≤ bestMargin c := by
  rw [← exists_hasMargin_iff_le_bestMargin hc]
  exact exists_congr fun _ => mem_datumCone_one_iff

/-- **Below conductor one the cones are empty from a finite window on**, for all weights. -/
theorem exists_datumCone_one_eq_empty {s : ℝ} (hs : s < 0) :
    ∃ c₀ : ℝ, ∀ c, c₀ ≤ c → datumCone 1 s c = ∅ := by
  obtain ⟨K, hK, h⟩ := exists_margin_ceiling
  have hlim : Tendsto (fun c => K * marginCeiling c) atTop (𝓝 0) := by
    simpa using tendsto_marginCeiling.const_mul K
  obtain ⟨c₁, hc₁⟩ := eventually_atTop.mp (hlim.eventually (gt_mem_nhds (neg_pos.mpr hs)))
  refine ⟨max c₁ 3, fun c hc => Set.eq_empty_of_forall_notMem fun lam hlam => ?_⟩
  have h1 := h c (-s) lam ((le_max_right _ _).trans hc) (by linarith)
    (mem_datumCone_one_iff.mp hlam)
  have h2 := hc₁ c ((le_max_left _ _).trans hc)
  linarith

/-- **At conductor one, nonemptiness on every window is RH.** -/
theorem riemannHypothesis_iff_forall_datumCone_one_zero_nonempty :
    RiemannHypothesis ↔ ∀ c, 3 / 10 ≤ c → (datumCone 1 0 c).Nonempty := by
  rw [riemannHypothesis_iff_forall_nonneg_levelValueAt]
  refine forall_congr' fun c => imp_congr_right fun hc => ?_
  rw [datumCone_one_nonempty_iff hc, neg_zero]
  rfl

/-- **Above conductor one every cone point carries a ball.** -/
theorem add_mem_datumCone_one {lam v : ℕ → ℝ} {t : Finset ℕ} {s c : ℝ}
    (hv : ∀ n, n ∉ t → v n = 0) (hsize : perturbationSize t v ≤ s)
    (h : WeilPositiveFullUpTo lam c) : (fun n => lam n + v n) ∈ datumCone 1 s c := by
  rw [mem_datumCone_one_iff]
  have h0 : HasMargin lam c 0 := fun f hf hfs => by
    rw [zero_mul]
    exact h f hf hfs
  exact (hasMargin_add hv h0).mono (by linarith)

/-! ### High conductor without a pole -/

theorem re_weilFullFunctional_zero_eq (g : WeilTestFn) :
    (weilFullFunctional (fun _ => 0) (EF.weilTest g.1 g.1)).re =
      weilArchRe (EF.weilTest g.1 g.1) := by
  rw [re_weilFullFunctional_eq]
  simp [Finsupp.linearCombination_apply]

/-- With no pole and no weights the energy is at least `(Ω(0) + s)‖f‖²`. -/
theorem gammaFloor_mul_le_datumEnergy (s : ℝ) {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) :
    (EF.gammaBracket 0 + s) * ∫ u, ‖f u‖ ^ 2 ≤ datumEnergy 0 s (fun _ => 0) f := by
  set g : WeilTestFn := ⟨f, hf, hfc⟩
  have h1 := pole_add_anomaly_le_weilArchRe' g
  have h2 := re_weilFullFunctional_zero_eq g
  rw [datumEnergy_eq]
  change (EF.gammaBracket 0 + s) * ∫ u, ‖g.1 u‖ ^ 2 ≤
    (weilFullFunctional (fun _ => 0) (EF.weilTest g.1 g.1)).re +
      (0 - 1) * (weilPoleTerm (EF.weilTest g.1 g.1)).re + s * ∫ u, ‖g.1 u‖ ^ 2
  rw [h2]
  nlinarith

/-- **A ball in the pole-free cone at every window.** -/
theorem add_mem_datumCone_zero {v : ℕ → ℝ} {t : Finset ℕ} {s c : ℝ}
    (hv : ∀ n, n ∉ t → v n = 0) (hsize : perturbationSize t v ≤ s + EF.gammaBracket 0) :
    v ∈ datumCone 0 s c := by
  intro f hf hfs
  have hfc := hasCompactSupport_of_tsupport_subset hfs
  have h1 := re_weilFullFunctional_add_ge (lam := fun _ => 0) hv hf hfc
  have hfun : (fun n => (fun _ : ℕ => (0 : ℝ)) n + v n) = v := funext fun n => by simp
  rw [hfun] at h1
  have h2 := gammaFloor_mul_le_datumEnergy s hf hfc
  rw [datumEnergy_eq] at h2 ⊢
  have hM : 0 ≤ ∫ u, ‖f u‖ ^ 2 := integral_nonneg fun _ => by positivity
  have h3 := mul_le_mul_of_nonneg_right hsize hM
  nlinarith

/-- **Past the threshold the cone of the pole-free datum is not a point**, at any window. -/
theorem exists_ne_mem_forall_datumCone_zero {s : ℝ} (hs : -EF.gammaBracket 0 < s) :
    ∃ lam₁ lam₂ : ℕ → ℝ, lam₁ ≠ lam₂ ∧ ∀ c, lam₁ ∈ datumCone 0 s c ∧ lam₂ ∈ datumCone 0 s c := by
  have hd : 0 < s + EF.gammaBracket 0 := by linarith
  have hq : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  set τ : ℝ := (s + EF.gammaBracket 0) * Real.sqrt 2 / 2 with hτ
  have hτ0 : 0 < τ := by positivity
  set v : ℕ → ℝ := fun n => if n = 2 then τ else 0 with hv
  refine ⟨fun _ => 0, v, fun h => ?_, fun c => ⟨?_, ?_⟩⟩
  · have := congrFun h 2
    simp only [hv, if_true] at this
    linarith
  · exact add_mem_datumCone_zero (t := ∅) (fun _ _ => rfl) (by simp [perturbationSize]; linarith)
  · refine add_mem_datumCone_zero (t := {2}) (fun n hn => ?_) ?_
    · simp only [Finset.mem_singleton] at hn
      simp [hv, hn]
    · unfold perturbationSize
      rw [Finset.sum_singleton, if_pos le_rfl]
      simp only [hv, if_true, abs_of_pos hτ0]
      push_cast
      rw [hτ]
      apply le_of_eq
      field_simp

/-- The dilated bump `φ(u/S)`. -/
def wideBump (S u : ℝ) : ℝ :=
  (⟨1, 2, one_pos, by norm_num⟩ : ContDiffBump (0 : ℝ)) (u / S)

theorem contDiff_wideBump (S : ℝ) : ContDiff ℝ 2 (wideBump S) :=
  (⟨1, 2, one_pos, by norm_num⟩ : ContDiffBump (0 : ℝ)).contDiff.comp
    (contDiff_id.div_const S)

theorem wideBump_eq_zero {S u : ℝ} (hS : 0 < S) (hu : 2 * S ≤ |u|) : wideBump S u = 0 := by
  refine (⟨1, 2, one_pos, by norm_num⟩ : ContDiffBump (0 : ℝ)).zero_of_le_dist ?_
  rw [Real.dist_eq, sub_zero, abs_div, abs_of_pos hS, le_div_iff₀ hS]
  exact hu

theorem hasCompactSupport_wideBump {S : ℝ} (hS : 0 < S) : HasCompactSupport (wideBump S) :=
  HasCompactSupport.intro (isCompact_Icc (a := -(2 * S)) (b := 2 * S)) fun u hu => by
    refine wideBump_eq_zero hS ?_
    by_contra h
    exact hu (abs_le.mp (not_le.mp h).le)

theorem tsupport_wideBump_subset {S : ℝ} (hS : 0 < S) :
    tsupport (fun u => (wideBump S u : ℂ)) ⊆ Icc (-(2 * S)) (2 * S) := by
  refine closure_minimal (fun u hu => ?_) isClosed_Icc
  by_contra h
  apply hu
  have h1 : 2 * S ≤ |u| := by
    by_contra h2
    exact h (abs_le.mp (not_le.mp h2).le)
  simp [wideBump_eq_zero hS h1]

theorem integral_wideBump_sq {S : ℝ} (hS : 0 < S) :
    ∫ u, wideBump S u ^ 2 = S * ∫ u, wideBump 1 u ^ 2 := by
  have h := integral_comp_div (fun x : ℝ => wideBump 1 x ^ 2) S
  simp only [abs_of_pos hS, smul_eq_mul] at h
  have e : ∀ u, wideBump S u = wideBump 1 (u / S) := fun u => by simp [wideBump]
  simp_rw [e]
  exact h

theorem integral_wideBump_one_sq_pos : 0 < ∫ u, wideBump 1 u ^ 2 := by
  have hc : Continuous fun u => wideBump 1 u ^ 2 := (contDiff_wideBump 1).continuous.pow 2
  have hcs : HasCompactSupport fun u => wideBump 1 u ^ 2 :=
    (hasCompactSupport_wideBump one_pos).comp_left (g := fun z : ℝ => z ^ 2) (by norm_num)
  refine hc.integral_pos_of_hasCompactSupport_nonneg_nonzero hcs (fun _ => sq_nonneg _) (x := 0) ?_
  have h0 : wideBump 1 0 = 1 := by
    unfold wideBump
    exact (⟨1, 2, one_pos, by norm_num⟩ : ContDiffBump (0 : ℝ)).one_of_mem_closedBall (by simp)
  rw [h0]
  norm_num

theorem fourierH1_wideBump {S : ℝ} (hS : 0 < S) : fourierH1 (wideBump S) = S⁻¹ * fourierH1 (wideBump 1) := by
  unfold fourierH1
  have hft : ∀ r : ℝ, ‖paperFT (fun u => (wideBump S u : ℂ)) r‖ ^ 2 =
      S ^ 2 * ‖paperFT (fun u => (wideBump 1 u : ℂ)) ((S * r : ℝ) : ℂ)‖ ^ 2 := fun r => by
    have e : (fun u => ((wideBump S u : ℝ) : ℂ)) = fun u => ((wideBump 1 (u / S) : ℝ) : ℂ) := by
      funext u
      simp [wideBump]
    rw [e, paperFT_comp_div (f := fun u => ((wideBump 1 u : ℝ) : ℂ)) hS, norm_mul, mul_pow,
      Complex.norm_real, Real.norm_eq_abs, sq_abs]
    push_cast
    rfl
  have hsub := Measure.integral_comp_mul_left
    (fun ρ : ℝ => ρ ^ 2 * ‖paperFT (fun u => (wideBump 1 u : ℂ)) (ρ : ℂ)‖ ^ 2) S
  rw [abs_of_pos (inv_pos.mpr hS), smul_eq_mul] at hsub
  have hint : ∫ r : ℝ, r ^ 2 * ‖paperFT (fun u => (wideBump S u : ℂ)) r‖ ^ 2 =
      S⁻¹ * ∫ ρ : ℝ, ρ ^ 2 * ‖paperFT (fun u => (wideBump 1 u : ℂ)) (ρ : ℂ)‖ ^ 2 := by
    rw [← hsub]
    refine integral_congr_ae (Eventually.of_forall fun r => ?_)
    simp only
    rw [hft r]
    ring
  rw [hint]
  ring

/-- The pole-free energy of a real test with no weights is the archimedean form plus the conductor. -/
theorem datumEnergy_zero_ofReal (s : ℝ) {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) :
    datumEnergy 0 s (fun _ => 0) (fun u => (g u : ℂ)) = archForm g + s * ∫ u, g u ^ 2 := by
  have hG : ContDiff ℝ 2 (fun u => (g u : ℂ)) := Complex.ofRealCLM.contDiff.comp hg
  have hGc : HasCompactSupport (fun u => (g u : ℂ)) := hgc.comp_left Complex.ofReal_zero
  set t : WeilTestFn := ⟨fun u => (g u : ℂ), hG, hGc⟩ with ht
  have h1 := re_weilFullFunctional_zero_eq t
  have h2 := BlindPrimePowerSlack.weilArchRe_sub_pole_eq t
  have hm : ∫ u, ‖(g u : ℂ)‖ ^ 2 = ∫ u, g u ^ 2 := by
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    simp [Complex.norm_real, sq_abs]
  rw [datumEnergy_eq, hm]
  change (weilFullFunctional (fun _ => 0) (EF.weilTest t.1 t.1)).re +
    (0 - 1) * (weilPoleTerm (EF.weilTest t.1 t.1)).re + s * ∫ u, g u ^ 2 = _
  rw [h1]
  unfold archForm
  have h3 : weilArchRe (EF.weilTest t.1 t.1) - (weilPoleTerm (EF.weilTest t.1 t.1)).re =
      1 / (2 * Real.pi) * ∫ r : ℝ, ‖paperFT (fun u => (g u : ℂ)) r‖ ^ 2 * EF.gammaBracket r := h2
  linarith

/-- **The sharp threshold of the zero weights.** The zero weights lie in `𝒜_{0,s}(c)` for every `c` iff
`s ≥ −Ω(0) = log π − ψ(¼)`. -/
theorem forall_zero_mem_datumCone_zero_iff {s : ℝ} :
    (∀ c, (fun _ => (0 : ℝ)) ∈ datumCone 0 s c) ↔ -EF.gammaBracket 0 ≤ s := by
  constructor
  · intro h
    by_contra hlt
    rw [not_le] at hlt
    set δ : ℝ := -(EF.gammaBracket 0 + s) with hδ
    have hδ0 : 0 < δ := by rw [hδ]; linarith
    set A : ℝ := ∫ u, wideBump 1 u ^ 2 with hA
    have hA0 : 0 < A := integral_wideBump_one_sq_pos
    set B : ℝ := fourierH1 (wideBump 1) with hB
    have hB0 : 0 ≤ B := fourierH1_nonneg _
    have hm := levySecondMoment_nonneg
    set S : ℝ := 1 + levySecondMoment * B / (δ * A) with hS
    have hq : 0 ≤ levySecondMoment * B / (δ * A) := by positivity
    have hS1 : 1 ≤ S := by rw [hS]; linarith
    have hS0 : 0 < S := by linarith
    have hge := h (2 * S) (fun u => (wideBump S u : ℂ))
      (Complex.ofRealCLM.contDiff.comp (contDiff_wideBump S)) (tsupport_wideBump_subset hS0)
    rw [datumEnergy_zero_ofReal s (contDiff_wideBump S) (hasCompactSupport_wideBump hS0)] at hge
    have hle := archForm_le (contDiff_wideBump S) (hasCompactSupport_wideBump hS0)
    rw [integral_wideBump_sq hS0, fourierH1_wideBump hS0,
      ← WeilLevyPole.gammaBracket_eq_two_mul_gammaHardyPhaseRate] at hle
    rw [integral_wideBump_sq hS0] at hge
    have hneg : (EF.gammaBracket 0 + s) * (S * A) + levySecondMoment * (S⁻¹ * B) < 0 := by
      have hSinv : S⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hS1
      have hbig : levySecondMoment * B < S * (δ * A) := by
        have h1 : levySecondMoment * B / (δ * A) < S := by rw [hS]; linarith
        rwa [div_lt_iff₀ (by positivity)] at h1
      have h2 : levySecondMoment * (S⁻¹ * B) ≤ levySecondMoment * B := by
        have : S⁻¹ * B ≤ 1 * B := mul_le_mul_of_nonneg_right hSinv hB0
        have := mul_le_mul_of_nonneg_left this hm
        linarith
      have e : (EF.gammaBracket 0 + s) * (S * A) = -(S * (δ * A)) := by
        rw [hδ]
        ring
      rw [e]
      linarith
    nlinarith
  · intro hs c f hf hfs
    refine le_trans ?_ (gammaFloor_mul_le_datumEnergy s hf (hasCompactSupport_of_tsupport_subset hfs))
    exact mul_nonneg (by linarith) (integral_nonneg fun _ => by positivity)

end GaloisForLFunctions.CriticalHardyTheoryOfTheWindowCone
