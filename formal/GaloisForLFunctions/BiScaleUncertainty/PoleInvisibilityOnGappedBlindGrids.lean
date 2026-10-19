import GaloisForLFunctions.RHTower.ArchimedeanPoleValueFunction
import GaloisForLFunctions.BiScaleUncertainty.OddSectorAndPrimitiveHyperplaneBiScaleSynthesis
import GaloisForLFunctions.BiScaleUncertainty.DistantCopyPolarEnforcement

/-!
# The pole constraint is invisible on gapped blind grids

`RHTower.WeilOneSided.riemannHypothesis_iff_zeroPoleBlindPositive` states RH as the positivity of
the archimedean symbol on every nonnegative combination of Weil tests that is blind at every
integer node `log n`, `n ≥ 2`, and has total pole mass zero. Without the pole constraint this
positivity fails. This module shows that blindness on a *sparse* set of nodes cannot replace
the full integer grid.

Call a node set `𝒩` *gapped* if arbitrarily far out there is a location `T` at logarithmic
distance at least `1/5` from every `log n`, `n ∈ 𝒩`. The distant pair
`g_{σ,T}(u) = b(u) - σ b(u - T)` of the corpus bump `b` (support `|u| < 1/10`) is then blind on
`𝒩`, its pole term is `2(1 - σe^{-T/2})(1 - σe^{T/2}) m₊ m₋` with `m_± = ∫ b e^{±u/2} > 0`, of
either sign and of size `≍ e^{T/2}`, while its archimedean part without the pole,
`γ(0) h(0) + 𝒥(g)`, stays bounded uniformly in `T` (the distant copy only touches the Lévy
kernel through an exponentially small tail).

* **Pole mass is free** (`exists_blindOn_poleMass_eq_abs_archOnly_le`): every prescribed pole mass
  is carried by an `𝒩`-blind combination of arbitrarily small archimedean cost.
* **Pole invisibility** (`exists_blindOn_poleMass_zero_archOnly_close`): every `𝒩`-blind
  combination is approximated in archimedean energy by `𝒩`-blind combinations of zero pole mass.
* **No-go** (`not_zeroPoleBlindPositiveOn_of_gapped`): zero-pole positivity fails on every gapped
  node set; in particular on the powers of any single integer `q ≥ 2`.

On the full integer grid the nodes are `e^{-T}`-dense at scale `T`, there are no gaps, and the
same positivity is equivalent to RH (`riemannHypothesis_iff_zeroPoleBlindPositiveOn_all`). The
pole constraint can only act through the exponential density of the integer logarithms.
-/

open MeasureTheory Set Filter Topology Complex Finsupp
open Zeta23
open RHTower RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm RHTower.WeilMarkovPole
open RHTower.WeilOneSided

namespace GaloisForLFunctions.BiScaleUncertainty

noncomputable section
set_option autoImplicit false

/-! ### 1. Blindness on a node set -/

/-- A combination is blind on `𝒩` if its node vector vanishes at every node of `𝒩`. -/
def BlindOn (𝒩 : Set ℕ) (c : WeilTestFn →₀ ℝ) : Prop :=
  ∀ j : LogIndex, (j : ℕ) ∈ 𝒩 → nodeVector c j = 0

/-- Zero-pole positivity with blindness imposed only on `𝒩`. -/
def ZeroPoleBlindPositiveOn (𝒩 : Set ℕ) : Prop :=
  ∀ c : WeilTestFn →₀ ℝ, (∀ f, 0 ≤ c f) → BlindOn 𝒩 c → nodePoleMass c = 0 →
    0 ≤ nodeArchEnergy c

/-- `𝒩` has arbitrarily far logarithmic gaps of half-width `1/5`. -/
def GappedNodeSet (𝒩 : Set ℕ) : Prop :=
  ∀ R : ℝ, ∃ T : ℝ, R ≤ T ∧ ∀ n ∈ 𝒩, 2 ≤ n → 1 / 5 ≤ |Real.log n - T|

/-- On the full integer grid, zero-pole positivity is exactly RH. -/
theorem riemannHypothesis_iff_zeroPoleBlindPositiveOn_all :
    RiemannHypothesis ↔ ZeroPoleBlindPositiveOn {n | 2 ≤ n} := by
  rw [riemannHypothesis_iff_zeroPoleBlindPositive]
  constructor
  · intro h c hc hb hp
    exact h c hc (Finsupp.ext fun j => hb j j.2) hp
  · intro h c hc hv hp
    exact h c hc (fun j _ => by rw [hv]; rfl) hp

/-! ### 2. The distant pair of the corpus bump -/

/-- The corpus bump `b`, supported in `|u| < 1/10`. -/
abbrev pairBump : ℝ → ℝ := fun u => adjBump u

theorem autocorr_pairBump_eq_zero {x : ℝ} (hx : 1 / 5 ≤ |x|) : autocorr pairBump x = 0 := by
  unfold autocorr
  have h0 : ∀ u, pairBump u * pairBump (u + x) = 0 := by
    intro u
    by_cases hu : 1 / 10 ≤ |u|
    · simp [pairBump, adjBump_eq_zero hu]
    · have hux : 1 / 10 ≤ |u + x| := by
        have := abs_sub_abs_le_abs_sub x (-u)
        rw [sub_neg_eq_add, add_comm, abs_neg] at this
        linarith
      simp [pairBump, adjBump_eq_zero hux]
  simp [h0]

theorem contDiff_pairBump : ContDiff ℝ 2 pairBump := adjBump.contDiff

theorem hasCompactSupport_pairBump : HasCompactSupport pairBump := adjBump.hasCompactSupport

/-- The distant pair `b(u) - σ b(u - T)`. -/
abbrev distantPair (σ T : ℝ) : ℝ → ℝ := subtractCopy pairBump σ T

theorem contDiff_distantPair (σ T : ℝ) : ContDiff ℝ 2 (distantPair σ T) :=
  contDiff_subtractCopy contDiff_pairBump σ T

theorem hasCompactSupport_distantPair (σ T : ℝ) : HasCompactSupport (distantPair σ T) :=
  hasCompactSupport_subtractCopy hasCompactSupport_pairBump σ T

/-- The distant pair as a corpus Weil test. -/
def distantPairTest (σ T : ℝ) : WeilTestFn :=
  ⟨fun u => ((distantPair σ T u : ℝ) : ℂ), Complex.ofRealCLM.contDiff.comp (contDiff_distantPair σ T),
    (hasCompactSupport_distantPair σ T).comp_left Complex.ofReal_zero⟩

/-- **Blindness in a gap.** If `log n` is at distance at least `1/5` from `T ≥ 1`, the distant
pair is blind at `n`. -/
theorem logValue_distantPair_eq_zero (σ : ℝ) {T : ℝ} (hT : 1 ≤ T) {n : ℕ} (hn : 2 ≤ n)
    (hgap : 1 / 5 ≤ |Real.log n - T|) :
    logValue (distantPairTest σ T).1 n = 0 := by
  have hlog2 : (1 : ℝ) / 5 < Real.log 2 := by
    have := Real.log_two_gt_d9; linarith
  have hlogn : Real.log 2 ≤ Real.log n := Real.log_le_log two_pos (by exact_mod_cast hn)
  have hval : autocorr (distantPair σ T) (Real.log n) = 0 := by
    rw [autocorr_subtractCopy contDiff_pairBump.continuous hasCompactSupport_pairBump]
    rw [autocorr_pairBump_eq_zero (x := Real.log n) (by rw [abs_of_pos (by linarith)]; linarith),
      autocorr_pairBump_eq_zero hgap,
      autocorr_pairBump_eq_zero (x := Real.log n + T)
        (by rw [abs_of_pos (by linarith)]; linarith)]
    ring
  have h1 := RHTower.AutocorrelationKrein.weilTest_eq (distantPair σ T) (Real.log n)
  have h2 := RHTower.AutocorrelationKrein.weilTest_eq (distantPair σ T) (-Real.log n)
  rw [autocorr_neg, hval] at h2
  rw [hval] at h1
  change (EF.weilTest (fun u => ((distantPair σ T u : ℝ) : ℂ)) (fun u => ((distantPair σ T u : ℝ) : ℂ))
    (Real.log n) + EF.weilTest (fun u => ((distantPair σ T u : ℝ) : ℂ))
      (fun u => ((distantPair σ T u : ℝ) : ℂ)) (-Real.log n)).re / Real.sqrt n = 0
  rw [h1, h2]
  simp

/-! ### 3. Pole term and archimedean part of the distant pair -/

/-- The half-exponential moments `m_s = ∫ b(u) e^{s u} du`. -/
def pairMoment (s : ℝ) : ℝ := ∫ u, pairBump u * Real.exp (s * u)

theorem pairMoment_pos (s : ℝ) : 0 < pairMoment s := by
  have hc : Continuous fun t => pairBump t * Real.exp (s * t) :=
    adjBump.continuous.mul (by fun_prop)
  refine hc.integral_pos_of_hasCompactSupport_nonneg_nonzero
    (hasCompactSupport_pairBump.mul_right) (fun t => mul_nonneg adjBump.nonneg (Real.exp_pos _).le)
    (x := 0) ?_
  rw [show pairBump 0 = adjBump 0 from rfl,
    adjBump.one_of_mem_closedBall (Metric.mem_closedBall_self adjBump.rIn_pos.le)]
  simp

/-- The pole term of a real source is twice the product of its two half-exponential moments. -/
theorem re_weilPoleTerm_ofReal_eq_moment_mul {f : ℝ → ℝ} (hf : Continuous f)
    (hfc : HasCompactSupport f) :
    (weilPoleTerm (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ)))).re =
      2 * ((∫ u, f u * Real.exp ((1 / 2) * u)) * ∫ u, f u * Real.exp ((-(1 / 2)) * u)) := by
  rw [re_weilPoleTerm_ofReal_eq_cosh_sq_sub_sinh_sq hf hfc]
  have hp : Integrable (fun u => f u * Real.exp ((1 / 2) * u)) :=
    (hf.mul (by fun_prop)).integrable_of_hasCompactSupport hfc.mul_right
  have hm : Integrable (fun u => f u * Real.exp ((-(1 / 2)) * u)) :=
    (hf.mul (by fun_prop)).integrable_of_hasCompactSupport hfc.mul_right
  have hc : (∫ u, f u * Real.cosh (u / 2)) =
      ((∫ u, f u * Real.exp ((1 / 2) * u)) + ∫ u, f u * Real.exp ((-(1 / 2)) * u)) / 2 := by
    rw [← integral_add hp hm, ← integral_div]
    refine integral_congr_ae (ae_of_all _ fun u => ?_)
    simp only [Real.cosh_eq]
    rw [show u / 2 = 1 / 2 * u by ring, show -(1 / 2 * u) = -(1 / 2) * u by ring]
    ring
  have hs : (∫ u, f u * Real.sinh (u / 2)) =
      ((∫ u, f u * Real.exp ((1 / 2) * u)) - ∫ u, f u * Real.exp ((-(1 / 2)) * u)) / 2 := by
    rw [← integral_sub hp hm, ← integral_div]
    refine integral_congr_ae (ae_of_all _ fun u => ?_)
    simp only [Real.sinh_eq]
    rw [show u / 2 = 1 / 2 * u by ring, show -(1 / 2 * u) = -(1 / 2) * u by ring]
    ring
  rw [hc, hs]
  ring

/-- **Pole term of the distant pair:** `2(1 - σe^{T/2})(1 - σe^{-T/2}) m₊ m₋`. -/
theorem pole_distantPairTest (σ T : ℝ) :
    (weilPoleTerm (EF.weilTest (distantPairTest σ T).1 (distantPairTest σ T).1)).re =
      2 * ((1 - σ * Real.exp ((1 / 2) * T)) * (1 - σ * Real.exp ((-(1 / 2)) * T))) *
        (pairMoment (1 / 2) * pairMoment (-(1 / 2))) := by
  change (weilPoleTerm (EF.weilTest (fun u => ((distantPair σ T u : ℝ) : ℂ))
    (fun u => ((distantPair σ T u : ℝ) : ℂ)))).re = _
  rw [re_weilPoleTerm_ofReal_eq_moment_mul (contDiff_distantPair σ T).continuous
    (hasCompactSupport_distantPair σ T),
    integral_subtractCopy_mul_exp contDiff_pairBump.continuous hasCompactSupport_pairBump,
    integral_subtractCopy_mul_exp contDiff_pairBump.continuous hasCompactSupport_pairBump]
  unfold pairMoment
  ring

/-- The archimedean part without the pole of the distant pair is bounded uniformly in `T ≥ 2`. -/
def pairArchBound : ℝ :=
  2 * |EF.gammaBracket 0| * autocorr pairBump 0 + 2 * biScaleLevyEnergy pairBump +
    2 / (1 - Real.exp (-2)) * ∫ x, |autocorr pairBump x|

theorem abs_archOnly_distantPairTest_le {σ T : ℝ} (hσ : σ ^ 2 = 1) (hT : 2 ≤ T) :
    |WeilOneSided.weilArchRe (EF.weilTest (distantPairTest σ T).1 (distantPairTest σ T).1) -
        (weilPoleTerm (EF.weilTest (distantPairTest σ T).1 (distantPairTest σ T).1)).re| ≤
      pairArchBound := by
  have hsupp : ∀ x, 1 / 5 < |x| → autocorr pairBump x = 0 :=
    fun x hx => autocorr_pairBump_eq_zero hx.le
  have hT' : (1 : ℝ) / 5 + 1 ≤ T := by linarith
  change |WeilOneSided.weilArchRe (EF.weilTest (fun u => ((distantPair σ T u : ℝ) : ℂ))
      (fun u => ((distantPair σ T u : ℝ) : ℂ))) -
    (weilPoleTerm (EF.weilTest (fun u => ((distantPair σ T u : ℝ) : ℂ))
      (fun u => ((distantPair σ T u : ℝ) : ℂ)))).re| ≤ _
  rw [weilArchRe_ofReal_eq_pole_add_gamma_add_biScaleLevyEnergy (contDiff_distantPair σ T)
    (hasCompactSupport_distantPair σ T),
    show ∀ a b c : ℝ, a + b + c - a = b + c from fun a b c => by ring,
    biScaleLevyEnergy_subtractCopy contDiff_pairBump hasCompactSupport_pairBump hsupp hT' σ]
  have h0 : autocorr (distantPair σ T) 0 = 2 * autocorr pairBump 0 := by
    rw [autocorr_subtractCopy contDiff_pairBump.continuous hasCompactSupport_pairBump, zero_sub,
      zero_add, autocorr_neg, autocorr_pairBump_eq_zero (x := T)
        (by rw [abs_of_pos (by linarith)]; linarith), hσ]
    ring
  rw [h0, hσ]
  have htail := abs_integral_shifted_autocorr_arch_le contDiff_pairBump hasCompactSupport_pairBump
    hsupp hT'
  have hfac : copyTailFactor (1 / 5) T ≤ 2 / (1 - Real.exp (-2)) := by
    unfold copyTailFactor
    have hd : 0 < 1 - Real.exp (-2) := by
      have := Real.exp_lt_one_iff.mpr (show (-2 : ℝ) < 0 by norm_num); linarith
    apply div_le_div_of_nonneg_right _ hd.le
    have : Real.exp (-(T - 1 / 5) / 2) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    linarith
  have hint : 0 ≤ ∫ x, |autocorr pairBump x| := integral_nonneg fun _ => abs_nonneg _
  have htail' : |∫ x in Ioi 0, autocorr pairBump (x - T) * archLevySinhWeight x| ≤
      2 / (1 - Real.exp (-2)) * ∫ x, |autocorr pairBump x| :=
    htail.trans (mul_le_mul_of_nonneg_right hfac hint)
  have hσabs : |σ| = 1 := by
    have : |σ| ^ 2 = 1 := by rw [sq_abs, hσ]
    nlinarith [abs_nonneg σ]
  have hJ : 0 ≤ biScaleLevyEnergy pairBump :=
    biScaleLevyEnergy_nonneg hasCompactSupport_pairBump contDiff_pairBump.continuous
  have h00 : 0 ≤ autocorr pairBump 0 := autocorr_zero_nonneg _
  unfold pairArchBound
  have e1 : |EF.gammaBracket 0 * (2 * autocorr pairBump 0)| =
      2 * |EF.gammaBracket 0| * autocorr pairBump 0 := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * autocorr pairBump 0)]; ring
  have e2 : |(1 + 1) * biScaleLevyEnergy pairBump| = 2 * biScaleLevyEnergy pairBump := by
    rw [abs_of_nonneg (by positivity)]; ring
  have e3 : |σ * ∫ x in Ioi 0, autocorr pairBump (x - T) * archLevySinhWeight x| =
      |∫ x in Ioi 0, autocorr pairBump (x - T) * archLevySinhWeight x| := by
    rw [abs_mul, hσabs, one_mul]
  rw [← add_assoc]
  refine (abs_add_three _ _ _).trans ?_
  rw [e1, e2, e3]
  linarith

/-- The pole term of the distant pair grows like `e^{T/2}`, with the sign `-σ`. -/
theorem abs_pole_distantPairTest_ge {σ T : ℝ} (hσ : σ = 1 ∨ σ = -1) (hT : 1 ≤ T) :
    2 * (1 - Real.exp (-(1 / 2))) * (Real.exp ((1 / 2) * T) - 1) *
        (pairMoment (1 / 2) * pairMoment (-(1 / 2))) ≤
      |(weilPoleTerm (EF.weilTest (distantPairTest σ T).1 (distantPairTest σ T).1)).re| := by
  rw [pole_distantPairTest]
  have hm : 0 < pairMoment (1 / 2) * pairMoment (-(1 / 2)) :=
    mul_pos (pairMoment_pos _) (pairMoment_pos _)
  have he1 : 1 ≤ Real.exp ((1 / 2) * T) := Real.one_le_exp_iff.mpr (by linarith)
  have he2 : Real.exp ((-(1 / 2)) * T) ≤ Real.exp (-(1 / 2)) := Real.exp_le_exp.mpr (by linarith)
  have he2' : 0 < Real.exp ((-(1 / 2)) * T) := Real.exp_pos _
  have he3 : Real.exp (-(1 / 2)) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
  rw [abs_mul, abs_mul, abs_of_pos hm, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  apply mul_le_mul_of_nonneg_right _ hm.le
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  rcases hσ with rfl | rfl
  · rw [abs_mul, abs_of_nonpos (by linarith), abs_of_nonneg (by linarith)]
    nlinarith
  · rw [abs_mul, abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
    nlinarith

theorem pole_distantPairTest_pos (T : ℝ) :
    0 < (weilPoleTerm (EF.weilTest (distantPairTest (-1) T).1 (distantPairTest (-1) T).1)).re := by
  rw [pole_distantPairTest]
  have := mul_pos (pairMoment_pos (1 / 2)) (pairMoment_pos (-(1 / 2)))
  have h1 : 0 < 1 - (-1) * Real.exp ((1 / 2) * T) := by linarith [Real.exp_pos ((1 / 2) * T)]
  have h2 : 0 < 1 - (-1) * Real.exp ((-(1 / 2)) * T) := by linarith [Real.exp_pos ((-(1 / 2)) * T)]
  positivity

theorem pole_distantPairTest_neg {T : ℝ} (hT : 0 < T) :
    (weilPoleTerm (EF.weilTest (distantPairTest 1 T).1 (distantPairTest 1 T).1)).re < 0 := by
  rw [pole_distantPairTest]
  have := mul_pos (pairMoment_pos (1 / 2)) (pairMoment_pos (-(1 / 2)))
  have h1 : 1 - 1 * Real.exp ((1 / 2) * T) < 0 := by
    have : 1 < Real.exp ((1 / 2) * T) := Real.one_lt_exp_iff.mpr (by linarith)
    linarith
  have h2 : 0 < 1 - 1 * Real.exp ((-(1 / 2)) * T) := by
    have : Real.exp ((-(1 / 2)) * T) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    linarith
  have := mul_neg_of_neg_of_pos h1 h2
  nlinarith

/-! ### 4. Pole mass is free on gapped grids -/

theorem nodeVector_single_apply (f : WeilTestFn) (t : ℝ) (j : LogIndex) :
    nodeVector (Finsupp.single f t) j = t * logValue f.1 j := by
  rw [nodeVector_eq, linearCombination_single, Finsupp.smul_apply, logVector_apply, smul_eq_mul]

theorem nodeArchOnly_single (f : WeilTestFn) (t : ℝ) :
    nodeArchOnly (Finsupp.single f t) =
      t * (WeilOneSided.weilArchRe (EF.weilTest f.1 f.1) - (weilPoleTerm (EF.weilTest f.1 f.1)).re) := by
  rw [nodeArchOnly, nodePoleMass_single, nodeArchEnergy_eq, linearCombination_single, smul_eq_mul]
  ring

/-- **Pole mass is free.** On a gapped node set every pole mass `p` is carried by a nonnegative
`𝒩`-blind combination whose archimedean part without the pole is at most `ε` in size. -/
theorem exists_blindOn_poleMass_eq_abs_archOnly_le {𝒩 : Set ℕ} (h𝒩 : GappedNodeSet 𝒩) (p : ℝ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ c : WeilTestFn →₀ ℝ, (∀ f, 0 ≤ c f) ∧ BlindOn 𝒩 c ∧ nodePoleMass c = p ∧
      |nodeArchOnly c| ≤ ε := by
  classical
  rcases eq_or_ne p 0 with rfl | hp
  · exact ⟨0, fun _ => le_rfl, fun j _ => by simp [nodeVector_eq], by simp [nodePoleMass],
      by simp [nodeArchOnly, nodeArchEnergy_eq, nodePoleMass, hε.le]⟩
  set σ : ℝ := if 0 < p then -1 else 1 with hσdef
  have hσ : σ = 1 ∨ σ = -1 := by rw [hσdef]; split_ifs <;> simp
  have hσsq : σ ^ 2 = 1 := by rcases hσ with h | h <;> rw [h] <;> norm_num
  set m : ℝ := pairMoment (1 / 2) * pairMoment (-(1 / 2)) with hmdef
  have hm : 0 < m := mul_pos (pairMoment_pos _) (pairMoment_pos _)
  set κ : ℝ := 2 * (1 - Real.exp (-(1 / 2))) * m with hκ
  have hκpos : 0 < κ := by
    have : Real.exp (-(1 / 2)) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
    rw [hκ]; nlinarith
  set B : ℝ := pairArchBound with hB
  have hBnn : 0 ≤ B := by
    have := abs_archOnly_distantPairTest_le (σ := 1) (T := 2) (by norm_num) le_rfl
    exact (abs_nonneg _).trans this
  -- a far location where the pole is large
  set R : ℝ := 2 * Real.log (1 + (|p| * B / ε + 1) / κ) + 2 with hR
  obtain ⟨T, hRT, hgap⟩ := h𝒩 R
  have hq0 : 0 ≤ (|p| * B / ε + 1) / κ := by positivity
  have hlogpos : 0 ≤ Real.log (1 + (|p| * B / ε + 1) / κ) :=
    Real.log_nonneg (by linarith)
  have hT2 : 2 ≤ T := by linarith
  have hT1 : 1 ≤ T := by linarith
  have hexp : 1 + (|p| * B / ε + 1) / κ ≤ Real.exp ((1 / 2) * T) := by
    rw [← Real.exp_log (show 0 < 1 + (|p| * B / ε + 1) / κ by positivity)]
    exact Real.exp_le_exp.mpr (by linarith)
  set P : ℝ := (weilPoleTerm (EF.weilTest (distantPairTest σ T).1 (distantPairTest σ T).1)).re
    with hPdef
  have hPabs : |p| * B / ε + 1 ≤ |P| := by
    have h1 := abs_pole_distantPairTest_ge hσ hT1
    have h1' : κ * (Real.exp ((1 / 2) * T) - 1) ≤ |P| := by
      have e : κ * (Real.exp ((1 / 2) * T) - 1) = 2 * (1 - Real.exp (-(1 / 2))) *
          (Real.exp ((1 / 2) * T) - 1) * (pairMoment (1 / 2) * pairMoment (-(1 / 2))) := by
        rw [hκ, hmdef]; ring
      rw [e]; exact h1
    have h3 : (|p| * B / ε + 1) / κ ≤ Real.exp ((1 / 2) * T) - 1 := by linarith
    have h2 := (div_le_iff₀ hκpos).mp h3
    linarith
  have hP0 : P ≠ 0 := by
    intro h0; rw [h0, abs_zero] at hPabs
    have : 0 ≤ |p| * B / ε := by positivity
    linarith
  -- the sign of `P` matches the sign of `p`
  have hsign : 0 < p / P := by
    rcases lt_or_gt_of_ne hp with hneg | hpos
    · have hσ1 : σ = 1 := by rw [hσdef, if_neg (not_lt.mpr hneg.le)]
      have hPneg : P < 0 := by rw [hPdef, hσ1]; exact pole_distantPairTest_neg (by linarith)
      exact div_pos_of_neg_of_neg hneg hPneg
    · have hσ1 : σ = -1 := by rw [hσdef, if_pos hpos]
      have hPpos : 0 < P := by rw [hPdef, hσ1]; exact pole_distantPairTest_pos T
      exact div_pos hpos hPpos
  set t : ℝ := p / P with htdef
  refine ⟨Finsupp.single (distantPairTest σ T) t, fun f => ?_, fun j hj => ?_, ?_, ?_⟩
  · rw [Finsupp.single_apply]; split_ifs <;> [exact hsign.le; exact le_rfl]
  · rw [nodeVector_single_apply, logValue_distantPair_eq_zero σ hT1 j.2 (hgap j hj j.2), mul_zero]
  · rw [nodePoleMass_single, ← hPdef, htdef, div_mul_cancel₀ _ hP0]
  · rw [nodeArchOnly_single, abs_mul, abs_of_pos hsign]
    have hA := abs_archOnly_distantPairTest_le hσsq hT2
    calc
      p / P * |WeilOneSided.weilArchRe (EF.weilTest (distantPairTest σ T).1
            (distantPairTest σ T).1) - (weilPoleTerm (EF.weilTest (distantPairTest σ T).1
            (distantPairTest σ T).1)).re| ≤ |p| / |P| * B := by
        rw [← abs_div, abs_of_pos hsign]
        exact mul_le_mul_of_nonneg_left hA hsign.le
      _ ≤ ε := by
        have hPpos : 0 < |P| := abs_pos.mpr hP0
        rw [div_mul_eq_mul_div, div_le_iff₀ hPpos]
        have := mul_le_mul_of_nonneg_left hPabs hε.le
        have hB' : |p| * B = ε * (|p| * B / ε) := by field_simp
        nlinarith

/-- **Pole invisibility.** On a gapped node set every nonnegative `𝒩`-blind combination is
`ε`-close in archimedean energy to a nonnegative `𝒩`-blind combination of zero pole mass. -/
theorem exists_blindOn_poleMass_zero_archOnly_close {𝒩 : Set ℕ} (h𝒩 : GappedNodeSet 𝒩)
    {c₁ : WeilTestFn →₀ ℝ} (hc₁ : ∀ f, 0 ≤ c₁ f) (hb₁ : BlindOn 𝒩 c₁) {ε : ℝ} (hε : 0 < ε) :
    ∃ c : WeilTestFn →₀ ℝ, (∀ f, 0 ≤ c f) ∧ BlindOn 𝒩 c ∧ nodePoleMass c = 0 ∧
      |nodeArchOnly c - nodeArchOnly c₁| ≤ ε := by
  obtain ⟨d, hd, hbd, hpd, had⟩ :=
    exists_blindOn_poleMass_eq_abs_archOnly_le h𝒩 (-nodePoleMass c₁) hε
  refine ⟨c₁ + d, fun f => ?_, fun j hj => ?_, ?_, ?_⟩
  · rw [Finsupp.add_apply]; exact add_nonneg (hc₁ f) (hd f)
  · rw [nodeVector_add, Finsupp.add_apply, hb₁ j hj, hbd j hj, add_zero]
  · rw [nodePoleMass_add, hpd, add_neg_cancel]
  · rw [nodeArchOnly_add, add_sub_cancel_left]; exact had

/-! ### 5. The no-go -/

/-- An all-integer-blind nonnegative combination with negative archimedean part. -/
theorem exists_blind_nodeArchOnly_neg :
    ∃ c : WeilTestFn →₀ ℝ, (∀ f, 0 ≤ c f) ∧ nodeVector c = 0 ∧ nodeArchOnly c < 0 := by
  obtain ⟨c, hc, hnull, hneg⟩ := RHTower.exists_blind_arch_add_mul_pole_neg (ε := -1) (by norm_num)
  refine ⟨c, hc, Finsupp.ext fun j => ?_, ?_⟩
  · rw [nodeVector_eq, linearCombination_logVector_apply, Finsupp.coe_zero, Pi.zero_apply]
    exact hnull j j.2
  · rw [nodeArchOnly, nodeArchEnergy_eq, nodePoleMass, linearCombination_apply,
      linearCombination_apply]
    simp only [smul_eq_mul] at hneg ⊢
    linarith

/-- **Zero-pole positivity fails on every gapped node set.** -/
theorem not_zeroPoleBlindPositiveOn_of_gapped {𝒩 : Set ℕ} (h𝒩 : GappedNodeSet 𝒩) :
    ¬ ZeroPoleBlindPositiveOn 𝒩 := by
  intro hpos
  obtain ⟨c₁, hc₁, hv₁, hneg⟩ := exists_blind_nodeArchOnly_neg
  have hb₁ : BlindOn 𝒩 c₁ := fun j _ => by rw [hv₁]; rfl
  obtain ⟨c, hc, hb, hp, hclose⟩ :=
    exists_blindOn_poleMass_zero_archOnly_close h𝒩 hc₁ hb₁ (ε := -nodeArchOnly c₁ / 2)
      (by linarith)
  have hE := hpos c hc hb hp
  have hEq : nodeArchEnergy c = nodeArchOnly c := by rw [nodeArchOnly, hp, sub_zero]
  rw [hEq] at hE
  have := (abs_le.mp hclose).2
  linarith

/-! ### 6. Powers of one integer are gapped -/

/-- The powers `q^j`, `j ≥ 1`, of an integer `q ≥ 2` form a gapped node set. -/
theorem gappedNodeSet_powers {q : ℕ} (hq : 2 ≤ q) :
    GappedNodeSet {n | ∃ j : ℕ, 1 ≤ j ∧ n = q ^ j} := by
  intro R
  have hq1 : (1 : ℝ) < q := by exact_mod_cast hq
  set L : ℝ := Real.log q with hL
  have hLpos : 0 < L := Real.log_pos hq1
  have hL2 : Real.log 2 ≤ L := Real.log_le_log two_pos (by exact_mod_cast hq)
  have hlog2 : (2 : ℝ) / 5 < Real.log 2 := by have := Real.log_two_gt_d9; linarith
  obtain ⟨k, hk⟩ := exists_nat_ge (R / L)
  refine ⟨((k : ℝ) + 1 / 2) * L, ?_, ?_⟩
  · have := (div_le_iff₀ hLpos).mp hk
    nlinarith
  · rintro n ⟨j, -, rfl⟩ -
    rw [Nat.cast_pow, Real.log_pow, ← hL]
    have hdist : |(j : ℝ) * L - ((k : ℝ) + 1 / 2) * L| = |(j : ℝ) - k - 1 / 2| * L := by
      rw [← sub_mul, abs_mul, abs_of_pos hLpos]; ring_nf
    rw [hdist]
    have hhalf : (1 : ℝ) / 2 ≤ |(j : ℝ) - k - 1 / 2| := by
      rcases le_or_gt j k with hjk | hjk
      · have : (j : ℝ) ≤ k := by exact_mod_cast hjk
        rw [abs_of_neg (by linarith)]; linarith
      · have : (k : ℝ) + 1 ≤ j := by exact_mod_cast hjk
        rw [abs_of_pos (by linarith)]; linarith
    nlinarith

/-- **Single-integer no-go.** For every integer `q ≥ 2`, zero-pole positivity on combinations
blind only at the powers of `q` is false. -/
theorem not_zeroPoleBlindPositiveOn_powers {q : ℕ} (hq : 2 ≤ q) :
    ¬ ZeroPoleBlindPositiveOn {n | ∃ j : ℕ, 1 ≤ j ∧ n = q ^ j} :=
  not_zeroPoleBlindPositiveOn_of_gapped (gappedNodeSet_powers hq)

end

end GaloisForLFunctions.BiScaleUncertainty
