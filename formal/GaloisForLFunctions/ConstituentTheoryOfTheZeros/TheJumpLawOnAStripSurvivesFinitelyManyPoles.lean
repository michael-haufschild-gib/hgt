import GaloisForLFunctions.ConstituentTheoryOfTheZeros.TheJumpLawHoldsOnEveryStripAboutTheLine
import GaloisForLFunctions.InfiniteRankPurityTheory.TheJumpLawSurvivesFinitelyManyPolesOnTheLine

/-!
# The jump law on a strip survives finitely many poles on the line

In `TheJumpLawHoldsOnEveryStripAboutTheLine` the function `Φ = −(ζ/s) G` is holomorphic on the
strip. Here finitely many singularities of `G` on the critical line are not cancelled: `Φ` has
simple poles at the points of a finite set `P` on the line, and `Φ − Σ_p r_p/(s − p)` is
holomorphic on the strip and bounded near the line.

* `fractSeries_sub_eq_polarPart_of_strip`: the two series of fractional parts differ by the polar
  part, `Σ b_i {a_i u} − Σ c_j {q_j u} = Σ_p r_p u^p`, on a strip of any width with arbitrary
  positive scales on both sides.
* `tsum_jump_eq_of_strip_of_poles`, `mergedWeight_eq_of_strip_of_poles`: the polar part is
  continuous, so the jumps agree at every `u₀ > 0` and the merged weights agree at every scale.
* `eq_of_strip_of_poles`: two families over the same injective scales are equal.

Finitely many uncancelled poles change nothing: the expansions on the two sides of the line are
still one expansion.
-/

open Complex Filter Topology Set MeasureTheory

noncomputable section

namespace GaloisForLFunctions.ConstituentTheoryOfTheZeros

open GaloisForLFunctions.InfiniteRankPurityTheory

variable {ι : Type*} {κ : Type*}

/-- **The two series differ by the polar part, on any strip about the line.** -/
theorem fractSeries_sub_eq_polarPart_of_strip [Countable ι] [Countable κ] {b : ι → ℂ}
    {a : ι → ℝ} {c : κ → ℂ} {q : κ → ℝ} (ha : ∀ i, 0 < a i) (hq : ∀ j, 0 < q j) {η : ℝ}
    (hη0 : 0 < η) (hη : η ≤ 1 / 2)
    (hR : ∀ σ : ℝ, 1 / 2 < σ → σ ≤ 1 / 2 + η → Summable fun i => ‖b i‖ * a i ^ σ)
    (hL : ∀ σ : ℝ, 1 / 2 - η ≤ σ → σ < 1 / 2 → Summable fun j => ‖c j‖ * q j ^ σ)
    {P : Finset ℂ} {r : ℂ → ℂ} (hP : ∀ p ∈ P, p.re = 1 / 2)
    {F : ℂ → ℂ} (hFd : DifferentiableOn ℂ F {s : ℂ | 1 / 2 - η < s.re ∧ s.re < 1 / 2 + η})
    {K : ℝ} (hFb : ∀ s : ℂ, 1 / 2 - η / 2 ≤ s.re → s.re ≤ 1 / 2 + η / 2 → ‖F s‖ ≤ K)
    (hFR : ∀ s : ℂ, 1 / 2 < s.re → s.re < 1 / 2 + η →
      F s = -(riemannZeta s / s) * (∑' i, b i * (a i : ℂ) ^ s) - ∑ p ∈ P, r p / (s - p))
    (hFL : ∀ s : ℂ, 1 / 2 - η < s.re → s.re < 1 / 2 →
      F s = -(riemannZeta s / s) * (∑' j, c j * (q j : ℂ) ^ s) - ∑ p ∈ P, r p / (s - p))
    {u : ℝ} (hu : 0 < u) : fractSeries b a u - fractSeries c q u = polarPart P r u := by
  have hRtop := hR (1 / 2 + η) (by linarith) le_rfl
  have hLbot := hL (1 / 2 - η) le_rfl (by linarith)
  set ρ : ℝ := ∑ p ∈ P, ‖r p‖ with hρ
  have hρ0 : 0 ≤ ρ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have mpol := measurable_polarPart P r
  have mR := measurable_fractSeries b a
  have mL := measurable_fractSeries c q
  -- the corrected functions
  set gR : ℝ → ℂ := fun u => fractSeries b a u - topPart (polarPart P r) u with hgR
  set gL : ℝ → ℂ := fun u => fractSeries c q u + botPart (polarPart P r) u with hgL
  have mgR : Measurable gR := mR.sub (mpol.indicator measurableSet_Ioi)
  have mgL : Measurable gL := mL.add (mpol.indicator measurableSet_Iic)
  have bpol : ∀ u : ℝ, 0 < u → ‖polarPart P r u‖ ≤ ρ * u ^ (1 / 2 : ℝ) := fun u hu =>
    norm_polarPart_le r hP hu
  have btop : ∀ σ : ℝ, 1 / 2 ≤ σ → ∀ u : ℝ, 0 < u →
      ‖topPart (polarPart P r) u‖ ≤ ρ * u ^ σ := by
    intro σ hσ u hu
    rcases lt_or_ge 1 u with h | h
    · rw [topPart_of_lt h]
      exact (bpol u hu).trans
        (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le h.le hσ) hρ0)
    · rw [topPart_of_le h, norm_zero]
      exact mul_nonneg hρ0 (Real.rpow_nonneg hu.le _)
  have bbot : ∀ σ : ℝ, σ ≤ 1 / 2 → ∀ u : ℝ, 0 < u →
      ‖botPart (polarPart P r) u‖ ≤ ρ * u ^ σ := by
    intro σ hσ u hu
    rcases lt_or_ge 1 u with h | h
    · rw [botPart_of_lt h, norm_zero]
      exact mul_nonneg hρ0 (Real.rpow_nonneg hu.le _)
    · rw [botPart_of_le h]
      exact (bpol u hu).trans
        (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_ge hu h hσ) hρ0)
  have bR : ∀ σ : ℝ, 1 / 2 < σ → σ ≤ 1 / 2 + η → ∀ u : ℝ, 0 < u →
      ‖gR u‖ ≤ ((∑' i, ‖b i‖ * a i ^ σ) + ρ) * u ^ σ := by
    intro σ h0 h1 u hu
    rw [add_mul]
    exact (norm_sub_le _ _).trans (add_le_add
      (norm_fractSeries_le ha (by linarith) (by linarith) (hR σ h0 h1) hu.le) (btop σ h0.le u hu))
  have bL : ∀ σ : ℝ, 1 / 2 - η ≤ σ → σ < 1 / 2 → ∀ u : ℝ, 0 < u →
      ‖gL u‖ ≤ ((∑' j, ‖c j‖ * q j ^ σ) + ρ) * u ^ σ := by
    intro σ h0 h1 u hu
    rw [add_mul]
    exact (norm_add_le _ _).trans (add_le_add
      (norm_fractSeries_le hq (by linarith) (by linarith) (hL σ h0 h1) hu.le) (bbot σ h1.le u hu))
  -- one transform on both sides
  have hFR' : ∀ s : ℂ, 1 / 2 < s.re → s.re < 1 / 2 + η → F s = mellin gR (-s) := by
    intro s h0 h1
    have hσ0 : 1 / 2 < (1 / 2 + s.re) / 2 := by linarith
    have hσ1 : (1 / 2 + s.re) / 2 ≤ 1 / 2 + η := by linarith
    have c1 : MellinConvergent (fractSeries b a) (-s) :=
      mellinConvergent_of_bounds mR (by linarith) (by linarith)
        (fun u hu => norm_fractSeries_le ha (by linarith) (by linarith) (hR _ hσ0 hσ1) hu.le)
        (fun u hu => norm_fractSeries_le ha (by linarith) (by linarith) hRtop hu.le)
        (by rw [Complex.neg_re]; linarith) (by rw [Complex.neg_re]; linarith)
    have c2 : MellinConvergent (topPart (polarPart P r)) (-s) :=
      (mellin_topPart mpol (by norm_num) bpol (by rw [Complex.neg_re]; linarith)).1
    rw [hFR s h0 h1, hgR, (hasMellin_sub c1 c2).2,
      mellin_fractSeries ha (by linarith) (by linarith) (hR s.re h0 h1.le),
      mellin_topPart_polarPart r hP h0]
  have hFL' : ∀ s : ℂ, 1 / 2 - η < s.re → s.re < 1 / 2 → F s = mellin gL (-s) := by
    intro s h0 h1
    have hσ0 : 1 / 2 - η ≤ (s.re + 1 / 2) / 2 := by linarith
    have hσ1 : (s.re + 1 / 2) / 2 < 1 / 2 := by linarith
    have c1 : MellinConvergent (fractSeries c q) (-s) :=
      mellinConvergent_of_bounds mL (by linarith) (by linarith)
        (fun u hu => norm_fractSeries_le hq (by linarith) (by linarith) hLbot hu.le)
        (fun u hu => norm_fractSeries_le hq (by linarith) (by linarith) (hL _ hσ0 hσ1) hu.le)
        (by rw [Complex.neg_re]; linarith) (by rw [Complex.neg_re]; linarith)
    have c2 : MellinConvergent (botPart (polarPart P r)) (-s) :=
      (mellin_botPart mpol (by norm_num) bpol (by rw [Complex.neg_re]; linarith)).1
    rw [hFL s h0 h1, hgL, (hasMellin_add c1 c2).2,
      mellin_fractSeries hq (by linarith) (by linarith) (hL s.re h0.le h1),
      mellin_botPart_polarPart r hP h1]
    ring
  have hdiff : ∀ x : ℝ,
      gR x - gL x = fractSeries b a x - fractSeries c q x - polarPart P r x := by
    intro x
    have h := topPart_add_botPart (polarPart P r) x
    show fractSeries b a x - topPart (polarPart P r) x -
      (fractSeries c q x + botPart (polarPart P r) x) = _
    rw [← h]
    ring
  -- agreement at the points of continuity
  have hinv : ∀ x : ℝ, 0 < x → x ≠ 1 →
      ContinuousAt (fun u => fractSeries b a u - fractSeries c q u) x →
      fractSeries b a x - fractSeries c q x = polarPart P r x := by
    intro x hx hx1 hcont
    have hc : ContinuousAt (fun u => gR u - gL u) x := by
      rw [show (fun u => gR u - gL u) =
        fun u => fractSeries b a u - fractSeries c q u - polarPart P r u from funext hdiff]
      exact hcont.sub (continuousAt_polarPart P r hx)
    have h := eq_of_mellin_eq_on_strip mgR mgL hη0
      (CR := fun σ => (∑' i, ‖b i‖ * a i ^ σ) + ρ) (CL := fun σ => (∑' j, ‖c j‖ * q j ^ σ) + ρ)
      bR bL hFd hFb hFR' hFL' hx hx1 hc
    have h2 := hdiff x
    rw [h, sub_self] at h2
    exact sub_eq_zero.mp h2.symm
  -- points of continuity are dense; the series are right continuous, the polar part continuous
  have hbad : ({u : ℝ | ∃ i, ∃ n : ℤ, a i * u = n} ∪ {u : ℝ | ∃ j, ∃ n : ℤ, q j * u = n} ∪
      {1}).Countable :=
    ((countable_jumpSet ha).union (countable_jumpSet hq)).union (countable_singleton 1)
  have hfreq : ∃ᶠ x in 𝓝[>] u, fractSeries b a x - fractSeries c q x = polarPart P r x := by
    refine ((frequently_nhdsGT_notMem hbad u).and_eventually self_mem_nhdsWithin).mono ?_
    rintro x ⟨hx, hxu⟩
    have hx0 : 0 < x := hu.trans hxu
    have hR1 : ∀ i, b i ≠ 0 → ∀ n : ℤ, a i * x ≠ n := fun i _ n hn =>
      hx (Or.inl (Or.inl ⟨i, n, hn⟩))
    have hL1 : ∀ j, c j ≠ 0 → ∀ n : ℤ, q j * x ≠ n := fun j _ n hn =>
      hx (Or.inl (Or.inr ⟨j, n, hn⟩))
    have hx1 : x ≠ 1 := fun h => hx (Or.inr h)
    exact hinv x hx0 hx1
      ((continuousAt_fractSeries ha (by linarith) (by linarith) hRtop hx0 hR1).sub
        (continuousAt_fractSeries hq (by linarith) (by linarith) hLbot hx0 hL1))
  exact tendsto_nhds_unique_of_frequently_eq
    ((tendsto_fractSeries_right ha (by linarith) (by linarith) hRtop hu).sub
      (tendsto_fractSeries_right hq (by linarith) (by linarith) hLbot hu))
    ((continuousAt_polarPart P r hu).tendsto.mono_left nhdsWithin_le_nhds) hfreq

open scoped Classical in
/-- **The jump law on a strip, with poles.** Under the hypotheses of
`fractSeries_sub_eq_polarPart_of_strip` the two series have the same jump at every `u₀ > 0`:
their difference is continuous. -/
theorem tsum_jump_eq_of_strip_of_poles [Countable ι] [Countable κ] {b : ι → ℂ} {a : ι → ℝ}
    {c : κ → ℂ} {q : κ → ℝ} (ha : ∀ i, 0 < a i) (hq : ∀ j, 0 < q j) {η : ℝ} (hη0 : 0 < η)
    (hη : η ≤ 1 / 2)
    (hR : ∀ σ : ℝ, 1 / 2 < σ → σ ≤ 1 / 2 + η → Summable fun i => ‖b i‖ * a i ^ σ)
    (hL : ∀ σ : ℝ, 1 / 2 - η ≤ σ → σ < 1 / 2 → Summable fun j => ‖c j‖ * q j ^ σ)
    {P : Finset ℂ} {r : ℂ → ℂ} (hP : ∀ p ∈ P, p.re = 1 / 2)
    {F : ℂ → ℂ} (hFd : DifferentiableOn ℂ F {s : ℂ | 1 / 2 - η < s.re ∧ s.re < 1 / 2 + η})
    {K : ℝ} (hFb : ∀ s : ℂ, 1 / 2 - η / 2 ≤ s.re → s.re ≤ 1 / 2 + η / 2 → ‖F s‖ ≤ K)
    (hFR : ∀ s : ℂ, 1 / 2 < s.re → s.re < 1 / 2 + η →
      F s = -(riemannZeta s / s) * (∑' i, b i * (a i : ℂ) ^ s) - ∑ p ∈ P, r p / (s - p))
    (hFL : ∀ s : ℂ, 1 / 2 - η < s.re → s.re < 1 / 2 →
      F s = -(riemannZeta s / s) * (∑' j, c j * (q j : ℂ) ^ s) - ∑ p ∈ P, r p / (s - p))
    {u₀ : ℝ} (hu₀ : 0 < u₀) :
    (∑' i, if ∃ n : ℤ, a i * u₀ = n then b i else 0) =
      ∑' j, if ∃ n : ℤ, q j * u₀ = n then c j else 0 := by
  have hRtop := hR (1 / 2 + η) (by linarith) le_rfl
  have hLbot := hL (1 / 2 - η) le_rfl (by linarith)
  have heq : ∀ u : ℝ, 0 < u → fractSeries b a u - fractSeries c q u = polarPart P r u :=
    fun u hu => fractSeries_sub_eq_polarPart_of_strip ha hq hη0 hη hR hL hP hFd hFb hFR hFL hu
  have hl1 := tendsto_fractSeries_left ha (by linarith) (by linarith) hRtop hu₀
  have hl2 := tendsto_fractSeries_left hq (by linarith) (by linarith) hLbot hu₀
  have hev : ∀ᶠ u in 𝓝[<] u₀, fractSeries b a u - fractSeries c q u = polarPart P r u := by
    filter_upwards [Ioo_mem_nhdsLT hu₀] with u hu
    exact heq u hu.1
  -- the left limits differ by the polar part, as the values do
  have hlim := tendsto_nhds_unique_of_frequently_eq (hl1.sub hl2)
    ((continuousAt_polarPart P r hu₀).tendsto.mono_left nhdsWithin_le_nhds) hev.frequently
  have j1 := fractSeries_sub_leftLimit ha (by linarith) (by linarith) hRtop hu₀
  have j2 := fractSeries_sub_leftLimit hq (by linarith) (by linarith) hLbot hu₀
  have h0 := heq u₀ hu₀
  apply neg_injective
  rw [← j1, ← j2]
  linear_combination h0 - hlim

open scoped Classical in
/-- **The merged weights agree, with poles.** Finitely many simple poles on the line do not
change the equality of the weights that the two expansions carry at a scale. -/
theorem mergedWeight_eq_of_strip_of_poles [Countable ι] [Countable κ] {b : ι → ℂ} {a : ι → ℝ}
    {c : κ → ℂ} {q : κ → ℝ} (ha : ∀ i, 0 < a i) (hq : ∀ j, 0 < q j) {η : ℝ} (hη0 : 0 < η)
    (hη : η ≤ 1 / 2)
    (hR : ∀ σ : ℝ, 1 / 2 < σ → σ ≤ 1 / 2 + η → Summable fun i => ‖b i‖ * a i ^ σ)
    (hL : ∀ σ : ℝ, 1 / 2 - η ≤ σ → σ < 1 / 2 → Summable fun j => ‖c j‖ * q j ^ σ)
    {P : Finset ℂ} {r : ℂ → ℂ} (hP : ∀ p ∈ P, p.re = 1 / 2)
    {F : ℂ → ℂ} (hFd : DifferentiableOn ℂ F {s : ℂ | 1 / 2 - η < s.re ∧ s.re < 1 / 2 + η})
    {K : ℝ} (hFb : ∀ s : ℂ, 1 / 2 - η / 2 ≤ s.re → s.re ≤ 1 / 2 + η / 2 → ‖F s‖ ≤ K)
    (hFR : ∀ s : ℂ, 1 / 2 < s.re → s.re < 1 / 2 + η →
      F s = -(riemannZeta s / s) * (∑' i, b i * (a i : ℂ) ^ s) - ∑ p ∈ P, r p / (s - p))
    (hFL : ∀ s : ℂ, 1 / 2 - η < s.re → s.re < 1 / 2 →
      F s = -(riemannZeta s / s) * (∑' j, c j * (q j : ℂ) ^ s) - ∑ p ∈ P, r p / (s - p))
    {t : ℝ} (ht : 0 < t) :
    (∑' i, if a i = t then b i else 0) = ∑' j, if q j = t then c j else 0 :=
  mergedWeight_eq_of_jump ha hq (σ₁ := 1 / 2 + η) (σ₂ := 1 / 2 - η / 2) (by linarith)
    (by linarith) (hR _ (by linarith) le_rfl) (hL _ (by linarith) (by linarith))
    (fun _ hu₀ => tsum_jump_eq_of_strip_of_poles ha hq hη0 hη hR hL hP hFd hFb hFR hFL hu₀) ht

/-- Two families over the same injective scales, indexed by a countable set, that represent one
function with finitely many simple poles on the line are equal. -/
theorem eq_of_strip_of_poles_of_countable [Countable ι] {b c : ι → ℂ} {a : ι → ℝ}
    (ha : ∀ i, 0 < a i) (hinj : Function.Injective a) {η : ℝ} (hη0 : 0 < η) (hη : η ≤ 1 / 2)
    (hR : ∀ σ : ℝ, 1 / 2 < σ → σ ≤ 1 / 2 + η → Summable fun i => ‖b i‖ * a i ^ σ)
    (hL : ∀ σ : ℝ, 1 / 2 - η ≤ σ → σ < 1 / 2 → Summable fun i => ‖c i‖ * a i ^ σ)
    {P : Finset ℂ} {r : ℂ → ℂ} (hP : ∀ p ∈ P, p.re = 1 / 2)
    {F : ℂ → ℂ} (hFd : DifferentiableOn ℂ F {s : ℂ | 1 / 2 - η < s.re ∧ s.re < 1 / 2 + η})
    {K : ℝ} (hFb : ∀ s : ℂ, 1 / 2 - η / 2 ≤ s.re → s.re ≤ 1 / 2 + η / 2 → ‖F s‖ ≤ K)
    (hFR : ∀ s : ℂ, 1 / 2 < s.re → s.re < 1 / 2 + η →
      F s = -(riemannZeta s / s) * (∑' i, b i * (a i : ℂ) ^ s) - ∑ p ∈ P, r p / (s - p))
    (hFL : ∀ s : ℂ, 1 / 2 - η < s.re → s.re < 1 / 2 →
      F s = -(riemannZeta s / s) * (∑' i, c i * (a i : ℂ) ^ s) - ∑ p ∈ P, r p / (s - p)) :
    b = c := by
  classical
  funext i
  have h := mergedWeight_eq_of_strip_of_poles ha ha hη0 hη hR hL hP hFd hFb hFR hFL (ha i)
  rw [tsum_eq_single i fun i' hi' => if_neg fun h' => hi' (hinj h'),
    tsum_eq_single i fun i' hi' => if_neg fun h' => hi' (hinj h'), if_pos rfl, if_pos rfl] at h
  exact h

/-- **The zeros of `ζ` cancel no pole of a two-sided expansion, up to finitely many.** Two
families over the same injective positive scales that represent, on the two sides of the line, a
function `−(ζ/s) G − Σ_p r_p/(s − p)` holomorphic on the strip and bounded near the line are
equal. The index set may be uncountable. -/
theorem eq_of_strip_of_poles {b c : ι → ℂ} {a : ι → ℝ}
    (ha : ∀ i, 0 < a i) (hinj : Function.Injective a) {η : ℝ} (hη0 : 0 < η) (hη : η ≤ 1 / 2)
    (hR : ∀ σ : ℝ, 1 / 2 < σ → σ ≤ 1 / 2 + η → Summable fun i => ‖b i‖ * a i ^ σ)
    (hL : ∀ σ : ℝ, 1 / 2 - η ≤ σ → σ < 1 / 2 → Summable fun i => ‖c i‖ * a i ^ σ)
    {P : Finset ℂ} {r : ℂ → ℂ} (hP : ∀ p ∈ P, p.re = 1 / 2)
    {F : ℂ → ℂ} (hFd : DifferentiableOn ℂ F {s : ℂ | 1 / 2 - η < s.re ∧ s.re < 1 / 2 + η})
    {K : ℝ} (hFb : ∀ s : ℂ, 1 / 2 - η / 2 ≤ s.re → s.re ≤ 1 / 2 + η / 2 → ‖F s‖ ≤ K)
    (hFR : ∀ s : ℂ, 1 / 2 < s.re → s.re < 1 / 2 + η →
      F s = -(riemannZeta s / s) * (∑' i, b i * (a i : ℂ) ^ s) - ∑ p ∈ P, r p / (s - p))
    (hFL : ∀ s : ℂ, 1 / 2 - η < s.re → s.re < 1 / 2 →
      F s = -(riemannZeta s / s) * (∑' i, c i * (a i : ℂ) ^ s) - ∑ p ∈ P, r p / (s - p)) :
    b = c := by
  classical
  have hbsupp : (Function.support b).Countable :=
    ((hR (1 / 2 + η) (by linarith) le_rfl).countable_support).mono fun i hi =>
      mul_ne_zero (norm_ne_zero_iff.mpr hi) (Real.rpow_pos_of_pos (ha i) _).ne'
  have hcsupp : (Function.support c).Countable :=
    ((hL (1 / 2 - η) le_rfl (by linarith)).countable_support).mono fun i hi =>
      mul_ne_zero (norm_ne_zero_iff.mpr hi) (Real.rpow_pos_of_pos (ha i) _).ne'
  set S : Set ι := Function.support b ∪ Function.support c with hS
  haveI : Countable S := (hbsupp.union hcsupp).to_subtype
  -- sums over the whole index set are sums over `S`
  have key : ∀ f : ι → ℂ, Function.support f ⊆ S → ∀ s : ℂ,
      ∑' i : S, f i * ((a i : ℝ) : ℂ) ^ s = ∑' i, f i * ((a i : ℝ) : ℂ) ^ s := by
    intro f hf s
    rw [tsum_subtype S fun i => f i * ((a i : ℝ) : ℂ) ^ s]
    refine tsum_congr fun i => ?_
    by_cases hi : i ∈ S
    · rw [Set.indicator_of_mem hi]
    · rw [Set.indicator_of_notMem hi]
      have h0 : f i = 0 := by
        by_contra h
        exact hi (hf h)
      rw [h0, zero_mul]
  have h := eq_of_strip_of_poles_of_countable (b := fun i : S => b i) (c := fun i : S => c i)
    (a := fun i : S => a i) (fun i => ha i) (hinj.comp Subtype.val_injective) hη0 hη
    (fun σ h1 h2 => (hR σ h1 h2).subtype S) (fun σ h1 h2 => (hL σ h1 h2).subtype S) hP hFd hFb
    (fun s h1 h2 => by rw [hFR s h1 h2, key b Set.subset_union_left s])
    (fun s h1 h2 => by rw [hFL s h1 h2, key c Set.subset_union_right s])
  funext i
  by_cases hi : i ∈ S
  · exact congrFun h ⟨i, hi⟩
  · have hb : b i = 0 := by
      by_contra hb
      exact hi (Or.inl hb)
    have hc : c i = 0 := by
      by_contra hc
      exact hi (Or.inr hc)
    rw [hb, hc]

end GaloisForLFunctions.ConstituentTheoryOfTheZeros
