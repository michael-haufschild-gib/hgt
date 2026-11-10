import GaloisForLFunctions.InfiniteRankPurityTheory.TheConstantTermsOnTheTwoSidesOfTheLineAgree
import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# The jump law survives finitely many poles on the line

In `TheConstantTermsOnTheTwoSidesOfTheLineAgree` the function `F = −G ζ/s` is holomorphic on the
strip: every singularity of the two-sided expansion `G` on the critical line is cancelled by a zero
of `ζ`. Here finitely many are not. Let `F` have simple poles at the points of a finite set `P` on
the line, with residues `r_p`, so that `F − Σ_p r_p/(s − p)` is holomorphic on the strip and bounded
near the line.

* `fractSeries_sub_eq_polarPart`: the two series of fractional parts no longer agree; they differ
  by the polar part, `Σ b_i {a_i u} − Σ c_j {q_j u} = Σ_p r_p u^p` for `u > 0`. The function
  `u ↦ u^p` cut off above `1` has the transform `1/(s − p)` right of the line, and cut off below
  `1` it has the transform `−1/(s − p)` left of it (`mellin_topPart_polarPart`,
  `mellin_botPart_polarPart`), so the corrected functions have one transform and
  `eq_of_mellin_eq_two_sided` applies.
* `tsum_jump_eq_of_poles`, `constantTerms_agree_of_poles`: the polar part is continuous, so the
  jumps of the two series still agree at every `u₀ > 0`, and so do the constant terms. Finitely
  many zeros of the denominator of `G` outside the zeros of `ζ` change nothing.
* `exists_principalParts`: the hypothesis in the form met in applications. If `H` is holomorphic on
  an open set containing `P`, then `H(z)/Π_p (z − p)` minus suitable simple principal parts at the
  points of `P` is holomorphic.
-/

open Complex Filter Topology Set MeasureTheory

noncomputable section

namespace GaloisForLFunctions.InfiniteRankPurityTheory

variable {ι : Type*} {κ : Type*}

/-! ### The polar part -/

/-- The polar part `Σ_p r_p u^p` of finitely many simple poles. -/
def polarPart (P : Finset ℂ) (r : ℂ → ℂ) (u : ℝ) : ℂ := ∑ p ∈ P, r p * (u : ℂ) ^ p

theorem norm_polarPart_le {P : Finset ℂ} (r : ℂ → ℂ) (hP : ∀ p ∈ P, p.re = 1 / 2) {u : ℝ}
    (hu : 0 < u) : ‖polarPart P r u‖ ≤ (∑ p ∈ P, ‖r p‖) * u ^ (1 / 2 : ℝ) := by
  rw [polarPart, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun p hp => ?_)
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hu, hP p hp]

theorem measurable_polarPart (P : Finset ℂ) (r : ℂ → ℂ) : Measurable (polarPart P r) := by
  unfold polarPart
  exact Finset.measurable_sum _ fun p _ => (Complex.measurable_ofReal.pow_const p).const_mul (r p)

theorem continuousAt_polarPart (P : Finset ℂ) (r : ℂ → ℂ) {u : ℝ} (hu : 0 < u) :
    ContinuousAt (polarPart P r) u := by
  unfold polarPart
  refine tendsto_finsetSum _ fun p _ => ?_
  exact ((Complex.continuousAt_ofReal_cpow_const u p (Or.inr hu.ne')).tendsto).const_mul (r p)

/-- Right of the line the part of `Σ_p r_p u^p` above `1` has the transform `Σ_p r_p/(s − p)`. -/
theorem mellin_topPart_polarPart {P : Finset ℂ} (r : ℂ → ℂ) (hP : ∀ p ∈ P, p.re = 1 / 2) {s : ℂ}
    (hs : 1 / 2 < s.re) :
    mellin (topPart (polarPart P r)) (-s) = ∑ p ∈ P, r p / (s - p) := by
  have h1 : ∀ t : ℝ, (t : ℂ) ^ (-s - 1) • topPart (polarPart P r) t =
      (Ioi (1 : ℝ)).indicator (fun t : ℝ => ∑ p ∈ P, r p * (t : ℂ) ^ (p - s - 1)) t := by
    intro t
    by_cases ht : t ∈ Ioi (1 : ℝ)
    · rw [topPart, indicator_of_mem ht, indicator_of_mem ht, polarPart, smul_eq_mul,
        Finset.mul_sum]
      refine Finset.sum_congr rfl fun p _ => ?_
      have ht0 : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr (by linarith [mem_Ioi.mp ht])
      rw [show p - s - 1 = (-s - 1) + p by ring, Complex.cpow_add _ _ ht0]
      ring
    · rw [topPart, indicator_of_notMem ht, indicator_of_notMem ht, smul_zero]
  have hre : ∀ p ∈ P, (p - s - 1).re < -1 := fun p hp => by
    rw [Complex.sub_re, Complex.sub_re, Complex.one_re, hP p hp]
    linarith
  rw [mellin]
  simp only [h1]
  rw [setIntegral_indicator measurableSet_Ioi,
    show Ioi (0 : ℝ) ∩ Ioi 1 = Ioi 1 from inter_eq_right.mpr (Ioi_subset_Ioi zero_le_one),
    integral_finsetSum _ fun p hp => (integrableOn_Ioi_cpow_of_lt (hre p hp) one_pos).const_mul _]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [integral_const_mul, integral_Ioi_cpow_of_lt (hre p hp) one_pos, Complex.ofReal_one,
    Complex.one_cpow, show p - s - 1 + 1 = -(s - p) by ring, neg_div_neg_eq]
  ring

/-- Left of the line the part of `Σ_p r_p u^p` below `1` has the transform `−Σ_p r_p/(s − p)`. -/
theorem mellin_botPart_polarPart {P : Finset ℂ} (r : ℂ → ℂ) (hP : ∀ p ∈ P, p.re = 1 / 2) {s : ℂ}
    (hs : s.re < 1 / 2) :
    mellin (botPart (polarPart P r)) (-s) = -∑ p ∈ P, r p / (s - p) := by
  have h1 : ∀ t ∈ Ioi (0 : ℝ), (t : ℂ) ^ (-s - 1) • botPart (polarPart P r) t =
      (Iic (1 : ℝ)).indicator (fun t : ℝ => ∑ p ∈ P, r p * (t : ℂ) ^ (p - s - 1)) t := by
    intro t ht0'
    by_cases ht : t ∈ Iic (1 : ℝ)
    · rw [botPart, indicator_of_mem ht, indicator_of_mem ht, polarPart, smul_eq_mul,
        Finset.mul_sum]
      refine Finset.sum_congr rfl fun p _ => ?_
      have ht0 : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr (ne_of_gt ht0')
      rw [show p - s - 1 = (-s - 1) + p by ring, Complex.cpow_add _ _ ht0]
      ring
    · rw [botPart, indicator_of_notMem ht, indicator_of_notMem ht, smul_zero]
  have hre : ∀ p ∈ P, -1 < (p - s - 1).re := fun p hp => by
    rw [Complex.sub_re, Complex.sub_re, Complex.one_re, hP p hp]
    linarith
  rw [mellin, setIntegral_congr_fun measurableSet_Ioi h1, setIntegral_indicator measurableSet_Iic,
    show Ioi (0 : ℝ) ∩ Iic 1 = Ioc 0 1 from rfl,
    integral_finsetSum _ fun p hp =>
      ((intervalIntegral.intervalIntegrable_cpow' (a := 0) (b := 1) (hre p hp)).1).const_mul _,
    ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun p hp => ?_
  have hne : p - s - 1 + 1 ≠ 0 := fun h => by
    have := congrArg Complex.re h
    rw [Complex.add_re, Complex.one_re, Complex.zero_re] at this
    linarith [hre p hp]
  rw [integral_const_mul, ← intervalIntegral.integral_of_le zero_le_one,
    integral_cpow (Or.inl (hre p hp)), Complex.ofReal_one, Complex.one_cpow, Complex.ofReal_zero,
    Complex.zero_cpow hne, sub_zero, show p - s - 1 + 1 = -(s - p) by ring, div_neg]
  ring

/-! ### The two series differ by the polar part -/

/-- **The two series differ by the polar part.** If `F`, holomorphic on the strip and bounded near
the line, is `−(ζ/s) Σ b_i a_i^s − Σ_p r_p/(s − p)` right of the line and
`−(ζ/s) Σ c_j q_j^s − Σ_p r_p/(s − p)` left of it, with the points `p` on the line, then
`Σ b_i {a_i u} − Σ c_j {q_j u} = Σ_p r_p u^p` at every `u > 0`. -/
theorem fractSeries_sub_eq_polarPart [Countable ι] [Countable κ] {b : ι → ℂ} {a : ι → ℝ}
    {c : κ → ℂ} {q : κ → ℝ} (ha : ∀ i, 0 < a i) (hq : ∀ j, 0 < q j)
    (hR : ∀ σ : ℝ, 1 / 2 < σ → Summable fun i => ‖b i‖ * a i ^ σ)
    (hL : ∀ σ : ℝ, σ < 1 / 2 → Summable fun j => ‖c j‖ * q j ^ σ)
    {P : Finset ℂ} {r : ℂ → ℂ} (hP : ∀ p ∈ P, p.re = 1 / 2)
    {F : ℂ → ℂ} (hFd : DifferentiableOn ℂ F {s : ℂ | 0 < s.re ∧ s.re < 1}) {K : ℝ}
    (hFb : ∀ s : ℂ, 1 / 4 ≤ s.re → s.re ≤ 3 / 4 → ‖F s‖ ≤ K)
    (hFR : ∀ s : ℂ, 1 / 2 < s.re → s.re < 1 →
      F s = -(riemannZeta s / s) * (∑' i, b i * (a i : ℂ) ^ s) - ∑ p ∈ P, r p / (s - p))
    (hFL : ∀ s : ℂ, 0 < s.re → s.re < 1 / 2 →
      F s = -(riemannZeta s / s) * (∑' j, c j * (q j : ℂ) ^ s) - ∑ p ∈ P, r p / (s - p))
    {u : ℝ} (hu : 0 < u) : fractSeries b a u - fractSeries c q u = polarPart P r u := by
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
  have bR : ∀ σ : ℝ, 1 / 2 < σ → σ ≤ 1 → ∀ u : ℝ, 0 < u →
      ‖gR u‖ ≤ ((∑' i, ‖b i‖ * a i ^ σ) + ρ) * u ^ σ := by
    intro σ h0 h1 u hu
    rw [add_mul]
    exact (norm_sub_le _ _).trans (add_le_add
      (norm_fractSeries_le ha (by linarith) h1 (hR σ h0) hu.le) (btop σ h0.le u hu))
  have bL : ∀ σ : ℝ, 0 ≤ σ → σ < 1 / 2 → ∀ u : ℝ, 0 < u →
      ‖gL u‖ ≤ ((∑' j, ‖c j‖ * q j ^ σ) + ρ) * u ^ σ := by
    intro σ h0 h1 u hu
    rw [add_mul]
    exact (norm_add_le _ _).trans (add_le_add
      (norm_fractSeries_le hq h0 (by linarith) (hL σ h1) hu.le) (bbot σ h1.le u hu))
  -- one transform on both sides
  have hFR' : ∀ s : ℂ, 1 / 2 < s.re → s.re < 1 → F s = mellin gR (-s) := by
    intro s h0 h1
    have hσ0 : 1 / 2 < (1 / 2 + s.re) / 2 := by linarith
    have hσ1 : (1 / 2 + s.re) / 2 ≤ 1 := by linarith
    have c1 : MellinConvergent (fractSeries b a) (-s) :=
      mellinConvergent_of_bounds mR (by linarith) zero_le_one
        (fun u hu => norm_fractSeries_le ha (by linarith) hσ1 (hR _ hσ0) hu.le)
        (fun u hu => norm_fractSeries_le ha zero_le_one le_rfl (hR 1 (by norm_num)) hu.le)
        (by rw [Complex.neg_re]; linarith) (by rw [Complex.neg_re]; linarith)
    have c2 : MellinConvergent (topPart (polarPart P r)) (-s) :=
      (mellin_topPart mpol (by norm_num) bpol (by rw [Complex.neg_re]; linarith)).1
    rw [hFR s h0 h1, hgR, (hasMellin_sub c1 c2).2,
      mellin_fractSeries ha (by linarith) h1 (hR s.re h0), mellin_topPart_polarPart r hP h0]
  have hFL' : ∀ s : ℂ, 0 < s.re → s.re < 1 / 2 → F s = mellin gL (-s) := by
    intro s h0 h1
    have hσ0 : (0 : ℝ) ≤ (s.re + 1 / 2) / 2 := by linarith
    have hσ1 : (s.re + 1 / 2) / 2 < 1 / 2 := by linarith
    have c1 : MellinConvergent (fractSeries c q) (-s) :=
      mellinConvergent_of_bounds mL le_rfl hσ0
        (fun u hu => norm_fractSeries_le hq le_rfl zero_le_one (hL 0 (by norm_num)) hu.le)
        (fun u hu => norm_fractSeries_le hq hσ0 (by linarith) (hL _ hσ1) hu.le)
        (by rw [Complex.neg_re]; linarith) (by rw [Complex.neg_re]; linarith)
    have c2 : MellinConvergent (botPart (polarPart P r)) (-s) :=
      (mellin_botPart mpol (by norm_num) bpol (by rw [Complex.neg_re]; linarith)).1
    rw [hFL s h0 h1, hgL, (hasMellin_add c1 c2).2,
      mellin_fractSeries hq h0 (by linarith) (hL s.re h1), mellin_botPart_polarPart r hP h1]
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
    have h := eq_of_mellin_eq_two_sided mgR mgL
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
      ((continuousAt_fractSeries ha zero_le_one le_rfl (hR 1 (by norm_num)) hx0 hR1).sub
        (continuousAt_fractSeries hq le_rfl zero_le_one (hL 0 (by norm_num)) hx0 hL1))
  exact tendsto_nhds_unique_of_frequently_eq
    ((tendsto_fractSeries_right ha zero_le_one le_rfl (hR 1 (by norm_num)) hu).sub
      (tendsto_fractSeries_right hq le_rfl zero_le_one (hL 0 (by norm_num)) hu))
    ((continuousAt_polarPart P r hu).tendsto.mono_left nhdsWithin_le_nhds) hfreq

open scoped Classical in
/-- **The jump law with poles.** Under the hypotheses of `fractSeries_sub_eq_polarPart` the two
series have the same jump at every `u₀ > 0`: their difference is continuous. -/
theorem tsum_jump_eq_of_poles [Countable ι] [Countable κ] {b : ι → ℂ} {a : ι → ℝ} {c : κ → ℂ}
    {q : κ → ℝ} (ha : ∀ i, 0 < a i) (hq : ∀ j, 0 < q j)
    (hR : ∀ σ : ℝ, 1 / 2 < σ → Summable fun i => ‖b i‖ * a i ^ σ)
    (hL : ∀ σ : ℝ, σ < 1 / 2 → Summable fun j => ‖c j‖ * q j ^ σ)
    {P : Finset ℂ} {r : ℂ → ℂ} (hP : ∀ p ∈ P, p.re = 1 / 2)
    {F : ℂ → ℂ} (hFd : DifferentiableOn ℂ F {s : ℂ | 0 < s.re ∧ s.re < 1}) {K : ℝ}
    (hFb : ∀ s : ℂ, 1 / 4 ≤ s.re → s.re ≤ 3 / 4 → ‖F s‖ ≤ K)
    (hFR : ∀ s : ℂ, 1 / 2 < s.re → s.re < 1 →
      F s = -(riemannZeta s / s) * (∑' i, b i * (a i : ℂ) ^ s) - ∑ p ∈ P, r p / (s - p))
    (hFL : ∀ s : ℂ, 0 < s.re → s.re < 1 / 2 →
      F s = -(riemannZeta s / s) * (∑' j, c j * (q j : ℂ) ^ s) - ∑ p ∈ P, r p / (s - p))
    {u₀ : ℝ} (hu₀ : 0 < u₀) :
    (∑' i, if ∃ n : ℤ, a i * u₀ = n then b i else 0) =
      ∑' j, if ∃ n : ℤ, q j * u₀ = n then c j else 0 := by
  have heq : ∀ u : ℝ, 0 < u → fractSeries b a u - fractSeries c q u = polarPart P r u :=
    fun u hu => fractSeries_sub_eq_polarPart ha hq hR hL hP hFd hFb hFR hFL hu
  have hl1 := tendsto_fractSeries_left ha zero_le_one le_rfl (hR 1 (by norm_num)) hu₀
  have hl2 := tendsto_fractSeries_left hq le_rfl zero_le_one (hL 0 (by norm_num)) hu₀
  have hev : ∀ᶠ u in 𝓝[<] u₀, fractSeries b a u - fractSeries c q u = polarPart P r u := by
    filter_upwards [Ioo_mem_nhdsLT hu₀] with u hu
    exact heq u hu.1
  -- the left limits differ by the polar part, as the values do
  have hlim := tendsto_nhds_unique_of_frequently_eq (hl1.sub hl2)
    ((continuousAt_polarPart P r hu₀).tendsto.mono_left nhdsWithin_le_nhds) hev.frequently
  have j1 := fractSeries_sub_leftLimit ha zero_le_one le_rfl (hR 1 (by norm_num)) hu₀
  have j2 := fractSeries_sub_leftLimit hq le_rfl zero_le_one (hL 0 (by norm_num)) hu₀
  have h0 := heq u₀ hu₀
  apply neg_injective
  rw [← j1, ← j2]
  linear_combination h0 - hlim

/-- **The constant terms agree, with poles.** Finitely many simple poles of `F` on the line do not
change the conclusion of `constantTerms_agree`. -/
theorem constantTerms_agree_of_poles [Countable ι] [Countable κ] {b : ι → ℂ} {a : ι → ℝ}
    {c : κ → ℂ} {q : κ → ℝ} (ha0 : ∀ i, 0 < a i) (ha1 : ∀ i, a i ≤ 1) (hq : ∀ j, 1 ≤ q j)
    (hR : ∀ σ : ℝ, 1 / 2 < σ → Summable fun i => ‖b i‖ * a i ^ σ)
    (hL : ∀ σ : ℝ, σ < 1 / 2 → Summable fun j => ‖c j‖ * q j ^ σ)
    {P : Finset ℂ} {r : ℂ → ℂ} (hP : ∀ p ∈ P, p.re = 1 / 2)
    {F : ℂ → ℂ} (hFd : DifferentiableOn ℂ F {s : ℂ | 0 < s.re ∧ s.re < 1}) {K : ℝ}
    (hFb : ∀ s : ℂ, 1 / 4 ≤ s.re → s.re ≤ 3 / 4 → ‖F s‖ ≤ K)
    (hFR : ∀ s : ℂ, 1 / 2 < s.re → s.re < 1 →
      F s = -(riemannZeta s / s) * (∑' i, b i * (a i : ℂ) ^ s) - ∑ p ∈ P, r p / (s - p))
    (hFL : ∀ s : ℂ, 0 < s.re → s.re < 1 / 2 →
      F s = -(riemannZeta s / s) * (∑' j, c j * (q j : ℂ) ^ s) - ∑ p ∈ P, r p / (s - p)) :
    (∑' j, if q j = 1 then c j else 0) = ∑' i, if a i = 1 then b i else 0 := by
  have hq0 : ∀ j, 0 < q j := fun j => lt_of_lt_of_le one_pos (hq j)
  have hcsum : Summable fun j => ‖c j‖ := by
    have h := hL 0 (by norm_num)
    simpa only [Real.rpow_zero, mul_one] using h
  exact constantTerms_agree_of_jump ha0 ha1 hq hcsum (hL (1 / 4) (by norm_num))
    fun u₀ hu₀ => tsum_jump_eq_of_poles ha0 hq0 hR hL hP hFd hFb hFR hFL hu₀

/-! ### Principal parts -/

/-- **Principal parts.** For `H` holomorphic on an open set containing the finite set `P`, there
are residues `r_p` such that `H(z)/Π_p (z − p) − Σ_p r_p/(z − p)` extends to a holomorphic function:
one pole at a time, the extension is the difference quotient of the previous one. -/
theorem exists_principalParts {U : Set ℂ} (hU : IsOpen U) (P : Finset ℂ) (hP : ∀ p ∈ P, p ∈ U) :
    ∀ H : ℂ → ℂ, DifferentiableOn ℂ H U → ∃ r : ℂ → ℂ, ∃ G : ℂ → ℂ, DifferentiableOn ℂ G U ∧
      ∀ z ∈ U, z ∉ P → G z = H z / ∏ p ∈ P, (z - p) - ∑ p ∈ P, r p / (z - p) := by
  classical
  induction P using Finset.induction_on with
  | empty =>
    intro H hH
    exact ⟨fun _ => 0, H, hH, fun z _ _ => by simp⟩
  | insert p₀ P hp₀ ih =>
    intro H hH
    obtain ⟨r, G, hG, hGeq⟩ := ih (fun p hp => hP p (Finset.mem_insert_of_mem hp)) H hH
    have hp₀U : p₀ ∈ U := hP p₀ (Finset.mem_insert_self _ _)
    set r' : ℂ → ℂ := fun p =>
      if p = p₀ then G p₀ - ∑ p' ∈ P, r p' / (p' - p₀) else r p / (p - p₀) with hr'
    have hr₀ : r' p₀ = G p₀ - ∑ p' ∈ P, r p' / (p' - p₀) := if_pos rfl
    have hrP : ∀ p ∈ P, r' p = r p / (p - p₀) := fun p hp =>
      if_neg fun h => hp₀ (by rw [← h]; exact hp)
    refine ⟨r', dslope G p₀, (differentiableOn_dslope (hU.mem_nhds hp₀U)).mpr hG,
      fun z hz hzP => ?_⟩
    have hz₀ : z ≠ p₀ := fun h => hzP (by rw [h]; exact Finset.mem_insert_self _ _)
    have hzP' : z ∉ P := fun h => hzP (Finset.mem_insert_of_mem h)
    have hsub : z - p₀ ≠ 0 := sub_ne_zero.mpr hz₀
    have hsum : ∑ p ∈ P, r' p / (z - p) = ∑ p ∈ P, r p / (p - p₀) / (z - p) :=
      Finset.sum_congr rfl fun p hp => by rw [hrP p hp]
    -- partial fractions of `1/((z − p)(z − p₀))`
    have hkey : (∑ p ∈ P, r p / (z - p)) / (z - p₀) =
        ∑ p ∈ P, r p / (p - p₀) / (z - p) - (∑ p ∈ P, r p / (p - p₀)) / (z - p₀) := by
      rw [Finset.sum_div, Finset.sum_div, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun p hp => ?_
      have h1 : z - p ≠ 0 := sub_ne_zero.mpr fun h => hzP' (by rw [h]; exact hp)
      have h2 : p - p₀ ≠ 0 := sub_ne_zero.mpr fun h => hp₀ (by rw [← h]; exact hp)
      field_simp
      ring
    rw [dslope_of_ne _ hz₀, slope_def_field, hGeq z hz hzP', Finset.prod_insert hp₀,
      Finset.sum_insert hp₀, hr₀, hsum, mul_comm (z - p₀), ← div_div, sub_div, sub_div,
      sub_div, hkey]
    ring

end GaloisForLFunctions.InfiniteRankPurityTheory
