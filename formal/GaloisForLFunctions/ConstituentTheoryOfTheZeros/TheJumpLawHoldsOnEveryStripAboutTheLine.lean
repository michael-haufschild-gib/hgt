import GaloisForLFunctions.InfiniteRankPurityTheory.TheConstantTermsOnTheTwoSidesOfTheLineAgree
import Mathlib.Analysis.Complex.LocallyUniformLimit

/-!
# The jump law holds on every strip about the critical line

Let `G` have a generalized Dirichlet expansion `Σ b_i a_i^s` on `½ < Re s ≤ ½ + η` and an expansion
`Σ c_j q_j^s` on `½ − η ≤ Re s < ½`, both absolutely convergent, with arbitrary positive scales on
both sides, and let `Φ = −G ζ/s` be holomorphic on the strip `|Re s − ½| < η` and bounded near the
line. Then:

* the two series of fractional parts agree, `Σ b_i {a_i u} = Σ c_j {q_j u}`
  (`fractSeries_eq_of_strip`), and so do their jumps (`tsum_jump_eq_of_strip`);
* the two expansions carry the same weight at every scale `t > 0`
  (`mergedWeight_eq_of_strip`): the jump law at the points `1/(kt)` and Möbius inversion over `k`;
* if the two families are indexed by the same injective scales, they are equal, the expansion
  converges absolutely on the closed strip and `Φ = −(ζ/s) Σ b_i a_i^s` on the whole strip
  (`eq_riemannZeta_div_mul_tsum_of_strip`).

So the zeros of `ζ` cancel no pole of a function that has absolutely convergent expansions on the
two sides of the line: such a function continues across the line.

The strip of half-width `η` is carried onto the unit strip by `s = 2η s' + ½ − η`, which fixes the
critical line; on the side of the functions this is `g ↦ (2η)⁻¹ v^{−(½−η)/(2η)} g(v^{1/(2η)})`
(`rescale`, `mellin_rescale`).
-/

open Filter Topology Set MeasureTheory

noncomputable section

namespace GaloisForLFunctions.ConstituentTheoryOfTheZeros

open GaloisForLFunctions.InfiniteRankPurityTheory

variable {ι : Type*} {κ : Type*}

/-! ### Rescaling a strip about the line onto the unit strip -/

/-- `g̃(v) = (2η)⁻¹ v^{−(½−η)/(2η)} g(v^{1/(2η)})`: its Mellin transform at `−s'` is the transform
of `g` at `−(2η s' + ½ − η)`. -/
def rescale (η : ℝ) (g : ℝ → ℂ) (v : ℝ) : ℂ :=
  (v : ℂ) ^ (-(((1 / 2 - η) / (2 * η) : ℝ) : ℂ)) • ((((2 * η)⁻¹ : ℝ) : ℂ) • g (v ^ (2 * η)⁻¹))

theorem mellin_rescale {η : ℝ} (hη : 0 < η) (g : ℝ → ℂ) (s : ℂ) :
    mellin (rescale η g) (-s) = mellin g (-(((2 * η : ℝ) : ℂ) * s + ((1 / 2 - η : ℝ) : ℂ))) := by
  have hκ : (0 : ℝ) < 2 * η := by positivity
  have hηc : (η : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hη.ne'
  unfold rescale
  rw [mellin_cpow_smul, mellin_const_smul, mellin_comp_rpow, abs_of_pos (inv_pos.mpr hκ), inv_inv,
    Complex.real_smul, smul_eq_mul, ← mul_assoc, ← Complex.ofReal_mul, inv_mul_cancel₀ hκ.ne',
    Complex.ofReal_one, one_mul]
  congr 1
  push_cast
  field_simp
  ring

theorem measurable_rescale (η : ℝ) {g : ℝ → ℂ} (hg : Measurable g) : Measurable (rescale η g) := by
  have h := (Complex.measurable_ofReal.pow_const (-(((1 / 2 - η) / (2 * η) : ℝ) : ℂ))).smul
    ((hg.comp (measurable_id.pow_const ((2 * η)⁻¹))).const_smul ((((2 * η)⁻¹ : ℝ)) : ℂ))
  exact h

/-- A bound `O(u^σ)` becomes `O(v^{(σ − (½ − η))/(2η)})`. -/
theorem norm_rescale_le {η : ℝ} (hη : 0 < η) {g : ℝ → ℂ} {C σ : ℝ}
    (hb : ∀ u : ℝ, 0 < u → ‖g u‖ ≤ C * u ^ σ) {v : ℝ} (hv : 0 < v) :
    ‖rescale η g v‖ ≤ (2 * η)⁻¹ * C * v ^ ((σ - (1 / 2 - η)) / (2 * η)) := by
  have hκ : (0 : ℝ) < 2 * η := by positivity
  have hpow : v ^ (-((1 / 2 - η) / (2 * η))) * (v ^ (2 * η)⁻¹) ^ σ =
      v ^ ((σ - (1 / 2 - η)) / (2 * η)) := by
    rw [← Real.rpow_mul hv.le, ← Real.rpow_add hv]
    congr 1
    field_simp
    ring
  unfold rescale
  rw [norm_smul, norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos hv, Complex.neg_re,
    Complex.ofReal_re, Complex.norm_real, Real.norm_of_nonneg (inv_pos.mpr hκ).le]
  calc v ^ (-((1 / 2 - η) / (2 * η))) * ((2 * η)⁻¹ * ‖g (v ^ (2 * η)⁻¹)‖)
      ≤ v ^ (-((1 / 2 - η) / (2 * η))) * ((2 * η)⁻¹ * (C * (v ^ (2 * η)⁻¹) ^ σ)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (hb _ (Real.rpow_pos_of_pos hv _)) (inv_pos.mpr hκ).le)
          (Real.rpow_nonneg hv.le _)
    _ = (2 * η)⁻¹ * C * (v ^ (-((1 / 2 - η) / (2 * η))) * (v ^ (2 * η)⁻¹) ^ σ) := by ring
    _ = (2 * η)⁻¹ * C * v ^ ((σ - (1 / 2 - η)) / (2 * η)) := by rw [hpow]

/-! ### Two functions with one transform, on a strip of any width -/

/-- **Two functions with one transform agree, on any strip about the line.** Let `g₊ = O(u^σ)` for
`σ ∈ (½, ½ + η]` and `g₋ = O(u^σ)` for `σ ∈ [½ − η, ½)`, and let one function `F`, holomorphic on
`|Re s − ½| < η` and bounded on `|Re s − ½| ≤ η/2`, be `M[g₊](−s)` right of the line and
`M[g₋](−s)` left of it. Then `g₊ = g₋` at every point of continuity of `g₊ − g₋` other than `1`. -/
theorem eq_of_mellin_eq_on_strip {gR gL : ℝ → ℂ} (mR : Measurable gR) (mL : Measurable gL)
    {η : ℝ} (hη0 : 0 < η) {CR CL : ℝ → ℝ}
    (bR : ∀ σ : ℝ, 1 / 2 < σ → σ ≤ 1 / 2 + η → ∀ u : ℝ, 0 < u → ‖gR u‖ ≤ CR σ * u ^ σ)
    (bL : ∀ σ : ℝ, 1 / 2 - η ≤ σ → σ < 1 / 2 → ∀ u : ℝ, 0 < u → ‖gL u‖ ≤ CL σ * u ^ σ)
    {F : ℂ → ℂ} (hFd : DifferentiableOn ℂ F {s : ℂ | 1 / 2 - η < s.re ∧ s.re < 1 / 2 + η})
    {K : ℝ} (hFb : ∀ s : ℂ, 1 / 2 - η / 2 ≤ s.re → s.re ≤ 1 / 2 + η / 2 → ‖F s‖ ≤ K)
    (hFR : ∀ s : ℂ, 1 / 2 < s.re → s.re < 1 / 2 + η → F s = mellin gR (-s))
    (hFL : ∀ s : ℂ, 1 / 2 - η < s.re → s.re < 1 / 2 → F s = mellin gL (-s))
    {x₀ : ℝ} (hx₀ : 0 < x₀) (hx₀1 : x₀ ≠ 1) (hcont : ContinuousAt (fun u => gR u - gL u) x₀) :
    gR x₀ = gL x₀ := by
  have hκ : (0 : ℝ) < 2 * η := by positivity
  -- the affine map `s' ↦ 2η s' + ½ − η` and its real part
  set A : ℂ → ℂ := fun s => ((2 * η : ℝ) : ℂ) * s + ((1 / 2 - η : ℝ) : ℂ) with hA
  have hAre : ∀ s : ℂ, (A s).re = 2 * η * s.re + (1 / 2 - η) := fun s => by
    simp only [hA, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      sub_zero]
  have hσ : ∀ σ' : ℝ, (2 * η * σ' + (1 / 2 - η) - (1 / 2 - η)) / (2 * η) = σ' := fun σ' => by
    field_simp
    ring
  set v₀ : ℝ := x₀ ^ (2 * η) with hv₀
  have hv₀pos : 0 < v₀ := Real.rpow_pos_of_pos hx₀ _
  have hback : v₀ ^ (2 * η)⁻¹ = x₀ := by
    rw [hv₀, ← Real.rpow_mul hx₀.le, mul_inv_cancel₀ hκ.ne', Real.rpow_one]
  have hv₀1 : v₀ ≠ 1 := fun h => hx₀1 (by rw [← hback, h, Real.one_rpow])
  have key : rescale η gR v₀ = rescale η gL v₀ := by
    refine eq_of_mellin_eq_two_sided (measurable_rescale η mR) (measurable_rescale η mL)
      (CR := fun σ' => (2 * η)⁻¹ * CR (2 * η * σ' + (1 / 2 - η)))
      (CL := fun σ' => (2 * η)⁻¹ * CL (2 * η * σ' + (1 / 2 - η)))
      (F := fun s' => F (A s')) (K := K) (fun σ' h0 h1 v hv => ?_) (fun σ' h0 h1 v hv => ?_) ?_
      (fun s h0 h1 => ?_) (fun s h0 h1 => ?_) (fun s h0 h1 => ?_) hv₀pos hv₀1 ?_
    · have h := norm_rescale_le hη0 (bR (2 * η * σ' + (1 / 2 - η)) (by nlinarith) (by nlinarith)) hv
      rwa [hσ σ'] at h
    · have h := norm_rescale_le hη0 (bL (2 * η * σ' + (1 / 2 - η)) (by nlinarith) (by nlinarith)) hv
      rwa [hσ σ'] at h
    · refine hFd.comp (Differentiable.differentiableOn (by fun_prop)) fun s hs => ?_
      have h0 : 0 < s.re := hs.1
      have h1 : s.re < 1 := hs.2
      show 1 / 2 - η < (A s).re ∧ (A s).re < 1 / 2 + η
      rw [hAre]
      exact ⟨by nlinarith, by nlinarith⟩
    · exact hFb _ (by rw [hAre]; nlinarith) (by rw [hAre]; nlinarith)
    · show F (A s) = mellin (rescale η gR) (-s)
      rw [mellin_rescale hη0]
      exact hFR _ (by rw [hAre]; nlinarith) (by rw [hAre]; nlinarith)
    · show F (A s) = mellin (rescale η gL) (-s)
      rw [mellin_rescale hη0]
      exact hFL _ (by rw [hAre]; nlinarith) (by rw [hAre]; nlinarith)
    · -- continuity of the rescaled difference at `v₀`
      have hc1 : ContinuousAt (fun v : ℝ => v ^ (2 * η)⁻¹) v₀ :=
        Real.continuousAt_rpow_const _ _ (Or.inl hv₀pos.ne')
      have hc2 : ContinuousAt (fun v : ℝ => gR (v ^ (2 * η)⁻¹) - gL (v ^ (2 * η)⁻¹)) v₀ :=
        ContinuousAt.comp_of_eq hcont hc1 hback
      have hc3 : ContinuousAt
          (fun v : ℝ => (v : ℂ) ^ (-(((1 / 2 - η) / (2 * η) : ℝ) : ℂ))) v₀ :=
        Complex.continuousAt_ofReal_cpow_const _ _ (Or.inr hv₀pos.ne')
      refine (hc3.smul (hc2.const_smul ((((2 * η)⁻¹ : ℝ)) : ℂ))).congr
        (Eventually.of_forall fun v => ?_)
      simp only [rescale, Pi.smul_apply', Pi.smul_apply, smul_sub]
  -- cancel the nonzero factors
  simp only [rescale, hback, smul_eq_mul] at key
  have h1 : (v₀ : ℂ) ^ (-(((1 / 2 - η) / (2 * η) : ℝ) : ℂ)) ≠ 0 := by
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hv₀pos.ne')]
    exact Complex.exp_ne_zero _
  have h2 : (((2 * η)⁻¹ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (inv_pos.mpr hκ).ne'
  exact mul_left_cancel₀ h2 (mul_left_cancel₀ h1 key)

/-! ### The two series agree -/

/-- **The two series of fractional parts agree, on any strip about the line.** The scales of both
families are arbitrary positive reals. -/
theorem fractSeries_eq_of_strip [Countable ι] [Countable κ] {b : ι → ℂ} {a : ι → ℝ} {c : κ → ℂ}
    {q : κ → ℝ} (ha : ∀ i, 0 < a i) (hq : ∀ j, 0 < q j) {η : ℝ} (hη0 : 0 < η) (hη : η ≤ 1 / 2)
    (hR : ∀ σ : ℝ, 1 / 2 < σ → σ ≤ 1 / 2 + η → Summable fun i => ‖b i‖ * a i ^ σ)
    (hL : ∀ σ : ℝ, 1 / 2 - η ≤ σ → σ < 1 / 2 → Summable fun j => ‖c j‖ * q j ^ σ)
    {F : ℂ → ℂ} (hFd : DifferentiableOn ℂ F {s : ℂ | 1 / 2 - η < s.re ∧ s.re < 1 / 2 + η})
    {K : ℝ} (hFb : ∀ s : ℂ, 1 / 2 - η / 2 ≤ s.re → s.re ≤ 1 / 2 + η / 2 → ‖F s‖ ≤ K)
    (hFR : ∀ s : ℂ, 1 / 2 < s.re → s.re < 1 / 2 + η →
      F s = -(riemannZeta s / s) * ∑' i, b i * (a i : ℂ) ^ s)
    (hFL : ∀ s : ℂ, 1 / 2 - η < s.re → s.re < 1 / 2 →
      F s = -(riemannZeta s / s) * ∑' j, c j * (q j : ℂ) ^ s)
    {u : ℝ} (hu : 0 < u) : fractSeries b a u = fractSeries c q u := by
  have hRtop := hR (1 / 2 + η) (by linarith) le_rfl
  have hLbot := hL (1 / 2 - η) le_rfl (by linarith)
  have hinv : ∀ x : ℝ, 0 < x → x ≠ 1 →
      ContinuousAt (fun u => fractSeries b a u - fractSeries c q u) x →
      fractSeries b a x = fractSeries c q x := fun x hx hx1 hcont =>
    eq_of_mellin_eq_on_strip (measurable_fractSeries b a) (measurable_fractSeries c q) hη0
      (CR := fun σ => ∑' i, ‖b i‖ * a i ^ σ) (CL := fun σ => ∑' j, ‖c j‖ * q j ^ σ)
      (fun σ h0 h1 u hu => norm_fractSeries_le ha (by linarith) (by linarith) (hR σ h0 h1) hu.le)
      (fun σ h0 h1 u hu => norm_fractSeries_le hq (by linarith) (by linarith) (hL σ h0 h1) hu.le)
      hFd hFb
      (fun s h0 h1 => by
        rw [hFR s h0 h1, mellin_fractSeries ha (by linarith) (by linarith) (hR s.re h0 h1.le)])
      (fun s h0 h1 => by
        rw [hFL s h0 h1, mellin_fractSeries hq (by linarith) (by linarith) (hL s.re h0.le h1)])
      hx hx1 hcont
  -- points of continuity are dense; both series are right continuous
  have hbad : ({u : ℝ | ∃ i, ∃ n : ℤ, a i * u = n} ∪ {u : ℝ | ∃ j, ∃ n : ℤ, q j * u = n} ∪
      {1}).Countable :=
    ((countable_jumpSet ha).union (countable_jumpSet hq)).union (countable_singleton 1)
  have hfreq : ∃ᶠ x in 𝓝[>] u, fractSeries b a x = fractSeries c q x := by
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
    (tendsto_fractSeries_right ha (by linarith) (by linarith) hRtop hu)
    (tendsto_fractSeries_right hq (by linarith) (by linarith) hLbot hu) hfreq

open scoped Classical in
/-- **The jump law on a strip.** Under the hypotheses of `fractSeries_eq_of_strip` the two series
have the same jump at every `u₀ > 0`. -/
theorem tsum_jump_eq_of_strip [Countable ι] [Countable κ] {b : ι → ℂ} {a : ι → ℝ} {c : κ → ℂ}
    {q : κ → ℝ} (ha : ∀ i, 0 < a i) (hq : ∀ j, 0 < q j) {η : ℝ} (hη0 : 0 < η) (hη : η ≤ 1 / 2)
    (hR : ∀ σ : ℝ, 1 / 2 < σ → σ ≤ 1 / 2 + η → Summable fun i => ‖b i‖ * a i ^ σ)
    (hL : ∀ σ : ℝ, 1 / 2 - η ≤ σ → σ < 1 / 2 → Summable fun j => ‖c j‖ * q j ^ σ)
    {F : ℂ → ℂ} (hFd : DifferentiableOn ℂ F {s : ℂ | 1 / 2 - η < s.re ∧ s.re < 1 / 2 + η})
    {K : ℝ} (hFb : ∀ s : ℂ, 1 / 2 - η / 2 ≤ s.re → s.re ≤ 1 / 2 + η / 2 → ‖F s‖ ≤ K)
    (hFR : ∀ s : ℂ, 1 / 2 < s.re → s.re < 1 / 2 + η →
      F s = -(riemannZeta s / s) * ∑' i, b i * (a i : ℂ) ^ s)
    (hFL : ∀ s : ℂ, 1 / 2 - η < s.re → s.re < 1 / 2 →
      F s = -(riemannZeta s / s) * ∑' j, c j * (q j : ℂ) ^ s)
    {u₀ : ℝ} (hu₀ : 0 < u₀) :
    (∑' i, if ∃ n : ℤ, a i * u₀ = n then b i else 0) =
      ∑' j, if ∃ n : ℤ, q j * u₀ = n then c j else 0 := by
  have hRtop := hR (1 / 2 + η) (by linarith) le_rfl
  have hLbot := hL (1 / 2 - η) le_rfl (by linarith)
  have heq : ∀ u : ℝ, 0 < u → fractSeries b a u = fractSeries c q u := fun u hu =>
    fractSeries_eq_of_strip ha hq hη0 hη hR hL hFd hFb hFR hFL hu
  have hl1 := tendsto_fractSeries_left ha (by linarith) (by linarith) hRtop hu₀
  have hl2 := tendsto_fractSeries_left hq (by linarith) (by linarith) hLbot hu₀
  have hev : ∀ᶠ u in 𝓝[<] u₀, fractSeries b a u = fractSeries c q u := by
    filter_upwards [Ioo_mem_nhdsLT hu₀] with u hu
    exact heq u hu.1
  have hlim := tendsto_nhds_unique_of_frequently_eq hl1 hl2 hev.frequently
  have j1 := fractSeries_sub_leftLimit ha (by linarith) (by linarith) hRtop hu₀
  have j2 := fractSeries_sub_leftLimit hq (by linarith) (by linarith) hLbot hu₀
  rw [heq u₀ hu₀, hlim, j2] at j1
  exact neg_injective j1.symm

/-! ### Möbius inversion at every scale -/

open scoped Classical in
/-- The part of a family on the scales that are `t` times a natural number. -/
def natScalePart (b : ι → ℂ) (a : ι → ℝ) (t : ℝ) (i : ι) : ℂ :=
  if ∃ n : ℕ, a i / t = n then b i else 0

theorem natScalePart_of_nat {b : ι → ℂ} {a : ι → ℝ} {t : ℝ} {i : ι} (h : ∃ n : ℕ, a i / t = n) :
    natScalePart b a t i = b i := by
  classical
  exact if_pos h

theorem norm_natScalePart_le (b : ι → ℂ) (a : ι → ℝ) (t : ℝ) (i : ι) :
    ‖natScalePart b a t i‖ ≤ ‖b i‖ := by
  classical
  unfold natScalePart
  split_ifs
  · exact le_rfl
  · rw [norm_zero]
    exact norm_nonneg _

/-- On its support the scale ratio of `natScalePart` is at least one. -/
theorem one_le_of_natScalePart_ne_zero {b : ι → ℂ} {a : ι → ℝ} (ha : ∀ i, 0 < a i) {t : ℝ}
    (ht : 0 < t) {i : ι} (h : natScalePart b a t i ≠ 0) : 1 ≤ a i / t := by
  classical
  have hex : ∃ n : ℕ, a i / t = n := by
    by_contra hne
    exact h (if_neg hne)
  obtain ⟨n, hn⟩ := hex
  have hpos : 0 < a i / t := div_pos (ha i) ht
  rw [hn] at hpos ⊢
  have : 0 < n := by exact_mod_cast hpos
  exact_mod_cast this

/-- The part of a family on the scales that are `t` times a natural number is absolutely summable,
also against the fourth root of the scale ratio. -/
theorem summable_natScalePart {b : ι → ℂ} {a : ι → ℝ} (ha : ∀ i, 0 < a i) {σ : ℝ}
    (hσ : 1 / 4 ≤ σ) (hsum : Summable fun i => ‖b i‖ * a i ^ σ) {t : ℝ} (ht : 0 < t) :
    (Summable fun i => ‖natScalePart b a t i‖) ∧
      Summable fun i => ‖natScalePart b a t i‖ * (a i / t) ^ (1 / 4 : ℝ) := by
  have hdom : Summable fun i => ‖b i‖ * (a i / t) ^ σ :=
    (hsum.div_const (t ^ σ)).congr fun i => by
      rw [Real.div_rpow (ha i).le ht.le, mul_div_assoc]
  have hnn : ∀ i, 0 ≤ ‖b i‖ * (a i / t) ^ σ := fun i =>
    mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (div_pos (ha i) ht).le _)
  refine ⟨Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun i => ?_) hdom,
    Summable.of_nonneg_of_le (fun i => mul_nonneg (norm_nonneg _)
      (Real.rpow_nonneg (div_pos (ha i) ht).le _)) (fun i => ?_) hdom⟩
  · by_cases h : natScalePart b a t i = 0
    · rw [h, norm_zero]
      exact hnn i
    · exact (norm_natScalePart_le b a t i).trans (le_mul_of_one_le_right (norm_nonneg _)
        (Real.one_le_rpow (one_le_of_natScalePart_ne_zero ha ht h) (by linarith)))
  · by_cases h : natScalePart b a t i = 0
    · rw [h, norm_zero, zero_mul]
      exact hnn i
    · exact mul_le_mul (norm_natScalePart_le b a t i)
        (Real.rpow_le_rpow_of_exponent_le (one_le_of_natScalePart_ne_zero ha ht h) hσ)
        (Real.rpow_nonneg (div_pos (ha i) ht).le _) (norm_nonneg _)

open scoped Classical in
/-- **Möbius inversion for two families.** If two summable families with positive scales carry the
same weight on the natural scales divisible by `k`, for every `k ≥ 1`, they carry the same weight
at the scale one: `tsum_eq_of_tsum_dvd` for their difference on the disjoint union. -/
theorem tsum_one_eq_of_tsum_dvd_eq [Countable ι] [Countable κ] {b : ι → ℂ} {a : ι → ℝ}
    {c : κ → ℂ} {q : κ → ℝ} (ha : ∀ i, 0 < a i) (hq : ∀ j, 0 < q j)
    (hb1 : Summable fun i => ‖b i‖) (hb4 : Summable fun i => ‖b i‖ * a i ^ (1 / 4 : ℝ))
    (hc1 : Summable fun j => ‖c j‖) (hc4 : Summable fun j => ‖c j‖ * q j ^ (1 / 4 : ℝ))
    (hS : ∀ k : ℕ, 1 ≤ k → (∑' i, if (∃ n : ℕ, a i = n ∧ k ∣ n) then b i else 0) =
      ∑' j, if (∃ n : ℕ, q j = n ∧ k ∣ n) then c j else 0) :
    (∑' i, if a i = 1 then b i else 0) = ∑' j, if q j = 1 then c j else 0 := by
  have he0 : ∀ x : ι ⊕ κ, 0 < Sum.elim a q x := by
    rintro (i | j)
    · exact ha i
    · exact hq j
  have h1 : Summable ((fun x : ι ⊕ κ => ‖Sum.elim b (fun j => -c j) x‖) ∘ Sum.inl) := hb1
  have h2 : Summable ((fun x : ι ⊕ κ => ‖Sum.elim b (fun j => -c j) x‖) ∘ Sum.inr) := by
    simpa only [Function.comp_def, Sum.elim_inr, norm_neg] using hc1
  have hdsum : Summable fun x : ι ⊕ κ => ‖Sum.elim b (fun j => -c j) x‖ :=
    (h1.hasSum.sum h2.hasSum).summable
  have h3 : Summable ((fun x : ι ⊕ κ => ‖Sum.elim b (fun j => -c j) x‖ *
      Sum.elim a q x ^ (1 / 4 : ℝ)) ∘ Sum.inl) := hb4
  have h4 : Summable ((fun x : ι ⊕ κ => ‖Sum.elim b (fun j => -c j) x‖ *
      Sum.elim a q x ^ (1 / 4 : ℝ)) ∘ Sum.inr) := by
    simpa only [Function.comp_def, Sum.elim_inr, norm_neg] using hc4
  have hd4 : Summable fun x : ι ⊕ κ => ‖Sum.elim b (fun j => -c j) x‖ *
      Sum.elim a q x ^ (1 / 4 : ℝ) := (h3.hasSum.sum h4.hasSum).summable
  -- a conditional sum over the union is the difference of the two conditional sums
  have hsplit : ∀ P : ι ⊕ κ → Prop,
      (∑' x : ι ⊕ κ, if P x then Sum.elim b (fun j => -c j) x else 0) =
        (∑' i, if P (Sum.inl i) then b i else 0) - ∑' j, if P (Sum.inr j) then c j else 0 := by
    intro P
    have hsa : Summable ((fun x : ι ⊕ κ => if P x then Sum.elim b (fun j => -c j) x else 0) ∘
        Sum.inl) :=
      Summable.of_norm_bounded hb1 fun i => by
        simp only [Function.comp_def, Sum.elim_inl]
        split_ifs
        · exact le_rfl
        · rw [norm_zero]
          exact norm_nonneg _
    have hsq : Summable ((fun x : ι ⊕ κ => if P x then Sum.elim b (fun j => -c j) x else 0) ∘
        Sum.inr) :=
      Summable.of_norm_bounded hc1 fun j => by
        simp only [Function.comp_def, Sum.elim_inr]
        split_ifs
        · rw [norm_neg]
        · rw [norm_zero]
          exact norm_nonneg _
    have hneg : ∀ j, (if P (Sum.inr j) then -c j else 0) = -(if P (Sum.inr j) then c j else 0) :=
      fun j => by
        split_ifs
        · rfl
        · rw [neg_zero]
    rw [Summable.tsum_sum hsa hsq]
    simp only [Sum.elim_inl, Sum.elim_inr]
    rw [tsum_congr hneg, tsum_neg, sub_eq_add_neg]
  have hS' : ∀ k : ℕ, 1 ≤ k →
      (∑' x : ι ⊕ κ, if (∃ n : ℕ, Sum.elim a q x = n ∧ k ∣ n) then
        Sum.elim b (fun j => -c j) x else 0) = if k = 1 then (0 : ℂ) else 0 := by
    intro k hk
    rw [ite_self, hsplit fun x => ∃ n : ℕ, Sum.elim a q x = n ∧ k ∣ n]
    exact sub_eq_zero.mpr (hS k hk)
  have hmain := tsum_eq_of_tsum_dvd he0 hdsum hd4 hS'
  rw [hsplit fun x => Sum.elim a q x = 1] at hmain
  exact sub_eq_zero.mp hmain

open scoped Classical in
/-- A family restricted to the scales `t·n` with `k ∣ n` is its jump at `1/(kt)`. -/
theorem natScalePart_dvd_eq_jump {b : ι → ℂ} {a : ι → ℝ} (ha : ∀ i, 0 < a i) {t : ℝ}
    (ht : 0 < t) {k : ℕ} (hk : 1 ≤ k) (i : ι) :
    (if (∃ n : ℕ, a i / t = n ∧ k ∣ n) then natScalePart b a t i else 0) =
      if ∃ n : ℤ, a i * (1 / t * (1 / (k : ℝ))) = n then b i else 0 := by
  have hiff : (∃ n : ℤ, a i * (1 / t * (1 / (k : ℝ))) = n) ↔ ∃ n : ℕ, a i / t = n ∧ k ∣ n := by
    rw [← exists_int_mul_inv_iff (div_pos (ha i) ht) hk,
      show a i * (1 / t * (1 / (k : ℝ))) = a i / t * (1 / (k : ℝ)) by ring]
  by_cases h : ∃ n : ℕ, a i / t = n ∧ k ∣ n
  · obtain ⟨n, hn, hkn⟩ := h
    rw [if_pos ⟨n, hn, hkn⟩, if_pos (hiff.mpr ⟨n, hn, hkn⟩), natScalePart_of_nat ⟨n, hn⟩]
  · rw [if_neg h, if_neg fun h' => h (hiff.mp h')]

open scoped Classical in
/-- At the scale ratio one the restricted family is the family at the scale `t`. -/
theorem natScalePart_one_eq (b : ι → ℂ) (a : ι → ℝ) {t : ℝ} (ht : 0 < t) (i : ι) :
    (if a i / t = 1 then natScalePart b a t i else 0) = if a i = t then b i else 0 := by
  by_cases h : a i = t
  · have h1 : a i / t = 1 := by rw [h, div_self ht.ne']
    rw [if_pos h1, if_pos h, natScalePart_of_nat ⟨1, by rw [h1, Nat.cast_one]⟩]
  · rw [if_neg h, if_neg fun h' => h ((div_eq_one_iff_eq ht.ne').mp h')]

open scoped Classical in
/-- **From the jump law to the merged weights.** If two families with positive scales have the same
jump at every `u₀ > 0`, they carry the same weight at every scale `t > 0`: the points `1/(kt)`
and Möbius inversion over `k`. -/
theorem mergedWeight_eq_of_jump [Countable ι] [Countable κ] {b : ι → ℂ} {a : ι → ℝ} {c : κ → ℂ}
    {q : κ → ℝ} (ha : ∀ i, 0 < a i) (hq : ∀ j, 0 < q j) {σ₁ σ₂ : ℝ} (hσ₁ : 1 / 4 ≤ σ₁)
    (hσ₂ : 1 / 4 ≤ σ₂) (hb : Summable fun i => ‖b i‖ * a i ^ σ₁)
    (hc : Summable fun j => ‖c j‖ * q j ^ σ₂)
    (hjump : ∀ u₀ : ℝ, 0 < u₀ → (∑' i, if ∃ n : ℤ, a i * u₀ = n then b i else 0) =
      ∑' j, if ∃ n : ℤ, q j * u₀ = n then c j else 0)
    {t : ℝ} (ht : 0 < t) :
    (∑' i, if a i = t then b i else 0) = ∑' j, if q j = t then c j else 0 := by
  have ha' : ∀ i, 0 < a i / t := fun i => div_pos (ha i) ht
  have hq' : ∀ j, 0 < q j / t := fun j => div_pos (hq j) ht
  obtain ⟨hb1, hb4⟩ := summable_natScalePart ha hσ₁ hb ht
  obtain ⟨hc1, hc4⟩ := summable_natScalePart hq hσ₂ hc ht
  have hS : ∀ k : ℕ, 1 ≤ k →
      (∑' i, if (∃ n : ℕ, a i / t = n ∧ k ∣ n) then natScalePart b a t i else 0) =
        ∑' j, if (∃ n : ℕ, q j / t = n ∧ k ∣ n) then natScalePart c q t j else 0 := by
    intro k hk
    have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
    rw [tsum_congr (natScalePart_dvd_eq_jump (b := b) ha ht hk),
      tsum_congr (natScalePart_dvd_eq_jump (b := c) hq ht hk)]
    exact hjump _ (by positivity)
  have hmain := tsum_one_eq_of_tsum_dvd_eq ha' hq' hb1 hb4 hc1 hc4 hS
  rwa [tsum_congr (natScalePart_one_eq b a ht), tsum_congr (natScalePart_one_eq c q ht)] at hmain

open scoped Classical in
/-- **The two expansions carry the same weight at every scale.** Under the hypotheses of
`fractSeries_eq_of_strip`, for every `t > 0` the weight of the right family at the scale `t` equals
the weight of the left family there. No condition on the scales of either side. -/
theorem mergedWeight_eq_of_strip [Countable ι] [Countable κ] {b : ι → ℂ} {a : ι → ℝ} {c : κ → ℂ}
    {q : κ → ℝ} (ha : ∀ i, 0 < a i) (hq : ∀ j, 0 < q j) {η : ℝ} (hη0 : 0 < η) (hη : η ≤ 1 / 2)
    (hR : ∀ σ : ℝ, 1 / 2 < σ → σ ≤ 1 / 2 + η → Summable fun i => ‖b i‖ * a i ^ σ)
    (hL : ∀ σ : ℝ, 1 / 2 - η ≤ σ → σ < 1 / 2 → Summable fun j => ‖c j‖ * q j ^ σ)
    {F : ℂ → ℂ} (hFd : DifferentiableOn ℂ F {s : ℂ | 1 / 2 - η < s.re ∧ s.re < 1 / 2 + η})
    {K : ℝ} (hFb : ∀ s : ℂ, 1 / 2 - η / 2 ≤ s.re → s.re ≤ 1 / 2 + η / 2 → ‖F s‖ ≤ K)
    (hFR : ∀ s : ℂ, 1 / 2 < s.re → s.re < 1 / 2 + η →
      F s = -(riemannZeta s / s) * ∑' i, b i * (a i : ℂ) ^ s)
    (hFL : ∀ s : ℂ, 1 / 2 - η < s.re → s.re < 1 / 2 →
      F s = -(riemannZeta s / s) * ∑' j, c j * (q j : ℂ) ^ s)
    {t : ℝ} (ht : 0 < t) :
    (∑' i, if a i = t then b i else 0) = ∑' j, if q j = t then c j else 0 :=
  mergedWeight_eq_of_jump ha hq (σ₁ := 1 / 2 + η) (σ₂ := 1 / 2 - η / 2) (by linarith)
    (by linarith) (hR _ (by linarith) le_rfl) (hL _ (by linarith) (by linarith))
    (fun _ hu₀ => tsum_jump_eq_of_strip ha hq hη0 hη hR hL hFd hFb hFR hFL hu₀) ht

/-! ### Continuation across the line -/

/-- Between two exponents a power is at most the sum of the powers at the ends. -/
theorem rpow_le_add_rpow {x : ℝ} (hx : 0 < x) {σ₁ σ σ₂ : ℝ} (h₁ : σ₁ ≤ σ) (h₂ : σ ≤ σ₂) :
    x ^ σ ≤ x ^ σ₁ + x ^ σ₂ := by
  rcases le_total x 1 with h | h
  · exact (Real.rpow_le_rpow_of_exponent_ge hx h h₁).trans
      (le_add_of_nonneg_right (Real.rpow_nonneg hx.le _))
  · exact (Real.rpow_le_rpow_of_exponent_le h h₂).trans
      (le_add_of_nonneg_left (Real.rpow_nonneg hx.le _))

/-- Two families over the same injective positive scales, indexed by a countable set, that
represent one function on the two sides of the line are equal. -/
theorem eq_of_strip_of_countable [Countable ι] {b c : ι → ℂ} {a : ι → ℝ}
    (ha : ∀ i, 0 < a i) (hinj : Function.Injective a) {η : ℝ} (hη0 : 0 < η) (hη : η ≤ 1 / 2)
    (hR : ∀ σ : ℝ, 1 / 2 < σ → σ ≤ 1 / 2 + η → Summable fun i => ‖b i‖ * a i ^ σ)
    (hL : ∀ σ : ℝ, 1 / 2 - η ≤ σ → σ < 1 / 2 → Summable fun i => ‖c i‖ * a i ^ σ)
    {F : ℂ → ℂ} (hFd : DifferentiableOn ℂ F {s : ℂ | 1 / 2 - η < s.re ∧ s.re < 1 / 2 + η})
    {K : ℝ} (hFb : ∀ s : ℂ, 1 / 2 - η / 2 ≤ s.re → s.re ≤ 1 / 2 + η / 2 → ‖F s‖ ≤ K)
    (hFR : ∀ s : ℂ, 1 / 2 < s.re → s.re < 1 / 2 + η →
      F s = -(riemannZeta s / s) * ∑' i, b i * (a i : ℂ) ^ s)
    (hFL : ∀ s : ℂ, 1 / 2 - η < s.re → s.re < 1 / 2 →
      F s = -(riemannZeta s / s) * ∑' i, c i * (a i : ℂ) ^ s) : b = c := by
  classical
  funext i
  have h := mergedWeight_eq_of_strip ha ha hη0 hη hR hL hFd hFb hFR hFL (ha i)
  rw [tsum_eq_single i fun i' hi' => if_neg fun h' => hi' (hinj h'),
    tsum_eq_single i fun i' hi' => if_neg fun h' => hi' (hinj h'), if_pos rfl, if_pos rfl] at h
  exact h

/-- The same for index sets of any size: an absolutely summable family has countable support, and
the two families are compared on the union of the supports. -/
theorem eq_of_strip {b c : ι → ℂ} {a : ι → ℝ}
    (ha : ∀ i, 0 < a i) (hinj : Function.Injective a) {η : ℝ} (hη0 : 0 < η) (hη : η ≤ 1 / 2)
    (hR : ∀ σ : ℝ, 1 / 2 < σ → σ ≤ 1 / 2 + η → Summable fun i => ‖b i‖ * a i ^ σ)
    (hL : ∀ σ : ℝ, 1 / 2 - η ≤ σ → σ < 1 / 2 → Summable fun i => ‖c i‖ * a i ^ σ)
    {F : ℂ → ℂ} (hFd : DifferentiableOn ℂ F {s : ℂ | 1 / 2 - η < s.re ∧ s.re < 1 / 2 + η})
    {K : ℝ} (hFb : ∀ s : ℂ, 1 / 2 - η / 2 ≤ s.re → s.re ≤ 1 / 2 + η / 2 → ‖F s‖ ≤ K)
    (hFR : ∀ s : ℂ, 1 / 2 < s.re → s.re < 1 / 2 + η →
      F s = -(riemannZeta s / s) * ∑' i, b i * (a i : ℂ) ^ s)
    (hFL : ∀ s : ℂ, 1 / 2 - η < s.re → s.re < 1 / 2 →
      F s = -(riemannZeta s / s) * ∑' i, c i * (a i : ℂ) ^ s) : b = c := by
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
  have h := eq_of_strip_of_countable (b := fun i : S => b i) (c := fun i : S => c i)
    (a := fun i : S => a i) (fun i => ha i) (hinj.comp Subtype.val_injective) hη0 hη
    (fun σ h1 h2 => (hR σ h1 h2).subtype S) (fun σ h1 h2 => (hL σ h1 h2).subtype S) hFd hFb
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

/-- **The zeros of `ζ` cancel no pole of a two-sided expansion.** Let two families over the same
injective positive scales represent `−sΦ/ζ` on the two sides of the line, absolutely, in a strip
about the line in which `Φ` is holomorphic and bounded near the line. Then the families are equal,
the expansion converges absolutely on the closed strip, and it represents `−sΦ/ζ` on the whole
strip: nothing was cancelled on the line. The index set may be uncountable. -/
theorem eq_riemannZeta_div_mul_tsum_of_strip {b c : ι → ℂ} {a : ι → ℝ}
    (ha : ∀ i, 0 < a i) (hinj : Function.Injective a) {η : ℝ} (hη0 : 0 < η) (hη : η ≤ 1 / 2)
    (hR : ∀ σ : ℝ, 1 / 2 < σ → σ ≤ 1 / 2 + η → Summable fun i => ‖b i‖ * a i ^ σ)
    (hL : ∀ σ : ℝ, 1 / 2 - η ≤ σ → σ < 1 / 2 → Summable fun i => ‖c i‖ * a i ^ σ)
    {F : ℂ → ℂ} (hFd : DifferentiableOn ℂ F {s : ℂ | 1 / 2 - η < s.re ∧ s.re < 1 / 2 + η})
    {K : ℝ} (hFb : ∀ s : ℂ, 1 / 2 - η / 2 ≤ s.re → s.re ≤ 1 / 2 + η / 2 → ‖F s‖ ≤ K)
    (hFR : ∀ s : ℂ, 1 / 2 < s.re → s.re < 1 / 2 + η →
      F s = -(riemannZeta s / s) * ∑' i, b i * (a i : ℂ) ^ s)
    (hFL : ∀ s : ℂ, 1 / 2 - η < s.re → s.re < 1 / 2 →
      F s = -(riemannZeta s / s) * ∑' i, c i * (a i : ℂ) ^ s) :
    b = c ∧ (∀ σ : ℝ, 1 / 2 - η ≤ σ → σ ≤ 1 / 2 + η → Summable fun i => ‖b i‖ * a i ^ σ) ∧
      ∀ s : ℂ, 1 / 2 - η < s.re → s.re < 1 / 2 + η →
        F s = -(riemannZeta s / s) * ∑' i, b i * (a i : ℂ) ^ s := by
  classical
  have hbc : b = c := eq_of_strip ha hinj hη0 hη hR hL hFd hFb hFR hFL
  subst hbc
  have hbot := hL (1 / 2 - η) le_rfl (by linarith)
  have htop := hR (1 / 2 + η) (by linarith) le_rfl
  have hdom : Summable fun i => ‖b i‖ * a i ^ (1 / 2 - η) + ‖b i‖ * a i ^ (1 / 2 + η) :=
    hbot.add htop
  have hsumall : ∀ σ : ℝ, 1 / 2 - η ≤ σ → σ ≤ 1 / 2 + η → Summable fun i => ‖b i‖ * a i ^ σ :=
    fun σ h1 h2 => Summable.of_nonneg_of_le
      (fun i => mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (ha i).le _))
      (fun i => by
        rw [← mul_add]
        exact mul_le_mul_of_nonneg_left (rpow_le_add_rpow (ha i) h1 h2) (norm_nonneg _)) hdom
  refine ⟨rfl, hsumall, ?_⟩
  -- the expansion is holomorphic on the strip and agrees with `F` right of the line
  set U : Set ℂ := {s : ℂ | 1 / 2 - η < s.re ∧ s.re < 1 / 2 + η} with hU
  have hUo : IsOpen U :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)
  have hUc : IsPreconnected U :=
    ((convex_halfSpace_re_gt _).inter (convex_halfSpace_re_lt _)).isPreconnected
  have hHd : DifferentiableOn ℂ (fun s => ∑' i, b i * (a i : ℂ) ^ s) U := by
    refine Complex.differentiableOn_tsum_of_summable_norm hdom (fun i s _ => ?_) hUo fun i s hs => ?_
    · exact ((differentiableAt_id.const_cpow
        (Or.inl (Complex.ofReal_ne_zero.mpr (ha i).ne'))).const_mul (b i)).differentiableWithinAt
    · rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (ha i), ← mul_add]
      exact mul_le_mul_of_nonneg_left (rpow_le_add_rpow (ha i) hs.1.le hs.2.le) (norm_nonneg _)
  have hGd : DifferentiableOn ℂ (fun s => -(riemannZeta s / s) * ∑' i, b i * (a i : ℂ) ^ s) U := by
    intro z hz
    have hz1 : z ≠ 1 := fun h => by
      have := hz.2
      rw [h, Complex.one_re] at this
      linarith
    have hz0 : z ≠ 0 := fun h => by
      have := hz.1
      rw [h, Complex.zero_re] at this
      linarith
    exact (((differentiableAt_riemannZeta hz1).div differentiableAt_id hz0).neg.differentiableWithinAt).mul
      (hHd z hz)
  have hz₀ : (((1 / 2 + η / 2 : ℝ)) : ℂ) ∈ U := by
    show 1 / 2 - η < (((1 / 2 + η / 2 : ℝ)) : ℂ).re ∧ (((1 / 2 + η / 2 : ℝ)) : ℂ).re < 1 / 2 + η
    rw [Complex.ofReal_re]
    exact ⟨by linarith, by linarith⟩
  have hev : F =ᶠ[𝓝 (((1 / 2 + η / 2 : ℝ)) : ℂ)]
      fun s => -(riemannZeta s / s) * ∑' i, b i * (a i : ℂ) ^ s := by
    have hopen : {z : ℂ | 1 / 2 < z.re ∧ z.re < 1 / 2 + η} ∈ 𝓝 (((1 / 2 + η / 2 : ℝ)) : ℂ) :=
      ((isOpen_lt continuous_const Complex.continuous_re).inter
        (isOpen_lt Complex.continuous_re continuous_const)).mem_nhds (by
          show 1 / 2 < (((1 / 2 + η / 2 : ℝ)) : ℂ).re ∧ (((1 / 2 + η / 2 : ℝ)) : ℂ).re < 1 / 2 + η
          rw [Complex.ofReal_re]
          exact ⟨by linarith, by linarith⟩)
    filter_upwards [hopen] with z hz
    exact hFR z hz.1 hz.2
  intro s h1 h2
  exact (hFd.analyticOnNhd hUo).eqOn_of_preconnected_of_eventuallyEq (hGd.analyticOnNhd hUo) hUc
    hz₀ hev ⟨h1, h2⟩

end GaloisForLFunctions.ConstituentTheoryOfTheZeros
