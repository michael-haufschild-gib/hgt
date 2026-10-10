import GaloisForLFunctions.RHTower.XiReciprocalSliceCriterion
import GaloisForLFunctions.RHTower.XiReciprocalSlicePolyaFrequency
import GaloisForLFunctions.HTGeometry.ReciprocalDoubleShadowing
import GaloisForLFunctions.RHTower.WeightedScrewPoleContradiction

/-!
# A dominant real zero forces reciprocal slice positivity

Let `t` be a height with `Ξ(t) ≠ 0`.  Let `γ` be a real zero of `Ξ` at distance `d = |t − γ|`, and
let `S = Σ_{z ≠ γ} 1/|z − t|²` run over the other zeros of `Ξ`, with multiplicity.

**Theorem** (`xiReciprocalSlicePositive_of_dominant_zero`).  If `d² S ≤ 1/20`, then every Taylor
coefficient of `1/(Ξ(t+σ)Ξ(t−σ))` at `σ = 0` is nonnegative.

This is a converse companion of the nearest-zero law
(`xi_critical_zero_at_nearest_distance_of_reciprocal_nonneg`): reciprocal positivity at `t` forces
the nearest zero to be real, and a real zero that is close enough relative to the others forces
reciprocal positivity.

Proof.  Write `Ξ(z) = (z − γ)Φ(z)`, so `h_t(σ) = h_t(0)(1 − σ²/d²)Ψ(σ)` with
`Ψ(σ) = Φ(t+σ)Φ(t−σ)/Φ(t)²` entire and `Ψ(0) = 1`.
* The canonical product gives `Ψ(σ) = lim Π_{z ≠ γ}(1 − σ²/(z − t)²)` (`tendsto_prod_erase`).
  On the disk `|σ| ≤ r = √3 d`, the bound `1 − y ≥ e^{−2y}` gives `|Ψ| ≥ e^{−6 d² S} ≥ e^{−3/10}`.
* Cauchy's estimate on the circle `|σ| = r` gives coefficients `|ψ_k| ≤ e^{3/10}/(3d²)^k` for
  `1/Ψ`.
* The coefficient of `σ^{2n}` in `1/h_t` is `h_t(0)^{−1} d^{−2n} Σ_{k ≤ n} d^{2k} ψ_k`.  Its real
  part is at least `h_t(0)^{−1} d^{−2n} (1 − e^{3/10}/2) > 0`.
-/

open Complex Filter Topology Metric
open scoped ComplexOrder Nat
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-- The genus-one pair identity `E₁((t+σ)/z) E₁((t−σ)/z) = (1 − σ²/(z−t)²) E₁(t/z)²`. -/
theorem weierstrassE1_pair_eq (t σ z : ℂ) (hz : z ≠ 0) (hzt : z ≠ t) :
    weierstrassE1 ((t + σ) / z) * weierstrassE1 ((t - σ) / z) =
      (1 - σ ^ 2 / (z - t) ^ 2) * weierstrassE1 (t / z) ^ 2 := by
  unfold weierstrassE1
  have hexp : Complex.exp ((t + σ) / z) * Complex.exp ((t - σ) / z) =
      Complex.exp (t / z) ^ 2 := by
    rw [← Complex.exp_add, sq, ← Complex.exp_add]
    congr 1
    ring
  have hzt' : z - t ≠ 0 := sub_ne_zero.mpr hzt
  calc (1 - (t + σ) / z) * Complex.exp ((t + σ) / z) * ((1 - (t - σ) / z) *
        Complex.exp ((t - σ) / z))
      = ((1 - (t + σ) / z) * (1 - (t - σ) / z)) *
          (Complex.exp ((t + σ) / z) * Complex.exp ((t - σ) / z)) := by ring
    _ = (1 - σ ^ 2 / (z - t) ^ 2) * ((1 - t / z) * Complex.exp (t / z)) ^ 2 := by
        rw [hexp]
        field_simp
        ring

theorem xiSpectralPoint_ne_ofReal {t : ℝ} (ht : XiC t ≠ 0) (q : XiZeroCopy) :
    xiSpectralPoint q ≠ (t : ℂ) := by
  intro h
  apply ht
  rw [← h]
  exact XiC_xiSpectralPoint_eq_zero q

/-- **The normalized product over the zeros.** -/
theorem tendsto_prod_one_sub_sq_div {t : ℝ} (ht : XiC t ≠ 0) (σ : ℂ) :
    Tendsto (fun S : Finset XiZeroCopy =>
        ∏ q ∈ S, (1 - σ ^ 2 / (xiSpectralPoint q - t) ^ 2)) atTop
      (𝓝 (xiHorizontalPair t σ / xiHorizontalPair t 0)) := by
  have hP : TendstoLocallyUniformlyOn
      (fun S x => ∏ q ∈ S, weierstrassE1 (x / xiSpectralPoint q)) xiCanonicalProduct atTop
      Set.univ := xiCanonicalProduct_hasProdLocallyUniformlyOn
  have hpt : ∀ x : ℂ, Tendsto (fun S : Finset XiZeroCopy =>
      ∏ q ∈ S, weierstrassE1 (x / xiSpectralPoint q)) atTop (𝓝 (xiCanonicalProduct x)) :=
    fun x => hP.tendsto_at (Set.mem_univ x)
  have hX : ∀ a, XiC a = XiC 0 * xiCanonicalProduct a := fun a => by
    simpa only [Pi.mul_apply] using congrFun XiC_eq_constant_mul_canonicalProduct a
  have hX0 : XiC 0 ≠ 0 := by
    have : XiC 0 = xi (((1 / 2 : ℝ)) : ℂ) := by simp [XiC]
    rw [this]
    exact xi_ne_zero_of_real _
  have hCt : xiCanonicalProduct t ≠ 0 := by
    intro h
    apply ht
    rw [hX, h, mul_zero]
  have hE : ∀ q : XiZeroCopy, weierstrassE1 ((t : ℂ) / xiSpectralPoint q) ≠ 0 := by
    intro q
    unfold weierstrassE1
    refine mul_ne_zero ?_ (Complex.exp_ne_zero _)
    rw [sub_ne_zero, ne_comm, Ne, div_eq_one_iff_eq (xiSpectralPoint_ne_zero q)]
    exact fun h => xiSpectralPoint_ne_ofReal ht q h.symm
  have hnum := ((hpt ((t : ℂ) + σ)).mul (hpt ((t : ℂ) - σ)))
  have hden := (hpt (t : ℂ)).pow 2
  have hlim := hnum.div hden (pow_ne_zero 2 hCt)
  have heq : ∀ S : Finset XiZeroCopy, ∏ q ∈ S, (1 - σ ^ 2 / (xiSpectralPoint q - t) ^ 2) =
      (∏ q ∈ S, weierstrassE1 (((t : ℂ) + σ) / xiSpectralPoint q)) *
          (∏ q ∈ S, weierstrassE1 (((t : ℂ) - σ) / xiSpectralPoint q)) /
        (∏ q ∈ S, weierstrassE1 ((t : ℂ) / xiSpectralPoint q)) ^ 2 := by
    intro S
    have hden : (∏ q ∈ S, weierstrassE1 ((t : ℂ) / xiSpectralPoint q)) ^ 2 ≠ 0 :=
      pow_ne_zero 2 (Finset.prod_ne_zero_iff.mpr fun q _ => hE q)
    rw [eq_div_iff hden, ← Finset.prod_pow, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun q _ => ?_
    rw [weierstrassE1_pair_eq _ _ _ (xiSpectralPoint_ne_zero q) (xiSpectralPoint_ne_ofReal ht q)]
  have hval : xiCanonicalProduct ((t : ℂ) + σ) * xiCanonicalProduct ((t : ℂ) - σ) /
      xiCanonicalProduct t ^ 2 = xiHorizontalPair t σ / xiHorizontalPair t 0 := by
    unfold xiHorizontalPair
    rw [hX ((t : ℂ) + σ), hX ((t : ℂ) - σ), add_zero, sub_zero, hX (t : ℂ)]
    field_simp
  rw [← hval]
  exact hlim.congr fun S => (heq S).symm

/-- `e^{−2y} ≤ 1 − y` on `[0, ½]`. -/
theorem exp_neg_two_mul_le_one_sub {y : ℝ} (hy0 : 0 ≤ y) (hy : y ≤ 1 / 2) :
    Real.exp (-(2 * y)) ≤ 1 - y := by
  have h1 := Real.add_one_le_exp (2 * y)
  have hpos : 0 < Real.exp (2 * y) := Real.exp_pos _
  rw [Real.exp_neg, inv_le_iff_one_le_mul₀ hpos]
  nlinarith

/-- A lower bound for a finite product of factors `1 − σ²/(z−t)²`. -/
theorem norm_prod_one_sub_sq_div_ge {t : ℝ} (F : Finset XiZeroCopy) {σ : ℂ} {r : ℝ}
    (hσ : ‖σ‖ ≤ r) (hr : ∀ q ∈ F, r ^ 2 / ‖xiSpectralPoint q - t‖ ^ 2 ≤ 1 / 2)
    (hne : ∀ q ∈ F, xiSpectralPoint q ≠ (t : ℂ)) :
    Real.exp (-(2 * r ^ 2 * ∑ q ∈ F, 1 / ‖xiSpectralPoint q - t‖ ^ 2)) ≤
      ‖∏ q ∈ F, (1 - σ ^ 2 / (xiSpectralPoint q - t) ^ 2)‖ := by
  rw [norm_prod, Finset.mul_sum, ← Finset.sum_neg_distrib, Real.exp_sum]
  refine Finset.prod_le_prod (fun q _ => (Real.exp_pos _).le) fun q hq => ?_
  have hzt : 0 < ‖xiSpectralPoint q - t‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (hne q hq))
  have hx : ‖σ ^ 2 / (xiSpectralPoint q - t) ^ 2‖ ≤ r ^ 2 / ‖xiSpectralPoint q - t‖ ^ 2 := by
    rw [norm_div, norm_pow, norm_pow]
    have := pow_le_pow_left₀ (norm_nonneg σ) hσ 2
    exact div_le_div_of_nonneg_right this (by positivity)
  have hy := hr q hq
  calc Real.exp (-(2 * r ^ 2 * (1 / ‖xiSpectralPoint q - t‖ ^ 2)))
      = Real.exp (-(2 * (r ^ 2 / ‖xiSpectralPoint q - t‖ ^ 2))) := by ring_nf
    _ ≤ 1 - r ^ 2 / ‖xiSpectralPoint q - t‖ ^ 2 :=
        exp_neg_two_mul_le_one_sub (by positivity) hy
    _ ≤ 1 - ‖σ ^ 2 / (xiSpectralPoint q - t) ^ 2‖ := by linarith
    _ ≤ ‖1 - σ ^ 2 / (xiSpectralPoint q - t) ^ 2‖ := by
        have := norm_sub_norm_le (1 : ℂ) (σ ^ 2 / (xiSpectralPoint q - t) ^ 2)
        rw [norm_one] at this
        exact this

theorem exp_three_tenths_lt_two : Real.exp (3 / 10) < 2 := by
  have h := Real.log_two_gt_d9
  calc Real.exp (3 / 10) < Real.exp (Real.log 2) := Real.exp_lt_exp.mpr (by norm_num at h ⊢; linarith)
    _ = 2 := Real.exp_log (by norm_num)

/-- **A dominant real zero forces reciprocal slice positivity.** -/
theorem xiReciprocalSlicePositive_of_dominant_zero {t γ : ℝ} (ht : XiC t ≠ 0)
    (q₀ : XiZeroCopy) (hq₀ : xiSpectralPoint q₀ = (γ : ℂ))
    (hS : ∀ F : Finset XiZeroCopy, q₀ ∉ F →
      (t - γ) ^ 2 * ∑ q ∈ F, 1 / ‖xiSpectralPoint q - t‖ ^ 2 ≤ 1 / 20) :
    XiReciprocalSlicePositive t := by
  set d : ℝ := t - γ with hd
  have hγ0 : XiC (γ : ℂ) = 0 := by rw [← hq₀]; exact XiC_xiSpectralPoint_eq_zero q₀
  have hd0 : d ≠ 0 := by
    intro h
    apply ht
    rw [show t = γ by linarith [h]]
    exact hγ0
  have hdc : (d : ℂ) ≠ 0 := by exact_mod_cast hd0
  have hdC : (d : ℂ) = (t : ℂ) - (γ : ℂ) := by simp only [hd]; push_cast; ring
  have hd2 : 0 < d ^ 2 := by positivity
  -- the factorization `Ξ(z) = (z − γ) Φ(z)`
  set Φ : ℂ → ℂ := dslope XiC (γ : ℂ) with hΦ
  have hΦdiff : Differentiable ℂ Φ := differentiable_dslope_entire XiC_differentiable _
  have hfac : ∀ z, XiC z = (z - γ) * Φ z := by
    intro z
    have := sub_smul_dslope XiC (γ : ℂ) z
    rw [hγ0, sub_zero, smul_eq_mul] at this
    exact this.symm
  have hΦt : Φ t ≠ 0 := by
    intro h
    apply ht
    rw [hfac, h, mul_zero]
  set Ψ : ℂ → ℂ := fun σ => Φ ((t : ℂ) + σ) * Φ ((t : ℂ) - σ) / Φ t ^ 2 with hΨ
  have hΨdiff : Differentiable ℂ Ψ := by
    have h1 : Differentiable ℂ (fun σ : ℂ => Φ ((t : ℂ) + σ)) := hΦdiff.comp (by fun_prop)
    have h2 : Differentiable ℂ (fun σ : ℂ => Φ ((t : ℂ) - σ)) := hΦdiff.comp (by fun_prop)
    exact (h1.mul h2).div_const _
  have hΨ0 : Ψ 0 = 1 := by
    simp only [hΨ, add_zero, sub_zero]
    field_simp
  have hh0 : xiHorizontalPair t 0 = (d : ℂ) ^ 2 * Φ t ^ 2 := by
    unfold xiHorizontalPair
    rw [add_zero, sub_zero, hfac, hdC]
    ring
  have hh : ∀ σ, xiHorizontalPair t σ =
      xiHorizontalPair t 0 * ((1 - (1 / (d : ℂ) ^ 2) * σ ^ 2) * Ψ σ) := by
    intro σ
    rw [hh0]
    unfold xiHorizontalPair
    rw [hfac ((t : ℂ) + σ), hfac ((t : ℂ) - σ)]
    have e1 : (t : ℂ) + σ - γ = d + σ := by rw [hdC]; ring
    have e2 : (t : ℂ) - σ - γ = d - σ := by rw [hdC]; ring
    rw [e1, e2]
    simp only [hΨ]
    field_simp
    ring
  -- the product over the other zeros converges to `Ψ`
  have hq₀d : xiSpectralPoint q₀ - t = -(d : ℂ) := by rw [hq₀, hd]; push_cast; ring
  have hlimΨ : ∀ σ : ℂ, σ ^ 2 ≠ (d : ℂ) ^ 2 → Tendsto (fun S : Finset XiZeroCopy =>
      ∏ q ∈ S.erase q₀, (1 - σ ^ 2 / (xiSpectralPoint q - t) ^ 2)) atTop (𝓝 (Ψ σ)) := by
    intro σ hσd
    have hT := tendsto_prod_one_sub_sq_div ht σ
    have hf0 : (1 - σ ^ 2 / (xiSpectralPoint q₀ - t) ^ 2) ≠ 0 := by
      rw [hq₀d, neg_sq, sub_ne_zero, ne_comm, Ne, div_eq_one_iff_eq (pow_ne_zero 2 hdc)]
      exact hσd
    have hT' := hT.div_const (1 - σ ^ 2 / (xiSpectralPoint q₀ - t) ^ 2)
    have hval : xiHorizontalPair t σ / xiHorizontalPair t 0 /
        (1 - σ ^ 2 / (xiSpectralPoint q₀ - t) ^ 2) = Ψ σ := by
      have hh0ne : xiHorizontalPair t 0 ≠ 0 := by
        rw [hh0]
        exact mul_ne_zero (pow_ne_zero 2 hdc) (pow_ne_zero 2 hΦt)
      rw [hh σ, hq₀d, neg_sq]
      field_simp
    rw [hval] at hT'
    refine hT'.congr' ?_
    filter_upwards [eventually_ge_atTop {q₀}] with S hS
    have hmem : q₀ ∈ S := hS (Finset.mem_singleton_self q₀)
    rw [← Finset.mul_prod_erase S _ hmem]
    field_simp
  -- the radius `r = √3 d`
  set r : ℝ := Real.sqrt 3 * |d| with hr
  have hr2 : r ^ 2 = 3 * d ^ 2 := by
    rw [hr, mul_pow, Real.sq_sqrt (by norm_num), sq_abs]
  have hrpos : 0 < r := by positivity
  have hsingle : ∀ q, q ≠ q₀ → d ^ 2 / ‖xiSpectralPoint q - t‖ ^ 2 ≤ 1 / 20 := by
    intro q hq
    have := hS {q} (by simpa [eq_comm] using hq)
    simpa [div_eq_mul_inv] using this
  have hneq : ∀ q, q ≠ q₀ → xiSpectralPoint q ≠ (t : ℂ) := fun q _ => xiSpectralPoint_ne_ofReal ht q
  have hfar : ∀ q, q ≠ q₀ → 20 * d ^ 2 ≤ ‖xiSpectralPoint q - t‖ ^ 2 := by
    intro q hq
    have hpos : 0 < ‖xiSpectralPoint q - t‖ ^ 2 :=
      pow_pos (norm_pos_iff.mpr (sub_ne_zero.mpr (hneq q hq))) 2
    have := hsingle q hq
    rw [div_le_iff₀ hpos] at this
    linarith
  -- the lower bound on the punctured disk
  have hbound : ∀ σ : ℂ, ‖σ‖ ≤ r → σ ^ 2 ≠ (d : ℂ) ^ 2 → Real.exp (-(3 / 10)) ≤ ‖Ψ σ‖ := by
    intro σ hσ hσd
    refine ge_of_tendsto ((hlimΨ σ hσd).norm) ?_
    refine Eventually.of_forall fun S => ?_
    have hnotmem : q₀ ∉ S.erase q₀ := Finset.notMem_erase q₀ S
    have hr' : ∀ q ∈ S.erase q₀, r ^ 2 / ‖xiSpectralPoint q - t‖ ^ 2 ≤ 1 / 2 := by
      intro q hq
      have hq' := (Finset.mem_erase.mp hq).1
      rw [hr2]
      have := hsingle q hq'
      have hpos : 0 < ‖xiSpectralPoint q - t‖ ^ 2 :=
        pow_pos (norm_pos_iff.mpr (sub_ne_zero.mpr (hneq q hq'))) 2
      rw [div_le_iff₀ hpos] at this ⊢
      linarith
    have hP := norm_prod_one_sub_sq_div_ge (S.erase q₀) hσ hr'
      (fun q hq => hneq q (Finset.mem_erase.mp hq).1)
    refine le_trans ?_ hP
    apply Real.exp_le_exp.mpr
    have hsum := hS (S.erase q₀) hnotmem
    rw [hr2]
    nlinarith
  have hbound' : ∀ σ : ℂ, ‖σ‖ ≤ r → Real.exp (-(3 / 10)) ≤ ‖Ψ σ‖ := by
    intro σ hσ
    by_cases hσd : σ ^ 2 = (d : ℂ) ^ 2
    · -- approach `σ` radially from inside
      have hσne : σ ≠ 0 := by
        intro h
        rw [h] at hσd
        simp at hσd
        exact hdc (by simpa using hσd.symm)
      set u : ℕ → ℂ := fun n => (1 - 1 / ((n : ℂ) + 2)) * σ with hu
      have hu_lim : Tendsto u atTop (𝓝 σ) := by
        have h1r : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 2)) atTop (𝓝 0) := by
          have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp (tendsto_add_atTop_nat 1)
          refine this.congr fun n => ?_
          simp only [Function.comp_apply]
          push_cast
          ring
        have h1 : Tendsto (fun n : ℕ => (1 : ℂ) / ((n : ℂ) + 2)) atTop (𝓝 0) := by
          have := (Complex.continuous_ofReal.tendsto 0).comp h1r
          rw [Complex.ofReal_zero] at this
          refine this.congr fun n => ?_
          simp only [Function.comp_apply]
          push_cast
          ring
        have := ((tendsto_const_nhds (x := (1 : ℂ))).sub h1).mul_const σ
        simpa [hu] using this
      have hΨlim := (hΨdiff.continuous.tendsto σ).comp hu_lim
      refine ge_of_tendsto hΨlim.norm (Eventually.of_forall fun n => ?_)
      have hc : ‖(1 : ℂ) - 1 / ((n : ℂ) + 2)‖ < 1 := by
        have : (1 : ℂ) - 1 / ((n : ℂ) + 2) = (((n : ℝ) + 1) / ((n : ℝ) + 2) : ℝ) := by
          push_cast
          field_simp
          ring
        rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity),
          div_lt_one (by positivity)]
        linarith
      have hc0 : 0 < ‖(1 : ℂ) - 1 / ((n : ℂ) + 2)‖ := by
        have : (1 : ℂ) - 1 / ((n : ℂ) + 2) = (((n : ℝ) + 1) / ((n : ℝ) + 2) : ℝ) := by
          push_cast
          field_simp
          ring
        rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
        positivity
      refine hbound (u n) ?_ ?_
      · simp only [hu, norm_mul]
        nlinarith [norm_nonneg σ]
      · intro h
        simp only [hu, mul_pow] at h
        rw [hσd] at h
        have h' : ((1 : ℂ) - 1 / ((n : ℂ) + 2)) ^ 2 = 1 := by
          have := mul_right_cancel₀ (pow_ne_zero 2 hdc) (h.trans (one_mul _).symm)
          exact this
        have := congrArg norm h'
        rw [norm_pow, norm_one] at this
        nlinarith
    · exact hbound σ hσ hσd
  have hΨne : ∀ σ : ℂ, ‖σ‖ ≤ r → Ψ σ ≠ 0 := fun σ hσ h => by
    have := hbound' σ hσ
    rw [h, norm_zero] at this
    exact absurd this (not_le.mpr (Real.exp_pos _))
  -- Cauchy's estimate for `1/Ψ`
  have hdiffOn : DifferentiableOn ℂ (fun σ => (Ψ σ)⁻¹) (closure (ball (0 : ℂ) r)) := by
    rw [closure_ball _ hrpos.ne']
    intro σ hσ
    exact ((hΨdiff σ).inv (hΨne σ (by simpa using hσ))).differentiableWithinAt
  have hcauchy : ∀ n, ‖iteratedDeriv n (fun σ => (Ψ σ)⁻¹) 0‖ ≤
      n ! * Real.exp (3 / 10) / r ^ n := by
    intro n
    refine Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n hrpos
      hdiffOn.diffContOnCl fun σ hσ => ?_
    have hσr : ‖σ‖ = r := by simpa using hσ
    rw [norm_inv]
    have := hbound' σ hσr.le
    calc ‖Ψ σ‖⁻¹ ≤ (Real.exp (-(3 / 10)))⁻¹ := inv_anti₀ (Real.exp_pos _) this
      _ = Real.exp (3 / 10) := by rw [Real.exp_neg, inv_inv]
  -- the coefficient formula for `1/h_t`
  set ψ : ℕ → ℂ := evenCoeffC (fun σ => (Ψ σ)⁻¹) with hψ
  have hψ0 : ψ 0 = 1 := by
    simp [hψ, evenCoeffC, hΨ0]
  have hψbound : ∀ k, ‖ψ k‖ ≤ Real.exp (3 / 10) / (3 * d ^ 2) ^ k := by
    intro k
    have h := hcauchy (2 * k)
    simp only [hψ, evenCoeffC, norm_mul, norm_inv, Complex.norm_natCast]
    have hfac : (0 : ℝ) < ((2 * k).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
    rw [inv_mul_le_iff₀ hfac]
    calc ‖iteratedDeriv (2 * k) (fun σ => (Ψ σ)⁻¹) 0‖ ≤ (2 * k) ! * Real.exp (3 / 10) / r ^ (2 * k) := h
      _ = ((2 * k).factorial : ℝ) * (Real.exp (3 / 10) / (3 * d ^ 2) ^ k) := by
          rw [pow_mul, hr2]
          ring
  have hinvA : AnalyticAt ℂ (fun σ => (Ψ σ)⁻¹) 0 :=
    (hΨdiff.analyticAt 0).inv (by rw [hΨ0]; exact one_ne_zero)
  have hQ := analyticAt_recipQuad (1 / (d : ℂ) ^ 2)
  have hQo := iteratedDeriv_recipQuad_odd (1 / (d : ℂ) ^ 2)
  have hinv_eq : (fun σ => (xiHorizontalPair t σ)⁻¹) =
      (fun _ => (xiHorizontalPair t 0)⁻¹) *
        (recipQuad (1 / (d : ℂ) ^ 2) * fun σ => (Ψ σ)⁻¹) := by
    funext σ
    simp only [Pi.mul_apply, recipQuad]
    rw [hh σ, mul_inv, mul_inv]
  have hconstA : AnalyticAt ℂ (fun _ : ℂ => (xiHorizontalPair t 0)⁻¹) 0 := analyticAt_const
  have hconstO : ∀ k : ℕ, iteratedDeriv (2 * k + 1) (fun _ : ℂ => (xiHorizontalPair t 0)⁻¹) 0 = 0 :=
    fun k => by rw [iteratedDeriv_const]; simp
  have hcoef : ∀ n, evenCoeffC (fun σ => (xiHorizontalPair t σ)⁻¹) n =
      (xiHorizontalPair t 0)⁻¹ * ∑ j ∈ Finset.range (n + 1), (1 / (d : ℂ) ^ 2) ^ j * ψ (n - j) := by
    intro n
    rw [hinv_eq, evenCoeffC_mul hconstA (hQ.mul hinvA) hconstO]
    rw [Finset.sum_eq_single 0]
    · simp only [evenCoeffC, mul_zero, Nat.factorial_zero, Nat.cast_one, inv_one, one_mul,
        iteratedDeriv_zero, Nat.sub_zero]
      congr 1
      have := evenCoeffC_mul hQ hinvA hQo n
      simp only [evenCoeffC] at this ⊢
      rw [this]
      refine Finset.sum_congr rfl fun j _ => ?_
      have hq := evenCoeffC_recipQuad (1 / (d : ℂ) ^ 2) j
      simp only [evenCoeffC] at hq
      rw [hq]
      rfl
    · intro j _ hj
      simp only [evenCoeffC]
      rw [iteratedDeriv_const, if_neg (by omega), mul_zero, zero_mul]
    · intro h
      simp at h
  -- the real part is positive
  have hh0real : xiHorizontalPair t 0 = ((d ^ 2 * (Φ t).re ^ 2 : ℝ) : ℂ) := by
    have hΦreal : (Φ t).im = 0 := by
      have hXreal : (XiC t).im = 0 := by
        have h := XiC_conj (t : ℂ)
        rw [Complex.conj_ofReal] at h
        have := congrArg Complex.im h
        simp only [Complex.conj_im] at this
        linarith
      have : Φ t = XiC t / (d : ℂ) := by
        rw [hfac t, hdC]
        rw [← hdC]
        field_simp
      rw [this]
      simp [Complex.div_im, hXreal]
    rw [hh0]
    apply Complex.ext
    · simp [sq, Complex.mul_re, hΦreal]
    · simp [sq, Complex.mul_im, hΦreal]
  have hΦre : (Φ t).re ≠ 0 := by
    intro h
    apply hΦt
    apply Complex.ext
    · simpa using h
    · have hXreal : (XiC t).im = 0 := by
        have h := XiC_conj (t : ℂ)
        rw [Complex.conj_ofReal] at h
        have := congrArg Complex.im h
        simp only [Complex.conj_im] at this
        linarith
      have : Φ t = XiC t / (d : ℂ) := by
        rw [hfac t, hdC]
        rw [← hdC]
        field_simp
      rw [this]
      simp [Complex.div_im, hXreal]
  set K : ℝ := (d ^ 2 * (Φ t).re ^ 2)⁻¹ with hK
  have hKpos : 0 < K := by positivity
  have hsumre : ∀ n, 0 < (∑ j ∈ Finset.range (n + 1), (1 / (d : ℂ) ^ 2) ^ j * ψ (n - j)).re := by
    intro n
    have hκ' : ∀ j : ℕ, (1 / (d : ℂ) ^ 2) ^ j = (((1 / d ^ 2) ^ j : ℝ) : ℂ) := by
      intro j
      push_cast
      ring
    rw [Complex.re_sum]
    have hterm : ∀ j ∈ Finset.range (n + 1), ((1 / (d : ℂ) ^ 2) ^ j * ψ (n - j)).re =
        (1 / d ^ 2) ^ j * (ψ (n - j)).re := by
      intro j _
      rw [hκ' j, Complex.re_ofReal_mul]
    rw [Finset.sum_congr rfl hterm]
    -- reindex by `i = n − j`
    rw [← Finset.sum_range_reflect]
    have hre : ∀ i ∈ Finset.range (n + 1), (1 / d ^ 2) ^ (n + 1 - 1 - i) * (ψ (n - (n + 1 - 1 - i))).re
        = (1 / d ^ 2) ^ n * ((d ^ 2) ^ i * (ψ i).re) := by
      intro i hi
      have hin : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      rw [show n + 1 - 1 - i = n - i by omega, show n - (n - i) = i by omega]
      have hd2' : d ^ 2 ≠ 0 := hd2.ne'
      calc (1 / d ^ 2) ^ (n - i) * (ψ i).re
          = (1 / d ^ 2) ^ (n - i) * ((1 / d ^ 2) ^ i * (d ^ 2) ^ i) * (ψ i).re := by
            rw [← mul_pow, one_div_mul_cancel hd2', one_pow, mul_one]
        _ = ((1 / d ^ 2) ^ (n - i) * (1 / d ^ 2) ^ i) * ((d ^ 2) ^ i * (ψ i).re) := by ring
        _ = (1 / d ^ 2) ^ n * ((d ^ 2) ^ i * (ψ i).re) := by
            rw [← pow_add, Nat.sub_add_cancel hin]
    rw [Finset.sum_congr rfl hre, ← Finset.mul_sum]
    refine mul_pos (by positivity) ?_
    rw [Finset.sum_range_succ', pow_zero, one_mul, hψ0, Complex.one_re]
    have htail : |∑ i ∈ Finset.range n, (d ^ 2) ^ (i + 1) * (ψ (i + 1)).re| ≤
        Real.exp (3 / 10) / 2 := by
      calc |∑ i ∈ Finset.range n, (d ^ 2) ^ (i + 1) * (ψ (i + 1)).re|
          ≤ ∑ i ∈ Finset.range n, |(d ^ 2) ^ (i + 1) * (ψ (i + 1)).re| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ i ∈ Finset.range n, Real.exp (3 / 10) * (1 / 3) ^ (i + 1) := by
            refine Finset.sum_le_sum fun i _ => ?_
            rw [abs_mul, abs_of_pos (by positivity)]
            have h1 := (Complex.abs_re_le_norm (ψ (i + 1))).trans (hψbound (i + 1))
            calc (d ^ 2) ^ (i + 1) * |(ψ (i + 1)).re|
                ≤ (d ^ 2) ^ (i + 1) * (Real.exp (3 / 10) / (3 * d ^ 2) ^ (i + 1)) :=
                  mul_le_mul_of_nonneg_left h1 (by positivity)
              _ = Real.exp (3 / 10) * (1 / 3) ^ (i + 1) := by
                  rw [mul_pow]
                  field_simp
                  rw [← mul_pow]
                  norm_num
        _ = Real.exp (3 / 10) * ∑ i ∈ Finset.range n, (1 / 3 : ℝ) ^ (i + 1) := by
            rw [Finset.mul_sum]
        _ ≤ Real.exp (3 / 10) * (1 / 2) := by
            refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
            have hg := geom_sum_eq (show (1 / 3 : ℝ) ≠ 1 by norm_num) n
            have : ∑ i ∈ Finset.range n, (1 / 3 : ℝ) ^ (i + 1) =
                (1 / 3) * ∑ i ∈ Finset.range n, (1 / 3 : ℝ) ^ i := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun i _ => ?_
              ring
            have hg' : ((1 / 3 : ℝ) ^ n - 1) / (1 / 3 - 1) = 3 / 2 * (1 - (1 / 3) ^ n) := by
              field_simp
              ring
            rw [this, hg, hg']
            have hp : 0 < (1 / 3 : ℝ) ^ n := by positivity
            linarith
        _ = Real.exp (3 / 10) / 2 := by ring
    have := exp_three_tenths_lt_two
    have := (abs_le.mp htail).1
    linarith
  intro n
  rcases Nat.even_or_odd' n with ⟨m, rfl | rfl⟩
  · have hc := hcoef m
    simp only [evenCoeffC] at hc
    have hfac : (((2 * m).factorial : ℂ)) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
    have hD : iteratedDeriv (2 * m) (fun σ => (xiHorizontalPair t σ)⁻¹) 0 =
        ((2 * m).factorial : ℂ) * ((xiHorizontalPair t 0)⁻¹ *
          ∑ j ∈ Finset.range (m + 1), (1 / (d : ℂ) ^ 2) ^ j * ψ (m - j)) := by
      rw [← hc]
      field_simp
    rw [Complex.nonneg_iff]
    constructor
    · rw [hD, hh0real, ← Complex.ofReal_inv]
      have hcast : ((2 * m).factorial : ℂ) = (((2 * m).factorial : ℝ) : ℂ) := by push_cast; rfl
      rw [hcast, ← mul_assoc, ← Complex.ofReal_mul, Complex.re_ofReal_mul]
      exact mul_nonneg (mul_nonneg (by positivity) (inv_nonneg.mpr (by positivity)))
        (hsumre m).le
    · exact (im_iteratedDeriv_inv_xiHorizontalPair t (2 * m)).symm
  · rw [iteratedDeriv_inv_xiHorizontalPair_odd]

/-- The squared reciprocal distances to a fixed point are summable. -/
theorem summable_inv_sq_norm_xiSpectralPoint_sub (c : ℂ) :
    Summable (fun q : XiZeroCopy => 1 / ‖xiSpectralPoint q - c‖ ^ 2) := by
  refine Summable.of_norm_bounded_eventually (xiSpectralPoint_inv_sq_summable.mul_left 4) ?_
  have hfin := finite_xiZeroCopy_norm_le (2 * ‖c‖)
  refine hfin.eventually_cofinite_notMem.mono fun q hq => ?_
  · simp only [Set.mem_setOf_eq, not_le] at hq
    have hpos := norm_pos_iff.mpr (xiSpectralPoint_ne_zero q)
    have hd : ‖xiSpectralPoint q‖ / 2 ≤ ‖xiSpectralPoint q - c‖ := by
      have := norm_sub_norm_le (xiSpectralPoint q) c
      linarith
    have hd0 : 0 < ‖xiSpectralPoint q‖ / 2 := by positivity
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc 1 / ‖xiSpectralPoint q - c‖ ^ 2 ≤ 1 / (‖xiSpectralPoint q‖ / 2) ^ 2 :=
          one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ hd0.le hd 2)
      _ = 4 * (1 / ‖xiSpectralPoint q‖ ^ 2) := by field_simp; ring

/-- **Reciprocal slice positivity near every simple real zero.**  If `γ` is a real zero of `Ξ`
carried by exactly one zero copy, then at every height `t ≠ γ` close enough to `γ`, `Ξ(t) ≠ 0`
and every Taylor coefficient of `1/(Ξ(t+σ)Ξ(t−σ))` at `0` is nonnegative. -/
theorem exists_xiReciprocalSlicePositive_near_simple_real_zero {γ : ℝ} (q₀ : XiZeroCopy)
    (hq₀ : xiSpectralPoint q₀ = (γ : ℂ)) (huniq : ∀ q, xiSpectralPoint q = (γ : ℂ) → q = q₀) :
    ∃ ε > 0, ∀ t : ℝ, 0 < |t - γ| → |t - γ| < ε → XiC t ≠ 0 ∧ XiReciprocalSlicePositive t := by
  classical
  -- a radius free of other zeros
  obtain ⟨δ₀, hδ₀, hδ₀le⟩ : ∃ δ₀ > 0, ∀ q, q ≠ q₀ → δ₀ ≤ ‖xiSpectralPoint q - γ‖ := by
    have hfin : {q : XiZeroCopy | ‖xiSpectralPoint q‖ ≤ |γ| + 1}.Finite :=
      finite_xiZeroCopy_norm_le _
    set F := hfin.toFinset.erase q₀
    by_cases hF : F.Nonempty
    · obtain ⟨q₁, hq₁, hmin⟩ := F.exists_min_image (fun q => ‖xiSpectralPoint q - γ‖) hF
      have hq₁ne : q₁ ≠ q₀ := (Finset.mem_erase.mp hq₁).1
      have hpos : 0 < ‖xiSpectralPoint q₁ - γ‖ := by
        refine norm_pos_iff.mpr (sub_ne_zero.mpr fun h => hq₁ne (huniq q₁ h))
      refine ⟨min 1 ‖xiSpectralPoint q₁ - γ‖, lt_min one_pos hpos, fun q hq => ?_⟩
      by_cases hqF : q ∈ F
      · exact (min_le_right _ _).trans (hmin q hqF)
      · have : ¬ ‖xiSpectralPoint q‖ ≤ |γ| + 1 := by
          intro h
          exact hqF (Finset.mem_erase.mpr ⟨hq, by simpa using h⟩)
        push Not at this
        have h2 := norm_sub_norm_le (xiSpectralPoint q) (γ : ℂ)
        rw [Complex.norm_real, Real.norm_eq_abs] at h2
        exact (min_le_left _ _).trans (by linarith)
    · refine ⟨1, one_pos, fun q hq => ?_⟩
      have hqF : q ∉ F := fun h => hF ⟨q, h⟩
      have : ¬ ‖xiSpectralPoint q‖ ≤ |γ| + 1 := by
        intro h
        exact hqF (Finset.mem_erase.mpr ⟨hq, by simpa using h⟩)
      push Not at this
      have h2 := norm_sub_norm_le (xiSpectralPoint q) (γ : ℂ)
      rw [Complex.norm_real, Real.norm_eq_abs] at h2
      linarith
  set A : ℝ := ∑' q, 1 / ‖xiSpectralPoint q - γ‖ ^ 2 with hA
  have hAsum := summable_inv_sq_norm_xiSpectralPoint_sub (γ : ℂ)
  have hA0 : 0 ≤ A := tsum_nonneg fun q => by positivity
  refine ⟨min (δ₀ / 2) (1 / (9 * (A + 1))), lt_min (by positivity) (by positivity), ?_⟩
  intro t ht0 htε
  have htδ : |t - γ| < δ₀ / 2 := htε.trans_le (min_le_left _ _)
  have htA : |t - γ| < 1 / (9 * (A + 1)) := htε.trans_le (min_le_right _ _)
  have hfar : ∀ q, q ≠ q₀ → ‖xiSpectralPoint q - γ‖ / 2 ≤ ‖xiSpectralPoint q - t‖ := by
    intro q hq
    have h1 := hδ₀le q hq
    have h2 : ‖xiSpectralPoint q - γ‖ ≤ ‖xiSpectralPoint q - t‖ + |t - γ| := by
      have := norm_sub_le (xiSpectralPoint q - t) ((γ : ℂ) - t)
      rw [show xiSpectralPoint q - t - ((γ : ℂ) - t) = xiSpectralPoint q - γ by ring] at this
      rw [show ‖(γ : ℂ) - t‖ = |t - γ| by
        rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm]] at this
      exact this
    linarith
  have hXt : XiC t ≠ 0 := by
    intro h
    obtain ⟨q, hq⟩ := (XiC_eq_zero_iff_exists_xiZeroCopy (t : ℂ)).mp h
    have hqne : q ≠ q₀ := by
      intro hqq
      rw [hqq, hq₀] at hq
      have : t = γ := by exact_mod_cast hq.symm
      rw [this, sub_self, abs_zero] at ht0
      exact lt_irrefl _ ht0
    have := hδ₀le q hqne
    rw [hq, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at this
    linarith
  refine ⟨hXt, xiReciprocalSlicePositive_of_dominant_zero hXt q₀ hq₀ fun F hF => ?_⟩
  have hsum : ∑ q ∈ F, 1 / ‖xiSpectralPoint q - t‖ ^ 2 ≤ 4 * A := by
    calc ∑ q ∈ F, 1 / ‖xiSpectralPoint q - t‖ ^ 2
        ≤ ∑ q ∈ F, 4 * (1 / ‖xiSpectralPoint q - γ‖ ^ 2) := by
          refine Finset.sum_le_sum fun q hq => ?_
          have hqne : q ≠ q₀ := fun h => hF (h ▸ hq)
          have hpos : 0 < ‖xiSpectralPoint q - γ‖ / 2 :=
            half_pos ((half_pos hδ₀).trans_le (by linarith [hδ₀le q hqne]))
          calc 1 / ‖xiSpectralPoint q - t‖ ^ 2 ≤ 1 / (‖xiSpectralPoint q - γ‖ / 2) ^ 2 :=
                one_div_le_one_div_of_le (by positivity)
                  (pow_le_pow_left₀ hpos.le (hfar q hqne) 2)
            _ = 4 * (1 / ‖xiSpectralPoint q - γ‖ ^ 2) := by field_simp; ring
      _ = 4 * ∑ q ∈ F, 1 / ‖xiSpectralPoint q - γ‖ ^ 2 := by rw [Finset.mul_sum]
      _ ≤ 4 * A := by
          refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
          exact hAsum.sum_le_tsum F (fun q _ => by positivity)
  have hsq : (t - γ) ^ 2 ≤ 1 / (81 * (A + 1)) := by
    have h1 : (t - γ) ^ 2 = |t - γ| ^ 2 := (sq_abs _).symm
    rw [h1]
    have h2 : |t - γ| ^ 2 ≤ (1 / (9 * (A + 1))) ^ 2 :=
      pow_le_pow_left₀ (abs_nonneg _) htA.le 2
    calc |t - γ| ^ 2 ≤ (1 / (9 * (A + 1))) ^ 2 := h2
      _ = 1 / (81 * (A + 1) ^ 2) := by field_simp; ring
      _ ≤ 1 / (81 * (A + 1)) := by
          refine one_div_le_one_div_of_le (by positivity) ?_
          nlinarith
  calc (t - γ) ^ 2 * ∑ q ∈ F, 1 / ‖xiSpectralPoint q - t‖ ^ 2
      ≤ 1 / (81 * (A + 1)) * (4 * A) :=
        mul_le_mul hsq hsum (Finset.sum_nonneg fun q _ => by positivity) (by positivity)
    _ ≤ 1 / 20 := by
        rw [div_mul_eq_mul_div, one_mul, div_le_div_iff₀ (by positivity) (by norm_num)]
        nlinarith

end

end RHTower
