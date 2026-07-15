import GaloisForLFunctions.HTGeometry.ReciprocalGammaPoleBranchTaylor
import GaloisForLFunctions.HTGeometry.GammaDifferentialFE
import GaloisForLFunctions.HTGeometry.ArgumentScalingInvariance
import GaloisForLFunctions.HTGeometry.HolomorphicJetReturn
import GaloisForLFunctions.HTGeometry.DifferentialPowerElimination
import Mathlib.Analysis.SpecialFunctions.Log.Summable

/-!
# The factorial microscope for `digamma ∘ Gamma`

This file proves that `z ↦ digamma (Gamma z)` is hypertranscendental.  The proof is a
static source constraint, not a propagation argument.

At the negative integers, the reciprocal Gamma function has the exact rescaling

`1 / Gamma (-n + (-1)^(n+1) x / n!) → -x`

locally uniformly.  Consequently the same factorial microscope sends `Gamma` to `-1/x`
and `digamma ∘ Gamma` to `x ↦ digamma (-1/x)`, with convergence of every holomorphic
jet on a disk about `-1`.

Any algebraic differential relation for the source has a nonzero highest
derivative-weight, highest-point-degree initial form under this rescaling.  The limiting
function would therefore satisfy a nonzero autonomous differential equation.  Pulling
that relation back through the involution `x ↦ -1/x` produces a nonzero
polynomial-coefficient relation among the digamma jets, contradicting the formalized
polynomial form of Hölder's theorem.

The terminal result is `hypertranscendental_digamma_comp_Gamma`.
-/

namespace GaloisForLFunctions

open Complex Filter Topology

noncomputable section

def reciprocalGammaBackwardProduct (n : ℕ) (δ : ℂ) : ℂ :=
  ∏ j ∈ Finset.range n, (δ - ((j + 1 : ℕ) : ℂ))

theorem reciprocalGammaEntire_neg_nat_add (n : ℕ) (δ : ℂ) :
    reciprocalGammaEntire (-(n : ℂ) + δ) =
      reciprocalGammaBackwardProduct n δ * reciprocalGammaEntire δ := by
  induction n with
  | zero => simp [reciprocalGammaBackwardProduct]
  | succ n ih =>
      rw [show -(↑(n + 1) : ℂ) + δ = (-(n : ℂ) + δ) - 1 by push_cast; ring]
      rw [show (-(n : ℂ) + δ) - 1 = (-(n : ℂ) + δ - 1) from rfl]
      have hrec := Complex.one_div_Gamma_eq_self_mul_one_div_Gamma_add_one
        (-(n : ℂ) + δ - 1)
      change reciprocalGammaEntire (-(n : ℂ) + δ - 1) = _
      rw [show reciprocalGammaEntire (-(n : ℂ) + δ - 1) =
          (-(n : ℂ) + δ - 1) * reciprocalGammaEntire (-(n : ℂ) + δ) by
        simpa [reciprocalGammaEntire] using hrec]
      rw [ih]
      simp only [reciprocalGammaBackwardProduct, Finset.prod_range_succ,
        Nat.cast_add, Nat.cast_one]
      ring

def reciprocalGammaFactorialScale (n : ℕ) : ℂ :=
  (-1 : ℂ) ^ (n + 1) / (n.factorial : ℂ)

def reciprocalGammaNormalizedProduct (n : ℕ) (x : ℂ) : ℂ :=
  ∏ j ∈ Finset.range n,
    (1 - reciprocalGammaFactorialScale n * x / ((j + 1 : ℕ) : ℂ))

theorem norm_reciprocalGammaFactorialScale (n : ℕ) :
    ‖reciprocalGammaFactorialScale n‖ = 1 / (n.factorial : ℝ) := by
  simp [reciprocalGammaFactorialScale, norm_pow]

theorem tendsto_reciprocalGammaNormalizedProduct_locallyUniformly :
    TendstoLocallyUniformly reciprocalGammaNormalizedProduct (fun _ : ℂ => 1) atTop := by
  rw [tendstoLocallyUniformly_iff_forall_isCompact]
  intro K hK
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨R, hR⟩ := hK.exists_bound_of_continuousOn continuous_norm.continuousOn
  let B : ℝ := max R 0
  have hB : ∀ x ∈ K, ‖x‖ ≤ B := by
    intro x hx
    have hxR : ‖x‖ ≤ R := by simpa using hR x hx
    exact hxR.trans (le_max_left _ _)
  have hsmall : Tendsto (fun n : ℕ =>
      Real.exp ((n : ℝ) * ‖reciprocalGammaFactorialScale n‖ * B) - 1)
      atTop (𝓝 0) := by
    have harg : Tendsto (fun n : ℕ =>
        (n : ℝ) * ‖reciprocalGammaFactorialScale n‖ * B) atTop (𝓝 0) := by
      have h := (tendsto_natPow_div_factorial 1).const_mul B
      convert h using 1
      · funext n
        rw [norm_reciprocalGammaFactorialScale]
        simp only [pow_one]
        ring
      · ring_nf
    have hexp := (Real.continuous_exp.continuousAt.tendsto.comp harg).sub_const 1
    simpa using hexp
  filter_upwards [hsmall.eventually_lt_const hε] with n hn x hx
  rw [dist_eq_norm]
  have hprod := Finset.norm_prod_one_add_sub_one_le (Finset.range n)
    (fun j : ℕ => -(reciprocalGammaFactorialScale n * x / ((j + 1 : ℕ) : ℂ)))
  have hsum :
      (∑ j ∈ Finset.range n,
          ‖-(reciprocalGammaFactorialScale n * x / ((j + 1 : ℕ) : ℂ))‖) ≤
        (n : ℝ) * ‖reciprocalGammaFactorialScale n‖ * B := by
    calc
      (∑ j ∈ Finset.range n,
          ‖-(reciprocalGammaFactorialScale n * x / ((j + 1 : ℕ) : ℂ))‖)
          ≤ ∑ _j ∈ Finset.range n,
              (‖reciprocalGammaFactorialScale n‖ * B) := by
            apply Finset.sum_le_sum
            intro j hj
            rw [norm_neg, norm_div, norm_mul, Complex.norm_natCast]
            have hjpos : (0 : ℝ) < (j + 1 : ℕ) := by positivity
            have hden : 1 ≤ ((j + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le j)
            calc
              ‖reciprocalGammaFactorialScale n‖ * ‖x‖ / ((j + 1 : ℕ) : ℝ)
                  ≤ ‖reciprocalGammaFactorialScale n‖ * B / ((j + 1 : ℕ) : ℝ) := by
                    gcongr
                    exact hB x hx
              _ ≤ ‖reciprocalGammaFactorialScale n‖ * B := by
                    exact div_le_self (mul_nonneg (norm_nonneg _) (le_max_right _ _)) hden
      _ = (n : ℝ) * ‖reciprocalGammaFactorialScale n‖ * B := by simp; ring
  have hexpmono := (Real.exp_le_exp.mpr hsum)
  calc
    ‖(1 : ℂ) - reciprocalGammaNormalizedProduct n x‖ =
        ‖reciprocalGammaNormalizedProduct n x - 1‖ := by rw [norm_sub_rev]
    _ ≤ Real.exp
        (∑ j ∈ Finset.range n,
          ‖-(reciprocalGammaFactorialScale n * x / ((j + 1 : ℕ) : ℂ))‖) - 1 := by
          simpa [reciprocalGammaNormalizedProduct, sub_eq_add_neg] using hprod
    _ ≤ Real.exp ((n : ℝ) * ‖reciprocalGammaFactorialScale n‖ * B) - 1 := by
          linarith
    _ < ε := hn

theorem tendsto_reciprocalGammaFactorialScale_zero :
    Tendsto reciprocalGammaFactorialScale atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have h := tendsto_cpow_div_factorial_pow 0 1 (by omega)
  rw [tendsto_zero_iff_norm_tendsto_zero] at h
  convert h using 1
  funext n
  simp [reciprocalGammaFactorialScale, norm_pow]

theorem tendsto_reciprocalGammaFactorialScale_mul_locallyUniformly :
    TendstoLocallyUniformly
      (fun (n : ℕ) (x : ℂ) => reciprocalGammaFactorialScale n * x)
      (fun _ : ℂ => 0) atTop := by
  rw [tendstoLocallyUniformly_iff_forall_isCompact]
  intro K hK
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨R, hR⟩ := hK.exists_bound_of_continuousOn continuous_norm.continuousOn
  let B : ℝ := max R 0
  have hB : ∀ x ∈ K, ‖x‖ ≤ B := by
    intro x hx
    have hxR : ‖x‖ ≤ R := by simpa using hR x hx
    exact hxR.trans (le_max_left _ _)
  have hsmall : Tendsto (fun n => ‖reciprocalGammaFactorialScale n‖ * B) atTop (𝓝 0) :=
    by
      simpa [mul_comm] using
        (tendsto_reciprocalGammaFactorialScale_zero.norm.const_mul B)
  filter_upwards [hsmall.eventually_lt_const hε] with n hn x hx
  rw [dist_eq_norm, norm_sub_rev, sub_zero, norm_mul]
  exact lt_of_le_of_lt
    (mul_le_mul_of_nonneg_left (hB x hx) (norm_nonneg _)) hn

theorem continuousAt_comp_tendstoLocallyUniformly_const
    {ι α : Type*} [TopologicalSpace α] {l : Filter ι}
    {F : ι → α → ℂ} {a : ℂ} {s : Set α} {φ : ℂ → ℂ}
    (hφ : ContinuousAt φ a)
    (hF : TendstoLocallyUniformlyOn F (fun _ => a) l s) :
    TendstoLocallyUniformlyOn (fun n x => φ (F n x)) (fun _ => φ a) l s := by
  rw [Metric.tendstoLocallyUniformlyOn_iff] at hF ⊢
  intro ε hε x hx
  rw [Metric.continuousAt_iff] at hφ
  obtain ⟨δ, hδ, hmap⟩ := hφ ε hε
  obtain ⟨t, ht, hFt⟩ := hF δ hδ x hx
  refine ⟨t, ht, hFt.mono fun n hn y hy => ?_⟩
  have h := hmap (by simpa [dist_comm] using hn y hy)
  simpa [dist_comm] using h

def reciprocalGammaTangent (z : ℂ) : ℂ :=
  dslope reciprocalGammaEntire 0 z

theorem reciprocalGammaTangent_zero : reciprocalGammaTangent 0 = 1 := by
  rw [reciprocalGammaTangent, dslope_same]
  simpa [reciprocalGammaEntire] using (hasDerivAt_oneDivGamma_neg_nat 0).deriv

theorem continuousAt_reciprocalGammaTangent_zero :
    ContinuousAt reciprocalGammaTangent 0 := by
  change ContinuousAt (fun z => dslope reciprocalGammaEntire 0 z) 0
  exact continuousAt_dslope_same.mpr
    (contDiff_reciprocalGammaEntire.differentiable (by simp)).differentiableAt

theorem tendsto_reciprocalGammaTangent_scale_locallyUniformly :
    TendstoLocallyUniformly
      (fun (n : ℕ) (x : ℂ) =>
        reciprocalGammaTangent (reciprocalGammaFactorialScale n * x))
      (fun _ : ℂ => 1) atTop := by
  have h := continuousAt_comp_tendstoLocallyUniformly_const
    continuousAt_reciprocalGammaTangent_zero
    (show TendstoLocallyUniformlyOn
      (fun (n : ℕ) (x : ℂ) => reciprocalGammaFactorialScale n * x)
      (fun _ : ℂ => 0) atTop Set.univ from
        tendstoLocallyUniformlyOn_univ.mpr
          tendsto_reciprocalGammaFactorialScale_mul_locallyUniformly)
  rw [← tendstoLocallyUniformlyOn_univ]
  simpa [reciprocalGammaTangent_zero] using h

theorem prod_neg_natSucc_cast (n : ℕ) :
    (∏ j ∈ Finset.range n, (-((j + 1 : ℕ) : ℂ))) =
      (-1 : ℂ) ^ n * (n.factorial : ℂ) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.prod_range_succ, ih, Nat.factorial_succ, Nat.cast_mul]
      push_cast
      ring

theorem reciprocalGammaBackwardProduct_scale (n : ℕ) (x : ℂ) :
    reciprocalGammaBackwardProduct n (reciprocalGammaFactorialScale n * x) =
      (-1 : ℂ) ^ n * (n.factorial : ℂ) *
        reciprocalGammaNormalizedProduct n x := by
  rw [reciprocalGammaBackwardProduct, reciprocalGammaNormalizedProduct]
  calc
    (∏ j ∈ Finset.range n,
        (reciprocalGammaFactorialScale n * x - ((j + 1 : ℕ) : ℂ))) =
        ∏ j ∈ Finset.range n,
          (-((j + 1 : ℕ) : ℂ)) *
            (1 - reciprocalGammaFactorialScale n * x / ((j + 1 : ℕ) : ℂ)) := by
              apply Finset.prod_congr rfl
              intro j hj
              have hj0 : (((j + 1 : ℕ) : ℂ)) ≠ 0 := by
                exact_mod_cast Nat.succ_ne_zero j
              field_simp
              ring
    _ = (∏ j ∈ Finset.range n, (-((j + 1 : ℕ) : ℂ))) *
        (∏ j ∈ Finset.range n,
          (1 - reciprocalGammaFactorialScale n * x / ((j + 1 : ℕ) : ℂ))) := by
            rw [Finset.prod_mul_distrib]
    _ = _ := by rw [prod_neg_natSucc_cast]

theorem reciprocalGammaEntire_eq_mul_tangent (z : ℂ) :
    reciprocalGammaEntire z = z * reciprocalGammaTangent z := by
  have hzero : reciprocalGammaEntire 0 = 0 := by
    simp [reciprocalGammaEntire]
  have h := sub_smul_dslope_of_zero hzero z
  simpa [reciprocalGammaTangent] using h.symm

theorem reciprocalGammaFactorialScale_cancel (n : ℕ) :
    (-1 : ℂ) ^ n * (n.factorial : ℂ) * reciprocalGammaFactorialScale n = -1 := by
  rw [reciprocalGammaFactorialScale]
  have hn : (n.factorial : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero n
  field_simp
  rw [← pow_add]
  rw [show n + (n + 1) = 2 * n + 1 by omega, pow_succ, pow_mul]
  norm_num

theorem reciprocalGammaFactorialBlowUp_exact (n : ℕ) (x : ℂ) :
    reciprocalGammaEntire (-(n : ℂ) + reciprocalGammaFactorialScale n * x) =
      -x * reciprocalGammaNormalizedProduct n x *
        reciprocalGammaTangent (reciprocalGammaFactorialScale n * x) := by
  rw [reciprocalGammaEntire_neg_nat_add,
    reciprocalGammaBackwardProduct_scale,
    reciprocalGammaEntire_eq_mul_tangent]
  have hcancel := reciprocalGammaFactorialScale_cancel n
  calc
    (-1 : ℂ) ^ n * ↑n.factorial * reciprocalGammaNormalizedProduct n x *
        (reciprocalGammaFactorialScale n * x *
          reciprocalGammaTangent (reciprocalGammaFactorialScale n * x)) =
      ((-1 : ℂ) ^ n * ↑n.factorial * reciprocalGammaFactorialScale n) *
        x * reciprocalGammaNormalizedProduct n x *
          reciprocalGammaTangent (reciprocalGammaFactorialScale n * x) := by ring
    _ = _ := by rw [hcancel]; ring

theorem tendstoLocallyUniformly_const_sequence
    {ι α β : Type*} [TopologicalSpace α] [UniformSpace β]
    {l : Filter ι} (f : α → β) :
    TendstoLocallyUniformly (fun _ : ι => f) f l := by
  intro u hu x
  refine ⟨Set.univ, univ_mem, Filter.Eventually.of_forall fun _ y _ => ?_⟩
  exact refl_mem_uniformity hu

theorem tendsto_reciprocalGammaFactorialBlowUp_locallyUniformly :
    TendstoLocallyUniformly
      (fun (n : ℕ) (x : ℂ) =>
        reciprocalGammaEntire (-(n : ℂ) + reciprocalGammaFactorialScale n * x))
      (fun x : ℂ => -x) atTop := by
  have hneg : TendstoLocallyUniformly
      (fun (_n : ℕ) (x : ℂ) => -x) (fun x : ℂ => -x) atTop :=
    tendstoLocallyUniformly_const_sequence (fun x : ℂ => -x)
  have hprod := hneg.mul₀ tendsto_reciprocalGammaNormalizedProduct_locallyUniformly
    continuous_neg continuous_const
  have hall := hprod.mul₀ tendsto_reciprocalGammaTangent_scale_locallyUniformly
    (continuous_neg.mul continuous_const) continuous_const
  change TendstoLocallyUniformly
    (fun n x => -x * reciprocalGammaNormalizedProduct n x *
      reciprocalGammaTangent (reciprocalGammaFactorialScale n * x))
    (fun x : ℂ => -x * 1 * 1) atTop at hall
  simpa only [mul_one, reciprocalGammaFactorialBlowUp_exact] using hall

theorem continuousAt_comp_tendstoLocallyUniformlyOn
    {ι α β γ : Type*} [PseudoMetricSpace α] [PseudoMetricSpace β]
    [PseudoMetricSpace γ] {l : Filter ι} {F : ι → α → β} {f : α → β}
    {s : Set α} {φ : β → γ}
    (hφ : ∀ x ∈ s, ContinuousAt φ (f x))
    (hf : ContinuousOn f s)
    (hF : TendstoLocallyUniformlyOn F f l s) :
    TendstoLocallyUniformlyOn (fun n x => φ (F n x)) (fun x => φ (f x)) l s := by
  rw [Metric.tendstoLocallyUniformlyOn_iff] at hF ⊢
  intro ε hε x hx
  have hε2 : 0 < ε / 2 := by linarith
  have hc := hφ x hx
  rw [Metric.continuousAt_iff] at hc
  obtain ⟨δ, hδ, hmap⟩ := hc (ε / 2) hε2
  have hδ2 : 0 < δ / 2 := by linarith
  have hfc := hf x hx
  rw [Metric.continuousWithinAt_iff] at hfc
  obtain ⟨η, hη, hfmap⟩ := hfc (δ / 2) hδ2
  obtain ⟨t, ht, hFt⟩ := hF (δ / 2) hδ2 x hx
  let u := t ∩ Metric.ball x η ∩ s
  have hu : u ∈ 𝓝[s] x := by
    exact inter_mem (inter_mem ht
      (mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds x hη))) self_mem_nhdsWithin
  refine ⟨u, hu, hFt.mono fun n hn y hy => ?_⟩
  have hyt : y ∈ t := hy.1.1
  have hyball : y ∈ Metric.ball x η := hy.1.2
  have hys : y ∈ s := hy.2
  have hfy : dist (f y) (f x) < δ / 2 := hfmap hys hyball
  have hFn : dist (f y) (F n y) < δ / 2 := hn y hyt
  have hfyδ : dist (f y) (f x) < δ := lt_trans hfy (by linarith)
  have hFnδ : dist (F n y) (f x) < δ := by
    calc
      dist (F n y) (f x) ≤ dist (F n y) (f y) + dist (f y) (f x) :=
        dist_triangle _ _ _
      _ < δ := by rw [dist_comm (F n y) (f y)]; linarith
  have hφfy := hmap hfyδ
  have hφFn := hmap hFnδ
  calc
    dist (φ (f y)) (φ (F n y)) ≤
        dist (φ (f y)) (φ (f x)) + dist (φ (f x)) (φ (F n y)) :=
      dist_triangle _ _ _
    _ < ε := by rw [dist_comm (φ (f x)) (φ (F n y))]; linarith

theorem tendsto_Gamma_factorialBlowUp_locallyUniformlyOn_ne_zero :
    TendstoLocallyUniformlyOn
      (fun (n : ℕ) (x : ℂ) =>
        Complex.Gamma (-(n : ℂ) + reciprocalGammaFactorialScale n * x))
      (fun x : ℂ => (-x)⁻¹) atTop {x : ℂ | x ≠ 0} := by
  have hH : TendstoLocallyUniformlyOn
      (fun (n : ℕ) (x : ℂ) =>
        reciprocalGammaEntire (-(n : ℂ) + reciprocalGammaFactorialScale n * x))
      (fun x : ℂ => -x) atTop {x : ℂ | x ≠ 0} := by
    have hHuniv := tendstoLocallyUniformlyOn_univ.mpr
      tendsto_reciprocalGammaFactorialBlowUp_locallyUniformly
    exact hHuniv.mono (Set.subset_univ _)
  have hinv := continuousAt_comp_tendstoLocallyUniformlyOn
    (φ := fun z : ℂ => z⁻¹)
    (fun x hx => continuousAt_inv₀ (neg_ne_zero.mpr hx))
    continuous_neg.continuousOn hH
  simpa only [reciprocalGammaEntire, inv_inv] using hinv

def reciprocalGammaBlowUpDisk : Set ℂ :=
  Metric.ball (-1 : ℂ) (1 / 4 : ℝ)

theorem isOpen_reciprocalGammaBlowUpDisk : IsOpen reciprocalGammaBlowUpDisk :=
  Metric.isOpen_ball

theorem reciprocalGammaBlowUpDisk_ne_zero {x : ℂ}
    (hx : x ∈ reciprocalGammaBlowUpDisk) : x ≠ 0 := by
  intro hzero
  subst x
  norm_num [reciprocalGammaBlowUpDisk, Complex.dist_eq] at hx

theorem reciprocalGammaBlowUpDisk_inv_neg_re_pos {x : ℂ}
    (hx : x ∈ reciprocalGammaBlowUpDisk) : 0 < ((-x)⁻¹ : ℂ).re := by
  have hnorm : ‖x - (-1 : ℂ)‖ < (1 / 4 : ℝ) := by
    simpa [reciprocalGammaBlowUpDisk, Complex.dist_eq] using hx
  have hreabs : |(x - (-1 : ℂ)).re| < (1 / 4 : ℝ) :=
    lt_of_le_of_lt (Complex.abs_re_le_norm _) hnorm
  rw [abs_lt] at hreabs
  have hnegRe : 0 < (-x).re := by
    simp only [Complex.sub_re, Complex.neg_re, Complex.one_re] at hreabs ⊢
    linarith
  rw [Complex.inv_re]
  exact div_pos hnegRe
    (Complex.normSq_pos.mpr (neg_ne_zero.mpr (reciprocalGammaBlowUpDisk_ne_zero hx)))

theorem tendsto_digamma_Gamma_factorialBlowUp_locallyUniformlyOn :
    TendstoLocallyUniformlyOn
      (fun (n : ℕ) (x : ℂ) => Complex.digamma
        (Complex.Gamma (-(n : ℂ) + reciprocalGammaFactorialScale n * x)))
      (fun x : ℂ => Complex.digamma ((-x)⁻¹)) atTop reciprocalGammaBlowUpDisk := by
  have hGamma := tendsto_Gamma_factorialBlowUp_locallyUniformlyOn_ne_zero.mono
    (fun x hx => reciprocalGammaBlowUpDisk_ne_zero hx)
  have hlimit : ContinuousOn (fun x : ℂ => (-x)⁻¹) reciprocalGammaBlowUpDisk :=
    continuous_neg.continuousOn.inv₀
      (fun x hx => neg_ne_zero.mpr (reciprocalGammaBlowUpDisk_ne_zero hx))
  apply continuousAt_comp_tendstoLocallyUniformlyOn _ hlimit hGamma
  intro x hx
  apply continuousAt_digamma
  intro m heq
  have hpos := reciprocalGammaBlowUpDisk_inv_neg_re_pos hx
  rw [heq] at hpos
  simp at hpos
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  linarith

def factorialBlowUpPointBase (n : ℕ) (x : ℂ) : ℂ :=
  (-(n : ℂ) + reciprocalGammaFactorialScale n * x) / ((n + 1 : ℕ) : ℂ)

theorem tendsto_factorialBlowUpPointBase (x : ℂ) :
    Tendsto (fun n => factorialBlowUpPointBase n x) atTop (𝓝 (-1)) := by
  have hinv := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℂ)
  have hfrac : Tendsto (fun n : ℕ => (n : ℂ) / ((n + 1 : ℕ) : ℂ)) atTop (𝓝 1) := by
    have hone : Tendsto (fun _ : ℕ => (1 : ℂ)) atTop (𝓝 1) := tendsto_const_nhds
    have h := hone.sub hinv
    convert h using 1
    · funext n
      have hn : (((n + 1 : ℕ) : ℂ)) ≠ 0 := by
        exact_mod_cast Nat.succ_ne_zero n
      field_simp
      push_cast
      ring
    · ring_nf
  have hscaleDiv : Tendsto
      (fun n : ℕ => reciprocalGammaFactorialScale n * x / ((n + 1 : ℕ) : ℂ))
      atTop (𝓝 0) := by
    have h := (tendsto_reciprocalGammaFactorialScale_zero.mul_const x).mul hinv
    simpa [div_eq_mul_inv] using h
  have h := hfrac.neg.add hscaleDiv
  simp only [add_zero] at h
  convert h using 1
  funext n
  rw [factorialBlowUpPointBase, add_div]
  ring

theorem tendsto_factorialScale_pow_mul_natSuccPow_zero
    (m q : ℕ) (hm : 1 ≤ m) :
    Tendsto (fun n : ℕ => reciprocalGammaFactorialScale n ^ m * ((n + 1 : ℕ) : ℂ) ^ q)
      atTop (𝓝 0) := by
  let P : Polynomial ℂ := (Polynomial.C 1 - Polynomial.X) ^ q
  have hP := poly_div_factorial_pow_tendsto P m hm
  rw [tendsto_zero_iff_norm_tendsto_zero] at hP ⊢
  convert hP using 1
  funext n
  rw [norm_mul, norm_pow, norm_reciprocalGammaFactorialScale, norm_pow,
    Complex.norm_natCast, norm_div, norm_pow, Complex.norm_natCast]
  have hPeval : P.eval (-(n : ℂ)) = ((n + 1 : ℕ) : ℂ) ^ q := by
    simp [P]
    congr 1
    ring
  rw [hPeval, norm_pow, Complex.norm_natCast]
  ring

def factorialBlowUpMonomialCoefficient
    (n : ℕ) (x : ℂ) (weightDefect pointExponent pointDegree : ℕ) : ℂ :=
  reciprocalGammaFactorialScale n ^ weightDefect *
    (-(n : ℂ) + reciprocalGammaFactorialScale n * x) ^ pointExponent /
      (((n + 1 : ℕ) : ℂ) ^ pointDegree)

theorem tendsto_factorialBlowUpMonomialCoefficient_of_weightDefect_pos
    (x : ℂ) {weightDefect : ℕ} (hweight : 1 ≤ weightDefect)
    (pointExponent pointDegree : ℕ) :
    Tendsto
      (fun n => factorialBlowUpMonomialCoefficient n x weightDefect pointExponent pointDegree)
      atTop (𝓝 0) := by
  have hinv := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℂ)).pow pointDegree
  have hbase := (tendsto_factorialBlowUpPointBase x).pow pointExponent
  have hfactor := tendsto_factorialScale_pow_mul_natSuccPow_zero
    weightDefect pointExponent hweight
  have h := (hfactor.mul hbase).mul hinv
  simp only [zero_mul] at h
  convert h using 1
  funext n
  have hn : (((n + 1 : ℕ) : ℂ)) ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero n
  rw [factorialBlowUpMonomialCoefficient, factorialBlowUpPointBase]
  simp only [one_div, inv_pow, div_pow]
  push_cast
  field_simp [hn]

theorem tendsto_factorialBlowUpMonomialCoefficient_of_pointExponent_lt
    (x : ℂ) {pointExponent pointDegree : ℕ} (hpoint : pointExponent < pointDegree) :
    Tendsto
      (fun n => factorialBlowUpMonomialCoefficient n x 0 pointExponent pointDegree)
      atTop (𝓝 0) := by
  have hinv := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℂ)).pow
    (pointDegree - pointExponent)
  have hbase := (tendsto_factorialBlowUpPointBase x).pow pointExponent
  have h := hbase.mul hinv
  have hdiff : pointDegree - pointExponent ≠ 0 := by omega
  simp only [zero_pow hdiff, mul_zero] at h
  convert h using 1
  funext n
  have hn : (((n + 1 : ℕ) : ℂ)) ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero n
  rw [factorialBlowUpMonomialCoefficient, factorialBlowUpPointBase]
  simp only [pow_zero, one_mul]
  simp only [one_div, inv_pow, div_pow]
  push_cast
  field_simp [hn]
  rw [mul_assoc, ← pow_add]
  rw [Nat.add_sub_of_le (Nat.le_of_lt hpoint)]

theorem tendsto_factorialBlowUpMonomialCoefficient_top
    (x : ℂ) (pointDegree : ℕ) :
    Tendsto
      (fun n => factorialBlowUpMonomialCoefficient n x 0 pointDegree pointDegree)
      atTop (𝓝 ((-1 : ℂ) ^ pointDegree)) := by
  have h := (tendsto_factorialBlowUpPointBase x).pow pointDegree
  convert h using 1
  funext n
  have hn : (((n + 1 : ℕ) : ℂ)) ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero n
  rw [factorialBlowUpMonomialCoefficient, factorialBlowUpPointBase]
  simp only [pow_zero, one_mul]
  simp only [div_pow]

def differentialMonomialWeight {r : ℕ} (α : Fin (r + 2) →₀ ℕ) : ℕ :=
  (Finsupp.comapDomain Fin.succ α
    (Set.injOn_of_injective (Fin.succ_injective (n := r + 1)))).sum
      fun j e => (j : ℕ) * e

def differentialMonomialPointExponent {r : ℕ} (α : Fin (r + 2) →₀ ℕ) : ℕ :=
  α 0

def differentialPolynomialTopWeight {r : ℕ}
    (P : MvPolynomial (Fin (r + 2)) ℂ) : ℕ :=
  P.support.sup differentialMonomialWeight

def differentialPolynomialTopPointDegree {r : ℕ}
    (P : MvPolynomial (Fin (r + 2)) ℂ) : ℕ :=
  (P.support.filter
    (fun α => differentialMonomialWeight α = differentialPolynomialTopWeight P)).sup
      differentialMonomialPointExponent

theorem exists_top_weight_point_monomial {r : ℕ}
    {P : MvPolynomial (Fin (r + 2)) ℂ} (hP : P ≠ 0) :
    ∃ α ∈ P.support,
      differentialMonomialWeight α = differentialPolynomialTopWeight P ∧
      differentialMonomialPointExponent α = differentialPolynomialTopPointDegree P := by
  have hsupp : P.support.Nonempty := MvPolynomial.support_nonempty.mpr hP
  obtain ⟨β, hβ, hβweight⟩ :=
    Finset.exists_mem_eq_sup P.support hsupp differentialMonomialWeight
  have hfiltered :
      (P.support.filter
        (fun α => differentialMonomialWeight α = differentialPolynomialTopWeight P)).Nonempty := by
    refine ⟨β, Finset.mem_filter.mpr ⟨hβ, ?_⟩⟩
    exact hβweight.symm
  obtain ⟨α, hα, hαpoint⟩ := Finset.exists_mem_eq_sup
    (P.support.filter
      (fun α => differentialMonomialWeight α = differentialPolynomialTopWeight P))
    hfiltered differentialMonomialPointExponent
  exact ⟨α, (Finset.mem_filter.mp hα).1, (Finset.mem_filter.mp hα).2,
    hαpoint.symm⟩

theorem differentialMonomialWeight_le_top {r : ℕ}
    {P : MvPolynomial (Fin (r + 2)) ℂ} {α : Fin (r + 2) →₀ ℕ}
    (hα : α ∈ P.support) :
    differentialMonomialWeight α ≤ differentialPolynomialTopWeight P :=
  Finset.le_sup hα

theorem differentialMonomialPointExponent_le_top {r : ℕ}
    {P : MvPolynomial (Fin (r + 2)) ℂ} {α : Fin (r + 2) →₀ ℕ}
    (hα : α ∈ P.support)
    (hweight : differentialMonomialWeight α = differentialPolynomialTopWeight P) :
    differentialMonomialPointExponent α ≤ differentialPolynomialTopPointDegree P := by
  exact Finset.le_sup (Finset.mem_filter.mpr ⟨hα, hweight⟩)

def differentialJetExponent {r : ℕ} (α : Fin (r + 2) →₀ ℕ) : Fin (r + 1) →₀ ℕ :=
  Finsupp.comapDomain Fin.succ α
    (Set.injOn_of_injective (Fin.succ_injective (n := r + 1)))

@[simp] theorem differentialJetExponent_apply {r : ℕ}
    (α : Fin (r + 2) →₀ ℕ) (j : Fin (r + 1)) :
    differentialJetExponent α j = α j.succ := by
  simp [differentialJetExponent]

noncomputable def factorialInitialForm {r : ℕ}
    (P : MvPolynomial (Fin (r + 2)) ℂ) : MvPolynomial (Fin (r + 1)) ℂ :=
  ∑ α ∈ P.support.filter (fun α =>
      differentialMonomialWeight α = differentialPolynomialTopWeight P ∧
      differentialMonomialPointExponent α = differentialPolynomialTopPointDegree P),
    MvPolynomial.monomial (differentialJetExponent α)
      (((-1 : ℂ) ^ differentialPolynomialTopPointDegree P) * MvPolynomial.coeff α P)

theorem differentialExponent_eq_of_tail_eq_of_point_eq {r : ℕ}
    {α β : Fin (r + 2) →₀ ℕ}
    (htail : differentialJetExponent α = differentialJetExponent β)
    (hpoint : differentialMonomialPointExponent α =
      differentialMonomialPointExponent β) : α = β := by
  ext i
  induction i using Fin.cases with
  | zero => exact hpoint
  | succ j =>
      have h := DFunLike.congr_fun htail j
      simpa using h

theorem factorialInitialForm_ne_zero {r : ℕ}
    {P : MvPolynomial (Fin (r + 2)) ℂ} (hP : P ≠ 0) :
    factorialInitialForm P ≠ 0 := by
  classical
  obtain ⟨β, hβsupp, hβweight, hβpoint⟩ := exists_top_weight_point_monomial hP
  have hβfilter : β ∈ P.support.filter (fun α =>
      differentialMonomialWeight α = differentialPolynomialTopWeight P ∧
      differentialMonomialPointExponent α = differentialPolynomialTopPointDegree P) :=
    Finset.mem_filter.mpr ⟨hβsupp, hβweight, hβpoint⟩
  intro hzero
  have hcoeff := congrArg (MvPolynomial.coeff (differentialJetExponent β)) hzero
  rw [factorialInitialForm, MvPolynomial.coeff_sum] at hcoeff
  simp only [MvPolynomial.coeff_zero] at hcoeff
  rw [Finset.sum_eq_single β] at hcoeff
  · rw [MvPolynomial.coeff_monomial, if_pos rfl] at hcoeff
    exact (mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
      (MvPolynomial.mem_support_iff.mp hβsupp)) hcoeff
  · intro α hα hαne
    rw [MvPolynomial.coeff_monomial, if_neg]
    intro htail
    apply hαne
    exact differentialExponent_eq_of_tail_eq_of_point_eq htail
      ((Finset.mem_filter.mp hα).2.2.trans hβpoint.symm)
  · intro hnot
    exact (hnot hβfilter).elim

def differentialJetMonomial {r : ℕ}
    (y : Fin (r + 1) → ℂ) (α : Fin (r + 2) →₀ ℕ) : ℂ :=
  (differentialJetExponent α).prod fun j e => y j ^ e

theorem differentialJetMonomial_scale {r : ℕ}
    (c : ℂ) (y : Fin (r + 1) → ℂ) (α : Fin (r + 2) →₀ ℕ) :
    differentialJetMonomial (fun j => c ^ (j : ℕ) * y j) α =
      c ^ differentialMonomialWeight α * differentialJetMonomial y α := by
  rw [differentialJetMonomial, differentialJetMonomial, differentialMonomialWeight]
  simp only [differentialJetExponent, mul_pow, ← pow_mul]
  rw [Finsupp.prod_mul, Finsupp.prod, Finset.prod_pow_eq_pow_sum, Finsupp.sum]

def factorialInitialLimitCoefficient {r : ℕ}
    (P : MvPolynomial (Fin (r + 2)) ℂ) (α : Fin (r + 2) →₀ ℕ) : ℂ :=
  if differentialMonomialWeight α = differentialPolynomialTopWeight P ∧
      differentialMonomialPointExponent α = differentialPolynomialTopPointDegree P then
    (-1 : ℂ) ^ differentialPolynomialTopPointDegree P * MvPolynomial.coeff α P
  else 0

theorem eval_factorialInitialForm {r : ℕ}
    (P : MvPolynomial (Fin (r + 2)) ℂ) (y : Fin (r + 1) → ℂ) :
    MvPolynomial.eval y (factorialInitialForm P) =
      ∑ α ∈ P.support,
        factorialInitialLimitCoefficient P α * differentialJetMonomial y α := by
  classical
  rw [factorialInitialForm, map_sum]
  simp only [MvPolynomial.eval_monomial]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro α hα
  by_cases htop : differentialMonomialWeight α = differentialPolynomialTopWeight P ∧
      differentialMonomialPointExponent α = differentialPolynomialTopPointDegree P
  · simp [htop, factorialInitialLimitCoefficient, differentialJetMonomial]
  · simp [htop, factorialInitialLimitCoefficient]

def factorialInitialCoefficient {r : ℕ}
    (P : MvPolynomial (Fin (r + 2)) ℂ) (α : Fin (r + 2) →₀ ℕ)
    (n : ℕ) (x : ℂ) : ℂ :=
  MvPolynomial.coeff α P *
    factorialBlowUpMonomialCoefficient n x
      (differentialPolynomialTopWeight P - differentialMonomialWeight α)
      (differentialMonomialPointExponent α)
      (differentialPolynomialTopPointDegree P)

theorem tendsto_factorialInitialCoefficient {r : ℕ}
    (P : MvPolynomial (Fin (r + 2)) ℂ) {α : Fin (r + 2) →₀ ℕ}
    (hα : α ∈ P.support) (x : ℂ) :
    Tendsto (fun n => factorialInitialCoefficient P α n x) atTop
      (𝓝 (factorialInitialLimitCoefficient P α)) := by
  have hweight := differentialMonomialWeight_le_top hα
  by_cases hw : differentialMonomialWeight α = differentialPolynomialTopWeight P
  · have hpoint := differentialMonomialPointExponent_le_top hα hw
    by_cases hp : differentialMonomialPointExponent α = differentialPolynomialTopPointDegree P
    · have htop := tendsto_factorialBlowUpMonomialCoefficient_top x
        (differentialPolynomialTopPointDegree P)
      simpa [factorialInitialCoefficient, factorialInitialLimitCoefficient, hw, hp,
        Nat.sub_self, mul_comm] using
          htop.const_mul (MvPolynomial.coeff α P)
    · have hplt : differentialMonomialPointExponent α <
          differentialPolynomialTopPointDegree P := lt_of_le_of_ne hpoint hp
      have hzero := tendsto_factorialBlowUpMonomialCoefficient_of_pointExponent_lt x hplt
      simpa [factorialInitialCoefficient, factorialInitialLimitCoefficient, hw, hp,
        Nat.sub_self] using hzero.const_mul (MvPolynomial.coeff α P)
  · have hwlt : differentialMonomialWeight α < differentialPolynomialTopWeight P :=
      lt_of_le_of_ne hweight hw
    have hdefect : 1 ≤ differentialPolynomialTopWeight P - differentialMonomialWeight α := by
      omega
    have hzero := tendsto_factorialBlowUpMonomialCoefficient_of_weightDefect_pos x hdefect
      (differentialMonomialPointExponent α) (differentialPolynomialTopPointDegree P)
    simpa [factorialInitialCoefficient, factorialInitialLimitCoefficient, hw] using
      hzero.const_mul (MvPolynomial.coeff α P)

theorem tendsto_differentialJetMonomial {r : ℕ}
    {G : ℕ → Fin (r + 1) → ℂ} {J : Fin (r + 1) → ℂ}
    (hG : ∀ j, Tendsto (fun n => G n j) atTop (𝓝 (J j)))
    (α : Fin (r + 2) →₀ ℕ) :
    Tendsto (fun n => differentialJetMonomial (G n) α) atTop
      (𝓝 (differentialJetMonomial J α)) := by
  unfold differentialJetMonomial
  exact tendsto_finsetProd _ (fun j _ => (hG j).pow (differentialJetExponent α j))

theorem factorialInitialForm_vanishes_of_rescaled_relations {r : ℕ}
    (P : MvPolynomial (Fin (r + 2)) ℂ) (x : ℂ)
    (G : ℕ → Fin (r + 1) → ℂ) (J : Fin (r + 1) → ℂ)
    (hG : ∀ j, Tendsto (fun n => G n j) atTop (𝓝 (J j)))
    (hrel : ∀ n, ∑ α ∈ P.support,
      factorialInitialCoefficient P α n x * differentialJetMonomial (G n) α = 0) :
    MvPolynomial.eval J (factorialInitialForm P) = 0 := by
  have hlim : Tendsto
      (fun n => ∑ α ∈ P.support,
        factorialInitialCoefficient P α n x * differentialJetMonomial (G n) α)
      atTop
      (𝓝 (∑ α ∈ P.support,
        factorialInitialLimitCoefficient P α * differentialJetMonomial J α)) := by
    apply tendsto_finsetSum
    intro α hα
    exact (tendsto_factorialInitialCoefficient P hα x).mul
      (tendsto_differentialJetMonomial hG α)
  have hzero : Tendsto
      (fun n => ∑ α ∈ P.support,
        factorialInitialCoefficient P α n x * differentialJetMonomial (G n) α)
      atTop (𝓝 0) := by
    convert tendsto_const_nhds using 1
    funext n
    exact hrel n
  rw [eval_factorialInitialForm]
  exact tendsto_nhds_unique hlim hzero

def factorialBlowUpZoom (h : ℂ → ℂ) (n : ℕ) (x : ℂ) : ℂ :=
  h (-(n : ℂ) + reciprocalGammaFactorialScale n * x)

theorem iteratedDeriv_factorialBlowUpZoom
    (h : ℂ → ℂ) (n j : ℕ) (x : ℂ) :
    iteratedDeriv j (factorialBlowUpZoom h n) x =
      reciprocalGammaFactorialScale n ^ j *
        iteratedDeriv j h (-(n : ℂ) + reciprocalGammaFactorialScale n * x) := by
  change iteratedDeriv j
    (fun z => h (-(n : ℂ) + reciprocalGammaFactorialScale n * z)) x = _
  have hfun : (fun z => h (-(n : ℂ) + reciprocalGammaFactorialScale n * z)) =
      fun z => (fun w => h (w + (-(n : ℂ)))) (reciprocalGammaFactorialScale n * z) := by
    funext z
    congr 1
    ring
  rw [hfun]
  rw [iteratedDeriv_comp_mul_left_uncond
    (fun w => h (w + (-(n : ℂ)))) (reciprocalGammaFactorialScale n) j x]
  rw [iteratedDeriv_comp_add_const]
  congr 2
  ring

theorem differentialFullMonomial_split {r : ℕ}
    (z : ℂ) (y : Fin (r + 1) → ℂ) (α : Fin (r + 2) →₀ ℕ) :
    α.prod (fun i e => ((Fin.cons z y : Fin (r + 2) → ℂ) i) ^ e) =
      z ^ differentialMonomialPointExponent α * differentialJetMonomial y α := by
  rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fin.prod_univ_succ]
  rw [differentialJetMonomial,
    Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  simp only [Fin.cons_zero, Fin.cons_succ, differentialMonomialPointExponent,
    differentialJetExponent_apply]

theorem eval_differentialPolynomial_as_sum {r : ℕ}
    (P : MvPolynomial (Fin (r + 2)) ℂ) (z : ℂ) (y : Fin (r + 1) → ℂ) :
    MvPolynomial.eval (Fin.cons z y) P =
      ∑ α ∈ P.support, MvPolynomial.coeff α P *
        (z ^ differentialMonomialPointExponent α * differentialJetMonomial y α) := by
  conv_lhs => rw [P.as_sum]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro α hα
  rw [MvPolynomial.eval_monomial, differentialFullMonomial_split]

theorem differentialJetMonomial_factorialBlowUpZoom {r : ℕ}
    (h : ℂ → ℂ) (n : ℕ) (x : ℂ) (α : Fin (r + 2) →₀ ℕ) :
    differentialJetMonomial
        (fun j : Fin (r + 1) => iteratedDeriv (j : ℕ) (factorialBlowUpZoom h n) x) α =
      reciprocalGammaFactorialScale n ^ differentialMonomialWeight α *
        differentialJetMonomial
          (fun j : Fin (r + 1) => iteratedDeriv (j : ℕ) h
            (-(n : ℂ) + reciprocalGammaFactorialScale n * x)) α := by
  have hvec : (fun j : Fin (r + 1) =>
      iteratedDeriv (j : ℕ) (factorialBlowUpZoom h n) x) =
      fun j : Fin (r + 1) => reciprocalGammaFactorialScale n ^ (j : ℕ) *
        iteratedDeriv (j : ℕ) h
          (-(n : ℂ) + reciprocalGammaFactorialScale n * x) := by
    funext j
    exact iteratedDeriv_factorialBlowUpZoom h n (j : ℕ) x
  rw [hvec, differentialJetMonomial_scale]

theorem factorialInitialRelation_of_differentialAnnihilator {r : ℕ}
    (h : ℂ → ℂ) (P : MvPolynomial (Fin (r + 2)) ℂ)
    (hP : ∀ z : ℂ, MvPolynomial.eval
      (Fin.cons z (fun j : Fin (r + 1) => iteratedDeriv (j : ℕ) h z)) P = 0)
    (n : ℕ) (x : ℂ) :
    ∑ α ∈ P.support,
      factorialInitialCoefficient P α n x *
        differentialJetMonomial
          (fun j : Fin (r + 1) => iteratedDeriv (j : ℕ) (factorialBlowUpZoom h n) x) α = 0 := by
  let point : ℂ := -(n : ℂ) + reciprocalGammaFactorialScale n * x
  let originalJet : Fin (r + 1) → ℂ :=
    fun j => iteratedDeriv (j : ℕ) h point
  calc
    (∑ α ∈ P.support,
      factorialInitialCoefficient P α n x *
        differentialJetMonomial
          (fun j : Fin (r + 1) => iteratedDeriv (j : ℕ) (factorialBlowUpZoom h n) x) α) =
      reciprocalGammaFactorialScale n ^ differentialPolynomialTopWeight P /
          (((n + 1 : ℕ) : ℂ) ^ differentialPolynomialTopPointDegree P) *
        (∑ α ∈ P.support, MvPolynomial.coeff α P *
          (point ^ differentialMonomialPointExponent α *
            differentialJetMonomial originalJet α)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro α hα
      rw [factorialInitialCoefficient, factorialBlowUpMonomialCoefficient,
        differentialJetMonomial_factorialBlowUpZoom]
      have hw := differentialMonomialWeight_le_top hα
      have hscale : reciprocalGammaFactorialScale n ^
            (differentialPolynomialTopWeight P - differentialMonomialWeight α) *
          reciprocalGammaFactorialScale n ^ differentialMonomialWeight α =
          reciprocalGammaFactorialScale n ^ differentialPolynomialTopWeight P := by
        rw [← pow_add, Nat.sub_add_cancel hw]
      dsimp only [point, originalJet]
      calc
        MvPolynomial.coeff α P *
              (reciprocalGammaFactorialScale n ^
                    (differentialPolynomialTopWeight P - differentialMonomialWeight α) *
                  (-↑n + reciprocalGammaFactorialScale n * x) ^
                    differentialMonomialPointExponent α /
                ↑(n + 1) ^ differentialPolynomialTopPointDegree P) *
            (reciprocalGammaFactorialScale n ^ differentialMonomialWeight α *
              differentialJetMonomial
                (fun j : Fin (r + 1) => iteratedDeriv (j : ℕ) h
                  (-↑n + reciprocalGammaFactorialScale n * x)) α) =
          (reciprocalGammaFactorialScale n ^
                (differentialPolynomialTopWeight P - differentialMonomialWeight α) *
              reciprocalGammaFactorialScale n ^ differentialMonomialWeight α) /
              ↑(n + 1) ^ differentialPolynomialTopPointDegree P *
            (MvPolynomial.coeff α P *
              ((-↑n + reciprocalGammaFactorialScale n * x) ^
                  differentialMonomialPointExponent α *
                differentialJetMonomial
                  (fun j : Fin (r + 1) => iteratedDeriv (j : ℕ) h
                    (-↑n + reciprocalGammaFactorialScale n * x)) α)) := by ring
        _ = _ := by rw [hscale]
    _ = reciprocalGammaFactorialScale n ^ differentialPolynomialTopWeight P /
          (((n + 1 : ℕ) : ℂ) ^ differentialPolynomialTopPointDegree P) *
        MvPolynomial.eval (Fin.cons point originalJet) P := by
      rw [eval_differentialPolynomial_as_sum]
    _ = 0 := by rw [hP point, mul_zero]

theorem exists_nonzero_factorialInitialForm_of_differentiallyAlgebraic
    {h f : ℂ → ℂ} {U : Set ℂ}
    (hDA : DifferentiallyAlgebraic h)
    (hjet : ∀ x ∈ U, ∀ j : ℕ,
      Tendsto (fun n => iteratedDeriv j (factorialBlowUpZoom h n) x) atTop
        (𝓝 (iteratedDeriv j f x))) :
    ∃ r : ℕ, ∃ Q : MvPolynomial (Fin (r + 1)) ℂ,
      Q ≠ 0 ∧ ∀ x ∈ U,
        MvPolynomial.eval
          (fun j : Fin (r + 1) => iteratedDeriv (j : ℕ) f x) Q = 0 := by
  obtain ⟨r, P, hP0, hP⟩ := hDA
  refine ⟨r, factorialInitialForm P, factorialInitialForm_ne_zero hP0, ?_⟩
  intro x hx
  apply factorialInitialForm_vanishes_of_rescaled_relations P x
    (fun n j => iteratedDeriv (j : ℕ) (factorialBlowUpZoom h n) x)
    (fun j => iteratedDeriv (j : ℕ) f x)
  · intro j
    exact hjet x hx (j : ℕ)
  · intro n
    exact factorialInitialRelation_of_differentialAnnihilator h P hP n x

theorem exists_eventually_differentiable_digammaGammaZoom_near
    {x : ℂ} (hx : x ∈ reciprocalGammaBlowUpDisk) :
    ∃ V : Set ℂ, IsOpen V ∧ x ∈ V ∧ V ⊆ reciprocalGammaBlowUpDisk ∧
      ∀ᶠ n : ℕ in atTop, DifferentiableOn ℂ
        (factorialBlowUpZoom (fun z => Complex.digamma (Complex.Gamma z)) n) V := by
  let limit : ℂ → ℂ := fun y => (-y)⁻¹
  have hx0 := reciprocalGammaBlowUpDisk_ne_zero hx
  have hlimitAt : ContinuousAt limit x := by
    exact continuousAt_neg.inv₀ (neg_ne_zero.mpr hx0)
  have hxpos : 0 < (limit x).re := reciprocalGammaBlowUpDisk_inv_neg_re_pos hx
  let ε : ℝ := (limit x).re / 4
  have hε : 0 < ε := by dsimp [ε]; linarith
  rw [Metric.continuousAt_iff] at hlimitAt
  obtain ⟨δ, hδ, hlimitMap⟩ := hlimitAt ε hε
  have hGammaOn : TendstoLocallyUniformlyOn
      (fun (n : ℕ) (y : ℂ) =>
        Complex.Gamma (-(n : ℂ) + reciprocalGammaFactorialScale n * y))
      limit atTop reciprocalGammaBlowUpDisk := by
    exact tendsto_Gamma_factorialBlowUp_locallyUniformlyOn_ne_zero.mono
      (fun y hy => reciprocalGammaBlowUpDisk_ne_zero hy)
  rw [Metric.tendstoLocallyUniformlyOn_iff] at hGammaOn
  obtain ⟨t, ht, hGt⟩ := hGammaOn ε hε x hx
  rw [isOpen_reciprocalGammaBlowUpDisk.nhdsWithin_eq hx] at ht
  have hnbhd : t ∩ Metric.ball x δ ∩ reciprocalGammaBlowUpDisk ∈ 𝓝 x :=
    inter_mem (inter_mem ht (Metric.ball_mem_nhds x hδ))
      (isOpen_reciprocalGammaBlowUpDisk.mem_nhds hx)
  obtain ⟨V, hVsub, hVopen, hxV⟩ := mem_nhds_iff.mp hnbhd
  refine ⟨V, hVopen, hxV, fun y hy => (hVsub hy).2, ?_⟩
  filter_upwards [hGt] with n hn
  intro y hy
  have hyall := hVsub hy
  have hyt : y ∈ t := hyall.1.1
  have hyball : y ∈ Metric.ball x δ := hyall.1.2
  have hyU : y ∈ reciprocalGammaBlowUpDisk := hyall.2
  let input : ℂ := -(n : ℂ) + reciprocalGammaFactorialScale n * y
  let gammaValue : ℂ := Complex.Gamma input
  have hcloseGamma : dist (limit y) gammaValue < ε := by
    exact hn y hyt
  have hcloseLimit : dist (limit y) (limit x) < ε := by
    exact hlimitMap hyball
  have hreGammaLimit :
      |gammaValue.re - (limit y).re| ≤ dist (limit y) gammaValue := by
    rw [Complex.dist_eq, norm_sub_rev]
    simpa only [Complex.sub_re] using Complex.abs_re_le_norm (gammaValue - limit y)
  have hreLimit : |(limit y).re - (limit x).re| ≤ dist (limit y) (limit x) := by
    rw [Complex.dist_eq]
    simpa only [Complex.sub_re] using Complex.abs_re_le_norm (limit y - limit x)
  have hgammaRe : 0 < gammaValue.re := by
    have h1 : (limit y).re - ε < gammaValue.re := by
      linarith [neg_le_of_abs_le hreGammaLimit]
    have h2 : (limit x).re - ε < (limit y).re := by
      linarith [neg_le_of_abs_le hreLimit]
    dsimp [ε] at h1 h2 ⊢
    linarith
  have hinputRegular : ∀ m : ℕ, input ≠ -(m : ℂ) := by
    intro m heq
    have hzero : gammaValue = 0 := by
      simp [gammaValue, input, heq, Complex.Gamma_neg_nat_eq_zero]
    rw [hzero] at hgammaRe
    simp at hgammaRe
  have hgammaRegular : ∀ m : ℕ, gammaValue ≠ -(m : ℂ) := by
    intro m heq
    have hre := congrArg Complex.re heq
    simp only [Complex.neg_re, Complex.natCast_re] at hre
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  have hinputDiff : DifferentiableAt ℂ (fun z : ℂ =>
      -(n : ℂ) + reciprocalGammaFactorialScale n * z) y := by fun_prop
  have hGammaDiff : DifferentiableAt ℂ (fun z : ℂ =>
      Complex.Gamma (-(n : ℂ) + reciprocalGammaFactorialScale n * z)) y := by
    exact (Complex.differentiableAt_Gamma input hinputRegular).comp y hinputDiff
  have hDigammaDiff : DifferentiableAt ℂ Complex.digamma gammaValue :=
    (contDiffAt_digamma_n gammaValue hgammaRegular 1).differentiableAt (by norm_num)
  have hcomp := hDigammaDiff.comp y hGammaDiff
  simpa [factorialBlowUpZoom, input, gammaValue, Function.comp_def] using
    hcomp.differentiableWithinAt

def digammaReciprocalLimit (x : ℂ) : ℂ :=
  Complex.digamma ((-x)⁻¹)

theorem iteratedDeriv_digammaGamma_factorialBlowUp_tendsto
    {x : ℂ} (hx : x ∈ reciprocalGammaBlowUpDisk) (j : ℕ) :
    Tendsto
      (fun n => iteratedDeriv j
        (factorialBlowUpZoom (fun z => Complex.digamma (Complex.Gamma z)) n) x)
      atTop (𝓝 (iteratedDeriv j digammaReciprocalLimit x)) := by
  obtain ⟨V, hVopen, hxV, hVU, hdiff⟩ :=
    exists_eventually_differentiable_digammaGammaZoom_near hx
  have hconv := tendsto_digamma_Gamma_factorialBlowUp_locallyUniformlyOn.mono hVU
  have hjet := iteratedDeriv_tendsto_of_locallyUniform hVopen hconv hdiff j hxV
  change Tendsto
    (fun (n : ℕ) => iteratedDeriv j
      (fun y => Complex.digamma
        (Complex.Gamma (-(n : ℂ) + reciprocalGammaFactorialScale n * y))) x)
    atTop (𝓝 (iteratedDeriv j (fun y => Complex.digamma ((-y)⁻¹)) x))
  exact hjet

theorem exists_local_autonomous_annihilator_digammaReciprocalLimit
    (hDA : DifferentiallyAlgebraic (fun z => Complex.digamma (Complex.Gamma z))) :
    ∃ r : ℕ, ∃ Q : MvPolynomial (Fin (r + 1)) ℂ,
      Q ≠ 0 ∧ ∀ x ∈ reciprocalGammaBlowUpDisk,
        MvPolynomial.eval
          (fun j : Fin (r + 1) => iteratedDeriv (j : ℕ) digammaReciprocalLimit x) Q = 0 := by
  exact exists_nonzero_factorialInitialForm_of_differentiallyAlgebraic hDA
    (fun x hx j => iteratedDeriv_digammaGamma_factorialBlowUp_tendsto hx j)

noncomputable def mobiusJetCoeff : ℕ → ℕ → Polynomial ℂ
  | 0, k => if k = 0 then 1 else 0
  | j + 1, k => Polynomial.X ^ 2 *
      ((mobiusJetCoeff j k).derivative +
        if k = 0 then 0 else mobiusJetCoeff j (k - 1))

theorem mobiusJetCoeff_eq_zero_of_lt :
    ∀ {j k : ℕ}, j < k → mobiusJetCoeff j k = 0 := by
  intro j
  induction j with
  | zero =>
      intro k hk
      simp [mobiusJetCoeff, Nat.ne_zero_of_lt hk]
  | succ j ih =>
      intro k hk
      have hk0 : k ≠ 0 := by omega
      have hjk : j < k := by omega
      have hjpred : j < k - 1 := by omega
      rw [mobiusJetCoeff, ih hjk, ih hjpred]
      simp [hk0]

theorem mobiusJetCoeff_diagonal : ∀ j : ℕ,
    mobiusJetCoeff j j = Polynomial.X ^ (2 * j) := by
  intro j
  induction j with
  | zero => simp [mobiusJetCoeff]
  | succ j ih =>
      rw [mobiusJetCoeff]
      have hzero := mobiusJetCoeff_eq_zero_of_lt (Nat.lt_succ_self j)
      rw [hzero, Polynomial.derivative_zero]
      simp only [zero_add, Nat.succ_ne_zero, if_false, Nat.add_sub_cancel, ih]
      rw [← pow_add]
      congr 1
      omega

noncomputable def mobiusJetMatrix (r : ℕ) : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ :=
  fun j k => (mobiusJetCoeff (j : ℕ) (k : ℕ)).eval 1

theorem mobiusJetMatrix_lowerTriangular (r : ℕ) :
    (mobiusJetMatrix r).BlockTriangular (fun i : Fin (r + 1) => OrderDual.toDual i) := by
  intro i k hik
  have hik' : (i : ℕ) < (k : ℕ) := OrderDual.toDual_lt_toDual.mp hik
  rw [mobiusJetMatrix, mobiusJetCoeff_eq_zero_of_lt hik']
  simp

@[simp] theorem mobiusJetMatrix_diag (r : ℕ) (j : Fin (r + 1)) :
    mobiusJetMatrix r j j = 1 := by
  rw [mobiusJetMatrix, mobiusJetCoeff_diagonal]
  simp

theorem mobiusJetMatrix_det (r : ℕ) : (mobiusJetMatrix r).det = 1 := by
  rw [Matrix.det_of_lowerTriangular _ (mobiusJetMatrix_lowerTriangular r)]
  simp

theorem mobiusJetMatrix_isUnit (r : ℕ) : IsUnit (mobiusJetMatrix r) := by
  rw [Matrix.isUnit_iff_isUnit_det, mobiusJetMatrix_det]
  exact isUnit_one

noncomputable def mobiusJetExpression (r : ℕ) (j : Fin (r + 1)) :
    MvPolynomial (Fin (r + 1)) (Polynomial ℂ) :=
  ∑ k : Fin (r + 1),
    MvPolynomial.C (mobiusJetCoeff (j : ℕ) (k : ℕ)) * MvPolynomial.X k

theorem map_eval_one_mobiusJetExpression (r : ℕ) (j : Fin (r + 1)) :
    MvPolynomial.map (Polynomial.evalRingHom 1) (mobiusJetExpression r j) =
      (mobiusJetMatrix r).toMvPolynomial j := by
  rw [mobiusJetExpression, map_sum]
  simp only [map_mul, MvPolynomial.map_C, MvPolynomial.map_X]
  rw [Matrix.toMvPolynomial]
  apply Finset.sum_congr rfl
  intro k hk
  rw [MvPolynomial.monomial_eq]
  simp [mobiusJetMatrix, Finsupp.prod_single_index]

noncomputable def mobiusJetPullback (r : ℕ)
    (Q : MvPolynomial (Fin (r + 1)) ℂ) :
    MvPolynomial (Fin (r + 1)) (Polynomial ℂ) :=
  MvPolynomial.bind₁ (mobiusJetExpression r) (MvPolynomial.map Polynomial.C Q)

theorem map_eval_one_mobiusJetPullback (r : ℕ)
    (Q : MvPolynomial (Fin (r + 1)) ℂ) :
    MvPolynomial.map (Polynomial.evalRingHom 1) (mobiusJetPullback r Q) =
      MvPolynomial.bind₁ (mobiusJetMatrix r).toMvPolynomial Q := by
  rw [mobiusJetPullback, MvPolynomial.map_bind₁]
  simp_rw [map_eval_one_mobiusJetExpression]
  have hmap : MvPolynomial.map (Polynomial.evalRingHom 1)
      (MvPolynomial.map Polynomial.C Q) = Q := by
    rw [MvPolynomial.map_map]
    convert MvPolynomial.map_id Q
    ext c
    simp
  rw [hmap]

theorem mobiusJetPullback_ne_zero {r : ℕ}
    {Q : MvPolynomial (Fin (r + 1)) ℂ} (hQ : Q ≠ 0) :
    mobiusJetPullback r Q ≠ 0 := by
  intro hzero
  have hspecial := congrArg
    (MvPolynomial.map (Polynomial.evalRingHom 1)) hzero
  rw [map_eval_one_mobiusJetPullback, map_zero] at hspecial
  obtain ⟨N, hMN⟩ := isUnit_iff_exists_inv.mp (mobiusJetMatrix_isUnit r)
  have hundone : MvPolynomial.bind₁ N.toMvPolynomial
      (MvPolynomial.bind₁ (mobiusJetMatrix r).toMvPolynomial Q) = Q := by
    rw [MvPolynomial.bind₁_bind₁]
    have hvar : (fun i => MvPolynomial.bind₁ N.toMvPolynomial
        ((mobiusJetMatrix r).toMvPolynomial i)) =
        (MvPolynomial.X : Fin (r + 1) → MvPolynomial (Fin (r + 1)) ℂ) := by
      funext i
      rw [← Matrix.toMvPolynomial_mul, hMN, Matrix.toMvPolynomial_one]
    rw [hvar]
    simp
  rw [hspecial, map_zero] at hundone
  exact hQ hundone.symm

noncomputable def mobiusJetValue (r : ℕ) (u : ℂ → ℂ) (z : ℂ)
    (j : Fin (r + 1)) : ℂ :=
  ∑ k : Fin (r + 1),
    (mobiusJetCoeff (j : ℕ) (k : ℕ)).eval z * iteratedDeriv (k : ℕ) u z

theorem eval₂_mobiusJetExpression (r : ℕ) (u : ℂ → ℂ) (z : ℂ)
    (j : Fin (r + 1)) :
    MvPolynomial.eval₂ (Polynomial.evalRingHom z)
      (fun k : Fin (r + 1) => iteratedDeriv (k : ℕ) u z)
      (mobiusJetExpression r j) = mobiusJetValue r u z j := by
  rw [mobiusJetExpression, MvPolynomial.eval₂_sum]
  simp [mobiusJetValue]

theorem eval₂_mobiusJetPullback (r : ℕ) (u : ℂ → ℂ) (z : ℂ)
    (Q : MvPolynomial (Fin (r + 1)) ℂ) :
    MvPolynomial.eval₂ (Polynomial.evalRingHom z)
      (fun k : Fin (r + 1) => iteratedDeriv (k : ℕ) u z)
      (mobiusJetPullback r Q) =
    MvPolynomial.eval (mobiusJetValue r u z) Q := by
  induction Q using MvPolynomial.induction_on with
  | C a => simp [mobiusJetPullback]
  | add P Q hP hQ =>
      simpa [mobiusJetPullback, map_add] using congrArg₂ (· + ·) hP hQ
  | mul_X P i hP =>
      rw [mobiusJetPullback, map_mul, MvPolynomial.map_X, map_mul,
        MvPolynomial.bind₁_X_right, map_mul, MvPolynomial.eval_X]
      rw [MvPolynomial.eval₂_mul]
      change MvPolynomial.eval₂ (Polynomial.evalRingHom z)
          (fun k : Fin (r + 1) => iteratedDeriv (k : ℕ) u z)
          (MvPolynomial.bind₁ (mobiusJetExpression r) (MvPolynomial.map Polynomial.C P)) *
        MvPolynomial.eval₂ (Polynomial.evalRingHom z)
          (fun k : Fin (r + 1) => iteratedDeriv (k : ℕ) u z)
          (mobiusJetExpression r i) = _
      rw [show MvPolynomial.bind₁ (mobiusJetExpression r)
          (MvPolynomial.map Polynomial.C P) = mobiusJetPullback r P from rfl,
        hP, eval₂_mobiusJetExpression]

noncomputable def mobiusJetExpansion (u : ℂ → ℂ) (j : ℕ) (z : ℂ) : ℂ :=
  ∑ k ∈ Finset.range (j + 1),
    (mobiusJetCoeff j k).eval z * iteratedDeriv k u z

theorem mobiusJet_sum_step (j : ℕ) (A B U : ℕ → ℂ) (hA : A (j + 1) = 0) :
    (∑ k ∈ Finset.range (j + 1), (A k * U k + B k * U (k + 1))) =
      ∑ k ∈ Finset.range (j + 2),
        (A k + if k = 0 then 0 else B (k - 1)) * U k := by
  have hAsum : (∑ k ∈ Finset.range (j + 2), A k * U k) =
      ∑ k ∈ Finset.range (j + 1), A k * U k := by
    rw [Finset.sum_range_succ, hA, zero_mul, add_zero]
  have hBsum :
      (∑ k ∈ Finset.range (j + 2),
        (if k = 0 then 0 else B (k - 1)) * U k) =
      ∑ k ∈ Finset.range (j + 1), B k * U (k + 1) := by
    rw [Finset.sum_range_succ']
    simp only [if_pos, zero_mul, Nat.succ_ne_zero, if_false, Nat.add_sub_cancel]
    rw [add_zero]
  calc
    (∑ k ∈ Finset.range (j + 1), (A k * U k + B k * U (k + 1))) =
        (∑ k ∈ Finset.range (j + 1), A k * U k) +
          ∑ k ∈ Finset.range (j + 1), B k * U (k + 1) := by
            rw [Finset.sum_add_distrib]
    _ = (∑ k ∈ Finset.range (j + 2), A k * U k) +
          ∑ k ∈ Finset.range (j + 2),
            (if k = 0 then 0 else B (k - 1)) * U k := by
            rw [hAsum, hBsum]
    _ = _ := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro k hk
      ring

theorem hasDerivAt_mobiusJetExpansion {u : ℂ → ℂ} {Ω : Set ℂ}
    (hu : ∀ z ∈ Ω, AnalyticAt ℂ u z) {z : ℂ} (hz : z ∈ Ω) (hz0 : z ≠ 0)
    (j : ℕ) :
    HasDerivAt (mobiusJetExpansion u j)
      (z⁻¹ ^ 2 * mobiusJetExpansion u (j + 1) z) z := by
  have hterm : ∀ k ∈ Finset.range (j + 1),
      HasDerivAt
        (fun w => (mobiusJetCoeff j k).eval w * iteratedDeriv k u w)
        ((mobiusJetCoeff j k).derivative.eval z * iteratedDeriv k u z +
          (mobiusJetCoeff j k).eval z * iteratedDeriv (k + 1) u z) z := by
    intro k hk
    exact ((mobiusJetCoeff j k).hasDerivAt z).mul
      (hasDerivAt_iteratedDeriv_of_analyticOn hu k hz)
  have hsum := HasDerivAt.fun_sum hterm
  have hzero : (mobiusJetCoeff j (j + 1)).derivative.eval z = 0 := by
    rw [mobiusJetCoeff_eq_zero_of_lt (Nat.lt_succ_self j), Polynomial.derivative_zero]
    simp
  have hstep := mobiusJet_sum_step j
    (fun k => (mobiusJetCoeff j k).derivative.eval z)
    (fun k => (mobiusJetCoeff j k).eval z)
    (fun k => iteratedDeriv k u z) hzero
  apply hsum.congr_deriv
  rw [hstep]
  simp only [mobiusJetExpansion, mobiusJetCoeff, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_add]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hz2 : z ^ 2 ≠ 0 := pow_ne_zero 2 hz0
  by_cases hk0 : k = 0
  · simp [hk0]
    field_simp [hz2]
  · simp [hk0]
    field_simp [hz2]

theorem neg_inv_neg_inv {z : ℂ} (hz : z ≠ 0) :
    (-(-z⁻¹))⁻¹ = z := by
  field_simp

theorem analyticAt_digamma_of_offPoles {z : ℂ}
    (hz : ∀ p : ℕ, z ≠ -(p : ℂ)) : AnalyticAt ℂ Complex.digamma z := by
  have h := analyticAt_iteratedDeriv_logDeriv 0 z hz
  simpa [iteratedDeriv_zero, Complex.digamma_def, logDeriv_apply] using h

theorem analyticAt_digammaReciprocalLimit_neg_inv {z : ℂ}
    (hz : ∀ p : ℕ, z ≠ -(p : ℂ)) (hz0 : z ≠ 0) :
    AnalyticAt ℂ digammaReciprocalLimit (-z⁻¹) := by
  have hx0 : -z⁻¹ ≠ 0 := neg_ne_zero.mpr (inv_ne_zero hz0)
  have hinner : AnalyticAt ℂ (fun x : ℂ => (-x)⁻¹) (-z⁻¹) :=
    analyticAt_id.neg.inv (neg_ne_zero.mpr hx0)
  have hψ : AnalyticAt ℂ Complex.digamma ((-(-z⁻¹))⁻¹) := by
    rw [neg_inv_neg_inv (z := z) hz0]
    exact analyticAt_digamma_of_offPoles hz
  have hcomp := AnalyticAt.comp (f := fun x : ℂ => (-x)⁻¹) (x := -z⁻¹) hψ hinner
  change AnalyticAt ℂ (fun x : ℂ => Complex.digamma ((-x)⁻¹)) (-z⁻¹)
  simpa only [Function.comp_def] using hcomp

theorem analyticAt_iteratedDeriv_of_analyticAt {u : ℂ → ℂ} {z : ℂ}
    (hu : AnalyticAt ℂ u z) : ∀ j : ℕ, AnalyticAt ℂ (iteratedDeriv j u) z := by
  intro j
  induction j with
  | zero => simpa [iteratedDeriv_zero] using hu
  | succ j ih =>
      rw [iteratedDeriv_succ]
      exact ih.deriv

theorem iteratedDeriv_digammaReciprocalLimit_neg_inv_eq_mobiusJetExpansion :
    ∀ (j : ℕ) (z : ℂ), (∀ p : ℕ, z ≠ -(p : ℂ)) → z ≠ 0 →
      iteratedDeriv j digammaReciprocalLimit (-z⁻¹) =
        mobiusJetExpansion Complex.digamma j z := by
  intro j
  induction j with
  | zero =>
      intro z hz hz0
      simp [mobiusJetExpansion, mobiusJetCoeff, iteratedDeriv_zero,
        digammaReciprocalLimit]
  | succ j ih =>
      intro z hz hz0
      let x : ℂ := -z⁻¹
      have hFan : AnalyticAt ℂ digammaReciprocalLimit x := by
        simpa [x] using analyticAt_digammaReciprocalLimit_neg_inv hz hz0
      have hFj : AnalyticAt ℂ (iteratedDeriv j digammaReciprocalLimit) x :=
        analyticAt_iteratedDeriv_of_analyticAt hFan j
      have hFderiv : HasDerivAt (iteratedDeriv j digammaReciprocalLimit)
          (iteratedDeriv (j + 1) digammaReciprocalLimit x) x := by
        simpa [iteratedDeriv_succ] using hFj.differentiableAt.hasDerivAt
      have hphi : HasDerivAt (fun w : ℂ => -w⁻¹) (z⁻¹ ^ 2) z := by
        simpa [inv_pow] using (hasDerivAt_inv hz0).neg
      have hcomp : HasDerivAt
          (fun w : ℂ => iteratedDeriv j digammaReciprocalLimit (-w⁻¹))
          (iteratedDeriv (j + 1) digammaReciprocalLimit x * z⁻¹ ^ 2) z := by
        simpa [x, Function.comp_def] using hFderiv.comp z hphi
      have hψan : ∀ w ∈ {w : ℂ | ∀ p : ℕ, w ≠ -(p : ℂ)},
          AnalyticAt ℂ Complex.digamma w := by
        intro w hw
        exact analyticAt_digamma_of_offPoles hw
      have hexp : HasDerivAt (mobiusJetExpansion Complex.digamma j)
          (z⁻¹ ^ 2 * mobiusJetExpansion Complex.digamma (j + 1) z) z :=
        hasDerivAt_mobiusJetExpansion hψan hz hz0 j
      have hev :
          (fun w : ℂ => iteratedDeriv j digammaReciprocalLimit (-w⁻¹)) =ᶠ[𝓝 z]
            mobiusJetExpansion Complex.digamma j := by
        filter_upwards [offPoles_isOpen.mem_nhds hz,
          (isOpen_compl_singleton.mem_nhds (Set.mem_compl_singleton_iff.mpr hz0))]
          with w hw hw0
        exact ih w hw (Set.mem_compl_singleton_iff.mp hw0)
      have heqderiv :
          iteratedDeriv (j + 1) digammaReciprocalLimit x * z⁻¹ ^ 2 =
            z⁻¹ ^ 2 * mobiusJetExpansion Complex.digamma (j + 1) z := by
        calc
          _ = deriv
              (fun w : ℂ => iteratedDeriv j digammaReciprocalLimit (-w⁻¹)) z :=
                hcomp.deriv.symm
          _ = deriv (mobiusJetExpansion Complex.digamma j) z := hev.deriv_eq
          _ = _ := hexp.deriv
      have hzInv2 : z⁻¹ ^ 2 ≠ 0 := pow_ne_zero 2 (inv_ne_zero hz0)
      have hcancel :
          z⁻¹ ^ 2 * iteratedDeriv (j + 1) digammaReciprocalLimit x =
            z⁻¹ ^ 2 * mobiusJetExpansion Complex.digamma (j + 1) z := by
        simpa [mul_comm] using heqderiv
      have hfinal := mul_left_cancel₀ hzInv2 hcancel
      simpa [x] using hfinal

theorem mobiusJetValue_eq_mobiusJetExpansion (r : ℕ) (u : ℂ → ℂ) (z : ℂ)
    (j : Fin (r + 1)) :
    mobiusJetValue r u z j = mobiusJetExpansion u (j : ℕ) z := by
  rw [mobiusJetValue, mobiusJetExpansion]
  rw [Fin.sum_univ_eq_sum_range
    (fun k : ℕ => (mobiusJetCoeff (j : ℕ) k).eval z * iteratedDeriv k u z) (r + 1)]
  symm
  apply Finset.sum_subset
  · exact Finset.range_mono j.isLt
  · intro k hkr hknot
    have hjk : (j : ℕ) < k := by
      rw [Finset.mem_range] at hkr
      simp only [Finset.mem_range, not_lt] at hknot
      omega
    rw [mobiusJetCoeff_eq_zero_of_lt hjk]
    simp

theorem mobiusJetValue_digamma_eq_limitJet (r : ℕ) (z : ℂ)
    (hz : ∀ p : ℕ, z ≠ -(p : ℂ)) (hz0 : z ≠ 0) (j : Fin (r + 1)) :
    mobiusJetValue r Complex.digamma z j =
      iteratedDeriv (j : ℕ) digammaReciprocalLimit (-z⁻¹) := by
  rw [mobiusJetValue_eq_mobiusJetExpansion]
  exact (iteratedDeriv_digammaReciprocalLimit_neg_inv_eq_mobiusJetExpansion
    (j : ℕ) z hz hz0).symm

theorem analyticAt_polyJetEval_digamma {m : ℕ}
    (G : MvPolynomial (Fin m) (Polynomial ℂ)) {z : ℂ}
    (hz : ∀ p : ℕ, z ≠ -(p : ℂ)) :
    AnalyticAt ℂ (fun w => polyJetEval m w G) z := by
  induction G using MvPolynomial.induction_on with
  | C p =>
      have heq : (fun w => polyJetEval m w (MvPolynomial.C p)) =
          fun w => p.eval w := by
        funext w
        simp [polyJetEval]
      rw [heq]
      exact (AnalyticOnNhd.eval_polynomial p) z (Set.mem_univ z)
  | add P Q hP hQ =>
      have heq : (fun w => polyJetEval m w (P + Q)) =
          fun w => polyJetEval m w P + polyJetEval m w Q := by
        funext w
        simp
      rw [heq]
      exact hP.add hQ
  | mul_X P i hP =>
      have heq : (fun w => polyJetEval m w (P * MvPolynomial.X i)) =
          fun w => polyJetEval m w P * iteratedDeriv (i : ℕ) Complex.digamma w := by
        funext w
        simp [polyJetEval, digammaJet]
      rw [heq]
      exact hP.mul
        (analyticAt_iteratedDeriv_of_analyticAt (analyticAt_digamma_of_offPoles hz) (i : ℕ))

theorem offPoles_isPreconnected :
    IsPreconnected {z : ℂ | ∀ p : ℕ, z ≠ -(p : ℂ)} := by
  have hoff : {z : ℂ | ∀ p : ℕ, z ≠ -(p : ℂ)} =
      (Set.range fun p : ℕ => (-(p : ℕ) : ℂ))ᶜ := by
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_compl_iff, Set.mem_range, not_exists]
    constructor
    · intro h p hp
      exact h p hp.symm
    · intro h p hp
      exact h p hp.symm
  rw [hoff]
  refine (Set.Countable.isPathConnected_compl_of_one_lt_rank ?_
    (Set.countable_range _)).isConnected.isPreconnected
  rw [Complex.rank_real_complex]
  norm_num

theorem polyJetEval_eq_zero_of_eventually {m : ℕ}
    (G : MvPolynomial (Fin m) (Polynomial ℂ)) {z₀ : ℂ}
    (hz₀ : ∀ p : ℕ, z₀ ≠ -(p : ℂ))
    (hlocal : ∀ᶠ z in 𝓝 z₀, polyJetEval m z G = 0) : G = 0 := by
  let Ω : Set ℂ := {z : ℂ | ∀ p : ℕ, z ≠ -(p : ℂ)}
  have han : AnalyticOnNhd ℂ (fun z => polyJetEval m z G) Ω := by
    intro z hz
    exact analyticAt_polyJetEval_digamma G hz
  letI : NeBot (𝓝[≠] z₀) := NormedField.nhdsNE_neBot z₀
  have hfreq : ∃ᶠ z in 𝓝[≠] z₀, polyJetEval m z G = 0 :=
    (hlocal.filter_mono nhdsWithin_le_nhds).frequently
  have hzero : Set.EqOn (fun z => polyJetEval m z G) 0 Ω :=
    han.eqOn_zero_of_preconnected_of_frequently_eq_zero offPoles_isPreconnected hz₀ hfreq
  exact polyJetEval_offPole_eq_zero G (fun z hz => hzero hz)

theorem hypertranscendental_digamma_comp_Gamma :
    Hypertranscendental (fun z => Complex.digamma (Complex.Gamma z)) := by
  intro hDA
  obtain ⟨r, Q, hQ, hQvan⟩ :=
    exists_local_autonomous_annihilator_digammaReciprocalLimit hDA
  let G : MvPolynomial (Fin (r + 1)) (Polynomial ℂ) := mobiusJetPullback r Q
  have hGne : G ≠ 0 := by
    exact mobiusJetPullback_ne_zero hQ
  have honeOff : ∀ p : ℕ, (1 : ℂ) ≠ -(p : ℂ) := by
    intro p hp
    have hre := congrArg Complex.re hp
    simp only [Complex.one_re, Complex.neg_re, Complex.natCast_re] at hre
    have hpnonneg : (0 : ℝ) ≤ p := Nat.cast_nonneg p
    linarith
  have hphiCont : ContinuousAt (fun z : ℂ => -z⁻¹) 1 := by
    simpa using (ContinuousAt.inv₀ continuousAt_id
      (one_ne_zero : (1 : ℂ) ≠ 0)).neg
  have hcenter : -((1 : ℂ)⁻¹) ∈ reciprocalGammaBlowUpDisk := by
    simp [reciprocalGammaBlowUpDisk]
  have hpre : ∀ᶠ z : ℂ in 𝓝 1, -z⁻¹ ∈ reciprocalGammaBlowUpDisk := by
    exact hphiCont (isOpen_reciprocalGammaBlowUpDisk.mem_nhds hcenter)
  have hlocal : ∀ᶠ z : ℂ in 𝓝 1, polyJetEval (r + 1) z G = 0 := by
    filter_upwards [hpre, offPoles_isOpen.mem_nhds honeOff,
      (isOpen_compl_singleton.mem_nhds
        (Set.mem_compl_singleton_iff.mpr (one_ne_zero : (1 : ℂ) ≠ 0)))]
      with z hzU hzOff hz0mem
    have hz0 : z ≠ 0 := Set.mem_compl_singleton_iff.mp hz0mem
    have hvalue := hQvan (-z⁻¹) hzU
    have hmv : mobiusJetValue r Complex.digamma z =
        fun j : Fin (r + 1) => iteratedDeriv (j : ℕ) digammaReciprocalLimit (-z⁻¹) := by
      funext j
      exact mobiusJetValue_digamma_eq_limitJet r z hzOff hz0 j
    change MvPolynomial.eval₂ (Polynomial.evalRingHom z)
      (fun j : Fin (r + 1) => iteratedDeriv (j : ℕ) Complex.digamma z) G = 0
    rw [show G = mobiusJetPullback r Q from rfl, eval₂_mobiusJetPullback, hmv]
    exact hvalue
  exact hGne (polyJetEval_eq_zero_of_eventually G honeOff hlocal)

end

end GaloisForLFunctions
