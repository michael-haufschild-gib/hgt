import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Summable principal parts of a logarithmic derivative

Summable residues on a discrete divisor define a normally convergent Cauchy sum away
from the divisor. Subtracting the multiplicity residues of a weighted logarithmic
derivative leaves a holomorphic function, including at the zeros.
-/

open Complex Filter Topology Set Metric

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- The Cauchy sum of the residues on a set of poles. -/
def residueCauchySum (E : Set ℂ) (r : ℂ → ℂ) (z : ℂ) : ℂ :=
  ∑' p : E, r p / (z - p)

/-- Uniform separation from the poles bounds the entire principal-part sum. -/
theorem norm_residueCauchySum_le {E : Set ℂ} {r : ℂ → ℂ}
    (hr : Summable fun p : E => ‖r p‖) {z : ℂ} {δ : ℝ} (hδ : 0 < δ)
    (hd : ∀ p ∈ E, δ ≤ ‖z - p‖) :
    ‖residueCauchySum E r z‖ ≤ (∑' p : E, ‖r p‖) / δ := by
  exact tsum_of_norm_bounded (hr.hasSum.div_const δ) fun p => by
    rw [norm_div]
    exact div_le_div_of_nonneg_left (norm_nonneg _) hδ (hd p p.2)

/-- Separation at the centre persists on the half-radius ball. -/
theorem half_separation_le {z p w : ℂ} {δ : ℝ}
    (hd : δ ≤ ‖z - p‖) (hw : w ∈ ball z (δ / 2)) : δ / 2 ≤ ‖w - p‖ := by
  have hw' : ‖w - z‖ < δ / 2 := mem_ball_iff_norm.mp hw
  have ht : ‖z - p‖ ≤ ‖w - z‖ + ‖w - p‖ := by
    calc
      ‖z - p‖ = ‖(z - w) + (w - p)‖ := by congr 1; ring
      _ ≤ ‖z - w‖ + ‖w - p‖ := norm_add_le _ _
      _ = ‖w - z‖ + ‖w - p‖ := by rw [norm_sub_rev z w]
  linarith only [hd, hw', ht]

/-- A Cauchy sum with summable residues is analytic wherever its poles are separated. -/
theorem analyticAt_residueCauchySum {E : Set ℂ} {r : ℂ → ℂ}
    (hr : Summable fun p : E => ‖r p‖) {z : ℂ} {δ : ℝ} (hδ : 0 < δ)
    (hd : ∀ p ∈ E, δ ≤ ‖z - p‖) : AnalyticAt ℂ (residueCauchySum E r) z := by
  have hsep : ∀ (p : E) (w : ℂ), w ∈ ball z (δ / 2) → δ / 2 ≤ ‖w - p‖ :=
    fun p w hw => half_separation_le (hd p p.2) hw
  have hdiff : DifferentiableOn ℂ (residueCauchySum E r) (ball z (δ / 2)) := by
    refine Complex.differentiableOn_tsum_of_summable_norm (hr.div_const (δ / 2))
      ?_ isOpen_ball ?_
    · intro p w hw
      exact ((differentiableAt_const (r p)).div (differentiableAt_id.sub_const _)
        (norm_pos_iff.mp ((half_pos hδ).trans_le (hsep p w hw)))).differentiableWithinAt
    · intro p w hw
      rw [norm_div]
      exact div_le_div_of_nonneg_left (norm_nonneg _) (half_pos hδ) (hsep p w hw)
  exact hdiff.analyticAt (ball_mem_nhds z (half_pos hδ))

/-- Removing the possible pole at the centre gives an analytic tail. -/
theorem analyticAt_residueCauchyTail {E : Set ℂ} {r : ℂ → ℂ}
    (hr : Summable fun p : E => ‖r p‖) {z : ℂ} {δ : ℝ} (hδ : 0 < δ)
    (hd : ∀ p ∈ E, p ≠ z → δ ≤ ‖z - p‖) :
    AnalyticAt ℂ (fun w => ∑' p : E, if (p : ℂ) = z then 0 else r p / (w - p)) z := by
  classical
  have hsep : ∀ (p : E), (p : ℂ) ≠ z → ∀ w ∈ ball z (δ / 2), δ / 2 ≤ ‖w - p‖ :=
    fun p hp w hw => half_separation_le (hd p p.2 hp) hw
  have hdiff : DifferentiableOn ℂ
      (fun w => ∑' p : E, if (p : ℂ) = z then 0 else r p / (w - p))
      (ball z (δ / 2)) := by
    refine Complex.differentiableOn_tsum_of_summable_norm (hr.div_const (δ / 2))
      ?_ isOpen_ball ?_
    · intro p
      by_cases hp : (p : ℂ) = z
      · simpa only [if_pos hp] using (differentiableOn_const 0 :
          DifferentiableOn ℂ (fun _ : ℂ => (0 : ℂ)) (ball z (δ / 2)))
      · simp only [if_neg hp]
        intro w hw
        exact ((differentiableAt_const (r p)).div (differentiableAt_id.sub_const _)
          (norm_pos_iff.mp ((half_pos hδ).trans_le (hsep p hp w hw)))).differentiableWithinAt
    · intro p w hw
      by_cases hp : (p : ℂ) = z
      · simp only [if_pos hp, norm_zero]
        exact div_nonneg (norm_nonneg _) (half_pos hδ).le
      · rw [if_neg hp, norm_div]
        exact div_le_div_of_nonneg_left (norm_nonneg _) (half_pos hδ) (hsep p hp w hw)
  exact hdiff.analyticAt (ball_mem_nhds z (half_pos hδ))

/-- The pole at the centre splits off from the normally convergent tail. -/
theorem residueCauchySum_eq_pole_add_tail {E : Set ℂ} {r : ℂ → ℂ}
    (hr : Summable fun p : E => ‖r p‖) {z : ℂ} (hz : z ∈ E) {δ : ℝ} (hδ : 0 < δ)
    (hd : ∀ p ∈ E, p ≠ z → δ ≤ ‖z - p‖) :
    residueCauchySum E r =ᶠ[𝓝[≠] z]
      fun w => r z / (w - z) + ∑' p : E, if (p : ℂ) = z then 0 else r p / (w - p) := by
  classical
  filter_upwards [nhdsWithin_le_nhds (ball_mem_nhds z (half_pos hδ)),
    self_mem_nhdsWithin] with w hw (hwz : w ≠ z)
  let ε := min (δ / 2) ‖w - z‖
  have hε : 0 < ε := lt_min (half_pos hδ) (norm_pos_iff.mpr (sub_ne_zero.mpr hwz))
  have hsep : ∀ p : E, ε ≤ ‖w - p‖ := by
    intro p
    by_cases hp : (p : ℂ) = z
    · rw [hp]
      exact min_le_right _ _
    · exact (min_le_left _ _).trans (half_separation_le (hd p p.2 hp) hw)
  have hs : Summable fun p : E => r p / (w - p) :=
    Summable.of_norm (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun p => by
      rw [norm_div]
      exact div_le_div_of_nonneg_left (norm_nonneg _) hε (hsep p)) (hr.div_const ε))
  simpa only [residueCauchySum, Subtype.ext_iff] using
    hs.tsum_eq_add_tsum_ite (⟨z, hz⟩ : E)

/-- Finite analytic order separates a point from every other zero. -/
theorem exists_separation_from_other_zeros {F : ℂ → ℂ} {E : Set ℂ} {z : ℂ}
    (hF : AnalyticAt ℂ F z) (hfin : analyticOrderAt F z ≠ ⊤)
    (hE : ∀ p ∈ E, F p = 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ p ∈ E, p ≠ z → δ ≤ ‖z - p‖ := by
  have hev : ∀ᶠ w in 𝓝[≠] z, F w ≠ 0 :=
    hF.eventually_eq_zero_or_eventually_ne_zero.resolve_left fun h =>
      hfin (analyticOrderAt_eq_top.mpr h)
  rw [eventually_nhdsWithin_iff] at hev
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨δ, hδ, fun p hp hpz => le_of_not_gt fun hnear => ?_⟩
  exact (hball (by simpa only [dist_eq_norm, norm_sub_rev] using hnear) hpz) (hE p hp)

/-- Multiplication by an analytic weight multiplies the residue by its value at the zero. -/
theorem exists_weighted_logDeriv_principalPart {F K : ℂ → ℂ} {z : ℂ}
    (hF : AnalyticAt ℂ F z) (hfin : analyticOrderAt F z ≠ ⊤)
    (hK : AnalyticAt ℂ K z) :
    ∃ H : ℂ → ℂ, AnalyticAt ℂ H z ∧
      (fun w => deriv F w * K w / F w) =ᶠ[𝓝[≠] z]
        fun w => ((analyticOrderNatAt F z : ℂ) * K z) / (w - z) + H w := by
  obtain ⟨g, hg, hg0, hfg⟩ := (hF.analyticOrderNatAt_eq_iff hfin).mp rfl
  simp only [smul_eq_mul] at hfg
  change F =ᶠ[𝓝 z] (fun w => (w - z) ^ analyticOrderNatAt F z * g w) at hfg
  let h := logDeriv g
  have hh : AnalyticAt ℂ h z := hg.deriv.div hg hg0
  have heq : logDeriv F =ᶠ[𝓝[≠] z]
      fun w => (analyticOrderNatAt F z : ℂ) / (w - z) + h w := by
    filter_upwards [nhdsWithin_le_nhds hfg.eventuallyEq_nhds,
      nhdsWithin_le_nhds (hg.continuousAt.eventually_ne hg0),
      nhdsWithin_le_nhds hg.eventually_analyticAt, self_mem_nhdsWithin]
      with w hw hgw hga (hwz : w ≠ z)
    have hsub : w - z ≠ 0 := sub_ne_zero.mpr hwz
    have hmodel : logDeriv F w =
        logDeriv (fun v => (v - z) ^ analyticOrderNatAt F z * g v) w := by
      rw [logDeriv_apply, logDeriv_apply, hw.deriv_eq, hw.eq_of_nhds]
    rw [hmodel, logDeriv_mul (f := fun v => (v - z) ^ analyticOrderNatAt F z) (g := g)
      w (pow_ne_zero _ hsub) hgw
      ((differentiableAt_id.sub_const z).fun_pow _) hga.differentiableAt]
    congr 1
    have hc := logDeriv_comp (f := fun v : ℂ => v ^ analyticOrderNatAt F z)
      (g := fun v : ℂ => v - z) (x := w) (by fun_prop)
      (differentiableAt_id.sub_const z)
    have hd : deriv (fun v : ℂ => v - z) w = 1 := by simp
    simpa only [Function.comp_def, logDeriv_pow, hd, mul_one] using hc
  obtain ⟨ε, hε, han⟩ := Metric.eventually_nhds_iff.mp hK.eventually_analyticAt
  have hKd : DifferentiableOn ℂ K (ball z ε) :=
    fun w hw => (han hw).differentiableAt.differentiableWithinAt
  have hds : AnalyticAt ℂ (dslope K z) z :=
    ((Complex.differentiableOn_dslope (ball_mem_nhds z hε)).mpr hKd).analyticAt
      (ball_mem_nhds z hε)
  refine ⟨fun w => (analyticOrderNatAt F z : ℂ) * dslope K z w + h w * K w,
    (analyticAt_const.mul hds).add (hh.mul hK), ?_⟩
  filter_upwards [heq, self_mem_nhdsWithin] with w hw (hwz : w ≠ z)
  have hden : w - z ≠ 0 := sub_ne_zero.mpr hwz
  have hquot : deriv F w * K w / F w = logDeriv F w * K w := by
    rw [logDeriv_apply]
    ring
  rw [hquot, hw, dslope_of_ne K hwz, slope_def_module, smul_eq_mul]
  field_simp [hden]
  <;> ring

/-- The actual residues of `K F'/F` at the zeros of `F`. -/
def weightedLogResidue (F K : ℂ → ℂ) (z : ℂ) : ℂ :=
  (analyticOrderNatAt F z : ℂ) * K z

/-- Subtracting all summable multiplicity residues removes every pole of a weighted
logarithmic derivative. The divisor need not be finite or uniformly separated. -/
theorem exists_holomorphic_sub_residueCauchySum {U E : Set ℂ} {F K : ℂ → ℂ}
    (hU : IsOpen U) (hF : DifferentiableOn ℂ F U) (hK : DifferentiableOn ℂ K U)
    (hfin : ∀ z ∈ U, analyticOrderAt F z ≠ ⊤)
    (hE : ∀ p ∈ E, F p = 0) (hcover : ∀ z ∈ U, F z = 0 → z ∈ E)
    (hr : Summable fun p : E => ‖weightedLogResidue F K p‖) :
    ∃ Φ : ℂ → ℂ, DifferentiableOn ℂ Φ U ∧ ∀ z ∈ U, F z ≠ 0 →
      Φ z = deriv F z * K z / F z - residueCauchySum E (weightedLogResidue F K) z := by
  let Q := fun z => deriv F z * K z / F z - residueCauchySum E (weightedLogResidue F K) z
  have hregular : ∀ z ∈ U, F z ≠ 0 → AnalyticAt ℂ Q z := by
    intro z hz hz0
    have hFa := hF.analyticAt (hU.mem_nhds hz)
    obtain ⟨δ, hδ, hd⟩ := exists_separation_from_other_zeros hFa (hfin z hz) hE
    have hsep : ∀ p ∈ E, δ ≤ ‖z - p‖ := by
      intro p hp
      exact hd p hp fun hpz => hz0 (hpz ▸ hE p hp)
    exact ((hFa.deriv.mul (hK.analyticAt (hU.mem_nhds hz))).div hFa hz0).sub
      (analyticAt_residueCauchySum hr hδ hsep)
  have hlocal : ∀ z ∈ U, ∃ H : ℂ → ℂ, AnalyticAt ℂ H z ∧ Q =ᶠ[𝓝[≠] z] H := by
    intro z hz
    by_cases hz0 : F z = 0
    · have hFa := hF.analyticAt (hU.mem_nhds hz)
      obtain ⟨δ, hδ, hd⟩ := exists_separation_from_other_zeros hFa (hfin z hz) hE
      obtain ⟨H, hH, heq⟩ := exists_weighted_logDeriv_principalPart hFa (hfin z hz)
        (hK.analyticAt (hU.mem_nhds hz))
      have htail := analyticAt_residueCauchyTail hr hδ hd
      have hsplit := residueCauchySum_eq_pole_add_tail hr (hcover z hz hz0) hδ hd
      refine ⟨fun w => H w - ∑' p : E,
        if (p : ℂ) = z then 0 else weightedLogResidue F K p / (w - p), hH.sub htail, ?_⟩
      filter_upwards [heq, hsplit] with w hw hsw
      dsimp only [Q]
      rw [hw, hsw]
      unfold weightedLogResidue
      ring
    · exact ⟨Q, hregular z hz hz0, Filter.EventuallyEq.rfl⟩
  have hmero : MeromorphicOn Q U := by
    intro z hz
    obtain ⟨H, hH, heq⟩ := hlocal z hz
    exact hH.meromorphicAt.congr heq.symm
  have horder : ∀ z ∈ U, 0 ≤ meromorphicOrderAt Q z := by
    intro z hz
    obtain ⟨H, hH, heq⟩ := hlocal z hz
    rw [meromorphicOrderAt_congr heq]
    exact hH.meromorphicOrderAt_nonneg
  refine ⟨toMeromorphicNFOn Q U, ?_, ?_⟩
  · intro z hz
    apply DifferentiableAt.differentiableWithinAt
    apply AnalyticAt.differentiableAt
    apply (meromorphicNFOn_toMeromorphicNFOn Q U hz).meromorphicOrderAt_nonneg_iff_analyticAt.mp
    rw [meromorphicOrderAt_toMeromorphicNFOn hmero hz]
    exact horder z hz
  · intro z hz hz0
    rw [toMeromorphicNFOn_eq_toMeromorphicNFAt hmero hz,
      toMeromorphicNFAt_eq_self.mpr (hregular z hz hz0).meromorphicNFAt]

end GaloisForLFunctions.HTGeometry
