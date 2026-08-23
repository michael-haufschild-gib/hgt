import GaloisForLFunctions.RHTower.SoninMellinMultiplier
import GaloisForLFunctions.RHTower.MellinLineMass
import GaloisForLFunctions.HTGeometry.LogWeightedPoisson
import Mathlib.Analysis.MellinInversion

/-!
# Mellin inversion for a vector of `L_a`

Burnol's Proposition 5.4 needs the value of the inverse Mellin transform at a point of the aperture
band.  Mathlib's `mellinInv_mellin_eq` supplies the inversion; what has to be provided is

* `MellinConvergent f σ` for `0 < σ < 1/2` — the band contributes `∫_0^a t^{σ-1}dt < ∞`, the tail
  is Cauchy--Schwarz against `t^{σ-1} ∈ L²(a,∞)`;
* `VerticalIntegrable (mellin f) σ` — this is where Definition 12's quick decrease enters;
* continuity at the evaluation point — for which the `L²` class is replaced by the representative
  that is *exactly* constant on the band.

## Main results

* `mellin_eq_extendedMellinContinuation` — the two charts agree: `mellin f w = M(f)(1−w)`.
* `mellinConvergent_of_band`
* `bandNormalize`, `mellinInv_eq_band_const` — the inverse transform is the band constant on the
  open band.
-/

open Complex Set Topology Filter MeasureTheory

namespace RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

/-! ## Convergence of the Mellin integral -/

theorem integrableOn_cpow_mul_Ioc_of_band {a : ℝ} (ha : 0 < a) {f : SoninL2} {d : ℂ}
    (hd : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ centralInterval a → (f : ℝ → ℂ) t = d)
    {s : ℂ} (hs : s.re < 1) :
    IntegrableOn (fun t : ℝ => ((t : ℝ) : ℂ) ^ (-s) * (f : ℝ → ℂ) t) (Ioc 0 a) volume := by
  have hconst : IntegrableOn (fun t : ℝ => ((t : ℝ) : ℂ) ^ (-s) * d) (Ioc 0 a) volume := by
    have hbase : IntegrableOn (fun t : ℝ => t ^ (-s.re)) (Ioo 0 a) volume :=
      (intervalIntegral.integrableOn_Ioo_rpow_iff ha).2 (by linarith)
    have hIoo : IntegrableOn (fun t : ℝ => ((t : ℝ) : ℂ) ^ (-s) * d) (Ioo 0 a) volume := by
      refine Integrable.mono' (hbase.const_mul ‖d‖) ?_ ?_
      · refine (ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioo)
        refine ContinuousOn.mul ?_ continuousOn_const
        intro t ht
        exact (Complex.continuousAt_ofReal_cpow_const t (-s)
          (Or.inr (ne_of_gt ht.1))).continuousWithinAt
      · filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with t ht
        have ht0 : (0 : ℝ) < t := ht.1
        rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht0, Complex.neg_re]
        exact le_of_eq (by ring)
    rw [IntegrableOn, ← Measure.restrict_congr_set Ioo_ae_eq_Ioc]
    exact hIoo
  refine hconst.congr_fun_ae ?_
  have hae : ∀ᵐ t ∂(volume.restrict (Ioc 0 a)), (f : ℝ → ℂ) t = d := by
    have hmem : ∀ᵐ t ∂(volume.restrict (Ioc 0 a)), t ∈ centralInterval a := by
      filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with t ht
      rw [centralInterval, Set.mem_Icc]
      exact ⟨by linarith [ht.1], ht.2⟩
    filter_upwards [ae_restrict_of_ae hd, hmem] with t h1 h2
    exact h1 h2
  filter_upwards [hae] with t ht
  rw [ht]

/-- **The Mellin integral of a vector of `L_a` converges on the strip `0 < Re w < 1/2`.** -/
theorem mellinConvergent_of_band {a : ℝ} (ha : 0 < a) {f : SoninL2} {d : ℂ}
    (hd : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ centralInterval a → (f : ℝ → ℂ) t = d)
    {w : ℂ} (hw0 : 0 < w.re) (hw1 : w.re < 1 / 2) :
    MellinConvergent ((f : ℝ → ℂ)) w := by
  have hs : ((1 : ℂ) - w).re < 1 := by simp; linarith
  have hs' : 1 / 2 < ((1 : ℂ) - w).re := by simp; linarith
  have hband := integrableOn_cpow_mul_Ioc_of_band ha hd (s := 1 - w) hs
  have htail := integrableOn_cpow_mul_Ioi ha f (s := 1 - w) hs'
  have hsplit : Ioi (0 : ℝ) = Ioc 0 a ∪ Ioi a := by
    rw [Set.Ioc_union_Ioi_eq_Ioi ha.le]
  have hun : IntegrableOn (fun t : ℝ => ((t : ℝ) : ℂ) ^ (-(1 - w)) * (f : ℝ → ℂ) t)
      (Ioi 0) volume := by
    rw [hsplit]
    exact hband.union htail
  refine hun.congr_fun_ae ?_
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
  have ht0 : (0 : ℝ) < t := ht
  have hexp : -(1 - w) = w - 1 := by ring
  rw [hexp, smul_eq_mul]

/-- The two Mellin charts agree. -/
theorem mellin_eq_extendedMellinContinuation {a : ℝ} (ha : 0 < a) {f : SoninL2} {c d : ℂ}
    (hev : f ∈ evenSubspace)
    (hc : ∀ᵐ u ∂(volume : Measure ℝ), u ∈ centralInterval a →
      ((fourierUnitary f : SoninL2) : ℝ → ℂ) u = c)
    (hd : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ centralInterval a → (f : ℝ → ℂ) t = d)
    {w : ℂ} (hw0 : 0 < w.re) (hw1 : w.re < 1 / 2) :
    mellin ((f : ℝ → ℂ)) w = extendedMellinContinuation a c d f (1 - w) := by
  set s : ℂ := 1 - w with hsdef
  have hsre : s.re = 1 - w.re := by rw [hsdef]; simp
  have hs1 : 1 / 2 < s.re := by rw [hsre]; linarith
  have hs2 : s.re < 1 := by rw [hsre]; linarith
  have hs0 : s ≠ 0 := by
    intro h; rw [h] at hsre; simp at hsre; linarith
  have hs1' : s ≠ 1 := by
    intro h; rw [h] at hsre; simp at hsre; linarith
  have hval := (differentiable_extendedMellinNumerator ha hev hc hd).2 s hs1 hs2
  have hden : s * (1 - s) ≠ 0 := mul_ne_zero hs0 (sub_ne_zero.2 fun h => hs1' h.symm)
  have hmel : mellin ((f : ℝ → ℂ)) w
      = ∫ t in Ioi (0 : ℝ), ((t : ℝ) : ℂ) ^ (-s) * (f : ℝ → ℂ) t := by
    rw [mellin]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have hexp : w - 1 = -s := by rw [hsdef]; ring
    rw [hexp, smul_eq_mul]
  rw [hmel, extendedMellinContinuation, ← hval]
  field_simp

/-! ## Vertical integrability from quick decrease -/

theorem continuous_mellin_vertical {a : ℝ} (ha : 0 < a) {f : SoninL2} {c d : ℂ}
    (hev : f ∈ evenSubspace)
    (hc : ∀ᵐ u ∂(volume : Measure ℝ), u ∈ centralInterval a →
      ((fourierUnitary f : SoninL2) : ℝ → ℂ) u = c)
    (hd : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ centralInterval a → (f : ℝ → ℂ) t = d)
    {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1 / 2) :
    Continuous fun y : ℝ => mellin ((f : ℝ → ℂ)) ((σ : ℂ) + (y : ℂ) * I) := by
  have hfun : ∀ y : ℝ, mellin ((f : ℝ → ℂ)) ((σ : ℂ) + (y : ℂ) * I)
      = extendedMellinContinuation a c d f (1 - ((σ : ℂ) + (y : ℂ) * I)) := by
    intro y
    refine mellin_eq_extendedMellinContinuation ha hev hc hd ?_ ?_
    · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
        Complex.ofReal_im, mul_zero, zero_mul, sub_zero, add_zero, zero_sub, neg_zero]
      linarith
    · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
        Complex.ofReal_im, mul_zero, zero_mul, sub_zero, add_zero, zero_sub, neg_zero]
      linarith
  refine Continuous.congr ?_ (fun y => (hfun y).symm)
  have hpath : Continuous fun y : ℝ => (1 : ℂ) - ((σ : ℂ) + (y : ℂ) * I) := by fun_prop
  refine continuous_iff_continuousAt.2 fun y => ?_
  have hre : ((1 : ℂ) - ((σ : ℂ) + (y : ℂ) * I)).re = 1 - σ := by simp
  have h0 : ((1 : ℂ) - ((σ : ℂ) + (y : ℂ) * I)) ≠ 0 := by
    intro h; rw [h] at hre; simp at hre; linarith
  have h1 : ((1 : ℂ) - ((σ : ℂ) + (y : ℂ) * I)) ≠ 1 := by
    intro h; rw [h] at hre; simp at hre; linarith
  exact ContinuousAt.comp (g := extendedMellinContinuation a c d f)
    (f := fun u : ℝ => (1 : ℂ) - ((σ : ℂ) + (u : ℂ) * I)) (x := y)
    (differentiableAt_extendedMellinContinuation ha hev hc hd h0 h1).continuousAt
    hpath.continuousAt

theorem verticalIntegrable_mellin {a : ℝ} (ha : 0 < a) {f : SoninL2} {c d : ℂ}
    (hev : f ∈ evenSubspace)
    (hc : ∀ᵐ u ∂(volume : Measure ℝ), u ∈ centralInterval a →
      ((fourierUnitary f : SoninL2) : ℝ → ℂ) u = c)
    (hd : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ centralInterval a → (f : ℝ → ℂ) t = d)
    (hrapid : HasStripRapidDecrease (extendedMellinContinuation a c d f))
    {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1 / 2) :
    Complex.VerticalIntegrable (mellin ((f : ℝ → ℂ))) σ volume := by
  show Integrable (fun y : ℝ => mellin ((f : ℝ → ℂ)) ((σ : ℂ) + (y : ℂ) * I)) volume
  have hcont := continuous_mellin_vertical ha hev hc hd hσ0 hσ1
  obtain ⟨T, C, hC0, hbound⟩ := hrapid (1 - σ) (1 - σ) 2
  set T₀ : ℝ := max T 1 with hT₀def
  have hT₀1 : (1 : ℝ) ≤ T₀ := le_max_right _ _
  have hTT₀ : T ≤ T₀ := le_max_left _ _
  -- a bound on the compact part
  obtain ⟨M₀, hM₀⟩ := (isCompact_Icc (a := -T₀) (b := T₀)).exists_bound_of_continuousOn
    hcont.continuousOn
  have hM₀0 : 0 ≤ M₀ := le_trans (norm_nonneg _) (hM₀ 0 (by
    rw [Set.mem_Icc]
    constructor <;> linarith))
  set K : ℝ := C + M₀ * (1 + T₀) ^ ((3 : ℝ) / 2) with hKdef
  have hK0 : 0 ≤ K := by
    rw [hKdef]
    have : (0:ℝ) ≤ M₀ * (1 + T₀) ^ ((3 : ℝ) / 2) := by positivity
    linarith
  refine Integrable.mono'
    ((GaloisForLFunctions.HTGeometry.integrable_one_add_abs_rpow_three_halves).const_mul K)
    hcont.aestronglyMeasurable ?_
  filter_upwards with y
  have hbase : (0 : ℝ) < 1 + |y| := by positivity
  have hone : (1 : ℝ) ≤ 1 + |y| := by simp [abs_nonneg]
  rcases le_or_gt |y| T₀ with hy | hy
  · -- compact part
    have hval : ‖mellin ((f : ℝ → ℂ)) ((σ : ℂ) + (y : ℂ) * I)‖ ≤ M₀ := by
      refine hM₀ y ?_
      rw [Set.mem_Icc]
      constructor <;> [linarith [neg_abs_le y]; linarith [le_abs_self y]]
    have hw : (1:ℝ) ≤ (1 + |y|) ^ (-((3 : ℝ) / 2)) * (1 + T₀) ^ ((3 : ℝ) / 2) := by
      have h1 : (1 + |y|) ^ ((3:ℝ)/2) ≤ (1 + T₀) ^ ((3:ℝ)/2) :=
        Real.rpow_le_rpow (by positivity) (by linarith) (by norm_num)
      have hpos : (0:ℝ) < (1 + |y|) ^ ((3:ℝ)/2) := Real.rpow_pos_of_pos hbase _
      rw [Real.rpow_neg hbase.le, inv_mul_eq_div, le_div_iff₀ hpos]
      linarith
    have hpos : (0:ℝ) < (1 + |y|) ^ (-((3 : ℝ) / 2)) := Real.rpow_pos_of_pos hbase _
    calc ‖mellin ((f : ℝ → ℂ)) ((σ : ℂ) + (y : ℂ) * I)‖ ≤ M₀ := hval
      _ = M₀ * 1 := by ring
      _ ≤ M₀ * ((1 + |y|) ^ (-((3 : ℝ) / 2)) * (1 + T₀) ^ ((3 : ℝ) / 2)) := by
          exact mul_le_mul_of_nonneg_left hw hM₀0
      _ = (M₀ * (1 + T₀) ^ ((3 : ℝ) / 2)) * (1 + |y|) ^ (-((3 : ℝ) / 2)) := by ring
      _ ≤ K * (1 + |y|) ^ (-((3 : ℝ) / 2)) := by
          refine mul_le_mul_of_nonneg_right ?_ hpos.le
          rw [hKdef]; linarith
  · -- the tail: quick decrease
    have hyT : T ≤ |y| := le_trans hTT₀ hy.le
    have hs : ((1 : ℂ) - ((σ : ℂ) + (y : ℂ) * I)).re = 1 - σ := by simp
    have hsim : |((1 : ℂ) - ((σ : ℂ) + (y : ℂ) * I)).im| = |y| := by
      have h : ((1 : ℂ) - ((σ : ℂ) + (y : ℂ) * I)).im = -y := by simp
      rw [h, abs_neg]
    have hval := hbound ((1 : ℂ) - ((σ : ℂ) + (y : ℂ) * I)) (by rw [hs]) (by rw [hs])
      (by rw [hsim]; exact hyT)
    rw [hsim] at hval
    have hfun : mellin ((f : ℝ → ℂ)) ((σ : ℂ) + (y : ℂ) * I)
        = extendedMellinContinuation a c d f (1 - ((σ : ℂ) + (y : ℂ) * I)) :=
      mellin_eq_extendedMellinContinuation ha hev hc hd (by simp; linarith) (by simp; linarith)
    rw [hfun]
    have hmono : (1 + |y|) ^ (-(2 : ℝ)) ≤ (1 + |y|) ^ (-((3 : ℝ) / 2)) := by
      refine Real.rpow_le_rpow_of_exponent_le hone (by norm_num)
    have hpos : (0:ℝ) < (1 + |y|) ^ (-((3 : ℝ) / 2)) := Real.rpow_pos_of_pos hbase _
    calc ‖extendedMellinContinuation a c d f (1 - ((σ : ℂ) + (y : ℂ) * I))‖
        ≤ C * (1 + |y|) ^ (-((2 : ℕ) : ℝ)) := hval
      _ ≤ C * (1 + |y|) ^ (-((3 : ℝ) / 2)) := by
          refine mul_le_mul_of_nonneg_left ?_ hC0
          simpa using hmono
      _ ≤ K * (1 + |y|) ^ (-((3 : ℝ) / 2)) := by
          refine mul_le_mul_of_nonneg_right ?_ hpos.le
          rw [hKdef]
          have : (0:ℝ) ≤ M₀ * (1 + T₀) ^ ((3 : ℝ) / 2) := by positivity
          linarith

/-! ## The value of the inverse transform on the band -/

/-- The representative of an `L²` class that is *exactly* the band constant on the band. -/
def bandNormalize (a : ℝ) (d : ℂ) (g : ℝ → ℂ) : ℝ → ℂ :=
  fun t => if |t| ≤ a then d else g t

theorem bandNormalize_ae {a : ℝ} {f : SoninL2} {d : ℂ}
    (hd : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ centralInterval a → (f : ℝ → ℂ) t = d) :
    bandNormalize a d ((f : ℝ → ℂ)) =ᵐ[volume] (f : ℝ → ℂ) := by
  filter_upwards [hd] with t ht
  rw [bandNormalize]
  by_cases hmem : |t| ≤ a
  · have hmem' : t ∈ centralInterval a := by
      rw [centralInterval, Set.mem_Icc]
      exact ⟨by linarith [neg_abs_le t], by linarith [le_abs_self t]⟩
    rw [if_pos hmem, ht hmem']
  · rw [if_neg hmem]

theorem continuousAt_bandNormalize {a : ℝ} {d : ℂ} (g : ℝ → ℂ) {x : ℝ}
    (hx : x ∈ Ioo (-a) a) : ContinuousAt (bandNormalize a d g) x := by
  have hopen : IsOpen (Ioo (-a) a) := isOpen_Ioo
  have hev : bandNormalize a d g =ᶠ[𝓝 x] fun _ => d := by
    filter_upwards [hopen.mem_nhds hx] with t ht
    rw [bandNormalize, if_pos]
    rw [abs_le]
    exact ⟨le_of_lt ht.1, le_of_lt ht.2⟩
  exact (continuousAt_const).congr hev.symm

theorem mellin_bandNormalize {a : ℝ} {f : SoninL2} {d : ℂ}
    (hd : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ centralInterval a → (f : ℝ → ℂ) t = d) (w : ℂ) :
    mellin (bandNormalize a d ((f : ℝ → ℂ))) w = mellin ((f : ℝ → ℂ)) w := by
  rw [mellin, mellin]
  refine setIntegral_congr_ae measurableSet_Ioi ?_
  filter_upwards [bandNormalize_ae hd] with t ht
  intro _
  rw [ht]

/-- **The inverse Mellin transform of a vector of `L_a` is the band constant on the band.** -/
theorem mellinInv_eq_band_const {a : ℝ} (ha : 0 < a) {f : SoninL2} {c d : ℂ}
    (hev : f ∈ evenSubspace)
    (hc : ∀ᵐ u ∂(volume : Measure ℝ), u ∈ centralInterval a →
      ((fourierUnitary f : SoninL2) : ℝ → ℂ) u = c)
    (hd : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ centralInterval a → (f : ℝ → ℂ) t = d)
    (hrapid : HasStripRapidDecrease (extendedMellinContinuation a c d f))
    {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1 / 2)
    {x : ℝ} (hx0 : 0 < x) (hxa : x < a) :
    mellinInv σ (mellin ((f : ℝ → ℂ))) x = d := by
  have hmel : mellin (bandNormalize a d ((f : ℝ → ℂ))) = mellin ((f : ℝ → ℂ)) := by
    funext w
    exact mellin_bandNormalize hd w
  have hconv : MellinConvergent (bandNormalize a d ((f : ℝ → ℂ))) (σ : ℂ) := by
    have h := mellinConvergent_of_band ha hd (w := (σ : ℂ)) (by simpa using hσ0)
      (by simpa using hσ1)
    refine h.congr_fun_ae ?_
    filter_upwards [ae_restrict_of_ae (bandNormalize_ae hd)] with t ht
    rw [ht]
  have hvert : Complex.VerticalIntegrable (mellin (bandNormalize a d ((f : ℝ → ℂ)))) σ volume := by
    rw [hmel]
    exact verticalIntegrable_mellin ha hev hc hd hrapid hσ0 hσ1
  have hcontx : ContinuousAt (bandNormalize a d ((f : ℝ → ℂ))) x :=
    continuousAt_bandNormalize _ ⟨by linarith, hxa⟩
  have := mellinInv_mellin_eq σ (bandNormalize a d ((f : ℝ → ℂ))) hx0 hconv hvert hcontx
  rw [hmel] at this
  rw [this, bandNormalize, if_pos]
  rw [abs_le]
  constructor <;> linarith

/-! ## Continuity of the inverse transform, and the endpoint of the band -/

theorem continuousAt_mellinInv {a : ℝ} (ha : 0 < a) {f : SoninL2} {c d : ℂ}
    (hev : f ∈ evenSubspace)
    (hc : ∀ᵐ u ∂(volume : Measure ℝ), u ∈ centralInterval a →
      ((fourierUnitary f : SoninL2) : ℝ → ℂ) u = c)
    (hd : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ centralInterval a → (f : ℝ → ℂ) t = d)
    (hrapid : HasStripRapidDecrease (extendedMellinContinuation a c d f))
    {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1 / 2) {x₀ : ℝ} (hx₀ : 0 < x₀) :
    ContinuousAt (mellinInv σ (mellin ((f : ℝ → ℂ)))) x₀ := by
  have hvert := verticalIntegrable_mellin ha hev hc hd hrapid hσ0 hσ1
  have hvert' : Integrable (fun y : ℝ => mellin ((f : ℝ → ℂ)) ((σ : ℂ) + (y : ℂ) * I)) volume :=
    hvert
  have hcont := continuous_mellin_vertical ha hev hc hd hσ0 hσ1
  set C : ℝ := (x₀ / 2) ^ (-σ) with hCdef
  have hC0 : 0 < C := Real.rpow_pos_of_pos (by linarith) _
  have hmain : ContinuousAt (fun x : ℝ =>
      ∫ y : ℝ, (x : ℂ) ^ (-((σ : ℂ) + (y : ℂ) * I))
        • mellin ((f : ℝ → ℂ)) ((σ : ℂ) + (y : ℂ) * I)) x₀ := by
    have hnbhd : Ioo (x₀ / 2) (2 * x₀) ∈ 𝓝 x₀ := by
      refine isOpen_Ioo.mem_nhds ?_
      constructor <;> linarith
    refine continuousAt_of_dominated (bound := fun y : ℝ =>
      C * ‖mellin ((f : ℝ → ℂ)) ((σ : ℂ) + (y : ℂ) * I)‖) ?_ ?_ ?_ ?_
    · filter_upwards [hnbhd] with x hx
      have hx0 : (0:ℝ) < x := lt_trans (by linarith) hx.1
      simp only [smul_eq_mul]
      refine AEStronglyMeasurable.mul ?_ hcont.aestronglyMeasurable
      refine Continuous.aestronglyMeasurable ?_
      have : Continuous fun y : ℝ => Complex.exp ((-((σ : ℂ) + (y : ℂ) * I)) * (Real.log x : ℂ)) := by
        fun_prop
      refine this.congr fun y => ?_
      rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.2 (ne_of_gt hx0)),
        ← Complex.ofReal_log hx0.le]
      ring_nf
    · filter_upwards [hnbhd] with x hx
      filter_upwards with y
      have hx0 : (0:ℝ) < x := lt_trans (by linarith) hx.1
      have hker : ‖(x : ℂ) ^ (-((σ : ℂ) + (y : ℂ) * I))‖ = x ^ (-σ) := by
        rw [Complex.norm_cpow_eq_rpow_re_of_pos hx0]
        congr 1
        simp
      have hle : x ^ (-σ) ≤ C := by
        rw [hCdef]
        exact Real.rpow_le_rpow_of_nonpos (by linarith) (le_of_lt hx.1) (by linarith)
      rw [norm_smul, hker]
      exact mul_le_mul_of_nonneg_right hle (norm_nonneg _)
    · exact hvert'.norm.const_mul C
    · filter_upwards with y
      have hkercont : ContinuousAt (fun x : ℝ => (x : ℂ) ^ (-((σ : ℂ) + (y : ℂ) * I))) x₀ :=
        Complex.continuousAt_ofReal_cpow_const x₀ _ (Or.inr (ne_of_gt hx₀))
      have hmul : ContinuousAt (fun x : ℝ => (x : ℂ) ^ (-((σ : ℂ) + (y : ℂ) * I))
          * mellin ((f : ℝ → ℂ)) ((σ : ℂ) + (y : ℂ) * I)) x₀ :=
        hkercont.mul continuousAt_const
      simpa [smul_eq_mul] using hmul
  have hfun : mellinInv σ (mellin ((f : ℝ → ℂ)))
      = fun x : ℝ => ((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ y : ℝ, (x : ℂ) ^ (-((σ : ℂ) + (y : ℂ) * I))
        • mellin ((f : ℝ → ℂ)) ((σ : ℂ) + (y : ℂ) * I) := by
    funext x
    rw [mellinInv, Complex.real_smul]
  rw [hfun]
  exact continuousAt_const.mul hmain

/-- **The inverse transform still takes the band value at the endpoint of the band.** -/
theorem mellinInv_eq_band_const_endpoint {a : ℝ} (ha : 0 < a) {f : SoninL2} {c d : ℂ}
    (hev : f ∈ evenSubspace)
    (hc : ∀ᵐ u ∂(volume : Measure ℝ), u ∈ centralInterval a →
      ((fourierUnitary f : SoninL2) : ℝ → ℂ) u = c)
    (hd : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ centralInterval a → (f : ℝ → ℂ) t = d)
    (hrapid : HasStripRapidDecrease (extendedMellinContinuation a c d f))
    {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1 / 2) {x : ℝ} (hx0 : 0 < x) (hxa : x ≤ a) :
    mellinInv σ (mellin ((f : ℝ → ℂ))) x = d := by
  rcases lt_or_eq_of_le hxa with hlt | heq
  · exact mellinInv_eq_band_const ha hev hc hd hrapid hσ0 hσ1 hx0 hlt
  · -- the endpoint: approach from inside the band
    subst heq
    set u : ℕ → ℝ := fun n => x - x / ((n : ℝ) + 2) with hudef
    have hupos : ∀ n : ℕ, 0 < u n := by
      intro n
      rw [hudef]
      have hn : (0:ℝ) < (n : ℝ) + 2 := by positivity
      have : x / ((n : ℝ) + 2) < x := by
        rw [div_lt_iff₀ hn]
        nlinarith
      simp only
      linarith
    have hult : ∀ n : ℕ, u n < x := by
      intro n
      rw [hudef]
      have hn : (0:ℝ) < (n : ℝ) + 2 := by positivity
      have : 0 < x / ((n : ℝ) + 2) := by positivity
      simp only
      linarith
    have hutend : Tendsto u atTop (𝓝 x) := by
      have hdiv : Tendsto (fun n : ℕ => x / ((n : ℝ) + 2)) atTop (𝓝 0) := by
        have h1 : Tendsto (fun n : ℕ => ((n : ℝ) + 2)) atTop atTop :=
          tendsto_atTop_add_const_right _ 2 (tendsto_natCast_atTop_atTop (R := ℝ))
        exact Filter.Tendsto.div_atTop tendsto_const_nhds h1
      have := (tendsto_const_nhds (x := x) (f := (atTop : Filter ℕ))).sub hdiv
      simpa [hudef] using this
    have hval : ∀ n : ℕ, mellinInv σ (mellin ((f : ℝ → ℂ))) (u n) = d := fun n =>
      mellinInv_eq_band_const ha hev hc hd hrapid hσ0 hσ1 (hupos n) (hult n)
    have hcont := continuousAt_mellinInv ha hev hc hd hrapid hσ0 hσ1 hx0
    have hlim := hcont.tendsto.comp hutend
    have h2 : Tendsto (mellinInv σ (mellin ((f : ℝ → ℂ))) ∘ u) atTop (𝓝 d) := by
      refine tendsto_const_nhds.congr fun n => ?_
      exact (hval n).symm
    exact tendsto_nhds_unique hlim h2

end

end RHTower
