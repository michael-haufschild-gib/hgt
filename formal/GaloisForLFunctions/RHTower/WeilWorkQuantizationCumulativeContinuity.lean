import GaloisForLFunctions.RHTower.WeilWorkQuantizationPeriodicSymbol
import Mathlib.Topology.Order.LeftRightLim
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
open Complex Set Filter MeasureTheory Metric Function
open scoped Topology ENNReal
/-!
# Continuity of the actual residual cumulative lift

A locally finite residual measure has atoms below one. Every point therefore
has a surrounding interval of mass below one. Continuity of the exponential
phase forces the monotone cumulative function's two one-sided limits to agree.
This retains singular-continuous mass and derives continuity from the actual
source and its represented phase, without an atomlessness premise.
-/

noncomputable section
namespace RHTower.WeilSpectral

theorem quantization_exp_phase_eq {u v : ℝ}
    (h : cexp (((2 * Real.pi * u : ℝ) : ℂ) * I) =
      cexp (((2 * Real.pi * v : ℝ) : ℂ) * I)) : ∃ n : ℤ, u = v + n := by
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp h
  have hi := congrArg Complex.im hn
  simp at hi
  refine ⟨n, ?_⟩
  nlinarith [Real.pi_pos]

theorem quantization_continuousAt_of_phase {C : ℝ → ℝ} (hC : Monotone C)
    {a x b : ℝ} (ha : a < x) (hb : x < b) (hsmall : C b - C a < 1)
    (hphase : ContinuousAt (fun y => cexp (((2 * Real.pi * C y : ℝ) : ℂ) * I)) x) :
    ContinuousAt C x := by
  let e : ℝ → ℂ := fun u => cexp (((2 * Real.pi * u : ℝ) : ℂ) * I)
  have he : Continuous e := by fun_prop
  have hl : e (leftLim C x) = e (C x) :=
    tendsto_nhds_unique (he.continuousAt.tendsto.comp (hC.tendsto_leftLim x))
      (hphase.tendsto.mono_left nhdsWithin_le_nhds)
  have hr : e (rightLim C x) = e (C x) :=
    tendsto_nhds_unique (he.continuousAt.tendsto.comp (hC.tendsto_rightLim x))
      (hphase.tendsto.mono_left nhdsWithin_le_nhds)
  obtain ⟨n, hn⟩ := quantization_exp_phase_eq (hr.trans hl.symm)
  have hn0 : (0 : ℝ) ≤ n := by linarith [hC.leftLim_le_rightLim (le_refl x)]
  have hn1 : (n : ℝ) < 1 := by linarith [hC.le_leftLim ha, hC.rightLim_le hb]
  have hnz : n = 0 := by
    have : (0 : ℤ) ≤ n := by exact_mod_cast hn0
    have : n < (1 : ℤ) := by exact_mod_cast hn1
    omega
  apply hC.continuousAt_iff_leftLim_eq_rightLim.mpr
  simpa only [hnz, Int.cast_zero, add_zero] using hn.symm

theorem quantization_cumulative_local_subunit {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {x : ℝ} (hx : 0 < x) :
    ∃ a b : ℝ, 0 < a ∧ a < x ∧ x < b ∧
      quantizationResidualCumulative hW b - quantizationResidualCumulative hW a < 1 := by
  let ν := quantizationResidualMeasure hW
  have hfin (a b : ℝ) : ν (Icc a b) ≠ ∞ :=
    ne_top_of_le_ne_top (quantization_boundaryMeasure_Icc_ne_top hW a b)
      (quantizationResidualMeasure_le hW _)
  letI : IsLocallyFiniteMeasure ν := ⟨fun y =>
    ⟨Icc (y - 1) (y + 1), Icc_mem_nhds (by linarith) (by linarith), (hfin _ _).lt_top⟩⟩
  have ht : Tendsto (fun δ : ℝ => ν.real (Icc (2*x-δ) (2*x+δ)))
      (𝓝[>] (0 : ℝ)) (𝓝 (ν.real {2*x})) :=
    (ENNReal.tendsto_toReal (isCompact_singleton.measure_ne_top (μ := ν))).comp
      (tendsto_measure_Icc_nhdsWithin_right' ν (2*x))
  have hsmall := ht.eventually (gt_mem_nhds (quantizationResidualMeasure_atom_lt_one hW (2*x)))
  obtain ⟨δ, hδmass, hδ0, hδx⟩ := (hsmall.and (Ioo_mem_nhdsGT (show (0 : ℝ) < 2*x by positivity))).exists
  let a := x - δ/2
  let b := x + δ/2
  have ha0 : 0 < a := by dsimp [a]; linarith
  have hax : a < x := by dsimp [a]; linarith
  have hxb : x < b := by dsimp [b]; linarith
  have hab : 2*a ≤ 2*b := by linarith
  have hadd : ν.real (Ioc 0 (2*b)) = ν.real (Ioc 0 (2*a)) + ν.real (Ioc (2*a) (2*b)) := by
    rw [← Ioc_union_Ioc_eq_Ioc (show 0 ≤ 2*a by positivity) hab]
    exact measureReal_union (Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc
      (quantizationResidualMeasure_Ioc_ne_top hW _ _) (quantizationResidualMeasure_Ioc_ne_top hW _ _)
  refine ⟨a, b, ha0, hax, hxb, ?_⟩
  change ν.real (Ioc 0 (2*b)) - ν.real (Ioc 0 (2*a)) < 1
  rw [hadd, add_sub_cancel_left]
  apply lt_of_le_of_lt (measureReal_mono (s₂ := Icc (2*x-δ) (2*x+δ)) ?_ (hfin _ _)) hδmass
  intro y hy
  dsimp [a, b] at hy
  exact ⟨by linarith [hy.1], by linarith [hy.2]⟩


/-- The represented actual phase lifts continuously because residual atoms are subunit. -/
theorem continuousOn_quantizationResidualCumulative_of_periodic
    {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) {q : ℕ} (hq : 2 ≤ q) {p : ℤ → ℂ}
    (hp : Summable fun k => ‖p k‖ * (q : ℝ) ^ k.natAbs)
    (hphase : ∀ x : ℝ, 0 < x →
      cexp (((2 * Real.pi * quantizationResidualCumulative hW x : ℝ) : ℂ) * I) =
        ∑' k : ℤ, p k * cexp (((2 * (k : ℝ) * Real.log q * x : ℝ) : ℂ) * I)) :
    ContinuousOn (quantizationResidualCumulative hW) (Ioi 0) := by
  obtain ⟨a, b, _, ha, hb, hP, _⟩ :=
    exists_nonzero_annulus_quantizationPeriodicSymbol hW hq hp hphase
  let z : ℝ → ℂ := fun x => cexp (((2 * Real.log q * x : ℝ) : ℂ) * I)
  have hz : ∀ x, z x ∈ GaloisForLFunctions.HTGeometry.annulusAt 0 a b := by
    intro x
    have hn : ‖z x‖ = 1 := Complex.norm_exp_ofReal_mul_I _
    simpa only [GaloisForLFunctions.HTGeometry.annulusAt, mem_setOf_eq, sub_zero, hn] using And.intro ha hb
  have hzc : Continuous z := by fun_prop
  have hpc := hP.continuousOn.comp_continuous hzc hz
  have hphc : ContinuousOn
      (fun x => cexp (((2 * Real.pi * quantizationResidualCumulative hW x : ℝ) : ℂ) * I))
      (Ioi 0) := hpc.continuousOn.congr (fun x hx =>
        (quantizationPeriodicSymbol_phase hW hphase hx).symm)
  intro x hx
  obtain ⟨u, v, _, hu, hv, hsmall⟩ := quantization_cumulative_local_subunit hW hx
  exact (quantization_continuousAt_of_phase (monotone_quantizationResidualCumulative hW)
    hu hv hsmall (hphc.continuousAt (Ioi_mem_nhds hx))).continuousWithinAt

/-- A continuous exponential lift differs from another by one fixed deck translation. -/
theorem quantization_continuous_lift_diff {s : Set ℝ} (hs : IsPreconnected s)
    {f g : ℝ → ℂ} (hf : ContinuousOn f s) (hg : ContinuousOn g s)
    (he : ∀ x ∈ s, cexp (f x) = cexp (g x)) {x y : ℝ} (hx : x ∈ s) (hy : y ∈ s) :
    f x - g x = f y - g y := by
  have hpi : (2 * (Real.pi : ℂ) * I) ≠ 0 := by simp [Real.pi_ne_zero]
  have hm : MapsTo (fun t => (f t - g t) / (2 * (Real.pi : ℂ) * I)) s
      (range (Int.cast : ℤ → ℂ)) := by
    intro t ht
    have hexp : cexp (f t - g t) = 1 := by
      rw [Complex.exp_sub, he t ht, div_self (Complex.exp_ne_zero _)]
    obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp hexp
    refine ⟨n, ?_⟩
    change (n : ℂ) = (f t - g t) / (2 * (Real.pi : ℂ) * I)
    rw [hn, mul_div_cancel_right₀ _ hpi]
  have h := hs.constant_of_mapsTo
    Complex.isClosedEmbedding_intCast.isEmbedding.isInducing.isDiscrete_range
    ((hf.sub hg).div_const _) hm hx hy
  have hh := congrArg (fun z : ℂ => z * (2 * (Real.pi : ℂ) * I)) h
  simpa only [div_mul_cancel₀ _ hpi, Pi.sub_apply] using hh

end RHTower.WeilSpectral
