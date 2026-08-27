import GaloisForLFunctions.RHTower.SoninAllPrimeMomentWeldApertureFloor
import GaloisForLFunctions.HTGeometry.HilbertSchmidtNearIsometryCount
import GaloisForLFunctions.RHTower.SoninPhysicalTailVanishing
import GaloisForLFunctions.RHTower.SoninSmallCutoffGroundRow
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated

/-!
# Large-aperture properness and compact-window confinement for the all-prime Sonin weld

At large aperture the exact Sonin projection tends strongly to zero, while its formal
physical--Fourier complement tends strongly to minus the identity. Consequently every fixed
principal-subtracted prime-power residual tends strongly to twice its symmetric dilation signal.
That limit is non-Hilbert--Schmidt: an infinite orthonormal shell family retains uniformly positive
image norm. Finite-family Hilbert--Schmidt domination therefore forces each weighted residual
block's Hilbert--Schmidt energy to diverge along every cofinal aperture sequence.

One fixed prime-square block already forces the zeroth all-prime trace moment to diverge. Combined
with exact-weld convergence and the previously proved positive lower aperture floor, this traps
every hypothetical F2 weld section eventually in a compact positive interval and produces a
positive finite cluster aperture. No Xi zero, RH premise, numerical computation, or extra axiom is
used.
-/

open Filter Topology
open scoped BigOperators

namespace RHTower

noncomputable section

set_option maxHeartbeats 1000000

private theorem tendsto_indicatorCutoff_apply_atTop
    (g : SoninL2) (R : ℕ → ℝ) (hR : Tendsto R atTop atTop) :
    Tendsto (fun n => indicatorCutoff (centralInterval (R n))
      (measurableSet_centralInterval (R n)) g) atTop (𝓝 g) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [norm_sub_rev] using tendsto_norm_sub_indicatorCutoff_atTop g R hR

private theorem tendsto_fourierCutoff_apply_atTop
    (g : SoninL2) (R : ℕ → ℝ) (hR : Tendsto R atTop atTop) :
    Tendsto (fun n => fourierCutoff (centralInterval (R n))
      (measurableSet_centralInterval (R n)) g) atTop (𝓝 g) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have htail := tendsto_norm_sub_indicatorCutoff_atTop (fourierUnitary g) R hR
  refine htail.congr fun n => ?_
  rw [fourierCutoff_apply]
  calc
    ‖fourierUnitary g -
        indicatorCutoff (centralInterval (R n))
          (measurableSet_centralInterval (R n)) (fourierUnitary g)‖ =
      ‖indicatorCutoff (centralInterval (R n))
          (measurableSet_centralInterval (R n)) (fourierUnitary g) -
        fourierUnitary g‖ := norm_sub_rev _ _
    _ = ‖fourierUnitary (fourierUnitary.symm
          (indicatorCutoff (centralInterval (R n))
            (measurableSet_centralInterval (R n)) (fourierUnitary g)) - g)‖ := by
      rw [map_sub, LinearIsometryEquiv.apply_symm_apply]
    _ = ‖fourierUnitary.symm
        (indicatorCutoff (centralInterval (R n))
          (measurableSet_centralInterval (R n)) (fourierUnitary g)) - g‖ := by
      exact fourierUnitary.norm_map _

private theorem tendsto_centralSoninFormalComplement_apply_atTop
    (g : SoninL2) (R : ℕ → ℝ) (hR : Tendsto R atTop atTop) :
    Tendsto (fun n => centralSoninFormalComplement (R n) g) atTop (𝓝 (-g)) := by
  have hP := tendsto_indicatorCutoff_apply_atTop g R hR
  have hF := tendsto_fourierCutoff_apply_atTop g R hR
  have hconst : Tendsto (fun _ : ℕ => g) atTop (𝓝 g) := tendsto_const_nhds
  simpa [centralSoninFormalComplement] using (hconst.sub hP).sub hF

private theorem tendsto_centralSoninProjection_apply_atTop
    (g : SoninL2) (R : ℕ → ℝ) (hR : Tendsto R atTop atTop) :
    Tendsto (fun n => centralSoninProjection (R n) g) atTop (𝓝 0) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa using tendsto_norm_centralSoninProjection_atTop g R hR

private theorem tendsto_formalComplement_apply_varying_atTop
    (x : ℕ → SoninL2) (y : SoninL2)
    (hx : Tendsto x atTop (𝓝 y))
    (R : ℕ → ℝ) (hR : Tendsto R atTop atTop) :
    Tendsto (fun n => centralSoninFormalComplement (R n) (x n)) atTop (𝓝 (-y)) := by
  let Q : ℕ → SoninL2 →L[ℂ] SoninL2 := fun n => centralSoninFormalComplement (R n)
  have hdiffNorm : Tendsto (fun n => ‖Q n (x n - y)‖) atTop (𝓝 0) := by
    have hxy : Tendsto (fun n => ‖x n - y‖) atTop (𝓝 0) :=
      tendsto_iff_norm_sub_tendsto_zero.mp hx
    apply squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hxy
    calc
      ‖Q n (x n - y)‖ ≤ ‖Q n‖ * ‖x n - y‖ := (Q n).le_opNorm _
      _ ≤ 1 * ‖x n - y‖ := mul_le_mul_of_nonneg_right
        (norm_centralSoninFormalComplement_le_one (R n)) (norm_nonneg _)
      _ = ‖x n - y‖ := one_mul _
  have hdiff : Tendsto (fun n => Q n (x n - y)) atTop (𝓝 0) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    simpa using hdiffNorm
  have hfixed := tendsto_centralSoninFormalComplement_apply_atTop y R hR
  have hadd := hdiff.add hfixed
  simpa only [Q, map_sub, sub_add_cancel, zero_add] using hadd

private theorem tendsto_centralSoninDilationCornerResidual_apply_atTop
    (p : ℝ) (hp : 1 < p) (g : SoninL2)
    (R : ℕ → ℝ) (hR : Tendsto R atTop atTop) :
    Tendsto (fun n => centralSoninDilationCornerResidual (R n) p hp g)
      atTop (𝓝 (2 • dilationSum p hp g)) := by
  let D : SoninL2 →L[ℂ] SoninL2 := dilationSum p hp
  let Q : ℕ → SoninL2 →L[ℂ] SoninL2 := fun n => centralSoninProjection (R n)
  let Q₀ : ℕ → SoninL2 →L[ℂ] SoninL2 := fun n => centralSoninFormalComplement (R n)
  have hQg : Tendsto (fun n => Q n g) atTop (𝓝 0) :=
    tendsto_centralSoninProjection_apply_atTop g R hR
  have hDQg : Tendsto (fun n => D (Q n g)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, map_zero] using
      D.continuous.continuousAt.tendsto.comp hQg
  have hQDQgNorm : Tendsto (fun n => ‖Q n (D (Q n g))‖) atTop (𝓝 0) := by
    have hnorm : Tendsto (fun n => ‖D (Q n g)‖) atTop (𝓝 0) := by
      simpa using hDQg.norm
    apply squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hnorm
    calc
      ‖Q n (D (Q n g))‖ ≤ ‖Q n‖ * ‖D (Q n g)‖ := (Q n).le_opNorm _
      _ ≤ 1 * ‖D (Q n g)‖ := mul_le_mul_of_nonneg_right
        (Submodule.starProjection_norm_le (centralSoninCarrier (R n))) (norm_nonneg _)
      _ = ‖D (Q n g)‖ := one_mul _
  have hQDQg : Tendsto (fun n => Q n (D (Q n g))) atTop (𝓝 0) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    simpa using hQDQgNorm
  have hQ₀g : Tendsto (fun n => Q₀ n g) atTop (𝓝 (-g)) :=
    tendsto_centralSoninFormalComplement_apply_atTop g R hR
  have hDQ₀g : Tendsto (fun n => D (Q₀ n g)) atTop (𝓝 (-(D g))) := by
    simpa only [Function.comp_def, map_neg] using
      D.continuous.continuousAt.tendsto.comp hQ₀g
  have hQ₀DQ₀g : Tendsto (fun n => Q₀ n (D (Q₀ n g))) atTop (𝓝 (D g)) := by
    simpa only [neg_neg] using
      tendsto_formalComplement_apply_varying_atTop
        (fun n => D (Q₀ n g)) (-(D g)) hDQ₀g R hR
  have hsum := (hDQg.sub hQDQg).sub (hDQ₀g.sub hQ₀DQ₀g)
  change Tendsto (fun n =>
      (D (Q n g) - Q n (D (Q n g))) -
        (D (Q₀ n g) - Q₀ n (D (Q₀ n g))))
    atTop (𝓝 (2 • D g))
  have htarget : (0 : SoninL2) - 0 - (-(D g) - D g) = 2 • D g := by
    simp only [two_smul]
    module
  rw [← htarget]
  exact hsum

private theorem tendsto_centralSoninWeightedPrimePowerResidual_apply_atTop
    (pk : Nat.Primes × ℕ) (g : SoninL2)
    (R : ℕ → ℝ) (hR : Tendsto R atTop atTop) :
    Tendsto (fun n => centralSoninWeightedPrimePowerResidual (R n) pk g)
      atTop (𝓝 (soninLogPrimePowerCoefficient pk •
        (2 • dilationSum (soninPrimePowerScale pk)
          (one_lt_soninPrimePowerScale pk) g))) := by
  have h := tendsto_centralSoninDilationCornerResidual_apply_atTop
    (soninPrimePowerScale pk) (one_lt_soninPrimePowerScale pk) g R hR
  simpa only [centralSoninWeightedPrimePowerResidual, centralSoninPrimePowerResidual,
    _root_.smul_apply] using
    h.const_smul (soninLogPrimePowerCoefficient pk)

private theorem norm_indicatorCutoff_apply_le
    (s : Set ℝ) (hs : MeasurableSet s) (g : SoninL2) :
    ‖indicatorCutoff s hs g‖ ≤ ‖g‖ := by
  calc
    ‖indicatorCutoff s hs g‖ ≤ ‖indicatorCutoff s hs‖ * ‖g‖ :=
      (indicatorCutoff s hs).le_opNorm g
    _ ≤ 1 * ‖g‖ := by
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg g)
      rw [indicatorCutoff_eq_physicalForbidden_starProjection]
      exact Submodule.starProjection_norm_le _
    _ = ‖g‖ := one_mul _

theorem tendsto_hsNormSq_centralSoninWeightedPrimePowerResidual_atTop
    (pk : Nat.Primes × ℕ) (R : ℕ → ℝ) (hR : Tendsto R atTop atTop) :
    Tendsto (fun n => ContinuousLinearMap.hsNormSq
      (centralSoninWeightedPrimePowerResidual (R n) pk)) atTop atTop := by
  let p : ℝ := soninPrimePowerScale pk
  have hp : 1 < p := one_lt_soninPrimePowerScale pk
  let e : ℕ → SoninL2 := evenShellVector 1 p hp
  have he : Orthonormal ℂ e := by
    simpa only [e] using evenShellVector_orthonormal 1 p (by norm_num) hp
  let c : ℝ := ‖soninLogPrimePowerCoefficient pk‖
  have hc : 0 < c := by
    exact norm_pos_iff.mpr (soninLogPrimePowerCoefficient_ne_zero pk)
  apply Filter.tendsto_atTop.mpr
  intro b
  obtain ⟨N : ℕ, hN⟩ := exists_nat_gt (b / c ^ 2)
  have hNc : b < (N : ℝ) * c ^ 2 := by
    rw [div_lt_iff₀ (sq_pos_of_pos hc)] at hN
    simpa [mul_comm] using hN
  have hmode : ∀ i : ℕ, ∀ᶠ n in atTop,
      c ≤ ‖centralSoninWeightedPrimePowerResidual (R n) pk (e i)‖ := by
    intro i
    have hlim := tendsto_centralSoninWeightedPrimePowerResidual_apply_atTop pk (e i) R hR
    have hD : 1 ≤ ‖dilationSum p hp (e i)‖ := by
      have hcontract := norm_indicatorCutoff_apply_le (Set.Icc (-1) 1) measurableSet_Icc
        (dilationSum p hp (e i))
      have hphysical := norm_physicalCutoff_dilationSum_evenShellVector
        1 p (by norm_num) hp i
      have hphysical' : ‖indicatorCutoff (Set.Icc (-1) 1) measurableSet_Icc
          (dilationSum p hp (e i))‖ = 1 := by
        simpa only [e, mul_one] using hphysical
      rw [hphysical'] at hcontract
      exact hcontract
    have htarget : c < ‖soninLogPrimePowerCoefficient pk •
        (2 • dilationSum p hp (e i))‖ := by
      have htwo : ‖2 • dilationSum p hp (e i)‖ =
          2 * ‖dilationSum p hp (e i)‖ := by
        rw [RCLike.norm_nsmul (K := ℂ), nsmul_eq_mul]
        norm_num
      rw [norm_smul]
      change c < c * ‖2 • dilationSum p hp (e i)‖
      rw [htwo]
      nlinarith
    exact hlim.norm.eventually (Ioi_mem_nhds htarget) |>.mono fun n hn => hn.le
  have hall : ∀ᶠ n in atTop, ∀ i ∈ Finset.range N,
      c ≤ ‖centralSoninWeightedPrimePowerResidual (R n) pk (e i)‖ :=
    (eventually_all_finset (Finset.range N)).2 fun i _ => hmode i
  have hpos : ∀ᶠ n in atTop, 0 < R n := hR.eventually_gt_atTop 0
  filter_upwards [hall, hpos] with n hn hnpos
  have hHS := centralSoninWeightedPrimePowerResidual_isHilbertSchmidt (R n) hnpos pk
  have henergy := card_mul_sq_le_hsNormSq_of_le_norm_apply hHS he (Finset.range N)
    c hc.le hn
  rw [Finset.card_range] at henergy
  exact hNc.le.trans henergy

theorem hsNormSq_centralSoninWeightedPrimePowerResidual_le_re_energyMoment_zero
    (a : ℝ) (ha : 0 < a) (pk : Nat.Primes × ℕ) :
    ContinuousLinearMap.hsNormSq (centralSoninWeightedPrimePowerResidual a pk) ≤
      (soninAllPrimeEnergyMoment a 0).re := by
  rw [soninAllPrimeEnergyMoment, HilbertSchmidt.hsPow,
    trace_soninAllPrimeResidualEnergyKernel a ha, Complex.ofReal_re,
    ← hsNormSqRect_soninAllPrimeColumnKernel_eq_residualKernel a ha,
    hsNormSqRect_soninAllPrimeColumnKernel_eq_tsum_block a ha]
  simpa using (summable_centralSoninWeightedPrimePowerResidual_hsNormSq a ha).sum_le_tsum
    ({pk} : Finset (Nat.Primes × ℕ)) (fun _ _ => ContinuousLinearMap.hsNormSq_nonneg _)

theorem tendsto_re_soninAllPrimeEnergyMoment_zero_comp_atTop
    (R : ℕ → ℝ) (hR : Tendsto R atTop atTop) :
    Tendsto (fun n => (soninAllPrimeEnergyMoment (R n) 0).re) atTop atTop := by
  let pk : Nat.Primes × ℕ := (⟨2, Nat.prime_two⟩, 0)
  have hlocal := tendsto_hsNormSq_centralSoninWeightedPrimePowerResidual_atTop pk R hR
  apply Filter.tendsto_atTop.mpr
  intro b
  have hpos : ∀ᶠ n in atTop, 0 < R n := hR.eventually_gt_atTop 0
  filter_upwards [hlocal.eventually_ge_atTop b, hpos] with n hn hnpos
  exact hn.trans (hsNormSq_centralSoninWeightedPrimePowerResidual_le_re_energyMoment_zero
    (R n) hnpos pk)

/-- The zeroth block-diagonal all-prime Sonin trace is a proper function of aperture at the
large-aperture end: it diverges along every real aperture tending to positive infinity. -/
theorem tendsto_re_soninAllPrimeEnergyMoment_zero_atTop :
    Tendsto (fun a : ℝ => (soninAllPrimeEnergyMoment a 0).re) atTop atTop := by
  rw [tendsto_iff_seq_tendsto]
  intro R hR
  simpa only [Function.comp_def] using
    tendsto_re_soninAllPrimeEnergyMoment_zero_comp_atTop R hR

/-- A Sonin moment weld cannot escape through arbitrarily large apertures: convergence of its
zeroth coordinate, together with large-aperture properness, forces a finite eventual ceiling. -/
theorem soninPrimeArchSingleMomentCoupling_eventually_aperture_boundedAbove
    {aperture : ℕ → ℝ} (h : SoninPrimeArchSingleMomentCoupling aperture) :
    ∃ A : ℝ, 0 < A ∧ ∀ᶠ j in atTop, aperture j < A := by
  let M : ℝ := normalizedPrimeArchMoment 0
  let B : ℝ := M + 1
  have hreal : Tendsto
      (fun j => (soninAllPrimeEnergyMoment (aperture j) 0).re) atTop (𝓝 M) := by
    have hre := (Complex.continuous_re.tendsto ((M : ℝ) : ℂ)).comp (h.2 0)
    simpa only [M, Function.comp_def, Complex.ofReal_re] using hre
  have hsmall : ∀ᶠ j in atTop,
      (soninAllPrimeEnergyMoment (aperture j) 0).re < B :=
    hreal.eventually (Iio_mem_nhds (by dsimp only [B]; linarith))
  have hlarge : ∀ᶠ a : ℝ in atTop,
      B ≤ (soninAllPrimeEnergyMoment a 0).re :=
    tendsto_re_soninAllPrimeEnergyMoment_zero_atTop.eventually_ge_atTop B
  obtain ⟨A₀, hA₀⟩ := eventually_atTop.1 hlarge
  let A : ℝ := max A₀ 1
  have hA : 0 < A := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  refine ⟨A, hA, hsmall.mono fun j hj => ?_⟩
  by_contra hnot
  have hAj : A ≤ aperture j := le_of_not_gt hnot
  have hA₀j : A₀ ≤ aperture j := (le_max_left A₀ 1).trans hAj
  exact (not_lt_of_ge (hA₀ (aperture j) hA₀j)) hj

/-- Every exact F2 weld section is eventually trapped in one compact positive aperture window. -/
theorem soninPrimeArchSingleMomentCoupling_eventually_aperture_mem_compactWindow
    {aperture : ℕ → ℝ} (h : SoninPrimeArchSingleMomentCoupling aperture) :
    ∃ δ A : ℝ, 0 < δ ∧ δ < A ∧
      ∀ᶠ j in atTop, aperture j ∈ Set.Icc δ A := by
  obtain ⟨δ, hδ, hlower⟩ :=
    soninPrimeArchSingleMomentCoupling_eventually_aperture_boundedBelow h
  obtain ⟨A₀, hA₀, hupper⟩ :=
    soninPrimeArchSingleMomentCoupling_eventually_aperture_boundedAbove h
  let A : ℝ := max A₀ (δ + 1)
  have hδA : δ < A := lt_of_lt_of_le (by linarith) (le_max_right _ _)
  refine ⟨δ, A, hδ, hδA, ?_⟩
  filter_upwards [hlower, hupper] with j hjlower hjupper
  exact ⟨hjlower.le, hjupper.le.trans (le_max_left _ _)⟩

/-- Compact-window confinement produces a positive finite cluster aperture along a genuine
subsequence of the witnessing F2 section. -/
theorem soninPrimeArchSingleMomentCoupling_exists_positive_aperture_cluster
    {aperture : ℕ → ℝ} (h : SoninPrimeArchSingleMomentCoupling aperture) :
    ∃ aStar : ℝ, 0 < aStar ∧ ∃ φ : ℕ → ℕ,
      StrictMono φ ∧ Tendsto (aperture ∘ φ) atTop (𝓝 aStar) := by
  obtain ⟨δ, A, hδ, _hδA, hwindow⟩ :=
    soninPrimeArchSingleMomentCoupling_eventually_aperture_mem_compactWindow h
  obtain ⟨N, hN⟩ := eventually_atTop.1 hwindow
  let x : ℕ → ℝ := fun n => aperture (n + N)
  have hx : ∀ n, x n ∈ Set.Icc δ A := by
    intro n
    exact hN (n + N) (Nat.le_add_left N n)
  obtain ⟨aStar, haStar, φ, hφ, hlim⟩ := isCompact_Icc.tendsto_subseq hx
  let ψ : ℕ → ℕ := fun n => φ n + N
  have hψ : StrictMono ψ := hφ.add_const N
  have hlimψ : Tendsto (aperture ∘ ψ) atTop (𝓝 aStar) := by
    simpa only [x, ψ, Function.comp_def] using hlim
  exact ⟨aStar, hδ.trans_le haStar.1, ψ, hψ, hlimψ⟩

/-- Every exact trace-moment weld has a witnessing aperture sequence trapped eventually between
positive finite endpoints. -/
theorem soninAllPrimeExactTraceMomentWeld_has_aperture_compactWindow
    (h : SoninAllPrimeExactTraceMomentWeld) :
    ∃ aperture : ℕ → ℝ, SoninPrimeArchSingleMomentCoupling aperture ∧
      ∃ δ A : ℝ, 0 < δ ∧ δ < A ∧
        ∀ᶠ j in atTop, aperture j ∈ Set.Icc δ A := by
  rw [soninAllPrimeExactTraceMomentWeld_iff_singleMomentCoupling] at h
  obtain ⟨aperture, haperture⟩ := h
  exact ⟨aperture, haperture,
    soninPrimeArchSingleMomentCoupling_eventually_aperture_mem_compactWindow haperture⟩


end

end RHTower


