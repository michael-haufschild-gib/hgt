import GaloisForLFunctions.HTGeometry.EllipticThetaCoordinateDivisor
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
# Principal part of the constructed theta logarithmic kernel

The multiplicative theta boundary is split into its unique singular atom at the aligned
half-period and two normally convergent remainder series. Explicit geometric majorants prove the
remainder continuous at the nome. The exponential coordinate has nonzero derivative there, so the
additively normalized constructed kernel has residue one, exactly matching analytic Jacobi theta.
-/

open Complex Set Filter Topology

namespace GaloisForLFunctions

noncomputable section

def ellipticThetaForwardRemainder (q x : ℂ) : ℂ :=
  ∑' k : ℕ, ellipticGammaLogAtom (q ^ (k + 2) / x)

def ellipticThetaBackwardSeries (q x : ℂ) : ℂ :=
  ∑' k : ℕ, ellipticGammaLogAtom (q ^ k * x)

def ellipticThetaLogRemainder (q x : ℂ) : ℂ :=
  ellipticThetaForwardRemainder q x - ellipticThetaBackwardSeries q x

theorem norm_ellipticGammaLogAtom_le_of_norm_le {t : ℂ} {c : ℝ} (hc1 : c < 1)
    (ht : ‖t‖ ≤ c) : ‖ellipticGammaLogAtom t‖ ≤ ‖t‖ / (1 - c) := by
  have hden : 1 - c ≤ ‖1 - t‖ := by
    have h := norm_sub_norm_le (1 : ℂ) t
    rw [norm_one] at h
    linarith
  have hpos : 0 < 1 - c := sub_pos.mpr hc1
  rw [ellipticGammaLogAtom, norm_div]
  exact div_le_div_of_nonneg_left (norm_nonneg t) hpos hden

theorem ellipticThetaLogKernel_eq_atom_add_remainder {q x : ℂ} (hq : ‖q‖ < 1) :
    ellipticThetaLogKernel q x =
      ellipticGammaLogAtom (q / x) + ellipticThetaLogRemainder q x := by
  have hf := summable_ellipticThetaForwardLogAtom (q := q) (x := x) hq
  have hb := summable_ellipticThetaBackwardLogAtom (q := q) (x := x) hq
  have hfShift : Summable (fun k : ℕ => ellipticGammaLogAtom (q ^ (k + 1) / x)) := by
    simpa [Function.comp_def] using hf.comp_injective (i := fun k : ℕ => k + 1)
      (fun _ _ h => Nat.add_right_cancel h)
  rw [ellipticThetaLogKernel]
  simp_rw [ellipticThetaLogSummand]
  rw [hfShift.tsum_sub hb]
  rw [hfShift.tsum_eq_zero_add]
  simp only [zero_add, pow_one]
  rw [ellipticThetaLogRemainder, ellipticThetaForwardRemainder, ellipticThetaBackwardSeries]
  norm_num [Nat.add_assoc]
  ring

theorem analyticAt_ellipticThetaForwardRemainder_nome
    {q : ℂ} (hq0 : q ≠ 0) (hq : ‖q‖ < 1) :
    AnalyticAt ℂ (ellipticThetaForwardRemainder q) q := by
  let a : ℝ := ‖q‖
  let r : ℝ := a * (1 + a) / 2
  let R : ℝ := (1 + a) / 2
  let c : ℝ := 2 * a / (1 + a)
  let s : Set ℂ := {x | r ≤ ‖x‖ ∧ ‖x‖ ≤ R}
  let U : Set ℂ := {x | r < ‖x‖ ∧ ‖x‖ < R}
  let u : ℕ → ℝ := fun k => (a ^ (k + 2) / r) / (1 - c)
  have ha0 : 0 < a := by simpa [a] using (norm_pos_iff.mpr hq0)
  have ha1 : a < 1 := by simpa [a] using hq
  have hr0 : 0 < r := by dsimp [r]; positivity
  have hR1 : R < 1 := by dsimp [R]; linarith
  have hqa : q ∈ s := by
    dsimp [s, r, R, a]
    constructor <;> nlinarith
  have hsnhds : s ∈ 𝓝 q := by
    have hopen : IsOpen {x : ℂ | r < ‖x‖ ∧ ‖x‖ < R} :=
      (isOpen_lt continuous_const continuous_norm).inter
        (isOpen_lt continuous_norm continuous_const)
    have hmem : q ∈ {x : ℂ | r < ‖x‖ ∧ ‖x‖ < R} := by
      dsimp [r, R, a]
      constructor <;> nlinarith
    apply Filter.mem_of_superset (hopen.mem_nhds hmem)
    intro x hx
    exact ⟨hx.1.le, hx.2.le⟩
  have hc0 : 0 ≤ c := by dsimp [c]; positivity
  have hc1 : c < 1 := by
    dsimp [c]
    rw [div_lt_one (by linarith : 0 < 1 + a)]
    linarith
  have hu : Summable u := by
    have hgeom : Summable (fun k : ℕ => a ^ k) :=
      summable_geometric_of_lt_one ha0.le ha1
    have hscaled := hgeom.mul_left (a ^ 2 / r / (1 - c))
    apply hscaled.congr
    intro k
    dsimp [u]
    rw [pow_add]
    ring
  have hargBound (k : ℕ) (x : ℂ) (hx : x ∈ s) :
      ‖q ^ (k + 2) / x‖ ≤ c := by
    have harg : ‖q ^ (k + 2) / x‖ ≤ a ^ (k + 2) / r := by
      rw [norm_div, norm_pow]
      apply div_le_div_of_nonneg_left (pow_nonneg (norm_nonneg q) _) hr0 hx.1
    have hpow : a ^ (k + 2) ≤ a ^ 2 := by
      exact pow_le_pow_of_le_one ha0.le ha1.le (by omega)
    apply harg.trans
    rw [div_le_iff₀ hr0]
    calc
      a ^ (k + 2) ≤ a ^ 2 := hpow
      _ = c * r := by
        dsimp [c, r]
        field_simp [ne_of_gt (by linarith : 0 < 1 + a)]
  have htermNorm (k : ℕ) (x : ℂ) (hx : x ∈ s) :
      ‖ellipticGammaLogAtom (q ^ (k + 2) / x)‖ ≤ u k := by
    have harg : ‖q ^ (k + 2) / x‖ ≤ a ^ (k + 2) / r := by
      rw [norm_div, norm_pow]
      apply div_le_div_of_nonneg_left (pow_nonneg (norm_nonneg q) _) hr0 hx.1
    have hcarg := hargBound k x hx
    exact (norm_ellipticGammaLogAtom_le_of_norm_le hc1 hcarg).trans (by dsimp [u]; gcongr)
  have hU : IsOpen U := (isOpen_lt continuous_const continuous_norm).inter
    (isOpen_lt continuous_norm continuous_const)
  have hqU : q ∈ U := by
    dsimp [U, r, R, a]
    constructor <;> nlinarith
  have htermDiff (k : ℕ) :
      DifferentiableOn ℂ (fun x : ℂ => ellipticGammaLogAtom (q ^ (k + 2) / x)) U := by
    intro x hx
    have hxS : x ∈ s := ⟨hx.1.le, hx.2.le⟩
    have hx0 : x ≠ 0 := by
      exact norm_pos_iff.mp (hr0.trans hx.1)
    have harglt : ‖q ^ (k + 2) / x‖ < 1 :=
      (hargBound k x hxS).trans_lt hc1
    have harg1 : q ^ (k + 2) / x ≠ 1 := by
      intro heq
      rw [heq, norm_one] at harglt
      exact lt_irrefl 1 harglt
    change DifferentiableWithinAt ℂ
      (fun y : ℂ => (q ^ (k + 2) / y) / (1 - q ^ (k + 2) / y)) U x
    have hinner : DifferentiableAt ℂ (fun y : ℂ => q ^ (k + 2) / y) x :=
      (differentiableAt_const _).div differentiableAt_id hx0
    exact (hinner.div ((differentiableAt_const _).sub hinner)
      (sub_ne_zero.mpr harg1.symm)).differentiableWithinAt
  have hdiff := Complex.differentiableOn_tsum_of_summable_norm hu htermDiff hU
    (fun k x hx => htermNorm k x ⟨hx.1.le, hx.2.le⟩)
  exact (hdiff.analyticOnNhd hU) q hqU

theorem analyticAt_ellipticThetaBackwardSeries_nome {q : ℂ} (hq : ‖q‖ < 1) :
    AnalyticAt ℂ (ellipticThetaBackwardSeries q) q := by
  let a : ℝ := ‖q‖
  let R : ℝ := (1 + a) / 2
  let s : Set ℂ := {x | ‖x‖ ≤ R}
  let U : Set ℂ := {x | ‖x‖ < R}
  let u : ℕ → ℝ := fun k => (a ^ k * R) / (1 - R)
  have ha0 : 0 ≤ a := by dsimp [a]; positivity
  have ha1 : a < 1 := by simpa [a] using hq
  have hR0 : 0 ≤ R := by dsimp [R]; linarith
  have hR1 : R < 1 := by dsimp [R]; linarith
  have hsnhds : s ∈ 𝓝 q := by
    have hopen : IsOpen {x : ℂ | ‖x‖ < R} := isOpen_lt continuous_norm continuous_const
    have hmem : q ∈ {x : ℂ | ‖x‖ < R} := by dsimp [R, a]; linarith
    apply Filter.mem_of_superset (hopen.mem_nhds hmem)
    intro x hx
    change ‖x‖ < R at hx
    change ‖x‖ ≤ R
    exact hx.le
  have hu : Summable u := by
    have hgeom : Summable (fun k : ℕ => a ^ k) :=
      summable_geometric_of_lt_one ha0 ha1
    have hscaled := hgeom.mul_right (R / (1 - R))
    apply hscaled.congr
    intro k
    dsimp [u]
    ring
  have hargBound (k : ℕ) (x : ℂ) (hx : x ∈ s) : ‖q ^ k * x‖ ≤ R := by
    change ‖x‖ ≤ R at hx
    rw [norm_mul, norm_pow]
    calc
      a ^ k * ‖x‖ ≤ a ^ k * R := by gcongr
      _ ≤ 1 * R := by
        gcongr
        exact pow_le_one₀ ha0 ha1.le
      _ = R := one_mul R
  have htermNorm (k : ℕ) (x : ℂ) (hx : x ∈ s) :
      ‖ellipticGammaLogAtom (q ^ k * x)‖ ≤ u k := by
    have hxs : ‖x‖ ≤ R := by simpa [s] using hx
    apply (norm_ellipticGammaLogAtom_le_of_norm_le hR1 (hargBound k x hx)).trans
    dsimp [u, a]
    rw [norm_mul, norm_pow]
    gcongr
  have hU : IsOpen U := isOpen_lt continuous_norm continuous_const
  have hqU : q ∈ U := by dsimp [U, R, a]; linarith
  have htermDiff (k : ℕ) :
      DifferentiableOn ℂ (fun x : ℂ => ellipticGammaLogAtom (q ^ k * x)) U := by
    intro x hx
    have hxlt : ‖x‖ < R := by simpa [U] using hx
    have hxS : x ∈ s := by simpa [s] using hxlt.le
    have harglt : ‖q ^ k * x‖ < 1 := (hargBound k x hxS).trans_lt hR1
    have harg1 : q ^ k * x ≠ 1 := by
      intro heq
      rw [heq, norm_one] at harglt
      exact lt_irrefl 1 harglt
    change DifferentiableWithinAt ℂ (fun y : ℂ => (q ^ k * y) / (1 - q ^ k * y)) U x
    have hinner : DifferentiableAt ℂ (fun y : ℂ => q ^ k * y) x :=
      (differentiableAt_const _).mul differentiableAt_id
    exact (hinner.div ((differentiableAt_const _).sub hinner)
      (sub_ne_zero.mpr harg1.symm)).differentiableWithinAt
  have hdiff := Complex.differentiableOn_tsum_of_summable_norm hu htermDiff hU
    (fun k x hx => htermNorm k x (by
      have hxlt : ‖x‖ < R := by simpa [U] using hx
      simpa [s] using hxlt.le))
  exact (hdiff.analyticOnNhd hU) q hqU

theorem analyticAt_ellipticThetaLogRemainder_nome
    {q : ℂ} (hq0 : q ≠ 0) (hq : ‖q‖ < 1) :
    AnalyticAt ℂ (ellipticThetaLogRemainder q) q := by
  exact (analyticAt_ellipticThetaForwardRemainder_nome hq0 hq).sub
    (analyticAt_ellipticThetaBackwardSeries_nome hq)

theorem ellipticThetaCoordinate_halfPeriod (τ : ℂ) :
    ellipticThetaCoordinate τ (thetaHalfPeriod τ) = ellipticNome τ := by
  simpa using ellipticThetaCoordinate_eq_nome_zpow_of_lattice τ 0 0

theorem hasDerivAt_ellipticThetaCoordinate (τ z : ℂ) :
    HasDerivAt (ellipticThetaCoordinate τ) (2 * Real.pi * I * ellipticThetaCoordinate τ z) z := by
  have hlin : HasDerivAt (fun w : ℂ => 2 * Real.pi * I * w) (2 * Real.pi * I) z :=
    by simpa only [id_eq, mul_one] using (hasDerivAt_id z).const_mul (2 * Real.pi * I)
  have hexp := (Complex.hasDerivAt_exp (2 * Real.pi * I * z)).comp z hlin
  have hmul := hexp.const_mul (-Complex.exp (Real.pi * I * τ))
  convert! hmul using 1
  simp only [ellipticThetaCoordinate]
  ring_nf

theorem tendsto_ellipticThetaAdditiveLogKernel_normalized_halfPeriod {τ : ℂ} (hτ : 0 < τ.im) :
    Tendsto
      (fun z : ℂ => (z - thetaHalfPeriod τ) * ellipticThetaAdditiveLogKernel τ z)
      (𝓝[≠] thetaHalfPeriod τ) (𝓝 1) := by
  let q := ellipticNome τ
  let z₀ := thetaHalfPeriod τ
  let X := ellipticThetaCoordinate τ
  have hq0 : q ≠ 0 := ellipticNome_ne_zero τ
  have hq : ‖q‖ < 1 := norm_ellipticNome_lt_one hτ
  have hX0 : X z₀ = q := by simpa [X, z₀, q] using ellipticThetaCoordinate_halfPeriod τ
  have hderiv : HasDerivAt X (2 * Real.pi * I * q) z₀ := by
    simpa [X, hX0] using hasDerivAt_ellipticThetaCoordinate τ z₀
  have hderiv0 : (2 * Real.pi * I * q : ℂ) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (mod_cast Real.pi_ne_zero)) I_ne_zero) hq0
  have hslope := hderiv.tendsto_slope
  have hsing : Tendsto
      (fun z : ℂ => (z - z₀) * (2 * Real.pi * I) *
        ellipticGammaLogAtom (q / X z))
      (𝓝[≠] z₀) (𝓝 1) := by
    have hquot : Tendsto
        (fun z : ℂ => (2 * Real.pi * I * q) / slope X z₀ z)
        (𝓝[≠] z₀) (𝓝 1) := by
      have hconst : Tendsto (fun _ : ℂ => (2 * Real.pi * I * q : ℂ))
          (𝓝[≠] z₀) (𝓝 (2 * Real.pi * I * q : ℂ)) := tendsto_const_nhds
      simpa only [div_self hderiv0] using! hconst.div hslope hderiv0
    have hmap := hderiv.tendsto_nhdsNE hderiv0
    have hXne : ∀ᶠ z in 𝓝[≠] z₀, X z ≠ q :=
      by simpa only [hX0, Set.mem_singleton_iff] using
        hmap.eventually self_mem_nhdsWithin
    apply hquot.congr'
    filter_upwards [self_mem_nhdsWithin, hXne] with z hz hzX
    have hz0 : z - z₀ ≠ 0 := sub_ne_zero.mpr hz
    have hX0z : X z ≠ 0 := ellipticThetaCoordinate_ne_zero τ z
    have hXq : X z - q ≠ 0 := sub_ne_zero.mpr hzX
    rw [ellipticGammaLogAtom]
    rw [show 1 - q / X z = (X z - q) / X z by field_simp]
    simp [slope, hX0]
    field_simp [hX0z, hXq, hz0]
  have houter : ContinuousAt (ellipticThetaLogRemainder q) (X z₀) := by
    simpa only [hX0] using (analyticAt_ellipticThetaLogRemainder_nome hq0 hq).continuousAt
  have hremCont : ContinuousAt (fun z => ellipticThetaLogRemainder q (X z)) z₀ :=
    houter.comp hderiv.continuousAt
  have hzsub : Tendsto (fun z : ℂ => z - z₀) (𝓝[≠] z₀) (𝓝 0) := by
    have hzlim : Tendsto (fun z : ℂ => z) (𝓝[≠] z₀) (𝓝 z₀) :=
      tendsto_id.mono_left inf_le_left
    have hc0 : Tendsto (fun _ : ℂ => z₀) (𝓝[≠] z₀) (𝓝 z₀) := tendsto_const_nhds
    simpa using hzlim.sub hc0
  have hrem : Tendsto
      (fun z : ℂ => (z - z₀) * (2 * Real.pi * I) * ellipticThetaLogRemainder q (X z))
      (𝓝[≠] z₀) (𝓝 0) := by
    have hc : Tendsto (fun _ : ℂ => (2 * Real.pi * I : ℂ))
        (𝓝[≠] z₀) (𝓝 (2 * Real.pi * I : ℂ)) := tendsto_const_nhds
    simpa only [zero_mul] using
      (hzsub.mul hc).mul (hremCont.tendsto.mono_left inf_le_left)
  have htotal := hsing.add hrem
  simpa only [add_zero] using htotal.congr' (by
    filter_upwards with z
    dsimp [ellipticThetaAdditiveLogKernel, X, q, z₀]
    rw [ellipticThetaLogKernel_eq_atom_add_remainder hq]
    ring)

end

end GaloisForLFunctions
