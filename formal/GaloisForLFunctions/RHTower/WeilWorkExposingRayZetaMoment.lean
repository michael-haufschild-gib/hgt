import GaloisForLFunctions.RHTower.WeilWorkExposingRayGridDefect
import GaloisForLFunctions.RHTower.WeilPositivityConstantShiftRigidity
import GaloisForLFunctions.RHTower.WeilPositivityRegularPerturbationRigidity
import GaloisForLFunctions.RHTower.WeilPolarConeExposedDuality
import Mathlib.MeasureTheory.Integral.Prod

/-!
# The zeta moment forced by an actual polar source

For every compact complex C² polar test, the integral of its Fourier density
against `Re ζ(1/2+iτ)` equals Fourier mass plus the `π / sqrt(n)` weighted
integer autocorrelation trace. The proof retains the whole continuous pole
integral, proves compact-lag Fubini and weighted convergence, and then uses
the exact polar cancellation. No integral interchange is assumed.

The finite-family capstone uses the literal exposing trace at every integer,
including its zero tail. It holds for arbitrary real row coefficients and
ray scale; positivity is unnecessary for this linear identity. This does not
establish the signed archimedean-energy inequality or RH.
Paper: docs/reports/weil-work/results/02-exposing-ray/GRID-DEFECT-PROOF.md.
-/

open MeasureTheory Filter Topology Set Real Zeta23
noncomputable section
namespace RHTower.ExposingRayZetaMoment
open ExposingRayGrid

/-- Finite critical Dirichlet head with the complete continuous pole removed. -/
def principal (K : ℕ) (τ : ℝ) : ℝ :=
  (∑ j ∈ Finset.range K, Real.cos (τ*Real.log (j+1))/Real.sqrt (j+1)) -
    ∫ y in 0..Real.log (K+1), 2*Real.cosh (y/2)*Real.cos (τ*y)

/-- The actual real part of zeta on the critical line. -/
def zetaReal (τ : ℝ) : ℝ := (riemannZeta (criticalPoint τ)).re

/-- Its signed moment against the actual Fourier density. -/
def moment (f : ℝ → ℂ) : ℝ := ∫ τ : ℝ, ‖paperFT f τ‖^2*zetaReal τ

private theorem principal_eq (K : ℕ) (τ : ℝ) :
    principal K τ = defect K τ -
      ∑ j ∈ Finset.range K, correctionCoeff j*Real.cos (τ*Real.log (j+1)) := by
  unfold principal defect
  rw [sub_right_comm, ← Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  unfold correctionCoeff
  ring

theorem principal_error_le (K : ℕ) (τ : ℝ) :
    |principal K τ-zetaReal τ| ≤ (8+2*|τ|)/Real.sqrt (K+1) := by
  have hd := defect_error_le K τ
  have hc := correction_tail_le K τ
  rw [principal_eq]
  unfold zetaReal
  have he : defect K τ -
      (∑ j ∈ Finset.range K, correctionCoeff j*Real.cos (τ*Real.log (j+1))) -
      (riemannZeta (criticalPoint τ)).re =
      (defect K τ-((riemannZeta (criticalPoint τ)).re+correction τ)) -
      ((∑ j ∈ Finset.range K, correctionCoeff j*Real.cos (τ*Real.log (j+1)))-correction τ) := by ring
  rw [he]
  have htriangle (a b : ℝ) : |a-b| ≤ |a|+|b| := by
    simpa only [sub_zero, zero_sub, abs_neg] using abs_sub_le a 0 b
  exact (htriangle _ _).trans ((add_le_add hd hc).trans_eq (by ring))

private theorem principal_zero (τ : ℝ) : principal 0 τ = 0 := by
  simp [principal]

theorem zetaReal_linear_bound (τ : ℝ) : |zetaReal τ| ≤ 8*(1+|τ|) := by
  have h := principal_error_le 0 τ
  simp only [principal_zero, Nat.cast_zero, zero_add, Real.sqrt_one, div_one,
    zero_sub, abs_neg] at h
  linarith [abs_nonneg τ]

theorem continuous_zetaReal : Continuous zetaReal := by
  change Continuous (fun τ => (riemannZeta (criticalPoint τ)).re)
  apply Complex.continuous_re.comp
  rw [continuous_iff_continuousAt]
  intro τ
  have hn : criticalPoint τ ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    norm_num [criticalPoint] at this
  exact (differentiableAt_riemannZeta hn).continuousAt.comp
    (show Continuous criticalPoint by unfold criticalPoint; fun_prop).continuousAt

theorem integrable_moment {a : ℝ} {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f)
    (hs : tsupport f ⊆ Icc (-a) a) :
    Integrable (fun τ : ℝ => ‖paperFT f τ‖^2*zetaReal τ) :=
  integrable_normSq_paperFT_mul_of_linear hf hs continuous_zetaReal zetaReal_linear_bound

private theorem density_continuous {a : ℝ} {f : ℝ → ℂ}
    (hf : ContDiff ℝ 2 f) (hs : tsupport f ⊆ Icc (-a) a) :
    Continuous (fun τ : ℝ => ‖paperFT f τ‖^2) :=
  (continuous_paperFT_real_of_integrable
    (hf.continuous.integrable_of_hasCompactSupport (weilTest_self_data hf hs).1)).norm.pow 2

private theorem pole_joint_integrable {a : ℝ} {f : ℝ → ℂ}
    (hf : ContDiff ℝ 2 f) (hs : tsupport f ⊆ Icc (-a) a) (L : ℝ) :
    Integrable (fun p : ℝ × ℝ => (2*Real.cosh (p.1/2))*‖paperFT f p.2‖^2 *
      Real.cos (p.2*p.1)) ((volume.restrict (Set.uIoc 0 L)).prod volume) := by
  have hlag : IntervalIntegrable (fun y : ℝ => 2*Real.cosh (y/2)) volume 0 L :=
    (show Continuous (fun y : ℝ => 2*Real.cosh (y/2)) by fun_prop).intervalIntegrable _ _
  have hbase := hlag.def'.mul_prod (integrable_normSq_paperFT hf hs)
  have hcont : Continuous (fun p : ℝ × ℝ => (2*Real.cosh (p.1/2))*‖paperFT f p.2‖^2 *
      Real.cos (p.2*p.1)) := by
    have hd := (density_continuous hf hs).comp
      (continuous_snd : Continuous (fun p : ℝ × ℝ => p.2))
    fun_prop
  apply hbase.mono' hcont.aestronglyMeasurable
  filter_upwards [] with p
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity :
    0 ≤ (2*Real.cosh (p.1/2))*‖paperFT f p.2‖^2)]
  exact mul_le_of_le_one_right (by positivity) (Real.abs_cos_le_one _)

private theorem integrable_pole_pairing {a : ℝ} {f : ℝ → ℂ}
    (hf : ContDiff ℝ 2 f) (hs : tsupport f ⊆ Icc (-a) a)
    {L : ℝ} (hL : 0 ≤ L) :
    Integrable (fun τ : ℝ => ‖paperFT f τ‖^2 *
      ∫ y in 0..L, 2*Real.cosh (y/2)*Real.cos (τ*y)) := by
  have hi := (pole_joint_integrable hf hs L).integral_prod_right
  simp only [Set.uIoc_of_le hL] at hi
  convert hi using 1
  ext τ
  rw [intervalIntegral.integral_of_le hL, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with y
  ring

/-- Fubini transfers the complete frequency-side pole integral to exact polar cancellation. -/
theorem pole_pairing_eq_zero {a : ℝ} {f : ℝ → ℂ} (hf : IsPolarTest a f)
    {L : ℝ} (hL : 2*a < L) :
    (∫ τ : ℝ, ‖paperFT f τ‖^2 *
      ∫ y in 0..L, 2*Real.cosh (y/2)*Real.cos (τ*y)) = 0 := by
  have hswap := intervalIntegral_integral_swap
    (f := fun y τ : ℝ => (2*Real.cosh (y/2))*‖paperFT f τ‖^2 * Real.cos (τ*y))
    (pole_joint_integrable hf.2.1 hf.2.2.1 L)
  have hin (y : ℝ) : (∫ τ : ℝ, (2*Real.cosh (y/2))*‖paperFT f τ‖^2 *
      Real.cos (τ*y)) = (2*Real.cosh (y/2))*π*weilTestEvenPart f y := by
    simp_rw [mul_assoc]
    rw [integral_const_mul, integral_const_mul,
      integral_normSq_paperFT_mul_cos_eq hf.2.1 hf.2.2.1]
    rfl
  have hout (τ : ℝ) : (∫ y in 0..L, (2*Real.cosh (y/2))*‖paperFT f τ‖^2 *
      Real.cos (τ*y)) = ‖paperFT f τ‖^2 *
      ∫ y in 0..L, 2*Real.cosh (y/2)*Real.cos (τ*y) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro y _
    ring
  simp_rw [hin, hout] at hswap
  rw [← hswap]
  have he : (fun y : ℝ => (2*Real.cosh (y/2))*π*weilTestEvenPart f y) =
      (fun y : ℝ => π*(weilTestEvenPart f y*(Real.exp (y/2)+Real.exp (-(y/2))))) := by
    ext y
    rw [Real.cosh_eq]
    ring
  rw [he, intervalIntegral.integral_const_mul,
    integral_weilTestEvenPart_mul_cosh_eq_zero hf.1 hf.2.1 hf.2.2.1 hf.2.2.2.1 hf.2.2.2.2 hL,
    mul_zero]

private theorem integrable_head {a : ℝ} {f : ℝ → ℂ}
    (hf : ContDiff ℝ 2 f) (hs : tsupport f ⊆ Icc (-a) a) (K : ℕ) :
    Integrable (fun τ : ℝ => ‖paperFT f τ‖^2 *
      ∑ j ∈ Finset.range K, Real.cos (τ*Real.log (j+1))/Real.sqrt (j+1)) := by
  simp_rw [Finset.mul_sum, ← mul_div_assoc]
  exact integrable_finsetSum _ fun j _ =>
    (integrable_normSq_paperFT_mul_cos hf hs (Real.log ((j:ℝ)+1))).div_const _

theorem integrable_principal_pairing {a : ℝ} {f : ℝ → ℂ}
    (hf : ContDiff ℝ 2 f) (hs : tsupport f ⊆ Icc (-a) a) (K : ℕ) :
    Integrable (fun τ : ℝ => ‖paperFT f τ‖^2*principal K τ) := by
  have hL : 0 ≤ Real.log ((K:ℝ)+1) := Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) K])
  apply ((integrable_head hf hs K).sub (integrable_pole_pairing hf hs hL)).congr
  filter_upwards [] with τ
  simp only [Pi.sub_apply, principal, mul_sub]

private theorem integrable_linear_density {a : ℝ} {f : ℝ → ℂ}
    (hf : ContDiff ℝ 2 f) (hs : tsupport f ⊆ Icc (-a) a) :
    Integrable (fun τ : ℝ => ‖paperFT f τ‖^2*(8+2*|τ|)) := by
  apply integrable_normSq_paperFT_mul_of_linear hf hs (by fun_prop) (Mp := 8)
  intro τ
  rw [abs_of_nonneg (by positivity)]
  linarith [abs_nonneg τ]

/-- A quantitative integral error; all required integrability follows from compact C² regularity. -/
theorem principal_pairing_error_le {a : ℝ} {f : ℝ → ℂ}
    (hf : ContDiff ℝ 2 f) (hs : tsupport f ⊆ Icc (-a) a) (K : ℕ) :
    |(∫ τ : ℝ, ‖paperFT f τ‖^2*principal K τ)-moment f| ≤
      (∫ τ : ℝ, ‖paperFT f τ‖^2*(8+2*|τ|))/Real.sqrt (K+1) := by
  unfold moment
  rw [← integral_sub (integrable_principal_pairing hf hs K) (integrable_moment hf hs),
    ← integral_div]
  rw [← Real.norm_eq_abs]
  apply norm_integral_le_of_norm_le ((integrable_linear_density hf hs).div_const _)
  filter_upwards [] with τ
  rw [← mul_sub, Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg _)]
  simpa only [mul_div_assoc] using
    mul_le_mul_of_nonneg_left (principal_error_le K τ) (sq_nonneg ‖paperFT f τ‖)

theorem tendsto_principal_pairing {a : ℝ} {f : ℝ → ℂ}
    (hf : ContDiff ℝ 2 f) (hs : tsupport f ⊆ Icc (-a) a) :
    Tendsto (fun K : ℕ => ∫ τ : ℝ, ‖paperFT f τ‖^2*principal K τ) atTop (𝓝 (moment f)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hz : Tendsto (fun K : ℕ => ((K:ℝ)+1)^(-(1/2:ℝ))) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<1/2)).comp
      (by simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using
        (tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat 1))
  have hlim := hz.const_mul (∫ τ : ℝ, ‖paperFT f τ‖^2*(8+2*|τ|))
  simp only [mul_zero] at hlim
  apply squeeze_zero (fun K => norm_nonneg _)
  · intro K
    have h := principal_pairing_error_le hf hs K
    simpa only [Real.rpow_neg (by positivity : 0 ≤ (K:ℝ)+1),
      ← Real.sqrt_eq_rpow, ← div_eq_mul_inv, Real.norm_eq_abs] using h
  · convert hlim using 1
    funext K
    rw [Real.rpow_neg (by positivity), ← Real.sqrt_eq_rpow, div_eq_mul_inv]

private theorem head_pairing {a : ℝ} {f : ℝ → ℂ}
    (hf : ContDiff ℝ 2 f) (hs : tsupport f ⊆ Icc (-a) a) {K : ℕ} (hK : 1 ≤ K) :
    (∫ τ : ℝ, ‖paperFT f τ‖^2 *
      ∑ j ∈ Finset.range K, Real.cos (τ*Real.log (j+1))/Real.sqrt (j+1)) =
      (∫ τ : ℝ, ‖paperFT f τ‖^2) +
        π*∑ n ∈ Finset.Icc 2 K, atomCoeff f n/Real.sqrt n := by
  induction K, hK using Nat.le_induction with
  | base => simp
  | succ K hK ih =>
    simp_rw [Finset.sum_range_succ, mul_add]
    rw [integral_add (integrable_head hf hs K)
      (by simpa only [mul_div_assoc] using
        ((integrable_normSq_paperFT_mul_cos hf hs (Real.log ((K:ℝ)+1))).div_const
          (Real.sqrt ((K:ℝ)+1)))), ih]
    simp_rw [← mul_div_assoc]
    rw [integral_div, integral_normSq_paperFT_mul_cos_eq hf hs,
      Finset.sum_Icc_succ_top (by omega)]
    simp only [atomCoeff, Nat.cast_add, Nat.cast_one]
    ring

theorem principal_pairing_eq {a : ℝ} {f : ℝ → ℂ} (hf : IsPolarTest a f)
    {K : ℕ} (hK : 1 ≤ K) (hL : 2*a < Real.log ((K:ℝ)+1)) :
    (∫ τ : ℝ, ‖paperFT f τ‖^2*principal K τ) =
      (∫ τ : ℝ, ‖paperFT f τ‖^2) +
        π*∑ n ∈ Finset.Icc 2 K, atomCoeff f n/Real.sqrt n := by
  simp_rw [principal, mul_sub]
  rw [integral_sub (integrable_head hf.2.1 hf.2.2.1 K)
    (integrable_pole_pairing hf.2.1 hf.2.2.1 (by linarith [hf.1])),
    pole_pairing_eq_zero hf hL, sub_zero]
  exact head_pairing hf.2.1 hf.2.2.1 hK

theorem moment_eq_at_cutoff {a : ℝ} {f : ℝ → ℂ} (hf : IsPolarTest a f)
    {M : ℕ} (hM : ⌊Real.exp (2*a)⌋₊ ≤ M) :
    moment f = (∫ τ : ℝ, ‖paperFT f τ‖^2) +
      π*∑ n ∈ Finset.Icc 2 M, atomCoeff f n/Real.sqrt n := by
  have hfloor : 1 ≤ ⌊Real.exp (2*a)⌋₊ :=
    (Nat.one_le_floor_iff _).2 (Real.one_le_exp_iff.2 (by linarith [hf.1]))
  have hEq : ∀ᶠ K : ℕ in atTop,
      (∫ τ : ℝ, ‖paperFT f τ‖^2*principal K τ) =
      (∫ τ : ℝ, ‖paperFT f τ‖^2) +
        π*∑ n ∈ Finset.Icc 2 M, atomCoeff f n/Real.sqrt n := by
    filter_upwards [eventually_ge_atTop M] with K hMK
    have hL : 2*a < Real.log ((K:ℝ)+1) := by
      apply (Real.lt_log_iff_exp_lt (by positivity)).2
      have hn : (⌊Real.exp (2*a)⌋₊:ℝ) ≤ K := by exact_mod_cast hM.trans hMK
      linarith [Nat.lt_floor_add_one (Real.exp (2*a))]
    rw [principal_pairing_eq hf (hfloor.trans (hM.trans hMK)) hL]
    congr 1
    congr 1
    symm
    apply Finset.sum_subset
      (show Finset.Icc 2 M ⊆ Finset.Icc 2 K from Finset.Icc_subset_Icc le_rfl hMK)
    intro n hn hnM
    have hMn : M < n := by
      have hn2 := (Finset.mem_Icc.mp hn).1
      have hnM' : ¬(2 ≤ n ∧ n ≤ M) := by simpa only [Finset.mem_Icc] using hnM
      omega
    rw [atomCoeff_eq_zero_of_floor_lt hf.2.2.1 (hM.trans_lt hMn), zero_div]
  exact tendsto_nhds_unique (tendsto_principal_pairing hf.2.1 hf.2.2.1)
    (tendsto_const_nhds.congr' (by
      filter_upwards [hEq] with K hK
      exact hK.symm))

/-- Exact zeta moment of every actual compact complex polar test. -/
theorem moment_eq {a : ℝ} {f : ℝ → ℂ} (hf : IsPolarTest a f) :
    moment f = (∫ τ : ℝ, ‖paperFT f τ‖^2) +
      π*∑ n ∈ Finset.Icc 2 ⌊Real.exp (2*a)⌋₊, atomCoeff f n/Real.sqrt n :=
  moment_eq_at_cutoff hf le_rfl

private theorem truncated_sum_eq {N M : ℕ} (hNM : N ≤ M) :
    (∑ n ∈ Finset.Icc 2 M, exposingWeightTrunc N n/Real.sqrt n) =
      ∑ n ∈ Finset.Icc 2 N, exposingWeight n/Real.sqrt n := by
  have hsub : Finset.Icc 2 N ⊆ Finset.Icc 2 M := Finset.Icc_subset_Icc le_rfl hNM
  have he : (∑ n ∈ Finset.Icc 2 N, exposingWeightTrunc N n/Real.sqrt n) =
      ∑ n ∈ Finset.Icc 2 M, exposingWeightTrunc N n/Real.sqrt n := by
    apply Finset.sum_subset hsub
    intro n hn hnN
    have hNn : N < n := by
      have hn2 := (Finset.mem_Icc.mp hn).1
      have hnN' : ¬(2 ≤ n ∧ n ≤ N) := by simpa only [Finset.mem_Icc] using hnN
      omega
    rw [exposingWeightTrunc_eq_zero hNn, zero_div]
  rw [← he]
  apply Finset.sum_congr rfl
  intro n hn
  rw [exposingWeightTrunc, if_pos (Finset.mem_Icc.mp hn).2]

/-- Every matched finite family has this moment, with no restriction on signs or row count. -/
theorem matched_moment {ι : Type*} [Fintype ι]
    (a : ι → ℝ) (f : ι → ℝ → ℂ) (α : ι → ℝ)
    (hf : ∀ i, IsPolarTest (a i) (f i)) (N : ℕ) (t : ℝ)
    (hmatch : ∀ n : ℕ, 2 ≤ n →
      2*π*(∑ i, α i*atomCoeff (f i) n) = t*exposingWeightTrunc N n) :
    (∑ i, α i*moment (f i)) =
      (∑ i, α i*(∫ τ : ℝ, ‖paperFT (f i) τ‖^2)) +
        (t/2)*(∑ n ∈ Finset.Icc 2 N, exposingWeight n/Real.sqrt n) := by
  classical
  let M := max N (Finset.univ.sup (fun i : ι => ⌊Real.exp (2*a i)⌋₊))
  have hM (i : ι) : ⌊Real.exp (2*a i)⌋₊ ≤ M :=
    (Finset.le_sup (f := fun i : ι => ⌊Real.exp (2*a i)⌋₊)
      (Finset.mem_univ i)).trans (le_max_right _ _)
  have he (i : ι) := moment_eq_at_cutoff (hf i) (hM i)
  simp_rw [he, mul_add, Finset.sum_add_distrib]
  congr 1
  have hsum : (∑ i, α i*(π*∑ n ∈ Finset.Icc 2 M, atomCoeff (f i) n/Real.sqrt n)) =
      π*∑ n ∈ Finset.Icc 2 M, (∑ i, α i*atomCoeff (f i) n)/Real.sqrt n := by
    simp_rw [Finset.mul_sum, Finset.sum_div]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro n _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hsum, Finset.mul_sum]
  have hterm (n : ℕ) (hn : n ∈ Finset.Icc 2 M) :
      π*((∑ i, α i*atomCoeff (f i) n)/Real.sqrt n) =
        (t/2)*(exposingWeightTrunc N n/Real.sqrt n) := by
    have h := hmatch n (Finset.mem_Icc.mp hn).1
    calc
      _ = (2*π*(∑ i, α i*atomCoeff (f i) n))/(2*Real.sqrt n) := by ring
      _ = _ := by rw [h]; ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, truncated_sum_eq (le_max_left _ _)]

end RHTower.ExposingRayZetaMoment
