import GaloisForLFunctions.RHTower.Suzuki.SuzukiCausalDepthGammaFiniteRowBoundary
import GaloisForLFunctions.HTGeometry.DiagonalEllTwoIndexed
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Literal radial regularization of the two-leg Gamma source

Multiplication of an arithmetic input by `1-r^n` cancels its boundary defect.
The resulting input/output pair belongs to the graph closure of the original
finite packets. No replacement columns or assumed graph-domain membership
enter this construction.
-/

open Filter Topology
open scoped BigOperators ENNReal InnerProduct
set_option autoImplicit false

noncomputable section
namespace RHTower
open GaloisForLFunctions.HTGeometry

private abbrev H := SuzukiCausalDepthGammaTraceL2
private abbrev Index := SuzukiCausalDepthGammaTraceIndex

def suzukiGammaSourceRadius (pe : Nat.Primes × ℕ) : ℝ :=
  Real.tanh (suzukiCausalDepthGammaFrequency pe)

theorem suzukiGammaSourceRadius_pos (pe : Nat.Primes × ℕ) :
    0 < suzukiGammaSourceRadius pe :=
  tanh_pos_of_pos (suzukiCausalDepthGammaFrequency_pos pe)

theorem suzukiGammaSourceRadius_lt_one (pe : Nat.Primes × ℕ) :
    suzukiGammaSourceRadius pe < 1 := Real.tanh_lt_one _

def suzukiGammaSourcePowerSymbol (n : ℕ) : Index → ℂ :=
  Sum.elim (fun pe => (suzukiGammaSourceRadius pe ^ n : ℝ)) (fun _ => 0)

theorem norm_suzukiGammaSourcePowerSymbol_le (n : ℕ) (i : Index) :
    ‖suzukiGammaSourcePowerSymbol n i‖ ≤ 1 := by
  cases i with
  | inl pe =>
    change ‖((suzukiGammaSourceRadius pe ^ n : ℝ) : ℂ)‖ ≤ 1
    rw [Complex.norm_real, Real.norm_of_nonneg (pow_nonneg (suzukiGammaSourceRadius_pos pe).le n)]
    exact pow_le_one₀ (suzukiGammaSourceRadius_pos pe).le (suzukiGammaSourceRadius_lt_one pe).le
  | inr k => simp [suzukiGammaSourcePowerSymbol]

def suzukiGammaSourcePower (n : ℕ) : H →L[ℂ] H :=
  HTGeometry.ellTwoDiagonal (suzukiGammaSourcePowerSymbol n)
    (norm_suzukiGammaSourcePowerSymbol_le n)

def suzukiGammaSourceRegularization (n : ℕ) : H →L[ℂ] H :=
  ContinuousLinearMap.id ℂ H - suzukiGammaSourcePower n

theorem suzukiGammaSourceRegularization_single (n : ℕ) (i : Index) :
    suzukiGammaSourceRegularization n (lp.single 2 i (1 : ℂ)) =
      (1 - suzukiGammaSourcePowerSymbol n i) • lp.single 2 i (1 : ℂ) := by
  change lp.single 2 i (1 : ℂ) -
      suzukiGammaSourcePower n (lp.single 2 i (1 : ℂ)) = _
  rw [suzukiGammaSourcePower,
    ← HTGeometry.ellTwoCoordinateBasis_apply i,
    HTGeometry.ellTwoDiagonal_coordinateBasis]
  module

theorem suzukiGammaSourceGain_nonneg_le (n : ℕ) (pe : Nat.Primes × ℕ) :
    0 ≤ (pe.1 : ℝ) * (1 - suzukiGammaSourceRadius pe ^ n) ∧
      (pe.1 : ℝ) * (1 - suzukiGammaSourceRadius pe ^ n) ≤ 2 * (n : ℝ) := by
  have hp : 0 ≤ (pe.1 : ℝ) := Nat.cast_nonneg _
  have hr := suzukiGammaSourceRadius_pos pe
  have hr1 := suzukiGammaSourceRadius_lt_one pe
  have hpow : suzukiGammaSourceRadius pe ^ n ≤ 1 := pow_le_one₀ hr.le hr1.le
  refine ⟨mul_nonneg hp (sub_nonneg.mpr hpow), ?_⟩
  have hd := suzukiCausalDepthGamma_prime_mul_boundaryDefect_le_two pe
  change (pe.1 : ℝ) * (1 - suzukiGammaSourceRadius pe) ≤ 2 at hd
  induction n with
  | zero => simp
  | succ n ih =>
    have hpn := pow_nonneg hr.le n
    have hpl : suzukiGammaSourceRadius pe ^ n ≤ 1 := pow_le_one₀ hr.le hr1.le
    have hg : 0 ≤ (pe.1 : ℝ) * (1 - suzukiGammaSourceRadius pe) :=
      mul_nonneg hp (sub_nonneg.mpr hr1.le)
    have ht := mul_le_mul_of_nonneg_left hd hpn
    have hi := ih hpl
    rw [pow_succ]
    push_cast
    nlinarith

def suzukiGammaSourceGainSymbol (n : ℕ) : Index → ℂ :=
  Sum.elim (fun pe => ((pe.1 : ℝ) * (1 - suzukiGammaSourceRadius pe ^ n) : ℝ))
    (fun _ => 0)

theorem norm_suzukiGammaSourceGainSymbol_le (n : ℕ) (i : Index) :
    ‖suzukiGammaSourceGainSymbol n i‖ ≤ 2 * (n : ℝ) := by
  cases i with
  | inl pe =>
    change ‖(((pe.1 : ℝ) * (1 - suzukiGammaSourceRadius pe ^ n) : ℝ) : ℂ)‖ ≤ _
    rw [Complex.norm_real, Real.norm_of_nonneg (suzukiGammaSourceGain_nonneg_le n pe).1]
    exact (suzukiGammaSourceGain_nonneg_le n pe).2
  | inr k => simp [suzukiGammaSourceGainSymbol]

def suzukiGammaRegularizedSynthesis (h a : Set.Ioi (0 : ℝ)) (n : ℕ) : H →L[ℂ] H :=
  (suzukiCausalDepthGammaFeatureOperator h.1 a.1 h.2 a.2).comp
    (HTGeometry.ellTwoDiagonal (suzukiGammaSourceGainSymbol n)
      (norm_suzukiGammaSourceGainSymbol_le n))

theorem suzukiGammaRegularizedSynthesis_single
    (h a : Set.Ioi (0 : ℝ)) (n : ℕ) (i : Index) :
    suzukiGammaRegularizedSynthesis h a n (lp.single 2 i (1 : ℂ)) =
      (1 - suzukiGammaSourcePowerSymbol n i) • suzukiGammaTwoLegFullColumn h a i := by
  rw [suzukiGammaRegularizedSynthesis, ContinuousLinearMap.comp_apply,
    ← HTGeometry.ellTwoCoordinateBasis_apply i, HTGeometry.ellTwoDiagonal_coordinateBasis,
    HTGeometry.ellTwoCoordinateBasis_apply, map_smul]
  cases i with
  | inl pe =>
    simp only [suzukiGammaSourceGainSymbol, suzukiGammaSourcePowerSymbol,
      Sum.elim_inl, suzukiGammaTwoLegFullColumn, suzukiGammaTwoLegColumn,
      smul_smul, Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_one]
    congr 1
    push_cast
    ring
  | inr k => simp [suzukiGammaSourceGainSymbol, suzukiGammaTwoLegFullColumn]

/-- Every regularized source lies in the actual minimal graph, by completion of
its literal finite packets. -/
theorem suzukiGammaRegularizedSynthesis_mem_closedGraph
    (h a : Set.Ioi (0 : ℝ)) (n : ℕ) (u : H) :
    (suzukiGammaSourceRegularization n u, suzukiGammaRegularizedSynthesis h a n u) ∈
      suzukiGammaTwoLegClosedGraph h a := by
  let F := (suzukiGammaSourceRegularization n).prod (suzukiGammaRegularizedSynthesis h a n)
  have hsingle (i : Index) : F (lp.single 2 i (1 : ℂ)) ∈
      suzukiGammaTwoLegClosedGraph h a := by
    change (suzukiGammaSourceRegularization n (lp.single 2 i (1 : ℂ)),
      suzukiGammaRegularizedSynthesis h a n (lp.single 2 i (1 : ℂ))) ∈ _
    rw [suzukiGammaSourceRegularization_single, suzukiGammaRegularizedSynthesis_single]
    exact (suzukiGammaTwoLegClosedGraph h a).smul_mem _
      (by simpa only [suzukiGammaTwoLegClosedSynthesis_graph] using
        suzukiGammaTwoLegClosedSynthesis_single_graph h a i)
  have ht := F.continuous.tendsto u |>.comp
    (lp.hasSum_single (p := (2 : ENNReal)) (by norm_num) u)
  apply (Submodule.isClosed_topologicalClosure _).mem_of_tendsto ht
  filter_upwards with s
  change F (∑ i ∈ s, lp.single 2 i (u i)) ∈ suzukiGammaTwoLegClosedGraph h a
  rw [map_sum]
  apply Submodule.sum_mem
  intro i _
  have hi := (suzukiGammaTwoLegClosedGraph h a).smul_mem (u i) (hsingle i)
  simpa only [← map_smul, ← lp.single_smul, smul_eq_mul, mul_one] using hi

theorem tendsto_suzukiGammaSourceRegularization (u : H) :
    Tendsto (fun n => suzukiGammaSourceRegularization n u) atTop (𝓝 u) := by
  have hpoint (i : Index) :
      Tendsto (fun n => ‖suzukiGammaSourcePower n u i‖ ^ 2) atTop (𝓝 0) := by
    cases i with
    | inl pe =>
      have ht := tendsto_pow_atTop_nhds_zero_of_lt_one
        (suzukiGammaSourceRadius_pos pe).le (suzukiGammaSourceRadius_lt_one pe)
      have hz := ((Complex.continuous_ofReal.tendsto 0).comp ht).mul_const (u (Sum.inl pe))
      simpa [suzukiGammaSourcePower, suzukiGammaSourcePowerSymbol] using hz.norm.pow 2
    | inr k => simp [suzukiGammaSourcePower, suzukiGammaSourcePowerSymbol]
  have hbound (n : ℕ) (i : Index) :
      ‖‖suzukiGammaSourcePower n u i‖ ^ 2‖ ≤ ‖u i‖ ^ 2 := by
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    change ‖suzukiGammaSourcePowerSymbol n i * u i‖ ^ 2 ≤ _
    rw [norm_mul]
    have hm : ‖suzukiGammaSourcePowerSymbol n i‖ * ‖u i‖ ≤ ‖u i‖ := by
      simpa using (mul_le_mul_of_nonneg_right
        (norm_suzukiGammaSourcePowerSymbol_le n i) (norm_nonneg (u i)))
    exact pow_le_pow_left₀ (by positivity) hm 2
  have ht := tendsto_tsum_of_dominated_convergence
    (HilbertSchmidt.summable_coe_sq u) hpoint (Filter.Eventually.of_forall hbound)
  simp only [tsum_zero, ← HilbertSchmidt.lp_norm_sq_eq] at ht
  have hn := Real.continuous_sqrt.continuousAt.tendsto.comp ht
  simp only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] at hn
  have hp : Tendsto (fun n => suzukiGammaSourcePower n u) atTop (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr hn
  simpa [suzukiGammaSourceRegularization] using tendsto_const_nhds.sub hp

end RHTower
