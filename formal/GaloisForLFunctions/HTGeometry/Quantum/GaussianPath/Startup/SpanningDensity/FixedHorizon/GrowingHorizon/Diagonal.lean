import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.FixedHorizon.Concentration.UniformOverlap
import GaloisForLFunctions.HTGeometry.MonotoneDiagonalSelection
import Mathlib.Analysis.PSeries

/-! # Dense circuit cuts lose overlap on a deterministic expanding window -/
open MeasureTheory Filter Set
open scoped Topology Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpanningDensity.FixedHorizon
noncomputable section
local instance : IsProbabilityMeasure pathPauliDisorderLaw := by unfold pathPauliDisorderLaw; infer_instance

/-- The same expanding interval controls all circuits. Its reciprocal is
both the cut-density and the overlap threshold, so both tend to zero. -/
theorem gaussian_expanding_cut_window :
    ∃ L : ℕ → ℕ, Monotone L ∧ Tendsto L atTop atTop ∧
      ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop, ∀ t ∈ Icc (1/(L n:ℝ)) (L n:ℝ),
        ω ∉ cutOverlapEvent n t (1/(L n:ℝ)) (1/(L n:ℝ)) := by
  classical
  obtain ⟨C,hC,hbound⟩ := gaussian_ae_pathHamiltonian_linear_norm_bound
  let H (k : ℕ) : ℝ := (k+1:ℕ)
  let d (k : ℕ) := 1/H k
  have hH (k) : 1 ≤ H k := by dsimp only [H]; exact_mod_cast (show 1 ≤ k+1 by omega)
  have hd (k) : 0 < d k := one_div_pos.mpr (zero_lt_one.trans_le (hH k))
  let B (k n : ℕ) := gridOverlap (d k) (H k) (d k) (d k/2) n
  let P (k n : ℕ) := pathPauliDisorderLaw.real (B k n) ≤ ((n:ℝ)^2)⁻¹ ∧
    max (H k-d k) (4*C/d k) < (n:ℝ)
  have hrow (k : ℕ) : ∀ᶠ n : ℕ in atTop, P k n := by
    have hwin : d k ≤ H k := (one_div_le_one_div_of_le zero_lt_one (hH k)).trans (by simpa using hH k)
    obtain ⟨A,_,c,hc,htail⟩ := grid_overlap_tail (hd k) hwin (hd k) (half_pos (hd k))
    have hsmall := ((Real.summable_pow_mul_exp_neg_nat_mul 5 hc).mul_left A).tendsto_atTop_zero
    obtain ⟨N,hN⟩ := exists_nat_gt (max (H k-d k) (4*C/d k))
    filter_upwards [htail,hsmall.eventually_lt_const zero_lt_one,eventually_ge_atTop N,
      eventually_ge_atTop 1] with n hn hsmall hlarge hpos
    refine ⟨hn.trans ?_,hN.trans_le (Nat.cast_le.mpr hlarge)⟩
    rw [←one_div,le_div_iff₀ (sq_pos_of_pos (Nat.cast_pos.mpr (by omega : 0 < n)))]
    calc A*(n:ℝ)^3*Real.exp (-c*n)*n^2 = A*((n:ℝ)^5*Real.exp (-c*n)) := by ring
         _ ≤ 1 := hsmall.le
  let F (k n : ℕ) : Bool := decide (P k n)
  have hF (k) : Tendsto (F k) atTop (pure true) := by
    apply tendsto_pure.mpr
    filter_upwards [hrow k] with n hn
    exact decide_eq_true hn
  obtain ⟨m,hm,_,htop,hmP⟩ := exists_monotone_diagonal_tendsto F hF
  have hgood : ∀ᶠ n : ℕ in atTop, P (m n) n := by
    filter_upwards [tendsto_pure.mp hmP] with n hn
    exact of_decide_eq_true hn
  have hsum : Summable fun n => pathPauliDisorderLaw.real (B (m n) n) := by
    apply (Real.summable_nat_pow_inv.2 (by norm_num : 1 < (2:ℕ))).of_norm_bounded_eventually_nat
    filter_upwards [hgood] with n hn
    simpa only [Real.norm_of_nonneg measureReal_nonneg] using hn.1
  have hb : ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop, ω ∉ B (m n) n := by
    apply ae_eventually_notMem
    simpa only [ofReal_measureReal (measure_ne_top _ _)] using hsum.tsum_ofReal_ne_top
  refine ⟨fun n => m n+1,fun _ _ h => Nat.succ_le_succ (hm h),(tendsto_add_atTop_nat 1).comp htop,?_⟩
  filter_upwards [hb,hbound] with ω hw hnorm
  filter_upwards [hw,hnorm,hgood,eventually_ge_atTop 2] with n hn hH' hP hn₂
  exact exclude_from_grid hC (hd (m n)) hn₂ hP.2 hH' hn

#print axioms gaussian_expanding_cut_window
end
end GaloisForLFunctions.HTGeometry.SpanningDensity.FixedHorizon
