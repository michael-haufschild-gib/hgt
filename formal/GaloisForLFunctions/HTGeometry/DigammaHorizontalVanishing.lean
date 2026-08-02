import GaloisForLFunctions.RHTower.DigammaGaussSeries
import Mathlib.NumberTheory.Harmonic.EulerMascheroni

/-!
# The digamma defect vanishes along the shift orbit

Along a horizontal orbit `z, z+1, z+2, …` the difference `ψ(z+n) − log(z+n)` tends to zero.  This is
the vanishing hypothesis of the telescoping estimate, and it is what makes the difference equation
determine the asymptotic expansion.

The proof is the Gauss series read backwards: the finite Gauss sum equals `ψ(z)+γ−(ψ(z+N)−ψ(N+1))`,
so `ψ(z+N)` differs from `ψ(N+1)` by a convergent tail, `ψ(N+1) = −γ + H_N` is the harmonic number,
and `H_N − log N → γ`, while `log(z+N) − log N → 0` because the modulus ratio tends to one and the
argument tends to zero.
-/

open Filter Topology Complex

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

/-- The digamma value at a positive integer is the harmonic number shifted by `-γ`. -/
theorem digamma_natCast_add_one (N : ℕ) :
    Complex.digamma ((N : ℂ) + 1)
      = -(Real.eulerMascheroniConstant : ℂ) + ∑ k ∈ Finset.range N, 1 / ((k : ℂ) + 1) := by
  induction N with
  | zero => simpa using Complex.digamma_one
  | succ N ih =>
      have hpole : ∀ m : ℕ, ((N : ℂ) + 1) ≠ -(m : ℂ) := by
        intro m hm
        have hre : ((N : ℂ) + 1).re = -(m : ℝ) := by
          rw [hm]
          simp
        simp only [Complex.add_re, Complex.natCast_re, Complex.one_re] at hre
        have : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
        have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
        linarith
      have hstep := Complex.digamma_apply_add_one ((N : ℂ) + 1) hpole
      have hcast : ((N + 1 : ℕ) : ℂ) + 1 = ((N : ℂ) + 1) + 1 := by push_cast; ring
      rw [hcast, hstep, ih, Finset.sum_range_succ]
      ring

/-- The harmonic sum in complex form. -/
theorem sum_one_div_natCast_succ_eq_harmonic (N : ℕ) :
    ∑ k ∈ Finset.range N, 1 / ((k : ℂ) + 1) = ((harmonic N : ℚ) : ℂ) := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, ih, harmonic_succ]
      push_cast
      ring

/-- The digamma value at a positive integer minus the logarithm tends to zero. -/
theorem tendsto_digamma_natCast_sub_log :
    Tendsto (fun N : ℕ => Complex.digamma ((N : ℂ) + 1) - Complex.log (N : ℂ))
      atTop (nhds 0) := by
  have hreal : Tendsto (fun N : ℕ => ((harmonic N : ℚ) : ℝ) - Real.log N) atTop
      (nhds Real.eulerMascheroniConstant) := Real.tendsto_harmonic_sub_log
  have hshift : Tendsto (fun N : ℕ => (((harmonic N : ℚ) : ℝ) - Real.log N)
      - Real.eulerMascheroniConstant) atTop (nhds 0) := by
    simpa using hreal.sub (tendsto_const_nhds (x := Real.eulerMascheroniConstant))
  have hC : Tendsto (fun N : ℕ => (((((harmonic N : ℚ) : ℝ) - Real.log N)
      - Real.eulerMascheroniConstant : ℝ) : ℂ)) atTop (nhds 0) := by
    have hcomp := (Complex.continuous_ofReal.tendsto (0 : ℝ)).comp hshift
    simpa [Function.comp_def] using hcomp
  refine hC.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with N hN
  have hlog : Complex.log (N : ℂ) = ((Real.log N : ℝ) : ℂ) := by
    rw [show ((N : ℂ)) = ((N : ℝ) : ℂ) by push_cast; ring]
    exact (Complex.ofReal_log (by positivity)).symm
  rw [digamma_natCast_add_one, sum_one_div_natCast_succ_eq_harmonic, hlog]
  push_cast
  ring


/-- Along the shift orbit the logarithm difference vanishes. -/
theorem tendsto_log_add_nat_sub_log (z : ℂ) :
    Tendsto (fun N : ℕ => Complex.log (z + N) - Complex.log (N : ℂ)) atTop (nhds 0) := by
  have hquot : Tendsto (fun N : ℕ => z / (N : ℂ)) atTop (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hnorm : ∀ N : ℕ, ‖z / (N : ℂ)‖ = ‖z‖ / (N : ℝ) := by
      intro N
      rw [norm_div, Complex.norm_natCast]
    refine Tendsto.congr (fun N => (hnorm N).symm) ?_
    exact tendsto_const_div_atTop_nhds_zero_nat ‖z‖
  have hto1 : Tendsto (fun N : ℕ => 1 + z / (N : ℂ)) atTop (nhds 1) := by
    have := tendsto_const_nhds (x := (1 : ℂ)) (f := atTop (α := ℕ))
    simpa using this.add hquot
  have hlog1 : Tendsto (fun N : ℕ => Complex.log (1 + z / (N : ℂ))) atTop (nhds 0) := by
    have hcont : ContinuousAt Complex.log 1 := by
      refine _root_.continuousAt_clog ?_
      simp [Complex.mem_slitPlane_iff]
    have := hcont.tendsto.comp hto1
    simpa [Function.comp_def] using this
  refine hlog1.congr' ?_
  have hnezero : ∀ᶠ N : ℕ in atTop, 1 + z / (N : ℂ) ≠ 0 := by
    have := hto1.eventually (eventually_ne_nhds (by norm_num : (1 : ℂ) ≠ 0))
    exact this
  filter_upwards [eventually_gt_atTop 0, hnezero] with N hN hne
  have hNC : ((N : ℝ) : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    positivity
  have hfac : z + (N : ℂ) = ((N : ℝ) : ℂ) * (1 + z / (N : ℂ)) := by
    have hNC' : ((N : ℂ)) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    rw [show ((N : ℝ) : ℂ) = (N : ℂ) by push_cast; ring]
    field_simp
    ring
  have hlogN : Complex.log ((N : ℂ)) = ((Real.log N : ℝ) : ℂ) := by
    rw [show ((N : ℂ)) = ((N : ℝ) : ℂ) by push_cast; ring]
    exact (Complex.ofReal_log (by positivity)).symm
  rw [hfac, Complex.log_ofReal_mul (by positivity) hne, hlogN]
  ring

/-- **The digamma defect vanishes along the shift orbit.**  For every point of the right half plane
`ψ(z+N) − log(z+N) → 0` as `N → ∞`. -/
theorem tendsto_digamma_sub_log_horizontal {z : ℂ} (hz : 0 < z.re) :
    Tendsto (fun N : ℕ => Complex.digamma (z + N) - Complex.log (z + N)) atTop (nhds 0) := by
  have hgauss : Tendsto
      (fun N : ℕ => ∑ n ∈ Finset.range N, RHTower.gaussDigammaSeriesTerm z n) atTop
      (nhds (Complex.digamma z + (Real.eulerMascheroniConstant : ℂ))) := by
    have hsum := RHTower.summable_gaussDigammaSeriesTerm hz
    have hval := RHTower.digamma_eq_neg_euler_add_tsum_gauss hz
    have hhas : HasSum (RHTower.gaussDigammaSeriesTerm z)
        (Complex.digamma z + (Real.eulerMascheroniConstant : ℂ)) := by
      have := hsum.hasSum
      rw [hval]
      simpa [add_comm, add_left_comm, add_assoc] using this
    exact hhas.tendsto_sum_nat
  have hterm : ∀ N : ℕ, Complex.digamma (z + N) - Complex.log (z + N)
      = (Complex.digamma ((N : ℂ) + 1) - Complex.log (N : ℂ))
        - (Complex.log (z + N) - Complex.log (N : ℂ))
        + ((Complex.digamma z + (Real.eulerMascheroniConstant : ℂ))
          - ∑ n ∈ Finset.range N, RHTower.gaussDigammaSeriesTerm z n) := by
    intro N
    have hid := RHTower.sum_gaussDigammaSeriesTerm_eq_digamma_shift hz N
    rw [hid]
    ring
  have hlim := ((tendsto_digamma_natCast_sub_log.sub (tendsto_log_add_nat_sub_log z)).add
    ((tendsto_const_nhds (x := Complex.digamma z + (Real.eulerMascheroniConstant : ℂ))
      (f := atTop (α := ℕ))).sub hgauss))
  simpa using hlim.congr (fun N => (hterm N).symm)

end

end GaloisForLFunctions.HTGeometry
