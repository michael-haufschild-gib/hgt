import GaloisForLFunctions.HTGeometry.ExplicitDigammaHerglotzPalette
import GaloisForLFunctions.HTGeometry.DigammaAsymptotic

/-!
# Canonical selection of the explicit digamma Herglotz source

The closed formula `psi(z + 1/2) + gamma` is not merely one convenient point.  On the right
half-plane it is forced by its unit-shift cocycle and its logarithmic normalization at infinity.

The analytic input is the already proved digamma asymptotic.  The new source-selection step is
the elementary rigidity mechanism: two solutions of the same additive cocycle differ by a
one-periodic function, while a periodic function tending to zero along every positive integer
translate is identically zero.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

/-- The unit-shift cocycle of the half-shifted digamma source. -/
noncomputable def explicitDigammaSourceCocycle (z : ℂ) : ℂ := (z + 1 / 2)⁻¹

/-- The explicit source satisfies its canonical half-shifted digamma recurrence on the right
half-plane. -/
theorem explicitDigammaHerglotzSource_add_one {z : ℂ} (hz : 0 < z.re) :
    explicitDigammaHerglotzSource (z + 1) =
      explicitDigammaHerglotzSource z + explicitDigammaSourceCocycle z := by
  have hpole : ∀ m : ℕ, z + 1 / 2 ≠ -(m : ℂ) := by
    intro m h
    have hre := congrArg Complex.re h
    norm_num at hre
    have hm : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  rw [explicitDigammaHerglotzSource, explicitDigammaHerglotzSource,
    show z + 1 + 1 / 2 = (z + 1 / 2) + 1 by ring,
    Complex.digamma_apply_add_one (z + 1 / 2) hpole]
  simp only [explicitDigammaSourceCocycle]
  abel_nf

/-- A fixed positive-real translate changes the principal logarithm by a term tending to zero. -/
theorem complex_log_add_nat_sub_log_nat_tendsto (w : ℂ) (hw : 0 < w.re) :
    Tendsto (fun N : ℕ ↦ Complex.log (w + N) - Complex.log ((N : ℂ) + 1))
      atTop (nhds 0) := by
  let ratio : ℕ → ℂ := fun N ↦ (w + N) / ((N : ℂ) + 1)
  have hsmall : Tendsto (fun N : ℕ ↦ (w - 1) * (1 / ((N : ℂ) + 1)))
      atTop (nhds 0) := by
    simpa using tendsto_const_nhds.mul
      (tendsto_one_div_add_atTop_nhds_zero_nat :
        Tendsto (fun N : ℕ ↦ (1 : ℂ) / ((N : ℂ) + 1)) atTop (nhds 0))
  have hratio : Tendsto ratio atTop (nhds 1) := by
    have h := (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (1 : ℂ)) atTop (nhds 1)).add hsmall
    have heq : ratio = fun N : ℕ ↦ 1 + (w - 1) * (1 / ((N : ℂ) + 1)) := by
      funext N
      dsimp [ratio]
      have hden : ((N : ℂ) + 1) ≠ 0 := by
        exact_mod_cast Nat.succ_ne_zero N
      field_simp
      ring
    simpa [heq] using h
  have hlogRatio : Tendsto (fun N : ℕ ↦ Complex.log (ratio N)) atTop (nhds 0) := by
    simpa using hratio.clog Complex.one_mem_slitPlane
  apply hlogRatio.congr'
  filter_upwards with N
  have hdenR : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hden : ((N : ℂ) + 1) ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero N
  have hnum : w + (N : ℂ) ≠ 0 := by
    intro hzero
    have hre := congrArg Complex.re hzero
    norm_num at hre
    have hN : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
    linarith
  have hratioNe : ratio N ≠ 0 := div_ne_zero hnum hden
  have hfactor : (((N : ℝ) + 1 : ℝ) : ℂ) * ratio N = w + (N : ℂ) := by
    dsimp [ratio]
    rw [show ((((N : ℝ) + 1 : ℝ) : ℂ)) = (N : ℂ) + 1 by
      apply Complex.ext <;> simp]
    field_simp
  rw [← hfactor, Complex.log_ofReal_mul hdenR hratioNe]
  have hlogCast : ((Real.log ((N : ℝ) + 1) : ℝ) : ℂ) =
      Complex.log ((N : ℂ) + 1) := by
    rw [show (N : ℝ) + 1 = (N + 1 : ℕ) by norm_num,
      show (N : ℂ) + 1 = (N + 1 : ℕ) by norm_num]
    exact Complex.natCast_log
  rw [hlogCast]
  abel_nf

/-- The full complex digamma logarithmic asymptotic after arbitrary fixed right-half-plane
translations. -/
theorem digamma_add_nat_sub_log_add_nat_tendsto
    (w v : ℂ) (hw : 0 < w.re) (hv : 0 < v.re) :
    Tendsto (fun N : ℕ ↦ Complex.digamma (w + N) - Complex.log (v + N))
      atTop (nhds 0) := by
  have hdiff : Tendsto
      (fun N : ℕ ↦ Complex.digamma (w + N) - Complex.digamma ((N : ℂ) + 1))
      atTop (nhds 0) := by
    refine squeeze_zero_norm' ?_
      (tendsto_const_div_atTop_nhds_zero_nat (2 * ‖w - 1‖))
    filter_upwards [eventually_ge_atTop 1,
      (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop (2 * ‖w - 1‖)]
      with N hN hthr
    exact RHTower.digamma_shift_diff_bound hN (by
      simp only [Complex.add_re, Complex.natCast_re]
      exact add_pos_of_pos_of_nonneg hw (Nat.cast_nonneg N)) hthr
  have hnat := RHTower.digamma_natCast_add_one_sub_log_tendsto
  have hlogV := complex_log_add_nat_sub_log_nat_tendsto v hv
  have h := (hdiff.add hnat).sub hlogV
  convert h using 1
  · funext N
    abel_nf
  · abel_nf

/-- The normalized explicit source has the canonical logarithmic constant `gamma` at infinity. -/
theorem explicitDigammaHerglotzSource_sub_log_tendsto (z : ℂ) (hz : 0 < z.re) :
    Tendsto (fun N : ℕ ↦
      explicitDigammaHerglotzSource (z + N) - Complex.log (z + N))
      atTop (nhds (Real.eulerMascheroniConstant : ℂ)) := by
  have hw : 0 < (z + 1 / 2).re := by
    norm_num
    linarith
  have h := digamma_add_nat_sub_log_add_nat_tendsto (z + 1 / 2) z hw hz
  have h' := h.add_const (Real.eulerMascheroniConstant : ℂ)
  convert h' using 1
  · funext N
    simp only [explicitDigammaHerglotzSource]
    rw [show z + (N : ℂ) + 1 / 2 = z + 1 / 2 + (N : ℂ) by abel_nf]
    abel_nf
  · abel_nf

/-- Two right-half-plane solutions of one additive unit-shift cocycle coincide if their
difference tends to zero along every positive integer ray. -/
theorem eqOn_rightHalfPlane_of_same_unitCocycle_and_tendsto_sub_zero
    (f g cocycle : ℂ → ℂ)
    (hf : ∀ z : ℂ, 0 < z.re → f (z + 1) = f z + cocycle z)
    (hg : ∀ z : ℂ, 0 < z.re → g (z + 1) = g z + cocycle z)
    (hlim : ∀ z : ℂ, 0 < z.re →
      Tendsto (fun n : ℕ ↦ f (z + n) - g (z + n)) atTop (nhds 0)) :
    Set.EqOn f g {z : ℂ | 0 < z.re} := by
  intro z hz
  have hconst : ∀ n : ℕ, f (z + n) - g (z + n) = f z - g z := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        have hzn : 0 < (z + (n : ℂ)).re := by
          simpa using add_pos_of_pos_of_nonneg hz (Nat.cast_nonneg n)
        rw [Nat.cast_succ,
          show z + ((n : ℂ) + 1) = (z + (n : ℂ)) + 1 by abel_nf,
          hf _ hzn, hg _ hzn]
        calc
          f (z + n) + cocycle (z + n) - (g (z + n) + cocycle (z + n)) =
              f (z + n) - g (z + n) := by abel_nf
          _ = f z - g z := ih
  have hconstLim :
      Tendsto (fun n : ℕ ↦ f (z + n) - g (z + n)) atTop (nhds (f z - g z)) := by
    simpa only [hconst] using (tendsto_const_nhds :
      Tendsto (fun _ : ℕ ↦ f z - g z) atTop (nhds (f z - g z)))
  have hzsub : f z - g z = 0 := tendsto_nhds_unique hconstLim (hlim z hz)
  exact sub_eq_zero.mp hzsub

/-- Common asymptotic normalization kills the periodic ambiguity between two solutions of the
same unit-shift cocycle. -/
theorem eqOn_rightHalfPlane_of_same_unitCocycle_and_common_asymptotic
    (f g cocycle reference : ℂ → ℂ) (limit : ℂ)
    (hf : ∀ z : ℂ, 0 < z.re → f (z + 1) = f z + cocycle z)
    (hg : ∀ z : ℂ, 0 < z.re → g (z + 1) = g z + cocycle z)
    (hfLim : ∀ z : ℂ, 0 < z.re →
      Tendsto (fun n : ℕ ↦ f (z + n) - reference (z + n)) atTop (nhds limit))
    (hgLim : ∀ z : ℂ, 0 < z.re →
      Tendsto (fun n : ℕ ↦ g (z + n) - reference (z + n)) atTop (nhds limit)) :
    Set.EqOn f g {z : ℂ | 0 < z.re} := by
  apply eqOn_rightHalfPlane_of_same_unitCocycle_and_tendsto_sub_zero f g cocycle hf hg
  intro z hz
  have h := (hfLim z hz).sub (hgLim z hz)
  convert h using 1 <;> abel_nf

/-- **Canonical source selection.**  The explicit digamma Herglotz source is the unique
right-half-plane solution of its half-shifted unit cocycle with logarithmic constant `gamma` at
positive infinity. -/
theorem explicitDigammaHerglotzSource_unique_of_cocycle_and_log_asymptotic
    (f : ℂ → ℂ)
    (hf : ∀ z : ℂ, 0 < z.re →
      f (z + 1) = f z + explicitDigammaSourceCocycle z)
    (hfLim : ∀ z : ℂ, 0 < z.re →
      Tendsto (fun n : ℕ ↦ f (z + n) - Complex.log (z + n))
        atTop (nhds (Real.eulerMascheroniConstant : ℂ))) :
    Set.EqOn f explicitDigammaHerglotzSource {z : ℂ | 0 < z.re} := by
  apply eqOn_rightHalfPlane_of_same_unitCocycle_and_common_asymptotic
    f explicitDigammaHerglotzSource explicitDigammaSourceCocycle Complex.log
    (Real.eulerMascheroniConstant : ℂ) hf
  · intro z hz
    exact explicitDigammaHerglotzSource_add_one hz
  · exact hfLim
  · intro z hz
    exact explicitDigammaHerglotzSource_sub_log_tendsto z hz

end GaloisForLFunctions.HTGeometry
