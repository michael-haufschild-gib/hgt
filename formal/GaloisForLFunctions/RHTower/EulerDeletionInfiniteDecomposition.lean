import GaloisForLFunctions.RHTower.EulerDeletionMixedDecompositionFinite
import Mathlib.NumberTheory.Harmonic.EulerMascheroni

/-!
# Infinite decomposition of the actual mixed Euler-deletion source

For `1/2 ≤ Re s < 1` and positive integer `p`, the ordinary ordered mixed
prefix converges to the quadratic dilation term, the zero-dependent amplitude,
the full boundary term, and the difference of two absolutely convergent arithmetic
remainder series. At the critical line the boundary term is `-log p / 2`.

Complete-cell convergence is extended to every ordinary cutoff. No infinite
mixed sum is represented by an unordered `tsum`; only the absolutely convergent
remainder uses that operation. This theorem supplies no arithmetic vanishing law
or RH implication.
-/

noncomputable section
open scoped BigOperators
open MeasureTheory Set Filter Topology
namespace RHTower.DeletionMixedRefinement

private theorem tendsto_dilate_nat {p : ℕ} (hp : 0 < p) :
    Tendsto (fun N : ℕ => p * N) atTop atTop := by
  apply tendsto_atTop_mono (f := fun N : ℕ => N) _ tendsto_id
  intro N
  simpa using Nat.mul_le_mul_right N (show 1 ≤ p by omega)

/-- Every complete-cell centered endpoint tends to zero. -/
theorem tendsto_centeredTail_blocks {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1)
    {p : ℕ} (hp : 0 < p) :
    Tendsto (fun N : ℕ => centeredTail s (riemannZeta s) p (p * N)) atTop (𝓝 0) := by
  have hr := tendsto_powerSumRemainder (by linarith : -1 < s.re) hs1
  have hk : Tendsto (kernel s) atTop (𝓝 0) :=
    tendsto_nat_cpow_zero (by simpa using neg_neg_of_pos hs)
  have h := (((hk.const_mul (kernel s p - amplitude s p)).div_const 2).add
    (hr.comp (tendsto_dilate_nat hp))).sub (hr.const_mul (amplitude s p))
  simp only [mul_zero, zero_div, zero_add, sub_zero] at h
  exact h.congr (fun N => (centeredTail_block s hp N).symm)

/-- The terminal error vanishes on the whole positive half-plane, including the critical line. -/
theorem tendsto_endpointError {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1)
    {p : ℕ} (hp : 0 < p) :
    Tendsto (endpointError s p) atTop (𝓝 0) := by
  have hr := tendsto_powerSumRemainder (by linarith : -1 < s.re) hs1
  have hk : Tendsto (kernel s) atTop (𝓝 0) :=
    tendsto_nat_cpow_zero (by simpa using neg_neg_of_pos hs)
  have hw := tendsto_powerSumRemainder_mul_cpow (s := s) (z := 1 - star s)
    (by linarith) hs1 (by simp; linarith)
  have hfirst := (tendsto_centeredTail_blocks hs hs1 hp).mul
    (((hk.comp (tendsto_dilate_nat hp)).star.div_const 2).add
      ((hr.comp (tendsto_dilate_nat hp)).star))
  have hsecond : Tendsto (fun N : ℕ => powerSumRemainder s (p * N) *
      star (powerMain s (p * N))) atTop (𝓝 0) := by
    have h := (hw.comp (tendsto_dilate_nat hp)).div_const (1 - star s)
    simp only [zero_div] at h
    exact h.congr (fun N => by
      simp only [Function.comp_apply]
      rw [star_powerMain, powerMain]
      ring)
  have hthird : Tendsto (fun N : ℕ => amplitude s p * powerSumRemainder s N *
      star (powerMain s (p * N))) atTop (𝓝 0) := by
    have h := (hw.const_mul (amplitude s p * star (amplitude s p))).div_const (1 - star s)
    simpa only [mul_zero, zero_div] using h.congr (fun N => by
      rw [powerMain_mul s hp, star_mul, star_powerMain, powerMain]; ring)
  have h := (hfirst.add hsecond).sub hthird
  simp only [zero_mul, add_zero, sub_zero] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with N hN
  exact (endpointError_decomposition s hp (by omega)).symm

/-- The power-sum difference has its asserted constant limit without discarding a half endpoint. -/
theorem tendsto_renormalizedPowerDifference {s : ℂ}
    (hs : (1 / 2 : ℝ) ≤ s.re) (hs' : s.re < 1) {p : ℕ} (hp : 0 < p) :
    Tendsto (renormalizedPowerDifference s p) atTop
      (𝓝 ((quadraticPower s p - 1) * riemannZeta (diagonalExponent s - 1))) := by
  have hq : -1 < (diagonalExponent s - 1).re := by
    simp only [diagonalExponent, Complex.sub_re, Complex.add_re, Complex.star_def, Complex.conj_re, Complex.one_re]
    linarith
  have hq1 : diagonalExponent s - 1 ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    simp only [diagonalExponent, Complex.sub_re, Complex.add_re, Complex.star_def, Complex.conj_re,
      Complex.one_re] at this
    linarith
  have hr := tendsto_powerSumRemainder hq hq1
  have h := ((hr.const_mul (quadraticPower s p)).const_add
    ((quadraticPower s p - 1) * riemannZeta (diagonalExponent s - 1))).sub
      (hr.comp (tendsto_dilate_nat hp))
  simp only [mul_zero, add_zero, sub_zero] at h
  exact h.congr (fun N => (renormalizedPowerDifference_decomposition s hp N).symm)

/-- The retained boundary term has a logarithmic critical branch. -/
def infiniteBoundary (s : ℂ) (p : ℕ) : ℂ :=
  if s.re = 1 / 2 then -(Real.log (p : ℝ) : ℂ) / 2
  else (boundaryPower s p - 1) * riemannZeta (diagonalExponent s) / 2

private theorem rawPrefix_one_eq_harmonic (N : ℕ) :
    rawPrefix 1 N = ((harmonic N : ℝ) : ℂ) := by
  simp [rawPrefix, kernel, harmonic, Complex.cpow_neg_one]

private theorem tendsto_harmonic_dilation {p : ℕ} (hp : 0 < p) :
    Tendsto (fun N : ℕ => rawPrefix 1 N - rawPrefix 1 (p * N)) atTop
      (𝓝 (-(Real.log (p : ℝ) : ℂ))) := by
  have h : Tendsto (fun N : ℕ => rawPrefix 1 N - (Real.log (N : ℝ) : ℂ)) atTop
      (𝓝 (Real.eulerMascheroniConstant : ℂ)) := by
    simpa only [rawPrefix_one_eq_harmonic, Complex.ofReal_sub] using
      Real.tendsto_harmonic_sub_log.ofReal
  have h' := (h.sub (h.comp (tendsto_dilate_nat hp))).sub_const (Real.log (p : ℝ) : ℂ)
  simp only [sub_self, zero_sub] at h'
  apply h'.congr'
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hp' : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  simp only [Function.comp_apply, Nat.cast_mul, Real.log_mul hp' hN', Complex.ofReal_add]
  ring

/-- The boundary power-sum difference converges, with its critical logarithm retained. -/
theorem tendsto_boundaryDifference {s : ℂ} (hs : (1 / 2 : ℝ) ≤ s.re)
    {p : ℕ} (hp : 0 < p) :
    Tendsto (fun N : ℕ => (boundaryPower s p * rawPrefix (diagonalExponent s) N -
      rawPrefix (diagonalExponent s) (p * N)) / 2) atTop (𝓝 (infiniteBoundary s p)) := by
  by_cases hc : s.re = 1 / 2
  · have ha : diagonalExponent s = 1 := by
      apply Complex.ext
      · simp [diagonalExponent]
        linarith
      · simp [diagonalExponent]
    simpa only [infiniteBoundary, if_pos hc, boundaryPower, ha, sub_self,
      Complex.cpow_zero, one_mul] using (tendsto_harmonic_dilation hp).div_const 2
  · have ha : 1 < (diagonalExponent s).re := by
      simp only [diagonalExponent, Complex.add_re, Complex.star_def, Complex.conj_re]
      have := lt_of_le_of_ne hs (Ne.symm hc)
      linarith
    have h := (((tendsto_rawPrefix ha).const_mul (boundaryPower s p)).sub
      ((tendsto_rawPrefix ha).comp (tendsto_dilate_nat hp))).div_const 2
    have he : infiniteBoundary s p =
        (boundaryPower s p * riemannZeta (diagonalExponent s) -
          riemannZeta (diagonalExponent s)) / 2 := by
      rw [infiniteBoundary, if_neg hc]
      ring
    rw [he]
    exact h

/-- The exact infinite mixed-source decomposition, before identifying its ordered limit. -/
def infiniteDecomposition (s : ℂ) (p : ℕ) : ℂ :=
  (amplitude s p - 1) * (Complex.normSq (riemannZeta s) : ℂ) +
    riemannZeta (diagonalExponent s - 1) / (1 - star s) * (quadraticPower s p - 1) +
    infiniteBoundary s p + infiniteRemainder s p - infiniteRemainder s 1

/-- Complete-cell cutoffs converge to the full arithmetic decomposition in both chambers. -/
theorem tendsto_mixedPrefix_blocks {s : ℂ}
    (hs : (1 / 2 : ℝ) ≤ s.re) (hs' : s.re < 1) {p : ℕ} (hp : 0 < p) :
    Tendsto (fun N : ℕ => mixedPrefix s (riemannZeta s) p (p * N)) atTop
      (𝓝 (infiniteDecomposition s p)) := by
  have hs0 : 0 < s.re := by linarith
  have hs1 : s ≠ 1 := by intro h; simp [h] at hs'
  have hA := ((tendsto_renormalizedPowerDifference hs hs' hp).div_const (1 - star s)).const_add
    ((amplitude s p - 1) * (riemannZeta s * star (riemannZeta s)))
  have hB := (hA.add (tendsto_boundaryDifference hs hp)).add (tendsto_remainderPrefix hs0 hs1 hp)
  have hC := hB.sub ((tendsto_remainderPrefix hs0 hs1 (p := 1) (by omega)).comp (tendsto_dilate_nat hp))
  have h := hC.add (tendsto_endpointError hs0 hs1 hp)
  have hz : riemannZeta s * star (riemannZeta s) = (Complex.normSq (riemannZeta s) : ℂ) := by
    simpa only [Complex.star_def] using Complex.mul_conj (riemannZeta s)
  rw [add_zero, hz] at h
  convert h using 1
  · ext N
    simpa only [Function.comp_apply, hz] using mixedPrefix_decomposition_with_error s hp N
  · unfold infiniteDecomposition
    congr 1
    ring

private theorem tendsto_of_dilated_residues {f : ℕ → ℂ} {L : ℂ} {p : ℕ} (hp : 0 < p)
    (h : ∀ r < p, Tendsto (fun N : ℕ => f (p * N + r)) atTop (𝓝 L)) :
    Tendsto f atTop (𝓝 L) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have he : ∀ᶠ N : ℕ in atTop, ∀ r ∈ Finset.range p, dist (f (p * N + r)) L < ε := by
    rw [eventually_all_finset]
    intro r hr
    exact eventually_atTop.2 ((Metric.tendsto_atTop.1 (h r (Finset.mem_range.1 hr))) ε hε)
  obtain ⟨N, hN⟩ := eventually_atTop.1 he
  refine ⟨p * N, fun n hn => ?_⟩
  have hdiv : N ≤ n / p := (Nat.le_div_iff_mul_le hp).2 (by simpa [Nat.mul_comm] using hn)
  have hmod := hN (n / p) hdiv (n % p) (Finset.mem_range.2 (Nat.mod_lt n hp))
  simpa only [Nat.div_add_mod] using hmod

private theorem centeredTail_residue (s : ℂ) {p : ℕ} (hp : 0 < p)
    (N r : ℕ) (hr : r < p) :
    centeredTail s (riemannZeta s) p (p * N + r) =
      centeredTail s (riemannZeta s) p (p * N) +
        ∑ j ∈ Finset.range r, kernel s (p * N + j + 1) := by
  simp only [centeredTail, Nat.mul_add_div hp, Nat.div_eq_of_lt hr, Nat.add_zero,
    Nat.mul_div_cancel_left N hp, rawPrefix, Finset.sum_range_add]
  ring

private theorem tendsto_kernel_residue {s : ℂ} (hs : 0 < s.re)
    {p : ℕ} (hp : 0 < p) (r : ℕ) :
    Tendsto (fun N : ℕ => kernel s (p * N + r + 1)) atTop (𝓝 0) := by
  have hk : Tendsto (kernel s) atTop (𝓝 0) :=
    tendsto_nat_cpow_zero (by simpa using neg_neg_of_pos hs)
  exact (hk.comp ((tendsto_add_atTop_nat (r + 1)).comp (tendsto_dilate_nat hp))).congr
    (fun N => by simp only [Function.comp_apply, Nat.add_assoc])

private theorem tendsto_centeredTail_residue {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1)
    {p : ℕ} (hp : 0 < p) (r : ℕ) (hr : r < p) :
    Tendsto (fun N : ℕ => centeredTail s (riemannZeta s) p (p * N + r)) atTop (𝓝 0) := by
  have hsum := tendsto_finsetSum (Finset.range r) (fun j _ => tendsto_kernel_residue hs hp j)
  simp only [Finset.sum_const_zero] at hsum
  have h := (tendsto_centeredTail_blocks hs hs1 hp).add hsum
  simp only [zero_add] at h
  exact h.congr (fun N => (centeredTail_residue s hp N r hr).symm)

/-- Every ordinary cutoff converges; incomplete final cells vanish also on the critical line. -/
theorem tendsto_mixedPrefix {s : ℂ}
    (hs : (1 / 2 : ℝ) ≤ s.re) (hs' : s.re < 1) {p : ℕ} (hp : 0 < p) :
    Tendsto (mixedPrefix s (riemannZeta s) p) atTop (𝓝 (infiniteDecomposition s p)) := by
  have hs0 : 0 < s.re := by linarith
  have hs1 : s ≠ 1 := by intro h; simp [h] at hs'
  apply tendsto_of_dilated_residues hp
  intro r hr
  have hsum : Tendsto (fun N : ℕ => ∑ j ∈ Finset.range r,
      centeredTail s (riemannZeta s) p (p * N + j) * star (kernel s (p * N + j + 1)))
      atTop (𝓝 0) := by
    have h := tendsto_finsetSum (Finset.range r) (fun j hj =>
      (tendsto_centeredTail_residue hs0 hs1 hp j ((Finset.mem_range.1 hj).trans hr)).mul
        (tendsto_kernel_residue hs0 hp j).star)
    simpa only [zero_mul, Finset.sum_const_zero] using h
  have h := (tendsto_mixedPrefix_blocks hs hs' hp).add hsum
  simp only [add_zero] at h
  apply h.congr
  intro N
  simp only [mixedPrefix, Finset.sum_range_add]

/-- Mixed-source sum selected by ordinary chronological cutoffs, including conditional convergence. -/
def infiniteMixed (s : ℂ) (p : ℕ) : ℂ :=
  limUnder atTop (mixedPrefix s (riemannZeta s) p)

/-- The infinite decomposition is an equality of the actual ordered limit and actual remainder series. -/
theorem infiniteMixed_eq_decomposition {s : ℂ}
    (hs : (1 / 2 : ℝ) ≤ s.re) (hs' : s.re < 1) {p : ℕ} (hp : 0 < p) :
    infiniteMixed s p =
      (amplitude s p - 1) * (Complex.normSq (riemannZeta s) : ℂ) +
        riemannZeta (diagonalExponent s - 1) / (1 - star s) * (quadraticPower s p - 1) +
        infiniteBoundary s p + infiniteRemainder s p - infiniteRemainder s 1 :=
  (tendsto_mixedPrefix hs hs' hp).limUnder_eq

/-- The remainder series is literally the series at the conjugate exponent appearing in the paper. -/
theorem infiniteRemainder_eq_conjugate_exponent {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) (p : ℕ) :
    infiniteRemainder s p = amplitude s p * ∑' n : ℕ,
      kernel s (n + 1) * powerSumRemainder (star s) (p * (n + 1)) := by
  simp only [infiniteRemainder, powerSumRemainder_star (by linarith : -1 < s.re) hs1]

/-- The diagonal exponent is twice the real part, with no hidden imaginary component. -/
theorem diagonalExponent_eq (s : ℂ) : diagonalExponent s = ((2 * s.re : ℝ) : ℂ) := by
  apply Complex.ext
  · simp [diagonalExponent]
    ring
  · simp [diagonalExponent]

/-- Unit deletion has zero ordered infinite mixed source at every exponent. -/
theorem infiniteMixed_one (s : ℂ) : infiniteMixed s 1 = 0 := by
  apply Filter.Tendsto.limUnder_eq
  have h : Tendsto (fun _ : ℕ => (0 : ℂ)) atTop (𝓝 0) := tendsto_const_nhds
  exact h.congr (fun N => (mixedPrefix_one s (riemannZeta s) N).symm)

/-- Strict-right branch of the infinite decomposition, with the full boundary constant retained. -/
theorem infiniteMixed_eq_strict {s : ℂ}
    (hs : (1 / 2 : ℝ) < s.re) (hs' : s.re < 1) {p : ℕ} (hp : 0 < p) :
    infiniteMixed s p =
      (amplitude s p - 1) * (Complex.normSq (riemannZeta s) : ℂ) +
        riemannZeta (diagonalExponent s - 1) / (1 - star s) * (quadraticPower s p - 1) +
        (boundaryPower s p - 1) * riemannZeta (diagonalExponent s) / 2 +
        infiniteRemainder s p - infiniteRemainder s 1 := by
  rw [infiniteMixed_eq_decomposition hs.le hs' hp, infiniteBoundary, if_neg hs.ne']

/-- Critical branch: the half endpoints give a logarithm rather than a zeta value at the pole. -/
theorem infiniteMixed_eq_critical {s : ℂ} (hs : s.re = (1 / 2 : ℝ))
    {p : ℕ} (hp : 0 < p) :
    infiniteMixed s p =
      (amplitude s p - 1) * (Complex.normSq (riemannZeta s) : ℂ) +
        (-1 / 2 : ℂ) / (1 - star s) * ((p : ℂ) - 1) - (Real.log (p : ℝ) : ℂ) / 2 +
        infiniteRemainder s p - infiniteRemainder s 1 := by
  have hd : diagonalExponent s = 1 := by rw [diagonalExponent_eq, hs]; norm_num
  rw [infiniteMixed_eq_decomposition (by linarith) (by linarith) hp,
    infiniteBoundary, if_pos hs, quadraticPower, hd]
  norm_num only [sub_self, show (2 : ℂ) - 1 = 1 by ring, Complex.cpow_one,
    RHTower.riemannZeta_zero_of_centred]
  ring

end RHTower.DeletionMixedRefinement
