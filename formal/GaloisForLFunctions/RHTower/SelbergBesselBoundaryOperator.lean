import GaloisForLFunctions.RHTower.SelbergBesselAdverseModes
import GaloisForLFunctions.RHTower.SelbergBesselBoundaryEnvelope
import GaloisForLFunctions.HTGeometry.BoundedDiagonalOperatorLp

/-!
# The actual compact correction to the critical cusp boundary form

At period `exp b` and height `exp T`, the critical Bessel response in each nonzero
integer Fourier channel is its physical frequency minus a strictly positive correction.
The source inverse-frequency envelope makes these corrections a compact diagonal operator
on complex square-summable sequences. The zero coefficient is explicitly zero.

The operator is positive and self-adjoint, and its kernel is precisely the constant channel.
The outgoing quadratic form has exactly the principal frequency-weighted domain. On that
domain it equals the principal form minus this actual compact correction, strictly so whenever
any nonzero Fourier channel is present.

This module identifies the sequence-space boundary form. It does not construct an automorphic
trace map, a quotient-core response, or a global Selberg inequality.
-/

open Set Filter Topology
open scoped ComplexOrder
namespace GaloisForLFunctions.RHTower.SelbergBoundaryOperator
open SelbergBesselSlope SelbergBesselModes SelbergBesselEnvelope
open GaloisForLFunctions.HTGeometry.LpDiagonal
noncomputable section

/-- Complex square-summable integer Fourier channels, including the constant channel. -/
abbrev BoundarySpace := LpTwo ℤ

/-- Actual Bessel correction coefficient; the excluded constant coefficient is set to zero. -/
def amplitude (b T : ℝ) (n : ℤ) : ℝ :=
  if n = 0 then 0 else correction (modeLog b n) T

/-- Width-independent operator bound at the chosen height. -/
def uniformBound (T : ℝ) : ℝ := 1 / (2 * Real.exp T)

/-- Constant in the inverse integer-frequency estimate. -/
def tailConstant (b T : ℝ) : ℝ := Real.exp b / (16 * Real.pi * Real.exp T ^ (2 : ℕ))

theorem uniformBound_pos (T : ℝ) : 0 < uniformBound T := by unfold uniformBound; positivity

theorem tailConstant_pos (b T : ℝ) : 0 < tailConstant b T := by unfold tailConstant; positivity

theorem amplitude_nonneg (b T : ℝ) (n : ℤ) : 0 ≤ amplitude b T n := by
  by_cases hn : n = 0
  · simp [amplitude, hn]
  · rw [amplitude, if_neg hn]
    exact (correction_inverse_frequency_bound _ _).1.le

theorem amplitude_pos_iff (b T : ℝ) (n : ℤ) : 0 < amplitude b T n ↔ n ≠ 0 := by
  by_cases hn : n = 0
  · simp [amplitude, hn]
  · rw [amplitude, if_neg hn]
    exact ⟨fun _ => hn, fun _ => (correction_inverse_frequency_bound _ _).1⟩

theorem amplitude_lt_uniform (b T : ℝ) (n : ℤ) : amplitude b T n < uniformBound T := by
  by_cases hn : n = 0
  · simpa only [amplitude, if_pos hn] using uniformBound_pos T
  · rw [amplitude, if_neg hn]
    have h := (outgoing_bounds (modeLog b n) T).1
    unfold correction uniformBound
    linarith

private theorem frequency_natAbs {n : ℤ} (hn : n ≠ 0) (b : ℝ) :
    Real.exp (modeLog b n) = 2 * Real.pi * (n.natAbs : ℝ) / Real.exp b := by
  have h := mode_frequency b ⟨n, hn⟩
  have ha : (n.natAbs : ℝ) = |(n : ℝ)| := by
    rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs]
  simpa only [ha] using h

/-- The actual correction decays strictly faster than this inverse-index envelope. -/
theorem amplitude_index_bound (b T : ℝ) (n : ℤ) :
    (n.natAbs : ℝ) * amplitude b T n < tailConstant b T := by
  by_cases hn : n = 0
  · simp only [hn, Int.natAbs_zero, Nat.cast_zero, zero_mul]
    exact tailConstant_pos b T
  · have hp : 0 < (n.natAbs : ℝ) := by exact_mod_cast Int.natAbs_pos.mpr hn
    have hb := (correction_inverse_frequency_bound (modeLog b n) T).2
    rw [frequency_natAbs hn b] at hb
    rw [amplitude, if_neg hn]
    calc
      _ < (n.natAbs : ℝ) * (1 / (8 * (2 * Real.pi * (n.natAbs : ℝ) / Real.exp b) * Real.exp T ^ (2 : ℕ))) :=
        mul_lt_mul_of_pos_left hb hp
      _ = _ := by
        unfold tailConstant
        field_simp
        ring

/-- The correction coefficients vanish outside finite sets of integer channels. -/
theorem amplitude_tendsto_cofinite (b T : ℝ) : Tendsto (amplitude b T) cofinite (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_gt (tailConstant b T / ε)
  apply Filter.eventually_cofinite.mpr
  apply (Finset.finite_toSet (Finset.Icc (-(N : ℤ)) (N : ℤ))).subset
  intro n hn
  change ¬ dist (amplitude b T n) 0 < ε at hn
  have hbad : ε ≤ amplitude b T n := by
    have hd : dist (amplitude b T n) 0 = amplitude b T n := by
      rw [Real.dist_eq, sub_zero, abs_of_nonneg (amplitude_nonneg b T n)]
    simpa only [hd, not_lt] using hn
  have hmul := (div_lt_iff₀ hε).mp hN
  have hidx := amplitude_index_bound b T n
  have hge := mul_le_mul_of_nonneg_left hbad (Nat.cast_nonneg n.natAbs : (0 : ℝ) ≤ n.natAbs)
  have hlt : (n.natAbs : ℝ) < N := by nlinarith
  have hnN : n.natAbs ≤ N := by exact_mod_cast hlt.le
  have habs : |n| ≤ (N : ℤ) := by rw [← Int.natCast_natAbs]; exact_mod_cast hnN
  exact Finset.mem_Icc.mpr (abs_le.mp habs)

theorem norm_amplitude (b T : ℝ) (n : ℤ) : ‖(amplitude b T n : ℂ)‖ = amplitude b T n := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (amplitude_nonneg b T n)]

/-- The literal Bessel correction as a bounded diagonal operator on complex ℓ². -/
def operator (b T : ℝ) : BoundarySpace →L[ℂ] BoundarySpace :=
  lpDiag (fun n => (amplitude b T n : ℂ)) (uniformBound T) (uniformBound_pos T).le
    (fun n => by rw [norm_amplitude]; exact (amplitude_lt_uniform b T n).le)

theorem operator_apply (b T : ℝ) (u : BoundarySpace) (n : ℤ) :
    operator b T u n = (amplitude b T n : ℂ) * u n := rfl

theorem operator_norm_le (b T : ℝ) : ‖operator b T‖ ≤ uniformBound T := norm_lpDiag_le _ _ _ _

/-- Inverse-index decay makes the actual correction operator compact. -/
theorem operator_compact (b T : ℝ) : IsCompactOperator (operator b T) := by
  apply isCompactOperator_lpDiag
  simpa only [norm_amplitude] using amplitude_tendsto_cofinite b T

theorem operator_symmetric (b T : ℝ) : (operator b T).toLinearMap.IsSymmetric := by
  intro u v
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  apply tsum_congr
  intro n
  simp only [ContinuousLinearMap.coe_coe, operator_apply, RCLike.inner_apply,
    map_mul, Complex.conj_ofReal]
  ring

/-- The correction is self-adjoint because each coefficient is real. -/
theorem operator_selfAdjoint (b T : ℝ) : IsSelfAdjoint (operator b T) :=
  ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr (operator_symmetric b T)

private theorem inner_term (b T : ℝ) (u : BoundarySpace) (n : ℤ) :
    inner ℂ (operator b T u n) (u n) =
      ((amplitude b T n * Complex.normSq (u n) : ℝ) : ℂ) := by
  simp only [operator_apply, RCLike.inner_apply, map_mul, Complex.conj_ofReal,
    Complex.ofReal_mul]
  rw [← Complex.mul_conj]
  ring

/-- Its real quadratic response is the absolutely convergent positive modal sum. -/
theorem quadratic_response (b T : ℝ) (u : BoundarySpace) :
    (inner ℂ (operator b T u) u).re = ∑' n : ℤ, amplitude b T n * Complex.normSq (u n) := by
  rw [lp.inner_eq_tsum, Complex.re_tsum (lp.summable_inner _ _)]
  apply tsum_congr
  intro n
  rw [inner_term, Complex.ofReal_re]

/-- Correction energy is summable for every square-summable boundary vector. -/
theorem quadratic_summable (b T : ℝ) (u : BoundarySpace) :
    Summable (fun n : ℤ => amplitude b T n * Complex.normSq (u n)) := by
  have hs := (lp.summable_inner (operator b T u) u).hasSum.mapL Complex.reCLM
  have he : (fun n : ℤ => (inner ℂ (operator b T u n) (u n)).re) =
      fun n => amplitude b T n * Complex.normSq (u n) := by
    funext n
    rw [inner_term, Complex.ofReal_re]
  change HasSum (fun n : ℤ => (inner ℂ (operator b T u n) (u n)).re) _ at hs
  rw [he] at hs
  exact hs.summable

/-- The actual diagonal correction is a positive operator. -/
theorem operator_positive (b T : ℝ) : (operator b T).IsPositive := by
  refine ⟨operator_symmetric b T, ?_⟩
  intro u
  change (0 : ℝ) ≤ (inner ℂ (operator b T u) u).re
  rw [quadratic_response]
  exact tsum_nonneg (fun n => mul_nonneg (amplitude_nonneg b T n) (Complex.normSq_nonneg _))

/-- The only vectors killed by the correction are supported on the constant channel. -/
theorem operator_kernel_iff (b T : ℝ) (u : BoundarySpace) :
    operator b T u = 0 ↔ ∀ n : ℤ, n ≠ 0 → u n = 0 := by
  constructor
  · intro hu n hn
    have he := congrArg (fun v : BoundarySpace => v n) hu
    rw [operator_apply] at he
    have ha : (amplitude b T n : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr ((amplitude_pos_iff b T n).mpr hn).ne'
    exact (mul_eq_zero.mp he).resolve_left ha
  · intro hu
    apply lp.ext
    funext n
    rw [operator_apply]
    by_cases hn : n = 0
    · simp [amplitude, hn]
    · simp [hu n hn]

/-- Zero correction energy is equivalent to absence of every nonconstant coefficient. -/
theorem quadratic_zero_iff (b T : ℝ) (u : BoundarySpace) :
    (inner ℂ (operator b T u) u).re = 0 ↔ ∀ n : ℤ, n ≠ 0 → u n = 0 := by
  rw [quadratic_response]
  constructor
  · intro h n hn
    have ht := (quadratic_summable b T u).le_tsum n
      (fun j _ => mul_nonneg (amplitude_nonneg b T j) (Complex.normSq_nonneg _))
    rw [h] at ht
    have hz : amplitude b T n * Complex.normSq (u n) = 0 :=
      le_antisymm ht (mul_nonneg (amplitude_nonneg b T n) (Complex.normSq_nonneg _))
    exact Complex.normSq_eq_zero.mp
      ((mul_eq_zero.mp hz).resolve_left ((amplitude_pos_iff b T n).mpr hn).ne')
  · intro h
    have hz : (fun n : ℤ => amplitude b T n * Complex.normSq (u n)) = fun _ : ℤ => 0 := by
      funext n
      by_cases hn : n = 0
      · simp [amplitude, hn]
      · simp [h n hn]
    rw [hz]
    exact tsum_zero

/-- Every vector with a nonconstant coefficient has strictly positive correction energy. -/
theorem quadratic_pos_iff (b T : ℝ) (u : BoundarySpace) :
    0 < (inner ℂ (operator b T u) u).re ↔ ∃ n : ℤ, n ≠ 0 ∧ u n ≠ 0 := by
  constructor
  · intro hp
    by_contra h
    have hz : ∀ n : ℤ, n ≠ 0 → u n = 0 := by
      intro n hn
      by_contra hu
      exact h ⟨n, hn, hu⟩
    exact hp.ne' ((quadratic_zero_iff b T u).mpr hz)
  · rintro ⟨n, hn, hu⟩
    rw [quadratic_response]
    exact lt_of_lt_of_le
      (mul_pos ((amplitude_pos_iff b T n).mpr hn) (Complex.normSq_pos.mpr hu))
      ((quadratic_summable b T u).le_tsum n
        (fun j _ => mul_nonneg (amplitude_nonneg b T j) (Complex.normSq_nonneg _)))

/-- Physical frequency, with its actual zero value on the constant channel. -/
def frequency (b : ℝ) (n : ℤ) : ℝ := 2 * Real.pi * (n.natAbs : ℝ) / Real.exp b

theorem seam_eq_frequency_sub (b T : ℝ) (n : ℤ) :
    seam b T n = frequency b n - amplitude b T n := by
  by_cases hn : n = 0
  · simp [seam, frequency, amplitude, hn]
  · rw [seam, amplitude, if_neg hn, if_neg hn, correction, frequency_natAbs hn b]
    unfold frequency
    ring

/-- The true outgoing form has exactly the principal frequency-weighted domain. -/
theorem seam_summable_iff (b T : ℝ) (u : BoundarySpace) :
    Summable (fun n : ℤ => seam b T n * Complex.normSq (u n)) ↔
      Summable (fun n : ℤ => frequency b n * Complex.normSq (u n)) := by
  constructor
  · intro h
    apply (h.add (quadratic_summable b T u)).congr
    intro n
    rw [seam_eq_frequency_sub]
    ring
  · intro h
    apply (h.sub (quadratic_summable b T u)).congr
    intro n
    rw [seam_eq_frequency_sub]
    ring

/-- Actual domain of finite principal boundary energy. -/
def FormDomain (b : ℝ) :=
  {u : BoundarySpace // Summable (fun n : ℤ => frequency b n * Complex.normSq (u n))}

/-- The principal frequency energy on its actual summability domain. -/
def principalForm (b : ℝ) (u : FormDomain b) : ℝ :=
  ∑' n : ℤ, frequency b n * Complex.normSq (u.val n)

/-- The outgoing Bessel quadratic form on the same domain. -/
def boundaryForm (b T : ℝ) (u : FormDomain b) : ℝ :=
  ∑' n : ℤ, seam b T n * Complex.normSq (u.val n)

/-- The outgoing boundary form is the frequency form minus the actual compact correction. -/
theorem boundary_form_decomposition (b T : ℝ) (u : FormDomain b) :
    boundaryForm b T u = principalForm b u - (inner ℂ (operator b T u.val) u.val).re := by
  rw [quadratic_response, boundaryForm, principalForm, ← u.property.tsum_sub (quadratic_summable b T u.val)]
  apply tsum_congr
  intro n
  rw [seam_eq_frequency_sub]
  ring

theorem boundary_form_le_principal (b T : ℝ) (u : FormDomain b) :
    boundaryForm b T u ≤ principalForm b u := by
  rw [boundary_form_decomposition, sub_le_self_iff, quadratic_response]
  exact tsum_nonneg (fun n => mul_nonneg (amplitude_nonneg b T n) (Complex.normSq_nonneg _))

/-- Equality occurs precisely on the constant channel. -/
theorem boundary_form_eq_principal_iff (b T : ℝ) (u : FormDomain b) :
    boundaryForm b T u = principalForm b u ↔ ∀ n : ℤ, n ≠ 0 → u.val n = 0 := by
  rw [boundary_form_decomposition, sub_eq_self, quadratic_zero_iff]

end
end GaloisForLFunctions.RHTower.SelbergBoundaryOperator
