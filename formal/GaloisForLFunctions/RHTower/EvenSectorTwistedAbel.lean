import GaloisForLFunctions.RHTower.EvenSectorPoleWeightUniqueness
import GaloisForLFunctions.RHTower.WeilWorkExposingRayCriticalTwists
import GaloisForLFunctions.RHTower.WeilWorkPBAPCriticalDensityLaplace

/-!
# All frequency twists from the even pole-free cone

Detuned real packets admit arbitrary signs. Splitting complex coefficients into
real and imaginary parts therefore admits every unitary arithmetic character,
without modulating an even source. Signed Abel integration produces a single
upper ceiling uniform over the entire vertical line. This uniformity is the
input for holomorphic removal of the missing pole direction.
-/

open Complex MeasureTheory Filter Topology Set
open scoped ComplexConjugate

noncomputable section
namespace RHTower.EvenSector
open ExposingRayTransfer WeilWorkPBAP OddSector

/-- Detuned even packets retain the real quadratic form of arbitrary complex
arithmetic coefficients. -/
theorem complex_toeplitz_of_weilPositiveEvenPolar {lam : ℕ → ℝ}
    (h : WeilPositiveEvenPolar lam) {N : ℕ} (hN : 1 ≤ N)
    (c : ℕ → ℂ) (hc : ∀ m, N < m → c m = 0) :
    2 * ∑ n ∈ Finset.Icc 2 N, lam n / Real.sqrt n *
        (∑ m ∈ Finset.Icc 1 N, c (n * m) * conj (c m)).re ≤
      (4 * Real.log N + Detuned.toeplitzConstant) *
        ∑ m ∈ Finset.Icc 1 N, ‖c m‖ ^ 2 := by
  have hr := Detuned.signed_toeplitz h hN (fun m => (c m).re)
    (fun m hm => by simp [hc m hm])
  have hi := Detuned.signed_toeplitz h hN (fun m => (c m).im)
    (fun m hm => by simp [hc m hm])
  have hmass (m : ℕ) : ‖c m‖ ^ 2 = (c m).re ^ 2 + (c m).im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  simp_rw [hmass]
  simpa only [Complex.re_sum, Complex.mul_re, Complex.conj_re, Complex.conj_im,
    mul_neg, sub_neg_eq_add, Finset.sum_add_distrib, mul_add] using add_le_add hr hi

/-- The signed coefficients twisted by a literal real frequency. -/
def evenTwist (lam : ℕ → ℝ) (t : ℝ) (n : ℕ) : ℝ :=
  lam n * Real.cos (t * Real.log n)

private theorem harmonic_twist_ceiling {lam : ℕ → ℝ} (h : WeilPositiveEvenPolar lam) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 1 ≤ N → ∀ t : ℝ,
      harmonicDensity (evenTwist lam t) N ≤ C * (1 + Real.log N) ^ 2 := by
  let C := 4 + |Detuned.toeplitzConstant|
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C, hC, fun N hN t => ?_⟩
  have hu := positive_twisted_harmonic_bound
    (fun c hc => complex_toeplitz_of_weilPositiveEvenPolar h hN c hc)
    (criticalLogTwist t) (fun m n hm hn => criticalLogTwist_mul t hm hn)
    (fun m _ => norm_criticalLogTwist t m)
  simp only [re_criticalLogTwist] at hu
  change 2 * harmonicDensity (evenTwist lam t) N ≤
    (4 * Real.log N + Detuned.toeplitzConstant) *
      ∑ m ∈ Finset.Icc 1 N, (1 : ℝ) / m at hu
  have hlog : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast hN)
  have hsum : 0 ≤ ∑ m ∈ Finset.Icc 1 N, (1 : ℝ) / m :=
    Finset.sum_nonneg fun m _ => by positivity
  have hB : 4 * Real.log N + Detuned.toeplitzConstant ≤ C * (1 + Real.log N) := by
    dsimp [C]
    nlinarith [le_abs_self Detuned.toeplitzConstant,
      mul_nonneg (abs_nonneg Detuned.toeplitzConstant) hlog]
  have h1 := mul_le_mul_of_nonneg_right hB hsum
  have h2 := mul_le_mul_of_nonneg_left (sum_Icc_inv_le_one_add_log N)
    (show 0 ≤ C * (1 + Real.log N) by positivity)
  have hpos : 0 ≤ C * (1 + Real.log (N : ℝ)) ^ 2 := by positivity
  nlinarith only [hu, h1, h2, hpos]

theorem summable_abs_evenTwist {lam : ℕ → ℝ} (h : WeilPositiveEvenPolar lam)
    {σ : ℝ} (hσ : 1 < σ) (t : ℝ) :
    Summable fun n : ℕ => |evenTwist lam t n| / (n : ℝ) ^ σ := by
  refine (summable_abs_div_rpow_of_weilPositiveEvenPolar h hσ).of_nonneg_of_le
    (fun _ => by positivity) fun n => ?_
  apply div_le_div_of_nonneg_right _ (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  dsimp [evenTwist]
  rw [abs_mul]
  exact (mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (abs_nonneg _)).trans_eq
    (mul_one _)

private theorem twisted_terms_summable {lam : ℕ → ℝ} (h : WeilPositiveEvenPolar lam)
    {s : ℝ} (hs : 0 < s) (t : ℝ) :
    Summable fun n : ℕ => ‖(if 2 ≤ n then evenTwist lam t n else 0) /
      (n : ℝ) ^ (1 + s)‖ := by
  refine (summable_abs_evenTwist h (by linarith : 1 < 1 + s) t).of_nonneg_of_le
    (fun _ => norm_nonneg _) fun n => ?_
  rw [Real.norm_eq_abs, abs_div, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)]
  split_ifs
  · exact le_rfl
  · simp only [abs_zero, zero_div]
    positivity

private theorem harmonic_factor_summable {s : ℝ} (hs : 0 < s) :
    Summable fun m : ℕ => (1 : ℝ) / (m : ℝ) ^ (1 + s) := by
  have h : Summable fun m : ℕ => (m : ℝ) ^ (-(1 + s)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  simpa only [Real.rpow_neg (Nat.cast_nonneg _), one_div] using h

private theorem pair_transform_div (lam : ℕ → ℝ) {s : ℝ} (hs : 0 < s) (q : ℕ × ℕ) :
    harmonicPairWeight lam q * Real.exp (-s * harmonicPairLevel q) =
      ((if 2 ≤ q.1 then lam q.1 else 0) / (q.1 : ℝ) ^ (1 + s)) *
        (1 / (q.2 : ℝ) ^ (1 + s)) := by
  rw [harmonicPair_transform lam hs]
  simp only [Real.rpow_neg (Nat.cast_nonneg _), div_eq_mul_inv, one_mul]

private theorem pair_transform_summable {lam : ℕ → ℝ} (h : WeilPositiveEvenPolar lam)
    {s : ℝ} (hs : 0 < s) (t : ℝ) :
    Summable fun q : ℕ × ℕ => |harmonicPairWeight (evenTwist lam t) q| *
      Real.exp (-s * harmonicPairLevel q) := by
  have hn := twisted_terms_summable h hs t
  have hm := (harmonic_factor_summable hs).norm
  have hp := hn.mul_of_nonneg hm (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
  apply hp.congr
  intro q
  have he := congrArg norm (pair_transform_div (evenTwist lam t) hs q)
  simpa only [norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using he.symm

private theorem pair_transform_tsum {lam : ℕ → ℝ} (h : WeilPositiveEvenPolar lam)
    {s : ℝ} (hs : 0 < s) (t : ℝ) :
    (∑' q : ℕ × ℕ, harmonicPairWeight (evenTwist lam t) q *
      Real.exp (-s * harmonicPairLevel q)) =
      oddDirichlet (evenTwist lam t) s * ∑' m : ℕ, (1 : ℝ) / (m : ℝ) ^ (1 + s) := by
  simp_rw [pair_transform_div _ hs]
  exact (tsum_mul_tsum_of_summable_norm (twisted_terms_summable h hs t)
    (harmonic_factor_summable hs).norm).symm

private theorem twisted_dirichlet_product_ceiling {lam : ℕ → ℝ}
    (h : WeilPositiveEvenPolar lam) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ s : ℝ, 0 < s → ∀ t : ℝ,
      s ^ 2 * (oddDirichlet (evenTwist lam t) s *
        ∑' m : ℕ, (1 : ℝ) / (m : ℝ) ^ (1 + s)) ≤ K * (2 + s ^ 2) := by
  obtain ⟨C, hC, hceil⟩ := harmonic_twist_ceiling h
  refine ⟨2 * C, by positivity, fun s hs t => ?_⟩
  have hu : ∀ y : ℝ, 0 ≤ y →
      signedCumulative (harmonicPairWeight (evenTwist lam t)) harmonicPairLevel y ≤
        (2 * C) * y ^ 2 + 2 * C := by
    intro y hy
    rw [signedCumulative_harmonicPair]
    have hN : 1 ≤ ⌊Real.exp y⌋₊ :=
      (Nat.le_floor_iff (Real.exp_pos y).le).mpr (by simpa using Real.one_le_exp_iff.mpr hy)
    have hlog0 : 0 ≤ Real.log (⌊Real.exp y⌋₊ : ℝ) :=
      Real.log_nonneg (by exact_mod_cast hN)
    have hlog : Real.log (⌊Real.exp y⌋₊ : ℝ) ≤ y :=
      (Real.log_le_iff_le_exp (by exact_mod_cast (by omega : 0 < ⌊Real.exp y⌋₊))).mpr
        (Nat.floor_le (Real.exp_pos y).le)
    have hh := hceil ⌊Real.exp y⌋₊ hN t
    have hsq : (1 + Real.log (⌊Real.exp y⌋₊ : ℝ)) ^ 2 ≤ 2 * (y ^ 2 + 1) := by
      nlinarith [sq_nonneg (y - 1)]
    have hm := mul_le_mul_of_nonneg_left hsq hC
    linarith
  have hc := signedCumulative_laplace_ceiling
    (harmonicPairWeight (evenTwist lam t)) harmonicPairLevel hs
    (show 0 ≤ 2 * C by positivity) (show 0 ≤ 2 * C by positivity)
    harmonicPairLevel_nonneg (pair_transform_summable h hs t) hu
  rw [pair_transform_tsum h hs t] at hc
  have hh := mul_le_mul_of_nonneg_left hc (pow_pos hs 3).le
  field_simp [hs.ne'] at hh
  nlinarith only [hh]

private theorem harmonic_factor_residue :
    Tendsto (fun s : ℝ => s * ∑' m : ℕ, (1 : ℝ) / (m : ℝ) ^ (1 + s))
      (𝓝[>] 0) (𝓝 1) := by
  have hx : Tendsto (fun s : ℝ => s) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
  have hshift : Tendsto (fun s : ℝ => 1 + s) (𝓝[>] 0) (𝓝[>] 1) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · simpa only [add_zero] using (tendsto_const_nhds.add hx :
        Tendsto (fun s : ℝ => 1 + s) (𝓝[>] 0) (𝓝 (1 + 0)))
    · filter_upwards [self_mem_nhdsWithin] with s hs
      change 1 < 1 + s
      linarith [show 0 < s from hs]
  simpa only [Function.comp_def, add_sub_cancel_left] using
    tendsto_sub_mul_tsum_nat_rpow.comp hshift

/-- Pole-free even positivity controls all vertical twists on one common
neighborhood. The neighborhood does not depend on frequency. -/
theorem uniform_twisted_abel_ceiling {lam : ℕ → ℝ} (h : WeilPositiveEvenPolar lam) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ᶠ s : ℝ in 𝓝[>] 0, ∀ t : ℝ,
      s * oddDirichlet (evenTwist lam t) s ≤ M := by
  obtain ⟨K, hK, hceil⟩ := twisted_dirichlet_product_ceiling h
  refine ⟨6 * K, by positivity, ?_⟩
  have hlo := harmonic_factor_residue.eventually
    (lt_mem_nhds (show (1 / 2 : ℝ) < 1 by norm_num))
  have hx : Tendsto (fun s : ℝ => s) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
  filter_upwards [hlo, hx.eventually_lt_const (show (0 : ℝ) < 1 by norm_num),
    self_mem_nhdsWithin] with s hsH hs1 hs t
  have hs0 : 0 < s := hs
  have hp := hceil s hs0 t
  have hs2 : s ^ 2 ≤ 1 := by nlinarith
  have hright : K * (2 + s ^ 2) ≤ 3 * K := by nlinarith
  have hp' : (s * oddDirichlet (evenTwist lam t) s) *
      (s * ∑' m : ℕ, (1 : ℝ) / (m : ℝ) ^ (1 + s)) ≤ 3 * K := by
    nlinarith only [hp, hright]
  by_cases hB : s * oddDirichlet (evenTwist lam t) s ≤ 0
  · linarith
  · have hBp : 0 ≤ s * oddDirichlet (evenTwist lam t) s := (lt_of_not_ge hB).le
    have hmul := mul_le_mul_of_nonneg_left hsH.le hBp
    nlinarith only [hp', hmul]

end RHTower.EvenSector
end
