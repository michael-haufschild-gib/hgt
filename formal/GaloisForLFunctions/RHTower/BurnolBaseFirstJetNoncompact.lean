import GaloisForLFunctions.RHTower.BurnolBaseFirstJetAdmission

/-!
# Noncompactness of the native Burnol first jet

Normalized prime packets escape along disjoint Mertens shells but retain a positive amount of
first-jet energy. Thus the bounded critical prime synthesis is noncompact. The obstruction is
off-diagonal and stronger than divergence of the sum of column energies.
-/

open Filter Topology
open scoped InnerProductSpace ComplexConjugate

namespace RHTower
open GaloisForLFunctions.HTGeometry
noncomputable section

theorem burnolBaseFirstJetPrimeKernel_eq_correlation_cube (p q : Nat.Primes) :
    burnolBaseFirstJetPrimeKernel p q =
      burnolPrimeClockCorrelation p q ^ 3 / (4 * Real.sqrt (p : ℝ) * Real.sqrt (q : ℝ)) := by
  have hcube (r : Nat.Primes) : Real.sqrt (stcClock r) ^ 3 =
      stcClock r * Real.sqrt (stcClock r) := by
    rw [pow_succ, Real.sq_sqrt (stcClock_pos' r).le]
  unfold burnolBaseFirstJetPrimeKernel stcPrimePoissonKernel burnolPrimeClockCorrelation
  simp only [mul_pow, hcube, div_eq_mul_inv, mul_inv_rev, ← inv_pow]
  ring

/-- Within one Mertens shell the normalized clock correlation stays uniformly positive. -/
theorem exp_neg_one_le_burnolPrimeClockCorrelation {n : ℕ} {p q : Nat.Primes}
    (hp : p ∈ mertensShell n) (hq : q ∈ mertensShell n) :
    Real.exp (-1) ≤ burnolPrimeClockCorrelation p q := by
  have hp' := mem_mertensShell.mp hp
  have hq' := mem_mertensShell.mp hq
  have hpa : Real.exp (n : ℝ) ≤ stcClock p := by
    exact (Real.le_log_iff_exp_le (stcClock_pos' p)).mp hp'.1
  have hqa : Real.exp (n : ℝ) ≤ stcClock q := by
    exact (Real.le_log_iff_exp_le (stcClock_pos' q)).mp hq'.1
  have hpb : stcClock p ≤ Real.exp ((n : ℝ) + 1) :=
    ((Real.log_lt_iff_lt_exp (stcClock_pos' p)).mp hp'.2).le
  have hqb : stcClock q ≤ Real.exp ((n : ℝ) + 1) :=
    ((Real.log_lt_iff_lt_exp (stcClock_pos' q)).mp hq'.2).le
  have hsqrt : Real.exp (n : ℝ) ≤ Real.sqrt (stcClock p) * Real.sqrt (stcClock q) := by
    have hm := mul_le_mul (Real.sqrt_le_sqrt hpa) (Real.sqrt_le_sqrt hqa)
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    simpa only [← sq, Real.sq_sqrt (Real.exp_pos (n : ℝ)).le] using hm
  have hscale : Real.exp (-1) * Real.exp ((n : ℝ) + 1) = Real.exp (n : ℝ) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hsum := mul_le_mul_of_nonneg_left (add_le_add hpb hqb) (Real.exp_pos (-1)).le
  rw [burnolPrimeClockCorrelation, le_div_iff₀ (add_pos (stcClock_pos' p) (stcClock_pos' q))]
  nlinarith

/-- Positive packet energy persists uniformly along every late prime shell. -/
theorem burnolBaseFirstJetPrimeKernel_shell_lower {n : ℕ} {p q : Nat.Primes}
    (hp : p ∈ mertensShell n) (hq : q ∈ mertensShell n) :
    Real.exp (-1) ^ 3 / 4 / (Real.sqrt (p : ℝ) * Real.sqrt (q : ℝ)) ≤
      burnolBaseFirstJetPrimeKernel p q := by
  rw [burnolBaseFirstJetPrimeKernel_eq_correlation_cube]
  have hpow := pow_le_pow_left₀ (Real.exp_pos (-1)).le
    (exp_neg_one_le_burnolPrimeClockCorrelation hp hq) 3
  have hden : 0 ≤ 4 * Real.sqrt (p : ℝ) * Real.sqrt (q : ℝ) := by positivity
  have h := div_le_div_of_nonneg_right hpow hden
  simpa only [div_div, mul_assoc] using h

private def burnolFirstJetPrimeGram :
    lp (fun _ : Nat.Primes => ℂ) 2 →L[ℂ] lp (fun _ : Nat.Primes => ℂ) 2 :=
  burnolBaseFirstJetPrimeSynthesis.adjoint ∘L burnolBaseFirstJetPrimeSynthesis

private theorem hasLpMatrix_burnolFirstJetPrimeGram :
    HasLpMatrix burnolFirstJetPrimeGram fun p q => (burnolBaseFirstJetPrimeKernel p q : ℂ) := by
  intro p q
  rw [coord_eq_inner, burnolFirstJetPrimeGram, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_right]
  simp only [lpBasisVec, burnolBaseFirstJetPrimeSynthesis_single, one_smul]
  exact inner_burnolBaseFirstJetField_prime p q

theorem norm_sq_burnolBaseFirstJetPrimeSynthesis_shell_lower {n : ℕ}
    (hn : 0 < mertensShellMass n) :
    Real.exp (-1) ^ 3 / 4 * mertensShellMass n ≤
      ‖burnolBaseFirstJetPrimeSynthesis (mertensShellVec n)‖ ^ 2 := by
  let δ : ℝ := Real.exp (-1) ^ 3 / 4
  have henergy : ‖burnolBaseFirstJetPrimeSynthesis (mertensShellVec n)‖ ^ 2 =
      ∑ p ∈ mertensShell n, ∑ q ∈ mertensShell n,
        shellCoeff n p * shellCoeff n q * burnolBaseFirstJetPrimeKernel p q := by
    rw [norm_sq_eq_re_inner (𝕜 := ℂ), ← ContinuousLinearMap.adjoint_inner_right]
    change (inner ℂ (mertensShellVec n) (burnolFirstJetPrimeGram (mertensShellVec n))).re = _
    rw [inner_mertensShellVec hasLpMatrix_burnolFirstJetPrimeGram]
    simp only [Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, sub_zero]
  rw [henergy]
  calc
    δ * mertensShellMass n =
        δ * (∑ p ∈ mertensShell n, shellCoeff n p / Real.sqrt (p : ℝ)) *
          (∑ q ∈ mertensShell n, shellCoeff n q / Real.sqrt (q : ℝ)) := by
      rw [sum_shellCoeff_div_sqrt hn]
      rw [mul_assoc, ← sq, Real.sq_sqrt hn.le]
    _ = ∑ p ∈ mertensShell n, ∑ q ∈ mertensShell n,
        δ * (shellCoeff n p / Real.sqrt (p : ℝ)) *
          (shellCoeff n q / Real.sqrt (q : ℝ)) := by
      simp only [← Finset.mul_sum, ← Finset.sum_mul]
    _ = ∑ p ∈ mertensShell n, ∑ q ∈ mertensShell n,
        shellCoeff n p * shellCoeff n q * (δ / (Real.sqrt (p : ℝ) * Real.sqrt (q : ℝ))) := by
      refine Finset.sum_congr rfl fun p _ => ?_
      refine Finset.sum_congr rfl fun q _ => ?_
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    _ ≤ _ := Finset.sum_le_sum fun p hp => Finset.sum_le_sum fun q hq =>
      mul_le_mul_of_nonneg_left (burnolBaseFirstJetPrimeKernel_shell_lower hp hq)
        (mul_nonneg (shellCoeff_nonneg n p) (shellCoeff_nonneg n q))

/-- The native first jet is bounded but its critical prime part is not compact. -/
theorem not_isCompactOperator_burnolBaseFirstJetPrimeSynthesis :
    ¬ IsCompactOperator burnolBaseFirstJetPrimeSynthesis := by
  intro hcompact
  obtain ⟨N, hN⟩ := exists_mertensShellMass_gt
  let u : ℕ → lp (fun _ : Nat.Primes => ℂ) 2 := fun n => mertensShellVec (N + n + 0)
  have hu : Orthonormal ℂ u := orthonormal_mertensShellVec_shift hN 0
  have hlim := IsCompactOperator.norm_apply_tendsto_zero_of_bounded_weakly_null
    burnolBaseFirstJetPrimeSynthesis hcompact u 1 (fun n => (hu.1 n).le)
    (Orthonormal.weakly_tendsto_zero hu)
  have hlimsq : Tendsto (fun n => ‖burnolBaseFirstJetPrimeSynthesis (u n)‖ ^ 2) atTop (𝓝 0) := by
    simpa using hlim.pow 2
  have hlower : ∀ n, Real.exp (-1) ^ 3 / 8 ≤
      ‖burnolBaseFirstJetPrimeSynthesis (u n)‖ ^ 2 := by
    intro n
    have hm := hN (N + n + 0) (by omega)
    have he := norm_sq_burnolBaseFirstJetPrimeSynthesis_shell_lower (by linarith :
      0 < mertensShellMass (N + n + 0))
    simp only [add_zero] at hm he
    dsimp [u]
    have hmul := mul_le_mul_of_nonneg_left hm.le
      (by positivity : 0 ≤ Real.exp (-1) ^ 3 / 4)
    exact (by nlinarith : Real.exp (-1) ^ 3 / 8 ≤
      Real.exp (-1) ^ 3 / 4 * mertensShellMass (N + n)).trans he
  have hbad := ge_of_tendsto hlimsq (Eventually.of_forall hlower)
  have hpos : 0 < Real.exp (-1) ^ 3 / 8 := by positivity
  linarith

/-- The bounded inclusion of the original prime slice into all prime-depth coefficients. -/
def burnolPrimeDepthZeroInclusion :
    lp (fun _ : Nat.Primes => ℂ) 2 →L[ℂ] lp (fun _ : RoutePPrimitiveIndex => ℂ) 2 :=
  finiteGramSynthesis (fun p : Nat.Primes => lp.single 2 (p, 0) (1 : ℂ))

theorem burnolPrimeDepthZeroInclusion_single (p : Nat.Primes) (z : ℂ) :
    burnolPrimeDepthZeroInclusion (lp.single 2 p z) = z • lp.single 2 (p, 0) (1 : ℂ) := by
  apply finiteGramSynthesis_single_of_majorant
    (T := ContinuousLinearMap.id ℂ (lp (fun _ : Nat.Primes => ℂ) 2))
    (K := fun p q => if p = q then 1 else 0)
  · intro p q
    by_cases h : p = q <;> simp [lpBasisVec, lp.single_apply, h]
  · intro p q
    by_cases h : p = q
    · subst q
      simp
    · simp [lp.inner_single_left, lp.single_apply, RCLike.inner_apply, h]

theorem burnolBaseFirstJetSynthesis_comp_primeInclusion :
    burnolBaseFirstJetSynthesis ∘L burnolPrimeDepthZeroInclusion =
      burnolBaseFirstJetPrimeSynthesis := by
  apply ContinuousLinearMap.ext
  intro x
  have h1 := (lp.hasSum_single (by norm_num) x).mapL
    (burnolBaseFirstJetSynthesis ∘L burnolPrimeDepthZeroInclusion)
  have h2 := (lp.hasSum_single (by norm_num) x).mapL burnolBaseFirstJetPrimeSynthesis
  simp only [ContinuousLinearMap.comp_apply, burnolPrimeDepthZeroInclusion_single,
    map_smul, burnolBaseFirstJetSynthesis_single, one_smul] at h1
  simp only [burnolBaseFirstJetPrimeSynthesis_single] at h2
  exact h1.unique h2

/-- Noncompactness survives the complete source admission; positive depths cannot remove it. -/
theorem not_isCompactOperator_burnolBaseFirstJetSynthesis :
    ¬ IsCompactOperator burnolBaseFirstJetSynthesis := by
  intro h
  have hc : IsCompactOperator (burnolBaseFirstJetSynthesis ∘L burnolPrimeDepthZeroInclusion) :=
    h.comp_clm burnolPrimeDepthZeroInclusion
  rw [burnolBaseFirstJetSynthesis_comp_primeInclusion] at hc
  exact not_isCompactOperator_burnolBaseFirstJetPrimeSynthesis hc

end
end RHTower
