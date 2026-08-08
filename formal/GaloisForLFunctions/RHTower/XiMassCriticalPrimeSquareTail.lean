import GaloisForLFunctions.RHTower.XiMassPrimeSquareBoundaryResidue
import GaloisForLFunctions.RHTower.XiMassCriticalErrorFlux

/-!
# Uniform prime-square tail beyond the critical mass cone

The moving cone has a second analytic use beyond truncating the arithmetic source.  Past
`H_d(u) = d u / (d - 1/2)`, the depth-`d` strip-shift exponent satisfies
`du - dh ≤ -h/2`.  For a square frequency `h = log(p²)`, this supplies one extra factor
`p⁻¹`; the critical square weight `log(p)/p` becomes the summable weight `log(p)/p²`.

This proves a uniform bound for the actual infinite prime-square tail outside the moving cone.
No numerical computation or asymptotic prime estimate is used.
-/

open Complex Filter MeasureTheory Set Topology

namespace RHTower

noncomputable section

theorem cone_exponent_le_neg_half
    {d u h : ℝ} (hdhalf : 1 / 2 < d)
    (hh : d * u / (d - 1 / 2) ≤ h) :
    u * d - h * d ≤ -h / 2 := by
  have hden : 0 < d - 1 / 2 := by linarith
  have hmul := (div_le_iff₀ hden).mp hh
  nlinarith

theorem primePowerCriticalWeight_square_mul_exp_neg_half_log_eq
    (p : Nat.Primes) :
    xiMassPrimePowerCriticalWeight p 1 *
        Real.exp (-Real.log (((p : ℕ) ^ 2 : ℕ) : ℝ) / 2) =
      xiMassPrimeSquareEulerWeight (1 / 2) p := by
  have hpR : 0 < (p : ℝ) := Nat.cast_pos.mpr p.prop.pos
  have hlog :
      Real.log (((p : ℕ) ^ 2 : ℕ) : ℝ) = 2 * Real.log (p : ℝ) := by
    rw [Nat.cast_pow, Real.log_pow]
    norm_num
  have hexp :
      Real.exp (-Real.log (((p : ℕ) ^ 2 : ℕ) : ℝ) / 2) =
        (p : ℝ) ^ (-1 : ℝ) := by
    rw [hlog, Real.rpow_def_of_pos hpR]
    congr 1
    ring
  rw [xiMassPrimePowerCriticalWeight_eq,
    xiMassPrimeSquareEulerWeight_eq, hexp]
  norm_num
  rw [Real.rpow_neg_one]
  field_simp

theorem norm_xiMassCenteredPrimeSquareAtom_beyond_cone_le
    {a sigma d u : ℝ} (hhalf : 1 / 2 < d) (hda : d < a)
    (hsigma : 0 < sigma) (hu : 0 ≤ u) (p : Nat.Primes)
    (hpcone : d * u / (d - 1 / 2) ≤
      Real.log (((p : ℕ) ^ 2 : ℕ) : ℝ)) :
    ‖xiMassCenteredPrimeAtom a ((sigma : ℂ) + u * I) ((p : ℕ) ^ 2)‖ ≤
      xiMassPrimeSquareEulerWeight (1 / 2) p *
        (∫ x : ℝ, Real.exp (-(sigma * |x|))) := by
  let h : ℝ := Real.log (((p : ℕ) ^ 2 : ℕ) : ℝ)
  let J : ℝ := ∫ x : ℝ, Real.exp (-(sigma * |x|))
  have hF := norm_stripFourier_xiMass_deepShift_le
    (a := a) (σ := sigma) (d := d) (by linarith) hda hsigma u h
  rw [abs_of_nonneg hu] at hF
  have hexp : Real.exp (u * d - h * d) ≤ Real.exp (-h / 2) :=
    Real.exp_le_exp.mpr (cone_exponent_le_neg_half hhalf hpcone)
  have hweight : 0 ≤ xiMassPrimePowerCriticalWeight p 1 := norm_nonneg _
  rw [xiMassCenteredPrimeAtom, norm_mul]
  change xiMassPrimePowerCriticalWeight p 1 *
      ‖stripFourier (xiMassAnalyticTest a ((sigma : ℂ) + u * I)) (h : ℂ)‖ ≤ _
  calc
    xiMassPrimePowerCriticalWeight p 1 *
        ‖stripFourier (xiMassAnalyticTest a ((sigma : ℂ) + u * I)) (h : ℂ)‖ ≤
      xiMassPrimePowerCriticalWeight p 1 * (Real.exp (u * d - h * d) * J) :=
        mul_le_mul_of_nonneg_left hF hweight
    _ ≤ xiMassPrimePowerCriticalWeight p 1 * (Real.exp (-h / 2) * J) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hexp (integral_nonneg fun _ => Real.exp_nonneg _))
        hweight
    _ = xiMassPrimeSquareEulerWeight (1 / 2) p * J := by
      rw [← mul_assoc, primePowerCriticalWeight_square_mul_exp_neg_half_log_eq]

noncomputable def xiMassCriticalPrimeSquareConeTail
    (a sigma d u : ℝ) : ℂ :=
  ∑' p : Nat.Primes,
    if d * u / (d - 1 / 2) <
        Real.log (((p : ℕ) ^ 2 : ℕ) : ℝ) then
      xiMassCenteredPrimeAtom a ((sigma : ℂ) + u * I) ((p : ℕ) ^ 2)
    else 0

theorem summable_norm_xiMassCriticalPrimeSquareConeTail
    {a sigma d u : ℝ} (hhalf : 1 / 2 < d) (hda : d < a)
    (hsigma : 0 < sigma) (hu : 0 ≤ u) :
    Summable (fun p : Nat.Primes =>
      ‖if d * u / (d - 1 / 2) <
          Real.log (((p : ℕ) ^ 2 : ℕ) : ℝ) then
        xiMassCenteredPrimeAtom a ((sigma : ℂ) + u * I) ((p : ℕ) ^ 2)
      else 0‖) := by
  let J : ℝ := ∫ x : ℝ, Real.exp (-(sigma * |x|))
  have hJ : 0 ≤ J := integral_nonneg fun _ => Real.exp_nonneg _
  have hmajor : Summable (fun p : Nat.Primes =>
      xiMassPrimeSquareEulerWeight (1 / 2) p * J) :=
    (summable_xiMassPrimeSquareEulerWeight (by norm_num)).mul_right J
  apply hmajor.of_nonneg_of_le
  · intro p
    exact norm_nonneg _
  · intro p
    split_ifs with hp
    · simpa only [J] using
        norm_xiMassCenteredPrimeSquareAtom_beyond_cone_le
          hhalf hda hsigma hu p hp.le
    · simp only [norm_zero]
      exact mul_nonneg (by
        rw [xiMassPrimeSquareEulerWeight_eq]
        positivity) hJ

theorem summable_xiMassCriticalPrimeSquareConeTail
    {a sigma d u : ℝ} (hhalf : 1 / 2 < d) (hda : d < a)
    (hsigma : 0 < sigma) (hu : 0 ≤ u) :
    Summable (fun p : Nat.Primes =>
      if d * u / (d - 1 / 2) <
          Real.log (((p : ℕ) ^ 2 : ℕ) : ℝ) then
        xiMassCenteredPrimeAtom a ((sigma : ℂ) + u * I) ((p : ℕ) ^ 2)
      else 0) :=
  summable_norm_iff.mp
    (summable_norm_xiMassCriticalPrimeSquareConeTail
      hhalf hda hsigma hu)

theorem norm_xiMassCriticalPrimeSquareConeTail_le
    {a sigma d u : ℝ} (hhalf : 1 / 2 < d) (hda : d < a)
    (hsigma : 0 < sigma) (hu : 0 ≤ u) :
    ‖xiMassCriticalPrimeSquareConeTail a sigma d u‖ ≤
      (∑' p : Nat.Primes, xiMassPrimeSquareEulerWeight (1 / 2) p) *
        (∫ x : ℝ, Real.exp (-(sigma * |x|))) := by
  let J : ℝ := ∫ x : ℝ, Real.exp (-(sigma * |x|))
  let f : Nat.Primes → ℂ := fun p =>
    if d * u / (d - 1 / 2) <
        Real.log (((p : ℕ) ^ 2 : ℕ) : ℝ) then
      xiMassCenteredPrimeAtom a ((sigma : ℂ) + u * I) ((p : ℕ) ^ 2)
    else 0
  have hnorm : Summable (fun p => ‖f p‖) := by
    simpa only [f] using
      summable_norm_xiMassCriticalPrimeSquareConeTail
        hhalf hda hsigma hu
  have hmajor : Summable (fun p : Nat.Primes =>
      xiMassPrimeSquareEulerWeight (1 / 2) p * J) :=
    (summable_xiMassPrimeSquareEulerWeight (by norm_num)).mul_right J
  have hpoint (p : Nat.Primes) :
      ‖f p‖ ≤ xiMassPrimeSquareEulerWeight (1 / 2) p * J := by
    dsimp only [f]
    split_ifs with hp
    · simpa only [J] using
        norm_xiMassCenteredPrimeSquareAtom_beyond_cone_le
          hhalf hda hsigma hu p hp.le
    · simp only [norm_zero]
      exact mul_nonneg (by
        rw [xiMassPrimeSquareEulerWeight_eq]
        positivity) (integral_nonneg fun _ => Real.exp_nonneg _)
  calc
    ‖xiMassCriticalPrimeSquareConeTail a sigma d u‖ ≤
        ∑' p : Nat.Primes, ‖f p‖ := by
      exact norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' p : Nat.Primes,
        xiMassPrimeSquareEulerWeight (1 / 2) p * J := by
      exact hnorm.tsum_le_tsum hpoint hmajor
    _ = (∑' p : Nat.Primes,
          xiMassPrimeSquareEulerWeight (1 / 2) p) *
        (∫ x : ℝ, Real.exp (-(sigma * |x|))) := by
      rw [tsum_mul_right]

end

end RHTower
