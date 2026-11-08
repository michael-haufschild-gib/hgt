import GaloisForLFunctions.SelbergClass.Primon.KestenCharacterSchur
import GaloisForLFunctions.HTGeometry.CompactTailDensePrimeShiftJet

/-!
# Prime jets of the likelihood curve

Remove the first `N` even characters from a prime likelihood and multiply
the remainder by `pᴺ`. Its Gram kernel is independent of `N`. Subtracting
the leading character gives exactly the original centered Cauchy kernel,
so every jet order has the same prime-limit error, even when the order
varies with the prime.
-/

open Filter Topology
open _root_.RHTower
open GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.SelbergClass.Primon
noncomputable section

/-- The next truncation appends precisely one even-character coordinate. -/
theorem kestenCharacterTruncation_succ (p : Nat.Primes) (N : ℕ) :
    kestenCharacterTruncation p (N + 1) = kestenCharacterTruncation p N +
      (p : ℝ)⁻¹ ^ N • spectralCharacterVector (2 * N) := by
  exact Finset.sum_range_succ _ N

/-- The likelihood remainder normalized by its first nonzero prime power. -/
def kestenNormalizedTail (p : Nat.Primes) (N : ℕ) : SemicircleL2 :=
  (p : ℝ) ^ N • (kestenLikelihoodVector p - kestenCharacterTruncation p N)

@[simp] theorem kestenNormalizedTail_zero (p : Nat.Primes) :
    kestenNormalizedTail p 0 = kestenLikelihoodVector p := by
  simp [kestenNormalizedTail, kestenCharacterTruncation]

private theorem prime_pow_mul_inverse_pow (p : Nat.Primes) (N : ℕ) :
    (p : ℝ) ^ N * (p : ℝ)⁻¹ ^ N = 1 := by
  rw [← mul_pow, mul_inv_cancel₀ (by exact_mod_cast p.property.ne_zero), one_pow]

/-- The leading character has coefficient one at every normalized depth. -/
theorem inner_kestenNormalizedTail_leading (p : Nat.Primes) (N : ℕ) :
    inner ℝ (kestenNormalizedTail p N) (spectralCharacterVector (2 * N)) = 1 := by
  rw [kestenNormalizedTail, inner_smul_left, inner_characterResidual_evenCharacter,
    if_neg (Nat.lt_irrefl N)]
  simpa only [conj_trivial] using prime_pow_mul_inverse_pow p N

/-- Removing the leading character advances the unnormalized remainder by one degree. -/
theorem kestenNormalizedTail_sub_leading (p : Nat.Primes) (N : ℕ) :
    kestenNormalizedTail p N - spectralCharacterVector (2 * N) =
      (p : ℝ) ^ N • (kestenLikelihoodVector p - kestenCharacterTruncation p (N + 1)) := by
  rw [kestenCharacterTruncation_succ, sub_add_eq_sub_sub, smul_sub, smul_smul,
    prime_pow_mul_inverse_pow, one_smul]
  rfl

/-- The normalized tails satisfy an exact backward innovation equation. -/
theorem kestenNormalizedTail_step (p : Nat.Primes) (N : ℕ) :
    kestenNormalizedTail p N = spectralCharacterVector (2 * N) +
      (p : ℝ)⁻¹ • kestenNormalizedTail p (N + 1) := by
  have hp : (p : ℝ) ≠ 0 := by exact_mod_cast p.property.ne_zero
  have he : (p : ℝ)⁻¹ * (p : ℝ) ^ (N + 1) = (p : ℝ) ^ N := by
    rw [pow_succ]
    calc
      _ = (p : ℝ) ^ N * ((p : ℝ)⁻¹ * (p : ℝ)) := by ring
      _ = _ := by rw [inv_mul_cancel₀ hp, mul_one]
  have hs : (p : ℝ)⁻¹ • kestenNormalizedTail p (N + 1) =
      (p : ℝ) ^ N • (kestenLikelihoodVector p - kestenCharacterTruncation p (N + 1)) := by
    rw [kestenNormalizedTail, smul_smul, he]
  rw [hs, ← kestenNormalizedTail_sub_leading]
  abel

/-- Rescaling a common character tail preserves the entire prime Gram kernel. -/
theorem inner_kestenNormalizedTail_sameDepth (p q : Nat.Primes) (N : ℕ) :
    inner ℝ (kestenNormalizedTail p N) (kestenNormalizedTail q N) =
      1 / (1 - primeReciprocal p * primeReciprocal q) := by
  have hp : (p : ℝ) ≠ 0 := by exact_mod_cast p.property.ne_zero
  have hq : (q : ℝ) ≠ 0 := by exact_mod_cast q.property.ne_zero
  have hc : ((p : ℝ) ^ N * (q : ℝ) ^ N) *
      (primeReciprocal p * primeReciprocal q) ^ N = 1 := by
    rw [← mul_pow, ← mul_pow]
    have he : ((p : ℝ) * (q : ℝ)) * (primeReciprocal p * primeReciprocal q) = 1 := by
      unfold primeReciprocal
      field_simp [hp, hq]
    rw [he, one_pow]
  rw [kestenNormalizedTail, kestenNormalizedTail, inner_smul_left, inner_smul_right,
    inner_likelihood_characterResidual]
  simp only [conj_trivial]
  calc
    _ = (((p : ℝ) ^ N * (q : ℝ) ^ N) * (primeReciprocal p * primeReciprocal q) ^ N) /
        (1 - primeReciprocal p * primeReciprocal q) := by ring
    _ = _ := by rw [hc]

/-- Every normalized prime tail has the same squared norm. -/
theorem norm_sq_kestenNormalizedTail (p : Nat.Primes) (N : ℕ) :
    ‖kestenNormalizedTail p N‖ ^ 2 = 1 / (1 - primeReciprocal p ^ 2) := by
  rw [← real_inner_self_eq_norm_sq, inner_kestenNormalizedTail_sameDepth]
  ring

/-- The centered Gram geometry is unchanged at every jet order. -/
theorem inner_kestenNormalizedTail_error (p q : Nat.Primes) (N : ℕ) :
    inner ℝ (kestenNormalizedTail p N - spectralCharacterVector (2 * N))
      (kestenNormalizedTail q N - spectralCharacterVector (2 * N)) =
        ((p : ℝ) * (q : ℝ) - 1)⁻¹ := by
  have hp : 1 < (p : ℝ) := by exact_mod_cast p.property.one_lt
  have hq : 1 < (q : ℝ) := by exact_mod_cast q.property.one_lt
  have hp0 : (p : ℝ) ≠ 0 := ne_of_gt (by linarith only [hp])
  have hq0 : (q : ℝ) ≠ 0 := ne_of_gt (by linarith only [hq])
  have hd : (p : ℝ) * (q : ℝ) - 1 ≠ 0 := by
    have h := mul_lt_mul_of_pos_left hq (show 0 < (p : ℝ) by linarith only [hp])
    nlinarith only [h, hp]
  rw [inner_sub_left, inner_sub_right, inner_sub_right,
    inner_kestenNormalizedTail_sameDepth, inner_kestenNormalizedTail_leading,
    real_inner_comm (kestenNormalizedTail q N) (spectralCharacterVector (2 * N)),
    inner_kestenNormalizedTail_leading, inner_spectralCharacterVector, if_pos rfl]
  unfold primeReciprocal
  field_simp [hp0, hq0, hd]
  ring

/-- The squared error in extracting any character is exactly `1/(p²-1)`. -/
theorem norm_sq_kestenNormalizedTail_error (p : Nat.Primes) (N : ℕ) :
    ‖kestenNormalizedTail p N - spectralCharacterVector (2 * N)‖ ^ 2 =
      ((p : ℝ) ^ 2 - 1)⁻¹ := by
  rw [← real_inner_self_eq_norm_sq, inner_kestenNormalizedTail_error]
  ring

/-- Character extraction remains asymptotically exact for any prime-dependent choice of order. -/
theorem tendsto_kestenNormalizedTail_error (order : Nat.Primes → ℕ) :
    Tendsto (fun p => ‖kestenNormalizedTail p (order p) -
      spectralCharacterVector (2 * order p)‖) cofinite (𝓝 0) := by
  have hi : Tendsto (fun p : Nat.Primes => (p : ℝ)⁻¹) cofinite (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_primeReal_cofinite_atTop
  have hd := (tendsto_const_nhds (x := (1 : ℝ))).sub (hi.pow 2)
  have h := (hi.pow 2).div hd (by norm_num : (1 : ℝ) - 0 ^ 2 ≠ 0)
  have he (p : Nat.Primes) : ((p : ℝ) ^ 2 - 1)⁻¹ =
      ((p : ℝ)⁻¹) ^ 2 / (1 - ((p : ℝ)⁻¹) ^ 2) := by
    have hp : (p : ℝ) ≠ 0 := by exact_mod_cast p.property.ne_zero
    field_simp [hp]
  have hs : Tendsto (fun p => ‖kestenNormalizedTail p (order p) -
      spectralCharacterVector (2 * order p)‖ ^ 2) cofinite (𝓝 0) := by
    simp_rw [norm_sq_kestenNormalizedTail_error, he]
    convert h using 1 <;> simp <;> ext p <;> rfl
  simpa only [Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using hs.sqrt

/-- Each fixed-order prime jet converges to its leading even Chebyshev character. -/
theorem tendsto_kestenNormalizedTail (N : ℕ) :
    Tendsto (fun p => kestenNormalizedTail p N) cofinite
      (𝓝 (spectralCharacterVector (2 * N))) :=
  tendsto_iff_norm_sub_tendsto_zero.2 (tendsto_kestenNormalizedTail_error (fun _ => N))

end
end GaloisForLFunctions.SelbergClass.Primon

