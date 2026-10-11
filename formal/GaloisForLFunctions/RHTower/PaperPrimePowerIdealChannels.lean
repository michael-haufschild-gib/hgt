import GaloisForLFunctions.RHTower.PaperPrimeRegularizedIdeal

/-!
# Every prime-power layer retained by the paper ideal trace

Restrict the literal DR/PBM coefficient rows to the escaping sequence of `(k+1)`-st powers of
all primes. The logarithmic row has quotient character `1/(k+1)` on every layer; the prime row
has character one on primes and zero on all proper powers. Thus infinitely many arithmetic
layers survive, despite equality of the two convergence receivers.
-/

namespace RHTower
noncomputable section
open GaloisForLFunctions GaloisForLFunctions.HTGeometry Filter
open scoped Topology ENNReal

/-- Literal restriction of the logarithmic row to one full prime-power layer. -/
def paperLogZetaPrimePowerChannel (k : ℕ) :
    PaperPrimeCoefficientSpace →L[ℂ] PaperPrimeCoefficientSpace :=
  paperConvergentDiagonal (fun n => (logZetaRegCoeff (paperPrimePowerIndex k n) : ℂ))
    (Complex.continuous_ofReal.continuousAt.tendsto.comp
      (tendsto_logZetaRegCoeff_primePower k))

/-- Literal restriction of the prime row to the same layer. -/
def paperPrimePrimePowerChannel (k : ℕ) :
    PaperPrimeCoefficientSpace →L[ℂ] PaperPrimeCoefficientSpace :=
  paperConvergentDiagonal (fun n => (primeRegCoeff (paperPrimePowerIndex k n) : ℂ))
    (Complex.continuous_ofReal.continuousAt.tendsto.comp
      (tendsto_primeRegCoeff_primePower k))

@[simp] theorem paperLogZetaPrimePowerChannel_apply (k : ℕ)
    (f : PaperPrimeCoefficientSpace) (n : ℕ) :
    paperLogZetaPrimePowerChannel k f n =
      (logZetaRegCoeff (paperPrimePowerIndex k n) : ℂ) * f n := rfl

@[simp] theorem paperPrimePrimePowerChannel_apply (k : ℕ)
    (f : PaperPrimeCoefficientSpace) (n : ℕ) :
    paperPrimePrimePowerChannel k f n =
      (primeRegCoeff (paperPrimePowerIndex k n) : ℂ) * f n := rfl

/-- Every logarithmic layer has a prescribed nonzero quotient character. -/
theorem paperLogZetaPrimePowerChannel_character (k : ℕ) :
    IsCompactOperator (paperLogZetaPrimePowerChannel k -
      Complex.ofReal (((k + 1 : ℕ) : ℝ)⁻¹) •
        (1 : PaperPrimeCoefficientSpace →L[ℂ] PaperPrimeCoefficientSpace)) := by
  exact paperConvergentDiagonal_sub_limit_compact
    (fun n => (logZetaRegCoeff (paperPrimePowerIndex k n) : ℂ))
    (Complex.continuous_ofReal.continuousAt.tendsto.comp
      (tendsto_logZetaRegCoeff_primePower k))

/-- The exact essential norm on every logarithmic layer. -/
theorem compactIdealDistance_paperLogZetaPrimePowerChannel (k : ℕ) :
    compactIdealDistance (paperLogZetaPrimePowerChannel k) = ((k + 1 : ℕ) : ℝ)⁻¹ := by
  rw [paperLogZetaPrimePowerChannel, paperConvergentDiagonal_compactIdealDistance]
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity :
    0 ≤ ((k + 1 : ℕ) : ℝ)⁻¹)]

/-- Every proper-power prime channel is compact. -/
theorem paperPrimePrimePowerChannel_compact (k : ℕ) :
    IsCompactOperator (paperPrimePrimePowerChannel (k + 1)) := by
  apply (paperConvergentDiagonal_compact_iff _ _).2
  simp

/-- The prime channel retains the identity character at exponent one. -/
theorem paperPrimePrimePowerChannel_primes_character :
    IsCompactOperator (paperPrimePrimePowerChannel 0 -
      (1 : PaperPrimeCoefficientSpace →L[ℂ] PaperPrimeCoefficientSpace)) := by
  have h := paperConvergentDiagonal_sub_limit_compact _
    (Complex.continuous_ofReal.continuousAt.tendsto.comp
      (tendsto_primeRegCoeff_primePower 0))
  simpa [paperPrimePrimePowerChannel, Function.comp_def, PaperPrimeCoefficientSpace] using h

/-- On each proper-power layer the two native operators differ by exactly a scalar identity. -/
theorem paperPrimePowerChannels_difference (k : ℕ) :
    paperLogZetaPrimePowerChannel (k + 1) - paperPrimePrimePowerChannel (k + 1) =
      Complex.ofReal (((k + 2 : ℕ) : ℝ)⁻¹) •
        (1 : PaperPrimeCoefficientSpace →L[ℂ] PaperPrimeCoefficientSpace) := by
  apply ContinuousLinearMap.ext
  intro f
  ext n
  simp only [sub_apply, lp.coeFn_sub, Pi.sub_apply, paperLogZetaPrimePowerChannel_apply,
    paperPrimePrimePowerChannel_apply]
  rw [← sub_mul, ← Complex.ofReal_sub, logZetaRegCoeff_sub_primeRegCoeff]
  have he := logPrimePowerDefect_primePower ⟨_, Nat.prime_nth_prime n⟩ k
  change _ * f n = _ * f n
  rw [show logPrimePowerDefect (paperPrimePowerIndex (k + 1) n) =
    ((k + 2 : ℕ) : ℝ)⁻¹ from he]

/-- Infinite paper ideal cost at every logarithmic prime-power layer. -/
theorem paperLogZetaPrimePowerChannel_traceCost (k : ℕ) :
    compactOperatorTraceCost PaperPrimeCoefficientSpace (paperLogZetaPrimePowerChannel k) = ∞ := by
  rw [paperLogZetaPrimePowerChannel, paperConvergentDiagonal_traceCost]
  have hk : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
  have hn : Complex.ofReal (((k + 1 : ℕ) : ℝ)⁻¹) ≠ 0 := by
    exact_mod_cast (inv_ne_zero hk.ne')
  rw [if_neg hn]

/-- The prime row has zero paper cost on every proper-power layer. -/
theorem paperPrimePrimePowerChannel_traceCost (k : ℕ) :
    compactOperatorTraceCost PaperPrimeCoefficientSpace (paperPrimePrimePowerChannel (k + 1)) = 0 :=
  (compactOperatorTraceCost_eq_zero_iff _).2 (paperPrimePrimePowerChannel_compact k)

/-- Both coefficient rows retain infinite cost on the actual prime layer. -/
theorem paperPrimePrimePowerChannel_primes_traceCost :
    compactOperatorTraceCost PaperPrimeCoefficientSpace (paperPrimePrimePowerChannel 0) = ∞ := by
  rw [paperPrimePrimePowerChannel, paperConvergentDiagonal_traceCost]
  simp

/-- Distinct logarithmic prime-power layers remain distinct modulo compact operators. -/
theorem paperLogZetaPrimePowerChannel_compact_difference_iff (j k : ℕ) :
    IsCompactOperator (paperLogZetaPrimePowerChannel j - paperLogZetaPrimePowerChannel k) ↔
      j = k := by
  rw [paperLogZetaPrimePowerChannel, paperLogZetaPrimePowerChannel,
    paperConvergentDiagonal_compact_sub_iff]
  simp

/-- Exact quotient distance between all pairs of logarithmic layers. -/
theorem compactIdealDistance_paperLogZetaPrimePowerChannel_difference (j k : ℕ) :
    compactIdealDistance (paperLogZetaPrimePowerChannel j - paperLogZetaPrimePowerChannel k) =
      |((j + 1 : ℕ) : ℝ)⁻¹ - ((k + 1 : ℕ) : ℝ)⁻¹| := by
  rw [paperLogZetaPrimePowerChannel, paperLogZetaPrimePowerChannel,
    paperConvergentDiagonal_compactIdealDistance_sub, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs]

end
end RHTower
