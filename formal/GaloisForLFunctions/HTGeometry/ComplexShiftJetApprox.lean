import GaloisForLFunctions.HTGeometry.ComplexShiftDigammaExpansion
import GaloisForLFunctions.HTGeometry.GammaMonomialRatApprox
import GaloisForLFunctions.HTGeometry.DigammaHypertranscendental

/-!
# Approximability of digamma jets at arbitrary complex shifts

Two steps remove every restriction on the shift.  A shift with nonnegative real part keeps the
translated abscissa in the right half plane, so the unshifted expansion applies verbatim.  An
arbitrary shift is moved into that range by finitely many unit steps of the digamma recurrence, and
each step costs only an inverse power, which is rational.
-/

open Filter Topology Complex

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

/-- Approximability with logarithms only depends on the values on tubes. -/
theorem hasLogRatApprox_of_tube_eq {f h : ℂ → ℂ} (hh : HasLogRatApprox h)
    (heq : ∀ M : ℝ, 0 < M → ∃ T : ℝ, 2 ≤ T ∧ ∀ σ t : ℝ, 0 < σ → σ ≤ M → T ≤ t →
      f ((σ : ℂ) + (t : ℂ) * Complex.I) = h ((σ : ℂ) + (t : ℂ) * Complex.I)) :
    HasLogRatApprox f := by
  intro M hM N
  obtain ⟨A, q, C, T, hq, hC, hT, hb⟩ := hh M hM N
  obtain ⟨T', hT', heq'⟩ := heq M hM
  refine ⟨A, q, C, max T T', hq, hC, le_trans hT (le_max_left _ _), fun σ t hσ hσM ht => ?_⟩
  rw [heq' σ t hσ hσM (le_trans (le_max_right _ _) ht)]
  exact hb σ t hσ hσM (le_trans (le_max_left _ _) ht)

/-- **The `n`-fold digamma jet recurrence.** -/
theorem digammaJet_add_natCast (j : ℕ) {z : ℂ} (hz : ∀ p : ℕ, z ≠ -(p : ℂ)) (n : ℕ) :
    iteratedDeriv j Complex.digamma (z + (n : ℂ))
      = iteratedDeriv j Complex.digamma z
        + ∑ i ∈ Finset.range n, (-1) ^ j * (j.factorial : ℂ) / (z + (i : ℂ)) ^ (j + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hzn : ∀ p : ℕ, z + (n : ℂ) ≠ -(p : ℂ) := by
        intro p hcon
        refine hz (p + n) ?_
        have hval : z = -(p : ℂ) - (n : ℂ) := by linear_combination hcon
        rw [hval]
        push_cast
        ring
      have hrw : z + ((n + 1 : ℕ) : ℂ) = (z + (n : ℂ)) + 1 := by push_cast; ring
      rw [hrw, digammaJet_shift j hzn, ih, Finset.sum_range_succ]
      ring

/-- A tube point shifted by any complex number avoids the poles of the digamma jets, once the
height exceeds the size of the shift. -/
theorem tube_add_ne_neg_natCast {σ t : ℝ} {lam : ℂ} (ht : ‖lam‖ < t) (p : ℕ) :
    (σ : ℂ) + (t : ℂ) * Complex.I + lam ≠ -(p : ℂ) := by
  intro hcon
  have him : (((σ : ℂ) + (t : ℂ) * Complex.I + lam)).im = t + lam.im := by simp
  rw [hcon] at him
  simp only [Complex.neg_im, Complex.natCast_im, neg_zero] at him
  have h1 : |lam.im| ≤ ‖lam‖ := Complex.abs_im_le_norm lam
  have h2 : -‖lam‖ ≤ lam.im := (abs_le.mp h1).1
  linarith

/-- **The complex-shifted digamma jets are approximable**, for a shift in the closed right half
plane. -/
theorem hasRatApprox_iteratedDeriv_digamma_complexShift {lam : ℂ} (hlam : 0 ≤ lam.re) (j : ℕ) :
    HasRatApprox (fun z => iteratedDeriv (j + 1) Complex.digamma (z + lam)) := by
  intro M hM N
  obtain ⟨Q, C, T, hC, hT, hb⟩ := exists_iteratedDeriv_digamma_complexShift_expansion lam hlam j N
  refine ⟨invReverse Q, Polynomial.X ^ Q.natDegree, C, T, pow_ne_zero _ Polynomial.X_ne_zero,
    hC, hT, fun σ t hσ hσM ht => ?_⟩
  have htpos : (0 : ℝ) < t := by linarith
  have ht1 : (1 : ℝ) ≤ t := by linarith
  have hs : ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := vertical_ne_zero_of_pos htpos
  have hval := hb σ t hσ ht
  rw [← eval_inv_eq_div Q hs]
  refine le_trans hval ?_
  have hpow : t ^ N ≤ t ^ (N + 1) := pow_le_pow_right₀ ht1 (by omega)
  exact div_le_div_of_nonneg_left hC (by positivity) hpow

/-- **The complex-shifted digamma is approximable with logarithms**, for a shift in the closed
right half plane. -/
theorem hasLogRatApprox_digamma_complexShift {lam : ℂ} (hlam : 0 ≤ lam.re) :
    HasLogRatApprox (fun z => Complex.digamma (z + lam)) := by
  intro M hM N
  obtain ⟨P, C, T, hC, hT, hb⟩ := exists_digamma_complexShift_expansion lam hlam N
  refine ⟨Polynomial.C (invReverse P) + Polynomial.X * Polynomial.C (Polynomial.X ^ P.natDegree),
    Polynomial.X ^ P.natDegree, C, T, pow_ne_zero _ Polynomial.X_ne_zero, hC, hT,
    fun σ t hσ hσM ht => ?_⟩
  have htpos : (0 : ℝ) < t := by linarith
  have ht1 : (1 : ℝ) ≤ t := by linarith
  have hs : ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := vertical_ne_zero_of_pos htpos
  have hval := hb σ t hσ ht
  set s : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I with hsdef
  have hden : Polynomial.eval s (Polynomial.X ^ P.natDegree) = s ^ P.natDegree := by
    rw [Polynomial.eval_pow, Polynomial.eval_X]
  have hnum : logPolyEval
      (Polynomial.C (invReverse P) + Polynomial.X * Polynomial.C (Polynomial.X ^ P.natDegree)) s
      = (invReverse P).eval s + Complex.log s * s ^ P.natDegree := by
    rw [logPolyEval, Polynomial.eval₂_add, Polynomial.eval₂_C, Polynomial.eval₂_mul,
      Polynomial.eval₂_X, Polynomial.eval₂_C]
    simp
  rw [hnum, hden]
  have hsplit : ((invReverse P).eval s + Complex.log s * s ^ P.natDegree) / s ^ P.natDegree
      = P.eval (1 / s) + Complex.log s := by
    have hinv : P.eval (1 / s) = (invReverse P).eval s / s ^ P.natDegree := by
      rw [eval_invReverse P hs, mul_comm, mul_div_assoc, div_self (pow_ne_zero _ hs), mul_one]
    rw [hinv, add_div, mul_div_assoc, div_self (pow_ne_zero _ hs), mul_one]
  rw [hsplit]
  have hrw : Complex.digamma (s + lam) - (P.eval (1 / s) + Complex.log s)
      = Complex.digamma (s + lam) - Complex.log s - P.eval (1 / s) := by ring
  rw [hrw]
  refine le_trans hval ?_
  have hpow : t ^ N ≤ t ^ (N + 1) := pow_le_pow_right₀ ht1 (by omega)
  exact div_le_div_of_nonneg_left hC (by positivity) hpow

/-- Every complex number is a natural translate away from the closed right half plane. -/
theorem exists_natCast_shift_re_nonneg (lam : ℂ) : ∃ m : ℕ, 0 ≤ (lam + (m : ℂ)).re := by
  refine ⟨⌈-lam.re⌉₊, ?_⟩
  have hle : -lam.re ≤ (⌈-lam.re⌉₊ : ℝ) := Nat.le_ceil _
  simp only [Complex.add_re, Complex.natCast_re]
  linarith

/-- **The digamma jets are approximable at every complex shift.** -/
theorem hasRatApprox_iteratedDeriv_digamma_anyShift (lam : ℂ) (j : ℕ) :
    HasRatApprox (fun z => iteratedDeriv (j + 1) Complex.digamma (z + lam)) := by
  obtain ⟨m, hm⟩ := exists_natCast_shift_re_nonneg lam
  set c : ℂ := (-1) ^ (j + 1) * (((j + 1).factorial : ℕ) : ℂ) with hc
  set h : ℂ → ℂ := fun z => iteratedDeriv (j + 1) Complex.digamma (z + (lam + (m : ℂ)))
    + ∑ i ∈ Finset.range m, (-c) / (z + (lam + (i : ℂ))) ^ (j + 2) with hhdef
  have hh : HasRatApprox h := by
    refine (hasRatApprox_iteratedDeriv_digamma_complexShift hm j).add ?_
    refine HasRatApprox.finsetSum _ _ fun i _ => ?_
    have hfun : (fun z : ℂ => (-c) / (z + (lam + (i : ℂ))) ^ (j + 2))
        = fun z : ℂ => Polynomial.eval z (Polynomial.C (-c))
            / Polynomial.eval z ((Polynomial.X + Polynomial.C (lam + (i : ℂ))) ^ (j + 2)) := by
      funext z
      simp [Polynomial.eval_pow]
    rw [hfun]
    exact hasRatApprox_ratEval _ (pow_ne_zero _ (Polynomial.X_add_C_ne_zero _))
  refine hasRatApprox_of_tube_eq hh fun M hM => ⟨max 2 (‖lam‖ + 1), le_max_left _ _, ?_⟩
  intro σ t hσ hσM ht
  have htlam : ‖lam‖ < t := lt_of_lt_of_le (by linarith) (le_trans (le_max_right _ _) ht)
  set z : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I with hz
  have hpole : ∀ p : ℕ, z + lam ≠ -(p : ℂ) := fun p => tube_add_ne_neg_natCast htlam p
  have hrec := digammaJet_add_natCast (j + 1) hpole m
  have hassoc : z + lam + (m : ℂ) = z + (lam + (m : ℂ)) := by ring
  rw [hassoc] at hrec
  have hterms : ∀ i : ℕ, z + lam + (i : ℂ) = z + (lam + (i : ℂ)) := fun i => by ring
  simp only [hhdef]
  rw [hrec]
  simp only [hterms, ← hc]
  have hcancel : (∑ x ∈ Finset.range m, c / (z + (lam + (x : ℂ))) ^ (j + 1 + 1))
      + ∑ i ∈ Finset.range m, (-c) / (z + (lam + (i : ℂ))) ^ (j + 2) = 0 := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_eq_zero fun i _ => by rw [neg_div]; ring
  linear_combination -hcancel

/-- **The digamma is approximable with logarithms at every complex shift.** -/
theorem hasLogRatApprox_digamma_anyShift (lam : ℂ) :
    HasLogRatApprox (fun z => Complex.digamma (z + lam)) := by
  obtain ⟨m, hm⟩ := exists_natCast_shift_re_nonneg lam
  set h : ℂ → ℂ := fun z => Complex.digamma (z + (lam + (m : ℂ)))
    + ∑ i ∈ Finset.range m, (-1 : ℂ) / (z + (lam + (i : ℂ))) with hhdef
  have hh : HasLogRatApprox h := by
    refine (hasLogRatApprox_digamma_complexShift hm).add ?_
    refine (HasRatApprox.finsetSum _ _ fun i _ => ?_).hasLogRatApprox
    have hfun : (fun z : ℂ => (-1 : ℂ) / (z + (lam + (i : ℂ))))
        = fun z : ℂ => Polynomial.eval z (Polynomial.C (-1 : ℂ))
            / Polynomial.eval z (Polynomial.X + Polynomial.C (lam + (i : ℂ))) := by
      funext z
      simp
    rw [hfun]
    exact hasRatApprox_ratEval _ (Polynomial.X_add_C_ne_zero _)
  refine hasLogRatApprox_of_tube_eq hh fun M hM => ⟨max 2 (‖lam‖ + 1), le_max_left _ _, ?_⟩
  intro σ t hσ hσM ht
  have htlam : ‖lam‖ < t := lt_of_lt_of_le (by linarith) (le_trans (le_max_right _ _) ht)
  set z : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I with hz
  have hpole : ∀ p : ℕ, z + lam ≠ -(p : ℂ) := fun p => tube_add_ne_neg_natCast htlam p
  have hrec := digammaJet_add_natCast 0 hpole m
  rw [iteratedDeriv_zero] at hrec
  have hassoc : z + lam + (m : ℂ) = z + (lam + (m : ℂ)) := by ring
  rw [hassoc] at hrec
  have hterms : ∀ i : ℕ, z + lam + (i : ℂ) = z + (lam + (i : ℂ)) := fun i => by ring
  simp only [hhdef]
  rw [hrec]
  simp only [hterms]
  have hcancel : (∑ x ∈ Finset.range m,
        (-1 : ℂ) ^ (0 : ℕ) * ((Nat.factorial 0 : ℕ) : ℂ) / (z + (lam + (x : ℂ))) ^ (0 + 1))
      + ∑ i ∈ Finset.range m, (-1 : ℂ) / (z + (lam + (i : ℂ))) = 0 := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun i _ => ?_
    norm_num
    rw [neg_div, one_div, add_neg_cancel]
  linear_combination -hcancel

end

end GaloisForLFunctions.HTGeometry
