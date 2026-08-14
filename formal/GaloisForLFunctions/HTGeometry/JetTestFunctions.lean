import GaloisForLFunctions.HTGeometry.SchwartzCompactSupport

/-!
# Test functions with prescribed jets at the origin

The monomials cut off near the origin form a family of Schwartz functions whose derivatives at the
origin are the Kronecker delta.  They realise every prescribed finite jet, which is what turns the
vanishing theorem for distributions supported at a point into a representation by derivatives of the
delta.
-/

open Set

namespace GaloisForLFunctions.HTGeometry

noncomputable section

theorem contDiff_ofReal_pow (j : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (fun x : ℝ => ((x : ℂ)) ^ j) :=
  (Complex.ofRealCLM.contDiff).pow j

theorem hasDerivAt_ofReal_pow (j : ℕ) (x : ℝ) :
    HasDerivAt (fun y : ℝ => ((y : ℂ)) ^ j) ((j : ℂ) * ((x : ℂ)) ^ (j - 1)) x := by
  have hbase : HasDerivAt (fun y : ℝ => ((y : ℂ))) 1 x := by
    have h0 := (hasDerivAt_id x).ofReal_comp
    rw [Complex.ofReal_one] at h0
    exact h0
  have h := hbase.pow j
  rw [mul_one] at h
  exact h

theorem deriv_ofReal_pow (j : ℕ) :
    deriv (fun y : ℝ => ((y : ℂ)) ^ j) = fun x : ℝ => (j : ℂ) * ((x : ℂ)) ^ (j - 1) := by
  funext x
  exact (hasDerivAt_ofReal_pow j x).deriv

/-- The iterated derivative of a monomial along the real line. -/
theorem iteratedDeriv_ofReal_pow (i j : ℕ) :
    iteratedDeriv i (fun x : ℝ => ((x : ℂ)) ^ j)
      = fun x : ℝ => ((j.descFactorial i : ℕ) : ℂ) * ((x : ℂ)) ^ (j - i) := by
  induction i generalizing j with
  | zero => simp [iteratedDeriv_zero]
  | succ i ih =>
    rw [iteratedDeriv_succ', deriv_ofReal_pow]
    have hconst : iteratedDeriv i (fun x : ℝ => (j : ℂ) * ((x : ℂ)) ^ (j - 1))
        = fun x : ℝ => (j : ℂ) * iteratedDeriv i (fun y : ℝ => ((y : ℂ)) ^ (j - 1)) x := by
      funext x
      have hcd : ContDiffAt ℝ (i : ℕ∞) (fun y : ℝ => ((y : ℂ)) ^ (j - 1)) x :=
        ((contDiff_ofReal_pow (j-1)).of_le (by exact_mod_cast le_top)).contDiffAt
      exact iteratedDeriv_const_smul hcd (j : ℂ)
    rw [hconst, ih (j - 1)]
    funext x
    rcases Nat.eq_zero_or_pos j with hj | hj
    · subst hj
      simp
    · have hdesc : (j.descFactorial (i+1) : ℕ) = j * ((j-1).descFactorial i) := by
        obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
        simpa using Nat.succ_descFactorial_succ m i
      have hsub : j - 1 - i = j - (i + 1) := by omega
      rw [hdesc, hsub]
      push_cast
      ring

theorem iteratedDeriv_ofReal_pow_zero (i j : ℕ) :
    iteratedDeriv i (fun x : ℝ => ((x : ℂ)) ^ j) 0 = if i = j then (Nat.factorial j : ℂ) else 0 := by
  rw [iteratedDeriv_ofReal_pow]
  rcases lt_trichotomy i j with h | h | h
  · have hpos : j - i ≠ 0 := by omega
    rw [if_neg (by omega)]
    simp [Complex.ofReal_zero, zero_pow hpos]
  · subst h
    rw [if_pos rfl, Nat.descFactorial_self, Nat.sub_self]
    simp
  · have hzero : j.descFactorial i = 0 := Nat.descFactorial_eq_zero_iff_lt.mpr h
    rw [if_neg (by omega), hzero]
    simp

/-- The `j`-th jet test function: the monomial `x^j/j!` localised near the origin. -/
def jetTest (j : ℕ) : SchwartzMap ℝ ℂ :=
  schwartzOfCompactSupport
    (f := fun x : ℝ => cutoffScaled (1/2) x • (((x : ℂ)) ^ j / (Nat.factorial j : ℂ)))
    ((contDiff_cutoffScaled _).smul ((contDiff_ofReal_pow j).div_const _))
    ((hasCompactSupport_cutoffScaled (by norm_num)).smul_right)

theorem jetTest_apply (j : ℕ) (x : ℝ) :
    (jetTest j : ℝ → ℂ) x = cutoffScaled (1/2) x • (((x : ℂ)) ^ j / (Nat.factorial j : ℂ)) := rfl

/-- Near the origin the jet test function is exactly the normalised monomial. -/
theorem jetTest_eventuallyEq (j : ℕ) :
    (jetTest j : ℝ → ℂ) =ᶠ[nhds (0:ℝ)] fun x : ℝ => ((x : ℂ)) ^ j / (Nat.factorial j : ℂ) := by
  have hmem : {x : ℝ | |x| < 1/2} ∈ nhds (0:ℝ) := by
    have hopen : IsOpen {x : ℝ | |x| < 1/2} := by
      have : {x : ℝ | |x| < 1/2} = (fun x : ℝ => |x|) ⁻¹' (Set.Iio (1/2)) := rfl
      rw [this]
      exact continuous_abs.isOpen_preimage _ isOpen_Iio
    exact hopen.mem_nhds (by norm_num)
  filter_upwards [hmem] with x hx
  rw [jetTest_apply, cutoffScaled_eq_one (by norm_num) (le_of_lt hx), one_smul]

/-- **The jet test functions realise the Kronecker delta.** -/
theorem iteratedDeriv_jetTest_zero (i j : ℕ) :
    iteratedDeriv i (jetTest j : ℝ → ℂ) 0 = if i = j then 1 else 0 := by
  have heq := Filter.EventuallyEq.iteratedFDeriv ℝ (jetTest_eventuallyEq j) i
  have hval : iteratedFDeriv ℝ i (jetTest j : ℝ → ℂ) 0
      = iteratedFDeriv ℝ i (fun x : ℝ => ((x : ℂ)) ^ j / (Nat.factorial j : ℂ)) 0 := heq.eq_of_nhds
  rw [iteratedDeriv_eq_iteratedFDeriv, hval, ← iteratedDeriv_eq_iteratedFDeriv]
  have hdiv : (fun x : ℝ => ((x : ℂ)) ^ j / (Nat.factorial j : ℂ))
      = fun x : ℝ => ((Nat.factorial j : ℂ)⁻¹) • (((x : ℂ)) ^ j) := by
    funext x
    rw [smul_eq_mul, div_eq_inv_mul]
  have hfun : (fun x : ℝ => ((Nat.factorial j : ℂ)⁻¹) • (((x : ℂ)) ^ j))
      = ((Nat.factorial j : ℂ)⁻¹) • (fun x : ℝ => ((x : ℂ)) ^ j) := rfl
  rw [hdiv, hfun]
  have hcd : ContDiffAt ℝ (i : ℕ∞) (fun x : ℝ => ((x : ℂ)) ^ j) 0 :=
    ((contDiff_ofReal_pow j).of_le (by exact_mod_cast le_top)).contDiffAt
  rw [iteratedDeriv_const_smul hcd, iteratedDeriv_ofReal_pow_zero]
  have hfac : ((Nat.factorial j : ℂ)) ≠ 0 := by
    simp only [ne_eq, Nat.cast_eq_zero]
    exact Nat.factorial_ne_zero j
  by_cases h : i = j
  · rw [if_pos h, if_pos h, smul_eq_mul, inv_mul_cancel₀ hfac]
  · rw [if_neg h, if_neg h, smul_zero]

end

end GaloisForLFunctions.HTGeometry
