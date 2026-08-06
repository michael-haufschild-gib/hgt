import GaloisForLFunctions.HTGeometry.LpDiagonalOperator
import GaloisForLFunctions.HTGeometry.OperatorFredholmGerm
import GaloisForLFunctions.HTGeometry.PrimeSieveRegularDeterminant

/-!
# The commuting prime sieve as a diagonal operator on `ℓ²`

The sieved diagonal operator is the multiplication by `n⁻¹` on the coordinates
indexed by the integers coprime to the primorial of the sieve, and by zero
elsewhere.  Its weights are square-summable, so it is Hilbert--Schmidt, and its
power traces are exactly the sieved zeta traces.

Consequently the polarized quotient of Hilbert--Carleman determinant germs
`det₂(1-tQ_P)/det₂(1+tQ_P)` is the exponential of the odd trace series: the even
degrees cancel between the two germs, and the odd degrees double.  This is the
identification of the determinant definition of the sieve character with its
logarithmic expansion.

The vacuum comparison is the same computation at degree two: the
Hilbert--Schmidt distance from the sieved operator to the rank-one projection on
the first coordinate is the second sieved trace minus one, which tends to zero
along any enumeration of the primes.
-/

open Filter Topology ContinuousLinearMap HilbertSchmidt
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The sieved diagonal weight: the reciprocal on the coprimality class of the
primorial, zero elsewhere. -/
def sieveWeight (P : Finset Nat.Primes) (n : ℕ) : ℂ :=
  if Nat.Coprime n (sievePrimorial P) then ((n : ℂ))⁻¹ else 0

theorem norm_sieveWeight_le_inv (P : Finset Nat.Primes) (n : ℕ) :
    ‖sieveWeight P n‖ ≤ ((n : ℝ))⁻¹ := by
  rw [sieveWeight]
  split
  · rw [norm_inv, Complex.norm_natCast]
  · rw [norm_zero]
    positivity

theorem norm_sieveWeight_le_one (P : Finset Nat.Primes) (n : ℕ) :
    ‖sieveWeight P n‖ ≤ 1 := by
  refine (norm_sieveWeight_le_inv P n).trans ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · norm_num
  · have h1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    simpa using inv_anti₀ (by norm_num : (0 : ℝ) < 1) h1

/-- Powers of the sieved weight are the sieved trace integrand. -/
theorem sieveWeight_pow (P : Finset Nat.Primes) {k : ℕ} (hk : 1 ≤ k) (n : ℕ) :
    (sieveWeight P n) ^ k
      = ((Set.indicator {n : ℕ | Nat.Coprime n (sievePrimorial P)}
            (fun n : ℕ => (((n : ℕ) : ℝ) ^ k)⁻¹) n : ℝ) : ℂ) := by
  by_cases h : Nat.Coprime n (sievePrimorial P)
  · rw [Set.indicator_of_mem (by exact h), sieveWeight, if_pos h, ← inv_pow]
    push_cast
    ring
  · rw [Set.indicator_of_notMem (by exact h), sieveWeight, if_neg h,
      zero_pow (by omega), Complex.ofReal_zero]

theorem summable_norm_sieveWeight_sq (P : Finset Nat.Primes) :
    Summable fun n : ℕ => ‖sieveWeight P n‖ ^ 2 := by
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
    (summable_natPow_inv (by norm_num : (1 : ℕ) < 2))
  calc ‖sieveWeight P n‖ ^ 2 ≤ (((n : ℝ))⁻¹) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (norm_sieveWeight_le_inv P n) 2
    _ = (((n : ℕ) : ℝ) ^ 2)⁻¹ := by rw [← inv_pow]

/-- The sum of a power of the sieved weights is the corresponding sieved
trace. -/
theorem tsum_sieveWeight_pow (P : Finset Nat.Primes) {k : ℕ} (hk : 1 ≤ k) :
    (∑' n : ℕ, (sieveWeight P n) ^ k) = ((sieveTrace P k : ℝ) : ℂ) := by
  rw [sieveTrace, sievedSum, Complex.ofReal_tsum]
  exact tsum_congr fun n => sieveWeight_pow P hk n

/-- **The commuting prime sieve as a Hilbert--Schmidt diagonal on `ℓ²`.** -/
def sieveOperator (P : Finset Nat.Primes) :
    lp (fun _ : ℕ => ℂ) 2 →L[ℂ] lp (fun _ : ℕ => ℂ) 2 :=
  diagOp (sieveWeight P) (summable_norm_sieveWeight_sq P)

theorem isHilbertSchmidt_sieveOperator (P : Finset Nat.Primes) :
    (sieveOperator P).IsHilbertSchmidt :=
  isHilbertSchmidt_diagOp _ _

theorem sieveOperator_apply (P : Finset Nat.Primes) (f : lp (fun _ : ℕ => ℂ) 2)
    (n : ℕ) : sieveOperator P f n = sieveWeight P n * f n :=
  diagOp_apply _ _ f n

/-- **The power traces of the sieve are the sieved zeta traces.** -/
theorem opTrace_sieveOperator_pow (P : Finset Nat.Primes) (n : ℕ) :
    opTrace ((sieveOperator P) ^ (n + 2)) = ((sieveTrace P (n + 2) : ℝ) : ℂ) := by
  rw [sieveOperator, opTrace_diagOp_pow _ _ (norm_sieveWeight_le_one P),
    tsum_sieveWeight_pow P (by omega)]

theorem operatorFredholmExpGerm_sieveOperator (P : Finset Nat.Primes) (z : ℂ) :
    HTGeometry.operatorFredholmExpGerm (sieveOperator P) z
      = ∑' n : ℕ, z ^ (n + 2) / ((n + 2 : ℕ) : ℂ)
          * ((sieveTrace P (n + 2) : ℝ) : ℂ) := by
  rw [HTGeometry.operatorFredholmExpGerm]
  exact tsum_congr fun n => by rw [opTrace_sieveOperator_pow]

section TraceBoundTwo

/-- The universal bound for the power traces from degree two onward. -/
def sieveTraceBoundTwo : ℝ := ∑' n : ℕ, (((n : ℕ) : ℝ) ^ 2)⁻¹

theorem sieveTraceBoundTwo_nonneg : 0 ≤ sieveTraceBoundTwo :=
  tsum_nonneg fun n => by positivity

theorem natPow_inv_le_two {k : ℕ} (hk : 2 ≤ k) (n : ℕ) :
    (((n : ℕ) : ℝ) ^ k)⁻¹ ≤ (((n : ℕ) : ℝ) ^ 2)⁻¹ := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [Nat.cast_zero, zero_pow (by omega), zero_pow (by omega)]
  · have h1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have h2 : (0 : ℝ) < ((n : ℝ)) ^ 2 := by positivity
    exact inv_anti₀ h2 (pow_le_pow_right₀ h1 hk)

theorem sieveTrace_le_boundTwo {k : ℕ} (hk : 2 ≤ k) (P : Finset Nat.Primes) :
    sieveTrace P k ≤ sieveTraceBoundTwo := by
  refine Summable.tsum_le_tsum (fun n => ?_)
    ((summable_natPow_inv (by omega)).indicator _)
    (summable_natPow_inv (by norm_num))
  by_cases h : n ∈ {n : ℕ | Nat.Coprime n (sievePrimorial P)}
  · rw [Set.indicator_of_mem h]
    exact natPow_inv_le_two hk n
  · rw [Set.indicator_of_notMem h]
    positivity

end TraceBoundTwo

section Polarization

/-- The germ series converges on the open unit disk. -/
theorem summable_expGerm_term (P : Finset Nat.Primes) {z : ℂ} (hz : ‖z‖ < 1) :
    Summable fun n : ℕ =>
      z ^ (n + 2) / ((n + 2 : ℕ) : ℂ) * ((sieveTrace P (n + 2) : ℝ) : ℂ) := by
  refine Summable.of_norm_bounded
    (g := fun n : ℕ => sieveTraceBoundTwo * ‖z‖ ^ 2 * (‖z‖) ^ n) ?_ fun n => ?_
  · exact (summable_geometric_of_lt_one (norm_nonneg _) hz).mul_left _
  · have hT0 : 0 ≤ sieveTrace P (n + 2) := sieveTrace_nonneg P _
    have hTb : sieveTrace P (n + 2) ≤ sieveTraceBoundTwo :=
      sieveTrace_le_boundTwo (by omega) P
    have hden : (1 : ℝ) ≤ ‖((n + 2 : ℕ) : ℂ)‖ := by
      rw [Complex.norm_natCast]
      have : (1 : ℕ) ≤ n + 2 := by omega
      exact_mod_cast this
    have hz2 : ‖z‖ ^ (n + 2) = ‖z‖ ^ 2 * ‖z‖ ^ n := by
      rw [← pow_add]
      ring_nf
    calc ‖z ^ (n + 2) / ((n + 2 : ℕ) : ℂ) * ((sieveTrace P (n + 2) : ℝ) : ℂ)‖
        = ‖z‖ ^ (n + 2) / ‖((n + 2 : ℕ) : ℂ)‖ * sieveTrace P (n + 2) := by
          rw [norm_mul, norm_div, norm_pow, Complex.norm_real,
            Real.norm_eq_abs, abs_of_nonneg hT0]
      _ ≤ ‖z‖ ^ (n + 2) * sieveTraceBoundTwo := by
          refine mul_le_mul ?_ hTb hT0 (by positivity)
          exact div_le_self (by positivity) hden
      _ = sieveTraceBoundTwo * ‖z‖ ^ 2 * ‖z‖ ^ n := by rw [hz2]; ring

/-- The polarized germ increment at one degree. -/
def expGermDiff (P : Finset Nat.Primes) (t : ℂ) (n : ℕ) : ℂ :=
  (-t) ^ (n + 2) / ((n + 2 : ℕ) : ℂ) * ((sieveTrace P (n + 2) : ℝ) : ℂ)
    - t ^ (n + 2) / ((n + 2 : ℕ) : ℂ) * ((sieveTrace P (n + 2) : ℝ) : ℂ)

/-- The even degrees cancel between the two polarized germs. -/
theorem expGermDiff_even (P : Finset Nat.Primes) (t : ℂ) (j : ℕ) :
    expGermDiff P t (2 * j) = 0 := by
  rw [expGermDiff, neg_pow, Even.neg_one_pow ⟨j + 1, by ring⟩, one_mul, sub_self]

/-- The odd degrees double between the two polarized germs. -/
theorem expGermDiff_odd (P : Finset Nat.Primes) (t : ℂ) (j : ℕ) :
    expGermDiff P t (2 * j + 1)
      = -2 * (t ^ (2 * j + 3) / ((2 * j + 3 : ℕ) : ℂ)
        * ((sieveTrace P (2 * j + 3) : ℝ) : ℂ)) := by
  rw [expGermDiff]
  simp only [show 2 * j + 1 + 2 = 2 * j + 3 from by omega]
  rw [neg_pow, Odd.neg_one_pow ⟨j + 1, by ring⟩]
  ring

/-- The polarized germ difference is the real odd trace series. -/
theorem expGerm_sub_eq_sieveLogPhi (P : Finset Nat.Primes) {t : ℝ} (ht : |t| < 1) :
    HTGeometry.operatorFredholmExpGerm (sieveOperator P) (-(t : ℂ))
        - HTGeometry.operatorFredholmExpGerm (sieveOperator P) (t : ℂ)
      = ((sieveLogPhi P t : ℝ) : ℂ) := by
  have hnorm : ‖(t : ℂ)‖ < 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact ht
  have hnormneg : ‖(-(t : ℂ))‖ < 1 := by rw [norm_neg]; exact hnorm
  have hsneg := summable_expGerm_term P hnormneg
  have hspos := summable_expGerm_term P hnorm
  have hsum : Summable (expGermDiff P (t : ℂ)) := hsneg.sub hspos
  have heven : Summable fun j : ℕ => expGermDiff P (t : ℂ) (2 * j) :=
    hsum.comp_injective fun a b hab => by omega
  have hodd : Summable fun j : ℕ => expGermDiff P (t : ℂ) (2 * j + 1) :=
    hsum.comp_injective fun a b hab => by omega
  have hcast : ((sieveLogPhi P t : ℝ) : ℂ)
      = -2 * ∑' j : ℕ, ((t : ℂ) ^ (2 * j + 3) / ((2 * j + 3 : ℕ) : ℂ)
          * ((sieveTrace P (2 * j + 3) : ℝ) : ℂ)) := by
    rw [sieveLogPhi, Complex.ofReal_mul, Complex.ofReal_tsum, Complex.ofReal_neg,
      Complex.ofReal_ofNat]
    refine congrArg (fun x : ℂ => (-2 : ℂ) * x) (tsum_congr fun j => ?_)
    push_cast
    ring
  rw [operatorFredholmExpGerm_sieveOperator, operatorFredholmExpGerm_sieveOperator,
    ← hsneg.tsum_sub hspos, hcast]
  have hfold : (fun n : ℕ =>
      (-(t : ℂ)) ^ (n + 2) / ((n + 2 : ℕ) : ℂ) * ((sieveTrace P (n + 2) : ℝ) : ℂ)
        - (t : ℂ) ^ (n + 2) / ((n + 2 : ℕ) : ℂ)
          * ((sieveTrace P (n + 2) : ℝ) : ℂ)) = expGermDiff P (t : ℂ) := rfl
  rw [hfold, ← tsum_even_add_odd heven hodd, tsum_congr (expGermDiff_even P (t : ℂ)),
    tsum_zero, zero_add, tsum_congr (expGermDiff_odd P (t : ℂ)), tsum_mul_left]

end Polarization

/-- The polarized determinant germ quotient `det₂(1-tQ_P)/det₂(1+tQ_P)`. -/
def sievePhi (P : Finset Nat.Primes) (t : ℂ) : ℂ :=
  HTGeometry.operatorFredholmDet2Germ (sieveOperator P) t
    / HTGeometry.operatorFredholmDet2Germ (sieveOperator P) (-t)

/-- **The determinant definition agrees with the logarithmic expansion.**  The
polarized quotient of Hilbert--Carleman germs of the sieved operator is the
exponential of the odd trace series. -/
theorem sievePhi_eq_exp_sieveLogPhi (P : Finset Nat.Primes) {t : ℝ} (ht : |t| < 1) :
    sievePhi P (t : ℂ) = Complex.exp ((sieveLogPhi P t : ℝ) : ℂ) := by
  rw [sievePhi, HTGeometry.operatorFredholmDet2Germ,
    HTGeometry.operatorFredholmDet2Germ, ← Complex.exp_sub]
  congr 1
  rw [neg_sub_neg]
  exact expGerm_sub_eq_sieveLogPhi P ht

section Vacuum

/-- The vacuum weight: the rank-one projection on the first coordinate. -/
def vacuumWeight (n : ℕ) : ℂ := if n = 1 then 1 else 0

theorem summable_norm_vacuumWeight_sq :
    Summable fun n : ℕ => ‖vacuumWeight n‖ ^ 2 := by
  refine summable_of_ne_finset_zero (s := {1}) fun n hn => ?_
  simp only [Finset.mem_singleton] at hn
  rw [vacuumWeight, if_neg hn, norm_zero]
  norm_num

/-- The vacuum projection on `ℓ²`. -/
def vacuumProjection : lp (fun _ : ℕ => ℂ) 2 →L[ℂ] lp (fun _ : ℕ => ℂ) 2 :=
  diagOp vacuumWeight summable_norm_vacuumWeight_sq

theorem sieveWeight_one (P : Finset Nat.Primes) : sieveWeight P 1 = 1 := by
  rw [sieveWeight, if_pos (Nat.coprime_one_left _)]
  norm_num

/-- The pointwise vacuum defect of the sieved weights. -/
theorem norm_sieveWeight_sub_vacuumWeight_sq (P : Finset Nat.Primes) (n : ℕ) :
    ‖sieveWeight P n - vacuumWeight n‖ ^ 2
      = Set.indicator {n : ℕ | Nat.Coprime n (sievePrimorial P)}
          (fun n : ℕ => (((n : ℕ) : ℝ) ^ 2)⁻¹) n
        - (if n = 1 then (1 : ℝ) else 0) := by
  by_cases hn : n = 1
  · subst hn
    rw [sieveWeight_one, vacuumWeight, if_pos rfl, sub_self, norm_zero,
      Set.indicator_of_mem (by exact Nat.coprime_one_left _), if_pos rfl]
    norm_num
  · rw [vacuumWeight, if_neg hn, sub_zero, if_neg hn, sub_zero]
    have hsq := sieveWeight_pow P (k := 2) (by omega) n
    have : ‖sieveWeight P n‖ ^ 2 = ‖(sieveWeight P n) ^ 2‖ := by
      rw [norm_pow]
    rw [this, hsq, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
    by_cases h : n ∈ {n : ℕ | Nat.Coprime n (sievePrimorial P)}
    · rw [Set.indicator_of_mem h]
      positivity
    · rw [Set.indicator_of_notMem h]

/-- **The Hilbert--Schmidt vacuum defect.**  The squared Hilbert--Schmidt
distance from the sieve to the vacuum projection is the second sieved trace minus
one. -/
theorem hsNormSq_sieveOperator_sub_vacuum (P : Finset Nat.Primes) :
    ContinuousLinearMap.hsNormSq (sieveOperator P - vacuumProjection)
      = sieveTrace P 2 - 1 := by
  have hsub : Summable fun n : ℕ => ‖sieveWeight P n - vacuumWeight n‖ ^ 2 := by
    refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
      ((summable_natPow_inv (by norm_num : (1 : ℕ) < 2)).indicator
        {n : ℕ | Nat.Coprime n (sievePrimorial P)})
    rw [norm_sieveWeight_sub_vacuumWeight_sq P n]
    have hnn : (0 : ℝ) ≤ if n = 1 then (1 : ℝ) else 0 := by split <;> norm_num
    linarith
  rw [sieveOperator, vacuumProjection, diagOp_sub _ _ _ _ hsub, hsNormSq_diagOp]
  rw [tsum_congr (norm_sieveWeight_sub_vacuumWeight_sq P),
    Summable.tsum_sub
      ((summable_natPow_inv (by norm_num : (1 : ℕ) < 2)).indicator _)
      (summable_of_ne_finset_zero (s := {1}) fun n hn => by
        simp only [Finset.mem_singleton] at hn
        rw [if_neg hn])]
  congr 1
  simp

/-- **Cofinal Hilbert--Schmidt convergence to the vacuum.**  Along any
enumeration of the primes the sieved operator converges to the rank-one vacuum
projection in Hilbert--Schmidt norm. -/
theorem tendsto_hsNormSq_sieveOperator_sub_vacuum (e : ℕ ≃ Nat.Primes) :
    Tendsto (fun m : ℕ =>
        ContinuousLinearMap.hsNormSq (sieveOperator (sievePrefix e m) - vacuumProjection))
      atTop (𝓝 0) := by
  have h := tendsto_sieveTrace_sievePrefix e (k := 2) (by norm_num)
  have hzero : (1 : ℝ) - 1 = 0 := by norm_num
  refine Tendsto.congr (fun m => (hsNormSq_sieveOperator_sub_vacuum _).symm) ?_
  rw [← hzero]
  exact h.sub tendsto_const_nhds

end Vacuum

end

end GaloisForLFunctions.HTGeometry
