import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.PrimeResidueWindowsConvergeToTheirUnitMean

/-!
# Uniform comparison for every finite residue Gram packet

The actual residue masses determine one error, independent of the feature
family and its coefficients. This error tends to zero and bounds every
signed residue reading in the full residue norm. Applied to squares, it
compares complete Gram forms while retaining non-unit prime powers.
-/

noncomputable section

open Finset Filter Topology
open scoped Classical

namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory

open RenormalizedArithmeticPotentialTheory

/-- The indicator of one residue class. -/
def primeResidueIndicator {q : ℕ} (r : ZMod q) (u : ZMod q) : ℝ :=
  if u = r then 1 else 0

/-- The exact error of one residue mass relative to its unit mean. -/
def primeResidueWindowError (q : ℕ) [NeZero q] (A B N : ℕ) (r : ZMod q) : ℝ :=
  residuePrimeWindow q (primeResidueIndicator r) A B N -
    primeClassKappa q (primeResidueIndicator r) * (Real.log B - Real.log A)

/-- One actual source error controls every finite feature family. -/
def primeResidueWindowErrorMass (q : ℕ) [NeZero q] (A B N : ℕ) : ℝ :=
  ∑ r : ZMod q, |primeResidueWindowError q A B N r|

theorem primeResidueWindowErrorMass_nonneg (q : ℕ) [NeZero q] (A B N : ℕ) :
    0 ≤ primeResidueWindowErrorMass q A B N :=
  sum_nonneg fun _ _ => abs_nonneg _

/-- Exact decomposition into the masses of individual residue classes. -/
theorem residuePrimeWindow_eq_indicator_sum {q : ℕ} [NeZero q]
    (F : ZMod q → ℝ) (A B N : ℕ) :
    residuePrimeWindow q F A B N =
      ∑ r : ZMod q, F r * residuePrimeWindow q (primeResidueIndicator r) A B N := by
  symm
  simp only [residuePrimeWindow, mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun k _ => ?_
  have he : ∀ r : ZMod q,
      F r * (primeResidueIndicator r (k : ZMod q) *
        (ArithmeticFunction.vonMangoldt k : ℝ) / k) =
      if r = (k : ZMod q) then F (k : ZMod q) *
        (ArithmeticFunction.vonMangoldt k : ℝ) / k else 0 := by
    intro r
    by_cases hr : r = (k : ZMod q)
    · subst r
      simp [primeResidueIndicator, mul_div_assoc]
    · simp only [primeResidueIndicator, if_neg hr, if_neg (Ne.symm hr),
        zero_mul, zero_div, mul_zero]
  simp_rw [he]
  rw [sum_ite_eq', if_pos (mem_univ _)]

/-- The unit mean has the same finite residue-coordinate decomposition. -/
theorem primeClassKappa_eq_indicator_sum {q : ℕ} [NeZero q]
    (F : ZMod q → ℝ) :
    primeClassKappa q F =
      ∑ r : ZMod q, F r * primeClassKappa q (primeResidueIndicator r) := by
  have h : (∑ u : (ZMod q)ˣ, F u) =
      ∑ r : ZMod q, F r * ∑ u : (ZMod q)ˣ, primeResidueIndicator r u := by
    symm
    simp only [mul_sum]
    rw [sum_comm]
    refine sum_congr rfl fun u _ => ?_
    simp only [primeResidueIndicator, mul_ite, mul_one, mul_zero]
    rw [sum_ite_eq, if_pos (mem_univ _)]
  unfold primeClassKappa
  rw [h, sum_div]
  exact sum_congr rfl fun r _ => by ring

/-- The source discrepancy is exactly the pairing with its residue errors. -/
theorem residuePrimeWindow_sub_unitMean_eq {q : ℕ} [NeZero q]
    (F : ZMod q → ℝ) (A B N : ℕ) :
    residuePrimeWindow q F A B N -
        primeClassKappa q F * (Real.log B - Real.log A) =
      ∑ r : ZMod q, F r * primeResidueWindowError q A B N r := by
  rw [residuePrimeWindow_eq_indicator_sum, primeClassKappa_eq_indicator_sum,
    sum_mul, ← sum_sub_distrib]
  exact sum_congr rfl fun r _ => by
    unfold primeResidueWindowError
    ring

/-- A finite, exact comparison valid for every signed residue pattern. -/
theorem abs_residuePrimeWindow_sub_unitMean_le {q : ℕ} [NeZero q]
    (F : ZMod q → ℝ) (A B N : ℕ) :
    |residuePrimeWindow q F A B N -
        primeClassKappa q F * (Real.log B - Real.log A)| ≤
      primeResidueWindowErrorMass q A B N * ∑ r : ZMod q, |F r| := by
  rw [residuePrimeWindow_sub_unitMean_eq, mul_sum]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun r _ => ?_)
  rw [abs_mul]
  have hr : |primeResidueWindowError q A B N r| ≤ primeResidueWindowErrorMass q A B N :=
    single_le_sum (fun u _ => abs_nonneg (primeResidueWindowError q A B N u)) (mem_univ r)
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left hr (abs_nonneg (F r))

/-- The common source error vanishes at every fixed conductor and window. -/
theorem tendsto_primeResidueWindowErrorMass {q : ℕ} [NeZero q]
    {A B : ℕ} (hA : 0 < A) (hAB : A ≤ B) :
    Tendsto (primeResidueWindowErrorMass q A B) atTop (𝓝 0) := by
  have h (r : ZMod q) : Tendsto (fun N => |primeResidueWindowError q A B N r|)
      atTop (𝓝 0) := by
    have ht := ((tendsto_residuePrimeWindow (primeResidueIndicator r) hA hAB).sub_const
      (primeClassKappa q (primeResidueIndicator r) * (Real.log B - Real.log A))).abs
    simpa only [sub_self, abs_zero, primeResidueWindowError] using ht
  change Tendsto (fun N => ∑ r : ZMod q, |primeResidueWindowError q A B N r|) atTop (𝓝 0)
  simpa only [sum_const_zero] using
    tendsto_finsetSum (univ : Finset (ZMod q)) (fun r _ => h r)

/-- One horizon controls every signed reading, including patterns chosen
after the horizon; no feature dimension enters the error constant. -/
theorem eventually_residuePrimeWindow_uniform {q : ℕ} [NeZero q]
    {A B : ℕ} (hA : 0 < A) (hAB : A ≤ B) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ F : ZMod q → ℝ,
      |residuePrimeWindow q F A B N -
          primeClassKappa q F * (Real.log B - Real.log A)| ≤
        ε * ∑ r : ZMod q, |F r| := by
  filter_upwards [(tendsto_primeResidueWindowErrorMass (q := q) hA hAB).eventually
    (gt_mem_nhds hε)] with N hN
  intro F
  exact (abs_residuePrimeWindow_sub_unitMean_le F A B N).trans
    (mul_le_mul_of_nonneg_right hN.le (sum_nonneg fun r _ => abs_nonneg _))

/-- Every finite Gram packet is compared in its full residue square norm.
The coefficient vector and the feature family may both depend on height. -/
theorem eventually_primeWindow_all_Gram_packets {ι : Type*} {q : ℕ} [NeZero q]
    {A B : ℕ} (hA : 0 < A) (hAB : A ≤ B) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ (s : Finset ι) (v : ι → ZMod q → ℝ) (x : ι → ℝ),
      |residuePrimeWindow q (fun r => (∑ i ∈ s, x i * v i r) ^ (2 : ℕ)) A B N -
          primeClassKappa q (fun r => (∑ i ∈ s, x i * v i r) ^ (2 : ℕ)) *
            (Real.log B - Real.log A)| ≤
        ε * ∑ r : ZMod q, (∑ i ∈ s, x i * v i r) ^ (2 : ℕ) := by
  filter_upwards [eventually_residuePrimeWindow_uniform (q := q) hA hAB hε] with N hN
  intro s v x
  calc
    _ ≤ ε * ∑ r : ZMod q, |(∑ i ∈ s, x i * v i r) ^ (2 : ℕ)| :=
      hN (fun r => (∑ i ∈ s, x i * v i r) ^ (2 : ℕ))
    _ = _ := congrArg (fun t : ℝ => ε * t)
      (sum_congr rfl fun r _ => abs_of_nonneg (sq_nonneg (∑ i ∈ s, x i * v i r)))


/-- The same common horizon controls complex Gram packets, including
primitive-root prefix features and all their mixed coefficients. -/
theorem eventually_primeWindow_all_complex_Gram_packets {ι : Type*}
    {q : ℕ} [NeZero q] {A B : ℕ} (hA : 0 < A) (hAB : A ≤ B)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ (s : Finset ι) (v : ι → ZMod q → ℂ) (x : ι → ℂ),
      |residuePrimeWindow q (fun r => Complex.normSq (∑ i ∈ s, x i * v i r)) A B N -
          primeClassKappa q (fun r => Complex.normSq (∑ i ∈ s, x i * v i r)) *
            (Real.log B - Real.log A)| ≤
        ε * ∑ r : ZMod q, Complex.normSq (∑ i ∈ s, x i * v i r) := by
  filter_upwards [eventually_residuePrimeWindow_uniform (q := q) hA hAB hε] with N hN
  intro s v x
  simpa only [abs_of_nonneg (Complex.normSq_nonneg _)] using
    hN (fun r => Complex.normSq (∑ i ∈ s, x i * v i r))

/-- Every actual residue mass is positive, including the non-unit prime powers. -/
theorem residuePrimeWindow_nonneg {q : ℕ} (F : ZMod q → ℝ)
    (hF : ∀ r, 0 ≤ F r) (A B N : ℕ) :
    0 ≤ residuePrimeWindow q F A B N := by
  unfold residuePrimeWindow
  exact sum_nonneg fun k _ => div_nonneg
    (mul_nonneg (hF _) ArithmeticFunction.vonMangoldt_nonneg) (Nat.cast_nonneg k)

/-- For lower bounds, non-unit prime powers have the favorable sign.
One horizon therefore dominates the unit model for every positive reading. -/
theorem eventually_residuePrimeWindow_dominates_unitMean {q : ℕ} [NeZero q]
    {A B : ℕ} (hA : 0 < A) (hAB : A ≤ B) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ F : ZMod q → ℝ, (∀ r, 0 ≤ F r) →
      (Real.log B - Real.log A - ε) * primeClassKappa q F ≤
        residuePrimeWindow q F A B N := by
  have hi (r : ZMod q) : ∀ u, 0 ≤ primeResidueIndicator r u := by
    intro u
    unfold primeResidueIndicator
    split_ifs <;> norm_num
  have hr (r : ZMod q) : ∀ᶠ N : ℕ in atTop,
      (Real.log B - Real.log A - ε) * primeClassKappa q (primeResidueIndicator r) ≤
        residuePrimeWindow q (primeResidueIndicator r) A B N := by
    have hk : 0 ≤ primeClassKappa q (primeResidueIndicator r) :=
      div_nonneg (sum_nonneg fun u _ => hi r u) (Nat.cast_nonneg _)
    rcases eq_or_lt_of_le hk with hz | hpos
    · exact Filter.Eventually.of_forall fun N => by
        rw [← hz, mul_zero]
        exact residuePrimeWindow_nonneg _ (hi r) A B N
    · have hlt : (Real.log B - Real.log A - ε) *
          primeClassKappa q (primeResidueIndicator r) <
          primeClassKappa q (primeResidueIndicator r) * (Real.log B - Real.log A) := by
        have hprod := mul_pos hε hpos
        nlinarith only [hprod]
      exact ((tendsto_residuePrimeWindow (primeResidueIndicator r) hA hAB).eventually
        (lt_mem_nhds hlt)).mono fun _ h => h.le
  filter_upwards [Filter.eventually_all.mpr hr] with N hN
  intro F hF
  rw [residuePrimeWindow_eq_indicator_sum, primeClassKappa_eq_indicator_sum, mul_sum]
  refine sum_le_sum fun r _ => ?_
  calc
    _ = F r * ((Real.log B - Real.log A - ε) *
        primeClassKappa q (primeResidueIndicator r)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (hN r) (hF r)

/-- A simultaneous lower operator bound in the unit Gram itself.
No full-residue penalty is needed, even on its null directions. -/
theorem eventually_primeWindow_dominates_all_complex_Gram_packets {ι : Type*}
    {q : ℕ} [NeZero q] {A B : ℕ} (hA : 0 < A) (hAB : A ≤ B)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ (s : Finset ι) (v : ι → ZMod q → ℂ) (x : ι → ℂ),
      (Real.log B - Real.log A - ε) *
          primeClassKappa q (fun r => Complex.normSq (∑ i ∈ s, x i * v i r)) ≤
        residuePrimeWindow q (fun r => Complex.normSq (∑ i ∈ s, x i * v i r)) A B N := by
  filter_upwards [eventually_residuePrimeWindow_dominates_unitMean (q := q) hA hAB hε]
    with N hN
  intro s v x
  exact hN _ (fun _ => Complex.normSq_nonneg _)

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory

#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.abs_residuePrimeWindow_sub_unitMean_le
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.tendsto_primeResidueWindowErrorMass
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.eventually_primeWindow_all_Gram_packets

#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.eventually_primeWindow_all_complex_Gram_packets
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.eventually_primeWindow_dominates_all_complex_Gram_packets
