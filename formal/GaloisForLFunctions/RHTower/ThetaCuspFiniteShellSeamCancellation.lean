import GaloisForLFunctions.RHTower.PrimeArchThetaGaussianApertureBalance
import GaloisForLFunctions.RHTower.XiCTaylorThetaTailSeamJets

/-!
# Finite theta-shell seam cancellation obstruction

Every positive theta shell has an explicit logarithmic slope at the modular seam.  The first
shell has positive slope, every later shell has negative slope, and the completed infinite source
has total slope zero by reflection.  It follows that every nonempty finite canonical shell prefix
has strictly positive seam derivative: the missing negative slope is carried by its infinite tail.

Thus no finite shell prefix is smoothly even at the seam.  Any high-frequency argument based on
even reflection of finitely many shells retains a nonzero cusp current; cancellation of that
current is intrinsically cofinal in the complete theta source.
-/

open Complex Real MeasureTheory Set Filter Topology Polynomial
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Exact logarithmic slope of the `n`th positive theta shell at the modular seam. -/
def thetaCuspAtomBoundaryLogSlope (n : ℕ) : ℝ :=
  9 / 2 - 2 * Real.pi * (n : ℝ) ^ 2 +
    6 / (2 * Real.pi * (n : ℝ) ^ 2 - 3)

/-- Every positive-index shell is strictly positive at the modular seam. -/
theorem thetaCuspSourceTerm_zero_pos
    {n : ℕ} (hn : 0 < n) :
    0 < thetaCuspSourceTerm 0 n := by
  rw [thetaCuspSourceTerm, thetaCuspSeed]
  norm_num
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hsq : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
  have : 0 < 2 * Real.pi * (n : ℝ) ^ 2 - 3 := by nlinarith
  rw [show 2 * Real.pi * (n : ℝ) ^ 4 - 3 * (n : ℝ) ^ 2 =
      (n : ℝ) ^ 2 * (2 * Real.pi * (n : ℝ) ^ 2 - 3) by ring]
  positivity

/-- Every shell after the first has strictly negative logarithmic seam slope. -/
theorem thetaCuspAtomBoundaryLogSlope_neg
    {n : ℕ} (hn : 2 ≤ n) :
    thetaCuspAtomBoundaryLogSlope n < 0 := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hsq : (4 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
  have hden : 21 < 2 * Real.pi * (n : ℝ) ^ 2 - 3 := by nlinarith
  have hfrac : 6 / (2 * Real.pi * (n : ℝ) ^ 2 - 3) < (2 / 7 : ℝ) := by
    rw [div_lt_iff₀ (by linarith : 0 < 2 * Real.pi * (n : ℝ) ^ 2 - 3)]
    nlinarith
  unfold thetaCuspAtomBoundaryLogSlope
  nlinarith

/-- Exact endpoint derivative of every shell, including the identically zero shell `n = 0`. -/
theorem iteratedDeriv_one_thetaCuspSourceTerm_zero_eq_slope
    (n : ℕ) :
    iteratedDeriv 1 (fun x : ℝ => thetaCuspSourceTerm x n) 0 =
      thetaCuspAtomBoundaryLogSlope n * thetaCuspSourceTerm 0 n := by
  rw [iteratedDeriv_thetaCuspSourceTerm_eq_polynomialAtom]
  simp [thetaCuspPolynomialAtom, thetaCuspLogDerivativePolynomial,
    thetaCuspLogDerivativeStep, thetaCuspSeedPolynomial,
    thetaCuspAtomBoundaryLogSlope, thetaCuspSourceTerm, thetaCuspSeed]
  by_cases hn : n = 0
  · subst n
    norm_num
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
    have hden : 2 * Real.pi * (n : ℝ) ^ 2 - 3 ≠ 0 := by
      have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
      have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hnpos
      nlinarith [sq_nonneg ((n : ℝ) - 1)]
    have hder :
        eval (n : ℝ) (derivative (C Real.pi ^ 2)) = 0 := by
      rw [Polynomial.derivative_pow, Polynomial.derivative_C]
      simp
    rw [hder]
    field_simp [hden]
    ring

/-- Every shell after the first has strictly negative derivative at the modular seam. -/
theorem iteratedDeriv_one_thetaCuspSourceTerm_zero_neg
    {n : ℕ} (hn : 2 ≤ n) :
    iteratedDeriv 1 (fun x : ℝ => thetaCuspSourceTerm x n) 0 < 0 := by
  rw [iteratedDeriv_one_thetaCuspSourceTerm_zero_eq_slope]
  exact mul_neg_of_neg_of_pos
    (thetaCuspAtomBoundaryLogSlope_neg hn)
    (thetaCuspSourceTerm_zero_pos (by omega))

/-- First `N` positive theta shells, with the identically zero shell `0` retained. -/
def thetaCuspFiniteShellPrefix (N : ℕ) (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.range (N + 1), thetaCuspSourceTerm x n

theorem hasDerivAt_thetaCuspFiniteShellPrefix (N : ℕ) :
    HasDerivAt (thetaCuspFiniteShellPrefix N)
      (∑ n ∈ Finset.range (N + 1),
        iteratedDeriv 1 (fun x : ℝ => thetaCuspSourceTerm x n) 0) 0 := by
  have h := HasDerivAt.sum (u := Finset.range (N + 1))
    (fun n _hn => hasDerivAt_iteratedDeriv_thetaCuspSourceTerm 0 n 0)
  simp only [iteratedDeriv_zero, zero_add] at h
  convert h using 1
  funext x
  simp only [thetaCuspFiniteShellPrefix, Finset.sum_apply]

/-- Reflection makes the complete infinite shell derivative vanish exactly. -/
theorem tsum_iteratedDeriv_one_thetaCuspSourceTerm_zero_eq_zero :
    (∑' n : ℕ,
      iteratedDeriv 1 (fun x : ℝ => thetaCuspSourceTerm x n) 0) = 0 := by
  change thetaCuspFullDerivative 1 0 = 0
  rw [← congrFun (iteratedDeriv_thetaCuspFullSource 1) 0]
  exact iteratedDeriv_thetaCuspFullSource_zero_of_odd (by norm_num)

/-- Every nonempty finite canonical shell prefix has strictly positive seam derivative. -/
theorem thetaCuspFiniteShellPrefix_boundary_derivative_pos
    {N : ℕ} (hN : 1 ≤ N) :
    0 < ∑ n ∈ Finset.range (N + 1),
      iteratedDeriv 1 (fun x : ℝ => thetaCuspSourceTerm x n) 0 := by
  let f : ℕ → ℝ := fun n =>
    iteratedDeriv 1 (fun x : ℝ => thetaCuspSourceTerm x n) 0
  have hf : Summable f := summable_iteratedDeriv_thetaCuspSourceTerm 1 0
  have htail : Summable (fun k : ℕ => f (k + (N + 1))) :=
    (summable_nat_add_iff (N + 1)).mpr hf
  have htailNeg : (∑' k : ℕ, f (k + (N + 1))) < 0 := by
    have hnegSummable : Summable (fun k : ℕ => -f (k + (N + 1))) :=
      htail.neg
    have hnonneg (k : ℕ) : 0 ≤ -f (k + (N + 1)) := by
      exact neg_nonneg.mpr (iteratedDeriv_one_thetaCuspSourceTerm_zero_neg
        (n := k + (N + 1)) (by omega)).le
    have hstrict : 0 < -f (0 + (N + 1)) := by
      exact neg_pos.mpr (iteratedDeriv_one_thetaCuspSourceTerm_zero_neg
        (n := 0 + (N + 1)) (by omega))
    have hpos := hnegSummable.tsum_pos hnonneg 0 hstrict
    rw [tsum_neg] at hpos
    exact neg_pos.mp hpos
  have hsplit := hf.sum_add_tsum_nat_add (N + 1)
  have htotal :
      (∑ n ∈ Finset.range (N + 1), f n) +
        (∑' k : ℕ, f (k + (N + 1))) = 0 := by
    rw [hsplit]
    exact tsum_iteratedDeriv_one_thetaCuspSourceTerm_zero_eq_zero
  change 0 < ∑ n ∈ Finset.range (N + 1), f n
  linarith

theorem deriv_thetaCuspFiniteShellPrefix_zero_pos
    {N : ℕ} (hN : 1 ≤ N) :
    0 < deriv (thetaCuspFiniteShellPrefix N) 0 := by
  rw [(hasDerivAt_thetaCuspFiniteShellPrefix N).deriv]
  exact thetaCuspFiniteShellPrefix_boundary_derivative_pos hN

/-- No nonempty finite canonical prefix inherits the evenness of the completed source. -/
theorem thetaCuspFiniteShellPrefix_not_even
    {N : ℕ} (hN : 1 ≤ N) :
    ¬Function.Even (thetaCuspFiniteShellPrefix N) := by
  intro heven
  have hder := hasDerivAt_thetaCuspFiniteShellPrefix N
  have hderNegZero : HasDerivAt (thetaCuspFiniteShellPrefix N)
      (∑ n ∈ Finset.range (N + 1),
        iteratedDeriv 1 (fun x : ℝ => thetaCuspSourceTerm x n) 0)
      (-(0 : ℝ)) := by
    simpa using hder
  have hneg : HasDerivAt
      (fun x : ℝ => thetaCuspFiniteShellPrefix N (-x))
      (-(∑ n ∈ Finset.range (N + 1),
        iteratedDeriv 1 (fun x : ℝ => thetaCuspSourceTerm x n) 0)) 0 := by
    simpa only [Function.comp_apply, neg_zero, mul_neg, mul_one] using
      hderNegZero.comp (0 : ℝ) (hasDerivAt_neg (0 : ℝ))
  have heq : (fun x : ℝ => thetaCuspFiniteShellPrefix N (-x)) =
      thetaCuspFiniteShellPrefix N := by
    funext x
    exact heven x
  rw [heq] at hneg
  have hslope := hder.unique hneg
  have hpos := thetaCuspFiniteShellPrefix_boundary_derivative_pos hN
  linarith

end

end RHTower
