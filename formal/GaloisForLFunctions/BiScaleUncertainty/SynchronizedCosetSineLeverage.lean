import GaloisForLFunctions.BiScaleUncertainty.TriangularGramSineBound
import GaloisForLFunctions.BiScaleUncertainty.MultiChainToeplitzGramCoupling
import GaloisForLFunctions.HTGeometry.FiniteExponentialHankel
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-!
# Synchronized odd-coset sine leverage

Actual compactly supported translates define finite Hilbert frames. Their within-chain and
cross-chain matrices give a sine improvement over the independent-chain Gram envelope, with
all imperfect integer-log zeros retained as explicit operator-norm errors. The arithmetic
entry identities identify those errors and the anchor samples on the actual integer grid.
No orthogonality, contractivity, nilpotence, or grid-zero premise is assumed.
-/

open MeasureTheory
open scoped BigOperators CompactlySupported InnerProductSpace
namespace GaloisForLFunctions.BiScaleUncertainty
open RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm RHTower.WeilMarkovPole
noncomputable section

private theorem translate_memLp (f : C_c(ℝ, ℝ)) (t : ℝ) :
    MemLp (fun u : ℝ => (f (u+t) : ℂ)) 2 volume :=
  (Complex.continuous_ofReal.comp (f.continuous.comp (continuous_add_const t))).memLp_of_hasCompactSupport
      ((hasCompactSupport_comp_add f.hasCompactSupport t).comp_left Complex.ofReal_zero)

/-- Actual translate as a Hilbert-space vector, with integrability proved from its data. -/
def translationFeature (f : C_c(ℝ, ℝ)) (t : ℝ) : Lp ℂ 2 (volume : Measure ℝ) :=
  (translate_memLp f t).toLp (fun u : ℝ => (f (u+t) : ℂ))

/-- Hilbert Gram entries are exactly the actual autocorrelation samples. -/
theorem translationFeature_inner (f : C_c(ℝ, ℝ)) (x y : ℝ) :
    inner ℂ (translationFeature f x) (translationFeature f y) =
      (autocorr f (y-x) : ℂ) := by
  rw [L2.inner_def]
  have he : (∫ u, inner ℂ (translationFeature f x u) (translationFeature f y u)) =
      ∫ u, (f (u+x) : ℂ) * (f (u+y) : ℂ) := by
    apply integral_congr_ae
    filter_upwards [(translate_memLp f x).coeFn_toLp, (translate_memLp f y).coeFn_toLp] with u hx hy
    change translationFeature f x u = _ at hx
    change translationFeature f y u = _ at hy
    rw [hx, hy]
    simp only [RCLike.inner_apply, Complex.conj_ofReal]
    ring
  rw [he]
  simp_rw [← Complex.ofReal_mul]
  have hcast : (∫ u, ((f (u+x) * f (u+y) : ℝ) : ℂ)) =
      Complex.ofReal (∫ u, f (u+x)*f (u+y)) := integral_ofReal
  rw [hcast, integral_shift_mul_shift]

/-- The Hilbert packet norm is exactly the full autocorrelation Gram energy. -/
theorem translationFeature_packet_energy {ι : Type*} (f : C_c(ℝ, ℝ))
    (s : Finset ι) (w t : ι → ℝ) :
    ‖∑ i ∈ s, (w i : ℂ) • translationFeature f (t i)‖ ^ 2 =
      translationGramEnergy f s w t := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ)]
  rw [sum_inner]
  simp_rw [inner_sum, inner_smul_left, inner_smul_right, translationFeature_inner]
  simp [translationGramEnergy, mul_assoc]

/-- A complete finite dyadic chain of actual translation vectors. -/
def dyadicFeatureFamily (f : C_c(ℝ, ℝ)) (n : ℕ) (base : ℝ) (i : Fin (n+1)) :=
  translationFeature f (base + (i : ℝ) * Real.log 2)

/-- The within-chain Gram matrix, independent of the base point. -/
def dyadicWithinGram (f : C_c(ℝ, ℝ)) (n : ℕ) : Matrix (Fin (n+1)) (Fin (n+1)) ℂ :=
  fun i j => (autocorr f (((j : ℝ)-(i : ℝ))*Real.log 2) : ℂ)

/-- Cross-coset Gram entries in the orientation with arithmetic lower-triangle zeros. -/
def dyadicCrossGram (f : C_c(ℝ, ℝ)) (n : ℕ) (b : ℝ) : Matrix (Fin (n+1)) (Fin (n+1)) ℂ :=
  fun i j => (autocorr f (((j : ℝ)-(i : ℝ))*Real.log 2-b) : ℂ)

/-- Deviation of a dyadic chain from an orthogonal equal-norm frame. -/
def dyadicWithinDefect (f : C_c(ℝ, ℝ)) (n : ℕ) :=
  gramMatrixOperator (dyadicWithinGram f n) - (autocorr f 0 : ℂ) • 1

theorem frameCrossGram_dyadicWithin (f : C_c(ℝ, ℝ)) (n : ℕ) (base : ℝ) :
    frameCrossGram (dyadicFeatureFamily f n base) (dyadicFeatureFamily f n base) =
      dyadicWithinGram f n := by
  ext i j
  simp only [frameCrossGram, dyadicFeatureFamily, translationFeature_inner, dyadicWithinGram]
  congr 2
  ring

theorem frameCrossGram_dyadicCross (f : C_c(ℝ, ℝ)) (n : ℕ) (base b : ℝ) :
    frameCrossGram (dyadicFeatureFamily f n (base+b)) (dyadicFeatureFamily f n base) =
      dyadicCrossGram f n b := by
  ext i j
  simp only [frameCrossGram, dyadicFeatureFamily, translationFeature_inner, dyadicCrossGram]
  congr 2
  ring

theorem translationFeature_norm_sq (f : C_c(ℝ, ℝ)) (t : ℝ) :
    ‖translationFeature f t‖ ^ 2 = autocorr f 0 := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), translationFeature_inner]
  simp

theorem frameGramDefect_dyadicFeature (f : C_c(ℝ, ℝ)) (n : ℕ) (base : ℝ) :
    frameGramDefect (dyadicFeatureFamily f n base) = dyadicWithinDefect f n := by
  unfold frameGramDefect dyadicWithinDefect
  rw [frameCrossGram_dyadicWithin]
  simp only [dyadicFeatureFamily, Fin.val_zero, Nat.cast_zero, zero_mul, add_zero,
    translationFeature_norm_sq]

theorem dyadicSynthesis_norm_sq_le (f : C_c(ℝ, ℝ)) (n : ℕ) (base : ℝ) :
    ‖HTGeometry.finiteSynthesis (dyadicFeatureFamily f n base)‖ ^ 2 ≤
      autocorr f 0 + ‖dyadicWithinDefect f n‖ := by
  have h := finiteSynthesis_norm_sq_le_defect (dyadicFeatureFamily f n base)
  rw [frameGramDefect_dyadicFeature] at h
  simpa only [dyadicFeatureFamily, Fin.val_zero, Nat.cast_zero, zero_mul, add_zero,
    translationFeature_norm_sq] using h

/-- The same real coefficients used in both chains, regarded in Euclidean coefficient space. -/
def realChainCoefficients {n : ℕ} (c : Fin (n+1) → ℝ) : EuclideanSpace ℂ (Fin (n+1)) :=
  WithLp.toLp 2 fun i => (c i : ℂ)

theorem realChainCoefficients_norm_sq {n : ℕ} (c : Fin (n+1) → ℝ) :
    ‖realChainCoefficients c‖ ^ 2 = ∑ i, c i ^ 2 := by
  simp [EuclideanSpace.norm_sq_eq, realChainCoefficients]

/-- Nodes of two equally long dyadic chains. -/
def dyadicPairNode (n : ℕ) (base b : ℝ) : Fin (n+1) ⊕ Fin (n+1) → ℝ :=
  Sum.elim (fun i => base+(i : ℝ)*Real.log 2) (fun i => base+b+(i : ℝ)*Real.log 2)

/-- Full coupled Gram energy of the synchronized chains. -/
def synchronizedDyadicGramEnergy (f : C_c(ℝ, ℝ)) (n : ℕ) (base b : ℝ)
    (c : Fin (n+1) → ℝ) : ℝ :=
  translationGramEnergy f Finset.univ (Sum.elim c c) (dyadicPairNode n base b)

theorem synchronizedDyadicGramEnergy_eq_norm (f : C_c(ℝ, ℝ)) (n : ℕ) (base b : ℝ)
    (c : Fin (n+1) → ℝ) :
    synchronizedDyadicGramEnergy f n base b c =
      ‖HTGeometry.finiteSynthesis (dyadicFeatureFamily f n base) (realChainCoefficients c) +
        HTGeometry.finiteSynthesis (dyadicFeatureFamily f n (base+b)) (realChainCoefficients c)‖ ^ 2 := by
  have h := translationFeature_packet_energy f Finset.univ (Sum.elim c c) (dyadicPairNode n base b)
  simpa [synchronizedDyadicGramEnergy, HTGeometry.finiteSynthesis_apply,
    realChainCoefficients, dyadicFeatureFamily, dyadicPairNode, Fintype.sum_sum_type] using h.symm

/-- Unconditional synchronized-chain sine bound with explicit within-chain and cross-chain errors. -/
theorem synchronizedDyadicGramEnergy_le_sine (f : C_c(ℝ, ℝ)) (n : ℕ) (base b : ℝ)
    (c : Fin (n+1) → ℝ) :
    synchronizedDyadicGramEnergy f n base b c ≤
      2 * (1+chainSineFactor n) *
        (autocorr f 0 + ‖dyadicWithinDefect f n‖ +
          ‖triangularGramError (dyadicCrossGram f n b)‖) * ∑ i, c i ^ 2 := by
  let A := HTGeometry.finiteSynthesis (dyadicFeatureFamily f n base)
  let B := HTGeometry.finiteSynthesis (dyadicFeatureFamily f n (base+b))
  let K := autocorr f 0 + ‖dyadicWithinDefect f n‖
  let E := ‖triangularGramError (dyadicCrossGram f n b)‖
  have hA : ‖A‖ ^ 2 ≤ K := dyadicSynthesis_norm_sq_le f n base
  have hB : ‖B‖ ^ 2 ≤ K := dyadicSynthesis_norm_sq_le f n (base+b)
  have hp : ‖A‖ * ‖B‖ ≤ K := by nlinarith [sq_nonneg (‖A‖-‖B‖)]
  have hm := mul_le_mul_of_nonneg_left hp (mul_nonneg (by positivity : (0 : ℝ) ≤ 2)
    (chainSineFactor_nonneg n))
  have hc : ‖A‖^2+‖B‖^2+2*chainSineFactor n*‖A‖*‖B‖+2*(1+chainSineFactor n)*E ≤
      2*(1+chainSineFactor n)*(K+E) := by nlinarith
  have h := synchronized_frame_energy_bound (dyadicFeatureFamily f n base)
    (dyadicFeatureFamily f n (base+b)) (realChainCoefficients c)
  rw [frameCrossGram_dyadicCross, realChainCoefficients_norm_sq] at h
  rw [synchronizedDyadicGramEnergy_eq_norm]
  exact h.trans (mul_le_mul_of_nonneg_right hc (Finset.sum_nonneg fun i _ => sq_nonneg (c i)))

/-- Sine-improved origin leverage, valid for every actual test with explicit grid defects. -/
theorem synchronizedDyadic_origin_leverage (f : C_c(ℝ, ℝ)) (n : ℕ) (base b a y : ℝ)
    (c : Fin (n+1) → ℝ) :
    autocorr f 0 * (∑ i : Fin (n+1) ⊕ Fin (n+1), Sum.elim c c i) -
        (∑ i : Fin (n+1) ⊕ Fin (n+1), Sum.elim c c i * autocorr f (dyadicPairNode n base b i)) -
        (1+chainSineFactor n) *
          (autocorr f 0 + ‖dyadicWithinDefect f n‖ + ‖triangularGramError (dyadicCrossGram f n b)‖) *
            (∑ i, c i ^ 2) / Real.exp a ≤
      Real.exp a * (autocorr f 0 - autocorr f y) +
        ∑ i : Fin (n+1) ⊕ Fin (n+1), Sum.elim c c i *
          (autocorr f 0 - autocorr f (dyadicPairNode n base b i-y)) := by
  have hbase := autocorr_gram_leverage_bound f Finset.univ (Sum.elim c c)
    (dyadicPairNode n base b) a y
  have hQ := synchronizedDyadicGramEnergy_le_sine f n base b c
  have hcost := div_le_div_of_nonneg_right hQ (by positivity : 0 ≤ 2*Real.exp a)
  have heq : (2*(1+chainSineFactor n)*
      (autocorr f 0+‖dyadicWithinDefect f n‖+‖triangularGramError (dyadicCrossGram f n b)‖)*
        (∑ i, c i^2))/(2*Real.exp a) =
      (1+chainSineFactor n)*
        (autocorr f 0+‖dyadicWithinDefect f n‖+‖triangularGramError (dyadicCrossGram f n b)‖)*
          (∑ i, c i^2)/Real.exp a := by ring
  rw [heq] at hcost
  unfold synchronizedDyadicGramEnergy at hcost
  linarith

/-- Odd integer bases and odd integer coset ratios are an unconditional specialization. -/
theorem oddCoset_synchronized_origin_leverage (f : C_c(ℝ, ℝ)) (n m q : ℕ) (a y : ℝ)
    (c : Fin (n+1) → ℝ) :
    autocorr f 0 * (∑ i : Fin (n+1) ⊕ Fin (n+1), Sum.elim c c i) -
        (∑ i : Fin (n+1) ⊕ Fin (n+1), Sum.elim c c i * autocorr f
          (dyadicPairNode n (Real.log ((2*m+3 : ℕ) : ℝ)) (Real.log ((2*q+3 : ℕ) : ℝ)) i)) -
        (1+chainSineFactor n) *
          (autocorr f 0 + ‖dyadicWithinDefect f n‖ +
            ‖triangularGramError (dyadicCrossGram f n (Real.log ((2*q+3 : ℕ) : ℝ)))‖) *
              (∑ i, c i ^ 2) / Real.exp a ≤
      Real.exp a * (autocorr f 0 - autocorr f y) +
        ∑ i : Fin (n+1) ⊕ Fin (n+1), Sum.elim c c i * (autocorr f 0 - autocorr f
          (dyadicPairNode n (Real.log ((2*m+3 : ℕ) : ℝ)) (Real.log ((2*q+3 : ℕ) : ℝ)) i-y)) :=
  synchronizedDyadic_origin_leverage f n _ _ a y c

/-- Each within-chain entry is an actual integer-log sample, in either orientation. -/
theorem dyadicWithinGram_grid_entry (f : C_c(ℝ, ℝ)) (n : ℕ) (i j : Fin (n+1)) :
    dyadicWithinGram f n i j =
      if i ≤ j then (autocorr f (Real.log ((2 ^ (j.val-i.val) : ℕ) : ℝ)) : ℂ)
      else (autocorr f (Real.log ((2 ^ (i.val-j.val) : ℕ) : ℝ)) : ℂ) := by
  by_cases hij : i ≤ j
  · have hlog : Real.log ((2 ^ (j.val-i.val) : ℕ) : ℝ) =
        ((j : ℝ)-(i : ℝ))*Real.log 2 := by
      rw [Nat.cast_pow, Real.log_pow, Nat.cast_sub (show i.val ≤ j.val from hij)]
      rfl
    simp only [dyadicWithinGram, if_pos hij, hlog]
  · have hji : j.val ≤ i.val := by omega
    have hlog : Real.log ((2 ^ (i.val-j.val) : ℕ) : ℝ) =
        ((i : ℝ)-(j : ℝ))*Real.log 2 := by
      rw [Nat.cast_pow, Real.log_pow, Nat.cast_sub hji]
      rfl
    simp only [dyadicWithinGram, if_neg hij, hlog]
    rw [show ((j : ℝ)-(i : ℝ))*Real.log 2 = -(((i : ℝ)-(j : ℝ))*Real.log 2) by ring,
      autocorr_neg]

/-- The forbidden cross entries are precisely integer-log samples at odd times dyadic ratios. -/
theorem oddCoset_triangularError_grid_formula (f : C_c(ℝ, ℝ)) (n q : ℕ) :
    triangularGramError (dyadicCrossGram f n (Real.log ((2*q+3 : ℕ) : ℝ))) =
      gramMatrixOperator (fun i j : Fin (n+1) => if i < j then 0 else
        (autocorr f (Real.log (((2*q+3) * 2^(i.val-j.val) : ℕ) : ℝ)) : ℂ)) := by
  let C := dyadicCrossGram f n (Real.log ((2*q+3 : ℕ) : ℝ))
  have he : triangularGramError C = gramMatrixOperator (C-strictUpperGram C) := by
    simp only [triangularGramError, gramMatrixOperator, map_sub]
  rw [he]
  congr 1
  ext i j
  by_cases hij : i < j
  · simp [strictUpperGram, hij]
  · have hji : j.val ≤ i.val := by omega
    have hlog : Real.log (((2*q+3) * 2^(i.val-j.val) : ℕ) : ℝ) =
        Real.log ((2*q+3 : ℕ) : ℝ) + ((i : ℝ)-(j : ℝ))*Real.log 2 := by
      rw [Nat.cast_mul, Nat.cast_pow, Real.log_mul (by positivity) (by positivity),
        Real.log_pow, Nat.cast_sub hji]
      rfl
    simp only [Matrix.sub_apply, strictUpperGram, if_neg hij, sub_zero, C, dyadicCrossGram, hlog]
    rw [show ((j : ℝ)-(i : ℝ))*Real.log 2 - Real.log ((2*q+3 : ℕ) : ℝ) =
      -(Real.log ((2*q+3 : ℕ) : ℝ)+((i : ℝ)-(j : ℝ))*Real.log 2) by ring, autocorr_neg]

/-- The first synchronized family is the literal odd dyadic integer grid. -/
theorem oddCoset_pairNode_inl (n m q : ℕ) (i : Fin (n+1)) :
    dyadicPairNode n (Real.log ((2*m+3 : ℕ) : ℝ)) (Real.log ((2*q+3 : ℕ) : ℝ)) (Sum.inl i) =
      Real.log (((2*m+3)*2^i.val : ℕ) : ℝ) := by
  rw [Nat.cast_mul, Nat.cast_pow, Real.log_mul (by positivity) (by positivity), Real.log_pow]
  rfl

/-- The second synchronized family lies in the coset whose odd base is the product. -/
theorem oddCoset_pairNode_inr (n m q : ℕ) (i : Fin (n+1)) :
    dyadicPairNode n (Real.log ((2*m+3 : ℕ) : ℝ)) (Real.log ((2*q+3 : ℕ) : ℝ)) (Sum.inr i) =
      Real.log ((((2*m+3)*(2*q+3))*2^i.val : ℕ) : ℝ) := by
  simp only [Nat.cast_mul, Nat.cast_pow]
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_pow]
  rfl

/-- The complete within-chain defect consists of off-diagonal integer-log samples. -/
theorem dyadicWithinDefect_grid_formula (f : C_c(ℝ, ℝ)) (n : ℕ) :
    dyadicWithinDefect f n = gramMatrixOperator (fun i j : Fin (n+1) =>
      if i = j then 0 else if i ≤ j then
        (autocorr f (Real.log ((2^(j.val-i.val) : ℕ) : ℝ)) : ℂ)
      else (autocorr f (Real.log ((2^(i.val-j.val) : ℕ) : ℝ)) : ℂ)) := by
  have hid : gramMatrixOperator ((autocorr f 0 : ℂ) • (1 : Matrix (Fin (n+1)) (Fin (n+1)) ℂ)) =
      (autocorr f 0 : ℂ) • 1 := by
    ext x i
    simp [gramMatrixOperator, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct, Matrix.one_apply]
  have he : dyadicWithinDefect f n = gramMatrixOperator
      (dyadicWithinGram f n - (autocorr f 0 : ℂ) • 1) := by
    simp only [gramMatrixOperator, map_sub] at hid ⊢
    unfold dyadicWithinDefect gramMatrixOperator
    rw [hid]
  rw [he]
  congr 1
  ext i j
  by_cases hij : i = j
  · subst j
    simp [dyadicWithinGram]
  · simp [Matrix.sub_apply, Matrix.smul_apply, hij,
      dyadicWithinGram_grid_entry]

/-- The independent-chain numerator at exact grid pinning gains a sine term minus explicit errors. -/
theorem synchronizedDyadic_gain_with_errors (f : C_c(ℝ, ℝ)) (n : ℕ) (base b : ℝ)
    (c : Fin (n+1) → ℝ) :
    2*((1-chainSineFactor n)*autocorr f 0 -
      (1+chainSineFactor n)*(‖dyadicWithinDefect f n‖ +
        ‖triangularGramError (dyadicCrossGram f n b)‖))*(∑ i, c i^2) ≤
      4*autocorr f 0*(∑ i, c i^2) - synchronizedDyadicGramEnergy f n base b c := by
  have h := synchronizedDyadicGramEnergy_le_sine f n base b c
  nlinarith


end
end GaloisForLFunctions.BiScaleUncertainty
