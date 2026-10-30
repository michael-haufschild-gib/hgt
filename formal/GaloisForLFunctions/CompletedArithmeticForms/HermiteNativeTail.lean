import GaloisForLFunctions.CompletedArithmeticForms.HermiteJetCongruence
import GaloisForLFunctions.CompletedArithmeticForms.NativePolynomialHorizon
import GaloisForLFunctions.HTGeometry.SiegelIsometryVanishing

/-!
# The complete theta remainder in Hermite coordinates

The entire infinite remainder is transported through the finite monic Hermite
matrix before its exponential source decay is spent. The resulting estimate
retains both mixed coefficient sums and every theta atom.
-/

noncomputable section

open Finset Matrix

namespace GaloisForLFunctions.CompletedArithmeticForms

open HTGeometry _root_.RHTower _root_.RHTower.ThetaCuspGaussianLimit

/-- Complete native signed moments in Gaussian mass and length coordinates. -/
def nativeBalancedFullMoment (x : ℝ) : ℕ → ℝ :=
  evenMomentSequence (fun k => thetaCuspNativeScaledEvenJet k x)

/-- Literal first-atom signed moments in the identical coordinates. -/
def firstAtomBalancedFullMoment (x : ℝ) : ℕ → ℝ :=
  evenMomentSequence (fun k => thetaCuspFirstAtomScaledEvenJet k x)

theorem firstAtomNormalizedRotatedPair_odd_jet (x : ℝ) (k : ℕ) :
    iteratedDeriv (2 * k + 1) (firstAtomNormalizedRotatedPair x) 0 = 0 := by
  unfold firstAtomNormalizedRotatedPair
  rw [iteratedDeriv_div_const,
    iteratedDeriv_comp_const_mul (firstAtomRotatedPair_entire x).contDiff]
  simp only [mul_zero, firstAtomRotatedPair_jet,
    thetaCuspFirstAtomReflectionJet_odd_zero (show Odd (2 * k + 1) from ⟨k, rfl⟩),
    Complex.ofReal_zero, mul_zero, zero_div]

/-- Every source jet, including its literal odd zeros, is the balanced signed moment. -/
theorem firstAtomNormalizedRotatedPair_all_jets (x : ℝ) (n : ℕ) :
    iteratedDeriv n (firstAtomNormalizedRotatedPair x) 0 =
      (firstAtomBalancedFullMoment x n : ℂ) := by
  rcases Nat.even_or_odd n with he | ho
  · obtain ⟨k, hk⟩ := he
    rw [show n = 2 * k by omega, firstAtomNormalizedRotatedPair_even_jet,
      firstAtomBalancedFullMoment, evenMomentSequence_even]
  · obtain ⟨k, hk⟩ := ho
    rw [show n = 2 * k + 1 by omega, firstAtomNormalizedRotatedPair_odd_jet,
      firstAtomBalancedFullMoment, evenMomentSequence_odd, Complex.ofReal_zero]

/-- The entire first-atom moment head equals the literal balanced real source head. -/
theorem realEntireMomentMatrix_firstAtom (N : ℕ) (x : ℝ) :
    realEntireMomentMatrix (firstAtomNormalizedRotatedPair x) N =
      finiteHankelMatrix (firstAtomBalancedFullMoment x) N := by
  ext i j
  simp only [realEntireMomentMatrix, firstAtomNormalizedRotatedPair_all_jets,
    Complex.ofReal_re, finiteHankelMatrix]

/-- Literal complete native head in the same monic Hermite coordinates. -/
def nativeHermiteHead (N : ℕ) (x : ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  hermiteJetMatrix N * finiteHankelMatrix (nativeBalancedFullMoment x) N *
    (hermiteJetMatrix N).transpose

/-- Raw complete-source error through an order cutoff, with its exponential decay unspent. -/
theorem nativeBalancedFullMoment_firstAtom_error_le {L n : ℕ} (hn : n ≤ 2 * L) {x : ℝ}
    (hq : 2 * (L : ℝ) + 6 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    |nativeBalancedFullMoment x n - firstAtomBalancedFullMoment x n| ≤
      nativePolynomialTailConstant * (24 : ℝ) ^ (2 * L) *
        thetaCuspSingleAtomReflectionScale 1 x ^ L *
        Real.exp (-3 * thetaCuspSingleAtomReflectionScale 1 x) := by
  let q := thetaCuspSingleAtomReflectionScale 1 x
  have hq6 : 6 ≤ q := by
    change 2 * (L : ℝ) + 6 ≤ q at hq
    linarith only [hq, Nat.cast_nonneg (α := ℝ) L]
  have hq1 : 1 ≤ q := by linarith only [hq6]
  have hq0 : 0 ≤ q := by linarith only [hq6]
  have hA := nativePolynomialTailConstant_pos
  rcases Nat.even_or_odd n with he | ho
  · obtain ⟨k, hk⟩ := he
    have hnk : n = 2 * k := by omega
    have hkL : k ≤ L := by omega
    have hkr : (k : ℝ) ≤ L := by exact_mod_cast hkL
    have htail : ((2 * k : ℕ) : ℝ) + 6 ≤ q := by
      push_cast
      change 2 * (L : ℝ) + 6 ≤ q at hq
      linarith only [hq, hkr]
    have hx := regimeOne_pos_of_six_le hq6
    have hraw := abs_thetaCuspNativeScaledEvenJet_sub_first_le_effective k hx htail
    have h24 := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 24)
      (Nat.mul_le_mul_left 2 hkL)
    have hpow := pow_le_pow_right₀ hq1 hkL
    have hm := mul_le_mul h24 hpow (pow_nonneg hq0 k) (by positivity)
    rw [hnk, nativeBalancedFullMoment, firstAtomBalancedFullMoment,
      evenMomentSequence_even, evenMomentSequence_even]
    calc
      _ ≤ 27 * (24 : ℝ) ^ (2 * k) * q ^ k * regimeOneLikelihoodScale x := hraw
      _ = nativePolynomialTailConstant * ((24 : ℝ) ^ (2 * k) * q ^ k) *
          Real.exp (-3 * q) := by
        rw [regimeOneLikelihoodScale_eq]
        unfold nativePolynomialTailConstant
        dsimp only [q]
        simp only [neg_mul]
        ring
      _ ≤ nativePolynomialTailConstant * ((24 : ℝ) ^ (2 * L) * q ^ L) *
          Real.exp (-3 * q) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hm hA.le) (Real.exp_pos _).le
      _ = _ := by dsimp only [q]; ring
  · obtain ⟨k, hk⟩ := ho
    rw [show n = 2 * k + 1 by omega, nativeBalancedFullMoment, firstAtomBalancedFullMoment,
      evenMomentSequence_odd, evenMomentSequence_odd, sub_self, abs_zero]
    change 0 ≤ nativePolynomialTailConstant * (24 : ℝ) ^ (2 * L) * q ^ L * Real.exp (-3 * q)
    positivity

/-- Both finite coefficient sums are paid before the infinite remainder is simplified. -/
theorem nativeHermiteHead_firstAtom_raw_error_le {x : ℝ} (N : ℕ)
    (hq : 2 * (N : ℝ) + 6 ≤ thetaCuspSingleAtomReflectionScale 1 x) (i j : Fin N) :
    |nativeHermiteHead N x i j -
      realWickJetMatrix (firstAtomNormalizedRotatedPair x) N i j| ≤
      (N : ℝ) ^ 2 * (N.factorial : ℝ) ^ 2 * Real.exp 8 *
        (nativePolynomialTailConstant * (24 : ℝ) ^ (2 * N) *
          thetaCuspSingleAtomReflectionScale 1 x ^ N *
          Real.exp (-3 * thetaCuspSingleAtomReflectionScale 1 x)) := by
  let E := finiteHankelMatrix (nativeBalancedFullMoment x) N -
    finiteHankelMatrix (firstAtomBalancedFullMoment x) N
  let B := (N.factorial : ℝ) * Real.exp 4
  let ε := nativePolynomialTailConstant * (24 : ℝ) ^ (2 * N) *
    thetaCuspSingleAtomReflectionScale 1 x ^ N *
    Real.exp (-3 * thetaCuspSingleAtomReflectionScale 1 x)
  have hT (a b : Fin N) : |hermiteJetMatrix N a b| ≤ B := by
    have hf : (a.val.factorial : ℝ) ≤ (N.factorial : ℝ) := by
      exact_mod_cast Nat.factorial_le (Nat.le_of_lt a.isLt)
    exact (hermiteJetCoefficient_abs_le a.val b.val).trans
      (mul_le_mul_of_nonneg_right hf (Real.exp_pos _).le)
  have hE (a b : Fin N) : |E a b| ≤ ε :=
    nativeBalancedFullMoment_firstAtom_error_le (by omega : a.val + b.val ≤ 2 * N) hq
  have hTE := HTGeometry.entry_abs_mul_le hT hE
  have hTt (a b : Fin N) : |(hermiteJetMatrix N).transpose a b| ≤ B := hT b a
  have h := HTGeometry.entry_abs_mul_le hTE hTt i j
  have he : nativeHermiteHead N x -
      realWickJetMatrix (firstAtomNormalizedRotatedPair x) N =
        hermiteJetMatrix N * E * (hermiteJetMatrix N).transpose := by
    rw [realWickJetMatrix_eq_congruence (firstAtomNormalizedRotatedPair_entire x),
      realEntireMomentMatrix_firstAtom]
    unfold nativeHermiteHead E
    rw [Matrix.mul_sub, Matrix.sub_mul]
  change |(nativeHermiteHead N x -
    realWickJetMatrix (firstAtomNormalizedRotatedPair x) N) i j| ≤ _
  rw [he]
  apply h.trans_eq
  have hexp : Real.exp (4 : ℝ) ^ 2 = Real.exp 8 := by
    rw [pow_two, ← Real.exp_add]
    norm_num
  dsimp only [B, ε]
  rw [← hexp]
  ring

private theorem factorial_le_exp_square (n : ℕ) :
    (n.factorial : ℝ) ≤ Real.exp ((n : ℝ) ^ 2) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hc : (n : ℝ) + 1 ≤ Real.exp (2 * (n : ℝ) + 1) := by
      linarith only [Real.add_one_le_exp (2 * (n : ℝ) + 1), hn]
    rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    calc
      _ ≤ Real.exp (2 * (n : ℝ) + 1) * Real.exp ((n : ℝ) ^ 2) :=
        mul_le_mul hc ih (Nat.cast_nonneg _) (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring

private theorem twenty_four_pow_le_exp (n : ℕ) :
    (24 : ℝ) ^ (2 * n) ≤ Real.exp (10 * (n : ℝ)) := by
  have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith only [Real.add_one_le_exp (1 : ℝ)]
  have h5 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) h2 5
  rw [← Real.exp_nat_mul] at h5
  norm_num at h5
  have hb : (24 : ℝ) ≤ Real.exp 5 := by linarith only [h5]
  calc
    _ ≤ Real.exp 5 ^ (2 * n) := pow_le_pow_left₀ (by norm_num) hb _
    _ = _ := by rw [← Real.exp_nat_mul]; congr 1; push_cast; ring

/-- Exponential source decay pays both complete Hermite coefficient sums on a quadratic scale. -/
theorem hermiteNativeTail_polynomial_payment (N : ℕ) {q : ℝ}
    (hq : 16 * ((N : ℝ) + 2) ^ 2 ≤ q) :
    (N : ℝ) ^ 2 * (N.factorial : ℝ) ^ 2 * Real.exp 8 *
        (nativePolynomialTailConstant * (24 : ℝ) ^ (2 * N) * q ^ N * Real.exp (-3 * q)) ≤
      nativePolynomialTailConstant * Real.exp 8 / q := by
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hqp : 0 < q := by nlinarith only [hq, hN, sq_nonneg (N : ℝ)]
  have hA := nativePolynomialTailConstant_pos
  have hcount : (N : ℝ) ^ 2 ≤ Real.exp (2 * (N : ℝ)) := by
    have hn : (N : ℝ) ≤ Real.exp (N : ℝ) := by linarith only [Real.add_one_le_exp (N : ℝ)]
    have h := pow_le_pow_left₀ hN hn 2
    rwa [← Real.exp_nat_mul, Nat.cast_ofNat] at h
  have hfac : (N.factorial : ℝ) ^ 2 ≤ Real.exp (2 * (N : ℝ) ^ 2) := by
    have h := pow_le_pow_left₀ (Nat.cast_nonneg _ : (0 : ℝ) ≤ N.factorial)
      (factorial_le_exp_square N) 2
    rwa [← Real.exp_nat_mul, Nat.cast_ofNat] at h
  have hp : q ^ N * Real.exp (-q) ≤ Real.exp ((N : ℝ) ^ 2) :=
    (_root_.RHTower.pow_mul_exp_neg_le_factorial N hqp.le).trans (factorial_le_exp_square N)
  have hm1 := mul_le_mul hcount hfac (sq_nonneg (N.factorial : ℝ)) (Real.exp_pos _).le
  have hm2 := mul_le_mul hm1 (twenty_four_pow_le_exp N) (by positivity) (by positivity)
  have hm3 := mul_le_mul hm2 hp (by positivity) (by positivity)
  have hm4 := mul_le_mul_of_nonneg_right hm3 (Real.exp_pos (-2 * q)).le
  have hm := mul_le_mul_of_nonneg_left hm4
    (show 0 ≤ nativePolynomialTailConstant * Real.exp 8 by positivity)
  have he : Real.exp (-3 * q) = Real.exp (-q) * Real.exp (-2 * q) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hcq : 3 * (N : ℝ) ^ 2 + 12 * (N : ℝ) ≤ q := by
    nlinarith only [hq, hN, sq_nonneg (N : ℝ)]
  have hinv : Real.exp (-q) ≤ 1 / q := by
    apply (le_div_iff₀ hqp).mpr
    have hp1 := _root_.RHTower.pow_mul_exp_neg_le_factorial 1 hqp.le
    norm_num at hp1
    nlinarith only [hp1]
  calc
    _ = (nativePolynomialTailConstant * Real.exp 8) *
        (((N : ℝ) ^ 2 * (N.factorial : ℝ) ^ 2) * (24 : ℝ) ^ (2 * N) *
          (q ^ N * Real.exp (-q)) * Real.exp (-2 * q)) := by rw [he]; ring
    _ ≤ (nativePolynomialTailConstant * Real.exp 8) *
        ((Real.exp (2 * (N : ℝ)) * Real.exp (2 * (N : ℝ) ^ 2)) *
          Real.exp (10 * (N : ℝ)) * Real.exp ((N : ℝ) ^ 2) * Real.exp (-2 * q)) := hm
    _ = nativePolynomialTailConstant * Real.exp 8 *
        Real.exp (3 * (N : ℝ) ^ 2 + 12 * (N : ℝ) - 2 * q) := by
      rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
      congr 1
      congr 1
      ring
    _ ≤ nativePolynomialTailConstant * Real.exp 8 * Real.exp (-q) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith only [hcq])) (by positivity)
    _ ≤ nativePolynomialTailConstant * Real.exp 8 * (1 / q) :=
      mul_le_mul_of_nonneg_left hinv (by positivity)
    _ = _ := by ring

/-- Complete native Hermite entries retain a uniform reciprocal error on a quadratic rank domain. -/
theorem nativeHermiteHead_firstAtom_error_le {x : ℝ} (N : ℕ)
    (hq : 16 * ((N : ℝ) + 2) ^ 2 ≤ thetaCuspSingleAtomReflectionScale 1 x) (i j : Fin N) :
    |nativeHermiteHead N x i j -
      realWickJetMatrix (firstAtomNormalizedRotatedPair x) N i j| ≤
      nativePolynomialTailConstant * Real.exp 8 / thetaCuspSingleAtomReflectionScale 1 x := by
  have hbase : 2 * (N : ℝ) + 6 ≤ thetaCuspSingleAtomReflectionScale 1 x := by
    nlinarith only [hq, Nat.cast_nonneg (α := ℝ) N, sq_nonneg (N : ℝ)]
  exact (nativeHermiteHead_firstAtom_raw_error_le N hbase i j).trans
    (hermiteNativeTail_polynomial_payment N hq)

#print axioms firstAtomNormalizedRotatedPair_all_jets
#print axioms nativeBalancedFullMoment_firstAtom_error_le
#print axioms nativeHermiteHead_firstAtom_raw_error_le
#print axioms hermiteNativeTail_polynomial_payment
#print axioms nativeHermiteHead_firstAtom_error_le

end GaloisForLFunctions.CompletedArithmeticForms
