import GaloisForLFunctions.RHTower.VonMangoldtSuccessorBianchiHankelWeld

/-!
# Cofinal von Mangoldt successor principal-relative Hankel law

The finite successor--pointed-Bianchi weld has a divergent head Gram and a divergent tail Gram.
Their source-fixed difference is nevertheless canonical: at every jet order it is the partial sum
of

`(Λ(n) / n) * (log(n + 1) ^ q - log(n) ^ q)`.

This file proves absolute summability at every order, finite-dimensional cofinal convergence, and
an exact all-order Hankel law.  The principal subtraction retains precisely the successor block
plus its forced mixed block; hence the mixed block cancels the successor Hankel-shift defect at
every finite aperture before passage to the limit.  This constructs the signed matrix-current
part of the singular Suzuki completion.  It does not assert positivity or identify the current
with the completed Euler/Xi trace.
-/

open Filter
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Order-`q` source term of the successor principal-relative moment. -/
def vonMangoldtSuccessorRelativeMomentTerm (q n : ℕ) : ℝ :=
  finiteVonMangoldtRealWeight n * vonMangoldtAdditiveLogJetDifference q n

/-- Uniform logarithmic inverse-square majorant for every source-relative moment term. -/
lemma abs_vonMangoldtSuccessorRelativeMomentTerm_le
    (q n : ℕ) (hn : 2 ≤ n) :
    |vonMangoldtSuccessorRelativeMomentTerm q n| ≤
      4 * (q : ℝ) * |Real.log (n + 1 : ℝ)| ^ q *
        (n + 1 : ℝ) ^ (-2 : ℝ) := by
  rcases q with _ | q
  · simp [vonMangoldtSuccessorRelativeMomentTerm,
      vonMangoldtAdditiveLogJetDifference, vonMangoldtAdditiveLogJet]
  · have hn1 : 1 ≤ n := by omega
    have hn0 : (0 : ℝ) < n := by positivity
    have hns0 : (0 : ℝ) < n + 1 := by positivity
    have hlogn : 0 ≤ Real.log (n : ℝ) :=
      Real.log_nonneg (by exact_mod_cast hn1)
    have hlogs : 0 ≤ Real.log (n + 1 : ℝ) :=
      Real.log_nonneg (by norm_num)
    have hlogle : Real.log (n : ℝ) ≤ Real.log (n + 1 : ℝ) :=
      Real.strictMonoOn_log.monotoneOn hn0 hns0 (by norm_num)
    have hvm : finiteVonMangoldtRealWeight n ≤ Real.log (n : ℝ) / (n : ℝ) := by
      rw [finiteVonMangoldtRealWeight]
      exact div_le_div_of_nonneg_right ArithmeticFunction.vonMangoldt_le_log hn0.le
    have hdiff := abs_vonMangoldtAdditiveLogJetDifference_le (q + 1) n hn1
    have hbase : |vonMangoldtSuccessorRelativeMomentTerm (q + 1) n| ≤
        (Real.log (n : ℝ) / (n : ℝ)) *
          ((q + 1 : ℕ) : ℝ) * Real.log (n + 1 : ℝ) ^ q / (n : ℝ) := by
      rw [vonMangoldtSuccessorRelativeMomentTerm, abs_mul,
        abs_of_nonneg (finiteVonMangoldtRealWeight_nonneg n)]
      calc
        finiteVonMangoldtRealWeight n *
            |vonMangoldtAdditiveLogJetDifference (q + 1) n| ≤
            (Real.log (n : ℝ) / (n : ℝ)) *
              |vonMangoldtAdditiveLogJetDifference (q + 1) n| :=
          mul_le_mul_of_nonneg_right hvm (abs_nonneg _)
        _ ≤ (Real.log (n : ℝ) / (n : ℝ)) *
            (((q + 1 : ℕ) : ℝ) * Real.log (n + 1 : ℝ) ^ q / (n : ℝ)) :=
          mul_le_mul_of_nonneg_left hdiff (div_nonneg hlogn hn0.le)
        _ = _ := by ring_nf
    calc
      |vonMangoldtSuccessorRelativeMomentTerm (q + 1) n| ≤
          (Real.log (n : ℝ) / (n : ℝ)) *
            ((q + 1 : ℕ) : ℝ) * Real.log (n + 1 : ℝ) ^ q / (n : ℝ) := hbase
      _ ≤ ((q + 1 : ℕ) : ℝ) * Real.log (n + 1 : ℝ) ^ (q + 1) /
          (n : ℝ) ^ 2 := by
        rw [pow_succ]
        have hpow : 0 ≤ Real.log (n + 1 : ℝ) ^ q := by positivity
        have hprod := mul_le_mul_of_nonneg_right hlogle hpow
        calc
          (Real.log (n : ℝ) / (n : ℝ)) * ((q + 1 : ℕ) : ℝ) *
              Real.log (n + 1 : ℝ) ^ q / (n : ℝ) =
              ((q + 1 : ℕ) : ℝ) *
                (Real.log (n : ℝ) * Real.log (n + 1 : ℝ) ^ q) /
                  (n : ℝ) ^ 2 := by ring_nf
          _ ≤ ((q + 1 : ℕ) : ℝ) *
                (Real.log (n + 1 : ℝ) * Real.log (n + 1 : ℝ) ^ q) /
                  (n : ℝ) ^ 2 := by gcongr
          _ = _ := by ring_nf
      _ ≤ 4 * ((q + 1 : ℕ) : ℝ) * Real.log (n + 1 : ℝ) ^ (q + 1) /
          (n + 1 : ℝ) ^ 2 := by
        have htwoNat : n + 1 ≤ 2 * n := by omega
        have htwo : (n + 1 : ℝ) ≤ 2 * (n : ℝ) := by exact_mod_cast htwoNat
        have hpow : (n + 1 : ℝ) ^ 2 ≤ 4 * (n : ℝ) ^ 2 := by nlinarith
        have hinv : 1 / (n : ℝ) ^ 2 ≤ 4 / (n + 1 : ℝ) ^ 2 := by
          rw [div_le_div_iff₀ (by positivity : 0 < (n : ℝ) ^ 2)
            (by positivity : 0 < (n + 1 : ℝ) ^ 2)]
          simpa only [one_mul] using hpow
        have hnum : 0 ≤ ((q + 1 : ℕ) : ℝ) *
            Real.log (n + 1 : ℝ) ^ (q + 1) := by positivity
        calc
          ((q + 1 : ℕ) : ℝ) * Real.log (n + 1 : ℝ) ^ (q + 1) / (n : ℝ) ^ 2 =
              (((q + 1 : ℕ) : ℝ) * Real.log (n + 1 : ℝ) ^ (q + 1)) *
                (1 / (n : ℝ) ^ 2) := by ring_nf
          _ ≤ (((q + 1 : ℕ) : ℝ) * Real.log (n + 1 : ℝ) ^ (q + 1)) *
                (4 / (n + 1 : ℝ) ^ 2) :=
            mul_le_mul_of_nonneg_left hinv hnum
          _ = _ := by ring_nf
      _ = 4 * ((q + 1 : ℕ) : ℝ) * |Real.log (n + 1 : ℝ)| ^ (q + 1) *
          (n + 1 : ℝ) ^ (-2 : ℝ) := by
        rw [abs_of_nonneg hlogs, Real.rpow_neg hns0.le]
        rw [show (n + 1 : ℝ) ^ (2 : ℝ) = (n + 1 : ℝ) ^ (2 : ℕ) by
          exact Real.rpow_natCast _ 2]
        ring_nf

/-- Every source-relative moment is absolutely summable. -/
theorem summable_vonMangoldtSuccessorRelativeMomentTerm (q : ℕ) :
    Summable (vonMangoldtSuccessorRelativeMomentTerm q) := by
  have hs0 : Summable (fun n : ℕ =>
      |Real.log (n + 1 : ℝ)| ^ q * (n + 1 : ℝ) ^ (-2 : ℝ)) := by
    simpa [Function.comp_def, Nat.cast_succ] using
      (summable_abs_log_natCast_pow_mul_rpow_neg q 2 (by norm_num)).comp_injective
        Nat.succ_injective
  have hmajor : Summable (fun n : ℕ =>
      4 * (q : ℝ) * |Real.log (n + 1 : ℝ)| ^ q *
        (n + 1 : ℝ) ^ (-2 : ℝ)) := by
    simpa only [mul_assoc] using hs0.mul_left (4 * (q : ℝ))
  apply (summable_nat_add_iff (f := vonMangoldtSuccessorRelativeMomentTerm q) 2).mp
  apply Summable.of_norm_bounded
    (hmajor.comp_injective (fun a b h => Nat.add_right_cancel h))
  intro n
  rw [Real.norm_eq_abs]
  exact abs_vonMangoldtSuccessorRelativeMomentTerm_le q (n + 2) (by omega)

/-- Aperture-`M` partial relative moment. -/
def finiteVonMangoldtSuccessorRelativeMoment (M q : ℕ) : ℝ :=
  ∑ p : Fin M, vonMangoldtSuccessorRelativeMomentTerm q ((p : ℕ) + 2)

/-- Cofinal source-relative moment. -/
def vonMangoldtSuccessorRelativeMoment (q : ℕ) : ℝ :=
  ∑' m : ℕ, vonMangoldtSuccessorRelativeMomentTerm q (m + 2)

/-- Head endpoint minus pointed raw tail is exactly the partial relative moment. -/
theorem finiteVonMangoldtSuccessorHeadMoment_sub_rawMoment
    (M k : ℕ) :
    finiteVonMangoldtSuccessorHeadMoment M k -
        finiteVonMangoldtGammaRawMoment M 0 (k + 2) =
      finiteVonMangoldtSuccessorRelativeMoment M (k + 2) := by
  rw [finiteVonMangoldtSuccessorHeadMoment,
    finiteVonMangoldtGammaRawMoment, finiteExponentialGammaRawMoment,
    finiteVonMangoldtSuccessorRelativeMoment, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  simp only [zero_mul, neg_zero, Real.exp_zero, mul_one]
  unfold vonMangoldtSuccessorRelativeMomentTerm finiteVonMangoldtRealWeight
  unfold vonMangoldtAdditiveLogJetDifference vonMangoldtAdditiveLogJet
  push_cast
  ring_nf

/-- Partial relative moments converge to the absolutely summable source current. -/
theorem tendsto_finiteVonMangoldtSuccessorRelativeMoment (q : ℕ) :
    Tendsto (fun M => finiteVonMangoldtSuccessorRelativeMoment M q)
      atTop (nhds (vonMangoldtSuccessorRelativeMoment q)) := by
  have hs : Summable (fun m : ℕ =>
      vonMangoldtSuccessorRelativeMomentTerm q (m + 2)) :=
    (summable_vonMangoldtSuccessorRelativeMomentTerm q).comp_injective
      (fun a b h => Nat.add_right_cancel h)
  have ht := hs.hasSum.tendsto_sum_nat
  unfold finiteVonMangoldtSuccessorRelativeMoment
  unfold vonMangoldtSuccessorRelativeMoment
  convert ht using 1
  funext M
  exact Fin.sum_univ_eq_sum_range
    (fun m : ℕ => vonMangoldtSuccessorRelativeMomentTerm q (m + 2)) M

/-- Finite principal-relative block: coupled head Gram minus the pointed tail Gram. -/
def finiteVonMangoldtSuccessorPrincipalRelativeMatrix
    (M N : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  finiteVonMangoldtSuccessorPointedWeldGram M N -
    finiteVonMangoldtPointedBianchiPositiveBoundary M N

/-- Canonical cofinal relative Hankel block. -/
def vonMangoldtSuccessorPrincipalRelativeHankel
    (N : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  HTGeometry.momentHankelMatrix
    (fun k => vonMangoldtSuccessorRelativeMoment (k + 2)) N

/-- Principal subtraction retains exactly the successor block and its forced mixed block. -/
theorem finiteVonMangoldtSuccessorPrincipalRelativeMatrix_eq_successor_add_cross
    (M N : ℕ) :
    finiteVonMangoldtSuccessorPrincipalRelativeMatrix M N =
      finiteVonMangoldtSuccessorPositiveFiniteGram M N +
        finiteVonMangoldtSuccessorPointedBianchiCross M N := by
  rw [finiteVonMangoldtSuccessorPrincipalRelativeMatrix,
    finiteVonMangoldtSuccessorPointedWeldGram_decomposition]
  ext i j
  simp only [Matrix.sub_apply, Matrix.add_apply]
  ring_nf

/-- Every finite principal-relative entry is the corresponding partial relative moment. -/
theorem finiteVonMangoldtSuccessorPrincipalRelativeMatrix_apply
    (M N : ℕ) (i j : Fin N) :
    finiteVonMangoldtSuccessorPrincipalRelativeMatrix M N i j =
      finiteVonMangoldtSuccessorRelativeMoment M
        ((i : ℕ) + (j : ℕ) + 2) := by
  rw [finiteVonMangoldtSuccessorPrincipalRelativeMatrix, Matrix.sub_apply,
    finiteVonMangoldtSuccessorPointedWeldGram_apply,
    finiteVonMangoldtPointedBianchiPositiveBoundary_eq_rawGram,
    finiteVonMangoldtGammaRawGram_apply]
  have hdepth : positiveLogJetDepth i + positiveLogJetDepth j =
      (i : ℕ) + (j : ℕ) + 2 := by
    unfold positiveLogJetDepth
    omega
  rw [hdepth]
  exact finiteVonMangoldtSuccessorHeadMoment_sub_rawMoment M
    ((i : ℕ) + (j : ℕ))

/-- Entrywise cofinal convergence of the signed principal-relative block. -/
theorem tendsto_finiteVonMangoldtSuccessorPrincipalRelativeMatrix_apply
    (N : ℕ) (i j : Fin N) :
    Tendsto
      (fun M => finiteVonMangoldtSuccessorPrincipalRelativeMatrix M N i j)
      atTop (nhds (vonMangoldtSuccessorPrincipalRelativeHankel N i j)) := by
  simpa [finiteVonMangoldtSuccessorPrincipalRelativeMatrix_apply,
    vonMangoldtSuccessorPrincipalRelativeHankel,
    HTGeometry.momentHankelMatrix] using
      tendsto_finiteVonMangoldtSuccessorRelativeMoment
        ((i : ℕ) + (j : ℕ) + 2)

/-- Whole finite jet block converges in its finite-dimensional matrix topology. -/
theorem tendsto_finiteVonMangoldtSuccessorPrincipalRelativeMatrix
    (N : ℕ) :
    Tendsto (fun M => finiteVonMangoldtSuccessorPrincipalRelativeMatrix M N)
      atTop (nhds (vonMangoldtSuccessorPrincipalRelativeHankel N)) := by
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_pi_nhds.mpr
  intro j
  exact tendsto_finiteVonMangoldtSuccessorPrincipalRelativeMatrix_apply N i j

/-- Infinite source-relative kernel before restriction to a finite jet block. -/
def vonMangoldtSuccessorPrincipalRelativeKernel (r s : ℕ) : ℝ :=
  vonMangoldtSuccessorRelativeMoment (r + s + 2)

/-- Every cofinal matrix is the finite restriction of one universal relative kernel. -/
theorem vonMangoldtSuccessorPrincipalRelativeHankel_apply
    (N : ℕ) (i j : Fin N) :
    vonMangoldtSuccessorPrincipalRelativeHankel N i j =
      vonMangoldtSuccessorPrincipalRelativeKernel (i : ℕ) (j : ℕ) := by
  rfl

/-- **All-order cofinal Hankel law.** Principal subtraction preserves the shift identity. -/
theorem vonMangoldtSuccessorPrincipalRelativeKernel_hankelShift
    (r s : ℕ) :
    vonMangoldtSuccessorPrincipalRelativeKernel (r + 1) s =
      vonMangoldtSuccessorPrincipalRelativeKernel r (s + 1) := by
  unfold vonMangoldtSuccessorPrincipalRelativeKernel
  congr 1
  omega

/-- Same all-order cancellation is exact before taking the cofinal limit. -/
theorem finiteVonMangoldtSuccessorPrincipalRelativeMatrix_hankelShift
    (M N : ℕ) (i j : Fin N)
    (hi : (i : ℕ) + 1 < N) (hj : (j : ℕ) + 1 < N) :
    finiteVonMangoldtSuccessorPrincipalRelativeMatrix M N
        ⟨(i : ℕ) + 1, hi⟩ j =
      finiteVonMangoldtSuccessorPrincipalRelativeMatrix M N i
        ⟨(j : ℕ) + 1, hj⟩ := by
  rw [finiteVonMangoldtSuccessorPrincipalRelativeMatrix_apply,
    finiteVonMangoldtSuccessorPrincipalRelativeMatrix_apply]
  change finiteVonMangoldtSuccessorRelativeMoment M
      (((i : ℕ) + 1) + (j : ℕ) + 2) =
    finiteVonMangoldtSuccessorRelativeMoment M
      ((i : ℕ) + ((j : ℕ) + 1) + 2)
  congr 1
  omega

/-- **Forced all-order curvature cancellation.** At every admissible depth, the mixed block
carries exactly the opposite Hankel-shift defect of the successor block. -/
theorem finiteVonMangoldtSuccessorPointedBianchiCross_hankelCurvature_eq_neg_successor
    (M N : ℕ) (i j : Fin N)
    (hi : (i : ℕ) + 1 < N) (hj : (j : ℕ) + 1 < N) :
    finiteVonMangoldtSuccessorPointedBianchiCross M N
          ⟨(i : ℕ) + 1, hi⟩ j -
        finiteVonMangoldtSuccessorPointedBianchiCross M N i
          ⟨(j : ℕ) + 1, hj⟩ =
      -(finiteVonMangoldtSuccessorPositiveFiniteGram M N
          ⟨(i : ℕ) + 1, hi⟩ j -
        finiteVonMangoldtSuccessorPositiveFiniteGram M N i
          ⟨(j : ℕ) + 1, hj⟩) := by
  have hdecomp :=
    finiteVonMangoldtSuccessorPrincipalRelativeMatrix_eq_successor_add_cross M N
  have hleft := congrFun (congrFun hdecomp ⟨(i : ℕ) + 1, hi⟩) j
  have hright := congrFun (congrFun hdecomp i) ⟨(j : ℕ) + 1, hj⟩
  have hhankel :=
    finiteVonMangoldtSuccessorPrincipalRelativeMatrix_hankelShift M N i j hi hj
  simp only [Matrix.add_apply] at hleft hright
  linarith

end

end RHTower
