import GaloisForLFunctions.CompletedArithmeticForms.TailRankHorizon
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspSchurMovingMinimizerVariance

/-!
# Exact successor addition and the reserve from incompatible minimizers

Adding two sources retains both exact successor reserves and adds the sum of
two positive head energies. Equality holds precisely when the inverse-head
minimizers agree. Complete native bands and tails satisfy this law on their
explicit logarithmic rank domain, giving strict successor order there.
-/

noncomputable section

open Matrix Finset

namespace GaloisForLFunctions.CompletedArithmeticForms

open HTGeometry _root_.RHTower

/-- The actual coupling to the next monomial. -/
def successorCoupling (m : ℕ → ℝ) (N : ℕ) : Fin N → ℝ := fun i => m (i.val + N)

/-- The unique inverse-head minimizer of the successor energy at a strict head. -/
def successorMinimizer (m : ℕ → ℝ) (N : ℕ) : Fin N → ℝ :=
  (finiteHankelMatrix m N)⁻¹ *ᵥ successorCoupling m N

theorem successorMinimizer_normal {m : ℕ → ℝ} {N : ℕ}
    (hm : (finiteHankelMatrix m N).PosDef) :
    finiteHankelMatrix m N *ᵥ successorMinimizer m N = successorCoupling m N := by
  unfold successorMinimizer
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _
    ((finiteHankelMatrix m N).isUnit_iff_isUnit_det.mp hm.isUnit), Matrix.one_mulVec]

theorem successorSchur_eq_minimizer (m : ℕ → ℝ) (N : ℕ) :
    finiteHankelSuccessorSchur m N =
      m (2 * N) - successorMinimizer m N ⬝ᵥ successorCoupling m N := by
  unfold finiteHankelSuccessorSchur successorMinimizer successorCoupling
  congr 1
  simp only [dotProduct, Matrix.mulVec, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- The inverse-head debit is nonnegative at every strict head. -/
theorem successorSchur_le_terminalMoment {m : ℕ → ℝ} {N : ℕ}
    (hm : (finiteHankelMatrix m N).PosDef) : finiteHankelSuccessorSchur m N ≤ m (2 * N) := by
  have hn := hm.inv.posSemidef.dotProduct_mulVec_nonneg (successorCoupling m N)
  simp only [star_trivial] at hn
  rw [successorSchur_eq_minimizer, successorMinimizer, dotProduct_comm]
  linarith only [hn]

private theorem monic_quadratic_expansion (m : ℕ → ℝ) (N : ℕ) (w : Fin N → ℝ) :
    Fin.snoc w 1 ⬝ᵥ finiteHankelMatrix m (N + 1) *ᵥ Fin.snoc w 1 =
      w ⬝ᵥ finiteHankelMatrix m N *ᵥ w +
        2 * (w ⬝ᵥ successorCoupling m N) + m (2 * N) := by
  simp only [dotProduct, Matrix.mulVec, finiteHankelMatrix, successorCoupling,
    Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last,
    Fin.val_castSucc, Fin.val_last, mul_one, one_mul,
    mul_add, Finset.sum_add_distrib, Nat.add_comm N, two_mul]
  have hc : (∑ i : Fin N, m (i.val + N) * w i) =
      ∑ i : Fin N, w i * m (i.val + N) := by
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hc]
  ring

/-- The exact complete square for every monic successor direction. -/
theorem successor_monic_energy_eq {m : ℕ → ℝ} {N : ℕ}
    (hm : (finiteHankelMatrix m N).PosDef) (w : Fin N → ℝ) :
    Fin.snoc (-w) 1 ⬝ᵥ finiteHankelMatrix m (N + 1) *ᵥ Fin.snoc (-w) 1 =
      finiteHankelSuccessorSchur m N +
        (w - successorMinimizer m N) ⬝ᵥ
          finiteHankelMatrix m N *ᵥ (w - successorMinimizer m N) := by
  rw [monic_quadratic_expansion, Matrix.mulVec_neg, neg_dotProduct,
    dotProduct_neg, neg_neg, neg_dotProduct, successorSchur_eq_minimizer]
  have he := schurMovingMinimizer_inverse (finiteHankelMatrix m N)
    (successorCoupling m N) w hm
  change w ⬝ᵥ finiteHankelMatrix m N *ᵥ w - 2 * (w ⬝ᵥ successorCoupling m N) +
    successorMinimizer m N ⬝ᵥ successorCoupling m N =
      (w - successorMinimizer m N) ⬝ᵥ
        finiteHankelMatrix m N *ᵥ (w - successorMinimizer m N) at he
  linarith only [he]

/-- The exact monic minimizing coefficient vector, retaining its terminal coefficient. -/
def successorTestVector (m : ℕ → ℝ) (N : ℕ) : Fin (N + 1) → ℝ :=
  Fin.snoc (-successorMinimizer m N) 1

theorem successorTestVector_ne_zero (m : ℕ → ℝ) (N : ℕ) : successorTestVector m N ≠ 0 := by
  intro h
  have he := congrFun h (Fin.last N)
  exact one_ne_zero (by simpa only [successorTestVector, Fin.snoc_last, Pi.zero_apply] using he)

/-- The global inverse-head test attains the exact successor reserve. -/
theorem successorTestVector_energy_eq {m : ℕ → ℝ} {N : ℕ}
    (hm : (finiteHankelMatrix m N).PosDef) :
    successorTestVector m N ⬝ᵥ finiteHankelMatrix m (N + 1) *ᵥ successorTestVector m N =
      finiteHankelSuccessorSchur m N := by
  rw [successorTestVector, successor_monic_energy_eq hm]
  simp only [sub_self, Matrix.mulVec_zero, dotProduct_zero, add_zero]

/-- Every monic direction pays at least the exact successor of its own complete source. -/
theorem successorSchur_le_monic_energy {m : ℕ → ℝ} {N : ℕ}
    (hm : (finiteHankelMatrix m N).PosDef) (w : Fin N → ℝ) :
    finiteHankelSuccessorSchur m N ≤
      Fin.snoc (-w) 1 ⬝ᵥ finiteHankelMatrix m (N + 1) *ᵥ Fin.snoc (-w) 1 := by
  rw [successor_monic_energy_eq hm]
  apply le_add_of_nonneg_right
  simpa only [star_trivial] using
    hm.posSemidef.dotProduct_mulVec_nonneg (w - successorMinimizer m N)

/-- The exact reserve gained by using a common minimizer for two complete sources. -/
def successorMixtureVariance (m n : ℕ → ℝ) (N : ℕ) : ℝ :=
  let w := successorMinimizer (fun k => m k + n k) N
  (w - successorMinimizer m N) ⬝ᵥ
      finiteHankelMatrix m N *ᵥ (w - successorMinimizer m N) +
    (w - successorMinimizer n N) ⬝ᵥ
      finiteHankelMatrix n N *ᵥ (w - successorMinimizer n N)

/-- Adding complete sources exposes an exact nonnegative minimizer-discrepancy reserve. -/
theorem successorSchur_add_eq {m n : ℕ → ℝ} {N : ℕ}
    (hm : (finiteHankelMatrix m N).PosDef) (hn : (finiteHankelMatrix n N).PosDef) :
    finiteHankelSuccessorSchur (fun k => m k + n k) N =
      finiteHankelSuccessorSchur m N + finiteHankelSuccessorSchur n N +
        successorMixtureVariance m n N := by
  let w := successorMinimizer (fun k => m k + n k) N
  have h1 := schurMovingMinimizer_inverse (finiteHankelMatrix m N) (successorCoupling m N) w hm
  have h2 := schurMovingMinimizer_inverse (finiteHankelMatrix n N) (successorCoupling n N) w hn
  change w ⬝ᵥ (finiteHankelMatrix m N *ᵥ w) - 2 * (w ⬝ᵥ successorCoupling m N) +
    successorMinimizer m N ⬝ᵥ successorCoupling m N =
      (w - successorMinimizer m N) ⬝ᵥ
        finiteHankelMatrix m N *ᵥ (w - successorMinimizer m N) at h1
  change w ⬝ᵥ (finiteHankelMatrix n N *ᵥ w) - 2 * (w ⬝ᵥ successorCoupling n N) +
    successorMinimizer n N ⬝ᵥ successorCoupling n N =
      (w - successorMinimizer n N) ⬝ᵥ
        finiteHankelMatrix n N *ᵥ (w - successorMinimizer n N) at h2
  have hsum : (finiteHankelMatrix (fun k => m k + n k) N).PosDef := hm.add hn
  have hw := successorMinimizer_normal hsum
  change (finiteHankelMatrix m N + finiteHankelMatrix n N) *ᵥ w =
    successorCoupling m N + successorCoupling n N at hw
  have he := congrArg (fun z => w ⬝ᵥ z) hw
  simp only [add_mulVec, dotProduct_add] at he
  rw [successorSchur_eq_minimizer, successorSchur_eq_minimizer, successorSchur_eq_minimizer]
  change m (2 * N) + n (2 * N) - w ⬝ᵥ (successorCoupling m N + successorCoupling n N) =
    (m (2 * N) - successorMinimizer m N ⬝ᵥ successorCoupling m N) +
      (n (2 * N) - successorMinimizer n N ⬝ᵥ successorCoupling n N) + _
  rw [dotProduct_add]
  unfold successorMixtureVariance
  change m (2 * N) + n (2 * N) -
    (w ⬝ᵥ successorCoupling m N + w ⬝ᵥ successorCoupling n N) =
      (m (2 * N) - successorMinimizer m N ⬝ᵥ successorCoupling m N) +
      (n (2 * N) - successorMinimizer n N ⬝ᵥ successorCoupling n N) +
      ((w - successorMinimizer m N) ⬝ᵥ
        finiteHankelMatrix m N *ᵥ (w - successorMinimizer m N) +
      (w - successorMinimizer n N) ⬝ᵥ
        finiteHankelMatrix n N *ᵥ (w - successorMinimizer n N))
  linarith only [h1, h2, he]

theorem successorMixtureVariance_nonneg {m n : ℕ → ℝ} {N : ℕ}
    (hm : (finiteHankelMatrix m N).PosDef) (hn : (finiteHankelMatrix n N).PosDef) :
    0 ≤ successorMixtureVariance m n N := by
  unfold successorMixtureVariance
  exact add_nonneg (by simpa only [star_trivial] using hm.posSemidef.dotProduct_mulVec_nonneg _)
    (by simpa only [star_trivial] using hn.posSemidef.dotProduct_mulVec_nonneg _)

/-- A common minimizer is the exact equality boundary for successor superadditivity. -/
theorem successorMixtureVariance_eq_zero_iff {m n : ℕ → ℝ} {N : ℕ}
    (hm : (finiteHankelMatrix m N).PosDef) (hn : (finiteHankelMatrix n N).PosDef) :
    successorMixtureVariance m n N = 0 ↔ successorMinimizer m N = successorMinimizer n N := by
  let w := successorMinimizer (fun k => m k + n k) N
  constructor
  · intro hz
    have h1 : 0 ≤ (w - successorMinimizer m N) ⬝ᵥ
        finiteHankelMatrix m N *ᵥ (w - successorMinimizer m N) := by
      simpa only [star_trivial] using hm.posSemidef.dotProduct_mulVec_nonneg (w - successorMinimizer m N)
    have h2 : 0 ≤ (w - successorMinimizer n N) ⬝ᵥ
        finiteHankelMatrix n N *ᵥ (w - successorMinimizer n N) := by
      simpa only [star_trivial] using hn.posSemidef.dotProduct_mulVec_nonneg (w - successorMinimizer n N)
    have hwm : w = successorMinimizer m N := by
      by_contra h
      have hp := (Matrix.posDef_iff_dotProduct_mulVec.mp hm).2
        (x := w - successorMinimizer m N) (sub_ne_zero.mpr h)
      simp only [star_trivial] at hp
      change _ + _ = 0 at hz
      linarith only [hz, hp, h2]
    have hwn : w = successorMinimizer n N := by
      by_contra h
      have hp := (Matrix.posDef_iff_dotProduct_mulVec.mp hn).2
        (x := w - successorMinimizer n N) (sub_ne_zero.mpr h)
      simp only [star_trivial] at hp
      change _ + _ = 0 at hz
      linarith only [hz, h1, hp]
    exact hwm.symm.trans hwn
  · intro hmn
    have hsum : (finiteHankelMatrix (fun k => m k + n k) N).PosDef := hm.add hn
    have hu : finiteHankelMatrix (fun k => m k + n k) N *ᵥ successorMinimizer m N =
        successorCoupling (fun k => m k + n k) N := by
      change (finiteHankelMatrix m N + finiteHankelMatrix n N) *ᵥ successorMinimizer m N =
        successorCoupling m N + successorCoupling n N
      rw [add_mulVec, successorMinimizer_normal hm, hmn, successorMinimizer_normal hn]
    have hw : w = successorMinimizer m N :=
      (Matrix.mulVec_injective_iff_isUnit.mpr hsum.isUnit)
        ((successorMinimizer_normal hsum).trans hu.symm)
    change (w - successorMinimizer m N) ⬝ᵥ _ *ᵥ (w - successorMinimizer m N) +
      (w - successorMinimizer n N) ⬝ᵥ _ *ᵥ (w - successorMinimizer n N) = 0
    rw [hw, hmn]
    simp only [sub_self, Matrix.mulVec_zero, dotProduct_zero, zero_add]

theorem successorSchur_superadditive {m n : ℕ → ℝ} {N : ℕ}
    (hm : (finiteHankelMatrix m N).PosDef) (hn : (finiteHankelMatrix n N).PosDef) :
    finiteHankelSuccessorSchur m N + finiteHankelSuccessorSchur n N ≤
      finiteHankelSuccessorSchur (fun k => m k + n k) N := by
  rw [successorSchur_add_eq hm hn]
  exact le_add_of_nonneg_right (successorMixtureVariance_nonneg hm hn)

/-- Literal native moments of a finite interval between two tail endpoints. -/
def nativeTailBandMoment (r t : ℝ) (k : ℕ) : ℝ :=
  thetaCuspNativeSignedJetTail k r - thetaCuspNativeSignedJetTail k t

/-- Native tail addition retains both exact Schur reserves and their full minimizer variance. -/
theorem nativeTailSuccessor_band_decomposition (N : ℕ) {r t : ℝ}
    (hr : 2 * nativeQuadraticRankHorizon (N + 2) ≤ r) (hrt : r < t) :
    finiteHankelSuccessorSchur (fun k => thetaCuspNativeSignedJetTail k r) N =
      finiteHankelSuccessorSchur (nativeTailBandMoment r t) N +
        finiteHankelSuccessorSchur (fun k => thetaCuspNativeSignedJetTail k t) N +
          successorMixtureVariance (nativeTailBandMoment r t)
            (fun k => thetaCuspNativeSignedJetTail k t) N := by
  have hB := nativeTailHead_sub_posDef_of_quadratic_rank_horizon (N + 1) hr hrt
  have hT := nativeTailHead_posDef_of_quadratic_rank_horizon (N + 1) (hr.trans hrt.le)
  have he : Function.Injective (Fin.castSucc : Fin N → Fin (N + 1)) := by
    intro i j hij
    exact Fin.ext (congrArg (fun z : Fin (N + 1) => z.val) hij)
  have hm : (finiteHankelMatrix (nativeTailBandMoment r t) N).PosDef := hB.submatrix he
  have hn : (finiteHankelMatrix (fun k => thetaCuspNativeSignedJetTail k t) N).PosDef :=
    hT.submatrix he
  simpa only [nativeTailBandMoment, sub_add_cancel] using successorSchur_add_eq hm hn

/-- The exact integrated native successor decreases strictly beyond its logarithmic boundary. -/
theorem nativeTailSuccessor_strictAnti_of_quadratic_rank_horizon (N : ℕ) {r t : ℝ}
    (hr : 2 * nativeQuadraticRankHorizon (N + 2) ≤ r) (hrt : r < t) :
    finiteHankelSuccessorSchur (fun k => thetaCuspNativeSignedJetTail k t) N <
      finiteHankelSuccessorSchur (fun k => thetaCuspNativeSignedJetTail k r) N := by
  have hB := nativeTailHead_sub_posDef_of_quadratic_rank_horizon (N + 1) hr hrt
  have hT := nativeTailHead_posDef_of_quadratic_rank_horizon (N + 1) (hr.trans hrt.le)
  have he : Function.Injective (Fin.castSucc : Fin N → Fin (N + 1)) := by
    intro i j hij
    exact Fin.ext (congrArg (fun z : Fin (N + 1) => z.val) hij)
  have hm : (finiteHankelMatrix (nativeTailBandMoment r t) N).PosDef := hB.submatrix he
  have hn : (finiteHankelMatrix (fun k => thetaCuspNativeSignedJetTail k t) N).PosDef :=
    hT.submatrix he
  have hp := (finiteHankelMatrix_succ_posDef_iff_schur_pos hm).mp hB
  have hv := successorMixtureVariance_nonneg hm hn
  rw [nativeTailSuccessor_band_decomposition N hr hrt]
  linarith only [hp, hv]

#print axioms successorSchur_add_eq
#print axioms successor_monic_energy_eq
#print axioms successorTestVector_energy_eq
#print axioms successorMixtureVariance_eq_zero_iff
#print axioms nativeTailSuccessor_band_decomposition
#print axioms nativeTailSuccessor_strictAnti_of_quadratic_rank_horizon

end GaloisForLFunctions.CompletedArithmeticForms
