import GaloisForLFunctions.RHTower.VonMangoldtGammaInfinitePointedWard

/-!
# Factorial trace normalization destroys cofinal Euler--Gamma source positivity

The pointed Ward reconstruction produces positive raw source Grams.  The trace-Hankel lane uses a
different normalization: its odd logarithmic moments are divided by `1!`, `3!`, and `5!` in the
first two-by-two block.  This file proves that the distinction is structural.

First, every shifted raw moment matrix

`M(i,j) = m_(r + a_i + a_j)`

is a cofinal positive semidefinite Gram.  In particular, the unnormalized odd block

`[[m_1,m_3],[m_3,m_5]]`

is positive semidefinite.  The literal factorial normalization sends it to

`[[m_1,m_3/3!],[m_3/3!,m_5/5!]]`.

Using the existing far-right determinant theorem, Lean proves that the determinant of this
normalized block is eventually strictly negative.  Thus the actual factorial normalization is
not positivity preserving even on the cofinal Euler source, before any inverse-critical transport
is attempted.  Any RH route requiring normalized Hankel positivity must supply an additional
coupled Gamma/polar/Mellin correction; raw source positivity alone cannot prove it.
-/

open scoped BigOperators Matrix
open Filter Topology

namespace RHTower

noncomputable section

/-- Finite raw Gram after shifting the source moment order by `r`. -/
def finiteVonMangoldtGammaShiftedRawGram
    (M r : ℕ) {n : ℕ} (x : ℝ) (a : Fin n → ℕ) :
    Matrix (Fin n) (Fin n) ℝ :=
  finiteExponentialGammaRawGram
    (fun p : Fin M ↦
      (ArithmeticFunction.vonMangoldt ((p : ℕ) + 2) / ((p : ℕ) + 2)) *
        Real.log ((p : ℕ) + 2) ^ r)
    (fun p : Fin M ↦ Real.log ((p : ℕ) + 2)) x a

/-- Entry formula for the shifted finite raw Gram. -/
theorem finiteVonMangoldtGammaShiftedRawGram_apply
    (M r : ℕ) {n : ℕ} (x : ℝ) (a : Fin n → ℕ) (i j : Fin n) :
    finiteVonMangoldtGammaShiftedRawGram M r x a i j =
      finiteVonMangoldtGammaRawMoment M x (r + a i + a j) := by
  rw [finiteVonMangoldtGammaShiftedRawGram,
    finiteExponentialGammaRawGram_apply]
  · rw [finiteExponentialGammaRawMoment, finiteVonMangoldtGammaRawMoment,
      finiteExponentialGammaRawMoment]
    apply Finset.sum_congr rfl
    intro p hp
    rw [pow_add, pow_add]
    ring
  · intro p
    exact mul_nonneg
      (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (by positivity))
      (pow_nonneg (Real.log_nonneg (by
        exact_mod_cast (show 1 ≤ (p : ℕ) + 2 by omega))) _)

/-- Every finite shifted raw moment matrix is positive semidefinite. -/
theorem finiteVonMangoldtGammaShiftedRawGram_posSemidef
    (M r : ℕ) {n : ℕ} (x : ℝ) (a : Fin n → ℕ) :
    (finiteVonMangoldtGammaShiftedRawGram M r x a).PosSemidef :=
  finiteExponentialGammaRawGram_posSemidef _ _ _ _

/-- Cofinal shifted raw moment Gram. -/
def infiniteVonMangoldtGammaShiftedRawGram
    (r : ℕ) {n : ℕ} (x : ℝ) (a : Fin n → ℕ) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j ↦ infiniteVonMangoldtGammaRawMoment x (r + a i + a j)

/-- Entrywise convergence of the shifted finite raw Grams. -/
theorem tendsto_finiteVonMangoldtGammaShiftedRawGram_apply
    {x : ℝ} (hx : 0 < x) (r : ℕ) {n : ℕ} (a : Fin n → ℕ) (i j : Fin n) :
    Tendsto
      (fun M ↦ finiteVonMangoldtGammaShiftedRawGram M r x a i j)
      atTop
      (nhds (infiniteVonMangoldtGammaShiftedRawGram r x a i j)) := by
  simpa only [finiteVonMangoldtGammaShiftedRawGram_apply,
    infiniteVonMangoldtGammaShiftedRawGram] using
      tendsto_finiteVonMangoldtGammaRawMoment hx (r + a i + a j)

/-- Every cofinal shifted raw moment matrix is positive semidefinite. -/
theorem infiniteVonMangoldtGammaShiftedRawGram_posSemidef
    {x : ℝ} (hx : 0 < x) (r : ℕ) {n : ℕ} (a : Fin n → ℕ) :
    (infiniteVonMangoldtGammaShiftedRawGram r x a).PosSemidef := by
  have hherm : (infiniteVonMangoldtGammaShiftedRawGram r x a).IsHermitian := by
    ext i j
    simp only [Matrix.conjTranspose_apply,
      infiniteVonMangoldtGammaShiftedRawGram, star_trivial]
    congr 1
    omega
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hherm
  intro c
  have hrow (i : Fin n) :
      Tendsto
        (fun M ↦ (finiteVonMangoldtGammaShiftedRawGram M r x a).mulVec c i)
        atTop
        (nhds ((infiniteVonMangoldtGammaShiftedRawGram r x a).mulVec c i)) := by
    simp only [Matrix.mulVec, dotProduct]
    apply tendsto_finsetSum
    intro j hj
    exact (tendsto_finiteVonMangoldtGammaShiftedRawGram_apply hx r a i j).mul_const
      (c j)
  have hquad :
      Tendsto
        (fun M ↦ star c ⬝ᵥ
          (finiteVonMangoldtGammaShiftedRawGram M r x a).mulVec c)
        atTop
        (nhds (star c ⬝ᵥ
          (infiniteVonMangoldtGammaShiftedRawGram r x a).mulVec c)) := by
    simp only [dotProduct]
    apply tendsto_finsetSum
    intro i hi
    exact tendsto_const_nhds.mul (hrow i)
  apply ge_of_tendsto hquad
  exact Filter.Eventually.of_forall fun M ↦
    (finiteVonMangoldtGammaShiftedRawGram_posSemidef M r x a).dotProduct_mulVec_nonneg c

/-- The unnormalized first odd trace-Hankel block of the cofinal source. -/
def infiniteVonMangoldtGammaFirstRawTraceGram (x : ℝ) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  !![infiniteVonMangoldtGammaRawMoment x 1,
      infiniteVonMangoldtGammaRawMoment x 3;
    infiniteVonMangoldtGammaRawMoment x 3,
      infiniteVonMangoldtGammaRawMoment x 5]

theorem infiniteVonMangoldtGammaFirstRawTraceGram_eq_shiftedRawGram
    (x : ℝ) :
    infiniteVonMangoldtGammaFirstRawTraceGram x =
      infiniteVonMangoldtGammaShiftedRawGram 1 x ![0, 2] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [infiniteVonMangoldtGammaFirstRawTraceGram,
      infiniteVonMangoldtGammaShiftedRawGram]

/-- The unnormalized odd trace block is a literal positive source Gram. -/
theorem infiniteVonMangoldtGammaFirstRawTraceGram_posSemidef
    {x : ℝ} (hx : 0 < x) :
    (infiniteVonMangoldtGammaFirstRawTraceGram x).PosSemidef := by
  rw [infiniteVonMangoldtGammaFirstRawTraceGram_eq_shiftedRawGram]
  exact infiniteVonMangoldtGammaShiftedRawGram_posSemidef hx 1 ![0, 2]

/-- The factorially normalized first trace-Hankel block. -/
def infiniteVonMangoldtGammaFirstFactorialTraceGram (x : ℝ) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  !![infiniteVonMangoldtGammaRawMoment x 1,
      infiniteVonMangoldtGammaRawMoment x 3 / 6;
    infiniteVonMangoldtGammaRawMoment x 3 / 6,
      infiniteVonMangoldtGammaRawMoment x 5 / 120]

/-- The literal first factorial trace-normalization map. -/
def vonMangoldtGammaFirstFactorialNormalize
    (A : Matrix (Fin 2) (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![A 0 0, A 0 1 / 6; A 1 0 / 6, A 1 1 / 120]

theorem infiniteVonMangoldtGammaFirstFactorialTraceGram_eq_normalize
    (x : ℝ) :
    infiniteVonMangoldtGammaFirstFactorialTraceGram x =
      vonMangoldtGammaFirstFactorialNormalize
        (infiniteVonMangoldtGammaFirstRawTraceGram x) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [infiniteVonMangoldtGammaFirstFactorialTraceGram,
      vonMangoldtGammaFirstFactorialNormalize,
      infiniteVonMangoldtGammaFirstRawTraceGram]

theorem det_infiniteVonMangoldtGammaFirstFactorialTraceGram
    (x : ℝ) :
    (infiniteVonMangoldtGammaFirstFactorialTraceGram x).det =
      infiniteVonMangoldtGammaRawMoment x 1 *
          (infiniteVonMangoldtGammaRawMoment x 5 / 120) -
        (infiniteVonMangoldtGammaRawMoment x 3 / 6) ^ (2 : ℕ) := by
  rw [infiniteVonMangoldtGammaFirstFactorialTraceGram, Matrix.det_fin_two]
  norm_num
  ring

/-- The reconstructed factorial block is exactly the existing normalized Euler trace-Hankel
determinant, shifted from source displacement `x` to Euler coordinate `x + 1`. -/
theorem det_infiniteVonMangoldtGammaFirstFactorialTraceGram_eq_normalized
    {x : ℝ} (hx : 0 < x) :
    (infiniteVonMangoldtGammaFirstFactorialTraceGram x).det =
      vonMangoldtNormalizedFirstHankelDet (x + 1) := by
  rw [det_infiniteVonMangoldtGammaFirstFactorialTraceGram,
    infiniteVonMangoldtGammaRawMoment_eq_vonMangoldtLogMoment hx,
    infiniteVonMangoldtGammaRawMoment_eq_vonMangoldtLogMoment hx,
    infiniteVonMangoldtGammaRawMoment_eq_vonMangoldtLogMoment hx,
    vonMangoldtNormalizedFirstHankelDet]

/-- The first factorially normalized source determinant is eventually strictly negative. -/
theorem infiniteVonMangoldtGammaFirstFactorialTraceGram_eventually_det_neg :
    ∀ᶠ x : ℝ in atTop,
      (infiniteVonMangoldtGammaFirstFactorialTraceGram x).det < 0 := by
  have hshift : Tendsto (fun x : ℝ ↦ x + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_id
  have hneg := hshift.eventually vonMangoldtNormalizedFirstHankelDet_eventually_neg
  filter_upwards [hneg, eventually_gt_atTop (0 : ℝ)] with x hxneg hx
  rw [det_infiniteVonMangoldtGammaFirstFactorialTraceGram_eq_normalized hx]
  exact hxneg

/-- The factorially normalized first source block is eventually not positive semidefinite. -/
theorem infiniteVonMangoldtGammaFirstFactorialTraceGram_eventually_not_posSemidef :
    ∀ᶠ x : ℝ in atTop,
      ¬ (infiniteVonMangoldtGammaFirstFactorialTraceGram x).PosSemidef := by
  filter_upwards
    [infiniteVonMangoldtGammaFirstFactorialTraceGram_eventually_det_neg]
      with x hx hpsd
  exact (not_lt_of_ge hpsd.det_nonneg) hx

/-- Exact positivity-destruction no-go: eventually the raw odd source block is positive
semidefinite while its literal factorial trace normalization is not. -/
theorem vonMangoldtGammaFirstFactorialNormalize_eventually_destroys_posSemidef :
    ∀ᶠ x : ℝ in atTop,
      (infiniteVonMangoldtGammaFirstRawTraceGram x).PosSemidef ∧
        ¬ (vonMangoldtGammaFirstFactorialNormalize
          (infiniteVonMangoldtGammaFirstRawTraceGram x)).PosSemidef := by
  filter_upwards
    [infiniteVonMangoldtGammaFirstFactorialTraceGram_eventually_not_posSemidef,
      eventually_gt_atTop (0 : ℝ)] with x hnot hx
  exact ⟨infiniteVonMangoldtGammaFirstRawTraceGram_posSemidef hx, by
    rw [infiniteVonMangoldtGammaFirstFactorialTraceGram_eq_normalize] at hnot
    exact hnot⟩

end

end RHTower
