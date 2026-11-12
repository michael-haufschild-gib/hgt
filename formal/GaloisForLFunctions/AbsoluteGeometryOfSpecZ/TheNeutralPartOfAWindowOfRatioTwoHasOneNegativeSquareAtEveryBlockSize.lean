import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheBlockMatricesOfShortWindowsArePositiveAtEveryBlockSize
import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheStepPacketsOfAWindowFormATowerUnderRefinement
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FiniteConfigurationPontryaginLaw
import GaloisForLFunctions.HeckeKreinToeplitz.TheMarginIsTheWidthOfTheIndexOneWindow
import GaloisForLFunctions.HeckeKreinToeplitz.ThePoleIsTheOnlyRemovableHyperbolicDirection

/-!
# The neutral part of a window of ratio two has one negative square at every block size

The block matrix of a window is the product of the two charges of the packet plus the neutral
part: density, jets and contacts. For every block size `R ≥ 1` and every window `(R, R + J]`
with `R ≤ J` and `50 J ≤ 53 R`, the neutral part has exactly one negative square
(`hermNegIndex_neutralWindow_eq_one`): the signature of an intersection form on a surface.

* **Refinement.** Translation by `log m` multiplies the first charge by `√m` and divides the
  second by `√m` (`sum_refineStep`, `sum_refineStep_mul_blockDegree`). The product of the charges
  is invariant, and so is the neutral part (`sum_neutralBlock_refine`).
* **One negative square.** The packet constant on the dyadic window `(R, 2R]` is the refinement
  of the packet of the first block, so the neutral part takes the value `R · N(1, 1) < 0` on it
  (`sum_neutralBlock_dyadic`, `sum_neutralBlock_dyadic_neg`): the density of the first block is
  below zero and its jet is positive.
* **No second one.** Where the first charge vanishes the neutral part is the block matrix
  (`sum_fin_neutralWindow_eq_blockWindow`). So on every window the indices of the two differ by
  at most one (`hermNegIndex_neutralWindow_le_blockWindow_add_one`), and the block matrix of a
  short window is positive.

Under the Riemann hypothesis every block matrix is nonnegative, so the neutral part of every
window that contains the dyadic window has exactly one negative square, whatever the ratio
(`hermNegIndex_neutralWindow_eq_one_of_riemannHypothesis`).
-/

open Finset Matrix
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

/-! ### The charges and the neutral part under refinement -/

/-- The first charge of the refinement is `√m` times the first charge. -/
theorem sum_refineStep {m : ℕ} (hm : 1 ≤ m) (J : ℕ) (σ : ℕ → ℝ) :
    ∑ i ∈ range (m * J), refineStep m σ i = Real.sqrt m * ∑ j ∈ range J, σ j := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hs0 : Real.sqrt m ≠ 0 := (Real.sqrt_pos.mpr hm').ne'
  have hs : Real.sqrt m * Real.sqrt m = m := Real.mul_self_sqrt hm'.le
  rw [sum_range_mul_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h : ∀ i ∈ range m, refineStep m σ (m * j + i) = σ j / Real.sqrt m := fun i hi =>
    refineStep_mul_add hm σ j (Finset.mem_range.mp hi)
  rw [Finset.sum_congr rfl h, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  calc (m : ℝ) * (σ j / Real.sqrt m)
      = Real.sqrt m * Real.sqrt m * (σ j / Real.sqrt m) := by rw [hs]
    _ = Real.sqrt m * σ j := by
      rw [mul_assoc, ← mul_div_assoc, mul_div_cancel_left₀ _ hs0]

/-- The degrees of the `m` blocks above `c` add up to the degree of their union. -/
theorem sum_blockDegree_range (c m : ℕ) :
    ∑ i ∈ range m, blockDegree (c + i) = Real.log ((c + m : ℕ) : ℝ) - Real.log c := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih, blockDegree, ← Nat.add_assoc]
    ring

/-- The second charge of the refinement is the second charge over `√m`. -/
theorem sum_refineStep_mul_blockDegree {R : ℕ} (hR : 1 ≤ R) {m : ℕ} (hm : 1 ≤ m) (J : ℕ)
    (σ : ℕ → ℝ) :
    ∑ i ∈ range (m * J), refineStep m σ i * blockDegree (m * R + i) =
      (∑ j ∈ range J, σ j * blockDegree (R + j)) / Real.sqrt m := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  rw [sum_range_mul_eq, Finset.sum_div]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h : ∀ i ∈ range m,
      refineStep m σ (m * j + i) * blockDegree (m * R + (m * j + i)) =
        σ j / Real.sqrt m * blockDegree (m * (R + j) + i) := fun i hi => by
    rw [refineStep_mul_add hm σ j (Finset.mem_range.mp hi), ← Nat.add_assoc, ← Nat.mul_add]
  rw [Finset.sum_congr rfl h, ← Finset.mul_sum, sum_blockDegree_range]
  have hRj : (0 : ℝ) < ((R + j : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < R + j)
  have hRj1 : (0 : ℝ) < ((R + j + 1 : ℕ) : ℝ) := by
    exact_mod_cast (by omega : 0 < R + j + 1)
  -- the blocks above `m(R + j)` subdivide the translate of the block above `R + j`
  have hlog : Real.log ((m * (R + j) + m : ℕ) : ℝ) - Real.log ((m * (R + j) : ℕ) : ℝ) =
      blockDegree (R + j) := by
    rw [blockDegree, show m * (R + j) + m = m * (R + j + 1) by ring, Nat.cast_mul,
      Nat.cast_mul, Real.log_mul hm'.ne' hRj1.ne', Real.log_mul hm'.ne' hRj.ne']
    ring
  rw [hlog]
  ring

/-- **The neutral part is invariant under refinement.** -/
theorem sum_neutralBlock_refine {R : ℕ} (hR : 1 ≤ R) {m : ℕ} (hm : 1 ≤ m) (Q J : ℕ)
    (σ : ℕ → ℝ) :
    ∑ i ∈ range (m * J), ∑ l ∈ range (m * J),
        refineStep m σ i * refineStep m σ l * neutralBlock Q (m * R + i) (m * R + l) =
      ∑ j ∈ range J, ∑ l ∈ range J, σ j * σ l * neutralBlock Q (R + j) (R + l) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hs0 : Real.sqrt m ≠ 0 := (Real.sqrt_pos.mpr hm').ne'
  have h1 := sum_blockMatrix_eq_charges_add_neutral Q (m * R) (m * J) (refineStep m σ)
  have h2 := sum_blockMatrix_eq_charges_add_neutral Q R J σ
  rw [sum_blockMatrix_refine hR hm, sum_refineStep hm, sum_refineStep_mul_blockDegree hR hm]
    at h1
  -- the product of the charges is invariant
  have h3 : ∀ a b s : ℝ, s ≠ 0 → 2 * (s * a) * (b / s) = 2 * a * b := fun a b s hs => by
    rw [mul_div_assoc', div_eq_iff hs]
    ring
  have h4 := h3 (∑ j ∈ range J, σ j) (∑ j ∈ range J, σ j * blockDegree (R + j)) _ hs0
  linarith

/-- **The neutral part on the packet constant on the dyadic window `(R, 2R]`** is `R` times its
value on the first block. -/
theorem sum_neutralBlock_dyadic (Q : ℕ) {R : ℕ} (hR : 1 ≤ R) :
    ∑ j ∈ range R, ∑ l ∈ range R, neutralBlock Q (R + j) (R + l) =
      R * neutralBlock Q 1 1 := by
  have hR' : (0 : ℝ) < R := by exact_mod_cast hR
  have hstep : ∀ i, refineStep R (fun _ => (1 : ℝ)) i = 1 / Real.sqrt R := fun _ => rfl
  have hsq : 1 / Real.sqrt R * (1 / Real.sqrt R) = 1 / (R : ℝ) := by
    rw [div_mul_div_comm, one_mul, Real.mul_self_sqrt hR'.le]
  have h := sum_neutralBlock_refine (R := 1) le_rfl hR Q 1 (fun _ => (1 : ℝ))
  have hL : ∑ i ∈ range (R * 1), ∑ l ∈ range (R * 1),
        refineStep R (fun _ => (1 : ℝ)) i * refineStep R (fun _ => (1 : ℝ)) l *
          neutralBlock Q (R * 1 + i) (R * 1 + l) =
      (∑ j ∈ range R, ∑ l ∈ range R, neutralBlock Q (R + j) (R + l)) / R := by
    rw [Nat.mul_one, Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [hstep, hstep, hsq]
    ring
  have hRHS : ∑ j ∈ range 1, ∑ l ∈ range 1,
      (fun _ : ℕ => (1 : ℝ)) j * (fun _ : ℕ => (1 : ℝ)) l * neutralBlock Q (1 + j) (1 + l) =
      neutralBlock Q 1 1 := by
    simp
  rw [hL, hRHS, div_eq_iff hR'.ne'] at h
  rw [h]
  ring

/-- The neutral part is negative on the packet constant on the dyadic window. -/
theorem sum_neutralBlock_dyadic_neg (Q : ℕ) {R : ℕ} (hR : 1 ≤ R) :
    ∑ j ∈ range R, ∑ l ∈ range R, neutralBlock Q (R + j) (R + l) < 0 := by
  rw [sum_neutralBlock_dyadic Q hR]
  exact mul_neg_of_pos_of_neg (by exact_mod_cast hR) (neutralBlock_one_one_neg Q)

/-! ### The matrices of a window -/

/-- The matrix of a kernel on the blocks of the window `(R, R + J]`. -/
def windowMatrix (K : ℕ → ℕ → ℝ) (R J : ℕ) : Matrix (Fin J) (Fin J) ℝ :=
  Matrix.of fun j l => K (R + (j : ℕ)) (R + (l : ℕ))

/-- The neutral part of the block matrix of the window `(R, R + J]`. -/
def neutralWindow (Q R J : ℕ) : Matrix (Fin J) (Fin J) ℝ := windowMatrix (neutralBlock Q) R J

/-- The block matrix of the window `(R, R + J]`. -/
def blockWindow (Q R J : ℕ) : Matrix (Fin J) (Fin J) ℝ := windowMatrix (blockMatrix Q) R J

/-- The form of the matrix of a window on the restriction of a step function. -/
theorem sum_fin_windowMatrix_coe (K : ℕ → ℕ → ℝ) (R J : ℕ) (σ : ℕ → ℝ) :
    ∑ i : Fin J, ∑ j : Fin J, σ i * σ j * windowMatrix K R J i j =
      ∑ j ∈ range J, ∑ l ∈ range J, σ j * σ l * K (R + j) (R + l) := by
  rw [← Fin.sum_univ_eq_sum_range (fun j => ∑ l ∈ range J, σ j * σ l * K (R + j) (R + l)) J]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Fin.sum_univ_eq_sum_range (fun l => σ i * σ l * K (R + i) (R + l)) J]
  rfl

/-- A real vector on the blocks of a window, extended by zero. -/
def extendFin {J : ℕ} (u : Fin J → ℝ) (j : ℕ) : ℝ := if h : j < J then u ⟨j, h⟩ else 0

theorem extendFin_coe {J : ℕ} (u : Fin J → ℝ) (i : Fin J) : extendFin u i = u i :=
  dif_pos i.2

theorem sum_fin_eq_sum_range_extendFin {J : ℕ} (u : Fin J → ℝ) :
    ∑ i, u i = ∑ j ∈ range J, extendFin u j := by
  rw [← Fin.sum_univ_eq_sum_range (extendFin u) J]
  exact Finset.sum_congr rfl fun i _ => (extendFin_coe u i).symm

theorem sum_fin_windowMatrix_eq (K : ℕ → ℕ → ℝ) (R : ℕ) {J : ℕ} (u : Fin J → ℝ) :
    ∑ i, ∑ j, u i * u j * windowMatrix K R J i j =
      ∑ j ∈ range J, ∑ l ∈ range J, extendFin u j * extendFin u l * K (R + j) (R + l) := by
  rw [← sum_fin_windowMatrix_coe]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
    rw [extendFin_coe, extendFin_coe]

/-- Where the first charge vanishes the neutral part of a window is its block matrix. -/
theorem sum_fin_neutralWindow_eq_blockWindow (Q R : ℕ) {J : ℕ} {u : Fin J → ℝ}
    (hu : ∑ i, u i = 0) :
    ∑ i, ∑ j, u i * u j * neutralWindow Q R J i j =
      ∑ i, ∑ j, u i * u j * blockWindow Q R J i j := by
  rw [neutralWindow, blockWindow, sum_fin_windowMatrix_eq, sum_fin_windowMatrix_eq]
  exact sum_neutralBlock_eq_of_charge_zero
    (Or.inl ((sum_fin_eq_sum_range_extendFin u).symm.trans hu))

/-! ### The packet of the dyadic window inside a longer window -/

/-- The step function with the value one on the first `R` blocks. -/
def firstBlocks (R : ℕ) (j : ℕ) : ℝ := if j < R then 1 else 0

theorem sum_range_firstBlocks_mul {R J : ℕ} (hRJ : R ≤ J) (F : ℕ → ℝ) :
    ∑ j ∈ range J, firstBlocks R j * F j = ∑ j ∈ range R, F j := by
  have key : ∑ j ∈ range R, firstBlocks R j * F j = ∑ j ∈ range J, firstBlocks R j * F j :=
    Finset.sum_subset (Finset.range_mono hRJ) fun j _ hj => by
      rw [firstBlocks, if_neg (by simpa using hj), zero_mul]
  rw [← key]
  exact Finset.sum_congr rfl fun j hj => by
    rw [firstBlocks, if_pos (Finset.mem_range.mp hj), one_mul]

/-- The neutral part of a window on the packet of its first `R` blocks. -/
theorem sum_firstBlocks_neutralBlock (Q : ℕ) {R J : ℕ} (hRJ : R ≤ J) :
    ∑ j ∈ range J, ∑ l ∈ range J,
        firstBlocks R j * firstBlocks R l * neutralBlock Q (R + j) (R + l) =
      ∑ j ∈ range R, ∑ l ∈ range R, neutralBlock Q (R + j) (R + l) := by
  have h1 : ∀ j ∈ range J, ∑ l ∈ range J,
      firstBlocks R j * firstBlocks R l * neutralBlock Q (R + j) (R + l) =
      firstBlocks R j * ∑ l ∈ range R, neutralBlock Q (R + j) (R + l) := fun j _ => by
    rw [← sum_range_firstBlocks_mul hRJ, Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => by ring
  rw [Finset.sum_congr rfl h1]
  exact sum_range_firstBlocks_mul hRJ _

/-! ### The signature -/

/-- The sum of the coordinates: the first charge of a complex packet. -/
def coordSum (J : ℕ) : (Fin J → ℂ) →ₗ[ℂ] ℂ where
  toFun x := ∑ i, x i
  map_add' x y := by simp only [Pi.add_apply, Finset.sum_add_distrib]
  map_smul' c x := by simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum, RingHom.id_apply]

/-- The real form of a real matrix as a double sum. -/
theorem dotProduct_mulVec_eq_sum {J : ℕ} (B : Matrix (Fin J) (Fin J) ℝ) (y : Fin J → ℝ) :
    y ⬝ᵥ (B *ᵥ y) = ∑ i, ∑ j, y i * y j * B i j := by
  simp only [dotProduct, mulVec, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- On the complex packets with first charge zero the neutral part of a window and its block
matrix have the same form. -/
theorem hermQuad_neutralWindow_eq_blockWindow (Q R : ℕ) {J : ℕ} {x : Fin J → ℂ}
    (hx : coordSum J x = 0) :
    hermQuad ((neutralWindow Q R J).map (↑) : Matrix (Fin J) (Fin J) ℂ) x =
      hermQuad ((blockWindow Q R J).map (↑) : Matrix (Fin J) (Fin J) ℂ) x := by
  -- the real and the imaginary part of the packet have first charge zero
  have hx0 : ∑ i, x i = 0 := hx
  have hre : ∑ i, (x i).re = 0 := by
    have h := congrArg Complex.re hx0
    rwa [Complex.re_sum, Complex.zero_re] at h
  have him : ∑ i, (x i).im = 0 := by
    have h := congrArg Complex.im hx0
    rwa [Complex.im_sum, Complex.zero_im] at h
  have e1 : ∑ i, ∑ j, (x i).re * (x j).re * neutralWindow Q R J i j =
      ∑ i, ∑ j, (x i).re * (x j).re * blockWindow Q R J i j :=
    sum_fin_neutralWindow_eq_blockWindow Q R hre
  have e2 : ∑ i, ∑ j, (x i).im * (x j).im * neutralWindow Q R J i j =
      ∑ i, ∑ j, (x i).im * (x j).im * blockWindow Q R J i j :=
    sum_fin_neutralWindow_eq_blockWindow Q R him
  rw [HeckeKreinToeplitz.hermQuad_map_ofReal, HeckeKreinToeplitz.hermQuad_map_ofReal,
    dotProduct_mulVec_eq_sum, dotProduct_mulVec_eq_sum, dotProduct_mulVec_eq_sum,
    dotProduct_mulVec_eq_sum, e1, e2]

/-- **The indices of the neutral part of a window and of its block matrix differ by at most
one**: the product of the charges is one hyperbolic plane. -/
theorem hermNegIndex_neutralWindow_le_blockWindow_add_one (Q R J : ℕ) :
    hermNegIndex ((neutralWindow Q R J).map (↑) : Matrix (Fin J) (Fin J) ℂ) ≤
      hermNegIndex ((blockWindow Q R J).map (↑) : Matrix (Fin J) (Fin J) ℂ) + 1 :=
  HeckeKreinToeplitz.hermNegIndex_le_add_one_of_eq_on_ker _ _ (coordSum J) fun _ hc =>
    hermQuad_neutralWindow_eq_blockWindow Q R hc

theorem hermNegIndex_blockWindow_le_neutralWindow_add_one (Q R J : ℕ) :
    hermNegIndex ((blockWindow Q R J).map (↑) : Matrix (Fin J) (Fin J) ℂ) ≤
      hermNegIndex ((neutralWindow Q R J).map (↑) : Matrix (Fin J) (Fin J) ℂ) + 1 :=
  HeckeKreinToeplitz.hermNegIndex_le_add_one_of_eq_on_ker _ _ (coordSum J) fun _ hc =>
    (hermQuad_neutralWindow_eq_blockWindow Q R hc).symm

/-- A nonnegative block matrix has no negative square. -/
theorem hermNegIndex_blockWindow_eq_zero_of_nonneg {Q R J : ℕ}
    (h : ∀ σ : ℕ → ℝ,
      0 ≤ ∑ j ∈ range J, ∑ l ∈ range J, σ j * σ l * blockMatrix Q (R + j) (R + l)) :
    hermNegIndex ((blockWindow Q R J).map (↑) : Matrix (Fin J) (Fin J) ℂ) = 0 := by
  refine ArithmeticCastelnuovoSeveri.negIndex_eq_zero_of_hermQuad_nonneg fun x => ?_
  rw [HeckeKreinToeplitz.hermQuad_map_ofReal, dotProduct_mulVec_eq_sum,
    dotProduct_mulVec_eq_sum, blockWindow, sum_fin_windowMatrix_eq, sum_fin_windowMatrix_eq]
  exact add_nonneg (h _) (h _)

/-- **Where the block matrix is nonnegative its neutral part has at most one negative
square.** -/
theorem hermNegIndex_neutralWindow_le_one_of_nonneg {Q R J : ℕ}
    (h : ∀ σ : ℕ → ℝ,
      0 ≤ ∑ j ∈ range J, ∑ l ∈ range J, σ j * σ l * blockMatrix Q (R + j) (R + l)) :
    hermNegIndex ((neutralWindow Q R J).map (↑) : Matrix (Fin J) (Fin J) ℂ) ≤ 1 := by
  have h1 := hermNegIndex_neutralWindow_le_blockWindow_add_one Q R J
  rwa [hermNegIndex_blockWindow_eq_zero_of_nonneg h, zero_add] at h1

/-- **The neutral part of a window that contains the dyadic window has a negative square**: the
packet constant on the dyadic window is a negative vector. -/
theorem one_le_hermNegIndex_neutralWindow (Q : ℕ) {R J : ℕ} (hR : 1 ≤ R) (hRJ : R ≤ J) :
    1 ≤ hermNegIndex ((neutralWindow Q R J).map (↑) : Matrix (Fin J) (Fin J) ℂ) := by
  by_contra hlt
  have h0 : hermNegIndex ((neutralWindow Q R J).map (↑) : Matrix (Fin J) (Fin J) ℂ) = 0 := by
    omega
  have hnn := ArithmeticCastelnuovoSeveri.hermQuad_nonneg_of_negIndex_eq_zero h0
    (fun i => ((firstBlocks R i : ℝ) : ℂ))
  rw [HeckeKreinToeplitz.hermQuad_map_ofReal_real, dotProduct_mulVec_eq_sum, neutralWindow,
    sum_fin_windowMatrix_coe (neutralBlock Q) R J (firstBlocks R),
    sum_firstBlocks_neutralBlock Q hRJ] at hnn
  linarith [sum_neutralBlock_dyadic_neg Q hR]

/-- **The neutral part of a short window has at most one negative square**, at every block
size. -/
theorem hermNegIndex_neutralWindow_le_one {Q R J : ℕ} (hR : 1 ≤ R) (hJ : 50 * J ≤ 53 * R)
    (hQ : 2 ≤ Q) :
    hermNegIndex ((neutralWindow Q R J).map (↑) : Matrix (Fin J) (Fin J) ℂ) ≤ 1 :=
  hermNegIndex_neutralWindow_le_one_of_nonneg fun σ =>
    (mul_nonneg (by norm_num) (Finset.sum_nonneg fun j _ => sq_nonneg (σ j))).trans
      (sum_blockMatrix_ge_of_short hR hJ hQ σ)

/-- **The neutral part of a window of ratio between `2` and `103/50` has exactly one negative
square, at every block size.** -/
theorem hermNegIndex_neutralWindow_eq_one {Q R J : ℕ} (hR : 1 ≤ R) (hRJ : R ≤ J)
    (hJ : 50 * J ≤ 53 * R) (hQ : 2 ≤ Q) :
    hermNegIndex ((neutralWindow Q R J).map (↑) : Matrix (Fin J) (Fin J) ℂ) = 1 :=
  le_antisymm (hermNegIndex_neutralWindow_le_one hR hJ hQ)
    (one_le_hermNegIndex_neutralWindow Q hR hRJ)

/-- **Under the Riemann hypothesis the neutral part of every window that contains the dyadic
window has exactly one negative square**, at every block size and every ratio. -/
theorem hermNegIndex_neutralWindow_eq_one_of_riemannHypothesis (hRH : RiemannHypothesis)
    {Q R J : ℕ} (hR : 1 ≤ R) (hRJ : R ≤ J) (hQ : R + J ≤ Q * R) :
    hermNegIndex ((neutralWindow Q R J).map (↑) : Matrix (Fin J) (Fin J) ℂ) = 1 :=
  le_antisymm
    (hermNegIndex_neutralWindow_le_one_of_nonneg fun σ => by
      rw [← packetForm_stepPacket_eq_sum_blockMatrix hR Q J σ]
      exact packetForm_stepPacket_nonneg_of_riemannHypothesis hRH hR hQ σ)
    (one_le_hermNegIndex_neutralWindow Q hR hRJ)

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
