import GaloisForLFunctions.GreenCalculusOfThePrimeFreeWindow.TheFirstOverlapStepOfWeilsFormFailsForTheSignTwin
import GaloisForLFunctions.GreenCalculusOfThePrimeFreeWindow.TheFirstOverlapStepHoldsAtEveryBlockSize

/-!
# The dipole of Weil's Green matrix carries the first overlap step

On a window `(R, 2(R + a) + b]` of ratio at most three the prime `2` acts only between the dyadic
middle `(D, 2D]`, `D = R + a`, and the two ends. With the contact of two weighted by `w`, Weil's
form on the window is the block form of

* the middle: Weil's form `𝔚_D`, positive definite and the same for every `w`;
* the ends: Weil's form `E` on the two ends, the same for every `w`;
* the coupling `P_w = W₀ − w C`: `W₀` the coupling of the jets and the pole plane, `C ≥ 0` the
  contact of two from the ends into the two slivers of the middle.

Eliminating the middle leaves `S_w = E − P_wᵀ 𝒢_D P_w`, `𝒢_D = 𝔚_D⁻¹`
(`forall_reweightedWindow_form_nonneg_iff_weilPencilSchur`), and

  `⟨e, S_w e⟩ = ⟨e, S₀ e⟩ + 2w ⟨W₀e, 𝒢_D Ce⟩ − w² ⟨Ce, 𝒢_D Ce⟩` (`weilPencilSchur_form`).

The last term is a square of the positive matrix `𝒢_D`, so `w ↦ S_w` is concave. The middle
term is the **dipole**: the interference of the jets and the pole plane with the contact of two
through the Green matrix of Weil's form on the middle. `w = 1` is `ζ`, `w = −1` the sign twin,
and `S₁ − S₋₁` is four times the dipole.

* `ζ`: `S₁ ⪰ 0` on every window of the first step (`weilSchur_nonneg_firstStep`).
* The sign twin: for every cutoff `Q ≥ 2` some window of the first step carries `e` with
  `⟨e, S₋₁ e⟩ < 0` (`exists_firstStep_weilPencilSchur_neg`): the step packet of the sign twin
  below `−1/1000` is refined to block size `5000` and placed in the first-step window
  `(5000R, 10609R]`.
* On that `e` the dipole is positive and pays for the whole failure of the twin,
  `4 ⟨W₀e, 𝒢_D Ce⟩ ≥ −⟨e, S₋₁ e⟩ > 0`, and every weight `w ≤ −1` fails
  (`exists_firstStep_weilDipole_pos`).
* **No bound blind to the sign of the contact proves the first step in Weil's normal form**
  (`weilSignTwin_obstruction_firstStep`): a majorant of the mediated form `⟨Pe, 𝒢_D Pe⟩` that
  takes the same value at `P₁` and `P₋₁` exceeds `E` on some window of the first step. Bounds
  that see the contact only through its size, such as two-sided bounds for the blocks of
  `𝒢_D`, are of this kind.
-/

open Finset Matrix
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.AbsoluteGeometryOfSpecZ
open GaloisForLFunctions.MixingArithmeticOfTheFloorTrees

noncomputable section

namespace GaloisForLFunctions.GreenCalculusOfThePrimeFreeWindow

/-! ### The pencil of the prime two in Weil's normal form -/

/-- Weil's coupling of the middle to the two ends of `(R, 2(R + a) + b]` with the contact of two
weighted by `w`. -/
def weilPencilCoupling (Q R a b : ℕ) (w : ℝ) : Matrix (Fin (R + a)) (Fin a ⊕ Fin b) ℝ :=
  weilCoupling Q R a b + (1 - w) • endContact Q R a b

/-- The coupling of the jets and the pole plane: Weil's coupling without the contacts. -/
def weilJetCoupling (Q R a b : ℕ) : Matrix (Fin (R + a)) (Fin a ⊕ Fin b) ℝ :=
  weilCoupling Q R a b + endContact Q R a b

/-- The Schur complement of the middle in Weil's form with the contact of two weighted by `w`. -/
def weilPencilSchur (Q R a b : ℕ) (w : ℝ) : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) ℝ :=
  weilEndForm Q R a b -
    (weilPencilCoupling Q R a b w)ᵀ * weilGreen (R + a) * weilPencilCoupling Q R a b w

/-- **The dipole of Weil's Green matrix**: the jets and the pole plane against the contact of
two, through the Green matrix of Weil's form on the middle. -/
def weilDipole (Q R a b : ℕ) (e : Fin a ⊕ Fin b → ℝ) : ℝ :=
  (weilJetCoupling Q R a b *ᵥ e) ⬝ᵥ (weilGreen (R + a) *ᵥ (endContact Q R a b *ᵥ e))

/-- The contact of two mediated by the Green matrix of Weil's form on the middle. -/
def weilContactForm (Q R a b : ℕ) (e : Fin a ⊕ Fin b → ℝ) : ℝ :=
  (endContact Q R a b *ᵥ e) ⬝ᵥ (weilGreen (R + a) *ᵥ (endContact Q R a b *ᵥ e))

theorem weilPencilCoupling_one (Q R a b : ℕ) :
    weilPencilCoupling Q R a b 1 = weilCoupling Q R a b := by
  rw [weilPencilCoupling, sub_self, zero_smul, add_zero]

theorem weilPencilSchur_one (Q R a b : ℕ) : weilPencilSchur Q R a b 1 = weilSchur Q R a b := by
  rw [weilPencilSchur, weilPencilCoupling_one, weilSchur]

theorem weilPencilCoupling_eq (Q R a b : ℕ) (w : ℝ) :
    weilPencilCoupling Q R a b w = weilJetCoupling Q R a b - w • endContact Q R a b := by
  rw [weilPencilCoupling, weilJetCoupling, sub_smul, one_smul]
  abel

theorem weilGreen_symm (D : ℕ) (i j : Fin D) : weilGreen D i j = weilGreen D j i := by
  have hT : (weilMiddle D)ᵀ = weilMiddle D := Matrix.ext fun i j => weilMiddle_symm D j i
  have h := congrFun (congrFun (Matrix.transpose_nonsing_inv (weilMiddle D)) j) i
  rw [hT] at h
  exact h

/-- The form of `Pᵀ G P` is the form of `G` on the image of `P`. -/
theorem form_transpose_mul_mul_eq {ι κ : Type*} [Fintype ι] [Fintype κ] (P : Matrix ι κ ℝ)
    (G : Matrix ι ι ℝ) (e : κ → ℝ) :
    e ⬝ᵥ ((Pᵀ * G * P) *ᵥ e) = (P *ᵥ e) ⬝ᵥ (G *ᵥ (P *ᵥ e)) := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    Matrix.vecMul_transpose]

theorem weilPencilSchur_form_eq (Q R a b : ℕ) (w : ℝ) (e : Fin a ⊕ Fin b → ℝ) :
    e ⬝ᵥ (weilPencilSchur Q R a b w *ᵥ e) =
      e ⬝ᵥ (weilEndForm Q R a b *ᵥ e) -
        (weilPencilCoupling Q R a b w *ᵥ e) ⬝ᵥ
          (weilGreen (R + a) *ᵥ (weilPencilCoupling Q R a b w *ᵥ e)) := by
  rw [weilPencilSchur, Matrix.sub_mulVec, dotProduct_sub, form_transpose_mul_mul_eq]

/-- **The pencil in Weil's normal form**: the weight of two enters through the dipole and the
mediated contact, `⟨e, S_w e⟩ = ⟨e, S₀ e⟩ + 2w · dipole − w² · ⟨Ce, 𝒢_D Ce⟩`. -/
theorem weilPencilSchur_form (Q R a b : ℕ) (w : ℝ) (e : Fin a ⊕ Fin b → ℝ) :
    e ⬝ᵥ (weilPencilSchur Q R a b w *ᵥ e) =
      e ⬝ᵥ (weilPencilSchur Q R a b 0 *ᵥ e) + 2 * w * weilDipole Q R a b e -
        w ^ 2 * weilContactForm Q R a b e := by
  have hP : ∀ v : ℝ, weilPencilCoupling Q R a b v *ᵥ e =
      weilJetCoupling Q R a b *ᵥ e - v • (endContact Q R a b *ᵥ e) := fun v => by
    rw [weilPencilCoupling_eq, Matrix.sub_mulVec, Matrix.smul_mulVec]
  rw [weilPencilSchur_form_eq, weilPencilSchur_form_eq, hP w, hP 0, zero_smul, sub_zero]
  simp only [Matrix.mulVec_sub, Matrix.mulVec_smul, sub_dotProduct, dotProduct_sub,
    smul_dotProduct, dotProduct_smul, smul_eq_mul]
  rw [dotProduct_mulVec_symm (weilGreen_symm (R + a)) (endContact Q R a b *ᵥ e)
    (weilJetCoupling Q R a b *ᵥ e)]
  unfold weilDipole weilContactForm
  ring

theorem weilContactForm_nonneg (Q : ℕ) {R a : ℕ} (b : ℕ) (hD : 1 ≤ R + a)
    (e : Fin a ⊕ Fin b → ℝ) : 0 ≤ weilContactForm Q R a b e := by
  unfold weilContactForm
  by_cases h : endContact Q R a b *ᵥ e = 0
  · rw [h, Matrix.mulVec_zero, dotProduct_zero]
  · exact (weilGreen_form_pos hD h).le

/-! ### The reweighted window in the blocks of the overlap -/

theorem reweightedBlock_comm (ω : ℕ → ℝ) (Q x y : ℕ) :
    reweightedBlock ω Q x y = reweightedBlock ω Q y x := by
  unfold reweightedBlock
  rw [blockMatrix_comm]
  congr 1
  exact Finset.sum_congr rfl fun k _ => by rw [floorGraph_comm]

/-- Inside a dyadic window no floor map acts. -/
theorem reweightedBlock_eq_of_lt_two_mul (ω : ℕ → ℝ) (Q : ℕ) {x y : ℕ}
    (h : max x y < 2 * min x y) : reweightedBlock ω Q x y = blockMatrix Q x y := by
  have hz : ∑ k ∈ Icc 2 Q, (1 - ω k) * floorGraph k x y = 0 :=
    Finset.sum_eq_zero fun k hk => by
      rcases le_total x y with hle | hge
      · rw [floorGraph_eq_zero (Finset.mem_Icc.mp hk).1 hle
          (by rwa [max_eq_right hle, min_eq_left hle] at h), mul_zero]
      · rw [floorGraph_comm, floorGraph_eq_zero (Finset.mem_Icc.mp hk).1 hge
          (by rwa [max_eq_left hge, min_eq_right hge] at h), mul_zero]
  rw [reweightedBlock, hz, add_zero]

/-- Below ratio three a reweighting of the contacts acts through the prime two. -/
theorem reweightedBlock_eq_of_lt_three_mul {Q : ℕ} (hQ : 2 ≤ Q) (ω : ℕ → ℝ) {x y : ℕ}
    (h : max x y < 3 * min x y) :
    reweightedBlock ω Q x y = blockMatrix Q x y + (1 - ω 2) * floorGraph 2 x y := by
  have hsplit : Icc 2 Q = insert 2 (Icc 3 Q) := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  have hz : ∑ k ∈ Icc 3 Q, (1 - ω k) * floorGraph k x y = 0 :=
    Finset.sum_eq_zero fun k hk => by
      rw [floorGraph_eq_zero_of_lt_three_mul (Finset.mem_Icc.mp hk).1 h, mul_zero]
  rw [reweightedBlock, hsplit, Finset.sum_insert (by simp), hz, add_zero]

theorem floorGraph_min_max (k x y : ℕ) : floorGraph k (min x y) (max x y) = floorGraph k x y := by
  rw [floorGraph, floorGraph, max_eq_right min_le_max, min_eq_left min_le_max]

/-- Below ratio three the contacts of a pair are the contact of two. -/
theorem floorContact_eq_floorGraph_two {Q : ℕ} (hQ : 2 ≤ Q) {x y : ℕ} (hxy : x ≤ y)
    (h3 : y < 3 * x) : floorContact Q x y = floorGraph 2 x y := by
  have hsplit : Icc 2 Q = insert 2 (Icc 3 Q) := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  have hmax : max x y < 3 * min x y := by rwa [max_eq_right hxy, min_eq_left hxy]
  have hz : ∑ k ∈ Icc 3 Q, floorGraph k x y = 0 :=
    Finset.sum_eq_zero fun k hk => floorGraph_eq_zero_of_lt_three_mul (Finset.mem_Icc.mp hk).1 hmax
  rw [floorContact_eq_sum_floorGraph Q hxy, hsplit, Finset.sum_insert (by simp), hz, add_zero]

theorem windowMatrix_reweightedBlock_dyadic (ω : ℕ → ℝ) (Q D : ℕ) :
    windowMatrix (reweightedBlock ω Q) D D = weilMiddle D := by
  rw [← blockWindow_dyadic_eq Q D]
  ext m₁ m₂
  simp only [AbsoluteGeometryOfSpecZ.blockWindow, windowMatrix, Matrix.of_apply]
  exact reweightedBlock_eq_of_lt_two_mul ω Q (by have := m₁.2; have := m₂.2; omega)

theorem joinColumns_reweightedBlock_eq {Q R a b : ℕ} (hQ : 2 ≤ Q)
    (h3 : 2 * (R + a) + b ≤ 3 * R) (ω : ℕ → ℝ) :
    joinColumns (posMatrix (reweightedBlock ω Q) (middlePos R a) (leftPos R a))
        (posMatrix (reweightedBlock ω Q) (middlePos R a) (rightPos R a b)) =
      weilPencilCoupling Q R a b (ω 2) := by
  ext m p
  have hxy3 : max (middlePos R a m) (Sum.elim (leftPos R a) (rightPos R a b) p) <
      3 * min (middlePos R a m) (Sum.elim (leftPos R a) (rightPos R a b) p) := by
    rcases p with i | j <;> simp only [middlePos, leftPos, rightPos, Sum.elim_inl, Sum.elim_inr]
    · have := m.2; have := i.2; omega
    · have := m.2; have := j.2; omega
  have hval : joinColumns (posMatrix (reweightedBlock ω Q) (middlePos R a) (leftPos R a))
      (posMatrix (reweightedBlock ω Q) (middlePos R a) (rightPos R a b)) m p =
      reweightedBlock ω Q (middlePos R a m) (Sum.elim (leftPos R a) (rightPos R a b) p) := by
    rcases p with i | j <;> rfl
  rw [hval, reweightedBlock_eq_of_lt_three_mul hQ ω hxy3, weilPencilCoupling, Matrix.add_apply,
    Matrix.smul_apply, smul_eq_mul, weilCoupling_apply, endContact_apply,
    floorContact_eq_floorGraph_two hQ min_le_max hxy3, floorGraph_min_max]

theorem fromBlocks_reweightedBlock_ends_eq {Q R a b : ℕ} (hR : 1 ≤ R)
    (h3 : 2 * (R + a) + b ≤ 3 * R) (ω : ℕ → ℝ) :
    fromBlocks (posMatrix (reweightedBlock ω Q) (leftPos R a) (leftPos R a))
        (posMatrix (reweightedBlock ω Q) (leftPos R a) (rightPos R a b))
        (posMatrix (reweightedBlock ω Q) (leftPos R a) (rightPos R a b))ᵀ
        (posMatrix (reweightedBlock ω Q) (rightPos R a b) (rightPos R a b)) =
      weilEndForm Q R a b := by
  have hblk : ∀ p₁ p₂ : Fin a ⊕ Fin b,
      reweightedBlock ω Q (Sum.elim (leftPos R a) (rightPos R a b) p₁)
          (Sum.elim (leftPos R a) (rightPos R a b) p₂) =
        blockMatrix Q (Sum.elim (leftPos R a) (rightPos R a b) p₁)
          (Sum.elim (leftPos R a) (rightPos R a b) p₂) := by
    intro p₁ p₂
    have hz : ∑ k ∈ Icc 2 Q, (1 - ω k) * floorGraph k (Sum.elim (leftPos R a) (rightPos R a b) p₁)
        (Sum.elim (leftPos R a) (rightPos R a b) p₂) = 0 :=
      Finset.sum_eq_zero fun k hk => by
        rw [floorGraph_endPos_eq_zero_of_le_three_mul hR h3 (Finset.mem_Icc.mp hk).1 p₁ p₂,
          mul_zero]
    rw [reweightedBlock, hz, add_zero]
  ext p₁ p₂
  rcases p₁ with i₁ | j₁ <;> rcases p₂ with i₂ | j₂
  · exact hblk (Sum.inl i₁) (Sum.inl i₂)
  · exact hblk (Sum.inl i₁) (Sum.inr j₂)
  · exact hblk (Sum.inl i₂) (Sum.inr j₁)
  · exact hblk (Sum.inr j₁) (Sum.inr j₂)

/-- **The reweighted window in the blocks of the overlap**: up to ratio three, Weil's middle,
Weil's ends, and the coupling `P_{ω(2)}`. -/
theorem reweightedWindow_submatrix_overlapEquiv_weil {Q R a b : ℕ} (hR : 1 ≤ R) (hQ : 2 ≤ Q)
    (h3 : 2 * (R + a) + b ≤ 3 * R) (ω : ℕ → ℝ) :
    (windowMatrix (reweightedBlock ω Q) R (a + (R + a) + b)).submatrix (overlapEquiv a (R + a) b)
        (overlapEquiv a (R + a) b) =
      fromBlocks (weilMiddle (R + a)) (weilPencilCoupling Q R a b (ω 2))
        (weilPencilCoupling Q R a b (ω 2))ᵀ (weilEndForm Q R a b) := by
  rw [windowMatrix_submatrix_overlapEquiv (reweightedBlock_comm ω Q) R a b,
    windowMatrix_reweightedBlock_dyadic, joinColumns_reweightedBlock_eq hQ h3,
    fromBlocks_reweightedBlock_ends_eq hR h3]

/-- **The overlap law of the pencil in Weil's normal form.** Up to ratio three, the reweighted
form is nonnegative on the window iff `S_{ω(2)} ⪰ 0` on its two ends. -/
theorem forall_reweightedWindow_form_nonneg_iff_weilPencilSchur {Q R a b : ℕ} (hR : 1 ≤ R)
    (hQ : 2 ≤ Q) (h3 : 2 * (R + a) + b ≤ 3 * R) (ω : ℕ → ℝ) :
    (∀ x : Fin (a + (R + a) + b) → ℝ,
        0 ≤ x ⬝ᵥ (windowMatrix (reweightedBlock ω Q) R (a + (R + a) + b) *ᵥ x)) ↔
      ∀ e : Fin a ⊕ Fin b → ℝ, 0 ≤ e ⬝ᵥ (weilPencilSchur Q R a b (ω 2) *ᵥ e) := by
  have hD : 1 ≤ R + a := by omega
  have key := fromBlocks_form_nonneg_iff_schur (weilMiddle_symm (R + a)) (isUnit_weilMiddle hD)
    (weilMiddle_form_nonneg hD) (weilPencilCoupling Q R a b (ω 2)) (weilEndForm Q R a b)
  refine Iff.trans ?_ key
  rw [← reweightedWindow_submatrix_overlapEquiv_weil hR hQ h3 ω]
  constructor
  · intro hx v
    have h1 := dotProduct_submatrix_equiv_mulVec
      (windowMatrix (reweightedBlock ω Q) R (a + (R + a) + b)) (overlapEquiv a (R + a) b)
      (v ∘ (overlapEquiv a (R + a) b).symm)
    have h2 : (v ∘ (overlapEquiv a (R + a) b).symm) ∘ overlapEquiv a (R + a) b = v := by
      ext y
      simp only [Function.comp_apply, Equiv.symm_apply_apply]
    rw [h2] at h1
    rw [h1]
    exact hx _
  · intro hv x
    rw [← dotProduct_submatrix_equiv_mulVec _ (overlapEquiv a (R + a) b) x]
    exact hv _

/-! ### `ζ` and its sign twin on the first step -/

/-- **`ζ` passes the first step in Weil's normal form**, at every block size and for every cutoff
`Q ≥ 2`: the ground energy of the aperture `1881/5000` is positive. -/
theorem weilSchur_nonneg_firstStep {Q R a b : ℕ} (hQ : 2 ≤ Q) (hR : 1 ≤ R)
    (ha : 100 * a ≤ 3 * R) (hb : 50 * b ≤ 3 * (R + a)) (e : Fin a ⊕ Fin b → ℝ) :
    0 ≤ e ⬝ᵥ (weilSchur Q R a b *ᵥ e) := by
  refine (forall_blockWindow_form_nonneg_iff_weilSchur Q R a b (by omega)).mp (fun x => ?_) e
  have hJ : 5000 * (R + (a + (R + a) + b)) ≤ 10609 * R := by omega
  have h3R : 3 * R ≤ (Q + 1) * R := Nat.mul_le_mul_right R (by omega)
  have h := groundEnergy_mul_le_packetForm_stepPacket hR (Q := Q) (A := ⟨1881 / 5000, by norm_num⟩)
    (log_window_lt_of_firstStep hR hJ) (by omega) (extendFin x)
  rw [packetForm_stepPacket_eq_blockWindow_form hR] at h
  have hx : (fun i : Fin (a + (R + a) + b) => extendFin x i) = x :=
    funext fun i => extendFin_coe x i
  rw [hx] at h
  have hE : (0 : ℝ) ≤ _root_.RHTower.ccmRestrictedWeilGroundEnergy ⟨1881 / 5000, by norm_num⟩ :=
    le_trans (by norm_num) one_div_50000_le_groundEnergy_firstStep
  exact (mul_nonneg hE (Finset.sum_nonneg fun j _ => sq_nonneg _)).trans h

/-- Padding a vector by zeros does not change its form. -/
theorem sum_sum_eq_of_eq_zero {J J' : ℕ} (hJ : J ≤ J') {τ σ : ℕ → ℝ}
    (hlt : ∀ n, n < J → τ n = σ n) (hge : ∀ n, J ≤ n → τ n = 0) (K : ℕ → ℕ → ℝ) :
    ∑ i ∈ range J', ∑ l ∈ range J', τ i * τ l * K i l =
      ∑ i ∈ range J, ∑ l ∈ range J, σ i * σ l * K i l := by
  have hsub : range J ⊆ range J' := Finset.range_mono hJ
  have hout : ∀ i ∈ range J', i ∉ range J → ∑ l ∈ range J', τ i * τ l * K i l = 0 :=
    fun i _ hi => Finset.sum_eq_zero fun l _ => by
      rw [hge i (not_lt.mp fun h => hi (Finset.mem_range.mpr h)), zero_mul, zero_mul]
  rw [← Finset.sum_subset hsub hout]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hin : ∀ l ∈ range J', l ∉ range J → τ i * τ l * K i l = 0 := fun l _ hl => by
    rw [hge l (not_lt.mp fun h => hl (Finset.mem_range.mpr h)), mul_zero, zero_mul]
  rw [← Finset.sum_subset hsub hin]
  refine Finset.sum_congr rfl fun l hl => ?_
  rw [hlt i (Finset.mem_range.mp hi), hlt l (Finset.mem_range.mp hl)]

/-- **The sign twin fails the first step in Weil's normal form**: for every cutoff `Q ≥ 2` some
window of the first step carries `e` with `⟨e, S₋₁ e⟩ < 0`. -/
theorem exists_firstStep_weilPencilSchur_neg {Q : ℕ} (hQ : 2 ≤ Q) :
    ∃ R a b : ℕ, 1 ≤ R ∧ 100 * a ≤ 3 * R ∧ 50 * b ≤ 3 * (R + a) ∧
      ∃ e : Fin a ⊕ Fin b → ℝ, e ⬝ᵥ (weilPencilSchur Q R a b (-1) *ᵥ e) < 0 := by
  obtain ⟨R₀, J, hR₀, hJ, σ, hσ⟩ :=
    exists_firstStep_window_signTwin_lt hQ (ω := fun _ => -1) rfl
  refine ⟨5000 * R₀, 150 * R₀, 309 * R₀, by omega, by omega, by omega, ?_⟩
  by_contra hne
  simp only [not_exists, not_lt] at hne
  have hall := (forall_reweightedWindow_form_nonneg_iff_weilPencilSchur (Q := Q) (R := 5000 * R₀)
    (a := 150 * R₀) (b := 309 * R₀) (by omega) hQ (by omega) (fun _ => -1)).mpr hne
  -- the step packet refined to block size `5000` and padded to `(5000R₀, 10609R₀]`
  obtain ⟨τ, hτ⟩ : ∃ τ : ℕ → ℝ,
      τ = fun n => if n < 5000 * J then refineStep 5000 σ n else 0 := ⟨_, rfl⟩
  have hpad := sum_sum_eq_of_eq_zero (J := 5000 * J)
    (J' := 150 * R₀ + (5000 * R₀ + 150 * R₀) + 309 * R₀) (by omega) (τ := τ)
    (σ := refineStep 5000 σ) (fun n hn => by rw [hτ]; exact if_pos hn)
    (fun n hn => by rw [hτ]; exact if_neg (not_lt.mpr hn))
    (fun i l => reweightedBlock (fun _ => -1) Q (5000 * R₀ + i) (5000 * R₀ + l))
  have href := sum_reweightedBlock_refine hR₀ (m := 5000) (by norm_num) (fun _ => -1) Q J σ
  have hx := hall (fun i => τ i)
  rw [dotProduct_mulVec_eq_sum, sum_fin_windowMatrix_coe, hpad, href] at hx
  have hmass : 0 ≤ ∑ j ∈ range J, σ j ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
  linarith

/-- **The dipole of Weil's Green matrix carries the first step.** On some window of the first step,
for every cutoff `Q ≥ 2`, a direction `e` of the ends has `⟨e, S₋₁ e⟩ < 0 ≤ ⟨e, S₁ e⟩`; there the
dipole is positive and at least a quarter of the failure of the twin, and every weight `w ≤ −1`
of the prime two fails. -/
theorem exists_firstStep_weilDipole_pos {Q : ℕ} (hQ : 2 ≤ Q) :
    ∃ R a b : ℕ, 1 ≤ R ∧ 100 * a ≤ 3 * R ∧ 50 * b ≤ 3 * (R + a) ∧
      ∃ e : Fin a ⊕ Fin b → ℝ, 0 ≤ e ⬝ᵥ (weilPencilSchur Q R a b 1 *ᵥ e) ∧
        e ⬝ᵥ (weilPencilSchur Q R a b (-1) *ᵥ e) < 0 ∧
        -(e ⬝ᵥ (weilPencilSchur Q R a b (-1) *ᵥ e)) ≤ 4 * weilDipole Q R a b e ∧
        ∀ w : ℝ, w ≤ -1 → e ⬝ᵥ (weilPencilSchur Q R a b w *ᵥ e) < 0 := by
  obtain ⟨R, a, b, hR, ha, hb, e, he⟩ := exists_firstStep_weilPencilSchur_neg hQ
  have h1 := weilSchur_nonneg_firstStep hQ hR ha hb e
  rw [← weilPencilSchur_one] at h1
  have hf1 := weilPencilSchur_form Q R a b 1 e
  have hfm := weilPencilSchur_form Q R a b (-1) e
  have hC := weilContactForm_nonneg Q b (by omega : 1 ≤ R + a) e
  have hdip : -(e ⬝ᵥ (weilPencilSchur Q R a b (-1) *ᵥ e)) ≤ 4 * weilDipole Q R a b e := by
    linarith
  refine ⟨R, a, b, hR, ha, hb, e, h1, he, hdip, fun w hw => ?_⟩
  have hfw := weilPencilSchur_form Q R a b w e
  have h2 : 0 ≤ 2 * weilDipole Q R a b e + (1 - w) * weilContactForm Q R a b e := by
    have := mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - w) hC
    linarith
  have h3 := mul_nonneg (by linarith : (0 : ℝ) ≤ -(w + 1)) h2
  nlinarith only [hfw, hfm, h3, he]

/-- **No bound blind to the sign of the contact proves the first step in Weil's normal form.** If
`F` majorizes the mediated form `⟨Pe, 𝒢_D Pe⟩` of every coupling and takes the same value at
`P₁` and `P₋₁`, then on some window of the first step Weil's form on the ends is below `F` at the
true coupling. -/
theorem weilSignTwin_obstruction_firstStep {Q : ℕ} (hQ : 2 ≤ Q)
    (F : ∀ R a b : ℕ, Matrix (Fin (R + a)) (Fin a ⊕ Fin b) ℝ → (Fin a ⊕ Fin b → ℝ) → ℝ)
    (hmaj : ∀ (R a b : ℕ) (P : Matrix (Fin (R + a)) (Fin a ⊕ Fin b) ℝ) (e : Fin a ⊕ Fin b → ℝ),
      (P *ᵥ e) ⬝ᵥ (weilGreen (R + a) *ᵥ (P *ᵥ e)) ≤ F R a b P e)
    (hsym : ∀ (R a b : ℕ) (e : Fin a ⊕ Fin b → ℝ),
      F R a b (weilPencilCoupling Q R a b 1) e = F R a b (weilPencilCoupling Q R a b (-1)) e) :
    ∃ R a b : ℕ, 1 ≤ R ∧ 100 * a ≤ 3 * R ∧ 50 * b ≤ 3 * (R + a) ∧
      ∃ e : Fin a ⊕ Fin b → ℝ, e ⬝ᵥ (weilEndForm Q R a b *ᵥ e) < F R a b (weilCoupling Q R a b) e := by
  obtain ⟨R, a, b, hR, ha, hb, e, he⟩ := exists_firstStep_weilPencilSchur_neg hQ
  refine ⟨R, a, b, hR, ha, hb, e, ?_⟩
  rw [weilPencilSchur_form_eq] at he
  rw [← weilPencilCoupling_one, hsym]
  linarith [hmaj R a b (weilPencilCoupling Q R a b (-1)) e]

end GaloisForLFunctions.GreenCalculusOfThePrimeFreeWindow
