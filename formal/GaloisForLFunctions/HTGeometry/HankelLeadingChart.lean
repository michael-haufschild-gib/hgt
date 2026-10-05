import GaloisForLFunctions.HTGeometry.HankelSecantDimension

/-!
# The leading-block chart of a Hankel secant ring

Let `A = K[x_0, …, x_{N−1}] / I_r` with `I_r` the ideal of maximal minors of the `(r+1) × (N−r)`
Hankel matrix, and let `δ = det (x_{i+j})_{i,j<r}` be the leading `r × r` minor.  Then

`A_δ ≅ K[y_0, …, y_{2r−1}]_δ`,

so `A_δ` is a localized polynomial ring and in particular integrally closed.

The map `y_k ↦ x_k` is injective because the first `2r` coordinates are algebraically independent
in `A`.  It is onto after inverting `δ`: for `n ≥ 2r` the maximal minor with columns
`0, …, r−1, n−r` is the bordered matrix `[[H, w], [v, x_n]]` with `H = (x_{i+j})_{i,j<r}`,
`v = (x_{r+j})_j`, `w = (x_{i+n−r})_i`, and its vanishing gives the Schur-complement recurrence
`x_n = v H⁻¹ w`, which expresses `x_n` through coordinates of smaller index.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial

noncomputable section

variable (K : Type) [Field K]

/-- The coordinate `x_n`, zero outside the range. -/
def hankelCoord (N n : ℕ) : MvPolynomial (Fin N) K := if h : n < N then X ⟨n, h⟩ else 0

/-- The leading `r × r` Hankel minor `det (x_{i+j})_{i,j<r}`. -/
def hankelLeadMinor (N r : ℕ) : MvPolynomial (Fin N) K :=
  Matrix.det (Matrix.of fun i j : Fin r => hankelCoord K N ((i : ℕ) + j))

/-- The Hankel secant ring `K[x] / I_r`. -/
abbrev HankelSecantRing (N r : ℕ) := MvPolynomial (Fin N) K ⧸ RHTower.finiteHankelSecantIdeal K N r

/-- The chart map `y_k ↦ x_k` on the first `2r` coordinates. -/
def hankelChartHom (N r : ℕ) : MvPolynomial (Fin (2 * r)) K →ₐ[K] HankelSecantRing K N r :=
  aeval fun k => Ideal.Quotient.mk _ (hankelCoord K N k)

/-- The chart element `δ` of `A`. -/
def hankelChartElem (N r : ℕ) : HankelSecantRing K N r :=
  (hankelChartHom K N r).toRingHom (hankelLeadMinor K (2 * r) r)

theorem hankelChartHom_coord {N r : ℕ} {k : ℕ} (hk : k < 2 * r) :
    hankelChartHom K N r (hankelCoord K (2 * r) k) = Ideal.Quotient.mk _ (hankelCoord K N k) := by
  rw [hankelCoord, dif_pos hk, hankelChartHom, aeval_X]

theorem hankelChartElem_eq {N r : ℕ} :
    hankelChartElem K N r = Ideal.Quotient.mk _ (hankelLeadMinor K N r) := by
  rw [hankelChartElem, hankelLeadMinor, hankelLeadMinor, RingHom.map_det, RingHom.map_det]
  congr 1
  ext i j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, AlgHom.toRingHom_eq_coe,
    RingHom.coe_coe]
  exact hankelChartHom_coord K (by have := i.isLt; have := j.isLt; omega)

/-- **The first `2r` coordinates are algebraically independent.** -/
theorem hankelChartHom_injective [CharZero K] {N r : ℕ} (hN : 2 * r ≤ N) :
    Function.Injective (hankelChartHom K N r) := by
  have hind := algebraicIndependent_hankelSecantQuotient K hN
  let e : Fin (2 * r) → Fin r ⊕ Fin r := fun k => finSumFinEquiv.symm (Fin.cast (by omega) k)
  have he : Function.Injective e := by
    intro a b h
    have := finSumFinEquiv.symm.injective h
    exact Fin.ext (by simpa using congrArg Fin.val this)
  have hcomp := hind.comp e he
  rw [algebraicIndependent_iff_injective_aeval] at hcomp
  have heq : hankelChartHom K N r = aeval ((fun k : Fin r ⊕ Fin r =>
      Ideal.Quotient.mk (RHTower.finiteHankelSecantIdeal K N r)
        (MvPolynomial.X ⟨confluentExp k, lt_of_lt_of_le (confluentExp_lt k) hN⟩)) ∘ e) := by
    unfold hankelChartHom
    congr 1
    funext k
    simp only [Function.comp, e, confluentExp, Equiv.apply_symm_apply, Fin.val_cast]
    rw [hankelCoord, dif_pos (by have := k.isLt; omega)]
  rw [heq]
  exact hcomp

theorem hankelLeadMinor_ne_zero {r : ℕ} : hankelLeadMinor K (2 * r) r ≠ 0 := by
  classical
  intro h
  -- evaluate at the point `y_{r-1} = 1`, all other coordinates zero
  have hev := congrArg (MvPolynomial.eval fun k : Fin (2 * r) =>
    if (k : ℕ) + 1 = r then (1 : K) else 0) h
  rw [map_zero, hankelLeadMinor, RingHom.map_det] at hev
  have hmat : (MvPolynomial.eval fun k : Fin (2 * r) => if (k : ℕ) + 1 = r then (1 : K) else 0).mapMatrix
      (Matrix.of fun i j : Fin r => hankelCoord K (2 * r) ((i : ℕ) + j)) =
      (Equiv.toPEquiv Fin.revPerm).toMatrix := by
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, hankelCoord]
    rw [dif_pos (by have := i.isLt; have := j.isLt; omega), eval_X]
    simp only [PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Option.mem_def, Option.some.injEq,
      Fin.revPerm_apply]
    by_cases hij : (i : ℕ) + j + 1 = r
    · have hj : Fin.rev i = j := Fin.ext (by rw [Fin.val_rev]; omega)
      simp [hij, hj]
    · have hj : Fin.rev i ≠ j := fun h' => hij (by
        have := congrArg Fin.val h'; rw [Fin.val_rev] at this; omega)
      simp [hij, hj]
  rw [hmat, Matrix.det_permutation] at hev
  have := Int.units_eq_one_or (Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin r)))
  rcases this with h1 | h1 <;> rw [h1] at hev <;> simp at hev

/-! ## The localized chart -/

/-- The localized chart map `K[y]_δ → A_δ`. -/
def hankelChartLoc (N r : ℕ) :
    Localization.Away (hankelLeadMinor K (2 * r) r) →+* Localization.Away (hankelChartElem K N r) :=
  IsLocalization.Away.lift (hankelLeadMinor K (2 * r) r)
    (g := (algebraMap (HankelSecantRing K N r) (Localization.Away (hankelChartElem K N r))).comp
      (hankelChartHom K N r).toRingHom)
    (IsLocalization.Away.algebraMap_isUnit (hankelChartElem K N r))

theorem hankelChartLoc_algebraMap (N r : ℕ) (p : MvPolynomial (Fin (2 * r)) K) :
    hankelChartLoc K N r (algebraMap _ _ p) =
      algebraMap (HankelSecantRing K N r) _ (hankelChartHom K N r p) := by
  unfold hankelChartLoc IsLocalization.Away.lift
  rw [IsLocalization.lift_eq]
  rfl

instance hankelSecantIdeal_isPrime (N r : ℕ) : (RHTower.finiteHankelSecantIdeal K N r).IsPrime :=
  RHTower.finiteHankelSecantIdeal_isPrime K N r

/-- **The localized chart map is injective.** -/
theorem hankelChartLoc_injective [CharZero K] {N r : ℕ} (hN : 2 * r ≤ N) :
    Function.Injective (hankelChartLoc K N r) := by
  rw [injective_iff_map_eq_zero]
  intro z hz
  obtain ⟨⟨p, ⟨_, k, rfl⟩⟩, rfl⟩ :=
    IsLocalization.mk'_surjective (Submonoid.powers (hankelLeadMinor K (2 * r) r)) z
  simp only at hz ⊢
  set u := IsLocalization.Away.invSelf (S := Localization.Away (hankelLeadMinor K (2 * r) r))
    (hankelLeadMinor K (2 * r) r) with hu_def
  have hsplit : IsLocalization.mk' (Localization.Away (hankelLeadMinor K (2 * r) r)) p
      (⟨hankelLeadMinor K (2 * r) r ^ k, k, rfl⟩ : Submonoid.powers _) =
      algebraMap _ _ p * u ^ k := by
    rw [IsLocalization.mk'_eq_mul_mk'_one, hu_def, IsLocalization.Away.invSelf,
      ← IsLocalization.mk'_pow]
    simp
  rw [hsplit, map_mul, hankelChartLoc_algebraMap] at hz
  have hu : IsUnit (hankelChartLoc K N r (u ^ k)) := by
    refine IsUnit.map _ (IsUnit.pow k ?_)
    have hinv := IsLocalization.Away.mul_invSelf
      (S := Localization.Away (hankelLeadMinor K (2 * r) r)) (hankelLeadMinor K (2 * r) r)
    exact IsUnit.of_mul_eq_one _ ((mul_comm _ _).trans hinv)
  have h0 := (hu.mul_left_eq_zero).mp hz
  rw [IsLocalization.map_eq_zero_iff (Submonoid.powers (hankelChartElem K N r))] at h0
  obtain ⟨⟨_, j, rfl⟩, hj⟩ := h0
  have h1 : hankelChartHom K N r (hankelLeadMinor K (2 * r) r ^ j * p) = 0 := by
    rw [map_mul, map_pow]
    exact hj
  have h2 := hankelChartHom_injective K hN (h1.trans (map_zero _).symm)
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact absurd (pow_eq_zero_iff'.mp h3).1 (hankelLeadMinor_ne_zero K)
  · rw [hsplit, h3, map_zero, zero_mul]

variable {K}

/-- The coordinates in the localized ring. -/
def hankelLocCoord (N r n : ℕ) : Localization.Away (hankelChartElem K N r) :=
  algebraMap (HankelSecantRing K N r) _
    (Ideal.Quotient.mk (RHTower.finiteHankelSecantIdeal K N r) (hankelCoord K N n))

/-- The leading block in the localized ring. -/
def hankelLocBlock (N r : ℕ) : Matrix (Fin r) (Fin r) (Localization.Away (hankelChartElem K N r)) :=
  Matrix.of fun i j => hankelLocCoord N r ((i : ℕ) + j)

theorem isUnit_det_hankelLocBlock (N r : ℕ) : IsUnit (hankelLocBlock (K := K) N r).det := by
  have h1 : (hankelLocBlock (K := K) N r).det =
      algebraMap (HankelSecantRing K N r) (Localization.Away (hankelChartElem K N r))
        (Ideal.Quotient.mk _ (hankelLeadMinor K N r)) := by
    rw [hankelLeadMinor, RingHom.map_det, RingHom.map_det]
    rfl
  have h2 : (Ideal.Quotient.mk (RHTower.finiteHankelSecantIdeal K N r) (hankelLeadMinor K N r)) =
      hankelChartElem K N r := (hankelChartElem_eq K).symm
  rw [h1, h2]
  exact IsLocalization.Away.algebraMap_isUnit _

/-- The column selection `0, …, r−1, n−r` of the bordered minor. -/
def borderCols (r n : ℕ) : Fin (r + 1) → ℕ := fun j => if (j : ℕ) < r then j else n - r

theorem borderCols_strictMono {r n : ℕ} (hn : 2 * r ≤ n) : StrictMono (borderCols r n) := by
  intro a b hab
  have hab' : (a : ℕ) < b := hab
  unfold borderCols
  have hb := b.isLt
  by_cases ha : (a : ℕ) < r
  · by_cases hbr : (b : ℕ) < r
    · rw [if_pos ha, if_pos hbr]; exact hab'
    · rw [if_pos ha, if_neg hbr]; omega
  · omega

/-- **The bordered-minor recurrence.**  In `A_δ`, for `2r ≤ n < N`,
`x_n = Σ_{j,i} x_{r+j} (H⁻¹)_{ji} x_{i+n−r}`. -/
theorem hankelLocCoord_eq_sum {N r n : ℕ} (hN : 2 * r ≤ N) (hn : 2 * r ≤ n) (hnN : n < N) :
    hankelLocCoord (K := K) N r n = ∑ j : Fin r, ∑ i : Fin r,
      hankelLocCoord N r (r + j) * (hankelLocBlock (K := K) N r)⁻¹ j i *
        hankelLocCoord N r ((i : ℕ) + (n - r)) := by
  classical
  set L := Localization.Away (hankelChartElem K N r)
  set ι : MvPolynomial (Fin N) K →+* L :=
    (algebraMap (HankelSecantRing K N r) L).comp (Ideal.Quotient.mk _) with hι
  have hbound : ∀ j, (r + 1) + borderCols r n j ≤ N := by
    intro j
    unfold borderCols
    split_ifs with h
    · omega
    · omega
  have hmem : RHTower.finiteHankelMaximalMinorOver K (borderCols r n) hbound ∈
      RHTower.finiteHankelSecantIdeal K N r :=
    Ideal.subset_span ⟨borderCols r n, hbound, borderCols_strictMono hn, rfl⟩
  have hzero : ι (RHTower.finiteHankelMaximalMinorOver K (borderCols r n) hbound) = 0 := by
    rw [hι, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem.mpr hmem, map_zero]
  rw [RHTower.finiteHankelMaximalMinorOver, RingHom.map_det] at hzero
  set M := ι.mapMatrix (fun i j : Fin (r + 1) =>
    (X (RHTower.finiteHankelIndex (borderCols r n) hbound i j) : MvPolynomial (Fin N) K)) with hM
  set H := hankelLocBlock (K := K) N r with hH
  set B : Matrix (Fin r) (Fin 1) L := fun i _ => hankelLocCoord N r ((i : ℕ) + (n - r))
  set C : Matrix (Fin 1) (Fin r) L := fun _ j => hankelLocCoord N r (r + j)
  set D : Matrix (Fin 1) (Fin 1) L := fun _ _ => hankelLocCoord N r n
  have hcoord : ∀ m (hm : m < N), ι (X ⟨m, hm⟩) = hankelLocCoord N r m := by
    intro m hm
    rw [hankelLocCoord, hankelCoord, dif_pos hm]
    rfl
  have hblocks : M.submatrix finSumFinEquiv finSumFinEquiv = Matrix.fromBlocks H B C D := by
    ext a b
    rcases a with i | i <;> rcases b with j | j
    · simp only [Matrix.submatrix_apply, Matrix.fromBlocks_apply₁₁, hM, RingHom.mapMatrix_apply,
        Matrix.map_apply, finSumFinEquiv_apply_left, RHTower.finiteHankelIndex, hH,
        hankelLocBlock, Matrix.of_apply]
      rw [hcoord]
      congr 1
      simp [borderCols, Fin.val_castAdd]
    · simp only [Matrix.submatrix_apply, Matrix.fromBlocks_apply₁₂, hM, RingHom.mapMatrix_apply,
        Matrix.map_apply, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right,
        RHTower.finiteHankelIndex, B]
      rw [hcoord]
      congr 1
      simp [borderCols, Fin.val_natAdd, Fin.val_castAdd, Fin.fin_one_eq_zero j]
    · simp only [Matrix.submatrix_apply, Matrix.fromBlocks_apply₂₁, hM, RingHom.mapMatrix_apply,
        Matrix.map_apply, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right,
        RHTower.finiteHankelIndex, C]
      rw [hcoord]
      congr 1
      simp [borderCols, Fin.val_natAdd, Fin.val_castAdd, Fin.fin_one_eq_zero i]
    · simp only [Matrix.submatrix_apply, Matrix.fromBlocks_apply₂₂, hM, RingHom.mapMatrix_apply,
        Matrix.map_apply, finSumFinEquiv_apply_right, RHTower.finiteHankelIndex, D]
      rw [hcoord]
      congr 1
      simp [borderCols, Fin.val_natAdd, Fin.fin_one_eq_zero i, Fin.fin_one_eq_zero j]
      omega
  haveI : Invertible H.det := (isUnit_det_hankelLocBlock (K := K) N r).invertible
  haveI : Invertible H := Matrix.invertibleOfDetInvertible H
  have hdet : M.det = H.det * (D - C * ⅟H * B).det := by
    rw [← Matrix.det_submatrix_equiv_self finSumFinEquiv, hblocks, Matrix.det_fromBlocks₁₁]
  rw [hzero] at hdet
  have hD : (D - C * ⅟H * B).det = 0 :=
    (isUnit_det_hankelLocBlock (K := K) N r).mul_right_eq_zero.mp hdet.symm
  rw [Matrix.det_unique] at hD
  have h00 : D 0 0 = (C * ⅟H * B) 0 0 := by
    rw [Matrix.sub_apply] at hD
    exact sub_eq_zero.mp hD
  rw [Matrix.invOf_eq_nonsing_inv] at h00
  simp only [D] at h00
  rw [h00, Matrix.mul_apply]
  simp only [Matrix.mul_apply, C, B]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun x _ => Finset.sum_mul _ _ _

/-! ## Surjectivity and integral closure -/

variable (K)

/-- The leading block over the polynomial chart. -/
def hankelChartBlock (r : ℕ) :
    Matrix (Fin r) (Fin r) (Localization.Away (hankelLeadMinor K (2 * r) r)) :=
  Matrix.of fun i j => algebraMap _ _ (hankelCoord K (2 * r) ((i : ℕ) + j))

theorem mapMatrix_hankelChartBlock {N r : ℕ} :
    (hankelChartLoc K N r).mapMatrix (hankelChartBlock K r) = hankelLocBlock (K := K) N r := by
  ext i j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, hankelChartBlock, hankelLocBlock,
    Matrix.of_apply, hankelChartLoc_algebraMap, hankelLocCoord]
  rw [hankelChartHom_coord K (by have := i.isLt; have := j.isLt; omega)]

theorem hankelLocCoord_mem_range_of_lt {N r n : ℕ} (hn : n < 2 * r) :
    hankelLocCoord (K := K) N r n ∈ (hankelChartLoc K N r).range :=
  ⟨algebraMap _ _ (hankelCoord K (2 * r) n), by
    rw [hankelChartLoc_algebraMap, hankelChartHom_coord K hn]; rfl⟩

theorem inv_hankelLocBlock_mem_range {N r : ℕ} (i j : Fin r) :
    (hankelLocBlock (K := K) N r)⁻¹ i j ∈ (hankelChartLoc K N r).range := by
  classical
  set f := hankelChartLoc K N r
  set H₀ := hankelChartBlock K r
  have hdet₀ : H₀.det = algebraMap _ _ (hankelLeadMinor K (2 * r) r) :=
    (RingHom.map_det (algebraMap (MvPolynomial (Fin (2 * r)) K)
      (Localization.Away (hankelLeadMinor K (2 * r) r)))
      (Matrix.of fun i j : Fin r => hankelCoord K (2 * r) ((i : ℕ) + j))).symm
  set u := IsLocalization.Away.invSelf (S := Localization.Away (hankelLeadMinor K (2 * r) r))
    (hankelLeadMinor K (2 * r) r)
  have hu : H₀.det * u = 1 := by
    rw [hdet₀]; exact IsLocalization.Away.mul_invSelf _
  have hH : f.mapMatrix H₀ = hankelLocBlock (K := K) N r := mapMatrix_hankelChartBlock K
  have hdet : (hankelLocBlock (K := K) N r).det = f H₀.det := by
    rw [← hH, RingHom.map_det]
  have hinv : Ring.inverse (hankelLocBlock (K := K) N r).det = f u := by
    have hunit := isUnit_det_hankelLocBlock (K := K) N r
    have h1 : (hankelLocBlock (K := K) N r).det * f u = 1 := by
      rw [hdet, ← map_mul, hu, map_one]
    rw [← mul_one (Ring.inverse (hankelLocBlock (K := K) N r).det),
      Ring.inverse_mul_eq_iff_eq_mul _ _ _ hunit, h1]
  rw [Matrix.inv_def, Matrix.smul_apply, hinv, ← hH, ← RingHom.map_adjugate, smul_eq_mul]
  exact ⟨u * H₀.adjugate i j, by rw [map_mul]; rfl⟩

theorem hankelLocCoord_mem_range [CharZero K] {N r : ℕ} (hN : 2 * r ≤ N) :
    ∀ n, n < N → hankelLocCoord (K := K) N r n ∈ (hankelChartLoc K N r).range := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hnN
    by_cases hn : n < 2 * r
    · exact hankelLocCoord_mem_range_of_lt K hn
    rw [hankelLocCoord_eq_sum hN (by omega) hnN]
    refine Subring.sum_mem _ fun j _ => Subring.sum_mem _ fun i _ => ?_
    refine Subring.mul_mem _ (Subring.mul_mem _ ?_ (inv_hankelLocBlock_mem_range K j i)) ?_
    · exact hankelLocCoord_mem_range_of_lt K (by have := j.isLt; omega)
    · exact ih _ (by have := i.isLt; omega) (by have := i.isLt; omega)

theorem algebraMap_mem_range [CharZero K] {N r : ℕ} (hN : 2 * r ≤ N) (a : HankelSecantRing K N r) :
    algebraMap _ (Localization.Away (hankelChartElem K N r)) a ∈ (hankelChartLoc K N r).range := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
  induction p using MvPolynomial.induction_on with
  | C c =>
      refine ⟨algebraMap _ _ (MvPolynomial.C c : MvPolynomial (Fin (2 * r)) K), ?_⟩
      rw [hankelChartLoc_algebraMap, hankelChartHom, aeval_C]
      rfl
  | add p q hp hq =>
      rw [map_add, map_add]
      exact Subring.add_mem _ hp hq
  | mul_X p n hp =>
      rw [map_mul, map_mul]
      refine Subring.mul_mem _ hp ?_
      have h := hankelLocCoord_mem_range K hN n n.isLt
      rwa [hankelLocCoord, hankelCoord, dif_pos n.isLt] at h

/-- **The localized chart map is onto.** -/
theorem hankelChartLoc_surjective [CharZero K] {N r : ℕ} (hN : 2 * r ≤ N) :
    Function.Surjective (hankelChartLoc K N r) := by
  intro z
  obtain ⟨⟨a, ⟨_, k, rfl⟩⟩, rfl⟩ :=
    IsLocalization.mk'_surjective (Submonoid.powers (hankelChartElem K N r)) z
  set u := IsLocalization.Away.invSelf (S := Localization.Away (hankelLeadMinor K (2 * r) r))
    (hankelLeadMinor K (2 * r) r)
  have hu : algebraMap _ (Localization.Away (hankelChartElem K N r)) (hankelChartElem K N r) *
      hankelChartLoc K N r u = 1 := by
    have h1 := congrArg (hankelChartLoc K N r) (IsLocalization.Away.mul_invSelf
      (S := Localization.Away (hankelLeadMinor K (2 * r) r)) (hankelLeadMinor K (2 * r) r))
    rw [map_mul, hankelChartLoc_algebraMap, map_one] at h1
    exact h1
  obtain ⟨b, hb⟩ := algebraMap_mem_range K hN a
  refine ⟨b * u ^ k, ?_⟩
  simp only
  rw [IsLocalization.eq_mk'_iff_mul_eq, map_mul, map_pow, hb, map_pow, mul_assoc, ← mul_pow,
    mul_comm (hankelChartLoc K N r u), hu, one_pow, mul_one]

/-- **The leading-block chart.**  `A_δ ≅ K[y_0, …, y_{2r−1}]_δ`. -/
def hankelChartEquiv [CharZero K] {N r : ℕ} (hN : 2 * r ≤ N) :
    Localization.Away (hankelLeadMinor K (2 * r) r) ≃+* Localization.Away (hankelChartElem K N r) :=
  RingEquiv.ofBijective (hankelChartLoc K N r)
    ⟨hankelChartLoc_injective K hN, hankelChartLoc_surjective K hN⟩

/-- **The leading-block chart is integrally closed.** -/
theorem isIntegrallyClosed_hankelChart [CharZero K] {N r : ℕ} (hN : 2 * r ≤ N) :
    IsIntegrallyClosed (Localization.Away (hankelChartElem K N r)) := by
  haveI : IsIntegrallyClosed (Localization.Away (hankelLeadMinor K (2 * r) r)) :=
    isIntegrallyClosed_of_isLocalization _ (Submonoid.powers (hankelLeadMinor K (2 * r) r))
      (powers_le_nonZeroDivisors_of_noZeroDivisors (hankelLeadMinor_ne_zero K))
  exact IsIntegrallyClosed.of_equiv (hankelChartEquiv K hN)

end

end GaloisForLFunctions.HTGeometry
