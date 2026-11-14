import GaloisForLFunctions.GreenCalculusOfThePrimeFreeWindow.TheFirstOverlapStepIsOneBoundStateOfTheMiddleDressedByTheAttractionOfItsTwoEnds

/-!
# A thin end is logarithmically stiff and a floor extends the bound range

Adjacent blocks are coupled with order one at every block size, so adding an end to a bound
window is not a small perturbation of its form in norm. It is a small perturbation of its bound
states, because a thin end is stiff.

* **A thin window is stiff** (`log_sub_two_le_blockPotential_of_thin`,
  `neutralWindow_form_ge_of_thin`): if `K J ≤ R`, `K ≥ 16`, every block of `(R, R + J]` has
  potential at least `log K − 2`, and the neutral form is at least `log K − 2`. The potential is
  the density `log R + O(1)` minus the jets to the `J` blocks of the window, `log J + O(1)`.
* **The coupling of two adjacent windows is bounded at every block size**
  (`dotProduct_adjacentCoupling_mulVec_sq_le`): by `24 + 2 Σ_{k ≤ Q} Λ(k)`, and by `26` when
  only the prime two is admitted.
* **The attraction of a thin end vanishes logarithmically** (`thin_attraction_form_le`):
  `C N⁻¹ Cᵀ ⪯ 676/(log K − 2)`. The window and its first part dressed by the thin end hold the
  same number of bound states (`hermNegIndex_neutralWindow_eq_of_thin_tail`).
* **A floor extends the bound range** (`exists_oneBoundState_neutralWindow_of_thin_tail`): if
  `(R, R + J]` holds one bound state with floor `c` on the complement of its ground vector and
  `log K ≥ c − ε + B²/ε + 2`, `B = 24 + 2 Σ_{k ≤ Q} Λ(k)`, `0 < ε < c`, then every window
  `(R, R + J + j]` with `K j ≤ R + J` holds one bound state with floor `c − ε`; up to ratio
  three `B² ≤ 676`. An end of relative width `δ` costs at most about `B²/log(1/δ)` of the floor.
  A range of ratios that is bound with a uniform floor is never closed; before a first unbound
  ratio the floors must tend to zero.
* **The certified range is not sharp** (`exists_oneBoundState_neutralWindow_beyond_certified`):
  the windows `(R, R + J + j]`, `50 J ≤ 53 R`, `K j ≤ R + J`, `log K ≥ 6760003`, hold one bound
  state with floor `1/10000` at every block size.

The extension is exponentially thin in `1/c`: an end of relative width `δ` has stiffness
`log(1/δ)` against a coupling of order one, and the losses `B²/log(1/δ)` of a chain of thin ends
of fixed total width are not summable.
-/

open Finset Matrix
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.AbsoluteGeometryOfSpecZ
open GaloisForLFunctions.MixingArithmeticOfTheFloorTrees

noncomputable section

namespace GaloisForLFunctions.GreenCalculusOfThePrimeFreeWindow

/-! ### Forms with a stiff corner -/

/-- Two bounds by the same quantity add like norms. -/
theorem sq_add_le_of_sq_le {x y a b P : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hP : 0 ≤ P)
    (hx : x ^ 2 ≤ a ^ 2 * P) (hy : y ^ 2 ≤ b ^ 2 * P) : (x + y) ^ 2 ≤ (a + b) ^ 2 * P := by
  have h0 : 0 ≤ a * b * P := mul_nonneg (mul_nonneg ha hb) hP
  have hxy : x * y ≤ a * b * P := by
    by_contra hgt
    rw [not_le] at hgt
    have h1 := mul_lt_mul'' hgt hgt h0 h0
    have h2 := mul_le_mul hx hy (sq_nonneg y) (mul_nonneg (sq_nonneg a) hP)
    nlinarith [h1, h2]
  nlinarith [hx, hy, hxy]

section Forms

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- A bound for a bilinear form is a bound for the transposed map. -/
theorem transpose_mulVec_sq_le {P : Matrix ι κ ℝ} {B : ℝ}
    (hP : ∀ (m : ι → ℝ) (e : κ → ℝ),
      (m ⬝ᵥ (P *ᵥ e)) ^ 2 ≤ B ^ 2 * ((m ⬝ᵥ m) * (e ⬝ᵥ e))) (m : ι → ℝ) :
    (Pᵀ *ᵥ m) ⬝ᵥ (Pᵀ *ᵥ m) ≤ B ^ 2 * (m ⬝ᵥ m) := by
  have h := hP m (Pᵀ *ᵥ m)
  have he : m ⬝ᵥ (P *ᵥ (Pᵀ *ᵥ m)) = (Pᵀ *ᵥ m) ⬝ᵥ (Pᵀ *ᵥ m) := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose]
  rw [he] at h
  have ht0 : 0 ≤ (Pᵀ *ᵥ m) ⬝ᵥ (Pᵀ *ᵥ m) := dotProduct_self_star_nonneg (v := Pᵀ *ᵥ m)
  have hm0 : 0 ≤ m ⬝ᵥ m := dotProduct_self_star_nonneg (v := m)
  by_contra hgt
  rw [not_le] at hgt
  have htpos : 0 < (Pᵀ *ᵥ m) ⬝ᵥ (Pᵀ *ᵥ m) :=
    lt_of_le_of_lt (mul_nonneg (sq_nonneg B) hm0) hgt
  nlinarith [mul_lt_mul_of_pos_right hgt htpos]

/-- **A stiff corner costs little of a floor.** Let `A ⪰ c` on a hyperplane, `E ⪰ s` and let the
coupling have norm at most `B`. If `s ≥ c − ε + B²/ε`, `ε > 0`, the block form is at least
`c − ε` on the vectors whose first part lies in the hyperplane. -/
theorem fromBlocks_form_ge_of_stiff_corner {A : Matrix ι ι ℝ} {ψ : ι → ℝ} {c s B ε : ℝ}
    (hε : 0 < ε) (hA : ∀ m : ι → ℝ, ψ ⬝ᵥ m = 0 → c * (m ⬝ᵥ m) ≤ m ⬝ᵥ (A *ᵥ m))
    (P : Matrix ι κ ℝ) {E : Matrix κ κ ℝ} (hE : ∀ e : κ → ℝ, s * (e ⬝ᵥ e) ≤ e ⬝ᵥ (E *ᵥ e))
    (hP : ∀ (m : ι → ℝ) (e : κ → ℝ),
      (m ⬝ᵥ (P *ᵥ e)) ^ 2 ≤ B ^ 2 * ((m ⬝ᵥ m) * (e ⬝ᵥ e)))
    (hs : c - ε + B ^ 2 / ε ≤ s) {m : ι → ℝ} (hm : ψ ⬝ᵥ m = 0) (e : κ → ℝ) :
    (c - ε) * (m ⬝ᵥ m + e ⬝ᵥ e) ≤
      Sum.elim m e ⬝ᵥ (fromBlocks A P Pᵀ E *ᵥ Sum.elim m e) := by
  rw [dotProduct_fromBlocks_mulVec]
  have h1 := hA m hm
  have h2 := hE e
  have h3 := hP m e
  have hx0 : 0 ≤ m ⬝ᵥ m := dotProduct_self_star_nonneg (v := m)
  have hy0 : 0 ≤ e ⬝ᵥ e := dotProduct_self_star_nonneg (v := e)
  have hd0 : 0 ≤ B ^ 2 / ε := by positivity
  have hd : ε * (B ^ 2 / ε) = B ^ 2 := by
    field_simp
  generalize B ^ 2 / ε = d at hs hd0 hd
  generalize m ⬝ᵥ m = x at h1 h3 hx0 ⊢
  generalize e ⬝ᵥ e = y at h2 h3 hy0 ⊢
  generalize m ⬝ᵥ (P *ᵥ e) = t at h3 ⊢
  -- `2|t| ≤ ε x + d y` by the inequality of the means
  have huv : ε * x * (d * y) = B ^ 2 * (x * y) := by
    have h : ε * x * (d * y) = ε * d * (x * y) := by ring
    rw [h, hd]
  have hX : 0 ≤ ε * x + d * y :=
    add_nonneg (mul_nonneg hε.le hx0) (mul_nonneg hd0 hy0)
  have hsq : (2 * t) ^ 2 ≤ (ε * x + d * y) ^ 2 := by
    nlinarith [sq_nonneg (ε * x - d * y), huv, h3]
  have hneg : -(ε * x + d * y) ≤ 2 * t := (abs_le_of_sq_le_sq' hsq hX).1
  have hsy : (c - ε + d) * y ≤ s * y := mul_le_mul_of_nonneg_right hs hy0
  nlinarith [h1, h2, hneg, hsy]

/-- **A positive eigenvector of negative eigenvalue and a floor on a hyperplane give one bound
state.** The functional of the hyperplane does not vanish at the eigenvector, whose energy is
negative. -/
theorem exists_oneBoundState_of_pos_eigenvector_of_hyperplane [Nonempty ι]
    {M : Matrix ι ι ℝ} (hM : ∀ i j, M i j = M j i) {φ₀ : ι → ℝ} (hφ₀ : ∀ i, 0 < φ₀ i)
    {lam : ℝ} (hlam : lam < 0) (heig : M *ᵥ φ₀ = lam • φ₀) {c : ℝ} (hc : 0 < c) {ℓ : ι → ℝ}
    (hfloor : ∀ y : ι → ℝ, ℓ ⬝ᵥ y = 0 → c * (y ⬝ᵥ y) ≤ y ⬝ᵥ (M *ᵥ y)) :
    ∃ φ : ι → ℝ, (∀ i, 0 < φ i) ∧ OneBoundState M φ (-lam) c := by
  have hs2 : 0 < φ₀ ⬝ᵥ φ₀ :=
    Finset.sum_pos (fun i _ => mul_pos (hφ₀ i) (hφ₀ i)) Finset.univ_nonempty
  set s := Real.sqrt (φ₀ ⬝ᵥ φ₀) with hs
  have hspos : 0 < s := Real.sqrt_pos.mpr hs2
  have hss : s * s = φ₀ ⬝ᵥ φ₀ := Real.mul_self_sqrt hs2.le
  set φ : ι → ℝ := s⁻¹ • φ₀ with hφdef
  have hφpos : ∀ i, 0 < φ i := fun i => by
    simp only [hφdef, Pi.smul_apply, smul_eq_mul]
    exact mul_pos (inv_pos.mpr hspos) (hφ₀ i)
  have hunit : φ ⬝ᵥ φ = 1 := by
    rw [hφdef, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, ← hss]
    field_simp
  have heig' : M *ᵥ φ = (-(-lam)) • φ := by
    rw [neg_neg, hφdef, Matrix.mulVec_smul, heig, smul_comm]
  have hℓ : ℓ ⬝ᵥ φ ≠ 0 := by
    intro h0
    have hf := hfloor φ h0
    have hE : φ ⬝ᵥ (M *ᵥ φ) = lam * (φ ⬝ᵥ φ) := by
      rw [heig', neg_neg]
      exact dotProduct_smul lam φ φ
    rw [hE, hunit] at hf
    linarith
  exact ⟨φ, hφpos, hM, hunit, heig', neg_pos.mpr hlam, hc,
    floor_orthogonal_of_floor_hyperplane hM (neg_pos.mpr hlam).le hc.le heig' hℓ hfloor⟩

end Forms

/-! ### A thin window is stiff -/

/-- **The potential of a thin window is logarithmic in its thinness**: if `K J ≤ R` with
`K ≥ 16`, every block of `(R, R + J]` has potential at least `log K − 2`. -/
theorem log_sub_two_le_blockPotential_of_thin {Q R J j K : ℕ} (hK : 16 ≤ K) (hKJ : K * J ≤ R)
    (hj : j < J) : Real.log K - 2 ≤ blockPotential Q R J j := by
  have hJ : 16 * J ≤ R := (Nat.mul_le_mul_right J hK).trans hKJ
  have hJ1 : 1 ≤ J := by omega
  have hJr : (0 : ℝ) < J := by exact_mod_cast hJ1
  have hKr : (0 : ℝ) < K := by exact_mod_cast (by omega : 0 < K)
  have hKJa : K * J ≤ R + j := hKJ.trans (Nat.le_add_right R j)
  rw [blockPotential_eq_of_window (by omega) hj]
  have hρ : blockDensity (R + j) =
      xLogXStep (R + j) - (Real.eulerMascheroniConstant + Real.log (2 * Real.pi)) := rfl
  rw [hρ]
  set a : ℕ := R + j
  set m : ℕ := R + j + R
  have ha1 : 1 ≤ a := by omega
  have hm1 : 1 ≤ m := by omega
  have hb_a := log_add_half_sub_le_xLogXStep ha1
  have hb_mJ := xLogXStep_le_log_add_half (m + J)
  have hb_m := log_add_half_sub_le_xLogXStep hm1
  have hb_j := xLogXStep_le_log_add_half j
  have hb_Jj := xLogXStep_le_log_add_half (J - 1 - j)
  -- the density: `a + 1/2 ≥ K J`
  have haR : (K : ℝ) * J ≤ (a : ℝ) + 1 / 2 := by
    have h : ((K * J : ℕ) : ℝ) ≤ (a : ℝ) := by exact_mod_cast hKJa
    push_cast at h
    linarith
  have hlogA : Real.log K + Real.log J ≤ Real.log ((a : ℝ) + 1 / 2) := by
    rw [← Real.log_mul hKr.ne' hJr.ne']
    exact Real.log_le_log (mul_pos hKr hJr) haR
  -- the jets inside the window: `(j + 1/2) + (J − 1 − j + 1/2) = J`
  set x : ℝ := (j : ℝ) + 1 / 2
  set y : ℝ := ((J - 1 - j : ℕ) : ℝ) + 1 / 2
  have hx : 0 < x := by positivity
  have hy : 0 < y := by positivity
  have hxy_sum : x + y = (J : ℝ) := by
    dsimp [x, y]
    have hnat : j + (J - 1 - j) + 1 = J := by omega
    have hcast : (j : ℝ) + ((J - 1 - j : ℕ) : ℝ) + 1 = (J : ℝ) := by exact_mod_cast hnat
    linarith
  have hxy_prod : x * y ≤ ((J : ℝ) / 2) ^ 2 := by
    have hsq : 0 ≤ (x - y) ^ 2 := sq_nonneg _
    have hid : ((J : ℝ) / 2) ^ 2 - x * y = (x - y) ^ 2 / 4 := by
      rw [← hxy_sum]
      ring
    linarith
  have hlog_xy : Real.log x + Real.log y ≤ 2 * (Real.log J - Real.log 2) := by
    rw [← Real.log_mul hx.ne' hy.ne']
    have hle := Real.log_le_log (mul_pos hx hy) hxy_prod
    have hrhs : Real.log (((J : ℝ) / 2) ^ 2) = 2 * (Real.log J - Real.log 2) := by
      rw [Real.log_pow, Real.log_div hJr.ne' (by norm_num)]
      push_cast
      ring
    rwa [hrhs] at hle
  -- the jets to the mirror image: `m ≥ 32 J`
  have hmR : (32 : ℝ) * J ≤ (m : ℝ) + 1 / 2 := by
    have h : ((32 * J : ℕ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast (show 32 * J ≤ m by omega)
    push_cast at h
    linarith
  have hmpos : (0 : ℝ) < (m : ℝ) + 1 / 2 := by positivity
  have hlogM : Real.log (((m + J : ℕ) : ℝ) + 1 / 2) - Real.log ((m : ℝ) + 1 / 2) ≤ 1 / 32 := by
    have hpos : (0 : ℝ) < ((m + J : ℕ) : ℝ) + 1 / 2 := by positivity
    rw [← Real.log_div hpos.ne' hmpos.ne']
    have h := Real.log_le_sub_one_of_pos (div_pos hpos hmpos)
    have h2 : (((m + J : ℕ) : ℝ) + 1 / 2) / ((m : ℝ) + 1 / 2) - 1 ≤ 1 / 32 := by
      rw [div_sub_one hmpos.ne', div_le_div_iff₀ hmpos (by norm_num)]
      push_cast
      linarith
    linarith
  have ha16 : (16 : ℝ) ≤ a := by exact_mod_cast (show 16 ≤ a by omega)
  have hm32 : (32 : ℝ) ≤ m := by exact_mod_cast (show 32 ≤ m by omega)
  have hrem_a : 1 / ((4 * (a : ℝ) + 1) * (4 * (a : ℝ) + 3)) ≤ 1 / (65 * 67) :=
    one_div_le_one_div_of_le (by norm_num) (mul_le_mul (by linarith) (by linarith) (by norm_num)
      (by positivity))
  have hrem_m : 1 / ((4 * (m : ℝ) + 1) * (4 * (m : ℝ) + 3)) ≤ 1 / (129 * 131) :=
    one_div_le_one_div_of_le (by norm_num) (mul_le_mul (by linarith) (by linarith) (by norm_num)
      (by positivity))
  have hγ :=
    RHTower.eulerMascheroniConstant_lt_fiveHundredSeventySevenThousandTwoHundredSixteen_over_oneMillion
  have hπ : Real.log (2 * Real.pi) < Real.log 2 + 1.1447302 := by
    rw [log_two_pi]
    linarith [log_pi_lt]
  linarith [Real.log_two_gt_d9]

/-- **A thin window is stiff**: if `K J ≤ R` with `K ≥ 16`, the neutral form of `(R, R + J]` is
at least `log K − 2`. -/
theorem neutralWindow_form_ge_of_thin {Q R J K : ℕ} (hK : 16 ≤ K) (hKJ : K * J ≤ R)
    (e : Fin J → ℝ) :
    (Real.log K - 2) * (e ⬝ᵥ e) ≤ e ⬝ᵥ (neutralWindow Q R J *ᵥ e) := by
  have h := form_ge_of_offDiag_nonpos (neutralWindow_symm Q R J)
    (fun _ _ hij => (neutralWindow_neg_of_ne Q R hij).le) (B := -(Real.log K - 2))
    (fun p => by
      have hrow : (neutralWindow Q R J *ᵥ fun _ => (1 : ℝ)) p = ∑ q, neutralWindow Q R J p q := by
        simp only [Matrix.mulVec, dotProduct, mul_one]
      rw [neg_neg, ← hrow, neutralWindow_mulVec_one]
      exact log_sub_two_le_blockPotential_of_thin hK hKJ p.2) e
  rwa [neg_neg] at h

/-- The stiffness of a thin window is positive. -/
theorem log_sub_two_pos {K : ℕ} (hK : 16 ≤ K) : 0 < Real.log K - 2 := by
  have h : Real.log 16 ≤ Real.log K := Real.log_le_log (by norm_num) (by exact_mod_cast hK)
  rw [log_sixteen] at h
  linarith [Real.log_two_gt_d9]

/-! ### A window and an adjacent window -/

/-- The coupling of the window `(R, R + J]` to the adjacent window `(R + J, R + J + j]`. -/
def adjacentCoupling (Q R J j : ℕ) : Matrix (Fin J) (Fin j) ℝ :=
  Matrix.of fun i l => neutralBlock Q (R + i) (R + J + l)

/-- The jets between two adjacent windows. -/
def adjacentJet (R J j : ℕ) : Matrix (Fin J) (Fin j) ℝ :=
  Matrix.of fun i l => blockJet (R + i) (R + J + l)

/-- The contacts between two adjacent windows. -/
def adjacentContact (Q R J j : ℕ) : Matrix (Fin J) (Fin j) ℝ :=
  Matrix.of fun i l => floorContact Q (R + i) (R + J + l)

theorem adjacentJet_apply (R J j : ℕ) (i : Fin J) (l : Fin j) :
    adjacentJet R J j i l = blockJet (R + i) (R + J + l) := rfl

theorem adjacentContact_apply (Q R J j : ℕ) (i : Fin J) (l : Fin j) :
    adjacentContact Q R J j i l = floorContact Q (R + i) (R + J + l) := rfl

theorem adjacent_lt (R : ℕ) {J j : ℕ} (i : Fin J) (l : Fin j) : R + (i : ℕ) < R + J + l := by
  have := i.2
  omega

/-- The coupling of two adjacent windows is minus the jets minus the contacts. -/
theorem adjacentCoupling_eq (Q R J j : ℕ) :
    adjacentCoupling Q R J j = -adjacentJet R J j - adjacentContact Q R J j := by
  ext i l
  rw [Matrix.sub_apply, Matrix.neg_apply]
  exact neutralBlock_of_lt (adjacent_lt R i l) Q

theorem blockJet_pos_of_lt {x y : ℕ} (hxy : x < y) : 0 < blockJet x y := by
  rw [blockJet]
  have h1 := xLogXDiff_pos (n := x + y + 1) (by omega)
  have h2 := xLogXDiff_pos (n := y - x) (by omega)
  linarith

theorem floorContact_nonneg (Q x y : ℕ) : 0 ≤ floorContact Q x y := by
  rw [floorContact]
  refine Finset.sum_nonneg fun k _ => ?_
  split_ifs
  · exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg k)
  · exact le_rfl

/-- **A window is its first part, the adjacent part and their coupling.** -/
theorem neutralWindow_submatrix_finSumFinEquiv (Q R J j : ℕ) :
    (neutralWindow Q R (J + j)).submatrix finSumFinEquiv finSumFinEquiv =
      fromBlocks (neutralWindow Q R J) (adjacentCoupling Q R J j) (adjacentCoupling Q R J j)ᵀ
        (neutralWindow Q (R + J) j) := by
  ext (i | l) (i' | l')
  · rfl
  · show neutralBlock Q (R + (i : ℕ)) (R + (J + (l' : ℕ))) =
      neutralBlock Q (R + i) (R + J + l')
    rw [Nat.add_assoc]
  · show neutralBlock Q (R + (J + (l : ℕ))) (R + (i' : ℕ)) =
      neutralBlock Q (R + i') (R + J + l)
    rw [neutralBlock_comm, Nat.add_assoc]
  · show neutralBlock Q (R + (J + (l : ℕ))) (R + (J + (l' : ℕ))) =
      neutralBlock Q (R + J + l) (R + J + l')
    rw [Nat.add_assoc, Nat.add_assoc]

/-- The part of a vector on the first `J` blocks. -/
def headPart {J j : ℕ} (y : Fin (J + j) → ℝ) : Fin J → ℝ :=
  fun i => y (finSumFinEquiv (Sum.inl i))

/-- The part of a vector on the last `j` blocks. -/
def tailPart {J j : ℕ} (y : Fin (J + j) → ℝ) : Fin j → ℝ :=
  fun l => y (finSumFinEquiv (Sum.inr l))

/-- A functional of the first `J` blocks, extended by zero. -/
def headFunctional {J : ℕ} (ψ : Fin J → ℝ) (j : ℕ) : Fin (J + j) → ℝ :=
  Sum.elim ψ (fun _ => 0) ∘ finSumFinEquiv.symm

theorem sum_fin_add_eq {J j : ℕ} (f : Fin (J + j) → ℝ) :
    ∑ k, f k = ∑ i : Fin J, f (finSumFinEquiv (Sum.inl i)) +
      ∑ l : Fin j, f (finSumFinEquiv (Sum.inr l)) := by
  rw [← Equiv.sum_comp finSumFinEquiv f, Fintype.sum_sum_type]

theorem comp_finSumFinEquiv_eq {J j : ℕ} (y : Fin (J + j) → ℝ) :
    y ∘ finSumFinEquiv = Sum.elim (headPart y) (tailPart y) := by
  funext s
  rcases s with i | l <;> rfl

theorem dotProduct_self_eq_head_add_tail {J j : ℕ} (y : Fin (J + j) → ℝ) :
    y ⬝ᵥ y = headPart y ⬝ᵥ headPart y + tailPart y ⬝ᵥ tailPart y :=
  sum_fin_add_eq fun k => y k * y k

theorem headFunctional_dotProduct {J j : ℕ} (ψ : Fin J → ℝ) (y : Fin (J + j) → ℝ) :
    headFunctional ψ j ⬝ᵥ y = ψ ⬝ᵥ headPart y := by
  have h := sum_fin_add_eq fun k => headFunctional ψ j k * y k
  have h1 : ∀ i : Fin J, headFunctional ψ j (finSumFinEquiv (Sum.inl i)) = ψ i := fun i => by
    simp only [headFunctional, Function.comp_apply, Equiv.symm_apply_apply, Sum.elim_inl]
  have h2 : ∀ l : Fin j, headFunctional ψ j (finSumFinEquiv (Sum.inr l)) = 0 := fun l => by
    simp only [headFunctional, Function.comp_apply, Equiv.symm_apply_apply, Sum.elim_inr]
  simp only [h1, h2, zero_mul, Finset.sum_const_zero, add_zero] at h
  exact h

/-- The neutral form of a window in its first part and the adjacent part. -/
theorem neutralWindow_form_eq_head_tail (Q R J j : ℕ) (y : Fin (J + j) → ℝ) :
    y ⬝ᵥ (neutralWindow Q R (J + j) *ᵥ y) =
      Sum.elim (headPart y) (tailPart y) ⬝ᵥ
        (fromBlocks (neutralWindow Q R J) (adjacentCoupling Q R J j)
          (adjacentCoupling Q R J j)ᵀ (neutralWindow Q (R + J) j) *ᵥ
            Sum.elim (headPart y) (tailPart y)) := by
  rw [← dotProduct_submatrix_equiv_mulVec (neutralWindow Q R (J + j)) finSumFinEquiv y,
    neutralWindow_submatrix_finSumFinEquiv, comp_finSumFinEquiv_eq]

/-! ### The coupling of two adjacent windows -/

/-- **The jets between two adjacent windows have norm at most `24`** at every block size:
Hilbert's inequality. -/
theorem dotProduct_adjacentJet_mulVec_sq_le (R J j : ℕ) (m : Fin J → ℝ) (e : Fin j → ℝ) :
    (m ⬝ᵥ (adjacentJet R J j *ᵥ e)) ^ 2 ≤ 24 ^ 2 * ((m ⬝ᵥ m) * (e ⬝ᵥ e)) := by
  simpa only [show (6 * (4 : ℝ)) ^ 2 = 24 ^ 2 by norm_num] using
    dotProduct_mulVec_sq_le_of_inv_add (adjacentJet R J j)
      (r := fun i : Fin J => J - (i : ℕ)) (s := fun l : Fin j => (l : ℕ) + 1)
      (fun i₁ i₂ h => by
        have h' : J - (i₁ : ℕ) = J - (i₂ : ℕ) := h
        have := i₁.2
        have := i₂.2
        exact Fin.ext (by omega))
      (fun l₁ l₂ h => by
        have h' : (l₁ : ℕ) + 1 = (l₂ : ℕ) + 1 := h
        exact Fin.ext (by omega))
      (fun i => by have := i.2; omega) (fun l => by omega) (B := 4) (by norm_num)
      (fun i l => by
        have hi := i.2
        have hlt := adjacent_lt R i l
        show |adjacentJet R J j i l| ≤
          4 / (((J - (i : ℕ) : ℕ) : ℝ) + (((l : ℕ) + 1 : ℕ) : ℝ))
        rw [adjacentJet_apply, abs_of_pos (blockJet_pos_of_lt hlt)]
        refine (blockJet_le_two_div hlt).trans ?_
        rw [div_le_div_iff₀
          (by exact_mod_cast (by omega : 0 < R + J + (l : ℕ) - (R + (i : ℕ))))
          (by positivity)]
        have hnat : (J - (i : ℕ)) + ((l : ℕ) + 1) ≤
            2 * (R + J + (l : ℕ) - (R + (i : ℕ))) := by omega
        have h2 : ((((J - (i : ℕ)) + ((l : ℕ) + 1) : ℕ) : ℝ)) ≤
            (((2 * (R + J + (l : ℕ) - (R + (i : ℕ))) : ℕ) : ℝ)) := Nat.cast_le.mpr hnat
        rw [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at h2
        linarith) m e

/-- **The contacts between two adjacent windows have norm at most `2 Σ_{k ≤ Q} Λ(k)`.** -/
theorem dotProduct_adjacentContact_mulVec_sq_le (Q R J j : ℕ) (m : Fin J → ℝ)
    (e : Fin j → ℝ) :
    (m ⬝ᵥ (adjacentContact Q R J j *ᵥ e)) ^ 2 ≤
      (2 * primeContactSum Q) ^ 2 * ((m ⬝ᵥ m) * (e ⬝ᵥ e)) := by
  refine dotProduct_mulVec_sq_le_of_row_col_sum (adjacentContact Q R J j)
    (fun i l => floorContact_nonneg Q _ _) (by linarith [primeContactSum_nonneg Q])
    (fun i => ?_) (fun l => ?_) m e
  · have h := sum_floorContact_injective_le (q := fun l : Fin j => R + J + (l : ℕ))
      (fun l₁ l₂ h => by
        have h' : R + J + (l₁ : ℕ) = R + J + (l₂ : ℕ) := h
        exact Fin.ext (by omega)) Q (R + (i : ℕ))
    refine le_of_eq_of_le (Finset.sum_congr rfl fun l _ => ?_) h
    show floorContact Q (R + i) (R + J + l) =
      floorContact Q (min (R + (i : ℕ)) (R + J + l)) (max (R + (i : ℕ)) (R + J + l))
    rw [min_eq_left (adjacent_lt R i l).le, max_eq_right (adjacent_lt R i l).le]
  · have h := sum_floorContact_injective_le (q := fun i : Fin J => R + (i : ℕ))
      (fun i₁ i₂ h => by
        have h' : R + (i₁ : ℕ) = R + (i₂ : ℕ) := h
        exact Fin.ext (by omega)) Q (R + J + (l : ℕ))
    refine le_of_eq_of_le (Finset.sum_congr rfl fun i _ => ?_) h
    show floorContact Q (R + i) (R + J + l) =
      floorContact Q (min (R + J + (l : ℕ)) (R + i)) (max (R + J + (l : ℕ)) (R + i))
    rw [min_eq_right (adjacent_lt R i l).le, max_eq_left (adjacent_lt R i l).le]

/-- **The coupling of two adjacent windows is bounded at every block size.** -/
theorem dotProduct_adjacentCoupling_mulVec_sq_le (Q R J j : ℕ) (m : Fin J → ℝ)
    (e : Fin j → ℝ) :
    (m ⬝ᵥ (adjacentCoupling Q R J j *ᵥ e)) ^ 2 ≤
      (24 + 2 * primeContactSum Q) ^ 2 * ((m ⬝ᵥ m) * (e ⬝ᵥ e)) := by
  have hsplit : m ⬝ᵥ (adjacentCoupling Q R J j *ᵥ e) =
      -(m ⬝ᵥ (adjacentJet R J j *ᵥ e)) + -(m ⬝ᵥ (adjacentContact Q R J j *ᵥ e)) := by
    rw [adjacentCoupling_eq, Matrix.sub_mulVec, Matrix.neg_mulVec, dotProduct_sub,
      dotProduct_neg]
    ring
  rw [hsplit]
  exact sq_add_le_of_sq_le (by norm_num) (by linarith [primeContactSum_nonneg Q])
    (mul_nonneg (dotProduct_self_star_nonneg (v := m)) (dotProduct_self_star_nonneg (v := e)))
    (by rw [neg_sq]; exact dotProduct_adjacentJet_mulVec_sq_le R J j m e)
    (by rw [neg_sq]; exact dotProduct_adjacentContact_mulVec_sq_le Q R J j m e)

theorem primeContactSum_two : primeContactSum 2 = Real.log 2 := by
  rw [primeContactSum, Finset.Icc_self, Finset.sum_singleton]
  exact_mod_cast ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two

/-- With the prime two alone the coupling of two adjacent windows has norm at most `26`. -/
theorem dotProduct_adjacentCoupling_two_mulVec_sq_le (R J j : ℕ) (m : Fin J → ℝ)
    (e : Fin j → ℝ) :
    (m ⬝ᵥ (adjacentCoupling 2 R J j *ᵥ e)) ^ 2 ≤ 26 ^ 2 * ((m ⬝ᵥ m) * (e ⬝ᵥ e)) := by
  have h := dotProduct_adjacentCoupling_mulVec_sq_le 2 R J j m e
  rw [primeContactSum_two] at h
  have hP : 0 ≤ (m ⬝ᵥ m) * (e ⬝ᵥ e) :=
    mul_nonneg (dotProduct_self_star_nonneg (v := m)) (dotProduct_self_star_nonneg (v := e))
  have hlog0 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hsq : (24 + 2 * Real.log 2) ^ 2 ≤ (26 : ℝ) ^ 2 :=
    pow_le_pow_left₀ (by positivity) (by linarith [Real.log_two_lt_d9]) 2
  exact h.trans (mul_le_mul_of_nonneg_right hsq hP)

/-! ### The attraction of a thin end -/

/-- **The dual overlap law for a thin end.** If `K j ≤ R + J` with `K ≥ 16`, the window
`(R, R + J + j]` and its first part dressed by the attraction of the end hold the same number of
bound states. -/
theorem hermNegIndex_neutralWindow_eq_of_thin_tail {Q R J j K : ℕ} (hK : 16 ≤ K)
    (hj : K * j ≤ R + J) :
    hermNegIndex ((neutralWindow Q R (J + j)).map (↑) :
        Matrix (Fin (J + j)) (Fin (J + j)) ℂ) =
      hermNegIndex ((neutralWindow Q R J - adjacentCoupling Q R J j *
        (neutralWindow Q (R + J) j)⁻¹ * (adjacentCoupling Q R J j)ᵀ).map (↑) :
          Matrix (Fin J) (Fin J) ℂ) := by
  rw [← hermNegIndex_map_submatrix _ finSumFinEquiv, neutralWindow_submatrix_finSumFinEquiv]
  exact hermNegIndex_fromBlocks_eq_of_corner_floor (neutralWindow_symm Q R J) _
    (neutralWindow_symm Q (R + J) j) (log_sub_two_pos hK) (neutralWindow_form_ge_of_thin hK hj)

/-- **The attraction of a thin end vanishes logarithmically**: if `K j ≤ R + J` with `K ≥ 16`,
the attraction of the end `(R + J, R + J + j]` on the window `(R, R + J]` is at most
`676/(log K − 2)`. -/
theorem thin_attraction_form_le {R J j K : ℕ} (hK : 16 ≤ K) (hj : K * j ≤ R + J)
    (m : Fin J → ℝ) :
    m ⬝ᵥ ((adjacentCoupling 2 R J j * (neutralWindow 2 (R + J) j)⁻¹ *
        (adjacentCoupling 2 R J j)ᵀ) *ᵥ m) ≤ 676 / (Real.log K - 2) * (m ⬝ᵥ m) := by
  have hpos := log_sub_two_pos hK
  have hform := dotProduct_transpose_mul_mul_mulVec (adjacentCoupling 2 R J j)ᵀ
    (neutralWindow 2 (R + J) j)⁻¹ m
  rw [Matrix.transpose_transpose] at hform
  rw [hform]
  have h1 := inv_form_le_of_form_floor hpos (neutralWindow_form_ge_of_thin (Q := 2) hK hj)
    ((adjacentCoupling 2 R J j)ᵀ *ᵥ m)
  have h2 := transpose_mulVec_sq_le (dotProduct_adjacentCoupling_two_mulVec_sq_le R J j) m
  have h3 : 1 / (Real.log K - 2) * (((adjacentCoupling 2 R J j)ᵀ *ᵥ m) ⬝ᵥ
      ((adjacentCoupling 2 R J j)ᵀ *ᵥ m)) ≤ 1 / (Real.log K - 2) * (26 ^ 2 * (m ⬝ᵥ m)) :=
    mul_le_mul_of_nonneg_left h2 (div_nonneg zero_le_one hpos.le)
  have h4 : 1 / (Real.log K - 2) * (26 ^ 2 * (m ⬝ᵥ m)) =
      676 / (Real.log K - 2) * (m ⬝ᵥ m) := by ring
  linarith

/-! ### A floor extends the bound range -/

/-- **A thin end costs little of a floor.** If `(R, R + J]` has floor `c` on the kernel of `ψ`
and `log K ≥ c − ε + B²/ε + 2` with `B = 24 + 2 Σ_{k ≤ Q} Λ(k)`, `ε > 0`, the window
`(R, R + J + j]` with `K j ≤ R + J` has floor `c − ε` on the vectors whose first part is in the
kernel of `ψ`. -/
theorem neutralWindow_form_ge_of_thin_tail {Q R J j K : ℕ} (hK : 16 ≤ K) (hj : K * j ≤ R + J)
    {ψ : Fin J → ℝ} {c ε : ℝ} (hε : 0 < ε)
    (hfloor : ∀ m : Fin J → ℝ, ψ ⬝ᵥ m = 0 →
      c * (m ⬝ᵥ m) ≤ m ⬝ᵥ (neutralWindow Q R J *ᵥ m))
    (hs : c - ε + (24 + 2 * primeContactSum Q) ^ 2 / ε + 2 ≤ Real.log K)
    {y : Fin (J + j) → ℝ} (hy : headFunctional ψ j ⬝ᵥ y = 0) :
    (c - ε) * (y ⬝ᵥ y) ≤ y ⬝ᵥ (neutralWindow Q R (J + j) *ᵥ y) := by
  rw [neutralWindow_form_eq_head_tail, dotProduct_self_eq_head_add_tail]
  exact fromBlocks_form_ge_of_stiff_corner hε hfloor (adjacentCoupling Q R J j)
    (s := Real.log K - 2) (neutralWindow_form_ge_of_thin hK hj)
    (dotProduct_adjacentCoupling_mulVec_sq_le Q R J j) (by linarith)
    ((headFunctional_dotProduct ψ y).symm.trans hy) (tailPart y)

/-- **A floor extends the bound range.** If the window `(R, R + J]` holds one bound state with
floor `c` and `log K ≥ c − ε + B²/ε + 2` with `B = 24 + 2 Σ_{k ≤ Q} Λ(k)`, `0 < ε < c`, then
every window `(R, R + J + j]` with `K j ≤ R + J` holds one bound state with floor `c − ε`. -/
theorem exists_oneBoundState_neutralWindow_of_thin_tail {Q R J j K : ℕ} (hR : 1 ≤ R)
    (hRJ : R ≤ J + j) (hK : 16 ≤ K) (hj : K * j ≤ R + J) {ψ : Fin J → ℝ} {ν c ε : ℝ}
    (h : OneBoundState (neutralWindow Q R J) ψ ν c) (hε : 0 < ε) (hεc : ε < c)
    (hs : c - ε + (24 + 2 * primeContactSum Q) ^ 2 / ε + 2 ≤ Real.log K) :
    ∃ ψ' : Fin (J + j) → ℝ, ∃ ν' : ℝ, (∀ i, 0 < ψ' i) ∧
      OneBoundState (neutralWindow Q R (J + j)) ψ' ν' (c - ε) := by
  have hJj : 1 ≤ J + j := by omega
  obtain ⟨φ₀, hφ₀, lam, heig⟩ := exists_groundVector_neutralWindow Q R hJj
  have hlam : lam < 0 := eigenvalue_neg_of_pos_eigenvector Q hR hRJ hφ₀ heig
  haveI : Nonempty (Fin (J + j)) := ⟨⟨0, by omega⟩⟩
  obtain ⟨φ, hφ, hO⟩ := exists_oneBoundState_of_pos_eigenvector_of_hyperplane
    (neutralWindow_symm Q R (J + j)) hφ₀ hlam heig (sub_pos.mpr hεc)
    (ℓ := headFunctional ψ j)
    (fun y hy => neutralWindow_form_ge_of_thin_tail hK hj hε h.floor hs hy)
  exact ⟨φ, -lam, hφ, hO⟩

/-- **Up to ratio three the constants are absolute**: if `(R, R + J]` holds one bound state with
floor `c` and `log K ≥ c − ε + 676/ε + 2`, `0 < ε < c`, every window `(R, R + J + j]` with
`K j ≤ R + J` and `J + j ≤ 2R` holds one bound state with floor `c − ε`. -/
theorem exists_oneBoundState_neutralWindow_of_thin_tail_of_le_two_mul {Q R J j K : ℕ}
    (hQ : 2 ≤ Q) (hR : 1 ≤ R) (hRJ : R ≤ J + j) (h3 : J + j ≤ 2 * R) (hK : 16 ≤ K)
    (hj : K * j ≤ R + J) {ψ : Fin J → ℝ} {ν c ε : ℝ}
    (h : OneBoundState (neutralWindow Q R J) ψ ν c) (hε : 0 < ε) (hεc : ε < c)
    (hs : c - ε + 676 / ε + 2 ≤ Real.log K) :
    ∃ ψ' : Fin (J + j) → ℝ, ∃ ν' : ℝ, (∀ i, 0 < ψ' i) ∧
      OneBoundState (neutralWindow Q R (J + j)) ψ' ν' (c - ε) := by
  rw [neutralWindow_eq_two_of_le_two_mul hQ h3]
  rw [neutralWindow_eq_two_of_le_two_mul hQ (by omega : J ≤ 2 * R)] at h
  refine exists_oneBoundState_neutralWindow_of_thin_tail hR hRJ hK hj h hε hεc (le_trans ?_ hs)
  have hsq : (24 + 2 * primeContactSum 2) ^ 2 ≤ (676 : ℝ) := by
    rw [primeContactSum_two]
    calc (24 + 2 * Real.log 2) ^ 2 ≤ (26 : ℝ) ^ 2 :=
          pow_le_pow_left₀ (by positivity) (by linarith [Real.log_two_lt_d9]) 2
      _ = 676 := by norm_num
  have hdiv : (24 + 2 * primeContactSum 2) ^ 2 / ε ≤ 676 / ε := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right hsq (inv_nonneg.mpr hε.le)
  linarith

/-- **The certified range is not sharp.** Every window `(R, R + J + j]` with `R ≤ J`,
`50 J ≤ 53 R` and `K j ≤ R + J`, `log K ≥ 6760003`, holds one bound state with floor `1/10000`,
at every block size. -/
theorem exists_oneBoundState_neutralWindow_beyond_certified {Q R J j K : ℕ} (hQ : 2 ≤ Q)
    (hR : 1 ≤ R) (hRJ : R ≤ J) (hJ : 50 * J ≤ 53 * R) (hK : (6760003 : ℝ) ≤ Real.log K)
    (hj : K * j ≤ R + J) :
    ∃ ψ' : Fin (J + j) → ℝ, ∃ ν' : ℝ, (∀ i, 0 < ψ' i) ∧
      OneBoundState (neutralWindow Q R (J + j)) ψ' ν' (1 / 10000) := by
  obtain ⟨ψ, ν, -, h⟩ := exists_oneBoundState_neutralWindow hR hRJ hJ hQ
  have hK16 : 16 ≤ K := by
    by_contra hlt
    rw [not_le] at hlt
    rcases Nat.eq_zero_or_pos K with rfl | hpos
    · rw [Nat.cast_zero, Real.log_zero] at hK
      norm_num at hK
    · have hK0 : (0 : ℝ) < K := by exact_mod_cast hpos
      have hKle : (K : ℝ) ≤ 16 := by exact_mod_cast hlt.le
      have := Real.log_le_sub_one_of_pos hK0
      linarith
  have h16j : 16 * j ≤ K * j := Nat.mul_le_mul_right j hK16
  have hs : (1 / 5000 : ℝ) - 1 / 10000 + 676 / (1 / 10000) + 2 ≤ Real.log K :=
    le_trans (by norm_num) hK
  obtain ⟨ψ', ν', hψ', h'⟩ := exists_oneBoundState_neutralWindow_of_thin_tail_of_le_two_mul hQ hR
    (by omega : R ≤ J + j) (by omega : J + j ≤ 2 * R) hK16 hj h (ε := 1 / 10000)
    (by norm_num) (by norm_num) hs
  have h2 : (1 / 5000 : ℝ) - 1 / 10000 = 1 / 10000 := by norm_num
  rw [h2] at h'
  exact ⟨ψ', ν', hψ', h'⟩

/-- Beyond the certified range the windows of the previous theorem hold exactly one bound
state. -/
theorem hermNegIndex_neutralWindow_eq_one_beyond_certified {Q R J j K : ℕ} (hQ : 2 ≤ Q)
    (hR : 1 ≤ R) (hRJ : R ≤ J) (hJ : 50 * J ≤ 53 * R) (hK : (6760003 : ℝ) ≤ Real.log K)
    (hj : K * j ≤ R + J) :
    hermNegIndex ((neutralWindow Q R (J + j)).map (↑) :
      Matrix (Fin (J + j)) (Fin (J + j)) ℂ) = 1 := by
  obtain ⟨ψ', ν', -, h⟩ :=
    exists_oneBoundState_neutralWindow_beyond_certified hQ hR hRJ hJ hK hj
  exact h.hermNegIndex_eq_one

end GaloisForLFunctions.GreenCalculusOfThePrimeFreeWindow
