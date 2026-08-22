import GaloisForLFunctions.HTGeometry.SteinbergTWTFinFourComplete
import GaloisForLFunctions.HTGeometry.SteinbergFinFourUpperKernel

/-!
# The rank-four TWT Weyl-kernel reduction

This formalizes the matrix core of Milnor's proof of Theorem 9.12.  A Weyl word has an
exact signed-monomial matrix image.  If a `TWT` product lies in the kernel, that monomial
matrix is upper unipotent; its permutation and all of its scales are then forced to be trivial.
Thus the Weyl factor itself belongs to `K₂`.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open Matrix

variable {F : Type*} [Field F] {n : Type*} [DecidableEq n] [Fintype n]

/-- The matrix of a signed permutation: column `s` is sent to the scalar `c s` in row `σ s`. -/
def signedMonomialMatrix (σ : Equiv.Perm n) (c : n → Fˣ) : Matrix n n F :=
  fun r s => if r = σ s then c s else 0

omit [Fintype n] in
set_option linter.unusedSimpArgs false in
/-- The matrix of one Steinberg Weyl generator is its signed transposition. -/
theorem weylMatrix_eq_signedMonomial {i j : n} (hij : i ≠ j) (u : Fˣ) :
    weylMatrix i j u = signedMonomialMatrix (Equiv.swap i j)
      (steinbergWeylRootScale (i := i) (j := j) u) := by
  ext r s
  by_cases hsi : s = i
  · subst s
    by_cases hrj : r = j
    · subst r
      simp [weylMatrix, signedMonomialMatrix, steinbergWeylRootScale, hij, Ne.symm hij]
    · by_cases hri : r = i
      · subst r
        simp [weylMatrix, signedMonomialMatrix, hij, Ne.symm hij]
      · simp [weylMatrix, signedMonomialMatrix, hij, Ne.symm hij, hrj, hri, Ne.symm hrj, Ne.symm hri]
  · by_cases hsj : s = j
    · subst s
      by_cases hri : r = i
      · subst r
        simp [weylMatrix, signedMonomialMatrix, steinbergWeylRootScale, hij, Ne.symm hij]
      · by_cases hrj : r = j
        · subst r
          simp [weylMatrix, signedMonomialMatrix, hij, Ne.symm hij]
        · simp [weylMatrix, signedMonomialMatrix, hij, Ne.symm hij, hri, hrj, Ne.symm hri, Ne.symm hrj]
    · by_cases hrs : r = s
      · subst r
        have hswap : Equiv.swap i j s = s :=
          Equiv.swap_apply_of_ne_of_ne hsi hsj
        simp [weylMatrix, signedMonomialMatrix, steinbergWeylRootScale, hij, Ne.symm hij, hsi, hsj,
          Ne.symm hsi, Ne.symm hsj, hswap]
      · by_cases hri : r = i
        · subst r
          have hswap : Equiv.swap i j s = s :=
            Equiv.swap_apply_of_ne_of_ne hsi hsj
          simp [weylMatrix, signedMonomialMatrix, hij, Ne.symm hij, hsi, hsj, Ne.symm hsi, Ne.symm hsj, hrs,
            hswap]
        · by_cases hrj : r = j
          · subst r
            have hswap : Equiv.swap i j s = s :=
              Equiv.swap_apply_of_ne_of_ne hsi hsj
            simp [weylMatrix, signedMonomialMatrix, hij, Ne.symm hij, hsi, hsj, Ne.symm hsi, Ne.symm hsj, hrs,
              hswap]
          · have hswap : Equiv.swap i j s = s :=
              Equiv.swap_apply_of_ne_of_ne hsi hsj
            simp [weylMatrix, signedMonomialMatrix, hij, Ne.symm hij, hsi, hsj, Ne.symm hsi, Ne.symm hsj,
              hrs, hri, hrj, hswap]

/-- Multiplication of signed monomial matrices composes the signed permutations. -/
theorem signedMonomialMatrix_mul (σ τ : Equiv.Perm n) (c d : n → Fˣ) :
    signedMonomialMatrix σ c * signedMonomialMatrix τ d
      = signedMonomialMatrix (τ.trans σ) (fun p => c (τ p) * d p) := by
  ext r s
  simp [signedMonomialMatrix, Matrix.mul_apply]

/-- Exact matrix normal form of an arbitrary signed Weyl word. -/
theorem steinbergWeylWord_matrix (w : SteinbergWeylWord F n) :
    ((steinbergToGL w.eval : (Matrix n n F)ˣ) : Matrix n n F)
      = signedMonomialMatrix w.perm w.scale := by
  induction w with
  | one =>
      ext r s
      simp [SteinbergWeylWord.eval, SteinbergWeylWord.perm, SteinbergWeylWord.scale,
        signedMonomialMatrix, Matrix.one_apply]
  | snoc w i j hij u ih =>
      rw [SteinbergWeylWord.eval, map_mul, Units.val_mul, ih, steinbergToGL_weyl,
        weylMatrix_eq_signedMonomial hij u, signedMonomialMatrix_mul]
      rfl

/-- A matrix with no entries below its diagonal and with all diagonal entries equal to one. -/
def IsUpperUnipotent {n : Type*} [LinearOrder n] (A : Matrix n n F) : Prop :=
  (∀ r s, s < r → A r s = 0) ∧ ∀ r, A r r = 1

/-- A positive-root transvection is upper unipotent. -/
theorem transvection_isUpperUnipotent {n : Type*} [DecidableEq n] [LinearOrder n]
    {i j : n} (hij : i < j) (a : F) :
    IsUpperUnipotent (Matrix.transvection i j a) := by
  constructor
  · intro r s hsr
    have hrs : r ≠ s := ne_of_gt hsr
    have hnot : ¬(i = r ∧ j = s) := by
      rintro ⟨rfl, rfl⟩
      exact (not_lt_of_ge (le_of_lt hsr)) hij
    simp [Matrix.transvection, hrs, hnot]
  · intro r
    have hnot : ¬(i = r ∧ j = r) := by
      rintro ⟨rfl, rfl⟩
      exact hij.false
    simp [Matrix.transvection, hnot]

/-- Upper-unipotent matrices are closed under multiplication. -/
theorem IsUpperUnipotent.mul {n : Type*} [DecidableEq n] [Fintype n] [LinearOrder n]
    {A B : Matrix n n F} (hA : IsUpperUnipotent A) (hB : IsUpperUnipotent B) :
    IsUpperUnipotent (A * B) := by
  constructor
  · intro r s hsr
    rw [Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro x _
    rcases lt_or_ge x r with hxr | hrx
    · rw [hA.1 r x hxr, zero_mul]
    · rw [hB.1 x s (lt_of_lt_of_le hsr hrx), mul_zero]
  · intro r
    rw [Matrix.mul_apply, Finset.sum_eq_single r]
    · rw [hA.2 r, hB.2 r]
      norm_num
    · intro x _ hxr
      rcases lt_or_gt_of_ne hxr with hxr' | hrx
      · rw [hA.1 r x hxr', zero_mul]
      · rw [hB.1 x r hrx, mul_zero]
    · simp

/-- Every rank-four upper collector has upper-unipotent matrix image. -/
theorem fin4_upper_tetrahedron_matrix_isUpper (a b c d e f : F) :
    IsUpperUnipotent
      ((steinbergToGL
        (steinbergUpperTetrahedron (by decide : (0 : Fin 4) ≠ 1)
          (by decide : (1 : Fin 4) ≠ 2) (by decide : (0 : Fin 4) ≠ 2)
          (by decide : (0 : Fin 4) ≠ 3) (by decide : (1 : Fin 4) ≠ 3)
          (by decide : (2 : Fin 4) ≠ 3) a b c d e f) : (Matrix (Fin 4) (Fin 4) F)ˣ)
        : Matrix (Fin 4) (Fin 4) F) := by
  have hupper : IsUpperUnipotent
      (Matrix.transvection (0 : Fin 4) 1 a * Matrix.transvection 0 2 b
        * Matrix.transvection 1 2 c
        * (Matrix.transvection 0 3 d * Matrix.transvection 1 3 e
          * Matrix.transvection 2 3 f)) := by
    apply IsUpperUnipotent.mul
    · apply IsUpperUnipotent.mul
      · apply IsUpperUnipotent.mul
        · exact transvection_isUpperUnipotent (by decide) a
        · exact transvection_isUpperUnipotent (by decide) b
      · exact transvection_isUpperUnipotent (by decide) c
    · apply IsUpperUnipotent.mul
      · apply IsUpperUnipotent.mul
        · exact transvection_isUpperUnipotent (by decide) d
        · exact transvection_isUpperUnipotent (by decide) e
      · exact transvection_isUpperUnipotent (by decide) f
  simpa only [steinbergUpperTetrahedron, steinbergUpperTriangle, steinbergUpperColumn,
    map_mul, steinbergToGL_x, Units.val_mul, elemUnit_val] using hupper

/-- The signed permutation behind an upper monomial matrix is pointwise non-increasing. -/
theorem signedMonomial_perm_le_of_upper {n : Type*} [DecidableEq n] [LinearOrder n]
    (σ : Equiv.Perm n) (c : n → Fˣ) (h : IsUpperUnipotent (signedMonomialMatrix σ c)) (p : n) :
    σ p ≤ p := by
  by_contra hnot
  have hlt : p < σ p := lt_of_not_ge hnot
  have hzero := h.1 (σ p) p hlt
  simp [signedMonomialMatrix] at hzero

/-- A non-increasing signed permutation of the four ordered indices is the identity. -/
theorem fin4_perm_eq_id_of_le (σ : Equiv.Perm (Fin 4)) (hσ : ∀ p, σ p ≤ p) :
    σ = Equiv.refl _ := by
  have h0 : σ 0 = 0 := by
    have hle := hσ 0
    apply Fin.ext
    omega
  have h1ne0 : σ 1 ≠ 0 := by
    intro h
    exact (by decide : (1 : Fin 4) ≠ 0) (σ.injective (h.trans h0.symm))
  have h1 : σ 1 = 1 := by
    have hle := hσ 1
    apply Fin.ext
    omega
  have h2ne0 : σ 2 ≠ 0 := by
    intro h
    exact (by decide : (2 : Fin 4) ≠ 0) (σ.injective (h.trans h0.symm))
  have h2ne1 : σ 2 ≠ 1 := by
    intro h
    exact (by decide : (2 : Fin 4) ≠ 1) (σ.injective (h.trans h1.symm))
  have h2 : σ 2 = 2 := by
    have hle := hσ 2
    apply Fin.ext
    omega
  have h3ne0 : σ 3 ≠ 0 := by
    intro h
    exact (by decide : (3 : Fin 4) ≠ 0) (σ.injective (h.trans h0.symm))
  have h3ne1 : σ 3 ≠ 1 := by
    intro h
    exact (by decide : (3 : Fin 4) ≠ 1) (σ.injective (h.trans h1.symm))
  have h3ne2 : σ 3 ≠ 2 := by
    intro h
    exact (by decide : (3 : Fin 4) ≠ 2) (σ.injective (h.trans h2.symm))
  have h3 : σ 3 = 3 := by
    have hle := hσ 3
    apply Fin.ext
    omega
  apply Equiv.ext
  intro p
  fin_cases p
  · simpa using h0
  · simpa using h1
  · simpa using h2
  · simpa using h3

/-- A rank-four upper-unipotent signed monomial matrix is the identity matrix. -/
theorem signedMonomial_fin4_eq_one_of_upper (σ : Equiv.Perm (Fin 4)) (c : Fin 4 → Fˣ)
    (h : IsUpperUnipotent (signedMonomialMatrix σ c)) :
    signedMonomialMatrix σ c = 1 := by
  have hperm : σ = Equiv.refl _ :=
    fin4_perm_eq_id_of_le σ (signedMonomial_perm_le_of_upper σ c h)
  have hscale : ∀ p, c p = 1 := by
    intro p
    apply Units.ext
    simpa [signedMonomialMatrix, hperm] using h.2 p
  ext r s
  simp [signedMonomialMatrix, Matrix.one_apply, hperm, hscale]

/-- A signed monomial matrix equal to the identity has trivial permutation and all scales one. -/
theorem signedMonomial_fin4_data_eq_one (σ : Equiv.Perm (Fin 4)) (c : Fin 4 → Fˣ)
    (h : signedMonomialMatrix σ c = 1) :
    σ = Equiv.refl _ ∧ c = fun _ => 1 := by
  have hupper : IsUpperUnipotent (signedMonomialMatrix σ c) := by
    rw [h]
    constructor
    · intro r s hsr
      rw [Matrix.one_apply, if_neg (Ne.symm (ne_of_lt hsr))]
    · intro r
      rw [Matrix.one_apply, if_pos rfl]
  have hperm : σ = Equiv.refl _ :=
    fin4_perm_eq_id_of_le σ (signedMonomial_perm_le_of_upper σ c hupper)
  refine ⟨hperm, ?_⟩
  funext p
  apply Units.ext
  have hdiag := congrFun (congrFun h p) p
  simpa [signedMonomialMatrix, hperm] using hdiag

/-- **Milnor §9.12, rank-four Weyl-kernel reduction.** If a `TWT` product is in `K₂`, then
its signed Weyl factor is in `K₂`. -/
theorem fin4_weylWord_mem_KTwo_of_TWT_mem_KTwo {t₁ t₂ : SteinbergGroup F (Fin 4)}
    (ht₁ : t₁ ∈ upperSteinbergSubgroup (F := F) (Fin 4))
    (ht₂ : t₂ ∈ upperSteinbergSubgroup (F := F) (Fin 4))
    (word : SteinbergWeylWord F (Fin 4))
    (hkernel : t₁ * word.eval * t₂ ∈ KTwo F (Fin 4)) :
    word.eval ∈ KTwo F (Fin 4) := by
  have hunit : steinbergToGL word.eval
      = steinbergToGL (t₁⁻¹ * t₂⁻¹) := by
    rw [mem_KTwo_iff, map_mul, map_mul] at hkernel
    calc
      steinbergToGL word.eval
          = (steinbergToGL t₁)⁻¹
            * (steinbergToGL t₁ * steinbergToGL word.eval * steinbergToGL t₂)
            * (steinbergToGL t₂)⁻¹ := by group
      _ = (steinbergToGL t₁)⁻¹ * (1 : (Matrix (Fin 4) (Fin 4) F)ˣ)
            * (steinbergToGL t₂)⁻¹ := by rw [hkernel]
      _ = steinbergToGL (t₁⁻¹ * t₂⁻¹) := by
        rw [map_mul, map_inv, map_inv]
        group
  have hu : t₁⁻¹ * t₂⁻¹ ∈ upperSteinbergSubgroup (F := F) (Fin 4) :=
    (upperSteinbergSubgroup (F := F) (Fin 4)).mul_mem
      ((upperSteinbergSubgroup (F := F) (Fin 4)).inv_mem ht₁)
      ((upperSteinbergSubgroup (F := F) (Fin 4)).inv_mem ht₂)
  rw [upperSteinbergSubgroup_fin4_eq_tetrahedron] at hu
  obtain ⟨a, b, c, d, e, f, hu⟩ := hu
  have hmatrix : ((steinbergToGL word.eval : (Matrix (Fin 4) (Fin 4) F)ˣ)
      : Matrix (Fin 4) (Fin 4) F)
      = ((steinbergToGL
          (steinbergUpperTetrahedron (by decide : (0 : Fin 4) ≠ 1)
            (by decide : (1 : Fin 4) ≠ 2) (by decide : (0 : Fin 4) ≠ 2)
            (by decide : (0 : Fin 4) ≠ 3) (by decide : (1 : Fin 4) ≠ 3)
            (by decide : (2 : Fin 4) ≠ 3) a b c d e f) : (Matrix (Fin 4) (Fin 4) F)ˣ)
          : Matrix (Fin 4) (Fin 4) F) := by
    rw [hunit, hu]
  have hwupper : IsUpperUnipotent
      ((steinbergToGL word.eval : (Matrix (Fin 4) (Fin 4) F)ˣ)
        : Matrix (Fin 4) (Fin 4) F) := by
    rw [hmatrix]
    exact fin4_upper_tetrahedron_matrix_isUpper a b c d e f
  have hmonUpper : IsUpperUnipotent (signedMonomialMatrix word.perm word.scale) := by
    rw [← steinbergWeylWord_matrix word]
    exact hwupper
  rw [mem_KTwo_iff]
  apply Units.ext
  calc
    ((steinbergToGL word.eval : (Matrix (Fin 4) (Fin 4) F)ˣ) : Matrix (Fin 4) (Fin 4) F)
        = signedMonomialMatrix word.perm word.scale := steinbergWeylWord_matrix word
    _ = 1 := signedMonomial_fin4_eq_one_of_upper word.perm word.scale hmonUpper

/-- **Milnor §9.11, rank-four Weyl centrality.** A signed Weyl word in `K₂` acts trivially on
every root generator, hence is central.  Unlike spare-index centrality, this allows a word using
all four indices. -/
theorem fin4_weylWord_mem_center_of_mem_KTwo (word : SteinbergWeylWord F (Fin 4))
    (hkernel : word.eval ∈ KTwo F (Fin 4)) :
    word.eval ∈ Subgroup.center (SteinbergGroup F (Fin 4)) := by
  have hmatrix : signedMonomialMatrix word.perm word.scale = 1 := by
    rw [← steinbergWeylWord_matrix word]
    have hunit : steinbergToGL word.eval = 1 := (mem_KTwo_iff word.eval).1 hkernel
    rw [hunit]
    rfl
  have hdata : word.perm = Equiv.refl _ ∧ word.scale = fun _ => 1 :=
    signedMonomial_fin4_data_eq_one word.perm word.scale hmatrix
  rw [Subgroup.mem_center_iff]
  intro z
  have hgen : (⊤ : Subgroup (SteinbergGroup F (Fin 4)))
      = Subgroup.closure
          (Set.range (PresentedGroup.of : SteinbergGen F (Fin 4) → SteinbergGroup F (Fin 4))) :=
    (PresentedGroup.closure_range_of (steinbergRels F (Fin 4))).symm
  have hclosure : Subgroup.closure
        (Set.range (PresentedGroup.of : SteinbergGen F (Fin 4) → SteinbergGroup F (Fin 4)))
      ≤ Subgroup.centralizer ({word.eval} : Set (SteinbergGroup F (Fin 4))) := by
    refine (Subgroup.closure_le _).2 ?_
    rintro x ⟨g, rfl⟩
    show steinbergX g.hij g.a ∈
      (Subgroup.centralizer ({word.eval} : Set (SteinbergGroup F (Fin 4))) : Set _)
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    rintro y hy
    rw [Set.mem_singleton_iff] at hy
    subst y
    have hspare : ∀ i j : Fin 4, i ≠ j → ∃ m : Fin 4, i ≠ m ∧ j ≠ m := by
      intro i j hij
      obtain ⟨m, him, hjm⟩ := exists_third_index (by decide : Fintype.card (Fin 4) ≥ 3) i j
      exact ⟨m, him.symm, hjm.symm⟩
    have hconj := word.conj_root hspare g.hij g.a
    have hconj' : word.eval * steinbergX g.hij g.a * word.eval⁻¹ = steinbergX g.hij g.a := by
      simpa [hdata.1, hdata.2] using hconj
    calc
      word.eval * steinbergX g.hij g.a
          = (word.eval * steinbergX g.hij g.a * word.eval⁻¹) * word.eval := by group
      _ = steinbergX g.hij g.a * word.eval := by rw [hconj']
  have hcent : (⊤ : Subgroup (SteinbergGroup F (Fin 4)))
      ≤ Subgroup.centralizer ({word.eval} : Set (SteinbergGroup F (Fin 4))) :=
    le_trans (le_of_eq hgen) hclosure
  have hz := hcent (Subgroup.mem_top z)
  rw [Subgroup.mem_centralizer_iff] at hz
  exact (hz word.eval (Set.mem_singleton word.eval)).symm

/-- The entire intersection of the rank-four Weyl subgroup with `K₂` is central. -/
theorem fin4_weylWordSubgroup_mem_center_of_mem_KTwo {w : SteinbergGroup F (Fin 4)}
    (hw : w ∈ steinbergWeylWordSubgroup (F := F) (n := Fin 4))
    (hkernel : w ∈ KTwo F (Fin 4)) :
    w ∈ Subgroup.center (SteinbergGroup F (Fin 4)) := by
  obtain ⟨word, hword⟩ := SteinbergWeylWord.exists_of_mem_subgroup hw
  rw [← hword]
  apply fin4_weylWord_mem_center_of_mem_KTwo word
  rwa [hword]

/-- **Milnor §9.12, completed at rank four.** Every element of the field Steinberg kernel is a
signed Weyl word. -/
theorem fin4_KTwo_le_weylWordSubgroup :
    KTwo F (Fin 4) ≤ steinbergWeylWordSubgroup (F := F) (n := Fin 4) := by
  intro z hz
  have htwt : z ∈ steinbergTWT (F := F) (n := Fin 4) := by
    rw [fin4_steinbergTWT_eq_top]
    exact Subgroup.mem_top z
  obtain ⟨t₁, w, t₂, ht₁, hw, ht₂, hz_eq⟩ := htwt
  obtain ⟨word, hword⟩ := SteinbergWeylWord.exists_of_mem_subgroup hw
  have hproductKernel : t₁ * word.eval * t₂ ∈ KTwo F (Fin 4) := by
    rw [hword, ← hz_eq]
    exact hz
  have hwordKernel : word.eval ∈ KTwo F (Fin 4) :=
    fin4_weylWord_mem_KTwo_of_TWT_mem_KTwo ht₁ ht₂ word hproductKernel
  have hwKernel : w ∈ KTwo F (Fin 4) := by
    rwa [← hword]
  have hwCenter : w ∈ Subgroup.center (SteinbergGroup F (Fin 4)) :=
    fin4_weylWordSubgroup_mem_center_of_mem_KTwo hw hwKernel
  have hcomm : w * t₁ = t₁ * w := (Subgroup.mem_center_iff.1 hwCenter t₁).symm
  have hupper : t₁ * t₂ ∈ upperSteinbergSubgroup (F := F) (Fin 4) :=
    (upperSteinbergSubgroup (F := F) (Fin 4)).mul_mem ht₁ ht₂
  have hfactor : w⁻¹ * z = t₁ * t₂ := by
    rw [hz_eq, ← hcomm]
    group
  have hkernelUpper : t₁ * t₂ ∈ KTwo F (Fin 4) := by
    rw [← hfactor]
    exact (KTwo F (Fin 4)).mul_mem ((KTwo F (Fin 4)).inv_mem hwKernel) hz
  have hinter : t₁ * t₂ ∈ upperSteinbergSubgroup (F := F) (Fin 4) ⊓ KTwo F (Fin 4) :=
    ⟨hupper, hkernelUpper⟩
  have hbot : t₁ * t₂ ∈ (⊥ : Subgroup (SteinbergGroup F (Fin 4))) := by
    rw [← upperSteinbergSubgroup_fin4_inter_KTwo_eq_bot]
    exact hinter
  have hupperOne : t₁ * t₂ = 1 := by
    simpa only [Subgroup.mem_bot] using hbot
  have hz_w : z = w := by
    rw [hz_eq, ← hcomm]
    calc
      w * t₁ * t₂ = w * (t₁ * t₂) := by group
      _ = w := by rw [hupperOne, mul_one]
  rw [hz_w]
  exact hw

/-- **Finite-rank central extension at rank four.** The full `K₂` kernel is central, with no
unstated stable-range hypothesis. -/
theorem fin4_KTwo_mem_center {z : SteinbergGroup F (Fin 4)} (hz : z ∈ KTwo F (Fin 4)) :
    z ∈ Subgroup.center (SteinbergGroup F (Fin 4)) :=
  fin4_weylWordSubgroup_mem_center_of_mem_KTwo (fin4_KTwo_le_weylWordSubgroup hz) hz

end GaloisForLFunctions.HTGeometry
