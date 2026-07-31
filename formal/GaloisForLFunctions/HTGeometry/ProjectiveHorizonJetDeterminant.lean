import GaloisForLFunctions.HTGeometry.ProjectiveHorizonFieldSeparation

/-!
# The jet determinant of a covector span

An observer group `G_t` acts on the homogeneous jets indexed by `t` through the `t`-block of the
inverse matrix.  That block is multiplicative on `G_t`, because a row indexed by `t` has no entries
in the columns outside `t`, and its determinant is one on the transvection generators.  Hence the
determinant of any square array of jets indexed by `t` is `G_t`-invariant.

The array of jets is a matrix of distinct free coordinates, so its determinant is nonzero: an
evaluation sending the array to the identity matrix witnesses this.  These two facts are the
ingredients of the rank-`r` separation of horizon fields.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix

noncomputable section

/-! ## Determinants of generic matrices -/

/-- A square matrix whose entries are pairwise distinct polynomial variables has nonzero
determinant: specialising the variables turns it into the identity matrix. -/
theorem det_map_X_ne_zero {ι σ K : Type*} [Fintype ι] [DecidableEq ι] [Field K]
    (f : ι → ι → σ) (hf : ∀ m c m' c', f m c = f m' c' → m = m' ∧ c = c') :
    (Matrix.of fun m c => (MvPolynomial.X (f m c) : MvPolynomial σ K)).det ≠ 0 := by
  classical
  set g : ι × ι → σ := fun p => f p.1 p.2 with hgdef
  have hginj : Function.Injective g := by
    rintro ⟨m, c⟩ ⟨m', c'⟩ hmc
    obtain ⟨h1, h2⟩ := hf m c m' c' hmc
    simp [h1, h2]
  set φ : σ → K :=
    Function.extend g (fun p : ι × ι => if p.1 = p.2 then (1 : K) else 0) 0 with hφdef
  have hφ : ∀ m c : ι, φ (f m c) = if m = c then 1 else 0 := by
    intro m c
    exact hginj.extend_apply _ _ (m, c)
  intro hzero
  have hmapdet := congrArg (MvPolynomial.eval φ) hzero
  rw [map_zero, RingHom.map_det, RingHom.mapMatrix_apply] at hmapdet
  have hone : (Matrix.of fun m c => (MvPolynomial.X (f m c) : MvPolynomial σ K)).map
      (MvPolynomial.eval φ) = (1 : Matrix ι ι K) := by
    ext m c
    rw [Matrix.map_apply, Matrix.of_apply, MvPolynomial.eval_X, hφ, Matrix.one_apply]
  rw [hone, Matrix.det_one] at hmapdet
  exact one_ne_zero hmapdet

variable {n : Type*} [Fintype n] [DecidableEq n] {K : Type*} [Field K]

/-! ## The block restriction of an observer -/

/-- The `t`-block of a unimodular matrix. -/
def blockRestrict (t : Finset n) (g : SpecialLinearGroup n K) : Matrix ↥t ↥t K :=
  Matrix.of fun m p => (g : Matrix n n K) ↑m ↑p

theorem blockRestrict_one (t : Finset n) :
    blockRestrict t (1 : SpecialLinearGroup n K) = 1 := by
  ext m p
  rw [blockRestrict, Matrix.of_apply, Matrix.SpecialLinearGroup.coe_one]
  rcases eq_or_ne m p with rfl | hmp
  · rw [Matrix.one_apply_eq, Matrix.one_apply_eq]
  · rw [Matrix.one_apply_ne (fun hcon => hmp (Subtype.ext hcon)), Matrix.one_apply_ne hmp]

/-- A row indexed by `t` of an observer of `t` has no entries outside `t`. -/
theorem coe_apply_eq_zero_of_mem_chartSubsetStabilizer {t : Finset n}
    {g : SpecialLinearGroup n K} (hg : g ∈ chartSubsetStabilizer (K := K) (↑t : Set n))
    {m q : n} (hm : m ∈ t) (hq : q ∉ t) :
    (g : Matrix n n K) m q = 0 := by
  have hmq : m ≠ q := fun h => hq (h ▸ hm)
  rw [hg q (by simpa using hq) m, Matrix.one_apply_ne hmq]

theorem blockRestrict_mul {t : Finset n} {g : SpecialLinearGroup n K}
    (hg : g ∈ chartSubsetStabilizer (K := K) (↑t : Set n)) (h : SpecialLinearGroup n K) :
    blockRestrict t (g * h) = blockRestrict t g * blockRestrict t h := by
  ext m p
  have hvanish : ∀ q ∈ (Finset.univ : Finset n), q ∉ t →
      (g : Matrix n n K) ↑m q * (h : Matrix n n K) q ↑p = 0 := by
    intro q _ hq
    rw [coe_apply_eq_zero_of_mem_chartSubsetStabilizer hg m.2 hq, zero_mul]
  rw [blockRestrict, Matrix.of_apply, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply,
    Matrix.mul_apply]
  calc ∑ q : n, (g : Matrix n n K) ↑m q * (h : Matrix n n K) q ↑p
      = ∑ q ∈ t, (g : Matrix n n K) ↑m q * (h : Matrix n n K) q ↑p :=
        (Finset.sum_subset (Finset.subset_univ t) hvanish).symm
    _ = ∑ q : ↥t, (g : Matrix n n K) ↑m ↑q * (h : Matrix n n K) ↑q ↑p :=
        (Finset.sum_coe_sort t _).symm

/-- **Unimodularity of the block.**  The `t`-block of an observer of `t` has determinant one. -/
theorem det_blockRestrict {t : Finset n} {g : SpecialLinearGroup n K}
    (hg : g ∈ chartSubsetStabilizer (K := K) (↑t : Set n)) :
    (blockRestrict t g).det = 1 := by
  rw [← closure_chartSubsetTransvectionSet_eq_chartSubsetStabilizer] at hg
  induction hg using Subgroup.closure_induction with
  | mem u hu =>
      obtain ⟨j, hj, x, hx, c, rfl⟩ := hu
      have hjt : j ∈ t := Finset.mem_coe.1 hj
      by_cases hxt : x ∈ t
      · have hne : (⟨x, hxt⟩ : ↥t) ≠ ⟨j, hjt⟩ := by simpa [Subtype.ext_iff] using hx
        have hblock : blockRestrict t (transvectionSL x j hx c) =
            Matrix.transvection (⟨x, hxt⟩ : ↥t) ⟨j, hjt⟩ c := by
          ext m p
          rw [blockRestrict, Matrix.of_apply, coe_transvectionSL, Matrix.transvection,
            Matrix.transvection, Matrix.add_apply, Matrix.add_apply]
          congr 1
          · rcases eq_or_ne m p with rfl | hmp
            · rw [Matrix.one_apply_eq, Matrix.one_apply_eq]
            · rw [Matrix.one_apply_ne (fun hcon => hmp (Subtype.ext hcon)),
                Matrix.one_apply_ne hmp]
          · rw [Matrix.single_apply, Matrix.single_apply]
            refine if_congr ?_ rfl rfl
            constructor
            · rintro ⟨h1, h2⟩
              exact ⟨Subtype.ext h1, Subtype.ext h2⟩
            · rintro ⟨h1, h2⟩
              exact ⟨congrArg Subtype.val h1, congrArg Subtype.val h2⟩
        rw [hblock, Matrix.det_transvection_of_ne _ _ hne]
      · have hblock : blockRestrict t (transvectionSL x j hx c) = 1 := by
          ext m p
          have hxm : x ≠ (↑m : n) := fun hcon => hxt (hcon ▸ m.2)
          rw [blockRestrict, Matrix.of_apply, coe_transvectionSL, Matrix.transvection,
            Matrix.add_apply, Matrix.single_apply, if_neg (fun h => hxm h.1), add_zero]
          rcases eq_or_ne m p with rfl | hmp
          · rw [Matrix.one_apply_eq, Matrix.one_apply_eq]
          · rw [Matrix.one_apply_ne (fun hcon => hmp (Subtype.ext hcon)),
              Matrix.one_apply_ne hmp]
        rw [hblock, Matrix.det_one]
  | one => rw [blockRestrict_one, Matrix.det_one]
  | mul u v hu _ ihu ihv =>
      have hus : u ∈ chartSubsetStabilizer (K := K) (↑t : Set n) := by
        rwa [closure_chartSubsetTransvectionSet_eq_chartSubsetStabilizer] at hu
      rw [blockRestrict_mul hus, Matrix.det_mul, ihu, ihv, one_mul]
  | inv u hu ihu =>
      have huinv : u⁻¹ ∈ chartSubsetStabilizer (K := K) (↑t : Set n) := by
        rw [← closure_chartSubsetTransvectionSet_eq_chartSubsetStabilizer]
        exact inv_mem hu
      have hprod : blockRestrict t (u⁻¹ * u) = blockRestrict t u⁻¹ * blockRestrict t u :=
        blockRestrict_mul huinv u
      rw [inv_mul_cancel, blockRestrict_one] at hprod
      have hdet := congrArg Matrix.det hprod
      rw [Matrix.det_one, Matrix.det_mul, ihu, mul_one] at hdet
      exact hdet.symm

/-! ## The jet array of a covector span -/

/-- The jet order used by one column of the jet array of `t`. -/
def jetOrder (t : Finset n) (c : ↥t) : ℕ := (Fintype.equivFin ↥t c : ℕ)

omit [Fintype n] [DecidableEq n] in
theorem jetOrder_injective (t : Finset n) : Function.Injective (jetOrder t) :=
  fun _ _ h => (Fintype.equivFin ↥t).injective (Fin.val_injective h)

/-- A square array of homogeneous jets: one row per element of `t` along a chosen row labelling,
one jet order per column. -/
def jetArray (t : Finset n) (ρ : ↥t → n) : Matrix ↥t ↥t (HomogeneousJetField n K) :=
  Matrix.of fun m c => freeCoordinate K (n × ℕ) (ρ m, jetOrder t c)

omit [Fintype n] in
/-- **Nondegeneracy of the jet array.**  Distinct row labels give a nonzero jet determinant. -/
theorem jetArray_det_ne_zero (t : Finset n) {ρ : ↥t → n} (hρ : Function.Injective ρ) :
    (jetArray (K := K) t ρ).det ≠ 0 := by
  have hpoly : (Matrix.of fun m c =>
      (MvPolynomial.X ((ρ m, jetOrder t c) : n × ℕ) : MvPolynomial (n × ℕ) K)).det ≠ 0 := by
    refine det_map_X_ne_zero _ ?_
    intro m c m' c' h
    exact ⟨hρ (congrArg Prod.fst h), jetOrder_injective t (congrArg Prod.snd h)⟩
  intro hzero
  refine hpoly ?_
  have hdet : algebraMap (MvPolynomial (n × ℕ) K) (HomogeneousJetField n K)
      ((Matrix.of fun m c =>
        (MvPolynomial.X ((ρ m, jetOrder t c) : n × ℕ) : MvPolynomial (n × ℕ) K)).det) =
      (jetArray (K := K) t ρ).det := by
    rw [RingHom.map_det, RingHom.mapMatrix_apply]
    rfl
  rw [hzero] at hdet
  exact (map_eq_zero_iff _ (IsFractionRing.injective (MvPolynomial (n × ℕ) K)
    (HomogeneousJetField n K))).1 hdet

end

end GaloisForLFunctions.HTGeometry
