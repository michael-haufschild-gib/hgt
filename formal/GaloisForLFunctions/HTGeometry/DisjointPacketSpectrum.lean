import GaloisForLFunctions.HTGeometry.KroneckerSumSpectrum
import GaloisForLFunctions.HTGeometry.DisconnectedProjectiveGapModuleLaw

/-!
# Spectrum of two non-interacting site packets

Two operators supported on disjoint site packets commute and are
simultaneously diagonalized by the product of their eigenbases, so the spectrum
of their sum is the set of sums of one eigenvalue from each packet.

Reindexing configurations into inside/outside coordinates turns the pair into
the Kronecker sum `B ⊗ I + I ⊗ C`, whose spectrum was computed separately.
-/

open scoped Matrix Kronecker BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

theorem isHermitian_reindex {n m : Type*} (e : n ≃ m)
    {M : Matrix n n ℂ} (hM : M.IsHermitian) :
    (Matrix.reindex e e M).IsHermitian := by
  show (Matrix.reindex e e M)ᴴ = _
  show Matrix.reindex e e Mᴴ = _
  rw [hM]

theorem reindex_scalar {n m : Type*} [Fintype n] [DecidableEq n]
    [Fintype m] [DecidableEq m] (e : n ≃ m) (μ : ℂ) :
    Matrix.reindex e e (Matrix.scalar n μ) = Matrix.scalar m μ := by
  ext x y
  show Matrix.scalar n μ (e.symm x) (e.symm y) = _
  simp only [Matrix.scalar_apply, Matrix.diagonal_apply,
    e.symm.injective.eq_iff]

/-- Relabelling the index type does not change the set of eigenvalues. -/
theorem range_eigenvalues_reindex {n m : Type*} [Fintype n] [DecidableEq n]
    [Fintype m] [DecidableEq m] (e : n ≃ m)
    {M : Matrix n n ℂ} (hM : M.IsHermitian) :
    Set.range (isHermitian_reindex e hM).eigenvalues =
      Set.range hM.eigenvalues := by
  ext μ
  rw [mem_range_hermitianEigenvalues_iff, mem_range_hermitianEigenvalues_iff]
  have hdet : (Matrix.scalar m (μ : ℂ) - Matrix.reindex e e M).det =
      (Matrix.scalar n (μ : ℂ) - M).det := by
    rw [← reindex_scalar e (μ : ℂ)]
    show ((Matrix.scalar n (μ : ℂ) - M).submatrix e.symm e.symm).det = _
    exact Matrix.det_submatrix_equiv_self e.symm _
  rw [hdet]

variable {V : Type*} [Fintype V] [DecidableEq V]
    {A : V → Type*} [∀ v, Fintype (A v)] [∀ v, DecidableEq (A v)]

/-- Split the spectator configurations of a packet along a disjoint second
packet. -/
def outsideSplitEquiv {S T : Finset V} (hdisj : Disjoint S T) :
    OutsideConfiguration A S ≃
      LocalConfiguration A T × OutsideBothConfiguration A S T where
  toFun x :=
    (restrictDisjointLocalConfiguration hdisj x,
      restrictOutsideBothConfiguration S T x)
  invFun p := fun v =>
    if h : v.1 ∈ T then p.1 ⟨v.1, h⟩ else p.2 ⟨v.1, ⟨v.2, h⟩⟩
  left_inv := by
    intro x
    funext v
    by_cases h : v.1 ∈ T
    · simp [restrictDisjointLocalConfiguration, h]
    · simp [restrictOutsideBothConfiguration, h]
  right_inv := by
    intro p
    ext v
    · simp [restrictDisjointLocalConfiguration, v.2]
    · simp [restrictOutsideBothConfiguration, v.2.2]

/-- A packet operator seen inside the spectator sector of a disjoint packet is
literally a Kronecker product with an identity factor. -/
theorem reindex_liftLocalMatrixOutsideDisjoint_eq_kronecker_one
    {S T : Finset V} (hdisj : Disjoint S T)
    (C : Matrix (LocalConfiguration A T) (LocalConfiguration A T) ℂ) :
    Matrix.reindex (outsideSplitEquiv (A := A) hdisj)
        (outsideSplitEquiv (A := A) hdisj)
        (liftLocalMatrixOutsideDisjoint hdisj C) =
      C ⊗ₖ (1 : Matrix (OutsideBothConfiguration A S T)
        (OutsideBothConfiguration A S T) ℂ) := by
  classical
  ext x y
  show liftLocalMatrixOutsideDisjoint hdisj C
      ((outsideSplitEquiv (A := A) hdisj).symm x)
      ((outsideSplitEquiv (A := A) hdisj).symm y) = _
  have hlocal : ∀ p : LocalConfiguration A T ×
      OutsideBothConfiguration A S T,
      restrictDisjointLocalConfiguration hdisj
          ((outsideSplitEquiv (A := A) hdisj).symm p) = p.1 :=
    fun p => congrArg Prod.fst
      ((outsideSplitEquiv (A := A) hdisj).apply_symm_apply p)
  have houtside : ∀ p : LocalConfiguration A T ×
      OutsideBothConfiguration A S T,
      restrictOutsideBothConfiguration S T
          ((outsideSplitEquiv (A := A) hdisj).symm p) = p.2 :=
    fun p => congrArg Prod.snd
      ((outsideSplitEquiv (A := A) hdisj).apply_symm_apply p)
  rw [liftLocalMatrixOutsideDisjoint, hlocal, houtside, hlocal, houtside]
  by_cases h : x.2 = y.2
  · simp [Matrix.kroneckerMap_apply, Matrix.one_apply, h]
  · simp [Matrix.kroneckerMap_apply, h]

/-- **Spectrum of a spectator-sector packet operator.** -/
theorem range_eigenvalues_liftLocalMatrixOutsideDisjoint
    [∀ v, Nonempty (A v)] {S T : Finset V} (hdisj : Disjoint S T)
    {C : Matrix (LocalConfiguration A T) (LocalConfiguration A T) ℂ}
    (hC : C.IsHermitian)
    (hlift : (liftLocalMatrixOutsideDisjoint hdisj C).IsHermitian) :
    Set.range hlift.eigenvalues = Set.range hC.eigenvalues := by
  classical
  have hcard : Fintype.card (OutsideBothConfiguration A S T) ≠ 0 :=
    Fintype.card_ne_zero
  ext μ
  rw [mem_range_hermitianEigenvalues_iff, mem_range_hermitianEigenvalues_iff]
  have hdet :
      (Matrix.scalar (OutsideConfiguration A S) (μ : ℂ) -
          liftLocalMatrixOutsideDisjoint hdisj C).det =
        ((Matrix.scalar (LocalConfiguration A T) (μ : ℂ) - C).det) ^
          Fintype.card (OutsideBothConfiguration A S T) := by
    rw [← Matrix.det_submatrix_equiv_self
      (outsideSplitEquiv (A := A) hdisj).symm
      (Matrix.scalar (OutsideConfiguration A S) (μ : ℂ) -
        liftLocalMatrixOutsideDisjoint hdisj C)]
    show (Matrix.reindex (outsideSplitEquiv (A := A) hdisj)
        (outsideSplitEquiv (A := A) hdisj)
        (Matrix.scalar (OutsideConfiguration A S) (μ : ℂ) -
          liftLocalMatrixOutsideDisjoint hdisj C)).det = _
    have hsub :
        Matrix.reindex (outsideSplitEquiv (A := A) hdisj)
            (outsideSplitEquiv (A := A) hdisj)
            (Matrix.scalar (OutsideConfiguration A S) (μ : ℂ) -
              liftLocalMatrixOutsideDisjoint hdisj C) =
          Matrix.scalar (LocalConfiguration A T ×
              OutsideBothConfiguration A S T) (μ : ℂ) -
            C ⊗ₖ (1 : Matrix (OutsideBothConfiguration A S T)
              (OutsideBothConfiguration A S T) ℂ) := by
      rw [show Matrix.reindex (outsideSplitEquiv (A := A) hdisj)
            (outsideSplitEquiv (A := A) hdisj)
            (Matrix.scalar (OutsideConfiguration A S) (μ : ℂ) -
              liftLocalMatrixOutsideDisjoint hdisj C) =
          Matrix.reindex (outsideSplitEquiv (A := A) hdisj)
              (outsideSplitEquiv (A := A) hdisj)
              (Matrix.scalar (OutsideConfiguration A S) (μ : ℂ)) -
            Matrix.reindex (outsideSplitEquiv (A := A) hdisj)
              (outsideSplitEquiv (A := A) hdisj)
              (liftLocalMatrixOutsideDisjoint hdisj C) from rfl,
        reindex_scalar,
        reindex_liftLocalMatrixOutsideDisjoint_eq_kronecker_one]
    rw [hsub]
    have hscalarKron :
        Matrix.scalar (LocalConfiguration A T ×
            OutsideBothConfiguration A S T) (μ : ℂ) =
          (Matrix.scalar (LocalConfiguration A T) (μ : ℂ)) ⊗ₖ
            (1 : Matrix (OutsideBothConfiguration A S T)
              (OutsideBothConfiguration A S T) ℂ) := by
      ext x y
      by_cases h₂ : x.2 = y.2
      · by_cases h₁ : x.1 = y.1 <;>
          simp [Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.one_apply,
            h₁, h₂, Prod.ext_iff]
      · simp [Matrix.scalar_apply, Matrix.diagonal_apply, h₂, Prod.ext_iff]
    have hsubkron :
        (Matrix.scalar (LocalConfiguration A T) (μ : ℂ) - C) ⊗ₖ
            (1 : Matrix (OutsideBothConfiguration A S T)
              (OutsideBothConfiguration A S T) ℂ) =
          (Matrix.scalar (LocalConfiguration A T) (μ : ℂ)) ⊗ₖ
              (1 : Matrix (OutsideBothConfiguration A S T)
                (OutsideBothConfiguration A S T) ℂ) -
            C ⊗ₖ (1 : Matrix (OutsideBothConfiguration A S T)
              (OutsideBothConfiguration A S T) ℂ) := by
      ext x y
      simp [Matrix.kroneckerMap_apply, Matrix.sub_apply, sub_mul]
    rw [hscalarKron, ← hsubkron, Matrix.det_kronecker,
      Matrix.det_one, one_pow, mul_one]
  rw [hdet, pow_eq_zero_iff hcard]

theorem conjTranspose_liftLocalMatrixOutsideDisjoint {S T : Finset V}
    (hdisj : Disjoint S T)
    (C : Matrix (LocalConfiguration A T) (LocalConfiguration A T) ℂ) :
    (liftLocalMatrixOutsideDisjoint hdisj C)ᴴ =
      liftLocalMatrixOutsideDisjoint hdisj Cᴴ := by
  ext x y
  simp only [Matrix.conjTranspose_apply, liftLocalMatrixOutsideDisjoint]
  by_cases h : restrictOutsideBothConfiguration S T x =
      restrictOutsideBothConfiguration S T y
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg (fun hh => h hh.symm), star_zero]

theorem isHermitian_liftLocalMatrixOutsideDisjoint {S T : Finset V}
    (hdisj : Disjoint S T)
    {C : Matrix (LocalConfiguration A T) (LocalConfiguration A T) ℂ}
    (hC : C.IsHermitian) :
    (liftLocalMatrixOutsideDisjoint hdisj C).IsHermitian := by
  show (liftLocalMatrixOutsideDisjoint hdisj C)ᴴ = _
  rw [conjTranspose_liftLocalMatrixOutsideDisjoint, hC]

theorem range_add_eq_of_range_eq {α β γ : Type*}
    {f : α → ℝ} {g : β → ℝ} {g' : γ → ℝ}
    (h : Set.range g = Set.range g') :
    Set.range (fun p : α × β => f p.1 + g p.2) =
      Set.range (fun p : α × γ => f p.1 + g' p.2) := by
  ext μ
  constructor
  · rintro ⟨p, rfl⟩
    obtain ⟨c, hc⟩ : g p.2 ∈ Set.range g' := by rw [← h]; exact ⟨p.2, rfl⟩
    exact ⟨(p.1, c), by simp [hc]⟩
  · rintro ⟨p, rfl⟩
    obtain ⟨b, hb⟩ : g' p.2 ∈ Set.range g := by rw [h]; exact ⟨p.2, rfl⟩
    exact ⟨(p.1, b), by simp [hb]⟩

/-- **Spectrum of two non-interacting site packets.**  The eigenvalues of a sum
of two operators supported on disjoint packets are exactly the sums of one
eigenvalue from each packet. -/
theorem range_eigenvalues_add_liftLocalMatrix_disjoint
    [∀ v, Nonempty (A v)] {S T : Finset V} (hdisj : Disjoint S T)
    {B : Matrix (LocalConfiguration A S) (LocalConfiguration A S) ℂ}
    {C : Matrix (LocalConfiguration A T) (LocalConfiguration A T) ℂ}
    (hB : B.IsHermitian) (hC : C.IsHermitian)
    (hsum : (liftLocalMatrix S B + liftLocalMatrix T C).IsHermitian) :
    Set.range hsum.eigenvalues =
      Set.range (fun p : LocalConfiguration A S × LocalConfiguration A T =>
        hB.eigenvalues p.1 + hC.eigenvalues p.2) := by
  classical
  set C' := liftLocalMatrixOutsideDisjoint hdisj C with hC'def
  have hC' : C'.IsHermitian := isHermitian_liftLocalMatrixOutsideDisjoint hdisj hC
  have heq :
      Matrix.reindex (configurationSplitEquiv A S)
          (configurationSplitEquiv A S)
          (liftLocalMatrix S B + liftLocalMatrix T C) =
        kroneckerSum B C' := by
    have hadd :
        Matrix.reindex (configurationSplitEquiv A S)
            (configurationSplitEquiv A S)
            (liftLocalMatrix S B + liftLocalMatrix T C) =
          Matrix.reindex (configurationSplitEquiv A S)
              (configurationSplitEquiv A S) (liftLocalMatrix S B) +
            Matrix.reindex (configurationSplitEquiv A S)
              (configurationSplitEquiv A S) (liftLocalMatrix T C) := rfl
    rw [hadd, reindex_liftLocalMatrix_eq_kronecker_one,
      reindex_liftLocalMatrix_disjoint_eq_one_kronecker hdisj]
    rfl
  have hkron : (kroneckerSum B C').IsHermitian :=
    isHermitian_kroneckerSum hB hC'
  have heigen :
      (isHermitian_reindex (configurationSplitEquiv A S) hsum).eigenvalues =
        hkron.eigenvalues := by
    apply (Matrix.IsHermitian.eigenvalues_eq_eigenvalues_iff
      (isHermitian_reindex (configurationSplitEquiv A S) hsum) hkron).2
    rw [heq]
  calc
    Set.range hsum.eigenvalues
        = Set.range (isHermitian_reindex
            (configurationSplitEquiv A S) hsum).eigenvalues :=
      (range_eigenvalues_reindex (configurationSplitEquiv A S) hsum).symm
    _ = Set.range hkron.eigenvalues := by rw [heigen]
    _ = Set.range (fun p : LocalConfiguration A S ×
          OutsideConfiguration A S =>
        hB.eigenvalues p.1 + hC'.eigenvalues p.2) :=
      range_eigenvalues_kroneckerSum hB hC'
    _ = _ :=
      range_add_eq_of_range_eq
        (range_eigenvalues_liftLocalMatrixOutsideDisjoint hdisj hC hC')

omit [Fintype V] [∀ v, Fintype (A v)] [∀ v, DecidableEq (A v)] in
theorem restrictLocalConfiguration_glue (S : Finset V)
    (a : LocalConfiguration A S) (z : ∀ v, A v) :
    restrictLocalConfiguration S (glueLocalConfiguration S a z) = a := by
  funext v
  show glueLocalConfiguration S a z v.1 = a v
  rw [glueLocalConfiguration_mem S a z v.2]

/-- Lifting a packet block to the full site product is injective. -/
theorem liftLocalMatrix_injective [∀ v, Nonempty (A v)] (S : Finset V) :
    Function.Injective
      (liftLocalMatrix (A := A) (R := ℂ) S) := by
  classical
  intro B B' hBB'
  ext a b
  let z : ∀ v, A v := fun v => Classical.arbitrary (A v)
  have hout : restrictOutsideConfiguration S (glueLocalConfiguration S a z) =
      restrictOutsideConfiguration S (glueLocalConfiguration S b z) := by
    funext v
    show glueLocalConfiguration S a z v.1 = glueLocalConfiguration S b z v.1
    rw [glueLocalConfiguration_notMem S a z v.2,
      glueLocalConfiguration_notMem S b z v.2]
  have hval := congrFun (congrFun hBB' (glueLocalConfiguration S a z))
    (glueLocalConfiguration S b z)
  rw [liftLocalMatrix, liftLocalMatrix, if_pos hout, if_pos hout,
    restrictLocalConfiguration_glue, restrictLocalConfiguration_glue] at hval
  exact hval

theorem isHermitian_of_isHermitian_liftLocalMatrix [∀ v, Nonempty (A v)]
    (S : Finset V)
    {B : Matrix (LocalConfiguration A S) (LocalConfiguration A S) ℂ}
    (hB : (liftLocalMatrix S B).IsHermitian) : B.IsHermitian := by
  refine liftLocalMatrix_injective S ?_
  rw [← conjTranspose_liftLocalMatrix]
  exact hB

theorem isHermitian_sum_liftLocalMatrix
    {C : Type*} [DecidableEq C]
    (S : C → Finset V)
    (B : ∀ c, Matrix (LocalConfiguration A (S c))
      (LocalConfiguration A (S c)) ℂ)
    (hB : ∀ c, (B c).IsHermitian) (t : Finset C) :
    (∑ c ∈ t, liftLocalMatrix (S c) (B c)).IsHermitian := by
  classical
  induction t using Finset.induction_on with
  | empty =>
      rw [Finset.sum_empty]
      exact Matrix.isHermitian_zero
  | insert c t hc ih =>
      rw [Finset.sum_insert hc]
      exact (isHermitian_liftLocalMatrix (S c) (hB c)).add ih

theorem isSiteSupported_sum_liftLocalMatrix
    {C : Type*} [DecidableEq C]
    (S : C → Finset V)
    (B : ∀ c, Matrix (LocalConfiguration A (S c))
      (LocalConfiguration A (S c)) ℂ)
    (t : Finset C) :
    IsSiteSupported (t.biUnion S) (∑ c ∈ t, liftLocalMatrix (S c) (B c)) := by
  classical
  induction t using Finset.induction_on with
  | empty =>
      rw [Finset.sum_empty, Finset.biUnion_empty]
      exact IsSiteSupported.zero _
  | insert c t hc ih =>
      rw [Finset.sum_insert hc, Finset.biUnion_insert]
      refine IsSiteSupported.add ?_ ?_
      · exact (isSiteSupported_liftLocalMatrix (S c) (B c)).mono
          Finset.subset_union_left
      · exact ih.mono Finset.subset_union_right

/-- **Spectrum of a family of non-interacting site packets.**  The eigenvalues
of a sum of operators supported on pairwise disjoint packets are exactly the
sums of one eigenvalue from each packet. -/
theorem range_eigenvalues_sum_liftLocalMatrix [∀ v, Nonempty (A v)]
    {C : Type*} [DecidableEq C]
    (S : C → Finset V) (hdisj : ∀ c d, c ≠ d → Disjoint (S c) (S d))
    (B : ∀ c, Matrix (LocalConfiguration A (S c))
      (LocalConfiguration A (S c)) ℂ)
    (hB : ∀ c, (B c).IsHermitian) (t : Finset C) :
    Set.range (isHermitian_sum_liftLocalMatrix S B hB t).eigenvalues =
      Set.range (fun x : ∀ c, LocalConfiguration A (S c) =>
        ∑ c ∈ t, (hB c).eigenvalues (x c)) := by
  classical
  induction t using Finset.induction_on with
  | empty =>
      have hzero :
          Set.range (isHermitian_sum_liftLocalMatrix S B hB ∅).eigenvalues =
            ({0} : Set ℝ) := by
        ext μ
        rw [mem_range_hermitianEigenvalues_iff]
        have hsum : (∑ c ∈ (∅ : Finset C), liftLocalMatrix (S c) (B c)) = 0 :=
          Finset.sum_empty
        rw [hsum, sub_zero, scalar_eq_smul_one, Matrix.det_smul, Matrix.det_one,
          mul_one]
        have hcard : Fintype.card (∀ v, A v) ≠ 0 := Fintype.card_ne_zero
        rw [pow_eq_zero_iff hcard]
        simp
      rw [hzero]
      ext μ
      simp
  | insert c₀ t hc₀ ih =>
      have hdisjT : Disjoint (S c₀) (t.biUnion S) := by
        rw [Finset.disjoint_biUnion_right]
        intro d hd
        exact hdisj c₀ d (fun h => hc₀ (h ▸ hd))
      obtain ⟨C', hC'eq⟩ :=
        exists_liftLocalMatrix_of_isSiteSupported
          (isSiteSupported_sum_liftLocalMatrix S B t)
      have hrestHerm : (liftLocalMatrix (t.biUnion S) C').IsHermitian := by
        rw [← hC'eq]
        exact isHermitian_sum_liftLocalMatrix S B hB t
      have hC' : C'.IsHermitian :=
        isHermitian_of_isHermitian_liftLocalMatrix _ hrestHerm
      have hsplit :
          (∑ c ∈ insert c₀ t, liftLocalMatrix (S c) (B c)) =
            liftLocalMatrix (S c₀) (B c₀) +
              liftLocalMatrix (t.biUnion S) C' := by
        rw [Finset.sum_insert hc₀, hC'eq]
      have hpair :
          Set.range (isHermitian_sum_liftLocalMatrix S B hB
              (insert c₀ t)).eigenvalues =
            Set.range (fun p : LocalConfiguration A (S c₀) ×
                LocalConfiguration A (t.biUnion S) =>
              (hB c₀).eigenvalues p.1 + hC'.eigenvalues p.2) := by
        have hHerm2 :
            (liftLocalMatrix (S c₀) (B c₀) +
              liftLocalMatrix (t.biUnion S) C').IsHermitian := by
          rw [← hsplit]
          exact isHermitian_sum_liftLocalMatrix S B hB (insert c₀ t)
        have heigen :
            (isHermitian_sum_liftLocalMatrix S B hB
                (insert c₀ t)).eigenvalues = hHerm2.eigenvalues := by
          apply (Matrix.IsHermitian.eigenvalues_eq_eigenvalues_iff
            (isHermitian_sum_liftLocalMatrix S B hB (insert c₀ t))
            hHerm2).2
          rw [hsplit]
        rw [heigen]
        exact range_eigenvalues_add_liftLocalMatrix_disjoint hdisjT
          (hB c₀) hC' hHerm2
      have hrest :
          Set.range hC'.eigenvalues =
            Set.range (fun x : ∀ c, LocalConfiguration A (S c) =>
              ∑ c ∈ t, (hB c).eigenvalues (x c)) := by
        rw [← ih]
        have heigen :
            (isHermitian_sum_liftLocalMatrix S B hB t).eigenvalues =
              hrestHerm.eigenvalues := by
          apply (Matrix.IsHermitian.eigenvalues_eq_eigenvalues_iff
            (isHermitian_sum_liftLocalMatrix S B hB t) hrestHerm).2
          rw [hC'eq]
        rw [heigen]
        exact (range_eigenvalues_liftLocalMatrix (t.biUnion S) hC').symm
      rw [hpair, range_add_eq_of_range_eq hrest]
      ext μ
      constructor
      · rintro ⟨p, rfl⟩
        refine ⟨Function.update p.2 c₀ p.1, ?_⟩
        dsimp only
        rw [Finset.sum_insert hc₀, Function.update_self]
        congr 1
        refine Finset.sum_congr rfl fun d hd => ?_
        have hne : d ≠ c₀ := by
          rintro rfl
          exact hc₀ hd
        rw [Function.update_of_ne hne]
      · rintro ⟨x, rfl⟩
        refine ⟨(x c₀, x), ?_⟩
        dsimp only
        rw [Finset.sum_insert hc₀]

theorem exists_reference_sum_liftLocalMatrix [∀ v, Nonempty (A v)]
    {C : Type*} [Fintype C] [DecidableEq C]
    (S : C → Finset V) (hdisj : ∀ c d, c ≠ d → Disjoint (S c) (S d))
    (B : ∀ c, Matrix (LocalConfiguration A (S c))
      (LocalConfiguration A (S c)) ℂ)
    (hB : ∀ c, (B c).IsHermitian) (r : ∀ v, A v) :
    ∃ r' : ∀ c, LocalConfiguration A (S c),
      (isHermitian_sum_liftLocalMatrix S B hB Finset.univ).eigenvalues r =
        finiteComponentSumEnergy (fun c => (hB c).eigenvalues) r' := by
  have hmem :
      (isHermitian_sum_liftLocalMatrix S B hB Finset.univ).eigenvalues r ∈
        Set.range (fun x : ∀ c, LocalConfiguration A (S c) =>
          ∑ c ∈ Finset.univ, (hB c).eigenvalues (x c)) := by
    rw [← range_eigenvalues_sum_liftLocalMatrix S hdisj B hB Finset.univ]
    exact ⟨r, rfl⟩
  obtain ⟨r', hr'⟩ := hmem
  exact ⟨r', hr'.symm⟩

/-- **Temporal rank of a family of non-interacting site packets.**  Under
mutual projective independence of the packet spectra, the rational temporal
rank of the total Hamiltonian is the sum of the maximal packet ranks. -/
theorem anchoredTemporalRank_sum_liftLocalMatrix [∀ v, Nonempty (A v)]
    {C : Type*} [Fintype C] [DecidableEq C]
    (S : C → Finset V) (hdisj : ∀ c d, c ≠ d → Disjoint (S c) (S d))
    (B : ∀ c, Matrix (LocalConfiguration A (S c))
      (LocalConfiguration A (S c)) ℂ)
    (hB : ∀ c, (B c).IsHermitian)
    (hindep : ComponentProjectivelyIndependent
      (fun c => (hB c).eigenvalues))
    (r : ∀ v, A v) :
    anchoredTemporalRank
        (isHermitian_sum_liftLocalMatrix S B hB Finset.univ).eigenvalues r =
      ∑ c, (Fintype.card (LocalConfiguration A (S c)) - 1) := by
  classical
  obtain ⟨r', hr'⟩ := exists_reference_sum_liftLocalMatrix S hdisj B hB r
  rw [anchoredTemporalRank_eq_of_range_eq
    (range_eigenvalues_sum_liftLocalMatrix S hdisj B hB Finset.univ) r r' hr']
  exact anchoredTemporalRank_finiteComponentSumEnergy_eq_sum
    (fun c => (hB c).eigenvalues) r' hindep

end

end GaloisForLFunctions.HTGeometry
