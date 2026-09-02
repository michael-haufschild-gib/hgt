import GaloisForLFunctions.HTGeometry.DifferentialVariationalProjectiveStandardApartment

/-!
# Commensurability of completed pseudodifferential valuation lattices

Every completed pseudodifferential operator has an integral valuation floor, and a sufficiently
large left power of the canonical uniformizer clears its denominator.  Finite generation gives a
uniform floor for an entire lattice.  Full completed-skew span gives finitely many coefficient
denominators for the standard basis, hence one uniformizer power clearing all of them.

Consequently every full finite valuation lattice lies between two constant-coweight standard
lattices.  Any two such lattices are therefore commensurable by correctly oriented left
uniformizer homotheties.  This is the lattice-boundedness prerequisite for a later relative-position
and metric construction; it does not assert a Cartan decomposition.
-/

open scoped Differential

namespace GaloisForLFunctions.HTGeometry.DiffOp

noncomputable section

variable {K : Type u} [Field K] [Differential K]

/-- Every completed pseudodifferential operator has an integral lower valuation bound. -/
theorem exists_int_le_completedPseudoDiffOpAddValue
    (x : CompletedPseudoDiffOp K) :
    ∃ m : ℤ, (m : WithTop ℤ) ≤ completedPseudoDiffOpAddValue x := by
  by_cases hx : x = 0
  · subst x
    exact ⟨0, (mem_completedPseudoDiffOpInteger_iff_addValue_nonneg 0).1
      (zero_mem _)⟩
  · exact ⟨(completedPseudoDiffOpAddValue x).untop
      (completedPseudoDiffOpAddValue_ne_top_of_ne_zero hx),
      (WithTop.coe_untop _ _).le⟩

/-- Every element lies in some constant-coweight standard lattice. -/
theorem exists_uniformizer_right_unscale_mem_integer
    (x : CompletedPseudoDiffOp K) :
    ∃ m : ℤ,
      x * ((completedPseudoDiffOpUniformizerUnit (K := K) ^ m)⁻¹ :
          (CompletedPseudoDiffOp K)ˣ) ∈ CompletedPseudoDiffOpInteger (K := K) := by
  obtain ⟨m, hm⟩ := exists_int_le_completedPseudoDiffOpAddValue x
  refine ⟨m, (mem_completedPseudoDiffOpInteger_iff_addValue_nonneg _).2 ?_⟩
  rw [completedPseudoDiffOpAddValue_mul,
    completedPseudoDiffOpAddValue_unit_eq_coe,
    completedPseudoDiffOpUnitAddValue_inv,
    completedPseudoDiffOpUnitAddValue_uniformizer_zpow]
  calc
    0 = (m : WithTop ℤ) + ((-m : ℤ) : WithTop ℤ) := by simp
    _ ≤ completedPseudoDiffOpAddValue x + ((-m : ℤ) : WithTop ℤ) :=
      by simpa [add_comm] using
        add_le_add_right hm (((-m : ℤ) : WithTop ℤ))

/-- A uniformizer power clears the left denominator of every completed operator. -/
theorem exists_uniformizer_left_scale_mem_integer
    (x : CompletedPseudoDiffOp K) :
    ∃ a : ℤ,
      ((completedPseudoDiffOpUniformizerUnit (K := K) ^ a :
          (CompletedPseudoDiffOp K)ˣ) : CompletedPseudoDiffOp K) * x ∈
        CompletedPseudoDiffOpInteger (K := K) := by
  by_cases hx : x = 0
  · subst x
    exact ⟨0, by simp⟩
  · let ux : (CompletedPseudoDiffOp K)ˣ := Units.mk0 x hx
    let a := -completedPseudoDiffOpUnitAddValue ux
    refine ⟨a, ?_⟩
    rw [mem_completedPseudoDiffOpInteger_iff_addValue_nonneg]
    change 0 ≤ completedPseudoDiffOpAddValue
      (((completedPseudoDiffOpUniformizerUnit (K := K) ^ a * ux :
          (CompletedPseudoDiffOp K)ˣ) : CompletedPseudoDiffOp K))
    rw [completedPseudoDiffOpAddValue_unit_eq_coe,
      completedPseudoDiffOpUnitAddValue_mul,
      completedPseudoDiffOpUnitAddValue_uniformizer_zpow]
    norm_cast
    simp [a]

/-- Enlarging a left denominator-clearing exponent preserves integrality. -/
theorem uniformizer_left_scale_mem_integer_of_le
    (x : CompletedPseudoDiffOp K) {b a : ℤ} (hba : b ≤ a)
    (hx : ((completedPseudoDiffOpUniformizerUnit (K := K) ^ b :
        (CompletedPseudoDiffOp K)ˣ) : CompletedPseudoDiffOp K) * x ∈
      CompletedPseudoDiffOpInteger (K := K)) :
    ((completedPseudoDiffOpUniformizerUnit (K := K) ^ a :
        (CompletedPseudoDiffOp K)ˣ) : CompletedPseudoDiffOp K) * x ∈
      CompletedPseudoDiffOpInteger (K := K) := by
  rw [mem_completedPseudoDiffOpInteger_iff_addValue_nonneg,
    completedPseudoDiffOpAddValue_mul,
    completedPseudoDiffOpAddValue_unit_eq_coe,
    completedPseudoDiffOpUnitAddValue_uniformizer_zpow] at hx ⊢
  exact hx.trans (add_le_add
    (WithTop.coe_le_coe.mpr hba) le_rfl)

variable {ι : Type*} [Fintype ι]

/-- Every full finite valuation lattice is contained in one constant-coweight standard lattice. -/
theorem exists_le_standardCompletedPseudoDiffOpLatticeAtConstantCoweight
    (L : CompletedPseudoDiffOpLattice K ι) :
    ∃ m : ℤ, L.carrier ≤
      (standardCompletedPseudoDiffOpLatticeAtCoweight (K := K)
        (fun _ : ι => m)).carrier := by
  classical
  obtain ⟨S, hSfinite, hSspan⟩ := Submodule.fg_def.mp L.fg
  let lowerBound : CompletedPseudoDiffOp K → ℤ := fun x =>
    Classical.choose (exists_int_le_completedPseudoDiffOpAddValue x)
  have lowerBound_spec (x : CompletedPseudoDiffOp K) :
      (lowerBound x : WithTop ℤ) ≤ completedPseudoDiffOpAddValue x :=
    Classical.choose_spec (exists_int_le_completedPseudoDiffOpAddValue x)
  let pairs : Finset ((ι → CompletedPseudoDiffOp K) × ι) :=
    hSfinite.toFinset ×ˢ Finset.univ
  let bounds : Finset ℤ :=
    insert 0 (pairs.image (fun p => lowerBound (p.1 p.2)))
  have bounds_nonempty : bounds.Nonempty := by
    exact ⟨0, by simp [bounds]⟩
  let m : ℤ := bounds.min' bounds_nonempty
  have m_le (s : ι → CompletedPseudoDiffOp K) (hs : s ∈ S) (i : ι) :
      m ≤ lowerBound (s i) := by
    apply Finset.min'_le bounds (lowerBound (s i))
    apply Finset.mem_insert_of_mem
    apply Finset.mem_image.mpr
    refine ⟨(s, i), ?_, rfl⟩
    simp [pairs, hSfinite.mem_toFinset, hs]
  refine ⟨m, ?_⟩
  rw [← hSspan, Submodule.span_le]
  intro s hs
  apply (mem_standardCompletedPseudoDiffOpLatticeAtCoweight_iff _ _).2
  intro i
  rw [completedPseudoDiffOpUniformizerCoweight,
    mem_completedPseudoDiffOpInteger_iff_addValue_nonneg,
    completedPseudoDiffOpAddValue_mul,
    completedPseudoDiffOpAddValue_unit_eq_coe,
    completedPseudoDiffOpUnitAddValue_inv,
    completedPseudoDiffOpUnitAddValue_uniformizer_zpow]
  have hmv : (m : WithTop ℤ) ≤ completedPseudoDiffOpAddValue (s i) :=
    (WithTop.coe_le_coe.mpr (m_le s hs i)).trans (lowerBound_spec (s i))
  calc
    0 = (m : WithTop ℤ) + ((-m : ℤ) : WithTop ℤ) := by simp
    _ ≤ completedPseudoDiffOpAddValue (s i) + ((-m : ℤ) : WithTop ℤ) := by
      simpa [add_comm] using
        add_le_add_right hmv (((-m : ℤ) : WithTop ℤ))

/-- Every full finite valuation lattice contains one constant-coweight standard lattice. -/
theorem exists_standardCompletedPseudoDiffOpLatticeAtConstantCoweight_le
    (L : CompletedPseudoDiffOpLattice K ι) :
    ∃ a : ℤ,
      (standardCompletedPseudoDiffOpLatticeAtCoweight (K := K)
        (fun _ : ι => a)).carrier ≤ L.carrier := by
  classical
  let basisVector : ι → (ι → CompletedPseudoDiffOp K) :=
    fun i => (Pi.basisFun (CompletedPseudoDiffOp K) ι) i
  have basis_mem_span (i : ι) : basisVector i ∈
      Submodule.span (CompletedPseudoDiffOp K)
        (L.carrier : Set (ι → CompletedPseudoDiffOp K)) := by
    rw [L.full]
    trivial
  let coeff : ι → ((ι → CompletedPseudoDiffOp K) →₀ CompletedPseudoDiffOp K) :=
    fun i => Classical.choose (Submodule.mem_span_set.mp (basis_mem_span i))
  have coeff_support (i : ι) :
      ((coeff i).support : Set (ι → CompletedPseudoDiffOp K)) ⊆
        (L.carrier : Set (ι → CompletedPseudoDiffOp K)) :=
    (Classical.choose_spec (Submodule.mem_span_set.mp (basis_mem_span i))).1
  have coeff_sum (i : ι) :
      (coeff i).sum (fun v r => r • v) = basisVector i :=
    (Classical.choose_spec (Submodule.mem_span_set.mp (basis_mem_span i))).2
  let clearExponent : CompletedPseudoDiffOp K → ℤ := fun x =>
    Classical.choose (exists_uniformizer_left_scale_mem_integer x)
  have clearExponent_spec (x : CompletedPseudoDiffOp K) :
      ((completedPseudoDiffOpUniformizerUnit (K := K) ^ clearExponent x :
          (CompletedPseudoDiffOp K)ˣ) : CompletedPseudoDiffOp K) * x ∈
        CompletedPseudoDiffOpInteger (K := K) :=
    Classical.choose_spec (exists_uniformizer_left_scale_mem_integer x)
  let pairs : Finset ((i : ι) × (ι → CompletedPseudoDiffOp K)) :=
    Finset.univ.sigma (fun i => (coeff i).support)
  let exponents : Finset ℤ :=
    insert 0 (pairs.image (fun p => clearExponent (coeff p.1 p.2)))
  have exponents_nonempty : exponents.Nonempty := by
    exact ⟨0, by simp [exponents]⟩
  let a : ℤ := exponents.max' exponents_nonempty
  have clearExponent_le (i : ι) (v : ι → CompletedPseudoDiffOp K)
      (hv : v ∈ (coeff i).support) : clearExponent (coeff i v) ≤ a := by
    apply Finset.le_max' exponents (clearExponent (coeff i v))
    apply Finset.mem_insert_of_mem
    apply Finset.mem_image.mpr
    refine ⟨⟨i, v⟩, ?_, rfl⟩
    simp [pairs, hv]
  have coeff_integral (i : ι) (v : ι → CompletedPseudoDiffOp K) :
      ((completedPseudoDiffOpUniformizerUnit (K := K) ^ a :
          (CompletedPseudoDiffOp K)ˣ) : CompletedPseudoDiffOp K) * coeff i v ∈
        CompletedPseudoDiffOpInteger (K := K) := by
    by_cases hv : coeff i v = 0
    · simp [hv]
    · exact uniformizer_left_scale_mem_integer_of_le (coeff i v)
        (clearExponent_le i v (Finsupp.mem_support_iff.mpr hv))
        (clearExponent_spec (coeff i v))
  have scaled_basis_mem (i : ι) :
      ((completedPseudoDiffOpUniformizerUnit (K := K) ^ a :
          (CompletedPseudoDiffOp K)ˣ) : CompletedPseudoDiffOp K) • basisVector i ∈
        L.carrier := by
    have hcombo : (coeff i).sum (fun v _ =>
        (⟨((completedPseudoDiffOpUniformizerUnit (K := K) ^ a :
              (CompletedPseudoDiffOp K)ˣ) : CompletedPseudoDiffOp K) * coeff i v,
            coeff_integral i v⟩ : CompletedPseudoDiffOpInteger (K := K)) • v) ∈
        L.carrier := by
      rw [Finsupp.sum]
      apply L.carrier.sum_mem
      intro v hv
      exact L.carrier.smul_mem _ (coeff_support i hv)
    convert hcombo using 1
    rw [← coeff_sum i, Finsupp.sum, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro v hv
    change ((completedPseudoDiffOpUniformizerUnit (K := K) ^ a :
        (CompletedPseudoDiffOp K)ˣ) : CompletedPseudoDiffOp K) •
        (coeff i v • v) =
      (((completedPseudoDiffOpUniformizerUnit (K := K) ^ a :
        (CompletedPseudoDiffOp K)ˣ) : CompletedPseudoDiffOp K) * coeff i v) • v
    exact smul_smul _ _ _
  refine ⟨a, ?_⟩
  intro x hx
  rw [standardCompletedPseudoDiffOpLatticeAtCoweight,
    mem_diagonalScaleCompletedPseudoDiffOpLattice_iff] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  have hy_integral (i : ι) :
      y i ∈ CompletedPseudoDiffOpInteger (K := K) :=
    (mem_standardCompletedPseudoDiffOpLattice_iff y).mp hy i
  have hdecomp :
      diagonalRightMulCompletedPseudoIntegerVecLinearEquiv
          (completedPseudoDiffOpUniformizerCoweight (K := K) (fun _ : ι => a)) y =
        ∑ i, (⟨y i, hy_integral i⟩ : CompletedPseudoDiffOpInteger (K := K)) •
          (((completedPseudoDiffOpUniformizerUnit (K := K) ^ a :
              (CompletedPseudoDiffOp K)ˣ) : CompletedPseudoDiffOp K) • basisVector i) := by
    funext j
    simp [diagonalRightMulCompletedPseudoIntegerVecLinearEquiv,
      completedPseudoDiffOpUniformizerCoweight, basisVector, Pi.basisFun_apply,
      Pi.single_apply]
    rfl
  rw [hdecomp]
  apply L.carrier.sum_mem
  intro i hi
  exact L.carrier.smul_mem _ (scaled_basis_mem i)

/-- Pointwise larger coweights give smaller diagonal valuation lattices. -/
theorem standardCompletedPseudoDiffOpLatticeAtCoweight_antitone
    {m n : ι → ℤ} (h : ∀ i, n i ≤ m i) :
    (standardCompletedPseudoDiffOpLatticeAtCoweight (K := K) m).carrier ≤
      (standardCompletedPseudoDiffOpLatticeAtCoweight n).carrier := by
  intro x hx
  apply (mem_standardCompletedPseudoDiffOpLatticeAtCoweight_iff n x).2
  intro i
  have hxi := (mem_standardCompletedPseudoDiffOpLatticeAtCoweight_iff m x).1 hx i
  rw [completedPseudoDiffOpUniformizerCoweight,
    mem_completedPseudoDiffOpInteger_iff_addValue_nonneg,
    completedPseudoDiffOpAddValue_mul,
    completedPseudoDiffOpAddValue_unit_eq_coe,
    completedPseudoDiffOpUnitAddValue_inv,
    completedPseudoDiffOpUnitAddValue_uniformizer_zpow] at hxi ⊢
  exact hxi.trans (add_le_add le_rfl
    (WithTop.coe_le_coe.mpr (neg_le_neg (h i))))

omit [Fintype ι] in
/-- Left homothety preserves inclusions of full valuation lattices. -/
theorem leftScaleCompletedPseudoDiffOpLattice_carrier_mono
    (a : (CompletedPseudoDiffOp K)ˣ) {L M : CompletedPseudoDiffOpLattice K ι}
    (h : L.carrier ≤ M.carrier) :
    (leftScaleCompletedPseudoDiffOpLattice a L).carrier ≤
      (leftScaleCompletedPseudoDiffOpLattice a M).carrier := by
  intro y hy
  obtain ⟨x, hx, rfl⟩ :=
    (mem_leftScaleCompletedPseudoDiffOpLattice_iff a L y).1 hy
  exact (mem_leftScaleCompletedPseudoDiffOpLattice_iff a M _).2
    ⟨x, h hx, rfl⟩

/-- Correctly oriented commensurability by left uniformizer homotheties. -/
def CompletedPseudoDiffOpLattice.LeftCommensurable
    (L M : CompletedPseudoDiffOpLattice K ι) : Prop :=
  ∃ a b : ℤ,
    (leftScaleCompletedPseudoDiffOpLattice
        (completedPseudoDiffOpUniformizerUnit (K := K) ^ a) L).carrier ≤ M.carrier ∧
    M.carrier ≤
      (leftScaleCompletedPseudoDiffOpLattice
        (completedPseudoDiffOpUniformizerUnit (K := K) ^ b) L).carrier

/-- Every pair of full finite valuation lattices is left-commensurable. -/
theorem completedPseudoDiffOpLattice_leftCommensurable
    (L M : CompletedPseudoDiffOpLattice K ι) : L.LeftCommensurable M := by
  obtain ⟨lLow, hlLow⟩ :=
    exists_standardCompletedPseudoDiffOpLatticeAtConstantCoweight_le L
  obtain ⟨lHigh, hlHigh⟩ :=
    exists_le_standardCompletedPseudoDiffOpLatticeAtConstantCoweight L
  obtain ⟨mLow, hmLow⟩ :=
    exists_standardCompletedPseudoDiffOpLatticeAtConstantCoweight_le M
  obtain ⟨mHigh, hmHigh⟩ :=
    exists_le_standardCompletedPseudoDiffOpLatticeAtConstantCoweight M
  refine ⟨mLow - lHigh, mHigh - lLow, ?_, ?_⟩
  · calc
      (leftScaleCompletedPseudoDiffOpLattice
          (completedPseudoDiffOpUniformizerUnit (K := K) ^ (mLow - lHigh)) L).carrier ≤
        (leftScaleCompletedPseudoDiffOpLattice
          (completedPseudoDiffOpUniformizerUnit (K := K) ^ (mLow - lHigh))
          (standardCompletedPseudoDiffOpLatticeAtCoweight
            (K := K) (fun _ : ι => lHigh))).carrier :=
        leftScaleCompletedPseudoDiffOpLattice_carrier_mono _ hlHigh
      _ = (standardCompletedPseudoDiffOpLatticeAtCoweight
          (K := K) (fun _ : ι => mLow)).carrier := by
        rw [leftScale_standardCompletedPseudoDiffOpLatticeAtCoweight_add_const]
        congr 2
        funext i
        simp
      _ ≤ M.carrier := hmLow
  · calc
      M.carrier ≤ (standardCompletedPseudoDiffOpLatticeAtCoweight
          (K := K) (fun _ : ι => mHigh)).carrier := hmHigh
      _ = (leftScaleCompletedPseudoDiffOpLattice
          (completedPseudoDiffOpUniformizerUnit (K := K) ^ (mHigh - lLow))
          (standardCompletedPseudoDiffOpLatticeAtCoweight
            (K := K) (fun _ : ι => lLow))).carrier := by
        rw [leftScale_standardCompletedPseudoDiffOpLatticeAtCoweight_add_const]
        congr 2
        funext i
        simp
      _ ≤ (leftScaleCompletedPseudoDiffOpLattice
          (completedPseudoDiffOpUniformizerUnit (K := K) ^ (mHigh - lLow)) L).carrier :=
        leftScaleCompletedPseudoDiffOpLattice_carrier_mono _ hlLow

end

end GaloisForLFunctions.HTGeometry.DiffOp
