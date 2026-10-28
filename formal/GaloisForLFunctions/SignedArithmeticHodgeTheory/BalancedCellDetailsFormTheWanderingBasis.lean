import GaloisForLFunctions.SignedArithmeticHodgeTheory.TheLogCellClockHasACompleteWanderingDecomposition

/-!
# Explicit balanced coordinates of the dyadic wandering space

Each adjacent cell pair has one actual translated coarse direction and one
unit balanced detail. Together with the first cell, these details form a
Hilbert basis of the wandering space of the weighted logarithmic-cell clock.
-/

noncomputable section

open RHTower GaloisForLFunctions.HTGeometry.PNatBlock

namespace GaloisForLFunctions.SignedArithmeticHodgeTheory

local notation "CellH" => lp (fun _ : ℕ+ => ℂ) 2
local notation "W" => logCellShift 2
local notation "e" => fun n : ℕ+ => (lp.single 2 n (1 : ℂ) : CellH)

/-- Left child of a positive integer cell. -/
def dyadicLeftCell (a : ℕ+) : ℕ+ := ⟨2 * (a : ℕ), by have := a.pos; omega⟩

/-- Right child of a positive integer cell. -/
def dyadicRightCell (a : ℕ+) : ℕ+ := ⟨2 * (a : ℕ) + 1, by omega⟩

/-- The actual left-child coefficient of logarithmic translation. -/
def dyadicLeftWeight (a : ℕ+) : ℝ :=
  Real.sqrt (logCell (2 * (a : ℕ)) / logCell a)

/-- The actual right-child coefficient of logarithmic translation. -/
def dyadicRightWeight (a : ℕ+) : ℝ :=
  Real.sqrt (logCell (2 * (a : ℕ) + 1) / logCell a)

/-- The two cell-length weights give a unit rotation. -/
theorem dyadicCellWeights_sq (a : ℕ+) :
    dyadicLeftWeight a ^ 2 + dyadicRightWeight a ^ 2 = 1 := by
  have h := sum_sq_logCellWeight (p := 2) (n := (a : ℕ)) (by norm_num) a.pos
  simpa only [Fin.sum_univ_two, Fin.val_zero, Fin.val_one, Nat.add_zero, mul_comm,
    dyadicLeftWeight, dyadicRightWeight] using h

private theorem weights_sq_complex (a : ℕ+) :
    (dyadicLeftWeight a : ℂ) ^ 2 + (dyadicRightWeight a : ℂ) ^ 2 = 1 := by
  exact_mod_cast dyadicCellWeights_sq a

private theorem dyadic_apply (f : CellH) (m : ℕ+) :
    (W f) m = logCellWeight 2 m * extZero f ((m : ℕ) / 2) :=
  divBlockOp_apply (by norm_num) (norm_logCellWeight_le_one (by norm_num)) f m

private theorem left_div (a : ℕ+) : (dyadicLeftCell a : ℕ) / 2 = a := by
  change (2 * (a : ℕ)) / 2 = (a : ℕ)
  omega

private theorem right_div (a : ℕ+) : (dyadicRightCell a : ℕ) / 2 = a := by
  change (2 * (a : ℕ) + 1) / 2 = (a : ℕ)
  omega

private theorem dyadic_apply_left (f : CellH) (a : ℕ+) :
    (W f) (dyadicLeftCell a) = (dyadicLeftWeight a : ℂ) * f a := by
  rw [dyadic_apply, left_div, extZero_coe, logCellWeight, left_div]
  rfl

private theorem dyadic_apply_right (f : CellH) (a : ℕ+) :
    (W f) (dyadicRightCell a) = (dyadicRightWeight a : ℂ) * f a := by
  rw [dyadic_apply, right_div, extZero_coe, logCellWeight, right_div]
  rfl

private theorem dyadic_apply_one (f : CellH) : (W f) 1 = 0 := by
  rw [dyadic_apply]
  change logCellWeight 2 1 * extZero f 0 = 0
  rw [extZero_zero, mul_zero]

/-- The actual cell clock is the weighted coarse direction in each pair. -/
theorem logCellDyadic_single (a : ℕ+) :
    W (e a) = (dyadicLeftWeight a : ℂ) • e (dyadicLeftCell a) +
      (dyadicRightWeight a : ℂ) • e (dyadicRightCell a) := by
  have h := divBlockOp_single_eq_sum (b := 2) (by norm_num)
    (norm_logCellWeight_le_one (by norm_num : 2 ≤ 2)) a
  have h0 : (a : ℕ) * 2 + 0 = 2 * (a : ℕ) := by omega
  have h1 : (a : ℕ) * 2 + 1 = 2 * (a : ℕ) + 1 := by omega
  have hd0 : (2 * (a : ℕ)) / 2 = a := by omega
  have hd1 : (2 * (a : ℕ) + 1) / 2 = a := by omega
  simpa only [Fin.sum_univ_two, Fin.val_zero, Fin.val_one, h0, h1, logCellWeight,
    hd0, hd1, dyadicLeftWeight, dyadicRightWeight, dyadicLeftCell, dyadicRightCell,
    Nat.toPNat, logCellShift] using h

/-- Unit detail orthogonal to the actual coarse direction of a cell pair. -/
def logCellDyadicDetail (a : ℕ+) : CellH :=
  (dyadicRightWeight a : ℂ) • e (dyadicLeftCell a) -
    (dyadicLeftWeight a : ℂ) • e (dyadicRightCell a)

/-- The detail readout is the exact weighted difference of the two coordinates. -/
theorem inner_logCellDyadicDetail (a : ℕ+) (f : CellH) :
    inner ℂ (logCellDyadicDetail a) f =
      (dyadicRightWeight a : ℂ) * f (dyadicLeftCell a) -
        (dyadicLeftWeight a : ℂ) * f (dyadicRightCell a) := by
  simp only [logCellDyadicDetail, inner_sub_left, inner_smul_left, lp.inner_single_left,
    RCLike.inner_apply, map_one, mul_one, Complex.conj_ofReal]

/-- Balanced details belong to the actual wandering space. -/
theorem logCellDyadicDetail_mem (a : ℕ+) :
    logCellDyadicDetail a ∈ logCellDyadicWandering := by
  apply (Submodule.mem_orthogonal' _ _).mpr
  rintro _ ⟨f, rfl⟩
  change inner ℂ (logCellDyadicDetail a) (W f) = 0
  rw [inner_logCellDyadicDetail, dyadic_apply_left, dyadic_apply_right]
  ring

private theorem firstCell_mem : e 1 ∈ logCellDyadicWandering := by
  apply (Submodule.mem_orthogonal' _ _).mpr
  rintro _ ⟨f, rfl⟩
  change inner ℂ (e 1) (W f) = 0
  rw [lp.inner_single_left, RCLike.inner_apply, dyadic_apply_one]
  simp

private theorem left_ne_right (a b : ℕ+) : dyadicLeftCell a ≠ dyadicRightCell b := by
  intro h
  have h' := congrArg PNat.val h
  change 2 * (a : ℕ) = 2 * (b : ℕ) + 1 at h'
  omega

private theorem left_ne_one (a : ℕ+) : dyadicLeftCell a ≠ 1 := by
  intro h
  have h' := congrArg PNat.val h
  have := a.pos
  change 2 * (a : ℕ) = 1 at h'
  omega

private theorem right_ne_one (a : ℕ+) : dyadicRightCell a ≠ 1 := by
  intro h
  have h' := congrArg PNat.val h
  have := a.pos
  change 2 * (a : ℕ) + 1 = 1 at h'
  omega

private theorem inner_unit (a b : ℕ+) : inner ℂ (e a) (e b) = if a = b then 1 else 0 := by
  classical
  simpa only [HilbertSchmidt.lpBasis_apply] using
    (orthonormal_iff_ite.mp (HilbertSchmidt.lpBasis ℕ+).orthonormal) a b

/-- Distinct balanced details are orthogonal and each has unit norm. -/
theorem inner_logCellDyadicDetail_detail (a b : ℕ+) :
    inner ℂ (logCellDyadicDetail a) (logCellDyadicDetail b) = if a = b then 1 else 0 := by
  classical
  simp only [logCellDyadicDetail, inner_sub_left, inner_sub_right,
    inner_smul_left, inner_smul_right, Complex.conj_ofReal, inner_unit]
  by_cases hab : a = b
  · subst b
    simp only [ite_true, if_neg (left_ne_right a a), if_neg (left_ne_right a a).symm,
      mul_one, mul_zero, sub_zero, zero_sub, mul_neg, sub_neg_eq_add]
    calc
      _ = (dyadicLeftWeight a : ℂ) ^ 2 + (dyadicRightWeight a : ℂ) ^ 2 := by ring
      _ = 1 := weights_sq_complex a
  · have hll : dyadicLeftCell a ≠ dyadicLeftCell b := by
      intro h
      apply hab
      apply PNat.eq
      have h' := congrArg PNat.val h
      change 2 * (a : ℕ) = 2 * (b : ℕ) at h'
      omega
    have hrr : dyadicRightCell a ≠ dyadicRightCell b := by
      intro h
      apply hab
      apply PNat.eq
      have h' := congrArg PNat.val h
      change 2 * (a : ℕ) + 1 = 2 * (b : ℕ) + 1 at h'
      omega
    simp only [if_neg hab, if_neg hll, if_neg hrr, if_neg (left_ne_right a b),
      if_neg (left_ne_right b a).symm, mul_zero, sub_zero]

/-- The first cell and one balanced detail for each adjacent pair. -/
def logCellDyadicGenerator : Option ℕ+ → CellH
  | none => e 1
  | some a => logCellDyadicDetail a

theorem logCellDyadicGenerator_mem (i : Option ℕ+) :
    logCellDyadicGenerator i ∈ logCellDyadicWandering := by
  cases i with
  | none => exact firstCell_mem
  | some a => exact logCellDyadicDetail_mem a

/-- Vanishing first-cell and detail readouts determine a wandering vector. -/
theorem eq_zero_of_logCellDyadic_coordinates {x : CellH}
    (hx : x ∈ logCellDyadicWandering) (hfirst : x 1 = 0)
    (hdetail : ∀ a : ℕ+, inner ℂ (logCellDyadicDetail a) x = 0) : x = 0 := by
  have hpair (a : ℕ+) : x (dyadicLeftCell a) = 0 ∧ x (dyadicRightCell a) = 0 := by
    have hc := (Submodule.mem_orthogonal _ _).mp hx (W (e a))
      (LinearMap.mem_range.mpr ⟨e a, rfl⟩)
    rw [logCellDyadic_single] at hc
    simp only [inner_add_left, inner_smul_left, lp.inner_single_left, RCLike.inner_apply,
      map_one, mul_one, Complex.conj_ofReal] at hc
    have hd := hdetail a
    rw [inner_logCellDyadicDetail] at hd
    have hu := weights_sq_complex a
    constructor
    · calc
        x (dyadicLeftCell a) =
            ((dyadicLeftWeight a : ℂ) ^ 2 + (dyadicRightWeight a : ℂ) ^ 2) *
              x (dyadicLeftCell a) := by rw [hu, one_mul]
        _ = (dyadicLeftWeight a : ℂ) *
              ((dyadicLeftWeight a : ℂ) * x (dyadicLeftCell a) +
                (dyadicRightWeight a : ℂ) * x (dyadicRightCell a)) +
            (dyadicRightWeight a : ℂ) *
              ((dyadicRightWeight a : ℂ) * x (dyadicLeftCell a) -
                (dyadicLeftWeight a : ℂ) * x (dyadicRightCell a)) := by ring
        _ = 0 := by rw [hc, hd]; ring
    · calc
        x (dyadicRightCell a) =
            ((dyadicLeftWeight a : ℂ) ^ 2 + (dyadicRightWeight a : ℂ) ^ 2) *
              x (dyadicRightCell a) := by rw [hu, one_mul]
        _ = (dyadicRightWeight a : ℂ) *
              ((dyadicLeftWeight a : ℂ) * x (dyadicLeftCell a) +
                (dyadicRightWeight a : ℂ) * x (dyadicRightCell a)) -
            (dyadicLeftWeight a : ℂ) *
              ((dyadicRightWeight a : ℂ) * x (dyadicLeftCell a) -
                (dyadicLeftWeight a : ℂ) * x (dyadicRightCell a)) := by ring
        _ = 0 := by rw [hc, hd]; ring
  refine lp.ext (funext fun m => ?_)
  change x m = 0
  by_cases hm : m = 1
  · simpa only [hm] using hfirst
  · have hm2 : 2 ≤ (m : ℕ) := by
      have := m.pos
      have hne : (m : ℕ) ≠ 1 := fun h => hm (PNat.eq h)
      omega
    let a : ℕ+ := ⟨(m : ℕ) / 2, by omega⟩
    have hcases : (m : ℕ) = 2 * (a : ℕ) ∨ (m : ℕ) = 2 * (a : ℕ) + 1 := by
      change (m : ℕ) = 2 * ((m : ℕ) / 2) ∨ (m : ℕ) = 2 * ((m : ℕ) / 2) + 1
      omega
    rcases hcases with h | h
    · have he : m = dyadicLeftCell a := PNat.eq h
      simpa only [he] using (hpair a).1
    · have he : m = dyadicRightCell a := PNat.eq h
      simpa only [he] using (hpair a).2

private theorem inner_first_detail (a : ℕ+) : inner ℂ (e 1) (logCellDyadicDetail a) = 0 := by
  simp only [logCellDyadicDetail, inner_sub_right, inner_smul_right, inner_unit,
    if_neg (left_ne_one a).symm, if_neg (right_ne_one a).symm, mul_zero, sub_zero]

private theorem inner_detail_first (a : ℕ+) : inner ℂ (logCellDyadicDetail a) (e 1) = 0 := by
  simp only [logCellDyadicDetail, inner_sub_left, inner_smul_left, inner_unit,
    if_neg (left_ne_one a), if_neg (right_ne_one a), mul_zero, sub_zero]

/-- The first cell and every balanced detail form an orthonormal family. -/
theorem orthonormal_logCellDyadicGenerator : Orthonormal ℂ logCellDyadicGenerator := by
  classical
  apply orthonormal_iff_ite.mpr
  intro i j
  cases i with
  | none =>
    cases j with
    | none => simp only [logCellDyadicGenerator, inner_unit, ite_true]
    | some b => simpa only [logCellDyadicGenerator, reduceCtorEq, if_false] using inner_first_detail b
  | some a =>
    cases j with
    | none => simpa only [logCellDyadicGenerator, reduceCtorEq, if_false] using inner_detail_first a
    | some b => simpa only [logCellDyadicGenerator, Option.some.injEq] using
        inner_logCellDyadicDetail_detail a b

/-- Explicit generators viewed inside the completed wandering space. -/
def logCellDyadicGeneratorInWandering (i : Option ℕ+) : logCellDyadicWandering :=
  ⟨logCellDyadicGenerator i, logCellDyadicGenerator_mem i⟩

private theorem generators_orthonormal : Orthonormal ℂ logCellDyadicGeneratorInWandering := by
  classical
  apply orthonormal_iff_ite.mpr
  intro i j
  change inner ℂ (logCellDyadicGenerator i) (logCellDyadicGenerator j) = _
  exact orthonormal_iff_ite.mp orthonormal_logCellDyadicGenerator i j

/-- The explicit readouts leave no missing wandering direction. -/
theorem logCellDyadicGenerator_total :
    (Submodule.span ℂ (Set.range logCellDyadicGeneratorInWandering))ᗮ = ⊥ := by
  apply (Submodule.eq_bot_iff _).mpr
  intro x hx
  apply Subtype.ext
  change (x : CellH) = 0
  apply eq_zero_of_logCellDyadic_coordinates x.property
  · have h := (Submodule.mem_orthogonal _ _).mp hx (logCellDyadicGeneratorInWandering none)
      (Submodule.subset_span ⟨none, rfl⟩)
    change inner ℂ (e 1) (x : CellH) = 0 at h
    simpa only [lp.inner_single_left, RCLike.inner_apply, map_one, mul_one] using h
  · intro a
    exact (Submodule.mem_orthogonal _ _).mp hx (logCellDyadicGeneratorInWandering (some a))
      (Submodule.subset_span ⟨some a, rfl⟩)

instance : CompleteSpace logCellDyadicWandering :=
  (Submodule.isClosed_orthogonal
    (LinearMap.range (logCellShift 2).toLinearMap)).completeSpace_coe

/-- The completed wandering space has exactly the first cell and balanced details
as its Hilbert coordinates. -/
def logCellDyadicWanderingBasis : HilbertBasis (Option ℕ+) ℂ logCellDyadicWandering :=
  HilbertBasis.mkOfOrthogonalEqBot generators_orthonormal logCellDyadicGenerator_total

/-- The Hilbert-basis construction retains the literal arithmetic generators. -/
theorem logCellDyadicWanderingBasis_apply (i : Option ℕ+) :
    (logCellDyadicWanderingBasis i : CellH) = logCellDyadicGenerator i := by
  exact congrArg (fun v : logCellDyadicWandering => (v : CellH))
    (congrFun (HilbertBasis.coe_mkOfOrthogonalEqBot generators_orthonormal
      logCellDyadicGenerator_total) i)

end GaloisForLFunctions.SignedArithmeticHodgeTheory

#print axioms GaloisForLFunctions.SignedArithmeticHodgeTheory.logCellDyadic_single
#print axioms GaloisForLFunctions.SignedArithmeticHodgeTheory.logCellDyadicDetail_mem
#print axioms GaloisForLFunctions.SignedArithmeticHodgeTheory.inner_logCellDyadicDetail_detail
#print axioms GaloisForLFunctions.SignedArithmeticHodgeTheory.eq_zero_of_logCellDyadic_coordinates

#print axioms GaloisForLFunctions.SignedArithmeticHodgeTheory.logCellDyadicGenerator_total
#print axioms GaloisForLFunctions.SignedArithmeticHodgeTheory.logCellDyadicWanderingBasis
