import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Matrix.Basis
import Mathlib.LinearAlgebra.Dimension.OrzechProperty
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# A Hermitian unit basis of the local qudit operator algebra

For local dimension `D` the `D^2` matrices

* `1` (label `(0,0)`),
* `E_{kk} - E_{00}` (label `(k,k)`, `k ≠ 0`),
* `E_{ij} + E_{ji}` (label `(i,j)`, `i < j`),
* `i(E_{ij} - E_{ji})` (label `(i,j)`, `i > j`)

are Hermitian, and every one of them except the identity is traceless.  This file
constructs them, proves Hermiticity and the trace dichotomy, and inverts the
change of basis: every matrix unit `E_{ab}` is an explicit complex combination of
them.  Together with the `D^2 = D^2` count this exhibits the family as a basis of
the local operator algebra; the string layer built on top of it inherits the
basis property by a product expansion.
-/

open Matrix

namespace GaloisForLFunctions.HTGeometry

variable {D : ℕ} [NeZero D]

/-- The local Hermitian unit attached to a pair of local indices.  The pair
`(0,0)` labels the identity; every other pair labels a traceless Hermitian
matrix. -/
noncomputable def quditHermUnit (p : Fin D × Fin D) : Matrix (Fin D) (Fin D) ℂ :=
  if p.1 = p.2 then
    (if p.1 = 0 then 1 else Matrix.single p.1 p.1 1 - Matrix.single 0 0 1)
  else if p.1 < p.2 then Matrix.single p.1 p.2 1 + Matrix.single p.2 p.1 1
  else Complex.I • (Matrix.single p.1 p.2 1 - Matrix.single p.2 p.1 1)

@[simp] theorem quditHermUnit_zero : quditHermUnit ((0, 0) : Fin D × Fin D) = 1 := by
  simp [quditHermUnit]

theorem quditHermUnit_diag_of_ne_zero {k : Fin D} (hk : k ≠ 0) :
    quditHermUnit ((k, k) : Fin D × Fin D)
      = Matrix.single k k 1 - Matrix.single 0 0 1 := by
  simp [quditHermUnit, hk]

theorem quditHermUnit_lt {i j : Fin D} (hij : i < j) :
    quditHermUnit ((i, j) : Fin D × Fin D)
      = Matrix.single i j 1 + Matrix.single j i 1 := by
  have hne : i ≠ j := ne_of_lt hij
  simp [quditHermUnit, hne, hij]

theorem quditHermUnit_gt {i j : Fin D} (hij : j < i) :
    quditHermUnit ((i, j) : Fin D × Fin D)
      = Complex.I • (Matrix.single i j 1 - Matrix.single j i 1) := by
  have hne : i ≠ j := (ne_of_lt hij).symm
  have : ¬ i < j := not_lt.mpr (le_of_lt hij)
  simp [quditHermUnit, hne, this]

/-- Every local Hermitian unit is Hermitian. -/
theorem quditHermUnit_conjTranspose (p : Fin D × Fin D) :
    (quditHermUnit p)ᴴ = quditHermUnit p := by
  rcases eq_or_ne p.1 p.2 with hd | hd
  · rcases eq_or_ne p.1 0 with h0 | h0
    · have : p = (0, 0) := Prod.ext h0 (hd ▸ h0)
      rw [this, quditHermUnit_zero, Matrix.conjTranspose_one]
    · have hp : p = (p.1, p.1) := Prod.ext rfl hd.symm
      rw [hp, quditHermUnit_diag_of_ne_zero h0]
      ext r c
      simp [Matrix.single_apply, Matrix.conjTranspose_apply, and_comm]
  · rcases lt_or_gt_of_ne hd with hlt | hgt
    · have hp : p = (p.1, p.2) := rfl
      rw [hp, quditHermUnit_lt hlt]
      ext r c
      simp [Matrix.single_apply, Matrix.conjTranspose_apply, and_comm]
      exact add_comm _ _
    · have hp : p = (p.1, p.2) := rfl
      rw [hp, quditHermUnit_gt hgt]
      ext r c
      simp [Matrix.single_apply, Matrix.conjTranspose_apply, Complex.ext_iff,
        and_comm]

/-- Coefficients expressing the matrix unit `E_{ab}` in the Hermitian unit
basis. -/
noncomputable def quditUnitCoeff (a b : Fin D) (p : Fin D × Fin D) : ℂ :=
  if a = b then
    (if p.1 = p.2 then
      (if p.1 = 0 then (D : ℂ)⁻¹
       else if p.1 = a then 1 - (D : ℂ)⁻¹
       else -(D : ℂ)⁻¹)
     else 0)
  else if p = (a, b) then (if a < b then 1 / 2 else -(Complex.I / 2))
  else if p = (b, a) then (if a < b then Complex.I / 2 else 1 / 2)
  else 0

/-- The diagonal part of the Hermitian unit family assembles into an explicit
diagonal matrix: the identity label contributes uniformly and every other
diagonal label moves weight from the ground index. -/
theorem sum_diag_smul_quditHermUnit (c : Fin D → ℂ) :
    ∑ k : Fin D, c k • quditHermUnit ((k, k) : Fin D × Fin D)
      = Matrix.diagonal (fun j =>
          if j = 0 then c 0 - ∑ k ∈ Finset.univ.erase (0 : Fin D), c k
          else c 0 + c j) := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : Fin D))]
  have hrest : ∑ k ∈ Finset.univ.erase (0 : Fin D),
        c k • quditHermUnit ((k, k) : Fin D × Fin D)
      = ∑ k ∈ Finset.univ.erase (0 : Fin D),
        c k • (Matrix.single k k (1 : ℂ) - Matrix.single 0 0 (1 : ℂ)) :=
    Finset.sum_congr rfl fun k hk => by
      rw [quditHermUnit_diag_of_ne_zero (Finset.ne_of_mem_erase hk)]
  rw [hrest, quditHermUnit_zero]
  ext r s
  have hentry : ∀ k : Fin D,
      ((c k • (Matrix.single k k (1 : ℂ) - Matrix.single 0 0 (1 : ℂ)) :
          Matrix (Fin D) (Fin D) ℂ)) r s
        = c k * ((if k = r ∧ k = s then (1 : ℂ) else 0)
          - (if (0 : Fin D) = r ∧ (0 : Fin D) = s then (1 : ℂ) else 0)) := by
    intro k
    rw [Matrix.smul_apply, Matrix.sub_apply, Matrix.single_apply,
      Matrix.single_apply, smul_eq_mul]
  rw [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.sum_apply,
    Finset.sum_congr rfl (fun k (_ : k ∈ Finset.univ.erase (0 : Fin D)) => hentry k),
    Matrix.diagonal_apply]
  by_cases hrs : r = s
  · subst hrs
    rw [Matrix.one_apply_eq, if_pos rfl, mul_one]
    by_cases hr : r = 0
    · subst hr
      rw [if_pos rfl]
      have hterm : ∀ k ∈ Finset.univ.erase (0 : Fin D),
          c k * ((if k = (0 : Fin D) ∧ k = (0 : Fin D) then (1 : ℂ) else 0)
            - (if (0 : Fin D) = (0 : Fin D) ∧ (0 : Fin D) = (0 : Fin D) then (1 : ℂ) else 0))
          = -c k := by
        intro k hk
        rw [if_neg (fun h => (Finset.ne_of_mem_erase hk) h.1), if_pos ⟨rfl, rfl⟩]
        ring
      rw [Finset.sum_congr rfl hterm, Finset.sum_neg_distrib]
      ring
    · rw [if_neg hr]
      have hterm : ∀ k ∈ Finset.univ.erase (0 : Fin D),
          c k * ((if k = r ∧ k = r then (1 : ℂ) else 0)
            - (if (0 : Fin D) = r ∧ (0 : Fin D) = r then (1 : ℂ) else 0))
          = if k = r then c r else 0 := by
        intro k _
        rw [if_neg (fun h : (0 : Fin D) = r ∧ (0 : Fin D) = r => hr h.1.symm)]
        rcases eq_or_ne k r with h | h
        · subst h
          rw [if_pos ⟨rfl, rfl⟩, if_pos rfl]
          ring
        · rw [if_neg (fun hh => h hh.1), if_neg h]
          ring
      rw [Finset.sum_congr rfl hterm,
        Finset.sum_ite_eq' (Finset.univ.erase (0 : Fin D)) r (fun _ => c r),
        if_pos (Finset.mem_erase.mpr ⟨hr, Finset.mem_univ r⟩)]
  · rw [Matrix.one_apply_ne hrs, if_neg hrs, mul_zero, zero_add]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [if_neg (fun h : k = r ∧ k = s => hrs (h.1.symm.trans h.2)),
      if_neg (fun h : (0 : Fin D) = r ∧ (0 : Fin D) = s => hrs (h.1.symm.trans h.2))]
    ring

/-- Only the diagonal labels contribute to a combination whose coefficients are
supported on the diagonal. -/
theorem sum_quditUnitCoeff_diag (a : Fin D) :
    ∑ p : Fin D × Fin D, quditUnitCoeff a a p • quditHermUnit p
      = ∑ k : Fin D, quditUnitCoeff a a (k, k) • quditHermUnit ((k, k) : Fin D × Fin D) := by
  rw [← Finset.univ_product_univ, Finset.sum_product]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ k)]
  have hz : ∑ j ∈ Finset.univ.erase k,
      quditUnitCoeff a a (k, j) • quditHermUnit ((k, j) : Fin D × Fin D) = 0 :=
    Finset.sum_eq_zero fun j hj => by
      have : (k, j).1 ≠ (k, j).2 := fun h => (Finset.ne_of_mem_erase hj) h.symm
      simp [quditUnitCoeff, this]
  rw [hz, add_zero]

/-- **Change of basis.**  Every matrix unit is the displayed complex combination
of local Hermitian units. -/
theorem single_eq_sum_quditUnitCoeff (a b : Fin D) :
    Matrix.single a b (1 : ℂ)
      = ∑ p : Fin D × Fin D, quditUnitCoeff a b p • quditHermUnit p := by
  have hDne : (D : ℂ) ≠ 0 := by
    have h : (D : ℕ) ≠ 0 := NeZero.ne D
    exact_mod_cast h
  rcases eq_or_ne a b with hab | hab
  · subst hab
    rw [sum_quditUnitCoeff_diag]
    have hc : ∀ k : Fin D, quditUnitCoeff a a (k, k)
        = if k = 0 then (D : ℂ)⁻¹ else ((if k = a then (1 : ℂ) else 0) - (D : ℂ)⁻¹) := by
      intro k
      rcases eq_or_ne k 0 with hk | hk
      · subst hk; simp [quditUnitCoeff]
      · rcases eq_or_ne k a with hka | hka
        · subst hka; simp [quditUnitCoeff, hk]
        · simp [quditUnitCoeff, hk, hka]
    rw [Finset.sum_congr rfl (fun k _ => by rw [hc k]), sum_diag_smul_quditHermUnit]
    have hcard : (Finset.univ.erase (0 : Fin D)).card = D - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
        Fintype.card_fin]
    have hDpos : 1 ≤ D := Nat.one_le_iff_ne_zero.mpr (NeZero.ne D)
    have hcast : ((D - 1 : ℕ) : ℂ) = (D : ℂ) - 1 := by
      rw [Nat.cast_sub hDpos, Nat.cast_one]
    have hT : ∑ k ∈ Finset.univ.erase (0 : Fin D),
          (if k = 0 then (D : ℂ)⁻¹ else ((if k = a then (1 : ℂ) else 0) - (D : ℂ)⁻¹))
        = (if a = 0 then (0 : ℂ) else 1) - ((D : ℂ) - 1) * (D : ℂ)⁻¹ := by
      rw [Finset.sum_congr rfl (fun k hk => by
        rw [if_neg (Finset.ne_of_mem_erase hk)])]
      rw [Finset.sum_sub_distrib, Finset.sum_const, hcard, nsmul_eq_mul, hcast,
        Finset.sum_ite_eq' (Finset.univ.erase (0 : Fin D)) a (fun _ => (1 : ℂ))]
      by_cases ha : a = 0
      · subst ha
        rw [if_neg (by simp), if_pos rfl]
      · rw [if_pos (Finset.mem_erase.mpr ⟨ha, Finset.mem_univ a⟩), if_neg ha]
    rw [hT]
    have hsingle : Matrix.single a a (1 : ℂ)
        = Matrix.diagonal (fun j => if j = a then (1 : ℂ) else 0) := by
      ext r s
      rw [Matrix.single_apply, Matrix.diagonal_apply]
      by_cases h : r = s
      · subst h
        rw [if_pos rfl]
        by_cases h2 : r = a
        · subst h2
          rw [if_pos ⟨rfl, rfl⟩, if_pos rfl]
        · rw [if_neg (fun hh => h2 hh.1.symm), if_neg h2]
      · rw [if_neg h, if_neg (fun hh : a = r ∧ a = s => h (hh.1.symm.trans hh.2))]
    rw [hsingle]
    congr 1
    funext j
    have hc0 : (if ((0 : Fin D) = 0) then (D : ℂ)⁻¹
        else ((if (0 : Fin D) = a then (1 : ℂ) else 0) - (D : ℂ)⁻¹)) = (D : ℂ)⁻¹ :=
      if_pos rfl
    by_cases hj : j = 0
    · subst hj
      rw [if_pos rfl, hc0]
      by_cases ha : a = 0
      · subst ha
        rw [if_pos rfl, if_pos rfl]
        field_simp
        ring
      · rw [if_neg (fun h : (0 : Fin D) = a => ha h.symm), if_neg ha]
        field_simp
        ring
    · rw [if_neg hj, hc0, if_neg hj]
      ring

  · have hne : ((a, b) : Fin D × Fin D) ≠ (b, a) := fun h => hab (congrArg Prod.fst h)
    have hsum : ∑ p : Fin D × Fin D, quditUnitCoeff a b p • quditHermUnit p
        = (if a < b then (1 : ℂ) / 2 else -(Complex.I / 2))
            • quditHermUnit ((a, b) : Fin D × Fin D)
          + (if a < b then Complex.I / 2 else (1 : ℂ) / 2)
            • quditHermUnit ((b, a) : Fin D × Fin D) := by
      have hterm : ∀ p : Fin D × Fin D, quditUnitCoeff a b p • quditHermUnit p
          = (if p = (a, b) then
              (if a < b then (1 : ℂ) / 2 else -(Complex.I / 2))
                • quditHermUnit ((a, b) : Fin D × Fin D)
             else 0)
            + (if p = (b, a) then
              (if a < b then Complex.I / 2 else (1 : ℂ) / 2)
                • quditHermUnit ((b, a) : Fin D × Fin D)
             else 0) := by
        intro p
        rcases eq_or_ne p ((a, b) : Fin D × Fin D) with h1 | h1
        · subst h1
          rw [if_pos rfl, if_neg hne, add_zero]
          simp [quditUnitCoeff, hab]
        · rcases eq_or_ne p ((b, a) : Fin D × Fin D) with h2 | h2
          · subst h2
            rw [if_neg h1, if_pos rfl, zero_add]
            simp [quditUnitCoeff, hab, h1]
          · rw [if_neg h1, if_neg h2, add_zero]
            simp [quditUnitCoeff, hab, h1, h2]
      rw [Finset.sum_congr rfl (fun p _ => hterm p), Finset.sum_add_distrib,
        Finset.sum_ite_eq' Finset.univ ((a, b) : Fin D × Fin D)
          (fun _ => (if a < b then (1 : ℂ) / 2 else -(Complex.I / 2))
            • quditHermUnit ((a, b) : Fin D × Fin D)),
        Finset.sum_ite_eq' Finset.univ ((b, a) : Fin D × Fin D)
          (fun _ => (if a < b then Complex.I / 2 else (1 : ℂ) / 2)
            • quditHermUnit ((b, a) : Fin D × Fin D)),
        if_pos (Finset.mem_univ _), if_pos (Finset.mem_univ _)]
    rw [hsum]
    have hII : (Complex.I / 2) * Complex.I = -(1 / 2 : ℂ) := by
      rw [div_mul_eq_mul_div, Complex.I_mul_I]
      norm_num
    have hII' : (-(Complex.I / 2)) * Complex.I = (1 / 2 : ℂ) := by
      rw [neg_mul, div_mul_eq_mul_div, Complex.I_mul_I]
      norm_num
    rcases lt_or_gt_of_ne hab with hlt | hgt
    · rw [if_pos hlt, if_pos hlt, quditHermUnit_lt hlt, quditHermUnit_gt hlt,
        smul_smul, hII]
      module
    · rw [if_neg (not_lt.mpr (le_of_lt hgt)), if_neg (not_lt.mpr (le_of_lt hgt)),
        quditHermUnit_gt hgt, quditHermUnit_lt hgt, smul_smul, hII']
      module

/-- **The local Hermitian units span the local operator algebra.** -/
theorem span_quditHermUnit_eq_top :
    Submodule.span ℂ (Set.range (quditHermUnit (D := D))) = ⊤ := by
  rw [eq_top_iff]
  rintro M -
  rw [Matrix.matrix_eq_sum_single M]
  refine Submodule.sum_mem _ fun r _ => Submodule.sum_mem _ fun c _ => ?_
  have hs : Matrix.single r c (M r c) = M r c • Matrix.single r c (1 : ℂ) := by
    rw [Matrix.smul_single, smul_eq_mul, mul_one]
  rw [hs, single_eq_sum_quditUnitCoeff]
  refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun p _ => ?_)
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨p, rfl⟩)

/-- **The local Hermitian units are a complex basis of the local operator
algebra.** -/
theorem linearIndependent_quditHermUnit :
    LinearIndependent ℂ (quditHermUnit (D := D)) := by
  refine linearIndependent_of_top_le_span_of_card_eq_finrank ?_ ?_
  · rw [span_quditHermUnit_eq_top]
  · rw [Module.finrank_matrix ℂ ℂ (Fin D) (Fin D), Fintype.card_prod,
      Fintype.card_fin, Module.finrank_self, mul_one]

/-- Coordinates in the local Hermitian unit family are unique. -/
theorem quditHermUnit_coeff_unique {c d : Fin D × Fin D → ℂ}
    (h : ∑ p, c p • quditHermUnit p = ∑ p, d p • quditHermUnit p) : c = d := by
  have hzero : ∑ p, (c p - d p) • quditHermUnit (D := D) p = 0 := by
    rw [Finset.sum_congr rfl (fun p _ => sub_smul (c p) (d p) (quditHermUnit p)),
      Finset.sum_sub_distrib, h, sub_self]
  have hcd := (Fintype.linearIndependent_iff.mp linearIndependent_quditHermUnit)
    (fun p => c p - d p) hzero
  funext p
  exact sub_eq_zero.mp (hcd p)

omit [NeZero D] in
/-- An off-diagonal matrix unit is traceless. -/
theorem trace_single_of_ne {i j : Fin D} (hij : i ≠ j) :
    (Matrix.single i j (1 : ℂ)).trace = 0 := by
  rw [Matrix.trace]
  refine Finset.sum_eq_zero fun x _ => ?_
  rw [Matrix.diag_apply, Matrix.single_apply,
    if_neg (fun h => hij (h.1.trans h.2.symm))]

/-- The trace of a local Hermitian unit: the identity label carries the local
dimension, every other label is traceless. -/
theorem trace_quditHermUnit (p : Fin D × Fin D) :
    (quditHermUnit p).trace = if p = (0, 0) then (D : ℂ) else 0 := by
  rcases eq_or_ne p.1 p.2 with hd | hd
  · rcases eq_or_ne p.1 0 with h0 | h0
    · have hp : p = (0, 0) := Prod.ext h0 (hd ▸ h0)
      rw [hp, quditHermUnit_zero, if_pos rfl, Matrix.trace_one]
      simp
    · have hp : p = (p.1, p.1) := Prod.ext rfl hd.symm
      rw [hp, quditHermUnit_diag_of_ne_zero h0,
        if_neg (fun h => h0 (congrArg Prod.fst h)), Matrix.trace_sub]
      simp
  · have hne : p ≠ (0, 0) := by
      intro h
      exact hd (by rw [h])
    rcases lt_or_gt_of_ne hd with hlt | hgt
    · rw [show p = (p.1, p.2) from rfl, quditHermUnit_lt hlt, if_neg hne,
        Matrix.trace_add, trace_single_of_ne hd, trace_single_of_ne (Ne.symm hd),
        add_zero]
    · rw [show p = (p.1, p.2) from rfl, quditHermUnit_gt hgt, if_neg hne,
        Matrix.trace_smul, Matrix.trace_sub, trace_single_of_ne hd,
        trace_single_of_ne (Ne.symm hd), sub_zero, smul_zero]

/-- A Hermitian matrix has real coordinates in the local Hermitian unit
family. -/
theorem exists_real_repr_of_conjTranspose_eq {M : Matrix (Fin D) (Fin D) ℂ}
    (hM : Mᴴ = M) :
    ∃ c : Fin D × Fin D → ℝ, M = ∑ p, ((c p : ℂ)) • quditHermUnit p := by
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp
    (by rw [span_quditHermUnit_eq_top]; trivial :
      M ∈ Submodule.span ℂ (Set.range (quditHermUnit (D := D))))
  have h1 : (∑ p, a p • quditHermUnit (D := D) p)ᴴ
      = ∑ p, (starRingEnd ℂ (a p)) • quditHermUnit p := by
    rw [Matrix.conjTranspose_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Matrix.conjTranspose_smul, quditHermUnit_conjTranspose]
    rfl
  have hconj : ∑ p, (starRingEnd ℂ (a p)) • quditHermUnit (D := D) p
      = ∑ p, a p • quditHermUnit p := by
    rw [← h1, ha]
    exact hM
  have hreal := quditHermUnit_coeff_unique hconj
  refine ⟨fun p => (a p).re, ?_⟩
  rw [← ha]
  refine Finset.sum_congr rfl fun p _ => ?_
  congr 1
  exact (Complex.conj_eq_iff_re.mp (congrFun hreal p)).symm

/-- A traceless Hermitian matrix has real coordinates vanishing at the identity
label. -/
theorem exists_real_repr_ground_zero_of_traceless {M : Matrix (Fin D) (Fin D) ℂ}
    (hM : Mᴴ = M) (htr : M.trace = 0) :
    ∃ c : Fin D × Fin D → ℝ, c (0, 0) = 0
      ∧ M = ∑ p, ((c p : ℂ)) • quditHermUnit p := by
  obtain ⟨c, hc⟩ := exists_real_repr_of_conjTranspose_eq hM
  have hDne : (D : ℂ) ≠ 0 := by
    have h : (D : ℕ) ≠ 0 := NeZero.ne D
    exact_mod_cast h
  have htr' : ((c (0, 0) : ℂ)) * (D : ℂ) = 0 := by
    have hsum := htr
    rw [hc, Matrix.trace_sum] at hsum
    rw [Finset.sum_congr rfl (fun p (_ : p ∈ Finset.univ) => by
      rw [Matrix.trace_smul, trace_quditHermUnit p, smul_eq_mul])] at hsum
    rw [Finset.sum_eq_single ((0, 0) : Fin D × Fin D)
      (fun b _ hb => by rw [if_neg hb, mul_zero])
      (fun h => absurd (Finset.mem_univ _) h), if_pos rfl] at hsum
    exact hsum
  refine ⟨c, ?_, hc⟩
  rcases mul_eq_zero.mp htr' with h | h
  · exact_mod_cast h
  · exact absurd h hDne

/-- A traceless Hermitian matrix lies in the real span of the non-identity local
Hermitian units. -/
theorem mem_span_real_nonIdentity_of_traceless {M : Matrix (Fin D) (Fin D) ℂ}
    (hM : Mᴴ = M) (htr : M.trace = 0) :
    M ∈ Submodule.span ℝ (quditHermUnit (D := D) '' {p | p ≠ (0, 0)}) := by
  obtain ⟨c, hc0, hc⟩ := exists_real_repr_ground_zero_of_traceless hM htr
  rw [hc, ← Finset.add_sum_erase _ _ (Finset.mem_univ ((0, 0) : Fin D × Fin D)),
    hc0]
  simp only [Complex.ofReal_zero, zero_smul, zero_add]
  refine Submodule.sum_mem _ fun p hp => ?_
  have hmem : quditHermUnit p ∈ quditHermUnit (D := D) '' {p | p ≠ (0, 0)} :=
    ⟨p, Finset.ne_of_mem_erase hp, rfl⟩
  have hsm : ((c p : ℂ)) • quditHermUnit p = c p • quditHermUnit (D := D) p := by
    rw [Complex.coe_smul]
  rw [hsm]
  exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)

end GaloisForLFunctions.HTGeometry
