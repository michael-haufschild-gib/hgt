import GaloisForLFunctions.RHTower.DeningerHazewinkelCorrectedRationalStage
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Deninger's field-valued Kronecker theorem

This file proves the field step needed to compare Hazewinkel's determinantal
filtration with the rational-Witt filtration.  A finite-rank Hankel matrix first
produces a minimal forward recurrence.  The recurrence produces a normalized
fraction `P / Q`, with the sharp stage bounds on the numerator and denominator.

Combining this converse with rational-Witt multiplication proves the corrected
field-valued multiplicative bound.  The argument is symbolic and works over an
arbitrary field; it uses neither root extraction nor a cardinality assumption.
-/

namespace RHTower
noncomputable section
open scoped BigOperators

/-- A linearly independent finite family of functions admits a nonsingular
finite evaluation matrix. -/
theorem exists_evaluation_minor_ne_zero_of_linearIndependent
    {K ι : Type*} [Field K] {n : ℕ}
    (v : Fin n → ι → K) (hv : LinearIndependent K v) :
    ∃ rows : Fin n → ι,
      Matrix.det (fun i j => v j (rows i)) ≠ 0 := by
  induction n with
  | zero =>
      exact ⟨Fin.elim0, by simp⟩
  | succ n ih =>
      let vold : Fin n → ι → K := Fin.init v
      have hvold : LinearIndependent K vold :=
        (linearIndependent_finSucc'.mp hv).1
      obtain ⟨rows, hM⟩ := ih vold hvold
      let M : Matrix (Fin n) (Fin n) K := fun i j => vold j (rows i)
      let b : Fin n → K := fun i => v (Fin.last n) (rows i)
      let c : Fin n → K := (M⁻¹).mulVec b
      have hMunit : IsUnit M.det := isUnit_iff_ne_zero.mpr hM
      have hsolve : M.mulVec c = b := by
        change M.mulVec ((M⁻¹).mulVec b) = b
        rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv M hMunit,
          Matrix.one_mulVec]
      let residual : ι → K := fun i =>
        v (Fin.last n) i - ∑ j : Fin n, c j * vold j i
      have hres : ∃ i : ι, residual i ≠ 0 := by
        by_contra h
        push Not at h
        have heq : v (Fin.last n) = ∑ j : Fin n, c j • vold j := by
          funext i
          have hi := h i
          simp only [residual, sub_eq_zero] at hi
          simpa [Finset.sum_apply, smul_eq_mul] using hi
        have hmem : v (Fin.last n) ∈ Submodule.span K (Set.range vold) := by
          rw [heq]
          exact Submodule.sum_mem _ fun j _ =>
            Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
        exact (linearIndependent_finSucc'.mp hv).2 hmem
      obtain ⟨i0, hi0⟩ := hres
      let rows' : Fin (n + 1) → ι := Fin.cons i0 rows
      let A : Matrix (Fin (n + 1)) (Fin (n + 1)) K :=
        fun i j => v j (rows' i)
      let E : Matrix (Fin (n + 1)) (Fin (n + 1)) K := fun k l =>
        Fin.cases (Fin.lastCases 1 (fun j => -c j) k)
          (fun j => if k = j.castSucc then 1 else 0) l
      let C : Matrix (Fin (n + 1)) (Fin (n + 1)) K := fun i l =>
        Fin.cases (residual (rows' i)) (fun j => vold j (rows' i)) l
      have hvold_apply (j : Fin n) (i : ι) : vold j i = v j.castSucc i := rfl
      have hresRows : ∀ i : Fin n, residual (rows i) = 0 := by
        intro i
        have hi := congrFun hsolve i
        change (∑ j : Fin n, M i j * c j) = b i at hi
        change v (Fin.last n) (rows i) -
          ∑ j : Fin n, c j * vold j (rows i) = 0
        rw [show (∑ j : Fin n, c j * vold j (rows i)) =
            ∑ j : Fin n, M i j * c j by
          apply Finset.sum_congr rfl
          intro j hj
          simp [M, mul_comm]]
        exact sub_eq_zero.mpr hi.symm
      have hCE : C = A * E := by
        ext i l
        cases l using Fin.cases with
        | zero =>
            rw [Matrix.mul_apply, Fin.sum_univ_castSucc]
            simp only [E, Fin.cases_zero, Fin.lastCases_last,
              Fin.lastCases_castSucc, mul_one]
            change residual (rows' i) =
              (∑ x : Fin n, A i x.castSucc * -c x) + A i (Fin.last n)
            change v (Fin.last n) (rows' i) -
                ∑ x : Fin n, c x * vold x (rows' i) =
              (∑ x : Fin n, v x.castSucc (rows' i) * -c x) +
                v (Fin.last n) (rows' i)
            have hsum :
                (∑ x : Fin n, v x.castSucc (rows' i) * -c x) =
                  -(∑ x : Fin n, c x * vold x (rows' i)) := by
              rw [← Finset.sum_neg_distrib]
              apply Finset.sum_congr rfl
              intro x hx
              rw [hvold_apply]
              ring
            rw [hsum]
            ring
        | succ j =>
            rw [Matrix.mul_apply]
            simp [E, C, A]
            exact hvold_apply j (rows' i)
      have hCdet : C.det ≠ 0 := by
        rw [Matrix.det_succ_column_zero]
        simp only [C, Fin.cases_zero, rows']
        rw [Fin.sum_univ_succ]
        simp only [Fin.val_zero, pow_zero, one_mul]
        have hminor :
            (C.submatrix (0 : Fin (n + 1)).succAbove Fin.succ) = M := by
          ext i j
          simp [C, M, rows', vold]
        rw [hminor]
        simp only [Fin.val_succ, Fin.cons_succ, hresRows,
          mul_zero, zero_mul, Finset.sum_const_zero, add_zero]
        exact mul_ne_zero hi0 hM
      refine ⟨rows', ?_⟩
      change A.det ≠ 0
      intro hA
      apply hCdet
      rw [hCE, Matrix.det_mul, hA, zero_mul]

/-- A positive-order forward recurrence for a field-valued sequence. -/
structure DeningerFieldHankelRecurrence
    {K : Type*} [Field K] (a : ℕ → K) (n : ℕ) where
  order : ℕ
  order_pos : 0 < order
  order_le : order ≤ n
  coeff : Fin order → K
  recurrence : ∀ i : ℕ,
    a (i + order) = ∑ j : Fin order, coeff j * a (i + j.val)

/-- Vanishing `(n+1)`-minors and constant coefficient one produce a recurrence
of positive order at most `n`. -/
noncomputable def deningerFieldHankelRecurrence_of_rankLT
    {K : Type*} [Field K] (a : ℕ → K) (n : ℕ)
    (ha0 : a 0 = 1)
    (hrank : ∀ rows cols : Fin (n + 1) → ℕ,
      (Matrix.submatrix (fun i j => a (i + j)) rows cols).det = 0) :
    DeningerFieldHankelRecurrence a n := by
  classical
  let col : ℕ → ℕ → K := fun j i => a (i + j)
  have hdep : ¬ LinearIndependent K (fun j : Fin (n + 1) => col j.val) := by
    intro hli
    obtain ⟨rows, hdet⟩ :=
      exists_evaluation_minor_ne_zero_of_linearIndependent
        (fun j : Fin (n + 1) => col j.val) hli
    apply hdet
    have heq : (fun i j => col j.val (rows i)) =
        Matrix.submatrix (fun i j => a (i + j)) rows
          (fun j : Fin (n + 1) => j.val) := by
      ext i j
      rfl
    rw [heq]
    exact hrank rows (fun j : Fin (n + 1) => j.val)
  let P : ℕ → Prop := fun d => d ≤ n ∧
    ¬ LinearIndependent K (fun j : Fin (d + 1) => col j.val)
  have hP : ∃ d : ℕ, P d := ⟨n, le_rfl, hdep⟩
  let d := Nat.find hP
  have hdP : P d := Nat.find_spec hP
  have hzeroLI : LinearIndependent K (fun j : Fin 1 => col j.val) := by
    rw [linearIndependent_unique_iff]
    intro hzero
    have hz := congrFun hzero 0
    simp [col, ha0] at hz
  have hdpos : 0 < d := by
    by_contra hd
    have hd0 : d = 0 := Nat.eq_zero_of_not_pos hd
    have hP0 : P 0 := hd0 ▸ hdP
    exact hP0.2 hzeroLI
  let e := d - 1
  have hde : d = e + 1 := by omega
  have hed : e < d := by omega
  have hePnot : ¬ P e := Nat.find_min hP hed
  have heLI : LinearIndependent K (fun j : Fin (e + 1) => col j.val) := by
    by_contra h
    exact hePnot ⟨by omega, h⟩
  have hdLI : LinearIndependent K (fun j : Fin d => col j.val) := by
    have hcomp := heLI.comp (Fin.cast hde) (Fin.cast_injective hde)
    simpa [Function.comp_def] using hcomp
  have hinitLI : LinearIndependent K
      (Fin.init (fun j : Fin (d + 1) => col j.val)) := by
    have heq : Fin.init (fun j : Fin (d + 1) => col j.val) =
        (fun j : Fin d => col j.val) := by
      funext j
      rfl
    rw [heq]
    exact hdLI
  have hlastMem : col d ∈
      Submodule.span K (Set.range
        (Fin.init (fun j : Fin (d + 1) => col j.val))) := by
    by_contra hnot
    exact hdP.2 (linearIndependent_finSucc'.mpr ⟨hinitLI, by simpa using hnot⟩)
  let hex := (Submodule.mem_span_range_iff_exists_fun K).mp hlastMem
  let c := Classical.choose hex
  have hc := Classical.choose_spec hex
  refine ⟨d, hdpos, hdP.1, c, ?_⟩
  intro i
  change (∑ j : Fin d, c j •
      Fin.init (fun j : Fin (d + 1) => col j.val) j) = col d at hc
  have hi := congrFun hc i
  have hi' : a (i + d) = ∑ j : Fin d,
      c j * (Fin.init (fun j : Fin (d + 1) => col j.val) j) i := by
    simpa [Finset.sum_apply, smul_eq_mul, col] using hi.symm
  calc
    a (i + d) = ∑ j : Fin d,
        c j * (Fin.init (fun j : Fin (d + 1) => col j.val) j) i := hi'
    _ = ∑ j : Fin d, c j * a (i + j.val) := by
      apply Finset.sum_congr rfl
      intro j hj
      rfl

/-- Recurrence denominator, normalized to have constant coefficient one. -/
def DeningerFieldHankelRecurrence.denominator
    {K : Type*} [Field K] {a : ℕ → K} {n : ℕ}
    (r : DeningerFieldHankelRecurrence a n) : Polynomial K :=
  1 - ∑ j : Fin r.order,
    Polynomial.C (r.coeff j) * Polynomial.X ^ (r.order - j.val)

@[simp] theorem DeningerFieldHankelRecurrence.denominator_coeff_zero
    {K : Type*} [Field K] {a : ℕ → K} {n : ℕ}
    (r : DeningerFieldHankelRecurrence a n) :
    r.denominator.coeff 0 = 1 := by
  rw [DeningerFieldHankelRecurrence.denominator, Polynomial.coeff_sub]
  simp only [Polynomial.coeff_one_zero]
  simp
  apply Finset.sum_eq_zero
  intro j hj
  rw [if_neg]
  omega

theorem DeningerFieldHankelRecurrence.denominator_natDegree_le
    {K : Type*} [Field K] {a : ℕ → K} {n : ℕ}
    (r : DeningerFieldHankelRecurrence a n) :
    r.denominator.natDegree ≤ r.order := by
  rw [DeningerFieldHankelRecurrence.denominator]
  have hsum : (∑ j : Fin r.order,
      Polynomial.C (r.coeff j) * Polynomial.X ^ (r.order - j.val)).natDegree ≤
      r.order := by
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro j hj
    refine Polynomial.natDegree_mul_le.trans ?_
    simp
  exact (Polynomial.natDegree_sub_le _ _).trans (max_le (by simp) hsum)

theorem DeningerFieldHankelRecurrence.coeff_denominator_mul_eq_zero
    {K : Type*} [Field K] {a : ℕ → K} {n : ℕ}
    (r : DeningerFieldHankelRecurrence a n) (F : PowerSeries K)
    (hF : ∀ i : ℕ, PowerSeries.coeff i F = a i)
    (N : ℕ) (hN : r.order ≤ N) :
    PowerSeries.coeff N ((r.denominator : PowerSeries K) * F) = 0 := by
  rw [DeningerFieldHankelRecurrence.denominator]
  push_cast
  rw [sub_mul, one_mul]
  have hcoe :
      ((↑(∑ j : Fin r.order,
          Polynomial.C (r.coeff j) * Polynomial.X ^ (r.order - j.val)) :
          Polynomial K) : PowerSeries K) =
        ∑ j : Fin r.order,
          ((Polynomial.C (r.coeff j) * Polynomial.X ^ (r.order - j.val) :
            Polynomial K) : PowerSeries K) := by
    simpa only [Polynomial.coeToPowerSeries.ringHom_apply] using
      map_sum (Polynomial.coeToPowerSeries.ringHom (R := K))
        (fun j : Fin r.order =>
          Polynomial.C (r.coeff j) * Polynomial.X ^ (r.order - j.val)) Finset.univ
  rw [hcoe, Finset.sum_mul, map_sub, map_sum]
  rw [hF]
  have hterm : ∀ j : Fin r.order,
      PowerSeries.coeff N
        (PowerSeries.C (r.coeff j) *
          (PowerSeries.X ^ (r.order - j.val) * F)) =
        r.coeff j * a (N - r.order + j.val) := by
    intro j
    rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul', if_pos]
    · rw [hF]
      congr 2
      omega
    · omega
  simp only [Polynomial.coe_mul, Polynomial.coe_C, Polynomial.coe_pow,
    Polynomial.coe_X, mul_assoc]
  simp_rw [hterm]
  have hrec := r.recurrence (N - r.order)
  rw [Nat.sub_add_cancel hN] at hrec
  exact sub_eq_zero.mpr hrec

/-- Numerator obtained by truncating the recurrence-corrected series. -/
def DeningerFieldHankelRecurrence.numerator
    {K : Type*} [Field K] {a : ℕ → K} {n : ℕ}
    (r : DeningerFieldHankelRecurrence a n) (F : PowerSeries K) : Polynomial K :=
  PowerSeries.trunc r.order ((r.denominator : PowerSeries K) * F)

@[simp] theorem DeningerFieldHankelRecurrence.numerator_coeff_zero
    {K : Type*} [Field K] {a : ℕ → K} {n : ℕ}
    (r : DeningerFieldHankelRecurrence a n) (F : PowerSeries K)
    (hF0 : PowerSeries.coeff 0 F = 1) :
    (r.numerator F).coeff 0 = 1 := by
  rw [DeningerFieldHankelRecurrence.numerator, PowerSeries.coeff_trunc,
    if_pos r.order_pos]
  rw [PowerSeries.coeff_mul]
  simp [Polynomial.coeff_coe, hF0, r.denominator_coeff_zero]

theorem DeningerFieldHankelRecurrence.numerator_natDegree_add_one_le
    {K : Type*} [Field K] {a : ℕ → K} {n : ℕ}
    (r : DeningerFieldHankelRecurrence a n) (F : PowerSeries K) :
    (r.numerator F).natDegree + 1 ≤ r.order := by
  have h := PowerSeries.natDegree_trunc_lt
    ((r.denominator : PowerSeries K) * F) (r.order - 1)
  rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt r.order_pos))] at h
  exact h

theorem DeningerFieldHankelRecurrence.denominator_mul_eq_numerator
    {K : Type*} [Field K] {a : ℕ → K} {n : ℕ}
    (r : DeningerFieldHankelRecurrence a n) (F : PowerSeries K)
    (hF : ∀ i : ℕ, PowerSeries.coeff i F = a i) :
    (r.denominator : PowerSeries K) * F = (r.numerator F : PowerSeries K) := by
  apply PowerSeries.ext
  intro N
  by_cases hN : N < r.order
  · rw [Polynomial.coeff_coe, DeningerFieldHankelRecurrence.numerator,
      PowerSeries.coeff_trunc, if_pos hN]
  · rw [r.coeff_denominator_mul_eq_zero F hF N (Nat.le_of_not_gt hN)]
    rw [Polynomial.coeff_coe, DeningerFieldHankelRecurrence.numerator,
      PowerSeries.coeff_trunc, if_neg hN]

theorem DeningerFieldHankelRecurrence.mul_denominator_eq_numerator
    {K : Type*} [Field K] {a : ℕ → K} {n : ℕ}
    (r : DeningerFieldHankelRecurrence a n) (F : PowerSeries K)
    (hF : ∀ i : ℕ, PowerSeries.coeff i F = a i) :
    F * (r.denominator : PowerSeries K) = (r.numerator F : PowerSeries K) := by
  rw [mul_comm]
  exact r.denominator_mul_eq_numerator F hF

/-- Field-valued Kronecker theorem with Deninger's stage convention: vanishing
Hankel minors of size `n+1` is equivalent to a normalized rational Witt
presentation of stage at most `n`. -/
theorem deningerField_hankelRankLT_iff_exists_rationalWittStage
    {K : Type*} [Field K] (n : ℕ) (w : DeningerBigWittAdditive K) :
    DeningerBigWittHankelRankLT (n + 1) w ↔
      ∃ x : DeningerCanonicalRationalWittRing K,
        DeningerCanonicalRationalWittStageLE n x ∧
          deningerCanonicalRationalWittBigWittCarrier x = w := by
  constructor
  · intro hrank
    let F := deningerBigWittSeries w
    let a : ℕ → K := fun i => PowerSeries.coeff i F
    have ha0 : a 0 = 1 := by
      simpa [a, F, PowerSeries.constantCoeff] using
        deningerBigWittSeries_constantCoeff w
    let r : DeningerFieldHankelRecurrence a n :=
      deningerFieldHankelRecurrence_of_rankLT a n ha0 (by
        intro rows cols
        have h := hrank rows cols
        change (Matrix.submatrix
          (fun i j => PowerSeries.coeff (i + j) F) rows cols).det = 0 at h
        exact h)
    let P := r.numerator F
    let Q := r.denominator
    have hP0 : P.coeff 0 = 1 := by
      apply r.numerator_coeff_zero
      exact ha0
    have hQ0 : Q.coeff 0 = 1 := r.denominator_coeff_zero
    have hPdeg : P.natDegree + 1 ≤ n :=
      (r.numerator_natDegree_add_one_le F).trans r.order_le
    have hQdeg : Q.natDegree ≤ n :=
      r.denominator_natDegree_le.trans r.order_le
    have hFcoeff : ∀ i : ℕ, PowerSeries.coeff i F = a i := fun _ => rfl
    have hFQ : F * (Q : PowerSeries K) = (P : PowerSeries K) :=
      r.mul_denominator_eq_numerator F hFcoeff
    let x : DeningerCanonicalRationalWittRing K :=
      ⟨Additive.ofMul (deningerRationalWittNormalizedFraction P Q hP0 hQ0)⟩
    have hGQ :=
      deningerRationalWittNormalizedFraction_powerSeries_mul_denominator P Q hP0 hQ0
    let G := deningerBigWittSeries
      (deningerRationalWittToBigWittAdditive K
        (deningerRationalWittNormalizedFraction P Q hP0 hQ0))
    have hGQ' : G * (Q : PowerSeries K) = (P : PowerSeries K) := by
      exact hGQ
    have hQunit : IsUnit (Q : PowerSeries K) := by
      rw [PowerSeries.isUnit_iff_constantCoeff]
      simp [hQ0]
    have hFG : F = G := hQunit.mul_right_cancel (hFQ.trans hGQ'.symm)
    have hxcarrier : deningerCanonicalRationalWittBigWittCarrier x = w := by
      change deningerRationalWittToBigWittAdditive K
        (deningerRationalWittNormalizedFraction P Q hP0 hQ0) = w
      apply Subtype.ext
      apply Units.ext
      exact hFG.symm
    exact ⟨x, ⟨P, Q, hP0, hQ0, hPdeg, hQdeg, rfl⟩, hxcarrier⟩
  · rintro ⟨x, hx, rfl⟩
    exact hx.hankelRankLT

@[simp] theorem deningerCanonicalRationalWittBigWittCarrier_mul
    {A : Type*} [CommRing A]
    (x y : DeningerCanonicalRationalWittRing A) :
    deningerCanonicalRationalWittBigWittCarrier (x * y) =
      deningerBigWittMul
        (deningerCanonicalRationalWittBigWittCarrier x)
        (deningerCanonicalRationalWittBigWittCarrier y) := by
  change Additive.toMul
      (deningerCanonicalRationalWittEmbedding (x * y)).additiveVal = _
  rw [map_mul]
  rfl

/-- Corrected field-valued multiplicative closure for Hazewinkel's Hankel
filtration.  The output bound comes from the exact rational-Witt resultant
degrees, not the false additive stage bound. -/
theorem deningerField_hankelRankLT_mul_corrected
    {K : Type*} [Field K] {n m : ℕ}
    {u v : DeningerBigWittAdditive K}
    (hu : DeningerBigWittHankelRankLT (n + 1) u)
    (hv : DeningerBigWittHankelRankLT (m + 1) v) :
    DeningerBigWittHankelRankLT
      (deningerCorrectedWittMulStageBound n m + 1)
      (deningerBigWittMul u v) := by
  obtain ⟨x, hx, hxu⟩ :=
    (deningerField_hankelRankLT_iff_exists_rationalWittStage n u).mp hu
  obtain ⟨y, hy, hyv⟩ :=
    (deningerField_hankelRankLT_iff_exists_rationalWittStage m v).mp hv
  rw [← hxu, ← hyv, ← deningerCanonicalRationalWittBigWittCarrier_mul]
  exact (hx.mul hy).hankelRankLT

end
end RHTower
