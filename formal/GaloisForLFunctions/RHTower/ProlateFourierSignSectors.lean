import GaloisForLFunctions.RHTower.HermiteEvenCarrier
import GaloisForLFunctions.RHTower.ConstrainedProlateSignedSpectrum
import GaloisForLFunctions.HTGeometry.GreedyCourantFischer
import Mathlib.Analysis.InnerProductSpace.StarOrder

/-!
# Positive and negative spectral sectors of the even prolate Fourier block

The concentration spectrum forgets the sign of the compressed Fourier eigenvalues.  This file
recovers genuine sign information without assuming classical prolate numbering.

First, C-star spectral order and the compact Fredholm alternative give an abstract bridge: a
strictly negative quadratic witness for a compact self-adjoint operator forces a negative
eigenvalue, and completeness of the signed greedy exhaustion forces that eigenvalue to occur as
one of its signed values.  Applying the bridge to the `4j+2` Hermite sector and to the `4j`
sector proves that the actual even prolate block has both negative and positive signed values at
every sufficiently large aperture.
-/

open Filter
open scoped InnerProduct InnerProductSpace

noncomputable section

namespace ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- If `x` is closer to a `-1` eigenvector than to zero, its quadratic value is negative. -/
theorem re_inner_neg_of_norm_add_lt_norm (S : H →L[ℂ] H) (x : H)
    (h : ‖x + S x‖ < ‖x‖) : RCLike.re (inner ℂ (S x) x) < 0 := by
  have hxpos : 0 < ‖x‖ := lt_of_le_of_lt (norm_nonneg (x + S x)) h
  have hre : RCLike.re (inner ℂ (x + S x) x) ≤ ‖x + S x‖ * ‖x‖ :=
    (RCLike.re_le_norm _).trans (norm_inner_le_norm _ _)
  have hmul : ‖x + S x‖ * ‖x‖ < ‖x‖ ^ (2 : ℕ) := by
    calc
      ‖x + S x‖ * ‖x‖ < ‖x‖ * ‖x‖ := mul_lt_mul_of_pos_right h hxpos
      _ = ‖x‖ ^ (2 : ℕ) := by ring
  have hform : RCLike.re (inner ℂ (S x) x) =
      RCLike.re (inner ℂ (x + S x) x) - ‖x‖ ^ (2 : ℕ) := by
    have hS : S x = (x + S x) - x := by abel
    calc
      RCLike.re (inner ℂ (S x) x) =
          RCLike.re (inner ℂ ((x + S x) - x) x) :=
        congrArg (fun y : H => RCLike.re (inner ℂ y x)) hS
      _ = RCLike.re (inner ℂ (x + S x) x) - ‖x‖ ^ (2 : ℕ) := by
        rw [inner_sub_left, map_sub, inner_self_eq_norm_sq_to_K]
        rw [RCLike.re_ofReal_pow]
  rw [hform]
  linarith

variable [CompleteSpace H]

/-- A negative quadratic witness for a compact self-adjoint operator produces a genuine negative
real eigenpair. -/
theorem exists_negative_eigenpair_of_re_inner_neg {S : H →L[ℂ] H}
    (hcpt : IsCompactOperator S) (hsym : S.IsSymmetric) {x : H}
    (hx : RCLike.re (inner ℂ (S x) x) < 0) :
    ∃ (c : ℝ) (v : H), c < 0 ∧ v ≠ 0 ∧ S v = (c : ℂ) • v := by
  have hself : IsSelfAdjoint S := isSelfAdjoint_iff_isSymmetric.mpr hsym
  have hnotnonneg : ¬ (0 : H →L[ℂ] H) ≤ S := by
    intro hnonneg
    have hpos : S.IsPositive := (nonneg_iff_isPositive S).mp hnonneg
    exact (not_lt_of_ge (hpos.re_inner_nonneg_left x)) hx
  have hnotall : ¬ ∀ c ∈ spectrum ℝ S, 0 ≤ c := by
    intro hall
    exact hnotnonneg ((StarOrderedRing.nonneg_iff_spectrum_nonneg S hself).mpr hall)
  push Not at hnotall
  obtain ⟨c, hcspec, hcneg⟩ := hnotall
  have hc0 : ((c : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_lt hcneg)
  have hcspecComplex : ((c : ℝ) : ℂ) ∈ spectrum ℂ S :=
    spectrum.algebraMap_mem ℂ hcspec
  have heigenvalue : Module.End.HasEigenvalue (S : Module.End ℂ H) (c : ℂ) :=
    (IsCompactOperator.hasEigenvalue_iff_mem_spectrum hcpt hc0).mpr hcspecComplex
  obtain ⟨v, hv⟩ := heigenvalue.exists_hasEigenvector
  exact ⟨c, v, hcneg, hv.2, hv.apply_eq_smul⟩

/-- A positive quadratic witness for a compact self-adjoint operator produces a genuine positive
real eigenpair. -/
theorem exists_positive_eigenpair_of_re_inner_pos {S : H →L[ℂ] H}
    (hcpt : IsCompactOperator S) (hsym : S.IsSymmetric) {x : H}
    (hx : 0 < RCLike.re (inner ℂ (S x) x)) :
    ∃ (c : ℝ) (v : H), 0 < c ∧ v ≠ 0 ∧ S v = (c : ℂ) • v := by
  have hneg : RCLike.re (inner ℂ ((-S) x) x) < 0 := by
    simpa using (neg_lt_zero.mpr hx)
  have hsymneg : (-S).IsSymmetric := by
    intro u v
    change inner ℂ (-(S u)) v = inner ℂ u (-(S v))
    rw [inner_neg_left, inner_neg_right]
    exact congrArg Neg.neg (hsym u v)
  obtain ⟨c, v, hcneg, hv0, hv⟩ :=
    exists_negative_eigenpair_of_re_inner_neg hcpt.neg hsymneg hneg
  refine ⟨-c, v, neg_pos.mpr hcneg, hv0, ?_⟩
  simpa [neg_smul] using congrArg Neg.neg hv

/-- Negative quadratic form forces a negative member of the complete signed-greedy spectrum. -/
theorem exists_sgVal_neg_of_re_inner_neg {S : H →L[ℂ] H}
    (hcpt : IsCompactOperator S) (hsym : S.IsSymmetric) {x : H}
    (hx : RCLike.re (inner ℂ (S x) x) < 0) :
    ∃ n : ℕ, sgVal S n < 0 := by
  obtain ⟨c, v, hcneg, hv0, hv⟩ :=
    exists_negative_eigenpair_of_re_inner_neg hcpt hsym hx
  have hc0 : ((c : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_lt hcneg)
  obtain ⟨n, hn⟩ := exists_sgVal_eq_of_eigenvalue hcpt hsym hv0 hv hc0
  refine ⟨n, ?_⟩
  have hnreal : sgVal S n = c := by exact_mod_cast hn
  rwa [hnreal]

/-- Positive quadratic form forces a positive member of the complete signed-greedy spectrum. -/
theorem exists_sgVal_pos_of_re_inner_pos {S : H →L[ℂ] H}
    (hcpt : IsCompactOperator S) (hsym : S.IsSymmetric) {x : H}
    (hx : 0 < RCLike.re (inner ℂ (S x) x)) :
    ∃ n : ℕ, 0 < sgVal S n := by
  have hneg : RCLike.re (inner ℂ ((-S) x) x) < 0 := by
    simpa using (neg_lt_zero.mpr hx)
  have hsymneg : (-S).IsSymmetric := by
    intro u v
    change inner ℂ (-(S u)) v = inner ℂ u (-(S v))
    rw [inner_neg_left, inner_neg_right]
    exact congrArg Neg.neg (hsym u v)
  obtain ⟨c, v, hcneg, hv0, hv⟩ :=
    exists_negative_eigenpair_of_re_inner_neg hcpt.neg hsymneg hneg
  have hpos : 0 < -c := neg_pos.mpr hcneg
  have hv' : S v = ((-c : ℝ) : ℂ) • v := by
    simpa [neg_smul] using congrArg Neg.neg hv
  have hc0 : (((-c : ℝ) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt hpos)
  obtain ⟨n, hn⟩ := exists_sgVal_eq_of_eigenvalue hcpt hsym hv0 hv' hc0
  refine ⟨n, ?_⟩
  have hnreal : sgVal S n = -c := by exact_mod_cast hn
  rwa [hnreal]

/-- Multiplicity-sensitive spectral exhaustion: a nonzero eigenvector has a nonzero coefficient
against some signed-greedy vector carrying the same eigenvalue. -/
theorem exists_sgVal_eq_of_eigenvalue_and_inner_ne_zero {S : H →L[ℂ] H}
    (hcpt : IsCompactOperator S) (hsym : S.IsSymmetric) {c : ℂ} {v : H}
    (hv : v ≠ 0) (heig : S v = c • v) (hc : c ≠ 0) :
    ∃ n, ((sgVal S n : ℝ) : ℂ) = c ∧ inner ℂ (sgVec S n) v ≠ 0 := by
  by_contra hall
  have horth : ∀ n, inner ℂ (sgVec S n) v = 0 := by
    intro n
    by_contra hn
    apply hall
    refine ⟨n, ?_, hn⟩
    have h1 : inner ℂ (sgVec S n) (S v) = c * inner ℂ (sgVec S n) v := by
      rw [heig, inner_smul_right]
    have h2 : inner ℂ (sgVec S n) (S v) =
        ((sgVal S n : ℝ) : ℂ) * inner ℂ (sgVec S n) v := by
      calc
        inner ℂ (sgVec S n) (S v) = inner ℂ (S (sgVec S n)) v :=
          (hsym (sgVec S n) v).symm
        _ = inner ℂ (((sgVal S n : ℝ) : ℂ) • sgVec S n) v := by
          rw [apply_sgVec]
        _ = ((sgVal S n : ℝ) : ℂ) * inner ℂ (sgVec S n) v := by
          rw [inner_smul_left]
          congr 1
          simp
    have h3 : (c - ((sgVal S n : ℝ) : ℂ)) * inner ℂ (sgVec S n) v = 0 := by
      rw [sub_mul, ← h1, ← h2, sub_self]
    rcases mul_eq_zero.mp h3 with hdiff | hinner
    · exact (sub_eq_zero.mp hdiff).symm
    · exact absurd hinner hn
  have hSv : S v = 0 := apply_eq_zero_of_forall_inner_sgVec hcpt hsym horth
  rw [heig] at hSv
  rcases smul_eq_zero.mp hSv with h | h
  · exact hc h
  · exact hv h

/-- A negative quadratic trial space of dimension at least `m` forces `m` orthonormal genuine
negative eigenvectors.  This is the finite-dimensional negative-index half of the min–max
principle, proved directly by repeatedly restricting to the orthogonal complement of the
eigenvectors already found. -/
theorem exists_orthonormal_negative_eigenfamily_of_finrank_le {S : H →L[ℂ] H}
    (hcpt : IsCompactOperator S) (hsym : S.IsSymmetric) (V : Submodule ℂ H) {m : ℕ}
    (hm : m ≤ Module.finrank ℂ V)
    (hneg : ∀ x : H, x ∈ V → x ≠ 0 → RCLike.re (inner ℂ (S x) x) < 0) :
    ∃ e : Fin m → H, Orthonormal ℂ e ∧
      ∀ i, ∃ c : ℝ, c < 0 ∧ S (e i) = (c : ℂ) • e i := by
  revert hm
  induction m with
  | zero =>
      intro _hm
      refine ⟨fun i => Fin.elim0 i, Orthonormal.of_isEmpty _, ?_⟩
      intro i
      exact Fin.elim0 i
  | succ m ih =>
      intro hm
      have hdim : m < Module.finrank ℂ V := lt_of_lt_of_le (Nat.lt_succ_self m) hm
      obtain ⟨e, he, heig⟩ := ih (Nat.le_of_lt hdim)
      let w : ℕ → H := fun k => if hk : k < m then e ⟨k, hk⟩ else 0
      obtain ⟨x, hxV, hx0, hxorth⟩ :=
        exists_mem_ne_zero_orthogonal_of_finrank_lt V w m hdim
      have hxe : ∀ i, inner ℂ (e i) x = 0 := by
        intro i
        simpa [w, i.isLt] using hxorth (i : ℕ) i.isLt
      set W : Submodule ℂ H := (Submodule.span ℂ (Set.range e))ᗮ with hW
      have hxW : x ∈ W := by
        rw [hW, Submodule.mem_orthogonal_span_iff]
        rintro u ⟨i, rfl⟩
        exact hxe i
      have hWinv : ∀ y ∈ W, S y ∈ W := by
        intro y hy
        rw [hW, Submodule.mem_orthogonal_span_iff] at hy ⊢
        rintro u ⟨i, rfl⟩
        obtain ⟨c, _hc, hceig⟩ := heig i
        have h1 : inner ℂ (e i) (S y) = inner ℂ (S (e i)) y :=
          (hsym (e i) y).symm
        rw [h1, hceig, inner_smul_left, hy (e i) ⟨i, rfl⟩, mul_zero]
      set Sw : W →L[ℂ] W := S.restrict hWinv with hSw
      have hSw_apply : ∀ z : W, (Sw z : H) = S (z : H) := fun z => rfl
      have hSw_compact : IsCompactOperator Sw := hcpt.restrict' hWinv
      have hSw_symm : Sw.IsSymmetric := hsym.restrict_invariant hWinv
      let xW : W := ⟨x, hxW⟩
      have hxnegW : RCLike.re (inner ℂ (Sw xW) xW) < 0 := by
        rw [Submodule.coe_inner, hSw_apply]
        exact hneg x hxV hx0
      obtain ⟨c, v, hc, hv0, hv⟩ :=
        exists_negative_eigenpair_of_re_inner_neg hSw_compact hSw_symm hxnegW
      let uW : W := ((‖v‖ : ℂ))⁻¹ • v
      have huNorm : ‖uW‖ = 1 := norm_smul_inv_norm hv0
      have huEigW : Sw uW = (c : ℂ) • uW := by
        change Sw (((‖v‖ : ℂ))⁻¹ • v) =
          (c : ℂ) • (((‖v‖ : ℂ))⁻¹ • v)
        rw [map_smul, hv]
        exact smul_comm ((‖v‖ : ℂ))⁻¹ (c : ℂ) v
      have huOrth : ∀ i, inner ℂ (uW : H) (e i) = 0 := by
        intro i
        have huW : (uW : H) ∈ (Submodule.span ℂ (Set.range e))ᗮ := by
          rw [← hW]
          exact uW.2
        have huW' := (Submodule.mem_orthogonal_span_iff.mp huW)
        have heu : inner ℂ (e i) (uW : H) = 0 := huW' (e i) ⟨i, rfl⟩
        rw [← inner_conj_symm, heu, map_zero]
      have huEig : S (uW : H) = (c : ℂ) • (uW : H) := by
        have h := congrArg (Subtype.val : W → H) huEigW
        rw [hSw_apply] at h
        simpa only [Submodule.coe_smul] using h
      refine ⟨Matrix.vecCons (uW : H) e,
        orthonormal_vecCons_iff.mpr ⟨huNorm, huOrth, he⟩, ?_⟩
      intro i
      refine Fin.cases ⟨c, hc, huEig⟩ (fun j => ?_) i
      exact heig j

/-- A negative quadratic trial space contributes at least its dimension many distinct negative
entries to the signed-greedy spectrum.  The distinctness is the multiplicity-sensitive part:
each induction step works in the orthogonal complement of all previously selected greedy vectors. -/
theorem exists_injective_negative_sgVal_indices_of_finrank_le {S : H →L[ℂ] H}
    (hcpt : IsCompactOperator S) (hsym : S.IsSymmetric) (V : Submodule ℂ H) {m : ℕ}
    (hm : m ≤ Module.finrank ℂ V)
    (hneg : ∀ x : H, x ∈ V → x ≠ 0 → RCLike.re (inner ℂ (S x) x) < 0) :
    ∃ r : Fin m → ℕ, Function.Injective r ∧ ∀ i, sgVal S (r i) < 0 := by
  revert hm
  induction m with
  | zero =>
      intro _hm
      refine ⟨fun i => Fin.elim0 i, ?_, ?_⟩
      · intro i
        exact Fin.elim0 i
      · intro i
        exact Fin.elim0 i
  | succ m ih =>
      intro hm
      have hdim : m < Module.finrank ℂ V := lt_of_lt_of_le (Nat.lt_succ_self m) hm
      obtain ⟨r, hrinj, hrneg⟩ := ih (Nat.le_of_lt hdim)
      let w : ℕ → H := fun k =>
        if hk : k < m then sgVec S (r ⟨k, hk⟩) else 0
      obtain ⟨x, hxV, hx0, hxorth⟩ :=
        exists_mem_ne_zero_orthogonal_of_finrank_lt V w m hdim
      have hxr : ∀ i, inner ℂ (sgVec S (r i)) x = 0 := by
        intro i
        simpa [w, i.isLt] using hxorth (i : ℕ) i.isLt
      let g : Fin m → H := fun i => sgVec S (r i)
      set W : Submodule ℂ H := (Submodule.span ℂ (Set.range g))ᗮ with hW
      have hxW : x ∈ W := by
        rw [hW, Submodule.mem_orthogonal_span_iff]
        rintro u ⟨i, rfl⟩
        exact hxr i
      have hWinv : ∀ y ∈ W, S y ∈ W := by
        intro y hy
        rw [hW, Submodule.mem_orthogonal_span_iff] at hy ⊢
        rintro u ⟨i, rfl⟩
        have h1 : inner ℂ (g i) (S y) = inner ℂ (S (g i)) y :=
          (hsym (g i) y).symm
        rw [h1, show S (g i) = ((sgVal S (r i) : ℝ) : ℂ) • g i by
          exact apply_sgVec S (r i), inner_smul_left, hy (g i) ⟨i, rfl⟩, mul_zero]
      set Sw : W →L[ℂ] W := S.restrict hWinv with hSw
      have hSw_apply : ∀ z : W, (Sw z : H) = S (z : H) := fun z => rfl
      have hSw_compact : IsCompactOperator Sw := hcpt.restrict' hWinv
      have hSw_symm : Sw.IsSymmetric := hsym.restrict_invariant hWinv
      let xW : W := ⟨x, hxW⟩
      have hxnegW : RCLike.re (inner ℂ (Sw xW) xW) < 0 := by
        rw [Submodule.coe_inner, hSw_apply]
        exact hneg x hxV hx0
      obtain ⟨c, v, hc, hv0, hv⟩ :=
        exists_negative_eigenpair_of_re_inner_neg hSw_compact hSw_symm hxnegW
      have hv0H : (v : H) ≠ 0 := by
        intro h
        exact hv0 (Subtype.ext h)
      have hvH : S (v : H) = (c : ℂ) • (v : H) := by
        have h := congrArg (Subtype.val : W → H) hv
        rw [hSw_apply] at h
        simpa only [Submodule.coe_smul] using h
      obtain ⟨n, hnval, hninner⟩ :=
        exists_sgVal_eq_of_eigenvalue_and_inner_ne_zero hcpt hsym hv0H hvH
          (Complex.ofReal_ne_zero.mpr (ne_of_lt hc))
      have hnreal : sgVal S n = c := by exact_mod_cast hnval
      have hnneg : sgVal S n < 0 := hnreal.trans_lt hc
      have hnrange : n ∉ Set.range r := by
        rintro ⟨i, rfl⟩
        apply hninner
        have hvW : (v : H) ∈ (Submodule.span ℂ (Set.range g))ᗮ := by
          rw [← hW]
          exact v.2
        exact (Submodule.mem_orthogonal_span_iff.mp hvW) (g i) ⟨i, rfl⟩
      let r' : Fin (m + 1) → ℕ := Fin.cons n r
      refine ⟨r', Fin.cons_injective_of_injective hnrange hrinj, ?_⟩
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa [r'] using hnneg
      · simpa [r'] using hrneg j

/-- A positive quadratic trial space of dimension at least `m` forces `m` orthonormal genuine
positive eigenvectors. -/
theorem exists_orthonormal_positive_eigenfamily_of_finrank_le {S : H →L[ℂ] H}
    (hcpt : IsCompactOperator S) (hsym : S.IsSymmetric) (V : Submodule ℂ H) {m : ℕ}
    (hm : m ≤ Module.finrank ℂ V)
    (hpos : ∀ x : H, x ∈ V → x ≠ 0 → 0 < RCLike.re (inner ℂ (S x) x)) :
    ∃ e : Fin m → H, Orthonormal ℂ e ∧
      ∀ i, ∃ c : ℝ, 0 < c ∧ S (e i) = (c : ℂ) • e i := by
  have hsymneg : (-S).IsSymmetric := by
    intro u v
    change inner ℂ (-(S u)) v = inner ℂ u (-(S v))
    rw [inner_neg_left, inner_neg_right]
    exact congrArg Neg.neg (hsym u v)
  have hneg : ∀ x : H, x ∈ V → x ≠ 0 →
      RCLike.re (inner ℂ ((-S) x) x) < 0 := by
    intro x hxV hx0
    simpa using (neg_lt_zero.mpr (hpos x hxV hx0))
  obtain ⟨e, he, heig⟩ :=
    exists_orthonormal_negative_eigenfamily_of_finrank_le hcpt.neg hsymneg V hm hneg
  refine ⟨e, he, fun i => ?_⟩
  obtain ⟨c, hc, hceig⟩ := heig i
  refine ⟨-c, neg_pos.mpr hc, ?_⟩
  simpa [neg_smul] using congrArg Neg.neg hceig

/-- A positive quadratic trial space contributes at least its dimension many distinct positive
entries to the signed-greedy spectrum. -/
theorem exists_injective_positive_sgVal_indices_of_finrank_le {S : H →L[ℂ] H}
    (hcpt : IsCompactOperator S) (hsym : S.IsSymmetric) (V : Submodule ℂ H) {m : ℕ}
    (hm : m ≤ Module.finrank ℂ V)
    (hpos : ∀ x : H, x ∈ V → x ≠ 0 → 0 < RCLike.re (inner ℂ (S x) x)) :
    ∃ r : Fin m → ℕ, Function.Injective r ∧ ∀ i, 0 < sgVal S (r i) := by
  revert hm
  induction m with
  | zero =>
      intro _hm
      refine ⟨fun i => Fin.elim0 i, ?_, ?_⟩
      · intro i
        exact Fin.elim0 i
      · intro i
        exact Fin.elim0 i
  | succ m ih =>
      intro hm
      have hdim : m < Module.finrank ℂ V := lt_of_lt_of_le (Nat.lt_succ_self m) hm
      obtain ⟨r, hrinj, hrpos⟩ := ih (Nat.le_of_lt hdim)
      let w : ℕ → H := fun k =>
        if hk : k < m then sgVec S (r ⟨k, hk⟩) else 0
      obtain ⟨x, hxV, hx0, hxorth⟩ :=
        exists_mem_ne_zero_orthogonal_of_finrank_lt V w m hdim
      have hxr : ∀ i, inner ℂ (sgVec S (r i)) x = 0 := by
        intro i
        simpa [w, i.isLt] using hxorth (i : ℕ) i.isLt
      let g : Fin m → H := fun i => sgVec S (r i)
      set W : Submodule ℂ H := (Submodule.span ℂ (Set.range g))ᗮ with hW
      have hxW : x ∈ W := by
        rw [hW, Submodule.mem_orthogonal_span_iff]
        rintro u ⟨i, rfl⟩
        exact hxr i
      have hWinv : ∀ y ∈ W, S y ∈ W := by
        intro y hy
        rw [hW, Submodule.mem_orthogonal_span_iff] at hy ⊢
        rintro u ⟨i, rfl⟩
        have h1 : inner ℂ (g i) (S y) = inner ℂ (S (g i)) y :=
          (hsym (g i) y).symm
        rw [h1, show S (g i) = ((sgVal S (r i) : ℝ) : ℂ) • g i by
          exact apply_sgVec S (r i), inner_smul_left, hy (g i) ⟨i, rfl⟩, mul_zero]
      set Sw : W →L[ℂ] W := S.restrict hWinv with hSw
      have hSw_apply : ∀ z : W, (Sw z : H) = S (z : H) := fun z => rfl
      have hSw_compact : IsCompactOperator Sw := hcpt.restrict' hWinv
      have hSw_symm : Sw.IsSymmetric := hsym.restrict_invariant hWinv
      let xW : W := ⟨x, hxW⟩
      have hxposW : 0 < RCLike.re (inner ℂ (Sw xW) xW) := by
        rw [Submodule.coe_inner, hSw_apply]
        exact hpos x hxV hx0
      obtain ⟨c, v, hc, hv0, hv⟩ :=
        exists_positive_eigenpair_of_re_inner_pos hSw_compact hSw_symm hxposW
      have hv0H : (v : H) ≠ 0 := by
        intro h
        exact hv0 (Subtype.ext h)
      have hvH : S (v : H) = (c : ℂ) • (v : H) := by
        have h := congrArg (Subtype.val : W → H) hv
        rw [hSw_apply] at h
        simpa only [Submodule.coe_smul] using h
      obtain ⟨n, hnval, hninner⟩ :=
        exists_sgVal_eq_of_eigenvalue_and_inner_ne_zero hcpt hsym hv0H hvH
          (Complex.ofReal_ne_zero.mpr (ne_of_gt hc))
      have hnreal : sgVal S n = c := by exact_mod_cast hnval
      have hnpos : 0 < sgVal S n := hnreal.symm ▸ hc
      have hnrange : n ∉ Set.range r := by
        rintro ⟨i, rfl⟩
        apply hninner
        have hvW : (v : H) ∈ (Submodule.span ℂ (Set.range g))ᗮ := by
          rw [← hW]
          exact v.2
        exact (Submodule.mem_orthogonal_span_iff.mp hvW) (g i) ⟨i, rfl⟩
      let r' : Fin (m + 1) → ℕ := Fin.cons n r
      refine ⟨r', Fin.cons_injective_of_injective hnrange hrinj, ?_⟩
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa [r'] using hnpos
      · simpa [r'] using hrpos j

end ContinuousLinearMap

namespace RHTower

/-! ## Uniform finite-depth Hermite sectors -/

/-- Sum of the positive-sector aperture truncation errors at fixed depth. -/
def hermitePositiveTruncationSum (a : ℝ) (n : ℕ) : ℝ :=
  ∑ j : Fin (n + 1),
    ‖hermiteEvenUnit (j : ℕ) - evenIndicatorCutoff a (hermiteEvenUnit (j : ℕ))‖

/-- Sum of the negative-sector aperture truncation errors at fixed depth. -/
def hermiteNegativeTruncationSum (a : ℝ) (n : ℕ) : ℝ :=
  ∑ j : Fin (n + 1),
    ‖hermiteEvenNegativeUnit (j : ℕ) -
      evenIndicatorCutoff a (hermiteEvenNegativeUnit (j : ℕ))‖

theorem tendsto_hermitePositiveTruncationSum (n : ℕ) :
    Tendsto (fun a : ℝ => hermitePositiveTruncationSum a n) atTop (nhds 0) := by
  have h : Tendsto (fun a : ℝ => ∑ j : Fin (n + 1),
      ‖hermiteEvenUnit (j : ℕ) - evenIndicatorCutoff a (hermiteEvenUnit (j : ℕ))‖)
      atTop (nhds (∑ _j : Fin (n + 1), (0 : ℝ))) :=
    tendsto_finsetSum _ fun j _ => tendsto_norm_sub_cut (hermiteEvenUnit (j : ℕ))
  simpa [hermitePositiveTruncationSum] using h

theorem tendsto_hermiteNegativeTruncationSum (n : ℕ) :
    Tendsto (fun a : ℝ => hermiteNegativeTruncationSum a n) atTop (nhds 0) := by
  have h : Tendsto (fun a : ℝ => ∑ j : Fin (n + 1),
      ‖hermiteEvenNegativeUnit (j : ℕ) -
        evenIndicatorCutoff a (hermiteEvenNegativeUnit (j : ℕ))‖)
      atTop (nhds (∑ _j : Fin (n + 1), (0 : ℝ))) :=
    tendsto_finsetSum _ fun j _ =>
      tendsto_norm_sub_cut (hermiteEvenNegativeUnit (j : ℕ))
  simpa [hermiteNegativeTruncationSum] using h

theorem norm_hermiteEvenUnit_sub_cut_le_truncationSum
    (a : ℝ) (n : ℕ) (j : Fin (n + 1)) :
    ‖hermiteEvenUnit (j : ℕ) - evenIndicatorCutoff a (hermiteEvenUnit (j : ℕ))‖
      ≤ hermitePositiveTruncationSum a n := by
  exact Finset.single_le_sum (f := fun k : Fin (n + 1) =>
    ‖hermiteEvenUnit (k : ℕ) - evenIndicatorCutoff a (hermiteEvenUnit (k : ℕ))‖)
    (fun k _ => norm_nonneg
    (hermiteEvenUnit (k : ℕ) - evenIndicatorCutoff a (hermiteEvenUnit (k : ℕ))))
    (Finset.mem_univ j)

theorem norm_hermiteEvenNegativeUnit_sub_cut_le_truncationSum
    (a : ℝ) (n : ℕ) (j : Fin (n + 1)) :
    ‖hermiteEvenNegativeUnit (j : ℕ) -
      evenIndicatorCutoff a (hermiteEvenNegativeUnit (j : ℕ))‖
      ≤ hermiteNegativeTruncationSum a n := by
  exact Finset.single_le_sum (f := fun k : Fin (n + 1) =>
    ‖hermiteEvenNegativeUnit (k : ℕ) -
      evenIndicatorCutoff a (hermiteEvenNegativeUnit (k : ℕ))‖)
    (fun k _ => norm_nonneg
    (hermiteEvenNegativeUnit (k : ℕ) -
      evenIndicatorCutoff a (hermiteEvenNegativeUnit (k : ℕ))))
    (Finset.mem_univ j)

/-- At every fixed depth, the actual compressed Fourier quadratic form is eventually strictly
positive on the entire nonzero positive Hermite trial space. -/
theorem eventually_strictlyPositiveOn_hermiteTrialSpace (n : ℕ) :
    ∀ᶠ a : ℝ in atTop, ∀ f : evenSubspace, f ∈ hermiteTrialSpace n → f ≠ 0 →
      0 < RCLike.re (inner ℂ (evenTimeBandFourier a f) f) := by
  let C : ℝ → ℝ := fun a =>
    ((n + 1 : ℕ) : ℝ) * (2 * hermitePositiveTruncationSum a n) ^ (2 : ℕ)
  have hC : Tendsto C atTop (nhds 0) := by
    have hη := tendsto_hermitePositiveTruncationSum n
    have h2η : Tendsto (fun a : ℝ => 2 * hermitePositiveTruncationSum a n)
        atTop (nhds 0) := by simpa using hη.const_mul 2
    have hsq : Tendsto (fun a : ℝ => (2 * hermitePositiveTruncationSum a n) ^ (2 : ℕ))
        atTop (nhds 0) := by simpa using h2η.pow 2
    simpa [C] using hsq.const_mul (((n + 1 : ℕ) : ℝ))
  have hsmall : ∀ᶠ a : ℝ in atTop, C a < 1 := hC.eventually_lt_const one_pos
  filter_upwards [hsmall] with a ha f hf hf0
  have hsq := norm_sq_sub_timeBand_le_of_hermite_trial a n
    (fun j => norm_hermiteEvenUnit_sub_cut_le_truncationSum a n j) hf
  have hfnorm : 0 < ‖f‖ ^ (2 : ℕ) := sq_pos_of_pos (norm_pos_iff.mpr hf0)
  have hdefectsq : ‖f - evenTimeBandFourier a f‖ ^ (2 : ℕ) < ‖f‖ ^ (2 : ℕ) := by
    refine hsq.trans_lt ?_
    change C a * ‖f‖ ^ (2 : ℕ) < ‖f‖ ^ (2 : ℕ)
    nlinarith [mul_lt_mul_of_pos_right ha hfnorm]
  have hdefect : ‖f - evenTimeBandFourier a f‖ < ‖f‖ := by
    nlinarith [sq_nonneg ‖f - evenTimeBandFourier a f‖, sq_nonneg ‖f‖,
      norm_nonneg (f - evenTimeBandFourier a f), norm_nonneg f]
  have hneg := ContinuousLinearMap.re_inner_neg_of_norm_add_lt_norm
    (-evenTimeBandFourier a) f (by
      rw [show (-evenTimeBandFourier a) f = -(evenTimeBandFourier a f) from rfl]
      simpa [sub_eq_add_neg] using hdefect)
  simpa using hneg

/-- At every fixed depth, the actual compressed Fourier quadratic form is eventually strictly
negative on the entire nonzero negative Hermite trial space. -/
theorem eventually_strictlyNegativeOn_hermiteNegativeTrialSpace (n : ℕ) :
    ∀ᶠ a : ℝ in atTop, ∀ f : evenSubspace, f ∈ hermiteNegativeTrialSpace n → f ≠ 0 →
      RCLike.re (inner ℂ (evenTimeBandFourier a f) f) < 0 := by
  let C : ℝ → ℝ := fun a =>
    ((n + 1 : ℕ) : ℝ) * (2 * hermiteNegativeTruncationSum a n) ^ (2 : ℕ)
  have hC : Tendsto C atTop (nhds 0) := by
    have hη := tendsto_hermiteNegativeTruncationSum n
    have h2η : Tendsto (fun a : ℝ => 2 * hermiteNegativeTruncationSum a n)
        atTop (nhds 0) := by simpa using hη.const_mul 2
    have hsq : Tendsto (fun a : ℝ => (2 * hermiteNegativeTruncationSum a n) ^ (2 : ℕ))
        atTop (nhds 0) := by simpa using h2η.pow 2
    simpa [C] using hsq.const_mul (((n + 1 : ℕ) : ℝ))
  have hsmall : ∀ᶠ a : ℝ in atTop, C a < 1 := hC.eventually_lt_const one_pos
  filter_upwards [hsmall] with a ha f hf hf0
  have hsq := norm_sq_add_timeBand_le_of_negative_hermite_trial a n
    (fun j => norm_hermiteEvenNegativeUnit_sub_cut_le_truncationSum a n j) hf
  have hfnorm : 0 < ‖f‖ ^ (2 : ℕ) := sq_pos_of_pos (norm_pos_iff.mpr hf0)
  have hdefectsq : ‖f + evenTimeBandFourier a f‖ ^ (2 : ℕ) < ‖f‖ ^ (2 : ℕ) := by
    refine hsq.trans_lt ?_
    change C a * ‖f‖ ^ (2 : ℕ) < ‖f‖ ^ (2 : ℕ)
    nlinarith [mul_lt_mul_of_pos_right ha hfnorm]
  have hdefect : ‖f + evenTimeBandFourier a f‖ < ‖f‖ := by
    nlinarith [sq_nonneg ‖f + evenTimeBandFourier a f‖, sq_nonneg ‖f‖,
      norm_nonneg (f + evenTimeBandFourier a f), norm_nonneg f]
  exact ContinuousLinearMap.re_inner_neg_of_norm_add_lt_norm
    (evenTimeBandFourier a) f hdefect

/-- At every fixed depth, the actual even prolate block eventually has `n+1` orthonormal
positive eigenvectors.  Unlike a one-vector sign witness, this records spectral multiplicity. -/
theorem eventually_exists_orthonormal_positive_evenProlateEigenfamily (n : ℕ) :
    ∀ᶠ a : ℝ in atTop,
      ∃ e : Fin (n + 1) → evenSubspace, Orthonormal ℂ e ∧
        ∀ i, ∃ c : ℝ, 0 < c ∧
          evenTimeBandFourier a (e i) = (c : ℂ) • e i := by
  filter_upwards [eventually_gt_atTop (0 : ℝ),
    eventually_strictlyPositiveOn_hermiteTrialSpace n] with a ha hpos
  exact ContinuousLinearMap.exists_orthonormal_positive_eigenfamily_of_finrank_le
    (isCompactOperator_evenTimeBandFourier a ha)
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
      (adjoint_evenTimeBandFourier a))
    (hermiteTrialSpace n) (by rw [finrank_hermiteTrialSpace]) hpos

/-- At every fixed depth, the actual even prolate block eventually has `n+1` orthonormal
negative eigenvectors.  This is the multiplicity-sensitive negative Hermite sector. -/
theorem eventually_exists_orthonormal_negative_evenProlateEigenfamily (n : ℕ) :
    ∀ᶠ a : ℝ in atTop,
      ∃ e : Fin (n + 1) → evenSubspace, Orthonormal ℂ e ∧
        ∀ i, ∃ c : ℝ, c < 0 ∧
          evenTimeBandFourier a (e i) = (c : ℂ) • e i := by
  filter_upwards [eventually_gt_atTop (0 : ℝ),
    eventually_strictlyNegativeOn_hermiteNegativeTrialSpace n] with a ha hneg
  exact ContinuousLinearMap.exists_orthonormal_negative_eigenfamily_of_finrank_le
    (isCompactOperator_evenTimeBandFourier a ha)
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
      (adjoint_evenTimeBandFourier a))
    (hermiteNegativeTrialSpace n) (by rw [finrank_hermiteNegativeTrialSpace]) hneg

/-- At fixed depth, `n+1` distinct entries of the actual signed-greedy prolate spectrum are
eventually positive. -/
theorem eventually_exists_injective_positive_evenProlateSignedIndices (n : ℕ) :
    ∀ᶠ a : ℝ in atTop,
      ∃ r : Fin (n + 1) → ℕ, Function.Injective r ∧
        ∀ i, 0 < evenProlateSignedValue a (r i) := by
  filter_upwards [eventually_gt_atTop (0 : ℝ),
    eventually_strictlyPositiveOn_hermiteTrialSpace n] with a ha hpos
  simpa only [evenProlateSignedValue] using
    (ContinuousLinearMap.exists_injective_positive_sgVal_indices_of_finrank_le
      (isCompactOperator_evenTimeBandFourier a ha)
      (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
        (adjoint_evenTimeBandFourier a))
      (hermiteTrialSpace n) (by rw [finrank_hermiteTrialSpace]) hpos)

/-- At fixed depth, `n+1` distinct entries of the actual signed-greedy prolate spectrum are
eventually negative. -/
theorem eventually_exists_injective_negative_evenProlateSignedIndices (n : ℕ) :
    ∀ᶠ a : ℝ in atTop,
      ∃ r : Fin (n + 1) → ℕ, Function.Injective r ∧
        ∀ i, evenProlateSignedValue a (r i) < 0 := by
  filter_upwards [eventually_gt_atTop (0 : ℝ),
    eventually_strictlyNegativeOn_hermiteNegativeTrialSpace n] with a ha hneg
  simpa only [evenProlateSignedValue] using
    (ContinuousLinearMap.exists_injective_negative_sgVal_indices_of_finrank_le
      (isCompactOperator_evenTimeBandFourier a ha)
      (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
        (adjoint_evenTimeBandFourier a))
      (hermiteNegativeTrialSpace n) (by rw [finrank_hermiteNegativeTrialSpace]) hneg)

/-- Each fixed positive Hermite mode becomes an approximate `+1` eigenvector. -/
theorem tendsto_norm_hermiteEvenUnit_sub_timeBand (j : ℕ) :
    Tendsto (fun a : ℝ =>
      ‖hermiteEvenUnit j - evenTimeBandFourier a (hermiteEvenUnit j)‖)
      atTop (nhds 0) := by
  have hbound : Tendsto (fun a : ℝ =>
      2 * ‖hermiteEvenUnit j - evenIndicatorCutoff a (hermiteEvenUnit j)‖)
      atTop (nhds 0) := by
    simpa using (tendsto_norm_sub_cut (hermiteEvenUnit j)).const_mul 2
  refine squeeze_zero' ?_ ?_ hbound
  · filter_upwards with a
    exact norm_nonneg _
  · filter_upwards with a
    exact norm_hermiteEvenUnit_sub_timeBand_le a j

/-- The actual even prolate Fourier block has a positive signed eigenvalue at every sufficiently
large aperture. -/
theorem eventually_exists_evenProlateSignedValue_pos :
    ∀ᶠ a : ℝ in atTop, ∃ n : ℕ, 0 < evenProlateSignedValue a n := by
  have hsmall : ∀ᶠ a : ℝ in atTop,
      ‖hermiteEvenUnit 0 - evenTimeBandFourier a (hermiteEvenUnit 0)‖ < 1 :=
    (tendsto_norm_hermiteEvenUnit_sub_timeBand 0).eventually_lt_const one_pos
  filter_upwards [eventually_gt_atTop (0 : ℝ), hsmall] with a ha hdefect
  have hquad : 0 < RCLike.re
      (inner ℂ (evenTimeBandFourier a (hermiteEvenUnit 0)) (hermiteEvenUnit 0)) := by
    have hneg := ContinuousLinearMap.re_inner_neg_of_norm_add_lt_norm
      (-evenTimeBandFourier a) (hermiteEvenUnit 0) (by
        change ‖hermiteEvenUnit 0 - evenTimeBandFourier a (hermiteEvenUnit 0)‖ <
          ‖hermiteEvenUnit 0‖
        rw [norm_hermiteEvenUnit]
        exact hdefect)
    simpa using hneg
  exact ContinuousLinearMap.exists_sgVal_pos_of_re_inner_pos
    (isCompactOperator_evenTimeBandFourier a ha)
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
      (adjoint_evenTimeBandFourier a)) hquad

/-- The actual even prolate Fourier block has a negative signed eigenvalue at every sufficiently
large aperture. -/
theorem eventually_exists_evenProlateSignedValue_neg :
    ∀ᶠ a : ℝ in atTop, ∃ n : ℕ, evenProlateSignedValue a n < 0 := by
  have hsmall : ∀ᶠ a : ℝ in atTop,
      ‖hermiteEvenNegativeUnit 0 +
        evenTimeBandFourier a (hermiteEvenNegativeUnit 0)‖ < 1 :=
    (tendsto_norm_hermiteEvenNegativeUnit_add_timeBand 0).eventually_lt_const one_pos
  filter_upwards [eventually_gt_atTop (0 : ℝ), hsmall] with a ha hdefect
  have hquad : RCLike.re
      (inner ℂ (evenTimeBandFourier a (hermiteEvenNegativeUnit 0))
        (hermiteEvenNegativeUnit 0)) < 0 :=
    ContinuousLinearMap.re_inner_neg_of_norm_add_lt_norm
      (evenTimeBandFourier a) (hermiteEvenNegativeUnit 0) (by
        change ‖hermiteEvenNegativeUnit 0 +
          evenTimeBandFourier a (hermiteEvenNegativeUnit 0)‖ <
            ‖hermiteEvenNegativeUnit 0‖
        rw [norm_hermiteEvenNegativeUnit]
        exact hdefect)
  exact ContinuousLinearMap.exists_sgVal_neg_of_re_inner_neg
    (isCompactOperator_evenTimeBandFourier a ha)
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
      (adjoint_evenTimeBandFourier a)) hquad

/-- Coarse Fourier-parity separation: for all sufficiently large apertures the true signed
prolate spectrum simultaneously contains positive and negative values. -/
theorem eventually_exists_positive_and_negative_evenProlateSignedValues :
    ∀ᶠ a : ℝ in atTop,
      (∃ n : ℕ, 0 < evenProlateSignedValue a n) ∧
        ∃ n : ℕ, evenProlateSignedValue a n < 0 :=
  eventually_exists_evenProlateSignedValue_pos.and
    eventually_exists_evenProlateSignedValue_neg

end RHTower

end
