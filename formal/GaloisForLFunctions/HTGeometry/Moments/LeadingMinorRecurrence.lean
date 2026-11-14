import GaloisForLFunctions.HTGeometry.Moments.LeadingMinorNonvanishing
import Mathlib.Algebra.LinearRecurrence

/-!
# Leading Hankel determinants characterize finite recurrences

Over any field, the leading Hankel determinants vanish above size `B` exactly
when the sequence satisfies a linear recurrence of order at most `B`.
Choose the largest nonzero leading block. Its invertibility makes recurrence
coefficients from every taller window agree, giving one recurrence on all indices.
This applies the finite leading-minor theorem without positivity or normalization
of the zeroth moment, and includes the zero sequence as a recurrence of order zero.
-/

open scoped BigOperators Matrix
namespace HTGeometry.FiniteHankel

variable {K : Type*} [Field K]

/-- The determinant of the leading size-`n` moment block. -/
abbrev leadingDet (s : ℕ → K) (n : ℕ) : K :=
  (Matrix.of fun i j : Fin n => s (i.val + j.val)).det

private theorem next_mem_span_of_tail_zero (s : ℕ → K) {m N : ℕ}
    (hmN : m + 1 ≤ N) (hm : leadingDet s m ≠ 0)
    (htail : ∀ n, m < n → leadingDet s n = 0) :
    column s N m ∈ Submodule.span K (Set.range (fun j : Fin m => column s N j.val)) := by
  have hli := ((independent_iff_exists_leading_det s m N).mpr
    ⟨m, le_rfl, by omega, hm⟩).2
  by_contra hn
  have hs : LinearIndependent K (fun j : Fin (m + 1) => column s N j.val) :=
    linearIndependent_finSucc'.mpr ⟨hli, hn⟩
  obtain ⟨n, hn, _, hd⟩ := (independent_iff_exists_leading_det s (m + 1) N).mp ⟨hmN, hs⟩
  exact hd (htail n (by omega))

/-- The last nonzero leading block determines a recurrence valid at every index. -/
theorem recurrence_of_last_nonzero_leading_det (s : ℕ → K) (m : ℕ)
    (hm : leadingDet s m ≠ 0) (htail : ∀ n, m < n → leadingDet s n = 0) :
    ∃ c : Fin m → K, ∀ r, s (r + m) = ∑ j : Fin m, c j * s (r + j.val) := by
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp
    (next_mem_span_of_tail_zero s (N := m + 1) le_rfl hm htail)
  have hcr : ∀ r < m + 1, s (r + m) = ∑ j : Fin m, c j * s (r + j.val) := by
    intro r hr
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, column]
      using (congrFun hc ⟨r, hr⟩).symm
  refine ⟨c, fun r => ?_⟩
  obtain ⟨d, hd⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp
    (next_mem_span_of_tail_zero s (N := m + r + 1) (by omega) hm htail)
  have hdr : ∀ i < m + r + 1, s (i + m) = ∑ j : Fin m, d j * s (i + j.val) := by
    intro i hi
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, column]
      using (congrFun hd ⟨i, hi⟩).symm
  have hli := ((independent_iff_exists_leading_det s m m).mpr
    ⟨m, le_rfl, le_rfl, hm⟩).2
  have hsum : (∑ j : Fin m, (c j - d j) • column s m j.val) = 0 := by
    funext i
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, column, Pi.zero_apply,
      sub_mul, Finset.sum_sub_distrib]
    rw [← hcr i.val (by omega), ← hdr i.val (by omega), sub_self]
  have hcd : c = d := funext fun j =>
    sub_eq_zero.mp (Fintype.linearIndependent_iff.mp hli (fun j => c j - d j) hsum j)
  rw [hcd]
  exact hdr r (by omega)

/-- Finite memory is equivalent to eventual vanishing of leading determinants, with the
same bound on recurrence order and determinant size. -/
theorem leading_tail_zero_iff_recurrence (s : ℕ → K) (B : ℕ) :
    (∀ n, B < n → leadingDet s n = 0) ↔
      ∃ E : LinearRecurrence K, E.order ≤ B ∧ E.IsSolution s := by
  classical
  constructor
  · intro ht
    let P : ℕ → Prop := fun n => leadingDet s n ≠ 0
    let m := Nat.findGreatest P B
    have hzero : P 0 := by simp [P, leadingDet]
    have hm : leadingDet s m ≠ 0 := Nat.findGreatest_spec (Nat.zero_le B) hzero
    have hmB : m ≤ B := Nat.findGreatest_le B
    have htail : ∀ n, m < n → leadingDet s n = 0 := by
      intro n hn
      by_cases hnB : n ≤ B
      · by_contra hne
        exact Nat.findGreatest_is_greatest hn hnB hne
      · exact ht n (by omega)
    obtain ⟨c, hc⟩ := recurrence_of_last_nonzero_leading_det s m hm htail
    exact ⟨⟨m, c⟩, hmB, hc⟩
  · rintro ⟨E, hEB, hE⟩ n hBn
    by_contra hdet
    have hli := ((independent_iff_exists_leading_det s (E.order + 1) n).mpr
      ⟨n, by omega, le_rfl, hdet⟩).2
    have hspan : column s n E.order ∈ Submodule.span K
        (Set.range (fun j : Fin E.order => column s n j.val)) := by
      apply (Submodule.mem_span_range_iff_exists_fun K).mpr
      refine ⟨E.coeffs, ?_⟩
      funext i
      simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, column]
        using (hE i.val).symm
    exact (linearIndependent_finSucc'.mp hli).2 hspan

#print axioms recurrence_of_last_nonzero_leading_det
#print axioms leading_tail_zero_iff_recurrence

end HTGeometry.FiniteHankel
