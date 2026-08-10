import Mathlib
import GaloisForLFunctions.HTGeometry.ConstraintRelativity.CongruenceOrderTraceDual

/-!
# Barcode invariants of the diagonal congruence order

The antisymmetric cotangent sector of the diagonal congruence order is indexed by the ordered
pairs of sheets, hence has rank `binom (N-1) 2`, and the trace-law and cotangent-law lengths
differ by exactly that number.
-/

namespace HTGeometry.ConstraintRelativity

/-! ## The antisymmetric index set -/

section PairIndex

variable {m : ℕ}

/-- The two-element subset attached to an ordered pair of sheets. -/
def pairToFinset (p : pairIndex m) : Set.powersetCard (Fin m) 2 :=
  ⟨{p.1.1, p.1.2}, by
    classical
    show ({p.1.1, p.1.2} : Finset (Fin m)).card = 2
    rw [Finset.card_insert_of_notMem (by simp [p.2.ne]), Finset.card_singleton]⟩

theorem pairToFinset_coe (p : pairIndex m) :
    (pairToFinset p : Finset (Fin m)) = {p.1.1, p.1.2} := rfl

theorem pairToFinset_injective : Function.Injective (pairToFinset (m := m)) := by
  classical
  intro p q h
  have h' : ({p.1.1, p.1.2} : Finset (Fin m)) = {q.1.1, q.1.2} := congrArg Subtype.val h
  have hp1 : p.1.1 ∈ ({q.1.1, q.1.2} : Finset (Fin m)) := by rw [← h']; simp
  have hp2 : p.1.2 ∈ ({q.1.1, q.1.2} : Finset (Fin m)) := by rw [← h']; simp
  have hq2 : q.1.2 ∈ ({p.1.1, p.1.2} : Finset (Fin m)) := by rw [h']; simp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp1 hp2 hq2
  have hpl : (p.1.1 : ℕ) < p.1.2 := p.2
  have hql : (q.1.1 : ℕ) < q.1.2 := q.2
  rw [Fin.ext_iff] at hp1 hp2 hq2
  refine Subtype.ext (Prod.ext ?_ ?_) <;> rw [Fin.ext_iff] <;> omega

theorem pairToFinset_surjective : Function.Surjective (pairToFinset (m := m)) := by
  classical
  rintro ⟨s, hs⟩
  obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.1 hs
  rcases lt_or_gt_of_ne hxy with h | h
  · exact ⟨⟨(x, y), h⟩, rfl⟩
  · exact ⟨⟨(y, x), h⟩, Subtype.ext (Finset.pair_comm y x)⟩

/-- Ordered pairs of sheets are the same as two-element sets of sheets. -/
noncomputable def pairIndexEquivPowersetCard (m : ℕ) :
    pairIndex m ≃ Set.powersetCard (Fin m) 2 :=
  Equiv.ofBijective _ ⟨pairToFinset_injective, pairToFinset_surjective⟩

/-- **Card `(7)`.**  The antisymmetric cotangent sector has rank `binom (N−1) 2`. -/
theorem card_pairIndex (m : ℕ) : Fintype.card (pairIndex m) = m.choose 2 := by
  classical
  rw [Fintype.card_congr (pairIndexEquivPowersetCard m)]
  have h : Fintype.card {s : Finset (Fin m) // s.card = 2} = (Fintype.card (Fin m)).choose 2 :=
    Fintype.card_finset_len 2
  rw [Fintype.card_fin] at h
  exact h.symm ▸ Fintype.card_congr (Equiv.refl _)

end PairIndex

/-! ## Lengths of the two defect modules -/

section Lengths

variable {R : Type*} [CommRing R]

theorem length_quotient_span_of_isMaximal (a : R)
    (hmax : (Ideal.span ({a} : Set R)).IsMaximal) :
    Module.length R (R ⧸ Ideal.span ({a} : Set R)) = 1 :=
  Module.length_eq_one_iff.2 (isSimpleModule_iff_isCoatom.2 hmax.out)

theorem length_quotient_span_sq [IsDomain R] {a : R} (ha : a ≠ 0)
    (hmax : (Ideal.span ({a} : Set R)).IsMaximal) :
    Module.length R (R ⧸ Ideal.span ({a ^ 2} : Set R)) = 2 := by
  have hord : Ring.ord R (a * a) = Ring.ord R a + Ring.ord R a :=
    Ring.ord_mul R (mem_nonZeroDivisors_of_ne_zero ha)
  have hone : Ring.ord R a = 1 := length_quotient_span_of_isMaximal a hmax
  show Ring.ord R (a ^ 2) = 2
  rw [pow_two, hord, hone]
  rfl

variable {a : R} {m : ℕ}

theorem length_traceDefectModel [IsDomain R] (ha : a ≠ 0)
    (hmax : (Ideal.span ({a} : Set R)).IsMaximal) :
    Module.length R (Fin m → R ⧸ Ideal.span ({a ^ 2} : Set R)) = ((2 * m : ℕ) : ℕ∞) := by
  rw [Module.length_pi_of_fintype,
    Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => length_quotient_span_sq ha hmax),
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  ring

theorem length_pairSector (hmax : (Ideal.span ({a} : Set R)).IsMaximal) :
    Module.length R (pairIndex m → R ⧸ Ideal.span ({a} : Set R))
      = ((m.choose 2 : ℕ) : ℕ∞) := by
  classical
  rw [Module.length_pi_of_fintype,
    Finset.sum_congr rfl
      (fun p (_ : p ∈ Finset.univ) => length_quotient_span_of_isMaximal a hmax),
    Finset.sum_const, Finset.card_univ, card_pairIndex, nsmul_eq_mul, mul_one]

/-- **Card `(27)`.**  The cotangent-law defect has length `2m + binom m 2`. -/
theorem length_cotangentModel [IsDomain R] (ha : a ≠ 0)
    (hmax : (Ideal.span ({a} : Set R)).IsMaximal) :
    Module.length R (cotangentModel a m) = ((2 * m + m.choose 2 : ℕ) : ℕ∞) := by
  rw [cotangentModel, Module.length_prod, length_traceDefectModel ha hmax,
    length_pairSector hmax]
  push_cast
  ring

/-- **Card `(28)`.**  The cotangent-law length exceeds the trace-law length by exactly
`binom (N−1) 2`. -/
theorem length_cotangentModel_eq_length_traceDefect_add [IsDomain R] (ha : a ≠ 0)
    (hmax : (Ideal.span ({a} : Set R)).IsMaximal) :
    Module.length R (cotangentModel a m)
      = Module.length R (Fin m → R ⧸ Ideal.span ({a ^ 2} : Set R)) + ((m.choose 2 : ℕ) : ℕ∞) := by
  rw [length_cotangentModel ha hmax, length_traceDefectModel ha hmax]
  push_cast
  ring

end Lengths

end HTGeometry.ConstraintRelativity
