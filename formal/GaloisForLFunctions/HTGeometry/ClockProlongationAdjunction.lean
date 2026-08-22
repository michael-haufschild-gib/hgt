/-
# The clock prolongation / internal-core adjunction

Finite differential prolongation `J_r` adjoins every reading obtainable from an intermediate field
in at most `r` applications of the derivation; finite internal-core erosion `C_r` retains exactly
the elements whose readings through order `r` remain inside a given intermediate field.  The two
operations form a Galois connection on the lattice of intermediate fields, erosion is the `r`-fold
iterate of the one-tick core, and prolongation inherits the corresponding semigroup law from
uniqueness of left adjoints.

On the jet ray of a hypertranscendental element both the unit and the counit of the adjunction are
equalities: prolongation and erosion translate along the tower without bulk loss, so the
counit-defect interval is trivial there and the only residue is the one-tick boundary.
-/
import GaloisForLFunctions.HTGeometry.HypertranscendentalClockBoundary

namespace GaloisForLFunctions.HTGeometry

open scoped Differential

noncomputable section

variable {F E : Type*} [Field F] [Field E] [Differential F] [Differential E]
  [Algebra F E] [DifferentialAlgebra F E]

/-- One tick of clock erosion: the observables of `C` whose derivative is still visible in `C`. -/
def differentialCore (C : IntermediateField F E) : IntermediateField F E where
  carrier := {b : E | b ∈ C ∧ b′ ∈ C}
  zero_mem' := ⟨C.zero_mem, by simp⟩
  one_mem' := ⟨C.one_mem, by simp⟩
  add_mem' := by
    rintro a b ⟨ha, hda⟩ ⟨hb, hdb⟩
    exact ⟨C.add_mem ha hb, by rw [map_add]; exact C.add_mem hda hdb⟩
  mul_mem' := by
    rintro a b ⟨ha, hda⟩ ⟨hb, hdb⟩
    refine ⟨C.mul_mem ha hb, ?_⟩
    rw [Derivation.leibniz]
    exact C.add_mem (C.mul_mem ha hdb) (C.mul_mem hb hda)
  inv_mem' := by
    rintro a ⟨ha, hda⟩
    refine ⟨C.inv_mem ha, ?_⟩
    rw [Derivation.leibniz_inv]
    exact C.mul_mem (C.neg_mem (C.toSubfield.pow_mem (C.inv_mem ha) 2)) hda
  algebraMap_mem' := by
    intro c
    exact ⟨C.algebraMap_mem c, by rw [deriv_algebraMap]; exact C.algebraMap_mem _⟩

theorem mem_differentialCore {C : IntermediateField F E} {b : E} :
    b ∈ differentialCore C ↔ b ∈ C ∧ b′ ∈ C := Iff.rfl

/-- **Finite clock erosion** `C_r`: the observables of `B` all of whose readings through tick `r`
remain visible in `B`. -/
def clockCore (B : IntermediateField F E) (r : ℕ) : IntermediateField F E :=
  differentialCore^[r] B

@[simp]
theorem clockCore_zero (B : IntermediateField F E) : clockCore B 0 = B := rfl

theorem clockCore_succ (B : IntermediateField F E) (r : ℕ) :
    clockCore B (r + 1) = differentialCore (clockCore B r) :=
  Function.iterate_succ_apply' _ _ _

theorem mem_clockCore_iff {B : IntermediateField F E} {r : ℕ} {b : E} :
    b ∈ clockCore B r ↔ ∀ q ≤ r, differentialJet q b ∈ B := by
  have hone : ∀ y : E, differentialJet 1 y = y′ := fun y => by simp
  induction r generalizing b with
  | zero =>
      constructor
      · intro hb q hq
        obtain rfl : q = 0 := Nat.eq_zero_of_le_zero hq
        simpa using hb
      · intro h
        simpa using h 0 le_rfl
  | succ r ih =>
      rw [clockCore_succ, mem_differentialCore]
      simp only [ih]
      constructor
      · rintro ⟨h1, h2⟩ q hq
        rcases Nat.eq_zero_or_pos q with rfl | hpos
        · simpa using h1 0 (Nat.zero_le _)
        · obtain ⟨p, rfl⟩ : ∃ p, q = p + 1 := ⟨q - 1, by omega⟩
          have := h2 p (by omega)
          rw [differentialJet_add p 1, hone]
          exact this
      · intro h
        refine ⟨fun q hq => h q (by omega), fun q hq => ?_⟩
        have := h (q + 1) (by omega)
        rwa [differentialJet_add q 1, hone] at this

theorem clockCore_add (B : IntermediateField F E) (r s : ℕ) :
    clockCore B (s + r) = clockCore (clockCore B r) s :=
  Function.iterate_add_apply _ s r B

/-- **Finite clock prolongation** `J_r`: adjoin every reading obtainable from `A` in at most `r`
clock ticks. -/
def clockProlongation (A : IntermediateField F E) (r : ℕ) : IntermediateField F E :=
  IntermediateField.adjoin F {y : E | ∃ q ≤ r, ∃ a ∈ A, y = differentialJet q a}

omit [Differential F] [DifferentialAlgebra F E] in
theorem differentialJet_mem_clockProlongation {A : IntermediateField F E} {r q : ℕ} (hq : q ≤ r)
    {a : E} (ha : a ∈ A) : differentialJet q a ∈ clockProlongation A r :=
  IntermediateField.subset_adjoin F _ ⟨q, hq, a, ha, rfl⟩

omit [Differential F] [DifferentialAlgebra F E] in
theorem le_clockProlongation (A : IntermediateField F E) (r : ℕ) :
    A ≤ clockProlongation A r := fun a ha => by
  simpa using differentialJet_mem_clockProlongation (r := r) (Nat.zero_le r) ha

/-- **The clock adjunction.**  Finite prolongation is left adjoint to finite internal-core
erosion on the lattice of intermediate differential observables. -/
theorem clockProlongation_le_iff_le_clockCore (A B : IntermediateField F E) (r : ℕ) :
    clockProlongation A r ≤ B ↔ A ≤ clockCore B r := by
  constructor
  · intro h a ha
    rw [mem_clockCore_iff]
    intro q hq
    exact h (differentialJet_mem_clockProlongation hq ha)
  · intro h
    rw [clockProlongation, IntermediateField.adjoin_le_iff]
    rintro y ⟨q, hq, a, ha, rfl⟩
    exact mem_clockCore_iff.mp (h ha) q hq

/-- Prolongation and erosion form a Galois connection at every fixed resolution. -/
theorem clockGaloisConnection (r : ℕ) :
    GaloisConnection (fun A : IntermediateField F E => clockProlongation A r)
      (fun B : IntermediateField F E => clockCore B r) :=
  fun A B => clockProlongation_le_iff_le_clockCore A B r

theorem le_clockCore_clockProlongation (A : IntermediateField F E) (r : ℕ) :
    A ≤ clockCore (clockProlongation A r) r :=
  (clockGaloisConnection r).le_u_l A

theorem clockProlongation_clockCore_le (B : IntermediateField F E) (r : ℕ) :
    clockProlongation (clockCore B r) r ≤ B :=
  (clockGaloisConnection r).l_u_le B

theorem clockProlongation_mono (r : ℕ) :
    Monotone (fun A : IntermediateField F E => clockProlongation A r) :=
  (clockGaloisConnection r).monotone_l

theorem clockCore_mono (r : ℕ) :
    Monotone (fun B : IntermediateField F E => clockCore B r) :=
  (clockGaloisConnection r).monotone_u

theorem clockCore_le (B : IntermediateField F E) (r : ℕ) : clockCore B r ≤ B := fun b hb => by
  simpa using mem_clockCore_iff.mp hb 0 (Nat.zero_le r)

/-- `C_r ∘ J_r` is idempotent: it is the closure operator of the clock adjunction. -/
theorem clockCore_clockProlongation_clockCore (B : IntermediateField F E) (r : ℕ) :
    clockCore (clockProlongation (clockCore B r) r) r = clockCore B r :=
  (clockGaloisConnection r).u_l_u_eq_u B

/-- `J_r ∘ C_r` is idempotent: it is the interior operator of the clock adjunction. -/
theorem clockProlongation_clockCore_clockProlongation (A : IntermediateField F E) (r : ℕ) :
    clockProlongation (clockCore (clockProlongation A r) r) r = clockProlongation A r :=
  (clockGaloisConnection r).l_u_l_eq_l A

/-- The erosion semigroup law, in commuting form. -/
theorem clockCore_clockCore_comm (B : IntermediateField F E) (r s : ℕ) :
    clockCore (clockCore B r) s = clockCore (clockCore B s) r := by
  rw [← clockCore_add, ← clockCore_add, Nat.add_comm]

/-- The prolongation semigroup law `J_(s+r) = J_r ∘ J_s`. -/
theorem clockProlongation_clockProlongation (A : IntermediateField F E) (r s : ℕ) :
    clockProlongation (clockProlongation A s) r = clockProlongation A (s + r) := by
  refine le_antisymm ?_ ?_
  · rw [clockProlongation_le_iff_le_clockCore, clockProlongation_le_iff_le_clockCore,
      ← clockCore_add]
    exact le_clockCore_clockProlongation A (s + r)
  · rw [clockProlongation_le_iff_le_clockCore, clockCore_add]
    exact le_trans (le_clockCore_clockProlongation A s)
      (clockCore_mono s (le_clockCore_clockProlongation (clockProlongation A s) r))

/-! ### The exact hypertranscendental orbit -/

/-- Prolongation moves along the jet ray: `J_r(P_N) = P_(N+r)` for every positive cutoff `N`. -/
theorem clockProlongation_jetObservableField {x : E} {N : ℕ} (hN : 1 ≤ N) (r : ℕ) :
    clockProlongation (jetObservableField F x N) r = jetObservableField F x (N + r) := by
  refine le_antisymm ?_ ?_
  · rw [clockProlongation, IntermediateField.adjoin_le_iff]
    rintro y ⟨q, hq, a, ha, rfl⟩
    exact jetObservableField_mono x (by omega)
      (differentialJet_mem_jetObservableField_add x ha q)
  · rw [jetObservableField, IntermediateField.adjoin_le_iff]
    rintro y ⟨n, hn, rfl⟩
    have hnlt : n < N + r := hn
    by_cases hnN : n < N
    · refine le_clockProlongation (jetObservableField F x N) r ?_
      exact IntermediateField.subset_adjoin F _ ⟨n, hnN, rfl⟩
    · have hbase : differentialJet (N - 1) x ∈ jetObservableField F x N :=
        IntermediateField.subset_adjoin F _ ⟨N - 1, show N - 1 < N by omega, rfl⟩
      have hsplit : differentialJet n x
          = differentialJet (n - (N - 1)) (differentialJet (N - 1) x) := by
        rw [← differentialJet_add]
        congr 1
        omega
      change differentialJet n x ∈ (clockProlongation (jetObservableField F x N) r : Set E)
      rw [hsplit]
      exact differentialJet_mem_clockProlongation (by omega) hbase

/-- Erosion moves back along the jet ray of a hypertranscendental source: `C_r(P_(N+r)) = P_N`. -/
theorem clockCore_jetObservableField [CharZero E] {x : E}
    (hx : HypertranscendentalOver F x) (N r : ℕ) :
    clockCore (jetObservableField F x (N + r)) r = jetObservableField F x N := by
  ext b
  rw [mem_clockCore_iff]
  exact hypertranscendental_clock_erosion_iff hx N r

/-- **The adjunction unit is an equality along the hypertranscendental jet ray.** -/
theorem clockCore_clockProlongation_jetObservableField [CharZero E] {x : E}
    (hx : HypertranscendentalOver F x) {N : ℕ} (hN : 1 ≤ N) (r : ℕ) :
    clockCore (clockProlongation (jetObservableField F x N) r) r = jetObservableField F x N := by
  rw [clockProlongation_jetObservableField hN r, clockCore_jetObservableField hx N r]

/-- **The adjunction counit is an equality along the hypertranscendental jet ray**, so the
counit-defect interval is trivial on the free tower. -/
theorem clockProlongation_clockCore_jetObservableField [CharZero E] {x : E}
    (hx : HypertranscendentalOver F x) {N : ℕ} (hN : 1 ≤ N) (r : ℕ) :
    clockProlongation (clockCore (jetObservableField F x (N + r)) r) r
      = jetObservableField F x (N + r) := by
  rw [clockCore_jetObservableField hx N r, clockProlongation_jetObservableField hN r]

/-- The one-tick core of the observable field at cutoff `N+1` is the field at cutoff `N`. -/
theorem differentialCore_jetObservableField [CharZero E] {x : E}
    (hx : HypertranscendentalOver F x) (N : ℕ) :
    differentialCore (jetObservableField F x (N + 1)) = jetObservableField F x N := by
  have := clockCore_jetObservableField hx N 1
  rwa [clockCore_succ, clockCore_zero] at this

end

end GaloisForLFunctions.HTGeometry
