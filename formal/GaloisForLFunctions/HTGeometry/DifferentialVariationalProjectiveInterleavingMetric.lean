import GaloisForLFunctions.HTGeometry.DifferentialVariationalProjectiveInterleaving

/-!
# A projective interleaving metric

The full-lattice interleaving metric is minimized over one left-homothety orbit.  Discreteness of
the natural-number radii gives an attained minimum, so no compactness or analytic assumption is
needed.  Homothety invariance and orbit absorption make the minimum independent of both lattice
representatives.  It therefore descends to a genuine separating natural-number metric on the
corrected projective building carrier.

This remains an integral interleaving metric, not the paper's Euclidean Cartan metric.
-/

open scoped Differential

namespace GaloisForLFunctions.HTGeometry.DiffOp

noncomputable section

variable {K : Type u} [Field K] [Differential K]
variable {ι : Type*} [Fintype ι]

/-- Two lattice orbits are interleaved at radius `n` if some left-homothetic representative of
the second is literally `n`-interleaved with the first. -/
def CompletedPseudoDiffOpLattice.LeftOrbitInterleavedAt
    (n : ℕ) (L M : CompletedPseudoDiffOpLattice K ι) : Prop :=
  ∃ a : (CompletedPseudoDiffOp K)ˣ,
    L.InterleavedAt n (leftScaleCompletedPseudoDiffOpLattice a M)

/-- Every pair of lattice orbits has an interleaving radius. -/
theorem exists_completedPseudoDiffOpLattice_leftOrbitInterleavedAt
    (L M : CompletedPseudoDiffOpLattice K ι) :
    ∃ n : ℕ, L.LeftOrbitInterleavedAt n M := by
  obtain ⟨n, hn⟩ := exists_completedPseudoDiffOpLattice_interleavedAt L M
  refine ⟨n, 1, ?_⟩
  simpa only [leftScaleCompletedPseudoDiffOpLattice_one] using hn

omit [Fintype ι] in
/-- Orbit interleaving is symmetric. -/
theorem CompletedPseudoDiffOpLattice.LeftOrbitInterleavedAt.symm
    {L M : CompletedPseudoDiffOpLattice K ι} {n : ℕ}
    (h : L.LeftOrbitInterleavedAt n M) : M.LeftOrbitInterleavedAt n L := by
  obtain ⟨a, ha⟩ := h
  refine ⟨a⁻¹, ?_⟩
  have hscaled :=
    (leftScaleCompletedPseudoDiffOpLattice_interleavedAt_iff a⁻¹
      (leftScaleCompletedPseudoDiffOpLattice a M) L n).2 ha.symm
  simpa only [leftScaleCompletedPseudoDiffOpLattice_mul, inv_mul_cancel,
    leftScaleCompletedPseudoDiffOpLattice_one] using hscaled

omit [Fintype ι] in
/-- Orbit interleaving persists after increasing the radius. -/
theorem CompletedPseudoDiffOpLattice.LeftOrbitInterleavedAt.mono
    {L M : CompletedPseudoDiffOpLattice K ι} {m n : ℕ} (hmn : m ≤ n)
    (h : L.LeftOrbitInterleavedAt m M) : L.LeftOrbitInterleavedAt n M := by
  obtain ⟨a, ha⟩ := h
  exact ⟨a, ha.mono hmn⟩

omit [Fintype ι] in
/-- Radius-zero orbit interleaving is exactly left homothety. -/
theorem completedPseudoDiffOpLattice_leftOrbitInterleavedAt_zero_iff
    (L M : CompletedPseudoDiffOpLattice K ι) :
    L.LeftOrbitInterleavedAt 0 M ↔ L.LeftHomothetic M := by
  constructor
  · rintro ⟨a, ha⟩
    have hEq := (completedPseudoDiffOpLattice_interleavedAt_zero_iff L
      (leftScaleCompletedPseudoDiffOpLattice a M)).1 ha
    refine ⟨a⁻¹, ?_⟩
    rw [hEq, leftScaleCompletedPseudoDiffOpLattice_mul]
    simp only [inv_mul_cancel, leftScaleCompletedPseudoDiffOpLattice_one]
  · rintro ⟨a, rfl⟩
    refine ⟨a⁻¹, ?_⟩
    rw [completedPseudoDiffOpLattice_interleavedAt_zero_iff,
      leftScaleCompletedPseudoDiffOpLattice_mul]
    simp only [inv_mul_cancel, leftScaleCompletedPseudoDiffOpLattice_one]

omit [Fintype ι] in
/-- Orbit interleaving radii add. -/
theorem CompletedPseudoDiffOpLattice.LeftOrbitInterleavedAt.add
    {L M N : CompletedPseudoDiffOpLattice K ι} {m n : ℕ}
    (hLM : L.LeftOrbitInterleavedAt m M)
    (hMN : M.LeftOrbitInterleavedAt n N) :
    L.LeftOrbitInterleavedAt (m + n) N := by
  obtain ⟨a, ha⟩ := hLM
  obtain ⟨b, hb⟩ := hMN
  have hbscaled :=
    (leftScaleCompletedPseudoDiffOpLattice_interleavedAt_iff a M
      (leftScaleCompletedPseudoDiffOpLattice b N) n).2 hb
  refine ⟨a * b, ?_⟩
  simpa only [leftScaleCompletedPseudoDiffOpLattice_mul] using ha.add hbscaled

omit [Fintype ι] in
/-- Scaling the first representative does not change orbit interleaving. -/
theorem leftScaleCompletedPseudoDiffOpLattice_leftOrbitInterleavedAt_iff
    (c : (CompletedPseudoDiffOp K)ˣ)
    (L M : CompletedPseudoDiffOpLattice K ι) (n : ℕ) :
    (leftScaleCompletedPseudoDiffOpLattice c L).LeftOrbitInterleavedAt n M ↔
      L.LeftOrbitInterleavedAt n M := by
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨c⁻¹ * a, ?_⟩
    have hscaled :=
      (leftScaleCompletedPseudoDiffOpLattice_interleavedAt_iff c⁻¹
        (leftScaleCompletedPseudoDiffOpLattice c L)
        (leftScaleCompletedPseudoDiffOpLattice a M) n).2 ha
    simpa only [leftScaleCompletedPseudoDiffOpLattice_mul, inv_mul_cancel,
      leftScaleCompletedPseudoDiffOpLattice_one] using hscaled
  · rintro ⟨a, ha⟩
    refine ⟨c * a, ?_⟩
    have hscaled :=
      (leftScaleCompletedPseudoDiffOpLattice_interleavedAt_iff c L
        (leftScaleCompletedPseudoDiffOpLattice a M) n).2 ha
    simpa only [leftScaleCompletedPseudoDiffOpLattice_mul] using hscaled

omit [Fintype ι] in
/-- Scaling the second representative is absorbed by the minimizing orbit. -/
theorem right_leftScaleCompletedPseudoDiffOpLattice_leftOrbitInterleavedAt_iff
    (c : (CompletedPseudoDiffOp K)ˣ)
    (L M : CompletedPseudoDiffOpLattice K ι) (n : ℕ) :
    L.LeftOrbitInterleavedAt n (leftScaleCompletedPseudoDiffOpLattice c M) ↔
      L.LeftOrbitInterleavedAt n M := by
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨a * c, ?_⟩
    simpa only [leftScaleCompletedPseudoDiffOpLattice_mul] using ha
  · rintro ⟨a, ha⟩
    refine ⟨a * c⁻¹, ?_⟩
    convert ha using 1
    rw [leftScaleCompletedPseudoDiffOpLattice_mul]
    congr 1
    simp [mul_assoc]

/-- Every pair of lattice orbits has a least interleaving radius. -/
theorem exists_least_completedPseudoDiffOpLattice_leftOrbitInterleavedAt
    (L M : CompletedPseudoDiffOpLattice K ι) :
    ∃ n : ℕ, L.LeftOrbitInterleavedAt n M ∧
      ∀ m : ℕ, L.LeftOrbitInterleavedAt m M → n ≤ m := by
  classical
  letI : DecidablePred (fun n : ℕ => L.LeftOrbitInterleavedAt n M) := Classical.decPred _
  let hex : ∃ n : ℕ, L.LeftOrbitInterleavedAt n M :=
    exists_completedPseudoDiffOpLattice_leftOrbitInterleavedAt L M
  exact ⟨Nat.find hex, Nat.find_spec hex, fun m hm => Nat.find_min' hex hm⟩

/-- Least orbit-interleaving radius between two lattice representatives. -/
noncomputable def completedPseudoDiffOpLatticeOrbitInterleavingDistance
    (L M : CompletedPseudoDiffOpLattice K ι) : ℕ :=
  Classical.choose (exists_least_completedPseudoDiffOpLattice_leftOrbitInterleavedAt L M)

/-- The least orbit radius is attained. -/
theorem completedPseudoDiffOpLatticeOrbitInterleavingDistance_spec
    (L M : CompletedPseudoDiffOpLattice K ι) :
    L.LeftOrbitInterleavedAt
      (completedPseudoDiffOpLatticeOrbitInterleavingDistance L M) M :=
  (Classical.choose_spec
    (exists_least_completedPseudoDiffOpLattice_leftOrbitInterleavedAt L M)).1

/-- Characterization of upper bounds for the least orbit-interleaving radius. -/
theorem completedPseudoDiffOpLatticeOrbitInterleavingDistance_le_iff
    (L M : CompletedPseudoDiffOpLattice K ι) (n : ℕ) :
    completedPseudoDiffOpLatticeOrbitInterleavingDistance L M ≤ n ↔
      L.LeftOrbitInterleavedAt n M := by
  constructor
  · intro h
    exact (completedPseudoDiffOpLatticeOrbitInterleavingDistance_spec L M).mono h
  · intro h
    exact (Classical.choose_spec
      (exists_least_completedPseudoDiffOpLattice_leftOrbitInterleavedAt L M)).2 n h

/-- Orbit-interleaving distance is symmetric. -/
theorem completedPseudoDiffOpLatticeOrbitInterleavingDistance_comm
    (L M : CompletedPseudoDiffOpLattice K ι) :
    completedPseudoDiffOpLatticeOrbitInterleavingDistance L M =
      completedPseudoDiffOpLatticeOrbitInterleavingDistance M L := by
  apply le_antisymm
  · rw [completedPseudoDiffOpLatticeOrbitInterleavingDistance_le_iff]
    exact (completedPseudoDiffOpLatticeOrbitInterleavingDistance_spec M L).symm
  · rw [completedPseudoDiffOpLatticeOrbitInterleavingDistance_le_iff]
    exact (completedPseudoDiffOpLatticeOrbitInterleavingDistance_spec L M).symm

/-- Orbit-interleaving distance vanishes exactly on a left-homothety class. -/
theorem completedPseudoDiffOpLatticeOrbitInterleavingDistance_eq_zero_iff
    (L M : CompletedPseudoDiffOpLattice K ι) :
    completedPseudoDiffOpLatticeOrbitInterleavingDistance L M = 0 ↔
      L.LeftHomothetic M := by
  constructor
  · intro h
    have hspec := completedPseudoDiffOpLatticeOrbitInterleavingDistance_spec L M
    rw [h, completedPseudoDiffOpLattice_leftOrbitInterleavedAt_zero_iff] at hspec
    exact hspec
  · intro h
    apply Nat.eq_zero_of_le_zero
    rw [completedPseudoDiffOpLatticeOrbitInterleavingDistance_le_iff,
      completedPseudoDiffOpLattice_leftOrbitInterleavedAt_zero_iff]
    exact h

/-- Triangle inequality for orbit-interleaving distance. -/
theorem completedPseudoDiffOpLatticeOrbitInterleavingDistance_triangle
    (L M N : CompletedPseudoDiffOpLattice K ι) :
    completedPseudoDiffOpLatticeOrbitInterleavingDistance L N ≤
      completedPseudoDiffOpLatticeOrbitInterleavingDistance L M +
        completedPseudoDiffOpLatticeOrbitInterleavingDistance M N := by
  rw [completedPseudoDiffOpLatticeOrbitInterleavingDistance_le_iff]
  exact (completedPseudoDiffOpLatticeOrbitInterleavingDistance_spec L M).add
    (completedPseudoDiffOpLatticeOrbitInterleavingDistance_spec M N)

/-- The orbit distance is unchanged by changing the first representative. -/
theorem completedPseudoDiffOpLatticeOrbitInterleavingDistance_leftScale
    (c : (CompletedPseudoDiffOp K)ˣ)
    (L M : CompletedPseudoDiffOpLattice K ι) :
    completedPseudoDiffOpLatticeOrbitInterleavingDistance
        (leftScaleCompletedPseudoDiffOpLattice c L) M =
      completedPseudoDiffOpLatticeOrbitInterleavingDistance L M := by
  apply le_antisymm
  · rw [completedPseudoDiffOpLatticeOrbitInterleavingDistance_le_iff,
      leftScaleCompletedPseudoDiffOpLattice_leftOrbitInterleavedAt_iff]
    exact completedPseudoDiffOpLatticeOrbitInterleavingDistance_spec L M
  · rw [completedPseudoDiffOpLatticeOrbitInterleavingDistance_le_iff]
    exact (leftScaleCompletedPseudoDiffOpLattice_leftOrbitInterleavedAt_iff c L M _).1
      (completedPseudoDiffOpLatticeOrbitInterleavingDistance_spec
        (leftScaleCompletedPseudoDiffOpLattice c L) M)

/-- The orbit distance is unchanged by changing the second representative. -/
theorem completedPseudoDiffOpLatticeOrbitInterleavingDistance_rightScale
    (c : (CompletedPseudoDiffOp K)ˣ)
    (L M : CompletedPseudoDiffOpLattice K ι) :
    completedPseudoDiffOpLatticeOrbitInterleavingDistance L
        (leftScaleCompletedPseudoDiffOpLattice c M) =
      completedPseudoDiffOpLatticeOrbitInterleavingDistance L M := by
  apply le_antisymm
  · rw [completedPseudoDiffOpLatticeOrbitInterleavingDistance_le_iff,
      right_leftScaleCompletedPseudoDiffOpLattice_leftOrbitInterleavedAt_iff]
    exact completedPseudoDiffOpLatticeOrbitInterleavingDistance_spec L M
  · rw [completedPseudoDiffOpLatticeOrbitInterleavingDistance_le_iff]
    exact (right_leftScaleCompletedPseudoDiffOpLattice_leftOrbitInterleavedAt_iff
      c L M _).1
      (completedPseudoDiffOpLatticeOrbitInterleavingDistance_spec L
        (leftScaleCompletedPseudoDiffOpLattice c M))

/-- The orbit distance respects left-homothety in its first argument. -/
theorem completedPseudoDiffOpLatticeOrbitInterleavingDistance_leftHomothetic
    {L L' : CompletedPseudoDiffOpLattice K ι} (M : CompletedPseudoDiffOpLattice K ι)
    (h : L.LeftHomothetic L') :
    completedPseudoDiffOpLatticeOrbitInterleavingDistance L M =
      completedPseudoDiffOpLatticeOrbitInterleavingDistance L' M := by
  obtain ⟨c, rfl⟩ := h
  exact (completedPseudoDiffOpLatticeOrbitInterleavingDistance_leftScale c L M).symm

/-- The orbit distance respects left-homothety in its second argument. -/
theorem completedPseudoDiffOpLatticeOrbitInterleavingDistance_rightHomothetic
    (L : CompletedPseudoDiffOpLattice K ι) {M M' : CompletedPseudoDiffOpLattice K ι}
    (h : M.LeftHomothetic M') :
    completedPseudoDiffOpLatticeOrbitInterleavingDistance L M =
      completedPseudoDiffOpLatticeOrbitInterleavingDistance L M' := by
  obtain ⟨c, rfl⟩ := h
  exact (completedPseudoDiffOpLatticeOrbitInterleavingDistance_rightScale c L M).symm

/-- Natural-number projective interleaving distance, independent of both representatives. -/
noncomputable def differentialVariationalProjectiveInterleavingDistance
    (x y : DifferentialVariationalProjectiveBuildingCarrier K ι) : ℕ :=
  Quotient.liftOn₂ x y completedPseudoDiffOpLatticeOrbitInterleavingDistance (by
    intro L M L' M' hL hM
    exact (completedPseudoDiffOpLatticeOrbitInterleavingDistance_leftHomothetic M hL).trans
      (completedPseudoDiffOpLatticeOrbitInterleavingDistance_rightHomothetic L' hM))

/-- Projective distance on quotient constructors is the orbit distance. -/
@[simp] theorem differentialVariationalProjectiveInterleavingDistance_mk
    (L M : CompletedPseudoDiffOpLattice K ι) :
    differentialVariationalProjectiveInterleavingDistance
      (Quotient.mk _ L) (Quotient.mk _ M) =
      completedPseudoDiffOpLatticeOrbitInterleavingDistance L M := rfl

/-- Projective interleaving distance vanishes on the diagonal. -/
@[simp] theorem differentialVariationalProjectiveInterleavingDistance_self
    (x : DifferentialVariationalProjectiveBuildingCarrier K ι) :
    differentialVariationalProjectiveInterleavingDistance x x = 0 := by
  induction x using Quotient.inductionOn with
  | _ L =>
      rw [differentialVariationalProjectiveInterleavingDistance_mk,
        completedPseudoDiffOpLatticeOrbitInterleavingDistance_eq_zero_iff]
      exact CompletedPseudoDiffOpLattice.LeftHomothetic.refl L

/-- Projective interleaving distance is symmetric. -/
theorem differentialVariationalProjectiveInterleavingDistance_comm
    (x y : DifferentialVariationalProjectiveBuildingCarrier K ι) :
    differentialVariationalProjectiveInterleavingDistance x y =
      differentialVariationalProjectiveInterleavingDistance y x := by
  induction x using Quotient.inductionOn with
  | _ L =>
      induction y using Quotient.inductionOn with
      | _ M => exact completedPseudoDiffOpLatticeOrbitInterleavingDistance_comm L M

/-- Projective interleaving distance separates projective lattice classes. -/
@[simp] theorem differentialVariationalProjectiveInterleavingDistance_eq_zero_iff
    (x y : DifferentialVariationalProjectiveBuildingCarrier K ι) :
    differentialVariationalProjectiveInterleavingDistance x y = 0 ↔ x = y := by
  induction x using Quotient.inductionOn with
  | _ L =>
      induction y using Quotient.inductionOn with
      | _ M =>
          rw [differentialVariationalProjectiveInterleavingDistance_mk,
            completedPseudoDiffOpLatticeOrbitInterleavingDistance_eq_zero_iff,
            Quotient.eq_iff_equiv]
          rfl

/-- Triangle inequality on the corrected projective building carrier. -/
theorem differentialVariationalProjectiveInterleavingDistance_triangle
    (x y z : DifferentialVariationalProjectiveBuildingCarrier K ι) :
    differentialVariationalProjectiveInterleavingDistance x z ≤
      differentialVariationalProjectiveInterleavingDistance x y +
        differentialVariationalProjectiveInterleavingDistance y z := by
  induction x using Quotient.inductionOn with
  | _ L =>
      induction y using Quotient.inductionOn with
      | _ M =>
          induction z using Quotient.inductionOn with
          | _ N => exact completedPseudoDiffOpLatticeOrbitInterleavingDistance_triangle L M N

end

end GaloisForLFunctions.HTGeometry.DiffOp
