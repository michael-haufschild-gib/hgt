import GaloisForLFunctions.HTGeometry.StokesEnergyTree

/-!
# Galois-orbit descent of finite Stokes coarea

This module descends a positive branch-cut presentation along a finite sheet-orbit map.  Mixed
orbit irregularities are defined by summing genuine branch contacts.  Their full quadratic pairing
is proved equal to the branch pairing, physical rank is proved equal to ramification-weighted rank,
and the exact coarea identity leaves one and only one possible nonpositive rank channel.

The branch cut system is still input here.  A separate coefficient-threshold construction supplies
it from finite Puiseux data.
-/

open scoped BigOperators

namespace GaloisForLFunctions.IrregularStokes

noncomputable section

/-- Finite Puiseux branches, grouped into Stokes-circle orbits, with a positive rooted-cut contact
presentation on the branches. -/
structure OrbitCoareaDatum (n m e : ℕ) where
  cuts : RootedCutContact m e
  orbit : Fin m → Fin n
  orbit_surjective : Function.Surjective orbit

namespace OrbitCoareaDatum

variable {n m e : ℕ}

/-- Pull an orbit charge back to every Puiseux branch. -/
def liftCharge (d : OrbitCoareaDatum n m e) (x : Fin n → ℝ) (a : Fin m) : ℝ :=
  x (d.orbit a)

/-- Total branch charge. -/
def physicalRank (d : OrbitCoareaDatum n m e) (x : Fin n → ℝ) : ℝ :=
  ∑ a, d.liftCharge x a

/-- Number of branches in an orbit. -/
def ramification (d : OrbitCoareaDatum n m e) (i : Fin n) : ℕ :=
  (Finset.univ.filter fun a => d.orbit a = i).card

/-- Full contact pairing after pulling orbit charges to branches. -/
def contactPairing (d : OrbitCoareaDatum n m e) (x : Fin n → ℝ) : ℝ :=
  ∑ a, ∑ b, d.liftCharge x a * d.liftCharge x b * d.cuts.contact a b

/-- Sum a branch function over one orbit. -/
def fiberSum (d : OrbitCoareaDatum n m e) (i : Fin n) (f : Fin m → ℝ) : ℝ :=
  ∑ a ∈ Finset.univ with d.orbit a = i, f a

/-- Mixed Hom irregularity: sum of branch contacts over two orbits. -/
def homIrregularity (d : OrbitCoareaDatum n m e) (i j : Fin n) : ℝ :=
  d.fiberSum i fun a => d.fiberSum j fun b => d.cuts.contact a b

/-- Quadratic pairing of the mixed Hom-irregularity matrix. -/
def orbitContactPairing (d : OrbitCoareaDatum n m e) (x : Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j, x i * x j * d.homIrregularity i j

/-- Positive block-charge coarea energy. -/
def blockEnergy (d : OrbitCoareaDatum n m e) (x : Fin n → ℝ) : ℝ :=
  ∑ edge, d.cuts.length edge *
    (∑ a, d.liftCharge x a * d.cuts.side edge a) ^ 2

/-- Positive terminal orbit energy. -/
def terminalEnergy (_d : OrbitCoareaDatum n m e) (x : Fin n → ℝ) : ℝ :=
  ∑ i, x i ^ 2

/-- Cartan polarization written directly from terminal energy, total rank, and mixed branch
irregularity. -/
def cartanQuadratic (d : OrbitCoareaDatum n m e) (x : Fin n → ℝ) : ℝ :=
  d.terminalEnergy x + d.physicalRank x ^ 2 - d.contactPairing x

/-- Every Stokes-circle orbit has positive ramification. -/
theorem ramification_pos (d : OrbitCoareaDatum n m e) (i : Fin n) :
    0 < d.ramification i := by
  obtain ⟨a, ha⟩ := d.orbit_surjective i
  apply Finset.card_pos.mpr
  exact ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha⟩⟩

/-- Total branch charge is exactly ramification-weighted physical rank. -/
theorem physicalRank_eq_ramification_sum
    (d : OrbitCoareaDatum n m e) (x : Fin n → ℝ) :
    d.physicalRank x = ∑ i, x i * d.ramification i := by
  simp only [physicalRank, liftCharge]
  calc
    (∑ a, x (d.orbit a)) =
        ∑ i, ∑ a ∈ Finset.univ with d.orbit a = i, x (d.orbit a) :=
      (Finset.sum_fiberwise Finset.univ d.orbit (fun a => x (d.orbit a))).symm
    _ = ∑ i, x i * d.ramification i := by
      apply Finset.sum_congr rfl
      intro i _
      calc
        (∑ a ∈ Finset.univ with d.orbit a = i, x (d.orbit a)) =
            ∑ _a ∈ Finset.univ.filter (fun a => d.orbit a = i), x i := by
              apply Finset.sum_congr rfl
              intro a ha
              rw [Finset.mem_filter] at ha
              rw [ha.2]
        _ = (Finset.univ.filter (fun a => d.orbit a = i)).card • x i :=
          Finset.sum_const (x i)
        _ = x i * d.ramification i := by
          simp only [ramification, nsmul_eq_mul]
          ring

/-- Mixed Hom irregularity is symmetric. -/
theorem homIrregularity_symm (d : OrbitCoareaDatum n m e) (i j : Fin n) :
    d.homIrregularity i j = d.homIrregularity j i := by
  simp only [homIrregularity, fiberSum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro a _
  exact d.cuts.contact_symm a b

/-- Weighted orbit sums may be evaluated branchwise. -/
theorem sum_mul_fiberSum (d : OrbitCoareaDatum n m e)
    (x : Fin n → ℝ) (f : Fin m → ℝ) :
    (∑ i, x i * d.fiberSum i f) = ∑ a, d.liftCharge x a * f a := by
  simp only [fiberSum, liftCharge]
  calc
    (∑ i, x i * ∑ a ∈ Finset.univ with d.orbit a = i, f a) =
        ∑ i, ∑ a ∈ Finset.univ with d.orbit a = i, x i * f a := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
    _ = ∑ i, ∑ a ∈ Finset.univ with d.orbit a = i,
        x (d.orbit a) * f a := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.mem_filter] at ha
      rw [ha.2]
    _ = ∑ a, x (d.orbit a) * f a :=
      Finset.sum_fiberwise Finset.univ d.orbit (fun a => x (d.orbit a) * f a)

/-- Finite fiber sums commute with finite weighted sums. -/
theorem fiberSum_sum_mul (d : OrbitCoareaDatum n m e) (i : Fin n)
    (x : Fin n → ℝ) (f : Fin n → Fin m → ℝ) :
    d.fiberSum i (fun a => ∑ j, x j * f j a) =
      ∑ j, x j * d.fiberSum i (f j) := by
  simp only [fiberSum]
  calc
    (∑ a ∈ Finset.univ with d.orbit a = i, ∑ j, x j * f j a) =
        ∑ j, ∑ a ∈ Finset.univ with d.orbit a = i, x j * f j a := by
      rw [Finset.sum_comm]
    _ = ∑ j, x j * ∑ a ∈ Finset.univ with d.orbit a = i, f j a := by
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.mul_sum]

/-- Galois orbit descent is exact: the mixed Hom matrix pairing is the branch contact pairing. -/
theorem orbitContactPairing_eq_contactPairing
    (d : OrbitCoareaDatum n m e) (x : Fin n → ℝ) :
    d.orbitContactPairing x = d.contactPairing x := by
  simp only [orbitContactPairing, homIrregularity]
  calc
    (∑ i, ∑ j, x i * x j *
      d.fiberSum i (fun a => d.fiberSum j fun b => d.cuts.contact a b)) =
      ∑ i, x i * d.fiberSum i (fun a =>
        ∑ j, x j * d.fiberSum j fun b => d.cuts.contact a b) := by
          apply Finset.sum_congr rfl
          intro i _
          calc
            (∑ j, x i * x j *
                d.fiberSum i (fun a => d.fiberSum j fun b => d.cuts.contact a b)) =
              x i * ∑ j, x j *
                d.fiberSum i (fun a => d.fiberSum j fun b => d.cuts.contact a b) := by
                  rw [Finset.mul_sum]
                  apply Finset.sum_congr rfl
                  intro j _
                  ring
            _ = x i * d.fiberSum i (fun a =>
                ∑ j, x j * d.fiberSum j fun b => d.cuts.contact a b) := by
                  rw [d.fiberSum_sum_mul]
    _ = ∑ a, d.liftCharge x a *
        (∑ j, x j * d.fiberSum j fun b => d.cuts.contact a b) := by
          rw [d.sum_mul_fiberSum]
    _ = ∑ a, d.liftCharge x a *
        (∑ b, d.liftCharge x b * d.cuts.contact a b) := by
          apply Finset.sum_congr rfl
          intro a _
          rw [d.sum_mul_fiberSum]
    _ = d.contactPairing x := by
          simp only [contactPairing]
          apply Finset.sum_congr rfl
          intro a _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro b _
          ring

/-- Branch contact coarea is root-rank square minus positive block energy. -/
theorem contactPairing_eq_root_rank_sq_sub_blockEnergy
    (d : OrbitCoareaDatum n m e) (x : Fin n → ℝ) :
    d.contactPairing x =
      d.cuts.root * d.physicalRank x ^ 2 - d.blockEnergy x := by
  simp only [contactPairing, RootedCutContact.contact, physicalRank, blockEnergy]
  have hroot :
      (∑ a, ∑ b, d.liftCharge x a * d.liftCharge x b * d.cuts.root) =
        d.cuts.root * (∑ a, d.liftCharge x a) ^ 2 := by
    rw [show (∑ a, ∑ b, d.liftCharge x a * d.liftCharge x b * d.cuts.root) =
        (∑ a, ∑ b, d.liftCharge x a * d.liftCharge x b) * d.cuts.root by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_mul]]
    rw [double_sum_mul]
    ring
  have hedge : ∀ edge : Fin e,
      (∑ a, ∑ b, d.liftCharge x a * d.liftCharge x b *
        (d.cuts.side edge a * d.cuts.side edge b)) =
      (∑ a, d.liftCharge x a * d.cuts.side edge a) ^ 2 := by
    intro edge
    calc
      (∑ a, ∑ b, d.liftCharge x a * d.liftCharge x b *
          (d.cuts.side edge a * d.cuts.side edge b)) =
        ∑ a, ∑ b, (d.liftCharge x a * d.cuts.side edge a) *
          (d.liftCharge x b * d.cuts.side edge b) := by
            apply Finset.sum_congr rfl
            intro a _
            apply Finset.sum_congr rfl
            intro b _
            ring
      _ = (∑ a, d.liftCharge x a * d.cuts.side edge a) *
          (∑ b, d.liftCharge x b * d.cuts.side edge b) := by
            rw [double_sum_mul]
      _ = (∑ a, d.liftCharge x a * d.cuts.side edge a) ^ 2 := by ring
  calc
    (∑ a, ∑ b, d.liftCharge x a * d.liftCharge x b *
        (d.cuts.root - ∑ edge, d.cuts.length edge *
          (d.cuts.side edge a * d.cuts.side edge b))) =
      (∑ a, ∑ b, d.liftCharge x a * d.liftCharge x b * d.cuts.root) -
        ∑ edge, d.cuts.length edge *
          (∑ a, ∑ b, d.liftCharge x a * d.liftCharge x b *
            (d.cuts.side edge a * d.cuts.side edge b)) := by
      simp_rw [mul_sub, Finset.sum_sub_distrib]
      simp_rw [Finset.mul_sum]
      apply congrArg₂ (· - ·) rfl
      calc
        (∑ a, ∑ b, ∑ edge, d.liftCharge x a * d.liftCharge x b *
            (d.cuts.length edge *
              (d.cuts.side edge a * d.cuts.side edge b))) =
          ∑ a, ∑ edge, ∑ b, d.liftCharge x a * d.liftCharge x b *
            (d.cuts.length edge *
              (d.cuts.side edge a * d.cuts.side edge b)) := by
                apply Finset.sum_congr rfl
                intro a _
                rw [Finset.sum_comm]
        _ = ∑ edge, ∑ a, ∑ b, d.liftCharge x a * d.liftCharge x b *
            (d.cuts.length edge *
              (d.cuts.side edge a * d.cuts.side edge b)) := by
                rw [Finset.sum_comm]
        _ = ∑ edge, ∑ a, ∑ b, d.cuts.length edge *
            (d.liftCharge x a * d.liftCharge x b *
              (d.cuts.side edge a * d.cuts.side edge b)) := by
                apply Finset.sum_congr rfl
                intro edge _
                apply Finset.sum_congr rfl
                intro a _
                apply Finset.sum_congr rfl
                intro b _
                ring
    _ = d.cuts.root * (∑ a, d.liftCharge x a) ^ 2 -
        ∑ edge, d.cuts.length edge *
          (∑ a, d.liftCharge x a * d.cuts.side edge a) ^ 2 := by
      rw [hroot]
      simp_rw [hedge]

/-- Exact orbit-level one-port coarea law. -/
theorem cartanQuadratic_eq_positive_sub_onePort
    (d : OrbitCoareaDatum n m e) (x : Fin n → ℝ) :
    d.cartanQuadratic x = d.terminalEnergy x + d.blockEnergy x -
      (d.cuts.root - 1) * d.physicalRank x ^ 2 := by
  rw [cartanQuadratic, d.contactPairing_eq_root_rank_sq_sub_blockEnergy]
  ring

/-- Terminal orbit energy is strictly positive away from zero. -/
theorem terminalEnergy_pos (d : OrbitCoareaDatum n m e) {x : Fin n → ℝ}
    (hx : x ≠ 0) : 0 < d.terminalEnergy x := by
  simp only [terminalEnergy]
  have hex : ∃ i, x i ≠ 0 := by
    by_contra h
    push Not at h
    apply hx
    funext i
    exact h i
  obtain ⟨i, hi⟩ := hex
  apply Finset.sum_pos'
  · intro j _
    exact sq_nonneg (x j)
  · exact ⟨i, Finset.mem_univ _, sq_pos_of_ne_zero hi⟩

/-- Block coarea energy is nonnegative. -/
theorem blockEnergy_nonneg (d : OrbitCoareaDatum n m e) (x : Fin n → ℝ) :
    0 ≤ d.blockEnergy x := by
  simp only [blockEnergy]
  apply Finset.sum_nonneg
  intro edge _
  exact mul_nonneg (d.cuts.length_pos edge).le (sq_nonneg _)

/-- The descended Cartan form is strictly positive on the physical-rank-zero hyperplane. -/
theorem cartanQuadratic_pos_of_physicalRank_eq_zero
    (d : OrbitCoareaDatum n m e) {x : Fin n → ℝ}
    (hrank : d.physicalRank x = 0) (hx : x ≠ 0) :
    0 < d.cartanQuadratic x := by
  rw [d.cartanQuadratic_eq_positive_sub_onePort, hrank]
  have ht := d.terminalEnergy_pos hx
  have hb := d.blockEnergy_nonneg x
  nlinarith

end OrbitCoareaDatum
end
end GaloisForLFunctions.IrregularStokes
