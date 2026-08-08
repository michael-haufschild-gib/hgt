import GaloisForLFunctions.HTGeometry.OmegaObstruction

/-!
# Realizations of the action-stability interface

Action stability of a coefficient subgroup holds for `⊥` and `⊤` and is preserved by intersections,
sums and infima.  For a subgroup presented by generators it reduces to the generators: a group action
stabilizes `AddSubgroup.closure S` as soon as it moves each element of `S` into the closure.

For the prime-log lattice that reduction is the checkable condition that each prime logarithm is
moved into the lattice, and it removes the stability premise from the gauge and resection
integrality gates.
-/

namespace GaloisForLFunctions

namespace RHTower

variable {G A : Type*} [Group G] [AddCommGroup A] [DistribMulAction G A]

/-! ## Lattice realizations -/

theorem isActionStable_bot : IsActionStable G (⊥ : AddSubgroup A) := by
  intro g x hx
  rw [AddSubgroup.mem_bot] at hx
  subst hx
  rw [smul_zero]
  exact AddSubgroup.zero_mem _

theorem isActionStable_top : IsActionStable G (⊤ : AddSubgroup A) := by
  intro _ _ _
  exact AddSubgroup.mem_top _

theorem IsActionStable.inf {Lambda Mu : AddSubgroup A}
    (hL : IsActionStable G Lambda) (hM : IsActionStable G Mu) :
    IsActionStable G (Lambda ⊓ Mu) := by
  intro g x hx
  exact ⟨hL g hx.1, hM g hx.2⟩

theorem IsActionStable.iInf {ι : Type*} {Lambda : ι → AddSubgroup A}
    (hL : ∀ i, IsActionStable G (Lambda i)) :
    IsActionStable G (⨅ i, Lambda i) := by
  intro g x hx
  rw [AddSubgroup.mem_iInf] at hx ⊢
  exact fun i => hL i g (hx i)

/-- **Generator reduction.**  A group action stabilizes a generated subgroup as soon as it moves
each generator into it. -/
theorem isActionStable_closure {S : Set A}
    (h : ∀ (g : G), ∀ x ∈ S, g • x ∈ AddSubgroup.closure S) :
    IsActionStable G (AddSubgroup.closure S) := by
  intro g x hx
  have hle : AddSubgroup.closure S ≤
      (AddSubgroup.closure S).comap (DistribSMul.toAddMonoidHom A g) :=
    (AddSubgroup.closure_le _).mpr fun y hy => h g y hy
  exact hle hx

theorem IsActionStable.sup {Lambda Mu : AddSubgroup A}
    (hL : IsActionStable G Lambda) (hM : IsActionStable G Mu) :
    IsActionStable G (Lambda ⊔ Mu) := by
  intro g x hx
  rw [AddSubgroup.mem_sup] at hx ⊢
  obtain ⟨y, hy, z, hz, rfl⟩ := hx
  exact ⟨g • y, hL g hy, g • z, hM g hz, (smul_add g y z).symm⟩

/-! ## The prime-log lattice -/

variable {Greal : Type*} [Group Greal] [DistribMulAction Greal ℝ]

/-- Stability of the prime-log lattice reduces to the prime logarithms. -/
theorem isActionStable_primeLogLattice_of_smul_primeLog
    (h : ∀ (g : Greal) (p : ℕ), p.Prime → g • Real.log p ∈ primeLogLattice) :
    IsActionStable Greal primeLogLattice := by
  apply isActionStable_closure
  intro g x hx
  obtain ⟨p, hp, rfl⟩ := hx
  exact h g p hp

/-- Gauge invariance of the prime-log integrality gate, with stability reduced to the prime
logarithms. -/
theorem gaugeUpdate_isPrimeLogIntegral_iff_of_smul_primeLog
    (h : ∀ (g : Greal) (p : ℕ), p.Prime → g • Real.log p ∈ primeLogLattice)
    (omega : Greal → Greal → ℝ) {b : Greal → ℝ}
    (hb : ∀ g, b g ∈ primeLogLattice) :
    IsPrimeLogIntegral (gaugeUpdate omega b) ↔ IsPrimeLogIntegral omega :=
  gaugeUpdate_isPrimeLogIntegral_iff
    (isActionStable_primeLogLattice_of_smul_primeLog h) omega hb

/-- Resection invariance of the prime-log integrality gate, with stability reduced to the prime
logarithms. -/
theorem resection_isPrimeLogIntegral_iff_of_smul_primeLog
    (D : SectionDefect Greal ℝ)
    (h : ∀ (g : Greal) (p : ℕ), p.Prime → g • Real.log p ∈ primeLogLattice)
    {b : Greal → ℝ} (hb : ∀ g, b g ∈ primeLogLattice) :
    IsPrimeLogIntegral (D.resection b).defect ↔ IsPrimeLogIntegral D.defect :=
  D.resection_isPrimeLogIntegral_iff
    (isActionStable_primeLogLattice_of_smul_primeLog h) hb

/-- The resected lattice class of a prime-log section defect, with stability reduced to the prime
logarithms. -/
theorem resection_isLatticeClass_of_primeLogFormula_of_smul_primeLog
    (D : SectionDefect Greal ℝ)
    (h : ∀ (g : Greal) (p : ℕ), p.Prime → g • Real.log p ∈ primeLogLattice)
    {b : Greal → ℝ} (hb : ∀ g, b g ∈ primeLogLattice)
    (formula : PrimeLogCochainFormula D.defect) :
    IsLatticeClass primeLogLattice (D.resection b).obstruction :=
  D.resection_isLatticeClass_of_primeLogFormula
    (isActionStable_primeLogLattice_of_smul_primeLog h) hb formula

end RHTower

end GaloisForLFunctions
