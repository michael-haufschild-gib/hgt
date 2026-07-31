import GaloisForLFunctions.RHTower.SeamSpectrumTranscendence
import GaloisForLFunctions.RHTower.WeldClassTable

/-!
# A section defect that fails the prime-log gate

The prime-log gates of the obstruction layer are fail-fast tests: one defect value outside the
prime-log lattice kills every finite prime-log formula.  Nothing in the corpus exhibited such a
value, nor a section defect carrying one.

Both are supplied here.  Because every nonzero element of the prime-log lattice is transcendental,
no nonzero algebraic real lies in it, so the lattice is a proper subgroup of the line and `1` is an
explicit element outside it.  The universal weld cocycle with conversion constant `1` is then a
section defect on the weld group whose obstruction class is nonzero and whose value on the
commuting generator pair is `1`, so it fails both prime-log gates while being a genuine weld.
-/

namespace GaloisForLFunctions.RHTower

noncomputable section

/-! ## The prime-log lattice is a proper subgroup -/

/-- No nonzero algebraic real lies in the prime-log lattice. -/
theorem not_mem_primeLogLattice_of_isAlgebraic {x : ℝ}
    (hx : IsAlgebraic ℚ x) (hx0 : x ≠ 0) : x ∉ primeLogLattice :=
  fun hmem => (weld_spectrum_transcendental x hmem hx0) hx

/-- One is not a prime-log lattice value. -/
theorem one_not_mem_primeLogLattice : (1 : ℝ) ∉ primeLogLattice :=
  not_mem_primeLogLattice_of_isAlgebraic isAlgebraic_one one_ne_zero

/-- The prime-log lattice is a proper subgroup of the line. -/
theorem primeLogLattice_ne_top : primeLogLattice ≠ ⊤ := by
  intro h
  exact one_not_mem_primeLogLattice (h ▸ AddSubgroup.mem_top (1 : ℝ))

/-! ## The universal weld as section-defect data -/

/-- The universal weld cocycle, packaged as carrier-free section-defect data. -/
def weldSectionDefect (θ : ℝ) : SectionDefect WeldGroup ℝ where
  defect := weldCocycle θ
  associative := weldCocycle_isTwoCocycle θ

@[simp] theorem weldSectionDefect_defect (θ : ℝ) :
    (weldSectionDefect θ).defect = weldCocycle θ := rfl

/-- The obstruction class of the weld section defect is nonzero exactly for a nonzero conversion
constant. -/
theorem weldSectionDefect_obstruction_ne_zero_iff (θ : ℝ) :
    (weldSectionDefect θ).obstruction ≠ 0 ↔ θ ≠ 0 :=
  weld_obstruction_ne_zero_iff θ

/-! ## The gate fires on an algebraic conversion constant -/

/-- A nonzero algebraic conversion constant puts the weld defect outside the prime-log lattice at
the generator pair. -/
theorem weldSectionDefect_value_not_mem_primeLogLattice {θ : ℝ}
    (hθ : IsAlgebraic ℚ θ) (hθ0 : θ ≠ 0) :
    (weldSectionDefect θ).defect weldGenD weldGenS ∉ primeLogLattice := by
  rw [weldSectionDefect_defect, weldCocycle_genD_genS]
  exact not_mem_primeLogLattice_of_isAlgebraic hθ hθ0

/-- Hence the finite prime-log formula gate is empty for that weld. -/
theorem isEmpty_primeLogCochainFormula_weldSectionDefect {θ : ℝ}
    (hθ : IsAlgebraic ℚ θ) (hθ0 : θ ≠ 0) :
    IsEmpty (PrimeLogCochainFormula (weldSectionDefect θ).defect) :=
  SectionDefect.no_primeLogFormula_of_value_not_mem (weldSectionDefect θ)
    (weldSectionDefect_value_not_mem_primeLogLattice hθ hθ0)

/-- And so is the prime-indexed formula gate. -/
theorem isEmpty_primeIndexedLogCochainFormula_weldSectionDefect {θ : ℝ}
    (hθ : IsAlgebraic ℚ θ) (hθ0 : θ ≠ 0) :
    IsEmpty (PrimeIndexedLogCochainFormula (weldSectionDefect θ).defect) :=
  SectionDefect.no_primeIndexedFormula_of_value_not_mem (weldSectionDefect θ)
    (weldSectionDefect_value_not_mem_primeLogLattice hθ hθ0)

/-- **The fail-fast gates are non-vacuous.**  There is a section defect on the weld group whose
obstruction class is nonzero — a genuine, ungaugeable weld — and which nevertheless admits no
finite prime-log formula and no prime-indexed log formula.  Nontriviality of the class and failure
of the prime-log gates are therefore compatible, and both are witnessed by the universal weld with
conversion constant one. -/
theorem exists_sectionDefect_obstruction_ne_zero_isEmpty_primeLogGates :
    ∃ D : SectionDefect WeldGroup ℝ,
      D.obstruction ≠ 0 ∧
        IsEmpty (PrimeLogCochainFormula D.defect) ∧
        IsEmpty (PrimeIndexedLogCochainFormula D.defect) :=
  ⟨weldSectionDefect 1,
    (weldSectionDefect_obstruction_ne_zero_iff 1).mpr one_ne_zero,
    isEmpty_primeLogCochainFormula_weldSectionDefect isAlgebraic_one one_ne_zero,
    isEmpty_primeIndexedLogCochainFormula_weldSectionDefect isAlgebraic_one one_ne_zero⟩

end

end GaloisForLFunctions.RHTower
