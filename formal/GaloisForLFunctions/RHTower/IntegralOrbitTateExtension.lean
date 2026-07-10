import GaloisForLFunctions.RHTower.FESemilinearTwoTorsionExtension

/-!
# Integral Tate descent of the two-torsion extension residue

Local rational Ext and its FE-Witt image are blind to whether reflection fixes a germ or swaps two
germs.  The missing distinction appears after retaining the canonical integral residue lattice.

For a fixed reflection orbit, the stabilizer `C₂` acts trivially on `ℤ`; its norm is `n |-> 2n`, so
the degree-zero Tate residue is reduction modulo two.  The unit extension residue `1` survives.

For a free two-point orbit, the residue lattice is the swap module `ℤ²`.  Every invariant pair is
diagonal and every diagonal pair `(c,c)` is the norm of `(c,0)`, so the free-orbit Tate quotient is
zero.  In particular the unit residue pair `(1,1)` dies.

The canonical integral matrix `[[X^m,1],[0,X]]` base-changes to the rational FE-semilinear unit
extension already constructed.  Thus integral orbit descent produces a fixed-vs-free invariant from
the same genuine extension, without a carrier, cutoff, or factorwise divisor source.
-/

noncomputable section
namespace RHTower

open Matrix Polynomial

/-- Norm on the integral residue lattice at a fixed reflection germ. -/
def fixedOrbitNorm (n : ℤ) : ℤ := n + n

/-- Degree-zero fixed-orbit Tate charge. -/
def fixedOrbitTateCharge (n : ℤ) : ZMod 2 := n

/-- The fixed-orbit Tate charge vanishes exactly on stabilizer norms. -/
theorem fixedOrbitTateCharge_eq_zero_iff_norm (c : ℤ) :
    fixedOrbitTateCharge c = 0 ↔ ∃ n : ℤ, fixedOrbitNorm n = c := by
  constructor
  · intro h
    have hdvd : (2 : ℤ) ∣ c :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd c 2).mp h
    obtain ⟨n, hn⟩ := hdvd
    refine ⟨n, ?_⟩
    simpa [fixedOrbitNorm, two_mul] using hn.symm
  · rintro ⟨n, rfl⟩
    simp only [fixedOrbitTateCharge, fixedOrbitNorm, Int.cast_add]
    exact CharTwo.add_self_eq_zero _

theorem fixedOrbitTateCharge_one_ne_zero : fixedOrbitTateCharge 1 ≠ 0 := by
  norm_num [fixedOrbitTateCharge]

/-- The reflection action on the residue pair of a free two-point orbit. -/
def freeOrbitSwap (x : ℤ × ℤ) : ℤ × ℤ := (x.2, x.1)

/-- Orbit norm on the free swap module. -/
def freeOrbitNorm (x : ℤ × ℤ) : ℤ × ℤ :=
  (x.1 + x.2, x.1 + x.2)

def IsFreeOrbitInvariant (x : ℤ × ℤ) : Prop := freeOrbitSwap x = x

/-- Every invariant residue on a free orbit is a norm; its degree-zero Tate quotient is zero. -/
theorem freeOrbit_invariant_is_norm {x : ℤ × ℤ} (hx : IsFreeOrbitInvariant x) :
    ∃ y : ℤ × ℤ, freeOrbitNorm y = x := by
  rcases x with ⟨a, b⟩
  simp [IsFreeOrbitInvariant, freeOrbitSwap] at hx
  rw [hx.1]
  exact ⟨(a, 0), by simp [freeOrbitNorm]⟩

theorem freeOrbit_unitPair_invariant : IsFreeOrbitInvariant (1, 1) := by
  rfl

theorem freeOrbit_unitPair_is_norm : ∃ y : ℤ × ℤ, freeOrbitNorm y = (1, 1) :=
  freeOrbit_invariant_is_norm freeOrbit_unitPair_invariant

/-- Integral lattice model of the canonical unit two-torsion extension. -/
def integralUnitTwoTorsionExtension (m : ℕ) :
    Matrix (Fin 2) (Fin 2) (Polynomial ℤ) :=
  !![X ^ m, 1; 0, X]

def integralPolynomialToRational (p : Polynomial ℤ) : Polynomial ℚ :=
  p.map (Int.castRingHom ℚ)

/-- The integral unit extension base-changes to the rational FE-semilinear extension. -/
theorem integralUnitTwoTorsionExtension_baseChange (m : ℕ) :
    (integralUnitTwoTorsionExtension m).map integralPolynomialToRational =
      feUnitTwoTorsionExtension m := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [integralUnitTwoTorsionExtension, integralPolynomialToRational,
      feUnitTwoTorsionExtension, twoTorsionPresentation]

theorem integralUnitTwoTorsionExtension_residue (m : ℕ) :
    (integralUnitTwoTorsionExtension m 0 1).coeff 0 = 1 := by
  simp [integralUnitTwoTorsionExtension]

/-- **Integral fixed/free separation.**  The unit extension has nonzero fixed-orbit Tate charge,
while its invariant residue pair on a free orbit is a norm. -/
theorem integralUnitExtension_tate_separates_fixed_free (m : ℕ) :
    (integralUnitTwoTorsionExtension m 0 1).coeff 0 = 1 ∧
      fixedOrbitTateCharge 1 ≠ 0 ∧
      IsFreeOrbitInvariant (1, 1) ∧
      ∃ y : ℤ × ℤ, freeOrbitNorm y = (1, 1) :=
  ⟨integralUnitTwoTorsionExtension_residue m,
    fixedOrbitTateCharge_one_ne_zero,
    freeOrbit_unitPair_invariant,
    freeOrbit_unitPair_is_norm⟩

end RHTower
