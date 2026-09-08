import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

/-!
# The Josephson supercharge on finite Fourier series

The circuit supercharge in arXiv:2405.03454, Supplement IV, acts on the
finite Fourier core `ℤ →₀ ℂ`. Charge, harmonic shifts, half-turn, and reflection
are constructed explicitly; their commutation relations are proved on that core.
-/

noncomputable section
namespace HTGeometry

abbrev CoppoFourierCore := ℤ →₀ ℂ
abbrev CoppoFourierEnd := Module.End ℂ CoppoFourierCore

/-- Multiplication by the `k`th Fourier harmonic. -/
def coppoFourierShift (k : ℤ) : CoppoFourierEnd :=
  Finsupp.lmapDomain ℂ ℂ (fun n => n + k)

/-- Charge acts by the integer Fourier frequency. -/
def coppoFourierCharge : CoppoFourierEnd :=
  Finsupp.linearCombination ℂ (fun n : ℤ => (n : ℂ) • Finsupp.single n 1)

/-- Half-turn translation on the Fourier core. -/
def coppoFourierHalfTurn : CoppoFourierEnd :=
  Finsupp.linearCombination ℂ (fun n : ℤ => (-1 : ℂ) ^ n • Finsupp.single n 1)

/-- Reflection of the phase coordinate reverses Fourier frequency. -/
def coppoFourierReflection : CoppoFourierEnd := Finsupp.lmapDomain ℂ ℂ (fun n : ℤ => -n)

@[simp] theorem coppoFourierShift_basis (k n : ℤ) :
    coppoFourierShift k (Finsupp.single n 1) = Finsupp.single (n + k) 1 := by
  simp [coppoFourierShift, Finsupp.lmapDomain_apply]

@[simp] theorem coppoFourierCharge_basis (n : ℤ) :
    coppoFourierCharge (Finsupp.single n 1) = (n : ℂ) • Finsupp.single n 1 := by
  simp [coppoFourierCharge]

@[simp] theorem coppoFourierHalfTurn_basis (n : ℤ) :
    coppoFourierHalfTurn (Finsupp.single n 1) = (-1 : ℂ) ^ n • Finsupp.single n 1 := by
  simp [coppoFourierHalfTurn]

@[simp] theorem coppoFourierReflection_basis (n : ℤ) :
    coppoFourierReflection (Finsupp.single n 1) = Finsupp.single (-n) 1 := by
  simp [coppoFourierReflection, Finsupp.lmapDomain_apply]

/-- Harmonic translations compose by addition. -/
theorem coppoFourierShift_mul (k l : ℤ) :
    coppoFourierShift k * coppoFourierShift l = coppoFourierShift (k + l) := by
  apply Finsupp.lhom_ext
  intro n z
  simp [coppoFourierShift, Module.End.mul_apply, Finsupp.lmapDomain_apply, add_assoc, add_comm k]

/-- The zeroth harmonic is the identity. -/
theorem coppoFourierShift_zero : coppoFourierShift 0 = 1 := by
  apply Finsupp.lhom_ext
  intro n z
  simp [coppoFourierShift, Finsupp.lmapDomain_apply]

/-- The exact charge-harmonic commutator on every finite Fourier series. -/
theorem coppoFourierCharge_shift_commutator (k : ℤ) :
    coppoFourierCharge * coppoFourierShift k - coppoFourierShift k * coppoFourierCharge =
      (k : ℂ) • coppoFourierShift k := by
  apply Finsupp.lhom_ext
  intro n z
  rw [show Finsupp.single n z = z • Finsupp.single n 1 by simp, map_smul, map_smul]
  congr 1
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.mul_apply,
    coppoFourierShift_basis, coppoFourierCharge_basis, map_smul, Int.cast_add]
  module

/-- Fourier half-turn is an involution. -/
theorem coppoFourierHalfTurn_sq : coppoFourierHalfTurn ^ 2 = 1 := by
  apply Finsupp.lhom_ext
  intro n z
  rw [show Finsupp.single n z = z • Finsupp.single n 1 by simp, map_smul, map_smul]
  congr 1
  simp only [pow_two, Module.End.mul_apply, coppoFourierHalfTurn_basis, map_smul,
    smul_smul, ← mul_zpow]
  simp

/-- Phase reflection is an involution. -/
theorem coppoFourierReflection_sq : coppoFourierReflection ^ 2 = 1 := by
  apply Finsupp.lhom_ext
  intro n z
  simp [coppoFourierReflection, pow_two, Module.End.mul_apply, Finsupp.lmapDomain_apply]

/-- Half-turn preserves charge. -/
theorem coppoFourierHalfTurn_charge :
    coppoFourierHalfTurn * coppoFourierCharge = coppoFourierCharge * coppoFourierHalfTurn := by
  apply Finsupp.lhom_ext
  intro n z
  rw [show Finsupp.single n z = z • Finsupp.single n 1 by simp, map_smul, map_smul]
  congr 1
  simp only [Module.End.mul_apply, coppoFourierHalfTurn_basis, coppoFourierCharge_basis, map_smul]
  module

/-- Half-turn acts on each harmonic by its integer parity. -/
theorem coppoFourierHalfTurn_shift (k : ℤ) :
    coppoFourierHalfTurn * coppoFourierShift k =
      (-1 : ℂ) ^ k • (coppoFourierShift k * coppoFourierHalfTurn) := by
  apply Finsupp.lhom_ext
  intro n z
  rw [show Finsupp.single n z = z • Finsupp.single n 1 by simp, map_smul, map_smul]
  congr 1
  simp only [Module.End.mul_apply, LinearMap.smul_apply, coppoFourierHalfTurn_basis,
    coppoFourierShift_basis, map_smul, zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0)]
  module

/-- Reflection changes the sign of charge. -/
theorem coppoFourierReflection_charge :
    coppoFourierReflection * coppoFourierCharge = -(coppoFourierCharge * coppoFourierReflection) := by
  apply Finsupp.lhom_ext
  intro n z
  rw [show Finsupp.single n z = z • Finsupp.single n 1 by simp, map_smul, map_smul]
  congr 1
  simp only [Module.End.mul_apply, LinearMap.neg_apply, coppoFourierReflection_basis,
    coppoFourierCharge_basis, map_smul, Int.cast_neg]
  module

/-- Reflection exchanges opposite Fourier harmonics. -/
theorem coppoFourierReflection_shift (k : ℤ) :
    coppoFourierReflection * coppoFourierShift k = coppoFourierShift (-k) * coppoFourierReflection := by
  apply Finsupp.lhom_ext
  intro n z
  simp [coppoFourierReflection, coppoFourierShift, Module.End.mul_apply,
    Finsupp.lmapDomain_apply, add_comm]

/-- The two physical parity symmetries commute. -/
theorem coppoFourierReflection_halfTurn :
    coppoFourierReflection * coppoFourierHalfTurn = coppoFourierHalfTurn * coppoFourierReflection := by
  apply Finsupp.lhom_ext
  intro n z
  rw [show Finsupp.single n z = z • Finsupp.single n 1 by simp, map_smul, map_smul]
  congr 1
  simp only [Module.End.mul_apply, coppoFourierHalfTurn_basis, coppoFourierReflection_basis,
    map_smul, zpow_neg, ← inv_zpow]
  simp

/-- Multiplication by `i a sin(x)` in the Fourier representation. -/
def coppoFourierImaginarySine (a : ℂ) : CoppoFourierEnd :=
  (a / 2) • (coppoFourierShift 1 - coppoFourierShift (-1))

/-- The literal circuit supercharge, with the half-turn acting first. -/
def coppoFourierSupercharge (a : ℂ) : CoppoFourierEnd :=
  (coppoFourierCharge + coppoFourierImaginarySine a) * coppoFourierHalfTurn

/-- Reflection anticommutes with the sine term. -/
theorem coppoFourierReflection_sine (a : ℂ) :
    coppoFourierReflection * coppoFourierImaginarySine a =
      -(coppoFourierImaginarySine a * coppoFourierReflection) := by
  apply Finsupp.lhom_ext
  intro n z
  rw [show Finsupp.single n z = z • Finsupp.single n 1 by simp, map_smul, map_smul]
  congr 1
  simp only [coppoFourierImaginarySine, Module.End.mul_apply, LinearMap.smul_apply,
    LinearMap.sub_apply, LinearMap.neg_apply, map_smul, map_sub,
    coppoFourierReflection_basis, coppoFourierShift_basis]
  simp only [neg_add_rev, add_comm (-1 : ℤ), add_comm (1 : ℤ), neg_neg]
  module

/-- The circuit supercharge reverses reflection parity on its actual Fourier core. -/
theorem coppoFourierSupercharge_anticommutes (a : ℂ) :
    coppoFourierReflection * coppoFourierSupercharge a =
      -(coppoFourierSupercharge a * coppoFourierReflection) := by
  apply Finsupp.lhom_ext
  intro n z
  rw [show Finsupp.single n z = z • Finsupp.single n 1 by simp, map_smul, map_smul]
  congr 1
  simp only [coppoFourierSupercharge, coppoFourierImaginarySine, Module.End.mul_apply,
    LinearMap.add_apply, LinearMap.sub_apply, LinearMap.neg_apply, LinearMap.smul_apply,
    coppoFourierHalfTurn_basis, coppoFourierReflection_basis, coppoFourierCharge_basis,
    coppoFourierShift_basis, map_smul, map_add, map_sub, Int.cast_neg, zpow_neg, ← inv_zpow]
  simp only [inv_neg, inv_one, neg_add_rev, add_comm (1 : ℤ), neg_neg]
  simp only [add_comm (-1 : ℤ)]
  module

/-- The shifted supersymmetric Josephson Hamiltonian on finite Fourier series. -/
def coppoFourierCircuitHamiltonian (a : ℂ) : CoppoFourierEnd :=
  coppoFourierCharge ^ 2 - (a / 2) • (coppoFourierShift 1 + coppoFourierShift (-1)) -
    (a ^ 2 / 4) • (coppoFourierShift 2 + coppoFourierShift (-2)) + (a ^ 2 / 2) • 1

/-- The circuit supercharge squares to the literal two-harmonic Hamiltonian. -/
theorem coppoFourierSupercharge_sq (a : ℂ) :
    coppoFourierSupercharge a ^ 2 = coppoFourierCircuitHamiltonian a := by
  apply Finsupp.lhom_ext
  intro n z
  rw [show Finsupp.single n z = z • Finsupp.single n 1 by simp, map_smul, map_smul]
  congr 1
  simp only [coppoFourierSupercharge, coppoFourierImaginarySine,
    coppoFourierCircuitHamiltonian, pow_two, Module.End.mul_apply,
    LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    coppoFourierHalfTurn_basis, coppoFourierCharge_basis, coppoFourierShift_basis,
    map_smul, map_add, map_sub, Int.cast_add, Int.cast_neg, Int.cast_one,
    zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0), zpow_one, zpow_neg_one,
    inv_neg, inv_one]
  simp only [add_assoc, show (1 : ℤ) + 1 = 2 from rfl,
    show (1 : ℤ) + -1 = 0 from rfl, show (-1 : ℤ) + 1 = 0 from rfl,
    show (-1 : ℤ) + -1 = -2 from rfl, add_zero, Module.End.one_apply]
  have hparity : (-1 : ℂ) ^ n * (-1 : ℂ) ^ n = 1 := by rw [← mul_zpow]; simp
  have hp : ((-1 : ℂ) ^ n) ^ 2 = 1 := by simpa only [pow_two] using hparity
  match_scalars <;> ring_nf <;> simp [hp]

/-- Projection onto even (`false`) or odd (`true`) reflection parity. -/
def coppoFourierParityProjector (odd : Bool) : CoppoFourierEnd :=
  (1 / 2 : ℂ) • (1 + (if odd then (-1 : ℂ) else 1) • coppoFourierReflection)

/-- Both actual reflection-parity sectors are projections. -/
theorem coppoFourierParityProjector_sq (odd : Bool) :
    coppoFourierParityProjector odd ^ 2 = coppoFourierParityProjector odd := by
  apply LinearMap.ext
  intro v
  have hh := congrArg (fun T : CoppoFourierEnd => T v) coppoFourierReflection_sq
  simp only [pow_two, Module.End.mul_apply, Module.End.one_apply] at hh
  cases odd <;>
    simp only [coppoFourierParityProjector, Bool.false_eq_true, ↓reduceIte,
      pow_two, Module.End.mul_apply, LinearMap.smul_apply, LinearMap.add_apply,
      Module.End.one_apply, map_smul, map_add, hh] <;> module

/-- Every finite Fourier series splits into its two reflection parities. -/
theorem coppoFourierParityProjector_partition :
    coppoFourierParityProjector false + coppoFourierParityProjector true = 1 := by
  unfold coppoFourierParityProjector
  simp only [Bool.false_eq_true, ↓reduceIte]
  module

/-- Charge switches reflection parity. -/
theorem coppoFourierCharge_switches_parity (odd : Bool) :
    coppoFourierParityProjector odd * coppoFourierCharge =
      coppoFourierCharge * coppoFourierParityProjector (!odd) := by
  apply LinearMap.ext
  intro v
  have hc := congrArg (fun T : CoppoFourierEnd => T v) coppoFourierReflection_charge
  simp only [Module.End.mul_apply, LinearMap.neg_apply] at hc
  cases odd <;>
    simp only [coppoFourierParityProjector, Bool.false_eq_true, ↓reduceIte,
      Bool.not_false, Bool.not_true, Module.End.mul_apply, LinearMap.smul_apply,
      LinearMap.add_apply, Module.End.one_apply, map_smul, map_add, hc] <;> module

/-- The literal circuit supercharge switches the same parity sectors. -/
theorem coppoFourierSupercharge_switches_parity (a : ℂ) (odd : Bool) :
    coppoFourierParityProjector odd * coppoFourierSupercharge a =
      coppoFourierSupercharge a * coppoFourierParityProjector (!odd) := by
  apply LinearMap.ext
  intro v
  have hc := congrArg (fun T : CoppoFourierEnd => T v) (coppoFourierSupercharge_anticommutes a)
  simp only [Module.End.mul_apply, LinearMap.neg_apply] at hc
  cases odd <;>
    simp only [coppoFourierParityProjector, Bool.false_eq_true, ↓reduceIte,
      Bool.not_false, Bool.not_true, Module.End.mul_apply, LinearMap.smul_apply,
      LinearMap.add_apply, Module.End.one_apply, map_smul, map_add, hc] <;> module

/-- The two-harmonic Hamiltonian preserves reflection parity. -/
theorem coppoFourierCircuitHamiltonian_reflection (a : ℂ) :
    coppoFourierReflection * coppoFourierCircuitHamiltonian a =
      coppoFourierCircuitHamiltonian a * coppoFourierReflection := by
  have hc (v : CoppoFourierCore) :=
    congrArg (fun T : CoppoFourierEnd => T v) (coppoFourierSupercharge_anticommutes a)
  simp only [Module.End.mul_apply, LinearMap.neg_apply] at hc
  rw [← coppoFourierSupercharge_sq]
  apply LinearMap.ext
  intro v
  simp only [pow_two, Module.End.mul_apply, hc, map_neg, neg_neg]

end HTGeometry
