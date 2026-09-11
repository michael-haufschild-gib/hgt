import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Module

/-!
# Exact discrete trace-dynamics charge conservation

The bosonic charge is preserved by explicit radial, quartic, Yang--Mills and Myers forces,
including every iterate of their leapfrog maps. Subsystem exchange is classified by the
commutator of squared coordinates. Central force projections preserve the charge.

Source: Singh, arXiv:2609.10571, section 13.2 and equation (87).
-/

set_option autoImplicit false

open scoped BigOperators
namespace GaloisForLFunctions.HTGeometry.TraceDynamics
noncomputable section
variable {A : Type*} [Ring A]
variable {ι : Type*} [Fintype ι]

def charge (q p : ι → A) : A := ∑ i, (q i * p i - p i * q i)

def quarticPairForce (q r : A) : A := q * r * r + r * r * q

def yangMillsPairForce (q r : A) : A :=
  r * (q * r - r * q) - (q * r - r * q) * r

theorem quarticPair_noether (q r : A) :
    (q * quarticPairForce q r - quarticPairForce q r * q) +
      (r * quarticPairForce r q - quarticPairForce r q * r) = 0 := by
  unfold quarticPairForce
  noncomm_ring

theorem yangMillsPair_noether (q r : A) :
    (q * yangMillsPairForce q r - yangMillsPairForce q r * q) +
      (r * yangMillsPairForce r q - yangMillsPairForce r q * r) = 0 := by
  unfold yangMillsPairForce
  noncomm_ring

theorem myersTriple_noether (q r s : A) :
    (q * (r*s-s*r) - (r*s-s*r)*q) +
    (r * (s*q-q*s) - (s*q-q*s)*r) +
    (s * (q*r-r*q) - (q*r-r*q)*s) = 0 := by
  noncomm_ring

variable [Algebra ℂ A]

theorem charge_drift (q p : ι → A) (h : ℂ) :
    charge (fun i => q i + h • p i) p = charge q p := by
  unfold charge
  apply Finset.sum_congr rfl
  intro i _
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm]
  abel

theorem charge_kick_defect (q p f : ι → A) (h : ℂ) :
    charge q (fun i => p i - h • f i) = charge q p - h • charge q f := by
  simp only [charge, mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc,
    Finset.sum_sub_distrib, Finset.smul_sum, smul_sub]
  abel

def quarticForce (q : ι → A) (a b : ι → ℂ) (c : ι → ι → ℂ) (i : ι) : A :=
  a i • q i + b i • (q i * q i * q i) +
    ∑ j, (c i j + c j i) • quarticPairForce (q i) (q j)

theorem charge_quarticForce (q : ι → A) (a b : ι → ℂ) (c : ι → ι → ℂ) :
    charge q (quarticForce q a b c) = 0 := by
  have hexpand : charge q (quarticForce q a b c) =
      ∑ i, ∑ j, (c i j + c j i) •
        (q i * quarticPairForce (q i) (q j) - quarticPairForce (q i) (q j) * q i) := by
    unfold charge quarticForce
    apply Finset.sum_congr rfl
    intro i _
    simp only [mul_add, add_mul, Finset.mul_sum, Finset.sum_mul,
      mul_smul_comm, smul_mul_assoc, smul_sub, Finset.sum_sub_distrib]
    simp only [mul_assoc]
    abel
  rw [hexpand]
  have hswap :
      (∑ i, ∑ j, c j i •
        (q i * quarticPairForce (q i) (q j) - quarticPairForce (q i) (q j) * q i)) =
      -(∑ i, ∑ j, c i j •
        (q i * quarticPairForce (q i) (q j) - quarticPairForce (q i) (q j) * q i)) := by
    rw [Finset.sum_comm]
    simp only [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [eq_neg_of_add_eq_zero_left (quarticPair_noether (q j) (q i)), smul_neg]
  simp only [add_smul, Finset.sum_add_distrib]
  rw [hswap, add_neg_cancel]

theorem quarticKick_conserves_charge (q p : ι → A)
    (a b : ι → ℂ) (c : ι → ι → ℂ) (h : ℂ) :
    charge q (fun i => p i - h • quarticForce q a b c i) = charge q p := by
  rw [charge_kick_defect, charge_quarticForce, smul_zero, sub_zero]

/-- A momentum kick followed by a drift and a second kick. -/
def leapfrog (a b : ι → ℂ) (c : ι → ι → ℂ) (h : ℂ)
    (z : (ι → A) × (ι → A)) : (ι → A) × (ι → A) :=
  let p := fun i => z.2 i - (h / 2) • quarticForce z.1 a b c i
  let q := fun i => z.1 i + h • p i
  (q, fun i => p i - (h / 2) • quarticForce q a b c i)

theorem leapfrog_conserves_charge (a b : ι → ℂ) (c : ι → ι → ℂ) (h : ℂ)
    (z : (ι → A) × (ι → A)) :
    charge (leapfrog a b c h z).1 (leapfrog a b c h z).2 = charge z.1 z.2 := by
  simp only [leapfrog]
  rw [quarticKick_conserves_charge, charge_drift, quarticKick_conserves_charge]

theorem leapfrog_iterate_conserves_charge (a b : ι → ℂ) (c : ι → ι → ℂ) (h : ℂ)
    (z : (ι → A) × (ι → A)) (n : ℕ) :
    charge ((leapfrog a b c h)^[n] z).1 ((leapfrog a b c h)^[n] z).2 = charge z.1 z.2 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', leapfrog_conserves_charge, ih]

/-- The two sectors exchange equal and opposite charge under the quartic interaction. -/
theorem quartic_subsystem_exchange (q r p s : A) (h : ℂ) :
    ((q * (p - h • quarticPairForce q r) -
        (p - h • quarticPairForce q r) * q) - (q*p-p*q)) =
    -((r * (s - h • quarticPairForce r q) -
        (s - h • quarticPairForce r q) * r) - (r*s-s*r)) := by
  have hn := congrArg (fun x : A => h • x) (quarticPair_noether q r)
  simp only [mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc]
  simp only [smul_add, smul_sub, smul_zero] at hn
  apply eq_neg_of_add_eq_zero_left
  convert neg_eq_zero.mpr hn using 1
  abel

/-- Scalar trace projections of the forces cannot change the charge defect. -/
theorem charge_centralForce (q f : ι → A) (d : ι → ℂ) :
    charge q (fun i => f i + algebraMap ℂ A (d i)) = charge q f := by
  unfold charge
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_add, add_mul, Algebra.commutes]
  abel

omit [Algebra ℂ A] in
/-- Quartic charge transfer measures commutation of the squared sector coordinates. -/
theorem quartic_subsystem_defect (q r p : A) :
    (q * (p - quarticPairForce q r) - (p - quarticPairForce q r) * q) -
      (q*p-p*q) = -(q*q*(r*r) - r*r*(q*q)) := by
  unfold quarticPairForce
  noncomm_ring

omit [Algebra ℂ A] in
theorem quartic_subsystem_no_exchange_iff (q r p : A) :
    (q * (p - quarticPairForce q r) - (p - quarticPairForce q r) * q) = q*p-p*q ↔
      q*q*(r*r) = r*r*(q*q) := by
  rw [← sub_eq_zero, quartic_subsystem_defect, neg_eq_zero, sub_eq_zero]

/-- Radial terms and pairwise commutator-square forces with arbitrary symmetric coupling data. -/
def yangMillsForce (q : ι → A) (a b : ι → ℂ) (c : ι → ι → ℂ) (i : ι) : A :=
  a i • q i + b i • (q i * q i * q i) +
    ∑ j, (c i j + c j i) • yangMillsPairForce (q i) (q j)

theorem charge_yangMillsForce (q : ι → A) (a b : ι → ℂ) (c : ι → ι → ℂ) :
    charge q (yangMillsForce q a b c) = 0 := by
  have hexpand : charge q (yangMillsForce q a b c) =
      ∑ i, ∑ j, (c i j + c j i) •
        (q i * yangMillsPairForce (q i) (q j) - yangMillsPairForce (q i) (q j) * q i) := by
    unfold charge yangMillsForce
    apply Finset.sum_congr rfl
    intro i _
    simp only [mul_add, add_mul, Finset.mul_sum, Finset.sum_mul,
      mul_smul_comm, smul_mul_assoc, smul_sub, Finset.sum_sub_distrib]
    simp only [mul_assoc]
    abel
  rw [hexpand]
  have hswap :
      (∑ i, ∑ j, c j i •
        (q i * yangMillsPairForce (q i) (q j) - yangMillsPairForce (q i) (q j) * q i)) =
      -(∑ i, ∑ j, c i j •
        (q i * yangMillsPairForce (q i) (q j) - yangMillsPairForce (q i) (q j) * q i)) := by
    rw [Finset.sum_comm]
    simp only [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [eq_neg_of_add_eq_zero_left (yangMillsPair_noether (q j) (q i)), smul_neg]
  simp only [add_smul, Finset.sum_add_distrib]
  rw [hswap, add_neg_cancel]

omit [Algebra ℂ A] in
/-- Charge is additive in the force, so independently invariant interactions can be combined. -/
theorem charge_force_add (q f g : ι → A) :
    charge q (fun i => f i + g i) = charge q f + charge q g := by
  simp only [charge, mul_add, add_mul, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  abel

/-- Simultaneous quartic matter and Yang--Mills geometric interactions conserve total charge. -/
def coupledMatrixForce (q : ι → A) (a b : ι → ℂ) (c d : ι → ι → ℂ) (i : ι) : A :=
  quarticForce q a b c i + yangMillsForce q (fun _ => 0) (fun _ => 0) d i

theorem charge_coupledMatrixForce (q : ι → A) (a b : ι → ℂ) (c d : ι → ι → ℂ) :
    charge q (coupledMatrixForce q a b c d) = 0 := by
  change charge q (fun i => quarticForce q a b c i +
    yangMillsForce q (fun _ => 0) (fun _ => 0) d i) = 0
  rw [charge_force_add, charge_quarticForce, charge_yangMillsForce, add_zero]

def coupledLeapfrog (a b : ι → ℂ) (c d : ι → ι → ℂ) (h : ℂ)
    (z : (ι → A) × (ι → A)) : (ι → A) × (ι → A) :=
  let p := fun i => z.2 i - (h/2) • coupledMatrixForce z.1 a b c d i
  let q := fun i => z.1 i + h • p i
  (q, fun i => p i - (h/2) • coupledMatrixForce q a b c d i)

theorem coupledLeapfrog_conserves_charge (a b : ι → ℂ) (c d : ι → ι → ℂ) (h : ℂ)
    (z : (ι → A) × (ι → A)) :
    charge (coupledLeapfrog a b c d h z).1 (coupledLeapfrog a b c d h z).2 =
      charge z.1 z.2 := by
  simp only [coupledLeapfrog]
  rw [charge_kick_defect, charge_coupledMatrixForce, smul_zero, sub_zero,
    charge_drift, charge_kick_defect, charge_coupledMatrixForce, smul_zero, sub_zero]

theorem coupledLeapfrog_iterate_conserves_charge (a b : ι → ℂ)
    (c d : ι → ι → ℂ) (h : ℂ) (z : (ι → A) × (ι → A)) (n : ℕ) :
    charge ((coupledLeapfrog a b c d h)^[n] z).1 ((coupledLeapfrog a b c d h)^[n] z).2 =
      charge z.1 z.2 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', coupledLeapfrog_conserves_charge, ih]

/-- The cubic Myers force acts on the three geometric sectors and vanishes on matter. -/
def myersForce (q : Fin 4 → A) : Fin 4 → A :=
  ![q 1*q 2-q 2*q 1, q 2*q 0-q 0*q 2, q 0*q 1-q 1*q 0, 0]

omit [Algebra ℂ A] in
theorem charge_myersForce (q : Fin 4 → A) : charge q (myersForce q) = 0 := by
  simp [charge, myersForce, Fin.sum_univ_succ]
  noncomm_ring

theorem charge_force_smul (q f : ι → A) (c : ℂ) :
    charge q (fun i => c • f i) = c • charge q f := by
  simp only [charge, mul_smul_comm, smul_mul_assoc, smul_sub, Finset.smul_sum]

/-- The four-sector force combines radial, quartic, Yang--Mills and Myers terms. -/
def surrogateForce (q : Fin 4 → A) (a b : Fin 4 → ℂ)
    (c d : Fin 4 → Fin 4 → ℂ) (κ : ℂ) (i : Fin 4) : A :=
  coupledMatrixForce q a b c d i + κ • myersForce q i

theorem charge_surrogateForce (q : Fin 4 → A) (a b : Fin 4 → ℂ)
    (c d : Fin 4 → Fin 4 → ℂ) (κ : ℂ) :
    charge q (surrogateForce q a b c d κ) = 0 := by
  change charge q (fun i => coupledMatrixForce q a b c d i + κ • myersForce q i) = 0
  rw [charge_force_add, charge_coupledMatrixForce, charge_force_smul,
    charge_myersForce, smul_zero, add_zero]

def surrogateLeapfrog (a b : Fin 4 → ℂ) (c d : Fin 4 → Fin 4 → ℂ) (κ h : ℂ)
    (z : (Fin 4 → A) × (Fin 4 → A)) : (Fin 4 → A) × (Fin 4 → A) :=
  let p := fun i => z.2 i - (h/2) • surrogateForce z.1 a b c d κ i
  let q := fun i => z.1 i + h • p i
  (q, fun i => p i - (h/2) • surrogateForce q a b c d κ i)

theorem surrogateLeapfrog_conserves_charge (a b : Fin 4 → ℂ)
    (c d : Fin 4 → Fin 4 → ℂ) (κ h : ℂ) (z : (Fin 4 → A) × (Fin 4 → A)) :
    charge (surrogateLeapfrog a b c d κ h z).1 (surrogateLeapfrog a b c d κ h z).2 =
      charge z.1 z.2 := by
  simp only [surrogateLeapfrog]
  rw [charge_kick_defect, charge_surrogateForce, smul_zero, sub_zero,
    charge_drift, charge_kick_defect, charge_surrogateForce, smul_zero, sub_zero]

theorem surrogateLeapfrog_iterate_conserves_charge (a b : Fin 4 → ℂ)
    (c d : Fin 4 → Fin 4 → ℂ) (κ h : ℂ) (z : (Fin 4 → A) × (Fin 4 → A)) (n : ℕ) :
    charge ((surrogateLeapfrog a b c d κ h)^[n] z).1
        ((surrogateLeapfrog a b c d κ h)^[n] z).2 = charge z.1 z.2 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', surrogateLeapfrog_conserves_charge, ih]

end
end GaloisForLFunctions.HTGeometry.TraceDynamics
