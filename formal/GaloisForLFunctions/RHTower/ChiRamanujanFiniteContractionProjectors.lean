import GaloisForLFunctions.RHTower.ChiRamanujanThreeFrequencyAtomAction
import Mathlib.Data.Int.Lemmas

/-!
# Exact physical contraction projectors on finite Fourier bands

Finite rational translation averages select equality of the first or
second Fourier coordinate with the third once their denominator exceeds
the band. Their complementary composition removes both contractions and
restores the intersection. The full transverse phase keeps its mixed term.
-/

noncomputable section
open scoped BigOperators
namespace RHTower.BAGTrace

def ramanujanTripleTranslate (v : ℝ × ℝ × ℝ) (t : ℝ) (x : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  (x.1+t*v.1, x.2.1+t*v.2.1, x.2.2+t*v.2.2)

/-- A literal finite rational translation average on periodic tests. -/
def ramanujanTranslationAverage (D : ℕ) (v : ℝ × ℝ × ℝ) :
    ((ℝ × ℝ × ℝ) → ℂ) →ₗ[ℂ] ((ℝ × ℝ × ℝ) → ℂ) where
  toFun F x := (D : ℂ)⁻¹ * ∑ a : Fin D, F (ramanujanTripleTranslate v ((a.val : ℝ)/D) x)
  map_add' F G := by
    ext x
    simp only [Pi.add_apply, Finset.sum_add_distrib]
    ring
  map_smul' c F := by
    ext x
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, ← Finset.mul_sum]
    ring

abbrev ramanujanContract13 (D : ℕ) := ramanujanTranslationAverage D (1,0,-1)
abbrev ramanujanContract23 (D : ℕ) := ramanujanTranslationAverage D (0,1,-1)

/-- Both equality contractions are removed, with their intersection restored. -/
def ramanujanNoncontractingProjector (D : ℕ) :
    ((ℝ × ℝ × ℝ) → ℂ) →ₗ[ℂ] ((ℝ × ℝ × ℝ) → ℂ) :=
  (LinearMap.id - ramanujanContract13 D).comp (LinearMap.id - ramanujanContract23 D)

private theorem phase_translate13 (n : ℤ × ℤ × ℤ) (t : ℝ) (x : ℝ × ℝ × ℝ) :
    ramanujanTripleFourierPhase n (ramanujanTripleTranslate (1,0,-1) t x) =
      ramanujanTripleFourierPhase n x * ramanujanFourierPhase (n.1-n.2.2) t := by
  simp only [ramanujanTripleFourierPhase, ramanujanTripleTranslate, ramanujanFourierPhase,
    ← Complex.exp_add]
  congr 1
  push_cast
  ring

private theorem phase_translate23 (n : ℤ × ℤ × ℤ) (t : ℝ) (x : ℝ × ℝ × ℝ) :
    ramanujanTripleFourierPhase n (ramanujanTripleTranslate (0,1,-1) t x) =
      ramanujanTripleFourierPhase n x * ramanujanFourierPhase (n.2.1-n.2.2) t := by
  simp only [ramanujanTripleFourierPhase, ramanujanTripleTranslate, ramanujanFourierPhase,
    ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem ramanujanContract13_phase {D : ℕ} (hD : D ≠ 0) (n : ℤ × ℤ × ℤ) :
    ramanujanContract13 D (ramanujanTripleFourierPhase n) =
      if D ∣ (n.1-n.2.2).natAbs then ramanujanTripleFourierPhase n else 0 := by
  ext x
  change (D : ℂ)⁻¹ * (∑ a : Fin D,
    ramanujanTripleFourierPhase n (ramanujanTripleTranslate (1,0,-1) ((a.val:ℝ)/D) x)) = _
  simp_rw [phase_translate13]
  rw [← Finset.mul_sum, sum_ramanujanFourierPhase_torsion hD]
  split_ifs <;> simp [hD, mul_comm]

theorem ramanujanContract23_phase {D : ℕ} (hD : D ≠ 0) (n : ℤ × ℤ × ℤ) :
    ramanujanContract23 D (ramanujanTripleFourierPhase n) =
      if D ∣ (n.2.1-n.2.2).natAbs then ramanujanTripleFourierPhase n else 0 := by
  ext x
  change (D : ℂ)⁻¹ * (∑ a : Fin D,
    ramanujanTripleFourierPhase n (ramanujanTripleTranslate (0,1,-1) ((a.val:ℝ)/D) x)) = _
  simp_rw [phase_translate23]
  rw [← Finset.mul_sum, sum_ramanujanFourierPhase_torsion hD]
  split_ifs <;> simp [hD, mul_comm]

theorem ramanujanNoncontractingProjector_phase {D : ℕ} (hD : D ≠ 0) (n : ℤ × ℤ × ℤ) :
    ramanujanNoncontractingProjector D (ramanujanTripleFourierPhase n) =
      if D ∣ (n.1-n.2.2).natAbs ∨ D ∣ (n.2.1-n.2.2).natAbs then 0
      else ramanujanTripleFourierPhase n := by
  have h13 := ramanujanContract13_phase hD n
  have h23 := ramanujanContract23_phase hD n
  by_cases h1 : D ∣ (n.1-n.2.2).natAbs <;>
    by_cases h2 : D ∣ (n.2.1-n.2.2).natAbs <;>
    simp [ramanujanNoncontractingProjector, LinearMap.comp_apply,
      LinearMap.sub_apply, LinearMap.id_apply, h13, h23, h1, h2]

private theorem dvd_natAbs_sub_iff {M p r : ℕ} (hp : p ≤ M) (hr : r ≤ M) :
    M+1 ∣ ((p : ℤ)-(r : ℤ)).natAbs ↔ p=r := by
  constructor
  · intro h
    have hb := Int.natAbs_coe_sub_coe_lt_of_lt (Nat.lt_succ_of_le hp) (Nat.lt_succ_of_le hr)
    have h0 := Int.natAbs_eq_zero.mp (Nat.eq_zero_of_dvd_of_lt h hb)
    exact_mod_cast sub_eq_zero.mp h0
  · rintro rfl
    simp

/-- On the entire covered band the rational translation projector has exactly
the two physical equality exclusions, with no congruence aliases. -/
theorem ramanujanNoncontractingProjector_nat_phase (M : ℕ) {p q r : ℕ}
    (hp : p ≤ M) (hq : q ≤ M) (hr : r ≤ M) :
    ramanujanNoncontractingProjector (M+1)
      (ramanujanTripleFourierPhase ((p : ℤ),(q : ℤ),(r : ℤ))) =
      if p=r ∨ q=r then 0 else ramanujanTripleFourierPhase ((p : ℤ),(q : ℤ),(r : ℤ)) := by
  rw [ramanujanNoncontractingProjector_phase (Nat.succ_ne_zero M)]
  simp only [dvd_natAbs_sub_iff hp hr, dvd_natAbs_sub_iff hq hr]

/-- The complete dual physical phase, with its transverse variable retained. -/
theorem ramanujan_physical_phase_completion (p q r x y z : ℝ) (hr : r ≠ 0) :
    p*q/r+x*p+y*q+z*r = (p+y*r)*(q+x*r)/r+(z-x*y)*r := by
  field_simp [hr]
  ring

/-- Simultaneous contraction translations retain the mixed transverse term. -/
theorem ramanujan_transverse_double_shift (x y z a b : ℝ) :
    (z-a-b)-(x+a)*(y+b) = (z-x*y)-(1+y)*a-(1+x)*b-a*b := by
  ring

end RHTower.BAGTrace
