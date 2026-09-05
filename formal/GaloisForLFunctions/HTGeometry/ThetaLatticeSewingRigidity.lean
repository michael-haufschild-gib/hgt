import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.Tactic

/-!
# Rank-one lattice sewing and its deformation space

The change of indices `(m,n) -> ((m+n)/2,(m-n)/2)` splits the
integer square lattice into its integer and half-integer sectors. For theta
atoms with fixed spatial frequencies, coefficient-faithful sewing therefore
has two amplitude equations and two heat-rate equations, defined below.

Nonvanishing normalized amplitudes have only a discrete half-sector sign.
Their normalized first-order deformation space is zero; the same rigidity
holds to every formal order. Heat rates have exactly one scalar parameter.
These statements concern the specified rank-one coefficient model, not
deformations of completed arithmetic correspondences or a zeta-zero theorem.
The analytic theta addition formula and extraction of its Fourier coefficients
are not formalized here. This is a classical theta/parallelogram bridge, not
a claim of a new arithmetic obstruction.
-/

namespace GaloisForLFunctions.HTGeometry

/-- Integer-sector index rotation preserves the Gaussian exponent. -/
theorem thetaSewing_integer_square_identity (i j : ℤ) :
    (i + j) ^ 2 + (i - j) ^ 2 = 2 * i ^ 2 + 2 * j ^ 2 := by ring

/-- Odd-sector index rotation has half-integer output frequencies. -/
theorem thetaSewing_half_square_identity (i j : ℤ) :
    ((i + j + 1 : ℤ) : ℚ) ^ 2 + ((i - j : ℤ) : ℚ) ^ 2 =
      2 * ((i : ℚ) + 1 / 2) ^ 2 + 2 * ((j : ℚ) + 1 / 2) ^ 2 := by
  push_cast
  ring

/-- Raw, normalized, nonvanishing amplitudes in the two lattice sectors. -/
def ThetaLatticeAmplitudeSewing {A : Type*} [CommRing A]
    (a b : ℤ → A) : Prop :=
  a 0 = 1 ∧ (∀ n, a n ≠ 0) ∧
    (∀ i j, a (i + j) * a (i - j) = a i * a j) ∧
    (∀ i j, a (i + j + 1) * a (i - j) = b i * b j)

/-- The normalized full-support amplitude space consists of exactly two points. -/
theorem thetaLatticeAmplitudeSewing_iff
    {A : Type*} [CommRing A] [NoZeroDivisors A] [Nontrivial A]
    (a b : ℤ → A) :
    ThetaLatticeAmplitudeSewing a b ↔
      a = (fun _ => 1) ∧ (b = (fun _ => 1) ∨ b = (fun _ => -1)) := by
  constructor
  · rintro ⟨hzero, hne, heven, hodd⟩
    have ha : ∀ n, a n = 1 := by
      intro n
      have h := heven n 0
      simp only [add_zero, sub_zero, hzero] at h
      exact mul_left_cancel₀ (hne n) h
    have hb0 : b 0 * b 0 = 1 := by
      simpa only [ha, one_mul] using (hodd 0 0).symm
    have hb : ∀ n, b n = b 0 := by
      intro n
      have hprod : b n * b 0 = 1 := by
        simpa only [ha, one_mul] using (hodd n 0).symm
      calc
        b n = b n * (b 0 * b 0) := by rw [hb0, mul_one]
        _ = (b n * b 0) * b 0 := (mul_assoc _ _ _).symm
        _ = b 0 := by rw [hprod, one_mul]
    refine ⟨funext ha, ?_⟩
    rcases mul_self_eq_one_iff.mp hb0 with h | h
    · exact Or.inl (funext fun n => (hb n).trans h)
    · exact Or.inr (funext fun n => (hb n).trans h)
  · rintro ⟨rfl, rfl | rfl⟩ <;>
      simp [ThetaLatticeAmplitudeSewing]

/-- First variation of the two sewing equations at their all-one source. -/
def ThetaLatticeAmplitudeTangent (u v : ℤ → ℂ) : Prop :=
  u 0 = 0 ∧
    (∀ i j, u (i + j) + u (i - j) = u i + u j) ∧
    (∀ i j, u (i + j + 1) + u (i - j) = v i + v j)

/-- This source has no nonzero normalized amplitude mode even at first order. -/
theorem thetaLatticeAmplitudeTangent_iff (u v : ℤ → ℂ) :
    ThetaLatticeAmplitudeTangent u v ↔ u = 0 ∧ v = 0 := by
  constructor
  · rintro ⟨hzero, heven, hodd⟩
    have hu : ∀ n, u n = 0 := by
      intro n
      have h := heven n 0
      simp only [add_zero, sub_zero, hzero] at h
      linear_combination h
    have hv0 : v 0 = 0 := by
      have h := hodd 0 0
      simp only [hu] at h
      linear_combination (-1 / 2 : ℂ) * h
    refine ⟨funext hu, funext fun n => ?_⟩
    change v n = 0
    have h := hodd n 0
    simp only [hu, hv0] at h
    linear_combination -h
  · rintro ⟨rfl, rfl⟩
    simp [ThetaLatticeAmplitudeTangent]

/-- Formal amplitudes with constant coefficient one cannot leave the theta source
at any order, not just at dual-number order. -/
theorem thetaLattice_formal_amplitudes_rigid
    (a b : ℤ → PowerSeries ℂ)
    (ha : ∀ n, PowerSeries.constantCoeff (a n) = 1)
    (hb : ∀ n, PowerSeries.constantCoeff (b n) = 1)
    (heven : ∀ i j, a (i + j) * a (i - j) = a i * a j)
    (hodd : ∀ i j, a (i + j + 1) * a (i - j) = b i * b j)
    (hzero : a 0 = 1) :
    a = (fun _ => 1) ∧ b = (fun _ => 1) := by
  have hne : ∀ n, a n ≠ 0 := by
    intro n hn
    have hc := ha n
    rw [hn, map_zero] at hc
    exact zero_ne_one hc
  obtain ⟨hA, hB | hB⟩ := (thetaLatticeAmplitudeSewing_iff a b).mp
    ⟨hzero, hne, heven, hodd⟩
  · exact ⟨hA, hB⟩
  · have hc := hb 0
    rw [hB] at hc
    norm_num at hc

/-- Heat-rate sewing retains the same two lattice correspondences and doubles time. -/
def ThetaLatticeRateSewing (q h : ℤ → ℂ) : Prop :=
  q 0 = 0 ∧
    (∀ i j, q (i + j) + q (i - j) = 2 * q i + 2 * q j) ∧
    (∀ i j, q (i + j + 1) + q (i - j) = 2 * h i + 2 * h j)

private theorem integerRate_of_parallelogram
    (q : ℤ → ℂ) (hz : q 0 = 0)
    (heven : ∀ i j, q (i + j) + q (i - j) = 2 * q i + 2 * q j) :
    ∀ n : ℤ, q n = (n : ℂ) ^ 2 * q 1 := by
  have hneg : ∀ n : ℤ, q (-n) = q n := by
    intro n
    have h := heven 0 n
    simp only [zero_add, zero_sub, hz] at h
    linear_combination h
  have hnat : ∀ n : ℕ, q (n : ℤ) = (n : ℂ) ^ 2 * q 1 := by
    apply Nat.twoStepInduction
    · simpa using hz
    · simp
    · intro n hn hn1
      have h := heven ((n : ℤ) + 1) 1
      have hidx : (n : ℤ) + 1 + 1 = ((n + 2 : ℕ) : ℤ) := by omega
      have hidx1 : (n : ℤ) + 1 = ((n + 1 : ℕ) : ℤ) := by omega
      rw [hidx, add_sub_cancel_right, hidx1, hn, hn1] at h
      push_cast at h ⊢
      linear_combination h
  intro n
  cases n with
  | ofNat n => simpa using hnat n
  | negSucc n =>
    have hi : Int.negSucc n = -((n + 1 : ℕ) : ℤ) := by omega
    rw [hi, hneg, hnat]
    push_cast
    ring

/-- Every allowed rank-one heat-rate field is the ordinary quadratic field with
one freely chosen scalar scale. There is no additional frequency-labelled mode. -/
theorem thetaLatticeRateSewing_iff (q h : ℤ → ℂ) :
    ThetaLatticeRateSewing q h ↔
      (∀ n, q n = (n : ℂ) ^ 2 * q 1) ∧
      (∀ n, h n = ((n : ℂ) + 1 / 2) ^ 2 * q 1) := by
  constructor
  · rintro ⟨hz, heven, hodd⟩
    have hq := integerRate_of_parallelogram q hz heven
    have hh0 : h 0 = q 1 / 4 := by
      have hx := hodd 0 0
      norm_num only [zero_add, zero_sub] at hx
      rw [hz] at hx
      linear_combination (-1 / 4 : ℂ) * hx
    refine ⟨hq, fun n => ?_⟩
    have hx := hodd n 0
    simp only [add_zero, sub_zero] at hx
    rw [hq (n + 1), hq n, hh0] at hx
    push_cast at hx
    linear_combination (-1 / 2 : ℂ) * hx
  · rintro ⟨hq, hh⟩
    refine ⟨?_, ?_, ?_⟩
    · simpa using hq 0
    · intro i j
      rw [hq (i + j), hq (i - j), hq i, hq j]
      push_cast
      ring
    · intro i j
      rw [hq (i + j + 1), hq (i - j), hh i, hh j]
      push_cast
      ring

/-- Once the heat scale at integer one is fixed, the entire source-rate field,
including its half-integer sector, is fixed. -/
theorem thetaLattice_rates_fixed_by_one
    (q h q' h' : ℤ → ℂ)
    (hs : ThetaLatticeRateSewing q h)
    (hs' : ThetaLatticeRateSewing q' h') (hone : q 1 = q' 1) :
    q = q' ∧ h = h' := by
  obtain ⟨hq, hh⟩ := (thetaLatticeRateSewing_iff q h).mp hs
  obtain ⟨hq', hh'⟩ := (thetaLatticeRateSewing_iff q' h').mp hs'
  constructor <;> funext n
  · rw [hq, hq', hone]
  · rw [hh, hh', hone]

end GaloisForLFunctions.HTGeometry
