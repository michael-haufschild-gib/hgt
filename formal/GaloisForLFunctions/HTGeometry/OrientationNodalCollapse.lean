import GaloisForLFunctions.HTGeometry.UniversalPrimeOrientationLimit
import GaloisForLFunctions.HTGeometry.PrimeDirichletTailPattern

/-!
# Orientation nodal collapse

Continuous residue deformations must cross the zero-residue wall at every changed sign
coordinate.  The affine chord attains this lower bound exactly.  For the summable universal
prime carrier, global complement has finite coefficient distance but crosses every wall and
collapses through the zero carrier.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Set Topology
open scoped BigOperators

noncomputable section

/-- The coordinates at which a real residue path meets the zero-residue wall. -/
def residuePathNodalSupport {P : Type*} (r : ℝ → P → ℝ) : Set P :=
  {p | ∃ t ∈ Set.Icc (0 : ℝ) 1, r t p = 0}

/-- Every changed orientation coordinate of a continuous residue path crosses its zero wall. -/
theorem orientation_disagreement_subset_residuePathNodalSupport
    {P : Type*} (epsilon delta : P → Bool) (w : P → ℝ) (r : ℝ → P → ℝ)
    (hw : ∀ p, 0 < w p)
    (hr0 : ∀ p, r 0 p = primeDirichletRealSign (epsilon p) * w p)
    (hr1 : ∀ p, r 1 p = primeDirichletRealSign (delta p) * w p)
    (hcontinuous : ∀ p, ContinuousOn (fun t => r t p) (Set.Icc (0 : ℝ) 1)) :
    {p | epsilon p ≠ delta p} ⊆ residuePathNodalSupport r := by
  intro p hp
  simp only [Set.mem_setOf_eq, residuePathNodalSupport]
  cases hepsilon : epsilon p with
  | false =>
      cases hdelta : delta p with
      | false => exact (hp (hepsilon.trans hdelta.symm)).elim
      | true =>
          have h0 := hr0 p
          have h1 := hr1 p
          simp [hepsilon, hdelta, primeDirichletRealSign] at h0 h1
          have hzero : (0 : ℝ) ∈ Set.Icc (r 1 p) (r 0 p) := by
            rw [h0, h1]
            constructor <;> linarith [hw p]
          obtain ⟨t, ht, hrt⟩ :=
            intermediate_value_Icc' (by norm_num : (0 : ℝ) ≤ 1)
              (hcontinuous p) hzero
          exact ⟨t, ht, hrt⟩
  | true =>
      cases hdelta : delta p with
      | false =>
          have h0 := hr0 p
          have h1 := hr1 p
          simp [hepsilon, hdelta, primeDirichletRealSign] at h0 h1
          have hzero : (0 : ℝ) ∈ Set.Icc (r 0 p) (r 1 p) := by
            rw [h0, h1]
            constructor <;> linarith [hw p]
          obtain ⟨t, ht, hrt⟩ :=
            intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 1)
              (hcontinuous p) hzero
          exact ⟨t, ht, hrt⟩
      | true => exact (hp (hepsilon.trans hdelta.symm)).elim

/-- A residue deformation with finite nodal support preserves the orientation tail. -/
theorem primeOrientationsEventuallyEqual_of_finite_residuePathNodalSupport
    {P : Type*} (epsilon delta : P → Bool) (w : P → ℝ) (r : ℝ → P → ℝ)
    (hw : ∀ p, 0 < w p)
    (hr0 : ∀ p, r 0 p = primeDirichletRealSign (epsilon p) * w p)
    (hr1 : ∀ p, r 1 p = primeDirichletRealSign (delta p) * w p)
    (hcontinuous : ∀ p, ContinuousOn (fun t => r t p) (Set.Icc (0 : ℝ) 1))
    (hnodal : (residuePathNodalSupport r).Finite) :
    PrimeOrientationsEventuallyEqual epsilon delta := by
  exact hnodal.subset
    (orientation_disagreement_subset_residuePathNodalSupport
      epsilon delta w r hw hr0 hr1 hcontinuous)

/-- Eventually opposite endpoints on an infinite label set force infinitely many nodal walls. -/
theorem residuePathNodalSupport_infinite_of_eventuallyOpposite
    {P : Type*} [Infinite P]
    (epsilon delta : P → Bool) (w : P → ℝ) (r : ℝ → P → ℝ)
    (hw : ∀ p, 0 < w p)
    (hr0 : ∀ p, r 0 p = primeDirichletRealSign (epsilon p) * w p)
    (hr1 : ∀ p, r 1 p = primeDirichletRealSign (delta p) * w p)
    (hcontinuous : ∀ p, ContinuousOn (fun t => r t p) (Set.Icc (0 : ℝ) 1))
    (hopposite : PrimeOrientationsEventuallyOpposite epsilon delta) :
    (residuePathNodalSupport r).Infinite := by
  have hset : {p | epsilon p ≠ delta p} = {p | epsilon p = delta p}ᶜ := by
    ext p
    simp
  have hdisagreement : {p | epsilon p ≠ delta p}.Infinite := by
    rw [hset]
    exact hopposite.infinite_compl
  exact hdisagreement.mono
    (orientation_disagreement_subset_residuePathNodalSupport
      epsilon delta w r hw hr0 hr1 hcontinuous)

/-- The coefficientwise affine chord between two signed residue palettes. -/
def orientationResidueChord {P : Type*}
    (epsilon delta : P → Bool) (w : P → ℝ) (t : ℝ) (p : P) : ℝ :=
  (1 - t) * (primeDirichletRealSign (epsilon p) * w p) +
    t * (primeDirichletRealSign (delta p) * w p)

@[simp] theorem orientationResidueChord_zero {P : Type*}
    (epsilon delta : P → Bool) (w : P → ℝ) (p : P) :
    orientationResidueChord epsilon delta w 0 p =
      primeDirichletRealSign (epsilon p) * w p := by
  simp [orientationResidueChord]

@[simp] theorem orientationResidueChord_one {P : Type*}
    (epsilon delta : P → Bool) (w : P → ℝ) (p : P) :
    orientationResidueChord epsilon delta w 1 p =
      primeDirichletRealSign (delta p) * w p := by
  simp [orientationResidueChord]

theorem continuous_orientationResidueChord_apply {P : Type*}
    (epsilon delta : P → Bool) (w : P → ℝ) (p : P) :
    Continuous (fun t => orientationResidueChord epsilon delta w t p) := by
  unfold orientationResidueChord
  fun_prop

/-- At the chord midpoint, precisely the changed coordinates are nodal. -/
theorem orientationResidueChord_half_eq_zero_iff {P : Type*}
    (epsilon delta : P → Bool) (w : P → ℝ) (p : P) (hw : 0 < w p) :
    orientationResidueChord epsilon delta w (1 / 2 : ℝ) p = 0 ↔
      epsilon p ≠ delta p := by
  cases hepsilon : epsilon p <;> cases hdelta : delta p <;>
    norm_num [orientationResidueChord, primeDirichletRealSign, hepsilon, hdelta] <;>
    linarith

theorem orientationResidueChord_midpoint_nodalSupport {P : Type*}
    (epsilon delta : P → Bool) (w : P → ℝ) (hw : ∀ p, 0 < w p) :
    {p | orientationResidueChord epsilon delta w (1 / 2 : ℝ) p = 0} =
      {p | epsilon p ≠ delta p} := by
  ext p
  exact orientationResidueChord_half_eq_zero_iff epsilon delta w p (hw p)

@[simp] theorem primeDirichletRealSign_not (b : Bool) :
    primeDirichletRealSign (!b) = -primeDirichletRealSign b := by
  cases b <;> simp [primeDirichletRealSign]

theorem orientationResidueChord_complement {P : Type*}
    (epsilon : P → Bool) (w : P → ℝ) (t : ℝ) (p : P) :
    orientationResidueChord epsilon (fun q => !(epsilon q)) w t p =
      (1 - 2 * t) * (primeDirichletRealSign (epsilon p) * w p) := by
  rw [orientationResidueChord, primeDirichletRealSign_not]
  ring

theorem orientationResidueChord_complement_half {P : Type*}
    (epsilon : P → Bool) (w : P → ℝ) (p : P) :
    orientationResidueChord epsilon (fun q => !(epsilon q)) w (1 / 2 : ℝ) p = 0 := by
  rw [orientationResidueChord_complement]
  ring

/-- Complementing every prime orientation negates every signed residue mass. -/
theorem universalPrimeOrientationWeight_complement
    (epsilon : Nat.Primes → Bool) (p : Nat.Primes) :
    universalPrimeOrientationWeight (fun q => !(epsilon q)) p =
      -universalPrimeOrientationWeight epsilon p := by
  cases hepsilon : epsilon p <;>
    simp [universalPrimeOrientationWeight, hepsilon]

/-- Complementing every orientation negates the complete prime Cauchy carrier. -/
theorem universalPrimeOrientationLimit_complement
    (epsilon : Nat.Primes → Bool) (z : ℂ) :
    universalPrimeOrientationLimit (fun p => !(epsilon p)) z =
      -universalPrimeOrientationLimit epsilon z := by
  simp only [universalPrimeOrientationLimit, discreteHerglotz]
  rw [← tsum_neg]
  apply tsum_congr
  intro p
  rw [universalPrimeOrientationWeight_complement]
  push_cast
  ring

/-- The affine chord in the ambient summable carrier space. -/
def universalPrimeOrientationChord
    (epsilon delta : Nat.Primes → Bool) (t : ℝ) (z : ℂ) : ℂ :=
  ((1 - t : ℝ) : ℂ) * universalPrimeOrientationLimit epsilon z +
    (t : ℂ) * universalPrimeOrientationLimit delta z

/-- A global orientation reversal is a scalar chord through the zero carrier. -/
theorem universalPrimeOrientationChord_complement
    (epsilon : Nat.Primes → Bool) (t : ℝ) (z : ℂ) :
    universalPrimeOrientationChord epsilon (fun p => !(epsilon p)) t z =
      ((1 - 2 * t : ℝ) : ℂ) * universalPrimeOrientationLimit epsilon z := by
  rw [universalPrimeOrientationChord,
    universalPrimeOrientationLimit_complement]
  push_cast
  ring

theorem universalPrimeOrientationChord_complement_half
    (epsilon : Nat.Primes → Bool) (z : ℂ) :
    universalPrimeOrientationChord epsilon (fun p => !(epsilon p)) (1 / 2 : ℝ) z = 0 := by
  rw [universalPrimeOrientationChord_complement]
  norm_num

/-- Coefficient `ell-one` distance between two prime orientation carriers. -/
def universalPrimeOrientationCoefficientDistance
    (epsilon delta : Nat.Primes → Bool) : ℝ :=
  ∑' p, |universalPrimeOrientationWeight delta p -
    universalPrimeOrientationWeight epsilon p|

theorem summable_universalPrimeWeight : Summable universalPrimeWeight := by
  apply Summable.of_norm
  simpa [Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (universalPrimeWeight_pos _)] using
    summable_norm_universalPrimeWeight

theorem abs_universalPrimeOrientationWeight_complement_sub
    (epsilon : Nat.Primes → Bool) (p : Nat.Primes) :
    |universalPrimeOrientationWeight (fun q => !(epsilon q)) p -
        universalPrimeOrientationWeight epsilon p| =
      2 * universalPrimeWeight p := by
  rw [universalPrimeOrientationWeight_complement]
  have habs : |universalPrimeOrientationWeight epsilon p| =
      universalPrimeWeight p := by
    cases hepsilon : epsilon p <;>
      simp [universalPrimeOrientationWeight, hepsilon,
        abs_of_pos (universalPrimeWeight_pos p)]
  calc
    |-universalPrimeOrientationWeight epsilon p -
        universalPrimeOrientationWeight epsilon p| =
        2 * |universalPrimeOrientationWeight epsilon p| := by
          rw [show -universalPrimeOrientationWeight epsilon p -
              universalPrimeOrientationWeight epsilon p =
              -(2 * universalPrimeOrientationWeight epsilon p) by ring,
            abs_neg, abs_mul]
          norm_num
    _ = 2 * universalPrimeWeight p := by rw [habs]

/-- Global complement crosses infinitely many walls but has finite exact coefficient distance. -/
theorem universalPrimeOrientationCoefficientDistance_complement
    (epsilon : Nat.Primes → Bool) :
    universalPrimeOrientationCoefficientDistance epsilon (fun p => !(epsilon p)) =
      2 * ∑' p, universalPrimeWeight p := by
  rw [universalPrimeOrientationCoefficientDistance]
  calc
    ∑' p, |universalPrimeOrientationWeight (fun q => !(epsilon q)) p -
        universalPrimeOrientationWeight epsilon p| =
        ∑' p, 2 * universalPrimeWeight p := by
          apply tsum_congr
          exact abs_universalPrimeOrientationWeight_complement_sub epsilon
    _ = 2 * ∑' p, universalPrimeWeight p := by rw [tsum_mul_left]

end

end GaloisForLFunctions.HTGeometry
