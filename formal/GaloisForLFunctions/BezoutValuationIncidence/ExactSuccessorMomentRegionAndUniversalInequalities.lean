import GaloisForLFunctions.BezoutValuationIncidence.SuccessorEnergyRigidityAndParityStability
import GaloisForLFunctions.RHTower.PMRamanujanPeriodDiagonal

/-!
# Exact successor moment region and universal quadratic inequalities

At every sieve level at least six, a prescribed mean `H`, Selberg second moment `S`, and
Bézout successor moment `B` are simultaneously realizable exactly when
`2 * H² ≤ S + B` and `2 * B ≤ S + H²`.

The construction reuses finite Ramanujan multiples inversion and puts independent coordinates
on divisors one, two, and six. After removing the mean, these modes generate the entire cone
`-V ≤ C ≤ V / 2`. Its dual classifies every universal inequality `α * V + β * C ≥ 0`:
it holds exactly when `α - β ≥ 0` and `2 * α + β ≥ 0`.
-/

open Finset ArithmeticFunction GaloisForLFunctions.BiScaleUncertainty RHTower RHTower.Sieve
open scoped BigOperators ArithmeticFunction.Moebius

namespace GaloisForLFunctions.BezoutValuationIncidence

noncomputable section
set_option autoImplicit false

/-- The finite Ramanujan inverse prescribes every Selberg coordinate, with zero outside the cutoff. -/
theorem selbergMultiplesCoord_ramanujan_inverse (N : ℕ) (y : ℕ → ℝ) (e : ℕ) :
    selbergMultiplesCoord N (pmRamanujanResidueCoeff y N) e =
      if e ∈ Finset.Icc 1 N then y e else 0 := by
  by_cases he : e ∈ Finset.Icc 1 N
  · rw [if_pos he]
    exact pmRamanujanResidueCoeff_multiples y
      (Finset.mem_Icc.mp he).1 (Finset.mem_Icc.mp he).2
  · rw [if_neg he]
    unfold selbergMultiplesCoord
    apply Finset.sum_eq_zero
    intro d hd
    obtain ⟨hdI, hed⟩ := Finset.mem_filter.mp hd
    obtain ⟨hdpos, hdN⟩ := Finset.mem_Icc.mp hdI
    have hepos : 1 ≤ e := by
      by_contra hn
      have he0 : e = 0 := by omega
      have hd0 : d = 0 := Nat.eq_zero_of_zero_dvd (he0 ▸ hed)
      omega
    exact (he (Finset.mem_Icc.mpr
      ⟨hepos, (Nat.le_of_dvd hdpos hed).trans hdN⟩)).elim

/-- Prescribed coordinates realize the entire Selberg diagonal. -/
theorem selbergForm_ramanujan_inverse (N : ℕ) (y : ℕ → ℝ) :
    selbergTotientDiagonalForm N (pmRamanujanResidueCoeff y N) =
      ∑ e ∈ Finset.Icc 1 N, (Nat.totient e : ℝ) * (y e)^2 := by
  unfold selbergTotientDiagonalForm
  apply Finset.sum_congr rfl
  intro e he
  rw [selbergMultiplesCoord_ramanujan_inverse, if_pos he]

/-- The same prescribed coordinates simultaneously realize the successor diagonal. -/
theorem bezoutForm_ramanujan_inverse (N : ℕ) (y : ℕ → ℝ) :
    bezoutCoprimeQuadraticForm N (pmRamanujanResidueCoeff y N) =
      ∑ e ∈ Finset.Icc 1 N, moebiusReal e * (y e)^2 := by
  rw [bezoutCoprimeQuadraticForm_eq_moebius_diagonal]
  apply Finset.sum_congr rfl
  intro e he
  rw [selbergMultiplesCoord_ramanujan_inverse, if_pos he]

/-- A profile supported on the constant mode and the two extreme successor modes. -/
def successorThreeModeProfile (h a b : ℝ) (e : ℕ) : ℝ :=
  if e = 1 then h else if e = 2 then a else if e = 6 then b else 0

/-- Exact diagonal evaluation of a three-mode profile at every level at least six. -/
theorem sum_successorThreeModeProfile_sq (N : ℕ) (w : ℕ → ℝ) (h a b : ℝ) :
    (∑ e ∈ Finset.Icc 1 (N + 6), w e * (successorThreeModeProfile h a b e)^2) =
      w 1 * h^2 + w 2 * a^2 + w 6 * b^2 := by
  have hterm (e : ℕ) : w e * (successorThreeModeProfile h a b e)^2 =
      (if e = 1 then w 1 * h^2 else 0) +
        (if e = 2 then w 2 * a^2 else 0) +
          (if e = 6 then w 6 * b^2 else 0) := by
    by_cases h1 : e = 1
    · subst e
      simp [successorThreeModeProfile]
    by_cases h2 : e = 2
    · subst e
      simp [successorThreeModeProfile]
    by_cases h6 : e = 6
    · subst e
      simp [successorThreeModeProfile]
    simp [successorThreeModeProfile, h1, h2, h6]
  simp_rw [hterm, Finset.sum_add_distrib]
  have h1 : 1 ≤ N + 6 := by omega
  have h2 : 2 ≤ N + 6 := by omega
  have h6 : 6 ≤ N + 6 := by omega
  simp [h1, h2, h6]

/-- A finite sieve weight realizing the constant mode and both extreme successor modes. -/
def successorThreeModeWeight (N : ℕ) (h a b : ℝ) : ℕ → ℝ :=
  pmRamanujanResidueCoeff (successorThreeModeProfile h a b) (N + 6)

/-- The three-mode weight realizes an arbitrary mean and two independent nonnegative variances. -/
theorem successorThreeModeWeight_moments (N : ℕ) (h a b : ℝ) :
    finiteHarmonicSum (N + 6) (successorThreeModeWeight N h a b) = h ∧
      selbergTotientDiagonalForm (N + 6) (successorThreeModeWeight N h a b) =
        h^2 + a^2 + 2 * b^2 ∧
      bezoutCoprimeQuadraticForm (N + 6) (successorThreeModeWeight N h a b) =
        h^2 - a^2 + b^2 := by
  have hphi6 : Nat.totient 6 = 2 := wall11_totient_degeneracy_broken_by_bezout.2.1
  have hmu1 : moebiusReal 1 = 1 := by simp [moebiusReal]
  have hmu2 : moebiusReal 2 = -1 := by
    simp [moebiusReal, ArithmeticFunction.moebius_apply_prime Nat.prime_two]
  have hmu6 : moebiusReal 6 = 1 := by
    have hgap := wall11_totient_degeneracy_broken_by_bezout.2.2.2
    rw [hphi6] at hgap
    change (2 : ℝ) - moebiusReal 6 = 1 at hgap
    linarith
  refine ⟨?_, ?_, ?_⟩
  · rw [← selbergMultiplesCoord_one_eq_finiteHarmonicSum]
    unfold successorThreeModeWeight
    rw [selbergMultiplesCoord_ramanujan_inverse, if_pos (by simp)]
    simp [successorThreeModeProfile]
  · unfold successorThreeModeWeight
    rw [selbergForm_ramanujan_inverse, sum_successorThreeModeProfile_sq]
    simp [hphi6]
  · unfold successorThreeModeWeight
    rw [bezoutForm_ramanujan_inverse, sum_successorThreeModeProfile_sq]
    (simp [hmu1, hmu2, hmu6]; ring)

/-- Removing the mean leaves exactly the two independent endpoint modes. -/
theorem successorThreeModeWeight_variance_covariance (N : ℕ) (h a b : ℝ) :
    sieveVariance (N + 6) (successorThreeModeWeight N h a b) = a^2 + 2 * b^2 ∧
      bezoutCoprimeQuadraticForm (N + 6) (successorThreeModeWeight N h a b) -
        (finiteHarmonicSum (N + 6) (successorThreeModeWeight N h a b))^2 = -a^2 + b^2 := by
  obtain ⟨hh, hs, hb⟩ := successorThreeModeWeight_moments N h a b
  have hv := selberg_eq_harmonic_sq_add_variance (N + 6) (successorThreeModeWeight N h a b)
  rw [hh, hs] at hv
  constructor
  · linarith
  · rw [hh, hb]
    ring

/-- Exact joint moment region: the universal successor inequalities are sufficient for realization. -/
theorem exists_sieve_weight_with_moments_iff (N : ℕ) (h s b : ℝ) :
    (∃ c : ℕ → ℝ, finiteHarmonicSum (N + 6) c = h ∧
      selbergTotientDiagonalForm (N + 6) c = s ∧
      bezoutCoprimeQuadraticForm (N + 6) c = b) ↔
      2 * h^2 ≤ s + b ∧ 2 * b ≤ s + h^2 := by
  constructor
  · rintro ⟨c, hh, hs, hb⟩
    obtain ⟨hl, hu⟩ := successor_covariance_bounds (N + 6) c
    have hv := selberg_eq_harmonic_sq_add_variance (N + 6) c
    rw [hh, hs] at hv
    rw [hh, hb] at hl hu
    constructor <;> linarith
  · intro hr
    let a : ℝ := Real.sqrt ((s + h^2 - 2 * b) / 3)
    let z : ℝ := Real.sqrt ((s + b - 2 * h^2) / 3)
    have ha : a^2 = (s + h^2 - 2 * b) / 3 :=
      Real.sq_sqrt (by linarith [hr.2])
    have hz : z^2 = (s + b - 2 * h^2) / 3 :=
      Real.sq_sqrt (by linarith [hr.1])
    obtain ⟨hh, hs, hb⟩ := successorThreeModeWeight_moments N h a z
    refine ⟨successorThreeModeWeight N h a z, hh, hs.trans ?_, hb.trans ?_⟩ <;> linarith

/-- Every universal linear inequality in variance and successor covariance comes from the two endpoints. -/
theorem universal_successor_quadratic_inequality_iff (α β : ℝ) :
    (∀ (N : ℕ) (c : ℕ → ℝ),
      0 ≤ α * sieveVariance N c +
        β * (bezoutCoprimeQuadraticForm N c - (finiteHarmonicSum N c)^2)) ↔
      0 ≤ α - β ∧ 0 ≤ 2 * α + β := by
  constructor
  · intro h
    have htwo := h 6 (successorThreeModeWeight 0 0 1 0)
    have hsix := h 6 (successorThreeModeWeight 0 0 0 1)
    obtain ⟨htV, htC⟩ := successorThreeModeWeight_variance_covariance 0 0 1 0
    obtain ⟨hsV, hsC⟩ := successorThreeModeWeight_variance_covariance 0 0 0 1
    rw [htV, htC] at htwo
    rw [hsV, hsC] at hsix
    constructor <;> nlinarith
  · rintro ⟨hα, hβ⟩ N c
    obtain ⟨hl, hu⟩ := successor_covariance_bounds N c
    have hd : 0 ≤ sieveVariance N c -
        2 * (bezoutCoprimeQuadraticForm N c - (finiteHarmonicSum N c)^2) := by linarith
    have hp : 0 ≤ sieveVariance N c +
        (bezoutCoprimeQuadraticForm N c - (finiteHarmonicSum N c)^2) := by linarith
    have hdprod := mul_nonneg hα hd
    have hpprod := mul_nonneg hβ hp
    nlinarith

end
end GaloisForLFunctions.BezoutValuationIncidence
