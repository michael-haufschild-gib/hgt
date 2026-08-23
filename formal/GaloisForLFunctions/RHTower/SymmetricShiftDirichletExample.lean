import GaloisForLFunctions.RHTower.SymmetricShiftAnalyticClass
import GaloisForLFunctions.RHTower.SymmetricShiftMultiplicity
import GaloisForLFunctions.RHTower.SymmetricShiftEulerSlopes
import GaloisForLFunctions.RHTower.DirichletCharacterTwoAdicPrimitive
import GaloisForLFunctions.RHTower.DirichletCompletedLConjugate
import GaloisForLFunctions.RHTower.DirichletLZeroExistence
import GaloisForLFunctions.RHTower.MirrorPencil

/-!
# Primitive odd Dirichlet realization of the symmetric-shift boundary

The explicit conductor-four quadratic character gives a closed standard-Gamma example.  Its
completed carrier is entire of order at most one, self-dual with constant root number, and its
symmetric shifts retain the functional equation.  On the Euler half-plane the uncompleted shifted
product is the literal product of two infinite prime Euler logarithms.  At every unramified prime,
the shifted reciprocal roots have moduli `p⁻ᵃ` and `pᵃ`; for `0 < a < 1/2` they satisfy the strict
partial-Ramanujan bound while failing full temperedness.
-/

open Complex Set LSeries
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-- The explicit primitive conductor-four quadratic character is odd. -/
theorem quadraticCharacterFour_odd :
    DirichletCharacter.Odd quadraticCharacterFour := by
  change quadraticCharacterFour (-1 : ZMod 4) = -1
  rw [show (-1 : ZMod 4) = 3 by decide]
  norm_num [quadraticCharacterFour, ZMod.χ₄]

/-- Quadraticity makes the conductor-four character self-dual. -/
theorem quadraticCharacterFour_inv : quadraticCharacterFour⁻¹ = quadraticCharacterFour :=
  quadraticCharacterFour_isQuadratic.inv

/-- Concrete primitive odd completed Dirichlet carrier. -/
def quadraticCharacterFourXi : ℂ → ℂ :=
  dirichletXi quadraticCharacterFour

theorem quadraticCharacterFourXi_differentiable :
    Differentiable ℂ quadraticCharacterFourXi := by
  change Differentiable ℂ (fun s : ℂ =>
    (4 : ℂ) ^ (s / 2) * DirichletCharacter.completedLFunction quadraticCharacterFour s)
  apply Differentiable.mul
  · apply Differentiable.const_cpow (differentiable_id.div_const (2 : ℂ))
    exact Or.inl (by norm_num)
  · exact DirichletCharacter.differentiable_completedLFunction quadraticCharacterFour_ne_one

/-- The conductor-four completed carrier is entire. -/
theorem quadraticCharacterFourXi_analyticOnNhd :
    AnalyticOnNhd ℂ quadraticCharacterFourXi univ := by
  rw [analyticOnNhd_univ_iff_differentiable]
  exact quadraticCharacterFourXi_differentiable

/-- The conductor-four completed carrier has order at most one. -/
theorem quadraticCharacterFourXi_orderOneEnvelope :
    OrderOneEnvelope quadraticCharacterFourXi := by
  have hpow0 := (orderOneEnvelope_natCast_cpow_neg (n := 4) (by norm_num)).comp_affine
    (-(1 / 2 : ℂ)) 0
  have hpow : OrderOneEnvelope (fun s : ℂ => (4 : ℂ) ^ (s / 2)) :=
    hpow0.congr fun s => by
      congr 1
      ring
  have hL : OrderOneEnvelope
      (DirichletCharacter.completedLFunction quadraticCharacterFour) :=
    completedLFunction_orderOneEnvelope quadraticCharacterFour_ne_one
  exact (hpow.mul hL).congr fun s => by
    rfl

/-- Every symmetric shift of the completed conductor-four carrier remains entire. -/
theorem quadraticCharacterFourXi_symmetricShift_analyticOnNhd (a : ℝ) :
    AnalyticOnNhd ℂ
      (symmetricShiftProduct quadraticCharacterFourXi a) univ :=
  analyticOnNhd_symmetricShiftProduct quadraticCharacterFourXi_analyticOnNhd a

/-- Every symmetric shift of the completed conductor-four carrier remains order one. -/
theorem quadraticCharacterFourXi_symmetricShift_orderOneEnvelope (a : ℝ) :
    OrderOneEnvelope (symmetricShiftProduct quadraticCharacterFourXi a) :=
  orderOneEnvelope_symmetricShiftProduct quadraticCharacterFourXi_orderOneEnvelope a

/-- Constant-root-number functional equation for the self-dual conductor-four carrier. -/
theorem quadraticCharacterFourXi_one_sub (s : ℂ) :
    quadraticCharacterFourXi (1 - s) =
      DirichletCharacter.rootNumber quadraticCharacterFour *
        quadraticCharacterFourXi s := by
  have h := dirichletXi_one_sub quadraticCharacterFour_isPrimitive s
  rw [quadraticCharacterFour_inv] at h
  exact h

/-- Schwarz reality of the conductor-four completed carrier. -/
theorem quadraticCharacterFourXi_conj (s : ℂ) :
    quadraticCharacterFourXi ((starRingEnd ℂ) s) =
      (starRingEnd ℂ) (quadraticCharacterFourXi s) := by
  rw [quadraticCharacterFourXi, dirichletXi, dirichletXi, map_mul,
    conj_completedLFunction quadraticCharacterFour_ne_one, quadraticCharacterFour_inv]
  congr 1
  have hpow := natCast_cpow_conj 4 (s / 2)
  rw [map_div₀, map_ofNat] at hpow
  exact hpow

/-- Line-reflection functional equation for the actual primitive odd carrier. -/
theorem quadraticCharacterFourXi_hasLineSchwarzFunctionalEquation :
    hasLineSchwarzFunctionalEquation quadraticCharacterFourXi
      (DirichletCharacter.rootNumber quadraticCharacterFour) := by
  intro s
  unfold lineReflect
  rw [quadraticCharacterFourXi_one_sub, quadraticCharacterFourXi_conj]

/-- Symmetric shifting squares the actual conductor-four root number. -/
theorem quadraticCharacterFourXi_symmetricShift_lineReflect (a : ℝ) :
    hasLineSchwarzFunctionalEquation
      (symmetricShiftProduct quadraticCharacterFourXi a)
      (DirichletCharacter.rootNumber quadraticCharacterFour ^ 2) :=
  hasLineSchwarzFunctionalEquation_symmetricShiftProduct
    quadraticCharacterFourXi_hasLineSchwarzFunctionalEquation a

/-- The completed conductor-four carrier is not the zero function. -/
theorem exists_quadraticCharacterFourXi_ne_zero :
    ∃ s : ℂ, quadraticCharacterFourXi s ≠ 0 := by
  obtain ⟨sigma, _, hsigma⟩ :=
    exists_completedLFunction_ne_zero_ray
      (χ := (quadraticCharacterFour : DirichletCharacter ℂ 4))
  refine ⟨(sigma : ℂ), ?_⟩
  change (4 : ℂ) ^ ((sigma : ℂ) / 2) *
      DirichletCharacter.completedLFunction quadraticCharacterFour (sigma : ℂ) ≠ 0
  exact mul_ne_zero
    (Complex.cpow_ne_zero_iff.mpr (Or.inl (by norm_num))) hsigma

/-- Self-duality forces the actual conductor-four root number to square to one. -/
theorem quadraticCharacterFour_rootNumber_mul_self :
    DirichletCharacter.rootNumber quadraticCharacterFour *
      DirichletCharacter.rootNumber quadraticCharacterFour = 1 := by
  obtain ⟨z, hz⟩ := exists_quadraticCharacterFourXi_ne_zero
  have hfirst := quadraticCharacterFourXi_one_sub z
  have hsecond := quadraticCharacterFourXi_one_sub (1 - z)
  rw [show (1 : ℂ) - (1 - z) = z by ring, hfirst] at hsecond
  apply mul_right_cancel₀ hz
  calc
    (DirichletCharacter.rootNumber quadraticCharacterFour *
        DirichletCharacter.rootNumber quadraticCharacterFour) * quadraticCharacterFourXi z =
      DirichletCharacter.rootNumber quadraticCharacterFour *
        (DirichletCharacter.rootNumber quadraticCharacterFour * quadraticCharacterFourXi z) := by
          ring
    _ = quadraticCharacterFourXi z := hsecond.symm
    _ = 1 * quadraticCharacterFourXi z := by rw [one_mul]

theorem quadraticCharacterFour_rootNumber_eq_one_or_neg_one :
    DirichletCharacter.rootNumber quadraticCharacterFour = 1 ∨
      DirichletCharacter.rootNumber quadraticCharacterFour = -1 :=
  mul_self_eq_one_iff.mp quadraticCharacterFour_rootNumber_mul_self

/-- The actual primitive root number has unit modulus. -/
theorem norm_quadraticCharacterFour_rootNumber :
    ‖DirichletCharacter.rootNumber quadraticCharacterFour‖ = 1 := by
  rcases quadraticCharacterFour_rootNumber_eq_one_or_neg_one with h | h
  · simp [h]
  · simp [h]

/-- The explicit odd character has the standard odd `Gammaℝ(s+1)` factor. -/
theorem quadraticCharacterFour_gammaFactor (s : ℂ) :
    DirichletCharacter.gammaFactor quadraticCharacterFour s = Gammaℝ (s + 1) :=
  quadraticCharacterFour_odd.gammaFactor_def s

/-- The symmetric completion carries the two literal standard shifted Gamma factors. -/
theorem quadraticCharacterFour_symmetricShift_gammaFactors (a : ℝ) (s : ℂ) :
    DirichletCharacter.gammaFactor quadraticCharacterFour (s + (a : ℂ)) *
        DirichletCharacter.gammaFactor quadraticCharacterFour (s - (a : ℂ)) =
      Gammaℝ (s + (a : ℂ) + 1) * Gammaℝ (s - (a : ℂ) + 1) := by
  rw [quadraticCharacterFour_gammaFactor, quadraticCharacterFour_gammaFactor]

/-- Positive shifts strictly below the partial-Ramanujan threshold. -/
abbrev SymmetricSubcriticalPositiveShift := {a : ℝ // 0 < a ∧ a < 1 / 2}

/-- Both standard odd Gamma parameters `(1±a)/2` are strictly positive. -/
theorem symmetricSubcriticalPositiveShift_gamma_parameters_pos
    (a : SymmetricSubcriticalPositiveShift) :
    0 < (1 + a.1) / 2 ∧ 0 < (1 - a.1) / 2 := by
  constructor <;> linarith [a.2.1, a.2.2]

/-- Euler primes unramified for the conductor-four character. -/
abbrev QuadraticCharacterFourUnramifiedPrime := {p : EulerPrime // p.1 ≠ 2}

theorem quadraticCharacterFour_prime_isUnit
    (p : QuadraticCharacterFourUnramifiedPrime) :
    IsUnit ((p.1.1 : ℕ) : ZMod 4) := by
  rw [ZMod.isUnit_iff_coprime, Nat.Prime.coprime_iff_not_dvd p.1.2]
  intro hp4
  have hp22 : p.1.1 ∣ 2 * 2 := by norm_num at hp4 ⊢; exact hp4
  rcases p.1.2.dvd_mul.mp hp22 with hp2 | hp2
  all_goals
    have heq : p.1.1 = 2 :=
      (Nat.dvd_prime Nat.prime_two).mp hp2 |>.resolve_left p.1.2.ne_one
    exact p.2 heq

/-- Actual unramified reciprocal root of the conductor-four Dirichlet factor. -/
def quadraticCharacterFourLocalRoot
    (p : QuadraticCharacterFourUnramifiedPrime) : UnitaryLocalRoot :=
  ⟨quadraticCharacterFour ((p.1.1 : ℕ) : ZMod 4),
    norm_dirichletCharacter_apply quadraticCharacterFour
      (quadraticCharacterFour_prime_isUnit p)⟩

/-- Exact moduli `p⁻ᵃ,pᵃ` of the actual shifted conductor-four reciprocal roots. -/
theorem norm_quadraticCharacterFour_symmetricShiftLocalRoots
    (p : QuadraticCharacterFourUnramifiedPrime) (a : ℝ) :
    ‖quadraticCharacterFour ((p.1.1 : ℕ) : ZMod 4) *
        (((p.1.1 : ℝ) ^ (-a) : ℝ) : ℂ)‖ = (p.1.1 : ℝ) ^ (-a) ∧
      ‖quadraticCharacterFour ((p.1.1 : ℕ) : ZMod 4) *
        (((p.1.1 : ℝ) ^ a : ℝ) : ℂ)‖ = (p.1.1 : ℝ) ^ a := by
  simpa [symmetricShiftLocalRoots, quadraticCharacterFourLocalRoot] using
    norm_symmetricShiftLocalRoots p.1 a (quadraticCharacterFourLocalRoot p)

/-- Exact opposite local logarithmic slopes for the actual conductor-four Euler factor. -/
theorem quadraticCharacterFour_symmetricShiftLocalSlopes
    (p : QuadraticCharacterFourUnramifiedPrime) (a : ℝ) :
    localRootLogSlope p.1
        (quadraticCharacterFour ((p.1.1 : ℕ) : ZMod 4) *
          (((p.1.1 : ℝ) ^ (-a) : ℝ) : ℂ)) = -a ∧
      localRootLogSlope p.1
        (quadraticCharacterFour ((p.1.1 : ℕ) : ZMod 4) *
          (((p.1.1 : ℝ) ^ a : ℝ) : ℂ)) = a := by
  simpa [symmetricShiftLocalRoots, quadraticCharacterFourLocalRoot] using
    localRootLogSlope_symmetricShiftLocalRoots p.1 a
      (quadraticCharacterFourLocalRoot p)

/-- Every positive subcritical shift obeys strict partial Ramanujan exponent `< 1/2`. -/
theorem quadraticCharacterFour_partialRamanujan
    (p : QuadraticCharacterFourUnramifiedPrime)
    (a : SymmetricSubcriticalPositiveShift) :
    max
        |localRootLogSlope p.1
          (quadraticCharacterFour ((p.1.1 : ℕ) : ZMod 4) *
            (((p.1.1 : ℝ) ^ (-a.1) : ℝ) : ℂ))|
        |localRootLogSlope p.1
          (quadraticCharacterFour ((p.1.1 : ℕ) : ZMod 4) *
            (((p.1.1 : ℝ) ^ a.1 : ℝ) : ℂ))| < 1 / 2 := by
  rw [(quadraticCharacterFour_symmetricShiftLocalSlopes p a.1).1,
    (quadraticCharacterFour_symmetricShiftLocalSlopes p a.1).2,
    abs_neg, abs_of_pos a.2.1, max_self]
  exact a.2.2

/-- Horizontal zero displacement equals the largest actual unramified local modulus slope. -/
theorem quadraticCharacterFour_horizontalDisplacement_eq_maxLocalSlope
    (p : QuadraticCharacterFourUnramifiedPrime) (rho : ℂ) (a : ℝ) :
    |(rho + (a : ℂ)).re - rho.re| =
      max
        |localRootLogSlope p.1
          (symmetricShiftLocalRoots p.1 a (quadraticCharacterFourLocalRoot p)).1|
        |localRootLogSlope p.1
          (symmetricShiftLocalRoots p.1 a (quadraticCharacterFourLocalRoot p)).2| := by
  calc
    |(rho + (a : ℂ)).re - rho.re| = |a| := by simp
    _ = _ :=
      (max_abs_localRootLogSlope_symmetricShiftLocalRoots p.1 a
        (quadraticCharacterFourLocalRoot p)).symm

/-- The actual conductor-four local factor is fully tempered exactly at collision. -/
theorem quadraticCharacterFour_symmetricShiftLocalTempered_iff
    (p : QuadraticCharacterFourUnramifiedPrime) (a : ℝ) :
    symmetricShiftLocalTempered p.1 a (quadraticCharacterFourLocalRoot p) ↔ a = 0 :=
  symmetricShiftLocalTempered_iff p.1 a (quadraticCharacterFourLocalRoot p)

/-- Every critical-line zero of the actual carrier produces the reflected off-line pair. -/
theorem quadraticCharacterFourXi_criticalZero_pair_off_critical_line
    {rho : ℂ} (a : ℝ) (hzero : quadraticCharacterFourXi rho = 0)
    (hrho : rho.re = 1 / 2) (ha : a ≠ 0) :
    (symmetricShiftProduct quadraticCharacterFourXi a (rho + (a : ℂ)) = 0 ∧
        symmetricShiftProduct quadraticCharacterFourXi a (rho - (a : ℂ)) = 0) ∧
      ((rho + (a : ℂ)).re ≠ 1 / 2 ∧ (rho - (a : ℂ)).re ≠ 1 / 2) :=
  ⟨symmetricShiftProduct_zero_translates quadraticCharacterFourXi a hzero,
    symmetricShiftProduct_pair_off_critical_line a hrho ha⟩

/-- Exact analytic-order divisor law for the actual completed conductor-four family. -/
theorem analyticOrderAt_quadraticCharacterFourXi_symmetricShiftProduct (a : ℝ) (z : ℂ) :
    analyticOrderAt (symmetricShiftProduct quadraticCharacterFourXi a) z =
      analyticOrderAt quadraticCharacterFourXi (z + (a : ℂ)) +
        analyticOrderAt quadraticCharacterFourXi (z - (a : ℂ)) :=
  analyticOrderAt_symmetricShiftProduct quadraticCharacterFourXi_analyticOnNhd a z

/-- Both translated copies retain at least the original multiplicity. -/
theorem analyticOrderAt_quadraticCharacterFourXi_le_symmetricShiftProduct_pair
    (a : ℝ) (rho : ℂ) :
    analyticOrderAt quadraticCharacterFourXi rho ≤
        analyticOrderAt (symmetricShiftProduct quadraticCharacterFourXi a)
          (rho + (a : ℂ)) ∧
      analyticOrderAt quadraticCharacterFourXi rho ≤
        analyticOrderAt (symmetricShiftProduct quadraticCharacterFourXi a)
          (rho - (a : ℂ)) :=
  analyticOrderAt_le_symmetricShiftProduct_pair quadraticCharacterFourXi_analyticOnNhd a rho

/-- Collision doubles every conductor-four completed zero multiplicity exactly. -/
theorem analyticOrderAt_quadraticCharacterFourXi_symmetricShiftProduct_zero_shift (rho : ℂ) :
    analyticOrderAt (symmetricShiftProduct quadraticCharacterFourXi 0) rho =
      2 * analyticOrderAt quadraticCharacterFourXi rho :=
  analyticOrderAt_symmetricShiftProduct_zero_shift quadraticCharacterFourXi_analyticOnNhd rho

/-- Literal infinite Euler-product identity for the two shifted Dirichlet factors. -/
theorem quadraticCharacterFour_LFunction_symmetricShift_eulerProduct
    (a : SymmetricSubcriticalPositiveShift) {s : ℂ} (hs : 1 + a.1 < s.re) :
    DirichletCharacter.LFunction quadraticCharacterFour (s + (a.1 : ℂ)) *
        DirichletCharacter.LFunction quadraticCharacterFour (s - (a.1 : ℂ)) =
      Complex.exp
          (∑' p : Nat.Primes,
            -Complex.log
              (1 - quadraticCharacterFour ((p.1 : ℕ) : ZMod 4) *
                (p.1 : ℂ) ^ (-(s + (a.1 : ℂ))))) *
        Complex.exp
          (∑' p : Nat.Primes,
            -Complex.log
              (1 - quadraticCharacterFour ((p.1 : ℕ) : ZMod 4) *
                (p.1 : ℂ) ^ (-(s - (a.1 : ℂ))))) := by
  have hplus : 1 < (s + (a.1 : ℂ)).re := by simp; linarith [hs, a.2.1]
  have hminus : 1 < (s - (a.1 : ℂ)).re := by simp; linarith
  rw [DirichletCharacter.LFunction_eq_LSeries quadraticCharacterFour hplus,
    DirichletCharacter.LFunction_eq_LSeries quadraticCharacterFour hminus,
    DirichletCharacter.LSeries_eulerProduct_exp_log quadraticCharacterFour hplus,
    DirichletCharacter.LSeries_eulerProduct_exp_log quadraticCharacterFour hminus]

end

end RHTower
