import Mathlib

/-!
# Sharp local mesh coercivity for physical prime endpoints

The physical prime aperture carrier is a centered step function.  At every interior endpoint,
its global squared `L²` energy contains the two adjacent cell energies.  This file formalizes the
exact two-cell variance identity, its sharp harmonic-mean jump floor, and the finite-mesh lift.

These are the finite algebraic coercivity statements used by the paper theorem
`physical-prime-endpoint-radical-mesh-coercivity`.  This module does not yet define the clipped
logarithmic prime endpoints, prove their jumps nonzero, or identify the finite mesh energy with
the analytic `FCRJ` response.
-/

open scoped BigOperators

namespace RHTower

/-! ## Ordinary-prime endpoint weights -/

/-- Weight carried by either endpoint of the physical ordinary-prime aperture interval. -/
def physicalPrimeEndpointWeight (p : ℕ) : ℝ :=
  Real.log p / (p : ℝ)

/-- Distinct primes have distinct physical endpoint weights.  Equality would exponentiate to
`p^q = q^p`, contradicting unique factorization. -/
theorem physicalPrimeEndpointWeight_ne_of_distinct
    {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    physicalPrimeEndpointWeight p ≠ physicalPrimeEndpointWeight q := by
  intro hweight
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne_zero
  have hcross : Real.log (p : ℝ) * (q : ℝ) =
      Real.log (q : ℝ) * (p : ℝ) := by
    exact (div_eq_div_iff hp0 hq0).mp hweight
  have hlogpow : Real.log ((p : ℝ) ^ q) = Real.log ((q : ℝ) ^ p) := by
    rw [Real.log_pow, Real.log_pow]
    simpa [mul_comm] using hcross
  have hpPowPos : (0 : ℝ) < (p : ℝ) ^ q := by positivity
  have hqPowPos : (0 : ℝ) < (q : ℝ) ^ p := by positivity
  have hpowReal : (p : ℝ) ^ q = (q : ℝ) ^ p := by
    have hexp := congrArg Real.exp hlogpow
    rwa [Real.exp_log hpPowPos, Real.exp_log hqPowPos] at hexp
  have hpowNat : p ^ q = q ^ p := by exact_mod_cast hpowReal
  exact hpq (hp.pow_inj' hq hq.ne_zero hp.ne_zero hpowNat).1

section TwoCell

/-- Exact two-cell variance decomposition.  The second term is the squared weighted mean, so the
first term is the sharp energy forced by the jump `b - a`. -/
theorem twoCellEnergy_eq_harmonicJump_add_weightedMean
    {L R a b : ℝ} (hLR : L + R ≠ 0) :
    L * a ^ 2 + R * b ^ 2 =
      L * R / (L + R) * (b - a) ^ 2 +
        (L * a + R * b) ^ 2 / (L + R) := by
  field_simp [hLR]
  ring

/-- The harmonic jump term is the sharp lower bound for two positive adjacent cells. -/
theorem harmonicJump_le_twoCellEnergy
    {L R a b : ℝ} (hLR : 0 < L + R) :
    L * R / (L + R) * (b - a) ^ 2 ≤ L * a ^ 2 + R * b ^ 2 := by
  rw [twoCellEnergy_eq_harmonicJump_add_weightedMean hLR.ne']
  exact le_add_of_nonneg_right (div_nonneg (sq_nonneg _) hLR.le)

/-- Equality in the sharp two-cell floor occurs exactly when the weighted mean on the two cells
vanishes. -/
theorem twoCellEnergy_eq_harmonicJump_iff
    {L R a b : ℝ} (hLR : 0 < L + R) :
    L * a ^ 2 + R * b ^ 2 = L * R / (L + R) * (b - a) ^ 2 ↔
      L * a + R * b = 0 := by
  rw [twoCellEnergy_eq_harmonicJump_add_weightedMean hLR.ne']
  constructor
  · intro h
    have hres : (L * a + R * b) ^ 2 / (L + R) = 0 := by linarith
    have hsq : (L * a + R * b) ^ 2 = 0 := by
      exact (div_eq_zero_iff.mp hres).resolve_right hLR.ne'
    exact sq_eq_zero_iff.mp hsq
  · intro h
    simp [h]

/-- The harmonic coefficient dominates half the shorter adjacent cell. -/
theorem half_min_le_harmonicCellCoefficient
    {L R : ℝ} (hL : 0 ≤ L) (hR : 0 ≤ R) (hLR : 0 < L + R) :
    min L R / 2 ≤ L * R / (L + R) := by
  rcases le_total L R with hle | hle
  · rw [min_eq_left hle]
    apply (le_div_iff₀ hLR).2
    have hprod : 0 ≤ L * (R - L) := mul_nonneg hL (sub_nonneg.mpr hle)
    nlinarith
  · rw [min_eq_right hle]
    apply (le_div_iff₀ hLR).2
    have hprod : 0 ≤ R * (L - R) := mul_nonneg hR (sub_nonneg.mpr hle)
    nlinarith

/-- The factor `1/2` in the shorter-cell lower bound is attained on two equal cells by the
centered half-interval values `jump/2` and `-jump/2`. -/
theorem equalTwoCell_halfMin_constant_is_sharp (sigma jump : ℝ) :
    sigma * (jump / 2) ^ 2 + sigma * (-jump / 2) ^ 2 =
      sigma / 2 * ((-jump / 2) - jump / 2) ^ 2 := by
  ring

end TwoCell

section FiniteMesh

variable {ι : Type*} [DecidableEq ι]

/-- Squared energy of a finite step mesh: cell length times squared cell value. -/
def finiteStepMeshEnergy
    (cells : Finset ι) (cellLength cellValue : ι → ℝ) : ℝ :=
  ∑ i ∈ cells, cellLength i * (cellValue i) ^ 2

theorem finiteStepMeshEnergy_nonneg
    (cells : Finset ι) (cellLength cellValue : ι → ℝ)
    (hlength : ∀ i ∈ cells, 0 ≤ cellLength i) :
    0 ≤ finiteStepMeshEnergy cells cellLength cellValue := by
  exact Finset.sum_nonneg fun i hi => mul_nonneg (hlength i hi) (sq_nonneg _)

/-- Every pair of distinct mesh cells contributes at least the sharp harmonic-mean energy of
their value jump.  For adjacent cells this is the physical endpoint coercivity law. -/
theorem harmonicJump_le_finiteStepMeshEnergy
    (cells : Finset ι) (cellLength cellValue : ι → ℝ)
    {left right : ι} (hleft : left ∈ cells) (hright : right ∈ cells)
    (hne : left ≠ right)
    (hlength : ∀ i ∈ cells, 0 ≤ cellLength i)
    (hpair : 0 < cellLength left + cellLength right) :
    cellLength left * cellLength right /
          (cellLength left + cellLength right) *
        (cellValue right - cellValue left) ^ 2 ≤
      finiteStepMeshEnergy cells cellLength cellValue := by
  have hsubset : ({left, right} : Finset ι) ⊆ cells := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl
    · exact hleft
    · exact hright
  have hmono :
      (∑ i ∈ ({left, right} : Finset ι),
          cellLength i * (cellValue i) ^ 2) ≤
        finiteStepMeshEnergy cells cellLength cellValue := by
    unfold finiteStepMeshEnergy
    exact Finset.sum_le_sum_of_subset_of_nonneg hsubset fun i hi _ =>
      mul_nonneg (hlength i hi) (sq_nonneg _)
  calc
    cellLength left * cellLength right /
          (cellLength left + cellLength right) *
        (cellValue right - cellValue left) ^ 2 ≤
        cellLength left * (cellValue left) ^ 2 +
          cellLength right * (cellValue right) ^ 2 :=
      harmonicJump_le_twoCellEnergy hpair
    _ = ∑ i ∈ ({left, right} : Finset ι),
          cellLength i * (cellValue i) ^ 2 := by
      simp [hne]
    _ ≤ finiteStepMeshEnergy cells cellLength cellValue := hmono

/-- Coarser but convenient form: half the shorter adjacent cell times the squared jump is bounded
by the total mesh energy. -/
theorem halfMinJump_le_finiteStepMeshEnergy
    (cells : Finset ι) (cellLength cellValue : ι → ℝ)
    {left right : ι} (hleft : left ∈ cells) (hright : right ∈ cells)
    (hne : left ≠ right)
    (hlength : ∀ i ∈ cells, 0 ≤ cellLength i)
    (hpair : 0 < cellLength left + cellLength right) :
    min (cellLength left) (cellLength right) / 2 *
        (cellValue right - cellValue left) ^ 2 ≤
      finiteStepMeshEnergy cells cellLength cellValue := by
  calc
    min (cellLength left) (cellLength right) / 2 *
        (cellValue right - cellValue left) ^ 2 ≤
      cellLength left * cellLength right /
          (cellLength left + cellLength right) *
        (cellValue right - cellValue left) ^ 2 :=
      mul_le_mul_of_nonneg_right
        (half_min_le_harmonicCellCoefficient
          (hlength left hleft) (hlength right hright) hpair)
        (sq_nonneg _)
    _ ≤ finiteStepMeshEnergy cells cellLength cellValue :=
      harmonicJump_le_finiteStepMeshEnergy cells cellLength cellValue
        hleft hright hne hlength hpair

/-- A nonzero jump across two positive mesh cells forces strictly positive total energy.  This is
the finite radical test used by the physical prime-endpoint theorem. -/
theorem finiteStepMeshEnergy_pos_of_nonzero_jump
    (cells : Finset ι) (cellLength cellValue : ι → ℝ)
    {left right : ι} (hleft : left ∈ cells) (hright : right ∈ cells)
    (hne : left ≠ right)
    (hlength : ∀ i ∈ cells, 0 ≤ cellLength i)
    (hleftPos : 0 < cellLength left) (hrightPos : 0 < cellLength right)
    (hjump : cellValue right - cellValue left ≠ 0) :
    0 < finiteStepMeshEnergy cells cellLength cellValue := by
  have hcoefficient :
      0 < cellLength left * cellLength right /
        (cellLength left + cellLength right) :=
    div_pos (mul_pos hleftPos hrightPos) (add_pos hleftPos hrightPos)
  have hjumpSq : 0 < (cellValue right - cellValue left) ^ 2 :=
    sq_pos_of_ne_zero hjump
  exact lt_of_lt_of_le (mul_pos hcoefficient hjumpSq)
    (harmonicJump_le_finiteStepMeshEnergy cells cellLength cellValue
      hleft hright hne hlength (add_pos hleftPos hrightPos))

end FiniteMesh

end RHTower
