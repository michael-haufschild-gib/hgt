import Mathlib

/-!
# Scalar whole-grade secular rigidity on coprime residues

This file formalizes the algebraic core of the positive survivor extracted from the
high-grade sieve no-go.

For a finite diagonal-plus-rank-one problem, the secular profile is an exact eigenvector as soon
as its carrier pairing is one.  Any observation whose value on every retained whole grade is a
fixed multiple of that grade's carrier therefore takes the same fixed value on the secular
profile, independently of the selected grades and of the scalar diagonal weights.

For the Boolean sieve, the inverse CRT Fourier value of a canonical grade carrier at a coprime
residue is `σ / (V * sqrtQ)` times its squared carrier mass.  The preceding finite identity then
gives the universal coprime plateau.  The last two results record the sharp boundary: a
non-scalar two-coordinate recentering splits the plateau, and scalarity alone gives no positive
lower bound for the secular root.

This is a finite rigidity/classification theorem.  It does not estimate the RH-equivalent
physical endpoint.
-/

open scoped BigOperators

namespace RHTower

noncomputable section

section FiniteSpike

variable {ι : Type*} [DecidableEq ι]

/-- Secular profile of a finite carrier for a scalar diagonal recentering. -/
def finiteSpikeSecularProfile (s : Finset ι) (w d : ι → ℝ) (lam : ℝ) (i : ι) : ℝ :=
  if i ∈ s then w i / (lam + d i) else 0

/-- Coordinate form of `|w><w| - diag(d)` on the selected finite support. -/
def finiteRankOneMinusDiagonal
    (s : Finset ι) (w d x : ι → ℝ) (i : ι) : ℝ :=
  w i * ∑ j ∈ s, w j * x j - d i * x i

/-- The secular profile vanishes away from the selected grade family. -/
theorem finiteSpikeSecularProfile_eq_zero_of_notMem
    (s : Finset ι) (w d : ι → ℝ) (lam : ℝ) {i : ι} (hi : i ∉ s) :
    finiteSpikeSecularProfile s w d lam i = 0 := by
  simp [finiteSpikeSecularProfile, hi]

/-- The secular equation is exactly the canonical carrier normalization. -/
theorem finiteSpikeSecularProfile_carrierPairing
    (s : Finset ι) (w d : ι → ℝ) (lam : ℝ)
    (hsec : ∑ i ∈ s, w i ^ (2 : ℕ) / (lam + d i) = 1) :
    (∑ i ∈ s, w i * finiteSpikeSecularProfile s w d lam i) = 1 := by
  calc
    (∑ i ∈ s, w i * finiteSpikeSecularProfile s w d lam i) =
        ∑ i ∈ s, w i ^ (2 : ℕ) / (lam + d i) := by
      apply Finset.sum_congr rfl
      intro i hi
      simp only [finiteSpikeSecularProfile, hi, if_true]
      rw [pow_two]
      exact (mul_div_assoc _ _ _).symm
    _ = 1 := hsec

/-- The secular profile is an exact eigenvector of the finite diagonal-plus-rank-one operator. -/
theorem finiteSpikeSecularProfile_eigen
    (s : Finset ι) (w d : ι → ℝ) (lam : ℝ)
    (hden : ∀ i ∈ s, lam + d i ≠ 0)
    (hsec : ∑ i ∈ s, w i ^ (2 : ℕ) / (lam + d i) = 1)
    {i : ι} (hi : i ∈ s) :
    finiteRankOneMinusDiagonal s w d (finiteSpikeSecularProfile s w d lam) i =
      lam * finiteSpikeSecularProfile s w d lam i := by
  unfold finiteRankOneMinusDiagonal
  rw [finiteSpikeSecularProfile_carrierPairing s w d lam hsec]
  simp only [finiteSpikeSecularProfile, hi, if_true, mul_one]
  field_simp [hden i hi]
  ring

/-- Any observation aligned grade-by-grade with the carrier has a universal value on the
secularly normalized profile.  Positivity is not used: this is the exact algebra behind the
coprime plateau. -/
theorem finiteSpikeSecularProfile_alignedTrace
    (s : Finset ι) (w d unitTrace : ι → ℝ) (lam scale : ℝ)
    (halign : ∀ i ∈ s, unitTrace i = scale * w i)
    (hsec : ∑ i ∈ s, w i ^ (2 : ℕ) / (lam + d i) = 1) :
    (∑ i ∈ s, unitTrace i * finiteSpikeSecularProfile s w d lam i) = scale := by
  calc
    (∑ i ∈ s, unitTrace i * finiteSpikeSecularProfile s w d lam i) =
        ∑ i ∈ s, scale * (w i * finiteSpikeSecularProfile s w d lam i) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [halign i hi]
      ring
    _ = scale * ∑ i ∈ s, w i * finiteSpikeSecularProfile s w d lam i := by
      rw [Finset.mul_sum]
    _ = scale := by
      rw [finiteSpikeSecularProfile_carrierPairing s w d lam hsec, mul_one]

end FiniteSpike

section GradeMass

variable {ι : Type*} [DecidableEq ι]

/-- Resolvent trace written directly in terms of whole-grade carrier masses. -/
def gradeResolventTrace
    (s : Finset ι) (gradeValue diagonal : ι → ℝ) (lam : ℝ) : ℝ :=
  ∑ i ∈ s, gradeValue i / (lam + diagonal i)

omit [DecidableEq ι] in
/-- Proportional whole-grade traces stay proportional after every scalar grade resolvent. -/
theorem gradeResolventTrace_eq_scale
    (s : Finset ι) (mass unitValue diagonal : ι → ℝ) (lam scale : ℝ)
    (halign : ∀ i ∈ s, unitValue i = scale * mass i)
    (hsec : gradeResolventTrace s mass diagonal lam = 1) :
    gradeResolventTrace s unitValue diagonal lam = scale := by
  unfold gradeResolventTrace at hsec ⊢
  calc
    (∑ i ∈ s, unitValue i / (lam + diagonal i)) =
        ∑ i ∈ s, scale * (mass i / (lam + diagonal i)) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [halign i hi]
      ring
    _ = scale * ∑ i ∈ s, mass i / (lam + diagonal i) := by
      rw [Finset.mul_sum]
    _ = scale := by rw [hsec, mul_one]

/-- Squared carrier mass of a Boolean ANOVA grade in the sieve normalization. -/
def booleanGradeMass (volume : ℝ) (phi : ι → ℝ) (i : ι) : ℝ :=
  volume ^ (2 : ℕ) / phi i

/-- Inverse CRT Fourier value of the canonical grade carrier at any coprime residue. -/
def booleanGradeCoprimeValue
    (sign volume sqrtQ : ℝ) (phi : ι → ℝ) (i : ι) : ℝ :=
  sign * volume / (sqrtQ * phi i)

omit [DecidableEq ι] in
/-- On every whole Boolean grade, the coprime value is the same fixed multiple of the squared
carrier mass. -/
theorem booleanGradeCoprimeValue_eq_scale_mass
    (sign volume sqrtQ : ℝ) (phi : ι → ℝ)
    (hvolume : volume ≠ 0) (hsqrtQ : sqrtQ ≠ 0) (i : ι) :
    booleanGradeCoprimeValue sign volume sqrtQ phi i =
      sign / (volume * sqrtQ) * booleanGradeMass volume phi i := by
  unfold booleanGradeCoprimeValue booleanGradeMass
  by_cases hphi : phi i = 0
  · simp [hphi]
  · field_simp [hvolume, hsqrtQ, hphi]

omit [DecidableEq ι] in
/-- **Universal coprime plateau.** For any selected family of whole Boolean grades and any scalar
diagonal weights, a secularly normalized positive-line candidate has the same coprime trace
`sign / (volume * sqrtQ)`.  The theorem is conditional only on the exact secular equation, so the
value is independent of the family, the spectral parameter, and the diagonal weights. -/
theorem booleanGrade_scalarRecentering_coprimePlateau
    (s : Finset ι) (phi diagonal : ι → ℝ) (lam sign volume sqrtQ : ℝ)
    (hvolume : volume ≠ 0) (hsqrtQ : sqrtQ ≠ 0)
    (hsec : gradeResolventTrace s (booleanGradeMass volume phi) diagonal lam = 1) :
    gradeResolventTrace s (booleanGradeCoprimeValue sign volume sqrtQ phi) diagonal lam =
      sign / (volume * sqrtQ) := by
  apply gradeResolventTrace_eq_scale s
      (booleanGradeMass volume phi)
      (booleanGradeCoprimeValue sign volume sqrtQ phi)
      diagonal lam (sign / (volume * sqrtQ))
  · intro i _hi
    exact booleanGradeCoprimeValue_eq_scale_mass sign volume sqrtQ phi hvolume hsqrtQ i
  · exact hsec

/-- Exact two-coordinate splitting caused by a non-scalar recentering.  The right side vanishes
only when the two diagonal entries agree (away from the two poles), which is the sharp boundary
of the whole-grade scalar plateau theorem. -/
theorem nonscalarTwoCoordinate_resolventDifference
    (lam a b : ℝ) (ha : lam + a ≠ 0) (hb : lam + b ≠ 0) :
    1 / (lam + a) - 1 / (lam + b) =
      (b - a) / ((lam + a) * (lam + b)) := by
  field_simp [ha, hb]
  ring

/-- Scalar whole-grade structure supplies no positive lower bound for the secular root: in a
one-grade problem of mass `m`, every prescribed `0 < epsilon < m` is the exact secular root for
the positive diagonal `m - epsilon`. -/
theorem oneGrade_secularRoot_can_be_arbitrarilySmall
    {m epsilon : ℝ} (hm : 0 < m) (hepsilon : 0 < epsilon) (hepsilon_m : epsilon < m) :
    0 < epsilon ∧ 0 < m - epsilon ∧
      m / (epsilon + (m - epsilon)) = 1 := by
  refine ⟨hepsilon, sub_pos.mpr hepsilon_m, ?_⟩
  rw [show epsilon + (m - epsilon) = m by ring, div_self (ne_of_gt hm)]

end GradeMass

section UnitNonunitCounterflow

variable {Ω E : Type*} [Fintype Ω] [DecidableEq Ω]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A scalar residue weight applied to a finite vector-valued source. -/
def residueChannelAmplitude (weight : Ω → ℝ) (source : Ω → E) : E :=
  ∑ x, weight x • source x

/-- The unweighted carrier of the residues selected by `isUnit`. -/
def residueUnitCarrier (isUnit : Ω → Prop) [DecidablePred isUnit] (source : Ω → E) : E :=
  ∑ x, if isUnit x then source x else 0

/-- The low-channel contribution of the complementary nonunit residues. -/
def residueNonunitCounterflow
    (isUnit : Ω → Prop) [DecidablePred isUnit]
    (lowWeight : Ω → ℝ) (source : Ω → E) : E :=
  ∑ x, if isUnit x then 0 else lowWeight x • source x

omit [DecidableEq Ω] in
/-- **Low-channel normal form.** If the low Boolean weight is the constant `headMass` on every
unit residue, then its full source amplitude is the positive unit fraction plus one canonical
nonunit counterflow. -/
theorem residueLowChannel_counterflowNormalForm
    (isUnit : Ω → Prop) [DecidablePred isUnit]
    (lowWeight : Ω → ℝ) (source : Ω → E) (headMass : ℝ)
    (hunit : ∀ x, isUnit x → lowWeight x = headMass) :
    residueChannelAmplitude lowWeight source =
      headMass • residueUnitCarrier isUnit source +
        residueNonunitCounterflow isUnit lowWeight source := by
  unfold residueChannelAmplitude residueUnitCarrier residueNonunitCounterflow
  calc
    (∑ x, lowWeight x • source x) =
        ∑ x, (headMass • (if isUnit x then source x else 0) +
          (if isUnit x then 0 else lowWeight x • source x)) := by
      apply Finset.sum_congr rfl
      intro x _hx
      by_cases hx : isUnit x
      · simp [hx, hunit x hx]
      · simp [hx]
    _ = headMass • (∑ x, if isUnit x then source x else 0) +
          ∑ x, if isUnit x then 0 else lowWeight x • source x := by
      rw [Finset.sum_add_distrib, Finset.smul_sum]

omit [DecidableEq Ω] in
/-- **High-channel normal form.** If low and high weights join to the unit indicator, the high
channel contains the complementary positive unit fraction and the exact negative of the same
nonunit counterflow. -/
theorem residueHighChannel_counterflowNormalForm
    (isUnit : Ω → Prop) [DecidablePred isUnit]
    (lowWeight highWeight : Ω → ℝ) (source : Ω → E) (headMass : ℝ)
    (hjoin : ∀ x, lowWeight x + highWeight x = if isUnit x then 1 else 0)
    (hunit : ∀ x, isUnit x → lowWeight x = headMass) :
    residueChannelAmplitude highWeight source =
      (1 - headMass) • residueUnitCarrier isUnit source -
        residueNonunitCounterflow isUnit lowWeight source := by
  unfold residueChannelAmplitude residueUnitCarrier residueNonunitCounterflow
  calc
    (∑ x, highWeight x • source x) =
        ∑ x, ((1 - headMass) • (if isUnit x then source x else 0) -
          (if isUnit x then 0 else lowWeight x • source x)) := by
      apply Finset.sum_congr rfl
      intro x _hx
      by_cases hx : isUnit x
      · have hj := hjoin x
        have hu := hunit x hx
        simp only [hx, if_true] at hj ⊢
        have hh : highWeight x = 1 - headMass := by linarith
        rw [hh]
        simp
      · have hj := hjoin x
        simp only [hx, if_false] at hj ⊢
        have hh : highWeight x = -lowWeight x := by linarith
        rw [hh]
        simp
    _ = (1 - headMass) • (∑ x, if isUnit x then source x else 0) -
          ∑ x, if isUnit x then 0 else lowWeight x • source x := by
      rw [Finset.sum_sub_distrib, Finset.smul_sum]

omit [DecidableEq Ω] in
/-- **Prime/composite counterflow cancellation.** Joined low and high Boolean channels discard
the entire nonunit counterflow and recover exactly the unit carrier.  In the square-root sieve
range the unit carrier is the ordinary-prime endpoint, so the cutoff has only reallocated that
endpoint between its two channels. -/
theorem residueLow_add_high_eq_unitCarrier
    (isUnit : Ω → Prop) [DecidablePred isUnit]
    (lowWeight highWeight : Ω → ℝ) (source : Ω → E)
    (hjoin : ∀ x, lowWeight x + highWeight x = if isUnit x then 1 else 0) :
    residueChannelAmplitude lowWeight source + residueChannelAmplitude highWeight source =
      residueUnitCarrier isUnit source := by
  unfold residueChannelAmplitude residueUnitCarrier
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _hx
  rw [← add_smul, hjoin x]
  by_cases hx : isUnit x <;> simp [hx]

/-- The low/high coordinates are an invertible reparametrization of the unit carrier and the
nonunit counterflow.  In particular, no information or smallness is created by passing to the two
cutoff channels. -/
theorem lowHighCounterflow_coordinates_inverse
    {X Y primeCarrier counterflow : E} (headMass : ℝ)
    (hX : X = headMass • primeCarrier + counterflow)
    (hY : Y = (1 - headMass) • primeCarrier - counterflow) :
    X + Y = primeCarrier ∧
      (1 - headMass) • X - headMass • Y = counterflow := by
  constructor
  · rw [hX, hY]
    module
  · rw [hX, hY]
    module

end UnitNonunitCounterflow

section RealInnerGeometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Complete geometry of the low/high cross term.  Its sign is controlled only by whether the
nonunit counterflow lies inside the radius-`‖primeCarrier‖ / 2` ball centered at
`(1 / 2 - headMass) • primeCarrier`; there is no source-free sign. -/
theorem lowHighCounterflow_realInner
    {X Y primeCarrier counterflow : E} (headMass : ℝ)
    (hX : X = headMass • primeCarrier + counterflow)
    (hY : Y = (1 - headMass) • primeCarrier - counterflow) :
    inner ℝ X Y =
      (1 / 4 : ℝ) * ‖primeCarrier‖ ^ (2 : ℕ) -
        ‖counterflow - (1 / 2 - headMass) • primeCarrier‖ ^ (2 : ℕ) := by
  rw [hX, hY,
    ← real_inner_self_eq_norm_sq
      (counterflow - (1 / 2 - headMass) • primeCarrier)]
  simp only [inner_add_left, inner_sub_left, inner_sub_right,
    real_inner_smul_left, real_inner_smul_right]
  simp only [real_inner_self_eq_norm_sq, real_inner_comm]
  ring

end RealInnerGeometry

end

end RHTower
