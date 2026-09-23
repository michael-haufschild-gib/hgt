import GaloisForLFunctions.RHTower.CriticalActivationReesSourceLaw

/-!
# The Rees grading carries a bounded positive metric

An ordinary bounded positive Gram completion of the mass/score pair dies at a divisor point: the
score drops exactly one grade below the mass, so the ratio blows up like the inverse square of the
local coordinate.

Dividing each entry by the power of the coordinate that its own grade prescribes removes the
blow-up.  In the graded coordinates the mass is the unit `u` and the score is `d·u + t·v`, both
regular, and a single constant completes them to a positive Gram at every nonzero point.  For the
monomial model the constant is the square of the multiplicity.

This is the positive counterpart of `no_bounded_positive_divisorReesGram`: the obstruction is to
the ungraded pair only, and the graded symbol carries the metric the ungraded quotient cannot.
-/

open scoped BigOperators Matrix

open GaloisForLFunctions

namespace RHTower

noncomputable section

/-! ### A positivity criterion for the Gram model -/

theorem divisorReesGram_isHermitian (B S C : ℝ) :
    (divisorReesGram B S C).IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [divisorReesGram]

/-- **The converse cross bound.**  A nonnegative diagonal and the Cauchy–Schwarz inequality
between the entries make the Gram model positive semidefinite. -/
theorem divisorReesGram_posSemidef_of_crossBound {B S C : ℝ} (hC : 0 ≤ C)
    (h : S ^ (2 : ℕ) ≤ B ^ (2 : ℕ) * C) : (divisorReesGram B S C).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    (divisorReesGram_isHermitian B S C) fun x => ?_
  have hform : (star x) ⬝ᵥ (divisorReesGram B S C *ᵥ x)
      = B ^ (2 : ℕ) * x 0 ^ (2 : ℕ) + 2 * S * x 0 * x 1 + C * x 1 ^ (2 : ℕ) := by
    simp [divisorReesGram, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    ring
  rw [hform]
  rcases eq_or_ne B 0 with hB | hB
  · have hS : S = 0 := by
      have h0 : S ^ (2 : ℕ) ≤ 0 := by simpa [hB] using h
      nlinarith [sq_nonneg S]
    have : 0 ≤ C * x 1 ^ (2 : ℕ) := mul_nonneg hC (sq_nonneg _)
    simpa [hB, hS] using this
  · have hB2 : 0 < B ^ (2 : ℕ) := by positivity
    have hkey : 0 ≤ B ^ (2 : ℕ) * (B ^ (2 : ℕ) * x 0 ^ (2 : ℕ) + 2 * S * x 0 * x 1 + C * x 1 ^ (2 : ℕ)) := by
      have hexp : B ^ (2 : ℕ) * (B ^ (2 : ℕ) * x 0 ^ (2 : ℕ) + 2 * S * x 0 * x 1 + C * x 1 ^ (2 : ℕ))
          = (B ^ (2 : ℕ) * x 0 + S * x 1) ^ (2 : ℕ) + (B ^ (2 : ℕ) * C - S ^ (2 : ℕ)) * x 1 ^ (2 : ℕ) := by ring
      rw [hexp]
      have h1 : 0 ≤ (B ^ (2 : ℕ) * x 0 + S * x 1) ^ (2 : ℕ) := sq_nonneg _
      have h2 : 0 ≤ (B ^ (2 : ℕ) * C - S ^ (2 : ℕ)) * x 1 ^ (2 : ℕ) :=
        mul_nonneg (by linarith) (sq_nonneg _)
      linarith
    nlinarith [hkey, hB2]

/-! ### The graded coordinates -/

/-- The Rees-graded mass: the overlap divided by the power of the coordinate prescribed by its
grade. -/
def gradedDivisorOverlap (d : ℕ) (t : ℝ) : ℝ := monomialDivisorOverlap d t / t ^ d

/-- The Rees-graded score: the Fisher numerator divided by the power of the coordinate prescribed
by *its* grade, one lower than the mass. -/
def gradedDivisorFisherNumerator (d : ℕ) (t : ℝ) : ℝ :=
  monomialDivisorFisherNumerator d t / t ^ (d - 1)

theorem gradedDivisorOverlap_eq_one {d : ℕ} {t : ℝ} (ht : t ≠ 0) :
    gradedDivisorOverlap d t = 1 := by
  rw [gradedDivisorOverlap, monomialDivisorOverlap, div_self (pow_ne_zero d ht)]

theorem gradedDivisorFisherNumerator_eq {d : ℕ} {t : ℝ} (ht : t ≠ 0) :
    gradedDivisorFisherNumerator d t = (d : ℝ) := by
  rw [gradedDivisorFisherNumerator, monomialDivisorFisherNumerator, mul_div_assoc,
    div_self (pow_ne_zero (d - 1) ht), mul_one]

/-- **The graded pair is boundedly positive.**  At every nonzero point the square of the
multiplicity completes the graded mass and score to a positive Gram. -/
theorem gradedDivisorReesGram_posSemidef (d : ℕ) {t : ℝ} (ht : t ≠ 0) :
    (divisorReesGram (gradedDivisorOverlap d t) (gradedDivisorFisherNumerator d t)
      ((d : ℝ) ^ (2 : ℕ))).PosSemidef := by
  refine divisorReesGram_posSemidef_of_crossBound (by positivity) ?_
  rw [gradedDivisorOverlap_eq_one ht, gradedDivisorFisherNumerator_eq ht]
  simp

/-- **The Rees grading restores bounded positivity.**  One constant works at every nonzero point,
in contrast with `no_bounded_positive_divisorReesGram` for the ungraded pair. -/
theorem exists_bounded_positive_gradedDivisorReesGram (d : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, t ≠ 0 →
      (divisorReesGram (gradedDivisorOverlap d t) (gradedDivisorFisherNumerator d t)
        C).PosSemidef :=
  ⟨(d : ℝ) ^ (2 : ℕ), by positivity, fun _ ht => gradedDivisorReesGram_posSemidef d ht⟩

/-! ### The general regular model -/

/-- The graded score of a general divisor datum `B = t^d u`, `S = d t^(d-1) u + t^d v`. -/
def gradedScoreOfUnit (d : ℕ) (u v : ℝ → ℝ) (t : ℝ) : ℝ := (d : ℝ) * u t + t * v t

/-- The graded score is the Fisher numerator of the general model divided by its own grade
power. -/
theorem gradedScoreOfUnit_eq (d : ℕ) (hd : 0 < d) (u v : ℝ → ℝ) {t : ℝ} (ht : t ≠ 0) :
    ((d : ℝ) * t ^ (d - 1) * u t + t ^ d * v t) / t ^ (d - 1)
      = gradedScoreOfUnit d u v t := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hd.ne'
  simp only [gradedScoreOfUnit, Nat.succ_sub_one, pow_succ]
  field_simp

/-- **The graded metric for a general regular divisor datum.**  Where the unit is bounded below and
the graded score is bounded above, a single constant completes the graded pair to a positive Gram —
no smallness of the coordinate is needed. -/
theorem gradedScoreOfUnit_posSemidef {d : ℕ} {u v : ℝ → ℝ} {m K : ℝ} (hm : 0 < m)
    {s : Set ℝ} (hu : ∀ t ∈ s, m ≤ |u t|)
    (hK : ∀ t ∈ s, |gradedScoreOfUnit d u v t| ≤ K) (t : ℝ) (hts : t ∈ s) :
    (divisorReesGram (u t) (gradedScoreOfUnit d u v t) (K ^ (2 : ℕ) / m ^ (2 : ℕ))).PosSemidef := by
  have hKnonneg : 0 ≤ K := le_trans (abs_nonneg _) (hK t hts)
  refine divisorReesGram_posSemidef_of_crossBound (by positivity) ?_
  have hut : m ^ (2 : ℕ) ≤ u t ^ (2 : ℕ) := by
    have := hu t hts
    nlinarith [abs_nonneg (u t), sq_abs (u t)]
  have hSt : gradedScoreOfUnit d u v t ^ (2 : ℕ) ≤ K ^ (2 : ℕ) := by
    have := hK t hts
    nlinarith [abs_nonneg (gradedScoreOfUnit d u v t), sq_abs (gradedScoreOfUnit d u v t)]
  have hm2 : 0 < m ^ (2 : ℕ) := by positivity
  have hgoal : K ^ (2 : ℕ) ≤ u t ^ (2 : ℕ) * K ^ (2 : ℕ) / m ^ (2 : ℕ) := by
    rw [le_div_iff₀ hm2]
    nlinarith [sq_nonneg K]
  calc gradedScoreOfUnit d u v t ^ (2 : ℕ) ≤ K ^ (2 : ℕ) := hSt
    _ ≤ u t ^ (2 : ℕ) * K ^ (2 : ℕ) / m ^ (2 : ℕ) := hgoal
    _ = u t ^ (2 : ℕ) * (K ^ (2 : ℕ) / m ^ (2 : ℕ)) := by ring

/-- **The metric constant is determined by the datum.**  On a compact region where the unit does not
vanish, the bounds of `gradedScoreOfUnit_posSemidef` exist automatically, so the positive metric is
source-defined rather than imposed: no constant has to be supplied by hand. -/
theorem exists_gradedScoreOfUnit_posSemidef_of_isCompact {d : ℕ} {u v : ℝ → ℝ} {s : Set ℝ}
    (hs : IsCompact s) (hne : s.Nonempty) (hu : ContinuousOn u s) (hv : ContinuousOn v s)
    (hu0 : ∀ t ∈ s, u t ≠ 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ s,
      (divisorReesGram (u t) (gradedScoreOfUnit d u v t) C).PosSemidef := by
  obtain ⟨t₀, ht₀s, ht₀⟩ := hs.exists_isMinOn hne hu.abs
  obtain ⟨t₁, ht₁s, ht₁⟩ := hs.exists_isMaxOn hne
    (((continuousOn_const.mul hu).add (continuousOn_id.mul hv)).abs)
  have hm : 0 < |u t₀| := abs_pos.mpr (hu0 t₀ ht₀s)
  refine ⟨|gradedScoreOfUnit d u v t₁| ^ (2 : ℕ) / |u t₀| ^ (2 : ℕ), by positivity, fun t hts => ?_⟩
  exact gradedScoreOfUnit_posSemidef hm (fun _ hw => ht₀ hw) (fun _ hw => ht₁ hw) t hts

/-! ### The graded symbol is a single-Kraus positive form -/

/-- **The graded Gram is an outer square.**  At every nonzero point the graded mass/score pair is
the outer product of the constant vector `(1, d)` with itself. -/
theorem gradedDivisorReesGram_eq_vecMulVec (d : ℕ) {t : ℝ} (ht : t ≠ 0) :
    divisorReesGram (gradedDivisorOverlap d t) (gradedDivisorFisherNumerator d t) ((d : ℝ) ^ (2 : ℕ))
      = Matrix.vecMulVec ![1, (d : ℝ)] ![1, (d : ℝ)] := by
  rw [gradedDivisorOverlap_eq_one ht, gradedDivisorFisherNumerator_eq ht]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [divisorReesGram, Matrix.vecMulVec, pow_two]

/-- **Single-Kraus complete positivity of the graded symbol.**  Being an outer square, the graded
Gram is positive with one Kraus vector, and that vector does not depend on the point. -/
theorem gradedDivisorReesGram_posSemidef_of_outerSquare (d : ℕ) {t : ℝ} (ht : t ≠ 0) :
    (divisorReesGram (gradedDivisorOverlap d t) (gradedDivisorFisherNumerator d t)
      ((d : ℝ) ^ (2 : ℕ))).PosSemidef := by
  rw [gradedDivisorReesGram_eq_vecMulVec d ht]
  simpa using Matrix.posSemidef_vecMulVec_self_star (R := ℝ) ![1, (d : ℝ)]

/-- **The graded symbol is constant on the punctured chamber.**  In particular every reflection of
the local coordinate leaves the graded Gram, and its metric constant, unchanged: the dagger costs
nothing on the graded symbol. -/
theorem gradedDivisorReesGram_eq_of_ne_zero (d : ℕ) {t t' : ℝ} (ht : t ≠ 0) (ht' : t' ≠ 0) :
    divisorReesGram (gradedDivisorOverlap d t) (gradedDivisorFisherNumerator d t) ((d : ℝ) ^ (2 : ℕ))
      = divisorReesGram (gradedDivisorOverlap d t') (gradedDivisorFisherNumerator d t')
          ((d : ℝ) ^ (2 : ℕ)) := by
  rw [gradedDivisorReesGram_eq_vecMulVec d ht, gradedDivisorReesGram_eq_vecMulVec d ht']

/-! ### The normalized graded symbol is a complete contraction -/

/-- The energy of the graded symbol: the squared length of its Kraus vector. -/
def gradedDivisorEnergy (d : ℕ) : ℝ := 1 + (d : ℝ) ^ (2 : ℕ)

theorem gradedDivisorEnergy_pos (d : ℕ) : 0 < gradedDivisorEnergy d := by
  unfold gradedDivisorEnergy
  positivity

/-- The contraction defect of the graded symbol normalized by its own energy. -/
def gradedDivisorDefect (d : ℕ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![(d : ℝ) ^ (2 : ℕ) / gradedDivisorEnergy d, -(d : ℝ) / gradedDivisorEnergy d;
     -(d : ℝ) / gradedDivisorEnergy d, 1 / gradedDivisorEnergy d]

/-- **The defect is again an outer square.**  Its Kraus vector is the orthogonal complement
`(d, -1)` of the symbol's own Kraus vector. -/
theorem gradedDivisorDefect_eq_vecMulVec (d : ℕ) :
    gradedDivisorDefect d
      = (gradedDivisorEnergy d)⁻¹ • Matrix.vecMulVec ![(d : ℝ), -1] ![(d : ℝ), -1] := by
  have hE := (gradedDivisorEnergy_pos d).ne'
  ext i j
  fin_cases i <;> fin_cases j <;>
    (simp [gradedDivisorDefect, Matrix.vecMulVec]; try field_simp; try ring)

theorem gradedDivisorDefect_posSemidef (d : ℕ) : (gradedDivisorDefect d).PosSemidef := by
  have hE := (gradedDivisorEnergy_pos d).ne'
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [gradedDivisorDefect]
  · have hform : (star x) ⬝ᵥ (gradedDivisorDefect d *ᵥ x)
        = (gradedDivisorEnergy d)⁻¹ * ((d : ℝ) * x 0 - x 1) ^ (2 : ℕ) := by
      simp [gradedDivisorDefect, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      field_simp
      ring
    rw [hform]
    have := (gradedDivisorEnergy_pos d).le
    positivity

theorem gradedDivisorDefect_eq (d : ℕ) {t : ℝ} (ht : t ≠ 0) :
    gradedDivisorDefect d
      = 1 - (gradedDivisorEnergy d)⁻¹ •
          divisorReesGram (gradedDivisorOverlap d t) (gradedDivisorFisherNumerator d t)
            ((d : ℝ) ^ (2 : ℕ)) := by
  have hE := (gradedDivisorEnergy_pos d).ne'
  rw [gradedDivisorReesGram_eq_vecMulVec d ht]
  ext i j
  fin_cases i <;> fin_cases j <;>
    (simp [gradedDivisorDefect, gradedDivisorEnergy, Matrix.vecMulVec];
      try field_simp; try ring)

/-- **The normalized graded symbol is a complete contraction.**  Divided by its own energy the
graded Gram is dominated by the identity, and the defect is itself an outer square, so the
contraction holds at every matrix level rather than only at the scalar one. -/
theorem gradedDivisorReesGram_contraction (d : ℕ) {t : ℝ} (ht : t ≠ 0) :
    (1 - (gradedDivisorEnergy d)⁻¹ •
      divisorReesGram (gradedDivisorOverlap d t) (gradedDivisorFisherNumerator d t)
        ((d : ℝ) ^ (2 : ℕ))).PosSemidef := by
  rw [← gradedDivisorDefect_eq d ht]
  exact gradedDivisorDefect_posSemidef d

/-! ### The normalized graded symbol is an orthogonal projection -/

/-- The energy-normalized graded symbol. -/
def gradedDivisorProjection (d : ℕ) : Matrix (Fin 2) (Fin 2) ℝ :=
  (gradedDivisorEnergy d)⁻¹ • Matrix.vecMulVec ![1, (d : ℝ)] ![1, (d : ℝ)]

theorem gradedDivisorProjection_eq (d : ℕ) {t : ℝ} (ht : t ≠ 0) :
    gradedDivisorProjection d
      = (gradedDivisorEnergy d)⁻¹ •
          divisorReesGram (gradedDivisorOverlap d t) (gradedDivisorFisherNumerator d t)
            ((d : ℝ) ^ (2 : ℕ)) := by
  rw [gradedDivisorProjection, gradedDivisorReesGram_eq_vecMulVec d ht]

/-- **The normalized graded symbol is idempotent.**  Being the outer square of a vector divided by
that vector's own squared length, it is the orthogonal projection onto the Kraus direction. -/
theorem gradedDivisorProjection_idempotent (d : ℕ) :
    gradedDivisorProjection d * gradedDivisorProjection d = gradedDivisorProjection d := by
  have hE := (gradedDivisorEnergy_pos d).ne'
  ext i j
  fin_cases i <;> fin_cases j <;>
    (simp [gradedDivisorProjection, gradedDivisorEnergy, Matrix.vecMulVec, Matrix.mul_apply,
      Fin.sum_univ_two]; try field_simp; try ring)

/-- **The graded symbol carries exactly one unit of trace**, uniformly in the multiplicity and in
the point.  So its contribution sits inside the four-unit budget with a factor-four margin, and the
margin is exact rather than estimated. -/
theorem trace_gradedDivisorProjection (d : ℕ) :
    Matrix.trace (gradedDivisorProjection d) = 1 := by
  have hE := (gradedDivisorEnergy_pos d).ne'
  rw [Matrix.trace_fin_two]
  simp only [gradedDivisorProjection, gradedDivisorEnergy, Matrix.vecMulVec, Matrix.smul_apply,
    Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, smul_eq_mul]
  field_simp

theorem trace_gradedDivisorProjection_le_four (d : ℕ) :
    Matrix.trace (gradedDivisorProjection d) ≤ 4 := by
  rw [trace_gradedDivisorProjection]
  norm_num

/-- **The symbol and its defect resolve the identity.** -/
theorem gradedDivisorProjection_add_defect (d : ℕ) :
    gradedDivisorProjection d + gradedDivisorDefect d = 1 := by
  have hE := (gradedDivisorEnergy_pos d).ne'
  ext i j
  fin_cases i <;> fin_cases j <;>
    (simp [gradedDivisorProjection, gradedDivisorDefect, gradedDivisorEnergy, Matrix.vecMulVec];
      try field_simp; try ring)

/-- **The symbol and its defect are orthogonal.**  They are the two complementary rank-one
projections of the graded plane. -/
theorem gradedDivisorProjection_mul_defect (d : ℕ) :
    gradedDivisorProjection d * gradedDivisorDefect d = 0 := by
  have hE := (gradedDivisorEnergy_pos d).ne'
  ext i j
  fin_cases i <;> fin_cases j <;>
    (simp [gradedDivisorProjection, gradedDivisorDefect, gradedDivisorEnergy, Matrix.vecMulVec,
      Matrix.mul_apply, Fin.sum_univ_two]; try field_simp; try ring)

/-- The defect carries the complementary unit of trace. -/
theorem trace_gradedDivisorDefect (d : ℕ) :
    Matrix.trace (gradedDivisorDefect d) = 1 := by
  have htr := congrArg Matrix.trace (gradedDivisorProjection_add_defect d)
  rw [Matrix.trace_add, trace_gradedDivisorProjection] at htr
  have hone : Matrix.trace (1 : Matrix (Fin 2) (Fin 2) ℝ) = 2 := by simp
  rw [hone] at htr
  linarith

/-- **Dagger stability for a general regular datum.**  If the parameter set is carried into itself
by the reflection, the same constant completes the reflected graded pair. -/
theorem gradedScoreOfUnit_posSemidef_reflected {d : ℕ} {u v : ℝ → ℝ} {m K : ℝ} (hm : 0 < m)
    {s : Set ℝ} {rho : ℝ → ℝ} (hrho : ∀ t ∈ s, rho t ∈ s)
    (hu : ∀ t ∈ s, m ≤ |u t|)
    (hK : ∀ t ∈ s, |gradedScoreOfUnit d u v t| ≤ K) (t : ℝ) (hts : t ∈ s) :
    (divisorReesGram (u (rho t)) (gradedScoreOfUnit d u v (rho t))
      (K ^ (2 : ℕ) / m ^ (2 : ℕ))).PosSemidef :=
  gradedScoreOfUnit_posSemidef hm hu hK (rho t) (hrho t hts)

end

end RHTower
