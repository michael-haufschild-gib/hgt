import GaloisForLFunctions.RHTower.GaussHodgeWeilDeviationMoment

/-!
# Insufficiency of the symmetry package for Weil positivity

Weil positivity on entire tests characterizes RH.  This module proves that no positivity source
can be extracted from the symmetry properties of the completed `xi` alone: evenness (the
functional equation), conjugation reality, and placement of the divisor in the open critical
strip are all satisfiable by an entire comparison function with an off-line zero quadruple, and
the Weil form of any finite conjugation-stable divisor containing an off-line point admits an
entire test with strictly negative diagonal.

* `finiteWeilForm` — the Weil polarization of an arbitrary finite divisor, in the same
  centered-coordinate normal form as `xiWeilPolarization`.
* `exists_entire_finiteWeilForm_neg` — **the abstract failure law**: any finite
  conjugation-stable divisor with an off-line point carries an entire (polynomial) test whose
  diagonal Weil value is negative.  The witness interpolates `1` and `-1` across the off-line
  reflection pair and kills the rest of the divisor with a product factor.
* `weilPositivity_not_symmetry_consequence` — **the comparison theorem**: an explicit entire
  function that is even, conjugation-real, and has all zeros in the open strip `|Im| < 1/2`,
  whose zero divisor nevertheless carries an entire test with negative Weil diagonal.  Hence
  every proof of the RH-equivalent positivity must consume input that distinguishes `xi`
  inside this symmetry class — the Euler product — and cannot proceed from the functional
  equation, reality, and strip alone.
-/

open Complex

namespace RHTower

noncomputable section

/-- The Weil polarization of an arbitrary finite divisor in centered coordinates. -/
def finiteWeilForm (S : Finset ℂ) (F G : ℂ → ℂ) : ℂ :=
  ∑ x ∈ S, F x * (starRingEnd ℂ) (G ((starRingEnd ℂ) x))

/-- **The abstract failure law.**  The Weil form of any finite conjugation-stable divisor with
an off-line point is not positive semidefinite on entire tests: an explicit polynomial witness
has diagonal value `-2`. -/
theorem exists_entire_finiteWeilForm_neg {S : Finset ℂ}
    (hconj : ∀ x ∈ S, (starRingEnd ℂ) x ∈ S) {a : ℂ}
    (haS : a ∈ S) (ha : a.im ≠ 0) :
    ∃ F : ℂ → ℂ, Differentiable ℂ F ∧ (finiteWeilForm S F F).re < 0 := by
  classical
  have hane : (starRingEnd ℂ) a ≠ a := by
    intro hcon
    apply ha
    have hcim := congrArg Complex.im hcon
    simp only [Complex.conj_im] at hcim
    linarith
  have hsubne : a - (starRingEnd ℂ) a ≠ 0 := sub_ne_zero.mpr (Ne.symm hane)
  set T : Finset ℂ := (S.erase a).erase ((starRingEnd ℂ) a) with hT
  set P : ℂ → ℂ := fun z => ∏ x ∈ T, (z - x) with hP
  have hPdiff : Differentiable ℂ P := by
    have h1 : Differentiable ℂ (∏ x ∈ T, fun z : ℂ => z - x) :=
      Differentiable.finsetProd fun x _ => Differentiable.sub_const differentiable_id x
    have h2 : P = ∏ x ∈ T, fun z : ℂ => z - x := by
      funext z
      rw [hP]
      simp only
      rw [Finset.prod_apply]
    rw [h2]
    exact h1
  have hPa : P a ≠ 0 := by
    rw [hP]
    simp only
    rw [Finset.prod_ne_zero_iff]
    intro x hx
    have hxa : x ≠ a := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hx)
    exact sub_ne_zero.mpr (Ne.symm hxa)
  have hPb : P ((starRingEnd ℂ) a) ≠ 0 := by
    rw [hP]
    simp only
    rw [Finset.prod_ne_zero_iff]
    intro x hx
    have hxb : x ≠ (starRingEnd ℂ) a := Finset.ne_of_mem_erase hx
    exact sub_ne_zero.mpr (Ne.symm hxb)
  have hPvan : ∀ x ∈ T, P x = 0 := by
    intro x hx
    rw [hP]
    simp only
    exact Finset.prod_eq_zero hx (sub_self x)
  set F : ℂ → ℂ := fun z =>
    P z * ((P a)⁻¹ * ((z - (starRingEnd ℂ) a) / (a - (starRingEnd ℂ) a)) +
      (P ((starRingEnd ℂ) a))⁻¹ * ((z - a) / (a - (starRingEnd ℂ) a))) with hF
  have hFa : F a = 1 := by
    rw [hF]
    simp only
    rw [sub_self, div_self hsubne, zero_div, mul_zero, add_zero, mul_one]
    exact mul_inv_cancel₀ hPa
  have hFb : F ((starRingEnd ℂ) a) = -1 := by
    rw [hF]
    simp only
    rw [sub_self, zero_div, mul_zero, zero_add]
    have hq : ((starRingEnd ℂ) a - a) / (a - (starRingEnd ℂ) a) = -1 := by
      rw [div_eq_iff hsubne]
      ring
    rw [hq, mul_neg_one, mul_neg, mul_inv_cancel₀ hPb]
  have hFvanT : ∀ x ∈ T, F x = 0 := by
    intro x hx
    rw [hF]
    simp only
    rw [hPvan x hx, zero_mul]
  have hFdiff : Differentiable ℂ F := by
    rw [hF]
    apply hPdiff.mul
    apply Differentiable.add
    · exact ((Differentiable.sub_const differentiable_id _).div_const _).const_mul _
    · exact ((Differentiable.sub_const differentiable_id _).div_const _).const_mul _
  refine ⟨F, hFdiff, ?_⟩
  have hbSa : (starRingEnd ℂ) a ∈ S.erase a := Finset.mem_erase.mpr ⟨hane, hconj a haS⟩
  have hsum : finiteWeilForm S F F = -2 := by
    rw [finiteWeilForm,
      ← Finset.add_sum_erase S _ haS,
      ← Finset.add_sum_erase (S.erase a) _ hbSa]
    have h1 : F a * (starRingEnd ℂ) (F ((starRingEnd ℂ) a)) = -1 := by
      rw [hFa, hFb, one_mul, map_neg, map_one]
    have h2 : F ((starRingEnd ℂ) a) *
        (starRingEnd ℂ) (F ((starRingEnd ℂ) ((starRingEnd ℂ) a))) = -1 := by
      rw [Complex.conj_conj, hFb, hFa, map_one, mul_one]
    have h3 : ∀ x ∈ (S.erase a).erase ((starRingEnd ℂ) a),
        F x * (starRingEnd ℂ) (F ((starRingEnd ℂ) x)) = 0 := by
      intro x hx
      rw [hFvanT x (by rw [hT]; exact hx), zero_mul]
    rw [h1, h2, Finset.sum_congr rfl h3, Finset.sum_const_zero]
    ring
  rw [hsum]
  simp only [Complex.neg_re, Complex.re_ofNat, neg_lt, neg_zero]
  norm_num

/-! ## The comparison function: all the xi symmetries, one off-line quadruple -/

/-- An off-critical-line point inside the open strip, in centered coordinates. -/
def comparisonOffLinePoint : ℂ := 1 + ((1 / 4 : ℝ) : ℂ) * Complex.I

theorem comparisonOffLinePoint_im : comparisonOffLinePoint.im = 1 / 4 := by
  rw [comparisonOffLinePoint]
  simp [Complex.add_im, Complex.mul_im]

/-- The entire comparison function: even, conjugation-real, all zeros in the open strip, one
reflection-stable off-line zero quadruple. -/
def comparisonSymmetryPolynomial (z : ℂ) : ℂ :=
  (z - comparisonOffLinePoint) * (z + comparisonOffLinePoint) *
    ((z - (starRingEnd ℂ) comparisonOffLinePoint) *
      (z + (starRingEnd ℂ) comparisonOffLinePoint))

theorem comparisonSymmetryPolynomial_even (z : ℂ) :
    comparisonSymmetryPolynomial (-z) = comparisonSymmetryPolynomial z := by
  rw [comparisonSymmetryPolynomial, comparisonSymmetryPolynomial]
  ring

theorem comparisonSymmetryPolynomial_conj (z : ℂ) :
    comparisonSymmetryPolynomial ((starRingEnd ℂ) z) =
      (starRingEnd ℂ) (comparisonSymmetryPolynomial z) := by
  rw [comparisonSymmetryPolynomial, comparisonSymmetryPolynomial]
  simp only [map_mul, map_sub, map_add, Complex.conj_conj]
  ring

theorem comparisonSymmetryPolynomial_differentiable :
    Differentiable ℂ comparisonSymmetryPolynomial := by
  have h1 : Differentiable ℂ fun z : ℂ => z - comparisonOffLinePoint :=
    Differentiable.sub_const differentiable_id _
  have h2 : Differentiable ℂ fun z : ℂ => z + comparisonOffLinePoint :=
    differentiable_id.add (differentiable_const _)
  have h3 : Differentiable ℂ fun z : ℂ => z - (starRingEnd ℂ) comparisonOffLinePoint :=
    Differentiable.sub_const differentiable_id _
  have h4 : Differentiable ℂ fun z : ℂ => z + (starRingEnd ℂ) comparisonOffLinePoint :=
    differentiable_id.add (differentiable_const _)
  exact (h1.mul h2).mul (h3.mul h4)

/-- Every zero of the comparison function lies in the open strip `|Im| < 1/2`. -/
theorem comparisonSymmetryPolynomial_zero_strip {z : ℂ}
    (hz : comparisonSymmetryPolynomial z = 0) : |z.im| < 1 / 2 := by
  rw [comparisonSymmetryPolynomial] at hz
  have him : z.im = 1 / 4 ∨ z.im = -(1 / 4) := by
    rcases mul_eq_zero.mp hz with h | h
    · rcases mul_eq_zero.mp h with h' | h'
      · left
        have := congrArg Complex.im (sub_eq_zero.mp h')
        rwa [comparisonOffLinePoint_im] at this
      · right
        have hzeq : z = -comparisonOffLinePoint := by linear_combination h'
        have := congrArg Complex.im hzeq
        rwa [Complex.neg_im, comparisonOffLinePoint_im] at this
    · rcases mul_eq_zero.mp h with h' | h'
      · right
        have := congrArg Complex.im (sub_eq_zero.mp h')
        rwa [Complex.conj_im, comparisonOffLinePoint_im] at this
      · left
        have hzeq : z = -(starRingEnd ℂ) comparisonOffLinePoint := by linear_combination h'
        have := congrArg Complex.im hzeq
        rw [Complex.neg_im, Complex.conj_im, comparisonOffLinePoint_im] at this
        rwa [neg_neg] at this
  rcases him with h | h <;> rw [h] <;> rw [abs_lt] <;> constructor <;> norm_num

/-- **The comparison theorem: the symmetry package cannot source Weil positivity.**  There is
an entire function satisfying evenness, conjugation reality, and strip placement of its
divisor — everything the completed `xi` offers short of arithmetic — with an off-line zero, a
conjugation-stable finite zero divisor, and an entire test of strictly negative diagonal Weil
value on that divisor.  Any producer of the RH-equivalent positivity must therefore consume
input beyond this package: the Euler product side of `xi`. -/
theorem weilPositivity_not_symmetry_consequence :
    ∃ P : ℂ → ℂ, Differentiable ℂ P ∧
      (∀ z, P (-z) = P z) ∧
      (∀ z, P ((starRingEnd ℂ) z) = (starRingEnd ℂ) (P z)) ∧
      (∀ z, P z = 0 → |z.im| < 1 / 2) ∧
      (∃ z, P z = 0 ∧ z.im ≠ 0) ∧
      ∃ S : Finset ℂ, (∀ x, x ∈ S → P x = 0) ∧ (∀ x ∈ S, (starRingEnd ℂ) x ∈ S) ∧
        ∃ F : ℂ → ℂ, Differentiable ℂ F ∧ (finiteWeilForm S F F).re < 0 := by
  classical
  set a : ℂ := comparisonOffLinePoint with hadef
  have haim : a.im = 1 / 4 := comparisonOffLinePoint_im
  set S : Finset ℂ := {a, -a, (starRingEnd ℂ) a, -(starRingEnd ℂ) a} with hS
  have hmemS : ∀ x, x ∈ S ↔
      (x = a ∨ x = -a ∨ x = (starRingEnd ℂ) a ∨ x = -(starRingEnd ℂ) a) := by
    intro x
    rw [hS]
    simp [Finset.mem_insert, Finset.mem_singleton]
  have hzeroS : ∀ x, x ∈ S → comparisonSymmetryPolynomial x = 0 := by
    intro x hx
    rw [comparisonSymmetryPolynomial]
    rcases (hmemS x).mp hx with h | h | h | h <;> rw [h] <;> ring
  have hconjS : ∀ x ∈ S, (starRingEnd ℂ) x ∈ S := by
    intro x hx
    rcases (hmemS x).mp hx with h | h | h | h <;> rw [h] <;> apply (hmemS _).mpr
    · right; right; left; rfl
    · right; right; right; rw [map_neg]
    · left; rw [Complex.conj_conj]
    · right; left; rw [map_neg, Complex.conj_conj]
  have haS : a ∈ S := (hmemS a).mpr (Or.inl rfl)
  have haim' : a.im ≠ 0 := by rw [haim]; norm_num
  obtain ⟨F, hFdiff, hFneg⟩ := exists_entire_finiteWeilForm_neg hconjS haS haim'
  exact ⟨comparisonSymmetryPolynomial, comparisonSymmetryPolynomial_differentiable,
    comparisonSymmetryPolynomial_even, comparisonSymmetryPolynomial_conj,
    fun z => comparisonSymmetryPolynomial_zero_strip,
    ⟨a, hzeroS a haS, haim'⟩,
    S, hzeroS, hconjS, F, hFdiff, hFneg⟩

end

end RHTower
