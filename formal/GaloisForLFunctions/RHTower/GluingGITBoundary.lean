import GaloisForLFunctions.RHTower.GluingWitness

/-!
# Simultaneous-conjugacy orbit sets versus GIT word traces

Procesi trace-word generators describe the invariant ring and hence the affine GIT quotient.  They
do not classify arbitrary simultaneous-conjugacy orbits: non-semisimple orbits with the same
semisimplification need not be conjugate.  This file gives an exact flat `2 × 2` rational witness.

Both pairs consist of commuting invertible upper-unipotent matrices and have identical per-generator
conjugacy data.  No simultaneous conjugacy relates them, while every positive or signed word has
trace `2` for both pairs.  It also records that the earlier noncommuting C3 witness cannot be a
constant cocycle for an abelian two-generator action.
-/

namespace GaloisForLFunctions

open Matrix

/-- Rational upper-unipotent `2 × 2` matrix with additive parameter. -/
def upperUnipotent (a : ℚ) : Mat2Rat := ![![1, a], ![0, 1]]

theorem upperUnipotent_mul (a b : ℚ) :
    upperUnipotent a * upperUnipotent b = upperUnipotent (a + b) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [upperUnipotent, Matrix.mul_apply, Fin.sum_univ_two, add_comm]

theorem upperUnipotent_comm (a b : ℚ) :
    upperUnipotent a * upperUnipotent b =
      upperUnipotent b * upperUnipotent a := by
  rw [upperUnipotent_mul, upperUnipotent_mul, add_comm]

theorem upperUnipotent_mul_neg (a : ℚ) :
    upperUnipotent a * upperUnipotent (-a) = 1 := by
  rw [upperUnipotent_mul]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [upperUnipotent]

theorem upperUnipotent_neg_mul (a : ℚ) :
    upperUnipotent (-a) * upperUnipotent a = 1 := by
  rw [upperUnipotent_comm, upperUnipotent_mul_neg]

theorem upperUnipotent_trace (a : ℚ) :
    (upperUnipotent a).trace = 2 := by
  norm_num [upperUnipotent, Matrix.trace, Fin.sum_univ_two]

/-- Evaluation of a positive word in a matrix pair. -/
def pairWordEval (A₀ A₁ : Mat2Rat) : List Bool → Mat2Rat
  | [] => 1
  | false :: w => A₀ * pairWordEval A₀ A₁ w
  | true :: w => A₁ * pairWordEval A₀ A₁ w

theorem pairWordEval_upper_exists (a b : ℚ) (w : List Bool) :
    ∃ c : ℚ, pairWordEval (upperUnipotent a) (upperUnipotent b) w =
      upperUnipotent c := by
  induction w with
  | nil =>
      refine ⟨0, ?_⟩
      ext i j
      fin_cases i <;> fin_cases j <;> norm_num [pairWordEval, upperUnipotent]
  | cons x w ih =>
      obtain ⟨c, hc⟩ := ih
      cases x
      · exact ⟨a + c, by simp [pairWordEval, hc, upperUnipotent_mul]⟩
      · exact ⟨b + c, by simp [pairWordEval, hc, upperUnipotent_mul]⟩

theorem trace_pairWordEval_upper (a b : ℚ) (w : List Bool) :
    (pairWordEval (upperUnipotent a) (upperUnipotent b) w).trace = 2 := by
  obtain ⟨c, hc⟩ := pairWordEval_upper_exists a b w
  rw [hc, upperUnipotent_trace]

/-- A signed letter chooses a generator and whether to invert it. -/
def signedUpperLetter (a b : ℚ) : Bool × Bool → Mat2Rat
  | (false, false) => upperUnipotent a
  | (false, true) => upperUnipotent (-a)
  | (true, false) => upperUnipotent b
  | (true, true) => upperUnipotent (-b)

/-- Evaluation of a signed word in upper-unipotent generators. -/
def signedUpperWordEval (a b : ℚ) : List (Bool × Bool) → Mat2Rat
  | [] => 1
  | x :: w => signedUpperLetter a b x * signedUpperWordEval a b w

theorem signedUpperWordEval_exists (a b : ℚ) (w : List (Bool × Bool)) :
    ∃ c : ℚ, signedUpperWordEval a b w = upperUnipotent c := by
  induction w with
  | nil =>
      refine ⟨0, ?_⟩
      ext i j
      fin_cases i <;> fin_cases j <;> norm_num [signedUpperWordEval, upperUnipotent]
  | cons x w ih =>
      obtain ⟨c, hc⟩ := ih
      rcases x with ⟨x, ε⟩
      cases x <;> cases ε
      · exact ⟨a + c, by simp [signedUpperWordEval, signedUpperLetter, hc,
          upperUnipotent_mul]⟩
      · exact ⟨-a + c, by simp [signedUpperWordEval, signedUpperLetter, hc,
          upperUnipotent_mul]⟩
      · exact ⟨b + c, by simp [signedUpperWordEval, signedUpperLetter, hc,
          upperUnipotent_mul]⟩
      · exact ⟨-b + c, by simp [signedUpperWordEval, signedUpperLetter, hc,
          upperUnipotent_mul]⟩

theorem trace_signedUpperWordEval (a b : ℚ) (w : List (Bool × Bool)) :
    (signedUpperWordEval a b w).trace = 2 := by
  obtain ⟨c, hc⟩ := signedUpperWordEval_exists a b w
  rw [hc, upperUnipotent_trace]

def flatGluingA₀ : Mat2Rat := upperUnipotent 1
def flatGluingA₁ : Mat2Rat := upperUnipotent 1
def flatGluingB₀ : Mat2Rat := upperUnipotent 1
def flatGluingB₁ : Mat2Rat := upperUnipotent 2

/-- Constant two-generator cocycle condition for a trivial action of an abelian group. -/
def IsConstantTwoGeneratorCocycle (A₀ A₁ : Mat2Rat) : Prop :=
  A₀ * A₁ = A₁ * A₀

theorem flatGluingA_isCocycle :
    IsConstantTwoGeneratorCocycle flatGluingA₀ flatGluingA₁ := by
  exact upperUnipotent_comm 1 1

theorem flatGluingB_isCocycle :
    IsConstantTwoGeneratorCocycle flatGluingB₀ flatGluingB₁ := by
  exact upperUnipotent_comm 1 2

theorem flatGluingB₀_eq_A₀ : flatGluingB₀ = flatGluingA₀ := rfl

theorem flatGluingB₁_eq_conj :
    gluingH * flatGluingA₁ * gluingHinv = flatGluingB₁ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [gluingH, gluingHinv, flatGluingA₁, flatGluingB₁,
      upperUnipotent, Matrix.mul_apply, Fin.sum_univ_two]

theorem flatGluingB₀_ne_B₁ : flatGluingB₀ ≠ flatGluingB₁ := by
  intro h
  have hentry := congr_fun (congr_fun h (0 : Fin 2)) (1 : Fin 2)
  norm_num [flatGluingB₀, flatGluingB₁, upperUnipotent] at hentry

/-- The two flat pairs are not in the same simultaneous-conjugacy orbit. -/
theorem flatGluing_not_jointly_conjugate
    (P Q : Mat2Rat)
    (h₀ : P * flatGluingA₀ * Q = flatGluingB₀)
    (h₁ : P * flatGluingA₁ * Q = flatGluingB₁) : False := by
  apply flatGluingB₀_ne_B₁
  rw [← h₀, ← h₁]
  rfl

theorem flatGluing_all_word_traces_equal (w : List Bool) :
    (pairWordEval flatGluingA₀ flatGluingA₁ w).trace =
      (pairWordEval flatGluingB₀ flatGluingB₁ w).trace := by
  change (pairWordEval (upperUnipotent 1) (upperUnipotent 1) w).trace =
    (pairWordEval (upperUnipotent 1) (upperUnipotent 2) w).trace
  rw [trace_pairWordEval_upper, trace_pairWordEval_upper]

theorem flatGluing_all_signed_word_traces_equal (w : List (Bool × Bool)) :
    (signedUpperWordEval 1 1 w).trace =
      (signedUpperWordEval 1 2 w).trace := by
  rw [trace_signedUpperWordEval, trace_signedUpperWordEval]

/-- The noncommuting C3 witness does not satisfy the constant cocycle condition for an abelian
two-generator action. -/
theorem c3_gluing_pair_not_constantCocycle :
    ¬ IsConstantTwoGeneratorCocycle gluingA2 gluingA3 := by
  intro h
  have hentry := congr_fun (congr_fun h (0 : Fin 2)) (0 : Fin 2)
  norm_num [IsConstantTwoGeneratorCocycle, gluingA2, gluingA3,
    Matrix.mul_apply, Fin.sum_univ_two] at hentry

/-- Closed counterexample to orbit-set classification by GIT word traces.  Both pairs are flat,
invertible and per-generator conjugate; their simultaneous-conjugacy orbits differ, although every
positive and signed word trace agrees. -/
theorem commuting_gluing_orbits_not_separated_by_word_traces :
    IsConstantTwoGeneratorCocycle flatGluingA₀ flatGluingA₁ ∧
    IsConstantTwoGeneratorCocycle flatGluingB₀ flatGluingB₁ ∧
    flatGluingB₀ = flatGluingA₀ ∧
    gluingH * gluingHinv = 1 ∧ gluingHinv * gluingH = 1 ∧
    gluingH * flatGluingA₁ * gluingHinv = flatGluingB₁ ∧
    (∀ P Q : Mat2Rat,
      P * flatGluingA₀ * Q = flatGluingB₀ →
      P * flatGluingA₁ * Q = flatGluingB₁ → False) ∧
    (∀ w : List Bool,
      (pairWordEval flatGluingA₀ flatGluingA₁ w).trace =
      (pairWordEval flatGluingB₀ flatGluingB₁ w).trace) ∧
    (∀ w : List (Bool × Bool),
      (signedUpperWordEval 1 1 w).trace =
      (signedUpperWordEval 1 2 w).trace) := by
  exact ⟨flatGluingA_isCocycle, flatGluingB_isCocycle,
    flatGluingB₀_eq_A₀, gluingH_mul_Hinv, gluingHinv_mul_H,
    flatGluingB₁_eq_conj, flatGluing_not_jointly_conjugate,
    flatGluing_all_word_traces_equal, flatGluing_all_signed_word_traces_equal⟩

universe uP uG

/-- A constant cocycle tuple is locally trivial when every generator value is conjugate to the
identity, which is the distinguished point in each one-generator nonabelian `H¹`. -/
def IsLocallyTrivialConstantTuple
    {P : Type uP} {G : Type uG} [Group G] (a : P → G) : Prop :=
  ∀ p, ∃ g : G, g * a p * g⁻¹ = 1

/-- Conjugacy cannot turn a nonidentity element into the identity.  Consequently local triviality
at every generator forces a constant cocycle tuple to be globally trivial. -/
theorem isLocallyTrivialConstantTuple_iff
    {P : Type uP} {G : Type uG} [Group G] (a : P → G) :
    IsLocallyTrivialConstantTuple a ↔ a = 1 := by
  constructor
  · intro h
    funext p
    change a p = (1 : G)
    obtain ⟨g, hg⟩ := h p
    calc
      a p = g⁻¹ * (g * a p * g⁻¹) * g := by simp [mul_assoc]
      _ = g⁻¹ * 1 * g := by rw [hg]
      _ = 1 := by simp
  · rintro rfl p
    exact ⟨1, by simp⟩

/-- Tuple-level model of the constant local-global kernel. -/
abbrev ConstantLocalGlobalKernel
    (P : Type uP) (G : Type uG) [Group G] :=
  {a : P → G // IsLocallyTrivialConstantTuple a}

/-- **Constant nonabelian local-global kernel vanishes in every rank.** This refutes the proposed
nonzero constant `Ш` layer: a constant class trivial on each cyclic generator is already trivial. -/
theorem constantLocalGlobalKernel_subsingleton
    (P : Type uP) (G : Type uG) [Group G] :
    Subsingleton (ConstantLocalGlobalKernel P G) := by
  constructor
  rintro ⟨a, ha⟩ ⟨b, hb⟩
  apply Subtype.ext
  exact (isLocallyTrivialConstantTuple_iff a).mp ha |>.trans
    ((isLocallyTrivialConstantTuple_iff b).mp hb).symm

end GaloisForLFunctions
