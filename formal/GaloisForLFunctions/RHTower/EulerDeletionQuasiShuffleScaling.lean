import GaloisForLFunctions.RHTower.CoprimeBlockCarryTransgression

/-!
# Euler-deletion quasi-shuffle scaling

An Euler-deletion block is a deterministic jump path.  Its level-one sum vanishes, but its
quasi-shuffle bracket—the sum of squared jumps—is nonzero.  This distinguishes source refinement
from scalar cancellation.

Two finite quadratic refinements have exact, different scale laws.  Replicating a source `p` times
multiplies quadratic mass by `p`; scaling one source by a complex amplitude `c` multiplies it by
`normSq c`.  For the Euler-dilation amplitude `exp((1 - sigma) log p)`, equality of these two
refinements at any nonzero source forces `sigma = 1/2`.

This file proves only finite algebra and the real-exponential scaling implication.  It does not
assert that a zeta zero supplies refinement coherence; that is the open producer.
-/

namespace RHTower

open scoped BigOperators

/-- Canonical Euler-deletion jump block of length `q + 1`: `q` unit jumps and one `-q` jump. -/
def eulerDeletionQuasiShuffleIncrement (q : ℕ) (i : Fin (q + 1)) : ℤ :=
  if i = Fin.last q then -(q : ℤ) else 1

/-- The canonical jump block is the literal deletion coefficient on one full modulus block. -/
theorem eulerDeletionQuasiShuffleIncrement_eq_blockDeletionCoefficient
    (q : ℕ) (i : Fin (q + 1)) :
    eulerDeletionQuasiShuffleIncrement q i =
      blockDeletionCoefficient (q + 1) (i.val + 1) := by
  by_cases hi : i = Fin.last q
  · subst i
    simp [eulerDeletionQuasiShuffleIncrement, blockDeletionCoefficient]
  · have hlt : i.val + 1 < q + 1 := by
      have hle : i.val ≤ q := Nat.le_of_lt_succ i.isLt
      have hne : i.val ≠ q := by
        intro heq
        apply hi
        apply Fin.ext
        simpa using heq
      omega
    have hpos : 0 < i.val + 1 := by omega
    have hndvd : ¬q + 1 ∣ i.val + 1 := Nat.not_dvd_of_pos_of_lt hpos hlt
    simp [eulerDeletionQuasiShuffleIncrement, hi, blockDeletionCoefficient, hndvd]

/-- Level-one endpoint of the canonical deletion jump block. -/
def eulerDeletionQuasiShuffleLevelOne (q : ℕ) : ℤ :=
  ∑ i : Fin (q + 1), eulerDeletionQuasiShuffleIncrement q i

/-- Level-two scalar bracket retained before signed endpoint cancellation. -/
def eulerDeletionQuasiShuffleBracket (q : ℕ) : ℤ :=
  ∑ i : Fin (q + 1), eulerDeletionQuasiShuffleIncrement q i ^ (2 : ℕ)

/-- Every canonical deletion block closes at level one. -/
theorem eulerDeletionQuasiShuffleLevelOne_eq_zero (q : ℕ) :
    eulerDeletionQuasiShuffleLevelOne q = 0 := by
  rw [eulerDeletionQuasiShuffleLevelOne, Fin.sum_univ_castSucc]
  simp [eulerDeletionQuasiShuffleIncrement]

/-- Exact nonzero bracket left by a deletion block: `(modulus - 1) * modulus`. -/
theorem eulerDeletionQuasiShuffleBracket_eq (q : ℕ) :
    eulerDeletionQuasiShuffleBracket q = (q : ℤ) * (q + 1) := by
  rw [eulerDeletionQuasiShuffleBracket, Fin.sum_univ_castSucc]
  simp [eulerDeletionQuasiShuffleIncrement]
  ring

/-- Strict chronological Hermitian second level of a finite complex jump word. -/
def chronologicalHermitianSecond : List ℂ → ℂ
  | [] => 0
  | z :: zs => z * star zs.sum + chronologicalHermitianSecond zs

/-- Diagonal quasi-shuffle bracket of a finite complex jump word. -/
def chronologicalQuadraticBracket : List ℂ → ℝ
  | [] => 0
  | z :: zs => Complex.normSq z + chronologicalQuadraticBracket zs

/-- Diagonal bracket is additive under chronological concatenation. -/
theorem chronologicalQuadraticBracket_append (xs ys : List ℂ) :
    chronologicalQuadraticBracket (xs ++ ys) =
      chronologicalQuadraticBracket xs + chronologicalQuadraticBracket ys := by
  induction xs with
  | nil => simp [chronologicalQuadraticBracket]
  | cons z zs ih => simp [chronologicalQuadraticBracket, ih, add_assoc]

/-- Bracket of a constant repeated jump. -/
theorem chronologicalQuadraticBracket_replicate (n : ℕ) (z : ℂ) :
    chronologicalQuadraticBracket (List.replicate n z) =
      n * Complex.normSq z := by
  induction n with
  | zero => simp [chronologicalQuadraticBracket]
  | succ n ih =>
      rw [List.replicate_succ]
      simp [chronologicalQuadraticBracket, ih]
      ring

/-- Chronological complex word underlying the modulus-`q + 1` deletion block. -/
def eulerDeletionChronologicalWord (q : ℕ) : List ℂ :=
  List.replicate q 1 ++ [-(q : ℂ)]

/-- The chronological deletion word closes exactly. -/
theorem eulerDeletionChronologicalWord_sum_eq_zero (q : ℕ) :
    (eulerDeletionChronologicalWord q).sum = 0 := by
  simp [eulerDeletionChronologicalWord]

/-- Its diagonal bracket agrees with the finite integer block calculation. -/
theorem eulerDeletionChronologicalWord_bracket_eq (q : ℕ) :
    chronologicalQuadraticBracket (eulerDeletionChronologicalWord q) =
      (q : ℝ) * (q + 1) := by
  rw [eulerDeletionChronologicalWord, chronologicalQuadraticBracket_append,
    chronologicalQuadraticBracket_replicate]
  simp [chronologicalQuadraticBracket]
  ring

/-- Every nontrivial deletion word has nonzero bracket. -/
theorem eulerDeletionChronologicalWord_bracket_ne_zero
    {q : ℕ} (hq : 0 < q) :
    chronologicalQuadraticBracket (eulerDeletionChronologicalWord q) ≠ 0 := by
  rw [eulerDeletionChronologicalWord_bracket_eq]
  positivity

/--
Hermitian quasi-shuffle identity: endpoint norm-square is diagonal bracket plus twice the real
strict chronological second level.
-/
theorem endpoint_normSq_eq_quadraticBracket_add_second (xs : List ℂ) :
    Complex.normSq xs.sum =
      chronologicalQuadraticBracket xs + 2 * (chronologicalHermitianSecond xs).re := by
  induction xs with
  | nil => simp [chronologicalQuadraticBracket, chronologicalHermitianSecond]
  | cons z zs ih =>
      rw [List.sum_cons, Complex.normSq_add, ih]
      simp [chronologicalQuadraticBracket, chronologicalHermitianSecond]
      ring

/-- Equal closed endpoints do not determine the chronological second level. -/
theorem closed_endpoint_does_not_determine_chronologicalSecond :
    ∃ xs ys : List ℂ,
      xs.sum = ys.sum ∧
      chronologicalHermitianSecond xs ≠ chronologicalHermitianSecond ys := by
  refine ⟨[1, -1], [2, -2], ?_, ?_⟩
  · norm_num
  · norm_num [chronologicalHermitianSecond]

/-- Concatenation law, including the exact cross-endpoint term. -/
theorem chronologicalHermitianSecond_append (xs ys : List ℂ) :
    chronologicalHermitianSecond (xs ++ ys) =
      chronologicalHermitianSecond xs + xs.sum * star ys.sum +
        chronologicalHermitianSecond ys := by
  induction xs with
  | nil => simp [chronologicalHermitianSecond]
  | cons z zs ih =>
      simp [chronologicalHermitianSecond, ih, List.sum_append]
      ring

/-- Chronological repetition by concatenating `p` copies of one jump word. -/
def repeatChronological : ℕ → List ℂ → List ℂ
  | 0, _ => []
  | p + 1, xs => xs ++ repeatChronological p xs

/-- Endpoint of chronological repetition. -/
theorem sum_repeatChronological (p : ℕ) (xs : List ℂ) :
    (repeatChronological p xs).sum = p * xs.sum := by
  induction p with
  | zero => simp [repeatChronological]
  | succ p ih =>
      rw [repeatChronological, List.sum_append, ih]
      push_cast
      ring

/-- A closed source has no cross-copy term, so its second level scales by replication count. -/
theorem chronologicalHermitianSecond_repeat_of_sum_eq_zero
    (p : ℕ) (xs : List ℂ) (hsum : xs.sum = 0) :
    chronologicalHermitianSecond (repeatChronological p xs) =
      p * chronologicalHermitianSecond xs := by
  induction p with
  | zero => simp [repeatChronological, chronologicalHermitianSecond]
  | succ p ih =>
      rw [repeatChronological, chronologicalHermitianSecond_append, ih,
        sum_repeatChronological, hsum]
      push_cast
      ring

/-- Multiply every jump in a chronological word by one complex amplitude. -/
def scaleChronological (c : ℂ) (xs : List ℂ) : List ℂ :=
  xs.map (fun z => c * z)

/-- Endpoint scaling for a chronological word. -/
theorem sum_scaleChronological (c : ℂ) (xs : List ℂ) :
    (scaleChronological c xs).sum = c * xs.sum := by
  induction xs with
  | nil => simp [scaleChronological]
  | cons z zs ih =>
      change c * z + (scaleChronological c zs).sum = c * (z + zs.sum)
      rw [ih]
      ring

/-- Hermitian second level scales by the amplitude norm-square. -/
theorem chronologicalHermitianSecond_scale (c : ℂ) (xs : List ℂ) :
    chronologicalHermitianSecond (scaleChronological c xs) =
      (Complex.normSq c : ℂ) * chronologicalHermitianSecond xs := by
  induction xs with
  | nil => simp [scaleChronological, chronologicalHermitianSecond]
  | cons z zs ih =>
      change c * z * star (scaleChronological c zs).sum +
          chronologicalHermitianSecond (scaleChronological c zs) =
        (Complex.normSq c : ℂ) *
          (z * star zs.sum + chronologicalHermitianSecond zs)
      rw [sum_scaleChronological, ih]
      rw [star_mul, ← Complex.mul_conj c]
      simp only [starRingEnd_apply]
      ring

/-- Quadratic bracket of a finite complex jump source. -/
def finiteComplexQuadraticMass {ι : Type*} [Fintype ι] (x : ι → ℂ) : ℝ :=
  ∑ i, Complex.normSq (x i)

/-- Quadratic bracket after chronological `p`-fold source replication. -/
def replicatedComplexQuadraticMass {ι : Type*} [Fintype ι]
    (p : ℕ) (x : ι → ℂ) : ℝ :=
  ∑ y : Fin p × ι, Complex.normSq (x y.2)

/-- Quadratic bracket after scaling every source jump by one complex amplitude. -/
def scaledComplexQuadraticMass {ι : Type*} [Fintype ι]
    (c : ℂ) (x : ι → ℂ) : ℝ :=
  finiteComplexQuadraticMass (fun i => c * x i)

/-- Replication multiplies quadratic mass by source multiplicity. -/
theorem replicatedComplexQuadraticMass_eq {ι : Type*} [Fintype ι]
    (p : ℕ) (x : ι → ℂ) :
    replicatedComplexQuadraticMass p x =
      (p : ℝ) * finiteComplexQuadraticMass x := by
  simp [replicatedComplexQuadraticMass, finiteComplexQuadraticMass,
    Fintype.sum_prod_type]

/-- Amplitude scaling multiplies quadratic mass by its norm-square. -/
theorem scaledComplexQuadraticMass_eq {ι : Type*} [Fintype ι]
    (c : ℂ) (x : ι → ℂ) :
    scaledComplexQuadraticMass c x =
      Complex.normSq c * finiteComplexQuadraticMass x := by
  simp [scaledComplexQuadraticMass, finiteComplexQuadraticMass,
    Complex.normSq_mul, Finset.mul_sum]

/-- Real-positive amplitude of the Euler dilation `p^(1-sigma)`, without complex phase. -/
noncomputable def eulerDilationAmplitude (p sigma : ℝ) : ℂ :=
  Real.exp ((1 - sigma) * Real.log p)

/-- Quadratic multiplier of the Euler-dilation amplitude. -/
noncomputable def eulerDilationQuadraticScale (p sigma : ℝ) : ℝ :=
  Real.exp (2 * (1 - sigma) * Real.log p)

/-- The norm-square of the Euler-dilation amplitude is its stated quadratic scale. -/
theorem normSq_eulerDilationAmplitude (p sigma : ℝ) :
    Complex.normSq (eulerDilationAmplitude p sigma) =
      eulerDilationQuadraticScale p sigma := by
  rw [eulerDilationAmplitude, Complex.normSq_ofReal,
    eulerDilationQuadraticScale, ← Real.exp_add]
  congr 1
  ring

/-- At every nontrivial dilation, quadratic Euler scale equals replication scale only at `1/2`. -/
theorem eulerDilationQuadraticScale_eq_iff_half
    {p sigma : ℝ} (hp : 1 < p) :
    eulerDilationQuadraticScale p sigma = p ↔ sigma = 1 / 2 := by
  have hp0 : 0 < p := lt_trans (by norm_num) hp
  constructor
  · intro h
    have h' : Real.exp (2 * (1 - sigma) * Real.log p) =
        Real.exp (Real.log p) := by
      calc
        Real.exp (2 * (1 - sigma) * Real.log p) = p := by
          simpa [eulerDilationQuadraticScale] using h
        _ = Real.exp (Real.log p) := (Real.exp_log hp0).symm
    have hexp : 2 * (1 - sigma) * Real.log p = Real.log p :=
      Real.exp_injective h'
    have hfac : (1 - 2 * sigma) * Real.log p = 0 := by
      nlinarith
    rcases mul_eq_zero.mp hfac with hsigma | hlog
    · linarith
    · exact (ne_of_gt (Real.log_pos hp) hlog).elim
  · intro hsigma
    subst sigma
    rw [eulerDilationQuadraticScale]
    calc
      Real.exp (2 * (1 - 1 / 2) * Real.log p) =
          Real.exp (Real.log p) := by
        congr 1
        ring
      _ = p := Real.exp_log hp0

/--
Any independently proved identification of replicated and Euler-scaled nonzero quadratic sources
forces the horizontal exponent to be `1/2`.  No such identification is assumed globally here.
-/
theorem eulerDilation_sigma_eq_half_of_quadraticRefinement
    {ι : Type*} [Fintype ι] (p : ℕ) (sigma : ℝ) (x : ι → ℂ)
    (hp : 2 ≤ p) (hx : finiteComplexQuadraticMass x ≠ 0)
    (hcoherence :
      replicatedComplexQuadraticMass p x =
        scaledComplexQuadraticMass (eulerDilationAmplitude p sigma) x) :
    sigma = 1 / 2 := by
  rw [replicatedComplexQuadraticMass_eq, scaledComplexQuadraticMass_eq,
    normSq_eulerDilationAmplitude] at hcoherence
  have hmass_nonneg : 0 ≤ finiteComplexQuadraticMass x := by
    apply Finset.sum_nonneg
    intro i hi
    exact Complex.normSq_nonneg _
  have hmass_pos : 0 < finiteComplexQuadraticMass x :=
    lt_of_le_of_ne hmass_nonneg (Ne.symm hx)
  have hscale : eulerDilationQuadraticScale p sigma = (p : ℝ) := by
    nlinarith
  exact (eulerDilationQuadraticScale_eq_iff_half (by exact_mod_cast hp)).mp hscale

/--
Chronological version of the finite fixed-exponent law.  Closedness removes cross-copy terms;
nonzero bracket guarantees a nonzero strict second level; equality of replicated and Euler-scaled
second levels then forces `sigma = 1/2`.
-/
theorem eulerDilation_sigma_eq_half_of_chronologicalSecondRefinement
    (p : ℕ) (sigma : ℝ) (xs : List ℂ)
    (hp : 2 ≤ p) (hsum : xs.sum = 0)
    (hbracket : chronologicalQuadraticBracket xs ≠ 0)
    (hcoherence :
      chronologicalHermitianSecond (repeatChronological p xs) =
        chronologicalHermitianSecond
          (scaleChronological (eulerDilationAmplitude p sigma) xs)) :
    sigma = 1 / 2 := by
  have hid := endpoint_normSq_eq_quadraticBracket_add_second xs
  rw [hsum] at hid
  simp only [map_zero] at hid
  have hre : (chronologicalHermitianSecond xs).re ≠ 0 := by
    intro hz
    apply hbracket
    nlinarith
  have hsecond : chronologicalHermitianSecond xs ≠ 0 := by
    intro hz
    apply hre
    rw [hz]
    rfl
  rw [chronologicalHermitianSecond_repeat_of_sum_eq_zero p xs hsum,
    chronologicalHermitianSecond_scale, normSq_eulerDilationAmplitude] at hcoherence
  have hc : ((p : ℝ) : ℂ) = (eulerDilationQuadraticScale p sigma : ℝ) :=
    mul_right_cancel₀ hsecond hcoherence
  have hscale : eulerDilationQuadraticScale p sigma = (p : ℝ) := by
    have hre := congrArg Complex.re hc
    simpa using hre.symm
  exact (eulerDilationQuadraticScale_eq_iff_half (by exact_mod_cast hp)).mp hscale

/--
Specialization to the actual modulus-`q + 1` deletion word: any chronological second-level
identification of replication and Euler dilation forces the half exponent.
-/
theorem eulerDeletionChronologicalWord_sigma_eq_half_of_secondRefinement
    (q : ℕ) (sigma : ℝ) (hq : 0 < q)
    (hcoherence :
      chronologicalHermitianSecond
          (repeatChronological (q + 1) (eulerDeletionChronologicalWord q)) =
        chronologicalHermitianSecond
          (scaleChronological (eulerDilationAmplitude ((q + 1 : ℕ) : ℝ) sigma)
            (eulerDeletionChronologicalWord q))) :
    sigma = 1 / 2 := by
  exact eulerDilation_sigma_eq_half_of_chronologicalSecondRefinement
    (q + 1) sigma (eulerDeletionChronologicalWord q) (by omega)
    (eulerDeletionChronologicalWord_sum_eq_zero q)
    (eulerDeletionChronologicalWord_bracket_ne_zero hq) hcoherence

/-- Premise-free finite capstone for the deletion bracket and the unique quadratic fixed exponent. -/
theorem eulerDeletionSignatureScaling_closed :
    (∀ q : ℕ, eulerDeletionQuasiShuffleLevelOne q = 0) ∧
    (∀ q : ℕ,
      eulerDeletionQuasiShuffleBracket q = (q : ℤ) * (q + 1)) ∧
    (∀ xs : List ℂ,
      Complex.normSq xs.sum =
        chronologicalQuadraticBracket xs +
          2 * (chronologicalHermitianSecond xs).re) ∧
    (∀ p sigma : ℝ, 1 < p →
      (eulerDilationQuadraticScale p sigma = p ↔ sigma = 1 / 2)) := by
  exact ⟨eulerDeletionQuasiShuffleLevelOne_eq_zero,
    eulerDeletionQuasiShuffleBracket_eq,
    endpoint_normSq_eq_quadraticBracket_add_second,
    fun _ _ hp => eulerDilationQuadraticScale_eq_iff_half hp⟩

end RHTower
