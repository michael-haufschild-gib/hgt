import GaloisForLFunctions.RHTower.MobiusDivisorLatePrimeBlocks

/-!
# All-order Boolean transport through an isolated late-prime block

The full future response of a processed core is its Boolean jet of energy
differences.  A late-prime block acts on every nonzero grade of that jet by
one signed scalar mass times the corresponding literal fibre.  This is an
exact source identity; it asserts no global selection or envelope bound.
-/

noncomputable section
set_option autoImplicit false
open Finset
namespace RHTower

/-- Alternating Boolean sum of a response over prospective prime insertions. -/
def mobiusDivisorBooleanAlternating (P A : Finset ℕ)
    (f : Finset ℕ → ℝ) : ℝ :=
  ∑ U ∈ A.powerset, (-1 : ℝ) ^ U.card * f (P ∪ U)

/-- Adding a prospective coordinate takes one forward difference of the
underlying response. -/
theorem mobiusDivisorBooleanAlternating_insert
    (P : Finset ℕ) {p : ℕ} {A : Finset ℕ} (hp : p ∉ A)
    (f : Finset ℕ → ℝ) :
    mobiusDivisorBooleanAlternating P (insert p A) f =
      mobiusDivisorBooleanAlternating P A (fun Q => f Q - f (insert p Q)) := by
  classical
  unfold mobiusDivisorBooleanAlternating
  rw [Finset.sum_powerset_insert hp, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro U hU
  have hpU : p ∉ U := fun h => hp (Finset.mem_powerset.mp hU h)
  have hunion : P ∪ insert p U = insert p (P ∪ U) := by
    ext x
    simp only [mem_union, mem_insert]
    tauto
  rw [hunion, Finset.card_insert_of_notMem hpU, pow_succ]
  ring

/-- The complete alternating response of a literal fibre is its source fibre
on the union of the prospective coordinates. -/
theorem mobiusDivisorSelectionFibre_booleanAlternating
    (M : ℕ) (P R A : Finset ℕ) (hRA : Disjoint R A) :
    mobiusDivisorBooleanAlternating P A
        (fun Q => mobiusDivisorSelectionFibre M Q R) =
      (-1 : ℝ) ^ A.card * mobiusDivisorSelectionFibre M P (R ∪ A) := by
  classical
  revert R
  induction A using Finset.induction_on with
  | empty =>
      intro R _
      simp [mobiusDivisorBooleanAlternating]
  | @insert p A hp ih =>
      intro R hRA
      have hpR : p ∉ R := by
        intro h
        exact (Finset.disjoint_left.mp hRA) h (mem_insert_self p A)
      have hRA' : Disjoint R A := by
        rw [Finset.disjoint_left] at hRA ⊢
        intro r hr hA
        exact hRA hr (mem_insert_of_mem hA)
      have hpRA : Disjoint (insert p R) A := by
        rw [Finset.disjoint_left]
        intro r hr hA
        rcases mem_insert.mp hr with rfl | hr
        · exact hp hA
        · exact (Finset.disjoint_left.mp hRA') hr hA
      rw [mobiusDivisorBooleanAlternating_insert P hp]
      have hstep : (fun Q =>
          mobiusDivisorSelectionFibre M Q R -
            mobiusDivisorSelectionFibre M (insert p Q) R) =
          fun Q => -mobiusDivisorSelectionFibre M Q (insert p R) := by
        funext Q
        rw [mobiusDivisorSelectionFibre_insert, if_neg hpR]
        ring
      rw [hstep]
      unfold mobiusDivisorBooleanAlternating
      simp only [mul_neg]
      rw [Finset.sum_neg_distrib]
      change -(mobiusDivisorBooleanAlternating P A
        (fun Q => mobiusDivisorSelectionFibre M Q (insert p R))) = _
      rw [ih (insert p R) hpRA]
      have hUnion : insert p R ∪ A = R ∪ insert p A := by
        ext x
        simp only [mem_union, mem_insert]
        tauto
      rw [hUnion, Finset.card_insert_of_notMem hp]
      ring

/-- Alternating Boolean sums preserve affine decompositions. -/
theorem mobiusDivisorBooleanAlternating_affine
    (P A : Finset ℕ) (f g : Finset ℕ → ℝ) (c d : ℝ) :
    mobiusDivisorBooleanAlternating P A (fun Q => f Q + c * g Q + d) =
      mobiusDivisorBooleanAlternating P A f +
        c * mobiusDivisorBooleanAlternating P A g +
          d * mobiusDivisorBooleanAlternating P A (fun _ => 1) := by
  unfold mobiusDivisorBooleanAlternating
  have hpoint (U : Finset ℕ) :
      (-1 : ℝ) ^ U.card * (f (P ∪ U) + c * g (P ∪ U) + d) =
        (-1 : ℝ) ^ U.card * f (P ∪ U) +
          c * ((-1 : ℝ) ^ U.card * g (P ∪ U)) +
            d * ((-1 : ℝ) ^ U.card * 1) := by
    ring
  calc
    _ = ∑ U ∈ A.powerset,
        ((-1 : ℝ) ^ U.card * f (P ∪ U) +
          c * ((-1 : ℝ) ^ U.card * g (P ∪ U)) +
            d * ((-1 : ℝ) ^ U.card * 1)) := by
      apply sum_congr rfl
      intro U _
      exact hpoint U
    _ = (∑ U ∈ A.powerset, (-1 : ℝ) ^ U.card * f (P ∪ U)) +
        c * (∑ U ∈ A.powerset, (-1 : ℝ) ^ U.card * g (P ∪ U)) +
          d * (∑ U ∈ A.powerset, (-1 : ℝ) ^ U.card * 1) := by
      rw [sum_add_distrib, sum_add_distrib, ← mul_sum, ← mul_sum]
    _ = _ := by rfl

/-- Every nonzero Boolean grade kills constants. -/
theorem mobiusDivisorBooleanAlternating_one_eq_zero
    (P A : Finset ℕ) (hA : A.Nonempty) :
    mobiusDivisorBooleanAlternating P A (fun _ => 1) = 0 := by
  unfold mobiusDivisorBooleanAlternating
  simp only [mul_one]
  calc
    (∑ U ∈ A.powerset, (-1 : ℝ) ^ U.card) =
        ∏ _p ∈ A, ((1 : ℝ) - 1) := by
      simpa using
        (Finset.prod_sub (fun _ : ℕ => (1 : ℝ)) (fun _ => (1 : ℝ)) A).symm
    _ = 0 := by
      obtain ⟨p, hp⟩ := hA
      apply Finset.prod_eq_zero hp
      ring

/-- Alternating Boolean jet of complete selection energy. -/
def mobiusDivisorEnergyBooleanAlternating (M : ℕ) (P A : Finset ℕ) : ℝ :=
  mobiusDivisorBooleanAlternating P A (mobiusDivisorSelectionEnergy M)

/-- Forward Boolean energy difference, normalized so a singleton is the usual
successor energy gain. -/
def mobiusDivisorEnergyBooleanDifference (M : ℕ) (P A : Finset ℕ) : ℝ :=
  (-1 : ℝ) ^ A.card * mobiusDivisorEnergyBooleanAlternating M P A

/-- On every nonempty Boolean grade, an isolated late block changes the
alternating energy response by one signed block mass times its literal fibre. -/
theorem mobiusDivisorEnergyBooleanAlternating_union_late_primes
    (M : ℕ) (P L A : Finset ℕ) (hA : A.Nonempty)
    (hL : ∀ s ∈ L, s.Prime ∧ s < M ∧ M ≤ 2 * s)
    (hfree : ∀ s ∈ L, s ∉ P) (hAL : Disjoint A L) :
    mobiusDivisorEnergyBooleanAlternating M (P ∪ L) A =
      mobiusDivisorEnergyBooleanAlternating M P A +
        2 * (∑ s ∈ L, mobiusDivisorDilationChannel M s) *
          ((-1 : ℝ) ^ A.card * mobiusDivisorSelectionFibre M P A) := by
  let S := ∑ s ∈ L, mobiusDivisorDilationChannel M s
  let T := ∑ s ∈ L, (mobiusDivisorDilationChannel M s) ^ 2
  have hterm (U : Finset ℕ) (hU : U ∈ A.powerset) :
      mobiusDivisorSelectionEnergy M ((P ∪ L) ∪ U) =
        mobiusDivisorSelectionEnergy M (P ∪ U) +
          2 * mobiusDivisorSelectionFibre M (P ∪ U) ∅ * S + S ^ 2 - T := by
    have hfreeU : ∀ s ∈ L, s ∉ P ∪ U := by
      intro s hs hPU
      rcases mem_union.mp hPU with hP | hmemU
      · exact hfree s hs hP
      · exact (Finset.disjoint_left.mp hAL)
          (Finset.mem_powerset.mp hU hmemU) hs
    have hblock := mobiusDivisorSelectionEnergy_union_late_primes M (P ∪ U) L hL hfreeU
    have hunion : (P ∪ L) ∪ U = (P ∪ U) ∪ L := by
      ext x
      simp only [mem_union]
      tauto
    rw [hunion, hblock]
  unfold mobiusDivisorEnergyBooleanAlternating
  calc
    mobiusDivisorBooleanAlternating (P ∪ L) A (mobiusDivisorSelectionEnergy M) =
        mobiusDivisorBooleanAlternating P A (fun Q =>
          mobiusDivisorSelectionEnergy M Q +
            (2 * S) * mobiusDivisorSelectionFibre M Q ∅ + (S ^ 2 - T)) := by
      unfold mobiusDivisorBooleanAlternating
      apply sum_congr rfl
      intro U hU
      rw [hterm U hU]
      ring
    _ = mobiusDivisorBooleanAlternating P A (mobiusDivisorSelectionEnergy M) +
        (2 * S) * mobiusDivisorBooleanAlternating P A
          (fun Q => mobiusDivisorSelectionFibre M Q ∅) +
          (S ^ 2 - T) * mobiusDivisorBooleanAlternating P A (fun _ => 1) := by
      exact mobiusDivisorBooleanAlternating_affine P A
        (mobiusDivisorSelectionEnergy M)
        (fun Q => mobiusDivisorSelectionFibre M Q ∅) (2 * S) (S ^ 2 - T)
    _ = _ := by
      rw [mobiusDivisorSelectionFibre_booleanAlternating M P ∅ A (by simp),
        mobiusDivisorBooleanAlternating_one_eq_zero P A hA]
      simp only [empty_union, mul_zero, add_zero]
      dsimp only [S]

/-- On every nonempty Boolean grade, a late block is a rank-one translation
of the forward energy jet by its signed mass and the matching literal fibre. -/
theorem mobiusDivisorEnergyBooleanDifference_union_late_primes
    (M : ℕ) (P L A : Finset ℕ) (hA : A.Nonempty)
    (hL : ∀ s ∈ L, s.Prime ∧ s < M ∧ M ≤ 2 * s)
    (hfree : ∀ s ∈ L, s ∉ P) (hAL : Disjoint A L) :
    mobiusDivisorEnergyBooleanDifference M (P ∪ L) A =
      mobiusDivisorEnergyBooleanDifference M P A +
        2 * (∑ s ∈ L, mobiusDivisorDilationChannel M s) *
          mobiusDivisorSelectionFibre M P A := by
  have hsign : (-1 : ℝ) ^ A.card * (-1 : ℝ) ^ A.card = 1 := by
    rw [← pow_add, show A.card + A.card = 2 * A.card by omega, pow_mul]
    norm_num
  unfold mobiusDivisorEnergyBooleanDifference
  rw [mobiusDivisorEnergyBooleanAlternating_union_late_primes M P L A hA hL hfree hAL]
  calc
    (-1 : ℝ) ^ A.card *
        (mobiusDivisorEnergyBooleanAlternating M P A +
          2 * (∑ s ∈ L, mobiusDivisorDilationChannel M s) *
            ((-1 : ℝ) ^ A.card * mobiusDivisorSelectionFibre M P A)) =
        (-1 : ℝ) ^ A.card * mobiusDivisorEnergyBooleanAlternating M P A +
          2 * (∑ s ∈ L, mobiusDivisorDilationChannel M s) *
            ((-1 : ℝ) ^ A.card * (-1 : ℝ) ^ A.card) *
              mobiusDivisorSelectionFibre M P A := by ring
    _ = _ := by
      rw [hsign]
      ring

end RHTower
