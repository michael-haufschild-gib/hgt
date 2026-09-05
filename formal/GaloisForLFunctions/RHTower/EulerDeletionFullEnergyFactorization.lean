import GaloisForLFunctions.RHTower.EulerDeletionFactorizationCurvature

/-!
# Complete quadratic energy in arithmetic factorization

For coprime labels, the actual coefficient relation is `a_pq = a_p + a_q - a_p a_q`.
Expanding its square retains both mixed orientations and the interaction square.
The resulting half-energy increment has zero factorization curvature coefficient by
coefficient. The source terms omitted by selecting only the grade-mixing pairing
carry exactly the curvature of that pairing. All infinite identities have proved
summability in the actual Dirichlet chamber; no zero or boundary-flatness premise is used.

This is polarization of the full source, not annihilation of one selected component.
-/

noncomputable section
open scoped BigOperators
namespace RHTower.DeletionFullEnergy

/-- All cross terms in half the literal composite-source square. -/
def fullCoefficient (p q n : ℕ) : ℝ :=
  let a : ℝ := blockDeletionCoefficient p n
  let b : ℝ := blockDeletionCoefficient q n
  a * b + (a * b) ^ 2 / 2 - a ^ 2 * b - a * b ^ 2

/-- The actual square terms left out when selecting only the `a * b²` channel. -/
def omittedCoefficient (p q n : ℕ) : ℝ :=
  let a : ℝ := blockDeletionCoefficient p n
  let b : ℝ := blockDeletionCoefficient q n
  a * b + (a * b) ^ 2 / 2 - a ^ 2 * b

theorem fullCoefficient_eq {p q : ℕ} (hpq : Nat.Coprime p q) (n : ℕ) :
    fullCoefficient p q n =
      ((blockDeletionCoefficient (p * q) n : ℝ) ^ 2 -
        (blockDeletionCoefficient p n : ℝ) ^ 2 -
        (blockDeletionCoefficient q n : ℝ) ^ 2) / 2 := by
  have h : (blockDeletionCoefficient (p * q) n : ℝ) =
      (blockDeletionCoefficient p n : ℝ) + (blockDeletionCoefficient q n : ℝ) -
        (blockDeletionCoefficient p n : ℝ) * (blockDeletionCoefficient q n : ℝ) := by
    have hc : (blockDeletionCoefficient p n : ℝ) * (blockDeletionCoefficient q n : ℝ) =
        (blockDeletionCoefficient p n : ℝ) + (blockDeletionCoefficient q n : ℝ) -
          (blockDeletionCoefficient (p * q) n : ℝ) := by
      exact_mod_cast blockDeletionCoefficient_mul_eq_add_sub_product_of_coprime hpq n
    linarith
  rw [fullCoefficient, h]
  ring

/-- Full source factorization is flat at each coefficient, before choosing a weight. -/
theorem fullCoefficient_curvature_zero {p q r : ℕ}
    (hpq : Nat.Coprime p q) (hpr : Nat.Coprime p r) (hqr : Nat.Coprime q r) (n : ℕ) :
    fullCoefficient p q n + fullCoefficient (p * q) r n -
      fullCoefficient q r n - fullCoefficient p (q * r) n = 0 := by
  rw [fullCoefficient_eq hpq, fullCoefficient_eq (Nat.Coprime.mul_left hpr hqr),
    fullCoefficient_eq hqr, fullCoefficient_eq (Nat.Coprime.mul_right hpq hpr),
    Nat.mul_assoc]
  ring

/-- No cutoff or nonnegative-weight assumption is needed for the full conservation law. -/
theorem weighted_prefix_curvature_zero {p q r : ℕ}
    (hpq : Nat.Coprime p q) (hpr : Nat.Coprime p r) (hqr : Nat.Coprime q r)
    (w : ℕ → ℝ) (N : ℕ) :
    ∑ n ∈ Finset.range N,
      (fullCoefficient p q n + fullCoefficient (p * q) r n -
        fullCoefficient q r n - fullCoefficient p (q * r) n) * w n = 0 := by
  simp only [fullCoefficient_curvature_zero hpq hpr hqr, zero_mul, Finset.sum_const_zero]

def fullEnergy (α : ℝ) (p q : ℕ) : ℝ :=
  ∑' n, fullCoefficient p q n * deletionDirichletWeight α n

def omittedEnergy (α : ℝ) (p q : ℕ) : ℝ :=
  ∑' n, omittedCoefficient p q n * deletionDirichletWeight α n

private theorem summable_square {α : ℝ} (hα : 1 < α) (p : ℕ) :
    Summable (fun n => (blockDeletionCoefficient p n : ℝ) ^ 2 *
      deletionDirichletWeight α n) := by
  simpa only [pow_two] using summable_deletionDirichlet_gram hα p p

theorem summable_fullCoefficient {α : ℝ} (hα : 1 < α)
    {p q : ℕ} (hpq : Nat.Coprime p q) :
    Summable (fun n => fullCoefficient p q n * deletionDirichletWeight α n) := by
  apply ((((summable_square hα (p * q)).sub (summable_square hα p)).sub
    (summable_square hα q)).mul_left (1 / 2 : ℝ)).congr
  intro n
  rw [fullCoefficient_eq hpq]
  ring

/-- The complete readout is the half-energy coboundary, not the selected grade pairing. -/
theorem fullEnergy_eq {α : ℝ} (hα : 1 < α)
    {p q : ℕ} (hpq : Nat.Coprime p q) :
    fullEnergy α p q =
      (deletionSourceEnergy α (p * q) - deletionSourceEnergy α p -
        deletionSourceEnergy α q) / 2 := by
  have hterm (n : ℕ) : fullCoefficient p q n * deletionDirichletWeight α n =
      (1 / 2 : ℝ) *
        ((blockDeletionCoefficient (p * q) n : ℝ) ^ 2 * deletionDirichletWeight α n -
          (blockDeletionCoefficient p n : ℝ) ^ 2 * deletionDirichletWeight α n -
          (blockDeletionCoefficient q n : ℝ) ^ 2 * deletionDirichletWeight α n) := by
    rw [fullCoefficient_eq hpq]
    ring
  simp_rw [fullEnergy, hterm]
  rw [tsum_mul_left,
    ((summable_square hα (p * q)).sub (summable_square hα p)).tsum_sub
      (summable_square hα q),
    (summable_square hα (p * q)).tsum_sub (summable_square hα p)]
  simp only [deletionSourceEnergy]
  ring

/-- The complete quadratic readout is the literal Mellin-source norm-square increment. -/
theorem fullEnergy_eq_mellinNormSq {s : ℂ} (hs : 1 / 2 < s.re)
    {p q : ℕ} (hpq : Nat.Coprime p q) :
    fullEnergy (2 * s.re) p q =
      ((∑' n, Complex.normSq (deletionMellinSource (p * q) s n)) -
        (∑' n, Complex.normSq (deletionMellinSource p s n)) -
        (∑' n, Complex.normSq (deletionMellinSource q s n))) / 2 := by
  simp only [tsum_normSq_deletionMellinSource hs]
  exact fullEnergy_eq (by linarith) hpq

/-- Literal full-energy factorization has no exponent-dependent associator. -/
theorem fullEnergy_curvature_zero {α : ℝ} (hα : 1 < α) {p q r : ℕ}
    (hpq : Nat.Coprime p q) (hpr : Nat.Coprime p r) (hqr : Nat.Coprime q r) :
    fullEnergy α p q + fullEnergy α (p * q) r -
      fullEnergy α q r - fullEnergy α p (q * r) = 0 := by
  rw [fullEnergy_eq hα hpq, fullEnergy_eq hα (Nat.Coprime.mul_left hpr hqr),
    fullEnergy_eq hα hqr, fullEnergy_eq hα (Nat.Coprime.mul_right hpq hpr),
    Nat.mul_assoc]
  ring

theorem summable_selectedCoefficient {α : ℝ} (hα : 1 < α) (p q : ℕ) :
    Summable (fun n => (blockDeletionCoefficient p n : ℝ) *
      (blockDeletionCoefficient q n : ℝ) ^ 2 * deletionDirichletWeight α n) := by
  apply (((summable_deletionDirichlet_first hα p).mul_left ((q : ℝ) - 1)).add
    ((summable_deletionDirichlet_gram hα p q).mul_left (2 - (q : ℝ)))).congr
  intro n
  have hsquare : (blockDeletionCoefficient q n : ℝ) ^ 2 =
      (q : ℝ) - 1 + (2 - (q : ℝ)) * (blockDeletionCoefficient q n : ℝ) := by
    exact_mod_cast blockDeletionCoefficient_sq_eq q n
  rw [hsquare]
  ring

theorem omittedCoefficient_eq (p q n : ℕ) :
    omittedCoefficient p q n = fullCoefficient p q n +
      (blockDeletionCoefficient p n : ℝ) * (blockDeletionCoefficient q n : ℝ) ^ 2 := by
  dsimp [omittedCoefficient, fullCoefficient]
  ring

theorem summable_omittedCoefficient {α : ℝ} (hα : 1 < α)
    {p q : ℕ} (hpq : Nat.Coprime p q) :
    Summable (fun n => omittedCoefficient p q n * deletionDirichletWeight α n) := by
  simpa only [omittedCoefficient_eq, add_mul] using
    (summable_fullCoefficient hα hpq).add (summable_selectedCoefficient hα p q)

/-- Omitted terms are fixed by the source square; none is chosen as an adjustable counterterm. -/
theorem omittedEnergy_eq {α : ℝ} (hα : 1 < α)
    {p q : ℕ} (hpq : Nat.Coprime p q) :
    omittedEnergy α p q = fullEnergy α p q + deletionFactorizationGradeCross α p q := by
  simp_rw [omittedEnergy, omittedCoefficient_eq, add_mul]
  rw [(summable_fullCoefficient hα hpq).tsum_add (summable_selectedCoefficient hα p q)]
  congr 1
  apply tsum_congr
  intro n
  simp only [deletionFactorizationInteraction, Int.cast_mul]
  ring

/-- The terms discarded by scalar grade selection carry exactly its nonzero curvature. -/
theorem omittedEnergy_curvature_eq {α : ℝ} (hα : 1 < α) {p q r : ℕ}
    (hpq : Nat.Coprime p q) (hpr : Nat.Coprime p r) (hqr : Nat.Coprime q r) :
    omittedEnergy α p q + omittedEnergy α (p * q) r -
      omittedEnergy α q r - omittedEnergy α p (q * r) =
        deletionFactorizationGradeCurvature α p q r := by
  rw [omittedEnergy_eq hα hpq, omittedEnergy_eq hα (Nat.Coprime.mul_left hpr hqr),
    omittedEnergy_eq hα hqr, omittedEnergy_eq hα (Nat.Coprime.mul_right hpq hpr)]
  have hflat := fullEnergy_curvature_zero hα hpq hpr hqr
  dsimp only [deletionFactorizationGradeCurvature]
  linarith

/-- In the off-critical chamber the omitted source channels have strictly nonzero boundary. -/
theorem omittedEnergy_curvature_neg {α : ℝ} (hα : 1 < α) (hα2 : α < 2)
    {p q r : ℕ} (hp : 1 < p) (hq : 1 < q) (hr : 1 < r)
    (hpq : Nat.Coprime p q) (hpr : Nat.Coprime p r) (hqr : Nat.Coprime q r) :
    omittedEnergy α p q + omittedEnergy α (p * q) r -
      omittedEnergy α q r - omittedEnergy α p (q * r) < 0 := by
  rw [omittedEnergy_curvature_eq hα hpq hpr hqr]
  exact deletionFactorizationGradeCurvature_neg_of_pairwise_coprime
    hα hα2 hp hq hr hpq hpr hqr

end RHTower.DeletionFullEnergy

