import Mathlib.Analysis.CStarAlgebra.CompletelyPositiveMap
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Positive observer covariance identity

The hidden-component covariance of an idempotent bimodular star-preserving conditional
expectation is exactly its Kadison multiplicativity defect.  This is the algebraic identity in
Theorem 2.1 of the positive-observer card; positivity of a faithful state can then be applied to
the displayed hidden square without any further expansion.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {A : Type*} [CStarAlgebra A]

/-- Algebraic laws of the conditional expectation used by the covariance theorem. -/
structure ConditionalExpectationCore where
  map : A →ₗ[ℂ] A
  idempotent : ∀ a, map (map a) = map a
  map_star : ∀ a, map (star a) = star (map a)
  left_bimodular : ∀ a b, map (map a * b) = map a * map b
  right_bimodular : ∀ a b, map (a * map b) = map a * map b

namespace ConditionalExpectationCore

variable (E : ConditionalExpectationCore (A := A))

/-- Component erased by the observer. -/
def hiddenComponent (a : A) : A :=
  a - E.map a

/-- Hidden covariance read by a linear state after applying the observer. -/
def hiddenCovariance (phi : A →ₗ[ℂ] ℂ) (a b : A) : ℂ :=
  phi (E.map (star (E.hiddenComponent a) * E.hiddenComponent b))

/-- Polarized Kadison multiplicativity defect read by the same state. -/
def observerKadisonCovariance (phi : A →ₗ[ℂ] ℂ) (a b : A) : ℂ :=
  phi (E.map (star a * b) - E.map (star a) * E.map b)

private theorem map_star_map (a : A) : E.map (star (E.map a)) = star (E.map a) := by
  rw [E.map_star, E.idempotent]

/-- Exact observer-defect identity
`phi(E(c(a)^*c(b))) = phi(E(a^*b) - E(a^*)E(b))`. -/
theorem hiddenCovariance_eq_observerKadisonCovariance (phi : A →ₗ[ℂ] ℂ) (a b : A) :
    E.hiddenCovariance phi a b = E.observerKadisonCovariance phi a b := by
  have hright : E.map (star a * E.map b) = E.map (star a) * E.map b :=
    E.right_bimodular (star a) b
  have hleft : E.map (star (E.map a) * b) = E.map (star a) * E.map b := by
    rw [← E.map_star]
    exact E.left_bimodular (star a) b
  have hboth : E.map (star (E.map a) * E.map b) = E.map (star a) * E.map b := by
    rw [E.right_bimodular, E.map_star_map, ← E.map_star]
  unfold hiddenCovariance hiddenComponent observerKadisonCovariance
  rw [star_sub, sub_mul, mul_sub, mul_sub]
  simp only [map_sub]
  rw [hright, hleft, hboth]
  abel

/-- Positivity is immediate on the diagonal because covariance is the state applied to a hidden
square. -/
theorem hiddenCovariance_re_nonneg
    (phi : A →ₗ[ℂ] ℂ) (hphi : ∀ x : A, 0 ≤ (phi (E.map (star x * x))).re) (a : A) :
    0 ≤ (E.hiddenCovariance phi a a).re := by
  exact hphi (E.hiddenComponent a)

/-- Full positive-semidefinite kernel law: every finite covariance quadratic form is nonnegative. -/
theorem hiddenCovariance_sum_re_nonneg
    (phi : A →ₗ[ℂ] ℂ) (hphi : ∀ x : A, 0 ≤ (phi (E.map (star x * x))).re)
    {ι : Type*} [Fintype ι] (a : ι → A) (z : ι → ℂ) :
    0 ≤ (∑ j, ∑ i, star (z i) * z j * E.hiddenCovariance phi (a i) (a j)).re := by
  let x : A := ∑ i, z i • E.hiddenComponent (a i)
  have hx :
      (∑ j, ∑ i, star (z i) * z j * E.hiddenCovariance phi (a i) (a j)) =
        phi (E.map (star x * x)) := by
    simp only [x, hiddenCovariance, star_sum, star_smul, Finset.sum_mul,
      Finset.mul_sum, smul_mul_assoc, mul_smul_comm, map_smul, map_sum]
    simp only [smul_eq_mul, Finset.mul_sum, mul_assoc, mul_left_comm]
  rw [hx]
  exact hphi x

/-- Connected filtered-product defect of the observer. -/
def connectedProductDefect (phi : A →ₗ[ℂ] ℂ) (a b : A) : ℂ :=
  phi (E.map (a * b) - E.map a * E.map b)

/-- Connected products are exactly star-paired hidden covariances. -/
theorem connectedProductDefect_eq_hiddenCovariance
    (phi : A →ₗ[ℂ] ℂ) (a b : A) :
    E.connectedProductDefect phi a b = E.hiddenCovariance phi (star a) b := by
  rw [E.hiddenCovariance_eq_observerKadisonCovariance]
  simp [connectedProductDefect, observerKadisonCovariance]

/-- A faithful multiplicative observer is the identity, hence has no relative hidden modes. -/
theorem map_eq_id_of_multiplicative_faithful
    (hmul : ∀ a b, E.map (a * b) = E.map a * E.map b)
    (hfaith : ∀ x, E.map (star x * x) = 0 → x = 0) :
    E.map = LinearMap.id := by
  apply LinearMap.ext
  intro a
  have hhidden : E.hiddenComponent a = 0 := by
    apply hfaith
    rw [hmul, E.map_star]
    simp [hiddenComponent, E.idempotent]
  simpa [hiddenComponent] using (sub_eq_zero.mp hhidden).symm

end ConditionalExpectationCore

open scoped InnerProductSpace ComplexOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Exact data used by the relative-jet covariance theorem: observer range, jet tower, relative
freeness `(5)`, and a faithful linear GNS realization. -/
structure RelativeJetCovarianceRealization (E : ConditionalExpectationCore (A := A)) where
  observerRange : Submodule ℂ A
  jet : ℕ → A
  observer_mem : ∀ a, E.map a ∈ observerRange
  relativelyJetFree : ∀ (N : ℕ) (b : A) (z : Fin (N + 1) → ℂ),
    b ∈ observerRange →
      b + ∑ j, z j • jet j = 0 → b = 0 ∧ ∀ j, z j = 0
  gns : A →ₗ[ℂ] H
  gns_injective : Function.Injective gns

namespace RelativeJetCovarianceRealization

variable {E : ConditionalExpectationCore (A := A)}

/-- The `j`-th hidden jet in the faithful covariance realization. -/
def hiddenJet (T : RelativeJetCovarianceRealization E (H := H)) (j : ℕ) : H :=
  T.gns (E.hiddenComponent (T.jet j))

/-- Relative jet freedom makes every finite initial hidden family independent before completion. -/
theorem hiddenComponent_linearIndependent
    (T : RelativeJetCovarianceRealization E (H := H)) (N : ℕ) :
    LinearIndependent ℂ (fun j : Fin (N + 1) => E.hiddenComponent (T.jet j)) := by
  rw [Fintype.linearIndependent_iff]
  intro z hz
  let b : A := -∑ j : Fin (N + 1), z j • E.map (T.jet j)
  have hb : b ∈ T.observerRange := by
    exact T.observerRange.neg_mem (T.observerRange.sum_mem fun j _ =>
      T.observerRange.smul_mem (z j) (T.observer_mem (T.jet j)))
  have hrelation : b + ∑ j : Fin (N + 1), z j • T.jet j = 0 := by
    calc
      b + ∑ j : Fin (N + 1), z j • T.jet j =
          ∑ j : Fin (N + 1), z j • E.hiddenComponent (T.jet j) := by
            simp only [b, ConditionalExpectationCore.hiddenComponent, smul_sub,
              Finset.sum_sub_distrib]
            abel
      _ = 0 := hz
  exact (T.relativelyJetFree N b z hb hrelation).2

/-- Faithfulness of the GNS realization preserves finite hidden-jet independence. -/
theorem hiddenJet_linearIndependent
    (T : RelativeJetCovarianceRealization E (H := H)) (N : ℕ) :
    LinearIndependent ℂ (fun j : Fin (N + 1) => T.hiddenJet j) := by
  rw [Fintype.linearIndependent_iff]
  intro z hz
  apply (Fintype.linearIndependent_iff.mp (T.hiddenComponent_linearIndependent N)) z
  apply T.gns_injective
  rw [map_sum, map_zero]
  simpa only [map_smul, hiddenJet] using hz

/-- Covariance Gram matrix of the first `N + 1` hidden jets. -/
def covarianceGram (T : RelativeJetCovarianceRealization E (H := H)) (N : ℕ) :
    Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ :=
  Matrix.gram ℂ (fun j : Fin (N + 1) => T.hiddenJet j)

/-- Every finite hidden covariance Gram is positive definite. -/
theorem covarianceGram_posDef
    (T : RelativeJetCovarianceRealization E (H := H)) (N : ℕ) :
    (T.covarianceGram N).PosDef :=
  Matrix.posDef_gram_of_linearIndependent (T.hiddenJet_linearIndependent N)

/-- Exact covariance-rank law: the `N`-jet Gram has rank `N + 1`. -/
theorem covarianceGram_rank
    (T : RelativeJetCovarianceRealization E (H := H)) (N : ℕ) :
    (T.covarianceGram N).rank = N + 1 := by
  simpa using Matrix.rank_of_isUnit (T.covarianceGram N) (T.covarianceGram_posDef N).isUnit

/-- Arbitrarily long independent hidden-jet packets force infinite covariance dimension. -/
theorem covarianceHilbert_not_finiteDimensional
    (T : RelativeJetCovarianceRealization E (H := H)) :
    ¬ FiniteDimensional ℂ H := by
  intro hfinite
  letI : FiniteDimensional ℂ H := hfinite
  have hle := (T.hiddenJet_linearIndependent (Module.finrank ℂ H)).fintype_card_le_finrank
  simp only [Fintype.card_fin] at hle
  omega

/-- Canonical positive norm action has a noncompact unit sublevel under relative jet freedom. -/
theorem canonicalPositiveAction_unitSublevel_not_compact
    (T : RelativeJetCovarianceRealization E (H := H)) :
    ¬ IsCompact {x : H | ‖x‖ ^ 2 ≤ 1} := by
  intro hcompact
  have hset : {x : H | ‖x‖ ^ 2 ≤ 1} = Metric.closedBall 0 1 := by
    ext x
    simp only [Set.mem_setOf_eq, Metric.mem_closedBall, dist_zero_right]
    constructor
    · intro hx
      nlinarith [norm_nonneg x]
    · intro hx
      nlinarith [norm_nonneg x]
  rw [hset] at hcompact
  exact T.covarianceHilbert_not_finiteDimensional
    (FiniteDimensional.of_isCompact_closedBall₀ ℂ zero_lt_one hcompact)

/-- Packaged relative-jet covariance theorem. -/
theorem relativeJetFreedom_forces_infinite_covariance_rank
    (T : RelativeJetCovarianceRealization E (H := H)) :
    (∀ N, (T.covarianceGram N).PosDef ∧ (T.covarianceGram N).rank = N + 1) ∧
      ¬ FiniteDimensional ℂ H := by
  exact ⟨fun N => ⟨T.covarianceGram_posDef N, T.covarianceGram_rank N⟩,
    T.covarianceHilbert_not_finiteDimensional⟩

end RelativeJetCovarianceRealization

end

end GaloisForLFunctions.HTGeometry
