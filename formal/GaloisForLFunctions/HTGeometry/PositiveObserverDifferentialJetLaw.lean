import GaloisForLFunctions.HTGeometry.PositiveObserverCovarianceLaw

/-!
# Differential positive observers and relative jet covariance

This file specializes the algebraic covariance law to the literal differential data of the paper:
source and observer cores, a Leibniz derivation preserving both cores, commutation `Eδ = δE`, and
the generated tower `δ^j f`.  Relative jet freedom then gives the exact hidden-jet identity,
positive-definite covariance matrices of rank `N + 1`, and infinite completed covariance dimension.

The same faithful GNS realization supplies Hermitian symmetry and Cauchy--Schwarz for covariance
and for star-paired connected products.  Multiplicativity is packaged as structure data in the
terminal no-hidden-mode theorem, so the result has no external proof premise.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open scoped InnerProductSpace ComplexOrder

variable {A : Type*} [CStarAlgebra A]

/-- Differential conditional observer on explicit source and observer algebra cores. -/
structure DifferentialConditionalObserver where
  expectation : ConditionalExpectationCore (A := A)
  sourceCore : Subalgebra ℂ A
  observerCore : Subalgebra ℂ A
  observer_le_source : observerCore.toSubmodule ≤ sourceCore.toSubmodule
  source_star_mem : ∀ {a}, a ∈ sourceCore → star a ∈ sourceCore
  observer_star_mem : ∀ {a}, a ∈ observerCore → star a ∈ observerCore
  derivation : A →ₗ[ℂ] A
  leibniz : ∀ a b, derivation (a * b) = derivation a * b + a * derivation b
  derivation_source : ∀ {a}, a ∈ sourceCore → derivation a ∈ sourceCore
  derivation_observer : ∀ {a}, a ∈ observerCore → derivation a ∈ observerCore
  expectation_source : ∀ {a}, a ∈ sourceCore → expectation.map a ∈ observerCore
  expectation_fixed : ∀ {b}, b ∈ observerCore → expectation.map b = b
  commutes_on_source : ∀ {a}, a ∈ sourceCore →
    expectation.map (derivation a) = derivation (expectation.map a)

namespace DifferentialConditionalObserver

variable (D : DifferentialConditionalObserver (A := A))

/-- Literal iterated differential jet `δ^j f`. -/
def jet (D : DifferentialConditionalObserver (A := A)) (f : A) : ℕ → A
  | Nat.zero => f
  | Nat.succ n => D.derivation (jet D f n)

@[simp] theorem jet_zero (f : A) : D.jet f 0 = f := rfl

@[simp] theorem jet_succ (f : A) (n : ℕ) :
    D.jet f (Nat.succ n) = D.derivation (D.jet f n) := rfl

theorem jet_mem_source {f : A} (hf : f ∈ D.sourceCore) :
    ∀ n, D.jet f n ∈ D.sourceCore := by
  intro n
  induction n with
  | zero => exact hf
  | succ n ih => exact D.derivation_source ih

/-- Commutation `Eδ = δE` propagates to every differential jet. -/
theorem expectation_jet {f : A} (hf : f ∈ D.sourceCore) :
    ∀ n, D.expectation.map (D.jet f n) = D.jet (D.expectation.map f) n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [D.jet_succ, D.jet_succ, D.commutes_on_source (D.jet_mem_source hf n), ih]

/-- Exact paper identity `c(δ^j f) = δ^j c(f)`. -/
theorem hiddenComponent_jet {f : A} (hf : f ∈ D.sourceCore) :
    ∀ n, D.expectation.hiddenComponent (D.jet f n) =
      D.jet (D.expectation.hiddenComponent f) n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [D.jet_succ, ConditionalExpectationCore.hiddenComponent,
        D.commutes_on_source (D.jet_mem_source hf n), ← map_sub, ←
        ConditionalExpectationCore.hiddenComponent, ih]
      rfl

end DifferentialConditionalObserver

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Faithful positive GNS realization of a relatively jet-free differential observer. -/
structure DifferentialJetCovarianceRealization
    (D : DifferentialConditionalObserver (A := A)) where
  f : A
  f_mem : f ∈ D.sourceCore
  state : A →ₗ[ℂ] ℂ
  state_positive : ∀ x,
    0 ≤ (state (D.expectation.map (star x * x))).re
  state_faithful : ∀ x,
    state (D.expectation.map (star x * x)) = 0 → x = 0
  gns : A →ₗ[ℂ] H
  gns_injective : Function.Injective gns
  gns_inner_hidden : ∀ a b,
    ⟪gns (D.expectation.hiddenComponent a),
      gns (D.expectation.hiddenComponent b)⟫_ℂ =
      D.expectation.hiddenCovariance state a b
  relativelyJetFree : ∀ (N : ℕ) (b : A) (z : Fin (N + 1) → ℂ),
    b ∈ D.observerCore →
      b + ∑ j, z j • D.jet f j = 0 → b = 0 ∧ ∀ j, z j = 0

namespace DifferentialJetCovarianceRealization

variable {D : DifferentialConditionalObserver (A := A)}
variable (T : DifferentialJetCovarianceRealization D (H := H))

/-- Completed hidden vector represented by the `j`-th differential jet. -/
def hiddenJet (j : ℕ) : H :=
  T.gns (D.expectation.hiddenComponent (D.jet T.f j))

theorem algebraicHiddenJet_linearIndependent (N : ℕ) :
    LinearIndependent ℂ
      (fun j : Fin (N + 1) => D.expectation.hiddenComponent (D.jet T.f j)) := by
  rw [Fintype.linearIndependent_iff]
  intro z hz
  let b : A := -∑ j : Fin (N + 1), z j • D.expectation.map (D.jet T.f j)
  have hb : b ∈ D.observerCore := by
    exact D.observerCore.neg_mem (D.observerCore.sum_mem fun j _ =>
      D.observerCore.toSubmodule.smul_mem (z j)
        (D.expectation_source (D.jet_mem_source T.f_mem j)))
  have hrelation : b + ∑ j : Fin (N + 1), z j • D.jet T.f j = 0 := by
    calc
      b + ∑ j : Fin (N + 1), z j • D.jet T.f j =
          ∑ j : Fin (N + 1), z j • D.expectation.hiddenComponent (D.jet T.f j) := by
            simp only [b, ConditionalExpectationCore.hiddenComponent, smul_sub,
              Finset.sum_sub_distrib]
            abel
      _ = 0 := hz
  exact (T.relativelyJetFree N b z hb hrelation).2

theorem hiddenJet_linearIndependent (N : ℕ) :
    LinearIndependent ℂ (fun j : Fin (N + 1) => T.hiddenJet j) := by
  rw [Fintype.linearIndependent_iff]
  intro z hz
  apply (Fintype.linearIndependent_iff.mp (T.algebraicHiddenJet_linearIndependent N)) z
  apply T.gns_injective
  rw [map_sum, map_zero]
  simpa only [map_smul, hiddenJet] using hz

/-- Covariance Gram matrix of the literal differential jets `δ^j f`. -/
def covarianceGram (N : ℕ) : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ :=
  Matrix.gram ℂ (fun j : Fin (N + 1) => T.hiddenJet j)

theorem covarianceGram_apply (N : ℕ) (i j : Fin (N + 1)) :
    T.covarianceGram N i j =
      D.expectation.hiddenCovariance T.state (D.jet T.f i) (D.jet T.f j) := by
  rw [covarianceGram, Matrix.gram_apply]
  change ⟪T.gns (D.expectation.hiddenComponent (D.jet T.f i)),
    T.gns (D.expectation.hiddenComponent (D.jet T.f j))⟫_ℂ = _
  exact T.gns_inner_hidden _ _

theorem covarianceGram_posDef (N : ℕ) : (T.covarianceGram N).PosDef :=
  Matrix.posDef_gram_of_linearIndependent (T.hiddenJet_linearIndependent N)

/-- Exact rank law `rank G_N = N + 1`. -/
theorem covarianceGram_rank (N : ℕ) : (T.covarianceGram N).rank = N + 1 := by
  simpa using Matrix.rank_of_isUnit (T.covarianceGram N) (T.covarianceGram_posDef N).isUnit

theorem covarianceHilbert_not_finiteDimensional
    (T : DifferentialJetCovarianceRealization D (H := H)) :
    ¬ FiniteDimensional ℂ H := by
  intro hfinite
  letI : FiniteDimensional ℂ H := hfinite
  have hle := (T.hiddenJet_linearIndependent (Module.finrank ℂ H)).fintype_card_le_finrank
  simp only [Fintype.card_fin] at hle
  omega

/-- Covariance kernel is Hermitian. -/
theorem hiddenCovariance_conj_symm (a b : A) :
    starRingEnd ℂ (D.expectation.hiddenCovariance T.state b a) =
      D.expectation.hiddenCovariance T.state a b := by
  rw [← T.gns_inner_hidden, ← T.gns_inner_hidden]
  exact inner_conj_symm _ _

theorem hiddenCovariance_self_eq_norm_sq (a : A) :
    D.expectation.hiddenCovariance T.state a a =
      (‖T.gns (D.expectation.hiddenComponent a)‖ ^ 2 : ℝ) := by
  rw [← T.gns_inner_hidden, inner_self_eq_norm_sq_to_K]
  exact (Complex.ofReal_pow _ 2).symm

/-- Cauchy--Schwarz for the hidden covariance kernel. -/
theorem hiddenCovariance_cauchySchwarz (a b : A) :
    ‖D.expectation.hiddenCovariance T.state a b‖ ≤
      ‖T.gns (D.expectation.hiddenComponent a)‖ *
        ‖T.gns (D.expectation.hiddenComponent b)‖ := by
  rw [← T.gns_inner_hidden]
  exact norm_inner_le_norm _ _

/-- Star-paired connected products are exactly covariance entries. -/
theorem connectedStarPaired_eq_hiddenCovariance (a b : A) :
    D.expectation.connectedProductDefect T.state (star a) b =
      D.expectation.hiddenCovariance T.state a b := by
  rw [D.expectation.connectedProductDefect_eq_hiddenCovariance]
  simp

theorem connectedStarPaired_conj_symm (a b : A) :
    starRingEnd ℂ (D.expectation.connectedProductDefect T.state (star b) a) =
      D.expectation.connectedProductDefect T.state (star a) b := by
  rw [T.connectedStarPaired_eq_hiddenCovariance,
    T.connectedStarPaired_eq_hiddenCovariance]
  exact T.hiddenCovariance_conj_symm a b

theorem connectedStarPaired_cauchySchwarz (a b : A) :
    ‖D.expectation.connectedProductDefect T.state (star a) b‖ ≤
      ‖T.gns (D.expectation.hiddenComponent a)‖ *
        ‖T.gns (D.expectation.hiddenComponent b)‖ := by
  rw [T.connectedStarPaired_eq_hiddenCovariance]
  exact T.hiddenCovariance_cauchySchwarz a b

/-- Every finite star-paired connected-product matrix is positive semidefinite. -/
theorem connectedStarPaired_sum_re_nonneg
    {ι : Type*} [Fintype ι] (a : ι → A) (z : ι → ℂ) :
    0 ≤ (∑ j, ∑ i, star (z i) * z j *
      D.expectation.connectedProductDefect T.state (star (a i)) (a j)).re := by
  simpa only [T.connectedStarPaired_eq_hiddenCovariance] using
    D.expectation.hiddenCovariance_sum_re_nonneg T.state T.state_positive a z

/-- Faithfulness upgrades multiplicativity to identity. -/
theorem expectation_eq_id_of_multiplicative
    (T : DifferentialJetCovarianceRealization D (H := H))
    (hmul : ∀ a b, D.expectation.map (a * b) =
      D.expectation.map a * D.expectation.map b) :
    D.expectation.map = LinearMap.id := by
  apply D.expectation.map_eq_id_of_multiplicative_faithful hmul
  intro x hx
  apply T.state_faithful x
  rw [hx, map_zero]

/-- Packaged differential relative-jet theorem. -/
theorem differential_relativeJetFreedom_capstone :
    (∀ n, D.expectation.hiddenComponent (D.jet T.f n) =
      D.jet (D.expectation.hiddenComponent T.f) n) ∧
      (∀ N, (T.covarianceGram N).PosDef ∧ (T.covarianceGram N).rank = N + 1) ∧
      ¬ FiniteDimensional ℂ H := by
  exact ⟨D.hiddenComponent_jet T.f_mem,
    fun N => ⟨T.covarianceGram_posDef N, T.covarianceGram_rank N⟩,
    T.covarianceHilbert_not_finiteDimensional⟩

end DifferentialJetCovarianceRealization

/-- Faithful differential observer realization whose expectation is also multiplicative. -/
structure MultiplicativeDifferentialJetCovarianceRealization
    (D : DifferentialConditionalObserver (A := A))
    extends DifferentialJetCovarianceRealization D (H := H) where
  multiplicative : ∀ a b, D.expectation.map (a * b) =
    D.expectation.map a * D.expectation.map b

namespace MultiplicativeDifferentialJetCovarianceRealization

variable {D : DifferentialConditionalObserver (A := A)}

/-- A faithful multiplicative conditional observer is the identity, hence has no hidden modes. -/
theorem expectation_eq_id
    (T : MultiplicativeDifferentialJetCovarianceRealization D (H := H)) :
    D.expectation.map = LinearMap.id :=
  T.toDifferentialJetCovarianceRealization.expectation_eq_id_of_multiplicative
    T.multiplicative

end MultiplicativeDifferentialJetCovarianceRealization

end

end GaloisForLFunctions.HTGeometry
