import GaloisForLFunctions.HTGeometry.AffineEigenbranchGeneralSecondOrderLaw
import GaloisForLFunctions.HTGeometry.BlockExtensionSecondOrderResponse
import GaloisForLFunctions.HTGeometry.QuadraticRateSecondVariation

/-!
# Quadratic-rate rigidity for a one-qubit local extension

This is the inductive half of branchwise quadratic-rate rigidity.  Attach a qubit with local field
`z` to a simple old spectrum and perturb the new edge by `A ⊗ X`.  A quadratic-rate identity for
the extended family restricts, along that edge direction, to `F(x)² = κ(Q₀ + x²Q_V)`; the first
variation vanishes because the perturbation is off-diagonal in the split eigenbasis, so the second
variation gives

`L₀(z) · ∂²ₓL(z,0) = κ Q_V`,

whose left factor is affine in `z` and whose right factor has no spectral pole.  The second-order
response is a simple-pole packet at the ordered old gaps, so every residue vanishes and, since a
nonzero affine function has one root, at most one ordered pair escapes.  The surviving equalities
are the crown graph, which stays connected after one deletion.

Consequently all the coefficients of the extended spectral action coincide.
-/

open Filter Topology
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {A : Type*} [Fintype A] [DecidableEq A]

/-- A finite combination of germs analytic at the base point is differentiable near it, with the
expected derivative. -/
theorem hasDerivAt_analyticCombination {ι : Type*} [Fintype ι] (f : ι → ℂ → ℂ) (c : ι → ℂ)
    (h : ∀ i, AnalyticAt ℂ (f i) 0) :
    ∀ᶠ g in 𝓝 (0 : ℂ),
      HasDerivAt (fun x => ∑ i, c i * f i x) (∑ i, c i * deriv (f i) g) g := by
  have hall : ∀ᶠ g in 𝓝 (0 : ℂ), ∀ i, HasDerivAt (f i) (deriv (f i) g) g := by
    refine Filter.eventually_all.mpr fun i => ?_
    filter_upwards [(h i).eventually_analyticAt] with g hg
    exact hg.differentiableAt.hasDerivAt
  filter_upwards [hall] with g hg
  have hfun : (∑ i, fun x => c i * f i x) = fun x => ∑ i, c i * f i x := by
    funext x
    rw [Finset.sum_apply]
  have hsum : HasDerivAt (∑ i : ι, fun x => c i * f i x) (∑ i : ι, c i * deriv (f i) g) g :=
    HasDerivAt.sum fun i _ => (hg i).const_mul (c i)
  rwa [hfun] at hsum

/-- The derivative combination is itself differentiable at the base point. -/
theorem hasDerivAt_analyticCombination_deriv {ι : Type*} [Fintype ι] (f : ι → ℂ → ℂ) (c : ι → ℂ)
    (h : ∀ i, AnalyticAt ℂ (f i) 0) :
    HasDerivAt (fun g => ∑ i, c i * deriv (f i) g) (∑ i, c i * deriv (deriv (f i)) 0) 0 := by
  have hfun : (∑ i, fun g => c i * deriv (f i) g) = fun g => ∑ i, c i * deriv (f i) g := by
    funext g
    rw [Finset.sum_apply]
  have hsum : HasDerivAt (∑ i : ι, fun g => c i * deriv (f i) g)
      (∑ i : ι, c i * deriv (deriv (f i)) 0) 0 :=
    HasDerivAt.sum fun i _ => ((h i).deriv.differentiableAt.hasDerivAt).const_mul (c i)
  rwa [hfun] at hsum

/-- **The key identity of a one-qubit extension.**  A quadratic-rate identity along the edge
direction produces the affine-times-pole-packet identity at every admissible local field. -/
theorem localExtension_quadraticRate_key
    {E : A → ℂ} {M : Matrix A A ℂ}
    (c : A × Bool → ℂ) {κ Qv : ℂ} {Q₀ : ℂ → ℂ}
    {S : Set ℂ}
    (hinj : ∀ z ∈ S, Function.Injective (layerSplitEnergy E z))
    (branch : ℂ → A × Bool → ℂ → ℂ)
    (hbranch : ∀ z ∈ S, ∀ i, AnalyticAt ℂ (branch z i) 0)
    (hbase : ∀ z ∈ S, ∀ i, branch z i 0 = layerSplitEnergy E z i)
    (hroot : ∀ z ∈ S, ∀ i, ∀ᶠ g in 𝓝 (0 : ℂ), matrixCharpolyRelation
        (Matrix.diagonal (layerSplitEnergy E z) + g • layerCrossPerturbation M, branch z i g) = 0)
    (hident : ∀ z ∈ S, ∀ᶠ g in 𝓝 (0 : ℂ),
        (∑ i, c i * branch z i g) ^ (2 : ℕ) = κ * (Q₀ z + g ^ (2 : ℕ) * Qv)) :
    ∀ z ∈ S,
      ((∑ α, (c (α, false) + c (α, true)) * E α)
          + ((∑ α, c (α, false) - ∑ α, c (α, true)) / 2) * z)
        * (∑ α, ∑ β, (c (α, false) - c (β, true)) * (M α β * M β α) / (z + E α - E β))
        = κ * Qv / 2 := by
  classical
  intro z hz
  have hFd := hasDerivAt_analyticCombination (branch z) c (hbranch z hz)
  have hF'd := hasDerivAt_analyticCombination_deriv (branch z) c (hbranch z hz)
  -- the first variation vanishes: the perturbation is off-diagonal
  have hfirst : ∀ i, deriv (branch z i) 0 = 0 := by
    intro i
    rw [affineEigenbranch_firstDerivative_eq_diagonal (layerSplitEnergy E z) (hinj z hz)
      (layerCrossPerturbation M) i (branch z i) (hbranch z hz i) (hbase z hz i)
      (hroot z hz i)]
    exact layerCrossPerturbation_diagonal M i
  have hF'0 : (∑ i, c i * deriv (branch z i) 0) = 0 := by
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [hfirst i, mul_zero]
  -- the second variation
  have hvar := quadraticRate_secondVariation hFd hF'd hF'0 (hident z hz)
  -- the base value is the affine uncoupled action
  have hbase0 : (∑ i, c i * branch z i 0)
      = (∑ α, (c (α, false) + c (α, true)) * E α)
        + ((∑ α, c (α, false) - ∑ α, c (α, true)) / 2) * z := by
    rw [← layerSplitAction_affine E c z]
    exact Finset.sum_congr rfl fun i _ => by rw [hbase z hz i]
  -- the second derivative is twice the pole packet
  have hsecond : (∑ i, c i * deriv (deriv (branch z i)) 0)
      = 2 * ∑ α, ∑ β, (c (α, false) - c (β, true)) * (M α β * M β α) / (z + E α - E β) := by
    have hterm : ∀ i : A × Bool, deriv (deriv (branch z i)) 0
        = 2 * ∑ y ∈ Finset.univ.erase i,
            layerCrossPerturbation M i y * layerCrossPerturbation M y i
              / (layerSplitEnergy E z i - layerSplitEnergy E z y) := by
      intro i
      exact affineEigenbranch_secondDerivative_eq_general (layerSplitEnergy E z) (hinj z hz)
        (layerCrossPerturbation M) i (branch z i) (hbranch z hz i) (hbase z hz i) (hroot z hz i)
    rw [Finset.sum_congr rfl fun i _ => by rw [hterm i]]
    rw [← layerCrossSecondOrder_weighted_sum E M c z, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hbase0, hsecond] at hvar
  have h2 : (2 : ℂ) ≠ 0 := by norm_num
  field_simp at hvar ⊢
  linear_combination hvar

/-- **Branchwise quadratic-rate rigidity for a one-qubit extension.**  A quadratic-rate identity
for the extended family forces every coefficient of the extended spectral action to coincide. -/
theorem localExtension_quadraticRate_collapse (hcard : 3 ≤ Fintype.card A)
    {E : A → ℂ} (hE : Function.Injective E)
    (hgap : ∀ α β γ δ : A, α ≠ β → γ ≠ δ → E β - E α = E δ - E γ → (α, β) = (γ, δ))
    {M : Matrix A A ℂ} (hM : ∀ α β : A, α ≠ β → M α β * M β α ≠ 0)
    (c : A × Bool → ℂ) {κ Qv : ℂ} {Q₀ : ℂ → ℂ}
    (hL : (∑ α, (c (α, false) + c (α, true)) * E α) ≠ 0
        ∨ ((∑ α, c (α, false) - ∑ α, c (α, true)) / 2) ≠ 0)
    {S : Set ℂ} (hS : S.Infinite)
    (havoid : ∀ z ∈ S, z ≠ 0 ∧ ∀ α β : A, α ≠ β → z ≠ E β - E α)
    (hinj : ∀ z ∈ S, Function.Injective (layerSplitEnergy E z))
    (branch : ℂ → A × Bool → ℂ → ℂ)
    (hbranch : ∀ z ∈ S, ∀ i, AnalyticAt ℂ (branch z i) 0)
    (hbase : ∀ z ∈ S, ∀ i, branch z i 0 = layerSplitEnergy E z i)
    (hroot : ∀ z ∈ S, ∀ i, ∀ᶠ g in 𝓝 (0 : ℂ), matrixCharpolyRelation
        (Matrix.diagonal (layerSplitEnergy E z) + g • layerCrossPerturbation M, branch z i g) = 0)
    (hident : ∀ z ∈ S, ∀ᶠ g in 𝓝 (0 : ℂ),
        (∑ i, c i * branch z i g) ^ (2 : ℕ) = κ * (Q₀ z + g ^ (2 : ℕ) * Qv)) :
    (∀ x y : A, c (x, false) = c (y, false)) ∧ (∀ x y : A, c (x, true) = c (y, true))
      ∧ (∀ x y : A, c (x, false) = c (y, true)) :=
  extensionPacket_crossPair_constant hcard hE hgap
    (w := fun α β => M α β * M β α) hM (fun α => c (α, false)) (fun β => c (β, true))
    hL hS havoid
    (localExtension_quadraticRate_key c hinj branch hbranch hbase hroot hident)

/-- **Lemma A2, inductive step.**  A zero-sum coefficient packet satisfying a quadratic-rate
identity for a one-qubit extension is identically zero. -/
theorem localExtension_quadraticRate_eq_zero (hcard : 3 ≤ Fintype.card A)
    {E : A → ℂ} (hE : Function.Injective E)
    (hgap : ∀ α β γ δ : A, α ≠ β → γ ≠ δ → E β - E α = E δ - E γ → (α, β) = (γ, δ))
    {M : Matrix A A ℂ} (hM : ∀ α β : A, α ≠ β → M α β * M β α ≠ 0)
    (c : A × Bool → ℂ) {κ Qv : ℂ} {Q₀ : ℂ → ℂ}
    (hL : (∑ α, (c (α, false) + c (α, true)) * E α) ≠ 0
        ∨ ((∑ α, c (α, false) - ∑ α, c (α, true)) / 2) ≠ 0)
    {S : Set ℂ} (hS : S.Infinite)
    (havoid : ∀ z ∈ S, z ≠ 0 ∧ ∀ α β : A, α ≠ β → z ≠ E β - E α)
    (hinj : ∀ z ∈ S, Function.Injective (layerSplitEnergy E z))
    (branch : ℂ → A × Bool → ℂ → ℂ)
    (hbranch : ∀ z ∈ S, ∀ i, AnalyticAt ℂ (branch z i) 0)
    (hbase : ∀ z ∈ S, ∀ i, branch z i 0 = layerSplitEnergy E z i)
    (hroot : ∀ z ∈ S, ∀ i, ∀ᶠ g in 𝓝 (0 : ℂ), matrixCharpolyRelation
        (Matrix.diagonal (layerSplitEnergy E z) + g • layerCrossPerturbation M, branch z i g) = 0)
    (hident : ∀ z ∈ S, ∀ᶠ g in 𝓝 (0 : ℂ),
        (∑ i, c i * branch z i g) ^ (2 : ℕ) = κ * (Q₀ z + g ^ (2 : ℕ) * Qv))
    (hzero : ∑ i, c i = 0) : c = 0 := by
  classical
  obtain ⟨hu, hv, huv⟩ := localExtension_quadraticRate_collapse hcard hE hgap hM c hL hS havoid
    hinj branch hbranch hbase hroot hident
  obtain ⟨a₀⟩ : Nonempty A := by
    rw [← Fintype.card_pos_iff]
    omega
  have hconst : ∀ i : A × Bool, c i = c (a₀, false) := by
    rintro ⟨x, r⟩
    cases r with
    | false => exact hu x a₀
    | true => exact (huv a₀ x).symm
  have hcard' : (Fintype.card (A × Bool) : ℂ) * c (a₀, false) = 0 := by
    rw [← hzero, Finset.sum_congr rfl fun i _ => hconst i]
    simp [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
  have hne : (Fintype.card (A × Bool) : ℂ) ≠ 0 := by
    have hpos : 0 < Fintype.card (A × Bool) := by
      rw [Fintype.card_prod]
      have : 0 < Fintype.card A := by omega
      simp only [Fintype.card_bool]
      omega
    exact Nat.cast_ne_zero.mpr hpos.ne'
  have h0 : c (a₀, false) = 0 := by
    rcases mul_eq_zero.mp hcard' with h | h
    · exact absurd h hne
    · exact h
  funext i
  rw [hconst i, h0]
  rfl

end

end GaloisForLFunctions.HTGeometry
