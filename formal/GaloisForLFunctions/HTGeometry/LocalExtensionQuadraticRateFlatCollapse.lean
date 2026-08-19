import GaloisForLFunctions.HTGeometry.LocalExtensionQuadraticRateCollapse

/-!
# The degenerate branch of quadratic-rate rigidity for a one-qubit extension

`localExtension_quadraticRate_eq_zero` assumes that the uncoupled spectral action `L₀` of the
extension is not identically zero in the new local field.  This module removes that hypothesis.

If `L₀ ≡ 0` then the key identity `L₀(z)·∂²ₓL(z,0) = κ Q_V` degenerates to `κ Q_V = 0`, so a probe
carrying a nonzero rate forces `κ = 0`.  The quadratic-rate identity then reads
`(∑ cᵢλᵢ)² = 0`, hence `∑ cᵢλᵢ = 0` on a whole neighbourhood of the uncoupled point, and its
second derivative is the same simple-pole packet -- now with the *constant* multiplier one.  A
constant nonzero multiplier has no root, so no ordered pair is exceptional at all, and the crown
graph collapses every layer coefficient.

Consequently a zero-sum coefficient packet satisfying a quadratic-rate identity for a one-qubit
extension vanishes, with no nondegeneracy hypothesis on the packet.
-/

open Filter Topology
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {A : Type*} [Fintype A] [DecidableEq A]

omit [DecidableEq A] in
/-- A crown-constant zero-sum packet on the split labels vanishes. -/
theorem crossPairConstant_eq_zero_of_sum_zero (hcard : 0 < Fintype.card A) (c : A × Bool → ℂ)
    (hu : ∀ x y : A, c (x, false) = c (y, false))
    (huv : ∀ x y : A, c (x, false) = c (y, true))
    (hzero : ∑ i, c i = 0) : c = 0 := by
  classical
  obtain ⟨a₀⟩ : Nonempty A := Fintype.card_pos_iff.mp hcard
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

/-- **The second-order response of the extension is the crown pole packet.**  This is the
computation inside the key identity, isolated so the degenerate branch can reuse it. -/
theorem localExtension_secondDeriv_sum
    {E : A → ℂ} {M : Matrix A A ℂ} (c : A × Bool → ℂ) {z : ℂ}
    (hinj : Function.Injective (layerSplitEnergy E z))
    (branch : A × Bool → ℂ → ℂ)
    (hbranch : ∀ i, AnalyticAt ℂ (branch i) 0)
    (hbase : ∀ i, branch i 0 = layerSplitEnergy E z i)
    (hroot : ∀ i, ∀ᶠ g in 𝓝 (0 : ℂ), matrixCharpolyRelation
        (Matrix.diagonal (layerSplitEnergy E z) + g • layerCrossPerturbation M, branch i g) = 0) :
    (∑ i, c i * deriv (deriv (branch i)) 0)
      = 2 * ∑ α, ∑ β, (c (α, false) - c (β, true)) * (M α β * M β α) / (z + E α - E β) := by
  classical
  have hterm : ∀ i : A × Bool, deriv (deriv (branch i)) 0
      = 2 * ∑ y ∈ Finset.univ.erase i,
          layerCrossPerturbation M i y * layerCrossPerturbation M y i
            / (layerSplitEnergy E z i - layerSplitEnergy E z y) := by
    intro i
    exact affineEigenbranch_secondDerivative_eq_general (layerSplitEnergy E z) hinj
      (layerCrossPerturbation M) i (branch i) (hbranch i) (hbase i) (hroot i)
  rw [Finset.sum_congr rfl fun i _ => by rw [hterm i]]
  rw [← layerCrossSecondOrder_weighted_sum E M c z, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- **The degenerate identity.**  A vanishing square of the spectral action makes the crown pole
packet vanish at that local field. -/
theorem localExtension_packet_eq_zero_of_flatSquare
    {E : A → ℂ} {M : Matrix A A ℂ} (c : A × Bool → ℂ) {z : ℂ}
    (hinj : Function.Injective (layerSplitEnergy E z))
    (branch : A × Bool → ℂ → ℂ)
    (hbranch : ∀ i, AnalyticAt ℂ (branch i) 0)
    (hbase : ∀ i, branch i 0 = layerSplitEnergy E z i)
    (hroot : ∀ i, ∀ᶠ g in 𝓝 (0 : ℂ), matrixCharpolyRelation
        (Matrix.diagonal (layerSplitEnergy E z) + g • layerCrossPerturbation M, branch i g) = 0)
    (hident : ∀ᶠ g in 𝓝 (0 : ℂ), (∑ i, c i * branch i g) ^ 2 = 0) :
    (∑ α, ∑ β, (c (α, false) - c (β, true)) * (M α β * M β α) / (z + E α - E β)) = 0 := by
  classical
  have hFzero : ∀ᶠ g in 𝓝 (0 : ℂ), (∑ i, c i * branch i g) = 0 := by
    filter_upwards [hident] with g hg
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hg
  have hFd := hasDerivAt_analyticCombination branch c hbranch
  have hF'd := hasDerivAt_analyticCombination_deriv branch c hbranch
  have hderiv1 : ∀ᶠ g in 𝓝 (0 : ℂ),
      deriv (fun x => ∑ i, c i * branch i x) g = ∑ i, c i * deriv (branch i) g := by
    filter_upwards [hFd] with g hg using hg.deriv
  have hderiv0 : ∀ᶠ g in 𝓝 (0 : ℂ), deriv (fun x => ∑ i, c i * branch i x) g = 0 := by
    filter_upwards [hFzero.eventually_nhds] with g hg
    have hEq : (fun x => ∑ i, c i * branch i x) =ᶠ[𝓝 g] fun _ => (0 : ℂ) := hg
    rw [hEq.deriv_eq]
    simp
  have hG : (fun _ : ℂ => (0 : ℂ)) =ᶠ[𝓝 (0 : ℂ)] fun g => ∑ i, c i * deriv (branch i) g := by
    filter_upwards [hderiv1, hderiv0] with g h1 h2
    rw [← h1, h2]
  have hsecondZero : (∑ i, c i * deriv (deriv (branch i)) 0) = 0 := by
    have hconst : HasDerivAt (fun _ : ℂ => (0 : ℂ))
        (∑ i, c i * deriv (deriv (branch i)) 0) 0 := hF'd.congr_of_eventuallyEq hG
    exact hconst.unique (hasDerivAt_const 0 0)
  have hsum := localExtension_secondDeriv_sum c hinj branch hbranch hbase hroot
  rw [hsum] at hsecondZero
  have h2 : (2 : ℂ) ≠ 0 := by norm_num
  rcases mul_eq_zero.mp hsecondZero with h | h
  · exact absurd h h2
  · exact h

/-- **Lemma A2, degenerate branch.**  A zero-sum coefficient packet whose uncoupled action
vanishes identically still vanishes, provided the probe carries a nonzero rate. -/
theorem localExtension_quadraticRate_eq_zero_of_flat (hcard : 3 ≤ Fintype.card A)
    {E : A → ℂ} (hE : Function.Injective E)
    (hgap : ∀ α β γ δ : A, α ≠ β → γ ≠ δ → E β - E α = E δ - E γ → (α, β) = (γ, δ))
    {M : Matrix A A ℂ} (hM : ∀ α β : A, α ≠ β → M α β * M β α ≠ 0)
    (c : A × Bool → ℂ) {κ Qv : ℂ} {Q₀ : ℂ → ℂ} (hQv : Qv ≠ 0)
    (hflat : (∑ α, (c (α, false) + c (α, true)) * E α) = 0
        ∧ ((∑ α, c (α, false) - ∑ α, c (α, true)) / 2) = 0)
    {S : Set ℂ} (hS : S.Infinite)
    (havoid : ∀ z ∈ S, z ≠ 0 ∧ ∀ α β : A, α ≠ β → z ≠ E β - E α)
    (hinj : ∀ z ∈ S, Function.Injective (layerSplitEnergy E z))
    (branch : ℂ → A × Bool → ℂ → ℂ)
    (hbranch : ∀ z ∈ S, ∀ i, AnalyticAt ℂ (branch z i) 0)
    (hbase : ∀ z ∈ S, ∀ i, branch z i 0 = layerSplitEnergy E z i)
    (hroot : ∀ z ∈ S, ∀ i, ∀ᶠ g in 𝓝 (0 : ℂ), matrixCharpolyRelation
        (Matrix.diagonal (layerSplitEnergy E z) + g • layerCrossPerturbation M, branch z i g) = 0)
    (hident : ∀ z ∈ S, ∀ᶠ g in 𝓝 (0 : ℂ),
        (∑ i, c i * branch z i g) ^ 2 = κ * (Q₀ z + g ^ 2 * Qv))
    (hzero : ∑ i, c i = 0) : c = 0 := by
  classical
  obtain ⟨z₀, hz₀⟩ := hS.nonempty
  have hkey := localExtension_quadraticRate_key c hinj branch hbranch hbase hroot hident z₀ hz₀
  rw [hflat.1, hflat.2] at hkey
  have h0 : (0 : ℂ) = κ * Qv / 2 := by simpa using hkey
  have hκ : κ = 0 := by
    have hprod : κ * Qv = 0 := by linear_combination (-2 : ℂ) * h0
    rcases mul_eq_zero.mp hprod with h | h
    · exact h
    · exact absurd h hQv
  have hidentity : ∀ z ∈ S,
      ((1 : ℂ) + 0 * z) * (∑ α, ∑ β, (c (α, false) - c (β, true)) * (M α β * M β α)
        / (z + E α - E β)) = 0 := by
    intro z hz
    have hpacket := localExtension_packet_eq_zero_of_flatSquare c (hinj z hz) (branch z)
      (hbranch z hz) (hbase z hz) (hroot z hz)
      (by
        filter_upwards [hident z hz] with g hg
        rw [hg, hκ, zero_mul])
    rw [hpacket]
    ring
  obtain ⟨hu, -, huv⟩ := extensionPacket_crossPair_constant hcard hE hgap
    (w := fun α β => M α β * M β α) hM (fun α => c (α, false)) (fun β => c (β, true))
    (p := 1) (q := 0) (cst := 0) (Or.inl one_ne_zero) hS havoid hidentity
  exact crossPairConstant_eq_zero_of_sum_zero (by omega) c hu huv hzero

/-- **Lemma A2, unconditional.**  A zero-sum coefficient packet satisfying a quadratic-rate
identity for a one-qubit extension vanishes.  No nondegeneracy hypothesis on the packet is
needed: the degenerate branch is handled by the constant-multiplier residue argument. -/
theorem localExtension_quadraticRate_eq_zero_unconditional (hcard : 3 ≤ Fintype.card A)
    {E : A → ℂ} (hE : Function.Injective E)
    (hgap : ∀ α β γ δ : A, α ≠ β → γ ≠ δ → E β - E α = E δ - E γ → (α, β) = (γ, δ))
    {M : Matrix A A ℂ} (hM : ∀ α β : A, α ≠ β → M α β * M β α ≠ 0)
    (c : A × Bool → ℂ) {κ Qv : ℂ} {Q₀ : ℂ → ℂ} (hQv : Qv ≠ 0)
    {S : Set ℂ} (hS : S.Infinite)
    (havoid : ∀ z ∈ S, z ≠ 0 ∧ ∀ α β : A, α ≠ β → z ≠ E β - E α)
    (hinj : ∀ z ∈ S, Function.Injective (layerSplitEnergy E z))
    (branch : ℂ → A × Bool → ℂ → ℂ)
    (hbranch : ∀ z ∈ S, ∀ i, AnalyticAt ℂ (branch z i) 0)
    (hbase : ∀ z ∈ S, ∀ i, branch z i 0 = layerSplitEnergy E z i)
    (hroot : ∀ z ∈ S, ∀ i, ∀ᶠ g in 𝓝 (0 : ℂ), matrixCharpolyRelation
        (Matrix.diagonal (layerSplitEnergy E z) + g • layerCrossPerturbation M, branch z i g) = 0)
    (hident : ∀ z ∈ S, ∀ᶠ g in 𝓝 (0 : ℂ),
        (∑ i, c i * branch z i g) ^ 2 = κ * (Q₀ z + g ^ 2 * Qv))
    (hzero : ∑ i, c i = 0) : c = 0 := by
  by_cases hL : (∑ α, (c (α, false) + c (α, true)) * E α) ≠ 0
      ∨ ((∑ α, c (α, false) - ∑ α, c (α, true)) / 2) ≠ 0
  · exact localExtension_quadraticRate_eq_zero hcard hE hgap hM c hL hS havoid hinj branch
      hbranch hbase hroot hident hzero
  · push Not at hL
    exact localExtension_quadraticRate_eq_zero_of_flat hcard hE hgap hM c hQv hL hS havoid hinj
      branch hbranch hbase hroot hident hzero


/-- **Chart escape for the quadratic-rate relation.**  Contrapositive of the unconditional
Lemma A2: a nonzero zero-sum coefficient packet cannot satisfy the quadratic-rate identity
throughout the one-qubit extension slice, so some admissible local field escapes it.  This is the
`hlabel` input of the analytic-escape machinery, in the extension slice. -/
theorem exists_localField_quadraticRate_not_eventually (hcard : 3 ≤ Fintype.card A)
    {E : A → ℂ} (hE : Function.Injective E)
    (hgap : ∀ α β γ δ : A, α ≠ β → γ ≠ δ → E β - E α = E δ - E γ → (α, β) = (γ, δ))
    {M : Matrix A A ℂ} (hM : ∀ α β : A, α ≠ β → M α β * M β α ≠ 0)
    (c : A × Bool → ℂ) {κ Qv : ℂ} {Q₀ : ℂ → ℂ} (hQv : Qv ≠ 0)
    {S : Set ℂ} (hS : S.Infinite)
    (havoid : ∀ z ∈ S, z ≠ 0 ∧ ∀ α β : A, α ≠ β → z ≠ E β - E α)
    (hinj : ∀ z ∈ S, Function.Injective (layerSplitEnergy E z))
    (branch : ℂ → A × Bool → ℂ → ℂ)
    (hbranch : ∀ z ∈ S, ∀ i, AnalyticAt ℂ (branch z i) 0)
    (hbase : ∀ z ∈ S, ∀ i, branch z i 0 = layerSplitEnergy E z i)
    (hroot : ∀ z ∈ S, ∀ i, ∀ᶠ g in 𝓝 (0 : ℂ), matrixCharpolyRelation
        (Matrix.diagonal (layerSplitEnergy E z) + g • layerCrossPerturbation M, branch z i g) = 0)
    (hzero : ∑ i, c i = 0) (hcne : c ≠ 0) :
    ∃ z ∈ S, ¬ (∀ᶠ g in 𝓝 (0 : ℂ),
      (∑ i, c i * branch z i g) ^ 2 = κ * (Q₀ z + g ^ 2 * Qv)) := by
  by_contra hcon
  push Not at hcon
  exact hcne (localExtension_quadraticRate_eq_zero_unconditional hcard hE hgap hM c hQv hS
    havoid hinj branch hbranch hbase hroot hcon hzero)


end

end GaloisForLFunctions.HTGeometry
