/-
# Cross-ratio obstruction for deck-normalized modular lifts

This is the first closed branch of the hRigid/Montel assembly after removing the false
closed-disk-extension assumption.  If the modular-lambda lifts have been deck-normalized so that
their center values remain in a strict subdisk, the generic normalized-lift extraction gives a
spherical normal subsequence.  The frontier cross-ratio obstruction forbids it.
-/
import GaloisForLFunctions.Bottcher.CrossRatioNormalBridge
import GaloisForLFunctions.Bottcher.ModularLambdaCompactRepresentatives

open Complex Metric Set Filter Topology UpperHalfPlane
open scoped UpperHalfPlane

namespace Bottcher

noncomputable section

/-- A genuine frontier cross-ratio family cannot have deck-normalized modular-lambda disk lifts.

The remaining global assembly task is to produce the normalized lift data from the `Γ(2)` deck
action.  Once that data is available, this theorem closes the normal-family contradiction without
any closed-disk extension of `λ ∘ cayleyInv`. -/
theorem no_deckNormalized_modularLift_crossRatio_of_frontier {c α β z₀ : ℂ}
    {ρ Rball s₀ : ℝ} {U : Set ℂ} {Rseq : ℕ → ℂ → ℂ} {gseq : ℕ → ℂ → ℂ}
    (hzfront : z₀ ∈ frontier (filledJulia c)) (hρ0 : 0 < ρ) (hρR : ρ < Rball / 2)
    (hs₀ : s₀ < 1)
    (hU : closedBall z₀ ρ ⊆ U)
    (hαβ : α ≠ β)
    (hβ : ∀ n z, z ∈ U → (quadratic c)^[n] z ≠ β)
    (hα : ∀ z ∈ U, z ≠ α)
    (hpreα : ∀ n z, z ∈ U → (quadratic c)^[n] z ≠ α)
    (hzβ : ∀ z ∈ U, z ≠ β)
    (hRcont : ∀ n, ContinuousOn (Rseq n) (closedBall z₀ ρ))
    (hR : ∀ n, Set.EqOn (Rseq n)
      (fun z => ((quadratic c)^[n] z - α) * (z - β) /
        (((quadratic c)^[n] z - β) * (z - α))) U)
    (hgdiff : ∀ n, DifferentiableOn ℂ (gseq n) (ball z₀ Rball))
    (hgbd : ∀ n z, z ∈ ball z₀ Rball → ‖gseq n z‖ ≤ 1)
    (hgbase : ∀ n, ‖gseq n z₀‖ ≤ s₀)
    (heq : ∀ n, Set.EqOn
      (fun z => stereo (modularLambda (cayleyInv (gseq n z))))
      (fun z => stereo (Rseq n z)) (ball z₀ Rball)) : False := by
  obtain ⟨φ, G, r, hφ, hr0, hrsub, hGcont, hconv⟩ :=
    spherical_normal_of_modularDiskTarget_basepoint_strict_lifts
      (Fseq := fun n z => stereo (Rseq n z)) hρ0 hρR hs₀ hgdiff hgbd hgbase heq
  have hU_r : closedBall z₀ r ⊆ U := fun z hz => hU (hrsub hz)
  have hRcont_r : ∀ n, ContinuousOn (Rseq n) (closedBall z₀ r) :=
    fun n => (hRcont n).mono hrsub
  exact no_spherical_crossRatio_uniform_limit_of_frontier hzfront hr0 hU_r hαβ hβ hα
    hpreα hzβ hRcont_r hR ⟨φ, G, hφ, hGcont, hconv⟩

/-- Basepoint-preimage form of `no_deckNormalized_modularLift_crossRatio_of_frontier`.

It is enough to choose, for each member, a preimage of the center value under `λ` whose Cayley
coordinate stays in a fixed strict subdisk.  The based covering lift then constructs the normalized
holomorphic disk lifts. -/
theorem no_basedPreimage_modularLift_crossRatio_of_frontier {c α β z₀ : ℂ}
    {ρ Rball s₀ : ℝ} {U : Set ℂ} {Rseq : ℕ → ℂ → ℂ}
    (hzfront : z₀ ∈ frontier (filledJulia c)) (hρ0 : 0 < ρ) (hρR : ρ < Rball / 2)
    (hs₀ : s₀ < 1)
    (hU : closedBall z₀ ρ ⊆ U)
    (hαβ : α ≠ β)
    (hβ : ∀ n z, z ∈ U → (quadratic c)^[n] z ≠ β)
    (hα : ∀ z ∈ U, z ≠ α)
    (hpreα : ∀ n z, z ∈ U → (quadratic c)^[n] z ≠ α)
    (hzβ : ∀ z ∈ U, z ≠ β)
    (hRcont : ∀ n, ContinuousOn (Rseq n) (closedBall z₀ ρ))
    (hR : ∀ n, Set.EqOn (Rseq n)
      (fun z => ((quadratic c)^[n] z - α) * (z - β) /
        (((quadratic c)^[n] z - β) * (z - α))) U)
    (hdiff : ∀ n, DifferentiableOn ℂ (Rseq n) (ball z₀ Rball))
    (homit : ∀ n z, z ∈ ball z₀ Rball → Rseq n z ∈ ({0, 1} : Set ℂ)ᶜ)
    (hτ : ∀ n, ∃ τ : ℍ, modularLambda (τ : ℂ) = Rseq n z₀ ∧ ‖cayley (τ : ℂ)‖ ≤ s₀) :
    False := by
  have hRball : 0 < Rball := by linarith
  choose τ hτeq hτbd using hτ
  have hlift : ∀ n, ∃ g : ℂ → ℂ,
      DifferentiableOn ℂ g (ball z₀ Rball) ∧
      (∀ z ∈ ball z₀ Rball, ‖g z‖ ≤ 1) ∧
      g z₀ = cayley (τ n : ℂ) ∧
      Set.EqOn (fun z => modularLambda (cayleyInv (g z))) (Rseq n) (ball z₀ Rball) := by
    intro n
    exact omitting_lift_member_based hRball (Rseq n) (hdiff n) (homit n) (τ n) (hτeq n)
  choose g hgdiff hgbd hgbase hgeq using hlift
  have hgbase_bd : ∀ n, ‖g n z₀‖ ≤ s₀ := by
    intro n
    rw [hgbase n]
    exact hτbd n
  have hstereo_eq : ∀ n, Set.EqOn
      (fun z => stereo (modularLambda (cayleyInv (g n z))))
      (fun z => stereo (Rseq n z)) (ball z₀ Rball) := by
    intro n z hz
    exact congrArg stereo (hgeq n hz)
  exact no_deckNormalized_modularLift_crossRatio_of_frontier
    (gseq := g) hzfront hρ0 hρR hs₀ hU hαβ hβ hα hpreα hzβ hRcont hR
    hgdiff hgbd hgbase_bd hstereo_eq

/-- Compact-basepoint branch of the deck-normalized cross-ratio obstruction.

If the center values of the cross-ratio sequence remain in a compact subset of `ℂ∖{0,1}`, properness
of the modular quotient supplies compactly bounded `λ`-preimages, hence based normalized lifts. -/
theorem no_compactBasepoint_modularLift_crossRatio_of_frontier {c α β z₀ : ℂ}
    {ρ Rball : ℝ} {U : Set ℂ} {Rseq : ℕ → ℂ → ℂ} {K : Set Punctured}
    (hzfront : z₀ ∈ frontier (filledJulia c)) (hρ0 : 0 < ρ) (hρR : ρ < Rball / 2)
    (hU : closedBall z₀ ρ ⊆ U)
    (hαβ : α ≠ β)
    (hβ : ∀ n z, z ∈ U → (quadratic c)^[n] z ≠ β)
    (hα : ∀ z ∈ U, z ≠ α)
    (hpreα : ∀ n z, z ∈ U → (quadratic c)^[n] z ≠ α)
    (hzβ : ∀ z ∈ U, z ≠ β)
    (hRcont : ∀ n, ContinuousOn (Rseq n) (closedBall z₀ ρ))
    (hR : ∀ n, Set.EqOn (Rseq n)
      (fun z => ((quadratic c)^[n] z - α) * (z - β) /
        (((quadratic c)^[n] z - β) * (z - α))) U)
    (hdiff : ∀ n, DifferentiableOn ℂ (Rseq n) (ball z₀ Rball))
    (homit : ∀ n z, z ∈ ball z₀ Rball → Rseq n z ∈ ({0, 1} : Set ℂ)ᶜ)
    (hK : IsCompact K)
    (hbaseK : ∀ n,
      (⟨Rseq n z₀, homit n z₀ (mem_ball_self (by linarith : 0 < Rball))⟩ : Punctured) ∈ K) :
    False := by
  let a : ℕ → Punctured :=
    fun n => ⟨Rseq n z₀, homit n z₀ (mem_ball_self (by linarith : 0 < Rball))⟩
  have haK : ∀ n, a n ∈ K := hbaseK
  obtain ⟨s, hs, hτ⟩ := exists_uniform_cayley_bound_of_compact_values hK haK
  exact no_basedPreimage_modularLift_crossRatio_of_frontier hzfront hρ0 hρR hs hU hαβ
    hβ hα hpreα hzβ hRcont hR hdiff homit
    (fun n => by
      obtain ⟨τ, hτeq, hτbd⟩ := hτ n
      exact ⟨τ, by simpa [a] using hτeq, hτbd⟩)

end

end Bottcher

namespace Bottcher

noncomputable section

/-- Compact-basepoint branch with a separate strictly increasing iterate-depth sequence.  This is the
selector-compatible form: the normalized family is indexed by `k`, but its genuine cross-ratio depth is
`nseq k`. -/
theorem no_compactBasepoint_modularLift_crossRatio_of_frontier_subseq {c α β z₀ : ℂ}
    {ρ Rball : ℝ} {U : Set ℂ} {Rseq : ℕ → ℂ → ℂ} {K : Set Punctured}
    {nseq : ℕ → ℕ}
    (hzfront : z₀ ∈ frontier (filledJulia c)) (hρ0 : 0 < ρ) (hρR : ρ < Rball / 2)
    (hnseq : StrictMono nseq)
    (hU : closedBall z₀ ρ ⊆ U)
    (hαβ : α ≠ β)
    (hβ : ∀ n z, z ∈ U → (quadratic c)^[n] z ≠ β)
    (hα : ∀ z ∈ U, z ≠ α)
    (hpreα : ∀ n z, z ∈ U → (quadratic c)^[n] z ≠ α)
    (hzβ : ∀ z ∈ U, z ≠ β)
    (hR : ∀ k, Set.EqOn (Rseq k)
      (fun z => ((quadratic c)^[nseq k] z - α) * (z - β) /
        (((quadratic c)^[nseq k] z - β) * (z - α))) U)
    (hdiff : ∀ k, DifferentiableOn ℂ (Rseq k) (ball z₀ Rball))
    (homit : ∀ k z, z ∈ ball z₀ Rball → Rseq k z ∈ ({0, 1} : Set ℂ)ᶜ)
    (hK : IsCompact K)
    (hbaseK : ∀ k,
      (⟨Rseq k z₀, homit k z₀ (mem_ball_self (by linarith : 0 < Rball))⟩ : Punctured) ∈ K) :
    False := by
  let a : ℕ → Punctured :=
    fun k => ⟨Rseq k z₀, homit k z₀ (mem_ball_self (by linarith : 0 < Rball))⟩
  have haK : ∀ k, a k ∈ K := hbaseK
  obtain ⟨s, hs, hτ⟩ := exists_uniform_cayley_bound_of_compact_values hK haK
  choose τ hτeq hτbd using hτ
  have hRball : 0 < Rball := by linarith
  have hlift : ∀ k, ∃ g : ℂ → ℂ,
      DifferentiableOn ℂ g (ball z₀ Rball) ∧
      (∀ z ∈ ball z₀ Rball, ‖g z‖ ≤ 1) ∧
      g z₀ = cayley (τ k : ℂ) ∧
      Set.EqOn (fun z => modularLambda (cayleyInv (g z))) (Rseq k) (ball z₀ Rball) := by
    intro k
    exact omitting_lift_member_based hRball (Rseq k) (hdiff k) (homit k) (τ k)
      (by simpa [a] using hτeq k)
  choose g hgdiff hgbd hgbase hgeq using hlift
  have hgbase_bd : ∀ k, ‖g k z₀‖ ≤ s := by
    intro k
    rw [hgbase k]
    exact hτbd k
  have hstereo_eq : ∀ k, Set.EqOn
      (fun z => stereo (modularLambda (cayleyInv (g k z))))
      (fun z => stereo (Rseq k z)) (ball z₀ Rball) := by
    intro k z hz
    exact congrArg stereo (hgeq k hz)
  obtain ⟨φ, G, r, hφ, hr0, hrsub, hGcont, hconv⟩ :=
    spherical_normal_of_modularDiskTarget_basepoint_strict_lifts
      (Fseq := fun k z => stereo (Rseq k z)) hρ0 hρR hs hgdiff hgbd hgbase_bd hstereo_eq
  have hU_r : closedBall z₀ r ⊆ U := fun z hz => hU (hrsub hz)
  exact no_spherical_crossRatio_uniform_limit_of_frontier_subseq
    (R := Rseq) (nseq := nseq) hzfront hr0 hU_r hαβ hnseq hβ hα hpreα hzβ hR
    ⟨φ, G, hφ, hGcont, hconv⟩

end

end Bottcher
