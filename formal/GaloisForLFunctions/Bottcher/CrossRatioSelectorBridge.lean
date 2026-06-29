import GaloisForLFunctions.Bottcher.CrossRatioDeckNormalBridge
import GaloisForLFunctions.Bottcher.CrossRatioCuspBridge

open Complex Metric Set Filter Topology UpperHalfPlane
open scoped UpperHalfPlane

namespace Bottcher

noncomputable section

/-- Global punctured-basepoint obstruction for frontier cross-ratio families.

The base values `Rseq n z₀ ∈ ℂ ∖ {0,1}` are routed by the modular-lambda selector.  The compact
subsequence is discharged by deck-normalized compact representatives, and the six escaping
anharmonic cusp subsequences are discharged by the corresponding cusp bridge theorems. -/
theorem no_puncturedBasepoint_modularLift_crossRatio_of_frontier
    {c α β z₀ : ℂ} {ρ Rlift : ℝ} {U : Set ℂ} {Rseq : ℕ → ℂ → ℂ}
    (hzfront : z₀ ∈ frontier (filledJulia c)) (hρ0 : 0 < ρ) (hρR : ρ < Rlift / 2)
    (hU : closedBall z₀ ρ ⊆ U)
    (hαβ : α ≠ β)
    (hβ : ∀ n z, z ∈ U → (quadratic c)^[n] z ≠ β)
    (hα : ∀ z ∈ U, z ≠ α)
    (hpreα : ∀ n z, z ∈ U → (quadratic c)^[n] z ≠ α)
    (hzβ : ∀ z ∈ U, z ≠ β)
    (hR : ∀ n, Set.EqOn (Rseq n)
      (fun z => ((quadratic c)^[n] z - α) * (z - β) /
        (((quadratic c)^[n] z - β) * (z - α))) U)
    (hdiff : ∀ n, DifferentiableOn ℂ (Rseq n) (ball z₀ Rlift))
    (homit : ∀ n z, z ∈ ball z₀ Rlift → Rseq n z ∈ ({0, 1} : Set ℂ)ᶜ) : False := by
  have hRlift_pos : 0 < Rlift := by linarith
  have hρRlift : ρ < Rlift := by linarith
  let u : ℕ → Punctured := fun n =>
    ⟨Rseq n z₀, homit n z₀ (mem_ball_self hRlift_pos)⟩
  obtain ⟨ψ, hψ, hcases⟩ := lambdaPunct_subseq_compact_or_anharmonic_cusp u
  let Sseq : ℕ → ℂ → ℂ := fun k z => Rseq (ψ k) z
  have hS_R : ∀ k, Set.EqOn (Sseq k)
      (fun z => ((quadratic c)^[ψ k] z - α) * (z - β) /
        (((quadratic c)^[ψ k] z - β) * (z - α))) U := by
    intro k
    simpa [Sseq] using hR (ψ k)
  have hSdiff : ∀ k, DifferentiableOn ℂ (Sseq k) (ball z₀ Rlift) := by
    intro k
    simpa [Sseq] using hdiff (ψ k)
  have hSomit : ∀ k z, z ∈ ball z₀ Rlift → Sseq k z ∈ ({0, 1} : Set ℂ)ᶜ := by
    intro k z hz
    simpa [Sseq] using homit (ψ k) z hz
  rcases hcases with hcompact | hcusp
  · obtain ⟨K, hK, hbaseK⟩ := hcompact
    exact no_compactBasepoint_modularLift_crossRatio_of_frontier_subseq
      (Rseq := Sseq) (K := K) (nseq := ψ) hzfront hρ0 hρR hψ hU hαβ hβ hα
      hpreα hzβ hS_R hSdiff hSomit hK (by
        intro k
        simpa [u, Sseq] using hbaseK k)
  · obtain ⟨σseq, hbase, hcharts⟩ := hcusp
    rcases hcharts with hInf | hZero | hInfAdd | hZeroAdd | hOne | hRec
    · have hτ : ∀ k, modularLambda (σseq k : ℂ) = Sseq k z₀ := by
        intro k
        simpa [u, Sseq] using hInf k
      exact no_cuspInf_basedPreimage_schwarzPick_modularLift_crossRatio_of_frontier_subseq
        (Rseq := Sseq) (τseq := σseq) (nseq := ψ) hzfront hρ0 hRlift_pos hρRlift hψ
        hU hαβ hβ hα hpreα hzβ hS_R hSdiff hSomit hτ hbase
    · have hτ : ∀ k, modularLambda (-1 / (σseq k : ℂ)) = Sseq k z₀ := by
        intro k
        simpa [u, Sseq] using hZero k
      exact no_cuspZero_basedPreimage_schwarzPick_modularLift_crossRatio_of_frontier_subseq
        (Rseq := Sseq) (σseq := σseq) (nseq := ψ) hzfront hρ0 hRlift_pos hρRlift hψ
        hU hαβ hβ hα hpreα hzβ hS_R hSdiff hSomit hτ hbase
    · have hτ : ∀ k, modularLambda ((σseq k : ℂ) + 1) = Sseq k z₀ := by
        intro k
        simpa [u, Sseq] using hInfAdd k
      exact no_cuspInf_addOne_basedPreimage_schwarzPick_modularLift_crossRatio_of_frontier_subseq
        (Rseq := Sseq) (σseq := σseq) (nseq := ψ) hzfront hρ0 hRlift_pos hρRlift hψ
        hU hαβ hβ hα hpreα hzβ hS_R hSdiff hSomit hτ hbase
    · have hτ : ∀ k, modularLambda (-1 / ((σseq k : ℂ) + 1)) = Sseq k z₀ := by
        intro k
        simpa [u, Sseq] using hZeroAdd k
      exact no_cuspZero_addOne_basedPreimage_schwarzPick_modularLift_crossRatio_of_frontier_subseq
        (Rseq := Sseq) (σseq := σseq) (nseq := ψ) hzfront hρ0 hRlift_pos hρRlift hψ
        hU hαβ hβ hα hpreα hzβ hS_R hSdiff hSomit hτ hbase
    · have hτ : ∀ k, modularLambda (1 - 1 / (σseq k : ℂ)) = Sseq k z₀ := by
        intro k
        simpa [u, Sseq] using hOne k
      exact no_cuspOne_basedPreimage_schwarzPick_modularLift_crossRatio_of_frontier_subseq
        (Rseq := Sseq) (σseq := σseq) (nseq := ψ) hzfront hρ0 hRlift_pos hρRlift hψ
        hU hαβ hβ hα hpreα hzβ hS_R hSdiff hSomit hτ hbase
    · have hτ : ∀ k, (modularLambda (σseq k : ℂ))⁻¹ = Sseq k z₀ := by
        intro k
        simpa [u, Sseq] using hRec k
      exact no_cuspOne_reciprocal_basedPreimage_schwarzPick_modularLift_crossRatio_of_frontier_subseq
        (Rseq := Sseq) (σseq := σseq) (nseq := ψ) hzfront hρ0 hRlift_pos hρRlift hψ
        hU hαβ hβ hα hpreα hzβ hS_R hSdiff hSomit hτ hbase

/-- Punctured-basepoint obstruction with a separate positive iterate-depth sequence.  This is the
selector form needed when the cross-ratio family is indexed by `k`, but the dynamical depth is
`nseq k` rather than `k`. -/
theorem no_puncturedBasepoint_modularLift_crossRatio_of_frontier_subseqDepth
    {c α β z₀ : ℂ} {ρ Rlift : ℝ} {U : Set ℂ} {Rseq : ℕ → ℂ → ℂ}
    {nseq : ℕ → ℕ}
    (hzfront : z₀ ∈ frontier (filledJulia c)) (hρ0 : 0 < ρ) (hρR : ρ < Rlift / 2)
    (hnseq : StrictMono nseq)
    (hU : closedBall z₀ ρ ⊆ U)
    (hαβ : α ≠ β)
    (hβ : ∀ n z, z ∈ U → (quadratic c)^[n] z ≠ β)
    (hα : ∀ z ∈ U, z ≠ α)
    (hpreα : ∀ n z, z ∈ U → (quadratic c)^[n] z ≠ α)
    (hzβ : ∀ z ∈ U, z ≠ β)
    (hR : ∀ n, Set.EqOn (Rseq n)
      (fun z => ((quadratic c)^[nseq n] z - α) * (z - β) /
        (((quadratic c)^[nseq n] z - β) * (z - α))) U)
    (hdiff : ∀ n, DifferentiableOn ℂ (Rseq n) (ball z₀ Rlift))
    (homit : ∀ n z, z ∈ ball z₀ Rlift → Rseq n z ∈ ({0, 1} : Set ℂ)ᶜ) : False := by
  have hRlift_pos : 0 < Rlift := by linarith
  have hρRlift : ρ < Rlift := by linarith
  let u : ℕ → Punctured := fun n =>
    ⟨Rseq n z₀, homit n z₀ (mem_ball_self hRlift_pos)⟩
  obtain ⟨ψ, hψ, hcases⟩ := lambdaPunct_subseq_compact_or_anharmonic_cusp u
  let Sseq : ℕ → ℂ → ℂ := fun k z => Rseq (ψ k) z
  let mseq : ℕ → ℕ := fun k => nseq (ψ k)
  have hmseq : StrictMono mseq := hnseq.comp hψ
  have hS_R : ∀ k, Set.EqOn (Sseq k)
      (fun z => ((quadratic c)^[mseq k] z - α) * (z - β) /
        (((quadratic c)^[mseq k] z - β) * (z - α))) U := by
    intro k
    simpa [Sseq, mseq] using hR (ψ k)
  have hSdiff : ∀ k, DifferentiableOn ℂ (Sseq k) (ball z₀ Rlift) := by
    intro k
    simpa [Sseq] using hdiff (ψ k)
  have hSomit : ∀ k z, z ∈ ball z₀ Rlift → Sseq k z ∈ ({0, 1} : Set ℂ)ᶜ := by
    intro k z hz
    simpa [Sseq] using homit (ψ k) z hz
  rcases hcases with hcompact | hcusp
  · obtain ⟨K, hK, hbaseK⟩ := hcompact
    exact no_compactBasepoint_modularLift_crossRatio_of_frontier_subseq
      (Rseq := Sseq) (K := K) (nseq := mseq) hzfront hρ0 hρR hmseq hU hαβ
      hβ hα hpreα hzβ hS_R hSdiff hSomit hK (by
        intro k
        simpa [u, Sseq] using hbaseK k)
  · obtain ⟨σseq, hbase, hcharts⟩ := hcusp
    rcases hcharts with hInf | hZero | hInfAdd | hZeroAdd | hOne | hRec
    · have hτ : ∀ k, modularLambda (σseq k : ℂ) = Sseq k z₀ := by
        intro k
        simpa [u, Sseq] using hInf k
      exact no_cuspInf_basedPreimage_schwarzPick_modularLift_crossRatio_of_frontier_subseq
        (Rseq := Sseq) (τseq := σseq) (nseq := mseq) hzfront hρ0 hRlift_pos
        hρRlift hmseq hU hαβ hβ hα hpreα hzβ hS_R hSdiff hSomit hτ hbase
    · have hτ : ∀ k, modularLambda (-1 / (σseq k : ℂ)) = Sseq k z₀ := by
        intro k
        simpa [u, Sseq] using hZero k
      exact no_cuspZero_basedPreimage_schwarzPick_modularLift_crossRatio_of_frontier_subseq
        (Rseq := Sseq) (σseq := σseq) (nseq := mseq) hzfront hρ0 hRlift_pos
        hρRlift hmseq hU hαβ hβ hα hpreα hzβ hS_R hSdiff hSomit hτ hbase
    · have hτ : ∀ k, modularLambda ((σseq k : ℂ) + 1) = Sseq k z₀ := by
        intro k
        simpa [u, Sseq] using hInfAdd k
      exact no_cuspInf_addOne_basedPreimage_schwarzPick_modularLift_crossRatio_of_frontier_subseq
        (Rseq := Sseq) (σseq := σseq) (nseq := mseq) hzfront hρ0 hRlift_pos
        hρRlift hmseq hU hαβ hβ hα hpreα hzβ hS_R hSdiff hSomit hτ hbase
    · have hτ : ∀ k, modularLambda (-1 / ((σseq k : ℂ) + 1)) = Sseq k z₀ := by
        intro k
        simpa [u, Sseq] using hZeroAdd k
      exact no_cuspZero_addOne_basedPreimage_schwarzPick_modularLift_crossRatio_of_frontier_subseq
        (Rseq := Sseq) (σseq := σseq) (nseq := mseq) hzfront hρ0 hRlift_pos
        hρRlift hmseq hU hαβ hβ hα hpreα hzβ hS_R hSdiff hSomit hτ hbase
    · have hτ : ∀ k, modularLambda (1 - 1 / (σseq k : ℂ)) = Sseq k z₀ := by
        intro k
        simpa [u, Sseq] using hOne k
      exact no_cuspOne_basedPreimage_schwarzPick_modularLift_crossRatio_of_frontier_subseq
        (Rseq := Sseq) (σseq := σseq) (nseq := mseq) hzfront hρ0 hRlift_pos
        hρRlift hmseq hU hαβ hβ hα hpreα hzβ hS_R hSdiff hSomit hτ hbase
    · have hτ : ∀ k, (modularLambda (σseq k : ℂ))⁻¹ = Sseq k z₀ := by
        intro k
        simpa [u, Sseq] using hRec k
      exact no_cuspOne_reciprocal_basedPreimage_schwarzPick_modularLift_crossRatio_of_frontier_subseq
        (Rseq := Sseq) (σseq := σseq) (nseq := mseq) hzfront hρ0 hRlift_pos
        hρRlift hmseq hU hαβ hβ hα hpreα hzβ hS_R hSdiff hSomit hτ hbase

end

end Bottcher
namespace Bottcher

noncomputable section

theorem no_periodic_free_crossRatio_modularSelector_of_frontier
    {c α β z₀ : ℂ} {ρ Rlift : ℝ}
    (hzfront : z₀ ∈ frontier (filledJulia c)) (hρ0 : 0 < ρ) (hρR : ρ < Rlift / 2)
    (hαβ : α ≠ β)
    (hβ : ∀ n z, z ∈ ball z₀ Rlift → (quadratic c)^[n] z ≠ β)
    (hα : ∀ z ∈ ball z₀ Rlift, z ≠ α)
    (hpreα : ∀ n z, z ∈ ball z₀ Rlift → (quadratic c)^[n] z ≠ α)
    (hzβ : ∀ z ∈ ball z₀ Rlift, z ≠ β)
    (hnper : ∀ n z, z ∈ ball z₀ Rlift → (quadratic c)^[n] z ≠ z) : False := by
  let Rseq : ℕ → ℂ → ℂ := fun n z => ((quadratic c)^[n] z - α) * (z - β) /
    (((quadratic c)^[n] z - β) * (z - α))
  have hRlift_pos : 0 < Rlift := by linarith
  have hρRlift : ρ < Rlift := by linarith
  have hU : closedBall z₀ ρ ⊆ ball z₀ Rlift := closedBall_subset_ball hρRlift
  have hR : ∀ n, Set.EqOn (Rseq n)
      (fun z => ((quadratic c)^[n] z - α) * (z - β) /
        (((quadratic c)^[n] z - β) * (z - α))) (ball z₀ Rlift) := by
    intro n z hz
    rfl
  have hdiff : ∀ n, DifferentiableOn ℂ (Rseq n) (ball z₀ Rlift) := by
    intro n
    exact differentiableOn_crossRatio_iterate (hβ n) hα
  have homit : ∀ n z, z ∈ ball z₀ Rlift → Rseq n z ∈ ({0, 1} : Set ℂ)ᶜ := by
    intro n
    exact crossRatio_iterate_omits_zero_one_on hαβ (hβ n) hα (hpreα n) hzβ (hnper n)
  exact no_puncturedBasepoint_modularLift_crossRatio_of_frontier
    (U := ball z₀ Rlift) (Rseq := Rseq) hzfront hρ0 hρR hU hαβ hβ hα hpreα hzβ
    hR hdiff homit

/-- Positive-period version of the frontier cross-ratio obstruction.

The older selector theorem is indexed by all `n : ℕ`, which includes the trivial depth `0`.  This
version uses the depth sequence `n + 1`, so the periodic-free hypothesis only excludes genuine
positive periods. -/
theorem no_positive_periodic_free_crossRatio_modularSelector_of_frontier
    {c α β z₀ : ℂ} {ρ Rlift : ℝ}
    (hzfront : z₀ ∈ frontier (filledJulia c)) (hρ0 : 0 < ρ) (hρR : ρ < Rlift / 2)
    (hαβ : α ≠ β)
    (hβ : ∀ n z, 1 ≤ n → z ∈ ball z₀ Rlift → (quadratic c)^[n] z ≠ β)
    (hα : ∀ z ∈ ball z₀ Rlift, z ≠ α)
    (hpreα : ∀ n z, 1 ≤ n → z ∈ ball z₀ Rlift → (quadratic c)^[n] z ≠ α)
    (hzβ : ∀ z ∈ ball z₀ Rlift, z ≠ β)
    (hnper : ∀ n z, 1 ≤ n → z ∈ ball z₀ Rlift → (quadratic c)^[n] z ≠ z) :
    False := by
  let nseq : ℕ → ℕ := fun n => n + 1
  let Rseq : ℕ → ℂ → ℂ := fun n z => ((quadratic c)^[nseq n] z - α) * (z - β) /
    (((quadratic c)^[nseq n] z - β) * (z - α))
  have hnseq : StrictMono nseq := by
    intro a b hab
    dsimp [nseq]
    omega
  have hnseq_pos : ∀ n, 1 ≤ nseq n := by
    intro n
    dsimp [nseq]
    omega
  have hβall : ∀ n z, z ∈ ball z₀ Rlift → (quadratic c)^[n] z ≠ β := by
    intro n z hz
    cases n with
    | zero =>
        simpa using hzβ z hz
    | succ n =>
        exact hβ (n + 1) z (by omega) hz
  have hpreαall : ∀ n z, z ∈ ball z₀ Rlift → (quadratic c)^[n] z ≠ α := by
    intro n z hz
    cases n with
    | zero =>
        simpa using hα z hz
    | succ n =>
        exact hpreα (n + 1) z (by omega) hz
  have hR : ∀ n, Set.EqOn (Rseq n)
      (fun z => ((quadratic c)^[nseq n] z - α) * (z - β) /
        (((quadratic c)^[nseq n] z - β) * (z - α))) (ball z₀ Rlift) := by
    intro n z hz
    rfl
  have hdiff : ∀ n, DifferentiableOn ℂ (Rseq n) (ball z₀ Rlift) := by
    intro n
    exact differentiableOn_crossRatio_iterate
      (fun z hz => hβ (nseq n) z (hnseq_pos n) hz) hα
  have homit : ∀ n z, z ∈ ball z₀ Rlift → Rseq n z ∈ ({0, 1} : Set ℂ)ᶜ := by
    intro n
    exact crossRatio_iterate_omits_zero_one_on hαβ
      (fun z hz => hβ (nseq n) z (hnseq_pos n) hz) hα
      (fun z hz => hpreα (nseq n) z (hnseq_pos n) hz) hzβ
      (fun z hz => hnper (nseq n) z (hnseq_pos n) hz)
  exact no_puncturedBasepoint_modularLift_crossRatio_of_frontier_subseqDepth
    (U := ball z₀ Rlift) (Rseq := Rseq) (nseq := nseq) hzfront hρ0 hρR hnseq
    (closedBall_subset_ball (by linarith : ρ < Rlift)) hαβ hβall hα hpreαall hzβ
    hR hdiff homit

end

end Bottcher
namespace Bottcher

noncomputable section

theorem exists_periodic_point_in_ball_of_crossRatio_avoidance_frontier
    {c α β z₀ : ℂ} {ρ Rlift : ℝ}
    (hzfront : z₀ ∈ frontier (filledJulia c)) (hρ0 : 0 < ρ) (hρR : ρ < Rlift / 2)
    (hαβ : α ≠ β)
    (hβ : ∀ n z, z ∈ ball z₀ Rlift → (quadratic c)^[n] z ≠ β)
    (hα : ∀ z ∈ ball z₀ Rlift, z ≠ α)
    (hpreα : ∀ n z, z ∈ ball z₀ Rlift → (quadratic c)^[n] z ≠ α)
    (hzβ : ∀ z ∈ ball z₀ Rlift, z ≠ β) :
    ∃ n z, z ∈ ball z₀ Rlift ∧ (quadratic c)^[n] z = z := by
  by_contra hnone
  have hnper : ∀ n z, z ∈ ball z₀ Rlift → (quadratic c)^[n] z ≠ z := by
    intro n z hz hper
    exact hnone ⟨n, z, hz, hper⟩
  exact no_periodic_free_crossRatio_modularSelector_of_frontier
    hzfront hρ0 hρR hαβ hβ hα hpreα hzβ hnper

/-- A positive-period-free frontier ball cannot omit two distinct fixed values under all positive
forward iterates. -/
theorem positive_periodic_free_frontier_ball_forward_orbit_hits_one_of_two_fixed_values
    {c α β z₀ : ℂ} {ρ Rlift : ℝ}
    (hzfront : z₀ ∈ frontier (filledJulia c)) (hρ0 : 0 < ρ) (hρR : ρ < Rlift / 2)
    (hαfix : quadratic c α = α) (hβfix : quadratic c β = β) (hαβ : α ≠ β)
    (hnper : ∀ n z, 1 ≤ n → z ∈ ball z₀ Rlift → (quadratic c)^[n] z ≠ z) :
    (∃ n z, 1 ≤ n ∧ z ∈ ball z₀ Rlift ∧ (quadratic c)^[n] z = α) ∨
      (∃ n z, 1 ≤ n ∧ z ∈ ball z₀ Rlift ∧ (quadratic c)^[n] z = β) := by
  by_cases hαhit : ∃ n z, 1 ≤ n ∧ z ∈ ball z₀ Rlift ∧ (quadratic c)^[n] z = α
  · exact Or.inl hαhit
  by_cases hβhit : ∃ n z, 1 ≤ n ∧ z ∈ ball z₀ Rlift ∧ (quadratic c)^[n] z = β
  · exact Or.inr hβhit
  have hβmiss : ∀ n z, 1 ≤ n → z ∈ ball z₀ Rlift → (quadratic c)^[n] z ≠ β := by
    intro n z hn hz hval
    exact hβhit ⟨n, z, hn, hz, hval⟩
  have hαmiss : ∀ n z, 1 ≤ n → z ∈ ball z₀ Rlift → (quadratic c)^[n] z ≠ α := by
    intro n z hn hz hval
    exact hαhit ⟨n, z, hn, hz, hval⟩
  have hα : ∀ z ∈ ball z₀ Rlift, z ≠ α := by
    intro z hz hzα
    have hper : (quadratic c)^[1] z = z := by
      rw [hzα]
      simpa using hαfix
    exact hnper 1 z (by norm_num) hz hper
  have hzβ : ∀ z ∈ ball z₀ Rlift, z ≠ β := by
    intro z hz hzβeq
    have hper : (quadratic c)^[1] z = z := by
      rw [hzβeq]
      simpa using hβfix
    exact hnper 1 z (by norm_num) hz hper
  exact False.elim (no_positive_periodic_free_crossRatio_modularSelector_of_frontier
    hzfront hρ0 hρR hαβ hβmiss hα hαmiss hzβ hnper)

/-- A positive-period-free frontier ball cannot omit two distinct off-ball target values under all
positive forward iterates.  Unlike the set-level blowing-up theorem below, this statement has no
depth-`0` escape hatch: the targets are explicitly outside the source ball, and the depth is
positive. -/
theorem positive_periodic_free_frontier_ball_forward_orbit_hits_one_of_two_values_off_ball
    {c α β z₀ : ℂ} {ρ Rlift : ℝ}
    (hzfront : z₀ ∈ frontier (filledJulia c)) (hρ0 : 0 < ρ) (hρR : ρ < Rlift / 2)
    (hαβ : α ≠ β)
    (hα : ∀ z ∈ ball z₀ Rlift, z ≠ α)
    (hβ : ∀ z ∈ ball z₀ Rlift, z ≠ β)
    (hnper : ∀ n z, 1 ≤ n → z ∈ ball z₀ Rlift → (quadratic c)^[n] z ≠ z) :
    (∃ n z, 1 ≤ n ∧ z ∈ ball z₀ Rlift ∧ (quadratic c)^[n] z = α) ∨
      (∃ n z, 1 ≤ n ∧ z ∈ ball z₀ Rlift ∧ (quadratic c)^[n] z = β) := by
  by_cases hαhit : ∃ n z, 1 ≤ n ∧ z ∈ ball z₀ Rlift ∧ (quadratic c)^[n] z = α
  · exact Or.inl hαhit
  by_cases hβhit : ∃ n z, 1 ≤ n ∧ z ∈ ball z₀ Rlift ∧ (quadratic c)^[n] z = β
  · exact Or.inr hβhit
  have hαmiss : ∀ n z, 1 ≤ n → z ∈ ball z₀ Rlift → (quadratic c)^[n] z ≠ α := by
    intro n z hn hz hval
    exact hαhit ⟨n, z, hn, hz, hval⟩
  have hβmiss : ∀ n z, 1 ≤ n → z ∈ ball z₀ Rlift → (quadratic c)^[n] z ≠ β := by
    intro n z hn hz hval
    exact hβhit ⟨n, z, hn, hz, hval⟩
  exact False.elim (no_positive_periodic_free_crossRatio_modularSelector_of_frontier
    hzfront hρ0 hρR hαβ hβmiss hα hαmiss hβ hnper)

/-- Positive-period dichotomy with two fixed anchors: every frontier ball either contains a positive
periodic point or a positive forward orbit hits one of the two anchors. -/
theorem frontier_ball_positive_periodic_or_forward_hit_fixed_pair
    {c α β z₀ : ℂ} {ρ Rlift : ℝ}
    (hzfront : z₀ ∈ frontier (filledJulia c)) (hρ0 : 0 < ρ) (hρR : ρ < Rlift / 2)
    (hαfix : quadratic c α = α) (hβfix : quadratic c β = β) (hαβ : α ≠ β) :
    (∃ n z, 1 ≤ n ∧ z ∈ ball z₀ Rlift ∧ (quadratic c)^[n] z = z) ∨
      (∃ n z, 1 ≤ n ∧ z ∈ ball z₀ Rlift ∧
        ((quadratic c)^[n] z = α ∨ (quadratic c)^[n] z = β)) := by
  by_cases hper : ∃ n z, 1 ≤ n ∧ z ∈ ball z₀ Rlift ∧ (quadratic c)^[n] z = z
  · exact Or.inl hper
  · have hnper : ∀ n z, 1 ≤ n → z ∈ ball z₀ Rlift → (quadratic c)^[n] z ≠ z := by
      intro n z hn hz hfix
      exact hper ⟨n, z, hn, hz, hfix⟩
    have hhit := positive_periodic_free_frontier_ball_forward_orbit_hits_one_of_two_fixed_values
      hzfront hρ0 hρR hαfix hβfix hαβ hnper
    rcases hhit with hαhit | hβhit
    · obtain ⟨n, z, hn, hz, hval⟩ := hαhit
      exact Or.inr ⟨n, z, hn, hz, Or.inl hval⟩
    · obtain ⟨n, z, hn, hz, hval⟩ := hβhit
      exact Or.inr ⟨n, z, hn, hz, Or.inr hval⟩

/-- Positive-period dichotomy with two off-ball target values.  This is the selector output needed
for near-return constructions: if the frontier ball has no genuine periodic point, some positive
iterate from the ball hits one of the prescribed off-ball values. -/
theorem frontier_ball_positive_periodic_or_forward_hit_value_pair_off_ball
    {c α β z₀ : ℂ} {ρ Rlift : ℝ}
    (hzfront : z₀ ∈ frontier (filledJulia c)) (hρ0 : 0 < ρ) (hρR : ρ < Rlift / 2)
    (hαβ : α ≠ β)
    (hα : ∀ z ∈ ball z₀ Rlift, z ≠ α)
    (hβ : ∀ z ∈ ball z₀ Rlift, z ≠ β) :
    (∃ n z, 1 ≤ n ∧ z ∈ ball z₀ Rlift ∧ (quadratic c)^[n] z = z) ∨
      (∃ n z, 1 ≤ n ∧ z ∈ ball z₀ Rlift ∧
        ((quadratic c)^[n] z = α ∨ (quadratic c)^[n] z = β)) := by
  by_cases hper : ∃ n z, 1 ≤ n ∧ z ∈ ball z₀ Rlift ∧ (quadratic c)^[n] z = z
  · exact Or.inl hper
  · have hnper : ∀ n z, 1 ≤ n → z ∈ ball z₀ Rlift → (quadratic c)^[n] z ≠ z := by
      intro n z hn hz hfix
      exact hper ⟨n, z, hn, hz, hfix⟩
    have hhit := positive_periodic_free_frontier_ball_forward_orbit_hits_one_of_two_values_off_ball
      hzfront hρ0 hρR hαβ hα hβ hnper
    rcases hhit with hαhit | hβhit
    · obtain ⟨n, z, hn, hz, hval⟩ := hαhit
      exact Or.inr ⟨n, z, hn, hz, Or.inl hval⟩
    · obtain ⟨n, z, hn, hz, hval⟩ := hβhit
      exact Or.inr ⟨n, z, hn, hz, Or.inr hval⟩

/-- Choose the two fixed anchors once for `c ≠ 1/4`.  Every frontier ball then either contains a
genuine positive-periodic point or has a positive forward hit to one of those two fixed anchors. -/
theorem exists_fixed_pair_frontier_ball_positive_periodic_or_forward_hit
    {c : ℂ} (hc : c ≠ 1 / 4) :
    ∃ α β : ℂ,
      quadratic c α = α ∧ quadratic c β = β ∧ α ≠ β ∧
        ∀ {z₀ : ℂ} {ρ Rlift : ℝ},
          z₀ ∈ frontier (filledJulia c) → 0 < ρ → ρ < Rlift / 2 →
            (∃ n z, 1 ≤ n ∧ z ∈ ball z₀ Rlift ∧ (quadratic c)^[n] z = z) ∨
              (∃ n z, 1 ≤ n ∧ z ∈ ball z₀ Rlift ∧
                ((quadratic c)^[n] z = α ∨ (quadratic c)^[n] z = β)) := by
  obtain ⟨α, β, hαfix, hβfix, hαβ⟩ := exists_two_distinct_fixed_points c hc
  refine ⟨α, β, hαfix, hβfix, hαβ, ?_⟩
  intro z₀ ρ Rlift hzfront hρ0 hρR
  exact frontier_ball_positive_periodic_or_forward_hit_fixed_pair
    hzfront hρ0 hρR hαfix hβfix hαβ

/-- If every positive forward hit to either fixed anchor can be converted into a positive periodic
point in the same frontier ball, then positive periodic points are locally dense in the frontier. -/
theorem forall_frontier_ball_positive_periodic_of_forward_hit_fixed_pair_to_positive_periodic
    {c α β : ℂ}
    (hαfix : quadratic c α = α) (hβfix : quadratic c β = β) (hαβ : α ≠ β)
    (hhit : ∀ {z₀ : ℂ} {ρ Rlift : ℝ},
      z₀ ∈ frontier (filledJulia c) → 0 < ρ → ρ < Rlift / 2 →
      ∀ n z, 1 ≤ n → z ∈ ball z₀ Rlift →
        ((quadratic c)^[n] z = α ∨ (quadratic c)^[n] z = β) →
        ∃ y ∈ ball z₀ Rlift, ∃ q : ℕ, 1 ≤ q ∧ (quadratic c)^[q] y = y) :
    ∀ z₀ ∈ frontier (filledJulia c), ∀ R : ℝ, 0 < R →
      ∃ y ∈ ball z₀ R, ∃ q : ℕ, 1 ≤ q ∧ (quadratic c)^[q] y = y := by
  intro z₀ hzfront R hR
  have hρ0 : 0 < R / 4 := by linarith
  have hρR : R / 4 < R / 2 := by linarith
  have hsel := frontier_ball_positive_periodic_or_forward_hit_fixed_pair
    (c := c) (α := α) (β := β) (z₀ := z₀) (ρ := R / 4) (Rlift := R)
    hzfront hρ0 hρR hαfix hβfix hαβ
  rcases hsel with hper | hhitcase
  · obtain ⟨n, z, hn, hz, hfix⟩ := hper
    exact ⟨z, hz, n, hn, hfix⟩
  · obtain ⟨n, z, hn, hz, hval⟩ := hhitcase
    exact hhit hzfront hρ0 hρR n z hn hz hval

/-- Margin version of
`forall_frontier_ball_positive_periodic_of_forward_hit_fixed_pair_to_positive_periodic`.
The selector is run on the half-radius ball, so a later Newton construction centered at the forward
hit has room to stay inside the original target ball. -/
theorem forall_frontier_ball_positive_periodic_of_forward_hit_fixed_pair_to_positive_periodic_half
    {c α β : ℂ}
    (hαfix : quadratic c α = α) (hβfix : quadratic c β = β) (hαβ : α ≠ β)
    (hhit : ∀ {z₀ : ℂ} {ρ R : ℝ},
      z₀ ∈ frontier (filledJulia c) → 0 < ρ → ρ < (R / 2) / 2 →
      ∀ n z, 1 ≤ n → z ∈ ball z₀ (R / 2) →
        ((quadratic c)^[n] z = α ∨ (quadratic c)^[n] z = β) →
        ∃ y ∈ ball z₀ R, ∃ q : ℕ, 1 ≤ q ∧ (quadratic c)^[q] y = y) :
    ∀ z₀ ∈ frontier (filledJulia c), ∀ R : ℝ, 0 < R →
      ∃ y ∈ ball z₀ R, ∃ q : ℕ, 1 ≤ q ∧ (quadratic c)^[q] y = y := by
  intro z₀ hzfront R hR
  have hρ0 : 0 < R / 8 := by linarith
  have hρR : R / 8 < (R / 2) / 2 := by linarith
  have hsel := frontier_ball_positive_periodic_or_forward_hit_fixed_pair
    (c := c) (α := α) (β := β) (z₀ := z₀) (ρ := R / 8) (Rlift := R / 2)
    hzfront hρ0 hρR hαfix hβfix hαβ
  rcases hsel with hper | hhitcase
  · obtain ⟨n, z, hn, hz, hfix⟩ := hper
    have hzR : z ∈ ball z₀ R := by
      rw [Metric.mem_ball] at hz ⊢
      linarith
    exact ⟨z, hzR, n, hn, hfix⟩
  · obtain ⟨n, z, hn, hz, hval⟩ := hhitcase
    exact hhit hzfront hρ0 hρR n z hn hz hval

end

end Bottcher

namespace Bottcher

noncomputable section

/-- A periodic-free frontier ball cannot omit two distinct values under all forward iterates.

Equivalently, if two complex values are distinct, then a frontier ball with no periodic point must
have some forward iterate hitting at least one of them.  This is the selector/Montel obstruction in
forward-orbit form, with depth `0` handling values already inside the ball. -/
theorem periodic_free_frontier_ball_forward_orbit_hits_one_of_two_values
    {c α β z₀ : ℂ} {ρ Rlift : ℝ}
    (hzfront : z₀ ∈ frontier (filledJulia c)) (hρ0 : 0 < ρ) (hρR : ρ < Rlift / 2)
    (hαβ : α ≠ β)
    (hnper : ∀ n z, z ∈ ball z₀ Rlift → (quadratic c)^[n] z ≠ z) :
    (∃ n z, z ∈ ball z₀ Rlift ∧ (quadratic c)^[n] z = α) ∨
      (∃ n z, z ∈ ball z₀ Rlift ∧ (quadratic c)^[n] z = β) := by
  by_cases hαhit : ∃ n z, z ∈ ball z₀ Rlift ∧ (quadratic c)^[n] z = α
  · exact Or.inl hαhit
  by_cases hβhit : ∃ n z, z ∈ ball z₀ Rlift ∧ (quadratic c)^[n] z = β
  · exact Or.inr hβhit
  have hβ : ∀ n z, z ∈ ball z₀ Rlift → (quadratic c)^[n] z ≠ β := by
    intro n z hz hval
    exact hβhit ⟨n, z, hz, hval⟩
  have hα : ∀ z ∈ ball z₀ Rlift, z ≠ α := by
    intro z hz hzα
    exact hαhit ⟨0, z, hz, by simp [hzα]⟩
  have hpreα : ∀ n z, z ∈ ball z₀ Rlift → (quadratic c)^[n] z ≠ α := by
    intro n z hz hval
    exact hαhit ⟨n, z, hz, hval⟩
  have hzβ : ∀ z ∈ ball z₀ Rlift, z ≠ β := by
    intro z hz hzβeq
    exact hβhit ⟨0, z, hz, by simp [hzβeq]⟩
  exact False.elim (no_periodic_free_crossRatio_modularSelector_of_frontier
    hzfront hρ0 hρR hαβ hβ hα hpreα hzβ hnper)

end

end Bottcher

namespace Bottcher

noncomputable section

/-- In a periodic-free frontier ball, the set of values omitted by every forward image of the ball has
at most one element. -/
theorem periodic_free_frontier_ball_forward_orbit_omitted_values_subsingleton
    {c z₀ : ℂ} {ρ Rlift : ℝ}
    (hzfront : z₀ ∈ frontier (filledJulia c)) (hρ0 : 0 < ρ) (hρR : ρ < Rlift / 2)
    (hnper : ∀ n z, z ∈ ball z₀ Rlift → (quadratic c)^[n] z ≠ z) :
    ∀ α β : ℂ,
      (∀ n z, z ∈ ball z₀ Rlift → (quadratic c)^[n] z ≠ α) →
      (∀ n z, z ∈ ball z₀ Rlift → (quadratic c)^[n] z ≠ β) →
      α = β := by
  intro α β hαmiss hβmiss
  by_contra hne
  have hhit := periodic_free_frontier_ball_forward_orbit_hits_one_of_two_values
    hzfront hρ0 hρR hne hnper
  rcases hhit with hαhit | hβhit
  · obtain ⟨n, z, hz, hval⟩ := hαhit
    exact hαmiss n z hz hval
  · obtain ⟨n, z, hz, hval⟩ := hβhit
    exact hβmiss n z hz hval

/-- Set-level blowing-up form of the selector obstruction: if a frontier ball contains no periodic
point, then the complement of the union of all forward images of that ball is subsingleton. -/
theorem periodic_free_frontier_ball_forward_image_compl_subsingleton
    {c z₀ : ℂ} {ρ Rlift : ℝ}
    (hzfront : z₀ ∈ frontier (filledJulia c)) (hρ0 : 0 < ρ) (hρR : ρ < Rlift / 2)
    (hnper : ∀ n z, z ∈ ball z₀ Rlift → (quadratic c)^[n] z ≠ z) :
    Set.Subsingleton
      ((⋃ n : ℕ, ((fun z => (quadratic c)^[n] z) '' ball z₀ Rlift))ᶜ) := by
  intro α hα β hβ
  exact periodic_free_frontier_ball_forward_orbit_omitted_values_subsingleton
    hzfront hρ0 hρR hnper α β
    (by
      intro n z hz hval
      exact hα (by
        refine Set.mem_iUnion.mpr ⟨n, ?_⟩
        exact ⟨z, hz, hval⟩))
    (by
      intro n z hz hval
      exact hβ (by
        refine Set.mem_iUnion.mpr ⟨n, ?_⟩
        exact ⟨z, hz, hval⟩))

/-- Dichotomy form of the selector obstruction.  Every frontier ball either already contains a
periodic point or its forward images cover all but at most one complex value. -/
theorem frontier_ball_periodic_or_forward_image_compl_subsingleton
    {c z₀ : ℂ} {ρ Rlift : ℝ}
    (hzfront : z₀ ∈ frontier (filledJulia c)) (hρ0 : 0 < ρ) (hρR : ρ < Rlift / 2) :
    (∃ n z, z ∈ ball z₀ Rlift ∧ (quadratic c)^[n] z = z) ∨
      Set.Subsingleton
        ((⋃ n : ℕ, ((fun z => (quadratic c)^[n] z) '' ball z₀ Rlift))ᶜ) := by
  by_cases hper : ∃ n z, z ∈ ball z₀ Rlift ∧ (quadratic c)^[n] z = z
  · exact Or.inl hper
  · refine Or.inr (periodic_free_frontier_ball_forward_image_compl_subsingleton
      hzfront hρ0 hρR ?_)
    intro n z hz hfix
    exact hper ⟨n, z, hz, hfix⟩

/-- If a set has subsingleton complement, it intersects every non-subsingleton target set. -/
theorem exists_mem_of_compl_subsingleton_of_not_subsingleton {S T : Set ℂ}
    (hcompl : Set.Subsingleton Sᶜ) (hT : ¬ Set.Subsingleton T) :
    ∃ w, w ∈ T ∧ w ∈ S := by
  by_contra hhit
  have hmiss : ∀ w, w ∈ T → w ∈ Sᶜ := by
    intro w hwT hwS
    exact hhit ⟨w, hwT, hwS⟩
  exact hT (by
    intro a ha b hb
    exact hcompl (hmiss a ha) (hmiss b hb))

/-- Periodic-free frontier-ball blow-up hits any target set with at least two distinct values. -/
theorem periodic_free_frontier_ball_forward_hit_of_not_subsingleton_target
    {c z₀ : ℂ} {ρ Rlift : ℝ} {T : Set ℂ}
    (hzfront : z₀ ∈ frontier (filledJulia c)) (hρ0 : 0 < ρ) (hρR : ρ < Rlift / 2)
    (hnper : ∀ n z, z ∈ ball z₀ Rlift → (quadratic c)^[n] z ≠ z)
    (hT : ¬ Set.Subsingleton T) :
    ∃ w ∈ T, ∃ n z, z ∈ ball z₀ Rlift ∧ (quadratic c)^[n] z = w := by
  let S : Set ℂ := ⋃ n : ℕ, ((fun z => (quadratic c)^[n] z) '' ball z₀ Rlift)
  have hcompl : Set.Subsingleton Sᶜ :=
    periodic_free_frontier_ball_forward_image_compl_subsingleton
      hzfront hρ0 hρR hnper
  obtain ⟨w, hwT, hwS⟩ := exists_mem_of_compl_subsingleton_of_not_subsingleton hcompl hT
  rcases Set.mem_iUnion.mp hwS with ⟨n, hwn⟩
  rcases hwn with ⟨z, hzball, hval⟩
  exact ⟨w, hwT, n, z, hzball, hval⟩

/-- A non-countable target set is non-subsingleton. -/
theorem not_subsingleton_of_not_countable {T : Set ℂ} (hT : ¬ T.Countable) :
    ¬ Set.Subsingleton T := by
  intro hsub
  exact hT hsub.countable

/-- Countable-avoidance form of the periodic-free frontier-ball blow-up: every non-countable target
set is hit by some forward image of the ball. -/
theorem periodic_free_frontier_ball_forward_hit_of_not_countable_target
    {c z₀ : ℂ} {ρ Rlift : ℝ} {T : Set ℂ}
    (hzfront : z₀ ∈ frontier (filledJulia c)) (hρ0 : 0 < ρ) (hρR : ρ < Rlift / 2)
    (hnper : ∀ n z, z ∈ ball z₀ Rlift → (quadratic c)^[n] z ≠ z)
    (hT : ¬ T.Countable) :
    ∃ w ∈ T, ∃ n z, z ∈ ball z₀ Rlift ∧ (quadratic c)^[n] z = w :=
  periodic_free_frontier_ball_forward_hit_of_not_subsingleton_target
    hzfront hρ0 hρR hnper (not_subsingleton_of_not_countable hT)

/-- Dichotomy form targeted at inverse-branch construction: every frontier ball either already
contains a periodic point, or its forward orbit hits any prescribed non-subsingleton target set. -/
theorem frontier_ball_periodic_or_forward_hit_target_of_not_subsingleton
    {c z₀ : ℂ} {ρ Rlift : ℝ} {T : Set ℂ}
    (hzfront : z₀ ∈ frontier (filledJulia c)) (hρ0 : 0 < ρ) (hρR : ρ < Rlift / 2)
    (hT : ¬ Set.Subsingleton T) :
    (∃ n z, z ∈ ball z₀ Rlift ∧ (quadratic c)^[n] z = z) ∨
      ∃ w ∈ T, ∃ n z, z ∈ ball z₀ Rlift ∧ (quadratic c)^[n] z = w := by
  by_cases hper : ∃ n z, z ∈ ball z₀ Rlift ∧ (quadratic c)^[n] z = z
  · exact Or.inl hper
  · refine Or.inr (periodic_free_frontier_ball_forward_hit_of_not_subsingleton_target
      hzfront hρ0 hρR ?_ hT)
    intro n z hz hfix
    exact hper ⟨n, z, hz, hfix⟩

/-- Countable-avoidance dichotomy form: every frontier ball either already contains a periodic point,
or its forward orbit hits any prescribed non-countable target set. -/
theorem frontier_ball_periodic_or_forward_hit_target_of_not_countable
    {c z₀ : ℂ} {ρ Rlift : ℝ} {T : Set ℂ}
    (hzfront : z₀ ∈ frontier (filledJulia c)) (hρ0 : 0 < ρ) (hρR : ρ < Rlift / 2)
    (hT : ¬ T.Countable) :
    (∃ n z, z ∈ ball z₀ Rlift ∧ (quadratic c)^[n] z = z) ∨
      ∃ w ∈ T, ∃ n z, z ∈ ball z₀ Rlift ∧ (quadratic c)^[n] z = w :=
  frontier_ball_periodic_or_forward_hit_target_of_not_subsingleton
    hzfront hρ0 hρR (not_subsingleton_of_not_countable hT)

/-- Positive critical orbit of the quadratic map, excluding the depth-zero critical point. -/
def positiveCriticalOrbit (c : ℂ) : Set ℂ :=
  Set.range fun j : ℕ => (quadratic c)^[j + 1] 0

/-- The positive critical orbit is countable. -/
theorem countable_positiveCriticalOrbit (c : ℂ) : (positiveCriticalOrbit c).Countable := by
  exact Set.countable_range _

/-- Removing a countable exceptional set from a non-countable target leaves a non-countable target. -/
theorem not_countable_diff_countable {T E : Set ℂ}
    (hT : ¬ T.Countable) (hE : E.Countable) :
    ¬ (T \ E).Countable := by
  intro hdiff
  apply hT
  exact (hdiff.union hE).mono (by
    intro z hzT
    by_cases hzE : z ∈ E
    · exact Or.inr hzE
    · exact Or.inl ⟨hzT, hzE⟩)

/-- Positive-depth blow-up for off-ball target sets.  If a frontier ball has no positive periodic
point, then its positive forward images hit every non-subsingleton target set lying off the ball. -/
theorem positive_periodic_free_frontier_ball_forward_hit_of_not_subsingleton_target_off_ball
    {c z₀ : ℂ} {ρ Rlift : ℝ} {T : Set ℂ}
    (hzfront : z₀ ∈ frontier (filledJulia c)) (hρ0 : 0 < ρ) (hρR : ρ < Rlift / 2)
    (hnper : ∀ n z, 1 ≤ n → z ∈ ball z₀ Rlift → (quadratic c)^[n] z ≠ z)
    (hT : ¬ Set.Subsingleton T)
    (hToff : ∀ w ∈ T, w ∉ ball z₀ Rlift) :
    ∃ w ∈ T, ∃ n z, 1 ≤ n ∧ z ∈ ball z₀ Rlift ∧ (quadratic c)^[n] z = w := by
  by_contra hnone
  apply hT
  intro α hα β hβ
  by_contra hαβ
  have hαoff : ∀ z ∈ ball z₀ Rlift, z ≠ α := by
    intro z hz hza
    exact hToff α hα (by simpa [hza] using hz)
  have hβoff : ∀ z ∈ ball z₀ Rlift, z ≠ β := by
    intro z hz hzb
    exact hToff β hβ (by simpa [hzb] using hz)
  have hhit := positive_periodic_free_frontier_ball_forward_orbit_hits_one_of_two_values_off_ball
    hzfront hρ0 hρR hαβ hαoff hβoff hnper
  rcases hhit with hhitα | hhitβ
  · obtain ⟨n, z, hn, hz, hval⟩ := hhitα
    exact hnone ⟨α, hα, n, z, hn, hz, hval⟩
  · obtain ⟨n, z, hn, hz, hval⟩ := hhitβ
    exact hnone ⟨β, hβ, n, z, hn, hz, hval⟩

/-- Countable-avoidance version of the positive-depth off-ball blow-up. -/
theorem positive_periodic_free_frontier_ball_forward_hit_of_not_countable_target_off_ball
    {c z₀ : ℂ} {ρ Rlift : ℝ} {T : Set ℂ}
    (hzfront : z₀ ∈ frontier (filledJulia c)) (hρ0 : 0 < ρ) (hρR : ρ < Rlift / 2)
    (hnper : ∀ n z, 1 ≤ n → z ∈ ball z₀ Rlift → (quadratic c)^[n] z ≠ z)
    (hT : ¬ T.Countable)
    (hToff : ∀ w ∈ T, w ∉ ball z₀ Rlift) :
    ∃ w ∈ T, ∃ n z, 1 ≤ n ∧ z ∈ ball z₀ Rlift ∧ (quadratic c)^[n] z = w :=
  positive_periodic_free_frontier_ball_forward_hit_of_not_subsingleton_target_off_ball
    hzfront hρ0 hρR hnper (not_subsingleton_of_not_countable hT) hToff

/-- Positive-period dichotomy for non-countable off-ball target sets. -/
theorem frontier_ball_positive_periodic_or_forward_hit_target_of_not_countable_off_ball
    {c z₀ : ℂ} {ρ Rlift : ℝ} {T : Set ℂ}
    (hzfront : z₀ ∈ frontier (filledJulia c)) (hρ0 : 0 < ρ) (hρR : ρ < Rlift / 2)
    (hT : ¬ T.Countable)
    (hToff : ∀ w ∈ T, w ∉ ball z₀ Rlift) :
    (∃ n z, 1 ≤ n ∧ z ∈ ball z₀ Rlift ∧ (quadratic c)^[n] z = z) ∨
      ∃ w ∈ T, ∃ n z, 1 ≤ n ∧ z ∈ ball z₀ Rlift ∧ (quadratic c)^[n] z = w := by
  by_cases hper : ∃ n z, 1 ≤ n ∧ z ∈ ball z₀ Rlift ∧ (quadratic c)^[n] z = z
  · exact Or.inl hper
  · refine Or.inr (positive_periodic_free_frontier_ball_forward_hit_of_not_countable_target_off_ball
      hzfront hρ0 hρR ?_ hT hToff)
    intro n z hn hz hfix
    exact hper ⟨n, z, hn, hz, hfix⟩

/-- Positive-period off-ball blow-up with automatic avoidance of the positive critical orbit. -/
theorem frontier_ball_positive_periodic_or_forward_hit_target_avoiding_criticalOrbit
    {c z₀ : ℂ} {ρ Rlift : ℝ} {T : Set ℂ}
    (hzfront : z₀ ∈ frontier (filledJulia c)) (hρ0 : 0 < ρ) (hρR : ρ < Rlift / 2)
    (hT : ¬ T.Countable)
    (hToff : ∀ w ∈ T, w ∉ ball z₀ Rlift) :
    (∃ n z, 1 ≤ n ∧ z ∈ ball z₀ Rlift ∧ (quadratic c)^[n] z = z) ∨
      ∃ w ∈ T, w ∉ positiveCriticalOrbit c ∧
        ∃ n z, 1 ≤ n ∧ z ∈ ball z₀ Rlift ∧ (quadratic c)^[n] z = w := by
  let Tgood : Set ℂ := T \ positiveCriticalOrbit c
  have hTgood : ¬ Tgood.Countable :=
    not_countable_diff_countable hT (countable_positiveCriticalOrbit c)
  have hToff_good : ∀ w ∈ Tgood, w ∉ ball z₀ Rlift := by
    intro w hw
    exact hToff w hw.1
  have hsel := frontier_ball_positive_periodic_or_forward_hit_target_of_not_countable_off_ball
    hzfront hρ0 hρR hTgood hToff_good
  rcases hsel with hper | hhit
  · exact Or.inl hper
  · rcases hhit with ⟨w, hwgood, n, z, hn, hz, hval⟩
    exact Or.inr ⟨w, hwgood.1, hwgood.2, n, z, hn, hz, hval⟩

end

end Bottcher
