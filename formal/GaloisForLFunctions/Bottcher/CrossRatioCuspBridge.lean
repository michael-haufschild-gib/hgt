/-
# Cross-ratio obstruction for modular-lambda cusp-normalized lifts

The compact-basepoint branch uses properness to keep modular-lambda lifts in a compact part of
`ℍ`.  The complementary branch is cusp escape.  This file closes the normal-family contradiction
once the lift coordinates have been normalized into one of the three cusp charts with uniform
height escape on the frontier ball.
-/
import GaloisForLFunctions.Bottcher.CrossRatioNormalBridge
import GaloisForLFunctions.Bottcher.ModularLambdaCuspNormal
import GaloisForLFunctions.Bottcher.DiskSchwarzPick
import GaloisForLFunctions.Bottcher.ModularLambdaOmittingLift

open Complex Metric Set Filter Topology

namespace Bottcher

noncomputable section

/-- A Harnack-style lower bound converts basepoint height escape into uniform height escape. -/
theorem uniform_im_tendsto_atTop_of_base_im_tendsto_atTop_of_harnack
    {K : Set ℂ} {τseq : ℕ → ℂ → ℂ} {z₀ : ℂ} {A : ℝ}
    (hA : 0 < A)
    (hbase : ∀ M : ℝ, ∀ᶠ n in atTop, M ≤ (τseq n z₀).im)
    (hH : ∀ n z, z ∈ K → A * (τseq n z₀).im ≤ (τseq n z).im) :
    ∀ M : ℝ, ∀ᶠ n in atTop, ∀ z ∈ K, M ≤ (τseq n z).im := by
  intro M
  filter_upwards [hbase (M / A)] with n hn z hz
  have hmul : M ≤ A * (τseq n z₀).im := by
    have h := mul_le_mul_of_nonneg_left hn hA.le
    rwa [mul_div_cancel₀ M hA.ne'] at h
  exact le_trans hmul (hH n z hz)

/-- Cusp `∞` branch: uniform height escape of lift coordinates makes `λ` converge spherically to
`0`, giving the forbidden spherical cross-ratio limit. -/
theorem no_cuspInf_modularLift_crossRatio_of_frontier {c α β z₀ : ℂ}
    {ρ : ℝ} {U : Set ℂ} {Rseq : ℕ → ℂ → ℂ} {τseq : ℕ → ℂ → ℂ}
    (hzfront : z₀ ∈ frontier (filledJulia c)) (hρ0 : 0 < ρ)
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
    (heq : ∀ n, Set.EqOn
      (fun z => stereo (modularLambda (τseq n z))) (fun z => stereo (Rseq n z))
      (closedBall z₀ ρ))
    (hIm : ∀ M : ℝ, ∀ᶠ n in atTop, ∀ z ∈ closedBall z₀ ρ, M ≤ (τseq n z).im) :
    False := by
  have hconv_raw :
      TendstoUniformlyOn
        (fun n z => stereo (modularLambda (τseq n z)))
        (fun _z => stereo (0 : ℂ)) atTop (closedBall z₀ ρ) :=
    tendstoUniformlyOn_stereo_modularLambda_of_im_tendsto_atTop hIm
  have hconv :
      TendstoUniformlyOn (fun n z => stereo (Rseq n z)) (fun _z => stereo (0 : ℂ))
        atTop (closedBall z₀ ρ) := by
    refine hconv_raw.congr ?_
    filter_upwards with n z hz
    exact heq n hz
  have hGcont : ContinuousOn (fun _z : ℂ => stereo (0 : ℂ)) (closedBall z₀ ρ) :=
    continuous_const.continuousOn
  exact no_spherical_crossRatio_uniform_limit_of_frontier hzfront hρ0 hU hαβ hβ hα
    hpreα hzβ hRcont hR
    ⟨id, fun _z => stereo (0 : ℂ), strictMono_id, hGcont, hconv⟩

/-- Cusp `0` branch: the normalized chart `τ = -1/σ`, with `Im σ → ∞`, makes `λ(τ)`
converge spherically to `1`. -/
theorem no_cuspZero_modularLift_crossRatio_of_frontier {c α β z₀ : ℂ}
    {ρ : ℝ} {U : Set ℂ} {Rseq : ℕ → ℂ → ℂ} {σseq : ℕ → ℂ → ℂ}
    (hzfront : z₀ ∈ frontier (filledJulia c)) (hρ0 : 0 < ρ)
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
    (heq : ∀ n, Set.EqOn
      (fun z => stereo (modularLambda (-1 / σseq n z))) (fun z => stereo (Rseq n z))
      (closedBall z₀ ρ))
    (hIm : ∀ M : ℝ, ∀ᶠ n in atTop, ∀ z ∈ closedBall z₀ ρ, M ≤ (σseq n z).im) :
    False := by
  have hconv_raw :
      TendstoUniformlyOn
        (fun n z => stereo (modularLambda (-1 / σseq n z)))
        (fun _z => stereo (1 : ℂ)) atTop (closedBall z₀ ρ) :=
    tendstoUniformlyOn_stereo_modularLambda_neg_inv_of_im_tendsto_atTop hIm
  have hconv :
      TendstoUniformlyOn (fun n z => stereo (Rseq n z)) (fun _z => stereo (1 : ℂ))
        atTop (closedBall z₀ ρ) := by
    refine hconv_raw.congr ?_
    filter_upwards with n z hz
    exact heq n hz
  have hGcont : ContinuousOn (fun _z : ℂ => stereo (1 : ℂ)) (closedBall z₀ ρ) :=
    continuous_const.continuousOn
  exact no_spherical_crossRatio_uniform_limit_of_frontier hzfront hρ0 hU hαβ hβ hα
    hpreα hzβ hRcont hR
    ⟨id, fun _z => stereo (1 : ℂ), strictMono_id, hGcont, hconv⟩

/-- Cusp `1` branch: the normalized chart `τ = 1 - 1/σ`, with `Im σ → ∞`, makes `λ(τ)`
converge spherically to the north pole. -/
theorem no_cuspOne_modularLift_crossRatio_of_frontier {c α β z₀ : ℂ}
    {ρ : ℝ} {U : Set ℂ} {Rseq : ℕ → ℂ → ℂ} {σseq : ℕ → ℂ → ℂ}
    (hzfront : z₀ ∈ frontier (filledJulia c)) (hρ0 : 0 < ρ)
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
    (heq : ∀ n, Set.EqOn
      (fun z => stereo (modularLambda (1 - 1 / σseq n z))) (fun z => stereo (Rseq n z))
      (closedBall z₀ ρ))
    (hIm : ∀ M : ℝ, ∀ᶠ n in atTop, ∀ z ∈ closedBall z₀ ρ, M ≤ (σseq n z).im) :
    False := by
  have hconv_raw :
      TendstoUniformlyOn
        (fun n z => stereo (modularLambda (1 - 1 / σseq n z)))
        (fun _z => northPole) atTop (closedBall z₀ ρ) :=
    tendstoUniformlyOn_stereo_modularLambda_one_sub_inv_of_im_tendsto_atTop hIm
  have hconv :
      TendstoUniformlyOn (fun n z => stereo (Rseq n z)) (fun _z => northPole)
        atTop (closedBall z₀ ρ) := by
    refine hconv_raw.congr ?_
    filter_upwards with n z hz
    exact heq n hz
  have hGcont : ContinuousOn (fun _z : ℂ => northPole) (closedBall z₀ ρ) :=
    continuous_const.continuousOn
  exact no_spherical_crossRatio_uniform_limit_of_frontier hzfront hρ0 hU hαβ hβ hα
    hpreα hzβ hRcont hR
    ⟨id, fun _z => northPole, strictMono_id, hGcont, hconv⟩

/-- Harnack-form cusp `∞` branch.  The remaining analytic producer should supply `A > 0` and
`A * Im τₙ(z₀) ≤ Im τₙ(z)` on the closed ball for normalized upper-half-plane lifts. -/
theorem no_cuspInf_harnack_modularLift_crossRatio_of_frontier {c α β z₀ : ℂ}
    {ρ A : ℝ} {U : Set ℂ} {Rseq : ℕ → ℂ → ℂ} {τseq : ℕ → ℂ → ℂ}
    (hzfront : z₀ ∈ frontier (filledJulia c)) (hρ0 : 0 < ρ)
    (hA : 0 < A)
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
    (heq : ∀ n, Set.EqOn
      (fun z => stereo (modularLambda (τseq n z))) (fun z => stereo (Rseq n z))
      (closedBall z₀ ρ))
    (hbase : ∀ M : ℝ, ∀ᶠ n in atTop, M ≤ (τseq n z₀).im)
    (hH : ∀ n z, z ∈ closedBall z₀ ρ → A * (τseq n z₀).im ≤ (τseq n z).im) :
    False :=
  no_cuspInf_modularLift_crossRatio_of_frontier hzfront hρ0 hU hαβ hβ hα hpreα hzβ
    hRcont hR heq
    (uniform_im_tendsto_atTop_of_base_im_tendsto_atTop_of_harnack hA hbase hH)

/-- Harnack-form cusp `0` branch, in the chart `τ = -1/σ`. -/
theorem no_cuspZero_harnack_modularLift_crossRatio_of_frontier {c α β z₀ : ℂ}
    {ρ A : ℝ} {U : Set ℂ} {Rseq : ℕ → ℂ → ℂ} {σseq : ℕ → ℂ → ℂ}
    (hzfront : z₀ ∈ frontier (filledJulia c)) (hρ0 : 0 < ρ)
    (hA : 0 < A)
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
    (heq : ∀ n, Set.EqOn
      (fun z => stereo (modularLambda (-1 / σseq n z))) (fun z => stereo (Rseq n z))
      (closedBall z₀ ρ))
    (hbase : ∀ M : ℝ, ∀ᶠ n in atTop, M ≤ (σseq n z₀).im)
    (hH : ∀ n z, z ∈ closedBall z₀ ρ → A * (σseq n z₀).im ≤ (σseq n z).im) :
    False :=
  no_cuspZero_modularLift_crossRatio_of_frontier hzfront hρ0 hU hαβ hβ hα hpreα hzβ
    hRcont hR heq
    (uniform_im_tendsto_atTop_of_base_im_tendsto_atTop_of_harnack hA hbase hH)

/-- Harnack-form cusp `1` branch, in the chart `τ = 1 - 1/σ`. -/
theorem no_cuspOne_harnack_modularLift_crossRatio_of_frontier {c α β z₀ : ℂ}
    {ρ A : ℝ} {U : Set ℂ} {Rseq : ℕ → ℂ → ℂ} {σseq : ℕ → ℂ → ℂ}
    (hzfront : z₀ ∈ frontier (filledJulia c)) (hρ0 : 0 < ρ)
    (hA : 0 < A)
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
    (heq : ∀ n, Set.EqOn
      (fun z => stereo (modularLambda (1 - 1 / σseq n z))) (fun z => stereo (Rseq n z))
      (closedBall z₀ ρ))
    (hbase : ∀ M : ℝ, ∀ᶠ n in atTop, M ≤ (σseq n z₀).im)
    (hH : ∀ n z, z ∈ closedBall z₀ ρ → A * (σseq n z₀).im ≤ (σseq n z).im) :
    False :=
  no_cuspOne_modularLift_crossRatio_of_frontier hzfront hρ0 hU hαβ hβ hα hpreα hzβ
    hRcont hR heq
    (uniform_im_tendsto_atTop_of_base_im_tendsto_atTop_of_harnack hA hbase hH)

/-- Schwarz-Pick-produced cusp `∞` branch for modular disk lifts.  The Harnack constant is the
closed-ball factor `(1 - ρ / Rlift) / (1 + ρ / Rlift)`, so no Harnack hypothesis remains. -/
theorem no_cuspInf_schwarzPick_modularDiskLift_crossRatio_of_frontier {c α β z₀ : ℂ}
    {ρ Rlift : ℝ} {U : Set ℂ} {Rseq : ℕ → ℂ → ℂ} {gseq : ℕ → ℂ → ℂ}
    (hzfront : z₀ ∈ frontier (filledJulia c)) (hρ0 : 0 < ρ)
    (hRlift : 0 < Rlift) (hρRlift : ρ < Rlift)
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
    (heq : ∀ n, Set.EqOn
      (fun z => stereo (modularLambda (cayleyInv (gseq n z)))) (fun z => stereo (Rseq n z))
      (closedBall z₀ ρ))
    (hgdiff : ∀ n, DifferentiableOn ℂ (gseq n) (ball z₀ Rlift))
    (hglt : ∀ n z, z ∈ ball z₀ Rlift → ‖gseq n z‖ < 1)
    (hbase : ∀ M : ℝ, ∀ᶠ n in atTop, M ≤ (cayleyInv (gseq n z₀)).im) :
    False := by
  let A : ℝ := (1 - ρ / Rlift) / (1 + ρ / Rlift)
  have hA : 0 < A := harnackFactor_pos hRlift hρ0.le hρRlift
  have hH : ∀ n z, z ∈ closedBall z₀ ρ →
      A * (cayleyInv (gseq n z₀)).im ≤ (cayleyInv (gseq n z)).im := by
    intro n z hz
    exact cayleyInv_im_harnack_closedBall (g := gseq n) (c := z₀) (ρ := ρ) (R := Rlift)
      hRlift hρ0.le hρRlift (hgdiff n) (hglt n) z hz
  exact no_cuspInf_harnack_modularLift_crossRatio_of_frontier
    (τseq := fun n z => cayleyInv (gseq n z)) hzfront hρ0 hA hU hαβ hβ hα hpreα
    hzβ hRcont hR heq hbase hH

/-- Schwarz-Pick-produced cusp `0` branch for modular disk lifts in the chart
`τ = -1 / σ`. -/
theorem no_cuspZero_schwarzPick_modularDiskLift_crossRatio_of_frontier {c α β z₀ : ℂ}
    {ρ Rlift : ℝ} {U : Set ℂ} {Rseq : ℕ → ℂ → ℂ} {gseq : ℕ → ℂ → ℂ}
    (hzfront : z₀ ∈ frontier (filledJulia c)) (hρ0 : 0 < ρ)
    (hRlift : 0 < Rlift) (hρRlift : ρ < Rlift)
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
    (heq : ∀ n, Set.EqOn
      (fun z => stereo (modularLambda (-1 / cayleyInv (gseq n z))))
      (fun z => stereo (Rseq n z)) (closedBall z₀ ρ))
    (hgdiff : ∀ n, DifferentiableOn ℂ (gseq n) (ball z₀ Rlift))
    (hglt : ∀ n z, z ∈ ball z₀ Rlift → ‖gseq n z‖ < 1)
    (hbase : ∀ M : ℝ, ∀ᶠ n in atTop, M ≤ (cayleyInv (gseq n z₀)).im) :
    False := by
  let A : ℝ := (1 - ρ / Rlift) / (1 + ρ / Rlift)
  have hA : 0 < A := harnackFactor_pos hRlift hρ0.le hρRlift
  have hH : ∀ n z, z ∈ closedBall z₀ ρ →
      A * (cayleyInv (gseq n z₀)).im ≤ (cayleyInv (gseq n z)).im := by
    intro n z hz
    exact cayleyInv_im_harnack_closedBall (g := gseq n) (c := z₀) (ρ := ρ) (R := Rlift)
      hRlift hρ0.le hρRlift (hgdiff n) (hglt n) z hz
  exact no_cuspZero_harnack_modularLift_crossRatio_of_frontier
    (σseq := fun n z => cayleyInv (gseq n z)) hzfront hρ0 hA hU hαβ hβ hα hpreα
    hzβ hRcont hR heq hbase hH

/-- Schwarz-Pick-produced cusp `1` branch for modular disk lifts in the chart
`τ = 1 - 1 / σ`. -/
theorem no_cuspOne_schwarzPick_modularDiskLift_crossRatio_of_frontier {c α β z₀ : ℂ}
    {ρ Rlift : ℝ} {U : Set ℂ} {Rseq : ℕ → ℂ → ℂ} {gseq : ℕ → ℂ → ℂ}
    (hzfront : z₀ ∈ frontier (filledJulia c)) (hρ0 : 0 < ρ)
    (hRlift : 0 < Rlift) (hρRlift : ρ < Rlift)
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
    (heq : ∀ n, Set.EqOn
      (fun z => stereo (modularLambda (1 - 1 / cayleyInv (gseq n z))))
      (fun z => stereo (Rseq n z)) (closedBall z₀ ρ))
    (hgdiff : ∀ n, DifferentiableOn ℂ (gseq n) (ball z₀ Rlift))
    (hglt : ∀ n z, z ∈ ball z₀ Rlift → ‖gseq n z‖ < 1)
    (hbase : ∀ M : ℝ, ∀ᶠ n in atTop, M ≤ (cayleyInv (gseq n z₀)).im) :
    False := by
  let A : ℝ := (1 - ρ / Rlift) / (1 + ρ / Rlift)
  have hA : 0 < A := harnackFactor_pos hRlift hρ0.le hρRlift
  have hH : ∀ n z, z ∈ closedBall z₀ ρ →
      A * (cayleyInv (gseq n z₀)).im ≤ (cayleyInv (gseq n z)).im := by
    intro n z hz
    exact cayleyInv_im_harnack_closedBall (g := gseq n) (c := z₀) (ρ := ρ) (R := Rlift)
      hRlift hρ0.le hρRlift (hgdiff n) (hglt n) z hz
  exact no_cuspOne_harnack_modularLift_crossRatio_of_frontier
    (σseq := fun n z => cayleyInv (gseq n z)) hzfront hρ0 hA hU hαβ hβ hα hpreα
    hzβ hRcont hR heq hbase hH

end

end Bottcher

namespace Bottcher

noncomputable section

/-- Cusp `∞` branch from based high modular preimages.  This removes the need for the caller to
construct the strict disk lifts: a chosen high base preimage for each member determines a based
covering lift, whose strict disk image feeds the Schwarz-Pick Harnack cusp close. -/
theorem no_cuspInf_basedPreimage_schwarzPick_modularLift_crossRatio_of_frontier {c α β z₀ : ℂ}
    {ρ Rlift : ℝ} {U : Set ℂ} {Rseq : ℕ → ℂ → ℂ} {τseq : ℕ → UpperHalfPlane}
    (hzfront : z₀ ∈ frontier (filledJulia c)) (hρ0 : 0 < ρ)
    (hRlift : 0 < Rlift) (hρRlift : ρ < Rlift)
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
    (hdiff : ∀ n, DifferentiableOn ℂ (Rseq n) (ball z₀ Rlift))
    (homit : ∀ n z, z ∈ ball z₀ Rlift → Rseq n z ∈ ({0, 1} : Set ℂ)ᶜ)
    (hτ : ∀ n, modularLambda (τseq n : ℂ) = Rseq n z₀)
    (hbase : ∀ M : ℝ, ∀ᶠ n in atTop, M ≤ (τseq n : ℂ).im) :
    False := by
  have hclosed_sub_ball : closedBall z₀ ρ ⊆ ball z₀ Rlift := by
    intro z hz
    have hzle : dist z z₀ ≤ ρ := by
      simpa [closedBall, dist_comm] using hz
    rw [mem_ball]
    exact lt_of_le_of_lt hzle hρRlift
  have hlift : ∀ n, ∃ g : ℂ → ℂ,
      DifferentiableOn ℂ g (ball z₀ Rlift) ∧
      (∀ z ∈ ball z₀ Rlift, ‖g z‖ < 1) ∧
      g z₀ = cayley (τseq n : ℂ) ∧
      Set.EqOn (fun z => modularLambda (cayleyInv (g z))) (Rseq n) (ball z₀ Rlift) := by
    intro n
    exact omitting_lift_member_based_strict hRlift (Rseq n) (hdiff n) (homit n) (τseq n) (hτ n)
  choose g hgdiff hglt hgbase hgeq using hlift
  have heq : ∀ n, Set.EqOn
      (fun z => stereo (modularLambda (cayleyInv (g n z)))) (fun z => stereo (Rseq n z))
      (closedBall z₀ ρ) := by
    intro n z hz
    exact congrArg stereo (hgeq n (hclosed_sub_ball hz))
  have hbase_g : ∀ M : ℝ, ∀ᶠ n in atTop, M ≤ (cayleyInv (g n z₀)).im := by
    intro M
    filter_upwards [hbase M] with n hn
    have hne : (τseq n : ℂ) + Complex.I ≠ 0 := by
      intro h
      have him : (τseq n : ℂ).im = -1 := by
        rw [show (τseq n : ℂ) = -Complex.I by linear_combination h]
        simp
      linarith [(τseq n).2]
    rw [hgbase n, cayleyInv_cayley hne]
    exact hn
  exact no_cuspInf_schwarzPick_modularDiskLift_crossRatio_of_frontier (gseq := g) hzfront hρ0
    hRlift hρRlift hU hαβ hβ hα hpreα hzβ hRcont hR heq hgdiff hglt hbase_g

end

end Bottcher

namespace Bottcher

noncomputable section

/-- Cusp `0` branch from based high modular preimages.  If each base value is represented as
`λ(-1 / σ_n)` with `Im σ_n → ∞`, the transformed family `1 - R_n` has based preimage `σ_n`.
The based strict disk lift and the `S` identity then return the family to the cusp `0` chart and
feed the Schwarz-Pick/Harnack cusp contradiction. -/
theorem no_cuspZero_basedPreimage_schwarzPick_modularLift_crossRatio_of_frontier {c α β z₀ : ℂ}
    {ρ Rlift : ℝ} {U : Set ℂ} {Rseq : ℕ → ℂ → ℂ} {σseq : ℕ → UpperHalfPlane}
    (hzfront : z₀ ∈ frontier (filledJulia c)) (hρ0 : 0 < ρ)
    (hRlift : 0 < Rlift) (hρRlift : ρ < Rlift)
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
    (hdiff : ∀ n, DifferentiableOn ℂ (Rseq n) (ball z₀ Rlift))
    (homit : ∀ n z, z ∈ ball z₀ Rlift → Rseq n z ∈ ({0, 1} : Set ℂ)ᶜ)
    (hσ : ∀ n, modularLambda (-1 / (σseq n : ℂ)) = Rseq n z₀)
    (hbase : ∀ M : ℝ, ∀ᶠ n in atTop, M ≤ (σseq n : ℂ).im) :
    False := by
  let Sseq : ℕ → ℂ → ℂ := fun n z => 1 - Rseq n z
  have hclosed_sub_ball : closedBall z₀ ρ ⊆ ball z₀ Rlift := by
    intro z hz
    have hzle : dist z z₀ ≤ ρ := by
      simpa [closedBall, dist_comm] using hz
    rw [mem_ball]
    exact lt_of_le_of_lt hzle hρRlift
  have hSdiff : ∀ n, DifferentiableOn ℂ (Sseq n) (ball z₀ Rlift) := by
    intro n
    exact (differentiableOn_const (c := (1 : ℂ))).sub (hdiff n)
  have hSomit : ∀ n z, z ∈ ball z₀ Rlift → Sseq n z ∈ ({0, 1} : Set ℂ)ᶜ := by
    intro n z hz
    rw [mem_compl_iff]
    intro hbad
    have hRomit := homit n z hz
    rw [mem_compl_iff] at hRomit
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hbad
    rcases hbad with hzero | hone
    · apply hRomit
      rw [Set.mem_insert_iff, Set.mem_singleton_iff]
      right
      exact (sub_eq_zero.mp hzero).symm
    · apply hRomit
      rw [Set.mem_insert_iff, Set.mem_singleton_iff]
      left
      have hneg : -Rseq n z = 0 := by linear_combination hone
      exact neg_eq_zero.mp hneg
  have hSbase : ∀ n, modularLambda (σseq n : ℂ) = Sseq n z₀ := by
    intro n
    have hSrel := modularLambda_S' (τ := (σseq n : ℂ)) (σseq n).2
    calc
      modularLambda (σseq n : ℂ)
          = 1 - modularLambda (-1 / (σseq n : ℂ)) := by linear_combination hSrel
      _ = Sseq n z₀ := by simp [Sseq, hσ n]
  have hlift : ∀ n, ∃ g : ℂ → ℂ,
      DifferentiableOn ℂ g (ball z₀ Rlift) ∧
      (∀ z ∈ ball z₀ Rlift, ‖g z‖ < 1) ∧
      g z₀ = cayley (σseq n : ℂ) ∧
      Set.EqOn (fun z => modularLambda (cayleyInv (g z))) (Sseq n) (ball z₀ Rlift) := by
    intro n
    exact omitting_lift_member_based_strict hRlift (Sseq n) (hSdiff n) (hSomit n) (σseq n)
      (hSbase n)
  choose g hgdiff hglt hgbase hgeq using hlift
  have heq : ∀ n, Set.EqOn
      (fun z => stereo (modularLambda (-1 / cayleyInv (g n z))))
      (fun z => stereo (Rseq n z)) (closedBall z₀ ρ) := by
    intro n z hz
    have hzball : z ∈ ball z₀ Rlift := hclosed_sub_ball hz
    have hgzlt : ‖g n z‖ < 1 := hglt n z hzball
    have hgne : g n z ≠ 1 := by
      intro h
      have hnorm : ‖g n z‖ = 1 := by rw [h, norm_one]
      linarith
    have hτim : 0 < (cayleyInv (g n z)).im := by
      rw [cayleyInv_im_eq_diskPoissonOne hgne]
      exact diskPoissonOne_pos_of_norm_lt_one hgzlt
    have hSrel := modularLambda_S' (τ := cayleyInv (g n z)) hτim
    have hLiftEq : modularLambda (cayleyInv (g n z)) = Sseq n z := hgeq n hzball
    have hval : modularLambda (-1 / cayleyInv (g n z)) = Rseq n z := by
      calc
        modularLambda (-1 / cayleyInv (g n z))
            = 1 - modularLambda (cayleyInv (g n z)) := hSrel
        _ = 1 - Sseq n z := by rw [hLiftEq]
        _ = Rseq n z := by simp [Sseq]
    exact congrArg stereo hval
  have hbase_g : ∀ M : ℝ, ∀ᶠ n in atTop, M ≤ (cayleyInv (g n z₀)).im := by
    intro M
    filter_upwards [hbase M] with n hn
    have hne : (σseq n : ℂ) + Complex.I ≠ 0 := by
      intro h
      have him : (σseq n : ℂ).im = -1 := by
        rw [show (σseq n : ℂ) = -Complex.I by linear_combination h]
        simp
      linarith [(σseq n).2]
    rw [hgbase n, cayleyInv_cayley hne]
    exact hn
  exact no_cuspZero_schwarzPick_modularDiskLift_crossRatio_of_frontier (gseq := g) hzfront hρ0
    hRlift hρRlift hU hαβ hβ hα hpreα hzβ hRcont hR heq hgdiff hglt hbase_g

end

end Bottcher

namespace Bottcher

noncomputable section

/-- Cusp `1` branch from based high modular preimages.  If each base value is represented as
`λ(1 - 1 / σ_n)` with `Im σ_n → ∞`, the transformed family `(1 - R_n)⁻¹` has based preimage
`σ_n`.  The `S` and `T` identities convert the strict disk lift back to the cusp `1` chart. -/
theorem no_cuspOne_basedPreimage_schwarzPick_modularLift_crossRatio_of_frontier {c α β z₀ : ℂ}
    {ρ Rlift : ℝ} {U : Set ℂ} {Rseq : ℕ → ℂ → ℂ} {σseq : ℕ → UpperHalfPlane}
    (hzfront : z₀ ∈ frontier (filledJulia c)) (hρ0 : 0 < ρ)
    (hRlift : 0 < Rlift) (hρRlift : ρ < Rlift)
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
    (hdiff : ∀ n, DifferentiableOn ℂ (Rseq n) (ball z₀ Rlift))
    (homit : ∀ n z, z ∈ ball z₀ Rlift → Rseq n z ∈ ({0, 1} : Set ℂ)ᶜ)
    (hσ : ∀ n, modularLambda (1 - 1 / (σseq n : ℂ)) = Rseq n z₀)
    (hbase : ∀ M : ℝ, ∀ᶠ n in atTop, M ≤ (σseq n : ℂ).im) :
    False := by
  let Fseq : ℕ → ℂ → ℂ := fun n z => ((1 : ℂ) - Rseq n z)⁻¹
  have hclosed_sub_ball : closedBall z₀ ρ ⊆ ball z₀ Rlift := by
    intro z hz
    have hzle : dist z z₀ ≤ ρ := by
      simpa [closedBall, dist_comm] using hz
    rw [mem_ball]
    exact lt_of_le_of_lt hzle hρRlift
  have hFdiff : ∀ n, DifferentiableOn ℂ (Fseq n) (ball z₀ Rlift) := by
    intro n
    exact ((differentiableOn_const (c := (1 : ℂ))).sub (hdiff n)).inv (by
      intro z hz
      exact sub_ne_zero.mpr (Ne.symm (mem_compl01.mp (homit n z hz)).2))
  have hFomit : ∀ n z, z ∈ ball z₀ Rlift → Fseq n z ∈ ({0, 1} : Set ℂ)ᶜ := by
    intro n z hz
    rw [mem_compl_iff]
    intro hbad
    have hRz := mem_compl01.mp (homit n z hz)
    have hden : (1 : ℂ) - Rseq n z ≠ 0 := sub_ne_zero.mpr (Ne.symm hRz.2)
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hbad
    rcases hbad with hzero | hone
    · exact hden (inv_eq_zero.mp hzero)
    · apply hRz.1
      have hdeneq : (1 : ℂ) - Rseq n z = 1 := inv_eq_one.mp hone
      have hneg : -Rseq n z = 0 := by linear_combination hdeneq
      exact neg_eq_zero.mp hneg
  have hFbase : ∀ n, modularLambda (σseq n : ℂ) = Fseq n z₀ := by
    intro n
    have hσim : 0 < (σseq n : ℂ).im := (σseq n).2
    have hnegim : 0 < (-1 / (σseq n : ℂ)).im := neg_inv_im_pos hσim
    have hSrel := modularLambda_S' (τ := (σseq n : ℂ)) hσim
    have hTrel : modularLambda (1 - 1 / (σseq n : ℂ)) =
        modularLambda (-1 / (σseq n : ℂ)) /
          (modularLambda (-1 / (σseq n : ℂ)) - 1) := by
      rw [show 1 - 1 / (σseq n : ℂ) = -1 / (σseq n : ℂ) + 1 by ring]
      exact modularLambda_T_eq' hnegim
    have hlam0 : modularLambda (σseq n : ℂ) ≠ 0 := (modularLambda_omits_zero_one' hσim).1
    have hRformula : Rseq n z₀ = 1 - (modularLambda (σseq n : ℂ))⁻¹ := by
      rw [← hσ n, hTrel, hSrel]
      field_simp [hlam0]
      ring
    change modularLambda (σseq n : ℂ) = ((1 : ℂ) - Rseq n z₀)⁻¹
    rw [hRformula]
    field_simp [hlam0]
    ring
  have hlift : ∀ n, ∃ g : ℂ → ℂ,
      DifferentiableOn ℂ g (ball z₀ Rlift) ∧
      (∀ z ∈ ball z₀ Rlift, ‖g z‖ < 1) ∧
      g z₀ = cayley (σseq n : ℂ) ∧
      Set.EqOn (fun z => modularLambda (cayleyInv (g z))) (Fseq n) (ball z₀ Rlift) := by
    intro n
    exact omitting_lift_member_based_strict hRlift (Fseq n) (hFdiff n) (hFomit n) (σseq n)
      (hFbase n)
  choose g hgdiff hglt hgbase hgeq using hlift
  have heq : ∀ n, Set.EqOn
      (fun z => stereo (modularLambda (1 - 1 / cayleyInv (g n z))))
      (fun z => stereo (Rseq n z)) (closedBall z₀ ρ) := by
    intro n z hz
    have hzball : z ∈ ball z₀ Rlift := hclosed_sub_ball hz
    have hgzlt : ‖g n z‖ < 1 := hglt n z hzball
    have hgne : g n z ≠ 1 := by
      intro h
      have hnorm : ‖g n z‖ = 1 := by rw [h, norm_one]
      linarith
    have hτim : 0 < (cayleyInv (g n z)).im := by
      rw [cayleyInv_im_eq_diskPoissonOne hgne]
      exact diskPoissonOne_pos_of_norm_lt_one hgzlt
    have hnegim : 0 < (-1 / cayleyInv (g n z)).im := neg_inv_im_pos hτim
    have hSrel := modularLambda_S' (τ := cayleyInv (g n z)) hτim
    have hTrel : modularLambda (1 - 1 / cayleyInv (g n z)) =
        modularLambda (-1 / cayleyInv (g n z)) /
          (modularLambda (-1 / cayleyInv (g n z)) - 1) := by
      rw [show 1 - 1 / cayleyInv (g n z) = -1 / cayleyInv (g n z) + 1 by ring]
      exact modularLambda_T_eq' hnegim
    have hLiftEq : modularLambda (cayleyInv (g n z)) = Fseq n z := hgeq n hzball
    have hRz := mem_compl01.mp (homit n z hzball)
    have hden : (1 : ℂ) - Rseq n z ≠ 0 := sub_ne_zero.mpr (Ne.symm hRz.2)
    have hval : modularLambda (1 - 1 / cayleyInv (g n z)) = Rseq n z := by
      rw [hTrel, hSrel, hLiftEq]
      change (1 - ((1 : ℂ) - Rseq n z)⁻¹) /
          ((1 - ((1 : ℂ) - Rseq n z)⁻¹) - 1) = Rseq n z
      field_simp [hden]
      ring
    exact congrArg stereo hval
  have hbase_g : ∀ M : ℝ, ∀ᶠ n in atTop, M ≤ (cayleyInv (g n z₀)).im := by
    intro M
    filter_upwards [hbase M] with n hn
    have hne : (σseq n : ℂ) + Complex.I ≠ 0 := by
      intro h
      have him : (σseq n : ℂ).im = -1 := by
        rw [show (σseq n : ℂ) = -Complex.I by linear_combination h]
        simp
      linarith [(σseq n).2]
    rw [hgbase n, cayleyInv_cayley hne]
    exact hn
  exact no_cuspOne_schwarzPick_modularDiskLift_crossRatio_of_frontier (gseq := g) hzfront hρ0
    hRlift hρRlift hU hαβ hβ hα hpreα hzβ hRcont hR heq hgdiff hglt hbase_g

end

end Bottcher

namespace Bottcher

noncomputable section

/-- Cusp `∞` branch for the anharmonic `T` case.  A high preimage `σ_n` whose translated value
`λ(σ_n + 1)` is the base cross-ratio is the same cusp-escape contradiction, using `σ_n + 1` as the
based upper-half-plane preimage. -/
theorem no_cuspInf_addOne_basedPreimage_schwarzPick_modularLift_crossRatio_of_frontier
    {c α β z₀ : ℂ} {ρ Rlift : ℝ} {U : Set ℂ} {Rseq : ℕ → ℂ → ℂ}
    {σseq : ℕ → UpperHalfPlane}
    (hzfront : z₀ ∈ frontier (filledJulia c)) (hρ0 : 0 < ρ)
    (hRlift : 0 < Rlift) (hρRlift : ρ < Rlift)
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
    (hdiff : ∀ n, DifferentiableOn ℂ (Rseq n) (ball z₀ Rlift))
    (homit : ∀ n z, z ∈ ball z₀ Rlift → Rseq n z ∈ ({0, 1} : Set ℂ)ᶜ)
    (hσ : ∀ n, modularLambda ((σseq n : ℂ) + 1) = Rseq n z₀)
    (hbase : ∀ M : ℝ, ∀ᶠ n in atTop, M ≤ (σseq n : ℂ).im) :
    False := by
  let τseq : ℕ → UpperHalfPlane := fun n =>
    ⟨(σseq n : ℂ) + 1, by simpa [Complex.add_im] using (σseq n).2⟩
  have hτ : ∀ n, modularLambda (τseq n : ℂ) = Rseq n z₀ := by
    intro n
    simpa [τseq] using hσ n
  have hbaseτ : ∀ M : ℝ, ∀ᶠ n in atTop, M ≤ (τseq n : ℂ).im := by
    intro M
    filter_upwards [hbase M] with n hn
    simpa [τseq, Complex.add_im] using hn
  exact no_cuspInf_basedPreimage_schwarzPick_modularLift_crossRatio_of_frontier (τseq := τseq)
    hzfront hρ0 hRlift hρRlift hU hαβ hβ hα hpreα hzβ hRcont hR hdiff homit hτ
    hbaseτ

/-- Cusp `0` branch for the anharmonic `S*T` case.  The shifted high preimage `σ_n + 1` puts
`λ(-1/(σ_n+1))` into the standard cusp-zero chart. -/
theorem no_cuspZero_addOne_basedPreimage_schwarzPick_modularLift_crossRatio_of_frontier
    {c α β z₀ : ℂ} {ρ Rlift : ℝ} {U : Set ℂ} {Rseq : ℕ → ℂ → ℂ}
    {σseq : ℕ → UpperHalfPlane}
    (hzfront : z₀ ∈ frontier (filledJulia c)) (hρ0 : 0 < ρ)
    (hRlift : 0 < Rlift) (hρRlift : ρ < Rlift)
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
    (hdiff : ∀ n, DifferentiableOn ℂ (Rseq n) (ball z₀ Rlift))
    (homit : ∀ n z, z ∈ ball z₀ Rlift → Rseq n z ∈ ({0, 1} : Set ℂ)ᶜ)
    (hσ : ∀ n, modularLambda (-1 / ((σseq n : ℂ) + 1)) = Rseq n z₀)
    (hbase : ∀ M : ℝ, ∀ᶠ n in atTop, M ≤ (σseq n : ℂ).im) :
    False := by
  let σshift : ℕ → UpperHalfPlane := fun n =>
    ⟨(σseq n : ℂ) + 1, by simpa [Complex.add_im] using (σseq n).2⟩
  have hσshift : ∀ n, modularLambda (-1 / (σshift n : ℂ)) = Rseq n z₀ := by
    intro n
    simpa [σshift] using hσ n
  have hbase_shift : ∀ M : ℝ, ∀ᶠ n in atTop, M ≤ (σshift n : ℂ).im := by
    intro M
    filter_upwards [hbase M] with n hn
    simpa [σshift, Complex.add_im] using hn
  exact no_cuspZero_basedPreimage_schwarzPick_modularLift_crossRatio_of_frontier (σseq := σshift)
    hzfront hρ0 hRlift hρRlift hU hαβ hβ hα hpreα hzβ hRcont hR hdiff homit
    hσshift hbase_shift

/-- Cusp `1` branch for the anharmonic `S*T*S` case, `w ↦ w⁻¹`.  The identity
`λ(1 - 1/(σ-1)) = (λ σ)⁻¹` converts the reciprocal value into the standard cusp-one chart, with
`σ_n - 1` still escaping vertically. -/
theorem no_cuspOne_reciprocal_basedPreimage_schwarzPick_modularLift_crossRatio_of_frontier
    {c α β z₀ : ℂ} {ρ Rlift : ℝ} {U : Set ℂ} {Rseq : ℕ → ℂ → ℂ}
    {σseq : ℕ → UpperHalfPlane}
    (hzfront : z₀ ∈ frontier (filledJulia c)) (hρ0 : 0 < ρ)
    (hRlift : 0 < Rlift) (hρRlift : ρ < Rlift)
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
    (hdiff : ∀ n, DifferentiableOn ℂ (Rseq n) (ball z₀ Rlift))
    (homit : ∀ n z, z ∈ ball z₀ Rlift → Rseq n z ∈ ({0, 1} : Set ℂ)ᶜ)
    (hσ : ∀ n, (modularLambda (σseq n : ℂ))⁻¹ = Rseq n z₀)
    (hbase : ∀ M : ℝ, ∀ᶠ n in atTop, M ≤ (σseq n : ℂ).im) :
    False := by
  let σshift : ℕ → UpperHalfPlane := fun n =>
    ⟨(σseq n : ℂ) - 1, by simpa [Complex.sub_im] using (σseq n).2⟩
  have hchart : ∀ n, modularLambda (1 - 1 / (σshift n : ℂ)) = Rseq n z₀ := by
    intro n
    let σ : ℂ := (σseq n : ℂ)
    have hσim : 0 < σ.im := (σseq n).2
    have hσ0 : σ ≠ 0 := by
      intro h
      have : σ.im = 0 := by rw [h]; simp
      linarith
    have hσ1 : σ - 1 ≠ 0 := by
      intro h
      have : σ = 1 := sub_eq_zero.mp h
      have him : σ.im = 0 := by rw [this]; simp
      linarith
    have hnegim : 0 < (-1 / σ).im := neg_inv_im_pos hσim
    have hu0 : -1 / σ + 1 ≠ 0 := by
      intro h
      have hσeq : σ = 1 := by
        field_simp [hσ0] at h
        linear_combination h
      have him : σ.im = 0 := by rw [hσeq]; simp
      linarith
    have huim : 0 < (-1 / σ + 1).im := by
      simpa [Complex.add_im] using hnegim
    have hσ1' : -1 + σ ≠ 0 := by
      intro h
      apply hσ1
      linear_combination h
    have harg : 1 - 1 / (σ - 1) = -1 / (-1 / σ + 1) + 2 := by
      field_simp [hσ0, hσ1, hσ1', hu0]
      ring_nf
    have hSouter := modularLambda_S' (τ := -1 / σ + 1) huim
    have hTinner := modularLambda_T_eq' (τ := -1 / σ) hnegim
    have hSinner := modularLambda_S' (τ := σ) hσim
    have hlam0 : modularLambda σ ≠ 0 := (modularLambda_omits_zero_one' hσim).1
    change modularLambda (1 - 1 / (σ - 1)) = Rseq n z₀
    calc
      modularLambda (1 - 1 / (σ - 1))
          = modularLambda (-1 / (-1 / σ + 1) + 2) := by rw [harg]
      _ = modularLambda (-1 / (-1 / σ + 1)) := modularLambda_add_two _
      _ = 1 - modularLambda (-1 / σ + 1) := hSouter
      _ = 1 - modularLambda (-1 / σ) / (modularLambda (-1 / σ) - 1) := by rw [hTinner]
      _ = 1 - (1 - modularLambda σ) / ((1 - modularLambda σ) - 1) := by rw [hSinner]
      _ = (modularLambda σ)⁻¹ := by
        field_simp [hlam0]
        ring
      _ = Rseq n z₀ := hσ n
  have hbase_shift : ∀ M : ℝ, ∀ᶠ n in atTop, M ≤ (σshift n : ℂ).im := by
    intro M
    filter_upwards [hbase M] with n hn
    simpa [σshift, Complex.sub_im] using hn
  exact no_cuspOne_basedPreimage_schwarzPick_modularLift_crossRatio_of_frontier (σseq := σshift)
    hzfront hρ0 hRlift hρRlift hU hαβ hβ hα hpreα hzβ hRcont hR hdiff homit
    hchart hbase_shift

end

end Bottcher

namespace Bottcher

noncomputable section

/-- Cusp-infinity obstruction for a subsequence of cross-ratio depths.

This is the based-preimage Schwarz-Pick lift form with an explicit strict depth
sequence `nseq`; it is the cusp branch needed after the punctured-value selector
passes to a subsequence. -/
theorem no_cuspInf_basedPreimage_schwarzPick_modularLift_crossRatio_of_frontier_subseq
    {c α β z₀ : ℂ} {ρ Rlift : ℝ} {U : Set ℂ} {Rseq : ℕ → ℂ → ℂ}
    {τseq : ℕ → UpperHalfPlane} {nseq : ℕ → ℕ}
    (hzfront : z₀ ∈ frontier (filledJulia c)) (hρ0 : 0 < ρ)
    (hRlift : 0 < Rlift) (hρRlift : ρ < Rlift)
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
    (hdiff : ∀ k, DifferentiableOn ℂ (Rseq k) (ball z₀ Rlift))
    (homit : ∀ k z, z ∈ ball z₀ Rlift → Rseq k z ∈ ({0, 1} : Set ℂ)ᶜ)
    (hτ : ∀ k, modularLambda (τseq k : ℂ) = Rseq k z₀)
    (hbase : ∀ M : ℝ, ∀ᶠ k in atTop, M ≤ (τseq k : ℂ).im) : False := by
  have hclosed_sub_ball : closedBall z₀ ρ ⊆ ball z₀ Rlift := by
    intro z hz
    have hzle : dist z z₀ ≤ ρ := by
      simpa [closedBall, dist_comm] using hz
    rw [mem_ball]
    exact lt_of_le_of_lt hzle hρRlift
  have hlift : ∀ k, ∃ g : ℂ → ℂ,
      DifferentiableOn ℂ g (ball z₀ Rlift) ∧
      (∀ z ∈ ball z₀ Rlift, ‖g z‖ < 1) ∧
      g z₀ = cayley (τseq k : ℂ) ∧
      Set.EqOn (fun z => modularLambda (cayleyInv (g z))) (Rseq k) (ball z₀ Rlift) := by
    intro k
    exact omitting_lift_member_based_strict hRlift (Rseq k) (hdiff k) (homit k) (τseq k) (hτ k)
  choose g hgdiff hglt hgbase hgeq using hlift
  have heq : ∀ k, Set.EqOn
      (fun z => stereo (modularLambda (cayleyInv (g k z)))) (fun z => stereo (Rseq k z))
      (closedBall z₀ ρ) := by
    intro k z hz
    exact congrArg stereo (hgeq k (hclosed_sub_ball hz))
  have hbase_g : ∀ M : ℝ, ∀ᶠ k in atTop, M ≤ (cayleyInv (g k z₀)).im := by
    intro M
    filter_upwards [hbase M] with k hk
    have hne : (τseq k : ℂ) + Complex.I ≠ 0 := by
      intro h
      have him : (τseq k : ℂ).im = -1 := by
        rw [show (τseq k : ℂ) = -Complex.I by linear_combination h]
        simp
      linarith [(τseq k).2]
    rw [hgbase k, cayleyInv_cayley hne]
    exact hk
  let A : ℝ := (1 - ρ / Rlift) / (1 + ρ / Rlift)
  have hA : 0 < A := harnackFactor_pos hRlift hρ0.le hρRlift
  have hH : ∀ k z, z ∈ closedBall z₀ ρ →
      A * (cayleyInv (g k z₀)).im ≤ (cayleyInv (g k z)).im := by
    intro k z hz
    exact cayleyInv_im_harnack_closedBall (g := g k) (c := z₀) (ρ := ρ) (R := Rlift)
      hRlift hρ0.le hρRlift (hgdiff k) (hglt k) z hz
  have hIm : ∀ M : ℝ, ∀ᶠ k in atTop, ∀ z ∈ closedBall z₀ ρ,
      M ≤ (cayleyInv (g k z)).im :=
    uniform_im_tendsto_atTop_of_base_im_tendsto_atTop_of_harnack hA hbase_g hH
  have hconv_raw : TendstoUniformlyOn
      (fun k z => stereo (modularLambda (cayleyInv (g k z))))
      (fun _z => stereo (0 : ℂ)) atTop (closedBall z₀ ρ) :=
    tendstoUniformlyOn_stereo_modularLambda_of_im_tendsto_atTop hIm
  have hconv : TendstoUniformlyOn (fun k z => stereo (Rseq k z)) (fun _z => stereo (0 : ℂ))
      atTop (closedBall z₀ ρ) := by
    refine hconv_raw.congr ?_
    filter_upwards with k z hz
    exact heq k hz
  have hGcont : ContinuousOn (fun _z : ℂ => stereo (0 : ℂ)) (closedBall z₀ ρ) :=
    continuous_const.continuousOn
  exact no_spherical_crossRatio_uniform_limit_of_frontier_subseq (R := Rseq) (nseq := nseq)
    hzfront hρ0 hU hαβ hnseq hβ hα hpreα hzβ hR
    ⟨id, fun _z => stereo (0 : ℂ), strictMono_id, hGcont, hconv⟩

end

end Bottcher
namespace Bottcher

noncomputable section

theorem no_cuspZero_basedPreimage_schwarzPick_modularLift_crossRatio_of_frontier_subseq
    {c α β z₀ : ℂ} {ρ Rlift : ℝ} {U : Set ℂ} {Rseq : ℕ → ℂ → ℂ}
    {σseq : ℕ → UpperHalfPlane} {nseq : ℕ → ℕ}
    (hzfront : z₀ ∈ frontier (filledJulia c)) (hρ0 : 0 < ρ)
    (hRlift : 0 < Rlift) (hρRlift : ρ < Rlift)
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
    (hdiff : ∀ k, DifferentiableOn ℂ (Rseq k) (ball z₀ Rlift))
    (homit : ∀ k z, z ∈ ball z₀ Rlift → Rseq k z ∈ ({0, 1} : Set ℂ)ᶜ)
    (hσ : ∀ k, modularLambda (-1 / (σseq k : ℂ)) = Rseq k z₀)
    (hbase : ∀ M : ℝ, ∀ᶠ k in atTop, M ≤ (σseq k : ℂ).im) : False := by
  let Sseq : ℕ → ℂ → ℂ := fun k z => 1 - Rseq k z
  have hclosed_sub_ball : closedBall z₀ ρ ⊆ ball z₀ Rlift := by
    intro z hz
    have hzle : dist z z₀ ≤ ρ := by
      simpa [closedBall, dist_comm] using hz
    rw [mem_ball]
    exact lt_of_le_of_lt hzle hρRlift
  have hSdiff : ∀ k, DifferentiableOn ℂ (Sseq k) (ball z₀ Rlift) := by
    intro k
    exact (differentiableOn_const (c := (1 : ℂ))).sub (hdiff k)
  have hSomit : ∀ k z, z ∈ ball z₀ Rlift → Sseq k z ∈ ({0, 1} : Set ℂ)ᶜ := by
    intro k z hz
    rw [mem_compl_iff]
    intro hbad
    have hRomit := homit k z hz
    rw [mem_compl_iff] at hRomit
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hbad
    rcases hbad with hzero | hone
    · apply hRomit
      rw [Set.mem_insert_iff, Set.mem_singleton_iff]
      right
      exact (sub_eq_zero.mp hzero).symm
    · apply hRomit
      rw [Set.mem_insert_iff, Set.mem_singleton_iff]
      left
      have hneg : -Rseq k z = 0 := by linear_combination hone
      exact neg_eq_zero.mp hneg
  have hSbase : ∀ k, modularLambda (σseq k : ℂ) = Sseq k z₀ := by
    intro k
    have hSrel := modularLambda_S' (τ := (σseq k : ℂ)) (σseq k).2
    calc
      modularLambda (σseq k : ℂ)
          = 1 - modularLambda (-1 / (σseq k : ℂ)) := by linear_combination hSrel
      _ = Sseq k z₀ := by simp [Sseq, hσ k]
  have hlift : ∀ k, ∃ g : ℂ → ℂ,
      DifferentiableOn ℂ g (ball z₀ Rlift) ∧
      (∀ z ∈ ball z₀ Rlift, ‖g z‖ < 1) ∧
      g z₀ = cayley (σseq k : ℂ) ∧
      Set.EqOn (fun z => modularLambda (cayleyInv (g z))) (Sseq k) (ball z₀ Rlift) := by
    intro k
    exact omitting_lift_member_based_strict hRlift (Sseq k) (hSdiff k) (hSomit k) (σseq k)
      (hSbase k)
  choose g hgdiff hglt hgbase hgeq using hlift
  have heq : ∀ k, Set.EqOn
      (fun z => stereo (modularLambda (-1 / cayleyInv (g k z))))
      (fun z => stereo (Rseq k z)) (closedBall z₀ ρ) := by
    intro k z hz
    have hzball : z ∈ ball z₀ Rlift := hclosed_sub_ball hz
    have hgzlt : ‖g k z‖ < 1 := hglt k z hzball
    have hgne : g k z ≠ 1 := by
      intro h
      have hnorm : ‖g k z‖ = 1 := by rw [h, norm_one]
      linarith
    have hτim : 0 < (cayleyInv (g k z)).im := by
      rw [cayleyInv_im_eq_diskPoissonOne hgne]
      exact diskPoissonOne_pos_of_norm_lt_one hgzlt
    have hSrel := modularLambda_S' (τ := cayleyInv (g k z)) hτim
    have hLiftEq : modularLambda (cayleyInv (g k z)) = Sseq k z := hgeq k hzball
    have hval : modularLambda (-1 / cayleyInv (g k z)) = Rseq k z := by
      calc
        modularLambda (-1 / cayleyInv (g k z))
            = 1 - modularLambda (cayleyInv (g k z)) := hSrel
        _ = 1 - Sseq k z := by rw [hLiftEq]
        _ = Rseq k z := by simp [Sseq]
    exact congrArg stereo hval
  have hbase_g : ∀ M : ℝ, ∀ᶠ k in atTop, M ≤ (cayleyInv (g k z₀)).im := by
    intro M
    filter_upwards [hbase M] with k hk
    have hne : (σseq k : ℂ) + Complex.I ≠ 0 := by
      intro h
      have him : (σseq k : ℂ).im = -1 := by
        rw [show (σseq k : ℂ) = -Complex.I by linear_combination h]
        simp
      linarith [(σseq k).2]
    rw [hgbase k, cayleyInv_cayley hne]
    exact hk
  let A : ℝ := (1 - ρ / Rlift) / (1 + ρ / Rlift)
  have hA : 0 < A := harnackFactor_pos hRlift hρ0.le hρRlift
  have hH : ∀ k z, z ∈ closedBall z₀ ρ →
      A * (cayleyInv (g k z₀)).im ≤ (cayleyInv (g k z)).im := by
    intro k z hz
    exact cayleyInv_im_harnack_closedBall (g := g k) (c := z₀) (ρ := ρ) (R := Rlift)
      hRlift hρ0.le hρRlift (hgdiff k) (hglt k) z hz
  have hIm : ∀ M : ℝ, ∀ᶠ k in atTop, ∀ z ∈ closedBall z₀ ρ,
      M ≤ (cayleyInv (g k z)).im :=
    uniform_im_tendsto_atTop_of_base_im_tendsto_atTop_of_harnack hA hbase_g hH
  have hconv_raw : TendstoUniformlyOn
      (fun k z => stereo (modularLambda (-1 / cayleyInv (g k z))))
      (fun _z => stereo (1 : ℂ)) atTop (closedBall z₀ ρ) :=
    tendstoUniformlyOn_stereo_modularLambda_neg_inv_of_im_tendsto_atTop hIm
  have hconv : TendstoUniformlyOn (fun k z => stereo (Rseq k z)) (fun _z => stereo (1 : ℂ))
      atTop (closedBall z₀ ρ) := by
    refine hconv_raw.congr ?_
    filter_upwards with k z hz
    exact heq k hz
  have hGcont : ContinuousOn (fun _z : ℂ => stereo (1 : ℂ)) (closedBall z₀ ρ) :=
    continuous_const.continuousOn
  exact no_spherical_crossRatio_uniform_limit_of_frontier_subseq (R := Rseq) (nseq := nseq)
    hzfront hρ0 hU hαβ hnseq hβ hα hpreα hzβ hR
    ⟨id, fun _z => stereo (1 : ℂ), strictMono_id, hGcont, hconv⟩

end

end Bottcher
namespace Bottcher

noncomputable section

theorem no_cuspOne_basedPreimage_schwarzPick_modularLift_crossRatio_of_frontier_subseq
    {c α β z₀ : ℂ} {ρ Rlift : ℝ} {U : Set ℂ} {Rseq : ℕ → ℂ → ℂ}
    {σseq : ℕ → UpperHalfPlane} {nseq : ℕ → ℕ}
    (hzfront : z₀ ∈ frontier (filledJulia c)) (hρ0 : 0 < ρ)
    (hRlift : 0 < Rlift) (hρRlift : ρ < Rlift)
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
    (hdiff : ∀ k, DifferentiableOn ℂ (Rseq k) (ball z₀ Rlift))
    (homit : ∀ k z, z ∈ ball z₀ Rlift → Rseq k z ∈ ({0, 1} : Set ℂ)ᶜ)
    (hσ : ∀ k, modularLambda (1 - 1 / (σseq k : ℂ)) = Rseq k z₀)
    (hbase : ∀ M : ℝ, ∀ᶠ k in atTop, M ≤ (σseq k : ℂ).im) : False := by
  let Fseq : ℕ → ℂ → ℂ := fun k z => ((1 : ℂ) - Rseq k z)⁻¹
  have hclosed_sub_ball : closedBall z₀ ρ ⊆ ball z₀ Rlift := by
    intro z hz
    have hzle : dist z z₀ ≤ ρ := by
      simpa [closedBall, dist_comm] using hz
    rw [mem_ball]
    exact lt_of_le_of_lt hzle hρRlift
  have hFdiff : ∀ k, DifferentiableOn ℂ (Fseq k) (ball z₀ Rlift) := by
    intro k
    exact ((differentiableOn_const (c := (1 : ℂ))).sub (hdiff k)).inv (by
      intro z hz
      exact sub_ne_zero.mpr (Ne.symm (mem_compl01.mp (homit k z hz)).2))
  have hFomit : ∀ k z, z ∈ ball z₀ Rlift → Fseq k z ∈ ({0, 1} : Set ℂ)ᶜ := by
    intro k z hz
    rw [mem_compl_iff]
    intro hbad
    have hRz := mem_compl01.mp (homit k z hz)
    have hden : (1 : ℂ) - Rseq k z ≠ 0 := sub_ne_zero.mpr (Ne.symm hRz.2)
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hbad
    rcases hbad with hzero | hone
    · exact hden (inv_eq_zero.mp hzero)
    · apply hRz.1
      have hdeneq : (1 : ℂ) - Rseq k z = 1 := inv_eq_one.mp hone
      have hneg : -Rseq k z = 0 := by linear_combination hdeneq
      exact neg_eq_zero.mp hneg
  have hFbase : ∀ k, modularLambda (σseq k : ℂ) = Fseq k z₀ := by
    intro k
    have hσim : 0 < (σseq k : ℂ).im := (σseq k).2
    have hnegim : 0 < (-1 / (σseq k : ℂ)).im := neg_inv_im_pos hσim
    have hSrel := modularLambda_S' (τ := (σseq k : ℂ)) hσim
    have hTrel : modularLambda (1 - 1 / (σseq k : ℂ)) =
        modularLambda (-1 / (σseq k : ℂ)) /
          (modularLambda (-1 / (σseq k : ℂ)) - 1) := by
      rw [show 1 - 1 / (σseq k : ℂ) = -1 / (σseq k : ℂ) + 1 by ring]
      exact modularLambda_T_eq' hnegim
    have hlam0 : modularLambda (σseq k : ℂ) ≠ 0 := (modularLambda_omits_zero_one' hσim).1
    have hRformula : Rseq k z₀ = 1 - (modularLambda (σseq k : ℂ))⁻¹ := by
      rw [← hσ k, hTrel, hSrel]
      field_simp [hlam0]
      ring
    change modularLambda (σseq k : ℂ) = ((1 : ℂ) - Rseq k z₀)⁻¹
    rw [hRformula]
    field_simp [hlam0]
    ring
  have hlift : ∀ k, ∃ g : ℂ → ℂ,
      DifferentiableOn ℂ g (ball z₀ Rlift) ∧
      (∀ z ∈ ball z₀ Rlift, ‖g z‖ < 1) ∧
      g z₀ = cayley (σseq k : ℂ) ∧
      Set.EqOn (fun z => modularLambda (cayleyInv (g z))) (Fseq k) (ball z₀ Rlift) := by
    intro k
    exact omitting_lift_member_based_strict hRlift (Fseq k) (hFdiff k) (hFomit k) (σseq k)
      (hFbase k)
  choose g hgdiff hglt hgbase hgeq using hlift
  have heq : ∀ k, Set.EqOn
      (fun z => stereo (modularLambda (1 - 1 / cayleyInv (g k z))))
      (fun z => stereo (Rseq k z)) (closedBall z₀ ρ) := by
    intro k z hz
    have hzball : z ∈ ball z₀ Rlift := hclosed_sub_ball hz
    have hgzlt : ‖g k z‖ < 1 := hglt k z hzball
    have hgne : g k z ≠ 1 := by
      intro h
      have hnorm : ‖g k z‖ = 1 := by rw [h, norm_one]
      linarith
    have hτim : 0 < (cayleyInv (g k z)).im := by
      rw [cayleyInv_im_eq_diskPoissonOne hgne]
      exact diskPoissonOne_pos_of_norm_lt_one hgzlt
    have hnegim : 0 < (-1 / cayleyInv (g k z)).im := neg_inv_im_pos hτim
    have hSrel := modularLambda_S' (τ := cayleyInv (g k z)) hτim
    have hTrel : modularLambda (1 - 1 / cayleyInv (g k z)) =
        modularLambda (-1 / cayleyInv (g k z)) /
          (modularLambda (-1 / cayleyInv (g k z)) - 1) := by
      rw [show 1 - 1 / cayleyInv (g k z) = -1 / cayleyInv (g k z) + 1 by ring]
      exact modularLambda_T_eq' hnegim
    have hLiftEq : modularLambda (cayleyInv (g k z)) = Fseq k z := hgeq k hzball
    have hRz := mem_compl01.mp (homit k z hzball)
    have hden : (1 : ℂ) - Rseq k z ≠ 0 := sub_ne_zero.mpr (Ne.symm hRz.2)
    have hval : modularLambda (1 - 1 / cayleyInv (g k z)) = Rseq k z := by
      rw [hTrel, hSrel, hLiftEq]
      change (1 - ((1 : ℂ) - Rseq k z)⁻¹) /
          ((1 - ((1 : ℂ) - Rseq k z)⁻¹) - 1) = Rseq k z
      field_simp [hden]
      ring
    exact congrArg stereo hval
  have hbase_g : ∀ M : ℝ, ∀ᶠ k in atTop, M ≤ (cayleyInv (g k z₀)).im := by
    intro M
    filter_upwards [hbase M] with k hk
    have hne : (σseq k : ℂ) + Complex.I ≠ 0 := by
      intro h
      have him : (σseq k : ℂ).im = -1 := by
        rw [show (σseq k : ℂ) = -Complex.I by linear_combination h]
        simp
      linarith [(σseq k).2]
    rw [hgbase k, cayleyInv_cayley hne]
    exact hk
  let A : ℝ := (1 - ρ / Rlift) / (1 + ρ / Rlift)
  have hA : 0 < A := harnackFactor_pos hRlift hρ0.le hρRlift
  have hH : ∀ k z, z ∈ closedBall z₀ ρ →
      A * (cayleyInv (g k z₀)).im ≤ (cayleyInv (g k z)).im := by
    intro k z hz
    exact cayleyInv_im_harnack_closedBall (g := g k) (c := z₀) (ρ := ρ) (R := Rlift)
      hRlift hρ0.le hρRlift (hgdiff k) (hglt k) z hz
  have hIm : ∀ M : ℝ, ∀ᶠ k in atTop, ∀ z ∈ closedBall z₀ ρ,
      M ≤ (cayleyInv (g k z)).im :=
    uniform_im_tendsto_atTop_of_base_im_tendsto_atTop_of_harnack hA hbase_g hH
  have hconv_raw : TendstoUniformlyOn
      (fun k z => stereo (modularLambda (1 - 1 / cayleyInv (g k z))))
      (fun _z => northPole) atTop (closedBall z₀ ρ) :=
    tendstoUniformlyOn_stereo_modularLambda_one_sub_inv_of_im_tendsto_atTop hIm
  have hconv : TendstoUniformlyOn (fun k z => stereo (Rseq k z)) (fun _z => northPole)
      atTop (closedBall z₀ ρ) := by
    refine hconv_raw.congr ?_
    filter_upwards with k z hz
    exact heq k hz
  have hGcont : ContinuousOn (fun _z : ℂ => northPole) (closedBall z₀ ρ) :=
    continuous_const.continuousOn
  exact no_spherical_crossRatio_uniform_limit_of_frontier_subseq (R := Rseq) (nseq := nseq)
    hzfront hρ0 hU hαβ hnseq hβ hα hpreα hzβ hR
    ⟨id, fun _z => northPole, strictMono_id, hGcont, hconv⟩

end

end Bottcher

namespace Bottcher

noncomputable section

/-- Subsequence form of the cusp-`∞` `T`-shift branch. -/
theorem no_cuspInf_addOne_basedPreimage_schwarzPick_modularLift_crossRatio_of_frontier_subseq
    {c α β z₀ : ℂ} {ρ Rlift : ℝ} {U : Set ℂ} {Rseq : ℕ → ℂ → ℂ}
    {σseq : ℕ → UpperHalfPlane} {nseq : ℕ → ℕ}
    (hzfront : z₀ ∈ frontier (filledJulia c)) (hρ0 : 0 < ρ)
    (hRlift : 0 < Rlift) (hρRlift : ρ < Rlift)
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
    (hdiff : ∀ k, DifferentiableOn ℂ (Rseq k) (ball z₀ Rlift))
    (homit : ∀ k z, z ∈ ball z₀ Rlift → Rseq k z ∈ ({0, 1} : Set ℂ)ᶜ)
    (hσ : ∀ k, modularLambda ((σseq k : ℂ) + 1) = Rseq k z₀)
    (hbase : ∀ M : ℝ, ∀ᶠ k in atTop, M ≤ (σseq k : ℂ).im) : False := by
  let τseq : ℕ → UpperHalfPlane := fun k =>
    ⟨(σseq k : ℂ) + 1, by simpa [Complex.add_im] using (σseq k).2⟩
  have hτ : ∀ k, modularLambda (τseq k : ℂ) = Rseq k z₀ := by
    intro k
    simpa [τseq] using hσ k
  have hbaseτ : ∀ M : ℝ, ∀ᶠ k in atTop, M ≤ (τseq k : ℂ).im := by
    intro M
    filter_upwards [hbase M] with k hk
    simpa [τseq, Complex.add_im] using hk
  exact no_cuspInf_basedPreimage_schwarzPick_modularLift_crossRatio_of_frontier_subseq
    (τseq := τseq) (nseq := nseq) hzfront hρ0 hRlift hρRlift hnseq hU hαβ hβ
    hα hpreα hzβ hR hdiff homit hτ hbaseτ

/-- Subsequence form of the cusp-`0` `S*T`-shift branch. -/
theorem no_cuspZero_addOne_basedPreimage_schwarzPick_modularLift_crossRatio_of_frontier_subseq
    {c α β z₀ : ℂ} {ρ Rlift : ℝ} {U : Set ℂ} {Rseq : ℕ → ℂ → ℂ}
    {σseq : ℕ → UpperHalfPlane} {nseq : ℕ → ℕ}
    (hzfront : z₀ ∈ frontier (filledJulia c)) (hρ0 : 0 < ρ)
    (hRlift : 0 < Rlift) (hρRlift : ρ < Rlift)
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
    (hdiff : ∀ k, DifferentiableOn ℂ (Rseq k) (ball z₀ Rlift))
    (homit : ∀ k z, z ∈ ball z₀ Rlift → Rseq k z ∈ ({0, 1} : Set ℂ)ᶜ)
    (hσ : ∀ k, modularLambda (-1 / ((σseq k : ℂ) + 1)) = Rseq k z₀)
    (hbase : ∀ M : ℝ, ∀ᶠ k in atTop, M ≤ (σseq k : ℂ).im) : False := by
  let σshift : ℕ → UpperHalfPlane := fun k =>
    ⟨(σseq k : ℂ) + 1, by simpa [Complex.add_im] using (σseq k).2⟩
  have hσshift : ∀ k, modularLambda (-1 / (σshift k : ℂ)) = Rseq k z₀ := by
    intro k
    simpa [σshift] using hσ k
  have hbase_shift : ∀ M : ℝ, ∀ᶠ k in atTop, M ≤ (σshift k : ℂ).im := by
    intro M
    filter_upwards [hbase M] with k hk
    simpa [σshift, Complex.add_im] using hk
  exact no_cuspZero_basedPreimage_schwarzPick_modularLift_crossRatio_of_frontier_subseq
    (σseq := σshift) (nseq := nseq) hzfront hρ0 hRlift hρRlift hnseq hU hαβ hβ
    hα hpreα hzβ hR hdiff homit hσshift hbase_shift

/-- Subsequence form of the reciprocal cusp-`1` anharmonic branch. -/
theorem no_cuspOne_reciprocal_basedPreimage_schwarzPick_modularLift_crossRatio_of_frontier_subseq
    {c α β z₀ : ℂ} {ρ Rlift : ℝ} {U : Set ℂ} {Rseq : ℕ → ℂ → ℂ}
    {σseq : ℕ → UpperHalfPlane} {nseq : ℕ → ℕ}
    (hzfront : z₀ ∈ frontier (filledJulia c)) (hρ0 : 0 < ρ)
    (hRlift : 0 < Rlift) (hρRlift : ρ < Rlift)
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
    (hdiff : ∀ k, DifferentiableOn ℂ (Rseq k) (ball z₀ Rlift))
    (homit : ∀ k z, z ∈ ball z₀ Rlift → Rseq k z ∈ ({0, 1} : Set ℂ)ᶜ)
    (hσ : ∀ k, (modularLambda (σseq k : ℂ))⁻¹ = Rseq k z₀)
    (hbase : ∀ M : ℝ, ∀ᶠ k in atTop, M ≤ (σseq k : ℂ).im) : False := by
  let σshift : ℕ → UpperHalfPlane := fun k =>
    ⟨(σseq k : ℂ) - 1, by simpa [Complex.sub_im] using (σseq k).2⟩
  have hchart : ∀ k, modularLambda (1 - 1 / (σshift k : ℂ)) = Rseq k z₀ := by
    intro k
    let σ : ℂ := (σseq k : ℂ)
    have hσim : 0 < σ.im := (σseq k).2
    have hσ0 : σ ≠ 0 := by
      intro h
      have : σ.im = 0 := by rw [h]; simp
      linarith
    have hσ1 : σ - 1 ≠ 0 := by
      intro h
      have : σ = 1 := sub_eq_zero.mp h
      have him : σ.im = 0 := by rw [this]; simp
      linarith
    have hnegim : 0 < (-1 / σ).im := neg_inv_im_pos hσim
    have hu0 : -1 / σ + 1 ≠ 0 := by
      intro h
      have hσeq : σ = 1 := by
        field_simp [hσ0] at h
        linear_combination h
      have him : σ.im = 0 := by rw [hσeq]; simp
      linarith
    have huim : 0 < (-1 / σ + 1).im := by
      simpa [Complex.add_im] using hnegim
    have hσ1' : -1 + σ ≠ 0 := by
      intro h
      apply hσ1
      linear_combination h
    have harg : 1 - 1 / (σ - 1) = -1 / (-1 / σ + 1) + 2 := by
      field_simp [hσ0, hσ1, hσ1', hu0]
      ring_nf
    have hSouter := modularLambda_S' (τ := -1 / σ + 1) huim
    have hTinner := modularLambda_T_eq' (τ := -1 / σ) hnegim
    have hSinner := modularLambda_S' (τ := σ) hσim
    have hlam0 : modularLambda σ ≠ 0 := (modularLambda_omits_zero_one' hσim).1
    change modularLambda (1 - 1 / (σ - 1)) = Rseq k z₀
    calc
      modularLambda (1 - 1 / (σ - 1))
          = modularLambda (-1 / (-1 / σ + 1) + 2) := by rw [harg]
      _ = modularLambda (-1 / (-1 / σ + 1)) := modularLambda_add_two _
      _ = 1 - modularLambda (-1 / σ + 1) := hSouter
      _ = 1 - modularLambda (-1 / σ) / (modularLambda (-1 / σ) - 1) := by rw [hTinner]
      _ = 1 - (1 - modularLambda σ) / ((1 - modularLambda σ) - 1) := by rw [hSinner]
      _ = (modularLambda σ)⁻¹ := by
        field_simp [hlam0]
        ring
      _ = Rseq k z₀ := hσ k
  have hbase_shift : ∀ M : ℝ, ∀ᶠ k in atTop, M ≤ (σshift k : ℂ).im := by
    intro M
    filter_upwards [hbase M] with k hk
    simpa [σshift, Complex.sub_im] using hk
  exact no_cuspOne_basedPreimage_schwarzPick_modularLift_crossRatio_of_frontier_subseq
    (σseq := σshift) (nseq := nseq) hzfront hρ0 hRlift hρRlift hnseq hU hαβ hβ
    hα hpreα hzβ hR hdiff homit hchart hbase_shift

end

end Bottcher
