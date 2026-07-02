/-
# q62 on the genuine carrier, from monodromy + tip + rigidity — and the first real pair

Two capstones.  `q62_phiMero_independence_of_monodromy_tip_rigidity` instantiates the conditional
q62 with the genuine Mandelbrot placement `Disc c = c ∉ M`: the connected-side transcendence
inputs are discharged **unconditionally** (`phiMero_transcendental_of_mem_mandelbrot`), the
both-connected input by `HoleFreeTip × SmoothPieceRigidity` (`HbothconnAssembly`), leaving the
Cantor monodromy Props as the disconnected lane's named remainder.

`q62_phiMero_independence_real_pair` then feeds the answered OP4 class: for real
`−2 < c₂ < c₁ < 0` both parameters are in `M ∖ {0,−2}` (`real_mem_mandelbrot`), the monodromy
Props are vacuous, and the hole-free tip comes from the Schoenflies collar at `imagTip c₁`
(`holeFreeTip_of_collar`).  The pair statement is thereby conditional on exactly TWO Props:
the collar (#124) and the rigidity (#118).  Axiom-clean.
-/
import GaloisForLFunctions.Bottcher.Q62PhiMeroConditional
import GaloisForLFunctions.Bottcher.HbothconnAssembly
import GaloisForLFunctions.Bottcher.ConnectedTranscendenceUnconditional
import GaloisForLFunctions.Bottcher.ImaginaryAxisTip

open Polynomial Set Metric

namespace Bottcher

/-- **q62 with the genuine Mandelbrot placement.**  Connected-side transcendence is discharged
outright; the both-connected case needs a hole-free tip and the rigidity Prop; disconnected
parameters contribute their Cantor-basin monodromy Props. -/
theorem q62_phiMero_independence_of_monodromy_tip_rigidity
    {U : Set ℂ} (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hc₁0 : c₁ ≠ 0) (hc₁2 : c₁ ≠ -2) (hc₂0 : c₂ ≠ 0) (hc₂2 : c₂ ≠ -2)
    (hmono₁ : c₁ ∉ mandelbrot →
      haveI := isDomain_analyticSubring U hUo hUc hUne
      letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
      ∀ d : ℕ, ∃ (σ : meroField U ≃ₐ[RatFunc ℂ] meroField U) (ζ : meroField U) (m : ℕ),
        d < m ∧ orderOf ζ = m ∧ σ (phiMero c₂ hU₂) = phiMero c₂ hU₂ ∧ σ ζ = ζ ∧
        σ (phiMero c₁ hU₁) = ζ * phiMero c₁ hU₁)
    (hmono₂ : c₂ ∉ mandelbrot →
      haveI := isDomain_analyticSubring U hUo hUc hUne
      letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
      ∀ d : ℕ, ∃ (σ : meroField U ≃ₐ[RatFunc ℂ] meroField U) (ζ : meroField U) (m : ℕ),
        d < m ∧ orderOf ζ = m ∧ σ (phiMero c₁ hU₁) = phiMero c₁ hU₁ ∧ σ ζ = ζ ∧
        σ (phiMero c₂ hU₂) = ζ * phiMero c₂ hU₂)
    (htip : c₁ ∈ mandelbrot → c₂ ∈ mandelbrot →
      ∃ (z₀ : ℂ) (r : ℝ), HoleFreeTip c₁ c₂ z₀ r)
    (hrig : c₁ ∈ mandelbrot → c₂ ∈ mandelbrot → SmoothPieceRigidity c₁ c₂) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  refine q62_phiMero_independence_conditional hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂
    (fun c => c ∉ mandelbrot) hmono₁ hmono₂ ?_ ?_ ?_
  · intro h1
    exact phiMero_transcendental_of_mem_mandelbrot hUo hUc hUne hUinf
      (not_not.mp h1) hc₁0 hc₁2 hU₁
  · intro h2
    exact phiMero_transcendental_of_mem_mandelbrot hUo hUc hUne hUinf
      (not_not.mp h2) hc₂0 hc₂2 hU₂
  · intro h1 h2
    obtain ⟨z₀, r, htip'⟩ := htip (not_not.mp h1) (not_not.mp h2)
    exact noRelation_phiMero_of_holeFreeTip_of_rigidity hUo hUc hUne hUinf
      (not_not.mp h1) (not_not.mp h2) hU₁ hU₂
      (phiMero_transcendental_of_mem_mandelbrot hUo hUc hUne hUinf
        (not_not.mp h2) hc₂0 hc₂2 hU₂)
      htip' (hrig (not_not.mp h1) (not_not.mp h2))

/-- **The first concrete nonexceptional pair class (OP4, answered): real `−2 < c₂ < c₁ < 0`.**
Both parameters are connected and nonexceptional; the tip is the explicit `imagTip c₁`; the pair
independence is conditional on exactly TWO named Props — the Schoenflies exterior collar at the
tip (the 04-answer's topological input, epic #124) and the smooth-piece rigidity (epic #118). -/
theorem q62_phiMero_independence_real_pair
    {U : Set ℂ} (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    {c₁ c₂ : ℝ} (h2 : -2 < c₂) (hlt : c₂ < c₁) (h1 : c₁ < 0)
    (hU₁ : U ⊆ escapeOpen (c₁ : ℂ)) (hU₂ : U ⊆ escapeOpen (c₂ : ℂ))
    (hcollar : ∀ ρ > 0, ∃ Uc : Set ℂ, IsOpen Uc ∧ imagTip c₁ ∈ Uc ∧
      Uc ⊆ Metric.ball (imagTip c₁) ρ ∧ IsPreconnected (Uc \ filledJulia (c₁ : ℂ)))
    (hrig : SmoothPieceRigidity (c₁ : ℂ) (c₂ : ℂ)) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero (c₁ : ℂ) hU₁) (phiMero (c₂ : ℂ) hU₂) := by
  have h1M : (c₁ : ℂ) ∈ mandelbrot := real_mem_mandelbrot (by linarith) (by linarith)
  have h2M : (c₂ : ℂ) ∈ mandelbrot := real_mem_mandelbrot (by linarith) (by linarith)
  refine q62_phiMero_independence_of_monodromy_tip_rigidity hUo hUc hUne hUinf
    (c₁ : ℂ) (c₂ : ℂ) hU₁ hU₂ ?_ ?_ ?_ ?_
    (fun h => absurd h1M h) (fun h => absurd h2M h) ?_ (fun _ _ => hrig)
  · intro h
    have : c₁ = 0 := by exact_mod_cast h
    linarith
  · intro h
    have : c₁ = -2 := by exact_mod_cast h
    linarith
  · intro h
    have : c₂ = 0 := by exact_mod_cast h
    linarith
  · intro h
    have : c₂ = -2 := by exact_mod_cast h
    linarith
  · intro _ _
    obtain ⟨r, hr⟩ := holeFreeTip_of_collar (le_of_lt h2) hlt h1.le hcollar
    exact ⟨imagTip c₁, r, hr⟩

end Bottcher
