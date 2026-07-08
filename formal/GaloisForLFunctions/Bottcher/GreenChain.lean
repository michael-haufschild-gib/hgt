/-
# Böttcher tower — chain gluing of green-conjugate branches (Brick B core)

The single-valued connected-case Böttcher coordinate `φ_c` is built by gluing the per-level branches
(`PhiLevel`) along a chain of domains. The atomic glue is `exists_greenConjugate_glue` (two analytic
branches with `Re = G_c` and a connected overlap → one branch on the union). This file iterates it:
given a sequence `U₀, U₁, …` of opens each carrying a local conjugate `Fᵢ` (`Re Fᵢ = G_c`), with each
running-union meeting the next domain in a **connected** overlap, there is a single analytic conjugate
`F` on the whole union `⋃ⱼ Uⱼ`. Then `exp F` is the single-valued `φ_c` on that union.

The overlap-connectedness rides as an explicit geometric hypothesis (the input that the level/path
geometry supplies). New file (hRigid connected lane); consumes `CoverConstruction`.
-/
import GaloisForLFunctions.Bottcher.CoverConstruction
import GaloisForLFunctions.Bottcher.ChainGlue

open Set

namespace Bottcher

/-- **Chain gluing of green-conjugate branches.** Local conjugates `Fᵢ` on opens `Uᵢ`
(`Re Fᵢ = G_c`), with each prefix-union meeting `U₍ᵢ₊₁₎` in a connected overlap, glue into a single
analytic conjugate on `⋃_{j ≤ k} Uⱼ`. Iterates `exists_greenConjugate_glue` by induction on `k`. -/
theorem exists_greenConjugate_glue_chain {c : ℂ} (U : ℕ → Set ℂ) (F : ℕ → ℂ → ℂ)
    (hUo : ∀ i, IsOpen (U i))
    (hF : ∀ i, AnalyticOnNhd ℂ (F i) (U i))
    (hFre : ∀ i, EqOn (fun w => (F i w).re) (greenLimit c) (U i))
    (hconn : ∀ i, IsConnected ((⋃ j ∈ Finset.range (i + 1), U j) ∩ U (i + 1)))
    (k : ℕ) :
    ∃ G : ℂ → ℂ, AnalyticOnNhd ℂ G (⋃ j ∈ Finset.range (k + 1), U j) ∧
      EqOn (fun w => (G w).re) (greenLimit c) (⋃ j ∈ Finset.range (k + 1), U j) :=
  exists_glue_chain
    (P := fun G V => AnalyticOnNhd ℂ G V ∧ EqOn (fun w => (G w).re) (greenLimit c) V)
    U F hUo (fun i => ⟨hF i, hFre i⟩)
    (fun hV hW hc pf ph => exists_greenConjugate_glue hV hW hc pf.1 ph.1 pf.2 ph.2) hconn k

/-- **The single-valued Böttcher coordinate on a glued chain.** `exp F` for the chain conjugate `F`
is analytic, nowhere zero, with `|exp F| = exp(G_c)`, on `⋃_{j ≤ k} Uⱼ`. -/
theorem exists_bottcher_on_chain {c : ℂ} (U : ℕ → Set ℂ) (F : ℕ → ℂ → ℂ)
    (hUo : ∀ i, IsOpen (U i))
    (hF : ∀ i, AnalyticOnNhd ℂ (F i) (U i))
    (hFre : ∀ i, EqOn (fun w => (F i w).re) (greenLimit c) (U i))
    (hconn : ∀ i, IsConnected ((⋃ j ∈ Finset.range (i + 1), U j) ∩ U (i + 1)))
    (k : ℕ) :
    ∃ β : ℂ → ℂ, AnalyticOnNhd ℂ β (⋃ j ∈ Finset.range (k + 1), U j) ∧
      (∀ z ∈ (⋃ j ∈ Finset.range (k + 1), U j), β z ≠ 0) ∧
      (∀ z ∈ (⋃ j ∈ Finset.range (k + 1), U j), ‖β z‖ = Real.exp (greenLimit c z)) := by
  obtain ⟨G, hGan, hGre⟩ := exists_greenConjugate_glue_chain U F hUo hF hFre hconn k
  refine ⟨fun z => Complex.exp (G z), hGan.cexp, fun z _ => Complex.exp_ne_zero _, fun z hz => ?_⟩
  rw [Complex.norm_exp]
  exact congrArg Real.exp (hGre hz)

end Bottcher
