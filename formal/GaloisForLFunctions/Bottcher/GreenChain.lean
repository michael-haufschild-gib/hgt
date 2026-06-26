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
      EqOn (fun w => (G w).re) (greenLimit c) (⋃ j ∈ Finset.range (k + 1), U j) := by
  induction k with
  | zero =>
    refine ⟨F 0, ?_, ?_⟩
    · simpa [Finset.range_one] using hF 0
    · simpa [Finset.range_one] using hFre 0
  | succ n ih =>
    obtain ⟨G, hGan, hGre⟩ := ih
    have hVopen : IsOpen (⋃ j ∈ Finset.range (n + 1), U j) := isOpen_biUnion (fun j _ => hUo j)
    obtain ⟨H, hHan, hHre⟩ :=
      exists_greenConjugate_glue hVopen (hUo (n + 1)) (hconn n) hGan (hF (n + 1)) hGre (hFre (n + 1))
    have hunion : (⋃ j ∈ Finset.range (n + 1 + 1), U j)
        = (⋃ j ∈ Finset.range (n + 1), U j) ∪ U (n + 1) := by
      rw [Finset.range_add_one, Finset.set_biUnion_insert]
      exact Set.union_comm _ _
    refine ⟨H, ?_, ?_⟩
    · rw [hunion]; exact hHan
    · rw [hunion]; exact hHre

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
