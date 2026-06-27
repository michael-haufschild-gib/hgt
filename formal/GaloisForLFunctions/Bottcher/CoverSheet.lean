/-
# A sheet of the connected dyadic cover: `bc`-coordinate + single-valued `z`-projection

A sheet of the cover is a domain on which BOTH the Böttcher coordinate `bc` (the cover coordinate) and
the `z`-projection `p₀` (a single-valued inverse of `f^[k]∘…`) are single-valued.  `CoverChart` builds the
`bc`-coordinate side (`bc` univalent ⇒ analytic inverse `ψbc`); `CoverSection` builds the projection side
(`f^[k]` injective ⇒ analytic inverse `ιf`).  This file assembles them: the composite `p₀ = ιf∘ψbc`
sections the cover coordinate `ι = bc∘f^[k] = φc₁^{2^k}` (`p₀∘ι = id`).  That `p₀∘ι = z` is exactly the
hypothesis `noRelation_of_precompMap` / `ratfuncToMeroVia` need to make the Kummer descent `ℂ(z)`-linear.
Axiom-clean.
-/
import GaloisForLFunctions.Bottcher.CoverSection
import GaloisForLFunctions.Bottcher.CoverChart

open Set Filter Topology

namespace Bottcher

/-- **Cover-sheet section: the single-valued `z`-projection `p₀` of a dyadic cover sheet.**  Given a deep
domain `A` on which `f^[k]` is injective and critical-free, and a shallower domain `B ⊇ f^[k](A)` with
`B ⊆ escapeOpen` on which `bc` is univalent, the two inverse charts assemble into an analytic
`p₀ = ιf∘ψbc` with `p₀(bc(f^[k] z)) = z` on `A`.  This is the single-valued `z`-projection of the cover
sheet `A` (`p₀∘ι = id` for the cover coordinate `ι = bc∘f^[k] = φc₁^{2^k}`) — the datum
`noRelation_of_precompMap` consumes, built from `CoverChart` (the `bc`-univalent chart `ψbc`) and
`CoverSection` (the `f^[k]`-injective section `ιf`).  Only a concrete such `(A, B)` and the global gluing
of sheets remain to feed the DONE Kummer close (`q62_disconnected_kummer`). -/
theorem exists_coverSheet_section {c : ℂ} (k : ℕ) {A B : Set ℂ}
    (hAo : IsOpen A) (hAcrit : ∀ z ∈ A, (∏ j ∈ Finset.range k, 2 * (quadratic c)^[j] z) ≠ 0)
    (hAinj : Set.InjOn ((quadratic c)^[k]) A)
    (hBo : IsOpen B) (hBsub : B ⊆ escapeOpen c) (hBinj : Set.InjOn (bottcherCoord c) B)
    (hAB : ∀ z ∈ A, (quadratic c)^[k] z ∈ B) :
    ∃ p₀ : ℂ → ℂ, ∀ z ∈ A, p₀ (bottcherCoord c ((quadratic c)^[k] z)) = z := by
  obtain ⟨ιf, hιf, _, _⟩ := exists_analytic_inverse_iterate_of_injOn c k hAo hAcrit hAinj
  obtain ⟨ψbc, hψbc, _, _⟩ := exists_analytic_inverse_bottcher_of_injOn hBo hBsub hBinj
  exact ⟨ιf ∘ ψbc, deep_section_composition k hψbc hιf hAB⟩

/-- **Analytic cover-sheet section.**  Strengthens `exists_coverSheet_section`: the projection
`p₀ = ιf∘ψbc` is not only a left inverse of the cover coordinate `ι = bc∘f^[k]` (`p₀(bc(f^[k] z)) = z`)
but is ANALYTIC at every cover-coordinate value `bc(f^[k] z)` (`z ∈ A`).  `ψbc` is analytic at
`bc(f^[k] z)` (since `f^[k] z ∈ B`), and `ιf` is analytic at `ψbc(bc(f^[k] z)) = f^[k] z` (since
`z ∈ A`); the composite is analytic by the chain rule.  So `p₀` is a genuine analytic germ on the
cover — the `meroField`-level projection `noRelation_of_precompMap` / `ratfuncToMeroVia p₀` consume to
make the Kummer descent `ℂ(z)`-linear.  This is the analyticity the bare `exists_coverSheet_section`
left implicit: the section is not merely a set-theoretic left inverse but a holomorphic chart. -/
theorem exists_coverSheet_section_analytic {c : ℂ} (k : ℕ) {A B : Set ℂ}
    (hAo : IsOpen A) (hAcrit : ∀ z ∈ A, (∏ j ∈ Finset.range k, 2 * (quadratic c)^[j] z) ≠ 0)
    (hAinj : Set.InjOn ((quadratic c)^[k]) A)
    (hBo : IsOpen B) (hBsub : B ⊆ escapeOpen c) (hBinj : Set.InjOn (bottcherCoord c) B)
    (hAB : ∀ z ∈ A, (quadratic c)^[k] z ∈ B) :
    ∃ p₀ : ℂ → ℂ, (∀ z ∈ A, p₀ (bottcherCoord c ((quadratic c)^[k] z)) = z) ∧
      (∀ z ∈ A, AnalyticAt ℂ p₀ (bottcherCoord c ((quadratic c)^[k] z))) := by
  obtain ⟨ιf, hιf, hιf_an, _⟩ := exists_analytic_inverse_iterate_of_injOn c k hAo hAcrit hAinj
  obtain ⟨ψbc, hψbc, hψbc_an, _⟩ := exists_analytic_inverse_bottcher_of_injOn hBo hBsub hBinj
  refine ⟨ιf ∘ ψbc, deep_section_composition k hψbc hιf hAB, ?_⟩
  intro z hz
  have hψat : AnalyticAt ℂ ψbc (bottcherCoord c ((quadratic c)^[k] z)) :=
    hψbc_an ((quadratic c)^[k] z) (hAB z hz)
  have hιat : AnalyticAt ℂ ιf (ψbc (bottcherCoord c ((quadratic c)^[k] z))) := by
    rw [hψbc ((quadratic c)^[k] z) (hAB z hz)]
    exact hιf_an z hz
  exact hιat.comp hψat

end Bottcher

namespace Bottcher
open Set Filter Topology

/-- **The cover coordinate `ι = bc∘f^[k]` is injective on a sheet.**  If `f^[k]` is injective on `A` and
`bc` is injective on `f^[k](A)`, then `z ↦ bc(f^[k] z)` is injective on `A`: the cover sheet `A` embeds
into value space via the cover coordinate `ι = bc∘f^[k] = φc₁^{2^k}`.  With `exists_coverSheet_section`
(the section `p₀` left-inverting `ι`), `ι : A → ι(A)` is a bijection — the sheet's identification with its
value image, on which `bc` is the single-valued cover coordinate.  (`exists_coverSheet_section`'s
`p₀∘ι = id` is precisely the `hp0ι` projection hypothesis of `noRelation_of_precompMap`, with
`ι = bc∘f^[k]` and `V = deepBall`.) -/
theorem bottcherIterate_injOn {c : ℂ} (k : ℕ) {A : Set ℂ}
    (hAinj : Set.InjOn ((quadratic c)^[k]) A)
    (hbcinj : Set.InjOn (bottcherCoord c) ((quadratic c)^[k] '' A)) :
    Set.InjOn (fun z => bottcherCoord c ((quadratic c)^[k] z)) A := by
  intro x hx y hy hxy
  exact hAinj hx hy (hbcinj (mem_image_of_mem _ hx) (mem_image_of_mem _ hy) hxy)

end Bottcher
