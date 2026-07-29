/-
# General cover chart: `bc` uniformizes any univalent escape subdomain

The connected dyadic cover the disconnected close needs (`noRelation_of_precompMap` consumes it) has
`bc = φ̃c` as its single-valued coordinate.  Its charts are the domains on which `bc` is injective:
there `bc : A → bc(A)` is a biholomorphism with analytic inverse `ψ` (the section / the `w ↦ phiMero`
descent).  `FarFieldUnivalence.exists_analytic_inverse_far` builds this chart on the far field
`{|z|>R}`; this file generalizes it to **every** open univalent escape subdomain `A`, the chart atlas
the cover is glued from (via `CoverChainGlue`).  Axiom-clean.
-/
import GaloisForLFunctions.Bottcher.FarFieldUnivalence
import GaloisForLFunctions.Bottcher.CoverConstruction

open Set Filter Topology

namespace Bottcher

/-- **General cover chart: `bc` is a biholomorphism onto its image on any univalent escape subdomain.**
For an open `A ⊆ escapeOpen c` on which `bottcherCoord c` is injective, the set-theoretic inverse
`ψ = invFunOn (bc) A` is analytic at every `bc z` (`z ∈ A`), left-inverts `bc` on `A`, and is a local
right inverse — so `bc : A → bc(A)` is a biholomorphism.  Same argument as the far-field chart
(`exists_analytic_inverse_far`, via `exists_localInverse_bottcherCoord` + `invFunOn`), now for an
arbitrary univalent domain.  These are the charts of the connected dyadic cover: glued along the basin
they realize `bc` as the uniformizing coordinate of the cover that the disconnected Kummer close needs. -/
theorem exists_analytic_inverse_bottcher_of_injOn {c : ℂ} {A : Set ℂ}
    (hAo : IsOpen A) (hAsub : A ⊆ escapeOpen c) (hinj : Set.InjOn (bottcherCoord c) A) :
    ∃ ψ : ℂ → ℂ,
      (∀ z ∈ A, ψ (bottcherCoord c z) = z) ∧
      (∀ z ∈ A, AnalyticAt ℂ ψ (bottcherCoord c z)) ∧
      (∀ z ∈ A, ∀ᶠ w in 𝓝 (bottcherCoord c z), bottcherCoord c (ψ w) = w) := by
  classical
  set ψ : ℂ → ℂ := Function.invFunOn (bottcherCoord c) A with hψdef
  have hleft : ∀ z ∈ A, ψ (bottcherCoord c z) = z := fun z hz => hinj.leftInvOn_invFunOn hz
  refine ⟨ψ, hleft, ?_, ?_⟩
  · intro z₀ hz₀
    obtain ⟨loc, hlocAn, hlocLeft, hlocRight⟩ := exists_localInverse_bottcherCoord (hAsub hz₀)
    have hlocAtz₀ : loc (bottcherCoord c z₀) = z₀ := hlocLeft.self_of_nhds
    have hlocInA : ∀ᶠ w in 𝓝 (bottcherCoord c z₀), loc w ∈ A :=
      hlocAn.continuousAt.preimage_mem_nhds (by rw [hlocAtz₀]; exact hAo.mem_nhds hz₀)
    have hagree : ψ =ᶠ[𝓝 (bottcherCoord c z₀)] loc := by
      filter_upwards [hlocInA, hlocRight] with w hwA hwRight
      have hex : ∃ a ∈ A, bottcherCoord c a = w := ⟨loc w, hwA, hwRight⟩
      exact hinj (Function.invFunOn_mem hex) hwA (by rw [Function.invFunOn_eq hex, hwRight])
    exact hlocAn.congr hagree.symm
  · intro z₀ hz₀
    obtain ⟨loc, hlocAn, hlocLeft, hlocRight⟩ := exists_localInverse_bottcherCoord (hAsub hz₀)
    have hlocAtz₀ : loc (bottcherCoord c z₀) = z₀ := hlocLeft.self_of_nhds
    have hlocInA : ∀ᶠ w in 𝓝 (bottcherCoord c z₀), loc w ∈ A :=
      hlocAn.continuousAt.preimage_mem_nhds (by rw [hlocAtz₀]; exact hAo.mem_nhds hz₀)
    filter_upwards [hlocInA, hlocRight] with w hwA hwRight
    exact Function.invFunOn_eq ⟨loc w, hwA, hwRight⟩

end Bottcher

namespace Bottcher
open Set Filter Topology

/-- **The cover chart is a full biholomorphism `bc : A ≅ bc(A)`.**  Strengthens
`exists_analytic_inverse_bottcher_of_injOn`: on a univalent escape subdomain `A`, the inverse `ψ`
left-inverts `bc` on `A` (`ψ∘bc = id` on `A`) AND right-inverts it on the image (`bc∘ψ = id` on `bc(A)`,
since every `w ∈ bc(A)` is `bc z` for `z ∈ A`).  So `bc : A → bc(A)` is a genuine biholomorphism with
analytic two-sided inverse — the single-chart `LiftUniformization` datum the deck conjugation consumes. -/
theorem exists_bottcher_biholo_of_injOn {c : ℂ} {A : Set ℂ}
    (hAo : IsOpen A) (hAsub : A ⊆ escapeOpen c) (hinj : Set.InjOn (bottcherCoord c) A) :
    ∃ ψ : ℂ → ℂ,
      (Set.EqOn (ψ ∘ bottcherCoord c) id A) ∧
      (Set.EqOn (bottcherCoord c ∘ ψ) id (bottcherCoord c '' A)) ∧
      (∀ z ∈ A, AnalyticAt ℂ ψ (bottcherCoord c z)) := by
  obtain ⟨ψ, hleft, hψan, _hright⟩ :=
    exists_analytic_inverse_bottcher_of_injOn hAo hAsub hinj
  refine ⟨ψ, fun z hz => hleft z hz, ?_, hψan⟩
  rintro w ⟨z, hzA, rfl⟩
  simp only [Function.comp_apply, id_eq, hleft z hzA]

/-- **Deck self-map on a single univalent chart.**  From the cover chart biholomorphism `bc : A ≅ V :=
bc(A)` (its right inverse `ψ`) and the value-rotation `ρ = ζ·` (a self-map of `V`, e.g. `V` a
norm-annulus), the conjugate `g = ψ∘ρ∘bc` is a self-map of `A` along which `bc` scales by `ζ`:
`bc(g z) = ζ·bc z` on `A`.  The genuine geometric deck on one chart
(`deck_scaling_of_invertible_lift` with the real Böttcher coordinate); the global deck on the connected
cover is these patched across sheets. -/
theorem bottcher_deck_scaling {c : ℂ} {A : Set ℂ} {ζ : ℂ} {ψ : ℂ → ℂ}
    (hψright : Set.EqOn (bottcherCoord c ∘ ψ) id (bottcherCoord c '' A))
    (hρmaps : Set.MapsTo (fun w => ζ * w) (bottcherCoord c '' A) (bottcherCoord c '' A)) :
    Set.EqOn (fun z => bottcherCoord c (ψ (ζ * bottcherCoord c z)))
      (fun z => ζ * bottcherCoord c z) A := by
  have h := deck_scaling_of_invertible_lift (φ := bottcherCoord c) (ψ := ψ)
    (ρ := fun w => ζ * w) (ζ := ζ) (U := A) (V := bottcherCoord c '' A)
    hψright (fun _ _ => rfl) (fun z hz => mem_image_of_mem _ hz) hρmaps
  intro z hz
  simpa [Function.comp_apply] using h hz

end Bottcher

namespace Bottcher
open Set Filter Topology

/-- **Deck self-map on a univalent chart with norm-annulus image.**  If `bc` is injective on an open
`A ⊆ escapeOpen` whose image `bc(A)` is a norm-annulus `{ρ < ‖w‖ < R}`, then for every unimodular `ζ`
the conjugate `g = ψ∘(ζ·)∘bc` (`ψ = bc⁻¹`) is a SELF-MAP of `A` along which `bc` scales by `ζ`:
`g(A) ⊆ A` and `bc(g z) = ζ·bc z` on `A`.  The rotation preserves the annulus
(`rotation_mapsTo_annulus`), so the deck is well-defined; for `ζ` a primitive `2ⁿ`-th root this is the
order-`2ⁿ` geometric deck scaling the genuine Böttcher coordinate `φc₁ = bc` (e.g. on the far field,
whose image is such an annulus by `FarFieldSurjective.exists_far_preimage`).  Reduces the geometric deck
to the single estimate `bc(A) = annulus`. -/
theorem exists_bottcher_deck_annulus {c : ℂ} {A : Set ℂ} {ρ R : ℝ} {ζ : ℂ}
    (hAo : IsOpen A) (hAsub : A ⊆ escapeOpen c) (hinj : Set.InjOn (bottcherCoord c) A)
    (himg : bottcherCoord c '' A = {w : ℂ | ρ < ‖w‖ ∧ ‖w‖ < R}) (hζ : ‖ζ‖ = 1) :
    ∃ g : ℂ → ℂ, Set.MapsTo g A A ∧
      Set.EqOn (fun z => bottcherCoord c (g z)) (fun z => ζ * bottcherCoord c z) A := by
  obtain ⟨ψ, hleft, hright, _hψan⟩ := exists_bottcher_biholo_of_injOn hAo hAsub hinj
  have hρmaps : Set.MapsTo (fun w => ζ * w) (bottcherCoord c '' A) (bottcherCoord c '' A) := by
    rw [himg]
    have := rotation_mapsTo_annulus hζ ρ R
    simpa [rotation] using! this
  refine ⟨fun z => ψ (ζ * bottcherCoord c z), ?_, ?_⟩
  · intro z hz
    show ψ (ζ * bottcherCoord c z) ∈ A
    have hwin : ζ * bottcherCoord c z ∈ bottcherCoord c '' A := hρmaps (mem_image_of_mem _ hz)
    obtain ⟨z', hz'A, hz'eq⟩ := hwin
    have hψeq : ψ (ζ * bottcherCoord c z) = z' := by
      rw [← hz'eq]; exact hleft hz'A
    rw [hψeq]; exact hz'A
  · exact bottcher_deck_scaling hright hρmaps

end Bottcher

namespace Bottcher
open Set Filter Topology

/-- **The geometric deck scales by `ζ^k` after `k` iterations.**  If `g` is a self-map of `A` with
`bc∘g = ζ·bc` (the deck of `exists_bottcher_deck_annulus`), then `bc(g^[k] z) = ζ^k·bc z` on `A`. -/
theorem bottcher_deck_iterate_scaling {c : ℂ} {A : Set ℂ} {ζ : ℂ} {g : ℂ → ℂ}
    (hgA : Set.MapsTo g A A)
    (hscale : Set.EqOn (fun z => bottcherCoord c (g z)) (fun z => ζ * bottcherCoord c z) A) :
    ∀ k : ℕ, Set.EqOn (fun z => bottcherCoord c (g^[k] z))
      (fun z => ζ ^ k * bottcherCoord c z) A := by
  intro k
  induction k with
  | zero => intro z _; simp
  | succ n ih =>
    intro z hz
    have hgnz : g^[n] z ∈ A := hgA.iterate n hz
    have h1 : bottcherCoord c (g (g^[n] z)) = ζ * bottcherCoord c (g^[n] z) := hscale hgnz
    have h2 : bottcherCoord c (g^[n] z) = ζ ^ n * bottcherCoord c z := ih hz
    show bottcherCoord c (g^[n + 1] z) = ζ ^ (n + 1) * bottcherCoord c z
    rw [Function.iterate_succ_apply', h1, h2, pow_succ]
    ring

/-- **The geometric deck has order dividing `2ⁿ`.**  If `g` is the deck (`bc∘g = ζ·bc` on `A`, `bc`
injective on `A`) and `ζ^{2ⁿ} = 1`, then `g^[2ⁿ] = id` on `A`: the deck is a `2ⁿ`-torsion self-map.  For
`ζ` a PRIMITIVE `2ⁿ`-th root the order is exactly `2ⁿ` — the dyadic monodromy realized as a genuine
self-biholomorphism of the Böttcher chart, scaling `φc₁ = bc` by `ζ`. -/
theorem bottcher_deck_iterate_id {c : ℂ} {A : Set ℂ} {ζ : ℂ} {g : ℂ → ℂ} {n : ℕ}
    (hgA : Set.MapsTo g A A) (hinj : Set.InjOn (bottcherCoord c) A)
    (hscale : Set.EqOn (fun z => bottcherCoord c (g z)) (fun z => ζ * bottcherCoord c z) A)
    (hζ : ζ ^ (2 ^ n) = 1) :
    Set.EqOn (g^[2 ^ n]) id A := by
  intro z hz
  have hgz : g^[2 ^ n] z ∈ A := hgA.iterate (2 ^ n) hz
  apply hinj hgz hz
  have := bottcher_deck_iterate_scaling hgA hscale (2 ^ n) hz
  simp only at this
  rw [this, hζ, one_mul]

end Bottcher

namespace Bottcher
open Set Filter Topology

/-- **The geometric deck and its inverse-rotation deck are mutually inverse on `A`.**  If `g, g'` are
self-maps of `A` (`bc` injective on `A`) with `bc∘g = ζ·bc` and `bc∘g' = ζ⁻¹·bc` (`ζ ≠ 0`), then
`g∘g' = g'∘g = id` on `A`.  So `g` is a self-BIHOLOMORPHISM of the chart `A` (the deck), with inverse
`g'` — exactly the mutually-inverse data `MeromorphicField.precompMeroEquiv` consumes to lift the deck
to a field automorphism of `meroField A` scaling the `φc₁`-germ by `ζ` while fixing the deck-invariant
base `φc₁^{2ⁿ} = bc∘f^[n]`. -/
theorem bottcher_deck_mutual_inverse {c : ℂ} {A : Set ℂ} {ζ : ℂ} {g g' : ℂ → ℂ}
    (hζ : ζ ≠ 0) (hinj : Set.InjOn (bottcherCoord c) A)
    (hgA : Set.MapsTo g A A) (hg'A : Set.MapsTo g' A A)
    (hg : Set.EqOn (fun z => bottcherCoord c (g z)) (fun z => ζ * bottcherCoord c z) A)
    (hg' : Set.EqOn (fun z => bottcherCoord c (g' z)) (fun z => ζ⁻¹ * bottcherCoord c z) A) :
    Set.EqOn (g ∘ g') id A ∧ Set.EqOn (g' ∘ g) id A := by
  refine ⟨fun z hz => ?_, fun z hz => ?_⟩
  · have hg'z : g' z ∈ A := hg'A hz
    apply hinj (hgA hg'z) hz
    show bottcherCoord c (g (g' z)) = bottcherCoord c (id z)
    have h1 : bottcherCoord c (g (g' z)) = ζ * bottcherCoord c (g' z) := hg hg'z
    have h2 : bottcherCoord c (g' z) = ζ⁻¹ * bottcherCoord c z := hg' hz
    rw [h1, h2, ← mul_assoc, mul_inv_cancel₀ hζ, one_mul, id_eq]
  · have hgz : g z ∈ A := hgA hz
    apply hinj (hg'A hgz) hz
    show bottcherCoord c (g' (g z)) = bottcherCoord c (id z)
    have h1 : bottcherCoord c (g' (g z)) = ζ⁻¹ * bottcherCoord c (g z) := hg' hgz
    have h2 : bottcherCoord c (g z) = ζ * bottcherCoord c z := hg hz
    rw [h1, h2, ← mul_assoc, inv_mul_cancel₀ hζ, one_mul, id_eq]

end Bottcher
