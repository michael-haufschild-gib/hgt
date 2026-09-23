import GaloisForLFunctions.Bottcher.EvenHoloExtension

/-!
# task02 §1 — boundary-continuation doubling propagation

The load-bearing dynamical step of the connected-case natural-boundary argument: for a solution `h`
of the Böttcher functional equation on the unit disk, holomorphic continuation across a boundary
point `ζ` (`|ζ|=1`) forces continuation across `ζ²`.  Iterating this along the angle-doubling map
spreads any positive-length arc of continuation over the whole circle — the remaining step (a
compactness/gluing argument producing holomorphy on a disk of radius `>1`, feeding
`c_mem_of_even_holo_ball`) is routine and not yet formalized here.
-/

open Complex Metric Set Filter Topology

namespace Bottcher

/-- `ContinuesAcross h ζ`: the germ of `h` on the open unit disk extends holomorphically across the
boundary point `ζ` — there is an open `U ∋ ζ` and a holomorphic `G` on `U` agreeing with `h` on the
inner side `U ∩ 𝔻`. -/
def ContinuesAcross (h : ℂ → ℂ) (ζ : ℂ) : Prop :=
  ∃ U : Set ℂ, IsOpen U ∧ ζ ∈ U ∧ ∃ G : ℂ → ℂ, DifferentiableOn ℂ G U ∧
    Set.EqOn G h (U ∩ Metric.ball 0 1)

/-- **Doubling propagation (task02 §1 heart).**  For a solution `h` of the Böttcher functional
equation on the unit disk, holomorphic continuation across a boundary point `ζ` (with `|ζ|=1`)
propagates to continuation across `ζ²`, via `G'(s) = G(τ s)² + c·s` with `τ` the branch of `√`
normalized by `τ(ζ²)=ζ`. -/
theorem continuesAcross_sq {h : ℂ → ℂ} {c : ℂ} {ζ : ℂ} (hζ : ‖ζ‖ = 1)
    (hfe : ∀ t ∈ ball (0 : ℂ) 1, h (t ^ (2 : ℕ)) = (h t) ^ (2 : ℕ) + c * t ^ (2 : ℕ))
    (hcont : ContinuesAcross h ζ) :
    ContinuesAcross h (ζ ^ (2 : ℕ)) := by
  obtain ⟨U, hUopen, hζU, G, hGd, hGh⟩ := hcont
  have hζ0 : ζ ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hζ; norm_num at hζ
  have hζ2 : (ζ : ℂ) ^ (2 : ℕ) ≠ 0 := pow_ne_zero 2 hζ0
  -- τ(s) = ζ · (s / ζ²)^{1/2}
  set τ : ℂ → ℂ := fun s => ζ * (s / ζ ^ (2 : ℕ)) ^ ((2 : ℂ)⁻¹) with hτdef
  have hτsq : ∀ s : ℂ, (τ s) ^ (2 : ℕ) = s := by
    intro s
    rw [hτdef, mul_pow]
    have hcp : ((s / ζ ^ (2 : ℕ)) ^ ((2 : ℂ)⁻¹)) ^ (2 : ℕ) = s / ζ ^ (2 : ℕ) := by
      have := Complex.cpow_nat_inv_pow (s / ζ ^ (2 : ℕ)) (n := 2) two_ne_zero
      rwa [Nat.cast_ofNat] at this
    rw [hcp]; field_simp
  have hτζ2 : τ (ζ ^ (2 : ℕ)) = ζ := by
    simp only [hτdef, div_self hζ2, Complex.one_cpow, mul_one]
  have hτnorm : ∀ s : ℂ, ‖τ s‖ ^ (2 : ℕ) = ‖s‖ := fun s => by rw [← norm_pow, hτsq]
  -- S = where the branch is analytic;  τ holomorphic on S
  set S : Set ℂ := {s : ℂ | s / ζ ^ (2 : ℕ) ∈ slitPlane} with hSdef
  have hSopen : IsOpen S := Complex.isOpen_slitPlane.preimage (continuous_id.div_const _)
  have hζ2S : (ζ : ℂ) ^ (2 : ℕ) ∈ S := by
    rw [hSdef, mem_setOf_eq, div_self hζ2]; exact Complex.one_mem_slitPlane
  have hτd : DifferentiableOn ℂ τ S := by
    intro s hs
    apply DifferentiableAt.differentiableWithinAt
    have hinner : DifferentiableAt ℂ (fun u : ℂ => u ^ ((2 : ℂ)⁻¹)) (s / ζ ^ (2 : ℕ)) :=
      (Complex.hasStrictDerivAt_cpow_const (hs : s / ζ ^ (2 : ℕ) ∈ slitPlane)).hasDerivAt.differentiableAt
    have hdiv : DifferentiableAt ℂ (fun s : ℂ => s / ζ ^ (2 : ℕ)) s := differentiableAt_id.div_const _
    have hcomp : DifferentiableAt ℂ (fun s => (s / ζ ^ (2 : ℕ)) ^ ((2 : ℂ)⁻¹)) s := by
      simpa [Function.comp_def] using hinner.comp s hdiv
    rw [hτdef]
    exact hcomp.const_mul ζ
  -- V = S ∩ τ⁻¹U:  open nbhd of ζ² on which τ lands in U
  set V : Set ℂ := S ∩ τ ⁻¹' U with hVdef
  have hVopen : IsOpen V := hτd.continuousOn.isOpen_inter_preimage hSopen hUopen
  have hζ2V : (ζ : ℂ) ^ (2 : ℕ) ∈ V := ⟨hζ2S, by rw [mem_preimage, hτζ2]; exact hζU⟩
  have hVS : V ⊆ S := inter_subset_left
  have hτmaps : MapsTo τ V U := fun s hs => hs.2
  -- the propagated continuation
  set G' : ℂ → ℂ := fun s => (G (τ s)) ^ (2 : ℕ) + c * s with hG'def
  have hG'd : DifferentiableOn ℂ G' V := by
    have hGτ : DifferentiableOn ℂ (fun s => G (τ s)) V := hGd.comp (hτd.mono hVS) hτmaps
    exact (hGτ.pow 2).add ((differentiableOn_const c).mul differentiableOn_id)
  have hG'h : Set.EqOn G' h (V ∩ ball 0 1) := by
    intro s hs
    obtain ⟨hsV, hsball⟩ := hs
    rw [mem_ball_zero_iff] at hsball
    have hτU : τ s ∈ U := hτmaps hsV
    have hτball : τ s ∈ ball (0 : ℂ) 1 := by
      rw [mem_ball_zero_iff]
      nlinarith [hτnorm s, norm_nonneg (τ s), sq_nonneg (‖τ s‖ - 1), hsball]
    have hGτh : G (τ s) = h (τ s) := hGh ⟨hτU, hτball⟩
    calc G' s = (h (τ s)) ^ (2 : ℕ) + c * (τ s) ^ (2 : ℕ) := by simp only [hG'def]; rw [hGτh, hτsq s]
      _ = h ((τ s) ^ (2 : ℕ)) := (hfe (τ s) hτball).symm
      _ = h s := by rw [hτsq s]
  exact ⟨V, hVopen, hζ2V, G', hG'd, hG'h⟩

end Bottcher
