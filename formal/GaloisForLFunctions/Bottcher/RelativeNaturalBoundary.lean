/-
# Relative natural-boundary obstruction (analytic coefficients)

The general-coefficient version of the natural-boundary machinery in `NaturalBoundaryContradiction` /
`AlgebraicBranch`, with the relation's coefficients allowed to be **arbitrary analytic functions**
`aᵢ(z)` rather than polynomials `(P.coeff i).aeval z`. This is exactly what the *relative* transcendence
`TranscendentalOverAdjoin φ_{c₁} φ_{c₂}` (the hRigid / Eremenko–van Strien input) needs: an algebraic
relation of `φ_{c₁}` over `K[φ_{c₂}]` has coefficients in `K[φ_{c₂}]`, which are analytic near a point of
`J_{c₁}∖J_{c₂}` (where `φ_{c₂}` is analytic) but not polynomial in `z`.

* `branch_unique_within_analytic` — boundary branch-uniqueness, analytic coefficients;
* `exists_analyticAt_branch_analytic` — simple-root branch, analytic coefficients;
* `false_of_basin_branch_dendrite_analytic` — the natural-boundary contradiction, analytic coefficients.
-/
import GaloisForLFunctions.Bottcher.AlgebraicBranch
import GaloisForLFunctions.Bottcher.NaturalBoundaryContradiction
import GaloisForLFunctions.Bottcher.DendriteBoundary
open Filter Topology Metric Set

namespace Bottcher

/-- **Branch uniqueness across a boundary point — general analytic-coefficient form.** The
`nhdsWithin` branch-uniqueness of `branch_unique_poly_within` with the polynomial coefficients
`(P.coeff i).aeval z` replaced by an arbitrary finite family of continuous coefficients `a i z`. Needed
for the *relative* transcendence `TranscendentalOverAdjoin` whose relation coefficients lie in
`K[φ_{c₂}]` (analytic, not polynomial in `z`). -/
theorem branch_unique_within_analytic {z₀ w₀ d : ℂ} {s : Finset ℕ} {a : ℕ → ℂ → ℂ}
    (hacont : ∀ i ∈ s, ContinuousAt (a i) z₀)
    (hpartial : HasDerivAt (fun w => ∑ i ∈ s, a i z₀ * w ^ i) d w₀) (hd : d ≠ 0)
    {t : Set ℂ} {g₁ g₂ : ℂ → ℂ}
    (hg₁ : ContinuousAt g₁ z₀) (h₁ : g₁ z₀ = w₀)
    (hg₂ : Tendsto g₂ (𝓝[t] z₀) (𝓝 w₀))
    (hrel₁ : ∀ᶠ z in 𝓝[t] z₀, ∑ i ∈ s, a i z * (g₁ z) ^ i = 0)
    (hrel₂ : ∀ᶠ z in 𝓝[t] z₀, ∑ i ∈ s, a i z * (g₂ z) ^ i = 0) :
    ∀ᶠ z in 𝓝[t] z₀, g₁ z = g₂ z := by
  have hfactor : ∀ z α β : ℂ,
      (∑ i ∈ s, a i z * α ^ i) - (∑ i ∈ s, a i z * β ^ i)
        = (α - β) * ∑ i ∈ s, a i z * (∑ j ∈ Finset.range i, α ^ j * β ^ (i - 1 - j)) := by
    intro z α β
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    have hg : α ^ i - β ^ i = (∑ j ∈ Finset.range i, α ^ j * β ^ (i - 1 - j)) * (α - β) :=
      (geom_sum₂_mul α β i).symm
    rw [← mul_sub, hg]; ring
  have hval : (∑ i ∈ s, a i z₀ * (∑ j ∈ Finset.range i, w₀ ^ j * w₀ ^ (i - 1 - j))) = d := by
    have hd' : HasDerivAt (fun w => ∑ i ∈ s, a i z₀ * w ^ i)
        (∑ i ∈ s, a i z₀ * ((i : ℂ) * w₀ ^ (i - 1))) w₀ := by
      have key : (fun w => ∑ i ∈ s, a i z₀ * w ^ i) = ∑ i ∈ s, (fun w => a i z₀ * w ^ i) := by
        funext w; simp only [Finset.sum_apply]
      rw [key]
      exact HasDerivAt.sum (fun i _ => (hasDerivAt_pow i w₀).const_mul (a i z₀))
    rw [← hd'.unique hpartial]
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    have hinner : ∀ j ∈ Finset.range i, w₀ ^ j * w₀ ^ (i - 1 - j) = w₀ ^ (i - 1) := by
      intro j hj; rw [Finset.mem_range] at hj; rw [← pow_add]; congr 1; omega
    rw [Finset.sum_congr rfl hinner, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hg1t : Tendsto g₁ (𝓝[t] z₀) (𝓝 w₀) := by
    rw [← h₁]; exact (hg₁.tendsto).mono_left nhdsWithin_le_nhds
  have hQt : Tendsto (fun z => ∑ i ∈ s, a i z *
      (∑ j ∈ Finset.range i, (g₁ z) ^ j * (g₂ z) ^ (i - 1 - j))) (𝓝[t] z₀)
      (𝓝 (∑ i ∈ s, a i z₀ * (∑ j ∈ Finset.range i, w₀ ^ j * w₀ ^ (i - 1 - j)))) := by
    apply tendsto_finsetSum
    intro i hi
    apply Tendsto.mul
    · exact ((hacont i hi).tendsto).mono_left nhdsWithin_le_nhds
    · apply tendsto_finsetSum
      intro j _
      exact (hg1t.pow j).mul (hg₂.pow _)
  have hQne : ∀ᶠ z in 𝓝[t] z₀, (∑ i ∈ s, a i z *
      (∑ j ∈ Finset.range i, (g₁ z) ^ j * (g₂ z) ^ (i - 1 - j))) ≠ 0 := by
    rw [hval] at hQt
    exact hQt.eventually (eventually_ne_nhds hd)
  filter_upwards [hrel₁, hrel₂, hQne] with z h1 h2 hQz
  have hz : (g₁ z - g₂ z) * (∑ i ∈ s, a i z *
      (∑ j ∈ Finset.range i, (g₁ z) ^ j * (g₂ z) ^ (i - 1 - j))) = 0 := by
    have h := hfactor z (g₁ z) (g₂ z)
    rw [h1, h2] at h
    simpa using h.symm
  rcases mul_eq_zero.mp hz with h | h
  · exact sub_eq_zero.mp h
  · exact absurd h hQz


/-- **Analytic-coefficient simple-root branch.** `exists_analyticAt_branch_poly` with the polynomial
coefficients replaced by analytic ones. -/
theorem exists_analyticAt_branch_analytic {z₀ w₀ d : ℂ} {s : Finset ℕ} {a : ℕ → ℂ → ℂ}
    (ha : ∀ i ∈ s, ContDiffAt ℂ ⊤ (a i) z₀)
    (hroot : ∑ i ∈ s, a i z₀ * w₀ ^ i = 0)
    (hpartial : HasDerivAt (fun w => ∑ i ∈ s, a i z₀ * w ^ i) d w₀) (hd : d ≠ 0) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g z₀ ∧ g z₀ = w₀ ∧
      ∀ᶠ z in 𝓝 z₀, ∑ i ∈ s, a i z * (g z) ^ i = 0 := by
  have hf : ContDiffAt ℂ ⊤ (fun p : ℂ × ℂ => ∑ i ∈ s, a i p.1 * p.2 ^ i) (z₀, w₀) := by
    apply ContDiffAt.sum
    intro i hi
    exact ((ha i hi).comp (z₀, w₀) contDiffAt_fst).mul (contDiffAt_snd.pow i)
  exact exists_analyticAt_branch_of_hasDerivAt hf hroot hpartial hd

/-- **Natural-boundary contradiction, analytic-coefficient form.** `false_of_basin_branch_dendrite`
with the relation's polynomial coefficients `(P.coeff i).aeval z` replaced by arbitrary analytic
coefficients `a i z` (this is what the relative case `TranscendentalOverAdjoin` needs: coefficients in
`K[φ_{c₂}]`, analytic near `J_{c₁}∖J_{c₂}`). -/
theorem false_of_basin_branch_dendrite_analytic {c z₀ w₀ d : ℂ} {r : ℝ} {s : Finset ℕ} {a : ℕ → ℂ → ℂ}
    (ha : ∀ i ∈ s, ContDiffAt ℂ ⊤ (a i) z₀)
    (hr : 0 < r) (hz₀ : z₀ ∈ filledJulia c)
    (hempty : ball z₀ r ∩ interior (filledJulia c) = ∅)
    (hroot : ∑ i ∈ s, a i z₀ * w₀ ^ i = 0)
    (hpartial : HasDerivAt (fun w => ∑ i ∈ s, a i z₀ * w ^ i) d w₀) (hd : d ≠ 0)
    {β : ℂ → ℂ}
    (hβlim : Tendsto β (𝓝[(filledJulia c)ᶜ] z₀) (𝓝 w₀))
    (hβrel : ∀ᶠ z in 𝓝[(filledJulia c)ᶜ] z₀, ∑ i ∈ s, a i z * (β z) ^ i = 0)
    (hβmod : ∀ᶠ z in 𝓝[(filledJulia c)ᶜ] z₀, ‖β z‖ = Real.exp (greenFunctionDyn c z)) :
    False := by
  have hz₀int : z₀ ∉ interior (filledJulia c) := fun h => by
    have : z₀ ∈ ball z₀ r ∩ interior (filledJulia c) := ⟨mem_ball_self hr, h⟩
    rwa [hempty] at this
  have hNeBot : (𝓝[(filledJulia c)ᶜ] z₀).NeBot :=
    mem_closure_iff_nhdsWithin_neBot.mp (by rw [closure_compl]; exact hz₀int)
  obtain ⟨g, hgAt, hgz₀, hgrel⟩ := exists_analyticAt_branch_analytic ha hroot hpartial hd
  have hacont : ∀ i ∈ s, ContinuousAt (a i) z₀ := fun i hi => (ha i hi).continuousAt
  have hmatch := branch_unique_within_analytic hacont hpartial hd hgAt.continuousAt hgz₀ hβlim
    (hgrel.filter_mono nhdsWithin_le_nhds) hβrel
  have hgmod : ∀ᶠ z in 𝓝[(filledJulia c)ᶜ] z₀, ‖g z‖ = Real.exp (greenFunctionDyn c z) := by
    filter_upwards [hmatch, hβmod] with z hz hzm; rw [hz, hzm]
  obtain ⟨ε₁, hε₁, hgan1⟩ := Metric.eventually_nhds_iff.mp hgAt.eventually_analyticAt
  obtain ⟨U, hUopen, hz₀U, hUsub⟩ := mem_nhdsWithin.mp hgmod
  obtain ⟨ε₂, hε₂, hUball⟩ := Metric.isOpen_iff.mp hUopen z₀ hz₀U
  set r' := min r (min ε₁ ε₂) with hr'def
  have hr' : 0 < r' := lt_min hr (lt_min hε₁ hε₂)
  have hr'r : r' ≤ r := min_le_left _ _
  have hr'1 : r' ≤ ε₁ := le_trans (min_le_right _ _) (min_le_left _ _)
  have hr'2 : r' ≤ ε₂ := le_trans (min_le_right _ _) (min_le_right _ _)
  refine no_continuation_dendrite (g := g) hr' ?_ hz₀ ?_ ?_ ?_
  · intro z hz
    exact hgan1 (lt_of_lt_of_le (mem_ball.mp hz) hr'1)
  · refine eq_empty_of_subset_empty ?_
    rw [← hempty]
    exact inter_subset_inter_left _ (Metric.ball_subset_ball hr'r)
  · intro z hz hzK
    exact hUsub ⟨hUball (Metric.ball_subset_ball hr'2 hz), hzK⟩
  · obtain ⟨z, hz1, hz2⟩ :=
      hNeBot.nonempty_of_mem (inter_mem_nhdsWithin _ (ball_mem_nhds z₀ hr'))
    exact ⟨z, hz2, hz1⟩

end Bottcher
