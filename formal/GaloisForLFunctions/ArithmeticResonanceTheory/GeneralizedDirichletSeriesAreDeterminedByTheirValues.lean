import Mathlib

/-!
# Generalized Dirichlet series are determined by their values

A generalized Dirichlet series `Σ_i w_i e^{−σ λ_i}` over any index type, with real coefficients and
**locally finite** frequencies (`{i | λ_i ≤ T}` finite for every `T`), absolutely convergent on
`σ > σ₀`, determines its coefficient masses: if it vanishes for all `σ > σ₀`, then the mass
`Σ_{λ_i = t} w_i` at every frequency `t` is `0` (`massAt_eq_zero_of_tsum_eq_zero`).

**Proof.** Take the least frequency `t₀` with nonzero mass. Below it every mass vanishes, so the
finite head `Σ_{λ_i ≤ t₀}` equals `e^{−σ t₀}` times the mass at `t₀`. Local finiteness gives a gap
`δ > 0` above `t₀`, and the tail is `O(e^{−σ(t₀ + δ)})`. Multiplying by `e^{σ t₀}` and letting
`σ → ∞` kills the mass at `t₀`.

This is the uniqueness used to read the length spectrum of a dynamical system off its zeta
function: two zeta functions that agree have the same periodic-orbit masses at every length. The
index is arbitrary and frequencies may repeat; the strictly increasing case is
`RHTower.generalizedDirichletSeries_coeff_eq_zero_of_eventuallyEq_zero`.
-/

open Filter Topology

namespace GaloisForLFunctions.ArithmeticResonanceTheory

variable {ι : Type*}

/-- The coefficient mass `Σ_{λ_i = t} w_i` at the frequency `t` (a finite sum). -/
noncomputable def massAt (w l : ι → ℝ) (hfin : ∀ T : ℝ, {i | l i ≤ T}.Finite) (t : ℝ) : ℝ :=
  ∑ i ∈ (hfin t).toFinset.filter (fun i => l i = t), w i

theorem mem_massAt_finset {l : ι → ℝ} {hfin : ∀ T : ℝ, {i | l i ≤ T}.Finite} {t : ℝ} {i : ι} :
    i ∈ (hfin t).toFinset.filter (fun i => l i = t) ↔ l i = t := by
  simp only [Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
  exact ⟨fun h => h.2, fun h => ⟨h.le, h⟩⟩

/-- The head `Σ_{λ_i ≤ T} w_i e^{−σλ_i}` grouped by frequency. -/
theorem head_eq_sum_massAt (w l : ι → ℝ) (hfin : ∀ T : ℝ, {i | l i ≤ T}.Finite) (T σ : ℝ) :
    ∑ i ∈ (hfin T).toFinset, w i * Real.exp (-(σ * l i)) =
      ∑ t ∈ (hfin T).toFinset.image l, Real.exp (-(σ * t)) * massAt w l hfin t := by
  classical
  rw [Finset.sum_image' (fun i => w i * Real.exp (-(σ * l i)))]
  intro i hi
  rw [massAt, Finset.mul_sum]
  have hset : (hfin (l i)).toFinset.filter (fun j => l j = l i) =
      (hfin T).toFinset.filter (fun j => l j = l i) := by
    ext j
    simp only [Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
    have hiT : l i ≤ T := by simpa using hi
    constructor
    · rintro ⟨-, h⟩; exact ⟨h ▸ hiT, h⟩
    · rintro ⟨-, h⟩; exact ⟨h.le, h⟩
  rw [hset]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [(Finset.mem_filter.mp hj).2]; ring

/-- **Uniqueness.** A generalized Dirichlet series with locally finite frequencies that vanishes on
`σ > σ₀` has zero coefficient mass at every frequency. -/
theorem massAt_eq_zero_of_tsum_eq_zero (w l : ι → ℝ) (hfin : ∀ T : ℝ, {i | l i ≤ T}.Finite)
    {σ₀ : ℝ} (hsum : ∀ σ, σ₀ < σ → Summable fun i => |w i| * Real.exp (-(σ * l i)))
    (hzero : ∀ σ, σ₀ < σ → ∑' i, w i * Real.exp (-(σ * l i)) = 0) (t : ℝ) :
    massAt w l hfin t = 0 := by
  classical
  by_contra ht
  -- the least frequency with nonzero mass
  set B : Finset ℝ := ((hfin t).toFinset.filter fun i => massAt w l hfin (l i) ≠ 0).image l with hB
  have htB : t ∈ B := by
    obtain ⟨i, hi⟩ : ((hfin t).toFinset.filter fun i => l i = t).Nonempty := by
      by_contra hempty
      rw [Finset.not_nonempty_iff_eq_empty] at hempty
      exact ht (by rw [massAt, hempty, Finset.sum_empty])
    have hlt : l i = t := mem_massAt_finset.mp hi
    refine Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨?_, by rwa [hlt]⟩, hlt⟩
    simp [hlt]
  have hBne : B.Nonempty := ⟨t, htB⟩
  set t₀ := B.min' hBne with ht₀
  have ht₀B : t₀ ∈ B := B.min'_mem hBne
  obtain ⟨i₀, hi₀, hli₀⟩ := Finset.mem_image.mp ht₀B
  have hmass : massAt w l hfin t₀ ≠ 0 := by
    have := (Finset.mem_filter.mp hi₀).2; rwa [hli₀] at this
  have ht₀t : t₀ ≤ t := B.min'_le t htB
  have hbelow : ∀ t' < t₀, massAt w l hfin t' = 0 := by
    intro t' ht'
    by_contra hne
    obtain ⟨i, hi⟩ : ((hfin t').toFinset.filter fun i => l i = t').Nonempty := by
      by_contra hempty
      rw [Finset.not_nonempty_iff_eq_empty] at hempty
      exact hne (by rw [massAt, hempty, Finset.sum_empty])
    have hlt : l i = t' := mem_massAt_finset.mp hi
    have hmem : t' ∈ B := Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr
      ⟨by simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq]; linarith, by rwa [hlt]⟩, hlt⟩
    exact absurd (B.min'_le t' hmem) (not_le.mpr ht')
  -- a gap `δ > 0` above `t₀`
  obtain ⟨δ, hδ, hgap⟩ : ∃ δ > 0, ∀ i, t₀ < l i → t₀ + δ ≤ l i := by
    set G := ((hfin (t₀ + 1)).toFinset.filter fun i => t₀ < l i).image l with hG
    by_cases hGne : G.Nonempty
    · refine ⟨G.min' hGne - t₀, ?_, fun i hi => ?_⟩
      · obtain ⟨j, hj, hjl⟩ := Finset.mem_image.mp (G.min'_mem hGne)
        have := (Finset.mem_filter.mp hj).2
        linarith
      · by_cases hi1 : l i ≤ t₀ + 1
        · have : l i ∈ G := Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr
            ⟨by simpa using hi1, hi⟩, rfl⟩
          linarith [G.min'_le (l i) this]
        · have hle : G.min' hGne ≤ t₀ + 1 := by
            obtain ⟨j, hj, hjl⟩ := Finset.mem_image.mp (G.min'_mem hGne)
            have : l j ≤ t₀ + 1 := by
              have := (Finset.mem_filter.mp hj).1
              simpa using this
            linarith
          linarith
    · refine ⟨1, one_pos, fun i hi => ?_⟩
      by_contra hlt
      exact hGne ⟨l i, Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr
        ⟨by simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq]; linarith, hi⟩, rfl⟩⟩
  -- for `σ ≥ σ₁`, the mass at `t₀` is bounded by `M e^{σ₁(t₀+δ)} e^{−σδ}`
  set σ₁ := σ₀ + 1 with hσ₁
  set M := ∑' i, |w i| * Real.exp (-(σ₁ * l i)) with hM
  have hM0 : 0 ≤ M := tsum_nonneg fun i => by positivity
  have hbound : ∀ σ, σ₁ ≤ σ →
      |massAt w l hfin t₀| ≤ M * Real.exp (σ₁ * (t₀ + δ)) * Real.exp (-(σ * δ)) := by
    intro σ hσ
    have hσ0 : σ₀ < σ := by linarith
    set F := (hfin t₀).toFinset with hF
    have hf : Summable fun i => w i * Real.exp (-(σ * l i)) :=
      Summable.of_norm_bounded (hsum σ hσ0) fun i => by
        rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    -- the head is `e^{−σ t₀}` times the mass at `t₀`
    have hhead : ∑ i ∈ F, w i * Real.exp (-(σ * l i)) =
        Real.exp (-(σ * t₀)) * massAt w l hfin t₀ := by
      rw [hF, head_eq_sum_massAt, Finset.sum_eq_single t₀]
      · intro t' ht' hne
        have : t' ≤ t₀ := by
          obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp ht'
          simpa using hj
        rw [hbelow t' (lt_of_le_of_ne this hne), mul_zero]
      · intro hnot
        exact absurd (Finset.mem_image.mpr ⟨i₀, by simp [hli₀], hli₀⟩) hnot
    -- the tail beyond the gap
    have htail : |∑' i : ↥((F : Set ι)ᶜ), w i * Real.exp (-(σ * l i))| ≤
        M * Real.exp (-((σ - σ₁) * (t₀ + δ))) := by
      have hsub := (hsum σ₁ (by linarith)).subtype ((F : Set ι)ᶜ)
      calc |∑' i : ↥((F : Set ι)ᶜ), w i * Real.exp (-(σ * l i))|
          ≤ ∑' i : ↥((F : Set ι)ᶜ), ‖w i * Real.exp (-(σ * l i))‖ := by
            rw [← Real.norm_eq_abs]; exact norm_tsum_le_tsum_norm (hf.subtype _).norm
        _ ≤ ∑' i : ↥((F : Set ι)ᶜ), |w i| * Real.exp (-(σ₁ * l i)) *
              Real.exp (-((σ - σ₁) * (t₀ + δ))) := by
            refine Summable.tsum_le_tsum (fun i => ?_) (hf.subtype _).norm
              (hsub.mul_right _)
            have hi : t₀ < l i := by
              have := i.2
              simp only [hF, Set.mem_compl_iff, Finset.mem_coe, Set.Finite.mem_toFinset,
                Set.mem_setOf_eq, not_le] at this
              exact this
            rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), mul_assoc,
              ← Real.exp_add]
            refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (abs_nonneg _)
            nlinarith [hgap i hi]
        _ = (∑' i : ↥((F : Set ι)ᶜ), |w i| * Real.exp (-(σ₁ * l i))) *
              Real.exp (-((σ - σ₁) * (t₀ + δ))) := tsum_mul_right
        _ ≤ M * Real.exp (-((σ - σ₁) * (t₀ + δ))) := by
            refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
            exact Summable.tsum_subtype_le (fun i => |w i| * Real.exp (-(σ₁ * l i)))
              _ (fun i => by positivity) (hsum σ₁ (by linarith))
    have hsplit := hf.sum_add_tsum_compl (s := F)
    rw [hzero σ hσ0, hhead] at hsplit
    have h1 : Real.exp (-(σ * t₀)) * |massAt w l hfin t₀| ≤
        M * Real.exp (-((σ - σ₁) * (t₀ + δ))) := by
      rw [← abs_of_pos (Real.exp_pos (-(σ * t₀))), ← abs_mul, show
        Real.exp (-(σ * t₀)) * massAt w l hfin t₀ =
          -∑' i : ↥((F : Set ι)ᶜ), w i * Real.exp (-(σ * l i)) by linarith, abs_neg]
      exact htail
    have h2 : |massAt w l hfin t₀| ≤
        M * Real.exp (-((σ - σ₁) * (t₀ + δ))) * Real.exp (σ * t₀) := by
      have he := Real.exp_pos (σ * t₀)
      calc |massAt w l hfin t₀| = Real.exp (σ * t₀) * (Real.exp (-(σ * t₀)) *
            |massAt w l hfin t₀|) := by
            rw [← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul]
        _ ≤ Real.exp (σ * t₀) * (M * Real.exp (-((σ - σ₁) * (t₀ + δ)))) :=
            mul_le_mul_of_nonneg_left h1 he.le
        _ = _ := by ring
    calc |massAt w l hfin t₀| ≤ M * Real.exp (-((σ - σ₁) * (t₀ + δ))) * Real.exp (σ * t₀) := h2
      _ = M * Real.exp (σ₁ * (t₀ + δ)) * Real.exp (-(σ * δ)) := by
          rw [mul_assoc, mul_assoc, ← Real.exp_add, ← Real.exp_add]
          congr 2
          ring
  -- the bound tends to `0`
  have hlim : Tendsto (fun σ : ℝ => M * Real.exp (σ₁ * (t₀ + δ)) * Real.exp (-(σ * δ)))
      atTop (𝓝 0) := by
    have h1 : Tendsto (fun σ : ℝ => -(σ * δ)) atTop atBot :=
      tendsto_neg_atTop_atBot.comp (tendsto_id.atTop_mul_const hδ)
    simpa using (Real.tendsto_exp_atBot.comp h1).const_mul (M * Real.exp (σ₁ * (t₀ + δ)))
  have hpos : 0 < |massAt w l hfin t₀| := abs_pos.mpr hmass
  obtain ⟨σ, hσ1, hσsmall⟩ := ((eventually_ge_atTop σ₁).and
    (hlim.eventually (gt_mem_nhds hpos))).exists
  exact absurd (hbound σ hσ1) (not_le.mpr hσsmall)

end GaloisForLFunctions.ArithmeticResonanceTheory
