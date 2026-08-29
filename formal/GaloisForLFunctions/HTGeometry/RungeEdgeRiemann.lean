import GaloisForLFunctions.HTGeometry.IntervalRiemannSum

/-!
# Rational approximation of a Cauchy-kernel edge integral

A contour integral `∫ γ(x) F(γ x) (γ x − z)⁻¹ dx` over a compact parametrized edge is uniformly
approximated, for `z` ranging over a compact set disjoint from the edge, by its left-endpoint
Riemann sums — which are rational functions of `z` with simple poles on the edge.

The uniformity comes for free: the two-variable integrand is continuous on the compact product of
the parameter interval with the `z`-set, hence uniformly continuous there.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex intervalIntegral MeasureTheory Set

noncomputable section

/-- The parametrized edge integral of the Cauchy-kernel integrand. -/
def edgeCauchyIntegral (F : ℂ → ℂ) (γ : ℝ → ℂ) (a b : ℝ) (z : ℂ) : ℂ :=
  ∫ x in a..b, F (γ x) * (γ x - z)⁻¹

/-- Its left-endpoint Riemann sum: a rational function of `z` with simple poles on the edge. -/
def edgeCauchyRiemann (F : ℂ → ℂ) (γ : ℝ → ℂ) (a b : ℝ) (N : ℕ) (z : ℂ) : ℂ :=
  ∑ i ∈ Finset.range N,
    (((b - a) / N : ℝ)) • (F (γ (uniformNode a b N i)) * (γ (uniformNode a b N i) - z)⁻¹)

theorem continuousOn_edgeCauchyIntegrand {F : ℂ → ℂ} {γ : ℝ → ℂ} {a b : ℝ} {Z : Set ℂ}
    (hγ : ContinuousOn γ (Icc a b)) (hF : ContinuousOn F (γ '' Icc a b))
    (hne : ∀ x ∈ Icc a b, ∀ z ∈ Z, γ x ≠ z) :
    ContinuousOn (fun p : ℝ × ℂ => F (γ p.1) * (γ p.1 - p.2)⁻¹) (Icc a b ×ˢ Z) := by
  have hγ' : ContinuousOn (fun p : ℝ × ℂ => γ p.1) (Icc a b ×ˢ Z) :=
    hγ.comp continuousOn_fst (fun p hp => hp.1)
  have hF' : ContinuousOn (fun p : ℝ × ℂ => F (γ p.1)) (Icc a b ×ˢ Z) :=
    hF.comp hγ' (fun p hp => ⟨p.1, hp.1, rfl⟩)
  refine hF'.mul ?_
  refine ContinuousOn.inv₀ (hγ'.sub continuousOn_snd) ?_
  intro p hp
  exact sub_ne_zero.2 (hne p.1 hp.1 p.2 hp.2)

/-- **Uniform rational approximation of an edge integral.** -/
theorem exists_edgeCauchyRiemann_approx {F : ℂ → ℂ} {γ : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    {Z : Set ℂ} (hZ : IsCompact Z) (hγ : ContinuousOn γ (Icc a b))
    (hF : ContinuousOn F (γ '' Icc a b)) (hne : ∀ x ∈ Icc a b, ∀ z ∈ Z, γ x ≠ z)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, 0 < N ∧ ∀ z ∈ Z,
      ‖edgeCauchyIntegral F γ a b z - edgeCauchyRiemann F γ a b N z‖ ≤ ε := by
  classical
  rcases eq_or_lt_of_le hab with rfl | hlt
  · refine ⟨1, one_pos, fun z _ => ?_⟩
    simp only [edgeCauchyIntegral, edgeCauchyRiemann, intervalIntegral.integral_same]
    have : (a - a) / (1 : ℕ) = 0 := by norm_num
    simp [hε.le]
  · set Φ : ℝ × ℂ → ℂ := fun p => F (γ p.1) * (γ p.1 - p.2)⁻¹ with hΦ
    have hcompact : IsCompact (Icc a b ×ˢ Z) := (isCompact_Icc).prod hZ
    have hcont : ContinuousOn Φ (Icc a b ×ˢ Z) := continuousOn_edgeCauchyIntegrand hγ hF hne
    have huc : UniformContinuousOn Φ (Icc a b ×ˢ Z) :=
      hcompact.uniformContinuousOn_of_continuous hcont
    set η : ℝ := ε / (2 * (b - a)) with hηdef
    have hηpos : 0 < η := by
      rw [hηdef]
      have : 0 < b - a := by linarith
      positivity
    obtain ⟨δ, hδ, hδΦ⟩ := (Metric.uniformContinuousOn_iff.1 huc) η hηpos
    obtain ⟨N, hN⟩ := exists_nat_gt ((b - a) / δ)
    have hNpos : 0 < N := by
      by_contra hcon
      push Not at hcon
      have hN0 : N = 0 := Nat.le_zero.1 hcon
      rw [hN0] at hN
      have : 0 < (b - a) / δ := by
        have : 0 < b - a := by linarith
        positivity
      simp at hN
      linarith
    have hNne : (0:ℝ) < (N : ℝ) := by exact_mod_cast hNpos
    have hcell : (b - a) / N < δ := by
      rw [div_lt_iff₀ hNne]
      rw [div_lt_iff₀ hδ] at hN
      linarith
    refine ⟨N, hNpos, fun z hz => ?_⟩
    have hnode : ∀ i, i ≤ N → uniformNode a b N i ∈ Icc a b := by
      intro i hi
      have hi' : (i : ℝ) ≤ (N : ℝ) := by exact_mod_cast hi
      have h0 : (0:ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
      constructor
      · simp only [uniformNode]
        have : 0 ≤ (i : ℝ) * (b - a) / N := by
          have : (0:ℝ) ≤ b - a := by linarith
          positivity
        linarith
      · simp only [uniformNode]
        have hle : (i : ℝ) * (b - a) / N ≤ (b - a) := by
          rw [div_le_iff₀ hNne]
          nlinarith
        linarith
    have hmono : ∀ i, uniformNode a b N i ≤ uniformNode a b N (i + 1) := by
      intro i
      have := uniformNode_succ_sub (a := a) (b := b) hNpos i
      have hpos : (0:ℝ) ≤ (b - a) / N := by
        have : (0:ℝ) ≤ b - a := by linarith
        positivity
      linarith
    have hsub : ∀ i, i < N → Set.uIoc (uniformNode a b N i) (uniformNode a b N (i + 1)) ⊆
        Icc a b := by
      intro i hi x hx
      have h1 := hnode i (le_of_lt hi)
      have h2 := hnode (i + 1) hi
      rw [Set.uIoc_of_le (hmono i)] at hx
      exact ⟨le_trans h1.1 (le_of_lt hx.1), le_trans hx.2 h2.2⟩
    have hcontz : ContinuousOn (fun x => F (γ x) * (γ x - z)⁻¹) (Icc a b) := by
      have h1 : ContinuousOn (fun x => F (γ x)) (Icc a b) :=
        hF.comp hγ (fun x hx => ⟨x, hx, rfl⟩)
      refine h1.mul (ContinuousOn.inv₀ (hγ.sub continuousOn_const) ?_)
      intro x hx
      exact sub_ne_zero.2 (hne x hx z hz)
    have hint : ∀ i < N, IntervalIntegrable (fun x => F (γ x) * (γ x - z)⁻¹) volume
        (uniformNode a b N i) (uniformNode a b N (i + 1)) := by
      intro i hi
      refine ContinuousOn.intervalIntegrable (hcontz.mono ?_)
      rw [Set.uIcc_of_le (hmono i)]
      exact Set.Icc_subset_Icc (hnode i (le_of_lt hi)).1 (hnode (i + 1) hi).2
    have hmod : ∀ i < N, ∀ x ∈ Set.uIoc (uniformNode a b N i) (uniformNode a b N (i + 1)),
        ‖(fun x => F (γ x) * (γ x - z)⁻¹) x -
          (fun x => F (γ x) * (γ x - z)⁻¹) (uniformNode a b N i)‖ ≤ η := by
      intro i hi x hx
      have hxab : x ∈ Icc a b := hsub i hi hx
      have hiab : uniformNode a b N i ∈ Icc a b := hnode i (le_of_lt hi)
      have hdist : dist ((x, z) : ℝ × ℂ) ((uniformNode a b N i, z) : ℝ × ℂ) < δ := by
        rw [Set.uIoc_of_le (hmono i)] at hx
        have h1 : uniformNode a b N i < x := hx.1
        have h2 : x ≤ uniformNode a b N (i + 1) := hx.2
        have h3 := uniformNode_succ_sub (a := a) (b := b) hNpos i
        have hd1 : dist x (uniformNode a b N i) < δ := by
          rw [Real.dist_eq, abs_of_pos (by linarith)]
          linarith
        rw [Prod.dist_eq, dist_self]
        exact max_lt hd1 hδ
      have := hδΦ ⟨x, z⟩ ⟨hxab, hz⟩ ⟨uniformNode a b N i, z⟩ ⟨hiab, hz⟩ hdist
      rw [Complex.dist_eq] at this
      exact le_of_lt this
    have hRiem := norm_intervalIntegral_sub_uniformRiemannSum_le (h := fun x =>
      F (γ x) * (γ x - z)⁻¹) hab hNpos hint hηpos.le hmod
    have hfin : (b - a) * η ≤ ε := by
      have hba : 0 < b - a := by linarith
      have hval : (b - a) * η = ε / 2 := by
        rw [hηdef]
        field_simp
      rw [hval]
      linarith
    calc ‖edgeCauchyIntegral F γ a b z - edgeCauchyRiemann F γ a b N z‖
        ≤ (b - a) * η := hRiem
      _ ≤ ε := hfin

end

end GaloisForLFunctions.HTGeometry
