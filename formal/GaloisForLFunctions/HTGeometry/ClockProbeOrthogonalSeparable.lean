import GaloisForLFunctions.HTGeometry.ClockProbeSeparablePotential

/-!
# Separable potentials along metric-orthogonal directions

The two-factor construction assumed one factor varies along a single coordinate. That is not the
right condition: what makes the product work is the vanishing of the carré du champ between the two
factors, and for covector lifts that is exactly **metric orthogonality** of the two covectors,

`⟨n₁, n₂⟩_G = ∑ᵢ (εᵢ)⁻¹ n₁ᵢ n₂ᵢ = 0`.

This file proves the Leibniz rule for the flat d'Alembertian at Picard–Lindelöf regularity in its
full form, `□(fg) = f□g + g□f + 2Γ(f,g)`, and deduces probes for

`V(x) = V₁(⟪n₁,x⟫) + V₂(⟪n₂,x⟫)`

for any pair of non-null, `G`-orthogonal covectors and arbitrary `C¹` profiles. Coordinate
directions are the special case; boosted pairs such as `(2,1,0,…)` and `(1,2,0,…)` on Minkowski
space are not.
-/

namespace GaloisForLFunctions.HTGeometry

open Set

open scoped ContDiff

variable {d : ℕ}

/-! ## The metric pairing of covectors -/

/-- Metric pairing of two covectors for a constant signature. -/
noncomputable def covectorPairing (eps n₁ n₂ : Fin (d + 1) → ℝ) : ℝ :=
  ∑ i, (eps i)⁻¹ * (n₁ i * n₂ i)

theorem covectorPairing_self (eps n : Fin (d + 1) → ℝ) :
    covectorPairing eps n n = covectorNormConst eps n := rfl

theorem covectorPairing_twoIndex (eps : Fin (d + 1) → ℝ) {j k : Fin (d + 1)} (hjk : j ≠ k)
    (α β γ δ : ℝ) :
    covectorPairing eps (fun i => if i = j then α else if i = k then β else 0)
        (fun i => if i = j then γ else if i = k then δ else 0)
      = (eps j)⁻¹ * (α * γ) + (eps k)⁻¹ * (β * δ) := by
  have hsub : ∑ i ∈ ({j, k} : Finset (Fin (d + 1))), (eps i)⁻¹ *
      ((if i = j then α else if i = k then β else 0) *
        (if i = j then γ else if i = k then δ else 0))
      = ∑ i, (eps i)⁻¹ *
      ((if i = j then α else if i = k then β else 0) *
        (if i = j then γ else if i = k then δ else 0)) := by
    refine Finset.sum_subset (Finset.subset_univ _) ?_
    intro i _ hi
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hi
    rw [if_neg hi.1, if_neg hi.2]
    ring
  rw [covectorPairing, ← hsub, Finset.sum_pair hjk]
  simp [Ne.symm hjk]

/-! ## The Leibniz rule at low regularity -/

/-- **The flat d'Alembertian obeys the second-order Leibniz rule**, needing only differentiable
first partial derivatives. -/
theorem dalembert_mul_of_differentiableAt (eps : Fin (d + 1) → ℝ) (heps : ∀ i, eps i ≠ 0)
    {f g : (Fin (d + 1) → ℝ) → ℝ} {x : Fin (d + 1) → ℝ}
    {U : Set (Fin (d + 1) → ℝ)} (hU : IsOpen U) (hxU : x ∈ U)
    (hfU : ∀ y ∈ U, DifferentiableAt ℝ f y) (hgU : ∀ y ∈ U, DifferentiableAt ℝ g y)
    (hfd : ∀ i, DifferentiableAt ℝ (coordPartial i f) x)
    (hgd : ∀ i, DifferentiableAt ℝ (coordPartial i g) x) :
    (SmoothPseudoMetric.ofSignature eps heps).chart.dalembert (fun y => f y * g y) x
      = f x * (SmoothPseudoMetric.ofSignature eps heps).chart.dalembert g x
        + g x * (SmoothPseudoMetric.ofSignature eps heps).chart.dalembert f x
        + 2 * (SmoothPseudoMetric.ofSignature eps heps).chart.gradPair f g x := by
  have hnhds : U ∈ nhds x := hU.mem_nhds hxU
  have hev : ∀ i : Fin (d + 1), coordPartial i (fun y => f y * g y) =ᶠ[nhds x]
      fun y => f y * coordPartial i g y + g y * coordPartial i f y := by
    intro i
    refine Filter.eventuallyEq_of_mem hnhds ?_
    intro y hy
    exact coordPartial_mul (hfU y hy) (hgU y hy) i
  have hdiffprod : ∀ i : Fin (d + 1),
      DifferentiableAt ℝ (coordPartial i (fun y => f y * g y)) x := by
    intro i
    rw [(hev i).differentiableAt_iff]
    exact ((hfU x hxU).mul (hgd i)).add ((hgU x hxU).mul (hfd i))
  have hsecond : ∀ i : Fin (d + 1),
      coordPartial i (coordPartial i (fun y => f y * g y)) x
        = f x * coordPartial i (coordPartial i g) x
          + g x * coordPartial i (coordPartial i f) x
          + 2 * (coordPartial i f x * coordPartial i g x) := by
    intro i
    have hadd := coordPartial_add (f := fun y => f y * coordPartial i g y)
      (g := fun y => g y * coordPartial i f y) (x := x)
      ((hfU x hxU).mul (hgd i)) ((hgU x hxU).mul (hfd i)) i
    rw [coordPartial_congr (hev i) i, hadd,
      coordPartial_mul (hfU x hxU) (hgd i) i, coordPartial_mul (hgU x hxU) (hfd i) i]
    ring
  rw [ofSignature_dalembert_of_differentiableAt eps heps hdiffprod,
    ofSignature_dalembert_of_differentiableAt eps heps hfd,
    ofSignature_dalembert_of_differentiableAt eps heps hgd,
    ofSignature_gradPair, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by rw [hsecond i]; ring

/-! ## The carré du champ of two covector lifts -/

theorem gradPair_covectorLift_pair (eps : Fin (d + 1) → ℝ) (heps : ∀ i, eps i ≠ 0)
    {n₁ n₂ : Fin (d + 1) → ℝ} {w₁ w₂ : ℝ → ℝ} {c₁ c₂ : ℝ} {x : Fin (d + 1) → ℝ}
    (h₁ : HasDerivAt w₁ c₁ (covectorPhase n₁ x)) (h₂ : HasDerivAt w₂ c₂ (covectorPhase n₂ x)) :
    (SmoothPseudoMetric.ofSignature eps heps).chart.gradPair
        (covectorLift n₁ w₁) (covectorLift n₂ w₂) x
      = covectorPairing eps n₁ n₂ * (c₁ * c₂) := by
  rw [ofSignature_gradPair, covectorPairing, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [coordPartial_covectorLift h₁ i, coordPartial_covectorLift h₂ i]
  ring

/-! ## Probes for an orthogonally separable potential -/

/-- **Local probes for a sum potential along two metric-orthogonal directions.** -/
theorem exists_orthogonal_separable_localProbe (eps : Fin (d + 1) → ℝ) (heps : ∀ i, eps i ≠ 0)
    {n₁ n₂ : Fin (d + 1) → ℝ} (hortho : covectorPairing eps n₁ n₂ = 0)
    (hQ₁ : covectorNormConst eps n₁ ≠ 0) (hQ₂ : covectorNormConst eps n₂ ≠ 0)
    {V₁ V₂ : ℝ → ℝ} (hV₁ : ContDiff ℝ 1 V₁) (hV₂ : ContDiff ℝ 1 V₂) (b₁ b₂ : ℝ) :
    ∃ (u : (Fin (d + 1) → ℝ) → ℝ) (ε : ℝ), 0 < ε ∧
      (∀ x : Fin (d + 1) → ℝ, covectorPhase n₁ x = b₁ → covectorPhase n₂ x = b₂ → u x = 1) ∧
      (∀ x : Fin (d + 1) → ℝ,
        covectorPhase n₁ x ∈ Ioo (b₁ - ε) (b₁ + ε) →
        covectorPhase n₂ x ∈ Ioo (b₂ - ε) (b₂ + ε) →
        SolvesPotentialWaveAt (SmoothPseudoMetric.ofSignature eps heps).chart.dalembert
          (fun y => V₁ (covectorPhase n₁ y) + V₂ (covectorPhase n₂ y)) u x) := by
  obtain ⟨w₁, dw₁, ddw₁, ε₁, hε₁, hw₁a, hd₁, hdd₁, heq₁⟩ :=
    exists_localLinearProbe (p := fun _ => (0 : ℝ)) contDiff_const
      (hV₁.div contDiff_const fun _ => hQ₁) b₁
  obtain ⟨w₂, dw₂, ddw₂, ε₂, hε₂, hw₂a, hd₂, hdd₂, heq₂⟩ :=
    exists_localLinearProbe (p := fun _ => (0 : ℝ)) contDiff_const
      (hV₂.div contDiff_const fun _ => hQ₂) b₂
  refine ⟨fun y => covectorLift n₁ w₁ y * covectorLift n₂ w₂ y, min ε₁ ε₂,
    lt_min hε₁ hε₂, ?_, ?_⟩
  · intro x h1 h2
    show w₁ (covectorPhase n₁ x) * w₂ (covectorPhase n₂ x) = 1
    rw [h1, h2, hw₁a, hw₂a, one_mul]
  · intro x hx1 hx2
    have hs1 : covectorPhase n₁ x ∈ Ioo (b₁ - ε₁) (b₁ + ε₁) := by
      obtain ⟨p, q⟩ := hx1
      have := min_le_left ε₁ ε₂
      constructor <;> linarith
    have hs2 : covectorPhase n₂ x ∈ Ioo (b₂ - ε₂) (b₂ + ε₂) := by
      obtain ⟨p, q⟩ := hx2
      have := min_le_right ε₁ ε₂
      constructor <;> linarith
    set U : Set (Fin (d + 1) → ℝ) :=
      covectorPhase n₁ ⁻¹' Ioo (b₁ - ε₁) (b₁ + ε₁) ∩
        covectorPhase n₂ ⁻¹' Ioo (b₂ - ε₂) (b₂ + ε₂) with hUdef
    have hU : IsOpen U :=
      (isOpen_Ioo.preimage (continuous_covectorPhase n₁)).inter
        (isOpen_Ioo.preimage (continuous_covectorPhase n₂))
    have hxU : x ∈ U := ⟨hs1, hs2⟩
    have hphase1 : ContDiff ℝ ∞ (covectorPhase (d := d) n₁) := contDiff_covectorPhase n₁
    have hphase2 : ContDiff ℝ ∞ (covectorPhase (d := d) n₂) := contDiff_covectorPhase n₂
    have hfU : ∀ y ∈ U, DifferentiableAt ℝ (covectorLift n₁ w₁) y := by
      intro y hy
      exact ((hd₁ _ hy.1).comp_hasFDerivAt y
        (differentiableAt_of_contDiff_infty hphase1 y).hasFDerivAt).differentiableAt
    have hgU : ∀ y ∈ U, DifferentiableAt ℝ (covectorLift n₂ w₂) y := by
      intro y hy
      exact ((hd₂ _ hy.2).comp_hasFDerivAt y
        (differentiableAt_of_contDiff_infty hphase2 y).hasFDerivAt).differentiableAt
    have hev1 : ∀ i : Fin (d + 1), coordPartial i (covectorLift n₁ w₁) =ᶠ[nhds x]
        fun y => n₁ i * covectorLift n₁ dw₁ y := by
      intro i
      refine Filter.eventuallyEq_of_mem (hU.mem_nhds hxU) ?_
      intro y hy
      exact coordPartial_covectorLift (hd₁ _ hy.1) i
    have hev2 : ∀ i : Fin (d + 1), coordPartial i (covectorLift n₂ w₂) =ᶠ[nhds x]
        fun y => n₂ i * covectorLift n₂ dw₂ y := by
      intro i
      refine Filter.eventuallyEq_of_mem (hU.mem_nhds hxU) ?_
      intro y hy
      exact coordPartial_covectorLift (hd₂ _ hy.2) i
    have hdw1 : DifferentiableAt ℝ (covectorLift (d := d) n₁ dw₁) x :=
      ((hdd₁ _ hs1).comp_hasFDerivAt x
        (differentiableAt_of_contDiff_infty hphase1 x).hasFDerivAt).differentiableAt
    have hdw2 : DifferentiableAt ℝ (covectorLift (d := d) n₂ dw₂) x :=
      ((hdd₂ _ hs2).comp_hasFDerivAt x
        (differentiableAt_of_contDiff_infty hphase2 x).hasFDerivAt).differentiableAt
    have hfd : ∀ i, DifferentiableAt ℝ (coordPartial i (covectorLift n₁ w₁)) x := by
      intro i
      rw [(hev1 i).differentiableAt_iff]
      exact hdw1.const_mul (n₁ i)
    have hgd : ∀ i, DifferentiableAt ℝ (coordPartial i (covectorLift n₂ w₂)) x := by
      intro i
      rw [(hev2 i).differentiableAt_iff]
      exact hdw2.const_mul (n₂ i)
    have hprod := dalembert_mul_of_differentiableAt eps heps hU hxU hfU hgU hfd hgd
    have hgp := gradPair_covectorLift_pair eps heps (hd₁ _ hs1) (hd₂ _ hs2)
    rw [hortho, zero_mul] at hgp
    have hf := dalembert_covectorLift_flat eps heps isOpen_Ioo hd₁ hdd₁ hs1
    have hg := dalembert_covectorLift_flat eps heps isOpen_Ioo hd₂ hdd₂ hs2
    have hE₁ : ddw₁ (covectorPhase n₁ x)
        + V₁ (covectorPhase n₁ x) / covectorNormConst eps n₁ * w₁ (covectorPhase n₁ x) = 0 := by
      have h := heq₁ (covectorPhase n₁ x)
      simpa using h
    have hE₂ : ddw₂ (covectorPhase n₂ x)
        + V₂ (covectorPhase n₂ x) / covectorNormConst eps n₂ * w₂ (covectorPhase n₂ x) = 0 := by
      have h := heq₂ (covectorPhase n₂ x)
      simpa using h
    have hQ1 : covectorNormConst eps n₁ * ddw₁ (covectorPhase n₁ x)
        = -(V₁ (covectorPhase n₁ x) * w₁ (covectorPhase n₁ x)) := by
      field_simp at hE₁
      linarith [hE₁]
    have hQ2 : covectorNormConst eps n₂ * ddw₂ (covectorPhase n₂ x)
        = -(V₂ (covectorPhase n₂ x) * w₂ (covectorPhase n₂ x)) := by
      field_simp at hE₂
      linarith [hE₂]
    show (SmoothPseudoMetric.ofSignature eps heps).chart.dalembert
        (fun y => covectorLift n₁ w₁ y * covectorLift n₂ w₂ y) x
      + (V₁ (covectorPhase n₁ x) + V₂ (covectorPhase n₂ x))
        * (w₁ (covectorPhase n₁ x) * w₂ (covectorPhase n₂ x)) = 0
    rw [hprod, hgp, hf, hg]
    show w₁ (covectorPhase n₁ x) * (covectorNormConst eps n₂ * ddw₂ (covectorPhase n₂ x))
        + w₂ (covectorPhase n₂ x) * (covectorNormConst eps n₁ * ddw₁ (covectorPhase n₁ x))
        + 2 * 0
      + (V₁ (covectorPhase n₁ x) + V₂ (covectorPhase n₂ x))
        * (w₁ (covectorPhase n₁ x) * w₂ (covectorPhase n₂ x)) = 0
    rw [hQ1, hQ2]
    ring

/-- **An orthogonally separable potential is determined by clock data.** -/
theorem orthogonal_separable_potential_determined (eps : Fin (d + 1) → ℝ)
    (heps : ∀ i, eps i ≠ 0) {n₁ n₂ : Fin (d + 1) → ℝ}
    (hortho : covectorPairing eps n₁ n₂ = 0)
    (hQ₁ : covectorNormConst eps n₁ ≠ 0) (hQ₂ : covectorNormConst eps n₂ ≠ 0)
    {V₁ V₂ : ℝ → ℝ} (hV₁ : ContDiff ℝ 1 V₁) (hV₂ : ContDiff ℝ 1 V₂)
    {other : (Fin (d + 1) → ℝ) → ℝ}
    (hother : ∀ (b₁ b₂ : ℝ) (u : (Fin (d + 1) → ℝ) → ℝ) (ε : ℝ), 0 < ε →
      (∀ x : Fin (d + 1) → ℝ,
        covectorPhase n₁ x ∈ Ioo (b₁ - ε) (b₁ + ε) →
        covectorPhase n₂ x ∈ Ioo (b₂ - ε) (b₂ + ε) →
        SolvesPotentialWaveAt (SmoothPseudoMetric.ofSignature eps heps).chart.dalembert
          (fun y => V₁ (covectorPhase n₁ y) + V₂ (covectorPhase n₂ y)) u x) →
      (∀ x : Fin (d + 1) → ℝ,
        covectorPhase n₁ x ∈ Ioo (b₁ - ε) (b₁ + ε) →
        covectorPhase n₂ x ∈ Ioo (b₂ - ε) (b₂ + ε) →
        SolvesPotentialWaveAt (SmoothPseudoMetric.ofSignature eps heps).chart.dalembert
          other u x)) :
    other = fun y => V₁ (covectorPhase n₁ y) + V₂ (covectorPhase n₂ y) := by
  funext x
  obtain ⟨u, ε, hε, hu1, hsolve⟩ :=
    exists_orthogonal_separable_localProbe eps heps hortho hQ₁ hQ₂ hV₁ hV₂
      (covectorPhase n₁ x) (covectorPhase n₂ x)
  have hx1 : covectorPhase n₁ x ∈ Ioo (covectorPhase n₁ x - ε) (covectorPhase n₁ x + ε) := by
    constructor <;> linarith
  have hx2 : covectorPhase n₂ x ∈ Ioo (covectorPhase n₂ x - ε) (covectorPhase n₂ x + ε) := by
    constructor <;> linarith
  refine potential_eq_of_solvesPotentialWaveAt
    (hother _ _ u ε hε hsolve x hx1 hx2) (hsolve x hx1 hx2) ?_
  rw [hu1 x rfl rfl]
  exact one_ne_zero

/-! ## The class is not confined to coordinate directions -/

/-- **A boosted orthogonal pair on Minkowski space.** Neither covector is a coordinate direction,
both are non-null, and they are metric-orthogonal. -/
theorem exists_boosted_orthogonal_pair :
    ∃ n₁ n₂ : Fin (d + 1 + 1) → ℝ,
      covectorPairing (fun i => if (i : ℕ) = 0 then -1 else 1) n₁ n₂ = 0 ∧
      covectorNormConst (fun i => if (i : ℕ) = 0 then -1 else 1) n₁ ≠ 0 ∧
      covectorNormConst (fun i => if (i : ℕ) = 0 then -1 else 1) n₂ ≠ 0 ∧
      n₁ 0 ≠ 0 ∧ n₁ 1 ≠ 0 ∧ n₂ 0 ≠ 0 ∧ n₂ 1 ≠ 0 := by
  classical
  have h01 : (0 : Fin (d + 1 + 1)) ≠ 1 := by simp
  have hv1 : ((1 : Fin (d + 1 + 1)) : ℕ) = 1 := by simp
  refine ⟨fun i => if i = 0 then 2 else if i = 1 then 1 else 0,
    fun i => if i = 0 then 1 else if i = 1 then 2 else 0, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [covectorPairing_twoIndex _ h01]
    norm_num [hv1]
  · rw [← covectorPairing_self, covectorPairing_twoIndex _ h01]
    norm_num [hv1]
  · rw [← covectorPairing_self, covectorPairing_twoIndex _ h01]
    norm_num [hv1]
  · simp
  · simp [Ne.symm h01]
  · simp
  · simp [Ne.symm h01]

end GaloisForLFunctions.HTGeometry
