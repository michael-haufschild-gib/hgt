import GaloisForLFunctions.RHTower.BurnolCoPoissonSourceSpace
import GaloisForLFunctions.RHTower.BurnolSoninDilationMellin

/-!
# The normalized dilation moves co-Poisson sources down the aperture ladder

The co-Poisson sum intertwines the normalized `L²` dilation with the dilation of its seed:
`√ρ · P_g(ρ t) = P_h(t)` for `h(u) = √ρ · g(ρ u)`.  Seed integrability and compact multiplicative
support are preserved, and for `r⁻¹ ≤ ρ ≤ r` the dilated support still lies in the window of the
shrunk aperture `r⁻¹ b`.

Consequently both `U_r` and `U_r^*` carry the closed co-Poisson source space at aperture `b` into
the closed co-Poisson source space at aperture `r⁻¹ b`.
-/

open Complex Real MeasureTheory Set Filter Topology

noncomputable section

namespace RHTower

/-- The seed of the dilated co-Poisson source. -/
def dilateSeed (ρ : ℝ) (g : ℝ → ℂ) : ℝ → ℂ := fun u => (Real.sqrt ρ : ℂ) * g (ρ * u)

theorem integrable_dilateSeed {ρ : ℝ} (hρ : 0 < ρ) {g : ℝ → ℂ} (hg : Integrable g) :
    Integrable (dilateSeed ρ g) :=
  (hg.comp_mul_left' hρ.ne').const_mul (Real.sqrt ρ : ℂ)

theorem support_dilateSeed_subset {ρ b r : ℝ} (hρ : 0 < ρ) (hb : 0 < b) (hr : 0 < r)
    (hlo : r⁻¹ ≤ ρ) (hhi : ρ ≤ r) {g : ℝ → ℂ}
    (hg : Function.support g ⊆ Icc b b⁻¹) :
    Function.support (dilateSeed ρ g) ⊆ Icc (r⁻¹ * b) (r⁻¹ * b)⁻¹ := by
  intro u hu
  have hgu : g (ρ * u) ≠ 0 := fun h => hu (by simp [dilateSeed, h])
  obtain ⟨h1, h2⟩ := hg hgu
  have hu0 : 0 < u := by
    rcases le_or_gt u 0 with h | h
    · nlinarith
    · exact h
  have hone : 1 ≤ ρ * r := by
    have h := mul_le_mul_of_nonneg_right hlo hr.le
    rwa [inv_mul_cancel₀ hr.ne'] at h
  have hbinv : 0 < b⁻¹ := inv_pos.mpr hb
  refine ⟨?_, ?_⟩
  · rw [show r⁻¹ * b = b / r from by ring, div_le_iff₀ hr]
    nlinarith
  · rw [mul_inv, inv_inv]
    nlinarith

/-- The co-Poisson sum intertwines the seed dilation with the normalized `L²` dilation. -/
theorem burnolCoPoissonRightSum_dilateSeed {ρ : ℝ} (hρ : 0 < ρ) (g : ℝ → ℂ) (t : ℝ) :
    burnolCoPoissonRightSum (dilateSeed ρ g) t =
      (Real.sqrt ρ : ℂ) * burnolCoPoissonRightSum g (ρ * t) := by
  have habs : |ρ * t| = ρ * |t| := by rw [abs_mul, abs_of_pos hρ]
  have hsum : (∑' n : ℕ, (((n + 1 : ℕ) : ℝ) : ℂ)⁻¹ * dilateSeed ρ g (|t| / ((n + 1 : ℕ) : ℝ))) =
      (Real.sqrt ρ : ℂ) *
        ∑' n : ℕ, (((n + 1 : ℕ) : ℝ) : ℂ)⁻¹ * g (|ρ * t| / ((n + 1 : ℕ) : ℝ)) := by
    rw [← tsum_mul_left]
    refine tsum_congr fun n => ?_
    have harg : ρ * (|t| / ((n + 1 : ℕ) : ℝ)) = |ρ * t| / ((n + 1 : ℕ) : ℝ) := by
      rw [habs]; ring
    simp only [dilateSeed, harg]
    ring
  have hconst : (∫ y in Ioi (0 : ℝ), ((y : ℂ)⁻¹ * dilateSeed ρ g y⁻¹)) =
      (Real.sqrt ρ : ℂ) * ∫ y in Ioi (0 : ℝ), ((y : ℂ)⁻¹ * g y⁻¹) := by
    have hsub := MeasureTheory.integral_comp_mul_left_Ioi
      (fun v : ℝ => ((v : ℂ)⁻¹ * g v⁻¹)) 0 (inv_pos.mpr hρ)
    rw [mul_zero, inv_inv] at hsub
    have hpt : (∫ x in Ioi (0 : ℝ), ((((ρ⁻¹ * x : ℝ)) : ℂ)⁻¹ * g (ρ⁻¹ * x)⁻¹)) =
        (ρ : ℂ) * ∫ x in Ioi (0 : ℝ), ((x : ℂ)⁻¹ * g (ρ * x⁻¹)) := by
      rw [← integral_const_mul]
      refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
      have hx0 : (0 : ℝ) < x := hx
      have harg : (ρ⁻¹ * x)⁻¹ = ρ * x⁻¹ := by field_simp
      have hcast : (((ρ⁻¹ * x : ℝ)) : ℂ)⁻¹ = (ρ : ℂ) * ((x : ℂ))⁻¹ := by
        push_cast
        field_simp
      rw [harg, hcast]
      ring
    rw [hpt, Complex.real_smul] at hsub
    have hρne : ((ρ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hρ.ne'
    have hA : (∫ x in Ioi (0 : ℝ), ((x : ℂ)⁻¹ * g (ρ * x⁻¹))) =
        ∫ x in Ioi (0 : ℝ), ((x : ℂ)⁻¹ * g x⁻¹) :=
      mul_left_cancel₀ hρne hsub
    rw [← hA, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
    simp only [dilateSeed]
    ring
  rw [burnolCoPoissonRightSum, burnolCoPoissonRightSum, hsum, hconst, mul_sub]

/-- The normalized dilation of a co-Poisson source is a co-Poisson source at the shrunk
aperture. -/
def BurnolCoPoissonSource.dilate {b r ρ : ℝ} (hb : 0 < b) (hr : 0 < r) (hρ : 0 < ρ)
    (hlo : r⁻¹ ≤ ρ) (hhi : ρ ≤ r) (src : BurnolCoPoissonSource b)
    (hmem : evenDilationCLM ρ hρ (src.vector : evenSubspace) ∈ soninExtendedSpace (r⁻¹ * b)) :
    BurnolCoPoissonSource (r⁻¹ * b) where
  seed := dilateSeed ρ src.seed
  seed_integrable := integrable_dilateSeed hρ src.seed_integrable
  seed_support := support_dilateSeed_subset hρ hb hr hlo hhi src.seed_support
  vector := ⟨evenDilationCLM ρ hρ (src.vector : evenSubspace), hmem⟩
  vector_eq_sum := by
    have hdil := dilation_ae ρ hρ (((src.vector : soninExtendedSpace b) : evenSubspace) : SoninL2)
    have hpull := (realMul_quasiMeasurePreserving ρ hρ.ne').ae src.vector_eq_sum
    filter_upwards [hdil, hpull] with x hx hy
    change (dilation ρ hρ
      (((src.vector : soninExtendedSpace b) : evenSubspace) : SoninL2) : ℝ → ℂ) x = _
    rw [hx, hy, burnolCoPoissonRightSum_dilateSeed hρ src.seed x]

/-- The forward dilation of a source generator is a source generator at the shrunk aperture. -/
theorem evenDilation_vector_mem_generatorSet {b r : ℝ} (hb : 0 < b) (hr1 : 1 ≤ r)
    (src : BurnolCoPoissonSource b) :
    evenDilationCLM r (lt_of_lt_of_le zero_lt_one hr1) (src.vector : evenSubspace) ∈
      burnolCoPoissonGeneratorSet (r⁻¹ * b) := by
  have hr : 0 < r := lt_of_lt_of_le zero_lt_one hr1
  have hmem := evenDilation_mem_soninExtendedSpace_inv_mul hb hr1 src.vector.property
  exact ⟨BurnolCoPoissonSource.dilate hb hr hr (by
      calc r⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hr1
        _ ≤ r := hr1) le_rfl src hmem, Or.inl rfl⟩

/-- The inverse dilation of a source generator is a source generator at the shrunk aperture. -/
theorem evenInverseDilation_vector_mem_generatorSet {b r : ℝ} (hb : 0 < b) (hr1 : 1 ≤ r)
    (src : BurnolCoPoissonSource b) :
    evenDilationCLM r⁻¹ (inv_pos.mpr (lt_of_lt_of_le zero_lt_one hr1))
        (src.vector : evenSubspace) ∈ burnolCoPoissonGeneratorSet (r⁻¹ * b) := by
  have hr : 0 < r := lt_of_lt_of_le zero_lt_one hr1
  have hmem := evenInverseDilation_mem_soninExtendedSpace_inv_mul hb hr1 src.vector.property
  exact ⟨BurnolCoPoissonSource.dilate hb hr (inv_pos.mpr hr) le_rfl (by
      calc r⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hr1
        _ ≤ r := hr1) src hmem, Or.inl rfl⟩

theorem soninCosineUnitary_evenDilation_inv {r : ℝ} (hr : 0 < r) (v : evenSubspace) :
    evenDilationCLM r hr (soninCosineUnitary v) =
      soninCosineUnitary (evenDilationCLM r⁻¹ (inv_pos.mpr hr) v) := by
  have h := soninCosineUnitary_evenDilation r hr (soninCosineUnitary v)
  rw [soninCosineUnitary_involutive] at h
  have h2 := congrArg soninCosineUnitary h
  rw [soninCosineUnitary_involutive] at h2
  exact h2

/-- Every generator at aperture `b` is carried by both normalized dilations into the closed source
space at the shrunk aperture. -/
theorem generatorSet_dilate_mem_sourceSpace {b r : ℝ} (hb : 0 < b) (hr1 : 1 ≤ r)
    {f : evenSubspace} (hf : f ∈ burnolCoPoissonGeneratorSet b) :
    evenDilationCLM r (lt_of_lt_of_le zero_lt_one hr1) f ∈
      burnolCoPoissonSourceSpace (r⁻¹ * b) := by
  have hr : 0 < r := lt_of_lt_of_le zero_lt_one hr1
  refine (burnolCoPoissonAlgebraicSourceSpace (r⁻¹ * b)).le_topologicalClosure
    (Submodule.subset_span ?_)
  obtain ⟨g, rfl | rfl⟩ := hf
  · exact evenDilation_vector_mem_generatorSet hb hr1 g
  · rw [soninCosineUnitary_evenDilation_inv hr]
    exact burnolCoPoissonGeneratorSet_cosine
      (evenInverseDilation_vector_mem_generatorSet hb hr1 g)

theorem generatorSet_inverseDilate_mem_sourceSpace {b r : ℝ} (hb : 0 < b) (hr1 : 1 ≤ r)
    {f : evenSubspace} (hf : f ∈ burnolCoPoissonGeneratorSet b) :
    evenDilationCLM r⁻¹ (inv_pos.mpr (lt_of_lt_of_le zero_lt_one hr1)) f ∈
      burnolCoPoissonSourceSpace (r⁻¹ * b) := by
  have hr : 0 < r := lt_of_lt_of_le zero_lt_one hr1
  refine (burnolCoPoissonAlgebraicSourceSpace (r⁻¹ * b)).le_topologicalClosure
    (Submodule.subset_span ?_)
  obtain ⟨g, rfl | rfl⟩ := hf
  · exact evenInverseDilation_vector_mem_generatorSet hb hr1 g
  · rw [← soninCosineUnitary_evenDilation r hr]
    exact burnolCoPoissonGeneratorSet_cosine
      (evenDilation_vector_mem_generatorSet hb hr1 g)

/-- **The forward dilation lowers the co-Poisson source space one aperture step.** -/
theorem evenDilation_mem_coPoissonSourceSpace {b r : ℝ} (hb : 0 < b) (hr1 : 1 ≤ r)
    {f : evenSubspace} (hf : f ∈ burnolCoPoissonSourceSpace b) :
    evenDilationCLM r (lt_of_lt_of_le zero_lt_one hr1) f ∈
      burnolCoPoissonSourceSpace (r⁻¹ * b) := by
  have hr : 0 < r := lt_of_lt_of_le zero_lt_one hr1
  let U := evenDilationCLM r hr
  let D := burnolCoPoissonSourceSpace (r⁻¹ * b)
  have hclosed : IsClosed ((D.comap (U : evenSubspace →ₗ[ℂ] evenSubspace) :
      Submodule ℂ evenSubspace) : Set evenSubspace) :=
    (isClosed_burnolCoPoissonSourceSpace (r⁻¹ * b)).preimage U.continuous
  have hle : burnolCoPoissonAlgebraicSourceSpace b ≤
      D.comap (U : evenSubspace →ₗ[ℂ] evenSubspace) := by
    rw [burnolCoPoissonAlgebraicSourceSpace, Submodule.span_le]
    intro x hx
    exact generatorSet_dilate_mem_sourceSpace hb hr1 hx
  exact (burnolCoPoissonAlgebraicSourceSpace b).topologicalClosure_minimal hle hclosed hf

/-- **The adjoint dilation lowers the co-Poisson source space one aperture step.** -/
theorem evenInverseDilation_mem_coPoissonSourceSpace {b r : ℝ} (hb : 0 < b) (hr1 : 1 ≤ r)
    {f : evenSubspace} (hf : f ∈ burnolCoPoissonSourceSpace b) :
    evenDilationCLM r⁻¹ (inv_pos.mpr (lt_of_lt_of_le zero_lt_one hr1)) f ∈
      burnolCoPoissonSourceSpace (r⁻¹ * b) := by
  have hr : 0 < r := lt_of_lt_of_le zero_lt_one hr1
  let U := evenDilationCLM r⁻¹ (inv_pos.mpr hr)
  let D := burnolCoPoissonSourceSpace (r⁻¹ * b)
  have hclosed : IsClosed ((D.comap (U : evenSubspace →ₗ[ℂ] evenSubspace) :
      Submodule ℂ evenSubspace) : Set evenSubspace) :=
    (isClosed_burnolCoPoissonSourceSpace (r⁻¹ * b)).preimage U.continuous
  have hle : burnolCoPoissonAlgebraicSourceSpace b ≤
      D.comap (U : evenSubspace →ₗ[ℂ] evenSubspace) := by
    rw [burnolCoPoissonAlgebraicSourceSpace, Submodule.span_le]
    intro x hx
    exact generatorSet_inverseDilate_mem_sourceSpace hb hr1 hx
  exact (burnolCoPoissonAlgebraicSourceSpace b).topologicalClosure_minimal hle hclosed hf

end RHTower
