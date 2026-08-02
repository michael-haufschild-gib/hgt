import GaloisForLFunctions.RHTower.DeningerPoissonSchwartz

/-!
# The Poisson operator is continuous

The decay constants of the two-ended estimates are explicit Schwartz seminorms: the constant of the
large-end estimate is `p_{2N+2,0}` of the function, that of the small-end estimate is
`p_{2N+2,0}` of its Fourier transform.  For the `n`-th derivative of the `s`-th weight the function
is `A_sⁿf`, so every seminorm of `Z_s f` is bounded by a fixed multiple of a Schwartz seminorm of
`A_sⁿf` and of `𝓕A_sⁿf` — and both `A_sⁿ` and `𝓕` are continuous operators on `𝒮(ℝ)`, so those are
bounded by finitely many Schwartz seminorms of `f`.

Summing over the finitely many coordinates of a product seminorm gives the continuity of the
Poisson operator into the radial space.

* `deningerShiftPowCLM` : the powers of `A_s`, as continuous linear maps.
* `exists_bound_seminorm_deningerPoissonSchwartz` : **every Schwartz seminorm of a weight is
  bounded by finitely many Schwartz seminorms of the argument.**
* `exists_bound_shiftedSeminorm_deningerPoisson` : the same for the oscillator seminorms.
* `deningerPoissonLM_bound` : **the Poisson operator is continuous** into the radial space.
-/

open scoped Real SchwartzMap FourierTransform ContDiff NNReal
open Complex MeasureTheory GaloisForLFunctions GaloisForLFunctions.RHTower

noncomputable section

namespace RHTower

/-! ## The powers of the shifted Euler operator -/

/-- The `n`-th power of `A_s = s + θ`, as a continuous linear map. -/
def deningerShiftPowCLM (s : ℤ) : ℕ → (𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ))
  | 0 => ContinuousLinearMap.id ℂ _
  | (n + 1) => (deningerShiftPowCLM s n).comp (deningerShiftCLM s)

theorem deningerShiftPowCLM_apply (s : ℤ) (n : ℕ) (f : 𝓢(ℝ, ℂ)) :
    deningerShiftPowCLM s n f = ((deningerShiftCLM s)^[n]) f := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih =>
    show deningerShiftPowCLM s n (deningerShiftCLM s f) = _
    rw [ih, Function.iterate_succ_apply]

/-! ## Bounding a seminorm of a continuous operator -/

theorem exists_bound_seminorm_comp (T : 𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ)) (p : ℕ) :
    ∃ (K : Finset (ℕ × ℕ)) (C : ℝ), 0 ≤ C ∧ ∀ f : 𝓢(ℝ, ℂ),
      SchwartzMap.seminorm ℂ p 0 (T f) ≤ C * (K.sup (schwartzSeminormFamily ℂ ℝ ℂ)) f := by
  set q : Seminorm ℂ 𝓢(ℝ, ℂ) :=
    (SchwartzMap.seminorm ℂ p 0).comp (T : 𝓢(ℝ, ℂ) →ₗ[ℂ] 𝓢(ℝ, ℂ)) with hq
  have hcont : Continuous q := by
    have hbase : Continuous (SchwartzMap.seminorm ℂ p 0 : 𝓢(ℝ, ℂ) → ℝ) :=
      (schwartz_withSeminorms ℂ ℝ ℂ).continuous_seminorm (p, 0)
    exact hbase.comp T.continuous
  obtain ⟨K, C, _, hC⟩ :=
    Seminorm.bound_of_continuous (schwartz_withSeminorms ℂ ℝ ℂ) q hcont
  refine ⟨K, (C : ℝ), (C : ℝ≥0).coe_nonneg, fun f => ?_⟩
  have h := hC f
  rw [_root_.smul_apply, NNReal.smul_def, smul_eq_mul] at h
  exact h

/-! ## The seminorms of a weighted Poisson sum -/

/-- **Every Schwartz seminorm of a weight of the Poisson sum is bounded by finitely many Schwartz
seminorms of the argument.** -/
theorem exists_bound_seminorm_deningerPoissonSchwartz (s : ℤ) (k n : ℕ) :
    ∃ (K : Finset (ℕ × ℕ)) (C : ℝ), 0 ≤ C ∧ ∀ (f : 𝓢(ℝ, ℂ)) (hf : f ∈ DeningerMeyerCap),
      SchwartzMap.seminorm ℂ k n (deningerPoissonSchwartz s f hf)
        ≤ C * (K.sup (schwartzSeminormFamily ℂ ℝ ℂ)) f := by
  classical
  set N : ℕ := deningerPoissonDecayIndex s with hN
  set p : ℕ := ccmRationalArchimedeanDecayExponent N with hp
  set κ : ℝ := ∑' m : ℤ, ccmRationalArchimedeanPSeriesKernel N m with hκ
  have hκnn : 0 ≤ κ := tsum_nonneg (ccmRationalArchimedeanPSeriesKernel_nonneg N)
  obtain ⟨K₁, C₁, hC₁, hb₁⟩ := exists_bound_seminorm_comp (deningerShiftPowCLM s n) p
  obtain ⟨K₂, C₂, hC₂, hb₂⟩ :=
    exists_bound_seminorm_comp (fourierSCLM.comp (deningerShiftPowCLM s n)) p
  refine ⟨K₁ ∪ K₂, (C₁ + C₂) * κ / 2 * (Nat.factorial k : ℝ), by positivity, fun f hf => ?_⟩
  set h : 𝓢(ℝ, ℂ) := ((deningerShiftCLM s)^[n]) f with hh
  have hhmem : h ∈ DeningerMeyerCap := deningerMeyerCap_shiftCLM_iterate hf s n
  have hsupnn : 0 ≤ ((K₁ ∪ K₂).sup (schwartzSeminormFamily ℂ ℝ ℂ)) f := apply_nonneg _ _
  have hmono₁ : (K₁.sup (schwartzSeminormFamily ℂ ℝ ℂ)) f
      ≤ ((K₁ ∪ K₂).sup (schwartzSeminormFamily ℂ ℝ ℂ)) f := by
    have hle : K₁.sup (schwartzSeminormFamily ℂ ℝ ℂ)
        ≤ (K₁ ∪ K₂).sup (schwartzSeminormFamily ℂ ℝ ℂ) :=
      Finset.sup_mono Finset.subset_union_left
    exact hle f
  have hmono₂ : (K₂.sup (schwartzSeminormFamily ℂ ℝ ℂ)) f
      ≤ ((K₁ ∪ K₂).sup (schwartzSeminormFamily ℂ ℝ ℂ)) f := by
    have hle : K₂.sup (schwartzSeminormFamily ℂ ℝ ℂ)
        ≤ (K₁ ∪ K₂).sup (schwartzSeminormFamily ℂ ℝ ℂ) :=
      Finset.sup_mono Finset.subset_union_right
    exact hle f
  have hconst₁ : ccmRationalArchimedeanDecayConstant h N
      ≤ C₁ * κ * ((K₁ ∪ K₂).sup (schwartzSeminormFamily ℂ ℝ ℂ)) f := by
    rw [ccmRationalArchimedeanDecayConstant]
    have hb := hb₁ f
    rw [deningerShiftPowCLM_apply] at hb
    calc SchwartzMap.seminorm ℂ p 0 h * κ
        ≤ (C₁ * (K₁.sup (schwartzSeminormFamily ℂ ℝ ℂ)) f) * κ :=
          mul_le_mul_of_nonneg_right hb hκnn
      _ ≤ (C₁ * ((K₁ ∪ K₂).sup (schwartzSeminormFamily ℂ ℝ ℂ)) f) * κ := by
          refine mul_le_mul_of_nonneg_right ?_ hκnn
          exact mul_le_mul_of_nonneg_left hmono₁ hC₁
      _ = C₁ * κ * ((K₁ ∪ K₂).sup (schwartzSeminormFamily ℂ ℝ ℂ)) f := by ring
  have hconst₂ : ccmRationalArchimedeanDecayConstant (𝓕 h) N
      ≤ C₂ * κ * ((K₁ ∪ K₂).sup (schwartzSeminormFamily ℂ ℝ ℂ)) f := by
    rw [ccmRationalArchimedeanDecayConstant]
    have hb := hb₂ f
    have hfun : (fourierSCLM.comp (deningerShiftPowCLM s n)) f = 𝓕 h := by
      show fourierSCLM (deningerShiftPowCLM s n f) = 𝓕 h
      rw [deningerShiftPowCLM_apply, fourierSCLM_eq]
    rw [hfun] at hb
    calc SchwartzMap.seminorm ℂ p 0 (𝓕 h) * κ
        ≤ (C₂ * (K₂.sup (schwartzSeminormFamily ℂ ℝ ℂ)) f) * κ :=
          mul_le_mul_of_nonneg_right hb hκnn
      _ ≤ (C₂ * ((K₁ ∪ K₂).sup (schwartzSeminormFamily ℂ ℝ ℂ)) f) * κ := by
          refine mul_le_mul_of_nonneg_right ?_ hκnn
          exact mul_le_mul_of_nonneg_left hmono₂ hC₂
      _ = C₂ * κ * ((K₁ ∪ K₂).sup (schwartzSeminormFamily ℂ ℝ ℂ)) f := by ring
  refine SchwartzMap.seminorm_le_bound ℂ k n _ (by positivity) fun t => ?_
  have hiter : ‖iteratedFDeriv ℝ n (deningerPoissonSchwartz s f hf : ℝ → ℂ) t‖
      = ‖deningerPoissonWeight s h t‖ := by
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    show ‖iteratedDeriv n (deningerPoissonWeight s f) t‖ = _
    rw [iteratedDeriv_deningerPoissonWeight]
  rw [hiter]
  have hbound : ‖t‖ ^ k * ‖deningerPoissonWeight s h t‖
      ≤ ((C₁ + C₂) * κ * ((K₁ ∪ K₂).sup (schwartzSeminormFamily ℂ ℝ ℂ)) f) / 2
        * (Nat.factorial k : ℝ) := by
    have hfacnn : (0 : ℝ) ≤ (Nat.factorial k : ℝ) := by positivity
    rcases le_total 0 t with ht | ht
    · refine (norm_deningerPoissonWeight_le_of_nonneg s k hhmem ht).trans ?_
      refine mul_le_mul_of_nonneg_right ?_ hfacnn
      have hstep : ccmRationalArchimedeanDecayConstant h N
          ≤ (C₁ + C₂) * κ * ((K₁ ∪ K₂).sup (schwartzSeminormFamily ℂ ℝ ℂ)) f := by
        refine hconst₁.trans ?_
        have : C₁ * κ ≤ (C₁ + C₂) * κ := by nlinarith
        exact mul_le_mul_of_nonneg_right this hsupnn
      linarith
    · refine (norm_deningerPoissonWeight_le_of_nonpos s k hhmem ht).trans ?_
      refine mul_le_mul_of_nonneg_right ?_ hfacnn
      have hstep : ccmRationalArchimedeanDecayConstant (𝓕 h) N
          ≤ (C₁ + C₂) * κ * ((K₁ ∪ K₂).sup (schwartzSeminormFamily ℂ ℝ ℂ)) f := by
        refine hconst₂.trans ?_
        have : C₂ * κ ≤ (C₁ + C₂) * κ := by nlinarith
        exact mul_le_mul_of_nonneg_right this hsupnn
      linarith
  refine hbound.trans (le_of_eq ?_)
  ring


/-! ## Finite suprema, the oscillator seminorms, and the product seminorm -/

theorem exists_bound_schwartzSup_deningerPoissonSchwartz (s : ℤ) (K₀ : Finset (ℕ × ℕ)) :
    ∃ (K : Finset (ℕ × ℕ)) (C : ℝ), 0 ≤ C ∧ ∀ (f : 𝓢(ℝ, ℂ)) (hf : f ∈ DeningerMeyerCap),
      (K₀.sup (schwartzSeminormFamily ℂ ℝ ℂ)) (deningerPoissonSchwartz s f hf)
        ≤ C * (K.sup (schwartzSeminormFamily ℂ ℝ ℂ)) f := by
  classical
  induction K₀ using Finset.induction with
  | empty =>
    refine ⟨∅, 0, le_refl 0, fun f hf => ?_⟩
    simp
  | insert a K₀ ha ih =>
    obtain ⟨K, C, hC, hb⟩ := ih
    obtain ⟨K', C', hC', hb'⟩ := exists_bound_seminorm_deningerPoissonSchwartz s a.1 a.2
    refine ⟨K ∪ K', C + C', by positivity, fun f hf => ?_⟩
    have hsupnn : 0 ≤ ((K ∪ K').sup (schwartzSeminormFamily ℂ ℝ ℂ)) f := apply_nonneg _ _
    have hlemono : K.sup (schwartzSeminormFamily ℂ ℝ ℂ)
        ≤ (K ∪ K').sup (schwartzSeminormFamily ℂ ℝ ℂ) :=
      Finset.sup_mono Finset.subset_union_left
    have hlemono' : K'.sup (schwartzSeminormFamily ℂ ℝ ℂ)
        ≤ (K ∪ K').sup (schwartzSeminormFamily ℂ ℝ ℂ) :=
      Finset.sup_mono Finset.subset_union_right
    have hmono : (K.sup (schwartzSeminormFamily ℂ ℝ ℂ)) f
        ≤ ((K ∪ K').sup (schwartzSeminormFamily ℂ ℝ ℂ)) f := hlemono f
    have hmono' : (K'.sup (schwartzSeminormFamily ℂ ℝ ℂ)) f
        ≤ ((K ∪ K').sup (schwartzSeminormFamily ℂ ℝ ℂ)) f := hlemono' f
    rw [Finset.sup_insert, Seminorm.sup_apply]
    refine max_le ?_ ?_
    · have hstep : (schwartzSeminormFamily ℂ ℝ ℂ a) (deningerPoissonSchwartz s f hf)
          ≤ C' * (K'.sup (schwartzSeminormFamily ℂ ℝ ℂ)) f := hb' f hf
      calc (schwartzSeminormFamily ℂ ℝ ℂ a) (deningerPoissonSchwartz s f hf)
          ≤ C' * (K'.sup (schwartzSeminormFamily ℂ ℝ ℂ)) f := hstep
        _ ≤ C' * ((K ∪ K').sup (schwartzSeminormFamily ℂ ℝ ℂ)) f :=
            mul_le_mul_of_nonneg_left hmono' hC'
        _ ≤ (C + C') * ((K ∪ K').sup (schwartzSeminormFamily ℂ ℝ ℂ)) f := by
            refine mul_le_mul_of_nonneg_right ?_ hsupnn
            linarith
    · calc (K₀.sup (schwartzSeminormFamily ℂ ℝ ℂ)) (deningerPoissonSchwartz s f hf)
          ≤ C * (K.sup (schwartzSeminormFamily ℂ ℝ ℂ)) f := hb f hf
        _ ≤ C * ((K ∪ K').sup (schwartzSeminormFamily ℂ ℝ ℂ)) f :=
            mul_le_mul_of_nonneg_left hmono hC
        _ ≤ (C + C') * ((K ∪ K').sup (schwartzSeminormFamily ℂ ℝ ℂ)) f := by
            refine mul_le_mul_of_nonneg_right ?_ hsupnn
            linarith

/-- **Every oscillator seminorm of a weight of the Poisson sum is bounded by finitely many
Schwartz seminorms of the argument.** -/
theorem exists_bound_shiftedSeminorm_deningerPoisson (s : ℤ) (m : ℕ) :
    ∃ (K : Finset (ℕ × ℕ)) (C : ℝ), 0 ≤ C ∧ ∀ (f : 𝓢(ℝ, ℂ)) (hf : f ∈ DeningerMeyerCap),
      shiftedSeminorm m (deningerPoissonSchwartz s f hf)
        ≤ C * (K.sup (schwartzSeminormFamily ℂ ℝ ℂ)) f := by
  obtain ⟨K₀, C₀, _, hb₀⟩ := shiftedSeminorm_le_schwartzSup m
  obtain ⟨K, C, hC, hb⟩ := exists_bound_schwartzSup_deningerPoissonSchwartz s K₀
  refine ⟨K, (C₀ : ℝ) * C, by positivity, fun f hf => ?_⟩
  have hstep : shiftedSeminorm m (deningerPoissonSchwartz s f hf)
      ≤ (C₀ : ℝ) * (K₀.sup (schwartzSeminormFamily ℂ ℝ ℂ)) (deningerPoissonSchwartz s f hf) := by
    have h := hb₀ (deningerPoissonSchwartz s f hf)
    rwa [_root_.smul_apply, NNReal.smul_def, smul_eq_mul] at h
  calc shiftedSeminorm m (deningerPoissonSchwartz s f hf)
      ≤ (C₀ : ℝ) * (K₀.sup (schwartzSeminormFamily ℂ ℝ ℂ)) (deningerPoissonSchwartz s f hf) :=
        hstep
    _ ≤ (C₀ : ℝ) * (C * (K.sup (schwartzSeminormFamily ℂ ℝ ℂ)) f) :=
        mul_le_mul_of_nonneg_left (hb f hf) (C₀ : ℝ≥0).coe_nonneg
    _ = (C₀ : ℝ) * C * (K.sup (schwartzSeminormFamily ℂ ℝ ℂ)) f := by ring

theorem exists_bound_sum_shiftedSeminorm_deningerPoisson (S : Finset ℤ) (k : ℤ → ℕ) :
    ∃ (K : Finset (ℕ × ℕ)) (C : ℝ), 0 ≤ C ∧ ∀ (f : 𝓢(ℝ, ℂ)) (hf : f ∈ DeningerMeyerCap),
      (∑ s ∈ S, shiftedSeminorm (k s) (deningerPoissonSchwartz s f hf))
        ≤ C * (K.sup (schwartzSeminormFamily ℂ ℝ ℂ)) f := by
  classical
  induction S using Finset.induction with
  | empty =>
    refine ⟨∅, 0, le_refl 0, fun f hf => ?_⟩
    simp
  | insert a S ha ih =>
    obtain ⟨K, C, hC, hb⟩ := ih
    obtain ⟨K', C', hC', hb'⟩ := exists_bound_shiftedSeminorm_deningerPoisson a (k a)
    refine ⟨K ∪ K', C + C', by positivity, fun f hf => ?_⟩
    have hsupnn : 0 ≤ ((K ∪ K').sup (schwartzSeminormFamily ℂ ℝ ℂ)) f := apply_nonneg _ _
    have hlemono : K.sup (schwartzSeminormFamily ℂ ℝ ℂ)
        ≤ (K ∪ K').sup (schwartzSeminormFamily ℂ ℝ ℂ) :=
      Finset.sup_mono Finset.subset_union_left
    have hlemono' : K'.sup (schwartzSeminormFamily ℂ ℝ ℂ)
        ≤ (K ∪ K').sup (schwartzSeminormFamily ℂ ℝ ℂ) :=
      Finset.sup_mono Finset.subset_union_right
    have hmono : (K.sup (schwartzSeminormFamily ℂ ℝ ℂ)) f
        ≤ ((K ∪ K').sup (schwartzSeminormFamily ℂ ℝ ℂ)) f := hlemono f
    have hmono' : (K'.sup (schwartzSeminormFamily ℂ ℝ ℂ)) f
        ≤ ((K ∪ K').sup (schwartzSeminormFamily ℂ ℝ ℂ)) f := hlemono' f
    rw [Finset.sum_insert ha]
    have h1 : shiftedSeminorm (k a) (deningerPoissonSchwartz a f hf)
        ≤ C' * ((K ∪ K').sup (schwartzSeminormFamily ℂ ℝ ℂ)) f :=
      (hb' f hf).trans (mul_le_mul_of_nonneg_left hmono' hC')
    have h2 : (∑ s ∈ S, shiftedSeminorm (k s) (deningerPoissonSchwartz s f hf))
        ≤ C * ((K ∪ K').sup (schwartzSeminormFamily ℂ ℝ ℂ)) f :=
      (hb f hf).trans (mul_le_mul_of_nonneg_left hmono hC)
    calc shiftedSeminorm (k a) (deningerPoissonSchwartz a f hf)
          + ∑ s ∈ S, shiftedSeminorm (k s) (deningerPoissonSchwartz s f hf)
        ≤ C' * ((K ∪ K').sup (schwartzSeminormFamily ℂ ℝ ℂ)) f
          + C * ((K ∪ K').sup (schwartzSeminormFamily ℂ ℝ ℂ)) f := add_le_add h1 h2
      _ = (C + C') * ((K ∪ K').sup (schwartzSeminormFamily ℂ ℝ ℂ)) f := by ring

/-- **The Poisson operator is continuous**: every seminorm of the radial presentation of the image
is bounded by finitely many Schwartz seminorms of the argument. -/
theorem deningerPoissonLM_bound (i : Finset ℤ × (ℤ → ℕ)) :
    ∃ (K : Finset (ℕ × ℕ)) (C : ℝ), 0 ≤ C ∧ ∀ f : DeningerMeyerCap,
      deningerRestrictSeminorm deningerRadialCompat
          (deningerPiFamily (fun _ : ℤ => (shiftedSeminorm : SeminormFamily ℂ 𝓢(ℝ, ℂ) ℕ)) i)
          (deningerPoissonLM f)
        ≤ C * deningerRestrictSeminorm DeningerMeyerCap
            (K.sup (schwartzSeminormFamily ℂ ℝ ℂ)) f := by
  obtain ⟨K, C, hC, hb⟩ := exists_bound_sum_shiftedSeminorm_deningerPoisson i.1 i.2
  refine ⟨K, C, hC, fun f => ?_⟩
  have hval : deningerRestrictSeminorm deningerRadialCompat
      (deningerPiFamily (fun _ : ℤ => (shiftedSeminorm : SeminormFamily ℂ 𝓢(ℝ, ℂ) ℕ)) i)
      (deningerPoissonLM f)
      = ∑ s ∈ i.1, shiftedSeminorm (i.2 s) (deningerPoissonSchwartz s (f : 𝓢(ℝ, ℂ)) f.2) := by
    rw [deningerRestrictSeminorm_apply, deningerPiFamily, deningerPiSeminorm_apply]
    rfl
  rw [hval]
  exact hb (f : 𝓢(ℝ, ℂ)) f.2

end RHTower

end
