import GaloisForLFunctions.RHTower.DeningerCapSupBound

/-!
# The weights of the Fourier transform

Under the Poisson operator the Fourier involution becomes multiplicative inversion, so in the
logarithmic coordinate it becomes reflection: the `s`-th weight of the Poisson sum of `𝓕f` is the
reflection of the `(1−s)`-th weight of the Poisson sum of `f`,

`e^{su}Z(𝓕f)(e^u) = e^{(1−s)(−u)}Zf(e^{−u})`.

Consequently the radial data of `𝓕f` is the radial data of `f` read backwards, and the polynomial
bounds for `𝓕f` are again bounds by finitely many Schwartz seminorms of weights of `Zf`.

* `deningerPoissonSchwartz_fourier` : **the weights of `Z𝓕f` are the reflected weights of `Zf`.**
* `exists_bound_seminorm_zero_fourier` : **`p_{m,0}(𝓕f)` is bounded by the radial data of `f`.**
-/

open scoped Real SchwartzMap FourierTransform ContDiff NNReal
open Complex MeasureTheory GaloisForLFunctions

noncomputable section

namespace RHTower

/-! ## Finite suprema for a continuous operator -/

/-- Every Schwartz seminorm of the image of a continuous operator is bounded by finitely many
Schwartz seminorms of the argument. -/
theorem exists_bound_seminorm_comp_pair (T : 𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ)) (p q : ℕ) :
    ∃ (K : Finset (ℕ × ℕ)) (C : ℝ), 0 ≤ C ∧ ∀ f : 𝓢(ℝ, ℂ),
      SchwartzMap.seminorm ℂ p q (T f) ≤ C * (K.sup (schwartzSeminormFamily ℂ ℝ ℂ)) f := by
  set r : Seminorm ℂ 𝓢(ℝ, ℂ) :=
    (SchwartzMap.seminorm ℂ p q).comp (T : 𝓢(ℝ, ℂ) →ₗ[ℂ] 𝓢(ℝ, ℂ)) with hr
  have hcont : Continuous r := by
    have hbase : Continuous (SchwartzMap.seminorm ℂ p q : 𝓢(ℝ, ℂ) → ℝ) :=
      (schwartz_withSeminorms ℂ ℝ ℂ).continuous_seminorm (p, q)
    exact hbase.comp T.continuous
  obtain ⟨K, C, _, hC⟩ :=
    Seminorm.bound_of_continuous (schwartz_withSeminorms ℂ ℝ ℂ) r hcont
  refine ⟨K, (C : ℝ), (C : ℝ≥0).coe_nonneg, fun f => ?_⟩
  have h := hC f
  rw [_root_.smul_apply, NNReal.smul_def, smul_eq_mul] at h
  exact h

/-- A finite supremum of Schwartz seminorms of the image of a continuous operator is bounded by
finitely many Schwartz seminorms of the argument. -/
theorem exists_bound_schwartzSup_comp (T : 𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ)) (K₀ : Finset (ℕ × ℕ)) :
    ∃ (K : Finset (ℕ × ℕ)) (C : ℝ), 0 ≤ C ∧ ∀ g : 𝓢(ℝ, ℂ),
      (K₀.sup (schwartzSeminormFamily ℂ ℝ ℂ)) (T g)
        ≤ C * (K.sup (schwartzSeminormFamily ℂ ℝ ℂ)) g := by
  classical
  induction K₀ using Finset.induction with
  | empty =>
    refine ⟨∅, 0, le_refl 0, fun g => ?_⟩
    simp
  | insert a K₀ ha ih =>
    obtain ⟨K, C, hC, hb⟩ := ih
    obtain ⟨K', C', hC', hb'⟩ := exists_bound_seminorm_comp_pair T a.1 a.2
    refine ⟨K ∪ K', C + C', by positivity, fun g => ?_⟩
    have hsupnn : 0 ≤ ((K ∪ K').sup (schwartzSeminormFamily ℂ ℝ ℂ)) g := apply_nonneg _ _
    have hlemono : K.sup (schwartzSeminormFamily ℂ ℝ ℂ)
        ≤ (K ∪ K').sup (schwartzSeminormFamily ℂ ℝ ℂ) :=
      Finset.sup_mono Finset.subset_union_left
    have hlemono' : K'.sup (schwartzSeminormFamily ℂ ℝ ℂ)
        ≤ (K ∪ K').sup (schwartzSeminormFamily ℂ ℝ ℂ) :=
      Finset.sup_mono Finset.subset_union_right
    have hmono : (K.sup (schwartzSeminormFamily ℂ ℝ ℂ)) g
        ≤ ((K ∪ K').sup (schwartzSeminormFamily ℂ ℝ ℂ)) g := hlemono g
    have hmono' : (K'.sup (schwartzSeminormFamily ℂ ℝ ℂ)) g
        ≤ ((K ∪ K').sup (schwartzSeminormFamily ℂ ℝ ℂ)) g := hlemono' g
    rw [Finset.sup_insert, Seminorm.sup_apply]
    refine max_le ?_ ?_
    · have hstep : (schwartzSeminormFamily ℂ ℝ ℂ a) (T g)
          ≤ C' * (K'.sup (schwartzSeminormFamily ℂ ℝ ℂ)) g := by
        have hb'' := hb' g
        have hfam : (schwartzSeminormFamily ℂ ℝ ℂ a) (T g)
            = SchwartzMap.seminorm ℂ a.1 a.2 (T g) := rfl
        rw [hfam]
        exact hb''
      calc (schwartzSeminormFamily ℂ ℝ ℂ a) (T g)
          ≤ C' * (K'.sup (schwartzSeminormFamily ℂ ℝ ℂ)) g := hstep
        _ ≤ C' * ((K ∪ K').sup (schwartzSeminormFamily ℂ ℝ ℂ)) g :=
            mul_le_mul_of_nonneg_left hmono' hC'
        _ ≤ (C + C') * ((K ∪ K').sup (schwartzSeminormFamily ℂ ℝ ℂ)) g := by
            refine mul_le_mul_of_nonneg_right ?_ hsupnn
            linarith
    · calc (K₀.sup (schwartzSeminormFamily ℂ ℝ ℂ)) (T g)
          ≤ C * (K.sup (schwartzSeminormFamily ℂ ℝ ℂ)) g := hb g
        _ ≤ C * ((K ∪ K').sup (schwartzSeminormFamily ℂ ℝ ℂ)) g :=
            mul_le_mul_of_nonneg_left hmono hC
        _ ≤ (C + C') * ((K ∪ K').sup (schwartzSeminormFamily ℂ ℝ ℂ)) g := by
            refine mul_le_mul_of_nonneg_right ?_ hsupnn
            linarith

/-! ## The reflected weights -/

/-- **The weights of the Poisson sum of a Fourier transform are the reflected weights of the
Poisson sum**, with the index reflected in `1/2`. -/
theorem deningerPoissonSchwartz_fourier (s : ℤ) (f : 𝓢(ℝ, ℂ)) (hf : f ∈ DeningerMeyerCap) :
    deningerPoissonSchwartz s (fourierSCLM f) (deningerMeyerCap_fourierSCLM hf)
      = deningerReflect (deningerPoissonSchwartz (1 - s) f hf) := by
  refine SchwartzMap.ext fun u => ?_
  have hpos : (0 : ℝ) < Real.exp (-u) := Real.exp_pos _
  have hrefl := deningerPoissonValue_fourier_reflection hf hpos
  have hinv : (Real.exp (-u))⁻¹ = Real.exp u := by
    rw [Real.exp_neg, inv_inv]
  rw [hinv] at hrefl
  have hlhs : deningerPoissonSchwartz s (fourierSCLM f) (deningerMeyerCap_fourierSCLM hf) u
      = ((Real.exp ((s : ℝ) * u) : ℝ) : ℂ) * deningerPoissonValue (fourierSCLM f)
        (Real.exp u) := by
    rw [deningerPoissonSchwartz_apply, deningerPoissonWeight, deningerExpWeight,
      deningerPoissonLog_eq]
  have hrhs : deningerReflect (deningerPoissonSchwartz (1 - s) f hf) u
      = ((Real.exp (((1 - s : ℤ) : ℝ) * (-u)) : ℝ) : ℂ) * deningerPoissonValue f
        (Real.exp (-u)) := by
    rw [deningerReflect_apply, deningerPoissonSchwartz_apply, deningerPoissonWeight,
      deningerExpWeight, deningerPoissonLog_eq]
  rw [hlhs, hrhs, hrefl]
  have hexp : ((Real.exp (((1 - s : ℤ) : ℝ) * (-u)) : ℝ) : ℂ)
      * (((Real.exp u : ℝ) : ℂ) * deningerPoissonValue (fourierSCLM f) (Real.exp u))
      = (((Real.exp (((1 - s : ℤ) : ℝ) * (-u)) * Real.exp u : ℝ)) : ℂ)
        * deningerPoissonValue (fourierSCLM f) (Real.exp u) := by
    push_cast
    ring
  have hexpval : Real.exp (((1 - s : ℤ) : ℝ) * (-u)) * Real.exp u = Real.exp ((s : ℝ) * u) := by
    rw [← Real.exp_add]
    congr 1
    push_cast
    ring
  rw [hexp, hexpval]

/-! ## The polynomial bounds for the Fourier transform -/

/-- **The supremum seminorms of the Fourier transform of a member of Meyer's space are bounded by
finitely many Schwartz seminorms of two weights of its own Poisson sum.** -/
theorem exists_bound_seminorm_zero_fourier (m : ℕ) :
    ∃ (K : Finset (ℕ × ℕ)) (C : ℝ), 0 ≤ C ∧ ∀ (f : 𝓢(ℝ, ℂ)) (hf : f ∈ DeningerMeyerCap),
      SchwartzMap.seminorm ℂ m 0 (fourierSCLM f)
        ≤ C * ((K.sup (schwartzSeminormFamily ℂ ℝ ℂ))
              (deningerPoissonSchwartz (1 - ((m : ℤ) + 2)) f hf)
            + (K.sup (schwartzSeminormFamily ℂ ℝ ℂ)) (deningerPoissonSchwartz 2 f hf)) := by
  classical
  obtain ⟨K₀, C₀, hC₀, hb₀⟩ := exists_bound_seminorm_zero m
  obtain ⟨K₁, C₁, hC₁, hb₁⟩ := exists_bound_schwartzSup_comp deningerReflectCLM K₀
  refine ⟨K₁, C₀ * C₁, by positivity, fun f hf => ?_⟩
  have hFmem : fourierSCLM f ∈ DeningerMeyerCap := deningerMeyerCap_fourierSCLM hf
  have hone : (1 : ℤ) - (-1) = 2 := by norm_num
  have hw₁ : deningerPoissonSchwartz ((m : ℤ) + 2) (fourierSCLM f) hFmem
      = deningerReflectCLM (deningerPoissonSchwartz (1 - ((m : ℤ) + 2)) f hf) :=
    deningerPoissonSchwartz_fourier ((m : ℤ) + 2) f hf
  have hw₂ : deningerPoissonSchwartz (-1) (fourierSCLM f) hFmem
      = deningerReflectCLM (deningerPoissonSchwartz 2 f hf) := by
    have h := deningerPoissonSchwartz_fourier (-1) f hf
    rw [hone] at h
    exact h
  have hstep := hb₀ (fourierSCLM f) hFmem
  rw [hw₁, hw₂] at hstep
  have hb₁' := hb₁ (deningerPoissonSchwartz (1 - ((m : ℤ) + 2)) f hf)
  have hb₂' := hb₁ (deningerPoissonSchwartz 2 f hf)
  set S₁ : ℝ := (K₁.sup (schwartzSeminormFamily ℂ ℝ ℂ))
    (deningerPoissonSchwartz (1 - ((m : ℤ) + 2)) f hf) with hS₁
  set S₂ : ℝ := (K₁.sup (schwartzSeminormFamily ℂ ℝ ℂ)) (deningerPoissonSchwartz 2 f hf) with hS₂
  calc SchwartzMap.seminorm ℂ m 0 (fourierSCLM f)
      ≤ C₀ * ((K₀.sup (schwartzSeminormFamily ℂ ℝ ℂ))
            (deningerReflectCLM (deningerPoissonSchwartz (1 - ((m : ℤ) + 2)) f hf))
          + (K₀.sup (schwartzSeminormFamily ℂ ℝ ℂ))
            (deningerReflectCLM (deningerPoissonSchwartz 2 f hf))) := hstep
    _ ≤ C₀ * (C₁ * S₁ + C₁ * S₂) :=
        mul_le_mul_of_nonneg_left (add_le_add hb₁' hb₂') hC₀
    _ = C₀ * C₁ * (S₁ + S₂) := by ring

end RHTower

end
