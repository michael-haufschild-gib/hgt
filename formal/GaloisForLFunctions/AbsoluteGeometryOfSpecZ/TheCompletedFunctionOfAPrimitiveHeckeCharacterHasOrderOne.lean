import GaloisForLFunctions.HeckeLFunctions.PrimitiveHeckeLFunctionsHaveCompletedFunctionalEquation
import GaloisForLFunctions.HeckeLFunctions.HeckeConductorsAndParitiesAreInvariantUnderInversion
import GaloisForLFunctions.HTGeometry.MellinMajorant
import GaloisForLFunctions.RHTower.CompletionOrderOneEnvelope

/-!
# The completed function of a primitive Hecke character has order one

For a primitive ray class character `ψ` of a number field, the pole-cleared completion
`Ξ_ψ(s) = s(s − 1) N^{s/2} Π_v Γ_ℝ(s + κ_v) Γ_ℂ(s)^{r₂} L(s, ψ)` satisfies

`‖Ξ_ψ(s)‖ ≤ exp(C (1 + ‖s‖) log(2 + ‖s‖))`   (`exists_orderOne_heckePoleClearedCompletion`),

and so does the completed function itself when `ψ ≠ 1`
(`exists_orderOne_heckeCompletedLFunction`).

* **Strip.** The completion is a finite sum of class weights `N𝔟^s` times continued Mellin
  transforms of theta functions, whose regular parts are bounded on vertical strips (the Mellin
  integral of the norm at the two edges). The divided differences that fill the values at `0` and
  `1` stay bounded. Hence `Ξ_ψ = O(|s|²)` on `−1 ≤ Re s ≤ 2`.
* **Right.** On `Re s ≥ 2` the Dirichlet series is bounded and every Gamma factor is at most
  `exp(2(1 + ‖s‖) log(2 + ‖s‖))`.
* **Left.** The functional equation `Ξ_ψ(1 − s) = W Ξ_{ψ⁻¹}(s)`, `|W| = 1`.
-/

noncomputable section

open Complex Filter Topology Set NumberField
open scoped Classical nonZeroDivisors

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

open HeckeLFunctions HTGeometry HTGeometry.IntegerLatticePoisson
open RHTower.CompletionGrowth

/-! ### Functions bounded on a vertical strip -/

/-- Bounded on the closed vertical strip `σ₀ ≤ Re s ≤ σ₁`. -/
def StripBounded (f : ℂ → ℂ) (σ₀ σ₁ : ℝ) : Prop :=
  ∃ C : ℝ, ∀ s : ℂ, σ₀ ≤ s.re → s.re ≤ σ₁ → ‖f s‖ ≤ C

namespace StripBounded

variable {f g : ℂ → ℂ} {σ₀ σ₁ : ℝ}

theorem const (c : ℂ) (σ₀ σ₁ : ℝ) : StripBounded (fun _ => c) σ₀ σ₁ :=
  ⟨‖c‖, fun _ _ _ => le_rfl⟩

theorem add (hf : StripBounded f σ₀ σ₁) (hg : StripBounded g σ₀ σ₁) :
    StripBounded (fun s => f s + g s) σ₀ σ₁ := by
  obtain ⟨A, hA⟩ := hf
  obtain ⟨B, hB⟩ := hg
  exact ⟨A + B, fun s h0 h1 => (norm_add_le _ _).trans (add_le_add (hA s h0 h1) (hB s h0 h1))⟩

theorem sub (hf : StripBounded f σ₀ σ₁) (hg : StripBounded g σ₀ σ₁) :
    StripBounded (fun s => f s - g s) σ₀ σ₁ := by
  obtain ⟨A, hA⟩ := hf
  obtain ⟨B, hB⟩ := hg
  exact ⟨A + B, fun s h0 h1 => (norm_sub_le _ _).trans (add_le_add (hA s h0 h1) (hB s h0 h1))⟩

theorem mul (hf : StripBounded f σ₀ σ₁) (hg : StripBounded g σ₀ σ₁) :
    StripBounded (fun s => f s * g s) σ₀ σ₁ := by
  obtain ⟨A, hA⟩ := hf
  obtain ⟨B, hB⟩ := hg
  refine ⟨max A 0 * max B 0, fun s h0 h1 => ?_⟩
  rw [norm_mul]
  exact mul_le_mul ((hA s h0 h1).trans (le_max_left _ _)) ((hB s h0 h1).trans (le_max_left _ _))
    (norm_nonneg _) (le_max_right _ _)

theorem sum {ι : Type*} (t : Finset ι) {F : ι → ℂ → ℂ}
    (hF : ∀ i ∈ t, StripBounded (F i) σ₀ σ₁) :
    StripBounded (fun s => ∑ i ∈ t, F i s) σ₀ σ₁ := by
  induction t using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using const 0 σ₀ σ₁
  | insert a t ha ih =>
    simp only [Finset.sum_insert ha]
    exact (hF a (Finset.mem_insert_self a t)).add
      (ih fun i hi => hF i (Finset.mem_insert_of_mem hi))

/-- The divided difference of an entire function bounded on a strip is bounded on the strip:
continuity near the base point, the two values away from it. -/
theorem dslope (hf : Differentiable ℂ f) (hb : StripBounded f σ₀ σ₁) (a : ℂ) :
    StripBounded (_root_.dslope f a) σ₀ σ₁ := by
  obtain ⟨A, hA⟩ := hb
  have hcont : Continuous (_root_.dslope f a) := by
    rw [continuous_iff_continuousAt]
    intro b
    rcases eq_or_ne b a with rfl | hba
    · exact continuousAt_dslope_same.mpr (hf b)
    · exact (continuousAt_dslope_of_ne hba).mpr hf.continuous.continuousAt
  obtain ⟨B, hB⟩ := (isCompact_closedBall a 1).exists_bound_of_continuousOn hcont.continuousOn
  refine ⟨max B (A + ‖f a‖), fun s h0 h1 => ?_⟩
  rcases le_or_gt (dist s a) 1 with hs | hs
  · exact (hB s (Metric.mem_closedBall.mpr hs)).trans (le_max_left _ _)
  · have hsa : s ≠ a := by
      rintro rfl
      rw [dist_self] at hs
      linarith
    have hd : 1 < ‖s - a‖ := by rwa [← dist_eq_norm]
    have hA0 : 0 ≤ A + ‖f a‖ :=
      add_nonneg ((norm_nonneg _).trans (hA s h0 h1)) (norm_nonneg _)
    refine le_trans ?_ (le_max_right _ _)
    rw [dslope_of_ne _ hsa, slope_def_field, norm_div, div_le_iff₀ (by linarith)]
    calc ‖f s - f a‖ ≤ ‖f s‖ + ‖f a‖ := norm_sub_le _ _
      _ ≤ A + ‖f a‖ := by linarith [hA s h0 h1]
      _ ≤ (A + ‖f a‖) * ‖s - a‖ := le_mul_of_one_le_right hA0 hd.le

end StripBounded

/-! ### The theta representation on a strip -/

variable {K : Type*} [Field K] [NumberField K] (𝔪 : Modulus K)

local instance : Fintype (ClassGroup (𝓞 K)) := Fintype.ofFinite _

theorem stripBounded_heckeClassWeight (ψ : HeckeCharacter 𝔪) (c : ClassGroup (𝓞 K))
    (σ₀ σ₁ : ℝ) : StripBounded (heckeClassWeight 𝔪 ψ c) σ₀ σ₁ := by
  have hn : 0 < Ideal.absNorm (heckeClassBaseIdeal 𝔪 c : Ideal (𝓞 K)) :=
    Nat.pos_of_ne_zero (Ideal.absNorm_ne_zero_of_nonZeroDivisors _)
  refine ⟨‖(heckeValue 𝔪 ψ (heckeClassBaseIdeal 𝔪 c : Ideal (𝓞 K)))⁻¹‖ *
    (Ideal.absNorm (heckeClassBaseIdeal 𝔪 c : Ideal (𝓞 K)) : ℝ) ^ σ₁, fun s _ h1 => ?_⟩
  rw [heckeClassWeight, norm_mul, Complex.norm_natCast_cpow_of_pos hn]
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le (Nat.one_le_cast.mpr hn) h1) (norm_nonneg _)

theorem re_heckeThetaMellinArgument (ψ : HeckeCharacter 𝔪) (s : ℂ) :
    (heckeThetaMellinArgument 𝔪 ψ s).re =
      ((Module.finrank ℚ K : ℝ) * s.re + parityDegree (heckeCoordinateParity 𝔪 ψ)) / 2 := by
  simp [heckeThetaMellinArgument]

/-- The regular part of the continued Mellin transform of a class theta function, in the Hecke
variable, is bounded on vertical strips. -/
theorem stripBounded_heckeUnitThetaMellinRegularPart {b : Ideal (𝓞 K)} (hb : b ⊔ 𝔪.fin = ⊤)
    (hb0 : b ≠ ⊥) (ψ : HeckeCharacter 𝔪) (σ₀ σ₁ : ℝ) :
    StripBounded (fun s => heckeUnitThetaMellinRegularPart 𝔪 hb hb0 ψ
      (heckeThetaMellinArgument 𝔪 ψ s)) σ₀ σ₁ := by
  have hn : (0 : ℝ) ≤ Module.finrank ℚ K := Nat.cast_nonneg _
  obtain ⟨C, -, hC⟩ := exists_bound_norm_WeakFEPair_Λ₀ (heckeUnitThetaMellinPair 𝔪 hb hb0 ψ)
    (((Module.finrank ℚ K : ℝ) * σ₀ + parityDegree (heckeCoordinateParity 𝔪 ψ)) / 2)
    (((Module.finrank ℚ K : ℝ) * σ₁ + parityDegree (heckeCoordinateParity 𝔪 ψ)) / 2)
  refine ⟨C, fun s h0 h1 => hC _ ?_ ?_⟩
  · rw [re_heckeThetaMellinArgument]
    have := mul_le_mul_of_nonneg_left h0 hn
    linarith
  · rw [re_heckeThetaMellinArgument]
    have := mul_le_mul_of_nonneg_left h1 hn
    linarith

theorem stripBounded_heckeCompletedThetaRegularPart (ψ : HeckeCharacter 𝔪) (σ₀ σ₁ : ℝ) :
    StripBounded (heckeCompletedThetaRegularPart 𝔪 ψ) σ₀ σ₁ := by
  have h : StripBounded (fun s : ℂ => heckeMellinNormalization (K := K) *
      ∑ c : ClassGroup (𝓞 K), heckeClassWeight 𝔪 ψ c s *
        heckeUnitThetaMellinRegularPart 𝔪 (heckeClassBaseIdeal_coprime 𝔪 c)
          (nonZeroDivisors.coe_ne_zero _) ψ (heckeThetaMellinArgument 𝔪 ψ s)) σ₀ σ₁ :=
    (StripBounded.const _ σ₀ σ₁).mul (StripBounded.sum _ fun c _ =>
      (stripBounded_heckeClassWeight 𝔪 ψ c σ₀ σ₁).mul
        (stripBounded_heckeUnitThetaMellinRegularPart 𝔪 _ _ ψ σ₀ σ₁))
  exact h

theorem stripBounded_heckeCompletedPhysicalNumerator (ψ : HeckeCharacter 𝔪) (σ₀ σ₁ : ℝ) :
    StripBounded (heckeCompletedPhysicalNumerator 𝔪 ψ) σ₀ σ₁ := by
  have h : StripBounded (fun s : ℂ => heckeMellinNormalization (K := K) *
      ∑ c : ClassGroup (𝓞 K), heckeClassWeight 𝔪 ψ c s *
        ((Units.regulator K : ℂ) * heckeThetaConstant 𝔪 ψ)) σ₀ σ₁ :=
    (StripBounded.const _ σ₀ σ₁).mul (StripBounded.sum _ fun c _ =>
      (stripBounded_heckeClassWeight 𝔪 ψ c σ₀ σ₁).mul (StripBounded.const _ σ₀ σ₁))
  exact h

theorem stripBounded_heckeCompletedDualNumerator (ψ : HeckeCharacter 𝔪) (σ₀ σ₁ : ℝ) :
    StripBounded (heckeCompletedDualNumerator 𝔪 ψ) σ₀ σ₁ := by
  have h : StripBounded (fun s : ℂ => heckeMellinNormalization (K := K) *
      ∑ c : ClassGroup (𝓞 K), heckeClassWeight 𝔪 ψ c s *
        (heckeThetaMellinScalar 𝔪 ψ
          ((𝔪.fin * (heckeClassBaseIdeal 𝔪 c : Ideal (𝓞 K)) : Ideal (𝓞 K)) :
            FractionalIdeal (nonZeroDivisors (𝓞 K)) K) 0 *
          ((Units.regulator K : ℂ) * heckeDualThetaConstant 𝔪 ψ))) σ₀ σ₁ :=
    (StripBounded.const _ σ₀ σ₁).mul (StripBounded.sum _ fun c _ =>
      (stripBounded_heckeClassWeight 𝔪 ψ c σ₀ σ₁).mul (StripBounded.const _ σ₀ σ₁))
  exact h

/-- **The entire regular part of the Gamma-completed function is bounded on vertical strips.** -/
theorem stripBounded_heckeGammaCompletedRegularPart (ψ : HeckeCharacter 𝔪) (σ₀ σ₁ : ℝ) :
    StripBounded (heckeGammaCompletedRegularPart 𝔪 ψ) σ₀ σ₁ := by
  by_cases hp : parityDegree (heckeCoordinateParity 𝔪 ψ) = 0
  · have h : StripBounded (fun s : ℂ => heckeCompletedThetaRegularPart 𝔪 ψ s -
        (2 / (Module.finrank ℚ K : ℂ)) * dslope (heckeCompletedPhysicalNumerator 𝔪 ψ) 0 s +
        (2 / (Module.finrank ℚ K : ℂ)) * dslope (heckeCompletedDualNumerator 𝔪 ψ) 1 s) σ₀ σ₁ :=
      ((stripBounded_heckeCompletedThetaRegularPart 𝔪 ψ σ₀ σ₁).sub
        ((StripBounded.const _ σ₀ σ₁).mul
          ((stripBounded_heckeCompletedPhysicalNumerator 𝔪 ψ σ₀ σ₁).dslope
            (differentiable_heckeCompletedPhysicalNumerator 𝔪 ψ) 0))).add
        ((StripBounded.const _ σ₀ σ₁).mul
          ((stripBounded_heckeCompletedDualNumerator 𝔪 ψ σ₀ σ₁).dslope
            (differentiable_heckeCompletedDualNumerator 𝔪 ψ) 1))
    obtain ⟨C, hC⟩ := h
    exact ⟨C, fun s h0 h1 => by
      rw [heckeGammaCompletedRegularPart, if_pos hp]
      exact hC s h0 h1⟩
  · obtain ⟨C, hC⟩ := stripBounded_heckeCompletedThetaRegularPart 𝔪 ψ σ₀ σ₁
    exact ⟨C, fun s h0 h1 => by
      rw [heckeGammaCompletedRegularPart, if_neg hp]
      exact hC s h0 h1⟩

/-! ### The conductor factor -/

theorem norm_heckeCompletionFactor (s : ℂ) :
    ‖heckeCompletionFactor 𝔪 s‖ = (heckeCompletionNorm 𝔪 : ℝ) ^ (s.re / 2) := by
  rw [heckeCompletionFactor, Complex.norm_natCast_cpow_of_pos (heckeCompletionNorm_pos 𝔪)]
  simp

theorem one_le_heckeCompletionNorm : (1 : ℝ) ≤ heckeCompletionNorm 𝔪 :=
  Nat.one_le_cast.mpr (heckeCompletionNorm_pos 𝔪)

/-- `s(s − 1)·(completion)` is `O(|s|²)` on `−1 ≤ Re s ≤ 2`. -/
theorem exists_strip_bound_heckePoleClearedCompletion (ψ : HeckeCharacter 𝔪) :
    ∃ B : ℝ, ∀ s : ℂ, -1 ≤ s.re → s.re ≤ 2 →
      ‖heckePoleClearedCompletion 𝔪 ψ s‖ ≤ B * (1 + ‖s‖) ^ 2 := by
  obtain ⟨C, hC⟩ := stripBounded_heckeGammaCompletedRegularPart 𝔪 ψ (-1) 2
  have hN1 := one_le_heckeCompletionNorm 𝔪
  refine ⟨(heckeCompletionNorm 𝔪 : ℝ) * (max C 0 + ‖heckeGammaCompletedZeroCoefficient 𝔪 ψ‖ +
    ‖heckeGammaCompletedOneCoefficient 𝔪 ψ‖), fun s h0 h1 => ?_⟩
  have hr := norm_nonneg s
  have hs1 : ‖s - 1‖ ≤ 1 + ‖s‖ := by
    calc ‖s - 1‖ ≤ ‖s‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 1 + ‖s‖ := by rw [norm_one, add_comm]
  have hfac : ‖heckeCompletionFactor 𝔪 s‖ ≤ heckeCompletionNorm 𝔪 := by
    rw [norm_heckeCompletionFactor]
    calc (heckeCompletionNorm 𝔪 : ℝ) ^ (s.re / 2) ≤ (heckeCompletionNorm 𝔪 : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
      _ = heckeCompletionNorm 𝔪 := Real.rpow_one _
  have hReg := (hC s h0 h1).trans (le_max_left C 0)
  have hprod : ‖s‖ * ‖s - 1‖ ≤ (1 + ‖s‖) ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hs1 hr]
  have t1 : ‖s * (s - 1) * heckeGammaCompletedRegularPart 𝔪 ψ s‖ ≤ (1 + ‖s‖) ^ 2 * max C 0 := by
    rw [norm_mul, norm_mul]
    exact mul_le_mul hprod hReg (norm_nonneg _) (by positivity)
  have t2 : ‖(s - 1) * heckeGammaCompletedZeroCoefficient 𝔪 ψ‖ ≤
      (1 + ‖s‖) ^ 2 * ‖heckeGammaCompletedZeroCoefficient 𝔪 ψ‖ := by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (by nlinarith) (norm_nonneg _)
  have t3 : ‖s * heckeGammaCompletedOneCoefficient 𝔪 ψ‖ ≤
      (1 + ‖s‖) ^ 2 * ‖heckeGammaCompletedOneCoefficient 𝔪 ψ‖ := by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (by nlinarith) (norm_nonneg _)
  rw [heckePoleClearedCompletion, norm_mul]
  calc ‖heckeCompletionFactor 𝔪 s‖ *
        ‖s * (s - 1) * heckeGammaCompletedRegularPart 𝔪 ψ s +
          (s - 1) * heckeGammaCompletedZeroCoefficient 𝔪 ψ +
          s * heckeGammaCompletedOneCoefficient 𝔪 ψ‖
      ≤ (heckeCompletionNorm 𝔪 : ℝ) * ((1 + ‖s‖) ^ 2 * max C 0 +
          (1 + ‖s‖) ^ 2 * ‖heckeGammaCompletedZeroCoefficient 𝔪 ψ‖ +
          (1 + ‖s‖) ^ 2 * ‖heckeGammaCompletedOneCoefficient 𝔪 ψ‖) :=
        mul_le_mul hfac ((norm_add₃_le).trans (add_le_add (add_le_add t1 t2) t3))
          (norm_nonneg _) (by positivity)
    _ = _ := by ring

/-! ### The right half-plane -/

/-- A real Gamma factor shifted by a point of the unit disc in the right half-plane. -/
theorem norm_Gammaℝ_add_le {s w : ℂ} (hs : 2 ≤ s.re) (hw0 : 0 ≤ w.re) (hw : ‖w‖ ≤ 1) :
    ‖Complex.Gammaℝ (s + w)‖ ≤ Real.exp (2 * (1 + ‖s‖) * Real.log (2 + ‖s‖)) := by
  have hr := norm_nonneg s
  have h := norm_Gammaℝ_le (s := s + w) (by rw [Complex.add_re]; linarith)
  refine h.trans (Real.exp_le_exp.mpr ?_)
  have hn : ‖s + w‖ ≤ 1 + ‖s‖ := (norm_add_le _ _).trans (by linarith)
  have hl0 : 0 ≤ Real.log (2 + ‖s + w‖) := Real.log_nonneg (by linarith [norm_nonneg (s + w)])
  have hl : Real.log (2 + ‖s + w‖) ≤ 2 * Real.log (2 + ‖s‖) := by
    rw [← Real.log_rpow (by positivity)]
    refine Real.log_le_log (by positivity) ?_
    norm_num
    nlinarith
  calc ‖s + w‖ * Real.log (2 + ‖s + w‖) ≤ (1 + ‖s‖) * (2 * Real.log (2 + ‖s‖)) :=
        mul_le_mul hn hl hl0 (by positivity)
    _ = 2 * (1 + ‖s‖) * Real.log (2 + ‖s‖) := by ring

/-- The Gamma product of a Hecke character on `Re s ≥ 2`. -/
theorem norm_heckeGammaFactor_le (ψ : HeckeCharacter 𝔪) {s : ℂ} (hs : 2 ≤ s.re) :
    ‖heckeGammaFactor 𝔪 ψ s‖ ≤
      Real.exp (2 * (1 + ‖s‖) * Real.log (2 + ‖s‖)) ^
        (Fintype.card {v : InfinitePlace K // v.IsReal} + 2 * InfinitePlace.nrComplexPlaces K) := by
  set G : ℝ := Real.exp (2 * (1 + ‖s‖) * Real.log (2 + ‖s‖)) with hG
  have hG0 : 0 ≤ G := (Real.exp_pos _).le
  have hreal : ∀ v : {v : InfinitePlace K // v.IsReal},
      ‖Complex.Gammaℝ (s + (heckeCoordinateParity 𝔪 ψ (Sum.inl v)).toNat)‖ ≤ G := fun v => by
    refine norm_Gammaℝ_add_le hs (by simp) ?_
    rw [Complex.norm_natCast]
    exact_mod_cast Bool.toNat_le _
  have hcomplex : ‖Complex.Gammaℂ s‖ ≤ G ^ 2 := by
    rw [← Complex.Gammaℝ_mul_Gammaℝ_add_one, norm_mul, sq]
    have h0 := norm_Gammaℝ_add_le (w := 0) hs (by simp) (by simp)
    rw [add_zero] at h0
    exact mul_le_mul h0 (norm_Gammaℝ_add_le hs (by simp) (by simp)) (norm_nonneg _) hG0
  rw [heckeGammaFactor, norm_mul, norm_prod, norm_pow, pow_add, pow_mul]
  refine mul_le_mul ?_ (pow_le_pow_left₀ (norm_nonneg _) hcomplex _)
    (pow_nonneg (norm_nonneg _) _) (pow_nonneg hG0 _)
  calc ∏ v : {v : InfinitePlace K // v.IsReal},
        ‖Complex.Gammaℝ (s + (heckeCoordinateParity 𝔪 ψ (Sum.inl v)).toNat)‖
      ≤ ∏ _v : {v : InfinitePlace K // v.IsReal}, G :=
        Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun v _ => hreal v
    _ = G ^ Fintype.card {v : InfinitePlace K // v.IsReal} := by
        rw [Finset.prod_const, Finset.card_univ]

/-- Constants and powers of `1 + r` are absorbed by the order-one envelope. -/
theorem exists_envelope_absorb (A : ℝ) (N : ℕ) {M : ℝ} (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 0 ≤ r →
      A * (1 + r) ^ N * Real.exp (M * (1 + r) * Real.log (2 + r)) ≤
        Real.exp (C * (1 + r) * Real.log (2 + r)) := by
  obtain ⟨C₀, hC₀, h⟩ := le_exp_envelope (A := A) (M := 0) le_rfl N
  refine ⟨C₀ + M, add_nonneg hC₀ hM, fun r hr => ?_⟩
  have h0 := h r hr
  simp only [zero_mul, Real.exp_zero, mul_one] at h0
  calc A * (1 + r) ^ N * Real.exp (M * (1 + r) * Real.log (2 + r))
      ≤ Real.exp (C₀ * (1 + r) * Real.log (2 + r)) *
          Real.exp (M * (1 + r) * Real.log (2 + r)) :=
        mul_le_mul_of_nonneg_right h0 (Real.exp_pos _).le
    _ = Real.exp ((C₀ + M) * (1 + r) * Real.log (2 + r)) := by
        rw [← Real.exp_add]
        ring_nf

/-- **The completed Hecke function on `Re s ≥ 2`**: at most
`S exp(M (1 + ‖s‖) log(2 + ‖s‖))`, with `S` the Dirichlet series of the norms at `2`. -/
theorem exists_halfPlane_bound_heckeCompletedLFunction (ψ : HeckeCharacter 𝔪) :
    ∃ S M : ℝ, 0 ≤ S ∧ 0 ≤ M ∧ ∀ s : ℂ, 2 ≤ s.re →
      ‖heckeCompletedLFunction 𝔪 ψ s‖ ≤
        S * Real.exp (M * (1 + ‖s‖) * Real.log (2 + ‖s‖)) := by
  have hg : LSeriesSummable (heckeCoeff 𝔪 ψ) 2 :=
    lSeriesSummable_heckeCoeff 𝔪 ψ (by norm_num)
  have hN1 := one_le_heckeCompletionNorm 𝔪
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hlN : 0 ≤ Real.log (heckeCompletionNorm 𝔪) := Real.log_nonneg hN1
  set d : ℕ := Fintype.card {v : InfinitePlace K // v.IsReal} +
    2 * InfinitePlace.nrComplexPlaces K with hd
  set M₀ : ℝ := Real.log (heckeCompletionNorm 𝔪) / Real.log 2 with hM₀
  have hM₀0 : 0 ≤ M₀ := div_nonneg hlN hl2.le
  refine ⟨∑' n, ‖LSeries.term (heckeCoeff 𝔪 ψ) 2 n‖, M₀ + 2 * d,
    tsum_nonneg fun n => norm_nonneg _, by positivity, fun s hs => ?_⟩
  have hr := norm_nonneg s
  have hL : Real.log 2 ≤ Real.log (2 + ‖s‖) := Real.log_le_log two_pos (by linarith)
  have hL0 : 0 ≤ Real.log (2 + ‖s‖) := hl2.le.trans hL
  -- the conductor factor
  have hfac : ‖heckeCompletionFactor 𝔪 s‖ ≤ Real.exp (M₀ * (1 + ‖s‖) * Real.log (2 + ‖s‖)) := by
    rw [norm_heckeCompletionFactor,
      Real.rpow_def_of_pos (by linarith : (0 : ℝ) < heckeCompletionNorm 𝔪), Real.exp_le_exp]
    have h1 : s.re / 2 ≤ 1 + ‖s‖ := by linarith [Complex.re_le_norm s]
    have h2 : Real.log (heckeCompletionNorm 𝔪) = M₀ * Real.log 2 := by
      rw [hM₀]
      field_simp
    calc Real.log (heckeCompletionNorm 𝔪) * (s.re / 2)
        ≤ Real.log (heckeCompletionNorm 𝔪) * (1 + ‖s‖) := mul_le_mul_of_nonneg_left h1 hlN
      _ = M₀ * (1 + ‖s‖) * Real.log 2 := by rw [h2]; ring
      _ ≤ M₀ * (1 + ‖s‖) * Real.log (2 + ‖s‖) :=
          mul_le_mul_of_nonneg_left hL (by positivity)
  -- the Gamma product
  have hgam : ‖heckeGammaFactor 𝔪 ψ s‖ ≤
      Real.exp ((2 * d : ℝ) * (1 + ‖s‖) * Real.log (2 + ‖s‖)) := by
    refine (norm_heckeGammaFactor_le 𝔪 ψ hs).trans (le_of_eq ?_)
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hser : ‖heckeL 𝔪 ψ s‖ ≤ ∑' n, ‖LSeries.term (heckeCoeff 𝔪 ψ) 2 n‖ :=
    norm_LSeries_le_of_two_le hg hs
  rw [heckeCompletedLFunction_eq 𝔪 ψ (by linarith : 1 < s.re), norm_mul, norm_mul]
  calc ‖heckeCompletionFactor 𝔪 s‖ * ‖heckeGammaFactor 𝔪 ψ s‖ * ‖heckeL 𝔪 ψ s‖
      ≤ Real.exp (M₀ * (1 + ‖s‖) * Real.log (2 + ‖s‖)) *
          Real.exp ((2 * d : ℝ) * (1 + ‖s‖) * Real.log (2 + ‖s‖)) *
          ∑' n, ‖LSeries.term (heckeCoeff 𝔪 ψ) 2 n‖ :=
        mul_le_mul (mul_le_mul hfac hgam (norm_nonneg _) (Real.exp_pos _).le) hser
          (norm_nonneg _) (by positivity)
    _ = (∑' n, ‖LSeries.term (heckeCoeff 𝔪 ψ) 2 n‖) *
          Real.exp ((M₀ + 2 * d) * (1 + ‖s‖) * Real.log (2 + ‖s‖)) := by
        rw [← Real.exp_add, mul_comm]
        ring_nf

/-! ### Three regions -/

/-- **Order one from a half-plane, a strip and a functional equation.** -/
theorem exists_orderOne_of_three_regions {E E' : ℂ → ℂ} {W : ℂ} (hW : ‖W‖ = 1)
    (hFE : ∀ s, E (1 - s) = W * E' s) {C₁ : ℝ} (hC₁ : 0 ≤ C₁)
    (hright : ∀ s : ℂ, 2 ≤ s.re →
      ‖E s‖ ≤ Real.exp (C₁ * (1 + ‖s‖) * Real.log (2 + ‖s‖)))
    (hright' : ∀ s : ℂ, 2 ≤ s.re →
      ‖E' s‖ ≤ Real.exp (C₁ * (1 + ‖s‖) * Real.log (2 + ‖s‖)))
    {B : ℝ} {N : ℕ} (hstrip : ∀ s : ℂ, -1 ≤ s.re → s.re ≤ 2 → ‖E s‖ ≤ B * (1 + ‖s‖) ^ N) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s, ‖E s‖ ≤ Real.exp (C * (1 + ‖s‖) * Real.log (2 + ‖s‖)) := by
  obtain ⟨C₂, hC₂0, hC₂⟩ := exists_envelope_absorb B N (le_refl (0 : ℝ))
  refine ⟨4 * C₁ + C₂, by positivity, fun s => ?_⟩
  have hx := norm_nonneg s
  have hL0 : 0 ≤ Real.log (2 + ‖s‖) := Real.log_nonneg (by linarith)
  have hmono : ∀ C' : ℝ, C' ≤ 4 * C₁ + C₂ →
      Real.exp (C' * (1 + ‖s‖) * Real.log (2 + ‖s‖)) ≤
        Real.exp ((4 * C₁ + C₂) * (1 + ‖s‖) * Real.log (2 + ‖s‖)) := by
    intro C' hC'
    rw [Real.exp_le_exp]
    have : 0 ≤ (1 + ‖s‖) * Real.log (2 + ‖s‖) := mul_nonneg (by positivity) hL0
    nlinarith
  rcases le_or_gt 2 s.re with h2 | h2
  · exact (hright s h2).trans (hmono C₁ (by linarith))
  rcases le_or_gt (-1) s.re with h1 | h1
  · have := hC₂ ‖s‖ hx
    simp only [zero_mul, Real.exp_zero, mul_one] at this
    exact ((hstrip s h1 h2.le).trans this).trans (hmono C₂ (by linarith))
  · have hflip : ‖E s‖ = ‖E' (1 - s)‖ := by
      have := hFE (1 - s)
      rw [sub_sub_cancel] at this
      rw [this, norm_mul, hW, one_mul]
    rw [hflip]
    have hre : 2 ≤ (1 - s).re := by
      rw [Complex.sub_re, Complex.one_re]
      linarith
    refine (hright' (1 - s) hre).trans ?_
    have hn : ‖1 - s‖ ≤ 1 + ‖s‖ := by
      calc ‖1 - s‖ ≤ ‖(1 : ℂ)‖ + ‖s‖ := norm_sub_le _ _
        _ = 1 + ‖s‖ := by rw [norm_one]
    refine le_trans ?_ (hmono (4 * C₁) (by linarith))
    rw [Real.exp_le_exp]
    have hl : Real.log (2 + ‖1 - s‖) ≤ 2 * Real.log (2 + ‖s‖) := by
      rw [← Real.log_rpow (by positivity)]
      refine Real.log_le_log (by positivity) ?_
      norm_num
      nlinarith
    have hl0 : 0 ≤ Real.log (2 + ‖1 - s‖) := Real.log_nonneg (by linarith [norm_nonneg (1 - s)])
    calc C₁ * (1 + ‖1 - s‖) * Real.log (2 + ‖1 - s‖)
        ≤ C₁ * (2 * (1 + ‖s‖)) * (2 * Real.log (2 + ‖s‖)) :=
          mul_le_mul (mul_le_mul_of_nonneg_left (by linarith) hC₁) hl hl0 (by positivity)
      _ = 4 * C₁ * (1 + ‖s‖) * Real.log (2 + ‖s‖) := by ring

/-! ### Order one -/

/-- The pole-cleared completion on `Re s ≥ 2`, in envelope form. -/
theorem exists_halfPlane_envelope_heckePoleClearedCompletion (ψ : HeckeCharacter 𝔪) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, 2 ≤ s.re →
      ‖heckePoleClearedCompletion 𝔪 ψ s‖ ≤ Real.exp (C * (1 + ‖s‖) * Real.log (2 + ‖s‖)) := by
  obtain ⟨S, M, hS, hM, hb⟩ := exists_halfPlane_bound_heckeCompletedLFunction 𝔪 ψ
  obtain ⟨C, hC, hab⟩ := exists_envelope_absorb S 2 hM
  refine ⟨C, hC, fun s hs => le_trans ?_ (hab ‖s‖ (norm_nonneg s))⟩
  have hr := norm_nonneg s
  have hs0 : s ≠ 0 := by
    rintro rfl
    rw [Complex.zero_re] at hs
    linarith
  have hs1 : s ≠ 1 := by
    rintro rfl
    rw [Complex.one_re] at hs
    linarith
  have hsub : ‖s - 1‖ ≤ 1 + ‖s‖ := by
    calc ‖s - 1‖ ≤ ‖s‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 1 + ‖s‖ := by rw [norm_one, add_comm]
  have hprod : ‖s‖ * ‖s - 1‖ ≤ (1 + ‖s‖) ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hsub hr]
  rw [heckePoleClearedCompletion_eq 𝔪 ψ hs0 hs1, norm_mul, norm_mul]
  calc ‖s‖ * ‖s - 1‖ * ‖heckeCompletedLFunction 𝔪 ψ s‖
      ≤ (1 + ‖s‖) ^ 2 * (S * Real.exp (M * (1 + ‖s‖) * Real.log (2 + ‖s‖))) :=
        mul_le_mul hprod (hb s hs) (norm_nonneg _) (by positivity)
    _ = S * (1 + ‖s‖) ^ 2 * Real.exp (M * (1 + ‖s‖) * Real.log (2 + ‖s‖)) := by ring

/-- **The pole-cleared completion of a primitive Hecke character has order one.** -/
theorem exists_orderOne_heckePoleClearedCompletion (ψ : HeckeCharacter 𝔪)
    (hψ : heckeFiniteConductor 𝔪 ψ = 𝔪.fin) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s, ‖heckePoleClearedCompletion 𝔪 ψ s‖ ≤
      Real.exp (C * (1 + ‖s‖) * Real.log (2 + ‖s‖)) := by
  obtain ⟨C₁, hC₁, h₁⟩ := exists_halfPlane_envelope_heckePoleClearedCompletion 𝔪 ψ
  obtain ⟨C₂, hC₂, h₂⟩ := exists_halfPlane_envelope_heckePoleClearedCompletion 𝔪 ψ⁻¹
  obtain ⟨B, hB⟩ := exists_strip_bound_heckePoleClearedCompletion 𝔪 ψ
  have hmono : ∀ {C C' : ℝ}, C ≤ C' → ∀ s : ℂ,
      Real.exp (C * (1 + ‖s‖) * Real.log (2 + ‖s‖)) ≤
        Real.exp (C' * (1 + ‖s‖) * Real.log (2 + ‖s‖)) := by
    intro C C' h s
    rw [Real.exp_le_exp]
    have hL0 : 0 ≤ Real.log (2 + ‖s‖) := Real.log_nonneg (by linarith [norm_nonneg s])
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right h (by positivity)) hL0
  exact exists_orderOne_of_three_regions (norm_heckeRootNumber 𝔪 ψ hψ)
    (heckePoleClearedCompletion_reflection 𝔪 ψ hψ) (le_max_of_le_left hC₁)
    (fun s hs => (h₁ s hs).trans (hmono (le_max_left C₁ C₂) s))
    (fun s hs => (h₂ s hs).trans (hmono (le_max_right C₁ C₂) s)) hB

theorem inv_ne_one_of_ne_one {ψ : HeckeCharacter 𝔪} (hψ1 : ψ ≠ 1) : ψ⁻¹ ≠ 1 := by
  intro h
  apply hψ1
  apply MonoidHom.ext
  intro g
  have hg := DFunLike.congr_fun h g
  change (ψ g)⁻¹ = 1 at hg
  change ψ g = 1
  exact inv_eq_one.mp hg

/-- **The completed function of a nontrivial primitive Hecke character has order one.** -/
theorem exists_orderOne_heckeCompletedLFunction {ψ : HeckeCharacter 𝔪}
    (hψ : heckeFiniteConductor 𝔪 ψ = 𝔪.fin) (hψ1 : ψ ≠ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s, ‖heckeCompletedLFunction 𝔪 ψ s‖ ≤
      Real.exp (C * (1 + ‖s‖) * Real.log (2 + ‖s‖)) := by
  obtain ⟨S₁, M₁, -, hM₁, h₁⟩ := exists_halfPlane_bound_heckeCompletedLFunction 𝔪 ψ
  obtain ⟨S₂, M₂, -, hM₂, h₂⟩ := exists_halfPlane_bound_heckeCompletedLFunction 𝔪 ψ⁻¹
  obtain ⟨C₁, hC₁, e₁⟩ := exists_envelope_absorb S₁ 0 hM₁
  obtain ⟨C₂, hC₂, e₂⟩ := exists_envelope_absorb S₂ 0 hM₂
  obtain ⟨C, hC⟩ := stripBounded_heckeGammaCompletedRegularPart 𝔪 ψ (-1) 2
  have hN1 := one_le_heckeCompletionNorm 𝔪
  have hmono : ∀ {C C' : ℝ}, C ≤ C' → ∀ s : ℂ,
      Real.exp (C * (1 + ‖s‖) * Real.log (2 + ‖s‖)) ≤
        Real.exp (C' * (1 + ‖s‖) * Real.log (2 + ‖s‖)) := by
    intro C C' h s
    rw [Real.exp_le_exp]
    have hL0 : 0 ≤ Real.log (2 + ‖s‖) := Real.log_nonneg (by linarith [norm_nonneg s])
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right h (by positivity)) hL0
  have hstrip : ∀ s : ℂ, -1 ≤ s.re → s.re ≤ 2 →
      ‖heckeCompletedLFunction 𝔪 ψ s‖ ≤ ((heckeCompletionNorm 𝔪 : ℝ) * max C 0) * (1 + ‖s‖) ^ 0 := by
    intro s h0 h1
    have hfac : ‖heckeCompletionFactor 𝔪 s‖ ≤ heckeCompletionNorm 𝔪 := by
      rw [norm_heckeCompletionFactor]
      calc (heckeCompletionNorm 𝔪 : ℝ) ^ (s.re / 2) ≤ (heckeCompletionNorm 𝔪 : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
        _ = heckeCompletionNorm 𝔪 := Real.rpow_one _
    rw [pow_zero, mul_one, heckeCompletedLFunction, heckeGammaCompletedLFunction,
      heckeGammaCompletedZeroCoefficient_eq_zero 𝔪 hψ1,
      heckeGammaCompletedOneCoefficient_eq_zero 𝔪 hψ1, zero_div, zero_div, add_zero, add_zero,
      norm_mul]
    exact mul_le_mul hfac ((hC s h0 h1).trans (le_max_left C 0)) (norm_nonneg _)
      (Nat.cast_nonneg _)
  refine exists_orderOne_of_three_regions (C₁ := max C₁ C₂) (norm_heckeRootNumber 𝔪 ψ hψ)
    (heckeCompletedLFunction_reflection_entire 𝔪 hψ hψ1) (le_max_of_le_left hC₁)
    (fun s hs => ?_) (fun s hs => ?_) hstrip
  · have := e₁ ‖s‖ (norm_nonneg s)
    rw [pow_zero, mul_one] at this
    exact ((h₁ s hs).trans this).trans (hmono (le_max_left C₁ C₂) s)
  · have := e₂ ‖s‖ (norm_nonneg s)
    rw [pow_zero, mul_one] at this
    exact ((h₂ s hs).trans this).trans (hmono (le_max_right C₁ C₂) s)

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
