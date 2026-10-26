import GaloisForLFunctions.ArithmeticPositiveDuality.TheExtensionsOfWeilsCorrelationAreIndexedByTheZeros

/-!
# Every point of the atomic box is an extension

`hasSum_affine_of_atomic` shows that an extension of an atomic archimedean correlation
`Σ_x c_x u^{ix}` to `Aff(ℚ)` has `φ(x ↦ ux + b) = Σ_x α_x u^{ix}` for `b ≠ 0` with
`0 ≤ α_x ≤ c_x`. This file proves the converse.

**Theorem** (`isPosDefOnGroup_boxExtension`, `boxExtension_affine`). For countably many
frequencies `x_a`, summable weights `c_a ≥ 0` and any `0 ≤ α_a ≤ c_a`,
`Ψ(g) = Σ_a u^{ix_a}(α_a + (c_a − α_a)·1[g is a dilation])`, `u = |slope g|`,
is positive definite on `Aff(ℚ)`, with `Ψ(x ↦ ux) = Σ_a c_a u^{ix_a}` and
`Ψ(x ↦ ux + b) = Σ_a α_a u^{ix_a}` for `u > 0`, `b ≠ 0`.

**Corollary** (`weil_extension_exists`). Under full-cone Weil positivity of `Λ` (equivalently RH),
every choice `0 ≤ α_x ≤ ν_W{x}` on the atoms of Weil's spectral measure is realized by a
positive-definite extension of Weil's correlation. With `weil_extension_classification`: the
extensions of Weil's correlation to the affine group, read on positive slopes, are exactly the
points of the box `Π_γ [0, w_γ]` over the critical zeros.

Mechanism. Positive definiteness is closed under pointwise limits (`IsPosDefOnGroup.of_tendsto`);
finite partial sums are sums of a slope character and a slope character induced from the dilations
(`isPosDefOnGroup_archSlope`, `isPosDefOnGroup_extendFromSubgroup`).
-/

open Complex MeasureTheory Filter Topology Finset
open scoped InnerProductSpace ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality

/-- **Positive definiteness is closed under pointwise limits.** -/
theorem IsPosDefOnGroup.of_tendsto {G ι : Type*} [Group G] {l : Filter ι} [l.NeBot]
    {F : ι → G → ℂ} (hF : ∀ i, IsPosDefOnGroup (F i)) {φ : G → ℂ}
    (h : ∀ g, Tendsto (fun i => F i g) l (𝓝 (φ g))) : IsPosDefOnGroup φ := by
  intro N x c
  set S : Set ℂ := {z | z.im = 0 ∧ 0 ≤ z.re}
  have hS : IsClosed S :=
    (isClosed_eq Complex.continuous_im continuous_const).inter
      (isClosed_le continuous_const Complex.continuous_re)
  have hlim : Tendsto (fun i => ∑ a, ∑ b, star (c a) * F i ((x a)⁻¹ * x b) * c b) l
      (𝓝 (∑ a, ∑ b, star (c a) * φ ((x a)⁻¹ * x b) * c b)) :=
    tendsto_finsetSum _ fun a _ => tendsto_finsetSum _ fun b _ =>
      ((tendsto_const_nhds.mul (h _)).mul tendsto_const_nhds)
  have hmem : ∀ i, (∑ a, ∑ b, star (c a) * F i ((x a)⁻¹ * x b) * c b) ∈ S := fun i => by
    obtain ⟨r, hr, hq⟩ := hF i N x c
    rw [hq]; exact ⟨Complex.ofReal_im r, by rwa [Complex.ofReal_re]⟩
  obtain ⟨him, hre⟩ := hS.mem_of_tendsto hlim (Eventually.of_forall hmem)
  exact ⟨_, hre, Complex.ext (by simp) (by simpa using him)⟩

section Box

variable {A : Type*} (x : A → ℝ) (c α : A → ℝ)

/-- One atom of the box: `u^{ix}(α + (c − α)·1[dilation])`. -/
def boxTerm (a : A) (g : AffineGroupQ) : ℂ :=
  (α a : ℂ) * archChar (x a) |affSlope g| +
    extendFromSubgroup dilationRange
      (fun h => ((c a - α a : ℝ) : ℂ) * archChar (x a) |affSlope (h : AffineGroupQ)|) g

/-- The box extension `Ψ = Σ_a boxTerm a`. -/
def boxExtension (g : AffineGroupQ) : ℂ := ∑' a, boxTerm x c α a g

variable {x c α}

theorem norm_boxTerm_le (hα : ∀ a, 0 ≤ α a ∧ α a ≤ c a) (a : A) (g : AffineGroupQ) :
    ‖boxTerm x c α a g‖ ≤ 2 * c a := by
  unfold boxTerm extendFromSubgroup
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, Complex.norm_real, norm_archChar, mul_one, Real.norm_of_nonneg (hα a).1]
  split_ifs
  · rw [norm_mul, Complex.norm_real, norm_archChar, mul_one,
      Real.norm_of_nonneg (sub_nonneg.mpr (hα a).2)]
    linarith [(hα a).1, (hα a).2]
  · rw [norm_zero]; linarith [(hα a).1, (hα a).2]

theorem isPosDefOnGroup_boxTerm (hα : ∀ a, 0 ≤ α a ∧ α a ≤ c a) (a : A) :
    IsPosDefOnGroup (boxTerm x c α a) :=
  ((isPosDefOnGroup_archChar_slope (x a)).const_mul' (hα a).1).add
    (isPosDefOnGroup_extendFromSubgroup
      ((((isPosDefOnGroup_archChar_slope (x a)).const_mul'
        (sub_nonneg.mpr (hα a).2))).restrict dilationRange))

theorem summable_boxTerm (hα : ∀ a, 0 ≤ α a ∧ α a ≤ c a) (hc : Summable c) (g : AffineGroupQ) :
    Summable fun a => boxTerm x c α a g :=
  Summable.of_norm_bounded (hc.mul_left 2) fun a => norm_boxTerm_le hα a g

/-- **Every point of the box is positive definite.** -/
theorem isPosDefOnGroup_boxExtension (hα : ∀ a, 0 ≤ α a ∧ α a ≤ c a) (hc : Summable c) :
    IsPosDefOnGroup (boxExtension x c α) :=
  IsPosDefOnGroup.of_tendsto (l := atTop)
    (fun s => isPosDefOnGroup_finset_sum s _ fun a _ => isPosDefOnGroup_boxTerm hα a)
    fun g => (summable_boxTerm hα hc g).hasSum

theorem boxTerm_affine (a : A) (b : ℚ) {u : ℚˣ} (hu : 0 < (u : ℚ)) :
    boxTerm x c α a (translation b * dilation u) =
      ((if b = 0 then c a else α a : ℝ) : ℂ) * archChar (x a) u := by
  have hslope : affSlope (translation b * dilation u) = u := by
    rw [affSlope_mul, affSlope_translation, affSlope_dilation, one_mul]
  have hshift : affShift (translation b * dilation u) = b := by
    rw [affShift_mul, affSlope_translation, affShift_dilation, affShift_translation]; ring
  have habs : |affSlope (translation b * dilation u)| = u := by rw [hslope, abs_of_pos hu]
  unfold boxTerm extendFromSubgroup
  by_cases hb : b = 0
  · have hmem : translation b * dilation u ∈ dilationRange := by
      rw [mem_dilationRange_iff, hshift, hb]
    simp only [dif_pos hmem, if_pos hb, habs]
    push_cast
    ring
  · have hmem : translation b * dilation u ∉ dilationRange := by
      rw [mem_dilationRange_iff, hshift]; exact hb
    rw [dif_neg hmem, if_neg hb, habs, add_zero]

/-- The values of the box extension on positive slopes. -/
theorem hasSum_boxExtension_affine (hα : ∀ a, 0 ≤ α a ∧ α a ≤ c a) (hc : Summable c) (b : ℚ)
    {u : ℚˣ} (hu : 0 < (u : ℚ)) :
    HasSum (fun a => ((if b = 0 then c a else α a : ℝ) : ℂ) * archChar (x a) u)
      (boxExtension x c α (translation b * dilation u)) := by
  have h : HasSum (fun a => boxTerm x c α a (translation b * dilation u))
      (boxExtension x c α (translation b * dilation u)) :=
    (summable_boxTerm hα hc (translation b * dilation u)).hasSum
  convert h using 1
  funext a
  exact (boxTerm_affine a b hu).symm

end Box

/-! ### Weil's extensions -/

variable (hW : RHTower.WeilPositiveFull fun n => (ArithmeticFunction.vonMangoldt n : ℝ))

/-- The atoms of `ν_W` and their weights. -/
abbrev weilAtoms : Type := {x : ℝ // 0 < weilMeasure hW {x}}

theorem summable_weilAtomWeight : Summable fun a : weilAtoms hW => (weilMeasure hW).real {(a : ℝ)} := by
  refine summable_of_sum_le (fun a => measureReal_nonneg) (c := (weilMeasure hW).real Set.univ)
    fun s => ?_
  calc ∑ a ∈ s, (weilMeasure hW).real {(a : ℝ)}
      = (weilMeasure hW).real (s.map (Function.Embedding.subtype _) : Set ℝ) := by
        rw [← sum_measureReal_singleton, Finset.sum_map]; rfl
    _ ≤ _ := measureReal_mono (Set.subset_univ _)

/-- Weil's correlation is the sum over the atoms of `ν_W`. -/
theorem hasSum_ratCorr (u : posUnits) :
    HasSum (fun a : weilAtoms hW => ((weilMeasure hW).real {(a : ℝ)} : ℂ) *
      archChar a ((u : ℚˣ) : ℚ)) (ratCorr u) := by
  set ν := weilMeasure hW
  set A : Set ℝ := {x | 0 < ν {x}}
  have hA : A.Countable := Measure.countable_meas_pos_of_disjoint_iUnion
    (As := fun x : ℝ => ({x} : Set ℝ)) (fun x => measurableSet_singleton x)
    (fun x y hxy => Set.disjoint_singleton.mpr hxy)
  have hcompl : ν Aᶜ = 0 := by
    have : Aᶜ = {x : ℝ | ν {x} = 0} := by
      ext x; simp only [Set.mem_setOf_eq, Set.mem_compl_iff, A, not_lt, nonpos_iff_eq_zero]
    rw [this]; exact weilMeasure_nonatomic_null hW
  have hrestrict : ν.restrict A = ν := Measure.restrict_eq_self_of_ae_mem (ae_iff.mpr hcompl)
  have hint : Integrable (fun x : ℝ => archChar x ((u : ℚˣ) : ℚ)) ν :=
    Integrable.of_bound (continuous_archChar_left _).aestronglyMeasurable 1
      (Eventually.of_forall fun x => (norm_archChar _ _).le)
  have hsum : Summable fun a : weilAtoms hW =>
      ((ν.real {(a : ℝ)} : ℂ) * archChar a ((u : ℚˣ) : ℚ)) :=
    Summable.of_norm_bounded (summable_weilAtomWeight hW) fun a => by
      rw [norm_mul, Complex.norm_real, norm_archChar, mul_one, Real.norm_of_nonneg measureReal_nonneg]
  have key : ratCorr u = ∑' a : A, ν.real {(a : ℝ)} • archChar a ((u : ℚˣ) : ℚ) := by
    rw [ratCorr_eq_integral_weilMeasure hW]
    change ∫ x, archChar x ((u : ℚˣ) : ℚ) ∂ν = _
    conv_lhs => rw [← hrestrict]
    exact setIntegral_countable _ hA hint.integrableOn
  rw [key]
  simp only [Complex.real_smul]
  exact hsum.hasSum

/-- **Every point of the box over the zeros is an extension of Weil's correlation.** -/
theorem weil_extension_exists (α : ℝ → ℝ)
    (hα : ∀ x, 0 ≤ α x ∧ α x ≤ (weilMeasure hW).real {x}) :
    ∃ φ : AffineGroupQ → ℂ, IsPosDefOnGroup φ ∧
      (∀ u : posUnits, φ (dilation (u : ℚˣ)) = ratCorr u) ∧
      ∀ u : ℚˣ, 0 < (u : ℚ) → ∀ b : ℚ, b ≠ 0 →
        HasSum (fun a : weilAtoms hW => (α a : ℂ) * archChar a u) (φ (translation b * dilation u)) := by
  set x : weilAtoms hW → ℝ := fun a => a
  set c : weilAtoms hW → ℝ := fun a => (weilMeasure hW).real {(a : ℝ)}
  have hα' : ∀ a : weilAtoms hW, 0 ≤ α a ∧ α a ≤ c a := fun a => hα a
  refine ⟨boxExtension x c (fun a => α a), isPosDefOnGroup_boxExtension hα' (summable_weilAtomWeight hW),
    fun u => ?_, fun u hu b hb => ?_⟩
  · have h1 := hasSum_boxExtension_affine (x := x) hα' (summable_weilAtomWeight hW) 0
      (u := (u : ℚˣ)) u.2
    simp only [translation_zero, one_mul] at h1
    exact h1.unique (hasSum_ratCorr hW u)
  · have h1 := hasSum_boxExtension_affine (x := x) hα' (summable_weilAtomWeight hW) b hu
    simp only [if_neg hb] at h1
    exact h1

end GaloisForLFunctions.ArithmeticPositiveDuality
