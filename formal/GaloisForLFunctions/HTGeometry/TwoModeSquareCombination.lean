import GaloisForLFunctions.HTGeometry.IntegralCauchySchwarz

/-!
# A vanishing admixture does not move a limit of squared masses

If the squared mass of `f` converges and the squared mass of `g` vanishes, then the squared mass of
`f + g` converges to the same limit: the cross term is controlled by Cauchy--Schwarz,
`|∫ f g| ≤ √(∫f² · ∫g²)`, and one factor tends to zero.

This is the shape a two-mode source takes when one of its two modes is asymptotically negligible:
the surviving mode keeps its limit, the vanishing mode contributes nothing, and the cross term
disappears with it.  Scaling the surviving mode by a convergent coefficient multiplies the limit by
the square of that coefficient, and scaling the negligible mode by a coefficient tending to zero
keeps it negligible even when its own squared mass does not vanish.

The measurability and integrability hypotheses are only required eventually along the filter, which
is what an asymptotic family of solutions of a differential equation supplies.
-/

open MeasureTheory Filter

open scoped Topology

namespace GaloisForLFunctions.HTGeometry

variable {ι : Type*} {l : Filter ι} {μ : Measure ℝ}

/-- The cross term is bounded by the geometric mean of the two masses. -/
theorem abs_integral_mul_le_sqrt {f g : ℝ → ℝ}
    (hfm : AEStronglyMeasurable f μ) (hgm : AEStronglyMeasurable g μ)
    (hf2 : Integrable (fun x => f x ^ (2 : ℕ)) μ) (hg2 : Integrable (fun x => g x ^ (2 : ℕ)) μ) :
    |∫ y, f y * g y ∂μ| ≤ Real.sqrt ((∫ y, f y ^ (2 : ℕ) ∂μ) * ∫ y, g y ^ (2 : ℕ) ∂μ) := by
  have hsq := sq_integral_mul_le hfm hgm hf2 hg2
  have habs : |∫ y, f y * g y ∂μ| = Real.sqrt ((∫ y, f y * g y ∂μ) ^ (2 : ℕ)) :=
    (Real.sqrt_sq_eq_abs _).symm
  rw [habs]
  exact Real.sqrt_le_sqrt hsq

/-- Expanding the square of a sum under the integral. -/
theorem integral_sq_add {f g : ℝ → ℝ}
    (hfm : AEStronglyMeasurable f μ) (hgm : AEStronglyMeasurable g μ)
    (hf2 : Integrable (fun x => f x ^ (2 : ℕ)) μ) (hg2 : Integrable (fun x => g x ^ (2 : ℕ)) μ) :
    ∫ x, (f x + g x) ^ (2 : ℕ) ∂μ
      = (∫ x, f x ^ (2 : ℕ) ∂μ) + 2 * (∫ x, f x * g x ∂μ) + ∫ x, g x ^ (2 : ℕ) ∂μ := by
  have hfg : Integrable (fun x => f x * g x) μ :=
    integrable_mul_of_sq_integrable hfm hgm hf2 hg2
  have hfg2 : Integrable (fun x => 2 * (f x * g x)) μ := hfg.const_mul 2
  calc ∫ x, (f x + g x) ^ (2 : ℕ) ∂μ
      = ∫ x, (f x ^ (2 : ℕ) + 2 * (f x * g x)) + g x ^ (2 : ℕ) ∂μ := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        ring
    _ = (∫ x, (f x ^ (2 : ℕ) + 2 * (f x * g x)) ∂μ) + ∫ x, g x ^ (2 : ℕ) ∂μ :=
        integral_add (hf2.add hfg2) hg2
    _ = ((∫ x, f x ^ (2 : ℕ) ∂μ) + ∫ x, 2 * (f x * g x) ∂μ) + ∫ x, g x ^ (2 : ℕ) ∂μ := by
        rw [integral_add hf2 hfg2]
    _ = (∫ x, f x ^ (2 : ℕ) ∂μ) + 2 * (∫ x, f x * g x ∂μ) + ∫ x, g x ^ (2 : ℕ) ∂μ := by
        rw [integral_const_mul]

/-- Rescaling a family by a fixed factor rescales its squared mass by the square of that
factor. -/
theorem integral_sq_const_mul (c : ℝ) (f : ℝ → ℝ) :
    ∫ x, (c * f x) ^ (2 : ℕ) ∂μ = c ^ (2 : ℕ) * ∫ x, f x ^ (2 : ℕ) ∂μ := by
  rw [show (fun x => (c * f x) ^ (2 : ℕ)) = fun x => c ^ (2 : ℕ) * f x ^ (2 : ℕ) from by funext x; ring,
    integral_const_mul]

/-- **A vanishing admixture does not move the limit.** -/
theorem tendsto_integral_sq_add_of_tendsto_zero {f g : ι → ℝ → ℝ} {A : ℝ}
    (hfm : ∀ᶠ i in l, AEStronglyMeasurable (f i) μ)
    (hgm : ∀ᶠ i in l, AEStronglyMeasurable (g i) μ)
    (hf2 : ∀ᶠ i in l, Integrable (fun x => f i x ^ (2 : ℕ)) μ)
    (hg2 : ∀ᶠ i in l, Integrable (fun x => g i x ^ (2 : ℕ)) μ)
    (hfA : Tendsto (fun i => ∫ x, f i x ^ (2 : ℕ) ∂μ) l (𝓝 A))
    (hg0 : Tendsto (fun i => ∫ x, g i x ^ (2 : ℕ) ∂μ) l (𝓝 0)) :
    Tendsto (fun i => ∫ x, (f i x + g i x) ^ (2 : ℕ) ∂μ) l (𝓝 A) := by
  have hmaj : Tendsto
      (fun i => 2 * Real.sqrt ((∫ x, f i x ^ (2 : ℕ) ∂μ) * ∫ x, g i x ^ (2 : ℕ) ∂μ)
        + ∫ x, g i x ^ (2 : ℕ) ∂μ) l (𝓝 0) := by
    have hprod : Tendsto (fun i => (∫ x, f i x ^ (2 : ℕ) ∂μ) * ∫ x, g i x ^ (2 : ℕ) ∂μ) l (𝓝 0) := by
      have := hfA.mul hg0
      rwa [mul_zero] at this
    have hsqrt : Tendsto
        (fun i => Real.sqrt ((∫ x, f i x ^ (2 : ℕ) ∂μ) * ∫ x, g i x ^ (2 : ℕ) ∂μ)) l (𝓝 0) := by
      have h := (Real.continuous_sqrt.tendsto (0 : ℝ)).comp hprod
      rw [Real.sqrt_zero] at h
      exact h
    have := (hsqrt.const_mul 2).add hg0
    simpa using this
  have hdiff : Tendsto
      (fun i => (∫ x, (f i x + g i x) ^ (2 : ℕ) ∂μ) - ∫ x, f i x ^ (2 : ℕ) ∂μ) l (𝓝 0) := by
    refine squeeze_zero_norm' (a := fun i =>
      2 * Real.sqrt ((∫ x, f i x ^ (2 : ℕ) ∂μ) * ∫ x, g i x ^ (2 : ℕ) ∂μ) + ∫ x, g i x ^ (2 : ℕ) ∂μ) ?_ hmaj
    filter_upwards [hfm, hgm, hf2, hg2] with i hfmi hgmi hf2i hg2i
    rw [integral_sq_add hfmi hgmi hf2i hg2i]
    have hnn : (0 : ℝ) ≤ ∫ x, g i x ^ (2 : ℕ) ∂μ :=
      integral_nonneg fun x => sq_nonneg _
    have hcs := abs_integral_mul_le_sqrt hfmi hgmi hf2i hg2i
    rw [Real.norm_eq_abs,
      show (∫ x, f i x ^ (2 : ℕ) ∂μ) + 2 * (∫ x, f i x * g i x ∂μ) + (∫ x, g i x ^ (2 : ℕ) ∂μ)
          - ∫ x, f i x ^ (2 : ℕ) ∂μ
        = 2 * (∫ x, f i x * g i x ∂μ) + ∫ x, g i x ^ (2 : ℕ) ∂μ from by ring]
    calc |2 * (∫ x, f i x * g i x ∂μ) + ∫ x, g i x ^ (2 : ℕ) ∂μ|
        ≤ |2 * (∫ x, f i x * g i x ∂μ)| + |∫ x, g i x ^ (2 : ℕ) ∂μ| := abs_add_le _ _
      _ = 2 * |∫ x, f i x * g i x ∂μ| + ∫ x, g i x ^ (2 : ℕ) ∂μ := by
          rw [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2), abs_of_nonneg hnn]
      _ ≤ 2 * Real.sqrt ((∫ x, f i x ^ (2 : ℕ) ∂μ) * ∫ x, g i x ^ (2 : ℕ) ∂μ) + ∫ x, g i x ^ (2 : ℕ) ∂μ := by
          have := mul_le_mul_of_nonneg_left hcs (by norm_num : (0:ℝ) ≤ 2)
          linarith
  have h := hdiff.add hfA
  simpa using h

/-- **Two-mode combination with variable coefficients.**  The negligible mode is only required to
have a bounded squared mass; its coefficient tending to zero is what removes it, together with the
cross term.  The surviving mode's limit is multiplied by the square of the limiting coefficient. -/
theorem tendsto_integral_sq_two_mode {f g : ι → ℝ → ℝ} {b c : ι → ℝ} {A B b₀ : ℝ}
    (hfm : ∀ᶠ i in l, AEStronglyMeasurable (f i) μ)
    (hgm : ∀ᶠ i in l, AEStronglyMeasurable (g i) μ)
    (hf2 : ∀ᶠ i in l, Integrable (fun x => f i x ^ (2 : ℕ)) μ)
    (hg2 : ∀ᶠ i in l, Integrable (fun x => g i x ^ (2 : ℕ)) μ)
    (hfA : Tendsto (fun i => ∫ x, f i x ^ (2 : ℕ) ∂μ) l (𝓝 A))
    (hgB : Tendsto (fun i => ∫ x, g i x ^ (2 : ℕ) ∂μ) l (𝓝 B))
    (hb : Tendsto b l (𝓝 b₀)) (hc : Tendsto c l (𝓝 0)) :
    Tendsto (fun i => ∫ x, (b i * f i x + c i * g i x) ^ (2 : ℕ) ∂μ) l (𝓝 (b₀ ^ (2 : ℕ) * A)) := by
  have hbf : Tendsto (fun i => ∫ x, (b i * f i x) ^ (2 : ℕ) ∂μ) l (𝓝 (b₀ ^ (2 : ℕ) * A)) := by
    refine ((hb.pow 2).mul hfA).congr fun i => ?_
    exact (integral_sq_const_mul (b i) (f i)).symm
  have hcg : Tendsto (fun i => ∫ x, (c i * g i x) ^ (2 : ℕ) ∂μ) l (𝓝 0) := by
    have h := (hc.pow 2).mul hgB
    rw [show (0 : ℝ) ^ (2 : ℕ) * B = 0 from by ring] at h
    exact h.congr fun i => (integral_sq_const_mul (c i) (g i)).symm
  refine tendsto_integral_sq_add_of_tendsto_zero
    (f := fun i x => b i * f i x) (g := fun i x => c i * g i x)
    (hfm.mono fun i h => h.const_mul (b i)) (hgm.mono fun i h => h.const_mul (c i))
    ?_ ?_ hbf hcg
  · filter_upwards [hf2] with i h
    refine (h.const_mul (b i ^ (2 : ℕ))).congr ?_
    filter_upwards with x
    ring
  · filter_upwards [hg2] with i h
    refine (h.const_mul (c i ^ (2 : ℕ))).congr ?_
    filter_upwards with x
    ring

/-! ## Bilinear form of the two-mode combination -/

/-- A family that is eventually measurable, eventually square-integrable, and whose squared masses
are eventually bounded by one fixed constant. -/
def SqBoundedFamily (μ : Measure ℝ) (l : Filter ι) (M : ℝ) (u : ι → ℝ → ℝ) : Prop :=
  ∀ᶠ i in l, AEStronglyMeasurable (u i) μ ∧ Integrable (fun x => u i x ^ (2 : ℕ)) μ
    ∧ ∫ x, u i x ^ (2 : ℕ) ∂μ ≤ M

theorem SqBoundedFamily.mono {M M' : ℝ} {u : ι → ℝ → ℝ} (h : SqBoundedFamily μ l M u)
    (hMM : M ≤ M') : SqBoundedFamily μ l M' u :=
  Filter.Eventually.mono h fun _ hi => ⟨hi.1, hi.2.1, hi.2.2.trans hMM⟩

/-- A bilinear pairing of two uniformly square-bounded families vanishes once it is weighted by a
coefficient tending to zero: Cauchy--Schwarz keeps the pairing bounded. -/
theorem tendsto_mul_integral_mul_of_tendsto_zero {u v : ι → ℝ → ℝ} {w : ι → ℝ} {M : ℝ}
    (hu : SqBoundedFamily μ l M u) (hv : SqBoundedFamily μ l M v)
    (hw : Tendsto w l (𝓝 0)) :
    Tendsto (fun i => w i * ∫ x, u i x * v i x ∂μ) l (𝓝 0) := by
  refine squeeze_zero_norm' (a := fun i => |w i| * M) ?_ ?_
  · filter_upwards [hu, hv] with i ⟨hum, hu2, hUM⟩ ⟨hvm, hv2, hVM⟩
    have hnnu : (0 : ℝ) ≤ ∫ x, u i x ^ (2 : ℕ) ∂μ := integral_nonneg fun x => sq_nonneg _
    have hnnv : (0 : ℝ) ≤ ∫ x, v i x ^ (2 : ℕ) ∂μ := integral_nonneg fun x => sq_nonneg _
    have hM : (0 : ℝ) ≤ M := hnnu.trans hUM
    have hprod : (∫ x, u i x ^ (2 : ℕ) ∂μ) * (∫ x, v i x ^ (2 : ℕ) ∂μ) ≤ M * M :=
      mul_le_mul hUM hVM hnnv hM
    have hsqrt : Real.sqrt ((∫ x, u i x ^ (2 : ℕ) ∂μ) * ∫ x, v i x ^ (2 : ℕ) ∂μ) ≤ M := by
      rw [show M = Real.sqrt (M * M) from (Real.sqrt_mul_self hM).symm]
      exact Real.sqrt_le_sqrt hprod
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_left
      ((abs_integral_mul_le_sqrt hum hvm hu2 hv2).trans hsqrt) (abs_nonneg _)
  · have h := hw.abs.mul_const M
    simpa using h

/-- Expanding a bilinear pairing of two two-mode combinations into its four blocks. -/
theorem integral_mul_two_mode_expand {u₀ u₁ v₀ v₁ : ℝ → ℝ} {α β : ℝ}
    (h00 : Integrable (fun x => u₀ x * v₀ x) μ)
    (h01 : Integrable (fun x => u₀ x * v₁ x) μ)
    (h10 : Integrable (fun x => u₁ x * v₀ x) μ)
    (h11 : Integrable (fun x => u₁ x * v₁ x) μ) :
    ∫ x, (α * u₀ x + β * u₁ x) * (α * v₀ x + β * v₁ x) ∂μ
      = α ^ (2 : ℕ) * (∫ x, u₀ x * v₀ x ∂μ) + α * β * (∫ x, u₀ x * v₁ x ∂μ)
        + α * β * (∫ x, u₁ x * v₀ x ∂μ) + β ^ (2 : ℕ) * ∫ x, u₁ x * v₁ x ∂μ := by
  have hA := h00.const_mul (α ^ (2 : ℕ))
  have hB := h01.const_mul (α * β)
  have hC := h10.const_mul (α * β)
  have hD := h11.const_mul (β ^ (2 : ℕ))
  calc ∫ x, (α * u₀ x + β * u₁ x) * (α * v₀ x + β * v₁ x) ∂μ
      = ∫ x, ((α ^ (2 : ℕ) * (u₀ x * v₀ x) + α * β * (u₀ x * v₁ x)) + α * β * (u₁ x * v₀ x))
            + β ^ (2 : ℕ) * (u₁ x * v₁ x) ∂μ := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        ring
    _ = (∫ x, ((α ^ (2 : ℕ) * (u₀ x * v₀ x) + α * β * (u₀ x * v₁ x)) + α * β * (u₁ x * v₀ x)) ∂μ)
          + ∫ x, β ^ (2 : ℕ) * (u₁ x * v₁ x) ∂μ := integral_add ((hA.add hB).add hC) hD
    _ = ((∫ x, (α ^ (2 : ℕ) * (u₀ x * v₀ x) + α * β * (u₀ x * v₁ x)) ∂μ)
          + ∫ x, α * β * (u₁ x * v₀ x) ∂μ) + ∫ x, β ^ (2 : ℕ) * (u₁ x * v₁ x) ∂μ := by
        congr 1
        exact integral_add (hA.add hB) hC
    _ = (((∫ x, α ^ (2 : ℕ) * (u₀ x * v₀ x) ∂μ) + ∫ x, α * β * (u₀ x * v₁ x) ∂μ)
          + ∫ x, α * β * (u₁ x * v₀ x) ∂μ) + ∫ x, β ^ (2 : ℕ) * (u₁ x * v₁ x) ∂μ := by
        congr 2
        exact integral_add hA hB
    _ = α ^ (2 : ℕ) * (∫ x, u₀ x * v₀ x ∂μ) + α * β * (∫ x, u₀ x * v₁ x ∂μ)
          + α * β * (∫ x, u₁ x * v₀ x ∂μ) + β ^ (2 : ℕ) * ∫ x, u₁ x * v₁ x ∂μ := by
        rw [integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul]

/-- **Off-diagonal vanishing for a two-mode combination.**  If the dominant-dominant block already
vanishes and the subordinate coefficient tends to zero, the whole pairing vanishes: the three
remaining blocks stay bounded by Cauchy--Schwarz and are killed by their coefficients. -/
theorem tendsto_integral_mul_two_mode {u₀ u₁ v₀ v₁ : ι → ℝ → ℝ} {α β : ι → ℝ} {M β₀ : ℝ}
    (hu₀ : SqBoundedFamily μ l M u₀) (hu₁ : SqBoundedFamily μ l M u₁)
    (hv₀ : SqBoundedFamily μ l M v₀) (hv₁ : SqBoundedFamily μ l M v₁)
    (hcross : Tendsto (fun i => ∫ x, u₁ i x * v₁ i x ∂μ) l (𝓝 0))
    (hα : Tendsto α l (𝓝 0)) (hβ : Tendsto β l (𝓝 β₀)) :
    Tendsto (fun i => ∫ x, (α i * u₀ i x + β i * u₁ i x) * (α i * v₀ i x + β i * v₁ i x) ∂μ)
      l (𝓝 0) := by
  have hαsq : Tendsto (fun i => α i ^ (2 : ℕ)) l (𝓝 0) := by
    have := hα.pow 2
    simpa using this
  have hαβ : Tendsto (fun i => α i * β i) l (𝓝 0) := by
    have := hα.mul hβ
    simpa using this
  have hT1 := tendsto_mul_integral_mul_of_tendsto_zero hu₀ hv₀ hαsq
  have hT2 := tendsto_mul_integral_mul_of_tendsto_zero hu₀ hv₁ hαβ
  have hT3 := tendsto_mul_integral_mul_of_tendsto_zero hu₁ hv₀ hαβ
  have hT4 : Tendsto (fun i => β i ^ (2 : ℕ) * ∫ x, u₁ i x * v₁ i x ∂μ) l (𝓝 0) := by
    have := (hβ.pow 2).mul hcross
    simpa using this
  have hsum := ((hT1.add hT2).add hT3).add hT4
  rw [show (0 : ℝ) + 0 + 0 + 0 = 0 from by norm_num] at hsum
  refine hsum.congr' ?_
  filter_upwards [hu₀, hu₁, hv₀, hv₁] with i ⟨hu₀m, hu₀2, _⟩ ⟨hu₁m, hu₁2, _⟩
    ⟨hv₀m, hv₀2, _⟩ ⟨hv₁m, hv₁2, _⟩
  exact (integral_mul_two_mode_expand
    (integrable_mul_of_sq_integrable hu₀m hv₀m hu₀2 hv₀2)
    (integrable_mul_of_sq_integrable hu₀m hv₁m hu₀2 hv₁2)
    (integrable_mul_of_sq_integrable hu₁m hv₀m hu₁2 hv₀2)
    (integrable_mul_of_sq_integrable hu₁m hv₁m hu₁2 hv₁2)).symm

end GaloisForLFunctions.HTGeometry
