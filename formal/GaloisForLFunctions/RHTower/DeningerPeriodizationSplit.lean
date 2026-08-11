import GaloisForLFunctions.RHTower.DeningerPartitionBump
import GaloisForLFunctions.RHTower.DeningerEulerDepletedKernel

/-!
# The periodization splits

Dividing the bump by its own periodization gives a compactly supported smooth `\chi` whose lattice
translates sum to `1`.  Multiplying a smooth periodic function by `\chi` therefore lifts it to a
compactly supported element of the source whose periodization is the original function, so the
periodization is surjective and split.

* `deningerPartitionUnity` : `\chi = \psi / \mathrm{Per}_L\psi`.
* `deningerPartitionUnity_tsum` : **`\sum_j \chi(t+jL) = 1`.**
* `deningerPeriodizationSplit` : **a linear section of `Per_L`.**
* `deningerPeriodizationMap_surjective` : **`Per_L` is surjective.**
-/

namespace RHTower

open SchwartzMap

noncomputable section

/-- The lattice partition of unity subordinate to the bump. -/
def deningerPartitionUnity (L : ℝ) (t : ℝ) : ℝ :=
  (deningerPartitionBump L : ℝ → ℝ) t * (deningerPartitionDenom L t)⁻¹

theorem deningerPartitionUnity_hasCompactSupport (L : ℝ) :
    HasCompactSupport (deningerPartitionUnity L) :=
  HasCompactSupport.mul_right (deningerPartitionBump_hasCompactSupport L)

theorem deningerPartitionUnity_contDiff {L : ℝ} (hL : 0 < L) :
    ContDiff ℝ (⊤ : ℕ∞) (deningerPartitionUnity L) := by
  refine (deningerPartitionBump L).contDiff.mul ?_
  exact (deningerPartitionDenom_contDiff hL).inv fun t =>
    ne_of_gt (deningerPartitionDenom_pos hL t)

/-- The denominator is invariant under every lattice translation. -/
theorem deningerPartitionDenom_int_shift {L : ℝ} (hL : 0 < L) (t : ℝ) (j : ℤ) :
    deningerPartitionDenom L (t + (j : ℝ) * L) = deningerPartitionDenom L t :=
  (Function.Periodic.int_mul (fun s => deningerPartitionDenom_periodic hL s) j) t

/-- **The lattice translates of `χ` sum to `1`.** -/
theorem deningerPartitionUnity_tsum {L : ℝ} (hL : 0 < L) (t : ℝ) :
    (∑' j : ℤ, deningerPartitionUnity L (t + (j : ℝ) * L)) = 1 := by
  have hterm : ∀ j : ℤ, deningerPartitionUnity L (t + (j : ℝ) * L)
      = (deningerPartitionBump L : ℝ → ℝ) (t + (j : ℝ) * L)
        * (deningerPartitionDenom L t)⁻¹ := by
    intro j
    rw [deningerPartitionUnity, deningerPartitionDenom_int_shift hL t j]
  rw [tsum_congr hterm, tsum_mul_right, ← deningerPartitionDenom]
  exact mul_inv_cancel₀ (ne_of_gt (deningerPartitionDenom_pos hL t))

/-- The compactly supported lift of a smooth periodic function. -/
def deningerSplitFun (L : ℝ) (F : DeningerSmoothPeriodic L) : ℝ → ℂ :=
  fun t => (deningerPartitionUnity L t : ℂ) * ((F : DeningerSmoothPeriodic L) : ℝ → ℂ) t

theorem deningerSplitFun_hasCompactSupport (L : ℝ) (F : DeningerSmoothPeriodic L) :
    HasCompactSupport (deningerSplitFun L F) := by
  refine HasCompactSupport.mul_right ?_
  exact (deningerPartitionUnity_hasCompactSupport L).comp_left
    (g := (Complex.ofRealCLM : ℝ →L[ℝ] ℂ)) (by simp)

theorem deningerSplitFun_contDiff {L : ℝ} (hL : 0 < L) (F : DeningerSmoothPeriodic L) :
    ContDiff ℝ (⊤ : ℕ∞) (deningerSplitFun L F) := by
  refine ContDiff.mul ?_ (deningerSmoothPeriodic_contDiff F)
  exact Complex.ofRealCLM.contDiff.comp (deningerPartitionUnity_contDiff hL)

/-- The lift, as an element of the source. -/
def deningerSplitSchwartz {L : ℝ} (hL : 0 < L) (F : DeningerSmoothPeriodic L) : 𝓢(ℝ, ℂ) :=
  HasCompactSupport.toSchwartzMap (deningerSplitFun_hasCompactSupport L F)
    (deningerSplitFun_contDiff hL F)

theorem deningerSplitSchwartz_apply {L : ℝ} (hL : 0 < L) (F : DeningerSmoothPeriodic L) (t : ℝ) :
    ((deningerSplitSchwartz hL F : 𝓢(ℝ, ℂ)) : ℝ → ℂ) t = deningerSplitFun L F t := rfl

theorem deningerSplitSchwartz_mem {L : ℝ} (hL : 0 < L) (F : DeningerSmoothPeriodic L) :
    deningerSplitSchwartz hL F ∈ DeningerExpSchwartz :=
  deningerExpSchwartz_of_hasCompactSupport (deningerSplitFun_hasCompactSupport L F)

/-- **The periodization of the lift is the original function.** -/
theorem deningerPeriodizationSum_splitSchwartz {L : ℝ} (hL : 0 < L)
    (F : DeningerSmoothPeriodic L) (t : ℝ) :
    deningerPeriodizationSum (deningerSplitSchwartz hL F) L t
      = ((F : DeningerSmoothPeriodic L) : ℝ → ℂ) t := by
  have hFper : ∀ j : ℤ, ((F : DeningerSmoothPeriodic L) : ℝ → ℂ) (t + (j : ℝ) * L)
      = ((F : DeningerSmoothPeriodic L) : ℝ → ℂ) t :=
    fun j => (Function.Periodic.int_mul (deningerSmoothPeriodic_periodic F) j) t
  have hterm : ∀ j : ℤ,
      ((deningerSplitSchwartz hL F : 𝓢(ℝ, ℂ)) : ℝ → ℂ) (t + (j : ℝ) * L)
        = (deningerPartitionUnity L (t + (j : ℝ) * L) : ℂ)
          * ((F : DeningerSmoothPeriodic L) : ℝ → ℂ) t := by
    intro j
    rw [deningerSplitSchwartz_apply, deningerSplitFun, hFper j]
  rw [deningerPeriodizationSum, tsum_congr hterm, tsum_mul_right]
  have hcast : (∑' j : ℤ, (deningerPartitionUnity L (t + (j : ℝ) * L) : ℂ))
      = ((∑' j : ℤ, deningerPartitionUnity L (t + (j : ℝ) * L) : ℝ) : ℂ) := by
    have hsum : Summable fun j : ℤ => deningerPartitionUnity L (t + (j : ℝ) * L) := by
      have hb := deningerPartitionDenom_summable hL t
      refine (hb.mul_right (deningerPartitionDenom L t)⁻¹).congr fun j => ?_
      rw [deningerPartitionUnity, deningerPartitionDenom_int_shift hL t j]
    rw [show ((∑' j : ℤ, deningerPartitionUnity L (t + (j : ℝ) * L) : ℝ) : ℂ)
        = Complex.ofRealCLM (∑' j : ℤ, deningerPartitionUnity L (t + (j : ℝ) * L)) from rfl,
      ContinuousLinearMap.map_tsum (Complex.ofRealCLM : ℝ →L[ℝ] ℂ) hsum]
    rfl
  rw [hcast, deningerPartitionUnity_tsum hL, Complex.ofReal_one, one_mul]

/-- **A linear section of the periodization.** -/
def deningerPeriodizationSplit {L : ℝ} (hL : 0 < L) :
    DeningerSmoothPeriodic L →ₗ[ℂ] DeningerExpSchwartz where
  toFun F := ⟨deningerSplitSchwartz hL F, deningerSplitSchwartz_mem hL F⟩
  map_add' F G := by
    refine Subtype.ext (SchwartzMap.ext fun t => ?_)
    show deningerSplitFun L (F + G) t = deningerSplitFun L F t + deningerSplitFun L G t
    rw [deningerSplitFun, deningerSplitFun, deningerSplitFun]
    show (deningerPartitionUnity L t : ℂ)
        * (((F : DeningerSmoothPeriodic L) : ℝ → ℂ) t
            + ((G : DeningerSmoothPeriodic L) : ℝ → ℂ) t) = _
    ring
  map_smul' c F := by
    refine Subtype.ext (SchwartzMap.ext fun t => ?_)
    show deningerSplitFun L (c • F) t = c * deningerSplitFun L F t
    rw [deningerSplitFun, deningerSplitFun]
    show (deningerPartitionUnity L t : ℂ)
        * (c * ((F : DeningerSmoothPeriodic L) : ℝ → ℂ) t) = _
    ring

/-- **The section is a right inverse of the periodization.** -/
theorem deningerPeriodizationMap_comp_split {L : ℝ} (hL : 0 < L) (F : DeningerSmoothPeriodic L) :
    deningerPeriodizationMap hL (deningerPeriodizationSplit hL F) = F := by
  refine Subtype.ext (funext fun t => ?_)
  exact deningerPeriodizationSum_splitSchwartz hL F t

/-- **The periodization is surjective onto `C^∞(ℝ/Lℤ)`.** -/
theorem deningerPeriodizationMap_surjective {L : ℝ} (hL : 0 < L) :
    Function.Surjective (deningerPeriodizationMap hL) :=
  fun F => ⟨deningerPeriodizationSplit hL F, deningerPeriodizationMap_comp_split hL F⟩

/-- **The periodization sequence is exact and split.**  `Δ_L` is injective with image the kernel of
`Per_L`, and `Per_L` is surjective with a linear section. -/
theorem deningerPeriodizationSequence_exact {L : ℝ} (hL : 0 < L) :
    Function.Injective (deningerPeriodizationDefect L)
      ∧ LinearMap.ker (deningerPeriodizationMap hL)
          = LinearMap.range (deningerPeriodizationDefect L)
      ∧ Function.Surjective (deningerPeriodizationMap hL) :=
  ⟨deningerPeriodizationDefect_injective hL, deningerPeriodizationMap_ker hL,
    deningerPeriodizationMap_surjective hL⟩

end

end RHTower
