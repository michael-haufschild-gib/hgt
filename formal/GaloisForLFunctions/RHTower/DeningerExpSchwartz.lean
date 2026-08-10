import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv

/-!
# The exponentially decreasing Schwartz source

Meyer's cochain space `H_- = S_exp(ℝ)` consists of the smooth functions all of whose derivatives
decay faster than every exponential.  Under `x ↦ log x` these are exactly the functions on the
positive ray that are rapidly decreasing at both ends, which is why they are the natural source of
the Möbius and Poisson calculus.

Every such function is Schwartz, because `|x|^k ≤ k! e^{|x|}`, so the space is a *subspace* of the
Schwartz space and inherits its linear structure.  Translation acts on it: the exponential weight
changes by the fixed factor `e^{|A||L|}`.  The prime periodization defect `Δ_L = 1 - τ_L` is
therefore an endomorphism of the source.

* `deningerExpShift` : translation of a Schwartz function.
* `DeningerExpSchwartz` : **the exponentially decreasing Schwartz source**, as a subspace.
* `deningerExpShift_mem` : translation preserves it.
* `deningerPeriodizationDefect` : `Δ_L = 1 - τ_L` on the source.
-/

namespace RHTower

open SchwartzMap

noncomputable section

/-! ## Translation of Schwartz functions -/

private theorem deningerNorm_le_two_mul_max (L x : ℝ) :
    ‖x‖ ≤ 2 * max ‖x + L‖ |L| := by
  have hsplit : ‖x‖ ≤ ‖x + L‖ + |L| := by
    have h := norm_sub_le (x + L) L
    have hx : (x + L) - L = x := by ring
    rw [hx] at h
    simpa [Real.norm_eq_abs] using h
  have h1 : ‖x + L‖ ≤ max ‖x + L‖ |L| := le_max_left _ _
  have h2 : |L| ≤ max ‖x + L‖ |L| := le_max_right _ _
  linarith

private theorem deningerPow_shift_le (L x : ℝ) (k : ℕ) :
    ‖x‖ ^ k ≤ 2 ^ k * (‖x + L‖ ^ k + |L| ^ k) := by
  have hmaxnn : (0 : ℝ) ≤ max ‖x + L‖ |L| := le_trans (norm_nonneg _) (le_max_left _ _)
  have hstep : ‖x‖ ^ k ≤ (2 * max ‖x + L‖ |L|) ^ k :=
    pow_le_pow_left₀ (norm_nonneg _) (deningerNorm_le_two_mul_max L x) k
  have hmax : (max ‖x + L‖ |L|) ^ k ≤ ‖x + L‖ ^ k + |L| ^ k := by
    rcases max_cases ‖x + L‖ |L| with ⟨heq, _⟩ | ⟨heq, _⟩
    · rw [heq]
      have : (0 : ℝ) ≤ |L| ^ k := pow_nonneg (abs_nonneg _) k
      linarith
    · rw [heq]
      have : (0 : ℝ) ≤ ‖x + L‖ ^ k := pow_nonneg (norm_nonneg _) k
      linarith
  calc ‖x‖ ^ k ≤ (2 * max ‖x + L‖ |L|) ^ k := hstep
    _ = 2 ^ k * (max ‖x + L‖ |L|) ^ k := by rw [mul_pow]
    _ ≤ 2 ^ k * (‖x + L‖ ^ k + |L| ^ k) :=
        mul_le_mul_of_nonneg_left hmax (by positivity)

/-- **Translation of a Schwartz function.** -/
def deningerExpShift (L : ℝ) (f : 𝓢(ℝ, ℂ)) : 𝓢(ℝ, ℂ) where
  toFun x := f (x + L)
  smooth' := (f.smooth' ).comp (contDiff_id.add contDiff_const)
  decay' k n := by
    obtain ⟨C1, hC1⟩ := f.decay' k n
    obtain ⟨C0, hC0⟩ := f.decay' 0 n
    refine ⟨2 ^ k * (C1 + |L| ^ k * C0), fun x => ?_⟩
    have hderiv : iteratedFDeriv ℝ n (fun x : ℝ => f (x + L)) x
        = iteratedFDeriv ℝ n (f : ℝ → ℂ) (x + L) :=
      iteratedFDeriv_comp_add_right n L x
    rw [hderiv]
    have hnn : (0 : ℝ) ≤ ‖iteratedFDeriv ℝ n (f : ℝ → ℂ) (x + L)‖ := norm_nonneg _
    have hstep : ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (f : ℝ → ℂ) (x + L)‖
        ≤ (2 ^ k * (‖x + L‖ ^ k + |L| ^ k)) *
          ‖iteratedFDeriv ℝ n (f : ℝ → ℂ) (x + L)‖ :=
      mul_le_mul_of_nonneg_right (deningerPow_shift_le L x k) hnn
    have h1 : ‖x + L‖ ^ k * ‖iteratedFDeriv ℝ n (f : ℝ → ℂ) (x + L)‖ ≤ C1 := hC1 (x + L)
    have h0 : ‖iteratedFDeriv ℝ n (f : ℝ → ℂ) (x + L)‖ ≤ C0 := by
      have h := hC0 (x + L)
      rwa [pow_zero, one_mul] at h
    have hLk : (0 : ℝ) ≤ |L| ^ k := pow_nonneg (abs_nonneg _) k
    have hexpand : (2 ^ k * (‖x + L‖ ^ k + |L| ^ k)) *
          ‖iteratedFDeriv ℝ n (f : ℝ → ℂ) (x + L)‖
        = 2 ^ k * (‖x + L‖ ^ k * ‖iteratedFDeriv ℝ n (f : ℝ → ℂ) (x + L)‖
            + |L| ^ k * ‖iteratedFDeriv ℝ n (f : ℝ → ℂ) (x + L)‖) := by ring
    refine le_trans hstep (le_trans (le_of_eq hexpand) ?_)
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have h2 : |L| ^ k * ‖iteratedFDeriv ℝ n (f : ℝ → ℂ) (x + L)‖ ≤ |L| ^ k * C0 :=
      mul_le_mul_of_nonneg_left h0 hLk
    linarith

@[simp]
theorem deningerExpShift_apply (L : ℝ) (f : 𝓢(ℝ, ℂ)) (x : ℝ) :
    deningerExpShift L f x = f (x + L) := rfl

theorem deningerExpShift_zero (f : 𝓢(ℝ, ℂ)) : deningerExpShift 0 f = f := by
  ext x
  rw [deningerExpShift_apply, add_zero]

/-! ## The exponentially decreasing source -/

/-- **The exponentially decreasing Schwartz source** `H_- = S_exp(ℝ)`: the Schwartz functions all
of whose derivatives decay faster than every exponential. -/
def DeningerExpSchwartz : Submodule ℂ (𝓢(ℝ, ℂ)) where
  carrier := {f | ∀ (A : ℝ) (n : ℕ), ∃ C : ℝ, ∀ x : ℝ,
    Real.exp (A * |x|) * ‖iteratedFDeriv ℝ n (f : ℝ → ℂ) x‖ ≤ C}
  add_mem' := by
    intro f g hf hg A n
    obtain ⟨Cf, hCf⟩ := hf A n
    obtain ⟨Cg, hCg⟩ := hg A n
    refine ⟨Cf + Cg, fun x => ?_⟩
    have hcoe : ((f + g : 𝓢(ℝ, ℂ)) : ℝ → ℂ) = (f : ℝ → ℂ) + (g : ℝ → ℂ) := rfl
    rw [hcoe, iteratedFDeriv_add_apply ((f.smooth n).contDiffAt) ((g.smooth n).contDiffAt)]
    have hnorm : ‖iteratedFDeriv ℝ n (f : ℝ → ℂ) x + iteratedFDeriv ℝ n (g : ℝ → ℂ) x‖
        ≤ ‖iteratedFDeriv ℝ n (f : ℝ → ℂ) x‖ + ‖iteratedFDeriv ℝ n (g : ℝ → ℂ) x‖ :=
      norm_add_le _ _
    have hexp : (0 : ℝ) ≤ Real.exp (A * |x|) := (Real.exp_pos _).le
    have := mul_le_mul_of_nonneg_left hnorm hexp
    have hf' := hCf x
    have hg' := hCg x
    nlinarith [Real.exp_pos (A * |x|)]
  zero_mem' := by
    intro A n
    refine ⟨0, fun x => ?_⟩
    have hcoe : ((0 : 𝓢(ℝ, ℂ)) : ℝ → ℂ) = fun _ => 0 := rfl
    rw [hcoe, iteratedFDeriv_fun_zero]
    simp
  smul_mem' := by
    intro c f hf A n
    obtain ⟨C, hC⟩ := hf A n
    refine ⟨‖c‖ * C, fun x => ?_⟩
    have hcoe : ((c • f : 𝓢(ℝ, ℂ)) : ℝ → ℂ) = c • (f : ℝ → ℂ) := rfl
    rw [hcoe, iteratedFDeriv_const_smul_apply ((f.smooth n).contDiffAt), norm_smul]
    have hstep : Real.exp (A * |x|) * (‖c‖ * ‖iteratedFDeriv ℝ n (f : ℝ → ℂ) x‖)
        = ‖c‖ * (Real.exp (A * |x|) * ‖iteratedFDeriv ℝ n (f : ℝ → ℂ) x‖) := by ring
    rw [hstep]
    exact mul_le_mul_of_nonneg_left (hC x) (norm_nonneg c)

theorem deningerExpSchwartz_mem_iff (f : 𝓢(ℝ, ℂ)) :
    f ∈ DeningerExpSchwartz ↔ ∀ (A : ℝ) (n : ℕ), ∃ C : ℝ, ∀ x : ℝ,
      Real.exp (A * |x|) * ‖iteratedFDeriv ℝ n (f : ℝ → ℂ) x‖ ≤ C := Iff.rfl

/-! ## Translation acts on the source -/

private theorem deningerExpWeight_shift (A L x : ℝ) :
    A * |x| ≤ A * |x + L| + |A| * |L| := by
  rcases le_or_gt 0 A with hA | hA
  · have h : |x| ≤ |x + L| + |L| := by
      have := abs_sub_abs_le_abs_sub x (x + L)
      have habs : |x - (x + L)| = |L| := by
        rw [show x - (x + L) = -L by ring, abs_neg]
      rw [habs] at this
      linarith
    have := mul_le_mul_of_nonneg_left h hA
    rw [abs_of_nonneg hA]
    nlinarith [abs_nonneg L]
  · have h : |x + L| ≤ |x| + |L| := by
      have hh := norm_add_le x L
      simpa [Real.norm_eq_abs] using hh
    have hAneg : A < 0 := hA
    rw [abs_of_neg hAneg]
    nlinarith [abs_nonneg L, abs_nonneg x, abs_nonneg (x + L)]

/-- **Translation preserves the exponentially decreasing source.** -/
theorem deningerExpShift_mem {f : 𝓢(ℝ, ℂ)} (hf : f ∈ DeningerExpSchwartz) (L : ℝ) :
    deningerExpShift L f ∈ DeningerExpSchwartz := by
  intro A n
  obtain ⟨C, hC⟩ := hf A n
  refine ⟨Real.exp (|A| * |L|) * max C 0, fun x => ?_⟩
  have hderiv : iteratedFDeriv ℝ n ((deningerExpShift L f : 𝓢(ℝ, ℂ)) : ℝ → ℂ) x
      = iteratedFDeriv ℝ n (f : ℝ → ℂ) (x + L) :=
    iteratedFDeriv_comp_add_right n L x
  rw [hderiv]
  have hexp : Real.exp (A * |x|) ≤ Real.exp (|A| * |L|) * Real.exp (A * |x + L|) := by
    rw [← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    have := deningerExpWeight_shift A L x
    linarith
  have hnn : (0 : ℝ) ≤ ‖iteratedFDeriv ℝ n (f : ℝ → ℂ) (x + L)‖ := norm_nonneg _
  have hstep : Real.exp (A * |x|) * ‖iteratedFDeriv ℝ n (f : ℝ → ℂ) (x + L)‖
      ≤ (Real.exp (|A| * |L|) * Real.exp (A * |x + L|)) *
        ‖iteratedFDeriv ℝ n (f : ℝ → ℂ) (x + L)‖ :=
    mul_le_mul_of_nonneg_right hexp hnn
  refine le_trans hstep ?_
  have hC' := hC (x + L)
  have hCmax : Real.exp (A * |x + L|) * ‖iteratedFDeriv ℝ n (f : ℝ → ℂ) (x + L)‖
      ≤ max C 0 := le_trans hC' (le_max_left _ _)
  have hassoc : (Real.exp (|A| * |L|) * Real.exp (A * |x + L|)) *
      ‖iteratedFDeriv ℝ n (f : ℝ → ℂ) (x + L)‖
      = Real.exp (|A| * |L|) *
        (Real.exp (A * |x + L|) * ‖iteratedFDeriv ℝ n (f : ℝ → ℂ) (x + L)‖) := by ring
  rw [hassoc]
  exact mul_le_mul_of_nonneg_left hCmax (Real.exp_pos _).le

/-! ## The prime periodization defect -/

/-- The translation, as an operator of the exponentially decreasing source. -/
def deningerExpShiftSource (L : ℝ) : DeningerExpSchwartz →ₗ[ℂ] DeningerExpSchwartz where
  toFun f := ⟨deningerExpShift L (f : 𝓢(ℝ, ℂ)), deningerExpShift_mem f.2 L⟩
  map_add' f g := by
    ext x
    rfl
  map_smul' c f := by
    ext x
    rfl

@[simp]
theorem deningerExpShiftSource_apply (L : ℝ) (f : DeningerExpSchwartz) (x : ℝ) :
    ((deningerExpShiftSource L f : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) x
      = ((f : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) (x + L) := rfl

/-- **The periodization defect** `Δ_L = 1 - τ_L` of the exponentially decreasing source. -/
def deningerPeriodizationDefect (L : ℝ) : DeningerExpSchwartz →ₗ[ℂ] DeningerExpSchwartz :=
  LinearMap.id - deningerExpShiftSource L

theorem deningerPeriodizationDefect_apply (L : ℝ) (f : DeningerExpSchwartz) (x : ℝ) :
    ((deningerPeriodizationDefect L f : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) x
      = ((f : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) x
        - ((f : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) (x + L) := rfl

/-- The defect at zero translation is zero: a period-zero defect kills everything. -/
theorem deningerPeriodizationDefect_zero (f : DeningerExpSchwartz) :
    deningerPeriodizationDefect 0 f = 0 := by
  ext x
  rw [deningerPeriodizationDefect_apply, add_zero]
  simp

end

end RHTower
