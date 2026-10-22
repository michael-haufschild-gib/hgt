import GaloisForLFunctions.RHTower.Deninger.DeningerPeriodizationSplit
import GaloisForLFunctions.RHTower.Deninger.DeningerMeyerOscillator
import GaloisForLFunctions.RHTower.Deninger.DeningerEulerDepletedKernel
import GaloisForLFunctions.RHTower.Deninger.DeningerGreenSumSource

/-!
# The twisted Floquet periodization sequence

The trivialization `U_α F(t) = e^{αt}F(t)` carries the `α`-twisted objects to the untwisted ones:
it takes the twisted defect `D_{α,L} = 1 - e^{αL}τ_L` to the ordinary defect `Δ_L`, the twisted
periodization `Per_{α,L}` to the ordinary periodization, and the Floquet line
`F(t+L) = e^{-αL}F(t)` to `C^∞(ℝ/Lℤ)`.  Since `U_α` is an automorphism of the source, the whole
twisted sequence is the untwisted one conjugated, and inherits injectivity, the kernel identity and
surjectivity.

* `deningerFloquetPeriodizationSum` : `Per_{α,L}h(t) = ∑_j e^{αjL}h(t+jL)`.
* `deningerFloquetPeriodizationSum_trivialize` : **`e^{αt}Per_{α,L}h(t) = Per_L(U_α h)(t)`.**
* `DeningerFloquetLine` : the smooth quasi-periodic line.
* `deningerFloquetDefect_injective` : **`D_{α,L}` is injective.**
* `deningerFloquetPeriodization_range_eq_kernel` : **`ker Per_{α,L} = D_{α,L}H_-`.**
* `deningerFloquetPeriodizationMap_surjective` : **`Per_{α,L}` is onto the Floquet line.**
-/

namespace RHTower

open SchwartzMap

noncomputable section

/-! ## The twisted periodization and its trivialization -/

/-- The `α`-twisted periodization `Per_{α,L}h(t) = ∑_j e^{αjL}h(t+jL)`. -/
def deningerFloquetPeriodizationSum (f : 𝓢(ℝ, ℂ)) (α L t : ℝ) : ℂ :=
  ∑' j : ℤ, ((Real.exp (α * ((j : ℝ) * L)) : ℝ) : ℂ) * (f : ℝ → ℂ) (t + (j : ℝ) * L)

/-- **The trivialization takes the twisted periodization to the ordinary one.** -/
theorem deningerFloquetPeriodizationSum_trivialize (h : DeningerExpSchwartz) (α L t : ℝ) :
    ((Real.exp (α * t) : ℝ) : ℂ)
        * deningerFloquetPeriodizationSum ((h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) α L t
      = deningerPeriodizationSum
        ((deningerExpMulLM α h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) L t := by
  rw [deningerFloquetPeriodizationSum, deningerPeriodizationSum, ← tsum_mul_left]
  refine tsum_congr fun j => ?_
  rw [deningerExpMulLM_apply, ← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add]
  congr 2
  ring

/-! ## The twisted defect -/

/-- The `α`-twisted Euler defect `D_{α,L} = 1 - e^{αL}τ_L`. -/
def deningerFloquetDefect (α L : ℝ) : DeningerExpSchwartz →ₗ[ℂ] DeningerExpSchwartz :=
  LinearMap.id - ((Real.exp (α * L) : ℝ) : ℂ) • deningerExpShiftSource L

@[simp]
theorem deningerFloquetDefect_apply (α L : ℝ) (h : DeningerExpSchwartz) (t : ℝ) :
    ((deningerFloquetDefect α L h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) t
      = ((h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) t
        - ((Real.exp (α * L) : ℝ) : ℂ) * ((h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) (t + L) := by
  show ((h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) t
      - ((Real.exp (α * L) : ℝ) : ℂ)
        * ((deningerExpShiftSource L h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) t = _
  rw [deningerExpShiftSource_apply]

/-- **The trivialization takes the twisted defect to the ordinary one.** -/
theorem deningerExpMulLM_floquetDefect (α L : ℝ) (h : DeningerExpSchwartz) :
    deningerExpMulLM α (deningerFloquetDefect α L h)
      = deningerPeriodizationDefect L (deningerExpMulLM α h) := by
  refine Subtype.ext (SchwartzMap.ext fun t => ?_)
  rw [deningerExpMulLM_apply, deningerFloquetDefect_apply, deningerPeriodizationDefect_apply,
    deningerExpMulLM_apply, deningerExpMulLM_apply]
  have hk : ((Real.exp (α * t) : ℝ) : ℂ) * ((Real.exp (α * L) : ℝ) : ℂ)
      = ((Real.exp (α * (t + L)) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, ← Real.exp_add]
    congr 2
    ring
  linear_combination (-(((h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) (t + L))) * hk

/-- **The twisted defect is injective.** -/
theorem deningerFloquetDefect_injective {L : ℝ} (hL : 0 < L) (α : ℝ) :
    Function.Injective (deningerFloquetDefect α L) := by
  intro a b hab
  have hstep : deningerPeriodizationDefect L (deningerExpMulLM α a)
      = deningerPeriodizationDefect L (deningerExpMulLM α b) := by
    rw [← deningerExpMulLM_floquetDefect, ← deningerExpMulLM_floquetDefect, hab]
  have hinj := deningerPeriodizationDefect_injective hL hstep
  have hcancel : ∀ u v : DeningerExpSchwartz,
      deningerExpMulLM α u = deningerExpMulLM α v → u = v := by
    intro u v huv
    refine Subtype.ext (SchwartzMap.ext fun t => ?_)
    have hval := congrArg (fun w : DeningerExpSchwartz =>
      ((w : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) t) huv
    rw [deningerExpMulLM_apply, deningerExpMulLM_apply] at hval
    exact mul_left_cancel₀ (Complex.ofReal_ne_zero.2 (Real.exp_ne_zero _)) hval
  exact hcancel a b hinj

/-- **`ker Per_{α,L} = D_{α,L}H_-`.** -/
theorem deningerFloquetPeriodization_range_eq_kernel {L : ℝ} (hL : 0 < L) (α : ℝ) :
    Set.range (deningerFloquetDefect α L)
      = {h : DeningerExpSchwartz | ∀ t : ℝ,
          deningerFloquetPeriodizationSum ((h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) α L t = 0} := by
  have hvanish : ∀ h : DeningerExpSchwartz,
      (∀ t : ℝ, deningerFloquetPeriodizationSum ((h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) α L t = 0)
        ↔ ∀ t : ℝ, deningerPeriodizationSum
          ((deningerExpMulLM α h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) L t = 0 := by
    intro h
    constructor
    · intro hall t
      rw [← deningerFloquetPeriodizationSum_trivialize, hall t, mul_zero]
    · intro hall t
      have hkey := deningerFloquetPeriodizationSum_trivialize h α L t
      rw [hall t] at hkey
      exact (mul_eq_zero.1 hkey).resolve_left (Complex.ofReal_ne_zero.2 (Real.exp_ne_zero _))
  have hcancel : ∀ u v : DeningerExpSchwartz,
      deningerExpMulLM α u = deningerExpMulLM α v → u = v := by
    intro u v huv
    refine Subtype.ext (SchwartzMap.ext fun t => ?_)
    have hval := congrArg (fun w : DeningerExpSchwartz =>
      ((w : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) t) huv
    rw [deningerExpMulLM_apply, deningerExpMulLM_apply] at hval
    exact mul_left_cancel₀ (Complex.ofReal_ne_zero.2 (Real.exp_ne_zero _)) hval
  ext h
  simp only [Set.mem_range, Set.mem_setOf_eq]
  rw [hvanish h]
  constructor
  · rintro ⟨g, rfl⟩
    have hmem : deningerPeriodizationDefect L (deningerExpMulLM α g)
        ∈ Set.range (deningerPeriodizationDefect L) := ⟨_, rfl⟩
    rw [deningerPeriodization_range_eq_kernel hL] at hmem
    intro t
    rw [deningerExpMulLM_floquetDefect]
    exact hmem t
  · intro hzero
    have hmem : deningerExpMulLM α h ∈ Set.range (deningerPeriodizationDefect L) := by
      rw [deningerPeriodization_range_eq_kernel hL]
      exact hzero
    obtain ⟨g, hg⟩ := hmem
    obtain ⟨g₀, rfl⟩ := deningerExpMulLM_surjective α g
    exact ⟨g₀, hcancel _ _ ((deningerExpMulLM_floquetDefect α L g₀).trans hg)⟩

/-! ## The Floquet line -/

/-- The trivialization on plain functions. -/
def deningerExpMulFunLM (α : ℝ) : (ℝ → ℂ) →ₗ[ℂ] (ℝ → ℂ) where
  toFun F := fun t => ((Real.exp (α * t) : ℝ) : ℂ) * F t
  map_add' F G := by
    funext t
    simp only [Pi.add_apply]
    ring
  map_smul' c F := by
    funext t
    simp only [Pi.smul_apply, RingHom.id_apply, smul_eq_mul]
    ring

@[simp]
theorem deningerExpMulFunLM_apply (α : ℝ) (F : ℝ → ℂ) (t : ℝ) :
    deningerExpMulFunLM α F t = ((Real.exp (α * t) : ℝ) : ℂ) * F t := rfl

/-- **The smooth Floquet line** `F(t+L) = e^{-αL}F(t)`, defined as the trivialization preimage of
`C^∞(ℝ/Lℤ)`. -/
def DeningerFloquetLine (α L : ℝ) : Submodule ℂ (ℝ → ℂ) :=
  Submodule.comap (deningerExpMulFunLM α) (DeningerSmoothPeriodic L)

/-- **Membership in the Floquet line is smoothness plus quasi-periodicity.** -/
theorem mem_deningerFloquetLine_iff (α L : ℝ) (F : ℝ → ℂ) :
    F ∈ DeningerFloquetLine α L
      ↔ ContDiff ℝ (⊤ : ℕ∞) (deningerExpMulFunLM α F)
        ∧ ∀ t : ℝ, F (t + L) = ((Real.exp (-(α * L)) : ℝ) : ℂ) * F t := by
  have hk : ∀ t : ℝ, ((Real.exp (α * (t + L)) : ℝ) : ℂ) * ((Real.exp (-(α * L)) : ℝ) : ℂ)
      = ((Real.exp (α * t) : ℝ) : ℂ) := by
    intro t
    rw [← Complex.ofReal_mul, ← Real.exp_add]
    congr 2
    ring
  constructor
  · rintro ⟨hsmooth, hper⟩
    refine ⟨hsmooth, fun t => ?_⟩
    have h := hper t
    rw [deningerExpMulFunLM_apply, deningerExpMulFunLM_apply] at h
    have hne : ((Real.exp (α * (t + L)) : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.2 (Real.exp_ne_zero _)
    refine mul_left_cancel₀ hne ?_
    rw [h, ← mul_assoc, hk t]
  · rintro ⟨hsmooth, hquasi⟩
    refine ⟨hsmooth, fun t => ?_⟩
    rw [deningerExpMulFunLM_apply, deningerExpMulFunLM_apply, hquasi t, ← mul_assoc, hk t]

/-- The twisted periodization lands in the Floquet line. -/
theorem deningerFloquetPeriodizationSum_mem {L : ℝ} (hL : 0 < L) (α : ℝ)
    (h : DeningerExpSchwartz) :
    (fun t => deningerFloquetPeriodizationSum ((h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) α L t)
      ∈ DeningerFloquetLine α L := by
  have hfun : deningerExpMulFunLM α
      (fun t => deningerFloquetPeriodizationSum ((h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) α L t)
      = deningerPeriodizationSum
        ((deningerExpMulLM α h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) L := by
    funext t
    rw [deningerExpMulFunLM_apply]
    exact deningerFloquetPeriodizationSum_trivialize h α L t
  show deningerExpMulFunLM α _ ∈ DeningerSmoothPeriodic L
  rw [hfun]
  exact deningerPeriodizationMem (deningerExpMulLM α h).2 hL

/-- **`Per_{α,L}` is onto the Floquet line.** -/
theorem deningerFloquetPeriodizationMap_surjective {L : ℝ} (hL : 0 < L) (α : ℝ)
    (F : DeningerFloquetLine α L) :
    ∃ h : DeningerExpSchwartz, ∀ t : ℝ,
      deningerFloquetPeriodizationSum ((h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) α L t
        = (F : ℝ → ℂ) t := by
  have hmem : deningerExpMulFunLM α (F : ℝ → ℂ) ∈ DeningerSmoothPeriodic L := F.2
  obtain ⟨g, hg⟩ := deningerPeriodizationMap_surjective hL
    (⟨deningerExpMulFunLM α (F : ℝ → ℂ), hmem⟩ : DeningerSmoothPeriodic L)
  obtain ⟨h, rfl⟩ := deningerExpMulLM_surjective α g
  refine ⟨h, fun t => ?_⟩
  have hval := congrArg (fun u : DeningerSmoothPeriodic L => (u : ℝ → ℂ) t) hg
  simp only [deningerPeriodizationMap_apply] at hval
  have hkey := deningerFloquetPeriodizationSum_trivialize h α L t
  rw [hval] at hkey
  have hne : ((Real.exp (α * t) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (Real.exp_ne_zero _)
  refine mul_left_cancel₀ hne ?_
  rw [hkey]
  rfl

end

end RHTower
