import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic

/-!
# Jointly continuous products on complex Schwartz space

Mathlib packages pointwise bilinear pairing of Schwartz functions and proves continuity after
fixing either argument.  The spectral-form and Schwartz-kernel constructions need the stronger
joint continuity.  This file proves it directly from the defining Schwartz seminorms.
-/

open Filter Function Topology
open scoped Topology

namespace SchwartzMap

noncomputable section

/-- Pointwise multiplication of two complex Schwartz functions. -/
def pointwiseMul (f g : 𝓢(ℝ, ℂ)) : 𝓢(ℝ, ℂ) :=
  pairing (ContinuousLinearMap.mul ℂ ℂ) f g

@[simp] theorem pointwiseMul_apply (f g : 𝓢(ℝ, ℂ)) (x : ℝ) :
    pointwiseMul f g x = f x * g x := rfl

@[simp] theorem pointwiseMul_zero_left (g : 𝓢(ℝ, ℂ)) : pointwiseMul 0 g = 0 := by
  ext x
  simp

@[simp] theorem pointwiseMul_zero_right (f : 𝓢(ℝ, ℂ)) : pointwiseMul f 0 = 0 := by
  ext x
  simp

theorem pointwiseMul_add_left (f₁ f₂ g : 𝓢(ℝ, ℂ)) :
    pointwiseMul (f₁ + f₂) g = pointwiseMul f₁ g + pointwiseMul f₂ g := by
  ext x
  simp [pointwiseMul]

theorem pointwiseMul_add_right (f g₁ g₂ : 𝓢(ℝ, ℂ)) :
    pointwiseMul f (g₁ + g₂) = pointwiseMul f g₁ + pointwiseMul f g₂ := by
  ext x
  simp [pointwiseMul]

theorem pointwiseMul_smul_left (c : ℂ) (f g : 𝓢(ℝ, ℂ)) :
    pointwiseMul (c • f) g = c • pointwiseMul f g := by
  ext x
  simp [pointwiseMul]

theorem pointwiseMul_smul_right (c : ℂ) (f g : 𝓢(ℝ, ℂ)) :
    pointwiseMul f (c • g) = c • pointwiseMul f g := by
  ext x
  simp [pointwiseMul]

/-- A single finite supremum of seminorms controlling every derivative up to `n`, with spatial
weight up to `k`. -/
def productControl (k n : ℕ) : Seminorm ℂ 𝓢(ℝ, ℂ) :=
  (Finset.Iic (k, n)).sup (schwartzSeminormFamily ℂ ℝ ℂ)

theorem weighted_iteratedFDeriv_le_productControl
    (f : 𝓢(ℝ, ℂ)) {k n i : ℕ} (hi : i ≤ n) (x : ℝ) :
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ i f x‖ ≤
      2 ^ k * productControl k n f := by
  calc
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ i f x‖ ≤
        (1 + ‖x‖) ^ k * ‖iteratedFDeriv ℝ i f x‖ := by gcongr; simp
    _ ≤ 2 ^ k * productControl k n f := by
      rw [productControl, show schwartzSeminormFamily ℂ ℝ ℂ =
        (fun m => SchwartzMap.seminorm ℂ m.1 m.2) by rfl]
      exact one_add_le_sup_seminorm_apply (𝕜 := ℂ) (m := (k, n)) le_rfl hi f x

theorem iteratedFDeriv_le_productControl
    (f : 𝓢(ℝ, ℂ)) {k n i : ℕ} (hi : i ≤ n) (x : ℝ) :
    ‖iteratedFDeriv ℝ i f x‖ ≤ 2 ^ k * productControl k n f := by
  rw [productControl, show schwartzSeminormFamily ℂ ℝ ℂ =
    (fun m => SchwartzMap.seminorm ℂ m.1 m.2) by rfl]
  simpa only [pow_zero, one_mul] using
    (one_add_le_sup_seminorm_apply (𝕜 := ℂ) (m := (k, n)) (Nat.zero_le k) hi f x)

/-- Product estimate for every defining Schwartz seminorm. -/
theorem seminorm_pointwiseMul_le (f g : 𝓢(ℝ, ℂ)) (k n : ℕ) :
    SchwartzMap.seminorm ℂ k n (pointwiseMul f g) ≤
      ‖ContinuousLinearMap.mul ℂ ℂ‖ * (2 : ℝ) ^ (2 * k + n) *
        productControl k n f * productControl k n g := by
  apply seminorm_le_bound ℂ k n (pointwiseMul f g) (by positivity)
  intro x
  have hderiv :=
    (ContinuousLinearMap.mul ℂ ℂ).bilinearRestrictScalars ℝ
      |>.norm_iteratedFDeriv_le_of_bilinear
        (f.smooth ⊤) (g.smooth ⊤) x (n := n) (mod_cast le_top)
  rw [ContinuousLinearMap.norm_bilinearRestrictScalars] at hderiv
  change ‖iteratedFDeriv ℝ n (fun y => f y * g y) x‖ ≤ _ at hderiv
  change ‖x‖ ^ k * ‖iteratedFDeriv ℝ n
      (fun y => (ContinuousLinearMap.mul ℂ ℂ) (f y) (g y)) x‖ ≤ _
  change ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (fun y => f y * g y) x‖ ≤ _
  grw [hderiv]
  rw [mul_assoc, Finset.mul_sum, Finset.mul_sum]
  calc
    ∑ i ∈ Finset.range (n + 1),
        ‖x‖ ^ k * (‖ContinuousLinearMap.mul ℂ ℂ‖ *
          ((n.choose i : ℝ) * ‖iteratedFDeriv ℝ i f x‖ *
            ‖iteratedFDeriv ℝ (n - i) g x‖)) ≤
        ∑ i ∈ Finset.range (n + 1),
          ‖ContinuousLinearMap.mul ℂ ℂ‖ * (n.choose i : ℝ) *
            (2 : ℝ) ^ (2 * k) * productControl k n f * productControl k n g := by
      apply Finset.sum_le_sum
      intro i hi
      have hin : i ≤ n := Finset.mem_range_succ_iff.mp hi
      have hni : n - i ≤ n := Nat.sub_le n i
      have hfbound :=
        weighted_iteratedFDeriv_le_productControl f (k := k) (n := n) hin x
      have hgbound :=
        iteratedFDeriv_le_productControl g (k := k) (n := n) hni x
      calc
        ‖x‖ ^ k * (‖ContinuousLinearMap.mul ℂ ℂ‖ *
            ((n.choose i : ℝ) * ‖iteratedFDeriv ℝ i f x‖ *
              ‖iteratedFDeriv ℝ (n - i) g x‖)) =
            ‖ContinuousLinearMap.mul ℂ ℂ‖ * (n.choose i : ℝ) *
              (‖x‖ ^ k * ‖iteratedFDeriv ℝ i f x‖) *
              ‖iteratedFDeriv ℝ (n - i) g x‖ := by ring
        _ ≤ ‖ContinuousLinearMap.mul ℂ ℂ‖ * (n.choose i : ℝ) *
            ((2 : ℝ) ^ k * productControl k n f) *
            ((2 : ℝ) ^ k * productControl k n g) := by
          gcongr
        _ = ‖ContinuousLinearMap.mul ℂ ℂ‖ * (n.choose i : ℝ) *
            (2 : ℝ) ^ (2 * k) * productControl k n f * productControl k n g := by
          rw [show (2 : ℝ) ^ (2 * k) = 2 ^ k * 2 ^ k by rw [two_mul, pow_add]]
          ring
    _ = ‖ContinuousLinearMap.mul ℂ ℂ‖ * (2 : ℝ) ^ (2 * k + n) *
        (productControl k n f * productControl k n g) := by
      calc
        ∑ i ∈ Finset.range (n + 1),
            ‖ContinuousLinearMap.mul ℂ ℂ‖ * (n.choose i : ℝ) *
              (2 : ℝ) ^ (2 * k) * productControl k n f * productControl k n g =
            ∑ i ∈ Finset.range (n + 1),
              (‖ContinuousLinearMap.mul ℂ ℂ‖ * (2 : ℝ) ^ (2 * k) *
                productControl k n f * productControl k n g) * (n.choose i : ℝ) := by
          apply Finset.sum_congr rfl
          intro i hi
          ring
        _ = (‖ContinuousLinearMap.mul ℂ ℂ‖ * (2 : ℝ) ^ (2 * k) *
              productControl k n f * productControl k n g) *
              ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) := by
          rw [Finset.mul_sum]
        _ = _ := by
          rw [show (∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ)) = (2 : ℝ) ^ n by
            exact_mod_cast Nat.sum_range_choose n, pow_add]
          ring

/-- Pointwise multiplication as an additive homomorphism in each argument. -/
def pointwiseMulAddHom : 𝓢(ℝ, ℂ) →+ 𝓢(ℝ, ℂ) →+ 𝓢(ℝ, ℂ) where
  toFun f :=
    { toFun := pointwiseMul f
      map_zero' := pointwiseMul_zero_right f
      map_add' := pointwiseMul_add_right f }
  map_zero' := by
    ext g x
    simp
  map_add' f₁ f₂ := by
    ext g x
    simp [pointwiseMul_add_left]

@[simp] theorem pointwiseMulAddHom_apply (f g : 𝓢(ℝ, ℂ)) :
    pointwiseMulAddHom f g = pointwiseMul f g := rfl

/-- Pointwise multiplication is jointly continuous in the Schwartz topology. -/
theorem continuous_pointwiseMul :
    Continuous (fun p : 𝓢(ℝ, ℂ) × 𝓢(ℝ, ℂ) => pointwiseMul p.1 p.2) := by
  apply continuous_of_continuousAt_zero₂ pointwiseMulAddHom
  · rw [ContinuousAt]
    rw [(schwartz_withSeminorms ℂ ℝ ℂ).tendsto_nhds]
    rintro ⟨k, n⟩ ε hε
    let C : ℝ := ‖ContinuousLinearMap.mul ℂ ℂ‖ * (2 : ℝ) ^ (2 * k + n)
    let A : ℝ := C + 1
    have hC : 0 ≤ C := by dsimp [C]; positivity
    have hA : 0 < A := by dsimp [A]; linarith
    let δ : ℝ := Real.sqrt (ε / A)
    have hδ : 0 < δ := Real.sqrt_pos.2 (div_pos hε hA)
    have hfst : Tendsto (fun p : 𝓢(ℝ, ℂ) × 𝓢(ℝ, ℂ) => p.1)
        (𝓝 (0, 0)) (𝓝 0) := continuous_fst.continuousAt
    have hsnd : Tendsto (fun p : 𝓢(ℝ, ℂ) × 𝓢(ℝ, ℂ) => p.2)
        (𝓝 (0, 0)) (𝓝 0) := continuous_snd.continuousAt
    have hfst' := (schwartz_withSeminorms ℂ ℝ ℂ).tendsto_nhds'
      (fun p : 𝓢(ℝ, ℂ) × 𝓢(ℝ, ℂ) => p.1) (0 : 𝓢(ℝ, ℂ)) |>.1 hfst
    have hsnd' := (schwartz_withSeminorms ℂ ℝ ℂ).tendsto_nhds'
      (fun p : 𝓢(ℝ, ℂ) × 𝓢(ℝ, ℂ) => p.2) (0 : 𝓢(ℝ, ℂ)) |>.1 hsnd
    have hfsmall := hfst' (Finset.Iic (k, n)) δ hδ
    have hgsmall := hsnd' (Finset.Iic (k, n)) δ hδ
    filter_upwards [hfsmall, hgsmall] with p hp hq
    simp only [sub_zero] at hp hq
    simp only [pointwiseMulAddHom_apply, pointwiseMul_zero_left, sub_zero,
      schwartzSeminormFamily_apply] at ⊢
    change productControl k n p.1 < δ at hp
    change productControl k n p.2 < δ at hq
    change SchwartzMap.seminorm ℂ k n (pointwiseMul p.1 p.2) < ε
    have hbound := seminorm_pointwiseMul_le p.1 p.2 k n
    change SchwartzMap.seminorm ℂ k n (pointwiseMul p.1 p.2) ≤
      C * productControl k n p.1 * productControl k n p.2 at hbound
    have hp0 : 0 ≤ productControl k n p.1 := by positivity
    have hq0 : 0 ≤ productControl k n p.2 := by positivity
    have hδsq : δ ^ (2 : ℕ) = ε / A := by
      dsimp only [δ]
      exact Real.sq_sqrt (div_nonneg hε.le hA.le)
    calc
      SchwartzMap.seminorm ℂ k n (pointwiseMul p.1 p.2) ≤
          C * productControl k n p.1 * productControl k n p.2 := hbound
      _ ≤ A * productControl k n p.1 * productControl k n p.2 := by
        have hCA : C ≤ A := by dsimp only [A]; linarith
        gcongr
      _ < A * δ * δ := by
        have hpq : productControl k n p.1 * productControl k n p.2 < δ * δ := by
          calc
            productControl k n p.1 * productControl k n p.2 ≤
                productControl k n p.1 * δ :=
              mul_le_mul_of_nonneg_left hq.le hp0
            _ < δ * δ := mul_lt_mul_of_pos_right hp hδ
        nlinarith
      _ = ε := by
        rw [show A * δ * δ = A * δ ^ (2 : ℕ) by ring, hδsq]
        exact mul_div_cancel₀ ε hA.ne'
  · intro f
    simpa only [pointwiseMulAddHom_apply, pointwiseMul] using!
      (pairing (ContinuousLinearMap.mul ℂ ℂ) f).continuous.continuousAt
  · intro g
    simpa only [pointwiseMulAddHom_apply, pointwiseMul] using!
      (pairing_continuous_left (ContinuousLinearMap.mul ℂ ℂ) g).continuousAt

/-- Pointwise complex conjugation as a continuous conjugate-linear map of Schwartz space. -/
def conjSLM : 𝓢(ℝ, ℂ) →SL[starRingEnd ℂ] 𝓢(ℝ, ℂ) :=
  mkCLM (σ := starRingEnd ℂ) (fun f x => (starRingEnd ℂ) (f x))
    (fun _ _ _ => by simp) (fun _ _ _ => by simp)
    (fun f => Complex.conjCLE.contDiff.comp (f.smooth ⊤)) (by
      rintro ⟨k, n⟩
      refine ⟨{(k, n)}, 1, by norm_num, fun f x => ?_⟩
      rw [Finset.sup_singleton, schwartzSeminormFamily_apply, one_mul]
      change ‖x‖ ^ k *
        ‖iteratedFDeriv ℝ n (Complex.conjLIE ∘ (f : ℝ → ℂ)) x‖ ≤ _
      rw [Complex.conjLIE.norm_iteratedFDeriv_comp_left f x n]
      exact le_seminorm ℂ k n f x)

@[simp] theorem conjSLM_apply (f : 𝓢(ℝ, ℂ)) (x : ℝ) :
    conjSLM f x = (starRingEnd ℂ) (f x) := rfl

theorem continuous_conjSLM : Continuous (conjSLM : 𝓢(ℝ, ℂ) → 𝓢(ℝ, ℂ)) :=
  conjSLM.continuous

/-- The product `f · conj g` used in spectral sesquilinear forms. -/
def pointwiseMulConj (f g : 𝓢(ℝ, ℂ)) : 𝓢(ℝ, ℂ) := pointwiseMul f (conjSLM g)

@[simp] theorem pointwiseMulConj_apply (f g : 𝓢(ℝ, ℂ)) (x : ℝ) :
    pointwiseMulConj f g x = f x * (starRingEnd ℂ) (g x) := rfl

@[simp] theorem pointwiseMulConj_add_left (f₁ f₂ g : 𝓢(ℝ, ℂ)) :
    pointwiseMulConj (f₁ + f₂) g =
      pointwiseMulConj f₁ g + pointwiseMulConj f₂ g := by
  ext x
  simp
  ring

@[simp] theorem pointwiseMulConj_smul_left (c : ℂ) (f g : 𝓢(ℝ, ℂ)) :
    pointwiseMulConj (c • f) g = c • pointwiseMulConj f g := by
  ext x
  simp
  ring

@[simp] theorem pointwiseMulConj_add_right (f g₁ g₂ : 𝓢(ℝ, ℂ)) :
    pointwiseMulConj f (g₁ + g₂) =
      pointwiseMulConj f g₁ + pointwiseMulConj f g₂ := by
  ext x
  simp
  ring

@[simp] theorem pointwiseMulConj_smul_right (c : ℂ) (f g : 𝓢(ℝ, ℂ)) :
    pointwiseMulConj f (c • g) =
      (starRingEnd ℂ) c • pointwiseMulConj f g := by
  ext x
  simp
  ring

theorem continuous_pointwiseMulConj :
    Continuous (fun p : 𝓢(ℝ, ℂ) × 𝓢(ℝ, ℂ) => pointwiseMulConj p.1 p.2) := by
  exact continuous_pointwiseMul.comp
    (continuous_fst.prodMk (continuous_conjSLM.comp continuous_snd))

end

end SchwartzMap
