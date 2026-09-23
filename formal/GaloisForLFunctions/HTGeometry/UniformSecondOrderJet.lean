import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Complex.Basic

/-!
# Uniform second-order jets on a parameter set

A family `F u z` of functions of a real variable `z ∈ [0,b]` indexed by a complex parameter `u`
has a uniform second-order jet `(c₀, c₁)` with constant `C` on a parameter set `S` when

`‖F u z - c₀ u - c₁ u * z‖ ≤ C * z²` for all `u ∈ S`, `z ∈ [0,b]`.

Such jets are closed under sums, scalar multiples by bounded coefficient functions, and products
with bounded coefficients.  Jointly bounded second derivatives give jets by Taylor's theorem.  This
is the bookkeeping behind horizon expansions that are uniform in the frequency; it carries no
analytic content of its own.
-/

namespace GaloisForLFunctions.HTGeometry
open Set Filter Topology
noncomputable section
set_option autoImplicit false

/-- Uniform second-order jet on the parameter set `S` and radius `b`. -/
def HasUniformJet2 (S : Set ℂ) (b : ℝ) (F : ℂ → ℝ → ℂ) (c₀ c₁ : ℂ → ℂ) (C : ℝ) : Prop :=
  ∀ u ∈ S, ∀ z ∈ Ioc (0:ℝ) b, ‖F u z - c₀ u - c₁ u * z‖ ≤ C * z ^ (2 : ℕ)

theorem HasUniformJet2.mono {S T : Set ℂ} {b : ℝ} {F : ℂ → ℝ → ℂ} {c₀ c₁ : ℂ → ℂ} {C : ℝ}
    (h : HasUniformJet2 S b F c₀ c₁ C) (hT : T ⊆ S) : HasUniformJet2 T b F c₀ c₁ C :=
  fun u hu => h u (hT hu)

theorem HasUniformJet2.mono_radius {S : Set ℂ} {b b' : ℝ} {F : ℂ → ℝ → ℂ} {c₀ c₁ : ℂ → ℂ} {C : ℝ}
    (h : HasUniformJet2 S b F c₀ c₁ C) (hb : b' ≤ b) : HasUniformJet2 S b' F c₀ c₁ C :=
  fun u hu z hz => h u hu z ⟨hz.1, hz.2.trans hb⟩

theorem HasUniformJet2.mono_const {S : Set ℂ} {b : ℝ} {F : ℂ → ℝ → ℂ} {c₀ c₁ : ℂ → ℂ} {C C' : ℝ}
    (h : HasUniformJet2 S b F c₀ c₁ C) (hC : C ≤ C') : HasUniformJet2 S b F c₀ c₁ C' :=
  fun u hu z hz => (h u hu z hz).trans (mul_le_mul_of_nonneg_right hC (sq_nonneg z))

theorem HasUniformJet2.congr {S : Set ℂ} {b : ℝ} {F G : ℂ → ℝ → ℂ} {c₀ c₁ : ℂ → ℂ} {C : ℝ}
    (h : HasUniformJet2 S b F c₀ c₁ C) (hFG : ∀ u ∈ S, ∀ z ∈ Ioc (0:ℝ) b, G u z = F u z) :
    HasUniformJet2 S b G c₀ c₁ C :=
  fun u hu z hz => by rw [hFG u hu z hz]; exact h u hu z hz

theorem HasUniformJet2.add {S : Set ℂ} {b : ℝ} {F G : ℂ → ℝ → ℂ} {c₀ c₁ d₀ d₁ : ℂ → ℂ} {C D : ℝ}
    (hF : HasUniformJet2 S b F c₀ c₁ C) (hG : HasUniformJet2 S b G d₀ d₁ D) :
    HasUniformJet2 S b (fun u z => F u z + G u z) (fun u => c₀ u + d₀ u) (fun u => c₁ u + d₁ u)
      (C + D) := by
  intro u hu z hz
  have h1 := hF u hu z hz
  have h2 := hG u hu z hz
  calc ‖F u z + G u z - (c₀ u + d₀ u) - (c₁ u + d₁ u) * z‖
      = ‖(F u z - c₀ u - c₁ u * z) + (G u z - d₀ u - d₁ u * z)‖ := by ring_nf
    _ ≤ ‖F u z - c₀ u - c₁ u * z‖ + ‖G u z - d₀ u - d₁ u * z‖ := norm_add_le _ _
    _ ≤ C * z ^ (2 : ℕ) + D * z ^ (2 : ℕ) := add_le_add h1 h2
    _ = (C + D) * z ^ (2 : ℕ) := by ring

theorem HasUniformJet2.sub {S : Set ℂ} {b : ℝ} {F G : ℂ → ℝ → ℂ} {c₀ c₁ d₀ d₁ : ℂ → ℂ} {C D : ℝ}
    (hF : HasUniformJet2 S b F c₀ c₁ C) (hG : HasUniformJet2 S b G d₀ d₁ D) :
    HasUniformJet2 S b (fun u z => F u z - G u z) (fun u => c₀ u - d₀ u) (fun u => c₁ u - d₁ u)
      (C + D) := by
  intro u hu z hz
  have h1 := hF u hu z hz
  have h2 := hG u hu z hz
  calc ‖F u z - G u z - (c₀ u - d₀ u) - (c₁ u - d₁ u) * z‖
      = ‖(F u z - c₀ u - c₁ u * z) - (G u z - d₀ u - d₁ u * z)‖ := by ring_nf
    _ ≤ ‖F u z - c₀ u - c₁ u * z‖ + ‖G u z - d₀ u - d₁ u * z‖ := norm_sub_le _ _
    _ ≤ C * z ^ (2 : ℕ) + D * z ^ (2 : ℕ) := add_le_add h1 h2
    _ = (C + D) * z ^ (2 : ℕ) := by ring

/-- Scalar multiplication by a coefficient function bounded on `S`. -/
theorem HasUniformJet2.const_mul {S : Set ℂ} {b : ℝ} {F : ℂ → ℝ → ℂ} {c₀ c₁ : ℂ → ℂ} {C : ℝ}
    (hF : HasUniformJet2 S b F c₀ c₁ C) {k : ℂ → ℂ} {K : ℝ} (hK : ∀ u ∈ S, ‖k u‖ ≤ K) :
    HasUniformJet2 S b (fun u z => k u * F u z) (fun u => k u * c₀ u) (fun u => k u * c₁ u)
      (K * C) := by
  intro u hu z hz
  have h1 := hF u hu z hz
  calc ‖k u * F u z - k u * c₀ u - k u * c₁ u * z‖
      = ‖k u‖ * ‖F u z - c₀ u - c₁ u * z‖ := by rw [← norm_mul]; ring_nf
    _ ≤ K * (C * z ^ (2 : ℕ)) := mul_le_mul (hK u hu) h1 (norm_nonneg _)
        ((norm_nonneg _).trans (hK u hu))
    _ = K * C * z ^ (2 : ℕ) := by ring

/-- The constant family. -/
theorem hasUniformJet2_const (S : Set ℂ) (b : ℝ) (k : ℂ → ℂ) :
    HasUniformJet2 S b (fun u _ => k u) k (fun _ => 0) 0 := by
  intro u _ z _
  simp

/-- The linear family `z ↦ k u * z`. -/
theorem hasUniformJet2_linear (S : Set ℂ) (b : ℝ) (k : ℂ → ℂ) :
    HasUniformJet2 S b (fun u z => k u * z) (fun _ => 0) k 0 := by
  intro u _ z _
  simp

/-- Products of jets with bounded coefficients, on radius at most one. -/
theorem HasUniformJet2.mul {S : Set ℂ} {b : ℝ} (hb1 : b ≤ 1)
    {F G : ℂ → ℝ → ℂ} {c₀ c₁ d₀ d₁ : ℂ → ℂ} {C D M : ℝ}
    (hF : HasUniformJet2 S b F c₀ c₁ C) (hG : HasUniformJet2 S b G d₀ d₁ D)
    (hC : 0 ≤ C) (hD : 0 ≤ D) (hM : 0 ≤ M)
    (hc₀ : ∀ u ∈ S, ‖c₀ u‖ ≤ M) (hc₁ : ∀ u ∈ S, ‖c₁ u‖ ≤ M)
    (hd₀ : ∀ u ∈ S, ‖d₀ u‖ ≤ M) (hd₁ : ∀ u ∈ S, ‖d₁ u‖ ≤ M) :
    HasUniformJet2 S b (fun u z => F u z * G u z) (fun u => c₀ u * d₀ u)
      (fun u => c₀ u * d₁ u + c₁ u * d₀ u) (M ^ (2 : ℕ) + C * (2 * M + D) + 2 * M * D) := by
  intro u hu z hz
  have hz0 : 0 ≤ z := hz.1.le
  have hz1 : z ≤ 1 := hz.2.trans hb1
  set r := F u z - c₀ u - c₁ u * z with hr
  set s := G u z - d₀ u - d₁ u * z with hs
  have hrn : ‖r‖ ≤ C * z ^ (2 : ℕ) := hF u hu z hz
  have hsn : ‖s‖ ≤ D * z ^ (2 : ℕ) := hG u hu z hz
  have hFz : F u z = c₀ u + c₁ u * z + r := by rw [hr]; ring
  have hGz : G u z = d₀ u + d₁ u * z + s := by rw [hs]; ring
  have hzn : ‖(z:ℂ)‖ = z := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hz0]
  have hGb : ‖G u z‖ ≤ 2 * M + D := by
    rw [hGz]
    calc ‖d₀ u + d₁ u * z + s‖ ≤ ‖d₀ u‖ + ‖d₁ u * z‖ + ‖s‖ := norm_add₃_le
      _ ≤ M + M * 1 + D * 1 := by
        gcongr
        · exact hd₀ u hu
        · rw [norm_mul, hzn]
          exact mul_le_mul (hd₁ u hu) hz1 hz0 hM
        · exact hsn.trans (mul_le_mul_of_nonneg_left (pow_le_one₀ hz0 hz1) hD)
      _ = 2 * M + D := by ring
  have hcb : ‖c₀ u + c₁ u * z‖ ≤ 2 * M := by
    calc ‖c₀ u + c₁ u * z‖ ≤ ‖c₀ u‖ + ‖c₁ u * z‖ := norm_add_le _ _
      _ ≤ M + M * 1 := by
        gcongr
        · exact hc₀ u hu
        · rw [norm_mul, hzn]
          exact mul_le_mul (hc₁ u hu) hz1 hz0 hM
      _ = 2 * M := by ring
  have hkey : F u z * G u z - c₀ u * d₀ u - (c₀ u * d₁ u + c₁ u * d₀ u) * z =
      c₁ u * d₁ u * (z:ℂ) ^ (2 : ℕ) + r * G u z + s * (c₀ u + c₁ u * z) := by
    rw [hFz]
    conv_rhs => rw [hGz]
    rw [hGz]
    ring
  rw [hkey]
  calc ‖c₁ u * d₁ u * (z:ℂ) ^ (2 : ℕ) + r * G u z + s * (c₀ u + c₁ u * z)‖
      ≤ ‖c₁ u * d₁ u * (z:ℂ) ^ (2 : ℕ)‖ + ‖r * G u z‖ + ‖s * (c₀ u + c₁ u * z)‖ := norm_add₃_le
    _ ≤ M * M * z ^ (2 : ℕ) + C * z ^ (2 : ℕ) * (2 * M + D) + D * z ^ (2 : ℕ) * (2 * M) := by
      gcongr
      · rw [norm_mul, norm_mul, norm_pow, hzn]
        exact mul_le_mul (mul_le_mul (hc₁ u hu) (hd₁ u hu) (norm_nonneg _) hM) le_rfl
          (by positivity) (by positivity)
      · rw [norm_mul]
        exact mul_le_mul hrn hGb (norm_nonneg _) (by positivity)
      · rw [norm_mul]
        exact mul_le_mul hsn hcb (norm_nonneg _) (by positivity)
    _ = (M ^ (2 : ℕ) + C * (2 * M + D) + 2 * M * D) * z ^ (2 : ℕ) := by ring

/-- Taylor's theorem with a jointly bounded second derivative gives a uniform jet. -/
theorem hasUniformJet2_of_deriv2_bound {S : Set ℂ} {b : ℝ} (hb : 0 ≤ b)
    {F : ℂ → ℝ → ℂ} {C : ℝ}
    (hsmooth : ∀ u ∈ S, ContDiffOn ℝ 2 (F u) (Icc 0 b))
    (hbound : ∀ u ∈ S, ∀ z ∈ Icc (0:ℝ) b, ‖iteratedDerivWithin 2 (F u) (Icc 0 b) z‖ ≤ C) :
    HasUniformJet2 S b F (fun u => F u 0) (fun u => derivWithin (F u) (Icc 0 b) 0) C := by
  intro u hu z hz
  have hz' : z ∈ Icc (0:ℝ) b := ⟨hz.1.le, hz.2⟩
  have h := taylor_mean_remainder_bound (f := F u) (a := 0) (b := b) (C := C) (n := 1) hb
    ((hsmooth u hu).of_le (by norm_num)) hz' (hbound u hu)
  have htay : taylorWithinEval (F u) 1 (Icc 0 b) 0 z = F u 0 + derivWithin (F u) (Icc 0 b) 0 * z := by
    rw [taylor_within_apply]
    simp [Finset.sum_range_succ, iteratedDerivWithin_zero, iteratedDerivWithin_one]
    ring
  rw [htay, sub_add_eq_sub_sub] at h
  simpa [Nat.factorial, sub_zero] using h

theorem HasUniformJet2.congr_coeff {S : Set ℂ} {b : ℝ} {F : ℂ → ℝ → ℂ} {c₀ c₁ d₀ d₁ : ℂ → ℂ} {C : ℝ}
    (h : HasUniformJet2 S b F c₀ c₁ C) (h₀ : ∀ u ∈ S, d₀ u = c₀ u) (h₁ : ∀ u ∈ S, d₁ u = c₁ u) :
    HasUniformJet2 S b F d₀ d₁ C :=
  fun u hu z hz => by rw [h₀ u hu, h₁ u hu]; exact h u hu z hz

theorem HasUniformJet2.pow_three {S : Set ℂ} {b : ℝ} (hb1 : b ≤ 1) {F : ℂ → ℝ → ℂ}
    {c₀ c₁ : ℂ → ℂ} {C M : ℝ} (hF : HasUniformJet2 S b F c₀ c₁ C) (hC : 0 ≤ C) (hM : 0 ≤ M)
    (hc₀ : ∀ u ∈ S, ‖c₀ u‖ ≤ M) (hc₁ : ∀ u ∈ S, ‖c₁ u‖ ≤ M) :
    ∃ C', HasUniformJet2 S b (fun u z => F u z ^ (3 : ℕ)) (fun u => c₀ u ^ (3 : ℕ))
      (fun u => 3 * c₀ u ^ (2 : ℕ) * c₁ u) C' := by
  have h2 := hF.mul hb1 hF hC hC hM hc₀ hc₁ hc₀ hc₁
  have hM2 : 0 ≤ M ^ (2 : ℕ) + C * (2 * M + C) + 2 * M * C := by positivity
  have hb₀ : ∀ u ∈ S, ‖c₀ u * c₀ u‖ ≤ M ^ (2 : ℕ) := fun u hu => by
    rw [norm_mul]; exact (mul_le_mul (hc₀ u hu) (hc₀ u hu) (norm_nonneg _) hM).trans_eq (by ring)
  have hb₁ : ∀ u ∈ S, ‖c₀ u * c₁ u + c₁ u * c₀ u‖ ≤ 2 * M ^ (2 : ℕ) := fun u hu => by
    calc ‖c₀ u * c₁ u + c₁ u * c₀ u‖ ≤ ‖c₀ u * c₁ u‖ + ‖c₁ u * c₀ u‖ := norm_add_le _ _
      _ ≤ M * M + M * M := by
        rw [norm_mul, norm_mul]
        exact add_le_add (mul_le_mul (hc₀ u hu) (hc₁ u hu) (norm_nonneg _) hM)
          (mul_le_mul (hc₁ u hu) (hc₀ u hu) (norm_nonneg _) hM)
      _ = 2 * M ^ (2 : ℕ) := by ring
  have hM' : 0 ≤ max M (2 * M ^ (2 : ℕ)) := le_max_of_le_left hM
  have hsq : M ^ (2 : ℕ) ≤ 2 * M ^ (2 : ℕ) := by nlinarith [sq_nonneg M]
  have h3 := h2.mul hb1 hF hM2 hC hM'
    (fun u hu => (hb₀ u hu).trans (hsq.trans (le_max_right _ _)))
    (fun u hu => (hb₁ u hu).trans (le_max_right _ _))
    (fun u hu => (hc₀ u hu).trans (le_max_left _ _))
    (fun u hu => (hc₁ u hu).trans (le_max_left _ _))
  refine ⟨_, (h3.congr (fun u _ z _ => by ring)).congr_coeff (fun u _ => by ring)
    (fun u _ => by ring)⟩

/-- A jet on a punctured closed ball extends to the centre by continuity. -/
theorem HasUniformJet2.closedBall_of_punctured {w₀ : ℂ} {r b : ℝ} (hr : 0 < r)
    {F : ℂ → ℝ → ℂ} {c₀ c₁ : ℂ → ℂ} {C : ℝ}
    (h : HasUniformJet2 (Metric.closedBall w₀ r \ {w₀}) b F c₀ c₁ C)
    (hF : ∀ z ∈ Ioc (0:ℝ) b, ContinuousAt (fun u => F u z) w₀)
    (hc₀ : ContinuousAt c₀ w₀) (hc₁ : ContinuousAt c₁ w₀) :
    HasUniformJet2 (Metric.closedBall w₀ r) b F c₀ c₁ C := by
  intro u hu z hz
  by_cases huw : u = w₀
  · subst huw
    have hcont : ContinuousAt (fun v => ‖F v z - c₀ v - c₁ v * z‖) u :=
      (((hF z hz).sub hc₀).sub (hc₁.mul continuousAt_const)).norm
    haveI : (𝓝[≠] u).NeBot := Module.punctured_nhds_neBot ℝ ℂ u
    apply le_of_tendsto (hcont.tendsto.mono_left (nhdsWithin_le_nhds (s := {u}ᶜ)))
    have hmem : Metric.ball u r \ {u} ∈ 𝓝[≠] u :=
      sdiff_mem_nhdsWithin_compl (Metric.ball_mem_nhds u hr) {u}
    filter_upwards [hmem] with v hv
    exact h v ⟨Metric.ball_subset_closedBall hv.1, hv.2⟩ z hz
  · exact h u ⟨hu, huw⟩ z hz

end
end GaloisForLFunctions.HTGeometry
