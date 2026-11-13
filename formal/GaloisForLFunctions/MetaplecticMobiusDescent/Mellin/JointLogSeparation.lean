/-
Joint logarithmic separation adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE in the parent directory for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.CubicSieve.CubeLabelsAndPrimePools

/-!
# Joint logarithmic separation

Frequency twists in the logarithmic phase convention, smooth complex cutoffs and outer
windows. Seven twisted kernels separate jointly (`seven_twisted_kernel_separation`); weighted
first-element energies are a small power.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Classical Topology InnerProductSpace ComplexConjugate MatrixGroups ENNReal
namespace GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
open Eisenstein CubicJacobi CubicKubota CubicRamified
open scoped NNReal Pointwise
open RationalSource
open scoped Manifold ContDiff
open scoped Matrix
open UniqueFactorizationMonoid
open Asymptotics
open scoped ContDiff FourierTransform SchwartzMap
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Topology
open Filter Asymptotics MeasureTheory
open scoped BigOperators Topology
open Filter Asymptotics MeasureTheory
open scoped BigOperators
open scoped BigOperators Topology
open Filter Asymptotics MeasureTheory
open scoped BigOperators Topology
open Filter Asymptotics MeasureTheory
open scoped BigOperators Topology
open Filter
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical SchwartzMap

namespace JointLogSeparation
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic MeasureTheory
open scoped Classical SchwartzMap FourierTransform ContDiff

theorem fourier_seminorm_from_derivative_integrals
    (g : 𝓢(ℝ, ℂ)) (k : ℕ) :
    (SchwartzMap.seminorm ℝ k 0) (𝓕 g) ≤
      (2 : ℝ) ^ k *
        ∑ p ∈ Finset.range 1 ×ˢ Finset.range (k + 1),
          ∫ v : ℝ, ‖v‖ ^ p.1 * ‖iteratedFDeriv ℝ p.2 g v‖ := by
  have hpoint (w : ℝ) :=
    Real.pow_mul_norm_iteratedFDeriv_fourier_le
      (K := ⊤) (N := ⊤) (f := (g : ℝ → ℂ)) (g.smooth ⊤)
      (by intro a b ha hb; exact g.integrable_pow_mul_iteratedFDeriv volume a b)
      (k := 0) (n := k) (by simp) (by simp) w
  have hpoint' (w : ℝ) :
      ‖w‖ ^ k * ‖(𝓕 g) w‖ ≤
        (2 : ℝ) ^ k *
          ∑ p ∈ Finset.range 1 ×ˢ Finset.range (k + 1),
            ∫ v : ℝ, ‖v‖ ^ p.1 * ‖iteratedFDeriv ℝ p.2 g v‖ := by
    simpa [SchwartzMap.fourier_coe] using hpoint w
  apply SchwartzMap.seminorm_le_bound ℝ k 0 (𝓕 g)
    (mul_nonneg (pow_nonneg (by norm_num) _) (Finset.sum_nonneg
      (fun p _ => integral_nonneg (fun v => mul_nonneg (pow_nonneg (norm_nonneg _) _) (norm_nonneg _)))))
  intro w
  simpa using hpoint' w

theorem uniform_fourier_seminorm_transfer
    (g : 𝓢(ℝ, ℂ)) (k : ℕ) (S C : ℝ)
    (hS : 0 ≤ S) (_hC : 0 ≤ C)
    (hsource : ∀ i ≤ k,
      S * ((SchwartzMap.seminorm ℝ 0 i) g +
        (SchwartzMap.seminorm ℝ (volume : Measure ℝ).integrablePower i) g) ≤ C) :
    S * (SchwartzMap.seminorm ℝ k 0) (𝓕 g) ≤
      (2 : ℝ) ^ k * (k + 1) *
        (2 ^ (volume : Measure ℝ).integrablePower *
          ∫ t : ℝ, (1 + ‖t‖) ^ (-(volume : Measure ℝ).integrablePower : ℝ)) * C := by
  let V : ℝ := 2 ^ (volume : Measure ℝ).integrablePower *
    ∫ t : ℝ, (1 + ‖t‖) ^ (-(volume : Measure ℝ).integrablePower : ℝ)
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hI (i : ℕ) (hi : i ≤ k) :
      S * (∫ t : ℝ, ‖iteratedFDeriv ℝ i g t‖) ≤ V * C := by
    have hbase := SchwartzMap.integral_pow_mul_iteratedFDeriv_le ℝ volume g 0 i
    have hbase' :
        (∫ t : ℝ, ‖iteratedFDeriv ℝ i g t‖) ≤
          V * ((SchwartzMap.seminorm ℝ 0 i) g +
            (SchwartzMap.seminorm ℝ (volume : Measure ℝ).integrablePower i) g) := by
      simpa [V] using hbase
    calc
      S * (∫ t : ℝ, ‖iteratedFDeriv ℝ i g t‖) ≤
          S * (V * ((SchwartzMap.seminorm ℝ 0 i) g +
            (SchwartzMap.seminorm ℝ (volume : Measure ℝ).integrablePower i) g)) :=
        mul_le_mul_of_nonneg_left hbase' hS
      _ = V * (S * ((SchwartzMap.seminorm ℝ 0 i) g +
            (SchwartzMap.seminorm ℝ (volume : Measure ℝ).integrablePower i) g)) := by ring
      _ ≤ V * C := mul_le_mul_of_nonneg_left (hsource i hi) hV
  have hFourier := fourier_seminorm_from_derivative_integrals g k
  calc
    S * (SchwartzMap.seminorm ℝ k 0) (𝓕 g) ≤
      S * ((2 : ℝ) ^ k *
        ∑ p ∈ Finset.range 1 ×ˢ Finset.range (k + 1),
          ∫ t : ℝ, ‖t‖ ^ p.1 * ‖iteratedFDeriv ℝ p.2 g t‖) :=
      mul_le_mul_of_nonneg_left hFourier hS
    _ = (2 : ℝ) ^ k *
      ∑ p ∈ Finset.range 1 ×ˢ Finset.range (k + 1),
        S * (∫ t : ℝ, ‖t‖ ^ p.1 * ‖iteratedFDeriv ℝ p.2 g t‖) := by
      simp only [Finset.mul_sum]
      ring_nf
    _ ≤ (2 : ℝ) ^ k *
      ∑ _p ∈ Finset.range 1 ×ˢ Finset.range (k + 1), V * C := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum
      intro p hp
      have hp0 : p.1 = 0 := by
        have hlt := Finset.mem_range.mp (Finset.mem_product.mp hp).1
        omega
      have hp2 : p.2 ≤ k := Nat.lt_succ_iff.mp
        (Finset.mem_range.mp (Finset.mem_product.mp hp).2)
      simpa [hp0] using hI p.2 hp2
    _ = (2 : ℝ) ^ k * (k + 1) * V * C := by
      simp []
      ring
    _ = (2 : ℝ) ^ k * (k + 1) *
        (2 ^ (volume : Measure ℝ).integrablePower *
          ∫ t : ℝ, (1 + ‖t‖) ^ (-(volume : Measure ℝ).integrablePower : ℝ)) * C := rfl

def fourierSeminormBound (k : ℕ) (C : ℝ) : ℝ :=
  (2 : ℝ) ^ k * (k + 1) *
    (2 ^ (volume : Measure ℝ).integrablePower *
      ∫ t : ℝ, (1 + ‖t‖) ^ (-(volume : Measure ℝ).integrablePower : ℝ)) * C

def fourierPointBound (k : ℕ) (C : ℝ) : ℝ :=
  2 ^ k * (fourierSeminormBound 0 C + fourierSeminormBound k C)

theorem fourierPointBound_nonneg (k : ℕ) (C : ℝ) (hC : 0 ≤ C) :
    0 ≤ fourierPointBound k C := by unfold fourierPointBound fourierSeminormBound; positivity

theorem uniform_fourier_pointwise (g : 𝓢(ℝ, ℂ)) (k : ℕ) (S C : ℝ)
    (hS : 0 ≤ S) (hC : 0 ≤ C)
    (hsource : ∀ i ≤ k,
      S * ((SchwartzMap.seminorm ℝ 0 i) g +
        (SchwartzMap.seminorm ℝ (volume : Measure ℝ).integrablePower i) g) ≤ C)
    (t : ℝ) :
    S * (1 + ‖t‖) ^ k * ‖(𝓕 g) t‖ ≤ fourierPointBound k C := by
  have h0 : S * (SchwartzMap.seminorm ℝ 0 0) (𝓕 g) ≤ fourierSeminormBound 0 C :=
    uniform_fourier_seminorm_transfer g 0 S C hS hC
      (fun i hi => hsource i (hi.trans (Nat.zero_le k)))
  have hk : S * (SchwartzMap.seminorm ℝ k 0) (𝓕 g) ≤ fourierSeminormBound k C :=
    uniform_fourier_seminorm_transfer g k S C hS hC hsource
  have hpow : (1 + ‖t‖) ^ k ≤ (2 : ℝ) ^ k * (1 + ‖t‖ ^ k) := by
    have h := add_pow_le (show (0 : ℝ) ≤ 1 by norm_num) (norm_nonneg t) k
    have he : (2 : ℝ) ^ (k - 1) ≤ (2 : ℝ) ^ k :=
      pow_le_pow_right₀ (by norm_num) (Nat.sub_le k 1)
    simp only [one_pow] at h
    exact h.trans (mul_le_mul_of_nonneg_right he (by positivity))
  have hn0 := SchwartzMap.norm_le_seminorm ℝ (𝓕 g) t
  have hnk := SchwartzMap.norm_pow_mul_le_seminorm ℝ (𝓕 g) k t
  calc
    _ ≤ S * ((2 : ℝ) ^ k * (1 + ‖t‖ ^ k)) * ‖(𝓕 g) t‖ := by gcongr
    _ = (2 : ℝ) ^ k * (S * ‖(𝓕 g) t‖ + S * (‖t‖ ^ k * ‖(𝓕 g) t‖)) := by ring
    _ ≤ (2 : ℝ) ^ k * (S * (SchwartzMap.seminorm ℝ 0 0) (𝓕 g) +
          S * (SchwartzMap.seminorm ℝ k 0) (𝓕 g)) := by gcongr
    _ ≤ fourierPointBound k C := by
      exact mul_le_mul_of_nonneg_left (add_le_add h0 hk) (by positivity)
def profileSourceBound (g : 𝓢(ℝ, ℂ)) (J : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (J + 1),
    ((SchwartzMap.seminorm ℝ 0 i) g +
      (SchwartzMap.seminorm ℝ (volume : Measure ℝ).integrablePower i) g)

lemma profileSourceBound_nonneg (g : 𝓢(ℝ, ℂ)) (J : ℕ) :
    0 ≤ profileSourceBound g J := by
  unfold profileSourceBound
  positivity

lemma source_le_profileSourceBound (g : 𝓢(ℝ, ℂ)) (J i : ℕ) (hi : i ≤ J) :
    (SchwartzMap.seminorm ℝ 0 i) g +
      (SchwartzMap.seminorm ℝ (volume : Measure ℝ).integrablePower i) g ≤
      profileSourceBound g J := by
  unfold profileSourceBound
  apply Finset.single_le_sum (s := Finset.range (J + 1)) (a := i)
    (f := fun k : ℕ => (SchwartzMap.seminorm ℝ 0 k) g +
      (SchwartzMap.seminorm ℝ (volume : Measure ℝ).integrablePower k) g)
  · intro j hj
    positivity
  · exact Finset.mem_range.mpr (by omega)

lemma profile_fourier_envelope (g : 𝓢(ℝ, ℂ)) (J : ℕ) (t : ℝ) :
    ‖(𝓕 g) t‖ ≤ fourierPointBound (J + 2) (profileSourceBound g (J + 2)) *
      firstLogDensity J t := by
  have h := uniform_fourier_pointwise g (J + 2) 1 (profileSourceBound g (J + 2))
    (by norm_num) (profileSourceBound_nonneg g _)
    (fun i hi => by simpa using source_le_profileSourceBound g (J + 2) i hi) t
  rw [firstLogDensity, ← div_eq_mul_inv]
  apply (le_div_iff₀ (pow_pos (by positivity : 0 < 1 + ‖t‖) (J + 2))).mpr
  simpa only [one_mul, mul_comm] using h


end JointLogSeparation

namespace JointLogSeparation
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic MeasureTheory
open scoped Classical SchwartzMap FourierTransform ContDiff

/-- Fourier inversion in the logarithmic phase convention. -/
lemma schwartz_phase_inversion (g : 𝓢(ℝ, ℂ)) (x : ℝ) :
    g x = ∫ t : ℝ, kernelLogPhase t x * (𝓕 g) t := by
  have he : g x = 𝓕⁻ (𝓕 (g : ℝ → ℂ)) x :=
    (g.integrable.fourierInv_fourier_eq (𝓕 g).integrable g.continuous.continuousAt).symm
  rw [he,Real.fourierInv_eq']
  apply integral_congr_ae
  filter_upwards [] with t
  simp only [smul_eq_mul,kernelLogPhase]
  congr 1
  congr 1
  simp only [RCLike.inner_apply,conj_trivial]
  push_cast
  ring

lemma product_three_integrals (f g h : ℝ → ℂ) :
    (∫ t, f t) * (∫ t, g t) * (∫ t, h t) =
      ∫ t₁, ∫ t₂, ∫ t₃, f t₁ * g t₂ * h t₃ := by
  simp_rw [integral_const_mul, integral_mul_const]
  simp_rw [integral_const_mul, integral_mul_const]

theorem joint_separation_identity
    (A₁ A₂ : 𝓢(ℝ, ℂ)) (b : 𝓢(ℝ, ℂ)) (P F : ℂ) (s₁ s₂ s₃ : ℝ)
    (hr : P * F = ∫ t : ℝ, P * kernelLogPhase t s₃ * b t) :
    P * A₁ s₁ * A₂ s₂ * F =
      ∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ,
        P * kernelLogPhase t₁ s₁ * kernelLogPhase t₂ s₂ * kernelLogPhase t₃ s₃ *
          ((𝓕 A₁) t₁ * (𝓕 A₂) t₂ * b t₃) := by
  calc
    _ = A₁ s₁ * A₂ s₂ * (P * F) := by ring
    _ = (∫ t : ℝ, kernelLogPhase t s₁ * (𝓕 A₁) t) *
        (∫ t : ℝ, kernelLogPhase t s₂ * (𝓕 A₂) t) *
        (∫ t : ℝ, P * kernelLogPhase t s₃ * b t) := by
      rw [← schwartz_phase_inversion, ← schwartz_phase_inversion, ← hr]
    _ = ∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ,
        (kernelLogPhase t₁ s₁ * (𝓕 A₁) t₁) * (kernelLogPhase t₂ s₂ * (𝓕 A₂) t₂) *
          (P * kernelLogPhase t₃ s₃ * b t₃) := by
      exact product_three_integrals
        (fun t : ℝ => kernelLogPhase t s₁ * (𝓕 A₁) t)
        (fun t : ℝ => kernelLogPhase t s₂ * (𝓕 A₂) t)
        (fun t : ℝ => P * kernelLogPhase t s₃ * b t)
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with t₁
      apply integral_congr_ae
      filter_upwards [] with t₂
      apply integral_congr_ae
      filter_upwards [] with t₃
      ring

theorem joint_separation_envelope {ι : Type*} [Fintype ι]
    (A₁ A₂ W : 𝓢(ℝ, ℂ)) (V : ι → ℝ → ℂ) (a₁ a₂ a₃ M : ι → ℝ)
    (hM : ∀ j, 0 ≤ M j) (hV : ∀ j x, V j x ≠ 0 → |x| ≤ M j) (A J : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R → ∃ b : 𝓢(ℝ, ℂ),
      (∀ y : ι → ℝ,
        (∏ j, V j (y j)) * A₁ (∑ j, a₁ j * y j) * A₂ (∑ j, a₂ j * y j) *
          paperRadialFourier W (R * Real.exp (∑ j, a₃ j * y j)) =
        ∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ,
          (∏ j, V j (y j)) * kernelLogPhase t₁ (∑ j, a₁ j * y j) *
            kernelLogPhase t₂ (∑ j, a₂ j * y j) * kernelLogPhase t₃ (∑ j, a₃ j * y j) *
            ((𝓕 A₁) t₁ * (𝓕 A₂) t₂ * b t₃)) ∧
      (∀ t₁ t₂ t₃ : ℝ, (1 + R) ^ A * ‖(𝓕 A₁) t₁ * (𝓕 A₂) t₂ * b t₃‖ ≤
        C * firstLogDensity J t₁ * firstLogDensity J t₂ * firstLogDensity J t₃) ∧
      Integrable (fun t : ℝ => (1 + ‖t‖) ^ J * ‖b t‖) := by
  classical
  obtain ⟨C₃, hC₃, hsep⟩ := paperRadialFourier_log_separation_envelope
    V a₃ M hM hV W A (J + 2)
  let C₁ := fourierPointBound (J + 2) (profileSourceBound A₁ (J + 2))
  let C₂ := fourierPointBound (J + 2) (profileSourceBound A₂ (J + 2))
  have hC₁ : 0 ≤ C₁ := fourierPointBound_nonneg _ _ (profileSourceBound_nonneg _ _)
  have hC₂ : 0 ≤ C₂ := fourierPointBound_nonneg _ _ (profileSourceBound_nonneg _ _)
  refine ⟨C₁ * C₂ * C₃, by positivity, ?_⟩
  intro R hR
  obtain ⟨b, hb, hweighted, _, hpoint⟩ := hsep R hR
  refine ⟨b, ?_, ?_, ?_⟩
  · intro y
    let P : ℂ := ∏ j, V j (y j)
    let s₁ : ℝ := ∑ j, a₁ j * y j
    let s₂ : ℝ := ∑ j, a₂ j * y j
    let s₃ : ℝ := ∑ j, a₃ j * y j
    have hr : P * paperRadialFourier W (R * Real.exp s₃) =
        ∫ t, P * kernelLogPhase t s₃ * b t := by
      have hh := hb y
      simpa only [Finset.prod_mul_distrib, ← kernelLogPhase_sum, P, s₃] using hh
    exact joint_separation_identity A₁ A₂ b P
      (paperRadialFourier W (R * Real.exp s₃)) s₁ s₂ s₃ hr
  · intro t₁ t₂ t₃
    have hb₃ : (1 + R) ^ A * ‖b t₃‖ ≤ C₃ * firstLogDensity J t₃ := by
      rw [firstLogDensity, ← div_eq_mul_inv]
      apply (le_div_iff₀ (pow_pos (by positivity : 0 < 1 + ‖t₃‖) (J + 2))).mpr
      simpa only [Real.norm_eq_abs, mul_comm, mul_left_comm, mul_assoc] using hpoint t₃
    have h₁ := profile_fourier_envelope A₁ J t₁
    have h₂ := profile_fourier_envelope A₂ J t₂
    simp only [norm_mul]
    calc
      _ = ‖(𝓕 A₁) t₁‖ * ‖(𝓕 A₂) t₂‖ * ((1 + R)^A * ‖b t₃‖) := by ring
      _ ≤ (C₁ * firstLogDensity J t₁) * (C₂ * firstLogDensity J t₂) * (C₃ * firstLogDensity J t₃) := by
        exact mul_le_mul (mul_le_mul h₁ h₂ (norm_nonneg _) (mul_nonneg hC₁ (firstLogDensity_nonneg _ _))) hb₃ (by positivity)
          (mul_nonneg (mul_nonneg hC₁ (firstLogDensity_nonneg _ _))
            (mul_nonneg hC₂ (firstLogDensity_nonneg _ _)))
      _ = _ := by ring
  · apply hweighted.mono'
    · exact (by fun_prop : Continuous (fun t : ℝ => (1 + ‖t‖) ^ J * ‖b t‖)).aestronglyMeasurable
    · filter_upwards [] with t
      rw [Real.norm_of_nonneg (by positivity)]
      rw [←Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ (by linarith [norm_nonneg t]) (Nat.le_add_right J 2)) (norm_nonneg _)

lemma seven_phase_factor (z ud ue uv kap x₁ x₂ t₁ t₂ t₃ : ℝ) :
    kernelLogPhase t₁ (z + x₁) * kernelLogPhase t₂ (z + x₂) *
      kernelLogPhase t₃ (kap - ud - 2 * ue - 2 * uv - x₁ - x₂) =
    kernelLogPhase (t₁ + t₂) z * kernelLogPhase t₃ (kap - ud - 2 * ue - 2 * uv) *
      kernelLogPhase (t₁ - t₃) x₁ * kernelLogPhase (t₂ - t₃) x₂ := by
  unfold kernelLogPhase
  simp only [← Complex.exp_add]
  congr 1
  push_cast
  ring

def outerWindow (V : Fin 7 → ℝ → ℂ) (z ud ue uv kap : ℝ) : ℂ :=
  V 0 z * V 1 ud * V 2 ue * V 3 uv * V 4 kap

def fixedColumnTest (V : ℝ → ℂ) (t : ℝ) (x : ℝ) : ℂ := V x * kernelLogPhase t x

theorem seven_kernel_separation (A₁ A₂ W : 𝓢(ℝ, ℂ))
    (V : Fin 7 → ℝ → ℂ) (M : Fin 7 → ℝ) (hM : ∀ j, 0 ≤ M j)
    (hV : ∀ j x, V j x ≠ 0 → |x| ≤ M j) (A J : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R → ∃ b : 𝓢(ℝ, ℂ),
      (∀ z ud ue uv kap x₁ x₂ : ℝ,
        outerWindow V z ud ue uv kap * V 5 x₁ * V 6 x₂ * A₁ (z + x₁) * A₂ (z + x₂) *
          paperRadialFourier W
            (R * Real.exp (kap - ud - 2 * ue - 2 * uv - x₁ - x₂)) =
        ∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ,
          outerWindow V z ud ue uv kap * kernelLogPhase (t₁ + t₂) z *
            kernelLogPhase t₃ (kap - ud - 2 * ue - 2 * uv) *
            fixedColumnTest (V 5) (t₁ - t₃) x₁ * fixedColumnTest (V 6) (t₂ - t₃) x₂ *
            ((𝓕 A₁) t₁ * (𝓕 A₂) t₂ * b t₃)) ∧
      (∀ t₁ t₂ t₃ : ℝ, (1 + R) ^ A * ‖(𝓕 A₁) t₁ * (𝓕 A₂) t₂ * b t₃‖ ≤
        C * firstLogDensity J t₁ * firstLogDensity J t₂ * firstLogDensity J t₃) ∧
      Integrable (fun t : ℝ => (1 + ‖t‖) ^ J * ‖b t‖) := by
  let a₁ : Fin 7 → ℝ := ![1, 0, 0, 0, 0, 1, 0]
  let a₂ : Fin 7 → ℝ := ![1, 0, 0, 0, 0, 0, 1]
  let a₃ : Fin 7 → ℝ := ![0, -1, -2, -2, 1, -1, -1]
  obtain ⟨C, hC, hsep⟩ := joint_separation_envelope A₁ A₂ W V a₁ a₂ a₃ M hM hV A J
  refine ⟨C, hC, ?_⟩
  intro R hR
  obtain ⟨b, hb, hpoint, hint⟩ := hsep R hR
  refine ⟨b, ?_, hpoint, hint⟩
  intro z ud ue uv kap x₁ x₂
  let y : Fin 7 → ℝ := ![z, ud, ue, uv, kap, x₁, x₂]
  have h₁ : (∑ j, a₁ j * y j) = z + x₁ := by
    simp [a₁, y, Fin.sum_univ_succ]
  have h₂ : (∑ j, a₂ j * y j) = z + x₂ := by
    simp [a₂, y, Fin.sum_univ_succ]
  have h₃ : (∑ j, a₃ j * y j) = kap - ud - 2 * ue - 2 * uv - x₁ - x₂ := by
    simp [a₃, y, Fin.sum_univ_succ]
    ring
  have hp : (∏ j, V j (y j)) = outerWindow V z ud ue uv kap * V 5 x₁ * V 6 x₂ := by
    simp [outerWindow, y, Fin.prod_univ_succ, mul_assoc]
  have h := hb y
  rw [h₁, h₂, h₃, hp] at h
  rw [h]
  apply integral_congr_ae
  filter_upwards [] with t₁
  apply integral_congr_ae
  filter_upwards [] with t₂
  apply integral_congr_ae
  filter_upwards [] with t₃
  have heq := seven_phase_factor z ud ue uv kap x₁ x₂ t₁ t₂ t₃
  unfold fixedColumnTest
  calc
    _ = (outerWindow V z ud ue uv kap * V 5 x₁ * V 6 x₂) *
      (kernelLogPhase t₁ (z + x₁) * kernelLogPhase t₂ (z + x₂) *
      kernelLogPhase t₃ (kap - ud - 2 * ue - 2 * uv - x₁ - x₂)) *
      ((𝓕 A₁) t₁ * (𝓕 A₂) t₂ * b t₃) := by ring
    _ = _ := by rw [heq]; ring

end JointLogSeparation

namespace JointLogSeparation
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic MeasureTheory
open scoped Classical SchwartzMap FourierTransform ContDiff

def phaseDerivative (t : ℝ) : ℂ := ((2 * Real.pi * t : ℝ) : ℂ) * Complex.I

lemma kernelLogPhase_hasDerivAt (t x : ℝ) :
    HasDerivAt (kernelLogPhase t) (phaseDerivative t * kernelLogPhase t x) x := by
  have h := ((Complex.ofRealCLM.hasDerivAt (x := x)).const_mul (phaseDerivative t)).cexp
  simp only [Complex.ofRealCLM_apply, Complex.ofReal_one, mul_one] at h
  have he (y : ℝ) : Complex.exp (phaseDerivative t * (y : ℂ)) = kernelLogPhase t y := by
    unfold phaseDerivative kernelLogPhase
    congr 1
    push_cast
    ring
  simp_rw [he] at h
  simpa only [mul_comm] using h

lemma kernelLogPhase_iteratedDeriv (t : ℝ) (n : ℕ) :
    iteratedDeriv n (kernelLogPhase t) = fun x => phaseDerivative t ^ n * kernelLogPhase t x := by
  induction n with
  | zero => funext x; simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext x
    rw [show deriv (fun y => phaseDerivative t ^ n * kernelLogPhase t y) x =
        phaseDerivative t ^ n * (phaseDerivative t * kernelLogPhase t x) from
      ((kernelLogPhase_hasDerivAt t x).const_mul _).deriv]
    simp only [pow_succ]
    ring

lemma phaseDerivative_norm (t : ℝ) : ‖phaseDerivative t‖ = 2 * Real.pi * ‖t‖ := by
  simp only [phaseDerivative, norm_mul, Complex.norm_real, Complex.norm_I, mul_one]
  rw [Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), Real.norm_of_nonneg Real.pi_pos.le]

lemma kernelLogPhase_iteratedFDeriv_norm (t x : ℝ) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (kernelLogPhase t) x‖ = (2 * Real.pi * ‖t‖) ^ n := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, kernelLogPhase_iteratedDeriv]
  simp only [norm_mul, norm_pow, phaseDerivative_norm, kernelLogPhase_norm, mul_one]

lemma kernelLogPhase_temperate (t : ℝ) : (kernelLogPhase t).HasTemperateGrowth := by
  constructor
  · unfold kernelLogPhase
    have h : ContDiff ℝ ∞ (fun u : ℝ => (2 * Real.pi * t : ℝ) * u) :=
      contDiff_const.mul contDiff_id
    exact ((Complex.ofRealCLM.contDiff.comp h).mul contDiff_const).cexp
  · intro n
    refine ⟨0,(2 * Real.pi * ‖t‖) ^ n,?_⟩
    intro x
    rw [kernelLogPhase_iteratedFDeriv_norm,pow_zero,mul_one]

def frequencyTwist (g : 𝓢(ℝ, ℂ)) (t : ℝ) : 𝓢(ℝ, ℂ) :=
  SchwartzMap.smulLeftCLM ℂ (kernelLogPhase t) g

@[simp] lemma frequencyTwist_apply (g : 𝓢(ℝ, ℂ)) (t x : ℝ) :
    frequencyTwist g t x = kernelLogPhase t x * g x := by
  exact SchwartzMap.smulLeftCLM_apply_apply (kernelLogPhase_temperate t) g x

lemma kernelLogPhase_add_frequency (t s x : ℝ) :
    kernelLogPhase (t + s) x = kernelLogPhase t x * kernelLogPhase s x := by
  unfold kernelLogPhase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

@[simp] lemma frequencyTwist_twice (g : 𝓢(ℝ, ℂ)) (t s : ℝ) :
    frequencyTwist (frequencyTwist g t) s = frequencyTwist g (t + s) := by
  ext x
  simp only [frequencyTwist_apply, kernelLogPhase_add_frequency]
  ring

@[simp] lemma frequencyTwist_norm (g : 𝓢(ℝ, ℂ)) (t x : ℝ) :
    ‖frequencyTwist g t x‖ = ‖g x‖ := by simp [kernelLogPhase_norm]

lemma frequencyTwist_tsupport (g : 𝓢(ℝ, ℂ)) (t : ℝ) :
    tsupport (frequencyTwist g t) = tsupport g := by
  apply congrArg (fun s : Set ℝ => closure s)
  ext x
  have hp : kernelLogPhase t x ≠ 0 := by
    intro hz
    have hn := kernelLogPhase_norm t x
    rw [hz, norm_zero] at hn
    norm_num at hn
  simp only [Function.mem_support, frequencyTwist_apply, ne_eq, mul_eq_zero, hp, false_or]

def derivativeSeminormSum (g : 𝓢(ℝ, ℂ)) (k n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (n + 1), (SchwartzMap.seminorm ℝ k i) g

lemma derivativeSeminormSum_nonneg (g : 𝓢(ℝ, ℂ)) (k n : ℕ) :
    0 ≤ derivativeSeminormSum g k n := by unfold derivativeSeminormSum; positivity

lemma seminorm_le_derivativeSeminormSum (g : 𝓢(ℝ, ℂ)) (k n i : ℕ) (hi : i ≤ n) :
    (SchwartzMap.seminorm ℝ k i) g ≤ derivativeSeminormSum g k n := by
  apply Finset.single_le_sum (s := Finset.range (n + 1))
    (f := fun j => (SchwartzMap.seminorm ℝ k j) g) (a := i)
  · intro j hj; positivity
  · exact Finset.mem_range.mpr (by omega)

theorem frequencyTwist_seminorm_bound (g : 𝓢(ℝ, ℂ)) (t : ℝ) (k n : ℕ) :
    (SchwartzMap.seminorm ℝ k n) (frequencyTwist g t) ≤
      (2 : ℝ)^n * (1 + 2 * Real.pi * ‖t‖)^n * derivativeSeminormSum g k n := by
  apply SchwartzMap.seminorm_le_bound ℝ k n _
    (mul_nonneg (mul_nonneg (by positivity) (by positivity)) (derivativeSeminormSum_nonneg _ _ _))
  intro x
  have hh := norm_iteratedFDeriv_mul_le (kernelLogPhase_temperate t).1 (g.smooth ⊤) x
    (n := n) (by exact_mod_cast le_top)
  have hfun : (frequencyTwist g t : ℝ → ℂ) = fun x => kernelLogPhase t x * g x := by
    funext x; exact frequencyTwist_apply g t x
  rw [hfun]
  calc
    _ ≤ ‖x‖^k * ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
        ‖iteratedFDeriv ℝ i (kernelLogPhase t) x‖ * ‖iteratedFDeriv ℝ (n-i) g x‖ := by gcongr
    _ = ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
        (2 * Real.pi * ‖t‖)^i * (‖x‖^k * ‖iteratedFDeriv ℝ (n-i) g x‖) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [kernelLogPhase_iteratedFDeriv_norm]
      ring
    _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
        (1 + 2 * Real.pi * ‖t‖)^n * derivativeSeminormSum g k n := by
      apply Finset.sum_le_sum
      intro i hi
      have hin : i ≤ n := Finset.mem_range_succ_iff.mp hi
      have hp : (2 * Real.pi * ‖t‖)^i ≤ (1 + 2 * Real.pi * ‖t‖)^n := by
        calc
          _ ≤ (1 + 2 * Real.pi * ‖t‖)^i := by gcongr; linarith
          _ ≤ _ := pow_le_pow_right₀ (by
            have hc : 0 ≤ 2 * Real.pi * ‖t‖ := by positivity
            linarith) hin
      have hs := (SchwartzMap.le_seminorm ℝ k (n-i) g x).trans
        (seminorm_le_derivativeSeminormSum g k n (n-i) (Nat.sub_le n i))
      exact mul_le_mul (mul_le_mul_of_nonneg_left hp (by positivity)) hs (by positivity)
        (by positivity)
    _ = _ := by
      rw [← Finset.sum_mul, ← Finset.sum_mul, ← Nat.cast_sum, Nat.sum_range_choose]
      norm_cast

theorem frequencyTwist_seminorm_polynomial (g : 𝓢(ℝ, ℂ)) (t : ℝ) (k n : ℕ) :
    (SchwartzMap.seminorm ℝ k n) (frequencyTwist g t) ≤
      ((2 : ℝ)^n * (1 + 2 * Real.pi)^n * derivativeSeminormSum g k n) * (1 + ‖t‖)^n := by
  have hsum := derivativeSeminormSum_nonneg g k n
  have hp : 1 + 2 * Real.pi * ‖t‖ ≤ (1 + 2 * Real.pi) * (1 + ‖t‖) := by
    nlinarith [Real.pi_pos, norm_nonneg t]
  calc
    _ ≤ (2 : ℝ)^n * (1 + 2 * Real.pi * ‖t‖)^n * derivativeSeminormSum g k n :=
      frequencyTwist_seminorm_bound g t k n
    _ ≤ (2 : ℝ)^n * ((1 + 2 * Real.pi) * (1 + ‖t‖))^n * derivativeSeminormSum g k n := by
      gcongr
    _ = _ := by rw [mul_pow]; ring

def twistSourceBound (g : 𝓢(ℝ, ℂ)) (K : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (K + 1),
    ((2 : ℝ)^i * (1 + 2 * Real.pi)^i *
      (derivativeSeminormSum g 0 i + derivativeSeminormSum g (volume : Measure ℝ).integrablePower i))

lemma twistSourceBound_nonneg (g : 𝓢(ℝ, ℂ)) (K : ℕ) : 0 ≤ twistSourceBound g K := by
  apply Finset.sum_nonneg
  intro i hi
  exact mul_nonneg (mul_nonneg (by positivity) (by positivity))
    (add_nonneg (derivativeSeminormSum_nonneg _ _ _) (derivativeSeminormSum_nonneg _ _ _))

theorem profileSourceBound_frequencyTwist (g : 𝓢(ℝ, ℂ)) (t : ℝ) (K : ℕ) :
    profileSourceBound (frequencyTwist g t) K ≤ twistSourceBound g K * (1 + ‖t‖)^K := by
  unfold profileSourceBound twistSourceBound
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i hi
  have hin : i ≤ K := Finset.mem_range_succ_iff.mp hi
  have hb := add_le_add (frequencyTwist_seminorm_polynomial g t 0 i)
    (frequencyTwist_seminorm_polynomial g t (volume : Measure ℝ).integrablePower i)
  have hn : 0 ≤ (2 : ℝ)^i * (1 + 2 * Real.pi)^i *
      (derivativeSeminormSum g 0 i + derivativeSeminormSum g (volume : Measure ℝ).integrablePower i) :=
    mul_nonneg (mul_nonneg (by positivity) (by positivity))
      (add_nonneg (derivativeSeminormSum_nonneg _ _ _) (derivativeSeminormSum_nonneg _ _ _))
  calc
    _ ≤ ((2 : ℝ)^i * (1 + 2 * Real.pi)^i *
        (derivativeSeminormSum g 0 i + derivativeSeminormSum g (volume : Measure ℝ).integrablePower i)) *
          (1 + ‖t‖)^i := by
            simpa only [←add_mul,←mul_add,mul_assoc] using hb
    _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by linarith [norm_nonneg t]) hin) hn

lemma fourierPointBound_mono (K : ℕ) {C D : ℝ} (hCD : C ≤ D) :
    fourierPointBound K C ≤ fourierPointBound K D := by
  unfold fourierPointBound fourierSeminormBound
  gcongr

lemma fourierPointBound_mul (K : ℕ) (C D : ℝ) :
    fourierPointBound K (C * D) = fourierPointBound K C * D := by
  unfold fourierPointBound fourierSeminormBound
  ring

theorem twisted_profile_fourier_envelope (g : 𝓢(ℝ, ℂ)) (t s : ℝ) (J : ℕ) :
    ‖(𝓕 (frequencyTwist g t)) s‖ ≤
      fourierPointBound (J + 2) (twistSourceBound g (J + 2)) *
        (1 + ‖t‖)^(J + 2) * firstLogDensity J s := by
  calc
    _ ≤ fourierPointBound (J + 2) (profileSourceBound (frequencyTwist g t) (J + 2)) *
        firstLogDensity J s := profile_fourier_envelope _ _ _
    _ ≤ fourierPointBound (J + 2) (twistSourceBound g (J + 2) * (1 + ‖t‖)^(J + 2)) *
        firstLogDensity J s :=
      mul_le_mul_of_nonneg_right (fourierPointBound_mono _ (profileSourceBound_frequencyTwist _ _ _))
        (firstLogDensity_nonneg _ _)
    _ = _ := by rw [fourierPointBound_mul]

end JointLogSeparation

namespace JointLogSeparation
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic MeasureTheory
open scoped Classical SchwartzMap FourierTransform ContDiff

lemma integrable_phase_schwartz (b : 𝓢(ℝ, ℂ)) (x : ℝ) :
    Integrable (fun t : ℝ => kernelLogPhase t x * b t) := by
  have h := integrable_log_pair b x 0 1
  convert h using 1
  funext t
  simp [kernelLogPhase, mul_comm]

theorem finite_triple_phase_integral {α : Type*} (s : Finset α)
    (b₁ b₂ b₃ : 𝓢(ℝ, ℂ)) (x y z : α → ℝ) (c : α → ℂ) :
    (∑ i ∈ s, ∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ,
      (kernelLogPhase t₁ (x i) * b₁ t₁) * ((kernelLogPhase t₂ (y i) * b₂ t₂) *
        ((kernelLogPhase t₃ (z i) * b₃ t₃) * c i))) =
    ∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ, ∑ i ∈ s,
      (kernelLogPhase t₁ (x i) * b₁ t₁) * ((kernelLogPhase t₂ (y i) * b₂ t₂) *
        ((kernelLogPhase t₃ (z i) * b₃ t₃) * c i)) := by
  let f := fun i (t₁ t₂ t₃ : ℝ) =>
    (kernelLogPhase t₁ (x i) * b₁ t₁) * ((kernelLogPhase t₂ (y i) * b₂ t₂) *
        ((kernelLogPhase t₃ (z i) * b₃ t₃) * c i))
  have hi₃ (i : α) (t₁ t₂ : ℝ) : Integrable (f i t₁ t₂) :=
    (((integrable_phase_schwartz b₃ (z i)).mul_const (c i)).const_mul _).const_mul _
  have hi₂ (i : α) (t₁ : ℝ) : Integrable (fun t₂ => ∫ t₃ : ℝ, f i t₁ t₂ t₃) := by
    simp only [f, integral_const_mul, integral_mul_const]
    exact ((integrable_phase_schwartz b₂ (y i)).mul_const _).const_mul _
  have hi₁ (i : α) : Integrable (fun t₁ => ∫ t₂ : ℝ, ∫ t₃ : ℝ, f i t₁ t₂ t₃) := by
    simp only [f, integral_const_mul, integral_mul_const]
    exact (integrable_phase_schwartz b₁ (x i)).mul_const _
  change (∑ i ∈ s, ∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ, f i t₁ t₂ t₃) = _
  rw [← integral_finsetSum _ (fun i _ => hi₁ i)]
  apply integral_congr_ae
  filter_upwards [] with t₁
  rw [← integral_finsetSum _ (fun i _ => hi₂ i t₁)]
  apply integral_congr_ae
  filter_upwards [] with t₂
  exact (integral_finsetSum _ (fun i _ => hi₃ i t₁ t₂)).symm

end JointLogSeparation

namespace JointLogSeparation
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic MeasureTheory
open scoped Classical SchwartzMap FourierTransform

abbrev Frequency := ℝ × ℝ × ℝ

def tripleCoefficient (b₁ b₂ b₃ : 𝓢(ℝ, ℂ)) (t : Frequency) : ℂ :=
  b₁ t.1 * (b₂ t.2.1 * b₃ t.2.2)

lemma tripleCoefficient_integrable (b₁ b₂ b₃ : 𝓢(ℝ, ℂ)) :
    Integrable (tripleCoefficient b₁ b₂ b₃) :=
  b₁.integrable.mul_prod (b₂.integrable.mul_prod b₃.integrable)

lemma tripleCoefficient_bounded_integrable (b₁ b₂ b₃ : 𝓢(ℝ, ℂ))
    (F : Frequency → ℂ) (hF : Continuous F) (M : ℝ) (hM : ∀ t, ‖F t‖ ≤ M) :
    Integrable (fun t => tripleCoefficient b₁ b₂ b₃ t * F t) :=
  (tripleCoefficient_integrable b₁ b₂ b₃).mul_bdd hF.aestronglyMeasurable
    (Filter.Eventually.of_forall hM)

lemma tripleCoefficient_norm_bounded_integrable (b₁ b₂ b₃ : 𝓢(ℝ, ℂ))
    (G : Frequency → ℝ) (hG : Continuous G) (M : ℝ) (hM : ∀ t, ‖G t‖ ≤ M) :
    Integrable (fun t => ‖tripleCoefficient b₁ b₂ b₃ t‖ * G t) :=
  (tripleCoefficient_integrable b₁ b₂ b₃).norm.mul_bdd hG.aestronglyMeasurable
    (Filter.Eventually.of_forall hM)

lemma tripleCoefficient_slice_integrable (b₁ b₂ b₃ : 𝓢(ℝ, ℂ))
    (F : Frequency → ℂ) (hF : Continuous F) (M : ℝ) (hM : ∀ t, ‖F t‖ ≤ M) (x : ℝ) :
    Integrable (fun t : ℝ × ℝ => tripleCoefficient b₁ b₂ b₃ (x,t) * F (x,t)) := by
  have hc : Integrable (fun t : ℝ × ℝ => b₁ x * (b₂ t.1 * b₃ t.2)) :=
    (b₂.integrable.mul_prod b₃.integrable).const_mul (b₁ x)
  apply hc.mul_bdd
  · exact (hF.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun t => hM (x,t))

lemma tripleCoefficient_norm_slice_integrable (b₁ b₂ b₃ : 𝓢(ℝ, ℂ))
    (G : Frequency → ℝ) (hG : Continuous G) (M : ℝ) (hM : ∀ t, ‖G t‖ ≤ M) (x : ℝ) :
    Integrable (fun t : ℝ × ℝ => ‖tripleCoefficient b₁ b₂ b₃ (x,t)‖ * G (x,t)) := by
  have hc : Integrable (fun t : ℝ × ℝ => ‖b₁ x * (b₂ t.1 * b₃ t.2)‖) :=
    ((b₂.integrable.mul_prod b₃.integrable).const_mul (b₁ x)).norm
  apply hc.mul_bdd
  · exact (hG.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun t => hM (x,t))

lemma nested_eq_integral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (f : Frequency → E) (hf : Integrable f)
    (hslice : ∀ x : ℝ, Integrable (fun yz : ℝ × ℝ => f (x,yz))) :
    (∫ x : ℝ, ∫ y : ℝ, ∫ z : ℝ, f (x,y,z)) = ∫ t : Frequency, f t := by
  rw [Measure.volume_eq_prod ℝ (ℝ × ℝ), integral_prod _ hf]
  apply integral_congr_ae
  filter_upwards [] with x
  simpa only [Measure.volume_eq_prod] using (integral_prod _ (hslice x)).symm

theorem triple_integral_bound (b₁ b₂ b₃ : 𝓢(ℝ, ℂ))
    (F : Frequency → ℂ) (G : Frequency → ℝ)
    (hF : Continuous F) (hG : Continuous G) (hG0 : ∀ t, 0 ≤ G t)
    (D M : ℝ) (hD : 0 ≤ D) (hM : ∀ t, G t ≤ M)
    (hpoint : ∀ t, ‖F t‖ ≤ D * G t) :
    ‖∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ,
      tripleCoefficient b₁ b₂ b₃ (t₁,t₂,t₃) * F (t₁,t₂,t₃)‖ ≤
    D * (∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ,
      ‖tripleCoefficient b₁ b₂ b₃ (t₁,t₂,t₃)‖ * G (t₁,t₂,t₃)) := by
  have hFb : ∀ t, ‖F t‖ ≤ D * M := fun t => (hpoint t).trans (mul_le_mul_of_nonneg_left (hM t) hD)
  have hGb : ∀ t, ‖G t‖ ≤ M := fun t => by simpa [Real.norm_of_nonneg (hG0 t)] using hM t
  have hfi := tripleCoefficient_bounded_integrable b₁ b₂ b₃ F hF (D*M) hFb
  have hgi := tripleCoefficient_norm_bounded_integrable b₁ b₂ b₃ G hG M hGb
  rw [nested_eq_integral _ hfi (tripleCoefficient_slice_integrable b₁ b₂ b₃ F hF (D*M) hFb),
    nested_eq_integral _ hgi (tripleCoefficient_norm_slice_integrable b₁ b₂ b₃ G hG M hGb)]
  calc
    _ ≤ ∫ t : Frequency, ‖tripleCoefficient b₁ b₂ b₃ t * F t‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ t : Frequency, D * (‖tripleCoefficient b₁ b₂ b₃ t‖ * G t) := by
      apply integral_mono hfi.norm (hgi.const_mul D)
      intro t
      simp only [norm_mul]
      calc
        _ ≤ ‖tripleCoefficient b₁ b₂ b₃ t‖ * (D * G t) :=
          mul_le_mul_of_nonneg_left (hpoint t) (norm_nonneg _)
        _ = _ := by ring
    _ = _ := integral_const_mul _ _

end JointLogSeparation

namespace JointLogSeparation
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic MeasureTheory
open scoped Classical SchwartzMap FourierTransform

theorem finite_triple_bounded_integral {α : Type*} (s : Finset α)
    (b₁ b₂ b₃ : 𝓢(ℝ, ℂ)) (F : α → Frequency → ℂ)
    (hF : ∀ i ∈ s, Continuous (F i)) (M : α → ℝ)
    (hM : ∀ i ∈ s, ∀ q, ‖F i q‖ ≤ M i) :
    (∑ i ∈ s, ∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ,
      tripleCoefficient b₁ b₂ b₃ (t₁,t₂,t₃) * F i (t₁,t₂,t₃)) =
    ∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ,
      tripleCoefficient b₁ b₂ b₃ (t₁,t₂,t₃) * (∑ i ∈ s, F i (t₁,t₂,t₃)) := by
  have hc : Continuous (fun q => ∑ i ∈ s, F i q) := continuous_finsetSum _ hF
  have hb (q : Frequency) : ‖∑ i ∈ s, F i q‖ ≤ ∑ i ∈ s, M i :=
    (norm_sum_le _ _).trans (Finset.sum_le_sum (fun i hi => hM i hi q))
  have hi (i : α) (hi : i ∈ s) := tripleCoefficient_bounded_integrable b₁ b₂ b₃ (F i) (hF i hi) (M i) (hM i hi)
  have hs := tripleCoefficient_bounded_integrable b₁ b₂ b₃ (fun q => ∑ i ∈ s, F i q) hc _ hb
  calc
    _ = ∑ i ∈ s, ∫ q : Frequency, tripleCoefficient b₁ b₂ b₃ q * F i q := by
      apply Finset.sum_congr rfl
      intro i hmem
      exact nested_eq_integral _ (hi i hmem)
        (tripleCoefficient_slice_integrable b₁ b₂ b₃ (F i) (hF i hmem) (M i) (hM i hmem))
    _ = ∫ q : Frequency, ∑ i ∈ s, tripleCoefficient b₁ b₂ b₃ q * F i q :=
      (integral_finsetSum s hi).symm
    _ = ∫ q : Frequency, tripleCoefficient b₁ b₂ b₃ q * (∑ i ∈ s, F i q) := by
      simp only [Finset.mul_sum]
    _ = _ := (nested_eq_integral _ hs
      (tripleCoefficient_slice_integrable b₁ b₂ b₃ (fun q => ∑ i ∈ s, F i q) hc _ hb)).symm

end JointLogSeparation

open scoped Classical SchwartzMap FourierTransform ContDiff

namespace JointLogSeparation
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic

def halfNormalizationMultiplier (U : ℝ → ℂ) (s : ℝ) : ℂ :=
  U s * (Real.exp (-s / 2) : ℂ)

lemma halfNormalization_temperate (U : ℝ → ℂ) (hUc : HasCompactSupport U)
    (hUs : ContDiff ℝ ∞ U) : (halfNormalizationMultiplier U).HasTemperateGrowth := by
  apply (hUc.mul_right : HasCompactSupport (halfNormalizationMultiplier U)).hasTemperateGrowth
  change ContDiff ℝ ∞ (fun s : ℝ => U s * (Real.exp (-s / 2) : ℂ))
  have he : ContDiff ℝ ∞ (fun s : ℝ => Real.exp (-s / 2)) := by fun_prop
  exact hUs.mul (Complex.ofRealCLM.contDiff.comp he)

def halfNormalizationCLM (U : ℝ → ℂ) : 𝓢(ℝ, ℂ) →L[ℝ] 𝓢(ℝ, ℂ) :=
  (SchwartzMap.smulLeftCLM ℂ (halfNormalizationMultiplier U)).restrictScalars ℝ

lemma halfNormalizationCLM_apply (U : ℝ → ℂ) (hUc : HasCompactSupport U)
    (hUs : ContDiff ℝ ∞ U) (g : 𝓢(ℝ, ℂ)) (s : ℝ) :
    halfNormalizationCLM U g s = U s * (Real.exp (-s / 2) : ℂ) * g s := by
  exact SchwartzMap.smulLeftCLM_apply_apply (halfNormalization_temperate U hUc hUs) g s

lemma sqrt_exp_half (s : ℝ) : Real.sqrt (Real.exp s) = Real.exp (s / 2) := by
  apply (Real.sqrt_eq_iff_mul_self_eq (Real.exp_pos s).le (Real.exp_pos (s / 2)).le).mpr
  rw [← Real.exp_add]
  congr 1
  ring

theorem halfNormalization_exact (U : ℝ → ℂ) (hUc : HasCompactSupport U)
    (hUs : ContDiff ℝ ∞ U) (g : 𝓢(ℝ, ℂ)) (hU : ∀ s, g s ≠ 0 → U s = 1) (s : ℝ) :
    halfNormalizationCLM U g s = g s / (Real.sqrt (Real.exp s) : ℂ) := by
  rw [halfNormalizationCLM_apply U hUc hUs]
  by_cases hg : g s = 0
  · simp [hg]
  rw [hU s hg, one_mul, sqrt_exp_half]
  have he : (Real.exp (-s / 2) : ℂ) = ((Real.exp (s / 2) : ℂ))⁻¹ := by
    rw [← Complex.ofReal_inv, ← Real.exp_neg]
    congr 2
    ring
  rw [he]
  exact (div_eq_inv_mul (g s) (Real.exp (s / 2) : ℂ)).symm

lemma halfNormalization_twist (U : ℝ → ℂ) (hUc : HasCompactSupport U)
    (hUs : ContDiff ℝ ∞ U) (g : 𝓢(ℝ, ℂ)) (t : ℝ) :
    halfNormalizationCLM U (frequencyTwist g t) = frequencyTwist (halfNormalizationCLM U g) t := by
  ext s
  simp only [halfNormalizationCLM_apply U hUc hUs, frequencyTwist_apply]
  ring

theorem halfNormalization_source_control (U : ℝ → ℂ) (S : Finset (ℕ × ℕ)) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧ ∀ g : 𝓢(ℝ, ℂ),
      S.sup (schwartzSeminormFamily ℝ ℝ ℂ) (halfNormalizationCLM U g) ≤
        C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) g :=
  SchwartzPlanePoisson.schwartzCLM_finite_seminorm_control (halfNormalizationCLM U) S

end JointLogSeparation

namespace JointLogSeparation
open Eisenstein SchwartzPlanePoisson
open scoped ContDiff

theorem exists_complex_smooth_cutoff (A : ℝ) (hA : 0 ≤ A) :
    ∃ U : ℝ → ℂ, HasCompactSupport U ∧ ContDiff ℝ ∞ U ∧
      (∀ s, |s| ≤ A → U s = 1) ∧
      tsupport U ⊆ Set.Icc (-(A + 1)) (A + 1) ∧
      (∀ s, A + 1 ≤ |s| → U s = 0) := by
  let b : ContDiffBump (0 : ℝ) := ⟨A + 1 / 2, A + 1, by linarith, by linarith⟩
  let U : ℝ → ℂ := fun s => (b s : ℂ)
  have hs (s : ℝ) (h : U s ≠ 0) : |s| < A + 1 := by
    have hb : s ∈ Function.support b := by
      intro hz
      exact h (by simp only [U, hz, Complex.ofReal_zero])
    rw [b.support_eq] at hb
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using hb
  have hsupport : Function.support U ⊆ Set.Icc (-(A + 1)) (A + 1) :=
    fun s hsU => abs_le.mp (hs s hsU).le
  refine ⟨U, HasCompactSupport.of_support_subset_isCompact isCompact_Icc hsupport,
    Complex.ofRealCLM.contDiff.comp b.contDiff, ?_, closure_minimal hsupport isClosed_Icc, ?_⟩
  · intro s hsA
    have hb : s ∈ Metric.closedBall (0 : ℝ) b.rIn := by
      change dist s 0 ≤ A + 1 / 2
      rw [Real.dist_eq, sub_zero]
      linarith
    simp only [U, b.one_of_mem_closedBall hb, Complex.ofReal_one]
  · intro s hsA
    by_contra h
    exact (not_lt_of_ge hsA) (hs s h)

end JointLogSeparation

namespace JointLogSeparation
open SecondPassArithmetic MeasureTheory
open scoped Classical SchwartzMap FourierTransform

lemma density_weight_identity (J : ℕ) (t : ℝ) :
    firstLogDensity J t * (1 + ‖t‖) ^ J = firstLogDensity 0 t := by
  have ht : 1 + ‖t‖ ≠ 0 := ne_of_gt (by positivity)
  simp only [firstLogDensity, zero_add, pow_add, mul_inv_rev]
  field_simp

def tripleLogDensity (J : ℕ) (t : Frequency) : ℝ :=
  firstLogDensity J t.1 * (firstLogDensity J t.2.1 * firstLogDensity J t.2.2)

lemma tripleLogDensity_integrable (J : ℕ) : Integrable (tripleLogDensity J) :=
  (firstLogDensity_integrable J).mul_prod
    ((firstLogDensity_integrable J).mul_prod (firstLogDensity_integrable J))

lemma tripleLogDensity_nonneg (J : ℕ) (t : Frequency) : 0 ≤ tripleLogDensity J t :=
  mul_nonneg (firstLogDensity_nonneg _ _) (mul_nonneg
    (firstLogDensity_nonneg _ _) (firstLogDensity_nonneg _ _))

lemma tripleLogDensity_bounded_integrable (J : ℕ) (G : Frequency → ℝ)
    (hG : Continuous G) (M : ℝ) (hM : ∀ t, ‖G t‖ ≤ M) :
    Integrable (fun t => tripleLogDensity J t * G t) :=
  (tripleLogDensity_integrable J).mul_bdd hG.aestronglyMeasurable
    (Filter.Eventually.of_forall hM)

lemma tripleLogDensity_slice_integrable (J : ℕ) (G : Frequency → ℝ)
    (hG : Continuous G) (M : ℝ) (hM : ∀ t, ‖G t‖ ≤ M) (x : ℝ) :
    Integrable (fun yz : ℝ × ℝ => tripleLogDensity J (x,yz) * G (x,yz)) := by
  have hc : Integrable (fun yz : ℝ × ℝ =>
      firstLogDensity J x * (firstLogDensity J yz.1 * firstLogDensity J yz.2)) :=
    ((firstLogDensity_integrable J).mul_prod (firstLogDensity_integrable J)).const_mul _
  apply hc.mul_bdd
  · exact (hG.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun t => hM (x,t))

theorem triple_coefficient_density_bound (b₁ b₂ b₃ : 𝓢(ℝ, ℂ)) (J : ℕ)
    (G : Frequency → ℝ) (hG : Continuous G) (hG0 : ∀ t, 0 ≤ G t)
    (M : ℝ) (hM : ∀ t, G t ≤ M) (S C : ℝ)
    (hpoint : ∀ t₁ t₂ t₃ : ℝ,
      S * ‖b₁ t₁*b₂ t₂*b₃ t₃‖ ≤
        C * firstLogDensity J t₁ * firstLogDensity J t₂ * firstLogDensity J t₃) :
    S * (∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ,
      ‖tripleCoefficient b₁ b₂ b₃ (t₁,t₂,t₃)‖ * G (t₁,t₂,t₃)) ≤
    C * (∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ,
      tripleLogDensity J (t₁,t₂,t₃) * G (t₁,t₂,t₃)) := by
  have hGb : ∀ t, ‖G t‖ ≤ M := fun t => by
    simpa only [Real.norm_of_nonneg (hG0 t)] using hM t
  have hc := tripleCoefficient_norm_bounded_integrable b₁ b₂ b₃ G hG M hGb
  have hd := tripleLogDensity_bounded_integrable J G hG M hGb
  rw [nested_eq_integral _ hc (tripleCoefficient_norm_slice_integrable b₁ b₂ b₃ G hG M hGb),
    nested_eq_integral _ hd (tripleLogDensity_slice_integrable J G hG M hGb),
    ← integral_const_mul, ← integral_const_mul]
  apply integral_mono (hc.const_mul S) (hd.const_mul C)
  intro t
  have hh := mul_le_mul_of_nonneg_right (hpoint t.1 t.2.1 t.2.2) (hG0 t)
  simpa only [tripleCoefficient, tripleLogDensity, mul_assoc] using hh

end JointLogSeparation

namespace JointLogSeparation
open SecondPassArithmetic MeasureTheory
open scoped Classical SchwartzMap FourierTransform

lemma one_add_norm_sub_le (x y : ℝ) :
    1 + ‖x-y‖ ≤ (1+‖x‖)*(1+‖y‖) := by
  have hn := norm_sub_le x y
  have hprod := mul_nonneg (norm_nonneg x) (norm_nonneg y)
  nlinarith

theorem difference_height_weight_le (x y z : ℝ) (J : ℕ) :
    (1+‖x-z‖)^J * (1+‖y-z‖)^J ≤
      (1+‖x‖)^(2*J) * (1+‖y‖)^(2*J) * (1+‖z‖)^(2*J) := by
  have hx := pow_le_pow_left₀ (by positivity : 0 ≤ 1+‖x-z‖) (one_add_norm_sub_le x z) J
  have hy := pow_le_pow_left₀ (by positivity : 0 ≤ 1+‖y-z‖) (one_add_norm_sub_le y z) J
  calc
    _ ≤ ((1+‖x‖)*(1+‖z‖))^J * ((1+‖y‖)*(1+‖z‖))^J :=
      mul_le_mul hx hy (by positivity) (by positivity)
    _ = (1+‖x‖)^J * (1+‖y‖)^J * (1+‖z‖)^(2*J) := by
      rw [mul_pow, mul_pow, two_mul, pow_add]
      ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_mul
        (pow_le_pow_right₀ (by linarith [norm_nonneg x] : 1 ≤ 1+‖x‖) (by omega : J ≤ 2*J))
        (pow_le_pow_right₀ (by linarith [norm_nonneg y] : 1 ≤ 1+‖y‖) (by omega : J ≤ 2*J))
        (by positivity) (by positivity)

theorem triple_density_polynomial_bound (G : Frequency → ℝ)
    (hG : Continuous G) (hG0 : ∀ t, 0 ≤ G t) (M : ℝ) (hM : ∀ t, G t ≤ M)
    (J : ℕ) (D : ℝ)
    (hbound : ∀ t, G t ≤ D * (1+‖t.1‖)^J * (1+‖t.2.1‖)^J * (1+‖t.2.2‖)^J) :
    (∫ x : ℝ, ∫ y : ℝ, ∫ z : ℝ, tripleLogDensity J (x,y,z) * G (x,y,z)) ≤
      D * (∫ t : ℝ, firstLogDensity 0 t)^3 := by
  have hGb : ∀ t, ‖G t‖ ≤ M := fun t => by
    simpa only [Real.norm_of_nonneg (hG0 t)] using hM t
  have hi := tripleLogDensity_bounded_integrable J G hG M hGb
  rw [nested_eq_integral _ hi (tripleLogDensity_slice_integrable J G hG M hGb)]
  have hh : ∀ t : Frequency, tripleLogDensity J t * G t ≤ D * tripleLogDensity 0 t := by
    intro t
    calc
      _ ≤ tripleLogDensity J t *
          (D * (1+‖t.1‖)^J * (1+‖t.2.1‖)^J * (1+‖t.2.2‖)^J) :=
        mul_le_mul_of_nonneg_left (hbound t) (tripleLogDensity_nonneg J t)
      _ = _ := by
        dsimp only [tripleLogDensity]
        rw [← density_weight_identity J t.1, ← density_weight_identity J t.2.1,
          ← density_weight_identity J t.2.2]
        ring
  calc
    _ ≤ ∫ t : Frequency, D * tripleLogDensity 0 t :=
      integral_mono hi ((tripleLogDensity_integrable 0).const_mul D) hh
    _ = D * (∫ t : Frequency, tripleLogDensity 0 t) := integral_const_mul _ _
    _ = _ := by
      have hslice (x : ℝ) : Integrable (fun yz : ℝ × ℝ => tripleLogDensity 0 (x,yz)) := by
        simpa only [tripleLogDensity, Measure.volume_eq_prod] using
          ((firstLogDensity_integrable 0).mul_prod (firstLogDensity_integrable 0)).const_mul
            (firstLogDensity 0 x)
      rw [← nested_eq_integral _ (tripleLogDensity_integrable 0) hslice]
      simp only [tripleLogDensity, integral_const_mul, integral_mul_const]
      ring

end JointLogSeparation

namespace JointLogSeparation
lemma kernelLogPhase_conjugate (t x : ℝ) : star (kernelLogPhase t x) = kernelLogPhase (-t) x := by
  unfold kernelLogPhase
  simp only [Complex.star_def, ← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I]
  congr 1
  push_cast
  ring
end JointLogSeparation

namespace DescentWeightedCauchy
open Eisenstein
open scoped Classical

/-- The first dual dilation records the square of the divisor generator. -/
def firstElementRowMap (q : O) (x : Ideal O × O) : O :=
  x.2 * cubicIdealGenerator x.1 ^ 2 * q

theorem firstElementRowMap_fiber_card (s : Finset (Ideal O × O)) (q z : O) (hz : z ≠ 0) :
    (s.filter (fun x => firstElementRowMap q x = z)).card ≤
      (idealDivisors (Ideal.span {z})).card := by
  have hspan : (Ideal.span {z} : Ideal O) ≠ 0 := by
    intro he
    have hm : z ∈ (Ideal.span {z} : Ideal O) := Ideal.subset_span (by simp)
    rw [he] at hm
    exact hz hm
  let A := s.filter (fun x => firstElementRowMap q x = z)
  let encode (x : A) : idealDivisors (Ideal.span {z}) := ⟨x.val.1, by
    have he := (Finset.mem_filter.mp x.property).2
    apply (mem_idealDivisors hspan).mpr
    rw [← he, firstElementRowMap]
    have hd : cubicIdealGenerator x.val.1 ∣ x.val.2 * cubicIdealGenerator x.val.1 ^ 2 * q := by
      refine ⟨x.val.2 * cubicIdealGenerator x.val.1 * q, ?_⟩
      ring
    simpa only [span_cubicIdealGenerator] using SecondPassArithmetic.span_dvd_of_element_dvd hd⟩
  have hinj : Function.Injective encode := by
    intro x y he
    have hxy : x.val.1 = y.val.1 := congrArg Subtype.val he
    have hxz := (Finset.mem_filter.mp x.property).2
    have hyz := (Finset.mem_filter.mp y.property).2
    have hq : q ≠ 0 := by intro h; simp [firstElementRowMap, h] at hxz; exact hz hxz.symm
    have hg : cubicIdealGenerator x.val.1 ≠ 0 := by
      intro h
      simp [firstElementRowMap, h] at hxz
      exact hz hxz.symm
    apply Subtype.ext
    apply Prod.ext hxy
    have heq : x.val.2 * (cubicIdealGenerator x.val.1 ^ 2 * q) =
        y.val.2 * (cubicIdealGenerator x.val.1 ^ 2 * q) := by
      simpa only [firstElementRowMap, ← hxy, mul_assoc] using hxz.trans hyz.symm
    exact mul_right_cancel₀ (mul_ne_zero (pow_ne_zero 2 hg) hq) heq
  simpa only [Fintype.card_coe] using Fintype.card_le_of_injective encode hinj

theorem first_element_energy_small_power (δ : ℝ) (hδ : 0 < δ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (s : Finset (Ideal O × O)) (T : Finset O) (q : O)
      (w : Ideal O × O → ℂ) (P : O → ℂ) (M Y : ℝ),
      0 ≤ M → (∀ x ∈ s, firstElementRowMap q x ∈ T) →
      (∀ z ∈ T, z ≠ 0) → (∀ z ∈ T, (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ Y) →
      (∀ x ∈ s, ‖w x‖ ≤ M) →
      (∑ x ∈ s, ‖w x‖ * ‖P (firstElementRowMap q x)‖ ^ 2) ≤
        M * K * Y ^ δ * ∑ z ∈ T, ‖P z‖ ^ 2 := by
  obtain ⟨K, hK, hdiv⟩ := IdealDivisorBound.ideal_divisor_small_power δ hδ
  refine ⟨K, hK, ?_⟩
  intro s T q w P M Y hM hmap hT hnorm hw
  apply (bounded_energy_pushforward s T (firstElementRowMap q) w P M hmap hw).trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro z hz
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  have hz0 : (Ideal.span {z} : Ideal O) ≠ 0 := by
    intro he
    have hm : z ∈ (Ideal.span {z} : Ideal O) := Ideal.subset_span (by simp)
    rw [he] at hm
    exact hT z hz hm
  have hb : ((s.filter (fun x => firstElementRowMap q x = z)).card : ℝ) ≤ K * Y ^ δ := by
    calc
      _ ≤ ((idealDivisors (Ideal.span {z})).card : ℝ) := by
        exact_mod_cast firstElementRowMap_fiber_card s q z (hT z hz)
      _ ≤ K * (Ideal.absNorm (Ideal.span {z}) : ℝ) ^ δ := hdiv _ hz0
      _ ≤ K * Y ^ δ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (Nat.cast_nonneg _) (hnorm z hz) hδ.le) hK.le
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hb hM

end DescentWeightedCauchy

namespace JointLogSeparation
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic MeasureTheory
open scoped Classical SchwartzMap FourierTransform ContDiff

theorem joint_twisted_separation_envelope {ι : Type*} [Fintype ι]
    (A₁ A₂ W : 𝓢(ℝ, ℂ)) (V : ι → ℝ → ℂ) (a₁ a₂ a₃ M : ι → ℝ)
    (hM : ∀ j, 0 ≤ M j) (hV : ∀ j x, V j x ≠ 0 → |x| ≤ M j) (A J : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ θ₁ θ₂ R : ℝ, 0 < R → ∃ b : 𝓢(ℝ, ℂ),
      (∀ y : ι → ℝ,
        (∏ j, V j (y j)) * (frequencyTwist A₁ θ₁) (∑ j, a₁ j * y j) * (frequencyTwist A₂ θ₂) (∑ j, a₂ j * y j) *
          paperRadialFourier W (R * Real.exp (∑ j, a₃ j * y j)) =
        ∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ,
          (∏ j, V j (y j)) * kernelLogPhase t₁ (∑ j, a₁ j * y j) *
            kernelLogPhase t₂ (∑ j, a₂ j * y j) * kernelLogPhase t₃ (∑ j, a₃ j * y j) *
            ((𝓕 (frequencyTwist A₁ θ₁)) t₁ * (𝓕 (frequencyTwist A₂ θ₂)) t₂ * b t₃)) ∧
      (∀ t₁ t₂ t₃ : ℝ, (1 + R) ^ A * ‖(𝓕 (frequencyTwist A₁ θ₁)) t₁ * (𝓕 (frequencyTwist A₂ θ₂)) t₂ * b t₃‖ ≤
        (C * (1+‖θ₁‖)^(J+2) * (1+‖θ₂‖)^(J+2)) * firstLogDensity J t₁ * firstLogDensity J t₂ * firstLogDensity J t₃) ∧
      Integrable (fun t : ℝ => (1 + ‖t‖) ^ J * ‖b t‖) := by
  classical
  obtain ⟨C₃, hC₃, hsep⟩ := paperRadialFourier_log_separation_envelope
    V a₃ M hM hV W A (J + 2)
  let C₁ := fourierPointBound (J + 2) (twistSourceBound A₁ (J + 2))
  let C₂ := fourierPointBound (J + 2) (twistSourceBound A₂ (J + 2))
  have hC₁ : 0 ≤ C₁ := fourierPointBound_nonneg _ _ (twistSourceBound_nonneg _ _)
  have hC₂ : 0 ≤ C₂ := fourierPointBound_nonneg _ _ (twistSourceBound_nonneg _ _)
  refine ⟨C₁ * C₂ * C₃, by positivity, ?_⟩
  intro θ₁ θ₂ R hR
  obtain ⟨b, hb, hweighted, _, hpoint⟩ := hsep R hR
  refine ⟨b, ?_, ?_, ?_⟩
  · intro y
    let P : ℂ := ∏ j, V j (y j)
    let s₁ : ℝ := ∑ j, a₁ j * y j
    let s₂ : ℝ := ∑ j, a₂ j * y j
    let s₃ : ℝ := ∑ j, a₃ j * y j
    have hr : P * paperRadialFourier W (R * Real.exp s₃) =
        ∫ t, P * kernelLogPhase t s₃ * b t := by
      have hh := hb y
      simpa only [Finset.prod_mul_distrib, ← kernelLogPhase_sum, P, s₃] using hh
    exact joint_separation_identity (frequencyTwist A₁ θ₁) (frequencyTwist A₂ θ₂) b P
      (paperRadialFourier W (R * Real.exp s₃)) s₁ s₂ s₃ hr
  · intro t₁ t₂ t₃
    have hb₃ : (1 + R) ^ A * ‖b t₃‖ ≤ C₃ * firstLogDensity J t₃ := by
      rw [firstLogDensity, ← div_eq_mul_inv]
      apply (le_div_iff₀ (pow_pos (by positivity : 0 < 1 + ‖t₃‖) (J + 2))).mpr
      simpa only [Real.norm_eq_abs, mul_comm, mul_left_comm, mul_assoc] using hpoint t₃
    have h₁ := twisted_profile_fourier_envelope A₁ θ₁ t₁ J
    have h₂ := twisted_profile_fourier_envelope A₂ θ₂ t₂ J
    simp only [norm_mul]
    calc
      _ = ‖(𝓕 (frequencyTwist A₁ θ₁)) t₁‖ * ‖(𝓕 (frequencyTwist A₂ θ₂)) t₂‖ * ((1 + R)^A * ‖b t₃‖) := by ring
      _ ≤ (C₁ * (1+‖θ₁‖)^(J+2) * firstLogDensity J t₁) * (C₂ * (1+‖θ₂‖)^(J+2) * firstLogDensity J t₂) * (C₃ * firstLogDensity J t₃) := by
        exact mul_le_mul (mul_le_mul h₁ h₂ (norm_nonneg _)
          (mul_nonneg (mul_nonneg hC₁ (by positivity)) (firstLogDensity_nonneg _ _))) hb₃
          (by positivity)
          (mul_nonneg (mul_nonneg (mul_nonneg hC₁ (by positivity)) (firstLogDensity_nonneg _ _))
            (mul_nonneg (mul_nonneg hC₂ (by positivity)) (firstLogDensity_nonneg _ _)))
      _ = _ := by ring
  · apply hweighted.mono'
    · exact (by fun_prop : Continuous (fun t : ℝ => (1 + ‖t‖) ^ J * ‖b t‖)).aestronglyMeasurable
    · filter_upwards [] with t
      rw [Real.norm_of_nonneg (by positivity)]
      rw [←Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ (by linarith [norm_nonneg t]) (Nat.le_add_right J 2)) (norm_nonneg _)

theorem seven_twisted_kernel_separation (A₁ A₂ W : 𝓢(ℝ, ℂ))
    (V : Fin 7 → ℝ → ℂ) (M : Fin 7 → ℝ) (hM : ∀ j, 0 ≤ M j)
    (hV : ∀ j x, V j x ≠ 0 → |x| ≤ M j) (A J : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ θ₁ θ₂ R : ℝ, 0 < R → ∃ b : 𝓢(ℝ, ℂ),
      (∀ z ud ue uv kap x₁ x₂ : ℝ,
        outerWindow V z ud ue uv kap * V 5 x₁ * V 6 x₂ * (frequencyTwist A₁ θ₁) (z + x₁) * (frequencyTwist A₂ θ₂) (z + x₂) *
          paperRadialFourier W
            (R * Real.exp (kap - ud - 2 * ue - 2 * uv - x₁ - x₂)) =
        ∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ,
          outerWindow V z ud ue uv kap * kernelLogPhase (t₁ + t₂) z *
            kernelLogPhase t₃ (kap - ud - 2 * ue - 2 * uv) *
            fixedColumnTest (V 5) (t₁ - t₃) x₁ * fixedColumnTest (V 6) (t₂ - t₃) x₂ *
            ((𝓕 (frequencyTwist A₁ θ₁)) t₁ * (𝓕 (frequencyTwist A₂ θ₂)) t₂ * b t₃)) ∧
      (∀ t₁ t₂ t₃ : ℝ, (1 + R) ^ A * ‖(𝓕 (frequencyTwist A₁ θ₁)) t₁ * (𝓕 (frequencyTwist A₂ θ₂)) t₂ * b t₃‖ ≤
        (C * (1+‖θ₁‖)^(J+2) * (1+‖θ₂‖)^(J+2)) * firstLogDensity J t₁ * firstLogDensity J t₂ * firstLogDensity J t₃) ∧
      Integrable (fun t : ℝ => (1 + ‖t‖) ^ J * ‖b t‖) := by
  let a₁ : Fin 7 → ℝ := ![1, 0, 0, 0, 0, 1, 0]
  let a₂ : Fin 7 → ℝ := ![1, 0, 0, 0, 0, 0, 1]
  let a₃ : Fin 7 → ℝ := ![0, -1, -2, -2, 1, -1, -1]
  obtain ⟨C, hC, hsep⟩ := joint_twisted_separation_envelope A₁ A₂ W V a₁ a₂ a₃ M hM hV A J
  refine ⟨C, hC, ?_⟩
  intro θ₁ θ₂ R hR
  obtain ⟨b, hb, hpoint, hint⟩ := hsep θ₁ θ₂ R hR
  refine ⟨b, ?_, hpoint, hint⟩
  intro z ud ue uv kap x₁ x₂
  let y : Fin 7 → ℝ := ![z, ud, ue, uv, kap, x₁, x₂]
  have h₁ : (∑ j, a₁ j * y j) = z + x₁ := by
    simp [a₁, y, Fin.sum_univ_succ]
  have h₂ : (∑ j, a₂ j * y j) = z + x₂ := by
    simp [a₂, y, Fin.sum_univ_succ]
  have h₃ : (∑ j, a₃ j * y j) = kap - ud - 2 * ue - 2 * uv - x₁ - x₂ := by
    simp [a₃, y, Fin.sum_univ_succ]
    ring
  have hp : (∏ j, V j (y j)) = outerWindow V z ud ue uv kap * V 5 x₁ * V 6 x₂ := by
    simp [outerWindow, y, Fin.prod_univ_succ, mul_assoc]
  have h := hb y
  rw [h₁, h₂, h₃, hp] at h
  rw [h]
  apply integral_congr_ae
  filter_upwards [] with t₁
  apply integral_congr_ae
  filter_upwards [] with t₂
  apply integral_congr_ae
  filter_upwards [] with t₃
  have heq := seven_phase_factor z ud ue uv kap x₁ x₂ t₁ t₂ t₃
  unfold fixedColumnTest
  calc
    _ = (outerWindow V z ud ue uv kap * V 5 x₁ * V 6 x₂) *
      (kernelLogPhase t₁ (z + x₁) * kernelLogPhase t₂ (z + x₂) *
      kernelLogPhase t₃ (kap - ud - 2 * ue - 2 * uv - x₁ - x₂)) *
      ((𝓕 (frequencyTwist A₁ θ₁)) t₁ * (𝓕 (frequencyTwist A₂ θ₂)) t₂ * b t₃) := by ring
    _ = _ := by rw [heq]; ring

end JointLogSeparation

namespace JointLogSeparation
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic
open scoped Classical

theorem outerWindow_global_bound (windows : Fin 7 → ℝ → ℂ)
    (hc : ∀ j, HasCompactSupport (windows j)) (hs : ∀ j, Continuous (windows j)) :
    ∃ Cw : ℝ, 0 ≤ Cw ∧ ∀ z ud ue uv kap : ℝ, ‖outerWindow windows z ud ue uv kap‖ ≤ Cw := by
  have hb (j : Fin 7) : ∃ B : ℝ, 0 ≤ B ∧ ∀ x : ℝ, ‖windows j x‖ ≤ B := by
    obtain ⟨B,hB⟩ := ((hc j).isCompact_range (hs j)).bddAbove_image continuous_norm.continuousOn
    have he (x : ℝ) : ‖windows j x‖ ≤ B := hB ⟨windows j x, ⟨x,rfl⟩,rfl⟩
    exact ⟨B,(norm_nonneg _).trans (he 0),he⟩
  choose B hB hbound using hb
  have h0 := hB 0
  have h1 := hB 1
  have h2 := hB 2
  have h3 := hB 3
  have h4 := hB 4
  refine ⟨B 0 * B 1 * B 2 * B 3 * B 4, by positivity, ?_⟩
  intro z ud ue uv kap
  simp only [outerWindow, norm_mul]
  gcongr
  all_goals first | positivity | apply hbound

end JointLogSeparation

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
