import GaloisForLFunctions.RHTower.LandauHeightKreinPinning
import GaloisForLFunctions.RHTower.HodgeZetaFlatnessLaw

/-!
# Resolvent-divided tilted kernels and bumped tests

The tilted kernel `Φ_θ(u) = Φ(u + iθ)` decays double-exponentially, so it is integrable against
every exponential weight (`superExpDecay_tiltedRiemannKernel`), with explicit weighted tails
(`expTail_tiltedPhi_le_of_rate`).  At an on-line zero `ρ₀ = 1/2 + iγ₀` of multiplicity `m₀` its transform
factors as `(z - γ₀)^{m₀} v(z)` with `v` analytic and `v(γ₀) ≠ 0`
(`exists_tiltedPhi_local_factor`), so the iterated resolvent division `D_{γ₀}^{m₀} Φ_θ` is a
super-exponentially decaying kernel whose transform vanishes at every zero except `γ₀`.

Truncating a kernel to `[-U, U]` and smoothing with the polar-free bump at radius `w` gives a
Hodge-class test at level `U + w` (`bumpedTest`).  The plain bump `κ₂` is itself a Hodge-class test
with `‖W(κ₂, κ₂)‖ ≤ B_w² (1+|ω|)⁴ · 24 A₀ log(|ω|+3)` (`norm_W_scaledBumpPolarFree_le`).
-/

open Complex MeasureTheory Filter Topology Set
open scoped Real
open Bottcher Zeta23

namespace RHTower

noncomputable section

/-! ## Monotonicity of the double-exponential profile -/

/-- For `a ≤ 2κ e^{2U}` and `v ≥ U`: `a v - κ e^{2v} ≤ a U - κ e^{2U}`. -/
theorem lin_sub_rate_le {a κ U v : ℝ} (hκ : 0 ≤ κ) (ha : a ≤ 2 * κ * Real.exp (2 * U))
    (hv : U ≤ v) :
    a * v - κ * Real.exp (2 * v) ≤ a * U - κ * Real.exp (2 * U) := by
  have hexp : Real.exp (2 * U) * (1 + 2 * (v - U)) ≤ Real.exp (2 * v) := by
    have h := Real.add_one_le_exp (2 * (v - U))
    have e : Real.exp (2 * v) = Real.exp (2 * U) * Real.exp (2 * (v - U)) := by
      rw [← Real.exp_add]; ring_nf
    rw [e]
    exact mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos _).le
  have h1 : κ * (Real.exp (2 * U) * (1 + 2 * (v - U))) ≤ κ * Real.exp (2 * v) :=
    mul_le_mul_of_nonneg_left hexp hκ
  have h2 : a * (v - U) ≤ 2 * κ * Real.exp (2 * U) * (v - U) :=
    mul_le_mul_of_nonneg_right ha (by linarith)
  nlinarith

/-- `e^{2x} ≥ 2x²` for `x ≥ 0`. -/
theorem two_mul_sq_le_exp_two_mul {x : ℝ} (hx : 0 ≤ x) : 2 * x ^ 2 ≤ Real.exp (2 * x) := by
  have := Real.sum_le_exp_of_nonneg (x := 2 * x) (by linarith) 3
  simp [Finset.sum_range_succ, Nat.factorial] at this
  nlinarith

/-! ## Super-exponential decay of the tilted kernel -/

theorem superExpDecay_tiltedRiemannKernel {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : 2 * θ < π / 2) :
    SuperExpDecay (tiltedPhi θ) := by
  have hθ4 : |θ| < π / 4 := by rw [abs_of_nonneg hθ0]; linarith
  refine ⟨continuous_tiltedPhi hθ4, fun c => ?_⟩
  obtain ⟨C, hC, hb⟩ := exists_norm_tiltedPhi_le hθ0 hθ
  set κ := π * Real.cos (2 * θ) with hκ
  have hcos : 0 < Real.cos (2 * θ) := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hθ⟩
  have hκ0 : 0 < κ := by rw [hκ]; have := Real.pi_pos; positivity
  set X := 1 + (|c| + 7) / (2 * κ) with hX
  have hX1 : 1 ≤ X := by rw [hX]; have : 0 ≤ (|c| + 7) / (2 * κ) := by positivity
                         linarith
  have hM := tiltedPhiTailConst_nonneg
  set K := C * Real.exp (|c| * X) + tiltedPhiTailConst with hK
  refine Integrable.mono' ((integrable_exp_neg_abs).const_mul K)
    (((continuous_tiltedPhi hθ4).norm.mul (by fun_prop)).aestronglyMeasurable)
    (Eventually.of_forall fun u => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hcu : c * |u| ≤ |c| * |u| := mul_le_mul_of_nonneg_right (le_abs_self c) (abs_nonneg u)
  rcases le_or_gt |u| X with hu | hu
  · have h1 := hb u
    calc ‖tiltedPhi θ u‖ * Real.exp (c * |u|) ≤ C * Real.exp (-|u|) * Real.exp (|c| * X) :=
          mul_le_mul h1 (Real.exp_le_exp.mpr (hcu.trans
            (mul_le_mul_of_nonneg_left hu (abs_nonneg c)))) (Real.exp_pos _).le (by positivity)
      _ ≤ K * Real.exp (-|u|) := by
          have : 0 ≤ tiltedPhiTailConst * Real.exp (-|u|) := by positivity
          rw [hK, add_mul]; nlinarith [Real.exp_pos (-|u|), Real.exp_pos (|c| * X)]
  · have hu0 : 0 ≤ |u| := abs_nonneg u
    have hquad : (|c| + 7) * |u| ≤ κ * Real.exp (2 * |u|) := by
      have h2 := two_mul_sq_le_exp_two_mul hu0
      have hk : |c| + 7 ≤ 2 * κ * |u| := by
        have : (|c| + 7) / (2 * κ) ≤ |u| := by linarith
        rwa [div_le_iff₀ (by positivity), mul_comm] at this
      nlinarith [mul_le_mul_of_nonneg_left h2 hκ0.le]
    have hrate : 1 ≤ π * Real.cos (2 * θ) * Real.exp (2 * |u|) := by
      rw [← hκ]; nlinarith [abs_nonneg c]
    have hbd := norm_tiltedPhi_le_of_rate hθ0 hθ hrate
    rw [← hκ] at hbd
    calc ‖tiltedPhi θ u‖ * Real.exp (c * |u|)
        ≤ tiltedPhiTailConst * Real.exp (9 / 2 * |u|) * Real.exp (-(κ * Real.exp (2 * |u|))) *
            Real.exp (|c| * |u|) :=
          mul_le_mul hbd (Real.exp_le_exp.mpr hcu) (Real.exp_pos _).le (by positivity)
      _ = tiltedPhiTailConst * Real.exp (9 / 2 * |u| - κ * Real.exp (2 * |u|) + |c| * |u|) := by
          rw [mul_assoc, mul_assoc, ← Real.exp_add, ← Real.exp_add]; ring_nf
      _ ≤ tiltedPhiTailConst * Real.exp (-|u|) := by
          gcongr; nlinarith
      _ ≤ K * Real.exp (-|u|) := by
          have : 0 ≤ C * Real.exp (|c| * X) * Real.exp (-|u|) := by positivity
          rw [hK, add_mul]; linarith

/-- **Weighted tails of the tilted kernel.**  With `κ = π cos(2θ)`, if `κ e^{2X} ≥ 1` and
`2κ e^{2X} ≥ 11/2 + b`, then `expTail Φ_θ b X ≤ 2M e^{(11/2+b)X} e^{-κ e^{2X}}`. -/
theorem expTail_tiltedPhi_le_of_rate {θ b X : ℝ} (hθ0 : 0 ≤ θ) (hθ : 2 * θ < π / 2)
    (hrate : 1 ≤ π * Real.cos (2 * θ) * Real.exp (2 * X))
    (hslope : 11 / 2 + b ≤ 2 * (π * Real.cos (2 * θ)) * Real.exp (2 * X)) :
    expTail (tiltedPhi θ) b X ≤
      2 * tiltedPhiTailConst * Real.exp ((11 / 2 + b) * X) *
        Real.exp (-(π * Real.cos (2 * θ) * Real.exp (2 * X))) := by
  have hθ4 : |θ| < π / 4 := by rw [abs_of_nonneg hθ0]; linarith
  set κ := π * Real.cos (2 * θ) with hκ
  have hcos : 0 < Real.cos (2 * θ) := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hθ⟩
  have hκ0 : 0 < κ := by rw [hκ]; have := Real.pi_pos; positivity
  have hM := tiltedPhiTailConst_nonneg
  set K := tiltedPhiTailConst * Real.exp ((11 / 2 + b) * X - κ * Real.exp (2 * X)) with hK
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  have hpt : ∀ u : ℝ, {u : ℝ | X ≤ |u|}.indicator
      (fun u => ‖tiltedPhi θ u‖ * Real.exp (b * |u|)) u ≤ K * Real.exp (-|u|) := by
    intro u
    simp only [indicator, mem_setOf_eq]
    split_ifs with h
    · have hr : 1 ≤ π * Real.cos (2 * θ) * Real.exp (2 * |u|) := by
        have : Real.exp (2 * X) ≤ Real.exp (2 * |u|) := Real.exp_le_exp.mpr (by linarith)
        show 1 ≤ κ * Real.exp (2 * |u|)
        calc (1 : ℝ) ≤ κ * Real.exp (2 * X) := hrate
          _ ≤ κ * Real.exp (2 * |u|) := mul_le_mul_of_nonneg_left this hκ0.le
      have hbd := norm_tiltedPhi_le_of_rate hθ0 hθ hr
      rw [← hκ] at hbd
      have hmono := lin_sub_rate_le (a := 11 / 2 + b) hκ0.le hslope h
      calc ‖tiltedPhi θ u‖ * Real.exp (b * |u|)
          ≤ tiltedPhiTailConst * Real.exp (9 / 2 * |u|) * Real.exp (-(κ * Real.exp (2 * |u|))) *
              Real.exp (b * |u|) := mul_le_mul_of_nonneg_right hbd (Real.exp_pos _).le
        _ = tiltedPhiTailConst * Real.exp ((11 / 2 + b) * |u| - κ * Real.exp (2 * |u|)) *
              Real.exp (-|u|) := by
            have e1 : Real.exp (9 / 2 * |u|) * Real.exp (-(κ * Real.exp (2 * |u|))) *
                Real.exp (b * |u|) =
                Real.exp ((11 / 2 + b) * |u| - κ * Real.exp (2 * |u|)) * Real.exp (-|u|) := by
              rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
            calc tiltedPhiTailConst * Real.exp (9 / 2 * |u|) *
                  Real.exp (-(κ * Real.exp (2 * |u|))) * Real.exp (b * |u|)
                = tiltedPhiTailConst * (Real.exp (9 / 2 * |u|) *
                    Real.exp (-(κ * Real.exp (2 * |u|))) * Real.exp (b * |u|)) := by ring
              _ = _ := by rw [e1]; ring
        _ ≤ K * Real.exp (-|u|) := by
            rw [hK]; gcongr
    · positivity
  have hint : Integrable (fun u : ℝ => K * Real.exp (-|u|)) := integrable_exp_neg_abs.const_mul K
  have hle := integral_mono_of_nonneg (Eventually.of_forall fun u => by
    simp only [indicator]; split_ifs <;> positivity) hint (Eventually.of_forall hpt)
  unfold expTail
  refine hle.trans (le_of_eq ?_)
  rw [integral_const_mul, integral_exp_neg_abs, hK, sub_eq_add_neg, Real.exp_add]; ring

/-! ## The local factor at an on-line zero -/

/-- At a nontrivial zero, `ζ(s) = (s - ρ₀)^{m₀} u(s)` near `ρ₀` with `u` analytic and
`u(ρ₀) ≠ 0`, where `m₀` is the multiplicity. -/
theorem exists_zeta_local_factor {ρ₀ : ℂ} (hρ₀ : ρ₀ ∈ zetaZeroConfig.carrier) :
    ∃ u : ℂ → ℂ, AnalyticAt ℂ u ρ₀ ∧ u ρ₀ ≠ 0 ∧
      ∀ᶠ s in 𝓝 ρ₀, riemannZeta s = (s - ρ₀) ^ (zetaZeroConfig.mult ρ₀) * u s := by
  have hnt : IsNontrivialZero ρ₀ := hρ₀
  have hρ1 : ρ₀ ≠ 1 := fun h => by have := hnt.2.2; rw [h] at this; simp at this
  have han : AnalyticAt ℂ riemannZeta ρ₀ := by
    have hopen : IsOpen {s : ℂ | s ≠ 1} := isOpen_ne
    have hd : DifferentiableOn ℂ riemannZeta {s : ℂ | s ≠ 1} :=
      fun s hs => (differentiableAt_riemannZeta hs).differentiableWithinAt
    exact hd.analyticAt (hopen.mem_nhds hρ1)
  have hm1 : 1 ≤ zetaZeroConfig.mult ρ₀ := zetaZeroConfig.one_le_mult ρ₀ hρ₀
  have hmult : zetaZeroConfig.mult ρ₀ = (analyticOrderAt riemannZeta ρ₀).toNat := rfl
  have htop : analyticOrderAt riemannZeta ρ₀ ≠ ⊤ := by
    intro h; rw [hmult, h] at hm1; simp at hm1
  have hord : analyticOrderAt riemannZeta ρ₀ = (zetaZeroConfig.mult ρ₀ : ℕ∞) := by
    rw [hmult, ENat.coe_toNat htop]
  obtain ⟨u, hu, hu0, hev⟩ := (han.analyticOrderAt_eq_natCast).mp hord
  exact ⟨u, hu, hu0, hev.mono fun s hs => by rw [hs, smul_eq_mul]⟩

/-- **The local factor of the tilted kernel at an on-line zero.**  For `ρ₀ = 1/2 + iγ₀` of
multiplicity `m₀`: `Φ̂_θ(z) = (z - γ₀)^{m₀} v(z)` near `γ₀`, `v` analytic, `v(γ₀) ≠ 0`. -/
theorem exists_tiltedPhi_local_factor {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : 2 * θ < π / 2) {ρ₀ : ℂ}
    (hρ₀ : ρ₀ ∈ zetaZeroConfig.carrier) (hline : ρ₀.re = 1 / 2) :
    ∃ v : ℂ → ℂ, AnalyticAt ℂ v (ρ₀.im : ℂ) ∧ v (ρ₀.im : ℂ) ≠ 0 ∧
      paperFT (tiltedPhi θ) =ᶠ[𝓝 (ρ₀.im : ℂ)]
        fun z => (z - (ρ₀.im : ℂ)) ^ (zetaZeroConfig.mult ρ₀) * v z := by
  have hnt : IsNontrivialZero ρ₀ := hρ₀
  obtain ⟨u, hu, hu0, hloc⟩ := exists_zeta_local_factor hρ₀
  set m := zetaZeroConfig.mult ρ₀
  set γ : ℂ := (ρ₀.im : ℂ) with hγ
  have hsγ : 1 / 2 + I * γ = ρ₀ := by
    apply Complex.ext <;> simp [hγ, hline]
  have hρ0 : ρ₀ ≠ 0 := fun h => by have := hnt.2.1; rw [h] at this; simp at this
  have hρ1 : ρ₀ ≠ 1 := fun h => by have := hnt.2.2; rw [h] at this; simp at this
  have hmap : Tendsto (fun z : ℂ => 1 / 2 + I * z) (𝓝 γ) (𝓝 ρ₀) := by
    have : Continuous fun z : ℂ => 1 / 2 + I * z := by fun_prop
    have h := this.tendsto γ
    rwa [hsγ] at h
  have hre : ∀ᶠ s in 𝓝 ρ₀, 0 < s.re :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hnt.2.1
  have hn0 : ∀ᶠ s in 𝓝 ρ₀, s ≠ 0 := eventually_ne_nhds hρ0
  have hn1 : ∀ᶠ s in 𝓝 ρ₀, s ≠ 1 := eventually_ne_nhds hρ1
  have hall := hmap.eventually (hloc.and (hre.and (hn0.and hn1)))
  have him : ∀ᶠ z in 𝓝 γ, |z.im| ≤ 1 / 2 := by
    have hc : Continuous fun z : ℂ => |z.im| := by fun_prop
    have : |γ.im| < 1 / 2 := by simp [hγ]
    exact (hc.tendsto γ).eventually (Iio_mem_nhds this) |>.mono fun z hz => le_of_lt hz
  set v : ℂ → ℂ := fun z => cexp (z * θ) * (I ^ m * (xiUnit (1 / 2 + I * z) * u (1 / 2 + I * z)))
    with hv
  have hxiU : AnalyticAt ℂ xiUnit ρ₀ := analyticAt_xiUnit hnt.2.1
  refine ⟨v, ?_, ?_, ?_⟩
  · have h1 : AnalyticAt ℂ (fun z : ℂ => xiUnit (1 / 2 + I * z)) γ :=
      hxiU.comp_of_eq (by fun_prop) hsγ
    have h2 : AnalyticAt ℂ (fun z : ℂ => u (1 / 2 + I * z)) γ :=
      hu.comp_of_eq (by fun_prop) hsγ
    have h3 : AnalyticAt ℂ (fun z : ℂ => cexp (z * θ)) γ := by fun_prop
    exact h3.mul (analyticAt_const.mul (h1.mul h2))
  · simp only [hv, hsγ]
    exact mul_ne_zero (Complex.exp_ne_zero _) (mul_ne_zero (pow_ne_zero _ Complex.I_ne_zero)
      (mul_ne_zero (xiUnit_ne_zero hρ0 hρ1 hnt.2.1) hu0))
  · filter_upwards [hall, him] with z hz hzim
    obtain ⟨hζ, hre', hz0, hz1⟩ := hz
    rw [paperFT_tiltedPhi hθ0 hθ hzim, ← riemannXiHat_eq, riemannXiHat_eq_xiUnit_mul_zeta hre' hz0 hz1,
      hζ]
    have e : 1 / 2 + I * z - ρ₀ = I * (z - γ) := by rw [← hsγ]; ring
    rw [e, mul_pow]; simp only [hv]; ring

/-! ## Truncation of a decaying kernel -/

/-- The kernel truncated to `[-U, U]`. -/
def cutoffCore (U : ℝ) (g : ℝ → ℂ) : ℝ → ℂ := (Icc (-U) U).indicator g

/-- The part of the kernel beyond `|u| = U`. -/
def cutoffTail (U : ℝ) (g : ℝ → ℂ) : ℝ → ℂ := {u : ℝ | U < |u|}.indicator g

theorem cutoffCore_add_tail (U : ℝ) (g : ℝ → ℂ) (u : ℝ) :
    cutoffCore U g u + cutoffTail U g u = g u := by
  unfold cutoffCore cutoffTail
  by_cases h : U < |u|
  · have h' : u ∉ Icc (-U) U := fun hm => by
      have := abs_le.mpr ⟨hm.1, hm.2⟩; linarith
    rw [indicator_of_notMem h', indicator_of_mem (show u ∈ {u : ℝ | U < |u|} from h), zero_add]
  · push Not at h
    have h' : u ∈ Icc (-U) U := ⟨(abs_le.mp h).1, (abs_le.mp h).2⟩
    rw [indicator_of_mem h', indicator_of_notMem (show u ∉ {u : ℝ | U < |u|} from not_lt.mpr h),
      add_zero]

theorem cutoffCore_eq_zero {U : ℝ} {g : ℝ → ℂ} {u : ℝ} (hu : U < |u|) : cutoffCore U g u = 0 := by
  unfold cutoffCore
  refine indicator_of_notMem (fun hm => ?_) _
  have := abs_le.mpr ⟨hm.1, hm.2⟩; linarith

theorem integrable_cutoffCore_mul_cexp {U : ℝ} {g : ℝ → ℂ} (hg : Continuous g) (z : ℂ) :
    Integrable (fun u : ℝ => cutoffCore U g u * cexp (I * z * u)) := by
  have hc : ContinuousOn (fun u : ℝ => g u * cexp (I * z * u)) (Icc (-U) U) :=
    (hg.mul (by fun_prop)).continuousOn
  have h := (hc.integrableOn_Icc (μ := (volume : Measure ℝ))).integrable_indicator
    measurableSet_Icc
  refine h.congr (Eventually.of_forall fun u => ?_)
  simp only [cutoffCore, indicator]
  split_ifs <;> simp

theorem integrable_cutoffCore {U : ℝ} {g : ℝ → ℂ} (hg : Continuous g) :
    Integrable (cutoffCore U g) := by
  have h := integrable_cutoffCore_mul_cexp (U := U) hg 0
  simpa using h

theorem integrable_cutoffTail_mul_cexp {U : ℝ} {g : ℝ → ℂ} (hg : SuperExpDecay g) (z : ℂ) :
    Integrable (fun u : ℝ => cutoffTail U g u * cexp (I * z * u)) := by
  have h := (hg.integrable_mul_cexp z).indicator (measurableSet_tiltedTailSet U)
  refine h.congr (Eventually.of_forall fun u => ?_)
  simp only [cutoffTail, indicator]
  split_ifs <;> simp

theorem paperFT_cutoffCore_eq {U : ℝ} {g : ℝ → ℂ} (hg : SuperExpDecay g) (z : ℂ) :
    paperFT (cutoffCore U g) z = paperFT g z - paperFT (cutoffTail U g) z := by
  unfold paperFT
  rw [eq_sub_iff_add_eq, ← integral_add (integrable_cutoffCore_mul_cexp hg.1 z)
    (integrable_cutoffTail_mul_cexp hg z)]
  congr 1; funext x
  rw [← add_mul, cutoffCore_add_tail]

/-- `‖(g_{>U})^(z)‖ ≤ expTail g (1/2) U` for `|Im z| ≤ 1/2`. -/
theorem norm_paperFT_cutoffTail_le {U : ℝ} {g : ℝ → ℂ} (hg : SuperExpDecay g) {z : ℂ}
    (hz : |z.im| ≤ 1 / 2) :
    ‖paperFT (cutoffTail U g) z‖ ≤ expTail g (1 / 2) U := by
  unfold paperFT expTail
  refine (norm_integral_le_integral_norm _).trans (integral_mono_of_nonneg
    (Eventually.of_forall fun u => norm_nonneg _) (hg.integrable_tail (1 / 2) U)
    (Eventually.of_forall fun u => ?_))
  simp only [cutoffTail, indicator, mem_setOf_eq]
  split_ifs with h1 h2
  · rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (norm_cexp_I_mul_le_exp hz u) (norm_nonneg _)
  · exact absurd h1.le h2
  · simp only [zero_mul, norm_zero]; positivity
  · simp

/-! ## Bumped tests -/

/-- `h ⋆ κ₂`: the kernel `h` smoothed by the polar-free bump at radius `w` and frequency `ω`. -/
def bumpedTest (h : ℝ → ℂ) (w ω : ℝ) : ℝ → ℂ :=
  convolution h (scaledBumpPolarFree w ω) (ContinuousLinearMap.mul ℝ ℂ) volume

theorem integrable_mul_cexp_of_support {h : ℝ → ℂ} {U : ℝ} (hh : Integrable h)
    (hsupp : ∀ u, U < |u| → h u = 0) (z : ℂ) :
    Integrable (fun u : ℝ => h u * cexp (I * z * u)) := by
  refine Integrable.mono' (hh.norm.mul_const (Real.exp (|z.im| * U)))
    (hh.aestronglyMeasurable.mul (by fun_prop : Continuous fun u : ℝ =>
      cexp (I * z * u)).aestronglyMeasurable) (Eventually.of_forall fun u => ?_)
  rw [norm_mul]
  by_cases hu : U < |u|
  · rw [hsupp u hu, norm_zero, zero_mul]; positivity
  · push Not at hu
    refine mul_le_mul_of_nonneg_left ((norm_cexp_I_mul_le_exp (le_refl _) u).trans ?_)
      (norm_nonneg _)
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hu (abs_nonneg _))

theorem paperFT_bumpedTest {h : ℝ → ℂ} {U w : ℝ} (hh : Integrable h)
    (hsupp : ∀ u, U < |u| → h u = 0) (hw : 0 < w) (ω : ℝ) (z : ℂ) :
    paperFT (bumpedTest h w ω) z = paperFT h z * paperFT (scaledBumpPolarFree w ω) z :=
  paperFT_convolution (integrable_mul_cexp_of_support hh hsupp z)
    (integrable_scaledBumpPolarFree_mul_exp hw ω z)

theorem contDiff_bumpedTest {h : ℝ → ℂ} (hh : Integrable h) {w : ℝ} (hw : 0 < w) (ω : ℝ) :
    ContDiff ℝ 2 (bumpedTest h w ω) :=
  (hasCompactSupport_scaledBumpPolarFree hw ω).contDiff_convolution_right
    (ContinuousLinearMap.mul ℝ ℂ) (n := 2) hh.locallyIntegrable (contDiff_scaledBumpPolarFree w ω)

theorem bumpedTest_eq_zero {h : ℝ → ℂ} {U w x : ℝ} (hsupp : ∀ u, U < |u| → h u = 0)
    (hw : 0 < w) (ω : ℝ) (hx : U + w < |x|) : bumpedTest h w ω x = 0 := by
  unfold bumpedTest
  rw [convolution_def]
  have : ∀ t : ℝ, (ContinuousLinearMap.mul ℝ ℂ) (h t) (scaledBumpPolarFree w ω (x - t)) = 0 := by
    intro t
    simp only [ContinuousLinearMap.mul_apply']
    by_cases ht : U < |t|
    · rw [hsupp t ht, zero_mul]
    · push Not at ht
      have hxt : w < |x - t| := by
        have := abs_sub_abs_le_abs_sub x t; linarith
      rw [scaledBumpPolarFree_eq_zero hw hxt, mul_zero]
  simp [this]

theorem tsupport_bumpedTest {h : ℝ → ℂ} {U w L : ℝ} (hsupp : ∀ u, U < |u| → h u = 0)
    (hw : 0 < w) (ω : ℝ) (hL : U + w ≤ L) : tsupport (bumpedTest h w ω) ⊆ Icc (-L) L := by
  apply closure_minimal _ isClosed_Icc
  intro x hx
  have h' : ¬ U + w < |x| := fun h' => hx (bumpedTest_eq_zero hsupp hw ω h')
  push Not at h'
  exact ⟨by linarith [(abs_le.mp h').1], by linarith [(abs_le.mp h').2]⟩

theorem paperFT_bumpedTest_half_I {h : ℝ → ℂ} {U w : ℝ} (hh : Integrable h)
    (hsupp : ∀ u, U < |u| → h u = 0) (hw : 0 < w) (ω : ℝ) :
    paperFT (bumpedTest h w ω) (I / 2) = 0 := by
  rw [paperFT_bumpedTest hh hsupp hw, paperFT_scaledBumpPolarFree hw]
  have : (I / 2) ^ 2 + 1 / 4 = (0 : ℂ) := by ring_nf; rw [Complex.I_sq]; ring
  rw [this]; ring

theorem paperFT_bumpedTest_neg_half_I {h : ℝ → ℂ} {U w : ℝ} (hh : Integrable h)
    (hsupp : ∀ u, U < |u| → h u = 0) (hw : 0 < w) (ω : ℝ) :
    paperFT (bumpedTest h w ω) (-(I / 2)) = 0 := by
  rw [paperFT_bumpedTest hh hsupp hw, paperFT_scaledBumpPolarFree hw]
  have : (-(I / 2)) ^ 2 + 1 / 4 = (0 : ℂ) := by ring_nf; rw [Complex.I_sq]; ring
  rw [this]; ring

/-! ## The plain bump as a Hodge-class test -/

theorem tsupport_scaledBumpPolarFree {w L : ℝ} (hw : 0 < w) (ω : ℝ) (hL : w ≤ L) :
    tsupport (scaledBumpPolarFree w ω) ⊆ Icc (-L) L := by
  apply closure_minimal _ isClosed_Icc
  intro x hx
  have h' : ¬ w < |x| := fun h' => hx (scaledBumpPolarFree_eq_zero hw h')
  push Not at h'
  exact ⟨by linarith [(abs_le.mp h').1], by linarith [(abs_le.mp h').2]⟩

theorem paperFT_scaledBumpPolarFree_half_I {w : ℝ} (hw : 0 < w) (ω : ℝ) :
    paperFT (scaledBumpPolarFree w ω) (I / 2) = 0 := by
  rw [paperFT_scaledBumpPolarFree hw]
  have : (I / 2) ^ 2 + 1 / 4 = (0 : ℂ) := by ring_nf; rw [Complex.I_sq]; ring
  rw [this]; ring

theorem paperFT_scaledBumpPolarFree_neg_half_I {w : ℝ} (hw : 0 < w) (ω : ℝ) :
    paperFT (scaledBumpPolarFree w ω) (-(I / 2)) = 0 := by
  rw [paperFT_scaledBumpPolarFree hw]
  have : (-(I / 2)) ^ 2 + 1 / 4 = (0 : ℂ) := by ring_nf; rw [Complex.I_sq]; ring
  rw [this]; ring

/-- **Weil energy of the plain bump.**  `‖W(κ₂, κ₂)‖ ≤ B_w² (1+|ω|)⁴ · 24 A₀ log(|ω|+3)`. -/
theorem norm_W_scaledBumpPolarFree_le {A₀ : ℝ} (hA₀ : 1 ≤ A₀)
    (hloc : ∀ t : ℝ, (zetaZeroConfig.N t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3))
    {w : ℝ} (hw : 0 < w) (hw4 : 4 * w ≤ 1) (ω : ℝ) :
    ‖zetaZeroConfig.W (scaledBumpPolarFree w ω) (scaledBumpPolarFree w ω)‖ ≤
      scaledBumpConst w ^ 2 * (1 + |ω|) ^ 4 * (24 * A₀ * Real.log (|ω| + 3)) := by
  have hC := scaledBumpConst_nonneg hw
  obtain ⟨hsumm, hsumle⟩ := window_tsum_le zetaZeroConfig hA₀ hloc ω
  set K := scaledBumpConst w ^ 2 * (1 + |ω|) ^ 4 with hK
  have hK0 : 0 ≤ K := by positivity
  have hpt : ∀ ρ : zetaZeroConfig.carrier,
      ‖zetaZeroConfig.Wsummand (scaledBumpPolarFree w ω) (scaledBumpPolarFree w ω) ρ‖ ≤
        K * ((zetaZeroConfig.mult ρ : ℝ) / (1 + |(ρ : ℂ).im - ω|) ^ 3) := by
    intro ρ
    have hmem := ρ.2
    have hstrip' : 0 < (ρ : ℂ).re ∧ (ρ : ℂ).re < 1 := by
      have h : IsNontrivialZero (ρ : ℂ) := hmem
      exact ⟨h.2.1, h.2.2⟩
    have hIm : |(gammaOf (ρ : ℂ)).im| ≤ 1 / 2 := (WeilEF.abs_gammaOf_im_lt hstrip').le
    have hIm' : |((starRingEnd ℂ) (gammaOf (ρ : ℂ))).im| ≤ 1 / 2 := by
      rw [Complex.conj_im, abs_neg]; exact hIm
    have hre1 : (gammaOf (ρ : ℂ)).re = (ρ : ℂ).im := WeilEF.gammaOf_re _
    have hre2 : ((starRingEnd ℂ) (gammaOf (ρ : ℂ))).re = (ρ : ℂ).im := by
      rw [Complex.conj_re, WeilEF.gammaOf_re]
    have hv1 := norm_paperFT_scaledBumpPolarFree_le hw hw4 ω hIm
    have hv2 := norm_paperFT_scaledBumpPolarFree_le hw hw4 ω hIm'
    rw [hre1] at hv1; rw [hre2] at hv2
    unfold ZeroConfig.Wsummand
    rw [norm_mul, norm_mul, Complex.norm_natCast, RCLike.norm_conj]
    have hm : (0 : ℝ) ≤ zetaZeroConfig.mult ρ := Nat.cast_nonneg _
    set D := 1 + |(ρ : ℂ).im - ω| with hD
    have hD1 : 1 ≤ D := by rw [hD]; linarith [abs_nonneg ((ρ : ℂ).im - ω)]
    have hq : (scaledBumpConst w * (1 + |ω|) ^ 2 / D ^ 2) *
        (scaledBumpConst w * (1 + |ω|) ^ 2 / D ^ 2) ≤ K * (1 / D ^ 3) := by
      rw [hK]
      have hD4 : D ^ 3 ≤ D ^ 4 := pow_le_pow_right₀ hD1 (by norm_num)
      have e : (scaledBumpConst w * (1 + |ω|) ^ 2 / D ^ 2) *
          (scaledBumpConst w * (1 + |ω|) ^ 2 / D ^ 2) =
          scaledBumpConst w ^ 2 * (1 + |ω|) ^ 4 * (1 / D ^ 4) := by
        field_simp
      rw [e]
      apply mul_le_mul_of_nonneg_left _ hK0
      exact one_div_le_one_div_of_le (by positivity) hD4
    calc (zetaZeroConfig.mult ρ : ℝ) * ‖paperFT (scaledBumpPolarFree w ω) (gammaOf ρ)‖ *
          ‖paperFT (scaledBumpPolarFree w ω) ((starRingEnd ℂ) (gammaOf ρ))‖
        ≤ (zetaZeroConfig.mult ρ : ℝ) * (scaledBumpConst w * (1 + |ω|) ^ 2 / D ^ 2) *
            (scaledBumpConst w * (1 + |ω|) ^ 2 / D ^ 2) := by gcongr
      _ = (zetaZeroConfig.mult ρ : ℝ) * ((scaledBumpConst w * (1 + |ω|) ^ 2 / D ^ 2) *
            (scaledBumpConst w * (1 + |ω|) ^ 2 / D ^ 2)) := by ring
      _ ≤ (zetaZeroConfig.mult ρ : ℝ) * (K * (1 / D ^ 3)) := mul_le_mul_of_nonneg_left hq hm
      _ = K * ((zetaZeroConfig.mult ρ : ℝ) / D ^ 3) := by ring
  have hsum' : Summable (fun ρ : zetaZeroConfig.carrier =>
      ‖zetaZeroConfig.Wsummand (scaledBumpPolarFree w ω) (scaledBumpPolarFree w ω) ρ‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hpt (hsumm.mul_left _)
  unfold ZeroConfig.W
  refine (norm_tsum_le_tsum_norm hsum').trans ?_
  refine (Summable.tsum_le_tsum hpt hsum' (hsumm.mul_left _)).trans ?_
  rw [tsum_mul_left]
  calc K * ∑' ρ : zetaZeroConfig.carrier,
        (zetaZeroConfig.mult ρ : ℝ) / (1 + |(ρ : ℂ).im - ω|) ^ 3
      ≤ K * (24 * A₀ * Real.log (|ω| + 3)) := mul_le_mul_of_nonneg_left hsumle hK0
    _ = _ := by rw [hK]

end

end RHTower
