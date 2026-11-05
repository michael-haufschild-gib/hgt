import GaloisForLFunctions.ZeroConfigurationGeometry.EffectiveHeights.LatticeRate
import GaloisForLFunctions.ZeroConfigurationGeometry.NegativeTests.ConvolutionCamera
import GaloisForLFunctions.ZeroConfigurationGeometry.NegativeTests.ClusterRate
import GaloisForLFunctions.ZeroConfigurationGeometry.NegativeTests.CubicTail

/-!
# Explicit cameras for cubic-logarithmically isolated clusters

A finite height makes the normalized convolution camera uniformly close to one
on a cluster and zero at every other nearby point. Radius-normalized variation
controls the local error; quartic spline order bounds the absolute Fourier tail.
-/

open MeasureTheory Complex Set Filter Topology
open scoped Real ComplexConjugate

noncomputable section
namespace GaloisForLFunctions.ZeroConfigurationGeometry
open Zeta23 SquareRootThreshold

/-- A finite camera height for clusters with cubic-logarithmic isolation cost. -/
def cameraCubicIsolationHeight (θ lam A S Lη : ℝ) : ℝ :=
  let β := lam - θ / 2
  let ℓ := 2 * Real.pi * A / lam
  let e := 6 * slackBound ℓ * (1 + slackBound ℓ)
  let c := 2 * growthRate ℓ * lam ^ 2 + 2 * floorRate ℓ * lam ^ 2 * (lam + Lη)
  let K := c / 2 + 2
  let MK := e * lam + K + 2
  let ρ := 8 * MK / β
  let α := 1 / (24 * MK * (1 + ρ))
  let q := max 0 (Real.log α⁻¹)
  let U := max (max 1 (2 * Real.pi / lam))
    (6 * MK * q + (lam + 4) + (Real.log (max S 1) + 605) + 1)
  2 * Real.pi * Real.exp (max U
    (Real.log (max (6 * cameraSlowConstant lam ℓ 0) (4 * lam) + 1)))

theorem cameraCubicIsolationHeight_ge (θ lam A S Lη : ℝ) :
    2 * Real.pi * Real.exp 1 ≤ cameraCubicIsolationHeight θ lam A S Lη := by
  unfold cameraCubicIsolationHeight
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
    (((le_max_left _ _).trans (le_max_left _ _)).trans (le_max_left _ _))) (by positivity)

private theorem cameraCubicIsolationHeight_eq_of_parameters
    {θ lam A S Lη β ℓ e c K MK ρ α q S'' V U₀ : ℝ}
    (hβ : β = lam - θ / 2) (hℓ : ℓ = 2 * π * A / lam)
    (he : e = 6 * slackBound ℓ * (1 + slackBound ℓ))
    (hc : c = 2 * growthRate ℓ * lam ^ 2 + 2 * floorRate ℓ * lam ^ 2 * (lam + Lη))
    (hK : K = c / 2 + 2) (hMK : MK = e * lam + K + 2)
    (hρ : ρ = 8 * MK / β) (hα : α = 1 / (24 * MK * (1 + ρ)))
    (hq : q = max 0 (Real.log α⁻¹)) (hS'' : S'' = max S 1)
    (hV : V = max (6 * cameraSlowConstant lam ℓ 0) (4 * lam) + 1)
    (hU₀ : U₀ = max (max (max 1 (2 * π / lam))
      (6 * MK * q + (lam + 4) + (Real.log S'' + 605) + 1)) (Real.log V)) :
    cameraCubicIsolationHeight θ lam A S Lη = 2 * π * Real.exp U₀ := by
  rw [hU₀, hV, hS'', hq, hα, hρ, hMK, hK, hc, he, hℓ, hβ]
  rfl

/-- A cluster with cubic-logarithmic isolation admits a normalized convolution camera:
quarter accuracy on the cluster, exact local blindness outside it, and quarter absolute tail. -/
theorem fourier_cluster_camera_explicit {θ lam A S Lη : ℝ} (hθ : 0 ≤ θ)
    (hlam : θ / 2 < lam) (hA : 0 ≤ A) (hLη0 : 0 ≤ Lη) :
    ∀ T : ℝ, cameraCubicIsolationHeight θ lam A S Lη ≤ T →
      ∀ Z Z' : ZeroConfig, TemperedConfig Z → TemperedConfig Z' →
        ∑' z, ‖multDiff Z Z' z‖ / (1 + Complex.normSq (gammaOf z)) ≤ S →
        (∀ (s : Finset ℂ) (x y : ℝ), x ≤ y →
          (∀ z ∈ s, multDiff Z Z' z ≠ 0 ∧ |z.im - T| ≤ T / 2 ∧ z.im ∈ Icc x y) →
            (s.card : ℝ) ≤ θ / (2 * π) * Real.log (T / (2 * π)) * (y - x) +
              A * Real.log (T / (2 * π))) →
        ∀ z₀ : ℂ, |z₀.im - T| ≤ T / 4 → |z₀.re - 1 / 2| ≤ 1 / 2 →
        ∀ η : ℝ, 0 < η → η ≤ 1 →
          max 0 (Real.log (1 / η)) ≤ Lη * Real.log (T / (2 * π)) ^ 3 →
        ∀ r : ℝ, 0 ≤ r → r ≤ η * T ^ (-(slowExponent lam + 2)) →
        (∀ z, multDiff Z Z' z ≠ 0 → |z.im - T| ≤ T / 2 →
          ‖z - z₀‖ ≤ r ∨ η ≤ ‖z - z₀‖) →
        ∃ f : ℝ → ℂ,
          ApertureWindow (2 * (lam * (Real.log (T / (2 * π)) / 2))) f ∧
          (∀ z, multDiff Z Z' z ≠ 0 → |z.im - z₀.im| ≤ T / 4 → ¬ ‖z - z₀‖ ≤ r →
            paperFT f (gammaOf z) = 0) ∧
          (∀ z : ℂ, ‖z - z₀‖ ≤ r → ‖paperFT f (gammaOf z) - 1‖ ≤ 1 / 4) ∧
          Summable (fourierFarTerm (multDiff Z Z') f z₀.im (T / 4)) ∧
          (∑' z, fourierFarTerm (multDiff Z Z') f z₀.im (T / 4) z) ≤ 1 / 4 := by
  have h2π0 : 0 < 2 * π := by positivity
  have hlam0 : 0 < lam := by linarith only [hθ, hlam]
  obtain ⟨β, hβ⟩ : ∃ β, β = lam - θ / 2 := ⟨_, rfl⟩
  have hβ0 : 0 < β := by rw [hβ]; linarith only [hlam]
  have hβlam : β ≤ lam := by rw [hβ]; linarith only [hθ]
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ, ℓ = 2 * π * A / lam := ⟨_, rfl⟩
  have hℓ0 : 0 ≤ ℓ := by rw [hℓ]; positivity
  obtain ⟨e, he⟩ : ∃ e, e = 6 * slackBound ℓ * (1 + slackBound ℓ) := ⟨_, rfl⟩
  have : 0 ≤ slackBound ℓ := by unfold slackBound; positivity
  have he0 : 0 ≤ e := by rw [he]; positivity
  obtain ⟨c, hc⟩ : ∃ c, c = 2 * growthRate ℓ * lam ^ 2 +
      2 * floorRate ℓ * lam ^ 2 * (lam + Lη) := ⟨_, rfl⟩
  have : 0 ≤ growthRate ℓ := growthRate_nonneg hℓ0
  have : 0 ≤ floorRate ℓ := floorRate_nonneg hℓ0
  have hc0 : 0 ≤ c := by rw [hc]; positivity
  obtain ⟨K, hK⟩ : ∃ K, K = c / 2 + 2 := ⟨_, rfl⟩
  have hK1 : 2 ≤ K := by rw [hK]; linarith only [hc0]
  obtain ⟨MK, hMK⟩ : ∃ MK, MK = e * lam + K + 2 := ⟨_, rfl⟩
  have hMK0 : 0 < MK := by rw [hMK]; positivity
  obtain ⟨ρ, hρ⟩ : ∃ ρ, ρ = 8 * MK / β := ⟨_, rfl⟩
  have hρ0 : 0 < ρ := by rw [hρ]; positivity
  obtain ⟨α, hα⟩ : ∃ α, α = 1 / (24 * MK * (1 + ρ)) := ⟨_, rfl⟩
  have hα0 : 0 < α := by rw [hα]; positivity
  obtain ⟨q, hq⟩ : ∃ q, q = max 0 (Real.log α⁻¹) := ⟨_, rfl⟩
  obtain ⟨S'', hS''⟩ : ∃ S'', S'' = max S 1 := ⟨_, rfl⟩
  have hS''1 : 1 ≤ S'' := by rw [hS'']; exact le_max_right _ _
  obtain ⟨V, hV⟩ : ∃ V, V = max (6 * cameraSlowConstant lam ℓ 0) (4 * lam) + 1 := ⟨_, rfl⟩
  have hV0 : 0 < V := by
    rw [hV]
    linarith only [hlam0, le_max_right (6 * cameraSlowConstant lam ℓ 0) (4 * lam)]
  obtain ⟨U₀, hU₀⟩ : ∃ U₀, U₀ = max (max (max 1 (2 * π / lam))
      (6 * MK * q + (lam + 4) + (Real.log S'' + 605) + 1)) (Real.log V) := ⟨_, rfl⟩
  have hheight := cameraCubicIsolationHeight_eq_of_parameters
    hβ hℓ he hc hK hMK hρ hα hq hS'' hV hU₀
  intro T hT Z Z' hZ hZ' hStail hcount z₀ hz₀ hz₀re η hη0 hη1 hlogη r hr0 hr hiso
  rw [hheight] at hT
  -- height scale `u = log(T / 2π)`
  have hTdiv : Real.exp U₀ ≤ T / (2 * π) := by
    rw [le_div_iff₀ h2π0]
    linarith only [hT]
  obtain ⟨u, hu⟩ : ∃ u, u = Real.log (T / (2 * π)) := ⟨_, rfl⟩
  rw [← hu] at hcount hlogη ⊢
  have huU₀ : U₀ ≤ u := by
    rw [hu, ← Real.log_exp U₀]
    exact Real.log_le_log (Real.exp_pos _) hTdiv
  rw [hU₀] at huU₀
  have hu1 : 1 ≤ u :=
    (((le_max_left _ _).trans (le_max_left _ _)).trans (le_max_left _ _)).trans huU₀
  have hu0 : 0 < u := by linarith only [hu1]
  have hu_lam : 2 * π / lam ≤ u :=
    (((le_max_right _ _).trans (le_max_left _ _)).trans (le_max_left _ _)).trans huU₀
  have hu_bud : 6 * MK * q + (lam + 4) + (Real.log S'' + 605) + 1 ≤ u :=
    ((le_max_right _ _).trans (le_max_left _ _)).trans huU₀
  have hTu : T = 2 * π * Real.exp u := by
    rw [hu, Real.exp_log (lt_of_lt_of_le (Real.exp_pos _) hTdiv)]
    field_simp
  have hT0 : 0 < T := by rw [hTu]; positivity
  have hEV : V ≤ Real.exp u := by
    have h1 : Real.log V ≤ u := (le_max_right _ _).trans huU₀
    calc V = Real.exp (Real.log V) := (Real.exp_log hV0).symm
      _ ≤ Real.exp u := Real.exp_le_exp.mpr h1
  have hbig : 6 * slowConst lam ℓ 0 ≤ Real.exp u := by
    rw [hV] at hEV
    have hmax := le_max_left (6 * cameraSlowConstant lam ℓ 0) (4 * lam)
    have hslow := slowConst_le_cameraSlowConstant (M' := 0) hlam0 hℓ0
    linarith only [hEV, hmax, hslow]
  have h4lam : 4 * lam ≤ Real.exp u := by
    rw [hV] at hEV
    linarith only [hEV, le_max_right (6 * cameraSlowConstant lam ℓ 0) (4 * lam)]
  have hET : Real.exp u ≤ T := by
    rw [hTu]; nlinarith only [Real.exp_pos u, Real.pi_gt_three]
  have hT1 : 1 ≤ T := (Real.one_le_exp hu0.le).trans hET
  -- camera parameters
  obtain ⟨a, ha⟩ : ∃ a, a = lam * (u / 2) := ⟨_, rfl⟩
  rw [← ha]
  obtain ⟨ε, hε⟩ : ∃ ε, ε = β * u / 8 := ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D, D = (θ + β) / (2 * π) * u := ⟨_, rfl⟩
  obtain ⟨C₀, hC₀⟩ : ∃ C₀, C₀ = A * u := ⟨_, rfl⟩
  obtain ⟨hDa, hD1, hDup, hC₀ℓ⟩ :=
    rvm_density_facts hθ hlam hA hβ hℓ hu0 hu_lam ha hε hD hC₀
  have hD0 : 0 < D := by linarith only [hD1]
  -- The spline has quartic logarithmic order.
  obtain ⟨k, hk⟩ : ∃ k : ℕ, k = ⌈K * u ^ 4⌉₊ := ⟨_, rfl⟩
  obtain ⟨W, hWdef⟩ : ∃ W, W = windowExponent (2 * D⁻¹) (localSlack D C₀) := ⟨_, rfl⟩
  have hW0 : 0 ≤ W := by
    rw [hWdef, windowExponent]
    have := windowSlack_localSlack_nonneg (C₀ := C₀) hD0
    positivity
  have hWle : W ≤ e * D := by rw [hWdef, he]; exact windowExponent_le hD1 hC₀ℓ
  obtain ⟨m, hmdef⟩ : ∃ m : ℕ, m = ⌈W⌉₊ + k := ⟨_, rfl⟩
  obtain ⟨hkK, hk1, hm', hmle, hmε⟩ :=
    quartic_camera_order_facts hK1 he0 hlam0 hβ0 hMK hρ hu1 hε hDup hW0 hWle hk hmdef
  have hm : windowExponent (2 * D⁻¹) (localSlack D C₀) + (k : ℝ) ≤ m := hWdef ▸ hm'
  -- the cluster near `z₀`
  have hsub_band : ∀ z : ℂ, |z.im - z₀.im| ≤ T / 4 → |z.im - T| ≤ T / 2 := fun z hz => by
    have h1 := abs_le.mp hz
    have h2 := abs_le.mp hz₀
    rw [abs_le]
    constructor <;> linarith only [h1.1, h1.2, h2.1, h2.2]
  have hiso' : ∀ z, multDiff Z Z' z ≠ 0 → |z.im - z₀.im| ≤ T / 4 →
      ‖z - z₀‖ ≤ r ∨ η ≤ ‖z - z₀‖ :=
    fun z hcz hzR => hiso z hcz (hsub_band z hzR)
  have hcount' : ∀ (s : Finset ℂ) (x y : ℝ), x ≤ y →
      (∀ z ∈ s, multDiff Z Z' z ≠ 0 ∧ |z.im - z₀.im| ≤ T / 4 ∧ z.im ∈ Icc x y) →
        (s.card : ℝ) ≤ D * (y - x) + C₀ := by
    intro s x y hxy hs
    have hc1 := hcount s x y hxy fun z hz =>
      ⟨(hs z hz).1, hsub_band z (hs z hz).2.1, (hs z hz).2.2⟩
    rw [← hC₀] at hc1
    have hDθ : θ / (2 * π) * u ≤ D := by
      rw [hD]
      exact mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right (by linarith only [hβ0]) h2π0.le) hu0.le
    have hmul : θ / (2 * π) * u * (y - x) ≤ D * (y - x) :=
      mul_le_mul_of_nonneg_right hDθ (sub_nonneg.mpr hxy)
    exact hc1.trans (add_le_add hmul (le_refl C₀))
  have hSbound : S ≤ S'' := by rw [hS'']; exact le_max_left _ _
  have hε0 : 0 < ε := by rw [hε]; positivity
  have hT4 : 4 ≤ T := by
    rw [hTu]
    have he := Real.one_le_exp hu0.le
    have hh := mul_le_mul_of_nonneg_left he (by positivity : (0 : ℝ) ≤ 2 * π)
    linarith only [hh, Real.pi_gt_three]
  have hT2 : 2 ≤ T := by linarith only [hT4]
  have hκ0 : 0 ≤ slowExponent lam := by
    unfold slowExponent
    linarith only [mul_pos Real.pi_pos hlam0, hlam0]
  have hDT : 4 * D ≤ T ^ 2 := by
    have h1 : 4 * D ≤ 4 * lam * Real.exp u := by
      have hh := mul_le_mul_of_nonneg_left (hDup.trans (mul_le_mul_of_nonneg_left
        (show u ≤ Real.exp u by linarith only [Real.add_one_le_exp u]) hlam0.le))
        (by norm_num : (0 : ℝ) ≤ 4)
      linarith only [hh]
    have h2 : 4 * lam * Real.exp u ≤ Real.exp u * Real.exp u :=
      mul_le_mul_of_nonneg_right h4lam (Real.exp_pos u).le
    have h3 : Real.exp u * Real.exp u ≤ T ^ 2 := by
      rw [sq]; exact mul_le_mul hET hET (Real.exp_pos u).le hT0.le
    exact h1.trans (h2.trans h3)
  have hrb : r ≤ T ^ (-(slowExponent lam + 2)) :=
    hr.trans ((mul_le_mul_of_nonneg_right hη1 (Real.rpow_nonneg hT0.le _)).trans_eq (one_mul _))
  have hr2 : r ≤ (T ^ 2)⁻¹ := by
    have hh := hrb.trans (Real.rpow_le_rpow_of_exponent_le hT1
      (by linarith only [hκ0] : -(slowExponent lam + 2) ≤ (-2 : ℝ)))
    simpa only [Real.rpow_neg hT0.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num,
      Real.rpow_natCast] using hh
  have hrD : r ≤ min (2 * D⁻¹ / 8) (1 / 2) := by
    refine le_min (hr2.trans ?_) (hr2.trans ?_)
    · rw [show 2 * D⁻¹ / 8 = (4 * D)⁻¹ by field_simp; ring]
      exact inv_anti₀ (by positivity) hDT
    · rw [inv_le_comm₀ (by positivity) (by norm_num), one_div, inv_inv]
      nlinarith only [hT2]
  have herror := cluster_relative_error_le_quarter hu1 hTu hlam0 hβlam hD1 hDup hC₀ℓ hε
    hbig hT4 hη0 hη1 hr
  have hrΛ : r * slowRate (2 * D⁻¹) (localSlack D C₀) η ε 1 ≤ 1 / 2 := by
    linarith only [herror]
  obtain ⟨b, hb, hbs, hb1, hb0, hbm⟩ := exists_explicit_bump hε0 m
  obtain ⟨f, hfw, hblind, happrox, hsum, hle⟩ := fourier_window_of_slow_pair 0
    hD0 hη0 hε0 hDa hb hbs hb1 hk1
    (by simpa only [Nat.add_zero] using hm) hbm (C0 := 1)
    (fun w => by rw [one_mul]; exact hb0 w) hZ hZ' hz₀re
    (R := T / 4) (by positivity) hr0 hrD hrΛ hiso' hcount'
  have hSg0 : 0 ≤ ∑' z, ‖multDiff Z Z' z‖ / (1 + Complex.normSq (gammaOf z)) :=
    tsum_nonneg fun z => div_nonneg (norm_nonneg _)
      (by linarith only [Complex.normSq_nonneg (gammaOf z)])
  have hfl0 : 0 < windowFloor (2 * D⁻¹) (localSlack D C₀) η :=
    windowFloor_pos (by positivity) (localSlack_nonneg hD0) hη0
  have hQ0 : 0 < (1 + T / 4) ^ (2 * k - 2) := by positivity
  have hQne := hQ0.ne'
  have hflne : windowFloor (2 * D⁻¹) (localSlack D C₀) η ^ 2 ≠ 0 := (pow_pos hfl0 2).ne'
  obtain ⟨Tl, hTl⟩ : ∃ Tl, Tl = (windowGrowth (2 * D⁻¹) (localSlack D C₀) *
      (4 * (1 + (m : ℝ) / ε)) ^ m * 1 * Real.exp ε) ^ 2 * Real.exp a *
        (5 / 4 * (1 + |z₀.im|) ^ 2 / (1 + T / 4) ^ (2 * k - 2)) *
          ∑' z, ‖multDiff Z Z' z‖ / (1 + Complex.normSq (gammaOf z)) := ⟨_, rfl⟩
  have htail : Tl / windowFloor (2 * D⁻¹) (localSlack D C₀) η ^ 2 ≤ 1 / 4 := by
    rw [hTl]
    apply camera_cubic_isolation_tail_budget (lam := lam) (β := β) (Lη := Lη) (ℓ := ℓ)
      (c := c) (K := K) (MK := MK) (ρ := ρ) (α := α) (q := q) (S'' := S'')
      (T := T) (u := u) (a := a) (ε := ε) (D := D) (C₀ := C₀) (η := η)
      (k := k) (m := m) (z₀ := z₀)
      hu1 hTu hlam0 hβlam hℓ0 hc hK hMK0 hρ0 hα hα0 hq hS''1
      hu_bud ha hε hε0 hD1 hDup hC₀ℓ hlogη hη0 hkK hk1 hmle hmε hz₀ hSg0
      (hStail.trans hSbound)
    apply le_of_eq
    unfold localCameraConst
    field_simp
  rw [← hTl] at hle
  refine ⟨f, hfw, hblind, ?_, hsum, hle.trans htail⟩
  intro z hz
  have hh := happrox z hz
  simp only [pow_zero, one_mul, zero_add, pow_one] at hh
  exact hh.trans herror


end GaloisForLFunctions.ZeroConfigurationGeometry

#print axioms GaloisForLFunctions.ZeroConfigurationGeometry.cameraCubicIsolationHeight_ge
#print axioms GaloisForLFunctions.ZeroConfigurationGeometry.fourier_cluster_camera_explicit
