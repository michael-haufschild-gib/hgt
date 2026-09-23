import GaloisForLFunctions.RHTower.ThetaCuspReflectedSourceOddStationary
import GaloisForLFunctions.RHTower.ThetaCuspHawkingQuantumEnergyInequalityEndpoint
import Mathlib.Analysis.Calculus.Taylor

open Set Filter Topology

namespace RHTower

noncomputable section

private theorem second_iteratedDeriv_nonneg_of_isLocalMin
    {f : ℝ → ℝ} {x : ℝ} (hf : ContDiff ℝ 2 f) (hmin : IsLocalMin f x) :
    0 ≤ iteratedDeriv 2 f x := by
  by_contra hnot
  have hsecond : iteratedDeriv 2 f x < 0 := lt_of_not_ge hnot
  have hfirst : iteratedDeriv 1 f x = 0 := by
    simpa only [iteratedDeriv_one] using hmin.hasDerivAt_eq_zero
      (hf.differentiable (by norm_num) x).hasDerivAt
  have htaylor := taylor_isLittleO_univ (f := f) (x₀ := x) (n := 2) hf
  have hquarter : 0 < -(iteratedDeriv 2 f x) / 4 := by linarith
  have hbound := htaylor.def hquarter
  have hpoly : ∀ y : ℝ,
      taylorWithinEval f 2 univ x y =
        f x + (y - x) * iteratedDeriv 1 f x +
          ((y - x) ^ (2 : ℕ) / 2) * iteratedDeriv 2 f x := by
    intro y
    rw [show 2 = 1 + 1 by norm_num, taylorWithinEval_succ,
      taylorWithinEval_succ, taylor_within_zero_eval]
    simp
    ring_nf
    simp
  have hevent : ∀ᶠ y in 𝓝 x,
      f x ≤ f y ∧
        ‖f y - taylorWithinEval f 2 univ x y‖ ≤
          (-(iteratedDeriv 2 f x) / 4) * ‖(y - x) ^ (2 : ℕ)‖ :=
    hmin.and hbound
  obtain ⟨y, hy, hymin, hybound⟩ := hevent.exists_gt
  rw [hpoly y, hfirst] at hybound
  have hsquare : 0 < (y - x) ^ (2 : ℕ) := sq_pos_of_pos (sub_pos.mpr hy)
  have hnorm : ‖(y - x) ^ (2 : ℕ)‖ = (y - x) ^ (2 : ℕ) := by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (y - x))]
  rw [hnorm] at hybound
  have hremainder :
      f y - (f x + (y - x) ^ (2 : ℕ) / 2 * iteratedDeriv 2 f x) ≤
        -(iteratedDeriv 2 f x) / 4 * (y - x) ^ (2 : ℕ) := by
    calc
      _ ≤ |f y - (f x + (y - x) ^ (2 : ℕ) / 2 * iteratedDeriv 2 f x)| := le_abs_self _
      _ = ‖f y - (f x + (y - x) ^ (2 : ℕ) / 2 * iteratedDeriv 2 f x)‖ :=
        (Real.norm_eq_abs _).symm
      _ ≤ _ := by simpa only [mul_zero, add_zero] using hybound
  nlinarith

/-- Schrödinger potential of a reflected source fibre: normalized ordinary second derivative
of the product. -/
def thetaCuspReflectedSourceSchrodingerPotential (u t : ℝ) : ℝ :=
  thetaCuspReflectedLogJetOne u t ^ (2 : ℕ) - thetaCuspReflectedLogJetTwo u t

/-- First ordinary jet of the positive source decay flux. -/
def thetaCuspReflectedSourceDecayFluxCurvature (u t : ℝ) : ℝ :=
  thetaCuspReflectedSourceProduct u t *
    (thetaCuspReflectedLogJetTwo u t - thetaCuspReflectedLogJetOne u t ^ (2 : ℕ))

/-- Riccati margin is exactly derivative of reflected Schrödinger potential. -/
theorem hasDerivAt_thetaCuspReflectedSourceSchrodingerPotential (u t : ℝ) :
    HasDerivAt (thetaCuspReflectedSourceSchrodingerPotential u)
      (thetaCuspReflectedLogRiccatiMargin u t) t := by
  have h1 := hasDerivAt_thetaCuspReflectedLogJetOne u t
  have h2 := hasDerivAt_thetaCuspReflectedLogJetTwo u t
  unfold thetaCuspReflectedSourceSchrodingerPotential
    thetaCuspReflectedLogRiccatiMargin
  have hraw := (h1.pow 2).sub h2
  refine (hraw.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun _ => rfl)).congr_deriv ?_
  norm_num

/-- Global Riccati positivity makes the fibre Schrödinger potential monotone. -/
theorem monotoneOn_thetaCuspReflectedSourceSchrodingerPotential (u : ℝ) :
    MonotoneOn (thetaCuspReflectedSourceSchrodingerPotential u) (Ici 0) := by
  apply monotoneOn_of_deriv_nonneg (convex_Ici (0 : ℝ))
  · intro t ht
    exact (hasDerivAt_thetaCuspReflectedSourceSchrodingerPotential u t).continuousAt.continuousWithinAt
  · intro t ht
    exact (hasDerivAt_thetaCuspReflectedSourceSchrodingerPotential u t).differentiableAt.differentiableWithinAt
  · intro t ht
    rw [interior_Ici] at ht
    rw [(hasDerivAt_thetaCuspReflectedSourceSchrodingerPotential u t).deriv]
    exact thetaCuspReflectedLogRiccatiMargin_nonneg ht.le

/-- The reflected Schrödinger potential is strictly negative at coalescence. -/
theorem thetaCuspReflectedSourceSchrodingerPotential_zero_neg (u : ℝ) :
    thetaCuspReflectedSourceSchrodingerPotential u 0 < 0 := by
  unfold thetaCuspReflectedSourceSchrodingerPotential
    thetaCuspReflectedLogJetOne thetaCuspReflectedLogJetTwo
  have hcurv := thetaCuspLogCurvature_pos u
  norm_num
  linarith

/-- Decay flux differentiates to product times reflected log-curvature deficit. -/
theorem hasDerivAt_thetaCuspReflectedSourceDecayFlux (u t : ℝ) :
    HasDerivAt (thetaCuspReflectedSourceDecayFlux u)
      (thetaCuspReflectedSourceDecayFluxCurvature u t) t := by
  have hp := hasDerivAt_thetaCuspReflectedSourceProduct u t
  have hq := hasDerivAt_thetaCuspReflectedLogJetOne u t
  have hp' : HasDerivAt (thetaCuspReflectedSourceProduct u)
      (-thetaCuspReflectedSourceProduct u t * thetaCuspReflectedLogJetOne u t) t := by
    simpa [thetaCuspReflectedSourceDecayFlux] using hp
  unfold thetaCuspReflectedSourceDecayFlux
    thetaCuspReflectedSourceDecayFluxCurvature
  have hraw := hp'.mul hq
  refine (hraw.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun _ => rfl)).congr_deriv ?_
  ring

/-- Flux curvature has sign opposite to the monotone Schrödinger potential. -/
theorem thetaCuspReflectedSourceDecayFluxCurvature_pos_iff
    (u t : ℝ) :
    0 < thetaCuspReflectedSourceDecayFluxCurvature u t ↔
      thetaCuspReflectedSourceSchrodingerPotential u t < 0 := by
  have hp : 0 < thetaCuspReflectedSourceProduct u t := by
    unfold thetaCuspReflectedSourceProduct
    exact mul_pos (thetaCuspFullSource_pos_all _) (thetaCuspFullSource_pos_all _)
  unfold thetaCuspReflectedSourceDecayFluxCurvature
    thetaCuspReflectedSourceSchrodingerPotential
  constructor <;> intro h <;> nlinarith

theorem thetaCuspReflectedSourceDecayFluxCurvature_neg_iff
    (u t : ℝ) :
    thetaCuspReflectedSourceDecayFluxCurvature u t < 0 ↔
      0 < thetaCuspReflectedSourceSchrodingerPotential u t := by
  have hp : 0 < thetaCuspReflectedSourceProduct u t := by
    unfold thetaCuspReflectedSourceProduct
    exact mul_pos (thetaCuspFullSource_pos_all _) (thetaCuspFullSource_pos_all _)
  unfold thetaCuspReflectedSourceDecayFluxCurvature
    thetaCuspReflectedSourceSchrodingerPotential
  constructor <;> intro h <;> nlinarith

/-- **Single-switch flux law.** Along a nonnegative fibre, positive flux curvature propagates
backward and negative flux curvature propagates forward. -/
theorem thetaCuspReflectedSourceDecayFluxCurvature_single_switch
    (u : ℝ) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    (0 < thetaCuspReflectedSourceDecayFluxCurvature u t →
        0 < thetaCuspReflectedSourceDecayFluxCurvature u s) ∧
      (thetaCuspReflectedSourceDecayFluxCurvature u s < 0 →
        thetaCuspReflectedSourceDecayFluxCurvature u t < 0) := by
  have ht : 0 ≤ t := hs.trans hst
  have hpotential := monotoneOn_thetaCuspReflectedSourceSchrodingerPotential u
    hs ht hst
  constructor
  · intro hJt
    rw [thetaCuspReflectedSourceDecayFluxCurvature_pos_iff] at hJt ⊢
    exact lt_of_le_of_lt hpotential hJt
  · intro hJs
    rw [thetaCuspReflectedSourceDecayFluxCurvature_neg_iff] at hJs ⊢
    exact lt_of_lt_of_le hJs hpotential

/-- Exact first-slope carrier for the reflected source odd wall. -/
def thetaCuspReflectedSourceOddParityWallSlope (u t : ℝ) : ℝ :=
  3 * thetaCuspReflectedSourceFirstDrop u t *
      thetaCuspReflectedSourceDecayFlux u (3 * t) +
    thetaCuspReflectedSourceDecayFlux u t *
      (thetaCuspReflectedSourceFullDrop u t +
        2 * thetaCuspReflectedSourceMiddleDrop u t) -
    4 * thetaCuspReflectedSourceMiddleDrop u t *
      thetaCuspReflectedSourceDecayFlux u (2 * t)

/-- Exact second-order carrier for the reflected source odd wall. -/
def thetaCuspReflectedSourceOddParityWallCurvature (u t : ℝ) : ℝ :=
  thetaCuspReflectedSourceDecayFluxCurvature u t *
      (thetaCuspReflectedSourceFullDrop u t +
        2 * thetaCuspReflectedSourceMiddleDrop u t) +
    9 * thetaCuspReflectedSourceFirstDrop u t *
      thetaCuspReflectedSourceDecayFluxCurvature u (3 * t) -
    8 * thetaCuspReflectedSourceMiddleDrop u t *
      thetaCuspReflectedSourceDecayFluxCurvature u (2 * t) +
    6 * thetaCuspReflectedSourceDecayFlux u t *
      thetaCuspReflectedSourceDecayFlux u (3 * t) -
    2 * (-thetaCuspReflectedSourceDecayFlux u t +
      2 * thetaCuspReflectedSourceDecayFlux u (2 * t)) ^ (2 : ℕ)

theorem hasDerivAt_thetaCuspReflectedSourceOddParityWall_slope (u t : ℝ) :
    HasDerivAt (thetaCuspReflectedSourceOddParityWall u)
      (thetaCuspReflectedSourceOddParityWallSlope u t) t := by
  convert hasDerivAt_thetaCuspReflectedSourceOddParityWall u t using 1
  unfold thetaCuspReflectedSourceOddParityWallSlope
    thetaCuspReflectedSourceFirstDrop thetaCuspReflectedSourceMiddleDrop
    thetaCuspReflectedSourceFullDrop
  ring

/-- The named wall slope differentiates to the exact multiscale wall curvature. -/
theorem hasDerivAt_thetaCuspReflectedSourceOddParityWallSlope (u t : ℝ) :
    HasDerivAt (thetaCuspReflectedSourceOddParityWallSlope u)
      (thetaCuspReflectedSourceOddParityWallCurvature u t) t := by
  let A : ℝ → ℝ := thetaCuspReflectedSourceFirstDrop u
  let B : ℝ → ℝ := thetaCuspReflectedSourceMiddleDrop u
  let T : ℝ → ℝ := thetaCuspReflectedSourceFullDrop u
  let D : ℝ → ℝ := thetaCuspReflectedSourceDecayFlux u
  let J : ℝ → ℝ := thetaCuspReflectedSourceDecayFluxCurvature u
  have hA : HasDerivAt A (D t) t := by
    unfold A D thetaCuspReflectedSourceFirstDrop
    have hraw := (hasDerivAt_const t (thetaCuspReflectedSourceProduct u 0)).sub
      (hasDerivAt_thetaCuspReflectedSourceProduct u t)
    exact (hraw.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun _ => rfl)).congr_deriv (by ring)
  have hB : HasDerivAt B (-D t + 2 * D (2 * t)) t := by
    have h1 := hasDerivAt_thetaCuspReflectedSourceProduct u t
    have h2 := (hasDerivAt_thetaCuspReflectedSourceProduct u (2 * t)).comp t
      ((hasDerivAt_id t).const_mul 2)
    unfold B D thetaCuspReflectedSourceMiddleDrop
    exact ((h1.sub h2).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun _ => rfl)).congr_deriv (by ring)
  have hT : HasDerivAt T (3 * D (3 * t)) t := by
    have h3 := (hasDerivAt_thetaCuspReflectedSourceProduct u (3 * t)).comp t
      ((hasDerivAt_id t).const_mul 3)
    unfold T D thetaCuspReflectedSourceFullDrop
    have hraw := (hasDerivAt_const t (thetaCuspReflectedSourceProduct u 0)).sub h3
    exact (hraw.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun _ => rfl)).congr_deriv (by ring)
  have hD1 : HasDerivAt D (J t) t := by
    simpa only [D, J] using hasDerivAt_thetaCuspReflectedSourceDecayFlux u t
  have hD2 : HasDerivAt (fun s : ℝ => D (2 * s)) (2 * J (2 * t)) t := by
    have h := (hasDerivAt_thetaCuspReflectedSourceDecayFlux u (2 * t)).comp t
      ((hasDerivAt_id t).const_mul 2)
    exact ((h.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun _ => rfl)).congr_deriv (by ring))
  have hD3 : HasDerivAt (fun s : ℝ => D (3 * s)) (3 * J (3 * t)) t := by
    have h := (hasDerivAt_thetaCuspReflectedSourceDecayFlux u (3 * t)).comp t
      ((hasDerivAt_id t).const_mul 3)
    exact ((h.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun _ => rfl)).congr_deriv (by ring))
  change HasDerivAt
    (fun s : ℝ => 3 * A s * D (3 * s) + D s * (T s + 2 * B s) -
      4 * B s * D (2 * s)) _ t
  have hraw :=
    (((hasDerivAt_const t (3 : ℝ)).mul hA).mul hD3).add
      (hD1.mul (hT.add ((hasDerivAt_const t (2 : ℝ)).mul hB))) |>.sub
        (((hasDerivAt_const t (4 : ℝ)).mul hB).mul hD2)
  refine hraw.congr_deriv ?_
  unfold thetaCuspReflectedSourceOddParityWallCurvature
  dsimp only [A, B, T, D, J]
  simp only [Pi.mul_apply, Pi.add_apply]
  ring

theorem contDiff_two_thetaCuspReflectedSourceOddParityWall (u : ℝ) :
    ContDiff ℝ 2 (thetaCuspReflectedSourceOddParityWall u) := by
  let f : ℝ → ℝ := thetaCuspReflectedSourceProduct u
  have hf : ContDiff ℝ 2 f :=
    (contDiff_thetaCuspReflectedSourceProduct u).of_le
      (WithTop.coe_le_coe.mpr le_top)
  change ContDiff ℝ 2 (fun t : ℝ =>
    (f 0 - f (3 * t)) * (f 0 - f t) - (f t - f (2 * t)) ^ (2 : ℕ))
  fun_prop

theorem iteratedDeriv_two_thetaCuspReflectedSourceOddParityWall (u t : ℝ) :
    iteratedDeriv 2 (thetaCuspReflectedSourceOddParityWall u) t =
      thetaCuspReflectedSourceOddParityWallCurvature u t := by
  rw [show 2 = 1 + 1 by norm_num, iteratedDeriv_succ, iteratedDeriv_one]
  have hslope : deriv (thetaCuspReflectedSourceOddParityWall u) =
      thetaCuspReflectedSourceOddParityWallSlope u := by
    funext s
    exact (hasDerivAt_thetaCuspReflectedSourceOddParityWall_slope u s).deriv
  rw [hslope]
  exact (hasDerivAt_thetaCuspReflectedSourceOddParityWallSlope u t).deriv

/-- Any negative fibre admits an interior local-minimum witness carrying both exact stationary
balance and nonnegative second-order multiscale curvature. -/
theorem exists_thetaCuspReflectedSourceOddParityWall_stationary_curvature_of_neg
    {u t₀ : ℝ} (ht₀ : 0 < t₀)
    (hneg : thetaCuspReflectedSourceOddParityWall u t₀ < 0) :
    ∃ t : ℝ, 0 < t ∧ thetaCuspReflectedSourceOddParityWall u t < 0 ∧
      IsLocalMin (thetaCuspReflectedSourceOddParityWall u) t ∧
      4 * thetaCuspReflectedSourceMiddleDrop u t *
          thetaCuspReflectedSourceDecayFlux u (2 * t) =
        thetaCuspReflectedSourceDecayFlux u t *
            (thetaCuspReflectedSourceFullDrop u t +
              2 * thetaCuspReflectedSourceMiddleDrop u t) +
          3 * thetaCuspReflectedSourceFirstDrop u t *
            thetaCuspReflectedSourceDecayFlux u (3 * t) ∧
      0 ≤ thetaCuspReflectedSourceOddParityWallCurvature u t := by
  have hcenter : 0 < thetaCuspReflectedSourceProduct u 0 ^ (2 : ℕ) := by
    simp only [thetaCuspReflectedSourceProduct, add_zero, sub_zero]
    exact pow_pos (mul_pos (thetaCuspFullSource_pos_all u)
      (thetaCuspFullSource_pos_all u)) 2
  have hposEventually : ∀ᶠ t : ℝ in atTop,
      0 < thetaCuspReflectedSourceOddParityWall u t :=
    (tendsto_thetaCuspReflectedSourceOddParityWall_atTop u).eventually
      (Ioi_mem_nhds hcenter)
  obtain ⟨R, hR⟩ := eventually_atTop.mp hposEventually
  let T : ℝ := max R (t₀ + 1)
  have hRT : R ≤ T := le_max_left _ _
  have ht₀T : t₀ < T := lt_of_lt_of_le (by linarith) (le_max_right _ _)
  have hTpos : 0 < thetaCuspReflectedSourceOddParityWall u T := hR T hRT
  have hcont : Continuous (thetaCuspReflectedSourceOddParityWall u) :=
    (contDiff_two_thetaCuspReflectedSourceOddParityWall u).continuous
  have ht₀mem : t₀ ∈ Icc (0 : ℝ) T := ⟨ht₀.le, ht₀T.le⟩
  obtain ⟨t, htmem, hmin⟩ := isCompact_Icc.exists_isMinOn
    ⟨t₀, ht₀mem⟩ hcont.continuousOn
  have htneg : thetaCuspReflectedSourceOddParityWall u t < 0 :=
    lt_of_le_of_lt (hmin ht₀mem) hneg
  have htpos : 0 < t := by
    by_contra hnot
    have htzero : t = 0 := le_antisymm (le_of_not_gt hnot) htmem.1
    subst t
    simp [thetaCuspReflectedSourceOddParityWall,
      toeplitzFourOddParityWall] at htneg
  have htT : t < T := by
    by_contra hnot
    have hteq : t = T := le_antisymm htmem.2 (le_of_not_gt hnot)
    subst t
    exact (not_lt_of_ge hTpos.le) htneg
  have hlocal : IsLocalMin (thetaCuspReflectedSourceOddParityWall u) t :=
    hmin.isLocalMin (Icc_mem_nhds htpos htT)
  have hstationary := hlocal.hasDerivAt_eq_zero
    (hasDerivAt_thetaCuspReflectedSourceOddParityWall_slope u t)
  have hbalance :
      4 * thetaCuspReflectedSourceMiddleDrop u t *
          thetaCuspReflectedSourceDecayFlux u (2 * t) =
        thetaCuspReflectedSourceDecayFlux u t *
            (thetaCuspReflectedSourceFullDrop u t +
              2 * thetaCuspReflectedSourceMiddleDrop u t) +
          3 * thetaCuspReflectedSourceFirstDrop u t *
            thetaCuspReflectedSourceDecayFlux u (3 * t) := by
    unfold thetaCuspReflectedSourceOddParityWallSlope at hstationary
    linarith
  have hcurvature : 0 ≤ thetaCuspReflectedSourceOddParityWallCurvature u t := by
    rw [← iteratedDeriv_two_thetaCuspReflectedSourceOddParityWall]
    exact second_iteratedDeriv_nonneg_of_isLocalMin
      (contDiff_two_thetaCuspReflectedSourceOddParityWall u) hlocal
  exact ⟨t, htpos, htneg, hlocal, hbalance, hcurvature⟩

/-- Every negative fibre has one and the same local-minimum witness carrying stationary balance,
dyadic retention, and nonnegative second-order multiscale curvature. -/
theorem exists_thetaCuspReflectedSourceOddParityWall_stationary_curvature_retention_of_neg
    {u t₀ : ℝ} (ht₀ : 0 < t₀)
    (hneg : thetaCuspReflectedSourceOddParityWall u t₀ < 0) :
    ∃ t : ℝ, 0 < t ∧ thetaCuspReflectedSourceOddParityWall u t < 0 ∧
      IsLocalMin (thetaCuspReflectedSourceOddParityWall u) t ∧
      4 * thetaCuspReflectedSourceMiddleDrop u t *
          thetaCuspReflectedSourceDecayFlux u (2 * t) =
        thetaCuspReflectedSourceDecayFlux u t *
            (thetaCuspReflectedSourceFullDrop u t +
              2 * thetaCuspReflectedSourceMiddleDrop u t) +
          3 * thetaCuspReflectedSourceFirstDrop u t *
            thetaCuspReflectedSourceDecayFlux u (3 * t) ∧
      3 * thetaCuspReflectedSourceDecayFlux u t / 4 <
        thetaCuspReflectedSourceDecayFlux u (2 * t) ∧
      0 ≤ thetaCuspReflectedSourceOddParityWallCurvature u t := by
  rcases exists_thetaCuspReflectedSourceOddParityWall_stationary_curvature_of_neg
      ht₀ hneg with ⟨t, ht, htneg, hlocal, hbalance, hcurvature⟩
  let A : ℝ := thetaCuspReflectedSourceFirstDrop u t
  let B : ℝ := thetaCuspReflectedSourceMiddleDrop u t
  let T : ℝ := thetaCuspReflectedSourceFullDrop u t
  let D₁ : ℝ := thetaCuspReflectedSourceDecayFlux u t
  let D₂ : ℝ := thetaCuspReflectedSourceDecayFlux u (2 * t)
  let D₃ : ℝ := thetaCuspReflectedSourceDecayFlux u (3 * t)
  have hA : 0 < A := thetaCuspReflectedSourceFirstDrop_pos u ht
  have hB : 0 < B := by
    dsimp only [B, thetaCuspReflectedSourceMiddleDrop,
      thetaCuspReflectedSourceProduct]
    exact sub_pos.mpr <| strictAntiOn_thetaCuspFullSource_mul_reflect u
      (show t ∈ Ici (0 : ℝ) from ht.le)
      (show 2 * t ∈ Ici (0 : ℝ) by
        simp only [mem_Ici]
        positivity)
      (by linarith)
  have hT : 0 < T := by
    simpa only [T, thetaCuspReflectedSourceFullDrop,
      thetaCuspReflectedSourceFirstDrop] using
      (thetaCuspReflectedSourceFirstDrop_pos u
        (show 0 < 3 * t by positivity))
  have hC : 0 < thetaCuspReflectedSourceProduct u (2 * t) -
      thetaCuspReflectedSourceProduct u (3 * t) := by
    unfold thetaCuspReflectedSourceProduct
    exact sub_pos.mpr <| strictAntiOn_thetaCuspFullSource_mul_reflect u
      (show 2 * t ∈ Ici (0 : ℝ) by
        simp only [mem_Ici]
        positivity)
      (show 3 * t ∈ Ici (0 : ℝ) by
        simp only [mem_Ici]
        positivity)
      (by linarith)
  have hTB : B < T := by
    dsimp only [B, T, thetaCuspReflectedSourceMiddleDrop,
      thetaCuspReflectedSourceFullDrop] at hC ⊢
    dsimp only [A, thetaCuspReflectedSourceFirstDrop] at hA
    linarith
  have hD₁ : 0 < D₁ := thetaCuspReflectedSourceDecayFlux_pos u ht
  have hD₂ : 0 < D₂ :=
    thetaCuspReflectedSourceDecayFlux_pos u (by positivity)
  have hD₃ : 0 < D₃ :=
    thetaCuspReflectedSourceDecayFlux_pos u (by positivity)
  have hright : B * (3 * D₁) <
      D₁ * (T + 2 * B) + 3 * A * D₃ := by
    nlinarith [mul_pos hD₁ (sub_pos.mpr hTB), mul_pos hA hD₃]
  have hbalanceLocal :
      4 * B * D₂ = D₁ * (T + 2 * B) + 3 * A * D₃ := by
    simpa only [A, B, T, D₁, D₂, D₃] using hbalance
  have hproduct : B * (3 * D₁) < B * (4 * D₂) := by
    calc
      B * (3 * D₁) < D₁ * (T + 2 * B) + 3 * A * D₃ := hright
      _ = 4 * B * D₂ := hbalanceLocal.symm
      _ = B * (4 * D₂) := by ring
  have hlinear : 3 * D₁ < 4 * D₂ := by
    by_contra hnot
    have hge : 4 * D₂ ≤ 3 * D₁ := le_of_not_gt hnot
    have hmul : B * (4 * D₂) ≤ B * (3 * D₁) :=
      mul_le_mul_of_nonneg_left hge hB.le
    exact (not_lt_of_ge hmul) hproduct
  refine ⟨t, ht, htneg, hlocal, hbalance, ?_, hcurvature⟩
  dsimp only [D₁, D₂] at hlinear ⊢
  linarith

/-- Unconditional second-order classification of the literal source-fibre wall. -/
theorem thetaCuspReflectedSourceOddParityWall_global_or_stationary_curvature_obstruction
    (u : ℝ) :
    (∀ t : ℝ, 0 < t → 0 ≤ thetaCuspReflectedSourceOddParityWall u t) ∨
      ∃ t : ℝ, 0 < t ∧ thetaCuspReflectedSourceOddParityWall u t < 0 ∧
        IsLocalMin (thetaCuspReflectedSourceOddParityWall u) t ∧
        4 * thetaCuspReflectedSourceMiddleDrop u t *
            thetaCuspReflectedSourceDecayFlux u (2 * t) =
          thetaCuspReflectedSourceDecayFlux u t *
              (thetaCuspReflectedSourceFullDrop u t +
                2 * thetaCuspReflectedSourceMiddleDrop u t) +
            3 * thetaCuspReflectedSourceFirstDrop u t *
              thetaCuspReflectedSourceDecayFlux u (3 * t) ∧
        3 * thetaCuspReflectedSourceDecayFlux u t / 4 <
          thetaCuspReflectedSourceDecayFlux u (2 * t) ∧
        0 ≤ thetaCuspReflectedSourceOddParityWallCurvature u t := by
  by_cases hglobal :
      ∀ t : ℝ, 0 < t → 0 ≤ thetaCuspReflectedSourceOddParityWall u t
  · exact Or.inl hglobal
  · right
    push Not at hglobal
    rcases hglobal with ⟨t, ht, hneg⟩
    exact
      exists_thetaCuspReflectedSourceOddParityWall_stationary_curvature_retention_of_neg
        ht hneg

end

end RHTower
