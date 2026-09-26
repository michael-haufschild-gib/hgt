import GaloisForLFunctions.RHTower.CircleSeamModulusMargin
import GaloisForLFunctions.RHTower.CircleLinearPhaseSeamMargin
import GaloisForLFunctions.RHTower.XiRightDiscPhaseIndexRiemannHypothesis
import GaloisForLFunctions.HTGeometry.BallLogarithm

/-!
# Seam margin of `xi` on zero-free discs: the boundary modulus ratio

On every closed disc on which `xi` has no zero, the adjoint Hankel seam of the `xi` boundary phase
satisfies

`1 − ‖(1 − P) U† P‖² ≥ m / M`   whenever `m ≤ |xi| ≤ M` on the boundary circle

(`xiDisc_one_sub_seam_sq_ge`).  Construction: zero-freeness on the closed disc extends to a
concentric open disc (compactness).  There `xi = xi(c) · exp(L)` with `L` holomorphic, so in disc
coordinates `xi(c + t w) = κ exp Ψ(w)` with `κ = |xi(c)|`.  The functions `h = exp(Ψ/2)` and
`h⁻¹ = exp(−Ψ/2)` are holomorphic on a larger disc, so their boundary values have no negative
Fourier modes.  The conjugate phase is `conj(h) · h⁻¹`, and `|h|² = |xi|/κ`.
`SeamModulusMargin.norm_sq_adjointSeam_le_of_outer_factor` with `A = √(M/κ)` and `B = √(κ/m)`
gives the bound.
-/

noncomputable section

open Complex Metric Filter Topology MeasureTheory

namespace RHTower

namespace XiSeamModulusMargin

open LinearPhaseSeam hiding e

local notation "𝕖" => LinearPhaseSeam.e

/-- The unit-circle datum of a holomorphic nonvanishing function on `ball 0 R`, `R > 1`. -/
def unitDatum {R : ℝ} (hR : 1 < R) (F : ℂ → ℂ)
    (hF : DifferentiableOn ℂ F (ball (0 : ℂ) R)) (hne : ∀ w, F w ≠ 0) : DiscArgumentDatum where
  c := 0
  t := 1
  R := (1 + R) / 2
  U := ball 0 R
  F := F
  t_pos := one_pos
  t_lt_R := by linarith
  isOpen := isOpen_ball
  closedBall_subset := closedBall_subset_ball (by linarith)
  differentiableOn := hF
  ne_zero := fun w _ => hne w

theorem unitDatum_value {R : ℝ} (hR : 1 < R) (F : ℂ → ℂ)
    (hF : DifferentiableOn ℂ F (ball (0 : ℂ) R)) (hne : ∀ w, F w ≠ 0) (x : ℝ) :
    (unitDatum hR F hF hne).value x = F (𝕖 x) := by
  simp [unitDatum, DiscArgumentDatum.value, DiscArgumentDatum.boundary, LinearPhaseSeam.e]

/-- A bounded circle symbol from a continuous periodic function with an explicit bound. -/
def liftSymbol (f : ℝ → ℂ) (hper : Function.Periodic f 1) (hc : Continuous f) (B : ℝ)
    (hB0 : 0 ≤ B) (hB : ∀ x, ‖f x‖ ≤ B) : CCMCircleBoundedSymbol where
  toFun := circleLift f
  bound := B
  bound_nonneg := hB0
  measurable := (continuous_circleLift hper hc).measurable
  norm_le z := by
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective z
    rw [circleLift_coe hper]
    exact hB x

theorem continuous_e : Continuous (fun x : ℝ => 𝕖 x) :=
  (continuous_circleMap 0 1).comp (continuous_const.mul continuous_id)

/-- **Seam margin on a zero-free disc.** -/
theorem xiDisc_one_sub_seam_sq_ge (c : ℂ) (t : ℝ) (ht : 0 < t)
    (hne : ∀ ζ ∈ sphere c t, xi ζ ≠ 0) (hzero : ∀ z ∈ closedBall c t, xi z ≠ 0)
    {m M : ℝ} (hm : 0 < m) (hbounds : ∀ ζ ∈ sphere c t, m ≤ ‖xi ζ‖ ∧ ‖xi ζ‖ ≤ M) :
    m / M ≤ 1 - ‖(xiDiscDatum c t ht hne).circlePhase.datum.adjointHankelSeam‖ ^ 2 := by
  -- zero-free on a larger open disc
  have hopen : IsOpen {z : ℂ | xi z ≠ 0} := isOpen_ne_fun xi_differentiable.continuous
    continuous_const
  obtain ⟨δ, hδ, hsub⟩ := (isCompact_closedBall c t).exists_thickening_subset_open hopen
    (fun z hz => hzero z hz)
  rw [thickening_closedBall hδ ht.le] at hsub
  have hball : ∀ z ∈ ball c (δ + t), xi z ≠ 0 := fun z hz => hsub hz
  obtain ⟨L, hLd, -, hLeq⟩ := GaloisForLFunctions.HTGeometry.exists_log_on_ball
    (by positivity : (0 : ℝ) < δ + t) xi_differentiable.differentiableOn hball
  set κ : ℝ := ‖xi c‖ with hκ
  have hxic : xi c ≠ 0 := hzero c (mem_closedBall_self ht.le)
  have hκpos : 0 < κ := norm_pos_iff.mpr hxic
  set R : ℝ := 1 + δ / t with hR
  have hδt : 0 < δ / t := by positivity
  have hR1 : 1 < R := by rw [hR]; linarith
  have hmap : ∀ w : ℂ, ‖w‖ < R → c + (t : ℂ) * w ∈ ball c (δ + t) := by
    intro w hw
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos ht]
    calc t * ‖w‖ < t * R := mul_lt_mul_of_pos_left hw ht
      _ = δ + t := by rw [hR]; field_simp; ring
  set Ψ : ℂ → ℂ := fun w => ((Complex.arg (xi c) : ℝ) : ℂ) * I + L (c + (t : ℂ) * w) with hΨ
  have hΨd : DifferentiableOn ℂ Ψ (ball (0 : ℂ) R) := by
    intro w hw
    rw [mem_ball, dist_zero_right] at hw
    have hmem := hmap w hw
    exact ((differentiableAt_const _).add ((hLd.differentiableAt (isOpen_ball.mem_nhds hmem)).comp
      w ((differentiableAt_const _).add ((differentiableAt_const _).mul differentiableAt_id)))
      ).differentiableWithinAt
  have hxiΨ : ∀ w : ℂ, ‖w‖ < R → xi (c + (t : ℂ) * w) = (κ : ℂ) * Complex.exp (Ψ w) := by
    intro w hw
    rw [hLeq _ (hmap w hw), hΨ]
    simp only
    rw [Complex.exp_add, ← mul_assoc, hκ, Complex.norm_mul_exp_arg_mul_I]
  -- the two holomorphic square roots
  set H : ℂ → ℂ := fun w => Complex.exp (Ψ w / 2) with hH
  set Hi : ℂ → ℂ := fun w => Complex.exp (-(Ψ w / 2)) with hHi
  have hHd : DifferentiableOn ℂ H (ball (0 : ℂ) R) := fun w hw =>
    ((hΨd w hw).div_const 2).cexp
  have hHid : DifferentiableOn ℂ Hi (ball (0 : ℂ) R) := fun w hw =>
    ((hΨd w hw).div_const 2).neg.cexp
  set DH := unitDatum hR1 H hHd (fun w => Complex.exp_ne_zero _) with hDH
  set DHi := unitDatum hR1 Hi hHid (fun w => Complex.exp_ne_zero _) with hDHi
  have hvH : ∀ x, DH.value x = H (𝕖 x) := unitDatum_value hR1 H hHd _
  have hvHi : ∀ x, DHi.value x = Hi (𝕖 x) := unitDatum_value hR1 Hi hHid _
  have he_lt : ∀ x, ‖𝕖 x‖ < R := fun x => by rw [norm_e]; exact hR1
  -- modulus of `H` on the circle
  have hnormH : ∀ x, ‖H (𝕖 x)‖ ^ 2 = ‖xi (c + (t : ℂ) * 𝕖 x)‖ / κ := by
    intro x
    rw [hxiΨ _ (he_lt x), norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hκpos]
    have : ‖H (𝕖 x)‖ ^ 2 = ‖Complex.exp (Ψ (𝕖 x))‖ := by
      rw [hH, pow_two, ← norm_mul, ← Complex.exp_add]; congr 2; ring
    rw [this]; field_simp
  have hsphere : ∀ x, c + (t : ℂ) * 𝕖 x ∈ sphere c t := by
    intro x
    rw [mem_sphere, dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos ht, norm_e, mul_one]
  have hMpos : 0 < M := lt_of_lt_of_le hm (le_trans (hbounds _ (hsphere 0)).1
    (hbounds _ (hsphere 0)).2)
  set A : ℝ := Real.sqrt (M / κ) with hA
  set B : ℝ := Real.sqrt (κ / m) with hB
  have hHbound : ∀ x, ‖DH.value x‖ ≤ A := by
    intro x
    rw [hvH, hA, ← Real.sqrt_sq (norm_nonneg _), hnormH]
    apply Real.sqrt_le_sqrt
    exact div_le_div_of_nonneg_right (hbounds _ (hsphere x)).2 hκpos.le
  have hHiH : ∀ w, Hi w * H w = 1 := by
    intro w; rw [hHi, hH, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero]
  have hHibound : ∀ x, ‖DHi.value x‖ ≤ B := by
    intro x
    rw [hvHi]
    have hprod : ‖Hi (𝕖 x)‖ * ‖H (𝕖 x)‖ = 1 := by rw [← norm_mul, hHiH, norm_one]
    have hHpos : 0 < ‖H (𝕖 x)‖ := norm_pos_iff.mpr (Complex.exp_ne_zero _)
    have hsq : ‖Hi (𝕖 x)‖ ^ 2 = κ / ‖xi (c + (t : ℂ) * 𝕖 x)‖ := by
      have h1 : ‖Hi (𝕖 x)‖ = 1 / ‖H (𝕖 x)‖ := by field_simp; linarith [hprod]
      rw [h1, div_pow, one_pow, hnormH]
      have : 0 < ‖xi (c + (t : ℂ) * 𝕖 x)‖ := lt_of_lt_of_le hm (hbounds _ (hsphere x)).1
      field_simp
    rw [hB, ← Real.sqrt_sq (norm_nonneg _), hsq]
    apply Real.sqrt_le_sqrt
    exact div_le_div_of_nonneg_left hκpos.le hm (hbounds _ (hsphere x)).1
  -- the four symbols
  have hcontH := DH.contDiff_value.continuous
  have hcontHi := DHi.contDiff_value.continuous
  set sH := liftSymbol DH.value DH.periodic_value hcontH A (Real.sqrt_nonneg _) hHbound
  set sHi := liftSymbol DHi.value DHi.periodic_value hcontHi B (Real.sqrt_nonneg _) hHibound
  set sHc := liftSymbol (fun x => starRingEnd ℂ (DH.value x))
    (fun x => by simp only [DH.periodic_value x]) (Complex.continuous_conj.comp hcontH) A
    (Real.sqrt_nonneg _) (fun x => by rw [Complex.norm_conj]; exact hHbound x)
  set sHic := liftSymbol (fun x => starRingEnd ℂ (DHi.value x))
    (fun x => by simp only [DHi.periodic_value x]) (Complex.continuous_conj.comp hcontHi) B
    (Real.sqrt_nonneg _) (fun x => by rw [Complex.norm_conj]; exact hHibound x)
  have hper_c : Function.Periodic (fun x => starRingEnd ℂ (DH.value x)) 1 :=
    fun x => by simp only [DH.periodic_value x]
  have hper_ic : Function.Periodic (fun x => starRingEnd ℂ (DHi.value x)) 1 :=
    fun x => by simp only [DHi.periodic_value x]
  have hc_eq : ∀ z, sHc.toFun z = starRingEnd ℂ (sH.toFun z) := by
    intro z
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective z
    show circleLift (fun x => starRingEnd ℂ (DH.value x)) (x : AddCircle (1 : ℝ)) =
      starRingEnd ℂ (circleLift DH.value (x : AddCircle (1 : ℝ)))
    rw [circleLift_coe hper_c, circleLift_coe DH.periodic_value]
  have hic_eq : ∀ z, sHic.toFun z = starRingEnd ℂ (sHi.toFun z) := by
    intro z
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective z
    show circleLift (fun x => starRingEnd ℂ (DHi.value x)) (x : AddCircle (1 : ℝ)) =
      starRingEnd ℂ (circleLift DHi.value (x : AddCircle (1 : ℝ)))
    rw [circleLift_coe hper_ic, circleLift_coe DHi.periodic_value]
  have hinv : ∀ z, sH.toFun z * sHi.toFun z = 1 := by
    intro z
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective z
    change circleLift _ _ * circleLift _ _ = 1
    rw [circleLift_coe DH.periodic_value, circleLift_coe DHi.periodic_value, hvH, hvHi,
      mul_comm, hHiH]
  have hneg_H : ∀ n : ℤ, n < 0 → fourierCoeff sH.toFun n = 0 :=
    fun n hn => DH.fourierCoeff_circleLift_value_of_neg hn
  have hneg_Hi : ∀ n : ℤ, n < 0 → fourierCoeff sHi.toFun n = 0 :=
    fun n hn => DHi.fourierCoeff_circleLift_value_of_neg hn
  -- the phase identity
  set D := xiDiscDatum c t ht hne with hD
  have hval : ∀ x, D.value x = (κ : ℂ) * (H (𝕖 x) * H (𝕖 x)) := by
    intro x
    have hbd : D.boundary x = c + (t : ℂ) * 𝕖 x := by
      simp [hD, DiscArgumentDatum.boundary, xiDiscDatum, LinearPhaseSeam.e, circleMap]
    rw [DiscArgumentDatum.value, hbd, show D.F = xi from rfl, hxiΨ _ (he_lt x), hH,
      ← Complex.exp_add]
    congr 2; ring
  have hphase : ∀ x, starRingEnd ℂ (D.phase x) =
      starRingEnd ℂ (H (𝕖 x)) * Hi (𝕖 x) := by
    intro x
    set Hx := H (𝕖 x)
    have hHx : Hx ≠ 0 := Complex.exp_ne_zero _
    have hcHx : starRingEnd ℂ Hx ≠ 0 := (map_ne_zero _).mpr hHx
    have hHix : Hi (𝕖 x) = Hx⁻¹ := by
      have := hHiH (𝕖 x)
      exact eq_inv_of_mul_eq_one_left this
    have hmod : ((D.modulus x : ℝ) : ℂ) = (κ : ℂ) * (Hx * starRingEnd ℂ Hx) := by
      rw [DiscArgumentDatum.modulus, hval, norm_mul, norm_mul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hκpos, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      push_cast; ring
    have hκ' : (κ : ℂ) ≠ 0 := ofReal_ne_zero.mpr hκpos.ne'
    rw [DiscArgumentDatum.phase, hmod, hval, hHix]
    simp only [map_mul, map_inv₀, Complex.conj_ofReal, Complex.conj_conj]
    field_simp
    rfl
  have hu : ∀ z, starRingEnd ℂ (D.circlePhase.toFun z) = sHc.toFun z * sHi.toFun z := by
    intro z
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective z
    rw [DiscArgumentDatum.circlePhase_toFun, circleLift_coe D.periodic_phase]
    change _ = circleLift _ _ * circleLift _ _
    rw [circleLift_coe hper_c, circleLift_coe DHi.periodic_value, hphase x, hvH, hvHi]
  have hABpos : 0 < sH.bound * sHic.bound := by
    change 0 < A * B
    rw [hA, hB]
    exact mul_pos (Real.sqrt_pos.mpr (div_pos hMpos hκpos))
      (Real.sqrt_pos.mpr (div_pos hκpos hm))
  have hmain := SeamModulusMargin.norm_sq_adjointSeam_le_of_outer_factor D.circlePhase
    sH sHi sHc sHic hneg_H hneg_Hi hc_eq hic_eq hinv hu hABpos
  have hAB2 : (sH.bound * sHic.bound) ^ 2 = M / m := by
    change (A * B) ^ 2 = M / m
    rw [mul_pow, hA, hB, Real.sq_sqrt (div_pos hMpos hκpos).le,
      Real.sq_sqrt (div_pos hκpos hm).le]
    field_simp
  rw [hAB2] at hmain
  have : 1 / (M / m) = m / M := by field_simp
  rw [this] at hmain
  linarith

end XiSeamModulusMargin

end RHTower
