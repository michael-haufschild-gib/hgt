import GaloisForLFunctions.RHTower.XiZeroFreeDiscSeamModulusMargin
import GaloisForLFunctions.HTGeometry.ZetaTailBound

/-!
# Seam margin of a zero-free disc datum, and the height-uniform margin of `ζ`

`DiscArgumentDatum.one_sub_seam_sq_ge` states the margin law for an arbitrary disc datum.  If the
function `F` has no zero in the closed disc and `m ≤ |F| ≤ M` on the boundary circle, the adjoint
Hankel seam `(1 − P) U† P` of the boundary phase `F/|F|` satisfies `1 − ‖(1 − P) U† P‖² ≥ m/M`.  The
proof is the one for `xi` (`XiSeamModulusMargin.xiDisc_one_sub_seam_sq_ge`), with `F` in place of
`xi`.

Application to `ζ` itself (`zetaDisc_one_sub_seam_sq_ge`): on every closed disc contained in
`Re s ≥ 3`, `|ζ − 1| ≤ 4 · 2^{−Re s} ≤ 1/2`, so the seam margin of the `ζ` phase is at least `1/3`,
uniformly in the height and the radius of the disc.  For the phase of `xi` the margin of fixed-radius
discs decays with the height, through the archimedean factor.  The Gamma factor is zero-free, so it
does not change the index, but it does erode the margin.
-/

noncomputable section

open Complex Metric Filter Topology MeasureTheory

namespace RHTower

open LinearPhaseSeam hiding e

local notation "𝕖" => LinearPhaseSeam.e

/-- **Seam margin law for a zero-free disc datum.** -/
theorem DiscArgumentDatum.one_sub_seam_sq_ge (D : DiscArgumentDatum)
    (hzero : ∀ z ∈ closedBall D.c D.t, D.F z ≠ 0) {m M : ℝ} (hm : 0 < m)
    (hbounds : ∀ ζ ∈ sphere D.c D.t, m ≤ ‖D.F ζ‖ ∧ ‖D.F ζ‖ ≤ M) :
    m / M ≤ 1 - ‖D.circlePhase.datum.adjointHankelSeam‖ ^ 2 := by
  set c := D.c
  set t := D.t
  have ht : 0 < t := D.t_pos
  have hsubU : closedBall c t ⊆ D.U :=
    (closedBall_subset_closedBall D.t_lt_R.le).trans D.closedBall_subset
  have hopen : IsOpen (D.U ∩ D.F ⁻¹' {0}ᶜ) :=
    D.differentiableOn.continuousOn.isOpen_inter_preimage D.isOpen isOpen_compl_singleton
  obtain ⟨δ, hδ, hsub⟩ := (isCompact_closedBall c t).exists_thickening_subset_open hopen
    (fun z hz => ⟨hsubU hz, hzero z hz⟩)
  rw [thickening_closedBall hδ ht.le] at hsub
  have hballU : ∀ z ∈ ball c (δ + t), z ∈ D.U := fun z hz => (hsub hz).1
  have hball : ∀ z ∈ ball c (δ + t), D.F z ≠ 0 := fun z hz => (hsub hz).2
  have hFd : DifferentiableOn ℂ D.F (ball c (δ + t)) := D.differentiableOn.mono
    (fun z hz => hballU z hz)
  obtain ⟨L, hLd, -, hLeq⟩ := GaloisForLFunctions.HTGeometry.exists_log_on_ball
    (by positivity : (0 : ℝ) < δ + t) hFd hball
  set κ : ℝ := ‖D.F c‖ with hκ
  have hFc : D.F c ≠ 0 := hzero c (mem_closedBall_self ht.le)
  have hκpos : 0 < κ := norm_pos_iff.mpr hFc
  set R : ℝ := 1 + δ / t with hR
  have hδt : 0 < δ / t := by positivity
  have hR1 : 1 < R := by rw [hR]; linarith
  have hmap : ∀ w : ℂ, ‖w‖ < R → c + (t : ℂ) * w ∈ ball c (δ + t) := by
    intro w hw
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos ht]
    calc t * ‖w‖ < t * R := mul_lt_mul_of_pos_left hw ht
      _ = δ + t := by rw [hR]; field_simp; ring
  set Ψ : ℂ → ℂ := fun w => ((Complex.arg (D.F c) : ℝ) : ℂ) * I + L (c + (t : ℂ) * w) with hΨ
  have hΨd : DifferentiableOn ℂ Ψ (ball (0 : ℂ) R) := by
    intro w hw
    rw [mem_ball, dist_zero_right] at hw
    have hmem := hmap w hw
    exact ((differentiableAt_const _).add ((hLd.differentiableAt (isOpen_ball.mem_nhds hmem)).comp
      w ((differentiableAt_const _).add ((differentiableAt_const _).mul differentiableAt_id)))
      ).differentiableWithinAt
  have hFΨ : ∀ w : ℂ, ‖w‖ < R → D.F (c + (t : ℂ) * w) = (κ : ℂ) * Complex.exp (Ψ w) := by
    intro w hw
    rw [hLeq _ (hmap w hw), hΨ]
    simp only
    rw [Complex.exp_add, ← mul_assoc, hκ, Complex.norm_mul_exp_arg_mul_I]
  set H : ℂ → ℂ := fun w => Complex.exp (Ψ w / 2) with hH
  set Hi : ℂ → ℂ := fun w => Complex.exp (-(Ψ w / 2)) with hHi
  have hHd : DifferentiableOn ℂ H (ball (0 : ℂ) R) := fun w hw =>
    ((hΨd w hw).div_const 2).cexp
  have hHid : DifferentiableOn ℂ Hi (ball (0 : ℂ) R) := fun w hw =>
    ((hΨd w hw).div_const 2).neg.cexp
  set DH := XiSeamModulusMargin.unitDatum hR1 H hHd (fun w => Complex.exp_ne_zero _) with hDH
  set DHi := XiSeamModulusMargin.unitDatum hR1 Hi hHid (fun w => Complex.exp_ne_zero _) with hDHi
  have hvH : ∀ x, DH.value x = H (𝕖 x) := XiSeamModulusMargin.unitDatum_value hR1 H hHd _
  have hvHi : ∀ x, DHi.value x = Hi (𝕖 x) := XiSeamModulusMargin.unitDatum_value hR1 Hi hHid _
  have he_lt : ∀ x, ‖𝕖 x‖ < R := fun x => by rw [norm_e]; exact hR1
  have hnormH : ∀ x, ‖H (𝕖 x)‖ ^ 2 = ‖D.F (c + (t : ℂ) * 𝕖 x)‖ / κ := by
    intro x
    rw [hFΨ _ (he_lt x), norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hκpos]
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
    have hsq : ‖Hi (𝕖 x)‖ ^ 2 = κ / ‖D.F (c + (t : ℂ) * 𝕖 x)‖ := by
      have h1 : ‖Hi (𝕖 x)‖ = 1 / ‖H (𝕖 x)‖ := by field_simp; linarith [hprod]
      rw [h1, div_pow, one_pow, hnormH]
      have : 0 < ‖D.F (c + (t : ℂ) * 𝕖 x)‖ := lt_of_lt_of_le hm (hbounds _ (hsphere x)).1
      field_simp
    rw [hB, ← Real.sqrt_sq (norm_nonneg _), hsq]
    apply Real.sqrt_le_sqrt
    exact div_le_div_of_nonneg_left hκpos.le hm (hbounds _ (hsphere x)).1
  have hcontH := DH.contDiff_value.continuous
  have hcontHi := DHi.contDiff_value.continuous
  set sH := XiSeamModulusMargin.liftSymbol DH.value DH.periodic_value hcontH A
    (Real.sqrt_nonneg _) hHbound
  set sHi := XiSeamModulusMargin.liftSymbol DHi.value DHi.periodic_value hcontHi B
    (Real.sqrt_nonneg _) hHibound
  have hper_c : Function.Periodic (fun x => starRingEnd ℂ (DH.value x)) 1 :=
    fun x => by simp only [DH.periodic_value x]
  have hper_ic : Function.Periodic (fun x => starRingEnd ℂ (DHi.value x)) 1 :=
    fun x => by simp only [DHi.periodic_value x]
  set sHc := XiSeamModulusMargin.liftSymbol (fun x => starRingEnd ℂ (DH.value x)) hper_c
    (Complex.continuous_conj.comp hcontH) A (Real.sqrt_nonneg _)
    (fun x => by rw [Complex.norm_conj]; exact hHbound x)
  set sHic := XiSeamModulusMargin.liftSymbol (fun x => starRingEnd ℂ (DHi.value x)) hper_ic
    (Complex.continuous_conj.comp hcontHi) B (Real.sqrt_nonneg _)
    (fun x => by rw [Complex.norm_conj]; exact hHibound x)
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
    show circleLift DH.value (x : AddCircle (1 : ℝ)) *
      circleLift DHi.value (x : AddCircle (1 : ℝ)) = 1
    rw [circleLift_coe DH.periodic_value, circleLift_coe DHi.periodic_value, hvH, hvHi,
      mul_comm, hHiH]
  have hneg_H : ∀ n : ℤ, n < 0 → fourierCoeff sH.toFun n = 0 :=
    fun n hn => DH.fourierCoeff_circleLift_value_of_neg hn
  have hneg_Hi : ∀ n : ℤ, n < 0 → fourierCoeff sHi.toFun n = 0 :=
    fun n hn => DHi.fourierCoeff_circleLift_value_of_neg hn
  have hval : ∀ x, D.value x = (κ : ℂ) * (H (𝕖 x) * H (𝕖 x)) := by
    intro x
    have hbd : D.boundary x = c + (t : ℂ) * 𝕖 x := by
      simp [DiscArgumentDatum.boundary, LinearPhaseSeam.e, circleMap, c, t]
    rw [DiscArgumentDatum.value, hbd, hFΨ _ (he_lt x), hH, ← Complex.exp_add]
    congr 2; ring
  have hphase : ∀ x, starRingEnd ℂ (D.phase x) =
      starRingEnd ℂ (H (𝕖 x)) * Hi (𝕖 x) := by
    intro x
    set Hx := H (𝕖 x)
    have hHx : Hx ≠ 0 := Complex.exp_ne_zero _
    have hcHx : starRingEnd ℂ Hx ≠ 0 := (map_ne_zero _).mpr hHx
    have hHix : Hi (𝕖 x) = Hx⁻¹ := eq_inv_of_mul_eq_one_left (hHiH (𝕖 x))
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
    show _ = circleLift (fun x => starRingEnd ℂ (DH.value x)) (x : AddCircle (1 : ℝ)) *
      circleLift DHi.value (x : AddCircle (1 : ℝ))
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

/-! ## The `ζ` phase far right -/

/-- The disc datum of `ζ` on a disc contained in `Re s ≥ 3`. -/
def zetaDiscDatum (c : ℂ) (t : ℝ) (ht : 0 < t) (hc : 3 + t ≤ c.re) : DiscArgumentDatum where
  c := c
  t := t
  R := t + 1 / 4
  U := {s : ℂ | 5 / 2 < s.re}
  F := riemannZeta
  t_pos := ht
  t_lt_R := by linarith
  isOpen := isOpen_lt continuous_const Complex.continuous_re
  closedBall_subset := by
    intro z hz
    rw [mem_closedBall, dist_eq_norm] at hz
    have h1 : |(z - c).re| ≤ ‖z - c‖ := Complex.abs_re_le_norm _
    rw [Complex.sub_re] at h1
    have h2 := neg_abs_le (z.re - c.re)
    show 5 / 2 < z.re
    linarith
  differentiableOn := fun s hs => by
    have hs1 : s ≠ 1 := by
      intro h; rw [h] at hs; simp at hs; linarith
    exact (differentiableAt_riemannZeta hs1).differentiableWithinAt
  ne_zero := fun ζ hζ => by
    apply riemannZeta_ne_zero_of_one_lt_re
    rw [mem_sphere, dist_eq_norm] at hζ
    have h1 : |(ζ - c).re| ≤ ‖ζ - c‖ := Complex.abs_re_le_norm _
    rw [Complex.sub_re] at h1
    have h2 := neg_abs_le (ζ.re - c.re)
    linarith

theorem norm_riemannZeta_bounds_of_three_le {s : ℂ} (hs : 3 ≤ s.re) :
    1 / 2 ≤ ‖riemannZeta s‖ ∧ ‖riemannZeta s‖ ≤ 3 / 2 := by
  have h := GaloisForLFunctions.HTGeometry.norm_riemannZeta_sub_one_le_rpow (s := s) (by linarith)
  have h2 : (4 : ℝ) * (2 : ℝ) ^ (-s.re) ≤ 1 / 2 := by
    have h3 : (2 : ℝ) ^ (-s.re) ≤ (2 : ℝ) ^ (-(3 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    have h4 : (2 : ℝ) ^ (-(3 : ℝ)) = 1 / 8 := by
      rw [Real.rpow_neg (by norm_num)]; norm_num
    rw [h4] at h3
    linarith
  have hle : ‖riemannZeta s - 1‖ ≤ 1 / 2 := le_trans h h2
  constructor
  · have := norm_sub_norm_le (1 : ℂ) (riemannZeta s)
    rw [norm_sub_rev, norm_one] at this
    linarith
  · have := norm_sub_norm_le (riemannZeta s) 1
    rw [norm_one] at this
    linarith

/-- **Height-uniform seam margin for the `ζ` phase.**  On every closed disc contained in
`Re s ≥ 3`, the adjoint seam of the boundary phase of `ζ` satisfies `1 − ‖(1 − P) U† P‖² ≥ 1/3`,
uniformly in the centre (in particular the height) and the radius. -/
theorem zetaDisc_one_sub_seam_sq_ge (c : ℂ) (t : ℝ) (ht : 0 < t) (hc : 3 + t ≤ c.re) :
    1 / 3 ≤ 1 - ‖(zetaDiscDatum c t ht hc).circlePhase.datum.adjointHankelSeam‖ ^ 2 := by
  have hre : ∀ z ∈ closedBall c t, 3 ≤ z.re := by
    intro z hz
    rw [mem_closedBall, dist_eq_norm] at hz
    have h1 : |(z - c).re| ≤ ‖z - c‖ := Complex.abs_re_le_norm _
    rw [Complex.sub_re] at h1
    have h2 := neg_abs_le (z.re - c.re)
    linarith
  have h := (zetaDiscDatum c t ht hc).one_sub_seam_sq_ge
    (fun z hz => riemannZeta_ne_zero_of_one_lt_re (by linarith [hre z hz]))
    (m := 1 / 2) (M := 3 / 2) (by norm_num)
    (fun ζ hζ => norm_riemannZeta_bounds_of_three_le (hre ζ (sphere_subset_closedBall hζ)))
  have : (1 / 2 : ℝ) / (3 / 2) = 1 / 3 := by norm_num
  rw [this] at h
  exact h

end RHTower
