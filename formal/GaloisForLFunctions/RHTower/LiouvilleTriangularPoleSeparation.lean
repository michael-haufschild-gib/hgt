import GaloisForLFunctions.RHTower.HardyTheorem
import GaloisForLFunctions.RHTower.XiEntireReal
import GaloisForLFunctions.RHTower.ZetaLogDerivResidue

/-!
# Pole separation for the short triangular Möbius head

The affine map `rho ↦ (rho+1)/2` cannot preserve all zeta zeros in the closed
right half of the critical strip: its iterates tend to the nonzero residue unit
at one. Starting with a critical zero therefore gives a shifted zero with real
part at least three quarters where the two other triangular-transform zeta
factors are nonzero.

At this point the complete three-term pole model is analytic exactly when the
coefficient of the shifted short-head term vanishes. Its other coefficients are
arbitrary. Adding an analytic remainder cannot change this local obstruction.
-/

open Complex Filter Topology Set

namespace RHTower.LiouvilleTriangularPoleSeparation
noncomputable section


private theorem unit_zero {z : ℂ} (hz : riemannZeta z = 0) :
    RHTower.zetaResidueUnit z = 0 := by
  have hz1 : z ≠ 1 := riemannZeta_zero_ne_one hz
  simp [RHTower.zetaResidueUnit, Function.update_of_ne hz1, hz]

private theorem critical_zero :
    ∃ z : ℂ, riemannZeta z = 0 ∧ z.re = 1 / 2 ∧ z.im ≠ 0 := by
  obtain ⟨t, ht, hzero⟩ := RHTower.exists_Xi_zero_gt 1
  refine ⟨1 / 2 + (t : ℂ) * I, ?_, by simp, ?_⟩
  · apply RHTower.riemannZeta_eq_zero_iff_xi_or_trivial.mpr
    apply Or.inl
    change RHTower.XiC (t : ℂ) = 0
    rw [RHTower.XiC_ofReal, hzero]
    simp
  · simp
    linarith

/-- A zeta zero whose affine half-shift is not another zeta zero. -/
private theorem exists_separated_zero :
    ∃ z : ℂ, riemannZeta z = 0 ∧ 1 / 2 ≤ z.re ∧ z.re < 1 ∧ z.im ≠ 0 ∧
      riemannZeta ((z + 1) / 2) ≠ 0 := by
  by_contra hnone
  have hstep : ∀ z : ℂ, riemannZeta z = 0 → 1 / 2 ≤ z.re → z.re < 1 →
      z.im ≠ 0 → riemannZeta ((z + 1) / 2) = 0 := by
    intro z hz hlow hu him
    by_contra hne
    exact hnone ⟨z, hz, hlow, hu, him, hne⟩
  obtain ⟨z, hz, hre, him⟩ := critical_zero
  let p : ℕ → ℝ := fun n => (1 / 2 : ℝ)^n
  let r : ℕ → ℂ := fun n => 1 + (z - 1) * (p n : ℂ)
  have hp : ∀ n, 0 < p n ∧ p n ≤ 1 := by
    intro n
    exact ⟨pow_pos (by norm_num) _, pow_le_one₀ (by norm_num) (by norm_num)⟩
  have hrre : ∀ n, (r n).re = 1 - p n / 2 := by
    intro n
    simp [r, hre]
    ring
  have hrim : ∀ n, (r n).im = z.im * p n := by
    intro n
    simp [r]
  have hrlo : ∀ n, 1 / 2 ≤ (r n).re := by
    intro n
    rw [hrre]
    have := (hp n).2
    linarith
  have hrhi : ∀ n, (r n).re < 1 := by
    intro n
    rw [hrre]
    have := (hp n).1
    linarith
  have hrimne : ∀ n, (r n).im ≠ 0 := by
    intro n
    rw [hrim]
    exact mul_ne_zero him (hp n).1.ne'
  have hrnext : ∀ n, r (n+1) = (r n + 1) / 2 := by
    intro n
    simp only [r, p, pow_succ, Complex.ofReal_mul, Complex.ofReal_div,
      Complex.ofReal_one, Complex.ofReal_ofNat]
    ring
  have hrzero : ∀ n, riemannZeta (r n) = 0 := by
    intro n
    induction n with
    | zero => simpa [r, p] using hz
    | succ n ih =>
      rw [hrnext]
      exact hstep _ ih (hrlo n) (hrhi n) (hrimne n)
  have hp0 : Tendsto p atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hr1 : Tendsto r atTop (𝓝 1) := by
    have hc : Tendsto (fun n => (p n : ℂ)) atTop (𝓝 0) :=
      Complex.continuous_ofReal.continuousAt.tendsto.comp hp0
    simpa [r] using tendsto_const_nhds.add (tendsto_const_nhds.mul hc)
  have hu1 := (RHTower.analyticAt_zetaResidueUnit 1).continuousAt.tendsto.comp hr1
  have hu0 : Tendsto (fun n => RHTower.zetaResidueUnit (r n)) atTop (𝓝 0) := by
    have he : (fun n => RHTower.zetaResidueUnit (r n)) = fun _ : ℕ => (0 : ℂ) :=
      funext fun n => unit_zero (hrzero n)
    rw [he]
    exact tendsto_const_nhds
  have he := tendsto_nhds_unique hu1 hu0
  simp at he

/-- The short-head denominator has a zero at or to the right of three quarters while both other
zeta denominators of the triangular transform are nonzero. -/
theorem exists_separated_pole :
    ∃ w : ℂ, 3 / 4 ≤ w.re ∧ w.re < 1 ∧ w.im ≠ 0 ∧
      riemannZeta (2*w-1) = 0 ∧ riemannZeta w ≠ 0 ∧
      riemannZeta (2*w-1/2) ≠ 0 := by
  obtain ⟨z,hz,hlo,hhi,him,hsep⟩ := exists_separated_zero
  let w : ℂ := (z+1)/2
  have hwre : w.re = (z.re+1)/2 := by simp [w]
  have hwim : w.im = z.im/2 := by simp [w]
  refine ⟨w, ?_, ?_, ?_, ?_, hsep, ?_⟩
  · rw [hwre]; linarith
  · rw [hwre]; linarith
  · rw [hwim]; exact div_ne_zero him (by norm_num)
  · have he : 2*w-1 = z := by dsimp [w]; ring
    rwa [he]
  · have he : 2*w-1/2 = z+1/2 := by dsimp [w]; ring
    rw [he]
    apply riemannZeta_ne_zero_of_one_le_re
    simp
    linarith



private theorem not_continuous_inverse_shifted_unit {w : ℂ}
    (hw : RHTower.zetaResidueUnit (2*w-1) = 0) :
    ¬ ContinuousAt (fun z : ℂ => (RHTower.zetaResidueUnit (2*z-1))⁻¹) w := by
  let f : ℂ → ℂ := fun z => RHTower.zetaResidueUnit (2*z-1)
  have hf : AnalyticOnNhd ℂ f Set.univ := by
    intro z _
    exact (RHTower.analyticAt_zetaResidueUnit _).comp (by fun_prop)
  have hnot : ¬ ∀ᶠ z in 𝓝 w, f z = 0 := by
    intro hzero
    have hall := hf.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      isPreconnected_univ (mem_univ w) hzero
    have h := hall (mem_univ (1 : ℂ))
    norm_num [f] at h
  have hpun := ((hf w (mem_univ w)).eventually_eq_zero_or_eventually_ne_zero).resolve_left hnot
  intro hcont
  have hprod : ContinuousAt (fun z => f z * (f z)⁻¹) w :=
    (hf w (mem_univ w)).continuousAt.mul hcont
  have hlim : Tendsto (fun z => f z * (f z)⁻¹) (𝓝[≠] w) (𝓝 0) := by
    simpa [f, hw] using hprod.tendsto.mono_left nhdsWithin_le_nhds
  have hone : Tendsto (fun z => f z * (f z)⁻¹) (𝓝[≠] w) (𝓝 1) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hpun] with z hz
    exact (mul_inv_cancel₀ hz).symm
  have he := tendsto_nhds_unique hlim hone
  exact zero_ne_one he

/-- The three non-remainder terms in the triangular source transform,
written with the entire zeta residue unit. -/
def poleModel (a b d : ℂ) (z : ℂ) : ℂ :=
  d * riemannZeta (2*z) / (z * RHTower.zetaResidueUnit z) +
    a / RHTower.zetaResidueUnit (2*z-1) +
    b * (2*z-3/2) / ((z-1/2) * RHTower.zetaResidueUnit (2*z-1/2))

/-- At one actual shifted zeta zero, the three-term transform is analytic
exactly when its short-head pole coefficient vanishes. -/
theorem exists_pole_coefficient_rigidity :
    ∃ w : ℂ, 3/4 ≤ w.re ∧ w.re < 1 ∧ w.im ≠ 0 ∧
      ∀ a b d : ℂ, AnalyticAt ℂ (poleModel a b d) w ↔ a = 0 := by
  obtain ⟨w, hlo, hhi, him, hz, hwz, hvz⟩ := exists_separated_pole
  have hw0 : w ≠ 0 := by intro h; simp [h] at hlo; norm_num at hlo
  have hw1 : w ≠ 1 := by intro h; simp [h] at hhi
  have hwh : w-1/2 ≠ 0 := by
    intro h
    have hr := congrArg Complex.re h
    simp at hr
    linarith
  have hv1 : 2*w-1/2 ≠ 1 := by
    intro h
    have hi := congrArg Complex.im h
    simp at hi
    exact him (by linarith)
  have h2w1 : 2*w ≠ 1 := by
    intro h
    have hr := congrArg Complex.re h
    simp at hr
    linarith
  have hUw : RHTower.zetaResidueUnit w ≠ 0 := by
    rw [RHTower.zetaResidueUnit, Function.update_of_ne hw1]
    exact mul_ne_zero (sub_ne_zero.mpr hw1) hwz
  have hUv : RHTower.zetaResidueUnit (2*w-1/2) ≠ 0 := by
    rw [RHTower.zetaResidueUnit, Function.update_of_ne hv1]
    exact mul_ne_zero (sub_ne_zero.mpr hv1) hvz
  have hUzero := unit_zero hz
  refine ⟨w,hlo,hhi,him,?_⟩
  intro a b d
  let g : ℂ → ℂ := fun z =>
    d * riemannZeta (2*z) / (z * RHTower.zetaResidueUnit z) +
    b * (2*z-3/2) / ((z-1/2) * RHTower.zetaResidueUnit (2*z-1/2))
  have hg : AnalyticAt ℂ g w := by
    have hZ : AnalyticAt ℂ (fun z : ℂ => riemannZeta (2*z)) w :=
      (analyticOn_riemannZeta _ h2w1).comp (by fun_prop)
    have hU : AnalyticAt ℂ (fun z : ℂ => RHTower.zetaResidueUnit (2*z-1/2)) w :=
      (RHTower.analyticAt_zetaResidueUnit _).comp (by fun_prop)
    exact ((analyticAt_const.mul hZ).div
      (analyticAt_id.mul (RHTower.analyticAt_zetaResidueUnit w)) (mul_ne_zero hw0 hUw)).add
      ((analyticAt_const.mul (by fun_prop)).div
        ((analyticAt_id.sub analyticAt_const).mul hU) (mul_ne_zero hwh hUv))
  constructor
  · intro ha
    by_contra hane
    have heq : (fun z => (poleModel a b d z - g z) / a) =
        fun z => (RHTower.zetaResidueUnit (2*z-1))⁻¹ := by
      funext z
      dsimp [poleModel, g]
      field_simp
      ring
    have hc : AnalyticAt ℂ (fun z => (poleModel a b d z - g z) / a) w :=
      (ha.sub hg).div_const
    rw [heq] at hc
    exact not_continuous_inverse_shifted_unit hUzero hc.continuousAt
  · rintro rfl
    have heq : poleModel 0 b d = g := by
      funext z
      simp [poleModel, g]
    rw [heq]
    exact hg

end
end RHTower.LiouvilleTriangularPoleSeparation
