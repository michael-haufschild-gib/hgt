import GaloisForLFunctions.HTGeometry.StrelitzLogJetReduction
import GaloisForLFunctions.HTGeometry.SecondDerivativeWimanValironAsymptotic
import GaloisForLFunctions.HTGeometry.CentralIndexGrowthWall
import GaloisForLFunctions.HTGeometry.NevanlinnaCoeffFun

/-!
# Wiman--Valiron asymptotics in Strelitz logarithmic coordinates

The existing order-two Wiman--Valiron theorem controls `z f'/f` and `z² f''/f`.  The exact
logarithmic-jet identity converts those two estimates into variable-accuracy control of
`z (z f'/f)'`.  This is the quantitative input used by Strelitz's Newton-polygon argument.
-/

open MeasureTheory Complex Set Filter

namespace GaloisForLFunctions.HTGeometry

variable {a : ℕ → ℂ}

/-- **Strelitz-coordinate Wiman--Valiron asymptotic.** At arbitrarily large logarithmic radii,
the first Euler logarithmic derivative is `ε`-close to the central index and its Euler derivative
has norm at most `ε ν²`.  The value is explicitly nonzero, so both logarithmic coordinates are
literal quotients rather than totalized artifacts. -/
theorem exists_radius_point_eulerLogDerivSecond_small
    (ha : EntireCoeffs a) {n₀ : ℕ} (hn₀ : a n₀ ≠ 0)
    (htrans : ∀ M : ℕ, ∃ n, M ≤ n ∧ a n ≠ 0)
    {eps : ℝ} (heps : 0 < eps) (R : ℝ) :
    ∃ x, R ≤ x ∧ ∃ z : ℂ, ‖z‖ = Real.exp x ∧
      maxTerm a (Real.exp x) ≤ ‖coeffFun a z‖ ∧ coeffFun a z ≠ 0 ∧
      ‖eulerLogDeriv (coeffFun a) z - (centralIndex a (Real.exp x) : ℂ)‖
        ≤ eps * (centralIndex a (Real.exp x) : ℝ) ∧
      ‖eulerLogDerivSecond (coeffFun a) z‖
        ≤ eps * (centralIndex a (Real.exp x) : ℝ) ^ 2 := by
  set δ : ℝ := min 1 (eps / 5) with hδdef
  have hδpos : 0 < δ := by
    rw [hδdef]
    exact lt_min one_pos (by positivity)
  have hδone : δ ≤ 1 := by rw [hδdef]; exact min_le_left _ _
  have hδeps : 5 * δ ≤ eps := by
    have h := min_le_right (1 : ℝ) (eps / 5)
    rw [← hδdef] at h
    linarith
  have htop : Tendsto (fun x : ℝ => centralIndex a (Real.exp x)) atTop atTop :=
    (tendsto_centralIndex_atTop ha htrans).comp Real.tendsto_exp_atTop
  obtain ⟨Rν, hRν⟩ := eventually_atTop.mp (htop.eventually_ge_atTop 1)
  obtain ⟨x, hx, z, hz, hfloor, hu, hq⟩ :=
    exists_radius_point_secondDeriv_close_centralIndex ha hn₀ htrans hδpos (max R Rν)
  have hxR : R ≤ x := le_trans (le_max_left _ _) hx
  have hxRν : Rν ≤ x := le_trans (le_max_right _ _) hx
  set ν : ℝ := (centralIndex a (Real.exp x) : ℝ) with hνdef
  set νc : ℂ := (centralIndex a (Real.exp x) : ℂ) with hνcdef
  set u : ℂ := eulerLogDeriv (coeffFun a) z with hudef
  set q : ℂ := z ^ 2 * deriv (deriv (coeffFun a)) z / coeffFun a z with hqdef
  set v : ℂ := eulerLogDerivSecond (coeffFun a) z with hvdef
  have hνoneN : 1 ≤ centralIndex a (Real.exp x) := hRν x hxRν
  have hνone : (1 : ℝ) ≤ ν := by rw [hνdef]; exact_mod_cast hνoneN
  have hνnonneg : (0 : ℝ) ≤ ν := le_trans zero_le_one hνone
  have hνcnorm : ‖νc‖ = ν := by
    rw [hνcdef, hνdef, Complex.norm_natCast]
  have hfz : coeffFun a z ≠ 0 := by
    have hmu : 0 < maxTerm a (Real.exp x) := maxTerm_pos ha (Real.exp_pos x) hn₀
    exact norm_pos_iff.mp (lt_of_lt_of_le hmu hfloor)
  have huδ : ‖u - νc‖ ≤ δ * ν := by
    simpa [hudef, hνdef, hνcdef, eulerLogDeriv] using hu
  have hqδ : ‖q - νc * (νc - 1)‖ ≤ δ * ν ^ 2 := by
    simpa [hqdef, hνdef, hνcdef] using hq
  have hueps : ‖u - νc‖ ≤ eps * ν := by
    have hδε : δ ≤ eps := by linarith [hδeps]
    exact le_trans huδ (mul_le_mul_of_nonneg_right hδε hνnonneg)
  have hunorm : ‖u‖ ≤ 2 * ν := by
    have htri : ‖u‖ ≤ ‖u - νc‖ + ‖νc‖ := by
      simpa using norm_add_le (u - νc) νc
    rw [hνcnorm] at htri
    have hδν : δ * ν ≤ ν := by nlinarith
    linarith
  have hsq : ‖u ^ 2 - νc ^ 2‖ ≤ 3 * δ * ν ^ 2 := by
    have hfactor : u ^ 2 - νc ^ 2 = (u - νc) * (u + νc) := by ring
    rw [hfactor, norm_mul]
    have hplus : ‖u + νc‖ ≤ 3 * ν := by
      have htri := norm_add_le u νc
      rw [hνcnorm] at htri
      linarith
    calc
      ‖u - νc‖ * ‖u + νc‖ ≤ (δ * ν) * (3 * ν) :=
        mul_le_mul huδ hplus (norm_nonneg _) (by positivity)
      _ = 3 * δ * ν ^ 2 := by ring
  have hfAnalytic : AnalyticAt ℂ (coeffFun a) z :=
    GaloisForLFunctions.Nevanlinna.analyticOnNhd_coeffFun ha z (by simp)
  have hqv : q = v + u ^ 2 - u := by
    rw [hqdef, hvdef, hudef]
    apply (div_eq_iff hfz).2
    have h := eulerSecondDeriv_eq hfAnalytic.differentiableAt
      hfAnalytic.deriv.differentiableAt hfz
    simpa [mul_comm] using h
  have hvexpr : v =
      (q - νc * (νc - 1)) - (u ^ 2 - νc ^ 2) + (u - νc) := by
    rw [hqv]
    ring
  have hvbound : ‖v‖ ≤ δ * ν ^ 2 + 3 * δ * ν ^ 2 + δ * ν := by
    rw [hvexpr]
    calc
      ‖(q - νc * (νc - 1)) - (u ^ 2 - νc ^ 2) + (u - νc)‖
          ≤ ‖q - νc * (νc - 1)‖ + ‖u ^ 2 - νc ^ 2‖ + ‖u - νc‖ := by
            calc
              _ ≤ ‖(q - νc * (νc - 1)) - (u ^ 2 - νc ^ 2)‖ + ‖u - νc‖ :=
                norm_add_le _ _
              _ ≤ (‖q - νc * (νc - 1)‖ + ‖u ^ 2 - νc ^ 2‖) + ‖u - νc‖ := by
                gcongr
                exact norm_sub_le _ _
      _ ≤ δ * ν ^ 2 + 3 * δ * ν ^ 2 + δ * ν := by linarith
  have hδνle : δ * ν ≤ δ * ν ^ 2 := by
    have hδnonneg : 0 ≤ δ := hδpos.le
    exact mul_le_mul_of_nonneg_left (by nlinarith : ν ≤ ν ^ 2) hδnonneg
  have hvε : ‖v‖ ≤ eps * ν ^ 2 := by
    have hνsq : 0 ≤ ν ^ 2 := sq_nonneg ν
    calc
      ‖v‖ ≤ δ * ν ^ 2 + 3 * δ * ν ^ 2 + δ * ν := hvbound
      _ ≤ 5 * δ * ν ^ 2 := by linarith
      _ ≤ eps * ν ^ 2 := mul_le_mul_of_nonneg_right hδeps hνsq
  exact ⟨x, hxR, z, hz, hfloor, hfz, by simpa [hudef, hνdef, hνcdef] using hueps,
    by simpa [hvdef, hνdef] using hvε⟩

end GaloisForLFunctions.HTGeometry
