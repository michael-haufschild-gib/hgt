import GaloisForLFunctions.RHTower.DeningerMeyerAdiabatic
import GaloisForLFunctions.RHTower.DeningerPreimageMomentCLM

/-!
# The strict adiabatic Möbius preimage

For `a ≥ 0` the full all-prime inverse is

`M_a h(x) = ∑ μ(n) n⁻ᵃ h(log(nx))`.

It is constructed here without a prime cutoff.  The exact gauge factorization

`M_a h(x) = xᵃ f_(exp(-a·)h)(x)`

places it on the already formalized critical Möbius preimage domain.  This simultaneously gives
the critical value at `a = 0` and all polynomial moments for every `a ≥ 0`.
-/

namespace RHTower

open Filter Topology MeasureTheory SchwartzMap ArithmeticFunction

noncomputable section

/-- The exponentially tilted source `t ↦ exp(-a t)h(t)`. -/
def deningerAdiabaticSource (a : ℝ) (h : DeningerMeyerSource) : DeningerMeyerSource :=
  DeningerMeyerSource.toSource.symm
    (deningerExpMulLM (-a) (DeningerMeyerSource.toSource h))

@[simp]
theorem deningerAdiabaticSource_apply (a : ℝ) (h : DeningerMeyerSource) (t : ℝ) :
    (((DeningerMeyerSource.toSource (deningerAdiabaticSource a h) :
        DeningerExpSchwartz) : 𝓢(ℝ, ℂ))) t =
      ((Real.exp (-a * t) : ℝ) : ℂ) *
        (((DeningerMeyerSource.toSource h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ))) t := by
  rw [deningerAdiabaticSource, LinearEquiv.apply_symm_apply, deningerExpMulLM_apply]

@[simp]
theorem deningerAdiabaticSource_zero (h : DeningerMeyerSource) :
    deningerAdiabaticSource 0 h = h := by
  apply DeningerMeyerSource.toSource.injective
  apply Subtype.ext
  apply SchwartzMap.ext
  intro t
  rw [deningerAdiabaticSource_apply]
  simp

/-- The coefficient `n⁻ᵃ`, written in the exponential form used by the Euler connection. -/
def deningerAdiabaticMobiusCoefficient (a : ℝ) (n : ℕ) : ℝ :=
  Real.exp (-a * Real.log (n : ℝ))

theorem deningerAdiabaticMobiusCoefficient_eq_rpow {a : ℝ} {n : ℕ} (hn : 0 < n) :
    deningerAdiabaticMobiusCoefficient a n = (n : ℝ) ^ (-a) := by
  rw [deningerAdiabaticMobiusCoefficient, Real.rpow_def_of_pos (by exact_mod_cast hn)]
  congr 1
  ring

/-- **The full adiabatic Möbius inverse**, constructed through the exact source gauge. -/
def deningerAdiabaticMobiusPreimage (a : ℝ) (h : DeningerMeyerSource) (x : ℝ) : ℂ :=
  ((x ^ a : ℝ) : ℂ) *
    deningerMobiusPreimage
      (((DeningerMeyerSource.toSource (deningerAdiabaticSource a h) :
        DeningerExpSchwartz) : 𝓢(ℝ, ℂ))) x

/-- **Literal all-integer series formula.**  No finite Euler gauge or cofinal prime aperture occurs:
the already formed canonical preimage has exactly the coefficient `μ(n)n⁻ᵃ`. -/
theorem deningerAdiabaticMobiusPreimage_eq_tsum
    (a : ℝ) (h : DeningerMeyerSource) {x : ℝ} (hx : 0 < x) :
    deningerAdiabaticMobiusPreimage a h x =
      ∑' n : ℕ, (((moebius n : ℤ) : ℝ) *
        deningerAdiabaticMobiusCoefficient a n : ℝ) *
          deningerLogPull
            (((DeningerMeyerSource.toSource h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)))
            ((n : ℝ) * x) := by
  rw [deningerAdiabaticMobiusPreimage, deningerMobiusPreimage, ← tsum_mul_left]
  apply tsum_congr
  intro n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hnx : (0 : ℝ) < (n : ℝ) * x := mul_pos hnR hx
    rw [deningerLogPull_apply, deningerLogPull_apply,
      deningerAdiabaticSource_apply, Real.log_mul hnR.ne' hx.ne']
    change ((x ^ a : ℝ) : ℂ) *
          (((moebius n : ℤ) : ℂ) *
            (((Real.exp (-a * (Real.log (n : ℝ) + Real.log x)) : ℝ) : ℂ) *
              (((DeningerMeyerSource.toSource h : DeningerExpSchwartz) :
                𝓢(ℝ, ℂ))) (Real.log (n : ℝ) + Real.log x))) = _
    rw [Real.rpow_def_of_pos hx]
    simp only [deningerAdiabaticMobiusCoefficient]
    have hscalar :
        Real.exp (Real.log x * a) *
            Real.exp (-a * (Real.log (n : ℝ) + Real.log x)) =
          Real.exp (-a * Real.log (n : ℝ)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have hfactor :
        ((Real.exp (Real.log x * a) : ℝ) : ℂ) *
            ((Real.exp (-a * (Real.log (n : ℝ) + Real.log x)) : ℝ) : ℂ) =
          ((Real.exp (-a * Real.log (n : ℝ)) : ℝ) : ℂ) := by
      rw [← Complex.ofReal_mul, hscalar]
    have hmu :
        ((moebius n : ℤ) : ℂ) = ((((moebius n : ℤ) : ℝ) : ℂ)) := by
      norm_cast
    rw [Complex.ofReal_mul, ← hmu]
    calc
      _ = ((moebius n : ℤ) : ℂ) *
          (((Real.exp (Real.log x * a) : ℝ) : ℂ) *
            (((Real.exp (-a * (Real.log (n : ℝ) + Real.log x)) : ℝ) : ℂ) *
              (((DeningerMeyerSource.toSource h : DeningerExpSchwartz) :
                𝓢(ℝ, ℂ))) (Real.log (n : ℝ) + Real.log x))) :=
        mul_left_comm _ _ _
      _ = ((moebius n : ℤ) : ℂ) *
          ((((Real.exp (Real.log x * a) : ℝ) : ℂ) *
            ((Real.exp (-a * (Real.log (n : ℝ) + Real.log x)) : ℝ) : ℂ)) *
              (((DeningerMeyerSource.toSource h : DeningerExpSchwartz) :
                𝓢(ℝ, ℂ))) (Real.log (n : ℝ) + Real.log x)) := by
        rw [mul_assoc]
      _ = _ := by rw [hfactor, mul_assoc]

/-- The adiabatic family specializes exactly to the canonical critical preimage. -/
@[simp]
theorem deningerAdiabaticMobiusPreimage_zero
    (h : DeningerMeyerSource) {x : ℝ} (hx : 0 < x) :
    deningerAdiabaticMobiusPreimage 0 h x =
      deningerMobiusPreimage
        (((DeningerMeyerSource.toSource h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ))) x := by
  rw [deningerAdiabaticMobiusPreimage, deningerAdiabaticSource_zero]
  simp [Real.rpow_zero]

/-- A nonnegative real power is controlled globally by two adjacent integer moments. -/
theorem deninger_rpow_le_one_add_pow {a : ℝ} (ha : 0 ≤ a) {N : ℕ} (haN : a ≤ N)
    {x : ℝ} (hx : 0 < x) :
    x ^ a ≤ 1 + x ^ N := by
  by_cases hx1 : x ≤ 1
  · have hpow : x ^ a ≤ 1 := Real.rpow_le_one hx.le hx1 ha
    exact hpow.trans (le_add_of_nonneg_right (pow_nonneg hx.le N))
  · have hx1' : 1 ≤ x := le_of_not_ge hx1
    have hpow : x ^ a ≤ x ^ (N : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hx1' haN
    rw [Real.rpow_natCast] at hpow
    exact hpow.trans (le_add_of_nonneg_left zero_le_one)

/-- Every adiabatic moment is measurable on the positive ray. -/
theorem deningerAdiabaticMoment_aestronglyMeasurable
    (a : ℝ) (r : ℕ) (h : DeningerMeyerSource) :
    AEStronglyMeasurable
      (fun x : ℝ => ((x ^ r : ℝ) : ℂ) * deningerAdiabaticMobiusPreimage a h x)
      (volume.restrict (Set.Ioi (0 : ℝ))) := by
  have hpow : AEStronglyMeasurable (fun x : ℝ => ((x ^ a : ℝ) : ℂ))
      (volume.restrict (Set.Ioi (0 : ℝ))) :=
    (Complex.continuous_ofReal.comp_continuousOn
      (continuousOn_id.rpow_const fun _ hx => Or.inl hx.ne')).aestronglyMeasurable
        measurableSet_Ioi
  have hpre := deningerMobiusPreimage_aestronglyMeasurable
    (DeningerMeyerSource.toSource (deningerAdiabaticSource a h)).2
  have hnat : AEStronglyMeasurable (fun x : ℝ => ((x ^ r : ℝ) : ℂ))
      (volume.restrict (Set.Ioi (0 : ℝ))) :=
    (Complex.measurable_ofReal.comp (measurable_id.pow_const r)).aestronglyMeasurable
  change AEStronglyMeasurable
    ((fun x : ℝ => ((x ^ r : ℝ) : ℂ)) *
      ((fun x : ℝ => ((x ^ a : ℝ) : ℂ)) *
        deningerMobiusPreimage
          (((DeningerMeyerSource.toSource (deningerAdiabaticSource a h) :
            DeningerExpSchwartz) : 𝓢(ℝ, ℂ)))))
      (volume.restrict (Set.Ioi (0 : ℝ)))
  exact hnat.mul (hpow.mul hpre)

/-- **All polynomial moments of the full adiabatic inverse are finite**, including the critical
`r = 0` moment.  At `a = 0` this uses the PNT-strength cancellation already built into the
canonical preimage; for `a > 0` no absolute critical-series shortcut is substituted. -/
theorem deningerAdiabaticMobiusPreimage_moment_integrable
    {a : ℝ} (ha : 0 ≤ a) (r : ℕ) (h : DeningerMeyerSource) :
    IntegrableOn
      (fun x : ℝ => ((x ^ r : ℝ) : ℂ) * deningerAdiabaticMobiusPreimage a h x)
      (Set.Ioi (0 : ℝ)) := by
  obtain ⟨N, haN⟩ := exists_nat_ge a
  let g : ℝ → ℂ := fun x => deningerMobiusPreimage
    (((DeningerMeyerSource.toSource (deningerAdiabaticSource a h) :
      DeningerExpSchwartz) : 𝓢(ℝ, ℂ))) x
  have hr := deningerMobiusPreimage_moment_integrable
    (DeningerMeyerSource.toSource (deningerAdiabaticSource a h)).2 r
  have hrN := deningerMobiusPreimage_moment_integrable
    (DeningerMeyerSource.toSource (deningerAdiabaticSource a h)).2 (r + N)
  have hmajor : IntegrableOn
      (fun x : ℝ => ‖((x ^ r : ℝ) : ℂ) * g x‖ +
        ‖((x ^ (r + N) : ℝ) : ℂ) * g x‖) (Set.Ioi (0 : ℝ)) :=
    hr.norm.add hrN.norm
  refine Integrable.mono' hmajor (deningerAdiabaticMoment_aestronglyMeasurable a r h) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hx0 : (0 : ℝ) < x := hx
  have hpow := deninger_rpow_le_one_add_pow ha haN hx0
  simp only [deningerAdiabaticMobiusPreimage, norm_mul, Complex.norm_real,
    Real.norm_eq_abs,
    abs_of_nonneg (pow_nonneg hx0.le r), abs_of_nonneg (Real.rpow_nonneg hx0.le a),
    abs_of_nonneg (pow_nonneg hx0.le (r + N))]
  change x ^ r * (x ^ a * ‖g x‖) ≤ x ^ r * ‖g x‖ + x ^ (r + N) * ‖g x‖
  have hxr : 0 ≤ x ^ r := pow_nonneg hx0.le _
  have hg : 0 ≤ ‖g x‖ := norm_nonneg _
  calc
    x ^ r * (x ^ a * ‖g x‖) ≤ x ^ r * ((1 + x ^ N) * ‖g x‖) := by gcongr
    _ = x ^ r * ‖g x‖ + x ^ (r + N) * ‖g x‖ := by
      rw [pow_add]
      ring

/-- The `x^r`-weighted adiabatic inverse as an honest ray function. -/
def deningerAdiabaticMomentFun (a : ℝ) (r : ℕ) (h : DeningerMeyerSource) : ℝ → ℂ :=
  fun x => ((x ^ r : ℝ) : ℂ) * deningerAdiabaticMobiusPreimage a h x

theorem deningerAdiabaticMomentFun_memLp {a : ℝ} (ha : 0 ≤ a) (r : ℕ)
    (h : DeningerMeyerSource) :
    MemLp (deningerAdiabaticMomentFun a r h) 1
      (volume.restrict (Set.Ioi (0 : ℝ))) :=
  memLp_one_iff_integrable.mpr
    (deningerAdiabaticMobiusPreimage_moment_integrable ha r h)

/-- The `x^r` adiabatic moment as an `L¹(0,∞)` element. -/
def deningerAdiabaticMomentLp {a : ℝ} (ha : 0 ≤ a) (r : ℕ)
    (h : DeningerMeyerSource) : Lp ℂ 1 (volume.restrict (Set.Ioi (0 : ℝ))) :=
  (deningerAdiabaticMomentFun_memLp ha r h).toLp _

end

end RHTower
