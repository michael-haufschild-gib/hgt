import GaloisForLFunctions.HTGeometry.MassDispersionRadiationCorona

/-!
# The half-wave symbol becomes a pure amplified plane wave at the outgoing end

At the negative frequency end the gauged dispersion satisfies `ω_{a,λ}(ξ) + ξ → iλ`, so the
half-wave symbol factors as

`exp (-i u ω(ξ)) = exp (i u ξ) · exp (-i u (ω(ξ) + ξ))`,

whose second factor converges to `e^{uλ}`.  Since the first factor is unimodular, the symbol is
asymptotically the amplified outgoing plane wave `e^{uλ} e^{iuξ}`.  No mass, no aperture and no
smoothing enters: the whole amplified end of the gauged half-wave is a translation with gain
`e^{uλ}`.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex Filter Topology

/-- The amplified outgoing plane wave `e^{uλ} e^{iuξ}`. -/
noncomputable def massGaugeRadiationModel (lambda u xi : ℝ) : ℂ :=
  ((Real.exp (u * lambda) : ℝ) : ℂ) * Complex.exp (I * (u : ℂ) * (xi : ℂ))

theorem continuous_massGaugeRadiationModel (lambda u : ℝ) :
    Continuous (massGaugeRadiationModel lambda u) := by
  unfold massGaugeRadiationModel
  fun_prop

theorem norm_exp_mul_I_ofReal (t : ℝ) : ‖Complex.exp (I * (t : ℂ))‖ = 1 := by
  rw [Complex.norm_exp]
  simp

@[simp]
theorem norm_massGaugeRadiationModel (lambda u xi : ℝ) :
    ‖massGaugeRadiationModel lambda u xi‖ = Real.exp (u * lambda) := by
  rw [massGaugeRadiationModel, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.exp_nonneg _), Complex.norm_exp]
  simp

/-- The half-wave symbol splits into the plane wave and the corrected exponential. -/
theorem massGaugeHalfWaveSymbol_eq_planeWave_mul (a lambda u xi : ℝ) :
    massGaugeHalfWaveSymbol a lambda u xi
      = Complex.exp (I * (u : ℂ) * (xi : ℂ))
        * Complex.exp (-I * (u : ℂ) * (massGaugeDispersion a lambda xi + (xi : ℂ))) := by
  rw [massGaugeHalfWaveSymbol, ← Complex.exp_add]
  congr 1
  ring

/-- The corrected exponential converges to the gauge gain at the outgoing end. -/
theorem tendsto_massGaugeHalfWaveCorrection_atBot {a lambda : ℝ} (ha : lambda ≤ a)
    (hlambda : 0 ≤ lambda) (u : ℝ) :
    Tendsto
      (fun xi : ℝ =>
        Complex.exp (-I * (u : ℂ) * (massGaugeDispersion a lambda xi + (xi : ℂ))))
      atBot (nhds (((Real.exp (u * lambda) : ℝ) : ℂ))) := by
  have h1 := tendsto_massGaugeDispersion_add_atBot ha hlambda
  have h2 : Tendsto
      (fun xi : ℝ => -I * (u : ℂ) * (massGaugeDispersion a lambda xi + (xi : ℂ)))
      atBot (nhds (-I * (u : ℂ) * ((lambda : ℂ) * I))) :=
    tendsto_const_nhds.mul h1
  have h3 := (Complex.continuous_exp.tendsto _).comp h2
  have hval : -I * (u : ℂ) * ((lambda : ℂ) * I) = ((u * lambda : ℝ) : ℂ) := by
    have hI : I * I = -1 := Complex.I_mul_I
    push_cast
    linear_combination (-(u : ℂ) * (lambda : ℂ)) * hI
  rw [hval, ← Complex.ofReal_exp] at h3
  exact h3

/-- **(24.44) The gauged half-wave symbol is asymptotically the amplified outgoing plane
wave.** -/
theorem tendsto_massGaugeHalfWaveSymbol_sub_radiation_atBot {a lambda : ℝ} (ha : lambda ≤ a)
    (hlambda : 0 ≤ lambda) (u : ℝ) :
    Tendsto
      (fun xi : ℝ => massGaugeHalfWaveSymbol a lambda u xi - massGaugeRadiationModel lambda u xi)
      atBot (nhds 0) := by
  have hbase := tendsto_massGaugeHalfWaveCorrection_atBot ha hlambda u
  have hzero : Tendsto
      (fun xi : ℝ =>
        Complex.exp (-I * (u : ℂ) * (massGaugeDispersion a lambda xi + (xi : ℂ)))
          - ((Real.exp (u * lambda) : ℝ) : ℂ)) atBot (nhds 0) := by
    have := hbase.sub (tendsto_const_nhds
      (x := ((Real.exp (u * lambda) : ℝ) : ℂ)) (f := (atBot : Filter ℝ)))
    simpa using this
  refine squeeze_zero_norm (fun xi => ?_)
    (tendsto_zero_iff_norm_tendsto_zero.1 hzero)
  have hfac : massGaugeHalfWaveSymbol a lambda u xi - massGaugeRadiationModel lambda u xi
      = Complex.exp (I * (u : ℂ) * (xi : ℂ))
        * (Complex.exp (-I * (u : ℂ) * (massGaugeDispersion a lambda xi + (xi : ℂ)))
          - ((Real.exp (u * lambda) : ℝ) : ℂ)) := by
    rw [massGaugeHalfWaveSymbol_eq_planeWave_mul, massGaugeRadiationModel]
    ring
  have hone : ‖Complex.exp (I * (u : ℂ) * (xi : ℂ))‖ = 1 := by
    rw [Complex.norm_exp]
    simp
  rw [hfac, norm_mul, hone, one_mul]

end GaloisForLFunctions.HTGeometry
