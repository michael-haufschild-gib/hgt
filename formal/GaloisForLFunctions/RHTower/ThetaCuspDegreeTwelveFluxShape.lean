import GaloisForLFunctions.RHTower.ThetaCuspKernelLogConcavity
import GaloisForLFunctions.RHTower.CothInfra

/-!
# One-sided sign geometry of the degree-twelve completed theta flux

The literal source flux has a strictly decreasing logarithmic derivative on the
positive center ray. Hence, once its derivative ceases to be positive, it is
strictly negative at every later center. This is a shape theorem, not a
native odd-four tail-capacity estimate.
-/

namespace RHTower
noncomputable section
open Set

/-- Logarithmic derivative of the degree-twelve center flux. -/
def thetaCuspDegreeTwelveFluxLogRate (a r : ℝ) : ℝ :=
  12/r + a*rcoth (a*r) + deriv thetaCuspLogSource (r/2)

/-- The actual complete-source logarithmic rate decreases strictly. -/
theorem thetaCuspDegreeTwelveFluxLogRate_strictAntiOn {a : ℝ} (ha : 0 < a) :
    StrictAntiOn (thetaCuspDegreeTwelveFluxLogRate a) (Ioi 0) := by
  have hL : StrictAnti (deriv thetaCuspLogSource) :=
    strictAntiOn_univ.mp <|
      strictConcaveOn_thetaCuspLogSource.strictAntiOn_deriv fun x _ =>
        (hasDerivAt_thetaCuspLogSource x).differentiableAt
  intro r hr s hs hrs
  simp only [mem_Ioi] at hr hs
  have hfirst : 12/s < 12/r := by
    rw [div_lt_div_iff₀ hs hr]
    nlinarith only [hrs]
  have hsecond : a*rcoth (a*s) < a*rcoth (a*r) := by
    apply mul_lt_mul_of_pos_left _ ha
    exact rcoth_strictAntiOn_pos (mul_pos ha hr) (mul_pos ha hs)
      (mul_lt_mul_of_pos_left hrs ha)
  have hthird : deriv thetaCuspLogSource (s/2) <
      deriv thetaCuspLogSource (r/2) := hL (by linarith)
  dsimp [thetaCuspDegreeTwelveFluxLogRate]
  linarith only [hfirst, hsecond, hthird]

/-- The literal degree-twelve flux, before naming its polynomial correction. -/
def thetaCuspDegreeTwelveFlux (a r : ℝ) : ℝ :=
  r^(12 : ℕ)*Real.sinh (a*r)*thetaCuspFullSource (r/2)^(2 : ℕ)

/-- Its derivative is its positive value times the source-selected log rate. -/
theorem thetaCuspDegreeTwelveFlux_deriv_eq_mul_logRate {a r : ℝ}
    (ha : 0 < a) (hr : 0 < r) :
    deriv (thetaCuspDegreeTwelveFlux a) r =
      thetaCuspDegreeTwelveFlux a r * thetaCuspDegreeTwelveFluxLogRate a r := by
  have hF := (hasDerivAt_thetaCuspFullSource_iterate_zero (r/2)).comp r
    ((hasDerivAt_id r).div_const 2)
  have h := (((hasDerivAt_id r).pow 12).mul
    (((hasDerivAt_id r).const_mul a).sinh)).mul (hF.pow 2)
  have hder : deriv (thetaCuspDegreeTwelveFlux a) r =
      (12*r^(11 : ℕ)*Real.sinh (a*r) +
        a*r^(12 : ℕ)*Real.cosh (a*r))*thetaCuspFullSource (r/2)^(2 : ℕ) +
        r^(12 : ℕ)*Real.sinh (a*r)*thetaCuspFullSource (r/2)*
          deriv thetaCuspFullSource (r/2) := by
    have h' : HasDerivAt (thetaCuspDegreeTwelveFlux a)
        ((12*r^(11 : ℕ)*Real.sinh (a*r) +
          a*r^(12 : ℕ)*Real.cosh (a*r))*thetaCuspFullSource (r/2)^(2 : ℕ) +
          r^(12 : ℕ)*Real.sinh (a*r)*thetaCuspFullSource (r/2)*
            deriv thetaCuspFullSource (r/2)) r := by
      exact h.congr_deriv (by dsimp [thetaCuspDegreeTwelveFlux]; simp only [iteratedDeriv_one]; ring)
    exact h'.deriv
  have hlog : deriv thetaCuspLogSource (r/2) =
      deriv thetaCuspFullSource (r/2)/thetaCuspFullSource (r/2) := by
    simpa only [iteratedDeriv_one] using (hasDerivAt_thetaCuspLogSource (r/2)).deriv
  have hs : Real.sinh (a*r) ≠ 0 :=
    (Real.sinh_pos_iff.mpr (mul_pos ha hr)).ne'
  have hsource : thetaCuspFullSource (r/2) ≠ 0 :=
    (thetaCuspFullSource_pos_all (r/2)).ne'
  rw [hder]
  unfold thetaCuspDegreeTwelveFlux thetaCuspDegreeTwelveFluxLogRate rcoth
  rw [hlog]
  field_simp [hr.ne', hs, hsource]

/-- The completed-source flux itself is positive on the physical ray. -/
theorem thetaCuspDegreeTwelveFlux_pos {a r : ℝ} (ha : 0 < a) (hr : 0 < r) :
    0 < thetaCuspDegreeTwelveFlux a r := by
  have hs : 0 < Real.sinh (a*r) := Real.sinh_pos_iff.mpr (mul_pos ha hr)
  unfold thetaCuspDegreeTwelveFlux
  exact mul_pos (mul_pos (pow_pos hr 12) hs)
    (sq_pos_of_pos (thetaCuspFullSource_pos_all (r/2)))

/-- A nonpositive flux derivative can never recover at a later source center. -/
theorem thetaCuspDegreeTwelveFlux_deriv_no_recovery {a r s : ℝ}
    (ha : 0 < a) (hr : 0 < r) (hrs : r < s)
    (hder : deriv (thetaCuspDegreeTwelveFlux a) r ≤ 0) :
    deriv (thetaCuspDegreeTwelveFlux a) s < 0 := by
  have hs : 0 < s := lt_trans hr hrs
  have hKr := thetaCuspDegreeTwelveFlux_pos ha hr
  have hKs := thetaCuspDegreeTwelveFlux_pos ha hs
  rw [thetaCuspDegreeTwelveFlux_deriv_eq_mul_logRate ha hr] at hder
  have hEr : thetaCuspDegreeTwelveFluxLogRate a r ≤ 0 := by
    nlinarith only [hder, hKr]
  have hEs : thetaCuspDegreeTwelveFluxLogRate a s <
      thetaCuspDegreeTwelveFluxLogRate a r :=
    thetaCuspDegreeTwelveFluxLogRate_strictAntiOn ha hr hs hrs
  rw [thetaCuspDegreeTwelveFlux_deriv_eq_mul_logRate ha hs]
  exact mul_neg_of_pos_of_neg hKs (lt_of_lt_of_le hEs hEr)

end
end RHTower
