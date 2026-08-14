import GaloisForLFunctions.RHTower.XiShiftedHardEdgeDyadicSampleCoherence

/-!
# Parabolic Nyquist alias chart for Route U

Pointwise dyadic coherence fixes the divisor coordinate before sending hard-edge mass to infinity.
The global divisor sum also probes the moving shell whose spectral height is quadratic in coarse
mass.  On that shell the fine Cayley phase approaches the coarse Nyquist wall, not the central
frequency: after subtracting one coarse alias period its exact limit is `-4 / u`.  Simultaneously,
the mass-scaled fine resolvent tends to `4 / u ^ 2`.

These premise-free limits isolate the nonuniform ultraviolet chart that falsifies naive exchange of
the pointwise even/odd limits with the complete Xi divisor.  The positive shell parameter is carried
by a subtype, so every public result is closed and has no positivity premise.
-/

open Complex Filter

noncomputable section

namespace RHTower

/-- Positive coordinate `u` on the quadratic spectral shell `height = u * mass²`. -/
abbrev RouteUPositiveParabolicScale := {u : ℝ // 0 < u}

/-- Spectral height on the quadratic shell based on the coarse dyadic mass. -/
def routeUDyadicParabolicHeight (u : RouteUPositiveParabolicScale) (k : ℕ) : ℝ :=
  (u : ℝ) * routeUHardEdgeMass (k : ℝ) ^ 2

/-- Fine Cayley phase folded back by one coarse alias period. -/
def routeUDyadicParabolicFoldedPhase
    (u : RouteUPositiveParabolicScale) (k : ℕ) : ℝ :=
  routeUHardEdgePhase (routeUDyadicFineIndex k : ℝ)
      (routeUDyadicParabolicHeight u k) -
    routeUHardEdgeAliasPeriod (k : ℝ)

/-- Coarse hard-edge mass tends to infinity on natural-number scales. -/
theorem tendsto_routeUHardEdgeMass_natCast_atTop :
    Tendsto (fun k : ℕ => routeUHardEdgeMass (k : ℝ)) atTop atTop := by
  simpa [routeUHardEdgeMass, abs_of_nonneg, add_comm] using
    (tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop)

/-- Exact reciprocal-arctangent form of the folded fine phase. -/
theorem routeUDyadicParabolicFoldedPhase_eq
    (u : RouteUPositiveParabolicScale) (k : ℕ) :
    routeUDyadicParabolicFoldedPhase u k =
      -2 * routeUHardEdgeMass (k : ℝ) *
        Real.arctan (2 / ((u : ℝ) * routeUHardEdgeMass (k : ℝ))) := by
  let a : ℝ := routeUHardEdgeMass (k : ℝ)
  have hu : 0 < (u : ℝ) := u.property
  have ha : 0 < a := routeUHardEdgeMass_pos (k : ℝ)
  have hx : 0 < (u : ℝ) * a / 2 := by positivity
  have harg : (u : ℝ) * a ^ 2 / (2 * a) = (u : ℝ) * a / 2 := by
    field_simp [ha.ne']
  have hinv : ((u : ℝ) * a / 2)⁻¹ = 2 / ((u : ℝ) * a) := by
    field_simp [hu.ne', ha.ne']
  have hatan := Real.arctan_inv_of_pos hx
  rw [hinv] at hatan
  rw [routeUDyadicParabolicFoldedPhase, routeUDyadicParabolicHeight,
    routeUHardEdgePhase, routeUHardEdgeAliasPeriod,
    routeUHardEdgeMass_fineIndex]
  change 2 * a * Real.arctan ((u : ℝ) * a ^ 2 / (2 * a)) - Real.pi * a = _
  rw [harg]
  rw [show Real.arctan ((u : ℝ) * a / 2) =
      Real.pi / 2 - Real.arctan (2 / ((u : ℝ) * a)) by linarith]
  ring

/-- The reciprocal-arctangent correction converges to the parabolic fold coordinate. -/
theorem tendsto_routeUDyadicParabolicArctanCorrection
    (u : RouteUPositiveParabolicScale) :
    Tendsto (fun k : ℕ =>
      -2 * routeUHardEdgeMass (k : ℝ) *
        Real.arctan (2 / ((u : ℝ) * routeUHardEdgeMass (k : ℝ))))
      atTop (nhds (-4 / (u : ℝ))) := by
  have hu : 0 < (u : ℝ) := u.property
  let a : ℕ → ℝ := fun k => routeUHardEdgeMass (k : ℝ)
  let x : ℕ → ℝ := fun k => 2 / ((u : ℝ) * a k)
  have ha : Tendsto a atTop atTop := by
    simpa only [a] using tendsto_routeUHardEdgeMass_natCast_atTop
  have hua : Tendsto (fun k => (u : ℝ) * a k) atTop atTop :=
    Tendsto.const_mul_atTop hu ha
  have hx : Tendsto x atTop (nhds 0) := by
    simpa only [x] using
      (tendsto_const_nhds.div_atTop hua :
        Tendsto (fun k => (2 : ℝ) / ((u : ℝ) * a k)) atTop (nhds 0))
  have hxne : ∀ k, x k ≠ 0 := by
    intro k
    exact div_ne_zero (by norm_num)
      (mul_ne_zero hu.ne' (routeUHardEdgeMass_pos _).ne')
  have hxWithin : Tendsto x atTop (nhdsWithin 0 {0}ᶜ) :=
    tendsto_nhdsWithin_iff.mpr
      ⟨hx, Eventually.of_forall fun k => by simpa using hxne k⟩
  have hderiv : HasDerivAt Real.arctan 1 0 := by
    simpa using (Real.hasDerivAt_arctan (x := 0))
  have hslope := hderiv.tendsto_slope_zero.comp hxWithin
  have hslope' : Tendsto (fun k : ℕ => (x k)⁻¹ * Real.arctan (x k))
      atTop (nhds 1) := by
    simpa only [Function.comp_def, zero_add, Real.arctan_zero, sub_zero,
      smul_eq_mul] using hslope
  have hscaled := Tendsto.const_mul (-4 / (u : ℝ)) hslope'
  convert hscaled using 1
  · funext k
    dsimp only [x, a]
    field_simp [hu.ne', (routeUHardEdgeMass_pos (k : ℝ)).ne']
    ring_nf
  · ring_nf

/-- The fine phase approaches the coarse Nyquist wall with finite folded coordinate `-4 / u`. -/
theorem tendsto_routeUDyadicParabolicFoldedPhase
    (u : RouteUPositiveParabolicScale) :
    Tendsto (routeUDyadicParabolicFoldedPhase u) atTop
      (nhds (-4 / (u : ℝ))) := by
  exact (tendsto_routeUDyadicParabolicArctanCorrection u).congr'
    (Eventually.of_forall fun k =>
      (routeUDyadicParabolicFoldedPhase_eq u k).symm)

/-- The complex Route U phase restricts exactly to the real phase on real spectral nodes. -/
theorem routeUComplexHardEdgePhase_ofReal (r α : ℝ) :
    routeUComplexHardEdgePhase r (α : ℂ) =
      (routeUHardEdgePhase r α : ℂ) := by
  rw [routeUComplexHardEdgePhase, routeUHardEdgePhase]
  push_cast
  rfl

/-- Complex periodization sees the same finite parabolic fold coordinate. -/
theorem tendsto_routeUDyadicParabolicComplexFoldedPhase
    (u : RouteUPositiveParabolicScale) :
    Tendsto (fun k : ℕ =>
      routeUComplexHardEdgePhase (routeUDyadicFineIndex k : ℝ)
          (routeUDyadicParabolicHeight u k : ℂ) -
        (routeUHardEdgeAliasPeriod (k : ℝ) : ℂ))
      atTop (nhds ((-4 / (u : ℝ) : ℝ) : ℂ)) := by
  have hreal := (Complex.continuous_ofReal.tendsto (-4 / (u : ℝ))).comp
    (tendsto_routeUDyadicParabolicFoldedPhase u)
  exact hreal.congr'
    (Eventually.of_forall fun k => by
      change (routeUDyadicParabolicFoldedPhase u k : ℂ) =
        routeUComplexHardEdgePhase (routeUDyadicFineIndex k : ℝ)
            (routeUDyadicParabolicHeight u k : ℂ) -
          (routeUHardEdgeAliasPeriod (k : ℝ) : ℂ)
      rw [routeUDyadicParabolicFoldedPhase,
        routeUComplexHardEdgePhase_ofReal]
      push_cast
      rfl)

/-- Real spectral profile of the mass-normalized hard-edge resolvent. -/
def routeURealHardEdgeResolventWeight (r α : ℝ) : ℝ :=
  routeUHardEdgeMass r ^ 2 /
    (routeUHardEdgeMass r ^ 2 + α ^ 2)

/-- Exact rational normal form of the scaled fine resolvent on the quadratic shell. -/
theorem routeUDyadicParabolicScaledResolventWeight_eq
    (u : RouteUPositiveParabolicScale) (k : ℕ) :
    routeUHardEdgeMass (k : ℝ) ^ 2 *
        routeURealHardEdgeResolventWeight (routeUDyadicFineIndex k : ℝ)
          (routeUDyadicParabolicHeight u k) =
      4 / (4 / routeUHardEdgeMass (k : ℝ) ^ 2 + (u : ℝ) ^ 2) := by
  let a : ℝ := routeUHardEdgeMass (k : ℝ)
  have hu : 0 < (u : ℝ) := u.property
  have ha : 0 < a := routeUHardEdgeMass_pos (k : ℝ)
  rw [routeURealHardEdgeResolventWeight, routeUDyadicParabolicHeight,
    routeUHardEdgeMass_fineIndex]
  change a ^ 2 * ((2 * a) ^ 2 /
      ((2 * a) ^ 2 + ((u : ℝ) * a ^ 2) ^ 2)) =
    4 / (4 / a ^ 2 + (u : ℝ) ^ 2)
  field_simp [ha.ne', hu.ne']
  ring

/-- On the quadratic shell the fine resolvent has exact nonzero scaled limit `4 / u²`. -/
theorem tendsto_routeUDyadicParabolicScaledResolventWeight
    (u : RouteUPositiveParabolicScale) :
    Tendsto (fun k : ℕ =>
      routeUHardEdgeMass (k : ℝ) ^ 2 *
        routeURealHardEdgeResolventWeight (routeUDyadicFineIndex k : ℝ)
          (routeUDyadicParabolicHeight u k))
      atTop (nhds (4 / (u : ℝ) ^ 2)) := by
  have hu : 0 < (u : ℝ) := u.property
  have hmassSq : Tendsto
      (fun k : ℕ => routeUHardEdgeMass (k : ℝ) ^ 2) atTop atTop :=
    (tendsto_pow_atTop (n := 2) (by norm_num)).comp
      tendsto_routeUHardEdgeMass_natCast_atTop
  have hrecip : Tendsto
      (fun k : ℕ => 4 / routeUHardEdgeMass (k : ℝ) ^ 2)
      atTop (nhds 0) := tendsto_const_nhds.div_atTop hmassSq
  have hden : Tendsto
      (fun k : ℕ => 4 / routeUHardEdgeMass (k : ℝ) ^ 2 + (u : ℝ) ^ 2)
      atTop (nhds ((u : ℝ) ^ 2)) := by
    simpa only [zero_add] using hrecip.add_const ((u : ℝ) ^ 2)
  have hquot : Tendsto
      (fun k : ℕ => 4 /
        (4 / routeUHardEdgeMass (k : ℝ) ^ 2 + (u : ℝ) ^ 2))
      atTop (nhds (4 / (u : ℝ) ^ 2)) :=
    tendsto_const_nhds.div hden (pow_ne_zero 2 hu.ne')
  exact hquot.congr'
    (Eventually.of_forall fun k =>
      (routeUDyadicParabolicScaledResolventWeight_eq u k).symm)

end RHTower
