import GaloisForLFunctions.RHTower.XiWardCubicBichamberHolomorphicCodiagonal
import GaloisForLFunctions.HTGeometry.HolomorphicSchwarzPolarization

/-!
# Cubic Ward sesquiholomorphic landing no-go (W-H193)

The reflection-Loewner kernel is holomorphic in its first argument and antiholomorphic in its
second.  A contour-compatible scalar weight would therefore be holomorphic in independent
variables `(s,v)` with `v = star t`.  On the reflection graph `s = 1-v`, however, the desired
cubic landing is the real, nonconstant density

`r^(2 : ℕ) (exp (-r Re v) - exp (-2 r Re v))^(2 : ℕ)`.

No jointly entire `(s,v)` weight can have that restriction.  Its pullback to the graph would be
an entire real-valued function, hence constant, while its values at horizontal depths zero and one
are distinct.  This proves that W-H191's `(s,t)`-holomorphic polarization lives in the opposite
complex structure from the Loewner kernel.  A successful contraction must therefore use a real
Stokes/Wirtinger correction, an additional polarized variable with a genuine incidence relation,
or recover positivity only after an averaging operation; ordinary two-variable meromorphic
residue calculus cannot supply the cubic positive landing.
-/

open Complex

namespace RHTower

noncomputable section

/-- Cubic radial self-density at horizontal depth `a`. -/
def xiWardCubicRadialSelfDensity (r a : ℝ) : ℝ :=
  r ^ (2 : ℕ) * (Real.exp (-(a * r)) - Real.exp (-((2 * a) * r))) ^ (2 : ℕ)

theorem xiWardCubicRadialSelfDensity_zero (r : ℝ) :
    xiWardCubicRadialSelfDensity r 0 = 0 := by
  simp [xiWardCubicRadialSelfDensity]

theorem xiWardCubicRadialSelfDensity_one_pos {r : ℝ} (hr : 0 < r) :
    0 < xiWardCubicRadialSelfDensity r 1 := by
  have hexp : Real.exp (-(2 * r)) < Real.exp (-r) :=
    Real.exp_lt_exp.mpr (by linarith)
  unfold xiWardCubicRadialSelfDensity
  norm_num
  exact mul_pos (sq_pos_of_pos hr) (sq_pos_of_pos (sub_pos.mpr hexp))

/-- No jointly entire Loewner-compatible weight restricts to the positive cubic density on the
FE reflection graph. -/
theorem not_exists_entire_sesquiholomorphic_cubicReflectionLanding
    {r : ℝ} (hr : 0 < r) :
    ¬ ∃ F : ℂ × ℂ → ℂ,
      Differentiable ℂ F ∧
      ∀ z : ℂ,
        F (1 - z, z) = (xiWardCubicRadialSelfDensity r z.re : ℂ) := by
  rintro ⟨F, hF, hland⟩
  let g : ℂ → ℂ := fun z => F (1 - z, z)
  have hg : Differentiable ℂ g := by
    dsimp only [g]
    fun_prop
  have hstarEq : (fun z : ℂ => star (g z)) = g := by
    funext z
    change star (F (1 - z, z)) = F (1 - z, z)
    rw [hland]
    exact Complex.conj_ofReal _
  have hgstar : Differentiable ℂ (fun z : ℂ => star (g z)) := by
    rw [hstarEq]
    exact hg
  have hconst :=
    GaloisForLFunctions.HTGeometry.eq_of_differentiable_pointwiseStar
      hg hgstar 1
  dsimp only [g] at hconst
  rw [hland, hland, Complex.ofReal_inj] at hconst
  norm_num at hconst
  rw [xiWardCubicRadialSelfDensity_zero] at hconst
  linarith [xiWardCubicRadialSelfDensity_one_pos hr]

end
end RHTower
