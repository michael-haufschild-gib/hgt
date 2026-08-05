import GaloisForLFunctions.HTGeometry.MovingCanonicalProduct

/-!
# The residue of the moving canonical log-derivative at a zero

The zeros of the moving canonical product are real and simple, so its negative logarithmic derivative
has a simple pole at each of them with residue `-1`.  Approaching a zero from anywhere off the zero
set, the product of the log-derivative with the displacement therefore tends to `-1`.

This is the leading blow-up datum of the packet: it is what a graded valuation on the span of the
jets needs at its lowest order, and unlike the model realizations it is read off the order-one
factorization of the product rather than from an exact identity.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

/-- **The log-derivative has residue `-1` at every zero.**  The product vanishes to order one, so it
factors as displacement times a nonvanishing analytic germ, and the displacement cancels the pole. -/
theorem tendsto_movingCanonicalLogDerivative_mul_sub (θ : BoundedRealSequence) (n : ℕ)
    {u : ℕ → ℂ} (humem : ∀ j m, u j ≠ (movingCanonicalZero θ m : ℂ))
    (hu : Tendsto u atTop (𝓝 ((movingCanonicalZero θ n : ℂ)))) :
    Tendsto (fun j => movingCanonicalLogDerivative θ (u j) *
      (u j - (movingCanonicalZero θ n : ℂ))) atTop (𝓝 (-1)) := by
  set ζ : ℂ := (movingCanonicalZero θ n : ℂ) with hζ
  have hM : AnalyticAt ℂ (movingCanonicalProduct θ) ζ :=
    movingCanonicalProduct_analytic θ ζ (Set.mem_univ ζ)
  obtain ⟨g, hg, hg0, hev⟩ :=
    (hM.analyticOrderAt_eq_natCast (n := 1)).mp
      (movingCanonicalProduct_zero_analyticOrderAt θ n)
  have hevmul : ∀ᶠ z in 𝓝 ζ, movingCanonicalProduct θ z = (z - ζ) * g z := by
    filter_upwards [hev] with z hz
    rw [hz, pow_one, smul_eq_mul]
  have hU : ∀ᶠ z in 𝓝 ζ,
      movingCanonicalProduct θ z = (z - ζ) * g z ∧ g z ≠ 0 ∧ AnalyticAt ℂ g z := by
    filter_upwards [hevmul, hg.continuousAt.eventually_ne hg0, hg.eventually_analyticAt]
      with z h1 h2 h3
    exact ⟨h1, h2, h3⟩
  obtain ⟨U, hUsub, hUopen, hUmem⟩ := eventually_nhds_iff.mp hU
  have hkey : ∀ z ∈ U, (∀ m, z ≠ (movingCanonicalZero θ m : ℂ)) →
      movingCanonicalLogDerivative θ z * (z - ζ)
        = -(g z + (z - ζ) * deriv g z) / g z := by
    intro z hzU hzne
    obtain ⟨hfac, hgz, hganz⟩ := hUsub z hzU
    have hzζ : z - ζ ≠ 0 := sub_ne_zero.mpr (hzne n)
    have hfacev : movingCanonicalProduct θ =ᶠ[𝓝 z] fun w => (w - ζ) * g w :=
      Filter.eventuallyEq_of_mem (hUopen.mem_nhds hzU) fun w hw => (hUsub w hw).1
    have hderiv : deriv (movingCanonicalProduct θ) z = g z + (z - ζ) * deriv g z := by
      have hd1 : HasDerivAt (fun w : ℂ => w - ζ) 1 z := (hasDerivAt_id z).sub_const ζ
      have hd2 : HasDerivAt g (deriv g z) z := hganz.differentiableAt.hasDerivAt
      have hprod : HasDerivAt (fun w : ℂ => (w - ζ) * g w)
          (1 * g z + (z - ζ) * deriv g z) z := hd1.mul hd2
      rw [hfacev.deriv_eq, hprod.deriv]
      ring
    have hlog := neg_logDeriv_movingCanonicalProduct_eq θ hzne
    rw [← hlog, logDeriv_apply, hderiv, hfac]
    field_simp
  have hevj : ∀ᶠ j in atTop, movingCanonicalLogDerivative θ (u j) * (u j - ζ)
      = -(g (u j) + (u j - ζ) * deriv g (u j)) / g (u j) := by
    filter_upwards [hu (hUopen.mem_nhds hUmem)] with j hj
    exact hkey (u j) hj (fun m => humem j m)
  have hgc : Tendsto (fun j => g (u j)) atTop (𝓝 (g ζ)) := hg.continuousAt.tendsto.comp hu
  have hdc : Tendsto (fun j => deriv g (u j)) atTop (𝓝 (deriv g ζ)) :=
    hg.deriv.continuousAt.tendsto.comp hu
  have hsub : Tendsto (fun j => u j - ζ) atTop (𝓝 0) := by
    have := hu.sub (tendsto_const_nhds (x := ζ))
    simpa using this
  have hlim : Tendsto (fun j => -(g (u j) + (u j - ζ) * deriv g (u j)) / g (u j)) atTop
      (𝓝 (-(g ζ + 0 * deriv g ζ) / g ζ)) :=
    ((hgc.add (hsub.mul hdc)).neg).div hgc hg0
  have hval : -(g ζ + 0 * deriv g ζ) / g ζ = -1 := by
    rw [zero_mul, add_zero, neg_div, div_self hg0]
  rw [hval] at hlim
  exact Filter.Tendsto.congr' (hevj.mono fun j h => h.symm) hlim


/-- **The residue datum along an approach from the upper half-plane.**  The zeros are real, so a
sequence with positive imaginary part never meets them. -/
theorem tendsto_movingCanonicalLogDerivative_mul_sub_of_upper (θ : BoundedRealSequence) (n : ℕ)
    {u : ℕ → ℂ} (hupper : ∀ j, 0 < (u j).im)
    (hu : Tendsto u atTop (𝓝 ((movingCanonicalZero θ n : ℂ)))) :
    Tendsto (fun j => movingCanonicalLogDerivative θ (u j) *
      (u j - (movingCanonicalZero θ n : ℂ))) atTop (𝓝 (-1)) := by
  refine tendsto_movingCanonicalLogDerivative_mul_sub θ n (fun j m => ?_) hu
  intro hcon
  have him : (u j).im = 0 := by rw [hcon]; simp
  exact absurd him (ne_of_gt (hupper j))

end GaloisForLFunctions.HTGeometry
