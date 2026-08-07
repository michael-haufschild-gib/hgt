import GaloisForLFunctions.RHTower.ArchLadderRegular
import GaloisForLFunctions.RHTower.CompletedFluxPrimeArchDecomposition
import GaloisForLFunctions.HTGeometry.ReflectedDigammaAnomaly
import GaloisForLFunctions.RHTower.DigammaVerticalMinimum
import GaloisForLFunctions.RHTower.ReflectionCocycleClass

/-!
# The completed split on the whole right half-plane

The strip form of the completed logarithmic-derivative split uses its upper bound `Re s < 1` for one
thing only: to know `s ≠ 1`, where `riemannZeta` has its pole and `archFactor` its zero.  With sharp
archimedean nonvanishing the bound is unnecessary, and the split holds on all of `Re s > 0` away from
`s = 1`, with `riemannZeta s ≠ 0` as the single genuine side condition.

This unifies the corpus's two regional statements — the strip form and the absolute-convergence form
— into one theorem covering both regions and everything between them.  On `Re s > 1` the side
condition is automatic.
-/

open Complex

namespace RHTower

/-- **Strip upper bound discharged in the completed split.** -/
theorem logDeriv_completed_split_of_re_pos {s : ℂ} (hs : 0 < s.re) (h1 : s ≠ 1)
    (hz : riemannZeta s ≠ 0) :
    logDeriv (fun z => archFactor z * riemannZeta z) s
      = logDeriv archFactor s + logDeriv riemannZeta s :=
  logDeriv_completed_split (archFactor_ne_zero_of_re_pos hs h1) hz
    (hasDerivAt_archFactor_of_re_pos hs).differentiableAt
    (differentiableAt_riemannZeta h1)

/-- **Prime/archimedean decomposition of the seam flux on the right half-plane.** The strip and the
absolute-convergence half-plane are the two regions the corpus records separately; both are instances
of this one statement. -/
theorem seamFluxCochain_eq_infinitePrimeFlux_add_archimedean_of_re_pos {s : ℂ}
    (hs : 0 < s.re) (h1 : s ≠ 1) (hz : riemannZeta s ≠ 0) :
    seamFluxCochain s = infinitePrimeFlux s - logDeriv archFactor s := by
  let U : Set ℂ := {z : ℂ | 0 < z.re} \ {1}
  have hUopen : IsOpen U :=
    (isOpen_lt continuous_const Complex.continuous_re).sdiff isClosed_singleton
  have hsU : s ∈ U := ⟨hs, by simpa using h1⟩
  have hev : xi =ᶠ[nhds s] fun z => archFactor z * riemannZeta z := by
    filter_upwards [hUopen.mem_nhds hsU] with z hzU
    exact xi_eq_archFactor_mul_zeta
      (by intro h; subst z; simpa using hzU.1)
      (by simpa using hzU.2)
      (Gammaℝ_ne_zero_of_re_pos hzU.1)
  have hlog : logDeriv xi s =
      logDeriv (fun z => archFactor z * riemannZeta z) s := by
    rw [logDeriv_apply, logDeriv_apply, hev.deriv_eq, hev.eq_of_nhds]
  rw [seamFluxCochain, infinitePrimeFlux, hlog,
    logDeriv_completed_split_of_re_pos hs h1 hz]
  ring

/-- **Unconditional completed split on `Re s ≥ 1`.** Classical non-vanishing of `ζ` on the closed
half-plane discharges the side condition, so no hypothesis about zeros survives.  This covers the
line `Re s = 1`, which neither of the corpus's two regional statements reaches: the strip form needs
`Re s < 1` and the absolute-convergence form needs `Re s > 1`. -/
theorem logDeriv_completed_split_of_one_le_re {s : ℂ} (hs : 1 ≤ s.re) (h1 : s ≠ 1) :
    logDeriv (fun z => archFactor z * riemannZeta z) s
      = logDeriv archFactor s + logDeriv riemannZeta s :=
  logDeriv_completed_split_of_re_pos (lt_of_lt_of_le zero_lt_one hs) h1
    (riemannZeta_ne_zero_of_one_le_re hs)

/-- **Unconditional prime/archimedean decomposition on `Re s ≥ 1`.** -/
theorem seamFluxCochain_eq_infinitePrimeFlux_add_archimedean_of_one_le_re {s : ℂ}
    (hs : 1 ≤ s.re) (h1 : s ≠ 1) :
    seamFluxCochain s = infinitePrimeFlux s - logDeriv archFactor s :=
  seamFluxCochain_eq_infinitePrimeFlux_add_archimedean_of_re_pos
    (lt_of_lt_of_le zero_lt_one hs) h1 (riemannZeta_ne_zero_of_one_le_re hs)

/-- **Completed split off the poles.** Positivity of the real part is not needed either: the
archimedean factor is nonvanishing and differentiable wherever `Γ(s/2)` is off its poles. -/
theorem logDeriv_completed_split_off_poles {s : ℂ}
    (hpole : ∀ m : ℕ, s / 2 ≠ -(m : ℂ)) (h1 : s ≠ 1) (hz : riemannZeta s ≠ 0) :
    logDeriv (fun z => archFactor z * riemannZeta z) s
      = logDeriv archFactor s + logDeriv riemannZeta s :=
  logDeriv_completed_split
    (archFactor_ne_zero_iff.mpr ⟨h1, fun n hc => hpole n (by rw [hc]; ring)⟩) hz
    (hasDerivAt_archFactor_off_poles hpole).differentiableAt
    (differentiableAt_riemannZeta h1)

/-- **Prime/archimedean decomposition off the poles.** With the pole-free set known to be open, the
neighbourhood on which `ξ = archFactor · ζ` is available everywhere off the trivial-zero ladder, so
the decomposition holds on the whole plane except at `s = 1` and the poles `-2, -4, …`. -/
theorem seamFluxCochain_eq_infinitePrimeFlux_add_archimedean_off_poles {s : ℂ}
    (hpole : ∀ m : ℕ, s / 2 ≠ -(m : ℂ)) (h1 : s ≠ 1) (hz : riemannZeta s ≠ 0) :
    seamFluxCochain s = infinitePrimeFlux s - logDeriv archFactor s := by
  let U : Set ℂ := {z : ℂ | ∀ m : ℕ, z / 2 ≠ -(m : ℂ)} \ {1}
  have hUopen : IsOpen U := isOpen_setOf_offPoles.sdiff isClosed_singleton
  have hsU : s ∈ U := ⟨hpole, by simpa using h1⟩
  have hev : xi =ᶠ[nhds s] fun z => archFactor z * riemannZeta z := by
    filter_upwards [hUopen.mem_nhds hsU] with z hzU
    exact xi_eq_archFactor_mul_zeta
      (fun hc => hzU.1 0 (by rw [hc]; simp))
      (by simpa using hzU.2)
      (Gammaℝ_ne_zero_off_poles hzU.1)
  have hlog : logDeriv xi s =
      logDeriv (fun z => archFactor z * riemannZeta z) s := by
    rw [logDeriv_apply, logDeriv_apply, hev.deriv_eq, hev.eq_of_nhds]
  rw [seamFluxCochain, infinitePrimeFlux, hlog,
    logDeriv_completed_split_off_poles hpole h1 hz]
  ring

/-- **Reflection formula off the poles.** The strip hypothesis was only ever used to place `s` and
`1 - s` where the seam decomposition was available; with the off-poles decomposition the identity
holds wherever both archimedean factors are regular and `ζ` is nonzero at both points. -/
theorem logDeriv_riemannZeta_add_reflect_off_poles {s : ℂ}
    (hs : ∀ m : ℕ, s / 2 ≠ -(m : ℂ)) (h1s : ∀ m : ℕ, (1 - s) / 2 ≠ -(m : ℂ))
    (hz : riemannZeta s ≠ 0) (hz' : riemannZeta (1 - s) ≠ 0) :
    logDeriv riemannZeta s + logDeriv riemannZeta (1 - s)
      = (Real.log Real.pi : ℂ)
        - Complex.digamma (s / 2) / 2 - Complex.digamma ((1 - s) / 2) / 2 := by
  have h0 : s ≠ 0 := fun h => hs 0 (by rw [h]; norm_num)
  have h1 : s ≠ 1 := fun h => h1s 0 (by rw [h]; norm_num)
  have h1sne1 : (1 : ℂ) - s ≠ 1 := fun hc => h0 (by linear_combination -hc)
  have hA := seamFluxCochain_eq_infinitePrimeFlux_add_archimedean_off_poles hs h1 hz
  have hB := seamFluxCochain_eq_infinitePrimeFlux_add_archimedean_off_poles h1s h1sne1 hz'
  rw [seamFluxCochain, infinitePrimeFlux] at hA hB
  have hrec := logDeriv_xi_reciprocity s
  have harch := logDeriv_archFactor_add_reflect hs h1s h0 h1
  rw [logDeriv_Gammaℝ_reflect_off_poles hs h1s] at harch
  linear_combination hA + hB + hrec - harch

/-- **Reflection formula for the logarithmic derivative of `ζ`.** On the open critical strip, away
from the zeros of `ζ` at `s` and at `1 - s`,

  `ζ'/ζ(s) + ζ'/ζ(1-s) = log π - ψ(s/2)/2 - ψ((1-s)/2)/2`.

The completed reciprocity `logDeriv ξ(1-s) = -logDeriv ξ(s)` kills the `ξ` terms, and the archimedean
reflection sum contributes only the Gamma weld, its rational part having cancelled. -/
theorem logDeriv_riemannZeta_add_reflect_of_strip {s : ℂ}
    (h0 : 0 < s.re) (h1 : s.re < 1)
    (hz : riemannZeta s ≠ 0) (hz' : riemannZeta (1 - s) ≠ 0) :
    logDeriv riemannZeta s + logDeriv riemannZeta (1 - s)
      = (Real.log Real.pi : ℂ)
        - Complex.digamma (s / 2) / 2 - Complex.digamma ((1 - s) / 2) / 2 := by
  have h1sre : 0 < (1 - s).re := by
    rw [Complex.sub_re, Complex.one_re]
    linarith
  exact logDeriv_riemannZeta_add_reflect_off_poles
    (div_two_ne_neg_nat_of_re_pos h0) (div_two_ne_neg_nat_of_re_pos h1sre) hz hz'

/-- **Reflection formula in the half-plane of absolute convergence.** Both nonvanishing hypotheses
are discharged there: `ζ(s) ≠ 0` classically for `Re s > 1`, and `ζ(1-s) ≠ 0` because reflection
preserves the zeta zero locus off the two pole ladders. What remains is the arithmetic condition
that `1 - s` avoid the trivial zeros, i.e. that `s` not be an odd integer `1, 3, 5, …`. -/
theorem logDeriv_riemannZeta_add_reflect_of_one_lt_re {s : ℂ} (hre : 1 < s.re)
    (hodd : ∀ m : ℕ, s ≠ 1 + 2 * (m : ℂ)) :
    logDeriv riemannZeta s + logDeriv riemannZeta (1 - s)
      = (Real.log Real.pi : ℂ)
        - Complex.digamma (s / 2) / 2 - Complex.digamma ((1 - s) / 2) / 2 := by
  have hs : ∀ m : ℕ, s / 2 ≠ -(m : ℂ) := div_two_ne_neg_nat_of_re_pos (by linarith)
  have h1s : ∀ m : ℕ, (1 - s) / 2 ≠ -(m : ℂ) := fun m hc =>
    hodd m (by linear_combination -2 * hc)
  have hz : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hre
  exact logDeriv_riemannZeta_add_reflect_off_poles hs h1s hz
    (fun h => hz ((riemannZeta_one_sub_eq_zero_iff_off_poles hs h1s).mp h))

/-- **Reflection formula on the critical line.** At `s = 1/2 + it` the reflection `1 - s` is
`1/2 - it`, so the identity becomes a relation between the two conjugate points of the line and the
two conjugate archimedean modes. -/
theorem logDeriv_riemannZeta_add_reflect_criticalLine {t : ℝ}
    (hz : riemannZeta (1 / 2 + (t : ℂ) * Complex.I) ≠ 0)
    (hz' : riemannZeta (1 / 2 - (t : ℂ) * Complex.I) ≠ 0) :
    logDeriv riemannZeta (1 / 2 + (t : ℂ) * Complex.I)
        + logDeriv riemannZeta (1 / 2 - (t : ℂ) * Complex.I)
      = (Real.log Real.pi : ℂ)
        - Complex.digamma (1 / 4 + (t : ℂ) * Complex.I / 2) / 2
        - Complex.digamma (1 / 4 - (t : ℂ) * Complex.I / 2) / 2 := by
  have hre : (1 / 2 + (t : ℂ) * Complex.I).re = 1 / 2 := by
    simp [Complex.add_re, Complex.mul_re]
  have hrefl : (1 : ℂ) - (1 / 2 + (t : ℂ) * Complex.I) = 1 / 2 - (t : ℂ) * Complex.I := by
    ring
  have hkey := logDeriv_riemannZeta_add_reflect_of_strip (s := 1 / 2 + (t : ℂ) * Complex.I)
    (by rw [hre]; norm_num) (by rw [hre]; norm_num) hz (by rwa [hrefl])
  rw [hrefl, show (1 / 2 + (t : ℂ) * Complex.I) / 2 = 1 / 4 + (t : ℂ) * Complex.I / 2 by ring,
    show (1 / 2 - (t : ℂ) * Complex.I) / 2 = 1 / 4 - (t : ℂ) * Complex.I / 2 by ring] at hkey
  exact hkey

/-- The logarithmic derivative of `ζ` respects complex conjugation. -/
theorem logDeriv_riemannZeta_conj (z : ℂ) :
    logDeriv riemannZeta ((starRingEnd ℂ) z)
      = (starRingEnd ℂ) (logDeriv riemannZeta z) := by
  have hfun : ((starRingEnd ℂ) ∘ riemannZeta ∘ (starRingEnd ℂ)) = riemannZeta := by
    funext w
    simp [Function.comp_def, riemannZeta_conj]
  have hderiv := deriv_conj_conj (f := riemannZeta)
  rw [hfun] at hderiv
  have hd : deriv riemannZeta ((starRingEnd ℂ) z)
      = (starRingEnd ℂ) (deriv riemannZeta z) := by
    have := congrFun hderiv ((starRingEnd ℂ) z)
    simpa [Function.comp_def] using this
  rw [logDeriv_apply, logDeriv_apply, hd, riemannZeta_conj, map_div₀]

/-- **Real part of `ζ'/ζ` on the critical line.** Away from the zeros, the real part is pinned to an
explicit archimedean quantity:

  `2·Re(ζ'/ζ(1/2+it)) = log π - Re ψ(1/4 + it/2)`.

The reflection `1 - s` of a critical-line point is its complex conjugate, so the reflection formula
becomes a statement about real parts.  The second nonvanishing hypothesis is discharged: `ζ` at the
conjugate point is the conjugate value. -/
theorem re_logDeriv_riemannZeta_criticalLine {t : ℝ}
    (hz : riemannZeta (1 / 2 + (t : ℂ) * Complex.I) ≠ 0) :
    2 * (logDeriv riemannZeta (1 / 2 + (t : ℂ) * Complex.I)).re
      = Real.log Real.pi - (Complex.digamma (1 / 4 + (t : ℂ) * Complex.I / 2)).re := by
  have hc1 : (starRingEnd ℂ) (1 / 2 + (t : ℂ) * Complex.I)
      = 1 / 2 - (t : ℂ) * Complex.I := by
    simp [Complex.conj_ofReal, Complex.conj_I, map_ofNat]
    ring
  have hc2 : (starRingEnd ℂ) (1 / 4 + (t : ℂ) * Complex.I / 2)
      = 1 / 4 - (t : ℂ) * Complex.I / 2 := by
    simp [Complex.conj_ofReal, Complex.conj_I, map_ofNat]
    ring
  have hz' : riemannZeta (1 / 2 - (t : ℂ) * Complex.I) ≠ 0 := by
    rw [← hc1, riemannZeta_conj]
    simpa using hz
  have hkey := logDeriv_riemannZeta_add_reflect_criticalLine (t := t) hz hz'
  rw [← hc1, logDeriv_riemannZeta_conj, ← hc2,
    ReflectedDigammaAnomaly.digamma_conj] at hkey
  have hR : ((2 * (logDeriv riemannZeta (1 / 2 + (t : ℂ) * Complex.I)).re : ℝ) : ℂ)
      = ((Real.log Real.pi
          - (Complex.digamma (1 / 4 + (t : ℂ) * Complex.I / 2)).re : ℝ) : ℂ) := by
    rw [← Complex.add_conj]
    push_cast
    rw [show ((Complex.digamma (1 / 4 + (t : ℂ) * Complex.I / 2)).re : ℂ)
        = (Complex.digamma (1 / 4 + (t : ℂ) * Complex.I / 2)
            + (starRingEnd ℂ) (Complex.digamma (1 / 4 + (t : ℂ) * Complex.I / 2))) / 2 by
      rw [Complex.add_conj]; push_cast; ring]
    linear_combination hkey
  exact Complex.ofReal_inj.mp hR

/-- **Unconditional upper bound for `Re(ζ'/ζ)` on the critical line.** The archimedean mode is
minimised on the real axis, so the critical-line value relation becomes an explicit bound with no
zeta-side input:

  `2·Re(ζ'/ζ(1/2+it)) ≤ log π - Re ψ(1/4)`. -/
theorem re_logDeriv_riemannZeta_criticalLine_le {t : ℝ}
    (hz : riemannZeta (1 / 2 + (t : ℂ) * Complex.I) ≠ 0) :
    2 * (logDeriv riemannZeta (1 / 2 + (t : ℂ) * Complex.I)).re
      ≤ Real.log Real.pi - (Complex.digamma (1 / 4 : ℂ)).re := by
  have hdiv2 : ∀ z : ℂ, (z / 2).re = z.re / 2 := by
    intro z
    rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, Complex.div_ofReal_re]
  have hid := re_logDeriv_riemannZeta_criticalLine hz
  have hmin := re_logDeriv_Gammaℝ_real_le (σ := 1 / 2) (by norm_num) t
  have hp1 : ∀ m : ℕ, (((1 / 2 : ℝ) : ℂ)) / 2 ≠ -(m : ℂ) :=
    div_two_ne_neg_nat_of_re_pos (by norm_num)
  have hp2 : ∀ m : ℕ, (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) / 2 ≠ -(m : ℂ) :=
    div_two_ne_neg_nat_of_re_pos (by simp [Complex.add_re, Complex.mul_re])
  rw [logDeriv_Gammaℝ_off_poles hp1, logDeriv_Gammaℝ_off_poles hp2,
    show (((1 / 2 : ℝ) : ℂ)) / 2 = (1 / 4 : ℂ) by norm_num,
    show (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) / 2
        = 1 / 4 + (t : ℂ) * Complex.I / 2 by push_cast; ring,
    Complex.sub_re, Complex.sub_re] at hmin
  simp only [hdiv2] at hmin
  linarith

/-- **Mirror-point value relation on a vertical line.** For `0 < σ < 1` the reflection `1 - s` of
`s = σ + it` is the conjugate of the mirror point `(1-σ) + it` at the same height, so the reflection
formula becomes a relation between the two real parts at a common height. Nonvanishing at the
mirror point is not a separate hypothesis: reflection and conjugation together carry the zero at
one point to a zero at the other. -/
theorem re_logDeriv_riemannZeta_add_mirror {σ t : ℝ} (h0 : 0 < σ) (h1 : σ < 1)
    (hz : riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0) :
    (logDeriv riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)).re
        + (logDeriv riemannZeta ((1 - (σ : ℂ)) + (t : ℂ) * Complex.I)).re
      = Real.log Real.pi
        - (Complex.digamma (((σ : ℂ) + (t : ℂ) * Complex.I) / 2)).re / 2
        - (Complex.digamma (((1 - (σ : ℂ)) + (t : ℂ) * Complex.I) / 2)).re / 2 := by
  have hconj : (starRingEnd ℂ) ((1 - (σ : ℂ)) + (t : ℂ) * Complex.I)
      = 1 - ((σ : ℂ) + (t : ℂ) * Complex.I) := by
    simp [Complex.conj_ofReal, Complex.conj_I]
    ring
  have hre : ((σ : ℂ) + (t : ℂ) * Complex.I).re = σ := by
    simp [Complex.add_re, Complex.mul_re]
  have hzrefl : riemannZeta (1 - ((σ : ℂ) + (t : ℂ) * Complex.I)) ≠ 0 := fun h =>
    hz ((riemannZeta_one_sub_eq_zero_iff (s := (σ : ℂ) + (t : ℂ) * Complex.I)
      (by rw [hre]; exact h0) (by rw [hre]; exact h1)).mp h)
  have hkey := logDeriv_riemannZeta_add_reflect_of_strip
    (s := (σ : ℂ) + (t : ℂ) * Complex.I) (by rw [hre]; exact h0) (by rw [hre]; exact h1)
    hz hzrefl
  rw [← hconj, logDeriv_riemannZeta_conj] at hkey
  rw [show (starRingEnd ℂ) ((1 - (σ : ℂ)) + (t : ℂ) * Complex.I) / 2
      = (starRingEnd ℂ) (((1 - (σ : ℂ)) + (t : ℂ) * Complex.I) / 2) by
    rw [map_div₀, map_ofNat], ReflectedDigammaAnomaly.digamma_conj] at hkey
  have hre2 := congrArg Complex.re hkey
  have hdiv2 : ∀ z : ℂ, (z / 2).re = z.re / 2 := by
    intro z
    rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, Complex.div_ofReal_re]
  have hcr : ∀ z : ℂ, ((starRingEnd ℂ) z).re = z.re := fun z => Complex.conj_re z
  simp only [Complex.add_re, Complex.sub_re, Complex.ofReal_re] at hre2
  simp only [hdiv2, hcr] at hre2
  linarith

/-- **Unconditional bound at a mirror pair.** Minimality of the archimedean mode on the real axis
turns the mirror-point relation into a bound depending only on the abscissa. -/
theorem re_logDeriv_riemannZeta_add_mirror_le {σ t : ℝ} (h0 : 0 < σ) (h1 : σ < 1)
    (hz : riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0) :
    (logDeriv riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)).re
        + (logDeriv riemannZeta ((1 - (σ : ℂ)) + (t : ℂ) * Complex.I)).re
      ≤ Real.log Real.pi
        - (Complex.digamma ((σ : ℂ) / 2)).re / 2
        - (Complex.digamma ((1 - (σ : ℂ)) / 2)).re / 2 := by
  have hdiv2 : ∀ z : ℂ, (z / 2).re = z.re / 2 := by
    intro z
    rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, Complex.div_ofReal_re]
  have hid := re_logDeriv_riemannZeta_add_mirror h0 h1 hz
  have hmin1 := re_logDeriv_Gammaℝ_real_le (σ := σ) h0 t
  have hmin2 := re_logDeriv_Gammaℝ_real_le (σ := 1 - σ) (by linarith) t
  have hp1 : ∀ m : ℕ, ((σ : ℝ) : ℂ) / 2 ≠ -(m : ℂ) :=
    div_two_ne_neg_nat_of_re_pos (by simpa using h0)
  have hp2 : ∀ m : ℕ, (((σ : ℝ) : ℂ) + (t : ℂ) * Complex.I) / 2 ≠ -(m : ℂ) :=
    div_two_ne_neg_nat_of_re_pos (by simpa [Complex.add_re, Complex.mul_re] using h0)
  have hp3 : ∀ m : ℕ, (((1 - σ : ℝ)) : ℂ) / 2 ≠ -(m : ℂ) :=
    div_two_ne_neg_nat_of_re_pos (by simpa using (by linarith : (0 : ℝ) < 1 - σ))
  have hp4 : ∀ m : ℕ, ((((1 - σ : ℝ)) : ℂ) + (t : ℂ) * Complex.I) / 2 ≠ -(m : ℂ) :=
    div_two_ne_neg_nat_of_re_pos
      (by simpa [Complex.add_re, Complex.mul_re] using (by linarith : (0 : ℝ) < 1 - σ))
  rw [logDeriv_Gammaℝ_off_poles hp1, logDeriv_Gammaℝ_off_poles hp2,
    Complex.sub_re, Complex.sub_re] at hmin1
  rw [logDeriv_Gammaℝ_off_poles hp3, logDeriv_Gammaℝ_off_poles hp4,
    Complex.sub_re, Complex.sub_re] at hmin2
  simp only [hdiv2, Complex.ofReal_re] at hmin1 hmin2
  rw [show (((1 - σ : ℝ)) : ℂ) = 1 - (σ : ℂ) by push_cast; ring] at hmin2
  linarith

end RHTower
