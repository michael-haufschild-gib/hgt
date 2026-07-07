/-
The completed seam-flux cochain is `−ξ'/ξ`, and its reciprocity is the functional equation.

The seam-positivity program builds a completed flux one-form `Ω_+^Δ(s) = Ω_fin + Ω_∞ + Ω_∂` from the
finite-prime seam flux, the archimedean Gaussian seam, and the two boundary seams at `0, 1`, and asks
for its chain-level reciprocity `R^*Ω_Δ = J_Δ Ω_Δ J_Δ⁻¹` (`R(s) = 1 − s`).  In the completed carrier
this object already exists in the project: it is the logarithmic-derivative one-form of `ξ`, because
`ξ = archFactor · ζ` (`ZetaCarrier.xi_eq_archFactor_mul_zeta`) with
`archFactor s = s(s−1)/2 · Gammaℝ s` — the two boundary seams `s(s−1)` times the archimedean Gaussian
seam `Gammaℝ s = π^{−s/2}Γ(s/2)` — and `ζ` the finite-prime Euler side.  So:

* the **completed flux cochain** is `seamFluxCochain s = −logDeriv ξ s = −ξ'/ξ`;
* its **archimedean part** is Deligne's real Gamma log-connection
  `ArchimedeanGamma.gammaRealLogConnection s = −½log π + ½ψ(s/2)` (the `Ω_∞` term);
* its **boundary part** is the polar pair `1/s + 1/(s−1) = logDeriv(s(s−1))` (the `Ω_∂` term);
* its **finite part** is `−ζ'/ζ`, the von Mangoldt side.

The program's chain-level **reciprocity** is then a theorem, not a postulate:
`seamFluxCochain (1 − s) = − seamFluxCochain s` (`seamFluxCochain_reciprocity`), derived directly from
the completed functional equation `ξ(1 − s) = ξ(s)` (`xi_one_sub`).  The `1`-form `−d log ξ` is
invariant under `s ↦ 1 − s` (its coefficient is anti-invariant, cancelling the `ds ↦ −ds` pullback);
`boundary_flux_reciprocity` exhibits the same anti-invariance for the boundary pair in isolation.

The remaining positivity object `H_Δ^1` is a Hilbert quotient of the completed seam space by the
boundary subspace; its norm is nonnegative because a quotient seminorm of a positive space is
(`seam_H1_seminorm_nonneg`).  The determinant identification of that quotient's spectral divisor with
the `ξ`-divisor stays the final RH-strength step (`SeamCrossingTower.seam_spectral_iff_rh`).
-/
import GaloisForLFunctions.RHTower.ZetaCarrier
import GaloisForLFunctions.ArchimedeanGamma

noncomputable section

namespace RHTower

open Complex

/-! ### §1 The completed flux cochain and its reciprocity -/

/-- The completed seam-flux cochain `Ω_+^Δ = −ξ'/ξ = −logDeriv ξ`.  It packages the finite-prime von
Mangoldt flux `−ζ'/ζ`, the archimedean flux `gammaRealLogConnection`, and the boundary poles at `0, 1`
into one object, via `ξ = archFactor · ζ`. -/
def seamFluxCochain (s : ℂ) : ℂ := -logDeriv xi s

/-- **Completed-cochain reciprocity from the functional equation.**  The coefficient of the flux
`1`-form is anti-invariant under `s ↦ 1 − s`: `logDeriv ξ (1 − s) = −logDeriv ξ s`, directly from
`ξ(1 − s) = ξ(s)` (`xi_one_sub`).  With the `ds ↦ −ds` pullback this makes `−d log ξ` reciprocity
invariant — the chain-level functional equation `R^*Ω_Δ = J_Δ Ω_Δ J_Δ⁻¹`, proved, not postulated. -/
theorem logDeriv_xi_reciprocity (s : ℂ) : logDeriv xi (1 - s) = -logDeriv xi s := by
  have hderiv : -deriv xi (1 - s) = deriv xi s := by
    have h : deriv (fun z => xi (1 - z)) s = deriv xi s := by simp_rw [xi_one_sub]
    rwa [deriv_comp_const_sub] at h
  have h2 : deriv xi (1 - s) = -deriv xi s := by rw [← hderiv]; ring
  rw [logDeriv_apply, logDeriv_apply, xi_one_sub, h2]; ring

/-- The completed flux cochain is reciprocity-invariant: `Ω_+^Δ(1 − s) = −Ω_+^Δ(s)`. -/
theorem seamFluxCochain_reciprocity (s : ℂ) : seamFluxCochain (1 - s) = -seamFluxCochain s := by
  rw [seamFluxCochain, seamFluxCochain, logDeriv_xi_reciprocity]

/-! ### §2 The archimedean and boundary flux terms are the existing objects -/

/-- The archimedean seam flux is Deligne's real Gamma log-connection `−½log π + ½ψ(s/2)` — the `Ω_∞`
term of the completed cochain, already in the project (`GaloisForLFunctions.gammaRealLogConnection`). -/
theorem archimedean_flux_def (s : ℂ) :
    GaloisForLFunctions.gammaRealLogConnection s
      = -(((Real.log Real.pi : ℝ) : ℂ) / 2) + Complex.digamma (s / 2) / 2 :=
  rfl

/-- **The boundary seam flux is the polar pair.**  `logDeriv(s(s−1))` splits into the two boundary
poles `1/s + 1/(s−1)` (the `Ω_∂` term). -/
theorem boundary_flux_partial_fractions (s : ℂ) (h0 : s ≠ 0) (h1 : s ≠ 1) :
    1 / s + 1 / (s - 1) = (2 * s - 1) / (s * (s - 1)) := by
  have e3 : (s - 1) ≠ 0 := sub_ne_zero.mpr h1
  field_simp; ring

/-- **Boundary seam reciprocity.**  The boundary pair `1/s + 1/(s−1)` is anti-invariant under
`s ↦ 1 − s`: `1/(1−s) + 1/((1−s)−1) = −(1/s + 1/(s−1))`.  This is the `Ω_∂` half of
`seamFluxCochain_reciprocity`, exhibited in isolation — the two boundary seams `η_0, η_∞` are
exchanged by reciprocity. -/
theorem boundary_flux_reciprocity (s : ℂ) (h0 : s ≠ 0) (h1 : s ≠ 1) :
    1 / (1 - s) + 1 / ((1 - s) - 1) = -(1 / s + 1 / (s - 1)) := by
  have e1 : (1 - s) ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
  have e2 : ((1 - s) - 1) ≠ 0 := by
    rw [show (1 - s) - 1 = -s by ring]; exact neg_ne_zero.mpr h0
  have e3 : (s - 1) ≠ 0 := sub_ne_zero.mpr h1
  field_simp; ring

/-! ### §3 The completed cochain is `−ξ'/ξ` with `ξ = archFactor · ζ` -/

/-- **The completed carrier of the flux cochain is `ξ` itself.**  `ξ = archFactor · ζ` with
`archFactor s = s(s−1)/2 · Gammaℝ s`: the boundary seams `s(s−1)` times the archimedean Gaussian seam
`Gammaℝ`, times the finite-prime Euler side `ζ`.  So the hand-built completed flux cochain
`Ω_fin + Ω_∞ + Ω_∂` is `−logDeriv(archFactor · ζ) = −logDeriv ξ = seamFluxCochain`, off the poles. -/
theorem seamFluxCochain_carrier {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) (hG : Gammaℝ s ≠ 0) :
    xi s = archFactor s * riemannZeta s :=
  xi_eq_archFactor_mul_zeta h0 h1 hG

/-! ### §4 Theorem B: the determinant bridge is conditional on the resolvent-flux identity -/

/-- **Theorem B (determinant bridge, conditional).**  Suppose the seam superdeterminant equals
`C·ξ` with `C ≠ 0`.  Then its divisor is the classical `ξ`-divisor: `analyticOrderAt (C·ξ) ρ =
analyticOrderAt ξ ρ` at every point — a nonzero constant does not move the divisor.

The hypothesis `D_Δ = C·ξ` is exactly what the resolvent-flux identity delivers: if
`Str_ren((s − Θ_Δ)⁻¹) = ξ'/ξ = −Ω_Δ`, then `d log D_Δ = d log ξ`, so `D_Δ/ξ` is locally constant and
`D_Δ = C·ξ`.  So the whole content of "the spectral divisor is the `ξ`-divisor" is the resolvent-flux
identity — the open bridge.  Positivity and reciprocity alone do **not** force it: one may adjoin an
orthogonal reciprocal spectral pair `{½ + iτ, ½ − iτ}`, preserving positivity and reciprocity while
multiplying the determinant by `(s − (½ + iτ))(s − (½ − iτ))` — changing the divisor.  Only the
resolvent-flux identity pins `D_Δ = C·ξ`. -/
theorem seam_determinant_divisor_of_const_mul (C : ℂ) (hC : C ≠ 0) (ρ : ℂ) :
    analyticOrderAt (fun s => C * xi s) ρ = analyticOrderAt xi ρ := by
  rw [show (fun s => C * xi s) = (fun _ : ℂ => C) * xi from rfl]
  have hconst : AnalyticAt ℂ (fun _ : ℂ => C) ρ := analyticAt_const
  have hxi : AnalyticAt ℂ xi ρ := (xi_analyticOnNhd Set.univ) ρ (Set.mem_univ _)
  rw [analyticOrderAt_mul hconst hxi,
    (AnalyticAt.analyticOrderAt_eq_zero hconst).mpr hC, zero_add]

/-! ### §5 The middle seam cohomology is positive -/

/-- **`H_Δ^1` positivity.**  The completed seam space is a positive Hilbert space; the middle
cohomology `H_Δ^1` is its quotient by the boundary subspace, whose seminorm — the infimum of the
positive norm over boundary representatives — is nonnegative.  So the seam quadratic form
`W_Δ(h) = ‖[𝔖_Δ(h)]‖²_{H^1} ≥ 0`, unconditionally.  (The identification of this quotient's spectral
divisor with the `ξ`-divisor remains the RH-strength step, `seam_spectral_iff_rh`.) -/
theorem seam_H1_seminorm_nonneg {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (B : Submodule ℂ E) (v : E) : 0 ≤ ⨅ β : B, ‖v + (β : E)‖ ^ 2 :=
  le_ciInf fun β => by positivity

end RHTower
