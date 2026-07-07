/-
The flat seam-resolvent trace identity: the completed flux `−ξ'/ξ` is the sum of three seam sectors.

The seam-suspension model assembles the completed logarithmic current as a flat resolvent supertrace
`Str^♭((s − Θ_Δ)⁻¹)` over a graded seam complex.  The whole-complex trace splits into three sectors,
each an independent local object:

* the **finite-prime sector** `ζ'/ζ = logDeriv ζ` — the von Mangoldt closed-return series
  `−Σ_{p,r} (log p) p^{−rs}` of the prime-power seam tower;
* the **archimedean sector** `Γ_ℝ'/Γ_ℝ = logDeriv Gammaℝ` — the logarithmic derivative of the Gaussian
  seam factor `Gammaℝ s = π^{−s/2} Γ(s/2)`, equal to Deligne's connection coefficient
  `gammaRealLogConnection s = −½log π + ½ψ(s/2)`;
* the **boundary sector** `1/s + 1/(s−1) = d/ds log(s(s−1))` — the two exceptional seams at `0, 1`.

Their sum is the completed flux, because `ξ = ½ s(s−1) Γ_ℝ(s) ζ(s)` and the constant `½` is invisible
to `logDeriv`:

  `logDeriv ξ s = (1/s + 1/(s−1)) + gammaRealLogConnection s + logDeriv ζ s`
  (`logDeriv_xi_sector_sum`),

equivalently `seamFluxCochain s = −(boundary + archimedean + finite)`
(`seamFluxCochain_sector_sum`).  This is the flat seam-resolvent trace identity
`Str^♭((s − Θ_Δ)⁻¹) = ξ'/ξ` at the log-derivative level: the scalar trace decomposition that the later
Hodge/Herglotz compression must lift to the positive middle cohomology `H_Δ^1`.

The archimedean brick `logDeriv Gammaℝ = gammaRealLogConnection` is the new content: mathlib carries the
Gaussian seam factor's derivative only at the single point `s = 1`, and the connection coefficient
existed only as a bare definition; here it is identified with `logDeriv Gammaℝ` at every point where
`Gammaℝ` is nonzero (equivalently `s ∉ {0, −2, −4, …}`).
-/
import GaloisForLFunctions.RHTower.SeamFluxCompletion
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

noncomputable section

namespace RHTower

open Complex Real

/-! ### §1 The archimedean Gaussian-seam sector -/

/-- Where `Gammaℝ s ≠ 0` the half-argument `s/2` avoids the poles of `Γ`: `s/2 ≠ −m` for all `m`. -/
theorem gammaR_half_ne_negNat {s : ℂ} (hG : Complex.Gammaℝ s ≠ 0) :
    ∀ m : ℕ, s / 2 ≠ -(m : ℂ) := by
  intro m hm
  apply hG
  rw [Complex.Gammaℝ_eq_zero_iff]
  exact ⟨m, by rw [eq_neg_iff_add_eq_zero] at hm ⊢; linear_combination 2 * hm⟩

/-- The Gaussian seam factor `Gammaℝ s = π^{−s/2} Γ(s/2)` is differentiable where it is nonzero. -/
theorem differentiableAt_Gammaℝ {s : ℂ} (hG : Complex.Gammaℝ s ≠ 0) :
    DifferentiableAt ℂ Complex.Gammaℝ s := by
  have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hs2 := gammaR_half_ne_negNat hG
  have hEq : Complex.Gammaℝ = fun z => (π : ℂ) ^ (-z / 2) * Complex.Gamma (z / 2) := by
    funext z; exact Complex.Gammaℝ_def z
  rw [hEq]
  have hinnerdiff : DifferentiableAt ℂ (fun z : ℂ => -z / 2) s := by fun_prop
  have hdf : DifferentiableAt ℂ (fun z : ℂ => (π : ℂ) ^ (-z / 2)) s :=
    hinnerdiff.const_cpow (Or.inl hpi)
  have hd2diff : DifferentiableAt ℂ (fun z : ℂ => z / 2) s := by fun_prop
  have hΓ : DifferentiableAt ℂ Complex.Gamma (s / 2) := Complex.differentiableAt_Gamma _ hs2
  exact hdf.mul (hΓ.comp s hd2diff)

/-- **The archimedean seam flux is `Γ_ℝ'/Γ_ℝ`.**  The logarithmic derivative of the Gaussian seam
factor `Gammaℝ s = π^{−s/2} Γ(s/2)` is Deligne's connection coefficient
`gammaRealLogConnection s = −½log π + ½ψ(s/2)`, at every `s` where `Gammaℝ s ≠ 0`.  Splitting
`log Gammaℝ = −(s/2) log π + log Γ(s/2)` gives `logDeriv(π^{−s/2}) = −½log π` (constant-base `cpow`)
and `logDeriv(Γ ∘ (·/2)) = ½ ψ(s/2)` (chain rule with `digamma = logDeriv Γ`). -/
theorem logDeriv_Gammaℝ {s : ℂ} (hG : Complex.Gammaℝ s ≠ 0) :
    logDeriv Complex.Gammaℝ s = GaloisForLFunctions.gammaRealLogConnection s := by
  have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hs2 := gammaR_half_ne_negNat hG
  have hEq : Complex.Gammaℝ = fun z => (π : ℂ) ^ (-z / 2) * Complex.Gamma (z / 2) := by
    funext z; exact Complex.Gammaℝ_def z
  rw [hEq]
  set f := fun z : ℂ => (π : ℂ) ^ (-z / 2) with hf
  set g := fun z : ℂ => Complex.Gamma (z / 2) with hg
  have hf0 : f s ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hpi)
  have hg0 : g s ≠ 0 := Complex.Gamma_ne_zero hs2
  have hinnerdiff : DifferentiableAt ℂ (fun z : ℂ => -z / 2) s := by fun_prop
  have hdf : DifferentiableAt ℂ f s := hinnerdiff.const_cpow (Or.inl hpi)
  have hd2diff : DifferentiableAt ℂ (fun z : ℂ => z / 2) s := by fun_prop
  have hΓ : DifferentiableAt ℂ Complex.Gamma (s / 2) := Complex.differentiableAt_Gamma _ hs2
  have hdg : DifferentiableAt ℂ g s := hΓ.comp s hd2diff
  rw [logDeriv_mul s hf0 hg0 hdf hdg]
  have hlf : logDeriv f s = -(Complex.log (π : ℂ)) / 2 := by
    have hbase : HasDerivAt (fun y : ℂ => (π : ℂ) ^ y)
        ((π : ℂ) ^ (-s / 2) * Complex.log (π : ℂ)) (-s / 2) :=
      (hasStrictDerivAt_const_cpow (Or.inl hpi)).hasDerivAt
    have hinner : HasDerivAt (fun z : ℂ => -z / 2) (-1 / 2 : ℂ) s := by
      simpa using (((hasDerivAt_id s).neg).div_const 2)
    have hd : HasDerivAt f ((π : ℂ) ^ (-s / 2) * Complex.log (π : ℂ) * (-1 / 2)) s :=
      hbase.comp s hinner
    rw [logDeriv_apply, hd.deriv]
    show (π : ℂ) ^ (-s / 2) * Complex.log (π : ℂ) * (-1 / 2) / f s = _
    rw [hf]
    field_simp
  have hlg : logDeriv g s = Complex.digamma (s / 2) / 2 := by
    have hderiv2 : deriv (fun z : ℂ => z / 2) s = 1 / 2 :=
      (((hasDerivAt_id s).div_const 2)).deriv
    rw [hg, show (fun z : ℂ => Complex.Gamma (z / 2)) = Complex.Gamma ∘ (fun z : ℂ => z / 2) from rfl,
      show logDeriv (Complex.Gamma ∘ fun z : ℂ => z / 2) s
        = logDeriv Complex.Gamma ((fun z : ℂ => z / 2) s) * deriv (fun z : ℂ => z / 2) s
        from logDeriv_comp hΓ hd2diff]
    rw [← Complex.digamma_def, hderiv2]
    ring
  rw [hlf, hlg, GaloisForLFunctions.gammaRealLogConnection, Complex.ofReal_log Real.pi_nonneg]
  ring

/-! ### §2 The boundary sector -/

/-- **The boundary seam flux is the polar pair.**  `logDeriv(s(s−1)/2) = 1/s + 1/(s−1)`: the
logarithmic derivative of the two exceptional seams `s, s−1`, with the constant `½` invisible. -/
theorem logDeriv_boundary {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) :
    logDeriv (fun z : ℂ => z * (z - 1) / 2) s = 1 / s + 1 / (s - 1) := by
  have e3 : (s - 1) ≠ 0 := sub_ne_zero.mpr h1
  have hmul : HasDerivAt (fun z : ℂ => z * (z - 1)) (1 * (s - 1) + s * 1) s :=
    (hasDerivAt_id s).mul (by simpa using (hasDerivAt_id s).sub_const 1)
  have hd : HasDerivAt (fun z : ℂ => z * (z - 1) / 2) ((1 * (s - 1) + s * 1) / 2) s :=
    hmul.div_const 2
  rw [logDeriv_apply, hd.deriv]
  show (1 * (s - 1) + s * 1) / 2 / (s * (s - 1) / 2) = 1 / s + 1 / (s - 1)
  field_simp

/-! ### §3 The archimedean factor splits into boundary and archimedean sectors -/

/-- The completed archimedean factor `archFactor = s(s−1)/2 · Gammaℝ` is differentiable where
`Gammaℝ ≠ 0`. -/
theorem differentiableAt_archFactor {s : ℂ} (hG : Complex.Gammaℝ s ≠ 0) :
    DifferentiableAt ℂ archFactor s := by
  have hAF : archFactor = fun z : ℂ => (z * (z - 1) / 2) * Complex.Gammaℝ z := rfl
  rw [hAF]
  exact (by fun_prop : DifferentiableAt ℂ (fun z : ℂ => z * (z - 1) / 2) s).mul
    (differentiableAt_Gammaℝ hG)

/-- **The archimedean factor's flux is boundary + archimedean.**
`logDeriv archFactor s = (1/s + 1/(s−1)) + gammaRealLogConnection s`, from
`archFactor = s(s−1)/2 · Gammaℝ` and the two sector fluxes. -/
theorem logDeriv_archFactor_eq {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) (hG : Complex.Gammaℝ s ≠ 0) :
    logDeriv archFactor s
      = (1 / s + 1 / (s - 1)) + GaloisForLFunctions.gammaRealLogConnection s := by
  have hbdry0 : (fun z : ℂ => z * (z - 1) / 2) s ≠ 0 := by
    show s * (s - 1) / 2 ≠ 0
    exact div_ne_zero (mul_ne_zero h0 (sub_ne_zero.mpr h1)) two_ne_zero
  have hbdrydiff : DifferentiableAt ℂ (fun z : ℂ => z * (z - 1) / 2) s := by fun_prop
  have hAF : archFactor = fun z : ℂ => (z * (z - 1) / 2) * Complex.Gammaℝ z := rfl
  rw [hAF, logDeriv_mul s hbdry0 hG hbdrydiff (differentiableAt_Gammaℝ hG),
    logDeriv_boundary h0 h1, logDeriv_Gammaℝ hG]

/-! ### §4 The total oriented seam trace -/

/-- **The completed carrier's flux is the three-sector sum.**  For the completed carrier
`archFactor · ζ`, off the ζ-divisor:
`logDeriv(archFactor · ζ) s = (1/s + 1/(s−1)) + gammaRealLogConnection s + logDeriv ζ s`
— the boundary, archimedean, and finite-prime sectors. -/
theorem logDeriv_completed_sector_sum {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1)
    (hG : Complex.Gammaℝ s ≠ 0) (hz : riemannZeta s ≠ 0) :
    logDeriv (fun z => archFactor z * riemannZeta z) s
      = (1 / s + 1 / (s - 1)) + GaloisForLFunctions.gammaRealLogConnection s
        + logDeriv riemannZeta s := by
  rw [logDeriv_mul s (archFactor_ne_zero h0 h1 hG) hz
      (differentiableAt_archFactor hG) (differentiableAt_riemannZeta h1),
    logDeriv_archFactor_eq h0 h1 hG]

/-- On the open critical strip `ξ` agrees with the completed carrier `archFactor · ζ` in a
neighbourhood (both sides satisfy `ξ = archFactor · ζ` there), so their logarithmic derivatives
coincide. -/
theorem logDeriv_xi_eq_completed {s : ℂ} (hstrip : 0 < s.re ∧ s.re < 1) :
    logDeriv xi s = logDeriv (fun z => archFactor z * riemannZeta z) s := by
  have hU : IsOpen {z : ℂ | 0 < z.re ∧ z.re < 1} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)
  have heqon : ∀ z ∈ {z : ℂ | 0 < z.re ∧ z.re < 1},
      xi z = archFactor z * riemannZeta z := by
    intro z hz
    obtain ⟨hz1, hz2⟩ := hz
    refine xi_eq_archFactor_mul_zeta ?_ ?_ (Gammaℝ_ne_zero_of_re_pos hz1)
    · intro h; rw [h, Complex.zero_re] at hz1; exact lt_irrefl 0 hz1
    · intro h; rw [h, Complex.one_re] at hz2; exact lt_irrefl 1 hz2
  have hev : xi =ᶠ[nhds s] (fun z => archFactor z * riemannZeta z) :=
    Filter.eventually_of_mem (hU.mem_nhds hstrip) heqon
  rw [logDeriv_apply, logDeriv_apply, hev.deriv_eq, hev.eq_of_nhds]

/-- **The completed flux `ξ'/ξ` is the three-sector sum on the strip.**  For `s` in the open critical
strip off the ζ-divisor:
`logDeriv ξ s = (1/s + 1/(s−1)) + gammaRealLogConnection s + logDeriv ζ s`.
This is the flat seam-resolvent trace identity `Str^♭((s − Θ_Δ)⁻¹) = ξ'/ξ` at the log-derivative
level: the boundary sector `d/ds log(s(s−1))`, the archimedean sector `Γ_ℝ'/Γ_ℝ`, and the
finite-prime sector `ζ'/ζ` sum to `ξ'/ξ`. -/
theorem logDeriv_xi_sector_sum {s : ℂ} (hstrip : 0 < s.re ∧ s.re < 1)
    (hz : riemannZeta s ≠ 0) :
    logDeriv xi s = (1 / s + 1 / (s - 1)) + GaloisForLFunctions.gammaRealLogConnection s
      + logDeriv riemannZeta s := by
  have h0 : s ≠ 0 := by
    intro h; rw [h, Complex.zero_re] at hstrip; exact absurd hstrip.1 (lt_irrefl 0)
  have h1 : s ≠ 1 := by
    intro h; rw [h, Complex.one_re] at hstrip; exact absurd hstrip.2 (lt_irrefl 1)
  rw [logDeriv_xi_eq_completed hstrip,
    logDeriv_completed_sector_sum h0 h1 (Gammaℝ_ne_zero_of_re_pos hstrip.1) hz]

/-- **The seam-flux cochain is minus the three-sector sum.**  In the project's completed-cochain
vocabulary `Ω_Δ = seamFluxCochain = −ξ'/ξ`, so on the strip off the ζ-divisor
`seamFluxCochain s = −((1/s + 1/(s−1)) + gammaRealLogConnection s + logDeriv ζ s)` — the completed
flux is the negated sum of the boundary, archimedean, and finite-prime seam fluxes. -/
theorem seamFluxCochain_sector_sum {s : ℂ} (hstrip : 0 < s.re ∧ s.re < 1)
    (hz : riemannZeta s ≠ 0) :
    seamFluxCochain s
      = -((1 / s + 1 / (s - 1)) + GaloisForLFunctions.gammaRealLogConnection s
        + logDeriv riemannZeta s) := by
  rw [seamFluxCochain, logDeriv_xi_sector_sum hstrip hz]

end RHTower
