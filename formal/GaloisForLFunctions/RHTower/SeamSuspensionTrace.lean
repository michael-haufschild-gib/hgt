/-
The seam-suspension trace: the compression mechanism and the two equivalent forms of the bridge.

The seam-suspension construction assembles the completed flux cochain `−ξ'/ξ` as a flat supertrace of a
resolvent `(s − Θ_Δ)⁻¹` over a three-degree seam complex — finite-prime closed returns (`ζ'/ζ`), the
Gaussian archimedean oscillator (`Γ_ℝ'/Γ_ℝ`), and two boundary states (`1/s + 1/(s−1)`) — summing to
`ξ'/ξ` because `ξ = ½s(s−1)Γ_ℝ ζ`.  Three formalizable cores of that construction:

* **§4 sector split** (`logDeriv_completed_split`): the completed log-derivative decomposes into the
  archimedean sector and the finite sector, `logDeriv(archFactor · ζ) = logDeriv archFactor +
  logDeriv ζ`.  With `ξ = archFactor · ζ` (`ZetaCarrier.xi_eq_archFactor_mul_zeta`) and
  `archFactor = s(s−1)/2 · Gammaℝ` this is the flat supertrace identity `Str^♭ = ξ'/ξ` at the
  log-derivative level: the three seam sectors sum to `ξ'/ξ`.

* **§7 compression mechanism** (`supertrace_supercommutator_zero`, `flat_eq_cohomology_trace`): the
  flat (whole-complex) supertrace descends to the cohomology supertrace because the difference
  `(I − P)·R` is a commutator, and the trace of a commutator vanishes.  So
  `Str((s − Θ_Δ)⁻¹ | 𝒞_Δ) = Str((s − Θ_Δ)⁻¹ | H_Δ)` once the Hodge relation `I − P = dG + Gd` holds —
  this is the exact algebraic content of the Seam Hodge Compression Lemma.

* **§10 Herglotz positivity** (`herglotz_rank_one_psd`): the equivalent spectral form of the bridge.
  A Nevanlinna/Herglotz function `G(z) = ∫ dν(λ)/(z − iλ)` with `ν ≥ 0` has a positive-semidefinite
  kernel `K(z,w) = (G(z) + conj G(w))/(z + conj w)`, because it is an integral of the rank-one PSD
  kernels `v(z)·conj(v(w))`, `v(z) = 1/(z − iλ)`.  The rank-one PSD core is proved here: the Gram-type
  sum `Σ_{i,j} v_i·conj(v_j)·c_i·conj(c_j) = |Σ_i c_i v_i|² ≥ 0`.

Both the Hodge relation `I − P = dG + Gd` (with renormalized cyclicity) and the Herglotz positivity
`K_Δ ≥ 0` are the two faces of the single remaining bridge; each would give
`Str((s − Θ_Δ)⁻¹ | H_Δ) = ξ'/ξ` on the positive `H_Δ^1`.
-/
import GaloisForLFunctions.RHTower.ZetaCarrier

noncomputable section

namespace RHTower

open Complex Matrix

/-! ### §4 The sector split of the completed log-derivative -/

/-- **The completed flux cochain splits into archimedean and finite sectors.**
`logDeriv(archFactor · ζ) = logDeriv archFactor + logDeriv ζ`.  With `ξ = archFactor · ζ` and
`archFactor = s(s−1)/2 · Gammaℝ`, this is the seam-suspension flat supertrace `Str^♭ = ξ'/ξ` at the
log-derivative level: the boundary sector `1/s + 1/(s−1)` (from `s(s−1)`), the archimedean sector
`Γ_ℝ'/Γ_ℝ` (from `Gammaℝ`), and the finite sector `ζ'/ζ` sum to `ξ'/ξ`. -/
theorem logDeriv_completed_split {s : ℂ} (haf : archFactor s ≠ 0) (hz : riemannZeta s ≠ 0)
    (hda : DifferentiableAt ℂ archFactor s) (hdz : DifferentiableAt ℂ riemannZeta s) :
    logDeriv (fun z => archFactor z * riemannZeta z) s
      = logDeriv archFactor s + logDeriv riemannZeta s :=
  logDeriv_mul s haf hz hda hdz

/-! ### §7 The compression mechanism: flat supertrace = cohomology supertrace -/

/-- **The supertrace of a supercommutator vanishes.**  `tr(dX − Xd) = 0`, by trace cyclicity.  This is
the algebraic engine of the Seam Hodge Compression Lemma. -/
theorem supertrace_supercommutator_zero {n : Type*} [Fintype n] [DecidableEq n]
    (d X : Matrix n n ℂ) : (d * X - X * d).trace = 0 := by
  rw [Matrix.trace_sub, Matrix.trace_mul_comm, sub_self]

/-- **Flat supertrace descends to cohomology.**  If the off-cohomology part `(I − P)·R` of the
resolvent is a commutator `dY − Yd` (which the Hodge relation `I − P = dG + Gd` produces, since
`[Θ_Δ, d] = 0` makes `R` commute with `d`), then the whole-complex supertrace equals the cohomology
supertrace: `tr R = tr(P·R)`.  So `Str((s − Θ_Δ)⁻¹ | 𝒞_Δ) = Str((s − Θ_Δ)⁻¹ | H_Δ)` — the exact
compression that would carry the flat identity `Str^♭ = ξ'/ξ` onto the positive `H_Δ^1`. -/
theorem flat_eq_cohomology_trace {n : Type*} [Fintype n] [DecidableEq n]
    (P Res d Y : Matrix n n ℂ) (h : (1 - P) * Res = d * Y - Y * d) :
    Res.trace = (P * Res).trace := by
  have hc : ((1 - P) * Res).trace = 0 := by
    rw [h, Matrix.trace_sub, Matrix.trace_mul_comm, sub_self]
  rw [Matrix.sub_mul, Matrix.one_mul, Matrix.trace_sub] at hc
  exact sub_eq_zero.mp hc

/-! ### §10 The Herglotz kernel positivity (the equivalent spectral form of the bridge) -/

/-- **The Herglotz/Nevanlinna rank-one kernel is positive semidefinite.**  For any nodes and
coefficients, `Σ_{i,j} v_i·conj(v_j)·c_i·conj(c_j) = |Σ_i c_i v_i|² ≥ 0`.  Taking
`v_i = 1/(z_i − iλ)` this is the positivity of the single-pole Herglotz kernel
`1/((z − iλ)(conj w + iλ))`; integrating against `ν ≥ 0` gives the positivity of the seam Herglotz
kernel `K_Δ(z,w) = (G_Δ(z) + conj G_Δ(w))/(z + conj w)`, whose positivity is equivalent (Nevanlinna
realization) to the existence of the self-adjoint seam generator `T_Δ` with
`Str_ren((s − Θ_Δ)⁻¹) = ξ'/ξ`.  This is the spectral face of the remaining bridge. -/
theorem herglotz_rank_one_psd {N : Type*} [Fintype N] (v c : N → ℂ) :
    0 ≤ (∑ i, ∑ j, (v i * (starRingEnd ℂ) (v j)) * (c i * (starRingEnd ℂ) (c j))).re := by
  have hsq : (∑ i, ∑ j, (v i * (starRingEnd ℂ) (v j)) * (c i * (starRingEnd ℂ) (c j)))
      = (∑ i, c i * v i) * (starRingEnd ℂ) (∑ i, c i * v i) := by
    rw [map_sum, Finset.sum_mul_sum]
    congr 1; ext i; congr 1; ext j; simp [map_mul]; ring
  rw [hsq, Complex.mul_conj, Complex.ofReal_re]
  exact Complex.normSq_nonneg _

end RHTower
