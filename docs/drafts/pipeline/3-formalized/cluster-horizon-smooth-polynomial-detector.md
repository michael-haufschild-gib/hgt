# Smooth polynomial-aperture detection from the cluster horizon

- **ID:** cluster-horizon-smooth-polynomial-detector
- **Stage:** 3-formalized
- **Type:** formalization bridge; no novelty claim
- **Source:** review-2410 J4(i); `zeta_hodge_index_cluster_horizon` and complete-form mollification.
- **Statement:** There is an absolute C>0 such that every nontrivial zeta zero
  ρ off the critical line has a smooth compact complex source f and radius a>0
  satisfying `supp f ⊆ [-a,a]`, `Re Wζ(f,f)<0`, and
  `a ≤ C |Re ρ-1/2|⁻² (4+|Im ρ|)²`.

## Paper proof

Let A≥1 be the universal constant in `zeta_hodge_index_cluster_horizon`.
That theorem excludes the Hodge index at radius b if

`b ≥ exp(6)`, `b ≥ 1/δ`, and
`10⁵ A log(|γ|+306) log(b)² ≤ b`,

provided `δ ≤ |Re ρ-1/2|`, δ>0, and |γ|≥2.

For a nontrivial zero set δ=|Re ρ-1/2| and γ=Im ρ. The critical strip gives
0<δ≤1. The proved zero-free strip `riemannZeta_ne_zero_of_im_sq_le` gives
|γ|≥2: otherwise γ²≤4≤32, contradicting that theorem.

Put `H=4+|γ|`, `K=exp(6)+10⁹(A+1)`, `u=KH/δ`, and b=u². Then u≥1,
u≥K, and u≥1/δ. Thus b≥exp(6) and b≥1/δ.

For x>0, `log x ≤ x^(1/4)/(1/4)`. Applying this at x=u² and squaring
the nonnegative sides gives `log(u²)²≤16u`. Also
`log(|γ|+306)≤|γ|+305≤77H`. The chosen K satisfies
`16·10⁵·77 A≤K`, so

`16·10⁵ A log(|γ|+306) ≤ KH ≤ u`.

Multiplying by u proves the remaining horizon condition. Hence the Hodge
index fails at b. The established implication from real compact-source Weil
positivity to the Hodge index supplies a real C² compact source F, supported
in [-b,b], with negative full Weil energy.

The complete-form mollifiers `smooth F k` converge in full Weil energy,
including the prime, Gamma, and polar terms. Each is C∞ and supported in
`[-b-rk,b+rk]`, where `rk=1/(4(k+1))≤1`. Some mollifier retains the strict
negative sign. Embed it in the complex source space and use
`zeta_W_eq_weilFullFunctional` to identify the zero-side form.

Its radius a=b+1 is positive and, since b≥1,

`a≤2b=2K² δ⁻² H²`.

Choose C=2K². Since H≥1, H²≤H³⁸, proving the requested degree-38 bound too.

## Scope and novelty audit

This is a coarse consequence of the existing cluster horizon. Neither the
quadratic bound nor its degree-38 corollary is claimed as a new analytic
estimate. The argument detects a hypothetical off-line zero; it supplies no
global positivity theorem and does not assert that such a zero exists.

## Formal status

- [x] Dependency-closed paper proof of the stronger exact statement.
- [x] Novelty audit: direct consequence of existing corpus results.
- [x] Canonical Lean leaf and degree-38 specialization checked.
- [x] Public declarations audited with `#print axioms`.
- [x] Owning umbrella import added.

Source: `SquareRootThreshold/SmoothWeilDetectorPolynomialAperture.lean`.
The full-source scratch check, all three public transitive axiom audits, and
the canonical `lake --old env lean` check passed. Only `propext`,
`Classical.choice`, and `Quot.sound` occur. The owning umbrella imports the
leaf exactly once. Evidence:
`logs/just-work-2410/SquareRootThreshold__SmoothWeilDetectorPolynomialAperture.{axioms,check}.{json,txt}`.

The exact declarations are `RHTower.exists_smooth_weil_negative_of_not_hodgeIndex`,
`RHTower.exists_smooth_weil_negative_quadratic_aperture`, and
`RHTower.exists_smooth_weil_negative_polynomial_aperture`.
