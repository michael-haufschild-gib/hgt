# Steinmetz's reduction theorem for entire compositions

- **Stage:** 3-formalized / not new scientific knowledge (Steinmetz 1980)
- **Serves:** 02 card `entire-composition-hypertranscendence-or-law` (the gap `hgap` of
  `CompositionInnerDecomposition.differentiallyAlgebraic_comp_iff_of_gap`).
- **Statement (Steinmetz 1980, Satz 1/Korollar 1/Satz 2, entire form).**  Let `g` be entire and
  transcendental, `F_μ` entire, `h_μ(z) = H_μ(z, g(z), …, g^{(n)}(z))` with `H_μ` polynomials, and
  `Σ F_μ(g) h_μ ≡ 0` with some `h_μ ≢ 0`.  Then `Σ Q_μ F_μ ≡ 0` for polynomials `Q_μ`, not all zero.
  Consequently `f ∘ g` DA with `g` hypertranscendental forces `f` DA.

## Route

Source: N. Steinmetz, *Über die faktorisierbaren Lösungen gewöhnlicher Differentialgleichungen*,
Math. Z. 170 (1980) 169–180, §4 (read from GDZ scan).  His proof of Satz 1 builds auxiliary
families `H_s` by an iterated elimination and then applies Nevanlinna's second main theorem for
**constant** targets — no small-function second main theorem is needed.

Simplification used here: the iterated construction is replaced by one linear-algebra step.
Choose `s = (m+1)(q+1)` points `t_j` avoiding the zeros of every `F_μ`, and `D = m(q+1)`.  The
homogeneous system `P_μ(t_j) = c_j F_μ(t_j)` (unknowns: coefficients of `P_μ`, `deg ≤ D`, and `c_j`)
has `(m+1)` more unknowns than equations, so it has a solution with some `P_μ ≠ 0`.  Then
`N = Σ P_μ(g) h_μ` vanishes on `g⁻¹{t_j}`.  If `N ≢ 0`:

- `Σ_j N(r, t_j, g) ≤ N(r, 0, N) + N(r, 0, g')` (divisor inequality at each preimage);
- `N(r, 0, N) ≤ m(r, N) + O(1) ≤ D·T(r,g) + Σ m(r, h_μ) + O(1)`;
- second main theorem `(s − 2)T ≤ Σ_j N(r, t_j, g) + S(r,g)`; jet bounds `T(r, g^{(j)}) ≤ 2^{n+1}T + C`
  along one sequence of radii (`IteratedDerivativeGrowth.exists_radii_jet_bound_and_error`).

So `(q − 1 − 2^{n+1} − K)T ≤ o(T)`, false for `q` large.  Korollar 1 is the elementary elimination
`G_μ = P_m F_μ − P_μ F_m`.  Satz 2: Faà di Bruno (`CompositionJetPolynomials.compJetPoly`) in the
meromorphic field of the plane, the substituted polynomial is nonzero (specialize `g' = 1`,
`g^{(i)} = 0`), and hypertranscendence of `g` keeps every nonzero coefficient nonzero.

## Status
- [x] interpolation lemma — `SteinmetzInterpolation.exists_polynomials_proportional_at_points`
- [x] Nevanlinna core (`N ≡ 0`) — `SteinmetzNevanlinnaCore.sum_eq_zero_of_vanishing_on_levels`
- [x] Satz 1, Korollar 1 — `SteinmetzReduction`
- [x] Satz 2 (Faà di Bruno) and the card's full Boolean law — `EntireCompositionSteinmetz`,
  `EntireCompositionOrLaw`; card 10 promoted

## Log
- 2026-09-29 — proof extracted from the 1980 paper; route fixed.
- 2026-09-29 — all four steps Lean, axiom-clean; wired.
