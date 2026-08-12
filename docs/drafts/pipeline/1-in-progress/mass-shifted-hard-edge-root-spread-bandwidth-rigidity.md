# Mass-shifted hard-edge root-spread bandwidth rigidity

- **ID:** `mass-shifted-hard-edge-root-spread-bandwidth-rigidity`
- **Stage:** 1-in-progress
- **Type:** CONJECTURE / target theorem
- **Depends on:** `mass-shifted-projective-gauss-root-renewal` and
  `mass-shifted-completed-source-hard-edge-compactness`

## Target

Let `a_j→∞`, `n_j/a_j` stay in a compact positive interval, and let `Q_j` be real-rooted degree
`n_j` hard-edge admission polynomials. Form normalized Cayley half-density packets

```text
g_j(x) = halfDensity(a_j,x) Q_j(cos(2 arctan(x/a_j))).
```

If `g_j` is completed-source tight and converges strongly in `L²(R)` to a nonzero finite-type
Paley--Wiener function, then empirical centered root spread cannot vanish:

```text
liminf_j (1/n_j) sum_k (r_(j,k) - mean_j)^2 > 0.
```

Combined with exact projective Gauss-root renewal, this would forbid simultaneous normalized
collapse of every projective-work account at parabolic first contact.

## Conjecture / proof-or-fail loop

1. Root spread directly bounds trigonometric Bernstein energy. **Unproved and too strong in raw
   finite form:** repeated-root packets have zero spread but angular energy of order `n`, so any
   correct bound needs the unavoidable `O(n)` baseline and only forces subquadratic energy.
2. Correct spectral form: empirical spread `o(1)` forces angular derivative Rayleigh quotient
   `o(n²)`. **Plausible survivor.** A nonzero strong physical `L²` limit has nonzero derivative
   energy, hence angular energy of order `a²≈n²`; contradiction.
3. Root interval support can simplify proof. **Unavailable pre-RH:** current corpus gives finite
   real/simple roots but no unconditional common compact interval for shifted-Xi admissions.
4. Concentrated-core/outlier factorization. **Current attack:** Chebyshev inequality puts
   `n-o(n)` roots in a shrinking interval. Their product has only `O(n)` angular curvature at the
   endpoint opposite the cluster. Remaining `o(n)`-degree factor cannot localize on physical
   `O(1)` scale by Bernstein/Remez. Need coefficient-free weighted product estimate controlling
   interaction between both factors.
5. Universal one-line variance Bernstein inequality. **No longer required and not claimed.** Exact
   full-period integration by parts gives angular energy as radial transport plus positive
   Laguerre root-deletion density, but does not by itself upper-bound energy by root spread.
6. Arithmetic outlier budget. **Proved in Lean.** At every radius `eta`,
   `eta^2 k_eta <= G_n` and `2(2n+1) eta^2 k_eta <= R_n`. Hence `G_n/n -> 0`, with
   `eta_n=(G_n/n)^(1/4)`, gives both `eta_n -> 0` and `k_eta/n -> 0`.
7. Constrained-zero bandwidth scale. **Primary theorem identified.** Borwein--Erdelyi's sharp
   constrained `L^2` Bernstein theorem gives energy `O(n(k+1))` for a degree-`n` trigonometric
   polynomial with only a degree-`k` exceptional factor. This is exactly `o(n^2)` for the paid
   outlier population. Missing proof is now localized: show normalized mass of the shrinking
   central root arc is negligible and transfer the two exterior estimates through the original
   arcsine/Cayley measure. Remez must control interaction between concentrated core and exceptional
   factor; this transfer is not yet claimed.

## Required proof surface

- finite real-rooted polynomial factorization into concentrated core and sublinear outliers
  (outlier count and its arithmetic price are Lean-proved);
- quantitative endpoint lower-width law for core factor;
- Remez/Bernstein lower-width law for outlier factor inside core endpoint window;
- transfer from angular width to physical Cayley width `x=a tan(theta/2)`;
- contradiction with completed-source logarithmic tightness and norm-one strong compactness;
- specialization to actual canonical first-contact packets.

No abstract theorem taking compactness or root concentration as unexplained hypotheses will be
formalized as route closure. Lean work begins only after dependency-closed paper proof exists.
