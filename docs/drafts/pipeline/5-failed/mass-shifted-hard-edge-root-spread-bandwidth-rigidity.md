# Mass-shifted hard-edge root-spread bandwidth rigidity

- **ID:** `mass-shifted-hard-edge-root-spread-bandwidth-rigidity`
- **Stage:** 5-failed
- **Type:** FALSE CONJECTURE / EXACT NO-GO / POSITIVE SURVIVOR EXTRACTED
- **Depends on:** `mass-shifted-projective-gauss-root-renewal` and
  `mass-shifted-completed-source-hard-edge-compactness`

## Target

**FALSIFIED.**  This target uses affine roots as if they were hard coordinates.  If a reciprocal
hard root `u` stays bounded, its ordinary Gauss root and affine observation are

```text
x = 1 / (y + u),
r = 2*y*x - 1 = (y-u)/(y+u) -> 1.
```

Therefore every bounded, nontrivial hard-root configuration has collapsing affine root spread.
Completed-source Paley--Wiener compactness is compatible with that collapse.  Equations identifying
projective work with affine spread remain true, but affine spread cannot close route.

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
8. Integral bandwidth-to-tightness bridge. **Proved in Lean.** If original angular energy satisfies
   `E(Q)<=B^2 M(Q)`, then an arc of radius `delta` carries at most
   `2 delta (1/(2 pi)+2B) M(Q)`.  Exact Cayley substitution sends `[-R,R]` to the arc of radius
   `2 arctan(R/a)`. Consequently `B/a->0` makes every fixed physical-window mass vanish.
9. Physical derivative lower bound. **No longer needed.** Completed-source tightness already says
   some fixed physical window retains almost all normalized mass. The exact arc cap contradicts
   this directly once the original-measure constrained energy estimate is available.
10. Affine-interval transfer. **Failed as an automatic step.** Moving an interior core outside a
    rescaled unit disk changes the arcsine weight and creates an artificial endpoint. The required
    estimate must retain or quantitatively compare the original Cayley measure. This is the sole
    analytic gap; it cannot be hidden in a generic Remez citation.
11. **Hostile coordinate test — TARGET FALSIFIED.** For bounded hard levels `u,v`, exact identity
    ```text
    (y-u)/(y+u) - (y-v)/(y+v)
      = 2*y*(v-u)/((y+u)*(y+v))
    ```
    shows affine separation is `O(1/y)` even when reciprocal hard separation is nonzero. Hence
    empirical affine spread collapse is automatic for the compact hard configurations route needs.
12. **Positive survivor — Möbius source capacity.** Reciprocal clearing sends ordinary root `x`
    to `u=x⁻¹-y`. At that root, actual diagonal adaptive completed-source producer `T` obeys
    `T(u)=0` and `T'(u)=-2*x⁻¹*S'(u)^2`. The endogenous capacity
    `C=-(x/2)T'(u)=S'(u)^2` is nonnegative and retains hard geometry. With Gauss/Padé residue
    `rho=lambda/x` and terminal mass `Gamma=y*x^4*lambda*P'(x)^2`, exact replacement law is
    ```text
    rho * y*x^(2N+1) * C = Gamma.
    ```
    This survivor is formalized in
    `RHTower.XiShiftedHardEdgeAdaptiveSourceTransversality`.

## Required proof surface

- finite real-rooted polynomial factorization into concentrated core and sublinear outliers
  (outlier count and its arithmetic price are Lean-proved);
- quantitative endpoint lower-width law for core factor;
- local constrained-zero energy law in the original Cayley arcsine measure;
- endpoint-potential/Remez exclusion when the concentrated core lies at the invisible endpoint;
- contradiction with completed-source logarithmic tightness through the Lean-proved exact Cayley
  window identity and integral small-arc cap;
- specialization to actual canonical first-contact packets.

This proof surface is retired because its premise-to-contradiction implication is false.  Correct
open core is source control of reciprocal hard Padé atoms: show actual positive-axis residue mass
vanishes, or equivalently force terminal divided-root mass to vanish or effective adaptive source
capacity to diverge.  No affine-spread or constrained-root bandwidth theorem can substitute for
that source law.

## No-go closure and exact positive survivor

- Exact false step: treating `2*y*x-1` as a faithful carrier of `x⁻¹-y` at `y->infinity`.
- Exact loss locus: nonproper/infinite-scale coordinate compression, not finite branching or
  missing root-count estimates.
- Strongest positive theorem: adaptive completed-source transverse capacity and its exact
  multiplicative conservation with Padé residue and hard terminal mass.
- Paper proof: dependency-closed.
- Lean status: unconditional and compiled; see
  `XiShiftedHardEdgeAdaptiveSourceTransversality.lean`.
