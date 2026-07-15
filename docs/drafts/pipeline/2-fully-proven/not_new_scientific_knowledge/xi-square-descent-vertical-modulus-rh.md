# Xi square-descent vertical-modulus criterion for RH

- **ID:** xi-square-descent-vertical-modulus-rh
- **Stage:** 2-fully-proven
- **Type:** `[PROVED ON PAPER; BRIDGE] [FINITE-VALUE CONTRADICTION CRITERION]`
- **Source:** live `formal/` and pipeline corpus
- **Statement:** If `F` is the entire square descent determined by `F(z^2)=XiC(z)`, then RH is equivalent to vertical monotonicity of `|F|` in the upper half-plane; the exterior source chamber already suffices.

## Goal

Replace the pole-bearing logarithmic-derivative sign by a finite entire-value inequality.  This is
a contradiction route: an off-line Xi zero becomes a nonreal zero of `F`, and monotonicity forces a
backward vertical arc of zeros, contradicting the identity theorem.  The source problem becomes a
finite modulus comparison rather than a pointwise sign at a meromorphic pole.

## Gates

- [x] 0 → 1 in-progress: well-posed, source-pure, attack idea, passport below
- [x] 1 → 2 fully-proven: square-descent construction and localized exterior converse complete
- [ ] 2 → 3 formalized: Lean theorem, exact-leaf build, axiom audit
- [ ] 3 → 4 publication-ready: standalone theorem and source interpretation

## Definitions

Write the global Taylor expansion `XiC(z)=sum_n a_n z^n`.  Evenness gives `a_(2n+1)=0`, and the
series

```text
F(w)=sum_n a_(2n) w^n
```

has infinite radius of convergence: for every `r>0`, convergence of the XiC series at radius
`sqrt(r)` gives convergence of the displayed series at radius `r`.  Thus `F` is the unique entire
function such that

```text
F(z^2) = XiC(z).                                             (1)
```

Write `w=u+iv`.  The global vertical-modulus condition is

```text
0 <= v1 <= v2  ->  |F(u+i v1)| <= |F(u+i v2)|.              (VM)
```

Fix the corpus's fully discharged quartet radius

```text
R_* = 218/25.
```

Let `D_(R_*)` consist of upper-half-plane `w` whose principal square root `z=x+iy` satisfies
`x>R_*` and `0<y<1/2`.  The localized condition `(VM_(R_*))` asks for the same inequality whenever
the closed vertical segment between the two points lies in `D_(R_*)`.  More generally the proof
works at every `R` equipped with `XiOffLineQuartetAccretiveBand R`; it is not asserted for an
arbitrary uncertified radius.

## Proof architecture

### RH implies `(VM)`

Under RH, every zero of `XiC` is real.  The unconditional multiplicity-exact Hadamard
factorization and reflection pairing give

```text
F(w) = XiC(0) product_a (1-w/a^2),                           (2)
```

with positive real `a^2`, repeated with the Xi multiplicities.  For every factor,

```text
|1-(u+iv)/a^2|^2 = (1-u/a^2)^2 + v^2/a^4,                  (3)
```

which is nondecreasing for `v>=0`.  The inequality holds for every reflection-closed finite
partial product and passes to the locally uniform canonical-product limit.  Hence `(VM)`.

### `(VM_(R_*))` implies RH by contradiction

Assume RH is false.  The formal theorem
`xiOffLineQuartetAccretiveBand_twoHundredEighteen_twentyFifths` and the exact quartet selector
produce an upper-right XiC zero `z0=x0+i y0` with `x0>R_*` and `0<y0<1/2`.  Then

```text
w0=z0^2=(x0^2-y0^2)+i(2 x0 y0)
```

is a nonreal zero of `F` in `D_(R_*)`.  The squaring map is locally biholomorphic at `z0!=0`, and
the inequalities defining the principal-root chamber are strict, so `D_(R_*)` is open at `w0`.
It supplies `epsilon>0` such that
`w0-i t` remains in `D_(R_*)` for `0<t<epsilon`.  Applying `(VM_(R_*))` to `w0-i t` and `w0` gives

```text
0 <= |F(w0-i t)| <= |F(w0)| = 0.
```

Thus an entire vertical arc accumulates at `w0` inside the zero set of `F`.  The identity theorem
forces `F=0`, contradicting `F(0)=XiC(0)!=0`.  Therefore RH holds.

### Differential/source identity

Away from zeros, differentiation of `(1)` gives

```text
XiC'(z)/XiC(z) = 2z F'(z^2)/F(z^2),
normalizedPrimeArchMomentGerm(z) = -2 F'(z^2)/F(z^2).       (4)
```

Consequently

```text
d/dv log|F(u+iv)| = -Im(F'(u+iv)/F(u+iv))
                   = (1/2) Im(normalizedPrimeArchMomentGerm(sqrt(u+iv))).  (5)
```

The vertical finite-difference criterion is therefore the integrated form of the corpus's
positive exterior paired-diagonal / anti-Herglotz criterion.  Its value is that `(VM_R)` is entire,
has no pole exclusions, and admits attacks by finite products, norm comparisons, OPUC, or total
positivity without first controlling a logarithmic derivative.

## Source-producer opportunities

1. **OPUC/Schur:** realize the Cayley transform of `-2 F'/F` as the limit of source-defined Schur
   functions.  Genuine contractivity would imply `(VM_R)`; ordinary Toeplitz positivity alone does
   not identify the required analytic function.
2. **Theta two-copy kernel:** expand
   `|F(u+iv2)|^2-|F(u+iv1)|^2` through the theta Fourier representation and seek a source-pure
   square after the functional-equation pairing.  The raw cosine cross-kernel is signed, so a
   successful proof must use theta-specific structure rather than positivity of the Fourier
   density alone.
3. **Prime--Gamma finite ratio:** integrate the completed prime--Gamma flux along a vertical
   `w`-segment and try to identify the exponential modulus ratio as a determinant or partition
   function with manifestly nonnegative loss.

## Endpoint-only no-go and positive successor

The weaker comparison `|F(u+iv)| >= |F(u)|` is not an exact contradiction criterion: a nonreal
zero can share its real coordinate `u` with a real zero.  Its positive content is nevertheless
precise: every nonreal zero would force a real zero at the same vertical base, with a local
vanishing-order constraint.  Requiring monotonicity between every two heights is the minimal
positive repair; it turns one zero into a forbidden arc of zeros.

## Open core

Prove `(VM_(R_*))` directly from one of the source representations without importing an assumption
already equivalent to RH.  Formula `(5)` identifies exactly what must be gained over the existing
boundary Loewner and finite OPUC results: a source-defined analytic Pick/anti-Herglotz continuation,
not merely positivity of real boundary matrices.

## Literature boundary

Horizontal modulus monotonicity of the completed zeta function and its RH equivalences are
classical; see Sondow--Dumitrescu, <https://arxiv.org/abs/1005.1104>, and
Matiyasevich--Saidak--Zvengrowski, <https://arxiv.org/abs/1205.2773>.  Singh studies monotonicity
along the quadratic family `t^2-delta*(sigma-sigma_0)^2=lambda` for `|delta|<1`; see
<https://doi.org/10.1007/s13226-023-00476-1>.  Fixed `Re(w)` in the square descent is the Lorentz
boundary `delta=1`, while vertical motion in `w` supplies the transverse parameter.  The present
criterion is therefore classified conservatively as a finite-value face of the already proved
anti-Herglotz gate, not as new RH progress.

## Log

- 2026-07-15 — `[CONJECTURE]` endpoint-only comparison proposed, then rejected as insufficient.
- 2026-07-15 — `[CONJECTURE]` repaired to full vertical monotonicity; contradiction chain and
  Hadamard-product reverse direction isolated; source producer remains open.
- 2026-07-15 — corrected the localized converse to require the exact quartet radius
  `R_*=218/25` (or a general `XiOffLineQuartetAccretiveBand R`) and calibrated the Lorentz-boundary
  formulation against horizontal and quadratic-curve modulus monotonicity literature.
- 2026-07-15 — completed the power-series square descent and local principal-root chamber proof;
  promoted the finite-value equivalence to the fully-proven bridge lane.  The source inequality
  remains the RH-bearing open problem and is not claimed proved.
