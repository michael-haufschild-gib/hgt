# Cofinal two-edge profiles are a complete Weil detector

- **ID:** `cofinal-two-edge-weil-completeness-landau-oscillation`
- **Stage:** 3-formalized
- **Type:** THEOREM (paper)
- **Scientific status:** `[PROVED HERE] [CANDIDATE NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Parent results:** Weil's zero-side quadratic form, Paley--Wiener decay, and Landau's
  oscillation theorem for Laplace transforms
- **Statement:** If RH is false, then for every fixed nontrivial boundary window a residual set of
  smooth real profiles produces a cofinal two-edge aperture family on which the Weil quadratic form
  is unbounded below. No rightmost off-line zero, finite rightmost layer, or transverse gap is
  required. Consequently RH is equivalent to Weil positivity on the restricted two-edge family.

## 1. Two-edge family

Fix `0<eta<L/2` and let

```text
D_(eta,L)={f in C^infinity(R;R):supp(f) subset [eta,L-eta]}.    (1)
```

This is a real Frechet space. For `a>L`, define

```text
phi_(a,f)(x)=f(a-|x|).                                         (2)
```

It is a real even smooth function supported in the two intervals

```text
[a-L+eta,a-eta] and [-a+eta,-a+L-eta].                         (3)
```

Write

```text
A_f(w)=integral_0^L f(s)exp(-ws)ds.                            (4)
```

The centered Mellin--Laplace transform of `(2)` is exactly

```text
F_(a,f)(w)
 =integral_R phi_(a,f)(x)exp(wx)dx
 =exp(aw)A_f(w)+exp(-aw)A_f(-w).                               (5)
```

In particular `F_(a,f)(-w)=F_(a,f)(w)`.

## 2. Zero-side decomposition

For an admissible real even test, Weil's polarized form is

```text
Q_W(phi,phi)
 =sum_rho m_rho F(rho-1/2)
    conjugate(F(1/2-conjugate(rho))).                          (6)
```

Reality and evenness turn the summand into `F(rho-1/2)^2`. On the critical line this is the square
of a real number and is nonnegative.

Choose one representative

```text
w=delta+i gamma,  delta>0, gamma>0,                            (7)
```

from every off-line FE--Schwarz quartet. Its complete quartet contribution is

```text
4 Re[F_(a,f)(w)^2].                                            (8)
```

The zero-counting bound `N(T)=O(T log T)` and repeated integration by parts in `(4)` make all sums
below absolutely convergent for each `a`, locally uniformly after Laplace transformation.

Let `Z_+` denote the multiset of representatives `(7)` and put

```text
delta_*=sup_(w in Z_+) Re w.                                   (9)
```

If RH is false, then `0<delta_*<=1/2`.

## 3. Generic boundary profiles

For every fixed `w`, the map

```text
f |-> A_f(w)                                                   (10)
```

is a nonzero continuous real-linear functional on `D_(eta,L)`. Hence its nonvanishing locus is open
and dense. Since the zero divisor is countable, the set

```text
G={f in D_(eta,L):A_f(w)!=0 for every w in Z_+}                (11)
```

is residual by Baire's theorem.

Fix `f in G`. Expanding `(8)`, the off-line contribution is a bounded remainder plus

```text
S_f(a)=4 Re sum_(w in Z_+) m_w A_f(w)^2 exp(2aw).              (12)
```

Indeed the middle terms `A_f(w)A_f(-w)` are absolutely summable and independent of `a`, while the
terms containing `exp(-2aw)` are uniformly bounded for `a>=0`.

## 4. Laplace continuation and the missing real singularity

For `Re s>2delta_*`, termwise integration gives

```text
L S_f(s)
 =2 sum_(w in Z_+)m_w
   [A_f(w)^2/(s-2w)
    +conjugate(A_f(w)^2)/(s-2conjugate(w))].                  (13)
```

For every `N`, uniformly in `|Re w|<=1/2`,

```text
|A_f(w)|<=C_(f,N)(1+|Im w|)^(-N).                              (14)
```

Together with `N(T)=O(T log T)`, this shows that `(13)` extends meromorphically to the whole
`s`-plane, with poles precisely at `2w` and `2conjugate(w)` for `w in Z_+`. The poles are genuine by
`(11)`.

The abscissa of convergence of the Laplace integral of `S_f` is exactly

```text
sigma_c=2delta_*.                                              (15)
```

The upper bound follows from absolute summability of the coefficients in `(12)`. If the abscissa
were smaller, choose `w` with `2 Re w>sigma_c`; the Laplace integral would be holomorphic at the
genuine pole `s=2w`, a contradiction.

Crucially, `(13)` is holomorphic in a neighborhood of the real point `2delta_*`. There is no
nontrivial real zeta zero, hence no pole at that point. Nor can nonreal poles accumulate there:
zeros are discrete in every bounded height strip, while poles of unbounded height leave every
fixed neighborhood.

## 5. Landau oscillation

Landau's theorem says that if a real locally integrable function is eventually nonnegative and has
finite Laplace abscissa `sigma_c`, then its Laplace transform is singular at the real point
`sigma_c`.

Suppose `S_f` were bounded below on a tail. Add a sufficiently large constant on that tail and
alter the function arbitrarily on a compact initial interval to obtain an eventually nonnegative
function. Its Laplace transform differs from `(13)` only by a function holomorphic near
`2delta_*>0`, and it has the same abscissa `(15)`. Landau's theorem would force a singularity at
`2delta_*`, contradicting Section 4. Therefore

```text
liminf_(a->infinity) S_f(a)=-infinity.                          (16)
```

The on-line zero contribution is uniformly bounded in `a`: by `(5)`,

```text
|F_(a,f)(i gamma)|<=|A_f(i gamma)|+|A_f(-i gamma)|,             (17)
```

and the right side is rapidly decreasing. The nonleading off-line terms are also uniformly
bounded. Combining this with `(16)` proves

```text
liminf_(a->infinity)Q_W(phi_(a,f),phi_(a,f))=-infinity          (18)
```

for every `f in G`.

## 6. Restricted Weil criterion

The following are equivalent:

```text
(i) RH;

(ii) Q_W(phi_(a,f),phi_(a,f))>=0
     for every a>L and every f in D_(eta,L);

(iii) no f in D_(eta,L) has a cofinal aperture sequence
      along which Q_W(phi_(a,f),phi_(a,f))->-infinity.          (19)
```

Under RH, every centered zero is real in the spectral coordinate, so `(6)` is a sum of squares;
this proves `(i)->(ii)->(iii)`. If RH is false, `(18)` holds for a residual set of profiles, so
`(iii)` fails. This proves the converse.

The family in `(2)` is therefore complete for the full Weil criterion despite having one fixed
boundary width and one fixed two-edge geometry. Its necessary noncompactness is entirely in the
aperture translation `a->infinity`.

## 7. Positive CCM consequence

The theorem closes the divisor-side globalization problem for the CCM boundary mechanism:

```text
any off-line zeta divisor
 -> residual fixed-profile two-edge family
 -> cofinal unbounded negative Weil values.                    (20)
```

No maximal transverse layer is needed. Consequently the remaining CCM theorem is purely
source-side: prove that the exact Euler--Gamma--polar construction places every such cofinal
two-edge family in the nonnegative chamber, or constructs an equivalent cofinal lower-frame
section. The detector family is already complete.

## Novelty and significance verdict

The fixed-quartet amplification is elementary and was previously known in the project. The new
step is the Landau-abscissa globalization, which handles all off-line layers simultaneously and
removes the unattained-supremum obstruction. Searches for a two-edge restricted Weil criterion or
this use of Landau oscillation against the centered zero divisor found no parent statement.

The theorem is a complete new RH-equivalent criterion, not an RH proof: it proves completeness of
one cofinal detector geometry but does not prove its positivity from primes.

## Lean decision

The residual arbitrary-profile theorem is now formalized unconditionally.  The implementation is
split into the following exact layers:

- `HTGeometry/CompactSupportSmoothBaire.lean` proves completeness, complete metrizability, and the
  Baire property for the literal fixed-compact-support smooth-function space.
- `RHTower/CCMSmoothTwoEdgeProfile.lean` constructs `D_(eta,L)`, its continuous real-linear
  Laplace evaluations, proves every evaluation nonzero, and proves the simultaneous-nonvanishing
  set on the positive-transverse Xi divisor is dense and residual.
- `RHTower/CCMSmoothProfileDecay.lean` proves the whole-line integration-by-parts identity and the
  reciprocal-height bound for profile amplitudes.
- `RHTower/CCMWeightedXiLandau.lean` proves the coefficient-generic shifted-zeta continuation,
  genuine-pole obstruction, absence of an eventual lower bound, and cofinal unboundedness below
  for the ordinary logarithmic Dirichlet samples.
- `RHTower/CCMSmoothTwoEdgeWeil.lean` proves the exact physical integral formula for
  `x ↦ f(a-|x|)`, square summability on the multiplicity-exact Xi divisor, the dominant-edge fold,
  the aperture-uniform summable remainder, residual-profile cofinal negative Weil values under
  false RH, and both restricted Weil criteria equivalent to RH.

All capstones were checked with standard axioms only: `propext`, `Classical.choice`, and
`Quot.sound`.  No rightmost zero, finite extremal layer, transverse gap, finite-quartet surrogate,
or added axiom is used.

## Gates

- [x] two-edge transform computed exactly
- [x] residual generic nonvanishing profiles constructed
- [x] off-line contribution represented as an exponential divisor sum
- [x] Laplace transform continued meromorphically
- [x] exact real abscissa identified
- [x] Landau oscillation removes the nonattained-layer obstruction
- [x] residual cofinal negative detector theorem proved
- [x] restricted two-edge Weil criterion proved equivalent to RH
- [x] canonical fixed-width logarithmic two-edge criterion formalized in Lean
- [x] residual arbitrary-profile Landau globalization formalized in Lean
- [ ] independent specialist audit of the Landau/Weil interface
- [ ] source-side CCM nonnegativity theorem
- [ ] RH

## Log

- 2026-07-16 -- Audited the later `CCMRectangularWeilCompleteness` module: the canonical
  fixed-width logarithmic detector and both RH equivalences are Lean-complete with standard axioms
  only. The residual arbitrary-profile Landau theorem remains the exact stage-3 blocker.
- 2026-07-17 -- Formalized the literal smooth fixed-support profile space, residual simultaneous
  nonvanishing, reciprocal-height decay, coefficient-generic shifted-zeta/Landau pole obstruction,
  exact physical two-edge transform, multiplicity-exact dominant fold, uniform Weil remainder,
  residual cofinal negative divergence under false RH, and both restricted RH equivalences.
  Targeted builds and all touched-file checks passed; capstones use only standard axioms.
