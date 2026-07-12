# Xi Taylor orientation-sensitive finite-coefficient sublinear flux

- **ID:** `xi-taylor-oriented-finite-coefficient-sublinear-flux`
- **Stage:** 1-in-progress
- **Type:** THEOREM TARGET / RH SOURCE PRODUCER
- **Scientific status:** `[OPEN CORE] [NOVELTY UNVERIFIED]`
- **Parent card:**
  `../3-formalized/not_new_scientific_knowledge/xi-taylor-anisotropic-rational-mesh-sublinear-flux.md`
- **Statement:** Prove, directly from the canonical finite Taylor coefficients of `XiC`, an
  orientation-sensitive estimate forcing sublinear upper logarithmic-derivative flux on the
  anisotropic Gaussian-rational meshes, without using Xi zero locations, real-rootedness,
  anti-Herglotz positivity, or an RH-equivalent limiting measure.

## Exact target

Let

```text
P_k(z) = xiCTaylorApprox(k,z),
z(s)   = (s-1/2)(-i),
```

and let `N` be a source-selected super-accurate schedule. For every integer `R >= 4`, define

```text
G_(n,R) = {a/n + i b/n^2 : a,b in Z}
          intersect {1/R <= Re(s) <= 1/2-1/R, |Im(s)| <= R}.
```

The required conclusion is

```text
max { Im(P_(N(n))'(z(s))/P_(N(n))(z(s))) :
      s in G_(n,R), P_(N(n))(z(s)) != 0 } = o(n).             (1)
```

An acceptable coefficient theorem must state a finite predicate or inequality on the actual
coefficients of `P_(N(n))`, prove that the canonical Xi coefficients satisfy it from their
prime--Gamma or theta-moment source, and derive `(1)` by a finite argument.

## Non-circularity firewall

The producer may not assume or invoke:

1. locations of Xi zeros or zero-freeness in the open left critical strip;
2. real-rootedness, Hermite--Biehler status, or Jensen-polynomial hyperbolicity strong enough to
   imply the limiting zero localization;
3. anti-Herglotz/Pick positivity of `XiC'/XiC`;
4. positivity of a limiting measure equivalent to RH;
5. a finite selector defined using the target flux inequality or an RH-equivalent predicate.

## Existing proved infrastructure

`[PROVED]` The paper criterion shows that `(1)` for a super-accurate schedule implies RH and that RH
implies `(1)`.

`[FORMALIZATION]` The Lean tree already contains:

- the super-accurate source schedule and its moving anisotropic lookup;
- the `1/n` by `1/n^2` rational mesh and positive reciprocal orientation;
- local Xi value lower bounds and derivative upper bounds on each mesh fibre;
- linear logarithmic-derivative growth at any hypothetical Xi zero;
- the terminal implication from sublinear anisotropic Xi flux to RH.

`[FORMALIZATION]` The finite-Taylor quotient transfer near a hypothetical zero and the terminal
finite-Taylor sublinear-flux implication to RH are now complete.  The remaining research theorem
is the unconditional coefficient producer `(1)`.

## Medalist lens

The smallest finite object is the oriented Hermitian numerator

```text
J_P(z) = Im(P'(z) * conjugate(P(z))),                         (2)
```

because

```text
Im(P'(z)/P(z)) = J_P(z)/|P(z)|^2                             (3)
```

when `P(z) != 0`. Coefficient sign information controls individual axes; `(2)` is a combination
mode coupling every coefficient pair and retaining orientation. The target is therefore a
finite lower-denominator/upper-current inequality, not coefficient positivity by itself.

## Candidate moves

1. `[CONJECTURE] Oriented Bezoutian minor.` Rewrite
   `J_P(z)-eta |P(z)|^2` as one explicit Hermitian coefficient form and seek a theta-source
   factorization whose negative part is `o(n)|P(z)|^2` uniformly on the finite mesh.
2. `[CONJECTURE] Truncated cosine two-point current.` Insert the theta-moment representation of the
   coefficients into `(2)`, obtaining a finite double integral. Isolate the antisymmetric kernel
   before integration and test whether completed prime--archimedean orientation supplies its sign
   or only its axis marginals.
3. `[CONJECTURE] Constraint residual rather than positivity.` Use the exact coefficient recurrences
   to show that any mesh point with current at least `epsilon*n` creates a finite residual violating
   one completed theta constraint. This must be a direct finite contradiction, not a compactness
   limit that reconstructs an RH-equivalent measure.
4. `[CONJECTURE] Denominator exclusion by source-conditioned resultants.` Construct a finite
   coefficient resultant separating the Taylor polynomial and its oriented derivative on the mesh,
   with a source lower bound stronger than the super-accurate error near a hypothetical Xi zero.

## Initial attacks and retired shortcuts

- `[PROVED ROUTE FAILURE]` Positive Taylor coefficients or positive theta moments alone cannot
  control `(2)`: axis positivity does not imply the first nontrivial Hankel/Schur combination sign.
- `[PROVED ROUTE FAILURE]` Fixed Taylor moduli, Newton geometry, HT status, and any bounded finite
  local passport do not select real-rootedness or global divisor orientation.
- `[PROVED ROUTE FAILURE]` An unrestricted nonlinear finite selector is an oracle unless its source
  formula and transfer theorem are supplied independently of the target.
- `[PROVED BRIDGE]` The oriented current `(2)` has an exact finite polynomial normal form and the
  strict inequality `J_P(z) < epsilon*n*|P(z)|^2` automatically excludes `P(z)=0` and implies the
  desired flux bound.  This is denominator clearing, not a source proof; treating it as the
  coefficient producer would merely rename the target.
- `[PROVED ROUTE FAILURE]` The theta two-point current kernel is not pointwise oriented.  For the
  full cosine kernel, one source coordinate at `u=0` and another at `v>0` contributes a cross term
  proportional to `-v cos(xv)sinh(yv)`; choosing `xv=pi` makes it positive for `y>0`.  Hence
  positivity of the theta weights cannot prove the current sign atom by atom.
- `[PROVED ROUTE FAILURE]` Positive even Schwartz source structure and all raw-moment Hankel
  inequalities are insufficient.  The density
  `g_epsilon(x)+a g_epsilon(x-1)+a g_epsilon(x+1)`, `0<a<1/2`, is strictly positive, even, and
  Schwartz and has a uniform strict log-concavity floor for `epsilon>1`, while its Fourier transform
  `exp(-epsilon z^2/2)(1+2a cos z)` has the explicit simple nonreal zeros
  `pi +/- i arcosh(1/(2a))`.  Any live inequality must distinguish the exact theta source from
  this family.
- `[PROVED ROUTE FAILURE]` A source-conditioned resultant or arithmetic lower bound at the
  Gaussian-rational nodes cannot exclude the pole amplifier: every complex target has the
  explicit `1/n` by `1/n^2` right approximants, and a hypothetical Xi zero makes the polynomial
  values naturally of order `n^{-m}`, not arithmetically exceptional.
- `[PROVED ROUTE FAILURE]` The finite Cauchy-jet, Toeplitz, and inverse-Cholesky frames in
  `HTGeometry/CauchyJetFrame.lean`, `CayleyMomentFrame.lean`, and
  `CofinalCholeskyFiniteFrame.lean` change coordinates but supply no orientation.  Congruence
  preserves the inertia of the indefinite coefficient-current form, every finite frame prefix
  retains a nontrivial carrier fibre, and only the complete compatible tower selects the measure.
  Using that complete tower here would reintroduce the forbidden limiting-measure route.
- `[OPEN CORE]` Determine whether the actual completed theta coefficient constraints factor the
  oriented two-point current `(2)` with a sign-definite leading term and a quantitatively sublinear
  residual. If they do not, isolate the first explicit indefinite source kernel and retire that
  candidate rather than weakening the theorem.

## Gates

- [x] prior pipeline, failed routes, and formal theorem surface audited
- [x] exact RH-equivalent endpoint separated from the requested source producer
- [ ] several genuinely different coefficient mechanisms constructed and attacked
- [ ] finite source predicate stated without target-oracle content
- [ ] canonical Xi coefficients proved to satisfy the predicate
- [ ] predicate proved to imply `(1)` on every compact anisotropic mesh
- [ ] complete paper proof independently checked
- [ ] exact theorem formalized in Lean with no forbidden declarations
- [ ] parent-theory, literature, novelty, and significance gates passed
