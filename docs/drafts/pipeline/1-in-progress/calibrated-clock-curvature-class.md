# Calibrated clock curvature as the thin boundary field

- **ID:** `calibrated-clock-curvature-class`
- **Stage:** 1-in-progress
- **Type:** GENERAL HT CONJECTURE / CURVED OBSERVABLE-RESOLUTION FIELD
- **Scientific status:** `[CONJECTURE] [BIANCHI LAW LEAN-FORMALIZED] [GAMMA RANK-ONE LAW PROVED ON PAPER] [NOVELTY UNVERIFIED]`
- **Parents:**
  - `../3-formalized/clock-shadow-curvature-bianchi.md`
  - `clock-descent-anomaly.md`
  - `hypertranscendental-constraint-corona-motive.md`
- **Statement:** A nonlocal constrained HT source is represented at finite clock resolutions by a
  curved system, not a pro-operator. The calibrated curvature of its finite shadows is the thin
  boundary datum from which the global source constraint, topology, and self-dual degeneracy
  theory should be reconstructed.

## Curved clock system

Let `O_N` be the `N`-clock observation space, `p_N:O_(N+1)->O_N` truncation, and `T_N` the formal
shadow of one fixed source operation. Define

```text
kappa_N=p_N T_(N+1)-T_N p_N.                              (1)
```

If the `T_N` were a genuine pro-operator, every `kappa_N` would vanish. Nonzero `kappa_N` measures
the folding of omitted global information back into earlier observables.

For three resolutions, the proved cocycle identity is

```text
kappa_(N,L)=p_(N,M) kappa_(M,L)+kappa_(N,M) p_(M,L).      (2)
```

Thus `(kappa_N)` is a curvature cocycle on the observation tower.

## Calibrated gauge class `[CONJECTURE]`

Changing shadows by `T_N' = T_N+g_N` changes curvature by

```text
kappa_N'=kappa_N+(p_N g_(N+1)-g_N p_N).                   (3)
```

Without restrictions, the choice `T_N=0` trivializes everything. Therefore ordinary operator
cohomology is the wrong invariant.

The source supplies a finite clock symbol, affine calibration, and formal principal part. Allow
only gauge corrections `g_N` which preserve those data. Define the **calibrated clock-curvature
class**

```text
[kappa]_cal = curvature modulo symbol-zero calibrated coboundaries.  (4)
```

**[CONJECTURE]** `(4)` is invariant under source-presentation equivalence and faithful changes of
clock charts. It is the concrete realization of the universal constraint-corona object.

## Descent Bianchi law

For source observations `q_N` and source-to-shadow anomalies

```text
alpha_N=T_N q_N-q_N S,                                   (5)
```

the Lean-formalized identity is

```text
p_N alpha_(N+1)-alpha_N=kappa_N q_(N+1).                 (6)
```

When higher source observations are surjective, the range of the left side is exactly
`range(kappa_N)`. Thus curvature is not a formal bookkeeping defect: every one of its values is
seen on an actual source variation.

## Gamma rank-one curvature `[PROVED ON PAPER]`

Let `O_N=K^N` record derivatives `a_0,...,a_(N-1)` and let the truncated unit translation shadow be

```text
(E_N a)_i=sum_(j=i)^(N-1) a_j/(j-i)!.                    (7)
```

Let `p_N` forget `a_N`. Direct cancellation gives

```text
(p_N E_(N+1)-E_N p_N)(a)_i=a_N/(N-i)!,  0<=i<N.         (8)
```

Therefore `kappa_N` has rank one. It is the outer product

```text
kappa_N = (1/N!,1/(N-1)!,...,1) tensor eval_N.           (9)
```

The accumulated transpose boundary vectors in `(9)` are exactly the factorial coefficients of
the infinite Taylor conormal

```text
nu(h)=sum_(n>=1) h^(n)(0)/n!=h(1)-h(0).                  (10)
```

This identifies, in one model, four objects previously seen separately:

```text
failure of finite shadow compatibility
  = rank-one clock curvature
  = finite tails of the infinite conormal
  = the data needed to reconstruct global translation.   (11)
```

## Thin-curvature conjecture

**[CONJECTURE]** A regular corona-pure constrained HT source has a nonzero calibrated curvature
class whose rank or operator-ideal profile is asymptotically thin relative to `dim(O_N)`. The
profile is source-invariant and measures boundary thickness:

- uniformly finite rank: finite-codimensional conormal boundary;
- nuclear or compact curvature: analytic/Calkin boundary;
- nonclosable curvature: singular source-topology boundary;
- torsion or profinite-invisible curvature: monodromy boundary.

The list is conjectural. A common abstract ideal name does not prove the realizations equivalent.

## Five obstruction realizations `[CONJECTURE]`

For a self-dual calibrated class `[kappa]_cal`:

1. spectral incompleteness is homology of its curvature complex;
2. continuation failure is failure to sum/integrate the curvature to a global source operator;
3. positivity failure is failure to orient its reflected Hermitian curvature pairing;
4. monodromy is holonomy of the calibrated curvature cocycle;
5. boundary-condition ambiguity is the torsor of calibrated primitives `T_N` with fixed
   curvature.

This is the first formulation in which all five rows are literal operations on one class rather
than analogies among separate operators.

## Self-dual degeneracy spectrum `[CONJECTURE]`

Suppose reflection sends the curvature system to its dual up to calibrated gauge. The common
degeneracy spectrum is the support where the self-dual curvature complex loses transversality.
Fixed points of the anti-linear reflection give its self-dual part; nonfixed degeneracies occur in
pairs.

For a completed-zeta source, critical zeros would be fixed-locus degeneracies of a source-derived
`[kappa_zeta]_cal`. Constructing the class from prime and archimedean constraints is mandatory;
defining it from `xi` or its zeros is circular. This is not an RH result.

## Attack

- Curvature of an arbitrary family of truncations is easy to manufacture. Calibration and
  presentation invariance must be defined before `(4)` has content.
- Uniform finite rank is false for general nonlocal operations. The correct thinness notion may
  be an operator ideal, a bornological class, or a categorical compactness condition.
- Gamma proves rank-one curvature for translation shadows, but not universality for all its source
  constraints.
- Holonomy and boundary primitives follow standard cohomology once a curvature class exists;
  spectral and positivity factorizations remain the difficult claims.
- Self-duality explains reflection symmetry only. It does not force fixed-locus confinement.

## Gates

- [x] clock-shadow curvature defined
- [x] Bianchi and cocycle identities Lean-formalized
- [x] exact curvature-range law Lean-formalized
- [x] Gamma rank-one formula proved on paper
- [ ] Gamma rank-one formula formalized in Lean
- [ ] calibrated gauge group defined
- [ ] nontriviality of `[kappa_Gamma]_cal` proved
- [ ] thinness notion selected by a parent-theory collision audit
- [ ] source-presentation invariance proved
- [ ] self-dual curvature complex constructed
- [ ] two obstruction realizations proved to preserve one class
- [ ] independent novelty/significance audit
