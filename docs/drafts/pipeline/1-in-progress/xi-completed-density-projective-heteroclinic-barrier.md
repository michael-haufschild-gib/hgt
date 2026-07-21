# Xi completed-density projective heteroclinic barrier

- **ID:** `xi-completed-density-projective-heteroclinic-barrier`
- **Stage:** 1-in-progress
- **Type:** `[CONJECTURE] [SOURCE-DYNAMICAL OPEN CORE] [RH-SUFFICIENT] [NO RH CLAIM]`
- **Parent:**
  `../5-failed/xi-completed-density-antipodal-crossing-barrier.md`
- **Formalized local geometry:**
  `../3-formalized/new_scientific_knowledge/xi-completed-density-projective-collision-geometry.md`

## Corpus frontier

Put

```text
F(z)=integral_(0,infinity) rho(x) exp(i x z) dx,
q(z)=z^2+1/4,
E=qF-1/4,
E#=qF(-z)-1/4,
R=E#/E.
```

Corpus proves

```text
E+E#=4z^2 XiC,                                        (1)
R=-1 iff XiC=0                                        (2)
```

on every noncentral regular chart.  Global `|E|>|E#|` is false, so `R` is not an inner function
and classical Hermite--Biehler phase monotonicity is unavailable.

Define the actual projective Wronskian and its division-free flow by

```text
W_E=(E#)'E-E#E',
V_E=E^2 conjugate(W_E).                               (3)
```

Then

```text
R'=W_E/E^2,
dR(V_E)=|W_E|^2.                                      (4)
```

Thus every regular component of `R^(-1)((-infinity,0))` is an oriented projective trajectory and
`R` is a strict coordinate on it.  A regular trajectory hits `-1` at most once.

This removes recurrence as the frontier.  An off-axis Xi zero is exactly a trajectory that crosses
`R=-1` **without being anchored at the real boundary**.

## Conjecture: no unanchored source-to-reflection heteroclinic

Let

```text
S+ = {z : Re z > 0 and 0 < Im z < 1/2},
L- = {z in S+ : R(z) is real and R(z)<0},
```

with projective jets used where `E E#=0`.  Conjecture:

> Every maximal `V_E` trajectory in `L-` whose `R`-image contains `-1` has a unique finite endpoint
> on `Im z=0`.  That endpoint is a positive real Xi zero.  Equivalently, there is no maximal
> trajectory lying entirely in the open half-strip whose projective endpoint values bracket `-1`.

The conjecture permits all phenomena already forced by corpus:

- `|R|=1` at phases other than `pi`;
- zeros and poles of the projective chart;
- negative-ray trajectories whose image lies wholly in `(-infinity,-1)` or `(-1,0)`;
- different inward directions at consecutive real zeros;
- critical points away from trajectories whose image contains `-1`.

It excludes only an interior source-to-reflection connection crossing the antipode.

## Why this closes the gap

Assume conjecture.  If `z in S+` is a Xi zero and `E(z)!=0`, `(2)` gives `R(z)=-1`.  Its maximal
projective trajectory therefore has a real endpoint `t`.  Real-boundary sharp conjugation gives
`|R(t)|=1`; since endpoint lies on negative ray, `R(t)=-1`.  Formula `(4)` makes `R` strictly
increasing on regular portion, so same trajectory cannot take `-1` at both `t` and interior `z`.
Projective first-nonzero jets give same conclusion at singular collisions.  Hence no open-strip Xi
zero exists.  Centered evenness and Schwarz symmetry cover remaining quadrants.

This implication uses more than the target value `R!=-1`: it asserts a source-selected global
classification of projective trajectories and has many independent falsifiers.

## Source mechanism to prove

The conjecture is split into four independently auditable source statements.

1. **Negative-ray regularity.** `W_E!=0` whenever `R in (-infinity,0)` and `R` lies in regular chart.
2. **Top-edge exclusion.** No trajectory with image bracketing `-1` enters through `Im z=1/2`.
3. **Horizontal escape.** Weighted theta-Schwartz decay sends `R` to `1` uniformly on closed
   substrips, so a bracketing trajectory cannot escape horizontally.
4. **Projective endpoint separation.** No negative-ray trajectory joins a zero stratum of `E#`
   to a pole stratum of `E` with image bracketing `-1`; first nonzero jets orient all multiple
   endpoints.

Statements 1 and 4 must be proved from exact theta atoms or an equivalent source variation law.
They may not be replaced by `XiC!=0`, Hermite--Biehler gap, Herglotz/Pick positivity, or divisor
enumeration.

## Scientific-method predictions

1. `W_E` rather than `C_F` is nonzero on every regular bracketing trajectory.
2. Boundary entry at a simple real zero is transverse with velocity

   ```text
   4t^2 Re(XiC'(t))/Im(E(t)),
   ```

   whose sign is allowed to vary.
3. Every admissible bracketing trajectory has exactly one real anchor and one projective/topological
   exit; it never has two projective interior endpoints.
4. A positive or monotone fake density satisfying only `(1)` need not obey endpoint separation;
   any successful proof must use theta-specific atom relations beyond density positivity.
5. At a multiple collision, first nonzero projective jet supplies nonzero oriented speed after the
   correct time rescaling.

## First attack

1. Expand `W_E` as signed double theta-source integral on `R<0`, without absolute values.
2. Use `E#=rE`, `r<0`, to eliminate one reflected channel before symmetrizing source variables.
3. Seek factorization of resulting kernel into `(x-y)^2` times a theta-specific monotonicity or
   total-positivity residue.  Raw positivity without projective constraint is not relevant.
4. Separately prove closed-substrip horizontal escape from existing theta-Schwartz derivatives.
5. Classify zero/pole endpoint jets and compute orientation inherited from `(4)`.

## Kill criteria

Retire or refine immediately if any of following occurs:

- `W_E=0` at a regular point with `R<0` and bracketing image;
- a top-edge trajectory has image bracketing `-1`;
- a theta-source zero of `E#` connects to a zero of `E` along `R<0` without a real anchor;
- finite projective jets fail to orient a multiple endpoint;
- proposed proof assumes global gap, innerness, Pick/Herglotz positivity, Xi zero locations,
  computations, or independent absolute bounds on reflected channels;
- signed double integral reduces to conserved raw current already formalized.

## SOTA audit

Classical Fourier/Hermite--Biehler criteria control all real zeros through a global positivity
condition.  Modern meromorphic-inner-function theory obtains increasing boundary phase and
interlacing after inner/Herglotz structure is known.  Corpus refutes that structure for current
split.  No audited source gives a single-level trajectory-exhaustion theorem for this mixed
completed theta pair.  Novelty claim is limited to exact projective connection `(3)`--`(4)` and
source-to-reflection heteroclinic formulation, not to general level-set monotonicity.

Audited references:

- Csordas--Varga, [Fourier Transforms and the Hermite--Biehler Theorem](https://doi.org/10.1090/S0002-9939-1989-0982401-1);
- Dimitrov--Xu, [Wronskians of Fourier and Laplace Transforms](https://arxiv.org/abs/1606.05011);
- Hatinoğlu, [Uniqueness theorems for meromorphic inner functions and canonical systems](https://doi.org/10.4153/S0008439524000588).

## Status

Open.  Local collision geometry and flow law are proved in Lean; four global source statements
remain unproved.  No RH claim.

## Log

- 2026-07-21 — Created after hostile audit killed negative-ray recurrence and proved previous
  `C_F` certificate differentiates wrong quotient.
