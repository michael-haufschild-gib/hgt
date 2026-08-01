# Route J principal-relative Julia current

- **ID:** `route-j-principal-relative-julia-current`
- **Stage:** 1-in-progress
- **Type:** `[CONJECTURE]` / SOURCE CONSTRUCTION / NO-GO CLASSIFICATION
- **Scientific status:** `[OPEN] [ROUTE J OWNER] [NO RH INPUT] [NO COMPUTATION]`
- **Parent no-go:** `../5-failed/route-j-julia-unrenormalized-coherent-energy-budget.md`
- **Endpoint:** Route A's literal first-clock source is eventually bounded below

## Mission

Determine whether Julia coherence can still orient the literal completed first clock after the
unrenormalized bad-energy budget is removed.  The only surviving category inserts a
principal-relative counterterm before good/bad positive projection and before scalarization.  It
must be source-defined and must produce a uniform lower floor, not rename that floor as a current.

This card owns that survivor.  No other frontier route currently constructs a Julia-specific
pre-projection relative current.

## 1. Exact endpoint

Write the attenuated completed source at aperture `L` and Julia scale `x` as

```text
C_x(L)=A(L)+G_x(L)-B_x(L),                               (1)
```

where `A` is the continuous archimedean half-wave budget and `G_x,B_x` are the origin
correlations of the nonnegative reduced good and bad prime channels.  The zero-scale finite-window
limit is the literal published first-clock value.

A successful relative current must construct a source-uniform constant `M` and a source-defined
quantity `R_x(L)` such that, along a source-faithful choice of scales,

```text
C_x(L)<0  ->  C_x(L)^2 <= R_x(L),
R_x(L) <= M.                                             (2)
```

Then `C_x(L)>=-sqrt(M)`, and source-faithful de-attenuation gives the eventual lower floor already
proved equivalent to RH.  Both arrows in `(2)` are required.  Defining `R_x(L)` from the negative
part of `C_x(L)` is representation theatre.

## 2. Closed unrenormalized predecessor

The literal bad Julia energy is

```text
E_B(x,L)=sum_(p,q) B_p(L) K_x(log q-log p) B_q(L).       (3)
```

At `L_m=6 log m`, every prime in `(2m^4,5m^4]` is a one-mode pure-bad channel and contributes
at least `(log p)^2/(4p)` on the diagonal.  The Julia kernel is pointwise positive with unit
diagonal, so

```text
E_B(x,L_m) >= log(m)/20                                 (4)
```

for every real `x`.  Thus `(3)` has no source-uniform upper budget.  At zero scale it instead
converges to the square of total bad mass.  Post hoc subtraction of the diagonal destroys the
normalized anchor-capacity inequality on one unit node.

These results retire only the unrenormalized subroute.

## 3. Two-channel linear-current classification `[PROVED HERE]`

Before scalarization, every channel-linear quadratic current on aggregate good/bad masses has the
form

```text
Q_(a,b,c)(g,h)=a g^2+2bgh+c h^2.                        (5)
```

Call it universally nonnegative when `Q(g,h)>=0` for all real `g,h`.

### Theorem A — null pure-bad diagonal kills the mixed coefficient

If `Q` is universally nonnegative and `c=0`, then `b=0`.  Hence

```text
Q_(a,b,0)(g,h)=a g^2.                                   (6)
```

Proof: `Q(1,0)>=0` gives `a>=0`.  Evaluate at
`(g,h)=(b,-(a+1))`.  With `c=0`, nonnegativity gives

```text
0 <= -(a+2)b^2.
```

Since `a+2>0`, this forces `b=0`.  Therefore a positive two-channel current cannot cancel the
bad self-current while retaining good/bad interference.  If both diagonal coefficients vanish,
the entire positive current vanishes.

### Theorem B — negative-excursion dominance retains full bad diagonal

Assume

```text
g-h<0 -> (g-h)^2 <= Q_(a,b,c)(g,h)                      (7)
```

for all real `g,h`.  Taking `(g,h)=(0,1)` gives `1<=c`.  Therefore no current satisfying `(7)`
can cancel pure-bad diagonal (`c=0`).  This conclusion does not assume positivity and is
independent of whether the counterterm was described as occurring before or after projection.

### Arithmetic strengthening

The sixth-power prime block contains an unbounded family of literal source cells with

```text
good_p(L_m)=0,
bad_p(L_m)>0.                                            (8)
```

The first identity follows from prime-power length one: neither the stable length-at-least-three
term nor the exceptional length-two small-square term is present.  The second follows from the
strict negative sine chamber and the existing positive squared lower bound.  Consequently a
packet-hereditary current that cancels every pure-bad singleton cannot orient even these actual
source cells:

```text
(good_p-bad_p)^2>0=Q(good_p,bad_p).                      (9)
```

Thus pre-projection timing does not rescue any channel-linear or finite-restriction-hereditary
counterterm.

### Theorem C — global positive cross-block rescue is impossible

Let `H(i,j)` be the symmetric real kernel of any quadratic relative current, and suppose every
two-node compression is nonnegative.  If exact principal subtraction makes one bad self-current null,
`H(j,j)=0`, then

```text
H(i,j)=H(j,i)=0 for every node i.
```

Indeed the two-node compression on `i,j` is Theorem A with `c=0`; symmetry gives the other
orientation.  Thus this is not merely a singleton-heredity obstruction.  A globally coupled
positive-semidefinite prime--Gamma kernel cannot cancel a bad diagonal and recover its excursion
through cross-prime or archimedean terms.  Any nonzero quadratic cross-block rescue attached to a
null bad diagonal is necessarily indefinite on the ambient coordinate space.

## 4. Anchored Schur-complement candidate `[CLOSED]`

For a normalized positive-definite kernel `K`, the canonical positive relative current is the
anchored covariance

```text
S_ij=K(t_j-t_i)-K(-t_i)K(t_j).                           (10)
```

For one node of mass `u` at `t`,

```text
anchor^2 = u^2 K(t)^2,
Schur residual = u^2 (1-K(t)^2).                         (11)
```

If `u!=0`, asking the residual to dominate the removed anchor correlation is equivalent to

```text
K(t)^2 <= 1/2.                                           (12)
```

Source-faithful de-attenuation has `K(xt)->1` as `x->0`, so `(12)` eventually fails on every
fixed nonzero source cell.  The Schur complement is positive precisely because it removes the
rank-one component containing the desired excursion.  It is a variance certificate, not a
relative orientation provider.

## 5. Candidate audit

1. **Post-projection diagonal subtraction:** fails on one unit node.
2. **Channel-linear pre-projection subtraction:** Theorems A--B force either retained bad
   diagonal or loss of all mixed orientation.
3. **Packet-hereditary relative current:** actual pure-bad one-mode cells `(8)` give the same
   contradiction inside the arithmetic source.
4. **Anchored covariance/Schur complement:** source fidelity drives its orientation inequality in
   the wrong direction by `(11)--(12)`.
5. **Invariant Sonin principal-relative trace:** existing Fourier-parity law annihilates the odd
   orientation channel; this is not a Julia repair.
6. **Gamma--Julia endpoint Hilbert--Schmidt dressing:** its exact multiplier has
   `chi_(p,e)^2<=1/2`.  On every nonzero pure-bad sixth-power cell, domination of the undressed
   excursion requires squared gain at least one.  Hence the existing compact dressing is a
   phase-faithful endpoint representation, not Route J's relative capacity.  Its separate
   Julia-dressed exterior-intertwiner conjecture has a completed three-node response endpoint.
7. **Definition by desired sign:** `R=(-min(C,0))^2` satisfies the first half of `(2)` tautologically
   and makes its boundedness exactly the Route-A/RH endpoint.  It creates no source knowledge.
8. **Generic positive-Euler/reflection current:** `positiveEulerQuartet_realization` and
   `positiveEulerQuartet_orientedCauchyResponse` realize a genuinely off-line quartet with
   nonnegative generalized-prime density, exact inversion/reflection data, and favorable
   unsquared orientation.  Therefore those generic properties cannot supply the missing sign.
9. **Globally positive cross-block kernel:** Theorem C annihilates the entire row and column of
   every cancelled bad diagonal.  Adding all primes and the Gamma node cannot restore orientation
   inside an ambient positive-semidefinite quadratic current.

## 6. Exact surviving class

Any remaining Route-J provider must satisfy all of the following:

1. **Source-constrained:** it may be defined only on the complete prime--archimedean packet;
   arbitrary coordinate packets cannot all remain admissible source inputs.
2. **Ambient-indefinite or nonlinear:** it cannot extend to a pairwise-positive quadratic kernel
   while both cancelling bad self-currents and retaining their cross-block couplings.  A quadratic
   survivor must be Krein-type and prove nonnegativity only on the literal arithmetic source locus;
   the other possibility is a genuinely nonlinear source functional with no quadratic extension.
3. **Non-positive-channel-linear:** it cannot be a fixed positive linear scalarization of the
   existing two-channel Julia Gram.
4. **Non-Schur:** it cannot be the canonical anchored covariance or any rank-one subtraction whose
   residual is asked to dominate the removed correlation universally.
5. **Arithmetic counterterm:** cancellation must follow from an exact prime--Gamma or co-Poisson
   identity before positive projection, not from an assigned diagonal subtraction.
6. **Source-uniform:** the same construction must prove the upper half of `(2)` without Xi zeros,
   eventual first-clock boundedness, or an RH-equivalent positivity premise.
7. **Source-faithful:** its scale choice must retain the zero-scale literal-source limit.
8. **Ordinary-prime-specific:** it must use a coupling falsified by the positive generalized-prime
   off-line quartet; positive Euler density, reflection, completion, and unsquared Cauchy
   orientation are insufficient even jointly.

This is a narrow but nonempty conjectural category.  The corpus contains phase-faithful Julia
dressings and joint finite prime--Gamma Grams, but none supplies an ambient-indefinite or nonlinear
source current, its arithmetic-locus positivity, negative-excursion orientation, and source-uniform
bound in `(2)`.  It also contains no theorem excluding every such source-constrained current.
Route J therefore remains open.

## 7. Strongest live conjecture

> **`JULIA-KREIN-PRINCIPAL-RELATIVE-COFINAL-ORIENTATION`.**  There is a completed
> prime--Gamma/co-Poisson current `T_(x,L)`, defined before good/bad projection, an arithmetic
> signature `J_(x,L)`, and a fixed source functional `tau_rel` such that
> `R_x(L)=tau_rel(T_(x,L)^* J_(x,L) T_(x,L))` obeys `(2)` on the literal source locus.  Its
> principal subtraction is an exact source identity, each cancelled bad diagonal has a nonzero
> source coupling, and the resulting ambient form is necessarily indefinite rather than a
> posteriori removal of positive diagonal mass.

Required construction witness: on the sixth-power pure-bad block, exhibit the exact cross-block or
archimedean term that cancels `(4)`, the ambient negative direction forced by Theorem C, and the
arithmetic identity keeping the literal full-source value nonnegative while retaining
negative-excursion orientation.  A signature symbol with no such identities is not a candidate.

## 8. Novelty and theatre audit

- Theorem A is elementary positive-cone algebra; no standalone novelty claim.
- Theorem B is elementary but closes the semantic loophole that moving diagonal subtraction
  “before projection” automatically preserves capacity.
- Theorem C is standard null-vector rigidity for positive-semidefinite kernels; no standalone
  novelty claim.  Its value is closing the proposed global prime--Gamma cross-block escape.
- New source-specific content is the weld of Theorems A--B to the exact infinite family of
  pure-bad sixth-power prime cells.
- The survivor is not counted as progress until a literal `T_(x,L)` and source identity are given.
  Current value is a falsifier and an exact route boundary.

## 9. Lean plan and gates

- [x] unrenormalized bad-energy route refuted unconditionally
- [x] exact route-level survivor ownership restored
- [x] channel-linear positivity classification proved on paper
- [x] negative-excursion diagonal-retention theorem proved on paper
- [x] actual pure-bad sixth-power source cells identified on paper
- [x] anchored Schur-complement candidate audited
- [x] formalize generic two-channel relative-capacity no-go
- [x] formalize actual pure-bad block specialization
- [x] formalize anchored one-node Schur tradeoff and source-faithful Julia failure
- [x] exclude existing Gamma--Julia endpoint Hilbert--Schmidt dressing as an excursion provider
- [x] prove positive global cross-block kernels cannot rescue a cancelled bad diagonal
- [ ] construct an ambient-indefinite/nonlinear source current or prove its source constraints
      inconsistent
- [ ] close Route J only when no unowned survivor remains
