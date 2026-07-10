# Perron--Mellin seam residues recover the arithmetic tail

- **ID:** perron-mellin-seam-residue
- **Stage:** 2-fully-proven
- **Type:** THEOREM / NATIVE OBJECT, `[PROVED HERE]`
- **Date:** 2026-07-10
- **Parents:** `sonin-perron-support-transfer.md`, `perron-carrier-flank-mass.md`
- **Lean:** `formal/GaloisForLFunctions/RHTower/PerronMellinSeamResidue.lean`

## Medalist lens

Exact cross-line Mellin coherence is too rigid: with finite horizontal carrier mass it forces finite
Dirichlet support.  The first repair is to write each negative line as

`F(-M+it) = T_M(g)(t) + Delta_M(t)`,                                  (D)

where `T_M(g)` is the normalized transform of the negatively weighted common source and `Delta_M`
is an `L2` seam defect.

A finite geometric bound on `||Delta_M||_2` is not new structure.  Triangle inequality merely
replaces the source radius by the maximum of the source and defect radii, again forcing finite
support.  The contour does not observe the full defect norm.  At coefficient index `n` and knot
width `delta`, it observes one pairing with the variable Perron kernel.

The native object is therefore the **Perron--Mellin seam residue**

`Res_(M,n,delta)(Delta) = (2*pi)^(-1) integral_R
  Delta_M(t) E_(n,delta)(-M+it) dt`,                                  (1)

and its knot-normalized coefficient coordinate

`A_(M,n,delta)(Delta) = delta^(-1) Res_(M,n,delta)(Delta)`.            (2)

The theorem proves that these are not generic error terms.  Beyond the physical source radius they
recover the Dirichlet coefficients exactly in the limit.

## Theorem A `[PROVED]`: full vertical boundary transport

Let `F E` be entire.  At a fixed depth `M`, suppose a height sequence sends the top and bottom
horizontal integrals to zero, sends the truncated right integral to its full integral, and tends to
infinity.  If the left vertical integrand is integrable, then

`integral_(Re s=c) F(s)E(s) ds/i
  = integral_(Re s=-M) F(s)E(s) ds/i`.                               (3)

### Proof

Cauchy's rectangle identity gives, at every truncation height,

`i R_k = Top_k - Bottom_k + i L_k`.

Right integrability and left integrability identify the limits of `R_k` and `L_k`; horizontal escape
kills the remaining two terms.  Uniqueness of limits gives `iR=iL`, and `i!=0` gives (3).

This strengthens the earlier boundary-charge inequality to an exact equality whenever the full left
integral exists.

## Theorem B `[PROVED]`: the Perron probe is an exact `L2` test vector

For `M>=2`, `n>=1`, and `0<delta<n`, put `D=n-delta`.  Then

`t |-> E_(n,delta)(-M+it)` belongs to `L2(R)` and

`||E_(n,delta)(-M+i·)||_2
  <= 4 sqrt(pi) D^(1-M)`.                                             (4)

### Proof

The pointwise flank estimate gives

`|E_(n,delta)(-M+it)| <= 4 D^(1-M)/(1+t^2)`.

The `L2` norm of `(1+t^2)^(-1)` is at most `sqrt(pi)` because its square is bounded by itself and
the latter integrates to `pi`.  `L2` domination gives (4).

Consequently every source trace and every `L2` seam defect has an integrable pairing with the
variable Perron probe.

## Theorem C `[PROVED]`: exact coefficient charge splitting

Let `F` be entire and agree on `Re(s)>=c>0` with an absolutely convergent Dirichlet series

`sum_(m>=1) a_m m^(-s)`.

Assume (D) at depth `M`, boundary escape at `(M,n,delta)`, `M>=2`, `n>=1`, and
`0<delta<min(1,n)`.  Define the source charge

`Src_(M,n,delta)(g) = (2*pi)^(-1) integral_R
  T_M(g)(t) E_(n,delta)(-M+it) dt`.                                  (5)

Then

`delta*a_n = Src_(M,n,delta)(g) + Res_(M,n,delta)(Delta)`.            (6)

### Proof

The variable Perron identity identifies `delta*a_n` with the normalized right vertical integral.
Theorem A transports that integral to the full left line.  Equation (D), Theorem B, and `L2` Holder
make both summands integrable, so the left integral splits into (5) and (1).  This is (6).

## Theorem D `[PROVED]`: source charge dies beyond physical support

Let `f` belong to the even Sonin carrier at cutoff `q>0`, and let

`g=logEvenUnitary(f)`.

Then

`|Src_(M,n,delta)(g)|
 <= kappa ||g|| q^(-M) (n-delta)^(1-M)`,                              (7)

where `kappa=2 sqrt(pi)/pi`.

If

`q^(-1) < n-delta`,                                                   (8)

then

`Src_(M,n,delta)(g) -> 0`.                                           (9)

### Proof

The Sonin logarithmic support theorem gives

`||T_M(g)||_2 <= q^(-M)||g||_2`.

Combine this with (4), Cauchy--Schwarz, and the normalization `(2*pi)^(-1)` to obtain (7).  Its
geometric ratio is `q^(-1)/(n-delta)`, which is strictly below one under (8), proving (9).

## Theorem E `[PROVED]`: seam residues recover the arithmetic tail

Assume:

1. `q>0` and `f` belongs to the even Sonin carrier at cutoff `q`;
2. the negative lines of `F` admit the additive defect decomposition (D);
3. `F` is entire and has the right-half-plane Dirichlet expansion above;
4. `F` has finite coefficient-independent Perron horizontal mass.

For every admissible `(n,delta)` satisfying (8),

`Res_(M,n,delta)(Delta) -> delta*a_n`,                                (10)

and therefore

`A_(M,n,delta)(Delta) -> a_n`.                                       (11)

### Proof

Horizontal carrier mass produces boundary escape eventually in `M`.  On that tail, (6) gives

`Res_(M,n,delta)(Delta) = delta*a_n - Src_(M,n,delta)(g)`.

Apply (9) to obtain (10); divide by the fixed nonzero `delta` to obtain (11).

## Corollaries `[PROVED]`

### Live seam witness

If `a_n!=0` and (8) holds, then

`A_(M,n,delta)(Delta) != 0`

eventually.  Thus every nonzero coefficient beyond the physical source radius gives a persistent,
coefficient-indexed seam witness.

### Knot-width independence

If `delta_1` and `delta_2` are both admissible and both satisfy (8), then

`A_(M,n,delta_1)(Delta) - A_(M,n,delta_2)(Delta) -> 0`.               (12)

The recovered arithmetic coordinate is independent of the auxiliary Perron probe width.  This is
the first intrinsic equivalence relation on the defect family: different constraint probes agree
asymptotically because they see the same coefficient.

## Candidate attack

- `[BRIDGE]` An additive defect with finite geometric `L2` radius gives support radius
  `max(q^(-1),R_defect)`.  This is useful bookkeeping but cannot retain infinite support.
- `[FAILED]` Scalar or cocyclic rescaling of the source trace.  A finite-modulus rescaling again has
  finite geometric radius; an infinite one only renames the obstruction.
- `[FAILED]` Coherence modulo an uncontrolled closed subspace.  Perron pairings do not descend to
  the quotient unless its annihilator is specified, so the quotient discards the coefficient data.
- `[SURVIVES]` The coefficient-indexed Perron pairing of an unrestricted `L2` defect.  It does not
  require a finite defect radius, and Theorem E proves that it carries the arithmetic tail exactly.

## What the theorem changes

The prior obstruction said only that exact coherence fails for infinite-support carriers.  The new
theorem identifies the residue left by that failure:

`cross-line defect --Perron probe--> Dirichlet coefficient`.

This is a constraint, not a propagation rule.  The family `Delta_M` need not evolve with `M`; its
asymptotic pairings are fixed by the right-half-plane arithmetic data.  Conversely, any proposed
source/carrier weld must reproduce the limits (11) and the knot-consistency relation (12).

## Novelty and significance gates

- **NOVEL:** (6), (10), (11), and (12) are not imported parent-theory statements.  They arise from
  composing the project-native negative Mellin trace, variable Perron extraction, horizontal carrier
  mass, and the newly isolated additive seam defect.  The defect is equipped with exact arithmetic
  coordinates rather than an undifferentiated error norm.
- **SIGNIFICANT:** the theorem replaces a falsified exact-coherence route by a viable native object
  for infinite support.  It locates the entire arithmetic tail in the cross-line seam and supplies a
  precise invariant that future divisor or cocycle constraints must kill, quantize, or reconstruct.

## Scope and open core

- `[PROVED]` `canonical-perron-mellin-seam.md` weakens the decomposition to an eventual interface,
  proves uniqueness, and constructs it canonically from carrier flank `L2` energy.  The defect Prop
  is no longer an assumption.
- The theorem still assumes finite horizontal carrier mass; it does not prove it for the target.
- `[OPEN CORE]` Repair the completed/raw mismatch: `xi` has archimedean decay but a dressed
  Dirichlet edge.  The next extractor must retain completion and expose an explicit arithmetic
  coefficient plus computable Gamma/boundary charge before a divisor or `M+` constraint can act.
- The theorem does not prove RH.

## Gates

- [x] 0 -> 1: additive defect and Perron seam coordinates isolated; norm-only repairs attacked.
- [x] 1 -> 2: exact charge splitting, source decay, tail recovery, and knot invariance proved.
- [x] 2 -> 3: theorem family formalized in Lean.
- [ ] 3 -> 4: the seam construction is canonical; promotion requires an archimedean-completed
  coefficient extractor and a divisor/cocycle constraint on its recovered coordinates.
