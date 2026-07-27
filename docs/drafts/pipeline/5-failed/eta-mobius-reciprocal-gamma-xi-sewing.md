# Eta/Möbius reciprocal-Gamma sewing does not transport the Xi source into the HT phase

- **ID:** `eta-mobius-reciprocal-gamma-xi-sewing`
- **Stage:** 5-failed
- **Type:** SOURCE-MISMATCH NO-GO / DIFFERENTIAL-AXIS NO-GO
- **Status:** `[FALSIFIED AS A DIRECT RH BRIDGE] [NO UNIVERSAL NO-GO CLAIM]`
- **Source:** `../2-fully-proven/new_scientific_knowledge/multiple-elliptic-gamma-reciprocal-rank-flat-phase-reversal.md`
- **Positive survivor:** `../2-fully-proven/new_scientific_knowledge/prime-completion-annihilates-hypertranscendence-at-even-temperature.md`

## Proposed bridge

Use a reciprocal-period multiple elliptic Gamma family whose finite fibres are
hypertranscendental and exponentially flat at a zero-nome boundary.  Identify a Dedekind-eta or
\(q\)-Pochhammer specialization with the prime Euler source, then use modular inversion to sew the
flat HT sector into the completed Xi source.

## Exact failures

### 1. Direct diagonal eta is not source-pure

For one local nome,

\[
 E(q)=(1-q)^{-1},
\qquad
 q\partial_q\log E(q)=\sum_{n\ge1}q^n.
\]

The inverse Euler \(q\)-product

\[
 P(q)=\prod_{d\ge1}(1-q^d)^{-1}
\]

instead satisfies

\[
 q\partial_q\log P(q)=\sum_{n\ge1}\sigma_1(n)q^n.
\]

Thus diagonal specialization inserts additive-partition multiplicities.  It is not the local
von Mangoldt depth ray.

### 2. One-particle extraction repairs the source but loses the HT carrier

The stronger statement “a \(q\)-Pochhammer carrier cannot contain the Euler ray” is false.  With a
fugacity \(x\),

\[
 [x]\prod_{e\ge0}(1-xq^e)^{-1}
   =\sum_{e\ge0}q^e=(1-q)^{-1}.
\]

For several nomes, the first coefficient is the full finite Euler packet
\(\prod_j(1-q_j)^{-1}\).  But this coefficient projection discards every higher Fock grade and
does not transport hypertranscendence of the full \(x\)-function into the spectral variable.

### 3. The differential axes do not match

The multiple elliptic Gamma dichotomy is a theorem for

\[
 \partial_z\quad\text{with all periods fixed}.
\]

The Xi spectral derivation moves every prime nome:

\[
 q_p=p^{-s},\qquad
 \partial_s q_p=-(\log p)q_p.
\]

Identifying \(z\) with \(s\) therefore changes the differential problem.  The existing
hypertranscendence theorem supplies no conclusion for this diagonal/base-period direction.
HTGeometry's directional-law corpus explicitly warns that DA/HT phase is derivation-dependent.

### 4. Plethystic Möbius repair returns the existing RH wall

Möbius inversion gives the exact identity

\[
 \prod_{d\ge1}P(q^d)^{\mu(d)}=(1-q)^{-1},
\]

or, logarithmically,

\[
 \sum_{d\ge1}\mu(d)\log P(e^{-d\beta})
   =-\log(1-e^{-\beta}).
\]

Its Mellin action is not new:

\[
 \Gamma(s)\zeta(s)\zeta(s+1)
   \longmapsto
 \frac1{\zeta(s)}
   \Gamma(s)\zeta(s)\zeta(s+1)
   =\Gamma(s)\zeta(s+1).
\]

Any attempt to continue the raw Möbius multiplier through
\(\operatorname{Re}s>1/2\) is the exact continuation wall already proved equivalent to RH in
`MobiusLaplaceCriterionFrontier.lean`.  Multiplication by an analytic nowhere-zero factor cannot
make that wall easier, by `MobiusLiouvilleSquareDilationWall.lean`.

### 5. Modular inversion and Möbius dilation do not commute

For \(D_d:\tau\mapsto d\tau\) and \(S:\tau\mapsto-1/\tau\),

\[
 SD_d=D_{1/d}S.
\]

Writing \(A(it)=\log P(e^{-2\pi t})\), eta modularity gives

\[
 A(i/(dt))
 =\frac{\pi dt}{12}-\frac12\log(dt)-\frac{\pi}{12dt}+A(idt).
\]

The raw inverse-dilation Möbius summands do not even tend to zero because of the linear modular
anomaly.  Subtracting that anomaly leaves the ordinary \(A(idt)\) Möbius sum, which is the
elementary Euler ray above.  Modularity has moved the cancellation problem into divergent or
regularized Möbius anomaly sums; it has not produced a new estimate.

## Scope of the no-go

This card kills:

- direct diagonal eta identification;
- one-particle extraction as a transporter of full HT;
- plethystic Möbius repair followed by ordinary eta modular inversion;
- any argument that silently identifies the additive \(z\)-derivation with the Xi
  \(s\)-derivation.

It does **not** rule out every nonlinear source map, every multiple-Gamma construction, or every
completion-stable invariant.

## Strongest positive survivor

Keeping the complete occupation product instead of diagonalizing or projecting yields an exact
source-pure theorem:

- every finite prime packet with at least two primes is HT;
- every logarithmic fugacity jet is a finite Euler packet;
- all-prime completion turns occupations into all positive integers;
- at every even integer exponent, Gamma reflection makes the completed function DA.

This is proved in
`prime-completion-annihilates-hypertranscendence-at-even-temperature.md`.

The surviving RH design requirement is therefore stronger than the original bridge:

> Construct a source-native polarized class which preserves the Xi spectral derivation, survives
> cofinal prime completion, retains at least one rank-three HT obstruction, and produces the missing
> finite-packet Pick-kernel domination.

Differential transcendence itself is not such a class.

## Paper and Lean status

The direct route is retired.  Its Möbius/Lambert and analytic-unit boundaries are already
unconditionally formalized in:

- `formal/GaloisForLFunctions/RHTower/PrimeLambertMobiusInversion.lean`;
- `formal/GaloisForLFunctions/RHTower/LambertRayRecovery.lean`;
- `formal/GaloisForLFunctions/RHTower/MobiusLaplaceCriterionFrontier.lean`;
- `formal/GaloisForLFunctions/RHTower/MobiusLiouvilleSquareDilationWall.lean`.

No new Lean theorem should formalize the elementary mismatches above merely to count progress.
Formal work belongs on the positive prime-completion survivor.

## Log

- 2026-07-27 — diagonal eta coefficient mismatch found.
- 2026-07-27 — overstrong claim corrected: first fugacity coefficient does recover the Euler ray.
- 2026-07-27 — differential-axis mismatch isolated.
- 2026-07-27 — plethystic Möbius repair reduced to the existing RH-equivalent continuation wall.
- 2026-07-27 — exact noncommutation with modular inversion exposed the divergent anomaly.
- 2026-07-27 — route retired only after extracting the source-pure prime-completion survivor.
