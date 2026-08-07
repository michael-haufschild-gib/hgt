# Burnol general reciprocal-seed landing

- **Stage:** 2-fully-proven
- **Route:** R
- **Claim label:** `[THEOREM — PAPER PROVED; LEAN OPEN]`
- **Target:** explicit squarefull Stokes summability producer

## Frozen claim

Let `0 < b`, and let `g` be an integrable complex seed supported in
`[b,b⁻¹]`.  If the literal co-Poisson sum `P g` represents a vector of
Burnol's extended Sonine space at aperture `b`, then

\[
  g^\vee(u)=u^{-1}g(u^{-1}), \qquad
  \mathcal F(Pg)=P(g^\vee)\quad\text{in }L^2(\mathbb R).
\]

Consequently the reciprocal seed, together with the cosine transform of the
original vector, is again a `BurnolCoPoissonSource b`; reciprocal landing is
involutive.  Since source seeds are measure-theoretic representatives, the
coefficient-faithful statement is equality almost everywhere whenever the
input seed is only specified almost everywhere.

## Conjecture loop

1. `[FALSIFIED]` Forward and inverse quotient contractions force the Mellin
   character to have unit modulus.  False: the carrier changes with aperture,
   and the kernel norm may grow exponentially.
2. `[FALSIFIED AS STATED]` Literal reciprocal landing follows from the existing
   `BurnolCoPoissonSource` fields by pointwise rewriting.  False as a proof
   method: `Integrable` and `vector_eq_sum` contain only almost-everywhere
   information, while the stored seed is a pointwise representative.
3. `[SURVIVES]` Reciprocal landing in the natural almost-everywhere category.
   Co-Poisson intertwining against every Schwartz test identifies
   `P(g^vee)` with the unitary Fourier transform of `P g` as a distribution;
   local integrability upgrades distributional equality to almost-everywhere
   equality.

## Dependency-closed paper proof

1. Inversion preserves the multiplicative window and sends an integrable
   window seed to an integrable window seed.  On the positive ray this is the
   change of variables `u = v⁻¹`; the factors `v⁻¹` and `v⁻² dv` reduce the
   norm integral to an integrable bounded multiple of `|g(u)|` on the compact
   window.
2. A co-Poisson sum of an integrable compact-window seed is locally
   integrable.  On every compact `t`-set its defining series is a fixed finite
   sum of dilates of the seed, plus a constant.
3. Pairing `P g` with an even Schwartz function and exchanging the absolutely
   convergent sum and integral gives Burnol's co-Poisson identity
   `⟨P g,phi⟩ = ⟨P(g^vee), F phi⟩`.
4. The source landing makes `P g` an `L²` vector.  Plancherel gives an `L²`
   vector `F(P g)` with the same Schwartz pairings as the locally integrable
   function `P(g^vee)`.
5. Uniqueness of locally integrable regular distributions yields
   `F(P g)=P(g^vee)` almost everywhere.  Fourier involutivity on the even
   carrier and `(g^vee)^vee=g` give involutivity.

## Route-R consequence after formalization

At a zeta zero, the general-seed Mellin factorization annihilates every source
vector.  Reciprocal landing makes each cosine generator another source vector,
so the Riesz evaluator annihilates the full closed co-Poisson source space, not
only the one-sided vector span.  Every actual right-half zero therefore enters
the already formalized full aperture ladder and obeys its exact forced-escape
law.  Remaining producer burden becomes a pre-divisor subexponential/tightness
bound on those actual kernels; such a bound forces the centered exponent and
hence the required squarefull Stokes summability.

## Novelty boundary

Burnol's co-Poisson intertwining and Sonine-space framework are literature.
New project content is the coefficient-faithful Lean landing for the corpus's
general source structure and its combination with the independently proved
two-sided aperture escape law.  Do not claim this theorem alone proves RH or
the squarefull summability endpoint.
