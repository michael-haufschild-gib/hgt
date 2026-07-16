# Meromorphic restriction preserves the complete hypertranscendental clock

- **ID:** `meromorphic-restriction-hypertranscendence`
- **Status:** FORMALISED IN LEAN 4
- **Type:** differential-field infrastructure / local observability theorem
- **Lean:**
  - `formal/GaloisForLFunctions/HTGeometry/MeromorphicDifferentialField.lean`
  - `formal/GaloisForLFunctions/HTGeometry/MeromorphicRestrictionHypertranscendence.lean`
- **Scientific novelty:** not claimed; this closes a reusable formal transport gap

## Statement

Let `V` be a nonempty open connected subdomain of an open connected complex domain `U`.  The
canonical restriction map

\[
  \operatorname{Mero}(U)\longrightarrow \operatorname{Mero}(V)
\]

commutes with the meromorphic differential.  When both fields carry their canonical embedded
rational coordinate field `C(z)`, restriction is a differential `C(z)`-algebra embedding.
Therefore

\[
  x\text{ hypertranscendental over }\mathbf C(z)
  \quad\Longrightarrow\quad
  x|_V\text{ hypertranscendental over }\mathbf C(z).
\]

## Lean declarations

Carrier and field naturality:

- `restrictAnalytic_analyticSubringDeriv`;
- `restrictMeroHom_deriv`.

Rational-coordinate and HT transport:

- `restrictMeroAlgHomRatFunc`;
- `restrictMeroAlgHomRatFunc_deriv`;
- `hypertranscendentalOver_restrictMeroAlgHomRatFunc`.

The field theorem is proved on arbitrary fractions and uses the exact quotient-rule differential.
The HT theorem then applies the existing covariance of differential independence under an
injective derivation-preserving algebra homomorphism.

## Corpus gain

The global meromorphic field is convenient for Gamma-orbit, elliptic-Gamma, and Dirichlet
hypertranscendence proofs.  Physical response laws are usually regular only on a smaller chart:
exponentiating a meromorphic source can create essential singularities at the source poles, while
the response is analytic on every pole-free observation domain.  Before this theorem, the corpus
had an injective meromorphic restriction map but no proof that it preserved derivatives, so global
HT results could not be transported through the general differential-clock embedding API.

That gap is now closed.  Any already-proved global meromorphic HT source can be restricted to a
regular local clock or experimental chart without re-proving its differential freeness.

## No-go and significant positive replacement

**No-go.** Plain field restriction does not by itself transport hypertranscendence: it must preserve
the complete jet, not only values.  Injectivity alone is insufficient for the differential theorem.

**Positive theorem.** Canonical meromorphic restriction is both injective and derivation-preserving,
so it preserves every finite jet-observable field and the full HT status exactly.

## Black-hole and RH pressure test

This discharges the domain-restriction premise in the Schwarzschild Love-response route: the global
Gamma/digamma clock may be moved to a pole-free local response domain without losing HT.  The one
remaining analytic identification is the local exponential-response germ itself.

For RH, the theorem is source transport rather than a source producer.  It prevents localization
from erasing an already-established Gamma or Euler HT source, but it does not supply the missing
prime residual sign or orient zeros.

## Verification

- `lake env lean GaloisForLFunctions/HTGeometry/MeromorphicDifferentialField.lean`
- exact target: `lake build +GaloisForLFunctions.HTGeometry.MeromorphicRestrictionHypertranscendence`
- direct file check: `lake env lean GaloisForLFunctions/HTGeometry/MeromorphicRestrictionHypertranscendence.lean`
- no numerical computation and no full build
