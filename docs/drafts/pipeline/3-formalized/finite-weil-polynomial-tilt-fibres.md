# Finite Weil polynomial tilt fibres and normalized uniqueness

Status: FORMALIZED — paper proof, three native leaves, and all six axiom audits verified.

## Objective

Classify every polynomial potential inducing a given canonical finite law, and identify the unique degree-at-most-r potential whose partition function is one. All final equivalences quantify arbitrary r, k, target law, and potential without added helper hypotheses.

## Corpus evidence

- `HTGeometry/TiltedEqualityRigidity.lean`: equal tilted laws iff potential difference is almost everywhere constant.
- `HTGeometry/FiniteNodePolynomialIdeal.lean`: constant node values iff a unique nodal-polynomial factorization exists.
- `RHTower/WeilLogShiftObservableSupport.lean`: canonical base almost-everywhere predicates hold iff they hold at every support atom.
- `RHTower/WeilLogShiftObservableLaw.lean`: every real observable is integrable on this finite support.
- `RHTower/WeilLogShiftPolynomialTiltRealization.lean`: the canonical interpolated log-density realizes precisely strictly positive target laws.
- Local Mathlib Lean: log Radon–Nikodym derivative of a tilt and Lagrange interpolation uniqueness.

Only local Lean evidence is used. Search artifacts: `/tmp/hgt-polynomial-tilt-fibres-search.json` and the offset-20 page. Exhaustive project Lean text search for combined polynomial-tilt equality/factor/uniqueness found only the preceding realization root.

## Dependency-closed paper proof

Write x_i for the distinct first coordinates of the r+1 canonical atoms, N(X)=product_i(X-x_i), and μ for their positive base law. Finite support discharges exponential integrability for every real polynomial.

1. μ tilted by p equals μ tilted by q iff p(x_i)-q(x_i) is constant in i. Anchor the constant at i=0. Applying the existing finite-node factorization theorem to p-q gives the equivalent unique expression p-q=C((p-q)(x_0))+N*h.
2. For arbitrary target Q, equality with its atomic law forces every Q_i>0 by the existing positive-support theorem. Conversely, when Q is positive, its canonical interpolated log-density L_Q induces Q. Substituting q=L_Q into step 1 gives the full fibre classification, including all high-degree potentials.
3. The partition function of L_Q is sum_i μ_i exp(log(Q_i/μ_i))=sum_i Q_i=1.
4. Suppose degree(p)<r+1, its partition function is one, and its tilt is Q. Positivity follows from step 2. Equality of tilted measures and the two log Radon–Nikodym identities, with both log partition functions zero, imply p(x_i)=L_Q(x_i). Lagrange uniqueness forces p=L_Q. The converse follows from realization, degree bound, and step 3.
5. Therefore there exists a unique normalized polynomial of degree<r+1 producing Q iff every Q_i>0.

No claim about the restricted three-parameter quadratic family is included. No asymptotic hypotheses or numerical experiments are needed.

## Planned formal artifacts

- `RHTower/WeilLogShiftPolynomialTiltRigidity.lean`
- `RHTower/WeilLogShiftPolynomialTiltFibres.lean`
- `RHTower/WeilLogShiftPolynomialTiltNormalization.lean`

## Verification progress

- Corpus lexical search inspected all 32 eligible declarations across two pages. The backend reported no markers; source checks supplied the exact ingredients.
- Native API scratch passed: 15 API bindings, with exact local signatures checked for log Radon–Nikodym derivatives and Lagrange uniqueness.
- Rigidity and Fibres native leaves passed with empty logs.
- Normalization native leaf passed with an empty log. The actual-root final native audit passed: all six declarations depend only on `propext`, `Classical.choice`, and `Quot.sound`, with no residual diagnostics.
- Metadata audit passed: all three objects and five direct import edges are fresh; whitespace is clean.
- All three new leaves are wired into the RHTower umbrella.
- Repository lint snapshot: 367 warnings and two unrelated unreachable modules, `HTGeometry.DyadicParentBase` and `HTGeometry.WalshPowerWeights`; no new-module lint errors.
- Final audit: `/tmp/hgt-polynomial-tilt-fibres-final-audit.lean` and `.log`. Metadata/axiom checker: `/tmp/hgt-polynomial-tilt-fibres-audit.py`. Lint snapshot: `/tmp/hgt-polynomial-tilt-fibres-lint.log`.

## New insight

The full polynomial family has an exact algebraic equality classification: its only redundancies are additive constants and polynomials vanishing on the support. Prescribing degree below support size and partition function one removes both, giving a unique polynomial parameter for every strictly positive finite target law. This strengthens existence into complete fibre classification and normalized uniqueness, including every finite r and k.

## Next conjecture, not proved here

Although a finite real tilt cannot attain a target with a zero atom, every boundary law should be a total-variation limit of the same bounded-degree polynomial family. A candidate construction mixes the target with a positive uniform law and applies the verified log-density polynomial. Search the local Lean corpus for the finite-law mixture and total-variation ingredients before implementation.
