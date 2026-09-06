# Exact admission boundary under one-prime attenuation

**Stage:** 3-formalized. **RH implication:** none. **Novelty:** not certified.

Module: `formal/GaloisForLFunctions/RHTower/EulerDeletionPrimeAttenuation.lean`.
Namespace: `RHTower.DeletionPrimeAttenuation`.

For a prime `p` and `0<=c<=1`, the actual coefficient is `b(n)=c^(v_p(n))` on positive
integers, extended by zero at zero. Lean proves complete multiplicativity, the upper bound
one, and strict positivity when `c>0`.

The exact summatory recurrence has bounded digit remainder
`R(N)=(p-c)*sum_(n<=N)b(n)-(p-1)*N`, with `0<=R(N)<=p-1`.
The general classification `bounded_deletion_iff` says that the coefficients
`(1-ell*[p|n])*b(n)` have bounded prefixes exactly when `ell*c=p`. At that normalization,
their prefix equals `N mod p-R(floor(N/p))`, with bound `p-1`.

`harmonicDeletion_tendsto` proves divergence to positive infinity at exponent one when
`c<1` and the original multiplier `p` is retained. Ordinary Dirichlet convergence propagates
to exponents further right; consequently `literal_not_convergent_of_re_lt_one` excludes
convergence at **every complex exponent with real part below one**. Conversely
`repaired_converges` admits the uniquely repaired coefficients throughout `Re(s)>0`.

The premise-free `fifth_attenuation_admission_separation` packages the concrete example
`p=5,c=1/5`: globally positive contractive multiplicative coefficients, unique multiplier
25, prefix bound 4, repaired positive-half-plane convergence, and failed literal convergence
at every `Re(s)<1`. No statement is made about other points on the boundary `Re(s)=1`.

`lake env lean /tmp/hgt-attenuation-LEwD86/Audit.lean` passed. Six axiom audits covering the
remainder, classification, divergence, two admission statements, and capstone report only
`propext`, `Classical.choice`, and `Quot.sound`. Production matches the audited scratch body.
The narrow final `lake build GaloisForLFunctions.RHTower.EulerDeletionPrimeAttenuation`
passed. Its umbrella import is wired; no full or umbrella build ran. Repository-wide
`scripts/formal_tools.py lint` failed solely on concurrent work outside this module:
`HTGeometry/QuarticJensenDispersionTransfer.lean` was unreachable from its theorem-area
umbrella. No lint error named this module. Output: `/tmp/hgt-attenuation-LEwD86/lint.log`.
That historical lint failure was cleared in the subsequent compatible-curvature audit:
repository-wide lint passed, with output `/tmp/hgt-compatible-curvature-Pe4gsu/lint.log`.

The [paper proof and analytic-continuation distinction](../2-fully-proven/euler-deletion-prime-attenuation-admission.md)
also explains the motivating Euler quotient. That quotient identification is not a new
exported Lean theorem here. No computational experiment or certificate was used.

This closes the [one-prime attenuation shortcut](../5-failed/euler-deletion-prime-attenuation-shortcut.md)
for extending finite coefficient countermodels to the infinite deletion source, with an
exact positive repair. It does not establish a relation forced by
an actual zeta zero, exclude off-line zeros, or qualify as a new RH architecture.
