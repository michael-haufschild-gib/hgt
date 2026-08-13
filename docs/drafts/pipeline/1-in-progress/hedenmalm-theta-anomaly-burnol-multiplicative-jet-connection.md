# Hedenmalm theta anomaly: Burnol multiplicative-jet connection

- **Label:** `P-G118`
- **Route:** P
- **Parents:** `P-G115`, `P-G117`
- **Status:** theorem proved and formalized; direct, exact module, and axiom audits passed; umbrella imported

## Conjecture tested

Differentiate the exact completed Burnol relation induced by `6 = 2 * 3`.  Its coefficient-jet
defect should not remain in P-G117's arithmetic syzygy kernel.  After the unique Hermitian
normalization by the two-prime frame energy, it should reconstruct the full spectral coordinate.
Its imaginary part would then recover P-G115's horizontal Gaussian/Gamma source gauge without
fitting a divisor-dependent coefficient.

## Target identities

For the two sine-addition coefficients `u` and `v`, write their literal derivatives as `du` and
`dv`.  There should be nonzero arithmetic weights `k3,k2` such that, division-free at every
spectral point including the removable origin,

```text
du(z) = -k3 z A3(z),
dv(z) = -k2 z A2(z).
```

Consequently the Hermitian jet numerator

```text
J(z) = du(z)/k3 conj(A3(z)) + dv(z)/k2 conj(A2(z))
```

obeys

```text
J(z) = -z (|A2(z)|^2 + |A3(z)|^2).
```

Since P-G112 proves frame energy strictly positive, `-J/E` is globally defined and equals `z`.
On an Xi copy `q`, P-G115's horizontal gauge should equal `-2 Im(-J/E)`.

## Result

Conjecture succeeds exactly.  Lean proves `du,dv` are literal complex derivatives of the two
sine-addition coefficients and proves differentiated `6 = 2 * 3` syzygy.  Explicit nonzero weights
give the two division-free opposite-cell identities at every `z`, including `z=0`.  Hermitian
contraction then gives `J(z)=-zE(z)`, while P-G112's strict frame-energy positivity makes
`-J(z)/E(z)=z` globally.

At every Xi multiplicity copy, the P-G115 Gaussian/Gamma horizontal gauge is exactly `-2` times
the imaginary part of this arithmetic multiplicative-jet connection.  Stronger division-free form
is

```text
Re(gauge(q)) E(q) = 2 Im(J(q)).
```

Thus value-level multiplicative relations form P-G117's kernel, but their first jet is the
tautological spectral connection on the quotient.  Arithmetic differentiation recovers both
height and horizontal displacement; its anti-Hermitian part is precisely the RH-bearing
determinant-line class.  This is a source construction, not a fitted divisor coefficient.

It does not prove flatness.  `Im(-J/E)=0` on all Xi copies remains equivalent to RH.  Next viable
producer must force the anti-Hermitian part of this concrete completed-source connection to vanish;
more value-level syzygies cannot do so.

## Scientific decision gate

- **Success:** arithmetic multiplicative jet curvature canonically recovers P-G115 horizontal
  class.  This upgrades source provenance and moves open problem to completed Ward flatness of a
  concrete connection.
- **Failure:** record exact degeneracy; pivot to completed polar/head-current transgression.
- Result must not claim RH unless an independent completed source identity forces recovered
  connection real on every Xi divisor mode.

## Verification log

- 2026-08-13 — Card opened after P-G117 proved value-level multiplicative syzygies lie entirely in
  arithmetic kernel.  Differentiation exposes candidate quotient class linear in spectral point.
- 2026-08-13 — Direct `lake env lean` passed with no diagnostics after proof cleanup.
- 2026-08-13 — Exact module build passed at `[12940/12940]`; module imported by `RHTower.lean`.
- 2026-08-13 — Capstone axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`.
