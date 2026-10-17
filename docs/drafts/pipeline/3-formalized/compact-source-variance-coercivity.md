# Compact-source variance coercivity and zero-energy rigidity

- **ID:** compact-source-variance-coercivity
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** The constructed mixed graph controls weighted source variance;
  its continuous zero-energy states are constant on the entire nonzero source,
  even when that source has disconnected support.

## Exact result

Use the compact mixture from `CompactSourceResistanceMass.lean`, its source
radius B, physical L² primitive f and finite jump energy J. Let

    M = ∫ψ²,    A = ∫ψ²f,    Q = ∫ψ²f².

Proved the premise-free inequality

    0 ≤ M Q − A² ≤ sinh(2B) J.

All quantities are constructed and finite by compact-source admission. The
unnormalized variance avoids a nonzero-mass assumption. Also proved the classification
`J=0` iff f(u)=f(v) whenever ψ(u)ψ(v)≠0. The actual source may
have holes: the diffuse positive-lag kernel still links different components.

## Mechanism and audit boundary

For contributing positive lags, 0<h≤2B and
`w_arch(h)≥1/sinh(2B)`. The change of variables v=u+h converts the
positive-lag pair energy to half the symmetric pair integral. Expanding that
integral gives `2(MQ−A²)`. The arithmetic part is nonnegative. Continuity and
full support of product Lebesgue measure turn zero variance into pointwise
constancy on every nonzero source region. All moments and transports have
constructed integrability proofs. Combining the result with compact admission
also bounds variance by `sinh(2B) * resistanceMass * sourceDirichletMass`.

Corpus query `compact source weighted variance graph spectral gap` completed
without errors or partial results. Candidate and source-argument sections contain
finite weighted-graph gap interfaces and finite weighted-variance identities,
but no matching compact diffuse-source theorem. Semantic coverage is unmeasured;
this is not an exhaustive novelty result.

Focused corpus search completed without errors or partial results. It found
the existing hyperbolic-multiplier variance and centered-energy identities,
plus compact admission, but no current compact mixed-graph coercivity theorem.
Coverage is semantic-unmeasured and its snapshot lags the index. The existing
`CenteredHyperbolicGramControl.lean` variance concerns a specific cosh multiplier;
the present arbitrary continuous pair/lag identity and actual graph comparison
were not present. Classical variance and positive-kernel methods are background,
not claimed as externally novel.

## Certification

Paper proof is complete in `docs/reports/BiScaleUncertainty/CompactSourceVarianceCoercivity.md`.
- [x] `CompactSourcePairVariance.lean`: 12 public theorems and 4 definitions.
- [x] `CompactSourceGraphCoercivity.lean`: 9 public theorems and 2 definitions.
- [x] Both final serial direct leaf checks passed with normal `.olean` outputs
  and no diagnostics; no umbrella build or heartbeat increase.
- [x] All 27 public declarations audited: only `propext`, `Classical.choice`,
  `Quot.sound`; main signatures have no analytic admission premises.
- [x] Both imports wired; all 21 theorem names present in generated API.
- [x] Repository whitespace check passed.
- [x] Formal lint run: seven unrelated concurrent modules lack umbrella imports;
  no error names either new leaf. Exact list and logs are in the fact ledger.

One connected contribution: **5/100**. No optimal coefficient, source-independent
bound, closed-operator identification or unitary affine action is claimed.
Its rough modulus successor is now certified in `rough-sobolev-modulus-nodal-defect.md`.
