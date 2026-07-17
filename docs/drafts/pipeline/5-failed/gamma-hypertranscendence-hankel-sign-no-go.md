# Gamma hypertranscendence does not force an RH-source Hankel sign violation

- **ID:** `gamma-hypertranscendence-hankel-sign-no-go`
- **Stage:** 5-failed
- **Type:** ROUTE NO-GO / FORMALIZED COUNTEREXAMPLE
- **Scientific status:** `[ROUTE FALSIFIED] [LEAN-FORMALIZED] [BRIDGE]`
- **Lean:** `formal/GaloisForLFunctions/HTGeometry/HypertranscendentalHankelPositivityNoGo.lean`
- **Statement:** Hypertranscendence of the archimedean Gamma/digamma factor cannot by itself force
  a negative Hankel quadratic in completed Xi source derivatives.

## Rejected implication

The polynomial--Gaussian Xi filter at time `t` is a Hankel quadratic in derivatives of the
completed Gaussian trace.  A proposed shortcut was:

```text
Gamma or digamma hypertranscendental
  -> its finite derivative Hankel forms cannot all be positive
  -> one completed Xi source form is negative
  -> not RiemannHypothesis.
```

The first implication is false.

## Unconditional counterexample

For `a>0`, normalize the positive-order digamma jets by

```text
m_m(a)=Re[(-1)^(m+2) digamma^(m+1)(a)/(m+1)!].
```

The existing Gamma--Bose spectral theorem proves

```text
m_m(a)=sum_(j>=0) (j+a)^(-(m+2)).
```

Thus `(m_m(a))` is the moment sequence of the infinite positive spectrum

```text
x_j=(j+a)^(-1),             w_j=(j+a)^(-2)>0.
```

Every finite Hankel matrix `(m_(r+s)(a))_(r,s<n)` is therefore positive definite, with strictly
positive determinant.  Independently, the formal Hölder theorem proves that `digamma` is
hypertranscendental.  The Lean theorem

```text
exists_hypertranscendental_hasStrictSignedJetHankelTower
```

combines these facts into one unconditional counterexample.

## Consequence for the RH-false goal

Differential transcendence is an equality obstruction; Hankel positivity is an order property.
The former does not force failure of the latter, even at every finite rank and every positive base
point.  A strict negative polynomial--Gaussian Xi trace must therefore come from the coupled
prime--Gamma completion, not from Hölder hypertranscendence of Gamma alone.

This does not retire the filtered Gaussian or reverse-Bessel source routes.  It removes only the
shortcut that tries to assign their missing sign from archimedean hypertranscendence without an
arithmetic source estimate.

## Gates

- [x] identify the proposed Hypertranscendence-to-sign implication
- [x] give a concrete hypertranscendental counterexample
- [x] prove strict finite-rank Hankel positivity at every positive base point
- [x] formalize the combined no-go theorem in Lean
- [x] retain the coupled prime--Gamma sign as the exact open source core
