# Finite quantum expectation graph rate–distortion law

- **Status:** Lean-formalized
- **Formal module:** `formal/GaloisForLFunctions/RHTower/FiniteQuantumExpectationGraphRateDistortionLaw.lean`
- **Headline theorem:** `exists_finiteQuantumExpectation_graph_rateDistortion`

## Exact result

Every finite family of scalar expectation histories

\[
f_a(t)-f_a(0)
=\sum_{i,j}c_{a,ij}\left(e^{it(E_i-E_j)}-1\right)
\]

obeys the following deterministic law for every chosen synchronization graph
\(G\) and every \(Q\in\mathbb N\). Some positive integer \(n\) satisfies

\[
n\le (Q+1)^{d-\#\pi_0(G)}
\]

and

\[
\sum_a\lambda_a|f_a(n)-f_a(0)|
\le
2M^{(1)}_{\rm omit}(G)
+2\frac{2\pi}{Q+1}M^{(1)}_{\rm select}(G).
\]

The coefficient masses are weighted \(\ell^1\) masses. The proof permits
equal Bohr gaps and arbitrary cancellation. The abstract coefficient
\(c_{a,ij}\) is formally identified with
\(\rho_{a,ij}A_{a,ji}\), and the scalar displacement is proved equal to

\[
\operatorname{tr}(\rho_a(t)A_a)-\operatorname{tr}(\rho_aA_a)
\]

in the energy basis.

## Truth boundary

- The coefficient-mass expression is a cancellation-resistant upper bound,
  not the exact frequency module of a scalar history.
- Exact visible scalar frequencies must be grouped by equal Bohr gap; their
  grouped coefficients can cancel.
- \(d-\#\pi_0(G)\) is a universal synchronization-capacity exponent, not the
  exact Diophantine exponent of every energy list.
- The theorem is finite-dimensional and stroboscopic. A separate post-exit
  theorem is required before calling the event a non-vacuous recurrence.

## Novelty status

`[NOVELTY UNVERIFIED]`. State/observable-dependent gap weights and finite-time
gap concentration have literature antecedents. Candidate novelty is the
chosen-graph rate–distortion deadline for arbitrary simultaneous scalar
expectation histories, especially once composed with a certified post-exit
return. This requires a dedicated external audit.

## Verification

Direct foreground compilation passed with

```text
lake env lean GaloisForLFunctions/RHTower/FiniteQuantumExpectationGraphRateDistortionLaw.lean
```
