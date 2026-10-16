# HCF: resolve the polynomial packet hidden at infinity

Status: conjecture/proof investigation.

## Starting frontier

Actual normal blocks, inertia/census, Toda multiplicities, and projective admission continuation are already proved. The previous continuation contracts degree n+k to the regular-head polynomial P_n and therefore loses k roots at infinity. The new task is to recover that missing polynomial packet structurally, without RH or positivity assumptions.

## Conjecture loop

1. Full matrix singular unfolding: determinant multiplicity alone does not identify individual eigenvalue orders. A proposed partial-multiplicity ladder needs new matrix-germ arguments; do not infer it from determinant order.
2. Exact local signature pattern: negative double-pole Toda connection should force alternating adjacent pivots near a normal block. This suggests looking at the entire polynomial flow, not stopping at a sign-count formula.
3. Weighted admission blow-up: for k<d, epsilon^(n+k) P_(n+k)(a+epsilon,z/epsilon) should continue analytically to z^n Q_(d,k)(z), where coefficient z^(k-l) of Q is choose(k,l) * (d-k).ascFactorial(l). This determines the entire escaped packet, rather than only its projective contraction.

## Paper mechanism under investigation

The corpus heat connection gives P_N'=(logDeriv Delta_N)' P_(N-1). Exact determinant order M_k=k(d-k) forces the rescaled connection value -M_k. For a coefficient with deficit l>0, meromorphic primitive cancellation gives C_(k,l)=M_k/l * C_(k-1,l-1). Its solution is choose(k,l)*(d-k).ascFactorial(l). Lower coefficients vanish at the larger blow-up scales; the leading coefficient remains one.

Search the corpus for positive rising-factorial moment representations to characterize real versus nonreal zeros of the universal packet. No numerical experiments, web, novelty audit, old research markdown, extra axioms, or heartbeat increases.

## Completion requirements

Only intrinsic positive-time/rank inputs in actual-source capstones. Focused foreground builds, one at a time; direct lake env lean audits; umbrella wiring; axiom/lint checks; cleanup. Complete source sign remains a separate open obstacle.
