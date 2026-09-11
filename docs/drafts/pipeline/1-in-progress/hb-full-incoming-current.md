# HB: full incoming wave-image current

Status: [ten theorems formalized](../3-formalized/hb-full-incoming-current.md). RH and the complete physical pairing remain unproved.

Chain: literal theta-cusp source → Xi occurrence → retained spin-two source → physical causal radial/left-QNM action → fixed Hawking-clock extinction → RH.

Hard target: cancellation of the complete physical mixed coefficient, with the original onset pulse and every boundary face retained. The already formalized source decomposition gives the wave-image stream

`Psi_s = a²(1+1/r)^(2s) chi(v) exp(2sv) [coexact H_s - s(s-1)/(4r²) coexact Q]`.

Here `H_s` is the constructed full angular response, not only its principal cusp terms. The existing physical lift-current theorem covers only the second summand. The formal module derives the full current, including its cross terms and two angular components, from the original Einstein-action theorem. It evaluates the original horizon limit and finite fixed-clock coefficients. The pulse response and its cross terms remain part of the extinction problem.

Conjecture loop: a shared source producer suggested transpose cancellation; its measure-dependent extra term and the full onset pulse remain. The next test keeps both angular response profiles in the actual current. A zero from a common angular covector cannot be reused for two distinct profiles.

## Analytical full-current evaluation

Let `s=physicalRate q true`, `t=-s-3`, and `c=a²b²/64`. All products below are complex bilinear covector products; no conjugation is inserted. The normalized trace and normal covectors are

```
U_s = coexact H_s - k_s coexact Q,
N_s = -s coexact H_s + k_s(s+2) coexact Q,
k_s = s(s-1)/4.
```

Put `A=N_s dot N_t`, `X=U_t dot N_s`, `Y=U_s dot N_t`. Define the two-component angular Green current by

```
G(P,Q) = y² (P_Y curl Q-Q_Y curl P, -P_X curl Q+Q_X curl P).
```

Set `G1=G(N_s,U_t)`, `G2=G(U_s,N_t)`. The complete horizon current is `C0 e^(-6v) chi² + C1 e^(-6v) chi chi' + C2 e^(-6v) (chi')²`, where the four rows are

| Component | C0 | C1 | C2 |
|---|---|---|---|
| v | `4c[(s-t)A+tX-sY]` | `2c(X-Y)` | `0` |
| r | `4c[t(2s+1)X-s(2t+1)Y]` | `-10c(X-Y)` | `2c(X-Y)` |
| angular | `-2c(t G1+s G2)` | `-c(G1+G2)` | `0` |

This follows from the exact static Einstein current after the ingoing coordinate transformation. Its regular orbital master is `r²(r²-1)Psi_rr+r²(Psi_vr+Psi_rv)+2r Psi_r-2r Psi_v`. The second pure radial derivative disappears only when evaluating the horizon; the angular mixed terms remain.

For every finite clock endpoint `V`, each component integrates to `C0 M+C1(3M+B/2)+C2 E`, with `M=integral_0^V e^(-6v)chi²`, `E=integral_0^V e^(-6v)(chi')²`, and `B=e^(-6V)chi(V)²`. This is a full incoming wave-image expression, not extinction of the full causal response. The onset-pulse response, its cross terms, and the other physical faces still need their signed comparison.

## Search and external ideas

Own broad corpus searches: `onset`, `intertwining`, `reciprocity`; mechanism searches: causal Green transfer of a wave image and transition pulse, and recovery from zero characteristic data. Source-method sections were inspected. Results were partial and mostly source-only; no proposed ingredient set supplied the missing physical cancellation. Existing exact source decomposition and full-action current were reused directly.

Broad arXiv discovery included [Reciprocity can halve what a mechanical network can learn](https://arxiv.org/abs/2609.04169) (3 September 2026), [Revival of transport reciprocity via quantum interference](https://arxiv.org/abs/2607.26898) (29 July 2026), [Exact statistical transmutation of quantum mixtures on a ring](https://arxiv.org/abs/2608.05290) (5 August 2026), and [Transmutation based Quantum Simulation for Non-unitary Dynamics](https://arxiv.org/abs/2601.03616) (7 January 2026). The first paper's transpose comparison prompted the source-space reciprocity test. None supplies or is used as a proof of the physical causal cancellation here. No numerical experiment was run.

Search coverage was generation 823349, with 523 pending/stale files reported by the broad cached query. Generated ingredient groups remained unverified; applicability was established only for the declarations used by the new Lean proofs.
