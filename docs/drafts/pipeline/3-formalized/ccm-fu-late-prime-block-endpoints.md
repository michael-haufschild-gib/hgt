# CCM-FU: exact endpoint control for late-prime blocks

- **Stage:** 3-formalized
- **Type:** unconditional actual-source fibre and energy laws
- **Source:** [adaptive original-diagonal ceiling PE4](../1-in-progress/ccm-fu-adaptive-prime-ceiling.md)
- **Boundary:** PE4, PE4G, SD1 and RH remain open. No block endpoint is assumed below the original diagonal to produce an RH conclusion.

## Exact arithmetic isolation

Fix cutoff M, a processed prime set P, and an unprocessed prime p with `M<=2p` and `p<M`. The active source labels are squarefree integers below M. If p divides such a label n, then n=p: its next positive multiple is already outside the active cutoff. Therefore the only retained fibre containing p is the singleton fibre `{p}`, with coefficient `C_p(M)`. The proved all-cutoff unsigned positivity gives `C_p(M)<=0`.

Write `h_P` for the empty-cofactor fibre and `Q_P` for the complete retained energy. The literal prime merger gives

`h_(P union {p})=h_P+C_p`,
`Q_(P union {p})-Q_P=2*h_P*C_p`.

The singleton square disappears and the head square changes; all other fibres remain unchanged. These are identities for the existing arithmetic selection energy, not a surrogate scalar model.

## Complete block formula

Let L be any finite set of such late primes disjoint from P. Put `c_L=sum_(p in L)C_p` and `q_L=sum_(p in L)C_p^2`. Exact iteration yields

`h_(P union L)=h_P+c_L`,
`Q_(P union L)=Q_P+2*h_P*c_L+c_L^2-q_L`.

The head is nonincreasing as primes in L are processed. If the final head is nonnegative, the entire block contracts energy. If the initial head is nonpositive, the entire block increases energy. For an arbitrary intermediate subset R of L, split on the sign of `h_(P union R)`: nonnegative sign compares its energy to the starting endpoint; nonpositive sign compares it to the final endpoint. Thus

`Q_(P union R)<=max(Q_P,Q_(P union L))`.

This holds for every intermediate subset and hence every ordering of the block. For every real ceiling B, it gives the exact equivalence

`(forall R subset L, Q_(P union R)<=B) iff (Q_P<=B and Q_(P union L)<=B)`.

## Consequence for the live path problem

Ordering inside a consecutive late-prime block introduces no additional energy ceiling. Only its endpoints need checking. This does not determine when to insert the block among smaller-prime steps, because those steps can change multiple retained fibres and alter the head. In particular it does not justify moving all late primes to the beginning or end. The [increasing-order obstruction](../5-failed/ccm-fu-prime-pair-energy.md) and [independent-average obstruction](../5-failed/ccm-fu-bernoulli-prime-energy.md) keep their proved scope.

The remaining PE4 input is coupled control of the actual smaller-prime overlaps and intervening late-block endpoints, including the complete signed terminal energy.

## Lean audit

- `MobiusDivisorLatePrimeFibres.lean`:5 public theorems; isolated singleton fibre, prime coefficient sign, full fibre update, head update and exact energy change.
- `MobiusDivisorLatePrimeBlocks.lean`:7 public theorems; exact block head and energy formulas, head monotonicity, both sign-controlled energy comparisons, arbitrary-subset endpoint bound and ceiling equivalence.

Both leaves passed scratch checks and foreground `lake env lean <leaf> -o <exact olean>`. All12 new public theorems were axiom-audited once, with only `propext`, `Classical.choice`, and `Quot.sound`. No experimental result or added axiom enters the proof. Both leaves are wired once into `RHTower.lean`; no umbrella or dependency build was run.

Global formal lint was run once. Its errors concern three concurrent modules missing umbrella imports: `ThetaCuspEffectiveFirstAtomJets`, `ThetaCuspEffectiveLikelihoodCooling`, and `ThetaCuspEffectiveSourceApproximation`. Neither new CCM-FU leaf is flagged.
