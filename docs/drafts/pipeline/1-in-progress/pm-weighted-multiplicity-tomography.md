# Weighted multiplicity tomography of the physical Fermi witness form

- **ID:** pm-weighted-multiplicity-tomography
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** Route PM; exact unweighted index and general Mellin-exponent removability
- **Statement:** For each intrinsic parameter `0<a<1`, the negative index of the literal weighted dyadic form equals total analytic multiplicity of zeta zeros with `1-a<Re rho<1`.
- **Novelty:** Scoped corpus/public searches found general zero-free-strip and `L^p` receivers but no matching weighted multiplicity index; global novelty unverified.

## Goal

Turn the canonical PM index into a source-based multiplicity profile across vertical thresholds.
At `a=1/2` recover the exact RH obstruction. Identify the regularity wall without assuming a
zero-location theorem. This remains a receiver until an independent weighted source bound exists.

## Gates

- [x] 0 → 1: source-pure definitions and mechanism specified
- [ ] 1 → 2: audit all analytic and weighted source obligations below
- [ ] 2 → 3: actual-leaf Lean audit and axiom audit
- [ ] 3 → 4: standalone publication and completed novelty review

## Exact proposed definitions

`W_a` consists of continuous complex functions on `(0,1]`, orthogonal to every actual generator
`phi_b`, `b≥1`, and with finite weighted squared norm

`E_a(w)=integral_0^1 t^(2a-1) |w(t)|² dt`.

`q_a(u,v)=integral_0^(1/2) t^(2a-1) u conj(v) - 2^(-2a) integral_0^1 t^(2a-1) u conj(v)`.

Let `M_a` be the extended supremum of finite analytic-multiplicity sums over actual zeta zeros
with `1-a<Re rho<1`. Conjecture: `ind_-(q_a|W_a)=M_a`, without RH, simplicity or finite-zero premises.

## Mechanism to audit

1. Weighted Cauchy–Schwarz gives Mellin exponent `a` and the boundary estimate
   `witnessMajorant(w,x) ≤ sqrt(E_a(w))/sqrt(2(x-a))`, `x>a`. It also gives ordinary `L¹`
   because `a<1`. Thus the actual correlation remains analytic for `Re s>0`.
2. Every zero jet `t^(conj(rho)-1) log^j(t)`, `j<ord_rho(zeta)`, belongs to `W_a` exactly on
   the required strict integrability side `Re rho>1-a`. Source orthogonality is the same literal
   derivative identity already proved; weighted integrability is a separate obligation.
3. Spurious witnesses remain admitted for every `a>0` and are neutral for `q_a`. Direct power
   integration gives the normalized coupling denominator at the shifted spurious node
   `d_l+1-2a` and numerator `2^(1-2a)c(rho)`, where `c(rho)=2^(-rho)-1/2`.
   Shifted nodes have real part `1-2a`, strictly below every admitted zero `Re rho>1-a`.
4. Divide the logarithmic jet normalization by this numerator. Existing confluent Cauchy
   controllability and the same Hermitian graph completion should produce both signed blocks
   with one slot per multiplicity.
5. Zero correlation jets at all admitted zeros clear all possible left-defect poles in
   `Re z<a`. The already proved general removability theorem, with the estimate in step 1,
   should force self-similarity. The weighted form then vanishes by change of variable.
6. Negative families therefore inject into the admitted multiplicity coordinates. The finite/
   infinite counting split is the same intrinsic argument as in the canonical index theorem.

## Critique and boundaries

- The weight and subtraction coefficient must move together; keeping coefficient `1/2` would
  destroy spurious neutrality and would test a different object.
- For `a>1/2`, admitted zero jets need not be ordinary `L²` witnesses. Do not reuse ordinary
  witness membership there; use the literal source pairing and weighted integrability separately.
- At `a=0`, spurious modes leave the weighted space; that endpoint is not covered by this formula.
- Infinite critical-line zero input for a proposed `a>1/2` index cliff is under corpus search;
  no such corollary is claimed yet.
- An exact index profile does not supply the source nonnegative-half-mass bound needed for RH.

## Prior research

Corpus query `weighted Fermi multiplicity negative index zero free strip --any --module FermiNyman`
reported `partial: true`. Hits include `no_zeta_zero_of_fermiNymanWitnessLp_selfSimilar`,
`zetaZeroFreeStrip_iff_mellinFermiWitness_selfSimilar`, general removability, and the new canonical
index. No weighted multiplicity theorem surfaced. Public weighted-Nyman/negative-index/inertia
queries found no exact match; absence is not certified.

## Log

- 2026-09-29 — created; no weighted Lean implementation started. Current rank/kernel/source-classification audits take priority.
