# Weighted Fermi index saturation above the critical parameter

- **ID:** pm-weighted-critical-index-saturation
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** PM weighted tomography; literal alternating generators; corpus Hardy theorem
- **Statement:** For every `1/2<a<1`, the negative index of the Fermi form with weight `t^(2a-1)` and subtraction coefficient `2^(-2a)` is infinite. At `a=1/2` it is the existing canonical RH index.

## Goal

Test whether varying the source norm supplies a deformation argument for positivity. The
source constraints stay fixed, but every strictly supercritical weight admits infinitely many
critical-line directions. Smooth variation of coefficients alone cannot justify preservation
of a finite index. This theorem does not determine the canonical index or prove RH.

## Gates

- [x] 0 → 1: fixed literal source and weighted form specified
- [x] 1 → 2: complete proof below, [PROVED HERE]
- [x] 2 → 3: targeted build, direct actual-leaf audit, axiom audit, umbrella wiring
- [ ] 3 → 4: publication and exact-statement novelty audit

## Definitions

`W_a` consists of continuous functions on `(0,1]` with finite
`E_a(w)=integral_0^1 t^(2a-1)|w(t)|² dt`, orthogonal to every original alternating generator
`phi_b(t)={1/(bt)}-2{1/(2bt)}`, `b>=1`, using the original unweighted pairing.

`q_a(u,v)=integral_0^(1/2) t^(2a-1)u(t)conj(v(t))dt
-2^(-2a) integral_0^1 t^(2a-1)u(t)conj(v(t))dt`.

Its extended negative index is the supremum of all finite dimensions of families with Gram
matrix `-I`. No zero location or multiplicity enters these definitions.

## Dependency-closed proof

1. For `w_z(t)=t^(z-1)`, the weighted squared norm integrand is
   `t^(2(a+Re z-1)-1)`. It is integrable exactly when `Re z>1-a`, including failure at
   equality. Its integral on `(0,c]` is `c^(2(a+Re z-1))/(2(a+Re z-1))`.
2. Every zeta zero `rho` with `1-a<Re rho<1` therefore gives the literal witness
   `w_rho(t)=t^(conj(rho)-1)`. Orthogonality follows from the proved generator Mellin
   identity, whose source factor multiplies `zeta(rho)=0`. Spurious witnesses `g_l` with
   parameters `1+2 pi i(l+1)/log 2` remain admitted whenever `a>0`.
3. Exact power integration gives
   `q_a(g_l,w_rho)=2^(1-2a)(2^(-rho)-1/2)/(rho-(d_l+1-2a))`,
   where `d_l=2 pi i(l+1)/log 2`. Applying the same formula to two spurious modes gives
   `q_a(g_l,g_k)=0`. No inequality replaces these literal integrals.
4. For `n` distinct admitted zeros, the matrix `B_lj=q_a(g_l,w_j)` is invertible:
   its column multipliers are nonzero for `Re rho_j<1`; its two node families are injective;
   they are disjoint because `Re rho_j>1-a>1-2a`. The existing polynomial proof of Cauchy
   invertibility applies without any zeta simplicity assumption.
5. Let `Q_ij=q_a(w_i,w_j)` and `X=-(Q+I)B^(-1)/2`. The witnesses
   `v_i=w_i+sum_l X_il g_l` have Gram matrix `Q+XB+(XB)*=-I`. Weighted products are
   integrable by the squared-norm bound. For `a<1`, weighted square integrability also
   implies ordinary integrability, so finite sums preserve the original source pairings.
6. The corpus theorem `exists_riemannZeta_line_zero_dyadic` proves that every sufficiently
   high dyadic interval contains a critical-line zeta zero. Thus critical-line ordinates are
   unbounded and contain arbitrarily large finite sets of distinct zeros. When `a>1/2`,
   all these zeros meet the strict admission inequality. Step 5 constructs `-I_n` for
   every natural `n`, proving the extended index is infinite.
7. At `a=1/2`, both the weight and subtraction coefficient reduce exactly to the canonical
   PM definitions. The existing theorem identifies vanishing of that index with RH.

## Exact insight and limits

The matching subtraction coefficient preserves the full spurious neutral sector throughout
the parameter family. Even so, changing the integrability domain admits unbounded negative
dimension immediately above the critical parameter. The power energy diverges at each mode's
entry threshold. An index-preserving deformation needs a separate uniform domain estimate.

The theorem does not assert an actual jump at `a=1/2`, because the canonical index itself has
not been proved finite. The stronger weighted multiplicity equality remains on the parent
tomography card; only its distinct-zero lower construction is needed here.

## Prior research and verification

Corpus searches covered weighted Fermi indices, source positivity and Hardy critical-line
zeros. Hybrid coverage was partial, with source inventory complete and much compiler metadata
pending or stale. Candidate declarations were read directly. Public searches found classical
weighted and dilation criteria, including [Báez-Duarte's general strong criterion](https://arxiv.org/abs/math/0505453).
No global novelty claim follows from these searches.

## Log

- 2026-09-30 — closed paper proof; weighted source leaf in targeted old-mode build;
  distinct-zero signature and Hardy saturation drafts await compiler audit. RH goal remains active.

## Complete Lean certificate

`FermiNymanWeightedWitness.lean` proves the exact power admission threshold, weighted energy,
logarithmic admission, literal spurious coupling, neutrality, and finite-sum integrability.
`FermiNymanWeightedSignature.lean` proves the finite Cauchy completion and unconditionally
constructs arbitrary negative dimensions from the actual Hardy critical-line zeros.

The intrinsic capstone `RHTower.weightedWitnessNegIndex_boundary_profile` has no hypothesis
parameters. Its exact type is

```lean
(RiemannHypothesis ↔ weightedWitnessNegIndex (1 / 2) = 0) ∧
  ∀ a ∈ Set.Ioo (1 / 2) 1, weightedWitnessNegIndex a = ⊤
```

Both targeted `lake --old build +GaloisForLFunctions.RHTower.<leaf>:olean` commands passed.
Final `lake env lean GaloisForLFunctions/RHTower/<leaf>.lean` checks on both actual leaves
passed exit 0 with no diagnostics. The `/tmp` audit printed axioms for all 42 new declarations
and the Hardy dependency: only `propext`, `Classical.choice`, and `Quot.sound` occurred.
Both modules are wired into `RHTower.lean`; no full or umbrella build was run. All 42 declaration
names were searched across the owned Lean tree, with no duplicate declaration outside these leaves.

Generated indexes were refreshed. `scripts/formal_tools.py lint --check-generated` exited 1
for 14 unrelated modules unreachable from their umbrellas; neither PM leaf had a finding.
This records scoped proof verification, not a passing global workspace gate.

- 2026-09-30 — actual-leaf, axiom and wiring audits completed; promoted to Stage 3.
