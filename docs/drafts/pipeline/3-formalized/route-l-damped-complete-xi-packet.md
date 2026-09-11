# Route L: same damped source in the complete Xi packet

- **ID:** L-C46
- **Date:** 2026-09-11
- **Stage:** 3-formalized
- **Type:** complete divisor packet / original Green–Tate–Sonin transport
- **Depends on:** [C44 weighted source](../3-formalized/route-l-damped-weighted-source-boundary.md); [C45 literal Mellin jets](../3-formalized/route-l-damped-full-mellin-jets.md)
- **RH status:** unproved

Chain: complete original Green/BV source → fixed physical-reader agreement
→ conormal vanishing → RH. The complete original divisor field and its full Xi-indexed Gamma graph
family are now closed in Lean, retaining every multiplicity copy. The leaf
module `DeningerDampedCompleteXiPacket` is wired into the umbrella and its
final leaf audit passed. Pointwise Mellin derivatives alone were insufficient: the
new proof supplies a summable bound in the full Hilbert norm.

## Complete-field proof

Fix a>1. Put w_p=p^(-a). The actual factor in the corpus is

`A_p(s)=(1-w_p exp(-log(p)*s))*(1-w_p exp(-log(p)*(1-s)))`.

For every s in the full closed unit strip, both exponential norms are at
most one. Thus `|A_p(s)| <= (1+w_p)^2 <= exp(2*w_p)` and, by expanding
`A_p-1`, `|A_p(s)-1| <= 2*w_p+w_p^2 <= 3*w_p`. Here `0<w_p<1`.
The sum of w_p over the original primes is finite, by comparison with the
ordinary p-series; no critical-line placement is used.

For the actual prime prefix P_N let A_N be its product. Then, uniformly in
s throughout the closed strip,

`|A_N(s)| <= C_a := exp(2*sum_p w_p)`.

If N<M, telescope the successive products. Every intermediate prefix is
bounded by C_a, giving

`|A_M(s)-A_N(s)| <= 3*C_a*sum_(N<p<=M) w_p`.

Let G be the original reflected-Gaussian full divisor field, already in
`XiDivisorL2`. Each entry is an actual Gaussian Mellin evaluation; the
index is the native `XiZeroCopy` sigma type, including all multiplicities.
The fields `F_N(q)=A_N(rho_q)*G(q)` consequently obey

`||F_M-F_N||_2 <= 3*C_a*||G||_2*sum_(N<p<=M) w_p`.

They form a Cauchy sequence in the existing unquotiented Hilbert space.
Coordinate evaluation is continuous. Comparing its limit with C44's
literal Mellin convergence identifies the completed field entry with
`M(g_a)(rho_q)`. C44 proves each of these entries nonzero. Reflection of
the actual Euler factors must pass through this same identified field.
The uniform estimate is valid for fixed a>1; it is not an endpoint bound
at a=1 and not a zero-damping theorem.

## Original Green, Tate and full graph transport

The completed Green primitive is `-Green(F)` in the existing Hilbert space;
`Green²=-id` proves that it resolves F. Continuity also transports the
actual finite-source Green primitives to this limit. The original
provenance map and Gamma residue packet retain the same coefficients.
The exact source multiplier is
`U_a(s)=1/(zeta(a+s)*zeta(a+1-s))`, identified only after source convergence.
At every actual Xi copy it is nonzero and satisfies `U_a(1-s)=U_a(s)`.
Consequently both Green primitive and original provenance equal the
Gaussian versions multiplied by U_a at that copy.

For every original prime p, Xi copy q and native Tate depth n, the chain
is the original prime cycle atom tensor the original averaging packet,
scaled by the actual provenance coefficient. Its completed differential
converges to that coefficient times the original singular graph vector.
The stronger conclusion retains all Xi copies simultaneously:
`x ↦ (q ↦ x(q) • v)` has norm at most `||x||₂*||v||`, so the constructed
chains converge in `lp (fun _ : XiZeroCopy => OriginalGammaGraph) 2`.
This is convergence in the full graph norm, not merely coordinatewise.

Both finite-depth and completed physical images equal U_a times the
original Gaussian physical image. Therefore the new physical image is
zero exactly when `Re(rho)=1/2`. This is an exact classification preserving
the fixed reader; it does not prove that any such image is zero.
The full Green/BV source-to-physical comparison remains open.

C44 already proves that g_2 has nonzero coefficients on every original
prime circle. Full packet convergence must retain that boundary and the
fixed physical reader. It cannot by itself supply their cancellation.

## Corpus evidence

`/tmp/route_l_c46_uniform_packet_deep.json` is terminal; all 20 candidates,
20 source arguments (including proof excerpts) and the proposed ingredient
group were inspected. Query:

`scripts/formal_tools.py research 'uniform infinite product summable norm perturbation bounded multiplier dominated L2 convergence' --mode deep --any --budget-seconds 120 --json`

Report index generation 876111; inventory snapshot generation 876120:
56944/56944 files inventoried, 47346 Lean files, 9598 prose files. Semantic
coverage was not measured because of the reporting budget. Text retrieval,
source retrieval and reranking are partial. Many compiler entries are
pending/source-only; candidate applicability must be checked in scratch.

The generated ingredient group proposes bounded diagonal multiplication in
ell-two; its explicit unresolved obligation is the uniform multiplier
bound, proved on paper above. It is not an automatic proof certificate.
`HTGeometry.memℓp_ellTwoDiagonal` and
`HTGeometry.norm_ellTwoDiagonalLinearMap_le` were read in full: they work
with an arbitrary index, suitable for native Xi copies.
`MeasureTheory.tendsto_lpBoundedMulCLM_apply` was also read: it needs one
uniform bound and pointwise convergence and proves strong convergence on
a fixed vector. Its measurable Lp carrier differs from the current lp
carrier; use the direct discrete Cauchy estimate unless a verified
carrier equivalence makes transfer simpler.

The method `norm_tprod_one_add_sub_one_le` gives an exact exponential
product-tail bound from summable perturbations. The direct finite-prefix
telescope above suffices and preserves the original prime order.

## Stronger original-domain test: all L1 corrections

The next search tested whether the infinite-prime common-Green obstruction
needs all-weight Meyer decay. Report
`/tmp/route_l_c46_common_green_L1_deep.json` is terminal, generation 876146;
semantic coverage was not measured (reporting budget). Text retrieval,
source retrieval and decomposition were partial. All 20 candidates and
20 source arguments and the proposed ingredient group were inspected.

**Conjecture.** An integrable source whose original periodizations vanish
almost everywhere for an unbounded sequence of positive periods is zero
almost everywhere. Therefore no nonzero integrable source can have an
integrable original translation primitive at every prime.

The existing `deningerCofinalTomography` requires exponential Schwartz
decay and uses only one harmonic plus the analytic identity theorem. Its
premise cannot be transferred to arbitrary L1 sources. The proposed L1
replacement uses all harmonics: the actual L1 periodization coefficient
law gives `Fourier(f)(k/L_n)=0` for every integer k. For each real frequency
w choose an integer k_n with `|k_n-w*L_n|<=1`, so `k_n/L_n -> w` when
`L_n -> infinity`. Continuity of the L1 Fourier transform then gives zero
at every w; Fourier uniqueness gives `f=0` almost everywhere. The original
translation-coboundary consequence still requires its exact Fourier
character identity (or an AE periodization telescoping proof).

The positive survivor would be a complete injectivity/classification law
for all original prime-circle observations on L1, extending the current
Meyer theorem. This is a paper mechanism under verification, not a new
Lean theorem and not a retirement of Route L. It would require a non-L1
source or a proved change of original Green domain for a nonzero
simultaneous cancellation; it does not rule out such a singular source.


## Additional corpus and boundary-method audit

`route_l_c46_packet_cauchy_deep.json` returned 20 candidate lemmas and 20
source arguments; all were inspected. Generation 876248; semantic coverage
not measured (reporting budget), with partial text/source and several
iterative queries. The useful direct theorem is
`cauchySeq_of_dist_le_of_summable`. The proposed ingredient group only gave
Cauchy boundedness and did not prove the required summability. The actual
proof establishes the step majorant first. The bounded vector-diagonal
method suggested the full Gamma graph spread; its source and the exact
`lp.norm_mono` and `lp.evalCLM` APIs were read and checked in scratch.

`route_l_c46_boundary_gluing_deep.json` returned 20 candidates and 20 source
arguments, all inspected. Generation 876316; inventory snapshot 876319 has
56949/56949 files; semantic coverage not measured. Text/source retrieval
and decomposition are partial. Its proposed group combines a different
kernel's Cauchy–Green rectangle identity with a chamber-restricted
homogeneous ODE derivative theorem. Reading both proof bodies exposes the
missing kernel/domain and derivative identifications. It does not supply
the original degree-six physical-reader comparison. A cyclic descent
proposition appearing as a method is an existential requirement, not its
producer. No proposed group was treated as a proof certificate.

Broad arXiv `gluing` search found Shengquan Xiang,
[Controlled harmonic map heat flow and blow-up from the disk to the sphere](https://arxiv.org/abs/2609.10129),
submitted 9 September 2026. Lemma A.11's proof and the barrier construction
retain the interface derivative jump in the weighted weak Green identity.
Matching values does not cancel that term; its sign gives a subsolution or
supersolution inequality. This suggests tracking the entire source jump,
but supplies neither a Route L energy class nor a vanishing jump. No such
PDE premise is transferred.

The next domain attack is recorded separately in
[original-circle injectivity on L1](../1-in-progress/route-l-l1-original-circle-injectivity.md).
The L1 conjecture above remains a proposed extension, not a C46 theorem.


## Lean validation

`lake env lean /tmp/route_l_c46_packet.lean` check3 passed without diagnostics.
The final `lake build GaloisForLFunctions.RHTower.DeningerDampedCompleteXiPacket`
audit passed; only the new leaf was built (272 seconds), with other graph
results replayed. The 457-line module is wired once into `RHTower.lean`.
No full/umbrella build, numerical experiment or axiom-print command was used.

Principal results:

- `deningerDampedPairedMultiplier_strip_bounds`
- `deningerDampedXiPrefix_cauchy`, `_tendsto`, `_error_bound`
- `deningerDampedXiField_apply`, `_apply_ne_zero`, `_factor`, `_reflect`
- `deningerDampedXiGreenPrimitive_resolves`, `_tendsto`, `_factor`
- `deningerDampedXiField_original_residue_normalization`
- `deningerDampedXiGreenProvenance_factor`
- `tendsto_deningerDampedXi_chain`
- `deningerDampedXi_finite_physical_readout`, `_completed_physical_readout`
- `deningerDampedXi_physical_readout_eq_zero_iff_criticalLine`
- `deningerDampedXiFullTateGraphPrefix_apply`, `_tendsto`

Logs: `/tmp/route_l_c46_packet_check3.log`,
`/tmp/route_l_c46_packet_build.log`. `scripts/formal_tools.py index` completed. Of 45 public declarations,
43 appear in `formal/LEAN_API.md`; the two one-line `@[simp] theorem`
declarations are absent from that generated API. Both are nevertheless present in the search index: separate exact lexical
queries retrieve `deningerDampedXiPrefix_apply` and
`deningerDampedXiFullGraphBoundary_apply`, each with one correct hit. The
API omission is not an omission from corpus search. Targeted diff check passes.
Formal lint subsequently passed in `/tmp/route_l_c47_l1_circle_lint.log`.
The earlier `/tmp/route_l_c46_packet_lint.log` failed while three concurrent
modules lacked umbrella imports; those imports are now present. C46's
own import was present throughout.
