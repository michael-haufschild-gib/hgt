# Route L: signed marginal stability and coherent growth

Status: formalized; scratch Lean, axiom audits, scoped final build and repository lint passed.
Date: 2026-09-11.

Module: `GaloisForLFunctions.RHTower.XiGammaSixWoldJordanSignedMarginal`.

## Mathematical target

The Green/BV-to-fixed-physical comparison is still missing. Positive prime escape
does not cover signed coherent corrections. This audit determines when such
corrections preserve the original reciprocal reporter, and tests that control
against the literal complete Frobenius source. No RH premise or new axiom occurs.

## Exact statements

For a finite edge packet `f`, define its left marginal and variation by

`m_f(p) = sum_q f(p,q)`, `V(m) = sum_p |m(p)|`.

The existing reporter factors exactly as

`E_c(f) = sum_p c(p) m_f(p)`.

For any complex marginal supported at primes at least the positive integer `B`,

`|E_(A/p)(m)| <= (|A|/B) V(m)`,

hence `B |E_(A/p)(m)| <= |A| V(m)`. No sign condition on the marginal or `A`
is needed. This bounds marginal variation, which can be smaller than the total
variation of the original edge coefficients after cancellation within a row.

More generally, let the real weights `c(p)` tend to zero outside finite prime
sets. If `V(m_n) <= M` uniformly and every coefficient `m_n(p)` tends to `m(p)`,
where the target `m` has finite support, then

`sum_p c(p) m_n(p) -> sum_p c(p) m(p)`.

The theorem is wired directly to the existing edge reporter with `c(p)=A/p`.
It does not assume convergence in the old Hilbert or one-leg graph norm. It
does not claim the same statement for arbitrary nonsummable target marginals.

For the actual complete coherent packet `R(a,S)`, put `N=|S|`. Its marginal is

`m_R(p) = N conj(a(p)) - sum_(q in S) conj(a(q))` for `p in S`, and zero outside.

Consequently:

- `m_R=0` if and only if `R(a,S)=0`.
- For `p,q in S`, `N |a(p)-a(q)| <= V(m_R)`.
- `exists M, forall finite S, V(m_R(a,S)) <= M` if and only if `a` is constant.

The last statement quantifies over the entire unscaled coherent family. It does
not exclude separately controlled or normalized source-selected families.

The normalization is also retained in a further bound:

`|S| |z (a(p)-a(q))| <= V(m_(z R(a,S)))`.

For growing finite sets, uniformly bounded marginal variation therefore forces
each retained normalized edge amplitude to tend to zero, even if the profiles
and complex scalars vary. The displayed amplitude has the same norm as the
literal conjugate right-leg coefficient. This does **not** imply that the
aggregated prime marginal or its physical readout tends to zero.

## Dependency-closed paper proofs

Factorization follows by regrouping the finite edge sum over its left-prime
fibres. The triangle inequality bounds the readout by `sum |c(p)| |m(p)|`;
on the tail, `|A/p| <= |A|/B` gives the cost estimate.

For continuity at zero, fix an error tolerance and choose a finite prime set
outside which `|c(p)|` is smaller than that tolerance divided by `2(M+1)`.
The finite head tends to zero coefficientwise. Its complementary weighted sum
is bounded by the small weight times `M`. Subtracting a finite target marginal
reduces the general statement to this case, using
`V(m_n-m) <= V(m_n)+V(m)`.

To evaluate a coherent marginal, apply the already proved finite covariance
identity to the indicator weight of one prime. Subtracting two marginals gives
`m_R(p)-m_R(q)=N conj(a(p)-a(q))`. The triangle inequality on those two coordinates
gives the variation lower bound. If the whole marginal vanishes, every profile
difference within `S` vanishes, so every edge coefficient vanishes. If `a` is
nonconstant, choose two unequal values and include those two primes in finite
sets of arbitrarily large cardinality; their lower bound rules out uniform
variation. Constant profiles give zero packets and variation zero.

Scalar multiplication commutes with the marginal, so the same two-coordinate
bound gives the normalized estimate. Divide by the positive cardinality and
compare with `M/|S|` to obtain edge vanishing along growing sets.

## Failed producer and positive survivor

Total-trace preservation does not preserve prime marginals. A fixed-anchor
coherent star shifts reciprocal readout while changing its anchor marginal.
The proposed vanishing-Hilbert-norm star sequence was not formalized here and
is not used by any theorem in this module.

The stronger proposal, uniform variation over every unscaled complete coherent
packet, fails for every nonconstant profile. Its positive survivor is the exact
growth bound and the reader continuity law for controlled marginal limits.
These identify a sufficient analytic comparison condition without asserting
that the Green/BV source satisfies it.

## Search and external transfer audit

Deep and method searches covered coherent covariance, finite-support norm
reindexing, signed variation, and vanishing-weight pairings. They reported
partial source/compiler or semantic coverage, approximately 722,000 indexed
declarations and 706,000 ready method descriptions. Generic dominated-convergence
hits lacked the needed summable majorant. The proof instead uses a finite-head
and uniformly bounded-tail argument. Source inspection verified the finite
Finsupp regrouping/filtering APIs, prime cofinite escape, and complex norm laws
against this Lean toolchain.

The corpus's `MarkedVariationDynamics` bounds coherent output by an admitted
positive mass-preserving source envelope; it does not construct that envelope
for this source. The completed physical-endpoint response modules retain a
separate signed response budget, with no proved bound usable here.

Broad arXiv terms included transport, concentration, compactness, hysteresis,
homogenization and coercivity. Recent-date searches frequently returned older
or unrelated material. [Fahli–Galichon, Optimal Transport in Economics](https://arxiv.org/abs/2609.06277), submitted 5 September 2026, sections 2.2 and
2.5.1, motivated testing a correction against its marginal constraints and dual
cost. No result from that paper is assumed in Lean or claimed to prove an
arithmetic comparison.

A subsequent deep variance query found the corpus's exact
`finite_weighted_hilbert_dispersion` and Hilbert centroid identities. The former's
source statement was read; applicability to the complete normalized star's edge
admission has not yet been checked in Lean. It is a candidate for the next norm
proof, not a dependency of this module.

## Verification

`lake env lean /tmp/route_l_signed_marginal.lean` passed the complete marginal,
continuity and coherent-classification proofs. Scratch axiom audits of the
factorization, tail cost, coherent kernel, reporter limit and coherent growth
capstones returned only `propext`, `Classical.choice`, and `Quot.sound`.
`lake env lean /tmp/route_l_signed_normalized.lean` then verified and axiom-audited
the retained-normalization extension with the same standard axioms.

The final command
`lake build GaloisForLFunctions.RHTower.XiGammaSixWoldJordanSignedMarginal`
passed. Only this module was newly built; its umbrella import is wired and no
umbrella build was run. `scripts/formal_tools.py lint` passed. All Lean checks
were foreground, sequential within this agent; no owned Lean process remains.

## Remaining proof-chain obligation

Green/BV source → agreement with fixed physical reader → zero conormal defect
→ critical-line placement → RH.

The first comparison remains open. The next source test must retain the original
diagonal/punctured-compensator coefficients and normalization while deriving a
controlled common marginal limit, or an adequate sublinear tail-variation bound.
Assigning those properties, erasing the boundary coefficient by normalization,
or replacing the physical reader with a selected zero output would not prove RH.
