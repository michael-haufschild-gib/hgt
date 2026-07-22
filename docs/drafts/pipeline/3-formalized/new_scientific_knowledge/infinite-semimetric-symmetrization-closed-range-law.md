# Infinite semimetric symmetrization and the sharp closed-range phase law

- **ID:** `infinite-semimetric-symmetrization-closed-range-law`
- **Stage:** 3-formalized
- **Type:** UNIVERSAL INFINITE-DIMENSIONAL OPERATOR THEOREM
- **Scientific status:** `[UNCONDITIONALLY PROVED IN LEAN]`
  `[EXTERNAL NOVELTY UNVERIFIED] [CCM SUPPORT THEOREM] [NOT AN RH PROOF]`
- **Formal module:**
  `formal/GaloisForLFunctions/RHTower/InfiniteSemimetricSymmetrization.lean`
- **Manuscript:** `docs/drafts/manuscripts/ccm-boundary-channel-completion/main.tex`

## Universal theorem

Let `H` be an arbitrary real Hilbert space. No finite-dimensional or finite-rank parameter occurs.

For every bounded operator `T`, Lean constructs the canonical algebraic equivalence

```text
(ker T)^perp  ~=  range T,
x             |-> T x.
```

Its inverse is exact on `range T` and selects the unique preimage orthogonal to `ker T`. This holds
whether or not the range is closed.

For bounded self-adjoint `T`, define symmetric support-inverse data `(G,P)` by

```text
G*=G,  P*=P,  P^2=P,
T G=G T=P,
T P=P T=T,
P G=G.
```

Lean proves the sharp topological phase law

```text
range T is closed  <->  Nonempty (SymmetricSupportInverse T).
```

The data, when it exists, is unique.

For arbitrary bounded `D`, define

```text
S_T(D) = (1/2) (P D P + G D* T).
```

Lean proves

```text
T S_T(D) = S_T(D)* T,
P S_T(D) = S_T(D) = S_T(D) P,
S_T(D) (ker T) = 0,
S_T(S_T(D)) = S_T(D),

S_T(D)=D
  <-> P D=D=D P and T D=D* T.
```

Thus `S_T` is the canonical idempotent retraction onto supported `T`-self-adjoint bounded
operators. Defect rank and radical dimension are unrestricted.

## Sharp infinite obstruction

The nonclosed-range phase is included in the theorem, not excluded by assumption. If `T=T*` and
`range T` is nonclosed, Lean proves `IsEmpty (SymmetricSupportInverse T)`. The algebraic range
inverse still exists, but no bounded symmetric support inverse exists.

This is the correct infinite distinction hidden by every finite matrix: finite range is always
closed, while cofinal small singular values can force a nonclosed range in the limit.

## CCM relation

The previously formalized finite rank-two boundary-channel trichotomy is now classified as a
sparse specialization, not the universal law:

- `CCMBoundaryChannelCompletion.lean` gives explicit rank-one corrections for the two active
  channels and the neutral channel;
- `CCMDividedDifferenceInstantiation.lean` discharges the finite divided-difference/reflection
  premises;
- `InfiniteSemimetricSymmetrization.lean` supplies the arbitrary-rank infinite topology and the
  exact bounded/nonbounded phase boundary.

The theorem does not assert that the actual unbounded CCM Weil clock fits the bounded `D` carrier,
that its weight has closed range, or that the nonclosed branch has the required graph-domain
Feshbach completion. Those are the remaining source-specific tasks.

## Claim-to-Lean closure

| Claim | Declaration |
|---|---|
| algebraic support--range equivalence | `algebraicSupportRangeEquiv` |
| exact inverse laws | `algebraicSupportRangeEquiv_symm_rightInverse`, `algebraicSupportRangeEquiv_symm_leftInverse` |
| closed range gives support inverse | `exists_symmetricSupportInverse_of_isClosed_range` |
| exact closed-range phase | `isClosed_range_iff_nonempty_symmetricSupportInverse` |
| support/inverse uniqueness | `symmetricSupportInverse_support_unique`, `symmetricSupportInverse_inverse_unique` |
| canonical data | `symmetricSupportInverse_unique`, `symmetricSupportInverse_subsingleton` |
| metric symmetrization | `infiniteSemimetricSymmetrization_metricAdjoint` |
| support law | `infiniteSemimetricSymmetrization_support` |
| radical annihilation | `infiniteSemimetricSymmetrization_apply_eq_zero_of_mem_ker` |
| idempotence | `infiniteSemimetricSymmetrization_idempotent` |
| fixed-point classification | `infiniteSemimetricSymmetrization_fixed_iff` |
| nonclosed obstruction | `no_symmetricSupportInverse_of_not_isClosed_range` |

## Novelty audit

Moore--Penrose inverse and closed-range equivalences are classical. Targeted primary-source search
found extensive weighted Moore--Penrose theory, so no priority claim is made for those ingredients
individually. No exact match was found for the specific canonical retraction

```text
D |-> (1/2)(PDP + T^dagger D* T)
```

with its fixed-point classification and CCM completion interpretation. External priority remains
unverified. Paper significance must rest on the full phase/retraction law and CCM boundary, not on
rediscovery of Moore--Penrose existence.

## Gates

- [x] arbitrary Hilbert space carrier
- [x] no finite-rank restriction
- [x] algebraic inverse in both topological phases
- [x] sharp closed-range equivalence
- [x] uniqueness/canonicity
- [x] metric-adjoint symmetrizer
- [x] support and radical laws
- [x] idempotent/fixed-point classification
- [x] all mathematical claims formalized in Lean
- [ ] independent operator-theory audit
- [ ] external priority audit of exact retraction formula
- [x] abstract unbounded graph-domain extension (`infinite-semimetric-graph-inverse-incidence-law.md`)
- [ ] actual CCM Weil-form connector
- [ ] divisor-preserving cofinal transfer

## Log

- 2026-07-22 -- Rejected finite rank-two theorem as paper headline.
- 2026-07-22 -- Derived and formalized arbitrary-rank infinite semimetric symmetrizer.
- 2026-07-22 -- Proved algebraic support--range inverse exists without closed range.
- 2026-07-22 -- Proved bounded symmetric support inverse exists iff range is closed.
- 2026-07-22 -- Proved uniqueness, radical annihilation, idempotence, and fixed-point law.
- 2026-07-22 -- Extended nonclosed branch to canonical closed partial inverse and exact incidence
  symmetrizer; see child card.
