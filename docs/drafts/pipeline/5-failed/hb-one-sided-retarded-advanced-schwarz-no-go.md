# HB one-sided retarded/advanced Schwarz no-go

- **ID:** HB-ONE-SIDED-CAUSAL-001
- **Stage:** 5-failed
- **Type:** THEOREM / ROUTE-KILL (Lean)
- **Source:** corpus definitions of the target-independent full-cokernel realization and physical retarded/advanced Schwarz exchange
- **Statement:** Any retarded/advanced pair with one response identically zero satisfies causal Schwarz exchange only when the other response is also zero. Consequently the canonical target-independent full-cokernel BM split `(Gret,Gadv)=(hbXiPeierlsPropagator n,0)` is never a physical Schwarz-exchanged causal split.

## RH chain being tested

`shared canonical HB/FZZ-P/PW-B/RBH ++- cokernel cut → physical retarded/advanced realization → opposite-sign passivity → universal cut extinction → RH`.

The current canonical realization declares the global BM propagator retarded and the advanced map
zero. Physical Schwarz transport must exchange the two causal orientations. If this architecture is
incompatible with that exchange, it cannot supply the missing HB producer; only a genuinely
two-sided response split survives.

## Corpus-derived conjecture

For arbitrary global complex-linear `G`, prove

`HBXiPeierlsRetardedToAdvancedSchwarzExchange G 0 ↔ G = 0`

and its reversed counterpart. Apply this classification to `hbXiPeierlsPropagator n`. Corpus
already proves its radial weight has nonzero imaginary part at every Xi copy and its induced
propagator is not channel-Schwarz odd. Therefore it is nonzero and cannot obey the one-sided
exchange law.

## Gates

- [x] 0 → 1: exact architecture, RH chain, and contradiction mechanism frozen
- [x] 1 → 2: paper proof and positive survivor complete
- [x] 2 → 3: Lean theorem, targeted build, axiom audit, umbrella wiring

## Proof `[PROVED HERE]`

Write `S` for involutive channel-Schwarz transport. If `(G,0)` obeys retarded-to-advanced
Schwarz exchange, then `S(G f)=0` for every carrier vector `f`. Apply `S` and use `S²=id` and
`S(0)=0`; hence `G f=0`, and extensionality gives `G=0`. Conversely zero pair obeys exchange.
Replacing `f` by `S f` proves reversed statement `exchange(0,G) ↔ G=0`. Green reciprocity is
automatic for zero pair, so adjoining it creates no exception.

Canonical target-independent full-cokernel construction uses
`(Gret,Gadv)=(hbXiPeierlsPropagator n,0)`. If this pair obeyed exchange, classification would force
canonical propagator to be zero. A zero propagator is channel-Schwarz odd. Corpus proves canonical
radial propagator is not channel-Schwarz odd, witnessed at every Xi copy by nonzero imaginary part
of its Green-jump weight. Contradiction.

## Lean certificate

Module:
`GaloisForLFunctions.RHTower.ThetaCuspHawkingOneSidedRetardedAdvancedSchwarzNoGo`

Principal declarations:

- `hbXiPeierlsRetardedToAdvancedSchwarzExchange_zero_advanced_iff`;
- `hbXiPeierlsRetardedToAdvancedSchwarzExchange_zero_retarded_iff`;
- `hbXiPeierlsOneSidedZeroAdvancedMinimalPhysical_iff`;
- `hbXiPeierlsOneSidedZeroRetardedMinimalPhysical_iff`;
- `hbXiPeierlsCanonicalFullCokernelOneSidedSplit_not_schwarzExchange`;
- `hbXiPeierlsCanonicalFullCokernelOneSidedSplit_not_minimallyPhysical`.

Audit, 2026-08-30:

- direct `lake env lean`: PASS;
- targeted module `lake build`: PASS;
- `#print axioms`: only `propext`, `Classical.choice`, `Quot.sound`;
- wired into `GaloisForLFunctions.RHTower` umbrella;
- corpus research index returns exact new unilateral classification and canonical no-go.

## Positive survivor required by no-go discipline

Balanced two-sided half-jumps `(Delta/2,-Delta/2)` survive precisely when `Delta` is Peierls-skew
and channel-Schwarz odd. Existing corpus classification supplies this survivor, but universal unit
BM incidence for such a physical pair is already equivalent to RH. Thus the one-sided canonical
model cannot be upgraded into an unconditional producer by relabelling its causal orientation.

## No-go closure

- **Exact killing theorem/mechanism:** involutivity of channel Schwarz forces every unilateral
  exchanged causal pair to be zero pair; canonical BM propagator is provably nonzero via its
  failure of channel-Schwarz oddness.
- **Strongest positive survivor:** genuinely two-sided reciprocal half-jumps
  `(Delta/2,-Delta/2)` for Peierls-skew, channel-Schwarz-odd `Delta`.
- **New insight:** setting advanced response to zero is not a harmless causal convention. It
  destroys physical Schwarz exchange for every nonzero retarded response, independently of
  locality, support, target fitting, diagonal form, or passivity.
- **Survivor status:** dependency-closed and Lean-formalized in imported retarded/advanced
  classification; universal literal unit BM incidence in this survivor class is RH-equivalent,
  not an unconditional producer.
- **Route status:** shared canonical target-independent one-sided full-cokernel producer for
  HB/FZZ-P/PW-B/RBH RETIRED. This does not retire genuinely two-sided source-derived versions of
  those routes.

## Log

- 2026-08-30 — conjectured from corpus after hostile audit of the canonical full-cokernel model.
- 2026-08-30 — unilateral architecture killed, positive two-sided survivor classified, Lean audit
  passed, card moved to failed/retired.
