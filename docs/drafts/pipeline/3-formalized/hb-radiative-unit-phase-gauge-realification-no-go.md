# HB radiative unit-phase gauge realification no-go

- **ID:** HC91
- **Stage:** 3-formalized
- **Type:** CONJECTURE / REFLECTION-REALITY GAUGE NO-GO
- **Source:** read-only `rh-current-frontier-map.md` · HC89 actual radiative FE transport · HC90 positive Hermitian metric

## Goal

Attack sharp survivor after HC90: perhaps positivity is too weak, but requiring a real
functional-equation transport coefficient selects the critical line. Determine whether reality is
invariant under physically harmless diagonal phase normalization.

Use actual nonlinear BM raw Ward amplitude `P(q)`, actual Green-dressed radiative cocycle `κrad`,
and full finite Xi packets. Construct a unit-modulus phase gauge from polar decomposition of `P`
and decide whether it makes radiative transport positive-real at every off-line copy. A positive
construction kills reflection-reality unless phase reference is fixed independently of source.

## Gates

- [x] 0 → 1 in-progress: corpus audit; exact conjecture frozen
- [x] 1 → 2 fully-proven: dependency-closed paper proof and bounded primary-literature audit
- [x] 2 → 3 formalized: unconditional Lean theorem, targeted build, axiom and lint audit
- [ ] 3 → 4 publication-ready: independent mathematical/physical review and broader novelty search

## Corpus audit

- `[CORPUS]` HC89 proves exact actual-amplitude transport
  `κrad(q) conj(P(q)) = P(Rq)`, cocycle involution, and nonzero bright cancellation off line.
- `[CORPUS]` HC90 lifts `κrad` to finite packets and constructs positive-definite antiunitary
  geometry plus positive orbit weights.
- `[CORPUS]` HC60 constructs a generally nonunitary literal-source amplitude gauge trivializing
  the undressed source cocycle; source-fixed real trivialization remains equivalent to RH.
- `[CORPUS]` existing packet classification shows reflection-real nonzero weights plus a fixed
  complex-bilinear Ward law imply RH.
- `[CORPUS NEGATIVE]` mandatory searches found no unit-modulus gauge made from actual radiative BM
  amplitude, no exact positive realification of `κrad`, and no full-packet conjugated transport law
  showing reflection-reality is phase-gauge dependent off line.

## Conjecture HC91-A: actual raw-amplitude phase gauge

Let

`bphase(q) = 1` when `P(q)=0`, and `P(q)/‖P(q)‖` otherwise.

Prove globally that `bphase(q) ≠ 0`, `‖bphase(q)‖=1`, and

`bphase(q) · ‖P(q)‖ = P(q)`.

Thus gauge is exact polar phase of actual raw physical amplitude, not arbitrary orbit choice.

## Conjecture HC91-B: positive realification of radiative FE

For anti-linear diagonal gauge define

`κrad^b(q) = b(Rq)⁻¹ κrad(q) conj(b(q))`.

At every off-line copy prove exact identity

`κrad^bphase(q) = ‖κrad(q)‖`.

Consequently transformed coefficient is strictly positive real and nowhere zero even when both
physical Ward channels are bright.

## Conjecture HC91-C: full finite-packet phase conjugation

Conjugate actual radiative packet transport by diagonal phase gauge. Prove exact coefficient law

`(T_rad^b x)(r) = κrad^b(Rr) conj(x(Rr))`.

For `bphase`, every off-line coefficient is the positive gain `‖κrad(Rr)‖`. Package this full
packet law together with HC89 bright cancellation as a closed theorem with no premise.

## Paper proof

Off line, `P(q)` and `P(Rq)` are nonzero. Exact HC89 transport and norm multiplicativity give

`P(Rq)=κrad(q)conj(P(q))`,
`‖P(Rq)‖=‖κrad(q)‖‖P(q)‖`.

Substitute `bphase=P/‖P‖` into gauged cocycle:

`(P(Rq)/‖P(Rq)‖)⁻¹ κrad(q) conj(P(q)/‖P(q)‖) = ‖κrad(q)‖`.

All cancelled factors are nonzero. Global phase norm and polar reconstruction follow by splitting
on `P(q)=0`. Packet coefficient formula is pointwise diagonal multiplication, anti-linear
transport, and reflection reindexing.

## Hostile checks

- Use actual raw nonlinear BM Ward amplitude, actual retarded Green-dressed cocycle, and full finite
  Xi packets.
- Gauge must have unit norm globally and reconstruct amplitude exactly.
- Prove positive-real equality, not only zero imaginary part.
- Prove full conjugated packet coefficient law.
- Exhibit coexistence with HC89 off-line bright cancellation.
- Do not claim source-fixed or divisor-independent phase; that is exact surviving constraint.
- No RH hypothesis, computation, numerical bound, new axiom, `sorry`, or `admit`.

## Expected route impact

If proved, reflection-reality is dead as a gauge-unqualified selector: actual radiative amplitude
itself supplies a unitary phase normalization making every off-line FE coefficient positive real.
Remaining RH-bearing burden is stricter: select phase reference before seeing source/divisor data,
or prove detector coordinates are fixed by local algebra and cannot follow raw amplitude phase.

## Bounded primary-literature audit (2026-08-28)

- `[LITERATURE]` Green--Hollands--Sberna--Toomani--Zimmerman,
  [*Conserved currents for Kerr and orthogonality of quasinormal modes*](https://arxiv.org/abs/2210.15935),
  constructs a conserved bilinear form and QNM excitation projections; it does not classify this
  Xi-source polar phase gauge or its RH-bearing source-independent survivor.
- `[LITERATURE]` Silva--Tambalo--Glampedakis--Yagi--Steinhoff,
  [*Quasinormal modes and their excitation beyond general relativity*](https://arxiv.org/abs/2404.11110),
  uses phase-amplitude methods for QNM frequencies/excitation factors, not an arithmetic
  Green/source-FE cocycle realification theorem.
- `[LITERATURE]` Mostafazadeh,
  [*Pseudo-Hermiticity versus PT-Symmetry III*](https://arxiv.org/abs/math-ph/0203005), relates
  anti-linear symmetries and positive metrics but does not give this source-native unit-phase
  finite-packet classification.
- `[NOVELTY CLAIM, BOUNDED]` Targeted primary-source and exact corpus searches found no theorem
  combining actual nonlinear BM amplitude polar phase, Green-dressed Xi FE transport, positive
  realification, finite-packet conjugation, and bright off-line cancellation. Audit is bounded.

## Formalization result

Formalized in
`GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMRadiativeSourceFEUnitPhaseRealificationNoGo`.

- Actual raw BM Ward amplitude defines a global polar phase gauge, with unit norm, no zeros, and
  exact reconstruction `bphase(q) · ‖P(q)‖ = P(q)` including the extinction wall.
- General anti-linear diagonal gauge formula is formalized for actual radiative cocycle and full
  finite-packet transport.
- Off line, Lean proves exact positive realification
  `κrad^bphase(q) = (‖κrad(q)‖ : ℂ)`, hence strictly positive real part and zero imaginary part.
- The conjugated full packet transport has exactly positive-gain reflected coefficients off line.
- General nowhere-zero diagonal gauge preserves cocycle involution; specialized unit-phase packet
  transport therefore still squares to identity globally.
- Closed theorem
  `hbXiPhaseSensitiveUnitRadiativeSourceFEUnitPhasePositiveRealBrightCancellation` packages global
  phase polar decomposition, positive off-line realification, full packet involution/coefficient
  law, and HC89 bright cancellation without any external premise.

Audit: direct `lake env lean` passed; targeted
`lake build GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMRadiativeSourceFEUnitPhaseRealificationNoGo`
passed all 12,020 jobs. Representative `#print axioms` outputs contain only `propext`,
`Classical.choice`, and `Quot.sound`. Formal lint reports only pre-existing unreachable modules
and no HC91 finding. Module is wired into `GaloisForLFunctions.RHTower` without a full umbrella
build.

## Open core after HC91

Reflection-reality is dead as a gauge-unqualified selector: actual source/Green amplitude supplies
a unitary diagonal phase normalization making every off-line radiative FE coefficient strictly
positive real, while full transport remains involutive and physical Ward channels remain bright
and cancel.

Only stronger phase rigidity can carry RH content: phase reference selected before and independently
of divisor/source amplitude, or a local detector/source algebra theorem forcing coordinates to stay
fixed under source variation. Hardest next question is whether one common gauge can realify multiple
independent physical source channels simultaneously; their relative phase holonomy may be the first
gauge-invariant survivor.

## Log

- 2026-08-28 — created directly in 1-in-progress after HC90 and mandatory corpus/literature audit.
