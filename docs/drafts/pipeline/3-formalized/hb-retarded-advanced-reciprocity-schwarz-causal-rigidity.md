# HB retarded/advanced reciprocity--Schwarz causal rigidity

- **ID:** HC73
- **Stage:** 3-formalized
- **Type:** THEOREM / LEAN-PROVED GREEN-OPERATOR STRUCTURAL CLASSIFICATION / HARD FRONTIER
- **Routes:** HB, FZZ-P, RBH, PW-B
- **Source:** HC72 arbitrary-global propagator obstruction; corpus symmetric Xi pairing; canonical
  involutive channel Schwarz transport; Green-hyperbolic retarded/advanced duality
- **Statement:** Retarded/advanced pairing reciprocity and one-sided Schwarz exchange force their
  causal jump to be Peierls-skew and Schwarz-odd; conversely every skew, Schwarz-odd global Xi
  propagator has an exact reciprocal Schwarz-exchanged retarded/advanced decomposition. Universal
  literal BM incidence for such a pair exists if and only if RH.

## Corpus-led conjecture

For arbitrary complex-linear global response maps `Gret` and `Gadv`, assume only

`pairing (Gret f) g = pairing f (Gadv g)`

and the one-sided Schwarz exchange

`S (Gret f) = Gadv (S f)`.

The corpus supplies symmetry of the Xi dot product and involutivity of `S`. It should therefore
derive the reverse reciprocity and reverse Schwarz-exchange laws. For the causal jump
`Delta = Gret - Gadv`, these imply

`Peierls(Delta; f,g) = -Peierls(Delta; g,f)`

and

`S (Delta f) = -Delta (S f)`.

The converse should be exact, not merely existential: every skew, Schwarz-odd `Delta` is the jump
of `Gret = (1/2) Delta` and `Gadv = -(1/2) Delta`. Thus the minimal algebraic retarded/advanced
axioms and HC72's two causal-jump axioms classify the same operator class. Combining the forward
direction with HC72 should give the closed endpoint

`(exists Gret Gadv, reciprocity and SchwarzExchange and universal BM incidence of Gret-Gadv)
  <-> RH`.

## Why this is frontier-level

HC72 left Peierls skewness and Schwarz oddness as independent assumptions on a monolithic causal
propagator. Physical Green theory instead constructs retarded and advanced solution operators, with
duality interchanging causal orientation and time-reflection exchanging the pair. HC73 asks whether
those standard producer laws really imply the exact HC72 hypotheses on the global Xi carrier and
whether any hidden algebraic restriction remains.

A two-way classification would close that structural translation completely. It would also prove a
no-go: retarded/advanced splitting alone adds no extra off-critical escape or rigidity. Remaining
physical burden would be sharper—construct the actual gauge-fixed Einstein--Teukolsky Green pair
and prove literal nonlinear BM incidence (plus analytic Green/inverse/support laws), not separately
postulate skewness or Schwarz oddness.

## Hostile checks

- Quantify over arbitrary global complex-linear `Gret` and `Gadv`; no diagonal/local/support/bounded
  hypothesis.
- Use one reciprocity identity and one Schwarz-exchange identity only; derive reverse directions.
- Prove both directions of the operator-class classification, including exact half-jump witnesses.
- State universal exact unit BM incidence iff RH as a closed theorem.
- Do not label abstract response maps as PDE Green operators; inverse and causal-support laws remain
  outside this carrier theorem.
- Keep frontier map read-only.

## Novelty boundary as of 2026-08-28

Mandatory Lean-corpus searches for retarded/advanced reciprocity, formal-adjoint exchange, causal
propagator skewness, and Schwarz/time-reflection exchange found HC72's monolithic skew/odd endpoint,
abstract retarded-minus-advanced cuts, and a Weyl-system skewness theorem, but no derivation of the
HC72 laws from a Green pair and no converse half-jump classification. Bounded primary-source audit
covered Baer's Green-hyperbolic operator framework (arXiv:1310.0738), where formal duality
interchanges advanced and retarded Green operators and the causal propagator is their difference;
Benini--Musante--Schenkel's Green-hyperbolic complexes (arXiv:2207.04069), where the
retarded-minus-advanced map produces covariant Poisson structures; and the Kerr adjoint-current
identities of Green--Hollands--Sberna--Toomani--Zimmerman (arXiv:2210.15935). No audited source
states this exact Xi-carrier two-way classification, literal BM incidence obstruction, or RH
equivalence. Bounded, not exhaustive, priority claim.

## Gates

- [x] 0 -> 1 in-progress: corpus gap, exact conjecture, hostile proof route, bounded literature audit
- [x] 1 -> 2 fully-proven: dependency-closed paper proof
- [x] 2 -> 3 formalized: closed Lean theorem, target build, axiom/lint audit, umbrella wire
- [ ] 3 -> 4 publication-ready: independent priority audit and standalone exposition

## Log

- 2026-08-28 — Opened after HC72 reduced the arbitrary-global obstruction to Peierls skewness,
  channel-Schwarz oddness, and literal incidence. Frontier map left unchanged.
- 2026-08-28 — First conjecture succeeded without weakening. Proved reverse reciprocity and reverse
  Schwarz exchange from pairing symmetry and involutivity, hence skewness and Schwarz oddness of
  every retarded-minus-advanced jump. Proved the converse exactly: every arbitrary global skew,
  Schwarz-odd propagator is the jump of the reciprocal, Schwarz-exchanged pair
  `Gret = (1/2) Delta`, `Gadv = -(1/2) Delta`. Therefore the two operator classes coincide, and
  universal literal unit BM incidence for the Green pair is equivalent to RH.
- 2026-08-28 — Formalized in
  `ThetaCuspHawkingRetardedAdvancedReciprocitySchwarzCausalRigidity.lean`. Direct
  `lake env lean` passed; target-only
  `lake build GaloisForLFunctions.RHTower.ThetaCuspHawkingRetardedAdvancedReciprocitySchwarzCausalRigidity`
  passed (`12024/12024`); all eleven exported theorem axiom audits report only `propext`,
  `Classical.choice`, and `Quot.sound`; umbrella import present. Formal lint reports no finding in
  this module and remains nonzero only for the pre-existing unrelated unreachable-module list.
