# HC71 — Schwarz-odd diagonal causal-propagator obstruction (2026-08-28)

Formal module: `formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingSchwarzOddDiagonalCausalPropagatorObstruction.lean`

Card: `docs/drafts/pipeline/3-formalized/hb-schwarz-odd-diagonal-causal-propagator-obstruction.md`

Corpus-led result:
- Defined `HBXiPeierlsWeightedPropagatorChannelSchwarzOdd w` by `S (Delta_w f) = - Delta_w (S f)` for all finite-support two-channel packets.
- Proved exact classification `hbXiPeierlsWeightedPropagatorChannelSchwarzOdd_iff`: this operator law holds iff every diagonal jump weight is Schwarz-real.
- Proved `hbXiPeierlsRadialWeight_im`: canonical BM radial weight has imaginary part `-(q.1).im`.
- Since every Xi divisor copy has nonzero imaginary height, proved canonical radial weights are never Schwarz-real and their diagonal propagator is never Schwarz-odd.
- Combined with HC70 fibre incidence rigidity to prove the closed endpoint `exists_hbXiPeierlsUniversalUnitDiagonalSourceIncidence_and_channelSchwarzOdd_iff_rh n`. Under RH the zero weight witnesses existence because all BM sources are extinct; conversely exact incidence plus Schwarz reality excludes every tilted fibre.

Scope: complete compatibility classification in copy-diagonal Green-jump class. Does not prove physical Einstein–Teukolsky causal propagator is copy-diagonal or that physical time reflection equals corpus channel Schwarz; those PDE identifications remain.

Audit: direct `lake env lean` passed; target-only build passed `12022/12022`; five exported theorem axiom audits use only `propext`, `Classical.choice`, `Quot.sound`; umbrella wired. Global lint has only unrelated pre-existing unreachable modules, no HC71 finding. Frontier map untouched. Scratch files removed.