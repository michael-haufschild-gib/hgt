# HC49 HB canonical Schwarz transport vs extinction (2026-08-28)

Formalized module: `GaloisForLFunctions.RHTower.ThetaCuspHawkingBMCanonicalSchwarzTransportExtinctionClassification`.

New result: corpus endpoint `HBXiPeierlsCanonicalLeftBranchCovariance` equates packets on disjoint direct-sum channel axes, so it is not genuine branch transport. Constructed canonical anti-linear channel Schwarz involution: coefficientwise conjugation plus regular/complementary axis exchange. It is involutive, maps every plus packet/left-source to matching minus packet unconditionally, and conjugates `hbXiPeierlsPairing`. Literal plus-axis = minus-axis equality iff both packets vanish. For nonzero seed, reflected both-zero locus is exactly critical line; global extinction is RH. Off wall, genuine transport exchanges two nonzero unequal packets.

Route consequence: ordinary Schwarz covariance has no RH-selective content. Old equality endpoint is source extinction. Hard HB producer is now a nontrivial FE divisor-reindexing/cocycle compatibility or nonzero source/response Ward law, not ordinary channel exchange.

Verification: direct Lean passed; target-only build passed 11,917 jobs; all 19 public theorem axiom audits only `propext`, `Classical.choice`, `Quot.sound`; wired into RHTower umbrella; lint no HC49 error. Card: `docs/drafts/pipeline/3-formalized/hb-canonical-schwarz-transport-vs-extinction.md`. Frontier map untouched.

Next: HC50 must start with `formal_tools.py research` and attack source-derived FE reindexing/cocycle compatibility, not numerical bounds.