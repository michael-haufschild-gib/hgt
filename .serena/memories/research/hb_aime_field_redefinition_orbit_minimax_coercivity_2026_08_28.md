# HC48 HB/AIME field-redefinition orbit-minimax coercivity (2026-08-28)

Formalized module: `GaloisForLFunctions.RHTower.ThetaCuspHawkingAIMEFieldRedefinitionOrbitMinimaxCoercivity`.

Core result: define projection-orbit cost `‖total‖/3`. It is invariant under affine channel redistribution and is the exact minimum peak norm among all equal-total triples; equal-channel representative is unique optimizer. On critical-line unit-BM matching locus, physical cost equals `‖amplitude‖^3 * d4AIMEThirdOrderOrbitMinimaxKernel (xiSpectralPoint q)`, with closed kernel `4 / ‖d4ThetaTeukolskyAngularQ z + 2‖`. Kernel is optical-shadow invariant and strictly positive on every Xi descendant. For nonzero seed, seed-normalized cost equals kernel and physical cost is positive. Sharp physical theorem quantifies over every equal-total coordinate representative and proves unique optimizer.

Verification: direct `lake env lean` passed; target-only `lake build` passed 12,753 jobs; all 14 public theorem axiom audits show only `propext`, `Classical.choice`, `Quot.sound`; wired into RHTower umbrella; lint has no HC48 error (global unrelated unreachable-module errors remain). Formalized card: `docs/drafts/pipeline/3-formalized/hb-aime-field-redefinition-orbit-minimax-coercivity.md`. Frontier map was not edited.

Next research direction: corpus-led HC49 should test whether closed kernel admits an exact q/reflection pairing or a global lower/upper bound that strengthens BM/AIME obstruction toward route endpoint, without assuming RH.