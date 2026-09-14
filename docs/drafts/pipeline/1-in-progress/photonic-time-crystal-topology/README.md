# Riemann objects from photonic time-crystal topology

- **ID:** PTC-NATIVE
- **Stage:** 1-in-progress
- **Type:** CANDIDATE INVESTIGATION with an explicit derived construction; no primary universal conjecture admitted
- **Statement:** Construct the zeta function, its nontrivial zeros, and its critical line from independently specified photonic time-crystal geometry, then identify the resulting topological RH problem.

## Scientific target

Start with temporal Maxwell evolution and its topology. Identify what the physical system supplies before selecting any Riemann object. The target is one construction that explains all three objects together, including why its coordinate has center `1/2`. A zeta-weighted dielectric profile or an operator defined using the desired zeros does not meet this target.

The [fact log](FACTS.md) records evidence and limitations. The [native-object analysis](native-objects.md) establishes the physical geometry and distinguishes the available spectral objects. The [parabolic return construction](parabolic-return-construction.md) now gives an exact ideal binary medium and derives a candidate response carrying the nontrivial zero divisor. Its classification is `[BRIDGE]`; it is not a proof of RH or a completed native-topology claim.

## Work map

1. Establish the physical model and distinct native spaces: temporal circle, dual quasifrequency circle, mode bundle, transfer geometry, and temporal-interface matching.
2. Derive candidate arithmetic objects from operations already available on those spaces. Test normalization and dependence on material deformation.
3. Freeze a precise conjecture only after a single construction generates all required objects; attack its truth and novelty independently.
4. Prove the exact surviving statement on paper, then formalize it unconditionally. Do not substitute unrelated Lean infrastructure for the native construction.

## Current mathematical issue

The [envelope obstruction](../photonic-time-crystal-native-geometry/ENVELOPE-OBSTRUCTION.md) changes the central target to the [full quantum response](envelope-response.md). A closed ideal lattice need not close its finite-energy preparation. The proposed primitive is the kernel of the Floquet resolvent between explicitly prepared and detected envelope/phase/logical channels. Its exact reduction retains the exterior memory `z²B(I-zD)⁻¹C`, together with source and observer dressing. Deriving its primitive-normalized cusp response is the next central attack; Riemann resonance identification and confinement remain separate problems. The earlier classical transfer construction below is a component, not an identification of this quantum kernel.

An explicit binary cell has noncentral parabolic monodromy. Its two-cell return response is `ζ(s)I+ζ(s−1)N`, with `N²=0`, after a specified Laplace–Mellin transformation. In the open strip, analytic invertible row/column operations reduce this to `diag(1,ζ(s)²)`. This gives response defects, not temporal-interface states. The zero divisor survives regrouping temporal cells.

The conserved flux vanishes identically on each defect kernel. It supplies a nondegenerate pairing between kernel and cokernel, not positivity on the kernel. The [canonical monodromy construction](detuning-monodromy.md) has a Lean-certified scalar continuation, nontrivial branch character, invariant projection, and exact first-jet recovery of the full classical return matrix. The material-detuning scratch supplies a candidate ramified multiplier cover, but that classical branch construction does not retain a photon envelope and is deferred behind the full-response problem. The negative-real character criterion for the critical line already exists in the corpus. A mechanism forcing defects into that locus remains open.

## Workflow and evidence

Methods read: `docs/meta/stroke-of-genius-method.md`, `docs/meta/scientific-method.md`, and the installed `/Users/michael/.claude/skills/hgtl7/SKILL.md`. Exact requested `hgt-fields-medalist` skill was not found in searched project, Codex, Claude, and parent skill locations; its path was requested. No claim of executing that missing file's instructions.

Corpus search commands include hybrid `research 'photonic time crystal topology Floquet' --any`, lexical `research 'Floquet' --mode lexical --no-refresh`, and deep mechanism searches for temporal monodromy, finite covers, half-densities, and theta–Mellin duality. Broad 2026 arXiv searches included holonomy, monodromy, pumping, torsion, metaplectic, and impedance. Literature findings are leads until their exact applicability is established.

The literal return-series identity, analytic reduction, RH equivalence, and flux obstruction are checked in `formal/GaloisForLFunctions/RHTower/PhotonicParabolicReturn.lean` (18 public theorems). The scalar continuation and first-jet bridge are checked in `formal/GaloisForLFunctions/RHTower/PhotonicReturnMonodromy.lean` (11 public theorems). Scratch validation and targeted leaf builds passed at default heartbeat limits. Both umbrella imports are present; all 29 public theorems were axiom-audited with only `propext`, `Classical.choice`, `Quot.sound`. No full or umbrella build was run. Global lint reports three unrelated unwired modules; the search index was refreshed. No numerical work. The requested fully native reframing remains unfinished.
