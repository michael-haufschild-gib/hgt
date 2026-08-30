# FZZ-P same-source divisor gradient-flow no-go

- **ID:** FZZ-P-SAME-SOURCE-DIVISOR-FLOW-NOGO
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `rh-current-frontier-map.md` · FZZ-P `ORIENT DYN`
- **Statement:** A continuous trajectory that stays in the divisor of the same literal FZZ parity Mellin source is constant; consequently it can realize the corpus reflected-Fermi inward-gradient velocity through an open-strip mode exactly on the critical wall, and universal existence of such trajectories is exactly RH.

## Goal

Kill the surviving fixed-source dynamical orientation chain

`literal FZZ parity Mellin source → continuous interacting transport of its divisor modes → reflected-Fermi inward gradient → source-mode stationarity/completeness → RH`.

This attacks the hardest remaining FZZ-P premise, not a constant or bound. It asks whether the already formalized inward source force can genuinely move a zero of the unchanged source. The theorem must classify the full continuous same-source class, prove off-wall impossibility, and identify the exact successor architecture.

## Gates

- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3  formalized: Lean theorem `RHTower.fzzCigarParity_sameSourceDivisorGradientFlow_noGo`, targeted `lake build` green, targeted axioms PASS
- [ ] 3 → 4  publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Frozen conjecture and proof chain

For an open-strip FZZ parity Mellin mode `rho`, call `gamma : ℝ → ℂ` a same-source reflected-Fermi gradient trajectory through `rho` when:

1. `gamma` is continuous and `gamma 0 = rho`;
2. every `gamma t` remains in the open strip and satisfies the unchanged equation `fzzCigarParityMellin (gamma t) = 0`;
3. its horizontal coordinate is differentiable at every `t`, with derivative equal to `-fzzCigarParityReflectedFermiInformationForce (gamma t).re`.

**Conjecture FZZ-P-D0 (transport producer).** Every open-strip FZZ parity mode admits such a trajectory.

**Hostile attack / proposed killing theorem.**

1. On the open strip, every FZZ parity Mellin mode is a completed-Xi zero.
2. Completed Xi is entire and nonzero, so its zero subtype is discrete.
3. A continuous map from connected `ℝ` into that subtype is constant.
4. A constant trajectory has derivative zero. The prescribed velocity is zero exactly at `Re rho = 1/2`.
5. Hence a same-source trajectory through `rho` exists iff `Re rho = 1/2`.
6. Universal existence of these trajectories is equivalent to corpus source-mode stationarity, hence to RH.
7. At every hypothetical tilted FZZ mode, the formal inward velocity is nonzero but no continuous same-source divisor trajectory realizes it.

Success kills Conjecture FZZ-P-D0 and every continuous fixed-source refinement at once. Failure must identify either a non-discrete divisor, an identically-zero source, or a path that changes the source family.

## Conjecturing loop

- **A — fixed-source inward transport:** hypothesize literal interacting FZZ dynamics moves each mode continuously while retaining the same Mellin divisor. **Preliminary verdict: falsified** by isolated-zero rigidity.
- **B — source-deformation necessity:** conjecture every nonconstant continuous zero motion must leave the fixed-source divisor, equivalently use a nonconstant family `M_t` with `M_t(gamma(t)) = 0`. **Current target:** prove the exact fixed-source classification and retain source deformation as strongest positive survivor.
- **C — successor after proof:** attack whether literal GFZZ physics canonically supplies such a source-changing family whose zero velocity equals the reflected-Fermi velocity. This successor is admissible only after B is formally closed; importing an arbitrary deformation would merely relocate RH.

## Approach

Use the corpus theorem `fzzCigarParityMellin_eq_zero_iff_xi_eq_zero` to lift any trajectory into the Xi-zero subtype. Install its discrete topology using `HTGeometry.discreteTopology_setOf_eq_zero`, `xi_analyticOnNhd_univ`, and the explicit witness `xi 0 = 1/2 ≠ 0`. Apply `PreconnectedSpace.constant`. Derivative uniqueness then forces prescribed velocity to vanish. Close the pointwise converse by the constant trajectory and the corpus unique-equilibrium theorem. Quantify over all open-strip modes and weld to `fzzCigarParityReflectedFermiInformationStationarity_iff_riemannHypothesis`.

## Paper theorem and proof

**Theorem `[PROVED HERE]`.** Let

`Z_Xi := {z : ℂ | xi z = 0}`.

1. If `T` is preconnected and `gamma : T → ℂ` is continuous, every `gamma(t)` lies in the open strip, and every `gamma(t)` is a mode of the unchanged literal FZZ parity Mellin source, then `gamma` is constant.
2. Fix an open-strip FZZ parity mode `rho`. A same-source reflected-Fermi gradient trajectory through `rho` exists if and only if `Re rho = 1/2`.
3. Every open-strip FZZ parity mode admits such a trajectory if and only if RH.
4. Equivalently, every nonconstant continuous path contained in the open strip leaves the unchanged FZZ parity divisor at some parameter value.

**Proof.** Completed Xi is entire. Moreover `xi(0)=1/2`, so it is not the zero function. The isolated-zero theorem therefore gives `Z_Xi` the discrete topology. The corpus divisor comparison proves that each open-strip FZZ parity Mellin mode is an element of `Z_Xi`. Thus `gamma` lifts continuously to a map `T → Z_Xi`. Every continuous map from a preconnected space into a discrete space is constant. Its projection to `ℂ` is therefore constant, proving (1).

For (2), let `gamma` be a same-source trajectory through `rho`. Apply (1) with `T=ℝ`; then `gamma(t)=rho` for all `t`. Hence `t ↦ Re(gamma(t))` is constant and has derivative zero. Uniqueness of derivatives and the trajectory equation give

`fzzCigarParityReflectedFermiInformationVelocity (Re rho)=0`.

Velocity is the negative reflected-Fermi force. The corpus unique-equilibrium theorem on the open strip gives `Re rho=1/2`. Conversely, if `Re rho=1/2`, the constant path `gamma(t)=rho` remains an open-strip mode, and its horizontal derivative and the reflected-Fermi velocity both vanish. It is therefore a trajectory.

For (3), universal trajectory existence is pointwise equivalent by (2) to every open-strip FZZ parity mode having real part `1/2`. By the corpus force zero criterion this is exactly universal reflected-Fermi information stationarity, already proved equivalent to RH. For (4), if a nonconstant path never left the fixed divisor, (1) would make it constant, a contradiction. ∎

## Novelty and hostile audit

- **Known core:** isolated zeros of a nonzero analytic function and constancy of continuous maps from connected spaces into discrete spaces are classical. They are not claimed as new.
- **Corpus gap:** corpus has literal FZZ source continuation, exact divisor comparison, strict reflected-Fermi inward velocity, and stationarity iff RH. It also kills local polynomially-tempered same-source FE reflection and several nonlocal reflection classes; those theorems classify implementations of Mellin reflection, not continuous motion inside one fixed divisor. Search found no prior connected-family rigidity theorem, trajectory/wall classification, or global same-source realizability/RH weld.
- **Literature audit through 2026-08-30:** Hikida--Schomerus, arXiv:0805.3931, prove FZZ duality. Pakman, arXiv:hep-th/0606067, shows a classical scattering problem does not uniquely determine the quantum reflection coefficient without an added dual-scattering assumption. No audited source supplies fixed-source divisor transport or an RH selection theorem. The de Bruijn--Newman evolution in arXiv:1904.12438 instead varies the entire function `H_t`, supporting source deformation as the correct surviving architecture rather than contradicting the no-go.
- **Novelty claim under test:** exact FZZ-P route-class classification and global RH equivalence of same-source gradient realizability, not the parent isolated-zero lemma.

## No-go closure (mandatory when falsified)

- **Exact killing theorem/mechanism:** fixed nonzero holomorphic source has a discrete divisor, so continuous same-source zero motion is constant; the nonzero off-wall inward force cannot be its tangent velocity.
- **Strongest positive survivor:** any live continuous FZZ-P orientation mechanism must deform the literal source/divisor family. At a moving simple zero, its velocity must come from source variation, not from a vector field on one fixed divisor.
- **New insight:** source force and divisor velocity are categorically different objects. The corpus force supplies an orientation on ambient source coordinates but cannot itself transport an unchanged spectral zero.
- **Status:** `[LEAN-PROVED]`. Exact capstone `RHTower.fzzCigarParity_sameSourceDivisorGradientFlow_noGo`; arbitrary preconnected-family rigidity, pointwise trajectory classification, global RH equivalence, and source-deformation survivor are formalized. `[CANDIDATE NEW SCIENTIFIC KNOWLEDGE]` pending independent proof/priority review.

## Lean certificate

- **Module:** `formal/GaloisForLFunctions/RHTower/FZZCigarParitySameSourceDivisorGradientFlowNoGo.lean`
- **Capstone:** `RHTower.fzzCigarParity_sameSourceDivisorGradientFlow_noGo`
- **Connected-family rigidity:** `RHTower.continuous_fzzCigarParity_sameSourceModeFamily_constant`
- **Pointwise classification:** `RHTower.fzzCigarParity_sameSourceReflectedFermiGradientTrajectory_iff`
- **Global endpoint:** `RHTower.fzzCigarParity_sameSourceReflectedFermiGradientRealizability_iff_riemannHypothesis`
- **Positive survivor:** `RHTower.exists_not_fzzCigarParityMellinMode_of_continuous_openStrip_path_ne`
- **Umbrella:** imported by `formal/GaloisForLFunctions/RHTower.lean`
- **Verification:** direct `lake env lean` PASS; targeted `lake build GaloisForLFunctions.RHTower.FZZCigarParitySameSourceDivisorGradientFlowNoGo` PASS; all listed theorems depend only on `propext`, `Classical.choice`, `Quot.sound`.
- **Lint:** new module is umbrella-reachable and contains no forbidden declaration; repository lint remains red only on unrelated `HTGeometry.RittFirstJetAffineDescent` reachability debt.

## Log

- 2026-08-30 — corpus search and current primary-literature audit completed; Conjecture A failed hostile attack, stronger source-deformation classification frozen before proof work.
- 2026-08-30 — `[PROVED HERE]`: discrete-divisor lift closes arbitrary preconnected-family rigidity; derivative uniqueness gives exact pointwise trajectory classification and global RH equivalence.
- 2026-08-30 — `[LEAN-PROVED]`: capstone, global RH endpoint, and source-deformation survivor formalized; direct check, targeted build, axioms audit, corpus-index audit, and owned-module reachability check pass.
