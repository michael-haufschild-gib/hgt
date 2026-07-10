# The infinite theta reader is forced to be singular at the heat boundary

- **ID:** xi-theta-heat-node-singularity
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean), [PROVED]
- **Date:** 2026-07-10
- **Module:** GaloisForLFunctions.RHTower.XiThetaHeatNodeObstruction
- **Paper proof:** ../../2-fully-proven/new/xi-theta-heat-node-singularity.md

## Formal surface

- thetaHeatNode: compactified square node exp(-pi m squared).
- thetaHeatNode_pos: every node lies in the punctured positive half-line.
- thetaHeatNode_tendsto_zero: the nodes accumulate at zero.
- thetaHeatNode_complex_tendsto_punctured_zero: convergence in the punctured complex neighborhood.
- no_analyticOnNhd_thetaHeatNode_reader: on any preconnected compactified domain containing zero
  and all nodes, a holomorphic symbol vanishing at every other node also vanishes at the selected
  node.
- no_analyticOnNhd_thetaHeatNode_delta: no such connected-domain holomorphic delta symbol exists.
- no_entire_thetaHeatNode_reader: an entire symbol vanishing on every other node also vanishes at
  the selected node.
- no_entire_thetaHeatNode_delta: no entire Kronecker-delta interpolation symbol exists.

## Certificate

- Direct source check passed.
- Targeted build passed: `lake build GaloisForLFunctions.RHTower.XiThetaHeatNodeObstruction`
  (8603 jobs).
- Axiom audit passed for the convergence theorem and the generalized and entire reader
  obstructions; only `propext`, `Classical.choice`, and `Quot.sound` occur.
- Generated theorem API refreshed; formal lint passed.
- No full or umbrella build.
- No sorry, admit, axiom, opaque, or unsafe declaration.

## Scope

The theorem forces a boundary singularity for every reader represented by a symbol holomorphic on
a connected compactified domain containing zero and all square heat nodes. It does not construct
the surviving Hardy/Blaschke reader in the uncompactified rate plane or rule out reader categories
without such a moment symbol.
