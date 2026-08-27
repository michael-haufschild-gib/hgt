# GTA symmetric graded quartic classification (2026-08-27)

## Result
For real scales k,l, even nodes a±kb and four odd nodes lb,lb,-lb,-lb define a complete graded lift of source pair a±ib.

Lean proves:
- first anomaly is always zero;
- universal second-anomaly vanishing iff k^2 - 2 l^2 = -1;
- on that negative Pell conic, quartic anomaly equals
  (k^2+1)b^2(12a^2+(k^2-3)b^2);
- trace-two preservation plus universal quartic nonnegativity iff Pell conic and 3 ≤ k^2;
- trace-two preservation plus quartic faithfulness (A4=0 iff b=0) iff Pell conic and 3 < k^2.

Sharp converse witness for every k^2 ≤ 3:
b=1, a=sqrt((3-k^2)/12), giving nonreal pair with zero quartic charge.

This shows positive orientation is a full chamber, not isolated (7,5). Canonical (1,1) is subcritical; (7,5) is faithful.

## Files
- formal/GaloisForLFunctions/HTGeometry/SourcePairSymmetricGradedQuarticClassification.lean
- docs/drafts/pipeline/3-formalized/source-pair-symmetric-graded-quartic-classification.md
- umbrella import in formal/GaloisForLFunctions/HTGeometry.lean

## Verification
- scratch and tree checked with lake env lean
- targeted lake build of exact module passed
- scripts/formal_tools.py lint passed
- #print axioms: propext, Classical.choice, Quot.sound only

## Route implication
Local GTA ORIENT is now classified for the full symmetric 2-even/4-odd family. Remaining hard core is global: build a conjugation/unitary-invariant, stage-degree-aware source reporter. Entrywise aggregation already has a closed 2x2 Hermitian counterexample; see `mem:rh/gta_positive_quartic_realification_and_entrywise_nogo_2026_08_27`.

Novelty label remains [NOVELTY UNVERIFIED].