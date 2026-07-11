# Ticket: door index — Hurwitz full-ladder independence closed + formalized

- Card `hurwitz-in-a-weld-escape-ht` moved 1-in-progress → 3-formalized/new_scientific_knowledge.
  Headline: for `Re s > 1`, `s ∉ ℚ`, the ladder {ζ(s+k,a)}_k is algebraically independent over
  ℂ(a) at ALL degrees (hence ζ(s,·) hypertranscendental in a). Proof: delocalized monodromy
  (deformation grid at N+1 branch points) + Vandermonde. Lean capstone:
  `HurwitzLadder.hurwitz_ladder_independence` (+ near-ray form), axiom-clean, in
  `FullyProvenNewTargets` as `HurwitzLadderFullIndependenceTarget`.
- Backlog card `hurwitz-degree3-pochhammer-obstacle` retired to 5-failed (superseded).
- Index/status lines mentioning "Hurwitz open core = degree ≥ 3 / rank lemma" should now read
  "closed for s ∉ ℚ; residual = rational non-integer s at degree ≥ denominator".
