# Weighted coefficient neighborhoods of negative defect

- **ID:** thim-weighted-coefficient-neighborhood
- **Stage:** 3-formalized
- **Type:** THEOREM (paper and Lean verified)
- **Scope:** Finite divisor-incidence distance, coefficient perturbation, and uniform radical-fiber certificates.

## Gates

- [x] Read attachment, complete current field README and direct dependency; broad corpus search.
- [x] Dependency-closed paper proof.
- [x] Scratch and actual-source Lean verification; axiom audit stopped at user request.
- [x] Umbrella, index/lint, ledger, positive survivor, memory and cleanup.

## Paper proof

Let W(N,K;c,b)=Σ_{d≤N}|c(d)−b(d)| floor(K/d). Exact divisor counting
bounds the sum of response errors up to K by W, hence each individual error.
If M+1≤K and the reference response b is bounded by B on the prefix, then
the response c is bounded by B+W. The established incidence perturbation
law therefore gives |D_c(M)−D_b(M)|≤4(B+W)W. This requires no squarefree
support and no a priori bound on c.

Set K=6(N+1), N≥2, b=μ. For 1≤M and M+1<K, |s_μ|≤2 and D_μ≤−1.
Therefore D_c≤−1+4(2+W)W. For squarefree-supported c the finite-certificate
transfer law extends this same bound to every M≥1 with R_N(M+1)<K,
uniformly in height. In particular 4(2+W)W≤1/2 gives D_c≤−1/2.
W≤1/20 gives the stronger bound D_c≤−59/100. Positive powers of any
finite certified base inherit the bound.

This is a whole coefficient neighborhood, not merely the power-damping curve.
The unit coefficient is charged with weight K, respecting the known gauge
obstruction to all-weight universal negativity. The finite distance is a
seminorm distance on infinite coefficient functions; it is a norm on visible
coefficient differences when K≥N.

To produce weights with no unverified budget input, project any perturbation h
onto squarefree indices, call it h_sf, and normalize by 20(1+W(N,K;h_sf,0)).
Then c=μ+h_sf/[20(1+W)] has distance W/[20(1+W)]<1/20. The constructor
is squarefree-supported for every h; all certified radical fibers thus have
strict defect below −59/100. Arbitrary positive powers retain this guarantee.
At the prime family N=6p−1,k=30p,p>5, the response is at least39/20 while
the defect is at most−59/100. No first-failure claim for general perturbations.

## Baseline and scope

Known constituents: weighted finite ℓ¹ triangle inequality, divisor-incidence
floor reciprocity, finite quadratic-form perturbation, and radical-state
transport. Classical observation baseline TH10 https://arxiv.org/abs/1009.5281;
shifted-correlation baseline CMS16 https://arxiv.org/abs/1612.03136.
Classification: New formulation. No external priority or optimal-radius claim.
Full all-ε≥0 damping control remains open.

Broad corpus query `weighted coefficient perturbation neighborhood strict
negative prefix defect divisor incidence`: partial=false,74149files,pending0,
generation1455104. All20 candidate and20 source-argument statements inspected.
The previous incidence estimate, weight scaling, gauge law and support-local
identities are available; no matching quantitative coefficient-neighborhood
certificate in returned hits. Compiler coverage is mixed and applicability
is now verified in this toolchain.

The normalized constructor satisfies the stronger strict counterfamily
separation response>39/20 and defect<−59/100 at every positive power of30p,
for every perturbation direction h and prime p>5.

Normalization query `squarefree projection normalize perturbation finite
coefficient distance`, field-filtered: partial=false,74150files,pending0,
generation1455117. All20 candidate and20 source-argument statements inspected.
Existing active interpolants solve a different prescribed-observation problem;
no matching automatic incidence-budget normalization in returned hits.

## Verification

- Source: `formal/GaloisForLFunctions/TransHorizonIncidenceMechanics/WeightedCoefficientNeighborhoodAndRadicalDefectStability.lean` (284 lines).
- SHA256: `6978501936dcce20b9b287e33b9cbc3a6d1243ec35467cc7c60deaea401866f3`.
- Full scratch and actual-source `lake --old env lean` exited 0 without warnings.
  The 18 public theorems and 3 definitions compile. The axiom check was
  stopped at the user's request (exit143); axiom closure remains unaudited.
- `logs/thim-neighborhood-audit.json` records the incomplete axiom audit and verifies all 21 public
  API entries and source positions, baseline docstrings, source/dependency hashes,
  fresh artifacts, unique umbrella import, MainTheorems reachability,
  whitespace and prohibited declarations.
- Evidence: `logs/thim-neighborhood-{lean,axioms,index,lint}.txt`.
  Index exited 0. Global `lint --check-generated` exited 1 with
  2 external findings, listed exactly in audit JSON.
  No owned-leaf or prohibited-declaration finding. Shared generated freshness
  can change under concurrent edits; no globally clean gate is claimed.
- All owned jobs terminal; eight owned temporary files removed and verified absent.
  README not edited. No full/umbrella build, numerical experiment, added axiom,
  heartbeat change, commit or push. Research paused at user request after
  this contribution; the next conjecture is recorded but not started.

## Next conjecture — separate the unit gauge (unproved)

The incidence budget charges a unit-coefficient shift a by K|a|, but the
exact gauge law charges defect only by a(s_c(M+1)−s_c(1)). This suggests a
larger neighborhood after separating the gauge coordinate.

Conjecture: take N≥2,K=6(N+1), squarefree-supported c with c(1)=1 and
W(N,K;c,μ)≤1/20. For every |a|≤1/40, the unit-shifted weight c+a·1_{d=1}
has D≤−411/800<−1/2 at every nonempty certified radical endpoint.
The allowed gauge interval would be independent of N, unlike direct
incidence charging of the unit coefficient.

Proposed mechanism: the new result gives D_c≤−59/100. Radical reduction
transfers the finite response bound |s_c|≤2+W to every certified endpoint;
the rough state has s_c=1. Hence |s_c(M+1)−1|≤3+W≤61/20 and the exact
gauge term costs at most61/800, leaving −411/800. A stronger proposed
certificate is D_shift≤−1+4(2+W)W+|a|(3+W). Check source hypotheses,
rough endpoints and the complete paper/Lean argument before claiming it.
No all-ε≥0 damping theorem follows from this conjecture.

Preliminary field-filtered query `unit shift gauge coefficient perturbation
strict negative defect neighborhood`: partial=false,74151files,pending0,
generation1455139. All20 candidates and20 source-argument statements inspected.
Exact gauge and radical laws were returned; no matching gauge-separated
quantitative neighborhood in returned hits. Broaden before new implementation;
compiler coverage remains mixed.
