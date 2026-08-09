# Serial reconstruction-radius failure and hidden-pair survivor law

- **ID:** ULF-RADIUS-2
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean 4)
- **Source:** Lean attack on ULF-DISTORTION-1
- **Statement:** Serial coarsening can strictly reduce internal-centre reconstruction radius, but
  it preserves all previously hidden source pairs and their distances; every uniform reconstructor
  is therefore bounded below by half the diameter of each hidden pair.
- **Formalized companion:** `formal/GaloisForLFunctions/HTGeometry/ConstitutiveReconstructionNoGo.lean`

## Closed counterexample

Use the metric subspace \(X=\{-1,0,1\}\subset\mathbb R\).  The fine observer has endpoint fibre
\(\{-1,1\}\) and singleton centre fibre \(\{0\}\).  Every legal section of the fine observer must
choose one endpoint as representative of the endpoint fibre, so the other endpoint has error two.
The serially coarser constant observer may select zero and has error at most one everywhere.

Hence the proposed law

\[
\mathfrak R(r\circ q)\geq \mathfrak R(q)
\]

is false when fibre radius restricts centres to the fibre.

## Exact survivor

For any observer \(q:X\to Y\), package a hidden pair as

\[
(x,x',\ q(x)=q(x')).
\]

Every postprocessing \(r:Y\to Z\) sends it canonically to a hidden pair for \(r\circ q\), without
changing \(x,x'\) or \(d(x,x')\).  If a legal section reconstructs every source point with error
at most \(C\), the triangle inequality gives

\[
d(x,x')\leq 2C
\]

for every hidden pair.  Thus pairwise fibre diameter, not internal-centre radius, is the monotone
serial obstruction.

## Field consequence

Even a plausible coordinate-free scalar can fail under composition.  CPM must retain the actual
hidden-pair relation (or its enriched kernel pair) before decategorifying it to radius, diameter, or
energy.  This is a structural correction, not a route-specific obstruction.

## Scope

- The theorem does not compute optimal radii for arbitrary observers.
- Diameter supplies a lower bound, not always an exact reconstruction error.
- The counterexample is finite and requires no compactness, probability, or arithmetic input.

## Log

- 2026-08-09 — false serial-radius law rejected; counterexample and kernel-pair survivor certified
  in Lean.

