# Rough Sobolev modulus realization and exact nodal defect

- **ID:** rough-sobolev-modulus-nodal-defect
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** Every actual logarithmic Sobolev state has a constructed modulus
  velocity with unchanged additive energy; its exact mixed-graph nodal loss
  transfers into path slack.

## Exact result

For physical L² q and G(t)=c+∫₀ᵗq, construct m=modulusVelocity q c. Proved

    m(t)=sign(G(t))q(t) almost everywhere,
    |c|+primitive m t=|G(t)| for every t,
    energy m a b=energy q a b for every a,b.

The logarithmic state (m,|c|) is exactly the modulus of (q,c), and every
weighted logarithmic Dirichlet interval energy is unchanged. For any constructed
mixed measure D, including infinite total energy,

    jumpEnergy D q=jumpEnergy D m+nodalEnergy D q c,
    slackEnergy D m=slackEnergy D q+nodalEnergy D q c,
    congestionEnergy D m=congestionEnergy D q.

Each edge budget is unchanged. Compact sources make all energies finite, give
the ordinary real jump-energy difference, and preserve weighted source mass.
The entire source-mass plus jump form has the same exact nodal defect.

## Proof mechanism

Absolute value contracts endpoint distances, hence preserves local absolute
continuity. A countable interval cover gives a.e. differentiability of |G|.
At G=0, both |G| and |G|+G attain minimum zero; their zero derivatives force
q=0 wherever both derivatives exist. Away from zero the ordinary chain rule
applies. Thus the measurable derivative of |G| has square q² a.e., belongs to
L² and defines m. The absolute-continuity fundamental theorem gives its exact
primitive. The existing nodal pair identity then integrates over the entire
mixed measure. Finite individual jumps justify the edgewise cancellation needed
for slack transfer; no infinite total energies are subtracted.

Paper: `docs/reports/BiScaleUncertainty/RoughSobolevModulus.md`.
No analytic admission, zero-level derivative or chain-rule premise is assumed.

## Corpus and novelty boundary

The focused deep search was partial (last query unfinished), with no execution
errors, older coverage snapshot and unmeasured semantic coverage. All candidate,
source-argument and ingredient entries were inspected. Mathlib supplies applicable
a.e. differentiability and absolute-continuity fundamental-theorem APIs. The
proposed ingredient group "Derivative zero implies absolute continuity" was
rejected: that implication fails without further assumptions. Absolute continuity
is established first. Existing field nodal algebra did not construct the modulus
inside the actual rough-state domain. Classical Sobolev chain rules and
Beurling–Deny contraction carry no external novelty claim here.

## Certification

- [x] Dependency-closed paper proof, including exact slack transfer.
- [x] `RoughSobolevModulus.lean`: 14 public theorems and 2 definitions.
- [x] `RoughModulusGraphDecomposition.lean`: 11 public theorems.
- [x] Both final serial direct leaf checks passed without diagnostics, with normal
  `.olean` outputs newer than final sources. No full/umbrella build or heartbeat increase.
- [x] All 27 public declarations passed axiom audit: only `propext`,
  `Classical.choice`, `Quot.sound`; seven main signatures inspected.
- [x] Both imports wired, all 25 theorem names indexed, whitespace check passed.
- [x] Global lint run: four unrelated concurrent missing imports, listed in the
  fact ledger. No error concerns either new leaf.

One connected contribution, **6/100**. No full closed-operator identification or
unitary affine action is claimed. All owned verification processes are terminal.
Follow-on result: `compact-nodal-mass-coercivity.md`, now formalized as package 7.
