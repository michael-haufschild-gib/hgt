# Further items: exact mathematical targets

- **ID:** further-items-review-1011
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** `docs/reports/review-1011/obstacles-summary.md`, §2.1, “Further items”.
- **Statement:** Resolve all fourteen tasks with dependency-closed proofs and unconditional Lean formalizations.
- **Constraints:** No web search, numerical experiments, or computation-based certificates. Local corpus search and deductive Lean proofs only.

| Item | Exact target | Status |
|---|---|---|
| A16 | Explicit Galerkin parameters `r,m,q` for `a≤1` | Numerical request; analytic certification unresolved |
| A19 | Explicit heat height at exponent `(3/2+ε)/t` | Open |
| A20 | Jensen degree rung toward the saddle scale, past `d⁴≪T log T` | Open |
| A24 | Certified theta-column scans and brackets for `S*(a,b)` | Numerical request; analytic certification unresolved |
| A28 | Reciprocal-quadric traces as vanishing-cycle Frobenius traces | Open |
| A30 | Sharp stencil exponent under RH in `[1/4,1/2]` | Open |
| A37 | Resonator mean of `|ζ|²` for growing resonators below the Kronecker scale | Open |
| A42 | Uniform Gamma-weighted transport of the fixed-head theta asymptotic to the adaptive head | Open |
| A46 | Local singular indices beyond the cubic cutoff | Complete: `primeVertexRelativeIndex_eq_signedCount`, direct check and standard-axiom audit passed; already imported by umbrella |
| A54 | Bianchi resolvent cusp expansion with nonzero Wronskian for `Δ−3/4` | Open |
| A55 | Functional-equation rigidity for continuous Beurling prime measures with `L¹` or `L²` defect | Continuous perturbation counterexample under investigation; countable-system theorem does not apply |
| A68 | Landing countermodel with ζ's Gamma factor and Riemann–von Mangoldt counting | Open |
| A86 | Growing-order top-mode filter transfer and near-diagonal cofactor pairs | Open |
| A91 | General Dedekind-zeta comb and Hodge index for higher-degree number rings | Open |

Each completion requires its exact statement, paper proof, correctly placed Lean declarations,
umbrella import, direct `lake --old env lean` check, and transitive `#print axioms` audit.
Conditional infrastructure does not discharge missing analytic hypotheses. Refutations require
the strongest positive survivor and its formalization.

## A46: all cutoffs

For every ambient bound `B`, cutoff `N`, and label `p : Fin (B+3)`,
`primeVertexRelativeIndex B N p = primeVertexSignedCount B N p`.
The right side is the alternating sum over all prime supports `S` above
`p` with `p·∏S≤N`, including the empty face. The left side is defined
through actual relative singular homology. No cubic-cutoff hypothesis
remains. Finiteness of that homology and the global sum `1−M(N)` are also
proved. Invalid labels contribute zero.

Proof: contract the local block; retract its exit to the upper link; apply
the finite-face singular Euler theorem. Insert the least prime to partition
all nonempty faces for the global identity. Existing declarations in
`RenormalizedIntersectionArithmeticCounts/PrimeVertexSignedLocalization.lean`
passed direct `lake --old env lean` verification, including eleven transitive
audits with only `propext`, `Classical.choice`, `Quot.sound`. See
`3-formalized/riac-prime-vertex-signed-localization.md`.

## Continuous-measure test for A55

Candidate: add to the Riemann prime-power measure the positive pushforward of
`ε x exp(-x) dx`, `x>0`, under `x↦exp x`. Its Mellin transform is
`ε/(s+1)²`; the convolution-exponential zeta is therefore
`ζ(s) exp(ε/(s+1)²)`. On the critical line, reflection cancels the leading
inverse-square term: the multiplier difference is `O(ε|t|⁻³)`.
The elementary bound `|ζ(1/2+it)|=O(1+|t|)` then gives an `L¹∩L²` defect.
This would refute continuous-measure rigidity, even for
arbitrarily small defects. Required: prove the measure identity, the full
Hamburger strip conditions, both defect norms, and nontriviality. No part
of this counterexample is counted as complete. The complex Mellin identity for
positive convolution exponentials and the positive density's transform have
passed Lean checks with only the standard axioms; the full counterexample
and its positive survivor remain unformalized.

Write `Mε(s)=exp(ε/(s+1)²)`, `βε=Mε(1)/2`, and
`gε(t)=ζ(1/2+2it)[Mε(1/2+2it)−Mε(1/2−2it)]`.
The pole subtraction `Eε=MεΛζ−βεΓℝ(s−1)` extends holomorphically
across `1`: use the divided difference of `Mε` and the regularized Gamma
factor. Existing uniform vertical decay of `Λζ` and `Γℝ(s−1)` supplies
the Hamburger strip bound. The positive survivor sought is a nontrivial
positive continuous Euler family preserving all zero locations, with
`|gε(t)|≤C ε exp(ε)/(1+t²)` and arbitrarily small such majorants.
The added measure is Lean-verified atomless, of mass one, supported above `1`.
