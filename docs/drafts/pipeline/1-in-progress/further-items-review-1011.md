# Further items: exact mathematical targets

- **ID:** further-items-review-1011
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Status:** Paused at user request. A37, A46, A55, A68 complete; ten items open.
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
| A37 | Resonator mean of `|ζ|²` for growing resonators below the Kronecker scale | Complete: `eventually_resonatorMean_zeta_uniform`, `0≤κ<2σ−1`; seven direct checks passed; umbrella wired |
| A42 | Uniform Gamma-weighted transport of the fixed-head theta asymptotic to the adaptive head | Open |
| A46 | Local singular indices beyond the cubic cutoff | Complete: `primeVertexRelativeIndex_eq_signedCount`, direct check and standard-axiom audit passed; already imported by umbrella |
| A54 | Bianchi resolvent cusp expansion with nonzero Wronskian for `Δ−3/4` | Open |
| A55 | Functional-equation rigidity for continuous Beurling prime measures with `L¹` or `L²` defect | Complete: rigidity refuted; arbitrarily small positive zero-preserving family formalized; six direct checks and standard-axiom audits passed; umbrella wired |
| A68 | Landing countermodel with ζ's Gamma factor and Riemann–von Mangoldt counting | Complete: `exists_riemann_gamma_counting_model_without_landing`; five direct checks and standard-axiom audits passed; umbrella wired |
| A86 | Growing-order top-mode filter transfer and near-diagonal cofactor pairs | Open |
| A91 | General Dedekind-zeta comb and Hodge index for higher-degree number rings | Open |

Each completion requires its exact statement, paper proof, correctly placed Lean declarations,
umbrella import, direct `lake --old env lean` check, and transitive `#print axioms` audit.
Further axiom checks were waived at user request; A37 has no complete transitive audit.
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

## A55: continuous-measure counterexample

Add to the Riemann prime-power measure the positive pushforward of
`ε x exp(-x) dx`, `x>0`, under `x↦exp x`. Its Mellin transform is
`ε/(s+1)²`; the convolution-exponential zeta is therefore
`ζ(s) exp(ε/(s+1)²)`. On the critical line, reflection cancels the leading
inverse-square term: the multiplier difference is `O(ε|t|⁻³)`.
The elementary bound `|ζ(1/2+it)|=O(1+|t|)` then gives an `L¹∩L²` defect.
This refutes continuous-measure rigidity, even for arbitrarily small
defects. Lean verifies the positive measure identity, nontriviality, zero
preservation, the full Hamburger strip certificate, `L¹`, `L²`, and
arbitrarily small inverse-square majorants. All six modules have successful
direct checks and standard transitive axioms. The umbrella imports
`ContinuousPrimeMeasuresAreNotRigidUnderFiniteDefects.lean`. The failed
rigidity route and its formalized positive survivor are recorded in
`5-failed/continuous-prime-finite-defect-rigidity.md`.

Write `Mε(s)=exp(ε/(s+1)²)`, `βε=Mε(1)/2`, and
`gε(t)=ζ(1/2+2it)[Mε(1/2+2it)−Mε(1/2−2it)]`.
The pole subtraction `Eε=MεΛζ−βεΓℝ(s−1)` extends holomorphically
across `1`: use the divided difference of `Mε` and the regularized Gamma
factor. Existing uniform vertical decay of `Λζ` and `Γℝ(s−1)` supplies
the Hamburger strip bound. The positive survivor is a nontrivial
positive continuous Euler family preserving all zero locations, with
`|gε(t)|≤C ε exp(ε)/(1+t²)` and arbitrarily small such majorants.
The base continuous measure is Lean-verified atomless, of mass one, supported above `1`.
The pole-subtracted remainder is holomorphic on `Re s>0`; the perturbed
zeta is meromorphic there. No continuation across `−1` is asserted.

## A68: Gamma-normalized landing calibration

The paired Xi ordinates give a real, FE-symmetric entire function of order
at most one, with simple off-line zeros approaching the line. Its positive
zero count differs from Xi's count by at most one. Entire decompletion
with `2/(sΓℝ(s))` gives a meromorphic function with residue one at `1`
and the Riemann Gamma completion. All five modules passed direct checks
and standard-axiom audits. See
`3-formalized/landing-calibration-with-the-riemann-gamma-factor.md`.
No Euler product or Dirichlet series is asserted.

## A37: uniformly growing resonators

For `1/2<σ<1` and `0≤κ<2σ−1`, the actual-zeta dyadic resonator mean
equals its full convolution diagonal up to `o(Σ|r_T(m)|²)`, uniformly
over arbitrary complex coefficients supported on positive integers at
most `T^κ`. All seven modules passed direct checks; the umbrella imports
`GrowingResonatorsKeepTheZetaMean.lean`. See
`3-formalized/growing-resonator-means-below-the-kronecker-scale.md`.

## A91: scope of the existing index law

`AbsoluteGeometryOfSpecZ/TheHodgeIndexOfANumberRingCountsTheZerosOfItsZetaFunction.lean`
proves the index law for a finite family of primitive Dirichlet characters:
the negative index counts distinct right zeros in their union with zeta's.
Its statement does not identify a general number field's Dedekind zeta or
its ideal-contact comb with that family. The general-field arithmetic
identification and comb limit remain required.
