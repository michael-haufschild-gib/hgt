# Algebraic-dilation independence over theta–Gamma coefficients

- **Stage:** 3-formalized
- **Type:** Theorem
- **Parent:** [three approaches, B](../1-in-progress/argon-three-orthogonal-rh-approaches.md).

## Theorem

All actual functions `ζ(rs)`, indexed by positive real algebraic `r`, are jointly
differentially algebraically independent over the concrete field
`ℂ(s)⟨Γ,θ₂,θ₃,θ₄,E₂⟩` in the common upper-end meromorphic field.

For every positive real algebraic `q`, the orbit `ζ(q^j s)`, `j≥0`, is jointly
differentially independent over this field exactly when `q≠1`. Thus no nonzero
finite polynomial in its jets, with coefficients in this field, vanishes for
`q≠1`. Expanding and contracting orbits are both covered; `q=1` repeats one
coordinate.

## Proof

1. **Actual source coefficients.** Set `F_r(s)=−r ζ'(rs)/ζ(rs)`. On every line
   `rσ>1`, the literal derivatives have the absolutely convergent expansion

   ```text
   F_r^(k)(σ+it) = Σ_p Σ_(m≥1)
     r (−mr)^k (log p)^(k+1) exp(−σmr log p) exp(−itmr log p).
   ```

   This follows from the von Mangoldt expansion of the logarithmic derivative,
   its differentiated series, and exact prime-power reindexing. Embed each
   term into the common atom `(p,α)` with `α=mr`. The embedding is injective;
   extension by zero preserves absolute summability and the actual series.

2. **Exact frequency collisions.** Baker linear independence of prime
   logarithms over algebraic numbers balances algebraic weights separately
   at each prime. A frequency supported on `D` distinct primes with positive
   algebraic weights therefore has no representation by fewer than `D`
   positive prime terms. Every representation with `D` terms permutes the
   same prime–weight pairs: positivity forces every target prime to occur,
   cardinality forces one occurrence per prime, and weight balance fixes its
   exponent. Scaled prime frequencies need not be globally independent.

3. **Prime-jet separation.** For a finite packet of distinct positive
   dilations `r_i`, the amplitude at the target atom `(p,r_j)` is the nonzero
   factor `log(p) exp(−σr_j log p)` times the row

   ```text
   V_(j,p)(i,k) = r_i 1_{r_j ∈ ℕ_{>0} r_i} (−r_j)^k (log p)^k.
   ```

   The positive-integer incidence matrix is triangular after ordering the
   dilations, with nonzero diagonal `r_i`. A linear form vanishing on all
   these rows outside any finite prime set gives a polynomial in `log p`
   with infinitely many roots; each coefficient vanishes, and triangularity
   kills the original form. Currying and deleting finitely many already-used
   primes extend this to arbitrary multilinear forms tested on distinct
   primes. This separation itself holds for positive real dilations.

4. **Top-degree extraction.** Suppose a nonzero polynomial relation among a
   finite rectangle of actual `F_r` jets vanishes on a common convergence
   line. Let `D` be its maximal supported degree. Absolute summability
   justifies the finite products and sums as one exponential series. Its
   Bohr coefficient at any target frequency on `D` distinct primes is zero.
   Step 2 kills all lower degrees and identifies each degree-`D` fiber with
   the finite sum over permutations of the target atoms. This is precisely
   the symmetric multilinear form of the top homogeneous component.
   Divide the nonzero decay factors and use Step 3: the form vanishes
   identically. Its diagonal is `D!` times the top component, contradicting
   a nonzero top coefficient over `ℂ`. Degree zero is included. Hence every
   finite logarithmic-jet rectangle is algebraically independent over `ℂ`
   as functions on every common convergence line.

5. **Actual rotated germs.** The functions `Y_r(z)=ζ(−irz)` and `F_r(−iz)`
   are analytic on `Im z>1/r`, and `Y_r` is nonzero there. Their literal
   logarithmic equation is `Y_r'/Y_r=iF_r(−iz)`. The `k`th derivative of
   the right-hand side is `i(−i)^k F_r^(k)(−iz)`, with nonzero scalar factor.
   A germ polynomial relation holds beyond some cutoff `H`. Choose a real
   `σ>H`, `σ>0`, and `r_iσ>1` for the finite packet, and evaluate at
   `z=i(σ+it)`. Step 4 forces the polynomial to be zero. Finite rectangles
   exhaust the full jet family. Coordinatewise replacement by logarithmic
   derivatives preserves differential independence: `Y_r` satisfies its
   first-order linear differential equation over its logarithmic coordinate,
   while that coordinate is a differential rational expression in `Y_r`.
   Thus the actual rotated zeta family is differentially independent over
   `ℂ` for every finite packet.

6. **Return to physical lines.** The rotated representative of a physical
   zeta jet is its rotated germ jet multiplied by `((−i)^k)⁻¹`. These nonzero
   coordinate factors preserve independence. Choose `a>0` with `r_i a>1`.
   A constant polynomial relation among physical jets on any line `σ>a`
   continues throughout the connected half-plane `Re s>a`; its rotated germ
   is zero, contradicting Step 5. Physical jets are therefore independent
   on that line. On `r_iσ≥2`, every jet is also continuous and Bohr almost
   periodic, by the zeta strip theorem, the exact chain factors `r_i^k`, and
   positive real reparametrization `t↦r_i t`.

7. **Concrete coefficient field.** Take `σ=2a`. The existing physical-line
   Gamma separation theorem applies to the actual analytic representatives
   of all jets in the finite dilation family. Gamma coefficient asymptotics
   and simultaneous Bohr recurrence reduce a relation to constants, which
   Step 6 excludes. Gamma stays in the original physical variable.
   Finite-subfamily independence yields the whole positive algebraic family.
   The actual theta constants and `E₂` are differentially algebraic over
   `ℂ(s)`; the proved theta–Gamma base-change equivalence preserves the full
   differential independence.

8. **Sharp orbit classification.** For positive algebraic `q≠1`, the powers
   `q^j` are distinct positive algebraic parameters, so restriction gives
   the orbit theorem. At `q=1`, its zeroth and first coordinates coincide,
   contradicting the injectivity required by algebraic independence.

No common convergence line for all positive algebraic dilations is assumed.
Every line is chosen after restricting to a finite family, including for
contracting orbits.

## Lean certificate

Main module: `ArithmeticHarmonicAnalysis/AlgebraicDilationThetaGammaIndependence.lean`.
Namespace: `GaloisForLFunctions.ArithmeticHarmonicAnalysis.GammaAlgebraic`.

- `finite_dilations_differentialIndependent_gamma`: each finite actual family.
- `zetaDilation_differentialIndependent_gamma`: all positive algebraic dilates.
- `zetaDilation_differentialIndependent_thetaGamma`: the stated concrete field.
- `mahlerZetaMero_differentialIndependent_iff`: exact multiplier classification.
- `mahlerZeta_no_polynomial_relation`: exclusion of nonzero finite mixed jet polynomials.
- `mahlerZeta_representative`: literal physical representative `s↦ζ(q^j s)`.

The supporting source theorems are
`AlgebraicDilationJetIndependence.source_jets_line_algebraicIndependent`,
`AlgebraicDilationGermIndependence.rotatedZetaMero_differentialIndependent`, and
`AlgebraicDilationPhysicalJets.dilate_jets_line_algebraicIndependent`.
Their imports contain the exact Baker collision classification, common-atom
series, multilinear separation, and coefficient-preserving polarization.

All twelve direct production checks passed without diagnostics. Their 78
transitive axiom audits use only `propext`, `Classical.choice`, and `Quot.sound`.
The ArithmeticHarmonicAnalysis umbrella imports all twelve modules.

## Scope

Baker independence, the general Bohr coefficient machinery, physical Gamma
separation, finite-subfamily principles, and theta base change already existed.
The source-level contribution is exact positive algebraic frequency collision
control combined with actual dilation coefficients and prime-jet separation.
It closes the algebraic irrational extension without pretending that scaled
prime frequencies are independent. No literature-priority claim is made.

This excludes the specified positive algebraic differential–Mahler realization.
Transcendental multipliers, arbitrary variable period coefficients, special-value
relations, and other nonlinear Böttcher realizations remain outside the result.
No RH conclusion follows.
