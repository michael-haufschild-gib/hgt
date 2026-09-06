# Zeta zeros of a chronological fusion response

**Status:** the capacity, face-Euler, heat, continuous-reference, Mellin, zero-locus, and zero-multiplicity chain is formalized in Lean. Every participating leaf passed its final build and declaration axiom audit. This establishes the construction below; it does not establish a new field or priority. No assertion about the locations of zeta zeros is assumed or proved.

## Construction without zeta as an input

An ordered six-endpoint pairing is observed through five real gaps. Set S=a+b+c+d+e and use the cubic seed

`P(a,b,c,d,e)=27ace+S(b+c+d)c`.

Its two displayed diagram terms each have capacity one under total variation `|a|+|b|+|c|+|d|+|e|≤1`. Their sum has proved capacity K>1, attained on the curved response arc. In closed form,

`q=(50−√313)/81`, `K=27q(1−q)²/4+q²`.

For n independent blocks sharing one variation budget, normalize the product by `n^(3n)`. The actual capacity supremum is C_n=K^n. The empty product has capacity one. Logarithmic capacity therefore gives the additive levels

`E_n=log C_n=n a`, `a=log K>0`.

Here “level” means logarithmic observation capacity, with no physical Hamiltonian postulated.

## The geometric coefficient

Coalescence and terminal-gap deletion identify a physical unit-cost norming section for genuine pairing families. In cubic degree it is

`X={g≥0 : Σ_(i=0)^4 g_i=1, g_i g_(i+1)=0 for i=0,…,3}`.

CubicRealization proves that every nonempty listed face is realized by a uniform-mass physical probe, and that these are exactly the realized supports. Its maximal faces are `{0,2,4}`, `{0,3}`, `{1,3}`, `{1,4}`: a filled triangle and three further edges. The exact face polynomial, including the empty face, is

`f_X(z)=(1+z)^3+2z+3z²`.

Thus f_X(−1)=1 and the reduced Euler characteristic is −1. For n independent copies, use block-labeled vertices and the join face condition: every block fiber must be a face of X. Lean proves the face/fiber bijection, additivity of face cardinality, and multiplication of the signed face sums. Consequently the n-fold join has reduced Euler coefficient −1 for every n≥1. This proof uses actual finite face sets; it does not assume a homology recurrence or invoke an unproved sphere classification.

The single cubic section also has an explicit strong deformation retraction:

`H_t(g)=(g₀+t g₂/2,g₁,(1−t)g₂,g₃,g₄+t g₂/2)`, `0≤t≤1`.

Lean constructs the continuous maps and a mathlib `HomotopyRel` fixing the retract. The retract is explicitly homeomorphic to `|x|+|y|=1`, via `(x,y)=(g₀−g₁,g₃−g₄)`. This familiar path-complex topology is prior art; see [Przytycki–Silvero, Proposition 3.6](https://arxiv.org/pdf/2305.18648), whose path parameter counts edges.

## A convergent integral with exactly the zeta zeros

Weight each positive level by the reduced Euler coefficient of its join. The discrete trace and its continuous reference are

`H(t)=Σ_(n≥1) (−1) exp(−E_n t)=−1/(exp(a t)−1)`,

`C(t)=−∫₀∞ exp(−a t x) dx=−1/(a t)`, for t>0.

Both the convergent series and the improper reference integral are proved. Define B=H−C, extended by zero to t≤0. Neither trace, nor B, uses zeta or its zeros in its definition.

For t>0,

`B(t)=1/(a t)−1/(exp(a t)−1)`.

The estimates `0≤B(t)≤min(1,1/(a t))` give ordinary Mellin convergence throughout `0<Re s<1`. The exact identity is

\[
\boxed{\int_0^\infty t^{s-1}B(t)\,dt
=-a^{-s}\Gamma(s)\zeta(s),\qquad 0<\Re s<1.}
\]

For the unit-scale defect b(t), the algebraic relation `2b(2t)−b(t)=1/(exp t+1)` reduces this to the classical Fermi Mellin identity, [DLMF 25.5.3](https://dlmf.nist.gov/25.5.E3). The dyadic factor cannot vanish in the open strip. The scale factor and Gamma are also nonzero there. Lean therefore proves equality of the response and zeta zero sets, and equality of their analytic orders at every point of the strip. No analytic continuation of a divergent response integral is used for this domain.

## What the topology loses

For the five cubic readouts

`Aace+B ad(c+d+e)+C be(a+b+c)+D Sbd+E Sc(b+c+d)`,

the homotopy preserves the B,C,D part. Its endpoint kills the A,E part. Three explicit ring probes prove the exact restriction kernel: a readout vanishes everywhere on the ring iff B=C=D=0. In particular, the entire amplification seed P is killed.

Thus the geometric construction must retain both the probe space and its observation. The ring's homotopy type alone cannot recover the positive capacity scale used above. Applying the positive-spacing recipe to the zero restricted seed would violate that recipe's domain. CubicPairings, CubicArcNorm, CubicNorm, and CubicNormLaws now prove the exact decomposition M=max(J(A,E),4|B|/27,4|C|/27,|D|/4), its norm laws, and maximum attainment. The retraction is a contractive projection onto the three interval factors and loses precisely the curved J-factor.

## Formal endpoints and scope

Sources lie in `formal/GaloisForLFunctions/HTGeometry/ChronologicalTensor/`:

- `FusionCapacity`: actual suprema and logarithmic levels.
- `CubicComplex`, `CubicFaces`, `CubicRealization`, `CubicJoin`: physical section, exact finite faces, join Euler coefficients, and Euler heat.
- `CubicRetraction`, `CubicDiamond`, `CubicObservation`: actual homotopy, homeomorphism, and readout loss.
- `FusionHeat`, `FusionMellin`, `FusionDivisor`: summation, bounds, Mellin convergence, and analytic divisor.
- `GeometricFusion`: actual continuous reference integral and final `geometricFusionKernel_zeroLocus` / `geometricFusionKernel_zeroMultiplicity` theorems.

Only standard logical axioms `propext`, `Classical.choice`, and `Quot.sound` occur in the audited dependencies. No numerical certificate enters a proof. The classical Fermi integral is reused from the corpus without using its RH-equivalence endpoints.

The logarithm law, joins, Euler characteristic, Bose/Fermi sums, and Mellin identity are classical. The research candidate is their concrete coupling to chronological observation capacity and its failure to survive a homotopy retraction. A sufficient novelty audit remains open. Also distinguish this independent-block product from the variable-coalescence operation in [Lafay–Peltola–Roussillon, Definition 2.13](https://doi.org/10.1090/btran/233).

Verification snapshot, 6 September 2026: all 101 ChronologicalTensor leaves are wired and individually built; all 1049 declarations are axiom-audited. The index was refreshed and final authoritative global lint passed. Existing file-size warnings remain. No full build was run, and no task-owned Lean process remains.
