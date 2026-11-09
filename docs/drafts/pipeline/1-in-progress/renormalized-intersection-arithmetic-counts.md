# Renormalized intersection theory of arithmetic counts

- **ID:** RIAC
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** [review 0811](../../../reports/review-0811/obstacles-summary.md)
- **Statement:** Prove square-root-scale signed cancellation of the actual local indices, using independent arithmetic counts, product-formula heights or completed invariants.

## Target and existing foundations

The governing quantity is `S(N)=Σ_p index_p(N)=1−M(N)`. The RH-scale
objective is `|S(N)|≪ε N^(1/2+ε)` for every `ε>0`. A strict `O(√N)`
estimate is a stronger question. Each auxiliary construction must identify
its mechanism for controlling this signed sum; quadratic scaling alone
is insufficient. No such cancellation estimate is proved.

Programme [README](../../../../formal/GaloisForLFunctions/RenormalizedIntersectionArithmeticCounts/README.md).
ESG supplies the actual cutoff complexes and persistence classification.
HHAC supplies the renormalized torsion operators for `δ>0`, arithmetic prime
blocks and the critical mixed-row obstruction. Existing RIT retains ownership
of its Hodge/scattering constructions.

## Open constructions

1. A [surface count](../0-backlog/riac-surface-riemann-roch-count.md) with
   integer quadratic Riemann–Roch scaling on Hecke correspondences, independent
   of `Q`, with independently proved sign control.
2. Critical `δ=0` torsion compensation, including the archimedean place.
3. A completed prime chain complex with proved `s`-dependent zero detection.
4. A canonical relative pair on the connected core with Euler number `M(N)`;
   signed localization of the full complex is constructed below.
5. A Farey cell realization with a modular action and controlled cutoff boundary.

First formalized branch: [prime-star compensation](../3-formalized/riac-prime-star-compensation.md):
exact minimal payment, unrestricted diagonal classification, explicit negative
probes, logarithmic-square obstruction and sharp power boundary.
Second formalized branch: [completed prime boundary](../3-formalized/riac-completed-prime-boundary.md).
The faithful dense weighted embedding admits a closed extension of the actual
augmentation exactly when `2 Re(s)+δ>1`, with unique bounded extension and
exact norm. At and below the boundary, explicit finite packets obstruct every
closed extension. The [critical exterior classification](../3-formalized/riac-critical-exterior-graph-closure.md)
now identifies that relation as the whole source–target Hilbert product in
every exterior degree, retaining the original finite-support chains and
their conductor norm. These critical closures retain no boundary constraint.
The [bounded-region graph comparison](riac-prime-boundary-graph-closure.md)
remains separate.
The [higher-degree question](../0-backlog/riac-completed-prime-koszul.md)
is whether the standard completed complex remains contractible above that threshold.
The [logarithmic compensation boundary](../3-formalized/riac-logarithmic-star-compensation.md)
is also formalized: leaf growth `(log p)^α` admits finite payment exactly
for `α>2`, with minimal positive completion and explicit negative probes.
The [vertical unitary graph comparison](../3-formalized/riac-unitary-prime-chain-gauge.md)
is formalized in every exterior degree, preserving the prescribed conductor
norms and the actual finite boundary graph closures.
The [full logarithmic torsion candidate](riac-logarithmic-torsion-completion.md)
asks for the sharp extension from prime stars to every conductor interaction.
The [canonical cone-pair candidate](../0-backlog/riac-relative-cone-normalization.md)
separates an actual relative-homology construction from a mere Euler subtraction;
it does not yet supply localization on the core.
The [modular filtration candidate](../0-backlog/riac-modular-height-filtration.md)
replaces an invariant finite cusp set by a moving cutoff with explicit matrix
height distortion; the prime-face comparison remains missing.

The [signed localization theorem](../3-formalized/riac-prime-vertex-signed-localization.md)
constructs an arithmetic self-map, actual local isolating blocks and exits,
and finite relative singular homology. Its local indices sum to `1−M(N)`;
the core sum is `1−M(N)−P_N`. Local definitions use only prime products.
The indices are unbounded below, allowing signed cancellation without a
quantitative bound. The [exit-bouquet classification](../3-formalized/riac-prime-exit-bouquet.md)
constructs the full arithmetic homotopy type of each exit, with sphere labels
in the exact multiplicative window determined by the least upper neighbour.

The [integer gluing count](../3-formalized/riac-integer-gluing-count.md)
now gives a direct integer realization of the aggregate target. Its
relations are divisor sums on `e_1,…,e_N` and `Σ_(j≥2)e_j=0`, defined
without Möbius sums or local indices. The actual quotient satisfies
`G_N≃ℤ/(1−M(N))ℤ`; its oriented determinant equals the signed local-index
sum. It is finite exactly when that sum is nonzero, with cardinality
`|1−M(N)|`; otherwise it is infinite cyclic. Its proved primary
decomposition yields `H_N=Σ_p v_p(#G_N)log p=log|1−M(N)|` on finite
quotients. The square-root height upper bound and the full count on Hecke
correspondences remain open.

The [actual divisor-lattice geometry](../3-formalized/riac-divisor-relation-geometry.md)
constructs its saturated integral basis and proves Gram volume
`V_N=√Q(N)≤√N`, where `Q(N)` counts squarefree labels. The actual Euclidean
nearest projection gives `|Σ_p index_p(N)|=V_N D_N` and finite-quotient
height `H_N=½log Q(N)+log D_N`. Unit changes remove Möbius signs from the
Gram matrix; the arithmetic gluing displacement retains them.
The required independent bound `D_N=Oε(N^ε)` remains open.

The [integral section theory](../3-formalized/riac-integral-section-height.md)
minimizes squared length over actual representatives of `ℤ^N/L_N`.
For charge `k=qa+r`, every minimizer is classified and their number is
`binomial(q,r)`. The exact addition defect is `−2 min(ρ(c),ρ(d))`;
normalized doubling decreases to `k²/q`. On the original gluing class,
minimum size equals `|S(N)|` and Tate height equals `D_N²`.
The logarithm of the minimizer count instead has zero Tate limit.
The actual [Gaussian section sum](../3-formalized/riac-gaussian-section-height.md)
provides a nonzero log-count height. Integral normal translation makes
its error from `tk²/q` periodic modulo `q`. The
[finite-height comparison](../3-formalized/riac-gaussian-section-positivity.md)
proves `tk²/q≤H_N(c,t)≤tE_N(c)` and error at most `tq/4`, using actual
lattice Poisson summation and paired integral sections. Its addition
defect lies in `[-tq,tq/2]`. On the original gluing class, class-dilation
has Tate limit `tD_N²`, while `lim_(t→∞)H_N([b],t)/t=|S(N)|`.
Finite dilation by `q` also gives `H_N(qc,t)=tqk²`. These are fixed-conductor
laws; an independent subpower displacement bound remains open.

The [uniform finite-rate comparison](../3-formalized/riac-uniform-gaussian-height.md)
sets `a_N=π+2log(4(N+1))`, `t_N=π²/(2a_N)` independently of the class.
It proves `0≤H_N(c,t_N)−t_N k²/q≤2/(N+1)` for every class and
`0≤H_N([b],t_N)/t_N−D_N²≤4a_N/(π²(N+1))` on the original gluing class.
An explicit integer coding bounds the actual dual Gaussian sum by
`θ(a/2)^(N+1)`; removing its zero frequency controls the shifted log-count
ratio. This removes the conductor-sized approximation error. An independent
upper bound on the distinguished height remains missing.

The [proper arithmetic intersection count](../3-formalized/riac-thickened-intersection-counts.md)
constructs actual finite rings `ℤ[X]/(P,Q)`, proves their resultant cardinality,
and gives quadratic integer prime-local multiplicities and logarithmic heights
under equal thickening. Distinct cyclotomic counts recover the established
torsion intersection. The [rational-radius construction](../3-formalized/riac-rational-abel-intersection-counts.md)
now realizes Abel energy by actual integral quotient counts. An explicit
residual exact sequence removes the coincident-root factor, prime by prime;
the diagonal count is the absolute discriminant. Normalized residual counts
converge to that diagonal height with the proved finite-radius error sign.
The critical sign and the comparison controlling the signed local-index
sum remain open.

The [prime-quadratic arithmetic family](../3-formalized/riac-prime-quadratic-counts.md)
defines `F_n=∏_(p^a∥n)(X²+p)^a` independently of Möbius coefficients.
For `N≥1`, its actual real orientation count is `R_N=N+M(N)`, with original
local indices `Σ_p index_p(N)=N+1−R_N`. The same equation gives actual different
quotients and prime-local/archimedean product-formula heights. Repeated
factors make those quotients infinite; every nontrivial conductor square
therefore leaves the finite-count locus. Global rational fibres instead
give `N+2−Q(N)` and lose the signed orientation. The exact cross-resultant
multiplication law survives. A [uniform geometric bound](riac-prime-quadratic-orientation-cover.md)
for the centred real count remains open. The
[residue-duality comparison](../3-formalized/monic-residue-duality.md)
identifies the actual trace cokernel of the monogenic order with its different
quotient, including repeated factors, and proves equality of absolute trace
and polynomial discriminants. Their signed equality remains open.

The [finite-field orientation count](../3-formalized/riac-finite-field-orientation-counts.md)
constructs actual square-root fibres of residue-field trace discriminants.
Their signed fibre counts recover polynomial Möbius signs. The aggregate
count uses established polynomial cancellation. A separate
[independent Frobenius orbit count](../3-formalized/riac-independent-frobenius-orbit-counts.md)
now derives `q^n` from normal-basis bijections and actual transporter sets.
The [signed orbit refinement](../3-formalized/riac-finite-field-signed-orbits.md)
constructs local weights in `{-1,0,1}`, proves collision cancellation and
retains Frobenius sign on distinct roots. Their total cancels independently
for at least two labels. The [arithmetic Vieta correspondence](../3-formalized/riac-arithmetic-vieta.md)
now identifies these stable root orbits with actual monic coefficient
polynomials, retaining all multiplicities. The [actual root-cover count](../3-formalized/riac-root-orientation-cover.md)
now proves `q^n` points independently of polynomial Möbius sums, through
fibres of size one, two or zero. The [integral discriminant equation](../3-formalized/riac-integral-discriminant-cover.md)
presents these points in ordinary coefficient coordinates, identifies their
equation with `Polynomial.discr`, and matches every discriminant character
with its signed transporter weight. The [cross-resultant comparison](../3-formalized/riac-discriminant-cover-signed-counts.md)
constructs an actual bijection with the factor-trace cover and proves
`w(f)=(-1)^deg(f) μ(f)` over odd fields, giving independent polynomial Möbius cancellation.
Identification with integer local indices remains open.

The [orientation quotient](../3-formalized/riac-orientation-quotient-counts.md)
realizes the total local weight as an integer difference of actual stable
orbit counts, retaining all stabilizers and both orientation labels.
The [elliptic divisor branch](../3-formalized/riac-elliptic-squarefree-divisor-cancellation.md)
constructs even/odd squarefree-divisor counts from actual closed places;
it proves `|E_n−O_n|≤8(n+1)²(√3)^n` and the prefix bound
`|Σ_(k≤n)(E_k−O_k)|≤24(n+1)²(√3)^n` on the actual elliptic curve over
`F₃`. The closed-place cutoff is exhaustive, infinity is retained, and the
Frobenius root bound is proved for the actual curve. These bounds do not
transfer to integer local indices without a further arithmetic comparison.
The [actual Frobenius-fibre theorem](../3-formalized/riac-elliptic-frobenius-orbits.md)
identifies projective-point orbits with supported closed-place fibres,
including infinity. The [stable-configuration theorem](../3-formalized/riac-elliptic-stable-orientation.md)
now identifies actual `n`-point configurations with degree-`n` squarefree
divisors and proves their intrinsic Frobenius orientation formula.
Their signed sum satisfies `J_n=(-1)^n(E_n−O_n)` and the same square-root
bound. The [original orientation-quotient counts](../3-formalized/riac-elliptic-orientation-quotients.md)
also have their complete comparison: `A_n−B_n=J_n`, hence
`|A_n−B_n|≤8(n+1)²(√3)^n`. They are defined independently from actual
point tuples and orientation labels; signed transporter counting retains
all collisions and proves the identification. The integer-height
comparison remains open.

The [conductor-compatible section module](../3-formalized/riac-hecke-stable-arithmetic-sections.md)
is the independent quotient by nonsquarefree coordinates. Its common-kernel
classification retains every dilated Möbius charge, and its gluing class
recovers the original local-index sum. The single-charge quotient admits no
ordinary prime dilation. On the full replacement, prime dilation is nonzero
but square-zero, so every normalized height with `H(T_p x)=pH(x)` vanishes.
This distinguishes additive class dilation from conductor multiplication;
a geometric correspondence action supporting a nonzero height remains open.

## Necessary distinctions

`Σ_faces(−1)^card=M(N)+P_N` for the core. For `N≥4`, its ordinary
topological Euler characteristic is `1−M(N)−P_N`. Relative subtraction must respect this sign.
Integer-valued `χ` alone is not a nonnegative count. Positive raw torsion
forms alone do not make their renormalized limit positive.

## Calibration

Curves: Manin, Stepanov, Rosati; polynomial prime complexes over finite fields.
The [general hyperelliptic orientation counts](../3-formalized/riac-curve-orientation-square-root.md)
satisfy `|A_n−B_n|≤(2q+2)(n+1)^(m−1)(√q)^n` for every squarefree
odd-degree `f` over an odd finite field, with `m=deg f` and `q=#F`.
Actual fixed-point counting, the permutation determinant and finite-degree
Newton comparison give the exact reciprocal-zeta coefficient; the derived
Stepanov theorem supplies every root bound. No splitting, simple-root or
cancellation premise remains. This proves the general curve calibration;
the integer-height comparison with `1−M(N)` remains open.
Countermodels: Golden, complex fake, shifted data and genus-two graph.
Retain full probe rank, both degrees plus primitive data, linear Betti mass,
isolated-prime fixed points and the square-root Euler lower law.

## Completion standard

Each claimed theorem needs a dependency-closed proof, direct Lean check and
transitive axiom audit. A failed mechanism needs its strongest positive
survivor. Full programme completion requires the five constructions and their
calibrations; the presently verified foundations do not discharge them.
