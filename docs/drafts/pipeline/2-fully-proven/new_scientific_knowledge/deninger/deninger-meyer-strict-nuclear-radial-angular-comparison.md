# Deninger--Meyer strict nuclear radial--angular comparison

- **ID:** `deninger-meyer-strict-nuclear-radial-angular-comparison`
- **Stage:** 2-fully-proven
- **Type:** SOURCE TOPOLOGICAL COMPARISON THEOREM
- **Labels:** `DAC_MEYER_NUCLEAR_RADIAL_STRICTNESS`,
  `DAC_HILBERT_KUMMER_STRICT_ANGULAR_COSHEAF_CONTRACTION`
- **Parent:** `deninger-poisson-relevant-complex-comparison`
- **Statement:** Meyer's Poisson complex is a strict complex of
  nuclear Fréchet spaces, remains strict after tensoring with the
  finite-stage Tate--Milnor coefficient and passing to its strict
  pro-Ind limit, and the Hilbert--Kummer modulus angle contracts by an
  explicit topological chain homotopy without contracting the unitary
  phase.

## 1. Radial nuclear spaces

Write
\[
 \mathcal H_-
 =
 \bigcap_{s\in\mathbb R}
 \mathcal S(\mathbb R_{>0}^{\times})_s,
 \qquad
 \mathcal S(\mathbb R_{>0}^{\times})_s
 =
 \{f:x^sf(x)\in\mathcal S(\mathbb R_{>0}^{\times})\}.
                                                                    \tag{1}
\]
It is enough to intersect over \(s\in\mathbb Z\).  Let
\[
 \mathcal H_\cap
 =
 \{f\in\mathcal S(\mathbb R):
 f(-x)=f(x),\ f(0)=\widehat f(0)=0\}.                              \tag{2}
\]

`[PROVED HERE] [DAC_MEYER_NUCLEAR_RADIAL_STRICTNESS]`

Both `(1)` and `(2)` are nuclear Fréchet spaces.  The Poisson operator
\[
 Z:\mathcal H_\cap\longrightarrow\mathcal H_-,
 \qquad
 Zf(x)=\sum_{n\geq1}f(nx),                                       \tag{3}
\]
is a strict closed embedding.  Consequently
\[
 0\longrightarrow\mathcal H_\cap
 \xrightarrow{Z}\mathcal H_-
 \longrightarrow M_\zeta
 \longrightarrow0                                                \tag{4}
\]
is a strict exact sequence of nuclear Fréchet spaces.

### Proof

The even Schwartz space is a closed subspace of
\(\mathcal S(\mathbb R)\), and `(2)` is the common kernel of two
continuous functionals.  Hence `(2)` is nuclear Fréchet.

Exhausting the weights in `(1)` by the intervals \([-m,m]\) realizes
\(\mathcal H_-\) as the countable projective limit of the nuclear
Fréchet spaces
\[
 \mathcal S(\mathbb R_{>0}^{\times})_{[-m,m]}.
\]
Equivalently it is the closed compatibility subspace of the product
of the integer-weight Schwartz spaces.  Countable products and closed
subspaces of nuclear Fréchet spaces are nuclear Fréchet.

Meyer's zeta estimate and Poisson summation theorem prove that `(3)`
is continuous, has closed range, and is a topological isomorphism
onto its range.  The quotient in `(4)` is therefore Fréchet and
nuclear.

This proof also fixes the support convention.  \(\mathcal H_-\) is
not \(C_c^\infty(\mathbb R_{>0})\); in logarithmic coordinates it is
the nuclear Fréchet space of smooth functions decaying faster than
every exponential at both ends.  Compactly supported smooth functions
form a dense core.

## 2. Strict tensor transport

Let \(E_\nu^\bullet\) be a finite pro-Stein character-lattice and
finite relative Tate--Milnor cell stage.  Every term is a nuclear
Fréchet space: coherent finite-rank analytic pieces over a Stein torus
are nuclear, and finite cones, kernels, quotients, and sums preserve
nuclearity.

Grothendieck exactness for completed projective tensor product with a
nuclear Fréchet space applied degreewise to `(4)` gives
\[
 0\to
 E_\nu^\bullet\widehat\otimes_\pi\mathcal H_\cap
 \xrightarrow{1\widehat\otimes Z}
 E_\nu^\bullet\widehat\otimes_\pi\mathcal H_-
 \to
 E_\nu^\bullet\widehat\otimes_\pi M_\zeta
 \to0                                                           \tag{5}
\]
as a strict exact sequence of complexes.

The pro-Stein Tate--Milnor coefficient is the strict filtered union of
these finite stages in each fixed bidegree.  Filtered colimits of
complex vector spaces are exact, and the topology is the final strict
pro-Ind topology.  Passing `(5)` through the stages therefore gives
the same strict sequence for the full phase coefficient
\(E_{\mathrm{phase}}^\bullet\).

The mixed \(L^1/L^2\) Kummer maps and the nuclear test-space maps are
continuous on every finite stage, hence on the final topology.
Density survives completed tensoring because the algebraic tensor of
dense subspaces is dense.  For the all-prime residue graph no general
tensor-flatness claim is needed:
`DAC_STRICT_PRO_LOG_COLLAR_SECTION` and
`DAC_COMPLETED_ARAKELOV_TRACE_KERNEL` give split strict boundary
sequences, and completed projective tensor product preserves an
explicit continuous splitting.  Thus `(5)` is compatible with:

1. the nuclear Kummer test topology;
2. the mixed \(L^1/L^2\) completion;
3. the completed finite-residue graph;
4. the real homology-current boundary;
5. the two endpoint functionals.

The dilation flow is continuous on `(1)`--`(2)`.  Meyer's theorem,
not a formal interchange of an infinite sum, defines `(3)` in these
topologies.  Deninger's identity
\[
 [F_nP,u]=[P,nu]=\phi^{\log n}[P,u]
\]
then identifies each summand with the corresponding source flow
pullback.

## 3. Angular cosheaf contraction

Let \(H=H_{\mathrm{Kum}}\) and \(S(H)\) be its unit sphere.  Use the
augmented topological singular-chain cosheaf
\[
 \epsilon:C_\bullet^{\mathrm{top}}(S(H))\longrightarrow\mathbb R,
                                                                    \tag{6}
\]
where each chain space has the free locally convex direct-sum topology
on singular simplices.  A continuous map or homotopy induces a
continuous chain map or prism operator.

The explicit contraction in
`DAC_DENINGER_HILBERT_KUMMER_POLAR_ANGULAR_CONTRACTION` gives a
continuous prism homotopy
\[
 \operatorname{id}
 \simeq
 \iota\epsilon                                                   \tag{7}
\]
for a chosen point inclusion \(\iota\).  Hence `(6)` is a split
chain-homotopy equivalence in complete locally convex complexes.

`[PROVED HERE]
[DAC_HILBERT_KUMMER_STRICT_ANGULAR_COSHEAF_CONTRACTION]`

For every complete phase/radial complex \(A^\bullet\), functoriality of
completed projective tensor product extends `(7)` to
\[
 C_\bullet^{\mathrm{top}}(S(H))
 \widehat\otimes_\pi A^\bullet
 \simeq
 A^\bullet.                                                       \tag{8}
\]
This is a continuous chain-homotopy equivalence, so it is stronger
than a bare cohomology isomorphism and remains valid for the nuclear,
mixed, residue-graph, and endpoint topologies above.

The positive rational flow multiplies \(h\in H\) by a positive scalar
and therefore fixes \(h/\|h\|\).  Thus `(8)` commutes with every
Poisson dilation and with their already-defined sum `(3)`.

For compact Galois descent, the augmentation `(6)` is equivariant even
though the chosen contraction need not be.  Continuous invariants are
exact on the complete coefficient modules used here by normalized
Haar averaging.  Applying invariants to `(6)` therefore preserves its
strict quasi-isomorphism.

## 4. Apex and unitary phase

The polar product is
\[
 X_{\mathrm{unit}}\times S(H)\times\mathbb R_{>0}.
\]
Only \(S(H)\) is contracted.  Fibrewise adjoining \(h=0\) forms the
cone on \(S(H)\), so `(8)` extends to
\[
 X_{\mathrm{unit}}\times H
 \rightsquigarrow
 X_{\mathrm{unit}}\times\mathbb R_{\geq0}.                        \tag{9}
\]
The unitary character factor remains the Tate--Milnor phase
coefficient at every radius, including zero.

On the radial Schwartz domain,
`DAC_RADIAL_KAHLER_ENDPOINT_FOURIER_TRACE` identifies the two relative
boundary maps as
\[
 f\longmapsto f(0),
 \qquad
 f\longmapsto\frac{\pi}{2}\widehat f(0).                          \tag{10}
\]
Therefore the relative common kernel is exactly
\(\mathcal H_\cap\).  No angular class and no extra “Fourier boundary
point” survives.

## 5. Arithmetic consequence

The Hilbert--Kummer bounded locus is used as its own fine ringed
source, with the continuous map to Deninger's pointwise coarse
approximation.  Sheafification means derived pushforward along this
map; boundedness need not be a local property of the coarse topology.

Equations `(5)`--`(10)` close the following parts of
`DAC_DENINGER_POISSON_RELEVANT_COMPLEX_COMPARISON`:

- radial nuclear sheaf/cosheaf topology;
- strictness and closed range of the Poisson differential;
- compatibility with mixed Kummer and completed residue topologies;
- strict angular contraction after retaining the phase coefficient;
- correct treatment of the unitary apex and both endpoint maps.

The remaining comparison is arithmetic gluing: identify the
finite-residue/real-boundary totalization of the intrinsic source
middle complex with `(4)`, and prove cup/trace compatibility.

## Hostile audit

- Ordinary contractibility alone is not used to preserve completed
  tensors; the continuous prism homotopy `(7)` supplies explicit
  splittings.
- No Haar probability measure on the infinite-dimensional sphere is
  asserted.
- No compact support is imposed in the angular direction.
- The phase factor is not contracted.
- Meyer's closed-range theorem supplies the infinite Poisson sum; no
  unjustified termwise convergence in a new topology is asserted.
- No zeta zero, spectral divisor, Weil positivity, RH, CCM object, or
  numerical computation enters the construction.

## References

- Ralf Meyer, *A spectral interpretation for the zeros of the Riemann
  zeta function*, especially Theorem 4.1:
  https://arxiv.org/abs/math/0412277.
- Alexander Grothendieck, *Résumé des résultats essentiels dans la
  théorie des produits tensoriels topologiques et des espaces
  nucléaires*, Ann. Inst. Fourier 4 (1952), 73--112:
  https://doi.org/10.5802/aif.46.
- Christopher Deninger, *Dynamical systems for arithmetic schemes*,
  §6 and §12: https://arxiv.org/abs/1807.06400.

## Log

- 2026-07-27 — Proved nuclearity and strict tensor stability of
  Meyer's Poisson complex and upgraded Hilbert--Kummer angular
  contractibility to an explicit strict cosheaf chain contraction.
