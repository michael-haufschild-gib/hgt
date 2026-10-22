# Topological spectrum of chronological observation

**Status:** new research branch requested by the user: zeta zeros should emerge within chronological geometry, without studying RH. The mechanism below is a paper-level construction, not yet a Lean theorem or an established novelty claim. No numerical experiment is needed.

## Candidate mechanism

For degree d≥1 pairings, coalescence leaves nonadjacent physical gaps. On the **unit-variation section**, this is the independence complex K_d of the path on 2d−1 gaps. The sparse set with variation **at most** one is a contractible cone and must not be used for this homology claim. Positive-degree homogeneity gives the same capacity on the unit section. Coalescence and preservation of the zero terminal coordinate are now formalized; the unit-section normalization and actual face/cohomology bridges are next.

The classical path-complex classification gives:

- K_(3k+1) contractible;
- K_(3k+2) homotopy equivalent to S^(2k);
- K_(3k+3) homotopy equivalent to S^(2k+1).

Consequently the direct sum, over all pairing degrees d≥1, of reduced rational homology has exactly one generator in every homological degree r≥0. This is a derived multiplicity, not a chosen list of zeta zeros. Grade by r+1 (the number of vertices of an r-simplex), and use the usual Euler sign (−1)^r. Pairing successive even and odd homological degrees yields the convergent response

`T(s) = Σ_(k≥0) [(2k+1)^(−s) − (2k+2)^(−s)]`, Re s>0.

Pairing is essential in this half-plane. Each difference is an integral of `s x^(−s−1)` over [2k+1,2k+2], so its absolute value is at most `|s|(2k+1)^(−Re s−1)`. The series converges locally uniformly. On Re s>1, separating even terms in the absolutely convergent zeta series gives `T(s)=(1−2^(1−s))ζ(s)`. Analytic continuation gives the identity on Re s>0, with the removable value at s=1 interpreted by T. Inside 0<Re s<1 the prefactor cannot vanish: its exponential term has modulus `2^(1−Re s)>1`. Thus T vanishes exactly at the zeta zeros there, with the same multiplicities. Nothing restricts the real parts of those zeros.

Equivalent heat trace: `Σ_(r≥0)(−1)^r exp(−(r+1)t)=1/(exp(t)+1)` for t>0. Its Mellin transform is Γ(s)T(s). This is the classical Fermi/eta identity; the proposed geometric contribution is deriving the graded trace from the norming complexes of endpoint-pairing observations.

## What makes this a substantive target, and what does not

The chain to prove is **pairing products → cost-preserving coalescence → norming complexes → graded topological classes → exact response divisor**. Merely defining T using the displayed series would formalize eta, not this chain. An Euler-characteristic recurrence alone also does not establish the individual homology groups or their grading.

The grading is homological degree plus one, not pairing degree or physical energy. Weighting by pairing degree instead produces a different combination of residue-class Dirichlet series; it must not be silently replaced by this grading. The zeros are cancellations of a complex graded response, not eigenvalues of a self-adjoint operator.

The established cubic retraction loses the curved observation plane while preserving topology. A useful next question is which observation-sensitive refinement distinguishes this lost metric data while retaining the topological zeta divisor. No such refinement is currently proved, and arbitrary multiplication by eta would not answer it.

## A sharper consequence: fusion removes every strip zero

For independently fused blocks, fixing the separating gap to zero makes the sparse probe complex the join of the two block complexes. Over the rationals, reduced homology of a join has grading `r=r₁+r₂+1`; occupation numbers `r+1` add. Thus the tower of ordered pairs has exactly j−1 classes at occupation j≥2. With the Euler-sign convention used above, its heat trace is **−H(t)²**, not H(t)²: reduced Euler characteristic acquires a minus sign under join.

Since `H(t)=1/(exp(t)+1)` satisfies `H²=H+H′`, integration by parts first on Re s>1 gives

`T_join(s) = η(s−1)−η(s)`.

Here T_join means the Mellin transform of −H² divided by Γ(s). The heat integral is holomorphic on Re s>0 (bounded at zero, exponentially decreasing at infinity), so the identity continues throughout that half-plane. At infinity the integration boundary vanishes exponentially; at zero it vanishes for Re s>1. The usual Γ recurrence supplies the coefficient of η(s−1).

For any zero ρ of ζ in 0<Re ρ<1, this yields `T_join(ρ)=η(ρ−1)≠0`. Indeed −1<Re(ρ−1)<0 contains no zeta zeros by the classical functional equation and zero-free right half-plane; the trivial negative-even zeros are outside this strip. The eta prefactor is also nonzero there. Therefore the single-block and two-block joined traces have **no common zero anywhere in the open critical strip**.

This is a concrete role for the zeros: a mode cancelled in the single-block topological response becomes visible after fusion. It is not a claim about their real parts. The heat identity is classical algebra and Mellin analysis; the remaining geometric obligation is the actual join/cohomology realization for the norming complexes. These statements have paper proofs here but no Lean proof yet. Higher fusion powers give finite combinations of shifted eta functions; their common-zero behavior remains open here.

## Prior art and novelty boundary

The path topology and hard-core fermion interpretation are known. [Przytycki–Silvero, §3.1, Proposition 3.6](https://arxiv.org/pdf/2305.18648) states the path homotopy classification (their path length counts edges). [Huijse–Schoutens, §5.1, Theorem 2](https://arxiv.org/abs/0903.0784) states the open-chain cohomology by chain length and fermion number. [Fendley–Schoutens–de Boer](https://doi.org/10.1103/PhysRevLett.90.120402) constructs supersymmetric hard-core lattice models. These are substantial overlaps; the topological tower or its Fermi interpretation cannot be advertised as invented here.

Corpus searches: exact phrase `"independence complex"` returned only unrelated symbol-name coincidences. Existing `SalemFermiModeIntegral.lean` and eta-pair modules contain the classical analytic identity; their RH equivalence endpoints are outside this branch. Broad literature searches did not establish priority for the coupling to chronological observation norms. Absence of a search hit is not evidence of novelty.

## Next proof work

1. Coalescence is formalized. Finish the physical unit-section capacity and actual path-face bridges; exclude the cone and auxiliary terminal coordinate from the topological claim.
2. Define actual sparse face complexes; prove path reduction and graded homology, or explicitly keep that dependency unformalized. A recurrence-defined surrogate is insufficient.
3. Reuse or prove the paired-series analytic identity, then connect its coefficients to the actual homology theorem. State strip-wide zero equivalence without RH assumptions.
4. Prove the independent-block join bridge and the two-trace disjoint-zero theorem; distinguish Euler signs from occupation parity.
5. Investigate an observation-sensitive invariant coupling the erased curved subspace to this topological response. Keep this distinction visible in the compact working notes.
