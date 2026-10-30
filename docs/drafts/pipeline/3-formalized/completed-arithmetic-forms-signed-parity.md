# Parity transfer and the escaping mixed rank

**ID:** completed-arithmetic-forms-signed-parity  
**Stage:** 3-formalized  
**Type:** Exact source transfer and rank boundary

For a real moment sequence $m$, define $s(2k)=m_k$ and $s(2k+1)=0$.
The bijection taking the two coordinate lists to $2i$ and $2i+1$ gives
$$
H_N(s)\cong H_{\lceil N/2\rceil}(m)\oplus
H_{\lfloor N/2\rfloor}(m_{\cdot+1}).
$$
This is an equality after simultaneous row and column reindexing. Positive definiteness,
positive semidefiniteness, and determinant therefore split exactly into the two parity blocks.
There are no omitted mixed entries: all cross-parity entries are the literal odd zeros.

The complete native signed theta jets have precisely this interleaving. The actual-source
shifted tail theorem makes each of the two required blocks positive definite on a cofinal ray.
Their finite intersection makes every fixed full native signed Hankel head positive definite.
The horizon depends on its rank; this says nothing about compact-center compensation or an
integrated all-order cone.

For the first atom, multiplication by the positive first-atom mass and powers of the positive
physical scale is an invertible diagonal congruence. It carries each balanced shifted head
to its literal signed moments. Parity transfer then makes every fixed full first-atom signed
head positive definite on a cofinal ray.

Let $\kappa(x)$ be the least dimension of a first-atom full signed Hankel head that is not
positive semidefinite. The negative signed moment theorem makes this dimension finite at
every center. For any fixed $K$, all heads of dimension at most $K$ are eventually positive
definite, so $\kappa(x)>K$ eventually. Thus $\kappa(x)\to\infty$.
If $\nu(x)$ is the least negative signed moment order, its diagonal occurs in dimension
$\nu(x)+1$, giving $\kappa(x)\le\nu(x)+1$. Mixed entries can cause an earlier failure.

Lean: `CompletedArithmeticForms/SignedParityTransfer.lean`,
`finiteHankelMatrix_parity`, `det_finiteHankelMatrix_evenMomentSequence`,
`finiteHankelMatrix_evenMomentSequence_posDef_iff`,
`finiteHankelMatrix_evenMomentSequence_posSemidef_iff`, and `nativeSignedHead_posDef_eventually`;
`CompletedArithmeticForms/FirstAtomRankBoundary.lean`,
`firstAtomSignedHead_posDef_eventually`, `firstAtomFailureRank_le_negativeOrder_succ`,
and `firstAtomFailureRank_tendsto`.
Kernel dependencies: `propext`, `Classical.choice`, `Quot.sound`.
