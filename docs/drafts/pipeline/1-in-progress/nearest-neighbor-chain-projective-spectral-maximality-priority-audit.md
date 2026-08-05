# Priority audit — generic maximal projective rank in a local quantum chain

- **Object audited:** `../3-formalized/nearest-neighbor-qudit-projective-spectral-maximality.md`
- **Audit date:** 2026-07-29; current-source refresh 2026-08-05
- **Status:** `[PRIMARY AUDIT COMPLETE TO CURRENT SEARCH]`
  `[NO EXACT COLLISION FOUND] [PROVISIONALLY NEW]`
- **Claim whose priority matters:** for every fixed \(q\geq2\), in the full
  real coupling space of arbitrary one-site and nearest-neighbour two-site
  qudit Hamiltonians on an open path,
  Lebesgue-almost every Hamiltonian has no rational affine relation among its
  \(q^n\) eigenvalues except trace. Equivalently, its projective spectral rank
  is \(q^n-1\).

## Exact-object distinction

The claim is not any of the following weaker statements:

1. generic simplicity of the energy levels;
2. nondegeneracy of pairwise energy gaps;
3. a fixed finite-order \(q\)-no-resonance condition;
4. random-matrix level statistics;
5. rational independence of \(O(n)\) one-particle energies in a free model;
6. a recurrence bound for an unrestricted random Hamiltonian.

It excludes every integer or rational relation
\[
 \sum_{j=1}^{q^n}m_jE_j=0,\qquad \sum_jm_j=0,
 \qquad m\in\mathbb Z^{q^n},
\]
simultaneously, for a static bounded-degree finite-range Hamiltonian family.
In particular it implies every finite-order \(q\)-no-resonance condition
simultaneously, whereas most equilibration sources assume one such condition
or control only one finite order.

## Primary-source comparison

| Source | What is established or assumed | Why it does not presently collide |
|---|---|---|
| Linden, Popescu, Short and Winter, *Quantum mechanical evolution towards thermal equilibrium* (2009), [arXiv:0812.2385](https://arxiv.org/abs/0812.2385) | Equilibration under a nondegenerate-energy-gap condition. | Nondegenerate gaps are a hypothesis used for dephasing, not an all-order rational-independence theorem for local coupling space. |
| Short, *Equilibration of quantum systems and subsystems* (2011), [arXiv:1012.4622](https://arxiv.org/abs/1012.4622) | Re-derives equilibration results under nondegenerate energy gaps and large effective dimension. | Again assumes or weakens gap multiplicity; it does not prove maximal projective rank. |
| Keating, Linden and Wells, *Spectra and eigenstates of spin chain Hamiltonians* (2015), [arXiv:1403.1121](https://arxiv.org/abs/1403.1121) | Proves Gaussian limiting density of states and eigenstate-entanglement results; notes generic nondegeneracy of eigenvalues for a broader chain family. | Simple spectrum is order-zero information. It neither excludes repeated nonzero gaps nor arbitrary rational affine relations. |
| Wells, *Quantum spin chains and random matrix theory* (2014), [arXiv:1410.1666](https://arxiv.org/abs/1410.1666) | Studies random nearest-neighbour chain ensembles, Gaussian density of states, numerical level correlations and simple spectra for many translation-invariant examples. | It supplies ensemble and numerical spectral evidence, not an all-order arithmetic theorem. No maximal projective rank or rational-independence statement for the static local coupling space is proved. |
| Riddell and Pagliaroli, *No-resonance conditions, random matrices, and quantum chaotic models* (2024), [arXiv:2307.05417](https://arxiv.org/abs/2307.05417) | Studies finite-\(q\) no-resonance conditions statistically in random matrices and a chaotic model, finding Poisson rather than repulsive sum statistics and allowing violations. | It explicitly describes higher no-resonance as usually assumed and studies statistics/violations. It gives no all-\(q\), almost-every local-chain theorem. |
| Riddell and Bertini, *Rationally independent free fermions with local hopping* (2024), [arXiv:2404.12100](https://arxiv.org/abs/2404.12100) | Engineers rational independence of the single-particle energies in one-dimensional free-fermion models. | Many-body energies remain additive combinations of only \(O(n)\) one-particle frequencies, so their projective rational rank is at most \(O(n)\), not \(2^n-1\). The construction also uses system-size-dependent hopping ranges indexed by divisors. |
| Huang, *Extensive entropy from unitary evolution* (2021), [arXiv:2104.02053](https://arxiv.org/abs/2104.02053) | Proves almost-everywhere nondegenerate gaps for geometrically local Hamiltonians. | Pair-gap nondegeneracy is one finite-order condition. It does not exclude arbitrary balanced integer relations or prove projective rank \(q^n-1\). |
| Kotowski and Oszmaniec, *Tight bounds on recurrence time in closed quantum systems* (2026), [arXiv:2601.10409](https://arxiv.org/abs/2601.10409) | Gives deterministic recurrence upper bounds and proves generic saturation for unrestricted random Hamiltonians. | It does not identify the arithmetic rank or prove saturation/maximal rank inside static nearest-neighbour coupling space. |
| Anand, Valluri, Davis and Ghose, *Quantum recurrences and arithmetic of Floquet dynamics* (2026), [arXiv:2508.09933](https://arxiv.org/abs/2508.09933) | Classifies exact state-independent Floquet recurrences through cyclotomic arithmetic. | Exact periods of driven Floquet operators are a different object. No almost-everywhere maximal projective rank theorem for static tensor-local path Hamiltonians follows. |
| Oszmaniec, Kotowski, Horodecki and Hunter-Jones, *Saturation and recurrence of quantum complexity in random local quantum dynamics* (2024), [arXiv:2205.09734](https://arxiv.org/abs/2205.09734) | Proves complexity saturation and recurrence in random local circuits and stochastic local Hamiltonian evolution. | The ensemble is time-random dynamics, not one fixed generic nearest-neighbour Hamiltonian, and the object is circuit complexity rather than all-order spectral arithmetic. |
| Cohen, *The Galois group of generic symmetric matrices* (1990), [EuDML](https://eudml.org/doc/115721) | Establishes full generic spectral Galois behaviour for unrestricted symmetric matrices. | It shows that maximal root arithmetic is classical in an ambient matrix ensemble. It does not treat the polynomial-size tensor-local subspace. |
| Poláčik and Valdebenito, *Some generic properties of Schrödinger operators with radial potentials* (2019), [journal](https://doi.org/10.1017/prm.2018.129) | Proves residual rational independence of discrete eigenvalues below essential spectrum for a class of radial Schrödinger potentials. | Generic spectral nonresonance is therefore not new as an abstract perturbation phenomenon. The system class, infinite-dimensional topology and proof differ from finite two-body tensor-local chains, and no recurrence-rank conclusion for that local many-body space follows. |
| Mason and Sigalotti, *Generic controllability properties for the bilinear Schrödinger equation* (2010), [arXiv:0911.5650](https://arxiv.org/abs/0911.5650) | Proves generic non-resonance of the discrete spectrum of \(-\Delta+V\) under variation of a continuum potential and combines it with generic eigenstate coupling to obtain approximate controllability. The proof uses analytic eigenbranches and countably many rational-relation exclusions. | This is a close methodological and conceptual ancestor. It proves that generic spectral non-resonance is not itself new. It does not treat a finite tensor-product many-body Hamiltonian restricted to a polynomial-dimensional static nearest-neighbour interaction space, nor identify the resulting exponential projective rank and recurrence law. |
| Privat and Sigalotti, *The squares of the Laplacian--Dirichlet eigenfunctions are generically linearly independent* (2009), [arXiv:0809.2889](https://arxiv.org/abs/0809.2889) | Proves generic non-resonance of a Dirichlet Laplacian spectrum under domain deformations, together with a generic eigenfunction-independence property. | It further removes any claim to novelty for the abstract analytic-genericity mechanism. Domain shape is an infinite-dimensional control variable; it does not imply maximal projective rank for a fixed bounded-degree tensor-local coupling architecture. |
| Chambrion, Mason, Sigalotti and Boscain, *Controllability of the discrete-spectrum Schrödinger equation driven by an external field* (2009), [arXiv:0801.4893](https://arxiv.org/abs/0801.4893) | Derives approximate controllability from a non-resonant discrete spectrum plus suitable transition couplings. | It makes all-order spectral arithmetic physically consequential, but uses non-resonance as a premise rather than proving it in the static local many-body family considered here. |
| Pavlov, *Logarithmically sparse symmetric matrices* (2024), [journal](https://link.springer.com/article/10.1007/s13366-024-00753-y) | Proposition 3.4 proves \(\mathbb Q\)-linear independence of the generic eigenvalue functions for a graph-sparse \(D\times D\) symmetric-matrix space. The proof specializes to a diagonal matrix with \(D\) independently selectable diagonal entries. | This is the closest finite-dimensional algebraic ancestor found. It does not collide with tensor locality: its sparse-matrix space has \(D\) independent diagonal controls, whereas an \(n\)-site fixed-\(q\) path has \(D=q^n\) levels but only polynomially many local coupling parameters and cannot independently set computational-basis diagonal entries. The endpoint theorem proves that noncommuting local interaction generates the missing exponential spectral freedom. |
| De Terán, Dmytryshyn and Dopico, *Generic eigenstructures of Hermitian pencils* (2023), [arXiv:2209.10495](https://arxiv.org/abs/2209.10495) | Classifies generic Kronecker/Jordan eigenstructures of rank-constrained Hermitian matrix pencils. | “Generic eigenstructure” here concerns regularity, ranks, Jordan blocks and sign characteristics of a generalized pencil. It does not prove rational independence of the ordinary eigenvalue branches of \(A+gV\), still less for tensor-local \(A,V\). |
| Vallejo-Fabila and Torres-Herrera, *Late-time universal distribution functions of observables in one-dimensional many-body quantum systems* (2023), [arXiv:2303.10213](https://arxiv.org/abs/2303.10213) | Finds exponential late-time return-probability and spectral-form-factor distributions when a central-limit condition holds, using clean and disordered spin-chain models. | It supplies the closest physics consequence. It does not prove projective rational independence for the static local coupling family, an exact finite-size independent-phase law, simultaneous all-order moment minimality, or an unconditional exponential limit. The proposed local theorem would discharge rather than assume the phase-independence mechanism. |
| Legramandi and Talwar, *The moments of the spectral form factor in SYK* (2025), [arXiv:2412.18737](https://arxiv.org/abs/2412.18737) | Uses \(2k\) replicas to study higher spectral-form-factor moments, replica saddle points and zero-mode manifolds in SYK, including late-time plateau combinatorics. | It makes replica moments and zero modes established physics language, so that terminology is not novel. It studies a disordered all-to-all ensemble and field-theoretic saddle structure, not exact time averages of one generic bounded-degree static chain or the tensor-local maximal-rank theorem. |
| Campos Venuti, Odavić and Hamma, *Integrability and chaos via fractal analysis of spectral form factors: Gaussian approximations and exact results* (2026), [arXiv:2505.05199](https://arxiv.org/abs/2505.05199) | Identifies SFF time statistics with a planar random walk, computes exact arbitrary moments under finite-order nondegeneracy, proves all-order nondegeneracy equivalent to rational independence, and obtains Gaussian/exponential limits under a Lyapunov weight condition. It says proving independence is difficult, notes random perturbations give it almost surely, and tests nonintegrable models numerically. | Directly absorbs novelty of the abstract independent-phase moment formula and exponential limit. It does **not** prove rational independence inside a deterministic polynomial-dimensional tensor-local coupling family. The surviving new theorem is exactly that premise discharge for almost every static nearest-neighbour chain. |

## Direct evidence that the scientific question is open

Konrad Szymański's 2024 research talk
[*State reachability in isolated systems with 2-body Hamiltonians*](https://quantumstat.es/talks/29aug2024/)
asks explicitly:

> Are eigenenergies of generic 2-body Hamiltonians rationally independent?

and restates it as:

> Are there hidden energy resonances in every 2-body Hamiltonian?

The nearest-neighbour theorem answers the projectively meaningful version:
**no**. Trace is unavoidable, but outside that common-energy relation,
almost every static nearest-neighbour two-body qudit Hamiltonian has no
hidden resonance of any order. Since the path-local space is a linear
subspace of the full two-body space and contains a nonzero witness for every
rational-relation polynomial, the same conclusion follows a fortiori for
almost every unrestricted two-body Hamiltonian and for every qudit
interaction graph containing a spanning path.

This talk is evidence of an explicitly asked community question, not a
priority source and not evidence that no private or differently worded
solution exists.

## Secondary assertion requiring caution

Friesdorf's thesis states that arbitrarily small random nearest-neighbour
interactions give nondegenerate gaps and cites the 2009 Linden--Popescu--
Short--Winter paper. The cited primary paper uses nondegenerate gaps as a
condition for equilibration; it does not supply the stronger all-order theorem
audited here. The thesis sentence is therefore not evidence of collision.
Even a proof of generic pair-gap nondegeneracy would remain strictly weaker.

## One-parameter strengthening

The full-measure local theorem has a physically sharper consequence. Write
the local space as the direct sum of onsite terms and pure edge-correlation
terms. For almost every fixed pair \((A,V)\), all relation polynomials
restricted to the line \(A+gV\) are nonzero polynomials in \(g\). Their
combined real zero set is countable. Therefore one scalar interaction knob
produces maximal projective rank for every coupling strength outside a
countable exceptional set, including values arbitrarily close to zero.

This is not claimed as an independent algebraic-genericity invention. It is
a new physical sharpening only insofar as the tensor-local parent theorem is
new: after a generic device background and interaction profile are fixed,
polynomially many independently tunable coefficients are unnecessary.
Matrix-pencil sources found in the targeted search classify eigenstructure
but do not supply this tensor-local rational-arithmetic conclusion.

## Provisional priority verdict

No exact collision has been found in the primary sources above.
The nearest-neighbour theorem appears to supply a missing local-Hamiltonian
fact that recurrence and equilibration papers either assume, replace by a
random-matrix ensemble, or establish only at finite resonance order.

The control literature materially narrows the novelty claim:

> **Not new:** analytic perturbation plus countable exclusion makes
> non-resonance generic in a sufficiently flexible operator family.
>
> **Candidate new theorem:** a polynomial-dimensional, bounded-degree,
> finite-range tensor-local family nevertheless generates the full
> \(q^n-1\) projective spectral rank for every finite local dimension.
>
> **Candidate new law:** that exponential rank is the observer's temporal
> codimension and fixes exact recurrence scarcity and typical return
> exponents.

Riddell--Bertini sharpen the physics priority boundary further. They prove
that rationally independent free one-particle energies still leave excess
many-body higher spectral-form-factor moments, state that free models can
only attain the smallest moments within the free class, and explicitly name
the interplay between rational independence and interacting perturbations as
future research. The proposed interacting path theorem would answer that
direction maximally: almost every static nearest-neighbour interaction
removes every nontrivial equal-cardinality many-body energy-sum collision,
so all replica moments attain the absolute fixed-weight floor rather than
the free-system floor.

Targeted searches have now covered:

1. spectral Galois terminology for generic spin chains and Hermitian matrix
   pencils;
2. tensor-structured and graph-sparse generic eigenvalue independence;
3. finite- and infinite-dimensional quantum-control nonresonance;
4. generic-gap claims in spin-chain equilibration sources;
5. all-order spectral-form-factor moments and rational independence;
6. weak integrability breaking and finite-time SFF crossover.

No source found proves the exact tensor-local statement. This clears the
internal novelty gate provisionally and permits formalization. It cannot
certify absence from private, unindexed or differently phrased work;
specialist review remains mandatory before submission.

## Rejection rule

Priority fails if a prior source proves, for the same full static path-local
coupling space or a strictly smaller physical subfamily, that almost every
spectrum has rational projective rank \(q^n-1\), or proves a theorem from which
that statement follows immediately.

## 2026-08-05 current-source closure

Search was rerun through current arXiv versions and journal records, including
Floquet exact recurrence, recurrence-time bounds, geometrically local
nondegenerate gaps, free-fermion rational independence, all-order spectral
form-factor moments, graph-sparse matrices, and continuum-control generic
nonresonance. No source found proves the exact object: full exponential
projective rank almost everywhere in a static one-dimensional bounded-degree
tensor-local Hamiltonian space with only polynomially many coefficients.

The priority claim is therefore deliberately narrow:

> A polynomial-dimensional static nearest-neighbour qudit family generically
> realizes projective spectral rank `q ^ n - 1`, discharging all finite-order
> no-resonance premises simultaneously and fixing the exact recurrence-density
> exponent.

**Verdict:** exact-object priority audit passed provisionally; no exact
collision found. This is not proof against unindexed or unpublished work and
must be rechecked during journal submission.
