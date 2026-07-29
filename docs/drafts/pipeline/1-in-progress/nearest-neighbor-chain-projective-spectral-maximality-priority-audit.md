# Priority audit — generic maximal projective rank in a local quantum chain

- **Object audited:** `../2-fully-proven/nearest-neighbor-chain-projective-spectral-maximality.md`
- **Audit date:** 2026-07-29
- **Status:** `[PRIMARY AUDIT IN PROGRESS] [NO EXACT COLLISION FOUND]`
- **Claim whose priority matters:** in the full real coupling space of arbitrary
  one-site and nearest-neighbour two-site qubit Hamiltonians on an open path,
  Lebesgue-almost every Hamiltonian has no rational affine relation among its
  \(2^n\) eigenvalues except trace. Equivalently, its projective spectral rank
  is \(2^n-1\).

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
 \sum_{j=1}^{2^n}m_jE_j=0,\qquad \sum_jm_j=0,
 \qquad m\in\mathbb Z^{2^n},
\]
simultaneously, for a static bounded-degree finite-range Hamiltonian family.

## Primary-source comparison

| Source | What is established or assumed | Why it does not presently collide |
|---|---|---|
| Linden, Popescu, Short and Winter, *Quantum mechanical evolution towards thermal equilibrium* (2009), [arXiv:0812.2385](https://arxiv.org/abs/0812.2385) | Equilibration under a nondegenerate-energy-gap condition. | Nondegenerate gaps are a hypothesis used for dephasing, not an all-order rational-independence theorem for local coupling space. |
| Short, *Equilibration of quantum systems and subsystems* (2011), [arXiv:1012.4622](https://arxiv.org/abs/1012.4622) | Re-derives equilibration results under nondegenerate energy gaps and large effective dimension. | Again assumes or weakens gap multiplicity; it does not prove maximal projective rank. |
| Keating, Linden and Wells, *Spectra and eigenstates of spin chain Hamiltonians* (2015), [arXiv:1403.1121](https://arxiv.org/abs/1403.1121) | Proves Gaussian limiting density of states and eigenstate-entanglement results; notes generic nondegeneracy of eigenvalues for a broader chain family. | Simple spectrum is order-zero information. It neither excludes repeated nonzero gaps nor arbitrary rational affine relations. |
| Riddell and Pagliaroli, *No-resonance conditions, random matrices, and quantum chaotic models* (2024), [arXiv:2307.05417](https://arxiv.org/abs/2307.05417) | Studies finite-\(q\) no-resonance conditions statistically in random matrices and a chaotic model, finding Poisson rather than repulsive sum statistics and allowing violations. | It explicitly describes higher no-resonance as usually assumed and studies statistics/violations. It gives no all-\(q\), almost-every local-chain theorem. |
| Riddell and Bertini, *Rationally independent free fermions with local hopping* (2024), [arXiv:2404.12100](https://arxiv.org/abs/2404.12100) | Engineers rational independence of the single-particle energies in one-dimensional free-fermion models. | Many-body energies remain additive combinations of only \(O(n)\) one-particle frequencies, so their projective rational rank is at most \(O(n)\), not \(2^n-1\). The construction also uses system-size-dependent hopping ranges indexed by divisors. |
| Kotowski and Oszmaniec, *Tight bounds on recurrence time in closed quantum systems* (2026), [arXiv:2601.10409](https://arxiv.org/abs/2601.10409) | Gives deterministic recurrence upper bounds and proves generic saturation for unrestricted random Hamiltonians. | It does not identify the arithmetic rank or prove saturation/maximal rank inside static nearest-neighbour coupling space. |
| Oszmaniec, Kotowski, Horodecki and Hunter-Jones, *Saturation and recurrence of quantum complexity in random local quantum dynamics* (2024), [arXiv:2205.09734](https://arxiv.org/abs/2205.09734) | Proves complexity saturation and recurrence in random local circuits and stochastic local Hamiltonian evolution. | The ensemble is time-random dynamics, not one fixed generic nearest-neighbour Hamiltonian, and the object is circuit complexity rather than all-order spectral arithmetic. |

## Direct evidence that the scientific question is open

Konrad Szymański's 2024 research talk
[*State reachability in isolated systems with 2-body Hamiltonians*](https://quantumstat.es/talks/29aug2024/)
asks explicitly:

> Are eigenenergies of generic 2-body Hamiltonians rationally independent?

and restates it as:

> Are there hidden energy resonances in every 2-body Hamiltonian?

The nearest-neighbour theorem answers the projectively meaningful version:
**no**. Trace is unavoidable, but outside that common-energy relation,
almost every static nearest-neighbour two-body qubit Hamiltonian has no
hidden resonance of any order. Since the path-local space is a linear
subspace of the full two-body space and contains a nonzero witness for every
rational-relation polynomial, the same conclusion follows a fortiori for
almost every unrestricted two-body Hamiltonian.

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

## Provisional priority verdict

No exact collision has been found in the primary sources above.
The nearest-neighbour theorem appears to supply a missing local-Hamiltonian
fact that recurrence and equilibration papers either assume, replace by a
random-matrix ensemble, or establish only at finite resonance order.

This is not yet a priority clearance. Searches still required:

1. spectral Galois theory for generic spin chains and matrix pencils;
2. algebraic-independence results for eigenvalues of sparse Hermitian matrix
   families;
3. controllability and inverse-spectral literature whose genericity lemmas may
   imply the result without using recurrence language;
4. citations to the nearest-neighbour generic-gap assertion beyond the thesis.

## Rejection rule

Priority fails if a prior source proves, for the same full static path-local
coupling space or a strictly smaller physical subfamily, that almost every
spectrum has rational projective rank \(2^n-1\), or proves a theorem from which
that statement follows immediately.
