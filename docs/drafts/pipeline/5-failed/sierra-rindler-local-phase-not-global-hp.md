# Sierra's Rindler mirror model is a local zero realization, not a global Hilbert--Pólya operator

- **ID:** `sierra-rindler-local-phase-not-global-hp`
- **Stage:** 5-failed
- **Type:** TERMINAL DIRECT HILBERT--PÓLYA IMPLEMENTATION VERDICT / POSITIVE GLOBALIZATION LAW
- **Scientific status:** `[PROVED ROUTE VERDICT] [SEARCH] [BRIDGE] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Route status:** The published zero-by-zero self-adjoint-extension implementation does not prove
  RH. The Rindler/Dirac carrier remains viable only after a single source-selected domain and an
  exact global determinant are constructed.
- **Statement:** In Sierra's transparent-mirror Rindler model, an on-line zero `E_n` becomes an
  eigenvalue only after the self-adjoint extension phase is tuned using the zeta phase and derivative
  sign at that same zero. The construction therefore realizes one selected on-line zero, not the
  full Xi divisor of one operator. The proposed contradiction from a hypothetical off-line zero
  does not follow from self-adjointness: divergence of the chosen limiting eigenfunction ansatz is
  compatible with continuous spectrum and may signal failure of the singular mirror limit. A viable
  Rindler Hilbert--Pólya theorem must instead produce one zero-independent arithmetic domain whose
  characteristic determinant is Xi locally uniformly and with multiplicity.

## 1. The known graded Dirac construction

Sierra constructs a massless two-component Dirac fermion in a Rindler wedge with delta interactions
at mirror positions associated to square-free integers. Prime mirrors have return times `log p`, so
the model contains the correct primitive arithmetic phases. The boundary at the accelerated
observer carries a self-adjoint extension parameter

```text
vartheta in R/pi Z.                                         (1)
```

At finite mirror strength the transfer matrices define a self-adjoint Hamiltonian `H_vartheta` on
the stated boundary domain.

In the transparent-mirror limit, the normalizability analysis gives, for a simple critical-line
zero `1/2+iE`, the necessary phase condition

```text
vartheta=-theta(E)+(pi/2) sign Z'(E) mod pi,                (2)
```

where

```text
zeta(1/2+iE)=exp(-i theta(E)) Z(E).                         (3)
```

The paper explicitly describes this as a **local** Hilbert--Pólya realization: one tunes
`vartheta` for the chosen zero. It also states that a single global Hamiltonian would require the
relevant phase to be constant over all zeros, which it is not.

## 2. Why phase tuning is not a global spectrum theorem

For a fixed self-adjoint operator the domain is fixed before an eigenvalue is solved. In `(2)`, the
domain parameter is a function of the target zero and the derivative of the target Hardy function.
Thus the implication established by the construction has the form

```text
given E with Z(E)=0,
choose Dom(H) using theta(E),sign Z'(E),
then E is a candidate eigenvalue.                            (4)
```

The global Hilbert--Pólya implication needed for RH is

```text
construct one source-selected self-adjoint H,
prove det_*(H-z)=C Xi(1/2-iz),
therefore every Xi zero is a real spectral point.            (5)
```

Equation `(4)` does not imply `(5)`. A family of operators indexed by already known zero data is a
spectral realization atlas, not one spectral proof.

The positive-density transverse relocation theorem sharpens the distinction. An ordinate-only
realization may reproduce the full on-line height measure while a symmetric completed function
still has positive-density off-line pairs at those heights. Without the exact characteristic
determinant in `(5)`, the Rindler spectrum does not transport transverse divisor information.

## 3. Failure of the proposed RH contradiction

The paper considers a hypothetical off-line quartet and derives a rapidly divergent asymptotic for
the same transfer-vector ansatz. It then argues that no discrete or continuum-normalized state would
remain, contradicting spectral decomposition of the self-adjoint Hamiltonian.

That conclusion has three independent gaps.

### 3.1 A failed ansatz is not failure of the spectral theorem

A self-adjoint operator may have purely continuous spectrum and no normalizable eigenfunction at a
given energy. Divergence of one proposed generalized eigenfunction normalization does not show that
the projection-valued spectral measure fails to exist. To obtain a contradiction one must prove that
the constructed transfer solutions exhaust the generalized spectral representation in a topology
where the claimed asymptotic is valid. No such completeness theorem is supplied.

### 3.2 The transparent-mirror limit is singular

The RH argument is made as the mirror strengths tend to zero while infinitely many mirrors remain.
Self-adjointness of every finite-strength operator does not by itself give strong-resolvent, norm-
resolvent, graph, or determinant convergence of the limiting family. If the zeta/Mobius asymptotic
ceases to define a vector when an off-line zero is present, the immediate conclusion is that the
proposed limit identification fails—not that the off-line zero cannot exist.

### 3.3 The analytic asymptotics assume unresolved zero control

The argument selects a zero with maximal real part on the right of the line and uses it as the
dominant term. Existence of an off-line zero does not imply that the set of real parts has an attained
maximum. More generally, contour shifts and Mobius-series asymptotics in this region require exactly
the uniform zero and convergence estimates that the paper leaves for further analysis.

The paper's conclusion itself records that convergence of the mathematical series still needs to be
analyzed. Therefore the contradiction is a conditional heuristic, not a proof of RH.

## 4. Finite-prime and phase-rank boundary

The mirror system correctly supplies primitive times `log p`. At cutoff `N` these have rational rank
`pi(N)`. The finite-Gamma projective-boundary theorem shows that the archimedean/Rindler completion
cannot replace those directions, while the autonomous order floor shows that a fixed finite flow
cannot generate them.

The Rindler model passes this provenance test better than scalar BBM: the arithmetic phase carrier is
explicit in the mirrors. Its failure is at the next gate:

```text
prime phase carrier present
  + one phase-tuned on-line eigenstate
  != full Xi divisor carried by one fixed domain.            (6)
```

## 5. Positive globalization theorem required

A viable Rindler/Dirac Hilbert--Pólya implementation must construct one cofinal system

```text
(H_N,Dom_N,Delta_N) -> (H_infinity,Dom_infinity,Delta_infinity)             (7)
```

with all of the following properties.

1. **Zero-independent domain:** every boundary/matching parameter is defined from completed
   Euler--Gamma source data, not from `theta(E_n)`, `Z'(E_n)`, or a zero list.
2. **Self-adjointness:** each `H_N`, and the limiting operator when used, is self-adjoint on the
   stated source-selected domain.
3. **Finite divisor:** `Delta_N` is a genuine characteristic/Fredholm determinant with zeros at
   finite stage, not merely a normalizability condition evaluated at known zeros.
4. **Cofinal transfer:** after explicit zero-free normalization,

   ```text
   Delta_N -> Xi(1/2-iz)                                    (8)
   ```

   locally uniformly and multiplicity-preservingly.
5. **Prime-rank preservation:** the cutoff carrier retains at least `pi(N)` marked prime phases
   through the archimedean completion.
6. **Horizontal control:** every zero of `Delta_N` has reflected-energy defect
   `o((log N)^2)`, or the global determinant is already the exact Xi determinant.

Under clauses 2 and 4, all zeros of the limiting entire determinant are real and RH follows. These
clauses are the positive mathematical content missing from the local phase-tuning construction.

## 6. Scope

- The card does not deny the correctness of the finite-strength self-adjoint Dirac/mirror operator.
- It does not deny that a chosen on-line zero can be realized after phase tuning.
- It closes the inference from that local family and its present transparent-mirror asymptotics to
  RH.
- A single source-selected Rindler operator satisfying Section 5 remains viable and would be a
  genuine Hilbert--Pólya proof.
- CCM, Sonin/prolate, and finite-Weil determinant routes are outside this verdict.

## Scientific status and sources

The distinction between a zero-dependent operator family and one global Hilbert--Pólya operator is
already explicit in Sierra's paper. The spectral-theorem and singular-limit objections are standard
operator theory. The route verdict is therefore `[SEARCH]`/`[BRIDGE]`, not new scientific knowledge.

Primary sources:

1. G. Sierra, *The Riemann zeros as spectrum and the Riemann hypothesis*, Symmetry 11 (2019), 494,
   arXiv `1601.01797`.
2. G. Sierra, *The Riemann zeros as energy levels of a Dirac fermion in a potential built from the
   prime numbers in Rindler spacetime*, J. Phys. A 47 (2014), 325204, arXiv `1404.4252`.

## Gates

- [x] exact zero-dependent extension phase identified from the primary source.
- [x] local versus global Hilbert--Pólya distinction proved.
- [x] spectral-theorem contradiction audited.
- [x] singular-limit and dominant-zero gaps isolated.
- [x] positive globalization theorem stated.
- [ ] reopen only with a single zero-independent domain and determinant satisfying Section 5.
