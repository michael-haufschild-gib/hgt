# Energy-matched eigenframe source-memory law

**Status:** `[ACTIVE] [ALGEBRAIC CORE IN LEAN] [HAAR SECOND MOMENT OPEN]`

## Frontier target

Replace entrywise squaring of the conserved Pauli-transfer block by one coefficient-matched,
signed product-eigenframe statistic.  The objective is a permanent operational separator whose
Haar false-positive bound does not pay dictionary cardinality.

## Conjecture loop

1. **Uniform entrywise score.**  The adaptive two-query score is at least `M^-2`, while Haar mean
   is `(D+1)^-1`.  This is proved, including fixed-body Majorana dictionaries, but retains the
   finite-size condition `M^2 < D+1`.
2. **Contract before squaring.**  Weight input and output dictionary words by the Hamiltonian
   coefficients, and include the signed output eigenvalue in each product-state trial.  Signed
   eigenframe extraction makes its expectation
   `h^T C(U) h / ||h||_1^2`.  If `C(U)h=h`, this is exactly
   `||h||_2^2 / ||h||_1^2`, at every time.  **Algebraic identity survives and is being formalized.**
3. **Haar adjoint variance.**  For traceless Pauli support, conjecture the exact law
   `E_Haar A_h(V)^2 = (||h||_2^2/||h||_1^2)^2/(D^2-1)`.
   This is the adjoint-representation matrix-coefficient variance.  If proved internally, Markov
   gives `Pr{|A_h(V)| >= A_h(static)/2} <= 4/(D^2-1)`, with no dictionary-size condition.

## Exact algebraic theorem

For a finite Pauli dictionary `A_i`, coefficient vector `h`, and transfer compression `C(U)`, define

```text
A_h(U) = ||h||_1^-2 sum_(j,i) h_j h_i
           2^-n sum_x lambda_(j,x) Tr(rho_(j,x) U^* A_i U).
```

The signed eigenframe identity gives

```text
A_h(U) = h^T C(U) h / ||h||_1^2.
```

Therefore every fixed coordinate `C(U)h=h` gives

```text
A_h(U) = ||h||_2^2 / ||h||_1^2 >= 1/M.
```

The final inequality is sharp for equal-magnitude coefficients.  Unlike the squared-entry score,
this is a one-forward-query mean: input word, output eigenframe, and measurement sign are sampled
from the normalized absolute coefficient weights.

## Hostile boundary

- Energy conservation itself is standard and is not a novelty claim.
- Knowing or sampling the Hamiltonian coefficients is part of the protocol.  This does not give a
  black-box test for an unknown generator.
- The exact Haar adjoint variance and a bounded-outcome sampling theorem are required before
  claiming a dictionary-free operational advantage.
- This proves permanent non-Haar memory, not Brown--Susskind complexity growth.

## Lean target

New module `HTGeometry/EnergyMatchedEigenframeSourceMemory.lean`:

- exact signed eigenframe contraction;
- exact fixed-vector value;
- inverse-cardinality participation lower bound;
- autonomous arbitrary-dictionary and fixed-body Majorana specializations;
- later: exact Haar adjoint variance and false-positive tail.
