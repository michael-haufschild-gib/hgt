# Energy-matched eigenframe source-memory law

**Status:** `[ACTIVE] [ALGEBRAIC CORE IN LEAN] [HAAR TRACE TAIL IN LEAN] [COEFFICIENT LINK OPEN]`

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

## 2026-08-11 exact Haar advance

The adjoint-representation conjecture has now been proved unconditionally for every finite register.
For every nonzero traceless Hermitian matrix `H` on a `D >= 2` dimensional space,

```text
E_Haar (Re tr(H U* H U))^2 = (tr(H^2))^2 / (D^2 - 1),
Pr_Haar{|Re tr(H U* H U)| >= tr(H^2)/2} <= 4 / (D^2 - 1).
```

The proof first establishes the balanced diagonal law from exchangeability and exact Haar fourth
moments, extends it to arbitrary Hermitian sources by spectral conjugation invariance, and transfers
it across every finite coordinate reindexing.  It uses no minimum spectral gap, nondegeneracy,
locality-dictionary size, or asymptotic approximation.

For every autonomous Hamiltonian, exact Schrödinger conjugation simultaneously gives

```text
Re tr(H exp(+itH) H exp(-itH)) = tr(H^2)
```

at every real time.  Hence a known local generator supplies a permanent source-memory witness while
the Haar false-positive probability is `O(D^-2)`.  The combined Lean theorem also retains the
one-query coefficient-matched inverse-participation lower bound for arbitrary supported Pauli
dictionaries.

### Conjecture-loop audit

1. Entrywise squared-score route paid `M^2`; proved but too weak.
2. Coefficient contraction predicted a `D^-2` Haar scale; algebraic fixed-vector law proved.
3. Diagonal-only Haar calculation succeeded but was not basis invariant; conjugation transport
   initially failed from elaboration blow-up, then succeeded after isolating trace cycling and Haar
   left/right invariance.
4. Canonical-index theorem did not yet apply to qubit registers; exact Haar-measure reindexing closed
   this gap and yielded the register-independent law above.

### Remaining exact bridge

The trace-autocorrelation witness is now complete.  To transfer the same `4/(D^2-1)` tail verbatim
to the literal signed product-eigenframe statistic, prove the Pauli-coordinate identity

```text
sum_(Q,P) h_Q h_P C(U)_(Q,P) = D^-1 Re tr(H U* H U)
```

under dictionary support, together with the matching `l1` normalization.  Until that identity is
formalized, the trace witness and coefficient-sampled witness are distinct operational statements.
