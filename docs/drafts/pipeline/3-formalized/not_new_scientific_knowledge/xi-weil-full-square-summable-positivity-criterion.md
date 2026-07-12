# Full square-summable Xi--Weil positivity criterion

- **ID:** `xi-weil-full-square-summable-positivity-criterion`
- **Stage:** 3-formalized
- **Type:** THEOREM / FORMALIZATION / BRIDGE / NOT NEW SCIENTIFIC KNOWLEDGE
- **Lean module:**
  `formal/GaloisForLFunctions/RHTower/XiWeilPositivityCriterion.lean`
- **Scientific status:** `[PROVED IN LEAN] [BRIDGE] [NOT AN RH PROOF]`

## Statement

Let `xiWeilPolarization` be the multiplicity-exact Hermitian polarization on the centered Xi
divisor. Lean proves

\[
\mathrm{RH}
\quad\Longleftrightarrow\quad
\Re\langle F,F\rangle_{\Xi,\mathrm{Weil}}\ge0
\quad\text{for every square-summable divisor test }F.
\]

The reverse implication is constructive. For a nonreal centered divisor point `alpha`, define

\[
F_\alpha(z)=
\begin{cases}
1,&z=\alpha,\\
-1,&z=\overline\alpha,\\
0,&\text{otherwise}.
\end{cases}
\]

This test has finite divisor support and is therefore square-summable. Its exact Weil square is

\[
\langle F_\alpha,F_\alpha\rangle_{\Xi,\mathrm{Weil}}
=-#\{q:\lambda_q\in\{\alpha,\overline\alpha\}\}<0.
\]

Thus every nonreal divisor orbit produces an explicit negative square, including multiple zeros;
no derivative or simplicity assumption is required.

## Positive carrier law

Every successful Connes--Consani--Moscovici or Weil implementation must extend its source-side
positive form to a carrier containing these finite conjugate-orbit sign tests. The normalized
Cauchy-pole exhaustion theorem now proves that regular moving two-pole packets already approach
every such sign test. A test space which is not closed under that cofinal pole approach has not yet
carried the RH-deciding incidence.

The existing formal corpus already supplies:

- the Hermitian Xi-divisor polarization;
- the exact prime-plus-archimedean relative-resolvent formula on separated finite Cauchy packets;
- the algebraic and closed Hilbert Cauchy cores.

The remaining CCM theorem is therefore smaller than full Cauchy-core density: the distinguished
semilocal source form must be shown positive on every regular two-pole Cauchy packet while retaining
the normalized cofinal pole limit. Lean proves that this rank-two positivity already forces RH.

## Formal declarations

```text
RHTower.xiOffRealSignTest
RHTower.xiOffRealSignTest_squareSummable
RHTower.xiOffRealSignTest_product
RHTower.xiWeilPolarization_offRealSignTest
RHTower.xiWeilPolarization_offRealSignTest_re_neg
RHTower.riemannHypothesis_of_xiWeilPolarization_nonneg
RHTower.riemannHypothesis_iff_xiWeilPolarization_nonneg
```

## Verification

- [x] nonreal sign test formalized
- [x] finite-support square summability formalized
- [x] exact negative multiplicity count formalized
- [x] positivity implies real centered divisor formalized
- [x] real centered divisor implies RH reused
- [x] RH implies full square-summable positivity reused
- [x] exact target module build
- [x] no `sorry`, `admit`, `axiom`, `opaque`, or `unsafe`
- [x] normalized two-pole Cauchy exhaustion formalized separately
- [ ] semilocal two-pole source positivity proved
- [ ] RH
