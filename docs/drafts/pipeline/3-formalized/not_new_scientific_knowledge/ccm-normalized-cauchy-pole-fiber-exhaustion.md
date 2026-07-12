# CCM normalized Cauchy-pole fiber exhaustion

- **ID:** `ccm-normalized-cauchy-pole-fiber-exhaustion`
- **Stage:** 3-formalized
- **Type:** THEOREM / FORMALIZATION / BRIDGE / NOT NEW SCIENTIFIC KNOWLEDGE
- **Lean module:**
  `formal/GaloisForLFunctions/RHTower/XiWeilCauchyPoleExhaustion.lean`
- **Scientific status:** `[PROVED IN LEAN] [BRIDGE] [NOT AN RH PROOF]`

## Statement

For every centered point `alpha`, the Xi divisor has a positive spectral gap away from its complete
multiplicity fiber:

\[
\exists\delta>0\quad
\lambda_q\ne\alpha\Longrightarrow |\lambda_q-\alpha|\ge\delta.
\]

For every prescribed positive approach cap, there is a positive speed below that cap and a sequence
of regular centered points `z_n -> alpha` of the explicit form

\[
z_n=\alpha+\frac{c}{n+1}
\]

such that the normalized Cauchy
evaluation vectors satisfy

\[
(\alpha-z_n)
  \left(\frac1{\lambda_q-z_n}\right)_q
\longrightarrow
\left(\mathbf 1_{\lambda_q=\alpha}\right)_q
\]

in the multiplicity-exact divisor `ell^2` norm.

The proof uses analytic isolation of Xi zeros and the uniform majorant

\[
\left|\frac{\alpha-z_n}{\lambda_q-z_n}\right|^2
\le
4\left|\frac1{\lambda_q-\alpha}\right|^2,
\]

whose divisor sum is finite by the already formalized Cauchy square-summability theorem. Tannery's
theorem gives the norm limit.

For nonreal `alpha`, subtracting the corresponding limit at `conjugate(alpha)` places the exact
off-real sign test in the closure of regular two-pole Cauchy packets. The bounded line-conjugation
Hilbert realization of the Weil form then gives the exact criterion

\[
\mathrm{RH}
\quad\Longleftrightarrow\quad
\Re\langle F,F\rangle_{\Xi,\mathrm{Weil}}\ge0
\quad\text{for every regular two-pole Cauchy packet }F.
\]

## Positive carrier law

A successful CCM construction does not need to prove density of the entire Cauchy span. It must
carry the smaller moving rank-two family consisting of normalized poles approaching each
functional-equation conjugate pair. That family already exhausts every RH-deciding negative sign
direction.

Consequently the remaining source theorem is precise: prove positivity of the distinguished
semilocal prime--archimedean/Sonin form on every admissible regular two-pole Cauchy packet, with the
required cofinal pole approach retained. The separately formalized continued two-pole source
criterion proves this explicit source positivity itself equivalent to RH.

Multiplicity is not an obstruction. Cauchy evaluation vectors and the limiting indicators are
constant on each multiplicity fiber, and the negative square counts the full fiber multiplicity.

## Formal declarations

```text
RHTower.xiWeilFiberIndicator
RHTower.xiWeilFiberIndicator_squareSummable
RHTower.exists_xiSpectralPoint_gap
RHTower.norm_normalizedCauchy_le
RHTower.exists_normalizedCauchyLp_tendsto_fiberIndicator_with_cap
RHTower.exists_normalizedCauchyLp_tendsto_fiberIndicator
RHTower.xiWeilTwoCauchyPacket
RHTower.xiWeilTwoCauchyPacket_squareSummable
RHTower.tendsto_xiWeilLineConjLp
RHTower.XiWeilRegularTwoCauchyNonneg
RHTower.riemannHypothesis_iff_regularTwoCauchy_nonneg
RHTower.CCMRegularTwoPolePassivity
RHTower.ccmRegularTwoPolePassivity_iff_riemannHypothesis
RHTower.CCMContinuedTwoPoleSourcePassivity
RHTower.riemannHypothesis_iff_ccmContinuedTwoPoleSourcePassivity
```

## Verification

- [x] analytic Xi-divisor gap formalized
- [x] finite multiplicity-fiber indicator formalized
- [x] normalized Cauchy majorant formalized
- [x] dominated `ell^2` convergence formalized
- [x] bounded Weil-form continuity reused
- [x] regular two-pole positivity criterion formalized
- [x] exact module and CCM umbrella builds
- [x] axiom audit: only `propext`, `Classical.choice`, and `Quot.sound`
- [ ] distinguished semilocal source positivity proved
- [ ] RH
