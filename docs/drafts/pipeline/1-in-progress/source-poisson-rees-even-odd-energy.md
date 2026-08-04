# Singular source Poisson--Rees even-over-odd energy law

- **ID:** `source-poisson-rees-even-odd-energy`
- **Stage:** 1-in-progress
- **Type:** CONJECTURE / RH-BEARING SOURCE PRODUCER
- **Source:** `CCMClosedXiConformalKreinLaw.lean`;
  `HellingerBetaMobiusThetaCofinalCoface.lean`;
  `PrimeDepthBVWoldReesCoronaQuotient.lean`;
  `PrimeGammaBocksteinReesCoronaComparison.lean`;
  `singular-infinite-source-pointed-common-test-factorization.md`;
  `cofinal-bockstein-polarized-adelic-stokes.md`
- **Statement:** The forced pre-divisor Poisson--Gamma source differential has a
  trace-filtered singular Hodge completion whose squared boundary energy is exactly the
  reflection-even minus reflection-odd Xi evaluation energy.

## Goal

Write

\[
 E_+(F)=E(F)+JE(F),\qquad E_-(F)=E(F)-JE(F),
\]

where `E` is the multiplicity-exact Xi evaluation landing and `J` is the functional-equation
Real involution.  The already-proved Clifford law is

\[
 4\,Q_{\mathrm W}(F,F)=\|E_+(F)\|^2-\|E_-(F)\|^2.                 \tag{1}
\]

The source theorem sought here is the stronger identity

\[
 \boxed{
 \|E_+(F)\|^2-\|E_-(F)\|^2
   =4\left\|\overline d_{\Lambda,\Gamma}
                  \mathcal P_{\mathrm{src}}F\right\|^2_{\mathcal H_{\mathrm{src}}}.}
                                                                    \tag{SPH}
\]

Objects on the right must be constructed before divisor extraction:

1. `P_src` is the cofinal Poisson lift obtained from the forced Hellinger--Beta adjacent coface
   and its Möbius--theta telescope;
2. `d_{Lambda,Gamma}` is the signed cross-prime incidence obtained by adjoining the actual
   Gamma Bockstein to the rational-adelic prime/depth differential;
3. its closure is taken only after prime and Gamma leading coordinates have been joined, in the
   coefficient-generated trace-filtered Rees graph topology;
4. `H_src` is the positive harmonic quotient of that source complex, not a completion whose
   norm is defined from `Q_W`, the Xi divisor, or `(1)`.

`(SPH)` would give Weil positivity from a genuine source norm.  Together with Weil's criterion
and `(1)`, it proves RH.  The Clifford-corrected bivariant product remains the exact numerical
recipient; it is not the positivity producer.

## Gates

- [x] 0 -> 1: exact statement, source-purity rules, falsifiers, internal audit, and external
  primary-source boundary recorded
- [x] prove the local Rees attenuation law on paper and identify why local contraction is
  nonselective
- [x] formalize the local attenuation/no-go theorem unconditionally
- [ ] construct the joined pre-completion differential and prove it is closable in the stated
  trace-filtered Rees topology
- [ ] prove common-domain landing of `P_src F` and the isometric comparison `(SPH)`
- [ ] 1 -> 2: dependency-closed paper proof with no RH-equivalent premise
- [ ] 2 -> 3: unconditional Lean theorem, targeted module build, umbrella wiring, axiom audit
- [ ] 3 -> 4: external hostile review and standalone publication proof

## Source-purity and anti-circularity constraints

1. No definition may inspect `rho`, `Re(rho)`, centered Xi rate, divisor multiplicity, an
   eigenspace, `E_+`, `E_-`, `Q_W`, or a critical-line predicate.
2. Divisor and multiplicity may enter only in the final comparison of the already-constructed
   source complex with the CCM/Xi quotient.
3. Positivity must be the norm of an independently constructed harmonic quotient.  Cholesky
   factorization of the Weil matrix, a graph contraction defined from `E_-/E_+`, or a Hilbert
   norm transported from the divisor side is circular.
4. Prime and Gamma legs must be joined before completion.  Completing individual feature legs
   and subtracting afterward is forbidden by the critical-completion trilemma.
5. The source comparison must retain prime, inverse-prime, depth, divisor, and leading-jet
   provenance.  Scalar distributional equality is insufficient.

## Hostile conjecture audit

### C1 -- ordinary positive Gram factorization

Factor every prime interval cell in an orthogonal Hilbert sum and add a positive Gamma border.

**Verdict:** `FALSE`.  Each reflected logarithmic interval already has a strict negative
two-test determinant.  A nonzero positive Gamma packet cannot short the cooriented defect.

### C2 -- block-diagonal Rees-corona contraction

Use the adjacent-depth Rees weight as a local contraction and infer criticality from its norm.

**Verdict:** `NONSELECTIVE`.  For a prime `p`, put

\[
 \kappa_p=\frac{(1-p^{-1})(2-p^{-1})}{2\log p}.
\]

Then the exact adjacent-depth weight is

\[
 w_p(a)=a\kappa_p,\qquad 0<\kappa_p<1.                           \tag{2}
\]

Thus `|w_p(a)|<1` for every strip grade `|a|<=1`, including every nonzero off-line grade.
Local Schur contractivity does not select `a=0`.

**Paper proof of `(2)`.**  Since `p>1`, `q=p^{-1}` lies in `(0,1)`.  The explicit Wold masses
and clocks are

\[
 m_0=1-q,\quad m_1=(1-q)q,\quad \lambda_0=\log p,\quad
 \lambda_1=2\log p.
\]

Hence

\[
 \frac{m_0\lambda_1-m_1\lambda_0}{\lambda_0\lambda_1}
   =\frac{(1-q)(2-q)}{2\log p}=\kappa_p.
\]

Positivity is immediate.  The elementary bound `log p >= 1-1/p`, together with
`2-q<2`, gives

\[
 (1-q)(2-q)<2(1-q)\le 2\log p,
\]

so `kappa_p<1`.  Moreover `w_p(a)=0` iff `a=0`; contraction and annihilation are sharply
different conditions.

### C3 -- finite or normally summable signed shorting

Cancel distinct prime/Gamma frequencies by a signed incidence after ordinary completion.

**Verdict:** `FALSE`.  Unique factorization and exponential Vandermonde independence kill every
finitely supported universal coefficient.  Bohr--Cesaro extraction extends the rigidity to every
absolutely summable physical orbit.

### C4 -- singular joined Poisson--Gamma Hodge differential

Join reflected prime interval legs with the Gamma Bockstein before any Hilbert completion, take
the coefficient-generated trace-filtered Rees closure, and prove `(SPH)` by a source Stokes/Green
identity.

**Verdict:** `SURVIVES PRELIMINARY ATTACK; OPEN`.  This is the only category not killed by the
internal no-go corpus.  It is falsifiable: nonclosability, loss of a leading prime/Gamma
coordinate, failure of common-domain landing, or one test violating `(SPH)` kills it.

## Exact open core

`[OPEN CORE -- SINGULAR_SOURCE_COMMON_DOMAIN_ISOMETRY]`

Construct the closure of the joined signed prime/Gamma differential and prove simultaneously:

\[
 \mathcal P_{\mathrm{src}}F\in\operatorname{Dom}
     \overline d_{\Lambda,\Gamma}
 \quad\text{and}\quad
 4\|\overline d_{\Lambda,\Gamma}\mathcal P_{\mathrm{src}}F\|^2
   =\|E_+(F)\|^2-\|E_-(F)\|^2.                                 \tag{3}
\]

Existing algebra proves the coface telescope, source-to-Xi landing, Bockstein/Rees coefficient
identity, and exact Weil bridge separately.  It does not prove common-domain landing or the
positive isometry `(3)`.  Assuming either clause in a norm transported from the Xi side would
assume Weil positivity and therefore RH.

## External boundary

- Connes--Marcolli's cyclic-cokernel trace formula identifies Weil positivity with RH but does not
  construct `(SPH)`: <https://arxiv.org/abs/math/0703392>.
- Connes--Consani prove an archimedean-place positivity mechanism and explicitly leave the
  general semilocal/global operator problem open: <https://arxiv.org/abs/2006.13771> and
  <https://arxiv.org/abs/1910.14368>.
- Connes--Consani--Moscovici construct the semilocal prolate operator but not global Weil
  positivity: <https://arxiv.org/abs/2310.18423>.
- Deninger proves that a real-coefficient Weil cohomology cannot provide the desired theory and
  isolates a complex/Real Hodge-star route as conjectural: <https://arxiv.org/abs/2204.02714>.

Exact-name, identity, and concept searches found no primary source proving `(SPH)`.  This is a
noncollision result, not a priority claim.

## No-go closure if `(SPH)` fails

- **Exact killing theorem/mechanism:** record which of closability, provenance retention,
  common-domain landing, or the energy identity fails and exhibit the smallest source witness.
- **Strongest positive survivor:** the exact Weil even-minus-odd identity, source-to-Xi landing,
  signed prime-current factorization, critical-completion trilemma, Bockstein/Rees energy port,
  and strict local attenuation law `(2)`.
- **New insight:** source positivity cannot be local contractivity, ordinary Gram positivity, or
  post-completion cancellation.  It must be a singular pre-completion Hodge identity coupling all
  prime frequencies to the Gamma boundary while retaining coefficient provenance.
- **Status:** conjecture open.  No RH proof claimed.

## Log

- 2026-08-04 -- Isolated `(SPH)` after Clifford phases and Lefschetz conformal flow were proved
  sign-conservative.  Internal audit eliminated ordinary Hilbert, positive Gamma, finite signed,
  and absolutely summable signed shorting.  External audit found no existing global theorem.
- 2026-08-04 -- Proved on paper the exact adjacent-depth attenuation `w_p(a)=a kappa_p` with
  `0<kappa_p<1`.  This kills local contraction as an RH-selective substitute and forces the
  singular joined source identity `(SPH)`.
- 2026-08-04 -- Formalized the attenuation, open-unit-interval bound, strip-wide strict
  contraction, and zero/nonzero classification in
  `PrimeDepthBVWoldReesCoronaContractionNoGo.lean`.  Direct source check, leaf module build,
  repository lint, and standard-axiom audit pass; module is wired into the RHTower umbrella.
