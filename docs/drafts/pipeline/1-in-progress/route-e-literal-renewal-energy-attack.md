# Route E: literal renewal energy attack

- **ID:** E-LREA-001
- **Stage:** 1-in-progress
- **Type:** CONJECTURE / ACTIVE PROOF ATTEMPT
- **Target:** unconditional bounded returns of the literal Möbius Gamma–Hankel covariance for orders cofinal above one.
- **Status:** RH remains unproved. No numerical experiments authorized or used.

## Proof chain and hard obstacle

For `F_N(x)=sum_{1<=n<=N} mu(n) exp(-n*x)`, the existing exact integral is
`E_N(r)=integral_0^infinity x^(r-1) F_N(x)^2 dx`.
The diagonal is uniformly bounded for each `r>1`. Bounded returns of the signed
off-diagonal covariance, for orders cofinal above one, imply RH through the
existing Mellin–Plancherel theorem. The unresolved step is this upper bound for
the literal integer prefix, with its whole shrinking cusp retained.

## Work plan

1. Search full corpus statements and proof methods for signed renewal energy
   mechanisms; inspect exact source identities and applicability.
2. Attack the finite divisor-renewal equation by an energy pairing. Test every
   proposed sign on the actual coefficients before attempting an infinite limit.
3. If it fails, retain its exact source defect and test a compensated inequality;
   formalize only a dependency-closed result that settles the attempted mechanism.
4. Audit targeted Lean files and axioms; update only justified route-independent
   facts in the global ledger. Do not count a conditional receiver as an RH proof.

## Source and method search

- `research 'Mobius Laplace covariance cusp' --mode deep`: partial result;
  semantic deadlines and unavailable Qdrant lane; generated queries confused
  Möbius arithmetic with Möbius transformations. No applicable producer found.
- Exact-name and signed-renewal method searches launched next. Available corpus
  hits must be checked against source and this Lean toolchain.
- Broad arXiv searches: hypocoercivity, renewal, discrepancy, balayage, prioritizing
  June–September 2026. [Bouin–Dolbeault–Ziviani, 2608.28120](https://arxiv.org/abs/2608.28120)
  suggests coupling a weighted norm with dissipation; its kinetic equation and
  stationary-state assumptions have not been realized for this source.
- [Doron et al., 2606.24471](https://arxiv.org/abs/2606.24471) tracks second moments
  during random-generator insertion. A random-code theorem supplies no estimate
  for deterministic Möbius coefficients without a proved arithmetic comparison.

## Conjecture/proof loop

Pending: retain the finite identity
`sum_{1<=k<=N} F_floor(N/k)(k*x)=exp(-x)` and pair its full nonidentity part
with `F_N`. Determine its actual sign before invoking accretivity or dissipation.

## Log

- 2026-09-11 — Opened source-specific energy attack from Route E's moving-cusp
  frontier. Existing absolute renewal contraction and complete-prime substitutions
  are excluded; this attempt retains signed finite cutoffs.
