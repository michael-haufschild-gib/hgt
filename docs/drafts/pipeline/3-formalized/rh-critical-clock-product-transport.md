# Actual critical clock product under joint prime/cutoff changes

- Owner: resumed clock/source task; own fact log.
- Type: THEOREM, formalized source transport and density cancellation; not an RH proof.
- Lean: `formal/GaloisForLFunctions/RHTower/MobiusDivisorCriticalClockProductTransport.lean`.
- Capstone: `RHTower.mobiusDivisorCriticalClockTriangularPairing_density_cancellation`.
- Mission: prove or falsify RH from the actual arithmetic source with a closed Lean proof.
- Frozen target: preserve the original normalized two-head product, its clock
  measure, and both moving endpoints under prime insertion. Produce the exact
  finite-window correction, without replacing either signed head by an envelope.

## Corpus facts and whole-route meaning

- `MobiusDivisorDilationMeanRenewal` proves the complete-ray four-term renewal
  from literal prime insertion. The complete integral suppresses the different
  finite upper boundaries of the copied terms.
- `MobiusDivisorPrimeFibreHomothety` keeps the two actual cutoffs and the mixed
  fibre product. Its raw copied square mass scales by `p`; this alone says
  nothing against the original quadratic normalization at cutoff `p*N`.
- `MobiusDivisorQuadraticCompletionSPEWeld` identifies a uniform quadratic cap
  through complete prime insertion with a sufficient RH producer. Exhaustion
  and a uniform cap remain unproved.
- The preceding inverse-cube single-head sign theorem removes the second
  signed factor. It does not settle the current target.

## Reframe and exact paper attack

Keep the cutoff as a clock coordinate. Set `g_P(t)=H_P(exp t)/exp t`, using
the actual continuous processed head. Prime insertion gives
`g_(P+p)(t)=g_P(t)-p^(-1/2)*g_P(t-log p)`.

Use the finite pairing
`C_P(Y,X)=∫_(0,X] (H_P(Y*x)/(Y*x))*(H_P(x)/x) dx/x`.
Thus its arithmetic expression is `(1/Y)*∫ H_P(Y*x)*H_P(x)/x^3 dx`.
The inverse cube here comes from TWO original normalized heads and the clock
measure `dx/x`; no extra decay is inserted into a single-head readout.

Change of variables and the literal insertion law force

`C_(P+p)(Y,pX) = C_P(Y,pX) + C_P(Y,X)/p
                 - (C_P(pY,X)+C_P(Y/p,pX))/sqrt(p)`.

Finite reciprocity gives `C_P(Y,X)=C_P(1/Y,YX)`, so the diagonal law is

`C_(P+p)(1,pX)-C_P(1,pX) = C_P(1,X)/p - 2*C_P(p,X)/sqrt(p)`.

All terms remain actual source products. The copied square and mixed terms
retain the smaller endpoint `X`; replacing them by terms at `pX` is invalid.
An arbitrary interval can be treated by endpoint subtraction, preserving both
the entrance and exit flux. The theorem must supply all integrability facts.

For the triangular weight, retain the clock age as well:
`A_P(y,T)=∫_(t≤T) (T-t)*g_P(t+y)*g_P(t) dt` and
`D_P(y,T)=∫_(t≤T) (1-t/T)*g_P(t+y)*g_P(t) dt`.
The source vanishes at nonpositive times, so `A_P(y,T)=T*D_P(y,T)` also
holds at the degenerate clock `T=0`. With `a=log p`, exact translation gives

`(T+a)*D_(P+p)(y,T+a) = (T+a)*D_P(y,T+a) + T*D_P(y,T)/p
  - (T*D_P(y+a,T)+(T+a)*D_P(y-a,T+a))/sqrt(p)`.

The weighted reciprocity is `A_P(y,T)=A_P(-y,T+y)`. Thus at zero lag,

`(T+a)*(D_(P+p)(0,T+a)-D_P(0,T+a))
   = T*D_P(0,T)/p - 2*T*D_P(a,T)/sqrt(p)`.

The cutoff-dependent normalization factors cannot be dropped. This is the
product-preserving and weight-preserving finite source law under examination,
not a claim that this quadratic triangular observable equals the scalar
Suzuki prime--polar action.

The literal density in the existing physical squarefree profile is
`rho_P = squarefreeDensity * ∏_(q∈P) q/(q+1)`.
It satisfies `rho_(P+p)=rho_P*p/(p+1)`. Combining this exact source factor
with the finite age-weighted identity cancels the copied positive diagonal:

`rho_(P+p)*A_(P+p)(0,T+a) - rho_P*A_P(0,T+a)
  + 2*rho_P*sqrt(p)/(p+1)*A_P(a,T)
 = -rho_P/(p+1)*(A_P(0,T+a)-A_P(0,T)) <= 0`.

The last sign follows from monotonicity of the actual square-source age
primitive. Thus the positive copy is absorbed with a nonnegative clock-boundary
surplus; no sign of the remaining mixed correlation is inserted as a premise.
This is an actual cancellation between the inherited diagonal and the literal
density change, not an independent positive reserve added to the source.

## Falsification / remaining hard gate

- These identities do not imply that the signed mixed term is positive or
  large enough to absorb the copied diagonal. No such sign is assumed.
- The integrated pairing is not itself asserted RH-equivalent; its pointwise
  normalization is the original critical one. A uniform bound through an
  exhaustive changing core remains necessary for the whole route.
- A zero-lag positive copied diagonal is accompanied by one signed mixed
  correlation. The identity derives that term from the source but does not
  determine its sign or prove that it pays the diagonal through exhaustion.
- Density cancellation does not identify the finite arithmetic selection energy
  with its fixed-core physical profile uniformly in a changing core. The
  finite-counting discrepancy and exhaustive mixed-correlation control remain
  unresolved; the profile identity alone is not a quadratic completion proof.
- Corpus searches: broad deep insertion search and delayed-autocorrelation
  method search completed with `partial=false`; restricted boundary hybrid
  search returned `partial=true`. Compiler coverage is mostly source-only.
  No indexed candidate supplied the finite triangular joint law; this is not
  a claim of completeness or literature priority.
- Recent broad arXiv screening opened the abstract of
  [Parity Anomaly as Modular Commutator with Massless Dirac Fermion](https://arxiv.org/abs/2608.26078).
  No verified arithmetic lemma transfers from that abstract; it is not a proof input.

## Lean status

- `mobiusDivisorCriticalClockHead_complete_integer_wall` identifies the source
  at complete integer walls with the exact original Abel moment divided by its
  cutoff. This discharges the normalization claim.
- Finite product, logarithmic change of variables, reciprocal clock transport,
  causal prime delay, triangular integrability, both joint renewal laws, and
  density cancellation are closed in Lean. The capstone has no sign, rate,
  uniformity, RH, or integrability assumption.
- `lake env lean /tmp/hgt-critical-clock-product.lean` passed. Axiom audits for
  all capstones returned only `[propext, Classical.choice, Quot.sound]`.
- Final named audit passed:
  `lake build GaloisForLFunctions.RHTower.MobiusDivisorCriticalClockProductTransport`.
  One owned Lean process; umbrella import added; no full or umbrella build.
- Index regeneration and whitespace checks passed.
- Repository lint failed on the same four unrelated unreachable modules:
  `ThetaCuspHawkingBMLiteralCyclicPeierlsLowerWeylRadialDetector`,
  `ThetaCuspHawkingBMLiteralCyclicPeierlsSelfInverseSquarePhysical`,
  `ThetaCuspHawkingBMLiteralCyclicPeierlsSelfMixedCuspFlux`, and
  `XiHeatCassiniWoldJointDepthMobiusSourceTransport`.
  It reported no error against this module; the whole repository is not certified.

## Next hard attack

The copied diagonal is now cancelled with its actual density factor and the
finite clock surplus retained. The remaining source term is the signed mixed
correlation in this exact identity. Establish cumulative control of that term
through exhaustive prime insertion and a uniform comparison with finite
arithmetic energy. Replacing it by a single-head primitive, dropping the old
clock factor, or assuming the fixed-core profile is uniform would lose the
hard problem again.
