# RP-56: complete short quadratic dispersion

Status: active hard-frontier problem; RP-56 obtained no frontier theorem. Route RP,
unconditional RH. RP-55 made no frontier progress. Positive-damping
negative-work payment, signed high-LCM control, and both history debts
remain open.

Read the actual short quadratic reconstruction and reflected pairing.
Target the complete signed work at x=exp(T), N=floor(sqrt(x)), retaining
both explicit short main terms and every source term of the N-by-N
matrix. Its existing bounded correction is already paid. The bound of
the work itself is explicitly RH-equivalent in the corpus.

First conjecture: combine the separable large-argument terms of the
matrix with the short main terms before estimating; use the exact
harmonic Mobius moment identities to see whether their remaining
quadratic form is dissipative. Then handle the residual source matrix
by a bilinear estimate with the physical cutoff retained. No independent
norm or sign of an isolated reflected component is assumed.

## Exact source used

Write D for ccmLogChebyshevDeficitPrimitive, S for
ccmPrimeDeficitDilationSource, F for ccmPrimeDeficitDivisorSource,
A=gamma+1, B=log(2*pi)/2, and R=S-A*(exp(t)-1)+B*t.
The existing short reconstruction is

    D(T) = 2*Main_N(T) - sum_(a,b<=N) mu(a)*mu(b)*F(T-log(a*b))
           + 2*sum_(a<=N) mu(a)*R(T-log a),
    N=floor(exp(T/2)).

The last term already has a square-root bound; its constant-limit
refinement is also already proved. The remaining complete work is
explicitly RH-equivalent in CCMPrimeDeficitShortQuadraticWork.lean.
CCMPrimeDeficitResidualPairing.lean supplies the two exact causal ramps
of F. CCMPrimeDeficitShortSourceMatrix.lean already excludes blanket
positive semidefiniteness of the actual matrix. None is a new result.

## Paper trials and unpaid terms

1. Combining the separable exponential terms with Main_N exposes the
   harmonic Mobius moment and its logarithmic moment together. The
   cancellation of their leading linear piece leaves a quadratic
   moment/tail correlation. No sign or critical estimate was proved.
   A tentative Laurent-constant calculation was not checked against
   corpus constants and is not used as evidence. Dropping the remaining
   source matrix or its near-cutoff part would invalidate this trial.

2. From the actual causal ramps, on Re(s)>1 the paper Laplace formulas are

       S_hat(s)=zeta(s)/(s*(s-1))+zeta'(s)/s^2,
       F_hat(s)=zeta(s)^2/(s*(s-1))+zeta(s)*zeta'(s)/s^2.

   These formulas have not been added to Lean in this turn. The infinite
   Hankel pairing at two absolutely convergent parameters s,t is
   (F_hat(t)-F_hat(s))/(s-t). Analytic continuation vanishes at two
   distinct zeta zeros; its coincident value at a simple zero rho is
   -zeta'(rho)^2/rho^2. This is NOT admission of an infinite pairing at
   those zeros and gives no physical positivity.

   For the actual finite square u,v in [0,R], put
   L_R(s)=integral_0^R F(v)*exp(-s*v) dv. Directly splitting u+v at R gives

       I_R(s,t) = [L_R(t)-L_R(s)
           +exp((s-t)*R)*(L_(2R)(s)-L_R(s))
           -exp(-(s-t)*R)*(L_(2R)(t)-L_R(t))]/(s-t).

   Both upper-triangle terms remain. The infinite divided difference
   cannot replace this expression at critical or off-critical zeros.

3. A positive critical-line norm estimate loses the relevant length.
   MoebiusMollifiedCriticalMoment.lean:176 gives, for a raw prefix of
   length N and a fixed ordinate window Y>=4, a bound proportional to
   sqrt((2Y+8N^2*(1+log(N^2)))*(1+log(N^2))^4
        *D*Y*(1+log Y)^4).
   This has a factor N, not a uniform polylogarithmic bound. A decaying
   weight in ordinate does not remove that loss on a fixed compact
   window. Varying the prefix length with ordinate has not been shown
   compatible with the physical square-root reconstruction. The
   three-lines source retains this loss near the critical edge.
   These modules were inspected as source, not freshly built here.

4. Retaining the signed contour gives a more precise unpaid expression.
   Let M_N(s)=sum_(n<=N) mu(n)*n^(-s), Z_N=zeta*M_N and
   L_N=M_N'+(T/2)*M_N. Along any finite contour avoiding 0 and 1,
   direct differentiation yields the paper identity

       integral exp(s*T)*M_N(s)^2*F_hat(s) ds
        = [exp(s*T)*Z_N(s)^2/(2*s^2)]_endpoints
          +integral exp(s*T)*zeta(s)^2*
             (M_N(s)^2*(1/(s*(s-1))+1/s^3)
               -M_N(s)*L_N(s)/s^2) ds.

   At T=2*log N, L_N has coefficients mu(n)*log(N/n). On 1<n<=N,
   the coefficients of zeta*L_N equal +Lambda(n), by the existing
   Sieve/LinearMollifierVonMangoldt theorem. The sign is positive.
   This does not control the long coefficients or their mixed terms.
   A critical contour shift also requires its pole-at-one residue,
   horizontal edges and limiting estimates. All remain part of the
   proof obligation. The displayed products are signed complex squares,
   not modulus squares. No positivity or endpoint deletion is justified.

5. The exact action permits arbitrary coefficient extension beyond N,
   but leaves the entire Mobius head through N fixed. Thus extension
   freedom does not by itself shorten the problematic mollifier. In
   Re(s)>1, Z_N-1 has coefficients supported above N, so its square is
   supported above N^2. This recovers the already-proved short action
   identity, not a new bound. Keeping its logarithmic partner returns
   the mixed Lambda/residual correlation in trial 4.

## Search audit

All searches used the documented deep command with module RHTower and
300-second budgets; candidate_lemmas, source_arguments, proof_ideas and
ingredient_sets were inspected. All relevant retrieved declarations
were source-only. No compiler applicability was inferred from retrieval.

| Query mechanism | Session / exit | Query generation | Coverage / current | Files | Partial |
|---|---|---|---|---|---|
| short quadratic Mobius bilinear dispersion | 62304 / 0 | 1191387 | 1191421 / 1191423 | 64666 | false |
| divisor-source Laplace Hankel divided difference | 10299 / 0 | 1191433 | 1191451 / 1191452 | 64671 | true |
| raw Mobius critical mollifier small-ordinate norm | 93760 / 0 | 1191468 | 1191484 / 1191499 | 64672 | false |
| signed quadratic zeta-derivative contour | 39394 / 0 | 1191528 | 1191538 / 1191539 | 64675 | false |

All coverage inventories reported zero pending files. Coverage snapshots
were older than current generation; semantic coverage was unavailable
and unmeasured, background refresh incomplete. The Hankel query left
semantic retrieval unfinished after a local runtime deadline. Other
queries reported no unfinished stage or errors. Hits concerning
meromorphic inner functions require that premise and use a different
carrier. The suggested BoxFubini ingredient set assumes nonvanishing
and does not bound this quadratic contour. Neither is imported as a
producer. Search failure is not an absence proof.

## Checkpoint

No new critical estimate, unconditional Lean theorem, proof or
falsification of RH. No Lean source edits or builds this turn; no new
umbrella entry is appropriate. RP-52 remains the latest verified advance.
The global lint gate was not rerun without Lean changes; its previously
reported unrelated unreachable modules remain an outstanding gate issue.

Continue the joint finite-contour/physical-cutoff estimate, retaining
the smooth pole residue, logarithmic Mobius factor and every boundary.
The immediate target is cancellation in this complete expression,
rather than separate raw-prefix norms or another exact reconstruction.
Positive-damping negative-work payment, signed high-LCM control and
both native history debts remain open. This is an unsuccessful estimate
trial, not a retired route or a claimed no-go theorem. Goal active.
