# TG C9.22: original Gamma clock admission in the tested Hardy nuclear ideal

- **Stage:** 3-formalized
- **Route:** TG, the Gamma component of completed source-to-Hardy compatibility
- **Predecessor:** tg-gamma-clock-hardy-phase.md
- **Ingredients:** tg-hardy-commutator-nuclear-continuity.md; tg-strong-nuclear-multiplier-admission.md
- **RH status:** open. Native prime–polar energy, full joint cubic compatibility, and strict sub-unit control remain unresolved.

## Exact new result

For every fixed intrinsic Schwartz spectral test g and every countably generated
cofinal family eps→0+, R→infinity, the original clock scattering unitaries U_i
satisfy

 T_i(g)=M_g(U_i^* P U_i-P) → M_g(U^* P U-P)

in the genuine trace norm. Here P is the original CCM Hardy projection and U
is the existing Gamma scattering unitary, with its exact original orientation
and factor two. Every finite cutoff with eps>0 is genuinely Schatten one.
Their ordinary cubic traces converge to the cubic trace of the displayed full
operator. Neither the trace-norm limit nor the cubic limit requires an all-stage
positivity premise or a nontrivial-filter premise; eventual positivity follows
from cofinal eps→0+.

The result retains g. It does not assert that the bare projection difference is
nuclear, remove localization from the joint TG cubic, or admit the arithmetic
source. No RH-strength analytic premise is added.

## Dependency-closed paper proof

1. Write gamma(u) for the literal positive Gamma clock density. The existing
   first-moment majorant extends to every u^(n+1)gamma(u), n>=0, by the actual
   polynomial-times-exponential integral theorem. Each moment is integrable on
   the entire original positive half-line.
2. A common real derivative family covers the full and every retained source:
   K_0(t,u)=(tu-sin(tu))gamma(u)/u;
   K_1(t,u)=(1-cos(tu))gamma(u);
   K_(n+2)(t,u)=u^(n+1)sin(tu+n*pi/2)gamma(u).
   Local domination of K_1 and global moment domination of the higher kernels
   justify every differentiation under the original integral.
3. The full-minus-cutoff Hardy lift is exactly the integral of K_0 over the
   discarded set (0,infinity) minus [eps,R]. Its n-th derivative is exactly the
   integral of K_n over that same set. Discarded moment masses tend to zero by
   the cofinal almost-everywhere cover theorem. The zeroth error is bounded by
   2t^2 times the first discarded moment, the first by |t| times that moment,
   and every higher error by its corresponding moment. Thus each error jet is
   bounded globally by e_n(i)(1+|t|)^2, with e_n(i)>=0 and e_n(i)→0.
4. Uniform polynomially weighted error estimates are closed under addition
   and multiplication. The product proof retains both linear error terms and
   the product of the errors. The exact ODE U_i'=a_i U_i, with a_i=2i Theta_i',
   and the complete Leibniz recurrence propagate convergence of the coefficient
   jets and the zeroth unitary phase to every exponential jet. The coefficient
   errors are precisely derivatives of the discarded original phase. All
   finite cutoff phases are temperate by the existing unitary-ODE theorem.
5. Multiply by the fixed Schwartz g. Every summand in the full Leibniz formula
   is controlled by its vanishing error coefficient times an actual Schwartz
   seminorm of g. Hence U_i g→Ug in every Schwartz seminorm. This applies to
   every cofinal endpoint family by eventual agreement on positive eps.
6. The two exact multiplier orderings and H=2P-1 give

   T_i(g)=(1/2) U_i^* (delta(U_i g)-delta(g) U_i), delta(h)=[H,M_h].

   Bundle this expression in the existing genuine S1 carrier. C9.22a gives
   delta(U_i g)→delta(Ug) in S1. C9.21 gives strong convergence of U_i; the
   isometry identity gives strong convergence of U_i^*. C9.22b admits the fixed
   right nuclear factor. The uniform norm-one bound and a two-term difference
   identity admit the outer left action with its varying nuclear factor.
   The same algebra identifies the limiting bundle with the original full
   tested Hardy projection difference.
7. S1 convergence controls the operator norm. The bounded strong left-action
   argument therefore admits successive nuclear products, including the cube.
   The ordinary trace is continuous in genuine trace norm. Exact source
   identifications then give the original cubic-trace limit, without any
   self-adjointness assumption on a complex Schwartz test.

## Lean implementation and audit

New leaves, all wired in RHTower.lean:

- SoninGammaClockPhaseJets: 25 public declarations, exact all-order original
  source derivatives, vanishing discarded moments and global weighted errors.
- PolynomialJetMultiplierLimit: seven public declarations, weighted-limit
  algebra, ODE propagation, and fixed-test Schwartz convergence.
- SoninGammaClockSchwartzLimit: six public declarations, actual finite phase
  temperateness and all-order/cofinal Schwartz admission.
- SoninGammaClockNuclearLimit: four public declarations, the literal tested
  operator, its nuclear membership, trace-norm limit, and ordinary cubic limit.

Five existing helper declarations were exposed without changing their proofs:
four source bounds in SoninGammaClockHardyPhase and the unitary-ODE temperate
closure theorem in CCMArchimedeanPhaseTemperate.

Every new and modified leaf passed the exact final foreground command
`lake --old env lean <leaf> -o <olean>`, with exit 0 and empty diagnostics.
No full or umbrella build, subagent, numerical experiment, heartbeat override,
added axiom, admitted proof, commit, or push was used.

The separate `/tmp` foundations audit exits 0 for all 42 new public declarations
and all five exposed helpers. Every dependency list contains only propext,
Classical.choice and Quot.sound. The generated index refresh exits 0; all 42
new public entries are present. Authoritative lint exits 1 for 17 unrelated
unreachable modules, with no finding in this work. No globally clean-lint claim
is made.

Audit artifacts: `/tmp/tg-c922-clock-jets-final.log`,
`/tmp/tg-c922-polynomial-limit-final.log`,
`/tmp/tg-c922-clock-schwartz-final.log`,
`/tmp/tg-c922-clock-nuclear-final.log`,
`/tmp/tg-c922-phase-expose-final.log`, `/tmp/tg-c922-ode-expose-final.log`,
`/tmp/tg-c922-clock-jets-axioms.lean`,
`/tmp/tg-c922-clock-admission-axioms.log`,
`/tmp/tg-c922-clock-admission-index.log`, and
`/tmp/tg-c922-clock-admission-lint.log`.

## Corpus grounding and contribution assessment

The moment, exponential-jet and actual-nuclear deep searches were nonpartial
snapshots with incomplete background compiler refresh. Candidate declarations,
source arguments and proposed ingredient sets were inspected. Unrelated Gamma
moment laws, L2 multiplier formulas and finite matrix trace cancellation did
not supply the source admission. The actual proof uses the literal first-moment
bound, real derivative kernels, the existing Gamma ODE, original Hardy product
identity, actual Hankel nuclear continuity, and HS-factor strong-limit bounds.

This closes the fixed-Schwartz Gamma source-to-Hardy nuclear/cubic gate, beyond
strong convergence alone. Next hard work concerns the unchanged native
prime–polar energy and full joint cubic/sub-unit producers; re-proving the
Gamma admission or silently removing the fixed test would not advance TG.
