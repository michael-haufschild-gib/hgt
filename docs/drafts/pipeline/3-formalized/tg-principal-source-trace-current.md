# TG C9.11n–o — complete principal response and harmonic obstruction

- **Stage:** 3-formalized
- **Status:** complete response, harmonic coefficient and raw-admission obstruction fully formalized; all sixteen public declarations across five leaves axiom-audited
- **Route:** TG, source-derived joint prime–Gamma relative admission
- **Predecessor:** C9.11m, coherent proper-prime-power source assembly

## Hard question

After admitting the original proper-prime-power family, the linear prime
shell still has its original coefficient `p^(-1/2)`. Neither failure of an
absolute majorant nor divergence of coefficient square energy decides the
complete two-leg correction response. Determine its exact trace current
before proposing a joint Gamma counterterm or carrier.

## Corpus evidence

`SoninTimeBandIdeal` defines `Q0=1-A-B`, `J=Q-Q0`, and proves the actual
response identity `C(D)=(1-Q)DJ-JDQ0`. `SoninTimeBandSchatten` proves J is
trace class at every positive aperture. A and B are the actual physical and
Fourier forbidden projections, and Q projects onto their common orthogonal
complement. The proper-source proof uses the actual right factors of J.

Three current deep searches are recorded in `/tmp/tg-c911n-*-search.json`.
All candidate and source-argument statements were inspected. They were
partial with snapshot coverage and an incomplete background refresh. The
targeted trace search returned the source trace-norm bound and relative
cyclicity infrastructure, but no theorem of the complete response trace
below. The generic first search mainly matched unrelated principal ideals;
the subsequent searches were restricted to Sonin modules.

## Exact trace identity: dependency-closed paper proof

For every bounded D and positive aperture,

`Tr C(D) = Tr (D(AB+BA))`.

Every trace operation here has a trace-class factor. Since A and B are
projections annihilating Q on both sides, `Q0 Q=Q Q0=Q` and `Q²=Q`.
Thus `J Q=0` and

`J-Q0 J = Q0²-Q0 = AB+BA`.

Cycle the trace-class J through the two original response terms:

`Tr C(D) = Tr (DJ) - Tr (QDJ) - Tr (JDQ0)`

`= Tr (DJ) - Tr (DJQ) - Tr (DQ0J)`

`= Tr (D(J-Q0J)) = Tr (D(AB+BA))`.

The right side is trace class because AB and BA are genuine time-band
factors. No positivity, self-adjointness or commutation premise on D is
needed. The resolvent disappears from this scalar current by exact
projection algebra; the full operator response is retained in its source.

The same algebra gives a stronger exact survivor before taking traces:

`C(D) = D(AB+BA) + [DQ0,J] - [Q,DJ]`.

Here `[X,Y]=XY-YX`; the last commutator reduces to QDJ because JQ=0.
Each commutator has a trace-class factor. Thus this is an exact operator
decomposition of the retained response, not just equality of scalar traces.
Both exact identities are now audited in `SoninCompleteResponseTrace.lean`.
Final `lake --old env lean` leaf audit passed; both public declarations depend
only on `propext`, `Classical.choice`, `Quot.sound`. The leaf is wired into
`RHTower.lean`; no umbrella build was run.

## Next conjecture and limits

Specialize D to the original symmetric prime dilation. Derive the actual
time-band diagonal trace, then determine whether its weighted prime trace
has a surviving harmonic component. This is a conjecture, not a proved
divergence assertion. A failure of raw admission must expose the exact
remaining source contribution; it does not retire the joint prime–Gamma
route. No arbitrary subtraction, Gram replacement, or RH-strength
convergence premise is admitted.

C9.11m is now fully formalized in P3 `tg-unsquared-relative-source-assembly.md`: the full original proper-prime-power family is admitted in trace norm.
The original linear-prime harmonic transfer is the next Lean target.
Full joint admission, Hardy
cubic compatibility and a source-derived strict sub-unit law remain open.

## C9.11n working log, 2026-10-02

The complete-response deep search was non-partial with snapshot coverage;
the dilation-trace search was partial. The rectangle-kernel search was
non-partial but returned mostly unrelated matrix/Fourier hits. All three
had incomplete background refresh. Candidate and source-argument statements
were inspected; no admission claim relies on search completeness.

Source verification found the stronger existing identity `J²+J=AB+BA`.
The audited response decomposition uses this exact polynomial, `QJ=JQ=0`,
and genuine Schatten-1 cyclicity. It retains both original response legs.

Next paper candidate for the actual normalized `D_r f(x)=sqrt(r) f(rx)`:

`Tr(D_r A B)=sqrt(r⁻¹) ∫_{[-a,a]} ∫_{[-a,a]} exp(2πi(1-r⁻¹)xy) dy dx`.

Insert B by trace-class cyclicity, conjugate by the original Fourier
unitary, and identify the two finite-window Fourier kernels. The corpus
`SchurKernelComposition.opTrace_comp_op` supplies the exact diagonal
product formula. A scratch proof is constructing those actual kernels;
their identity with the original dilation operator must be checked before
any principal-prime divergence conclusion. No coefficient-energy argument
is substituted for the complete trace.

### Positive oscillatory survivor (paper derivation, Lean pending)

The sinc search was partial with snapshot coverage. It found
`HTGeometry/GoldenRuleSincIntegral.integral_sinc_sq`, an unconditional
Plancherel proof that `∫_ℝ sinc² = π`; source inspected. This yields a
positive exact representation of the apparent oscillatory obstacle. For T>0,

`Si(T)=∫₀^(T/2) sinc²(u) du + (1-cos T)/T`.

Differentiate `sin²(u)/u`: its derivative is
`sin(2u)/u - sin²(u)/u²`; integrate and use the zero-endpoint limit.
Both terms on the right are nonnegative and the first is strictly positive.
Evenness and integrability of sinc² imply `Si(T)→π/2`.

For `Phi_a(c)=∫_{[-a,a]²} exp(2πicxy)`, direct integration gives
`Phi_a(c)=2 Si(2πca²)/(πc)` for c>0. Consequently Phi is positive there
and `c Phi_a(c)→1`. Once the actual operator trace identification is
formalized, the two original dilation legs therefore predict

`sqrt(r) Tr(C(D_r+D_(r⁻¹))) → 2(Phi_a(1)+1) > 0`.

Thus the original linear-prime weight predicts an exact positive harmonic
trace contribution, not merely failure of an absolute majorant. This is
paper mathematics only at present: the kernel identification, endpoint
integrations and asymptotic transfer still require Lean audit. It motivates
canonical joint Gamma/pole cancellation; it is not an RH conclusion.

### Actual dilation identification audited

`SoninDilationTimeBandTrace.lean` passed its final foreground
`lake --old env lean` leaf audit. It proves `opTrace_dilation_timeBand`
and `re_opTrace_centralSoninCornerCorrectionResponse_dilationSum`.
The latter retains the full symmetric original response and both finite
window integrals. The exact kernel construction is square-integrable;
trace-class insertion and Fourier conjugacy identify it with the actual
operator. The leaf is wired; no umbrella build was run. Axiom audit and
the sine-current positivity/asymptotic formalization are next.

### Sine-current step audited

`SoninSineTraceCurrent.lean` passed the final leaf audit. It proves
`integral_sinc_eq_square_current`, `integral_sinc_pos`, and
`tendsto_integral_sinc_atTop`. The exact positive identity is recorded
without any endpoint singularity:

`∫₀^(2R) sinc = ∫₀^R sinc² + R sinc²(R)` for R≥0.

The finite current is strictly positive for every positive endpoint and
tends to π/2. Proof uses the corpus sinc² Plancherel normalization,
continuity at zero, and the exact endpoint derivative. No computations
or heartbeat increases. The two actual dilation trace declarations were
axiom-audited: only `propext`, `Classical.choice`, `Quot.sound`.

The latest central-window search was partial with pending coverage and
incomplete background refresh. Its candidate/source statements confirmed
the actual band-indicator Fourier formula; the scalar window identity is
being connected directly to the verified finite Fourier integral.

### Scalar window identification and exact coefficient

`SoninTimeBandTraceCurrent.lean` now proves the actual double Fourier
window equals `2 Si(2πca²)/(πc)` for c≠0. It also proves strict positivity
for c>0 and the exact asymptotic `c Re(Phi_a(c))→1`. Its first final leaf
audit passed; a redundant-tactic cleanup is being reaudited. All three
sine-current declarations passed axiom audit with the standard three
axioms only.

The hard remaining step on this card is now **transfer to the original
linear-prime family**, then canonical Gamma/pole cancellation. Conjecture:
for `S_p=(sqrt(p))⁻¹ C(soninPrimeDilationSignal p)`,
`p Re Tr S_p→2(Phi_a(1)+1)>0`, hence no raw trace-norm sum exists.
This is not inferred from coefficient energy: it follows on paper from the
verified complete two-leg trace, continuity at frequency 1, evenness of
the scalar window, and the verified large-frequency coefficient. These
remaining transfers and the non-summability claim are not yet Lean-audited.

Corpus verification: `soninPrimeDilationSignal p` is the exact original
symmetric prime dilation. `soninLogPrimePowerCoefficient` only indexes
proper powers k+2; no named linear residual assembly was found in the
targeted source search. The linear coefficient is the deleted first Euler
coefficient `(sqrt p)⁻¹`; it must be restored explicitly with the actual
response, not with a square-energy or Gram replacement. The principal
harmonic deep search was partial, snapshot-covered and refresh-incomplete;
all candidate/source statements were inspected.

For the next Lean step, the corpus gives `Nat.Primes.not_summable_one_div`.
`Subtype.val_injective.tendsto_cofinite` and `Nat.cofinite_eq_atTop` transport
the natural prime values to infinity. `intervalIntegral.continuous_primitive`
with `Real.continuous_sinc.intervalIntegrable` supplies continuity of Si.
Use the exact identities `sqrt(r)*sqrt(r⁻¹)=1`, `sqrt(r)²=r`; normalize the
verified complete response to `2(Phi_a(1-r⁻¹)+r Phi_a(r-1))`. The second
term is `r/(r-1)` times the already verified scaled window.

### Final validation checkpoint

All four final foreground `lake --old env lean <leaf> -o <olean>` audits
passed with no remaining diagnostics. All ten public declarations passed
the combined `/tmp/tg-c911n-all-axioms.lean` audit: only `propext`,
`Classical.choice`, `Quot.sound`. All four leaves are wired into RHTower;
no full or umbrella build was run. No computations, proof holes, added
axioms, or heartbeat overrides were introduced.

Authoritative lint ran and returned 11 unrelated unreachable-module
errors; none names these four leaves. Full report is retained in
`/tmp/tg-c911n-final-lint.log`. The index command completed successfully;
current API/gap/overview files were regenerated. Search and final audit
logs are retained. Temporary proof fragments are cleaned up.

This turn directly reduced the principal-source problem: the complete
response trace is now an exact positive scalar window current with known
large-frequency coefficient. It has not supplied joint prime–Gamma
admission, Hardy cubic compatibility, a strict sub-unit law, or RH. The
next conjecture remains the original linear-prime harmonic trace law
above, followed by source-derived Gamma/pole cancellation.

### C9.11o — original linear-prime harmonic law

Next conjecture is the exact positive coefficient of the original weighted
linear-prime correction response, with both dilation directions and correction
legs intact. Its paper proof is dependency-closed: evenness and continuity of
the verified sine-window current, square-root normalization of the complete
trace identity, and the verified large-frequency limit give
`p Re Tr S_p → 2(Phi_a(1)+1) > 0`. Prime reciprocal divergence then excludes raw
Schatten-1 summability by the continuous ordinary trace functional. The exact
coefficient is the positive survivor and required scalar cancellation datum;
this does not exclude a joint prime–Gamma construction.

Corpus search `/tmp/tg-c911o-linear-current-search.json` returned partial
pending coverage, background refresh incomplete, reranking deadline expired.
All candidate and source statements were inspected. They confirm proper-power
assembly, the complete response trace identity, and the distinction between
coefficient-energy divergence and the original linear source. The proof will
use the original source, not the squared-energy proxy. Scalar transfer and
Schatten-1 contradiction are now being formalized in scratch.


### Original linear-prime transfer — final leaf passes

`SoninLinearPrimeTraceObstruction.lean` defines the original source directly as
`(sqrt p)⁻¹ C_a(soninPrimeDilationSignal p)` in `SchattenOneOperator SoninL2`.
The literal double-window formula gives the exact identity

`p Re Tr S_p = 2(Phi_a(1-p⁻¹) + p Phi_a(p-1))`.

Evenness follows from evenness of sinc and oriented interval integration.
Continuity at frequency 1 follows from continuity of its primitive. The second
term factors as `p/(p-1) * ((p-1) Phi_a(p-1))`; its two factors tend to 1.
Hence `p Re Tr S_p → K_a=2(Phi_a(1)+1)>0`. Eventually the trace dominates
`K_a/(2p)`. Summability would contradict the corpus theorem
`Nat.Primes.not_summable_one_div`. The private continuous trace reader on the
genuine Schatten-one Banach space then rules out raw source summability.
This retains both correction legs and both normalized dilation directions.

Final foreground leaf command passed with an empty diagnostic log:
`/tmp/tg-c911o-leaf-final.log`. Umbrella import added, no umbrella build.
Axiom audit passed separately in `/tmp/tg-c911o-axioms.lean`: all six new
declarations use only `propext`, `Classical.choice`, `Quot.sound`.

### Next conjecture — literal polar cancellation on the source operators

Further searches are saved as `/tmp/tg-c911o-gamma-source-search.json`,
`/tmp/tg-c911o-continuum-search.json`, and `/tmp/tg-c911o-polar-search.json`.
All returned candidate/source statements were inspected; coverage was partial,
with background refresh incomplete. The latter two had full source inventory
snapshots but predominantly pending/stale compiler metadata. No new admission
claim is inferred from search absence.

Verified source files provide the actual log-dilation integral
`ccmIntegratedScaling`, the Gamma normal form `LΓ=A₁+R₁-1`, and the literal
polar density `2 cosh(u/2) du`. The critical prime atom is
`Λ(n)/sqrt(n)`; division by its nonzero logarithmic position gives exactly
`1/(k sqrt(p^k))` at `n=p^k`, including the linear source used here.
Therefore the candidate logarithmic polar tail is determined by that same
source: `(2 cosh(u/2)/u) du`, not by an arbitrary normalized trace probe.

The next operator target pairs the original prime head with this polar
continuum before any cofinal limit. Derive its actual two-leg kernel and prove
or falsify trace-norm Cauchy convergence. The already admitted proper powers
can then be restored without another convergence premise. The near-zero
Gamma/pole normalization and meromorphic transport must also be derived from
the existing source. A scalar trace match cannot establish this operator law.

First paper diagnostic: separate prime and pole norm estimates cannot prove
this signed limit; the harmonic trace identified here must cancel inside the
source. The corpus's quantile result only supplies `o(e^a)` on the physical
mass-plus-Gamma form domain, not trace-norm Cauchy control. Do not silently
upgrade that result. Next derive the signed kernel using the actual right
factorization `J=AB(1-AW)+BAW`, keeping the full adjoint response.


### C9.11o final checkpoint

The leaf and all six public axiom queries passed. The module is wired into
RHTower. Authoritative lint reports 13 unrelated unreachable leaves, none in
this change; exact log `/tmp/tg-c911o-lint.log`. Corpus index completed and
all six new declarations are present in LEAN_API. No full build, computation,
proof hole, added axiom, or heartbeat override. Source proof scratches are
removed; final audit files/logs and corpus-search results are retained.

Raw-admission no-go and its exact positive survivor are recorded in
`../5-failed/tg-raw-linear-prime-nuclear-admission.md`. The hard continuation
work proceeds in `../1-in-progress/tg-principal-polar-operator-cancellation.md`.
This closes the exact-trace card, not TG or RH.
