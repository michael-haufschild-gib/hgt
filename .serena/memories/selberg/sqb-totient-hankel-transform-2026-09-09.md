# SQB full totient-Hankel transform and mean-pole cancellation

Active goal remains unconditional RH via SQB. RH and occurrence remain UNPROVED. Frontier map is READ ONLY; NO numerical computations; no subagents. Each turn opens full proof chain, hardest mathematical obstacle, analytical attack. Do not generate further no-go modules or merely conditional occurrence receivers.

## Closed positive result

New module `formal/GaloisForLFunctions/RHTower/SelbergThetaTotientHankel.lean`, namespace `RHTower.SelbergThetaTotientHankel`, 14 public declarations, wired once in RHTower umbrella.

Use g = SelbergThetaDilationTransform.profile rho, J(v)=∫conj(g(t))g(v-t)dt. Actual kernel:
H(v)=Σ(q:PNat) φ(q)/q ∫ J(v-2 log q-log(1+x²))/sqrt(1+x²) dx.

For P : D4BMEisensteinAbsoluteConvergenceParameter (Re P.s>1), put s=P.s-1/2. `row_eq_totient_integral` identifies the literal square-root kernel. `row_integrable`, `row_norm_summable` prove absolute weighted row integrability and summability of all integrated norms; `kernel_integrable` proves complete sum integrable. Exact:
transform H (-I*s)=Λ(2s)/Λ(2s+1)*transform J(-I*s).
Public `transform_kernel_completed` and `transform_kernel` state this with P. No discarded denominators/cross terms, no assumed Fubini or occurrence.

At actual q : XiZeroCopy with rho=q.1, d_s=2-exp((s-1/2)log2), B_rho(s)=d_s*dslope xi rho (rho+1-2s). Both original factors vanish: d_s*xi(rho+1-2s)=(1-2s)B_rho(s), likewise conj rho. Define public `continuation q s`:
C(s)=(2s-1)(2s+1)*xi(2s)/xi(2s+1)*B_conj(rho)(s)*B_rho(s).
`continuation_analytic`: analytic at every Re s>0 (xi denominator Euler-side nonzero).
`transform_kernel_eq_continuation`: C equals actual full-kernel transform on Re s>1/2.
`continuation_mean`: C(1/2)=0.
`hasDerivAt_continuation_mean`: C'(1/2)=2/xi(2)*conj(xi'(rho))*xi'(rho). No simple-zero premise.
`kernel_mean_abel_limit`: actual Laplace integrals tend to zero as real sigma decreases to 1/2 from above. This is an Abel limit, NOT original integral convergence beyond the safe domain.

Other public definitions `row`, `kernel`; all 14 counted include these and continuation.

## Exact corpus reuse

`ThetaCuspHawkingBMEisensteinActualZeroFourierCoefficient` already provides zero Ramanujan L-series ζ(2P.s-1)/ζ(2P.s) and `d4BM_completedZeroWeylFactor_eq_reflectedConstantTerm`. Its zero Ramanujan coefficient is proved equal to Nat.totient via explicit units/isUnit equivalence. Absolute arithmetic summability reuses `ArithmeticFunction.LSeriesSummable_mul` on id and Moebius, then `.subtype`. Generic Fubini helpers kept private in new module.
`GaloisForLFunctions.HTGeometry.integrable_tsum_of_summable_integral_norm` and `integral_tsum_eq_tsum_integral_of_summable_integral_norm` are in HTGeometry namespace, despite second theorem residing in an RHTower file.
Existing `xi_deriv_conj`, `deriv_xi_conj`, `xi_conj` are all available transitively from current imports.

## Verification

Scratch and source `lake env lean` clean. Final preflight `lake --old --no-build build GaloisForLFunctions.RHTower.SelbergThetaTotientHankel` found ONLY leaf stale. Final named `lake --old build ...` passed, only 1 Built line, 32s. Dependency replay messages are historical and not fresh compiles. All 14 #print axioms via /tmp/sqb34_axioms.lean show only propext/Classical.choice/Quot.sound. Index refreshed. Scoped whitespace and read-only frontier checks clean. All owned Lean/Lake processes terminal.
Repository lint ran but failed on one separately/concurrently added untracked module `GaloisForLFunctions.HTGeometry.GomesDilatonDensityShape`, unreachable from HTGeometry umbrella. Do NOT call global lint passing. SQB module wired once and has no lint error. This peer integration was not modified.
Logs /tmp/sqb34_{source_check,build_preflight,leaf_build,axioms,index,lint}.log. Scratch /tmp/sqb34_kernel.lean.
Report `docs/drafts/pipeline/3-formalized/sqb-theta-totient-hankel.md`; current loop card section 5 updated equations (16),(16a),(16b), verification section updated. Universal STATUS unchanged because result is route-specific. Frontier untouched.

## Remaining hardest obstacle / next analytical work

Full chain: actual theta source -> normalized native approximate vectors at full Xi target -> occurrence -> real-preimage classification -> critical line -> RH.
For dilation-family Q(L), paper Gram is <Q(L),Q(M)>=K(M-L)+H(L+M); full energy G(w), residual energy G(w''-kappa²w). Need positive denominator and relative residual tending zero. Native Gram identity / real-frequency boundary integration still unproved. C(s) is proved holomorphic on Re s>0 but original H weighted integrability outside Re s>1/2 and real boundary/contour/norm interchanges remain open. The new double cancellation and actual Abel limit are the positive source data for this step.
Do not confuse this g/dilation H kernel with the different first-order centered vector V from SelbergThetaNativePairing; V already nonzero/unit normalized, but neither source currently has a proved vanishing full residual family. Do not restate normalization or gaussian real-frequency no-go.

## Lean lessons

`Measurable (archKernel P)` / `Integrable (fourierIntegrand ... z)` require eta-expansion via change before simp_rw pointwise identities. Generic integral_sub_right_eq_self needs explicit `(fun v => norm (f v))` under a norm. integral_integral_swap on `.swap` needs typed uncurry Integrable local to fix inference. Explicit typed unit equivalence avoids huge Fintype instance defeq in Submonoid.unitsTypeEquivIsUnitSubmonoid. `IsUnit.unit_of_val_units` takes u.isUnit, not u. AddChar.map_zero_eq_one, not map_zero. For derivative product instance diamonds, use typed HasDerivAt plus `simpa using!`, not naive convert. Use explicit `(xi_differentiable.analyticAt _)` argument and local `have hxiD := xi_differentiable` for fun_prop. No need another independent proof of arithmetic or Gamma factors.
