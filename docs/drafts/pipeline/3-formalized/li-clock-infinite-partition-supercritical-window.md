# Infinite partition: strict supercritical weighted-window obstruction

- **ID:** LI-CLOCK-INFINITE-PARTITION-SUPERCRITICAL-WINDOW
- **Stage:** 3-formalized
- **Type:** THEOREM (complete paper, source/proof, named/direct and all-public axiom audits PASS)
- **Source:** [complete source boundary](../3-formalized/li-clock-infinite-partition-density-tail-boundary.md), [weighted quarter-window](../3-formalized/li-clock-infinite-partition-quarter-window.md)
- **Mission:** identify exact source-truncation limits relevant to the actual completed-clock compensation problem, without claiming an inverse-clock sign.

## Exact theorem

For N>0 set L_N=log(2N), s=2-sqrt(2). Keep the literal complete actual/reference finite Borel kernels and each source's own half-tilt mass Z_X,N. For every fixed c>1/4, beta=2(sqrt(c)-1/2)^2>0, and every complex z with |z|>=cL_N,

    exp(-2|z|)*||B_X,N(z)||
      <= exp(-beta*L_N)/(Z_X,N²*(c-1/4))
      <= exp(-beta*L_N)/(s²*(c-1/4)),    X=A,U.

The finite numerator refinement and the independent polynomial estimate

    exp(-2|z|)*||B_X,N(z)||
      <= L_N*exp(-beta*L_N)/[(sqrt(c)+1/2)*Z_X,N²]
      <= (2L_N/s²)*exp(-beta*L_N)

are retained. The constant envelope improves the polynomial envelope asymptotically at fixed c; no pointwise ordering of those two envelopes for every small N is asserted.

Both complete finite kernels vanish after scaling uniformly throughout the entire exterior, and along every qualified natural source sequence with arbitrary exterior complex clocks. At t_N=cL_N, the scaled finite real kernels tend zero; their signed finite-minus-infinite errors tend -lambda/2 and -1/2, and their absolute/complex-norm errors tend lambda/2 and 1/2.

For every C>1/4, the shared interior real witness z_N=((C+1/4)/2)L_N eventually has weighted actual error at least lambda/4 and reference error at least1/4. Neither source admits a vanishing sequence of eventual uniform weighted error bounds on the open or closed disk of radius CL_N. No positivity assumption on that hypothetical error sequence is needed.

Complete frozen proof and S1–S4 target matrix appear below. The [critical c=1/4 transition](../3-formalized/li-clock-infinite-partition-critical-transition.md) is fully formalized in three audited Lean leaves. The [coupled supercritical ratio and sharp real decay rate](../3-formalized/li-clock-infinite-partition-supercritical-ratio.md) are fully formalized across three audited Lean leaves. Inverse-clock sign, completed-clock compensation and RH remain OPEN. The immutable paper below predates these two follow-ups; its exclusions record that theorem's original scope.

## Complete Lean certificate

2026-09-30 16:12 UTC — Exact complete1003-line
[`LiClockPairedEtaInfinitePartitionSupercriticalWindow.lean`](../../../../formal/GaloisForLFunctions/RHTower/LiClockPairedEtaInfinitePartitionSupercriticalWindow.lean),
SHA256 `3076b0939b63c00db7f5354666adec96811a7ed4cfe1b00739e23e4e729bfb2d`,
is byte-identical to the fully root/independent-audited freeze. All65 declarations
covered:18 public (2 definitions,16 theorems) and47 private. Both exact P_N-refined
real/complex bounds, own normalizers, original polynomial intermediate and full
complex-norm limits remain proved explicitly.

Named22966, exact direct53355 and all18 public axioms33525 exited0. Direct log
empty; named build has no own-leaf diagnostics. Every unique source-order axiom
report is exactly `[propext, Classical.choice, Quot.sound]`. Final certificate
`/tmp/li_current_supercritical_final_certificate.md`,69 lines/SHA256
`36b637aca6d3e31126f462b15eb620ca10baa0a9788b30e68cdc768bc435c627`,
and all18 reports read by root. Complete literal API ledger208 and coverage97
remain linked in that certificate. No theorem or public definition was sampled.

Root added the unique area-umbrella import; generated API contains all18 rows.
Index34761 exited0. Authoritative lint63341 exited1 with17 unrelated unreachable
modules and172 large-file warnings; every diagnostic classified, no owned-leaf
finding or forbidden declaration. Logs: `/tmp/hgt-li-supercritical-final-index.log`
and `/tmp/hgt-li-supercritical-final-lint.log`. Whole-tree lint is not green.
All mathematical/formal targets on this card are certified; publication novelty
and the original completed-clock/RH problem remain open.

## Prior research

Direct documented search launched 2026-09-30 13:21 UTC:
`scripts/formal_tools.py research 'Borel finite support supercritical quarter saddle window' --json`
Output `/tmp/hgt-li-supercritical-window-research.json`; complete returned-hit/source/coverage audits are recorded below. No absence/novelty claim.

## Gates

- [x] Complete prior-research/source applicability audit.
- [x] Dependency-closed paper proof of every exact proposed target.
- [x] Independent complete proof/assumption audit.
- [x] Exact source-preserving formal plan and complete target audit.
- [x] Complete Lean scratch implementation; full root and independent proof/API audits.
- [x] Named/direct/all-public foundational gates and integration; global lint caveat above.
- [ ] Publication novelty audit.

2026-09-30 14:39 UTC — All three support packets certified and released for exact
private/name-only reuse: exponent24/SHA256
`fe604213a92840a3817d2461a19b429268fd80cec6100f9c39df23a34cb7997a`,
complete-series31/SHA256
`762ea77289b74da9e157e07c1ed2e68b409b951cabb7f4cfc2171ccb9448dd07`,
and scalar89/SHA256
`86c9889431ecd2a8c71653933f79c86b5dc4427fa1c9c34cf1e5c7b4f3eeaeaf`.
Every statement/body received root and independent review; probes/full proofs
exit0 with empty diagnostics, all1/1/4 axiom reports foundational only. Original
scalar axiom16975 exit0 recovered by owner; no replacement compiler was run.
All private numerator and Jplus/Jminus refinements remain present.

Current's early complete source core, `/tmp/li_current_supercritical_core_frozen.lean`,
249 lines/SHA256 `408903eedb5cbfc6fb1832f335a9f4585ca3b286e17321f58cb43871afe9d75b`,
compiled3943 exit0/empty. Root reviewed every new body/header and mechanically
matched both reused helper blocks in full; certificate
`/tmp/hgt-li-supercritical-core-root-audit.md`. Genuine finite exp/cosh
integrability, exact real finite MGF, integrated single-order comparison,
full Borel/cosh and both complex radial bounds, plus five public rate/envelope
interfaces, are covered. Pole independent ALL249 core audit PASS,
`/tmp/li_pole_supercritical_core_independent_audit.md`,73 lines/SHA256
`78013f388b99463a4ce26c3a5d01df3dc6059d88263b51f3c78b6cc1f00f16fd`;
root read every certificate line.

2026-09-30 14:53 UTC — MGF-stage freeze `/tmp/li_current_supercritical_mgf_frozen.lean`,
457 lines/SHA256 `94e1819c22f06dc57012457a4891f908a124c34e7a8a5fabc042016b6eef3783`,
compiled16308 exit0/empty. Root and Pole complete-source audits PASS: exact
247-line inherited core,86-line scalar mapping, and all eight new proof bodies.
Certificates `/tmp/hgt-li-supercritical-mgf-root-audit.md` and
`/tmp/li_pole_supercritical_mgf_independent_audit.md`, latter96 lines/SHA256
`cc0c4d4229f361c1801961f721a6245ce6593ad3040cb7a69eda1c2cbcf34276`, fully read.
Exact P_N expectation, constant and polynomial real bounds preserve both own
normalizers; actual comparison cancels only ZU². Remaining13 public targets,
explicit P_N-refined real/exterior inequalities for both sources, and private
complex-norm limits remain obligations. Owner acknowledged every refinement.
No source-tree promotion or full-module completion claim.

2026-09-30 15:16 UTC — Complete source freeze now compiles cleanly:
`/tmp/li_current_supercritical_complete_frozen.lean`,1003 lines/SHA256
`3076b0939b63c00db7f5354666adec96811a7ed4cfe1b00739e23e4e729bfb2d`.
Compiler21845 exited0/empty. Final specialized Mathlib name probe49800
exited0/empty. Root complete proof/API PASS: first455 lines byte-identical
to fully audited MGF packet, all new456–1003 read, all18 complete literal
public ledger blocks matched uniquely in source order including definitions
and type-level lets.47 private declarations retained. Explicit P_N-refined
both-source real/exterior bounds and paired complex-norm error limits are
present. Certificate `/tmp/hgt-li-supercritical-complete-root-audit.md`.
Independent full-source review, identical promotion, named/direct/all18
axiom gates and root integration remain pending. Card stays Stage2.

Actual residual Re(C-K_N+H_N)>=0 and RH remain OPEN.

2026-09-30 15:42 UTC — Independent complete source/API audit PASS:
`/tmp/li_pole_supercritical_complete_independent_audit.md`,85 lines/SHA256
`e6f70f629466595de9fb41fccaeea64c5087183d92531ffcb7e6d2e3d77a7d89`.
Root read ALL certificate lines and spot-checked the complete refined complex
bounds680–739. All1003 source lines,18 literal public blocks,47 private proofs
and65 total declarations covered. Identical-source promotion now released to
Current, followed by named build, direct source check and all18 public axiom
reports. Card remains Stage2 until those gates and root integration finish.

2026-09-30 14:11 UTC — Implementation released to Current for the sole new `LiClockPairedEtaInfinitePartitionSupercriticalWindow.lean`, first in complete runnable scratch. Root read all final independent formal-plan certificate90 lines, `/tmp/hgt-li-supercritical-formal-plan-audit.md`, SHA256 `2f876fc9e78e69299f58cd204fcfb949227ebc383a564bf6bcf8467902f72f0b`. All18 public targets, private exact numerator/refined bounds and polynomial intermediate remain required; the certificate explicitly pins both private complex-norm error limits so every S3 paper claim is formalized. Final named command is `lake --old build ...`. Root additionally owns disjoint scalar P4 series-comparison scratch `/tmp/hgt-li-supercritical-series-*`, with exact contract requested by Current and complete29-line micro-plan independently PASS by producer. Source probability/integrability/MGF/per-order integral and all final module integration remain Current-owned. No existing FINAL source edits, tree promotion, or completed-source claim.

2026-09-30 13:24 UTC — Root exhausted both direct search reports: first query terminal35920 exit0/27.557s, all20 candidate statements/all20 source arguments and available methods/all10 prose records; no declarations/exploration/proofideas/ingredientsets/sourcepassages. Mostly unrelated hits; existing quarter-window paper recovered. Rephrased documented query `partition Borel finite density exponential`, terminal47409 exit0/15.939s, `/tmp/hgt-li-supercritical-source-research.json`: all20 candidate statements/all20 argument proof excerpts and methods/all10 prose/one Mathlib-import source passage read; no declarations/exploration/proofideas/ingredientsets. Relevant hits are existing FINAL Borel raw domination, raw moment and raw-kernel representation ingredients; no new supercritical theorem supplied. Full source applicability belongs to paper audit, not inferred from indexed truncated headers.

Both searches partial=false/errors=[]/unfinished=[]; inventories63326/63326 then63327/63327 complete,pendingfiles0. First coverage/index1156577 versus current1156578; second coverage/current1156614 versus index1156613. Second compiler43compiled,2error,10191notapplicable,47738pending,2660stale,38stalesnapshot,1umbrellasourceonly,2654unavailable. Semantic coverage unmeasured and background refresh incomplete. Several display batches truncated; every omitted prose/passage was subsequently read in bounded batches. No corpus-absence or publication-novelty claim.

Current assigned sole `/tmp/li_current_supercritical_window_paper.md`, paper-only alltargets/source-audit; no Lean released. Proposed positive bound must retain exact full source and both squared normalizers; critical endpoint and supercritical ratio remain outside this card.

2026-09-30 13:27 UTC — Paper audit exposed a potentially stronger constant bound via the literal reference MGF and complete even-series comparison. For a=sqrt(c)>1/2, candidate full exterior bound is `[1/(s²*(a²-1/4))]*exp(-2*(a-1/2)^2*L_N)`, replacing the polynomial-size majorant. Finite Borel<=exp(t/a)*finite MGF(a); the exact two half-tilt factors supply MGF(a)<=exp((a-1/2)L_N)/(Z²*(a²-1/4)), and 1/a-2<0 handles every t>=cL_N. Public actual/reference moment ceiling may preserve both own normalizers while avoiding inaccessible private factorial machinery. Root/current/producer audit all premises and complex/full-series transfer before making any theorem claim or Lean release.

2026-09-30 13:37 UTC — Producer complete read-only public-API audit PASS, `/tmp/hgt-li-supercritical-api-audit.md`182lines; root READ ALL and mechanically matched all20 full public headers/definitions against current source. Existing public actual ceiling, compact normalized reference probability/support, finite all-parameter MGF, both complete Borel summability/radial norm routes and both normalizer floors suffice; no existing FINAL source changes or new public wrapper required. Root independent algebra/source-domain check PASS: a=sqrt(c)>1/2 uses FINITE compact-support MGF only, never infinite-source MGF outside its strip. Exact paper author snapshot and Pole complete independent final audit remain pending; no Lean released.

2026-09-30 13:45 UTC — Pole complete independent mathematical/source audit PASS, `/tmp/li_pole_supercritical_independent_audit.md` (143 lines/SHA256 `c1d7757787d0b6456f48b669246d87943e87da722e809b21031aaa2256a9e767`); root READ ALL. Exact finite compact MGF outside infinite strip, full cosh coefficient/Borel sums, own ZA²/ZU², complete complex exterior, signed/absolute real-ray limits and larger-disk obstruction checked. Independent prior deep/lexical searches fully inspected with reported coverage/freshness; no absence/novelty claim. This verdict covers the proposed theorem and source route; final author-packet certification still requires its frozen text. No Lean released.

2026-09-30 13:49 UTC — Complete author paper frozen244 lines/SHA256 `6a13233f1e2b3579588ea0bbf843116743f6981a91491ff4d8cc2057bd376247`, `/tmp/li_current_supercritical_window_paper.md`; root READ ALL/PASS and hash verified. All S1–S4 plus original Section6 polynomial bound retained; complete exterior epsilon/qualified-sequence quantifiers, both own normalizers, finite/signed/absolute real-ray limits, shared interior witnesses and both open/closed disk no-vanishing statements checked. Pole final frozen-author audit pending. Current assigned read-only complete formal plan in `/tmp/li_current_supercritical_formal_plan.md`; no Lean implementation released.

2026-09-30 13:54 UTC — Final independent frozen-author audit PASS: author244 fully read by root/Pole, all primary and optional cross-check proofs covered. Certificate `/tmp/li_pole_supercritical_independent_audit.md`162lines/SHA256 `c1c087690fde71b8e68639f3f64dcf3b4d9be331c3b44cafb60b214c3316a8e0`; root READ ALL19-line final append and mechanically verified the earlier143 lines remain exact. Paper card promoted Stage2; complete formal plan pending, no Lean implementation released.

## Complete frozen paper proof

Author snapshot244 lines, SHA256 `6a13233f1e2b3579588ea0bbf843116743f6981a91491ff4d8cc2057bd376247`. Original pending-status wording and Stage1 path are preserved as frozen history; the completed root/independent audits above govern current status.

<!-- BEGIN FROZEN SUPERCRITICAL PAPER -->
# Strict supercritical finite-partition Borel windows

**Author verdict: PASS on paper, pending independent complete audit.** This note proves every proposed target on the Stage1 card `docs/drafts/pipeline/1-in-progress/li-clock-infinite-partition-supercritical-window.md`, plus the stronger polynomial-free full complex exterior estimate. It does not formalize a new Lean theorem. No compiler, numerical experiment, source-tree edit, or source replacement was used.

## 1. Literal source and hypotheses

Throughout, N is a natural number with N>=1, L=L_N=log(2N)>0, and s=2-sqrt(2)>0. The actual finite logarithmic support is the COMPLETE union

    E_N = union_{0<=n<N} (log(2n+1), log(2n+2)].

Its raw measure is nu_A,N=volume restricted to E_N, and the reference is nu_U,L=volume restricted to (0,L]. They are different measures for N>=2. Their literal half-tilt masses are

    Z_A,N = integral exp(-u/2) dnu_A,N(u),
    Z_U,L = integral exp(-u/2) dnu_U,L(u) = 2(1-exp(-L/2)).

Both Z_A,N and Z_U,L are at least s, by the exact first interval (0,log2] and actual-to-reference measure domination. In particular both are positive; s>0 follows from sqrt2<2.

For X=A,U, mu_X is the probability on the full INDEPENDENT product with density exp(-(u+v)/2)/Z_X^2 with respect to nu_X.prod nu_X. Put D(u,v)=u-v and

    d_X,j = integral D^(2j) dmu_X,
    B_X^C(z) = sum_{j>=0} d_X,j*z^(2j)/((2j)!)^2,
    B_X(t) = sum_{j>=0} d_X,j*t^(2j)/((2j)!)^2,  t real.

These are the existing literal finite Borel kernels. Both factorials are retained. Every d_X,j is positive, d_X,0=1, and the complete complex series is absolutely convergent at every z. Its restriction to a real clock is the real kernel, embedded in C. No finite Taylor truncation or altered source is introduced.

The complete infinite actual kernel is A_infinity(t), with actual infinite mass Z and comparison constant lambda=2log2/Z^2. The complete half-line reference kernel is U_infinity(t)=cosh(2t). Certified source results give 0<lambda<1 and

    exp(-2t) A_infinity(t) -> lambda/2,
    exp(-2t) U_infinity(t) -> 1/2,  as t->+infinity.

The actual limit is the existing full-source Borel theorem. The reference limit follows exactly from exp(-2t)cosh(2t)=(1+exp(-4t))/2. Neither limit is an infinite-source MGF evaluation.

Fix c>1/4. Write theta=sqrt(c)>1/2, a=theta-1/2>0, and beta=2a^2>0. Thus theta^2=c and a(a+1)=c-1/4. There is NO upper restriction on c. No assertion is made at c=1/4.

## 2. Exact statements

S1. For every N>=1 and z in C with tau=|z|>=cL_N, separately for X=A,U,

    exp(-2tau)|B_X,N^C(z)|
      <= exp(-beta L_N) / [Z_X,N^2(c-1/4)]
      <= exp(-beta L_N) / [s^2(c-1/4)].                 (1)

The own-normalizer bound is primary: Z_U,N means Z_U,L_N, and actual Z_A,N is NEVER replaced by Z_U,N. At fixed c, its constant envelope is asymptotically smaller than the proposed 2L_N/s^2 polynomial envelope; it need not be smaller at every small N. Both estimates are proved below. A finite numerator refinement P_N=(1-exp(-aL_N))(1-exp(-(a+1)L_N)) in (0,1) can multiply the first right side; bound (1) suffices for the main stated targets.

S2. Uniformly over the ENTIRE strict supercritical complex exterior, the left side of (1) tends to zero: for every epsilon>0, eventually N, every z with |z|>=cL_N satisfies exp(-2|z|)|B_X,N^C(z)|<epsilon. Consequently any qualified sequence N_k->infinity and |z_k|>=cL_Nk eventually has scaled finite norm tending to zero, without an upper bound on |z_k|.

S3. At the positive real boundary clock t_N=cL_N,

    exp(-2t_N) A_N(t_N) -> 0,
    exp(-2t_N) U_N(t_N) -> 0,
    exp(-2t_N)[A_N(t_N)-A_infinity(t_N)] -> -lambda/2,
    exp(-2t_N)[U_N(t_N)-U_infinity(t_N)] -> -1/2.       (2)

Hence the corresponding absolute errors, and complex norms at the real clocks, tend to lambda/2 and 1/2. Both constants are strictly positive.

S4. For every fixed C>1/4, choose d=(C+1/4)/2, so 1/4<d<C. Eventually N, the SAME real complex witness z_N=dL_N lies strictly inside |z|<CL_N and satisfies

    exp(-2|z_N|)|B_A,N^C(z_N)-B_A,infinity^C(z_N)| >= lambda/4,
    exp(-2|z_N|)|B_U,N^C(z_N)-B_U,infinity^C(z_N)| >= 1/4.  (3)

For either X, there is consequently no real sequence e_N->0 which eventually bounds its scaled error at ALL |z|<=CL_N. The same impossibility holds on the open disk |z|<CL_N, since these witnesses are interior. Exact quantifier form is

    NOT exists e:Nat->Real,
      e_N->0 AND eventually N, forall z in C,
      |z|<=CL_N => exp(-2|z|)|B_X,N^C(z)-B_X,infinity^C(z)|<=e_N.

No sign or nonnegativity premise for e_N is needed. These are source-truncation approximation obstructions, not a claim about inverse clocks or completed-response signs.

## 3. Finite probability integrability and exact MGF

Use the reference normalized product law mu_U,L ONLY. Its public probability theorem applies because L>0, and its public support theorem gives |D|<=L almost everywhere. D is measurable as a continuous coordinate difference. Thus, for EVERY real v, exp(vD) is measurable and a.e bounded by exp(|v|L), so is genuinely integrable against this probability measure. The same holds for cosh(theta D). Every power D^(2j) is independently integrable. These facts license all finite integral comparisons and the averaging below; none is an identity of totalized divergent integrals.

Define M_L(theta)=integral cosh(theta D) dmu_U,L. The exact public finite complexMGF source formula, restricted at plus/minus real theta, gives equal real exponential expectations because its two filled Laplace factors swap:

    integral exp(theta D) dmu_U,L
      = integral exp(-theta D) dmu_U,L
      = U_L(1/2-theta) U_L(1/2+theta) / Z_U,L^2,

where U_L(q)=integral_0^L exp(-qu)du is the literal FILLED contiguous partition. Averaging the two genuinely integrable exponentials gives the same value for M_L(theta); the cosh factor 1/2 cancels their equal values. Both independent product factors remain.

At theta>1/2, the two parameters 1/2-theta and 1/2+theta are nonzero. The filled finite partition formula therefore yields

    M_L(theta)
      = [(exp((theta-1/2)L)-1)(1-exp(-(theta+1/2)L))]
          / [(theta^2-1/4)Z_U,L^2]
      = exp(aL)(1-exp(-aL))(1-exp(-(a+1)L))
          / [a(a+1)Z_U,L^2]
      <= exp(aL) / [(c-1/4)Z_U,L^2].                 (4)

All factors in the numerator are positive for L>0. No principal logarithm, central nonzero germ, or eta denominator is involved. In particular 1/2-theta<0 is legitimate for the FINITE compactly supported partition, whose transform is entire. The infinite-source MGF only has a strip of genuine integrability; theta>1/2 is outside that strip. It is NOT used or continued as a supplied premise here.

## 4. Complete coefficient comparison, retaining both factorials

For each j>=0 and every real y, the complete cosh series has nonnegative terms, hence

    y^(2j)/(2j)! <= cosh(y).

Apply this pointwise with y=theta D. Integrability of both sides was established in Section3. Linearity of the integral and the literal moment definition give

    d_U,j theta^(2j)/(2j)! <= M_L(theta).             (5)

This is a SINGLE-TERM comparison at each order, not an exchange of an infinite series with an integral. For every tau>=0 multiply (5) by the nonnegative number (tau/theta)^(2j)/(2j)!, obtaining

    d_U,j tau^(2j)/((2j)!)^2
      <= M_L(theta)(tau/theta)^(2j)/(2j)!.

The left full series is already summable by the certified contiguous Borel theorem. The right full series is summable by the complete real cosh expansion. Comparing their sums, all j retained, gives

    U_L(tau) <= M_L(theta) cosh(tau/theta)
             <= M_L(theta) exp(tau/theta).            (6)

The final inequality holds because tau/theta>=0 and cosh(x)=(exp(x)+exp(-x))/2<=exp(x). Source positivity is used only in inequalities; no complex phase is discarded in an asserted identity.

For the actual finite source the public complete endpoint ceiling gives, for N>=1 and tau>=0,

    A_N(tau) <= (Z_U,L_N/Z_A,N)^2 U_L_N(tau).          (7)

That theorem was proved from the literal FULL union and product domination before normalization, over all coefficients. It is not an equality of the two measures. Combining (4), (6), and (7) cancels only Z_U,L_N^2 in the numerator/denominator and leaves

    B_X,N(tau) <= exp(aL_N+tau/theta)
                    / [(c-1/4)Z_X,N^2], X=A,U.       (8)

This step is where losing the actual normalizer would change the source. The exact squared actual mass in (8) remains independently present.

## 5. Complex radial bound and exterior algebra

All coefficients d_X,j/((2j)!)^2 are nonnegative, and the complete complex series is norm-summable. Triangle inequality for its complete sum gives, for every z,

    |B_X,N^C(z)|
      <= sum_j [d_X,j/((2j)!)^2] |z|^(2j)
       = B_X,N(|z|).                                (9)

There is no conditional rearrangement: exact term norms equal the displayed nonnegative radial terms. Apply (8) with tau=|z|. For tau>=cL_N, the coefficient 1/theta-2 is strictly negative. Therefore

    -2tau+aL_N+tau/theta
      <= aL_N+(1/theta-2)cL_N
       = [-2theta^2+2theta-1/2]L_N
       = -2(theta-1/2)^2 L_N = -beta L_N.

This algebra proves (1), then both Z_X,N>=s prove its uniform source-independent envelope. It requires no saddle-point approximation or differentiation. Since L_N->+infinity and beta>0, the right side tends to zero. This proves S2 with its complete exterior quantifiers, and the first two limits in S3 by the real-clock bridge and finite-kernel nonnegativity.

## 6. Original polynomial envelope and literal raw-density cross-check

The original polynomial estimate also follows through the SAME public finite-MGF proof, without any new integral/series interchange. The exact two raw factors in (4) satisfy

    J_plus=(exp(aL)-1)/a <= L exp(aL),
    J_minus=(1-exp(-(a+1)L))/(a+1) <= 1/(a+1) <= 1.

For the first inequality, use 1-exp(-aL)<=aL, itself following from exp(x)>=1+x. Consequently M_L(theta)<=L exp(aL)/[(a+1)Z_U,L^2]. Repeating (6)–(9) and the identical exterior algebra gives

    exp(-2tau)|B_X,N^C(z)| <= L_N exp(-beta L_N)/[(a+1)Z_X,N^2]
                           <= 2L_N exp(-beta L_N)/s^2.

Thus the original quantitative target can be formalized with the existing public route. The following cross-check is an independent source-density explanation, not an additional required formal API or theorem target.

This independent cross-check verifies the originally proposed raw-source mechanism, although Section3–5 is the shorter PUBLIC-API formalization path. Let g_A,N and g_U,L be the canonical raw product-difference densities. Existing complete-density theorems give their evenness/nonnegativity, g_A,N<=g_U,L_N pointwise, and zero when |x|>=L_N. For 0<=r<L,

    g_U,L(r)=exp(-r/2)(1-exp(r-L));

the same formula holds at r=L because both sides vanish. Both normalized density formulas divide by their own Z_X^2. Their complete raw even-moment identities are integral x^(2j)g_X(x)dx=Z_X^2 d_X,j.

Let F(w)=sum_j w^(2j)/((2j)!)^2. Its complete norm sum is bounded by exp(2sqrt(|w|)): it is an even subseries of sum_k |w|^k/(k!)^2, itself the nonnegative diagonal subseries of [sum_k sqrt(|w|)^k/k!]^2. All sums are absolutely convergent. On compact source support this gives an integrable common majorant for the complete raw integral/series exchange. Thus the literal kernel integral, with own Z_X^2, gives

    exp(-2tau)|B_X,N^C(z)|
      <= (2/Z_X^2) integral_0^L exp(f_tau(r))(1-exp(r-L))dr,
    f_tau(r)=-r/2+2sqrt(tau*r)-2tau.

The factor2 comes from two halves of the even raw density. For tau>=cL and 0<=r<=L,

    f_tau(L)-f_tau(r)
      = -(L-r)/2+2sqrt(tau)(sqrt(L)-sqrt(r))
      >= (sqrt(tau/L)-1/2)(L-r) >= a(L-r).

Here sqrt(L)-sqrt(r)=(L-r)/(sqrt(L)+sqrt(r))>=(L-r)/(2sqrt(L)), using L>0. Also f_tau(L)<=f_cL(L)=-beta L: equivalently f_tau(L)=-(sqrt(L)-2sqrt(tau))^2/2 and 2sqrt(tau)-sqrt(L)>=2sqrt(cL)-sqrt(L)>0. Hence the crude original bound is 2L exp(-beta L)/Z_X^2, then 2L exp(-beta L)/s^2.

Retaining the exact endpoint density improves it to

    (2/Z_X^2)exp(-beta L) integral_0^L exp(-ay)(1-exp(-y))dy
    <= 2 exp(-beta L)/[Z_X^2 a(a+1)].

The exact finite integral equals (1-exp(-aL))/a-(1-exp(-(a+1)L))/(a+1), and comparison with its nonnegative integral on [0,infinity) gives upper bound 1/a-1/(a+1)=1/[a(a+1)]. This independent factor2 bound is weaker than (1); the factor1 Chernoff estimate correctly averages the two equal finite MGFs rather than discarding a coordinate or half-line.

The existing Borel finite raw-kernel representation is PRIVATE. This cross-check is a paper proof licensed by the complete compact interchange and public raw-moment identities; it is not a claim that those private symbols are callable from a new leaf. The selected Sections3–5 proof avoids that API obstacle and reproducing the raw/Gamma infrastructure.

## 7. Error constants and exact disk obstruction

Since c>1/4>0 and L_N->infinity, t_N=cL_N->infinity. Compose the certified infinite-source real asymptotics with t_N, and subtract the two finite limits proved above. This proves the two signed error limits in (2). Absolute value is continuous, and the exponential weight is positive, so the absolute-error limits are lambda/2 and1/2. The four ofReal identities for finite actual/reference and infinite actual/reference turn these into exactly the complex norm errors at real t_N.

As lambda>0, convergence gives eventually actual scaled error>=lambda/4; reference convergence similarly gives eventually error>=1/4. Intersect these two eventual sets to use the SAME boundary clock. For a prescribed larger disk coefficient C>1/4, apply this reasoning at d=(C+1/4)/2. N>=1 supplies L_N>0, so |dL_N|=dL_N<CL_N. This proves the simultaneous interior witnesses (3).

If the actual disk had eventual uniform upper bounds e_N->0, then eventually e_N<lambda/4. Intersect with its uniform-bound eventual set and the witness eventual set; the actual inequality would give lambda/4<=e_N<lambda/4. This contradiction proves S4. Use 1/4 for reference. The same witness belongs to both open and closed disks. Thus every disk strictly larger than the quarter scale fails vanishing weighted approximation. No supremum existence, choice of finite frequency subset, or unproved uniform convergence of the infinite complex source is needed.

## 8. Exact source applicability and formal dependency ledger

Paths below are relative to `formal/GaloisForLFunctions/RHTower/`. Every declaration used in the primary proof was read in current source; existing full-proof certification is not inferred from cached search/compiler status. `/tmp/hgt-li-supercritical-api-audit.md` contains ALL20 full public blocks and the independent public-API applicability audit, also mechanically matched by root.

| Requirement | Verified source and exact symbol |
|---|---|
| Actual nu/Z/product/d_j, both factorials | `LiClockPairedEtaFinitePartitionVolterra.lean:35,39,44,767`: `liClockPairedEtaPartitionNormalizer`, `liClockPairedEtaSymmetrizedMeasure`, `liClockPairedEtaSymmetrizedEvenMoment`, `liClockPairedEtaPartitionBorelCoefficient` |
| Actual d_j>0 and complete real sum | same file:936 `liClockPairedEtaSymmetrizedEvenMoment_pos`;1083 `liClockPairedEtaPartitionBorelKernel_eq_tsum`;1092 `summable_liClockPairedEtaPartitionBorelTerm` |
| Literal reference definitions | `LiClockPairedEtaContiguousMeasure.lean:25–56`: `liClockPairedEtaContiguousLogMeasure`, `...PartitionNormalizer`, `...SymmetrizedMeasure`, `...SymmetrizedEvenMoment`, `...BorelCoefficient`, `...BorelKernel`, `...BorelKernelComplex` |
| Reference probability/support and genuine moments | same file:131 `liClockPairedEtaContiguousSymmetrizedMeasure_isProbability`;198 `...SymmetrizedMeasure_support`;165 `integrable_liClockPairedEtaContiguousSymmetrizedEvenMoment` |
| Finite transforms at ALL real/complex parameters | same file:58/63 `integrable_rexp_neg_mul_liClockPairedEtaContiguousLogMeasure`, `integrable_cexp_neg_mul_liClockPairedEtaContiguousLogMeasure`;68 `...Partition_eq_integral_logMeasure`;258 `...SymmetrizedMeasure_complexMGF_eq_source` |
| Filled transform formula at nonzero parameters | `LiClockPairedEtaContiguousSource.lean:19` `liClockPairedEtaContiguousPartition_eq_div`; no positive-real-part premise |
| Reference all-order moment normalization | `LiClockPairedEtaContiguousMeasure.lean:178` `liClockPairedEtaContiguousSymmetrizedEvenMoment_eq_double_integral` |
| Complete actual-to-reference ceiling | `LiClockPairedEtaPartitionEndpointComparison.lean:917` `liClockPairedEtaPartitionEndpoint_borel_le_ceiling`, N>0,t>=0, exact (ZU/ZA)^2 |
| Complete complex summability and finite bridges | same file:1158 `liClockPairedEtaPartitionBorelKernelComplex`;1187 `summable_norm_liClockPairedEtaPartitionBorelTermComplex`;1209 `...BorelKernelComplex_ofReal` |
| Complete reference summability/positivity/bridge | `LiClockPairedEtaContiguousMeasure.lean:387` `liClockPairedEtaContiguousBorelCoefficient_pos`;419/424 norm/real summability;439 `...BorelKernelComplex_ofReal`;446 `...BorelKernel_eq_tsum` |
| BOTH normalizer floors | `LiClockPairedEtaInfinitePartitionMeasure.lean:667,675` `liClockPairedEtaPartitionNormalizer_ge_first`, `liClockPairedEtaContiguousPartitionNormalizer_ge_first`, N>0 |
| Actual infinite scaling | `LiClockPairedEtaInfinitePartitionBorel.lean:1656` `tendsto_liClockPairedEtaInfinitePartitionBorelKernel_scaled` |
| Exact reference cosh and infinite bridges | same file:1198/1203 infinite/half-line `...BorelKernelComplex_ofReal`;1207 `liClockPairedEtaHalfLineBorelKernel_eq_cosh` |
| Nonzero actual error constant | `LiClockPairedEtaInfinitePartitionDensityTail.lean:1480` `liClockPairedEtaInfinitePartitionComparisonLimit_pos`;1495 `...ComparisonLimit_lt_one` |
| Direct cross-check raw density/support/moments | `LiClockPairedEtaPartitionDensityRatio.lean:245–281,357–391,970–987`: exact evenness, nonnegativity, actual<=reference, reference density, cutoff zero, integrability, and own-Z^2 moment identities |

Source-read installed primary Mathlib APIs are `Real.hasSum_cosh` and `Real.cosh_eq_tsum` in `Analysis/SpecialFunctions/Trigonometric/Series.lean:142–149`, `ProbabilityTheory.complexMGF_ofReal`/`re_complexMGF_ofReal` in `Probability/Moments/ComplexMGF.lean:98–103`, and `norm_tsum_le_tsum_norm` in `Analysis/Normed/Group/InfiniteSum.lean:149`. Their applicability is paper-audited; no new toolchain probe/Lean result is claimed. A future released implementation must verify every new recalled API in its own /tmp scratch. The primary route needs only small private integrability/cosh-moment/radial adapters; no existing FINAL leaf changes or fresh public source wrapper are required.

## 9. Full target matrix and scope boundaries

| Proposed target | Paper proof |
|---|---|
| Actual strict c>1/4 weighted finite real ray ->0 | S1–S3, own ZA^2 |
| Reference strict c>1/4 weighted finite real ray ->0 | S1–S3, own ZU^2 |
| Original polynomial-size exact source envelope | Section6, every interval/gap retained |
| Stronger full complex exterior envelope | Sections3–5, exact factor1/[ZX^2(c-1/4)], then common s^2 |
| Complete sums/convergence/integrability | Sections1,3,4,5; single-term integral comparison plus already-summable full Borel/cosh comparison |
| Actual weighted absolute error ->lambda/2 | Section7, strictly positive source constant |
| Reference weighted absolute error ->1/2 | Section7, exact half-line cosh |
| Same-ray eventual lambda/4 and1/4 witnesses | Section7 |
| Every larger open/closed proportional disk cannot have vanishing weighted uniform error | S4/Section7, exact eventual forall-z quantifiers |
| No actual-source substitution or normalizer loss | Section1 full union, Section4 exact endpoint ceiling/cancellation |

No claim is made at c=1/4 or about optimal constants/rates. The finite actual/reference ratio beyond the quarter window remains undetermined: their simultaneous weighted decay gives a 0/0 problem, not a ratio limit. No complex infinite-source asymptotic on all phases is supplied. Actual completed-response compensation, relative Volterra inversion, orientation sign, and RH remain OPEN. This note supplies a positive exterior decay law and precise approximation boundary, without retiring the main candidate.

## 10. Prior-research coverage and overlap

The documented direct searches were inspected BEFORE this new paper proof. Parent read all returned candidates/arguments/prose; this audit independently read the ranked candidate/argument statements and traced every used source ingredient rather than relying on truncated indexed headers.

First report `/tmp/hgt-li-supercritical-window-research.json`: query `Borel finite support supercritical quarter saddle window`, hybrid, partial=false, 20 candidates/20 source arguments, no declarations/proofideas/ingredientsets/sourcepassages/exploration. Hits were mostly unrelated quarter/finite-window topics; no applicable supercritical theorem was supplied. Inventory63326/63326 complete,pendingfiles0; coverage/index1156577 versus current1156578. Compiler coverage mostly pending/stale/unavailable; semantic coverage unmeasured, background refresh incomplete; elapsed27.5566s.

Rephrased report `/tmp/hgt-li-supercritical-source-research.json`: query `partition Borel finite density exponential`, hybrid, partial=false, 20 candidates/20 arguments/10 prose/one source passage, no declarations/proofideas/ingredientsets/exploration. Useful arguments were existing FINAL private finite raw domination1305/raw moment1329 and raw-kernel representation ingredients; the sole installed source passage was an irrelevant Mathlib import block. Inventory63327/63327 complete,pendingfiles0; index1156613 versus coverage/current1156614. Compiler43compiled_snapshot,2error,10191not_applicable,47738pending,2660stale,38stale_snapshot,1umbrella_source_only,2654unavailable. Semantic coverage unmeasured; elapsed15.9394s. These reports certify search execution/coverage only, not Lean applicability.

Own direct lexical broadening `scripts/formal_tools.py research 'factorial kernel' --mode lexical --module LiClockPairedEta --json` terminated0 and returned the existing private Borel kernel uniform-convergence/analytic helpers103/110 (six total matches, displayed two per module). Their primary proofs were read. Lexical response did not report whole-corpus coverage/freshness. No additional supercritical theorem was found in these returned hits; no absence or worldwide novelty claim follows.

Overlap is explicit: complete Borel factorial majorants, source product domination/normalization, compact finite transforms, and subcritical finite/infinite limits are already banked. Chernoff coefficient comparison and compact-support exponential bounds are generic mathematics. The surviving source-specific result is their exact application to the unchanged literal complete partition kernels with both normalizers, the strict exterior rate beta=2(sqrt(c)-1/2)^2, and the actual lambda/2 versus reference1/2 nonvanishing approximation constants. Publication novelty is not asserted. Independent ALL-proof/source audit remains required before formal release.
<!-- END FROZEN SUPERCRITICAL PAPER -->

2026-09-30 13:56 UTC — Root isolated pure-algebra micro-plan `/tmp/hgt-li-supercritical-algebra-plan.md` independently PASS by Pole against exact paper Section5. Root alone owns `/tmp/hgt-li-supercritical-algebra-*`, retaining c>1/4,L>=0,cL<=tau and exact exponent conclusion; Mathlib name/type probe1828 running. Only this already-proved algebra scratch is released; complete source leaf remains held for full formal-plan audit. No existing FINAL source changes.

2026-09-30 14:07 UTC — Pure exponent helper FINAL_READY: `/tmp/hgt-li-supercritical-algebra-frozen.lean`, 24 lines/SHA256 `fe604213a92840a3817d2461a19b429268fd80cec6100f9c39df23a34cb7997a`. Corrected type-specialized Mathlib probe97726 and full proof50791 both exit0 with empty diagnostics; sole-theorem axiom check76602 exit0 with only `propext`, `Classical.choice`, `Quot.sound`. Root and Pole read every statement/body line; independent certificate `/tmp/li_pole_supercritical_algebra_audit.md`21 lines fully read by root. Exact private/name-only reuse released. Complete source plan `/tmp/li_current_supercritical_formal_plan.md`245 lines/SHA256 `e01f900ef5f511c6301b82a5281a75c5dca169f8858b4f8244131d84838f0495` read entirely by root/producer; architecture PASS. Explicit private complex-norm limit obligations are being pinned before full implementation release; 18 public declarations and every paper target retained.
