# HB full canonical unit-source matching: closed no-go

Current proof chain: literal theta-cusp → Xi occurrence → retained spin-two source → physical causal radial/left-QNM action → fixed Hawking-clock extinction → RH. RH remains unproved/unfalsified. The full canonical action cannot match the literal complementary unit-source receiver; this does not exclude different source-retaining receivers.

## Authoritative sources
- formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMCanonicalSourcePeriodAttachment.lean (DN31): original complete action = -mu*C*((mu-2)*(Td*M+T*X)+T*Y), for every physical q, branch, side, amplitude. Td holds source rate fixed. All original finite-part constants retained. Scratch and exact isolated module audit passed (57s, 2 jobs).
- formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMCanonicalContourAttachment.lean (DN32): at true/true, amplitude1, w=-1-rho/2, E(w)^2*(5w+8)^2*canonicalQNMValue = -mu*C*G(w). Scratch and exact isolated audit passed (149s, 2 jobs).
- formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMFullCanonicalMatchingNoGo.lean (DN33-DN35): combined angular counting, radial counting, density and final contradiction. Scratch passed; final isolated exact module audit passed (98s, 2 jobs), no warnings. All three modules wired into RHTower.lean; umbrella not built.
- Own facts: docs/drafts/pipeline/1-in-progress/hb-dn-source-resolvent-facts.md, now DN1–DN35.
- Current paper: docs/drafts/pipeline/1-in-progress/hb-dn-source-moment-reduction.md. Actual matching status rewritten as closed no-go. The alternative w=0 expansion is analytical and unused; nontriviality instead uses the Lean-verified w=-1 anchor.
- Closed option card: docs/drafts/pipeline/5-failed/hb-full-canonical-unit-source-matching.md.

## Exact proved outcome
FullCanonicalMatchingNoGo.fundamentalCanonicalCriticalZeroFinset_card_linear (namespace RHTower.D4BMJointSource): only O(N) simple critical Xi zeros up to N/3 can have zero complete true/true amplitude1 action. fundamentalCanonicalCriticalZeroFinset_relative_density_zero: for every eps>0 this bad count is eventually ≤ eps times the actual simple-critical count. This is the positive survivor: relative-density-one nonvanishing, controlling cancellation of the full temporal/metric/forcing action.
RHTower.exists_critical_canonicalQNMValue_ne_zero: an actual critical Xi copy q has canonicalQNMValue q true true 1 ≠ 0.
RHTower.not_exists_hbXiPeierls_fullCanonicalQNM_matching: no returned : XiZeroCopy → HBXiPeierlsCarrier gives unit-source profile equal to this complete canonical value for every q.
RHTower.not_exists_hbXiPeierls_fullCanonicalExtinction_matching: even equivalence of zero loci is impossible.
RHTower.not_exists_hbXiPeierls_arbitraryResponse_fullCanonicalQNM_matching: includes arbitrary nonlinear carrier responses.
These final no-go theorems have no supplied matching/nonvanishing/density/RH hypotheses.

## Proof mechanism
Actual full G is entire finite exponential type; source-derived anchor G(-1)=27*pi²*T(-2,-1)/4>0 gives O(N) radial exceptions. At critical rho, angular C=0 forces xi at one of 2-5rho/2, 1-rho/2, 3rho/2 to vanish. These injective maps have Re=.75 and fit the symmetric height N-2 rectangle for census height N/3 and N≥12. The actual residue-unit multiplicity count bounds each exception set; corpus Ingham bound at .75 gives each ≤N eventually. Union is O(N), while existing simple critical census is Ω(N log N). Unit-source probe vanishes at every critical copy regardless of returned vector.

## Verification/cleanup
Logs retained: /tmp/hb-ea-canonical-period-audit.log, /tmp/hb-eb-canonical-contour-audit.log, /tmp/hb-full-canonical-matching-final-check1.log, /tmp/hb-full-canonical-matching-audit.log. All owned Lean/Lake processes ended; private audit directories and pending EA/EB/EC/ED/EF/final scratch files removed. Intermediate EC/ED were combined into the final leaf, not installed separately, to avoid extra audits. No computations, #print axioms, full builds, umbrella builds, git or launch.sh. Frontier map untouched.
Global lint /tmp/hb-full-canonical-matching-lint.log exited1 solely for unrelated unwired RHTower.DivisorCoreMellinResidueUniformMargin, plus ordinary large-file warnings; no new-module error. No fix to other agents' files.

## Lean efficiency facts
Latest user complained about accumulated build time. The two angular scratch attempts each took about 2m40s, not a single 30-minute build; they ended. Reduced unused imports, replaced degree16 nlinarith by scalar divide-by-three bounds, and generalized 1+log N to a variable before ring normalization. Combined final scratch passed in about2m20s; final audit98s. No heartbeat/transparency hacks.
Numeric complex lemmas are Complex.re_ofNat/im_ofNat (not ofNat_re/im). Fin-vector cases: use change to expose actual affine equality, not dsimp only with Matrix.cons_val_* on Fin constructors. Rectangle endpoint needs whole-real-expression cast (((N:ℝ)-2:ℝ):ℂ). Include Set.mem_Icc when simp comparing membership with conjunction of inequalities.
