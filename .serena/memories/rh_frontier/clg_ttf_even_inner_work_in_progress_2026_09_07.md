# IN-PROGRESS: explicit even-four energy interval (do not claim endpoint proved yet)

Active unbounded RH goal, unchanged. Previous turn explicit outer x≥6/5 was PROGRESS. Current target: corrected native even4 PD on0≤x≤8/95 for every C≥1e12; canonical weighted PD0<r≤16/95. Combine with old outer endpoint to leave explicit gap[8/95,6/5]. Rank7/all-order/RH remain OPEN. No subagents authorized/spawned.

## Mathematical design (exact; final incidence checks still pending)

Actual modular coordinates u=thetaCuspModularMassDrift, a=GapAmplitude, w=TransverseShear, M=completedThetaProfile. On x∈[0,8/95], old energy bounds give u,w∈[0,1],a∈[17,20],u≤w≤5u/4,u≥39x/4,a≥R0²-228x²,strong energy a+4u²/3<96/5. New CHECKED ThetaCuspEvenCompactState proves191/10-12u²/5≤a≤96/5-4u²/3 and exact t,v∈[0,1]: a=191/10-12u²/5+t(1/10+16u²/15),w=u(1+v/4).

Q=u²/24+a/16-3/8, Phi=M Q. New CHECKED ThetaCuspEvenCompactCorrection proves normalized source slope F1≥-15/8 using relative shear, then G=3Phi²+2xPhiPhi' ≥M² Q(3Q-6/19). This improves old energy G≥M² and makes correction even in u, essential to the determinant certificate.

Exact source p0=Q; recurrence p_(n+1)=u*p_n/6+(-3+u²/3+3a/4)∂u p_n-2aw∂a p_n+(2+a/2+2u²/9+2uw/3)∂w p_n. Old p0..10 checked in PolynomialODEOddCompactSourceJets/Scalars. New arbitrary-center p11,p12 and reflected12 all CHECKED from covariant Lie recurrence and all13Leibniz terms. Source term counts119,148; reflected12 count210. Signs m_k=(-1)^k j_(2k)/M².

Fixed balancing m_k/100^k. Substitute R=u² and the coupled a,w formulas. Seven exact unit moment polynomials have9,31,72,133,218,331,476 terms. Unit correction=Q_unit(3Q_unit-6/19); coefficient1e12/100^6=1, so unit determinant is H4(m0unit,...,m6unit+Gunit). Actual det normalization divisor100^12 M8=1e24 M8, including actual head cofactor. Desired unit determinant≥1/1000 gives actual corrected cofactor reserve≥1e21 M8.

Pure rational guidance generated exact normalized determinant polynomial T(R,t,v),5368terms degrees(20,20,21). Positivity design: replace each adverse monomial exponent by min(exponent,4), drop favorable monomials having any exponent>4; retain all exact nonnegative slacks via old oddCompactUnitSlack=max0(1-R^i t^j v^k). Result L has95terms, degree≤4 in EACH variable (not total degree4). All125 Bernstein coefficients exceed1/1000; exact positive Bernstein identity is CHECKED in PolynomialODEEvenCompactQuartic. The full determinant-to-certificate identity is NOT checked yet, so guidance supplies no source sign premise.

## Workspace / checked state

All owned scratch uses /tmp/clg_even_inner*. Stage root /tmp/clg_even_inner_stage/GaloisForLFunctions. See /tmp/clg_even_inner_checkpoint.json for copied/wired list (may lag one latest check). 14 modules checked, copied byte-for-byte, wired into umbrellas:
HT: PolynomialODEEvenCompactSourceEleven,SourceTwelve,SourceScalars,ReflectedTwelve,Quartic,UnitCoordinates,MomentZero,MomentOne,MomentTwo,MomentThree,MomentFour,MomentFive (full names all PolynomialODEEvenCompact*).
RHT: ThetaCuspEvenCompactState,ThetaCuspEvenCompactCorrection.
Only needed oleans emitted. NO full/umbrella/cascade builds. NO axiom audit or lint yet this turn. Audit NEW capstones once at final closure; never old results. Previous turn global lint failure was unrelated MobiusDivisorTwoChannelPrimeBlocks missing umbrella import, might have been fixed by concurrent EDQ task. Do not touch EDQ files/processes.

## CURRENT LIVE HANDLE (revalidate!)

Original fractional Block0 check session58265 ran >10min/4-5GB, was deliberately stopped with SIGINT to owned PID27767 to improve proof arithmetic, returned exit130. This was NOT a missing-handle restart. Prepared equivalent integer/common-denominator certificates. New Block0 session98966, PID28897,parent28866, observed live2:18 CPU98%; poll THIS session. Do not start another Lean process while it runs. Other unrelated EDQ Lean processes may be active; leave them alone.

All12 staged Block0..11 now use ONE common denominator: raw integer polynomial /d, reduced integer polynomial /d, nonnegative integer remainder /d. Proof unfolds, rw[←add_div],congr1,simp only[oddCompactUnitSlack_eq cube bounds],ring; nonneg proof unfolds remainder AND oddCompactUnitSlack then positivity. This should avoid repeated rational normalization. Block0 not yet checked/copied. Alternative exact data same T and L.

## Staged / pending Lean files

- HT PolynomialODEEvenCompactMomentSix: NOT checked. Modified to split substitution into private relativeMomentSix(u²,a,v) with210terms, then gap substitution in abstract R before specializing R=u². Main public signature unchanged. Avoid rerunning old unit generator: it would overwrite this optimization and the corrected unused _v binder in MomentZero.
- HT PolynomialODEEvenCompactModel: seven signed moment function Fin7, seven unit moments, exact unit identity via fin_cases, evenCompactUnitDet.
- HT PolynomialODEEvenCompactBlock0..11:448terms each exceptlast. Common integer denominators, same public raw/Lower/Remainder/eq/remainder_nonneg interfaces.
- HT PolynomialODEEvenCompactUnitReserve: sum blocks, equality of sum Lower to checked Quartic, combine exact nonnegative remainder to UnitPolynomial≥1/1000. Unchecked.
- HT PolynomialODEEvenCompactDeterminant: imports Model+UnitReserve. Big exact identity UnitDet=UnitPolynomial by norm_num model Fin cases, unfold H4/7moment definitions/correction/gap/all12rawBlocks,ring. maxHeartbeats40M. Might require splitting/cofactor normalization for efficiency. Then UnitDet_lower.
- RHT ThetaCuspEvenCompactSourceCoordinates: actual modular state→real scalar moments through12; exact balanced unit moments; actual determinant ratio (detE0+1e12 M² Gunit detA)/(100^12M8). Unchecked. Generic helper takes Complex.re of old all-order reflection incidence. Zero case uses full-source identity; others use checked reflected scalar2..12.
- RHT ThetaCuspEvenFourExplicitCompact: prepared final actual coefficient-family compact reserve, PD interval, canonical native/weighted outside explicit gap. Unchecked; no sign claim yet.

Next: poll Block0 (98966). Once terminal handle checked, finish remaining staged files sequentially with lake env lean --root=/tmp/clg_even_inner_stage -o .lake/build/lib/lean/GaloisForLFunctions/<group>/<name>.olean /tmp/clg_even_inner_stage/GaloisForLFunctions/<group>/<name>.lean from formal/. Copy only successful final bytes, wire immediately. MomentSix→Model→SourceCoordinates can be checked before remaining polynomial blocks. Block1..11→UnitReserve; Model+UnitReserve→Determinant; then SourceCoordinates+Determinant→ExplicitCompact. Fix actual errors only. Be efficient; if large ring proof fails/too costly, split exact algebra, do not full rebuild.

## Scripts / data / hazards

/tmp/clg_even_inner_explore.py: pure Fraction sparse polynomial recurrence, first numerical guidance. Broad independent box positivity FAILED at toy points violating source correlations; no formal no-go and no route retired. Keep actual correlations.
_det.py/_det.json: original corrected D using old .137 lower correction,3312terms. _transform.py replaces that correction with6/19, substitutes W=u(1+v/4),u²=R, then a coupled affine-R/t form, outputs /tmp/clg_even_inner_unit.json. _minorant.py gives L and125 Bernstein coefficients. All numeric evaluations guidance only, exact expressions must ring-check.
_commonblocks.py generated common-denominator blocks1..11 plus /tmp/clg_even_inner_block0_common.lean (copied over active stage0 only AFTER stopping original run). _blockgen.py is OLD fractional format; DO NOT rerun.
_sourcegen.py OLD unused simp args; DO NOT rerun over checked sources.
_scalargen.py source scalar11/12 and reflected12. _unitgen.py OLD unsplitMomentSix/unused v in MomentZero; DO NOT rerun.
_modelgen.py/_actualgen.py generate pending model/determinant/source incidence. Any generator overwrites stage files; use carefully.

## Finalization (not done)

Active card docs/drafts/pipeline/1-in-progress/clg-ttf-center-integration-compensation.md updated current inner target: coupled tube,G bound,source12,positive quartic checked; full determinant/actual endpoint pending. Frontier/STATUS NOT yet updated this turn beyond card. After full success, write dependency-closed paper clg-ttf-even-four-energy-interval.md; explain tri-quartic bound and actual complete-source incidence, update frontier to explicit remaining[8/95,6/5], STATUS route-independent exact parameter correlation/normalization evidence. Update prior cards where inner δ was existential. Run one new-capstone axiom audit, one formal lint, targeted diff/byte/import checks, save final memory, remove ALL owned /tmp/clg_even_inner* and owned processes. Preserve unrelated EDQ work and massive dirty tree. Goal ACTIVE; RH unproved even if this finite interval closes.