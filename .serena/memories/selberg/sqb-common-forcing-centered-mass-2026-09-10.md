# SQB56: common-forcing centered native mass closed

RH, SQB occurrence and arithmetic source cancellation remain UNPROVED. Goal remains active. This turn produced a new closed positive theorem, not an RH proof or a cancellation estimate.

New module formal/GaloisForLFunctions/RHTower/SelbergThetaCommonForcingMass.lean (201 lines), wired into formal/GaloisForLFunctions/RHTower.lean. Imports CommonForcingGram only. Eight public theorems:
- positiveSource_cusp_bound: exists C>0, for every z with im z>=1/2, actual full positiveSource z <= C/im z.
- positiveSource_not_ae_constant: positiveSource is not equal almost everywhere in the original angularMeasure to ANY complex constant.
- centered_nativePositive_ne_zero.
- forcing_ne_zero for CommonForcingGram.forcing.
- vector_ne_zero for every actual XiZeroCopy q.
- vector_norm_pos.
- unitDomain_norm: actual scalar normalization in energyOperator.domain has native norm 1.
- unitDomain_equation: (A-energy(q)) unitDomain(q) = norm(vector(q))^-1 times the complete fixed centered forcing.

Positive proof mechanism:
Use existing positiveProfile_power_bound at -1 and 3. For a nonidentity primitive row, cuspRow_nonparabolic_height_le gives h<=1/y. Thus P(h)<=B*h^3<=(B/y)*h^2. Sum every nonidentity row, using SelbergResummedSource.nonparabolic_quadratic_bound D. The identity row contributes <=A/y, so full source <=(A+B*D)/y.
Every cusp region {z: 2<im z, Y<im z, |re z|<1/2} is nonempty open, inside fd, and has positive hyperbolic volume. AE-constant source must have positive real constant (source is everywhere positive), but the cusp bound on arbitrarily high positive-measure regions contradicts it.
If centered common-forcing vector vanished, the linear native graph equation would force centered nativePositive=0. Contradiction. Normalize in that same domain.
DO NOT redo this mass gate. It concerns the common-forcing vector, distinct from the previously normalized first-order vector in SelbergThetaNativePairing.

Verification all terminal collected:
- lake env lean /tmp/sqb56_mass.lean: core scratch passes after fixing algebra and names.
- lake env lean GaloisForLFunctions/RHTower/SelbergThetaCommonForcingMass.lean: passes, includes normalization.
- preflight lake build MODULE --old --no-build: sole missing leaf.
- lake build GaloisForLFunctions.RHTower.SelbergThetaCommonForcingMass --old: sole Built leaf (21 seconds); dependencies replayed, no umbrella/full build.
- lake env lean /tmp/sqb56_mass_audit.lean: all 8 public theorems have only propext, Classical.choice, Quot.sound.
- python3 scripts/formal_tools.py lint: passes.
Logs /tmp/sqb56_mass{,_source,_preflight,_build,_audit,_lint}.log. All owned Lean/Lake processes completed.

Updated docs/drafts/pipeline/1-in-progress/sqb-native-spectral-source-comparison.md with exact proof/current remaining obligation. Frontier map remained READ ONLY. Universal STATUS unchanged: this is source-specific, not a new route-independent Must/Cannot law. No computations, Git, launch.sh or subagents.

Search loop preceding proof:
Broad OR and deep all-view searches on native forcing, quadratic pencils, channel/Kirchhoff/Bessel coupling, theta/Bessel, reflectionless/Dirac/single-lobe, nonconstant/cusp decay/centered mass, plus mechanism-described deep cusp search. Outputs /tmp/sqb56_{native_forcing,pencil,channel,theta_bessel,dirac,mass,cusp}_search.json. Candidate lemmas, source arguments, proof ideas and proposed groups inspected. Inventory 55971 files complete; semantic coverage incomplete and most compiler metadata source-only/pending; some deadline stages incomplete. These searches do not establish absence.
Classical BM PDE response retains its explicit forcing (old excluded fixed-source family). Supersymmetric Dirac realizes singular values of A, not Xi occurrence. Reflection-folded Dirac still has common forcing. Real prime-channel convolution multipliers do not admit complex Xi frequencies. Bessel atom sums lack an established common symmetric relation between all channel values and derivatives. Generated cusp ingredient group combined unrelated centering spaces. No mathematical source-cancellation join found.

Next hardest obstacle: arithmetic cancellation producing normalized full-native occurrence residuals tending to zero, now with mass and unit normalization closed for common-forcing source. The pure Cauchy pairing formula and exact mean cancellation from SQB54 remain available. Do not claim the normalized graph equation itself is homogeneous or proves RH.