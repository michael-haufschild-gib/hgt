# Direct Xi identification for the actual prescribed norm shift

- **ID:** sz-prescribed-shift-direct-xi-identification
- **Stage:** 5-failed
- **Route:** SZ
- **Type:** FALSIFIED
- **Date:** 2026-10-02
- **Claim rejected:** Some cofinal aperture sequence of actual prescribed-shift V2 Livsic carriers converges locally uniformly to xiHedenmalmLivsicTarget on the upper half-plane.

## Exact obstruction [PROVED HERE]

The actual covariance first defect tends to0 along the entire positive-aperture
filter, hence along every cofinal aperture sequence. The actual V2 defect is
exactly 2i times the carrier derivative at i. Locally uniform convergence of
these actual holomorphic carriers to Xi would force this same sequence to
converge to xiHedenmalmLivsicFirstDefectJet. The corpus proves that scalar lies
in (77/85,1). Uniqueness of limits contradicts convergence to0.

Lean root, with no hypothesis binders:
`RHTower.not_exists_suzukiTaV2_prescribed_cofinal_xi_limit` in
SuzukiTaV2PrescribedXiSeparation. Final audit13420 passed.

## Strongest positive survivor

With actual c_a and common scale t_a=c_a exp(-2a), both literal V2 parity
energies converge to1/4. Their sum tends to1/2 and signed difference to0.
The normalized raw anchor Wronskian tends to0 with its two apertures
independently cofinal. These are actual source/covariance limit laws, not
restatements of the rejected identification.

Dependency-closed proof, exact Lean roots and final audit ledger:
P3:sz-prescribed-shift-first-defect-collapse. All three leaves have passed
final audits; all twelve public axiom checks passed (audit60205).

## New insight and boundary

The prescribed norm shift produces asymptotically equal actual V2 parity
channels, incompatible with the strict imbalance required by the normalized
Xi target. Any successful route must solve a genuinely different shift or
normalization problem. This rejects these precise coordinates along every
cofinal schedule; it does not reject route SZ or RH.

The stronger positive survivor is now formalized:
P3:sz-prescribed-shift-full-carrier-collapse proves locally uniform convergence
of the entire actual prescribed-shift family to0 on the upper half-plane,
along the full positive-aperture filter. Four final leaf audits and thirteen
public axiom checks pass, standard axioms only. This identifies the whole
limiting carrier, beyond the single collapsed jet. Full signed Wronskian/cusp cancellation,
shift removal and Xi identification remain hard open obligations.

## Stronger obstruction: every raised metric shift

The exclusion now extends to every nonnegative increment t_a of the
prescribed shift, with no upper bound or regularity condition on t_a.
`RHTower.not_exists_suzukiRaisedMetric_cofinal_xi_segment_limit` rejects
even pointwise Xi identification on 1/2<Im(z)<1 along the imaginary axis;
`RHTower.not_exists_suzukiRaisedMetric_cofinal_xi_limit` excludes locally
uniform Xi identification on the upper half-plane. Both roots have no
hypothesis binders. Carrier final61584 passed without warnings.

Positive survivor: for the same actual Friedrichs operator,
x_t=C(I+tC)^(-1)p satisfies (A+c+t)x_t=p and
norm((c+t)x_t-p)<=norm(c C p-p). The actual covariance retains reflection.
Both complete complex mixed pairings have joint-filter limits 1/(1+s),0,
uniformly over all t>=0; the literal Fourier quotient tends to0 on the
interior imaginary segment. Zero increment recovers the original V2
carrier exactly. Source final42847 and limit final93705 passed without
warnings. The source contraction and uniform pairing classification are
new positive information, not a restatement of the excluded convergence.

This closes the proposed repair by increasing the metric shift. It does
not classify the raised carriers away from this segment or prove a Schur
property for them. The next question is sub-prescribed admissible shifts
near the actual spectral floor; see P1:sz-spectral-edge-shift-necessity.
Unshifted canonical-head sign, singular-regime source residues and RH
remain open. Full paper proof and audit ledger are in
P3:sz-raised-metric-shift-source-collapse. All seventeen public axiom checks
passed in50108 with only propext, Classical.choice and Quot.sound.

### All-admissible positive survivor: relative-floor necessity

P3:sz-spectral-edge-shift-necessity strengthens the raised-shift obstruction.
For the actual interval covariance, every strict admissible shift d>-E is
constructed through m=(E+d)/(E+c)>0. Its transfer has coercivity min(1,m),
and the exact weighted source defect proves two full complex weighted
mixed-source limits. Any nonzero fixed-source carrier limit on the interior
imaginary segment forces m->0; local uniform Xi identification therefore
requires relative approach to the actual floor. No simple-ground, parity,
nonzero-overlap or positive-shift premise is assumed. This does not say the
absolute gap tends to zero, and it does not prove an identifying schedule
exists. The source and limit leaves plus the necessity leaf passed final
Lean audits17124,44729,15580; reused witness audit2368 passed. Axiom39186
checked all15 new public theorems and the witness, standard axioms only.
Actual signed residues and unshifted sign remain open.

### Actual amplified-vector survivor

P3:sz-actual-source-defect-quasimode now proves the vector-level consequence
of the relative-floor necessity. A nonzero fixed-source carrier limit
forces exp(-a)*norm(d*x-p) eventually bounded below and the normalized
actual defect to satisfy the relative covariance eigen-equation. The
source/quotient identities supply the amplification; no source overlap or
spectral gap is assumed. Source final5344, quasimode final76442, and all nine
public axiom checks52632 passed with standard axioms only. Signed parity
and the canonical-head phase gap are still open; this is not an RH proof.
