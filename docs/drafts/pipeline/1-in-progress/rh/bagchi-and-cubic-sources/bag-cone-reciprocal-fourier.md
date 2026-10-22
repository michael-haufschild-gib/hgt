# BAG direct reciprocal-phase Fourier identity

01ax. Hard actual moving-profile transfer. Corpus searches and exact
mechanism recorded in P1 bag-physical-height-averaging-transfer. Source
search48168 incomplete inventory66653files/170pending, noerrors; all20+20
candidate/source statements inspected. Exact source APIs, signs and
normalizations read before deriving target.

For the actual normalized H_N=(logN)^3/N times the cone restriction of
bagCubicPhysicalSchwartz, conjectured ordinary Fourier transform is
 2pi integral_[1,2]^3 F_N(P)F_N(Q)conj(F_N(R))*W(PQ/R)/R²
                 *exp(-2pi*i*(P*b+Q*a+a*b/N)/R),
where F_N(P)=logN*bagCubicMellinSliceValue N eta_N 0 (N*P).
Full original W and selected shrinking cutoffs remain. No stationary
replacement or Mellin-window truncation.

Generic fixed-r identity on Schwartz plane: Fourier of
 exp(2pi*i*r*x*y)*Fhat(x,y) at(a,b)
 =r^-1 integral_p,q F(p,q)*exp(-2pi*i*(p+a)*(q+b)/r).
Prove using ordinary y Fourier inversion on a frequency-row Schwartz
restriction and continuous compact physical row, then x=(q+b)/r.
The full physical amplitude contains exp(2pi*i*p*q/r), so phase becomes
-(pb+qa+ab)/r exactly. Final physical r interchange requires uniform
fixed-N integrability of the two-frequency slices; do not assume it.
Scratch /tmp/bag-reciprocal-fourier-01ax.lean written, not built yet while
selected sharp-comparison production38864 runs. No result Lean-claimed.

After identity: two P,Q integrations by parts and R first variation
produce the audited curved denominator. W derivatives bounded on[1,2]^3.
Selected amplitude uniform derivative budgets can be proved by writing
logN/log(NP)=1/(1+h*logP), h=1/logN in[0,1]. The remaining smooth factor
V(P)/(1+h*logP) has uniformly bounded P derivatives by joint smoothness
on the compact (h,P) domain; denominator>=1. Leibniz with the selected
cutoff derivative budgets gives first-variation uniformity and kth
L1 budget delta^(1-k). No tau parameter is needed in this direct formula.
All amplitude, interchange, energy assembly and log-pullback claims remain
formal obligations; physical saving and RH remain open.

Height-interchange breakthrough01ax (paper, not audited): existing
bagThirdPhysicalSlice_eq_inverse expresses EACH two-frequency physical
slice at height r as inverse one-dimensional Fourier transform of the
Schwartz restriction z->Fhat_3D(x,y,z). Therefore its norm is bounded by
integral_z |Fhat_3D(x,y,z)|, INDEPENDENT of r. Physical support restricts r
to the finite band. Integrating this majorant over(r,x,y) costs only band
length times the full three-dimensional Fourier L1 norm, already finite
by Schwartz. Thus fixed-N Fubini needs no extra parameter-derivative theorem.
The frequency-row identity, obtained by Fourier-inverting the same exact
public equality, identifies the cone restriction with the height integral.
Fixed-r chirp identity plus this absolute Fubini then produces the direct
reciprocal formula. Construct plane slices of the original Schwartz source
by proper affine compCLM; support and smoothness inherited automatically.
This removes a previously stated uniform fixed-N slice-regularity obligation
through an existing corpus inverse-Fourier bound; actual Lean assembly next.

Formal checkpoint01ax: fixed-r generic chirp Fourier identity scratch87036
PASS (mathlib-only, no warnings). Added exact frequency marginal bound,
its integrability, full joint physical-slice integrability, cone/height
identity, proper affine Schwartz plane slices and complete r/Fourier
Fubini assembly. Full scratch63460 reached final generic identity with
only two local rewrite/projection errors, now corrected. Actual selected
physical amplitude specialization appended: full W, conjugate/logarithmic
slices, r^-2 and exact -(pb+qa+ab)/r phase. Current scratch26143 running;
no public result or production leaf claimed yet. Consumed extension
scratch templates cleaned; active /tmp/bag-reciprocal-fourier-01ax.lean
retained. Only one owned foreground Lean audit active.

CLOSED01ax: full scratch56722 PASS, production13249emptyPASS, finalaxiom77734
bothstandard3. Index67027PASS/API2/importonce; lint81297 sevenunrelated
unreachable362warnings,noownederror. P2/P3 bag-cone-reciprocal-fourier record
exact full identity and proof. Normalization and amplitude/H^s assembly remain open.

Exact normalization CLOSED01ax: ChiCubicNormalizedFourier78lines/API1,
bagCubicControlledCone_normalized_fourier. For everyN>1 and admissibleH,
(logN)^3/N times the ACTUAL cone Fourier transform is exactly
 2pi integral_RQP F(P)F(Q)conj(F(R))*W(PQ/R)/R²
                *exp(-2pi*i*(Pb+Qa+ab/N)/R),
F=bagCubicNormalizedSlice(H/N,1/logN). Three explicit positive-dilation
changes of variable supplyN³; exact slice identities and total-field
algebra, includingR=0, pay all normalization/Jacobian factors.
Scratch49555PASS (two redundanttactics removed); production15138emptyPASS;
axiom95238standard3; index35848PASS/API1/importonce. Lint28068terminal1:
two unrelated unreachable(KuznetsovKernelIntegral,KuznetsovPoincareRows),
362warnings,noownederror. Diff checkPASS. No full/umbrella build.
The actual coupled energy estimate remains open; normalized identity
supplies its literal target. Scratch /tmp/bag-reciprocal-ibp-01ax.lean
now tests exact height resolvent and norm control; no further claim yet.
