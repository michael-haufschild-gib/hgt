# BAG exact reciprocal Fourier representation

01ax. Paper proof and production Lean audit COMPLETE.

For every N>1 and selected edge width0<H<N/2, the ordinary Fourier
transform of the actual cone-restricted Schwartz amplitude at(a,b) equals
integral_r integral_q integral_p
 (2pi)*slice(p)*slice(q)*conj(slice(r))/r² * W(pq/(rN))
 *exp(-2pi*i*(pb+qa+ab)/r).
All three original Gaussian/logarithmic slices, the conjugate, selected
cutoff family and full physical height window remain. No asymptotic,
stationary substitution, cancellation or interchange premise is assumed.

Fixed-height proof: ordinary one-dimensional Fourier inversion on a
Schwartz frequency row, followed by x=(q+b)/r, gives the reciprocal chirp
kernel. The existing physical-slice inverse formula bounds each height
slice by integral_z |Fhat_3D(x,y,z)|, independent of height. This marginal
is integrable by Schwartz integrability and the volume-preserving
coordinate map. Finite physical-height support therefore pays all joint
integrability and Fubini steps. The same inverse formula identifies the
cone with the height integral. Finally the original pq/r oscillation
cancels exactly, leaving -(pb+qa+ab)/r and r^-2.

Source: ChiCubicReciprocalFourier563lines/API2.
Scratch56722 PASS; production13249 emptyPASS; finalaxiom77734 both results
standard3 only. Index67027 PASS; API2 and umbrellaonce verified. Lint81297
terminal1: seven unrelated unreachable modules (BesselInverseGaussianComplexRate,
CauchyBetaIntegral, ThetaCuspRatioTerminalAmplitudePolynomial,
ZetaSquareDiagonalHarmonic, LegendreFusionGaugeNeutrality,
LegendreResidualTransduction, UnframedPromoterNoGo),362warnings, no owned
error. No resource-limit increase or full/umbrella build.

The exact raw identity is closed. Normalized scaling, actual amplitude
budgets, uniform Sobolev energy, log-coordinate/Mellin tails and moving-test
signed transfer remain open. Full sharp-action transfer and RH are not
proved by this identity.

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
