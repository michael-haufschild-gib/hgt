# HB original two-source clock cap: verified 11 September 2026

Goal remains ACTIVE. Extinction and RH are NOT proved. No added source-law premise or axiom. No #print axioms was used. No subagents spawned.

## Verified leaf
`formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMLateSourceClock.lean`
Namespace `RHTower.D4BMLateSourceClock`; 352 lines, ten public theorems and three public definitions.
SHA-256 `e3e2e9f17106759afcf185d9995cd9af35f3533ab80642c6189e2e88d4967f7d`.
Scratch passed without warnings. Exact isolated cached `lake build GaloisForLFunctions.RHTower.ThetaCuspHawkingBMLateSourceClock` audit passed in 98s without warnings, twelve cache roots, only leaf compiled. Wired once into `RHTower.lean`; no umbrella/full build. Static API refreshed and all thirteen entries verified (API uses bare declaration names plus module columns, not fully qualified names). Global lint passed with existing large-file warnings. Canonical olean 1534456 bytes and ilean 93179 bytes retained. All owned scratch/search/audit/log temps cleaned. All owned Lean/search sessions terminal; no owned Lean process remains. No commit/push.

## Exact source result
s=physicalRate(q,branch), t=-s-3; chi is original smoothTransition.
alpha=(2s+1)(2s+2), gamma=(2t+1)(2t+2).
b_r(z)=r(r-1)z[3+(2r+3)z]/[2(1+z)].
g_r(z,v)=exp(2rv)[(2r+1)(2r+2)chi(v)-b_r(z)chi'(v)].
These are existing `D4BMSpinTwoDelay.clockProfile`; `clockProfile_original` gives their original reduced wave-image-source coefficient, with radial prefactor.
W_V(h)=existing clockDensity=integral_0^(V-h) g_s(u,v+h)g_t(w,v)dv.
Global closed original-source cap theorem: partial_V W_V(h)=g_s(u,V)g_t(w,V-h), retaining both onset regions.
On 1<h<V-1:
a=alpha[gamma-6 b_t(w)] tailClock,
b_V=alpha gamma exp(-6V)/6,
W_V(h)=a exp(2sh)-b_V exp((2s+6)h).
Uses original finite_clock_contact and exact finite tail integral. Full first and second h derivatives proved.
(partial_h-2s)W=-6 b_V exp((2s+6)h), partial_V W=+6 b_V exp((2s+6)h).
b_V !=0 for every actual Xi q by occurrence nonrealness; not an RH assumption.
For h>1,V>h+1,H>0:
W_(V+H)(h)-W_V(h)=b_V[1-exp(-6H)]exp((2s+6)h) !=0.
H is unchanged original time. This compares observation caps for the same source, NOT the complete spacetime-field translation action.

## Actual spin-two attachment
Z=existing direct/image delayArgument, A=delaySlope, B=original invariantTimeSecond.
E_r=r²/A²-3Br/A³+(3B²-A²)/A⁴.
Existing delayBulk = F[a exp(2sh)E_(2s)-b_V exp((2s+6)h)E_(2s+6)]
with actual native spin-two primitive F; x,y:Iic0 and h in Ioo(max1 causalDelayStart)(V-1). Original full angular half-square mean retained, not an eigenvalue/scalar substitute. Both images covered. Original endpoint transfer remains in its existing module; late formula is not extended across transition layer or characteristic endpoint.
Weighted Rodrigues correction: -Delta(Delta-2)M=-partial_Z²[(Z²-1)² partial_Z²M]. Twice-transposed coefficient in dh measure is A partial_Z²(W/A), not unweighted fourth derivative. Clock-only bulk annihilation would require W/A affine in Z. No proof that the complete direct-minus-image/reversed-branch/channel action cancels.

## Public theorem lines
91 clockDensity_late; 146 clockDensity_cap_balance; 207 clockDensity_late_derivatives; 218 terminalCoefficient_ne_zero; 238 clockDensity_late_terminal_law; 254 delayBulk_late; 279 clockDensity_terminal_flux; 304 clockDensity_terminal_flux_ne_zero; 313 clockDensity_finite_cap_translation; 335 clockDensity_finite_cap_translation_ne_zero.

## Documents
`docs/drafts/pipeline/3-formalized/hb-two-source-clock-cap-balance.md`: dependency-closed proof and actual scope.
`docs/drafts/pipeline/1-in-progress/hb-fixed-clock-source-translation.md`: C20-C21, source mechanism tests, research applicability limits and verification.
Frontier map and STATUS not edited. Shared worktree has others' changes; preserve them.

## Research and next hard obstacle
Deep/hybrid generations 874971,874982,874991,875003,875070,875160 were partial. No source sign/extinction producer. Proposed generic dual-system/three-point source/energy expansion hits did not identify HB physical action. Existing self-dual Plebanski local Jacobi no-go was checked (exact graph energy, only diagonal zero); do not duplicate it.
Broad June-Sept2026 arxiv tests: Spin(7) ddPhi/cohomology; unitary group cohomology; skyrmion circle-mean residual bounds; nonlocal transport compactness/energy saturation; dihedral elliptic boundary domains; helicity descendants and celestial metric-source completion. Exact sources/applicability failures in active card. No paper theorem imported as source-law assumption.
Adjacent newly added PhysicalRadialNorm read through final theorem: original horizon finite part is nonzero Gamma quotient at fundamental frequencies and vanishing reduces to remaining residue factor. It supplies no vanishing multiplier or physical sign. Not modified or independently rebuilt.
Next attack must derive compensation/sign of COMPLETED causal/left-QNM action with this explicit cap: onset layers, direct-minus-image and reversed branch, independent SS/SV/VV channels, solved ++/+- corrections, changing weights and all faces. Do not substitute covariance of W or a redefined clock. After physical identification Cphys=-Sigma|D|² (Sigma>0), independently source-prove Re Cphys>=0 or strict epsilon<1 deficit estimate; that remains missing. Current leaf evaluates a necessary contribution, not the requested extinction law.

Lean workflow reminder: one owned foreground process; `lake env lean /tmp/file.lean`; exact leaf build final audit only; cache dependencies, wire without umbrella build, no #print axioms/numerical experiments/proof debt. For real-to-complex FTC composition use HasDerivAt.scomp, not comp. Annotate real integrals/derivatives explicitly before complex casting; normalize casts in exponent identities AND target together.
