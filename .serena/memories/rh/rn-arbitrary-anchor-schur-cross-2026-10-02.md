Route RN, active unconditional RH goal NOT achieved. No subagents.
Completed RN-P-7t: generalized actual center Schur cross sign to every nonnegative anchor:
H(b,x)H(b,y)<H(b,b)H(x,y) for 0<=b<x and b<y.
Actual larger-node projection coefficient (Hbb Hzy-Hbz Hby)/ThetaSturm.determinant b z>0.
Namespace RHTower.ThetaGaussianCoarea.
Modified existing leaves ThetaTailGaussianSubmodular and ThetaTailCenterSchurCross (no new module). Existing center capstones preserved as specializations. Umbrella imports already present.

Key source proof, with t=shift b x u, s=b+t,r=x+t,L=s+r,P=p(s)+p(r),M=L(c(s)+c(r))-2P>0:
d_x massRate(b,x,u) numerator =
(x-b)(L c(r)-P)+L s(c(r)-c(s))+b M>0.
All signs follow actual c increasing, tangent gaps and prior mixed_margin_pos.
New public potential_submodular_at, massRate_hasDerivAt_right, massRate_strictMono_above, anchoredAmplitude positivity/continuity/zero/strictAnti/le_one, density_anchored_product_lt.
Generalized original covariance proof to anchoredAmplitude rather than duplicating it.
New capstones anchored_schur_cross_pos (line107) and anchored_positive_node_coefficient_pos (line128).
Two targeted lake --old leaf builds passed; both final lake env lean actual-file checks passed with zero diagnostics; all29 public theorem axiom queries returned only propext, Classical.choice, Quot.sound. No full/umbrella builds, numerical experiments, new axioms, heartbeat increase, subagents or commits.
Lint:12 unrelated unreachable modules; none in these leaves. Exact list in P3 certificate.

New P3 certificate docs/drafts/pipeline/3-formalized/theta/rn-gaussian-coarea-arbitrary-anchor.md.
RN map updated to arbitrary-anchor sign; earlier center P3 annotated.
Working log RN-P-7t appended to docs/drafts/pipeline/1-in-progress/rn-singular-weight-conjecture-loop-2026-10-01.md.
Main hard card docs/drafts/pipeline/1-in-progress/rn-center-schur-coordinate-row-flow.md updated.
Prior context mem:rh/rn-gaussian-coarea-center-schur-2026-10-02.

Hard targets unchanged: finite-pair coordinate-port UPPER compensation, full port signs at general anchors, arbitrary rank, arithmetic off-diagonal transfer. The new theorem is only a lower sign.
Current turn began trying joint-center necessary test for E_y<0. Paper calculation (NOT Lean audited, sign OPEN):
P=k0^2,I=derivativeMass,J=H00,S=secondMass,q=c0, beta=2I-P.
E(x,y)=beta/P-coordinateEnergy/(3P)(x²+y²)+(S/2-I²/J)/P*xy+...
E_y(x,x)/x -> [-S/6+2qI-2qP/3-I²/J]/P.
Necessary sign D=S/6-2qI+2qP/3+I²/J>=0.
Based on existing center Hxy=beta,Hxx=-2I,Hxyyy=qP-2S; Hxxyy=2S also derived on paper but not yet formalized. Joint Taylor remainder and D sign remain unproved. Do not claim a falsification or use D as premise. Formula includes full inverse-Gram I²/J term.
No owned tool processes remain running; All9 owned /tmp search/build/audit files removed successfully; cleanup also recorded in the working log. No Lean edits needed after passed final audits.