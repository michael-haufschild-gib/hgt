# Moving-corner false-root bifurcation: frozen protocol

Parent result: complete corner ratio is real on `Re rho=1/2`, but at `L=2e` has an additional reflected pair of real-ratio points at heights 50 and 100. Other tested scales did not. Derivative deletion produced a different extra pair at height 14, `L=10`.

Question: are extra roots numerical accidents, isolated scale effects, or roots born through a symmetry-forced pitchfork from the critical line? Classify topology rather than optimize a threshold.

Reflection makes `Im kappa(1-sigma)=-Im kappa(sigma)`. A symmetric extra pair can be born when the central slope `partial_sigma Im kappa|_(1/2)` changes sign. For heights `14.1347,20,30,50,75,100,150,200`, scan `L` on a fixed 49-point geometric grid from `2e` to 40, refine every central-slope zero, and record the central cubic coefficient. Independently count all real-part roots on fixed scales `2e,6,8,10,15,20,30,40`. Pod A runs complete `D_star`; Pod B runs derivative-deleted control.

Candidate classification passes if root-count changes occur only across refined central-slope zeros, extra roots are reflected to numerical precision, and 100/160-digit slope/cubic repeats agree. A root entering through sigma=.02/.98 or denominator zero is separately classified and falsifies pure pitchfork description.

Consequences: persistent/cofinal false-root branches kill any corner-only reality detector. A compact finite-scale island constrains required cancellation by remaining currents but does not rescue complete action. Ablation differences measure material boundary sensitivity; derivative deletion stays unphysical.

Exact radial primitives, all source-polynomial corner coefficients and complementary ordering are unchanged from parent. Angular pairings, other faces, full causal current and SS/SV/VV sectors remain unknown. One 570-second guard per pod, 14 workers maximum, unique remote directories, partial output retained, no grid enlargement.

Scientific-method mechanics: turn failure into classification; exploit symmetry; vary scale and height jointly; compare complete/ablated boundary structure; refine bifurcations; challenge with root counts; preserve positive topology law if detector fails.
