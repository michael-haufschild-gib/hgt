Mission: close actual Maass-to-automorphic/model chain, then arithmetic exclusion. Goal remains ACTIVE: this is verified progress, not full correspondence or Selberg proof.

Four new built modules (565 lines):
- formal/GaloisForLFunctions/HTGeometry/SmoothAngularAverage.lean (137): normalized integral over Ioc 0 (2*pi), compact domination, C∞, first/second radial derivatives, periodic FTC.
- formal/GaloisForLFunctions/HTGeometry/HyperbolicRadialODE.lean (87): eq_zero_of_initial for smooth complex solutions of sinh r*u''+cosh r*u'+lambda*sinh r*u=0, lambda>0, u(0)=0. ODE continuity derives u'(0)=0; energy |u'|²+lambda|u|² decreases.
- formal/GaloisForLFunctions/RHTower/MaassCircleDifferential.lean (185): namespace GaloisForLFunctions.RHTower.MaassCircle. Actual circlePoint in H uses existing root RHTower.D4BMNativeCircle chart. Actual C∞ source chain rule and polar symbol/connection identities prove circle_polar and maass_circle_polar. No supplied compatibility.
- formal/GaloisForLFunctions/RHTower/MaassCircleMean.lean (156): mean, mean_smooth, mean_zero; mean_polar line51, mean_radial_equation86; mean_cross_mul100 for any f,g of same positive real eigenvalue, even different subgroups; exists_mean_multiplier132 derives smooth scalar phi with phi0=1 and mean_f(z,r)=phi(r)*f(z), r>=0.

Final targeted LEAN_NUM_THREADS=1 lake build GaloisForLFunctions.RHTower.MaassCircleMean PASSED. Only four modules built (19s,8.9s,40s,5.2s); 12611 dependency jobs mostly cached. No full/umbrella builds. One owned foreground Lean process at a time; confirmed Lake likewise only one child. All29 public declarations #print axioms via /tmp/maass_circle_axioms.lean PASSED, only propext,Classical.choice,Quot.sound. No new warnings/settings/axioms/placeholders/computation certificates. Umbrella imports exactlyonce each.

Global lint DOES NOT PASS: both lint and lint --check-generated fail on unrelated untracked RHTower/MobiusThetaNativeMeyerAdmission.lean missing its umbrella import. Do not modify/wire another worker's unfinished source. index refreshed generateddocs +searchDB (11changed). Scoped checks pass. Logs /tmp/maass_circle_{final_build,axioms,lint,generated_lint,index}.log. All sessions collected; no owned Lean processes left after final process audit (see card).

Searches before code:
- /tmp/maass_circle_darboux_search.json deep: found existing actual circle geometry, no general Maass bridge.
- /tmp/maass_angular_average_methods.json: private compact averaging and periodicFTC mechanisms, generalized without copying source settings.
- /tmp/maass_volterra_uniqueness_search.json partialtrue: kernel assumptions do not directly handle origin. Pivot to positive energy, now closed in Lean.
- /tmp/maass_radial_energy_search.json: no needed theorem found.
- /tmp/maass_smooth_kernel_method_search.json deep,partialfalse: UnitaryFlowSmoothing source gives bounded convolution/commutation, not smooth-vector derivatives; finiteblock claims require compactness. Do not use as gap proof.
Broad arxiv Volterra/transmutation Aug2026 primary abstracts screened (2608.31099,2608.11956,2608.10594); no applicable theorem imported. Card records screens and limits.

NEXT PROMISING HARD-OBSTACLE ATTACK (paper calculation only, not Lean yet):
Avoid separate Haar polar integration by moving base-point derivatives to circle parameters. For F_z(r,theta)=f(circlePoint r theta z), r>0:
 X_z=y*d_x = sin(theta)*d_r + (coth(r)*cos(theta)-1)*d_theta.
 Y_z=y*d_y = cos(theta)*d_r - coth(r)*sin(theta)*d_theta.
Coordinate checks follow directly from existing offset/height first derivatives, sinh≠0, positive denominator, trig and hyperbolic square identities. For X, coefficients of Dx,Dy become1,0; forY becomeoffset,height.
Choose smooth radial bump in small positive annulus where proved phi has positive real part; its averaged action is c*f, c≠0. Integrate X/Y by parts onto the kernel. Formal-transpose kernels stay smooth, periodic, supported in annulus. Iterate to bound every word inX,Y appliedtof by |c|^-1 ||f||∞ ||kernel_word||1. Existing MaassCongruenceL2.source_bounded and finite quotient measure then give all-order L2; dominated differencequotients can identifyactualHilbert generators. This may be simpler than fullG Haar radial disintegration/smoothing.
Unproved Lean steps: transfer identities, nonzero compact kernel, repeated parameterIBP, uniform all-word bounds, Hilbert norm differentiation/completion. Search every mechanism first. Arithmetic exclusion of complementary series remains separate open problem.

Persistent complete record: docs/drafts/pipeline/1-in-progress/selberg-actual-maass-model-intertwiner.md, last sections. Prior verified quotient admission in mem:selberg/iwasawa-finite-covolume-actual-maass-quotient-l2-2026-09-12.
