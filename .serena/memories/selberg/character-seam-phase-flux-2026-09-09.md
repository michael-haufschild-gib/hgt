# Selberg cycle47 — original character seam flux, fully audited

Latest continuation of mem:selberg/inversion-phase-full-gradient-2026-09-09. Full unbudgeted Selberg1/4 goal remains ACTIVE / UNPROVED. Current turn is PROGRESS: new positive original-source mathematics. Do not mark goal complete or blocked. User insists on corpus-derived conjecture→proof/fail→pivot loops, not repeated negative wrappers. One owned foreground Lean worker at a time, lake env lean for scratch/source, serialized single-module lake build for final audits, no full/umbrella builds or numerical experiments. Shared dirty tree; preserve others' changes.

## Completed source modules and exact APIs

1. formal/GaloisForLFunctions/RHTower/SelbergMaassProjectionFlux.lean, namespace GaloisForLFunctions.RHTower.SelbergMaassProjectionFlux. Eight public theorems, imports audited InversionPhaseEnergy.
- character_complement_orthogonal: <v-Pv,Pw>=0.
- projection_mismatch_corners: P_s v-Q_-r v=(I-Q_-r)P_s v-Q_-r(I-P_s)v.
- transfer_loss_mismatch_identity at42: ||v||²-||C_rs v||² = ||(P_s-Q_-r)v||² + ||(I-Q_-r)(I-P_s)v||². Exact actual projectors, every r,s and every level.
- projection_mismatch_le_transfer_loss; transfer_loss_nonneg.
- character_flux_difference: difference of Re<P_s v,w> and Re<Q_-r v,w> is their exact coherent mismatch pairing.
- character_flux_sq_le_transfer_loss: squared difference <= actual transfer loss * ||w||².
- character_flux_sq_le_phase_energy: same with literal complete normalized arithmetic triple phase displacement.

2. formal/GaloisForLFunctions/RHTower/SelbergMaassCharacterSeamFlux.lean, matching namespace.21 public declarations. Imports ProjectionFlux, CurrentTransport, TraceBoundary, CharacterGradient, TraceStokes.
- sourceDerivative N f v z: WithLp vector q↦dir v(field N f q)(z:Complex). Every coordinate is an original physical derivative.
- sourceDerivative_neg, sourceDerivative_components: real-linearity in direction.
- sourceDerivative_gradient: ||D_1 F||²+||D_I F||²=original gradientDensity.
- sourceDerivative_polar_energy at66: ||D_v F||²+||D_(I*v) F||²=normSq(v)*gradientDensity. Exact, no cross terms discarded.
- sourceDerivative_sq_le_gradient.
- sourceDerivative_modular at83: actual reciprocal-square Möbius differential and regular deck permutation, via audited field_dir_modular.
- sourceDerivative_radial_inversion at90: D_(S z)F(S z)=-U_S D_z F(z).
- radialFlux N f r z:=Re<P_r sourceVector(z),sourceDerivative(z,z)>.
- radialFlux_seam_identity at107: radialFlux(z)+radialFlux(S^-1 z)=Re<(P_r-Q_-r)source(z),D_z F(z)>. Proof applies radial inversion at S^-1 z and actual lower-character conjugacy; DOES NOT assume U_S=U_S^-1 on arbitrary vectors.
- radialFlux_seam_sq_le_loss; radialFlux_seam_sq_le_gradient.
- sourceDerivative_eq_dir at140: vector above equals actual source chart Fréchet derivative, via C² source and coordinate CLM composition.
- character_mass_dir at153: dir v(||P_p,r source(ofComplex w)||²)(z)=2 Re<P_p,r source(z),sourceDerivative(v,z)>. Actual mass derivative, not an independent flux datum.
- radialFlux_seam_angular_remainder at176: squared paired flux + transferLoss*||D_(I*z) F||² <= transferLoss*normSq(z)*gradientDensity.
- inverse_inversion_on_unit_circle at186: S^-1(ofComplex(point x y))=ofComplex(point(-x)y), with positive y and x²+y²=1. Uses proved forward inversion at -x and inverse group action.
- unit_circle_flux_sq_le_phase_gradient at192: actual paired radial flux squared <= complete triple phase energy of original source at (x,y) * original physical gradientDensity(point x y).
- circleNormalCurrent N f r x y at210: literal dir((-y^-1) • point x y) of projected mass at point x y. On the circle this is outward normal density (-x/y,-1), retaining arc-length Jacobian.
- circleNormalCurrent_eq_radialFlux at216: exactly -2*y^-1*radialFlux(point x y).
- unit_circle_normal_current_sq_le_loss_gradient at232: squared paired outward normal current <=4/y² * actual transferLoss * physical gradientDensity.
- CAPSTONE modular_arc_normal_current_sq_le at250: for x : Set.Icc(-1/2)(1/2), original y=TraceStokes.arcHeight x, squared paired actual outward current <=(16/3)*transferLoss(source at point x y)*gradientDensity(point x y). Constant independent of level. This is a boundary-current estimate, NOT the desired full-domain spectral constant4.

## Corpus / positive proof loop

Initial prior-turn interruption left a concrete card and corpus search, no owned running Lean. On resumption verified unchanged cycle46 hashes and card. Queries explicit OR because spaces default AND:
- boundary impedance/two projections/angle gap/Hardy gluing/spectral concentration:23 declarations/9modules, /tmp/selberg_gluing49_corpus.json.
- gluing/impedance/uncertainty/projection angle/Schur complement:728 declarations/179modules, /tmp/selberg_gluing49_wide.json. All indexed matches retrieved, not all proof bodies inspected.
Read actual HTGeometry/TwoProjectionDeficiency (angle bounds explicit, not supplied Maass hypotheses), ProjectionCornerCommutator (positive complementary-corner algebra), RHTower/SelbergScatteringSpectralConcentration (independent Xi-family input, not actual Maass input), actual CurrentTransport/TraceBoundary.
Conjecture→proof: exact mismatch/loss corners; actual radial derivative and coherent seam identity; stronger exact polar energy retaining angular remainder; literal projected-mass derivative; complete triple phase bound; actual normal-density Jacobian; uniform16/3 modular-arc bound. No numerical experiments or negative-wrapper detour.

## Completed audits and artifacts

All29 public declarations passed complete scratch, source, and post-build axiom checks. Every axiom list contains only standard propext, Classical.choice, Quot.sound. No added axioms/admissions. No new source warnings. Final builds serialized and each rebuilt ONLY named target: ProjectionFlux11s, CharacterSeamFlux4.7s. Cached EvenL2LogUnitary informational suggestion is unrelated existing output. Only ProjectionFlux olean emitted pre-build for dependent scratch.
Both source SHA256 hashes verified unchanged, exact29 names in /tmp/selberg_seam49_manifest.json. /tmp/selberg_seam49_audit.json records full audit. Search coverage31 entries incl2 local gammaNormal instances; all29 public declarations verified under exact module rows in formal/LEAN_API.md. Both imports once in RHTower. Index refreshed; repository lint PASSED with existing large-file warnings. Scoped whitespace and every local link in3 updated research cards checked.
Every owned Lean/build/index/lint handle terminal. Final process scan finds no owned Lean/Lake worker. No build overlap in this cycle; no full/umbrella build, commit, push. Never start next Lean while write_stdin still returns session_id. All source files now finished; do NOT rerun checks without a change/failure/new concern.
Artifacts prefix /tmp/selberg_seam49: projection.lean/log, source.lean/log, projection_source.log, source_final.log, projection_build.log, source_build.log, axioms.lean/log, manifest.json, audit.json, coverage.json, index.log, lint.log.
Card moved to docs/drafts/pipeline/3-formalized/selberg-character-seam-flux.md; old1-in-progress path absent. Parent selberg-quarter-conjecturing-loop.md has cycle47 and newest verification entry. selberg-original-source-conserved-currents.md frontier updated.

## Next positive proof target

Attach literal character currents to an integrated characterwise core–cusp energy identity retaining actual Bessel boundary forms, all Fourier modes, and positive angular remainder. Test whether actual arithmetic phase coupling controls full quarter deficit. Need original full-domain mass<=4 physical gradient; no endpoint assumed. Existing full-gradient full-cell identity already audited, as are original Bessel remainder and boundary form. Avoid reproving this cycle's source/polar/corner formulas. Corpus search for a concrete integrated mechanism, then prove it on actual projected source.
Relevant existing files confirmed: SelbergMaassBoundaryForm.lean, SelbergMaassBesselRemainder.lean, SelbergMaassFullGradient.lean, SelbergMaassTraceStokes.lean. There is NO SelbergMaassCoreEnergy.lean or SelbergMaassCoreStokes.lean. Use rg --files before reading an unobserved path. point is SelbergMaassMean.point, defined in SelbergMaassFourierMean.lean; namespace != filename.

## Toolchain lessons verified in scratch

Complement loss proof requires simp_rw [characterProjection_loss] after transfer_loss_decomposition, not a single rw of only first square.
For real scalar polar expansions on EuclideanSpace Complex Deck, norm_add_sq_real +real_inner_smul_left/right work. Finish norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, neg_sq and ring. Opening UpperHalfPlane and Complex makes I,I_re,I_im ambiguous; always Complex.I etc.
sourceDerivative_eq_dir proof: compose actual C² derivative with (EuclideanSpace.proj q).restrictScalars Real; congrArg evaluation; change both sides to literal source field coordinates.
HasFDerivAt.norm_sq has natural 2-smul: simplify smul_apply, ContinuousLinearMap.comp_apply, innerSL_apply_apply, nsmul_eq_mul before change. Deprecated ContinuousLinearMap.smul_apply should not be used. Real PiLp inner is NOT definitionally real part of complex PiLp inner; simp only [PiLp.inner_apply,Complex.re_sum] then rfl proves it.
For normal current, unfold dir and rw/map_smul before change; derivative linearity is not definitional. Rewrite ofComplex_apply_of_im_pos consistently in both h and target (simpa only using h), since rw at h also replaces UHP points with mk constructors.
Avoid ambiguous add_le_add_right from open namespaces; add_le_add h le_rfl works. inv_pow orients inverse-of-power to power-of-inverse in reverse for ring goal; rw [div_eq_mul_inv,← inv_pow] then ring. No recalled unverified mathlib names used in final sources.
