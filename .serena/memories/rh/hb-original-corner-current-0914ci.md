# HB actual remainder cutoff agreement — 2026-09-14 ci

Active target remains full temporal/metric/QNM matching or proof matching impossible. RH unproved. Frontier map read-only; no computations, Git, launch.sh, axioms printing, heartbeat increases, or umbrella builds.

User asked whether computations/results.md has useful findings. Reviewed relevant HB/QNM, coupled-reader and photonic sections and the fixed-clock-QNM-capacity and physical-horizon-angularpair reports. Existing own facts F160,F176,F178,F180,F187,F192 already capture the relevant distinctions:
- Finite-variation Jost spectra cannot persistently cancel the nonzero AIME counterterm. The full original metric/action has NOT been identified with that spectral class; persistent cancellation must also be connected to the actual matching claim.
- The negative quartic horizon-background experiment uses lift/lift, whereas the target uses original causal source/physical left-QNM. It is not the identified coefficient of our actual pairing.
- Physical photonic drive reverses the geometry-only survival failure, yet near-unit survival retains logical operator mismatch. Useful comparison method, not an HB identity.
- Two-reader radial rank loss involves columns with different temporal source frequencies; it is not a demonstrated full temporal kernel.

New verified module:
formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMOriginalCornerCurrentAdmission.lean
namespace RHTower.D4BMOriginalCornerCurrentAdmission.
Imports OriginalCollarCurrentBounds plus mathlib derivative measurability, improper integrals, product integration.
SHA256 dab770523026c5163e0416b2d8fb821dfe38e798d01dc3b31860c4f413441750.
Clean scratch passed. Isolated exact lake build GaloisForLFunctions.RHTower.ThetaCuspHawkingBMOriginalCornerCurrentAdmission passed (36s, 2 jobs). No dependencies rebuilt: 4562 existing oleans copied to isolated cache, missing none. Five leaf artifacts promoted; olean 368136 bytes. Umbrella wired immediately after OriginalCollarCurrentBounds, not built.

Definitions:
reader w chi L = exp(w*(-L/2))*tortoiseMode true w chi (-L/2)
readerTrace w chi = connection w chi/(2*w)*power(-w,2)
scalar q br amp L p = originalScalar q br amp p(p+L)
sourceRemainder = exp(-w*p)*(reader*(deriv scalar+w*scalar)-readerTrace*(deriv horizonTrace+w*horizonTrace)).
forcingRemainder retains actual timeOriginalForcing(p+L/2,-L/2,z)/horizonCoordinate(-L/2) and the original full forcingTrace, with both angular channels.
staticCut f L0 T integrates f on L>L0,p>0 with p+L/2<T.
radialCut uses L/2<T on the same product collar.

Public results:
original_source_remainder_integrable q br amp w hw hwr:
for Im(w)!=0 and Re(w)>G=Re(1-q/2), exists L0>0 with actual sourceRemainder absolutely integrable on (L0,infty)x(0,infty).
original_forcing_remainder_integrable q br amp w hw hwr z:
same for actual forcingRemainder, for Im(w)!=0, Re(w)>0, at each fixed angular point z.
original_source_remainder_cutoff_agreement and original_forcing_remainder_cutoff_agreement additionally prove staticCut-radialCut tends to zero.

Mechanism: actual scalar globally jointly continuous via original native response + original onset lift. mathlib measurable_deriv_with_param supplies parameterized derivative measurability; no extra derivative smoothness is assumed. Actual reader is continuous for L>0. Original forcing factorization provides its measurability. F203's exponential bounds give a product-integrable majorant; DCT proves both cutoff limits equal the same product integral.

Scope: these are actual remainders, not an arbitrary density ansatz. They remove the remainder's cutoff discrepancy. They do NOT compute the retained nonintegrable leading horizon density's first temporal moment, establish full angular finite-part assembly/unbounded interchange, attach the complete metric corner, or continue the assembled action to QNM frequencies. F140 remains the paper causal-leading-triangle identity awaiting full attachment: -J1-K log2; candidate residue cancellation is not complete matching. Forcing integrability is pointwise in angular z. Chart Jacobian 1/2 preserves zero remainder difference.

Own fact log updated F203 and added F204/F205. Own card hb-physical-mode-action-contact.md updated around horizon error/product admission. No frontier/results/other-agent log changes.
Global formal lint exit1: same 159 large-file warnings and sole unrelated existing unreachable module GaloisForLFunctions.RHTower.Sieve.KloostermanGlobalCollisionCoprime; no new leaf lint error.

Search: broad OR variation/Jost completed, coverage 57925 files, 57924 indexed, one failed; mostly source-only. Deep complete-action spectral-class query partial; retrieved variance rather than variation, unrelated finite-set methods, unverified ingredient set; no verified full-action representation supplied. No numerical experiment run.

Lean details: use explicit change before rewriting partially applied scalar/reader; explicit comp_of_eq avoids composing affine arguments at the wrong point. ContinuousAt product expression needed convert using 1; funext l; rfl. Product-volume rewrite is Measure.volume_eq_prod together with Measure.prod_restrict and Pi.add_apply. Indicator bound norm_indicator_le_norm_self requires f v; indicator_of_mem must specify membership in the pair-domain clock sublevel set.

All owned Lean/Lake/search/lint processes terminated successfully or with recorded terminal errors. Cleanup verified: all seven owned /tmp/hb-ci-* paths removed; remaining owned prefix empty. Goal stays active.