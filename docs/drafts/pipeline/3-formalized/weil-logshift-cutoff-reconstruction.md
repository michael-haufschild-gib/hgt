# First-probe reconstruction on an exact cutoff mesh

Status: FORMALIZED. Dependency-closed paper proof, final leaf compile/export,
all public axiom audits, and global formal lint passed on 2026-10-09.

Mission: recover the information lost by integer-cutoff first-probe sampling.
Sources: only our Lean corpus; no web, external papers, or numerical experiments.

## Corpus audit

- `WeilLogShiftFirstProbeInterpolation.lean`: arbitrary integer-cutoff histories,
  even with divergent signed potentials; integer histories alone cannot control
  local convergence.
- `WeilFinitePanelPositiveCompletion.lean`: K_L(y)>0 iff |y|<2L.
- `WeilTailPanelPositiveCompletion.lean`: exact real paired log-shift kernel.
- `WeilFullConeRiemannKernelRigidity.lean`: compact tests give finite prime-atom
  support and summable prime atoms for arbitrary coefficients.
- `WeilFiniteBlockExcessMass.lean`: finite complex functional-difference proof
  pattern for integer panels; needs adaptation to the finer real cutoff mesh.
- `WeilFullConeExposedPoint.lean`: equality of coefficients at n>=2 implies
  equality of every full functional. No new analytic premise is required.
- `HTGeometry/TriangularCoefficientInjectivity.lean`: finite triangular matrix
  injectivity exists in another setting; natural-number induction is sufficient
  here and avoids an unrelated import.

## Paper proof

Set L_n=(log(n+1)-log 2)/2 for n>=2. Then L_n>0,
log n-log 2<2L_n<=log n. At j=n the paired m=2 test kernel is
-2 K_(L_n)(log n-log 2), strictly negative. For j>n all three autocorrelation
terms vanish, including the boundary j=n+1. Thus the real probe difference at
L_n is a finite sum over 2<=j<=n of coefficient differences times a triangular
weight, with strictly positive diagonal 2 K_(L_n)(log n-log 2)/sqrt n.

If all earlier coefficients agree, this difference is exactly the positive
diagonal times lambda(n)-mu(n). Induction therefore makes equality of mesh
samples through n equivalent to equality of coefficients through n. Full mesh
equality and full positive-real-cutoff equality are each equivalent to equality
of every coefficient at n>=2. The forced invisible coordinates zero and one
are excluded explicitly; no growth, summability, positivity, or RH assumption.

For a direct comparison, realize the integer-cutoff history of von Mangoldt
using the preceding nonsummable-history theorem. The resulting coefficients
agree on every integer sample but cannot agree with von Mangoldt at all n>=2,
since their signed potential is nonsummable. Hence integer sampling is not
injective even modulo the two invisible coordinates, while the fine mesh is.

## Formal result

Leaf: `formal/GaloisForLFunctions/RHTower/WeilLogShiftCutoffReconstruction.lean`.
Three definitions and ten public theorems:

- `weilLogShiftRecoveryCutoff`, `weilLogShiftRecoveryProbe`,
  `weilLogShiftRecoveryWeight`: explicit cutoff, observable, and coefficient matrix.
- `weilLogShiftRecoveryCutoff_bounds`: positive cutoff and strict visibility of
  atom n for n>=2.
- `weilLogShiftRecoveryWeight_eq_zero_of_lt`: exact upper-triangular vanishing;
  valid at every index, without an n>=2 premise.
- `weilLogShiftRecoveryWeight_diagonal`,
  `weilLogShiftRecoveryWeight_diagonal_pos`: explicit positive diagonal for n>=2.
- `weilLogShiftRecoveryProbe_sub`: exact finite coefficient-difference formula,
  valid at every index. Compact support alone discharges summability.
- `weilLogShiftRecoveryProbe_first_difference`: after earlier coefficients
  agree, the next sample difference is the positive diagonal times the next
  coefficient difference.
- `weilLogShiftRecoveryProbe_prefix_iff`: equality of samples through N iff
  equality of coefficients through N, always restricting visible indices to n>=2.
- `weilLogShiftRecoveryProbe_eq_iff`: the full countable mesh determines all
  visible coefficients with no growth, summability, sign, or RH assumption.
- `real_cutoff_firstProbe_eq_iff`: the entire positive-real-cutoff m=2 history
  has exactly the same coefficient-identification power.
- `exists_integer_firstProbe_collision_detected_by_recovery_mesh`: identical
  integer histories can conceal coefficient differences detected by this mesh.

Lean exposed two removable lower-index premises: tail vanishing and the finite
response formula hold even at rows zero and one. Their positive-diagonal and
reconstruction statements correctly retain the visible-index restriction.

## Verification

- Final leaf compile/export: exit 0, no diagnostics.
- All thirteen public declarations: exactly `[propext, Classical.choice, Quot.sound]`.
- Umbrella wired; index refreshed after final compilation; all thirteen API
  entries inspected.
- `scripts/formal_tools.py lint`: exit 0, `formal lint passed`. Earlier unrelated
  missing-import reports are superseded by this successful gate.
- Initial elaboration fixes concerned repeated conditional rewrites and local
  definition unfolding; final cleanup removed unused index premises.
- No external sources, numerical experiments, new analytic premises/axioms,
  heartbeat increases, umbrella builds, commits, pushes, or subagents.

The rejected integer-cutoff recovery route and this positive survivor are
recorded in `../5-failed/weil-logshift-integer-cutoff-injectivity-no-go.md`.

Follow-up: `WeilLogShiftRecoveryHomeomorphism.lean` now supplies the explicit
triangular inverse for every real history, unique after fixing coordinates zero
and one. Both directions are continuous for coordinatewise convergence, and
the result is packaged as a homeomorphism. All twelve public declarations
compiled and passed axiom audits. See `weil-logshift-recovery-homeomorphism.md`;
its global lint snapshot has one unrelated unwired module. No uniform-norm
stability or coefficient-growth bound has been proved.
