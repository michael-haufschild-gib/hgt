# BAG full third-lift Poisson identity

Route: signed physical cubic, full tangential inverse-fibre operator.
Status: dependency-closed paper proof; Lean production and axiom audits pass.
No signed asymptotic saving or RH proof.

Let F be the actual three-coordinate Schwartz amplitude, supported in the
box [a,b]^3. Define the full physical slice

  g_(xi,upsilon)(r) = integral_q integral_p
    exp(-2*pi*i*(p*xi+q*upsilon))*F(p,q,r).

No Mellin, Gaussian, height-window or reciprocal factor is removed from F.
At fixed xi,upsilon restrict the full Fourier transform to the affine line
h(t)=Fourier(F)(xi,upsilon,t). This line has temperate growth and norm at
least |t|; composition therefore makes h a one-dimensional Schwartz map.
Fubini for the volume-normalized Euclidean coordinates gives Fourier(g)=h.
Its absolute integrability is the already proved Schwartz integrability
with a unit-norm Fourier character. This involves no integer series.

The p,q integrals can each be restricted to [a,b] by actual support. The
continuous compact-domain parametric integral theorem applied twice shows
g is continuous. It vanishes for r outside [a,b], so it is integrable.
Since h is Schwartz, Fourier(g) is integrable too. Ordinary Fourier inversion
now identifies g with inverseFourier(h) pointwise, including the endpoints.
This proves the required Schwartz regularity without assuming a parameter
integral differentiability theorem.

Apply shifted Poisson to h at -z. Fourier(h)(-n)=g(n); change n to -n in the
whole integer series. Exactly

  sum_k Fourier(F)(xi,upsilon,k-z)
    = sum_n exp(2*pi*i*n*z)*g_(xi,upsilon)(n).

Every integer lift k remains. Since g(n)=0 outside [a,b], the right side is
the finite sum over ceil(a)<=n<=floor(b). This is an exact physical support
restriction, not a cutoff of near-cone defects. Absolute convergence on the
left follows by restricting the already absolutely summable full shifted
three-dimensional Fourier lattice to k1=k2=0.

Finally use absolute full-lattice summability to write the complete lifted
test as the two outer tangential lift sums, and apply the identity to its
inner third-lift sum. The finite n sum stays inside the two tangential sums;
no unsupported interchange or norm estimate is needed. The existing actual
smooth cutoff family supplies all box conditions and keeps its original
sharp/smooth error at the log^2(N)/N scale. Both literal projectors can still
act on this pointwise equality of full tests.

Remaining hard problem: apply the literal third critical source to these
finite physical heights, retain both tangential profiles and both projectors,
and couple the full growing prime-factor source to the nonzero cone pole
and near-cone/tails at complex norm o(N/log^2 N). Current corpus proves exact
critical prime-log selection on covered integer bands; that selection is
not cancellation. Growing moments, moving cofactors, deterministic common-
height self-return and RH remain open.

## Next exact source contraction

For each first/second atom and each projector translation, move the finite
third-atom sum inside the two remaining lattice sums. Justification uses
absolute summability of each ENTIRE third-lift block, inherited from the
full shifted three-dimensional Fourier series. It does not require moving
an individual physical-height slice outside either lattice sum. Inside the
block, only finite sums over heights and third atoms are exchanged. The
unconditional distinguished-prime multiplier theorem evaluates the result;
on the actual positive integer band it is the exact prime logarithm. The
projector translations contribute the full phase exp(-2*pi*i*n*(u+v)/D),
and retain the two shifted tangential frequencies. This is the next source
coupling conjecture; its formal proof and signed estimate are still open.

## Lean audit — continuation01ai

ChiPrimeGaussianCubicPartialPoisson:263 lines/9 public declarations;
production72166 passes empty. Existing volume-normalized Fubini theorem
Transverse.integral_three is now public; its unchanged proof passes
production10442. Axiom36461 checks all9 plus this helper, standard3 only.
Index21677 completes, all9 and public Fubini appear in LEAN_API; new umbrella
import occurs once. Lint85350 reports28 unreachable modules outside these
changed leaves, all inspected; no proof-debt/new-leaf finding. Global lint
is not clean. No full/umbrella build, numerical computation, limit hack or
subagent. Owned jobs terminal; completed scratch sources removed, logs kept.

Elaboration lesson: broad congr/convert on Fourier maps and summability can
unfold large analytic definitions or expose differing inferred algebra
instances. Explicit coordinate equalities and Summable.congr close the proof
within the original heartbeat limit. Compact-domain continuity plus inverse
Schwartz identification avoids an unproved smooth parameter-integral premise.

Intermittent missing import objects were rebuilt only as needed, serially:
MellinTestFunctionPerron93291, LogPhaseMorseSubstitution11591,
SmoothLogPhaseFresnel11147, ChiRamanujanDampedSquareMellin39960. All passed
empty without source edits. Final axiom audit36461 is successful.

Assessment: full third-lift Poisson is proved for the actual family. The next
hard attack is finite third-prime source contraction inside the remaining
lattice sums, under both projectors, then the full growing signed estimate.
The physical-height sum must stay inside the tangential sums unless a new
summability proof justifies another exchange. Goal remains ACTIVE.


Successor closure (continuation01aj): ChiPrimeGaussianCubicPrimeHeight now
proves the complete finite third-source contraction under both projectors.
Its finite torsion coefficient extraction also proves individual-height
joint absolute summability, so the finite height sum can move outside both
tangential series. See P3 bag-third-prime-height-action and frontier ag.17.
The full prime-factor/signed growing-height estimate remains open.
