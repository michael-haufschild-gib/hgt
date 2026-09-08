# CCM-FU: coarea mass-envelope selection

- Status: monotone greedy candidate rejected by independently audited numerical evidence;
  fixed-slope transport, actual initial slope growth, and general prime dissipation kernel checked.
  Numerical rejection is not a Lean counterexample.
- Type: derived selection candidate and diagnostic experiment, not a primary universal conjecture.
- Chain: actual source → exhaustive prime order with quadratic energy ceiling → O(M) Abel sum → CCM-FU → RH.
- Frontier map read only. No unconditional selection theorem is asserted.

## Frozen candidate

For each actual retained prime-factor cell R, retain both its signed mass
`F_R=Σ C_d` and original absolute mass `A_R=Σ |C_d|`. Define

    J(P)=Σ_R F_R²/A_R,
    m(P)=max_R A_R,
    B(P)=m(P) J(P),

with zero-mass cells contributing zero. Then `Q(P)≤B(P)`. At the empty
processed set, `B=mU=O(M²)` by the uniform channel ceiling and the
absolute-mass upper bound. At complete processing, `B=(Σ C_d)²`.
Coarea makes J nonincreasing, whereas m is nondecreasing. The candidate
is that choosing a prime minimizing the next B permits every step to be
nonincreasing on the actual source. This candidate is stronger than a
uniform peak bound, and a failure of monotonicity will not refute that
separate peak bound.

The reason to test this quantity is specific: raw-energy greedy paths
have transverse traps, while plain probability-normalized energy loses
a factor M. B keeps the changing cell mass that the latter estimate
omits. These facts do not imply the candidate. Its truth is uncertain.

## Frozen diagnostic

- Cutoffs: 512, 1024, 2048, 8192; four independent worker processes.
- Begin with P empty and the complete literal divisor source.
- At every step consider every unprocessed prime below M.
- Choose the smallest next B, with increasing prime as tie breaker.
- Continue through every prime, including after a strict positive step.
- Record the first strict trap, every selected prime, all B values,
  raw energy, J, largest cell mass, terminal signed sum, and peak B/B₀.
- A strict trap means the smallest gain exceeds `1e-10 max(1,B₀)`.
- Independently audit the first strict trap at the smallest cutoff, if
  found, using 80-digit arithmetic and the original time-sum source.
- Stop the screen after 90 seconds and the audit after 90 seconds.
- Run only on the supplied RunPod. Download scripts/results; remove
  owned remote jobs and temporary files. Numerical evidence is guidance,
  never a Lean certificate.

For a prime q, merge cells r and qr. If their masses and signed values
are `(a,x)` and `(b,y)`, the exact decrease of J is
`(b x-a y)²/(a b(a+b))` when a,b>0. The largest new cell mass is the
maximum of the old largest mass and all a+b. This permits scoring all
primes from the affected cells without rebuilding the source for each
candidate. Recompute selected-state quantities directly after merging
to check the scoring identity.

## Prior corpus checks

Broad OR searches included mass/variance, signed coupling, coarea,
conductance, entropy, parity balance, and maximum-cell comparisons.
`RouteEPhysicalFibreCoarea` supplies exact conditional-energy loss;
`MobiusDivisorPositiveNormalizationCost` supplies the sharp initial
normalization cost. `RouteEOppositeParityMetropolisRejection` and
`MobiusBoundaryOppositeSignTransport` need a quantitative accepted-flow
or Hall-capacity estimate; full opposite-sign transport's optimum is
the original signed imbalance. `RouteECofactorUnsignedMass` supplies
unsigned mass in both parity classes, not the required critical
equidistribution rate. None determines the experiment's outcome.

## Positive survivor: a fixed slope along the late-prime mass direction

The screen found positive steps at all four cutoffs. An independent
80-digit audit confirmed the first trap at M=512 and every preceding
greedy choice. The following exact algebra does not depend on those
numerical signs and has a dependency-closed paper proof.

Write `a=A_empty`, `f=F_empty`, and `K=Σ_{R≠empty} F_R²/A_R`.
Define head action `H=f²+aK` and slope `g=K-a-2f`.
For an available prime p with `M≤2p`, the only source index containing
p is p itself. Its coefficient is nonpositive. Put `b=|C_p|`.
Processing p therefore gives

    (a,f,K) → (a+b, f-b, K-b).

The last identity retains every other cell and uses `C_p²/|C_p|=|C_p|`,
including the zero-coefficient case. Consequently

    g(P union {p}) = g(P),
    H(P union {p}) - H(P) = b g(P).

For every finite fresh late-prime block L, the same identity iterates:
`H(P union L)-H(P) = (Σ_{p∈L}|C_p|) g(P)`, and g is unchanged. Thus
the increment depends only on total mass, not on the order of L. If
`a` is already the largest cell mass, it remains largest under these
mergers and B equals H throughout. Every nonzero late-prime step then
has the sign of the same fixed g. A positive g cannot be repaired by
choosing a different late prime, consuming smaller late masses, or
batching them; a negative g gives monotone processing of the entire
fresh late block in every order.

This is a sharp direction classification, not an exhaustive prime-order
theorem. Reorienting g requires a merger that changes nonempty mixed
cells. That is a concrete obligation on the unresolved small/middle front.

## Actual source forces a growing positive initial slope

This statement uses no numerical evidence. Let T(M) be the positive
mass of primes in `(M/2,M]`. At M=4N every active such prime is isolated
and remains outside P={2}. Therefore `K(4N,{2})≥T(4N)`.
The head at P={2} contains only original source indices 1 and 2, so
`a≤(6/5)sqrt(M)`. Since `f≤|f|≤a`, the exact slope satisfies

    g(4N,{2}) ≥ T(4N) - 4 sqrt(4N).

The existing prime-window theorem gives `T(4N)/(4N)→+∞`. The displayed
bound proves `g(4N,{2})/(4N)→+∞`. Thus sufficiently large cutoffs have
positive actual slope after the very first prime, and no later block
of isolated late primes can reverse it. This is an unconditional
source-growth law, rather than only a sign observed at the numerical trap.

## General dissipation of the same slope

The fixed late-prime slope is part of a stronger monotonic law. For any
available prime q, let `b=A_{q}` and `h=F_{q}` before insertion. Pairwise
conditional Cauchy, applied to every nonempty complementary pair,
gives `K(P union {q})≤K(P)-h²/b`. Head updates are `a→a+b` and
`f→f+h`. Thus

    g(P)-g(P union {q}) ≥ (h+b)²/b ≥ 0.

Zero b forces zero h and contributes zero. The retained transverse
conditional variances give the remaining nonnegative loss. Therefore
all prime mergers dissipate g; isolated pure negative cells saturate
the zero-loss case. This supplies an exact quantity for selecting a
mixed-cell reorientation, rather than judging only the immediate B
increment. It does not yet bound how much absolute head mass must be
collected before g becomes nonpositive. The argument is kernel checked
without numerical input as `mobiusDivisorCoareaHeadSlope_insert_loss_ge`
and `mobiusDivisorCoareaHeadSlope_insert_le`.

A rule that postpones all isolated late primes until after completing
the half-prime core is already ruled out by the actual intermediate-head
growth theorem in `MobiusDivisorLatePrimeHeadAsymptotic`. Monotonicity of
g alone does not justify such an order. A successful schedule still needs
joint control of slope dissipation, head growth, and late-prime use.

## Screen result and scope

The complete-prime greedy screen at M=512,1024,2048,8192 gives peak B/B₀
of 2.253066, 4.061134, 6.679569, and 21.898473 respectively; the corresponding
raw-energy peak ratios are 1.262507, 2.314992, 3.892479, and 15.800353.
The finite data reject monotonicity, but do not prove an asymptotic
failure of every fixed quadratic envelope or of every prime order.

At M=512 the audited greedy prefix is `2,479,509`. Every remaining
prime increases B; the smallest increase, at 503, is approximately
0.71767451228624735. The receiving mass has nearly reached the largest
background cell, and the 503 merger makes it largest. The invariant
head-action slope is approximately 63.50466829 from prime two onward
through these late-prime steps. Full scripts, results and audit are
[archived with the computation](../2-fully-proven/computations/ccm-fu-coarea-mass-envelope-2026-09-08/README.md).

Both numerical stages ran on RunPod with four workers, in 6.666 and
0.481 seconds, under separate 90-second deadlines. Numerical results
were downloaded and owned remote jobs/files removed.

## Formal positive survivor

The three new leaves are
[MobiusDivisorCoareaHeadTransport](../../../../formal/GaloisForLFunctions/RHTower/MobiusDivisorCoareaHeadTransport.lean)
and [MobiusDivisorCoareaInitialSlopeGrowth](../../../../formal/GaloisForLFunctions/RHTower/MobiusDivisorCoareaInitialSlopeGrowth.lean),
plus [MobiusDivisorCoareaSlopeDissipation](../../../../formal/GaloisForLFunctions/RHTower/MobiusDivisorCoareaSlopeDissipation.lean).
They contain twelve exact cell/block/action theorems, four actual
source-growth theorems, and four general prime-dissipation theorems.
The block theorem is
`mobiusDivisorCoareaHead_late_block`; the source capstone is
`tendsto_mobiusDivisorCoareaHeadSlope_two_div_atTop`.

The proof keeps every actual source cell and handles zero-mass terms
explicitly. Favourable head dominance and nonpositive slope appear as
explicit conditions where needed; the source-growth capstone has no
such premises and supplies the eventual opposite sign after prime two.
An exhaustive order controlling the intervening mixed-cell transitions
remains unproved. RH remains open.

## Verification

All three scratch proofs and installed leaves passed `lake env lean`.
Only their required oleans were emitted. Each of the twenty new public
theorems was audited once in external scratch files; all depend only
on `propext`, `Classical.choice`, and `Quot.sound`. No old theorem was
re-audited and no computation result enters these proofs.

Final exact-module `lake build` audits passed sequentially in an isolated
temporary package containing byte-identical sources and this repository's
toolchain. Empty-glob cache dependencies exposed existing oleans without
dependency-source targets. Head transport compiled in 5.8 seconds, initial
slope growth in 7.0 seconds, and general slope dissipation in 4.6 seconds.
Only these three new modules were compiled. Initial cache-package manifest
warnings were packaging warnings; the Lean leaves produced no warnings.

All three leaves are imported by RHTower. No full or umbrella build ran.
Indexes were regenerated. Global formal lint currently fails solely on
three unrelated modules missing umbrella reachability:
`SelbergMaassAugmentedDirection`, `SelbergMaassChordEnergy`, and
`SelbergWeightedPathEnergy`. Those files were not edited here. Thus no
passing global lint gate is claimed. Own documentation links, source
copies, import wiring, and whitespace checks passed.

Owned scratch files and the temporary audit package were removed, with
no owned Lean process left running. Owned RunPod artifacts were downloaded
and the remote temporary directory removed. The frontier map was kept
read-only. The RH goal remains active and unachieved.
