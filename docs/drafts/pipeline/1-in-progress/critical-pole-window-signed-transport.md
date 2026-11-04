# Signed transport between the critical pole and a terminal window

- **ID:** critical-pole-window-signed-transport
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Parent:** [critical-ratio continuation](critical-ratio-continuation.md)

## Exact conjecture

Let L=log N, c_N≥1, c_N⁸/L→R>0, B_N the complete tilted-spline
matrix, v_m its normalized Ramanujan horizon vector and
x_N(n)=h(log n−log N)/sqrt(n). Assume h is C² and supported in [-A,0].
Set a=(∫φ)²/∫φ² and, for y<0,

    D(y)=exp(-y)−ψ(exp(-y))−log(2π)−½log(1−exp(2y)),
    ℓ(h)=∫_(-∞,0) exp(y) h(y) D(y) dy.

The boundary logarithm is locally integrable; compact support and
continuity of h make this integral well-defined. The proposed exact
mixed limit is

    (sqrt(L)/c_N) ⟨B_N v_m,x_N⟩ → a ℓ(h) [m=1].

The limit is conjectured to be independent of R. In particular, it
contains no surviving aliasing term. **[OPEN CORE]** Prove or refute
that assertion for the literal discrete pole–window pairing. A continuum
calculation does not justify it.

## Source, not an analogy

`ccmRestrictedWeilOperator_polarPlus_coeFn` in
`RHTower/CCM/CCMRestrictedWeilPolarSourceCancellation.lean` identifies
the actual finite-aperture pole image. After translation x=y+a₀ and
normalization by exp(-a₀/2), its interior coefficient is

    exp(y/2)[κ+B(-y,2a₀+y)
               −(ψ(exp(-y))−exp(-y))−E_M(2a₀+y)]
      −exp(-2a₀)exp(-y/2),

where κ=−γ−log(2π),
B(r,l)=−½log(1−exp(-2r))−½log(tanh(l/2)), and
E_M(t)=Σ_(n≤exp t)Λ(n)/n−t. The existing Mertens limit is E_M→−γ.
At every fixed y<0 this expression tends to exp(y/2)D(y).
Pairing with H(y)=exp(y/2)h(y) gives exactly ℓ(h).

This continuous source identity and the critical fixed-conductor
residue have both been inspected in Lean. No theorem transferring this
half-line source to the discrete critical mixed form has been found
in the targeted corpus searches. That is a search result, not an
exhaustive absence claim.

## Consistency check and competing failure

The proposed source has the correct polar mass:

    ∫_(-∞,0) exp(y) D(y) dy = 2+γ−log(4π)=g.

Indeed, partial summation gives
∫₁ˣ(t−ψ(t))/t² dt=log X−Σ_(n≤X)Λ(n)/n+ψ(X)/X→γ+1.
The boundary integral is 1−log 2, and the remaining constant contributes
−log(2π). This is a paper consistency calculation, not a new checked
Lean endpoint. It matches the already checked positive polar genus.

The principal competing possibility is an additional R-dependent
functional from the discrete high-frequency tail. The mixed aliasing
integral with a compact h would be finite even though the pole's self
aliasing integral diverges. Neither fact justifies applying the compact
window theorem to the full pole.

The actual discrete source gives a stronger reason to test cancellation.
`nearGammaDownwardCoefficient` subtracts the full Mangoldt divisor
convolution. At conductor one this is exactly log j, so, writing q for
the shell autocorrelation divided by atom mass, its coefficient is

    [archPair−log(N/c)q]−[log c+log(j/N)]q.

Thus the large log N cancels before any terminal pairing or estimate.
This identity uses all quotient indices j/d of the pole; truncating that
pole to a compact window destroys the divisor identity. The same
decomposition retains the divisor jet for general conductor m, as shown
by `nearGammaDownward_add_nearCenter_row_eq` in
`LogarithmFreeCriticalConductorResiduals.lean`. This is source support
for the conjecture, not the missing complete weighted limit: all
replacement and boundary terms still require their stated estimates.

Test m=2 separately. Cancellation against every fixed conductor does not
by itself exclude a nonpolar boundary source detected by a terminal
window. If such a source survives, retain its exact profile and replace
the proposed rank-one conclusion by the resulting charge space.

## Mathematical payoff

The checked pole energy gives

    (L/c_N)⟨B_Nv₁,v₁⟩ → J(1)/R+a g.

If the mixed conjecture holds, the exact two-dimensional limit for
x_N+t sqrt(L)v₁ is

    a Q(H)+(7J(1)/R)M₈(H)+2t a ℓ(h)+t²[J(1)/R+a g].

Thus the WIP's all-vector positivity on its established small band
would imply the stronger window bound

    a Q(H)+(7J(1)/R)M₈(H)
      ≥ a²ℓ(h)²/[J(1)/R+a g].

This does not extend the known band or remove compensation. It computes
the actual energy benefit of the growing pole corrector, which
orthogonal projection does not measure. The next stronger question is
whether all energy-optimal correctors in the growing conductor packet
reduce to this one source functional, or retain further arithmetic
charges. Pointwise mixed convergence alone cannot settle that question;
an inverse-energy summable envelope is required.

There is a sharp limit to this mechanism. If the uniform optimized
correction is exhausted by ℓ, it changes the window form by one rank-one
term. On ker ℓ the full aliasing mass remains. Thus even that stronger
rank-one theorem would not remove compensation on all windows; a proof
would still need further growing arithmetic charges or direct control
of the complementary window form.

## Attack and proof obligations

The exact center row already supplies the two terms
`1/x−½log(1−x²)` in D(log x):
`sum_pole_minus_center_div_sqrt` writes it as a rational pole row plus
`H_N−(H_(N−n)+H_(N+n))/2+3/(4n)`. The upward row at n/N→x
should supply `−ψ(1/x)` through finitely many prime powers. The remaining
Gamma/downward cancellation must supply `−log(2π)`. These are discrete
channels to prove separately, not a replacement of the discrete matrix
by its continuous analogue.

For nonpolar conductors, retain both the harmonic receiving charge
`−Λ(m)/sqrt(φ(m))` and the opposite near divisor-jet charge. Their
weighted cancellation must be established before claiming a zero source.

For conductor one, put F(x)=h(log x), extended by zero outside (0,1),
and read raw pairings after division by c. The discrete channel limits
needed for the conjecture are:

| Channel | Proposed limit |
|---|---|
| Full center | a∫F(x)[1/x−½log(1−x²)]dx |
| Near Gamma remainder minus separated cross | −a(log(4π)+γ)∫F |
| Near logarithmic row | −a∫F(x)log x dx |
| Near center minus log c times near Gram | a∫F(x)[log(2x)+γ]dx |
| Upward prime row, entering negatively | a∫F(x)ψ(1/x)dx |
| Remaining diagonal, ratio and replacement terms | 0 |

The middle three rows sum to −a log(2π)∫F. Since F is supported
away from zero, only finitely many prime powers occur in the proposed
upward limit. This is a finite-prime transport problem at the terminal
window, not a use of the large-horizon upward asymptotic there.
The table is a proof decomposition, **not** an established collection
of limits. In particular, weighted harmonic-center cancellation and
transfer of the actual upward rows remain open.

### Closed auxiliary argument: terminal weights in a near-pair mean

For bounded periodic u,v, a bounded Lipschitz gap kernel K on [α,β],
and a globally bounded F Lipschitz on [0,1], the proposed auxiliary
theorem is

    nearPairSum(K,α,β,c_N/N,N,u,v,F(·/N))/c_N
      → 2 mean(u)mean(v) (∫_α^β K) (∫₀¹ F),

under c_N>0, c_N→∞ and c_N/N→0. Here F weights the smaller
index. The existing arbitrary-weight row estimate has error
`O_F(1+log c_N+c_N²/N)`. Dividing by c_N makes it vanish.
Its main term is

    (∫_α^β K(s)exp(c_N s/(2N))ds)
      · (1/N)Σ F(n/N)[u(n)mean(v)+v(n)mean(u)].

The first factor tends to ∫K uniformly on the fixed gap interval;
the proved periodic weighted Riemann theorem gives the second limit.
This closes the auxiliary paper argument without a new arithmetic input.
It extends one existing channel to terminal tests; it neither settles
the aliasing cross term nor the complete mixed conjecture. Lean
formalization now checks in `TerminalWeightsPreserveThePolarNearMean.lean`
with `[propext, Classical.choice, Quot.sound]`, including its final
actual-path no-olean audit.

The same limit holds with F(n/N) on either endpoint. On a contributing
pair, `|n−j|/N≤|log n−log j|≤βc_N/N`, so replacing the smaller-index
weight by an endpoint weight changes it by at most `Lip(F)βc_N/N`.
The bounded-kernel pair mass is O(c_N). After division by c_N the
error tends to zero. This supplies the orientation needed for the
literal mixed form; it does not use positivity of that form.
`TerminalWeightsReadEitherEndOfANearPair.lean` passes its final actual-path
no-olean audit with the standard three axioms.

The next closed auxiliary argument retains F in the actual Gamma pair:

    [nearRemainder(Fu,v)−farCross(Fu,v)]/c_N
      → −a(log(4π)+γ) mean(u)mean(v) ∫₀¹F.

On each fixed scaled-gap interval, the proved entry replacement has
O(c_N/N) error, the pair mass is O(c_N), and the endpoint-weighted
mean applies. Beyond a scaled gap T, the existing tail estimate is
`O_F(c_N/T+c_N²/N)`, uniformly in N. Divide by c_N, first take
N→∞, then T→∞. The existing exact near/far profile integral supplies
the displayed constant. The tail estimate accepts bounded arbitrary
weights, so inserting F(n/N) requires no periodicity of the product.
The weighted transfer now passes its actual-path no-olean check in
`TerminalWindowsRetainTheSignedGammaMean.lean`, with exactly
`[propext, Classical.choice, Quot.sound]`. It holds for bounded periodic
u,v and bounded Lipschitz F under only c_N>0, c_N→∞ and c_N/N→0.
It establishes the Gamma row of the channel table, not the complete
mixed limit.

### Near-center reduction

For bounded Lipschitz F vanishing on [0,δ], δ>0, put d_N=exp(2c_N/N)−1.
The weighted near center has the following reduction:

    nearCenterPair(c_N,N,F(·/N)c_l,c_m)/N
      − [m=l](1/N)Σ_(n≤N) F(n/N) lagHarmonic(m,floor(d_N n)) → 0.

Order the pairs by their positive integer gap j. Moving F from the
larger endpoint to the smaller costs O_F(c_N/N). On each gap row,
bounded periodic primitives and Abel summation replace the Ramanujan
product by its exact mean `2[m=l]c_m(j)` with error O_(F,m,l)(1).
Summing against 1/j and dividing by N costs O_(F,m,l)(log(1+c_N)/N).
Removing the top restriction n+j≤N deletes at most j terms for each
gap; its total normalized cost is O_(F,m,l)(c_N/N). Interchanging the
remaining finite sums gives the displayed harmonic sum. The near sum
kernel is also O_(F,m,l)(c_N/N).

On F's support, d_N n→∞ uniformly and d_N N/c_N→2. Thus the existing
harmonic finite parts give, after subtracting `[m=l=1] log(c_N)∫F`,

    [m=l=1] ∫₀¹F(x)[log(2x)+γ]dx
      − [m=l>1] Λ(m)∫₀¹F(x)dx.

The Riemann-sum error multiplied by log(c_N) vanishes since it is
O_F(log(c_N)/N). This derives the required local logarithm before
cancellation with the logarithmic row; substituting the unweighted
constant log 2+γ−1 would lose F's profile.

This finite-part statement now passes its final actual-path check in
`TerminalWindowsRetainTheNearCenterFinitePart.lean`, with exactly
`[propext, Classical.choice, Quot.sound]`, under only c_N>0,
c_N→∞ and c_N/N→0. Combining it with the actual near-Gram subtraction
still requires a terminally weighted near-Gram error small after
multiplication by log(c_N).

Its paper reduction follows directly from the existing weighted near-pair
row estimate. For a fixed bounded Lipschitz kernel K and periodic u,v,
the normalized error is O((1+log c_N)/c_N+c_N/N). The row integral differs
from ∫K by O(c_N/N), and the weighted periodic Riemann mean differs from
its limit by O(1/N). Moving the weight to either endpoint costs O(c_N/N).
Hence multiplication by log(c_N) still gives zero when c_N→∞ and
c_N log(c_N)/N→0. The required fourth-order logarithmic clock implies
this condition. `TerminalNearPairsRetainLogarithmicAccuracy.lean` now
passes its final actual-path no-olean audit with the standard three
axioms. The literal joint subtraction is
implemented in `TerminalWindowsRetainTheJointNearCenter.lean` and awaits
its own audit. Plain convergence of the weighted near mean would not
supply this rate.

The uniform weighted gap-row estimate now passes its actual-path check
in `TerminalWeightsPreserveHarmonicGapRows.lean`, with the standard
three axioms. It includes every integer interval, including empty ones;
the error is independent of the gap and interval length.
`TerminalNearCenterHasAHarmonicModel.lean` now checks the complete weighted
near-center reduction above with those same axioms. The quantitative
error is O_(F,m,l)(harmonic(N)/N+exp(2c_N/N)−1), so the approximation
needs only c_N>0 and c_N/N→0. Its final actual-path no-olean audit also
passes with the standard three axioms.

`TerminalHarmonicMeansRetainTheirFiniteParts.lean` also passes its final
actual-path check with the standard three axioms. For any scale a_N→∞,
it proves the terminal average of
`lagHarmonic(m,floor(a_N n/N))−[m=1]log a_N` tends to
`[m=1]∫F(x)(γ+log x)dx−[m>1]Λ(m)∫F`.
The subtraction occurs inside the finite sum, so this auxiliary theorem
needs no growth-rate relation between a_N and N.

### Full polar-center reduction

The exact row `sum_pole_minus_center_div_sqrt` reduces this channel to

    (a/N)Σ F(n/N)[N/n+H_N−(H_(N−n)+H_(N+n))/2+3/(4n)].

The source theorem `HTGeometry.abs_harmonic_sub_log_sub_eulerMascheroni_le`
gives `|H_k−log k−γ|≤1/k` for k≥1. For n<N, replacing the three
harmonic numbers by their logarithms leaves a weighted error O_F(1/N)
per summand: `|F(n/N)|≤Lip(F)(N−n)/N` pays the apparent singularity
`1/(N−n)`, while F vanishes for n≤δN. The n=N term is zero because
F(1)=h(0)=0. The normalized total error is O_F(1/N).

The resulting function
`F(x)[1/x−½log(1−x²)]`, defined as zero at both endpoints,
is continuous on [0,1]. At x=1, this follows from
`(1−x)log(1−x²)→0`; at x=0, F vanishes on a neighbourhood.
Its Riemann sums therefore converge to the full-center integral in the
channel table. `TerminalWindowsReadThePolarCenter.lean` proves both the
weighted row limit and its literal double-kernel version. Its final
actual-path no-olean audit passes with exactly
`[propext, Classical.choice, Quot.sound]`.

### Nonpolar center: the receiving charge survives separately

For m≥2 and bounded Lipschitz F on [0,1], the proposed full-center limit is

    (1/N)Σ_(n,j≤N) F(n/N)c_m(j)
      [poleKernel(n,j)−centerKernel(n,j)]/sqrt(nj)
        → −Λ(m)∫₀¹F.

The paper reduction is closed. The exact pole-gauged center kernel is
½[1/|n−j|+1/(n+j)] off the diagonal. On each difference-gap row, periodic
mean zero and weighted Abel summation bound both orientations uniformly
in the gap, including the shifted terminal weight. Summation against
1/gap and division by N costs O_(F,m)(H_N/N). For the sum kernel, the
shifted harmonic Abel bound gives O_m(1/(n+1)) per row; deleting its
diagonal has the same total O_(F,m)(H_N/N) cost. Both center terms vanish.

The two pole products are exactly
`lagHarmonic(m,N)·(ΣF(n/N)/N)` and
`lagSum(m,N)·(ΣF(n/N)/n)/N`. The second vanishes by the bounded partial
sum estimate; the first tends to the displayed charge by the checked
`tendsto_lagHarmonic` and Lipschitz Riemann estimate. Thus the full center
alone is not zero at m=2. Its charge must cancel the opposite near
divisor-jet mean, whose exact finite conductor lowering is already
proved in `TheDivisorJetHasAPolarNearMean.lean`. The terminal transfer
of this nonpolar full-center argument remains to be formalized.

### Terminal logarithm and divisor-jet cancellation

On a near pair, the exact identity
`log(j/N)−log(n/N)=log j−log n` bounds its absolute value by 2c_N/N.
Thus moving the logarithm to the terminal endpoint costs at most
`O_F(c_N/N)` times the normalized bounded-kernel pair mass, which has
a finite limit. The endpoint mean for `logProfile(y↦yh(y))` then gives
the near logarithmic row in the table, with its negative sign supplied
by the downward-row identity. This argument needs only c_N→∞ and
c_N/N→0 and has no singularity at zero because h has compact log support.

The divisor jet is bounded and periodic, with mean Λ(m). The same
endpoint theorem therefore gives its terminal near mean
`a Λ(m)∫F`, exactly opposite to the nonpolar full-center charge.
These are closed paper reductions using the actual divisor-jet mean;
the logarithmic transfer and terminal jet cancellation still need Lean
audits. `TerminalWindowsReadTheNonpolarCenter.lean` contains the
full-center reduction and awaits its first check.

### Polar upward-row reduction

The conductor-one upward row has a closed paper reduction for the same
F, under c_N≥1, c_N→∞ and c_N⁴(log N)²/N→0:

    (1/c_N)Σ_(n≤N) [F(n/N)/n] upwardModeRow(φ,c_N,N,1,n)
      → a∫₀¹ F(x)ψ(1/x)dx.

Use the existing row comparison with H_N=ceil(2c_N) and its parameter
1/(2c_N). Retain `upwardBoundaryMass` instead of its logarithmic
majorant. On F's support n≥δN; every boundary prime power then satisfies
k≤2/δ once H_N≤N. For each such k the boundary condition allows at most
2H_N/k+1 values of n. Its weighted normalized contribution is therefore
O_(F,δ)(c_N/N). The remaining row-comparison error is
O_(F,φ,δ)(c_N³ log(4c_N)/N), which also vanishes.

In the affine-shell model, the conductor-one coefficient is identically
one. The Lipschitz Riemann estimate for the compact autocorrelation gives

    upwardShellModel(φ,c_N,N,1,H_N,kn)
      = a c_N kn/N + O_φ(1)

uniformly for δN≤n and kn≤N. Hence only finitely many k≤1/δ remain,
and the normalized model is `(a/N)Σ F(n/N)ψ(N/n)+o(1)`.
Swap those finite prime-power sums before taking the Riemann limit:
each k contributes `Λ(k)∫₀^(1/k)F`. This avoids any unjustified
uniform estimate across the jumps of ψ. The argument uses only the
actual row comparison and finite sums; its Lean transfer is pending.
Nonpolar upward sources still require their separate periodic audit.

The exact affine selection rule already exists in
`SuccessorShellArithmetic/Conductor/AffineShellConductorSelection.lean`:
over a common period, the correlation of c_l(n) and c_m(kn+j)
equals c_m(j) times the period length precisely when
`l=m/gcd(m,k)`, and is zero otherwise. For the untwisted terminal
receiver l=1, only m dividing k survive. Since the terminal support
restricts k to a fixed finite set, its upward mean sees only finitely
many conductors; for general fixed l, the selection forces m≤kl.
These are consequences of the existing exact finite identity, not a
new prime-distribution hypothesis. The remaining uniform problem is
to control incomplete weighted periods and boundary errors before
summing a growing packet. Averaging first in the long terminal index
can do this without assuming m≪c_N; averaging first in the short
gap would impose that unnecessary restriction.

- Verdict: `BRIDGE` candidate. The continuous pole action is existing
  corpus mathematics; the proposed discrete mixed transport is the gap.
- Check the scale sqrt(L)/c_N and every atomic normalization directly.
- Retain both prime directions, the near/far Gamma cancellation, the
  center term and both pole moments before estimating.
- Isolate the discrete aliasing cross term and determine its limit.
- Only after these steps, prove and formalize the exact mixed limit,
  then its uniform inverse-energy version if it survives.
- No external novelty claim. The complete mixed limit and any resulting
  strengthened window inequality remain unproved.
