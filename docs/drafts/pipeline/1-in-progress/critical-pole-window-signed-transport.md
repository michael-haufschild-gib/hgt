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

The same conjecture tests whether the current R² collar loss is an
artifact. Put `r₁=B_Nv₁−E₁(c_N)v₁` and let Ψ₇ include its dual-seventh
mass divided by E₁. For a terminal test with ℓ(h)≠0, its support lies
entirely in the top collar eventually. Weighted Cauchy–Schwarz and
`c_N⁷E₁(c_N)→J(1)` would then force

    liminf (c_N⁷/L) Ψ₇
      ≥ R² a²ℓ(h)² / [J(1) M₈(H)],   H(y)=exp(y/2)h(y).

Indeed the mixed square is asymptotic to `c_N²a²ℓ(h)²/L`, while the
test's seventh-power collar mass tends to M₈(H). Thus that R² dependence
cannot vanish merely by sharpening the present absolute residual norm,
if the mixed conjecture holds. Paying with the full positive polar
energy changes its denominator to `J(1)+Rag`; the resulting bound still
grows with R. The positive survivor would be the exact joint signed
source–complement problem. This is a conditional consequence to test,
not a proved obstruction while the complete mixed limit remains open.

### Uniformity exposed by the existing conductor bounds

For a fixed bounded terminal window, set
`q_N(m)=|⟨r_m,x_N⟩|²/(c_N E_m(c_N))`, and
`Q_N=floor((log N)^(13/32))`. The following tightness reduction has a
closed paper proof; its Lean transfer is pending.

Choose a collar cutoff below the fixed support of x_N and above
`2 linearPrimeStrip(c_N)`. The window's prefix mass is zero and its
seventh collar mass is bounded. Weighted Cauchy–Schwarz and
`exists_completeWeil_dualSeventh_conductor_residual_log_free` give

    |⟨r_m,x_N⟩|² ≤ C_h m²[c_N²/L+c_N³L/N+c_N¹⁰(L/N)²].

The actual conductor-scale floor, stronger than the common `κ/c_N⁷`
floor, is `c_N⁷ E_m(c_N)≥κm⁷` for `m≤c_N`. Consequently

    q_N(m) ≤ (C_h/κ)[c_N⁸/L+c_N⁹L/N+c_N¹⁶L²/N²]/m⁵.

The bracket tends to R. This supplies one summable envelope for all
conductors below overlap at one eventual horizon. Above overlap,
`E_m(c_N)≥κ`. The public quadratic residual bound has conductor factor
`m(1+log m)²`, so ordinary Cauchy–Schwarz gives

    Σ_(c_N<m≤Q_N) q_N(m)
      ≤ C_h Q_N²(1+log Q_N)²
        [c_N(1+log c_N)³ L^(1/k)/L+c_N⁹(L/N)²] → 0

for any fixed integer k>16. The first power of L is
`−1/16+1/k<0`; powers of log L do not change the limit. The second
term vanishes by the critical-clock polynomial/logarithmic estimates.
Both estimates hold for every fixed R>0. Thus, once the fixed-m mixed
limits are proved, passage through the growing packet needs no new
conductor-uniform prime-distribution conjecture: split at c_N, use
the summable envelope below, and the vanishing total above.

The source floors are
`seventh_mul_completedConductorEnergy_ge_below_overlap` and
`tiltedUnitSpline_completedConductorEnergy_ge_above_overlap`;
the high-conductor norm bound is
`exists_completeWeil_quadratic_conductor_residual_variable_rate`.
Their statements and proofs have been read. The reference diagonal
also has a closed paper bound: the uniform window coordinate is
`|⟨v_m,x_N⟩|≤C_h/sqrt(L)`, while
`completedConductorEnergy_le_logarithmic_uniform` gives
`E_m≤C_φ+2log m+3`, uniformly in c≥1. Hence

    Σ_(m≤Q_N) E_m |⟨v_m,x_N⟩|²/c_N
      ≤ C_h Q_N(C_φ+2log Q_N+3)/(c_N L) → 0.

The Euclidean triangle inequality for these weighted coefficient
vectors transfers tightness from r_m to B_Nv_m. This transfer also
awaits Lean verification. Optimizing against the full signed packet
Gram remains separate; none of these bounds proves whole-space
positivity or removes the window compensation.

## Attack and proof obligations

The exact center row already supplies the two terms
`1/x−½log(1−x²)` in D(log x):
`sum_pole_minus_center_div_sqrt` writes it as a rational pole row plus
`H_N−(H_(N−n)+H_(N+n))/2+3/(4n)`. The upward row at n/N→x
should supply `−ψ(1/x)` through finitely many prime powers. The remaining
Gamma/downward cancellation must supply `−log(2π)`. These are discrete
channels to prove separately, not a replacement of the discrete matrix
by its continuous analogue.

For nonpolar conductors, retain both the full-center coefficient
`−aΛ(m)/sqrt(φ(m))` and the opposite near divisor-jet charge. Their
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
The table separates checked constituents from pending transfers. The
polar full center, signed Gamma remainder and joint near-center finite
part and near logarithm are checked. Complete assembly and general
upward-row transfer still require their Lean audits.

### Checked terminal averaging and center laws

For bounded periodic u,v and a bounded Lipschitz gap kernel K, terminal
endpoint weights preserve the near-pair mean. The weighted near-Gram
error is O((1+log c)/c+c/N); multiplying by log c still gives zero when
c→∞ and c log c/N→0. The shifted periodic harmonic-row bound is uniform
in the gap and subinterval, including empty intervals.

The actual near-center finite part is
`a[m=l][(log 2+γ)∫F+∫F log x]` for m=1 and
`−a[m=l]Λ(m)∫F` for m>1. The joint statement subtracts log c times the
actual weighted near Gram; ordinary convergence does not suffice.
The full polar center retains `∫F(x)[1/x−½log(1−x²)]dx`.

These statements pass actual-path Lean checks with exactly
`[propext, Classical.choice, Quot.sound]` in
`TerminalWeightsReadEitherEndOfANearPair.lean`,
`TerminalNearPairsRetainLogarithmicAccuracy.lean`,
`TerminalWeightsPreserveHarmonicGapRows.lean`,
`TerminalWindowsRetainTheNearCenterFinitePart.lean`,
`TerminalWindowsRetainTheJointNearCenter.lean` and
`TerminalWindowsReadThePolarCenter.lean`.

### Nonpolar center: its receiving charge survives separately

For fixed m≥2 and bounded globally Lipschitz F, the full center divided
by N tends to `−Λ(m)∫F`. The harmonic difference and sum kernels cost
O_(F,m)(H_N/N); the harmonic pole product supplies the surviving charge.
`TerminalWindowsReadTheNonpolarCenter.lean` proves both the center-kernel
mean and literal double-kernel pairing. Its actual-path check uses
exactly `[propext, Classical.choice, Quot.sound]`. The opposite terminal
near-jet charge must cancel before asserting a zero nonpolar source.

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
`TerminalWindowsReadTheNearLogarithm.lean` now proves the logarithmic
transfer and actual terminal near-log limit, with an actual-path check
using precisely `[propext, Classical.choice, Quot.sound]`. The terminal
jet cancellation still needs its Lean audit. The full-center reduction
has passed its actual-path check.

The three signed polar limits combine algebraically to
`−a log(2π)∫F`: the terminal `∫F log x` and Euler constants cancel,
and `log(4π)=log 2+log(2π)`. Their literal sum is implemented in
`TerminalPoleGammaAndCenterHaveOneConstant.lean`; its actual-path audit
passes with exactly `[propext, Classical.choice, Quot.sound]`.

The finite normalization has a closed algebraic reduction. Write
`x_F(n)=F(n/N)/sqrt(n)` and `L=log N`. Then
`sqrt(L)⟨A v_m,x_F⟩` is the literal double sum with denominator
`sqrt(nj φ(m))`; a row normalized by `sqrt(L)` gives the corresponding
single sum. For m=1, the exact Mangoldt divisor convolution is log j.
The identity `log(N/c)+log c+log(j/N)=log j` therefore decomposes the
near row into its Gamma remainder, negative logarithmic near Gram and
negative terminal-log row. Near-center and separated-cross pairings
are their existing literal sums with the same normalization. No
limiting interchange or continuum identification enters this step.
Restoring the completed conductor energy also cancels its shell and
polar diagonals. The remaining scalar is exactly
`selfFinitePart(c)+adjunctionEnergy(m)−γ`; the constant γ must be
retained in the finite identity even though its normalized pairing
vanishes. The finite identities in
`TerminalPolePairingsHaveTheirLiteralChannels.lean` pass their actual-path
audit with exactly `[propext, Classical.choice, Quot.sound]`.

The remaining ratio, self and pole errors have closed paper bounds
against every bounded terminal window. Its norm is bounded uniformly
in N. After squaring the normalization `sqrt(L)/c`, the existing source
bounds become respectively `O_m(c⁻²)`, `O_m(L/N²)` and
`O_m((c⁴L²/N)²)`, all tending to zero at critical scale. For the
reference diagonal, use the stronger window/conductor coordinate
`O(1/sqrt(L))` and the exact scalar `C_m−log c`; its mixed cost is
`O_m((1+log c)/c)`. A physical-norm estimate alone would not pay this
diagonal. All four transfers in
`TerminalWindowErrorChannelsDisappear.lean` pass their actual-path audit
with exactly `[propext, Classical.choice, Quot.sound]`.

### Polar upward-row reduction

There is an exact shorter-window test of the conjecture. If F vanishes
on `[0,δ]` for some δ>1/2, the entire actual upward row vanishes on
F's support eventually, uniformly in conductor m. Indeed take
H=ceil(2c_N). Since H/N→0, `N+H<2n` for every contributing n.
Every prime-power multiple kn with k≥2 then lies above N+H, so both
punctured windows in `upwardModeRow_eq_sum_inner` are empty. The k=0,1
terms have zero Mangoldt weight.
`TerminalWindowsAboveHalfHaveNoUpwardPrimes.lean` proves this exact
annihilation; its actual-path audit passes with precisely
`[propext, Classical.choice, Quot.sound]`. It isolates
the prime-free terminal source without a boundary approximation.
It suffices to test a nonzero ℓ and the proposed intrinsic R² collar
cost before the full finite-prime transfer below is completed.

If F also vanishes for x≥η with η<1, the actual exterior downward
row vanishes on its support eventually, uniformly in m. The existing
linear strip satisfies `linearPrimeStrip(c)≤(e+1)c`; since c_N/N→0,
every contributing n satisfies `n+linearPrimeStrip(c_N)<N`. The exact
regrouping and strip-support theorem then give zero. Thus a profile
supported in a fixed interval `(δ,η)⊂(1/2,1)` removes both prime
boundary channels exactly. This closed paper reduction is implemented
in `TerminalWindowsAwayFromTheHorizonHaveNoExteriorPrimes.lean`;
its actual-path audit passes with exactly
`[propext, Classical.choice, Quot.sound]`. It isolates the local source without
assuming a prime-distribution estimate or a continuum replacement.

For this interior support the polar assembly is now dependency-closed
on paper. The checked finite identity above, the four vanishing error
channels and both exact prime annihilations leave

    (sqrt(L)/c_N)⟨B_Nv₁,x_N⟩
      → a[∫₀¹ F(x)(1/x−½log(1−x²))dx−log(2π)∫₀¹F].

The critical clock implies c_N log(c_N)/N→0, so the checked joint
near-center rate applies. The signed Gamma constant and near-log mean
cancel exactly as stated above. This restriction therefore has no
remaining analytic input in its paper proof; the finite channel
identity and pending supporting Lean proofs still need verification.
`TerminalPolarSourceAboveHalf.lean` contains the exact assembly and
limiting statement. Neither endpoint has passed Lean yet. This does
not settle general terminal support or the nonpolar complete source.

The restricted source has an explicit nonzero paper witness. Take
`δ=127/128`, `η=255/256`,
`F(x)=tiltedUnitSpline((x−δ)/(η−δ))` and `h(y)=F(exp y)`.
This is a nonnegative compact C² window with positive integral.
On its support below one,
`(2π)²(1−x²)<64(1−δ²)<1`, using π<4. Hence

    1/x−log(2π)−½log(1−x²)
      =1/x−½log((2π)²(1−x²)) > 1/x ≥ 1.

Its proposed source mean is therefore strictly positive. This uses
an exact rational inequality, not numerical evidence.
`TerminalPolarSourceIsNonzero.lean` implements this witness as
`F(x)=tiltedUnitSpline(256x−254)`, with the wider guards
`253/256` and `511/512` for the exact prime annihilations. Its first
Lean audit is pending; the resulting collar lower bound also remains
unverified.

For the first lower-bound theorem it suffices to take the collar cutoff
`M_N=floor(N/2)`. The witness has zero prefix there, while
`topCollarSeventhMass(M_N,N,x_N)≤128‖x_N‖²`, uniformly in N.
The checked weighted Cauchy–Schwarz inequality, the positive proposed
source S and the explicit bound `E₁(c)≤C_E/c⁷` then give an absolute
κ>0, independent of R and the clock, such that eventually

    (c_N⁷/L) topCollarDualSeventhMass(M_N,N,r₁)/E₁(c_N) ≥ κR².

Indeed the normalized residual pairing eventually exceeds S/2;
its reference-diagonal correction tends to zero by the uniform window
coordinate bound. If T bounds the seventh collar mass, the same
Cauchy–Schwarz inequality gives the left side at least
`[S²/(8C_E T)](c_N⁸/L)²`, hence κ may be `S²/(32C_E T)`.
This paper reduction uses the explicit conductor-energy upper bound,
so it needs neither a new Jordan asymptotic nor an exact collar-mass
limit. Its unconditional Lean realization still depends on the pending
complete-source and witness audits.

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
