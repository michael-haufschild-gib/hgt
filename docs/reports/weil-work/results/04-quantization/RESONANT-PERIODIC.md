# Resonant periodic phase rigidity — candidate L1

Status: dependency-closed paper argument below; **NOT YET LEAN VERIFIED**.
Verdict: **SURVIVES PRELIMINARY ATTACK**. Scientific novelty remains provisional.
The general almost-periodic conjecture L and the full WP04 target remain open.

## Exact statement

Write R for `((∀ n≥2, lam n = Λ n) ∧ RiemannHypothesis)`. Let hW be any
`WeilPositiveFull lam`, ν its actual integer-floor residual measure,
`C(x)=ν((0,2x])`, and `W(x)=exp(2πi C(x))` for x>0.

For every integer q≥2, there is no sequence `(p_k)_{k∈ℤ}` satisfying

1. `Σ_k |p_k| q^{|k|}<∞`, and
2. `W(x)=Σ_k p_k exp(2ik(log q)x)` for every x>0,

unless R holds. The final source-only formulation is R or failure of every
such representation. No periodicity or representation is asserted to follow
from hW. The theorem concerns the actual phase, including trace zeros.

New proposed mechanism: arithmetic resonances on one q-power chain produce a
Toeplitz equation with a prescribed geometric right side. Positive winding
annihilates its left side but cannot annihilate its right side. This retains
all harmonics, including infinitely many resonant negative harmonics.

## Attack and parent audit

A generic nonconstant analytic circle-valued periodic function is not a
counterexample: it does not supply the actual positive arithmetic source.
Conversely, bounded oscillation of a periodic argument is not a variation
bound. Existing nonresonant AP receivers explicitly exclude the rational
resonances retained here and supply a continuous critical-edge completion.
Neither restriction is used below. A dilation expansion of λ or a bounded
ζ quotient has not been assumed.

The factorization and range-obstruction part is classical Wiener–Hopf
theory, not a novelty claim. Relevant inspected primary sources:
[Câmara, 2017](https://arxiv.org/abs/1710.11572),
[Câmara–Malheiro–Partington, 2021](https://link.springer.com/article/10.1007/s00025-020-01323-z),
and [Nolasco–Castro, 2006](https://arxiv.org/abs/math/0511127).
These do not by themselves give the canonical arithmetic coupling used here.
No claim of exhaustive external absence is made.

Two fresh deep corpus searches for periodic locks and Toeplitz factorization
returned partial results: respectively 68,496 and 68,495 indexed files,
with semantic retrieval unfinished (the periodic query also left judging and
decomposition unfinished). All returned candidate and source-argument rows
were inspected. No applicable stronger source theorem was identified.

## 1. Actual-source inputs

Set `a(n)=dirichletExp(lamLog lam)(n)`, G the canonical completion,
`κ=quantizationOriginPhase hW`, and F its uncompleted analytic product.
The previously audited corpus gives:

- `a(1)=1`, `Σ_{n≥1}|a(n)| n^{-3/2}<∞`, and `F(s)=Σ a(n)n^{-s}` on Re s>1.
- F is holomorphic in the lower part of the open strip 1/2<Re s≤3/2,
  polynomially bounded uniformly there. Its measurable radial trace f(y)
  exists pointwise and is bounded on compact intervals away from the pole
  factors. Compact integrals converge by the actual right majorant.
- The reflected trace satisfies `f_ref(2t)=κ W(-t) f(2t)` a.e. for t<0.
  Here |κ|=1, and the positive-integer lower-half radial residue is G(1),
  after multiplying the defect-Laplace normalization by 2π. G(1)≠0 because
  1 lies inside the open domain of the exponential completion.
- ν is locally finite and positive; every singleton mass lies in [0,1).
  Its cumulative function is monotone, right-continuous and has jump
  `ν{2x}` at x>0. A bounded positive-half cumulative function gives the
  existing phase-growth rigidity conclusion R.
- The exact critical coefficient energy bound is
  `Σ_{1≤n≤N}|a(n)|²/n ≤ K(1+log N)` for a source-dependent K≥0.
  This is `WeilSingularArithmetic.exists_forwardCoeff_critical_energy_le`:
  its `forwardCoeff` equals a since its truncated `logZetaCoeff` equals
  `lamLog lam` pointwise, including n=0 and n=1.

The last bound implies `b_j=q^{-j/2}a(q^j)=O(sqrt(1+j))`. No coefficientwise
positivity or Euler product is used. q need not be prime.

## 2. All resonances survive the radial limit

Write kτ(s) for `TruncatedRadial.offKernel τ s`, τ=ε+im, and

`J_ω,m(ε)=ε ∫_{t≤-1} exp(-iωt) f(2t) kτ(1/2+2it) dt`.

Write `M_m(ε)=ε ∫_{t≤-1} m^{-3/2-2it} kτ(3/2+2it) dt`.
The exact scaling identity already in Lean is `M_m(ε)=M_1(ε/m)`.
Define cω,m to be zero if there is no positive integer n with
`n exp(ω/2)=m`, and otherwise `exp(ω/4)a(n)`; that n is unique.

We claim `J_ω,m(ε)-cω,m M_m(ε)→0` as ε↓0, and both J and cM are bounded
by a source- and m-dependent constant times `exp(|ω|/2)`, uniformly for
0<ε≤1. Here are all contour and limit obligations.

Multiply F(s) by `Aω(s)=exp(-(ω/2)(s-1/2))`. On the closed strip its modulus
is at most `exp(|ω|/2)`; on the right edge it is exactly `exp(-ω/2)`.
Apply the existing open-rectangle inequality to AωF. For fixed finite
lower heights A≤B=-2, the radial boundary passage follows from the compact
right majorant multiplied by this uniform bound. Thus no continuous
completion at Re s=1/2 is needed. For each fixed ε>0 the distant lower
edge tends to zero: polynomial growth is dominated by
`exp(-|A| ε/|τ|)`. The remaining horizontal bound at B=-2 is uniformly
O(exp(|ω|/2)) as ε↓0, hence disappears after multiplication by ε.

On the right edge absolute Dirichlet convergence permits termwise
integration. This follows from the majorant
`exp(-ω/2) Σ |a(n)|n^{-3/2} · |kτ(3/2+iy)|`, whose lower-half integral is
finite. The exact term identity is

`n^{-s} Aω(s) = exp(ω/4) exp(-(log n+ω/2)s)`.

If `log n+ω/2=log m`, the term is exactly cω,m times the m-main kernel.
For each other fixed n, let `d_n=|log n+ω/2−log m|>0`. Since
`log|ε+im|→log m`, its separation is at least d_n/2 for small ε. The existing
right-edge exponential expansion bounds the integral of this term by

`exp(-ω/2)|a(n)|n^{-3/2} · O_m(1+d_n^{-1})`.

Thus its product with ε tends to zero. To sum over n, use the absolute
kernel bound in the next paragraph: the ε-scaled term is bounded by
`Q(m+1)^2 exp(-ω/2)|a(n)|n^{-3/2}`, uniformly in ε. Dominated convergence
over n proves the claimed zero limit after erasing the unique resonant
term. No uniform separation in n or ω is required.

For the uniform bound, use the absolute right-edge kernel bound directly:
`|kτ(3/2+iy)|≤Q |τ| exp(y ε/|τ|)` for y≤-2, Q independent of ω and ε.
Its integral multiplied by ε is bounded by `Q|τ|²≤Q(m+1)²`.
The horizontal bound has already been paid. This proves
`|J_ω,m(ε)|≤K_m exp(|ω|/2)`. The same kernel estimate, with coefficient 1,
proves that M_m is uniformly bounded. Finally, if S=Σ|a(n)|n^{-3/2},

`|cω,m|≤S m^{3/2}exp(-ω/2)≤S m^{3/2}exp(|ω|/2)`.

For ωk=2k log q, the assumed moment is exactly
`Σ|p_k|exp(|ωk|/2)<∞`. Fubini for each ε uses the summable |p_k| and the
integrable actual trace kernel. Dominated convergence for the differences
`p_k(J_ωk,m−cωk,m M_m)` uses the uniform bounds just proved. Consequently,
with the absolutely convergent sum `B(m)=Σ_k p_k cωk,m`,

`κ B(m) M_1(ε/m) → G(1)` for every integer m≥1.

The compact interval -1<t<0 carries no residue: W is bounded and the
actual trace is locally bounded; the existing near-interval estimate
applies. The remaining lower integral is the reflected radial residue
from §1. This pays the left side of the limit identity.

At m=1, B(1)=0 would make the left side identically zero, contradicting
G(1)≠0. Hence B(1)≠0 and
`M_1(ε)→G(1)/(κ B(1))≠0`. Positive scaling ε↦ε/m then gives
`B(m)=B(1)` for every positive integer m. No explicit value of M_1's limit,
and no unproved inverse Mellin formula, is required.

## 3. A geometric right side excludes positive winding

Put `P(z)=Σ_{k∈ℤ}p_k z^k`. On `q^{-1}<|z|<q`, each
`|z^k|≤q^{|k|}`: use |z|≤q for k≥0 and |z|^{-1}≤q for k<0.
The supplied weighted moment uniformly dominates the whole Laurent series
on this open annulus. Its terms are holomorphic there, so P is analytic.
Every unit-circle z has the form `exp(2i(log q)x)` with x>0: take
`x=(arg z+2π)/(2 log q)`. The actual phase representation therefore gives
|P(z)|=1, retaining the original source rather than a substituted symbol.
For m=q^l, the resonant integers are exactly n=q^j, j≥0,
with k=l−j. Therefore, putting d=B(1)≠0 and ρ=q^{-1/2}∈(0,1),

`Σ_{j≥0}p_{l-j}b_j=d ρ^l` for every l≥0.                         (T)

All series converge absolutely: p has exponential tails and b polynomial
growth. We prove directly that (T) forbids positive winding of P.

Since P has no zeros on the circle, its open nonzero set inside the original
annulus contains a uniform neighborhood of the compact unit circle.
For z≠0 the radial projection z/|z| lies on that circle and has distance
`||z|-1|` from z. Thus a sufficiently narrow round annulus is contained
in this nonzero set. Choose 0<r<1<R in it. Let N be its winding number.
The function `P'/P−N/z` has zero residue and a Laurent primitive L there.
Choosing the additive constant gives `P=z^N exp L`. Split the Laurent
series into its strictly negative and nonnegative parts `L_-+L_+`.
Then `P=P_- z^N P_+`, with `P_-=exp L_-` zero-free for |z|>r and
`P_+=exp L_+` zero-free for |z|<R. This also proves the factorization
being used, rather than assuming a Fredholm theorem on the sequence b.

Expand `γ(z)=P_-^{-1}(z)=Σ_{l≥0}γ_l z^{-l}`. Its coefficients decay
exponentially, and `γ(1/ρ)≠0` because 1/ρ>1>r. If N≥1, the function
`γP=z^N P_+` has no nonpositive Laurent coefficients. In particular

`Σ_{l≥0}γ_l p_{l-j}=0` for every j≥0.                            (A)

Explicitly, the left side of (A) is
`(2πi)^{-1}∮_{|z|=1} z^{j-1}γ(z)P(z) dz`. Both coefficient families
are absolutely summable on this circle. Termwise integration selects
exactly `k=l-j`. With `γP=z^N P_+` and N≥1, the integrand is
`z^{N+j-1}P_+`, analytic throughout the disc, so its integral is zero.
The formal circle-coefficient proof includes j=0 and all infinite sums.

Multiply (T) by γ_l and sum. Here is a direct absolute-convergence proof
using the formally established bound |b_j|≤D(j+1). Both first moments
`Σ_k |p_k|(|k|+1)` and `Σ_l |γ_l|(l+1)` are finite: q≥2 gives
`|k|+1≤q^{|k|}`, and the γ coefficients have exponential decay.
For l,j≥0,

`j+1≤(l+1)(|l-j|+1)`.

Consequently the double absolute sum is bounded by
`D (Σ_l |γ_l|(l+1)) (Σ_k |p_k|(|k|+1))`, using the injective map
`(l,j)↦(l,l-j)` into ℕ×ℤ. This pays Fubini without placing b in a Hardy
space or assuming square summability. Equation (A) gives

`0=Σ_l γ_l Σ_j p_{l-j}b_j=d Σ_l γ_lρ^l=d γ(1/ρ)≠0`,

a contradiction. Thus N≤0.

## 4. Actual positivity excludes negative winding

Continuity of W on x>0 forces ν to have no positive atoms. Indeed, the
left and right limits of C differ by ν{2x}∈[0,1); continuity of exp(2πiC)
says that difference is an integer, hence zero. Right continuity then
makes C continuous on x>0. This argument does not discard a singular
continuous component.

Set T=π/log q. Periodicity gives `C(x+T)−C(x)∈ℤ`. This continuous,
integer-valued function is constant on x>0, equal to N: 2πC is a
continuous lift of the phase over one circle traversal. Monotonicity
gives N≥0. Section 3 gives N≤0; hence N=0. A monotone periodic function
is constant, so C is bounded. The existing actual-phase power rigidity
theorem, with any exponent in (0,1), now gives R.

All source and analytic obligations have paper proofs above. The weighted
radial passage, complete resonance system, arithmetic q-chain, exterior
inverse, absolute double-series interchange and coefficient annihilator
are now Lean verified. The actual phase excludes a strictly positive
analytic factorization. Lean must still construct the periodic analytic
symbol and its annular logarithm, identify the actual winding, and assemble
the implications before L1 can be called a theorem. The full problem
remains the source mechanism that controls phases without this representation.

## Formalization plan

1. Weighted compact radial convergence and open-strip contour displacement
   for the actual source; uniform frequency bound.
2. Retain the unique resonant term for each frequency; sum with its actual
   exponential moment; normalize at m=1.
3. Laurent annihilator and q-chain energy bound; derive N≤0.
4. Actual cumulative continuity, periodic winding and positivity; assemble
   the hW-only rigidity-or-no-representation alternative.
5. Direct final leaf audits, scratch axiom audit, umbrella imports and lint.

Step 1 is compiled and wired in WeilWorkQuantizationTwistContour.lean; all six declarations passed the standard-axiom audit. The five term/series lemmas for step 2 are compiled and wired in WeilWorkQuantizationResonantTerms.lean. WeilWorkQuantizationResonance.lean also passed its clean final audit and is wired: exact source resonance, coefficient bounds and common-kernel scaling. WeilWorkQuantizationFrequencySum passed its clean final audit and is wired. It handles countable frequency families with every resonance retained. WeilWorkQuantizationPhaseCoupling compiled the reflected phase comparison and m=1 normalization: B(1) is nonzero and B(m)=B(1) for every positive integer. Its clean final direct leaf audit and three-declaration standard-axiom audit passed. WeilWorkQuantizationQChain now proves the q-power coefficient bound, exact resonance classification and reindexing, every row's convergence, and the nonzero geometric right side. Its clean direct leaf audit and all fourteen standard-axiom checks passed. WeilWorkQuantizationLaurentInverse also passed clean final and eight-declaration standard-axiom audits. It constructs Γ(w)=exp(-w Σ a_n w^n), analytic for |w|<1/r and nonzero everywhere, proves Γ(1/z)=exp(-Lminus(z)) for |z|>r, proves its multiplicative Laurent factorization, and bounds its Taylor coefficients on every smaller disc. The annular logarithm for P after removing its winding, coefficient annihilator and actual winding assembly remain unformalized. Full L1 is not Lean verified.


Formal normalization: `quantizationMainRadial` uses the y-coordinate
integral, so it is twice the paper's t-coordinate main kernel. The
corresponding source limit is `4 * betaG G = 2 * G(1)`. This common factor
cancels when comparing B(m) with B(1); it is not a changed arithmetic
coefficient.
