# Bounded overlap of the complete Weil form and single-prime flips

- **ID:** bounded-overlap-complete-weil-and-prime-flips
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** `docs/reports/review-2910/breakthrough-question-2.md`; attached task.
- **Statement:** Prove unconditional complete Weil positivity at overlap ratio two, paying successor interactions at full weight, and determine fixed-ratio selectivity of single-prime flips.

## Required outcome

1. Explicit nonzero smooth profile; eventual positivity of the actual complete form at width
   `2 / N`, for every coefficient vector, with an explicit or explicitly bounded horizon.
   Explain the signed mechanism for the successor shells, including Gamma and both poles.
2. Decide the flip at eleven at `1 + 10⁻¹⁸` and at `2`; determine the finite/infinite threshold
   question for primes at least eleven and its dependence on the profile and prime.
3. Establish the zero-side content of ratio two, including the role of finite off-line support
   and actual zeta zero density.
4. Report the exact status and obstruction for arbitrary growing overlap schedules.
5. Complete paper proofs, unconditional Lean formalization, targeted final checks, transitive
   axiom audits, and umbrella imports. Do not replace these outcomes by a criterion or no-go.

## Placement and integrity

All new Lean code for this answer belongs in
`formal/GaloisForLFunctions/TransMetzlerWeilPositivity/BoundedOverlap/`.
Only import wiring may be added outside that subfolder. Existing unrelated edits are preserved.
Corpus searches and conjecturing only; no further web searches. No numerical experiments,
trusted-computation shortcuts, added mathematical assumptions,
placeholders, raised proof limits, or full builds. Do not use the hgtl7 skill.

## Gates

- [x] Task and briefing read; existing worktree changes recorded and preserved.
- [x] Initial corpus search run before consulting Mathlib.
- [ ] Exact finite-horizon definitions and briefing's shell statements checked in source.
- [ ] Complete paper proof of ratio-two positivity and flip conclusions.
- [ ] Lean checks and transitive axiom audit of exact claimed results.
- [ ] Requirement-by-requirement completion audit.

## Current evidence

Initial corpus searches locate `eventually_completeWeilMatrix_posDef_certified` and
`eventually_completeWeilMatrix_posDef_cZero`, but no macroscopic-overlap positivity result.
`primeFlip_exists_negative_complete_test` concerns unrestricted compact tests; it does not
settle a fixed overlap ratio. These are leads pending source and dependency checks.

## Conjecture loop

1. The literal bounded-overlap row estimate contains a downward `(n/N) log n` term.
   The successor operator is not uniformly bounded merely by the upward dyadic Chebyshev
   increment. Gamma's overlapping Gram term and the downward divisor logarithm must cancel
   before an operator estimate. The corpus's exact divisor-jet identity confirms this.
2. A concrete flip witness is available for proof: put
   `F_p(n)=1-2*1_(p|n)+2*1_(p²|n)` and `x_n=F_p(n)/sqrt(n)`.
   It has square one, mean `a_p=1-2/p+2/p²`, and lies in the Ramanujan span
   of conductors `1,p,p²`, with raw coefficients
   `a_p, -2(p-1)/p², 2/p²`.
   Its untwisted adjunction excitation is exactly `4 log(p)/p`.
   Multiplication by `p` gives `F_p(n)F_p(pn)=-1+2*1_(p²|n)`.
   The twisted-minus-untwisted prime correction at this first power cancels the
   `4 log(p)/p` excitation; the remaining odd powers start at `p³`.
   Bounding their correlations above by one gives remaining cost at most
   `4 log(p)*(2/p³+1/(p²(p-1)))`.
3. At `p=11`, proposed separated complete-form upper limit at ratio `r=99/100` is
   `β/M-log(2πr)+r*q*(101/121)² +4 log(11)*(2/11³+1/(11²*10))`.
   The existing plateau bounds give `β/M≤21/20` and `q≤1`.
   Elementary bounds `log(2π)>9/5`, `log(11)<5/2`,
   `(101/121)²<7/10`, `-log(r)≤1/99`, and tail cost `<1/40`
   make this strictly negative. This is an analytic argument, not a numerical experiment.
   The finite packet limit, literal twisted-prime correction, and variable-width transfer
   have now passed Lean with only `propext`, `Classical.choice`, and `Quot.sound`.
   Rounding the sub-horizon gives eventual negativity for every fixed `c≥99/100`,
   including both requested ratios `cZero` and `2`.
   This construction does not prove zeta positivity at ratio two or classify all primes.
4. At ratio two the candidate completed mode energy subtracts
   `2 μ(m)/totient(m) * integral_(1/2)^1 (G(u)/M)/u du` from the separated energy.
   For the indicator limit, conductors one and two give respectively
   `4-3*log(2)-log(2*pi)` and `log(4/pi)`, both positive. The prime successor sum
   has twice the leading short-overlap Gamma contribution; cancelling both completely
   would miss this finite spectral correction. Actual norm quasimodes and spectral exhaustion
   remain unproved. Ordinary charge variance alone does not suffice.

## Candidate mechanism for the full ladder — unproved

Write `G(u)=integral φ(v)φ(v+u) dv`, `M=integral φ²`, `q=(integral φ)²/M`.
The proposed actual conductor energy is
`E_m(c)=self(c)+log(m)+tameDifferent(m)+1_(m=1)*c*q
-2/(M*totient(m))*sum_(1≤h<c) c_m(h)*integral_(h/c)^1 G(u)/u du`.
Its divisor identity should be `E_m(c)=sum_(d|m) d*μ(m/d)*E_1(c/d)/totient(m)`.
Poisson summation suggests a positive representation by integrated squared Fourier transforms
at nonzero primitive frequency classes. This would give positivity and decay as `c→∞`.
The actual operator limit, its positive representation, and coercivity are separate obligations.

For coercivity, the unmodified plateau has a partition-of-unity resonance at spacing `1-η`;
strict periodization variance cannot be assumed uniformly. A candidate profile
`exp(τ*u)*plateau(η,u)`, `τ>0` small, breaks this resonance. On each interval avoiding the
transition layers, every periodized Fourier fibre is a nonzero geometric sum times an
exponential. A uniform high-frequency frame bound on fixed overlap ranges could then pay
the high block at order `log N`; Hilbert's inequality pays the low/high Gamma cross block,
and a Schur estimate pays the full prime shells and the pole cross terms. None of these
operator bridges has yet been formalized here.

A more direct coercivity candidate uses an exponentially tilted compact spline, whose
Fourier transform has no real zeros. A triangular frequency window of width `B*N`,
centered above `B*N`, has Fourier off-diagonal entries bounded by
`4/(B*N*|log(m/n)|²)`. Integer log separation and the convergent inverse-square sum give
a lower mean-square bound of order `N*sum|x_n|²` when `B` is a sufficiently large fixed
constant. No sharp Hilbert inequality is needed. A positive Fourier minimum on this
fixed rescaled band would then give Gamma coercivity of order `log N` on a top block.
The lower prefix is separated; prime and pole mixed blocks can be paid by one Schur
estimate, and the separated Gamma mixed block by the Hilbert matrix bound. This could
produce the full prime-defect reserve needed for spectral exhaustion. The corpus already
contains a boosted cubic spline (`splineProbe`), but this complete argument is unproved.

A subsequent corpus search located the already verified
`HTGeometry.interval_integral_normSq_expSum_ge`. Applied at frequencies
`log(n)/(2*pi)`, separation is `1/(2*pi*N)` and its endpoint error is `52*N`.
The actual interval `[N,101*N]` therefore retains at least
`48*N*sum|x_n|²`. This replaces the redundant triangular-kernel draft.
The profile multiplier and complete-form coercivity bridges remain unproved.

## Core proof audit: finite modes and escaping vectors

This is a proposed proof to audit, not a completed theorem. The user explicitly
rejected helper-code accumulation as an answer. Do not add further infrastructure
without resolving these mathematical steps and connecting them to the final statement.

### Scalar sign, with its missing normalization identified

Use the Fourier convention `hatφ(t)=integral φ(u)*exp(i*t*u) du`.
Put `g=G/M` and `B=β/M`. The conductor-one candidate is

`E1(c)=B-log(2*pi*c)+c*q-2*sum_(1≤h<c) integral_(h/c)^1 g(u)/u du`.

Direct differentiation and Poisson summation give

`E1'(c)=-1/M*sum_(k in Z, k≠0)|hatφ(2*pi*c*k)|²`.

The additive constant is essential. To determine it, compare with the indicator
autocorrelation `g0(u)=1-u` on `[0,1]`. At positive integer `L`, its energy is

`2*log(Gamma L)-(2*L-1)*log L+2*L-log(2*pi)`,

twice the Stirling remainder, which tends to zero. For a smooth profile,

`E1(c)-Eindicator(c)=integral_0^1 (2*fract(c*u)-1)*(g(u)-(1-u))/u du`.

The quotient extends continuously at zero; its derivative is integrable because
`g` is C² and `g'(0)=0`. Cellwise mean-zero averaging gives convergence to zero.
Hence `E1(infinity)=0`, and integrating the derivative gives a positive Fourier-tail
representation. The relevant corpus inputs are `abs_log_Gamma_sub_stirling_le`
and `abs_integral_mul_meanZero_le`; exact bridges are not yet formalized.

Möbius inversion gives

`Em(c)=sum_(d|m) d*mu(m/d)*E1(c/d)/totient(m)`.

Differentiating selects primitive frequency classes. For `m>1`,

`Em(c)=1/(M*totient(m))*integral_c^infinity
  sum_(a in Z, gcd(a,m)=1)|hatφ(2*pi*s*a/m)|² ds`.

The terms `a=±1` give the conductor-uniform lower bound
`Em(c)≥2/M*integral_c^infinity |hatφ(2*pi*s)|² ds>0`.
For `m=1`, omit `a=0`; the same lower bound holds. This uniform bound is stronger
than checking finitely many scalar energies. Its identification with actual matrix
quasimodes at overlap remains an explicit obligation.

### A common explicit profile for the core and eleven flip

A candidate avoiding the plateau resonance while retaining the negative eleven margin:
`epsilon=10^-6`, `tau=epsilon^3`, `a=(1-6*epsilon)/2`, and

`φ(u)=exp(tau*(u-1/2))*(2*a)*(unif a * upow epsilon 2)(u-1/2)`.

Here `*` is convolution, and each `unif` has mass one. Four interval convolutions
give C² regularity, support `[0,1]`, and positivity on its interior. Before the
exponential tilt, the profile lies in `[0,1]`, equals one on
`[6*epsilon,1-6*epsilon]`, and has Lipschitz constant at most `1/(2*epsilon)`.
Splitting the Robin integral at `6*epsilon` bounds its small-shift part by
`O(epsilon)` and its remaining part by `1+12*epsilon*log(1/(6*epsilon))`.
The existing Lipschitz perturbation bound pays the tilt by `O(tau/epsilon)`.
These bounds should give `β/M≤21/20`, the same margin used for the eleven trial.
This profile construction and those numerical inequalities are not yet checked.

Its Fourier transform has the explicit lower bound

`2*sinh(a*tau)*sinh(epsilon*tau)^3 /
  (epsilon^3*(tau²+t²)²)`.

It follows by multiplying the four tilted-interval Fourier factors. The numerator
is strictly positive. Thus the high-frequency band bound has a positive constant
for every fixed `c`, while every successor interaction keeps its original weight.

### The all-vector coercivity argument to verify

Fix `c>0`, choose `0<delta<min(1,1/(4*c))`, and split at `M=floor(delta*N)`.
All forms below use the same physical width `c/N` and atom-mass normalization.

1. The low principal block is exactly the width-`c*M/N` length-`M` matrix.
   `exists_uniform_completeWeil_primeDefect_reserve_through_touching` gives
   `W_low≥b*D_M-C*||x_low||²`, with `b=(1-q)/4>0`.
2. The Fourier lower bound and Montgomery–Vaughan give
   `Gamma_high≥A(c)*log(N)*||x_high||²-C(c)*||x_high||²`, `A(c)>0`.
   The global Gamma lower bound and the finite overlap count pay the rest of the
   Fourier integral. The high-high prime block has only bounded prime-power ratios
   `k≤2/delta`; its norm and the high-high pole norm are bounded independently of `N`.
3. The actual low-high prime block has weighted upward row `O_(c,delta)(1)`
   and downward row `O_c(log N)`, with weight `n^(-1/2)`. The upward estimate is
   a finite union of dyadic Mangoldt windows; the downward estimate sums the exact
   divisor identity over the finitely many integer offsets. Weighted Schur gives
   cross norm `O_(c,delta)(sqrt(log N))`, without reducing any successor weight.
4. The mixed Gamma kernel is bounded by `C(c)/(m-n)` across `n≤M<m`:
   the gap exceeds twice the atom width, and
   `omega(s-w)≤exp(w/2)*sqrt(m*n)/(m-n)`.
   Reindexing around `M` gives a Hilbert matrix. The corpus's Hilbert bound pays
   this block by a constant times `||x_low||*||x_high||`.
5. The two mixed pole terms together cost `O_(c,delta)(sqrt(log N))` times the
   product of the two coefficient norms. One Schur absorption into the high Gamma
   reserve leaves `W≥b*D_M+(A(c)/2)*log N*||x_high||²-C*||x||²`.
6. Splitting the literal prime defect yields
   `D_N≤D_M+4*log N*||x_high||²+C_delta*||x||²`.
   Therefore `W≥b_c*D_N-C_c*||x||²`, with `b_c>0`.

This is the proposed mechanism paying the full shells. The finite-block identities,
uniform row bounds, and constants must be proved for the actual form before treating
the argument as established. It uses actual prime arithmetic and both poles.

### Closing the spectral argument

Bounded prime defect has a horizon-independent finite Ramanujan approximation
(`exists_finite_ramanujan_approximation_of_poleDefect_le`). A normalized nonpositive
eigenvector would therefore be close to one fixed finite Ramanujan span. Actual norm
quasimodes with the uniformly positive `Em(c)` force all its coordinates in that
span to tend to zero, a contradiction. The required norm-quasimode extension is:

- Near-diagonal Gamma contributes `G(h*N/(c*n))*log N`.
- The downward successor divisor jet contributes the matching `log n` term.
- Their difference is supported on `n` proportional to `N`, with squared pole-profile
  norm `O(1)`; after division by `log N` it vanishes.
- Far Gamma and the pole center must remain paired; either alone has a logarithmic
  row on the conductor-one profile.
- Upward affine prime windows produce exactly the scalar correction in `Em(c)`.
  Uniformity on `n≤N/J` follows from the corpus's affine reduced-residue theorem;
  the remaining top interval has harmonic mass `O(log J)`, negligible after
  normalization. Boundary shells, including the finite-horizon second shell at
  `c=2`, must be retained and bounded using endpoint vanishing.

No actual norm-quasimode theorem beyond touching has yet been proved here. An
effective horizon also needs quantitative moduli for this extension; a mere choice
from an eventual theorem is not an explicit bound.

The row argument can be organized without a uniform prime-window limit at a fixed
top cutoff. For each fixed `J>2*c+2`, rows `n≤N/J` have no overlapping Gamma
neighbour and no downward non-ratio lag. Only the upward affine windows remain.
Choose `J` using the residue-window modulus; their error is then `epsilon/sqrt(n)`.
For `n>N/J`, keep Gamma and the downward divisor sum together. At each bounded
integer offset `h`, their leading terms are exactly the same correlation factor
times `log(N)` and `log(n-h)`. The difference is bounded by
`C*(1+log(2*J))/sqrt(n)`. This top interval has bounded harmonic mass, so its
normalized squared residual tends to zero. The reference center and both poles
remain paired throughout.

A uniform near-pair Gamma remainder follows directly on the Fourier side:
after subtracting `log(1/w)*G(s/w)`, its absolute value is bounded by
`C*integral |hatφ(t)|²*(1+|log |t||) dt`, independently of `s/w` and `0<w≤1`.
The separated remainder is already bounded by `C*w²/s²` in
`exists_profile_crossError_uniform`. Acting on a bounded periodic pole profile,
this gives an unnormalized squared norm bounded independently of `N`; division
by `log N` removes it. These exact bridges are still to be formalized.

The corpus does contain a quantitative residue input:
`RHTower.exists_characterChebyshevPsi_power_log` gives, for each nonprincipal
character, `|psi_chi(x)|≤C*x*exp(-rho*(log x)^(1/10))` beyond `x0`.
Consequently the squared affine-window errors are integrable against `dy/y`;
an `O(1/sqrt(log N))` norm residual is available in principle. Its constants
depend on the character Perron strip constants. Those constants are existential
in the current source; this does not yet supply the required explicit horizon.

### All-prime consequence if the actual extension closes

The three-conductor trial has exact untwisted limiting energy

`(1-2/p)^2*E1(c)+4*(p-2)/p²*E1(c/p)+4/p²*E1(c/p²)`.

Its exact limiting flip correction should be

`-4*log(p)*(p³-4*p+2)/(p²*(p²-1))<0`.

The first odd power has mean correlation `-1+2/p²`; all odd powers at least three
have mean `1-2/p+2/p²`. Summing their geometric series gives the expression above.
Non-ratio corrections for a fixed prime power contribute only bounded harmonic
top mass and vanish after logarithmic normalization; a geometric tail controls the
remaining powers. Since each `E1(c/d)` tends to zero, this would prove finiteness of
every prime-flip threshold. Quartic Fourier decay gives a coarse explicit upper
bound of order `p^(13/7)/(log p)^(1/7)` for this profile. Uniform fixed-`c` zeta
coercivity and the exact translation bound `O(log p/sqrt p)` for the flip perturbation
would imply `c*(p)→infinity`. These consequences are still unproved, and the coarse
upper bound is not claimed to be sharp threshold growth.

### A sharper proposed threshold description

The scalar energies satisfy, for prime `p`,

`E_(m*p)(c) = (p*E_m(c/p)-E_m(c))/(p-1)` if `p` does not divide `m`,
and `E_(m*p)(c)=E_m(c/p)` otherwise.

The positive Fourier-tail representation makes every `E_m` strictly decreasing.
Hence `E_(m*p)(c)>E_m(c)` and, in particular, `E_m(c)≥E_1(c)`.
This improves the conductor-uniform lower bound.

The limiting flip perturbation preserves the prime-to-`p` conductor `q` and acts
identically on each chain `q*p^k`. Since `E_(q*p^k)≥E_(p^k)`, its lowest block is
the `p`-power chain. Let `D_p` be diagonal with entries `d_0=0` and
`d_k=(k+1/(p-1))*log(p)` for `k≥1`, and let `U_p` multiply a valuation profile
by `(-1)^v`. The bounded flip perturbation is `U_p*D_p*U_p-D_p`.

When `c<p`, every non-ground conductor in this chain is still separated, so the
candidate completed block is exactly

`self(c)*I + U_p*D_p*U_p + (E_1(c)-self(c))*P_0`.

Writing `a=-self(c)`, `E=E_1(c)`, the squared coordinates of `U_p e_0` are

`b_0²=(p-1)²/(p+1)²`,
`b_k²=4*(p-1)*p^(1-k)/(p+1)²` for `k≥1`.

For `0<a<d_1`, define the convergent positive series
`S_p(a)=sum_(k≥1) b_k²/(d_k-a)`.
The rank-one Schur calculation says positivity changes precisely when

`(a+E)*(b_0²-a*S_p(a))=a`.

This is a proposed exact threshold equation, pending the actual spectral-transfer
and valuation-block proofs. It is not an established answer or a substitute for
those proofs. The full limiting operator is strictly decreasing in `c`, and its
conductor energy tends to infinity, so this framework would give a unique first
zero rather than an arbitrary trial threshold.

For the near-indicator profile, total variation can be bounded by `21/10`.
The Fourier tail then gives `E_1(c)≤(Var φ)²/(12*M*c)`. Combining this with the
three-conductor trial at `c=p/4` appears sufficient to prove `c*(p)≤p/4` for
all `p≥11`, after checking the elementary constants. This sharper finite-prime
bound would avoid waiting for the quartic-decay regime.

For the explicit four-box tilted profile, its Fourier numerator is periodic and
strictly positive, and `E_1(c)~D*c^(-7)` with `D>0`. The scalar Schur equation
then predicts the sharper asymptotic

`c*(p) ~ ((3*D/2)*p/log(p))^(1/7)`.

At this scale `a/log(p)→1/7` and
`S_p(a)~14/(3*p*log(p))`; the critical right side is
`2*log(p)/(3*p)`. This asymptotic remains a conjecture until both the block
identification and uniform error estimates are proved.

## Proof and Lean status

`elevenTrialUpperMargin_neg` passed Lean with only `propext`, `Classical.choice`, and
`Quot.sound`. `PrimeSquareTrial.lean` and `PrimeFlipTail.lean` also compiled, including the
exact Ramanujan expansion, harmonic correlation, finite full-tail bound, and its limit.
`VariablePacketLimit.lean`, `ElevenPacket.lean`, `PrimeFlipCompleteForm.lean`, and
`ElevenFlipNegativity.lean` also compiled with the three standard axioms.
`ElevenFlipAtEveryHorizon.lean` passed the required no-olean check, including
`eventually_elevenFlip_negative_two` and `eventually_elevenFlip_negative_cZero`.
The final repeat check after removing two redundant tactics also passed.
`LogarithmicBandMass.lean` passed its final no-olean check with the same three standard
axioms. It proves that every real coefficient vector retains at least
`48*N*sum_(n=1..N) x_n²` of Dirichlet-polynomial squared mass on `[N,101*N]`.

Thus the requested eleven-flip decisions are answered for `transMetzlerProfile`:
both ratios are eventually negative on an explicit atomic coefficient vector.
For fixed `c≥99/100`, put `H_N=floor((99/(100*c))*N)` and use
`x_n=(1-2*1_(11|n)+2*1_(121|n))/sqrt(n)` for `n≤H_N`, zero otherwise.
The upper limiting energy, divided by `(c/N)*log(H_N)*M`, is strictly negative.
This includes Gamma, both poles, and every prime power.

The main zeta positivity claim at ratio two, its explicit horizon, and the full
all-prime threshold classification are still unproved. Overall goal remains incomplete
and is paused at the user's request.

## Pause checkpoint

The user requested completion of started Lean work and formalization of completed
paper proofs, followed by a pause. The eleven-flip proof is extracted into
`../3-formalized/bounded-overlap-eleven-flip-negativity.md` with its checked Lean declarations.
All nine started Lean modules in `BoundedOverlap/` are finished and checked. The final
eleven-flip and band-mass declarations passed their axiom audits; both modules are
imported by the umbrella. No unfinished Lean draft or completed paper proof remains
from this work. Owned scratch files have been removed.
The core and threshold sections above are conjectural arguments, not completed
paper proofs awaiting a ceremonial Lean wrapper.

An alternative constructive core route was considered but not started in Lean:
use an exponentially tilted, box-smoothed positive profile containing `1+cos(K*u)`.
For a box radius `a` with `K*a` an odd multiple of `pi`, the unsmoothed transform is
proportional to `K²*sin(a*z)/(z*(z²-K²))` and has only real zeros. A small box convolution
gives C² regularity; exponential tilt removes real Fourier zeros. A band near `K`
may retain a lower Fourier bound independent of `K`, while the Robin quotient grows
like `log K`. Height and mass remain bounded. This could make the low-prefix mass
reserve large enough to pay a full Schur cost at ratio two using only elementary
prime bounds, avoiding existential residue-class constants in the core horizon.
The uniform constants, support construction, and complete-form Schur estimate were
not completed. Do not treat this route as a proved profile or a solution.
