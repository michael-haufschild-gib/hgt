# SZ: critical first variation of the literal arithmetic source

- **ID:** sz-critical-source-first-variation-2026-10-18
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** corpus-only source inspection; Suzuki route SZ and BiScale uncertainty.
- **Statement:** Recover the complete Weil quadratic form from the positive-shift first variation of `suzukiSourceHFinite`, retaining the Gamma atom, both pole terms, and every arithmetic cusp.

## Goal

For a real smooth compactly supported source `f`, let `C(t) = integral f(u) f(u+t)` and
`A_w(t) = exp(t/2) suzukiSourceHFinite w (exp t)`. Prove that
`(C(0) - integral_(0,infinity) C(t) A_w(t)) / w` tends to the complete Weil form as
`w` tends to zero through positive values. Produce quantitative, translation-uniform cusp
control using BiScale's Levy energy, without paying for derivatives of `f`.

This removes a critical-source limiting input. It does not assert positivity of the resulting
Weil form, moving-aperture control without a rate, or RH.

## Gates

- [x] 0 → 1: literal source, positive shifts, precise proposed limit, source attack.
- [x] 1 → 2: complete paper proof, checked normalization, all analytic dependencies closed.
- [ ] 2 → 3: canonical leaf compilation and complete public-declaration axiom audit.
- [ ] 3 → 4: publication preparation (not requested).

## Plan and proof obligations

1. Check the source's exact log-coordinate decomposition and Weil normalization.
2. Prove the primary Beta kernel mass and its first variation. Control the atom at the origin
   separately from the compensated Levy integral.
3. Prove uniform translated-cusp convergence from Krein increments and Levy energy.
4. Carry the pole convolution through compact tests. Its critical density is not globally
   integrable; retain the compact aperture throughout Fubini and limiting arguments.
5. Differentiate the locally finite arithmetic sum using the actual coefficients and their
   existing derivative `2 * vonMangoldt n` at zero. Keep all terms up to one common cutoff.
6. Identify the complete Weil form; formalize the exact dependency-closed theorem, wire the
   umbrella, audit axioms, index, and lint.

## Kernel identities

The primary log density from the literal source is

`B_w(t) = 2*pi^w/Gamma(w) * exp(-(5/2-w)*t) * (1-exp(-2*t))^(w-1)`.

Its mass is `M_w = pi^w Gamma(5/4-w/2)/Gamma(5/4+w/2)`. For `w > 0`,
`B_w/w = [pi^w/Gamma(1+w)] K(t) (2*sinh t)^w`, where
`K(t) = 2 exp(-5*t/2)/(1-exp(-2*t))`.

For sufficiently small positive `w`, `M_w <= 2` and
`B_w(t) <= 2*w*w_arch(t)`, with `w_arch(t) = 2 exp(-t/2)/(1-exp(-2*t))`.
Krein and Cauchy-Schwarz give

`|integral B_w(t) (C(u+t)-C(u))|^2 <= 8*w*C(0)*J_arch(f)`

uniformly in `u`. This pays for every arithmetic cusp using the same energy.

The compensated primary limit, Gamma recurrence, and pole convolution yield the
archimedean and polar terms. Existing `hasDerivAt_suzukiShiftedCoefficient` supplies the
arithmetic tangent. The complete normalization check appears in the proof below.

Uniform first-variation convergence on a bounded `C(0)+J_arch` ball is not assumed. The ratio
`B_w/(w*K)` behaves nonuniformly near the origin. A log-weighted Levy energy may supply a
quantitative replacement, but no no-go or replacement theorem is claimed yet.

## Corpus audit

- Two deep searches completed with partial results: inventory complete, compiler metadata
  mostly source-only, semantic coverage unavailable, background refresh incomplete. Candidate
  applicability must therefore be checked against source and Lean.
- Existing continuity/differentiability lemmas for the literal source require `1 < w`;
  local L2 lemmas require `1/2 < w`. They do not cover this critical limit.
- Generic Fourier/Livsic tangents assume the source variation and cannot supply it.
- Existing unitary Hankel realizations assume innerness and cannot supply unconditional sign.
- `WeilArchReLevyPoleForm.weilArchRe_eq_levy_pole` supplies the normalization target.

## Paper proof — [PROVED HERE]

Assume `f` is real, C², and compactly supported. Write `C = autocorr f`, `R = C(0)`,
`J = biScaleLevyEnergy f`, and choose `A > 0` with `C(t)=0` for `|t| >= A`.
The corpus proves `|C(t)| <= R`, `Delta(t)=R-C(t) >= 0`, integrability of
`Delta*w_arch`, and `(C(u+t)-C(u))² <= 2 R Delta(t)`. The latter is the Krein
increment theorem, valid for every location `u`.

### Primary density and mass

Take `0 < w <= 1`. The change of variable `x=exp(-t)` in
`hasMellin_suzukiPrimaryBetaKernel` at `s=1/2` gives exactly the displayed `B_w`
and `M_w`. The convergence condition is `w-2 < 1/2`, which holds. Complex powers
are powers of positive reals on the integration interval, so this density is real
and nonnegative. The Gamma functional equation gives

`B_w(t)/w = a_w * 2 exp(-(5/2-w)t) (1-exp(-2t))^w / (1-exp(-2t))`,
`a_w = pi^w/Gamma(1+w)`.

Since `0 < 1-exp(-2t) < 1` and `w <= 1 < 2`, this is at most `a_w*w_arch(t)`.
Continuity of Gamma away from nonpositive integers gives `a_w -> 1`, `M_w -> 1`;
hence both are at most 2 for all sufficiently small positive shifts. For fixed
`t > 0`, `B_w(t)/w -> K(t)`. Moreover, for every `epsilon > 0`,
`integral_[epsilon,infinity) B_w <= a_w*w*integral_[epsilon,infinity) w_arch -> 0`.
Thus `B_w(t) dt` converges against every bounded continuous test on `[0,infinity)`
to the unit atom at zero. This assertion follows directly by splitting at
`epsilon`, using continuity at zero on the first part and the displayed tail
bound on the second; it assumes neither innerness nor RH.

Weighted Cauchy-Schwarz and Krein give, for every real `u`,

`|integral B_w(t)(C(u+t)-C(u)) dt|² <= M_w * integral B_w(t)(C(u+t)-C(u))² dt`
`<= 2 R M_w * integral B_w(t) Delta(t) dt <= 2 R M_w a_w w J`.

All integrals exist: `C` is bounded, `B_w` is integrable, and the last integrand
is dominated by the integrable Levy density times `Delta`. This proves the
translation-uniform cusp estimate, including `8*w*R*J` once `a_w,M_w <= 2`.

### Compensated first variation and Gamma constant

The Gamma ratio is differentiable near zero. Its logarithmic derivative gives
`M'_0 = log pi - psi(5/4)`, with `psi` real on positive real arguments. Therefore

`(integral B_w C - R)/w = ((M_w-1)/w) R - integral (B_w/w) Delta`
`-> (log pi - psi(5/4)) R - integral K Delta`.

Dominated convergence is justified by `0 <= (B_w/w)Delta <= 2*w_arch*Delta`.
The Gamma recurrence gives `psi(5/4)=psi(1/4)+4`. The exact elementary identity
`w_arch-K = 2 exp(-t/2)` and `integral_0^infinity 2 exp(-t/2) dt = 4` then give

`primary derivative = -Omega(0) R - J - 2 integral exp(-t/2) C(t) dt`,

where `Omega(0) = psi(1/4)-log pi = EF.gammaBracket 0`, as in
`ArchimedeanAnomalyConstantLaws.gammaBracket_eq_re_digamma`.

### Full signed archimedean source, including its pole

The exact corpus identity `suzukiCanonicalG = pi^w P_w - 2w*pi^w(P_w *_M p_w)`
and its almost-everywhere equality to `suzukiSourceG` imply in log coordinates

`G_w(t) = B_w(t) - 2w integral_0^t B_w(r) exp((1/2-w)(t-r)) dr`.

Pair against `C(u+t)`, for `u >= 0`. Fubini is legitimate on the triangle
`r,s >= 0, r+s <= A`: the integrand's absolute integral is at most
`M_w R A exp(A/2)`. No global integrability of the growing pole density is used.
The pole contribution divided by `w` equals

`-2 integral B_w(r) Psi_(w,u)(r) dr`,
`Psi_(w,u)(r) = integral_0^infinity exp((1/2-w)s) C(u+r+s) ds`.

These functions vanish for `r >= A`, and `Psi_(w,u) -> Psi_(0,u)` uniformly:
on `0 <= s <= A`, the exponentials converge uniformly and `|C| <= R`.
`Psi_(0,u)` is continuous by bounded convergence on `[0,A]`. The primary
approximate-identity result and bounded mass therefore give the pole derivative
`-2 integral exp(t/2) C(t) dt` at `u=0`. Combining both pieces gives

`(integral G_w C - R)/w -> -Omega(0)R - J - 4 integral cosh(t/2) C(t) dt`.

The same estimates give the fully signed, translated quantitative bound

`|integral G_w(t) C(u+t) dt - M_w C(u)|`
`<= sqrt(2 R M_w a_w w J) + 2 w M_w R A exp(A/2)`

for every `u >= 0`, with no discarded pole term and no source derivative norm.

### Arithmetic cusps and the complete Weil functional

Put `N=floor(exp A)` and `T_w(A)=sum_(1<=n<=N) c_w(n)/sqrt(n)`. The literal
definition of `suzukiSourceHFinite`, followed in each summand by
`t=log(n)+v`, gives exactly

`integral C(t) A_w(t) dt = sum_(1<=n<=N) [c_w(n)/sqrt(n)] integral G_w(v) C(log(n)+v) dv`.

Terms outside this common cutoff vanish by support. Endpoint values occur only
on finitely many null sets. Every coefficient is nonnegative for `w>0`, directly
from the product definition; `c_w(1)=1`. Consequently the full source differs
from `M_w sum c_w(n) C(log n)/sqrt(n)` by at most

`T_w(A) * [sqrt(2 R M_w a_w w J) + 2 w M_w R A exp(A/2)]`.

This also records the precise moving-head and aperture costs; it does not claim
they stay bounded as `A` grows.

For each `n>=2`, the corpus proves `c_0(n)=0` and `c'_0(n)=2 Lambda(n)`.
The translated full source converges to `C(log n)` by the quantitative bound and
`M_w -> 1`. Thus its product with `c_w(n)/w` tends to
`2 Lambda(n) C(log n)`. There are finitely many terms at this fixed aperture, so
the limit interchanges with their sum. Combining with the `n=1` first variation,

`(R-integral C A_w)/w -> Omega(0)R + J + 4 integral cosh(t/2)C(t)dt`
`                               - 2 sum_(2<=n<=N) Lambda(n) C(log n)/sqrt(n)`.

This is the real complete Weil functional: the corpus's archimedean-pole identity
supplies the first three terms, and the definition of `weilFullFunctional` supplies
the two equal arithmetic evaluations at `log n` and `-log n`, since `C` is even.
The complete-source theorem is dependency-closed on paper. Its full Lean
formalization remains pending; the certified primary component is detailed below.

### Stronger primary statement on the finite-energy domain — [PROVED HERE]

The primary first-variation argument needs only a measurable real profile `C`, with
`|C(t)| <= C(0)` almost everywhere on the positive ray, and integrability of
`(C(0)-C(t))*w_arch(t)`. It needs neither smoothness, compact support, nor positive
definiteness. The pointwise envelope implies the compensator is nonnegative. Its
weighted integrability supplies exactly the dominating function in the primary
proof above; boundedness supplies integrability against each `B_w`. Splitting
`C(t)=C(0)-(C(0)-C(t))` and differentiating the explicit mass then proves

`(integral C B_w-C(0))/w -> (log pi-psi(5/4))*C(0)-integral (C(0)-C(t))*K(t)`.

This is a primary-kernel theorem, not a complete-source positivity claim. Internal
novelty audit: exhaustive references to `suzukiPrimaryBetaKernel` occur only in
its defining Mellin module and the arithmetic module's measurability proof.
The other retrieved Beta asymptotics in `SuzukiRealKernelForm` take a spatial
endpoint limit at a fixed positive shift, and do not give this shift-zero theorem.
No external novelty claim is made.

## Formalization checkpoint

### Complete-source formalization resumed

The current target is the exact paper theorem above, starting with the
translation-uniform primary cusp estimate. Its source domain is every real
compactly supported `C²` function; boundedness, measurability, and finite Lévy
energy are discharged from that domain, not assumed as analytic inputs.
The first leaf will prove
`(integral B_w(t) C(u+t) dt - M_w C(u))² <= 2 R M_w a_w w J`
for every real `u` and `0 < w <= 2`, then uniform convergence of the translated
primary pairings. Weighted Cauchy–Schwarz and the existing Krein increment law
give the paper proof displayed above. The signed pole and arithmetic assembly
remain required before the full card can move to stage 3.

Leaf status:

- `SuzukiCriticalTranslatedCusp.lean` compiles: the squared uniform cusp bound, its
  explicit vanishing error, uniform convergence over all translations, and
  specialization of the primary first variation to compact `C²` sources. Its
  olean was produced for the pole-pairing leaf. Its 11 public declarations passed
  the transitive axiom audit; only `propext`, `Classical.choice`, and `Quot.sound`
  occur. Final direct-source check remains pending.
- `SuzukiCriticalLogKernel.lean` compiles: exact logarithmic transport of the literal
  Beta–pole convolution and the full signed source identity. The pole identity
  holds for all real logarithmic arguments: for nonpositive arguments both
  integration regions are empty. The signed source identity is asserted for
  positive arguments, avoiding the source's separately totalized endpoint. Its
  olean was produced for the pole-pairing leaf. All 5 public declarations passed
  the same axiom audit; final direct-source check remains pending.
- `SuzukiCriticalPolePairing.lean` compiles: `L¹` compact-test Fubini, the tested
  pole limit, translated full-source convergence, and the full archimedean
  source first variation with the growing pole retained. Arithmetic assembly
  and identification with the complete Weil functional still remain. Its 10
  public declarations passed the same axiom audit. The cutoff and source
  integrability are derived from compact support. Final direct-source check
  remains pending. The three finished leaves are wired into `RHTower.lean`;
  the umbrella has not been compiled.
- Concurrently available drafts `SuzukiCriticalWeilNormalization.lean` and
  `SuzukiCriticalArithmeticVariation.lean` cover the remaining finite arithmetic
  assembly and Gamma normalization. Their files are preserved and reused; they
  do not yet supply a verified complete-source capstone in this checkpoint.

For the remaining compact-test Fubini step, the primary density belongs to
`L¹`, but need not belong to `L²` at small shifts. Use `L¹` convolution
integrability with the pole exponential cut off to the fixed aperture, then
multiply the joint integrand by the bounded autocorrelation. This supplies
absolute integrability directly and does not import an inapplicable `L²`
kernel-transposition theorem.

The next conjecture exposed by this proof is extension of the complete literal
source tangent to compact finite-Lévy-energy source space, without `C²`
regularity. The primary theorem already admits that energy domain; the remaining
audit must retain continuity of correlation, translated Krein control, compact
pole testing, and the full Weil-form identification. This conjecture is not an
arithmetic sign bound and is not claimed proved by the current leaves.

This is formalization of an existing paper proof, not a new source cancellation
claim. WL's growing-aperture one-sided bound remains open.

The primary finite-energy first variation is now formalized in
`formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiCriticalBetaKernel.lean`.
Canonical compilation and the audit of all 19 public declarations passed; only
`propext`, `Classical.choice`, and `Quot.sound` occur. The exact child result is
tracked in `../3-formalized/sz-critical-beta-finite-energy-2026-10-18.md`.

The primary capstone assumes `|C(t)| <= C(0)`. A translated autocorrelation need
not satisfy that hypothesis with `C(u)` at its origin. The arithmetic-cusp passage
uses the separately proved Krein estimate and weak approximate-identity argument.

The translated-cusp estimate, compactly tested pole convolution, arithmetic sum,
and their combined complete-source limit remain paper-proved but not formalized
here. The BiScale import closure still lacks three shared artifacts at the audit
checkpoint; see `/tmp/hgt-sz-pending-imports.txt`. No duplicate shared build was
launched. No positivity or RH conclusion follows from the certified primary limit.

## Rotation

Prior substantive turns: RW → TH → MSC → RB. This turn: SZ. RW is audit cleanup only while
its shared import closure is rebuilding. No framework README or frontier-map edits.

## Log

- 2026-10-18 — opened before further hard proof work. RH remains open.
