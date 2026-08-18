# CCM canonical-head completed-error producer

- **ID:** CCM-O-HEAD-D
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** Route O canonical exact-ground Gamma--Slepian heads; CCM-FU/UR completed current
- **Statement:** For every positive aperture and every canonical actual Gamma--Slepian ground head, the complete archimedean energy plus the signed completed-error pairing of its literal aperture autocorrelation is nonnegative.

## Goal

Construct the missing source-side producer, not another receiver: prove the literal finite
von-Mangoldt compression cannot exceed identity, scalar Gamma, and polar energy on canonical
actual ground heads.  Via the established canonical-head convergence and nested-floor theorem,
this yields nonnegative restricted-Weil floors and RH.  Common-clock, reporter-only, and
separately-positive prime/polar replacements are inadmissible.

## Gates

- [x] 0 -> 1 in-progress: exact source-pure claim; canonical heads and completed current are literal
- [ ] 1 -> 2 fully-proven: dependency-closed paper proof, `[PAPER-PROVED]`, no open implication
- [ ] 2 -> 3 formalized: exact unconditional Lean theorem, targeted leaf build and axiom audit
- [ ] 3 -> 4 publication-ready: standalone theorem/proof/Lean certificate/priority audit

## Exact notation

For aperture `a`, let `h_(a,n)` be the corpus's canonical projection of the exact restricted-Weil
ground onto a finite peripheral Gamma--Slepian head and let `v_(a,n)` be its physical zero-extended
aperture vector.  Put

```text
C_(a,n)(t) = integral_R v_(a,n)(x+t) conjugate(v_(a,n)(x)) dx,
D(t)       = 4 sinh(t/2) - sum_(2 <= m <= exp t) Lambda(m)/sqrt(m).
```

On differentiable heads the established Stieltjes law identifies polar minus prime with
`-2 Re integral_(0,2a] D(t) C'_(a,n)(t) dt`; without differentiability use the original signed
Stieltjes pairing.  Exact producer target is the corresponding signed pairing plus complete
archimedean quadratic energy `>= 0`, equivalently
`CCMRestrictedWeilCanonicalGroundHeadReversePrimeBound a n`.

## Approach

Audit only source-faithful mechanisms acting on `C_(a,n)`: completed-error Stieltjes integration,
the exact Gamma--Slepian ground equation, head/tail shifted-defect identity, and possible
prime--polar square/Schur decompositions.  Hostile tests must reject any law valid only for a
reporter, a common clock, separate absolute estimates, fixed positive margin, or an assumed RH
continuation.

## Live claim

- `[OPEN CORE]` Produce a non-circular signed order or square law for the completed-error pairing
  on `C_(a,n)` that pays the complete Gamma energy and is stable under the canonical head limit.

## No-go closure

- **Exact killing theorem/mechanism:** A derivative pairing `-2 Re int D(t) C'(t) dt` is not a
  lawful actual-head theorem at form-domain regularity.  Common-clock substitution changes the
  operator, while the Gamma-head projection commutator only reproduces the already-known tail
  defect and retains the unknown exact-ground floor.
- **Strongest positive survivor:** The literal source has an exact regularity-free defect balance:
  complete Gamma form energy plus the signed endpoint completed error plus a nonnegative atomwise
  prime translation loss, minus the actual polar autocorrelation debt.  On canonical heads its
  nonnegativity is exactly literal reverse-prime control.
- **New insight:** Prime--polar--Gamma cancellation can be preserved without differentiating the
  autocorrelation.  Each prime pair is scalar mass minus a squared translation defect; after
  subtracting polar endpoint mass, the sole scalar remainder is `2 D(2a) ||v||^2`.  Thus the open
  sign is a comparison of two explicit autocorrelation defects, not an undefined Stieltjes
  pairing on a rough head.
- **Status:** Stage 1.  Exact balance and equivalence are paper-proved and Lean-formalized; the
  RH-bearing inequality asserting balance nonnegativity on canonical heads remains open.

## Log

- 2026-08-17 -- created after corpus search isolated the actual-head completed-error pairing as the
  only lawful Route O / CCM-FU interface; fixed positive head margin already closed negatively.
- 2026-08-18 -- hostile-tested forcing-complement, first-contact regularity, optimal-transport,
  trace/tilt, and Gamma-commutator candidates.  Retained the regularity-free atomwise defect
  decomposition and formalized it in
  `CCMRestrictedWeilCanonicalHeadCompletedErrorControl.lean`.

## Exact regularity-free producer balance

Let `U_h` be logarithmic translation on the physical aperture space, `f = A_a u`, and

```text
J_prime(a,f) = sum_(2 <= m <= exp(2a))
  Lambda(m)/sqrt(m) * ||U_(log m) f - f||^2,

J_polar(a,f) = 8 sinh(a) ||f||^2 - Re <P_a f,f>.
```

Unitarity and `U_h^* = U_(-h)` give, atom by atom,

```text
Re <T_m f,f> = 2/sqrt(m) ||f||^2
  - 1/sqrt(m) ||U_(log m)f-f||^2.
```

After summing with `Lambda(m)`, expanding the literal bounded remainder, and using
`D(2a) = 4 sinh(a) - M_prime(2a)`, one obtains the exact identity

```text
Q_a(u) = ||u||_GammaForm^2
  + (2 gammaHardyPhaseRate(0) - 1 + 2 D(2a)) ||f||^2
  + J_prime(a,f) - J_polar(a,f).
```

Both defect carriers are defined on actual `L2` heads.  `J_prime >= 0` follows termwise.
The exact polar-vector norms are

```text
||p_(1/2)||^2 = ||p_(-1/2)||^2 = 2 sinh(a),
```

so Cauchy--Schwarz gives `Re <P_a f,f> <= 4 sinh(a)||f||^2` and hence `J_polar >= 0`.
No smoothness, endpoint-zero condition, or autocorrelation derivative occurs.

For `u = h_(a,n)`, Lean proves

```text
literal reverse-prime bound on h_(a,n)
  iff 0 <= completed-error defect balance(a,h_(a,n)).
```

It also welds the new balance to the exact canonical head/tail theorem:

```text
balance(a,h_(a,n))
  = epsilon_a ||v_(a,n)||^2 + headTailDefect(a,n),

0 <= headTailDefect(a,n) <= sourceAlignedRate(a,n).
```

This is the literal vanishing head error, not a fixed coercive margin.

The exact remaining theorem is therefore the source-derived comparison

```text
J_polar(a,v_(a,n)) <= ||h_(a,n)||_GammaForm^2
  + (2 gammaHardyPhaseRate(0) - 1 + 2 D(2a)) ||v_(a,n)||^2
  + J_prime(a,v_(a,n))
```

eventually in `n`, with its vanishing head error.  Proving this comparison closes the fixed-
aperture floor; the present identity does not assume or disguise that sign.

## 2026-08-18 actual-head cancellation closure

Corpus-first hostile audit killed scalar Gamma-Levy, parity, common-clock, conservative-dilation,
and modewise Schur candidates as producers: each either leaves the counter-phased von Mangoldt
observable unchanged or restates the unknown ground sign.  The surviving same-head law is new:
for every complex physical aperture vector `f` in the actual `L2` Hilbert space, define

```text
E_f(h) = ||U_h f - f||^2.
```

Then the full polar debt is not an independent negative carrier.  It has the exact rough-head
representation

```text
J_polar(a,f) = integral_[0,2a] 2 cosh(h/2) E_f(h) dh.
```

Proof uses literal mixed CCM polar factorization on the strict-interior smooth source, joint strong
continuity of logarithmic translations, continuity of the compact-lag defect integral in `f`, and
density of the smooth physical source image.  No derivative of `C_f`, pointwise representative,
or common-clock bridge occurs.  Endpoint overlap of an aperture vector with its `2a` translate is
null, so

```text
E_f(2a) = 2 ||f||^2.
```

Hence prime, polar, and completed endpoint are one signed quadrature on the same actual-head
profile:

```text
X_D(a,f) = D(2a) E_f(2a)
  + sum_(2 <= m <= exp(2a)) Lambda(m)/sqrt(m) E_f(log m)
  - integral_[0,2a] 2 cosh(h/2) E_f(h) dh.

Q_a(u) = ||u||_GammaForm^2
  + (2 gammaHardyPhaseRate(0) - 1) ||f||^2 + X_D(a,f).
```

This is the literal completed-error Stieltjes action on an actual rough head, expressed without
illegal integration by parts.  Lean module
`CCMRestrictedWeilActualHeadCompletedErrorProducer.lean` proves the all-`L2` polar law, endpoint
law, source identity, canonical Gamma--Slepian ground-plus-tail identity, and exact equivalence of
canonical-head producer nonnegativity with the literal reverse-prime bound.  Remaining RH-bearing
core is now sharply only the sign of this single quadrature-plus-Gamma expression on canonical
Gamma--Slepian heads; convergence/definition and prime--polar cancellation are closed.

## 2026-08-18 prime--polar--Gamma same-head producer

Corpus and current Suzuki/CCM audit isolated one missing carrier: literature identifies the Gamma
form spectrally and extends it to the complete form domain by closure, but does not give an exact
positive translation-defect formula on the literal rough physical head. A universal pointwise
Gamma--polar autocorrelation sign was hostile-killed because finite Gamma--Slepian projections may
have negative autocorrelations. The surviving statement uses squared increments and requires no
pointwise sign.

For `h > 0`, set

```text
k_Gamma(h) = exp(-h/2) / (1 - exp(-2h)).
```

The quarter-line Binet series, summed with absolute integral control, gives the exact scalar law

```text
integral_(0,infinity) (2 - 2 cos(2 pi xi h)) k_Gamma(h) dh
  = 2 (gammaHardyPhaseRate(2 pi xi) - gammaHardyPhaseRate(0)).
```

Tonelli plus unitary Fourier Plancherel then proves, for every actual complex `L2` head `f`,

```text
GammaDefect(f)
  := integral_(0,infinity) k_Gamma(h) ||U_h f - f||^2 dh
   = integral_R 2 (gammaHardyPhaseRate(2 pi xi) - gammaHardyPhaseRate(0))
       |f_hat(xi)|^2 dxi.
```

This theorem is on the head itself, not a smooth approximation or a separately chosen reporter.
For every complete CCM form vector `u` with literal physical aperture head `f = A_a u`, it yields

```text
GammaDefect(f) = ||u||_GammaForm^2 - ||f||^2.
```

Consequently the cancellation-preserving producer has the single-head form

```text
P_PPGamma(a,u)
  = 2 gammaHardyPhaseRate(0) ||f||^2
    + GammaDefect(f)
    + D(2a) E_f(2a)
    + sum_(2 <= m <= exp(2a)) Lambda(m)/sqrt(m) E_f(log m)
    - integral_[0,2a] 2 cosh(h/2) E_f(h) dh,

E_f(h) = ||U_h f - f||^2.
```

Lean proves unconditionally

```text
P_PPGamma(a,u) = Q_a(u),

P_PPGamma(a,h_(a,n))
  = epsilon_a ||v_(a,n)||^2 + headTailDefect(a,n),

literal reverse-prime bound on h_(a,n)
  iff 0 <= P_PPGamma(a,h_(a,n)).
```

Formal modules:

- `CCMActualHeadGammaAutocorrelationEnergy.lean`
- `CCMRestrictedWeilActualHeadPrimePolarGammaProducer.lean`

Both are wired into `RHTower.lean`; targeted leaf builds and standard-axiom audits pass. This
closes Gamma convergence/positivity and creates the requested signed common-head producer while
preserving prime--polar--Gamma cancellation. RH-bearing open core is now only nonnegativity of
this explicit functional on canonical finite heads; no undefined Gamma term, rough-head limit, or
operator bridge remains inside the statement.

## 2026-08-18 reflected wall-Gram signed producer

Corpus-first comparison of Route O and Suzuki's wall construction exposes a common source block
without identifying their distinct operators. For `n = p^(e+1)`, define the Mellin wall

```text
Omega_n(xi) = sqrt(Lambda(n)/sqrt(n)) exp(i pi xi log n).
```

Its functional-equation reflected chord satisfies the exact atomic law

```text
|Omega_n(xi) - Omega_n(-xi)|^2
  = Lambda(n)/sqrt(n) * (2 - 2 cos(2 pi xi log n)).
```

At every prime power, `Omega_n(xi)` is literally Suzuki's wall field at height `2 pi xi`.
Therefore Route O's prime translation loss and Suzuki's far current are the real and imaginary
polarizations of the same reflected anti-diagonal entry of Suzuki's positive rank-one two-height
Gram:

```text
Re K(t,-t) = Lambda(n)/sqrt(n) cos(t log n),
Im K(t,-t) = Lambda(n)/sqrt(n) sin(t log n),
|W(t)-W(-t)|^2 = 2 Lambda(n)/sqrt(n) - 2 Re K(t,-t).
```

Plancherel lifts the real chord polarization against the spectral density of the actual physical
head, atom by atom and through the finite arithmetic head, to the literal prime translation-defect
energy. Substitution into the completed-error producer yields `P_WallGram`, with Lean proving
unconditionally

```text
P_WallGram(a,u) = P_PPGamma(a,u) = Q_a(u),

P_WallGram(a,h_(a,n))
  = epsilon_a ||v_(a,n)||^2 + headTailDefect(a,n),

literal reverse-prime bound on h_(a,n)
  iff 0 <= P_WallGram(a,h_(a,n)).
```

Formal module `CCMActualHeadWallGramSignedProducer.lean` is wired into `RHTower.lean`; targeted
Lean check, leaf build, and standard-foundation axiom audit pass. This removes the prior lawful
bridge obstruction: common-clock and Gamma--Slepian heads remain distinct, but their prime source
channels now meet inside one literal PSD wall Gram. It does not prove the RH-bearing sign. Exact
remaining core is signed domination of the continuous polar debt by Gamma autocorrelation plus
the reflected wall-Gram chord energy on canonical Gamma--Slepian heads.

## 2026-08-18 first-Gamma-mode / outgoing-polar reduction

The next conjecture loop first tested a universal lag-metric comparison between prime samples and
the polar continuum. It was killed before formalization: on arbitrary aperture heads it would imply
the full restricted-Weil sign and contradict the corpus equivalence between negative directions and
failure of the reverse-prime bound. Canonicality cannot enter through generic subadditivity of
`sqrt(E_f)`.

The surviving source identity begins with the exact Binet decomposition

```text
k_Gamma(h) = exp(-h/2) + k_Gamma,>=1(h),
k_Gamma,>=1(h)
  = exp(-h/2) exp(-2h) / (1-exp(-2h))
  = sum_(n>=1) exp(-2(n+1/4)h).
```

The first coefficient `exp(-h/2)` is literally the real Cauchy-height Gram of Suzuki wall phases
at source separation `h`. This is a common scalar source kernel, not an identification of the
common-clock and Gamma--Slepian operators.

For an actual aperture head, `E_f(h)=2||f||^2` whenever `h>2a`. Hence the first Gamma mode has the
exact aperture split

```text
integral_(0,infinity) exp(-h/2) E_f(h) dh
  = integral_[0,2a] exp(-h/2) E_f(h) dh
    + 2 exp(-a) E_f(2a).
```

At the same time,

```text
integral_[0,2a] 2 cosh(h/2) E_f(h) dh
  = integral_[0,2a] exp(h/2) E_f(h) dh
    + integral_[0,2a] exp(-h/2) E_f(h) dh.
```

Thus Gamma's first Binet mode cancels the entire decaying half of the polar debt. Its exterior tail
joins the completed endpoint, producing the exact coefficient collapse

```text
D(2a) + 2 exp(-a)
  = 2 exp(a) - M_prime(2a).
```

Define the outgoing producer on `f=A_a u`, with spectral head `g`, by

```text
P_out(a,u)
  = 2 gammaHardyPhaseRate(0) ||f||^2
    + GammaHigher(f)
    + (2 exp(a)-M_prime(2a)) E_f(2a)
    + sum_(2<=m<=exp(2a)) integral_R |Omega_m(xi)-Omega_m(-xi)|^2 |g(xi)|^2 dxi
    - integral_[0,2a] exp(h/2) E_f(h) dh.
```

Lean proves unconditionally

```text
P_out(a,u) = P_WallGram(a,u) = Q_a(u),

P_out(a,h_(a,n))
  = epsilon_a ||v_(a,n)||^2 + headTailDefect(a,n),

literal reverse-prime bound on h_(a,n)
  iff 0 <= P_out(a,h_(a,n)).
```

Formal module: `CCMActualHeadGammaWallOutgoingProducer.lean`. Corpus search found no prior
actual-head first-Binet-mode cancellation or outgoing-error coefficient theorem. This is a strict
frontier reduction, not a sign proof: the remaining RH-bearing task is signed control of the one
growing polar continuum against the positive higher-Gamma modes, reflected prime-wall chords, and
the literal outgoing arithmetic endpoint on canonical Gamma--Slepian heads.

## 2026-08-18 completed-error autocorrelation current

### Killed conjecture: positive canonical autocorrelation

The tempting route was to choose the exact restricted-Weil ground nonnegative, infer
`C_f(h)>=0`, and compare the arithmetic samples with the polar continuum. Corpus audit kills this
before any new conjecture is used: `SuzukiScrewDisjointCrossCoupling.lean` proves that for large
aperture no scalar shift of the full screw-regular form satisfies the first Beurling--Deny
criterion. Hence there is no positivity-preserving semigroup or modulus-ground theorem available
for the operator that selects the canonical head. Parity survives; pointwise autocorrelation
positivity does not.

### Surviving exact current

For one actual physical head put

```text
C_f(h)=Re(<U_h f,f>+<U_(-h)f,f>)/2,
E_f(h)=2||f||^2-2C_f(h).
```

Substitution into the completed-error quadrature gives a cancellation not previously present in
the corpus. With `L=2a`, `M(L)=sum_(n<=exp L) Lambda(n)/sqrt(n)`, and
`D(L)=4sinh(L/2)-M(L)`, one has exactly

```text
D(L)E_f(L)
  + sum_(n<=exp L) Lambda(n)/sqrt(n) E_f(log n)
  - integral_[0,L] 2cosh(h/2)E_f(h)dh

= 2 integral_[0,L] 2cosh(h/2) C_f(h)dh
  - 2 sum_(n<=exp L) Lambda(n)/sqrt(n) C_f(log n).
```

All scalar completed endpoint, polar mass, and cumulative prime mass cancel. This is a
regularity-free Stieltjes integration-by-parts law: it uses continuous `L2` translation
autocorrelation, not an unproved derivative or bounded variation of `C_f`.

After the already-proved first-Gamma-mode cancellation, the same identity sharpens to

```text
P_boundary(a,u)
 = (4+2 gammaHardyPhaseRate(0))||f||^2
   + GammaHigher(f)
   + 2 integral_[0,2a] exp(h/2) C_f(h)dh
   - 2 sum_(n<=exp(2a)) Lambda(n)/sqrt(n) C_f(log n).
```

Lean proves unconditionally

```text
P_boundary(a,u)=P_out(a,u)=Q_a(u),

P_boundary(a,h_(a,n))
  = epsilon_a||v_(a,n)||^2+headTailDefect(a,n),

literal reverse-prime bound on h_(a,n)
  iff 0<=P_boundary(a,h_(a,n)).
```

This identifies the hard producer with a signed boundary-transfer current rather than a bulk
translation-loss comparison. The singular higher-Gamma term remains in defect form; separating
its norm and autocorrelation pieces would create two divergent integrals and destroy the lawful
Gamma cancellation.

Primary-source novelty audit against Suzuki's June 2026 *Weil's quadratic form via the screw
function*, Suzuki's 2025 Hilbert-space paper, and Connes--Consani--Moscovici's 2025 *Zeta Spectral
Triples* found only RH-equivalent screw positivity and conjectural finite-interval operator or
determinant convergence. None states this actual-head mass cancellation or the outgoing
boundary-current identity.

Formal module: `CCMActualHeadCompletedAutocorrelationProducer.lean`, wired into `RHTower.lean`.
The remaining hard theorem is now precise: sign the last displayed current on canonical
Gamma--Slepian heads cofinally while retaining the nonnegative vanishing head defect. Generic
autocorrelation positivity, scalar pole domination, and splitting the higher-Gamma singularity are
all forbidden pivots.
