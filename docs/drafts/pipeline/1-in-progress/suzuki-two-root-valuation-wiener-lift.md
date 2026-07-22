# Suzuki two-root valuation Wiener lift

- **ID:** `suzuki-two-root-valuation-wiener-lift`
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** M. Suzuki, *Weil's quadratic form via the screw function*,
  arXiv:2606.09096v1; `docs/handover/connes.md` Sections 57--59
- **Statement:** Every completed Suzuki zero mode admits an exact two-endpoint Wiener--Hopf
  representation whose high-frequency inverse lies in the weighted valuation Wiener algebra;
  the remaining RH-bearing assertion is injectivity of the resulting two-port boundary return
  operator.

## Goal

Replace the spatially dense seam problem by a coefficient-space problem on the prime-valuation
lattice.  Prove, rather than assume, that all propagated seam amplitudes are absolutely summable
and slaved to two exterior endpoint amplitudes.  Then attack the only remaining corona equation as
a two-port Wiener--Hopf kernel, not as an uncontrolled countable family of local punctured germs.

The target is source-pure.  It uses Suzuki's actual finite-aperture von-Mangoldt translation
polynomial and polar--Gamma multiplier.  It contains no Xi-zero data and assumes neither RH nor a
positivity statement equivalent to RH.

## Gates

- [x] 0 → 1  in-progress: exact representation, bridge theorem, falsifiers, and open core stated
- [ ] 1 → 2  fully-proven: construct Suzuki endpoint Hardy amplitudes on the completed form domain
  and prove the two-port boundary return kernel is zero for every aperture
- [ ] 2 → 3  formalized: formalize only after the concrete logarithmic multiplier and completed
  form domain exist in Lean
- [ ] 3 → 4  publication-ready: standalone theorem, proof, source-normalization audit, Lean
  certificate, and external novelty audit

## 1. Why physical seam localization is the wrong carrier

For fixed aperture `a`, only finitely many prime powers satisfy `p^j <= exp(2a)`, but their iterated
translations generate a dense subset of the interval.  Consequently no construction based on
pairwise disjoint punctured spatial neighborhoods can control all seam grades simultaneously.
This is a representation obstruction, not evidence that the seam series diverges.

Let `P_a` be the finite set of visible primes and put

```text
Gamma_a = Z^(P_a),
lambda(nu) = sum_(p in P_a) nu_p log p.                  (1)
```

Unique factorization makes `lambda` injective.  Work in the convolution Banach algebra

```text
W_a = ell^1(Gamma_a),
||c||_W = sum_nu |c_nu|.                                (2)
```

Its characters are

```text
Ev_xi(c) = sum_nu c_nu exp(-i xi lambda(nu)),
|Ev_xi(c)| <= ||c||_W.                                  (3)
```

Thus dense physical phases are harmless whenever the coefficient family is in `W_a`: evaluation
converges absolutely and uniformly in the phase variable.

## 2. Exact finite-aperture multiplier split

After removal of the principal polar--Gamma logarithm, Suzuki's real high-frequency multiplier has
the form

```text
p_a(xi) = kappa L(xi) + q_a(xi) + Ev_xi(t_a),            (4)
L(xi) = log <xi>,   kappa > 0,
sup_(|xi|>=Xi_0) |q_a(xi)| <= C_a,
t_a = -sum_(p^j<=exp(2a)) (log p)/p^(j/2)
        (delta_(j e_p) + delta_(-j e_p)).                (5)
```

The common minus sign is Suzuki's prime-translation convention; reversing the convention changes
only alternating signs below.  Digamma asymptotics give bounded `q_a`; polar rational terms decay.
The finite translation mass is

```text
M_a = ||t_a||_W
    = 2 sum_(p^j<=exp(2a)) (log p)/p^(j/2) < infinity.   (6)
```

Formula `(4)` is the exact source connector that an abstract almost-periodic model lacks.  Its
normalization still has to be copied line by line from Suzuki when the analytic realization is
built; no argument below depends on a guessed value of `kappa`.

## 3. `[PROVED HERE]` valuation-Wiener resolvent theorem

Let `Gamma` be any discrete abelian group, `W=ell^1(Gamma)`, `t in W`, `kappa>0`, and let
`q(L)` be scalar with `|q(L)|<=C`.  For

```text
h_L = kappa L delta_0 + q(L) delta_0 + t                (7)
```

and `kappa L>C+||t||_W`, the element `h_L` is invertible in the unitized convolution algebra and

```text
h_L^(-1)
 = 1/(kappa L) sum_(k>=0)
     [-(q(L)delta_0+t)/(kappa L)]^(*k),                 (8)

||h_L^(-1)||_W <= 1/(kappa L-C-||t||_W).               (9)
```

The remainder after grade `N` satisfies

```text
||h_L^(-1)-1/(kappa L)sum_(k=0)^N
   [-(q(L)delta_0+t)/(kappa L)]^(*k)||_W
 <= 1/(kappa L) * rho_L^(N+1)/(1-rho_L),                (10)
rho_L=(C+||t||_W)/(kappa L)<1.                          (11)
```

### Proof

Factor `(7)` as

```text
h_L = kappa L [delta_0 + (q(L)delta_0+t)/(kappa L)].    (12)
```

The second summand has `W`-norm at most `rho_L<1`.  The Banach-algebra geometric series gives
`(8)`.  Summing its norm majorant gives `(9)`, and summing the tail beginning at `N+1` gives `(10)`.
`QED`

This is a standard Banach-algebra bridge.  The Suzuki-specific advance is the identification of
`t=t_a` and the consequences for the seam system.

## 4. `[PROVED HERE]` first-arrival coefficient cannot cancel

Assume all nonzero coefficients of `t` have one common sign.  For `nu in Gamma`, define its
translation distance

```text
d(nu)=min {k : (t^(*k))_nu != 0}.                       (13)
```

If `d(nu)=d<infinity`, then

```text
(h_L^(-1))_nu
 = (-1)^d (t^(*d))_nu /(kappa^(d+1)L^(d+1))
   + O(L^(-d-2)).                                      (14)
```

In particular the leading coefficient is nonzero and its absolute value is the positive weighted
sum of all shortest prime-translation words reaching `nu`.

### Proof

Terms of `(8)` with `k<d` cannot reach `nu`.  In the `k=d` term, any occurrence of the zero-step
factor `q(L)delta_0` would leave fewer than `d` nonzero translations, again impossible by
minimality.  Hence its `nu` coefficient is exactly `(-1)^d(t^(*d))_nu/(kappa L)^(d+1)`.
Every term with `k>=d+1` is bounded in `W`-norm by the geometric tail in `(10)`, which is
`O(L^(-d-2))`.  Common sign prevents cancellation inside `t^(*d)`. `QED`

This proves more than formal collision classification: the full infinite seam expansion converges
absolutely at high logarithmic frequency, and every reachable seam has a nonzero first-arrival
coefficient.  No enumeration of dense spatial neighborhoods is required.

## 5. `[PROVED HERE]` exact two-root exterior reduction

Let `I_a=(-a,a)`, extend a zero mode `v` by zero to the line, and denote the translation-invariant
restricted-Weil distribution by `P_a`.  Distributionally,

```text
(A_a v)|_(I_a)=0
  iff b:=P_a v_tilde has support in (-infinity,-a] union [a,infinity). (15)
```

Split `b=b_-+b_+` with the two indicated half-line supports.  Translation of half-line
distributions gives exact Fourier factors

```text
bhat(xi)=exp(+i a xi) B_-(xi)+exp(-i a xi) B_+(xi),      (16)
p_a(xi)vhat(xi)
 =exp(+i a xi)B_-(xi)+exp(-i a xi)B_+(xi).              (17)
```

Here `B_-` and `B_+` are boundary values of opposite half-plane distributional Hardy classes when
the source has the corresponding `L2` regularity.  Formula `(16)` itself needs only temperedness
and the support split.  For sufficiently large `|xi|`, `(9)` makes `p_a(xi)` nonzero, so `(17)`
may there be divided by `p_a`; no global nonvanishing is assumed.

Apply `(8)` in the two-root module

```text
M_a = W_a e_- direct-sum W_a e_+.                       (18)
```

Then every prime seam descendant is slaved to the two amplitudes `(B_-,B_+)`, with absolute
coefficient convergence and bound `(9)`.  At resonant apertures the evaluated physical phases of
the two roots may coincide, but they remain distinct in `M_a`; their opposite one-sided boundary
orientations recover the labels.  Thus there is no countable family of independent seam data.

### Proof

Equation `(15)` is the definition of compression after zero extension.  Any distribution supported
in the displayed disjoint half-lines splits into two supported distributions (assign endpoint
atoms consistently).  Translating these supports to the origin gives `(16)`.  Fourier
diagonalization of `P_a` gives `(17)` globally as a distributional product.  High-frequency
division is guaranteed by `(9)`.  Convolution of the coefficient inverse `(8)` with each root
component gives the asserted high-frequency module expansion. `QED`

## 6. The actual frontier: a two-port Wiener--Hopf kernel

The preceding theorems close three problems previously grouped together:

```text
dense seam overlap,
convergence of all valuation grades,
first-arrival cancellation.                             (19)
```

They do **not** prove RH.  The exterior amplitudes in `(16)` can still contain inverse-log-flat or
continuous boundary content.  Compact support of `v` imposes a coupled Hardy support condition on
`(17)`.  The exact two-port matching problem is

```text
find V in PW_a and opposite Hardy amplitudes B_-, B_+ such that
p_a V=exp(+ia xi)B_-+exp(-ia xi)B_+,
B_- in H_+,  B_+ in H_-.                                (20)
```

Here `V=vhat`, and all spaces in `(20)` mean their distributional logarithmic form-domain
versions.  This formulation retains possible finite-frequency zeros of `p_a`: at such points
`(20)` imposes divisibility rather than illegally dividing by the symbol.  On the high-frequency
tail, `(8)` solves `(20)` explicitly in the two-root valuation module.

### `SUZUKI-TWO-PORT-RETURN-INJECTIVITY`

`[CONJECTURE; RH-BEARING OPEN CORE]` For every `a>0`, the only triple `(V,B_-,B_+)` in the
completed Suzuki boundary classes satisfying `(20)` is `(0,0,0)`.

By `(15)`--`(17)`, this is equivalent to `ker A_a=0` for every aperture, hence to RH through
Suzuki's theorem.  It is not offered as a proof.  Its value is that the previously countable dense
corona transport has been reduced rigorously to two Hardy amplitudes, and its entire high-frequency
prime propagation is now an explicit absolutely convergent Neumann series.

The first non-circular subproblem is:

```text
TRACE-ZERO ENDPOINT CLASSIFICATION:
if both half-log coefficients of B_- and B_+ vanish, prove that (17) is H1;
equivalently exclude inverse-log-flat elements of the two-port Hardy kernel. (21)
```

After `(21)`, the existing connector sends the trace-zero channel to the raw screw kernel.  The two
remaining source theorems are then exactly:

```text
CORONA: no nonzero half-log pair satisfies the two-port return law;
REGULAR: det(M_a^* M_a)>0 for the raw Evans map at every a. (22)
```

## 7. Hostile audit and falsifiers

1. `[(8) IS NOT RH]` It is high-frequency inversion only.  A low-frequency two-port mode can still
   satisfy `(20)`.
2. `[SOURCE DOMAIN]` The completed space `H(S_(a,mu))` is not contained in `L2`.  Hardy labels and
   Fourier products in `(16)`--`(20)` must be constructed on Suzuki's actual logarithmic form
   domain, not imported from the raw `L2_0` model.
3. `[FLAT AMPLITUDE]` An arbitrary flat factor such as `exp(-sqrt(log <xi>))` multiplying both root
   amplitudes survives the algebraic Neumann expansion.  Source-specific endpoint regularity is
   required to exclude it.
4. `[RESONANCE]` At `exp(2a)=mn`, two evaluated roots can occupy the same physical phase.  Treating
   evaluation as injective is false; the direct-sum root label and one-sided orientation are
   essential.
5. `[NORMALIZATION]` If Suzuki's exact multiplier contains an additional unbounded term after the
   principal logarithm is removed, bound `(6)` is insufficient.  This is a direct source-check
   falsifier.
6. `[NO POSITIVITY SMUGGLING]` Positivity or contractivity of the full return operator may not be
   assumed: either would already carry the RH content.

## 8. Corpus and external audit

Corpus already contains:

- prime-log independence and finite Laurent collision laws in
  `SuzukiPrimeValuationSeam.lean`;
- finite exponential-pencil Cesaro coefficient extraction in
  `FiniteExponentialPencilMeanSquare.lean`;
- one theta-cusp-specific absolutely convergent finite-prime translation series in
  `ThetaCuspFinitePrimeSource.lean`.

Corpus does not contain Suzuki's weighted valuation-Wiener inverse, the two-root exterior module,
or the exact reduction `(20)`.  Shubin's almost-periodic pseudodifferential calculus and Wahlberg's
Besicovitch representations establish the general parent setting.  The Banach-algebra Neumann
argument is standard.  Therefore:

```text
weighted Wiener inverse theorem                  [BRIDGE]
Suzuki finite-aperture identification (4)--(6)  [BRIDGE; SOURCE CHECK PENDING]
two-root valuation reduction (15)--(20)         [NOVELTY UNVERIFIED]
two-port return injectivity                     [CONJECTURE; RH-EQUIVALENT]
```

No Lean wrapper is warranted yet.  The formal tree lacks the concrete Suzuki logarithmic
multiplier, completed form domain, exterior support split, and Hardy boundary spaces; formalizing
only `(8)` would certify a standard bridge while leaving every RH-bearing connector open.

## Log

- 2026-07-22 — created directly in stage 1 after corpus audit; replaced Besicovitch `ell^2` carrier
  by stronger weighted Wiener `ell^1` carrier; proved absolute convergence, resolvent remainder,
  first-arrival noncancellation, and exact two-root exterior reduction; isolated two-port
  Wiener--Hopf injectivity as the remaining RH-bearing problem.
- 2026-07-22 — priority correction after full `RiemannHypothesisSOTA2026` audit: this is a valid
  secondary finite-frequency matching reduction, not current main Suzuki frontier.  Later formal
  source chain reaches causal entry-wall light completion and rectangular Ward assembly directly.
  Main live card is `suzuki-coherent-fusion-gamma-weld.md`; no claim in this card proves its trace
  identity or Ward lower bound.
