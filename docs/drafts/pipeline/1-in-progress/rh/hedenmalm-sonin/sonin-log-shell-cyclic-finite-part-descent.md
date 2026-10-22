# Sonin log-shell cyclic finite-part descent

- **ID:** `sonin-log-shell-cyclic-finite-part-descent`
- **Stage:** 1-in-progress, active
- **Type:** FRONTIER BRIDGE with formalized principal cyclic layer
- **Source:** right-to-left from Connes finite-part source class to Sonin three-grade carrier
- **Statement:** The physical/Fourier principal-shell algebra admits a canonical Fourier-symmetric
  semifinite trace whose cutoff-translation cocycle is logarithmic shell length.  The exact Sonin
  projection changes its principal representative by a trace-class time-band term, so this shell
  trace and the ordinary trace of the residual combine into a well-defined cyclic finite-part
  functional with prime-power density `log(p) * p^(-m/2)`.

## Goal

Close the rightmost source-side gap before completed positivity: descend the already fixed Connes
prime finite part through the actual Sonin projection/resolvent without a guessed normalization,
without squaring Euler coefficients, and without using the Xi divisor.

If successful, the right-hand RH chain becomes

```text
Connes prime--Gamma finite part
  -> exact Sonin principal--relative cyclic functional
  -> completed Sonin/CCM contraction [OPEN]
  -> all-degree Weil positivity
  -> RH.
```

This does not assert the contraction or RH.

## Exact candidate

Put the even radial physical channel in logarithmic coordinates.  Let

```text
(U_h f)(x)=f(x-h),        P=M_(1_[0,infinity)).
```

For `h>0`,

```text
U_(-h)[P,U_h]=P_(-h)-P=M_(1_[-h,0)),                    (1)
```

where `P_t=M_(1_[t,infinity))`.  In the algebraic crossed product of logarithmic step
functions by the prime-translation group, the canonical semifinite trace is

```text
tau(sum_g f_g U_g)=integral f_0.
```

Consequently

```text
tau(U_(-h)[P,U_h])=h.                                   (2)
```

For `h=m log p` and the Euler-logarithm coefficient `p^(-m/2)/m`, `(2)` gives

```text
(p^(-m/2)/m) tau(U_(-h)[P,U_h])
  =log(p) p^(-m/2),                                     (3)
```

the unsquared local prime flux.  No bounded response is being normalized to equal `h`; the
unbounded length is intrinsic to a finite-trace shell projection.

The Fourier branch is the conjugate polarization.  Fourier symmetry forces equal channel weights;
the normalized two-polarization functional is their average, so a diagonal physical-plus-Fourier
shell again has value `h`, not `2h`.

## Proposed Sonin descent

### Corpus correction and principal cyclic layer (2026-07-22)

The original gate list below became stale. `SoninPrincipalRelativeIdeal.lean` already proves that
the actual quadratic Gram corner differs from its shell representative by the retained exact
principal-relative ideal, proves multiplication closure modulo that ideal, and proves finite-prime
principal/residual uniqueness. `CCMSoninFiniteWordFaithfulness.lean` proves a stronger faithful
zero/live normal form and exact associativity of its tropical product.

`SoninPrincipalShellCyclicTrace.lean` now closes the next connector. For a live canonical window
`d=(C,F,x)`, define

```text
tau_a(d) = log(C)-log(F),  if x=1,
           0,              otherwise,
tau_a(0)=0.                                                   (P1)
```

Then for every positive aperture and all canonical states `s,t`,

```text
tau_a(s*t)=tau_a(t*s).                                      (P2)
```

The proof is source-specific. If the product displacement is not one, both sides vanish. If
`x y=1`, the reverse overlap window is exactly the `x`-dilate of the forward overlap window:

```text
C_(t*s)=x C_(s*t),        F_(t*s)=x F_(s*t).               (P3)
```

Thus live/zero status agrees and logarithmic width is unchanged. Faithfulness makes `(P1)`
Calkin-invariant on canonical normal states, and finite-support linearization gives a cyclic
bilinear trace pairing on the algebraic state core.

For a genuine CCM Gram factor with source scale `r` and target scale `q`, the trace diagonalizes
exactly:

```text
tau_a(Gram(r,q)) = if r=q then log(r) else 0.               (P4)
```

Hence a diagonal prime-power factor `r=p^(m)` returns `m log p`, independently of aperture, and
the Euler-logarithm coefficient `p^(-m/2)/m` gives exactly
`log(p) p^(-m/2)`. This is the fixed Connes nonarchimedean orbital coefficient, with no guessed
normalization.

What remains is no longer principal cyclicity or finite-place source matching. The canonical trace
is now extended through the exact fixed-aperture principal-relative ideal. Exact nested-aperture
analysis proves that restriction creates a positive noncompact lost-layer Gram defect. Hence
compatibility cannot live on the relative term. Exact principal reduction now identifies that
defect with an existing scale-one live shell. Retained plus lost shell mass is exactly `log r`,
and all remaining path curvature is Schatten-1. The next carrier needs no new principal reader.
Its ordinary trace is now the exact negative squared Hilbert--Schmidt norm of the successive-layer
transition, with an exact canonical Ward cancellation. The open connector is identification of
that forced Ward energy with the relative finite part of the concrete Burnol counterterm.

Let `J_TB` be the algebraic two-sided ideal generated by the mixed finite time-band blocks
`A_s R_t` and `R_s A_t`.  The project currently proves `J_TB subset S_2`.  The first strengthening
to prove is

```text
J_TB subset S_1.                                        (4)
```

Indeed `A_s F^* A_t` has the analytic finite-rectangle kernel

```text
exp(2 pi i x y)=sum_(n>=0) (2 pi i)^n x^n y^n/n!.
```

The sum of rank-one nuclear norms is finite on every rectangle.  Hence `A_s F^* A_t`, and therefore
`A_s R_t=(A_s F^* A_t)F`, is trace class; the adjoint generator is trace class as well.  Two-sided
ideal closure then proves `(4)`.  In particular the exact projection correction

```text
C_a=Q_a-(1-A_a-R_a)
```

and every bounded-observable corner response are trace class, not only Hilbert--Schmidt.

The existing Calkin shell proof must then be replayed without forgetting this stronger ideal:
the difference between each actual Sonin mixed Gram entry and its physical/Fourier shell-translation
representative lies in `J_TB subset S_1`.  For a finite prime family, existing Calkin faithfulness
implies the principal shell span intersects `J_TB` trivially.  Therefore every element of the
resulting principal--relative extension has a unique decomposition

```text
T=S+K,     S principal shell,     K in J_TB,              (5)
```

and one can define

```text
FP_Sonin(T)=tau_shell(S)+Tr(K).                           (6)
```

Fixed-aperture decomposition, linearity, bounded cyclicity, aperture-layer principal closure, and
orbital-mass conservation and exact Ward transgression are now closed. The cofinal proof
obligations are compatibility under enlarging the finite prime family and equality between the
forced relative Ward energy and Connes's finite part including the archimedean Burnol conductor
term.

## Trace-class strengthening: paper proof

`[PROVED HERE]` Fix `s,t>0` and write the finite-rectangle inverse-Fourier block as

```text
(K_(s,t)f)(x)=integral_[-t,t] exp(2 pi i x y) f(y) dy,
               x in [-s,s].                              (7)
```

On the rectangle the exponential series gives the rank-one expansion

```text
K_(s,t)=sum_(n>=0) c_n (u_n tensor v_n),
c_n=(2 pi i)^n/n!,
u_n(x)=x^n 1_[-s,s](x),
v_n(y)=y^n 1_[-t,t](y).                                  (8)
```

The rank-one nuclear masses are

```text
N_n=|c_n| ||u_n||_2 ||v_n||_2
   =(2 pi)^n/n! * 2 (s t)^(n+1/2)/(2n+1)
   <=2 sqrt(s t) (2 pi s t)^n/n!.                        (9)
```

Therefore

```text
sum_n N_n <= 2 sqrt(s t) exp(2 pi s t)<infinity.          (10)
```

For completeness, `(8)` supplies the factorization used by the formal project definition of
trace class.  Normalize the nonzero vectors in `(8)` to `uHat_n,vHat_n`, choose an orthonormal
bridge sequence `e_n` in `L2(R)`, put `d_n=sqrt(N_n)`, and absorb the phase of `c_n` into
`uHat_n`.  Define

```text
U f=sum_n d_n <vHat_n,f> e_n,
S z=sum_n d_n <e_n,z> phase(c_n) uHat_n.                  (11)
```

Both series define bounded maps by Cauchy--Schwarz.  Extending `e_n` to a Hilbert basis gives

```text
||U||_HS^2=sum_n N_n,       ||S||_HS^2=sum_n N_n,
S U=K_(s,t).                                                    (12)
```

Thus `K_(s,t)` is a product of two Hilbert--Schmidt maps.  Restriction/extension by the interval
cutoffs and right multiplication by the Fourier unitary preserve trace class, proving
`A_s R_t` trace class.  Its adjoint `R_t A_s` is trace class.  Finite sums and bounded two-sided
multiples preserve `S_1`, hence

```text
J_TB subset S_1.                                         (13)
```

The explicit bound `(10)` is not needed for source matching; it certifies convergence of the
nuclear factorization.  The proof uses no spectral estimates or prolate asymptotics.

### Consequence for the old linear-cross obstruction

The exact correction response factors as

```text
(1-Q_a) D C_a-C_a D (1-A_a-R_a).                         (14)
```

Since `C_a` is trace class, `(14)` is trace class for every bounded `D`.  In particular the
principal/residual linear Gram cross now has an ordinary trace; Koplienko subtraction is not
needed for the concrete Sonin residual.

This does **not** make the old bounded scalarization a source trace.  For the normalized dilation
sum, `||D||<=2`, so the trace norm of `(14)` is bounded by a constant depending only on aperture
and `||C_a||_1`, uniformly in `p^m`.  Any ordinary trace extracted solely from `(14)` is therefore
uniformly bounded, while the required response is `m log p`.  The positive survivor is sharper:
the residual is genuinely `S_1`, but all orbital-length growth is forced into the principal
semifinite shell trace `(2)`.

## Hostile falsifiers

The conjecture is killed if any of the following occurs.

1. The analytic rectangle expansion does not yield a factorization into two Hilbert--Schmidt
   operators on the actual `SoninL2` model.
2. A nonzero principal shell combination lies in `J_TB`, destroying uniqueness in `(5)`.
3. Products of principal representatives create compact errors outside `J_TB`.
4. `tau_shell` fails cyclicity on the required finite-prime crossed-product core.
5. The Fourier-symmetric normalization disagrees with the already fixed Connes local orbital
   coefficient.
6. The archimedean conductor correction is not trace-compatible with `(6)`.

Passing only `(1)`--`(3)` is not enough; those identities alone are standard cutoff-index
geometry and do not close the Sonin descent.

## Cofinal positivity obstruction

`SuzukiCofinalPositiveFinitePartNoGo.lean` rules out a previously implicit promotion of `(6)`.
At each finite prime set, `(6)` may be a finite linear trace. It cannot converge to a finite-valued
positive linear functional on a unital cofinal domain while preserving every finite prime-shell
value. The exact critical shell masses are nonnegative and nonsummable; order-unit monotonicity
would bound every finite partial sum by the value at the unit, contradicting nonsummability.

More strongly, every exact finite-valued linear extension on a domain containing the unit and all
finite indicators is unbounded below on its nonnegative cone. Therefore the cofinal object sought
here must be genuinely semifinite/nonunital. Its completed Burnol finite part is necessarily signed,
and no global lower floor can be inherited from finite-level Gram positivity. Only a lower floor on
the specific completed resolvent test family can survive.

`SuzukiCompletedMellinPositiveDomainNoGo.lean` closes the apparent nonunital escape for the actual
endpoint profiles.  For a positive profile `f`, positivity and finite-cutoff compatibility imply
`sum_F w_p f_p <= Phi(f)` without using an order unit.  Critical Suzuki transport to actual Mellin
abscissa `sigma` is exactly

```text
w_p f_sigma(p) = Lambda(p) exp(-sigma log p),
Summable_p (w_p f_sigma(p))  iff  1 < sigma.
```

Thus no positive finite-valued domain can contain even one completed left-half profile and its
finite truncations.  The surviving object is not a positive semifinite trace with a cleverly chosen
proper domain; it must be a signed finite-part anomaly.  Any exact such extension is unbounded below
on its full positive cone, so a usable floor can only concern the source-normalized profile family,
not its conic or linear closure.

## Gates

- [x] rightmost open source-side interface identified from RH endpoints
- [x] internal corpus audited for existing shell, residual, and failed scalarization theorems
- [x] exact logarithmic cutoff cocycle isolated
- [x] prime-power coefficient calculation `(3)` checked
- [x] complete paper proof of analytic nuclear factorization and `(4)`
- [x] strengthen actual Sonin shell congruences from compact error to the retained exact relative ideal
- [x] prove finite-prime uniqueness and principal algebra closure
- [x] prove cyclicity on faithful zero/live normal states and the finite-support algebraic core
- [x] identify the diagonal finite-place principal trace with `log(p^m)` and the exact Connes orbital coefficient
- [x] extend the canonical principal trace through the exact relative ideal with ordinary trace on its trace-class part
- [x] falsify aperture-restriction compatibility inside the trace-class relative extension
- [x] isolate the exact positive noncompact lost-layer Gram defect and its compact-distance lower bound
- [x] prove every strict aperture pair fails relative compatibility at some genuine prime scale
- [x] prove nested aperture defects already lie in the canonical principal normal-state algebra
      modulo the exact relative ideal, and extend the cyclic reader to them
- [x] prove exact retained/lost operator and cyclic orbital-mass conservation
- [x] compute the ordinary trace of the Schatten-1 aperture curvature and prove scalar faithfulness
- [x] identify its canonical positive Ward counterterm by exact transgression
- [x] integrate scalar curvature to an explicit Ward potential and prove exact base-gauge change
- [x] prove Fourier-parity no-go: invariant complex-linear relative trace cannot identify the
      RH-odd bilateral holonomy with positive Ward energy except in the flat case
- [x] retire invariant relative-trace/Burnol equality as a possible RH-orientation mechanism
- [x] exclude positive or globally lower-bounded unital cofinal finite-part extensions
- [x] exclude positive or globally lower-bounded finite-part extensions containing any completed
      left-half Mellin profile, without a unit premise
- [ ] construct the fibre-pointed co-Poisson/Burnol anomaly on normalized completed profiles, or
      prove its source constraints inconsistent; global Fourier-invariant linear traces are closed
- [ ] formalize every dependency-closed theorem in Lean and wire `RHTower.lean`

## Novelty status

- `(1)`--`(3)`: classical crossed-product/cutoff-index mechanism; not new by itself.
- analytic trace-class strengthening of the concrete Sonin time-band ideal: corpus-new; external
  novelty not yet claimed.
- cyclic pullback `(6)` through the exact Sonin resolvent with finite-prime Calkin faithfulness:
  candidate new source-specific theorem; literature audit pending exact proof.
- faithful tropical-state trace law `(P2)`, exact CCM diagonalization `(P4)`, and prime-power source
  value are formalized and corpus-new. A targeted primary-source audit found the semilocal Sonin
  carrier and Hilbertian isomorphism, but not this normal-state cyclic trace theorem; external
  novelty remains provisional until expert review.

## Log

- 2026-07-22 — created as single active right-to-left frontier claim after residual-Gram and
  bounded projection-correction scalarizations were ruled out by existing Lean theorems.
- 2026-07-22 — stale gates corrected from formal corpus; principal normal-state cyclicity,
  Calkin invariance, exact CCM diagonalization, and von-Mangoldt source value proved in
  `SoninPrincipalShellCyclicTrace.lean`. First open connector is now trace extension through the
  exact relative ideal plus Burnol completion.
- 2026-07-22 — cofinal positive extension killed. Exact finite source values plus nonsummability
  force every unital finite-valued linear extension to be unbounded below on the positive cone.
  Finite-set trace extension remains meaningful, but its cofinal completion must be a proper
  nonunital semifinite domain; finite-cutoff positivity cannot supply the completed lower floor.
- 2026-07-22 — nonunital positive escape killed on the actual endpoint family.  Exact displacement
  transport gives first-prime mass `Lambda(p)p^(-sigma)` and sharp summability boundary `sigma>1`.
  Every left-half profile therefore has infinite positive Suzuki mass, so no positive finite domain
  can contain it even when the unit is absent.  Remaining connector is necessarily a signed,
  canonically normalized Burnol finite-part anomaly; abstract domain restriction no longer counts.
- 2026-07-22 — relative-only aperture closure killed universally, not only in one chamber. For every
  `0<a<b`, Archimedean selection and Euclid supply a prime `p` with `b<p*a`; its diagonal
  restriction defect is noncompact and outside the exact relative ideal.
- 2026-07-22 — previous enlarged-algebra conclusion corrected. In every strict crossing chamber,
  the defect is the canonical scale-one shell `S(ra,rb)` modulo the exact relative ideal. The full
  canonical zero/live state algebra closes modulo that ideal, the shell reader is `log(b/a)`, and
  aperture defects form an additive principal cocycle. All remaining aperture curvature is
  Schatten-1. Next open object is its ordinary trace and exact Burnol cancellation, not a new
  principal algebra.
- 2026-07-22 — retained and lost live shells now conserve the exact diagonal orbital mass `log r`.
  The principal aperture channel is completely flat; only the scalar trace of its Schatten-1
  curvature can participate in the Burnol weld.
- 2026-07-22 — curvature scalar and its canonical counterterm are closed. For successive layers
  `Z=L_(a,b)D_rL_(b,c)`, Lean proves `Re Tr Kappa=-||Z||_HS^2`, trace faithfulness, and
  `2 Re Tr Kappa+||[Z+Z^*,L_(a,b)]||_HS^2=0`. Next connector is not another trace computation:
  it is equality between this relative Ward energy and the relative finite part of Suzuki's
  concrete noncompact Burnol conductor.
- 2026-07-22 — prior connector retired. Curvature satisfies operator Bianchi and integrates to an
  explicit Ward potential with exact base-gauge change. Symmetric Ward channel is Fourier-even;
  bilateral forward-minus-inverse holonomy is Fourier-odd. Every Fourier-invariant complex-linear
  reader annihilates that holonomy, and equality with Ward energy is equivalent to `Z=0`. Hence a
  global invariant relative trace cannot carry RH orientation. Only fibre-pointed co-Poisson
  evaluation survives.
