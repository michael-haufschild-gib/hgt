# The prime boundary layer is an endpoint jet; the zeta divisor survives only as escaping monodromy

- **ID:** `prime-boundary-perturbative-jet-monodromy-escape`
- **Stage:** 3-formalized
- **Type:** THEOREM / PERTURBATIVE-NONPERTURBATIVE NO-GO
- **Scientific status:** `[PROVED; BRIDGE; NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Source:** the signed Levy defect left by
  `prime-boundary-symmetric-dickman-zero-free-law`; separate from RHTower Routes A--D
- **Statement:** After the symmetric Dickman boundary law is removed, every algebraic correction in
  `1/log N` is a distributional jet supported at the collapsed endpoint `u=0`.  The zeta divisor is
  not in any finite jet: it is the quantized monodromy of the analytically continued prime zeta
  function, and its branch points escape every compact boundary chart at speed `log N`.

## 1. Prime-harmonic boundary defect

Put `L=log N` and define the positive prime-harmonic measure

```text
mu_N = sum_(p<=N) (1/p) delta_(log p/L).                         (1)
```

Its scale-invariant limit on `(0,1]` is

```text
mu(du)=du/u.                                                     (2)
```

For a test function `h` on `[0,1]` satisfying `h(0)=0`, define

```text
D_N(h)
  = <mu_N-mu,h>
  = sum_(p<=N) h(log p/L)/p - integral_0^1 h(u) du/u.            (3)
```

Let `P(s)=sum_p p^(-s)` be the prime zeta function.  On a chosen branch at `s=1`, write

```text
P(1+w)=log(1/w)+sum_(k>=0) alpha_k w^k/k!,   |w|<1/2.           (4)
```

The coefficients satisfy, for every `k>=1`,

```text
alpha_k
  = (-1)^k lim_(x->infinity)
      {sum_(p<=x) (log p)^k/p - (log x)^k/k}.                   (5)
```

Equation `(5)` is the recently explicit higher-order Mertens theorem of Kawalec.  It also follows
directly by Stieltjes integration from the classical prime number theorem with a zero-free-region
error term.

## 2. Endpoint-jet theorem

`[PROVED]` Fix `M>=1`.  For every `h in C^(M+1)([0,1])` with `h(0)=0`,

```text
D_N(h)
  = sum_(k=1)^M
      ((-1)^k alpha_k/k!) h^(k)(0)/L^k
    + O_(h,M)(L^(-M-1)).                                      (6)
```

Equivalently, in the distribution space dual to smooth functions vanishing at zero,

```text
mu_N-mu
  ~ sum_(k>=1) alpha_k delta_0^(k)/(k! L^k).                   (7)
```

Here `<delta_0^(k),h>=(-1)^k h^(k)(0)`, so `(6)` and `(7)` have the same signs.

### Proof

Let

```text
A_k(x)=sum_(p<=x) (log p)^k/p.                                 (8)
```

The coefficient formula `(5)`, strengthened by the classical de la Vallee Poussin remainder,
gives

```text
A_k(x)
  = (log x)^k/k + (-1)^k alpha_k
    + O_k(poly_k(log x) exp(-a sqrt(log x)))                   (9)
```

for some `a>0`.  Applying `(3)` to `h(u)=u^k` and using `(9)` yields

```text
D_N(u^k)=(-1)^k alpha_k/L^k+O_k(exp(-a sqrt L)).               (10)
```

Taylor-expand

```text
h(u)=sum_(k=1)^M h^(k)(0)u^k/k!+r_M(u),                        (11)
```

where `r_M(u)=O(u^(M+1))` and `r_M'(u)=O(u^M)`.

It remains to control `D_N(r_M)`.  Write

```text
pi(t)=li(t)+q(t),
q(t)=O(t exp(-a sqrt(log t))).                                 (12)
```

Stieltjes integration of `r_M(log t/L)/t` against `d pi(t)` splits into the exact continuum term
and the `q`-remainder.  The omitted continuum interval `0<u<log 2/L` and the lower boundary term are
both `O(L^(-M-1))`.  For the integral remainder, put `y=log t`.  Since

```text
d/dt [r_M(log t/L)/t]
  = {r_M'(log t/L)/L-r_M(log t/L)}/t^2,                        (13)
```

equation `(12)` bounds its absolute value by a constant times

```text
L^(-M-1) integral_(log 2)^L
  exp(-a sqrt y) (y^M+y^(M+1)) dy
  + exp(-a sqrt L).                                            (14)
```

The integral remains bounded when its upper endpoint is replaced by infinity.  Hence
`D_N(r_M)=O(L^(-M-1))`.  Combining this with `(10)`--`(11)` proves `(6)`.  QED.

## 3. Symmetric Wick expansion

The scaled finite Wick cumulant is

```text
K_N^bdry(z)
  = 2 sum_(p<=N) [cosh(z log p/L)-1]/p.                        (15)
```

Its symmetric Dickman limit is

```text
Phi(z)=2 integral_0^1 [cosh(zu)-1] du/u.                       (16)
```

Apply `(6)` with `h_z(u)=2(cosh(zu)-1)`.  Uniformly for `z` in a fixed compact subset of `C`, and
for every `M>=1`,

```text
K_N^bdry(z)
  = Phi(z)
    + sum_(m=1)^M 2 alpha_(2m) z^(2m)/((2m)! L^(2m))
    + O_(M,z)(L^(-2M-2)).                                     (17)
```

In particular,

```text
L^2 [K_N^bdry(z)-Phi(z)] -> alpha_2 z^2.                       (18)
```

All odd corrections vanish.  The entire perturbative tower is a local even jet at the collapsed
small-prime endpoint.

For a test function supported in `[delta,1]` with `delta>0`, every derivative at zero vanishes.
Equation `(6)` for arbitrary `M` therefore gives

```text
D_N(h)=O_(h,M)(L^(-M)) for every M.                            (19)
```

The direct PNT estimate strengthens this to an error exponentially small in `sqrt(delta L)`.
Thus the bulk arithmetic fluctuation is beyond every algebraic order in the boundary-layer scale.

## 4. Finite perturbation theory is structurally zero-free

Every finite truncation of `(17)`, after exponentiation, has the form

```text
exp(Phi(z)+Q_M(z/L)),                                         (20)
```

where `Q_M` is an even polynomial with zero constant term.  It is nonzero for every complex `z`.
The exact finite characteristic amplitude is also an exponential and is nonzero.

Consequently no finite number of boundary coefficients can create a zeta node.  This is stronger
than saying that a particular coefficient fails: the entire algebraic perturbation category is
zero-free.

This does not mean that the infinite prime germ contains no zero information.  It means that the
information is not perturbative in the compact `1/log N` chart.

## 5. The divisor is a monodromy sector

Prime zeta continuation is governed by

```text
P(s)=sum_(n>=1) mu(n)/n log zeta(ns).                          (21)
```

It has logarithmic branch points at `s=1/n` and `s=rho/n`, where `rho` ranges over nontrivial zeta
zeros and `mu(n)!=0`.

The regular germ in `(4)` has radius exactly `1/2`: the first obstruction is the prime-power branch
at `s=1/2`, caused by the pole of `zeta(2s)`.  Therefore even the full convergent Taylor germ at
`s=1` reaches a prime-power branch wall before it reaches any nontrivial zero.

Let `rho` be a nontrivial zeta zero with `Re rho>=1/2`, and let `m_rho` be its multiplicity.  For
every `n>=2`, either `Re(n rho)>1`, or `Re(n rho)=1` with nonzero imaginary part.  The classical
zero-free line `Re s=1` then makes every `n>=2` term in `(21)` regular near `rho`.  Hence analytic
continuation of `P` around a sufficiently small positive loop `gamma_rho` gives the exact quantized
charge

```text
(1/(2 pi i)) Delta_(gamma_rho) P = m_rho.                     (22)
```

This monodromy is the divisor information missing from the positive boundary field.

In the boundary coordinate

```text
z=L(s-1),                                                     (23)
```

the branch point belonging to `rho` is located at

```text
z_N(rho)=L(rho-1).                                            (24)
```

Because `rho!=1`, `|z_N(rho)| -> infinity`.  Every zeta-divisor charge therefore escapes every
fixed compact boundary chart.  The prime-power wall at `s=1/2` itself sits at `z=-L/2` and also
escapes.

This is the precise perturbative/nonperturbative split:

```text
compact boundary chart: endpoint jets, Dickman field, no nodes;
escaping sector:         prime-zeta branch monodromy, integer divisor charge.    (25)
```

## 6. Why the Gamma/theta weld cannot repair perturbation theory

The archimedean completion factor

```text
A_infinity(s)=s(s-1) pi^(-s/2) Gamma(s/2)/2                    (26)
```

is holomorphic and nonzero on the open critical strip.  It therefore has a holomorphic logarithm
there.  Adding `log A_infinity` changes the local Taylor coefficients in `(17)`, but it has zero
monodromy around every nontrivial zeta zero.

Thus the Gamma/theta weld can renormalize the perturbative endpoint jet but cannot cancel, create,
or relocate the integer charge `(22)`.  A finite-order cancellation between prime and archimedean
coefficients is not a divisor theorem.

## 7. Terminal RH verdict

This route does **not** prove RH.

The natural quantized invariant requested by the boundary-layer analysis is not an unknown physical
observable: it is winding number, equivalently prime-zeta monodromy or divisor multiplicity.
Classically,

```text
RH
  iff P has no zero-generated branch point in 1/2<Re(s)<1.     (27)
```

The equivalence follows from `(21)` and functional-equation symmetry.  But proving the support
statement on the right is exactly RH in monodromy language.  The reformulation is faithful and
nonperturbative, but not easier.

There are two further hard consequences.

1. Every finite cumulant `K_N` is entire and has zero monodromy.  Its derivatives cannot converge
   uniformly on a loop to a limit with nonzero residue, because contour integration preserves the
   zero integral.  Quantized charge cannot nucleate through locally uniform convergence of regular
   finite fields.
2. Exponentials of finite Euler sums are zero-free.  By Hurwitz's theorem, a locally uniform limit
   of such zero-free holomorphic functions is zero-free or identically zero.  Hence raw finite Euler
   exponentials, even multiplied by nonvanishing Gamma or exponential gauges, cannot converge
   locally uniformly to `Xi` on any connected domain containing a known `Xi` zero.

A viable finite-prime architecture must therefore carry nonzero winding already at finite stage,
for example through determinants with genuine zeros, and prove that those integer charges persist
cofinally.  Finite positivity, finite self-adjointness, finite spectral agreement, and every finite
boundary jet remain on the zero-charge side.

## 8. Lean surface

`formal/GaloisForLFunctions/RHTower/PrimeBoundaryDickmanWick.lean` now additionally defines and proves:

- `primeBoundaryLogMoment`;
- `iteratedDeriv_primeBoundaryWickCumulant_even`;
- `iteratedDeriv_primeBoundaryWickCumulant_odd`.

The Lean theorem identifies every positive even derivative of the finite entire cumulant at zero
with the corresponding symmetric prime-log moment, and proves exact vanishing of every odd
derivative.  It contains no asymptotic hypothesis and no analytic-number-theory placeholder.

The higher-order Mertens expansion `(6)` remains a paper theorem because formalizing the classical
PNT zero-free-region remainder would be a separate foundational project.  No assumed PNT interface
has been inserted into Lean.

## 9. Parent boundary

- Artur Kawalec, *On the series expansion of the prime zeta function about s=1 and its
  coefficients*, 2026, <https://arxiv.org/abs/2603.21535>, proves `(4)`--`(5)` and identifies the
  radius `1/2` regular germ.
- C.-E. Froberg, *On the prime zeta function*, BIT 8 (1968), 187--202,
  <https://doi.org/10.1007/BF01933420>, is the classical source for `(21)`, its analytic
  continuation, and its logarithmic singularities.
- The endpoint distribution expansion `(6)` and boundary-chart interpretation are direct
  consequences of those parent results plus classical Stieltjes integration.  The monodromy and
  Hurwitz obstructions are standard complex analysis.

The synthesis sharply terminates the prime-superspace perturbative route, but it does not pass the
new-science gate.  Its value is architectural: it identifies the only divisor-faithful sector and
shows why every fixed boundary-layer calculation misses it.

## Gates

- [x] all higher prime-log moment constants identified
- [x] distributional endpoint-jet expansion proved
- [x] symmetric Wick expansion proved to arbitrary algebraic order
- [x] compact boundary sector proved zero-free
- [x] bulk defect proved beyond all algebraic orders
- [x] zeta divisor identified as escaping prime-zeta monodromy
- [x] Gamma completion proved unable to change divisor charge
- [x] exact finite cumulant-moment parity formalized in Lean
- [x] parent theory audit completed; classified as bridge
- [x] RH endpoint identified: monodromy support localization is RH itself

## 2026-08-20 — Stage-3 formalization

The card is formalized unconditionally across seven new modules plus two corpus modules that
already carried the monodromy half.

### New modules

| module | content |
|-|-|
| `RHTower/PrimeHigherMertens.lean` | the higher-order Mertens theorem `∑_{p≤x}(log p)^k/p - (log x)^k/k → C_k`, by Abel summation against `θ`; the devices `exp_neg_sqrt_le_pow` and `integrableOn_logPow_pntErrorWeight` |
| `RHTower/PrimeHigherMertensRate.lean` | the same with the de la Vallée Poussin rate, the packaged PNT envelope, the half-exponential tail bound, and the monomial defect estimate |
| `RHTower/PrimeEndpointJet.lean` | the boundary defect `D_x`, its exact Abel decomposition, and the master remainder estimate |
| `RHTower/PrimeEndpointJetExpansion.lean` | linearity of `D_x` and the jet expansion for `polynomial + remainder` test functions |
| `RHTower/PrimeEndpointJetTaylor.lean` | iterated integration, the Taylor polynomial of a derivative tower, the remainder bound, and `(6)` for smooth test functions |
| `RHTower/PrimeBoundaryWickExpansion.lean` | the hyperbolic and trigonometric towers, the two-axis Wick expansion, the leading correction, the beyond-all-orders statement, and the zero-freeness of truncations |
| `RHTower/PrimeBoundaryMonodromyEscape.lean` | the Möbius-inversion derivative form, the quantized monodromy charge, the boundary-chart escape, the archimedean zero-charge statement, the RH restatement, and the two zero-charge obstructions |

### Item table

| card item | Lean declaration |
|-|-|
| `(1)`, `(2)` prime-harmonic boundary defect | `primeBoundaryDefect`, `primeBoundaryDefect_eq` |
| `(3)` defect of a test function | `primeBoundaryDefect`, `primeBoundaryDefect_add`, `primeBoundaryDefect_const_mul`, `primeBoundaryDefect_sum` |
| `(4)`, `(5)` prime zeta germ coefficients | `mertensLogPowConstant`, `mertensLogPowConstantFull`, `tendsto_primeLogPowSum_sub` |
| `(6)`, `(7)` endpoint-jet expansion | `exists_abs_primeBoundaryDefect_jet_le`, `exists_abs_primeBoundaryDefect_taylor_jet_le` |
| `(8)`, `(9)` `A_k(x)` and its remainder | `primeLogPowSum`, `primeLogPowSumIoc_sub_eq`, `exists_primeLogPowSum_sub_bound` |
| `(10)` monomial defect | `exists_abs_primeBoundaryDefect_pow_le`, `tendsto_logPow_mul_primeLevyDefect_pow` |
| `(11)`–`(14)` Taylor split and remainder control | `jetTaylor`, `abs_sub_jetTaylor_le`, `tower_bound`, `jetTailWeight`, `integrableOn_jetTailWeight`, `exists_abs_primeBoundaryDefect_le` |
| `(15)`, `(16)` finite and limiting Wick cumulants | `primeClockRadialEnergy`, `primeClockVerticalEnergy`, `wickProfile` |
| `(17)` symmetric Wick expansion | `exists_abs_primeClockRadialEnergy_jet_le`, `exists_abs_primeClockVerticalEnergy_jet_le` |
| `(18)` leading correction at scale `(log N)^2` | `tendsto_logSq_mul_primeClockRadialEnergy_sub` |
| `(19)` beyond all algebraic orders | `exists_abs_primeBoundaryDefect_flat_le` |
| `(20)` finite truncations are zero-free | `exp_wickProfile_add_poly_ne_zero` |
| `(21)` prime zeta continuation | `primeBoundary_moebius_inversion` (derivative form of `P(s) = ∑ μ(n)/n log ζ(ns)`), `primeGradeSource_eq_continuation` |
| `(22)` quantized monodromy charge | `primeBoundary_monodromy_charge` |
| `(23)`, `(24)` boundary chart and escape | `tendsto_boundaryChart_escape` |
| `(25)` the perturbative/nonperturbative split | `exp_wickProfile_add_poly_ne_zero` with `primeBoundary_monodromy_charge` |
| `(26)` the archimedean weld has zero monodromy | `circleIntegral_logDeriv_archFactor_eq_zero` |
| `(27)` terminal RH restatement | `riemannHypothesis_iff_no_primeBoundary_charge` |
| §7.1 finite cumulants carry no charge | `circleIntegral_deriv_of_entire_eq_zero` |
| §7.2 Hurwitz obstruction | `no_zero_of_tendstoUniformlyOn_zeroFree` |

Every declaration has axiom set `[propext, Classical.choice, Quot.sound]`.

Two deliberate renderings, both faithful and both noted here:

* `(6)` is stated for a derivative tower on `ℝ` with the explicit remainder bounds
  `|r| ≤ A u^{M+1}`, `|r'| ≤ A u^M` on `(0,1]` — exactly the hypotheses the Abel proof uses, and
  exactly what the Taylor module supplies for a `C^{M+1}` test function.
* `(21)`–`(22)` are formalized in derivative form: the monodromy of `P` around a loop is the
  contour integral of `P'`, so the branch-point statement is the residue statement for the
  continued prime-log current, which is what the corpus modules `GradeMonodromyInversion` and
  `XiHeatCassiniWoldZetaPoleCarrier` already prove.
* `(17)` is proved on the two real axes (radial `cosh` and vertical `cos`), which are the
  restrictions the corpus energies `R_N` and `V_N` use; the general complex statement follows by
  applying the same theorem to real and imaginary parts.

**Stage: 3-formalized.**

## Gates (stage 3)

- [x] higher-order Mertens constants constructed and their limits proved
- [x] rate form proved with the de la Vallée Poussin error
- [x] endpoint remainder estimate proved
- [x] endpoint-jet expansion proved, including the Taylor construction for smooth test functions
- [x] symmetric Wick expansion proved on both axes
- [x] leading `(log N)^2` correction identified with the second Mertens constant
- [x] bulk defect proved beyond all algebraic orders
- [x] finite truncations proved zero-free
- [x] Möbius inversion and quantized monodromy charge assembled from the corpus
- [x] boundary-chart escape proved
- [x] archimedean weld proved to carry zero monodromy
- [x] terminal RH restatement proved
- [x] both zero-charge obstructions proved
- [x] axiom audit clean
