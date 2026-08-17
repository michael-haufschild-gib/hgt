# Logarithmic recurrence is the sharp polynomial-carrier wall for Suzuki orbit transport

- **ID:** `suzuki-log-recurrence-polynomial-carrier-trichotomy`
- **Stage:** 3 — formalized in Lean 4
- **Type:** APERTURE CLASSIFICATION / POLYNOMIAL-GROUP SURVIVOR / HARD-WALL THEOREM
- **Scientific status:** `[PAPER-PROVED] [UNCONDITIONAL] [NOVELTY UNVERIFIED] [NOT RH]`
- **Route:** completed Evans/logarithmic-seam branch of Connes/CCM
- **Inputs:** `suzuki-tempered-orbit-carrier-aperture-recurrence-dichotomy.md`,
  `suzuki-paired-gamma-logistic-flat-sector-conjecture.md`
- **Literature:** Hatano--Nelson 1996 for asymmetric-hopping/imaginary-gauge spectra; standard
  polynomially weighted propagation for finite-range lattice operators; Matveev's lower bound for
  integer linear forms in logarithms of algebraic numbers.

## 1. New aperture invariant

Fix an aperture \(a\), visible-prime valuation lattice

```text
G=Z^d,
ell(nu)=sum_(p in P_a)nu_p log p.                        (1)
```

For nonresonant labels define the two physical event times

```text
tau_0(nu)=[-log|ell(nu)|]_+,
tau_a(nu)=[-log|2a-ell(nu)|]_+,
tau(nu)=max(tau_0(nu),tau_a(nu)).                        (2)
```

Exact resonances are retained as root ports and omitted from the corresponding quotient. Define

```text
T_log(a)
 =limsup_(|nu|_1->infinity)
   tau(nu)/log(2+|nu|_1),                               (3)

R(a)
 =limsup_(|nu|_1->infinity)
   tau(nu)/|nu|_1.                                      (4)
```

The first event family always has finite logarithmic type. Matveev's theorem applied to the fixed
multiplicatively independent rational primes gives constants \(c,C>0\) such that every nonzero
integer linear form satisfies

```text
|ell(nu)|>=c(2+|nu|_1)^(-C).
```

Therefore

```text
tau_0(nu)<=C_a log(2+|nu|_1).                           (5)
```

Thus only the opposite-end family can make `(3)` infinite; `(3)` retains both for symmetry.

## 2. Main trichotomy

Let \(A_a\) be the finite-range self-adjoint prime adjacency on \(\ell^2(G)\). Let

```text
(D_w z)_nu=w(nu)z_nu,
B_w=D_w A_a D_w^(-1)                                   (6)
```

on finitely supported vectors, with its bounded extension when generator ratios are bounded.

### Theorem

For every prescribed \(0<\sigma<1\):

1. If \(T_{\log}(a)<\infty\), there is a polynomial weight

   ```text
   w_kappa(nu)=(1+|nu|_1)^(-kappa)                      (7)
   ```

   such that

   ```text
   w_kappa in ell2(G),
   sum_nu w_kappa(nu)^2 exp(2sigma tau(nu))<infinity,   (8)
   ```

   every prime shift is bounded, and

   ```text
   ||exp(-i x B_w/2)||+||exp(i x B_w/2)||
   <=C(1+|x|)^m.                                        (9)
   ```

   Thus the prime group has controlled polynomial, rather than exponential, distortion. Applying
   paired Gamma Hardy uniformly requires the sharper inequality \(\kappa<\sigma<1\) between the
   actual transport degree and Gamma height. Source frequency moments do not by themselves erase
   a free homogeneous component.

2. If \(T_{\log}(a)=\infty\) but \(R(a)<\infty\), exponential weights still give event
   summability, but the radial exponential choice

   ```text
   w(nu)=exp(-kappa|nu|_1)                              (10)
   ```

   has a nonreciprocal Hatano--Nelson limit operator with nonreal spectrum. Its group has
   exponential norm growth on one frequency tail, so `(9)` fails.

3. If \(R(a)=\infty\), no orbit weight with uniformly bounded generator ratios can absorb all
   event factors. This is the predecessor tempered-weight no-go.

Hence finite exponential recurrence was not the correct admission criterion even for polynomial
transport. Finite **logarithmic** recurrence is the sharp class for polynomial carrier distortion;
it is not by itself a shifted-\(L^2\) theorem.

## 3. Polynomial event summability

Assume \(T_{\log}(a)<\infty\). Choose \(Q>T_{\log}(a)\). Apart from finitely many labels,

```text
tau(nu)<=Q log(2+|nu|_1).                               (11)
```

The number of lattice points with \(|\nu|_1=N\) is \(O_d((1+N)^{d-1})\). For `(7)`,

```text
w_kappa(nu)^2 exp(2sigma tau(nu))
 <=(1+|nu|_1)^(-2kappa+2sigma Q).                       (12)
```

Choose

```text
2kappa>d+2sigma Q.                                      (13)
```

Shell summation proves `(8)`, and `(13)` also implies \(w_\kappa\in\ell^2(G)\).

For every fixed generator step \(s\),

```text
w_kappa(nu)/w_kappa(nu+s)
 =[(1+|nu+s|_1)/(1+|nu|_1)]^kappa
 <=(1+|s|_1)^kappa.                                    (14)
```

Thus both oriented weighted shifts are bounded.

## 4. Polynomial propagation of the weighted prime adjacency

Work first with integer \(m\ge\kappa\). Let

```text
<nu>=1+|nu|_1.
```

The unweighted \(A_a\) is a finite Laurent polynomial in commuting lattice shifts. Its unitary
group is a finite-range lattice evolution. Repeated commutation with coordinate multiplication
gives, for every multi-index \(|\alpha|\le m\),

```text
X^alpha exp(-i x A_a)
 =sum_(beta<=alpha)
   P_(alpha,beta)(x)
   exp(-i x A_a)X^beta,                                 (15)
```

where \(P_{\alpha,\beta}\) is an operator-valued polynomial of degree at most
\(|\alpha-\beta|\). This follows by differentiating

```text
exp(i x A_a)X_j exp(-i x A_a)
 =X_j+i integral_0^x
   exp(i t A_a)[A_a,X_j]exp(-i t A_a)dt,                (16)
```

and observing that every iterated commutator of the finite Laurent polynomial \(A_a\) with
coordinates is again a bounded finite Laurent polynomial. All these Laurent polynomials commute,
so `(16)` actually terminates at finite order.

Equations `(15)`--`(16)` give the standard weighted estimate

```text
||<X>^(-m) exp(-i x A_a)<X>^m||
 <=C_m(1+|x|)^m.                                       (17)
```

Fractional polynomial weights follow by complex interpolation. The larger integer \(m\) chosen in
`(13)` proves polynomial propagation, but cannot be used for direct Gamma Hardy when \(m\ge1\).
Since \(D_w=\langle X\rangle^{-m}\),

```text
exp(-i x B_w)
 =D_w exp(-i x A_a)D_w^(-1)                            (18)
```

first on finitely supported vectors and then by `(17)` on all \(\ell^2(G)\). This proves `(9)`.

The same argument applies to the finitely many prime-power steps in Suzuki's literal adjacency;
their lengths change constants and polynomial degree, not the conclusion. `QED`

## 5. Exponential weights create a Hatano--Nelson hard wall

The hard-wall mechanism is classical. The source-specific identification is as follows.

Consider first \(G=\mathbb Z\), nearest-neighbor adjacency

```text
A=S+S^(-1),
w(n)=exp(-kappa|n|),       kappa>0.                     (19)
```

On the far positive half-line, `(6)` is exactly

```text
B_+=exp(kappa)S+exp(-kappa)S^(-1).                      (20)
```

Under the circle Fourier transform its symbol is

```text
lambda_kappa(theta)
 =exp(kappa+i theta)+exp(-kappa-i theta)

 =2cosh(kappa)cos(theta)
  +2i sinh(kappa)sin(theta).                            (21)
```

This is the Hatano--Nelson ellipse. At \(\theta=\pi/2\),

```text
lambda_kappa(pi/2)=2i sinh(kappa) notin R.              (22)
```

Long normalized plane-wave packets supported arbitrarily far in the positive half-line have
boundary error \(O(M^{-1/2})\), so every point of `(21)` belongs to the approximate spectrum of
the radial full-line operator \(B_w\).

For the full finite prime-power adjacency on \(\mathbb Z^d\), use boxes receding into the positive
orthant. The limit Laurent symbol is

```text
b_kappa(theta)
 =c_0+sum_(q in Q_a)c_q[
   exp(kappa|q|_1+i<q,theta>)
  +exp(-kappa|q|_1-i<q,theta>)].                        (23)
```

Its imaginary part is the nonzero trigonometric polynomial

```text
2 sum_q c_q sinh(kappa|q|_1)sin(<q,theta>).             (24)
```

Distinct valuation steps have distinct Fourier characters and \(c_q>0\), so `(24)` is not
identically zero. Hence the approximate spectrum contains a nonreal point
\(\lambda\) with \(\operatorname{Im}\lambda\ne0\).

Spectral mapping now gives

```text
||exp(-i x B_w/2)||
 >=spectralRadius(exp(-i x B_w/2))
 >=exp(x Im(lambda)/2)                                  (25)
```

for the sign of \(x\) making the exponent positive. No polynomial two-sided group bound is
possible. `QED`

This does not say a realized tempered Suzuki solution grows exponentially. It says temperedness
must enforce a stable/unstable spectral cancellation absent from the previous Hardy proof.

## 6. Almost every aperture has finite logarithmic type

Fix a bounded aperture interval \(J\Subset(0,\infty)\) on which the visible-prime dimension is
constant, and choose \(q>d\). For each valuation label with \(|\nu|_1=N\), the bad apertures

```text
E_nu(q)
 ={a in J:0<|2a-ell(nu)|<(2+N)^(-q)}                   (26)
```

have length at most \((2+N)^{-q}\). There are \(O_d(N^{d-1})\) labels on shell \(N\), so

```text
sum_nu |E_nu(q)|
 <=C sum_(N>=1)N^(d-1-q)<infinity.                      (27)
```

Borel--Cantelli gives, for almost every \(a\in J\),

```text
tau_a(nu)<=q log(2+|nu|_1)
```

for all sufficiently large nonresonant \(\nu\). The zero-event family already has logarithmic type
by the fixed-prime Matveev bound `(5)` and is aperture-independent.
Taking a countable cover of aperture space and any integer \(q>d\) proves

```text
T_log(a)<infinity for Lebesgue-almost every a.           (28)
```

For \(d\ge2\), the additive prime-log group is dense. Starting in any aperture interval, choose
successive distinct valuation centers \(\ell(\nu_k)/2\) in nested intervals of radii
\((2+|\nu_k|_1)^{-k}\). Their unique nested limit \(a\) satisfies

```text
tau_a(nu_k)/log(2+|nu_k|_1)>=k,
```

so \(T_{\log}(a)=\infty\). The construction can start in every interval; logarithmic-Liouville
apertures are dense.

Thus the polynomial-carrier class is full measure but not all apertures.

## 7. Exact corrected frontier

```text
rank d <= 1 with bounded recurrence clock:
  fractional polynomial event carrier
  + d/2 < kappa < sigma < 1
  -> uniform radial Gamma-Hardy window;                 [PAPER-PROVED]

rank d >= 2:
  lattice square summability requires kappa>d/2>=1
  -> no uniform radial polynomial Gamma-Hardy window;   [PAPER-PROVED NO-GO]

source-selected homogeneous cancellation
  or primitive-flux finite-to-flat transfer;            [OPEN]

T_log(a)=infinity, R(a)<infinity:
  event carrier exists,
  radial exponential carrier has nonreal limit spectrum,
  stable/unstable Evans matching required;              [OPEN]

R(a)=infinity:
  no bounded-ratio event carrier;                       [PAPER-PROVED]

all apertures:
  needs a biweighted/closed-relation dichotomy theorem. [OPEN]              (29)
```

The full-measure finite-type attack cannot close through a uniform radial polynomial carrier in
rank at least two. It needs source-selected dichotomy cancellation or primitive-flux
finite-to-flat transfer. Rank one is a genuine positive survivor because its event clock is
bounded and admits, for example, \((\kappa,\sigma)=(2/3,3/4)\).

## 8. Stronger survivor conjecture

The failure suggests a two-sided carrier rather than a more aggressive scalar weight:

```text
SUZUKI-BIWEIGHTED-EVANS-DICHOTOMY:

for every aperture with R(a)<infinity, the reciprocal carriers
w and w^(-1) form a dual incoming/outgoing pair;
their nonreal Hatano--Nelson limit spectra have opposite orientation;
physical two-ended support identifies the stable space on one frequency
tail with the unstable annihilator on the other;
the resulting Evans matching is Fredholm and has no trace-zero kernel.      (30)
```

The ellipse obstruction no longer kills `(30)`: reciprocal weighting reverses `(24)`, so growing
and decaying channels are paired rather than ignored.

`[OPEN CORE]` Construct the dual Fredholm pairing without using the raw Evans injectivity that is
ultimately RH-bearing.

## 9. Hostile and novelty audit

1. **Ellipse is not new.** It is the clean Hatano--Nelson spectrum and is labeled literature.
2. **Source-specific novelty boundary.** Candidate-new content is invariant `(3)`, its exact
   polynomial-weight equivalence `(8)`--`(9)`, and its placement between the previous recurrence
   classes.
3. **No real-spectrum overclaim.** Polynomial carrier proves a group bound directly, not through
   spectrum alone.
4. **No exponential-carrier no-go overclaim.** The theorem kills radial exponential weight for
   Hardy transfer; other biweighted or non-diagonal relations remain open.
5. **No almost-everywhere-to-everywhere leap.** Dense logarithmic-Liouville apertures remain.
6. **No polynomial-to-Hardy leap.** Gamma's exact horizontal decay absorbs degree \(\kappa\)
   exactly when \(\kappa<\sigma\); source moments do not remove an arbitrary homogeneous channel.
7. **No RH claim.** Raw Evans positivity and all-aperture passage remain.

## 10. Lean target

Faithful formalization requires:

- lattice shell summability for `(8)`;
- bounded polynomial-weight shift ratios `(14)`;
- iterated position commutator identity `(15)`;
- polynomial group estimate `(17)`;
- Fourier-symbol ellipse and nonreal point `(21)`--`(24)`;
- Borel--Cantelli aperture theorem `(28)`.

Formalizing only scalar hyperbolic algebra would not certify the carrier theorem. The full chain is
now unconditional in Lean:

| item | Lean |
|---|---|
| `(8)` | `RHTower.summable_polyDecay_fin`, `RHTower.summable_polyWeight_sq_event` in `RHTower/SuzukiLatticeShellSummability.lean` |
| `(14)` | `RHTower.polyWeight_ratio_le`, `RHTower.polyWeight_ratio_le'` in `RHTower/SuzukiLatticeCarrierWeight.lean` |
| `(15)` | `RHTower.position_mul_exp`, `RHTower.listProd_mul_exp`, `RHTower.exists_time_polynomial` in `RHTower/SuzukiPositionCommutatorGroup.lean` |
| `(17)` | `RHTower.exists_polynomial_word_bound`, `RHTower.exists_polynomial_group_bound` in `RHTower/SuzukiPolynomialGroupEstimate.lean` |
| `(21)`--`(24)` | `RHTower.hatanoNelsonSymbol_eq`, `RHTower.hatanoNelsonSymbol_quarter`, `RHTower.hatanoNelsonSymbol_im_ne_zero`, `RHTower.primeStepSymbol_im` in `RHTower/SuzukiHatanoNelsonEllipse.lean` |
| `(28)` | `RHTower.ae_finite_badAperture`, `RHTower.ae_finite_logType` in `RHTower/SuzukiApertureBorelCantelli.lean` |

Every declaration audits to `[propext, Classical.choice, Quot.sound]`.

## Gates

- [x] define logarithmic recurrence type
- [x] prove polynomial event summability iff a sufficiently strong polynomial weight is chosen
- [x] prove polynomially bounded weighted prime group
- [x] expose exact degree threshold `kappa < sigma`
- [x] classify uniform radial carrier window as rank zero/one only
- [x] identify radial exponential adjacency with Hatano--Nelson limit operator
- [x] prove nonreal approximate spectrum and exponential group lower bound
- [x] prove finite logarithmic type has full measure
- [x] prove logarithmic-Liouville apertures are dense
- [x] extract reciprocal biweighted Evans survivor
- [x] formalize exact theorem chain in Lean
- [ ] prove biweighted Evans dichotomy or refute it
- [ ] prove source-selected homogeneous cancellation or replace direct Hardy by primitive flux
- [ ] prove trace-zero \(H^1_0\) on finite logarithmic type
- [ ] pass all apertures
- [ ] prove RH or a genuine whole-Connes no-go

## Log

- **2026-08-17.** The six-item Lean chain of §10 is closed unconditionally, and the card moves to
  Stage 3.

  Three of the six needed new mathematics rather than transcription.

  *Shell summability without shell counting.*  `(8)` was stated through the shell count
  `O_d(N^{d-1})`.  That route needs a lattice-sphere estimate.  It is unnecessary: since
  `1 + |ν_i| ≤ 1 + |ν|₁` coordinatewise, `∏_i (1 + |ν_i|) ≤ (1 + |ν|₁)^d`, so
  `(1 + |ν|₁)^{-p} ≤ ∏_i (1 + |ν_i|)^{-p/d}`, and the right-hand side is a product of one-dimensional
  `p/d`-series.  Convergence for `p > d` is then a `d`-fold Fubini induction over coordinates and
  needs no counting at all.  The exponent threshold is identical, so nothing is lost.

  *`(16)` terminates at first order.*  The card derives `(15)` from the integral formula `(16)` and
  the observation that iterated commutators stay finite Laurent polynomials.  The sharper statement
  is that the Heisenberg flow is exactly affine: writing `C = AX − XA`, the finite-range structure
  gives `AC = CA`, so `u ↦ e^{uA} X e^{-uA}` has constant derivative `C` and therefore

  ```text
  e^{uA} X e^{-uA} = X + u C
  ```

  with no integral remainder and no truncation.  Iterating over a word of coordinates gives the
  exact form of `(15)`: a coordinate word passes through the evolution and becomes the *same* word
  in the shifted coordinates, `X^α U = U ∏_j (X_j + x C_j)^{α_j}`.  Expanding that ordered product
  exhibits the `P_{α,β}` of `(15)` as the coefficients of a time polynomial of degree at most the
  word length.

  *`(17)` needs no complex interpolation.*  The card obtains fractional weights by interpolating
  between integer ones.  The exact identity above makes that unnecessary.  Because each shift
  `C_j` is a bounded symbol and the symbol class is closed under commutation with the coordinates,
  every coefficient of the time polynomial is a finite sum `∑ B · X^w` with `B` bounded and
  `|w| ≤ m − k` at the `k`-th power of the time.  Such an operator is bounded by the order-`(m−k)`
  position graph norm, so the whole word is bounded by `C (1 + |x|)^m` times the order-`m` graph
  norm — and the evolution being isometric turns this into the weighted group estimate directly.
  The constant is uniform in the time because the coefficients are.

  *Effective Baker is not on the critical path.*  `(5)` cites Matveev, which the card lists as
  Literature; §10 does not ask for it.  The Lean chain therefore closes without an effective
  linear-forms-in-logarithms bound.  What `(5)` supplies — finiteness of the logarithmic type of
  the zero-event family — is aperture-independent and enters only the qualitative statement that
  the *other* family alone can make `(3)` infinite.

  Open items in §7 and §8 (`(29)`, `(30)`) are unchanged research gates and do not touch the
  formalized chain.
