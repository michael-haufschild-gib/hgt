# CCM unit-Riesz Markov--virial and one-sided Landau law

- **ID:** `ccm-unit-riesz-markov-virial-landau-law`
- **Stage:** 2-fully-proven/not_new_scientific_knowledge
- **Type:** THEOREM (paper), exact source factorization and RH connector
- **Scientific status:** `[PROVED] [KNOWN-DERIVED CORPUS INFRASTRUCTURE]`
  `[NOT NEW SCIENTIFIC KNOWLEDGE] [NOT RH]`
- **Parent:** `ccm-unit-riesz-mobius-wavelet-reduction.md`
- **Open consumer:**
  `../../1-in-progress/ccm-unit-riesz-causal-complement-wavelet.md`

## Statement

The moving unit-Riesz wavelet coefficient is exactly a fixed Markov convolution of one causal
virial.  Its Markov density has an explicit zeta Laplace transform.  The resulting coefficient
transform retains every off-critical zeta zero as a genuine simple pole.  Consequently the
all-epsilon one-sided coefficient bound implies RH by Landau's first-singularity theorem.

This closes the connector.  It does not prove the one-sided coefficient bound.

Cell positivity/gluing and finite Möbius virial algebra are formalized respectively in
`formal/GaloisForLFunctions/RHTower/CCMUnitRieszMarkovDensity.lean` and
`formal/GaloisForLFunctions/RHTower/CCMUnitRieszMobiusCausalVirial.lean`.  Global convolution and
Laplace/Landau analysis remain paper-level.

## 1. Fixed logarithmic profile

For `t>=1`, define

```text
g(t)=sum_(1<=r<=t)(1-sqrt(r/t)),
W(t)=3g(t)/t.                                             (1)
```

The parent theorem proves `0<=W<=1`, `W(1)=0`, and `W(t)->1`.  Put

```text
w(v)=W(exp(v)),                 v>=0,
d(v)=w'(v)                      almost everywhere.       (2)
```

The derivative is nonnegative.  Indeed, on
`log(m)<=v<log(m+1)`, with `A_m=sum_(r=1)^m sqrt(r)`, one has

```text
w(v)=3m exp(-v)-3A_m exp(-3v/2),
d(v)=-3m exp(-v)+(9/2)A_m exp(-3v/2).                    (3)
```

The sharp elementary prefix inequality

```text
A_m >=(2/3)m sqrt(m+1)                                  (4)
```

holds for every `m>=1`.  For the induction step, `(4)` at `m` reduces the claim at `m+1` to

```text
(2m+3)sqrt(m+1)>=2(m+1)sqrt(m+2),
```

whose squares differ by exactly `m+1>0`.  Since `exp(v/2)<sqrt(m+1)` in the cell, `(3)` and `(4)`
give `d(v)>=0`.

At `v=log m`, the newly entering summand in `g` is zero, so `w` is continuous.  It is locally
absolutely continuous, increases from `0` to `1`, and therefore

```text
d(v)>=0,
integral_0^infinity d(v)dv=1.                            (5)
```

Thus `d(v)dv` is a probability law fixed by unit aperture, independent of the source and scale.

## 2. Exact zeta transform of the Markov density

For `Re(z)>0`, Tonelli applied to the nonnegative profile gives

```text
Lw(z)
 =3 sum_(r>=1) integral_(log r)^infinity
      [exp(-(z+1)v)-sqrt(r)exp(-(z+3/2)v)]dv
 =3/2 * zeta(1+z)/[(z+1)(z+3/2)].                       (6)
```

Integration by parts, using `w(0)=0` and `w(infinity)=1`, yields

```text
D(z):=Ld(z)
 =3z zeta(1+z)/[2(z+1)(z+3/2)],
D(0)=1.                                                  (7)
```

Equation `(7)` is an explicit probability-transform representation of the unit-Riesz aperture
kernel.

## 3. Markov--virial factorization

Use the critical causal complement from the corpus,

```text
h(t)=h_0(t)=exp(-t)-m_0(t),
m_0(t)=sum_(n<=exp(t))mu(n)/n.                           (8)
```

For `T>0`, the parent wavelet is

```text
Phi_T(u)=u w(T-u),
K_T(u)=Phi_T'(u)=w(T-u)-u d(T-u).                        (9)
```

Define the causal virial

```text
V_h(t)=integral_0^t h(u)du-t h(t).                       (10)
```

Since `w=1*d`, associativity of causal convolution gives the exact identity

```text
I(T):=integral_0^T h(u)K_T(u)du
    =(h*w)(T)-((t h)*d)(T)
    =(d*V_h)(T).                                         (11)
```

The floor identity `sum_(n<=x)mu(n)floor(x/n)=1` also gives

```text
h(t)=-exp(-t)sum_(n<=exp(t))mu(n){exp(t)/n}.             (12)
```

Direct integration of `(8)` gives the arithmetic virial

```text
V_h(t)
 =1-(1+t)exp(-t)+sum_(n<=exp(t))mu(n)log(n)/n
 =1-(1+t)exp(-t)-Q(exp(t)),                              (13)

Q(X)=-sum_(n<=X)mu(n)log(n)/n.
```

Therefore the entire unresolved unit-Riesz coefficient is a positive fixed average of the
single signed defect `1-Q`, with only the explicit polar boundary correction in `(13)`.

## 4. Coefficient transform and noncensorship

The corpus causal transform is

```text
H(z)=Lh(z)=1/(1+z)-1/[z zeta(1+z)].                     (14)
```

Laplace transformation of `(10)` and `(11)` gives

```text
LV_h(z)=H(z)/z+H'(z),
LI(z)=D(z)[H(z)/z+H'(z)].                               (15)
```

Substitution of `(7)` and `(14)` simplifies completely to

```text
LI(z)
 =3/[2(z+1)(z+3/2)]
    *[zeta(1+z)/(1+z)^2+zeta'(1+z)/zeta(1+z)].          (16)
```

At a nontrivial zero `rho` of multiplicity `m`, `z_rho=rho-1` is a genuine simple pole of `(16)`
with residue

```text
3m/[2 rho (rho+1/2)].                                   (17)
```

The residue is nonzero.  The zero of the probability multiplier `D` cancels one order of the
double reciprocal-zeta virial pole, but it cannot censor the remaining logarithmic-derivative
pole.  Thus fixed Markov averaging preserves every off-line mode relevant to RH.

The apparent singularity of `(16)` at `z=0` is removable: the `1/z` terms from `zeta(1+z)` and
`zeta'/zeta(1+z)` cancel.

## 5. One-sided Landau connector `[PROVED]`

Assume that for every `epsilon>0` there are `C_epsilon,T_epsilon` such that

```text
I(T)>=-C_epsilon exp((-1/2+epsilon)T),
T>=T_epsilon.                                           (18)
```

Suppose `zeta(rho)=0` with `Re(rho)>1/2`.  Put

```text
z_rho=rho-1,
delta=Re(z_rho)>-1/2.                                   (19)
```

Choose `0<epsilon<delta+1/2` and set `c=-1/2+epsilon<delta`.  By `(18)`,

```text
b(T)=I(T)+C_epsilon exp(cT)                              (20)
```

is nonnegative on a tail.  Altering it on a compact initial interval makes it nonnegative
everywhere and changes its Laplace transform only by an entire function.

The trivial bound `|m_0(T)|<=1+T`, together with `(5)`, `(10)`, and `(11)`, gives
`I(T)=O(1+T^2)`.  Hence the Laplace abscissa `sigma_c` of `b` is finite and `sigma_c<=0`.
The genuine pole `(17)` cannot occur in the open convergence half-plane, while the added
exponential in `(20)` has its only pole at `c<delta`.  Therefore

```text
delta<=sigma_c<=0.                                      (21)
```

Landau's first-singularity theorem for a nonnegative Laplace transform forces a singularity at
the real point `sigma_c`.  But `(16)` is holomorphic on the real interval `[delta,0]`: zeta has no
real zero on `(1/2,1)`, and `z=0` is removable.  The correction pole `c` lies strictly left of
that interval.  This contradicts Landau.  Thus no nontrivial zero has real part greater than
`1/2`.  Functional-equation symmetry then gives RH.

Consequently

```text
all-epsilon causal-virial wavelet lower bound (18)
  -> Riemann hypothesis.                                (22)
```

Combined with the parent identity between `I(T)` and the CCM Riesz source, this closes the
previously open one-sided Landau connector.

## 6. What remains open

The new Markov factorization is positive but supplies no free half-unit decay.  The probability
law `d` is fixed in `T`; its contractivity only gives norm control.  The required exponent must be
proved for the source-fixed virial `(13)` before or inside the positive convolution `(11)`.

The exact surviving theorem is:

```text
(d*V_h)(T)>=-C_epsilon exp((-1/2+epsilon)T)              (23)
```

for every `epsilon>0`, directly from the coupled Möbius floor source.  By `(22)`, proving `(23)`
proves RH.  Equation `(23)` is not proved here.

## Coisometry verdict

The existing Möbius Schur coisometry cannot by itself prove `(23)`:

1. its critical causal sum is exactly `exp(-t)` after `h_0` and `m_0` recombine;
2. `(11)` shows unit-Riesz processing adds only one fixed Markov convolution;
3. neither operation contains a scale-dependent factor `exp(-T/2)`;
4. `(17)` proves the continued coefficient still has every relevant zeta pole.

Therefore generic Euler-side contractivity is retired as provider.  A viable proof must establish
a source-specific lower law for the virial `1-Q`, or an equivalent signed first-crossing pairing,
before generic norm contraction.

## Literature boundary

Classical Riesz and Möbius-convolution criteria use related smoothing ideas, but targeted searches
did not locate `(7)`, `(11)`, `(13)`, and `(16)` as one CCM unit-aperture Markov--virial theorem.
The recent discrete-Laplace Möbius criterion of Liflandsky (`arXiv:2607.09797`) studies a different
kernel and assumes simple zeros for its explicit formula.  It does not prove `(23)`.

Novelty claim withdrawn.  These elementary identities are retained to prevent the corpus from
re-proposing them as frontier research.

## Gates

- [x] prove unit-Riesz logarithmic profile is a CDF
- [x] compute exact zeta transform of its probability density
- [x] factor moving wavelet as fixed Markov average of causal virial
- [x] identify exact Möbius logarithmic virial
- [x] prove continued coefficient retains every off-critical zero
- [x] prove one-sided Landau connector to RH
- [x] retire generic critical coisometry as exponent provider
- [x] cell positivity/gluing and finite virial algebra formalized
- [ ] prove source-specific Markov--virial lower bound `(23)`
- [ ] RH

## Lean status — the exact zeta transform, 2026-08-15

`formal/GaloisForLFunctions/RHTower/CCMUnitRieszMarkovTransform.lean` (wired, axiom-clean, 26
declarations) proves the analytic heart of sections 2 and 4.

- `unitRieszAtom` — the `r`-th arithmetic atom `1_{log r <= v}(exp(-v) - sqrt r exp(-3v/2))`, with
  `unitRieszAtom_nonneg` (each atom is nonnegative on its own support, vanishing exactly at the
  switch-on point) and `unitRieszAtom_le` (each atom is bounded by `exp(-v)`).
- **`unitRieszLogProfile_eq_tsum`** — the corpus's cell-assembled profile *is* the atom series:
  `w(v) = 3 sum_r unitRieszAtom r v` for `v >= 0`.
- `integral_Ioi_translate`, `integral_Ioi_cexp_neg_mul_shift`, `integral_Ioi_rexp_neg_mul_shift`,
  `setIntegral_Ioi_of_vanishing` — the elementary half-line toolbox.
- **`integral_unitRieszAtomIntegrand`** — each atom's Laplace integral in closed form:
  `exp(-(z+1) log r) ((z+1)^{-1} - (z+3/2)^{-1})`; the `sqrt r` is absorbed exactly by
  `sqrt r = exp(log r / 2)`, so no cpow algebra is needed.
- **`summable_integral_norm_unitRieszAtomIntegrand`** — absolute convergence: the `r`-th norm
  integral is at most `r^{-(Re z + 1)}/(Re z + 1)`, summable for `Re z > 0`.
- **`unitRieszLaplace_eq`** — equation `(6)`:

  ```text
  Lw(z) = (3/2) zeta(1+z) / ((z+1)(z+3/2)),      Re z > 0,
  ```

  by term-by-term integration (`integral_tsum_of_summable_integral_norm`) and the Dirichlet series
  of zeta.  No asymptotics, no unproved interchange.
- `unitRieszMarkovTransform`, **`unitRieszMarkovTransform_eq_mul`** — equation `(7)`:
  `D(z) = z Lw(z) = 3 z zeta(1+z)/(2(z+1)(z+3/2))`.
- **`tendsto_unitRieszMarkovTransform_zero`** — `D(0) = 1`: the zeta pole at `1` supplies exactly
  the unit mass, so the aperture kernel is a probability transform.
- `unitRieszCausalTransform`, **`hasDerivAt_unitRieszCausalTransform`** — equation `(14)` and its
  derivative, off the zeta pole and off the zeta zeros.
- **`unitRieszCoefficientTransform_eq`** — equations `(15)`-`(16)`: the complete simplification

  ```text
  D(z)[H(z)/z + H'(z)] = 3/(2(z+1)(z+3/2)) [zeta(1+z)/(1+z)^2 + zeta'(1+z)/zeta(1+z)].
  ```

- **`tendsto_unitRieszCoefficientResidue`** — equation `(17)`: at a zeta zero `rho` of
  logarithmic-derivative residue `m`, the coefficient transform has residue
  `3m/(2 rho (rho + 1/2))`.  The probability multiplier's own zero cancels one order of the double
  reciprocal-zeta pole but cannot censor the logarithmic-derivative pole.

Still to formalize for this card: the total-mass statement `(5)` in its direct form
(`w(v) -> 1`), the causal-convolution factorization `(11)`, and the Landau connector `(18)`-`(22)`.
