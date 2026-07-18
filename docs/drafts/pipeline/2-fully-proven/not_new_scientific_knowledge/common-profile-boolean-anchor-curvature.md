# Common-profile Boolean response and anchor-curvature identity

- **ID:** `common-profile-boolean-anchor-curvature`
- **Stage:** `2-fully-proven`
- **Type:** `[PAPER-PROVED] [BRIDGE] [REDISCOVERED] [POSITIVE SALVAGE]`
- **Source:** `critical-multiplicative-compensated-cancellation-rh.md`, `(PF1)`, `(AC13)`,
  `(AC24)`
- **Statement:** The complete future Bernoulli average of the causally anchored primitive
  response is exactly a squarefree-sieved physical occupancy minus its Euler vacuum; when the
  common physical profile is a Gram kernel, the height-summed occupancy is exactly the Boolean
  anchor curvature of the sifted Gram energy.

## Exact response statement

Fix a gap `h`, a squarefree anchor `c`, and a squarefree future packet `N` with `(c,N)=1`.  Write

```text
nu_h(q)=#{x mod q:q|x(x+h)},
theta_h(q)=nu_h(q)/q,
V_N(h)=product_(p|N)(1-theta_h(p)),
w_(N,h)(r)=theta_h(r)V_(N/r)(h),              r|N.
```

Let `W_h` be the common physical profile, extended by zero, and let `J_h=integral_R W_h`.  With
the Fourier convention of `(PF1)`, define

```text
A_(q,h)=1/nu_h(q) sum_(u!=0) hat(W)_h(u/q)S_(q,h)(u),

B_(c,r,h)=1/(nu_h(c)nu_h(r))
  sum_(u!=0,(u,r)=1)hat(W)_h(u/(cr))S_(cr,h)(u),

Eresp_(c,N,h)=sum_(r|N)mu(r)w_(N,h)(r)B_(c,r,h).
```

Then

```text
B_(c,r,h)=sum_(d|r)mu(d)A_(cr/d,h),                    (CG1)

Eresp_(c,N,h)=sum_(e|N)mu(e)theta_h(e)A_(ce,h),        (CG2)

Eresp_(c,N,h)
 =c/nu_h(c) sum_m W_h(m)1_(c|m(m+h))P_N(m)P_N(m+h)
   -J_h V_N(h),                                        (CG3)
```

where

```text
P_N(m)=product_(p|N)1_(p does not divide m).
```

Equivalently, the normalization that interfaces with `(AC24)` is

```text
theta_h(c)Eresp_(c,N,h)
 =sum_m W_h(m)1_(c|m(m+h))P_N(m)P_N(m+h)
   -theta_h(c)J_hV_N(h).                               (CG4)
```

## Common-Gram anchor curvature

Let `C` be the prime-factor set of `c`.  Suppose a finitely supported real Hilbert packet `g_m`
realizes the same profile:

```text
W_h(m)=<g_m,g_(m+h)>.
```

For every finite prime set `S`, put

```text
P_S(m)=product_(p in S)1_(p does not divide m),
Energy(S)=||sum_m P_S(m)g_m||^2.
```

Then the physical occupancy has the exact Boolean curvature law

```text
sum_(h,m)W_h(m)1_(c|m(m+h))P_N(m)P_N(m+h)
 =sum_(D subset C)(-1)^|D| Energy(N union D).           (CG5)
```

Consequently `(CG4)` joins globally as

```text
sum_h theta_h(c)Eresp_(c,N,h)
 =sum_(D subset C)(-1)^|D| Energy(N union D)
   -sum_h theta_h(c)V_N(h)J_h.                         (CG6)
```

The finite theorem is stronger than the Boolean specialization.  If arbitrary real coordinate
weights `a_p(m)` replace `1_(p does not divide m)`, define

```text
a_S(m)=product_(p in S)a_p(m),
Anchor_C(m,n)=product_(p in C)(1-a_p(m)a_p(n)).
```

For disjoint finite coordinate sets `N,C`, one still has

```text
sum_(m,n)a_N(m)a_N(n)Anchor_C(m,n)<g_m,g_n>
 =sum_(D subset C)(-1)^|D| ||sum_m a_(N union D)(m)g_m||^2.  (CG7)
```

This weighted strengthening is forced by the algebra and remains an elementary bridge.

## Dependency-closed paper proof

For `(CG1)`, insert

```text
1_((u,r)=1)=sum_(d|(u,r))mu(d)
```

into the definition of `B`.  In the `d`-term write `u=dv`.  Because `r` is squarefree and
`(c,r)=1`, the modulus `d` is coprime to `c(r/d)`, so reduced-frequency CRT lifting gives

```text
S_(cr,h)(dv)=nu_h(d)S_(c(r/d),h)(v).
```

Multiplicativity gives `nu_h(cr)=nu_h(c)nu_h(d)nu_h(r/d)`.  The factor `nu_h(d)` therefore
cancels exactly and the remaining term is `mu(d)A_(cr/d,h)`.  This proves `(CG1)` with the
normalization in `(AC13)`; no primitivity condition along the anchor `c` has been introduced.

Substitute `(CG1)` into `Eresp`, put `r=de`, and use squarefreeness.  Since `d` and `e` are
coprime,

```text
mu(de)mu(d)=mu(e),
theta_h(de)=theta_h(d)theta_h(e).
```

For each fixed `e`, the remaining `d`-sum is the complete Bernoulli mass

```text
sum_(d|N/e)theta_h(d)V_(N/(de))(h)=1.
```

This proves `(CG2)`.

Equation `(PF1)` says

```text
A_(q,h)=q/nu_h(q) delta_h(e_q).
```

Hence `(CG2)` and `(c,N)=1` give

```text
Eresp_(c,N,h)=c/nu_h(c) sum_(e|N)mu(e)delta_h(e_(ce)).
```

Expanding `delta_h=beta_h-J_h theta_h`, finite inclusion-exclusion gives

```text
sum_(e|N)mu(e)beta_h(e_(ce))
 =sum_m W_h(m)1_(c|m(m+h))P_N(m)P_N(m+h),

sum_(e|N)mu(e)theta_h(ce)=theta_h(c)V_N(h).
```

Multiplication by `c/nu_h(c)=1/theta_h(c)` proves `(CG3)` and `(CG4)`.

For `(CG5)`, change variables `n=m+h`.  The left side becomes the finite double Gram sum

```text
sum_(m,n)<g_m,g_n>P_N(m)P_N(n)1_(c|mn).
```

For the squarefree anchor,

```text
1_(c|mn)
 =product_(p in C)(1-1_(p does not divide m)1_(p does not divide n))
 =sum_(D subset C)(-1)^|D|P_D(m)P_D(n).                (CG8)
```

Interchange the finite sums and use Gram polarization:

```text
sum_(m,n)P_(N union D)(m)P_(N union D)(n)<g_m,g_n>
 =||sum_m P_(N union D)(m)g_m||^2.
```

This proves `(CG5)` and `(CG6)`.  The same product expansion with arbitrary `a_p(m)` proves
`(CG7)`.

## Hostile audit and exact significance

- **Normalization:** omitting `c/nu_h(c)` in `(CG3)` is false.  The correct AC13-facing form is
  `(CG3)`, and the density-weighted AC24-facing form is `(CG4)`.
- **No independent profiles:** `(CG5)` uses one common Gram family `g_m`; it does not hold for
  sectorwise independently chosen response profiles.
- **No positivity:** Boolean curvature is an alternating sum of positive energies, not a positive
  energy.  Already for one anchor coordinate it is `Energy(N)-Energy(N union {p})`, which can have
  either sign because deleting one vector packet can remove constructive or destructive
  interference.
- **No estimate:** `(CG6)` is an exact change of representation.  It neither bounds the curvature
  nor cancels the Euler vacuum at the `M^(-1)` scale.
- **No RH smuggling:** no zero location or Mertens-strength input appears.  Conversely, the
  unresolved bound for the actual `g_m` remains the same response-correlation problem as `(AC25)`.
- **Internal corpus:** the local tree already contains the Bernoulli mass law, reduced-frequency
  alias lifting, and finite inclusion-exclusion product.  It does not contain this exact common-Gram
  response/curvature join.
- **Parent theory:** `(CG1)`--`(CG7)` are finite Boolean Möbius inversion, CRT alias lifting, and
  Gram polarization.  The verdict is `REDISCOVERED` / `BRIDGE`, not new scientific knowledge.

The exact positive insight is nevertheless useful: **the common physical profile prevents
sectorwise response steering and turns the global future response into a Boolean finite
difference of one energy functional.**  The remaining analytic question is now whether that
specific energy curvature cancels its explicit Euler vacuum after the full causal
`h,p,a,r` joining; positivity or abstract Hilbert geometry alone cannot do so.

## Gates

- [x] Audited against the exact `(PF1)`, `(AC13)`, and `(AC24)` normalizations.
- [x] Checked squarefree/coprime hypotheses and the protected-anchor frequency condition.
- [x] Completed the response, occupancy, and common-Gram paper proof.
- [x] Hostile sign, source-independence, and circularity audit.
- [x] Classified under standard Boolean Möbius inversion and Gram polarization.
- [ ] Exact Lean theorem and axiom gate.

