# Theta Mellin-six holonomy forms the integral--nuclear history

- **ID:** ULF-TM6H-001
- **Stage:** 2-fully-proven
- **Type:** unconditional pre-divisor four-organ formation theorem
- **Parents:** ULF-DHNJ-001, ULF-PPTI-001;
  `EulerHedenmalmGammaStokesTransgression`,
  `EulerPrimitivePolarizedHodgeBetaTransgression`
- **Surviving RH edge:** the source history of the prime-mixed defect is now literally theta-formed;
  the remaining edge is a same-boundary theorem carrying this formed defect into completed Xi
  relative energy without supplying a divisor or restating RH.

## 1. Higher-law interpretation

The history marginal of the prime-mixed integral--nuclear defect is not an auxiliary Kummer law.
It is the discrete transgression of one literal theta atom.  Remove the universal Euler pole
polynomial from the atom's Mellin response, move six units in Mellin degree, and normalize at the
first admissible grade.  The result is exactly every survival tail of `mathsf T`; its adjacent
loss is exactly every emitted nuclear weight.

```text
literal theta first atom
  -- Mellin transform --> Euler pole polynomial * Gamma_R
  -- strip pole polynomial --> Gamma_R
  -- normalized shift by six --> Hodge survival m_n
  -- adjacent transgression --> nuclear flux w_n
  -- tensor prime Poisson Gram --> mathsf T.
```

No zero, Xi divisor, ordinate, fitted clock, or RH premise occurs.  The shift by six is not a
chosen scale: it is the composition of the two source-forced `3/2` Hellinger sewings in
ULF-DHNJ-001, expressed in the doubled Mellin coordinate of `Gamma_R`.

## 2. Corpus audit before formulation

Lean-corpus searches for `theta cusp source Mellin transform first atom Gamma half density`,
`Hodge column beta history tail m_n gamma product recurrence`, `Gamma six theta first atom
history tail normalized Mellin holonomy universal polynomial anomaly`, and `thetaCuspSeed
archFactor normalized Hodge history` found:

- `mellin_thetaCuspSeed_eq_archFactor`: the literal first theta atom has Mellin transform
  `A(s)=s(s-1)Gamma_R(s)/2` on `Re(s)>0`;
- `eulerPrimitiveBoundaryHodgeBetaColumn_eq_gammaRatio`: the forced odd-Hodge response is
  `h(a)=-Gamma(a+1/2)Gamma(3/2)/Gamma(a+2)`;
- `eulerPrimitiveBoundaryHodgeBetaColumn_add_one`: its coface ratio is
  `(a+1/2)/(a+2)`;
- ULF-DHNJ-001: `m_n=h(n+1)h(n+5/2)/(h(1)h(5/2))`;
- ULF-PPTI-001: the prime--history operator is `mathsf T=Phi tensor A_d`, where
  `Phi=diag(w_n)`, `w_n=m_n-m_(n+1)`, and `A_d` is the coefficient-faithful prime Cauchy cube.

No checked theorem identifies `m_n` with a normalized Mellin shift of the literal theta atom or
reconstructs `mathsf T` from that shift.

## 3. Pole-stripped theta response

Let `theta_1(t)=thetaCuspSeed(t)` be the literal first theta atom and, for real `s>1`, put

```text
A(s)=integral_(0,infinity) t^(s-1) theta_1(t) dt,
G_theta(s)=2 A(s)/(s(s-1)).                          (TM6H.1)
```

Corpus theorem `mellin_thetaCuspSeed_eq_archFactor` gives

```text
A(s)=s(s-1) Gamma_R(s)/2,
G_theta(s)=Gamma_R(s).                               (TM6H.2)
```

This stripping is forced.  It removes exactly the universal polynomial which cancels the Euler
poles in the completed Xi carrier; no scalar function remains to choose.  Restriction to `s>1`
keeps all divisions source-side and nonzero.

Define the normalized Mellin-six holonomy

```text
H_n = [G_theta(2n+3)/G_theta(2n+9)]
      /[G_theta(3)/G_theta(9)].                      (TM6H.3)
```

## 4. Exact theta-to-history theorem

**Theorem TM6H-A (theta formation of Hodge history).**  For every `n>=0`,

```text
H_n = 105/[(2n+3)(2n+5)(2n+7)] = m_n.               (TM6H.4)
```

Consequently

```text
H_0=1,
H_n-H_(n+1)=w_n,
sum_(k>=n) (H_k-H_(k+1))=H_n.                        (TM6H.5)
```

**Proof.**  Deligne's real Gamma factor obeys

```text
Gamma_R(s+2)=s/(2 pi) Gamma_R(s).
```

Three iterations give

```text
Gamma_R(s)/Gamma_R(s+6)
 =8 pi^3/[s(s+2)(s+4)].                              (TM6H.6)
```

Insert `s=2n+3`, divide by the same formula at `s=3`, and use `(TM6H.2)`:

```text
H_n
 =[8pi^3/((2n+3)(2n+5)(2n+7))]/[8pi^3/(3*5*7)]
 =105/[(2n+3)(2n+5)(2n+7)].
```

This is `PrimeHodgeHistory.m n`.  Equations `(TM6H.5)` are the definition of `w_n` and the
already proved positive telescope. QED.

## 5. Why the double-Hodge product collapses to one theta holonomy

The Hodge response can itself be written in the pole-stripped theta coordinate:

```text
h(a)=-(1/(2pi)) G_theta(2a+1)/G_theta(2a+4).         (TM6H.7)
```

Indeed `G_theta=Gamma_R`, and the definition of `Gamma_R` turns the right side into
`-Gamma(a+1/2)Gamma(3/2)/Gamma(a+2)`.

At the two forced grades from ULF-DHNJ-001, the middle response cancels:

```text
h(n+1)h(n+5/2)
 =(1/(4pi^2))
   [G_theta(2n+3)/G_theta(2n+6)]
   [G_theta(2n+6)/G_theta(2n+9)]
 =(1/(4pi^2)) G_theta(2n+3)/G_theta(2n+9).           (TM6H.8)
```

Thus the earlier double-Hellinger factorization is the local two-chart expression of one global
theta Mellin-six holonomy.  The half-density grade `2n+6` is an internal gauge and disappears
from the recovered history; the endpoints remain.

## 6. Reconstruction of the prime-mixed integral--nuclear object

Let

```text
Phi_theta e_n=(H_n-H_(n+1))e_n,
A_d=W_d^* W_d,
mathsf T_theta=Phi_theta tensor A_d.                 (TM6H.9)
```

By `(TM6H.4)--(TM6H.5)`, `Phi_theta=Phi` exactly.  Therefore

```text
mathsf T_theta=mathsf T_d.                           (TM6H.10)
```

All conclusions of ULF-PPTI-001 transfer without alteration:

- `mathsf T_theta` is positive and Schatten `S_1`;
- `Tr(mathsf T_theta)=||mathsf T_theta||_1=1`;
- every same-history cross-prime matrix entry is nonzero;
- every history-tail trace is `H_n=m_n`;
- every unsquared prime coefficient is retained in the formation map `Q_d`.

This is a literal formation theorem: theta controls the history flux, the degree-three Poisson
sector controls prime mixing, and their tensor incidence is the pre-divisor object nobody asked
for.

## 7. Joint conservation and exact limitation

Combining `(TM6H.5)` with the source Fredholm colligation gives

```text
normalized theta Mellin-six boundary loss
 =sum_n(H_n-H_(n+1))
 =Tr(Phi_theta)
 =Tr(mathsf T_theta)
 =-index(C)
 =1.                                                 (TM6H.11)
```

This identifies the integral orientation as an archimedean boundary transgression before any
divisor exists.  It also removes one false open problem: no additional producer is needed for the
history law of `mathsf T`.

It does **not** prove RH.  The remaining theorem is not another source object or scalar
contractivity estimate.  One must prove that completed Xi relative energy is the same boundary
functional as `(TM6H.11)`, after the already forced relative metric anomaly is removed, and that
the completed residual boundary vanishes.  Supplying a zero and evaluating `(TM6H.3)` on its
grade would be a receiver and is disallowed.

## 8. Literature scope

Mellin transforms of Gaussian theta kernels, the recurrence of `Gamma_R`, and Beta/Gamma
factorizations are classical.  Current primary-source search also finds general Poisson/Mellin
and local-Gamma transform frameworks.  No novelty claim is made for those ingredients.  The
proved corpus statement is their exact joint identification with the prime-mixed nuclear history
and its integral Fredholm flux.

