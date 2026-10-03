# Theta Mellin-six holonomy forms the integral--nuclear history

- **ID:** ULF-TM6H-001
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
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

## Lean certificate

- [x] 2 → 3: Lean `GaloisForLFunctions.RHTower.ThetaMellinSixIntegralNuclearFormation`, `GaloisForLFunctions.RHTower.ThetaMellinSixHodgeFormation`; `lake env lean` + module build pass; axiom audit `[propext, Classical.choice, Quot.sound]` only

Modules `GaloisForLFunctions.RHTower.ThetaMellinSixIntegralNuclearFormation` (corpus) and
`GaloisForLFunctions.RHTower.ThetaMellinSixHodgeFormation` (new), on the corpus cores
`RHTower.PrimeHodgeHistoryIntegralNuclearDefect`, `RHTower.PrimeHodgeHistorySurvivalFredholmColligation`,
`RHTower.EulerPrimitivePolarizedHodgeBetaTransgression`; all `lake env lean` clean, built, axiom audit
`[propext, Classical.choice, Quot.sound]` only.  `G_θ = thetaCuspPoleStrippedMellinResponse`,
`H_n = thetaCuspMellinSixHolonomy n`.

| Claim | Lean declaration |
|-|-|
| (TM6H.1)–(TM6H.2) `A(s) = s(s-1)Γ_ℝ(s)/2`, `G_θ = Γ_ℝ` on `Re s > 1` | corpus `mellin_thetaCuspSeed_eq_archFactor`, `thetaCuspPoleStrippedMellinResponse`, `thetaCuspPoleStrippedMellinResponse_eq_GammaR` |
| (TM6H.3) normalized Mellin-six holonomy | `thetaCuspMellinSixHolonomy` |
| (TM6H.6) `Γ_ℝ(s)/Γ_ℝ(s+6) = 8π³/(s(s+2)(s+4))` | `gammaReal_shift_six`, `gammaReal_div_shift_six` |
| Theorem TM6H-A, (TM6H.4) `H_n = 105/((2n+3)(2n+5)(2n+7)) = m_n` | `thetaCuspMellinSixHolonomy_eq_primeHodgeHistory_m` |
| (TM6H.5) `H_0 = 1`, `H_n - H_{n+1} = w_n`, tail sums | `thetaCuspMellinSixHolonomy_zero`, `thetaCuspMellinSixHolonomy_sub_succ_eq_primeHodgeHistory_w`, `thetaCuspMellinSixFlux`, `thetaCuspMellinSixFlux_eq_primeHodgeHistory_w`, `thetaCuspMellinSixFlux_tail_hasSum` |
| (TM6H.7) `h(a) = -(1/2π) G_θ(2a+1)/G_θ(2a+4)` (Γ_ℝ form for `a > -1/2`, theta form for `a > 0`) | `gammaReal_ofReal`, `eulerPrimitiveBoundaryHodgeBetaColumn_eq_gammaReal`, `eulerPrimitiveBoundaryHodgeBetaColumn_eq_thetaResponse` |
| (TM6H.8) `h(n+1)h(n+5/2) = (1/4π²) G_θ(2n+3)/G_θ(2n+9)` | `hodgeBetaColumn_product_eq_thetaHolonomy` |
| (TM6H.9)–(TM6H.10) `𝖳_θ = Φ_θ ⊗ A_d = 𝖳_d`; positive, S₁, trace = trace norm = 1, prime-mixed, history tails `H_n` | `thetaFormedDefectOperator`, `historyStokesKernel_thetaFlux`, `thetaFormedDefectOperator_eq`, `thetaFormedDefectOperator_properties`, `primeHodgeHistoryDiagonalWeight_eq_thetaCuspMellinSixFlux`, `zero_lt_thetaCuspMellinSixFlux` |
| Unsquared prime coefficients retained in the formation map `Q_d` | `historyFormationChannel`, `adjoint_comp_historyFormationChannel` (ULF-PPTI-001) |
| (TM6H.11) `∑(H_n-H_{n+1}) = Tr Φ_θ = Tr 𝖳_θ = -ind C = 1` | `thetaMellinSix_boundaryLoss_conservation`, corpus `primeHodgeHistorySurvivalShiftIndex_eq_neg_one`, `opTrace_primeHodgeHistoryFluxOperator` |

§7's same-boundary theorem for completed Xi relative energy is explicitly open in the card and is
not claimed.

## Log

- 2026-10-03 — Lean certificate audited; every numbered claim mapped to a declaration; moved to 3-formalized.
