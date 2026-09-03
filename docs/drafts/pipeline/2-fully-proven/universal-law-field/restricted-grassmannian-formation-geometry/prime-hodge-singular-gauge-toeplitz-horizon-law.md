# Prime--Hodge singular-gauge Toeplitz-horizon law

- **ID:** ULF-PHSTH-001
- **Stage:** 2-fully-proven
- **Type:** unconditional pre-divisor completion-classification theorem
- **Parents:** ULF-PHSG-001, ULF-PHIN-001, ULF-PHSF-001
- **Status:** `[PAPER-PROVED] [BRIDGE] [RH SELECTOR RETIRED]`
- **Lean:** not yet formalized; no Lean work was performed in this research pass

## 1. Higher-law interpretation

The pre-divisor integral--nuclear object is not merely a positive density. It is the exact local
displacement of a compact arithmetic completion under one universal open-history shift:

```text
local defect T = compact completion G_A - one-step backward transport of G_A.       (PHSTH.1)
```

Every bounded completion with this same local defect is `G_A` plus a shift-harmonic horizon. Those
horizons are precisely operator-valued Toeplitz operators. No nonzero horizon is compact; a
positive nonzero horizon repeats positive mass at every history grade and therefore has infinite
trace. Consequently the compact completion is unique, and positivity plus any finite trace budget
selects it without amplification.

This is the mechanism hidden by the prior route vocabulary:

```text
closed observer datum  --shift-harmonic lift-->  Toeplitz horizon
                                               |
finite source capacity ------------------------+--> horizon must vanish.
```

The theorem is pre-divisor. It uses literal history weights and a literal prime-mixed positive
trace-class carrier, but no zero, divisor, or RH assumption.

## 2. Corpus and literature audit

Required Lean-corpus searches were run for:

```text
prime Hodge weighted shift Gramian defect trace one open history
operator Toeplitz shift fixed point compact trace class completion
Euler collision capacity strict right zero 115/108 completion transport
cubic Hardy mixed jet landing Cauchy Hessian
theta signed polarization correction no go
```

They found:

- `PrimeHodgeHistorySurvivalFredholmColligation`: the forced survival shift `C`;
- `PrimeHodgeHistoryIntegralNuclearDefect` and
  `PrimeHodgeHistoryIntegralNuclearHomotopyDefect`: the positive and signed objects `T`;
- `PrimeHodgeHistoryFirstExitTransgression`: first-exit curvature reconstructs that same `T`;
- `RoutePCubicHardyMixedJetLanding`: the bare Cauchy-to-cubic jet is already known;
- `HedenmalmThetaSignedPolarizationEscape`: fixed theta-metric corrections cannot converge as
  required;
- `DirectSubunitEscapeCapacityFusion` and `XiWardCubicTranslationEnergySeparator`: the present
  capacity/escape sides, still on different objects.

Discrete Stein equations and the Brown--Halmos characterization of Toeplitz operators are
classical. Modern primary-source formulations include
[the abstract Brown--Halmos property](https://arxiv.org/abs/1802.08438) and
[a recent shift-invariance extension](https://arxiv.org/abs/2411.02962). The fact that a compact
Toeplitz operator must vanish is also standard; a recent application states the same rigidity in
an operator-theoretic setting ([source](https://arxiv.org/abs/2507.00998)). No novelty is claimed
for those abstract results. Corpus-specific content is the singular arithmetic gauge, exact
identification of the already constructed prime-mixed `T` as its displacement, and resulting
finite-capacity completion selector.

## 3. Arithmetic singular gauge

Let `H=ell2(Nat)` with basis `(e_n)` and let `U e_n=e_(n+1)` be the unilateral shift. Recall

```text
m_n=105/((2n+3)(2n+5)(2n+7)),
r_n=m_(n+1)/m_n=(2n+3)/(2n+9),
w_n=m_n-m_(n+1),
C e_n=sqrt(r_n)e_(n+1).
```

Put

```text
Q e_n=sqrt(m_n)e_n,       G=Q^2=diag(m_n),       Phi=diag(w_n).       (PHSTH.2)
```

**Theorem PHSTH-A (singular gauge).** `Q` is positive, compact, injective, and has dense nonclosed
range. It intertwines pure open history with arithmetic survival:

```text
C Q=Q U.                                                               (PHSTH.3)
```

Thus `C=Q U Q^(-1)` on `ran Q`, but `Q^(-1)` is unbounded.

**Proof.** Positivity and boundedness are diagonal. Since `m_n>0` and `m_n->0`, `Q` is injective
and compact. Every basis vector lies in its range, so the range is dense. It is not closed because
`||Q e_n||=sqrt(m_n)->0` while `||e_n||=1`. Finally

```text
C Q e_n=sqrt(m_n r_n)e_(n+1)=sqrt(m_(n+1))e_(n+1)=Q U e_n.
```

Equality on the basis extends by boundedness. QED.

This identity explains why arithmetic history looks contractive in every finite route although
its ungauged lift is the pure noncompact unilateral shift.

## 4. The defect is a shift displacement

Let `K` be any separable Hilbert space and let `A>=0` be trace class on `K`. On
`H tensor K` define

```text
mathcal U=U tensor I_K,
mathcal G_A=G tensor A,
mathcal T_A=Phi tensor A.                                               (PHSTH.4)
```

The prime-Hodge object is obtained by taking `K` to be the prime carrier and `A=A_d`, the literal
positive trace-one prime Cauchy-cube/Stokes formation operator. Then `mathcal T_A` is exactly the
already constructed pre-divisor, prime-mixed, integral--nuclear defect.

**Theorem PHSTH-B (local displacement and reconstruction).**

```text
mathcal G_A-mathcal U* mathcal G_A mathcal U=mathcal T_A,                (PHSTH.5)
mathcal G_A=sum_(j>=0) mathcal U*^j mathcal T_A mathcal U^j              (PHSTH.6)
```

where `(PHSTH.6)` converges in trace norm. Moreover

```text
||mathcal T_A||_1=Tr A,
||mathcal G_A||_1=(7/4)Tr A,
sum_j ||mathcal U*^j mathcal T_A mathcal U^j||_1=(7/4)Tr A.              (PHSTH.7)
```

**Proof.** On grade `n`, the left side of `(PHSTH.5)` is
`(m_n-m_(n+1))A=w_n A`. For `(PHSTH.6)`, its grade-`n` block is

```text
sum_(j>=0) w_(n+j) A=m_n A
```

by the first-exit telescope. The trace norm of the `j`th positive summand is
`m_j Tr A`; ULF-PHSG-001 proves `sum_j m_j=7/4`. This gives trace-norm convergence and all formulas
in `(PHSTH.7)`. QED.

For `Tr A_d=1`, `(PHSTH.7)` recovers integral defect mass one and completion mass `7/4`. For the
signed homotopy object, multiply `(PHSTH.5)` by the chamber orientation; at the neutral parameter
both sides are zero.

## 5. Complete classification of same-defect completions

Let `X` be a bounded operator on `H tensor K` satisfying

```text
X-mathcal U* X mathcal U=mathcal T_A.                                  (PHSTH.8)
```

**Theorem PHSTH-C (Toeplitz-horizon classification).** Every solution has the unique form

```text
X=mathcal G_A+R,       R=mathcal U* R mathcal U.                         (PHSTH.9)
```

Writing `R_(n,m)` for its operator-valued history blocks, the fixed-point law is equivalent to

```text
R_(n,m)=R_(n+1,m+1)                                                    (PHSTH.10)
```

for every `n,m`. Hence the ambiguity is exactly an operator-valued Toeplitz horizon.

**Proof.** Subtract `(PHSTH.5)` from `(PHSTH.8)`. This gives the fixed-point law, and the converse
is immediate. Taking matrix coefficients gives `(PHSTH.10)`. QED.

**Theorem PHSTH-D (compact properness).** A compact fixed point of
`R -> mathcal U*Rmathcal U` is zero. Therefore `mathcal G_A` is the unique compact, Schatten-class,
or trace-class solution of `(PHSTH.8)`.

**Proof.** Iterating the fixed-point equation gives, for all `x,y`,

```text
<R x,y>=<R mathcal U^N x,mathcal U^N y>.
```

The vectors `mathcal U^N x` converge weakly to zero. Compactness therefore gives
`||R mathcal U^N x||->0`, while `||mathcal U^N y||=||y||`. The right side tends to zero, so every
matrix coefficient of `R` vanishes. QED.

Thus the displacement map is proper on its compact fibre over the arithmetic defect: that fibre
is one point.

## 6. Positive finite-capacity selector

**Theorem PHSTH-E (no positive finite horizon).** Suppose `X>=0` satisfies `(PHSTH.8)`. Then

```text
X>=mathcal G_A,
R=X-mathcal G_A>=0,
R=mathcal U*Rmathcal U.                                                 (PHSTH.11)
```

If `R!=0`, its mass repeats at every history grade. In particular `R` is noncompact and not trace
class. Hence

```text
X>=0 and Tr X<infinity  ==>  X=mathcal G_A.                             (PHSTH.12)
```

**Proof.** Iterating `(PHSTH.8)` gives

```text
X=sum_(j<N)mathcal U*^j mathcal T_A mathcal U^j
  +mathcal U*^N X mathcal U^N.
```

The last term is positive. Letting `N->infinity` and using `(PHSTH.6)` gives `X>=mathcal G_A`;
then `(PHSTH.9)` gives the positive fixed point `R`. If `R!=0`, positivity implies some
`v in K` has `b=<R(e_0 tensor v),e_0 tensor v>>0`; otherwise the zero diagonal block, repeated by
`(PHSTH.10)`, would force all blocks to vanish by Cauchy--Schwarz. Shift invariance gives the same
expectation `b` on every orthogonal vector `e_n tensor v`. The traces of the first `N` history
compressions are therefore at least `Nb`, so `R` cannot be trace class. Compact rigidity gives the
stronger compact conclusion. QED.

No numerical amplification is used. Any finite trace ceiling suffices.

## 7. Harmonic/exit lift bifurcation

Let `p>=0`, `p!=0`, be a finite-rank observer on `K`. Its shift-harmonic history lift is

```text
H_p=I_H tensor p.                                                       (PHSTH.13)
```

**Theorem PHSTH-F (observer-opening law).** `H_p` is a positive Toeplitz horizon,

```text
mathcal U* H_p mathcal U=H_p,
P_0 H_p P_0=p,
```

but `H_p` is noncompact and has infinite trace. A closed finite observer therefore projects from
an open lifted history; recurrence of the observer does not close the lift.

**Proof.** The first two identities are immediate from `U*U=I`. The range contains the mutually
orthogonal copies `e_n tensor ran p`, so it has infinite rank with one fixed positive singular
value repeated at every grade. QED.

This is an exact theorem, not a curvature metaphor.

It is not, however, the source's unique or canonical way to form history. The already proved
first-exit mechanism gives the different lift

```text
E_p=Phi tensor p
   =(G tensor p)-mathcal U*(G tensor p)mathcal U.                       (PHSTH.14)
```

**Theorem PHSTH-G (two-lift law).** For finite-rank positive `p`, `H_p` and `E_p` recover the same
observer by different boundary operations:

```text
grade-zero compression of H_p = p,
sum of all history blocks of E_p = p.
```

But `H_p` is shift harmonic, noncompact, and infinite trace, whereas `E_p` is positive trace class
with `Tr E_p=Tr p`. Thus closed observation does not determine open-history behavior. Harmonic
repetition and first-exit formation are inequivalent lifts of the same observer.

**Proof.** The first line for `H_p` is PHSTH-F. For `E_p`, its grade-`n` block is `w_n p`, and
`sum_n w_n=1`; positivity gives trace-norm convergence and trace `Tr p`. Equation `(PHSTH.14)` is
PHSTH-B with `A=p`. QED.

## 8. What this explains and what it does not

The law explains several corpus-wide shadows:

- local routes see the compact coboundary `T`, not the arbitrary noncompact Toeplitz symbol;
- dense source recovery cannot remove a horizon living in the noncompact fixed sector;
- positivity is a quotient: every positive completion is minimal compact completion plus positive
  Toeplitz horizon;
- recurrence is compatible with open history under the harmonic lift `(PHSTH.13)`, but the source
  also has the inequivalent nuclear first-exit lift `(PHSTH.14)`;
- finite capacity is a properness condition, not an energy-amplification argument.

It does **not** identify an actual Xi/theta completion with `(PHSTH.8)`, prove that an off-line zero
creates a nonzero positive horizon, or prove RH. Hypertranscendence has not been identified with
this noncompact sector and is not claimed here.

## 9. Selector failure and surviving leverage

The proposed RH use required a strict-right rank-one horizon to lift as `H_p`. Corpus audit killed
that inference. `IntegralNuclearRelationIncidenceHorizon` supplies the rank-one `p` after divisor
specialization, but ULF-PHSG-001 and `PrimeHodgeHistoryFirstExitTransgression` make `E_p`, not
`H_p`, the literal source formation law. `E_p` has finite trace and causes no contradiction.

Therefore finite capacity plus PHSTH-E is not a selector unless an independent pre-divisor theorem
forces harmonic rather than first-exit lifting. Requiring that theorem merely because `H_p` has
infinite trace is circular. The strongest surviving leverage is the two-lift discriminator:

> any valid completion law must derive, from literal integer/Poisson structure, whether the
> completed horizon is shift harmonic, first-exit formed, or carries a nontrivial relative class
> between them.

This is a no-go/classification advance, not RH selection.

## 10. Hostile audit

- `[LITERATURE]` Shift displacement equations, Toeplitz fixed points, and compact Toeplitz rigidity
  are classical.
- `[PAPER-PROVED]` The exact arithmetic gauge `(PHSTH.3)`, displacement `(PHSTH.5)`, trace-norm
  reconstruction `(PHSTH.6)`, compact fibre theorem, finite-trace selector, and observer-opening
  law are dependency-closed.
- `[PAPER-PROVED]` PHSTH-G exhibits the competing nuclear first-exit lift of the same observer.
- `[CORPUS FUSION]` The same pre-existing `m_n,w_n,A_d` now generate both compact completion and
  prime-mixed defect; no fitted divisor datum enters.
- `[NOT PROVED]` Actual polar--Gamma/theta completion has this displacement.
- `[FALSIFIED AS SOURCE INFERENCE]` A strict-right rank-one horizon is not automatically the
  harmonic lift `I tensor p`; the literal source already supplies `Phi tensor p`.
- `[NOVELTY]` No claim for general operator theory. Potential new content is only its exact
  arithmetic fusion and RH reduction; independent priority review remains required.
