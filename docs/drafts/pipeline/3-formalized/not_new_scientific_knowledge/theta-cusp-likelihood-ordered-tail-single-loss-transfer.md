# Theta-cusp likelihood-ordered tail has only one enclosure loss

- **ID:** `theta-cusp-likelihood-ordered-tail-single-loss-transfer`
- **Stage:** 3-formalized/not_new_scientific_knowledge
- **Type:** THEOREM / `[VALUE RELATION] [TOP-DOWN HYPOTHESIS DISCHARGE]`
- **Scientific status:** `[FORMALIZED] [BRIDGE] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Parents:** `../../1-in-progress/theta-cusp-dominant-first-atom-ratio-certificate.md`;
  `../../1-in-progress/theta-cusp-thermal-susceptibility-window.md`
- **Lean inputs:** `PrimeArchThetaSourceAtomDomination.lean`;
  `PrimeArchThetaAtomLikelihoodRatio.lean`
- **Lean output:** `PrimeArchThetaLikelihoodOrderedTailTransfer.lean`
- **Statement:** The exact likelihood-ratio order of the higher theta atoms makes their relative
  moment weights decrease with moment order. Therefore each of the two first-atom-to-full-source
  transfers loses only one factor `3005/2997`, rather than the square used by the existing
  coordinatewise enclosure.

## Setup

Write the completed even theta moments as

```text
m_j=a_j+r_j,
```

where `a_j` is the first-atom moment and `r_j` is the sum of all higher-atom moments. The formal
source already supplies

```text
a_j>0,
r_j>0,
r_j<=(8/2997)*a_j,
m_j<=(3005/2997)*a_j.                                    (1)
```

Put `c=3005/2997`. The newer Born--Witten likelihood-ratio theorem is stronger than `(1)`. Its
division-free moment form says, for every `k,n`,

```text
r_(k+n)*a_k <= a_(k+n)*r_k.                              (2)
```

Since every `a_k` is positive, the relative tail weights `t_k=r_k/a_k` are nonincreasing:

```text
0<t_(k+1)<=t_k<=c-1.                                    (3)
```

This is the exact value relation that the coordinatewise enclosure discards.

## Single-loss transfer for the lower susceptibility gate

Assume the first atom satisfies

```text
14*c*a_2^2 <= 9*a_1*a_3.                                (4)
```

The case `(k,n)=(1,1)` of `(2)` gives

```text
m_2*a_1=(a_2+r_2)*a_1
       <=a_2*(a_1+r_1)=a_2*m_1.                         (5)
```

Hence

```text
14*m_2^2
 <=14*a_2^2*m_1^2/a_1^2
 <=9*a_3*m_1^2/(c*a_1).
```

By `(1)`, `m_1<=c*a_1`, while `a_3<=m_3`. Therefore

```text
9*a_3*m_1^2/(c*a_1) <= 9*m_1*m_3,
```

and so

```text
14*m_2^2 <= 9*m_1*m_3.                                  (6)
```

The previous sufficient condition used `14*c^2*a_2^2<=9*a_1*a_3`. Equation `(4)` removes one
complete tail-enclosure loss.

## Single-loss transfer for the upper susceptibility gate

Assume instead that

```text
16*c*a_0*a_2 <= 45*a_1^2.                               (7)
```

Again `(5)` gives `m_2<=a_2*m_1/a_1`, and `(1)` gives `m_0<=c*a_0`. Thus

```text
16*m_0*m_2
 <=16*c*a_0*a_2*m_1/a_1
 <=45*a_1*m_1
 <=45*m_1^2.                                             (8)
```

Consequently `(7)` implies the full-source relaxed fourth-moment concentration inequality. The
previous sufficient condition used `16*c^2*a_0*a_2<=45*a_1^2`; here too one enclosure factor is
unnecessary.

## Probability form

After normalizing the first and higher parts separately, `(2)` says that every size-biased
higher-atom state is below the corresponding first-atom state in likelihood-ratio order. Size
biasing multiplies both densities by the same positive power and therefore preserves their
likelihood ratio. The moment ratio of the higher component can never overtake the first-atom
ratio. Algebraically this is exactly `(5)`.

For the `k=0` coefficient of variation, the algebraic envelope is saturated only by the
degenerate limiting configuration in which the added tail mass sits at the origin. The tail can
cost the inverse first-atom mixture weight once, but it cannot independently inflate both the
zeroth and fourth moments. The old `c^2` transfer paid for precisely that impossible independent
inflation.

## RH-facing consequence

The complete top-down chain is now

```text
14*c*a_2^2<=9*a_1*a_3
  + 16*c*a_0*a_2<=45*a_1^2
  + prime--Gamma degree-two integer-polynomial tail positivity
    -> complete theta susceptibility window
    -> every integer-polynomial prime--Gamma Hankel test is nonnegative
    -> RH.                                                (9)
```

The degree-two tail and the two first-atom inequalities remain open. The theorem strictly
weakens both first-atom interfaces and uses only source relations already present in the corpus;
it does not assume any Xi divisor location, real-rootedness, anti-Herglotz sign, or limiting
measure.

The same replacement applies mathematically to the two-channel Rayleigh--Ritz and quadratic Stein
certificates: their buffered coefficient `14*c^2-9` may be replaced by `14*c-9`. The direct
first-atom transfer and RH consumer are formalized here; certificate-specific adapters remain
separate compatibility work. The independent relaxed radial certificate loses one factor `c` in
the same way.

## Literature calibration

Monotone-likelihood-ratio order and its preservation under multiplication of both densities by a
common positive weight are standard total-positivity facts. No external theorem is needed for
the present implication: the required cross-moment inequality `(2)` is already proved directly
from the explicit theta kernel in `PrimeArchThetaAtomLikelihoodRatio.lean`. The project result is
the algebraic single-loss synthesis `(4)`--`(8)`, so no novelty claim is made.

## Gates

- [x] isolate the relative tail sequence `t_j=r_j/a_j`
- [x] derive its monotonicity from the exact theta likelihood-ratio kernel
- [x] prove the lower-gate transfer with one factor `c`
- [x] prove the upper-gate transfer with one factor `c`
- [x] splice both sharpened gates into the RH-facing theta/Hankel chain
- [x] formalize the adjacent division-free tail order and both transfer theorems in Lean
- [x] formalize the direct linear-Hankel and degree-two-tail/RH consumers
- [ ] prove the two sharpened first-atom inequalities
- [ ] prove the degree-two prime--Gamma tail
- [ ] RH

The paper proof uses no numerical experiment or computation. The exact Lean target and axiom
audits pass; the public theorems use only `propext`, `Classical.choice`, and `Quot.sound`.

## Exact-budget successor

The reflected half-density value relation later determines the complete weighted higher-atom mass

```text
H=1/2-(4*pi-1)*exp(-pi).
```

Because the relative tail weights in this card are nonincreasing, that one global value gives
`r_0<=H` and `r_1/a_1<=H/(a_0+a_1/8)`.  The resulting transfers no longer use the uniform factor
`c` at all.  The full theorem and its two replacement first-atom conditions are in
`theta-cusp-half-density-ward-laplace-budget-transfer.md`.
