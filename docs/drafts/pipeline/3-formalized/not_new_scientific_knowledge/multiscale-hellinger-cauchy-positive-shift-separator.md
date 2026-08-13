# Multiscale Hellinger--Cauchy positive-shift separator

- **ID:** `multiscale-hellinger-cauchy-positive-shift-separator`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) / BRIDGE / NOT NEW SCIENTIFIC KNOWLEDGE
- **Source:** `../../1-in-progress/zeta23-beyond-bandwidth-one-proportion.md`
- **Statement:** Logarithmic-scale dyadic semigroup differences give a fixed positive diagonal
  quantum for every positive horizontal shift, zero quantum at shift zero, and a finite
  multiplicity energy with no negative cross channel.
- **Formal module:**
  `formal/GaloisForLFunctions/RHTower/XiWardMultiscaleHellingerCauchySeparator.lean`
- **Scientific status:** `[PAPER-PROVED] [LEAN-PROVED] [BRIDGE] [NOT RH]`
  `[NO COMPUTATION] [NO DENSITY IMPROVEMENT CLAIMED]`

## Goal

Resolve the local submicroscopic obstruction exposed by the Zeta-23 audit without choosing a
scale from an unknown zero. Fixed finite-band and finite-prime detectors are continuous at
horizontal displacement zero, so their uniform off-line quantum vanishes. The survivor replaces
one fixed scale by the complete logarithmic scale axis.

## Gates

- [x] 0 → 1 in-progress: source role, exact kernel, and hostile continuity test fixed.
- [x] 1 → 2 fully-proven: complete paper proof below; no open dependency in the finite-packet
  theorem.
- [x] 2 → 3 formalized: targeted module build and standard-axiom audit pass.
- [ ] 3 → 4 publication-ready: not pursued; the kernel is classical
  Frullani/Littlewood--Paley calculus and the source upper bound remains open.

## Exact theorem

For `a >= 0` define the dyadic semigroup difference

```text
q_a(r) = exp(-a r) - exp(-2 a r),  r>0.
```

For `a,b>0`, its logarithmic-scale Gram entry is

```text
K(a,b)
 = integral_0^infinity q_a(r)q_b(r) dr/r
 = log (((a+2b)(2a+b))/(2(a+b)^2)).                    (1)
```

If either argument is zero, set `K=0`. Since

```text
(a+2b)(2a+b) - 2(a+b)^2 = ab,
```

every positive-positive entry is strictly positive. On the diagonal,

```text
K(a,a)=log(9/8)                                         (2)
```

for every `a>0`, independently of its size.

For `h>0`, tensor `(1)` with the real Gram kernel of vertically damped characters:

```text
V_h(delta)=h/(h^2+delta^2)>0.
```

For finite depths `a_j>0`, ordinates `gamma_j`, and integral multiplicities `m_j`, put

```text
E_h = sum_(j,k) m_j m_k K(a_j,a_k)V_h(gamma_j-gamma_k).
```

All entries are nonnegative, while the diagonal equals
`m_j^2 log(9/8)/h`. Therefore

```text
sum_j m_j <= sum_j m_j^2 <= h/log(9/8) E_h.             (3)
```

No shallow-depth restriction, ordinate separation, random signs, or zero-adapted scale occurs.
Critical displacement contributes exactly zero.

If `N=N_0+2R`, `(3)` gives the exact receiver

```text
h/log(9/8) E_h <= N/8  ==>  3N/4 <= N_0.                (4)
```

## Paper proof

Near `r=0`, `q_a(r)q_b(r)/r=O(ab r)`; at infinity it decays exponentially. Expanding the product
and grouping two Frullani differences gives

```text
K(a,b)
 = integral [exp(-(a+b)r)-exp(-(a+2b)r)] dr/r
   + integral [exp(-2(a+b)r)-exp(-(2a+b)r)] dr/r
 = log((a+2b)/(a+b)) + log((2a+b)/(2(a+b))),
```

which is `(1)`. The displayed algebraic difference proves strict positivity; `b=a` proves `(2)`.
The elementary Laplace transform of the damped characters gives `V_h`. Every term of the tensor
Gram sum is then nonnegative, so discarding mixed terms and using `m_j<=m_j^2` proves `(3)`.
Substituting `R<=h E_h/log(9/8)` into `N=N_0+2R` proves `(4)`. `QED`

## Lean certificate

The formal module proves:

- `dyadicHellingerHorizontalKernel_zero_left` and `_zero_right`;
- `dyadicHellingerHorizontalKernel_symm`;
- `dyadicHellingerHorizontalKernel_pos`;
- `dyadicHellingerHorizontalKernel_self`;
- `dampedVerticalCauchyKernel_pos`;
- `multiscaleHellingerCauchyKernel_pos` and `_self`;
- `finiteMultiscaleHellingerCauchyEnergy_nonneg`;
- `finiteMultiscaleHellingerCauchyEnergy_ge_diagonal`;
- `sum_multiplicity_le_multiscaleHellingerCauchyEnergy`;
- `xiRight_card_le_multiscaleHellingerCauchyEnergy`;
- `three_quarters_line_of_multiscaleHellingerCauchyEnergy`.

Targeted validation:

```text
lake build GaloisForLFunctions.RHTower.XiWardMultiscaleHellingerCauchySeparator
```

passes. `#print axioms` on the headline declarations reports exactly
`[propext, Classical.choice, Quot.sound]`. Forbidden-token and diff checks pass. The umbrella
`formal/GaloisForLFunctions/RHTower.lean` imports the module.

## Hostile audit

1. Compact scale intervals fail: their diagonal tends to zero as `a->0`.
2. Fixed prime cutoffs fail below `a log N`: the formalized critical-window profile tends to zero.
3. Choosing `N` or `r` from a named zero would be circular. The measure `dr/r` is fixed before the
   divisor and is dilation-invariant.
4. The theorem is zero-side. It does not prove the full square function lies in a bounded
   Euler--Gamma source domain.
5. A source bound assumed only after specializing to Xi root vectors would restate the RH-bearing
   descent already retired elsewhere in corpus.

## Novelty boundary

Frullani identity, semigroup square functions, and Cauchy Gram positivity are classical. No
external novelty is claimed. Corpus contribution is the bridge showing that all-scale
Littlewood--Paley accumulation exactly supplies the discontinuous positive-shift quantum demanded
by the submicroscopic Zeta-23 obstruction, while retaining multiplicity and eliminating signed
cross terms.

## Open source core

Construct the complete logarithmic-scale square function from one pre-spectral rational-prime and
Gamma source, then prove its height-window budget at the constant required by `(4)`. This is
strictly stronger than the finite-packet theorem and remains open. No unconditional zero-density
improvement follows from the present module alone.

## Log

- 2026-08-13 — conjectured from the collision barrier; fixed-scale and finite-prime variants
  falsified.
- 2026-08-13 — exact Frullani kernel, positive mixed Gram law, multiplicity bound, Xi
  specialization, and three-quarters receiver paper-proved and formalized in Lean.
