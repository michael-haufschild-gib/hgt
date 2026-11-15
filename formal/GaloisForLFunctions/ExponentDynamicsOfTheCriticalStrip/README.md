# Exponent Dynamics of the Critical Strip (EDCS)

Namespace `GaloisForLFunctions.ExponentDynamicsOfTheCriticalStrip`; umbrella
`ExponentDynamicsOfTheCriticalStrip.lean`.

Theorems of other programmes carry their programme: MMD (MetaplecticMobiusDescent), FCT
(FamilyContinuationTheory), SRT (SquareRootThreshold), MAFT (MixingArithmeticOfTheFloorTrees), GCW
(GreenCalculusOfThePrimeFreeWindow), MZF (MultiscaleMollifiedZetaField), BVI (BezoutValuationIncidence),
AOG (ArithmeticOrientationGeometry), ACS (ArithmeticCastelnuovoSeveri).

## 1. Motivation

Write $\Theta=\sup\operatorname{Re}\rho$ for the abscissa of the zeros of $\zeta$ and $w=\Theta-\tfrac12$ for
the zero width. The corpus reads $\Theta$ in many exact ways: growth of Möbius sums, moments of mollified
$\zeta$, the rate at which window forms turn negative, the growth of orbit correlations. It moves $\Theta$
in one way: the zero-free half-plane $\operatorname{Re}s>\tfrac78$ (MMD). Every other route ends at a
statement of one of three kinds: an estimate at exponent zero is missing; a statement holds at every finite
stage and its limit is the Riemann hypothesis; the object that would carry the sign does not exist in
finite type.

All three are statements about maps that are not there. A reading does not change the number it reads. What
changes it is a map on exponents, a theorem $\Theta\le b\Rightarrow\Theta\le T(b)$ with $T(b)<b$, or a map
between stages, a theorem that passes from stage $n$ to stage $2n$ with a controlled loss. EDCS has these
maps as its objects. In its language a proof of the Riemann hypothesis is one of two things:

> a contraction of $[\tfrac12,1]$ with fixed point $\tfrac12$ applied to a bound with no hypothesis, or a
> stage recursion whose cumulative loss is bounded.

The programme asks which maps exist, where their fixed points lie, what each of them costs, and which
classes of maps provably cannot reach the line.

## 2. Objects

| Object | Lean | Meaning |
|---|---|---|
| Abscissa, width | `zetaZeroAbscissa`, `zetaZeroWidth` (SRT) | $\Theta$ and $w=\Theta-\tfrac12$ |
| Seed | `riemannZeta_zero_mem_quasiRH_strip` (MMD), `zetaZeroWidth_le_three_eighths` (SRT) | a bound with no hypothesis: $\Theta\le\tfrac78$, $w\le\tfrac38$ |
| Ruler | `IsRuler` | a law $P(\beta)$ on exponents with $P(\beta)\Leftrightarrow w\le\beta$ on its range |
| Half ruler | `IsTransmitter`, `IsReceiver` | one direction only: $w\le\beta\Rightarrow P(\beta)$, or $P(\beta)\Rightarrow w\le\beta$ |
| Lever | `IsLever` | a map $T$ with $\Theta\le b\Rightarrow\Theta\le T(b)$ |
| Gap law | `excluded` | the set $\{b:T(b)<b\}$ of values a lever forbids to $\Theta$ |
| Affine lever | `pairingStep c k` (FCT) | $T(b)=(c+b)/k$: the correction of a source sits at the dilated argument $ks-c$ |
| Tower | `IsTower` | abscissas $\Theta_0,\Theta_1,\dots$ with $\Theta_r\le\max(\sigma_0,T_r(\Theta_{r+1}))$ |
| Tower value | `towerValue` | $V=\sum_r c_r/(k_0\cdots k_r)$, the limit of $T_0\circ\dots\circ T_{n}$ |
| Wall | `wall` | the largest value below the seed that every available lever allows |
| Centre | `coupledBarrier` (FCT) | the fixed point $c/(k-1)$ of an affine lever; centred means $\le\tfrac12$ |
| Price | `pairingC` (FCT) | what one factor adds to $c$: $(\tfrac12-\tfrac1m)k$ per completed factor of order $m$, $\tfrac k2-1$ per row twist |
| Stage | — | a finite parameter whose limit is the statement: ratio of a window, aperture, mollifier length, degree, overlap, height |
| Stage map | — | a theorem from stage $n$ to stage $2n$ with a loss |
| Loss, loss exponent | `MarginRate` (MAFT) | the shift needed at a stage; its growth exponent. $\tfrac12$ is trivial, below $\tfrac12$ is a half-plane, bounded is the Riemann hypothesis |
| World | — | a zero configuration or Euler model on which a lever can be tested |

## 3. Language

- A **ruler** reads $w$ exactly. A **transmitter** passes every bound for $w$ to its quantity; a
  **receiver** passes every bound for its quantity to $w$.
- A **lever** moves bounds for $\Theta$. It **bites** at $b$ if $T(b)<b$. Its **gap** is the set where it
  bites.
- A **seed** is a bound that needs no hypothesis. The **wall** of a family of levers below a seed is the
  largest value that no lever of the family forbids.
- A lever is **centred** if it has no fixed point above $\tfrac12$.
- A **source** is an exact identity that writes a Möbius-signed Dirichlet series as a quotient containing
  $\zeta$ at a dilated argument, with a reflection that allows estimates. Its **frame** is the pair
  $(c,k)$. A reflection is **independent** if its functional equation does not contain the target.
- A family **acts on the abscissa** if passing to a member transforms $\Theta$ by a known map (dilation,
  tensor power, base change).
- A stage recursion is **neutral** if it reproduces the exponent it is given, **contracting** if its loss
  factor is below the trivial one.
- A lever is **selective** against a class of worlds if it fails on some world of the class.

## 4. Principles and mechanisms

1. **Measuring is not moving.** An exact ruler transfers every bound and creates none. With the seed,
   every transmitter holds at $\tfrac38$; no ruler lowers $\tfrac38$.
2. **A lever is a gap law.** For monotone $T$, the theorem $\Theta\le b\Rightarrow\Theta\le T(b)$ is the
   statement $\Theta\le T(\Theta)$: the abscissa avoids the set where the lever bites. Levers and forbidden
   sets of values of $\Theta$ are the same thing.
3. **A wall is a fixed point.** Below a seed $s$ the abscissa is at most the largest $b\le s$ with
   $b\le T(b)$ for every available $T$, and this value satisfies every lever: nothing further follows.
   A wall is crossed by another lever, not by better constants.
4. **Convexity.** Closing a family of levers under composition, minima and towers does not lower its wall.
   For affine levers the value of a mixed tower is the Cantor series $\sum_r c_r/(k_0\cdots k_r)$, a mean
   of the centres $c_r/(k_r-1)$.
5. **Centring.** An affine lever reaches the line iff $c\le(k-1)/2$. No Möbius-signed Gauss pairing does
   (FCT): each has centre $\ge\tfrac35$, with equality only for the frame $(3,6)$.
6. **Independence of the reflection.** At order two the reflection of a Möbius-signed sum contains the
   target and is circular. At order $\ge3$ the root numbers are Gauss sums with their own generating
   series; the reflection is independent and each factor has a price.
7. **Action.** A law over a family becomes a lever only if the family acts on the abscissa. A mean over a
   family that does not act is blind to its trivial member.
8. **Uniformity.** A stage statement is worth its constant. One constant for all stages is the theorem;
   each stage alone is a certificate.
9. **Loss exponents.** A recursion $\operatorname{loss}(2K)\le\lambda\operatorname{loss}(K)+C$ has loss
   exponent $\log_2\lambda$. For the margin of the window matrices the trivial factor is $\sqrt2$, and a
   loss $CK^\theta$ with $\theta<\tfrac12$ confines the zeros to $|{\operatorname{Re}\rho-\tfrac12}|\le\theta$
   (MAFT).
10. **Selectivity.** A lever that holds on a class of worlds realizing every abscissa is the identity. A
    lever that bites uses a property the worlds lack.

## 5. Pillar theorems

| Theorem | Lean | Status |
|---|---|---|
| Seed | `riemannZeta_zero_mem_quasiRH_strip`, `zetaZeroWidth_le_three_eighths` | MMD, SRT |
| One number in every language | `zetaZeroWidth_le_iff_zetaZeroAbscissa_le`, `zetaZeroWidth_le_iff_xiZeroHalfPlaneBound` | SRT |
| Exact rulers | `zetaZeroWidth_le_iff_pointwise`, `zetaZeroWidth_le_iff_unit_window` (MZF); `zetaZeroAbscissa_le_iff_forall_signal_le` (FCT); `zeta_orbitCorr_rate_iff_zetaZeroWidth_le` (AOG); `zetaZeroWidth_le_iff_twoEndOdd_rate` (MAFT) | proved |
| Receivers | `zetaZeroWidth_le_of_neutralWindow_marginRate` (MAFT) | proved; converse open (E1) |
| Transmitters | `newmanConstant_le_half_sq_zetaZeroWidth` (SRT); `exists_moebius_power_bound_of_abscissa_lt` (BVI) | proved |
| Affine tower contraction | `abscissa_le_max_fixedPoint_of_tower` | FCT |
| Wall of the Gauss class | `three_fifths_le_coupledBarrier`, `coupledBarrier_eq_three_fifths_iff`, `not_exists_moebiusGaussPairing_reaching_critical_line` | FCT |
| Bounded loss is the line | `riemannHypothesis_iff_initialWindow_margin_bddBelow` | MAFT |
| Excess of one overlap step | `windowExcess_le_couplingNorm` | GCW |

## 6. Tools

**Inherited.** The dictionary between $\Theta$, $w$ and half-plane bounds (SRT); the classification of
Möbius-signed Gauss pairings with their prices (FCT); the overlap law and the rate law of the window
matrices (MAFT); the Green calculus of one overlap step (GCW).

**To build.**
- The calculus of levers: gap laws, walls, closure under composition, sharpness by models.
- Tower values for towers with varying frames.
- Transmission of the seed through every transmitter.
- The loss function of a stage calculus and the passage from a doubling inequality to a loss exponent.
- A converse rate law for the margin on all packets.
- Worlds with prescribed abscissa as tests for levers.

## 7. Questions

| # | Question | First theorem |
|---|---|---|
| E1 | Which half rulers are exact? | the converse rate law of the margin for all packets; a two-sided law between the heat time and $w$, or a proof that none holds |
| E2 | Which rulers have a stage map with loss factor below the trivial one? | a doubling inequality for the margin with $\lambda<\sqrt2$; a slope law for long moments |
| E3 | Is there a centred lever with an independent reflection? | a source outside the Gauss class with $c/(k-1)<\tfrac35$, or its exclusion |
| E4 | Is every lever built from complete exponential sums of bounded rank non-centred? | abelian rigidity of Gauss monomials; convexity |
| E5 | What do the two levers of a function field, tensor powers and base change, become over $\mathbb Z$? | the price law as a statement about weights of rank-one tensor powers |
| E6 | Which families admit a seed? | the Grössencharacter rung |
| E7 | Which property of $\zeta$ does each lever use that an Euler model with zeros on $\operatorname{Re}s=\Theta$ lacks? | the list, lever by lever |

## 8. Open research topics

- Exactness of the margin: does $w\le\beta$ bound the second eigenvalue of every window matrix by
  $-C_\varepsilon K^{\beta+\varepsilon}$, uniformly in the block size?
- The doubling law of the window calculus, with no statement about zeros as an input.
- The closure of the abelian class: sources of rank $\ge2$ whose target contains $\zeta(ks-c)$.
- The acid test over $\mathbb F_q[T]$: the gap of the windows by stage maps, without Weil's theorem.
- The critical exponent of the complete Weil matrix between $\tfrac18$ and $\tfrac14$ as a stage problem
  with two proved ends.

## 9. Traps

| Trap | Truth |
|---|---|
| A new exact reading of $\Theta$ is progress | A ruler transfers bounds; it creates none |
| Better constants lower a wall | A wall is a fixed point; only another lever crosses it |
| Mixing frames beats the best frame | Composites and mixed towers stay above the best centre |
| A stage statement for every $n$ is the theorem | Without one constant it is a list of certificates |
| A mean over a family bounds its trivial member | Only if the family acts on the abscissa |
| An identity that returns the unknown at a smaller scale is a lever | If the returned term has the same exponent the recursion is neutral |
| A lever can be soft | A lever that holds on worlds of every abscissa is the identity |
| A bound at $\tfrac38+\varepsilon$ from a ruler is a second producer | It is the seed read by the ruler |

## 10. Context

EDCS sits above the routes. It does not replace one: it compares what their maps can do.

| Neighbour | Interface |
|---|---|
| MetaplecticMobiusDescent | the seed; the only lever-like mechanism with an estimate attached |
| FamilyContinuationTheory | frames, prices, the tower contraction, the wall of the Gauss class |
| SquareRootThreshold | the zero width and its readings |
| MixingArithmeticOfTheFloorTrees, GreenCalculusOfThePrimeFreeWindow | the window matrices as a stage calculus: margin, overlap step, rate law |
| MultiscaleMollifiedZetaField, BezoutValuationIncidence | rulers on the Möbius side |
| ArithmeticCastelnuovoSeveri | windows and the function-field calibration |

Fields with neighbouring names have other objects: conversion of laws into points, defect transport and
the gluing of windows study defects, exceptions and windows. EDCS studies the maps on exponents.

## 11. Success criteria and criteria for a contribution

A contribution does one of the following.
1. It proves a ruler two-sided.
2. It lowers a fixed point.
3. It gives a ruler a stage map with an explicit loss factor.
4. It proves that every lever of a class has fixed point $\ge b$.
5. It supplies a seed for a family.

A result that adds one more reading of $\Theta$, certifies one more stage, or improves a constant at a
fixed exponent is outside the programme. A statement with the Riemann hypothesis as its antecedent is
calibration only.

The programme succeeds if it produces a second lever, or a second seed, or a contracting stage map; or if
it proves, class by class, that none exists, with the exact property of $\zeta$ a lever would have to use.

## 12. Big picture

The corpus has one producer and many rulers. EDCS explains why the rulers agree and why they do not help:
they are conjugate readings of one number, and a bound enters them only through the seed. What remains is
a short list of maps. Affine levers of the Gauss class have their centres at $\tfrac35$ or above. The
window calculus has a trivial loss factor $\sqrt2$ and no proved saving. The function field has two levers
that act on the abscissa, and over $\mathbb Z$ their analogues pay a price at every factor. For each of
them the programme asks for the fixed point, the price and the property of $\zeta$ that is used.
