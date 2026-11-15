# Exponent Dynamics of the Critical Strip (EDCS)

Namespace `GaloisForLFunctions.ExponentDynamicsOfTheCriticalStrip`; umbrella
`ExponentDynamicsOfTheCriticalStrip.lean`.

Every theorem named here is proved in Lean with no hypothesis on the zeros. Theorems of other
programmes carry their programme: MMD (MetaplecticMobiusDescent), FCT (FamilyContinuationTheory), SRT
(SquareRootThreshold), MAFT (MixingArithmeticOfTheFloorTrees), GCW (GreenCalculusOfThePrimeFreeWindow),
AGZ (AbsoluteGeometryOfSpecZ), MZF (MultiscaleMollifiedZetaField), CDG (ConjugateDiagonalGeometry), IRW
(InfiniteRankWeilTheory), AKT (ArithmeticKunnethTheory), WZC (WorldsOfTheZeroConfiguration).

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
| Ruler | `IsRuler w D P` | a law $P(\beta)$ on exponents with $P(\beta)\Leftrightarrow w\le\beta$ for $\beta\in D$ |
| Half ruler | `Transmits`, `Receives` | one direction only: $w\le\beta\Rightarrow P(\beta)$, or $P(\beta)\Rightarrow w\le\beta$ |
| Lever | `IsLever θ T` | a map $T$ with $\theta\le b\Rightarrow\theta\le T(b)$ |
| Gap | `excluded T` | the set $\{b:T(b)<b\}$ of values a lever forbids |
| Allowed set, wall | `allowed`, `wall` | the values below a seed that every lever of a family allows; their supremum |
| Frame, affine lever | `pairingStep c k` (FCT), `frameLever` | $T(b)=(c+b)/k$: the correction of a source sits at the dilated argument $ks-c$ |
| Centre, price | `coupledBarrier`, `pairingC` (FCT) | the fixed point $c/(k-1)$; what one factor adds to $c$ |
| Tower, tower value | `IsTower`, `IsTowerSolution`, `towerValue` | abscissas with $\Theta_r\le\max(\sigma_0,T_r(\Theta_{r+1}))$; the Cantor series $\sum_j c_{r+j}/(k_r\cdots k_{r+j})$ |
| Rung, correction | `rungAbscissa`, `correctionAbscissa` | the abscissas of a Grössencharacter $L$-function and of the correction of the cubic probe |
| World | `IsEulerWorld`, `coshModel` (IRW), `IsEdit` (WZC) | a zero configuration or Euler model on which a lever can be tested |
| Logarithmic energy | `logEnergy`, `packetLogEnergy` | $E(f)=\int_0^1\lVert f(\cdot+t)-f\rVert^2\,dt/t$ |
| Stage | — | a finite parameter whose limit is the statement: ratio of a window, block size, mollifier length |
| Level law | `IsLevelLaw ρ a` | the neutral matrix of the window $(\rho(K),(3K+1)\rho(K)]$ plus $a(K)$ has at most one negative square |
| Margin law | `MarginLaw ρ β` | the level law $a(K)=CK^\beta$ |
| Doubling law | `DoublingLaw ρ λ` | a monotone level law with $a(2K)\le\lambda a(K)+c$: a stage map with loss factor $\lambda$ |
| Slope law | `SlopeLaw κ` | exponents $a(\theta)$ of the long moments $\int_1^T\lvert\zeta M_{T^\theta}\rvert^2$ with $a(2\theta)\le a(\theta)+\kappa\theta$ |

## 3. Language

- A **ruler** reads $w$ exactly. A **transmitter** passes every bound for $w$ to its quantity; a
  **receiver** passes every bound for its quantity to $w$.
- A **lever** moves bounds. It **bites** at $b$ if $T(b)<b$. Its **gap** is the set where it bites.
- A **seed** is a bound that needs no hypothesis. The **wall** of a family of levers below a seed is the
  largest value that no lever of the family forbids.
- A lever is **centred** if it has no fixed point above $\tfrac12$.
- A **source** is an exact identity that writes a Möbius-signed Dirichlet series as a quotient containing
  $\zeta$ at a dilated argument, with a reflection that allows estimates. Its **frame** is the pair
  $(c,k)$. A reflection is **independent** if its functional equation does not contain the target.
- A family **acts on the abscissa** if passing to a member transforms $\Theta$ by a known map (dilation,
  tensor power, base change).
- The **margin** of a window is the least level at which its neutral matrix has at most one negative
  square. A **block-size law** $\rho$ fixes the block size of the window of ratio $3K+1$; it is
  **polynomial** if $K^{10}\le\rho(K)\le K^A$.
- A stage map is **neutral** if it reproduces the exponent it is given, **contracting** if its loss
  factor is below the trivial one. The **loss exponent** of a factor $\lambda$ is $\log_2\lambda$.
- A lever is **selective** against a class of worlds if it fails on some world of the class.

## 4. Principles and mechanisms

1. **Measuring is not moving.** The readings of a ruler are exactly the bounds of $w$; a lever stated on
   one ruler is the same lever on every other. With the seed, every transmitter holds at $\tfrac38$; no
   ruler lowers $\tfrac38$.
2. **A lever is a gap law.** For monotone $T$, the theorem $\Theta\le b\Rightarrow\Theta\le T(b)$ is the
   statement $\Theta\le T(\Theta)$: the abscissa avoids the set where the lever bites.
3. **A wall is a fixed point.** Below a seed the abscissa is at most the wall, and the wall satisfies
   every lever: nothing further follows. Closing a family under composition and minimum does not move it.
   A wall is crossed by another lever, not by better constants.
4. **Convexity.** The value of a mixed tower of affine levers is a mean of the centres of its frames. It
   equals the best centre only if every frame has it.
5. **Centring.** An affine lever reaches the line iff $c\le(k-1)/2$. No Möbius-signed Gauss pairing does
   (FCT): each has centre $\ge\tfrac35$, with equality only for the frame $(3,6)$.
6. **A frame is exact.** The lever of a frame is a ruler between two abscissas: the correction of the
   cubic probe has abscissa $(3+\Theta_{\mathrm{rung}})/6$. It moves a bound for the rung to the
   correction and back without loss and produces a bound for neither. A tower needs a seed for its rungs.
7. **Independence of the reflection.** At order two the reflection of a Möbius-signed sum contains the
   target and is circular. At order $\ge3$ the root numbers are Gauss sums with their own generating
   series; the reflection is independent and each factor has a price.
8. **Action.** A law over a family becomes a lever only if the family acts on the abscissa. Over a finite
   field base change and tensor powers act (IRW, AKT). Over $\mathbb Z$ the first needs the outer modes to
   be well-founded (IRW) and the second pays a price at every factor (FCT).
9. **The normalisation decides exactness.** Against the mass, the floor of Weil's form at a fixed
   aperture sees the number of zeros off the line in a unit window, and is a ruler only with a cluster
   law (SRT). Against the logarithmic energy the floor is a ruler with no loss in the exponent. A step
   packet of block size $R$ has logarithmic energy at most $12\log(1+R+J)$ times its mass, so at
   polynomial block size the two normalisations differ by a power $K^\varepsilon$.
10. **Samples carry the form.** Weil's form is continuous in the logarithmic energy, and a Lipschitz
    packet differs from its step sample by $O(1/R)$ in the uniform norm. A plane of smooth packets on
    which the form is deeply negative is therefore a plane of the window matrix once $R\ge K^{10}$. No
    limit in the block size is taken.
11. **A stage map with a loss is a ruler.** A doubling law with factor $\lambda$ is a margin law of rate
    $\log_2\lambda$ and conversely; a slope law with loss $\kappa$ is the half-plane $w\le\kappa/2$ and
    conversely. The best factor is $2^w$ and the best loss is $2w$. A stage map does not move $\Theta$
    unless its loss is proved by a calculus that does not pass through the zeros.
12. **Uniformity.** A stage statement is worth its constant. One constant for all stages is the theorem;
    each stage alone is a certificate.
13. **Selectivity.** A lever that holds on a family of worlds bites at no abscissa the family realizes.
    A lever that bites uses a property the worlds lack.

## 5. Pillar theorems

**Calculus of levers.** Gap law: `isLever_iff_notMem_excluded`, `disjoint_excluded_range_of_isLever`.
Wall: `le_wall`, `isLever_wall`, `wall_generated`. Mixed towers: `IsTower.le_solution`,
`IsTowerSolution.le_of_centres_ge`, `IsTowerSolution.centres_eq_of_eq`, `isTowerSolution_towerValue`.
Gauss class: every tower that mixes Möbius-signed Gauss pairings has value $\ge\tfrac35$, with equality
iff every frame is $(3,6)$ (`three_fifths_le_towerValue_pairings`,
`towerValue_pairings_eq_three_fifths_iff`); the wall of the finite-field Gauss levers below any seed
$\ge\tfrac35$ is $\tfrac35$ (`wall_gaussLevers`, `wall_generated_gaussLevers`). Inherited:
`abscissa_le_max_fixedPoint_of_tower`, `three_fifths_le_coupledBarrier` (FCT).

**Rulers and the seed.** `IsRuler.setOf_eq`, `IsRuler.congr`, `IsRuler.lever_transport`. Rulers of the
width: `isRuler_zetaZeroAbscissa`, `isRuler_moebiusPoly_pointwise`, `isRuler_unit_window`,
`isRuler_moebiusPoly_zero_free`, `isRuler_signal`, `isRuler_twoEndOdd`. The seed on each:
`newmanConstant_le_nine_div_128`, `wdHeatThreshold_le_three_div_64`,
`exists_mertens_le_of_seven_eighths_lt`, `exists_norm_moebiusPoly_le_three_eighths`,
`exists_unit_window_le_three_eighths`, `exists_pure_moebius_moment_le_seed`,
`jasAbscissa_eq_zero_or_one_add_sSup_le`, `homogeneousReturnWindowTransfer_iff_riemannHypothesis`.

**The margin is exact (E1).**
- *Floor in the logarithmic energy.* $|W(u,u)|\le160\,L(a,w)\,(E(u)+\int|u|^2)$ on sources of aperture
  $a$, $L(a,w)=4(2a+2+2\pi)e^{2\pi}e^{w(2a+3)}$ (`abs_sourceQuadratic_le_logEnergy`); the floor is a
  ruler (`isRuler_logEnergyFloor`), and a floor polynomial in the aperture is the line
  (`riemannHypothesis_iff_logEnergyFloor_zero`).
- *All packets, all block sizes.* `neg_packetLogEnergy_le_packetForm`; the neutral matrix of every
  window $(R,(3K+1)R]$ plus $C(1+\log K)^2K^\theta(1+\log R)$ has at most one negative square for
  $\theta\ge w$ (`exists_neutralWindow_marginDepth`), and $CK^{\theta+\varepsilon}$ suffices on
  $R\le K^A$ (`exists_neutralWindow_marginRate_of_blockSize_le_pow`).
- *Continuity and samples.* `abs_sourceQuadratic_sub_le`, `abs_packetForm_sub_le`,
  `abs_neutralForm_stepSample_sub_le`.
- *The ruler.* A margin law of rate $\theta<\tfrac12$ along block sizes $\rho(K)\ge K^{10}$ gives
  $w\le\theta$ (`zetaZeroWidth_le_of_neutralWindow_marginRate_of_pow_le_blockSize`); at polynomial block
  size the margin law is a ruler (`isRuler_marginLaw`) and the infimum of its rates is $w$
  (`sInf_marginLaw_eq_zetaZeroWidth`).

**Stage maps (E2).** A monotone sequence with $a(2K)\le\lambda a(K)+c$ is $O(K^{\log_2\lambda})$
(`le_rpow_logb_of_doubling`). A doubling law with factor $\lambda$ gives $w\le\log_2\lambda$
(`zetaZeroWidth_le_logb_of_doublingLaw`); every factor above $2^{3/8}$ occurs
(`doublingLaw_of_three_eighths_lt`); the best factor is $2^w$
(`sInf_doublingLaw_eq_two_rpow_zetaZeroWidth`). A slope law of the long moments with loss $\kappa$ gives
$w\le\kappa/2$ (`zetaZeroWidth_le_of_slopeLaw`); the loss $\tfrac34$ occurs (`slopeLaw_three_quarters`);
the least loss is $2w$ (`isLeast_slopeLaw`).

**Frames (E6).** `correctionAbscissa_eq`: $\Theta_{\mathrm{corr}}=(3+\Theta_{\mathrm{rung}})/6$ for every
finite set of primes of the probe; `correctionAbscissa_le_iff`;
`correctionAbscissa_le_thirtyOne_fortyEighths_iff`: a half-plane $\operatorname{Re}w>\tfrac78$ for the
rung is the half-plane $\operatorname{Re}s>\tfrac{31}{48}$ for the correction.

**Worlds (E7).** Integer-norm Euler products without a functional equation realize every abscissa in
$(\tfrac12,\tfrac23)$ (`exists_eulerWorld_zeroAbscissa_eq`, `le_apply_of_isLever_eulerWorlds`); the cosh
models, with a functional equation and no Dirichlet series, realize every abscissa $\ge\tfrac12$
(`exists_coshModel_zeroSupRe_eq`, `le_apply_of_isLever_coshModels`); an edit of the primes with a power
saving in its count has its zeros on $\operatorname{Re}s=\sigma$ for any $\tfrac78<\sigma<\tfrac{14}{15}$
(`exists_isEdit_zeros_on_line_right_of_seed`). A frame with centre below $\tfrac23$ is a lever in
neither of the first two families (`exists_world_not_isLever_frame`).

## 6. Tools

**Inherited.** The dictionary between $\Theta$, $w$ and half-plane bounds (SRT); the classification of
Möbius-signed Gauss pairings with their prices (FCT); the neutral matrices of the windows and the rate
law of the two ends (AGZ, MAFT); the Green calculus of one overlap step (GCW); the slope rigidity of the
long moments (CDG).

**Built here.**
- The calculus of levers: gap laws, walls, closure, towers with varying frames, sharpness by worlds.
- Rulers as objects: transport of levers, transmission of the seed.
- Sampling of transforms on logarithmically dense points (`sum_weight_mul_log_mul_norm_sq_testTransform_le`)
  and the logarithmic energy as the form domain of Weil's form.
- Step samples of Lipschitz packets with an explicit error (`sampleError`).
- The stage calculus: level laws, the passage from a doubling inequality to a loss exponent and back.

## 7. Questions

| # | Question | State |
|---|---|---|
| E1 | Which half rulers are exact? | The margin: exact against the logarithmic energy, and against the mass at polynomial block size. Against the mass at every block size it is the width together with a cluster law. Open: a two-sided law between the heat time and $w$ |
| E2 | Which rulers have a stage map with loss factor below the trivial one? | The margin and the long moments: best factor $2^w$, best slope loss $2w$; the factors above $2^{3/8}$ and the loss $\tfrac34$ hold. Open: any factor below $\sqrt2$ proved by the gluing calculus |
| E3 | Is there a centred lever with an independent reflection? | Open |
| E4 | Is every lever built from complete exponential sums of bounded rank non-centred? | Convexity: proved. Open: abelian rigidity of Gauss monomials (the factorisation of Gauss sums is not in the corpus); sources of rank $\ge2$ |
| E5 | What do the two levers of a function field become over $\mathbb Z$? | Over a finite field both are theorems (IRW `CurveDatum.unitary_of_thick_trace_bound`; AKT `fixed_base_tensor_bound_iff`). Over $\mathbb Z$: base change needs well-founded outer modes (IRW `mergedWeight_eq_zero_of_thick_bound`); tensor powers pay the price law (FCT). Open: a lever from either |
| E6 | Which families admit a seed? | $\zeta$, Dirichlet characters of every modulus, Hecke characters of finite order of $\mathbb Q(\omega)$ (MMD). The frame $(3,6)$ is exact, so the tower needs a seed for Grössencharacters. Open: that seed |
| E7 | Which property of $\zeta$ does each lever use that an Euler model with zeros on $\operatorname{Re}s=\Theta$ lacks? | A frame with centre below $\tfrac23$ uses the Dirichlet series and the functional equation together; the seed uses a property of the rational primes that an edit lacks. Open: a world with both an Euler product and a functional equation |

## 8. Open research topics

- **A contracting stage map.** A doubling law for the margin with a factor below $\sqrt2$, or a slope law
  with loss below $1$, proved from the gluing calculus (Green matrices of the middle, overlap steps) with
  no statement about zeros as an input. A factor below $2^{3/8}$ is a half-plane beyond the seed.
- **The cluster law.** Is the number of zeros off the line in a unit window bounded? It is the difference
  between the two normalisations of the margin.
- **A seed for the rungs.** A zero-free half-plane for $L(s,\psi^k)$, $\psi$ a Grössencharacter of
  $\mathbb Q(\omega)$; with $\tfrac78$ the wall of the frame $(3,6)$ is $\tfrac{31}{48}$.
- **The closure of the abelian class.** Sources outside the Gauss class; sources of rank $\ge2$ whose
  target contains $\zeta(ks-c)$.
- **The heat time.** $\Lambda\le w^2/2$ and one zero at depth $\delta$ and height $\gamma$ gives
  $\Lambda\ge\delta^2/(200\log\gamma)$ (SRT, RHTower). Which function of the zeros is $\Lambda$?
- **The acid test over $\mathbb F_q[T]$.** The gap of the windows by stage maps, without Weil's theorem.

## 9. Traps

| Trap | Truth |
|---|---|
| A new exact reading of $\Theta$ is progress | A ruler transfers bounds; it creates none |
| Better constants lower a wall | A wall is a fixed point; only another lever crosses it |
| Mixing frames beats the best frame | Composites and mixed towers stay above the best centre |
| A stage statement for every $n$ is the theorem | Without one constant it is a list of certificates |
| A doubling law at $2^{3/8+\varepsilon}$ is a second producer | It is the seed read by the margin; a producer proves the loss without the zeros |
| The margin against the mass is exact at every block size | A packet of block size $R$ resolves heights up to $R$, where a unit window may carry $C\log R$ zeros off the line |
| Squaring the ratio contracts | $K\mapsto K^2$ squares the loss; the exponent is unchanged |
| A mean over a family bounds its trivial member | Only if the family acts on the abscissa |
| An identity that returns the unknown at a smaller scale is a lever | If the returned term has the same exponent the recursion is neutral |
| A frame lowers the abscissa of its rung | It is exact in both directions; the bound has to come from a seed |
| A lever can be soft | A lever that holds on worlds of every abscissa is the identity |

## 10. Context

EDCS sits above the routes. It does not replace one: it compares what their maps can do.

| Neighbour | Interface |
|---|---|
| MetaplecticMobiusDescent | the seed; the one mechanism with an estimate attached |
| FamilyContinuationTheory | frames, prices, the tower contraction, the wall of the Gauss class, the probe |
| SquareRootThreshold | the zero width, its readings, the cluster law |
| AbsoluteGeometryOfSpecZ, MixingArithmeticOfTheFloorTrees | the neutral matrices of the windows, the states of the two ends, the rate law |
| GreenCalculusOfThePrimeFreeWindow | one overlap step; the additive loss law below the binding energy |
| MultiscaleMollifiedZetaField, ConjugateDiagonalGeometry | rulers on the Möbius side; the slope of the long moments |
| InfiniteRankWeilTheory, ArithmeticKunnethTheory | base change and tensor powers over a finite field |
| WorldsOfTheZeroConfiguration, ArithmeticPositiveDuality | the worlds |

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
they are conjugate readings of one number, and a bound enters them only through the seed. The same holds
one level up. The stage maps of the window calculus and of the long moments are rulers too: their best
loss factors are $2^w$ and $2w$, so a stage map is worth exactly the half-plane its loss encodes. The
frames are exact as well: a frame transports a bound between two abscissas and leaves both where the
seeds put them.

What remains is a short list of places where a bound could enter. A loss factor proved by gluing instead
of by zeros. A seed for the rungs of the cubic tower. A source outside the Gauss class with centre below
$\tfrac35$. For each the programme states the number that has to be beaten and the property of $\zeta$
that has to be used.
