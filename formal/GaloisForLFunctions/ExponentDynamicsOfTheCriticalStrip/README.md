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
   be well-founded (IRW); the second reaches $\zeta$ only through torsion, and a factor of order $m$ carries
   only $p^{k/m}$ of the weight $k/2$ of its $k$-th power: its price is the Stickelberger defect $(\tfrac12-\tfrac1m)k$.
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
14. **The sign has a price.** The Möbius parity of a Gauss monomial is the half-integrality of its
    Stickelberger defect (weight minus $p$-content), and the defects of its Galois conjugates average to
    zero. A Möbius-signed abelian monomial is pure at no place above $p$ and pays at least $\tfrac12$ at some
    place.
15. **Exponent zero is the line.** For the margin of the windows, bounded loss, a doubling factor one
    with any additive loss, and the margin law at every positive rate are all the Riemann hypothesis; the
    least levels are bounded or grow like a power.

## 5. Pillar theorems

**Calculus of levers.** Gap law: `isLever_iff_notMem_excluded`, `disjoint_excluded_range_of_isLever`.
Wall: `le_wall`, `isLever_wall`, `wall_generated`. Mixed towers: `IsTower.le_solution`,
`IsTowerSolution.le_of_centres_ge`, `IsTowerSolution.centres_eq_of_eq`, `isTowerSolution_towerValue`.
Gauss class: every tower that mixes Möbius-signed Gauss pairings has value $\ge\tfrac35$, with equality
iff every frame is $(3,6)$ (`three_fifths_le_towerValue_pairings`,
`towerValue_pairings_eq_three_fifths_iff`); the wall of the finite-field Gauss levers below any seed
$\ge\tfrac35$ is $\tfrac35$ (`wall_gaussLevers`, `wall_generated_gaussLevers`). Towers on the line of the sign
$c=k/2$ have values in $(\tfrac12,K/(2(K-1))]$ for periods $\ge K$: their wall is $\tfrac12$, not attained
(`towerValue_signLine_mem`, `exists_towerValue_signLine_lt`). Inherited:
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
the least loss is $2w$ (`isLeast_slopeLaw`). Loss exponent zero is bounded loss: RH iff a constant level
works, iff a doubling law with factor one holds, iff the margin law holds at every positive rate
(`riemannHypothesis_iff_exists_const_isLevelLaw`, `riemannHypothesis_iff_doublingLaw_one`,
`riemannHypothesis_iff_forall_marginLaw_pos`); the least levels are bounded or not $O(K^\beta)$ for some
$\beta>0$ (`exists_const_isLevelLaw_or_exists_not_marginLaw`).

**Frames (E6).** `correctionAbscissa_eq`: $\Theta_{\mathrm{corr}}=(3+\Theta_{\mathrm{rung}})/6$ for every
finite set of primes of the probe; `correctionAbscissa_le_iff`;
`correctionAbscissa_le_thirtyOne_fortyEighths_iff`: a half-plane $\operatorname{Re}w>\tfrac78$ for the
rung is the half-plane $\operatorname{Re}s>\tfrac{31}{48}$ for the correction. Seeds of finite order:
`heckeXi_cubicTwoHecke_ne_zero` (the Artin character of $\mathbb Q(\sqrt[3]2)$),
`heckeXi_ne_zero_of_seven_eighths_lt_re` (every nontrivial ray class $\Xi_\psi$ of $\mathbb Q(\omega)$),
`heckeHalfPlane_seven_eighths` (the whole Hecke family of $\mathbb Q(\omega)$, trivial characters included),
`heckeHalfPlane_rat_seven_eighths` (the Hecke family of $\mathbb Q$). The rungs: their coefficients are the
powers $\overline{\tilde g_{\mathfrak p}}^{\,18k}$ of the normalized cubic Gauss sums
(`grossenPrimeTerm_eq_conj_normalizedCubicGauss`) and are not algebraic integers at split primes, so no
rung is a quotient of products of finite-order Hecke $L$-functions (`not_grossenLFunction_mul_prod_eq`).

**Worlds (E7).** Integer-norm Euler products without a functional equation realize every abscissa in
$(\tfrac12,\tfrac23)$ (`exists_eulerWorld_zeroAbscissa_eq`, `le_apply_of_isLever_eulerWorlds`); the cosh
models, with a functional equation and no Dirichlet series, realize every abscissa $\ge\tfrac12$
(`exists_coshModel_zeroSupRe_eq`, `le_apply_of_isLever_coshModels`); an edit of the primes with a power
saving in its count has its zeros on $\operatorname{Re}s=\sigma$ for any $\tfrac78<\sigma<\tfrac{14}{15}$
(`exists_isEdit_zeros_on_line_right_of_seed`). A frame with centre below $\tfrac23$ is a lever in
neither of the first two families (`exists_world_not_isLever_frame`). The shifted pairs
$\zeta(s-a)\zeta(s+a)$, $0\le a<\tfrac12$, have a Dirichlet series with nonnegative coefficients, an Euler
product and a functional equation, and realize every abscissa in $[\Theta,\Theta+\tfrac12)\supseteq[\tfrac78,1)$
(`zeroSupRe_shiftedZetaPair`, `le_apply_of_isLever_shiftedPairs`). A map that bites at $b$ fails for the pair
$a=b-\Theta$, whose coefficients are $\le d(n)n^{a}$ and admit no bound $Cn^{\varepsilon}$ with $\varepsilon<a$
(`exists_shiftedPair_not_isLever`): a lever that bites at distance $\delta$ above the zeros uses the size of
the coefficients of $\zeta$ to the precision $n^\delta$. A frame with centre below $1$ fails for some pair
(`exists_shiftedPair_not_isLever_frame`).

**Tensor powers over $\mathbb Z$ (E5).** In an algebraic closure of $\mathbb Q_p$, with the Teichmüller
character $\omega$: $\|g(\omega^n)\|^{p-1}=p^{-(p-1-n)}$ (`norm_gaussSum_teichCharK_pow_pow`, Stickelberger's
congruence for the prime field), and every character is a power of $\omega$ (`exists_eq_teichCharK_pow`).
A character of order $m$ has $\|g(\chi)\|^m=p^{-v}$ with $1\le v<m$ coprime to $m$
(`exists_norm_gaussSum_pow_orderOf`); the extremal character $\chi_m=\omega^{-(p-1)/m}$ has $v=1$
(`norm_gaussSum_extremalChar_pow`), and in $g(\chi_m)^m=\chi_m(-1)\,p\prod J$ the Jacobi product is a unit
(`norm_prod_jacobiSum_extremalChar`). So $g(\chi)^k$ reaches $\zeta$ only through $p^{k/m}$, and its price
$(\tfrac12-\tfrac1m)k$ is the weight $k/2$ minus that content: the price of FCT's pairings is a Stickelberger
defect (`price_eq_weight_add_logb`, `pairingC_eq_weight_add_logb`).

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
- Stickelberger's valuation of the Gauss sums of a prime field: the Teichmüller character by Hensel's
  lemma, the uniformizer $\zeta-1$ of norm $p^{-1/(p-1)}$, and the congruence $a!\,c_a\equiv-1$.

## 7. Questions

| # | Question | State |
|---|---|---|
| E1 | Which half rulers are exact? | The margin: exact against the logarithmic energy, and against the mass at polynomial block size. Against the mass at every block size it is the width together with a cluster law. The heat time is not: dense models of width $\delta$ and zero spacing $2\pi/L$ have $L\Lambda_L\to\delta$ (`tendsto_mul_cosDefectHeatTime`), so no bound $\Lambda\ge\Phi(w)$ holds on worlds (`exists_cosDefect_width_heatTime_lt`). Open: the law for $\zeta$, which has to use the density of its zeros |
| E2 | Which rulers have a stage map with loss factor below the trivial one? | Answered for the gluing calculus. The finite-matrix window calculus proves `DoublingLaw ρ (√2)` for every `ρ` (`doublingLaw_sqrt_two`), and `ReweightedDoublingLaw ω ρ (√2)` for every bounded contact weight (`reweightedDoublingLaw_sqrt_two`). On gluing-indistinguishable sub-Euler models (`0 ≤ ω ≤ 1`, `ω(p^r) = ω(p)`, identical to `ζ` up to `Q₀` and on every `primeFreeMiddle D`), no factor `< √2` holds (`not_reweightedDoublingLaw_of_lt_sqrt_two_subEulerGluingWeight`, `sInf_reweightedDoublingLaw_subEulerGluingWeight_eq_sqrt_two`). On `neutralWindow`, the un-updated glued matrix `neutralWindow (3K + 1) R (6KR)` jumps to `hermNegIndex ≥ 2` up to `(1/2000)√K − 40000` (`eventually_two_le_hermNegIndex_neutralWindow_halfCutoff`), so any factor `< √2` (and `< 2^{3/8}` iff `w < 3/8`, `exists_doublingLaw_lt_two_rpow_three_eighths_iff`) requires `Ω(√K)` cancellation in the fresh prime octave `[3K + 2, 6K + 1]` (`topOctave_jump_of_doublingLaw_lt_sqrt_two`) |
| E3 | Is there a centred lever with an independent reflection? | Rank one: no. A Möbius-signed abelian monomial has Stickelberger price $\ge k/2$ whatever its completion, so no abelian frame is centred (`half_lt_stickelbergerPrice_div`); the Gauss pairings are priced above it (`half_mul_period_le_pairingC`) and end at $\tfrac35$ (FCT). Between: the arithmetic allows centres $k/(2(k-1))$, below $\tfrac35$ from $k=7$ on, so a source below $\tfrac35$ needs a joint metaplectic completion of a short Möbius monomial. Order two (Liouville, Eisenstein): centred, reflection circular. Rank two: in FCT's exponent budget the specializations of the $A_2$ multiple Dirichlet series have boundary exponents above $\tfrac78$ (`rank_two_rejection_boundary_exponents`). For a cubic pair the joint factor is a Grössencharacter: $g(\chi_{\mathfrak p})^3=N\mathfrak p\,J(\chi_{\mathfrak p},\chi_{\mathfrak p})$, $J=-\pi_{\mathfrak p}$ (MMD), and its powers are the rungs (`idealPsiSix_eq_conj_normalizedCubicGauss_pow`), so a joint completion of a cubic Möbius pair runs into the rung seed of E6. Open: sources of rank $\ge2$ with $\zeta$ undilated |
| E4 | Is every lever built from complete exponential sums of bounded rank non-centred? | Convexity: proved. Stickelberger's valuation of prime-field Gauss sums: proved; the Möbius parity law of a Gauss monomial is the half-integrality of its Stickelberger defect, so a Möbius-signed monomial is pure at no place above $p$ (`isMoebiusSignedTuple_iff_defect`, `half_le_abs_stickelbergerDefect`); the defects of its Galois conjugates average to zero, so the sign costs at least $\tfrac12$ at some place (`exists_conjList_half_le_stickelbergerDefect`). Rank one: priced by its largest conjugate defect, a Möbius-signed monomial has $c\ge k/2>(k-1)/2$ at every period, so no such frame is centred (`half_lt_stickelbergerPrice_div`); the prices of the Gauss pairings dominate it, $c\ge k/2$ for every pairing over $\mathbb F_p$ (`stickelbergerPrice_le_pairingC`, `half_mul_period_le_pairingC`). The bound is attained by every Möbius-signed monomial of length two or three (`stickelbergerPrice_eq_half_mul`): arithmetic prices the sign on the line $c=k/2$, with centres $k/(2(k-1))\to\tfrac12$, and the Gauss wall $\tfrac35$ is its point $k=6$, where the completion bound $c\ge\tfrac23k-1$ (FCT) takes over. Open: the classification of pure Gauss monomials (relations generated by reflection and Hasse–Davenport), the analytic step from a monomial to a source, sources of rank $\ge2$ |
| E5 | What do the two levers of a function field become over $\mathbb Z$? | Answered. Over a finite field both are theorems (IRW `CurveDatum.unitary_of_thick_trace_bound`; AKT `fixed_base_tensor_bound_iff`). Over $\mathbb Z$ base change becomes the thick-set lag lever: RH iff the zeros approach the line and one tower has a bounded lag on a thick set of levels (IRW `riemannHypothesis_iff_zerosApproachLine_and_thick_lag_bounded`); well-foundedness of the outer modes cannot be dropped (IRW `exists_tower_bounded_without_wellFounded`). Tensor powers become the powers of Gauss sums, which reach $\zeta$ only through torsion at the rate $1/m$, so a factor of order $m$ pays $(\tfrac12-\tfrac1m)k$ (`price_eq_weight_add_logb`). The Grössencharacter rungs of the cubic tower are this lever at the cubic Gauss sums: their coefficients are $\overline{\tilde g_{\mathfrak p}}^{\,18k}$ (`grossenPrimeTerm_eq_conj_normalizedCubicGauss`). Over $\mathbb F_q[T]$ the same torsion costs nothing: a count at the even degrees and base change give the line for cubic characters (`riemannHypothesis_cubicCharacter`). The remaining input of the first lever is the approach of the zeros to the line; of the second, a completion below the price |
| E6 | Which families admit a seed? | $\zeta$, Dirichlet characters of every modulus, Hecke characters of finite order of $\mathbb Q(\omega)$ (MMD), and a non-abelian Artin character: the completed $L$-function of the degree-two character of $\mathbb Q(\sqrt[3]{2},\omega)$ has no zero on $\operatorname{Re}s>\tfrac78$ (`heckeXi_cubicTwoHecke_ne_zero`), through a bridge from the theta-lattice continuation of MMD to the completed ray class $L$-functions. The bridge holds for every ray class character of $\mathbb Q(\omega)$: every nontrivial $\Xi_\psi$ is zero-free on $\operatorname{Re}s>\tfrac78$, and the Hecke family of $\mathbb Q(\omega)$ has the half-plane $\tfrac78$ (`heckeHalfPlane_seven_eighths`). A second field: the ray class characters of $\mathbb Q$ are Dirichlet characters on the positive integers, so the Hecke family of $\mathbb Q$ has the half-plane $\tfrac78$ (`heckeHalfPlane_rat_seven_eighths`), the base change of the seed of $\mathbb Q(\omega)$. The frame $(3,6)$ is exact, so the cubic tower needs a seed for Grössencharacters. That seed is not a transport: the coefficient of a rung $L(w,\psi_6^k\psi)$ at a split prime is not an algebraic integer (`exists_not_isIntegral_rungCoeff`), so no rung is a quotient of products of finite-order Hecke $L$-functions of $\mathbb Q(\omega)$ (`not_grossenLFunction_mul_prod_eq`). The rungs are tensor powers of a rank-one sum: $\psi_6(\mathfrak p)=\overline{\tilde g_{\mathfrak p}}^{\,18}$, $\tilde g_{\mathfrak p}$ the normalized cubic Gauss sum (`idealPsiSix_eq_conj_normalizedCubicGauss_pow`). Open: a second seed, for the rungs, which has to see the infinity type (the probe of MMD with an infinity type) |
| E7 | Which property of $\zeta$ does each lever use that an Euler model with zeros on $\operatorname{Re}s=\Theta$ lacks? | Answered lever by lever. A frame with centre below $\tfrac23$ uses the Dirichlet series and the functional equation together (Euler worlds, cosh models); a frame with centre below $1$, and any lever that bites at distance $\delta$ above the zeros, uses the Ramanujan bound to the precision $n^\delta$ (shifted pairs, which have Euler product and functional equation); the seed uses a property of the rational primes beyond a count $Ax+O(x^{14/15})$ (edits) and the Ramanujan bound to the precision $n^{3/8}$ (shifted pairs with $a&gt;\tfrac38$). Every lever that bites above the zeros therefore uses Euler product, functional equation and Ramanujan bound together, the hypotheses under which the line is a theorem over a finite field |

## 8. Open research topics

- **Top-octave prime cancellation (`< 2^{3/8}`).** Pure window gluing stops sharply at `√2` (`sInf_reweightedDoublingLaw_subEulerGluingWeight_eq_sqrt_two`), and the un-updated glued matrix `neutralWindow (3K + 1) R (6KR)` has `hermNegIndex ≥ 2` up to `(1/2000)√K − 40000`. Open: proving the `Ω(√K)` cancellation on the direct end-to-end top-octave prime sum `∑_{k=3K+2}^{6K+1} floorGraph k` on `(R, 2R] × ((3K+1)R, (6K+1)R]` required for `DoublingLaw ρ λ` with `λ < 2^{3/8}`.
- **The cluster law.** Is the number of zeros off the line in a unit window bounded? It is the difference
  between the two normalisations of the margin.
- **A seed for the rungs.** A zero-free half-plane for $L(s,\psi^k)$, $\psi$ a Grössencharacter of
  $\mathbb Q(\omega)$; with $\tfrac78$ the wall of the frame $(3,6)$ is $\tfrac{31}{48}$. It is a second seed: the rungs
  are not quotients of products of seeded $L$-functions, and their coefficients are the powers
  $\overline{\tilde g_{\mathfrak p}}^{\,18k}$ of the cubic Gauss sums.
- **The critical exponent of the complete Weil matrix.** The tilted-spline matrix is positive definite
  for overlap $1\le c\le 2K(\log N)^{1/8}$ (CACT `exists_critical_multiple_completeWeilMatrix_posDef`);
  eventual nonnegativity at overlap $2(\log N)^{\alpha}$, $\alpha>\tfrac14$, is equivalent to RH (RAPT
  `tiltedUnitSpline_overlap_window`). Open: the band
  $\tfrac18\le\alpha\le\tfrac14$ as a stage problem, where positivity does not decide RH.
- **The closure of the abelian class.** The arithmetic price of the sign is $k/2$ and is attained; the wall
  $\tfrac35$ comes from completing each Gauss factor by its own theta series. Open: a joint completion of a
  Möbius pair or triple (coefficients $g(\chi)g(\varphi)$ or $p\,J(\chi_1,\chi_2)$) with a dilated target at a
  period $k\ge7$; sources of rank $\ge2$ whose target contains $\zeta(ks-c)$.
- **The heat time of $\zeta$.** The local heat threshold is $\asymp\text{depth}^2/\text{local count}$ (RHTower
  `TheLocalHeatThreshold`); the dense models are its case of regular spacing, $\Lambda\sim w/L$. Open: an
  upper bound for $\Lambda$ by the local data of the zeros off the line, uniform in the height.
- **The acid test over $\mathbb F_q[T]$.** Passed for quadratic characters of split squarefree moduli of odd
  degree: Stepanov's counts at even degrees on both parity classes and the base-change lever give index zero
  of the trace kernel without Weil's theorem (RHTower `riemannHypothesis_splitHyperelliptic`, AKLT
  `stepanov_order_hyperelliptic`). Characters of order three: Stepanov's count with three levels
  (`cubic_stepanov_independence`, by the norm form and cubic descent) equidistributes $h(x)^N$ among the
  cube roots of unity and gives $|\#\{y^3=h(x)\}-s^2|\le 2(5D+4)s+4D$ over $\mathbb F_{s^2}$
  (`abs_card_cubicCurve_sub_le`), and with the base-change lever the Riemann hypothesis for the
  $L$-function of a cubic character on a split squarefree modulus of degree prime to three
  (`riemannHypothesis_cubicCharacter`), without Weil's theorem. Open: the gluing calculus of the windows
  as the producer.

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
| The seed of the rungs follows from the seeds of finite order | A rung is not a quotient of products of finite-order $L$-functions: its prime coefficients are not algebraic integers |
| A lever can be soft | A lever that holds on worlds of every abscissa is the identity |
| A stage recursion needs summable losses to reach the line | For the margin a factor one with a constant additive loss already is the line |
| The heat time is a ruler of the width | On dense models of width $w$ and spacing $2\pi/L$ it is $\sim w/L$; it reads depth and density together |
| Euler product and functional equation force the line | The shifted pairs have both and realize every abscissa in $[\Theta,1)$; the Ramanujan bound is what they lack |

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

The prices are arithmetic. The price of a torsion factor in the Gauss class is its Stickelberger defect, the
Möbius sign alone costs half a unit of weight at some place, and exactly half for a pair or a triple; the wall
$\tfrac35$ is where completing factor by factor costs more than the sign, and the line is reached by a stage recursion
as soon as its loss exponent is zero. The seed covers the finite-order Hecke families of $\mathbb Q(\omega)$ and of
$\mathbb Q$ and the Artin characters induced from them; the rungs of the cubic tower are powers of the cubic Gauss
sums and lie outside the multiplicative closure of that family, so a seed for them is a second seed. What remains
is a short list of places where a bound could enter. A loss factor proved by gluing instead
of by zeros. A seed for the rungs of the cubic tower. A source outside the Gauss class with centre below
$\tfrac35$. For each the programme states the number that has to be beaten and the property of $\zeta$
that has to be used.
