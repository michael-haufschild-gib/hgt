# Review 2410 — Opus: mechanisms past the walls, three focus questions, and a field for the tools

**Date** 2026-10-25. **Scope.** Read-only review. Sources: the five reports named in the brief
(frontier map, killed routes, route-unification ledger, hard obstacles, walls ledger) and the
eighteen programme READMEs. No other Markdown was read. Proven/unproven status was checked with
`scripts/formal_tools.py research` and confirmed against Lean source text; every declaration named
below was grep-confirmed to exist (§6). No builds, no compiles, no web. Research log:
`logs/opus-review-2410-research.md`.

---

## 0. Answers in brief

1. **New mechanism?** No mechanism in the corpus, and none I can construct, crosses a wall
   outright. The corpus has proved that the walls hold up under eleven separate kinds of attack
   (§1.3). Taken together, those no-gos leave only a small region open: a closing argument must be
   *signed, single-ζ, Beurling-selective through the additive structure of ℤ, live at the
   square-root scale, charge prime powers individually, break under single-prime deformation,
   carry a quantized invariant, and hold uniformly in the horizon.* Three mechanisms lie in that
   region, and as far as the search shows, none has been pursued:
   - **(A)** spectral rigidity of the *escape module* over the critical Wiener algebra;
   - **(B)** Riemann–Roch for the scaling surface, posed as a *vanishing theorem for a
     payment cohomology*;
   - **(C)** a *one-sided Stepanov-type count* at the band.

   For each one, §2 gives the first theorem to try and a test that would retire it.
2. **The three questions** (one per wall):
   - **Q-I (Wall 1):** a Beurling-selective, single-ζ estimate that beats the trivial exponent
     at the square-root band. This is equivalent to a fixed zero-free strip. At the tool level it
     asks which Bézout-selective identity controls the off-diagonal Vaughan entries.
   - **Q-II (Wall 14):** Riemann–Roch for the scaling surface, i.e. a source-defined effective
     cone with the RR axiom whose Bézout positivity is a linear degree statement.
   - **Q-III (Wall 3):** a classification of escape states, i.e. an index formula below the
     width.
3. **The field:** I call it ***Biarithmetic Geometry***, the geometry of the ring ℤ at finite
   horizon. The three walls trace back to one structural absence. Over $\mathbb F_q$ the horizon
   equals the period and Frobenius is a ring endomorphism, so square-root cancellation becomes an
   identity (Gauss sums, Lefschetz). Over ℤ the multiplicative period of the horizon-$N$ divisor
   structure is $\operatorname{lcm}(1..N)=e^{\psi(N)}$. Complete-period quadratic data are exactly
   sign-blind. Additive structure is destroyed by every escape limit except at the square-root
   translation scale. Local payments always exist but do not glue. The field's objects are
   *horizon-truncated ring actions* (the affine semigroup $\mathbb N\rtimes\mathbb N^\times$ cut
   at $N$), a *payment sheaf* and its cohomology, *escape modules* over $\mathcal W_{1/2}$, and a
   built-in *selectivity battery*. §4 gives its questions, principles, criteria and research
   topics.

---

## 1. The frontier, as I read it

### 1.1 One receiver, one number

Every route reads the zero width $\Delta=\sup_\rho|\Re\rho-\tfrac12|$. The unification ledger
proves that the $\Delta$-readings form a single isomorphism class of receivers, so further
reformulation at receiver level is finished. Exact, faithful readings I used:

| reading | statement | Lean |
|---|---|---|
| Damping of the pronic receiver | infimum of the derived admission set $=\Theta-\tfrac12$ | `receiverDampingRate_eq_zetaZeroAbscissa_sub_half` |
| One packet, one side | RH ⟺ $\sum_{n\le e^{\tau+4}}\Lambda(n)\sqrt n\,B(\log n-\tau)\le\int2\cosh(x/2)e^xB(x-\tau)+Ke^\tau$, $\tau>4$ | `riemannHypothesis_iff_spline_prime_sum_le_of_gt_four` |
| Band of one packet | RH ⟺ linear band of a universal probe | `riemannHypothesis_iff_packet_band_of_universal` |
| Hodge defect | $n\le\#\{\Re\rho>\tfrac12\}$ ⟺ positive index $\ge1+n$ on $n$ tests; one spectrally generic $g$ and any dense shift set suffice | `zeta_hodgeDefect_iff`, `zeta_cyclic_hodgeDefect_iff` |
| Index exit | RH ⟺ $\#\text{rightZeros}<2$; finite ⇒ even | `riemannHypothesis_iff_encard_rightZeros_lt_two`, `even_ncard_rightZeros` |
| Obstruction hull | unpaid ⟺ some Bohr point kills every repairing kernel | `not_receiverBounded_iff_exists_obstruction` |
| Bézout on the scaling surface | Bézout(positive cone) ⟺ cofinal bounded damped divisor energy (the BVI receiver) | `positiveCone_bezout_iff_cofinal_budget` |
| Criticality | RH ⟺ odd jump form nonnegative with no Hardy weight; $\Lambda(n)n^{-1/2}$ least admissible prime rate | `riemannHypothesis_iff_nonneg_and_no_hardyWeight`, `riemannHypothesis_iff_isLeast_primeRate` |
| Self-improvement | any subexponential odd defect floor ⇒ RH | `rightZeros_zeta_eq_empty_iff_subexponential_scalingSubsurface_odd_defect_floor` |

### 1.2 What is unconditionally in hand at the edge

- **Small apertures:** strict-coupled-cone RR on the odd sector through $r\le181/500$
  (`strictCoupledArithmeticCone_odd_riemannRoch_of_le_threeHundredSixtyTwoThousandths`).
  Ample, Bézout and RR on the section cone through $r\le3/10$
  (`scalingSubsurface_all_sectionEffectivityCone_castelnuovoSeveri_of_le`).
- **Local payment:** every prime-power atom is paid by its own reflection-strip surplus
  (`two_mul_primePowerShift_le_stripSurplus`). Failure can only come from interaction between
  atoms.
- **VK band:** the receiver is bounded on $\tfrac12-\kappa\sigma(T)/(480\log T)\le\varepsilon\le\tfrac12$
  (`exists_receiver_le_on_vinogradovKorobovBand`). The parity pair separates on that band
  (`parityPair_separated_on_vinogradovKorobovBand`). This is the corpus's **first receiver
  statement that is selective against Beurling systems**, and its extra width over
  Diamond–Montgomery–Vorhauer is paid by Vinogradov's mean value theorem
  (`shiftedPair_and_vkBand_selectivity`).
- **Large values:** Guth–Maynard Theorem 1.1 is formalized unconditionally
  (`guthMaynardLargeValuesBound_holds`), giving
  $N(\sigma,T)\ll T^{(30/13+\varepsilon)(1-\sigma)}$
  (`exists_zeroHeightBox_ncard_le_thirty_thirteenths`). It is used only for density.
- **Escape structure:** the normalized cofactor Grams of the actual receiver have a common
  limit $K$ at every subcritical damping (`exists_cofactorGram_limit`). $K$ is PSD with
  $K(1,1)=1$ and $|K(j,k)|\le(jk)^{-1/2}$, and for every $p\in\mathbb N_+$,
  $K(p\cdot,p\cdot)\le\tfrac1pK$ as forms. On escape the residual is antipodal (ADR), and fixed
  successor translations become the identity (ADR, `FixedSuccessorsDisappearFromEscapingProfiles`).

### 1.3 The admissible region: what a closing mechanism must be

These are proven constraints, not taste. I collected them because together they sharply narrow
what can still work.

| | constraint | source |
|---|---|---|
| C1 | **Beurling-selective.** Multiplicative identities hold in Beurling systems with off-line zeros. | THIM Class I (`selectivity_class_I_beurling_universal_laws`); golden datum; BVI §1.2 |
| C2 | **Degenerate point.** Must work for ζ alone: one character, modulus one, no family average. | BiScale §7.1; killed meta "additive tools need a family" |
| C3 | **Signed.** Amplitude data decide payment only above $\tfrac12$; blindness is closed under post-processing. | THIM parity barrier; BVI pillar 12 (`periodCovariance_eq_iff_exists_scaledSelbergRow`) |
| C4 | **Square-root scale.** The barrier lives entirely in the band $\lvert\xi\rvert<\sqrt N$. Square-root node density is the critical density for seeing the pole. | BiScale §3.10, §3.4 (`exists_blindOn_poleMass_eq_small_of_density`) |
| C5 | **Node-critical.** Must charge prime powers individually; deleting node 4 falsifies positivity. | `not_zeroPoleBlindPositiveOn_diff_four` |
| C6 | **Deformation-sensitive.** Inequalities that survive deformation give nothing (Estermann single-prime deformation). | killed meta-no-go |
| C7 | **Quantized.** Continuous functionals miss quanta. | killed meta-no-go |
| C8 | **Horizon-uniform.** The constant may depend on the damping, never on $T$; limits do not commute. | BVI/THIM traps |
| C9 | **Escape keeps only multiplicative structure.** Fixed successors vanish after normalization; a moving translation of length $k$ vanishes unless $k^2\gtrsim E$. | ADR |
| C10 | **Non-circular.** Summation by parts returns coefficient 1, never $1-\delta$; rewriting an eigenvalue bound as an inequality proves nothing. | BVI §5, THIM §5 |
| C11 | **Interaction.** Local payments exist (AIP, AOT towers); everything left is in shared budgets. | AIP, AOT; Wall 3 |

**What this rules out.** C1 and C2 together exclude every multiplicative-only method and every
averaged additive method. The inputs in the corpus that satisfy both are Vinogradov's mean
value theorem, Guth–Maynard large values, Poisson summation over ℤ (which is too weak: the
functional equation alone is Beurling-compatible) and the Bézout identities
$\gcd(n,n+1)=1$, $pa-qb=1$ (identities, not estimates). None of them reaches C4. Wall 1 is
therefore precisely: *no known additive input at one ζ has square-root strength.* A
circumvention must either supply such an input or find a structure in which square-root
strength comes from an identity, as it does over $\mathbb F_q$.

---

## 2. Q1 — Mechanisms that lie in the admissible region

**Verdict.** I found no mechanism that crosses a wall today. Below are three that are, by the
search, neither already pursued nor killed. Each lists the corpus facts it rests on, the new step
it needs, the first theorem to attempt, and a test that would retire it. I also list ideas I
checked and rejected.

### 2.1 Mechanism A — spectral rigidity of the escape module (targets Wall 3 → Wall 1)

**Corpus facts.**
- `exists_cofactorGram_limit` gives the kernel $K$ with dilation contraction $1/p$.
- AOT's critical Wiener algebra $\mathcal W_{1/2}$ has spectrum equal to the Bohr polydisk.
- Its paid ideal $P(c)$ and obstruction hull satisfy: unpaid ⟺ hull nonempty
  (`not_receiverBounded_iff_exists_obstruction`).
- The hull of $d^{-\varepsilon}$ is the single point $s=1-\varepsilon$
  (`mem_obstructionHull_smoothPower_iff`).
- On the computed families the hull is counted by the codimension of $P(c)$
  (`finrank_quotient_paidIdeal_oscillating`, `…_of_zeta_eq_zero`).
- Liouville and Möbius have the same paid ideal, hull and index
  (`liouville_paidIdeal_obstructionHull_and_index_eq_moebius`).

**New observation (elementary, unformalized).** Let $H_K$ be the GNS space of $K$, with $\delta_j$
the image of $j$ and $V_n\delta_j=\delta_{nj}$.

- The form inequality gives $\|V_n\|\le n^{-1/2}$ for every $n$. Also $V_mV_n=V_{mn}$ and
  $V_1=\mathrm{id}$.
- Hence $\pi(a)=\sum a_nV_n$ defines a **contractive unital representation of $\mathcal W_{1/2}$**
  with $\|\pi(a)\|\le\sum|a_n|n^{-1/2}$. The vector $\delta_1$ is cyclic.
- By commutativity, $\operatorname{Ann}(\delta_1)=\ker\pi$, a proper closed ideal, so its hull
  $h(\ker\pi)$ is a **nonempty** subset of the Bohr polydisk.

So the escape state is a Hilbert module of exactly the kind on which AOT's index theory acts.

**Two calibrations that sharpen the open core.**
1. The white-noise kernel $K_0(j,k)=\delta_{jk}/j$ satisfies every property in
   `exists_cofactorGram_limit` (PSD, $K(1,1)=1$, radius, dilation with equality). Its module is the
   Hardy space of Dirichlet series, where $\ker\pi=0$ and the hull is the whole polydisk. *So the
   listed properties cannot exclude anything.* An exclusion argument must use antipodality, the
   pole trace and the forcing split, and it must show that white noise violates them.
2. If the receiver energy grows like $T^{\alpha}$ along the subsequence (regular variation), pronic
   self-similarity of `rowDilate` suggests $K(pj,pj)=p^{-1-\alpha}K(j,j)$. Then
   $\|\sqrt p\,V_p\|\le p^{-\alpha/2}$: **the spectral radius of the dilation module reads the
   escape exponent.** An off-line zero $\rho$ seen at damping $\varepsilon$ gives
   $\alpha=2(\Re\rho-\tfrac12-\varepsilon)$, and the module sits on the polydisk of radii
   $p^{-\alpha/2}$, which is the "translated off-line hull". Exclusion is then equivalent to
   forcing $\alpha=0$, i.e. a *unitarity/isometry* law for the dilation action.

**Where C1 and C9 bite, and the new step.** Without more input this module is Beurling-universal:
Beurling systems also have dilations, and the golden datum escapes. C9 says additive information
survives only along translations of length $k$ with $k^2\gtrsim E$. With $E\asymp T^{\alpha}$ that
means $k\asymp T^{\alpha/2}$. The new step is to **build the limit together with translations at
that scale** and prove a ring-type covariance between them and $V_p$. The model is the relation
$s_nu=u^ns_n$ of the affine semigroup $\mathbb N\rtimes\mathbb N^\times$: dilating then translating
by $n$ equals translating by 1 then dilating. Beurling systems have no such relation, so this is
where selectivity would enter.

**First theorems.**
- (A1) Repairing kernels annihilate the escape state: $P(\mu_\varepsilon)\subseteq\ker\pi$,
  first for finitely supported kernels.
- (A2) Hence $h(\ker\pi)\subseteq\operatorname{obstructionHull}(\mu_\varepsilon)$.
- (A3) A regular-variation lemma: along an Abel subsequence of an escaping receiver,
  $K(p\cdot,p\cdot)=p^{-1-\alpha}K$.
- (A4) Existence of a $T^{\alpha/2}$-scale translation limit and its commutation law with $V_p$.

**Kill test.** Build the same module for the golden datum and for a Beurling system with an
off-line zero. If (A1)–(A4) hold there verbatim, the mechanism cannot exclude. If (A4) fails there
but holds for ℤ, it survives. *Relation to known mathematics:* Nikolski showed the
Nyman–Beurling criterion is a cyclicity problem in $H^2(\mathbb D^\infty)$, and the search found
no Nikolski-type cyclicity results in the corpus. Mechanism A adds information that cyclicity
formulations lack: antipodality and the escape exponent.

### 2.2 Mechanism B — Riemann–Roch as a vanishing theorem for a payment cohomology (targets Wall 14, with Wall 3)

**Corpus facts.**
- HI ⟺ some cone carries both RR and Bézout (`exists_bezout_effectivity_iff_hodgeIndex`,
  `hodgeIndex_bezout_tfae`).
- The positive graph cone is ample and Bézout given nonnegative point counts, but fails RR on
  every nonempty window (`graphCone_bezout`, `graphCone_not_riemannRoch`).
- The golden datum defeats section cones (`goldenDatum_not_bezout_sectionEffectivityCone`).
- Bézout on the positive cone is the BVI receiver (`positiveCone_bezout_iff_cofinal_budget`).
- The unification ledger: "ACS's Riemann–Roch is AIP's allocation".
- AOT's Nyquist–RR: the box Euler characteristic is
  $\text{polar DoF}-\text{prime-node count}=E(s)=e^s+s-1-\psi(e^s)=h^0_{\text{box}}-h^1_{\text{box}}$,
  with $h^1=0$ below $\log2$. These box quantities are real weighted charges, not ordinary
  cohomology dimensions. At aperture level,
  $\text{defect}+h^1\text{-correction}=\text{arch budget}$
  (`aperture_nyquist_riemannRoch_defect_identity`).
- Prime-blind sections of low spectral height vanish (`finrank_primeBlind_subspace_eq_zero`,
  $T^2\le69/2$), while trans-Nyquist supply has dimension $\ge(2-\eta)e^{2L}$
  (`zeta_weil_near_radical_sharp_count`).

**The reframing.** AIP shows every atom is payable locally and that failure is purely a gluing
failure (C11). That is the defining property of a first cohomology class. Define a *payment
sheaf* $\mathcal P$ on the aperture line or the scaling site:
- sections over a window $U$ are admissible local allocations of archimedean surplus to the atoms
  in $U$;
- restriction forgets atoms outside $U$.

AOT's frustration index is the nearest seed: a signed graph is balanced iff its sign cocycle is a
coboundary. Relating an actual gluing obstruction to RH remains open. The literal ordinary-dimension
identity for $E(s)$ is now refuted: at $s=\log(3/2)$ the box defect is strictly between zero and
one (`BiarithmeticGeometry.no_dimension_model_for_boxDefect`). Its proved replacement is an
arithmetic degree with a separate integral torsion datum. For $N\ge1$, put
$Q_N=\operatorname{lcm}(1,\ldots,N)/N$; then
$E(\log N)=(N-1)-\log Q_N$, with an exact continuous interpolation between integer horizons
(`boxDefect_eq_degree_sub_log_card`, `boxDefect_all_apertures`). A payment theory must preserve
this distinction between integer cohomological index and real weighted degree. The identity
does not itself construct the sheaf, its duality, or a vanishing theorem.

**Why this could matter.** It brings in the *Weil chain* whose missing link the corpus has
located:

$$
\text{duality}\;\Rightarrow\;\text{vanishing in negative degree}\;\Rightarrow\;\text{RR supply}
\;\Rightarrow\;\text{Hodge index}.
$$

- **Duality is available** in arithmetic form: theta/Poisson on Spec ℤ already satisfies exact
  RR (frontier map, base level).
- **Degree positivity of effective classes is the BVI receiver.** So the analytic content
  relocates into a *linear* degree statement on a cone, not a quadratic positivity.
- In algebraic geometry, degree positivity is automatic because an effective class *has a
  section*, and a section's zeros count its degree. The analogue here is zero counting for entire
  functions of exponential type (Jensen/Landau), with the integer nodes $\log n$ as zero sites.
- Dimensions are integers (C7), and the universal floor law concerns quadratic floors, not
  dimensions.

**First theorems.**
- (B1) Define $\mathcal P$ with a separate integer obstruction index and real arithmetic degree;
  recover the proved degree-minus-log-torsion formula and its all-aperture interpolation.
- (B2) A Mayer–Vietoris sequence across two apertures, so that $h^1$ jumps are localized at
  prime-power nodes. This matches node criticality (C5) and the shell-flux decomposition
  (Wall 1.13).
- (B3) A duality pairing $h^1(D)\simeq h^0(K-D)^\vee$ from the theta functional equation at
  base level.
- (B4) Recover the certified windows ($r\le3/10$, odd $r\le181/500$) as vanishing of a
  genuine obstruction. The proved weighted statement is payment by the archimedean budget,
  not vanishing of `apertureH1ChebyshevCorrection`. On horizon-prime-blind odd tests that
  correction still equals `poleCharge = 2 * oddPoleMoment²`
  (`apertureH1ChebyshevCorrection_of_isHorizonPrimeBlind`).

**Kill test.** Over $\mathbb F_q$ the construction must reproduce étale $H^1$ of the curve and its
dimension $2g$ (the corpus already identifies "the genus is the aperture of the radical"). On the
golden datum, (B1)–(B3) must hold while the vanishing fails. If (B3) and the degree statement
both hold for the golden datum, the mechanism is Beurling-universal and dead.

**Honest assessment.** B does not create the missing estimate. It moves it into a degree
statement and adds exact-sequence tools that let local certificates (which exist) glue. Its value
is structural, and its risk is that $\mathcal P$, a sheaf of convex sets, has only a nonabelian
$H^1$. Linearizing through the dual cone (negative directions) is the first technical step.

### 2.3 Mechanism C — one-sided Stepanov counting at the band (targets Wall 1 directly)

**Corpus facts.**
- RH is equivalent to a *one-sided upper bound* for one explicit spline prime sum at square-root
  precision (`riemannHypothesis_iff_spline_prime_sum_le_of_gt_four`), via the one-sided Landau
  engine.
- On curves: purity ⟺ the Hasse–Weil square-root remainder (killed routes, ACS dual/ambient
  survivor).
- Stepanov's method over finite fields is formalized (`RHTower/StepanovCount.lean`:
  `Stepanov.exists_nonzero_solution`; `HTGeometry/ShiftedSubgroupStepanov.lean`).
- Upper-bound sieves lose a factor 2 on signed pair statistics (TTPC).
- Sign-blind octave statements hold for every $\{-1,0,1\}$ sequence, so they cannot bound
  (THIM §3.20).

**Observation.** The packet theorem has exactly the logical shape of Bombieri's proof of Weil:
an *upper* bound for point counts at square-root precision suffices. Bombieri gets that upper
bound from Stepanov's auxiliary polynomial. It is the only upper-bound engine known in any
arithmetic setting that is *parity-free*, because Frobenius makes "vanish at every rational
point" a single algebraic identity, $f^q=f\circ F$, rather than a sieve condition. Over ℤ the
missing ingredient is precisely an **exact identity that forces an auxiliary function to vanish
to high order at every prime power in a window simultaneously**. Candidates to test:
- $\log=\Lambda\star1$ (log is the "Frobenius derivative" of the divisor lattice);
- $\Lambda(n(n+1))=0$ for $n\ge2$ (Bézout);
- the cyclotomic incidence recurrence (BVI pillar 2).

The capacity side is Landau/Jensen zero counting for band-limited functions, which the corpus
already uses (Landau–Markov frame bounds on prime-power nodes).

**First theorems.**
- (C1) An $\mathbb F_q[t]$ calibration: rewrite the corpus Stepanov count as a band-limited
  auxiliary function on the scaling line of a curve datum, and recover the Hasse–Weil upper
  bound in the corpus's packet coordinates.
- (C2) Identify which step uses Frobenius and test each candidate identity above as a
  replacement on a window $[X,e^\ell X]$.

**Kill test.** The parity twin (Liouville against 1 on rough numbers, BVI §5). If the vanishing
condition is equally satisfied by the twin's weights, the count loses the factor 2 and the
mechanism dies.

**Honest assessment.** Lowest probability, highest payoff: it would cross Wall 1 directly
rather than move it.

### 2.4 Checked and rejected

| idea | why not | evidence |
|---|---|---|
| KMS / Bost–Connes positivity | Positivity alone supplies no upper bound; passive KMS completions are killed. (Mechanism A uses the ring relation as rigidity, not positivity.) | killed routes CANNOT-03, no-go-123, no-go-374 |
| Bagchi strong recurrence | Already in the corpus as an equivalence; adds no input | `riemannHypothesis_of_zetaStronglyRecurrent`, `zetaZeroWidth_le_iff_forall_exists_zetaDiscStronglyRecurrentOn` |
| Tensor-power amplification | Over $\mathbb F_q$ base change keeps the genus and raises $q$. Over ℚ, every amplification I know grows the conductor in proportion, so powers multiply the exponent (heuristic; topic 7 of §4.8 proposes proving it) | walls ledger 1.7 |
| Guth–Maynard as is | Formalized and selective, but density-level; reaches neither C4 nor a strip | §1.2 |
| More sign-blind or higher-moment observation | Blindness is closed under post-processing; degrees 5–6 close the hierarchy | BVI §5, THIM §5 |

---

## 3. Q2 — The three questions to focus on

The choice rule is leverage: each question is the meeting point of one wall's faces across all
programmes, has a precise corpus formulation, and has milestones that count as progress even
without RH (walls ledger §6).

### Q-I (Wall 1, U1). Is there a Beurling-selective, single-ζ estimate that beats the trivial exponent at the square-root band?

**Precise forms.** These are equivalent in the corpus, and each is a fixed zero-free strip:
- $\sup_TE_T(\varepsilon)<\infty$ at *one* fixed $\varepsilon<\tfrac12$ along an interval of
  dampings (BVI §7.1);
- $\bigl|\sum_{e\le N}(\mu\star\Lambda)(e)\bigr|\le CN^\beta$ for one $\beta<1$
  (`receiverBounded_moebius_and_liouville_of_vonMangoldtConv_partialSum_rpow`);
- a Möbius short-window mean-square power saving at a fixed power length
  (`moebiusPowerWindowSaving_iff`);
- a cross entry of the two-pole compression with rate $<2$ (BiScale §3.10: the rate is
  $1+2\Delta$, and VK gives exactly 2).

**Tool-level form.** Which Class III (Bézout-selective) identity controls the off-diagonal
entries $G_{ij}$, $i\ne j$, of the 25-entry Vaughan Gram of the signed interior energy?
- The diagonal is sign-blind and nonsummable
  (`complete_signed_interior_energy_and_vaughan_calibration`).
- The equivalent obligations are BVI's coercive contraction
  $2M^{\mathrm{int}}_T+\dots\le(1-\delta)E_T+C_\varepsilon$, and THIM's interior anti-alignment
  gap $\theta(\varepsilon,t)<1$ between the proved collars
  (`riemannHypothesis_iff_forall_ne_zero_exists_longSawtooth_tail_antiAlignment_gap`). Planted
  Euler kernels show collars alone do not suffice
  (`plantedEulerKernel_collar_and_finiteness_obstruction`).

**Why this one.**
- All 31 live routes need Wall 1, and a strip is the strongest possible result short of RH.
- The VK band is the only selective receiver statement so far, and its extra width is exactly
  Vinogradov's additive input. That is a working proof of concept that selectivity comes from
  additive structure at one ζ.
- Guth–Maynard is formalized and already supplies unbalanced centered-prime dispersion in
  `ShortWindowDispersionAtSeventeenThirtieths`; its range excludes the balanced band.
  The analytic face of the remaining question is short-interval prime variance,
  equivalently signed prime pairs at gap $h\le\sqrt N$ (TTPC).

**Milestones.**
- Any improvement of the VK band exponent proved in receiver coordinates.
- A selective statement at fixed $\varepsilon<\tfrac12$ on a *restricted* family (the
  oscillating-probe superpositions are fully classified, so the next family should be the
  Vaughan pieces).
- Or a sharp no-go: "Class III identities as identities cannot control $G_{ij}$", together with
  its positive survivor.

**Formalized Vaughan milestone.** Fixed real superpositions of the five Vaughan pieces are
now classified for $0<\varepsilon<1/2$. Admission forces the explicit linear mean to vanish
and, for positive cutoffs, forces equal coefficients on the two convolution pieces.
After these cancellations, admission is exactly the original receiver problem unless its
coefficient is zero. The admitted coefficient space has dimension two or three, according
as the receiver is unpaid or paid, with unique coordinates in two explicit paid directions
and the receiver direction (`TheAdmittedVaughanCoefficientSpace`).
The centered fixed-cutoff Gram has an explicit smooth rank-one density
at scale $T^{1-2\varepsilon}$; the actual interior has zero density at that scale.
The harmonic factors are nonzero at every positive finite cutoff by an exact terminal-prime
valuation law. See `FixedVaughanPacketsHaveTwoExplicitObstructions`,
`VaughanPacketsHaveAnExactResidualEnergyDensity`, and
`RHTower/FiniteMobiusHarmonicSumsNeverVanish`.
At product horizons `T=UV`, the entire centered Gram is uniformly `o(T^(1-2ε))`
over all factorizations, including a fixed smaller cutoff; packets with bounded moving
coefficients obey the same law (`ProductHorizonVaughanGramsHaveZeroTrivialDensity`).
For every fixed `0<ε≤1`, a power gain for the normalized square empty-leg energy
is equivalent to `Θ<1`, through its exact quartic comparison with the signed reciprocal
tail (`TheEmptyVaughanLegDetectsAFixedStrip`).
The undamped truncated convolution also satisfies
`Σ_(d≤n)(μ_≤U*μ_≤V*1)(d)=nH_UH_V+O_q(n/(log n)^q)` for every fixed integer `q≥0`,
uniformly over all cutoff pairs (`UniformLogarithmicCancellationInTheVaughanConvolution`).
The generic damped floor transform now preserves all common logarithmic savings
for divisor-square bounded coefficient families with convergent reciprocal mass
(`LogarithmicCancellationSurvivesTheDampedFloorTransform`, `0<ε≤1/2`).
The actual Vaughan coefficient minus `H_UH_V` now satisfies those bounds, and its
centered convolution row is exactly `-H_UH_V A_(1,ε)-A_(r,ε)`
(`TheVaughanConvolutionSeparatesItsSmoothMean`). All truncated Möbius partial sums
and their damped centered prefixes also share every logarithmic rate uniformly
over the cutoff (`UniformLogarithmicCancellationInTruncatedMobiusReceivers`).
The checked generic prefix-to-energy transfer preserves these logarithmic rates
in pronic norm below half damping, retaining the common finite-head bound
(`UniformLogarithmicEnergyFromPrefixCancellation`). The actual convolution
fluctuation and all truncated Möbius receivers now satisfy those common norm
bounds (`UniformLogarithmicEnergyInTheVaughanConvolution`). The actual centered
Möbius prefix and Bézout interior now have every logarithmic norm saving below
half damping (`LogarithmicEnergySavingsForTheMobiusInterior`). All five actual
smooth-subtracted rows now share every logarithmic norm saving uniformly in both
cutoffs; their sum is exactly the Bézout interior
(`UniformLogarithmicRemaindersInAllVaughanRows`). The complete centered Gram now
satisfies the uniform smooth rank-one law with every logarithmic error rate
(`UniformVaughanGramsFollowTheirSmoothRankOneTerm`). Hence every normalized
entry tends to zero when the horizon and cutoff product diverge separately,
with no relation required between those scales. Every centered packet has the
corresponding homogeneous logarithmic norm and energy bounds, with factors
`L(w)=Σ_i|w_i|` and `L(w)^2`. Equal convolution coefficients remove the smooth
term, and bounded moving coefficients preserve zero normalized packet norm at
independently divergent horizons and cutoff products
(`UniformLogarithmicLawsForVaughanSuperpositions`). The actual amplitude set
`{H_U²H_V²}` is now Lean-verified compact and countably infinite; positive limits
force eventual equality in one finite cutoff fiber. At positive cutoffs its
zero limit is equivalent to product escape
(`TheCompactArithmeticAmplitudesOfVaughanGrams`). Every finite subcritical Gram
limit is the smooth matrix of an amplitude in that set; every amplitude is
attained with positive cutoffs. Convergence is equivalent to product escape or
eventual constancy of a positive amplitude (`TheSubcriticalVaughanGramLimitSet`).
The explicit bounded-packet energy decay corollary is checked as well. Zero is
the unique scalar amplitude accumulation point; positive amplitudes are isolated
and the two convergence alternatives are mutually exclusive
(`TheOnlyAccumulationOfVaughanAmplitudesIsZero`). Exact matrix ranks are checked:
zero at zero amplitude and one at every positive amplitude
(`TheRanksOfSubcriticalVaughanLimits`). The actual matrix family is compact and
countably infinite with unique zero accumulation; its normalized form is
independent of damping (`TheTopologyOfSubcriticalVaughanGramLimits`). All 39
targets in the complete subcritical classification passed final direct checks.
Finite denominator clearing also gives `|H_N|≥1/D` for every positive common
multiple of `1,...,N`, hence `|H_N|≥1/N!` for positive N; all three arithmetic
targets passed final checks (`FiniteMobiusHarmonicSumsHaveExplicitLowerBounds`).
The relative Gram error is bounded by `C_(ε,q)(U!V!)²/(log H)^q`. Every positive
cutoff schedule admits divergent horizons making this error vanish. With
`U=V=n+1`, the same horizons give zero ordinary normalized limit and a rank-one
relative limit (`VaughanGramsAtTheirActualHarmonicAmplitude`); all seven targets
passed final direct checks.
These checked restricted-family results do not supply a fixed strip; full Q-I remains open.

### Q-II (Wall 14, U2/U3). Riemann–Roch for the scaling surface: which source-defined effective cone has the RR axiom, and is its Bézout positivity a linear degree statement?

**Precise form.** Construct $E\subset$ scaling cycles, defined from arithmetic sources and not
from the sign of $W$, such that $x^2>0\Rightarrow x\in E\lor -x\in E$ at every aperture. By
`exists_bezout_effectivity_iff_hodgeIndex`, Bézout on such an $E$ implies RH. The converse for
a chosen $E$ needs a separate proof: the theorem concerns existence of some cone, not every RR
cone. Indeed, the negative-Chebyshev graded source cone has unconditional all-aperture RR and
unconditionally fails Bézout (`gradedChebyshevSourceCone_riemannRoch_and_not_bezout`). On the
positive cone, Bézout is already the BVI receiver. The vanishing-theorem version is Mechanism B: find $h^1$ of the
payment sheaf, prove duality, and reduce vanishing to degree.

**Source-boundary audit.** For nonnegative even fibre-invariant reserves, RR and Bézout together
force exact equality between the reserve and the Weil defect. Bézout on the graded cone itself
forces reserve nonnegativity; allowing a signed reserve does not remove that obligation
(`sourceCone_riemannRoch_and_bezout_iff`, `gradedSourceCone_riemannRoch_and_bezout_iff`).
Every finite scalar L² reserve and every postprocessing of finitely many linear source
readings fails Bézout at every positive aperture. The positive theorem behind this obstruction
is unbounded Weil energy in every such reading kernel
(`exists_realTestAt_in_ker_weilPair_gt_mul_integral_sq`). These results separate unconditional
RR supply from the still missing independent degree or section mechanism.

Even adjoining exact L² mass to those finite readings does not suffice:
unit-mass Weil energy remains unbounded in their common kernel. Every nonlinear
threshold based on these data admits a strict effective negative square
(`FiniteReadingsAndMassCannotSupplyBezout`). This obstruction concerns the stated
fibre-threshold source cones, rather than arbitrary source restrictions.

Evenness is unnecessary for the sharp boundary: closed and strict cones only read
`max(Φ,0)`, and RR together with Bézout forces that positive part to equal the defect
(`sourceCone_riemannRoch_and_bezout_iff_positivePart_eq_defect`). Compact scaling numerical
equivalence is equality (`scalingSurface_numerical_equivalence_iff_eq`), so nonzero principal
representatives require a larger source carrier. The Boolean `sourceH0` encoding cannot
satisfy the classical dimension form of RR for any canonical class or Euler constant
(`exists_sourceH0_riemannRoch_dimension_failure`). These statements have clean transitive
Lean axiom audits; they do not supply the missing positive sheaf theory.

Independent arithmetic Bézout is available on the original pairing once its reserve retains
the full source energy. At every positive aperture, the explicit Chebyshev majorant
`criticalDeficitSourceEnergy + 2(10 + 72 exp(r)) integral(f²)` has Bézout and ampleness;
an effective class of ample degree zero is actually zero. Its strictly positive extra
reserve makes RR fail (`ArithmeticMajorantsSupplyBezout`). The remaining problem is
simultaneous RR and Bézout, not independent Bézout alone.
These same aperture cones are convex, pointed and generating, with closure
under addition and nonnegative scaling (`ArithmeticMajorantConeGeometry`).

The precise quadratic price is now certified: threshold `δ + κM` has original-pairing
Bézout exactly when `δ + (κ/2)M` is nonnegative, for a nonnegative fibre-null quadratic
mass and `κ ≥ 0` (`BezoutCostsTwiceTheNegativeReserve`). Thus changing effectivity
requires twice the compensation needed when changing the intersection pairing.
The full prime source also has an aperture-independent estimate
`primeSum(f) ≤ 2 S integral((exp(|t|)f(t))²)`, where `S = sum Lambda(n)/n^(3/2)`
(`ExponentialSourceMassControlsTheFullPrimeSum`). These are unconditional source
bounds; neither removes the extra reserve required by RR.

This prime bound now gives one globally compatible arithmetic cone on the full
compact-source surface, with no aperture parameter. It is convex, pointed, and
generating; Bézout and strict ampleness hold on the original pairing. Its reserve
is exactly `δ+2R`, with `R` bounded below by source mass, so RR fails
(`GlobalArithmeticMajorantsSupplyBezout`). Aperture gluing is therefore unnecessary
for independent arithmetic Bézout; eliminating the extra reserve remains open.

Linearity also does not settle descent or positivity. On the larger actual Meyer source,
origin evaluation is a complex-linear degree whose sharp-square value is the strictly
positive mass `integral exp(t)|g(t)|²`. A nonzero Xi-cap Poisson boundary has positive square
degree, so this degree cannot descend to genuine cohomology
(`OriginDegreeDoesNotDescendThroughPoissonBoundaries`). The descended ordinary trace
degree and the positive origin degree therefore solve different parts of the requested
degree construction.

This failure persists after arbitrary normalized corrections using both pole values.
The actual negative Euler operator produces a nonzero boundary with transform
`s(s−1)xi(s)`; its sharp square gives a pure-source principal cycle with positive
origin degree and zero pole readings (`PoleBlindPoissonBoundariesHavePositiveOriginDegree`).
Thus the descent obstruction cannot be repaired by adjusting the two fibre degrees.

The ordinary trace's exact loss of information is now classified
(`MeyerNumericalRadicalAndMultiplicity`). Its radical consists of sources whose zeroth
Mellin values vanish at every Xi point; genuine Poisson boundaries require all lower
jets to vanish. Equality of numerical and principal equivalence is therefore exactly
simplicity of the Xi divisor. Ordinary sharp-square trace positivity is exactly RH,
with no simplicity requirement. These are distinct obligations, even on the genuine
source quotient; a multiple zero supplies an actual nonprincipal square-zero class.

Actual source inversion now gives an algebraic description of the same radical
(`MeyerQuasiInverseRadical`). A class has a quasi-inverse precisely when none of
its Xi values equals −1. Every product of a class has a quasi-inverse precisely
when all its Xi values vanish. Thus this universal inversion condition is exactly
the ordinary trace radical; its vanishing is equivalent to Xi simplicity.

The genuine Meyer surface now carries this descended linear trace degree as an
actual RR construction (`MeyerSourceIntersectionSurface`). Its degree cone has
Bézout, ampleness, and additive closure each exactly under RH. The full source
carrier and genuine principal classes therefore do not remove the order obligation;
faithfulness of numerical equivalence retains the separate simplicity condition.

A critical Xi point supplied by Hardy gives an unconditional positive descended
degree with an explicit nonprincipal null source (`PositiveMeyerDegreesCanForgetClasses`).
Its sharp-square degree is normalized to one on another actual source.

Changing the linear degree cannot remove this second obstruction while retaining
strict positivity on the sharp square of every nonprincipal source. Existence of any such degree
is exactly RH together with simplicity (`FaithfulPositiveMeyerDegrees`). The exact
local witness is a single jet of order `j`: its sharp square is principal precisely
when reflection moves its Xi point or `2j` reaches the local multiplicity. These
criteria are formalized on the genuine source quotient without continuity assumptions.

The actual faithful full-Hasse convolution representation respects arithmetic
sharp as Hilbert adjoint exactly under the same RH-and-simplicity condition
(`ArithmeticSharpAndTheHilbertAdjoint`). Thus an operator Gram interpretation
of every arithmetic sharp square has precisely the faithful-degree obstruction;
the Hilbert representation alone does not discharge it.

The actual full-Hasse operators nevertheless supply a faithful descended
quadratic reserve (`FaithfulHilbertSchmidtSourceReserves`). Its difference
from the ordinary trace defect is exactly half the squared Hilbert–Schmidt
adjoint defect. The resulting cone has Bézout, ampleness, convexity, generation,
and pointedness modulo genuine principal classes unconditionally. Its RR axiom,
and existence of a linear degree representing this exact reserve on arithmetic
sharp squares, are each equivalent to RH plus simplicity.

Full-Hasse centered orbits have an exact support classification
(`MeyerBoundedCenteredOrbits`): Hilbert–Schmidt boundedness, boundedness of every
individual Xi jet, support only in critical highest jets, and Hilbert–Schmidt
norm isometry are equivalent. Boundedness for all sources, or already for the
fixed Xi-avoiding source, is exactly RH plus simplicity.
The bounded-orbit classes form an explicitly defined nontrivial complex subspace,
stable under sharp and convolution (`MeyerCriticalTopAlgebra`). Products retain
only simple critical values. Ordinary trace is nonnegative on this carrier,
and its value-zero radical annihilates the carrier in genuine cohomology.
The faithful reserve is bounded along a source orbit exactly when it is
invariant there, equivalently when the source belongs to this carrier
(`MeyerHilbertReserveFlowRigidity`). Global reserve invariance is exactly
the faithful cone's RR condition, hence RH plus simplicity.

Restricting the original pairing and both fibres to bounded source orbits
gives RR, Bézout, ampleness and additive closure unconditionally
(`BoundedMeyerSourceSurface`). Its numerical radical and cone lineality
are exactly zero pole degrees and zero Xi values. Equality with principal
cycles is equivalent to simplicity of critical zeros alone. Actual sources
of trace one occur above every height; coverage of the full source surface
still requires RH plus simplicity.
On this restricted carrier the faithful reserve remains invariant, with
Bézout and ampleness unconditionally (`BoundedMeyerFaithfulReserve`). Its
RR axiom, adjoint compatibility, existence of a faithful positive degree,
and exact linear-degree representation of the reserve are equivalent to
critical simplicity alone. At any multiple critical point an explicit
isometric nonprincipal source has zero ordinary trace and strictly positive
reserve and squared adjoint defect. No multiple critical zero is assumed
or proved to exist.

Centered flow preserves the literal mixed arithmetic sharp product, so every
reading of that product is invariant. A nonnegative invariant majorant controlling
the original mixed trace exists exactly under RH
(`FlowInvariantMeyerMajorantsForceCriticality`). Two fixed point sources already
turn such a majorant into control of each Mellin evaluation; no norm axioms or
quotient descent are needed. Positivity and invariance of another degree alone
therefore do not supply the missing comparison with the original pairing.

The sum over all critical Xi multiplicity copies now gives a canonical positive
linear degree on genuine cohomology (`CriticalMeyerTraceDegree`). Its square
energy is exactly the summable critical-value norm square; its kernel consists
of sources vanishing at every critical Xi value. This energy is invariant,
dominates the original mixed trace exactly under RH, and is faithful exactly
under RH plus simplicity. The construction does not classify arbitrary positive
degrees or provide an independent prime-side positivity law.

**Why this one.**
- It is the only formulation in which positivity could be *forced* rather than estimated, which
  is how purity is obtained over $\mathbb F_q$.
- The corpus has calibrated it unusually well: positive point counts, integrality,
  Witt structure and the functional equation are each proved insufficient (golden datum);
  pairing-preserving ambient enlargement is refuted; base RR exists. That leaves one missing
  datum: *how classes move* (linear equivalence, sections).
- Partial answers produce new certified windows, so progress is measurable.

The finite-field calibration now separates these requirements exactly. Every Rosati
source cone and its Frobenius-mass section presentation has Bézout and ampleness,
even for nonunitary curve data. RR holds precisely when the Frobenius reflection
defect vanishes (`RosatiSectionsHaveBezoutWithoutUnitarity`). The golden datum
satisfies both positivity axioms and fails RR: positive section mass alone does
not supply purity.

**Milestones after the audit.**
- All-aperture source RR is already available, including the exact arithmetic source reserve
  in `ExactArithmeticSourceEffectivity`. Prove its simultaneous Bézout positivity from an
  independent arithmetic construction.
- Recover Weil's full chain over $\mathbb F_q$, keeping positive source masses distinct from
  the purity condition needed for RR.
- Genuine Poisson principal cycles and their trace-degree-zero law are available on the
  Meyer carrier. Construct the requested geometric section theory and account for the
  higher-jet information that ordinary numerical degree discards.

### Q-III (Wall 3). What are the possible escape states, and is every one generated by a hull point on the Kronecker curve?

**Precise form.**
- Classify the $\mathcal W_{1/2}$-modules $H_K$ that arise from `exists_cofactorGram_limit` along
  an escaping receiver, together with their signed data (antipodality, pole trace, forcing split).
- Decide whether the hull of $\ker\pi$ always lies in the translated off-line zero hull, and
  whether its codimension equals the number of zeros (AOT index formula below the width; THIM
  §7.8 topic 2).
- Since $\#$rightZeros is even when finite and RH ⟺ $\#<2$, an index formula with an
  *independent* (arithmetic) evaluation would decide RH by an integer computation.

**Why this one.**
- It turns an estimate (Wall 1.10: "absolute source control *or exclusion of escape*") into a
  rigidity/classification problem. Such problems are solved by structure, and integer-valued
  answers satisfy C7.
- The existence of the limit, hull nonemptiness and "codimension = count" on computed families
  are already proved. What is missing is the module–ideal bridge (A1–A2), the exponent law (A3)
  and the square-root-scale additive structure (A4).

**Milestones.**
- (A1)–(A3) are self-contained, Lean-sized theorems.
- The golden-datum escape module as a computed counterexample class.
- A proof that white noise violates antipodality.

**Q-III audit correction.** Several proposed milestones require revision.

- A1–A2 now have unconditional proofs for every actual common Gram limit,
  including infinite-support paid Wiener kernels. The universal construction
  and all corresponding canonical source checks and transitive axiom audits
  passed. See `TheCofactorLimitCarriesACyclicDilationAction`,
  `TheCofactorLimitIsAWienerModule`, and
  `PaidWienerKernelsAnnihilateTheCofactorLimit` in `ArithmeticDefectRigidity/`.
- White noise **does not violate Gram antipodality**. Every positive kernel
  has a unique extension adjoining the negative receiver vector. The actual
  source's full fixed signed table is now formalized: receiver, residual, and
  forcing coordinates are `v_j`, `-v_j`, and zero, respectively. Fixed pole
  traces normalized by the receiver norm vanish. The existing moving-dilation
  commutator also vanishes after normalization. The unscaled trace and moving
  cofactor summation remain additional information.
- Stronger dilation contraction controls the operator-norm-bounded character
  locus, not automatically the entire hull of the annihilator. Faithful
  weighted white kernels have exact stronger contraction and full annihilator
  hull. Closed representation image suffices to identify the two hulls; in
  particular this distinction disappears in finite dimension. The family’s
  faithfulness, full hull, exact power norms, spectral radius, unbounded extra
  character, and closed-image comparison passed Lean with standard axioms
  and final source checks. The generic spectral inference is retired with
  this positive replacement.
- The suggested nontrivial raw translation scale with bounded `k²/E` collapses
  for the actual receiver. Recentring, leaving the origin value, and resetting
  only the origin give different dilation domains. The stronger recentered
  collapse for bounded `k/E` passed its final Lean source check. The actual
  Vinogradov–Korobov saving gives still larger invisible translation scales:
  bounded `k^(1-epsilon)/E` for recentered shifts and bounded
  `k^(2-2epsilon)/E` for raw shifts. Both passed Lean axiom audits and final
  source verification.
- The closed Wiener-annihilator quotient cannot have countably infinite Hamel
  dimension. Its finite dimension agrees with the cyclic Hilbert module’s
  dimension. The stronger exact infinite value, continuum Hamel dimension,
  also passed Lean with standard axioms and final source checks. Thus an
  infinite zero-count formula must specify its index convention and recover
  multiplicity separately.
- Common Gram modules also exist on admission. Every actual admitted module
  has faithful Wiener action and the full Bohr hull; a nonfaithful actual
  module therefore forces escape. Complete source pairings and triangular
  coefficient recovery prove this with standard axioms and final Lean checks.
  Admission also gives a unique common kernel, infinite Hilbert dimension
  and continuum annihilator-quotient index. Thus a finite-dimensional actual
  module forces escape. These refinements passed final Lean source checks.
  These admitted modules are not counterexamples about escaping receivers.
- Actual diagonal data now retain numeric horizon order:
  `E(floor((T_m+1)/p))/E(T_m+1)` tends to `p*K(p,p)` for every actual
  common limit. This profile decreases in the ordinary integer order and
  equals one on admission. Exact dilation blocks and the diagonal theorem
  passed canonical Lean source checks and standard axiom audits. Mixed
  horizon transport and its stronger module consequences remain pending.
- Changing the cyclic vector by a critical Wiener unit gives a unitary
  comparison intertwining the full Wiener action. It preserves all operator
  norms, the annihilator, operator hull and dimension. Actual real unit
  convolutions now have the same transport after own-energy normalization:
  the correction vanishes and the source-energy ratio has a positive limit.
  Escape is preserved, including for the Möbius–Liouville unit relation.
  These statements passed canonical Lean checks with standard axioms.
- Finite actual annihilator-quotient dimension is the sum of joint generalized
  character-space multiplicities, indexed by normalized Bohr representatives.
  Every occurring multiplicity is positive. The exact counting theorem passed
  canonical Lean checks; it does not identify these characters with zeta zeros.
- Numeric horizon order has a sharp positive consequence: a zero cofactor at
  `p` forces dimension at most `p-1`. It still does not select finite half-plane
  points from abstract rank-one data. Augmentation satisfies every packet
  contraction and numeric diagonal order, but its singleton hull lies outside
  all finite half-plane points. Countermodel and cutoff survivor passed
  canonical Lean checks; no actual Möbius realization of augmentation is asserted.
- Every actual rank-one character is augmentation or a real power times a
  multiplicative sign: `chi(p)=eta(p)*p^(-s)`, `s>=1/2`, `eta(p)` in `{−1,1}`.
  The full factorization passed canonical Lean checks with standard axioms.
  It leaves the signs unselected and gives no arithmetic zero identification.

The open classification is still the arithmetic identification of the actual
module hull with translated zero data, including Kronecker-curve generation
and multiplicities. The module–ideal inclusion alone does not settle it.

---

## 4. Q3 — A field that would supply the tools: *Biarithmetic Geometry*

### 4.1 Diagnosis: one absence behind three walls

| wall | the missing tool, as a question | what $\mathbb F_q$ has | what ℤ has (corpus) |
|---|---|---|---|
| W1 | An identity-level source of square-root cancellation in incomplete signed sums | Gauss/Lefschetz: $\lvert S\rvert^2=q$ from complete sums (SSA) | Only complete-period quadratic data are identities, and they are **exactly sign-blind** (BVI pillar 12); period $e^{\psi(N)}\gg$ horizon $N$ |
| W3 | Retaining information through limits, observation and shared budgets | Finite horizon $=$ period; $\zeta_C$ determined by $g$ counts | Escape keeps dilation and kills fixed successors (ADR); local payments exist but do not glue (AIP); finite observation is exact but proves nothing |
| W14 | A structure that orients the obstruction space | Frobenius is a ring endomorphism; Hodge index on $C\times C$ via RR | The scaling surface has Hodge index ⟺ RH; all-aperture graded source RR exists, but compatible independent Bézout/ample positivity is missing; golden datum shows positivity and integrality do not orient |

**Thesis.** All three walls are the absence of an arithmetic substitute for the pair *(Frobenius
as a ring endomorphism, complete sums of polynomial length)*.
- Multiplicative structure alone is Beurling-universal (C1).
- Additive structure alone needs family averages (C2).
- The usable coupling of the two over ℤ is the ring relation itself:
  $n\cdot(m+1)=nm+n$, the affine semigroup $\mathbb N\rtimes\mathbb N^\times$, whose shadows in the
  corpus are the Class III Bézout-selective laws. Those laws are presently *identities without
  estimates*.

The field's job is to give that coupling a geometry in which estimates follow from structure.

### 4.2 Questions of the field

1. **Horizon-complete objects.** Which finite structures attached to $[1,N]$ have "period =
   horizon", so that a complete-sum identity, unlike a complete-*period* one, retains signs? How
   does sign visibility decay as a function of horizon/period?
2. **The ring action at finite horizon.** What is the representation theory of the truncated
   affine semigroup acting on sequences and on the scaling line? Which positive-definite states
   with prescribed dilation scaling and translation covariance exist?
3. **Payment cohomology.** For the sheaf of local payments on the scaling site: what are
   $h^0,h^1$, their Euler characteristic (conjecturally $E(s)$), the exact sequences across
   apertures and prime-power nodes, and a duality?
4. **Orientation.** Is there a polarization on $H^1$ whose sign is *forced* by integrality
   together with the ring relation (not by either alone, since both alone are calibrated
   insufficient)?
5. **Escape and rigidity.** Which modules over $\mathcal W_{1/2}$ arise as limits of unbounded
   arithmetic energies, and when is such a module determined by its hull (spectral synthesis in
   infinite rank)?
6. **Infinite-rank coercivity.** When is a translation-invariant form over a dense subgroup of ℝ
   generated by infinitely many independent logarithms coercive? The rank-one (lattice, curve
   comb) case is coercive; the ℤ case (dense prime shifts, `denseShifts_twoPrime`) is not, under
   current tools.

### 4.3 Point of view

- **From functions to actions.** The primary object is not ζ or Λ but the action of
  $\mathbb N\rtimes\mathbb N^\times$, truncated at horizon $N$, on the divisor incidence
  $\mathbf 1_{d\mid n}$. Dirichlet series, receivers and Weil forms are its characters, matrix
  coefficients and invariants.
- **From positivity to obstruction.** Positivity is the *vanishing of an obstruction class*,
  with local existence given for free. Estimates are bounds on dimensions or norms of
  obstruction spaces.
- **From continuous to quantized.** Main invariants are integers (indices, codimensions, $h^i$,
  defect counts), computed by exact sequences, not by deformation (C6, C7).
- **Selectivity is part of the definition.** A statement is not a theorem of the field until its
  selectivity class is stated and its battery run.

### 4.4 Objects

| object | definition sketch | corpus seed |
|---|---|---|
| Horizon ring $R_N$ | $[1,N]$ with partial $+$ and $\times$; incidence $I_{N,M}=\mathbf 1_{d\mid n}$, $d\le N<n\le M$ | BVI rows, THIM trans-horizon |
| Truncated affine semigroup $\mathcal A_N$ | translations $u$ and dilations $s_n$, $n\le N$, with $s_nu=u^ns_n$ where defined | Class III laws; ADR successor words (`abs_receiver_word_sub_dilation_le`) |
| Scaling site $\mathcal S$ | the aperture line with the prime-power node divisor and pole plane | ACS scaling surface; AOT Nyquist–RR |
| Payment sheaf $\mathcal P$ | local allocations of archimedean surplus to atoms, with restriction | AIP strip surplus; AOT frustration index |
| Obstruction classes $h^1(\mathcal P)$ | gluing obstruction; Euler characteristic $E(s)$ | AOT `boxH1Obstruction` |
| Escape modules | $(H_K,\pi)$ over $\mathcal W_{1/2}$ from normalized escaping energies, with signed data | ADR `exists_cofactorGram_limit`; AOT paid ideal |
| Bohr hulls and indices | hull in $\overline{\mathbb D}^\infty$, codimension of ideals | AOT |
| Selectivity battery | Beurling systems, golden datum, shifted pair $\zeta(s-a)\zeta(s+a)$, Estermann single-prime deformation, parity twins, $\log4$ vs $\log6$, $\mathbb F_q$ reduction | BiScale §7.1, BVI §7.8, SSA, ACS |

### 4.5 Language

- Sheaves and exact sequences over $\mathcal S$ with a horizon filtration.
- Banach modules and Gelfand spectra in infinite rank.
- Representations of $\mathcal A_N$ and their limits as $N\to\infty$, with stated order of the
  horizon and damping limits.
- Indices, Euler characteristics and dualities.
- A *selectivity grading* attached to every statement: I (Beurling-universal),
  II (sign-blind), III (ring-selective), as THIM already does informally.

### 4.6 Foundational principles

1. **Biselectivity.** Every main theorem uses $+$ and $\times$ jointly; a statement provable from
   one alone is classified, not credited.
2. **Horizon realism.** Objects live at polynomial horizon $N^{O(1)}$, never at the full period;
   every limit names its order.
3. **Signed linearity first.** Primary quantities are linear in signed data (readouts, packets,
   prefix discrepancies). Quadratic positivity is derived, because sign-blindness is closed under
   post-processing.
4. **Quantization.** Invariants are integers, and continuity arguments are replaced by exact
   sequences and rigidity.
5. **Deformation sensitivity.** Theorems must fail under single-prime Euler deformation; a
   statement robust to it is a meta-no-go instance.
6. **Pole before zeros.** The polar density $e^{t/2}$ sets the critical node density (square
   root). Every construction pays the pole first (SSA, BiScale §3.4).
7. **Local is free, gluing is everything.** Per-prime payments are assumed available. The content
   of every theorem is in interaction, i.e. in $h^1$.
8. **Calibrate over $\mathbb F_q$.** Every definition must specialize to the Weil/Bombieri
   argument, where horizon $=$ period and Frobenius is a ring map.

### 4.7 Criteria it must fulfil

- **(K1) Specialization.** Over $\mathbb F_q[t]$ and curve data, $h^1(\mathcal P)$ has dimension
  $2g$, duality is Serre duality, and the RH-equivalent statement is a theorem.
- **(K2) Selectivity.** The central statements fail for the golden datum, for every Beurling
  system with an off-line zero, under Estermann deformation and for the shifted pair, and they
  separate $\log4$ from $\log6$.
- **(K3) Recovery.** The field reproves, in its own coordinates, PNT (as $h^1$ subexponential),
  the VK band and the Guth–Maynard density exponent, and identifies which structure each one
  uses.
- **(K4) New unconditional output.** Before any claim toward RH, the field must produce a new
  unconditional statement: a certified window past $181/500$, an improved band exponent, or a
  classified escape-module family.
- **(K5) Finitary checkability.** Every horizon-$N$ statement is a finite identity or inequality
  that can be formalized without new analytic premises (corpus integrity rules).

### 4.8 Research topics (ranked)

1. **Horizon-complete sums and sign visibility.** Quantify the loss between prefix data (which
   see signs) and complete-period data (which provably do not) as a function of horizon/period.
   *Seed:* BVI pillar 12; `parityPair_separated_on_vinogradovKorobovBand`.
2. **Escape modules (Mechanism A).** Prove A1–A4, compute the golden-datum module, and test
   white noise against antipodality.
3. **Payment cohomology (Mechanism B).** Define $\mathcal P$, realize the corrected arithmetic
   degree and integer obstruction index, prove Mayer–Vietoris across prime-power nodes and base duality; restate the
   certified windows as $h^1=0$.
4. **Quantitative Class III.** Turn the Bézout-selective identities (zero-diagonal pronic Abel
   summation, Bézout shell midpoint annihilation, least successor-seed resonance) into
   inequalities on the off-diagonal Vaughan entries (Q-I).
5. **Stepanov over the horizon ring (Mechanism C).** Find a vanishing-forcing identity at prime
   powers, calibrated by the corpus's $\mathbb F_q$ Stepanov count.
6. **Infinite-rank coercivity.** Bohr lifting with unbounded weights: when does per-coordinate
   (per-prime tower) coercivity, which is proved in AOT, transfer to the Kronecker line?
7. **Amplification with bounded conductor.** Prove as a no-go theorem that no Euler-preserving
   operation on ℚ-data multiplies the Frobenius exponent at bounded conductor, or find the
   exception. This explains walls-ledger 1.7 and fixes what a tensor-power trick over ℤ would
   need.
8. **Orientation.** A polarization on $h^1$ forced by integrality plus the ring relation, with
   the golden datum as the obligatory counterexample to each relation dropped.

### 4.9 Relation to existing mathematics, and what the field is not

- It borrows from Arakelov theory (theta $h^0$ and RR on Spec ℤ), from $\mathbb F_1$/λ-ring
  ideas (Frobenius lifts as descent data), from the Connes–Consani scaling site, from ring
  C*-algebras of $\mathbb N\rtimes\mathbb N^\times$ (Cuntz $\mathcal Q_\mathbb N$, Laca–Raeburn),
  from Hardy spaces of Dirichlet series and Nikolski cyclicity, and from additive combinatorics
  (Vinogradov, Guth–Maynard).
- It differs from each by insisting on **finite horizon, signed linear data, quantized
  invariants and the selectivity battery** as foundations. Those are the four places where the
  corpus proved existing frameworks lose the information RH needs.
- It is **not** another receiver reformulation: the width functor closes that line. It is not a
  positivity framework, since positivity alone is killed. It is not a family-average theory,
  which fails C2.

---

## 5. Recommended immediate actions (within existing programmes, read-only suggestions)

1. **ADR:** prove (A1) and (A3); compute the white-noise module against antipodality. This is the
   cheapest test of Mechanism A.
2. **AOT/ACS:** construct payment cohomology compatible with the proved arithmetic degree and
   torsion formula (B1). The original ordinary-dimension identity is impossible.
3. **BVI/THIM:** run the Vaughan off-diagonal entries $G_{ij}$ through the three selectivity
   classes and record which class each existing bound belongs to. This identifies where a Class
   III estimate must enter for Q-I.
4. **ACS (calibration):** rewrite `Stepanov.exists_nonzero_solution` in packet coordinates over a
   curve datum (C1).

---

## 6. Evidence

**Read in full:** the five reports above. **READMEs read:** all eighteen in the brief. For
BiScaleUncertainty, THIM and BVI, §§1–3 were read selectively and §§5–8 in full; the others were
read in full.

**Corpus searches** (`scripts/formal_tools.py research`; full output summaries in the log):
- obstruction hull / repairing ideal;
- escape covariance limit;
- curve vs integer comb;
- Hodge defect / RR;
- Beurling countermodels;
- forcing-data TFAE;
- Vinogradov MVT;
- Guth–Maynard large values (and lexical `guthMaynardLargeValuesBound`);
- Bézout axiom on the scaling surface;
- eventual Hodge index / tensor power;
- signed prime pairs;
- spectral synthesis;
- ADR dilation contraction;
- Stepanov;
- KMS / affine semigroup;
- Hardy space of Dirichlet series / Nikolski;
- Bagchi recurrence;
- Serre duality / vanishing;
- payment cohomology;
- ACT criticality;
- AIP local payment.

**Absent from the corpus by search:** Nikolski-type cyclicity in $H^2(\mathbb D^\infty)$, Serre
duality or vanishing on the scaling surface, payment cohomology, and Stepanov over ℤ. **Present:**
Bagchi recurrence, finite-field Stepanov, Guth–Maynard (unconditional), KMS (killed variants).

**Declarations confirmed by grep of `theorem|def NAME`** (file under
`formal/GaloisForLFunctions/`):

| declaration | file |
|---|---|
| `riemannHypothesis_iff_spline_prime_sum_le_of_gt_four` | BiScaleUncertainty/SplineProbeFiniteShiftBounds.lean |
| `riemannHypothesis_iff_packet_band_of_universal` | BiScaleUncertainty/PacketBandLaw.lean |
| `exists_blindOn_poleMass_eq_small_of_density` | BiScaleUncertainty/BlindSymbolValueAndLineDesigns.lean |
| `not_zeroPoleBlindPositiveOn_diff_four` | BiScaleUncertainty/PrimePowerZeroPoleNodeCriticality.lean |
| `finrank_primeBlind_subspace_eq_zero` | ArithmeticOrientationTheory/NyquistRiemannRochBeyondRankNullity.lean |
| `not_receiverBounded_iff_exists_obstruction`, `mem_obstructionHull_smoothPower_iff` | ArithmeticOrientationTheory/UnpayabilityIsLocatedOnTheBohrPolydisk.lean |
| `liouville_paidIdeal_obstructionHull_and_index_eq_moebius` | ArithmeticOrientationTheory/AnIndexFormulaForTheActualReceiver.lean:345 |
| `positiveCone_bezout_iff_cofinal_budget` | ArithmeticOrientationTheory/PoleSubtractionAndTheForcingSignDictionary.lean:224 |
| `scalingSubsurface_all_sectionEffectivityCone_castelnuovoSeveri_of_le` | ArithmeticOrientationTheory/TheEffectivityConeFromSections.lean:685 |
| `goldenDatum_not_bezout_sectionEffectivityCone` | ArithmeticOrientationTheory/TheEffectivityConeFromSections.lean |
| `graphCone_not_riemannRoch`, `exists_bezout_effectivity_iff_hodgeIndex`, `graphCone_bezout` | ArithmeticCastelnuovoSeveri/BezoutEffectivityAndTheBeurlingObstruction.lean |
| `hodgeIndex_bezout_tfae` | ArithmeticCastelnuovoSeveri/WhichArithmeticDataForceTheSign.lean:685 |
| `zeta_hodgeDefect_iff` | ArithmeticCastelnuovoSeveri/TheHodgeDefectCountsTheRightZeros.lean:556 |
| `zeta_cyclic_hodgeDefect_iff`, `denseShifts_twoPrime` | ArithmeticCastelnuovoSeveri/TheHodgeDefectIsCyclic.lean |
| `rightZeros_zeta_eq_empty_iff_subexponential_scalingSubsurface_odd_defect_floor`, `strictCoupledArithmeticCone_odd_riemannRoch_of_le_threeHundredSixtyTwoThousandths` | ArithmeticCastelnuovoSeveri/RiemannRochForZAndTheReflectedPrimePolarLedger.lean |
| `riemannHypothesis_iff_encard_rightZeros_lt_two`, `even_ncard_rightZeros` | ArithmeticOrientationGeometry/TheIndexExit.lean:477, :461 |
| `exists_cofactorGram_limit` | ArithmeticDefectRigidity/CountableCofactorCovariancesHaveACommonLimit.lean:208 |
| `abs_receiver_word_sub_dilation_le` | ArithmeticDefectRigidity/CofactorSuccessorWordsHaveABoundaryCost.lean:102 |
| `riemannHypothesis_iff_nonneg_and_no_hardyWeight` | ArithmeticCriticalityTheory/OddFormCriticality.lean |
| `riemannHypothesis_iff_isLeast_primeRate` | ArithmeticCriticalityTheory/JumpRateCriticality.lean:163 |
| `two_mul_primePowerShift_le_stripSurplus` | ArithmeticIncidencePositivity/SharpMicroFoldHarnack.lean:746 |
| `selectivity_class_I_beurling_universal_laws`, `selectivity_class_III_bezout_successor_selective_laws`, `complete_signed_interior_energy_and_vaughan_calibration` | TransHorizonIncidenceMechanics/CompleteSignedTransHorizonEnergyAndTransferSelectivity.lean |
| `riemannHypothesis_iff_forall_ne_zero_exists_longSawtooth_tail_antiAlignment_gap`, `plantedEulerKernel_collar_and_finiteness_obstruction` | TransHorizonIncidenceMechanics/OscillatingProbeSourceEstimatesEnergyGapAndCollarLimitations.lean |
| `receiverBounded_moebius_and_liouville_of_vonMangoldtConv_partialSum_rpow` | TransHorizonIncidenceMechanics/SubHalfDampingPartialPoleSumsAndLogarithmicMomentIndexLaws.lean |
| `tendsto_probeEnergy_half_div_log` | TransHorizonIncidenceMechanics/TheProbeReceiverEnergyMeasuresTheModulusOfZeta.lean |
| `periodCovariance_eq_iff_exists_scaledSelbergRow` | BezoutValuationIncidence/CompletePeriodQuadraticFormsSignInvarianceAndTransHorizonSeparation.lean |
| `moebiusPowerWindowSaving_iff` | BezoutValuationIncidence/ShortWindowMoebiusSavingIsTheQuasiRiemannHypothesis.lean |
| `exists_receiver_le_on_vinogradovKorobovBand` | BezoutValuationIncidence/ReceiverBoundedInTheVinogradovKorobovBand.lean |
| `parityPair_separated_on_vinogradovKorobovBand` | BezoutValuationIncidence/ParityPairSeparatedOnTheVinogradovKorobovBand.lean |
| `shiftedPair_and_vkBand_selectivity` | BezoutValuationIncidence/ParityPairAndSelectivitySynthesis.lean |
| `exists_criticalZero_linear_dualResidual_floor` | BezoutValuationIncidence/PowerDampedResidualHasLinearCusp.lean |
| `receiverDampingRate_eq_zetaZeroAbscissa_sub_half` | RHTower/AdmissionBelowHalfDampingAboveTheZeroWidth.lean |
| `zeta_weil_near_radical_sharp_count` | RHTower/SharpWeilNearRadicalCount.lean |
| `guthMaynardLargeValuesBound_holds` | RHTower/Sieve/GuthMaynardTheoremOneOne.lean:184 |
| `exists_zeroHeightBox_ncard_le_thirty_thirteenths` | RHTower/ZetaZeroDensityThirtyThirteenths.lean:172 |
| `Stepanov.exists_nonzero_solution` | RHTower/StepanovCount.lean:54 |
| `riemannHypothesis_of_zetaStronglyRecurrent` | RHTower/ZetaStrongRecurrenceReceiver.lean:329 |

**Not verified (stated as proposals, not facts):**
- the module observation of §2.1 (elementary, not formalized);
- the exponent law (A3);
- all of Mechanisms B and C;
- that the white-noise kernel violates antipodality.
