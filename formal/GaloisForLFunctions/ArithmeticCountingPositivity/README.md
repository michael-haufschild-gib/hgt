# Arithmetic Counting Positivity (ACountP)

Namespace `GaloisForLFunctions.ArithmeticCountingPositivity`; umbrella `ArithmeticCountingPositivity.lean`.

**Question.** Produce positivity from arithmetic **counts**, with multiplicativity selecting the untwisted source. A positive
representation assumed at the outset does not solve this; neither does an identity transferring an unproved sign. Over $\mathbb F_q$ an
independently proved point count supplies the Hodge inequality. Over $\mathbb Z$ the complete Weil form has an exact arithmetic
description but no proved sign. What must a count retain to produce it — arithmetic incidence, signed correlations, the
archimedean term, the two poles?

---

## 1. Place in the research

The explicit formula splits the complete form into Gamma, poles and prime source. Majorants discard what distinguishes $\Lambda$ from
its Liouville twist; multiplicativity alone permits that twist. A successful count must use a compatibility that changes under
twisting and prove an inequality from it. Starting point: the discrete multiplicative walk has sharp harmonic-hyperplane gap
$2\log2$, the Liouville twin gap $0$ (RAPT/SMAP). Open passage: discrete energy → continuous overlapping sources → source-complete exhaustion.

ACountP owns **independent counting constructions** and exact tests of what information their positivity preserves.

| Programme | Interface |
|---|---|
| ArithmeticCastelnuovoSeveri | Intersection theory, effectivity, section counts, finite-field calibration |
| ArithmeticOrientationGeometry | Orbit correlation, Toeplitz index, finite-support receivers |
| ArithmeticCorrespondencePositivity | Sparse annihilators; lattice requirement of Stepanov's mechanism |
| SelectiveMultiscaleArithmeticPositivity | Selective discrete margin; multiscale transfer |
| RenormalizedArithmeticPotentialTheory | Sharp multiplicative Poincaré inequality, prime-defect identity, finite-prime gauges |
| MultiplicativePositivityGeometry | Arithmetic positive definiteness on the boundary and its interior limits |
| ArithmeticIncidencePositivity | Prime incidence, atomic forms, surplus allocation |
| SignedArithmeticHodgeTheory, ArithmeticIndexDescent | Complete source coordinates; uniform index bounds for prime layers; first-layer obstruction |
| BezoutValuationIncidence | Divisor incidence and correlations unavailable in Beurling systems |
| ArithmeticEffectivityTheory | Counting as effectivity; Stepanov over $\mathbb Z$ reaches only the base |

---

## 2. Objects and language

| Object | Information retained |
|---|---|
| Complete Weil form $W=\Gamma+\text{poles}-P$ | Both poles, every prime power, all mixed entries, multiplicities |
| Twisted forms $W_\lambda$ | Which steps distinguish the actual source from bounded twins |
| Multiplicative incidence, walk energy | Divisibility, prime-power edges, harmonic mass, signed edge correlations |
| Sign gauge $\omega$, harmonic count $S_N=\sum\omega(n)/n$, $H_N=\sum1/n$, angle $c_N=S_N/H_N$ | Correlation of a gauge with the pole |
| Prime parity gauge $\omega_p(n)=(-1)^{v_p(n)}$ | The simplest non-Liouville completely multiplicative flip |
| Auxiliary sections | Explicit construction, vanishing orders, dimension, complexity |
| Orbit Toeplitz forms; signature counts | Every index difference; positive/negative indices, trace, Frobenius energy |
| Exhaustions | Source maps, domains, growing parameters, topology, uniform errors |

A **selective inequality** fails for a specified bounded twin; a **parity-breaking input** changes under Liouville twisting (necessary,
not sufficient). A **counting producer** constructs what it counts and proves its bound independently of the output sign; a
**receiver** translates a supplied bound into a sign. An **arithmetic Herglotz theorem** would produce Toeplitz positivity for a
prime-generated form from arithmetic. Finite incidence counts are exact; a count supplying the Weil sign must reach square-root
precision — do not conflate the two.

---

## 3. Mechanisms

1. **Pole-angle transfer.** On the harmonic hyperplane $\operatorname{Var}_{1/n}(\sqrt n\,\omega(n)x_n)\ge c_N^2\sum x_n^2$ (attained by the gauged pole's projection); with the
   sharp multiplicative Poincaré inequality, eventually and **uniformly over all sign gauges** (even $N$-dependent ones):
   $P_N(\omega x)\le(\log N-\gamma-(2\log2)c_N^2+\varepsilon)\sum x_n^2$. A signed harmonic count pays a prime gap.
2. **Prime parity pairing (exact counting producer).** Negative coordinates of $\omega_p$ are $p$ times positive ones:
   $p(H_N-S_N)=H_{\lfloor N/p\rfloor}+S_{\lfloor N/p\rfloor}$; hence $S_N/H_N\ge(p-1)/(p+1)$, with excess $(p+1)S_N-(p-1)H_N=\sum_{N/p<n\le N}(1+\omega_p(n))/n\in[0,2(1+\log p)]$, so
   $c_N\to(p-1)/(p+1)$ and the unconditional gap is $2\log2((p-1)/(p+1))^2$ (at $p=2$: $2\log2/9$; Liouville: 0).
3. **Sparse flips keep near-maximal gaps.** $\sum_{p\mid n,n\le N}1/n=H_{\lfloor N/p\rfloor}/p$: a single flip at a large prime has gap $\ge a$ for any $a<2\log2$, is completely
   multiplicative and keeps polar matching.
4. **Full-cone uniqueness kills them.** A full-Weil-positive weight equals $\Lambda$ on $n\ge2$; $\omega_p\Lambda$ has $-\log p$ at $p$, so each has a compact $C^2$ test with
   negative complete Weil functional (Gamma, poles, all prime powers retained).
5. **Ramanujan coordinates of prime parity.** Divisibility incidence writes the conductor-$m$ harmonic count as a finite Möbius sum of
   decimated parity counts $S_{\lfloor N/d\rfloor}$ with bounded boundary errors; normalized by $H_N$ it tends to
   $\frac{p-1}{p+1}\sum_{d\mid m}\mu(m/d)\,\omega_p(d)$, hence to 0 for every conductor $m\ge2$ coprime to $p$. A prime flip is visible only at
   conductors divisible by $p$.
6. **Counts determine actual eigenline coordinates.** Normalize both the parity constraint and the conductor-$m$ Ramanujan mode by
   $\sqrt{H_N}$. The mixed count is their exact inner product. The Ramanujan residual tends to zero, so projection onto its isolated
   prime eigenline changes that inner product by $o(1)$. The squared coordinate of the unit parity constraint therefore tends to
   $\left(\frac{p-1}{p+1}\frac{\sum_{d\mid m}\mu(m/d)\omega_p(d)}{\sqrt{\varphi(m)}}\right)^2$.
   This identifies a multiplicative constraint inside the actual finite spectrum; it does not bound its full orthogonal complement.
7. **Finite-prime density.** For any finite set $F$ of primes,
   $S_F(N)=c_FH_N+O_F(1)$ with $c_F=\prod_{p\in F}(p-1)/(p+1)>0$. Adding a prime gives an exact divisibility recurrence;
   the bounded harmonic shell and contraction under $N\mapsto\lfloor N/p\rfloor$ control its error. The resulting prime gap is
   $(2\log2)c_F^2$. Both the error constant and the eventual horizon retain their dependence on $F$.
8. **Finite-prime exhaustion separates quantifiers.** Flipping all primes below $Q$ agrees exactly with Liouville at every integer
   below $Q$. Each fixed cutoff is multiplicative, polar matched and positively gapped. Yet no positive gap holds with one horizon
   bound uniform in all sufficiently large cutoffs: choosing $Q>N$ would give the forbidden positive Liouville gap at horizon $N$.
9. **Large prime flips attain the maximal gap.** For every prime $p\ge11$ the flip $\omega_p$ has hyperplane gap exactly $2\log2$,
   the maximum over all sign gauges. In the two-scale decomposition of $[1,N]$ (smooth parts below a horizon $X$, rough fibres),
   the flipped pole $\omega_p(n)/\sqrt n$ differs from the pole only inside the $p$-ladders of the smooth box. Efron–Stein on the box,
   keeping the $p$-ladders separate, pays the within-$p$-fibre variance with the ladder constant $\log p\,W_p(X)\ge\log p(1+1/p)$
   rather than $2\log2$; the pairing of $\omega_p$ with a mean-zero function is controlled by that variance with constant
   $(1-c_p^2)W_p(X)$, $c_p=(p-1)/(p+1)$. The rotation of the pole therefore costs $2\log2(1-c_p^2)$ against an excess
   $c_p^2(\log p-2\log2)$, and $4p\cdot2\log2<(p-1)^2(\log p-2\log2)$ holds from $p=11$ on. The halo above $X$ and the variation of
   the rough masses below $X$ are paid by the walk energy and vanish with the horizon. Consequence: the exact discrete margin, even at
   its maximum and together with complete multiplicativity and polar matching, does not select $\Lambda$.
10. **Eleven is the exact single-prime cutoff.** Every hyperplane gap of $\omega_p$ is at most
   $p\log p/(p+3)$. The ground and conductor-$p$ eigenlines have limiting squared parity coordinates
   $c_p^2$ and $4c_p^2/(p-1)$; their exactly constrained plane gives this upper bound. For $p<11$ it is
   strictly below $2\log2$, since $p\le7$ and $7^7<2^{20}$. Together with the large-prime lower bound,
   $\omega_p$ attains the maximal gap if and only if $p\ge11$.
11. **A complete parity expansion with uniform error.** Let $c_p=(p-1)/(p+1)$ and truncate the Ramanujan tower at $p^K$:
   $z_{K,N}=c_pu_{1,N}+\sum_{k=1}^K(2c_p(-1)^k/\sqrt{\varphi(p^k)})u_{p^k,N}$.
   Its arithmetic profile equals $\omega_p(n)$ outside $p^K\mid n$, and equals $c_p(-1)^K$ on that fibre. Therefore
   $\|v_{p,N}-z_{K,N}\|^2=((1+c_p^2)H_{\lfloor N/p^K\rfloor}-2c_pS_p(\lfloor N/p^K\rfloor))/(p^KH_N)
   \le4p/((p+1)^2p^K)$ for every $N\ge1$. The bound is attained as $N\to\infty$;
   the squared coefficients sum to $1-4p/((p+1)^2p^K)$ and exhaust mass one. Individual spectral coordinates now assemble
   into a finite arithmetic approximation with an error uniform over the integer horizon.
12. **Cofinite flips expose the exhaustion topology.** Put $\eta_F=\lambda\omega_F$. Removing one prime sign gives
   $pS_{\eta_{F\cup\{p\}}}(N)-S_{\eta_{F\cup\{p\}}}(\lfloor N/p\rfloor)
   =pS_{\eta_F}(N)+S_{\eta_F}(\lfloor N/p\rfloor)$. The elementary Liouville square count and induction give
   $|S_{\eta_F}(N)|\le2/c_F$ for every horizon. Consequently every cofinite flip has greatest hyperplane gap zero.
   The harmonic squared distance $D_F(N)=H_N^{-1}\sum_{n\le N}(\omega_F(n)-\lambda(n))^2/n$ satisfies
   $D_F(N)=2-2S_{\eta_F}(N)/H_N$ and $|D_F(N)-2|\le4/(c_FH_N)$. Thus its horizon limit is two at every
   fixed prime cutoff, while its prime-cutoff limit is zero at every fixed horizon. Conversely, the zero-gap cofinite flips
   stabilize pointwise to the untwisted sign, whose greatest gap is $2\log2$.
13. **The counted tower has an exact secular root.** Its coefficients $a_0=c_p$ and
   $a_k=2c_p(-1)^k/\sqrt{\varphi(p^k)}$ have squared sum one. With $D_0=0$ and
   $D_k=k\log p+\log p/(p-1)$, the series $\sum_{k\ge0}a_k^2/(D_k-s)$ has a unique zero
   $\alpha_p$ in $(0,D_1)$. The higher tower has positive mass, so
   $\alpha_p<p\log p/(p+3)$. Identification with the actual constrained prime-matrix gap uses
   the finite constraint criterion and control of all omitted eigenlines.
14. **Reciprocal mass decides the finite constraint.** For a diagonal form with one negative weight
   $-b$ and positive weights $w_i$, the constraint $cx_0+\sum a_ix_i=0$, $c\ne0$, removes the
   negative direction exactly when $b\sum a_i^2/w_i\le c^2$. Weighted Cauchy–Schwarz proves
   sufficiency; $x_i=a_i/w_i$ proves necessity. A packet omitting only weights at least $\eta>0$
   loses at most its omitted squared coordinate mass divided by $\eta$. Orthonormal expansion gives
   the same exact criterion for the actual Hermitian form. Eventual packet bounds with convergent
   lower and upper limits pass to the whole scalar expression without a uniform packet horizon.
15. **The tower determines the full actual resolvent.** Let $E_{i,N}=\log N-\lambda_{i,N}-\gamma$,
   and $b_{i,N}=\langle v_{p,N},e_{i,N}\rangle$ for an actual orthonormal prime eigenbasis.
   For every $0<s<2\log2$, $\sum_i b_{i,N}^2/(E_{i,N}-s)$ converges to
   $\sum_{k\ge0}a_k^2/(D_k-s)$. A threshold between $s$ and $2\log2$ contains only the ground
   eventually. Every omitted reciprocal denominator is therefore bounded below by one fixed
   positive number. The selected tower mass exhausts one, controlling all remaining actual
   eigenlines, including those whose energies diverge. This transfers the whole scalar reading
   from counted arithmetic coordinates to the finite prime matrix.
16. **Exact single-prime gaps.** The greatest hyperplane gap of $\omega_p$ is
   $\delta_p=\min(2\log2,\alpha_p)$. Below the first global excitation, the finite constrained
   form is nonnegative exactly when its full reciprocal reading is nonpositive. Resolvent
   convergence and the sign on either side of the unique root prove both attainment and the
   necessary bound. Thus every real gap is classified by $g\le\delta_p$; for $p=2,3,5,7$,
   $\delta_p=\alpha_p$, characterized by
   $\sum_{k\ge1}4/(\varphi(p^k)(k\log p+\log p/(p-1)-\alpha_p))=1/\alpha_p$.
   Every prime-flip gap is strictly below $p\log p/(p+3)$.
17. **Finite prime sets have unit conductor mass.** Put $b_F=\mu*\omega_F$ on positive integers.
   Its local value at $p^k$, $k\ge1$, is $2(-1)^k$ for $p\in F$ and zero otherwise. Hence
   $b_F(m)^2=4^{\omega(m)}$ when every prime factor of $m$ belongs to $F$, and zero elsewhere.
   The normalized coefficients $a_F(m)=c_Fb_F(m)/\sqrt{\varphi(m)}$ satisfy
   $\sum_{m\ge1}a_F(m)^2=1$: the finite Euler product has local factors
   $1+4p/(p-1)^2=(p+1)^2/(p-1)^2$, exactly cancelled by $c_F^2$.
   All prime-power tails are included. This gives the total mass needed for a joint resolvent
   transfer; identifying the finite-set coordinates on actual eigenlines is a separate step.
18. **Finite-set counts determine actual eigenline coordinates.** The mixed harmonic count is
   $\sum_{d\mid m}\mu(m/d)\omega_F(d)S_F(\lfloor N/d\rfloor)$. Its normalized limit is
   $c_Fb_F(m)$, so the inner product with the normalized Ramanujan mode tends to $a_F(m)$.
   The common quasimode residual and isolated spectral window then give an actual eigenline
   sequence with energy tending to the conductor energy and squared constraint coordinate
   tending to $a_F(m)^2$. This includes every mixed conductor. Together with unit mass it
   supplies the arithmetic inputs for controlling all omitted lines in the joint resolvent.

19. **The joint resolvent retains every spectral direction.** For every finite prime set $F$ and
   $0<s<2\log2$, the full actual reciprocal reading tends to
   $c_F^2\Phi_F(s)$, where $\Phi_F(s)=-1/s+\sum_{m\ge2}w_F(m)/(D_m-s)$.
   Distinct conductor energies separate each finite packet, without an ordering by conductor size.
   The unique ground count bounds all omitted denominators below by a fixed positive number;
   unit conductor mass then makes the omitted contribution vanish. The normalized function is
   strictly increasing throughout the physical first gap, including for the empty prime set.

20. **Exact finite-prime gap criterion and inclusion law.** Every real gap is classified by
   $g\le2\log2$ and $\Phi_F(s)\le0$ for every $0<s<g$. Necessity passes the actual finite
   reciprocal sign to its arithmetic limit. For sufficiency, a test value slightly above $s$
   makes the limit strictly negative, giving an eventual finite inequality. The epsilon in
   the gap definition includes the endpoint: the greatest gap $\delta_F$ is attained and
   $(2\log2)c_F^2\le\delta_F\le2\log2$. Enlarging $F$ adds supported conductor weights,
   increasing $\Phi_F$ and decreasing $\delta_F$. These assertions include the empty set.

21. **Interior roots and the maximal plateau.** The same summable denominator bound makes
   $\Phi_F$ continuous on $(0,2\log2)$. If the greatest gap is below the ceiling, then
   $\Phi_F(\delta_F)=0$; every zero in this interval equals $\delta_F$. For proper inclusion
   $F\subsetneq G$, a newly flipped prime contributes a strictly positive conductor term,
   so $\Phi_F(s)<\Phi_G(s)$. Consequently
   $\delta_G<\delta_F$ exactly when $\delta_G<2\log2$: equal gaps under proper inclusion
   occur only at the maximum. This completes the finite-set classification without introducing
   secular roots above the physically relevant ceiling.

22. **Joint gaps vanish above every fixed prime cutoff.** Let $F_{B,Q}$ contain the primes
   $B<p\le Q$. Then $\delta_{F_{B,Q}}\to0$, although each finite-stage greatest gap is
   positive. The progression $B!(n+2)+1$ supplies conductors supported above $B$;
   its reciprocal logarithmic mass diverges by condensation. Since
   $w_F(m)/(D_m-s)\ge1/(2m\log m)$ for supported $m\ge2$ and $0<s<2\log2$,
   a sufficiently large finite packet contradicts any fixed positive secular gap.
   Inclusion makes the gaps decrease. In particular, arbitrarily large primes can each
   have maximal singleton gap while their joint greatest gap is arbitrarily small.
   This uses fixed finite packets, with no exchange of horizon and prime-cutoff limits.

23. **One fixed dyadic probe selects finite prime signs.** Let $\delta_2$ be the greatest gap
   of dyadic parity. Among finite prime flips, the two lower bounds
   $\operatorname{Gap}(\omega_F)\ge2\log2$ and
   $\operatorname{Gap}(\omega_2\omega_F)\ge\delta_2$ hold together exactly when $F$ is empty.
   The first excludes $2\in F$, since inclusion would force a gap at most
   $\delta_2<2\log2$. For every remaining nonempty $F$, the dyadic toggle inserts two,
   and strict inclusion makes its gap smaller than $\delta_2$. Both readings are attained
   for the untwisted sign. This selects within the finite-prime family using a fixed
   additional arithmetic probe; it does not assert selection among arbitrary weights.

24. **Conductor mass controls gap loss and probe precision.** For $F\subseteq G$, the added
   normalized weight has total mass $\Delta=c_G^{-2}-c_F^{-2}\ge0$. Its full secular
   increment is at most $\Delta/(g_0-s)$, where $g_0=2\log2$. The reciprocal ground term gives
   $(\delta_F-\delta_G)(g_0-\delta_G)\le\delta_G\delta_F\Delta$, hence
   $(\delta_F-\delta_G)^2\le g_0^2\Delta$. The proof includes the maximal plateau by taking
   a reciprocal limit from below, with no continuity assertion at the excitation itself.
   Inserting a prime gives squared loss at most $16g_0^2/(pc_F^2)$. At the interior dyadic
   calibration the stronger product bound gives loss at most
   $16g_0^2/(pc_2^2(g_0-\delta_2))$. Thus arbitrarily remote maximal-gap single-prime flips
   have a strictly smaller dyadic response, yet approach the untwisted reading at order
   $1/p$. Exact finite-prime selection has no fixed positive tolerance.

25. **The counted first energy moment bounds the gap.** Dual numbers retain mass and
   energy in a finite Euler product, giving
   $M_F=\sum_m a_F(m)^2D_m=\sum_{p\in F}4p\log p/(p^2-1)$.
   Weighted Cauchy-Schwarz in the full secular series gives
   $\delta_F\le c_F^2M_F/(1-c_F^2)$ for nonempty $F$.
   Combined with $g_0c_F^2\le\delta_F$, this relates both sides of the attained
   gap to arithmetic counts without assuming full-vector energy convergence.

26. **Quantitative collapse above every fixed prime cutoff.** For
   $F_{B,Q}=\{p\text{ prime}:B<p\le Q\}$, elementary Mertens bounds give
   $c_{F_{B,Q}}\le D_B/(\log Q)^2$ and
   $M_{F_{B,Q}}\le(16/3)(\log Q+C_1)$, where
   $D_B=\exp(2(C_2+1+\sum_{p\le B}1/p))$ is explicit.
   Eventually $c_{F_{B,Q}}\le1/2$, so the moment inequality pays
   $\delta_{F_{B,Q}}\le(64/3)D_B^2/(\log Q)^3$.
   For $B\ge10$, every constituent single-prime flip is maximal while this
   positive joint gap decays. The prime-cutoff limit is quantified directly
   in the attained gaps, with no exchange of integer-horizon limits.

27. **Divisibility counts control genuinely infinite prime patterns.** Let
   $\omega_P$ flip any set $P$ of primes, and put
   $\eta_P(N)=\sum_{p\le N,\,p\in P}1/p$. The actual gauge agrees with its
   finite prime cutoff throughout $[1,N]$. Counting multiples gives
   $S_P(N)/H_N\ge1-2\eta_P(N)$, and the normalized squared harmonic error
   of cutting off at $Q$ is at most $4\eta_{P\cap(Q,\infty)}(N)$.
   Both bounds are uniform in the integer horizon and assume no limiting
   mean. An increasing prime sequence bounded below geometrically has
   arbitrarily small reciprocal mass. Its infinite sign therefore retains
   every prescribed gap below $2\log2$, with the gap paid directly by the
   uniform count. Pointwise convergence alone is not used to transfer it.

28. **Prime stripping has an additive cost independent of the residual sign.**
   If a multiplicative sign $\omega$ is unflipped on the finite prime set $F$,
   then $|S_{\omega_F\omega}(N)-c_FS_\omega(N)|\le K_F$, where
   $K_F=\sum_{p\in F}2(1+\log p)/(p+1)$. The exact divisibility recurrence
   expresses each one-prime error as two harmonic shells. Their costs add
   because each local density factor lies in $(0,1]$. If $F\subseteq[1,Q]$,
   elementary Mertens counting gives
   $K_F\le2(1+1/\log2)(\log Q+C_1)$. Thus the error is explicit and uniform
   in the integer horizon and every remaining, possibly infinite, prime pattern.

29. **Every prime pattern has its Euler-product harmonic mean.** For any
   prime set $P$, let $c_Q=\prod_{p\in P,\,p\le Q}(p-1)/(p+1)$ and
   $c=\inf_Qc_Q$. Then $0\le c\le1$, $c_Q\to c$, and
   $S_P(N)/H_N\to c$ without any summability or density hypothesis.
   If $c=0$, finite prime stripping squeezes the full correlation between
   $\pm c_Q$ with a vanishing fixed-cutoff error. If $c>0$, the finite
   product inequality $c_F(1+\sum_{p\in F}1/p)\le1$ bounds residual
   reciprocal mass by $c_Q/c-1$. Divisibility counting and stripping then
   squeeze both correlation limits to $c$. The actual sign retains gap
   $(2\log2)c^2$. This establishes a paid lower bound; zero density alone
   does not determine the greatest gap.

30. **Positive density is exactly harmonic cutoff completeness.** The residual
   prime pattern beyond $Q$ has density $c/c_Q$. Its multiplicative partition
   gives the exact squared harmonic cutoff distance
   $D(P,Q,N)=2(1-C_{P\setminus[1,Q]}(N))$ for $N\ge1$, hence
   $D(P,Q,N)\to2(1-c/c_Q)$ at fixed $Q$. Finite prime cutoffs approximate
   the full sign in eventual harmonic mean square exactly when $c>0$.
   If $c=0$, every fixed cutoff stays at limiting squared distance two.
   In the reverse order, $Q\ge N$ makes the distance exactly zero.
   Thus both orders of exhaustion are explicit; this does not transfer an
   unbounded quadratic form solely from harmonic norm approximation.

---

## 4. Pillar theorems

1. **Pole-angle transfer** (`harmonicCorrelation_sq_mul_mass_le_variance`, `gaugeWitness_attains_variance_bound`,
   `eventually_prime_gap_ge_squared_correlation`).
2. **Prime parity pairing and its paid gap** (`prime_parity_pairing`, `prime_parity_boundary_bounds`, `primeFlip_harmonicCorrelation_tendsto`,
   `primeFlip_hasHyperplaneGap`, `two_adic_parity_has_gap_but_liouville_does_not`).
3. **A positive gap is weaker than selection** (`harmonicMass_multiples`, `every_submaximal_gap_has_a_nontrivial_multiplicative_twin`).
4. **Near-maximal gaps do not force Weil positivity**: no fixed gap threshold below $2\log2$, even with multiplicativity and polar
   matching, forces complete positivity (`primeFlip_exists_negative_complete_test`, `near_maximal_gaps_do_not_force_weil_positivity`).
5. **Harmonic Ramanujan coordinates of prime parity** (`gaugeHarmonicSum_divisibility`, `primeParityRamanujanSum_tendsto`,
   `primeParityRamanujanSum_tendsto_zero`).
6. **Counting-to-eigenline bridge** (`primeParityHorizonVector_inner`, `tendsto_primeParityWindowCoordinateSq`,
   `exists_primeParity_eigenline_coordinates`): exact harmonic counts determine orientation-independent coordinates on actual simple
   prime eigenlines.
7. **Positive density for every finite set of flips** (`finiteFlip_harmonic_recurrence`, `finiteFlip_harmonic_error_bounded`,
   `finiteFlip_harmonicCorrelation_tendsto`, `finiteFlip_hasHyperplaneGap`).
8. **Exact exhaustion obstruction with positive finite stages** (`finitePrimeExhaustion_eventually_eq_liouville`,
   `finitePrimeExhaustion_each_stage_matched_positive`, `finitePrimeExhaustion_no_uniform_positive_gap`).
9. **The maximal gap is not rigid** (`boxGap_mul_boxVar_add_le`, `sum_flip_mul_sq_le`, `eventually_primeFlip_poleDefect_ge`,
   `primeFlip_hasHyperplaneGap_two_mul_log_two`, `isGreatest_primeFlip_hyperplaneGap`, `maximal_gap_does_not_select_the_source`):
   every prime $p\ge11$ gives a completely multiplicative, polar-matched sign twin with the greatest hyperplane gap $2\log2$,
   Weil coefficients of the size of $\Lambda$, and a negative complete Weil test.
10. **Exact threshold and small-prime obstruction** (`primeFlip_hyperplaneGap_le_prime_log_div`,
   `smallPrimeFlip_has_positive_but_not_maximal_gap`, `primeFlip_hasHyperplaneGap_two_mul_log_two_iff`):
   every single-prime flip has gap at most $p\log p/(p+3)$, and maximal-gap attainment is equivalent to $p\ge11$.
11. **Uniform Ramanujan tower exhaustion** (`primeParityTowerProfile_value`, `primeParityTowerVector_eq_ramanujan`,
   `primeParityTower_error_sq_eq`, `primeParityTower_error_sq_le`, `tendsto_primeParityTower_error_sq`,
   `primeParityTower_coefficient_mass`, `tendsto_primeParityTower_coefficient_mass`, `primeParityTower_uniform_exhaustion`).
   Exact divisibility counts supply the uniform norm bound and its sharp constant.
12. **Cofinite zero gaps and distinct harmonic limits** (`cofiniteFlip_harmonic_recurrence`,
   `cofiniteFlip_harmonicSum_abs_le`, `isGreatest_cofiniteFlip_hyperplaneGap`,
   `finiteFlipLiouvilleDistanceSq_error_le`, `finitePrimeExhaustion_two_harmonic_limits`,
   `cofinitePrimeExhaustion_eventually_eq_one`). A bounded arithmetic count gives an exact gap classification
   and identifies the harmonic distance discarded by pointwise convergence.
13. **Exact arithmetic secular data** (`primeParityTowerEnergy_eq`,
   `primeParityTowerCoefficient_sq_succ`, `hasSum_primeParityTowerCoefficient_sq`,
   `primeParitySecularRoot_spec`, `primeParitySecularRoot_unique`). The existing infinite secular
   theory applies to the counted parity tower and gives the root used in the exact gap classification.
14. **Finite constraint and exhaustion tools** (`diagonal_hyperplane_nonneg_iff`,
   `reciprocal_mass_le_packet_add_tail`, `exists_negative_diagonal_on_hyperplane`,
   `one_negative_diagonal_nonneg_iff`, `hermitian_hyperplane_bound_iff`,
   `tendsto_of_eventual_packet_bounds`). These classical criteria retain every spectral direction
   and expose the precise tail estimate needed for arithmetic transfer.
15. **Actual resolvent convergence** (`primeParityTowerCoefficient_eq_moebius`,
   `exists_primeParity_tower_eigenline`, `eventually_fullPrime_ground_count_one`,
   `primeParityTowerEnergy_strictMono`, `primeParityTowerEnergy_ge_excitation`,
   `tendsto_primeParityFiniteResolvent`). Every unselected eigenline is included in the remainder bound.
16. **Complete single-prime classification** (`primeFlip_hasHyperplaneGap_min_secularRoot`,
   `primeFlip_hyperplaneGap_le_secularRoot`, `isGreatest_primeFlip_hyperplaneGap_min_secularRoot`,
   `primeFlip_hasHyperplaneGap_iff_le_min_secularRoot`,
   `primeParitySecularRoot_lt_two_mul_log_two_iff`,
   `isGreatest_smallPrimeFlip_hyperplaneGap_secularRoot`,
   `primeFlip_hyperplaneGap_lt_prime_log_div`, `hasSum_primeParitySecularRoot_reciprocals`).
   The counted series determines the exact constrained gap of the actual prime matrices.
17. **Exact mass for arbitrary finite prime sets** (`finiteFlipMobius_isMultiplicative`,
   `finiteFlipMobius_eq_divisor_sum`, `finiteFlipMobius_prime_pow`,
   `finiteFlipMobius_sq_eq_prod`, `finiteFlipSpectralWeight_eq`,
   `hasSum_finiteFlipSpectralWeight_supported`, `finiteFlipConductorCoefficient_sq`,
   `hasSum_finiteFlipConductorCoefficient_sq`). The supported conductor weights and their
   summability are proved directly from local geometric counts and the finite Euler product.
18. **Actual coordinates for every finite prime set** (`finiteFlipRamanujanSum_eq`,
   `finiteFlipRamanujanSum_tendsto`, `finiteFlipHorizonVector_norm_sq`,
   `finiteFlipHorizonVector_inner`, `tendsto_finiteFlipHorizonVector_inner`,
   `tendsto_finiteFlipWindowCoordinateSq`, `exists_finiteFlip_eigenline_coordinates`,
   `exists_finiteFlip_conductor_eigenline`). Every positive conductor has its counted
   squared mass on an actual prime eigenline; the horizon limit is for fixed F and m.

19. **Full joint-prime resolvent and strict increase** (`summable_finiteFlipSecularTail`,
   `hasSum_finiteFlipSecularSeries`, `tendsto_finiteFlipFiniteResolvent`,
   `finiteFlipSecular_strictMonoOn`). Summability and unit counted mass control the entire actual
   reading below the first excitation; no unselected eigenline is discarded.

20. **Attained finite-prime gaps and inclusion comparison** (`finiteFlip_hasHyperplaneGap_iff_secular`,
   `isGreatest_finiteFlip_hyperplaneGap`, `finiteFlip_hasHyperplaneGap_iff_le_greatestGap`,
   `finiteFlipGreatestGap_bounds`, `finiteFlipGreatestGap_pos`, `finiteFlipSpectralWeight_mono`,
   `finiteFlipSecular_mono`, `finiteFlipGreatestGap_antitone`). The explicit counted series
   classifies the exact uniform gap, including its endpoint and arbitrary joint flips.

21. **Interior-root classification and strict inclusion law** (`finiteFlipSecular_continuousAt`,
   `finiteFlipSecular_greatestGap_eq_zero`, `finiteFlipGreatestGap_eq_iff_secular_zero`,
   `finiteFlipSecular_lt_of_ssubset`, `finiteFlipGreatestGap_lt_iff_of_ssubset`). Every submaximal
   finite-set gap is the unique interior arithmetic root; equality under proper inclusion is
   confined to the maximal plateau.

22. **Prime-tail collapse despite individually maximal constituents**
   (`not_summable_progressionReciprocalLog`, `tendsto_sum_progressionReciprocalLog_atTop`,
   `exists_primeTailCutoff_gap_lt`, `tendsto_primeTailGreatestGap_zero`,
   `exists_maximal_prime_flips_with_small_joint_gap`). An explicit rough progression
   supplies enough positive conductor mass to force the joint greatest gaps to zero.

23. **Exact selection by a fixed dyadic probe** (`finiteFlip_dyadicPrimeToggle`,
   `dyadicFlipGreatestGap_lt_ceiling`, `finiteFlip_two_gap_selection`). The maximal original
   gap and the untwisted dyadic-response gap are jointly rigid among finite prime flips.

24. **Quantitative gap stability and exact probe precision** (`hasSum_finiteFlipSpectralWeight`,
   `finiteFlipSecular_increment_le`, `finiteFlipGreatestGap_loss_mul_ceiling_le`,
   `finiteFlipGreatestGap_loss_sq_le`, `finiteFlipGreatestGap_insert_loss_sq_le`,
   `dyadicGreatestGap_prime_response_loss_le`,
   `exists_maximal_flip_with_almost_unchanged_dyadic_gap`). Total counted conductor mass
   pays a global perturbation bound and the sharp qualitative tolerance obstruction.

25. **Exact conductor moment and greatest-gap upper bound**
   (`hasSum_finiteFlipConductorEnergy`, `finiteFlipHarmonicDensity_lt_one`,
   `finiteFlipGreatestGap_le_energyMoment`). A dual-number Euler product evaluates
   the first moment; weighted Cauchy-Schwarz converts it to a gap bound.

26. **Explicit inverse-log-cube prime-tail gap bound**
   (`finiteFlipHarmonicDensity_primeTail_le`,
   `finiteFlipConductorEnergyMoment_primeTail_le`,
   `eventually_primeTailGreatestGap_le_inverse_log_cube`). Elementary prime
   counts bound density and mean energy, and hence the actual greatest gap.

27. **Uniform infinite-prime counting and sparse infinite gaps**
   (`primeSetFlip_eq_finiteFlip_of_le`, `primeSetFlip_harmonicCorrelation_ge`,
   `primeSetFlip_cutoff_distance_sq_le`,
   `exists_infinite_primes_bounded_reciprocal_mass`,
   `exists_infinite_prime_flips_with_near_maximal_gap`). Exact finite-horizon
   counts provide an explicit truncation error and actual infinite-family gaps.

28. **Additive uniform prime stripping** (`finiteFlip_harmonic_stripping_error`,
   `finiteFlip_harmonic_stripping_error_le_log_cutoff`). Two harmonic shells
   per prime pay an explicit error uniform in the horizon and residual sign.

29. **All-pattern harmonic mean and paid gap** (`tendsto_primeSetCutoff_density`,
   `primeSetHarmonicDensity_bounds`, `primeSetFlip_harmonicCorrelation_tendsto`,
   `primeSetFlip_hasHyperplaneGap`). Every prime pattern has the exact
   decreasing Euler-product mean, which pays its squared-density gap.

30. **Exact harmonic cutoff boundary** (`primeSetCutoffDistanceSq_eq_zero_of_le`,
   `primeSetHarmonicDensity_tail`, `primeSetFlip_cutoff_distance_sq_eq`,
   `primeSetFlip_cutoff_distance_sq_tendsto`,
   `primeSetFlip_harmonic_cutoffs_complete_iff`). Positive Euler density is
   necessary and sufficient for harmonic approximation by prime cutoffs.

**Pillar obligations** (targets, not theorems): count before sign (an integer-side construction with square-root error);
arithmetic selection on overlapping complete sources; uniform mixed-term control through exhaustion; a displacement-sensitive
signature bound or uniform complete-source index ceiling; obstructions with positive content.

---

## 5. Traps

| Temptation | Correction |
|---|---|
| A Gram representation settles the sign | Prove equality with the literal complete form |
| Multiplicativity breaks parity | Liouville is completely multiplicative |
| A positive, even maximal, selective gap identifies the source | Single-prime flips at $p\ge11$ have the maximal gap $2\log2$ and keep polar matching |
| Exact finite-prime selection survives a fixed measurement tolerance | Remote maximal-gap flips have dyadic-response loss of order $1/p$ |
| Positive arithmetic weights select $\zeta$ | Test scalings, mixtures, golden data, Beurling systems |
| Finite counts or ranks retain signs | Record exact correlations and what reweighting loses |
| A fixed arithmetic mode controls a full spectrum | Bound its orthogonal complement uniformly |
| Finite-horizon positivity passes to the limit | State the topology, error currency, uniformity |
| Positive gaps at every finite prime cutoff give a gap after exhaustion | Their horizon bounds need not be uniform; finite flips stabilize to Liouville |
| Pointwise arithmetic convergence controls the optimal gap | Zero-gap cofinite flips converge pointwise to the untwisted maximal-gap sign |
| Positive measures explain arithmetic Herglotz | Positivity must come from arithmetic, not zeros |
| A no-go completes a route | Extract its positive survivor |

Battery: Liouville twin, scaled $\Lambda$, quadratic mixtures, golden curve, over-regular Beurling systems, Davenport–Heilbronn.

---

## 6. Open problems

1. **Quantitative exhaustion and source selection.** Determine sharp joint-gap decay rates and
   extend source selection beyond finite prime signs. An explicit upper bound
   $O_B((\log Q)^{-3})$ is proved for primes $B<p\le Q$. The fixed dyadic probe selects this
   family exactly, but no fixed positive tolerance survives remote prime flips. Prime cutoffs above
   every fixed bound have greatest gaps tending to zero. Reciprocal-mass counts
   now control truncation uniformly for arbitrary prime patterns and give sparse
   infinite examples with near-maximal positive gaps. Prime stripping also has an
   explicit additive error, at most O(log Q), uniform in every residual sign.
   Every infinite pattern now has its exact Euler-product harmonic mean
   and the corresponding squared-density gap. Harmonic approximation by finite
   prime cutoffs holds exactly at positive Euler density, with an exact squared
   distance formula. Optimal-gap transfer requires further work. Selection among arbitrary multiplicative weights
   remains open.
   Every finite prime set has an attained greatest gap characterized by its explicit secular
   signs and unique interior root. Proper inclusion strictly decreases a submaximal larger-set
   gap; equality can occur only at the maximum. Single-prime gaps are classified by the
   arithmetic secular root and the dyadic ceiling, including the cutoff at eleven.
2. **Selective overlap transfer**: carry the discrete hyperplane gap into continuous atomic families beyond the Robin–Euler threshold, paying the
   affine pole direction separately.
3. **Arithmetic Herglotz theory**: Toeplitz positivity from prime-side data with Gamma and poles.
4. **Integer-side auxiliary vanishing**: arithmetic sections replacing the Frobenius lattice annihilator with controlled complexity and
   vanishing; parity-sensitive input exposed before any sieve count.
5. **Finite-rank renormalization**: a uniform index ceiling for the complete source, retaining the first prime layer (endpoint: finite
   off-line support ⇒ a fixed zero-free strip).
6. **Exact inertia counting**: an observable separating a reflected pair from two critical points at depth $\asymp1/\log T$.
7. **Structural questions**: why the smallest prime fixes both the dyadic generator and the sharp gap; what survives the parity barrier;
   the heat-flow reality horizon $\exp((27/40+\varepsilon)/t)$ as $t\to0$; a topology preserving complete inequalities under exhaustion.

## 7. Tools to build

Signed incidence counts with exact mixed entries; selective overlap transfer; arithmetic Herglotz constructions; integer-side
auxiliary sections; displacement-sensitive inertia counts.

## 8. Contribution standard

A new unconditional count, paid sign, energy bound, index ceiling or sharp classification, with its arithmetic construction,
domain, growing-parameter dependence, battery behaviour and relation to an open mechanism. First decisive success: selective
positivity past the Robin–Euler point, a new displacement-sensitive census bound, or a uniform finite-index bound for the complete
source.
