# Renormalized Arithmetic Potential Theory of the Characteristic Circle (RAPT)

Namespace `GaloisForLFunctions.RenormalizedArithmeticPotentialTheory`; umbrella `RenormalizedArithmeticPotentialTheory.lean`.

**Question.** Over $\mathbb F_q$ Weil uses one pairing that is positive, Frobenius-equivariant and finite on the diagonal. Over $\mathbb Z$ the
pieces live on separate carriers: potential theory of the zero divisor (AES), intersection theory of the characteristic circle
with an anomalous diagonal (AIT), renormalization with survival cones (RBG). Every pairing of the explicit formula is a
regularized self-energy, and the two places of $\mathbb Q$ regularize the same diagonal. **Which regulator, counterterm and coupling
of the prime place, the archimedean place and the arithmetic point keep positivity and Hecke equivariance together through
the limit, and which provably cannot?**

RAPT is the theory of the **renormalization data** of the explicit formula: regulators, their counterterms (rank, survival
cone), Hecke anomalies, and the coupling of places that pays the divergence.

> The rank of a counterterm belongs to the regulator, not the pairing. The Abel radius leaves nothing. The **horizon** (Weil's
> own regulator, orders $\le N$) has as counterterm the tensor product of the two places' counterterms — identity on torsion
> orbits weighted by size, times the polar projection on log-scale profiles — and it is **Hecke covariant**: the anomaly
> $\log p$ of $[p]$ becomes the density scaling $1/p$ and cancels. The covariant scalar is $\log N+O(1)$ with constant one (the anomaly
> of $[N]$); torsion renormalization costs $\varphi\log N$. What remains after the polar counterterm is $-2\gamma$; on $p$-adic classes the
> tower form of $p$. Polar matching selects the Euler gauge.

---

## 1. Place in the research

Of Weil's ingredients, missing over $\mathbb Z$ are a finite self-intersection of the diagonal, archimedean payment of the
local-to-global divergence, and stability of the computed equilibrium — all statements about one object, the **counterterm**
and the place that pays it.

| Programme | Takes / adds |
|---|---|
| RenormalizedBiarithmeticGeometry | Regularized families, survival cones, torsion and lattice germs / coupled survival law, joint germ |
| ArithmeticIntersectionTheory | Orbit intersections, different, Hecke cocycle, anomaly, spacing regulator / covariance as constraint; horizon tensor law |
| ArithmeticElectrostatics | Torsion pairing, atomic Weil form, arithmetic point, atomic stability / exact constants, spectral ends |
| ArithmeticEffectivityTheory | Torsion orbits, Weil prime kernel as renormalized torsion energy |
| SpacingScaleHarmonicAnalysis | Stability at a fixed fraction of the spacing; overlap critical exponent |
| BiarithmeticGaugeGeometry | Gauge torus, twins / gauge behaviour of matching |
| `RHTower`, `ArtinMertens` | Mertens theorems (with $\gamma$; for Artin characters) |

---

## 2. Why

**Over $\mathbb Z$ the diagonal is a divergence.** Prime place: torsion orbits, Green function $-\log|1-z\bar w|$, Abel self-energy $\log1/(1-r)$.
Archimedean place: atoms at $\log n$, width-$\varepsilon$ self-energy $\log(1/\varepsilon)+O(1)$. The arithmetic point $z=1$ (the pole) is where both
divergences meet. Positivity lives before the limit (Gram matrices), equivariance after (Hecke invariance of the prime
kernel); positivity passes the limit exactly on the counterterm's null cone (RBG).

**What the theory decides.**
1. *Coupling never lowers the prime counterterm's rank*; the archimedean germ (rank one) pays exactly one direction: the arithmetic point.
2. *The rank belongs to the regulator*: at the horizon the counterterm is the tensor (orbital × polar) one, with nontrivial
   survival cone: the class-wise polar hyperplane.
3. *The anomaly cancels at the horizon*: $[p]$ shifts classes, densities scale by $1/p$, the polar functional by $p^{-1/2}$.
4. *Covariance costs $\log N+O(1)$*, constant one = the archimedean self-energy at spacing $\varepsilon\asymp1/N$. Keeping the self-intersection
   (torsion renormalization) costs exactly $\varphi\log N+O(1)$, $\varphi$ the golden ratio (extremal charges $\varphi^{\omega(n)}/\sqrt n$).
5. *The finite part is computed*: $-2\gamma$ on uniform profiles; on $p$-adic classes $-2\gamma_p\cdot1+\log p(K_{p^{-1/2}}-1)$ (the tower form); for a finite prime
   set $Q$ the matched operator $A_Q=\operatorname{diag}(\log n)-P_Q+\gamma_Q\cdot1$ has a complete basis with simple energies
   $\gamma+\log m+\text{tameDifferent}(m)$ and compact shifted inverse; the same energies appear in the full prime matrix via Ramanujan profiles.
6. *Matching is not gauge blind*: $\zeta$ diverges along the polar direction with coefficient $+1$, its Liouville twin with $-1$.

---

## 3. Objects and language

| Object | Definition | Lean |
|---|---|---|
| Weil's prime kernel; atomic prime form | $P(m,n)=\Lambda(n/m)(n/m)^{-1/2}$; $P_N(x)$ | `weilPrimeKernel`, `atomicWeilForm` |
| pole vector; polar functional | $u_n=n^{-1/2}$; $\ell(x)=\sum x_nn^{-1/2}$ | `poleVector`, `polarFunctional` |
| step / class profiles | log-scale steps $u^{(M)}$; valuation classes $w_j^{(M)}$, densities $\delta_j$ | `stepProfile`, `classPole`, `classDensity` |
| tensor counterterm | $\sum_j\delta_j^{-1}\ell_j(x)^2$ | `tensorCounterterm` |
| Hecke shift | $(T_tx)(n)=x(n/t)$ | `heckeShift` |
| coupled counterterm, prime survival, joint germ | prime block + partner block | `coupled`, `primeSurvival`, `jointGerm` |
| covariant / torsion counterterms | least scalar with $P_N\le\kappa|x|^2$; least renormalizing torsion pairing | `covariantCounterterm_sandwich`, `torsionCounterterm_window` |
| matched sieve operator | $A_Q$ on the maximal log domain of $\ell^2(S_Q)$ | `sieveAdjunctionOperator` |
| Ramanujan profile, adjunction energy | $u_m(n)=c_m(n)/\sqrt{\varphi(m)n}$; $\gamma+\log m+\text{tameDifferent}(m)$ | `ramanujanHorizonVector`, `ramanujanAdjunctionEnergy` |
| complete Weil horizon matrix | self-energy + prime kernel + archimedean cross integrals + two pole products | `fullWeilHorizonMatrix`, `normalizedFullWeilHorizonMatrix` |
| archimedean center kernel | collar of the Lévy density in pole gauge | `archimedeanCenterKernel` |

| Regulator | Counterterm | Rank | Survival | Anomaly of $[t]$ |
|---|---|---|---|---|
| Abel radius | $\varphi(n)\delta_{mn}$ | #orders | $\{0\}$ | $\log t-$tame different |
| spacing radius | scalar | #orders | $\{0\}$ | tame different |
| horizon, uniform | $\ell(x)^2$ | 1 | $\int g=0$ | — |
| horizon, class-wise | $\sum_j\delta_j^{-1}\ell_j^2$ | #classes | $\ell_j=0\ \forall j$ | none for $[p]$ |

**Words.** Counterterm *scalar / polar / orbital / tensor*; renormalization *covariant / anomalous*; a coupling *pays* a direction;
divergences *matched / anti-matched*; *uniform* vs *class-wise* profiles. Every theorem states regulator, counterterm (rank,
survival cone), anomaly, and paying place.

---

## 4. Mechanisms

1. **Coupled survival**: partner-kernel inclusion; prime survival $\le$ rank of the partner.
2. **Horizon polarity and tensor law**: on uniform step profiles $P_N=\ell^2+O(\text{mass})$; on class-wise profiles $P_N=\sum\delta_j^{-1}\ell_j^2+O(H_N|c|^2)$; extends to
   profiles of bounded variation.
3. **Covariance forces a scalar**; Schur with the pole vector is extremal: $\kappa_{\rm cov}(N)=\log N-\gamma+o(1)$.
4. **Finite parts from Mertens limits**: if $A_\varepsilon(y)-\kappa\log y\to\alpha$, then $P_N(\varepsilon x)=\kappa\ell^2+2\alpha|x|^2+o(\text{mass})$ (for $\zeta$: $\kappa=1$, $\alpha=-\gamma$); the
   remainder is the harmonic convolution of the Mertens error.
5. **Residue classes and characters**: the horizon reads valuations, not residues (rank one on unit classes mod $q$); a class
   function is seen only through its mean; the finite part is diagonalized by characters with eigenvalues $2\Re(-L'/L(1,\chi))$.
6. **Prime spectral exhaustion**: the pole gap is exactly $2\log2$ (2-adic step). Finite Ramanujan spans uniformly approximate
   bounded-defect sublevels. For $\log N\,I-P_N$, this gives eventual exact counts, including multiplicity, from limiting energies
   $\gamma+\log m+d(m)$, and convergence of simple eigenlines to Ramanujan profiles.
7. **Atomic stability**: Lévy self-energy with constant one; Markov form nonnegative down to $\delta_N/(C\log N)$ with absolute
   interaction; at width $c/N$ the ground energy is $2\theta'(0)+\log(1/c)+\kappa_L(\varphi)+\gamma+O(c)$ (Robin constant + Euler constant).
8. **Complete Weil matrix at the spacing**: exact separation into common self-energy, full prime kernel, literal archimedean
   cross integrals and two pole products; the center-density kernel in pole gauge is inverse-difference + inverse-sum
   (harmonic); restoring the pole rows cancels the harmonic bulk, leaving identity + boundary layer; the center collar is
   paid by the top-atom potential $(n/N)\log n$; replacing literal cross integrals by the center kernel has uniform errors;
   complete Weil trial energies are simple and proper (pole shift affects only conductor one, below the first arithmetic excitation).

---

## 5. Pillar theorems

1. **Coupled survival; archimedean place pays the arithmetic point** (`card_le_rank_coupled`, `primeSurvival_jointGram`).
2. **Covariant counterterm is the anomaly** $\log N-\gamma+o(1)$ (`renormalizedPrimeForm_covariant_iff`).
3. **Torsion counterterm is the golden ratio** $\varphi\log N+O(1)$ (`torsionCounterterm_golden`); fixed-point law for $\alpha\operatorname{diag}(\log n)+P_N$ (`fixedPoint_top`).
4. **Tensor law; no anomaly at the horizon** (`abs_atomicWeilForm_classProfile_sub_le`, `finitePart_heckeShift`).
5. **Finite part is Euler's constant / the tower form / twice the Mertens limit** (`exists_abs_atomicWeilForm_stepProfile_add_le_of_polar`,
   `exists_abs_atomicWeilForm_classCombination_finitePart_le`).
6. **Tower deficit changes sign between 43 and 47**; the archimedean valuation potential pays it (`towerDeficit_eq_div_sinh`).
7. **Matched operator $A_Q$**: complete basis, simple energies, compact resolvent (modules `TheSieveOperatorHasTheAdjunctionEigenbasis`,
   `TheAdjunctionResolventIsCompact`; `sieveAdjunctionInverse_isCompact`).
8. **Spectral gap $2\log2$, exact counts and simple eigenlines** (`exists_poleDefect_ge`,
   `eventually_fullPrime_spectral_count_eq`, `exists_simple_fullPrime_eigenline`).
9. **Gauge selectivity**: matching coefficient = density of the gauge; finite part sees every flipped prime and $\zeta$ maximizes it;
   pole hyperplane and finite part separate $\zeta$ from Liouville (`liouville_matching`, `exists_pole_hyperplane_separates_liouville`).
10. **Characters and Chebotarev patterns matched by their mean** (`exists_norm_charMertensSum_le`, RP25/RP38/RP60 modules).
11. **Atomic stability with constant one** (`markovEnergy_atomicTest_nonneg_sharp`, `markovEnergy_atomicTest_nonneg_logSpacing`).
12. **Complete Weil matrix splits at the spacing; pole cancels the harmonic center row; trial energies simple and proper**
    (`normalizedFullWeilHorizonMatrix_apply_of_separated`, `sum_pole_minus_center_div_sqrt`, `collar_quadratic_div_horizon_le`,
    `completeWeilAdjunctionEnergy_injectiveOn`).

---

## 6. Traps

| Trap | Truth |
|---|---|
| The counterterm rank is intrinsic to the pairing | It belongs to the regulator |
| Coupling the places lowers the prime counterterm | Never; the archimedean germ pays one direction |
| Renormalization is necessarily anomalous | At the horizon the anomaly cancels exactly |
| A covariant scalar counterterm is cheap | $\log N+O(1)$, constant one; torsion costs $\varphi\log N$ |
| The continuum model gives the torsion constant | $e/(e-1)$ is wrong; extremal charges are multiplicative ($\varphi$) |
| Each place's counterterm sees the gauge | Each is gauge blind; their matching is not |
| The horizon reads residue classes | Only through the mean; residues are invisible to the divergence, visible to the finite part |
| The spacing regime is beyond reach | Separated regime computed; the open part is the overlap regime |

---

## 7. Open problems

1. **Overlap regime** $w\gg\delta_N$: which finite part (signed interaction + pole) keeps the matching through overlaps; SSHA ties
   positivity at widths $N^{-\theta}$, $\theta<1$, to RH. Next step on the complete Weil matrix: pass from the center-kernel replacement
   and trial energies to a lower bound of the full matrix at the spacing.
2. **All primes at once in the class-profile finite part**, or growing normalized class families.
3. **The $O(1)$ term of the torsion constant**; twisted torsion pairings.
4. **Finite parts of Chebotarev patterns** (needs Artin $L$ Mertens constants); patterns not constant on divisions (Hecke $L$-functions).
5. **Finite parts of the archimedean place and the pole** beyond the separated regime.

## 8. Tools to build

A lower bound for the complete Weil horizon matrix through overlaps; the finite-part law for all primes; Mertens constants
for Artin and Hecke $L$-functions.

## 9. Contribution standard

State regulator, counterterm (rank, survival cone), anomaly and paying place; separate divergence (matching) from finite
part; report gauge behaviour (Liouville, character, Chebotarev gauges); unconditional with no positivity premise.
