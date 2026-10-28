# Arithmetic Intersection Theory (AIT)

Namespace `GaloisForLFunctions.ArithmeticIntersectionTheory`; umbrella `ArithmeticIntersectionTheory.lean`.

**Question.** Weil's proof for curves is intersection theory on $C\times C$: integer intersection numbers, correspondences with a
projection formula, a diagonal with finite self-intersection (adjunction), and the Hodge index for the sign. Over $\mathbb Z$ the
explicit formula is a pairing of the same shape. Which of the four ingredients exist, on which carrier, how do the carriers
glue, and what exactly is the one missing statement?

AIT is the intersection theory of the **characteristic circle** — the torsion $\mu_\infty\subset\mathbb G_m(\mathbb C)$ with power maps, rotations, Galois
— and of its transfer to the scaling surface.

> Over $\mathbb Z$ intersection numbers of torsion cycles exist, are log-orders of finite rings, and obey the projection formula; the
> self-intersection of a torsion orbit is the discriminant of its cyclotomic field. The diagonal exists only after a
> regularization, which is not covariant: $[t]$ rescales the regulator, anomaly $\log\#\ker[t]$. Weil's prime form is the finite
> intersection pairing, a sum of transverse local tower forms, each bounded; their sum is not, and RH is the statement that
> the archimedean place pays for it.

---

## 1. Place in the research

Exhaustion laws reduce to three structural facts: the Hecke algebra is commutative, every receiver is a linear functional of
the explicit formula, the diagonal has no finite self-intersection. Over $\mathbb F_q$ one object removes all three; AIT builds what
remains over $\mathbb Z$ and locates the missing statement.

| Programme | Takes / adds |
|---|---|
| ArithmeticEffectivityTheory | Torsion orbits, $I(m,n)$, Hecke law, Abel energies / projection formula, anomaly, different, Hecke cocycle, log-orders |
| ArithmeticElectrostatics | Potential reading / covariance theory of the counterterm |
| RenormalizedBiarithmeticGeometry | Survival law, rank dichotomy, lattice germ / germ = rotation spectrum (Gauss digamma) |
| ArithmeticCastelnuovoSeveri, ArithmeticOrientationGeometry | Scaling surface, Hecke towers on the zero side / tower form on the prime side; local Hodge index |
| `RHTower`, BiScaleUncertainty | Narrow bumps, Lévy gain, Weil positivity under RH / transfer identity on log-atom tests |
| BiarithmeticGaugeGeometry, ArithmeticCorrelationGeometry | Gauge torus, twins / tensor form of the prime kernel; gauge blindness |
| ArithmeticPolarization, ConjugateDiagonalGeometry | $W,D,\Delta$ / zero moments as Rosati pairings |
| SpacingScaleHarmonicAnalysis | Exact atom constants (Robin constant, two-atom pairing) |
| TransThresholdPairCorrelation, SquareRootThreshold | Two-point form of the missing statement |

---

## 2. Why

**Weil's four ingredients**: (i) integer intersection numbers, Lefschetz $\Gamma_m\cdot\Delta=N_m$; (ii) projection formula; (iii) $\Delta^2=2-2g$; (iv) Hodge
index. (i)–(iii) are identities; (iv) is the sign.

**Over $\mathbb Z$ the identities hold on the circle.** $O_n=\{\Phi_n=0\}$ is a horizontal divisor of $\mathbb G_m/\mathbb Z$.
- *Intersection numbers are log-orders*: $I(n,m)=\log\#(\mathcal O_{\mathbb Q(\zeta_n)}/(\Phi_m(\zeta_n)))$; with $O_1=\{1\}$, $\Lambda(n)=\log\#(\mathcal O/(\zeta_n-1))$.
- *Correspondences*: $[t]$ is Hecke; $z^t-w^t=\prod_{\omega\in\mu_t}(z-\omega w)$ is the projection formula.
- *Adjunction*: self-intersection per point of $O_n$ = $\sum_{p^a\|n}(a-\tfrac1{p-1})\log p$ = the different per unit degree; $I(p^k,p^k)=\log|d_{\mathbb Q(\zeta_{p^k})}|$.

**The regularization is not covariant.** At Abel radius $r<1$ energies are positive (archimedean Hodge index); Weil's prime kernel
is their limit after subtracting $\log1/(1-r)$ per point. $[t]$ replaces $r$ by $r^t$; the counterterm moves by $\log t$. On orbits this
is the Hecke cocycle $\beta(n,t)$, not a bounded coboundary. Scaling radii with the spacing removes the anomaly — leaving a scalar
counterterm that carries no sign.

**The local sign exists; the global sign is RH.** At $p$ the finite intersection on a ladder $\{cp^j\}$ is a positive
Kac–Murdock–Szegő form, spectrum in $[(1-q)/(1+q),(1+q)/(1-q)]$, $q=p^{-1/2}$. Weil's prime kernel is $\sum_p\log p(\text{tower}-1)$: transverse local
forms, each bounded, sum unbounded. On log-atom tests the prime functional *is* this sum.

**Elliptic correspondences look the wrong way**: rotations diagonalize torsion energy on $\mu_N$ with eigenvalues = archimedean
local factor at rational points (Gauss digamma). Zeros enter only through hyperbolic Hecke maps.

---

## 3. Objects and language

| Over $\mathbb F_q$ | AIT object | Lean |
|---|---|---|
| curves on $C\times C$ | torsion cycles $\sum x_nO_n$; point cycles on $\mu_N$; log-atom cycles | `primitiveRoots`, `logAtomTest` |
| $D\cdot E$; Lefschetz | $I(m,n)$ as log-order; intersection with the arithmetic point | `orbitIntersection`, `log_card_quotient_cyclotomicValue`, `log_card_quotient_zeta_sub_one` |
| projection formula | power maps, fibres $\mu_tz$, rotations | `sum_log_norm_sub_mul_nthRoots`, `pow_mul_rotate` |
| $\Delta^2$ | $c(n)=I(n,n)/\varphi(n)$, the different | `selfIntersection_eq_sum_local`, `orbitIntersection_self_eq_log_discr` |
| — | regulators: Abel radius; spacing radius $e^{-\varepsilon/n}$ | `circleKernel`, `spacingRadius` |
| — | Hecke cocycle $\beta(n,t)=\log t-\sum_{p\mid t,p\nmid n}\log p/(p-1)$ | `heckeCocycle_eq` |
| local intersection | $p$-ladder, tower form $K_q=(q^{|i-j|})$ | `kmsForm_eq_orbit_levels` |
| one Frobenius ladder | transverse ladders $L_p=\log p(K_p-1)\otimes1$, $P=\sum_pL_p$ | `ladderKernel_eq_tensor`, `weilPrimeKernel_eq_sum_ladderKernel` |
| — | rotation spectrum = lattice germ $G_{r^N}(k/N)$, digamma | `rootCycleEnergy_eq`, `gauss_digamma_theorem` |
| Hodge index | archimedean / local / global | `hasSum_pointEnergy`, `localForm_lower`, `riemannHypothesis_archPolar_ge_towers` |

**Words.** *Carrier* and *transition*; *finite / archimedean / Fourier reading*; *regulator, counterterm, anomaly, covariant*;
*saturated cycle*; *tame different*; *ladder, tower form, level, transverse*; *log-atom test* (bumps narrower than $\log(1+1/M)$);
*pole direction* $x_n=n^{-1/2}$.

---

## 4. Mechanisms

1. **Projection formula and regulator anomaly**: $[t]$ maps $r\mapsto r^t$; renormalized pullback shifted by $-t\log t$ per unit mass.
2. **Log-orders**: norms of $\Phi_m(\zeta_n)$ over complex embeddings.
3. **Adjunction**: $\log$ is a derivation of Dirichlet convolution: $\mu*(\mathrm{id}\cdot\log)=\varphi\log+\varphi*\Lambda$.
4. **Towers**: $K_q(x)=T_0^2+(1-q^2)\sum_{k\ge1}T_k^2$ in tail coordinates.
5. **Transverse decomposition**: exactly one prime carries each kernel entry; local bounds $2q\log p|x|^2/(1\pm q)$.
6. **Local forms do not sum**: along the pole direction the prime form is $\asymp(\log M)^2$ at mass $\asymp\log M$.
7. **Gauge blindness**: $P^\varepsilon(m,n)=\varepsilon(m)\varepsilon(n)P(m,n)$ for every real sign twin.
8. **Fourier duality on $\mu_N$**: rotation modes diagonalize the energy with lattice-germ eigenvalues; Gauss's theorem with anomaly $\log N$.
9. **Transfer**: log-atom lags see only exact ratios; prime functional $=\|\varphi\|^2\sum x_mx_nP(m,n)$.
10. **Spacing regulator**: radii $e^{-\varepsilon/n}$ keep the Gram structure, scalar counterterm $\log(1/2\varepsilon)$, only tame ramification varies.
11. **Polar part on log-atoms**: rank-two pairing of $\sum x_nn^{-1/2}$ with $\sum x_nn^{1/2}$.
12. **Square-root price**: paying towers separately costs $\sqrt M$ against $\log M$ jointly.
13. **Tower coordinates**: $\Re(\text{arch}+\text{polar})=E_\varphi|x|^2+2\alpha\beta(\sum x/\sqrt n)(\sum x\sqrt n)-\sum_{m<n}x_mx_nK_\varphi(\log n/m)$.
14. **Adjunction beats the tower**: above the second level of every ladder the renormalized torsion form is negative definite.
15. **Positive squares on boxes**: anti-poles at prime bases pair against first rungs; ground-state identity bounds them above.

---

## 5. Pillar theorems

1. **Projection formula and anomaly** (module `TheProjectionFormulaAndTheRegulatorAnomaly`).
2. **Intersection numbers are log-orders; adjunction = discriminant** (`log_card_quotient_cyclotomicValue`, `selfIntersection_eq_sum_local`,
   `orbitIntersection_self_eq_log_discr`).
3. **Hecke cocycle is not a bounded coboundary** (`heckeCocycle_eq`, `not_exists_bounded_potential`).
4. **Local Hodge index; transversality; local is not global** (`kmsForm_eq_orbit_levels`, `weilPrimeKernel_eq_sum_ladderKernel`, `not_exists_primeForm_le`).
5. **Gauge blindness** (`signTwistForm_eq`).
6. **Fourier duality / Gauss digamma** (`gauss_digamma_theorem`).
7. **Transfer and RH in tower coordinates**: under RH $\|\varphi\|^2\sum_pQ_p+\sum_{m<n}x_mx_nK_\varphi\le E_\varphi|x|^2+2\alpha\beta(\sum x/\sqrt n)(\sum x\sqrt n)$
   (`primeSum_logAtom_eq_towers`, `riemannHypothesis_archPolar_ge_towers`; module `TheHodgeIndexInTowerCoordinates`).
8. **Spacing regulator: positive, covariant up to tame ramification, indefinite limit** (`spacingForm_nonneg`, `spacingLimit_transport`).
9. **Rosati moments** (`pair_pow_eq_two_re`).
10. **Adjunction beats the tower** (`renormalized_ladder_le`).
11. **Positive index on boxes** between $cN^{1/5}/\log N$ and $N^{4/5+\varepsilon}$ (modules `TheTorsionFormHasPolynomiallyManyPositiveSquares`,
    `ThePositiveSquaresOfTheTorsionFormLiveBelowFourFifths`).
12. **Base and successor**: ladders of distinct primes are disjoint; successor transverse to every ladder except $1\to2$ (`sameLadder_succ_iff`).

---

## 6. Answers in brief

- **Covariant renormalization of the diagonal?** Not with a uniform regulator (anomaly $\log t$, cocycle); with the spacing regulator
  the anomaly disappears but the counterterm is scalar and the limit indefinite. Missing: a covariant regulator whose
  counterterm has a nontrivial null cone.
- **Where do integers enter?** As orders of finite rings — local; they give the local Hodge index, not the global sign.
- **Elliptic correspondence?** Rotations: exact, but localize in additive $\mathbb Q/\mathbb Z$; zero ordinates live in the multiplicative dual.
- **The base?** No common ladder: commuting transverse local operators on $\ell^2(\oplus_p\mathbb N)$; additive information lives between towers.
- **Which positivity where?** Archimedean at finite regulator; local at each prime; global = RH, readable in tower coordinates;
  the content is the regime $\delta\asymp1/M$ of the widest admissible atoms.
- **Two-point form**: zero moments of Dirichlet polynomials are Rosati pairings; beyond the threshold their prime side is TTPC's
  coalescent surplus.

---

## 7. Traps

| Trap | Truth |
|---|---|
| Exact projection formula ⇒ covariant renormalized pairing | $[t]$ rescales the regulator; counterterm moves by $\log t$ |
| A scalar counterterm commutes with everything | Its change under $[t]$ is the cocycle $\beta$ |
| A covariant regulator gives a sign | Spacing regulator: covariant, positive at every $\varepsilon$, indefinite limit |
| Integer intersection numbers give the sign | Integrality is local; the sum of local forms is unbounded |
| Local positivity at every prime sums | The identity is subtracted once per prime; $\sum\log p/\sqrt p$ diverges |
| Rotations localize zeros | Their spectrum is the archimedean factor at rational points |
| A finer prime-side statement separates $\zeta$ from twins | Sign twins have unitarily equivalent prime forms |
| Over $\mathbb Z$ there is one Frobenius | One ladder per prime, transverse |
| Moments over zeros are positive data | Rosati pairings; positive only on critical configurations |

---

## 8. Open problems

1. **A covariant regulator with a nontrivial null cone** (by the survival law, exactly what a sign through the limit requires).
2. **The tower inequality on the polar hyperplane** at the widest admissible atoms $\delta\asymp1/M$ (constants now exact, SSHA).
3. **Arithmetic Riemann–Roch on torsion orbits**: a section functor on the scaling surface with defect $\tfrac12\log|d|$.
4. **The discriminant for all $n$**: $I(n,n)=\log|d_{\mathbb Q(\zeta_n)}|$ beyond prime powers.
5. **Exact exponent of the positive index on boxes** (numerically $\approx N^{0.38}$; heuristics $\alpha^*\approx0.32$ or $1/\phi^2$).
6. **Thresholds as weights**: a weight filtration of log-atom cycles by $\log(1/\delta)/\log M$.

## 9. Contribution standard

Unconditional; name the carrier and reading (finite, archimedean, Fourier); state covariance (anomaly) and positivity separately;
separate identities from signs; report over $\mathbb F_q$, on the golden datum and the sign twins; record the positive survivor of every
no-go. Every regularization carries its anomaly; no positivity without a count; local is not global.
