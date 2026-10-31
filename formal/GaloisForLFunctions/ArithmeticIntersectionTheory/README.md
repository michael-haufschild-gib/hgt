# Arithmetic Intersection Theory (AIT)

Namespace `GaloisForLFunctions.ArithmeticIntersectionTheory`; umbrella `ArithmeticIntersectionTheory.lean`; 20 modules.
Everything is unconditional. Statements with `riemannHypothesis_` take RH as a hypothesis (they are implications, not proofs of RH).

## 1. Motivation

Weil's proof for curves uses four ingredients on C × C: integer intersection numbers, correspondences with a projection
formula, a diagonal with finite self-intersection (adjunction), and the Hodge index for the sign. AIT builds the
analogue over ℤ on the characteristic circle (torsion orbits O_n = primitive n-th roots of unity, power maps as Hecke
correspondences, rotations), proves which ingredients exist, and isolates the one missing statement: the global sign.

## 2. Objects

| Object | Lean | Meaning |
|---|---|---|
| Orbit intersection | `orbitIntersection` (ArithmeticEffectivityTheory) | I(m,n) = Σ_{ζ∈O_m,η∈O_n} log|ζ − η| |
| Self-intersection per point | `selfIntersection`, `tameDifferent` | c(n) = I(n,n)/φ(n) = log n − Σ_{p|n} log p/(p−1) |
| Abel kernel; cycle energy | `circleKernel`, `cycleEnergy`, `pullbackPoint` | k_r(z,w) = −log|1 − rzw̄| |
| Cyclotomic value | `cyclotomicValue`, `zetaN` | Φ_m(ζ_n) ∈ 𝓞(ℚ(ζ_n)) |
| Hecke cocycle | `heckeCocycle` | β(n,t) = c(tn) − c(n) |
| Torsion forms | `torsionForm`, `renormalizedTorsionForm`, `torsionBilinear`, `heckeTransport` | Q_r(x) and its limit −P(x) − Σx_n²c(n) |
| Weil prime kernel | `weilPrimeKernel` (ArithmeticEffectivityTheory), `primeForm` | P(m,n) = Λ(n/m)(n/m)^{−1/2} on m ∣ n, m ≠ n |
| Tower (KMS) form | `kmsEntry`, `kmsForm`, `towerTail`, `ladderForm` | K_q = (q^{|i−j|}), q = p^{−1/2}, on a p-ladder c·p^i |
| Ladder kernel; local form | `ladderKernel`, `localForm`, `towerOnSet` | L_p = log p·(K_p − 1) ⊗ 1; Q_p(x) |
| Pole direction | `poleVector` | x_n = n^{−1/2} |
| Sign gauge | `IsSignGauge`, `signTwistKernel`, `liouville` | completely multiplicative ε = ±1 |
| Point cycles on the circle | `cosCoeff`, `sinCoeff`, `circlePoint`, `rootCycleEnergy`, `rootMode` | Fourier data of Σx_a δ_{e^{iθ_a}} |
| Torsion Fourier coefficient | `torsionFourier`, `rootAngle`, `rootPoint` | Σ_a −log|1 − rζ^a| cos(kθ_a) |
| Log-atom test | `logAtomTest`, `logAtomAutocorr`, `LogAtomData`, `primeSum` | Σ_{n∈S} x_n φ(u − log n), width δ < log(1 + 1/M) |
| Explicit-formula parts | `archPolarPart`, `gammaPart`, `atomSelfEnergy`, `archKernel`, `jumpWeight` | arch + pole and Γ parts; E_φ, K_φ |
| Spacing regulator | `spacingRadius`, `spacingEnergy`, `spacingForm`, `spacingLimit` | radius e^{−ε(1/m + 1/n)} |
| Rosati product | `reflectPoint`, `dirichletPoly`, `dualPoly`, `rosatiProduct` | Q(ρ)·conj Q(1 − ρ̄) |
| Anti-pole | `armVector`, `armWeight`, `Windows` | δ_q − Σ_{p∈A} δ_{qp}/(2√p) |
| Frobenius tower | `frobeniusTower` | degree-d place on the single ladder over 𝔽_q |
| Positive atoms | `torsionPositiveAtoms` | n with 2A(N/n) + d(n) > ½log n |

## 3. Language

- **Carrier**: the characteristic circle (torsion) vs the scaling surface (log-atom tests); the **transition** between them is the log-atom identity.
- **Regulator / counterterm / anomaly**: Abel radius r, subtraction log(1/(1−r)) per point, the shift log t caused by [t].
- **Saturated cycle**: every prime of t divides every order; there the anomaly is pure log t.
- **p-ladder**: orders agreeing away from p (c·p^i); ladders of distinct primes are **transverse**.
- **Local / global sign**: positivity of each Q_p vs positivity of Σ_p Q_p against the archimedean place.

## 4. Mechanisms

**A. Identities on the circle**
1. Projection formula: ∏_{ω∈μ_t}(z − ωw) = z^t − w^t, so Σ_ω log|z − ωw| = log|z^t − w^t|; regularized: Σ_ω k_r(ωz, w) = k_{r^t}(z^t, w^t).
2. Log-orders: log #(𝓞_{ℚ(ζ_n)}/(Φ_m(ζ_n))) = I(n,m) (norm = product over embeddings); Λ(n) = log #(𝓞/(ζ_n − 1)).
3. Adjunction: log is a derivation of Dirichlet convolution, μ⋆(id·log) = φ·log + φ⋆Λ, (φ⋆Λ)(n) = φ(n)·tameDifferent(n) ⇒ c(n) = Σ_{p^a∥n}(a − 1/(p−1))log p ≥ 0; I(p^k,p^k) = log|disc ℚ(ζ_{p^k})|.

**B. Renormalization and covariance**
4. Regulator anomaly: (1 − r^t)/(1 − r) → t ⇒ renormalized pullback = t·renormalized image − t log t·mass.
5. Hecke cocycle: P(tm,tn) = P(m,n) but β(n,t) = log t − Σ_{p|t,p∤n} log p/(p−1) ∈ [c(t), log t]; cocycle identity; along 2^k it grows like k log 2, so it is not a bounded coboundary.
6. Spacing regulator e^{−ε/n}: Gram positivity via Ramanujan sums at every ε, scalar counterterm log(1/(2ε)), limit −P + Σx_n²·tameDifferent changes under [t] only by tame ramification — and is indefinite ((1 − √2)log 2 on {1,2}).

**C. Towers**
7. On a p-ladder P = log p·(K_q − 1); tail coordinates K_q = T_0² + (1 − q²)Σ T_k², with level weights φ(p^k); spectrum of K_q in [(1−q)/(1+q), (1+q)/(1−q)].
8. Transversality: each nonzero P(m,n) lives on exactly one ladder; P = Σ_p L_p; primeForm = Σ_p Q_p with −2q log p|x|² ≤ (1+q)Q_p, (1−q)Q_p ≤ 2q log p|x|².
9. Local does not sum: on [1,M²] the pole direction has primeForm ≥ H_M Σ_{t≤M}Λ(t)/t at mass H_{M²} ⇒ no bound C|x|². Summing local bounds separately costs 238√M; joint Schur gives log M.
10. Adjunction beats the tower: c(cp^j) ≥ (j − 1/(p−1))log p ⇒ R negative definite above level 2 on every ladder.
11. Positive squares on boxes: anti-poles at prime bases are positive (R(v_q) ≥ ½Σ_A log p/p − log q) and mutually orthogonal ⇒ index ≥ cN^{1/5}/log N; diagonal domination R_N ≤ Σ(2A(N/n) + d(n) − ½log n)x_n² ⇒ index ≤ N^{4/5+ε}.

**D. Fourier and gauge**
12. Rotations are exact (no anomaly); point-cycle energy = Σ_j (r^j/j)(C_j² + S_j²) ≥ 0; on μ_N eigenvalues are lattice germs (r^k/N)G_{r^N}(k/N) and the renormalized limit is Gauss's digamma theorem, with log N the anomaly of [N].
13. Gauge: P^ε = diag(ε)P diag(ε); sign twins (Liouville included) have unitarily equivalent prime forms.

**E. Transfer to Weil's form**
14. Log-atom lags see only exact ratios: primeSum(f⋆f̃) = ‖φ‖²·primeForm = ‖φ‖²Σ_p Q_p(x).
15. Polar part = 2αβ(Σx_n n^{−1/2})(Σx_n n^{1/2}); Re(arch + polar) = E_φ|x|² + polar − Σ_{m<n}x_m x_n K_φ(log(n/m)); E_φ ≥ ‖φ‖²(γ₀ + e^{−1/2}log((1−δ)/δ)).
16. Rosati: Q̃(ρ) = conj Q(ρ*); on the line QQ̃ = |Q|²; off the line a pair contributes 2Re(Q(ρ)conj Q(ρ*))^k.

## 5. Pillar theorems

| Theorem | Lean | Status |
|---|---|---|
| Projection formula; regularized pullback; regulator anomaly | `sum_log_norm_sub_mul_nthRoots`, `cycleEnergy_pullback`, `tendsto_renormalized_pullback_sub` | proved |
| Intersection numbers are log-orders; Λ as log-order | `log_card_quotient_cyclotomicValue`, `log_card_quotient_zeta_sub_one` | proved |
| Adjunction: c(n) = different per degree; discriminant at prime powers | `selfIntersection_eq_sum_local`, `orbitIntersection_self_eq_log_discr` | proved |
| Hecke cocycle formula; not a bounded coboundary; Hecke variation | `heckeCocycle_eq`, `not_exists_bounded_potential`, `tendsto_heckeVariation` | proved |
| Tower form: orbit levels; KMS bounds; ladder bounds | `kmsForm_eq_orbit_levels`, `kmsForm_lower`, `kmsForm_upper`, `ladderForm_eq` | proved |
| Transverse decomposition; local Hodge index | `weilPrimeKernel_eq_sum_ladderKernel`, `ladderKernel_eq_tensor`, `primeForm_eq_sum_localForm`, `localForm_lower`, `localForm_upper` | proved |
| Local forms do not sum; square-root price | `not_exists_primeForm_le`, `primeForm_le_sqrt` | proved |
| Gauge blindness of the finite intersection | `signTwistKernel_eq`, `signTwistForm_eq`, `not_exists_signTwistForm_le` | proved |
| Gauss digamma = Fourier transform of torsion energy | `torsionFourier_eq`, `gauss_digamma_theorem` | proved |
| Rotation spectrum on μ_N | `hasSum_pointEnergy`, `rootCycleEnergy_eq`, `rootCycle_eigenvalues_nonneg` | proved |
| Weil's prime functional = finite intersection | `primeSum_logAtom_eq`, `primeSum_logAtom_eq_towers` | proved |
| Polar part on log-atoms; arch part in tower coordinates; atom self-energy | `weilPoleTerm_logAtom`, `weilArchRe_logAtom`, `atomSelfEnergy_ge` | proved |
| RH ⇒ tower inequality (arch + pole pay the towers) | `riemannHypothesis_archPolar_ge_towers`, `riemannHypothesis_gammaPart_ge_towers`, `riemannHypothesis_tower_inequality` | proved implication |
| Spacing regulator: positive, covariant up to tame part, indefinite limit | `spacingForm_nonneg`, `tendsto_spacingForm`, `spacingLimit_transport`, `spacingLimit_not_nonneg` | proved |
| Adjunction beats the tower above level 2 | `renormalized_ladder_le` | proved |
| Positive index of R on [1,N] ∈ [cN^{1/5}/log N, N^{4/5+ε}] | `renormalizedTorsionForm_pos_on_span`, `eventually_finrank_le_rpow` | proved |
| Zero moments are Rosati pairings | `dualPoly_eq_conj`, `pair_pow_eq_two_re`, `sum_moment_re_nonneg_of_critical` | proved |
| Ladders of distinct primes disjoint; successor transverse | `ladderKernel_mul_ladderKernel_eq_zero`, `sameLadder_succ_iff`, `frobeniusTower_lcm_ne_zero` | proved |

## 6. Tools

**Developed**
- Logarithmic derivation of Dirichlet convolution (`pmul_log_mul`, `moebius_mul_id_pmul_log`, `totient_mul_vonMangoldt_eq`).
- KMS tail calculus (`towerTail_eq`, `kmsForm_eq_tail`) and ladder fibre decomposition (`towerOnSet_eq_sum_fibres`).
- Cyclotomic norm computation of intersection numbers (`embedding_cyclotomicValue`).
- Log-lattice separation lemma (`eq_of_abs_log_sub_lt`) and log-atom autocorrelation formulas (`autocorr_logAtom`, `logAtomAutocorr_log`).
- Fourier folding on μ_N (`hasSum_residue`, `hasSum_progression`, `sum_cos_mul_cos_rootAngle`).
- Anti-pole construction with prime windows and the diagonal-domination index bound (`finrank_le_of_renormalizedTorsionForm_pos`).

**To build**
- A Hecke-covariant regulator whose counterterm has a nontrivial null cone.
- The tower inequality on the polar hyperplane at atom width δ ~ 1/M, unconditionally.
- I(n,n) = log|disc ℚ(ζ_n)| for composite n.
- An arithmetic Riemann–Roch / section functor for torsion orbits.

## 7. Open questions

1. Is there a covariant regulator with a nontrivial null cone (the only way a sign can survive the limit)?
2. Does the tower inequality (Γ-part pays Σ_p Q_p on the polar hyperplane) hold unconditionally for log-atom widths δ ~ 1/M?
3. The exact exponent of the positive index of the renormalized torsion form on [1,N] (proved between 1/5 and 4/5).
4. A weight filtration of log-atom cycles by log(1/δ)/log M that turns the thresholds (√M separate, log M joint) into weights.
5. Can the two-point (Rosati) form of the missing sign be attacked beyond the square-root threshold (TTPC coalescent surplus)?

## 8. Traps

| Trap | Fact |
|---|---|
| An exact projection formula gives a covariant renormalized pairing | [t] rescales the regulator; the counterterm moves by log t |
| A scalar counterterm commutes with Hecke | Its change under [t] is the cocycle β, unbounded |
| A covariant regulator gives a sign | The spacing regulator is covariant and positive at every ε; its limit is indefinite |
| Integer intersection numbers give the global sign | Integrality is local; the sum of bounded local forms is unbounded |
| Local positivity at every prime sums | The identity is subtracted once per prime; Σ log p/√p diverges |
| Summing local bounds is harmless | It costs √M against log M for the joint bound |
| Rotations can localize zeros | Their spectrum is the archimedean factor at rational points |
| A finer prime-side statement separates ζ from twins | Sign twins have unitarily equivalent prime forms |
| Over ℤ there is one Frobenius ladder | One ladder per prime, pairwise transverse |
| Zero moments are positive data | They are Rosati pairings, positive only on critical configurations |
| `riemannHypothesis_tower_inequality` is a proof step toward RH | It is an implication from RH, giving the target inequality |

## 9. Context

| Uses | Modules |
|---|---|
| RHTower | 8 (separated bumps, Lévy density, exact archimedean form, pole term, Mertens, prime windows, crease budget) |
| ArithmeticEffectivityTheory | 5 (orbit intersections, Hecke law, Weil kernel as renormalized torsion energy) |
| RenormalizedBiarithmeticGeometry, RenormalizedArithmeticPotentialTheory, BiScaleUncertainty | 1 each (lattice germ; ground-state identity; RH ⇒ critical Weil energy) |

| Used by | Modules |
|---|---|
| RenormalizedArithmeticPotentialTheory | 10 (different, Hecke cocycle, tower form, transverse towers, positive squares) |
| ArithmeticElectrostatics | 1 (tame different) |
| CriticalArithmeticCorrelationTheory, ArithmeticLorentzianGeometry, CompletedArithmeticForms | 1 each |
| MainTheorems | umbrella |

| Neighbour | Relation |
|---|---|
| ArithmeticEffectivityTheory | defines I(m,n), Hecke law and the Weil kernel as renormalized torsion energy; AIT supplies adjunction, cocycle, towers |
| ArithmeticElectrostatics | potential-theoretic reading; uses the tame different for torsion self-intersections |
| RenormalizedArithmeticPotentialTheory | main consumer: counterterms, ground states, spectral points of the prime form |
| RenormalizedBiarithmeticGeometry | lattice germ; its survival law explains why scalar counterterms lose the sign |
| SpacingScaleHarmonicAnalysis | exact atom constants for the tower inequality at the spacing scale |

## 10. Big picture

Over ℤ three of Weil's four ingredients exist and are proved: intersection numbers of torsion cycles are logarithms of
orders of finite rings, power maps satisfy the projection formula, and the self-intersection of a torsion orbit is the
discriminant of its cyclotomic field. The diagonal, however, only exists after a regularization, and every
regularization tried either breaks Hecke covariance (the anomaly log t) or, once covariance is restored, loses the sign.

The sign itself splits cleanly: at each prime it holds (a positive Kac–Murdock–Szegő tower), but the towers of
different primes are transverse and their bounded local forms do not sum; on narrow log-atom tests Weil's prime
functional is exactly this sum, so RH becomes one inequality in which the archimedean self-energy and the pole must pay
for all towers at once. The finite intersection cannot tell ζ from its sign twins, and rotations see only the
archimedean factor, so the missing input must couple the archimedean place to the multiplicative structure across
primes. AIT turns "prove RH" into "prove the tower inequality at the widest admissible atoms".
