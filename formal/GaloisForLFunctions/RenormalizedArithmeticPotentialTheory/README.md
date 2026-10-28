# Renormalized Arithmetic Potential Theory of the Characteristic Circle (RAPT)

**One question.** Over `𝔽_q` Weil's proof of the Riemann hypothesis uses one pairing that is
positive, Frobenius equivariant and finite on the diagonal. Over `ℤ` the corpus has these pieces on
separate carriers: a potential theory of the zero divisor (AES), an intersection theory of the
characteristic circle with an anomalous diagonal (AIT), and a renormalization theory whose survival
cones decide which positivity passes a limit (RBG). Every pairing of the explicit formula is a
regularized self-energy, and the two places of `ℚ` regularize the same diagonal. **Which regulator,
which counterterm and which coupling of the prime place, the archimedean place and the arithmetic
point keep positivity and Hecke equivariance together through the limit, and which provably cannot?**

RAPT is the theory of the **renormalization data** of the explicit formula: regulators, the
counterterms they produce, the rank and survival cone of those counterterms, the anomaly of the
Hecke correspondences, and the coupling of the places that must pay the divergence. Its organizing
sentence:

> *The rank of a counterterm is a property of the regulator, not of the pairing. The Abel radius
> renormalizes the self-energy of every torsion point and leaves nothing. The horizon — the
> regulator of Weil's form — has as counterterm the tensor product of the two places'
> counterterms: the identity on the torsion orbits, weighted by their sizes, times the polar
> projection on log-scale profiles. This counterterm is Hecke covariant: the degree of `[p]`,
> additive anomaly `log p` under the radius, becomes the scaling `1/p` of the orbit densities and
> cancels exactly. Coupling never lowers the prime counterterm's rank, and the archimedean place
> pays exactly one direction, the arithmetic point. Covariance forces a scalar counterterm. The
> scalar the archimedean place must supply at atomic resolution `N` is `log N + O(1)`, with
> constant one: the anomaly of `[N]`. The anomalous torsion renormalization costs at least half a
> logarithm more. What remains after the polar counterterm is the scalar `−2γ`: the constant term
> of `−ζ′/ζ` at its pole, once for each Hecke direction. On the `p`-adic classes what remains is the
> tower form of `p`, the local Hodge index structure. Polar matching selects the Euler gauge: the
> Liouville twin diverges with the opposite sign.*

Namespace `GaloisForLFunctions.RenormalizedArithmeticPotentialTheory`; umbrella
`RenormalizedArithmeticPotentialTheory.lean`. Everything is unconditional; RH and its partial forms
appear only inside equivalences.

---

## 1. Place in the research

The frontier ([obstacles summary](../../../docs/reports/review-2710/obstacles-summary.md), §4)
locates, ingredient by ingredient, what of Weil's argument over `𝔽_q` exists over `ℤ`. A positive
Hermitian structure with Hecke similitudes exists after regularization. Local Hodge index holds at
every prime. Tensor amplification exists with a non-scaling loss. Missing are a finite
self-intersection of the diagonal, archimedean payment of the local-to-global divergence, and
stability of the computed equilibrium. All three are statements about one object: the
**counterterm** the diagonal requires, and the place that pays it.

RAPT owns that object. Its core is Q2 of the report, coupled renormalization of the two places
(B3.25, B3.26, W11, W12). It also takes up the renormalization faces of Q1 (what bounds the field)
and Q3 (the gauge charge of a positive form). In wall terms it is Wall 14 (the diagonal), face
1.16 (polarization) and face 3.23 (positivity and equivariance in one form).

| Programme | What RAPT takes | What RAPT adds |
|---|---|---|
| [RenormalizedBiarithmeticGeometry](../RenormalizedBiarithmeticGeometry/README.md) | regularized families, survival cones, scheme independence, the torsion germ (identity counterterm), the lattice germ (polar hyperplane), periodic germs and Ramanujan modes, the pole node | the **coupled** survival law; the joint germ of the two places and its matched rank-one coupling |
| [ArithmeticIntersectionTheory](../ArithmeticIntersectionTheory/README.md) | orbit intersections, the different `c(n)`, the Hecke cocycle `β`, the regulator anomaly, the spacing regulator, Hecke invariance of `P` | covariance as a constraint on counterterms; the price of the anomaly; the horizon regulator and its tensor law |
| [ArithmeticElectrostatics](../ArithmeticElectrostatics/README.md) | the torsion pairing and `RenormalizesAt`, the atomic Weil form, the arithmetic point, the stability law at atomic resolution, gauge invisibility and margins, alignment at zero ordinates | the exact constants `log N + O(1)` (covariant) and `≥ (3/2) log N` (torsion); the spectral ends `± log N` |
| [ArithmeticEffectivityTheory](../ArithmeticEffectivityTheory/README.md) | torsion orbits `O_n`, `I(m, n)`, Ramanujan sums, Weil's prime kernel `P` as a renormalized torsion energy | — |
| [ArithmeticPolarization](../ArithmeticPolarization/README.md), [ConjugateDiagonalGeometry](../ConjugateDiagonalGeometry/README.md) | `W`, `D`, `Δ`, the Hecke defect | the place of the prime form among regularized families |
| [ArithmeticCastelnuovoSeveri](../ArithmeticCastelnuovoSeveri/README.md), [ArithmeticOrientationGeometry](../ArithmeticOrientationGeometry/README.md) | the scaling surface, Hodge index, `𝔽_q` calibration, the pole plane | the renormalized reading of `Δ² = 2 − 2g` |
| [BiarithmeticGaugeGeometry](../BiarithmeticGaugeGeometry/README.md) | the gauge torus, square-class blindness, sign twins | gauge behaviour of the matching between places |
| [SpacingScaleHarmonicAnalysis](../SpacingScaleHarmonicAnalysis/README.md) | the stability law at a fixed fraction `c₀δ_N` of the spacing (tilted weight `1 + n/N`); the critical exponent of the overlap regime | the counterterm calculus it matches: the covariant `log N + O(1)`, the constant-one self-energy, the finite parts |
| `RHTower` | Mertens' first theorem; Mertens' theorem with Euler's constant | — |

RAPT does not re-prove what these programmes own; it imports them and proves the laws that join
them.

---

## 2. Why

**Weil's diagonal over `𝔽_q`.** On `C × C` the diagonal is a curve and adjunction gives
`Δ² = 2 − 2g`, a finite number. The tensor-power argument works because this loss does not grow
with the power, and the Hodge index theorem gives the sign on the primitive part.

**Over `ℤ` the diagonal is a divergence.** Every pairing of the explicit formula is singular on the
diagonal:

* at the **prime place** the charges are torsion orbits `O_n` on the circle, with Green function
  `−log |1 − z w̄|`; the Abel radius `r < 1` makes the self-energy of a point finite,
  `log(1/(1 − r))`;
* at the **archimedean place** the charges are atoms at `log n` on the line; a width `ε` makes the
  self-energy of an atom finite, `log(1/ε) + O(1)`;
* the **arithmetic point** `z = 1`, the orbit `O_1`, is fixed by every power map; the torsion
  divergence and the archimedean divergence meet there (the pole).

Positivity lives before the limit, since Abel energies are Gram matrices. Equivariance lives after
it, since Weil's prime kernel is Hecke invariant. RBG proved that positivity passes the limit
exactly on the null cone of the counterterm, and that the Abel torsion germ has the identity as
counterterm, so nothing survives. AIT proved that the counterterm is not Hecke covariant: the
regulator anomaly `log t` of `[t]`, minus the tame different. The report's central conjecture asks
for an **admissible coupling** of the places: low-rank counterterm, covariant finite part, and a
survival cone containing the degree-zero cycles.

**What a theory of renormalization data has to decide, and what it decides.**

1. *Can coupling the places lower the prime counterterm?* No. A positive coupled family whose prime
   block keeps the torsion germ has counterterm rank at least the number of orders. The torsion
   directions that survive span at most the rank of the partner's counterterm. The archimedean
   germ has rank one and pays exactly one direction, the arithmetic point.
2. *Is the rank of the counterterm intrinsic?* No; it belongs to the regulator. At the
   **horizon** (orders `≤ N`, Weil's own regularization) the prime form has no diagonal. Its
   divergence is the tensor product of the identity on torsion orbits, weighted by their sizes, and
   the polar projection on log-scale profiles. These are exactly the counterterms of the Abel
   torsion germ and of the archimedean lattice germ. The survival cone is nontrivial: the
   class-wise polar hyperplane, the degree-zero part of each class.
3. *Can the anomaly be cancelled?* At the horizon it cancels exactly. `[p]` moves the class `j` to
   `j + 1`, whose orbit density is `1/p` of the previous one, while the polar functional scales by
   `p^{−1/2}`. The tensor counterterm, and with it the renormalized finite part, is invariant.
4. *What does covariance cost?* A Hecke-covariant renormalized prime form has a scalar diagonal. Its
   least positive counterterm on orders `≤ N` is `log N + O(1)`: the anomaly `log #ker[N]` of `[N]`,
   with constant one. This is the size of the archimedean self-energy `log(1/ε)` of an atom at the
   atomic spacing `ε ≍ 1/N` (§9.1). The archimedean self-energy has constant one as well. With the
   interaction of the atoms in absolute value it pays the prime place down to width `δ_N/(C log N)`
   (RP18). With the tilted weight `1 + n/N` it pays down to a fixed fraction `c₀δ_N` of the spacing
   (SSHA). Keeping
   the self-intersection, the anomalous torsion renormalization, costs between `½ log N` and
   `log N` more.
5. *What is the finite part?* On the polar hyperplane of uniform profiles, the renormalized prime
   form is the scalar `−2γ`, up to `o(1)` per unit mass. In Weil's form, where `P` enters with a
   minus sign, the renormalized prime place is positive there. On the `p`-adic classes the finite
   part is `−2γ_p · 1 + log p (K_{p^{−1/2}} − 1)`, with `γ_p = γ + log p/(p − 1)`: the tower form of `p`
   (AIT), the local Hodge index, now as the finite part of a renormalization. For any finite prime
   set `Q`, the density-normalized class finite part is the sum of its transverse tower forms
   minus `2γ_Q · 1`, with the shared constant `γ_Q = γ + Σ_{p∈Q} log p/(p−1)`.
   Matching the scalar `log M` leaves the actual operator
   `A_Q = diag(log n) − P_Q + γ_Q · 1` on `ℓ²` of the positive `Q`-supported integers.
   Its complete Blaschke product basis has simple energies
   `γ + log m + tameDifferent(m) = γ + 2 log m − selfIntersection(m)`.
   This diagonalization identifies the entire maximal logarithmic domain;
   `A_Q + (1−γ)·1` has a compact inverse.
   The same energies occur in the full integer prime matrices: the Ramanujan
   profiles `u_m(n)=c_m(n)/√(φ(m)n)` have squared norm asymptotic to `log N`
   and squared residual `o(log N)` at `log N−γ−log m−tameDifferent(m)`.
   Every fixed finite conductor packet therefore gives distinct actual spectral
   points at these offsets, with any prescribed eventual accuracy.
6. *Is the matching of the places gauge blind?* No. Each place's counterterm is gauge blind, but
   their matching is not: the prime place of `ζ` diverges along the archimedean polar direction
   with coefficient `+1`, the Liouville twin with coefficient `−1`.

These answers replace the report's central conjecture by a statement in which every divergence is
computed and matched, the prime finite part is computed, and only the finite parts of the
archimedean place and the pole are open (§9.1).

---

## 3. Objects and language

### 3.1 Carriers and charges

| Object | Definition | Lean |
|---|---|---|
| characteristic circle | `ℝ/ℤ`, torsion `μ_∞`, orbits `O_n`, the arithmetic point `O_1 = {1}` | `primitiveRoots` (AET) |
| orbit intersection | `I(m, n) = Σ_{ζ∈O_m, η∈O_n} log |ζ − η|`, `= φ(m) Λ(n/m)` for `m ∣ n` | `orbitIntersection` (AET) |
| self-intersection density | `c(n) = I(n, n)/φ(n) = log n − Σ_{p∣n} log p/(p − 1)` | `selfIntersection` (AIT) |
| Weil's prime kernel | `P(m, n) = Λ(n/m)(n/m)^{−1/2}` on `m ∣ n`, `m ≠ n`, symmetric | `weilPrimeKernel` (AET) |
| atomic prime form | `P_N(x) = Σ_{m,n ≤ N} x_m x_n P(m, n)` | `atomicWeilForm` (AES), `primeBilinear` |
| torsion pairing | `Σ y_m y_n I(m, n)` against the self-mass `Σ φ(n) y_n²` | `torsionPairing`, `selfMass`, `RenormalizesAt` (AES) |
| pole vector | `u_n = n^{−1/2}`; truncated `u^{(M)} = u 𝟙_{n ≤ M}` | `poleVector`, `truncPole` |
| polar functional | `ℓ(x) = Σ x_n n^{−1/2}`, one factor of Weil's pole term `(Σ x_n √n)(Σ x_n/√n)` | `polarFunctional` |
| step profile | `Σ_i c_i u^{(M_i)}`: the log-scale profile `g = Σ c_i 𝟙_{[0, a_i]}`, `M_i = N^{a_i}` | `stepProfile` |
| class pole vector | `w_j^{(M)} = u^{(M)} 𝟙_{v_p(n) = j}`: the valuation class `j`, dual to the orbit `O_{p^{J+1−j}}` of `μ_{p^{J+1}}` | `classPole` |
| class density | `δ_j = (1 − 1/p)/p^j = φ(p^{J+1−j})/p^{J+1}` | `classDensity`, `classDensity_eq_orbit` |
| class polar functional | `ℓ_j(x) = Σ_{v_p(n) = j} x_n n^{−1/2}` | `classPolar` |
| class-wise profile | `Σ_{j ≤ J} Σ_i c_{ji} w_j^{(M_i)}` | `classProfile` |
| Hecke shift | `(T_t x)(n) = x(n/t)` on multiples of `t` | `heckeShift` |
| tensor counterterm | `C(x) = Σ_{j ≤ J} δ_j^{−1} ℓ_j(x)²` | `tensorCounterterm` |
| matched finite-sieve operator | `A_Q = diag(log n) − P_Q + γ_Q · 1` on the maximal logarithmic domain in `ℓ²(S_Q)` | `sieveAdjunctionOperator` |
| full-horizon Ramanujan profile | `u_m(n)=c_m(n)/√(φ(m)n)`, `1≤n≤N`; arithmetic trial energy `E(m)=γ+log m+tameDifferent(m)` | `ramanujanHorizonVector`, `ramanujanAdjunctionEnergy` |
| Liouville pole vector | `λ(n) n^{−1/2}`, `λ = (−1)^Ω` | `liouvilleSign`, `liouvilleTrunc` |

### 3.2 Renormalization data

| Object | Definition | Lean |
|---|---|---|
| regularized family, counterterm, survival cone | `Q_s − σ_s B → A`; the null cone of `B` (RBG) | `quad`, `survivalCone` (RBG) |
| coupled counterterm | `[[A, C], [Cᵀ, D]]` on a prime block and a partner block | `coupled` |
| prime survival | projection of the survival space to the prime block | `primeSurvival` |
| matched coupling | `[[1, b vᵀ], [v bᵀ, v vᵀ]]` with `|b| = 1` | `primeSurvival_rankOne` |
| joint germ | torsion orbits with modes `c_n/√φ(n)` and archimedean nodes with the constant mode | `jointGerm`, `jointGram` |
| renormalized prime form | `−P + diag(h)`; **covariant** when invariant under every Hecke transport | `renormalizedPrimeForm` |
| covariant counterterm `κ_cov(N)` | least scalar `κ` with `P_N ≤ κ |x|²` | `covariantCounterterm_sandwich` |
| torsion counterterm `κ_tor(N)` | least `κ` renormalizing the torsion pairing on orders `≤ N` | `torsionCounterterm_window` |
| Hecke excess `e(t)` | `Λ(t)(φ(t)^{−1/2} − t^{−1/2})`: the torsion kernel minus Weil's kernel, at most | `heckeExcess`, `sum_heckeExcess_le` |
| horizon counterterm | the divergent part of `P_N` on a fixed profile space as `N → ∞` | `abs_atomicWeilForm_classProfile_sub_le` |

### 3.3 The regulators

| Regulator | Counterterm | Rank | Survival cone | Anomaly of `[t]` | Owner |
|---|---|---|---|---|---|
| Abel radius `r` | `φ(n) δ_{mn}` | number of orders | `{0}` | `log t − (tame different)` | RBG, AIT |
| spacing radius `e^{−ε/n}` | scalar | number of orders | `{0}` | tame different | AIT |
| horizon, uniform profiles | `ℓ(x)²` | `1` | `∫ g = 0` | — | RAPT RP5 |
| horizon, class-wise profiles | `Σ_j δ_j^{−1} ℓ_j(x)²` | number of classes | `ℓ_j(x) = 0` for all `j` | none for `[p]` | RAPT RP7, RP9 |

### 3.4 Words

*Regulator*, *counterterm*, *survival cone* as in RBG. A counterterm is *scalar*, *polar* (rank one,
along the polar functional), *orbital* (diagonal on the torsion orbits) or a *tensor* counterterm
(orbital on the arithmetic factor, polar on the profile factor). A renormalization is *covariant*
when its finite part is Hecke invariant, *anomalous* otherwise. A coupling *pays* a prime direction
when that direction lies in the prime survival. Two divergences are *matched* when their leading
terms agree in rank and constant; *anti-matched* when they agree with opposite sign. *Uniform*
profiles depend on `log n` only; *class-wise* profiles also on the `p`-adic valuation. The *arithmetic
factor* of a profile space is its decomposition by classes; the *profile factor* is its log-scale
shape.

Every theorem states its regulator, its counterterm with rank and survival cone, its anomaly, and
the place that pays.

---

## 4. Mechanisms

### A. Coupling the places

1. **The partner kernel is blind to the coupling** (`coupling_mulVec_eq_zero`, `rank_coupling_le`).
   In a positive coupled counterterm `D w = 0 ⇒ C w = 0`, so `rank C ≤ rank D`.
2. **Coupled survival** (`mem_survivalCone_coupled_iff`, `eq_zero_of_inl_mem_survivalCone`,
   `finrank_survival_le_card`, `card_le_rank_coupled`, `finrank_primeSurvival_le_rank`). Survival
   vectors solve `A u + C w = 0`, `Cᵀ u + D w = 0`. If the prime block is nondegenerate, no pure prime
   vector survives, the counterterm has rank `≥ #prime`, and the prime survival has dimension
   `≤ rank D`.
3. **Rank one pays one matched direction** (`coupling_eq_vecMulVec`, `dotProduct_self_le_one`,
   `primeSurvival_rankOne`). With `A = 1` and `D = v vᵀ`: `C = b vᵀ`, `|b| ≤ 1`, prime survival `ℝ b` if
   `|b| = 1`, `0` otherwise.
4. **The torsion germ** (`primeBlock_eq_smul_one`, `coupled_torsion_survival`,
   `coupled_lattice_primeSurvival_le_one`). In every positive symmetric coupled family whose prime
   block is the torsion germ, the prime block of the counterterm is `c · 1` with `c > 0` (scheme
   independence). Hence rank `≥ #S`, and coupled to the lattice germ at most one torsion direction
   survives.
5. **The archimedean place pays the arithmetic point** (`ramanujanMode_one`, `jointGram_eq`,
   `primeSurvival_jointGram`, `jointGerm_quad_nonneg`, `tendsto_jointGerm`, `jointGerm_survival`).
   Ramanujan orthogonality makes the joint counterterm the matched rank-one coupling with `b = e₁`.
   The mode of `O_n`, `n ≥ 2`, has mean zero, while `c_1 ≡ 1` is the archimedean mode itself.

6. **Gårding is a finite-rank survival** (`survival_of_functionals`, `functionals_of_survival`,
   `garding_iff_survival`, `garding_iff_regularized`, `finrank_le_of_garding`). A form is nonnegative
   on a subspace of codimension `≤ k` iff it is nonnegative on the survival cone of a positive
   counterterm of rank `≤ k`, iff `A + sB + εI` is eventually positive. Then it has at most `k`
   negative directions. The finite negative index of Weil's form at every aperture (APol, ACS) is
   survival with a finite-rank counterterm, and RH is the statement that the counterterm vanishes.

### B. Covariance and the anomaly

7. **Covariance forces a scalar** (`renormalizedPrimeForm_transport`,
   `renormalizedPrimeForm_covariant_iff`, `heckeCovariant_iff_const`). Transport moves the diagonal
   from `h(n)` to `h(tn)`; covariance holds iff `h` is constant. A scalar counterterm has survival
   cone `{0}`, so covariance and survival exclude each other for diagonal counterterms.
8. **The exact rows** (`sum_up_eq`, `sum_down_eq`, `row_eq`). The Schur-weighted row of `P` at `m` on
   orders `≤ N` is `A(⌊N/m⌋) + log m`, with `A(y) = Σ_{t ≤ y} Λ(t)/t`.
9. **The covariant counterterm is `log N + O(1)`** (`row_le`, `row_ge`, `poleVector_eigen`,
   `atomicWeilForm_le_log`, `atomicWeilForm_poleVector_ge`, `log_sub_le_of_atomicWeilForm_le`,
   `covariantCounterterm_sandwich`). The pole vector is an approximate eigenvector with eigenvalue
   `log N`, coordinatewise. Its finite part is sharp (`covariantCounterterm_sharp`): the tilted pole
   `n^{−1/2}(1 + ηn/N)` is a Collatz–Wielandt vector, so `P_N ≤ (log N − γ + o(1))|·|²` on every
   vector, and the pole attains it: `κ_cov(N) = log N − γ + o(1)`.
10. **The anomaly costs half a logarithm** (`totient_mul_le`, `poleVector_mul_kernel_le`,
   `torsionPairing_torsionTest_ge`, `sum_log_div_ge`, `sum_tameDifferent_div_le`,
   `torsionCounterterm_ge`, `anomaly_cost`). By `φ(mt) ≤ t φ(m)` the torsion pairing dominates `P`
   entrywise. Its diagonal adds `Σ c(n)/n ≈ ½ log² N`, and the tame part averages to `O(H_N)`.
11. **The anomaly costs at most one logarithm** (`normalizedIntersection_le`, `heckePair_le`,
    `offDiag_le`, `heckeExcess_prime_pow_le`, `sum_heckeExcess_le`, `renormalizesAt_two_log`). In
    the charges `z_n = √φ(n) y_n` the torsion kernel is `Λ(t)√(φ(m)/φ(mt))` on Hecke pairs. By
    `φ(m)φ(t) ≤ φ(mt) ≤ tφ(m)` it lies between `P(m, mt)` and `P(m, mt) + e(t)`, with
    `e(t) = Λ(t)(φ(t)^{−1/2} − t^{−1/2})`. The excess lives on prime powers,
    `e(p^k) ≤ (log p/(p − 1)) p^{−k/2}`, and is summable. So the torsion pairing is Weil's form plus
    the diagonal `c(n) ≤ log N` plus a bounded operator: `κ_tor(N) ≤ 2 log N + C`.

### C. The horizon

12. **Polarity on uniform profiles** (`primeBilinear_truncPole_eq`,
    `abs_primeBilinear_truncPole_sub_le`, `abs_atomicWeilForm_stepProfile_sub_le`,
    `abs_atomicWeilForm_stepProfile_le_of_polar`). The pole Gram is `H_M H_{M'} + O(H_{min})`. So
    `P_N = ℓ² + O(|c|-mass)` on step profiles, with no divergence on `ℓ = 0`.
13. **Orbital divergence** (`sum_dvd_vonMangoldt_div_le`, `sum_divisors_dvd_vonMangoldt_le`,
    `offClassRow_le`, `classRow_self_ge`, `primeBilinear_classPole_self_ge`,
    `primeBilinear_classPole_le`, `atomicWeilForm_classCombination_ge`,
    `horizonCounterterm_rank_unbounded`). Leaving a valuation class costs one prime power of `p`.
    Each class is an approximate eigenvector with eigenvalue `log M`, and classes decouple. So no
    counterterm of rank `≤ J` plus a bounded scalar renormalizes the prime place.
14. **The tensor law** (`classDensity_eq_orbit`, `abs_unitHarmonic_sub_le`, `abs_classMass_sub_le`,
    `primeBilinear_classPole_two_eq`, `abs_classGram_self_sub_le`, `classGram_cross_le`,
    `abs_atomicWeilForm_classProfile_sub_le`, `abs_atomicWeilForm_classProfile_le_of_polar`).
    On class-wise profiles the horizon counterterm is `Σ_j δ_j^{−1} ℓ_j²`, the class polar squares
    weighted by inverse orbit densities.

### D. Covariance at the horizon

15. **No anomaly** (`atomicWeilForm_heckeShift`, `heckeShift_classPole`, `classDensity_succ`,
    `classPolar_heckeShift_succ`, `classPolar_heckeShift_zero`, `tensorCounterterm_heckeShift`,
    `finitePart_heckeShift`). `P_{pN}(T_p x) = P_N(x)`; `T_p w_j^{(M)} = √p w_{j+1}^{(pM)}`;
    `ℓ_{j+1}(T_p x) = ℓ_j(x)/√p` and `δ_{j+1} = δ_j/p`. Hence `C(T_p x) = C(x)`, and the finite part
    `P − C` is invariant under `[p]`.

### E. The finite part

16. **Euler's constant** (`tendsto_mertensSum_sub_log`, `tendsto_harmonicSum_sub_log`, `roundoff_le`,
    `exists_abs_primeBilinear_truncPole_finitePart_le`,
    `exists_abs_atomicWeilForm_stepProfile_finitePart_le`,
    `exists_abs_atomicWeilForm_stepProfile_add_le_of_polar`). With `Σ_{t ≤ y} Λ(t)/t = log y − γ + o(1)`
    and `H_M = log M + γ + o(1)`, the pole Gram is `H_M H_{M'} − 2γ H_{min} + o(H_{min})`. Hence
    `P_N = ℓ² − 2γ |x|² + o(|c|-mass)` on step profiles.

17. **The tower form** (`tendsto_pPowerMertensSum`, `tendsto_unitMertensSum_sub_log`,
    `tendsto_unitHarmonic_sub`, `tendsto_classMass_sub`, `sum_divisors_dvd_vonMangoldt_eq`,
    `classRow_self_eq`, `classRow_of_lt`, `primeBilinear_classPole_cross_eq`,
    `exists_abs_classGram_self_finitePart_le`,
    `exists_abs_atomicWeilForm_classCombination_finitePart_le`). Inside a class the row is exactly
    `A_{p'}(⌊M/m⌋) + log m − j log p`, with `A_{p'}(y) = log y − γ_p + o(1)`. Across classes it is exactly
    one prime power, `log p`. The finite part on class combinations is `−2γ_p Σ a_j² |w_j|²` plus
    `log p Σ_{j ≠ j'} a_j a_{j'} |w_{max}|²`; normalized, the coupling is `log p · p^{−|j−j'|/2}`.
18. **The sign of the tower finite part** (`localEuler_sub_eq`, `towerFinitePart_ge`, `kmsForm_one`,
    `towerFinitePart_one`, `towerFinitePart_add_nonneg_iff`, `towerFinitePart_nonneg_iff`,
    `towerDeficit_two_pos`, `towerDeficit_nonpos`). In Weil's form the tower finite part is
    `F_p = 2γ_p + log p (1 − K_q)`. The Kac–Murdock–Szegő bound gives `F_p ≥ −2d_p`, with the
    **tower deficit** `d_p = √p log p/(p − 1) − γ`. The uniform class profile attains it:
    `F_p(1_N) = −2N d_p + O(1)`. So `F_p + c ≥ 0` on every depth iff `c ≥ 2d_p`: the prime finite
    part is nonnegative on the classes of `p` iff `√p log p ≤ γ(p − 1)`. This fails at `p = 2` and
    holds for `p ≥ 2^16` (numerically exactly for `p ≥ 47`).
19. **The archimedean place pays the tower deficit** (`sum_cross_le_valuation`,
    `towerFinitePart_add_valuation_ge`, `eventually_atomicWeilForm_classCombination_le`). The
    archimedean self-energy is uniform in the classes; against it the prime form keeps the
    valuation potential `j log p`, and `F_p + Σ_j j log p b_j² ≥ (γ + γ_p)|b|²`. Hence
    `P_M ≤ (log M − γ + η)|·|²` on every `p`-class combination: the pole is the extremal class profile.
20. **Hodge index on the classes** (`eventually_isHyperbolic_classHodgeGram`,
    `eventually_atomicWeilForm_classCombination_sharpGap_le`). On the span of the class pole vectors of
    depth `≤ J`, `P_M − (log M − γ − η)` has at most one positive square; on the polar hyperplane the
    gap is `p log p/(p − 1)` at every depth. The valuation tower operator is exactly solvable
    (`towerOp_pole`, `towerOp_step`): spectrum `{γ} ∪ {γ_p + k log p : k ≥ 1}`, eigenvectors the pole
    profile and the valuation steps.

### F. Stability

21. **The matched stability law** (`markovEnergy_atomicTest_ge_matched`, `matchedAtomicGain_nonneg`,
    `atomicWidth_le_matchedAtomicWidth`, `markovEnergy_atomicTest_nonneg_matched`). The archimedean
    Lévy gain `e^{−1/2} log(δ_N/(2w))` of an atomic test pays the covariant counterterm
    `log N + O(1)`. So the Markov form (archimedean minus prime) is nonnegative at every width
    `w ≤ (δ_N/4) N^{−e^{1/2}} e^{−C}`, half the exponent needed with the bound `2 log N` (AES).

22. **The self-energy has constant one** (`archLevyDensity_ge_of_le`,
    `levyEnergy_ge_of_disjoint_shifts_sharp`, `levyEnergy_atomicTest_ge_sharp`,
    `markovEnergy_atomicTest_nonneg_sharp`, `sharpAtomicWidth_ge`). On the shifts `x ≤ δ_N/2`
    that separate atoms the Lévy density is `ω(x) ≥ e^{−δ_N/4}/(2x)`, so the gain is
    `e^{−δ_N/4} log(δ_N/(2w))`, constant `1 − O(1/N)`. Against the covariant counterterm this
    gives nonnegativity at every width `w ≤ c δ_N/N`. The remaining factor `N` is `1/δ_N`: the
    self-energy is counted relative to the spacing because the longer shifts make atoms overlap.
23. **The stability law reaches the spacing up to a logarithm** (`integral_sub_shift_sq`,
    `abs_bumpPairing_le`, `bumpPairing_eq_zero`, `archLevyDensity_le`, `archLevyDensity_ge_sub`,
    `archLevyDensity_mul_cross_le`, `integral_crossMajorant_le`, `sum_erase_inv_abs_sub_le`,
    `sum_crossCoeff_le`, `levyEnergy_atomicTest_ge_cross`, `markovEnergy_atomicTest_nonneg_logSpacing`).
    Keep every shift `s ∈ (w, 1]`. Then `‖f − f(· + s)‖² = 2‖f‖² − 2Σ x_m x_n c_{mn}(s)`, the
    self-energy is the full `log(1/w) − 1/2`, and the atoms interact only at `s ≈ log(n/m)`, where
    `ω(s) ≤ 2/(3 log(n/m)) + 1`. Each pair costs `2w` in `s`. Since `|log n − log m| ≥ |n − m|/N`,
    the interaction is a Hilbert-type kernel of norm `≤ 4wN((4/3)H_N + 1)`. At width
    `w ≤ e^{−C₁}/(N(1 + log N))` it is bounded, the self-energy exceeds `log N + C₁`, and the Markov
    form of every atomic test is nonnegative.

### G. Gauge

24. **The twisted Mertens sum** (`sum_one_add_liouville_le`, `liouvilleMertensSum_le`,
    `neg_le_liouvilleMertensSum`). `Σ_{t ≤ y} λ(t)Λ(t)/t = −log y + O(1)`: the even prime powers are
    summable.
25. **Dirichlet's hyperbola identity** (`sum_divisors_div_swap`). The divisor part of a row averages
    to its Mertens part.
26. **The spectral ends** (`abs_atomicWeilForm_le`, `atomicWeilForm_liouvillePole_le`,
    `atomicWeilForm_spectrum_ends`). `|P_N| ≤ log N + O(1)`. The pole vector reaches the top and the
    Liouville pole vector the bottom, `−log N + O(1)`.
27. **The polar divergence flips** (`primeBilinear_liouvilleTrunc_eq`,
    `abs_primeBilinear_liouvilleTrunc_add_le`, `abs_liouvilleForm_stepProfile_add_le`). On uniform
    profiles `P(λx) = −ℓ(x)² + O(|c|-mass)`.
28. **The matching law** (`IsSignGauge`, `sum_weilPrimeKernel_gauge`, `primeBilinear_gaugeTrunc_eq`,
    `abs_primeBilinear_gaugeTrunc_sub_le`, `abs_gaugeForm_stepProfile_sub_le`, `euler_matching`,
    `liouville_matching`, `finiteFlip_matching`). If `A_ε(y) = κ log y + O(1)`, then
    `P(εx) = κ ℓ(x)² + O(|c|-mass)` on uniform profiles. The Euler gauge has `κ = 1`, Liouville
    `κ = −1`, and every gauge flipping finitely many primes `κ = 1`.
29. **Mertens' theorem for characters** (`norm_sum_antitone_mul_le`, `norm_LFunction_sub_partial_le`,
    `norm_LFunction_one_sub_partial_le`, `norm_charLogSum_le`, `charLogSum_eq`,
    `exists_norm_charMertensSum_le`). For `χ ≠ 1` mod `q`, Abel summation gives
    `‖L(σ, χ) − Σ_{n<M} χ(n)n^{−σ}‖ ≤ 2q/M` for `σ > 1`, and continuity of `L(·, χ)` carries it to
    `σ = 1`. The hyperbola identity writes `Σ_{n ≤ M} χ(n) log n/n`, which is `O(q)`, as
    `L(1, χ) A_χ(M) + O(q)`. With `L(1, χ) ≠ 0`, `A_χ(M) = Σ_{t ≤ M} χ(t)Λ(t)/t` is bounded.
30. **Characters are invisible to polar matching** (`charGauge_isSignGauge`,
    `charGauge_mul_vonMangoldt`, `charGauge_matching`, `abs_charGaugeForm_stepProfile_le`). For a
    real `χ ≠ 1` mod a prime `ℓ`, the gauge `ε(n) = χ(n/ℓ^{v_ℓ(n)})` is a sign gauge with
    `A_ε = Re A_χ + O(1)`, so its matching coefficient is `κ = 0`. The gauged step profiles have no
    polar divergence: the horizon counterterm is blind to characters.
31. **Mertens' theorem in residue classes** (`totient_mul_classMertensSum_eq`,
    `abs_principalMertensSum_sub_log_le`, `exists_abs_classMertensSum_sub_le`). Orthogonality gives
    `φ(q) A(y; r) = Σ_χ χ(r^{−1}) A_χ(y)`. The principal term is Mertens' sum without the powers of
    the primes dividing `q`, and the others are `O(1)`. So every unit class carries
    `A(y; r) = log y/φ(q) + O(1)`: the same divergence, the prime place does not separate them.

### H. Residues and finite parts

32. **Residue classes are invisible to the divergence** (`classHarmonic`,
    `abs_classHarmonic_add_one_sub_le`, `primeBilinear_residuePole_eq`,
    `exists_abs_atomicWeilForm_unitClassProfile_sub_le`). The shift `m ↦ m + 1` moves a class harmonic
    sum by at most `2`, so every class has `S_a(M) = log M/q + O(q)`. A prime power `t` carries the
    class `a` into `at`, so the residue Gram is a sum of class Mertens sums, and the counterterm on
    the unit classes is the single square `(q/φ(q)) ℓ²`. A class function is seen through its mean
    only (RP24, RP25).
33. **Every profile is a step profile** (`stepProfile_horizonDiff`, `horizonVariation_le`).
    Summation by parts writes `G(n)/√n` as a step profile whose coefficient mass is the variation of
    `G`, so the horizon laws hold for every profile of bounded variation (RP27).
34. **The remainder is the convolution of the Mertens error** (`abs_primeBilinear_gaugeTrunc_sub_transfer_le`,
    `gaugePole_finitePart_iff`). The gauged pole Gram is `Σ_{m ≤ M} (A_ε(⌊M'/m⌋) + A_ε(⌊M/m⌋))/m`
    exactly. After the matched divergence `κ H H'` the remainder is the harmonic convolution of
    `E = A_ε − κ log`. The divergence reads the leading order of `A_ε` (RP26); the finite part on
    the pole is `2α` exactly when `E` has harmonic mean `α`, and in particular when `E → α` (RP30).
35. **The finite part reads `−L′/L` at `s = 1`** (`charMertensSum_eq_abel`,
    `tendsto_LSeries_twist_vonMangoldt`, `charMertensLimit_eq_neg_logDeriv`). Abel summation against
    the prime number theorem for characters makes `A_χ` converge. Abel's theorem for the Dirichlet
    series of `χΛ` and the continuity of `−L′/L` at `1` identify the limit. `ζ` contributes `−γ`, the
    constant term of `−ζ′/ζ` at its pole; a character contributes `−L′/L(1, χ)` (RP31).
36. **Characters diagonalize the residue finite part** (`classMertensConstant_eq_sum`,
    `sum_classMertensConstant_mul_char`, `sum_residueFinitePart_mul_char`). The class Mertens
    constants are the character transform of the values `β_χ`. The finite-part matrix
    `c_{a⁻¹b} + c_{b⁻¹a}` is a convolution on `(ℤ/q)ˣ`, so the characters are its eigenvectors with
    eigenvalues `2 Re β_χ`. The second-order class asymptotics make the logarithmic model Gram
    exact to `O(1)` (RP34, RP35).
37. **The finite part selects `ζ`** (`finitePartLimit_le_and_eq_iff`, `liouvilleLimit_le_and_eq_iff`).
    `A_ε = A − Σ (1 − ε(t))Λ(t)/t` with non-negative terms. So among matched gauges the Mertens limit
    is at most `−γ`, with equality only when `ε = 1` at every prime. Dually, Liouville is the bottom
    of the anti-matched family (RP33, RP36). Residue patterns are matched by their mean (RP38).

---

## 5. Pillar theorems

| Pillar | Statement | Lean |
|---|---|---|
| **RP1 Coupled survival** | partner-kernel inclusion; survival equations; rank `≥ #prime`; prime survival `≤ rank` of the partner; rank one pays one matched direction; for the torsion germ, coupled to any partner | `coupling_mulVec_eq_zero`, `card_le_rank_coupled`, `finrank_primeSurvival_le_rank`, `primeSurvival_rankOne`, `coupled_torsion_survival`, `coupled_lattice_primeSurvival_le_one` |
| **RP2 The archimedean place pays the arithmetic point** | joint counterterm `= [[1, e₁𝟙ᵀ], [𝟙e₁ᵀ, 𝟙𝟙ᵀ]]`; prime survival `ℝ e₁`; matched survival of the joint germ | `jointGram_eq`, `primeSurvival_jointGram`, `jointGerm_survival` |
| **RP3 The covariant counterterm is the anomaly** | covariance ⇔ constant diagonal; `log N − log 8 − 4 ≤ κ_cov(N) ≤ log N + log 4 + 4`, sharpened to `κ_cov(N) = log N − γ + o(1)`; the pole vector is extremal | `renormalizedPrimeForm_covariant_iff`, `heckeCovariant_iff_const`, `poleVector_eigen`, `covariantCounterterm_sandwich`, `covariantCounterterm_sharp` |
| **RP4 The anomaly costs half a logarithm** | `κ_tor(N) ≥ (3/2) log N − C`; `κ_tor − (log N + log 4 + 4) ≥ ½ log N − C` | `torsionCounterterm_ge`, `anomaly_cost` |
| **RP5 Horizon polarity** | on uniform step profiles `P_N = ℓ² + O(|c|-mass)`; no divergence on `ℓ = 0` | `abs_atomicWeilForm_stepProfile_sub_le`, `abs_atomicWeilForm_stepProfile_le_of_polar` |
| **RP6 Orbital divergence** | every class combination has `P ≥ (log M − C)|x|²`; the horizon counterterm has unbounded rank | `atomicWeilForm_classCombination_ge`, `horizonCounterterm_rank_unbounded` |
| **RP7 The tensor law** | `P_N = Σ_j δ_j^{−1} ℓ_j² + O(H_N |c|²)` on class-wise profiles; `δ_j = φ(p^{J+1−j})/p^{J+1}`; survival on the class-wise polar hyperplane | `abs_atomicWeilForm_classProfile_sub_le`, `classDensity_eq_orbit`, `abs_atomicWeilForm_classProfile_le_of_polar` |
| **RP8 Spectral ends and the Liouville flip** | spectral ends `±(log N + O(1))`; the Liouville twin diverges as `−ℓ²` on uniform profiles | `atomicWeilForm_spectrum_ends`, `abs_liouvilleForm_stepProfile_add_le` |
| **RP9 No anomaly at the horizon** | `[p]` shifts the classes and scales the orbit densities by the degree; the tensor counterterm and the finite part are invariant | `tensorCounterterm_heckeShift`, `finitePart_heckeShift`, `heckeShift_classPole` |
| **RP10 The finite part is Euler's constant** | `P_N = ℓ² − 2γ|x|² + o(|c|-mass)` on step profiles; `P_N = −2γ|x|² + o(·)` on the polar hyperplane | `exists_abs_atomicWeilForm_stepProfile_finitePart_le`, `exists_abs_atomicWeilForm_stepProfile_add_le_of_polar` |
| **RP11 Matching reads the density of the gauge** | the polar matching coefficient `κ` of a sign gauge, read off `A_ε(y) = κ log y + O(1)`, governs its horizon divergence; finitely many flips leave `κ = 1` | `abs_gaugeForm_stepProfile_sub_le`, `finiteFlip_matching`, `liouville_matching` |
| **RP12 The finite part is the tower form** | on class combinations `P_M = Σ_j δ_j^{−1} ℓ_j² − 2γ_p Σ_j a_j²|w_j|² + log p Σ_{j≠j'} a_j a_{j'} |w_{max}|² + o(·)`; the cross-class Gram is exact | `exists_abs_atomicWeilForm_classCombination_finitePart_le`, `primeBilinear_classPole_cross_eq`, `classRow_self_eq` |
| **RP13 The matched stability law** | the Markov form of every atomic test of width `≤ (δ_N/4) N^{−e^{1/2}} e^{−C}` is nonnegative | `markovEnergy_atomicTest_nonneg_matched`, `markovEnergy_atomicTest_ge_matched` |
| **RP14 Gårding is a finite-rank survival** | nonnegative on codimension `≤ k` ⇔ survival with a positive counterterm of rank `≤ k` ⇔ renormalized limit of positive forms; at most `k` negative directions | `garding_iff_survival`, `garding_iff_regularized`, `finrank_le_of_garding` |
| **RP15 The anomaly costs at most one logarithm** | `κ_tor(N) ≤ 2 log N + log 4 + 4 + 2C_e`; the window `[(3/2) log N − C₁, 2 log N + C₂]` | `renormalizesAt_two_log`, `torsionCounterterm_window`, `anomaly_cost_window` |
| **RP16 The sign of the tower finite part** | `F_p + c|·|² ≥ 0` on every depth iff `c ≥ 2d_p`, `d_p = √p log p/(p − 1) − γ`; `d_2 > 0`, `d_p ≤ 0` for `p ≥ 2^16` | `towerFinitePart_add_nonneg_iff`, `towerFinitePart_nonneg_iff`, `towerDeficit_two_pos`, `towerDeficit_nonpos` |
| **RP17 The self-energy has constant one** | Lévy gain `e^{−δ_N/4} log(δ_N/(2w))`; the Markov form of every atomic test of width `≤ sharpAtomicWidth N` is nonnegative, and `sharpAtomicWidth N ≥ c δ_N/N` | `levyEnergy_atomicTest_ge_sharp`, `markovEnergy_atomicTest_nonneg_sharp`, `sharpAtomicWidth_ge` |
| **RP18 The stability law reaches the spacing up to a logarithm** | the Markov form of every atomic test of width `w ≤ e^{−C₁}/(N(1 + log N))` is nonnegative; quantitatively `M(f) ≥ (2θ′(0) + log(1/w) − ½ − 4wN((4/3)H_N + 1) − log N − log 4 − 4)‖f‖²` | `markovEnergy_atomicTest_nonneg_logSpacing`, `markovEnergy_atomicTest_ge_cross` |
| **RP19 Mertens' theorem for characters** | for `χ ≠ 1`, `A_χ(y) = Σ_{t ≤ y} χ(t)Λ(t)/t` is bounded | `exists_norm_charMertensSum_le` |
| **RP20 Characters are invisible to polar matching** | real character gauges mod a prime are sign gauges with matching coefficient `0`; their step profiles carry no polar divergence | `charGauge_matching`, `abs_charGaugeForm_stepProfile_le` |
| **RP21 Mertens' theorem in residue classes** | for `r` a unit mod `q`, `Σ_{t ≤ y, t ≡ r} Λ(t)/t = log y/φ(q) + O(1)` | `exists_abs_classMertensSum_sub_le` |
| **RP22 The torsion counterterm is the golden ratio** | `φ log N − C₁ ≤ κ_tor(N) ≤ φ log N + C₂` for every `N ≥ 1`; `diag(log n) + P_N ≤ φ(log N + log 4 + 4)`, attained up to `O(1)` by `x_n = φ^{ω(n)}/√n` | `torsionCounterterm_golden`, `diag_add_atomicWeilForm_le_golden_log`, `diag_add_atomicWeilForm_goldenTest_ge` |
| **RP23 The fixed-point law** | for every `α ∈ ℝ`, `spec(α diag(log n) + P_N) ⊂ [κ₋(log N + C), κ₊(log N + C)]`, both ends attained up to `O(1)`, `κ± = (α ± √(α² + 4))/2`; at `α = 1`: `[−log N/φ, φ log N]` | `fixedPoint_identity`, `fixedPoint_top`, `fixedPoint_bottom` |
| **RP24 The horizon is blind to residue classes** | on step profiles over the unit classes mod `q`, `P_N = (q/φ(q)) ℓ² + O(\|c\|-mass)`: rank one for every `q`; survival on `ℓ = 0`; inputs `Σ_{m ≤ M, m ≡ a} 1/m = log M/q + O(q)` and `Σ_{m ≡ a} log(M/m)/m = (log M)²/(2q) + O(q log M)` | `exists_abs_atomicWeilForm_unitClassProfile_sub_le`, `exists_abs_residueGram_sub_le`, `abs_classHarmonic_sub_log_le`, `abs_classLogSum_sub_le` |
| **RP25 The horizon sees only the mean of a class function** | twisting by `f(n mod q)` on the units gives the divergence `κ_f (Σ_i c_i log M_i)²`, `κ_f = (Σ_{a ∈ (ℤ/q)ˣ} f(a))²/(q φ(q))`; every character `χ ≠ 1` of every modulus (real and imaginary parts) has none | `exists_abs_atomicWeilForm_classFunctionProfile_sub_le`, `exists_abs_atomicWeilForm_charRe_le`, `exists_abs_atomicWeilForm_charIm_le` |
| **RP26 Polar matching needs only the leading order** | transfer law: the horizon remainder of the gauged pole Gram is `Σ_{m ≤ M} (E(⌊M'/m⌋) + E(⌊M/m⌋))/m + O(H_M)`, `E = A_ε − κ log`; `A_ε(y)/log y → κ` gives `\|P_N(εx) − κℓ²\| ≤ (η log N + C_η) · mass`; on the diagonal, mass-scale remainder ⇔ `Σ_m E(⌊M/m⌋)/m = O(H_M)` ; every sign pattern `g` on the primes with `Σ_{p ≤ y} g(p) log p/p = κ log y + o(log y)` obeys this soft law, and flipping primes of logarithmic density `ϑ` gives `κ = 1 − 2ϑ` | `abs_primeBilinear_gaugeTrunc_sub_transfer_le`, `gaugeForm_stepProfile_of_tendsto`, `gaugePole_bounded_iff`, `gaugeForm_primeSignGauge_soft`, `flipGauge_kappa` |
| **RP27 The horizon laws hold for profiles of bounded variation** | every vector `G(n)/√n` is a step profile with absolute coefficient mass `V_N(G)`, the horizon variation; `\|P_N − ℓ²\| ≤ (log 8 + 5) H_N V_N²`, `\|P_N − ℓ² + 2γ\|x\|²\| ≤ (ηH_N + C_η) V_N²`, the tensor law with `C_{p,J} H_N (Σ_j V_N(G_j))²`; for `G = g(log ·/log N)`, `V_N ≤ Var g + \|g(1)\|`, so smooth signed (class) profiles obey the laws up to `o(mass)` | `abs_atomicWeilForm_profile_sub_le`, `exists_abs_atomicWeilForm_profile_finitePart_le`, `abs_atomicWeilForm_classwiseProfile_sub_le`, `exists_abs_atomicWeilForm_bv_finitePart_le`, `abs_atomicWeilForm_bv_classwise_sub_le` |
| **RP28 The tower deficit changes sign between 43 and 47** | `d_p = u/sinh u − γ`, `u = (log p)/2`, strictly decreasing in `p`; for primes `d_p > 0` iff `p ≤ 43`; the tower finite part of `p` is nonnegative on every depth iff `p ≥ 47` | `towerDeficit_eq_div_sinh`, `towerDeficit_strictAnti`, `towerDeficit_pos_iff`, `towerFinitePart_nonneg_iff_fortySeven_le` |
| **RP29 The prime form has a spectral gap below its pole** | there is `g > 0` with `D_N(x) ≥ g|x|²` and, eventually, `P_N(x) ≤ (log N − γ − g + ε)|x|²` for every `x ⊥ n^{−1/2}`; the harmonic measure `1/n` on `[1, N]` tensorizes over primes up to a constant | `exists_poleDefect_ge`, `exists_atomicWeilForm_le_of_pole_orthogonal`, `exists_harmonicVar_le_glauberForm` |
| **RP30 The finite part is twice the Mertens limit** | if `A_ε(y) − κ log y → α` with `\|κ\| ≤ 1`, the gauged pole Gram is `κ H_M H_{M'} + 2α H_M + o(H_M) + O(1)` and `P_N(εx) = κℓ² + 2α\|x\|² + o(mass)` on uniform profiles; for `ζ` (`κ = 1`, `α = −γ`) this is RP10; converse on the pole: the finite part is `2α` iff the harmonic mean `Σ_{m ≤ M} E(⌊M/m⌋)/m` of the Mertens error is `α H_M + o(H_M)` | `exists_abs_primeBilinear_gaugeTrunc_finitePart_le`, `exists_abs_gaugeForm_stepProfile_finitePart_le`, `exists_abs_sum_div_sub_le_of_tendsto`, `gaugePole_finitePart_iff` |
| **RP31 The character Mertens limit is the logarithmic derivative** | for `χ ≠ 1`, `A_χ(y) → −L′/L(1, χ)` (prime number theorem for characters, Abel summation, Abel's theorem for the Dirichlet series of `χΛ`); a real character gauge mod a prime `ℓ` has finite part `2(Re(−L′/L(1, χ)) + lim_y Σ_{t ≤ y, ℓ ∣ t} Λ(t)/t)` | `tendsto_charMertensSum`, `charMertensLimit_eq_neg_logDeriv`, `exists_abs_charGaugeForm_stepProfile_finitePart_le`, `tendsto_gaugeMertensSum_charGauge_logDeriv` |
| **RP32 The pole hyperplane separates `ζ` from its Liouville twin** | on `Σ x_n/√n = 0`: `P_N(x) ≤ (log N − γ − g + ε)|x|²`, while `P_N(λx) ≥ (log N − γ − ε)|x|²` at some `x ≠ 0`; a margin `g` uniform in `N`, carried by the pole term | `exists_pole_hyperplane_separates_liouville`, `abs_sum_liouvilleSign_div_le`, `atomicWeilForm_truncPole_add` |
| **RP33 The finite part separates ζ from its Liouville twin** | `A_λ(y) + log y → γ + τ`, `τ = lim Σ_{t ≤ y} (1 + λ(t))Λ(t)/t ≥ (log 2)/2`; `P_N(λx) = −ℓ² + 2(γ + τ)\|x\|² + o(mass)`; on `ℓ = 0`, `P_N(λx) − P_N(x) = 2(2γ + τ)\|x\|² + o(mass)` with `2γ + τ > 0` | `tendsto_liouvilleMertensError`, `exists_abs_liouvilleForm_stepProfile_finitePart_le`, `exists_abs_liouvilleForm_sub_zetaForm_sub_le` |
| **RP34 Mertens' theorem in residue classes with its constant** | for `r` a unit mod `q`, `Σ_{t ≤ y, t ≡ r} Λ(t)/t = log y/φ(q) + c_r + o(1)` with `φ(q) c_r = −γ − Q_q + Re Σ_{χ ≠ 1} χ(r⁻¹)(−L′/L(1, χ))`, `Q_q = lim Σ_{t ≤ y, (t,q) > 1} Λ(t)/t` | `tendsto_classMertensSum_sub`, `classMertensConstant_eq`, `tendsto_principalMertensSum_sub_log` |
| **RP35 The residue finite part is diagonalized by characters** | for units `a, b`: `⟨w_a^{(M)}, P w_b^{(M')}⟩ = (q/φ(q)) S_a(M) S_b(M') + c_{a⁻¹b} S_a(M) + c_{b⁻¹a} S_b(M) + O(η H_M + C_η)`; the finite-part matrix `F_{ab} = c_{a⁻¹b} + c_{b⁻¹a}` has every character as eigenvector, `Σ_b F_{ab} χ(b) = 2 Re β_χ · χ(a)`, `β_χ = −L′/L(1, χ)` (`χ ≠ 1`), `β_1 = −γ − Q_q`; inputs: class constants `q S_a(M) = log M + d_a + O(1/M)`, `L_a` to second order; the twisted pole `Re χ(n) u^{(M)}_n` has `P_N(x) = 2 Re(−L′/L(1, χ))\|x\|² + o(mass)` for every `χ ≠ 1` | `exists_abs_residueGram_finitePart_le`, `sum_residueFinitePart_mul_char`, `sum_classMertensConstant_mul_char`, `exists_classHarmonic_constant`, `exists_abs_atomicWeilForm_charPole_sub_le` |
| **RP36 The finite part sees every flipped prime; ζ maximizes it** | a twin flipping a finite prime set `F` has `A_{ε_F}(y) − log y → −γ − δ_F` with `δ_F ≥ 2 log p/p` for each `p ∈ F`; on every uniform profile `P_N(ε_F x) − P_N(x) = −2δ_F\|x\|² + o(mass)`. Rigidity: every sign gauge with `κ = 1` and `A_ε(y) − log y → α` has `α ≤ −γ`, with equality only for `ε = 1`, so `ζ` is the unique maximizer of the finite part among its matched twins; mirror: every gauge with `κ = −1` and `A_ε(y) + log y → α` has `α ≥ γ + τ`, with equality only for Liouville | `exists_abs_finiteFlipForm_sub_zetaForm_add_le`, `two_mul_log_div_le_finiteFlipLimit`, `finitePartLimit_le_and_eq_iff`, `exists_abs_gaugeForm_sub_zetaForm_sub_le`, `liouvilleLimit_le_and_eq_iff` |
| **RP37 The gap below the pole is `2 log 2`, carried by the 2-adic step** | for every `ε > 0`, eventually in `N`: `D_N(x) ≥ (2 log 2 − ε) Var_{1/n}(√n x)` for every `x`, so `P_N(x) ≤ (log N − γ − 2 log 2 + ε)\|x\|²` on `x ⊥ n^{−1/2}`; the 2-adic step `(1_{2∣n} − E_N/H_N)/√n` has `D_N = log 2 · E_N ≤ 2 log 2 \|x\|²` for every `N` and `P_N ≥ (log N − γ − 2 log 2 − ε)\|x\|²`. Mechanism: the finitely-many-prime valuation chain has gap `→ 2 log 2` (sharp ladder `log p Σ_{j ≤ J} p^{−j}`, Efron–Stein on boxes, halo paid by `log a`); `[1, N] = ⊔_a a · R(Q, N/a)` with the rough fibres tensorized at cost `K/log Q`, and the fibre means compared by Jensen with shell error `(1 + log t)/F(N/X)` | `eventually_smoothVar_le_smoothEnergy`, `two_scale_le`, `eventually_mul_harmonicVar_le_poleDefect`, `eventually_atomicWeilForm_le_two_log_two`, `poleDefect_twoAdicStep`, `eventually_atomicWeilForm_below_pole_two_log_two` |
| **RP38 Residue-pattern gauges are matched by their mean** | for every `±1` pattern `f` on `ℤ/q`, the gauge `ε_f(p^k) = f(p mod q)^k` has `A_{ε_f}(y) − κ_f log y → α_f` with `κ_f = φ(q)^{−1} Σ_{u ∈ (ℤ/q)ˣ} f(u)` and `α_f = Σ_u f(u) c_u + Σ_{a ∉ (ℤ/q)ˣ} f(a) ν_a + R_∞` (proper prime powers absolutely summable); so `P_N(ε_f x) = κ_f ℓ² + 2α_f\|x\|² + o(mass)`: the abelian Chebotarev patterns are matched by their mean | `tendsto_primeClassMertensError`, `exists_abs_primeClassGaugeForm_finitePart_le`, `gaugeMertensSum_primeClassGauge_eq` |

---

## 6. The questions and their answers

The twelve questions of the report (§4.4), in RAPT's terms.

1. **What is the admissible metric of the characteristic circle?** Under the Abel radius there is
   none: coupling cannot lower the torsion counterterm's rank, and the archimedean place pays one
   direction, the arithmetic point (RP1, RP2). Under the horizon the prime counterterm is the tensor
   product of the torsion counterterm and the archimedean counterterm, with the class-wise polar
   hyperplane as survival cone (RP5–RP7). Its rank is the number of torsion orbits read, so
   condition (i) of the central conjecture (bounded rank on Hecke orbits) is false for every
   regulator in the corpus (RP1, RP6). What replaces it is the tensor law. Condition (ii) holds:
   the finite part is covariant under `[p]` (RP9). Condition (iii) is the sign of the finite part on
   the degree-zero classes. Its prime component is computed: the positive scalar `+2γ` in Weil's
   form on uniform profiles (RP10), and minus the tower form of `p` on the classes (RP12). Its sign
   is decided prime by prime (RP16): nonnegative on the classes of `p` iff `√p log p ≤ γ(p − 1)`,
   with the exact deficit `2d_p` at the small primes. Matched against the archimedean self-energy
   the deficit disappears: the valuation potential `j log p` pays it, and the class profiles have
   prime finite part at most that of the pole (§4 item 19). The archimedean cross terms and the
   polar component remain open (§9.1). *Answer:* the admissible regulator is the
   horizon, its metric is the tensor counterterm, and its prime finite part is the local tower form.
2. **Does the anomaly cancel?** Yes, in two ways. Removing the self-intersection, as Weil's prime
   sum does, gives a covariant renormalized form. Covariance then forces a scalar counterterm,
   `log N − γ + o(1)` with constant one (RP3). Keeping the anomaly costs exactly `(φ − 1) log N + O(1)`,
   `φ` the golden ratio (RP22; the window was `[½, 1]`, RP4, RP15).
   At the horizon the cocycle disappears altogether: the tensor counterterm and the finite part are
   exactly invariant under `[p]` (RP9). The degree of `[p]` scales the orbit densities instead of
   shifting the regulator. *Answer:* the anomaly is an artifact of the radius; at the horizon it
   cancels exactly, and the archimedean place pays the scalar `log N`.
3. **What bounds the field?** The field law is RH-strength (AES `TheFieldLawHasAThreshold`). The
   energy of a zero is `O(log γ)` (AES `TheEnergyOfAZeroIsLogarithmic`). RAPT locates the missing
   inequality as a bound on a *finite part*. Every divergence is computed and matched (RP3, RP7),
   and the prime finite part is the scalar `−2γ` (RP10), so neither a counterterm nor the prime
   place can supply it. *Answer:* located in the archimedean and polar finite parts; open.
4. **What bounds the moment of inertia?** Uniform bounds are strips and height averages are density
   estimates (AES `TheHeckeDefectIsTheMomentOfInertia`). *Answer:* located (AES).
5. **What is the Frobenius at infinity?** On the circle, conjugation is the power map of degree `−1`;
   on the divisor its realization by a correspondence is RH (AES). *Answer:* AES.
6. **What is the arithmetic point?** It is the unique orbit coupled to the archimedean germ (RP2).
   Its pole carries the polar divergence of the horizon: the pole vector is an approximate
   eigenvector at the top of the spectrum, with eigenvalue `log N` (RP3, RP5). In the orbital
   decomposition of `μ_{p^{J+1}}` it is dual to the residue `0`, the one-point orbit (RP7).
   *Answer:* the matched direction of the coupled renormalization.
7. **How does `σ_γ` localize beyond the conductor; are zero ordinates aligned with small primes?**
   The alignment law at zero ordinates and its higher moments are in AES
   (`LargeValuesAtZeroOrdinates`, `HigherMomentsAtZeroOrdinates`). *Answer:* AES.
8. **What is the non-archimedean gauge charge of a positive form?** Counterterms of each place are
   gauge blind (the twin's prime form is `P` in the gauge `x ↦ εx`), but their **matching** is
   charged. `ζ`'s prime divergence is `+ℓ²` along the archimedean polar direction; the Liouville
   twin's is `−ℓ²` (RP8). For every sign gauge the matching coefficient `κ` is the density of
   unflipped minus flipped primes read through `A_ε`. A twin flipping finitely many primes has
   `κ = 1` and is matched exactly as `ζ` is (RP11). AES adds the coefficient margin `2 log² p` of the
   source at each flipped prime and the stability law for every twin. *Answer:* the gauge charge
   sits in the matching of the two places' counterterms, which reads the density of the gauge.
   Individual primes are separated only by finite parts.
9. **How does a quantized statistic reach every window?** By window energies (AES).
10. **Is the coupled class bounded at the centre?** Owned by BGG.
11. **What selects the fibre?** Divergences are soft: the tensor law holds for every sign twin in
    its gauged coordinates. Selection must come from the finite parts and from the gauge-charged
    matching (RP8, RP11), which reads only the density of the gauge. Within the twins flipping
    finitely many primes the finite part does select `ζ`: each flipped prime lowers it by at least
    `4 log p/p`, and among all twins with `κ = 1` and a convergent Mertens error `ζ` is the unique
    maximizer of the finite part (RP36); the Liouville twin is separated on the polar hyperplane
    (RP33).
12. **What are the escape states of `ζ` at infinite height?** Infinite transverse energy (AES).

---

## 7. Traps

| Trap | Truth |
|---|---|
| The torsion counterterm is the identity, so the prime place has no survival | That is the Abel radius; at the horizon the survival cone is the class-wise polar hyperplane |
| Coupling with the archimedean place lowers the torsion counterterm's rank | The prime block keeps its rank; a partner pays at most its own rank (`finrank_primeSurvival_le_rank`) |
| Any torsion orbit can be matched to the archimedean place | Ramanujan modes of order `≥ 2` have mean zero; only `O_1` couples |
| A better diagonal makes the renormalized form covariant and positive | Covariance forces a scalar, and a scalar counterterm has no survival |
| `κ ≍ log N` is a soft statement | The covariant constant is exactly one; the torsion constant is at least `3/2` |
| The anomaly is a nuisance to be removed for free | Its potential is the self-intersection; removing it saves at least `½ log N` |
| At the horizon the divergence is rank one | Only on uniform profiles; on class-wise profiles it is the tensor counterterm, of unbounded rank |
| A sign twin has the same divergences, so the same renormalization | The same spectrum, but the opposite polar matching at the Liouville gauge |
| A twin flipping one prime is separated by the coupled renormalization | Its polar matching coefficient is `1`, as for `ζ`; only finite parts see individual primes, each lowering it by at least `4 log p/p` (RP36) |
| The Hecke anomaly `log t` is intrinsic to the prime place | It belongs to the Abel radius; at the horizon `[p]` scales the orbit densities by `1/p` and the anomaly cancels |
| A matched counterterm proves the sign | It removes the divergence; the sign lives in the finite part |
| The finite part of the prime place hides the zeros | On uniform profiles it is the scalar `−2γ`, on the classes the tower form; the zeros are invisible at log-scale resolution, and the sign is decided by the archimedean place and the pole |
| The local Hodge index at `p` and the renormalization at the horizon are separate topics | The tower form of `p` is the finite part of the horizon renormalization on the `p`-adic classes |
| Refining by residue classes raises the counterterm rank, as the valuation classes do | On the unit classes mod `q` the counterterm stays the single square `(q/φ(q)) ℓ²`; only valuations raise the rank (RP24) |
| Characters are invisible at the horizon | Invisible to the divergence; their finite part is `2 Re(−L′/L(1, χ))`, and on residue profiles the characters are the eigenvectors of the finite part (RP31, RP35) |
| A finite part needs a convergent Mertens error | It needs exactly a harmonic mean of the error; convergence is the Abelian sufficient condition (RP30) |

---

## 8. Tools

**Imported.** Survival law, germs, Ramanujan relations, Cesàro Grams (RBG); orbit intersections,
the different, the Hecke cocycle and transport (AIT); torsion pairing, atomic Weil form, Schur
machinery (AES); Mertens' first theorem and Mertens' theorem with Euler's constant (RHTower).

**Built here.** Coupled counterterms and the partner-rank calculus; Hecke shifts and the covariance
of the tensor counterterm; the finite part with Euler's constant; the joint germ of the two
places; covariance of diagonals; the exact Schur rows and sharp two-sided bounds for the atomic
prime form; pole vectors, the polar functional, step profiles and their Gram; `p`-adic class pole
vectors, prime-power sums, class masses and the class Gram; the tensor law; Liouville signs, the
twisted Mertens sum and Dirichlet's hyperbola identity; telescoping bounds for `Σ log n/n`.

Also built: the Hecke excess and its summability over prime powers; the tower deficit and the
Kac–Murdock–Szegő extremal profile; the sharp two-sided Lévy density, bump pairings, the cross
majorant and the Hilbert-type row bound for the archimedean interaction of atoms; the archimedean
self-energy with constant one; Abel summation with decreasing weights and Mertens' theorem for
characters; character gauges; the equivalence of Gårding inequalities with finite-rank survival.

Mertens' theorem in residue classes is built as well, with harmonic and logarithmic sums over
residue classes, residue pole vectors and their exact Gram, class-function profiles, the
transfer of the Mertens error to the horizon remainder, and summation by parts at the horizon
(every profile as a step profile, with its horizon variation).

**To build.** The finite part of the matching in the overlap regime beyond the spacing
(the spacing itself is reached in SSHA).

---

## 9. Open research topics

1. **Beyond the atomic spacing.** At width `ε = c/N` the archimedean self-energy `log(1/ε)` and the
   covariant counterterm `log N + O(1)` agree to `O(1)`. With the interaction of the atoms in
   absolute value, the Markov form is nonnegative down to width `δ_N/(C log N)` (RP18). There the
   absolute interaction kernel `w/|log n − log m|` is bounded; at width `cδ_N` it has norm
   `≍ c log N`. The spacing itself is reached in
   [SpacingScaleHarmonicAnalysis](../SpacingScaleHarmonicAnalysis/README.md)
   (`markovEnergy_atomicTest_nonneg_spacing`): the tilted Schur weight `1 + n/N` lets the down tower
   of the prime form pay the archimedean cross kernel row by row. The Markov form is nonnegative at
   widths `≤ c₀δ_N`, and `Re W + 2S² ≥ 0` there, a rank-one pole correction. The open question
   moves into the overlap regime `w ≫ δ_N`. There SSHA's critical-exponent law ties positivity at
   widths `N^{−θ}`, `θ < 1`, to RH. In RAPT terms this asks which finite part, signed interaction
   plus pole, keeps the matching through the overlaps. In the separated regime the finite part is
   computed: at width `w = c/N` the Markov ground energy is `2θ′(0) + log(1/c) + κ_L(φ) + γ + O(c)`,
   the Robin constant of the atom plus the Euler constant of the pole
   (`TheFinitePartOfTheMarkovFormAtTheSpacing`); the archimedean cross terms are paid in mean
   square by the pole defect, not row by row.
2. **Who pays the tower deficit.** *Answered:* the archimedean place. Its self-energy is uniform
   in the classes, while the horizon counterterm of class `j` is `log(M/p^j)`; the difference, the
   valuation potential `j log p`, covers `2d_p` with margin: `F_p + V_p ≥ (γ + γ_p)|b|²`, the pole is
   the ground state, `P_M ≤ (log M − γ + η)|·|²` on class combinations, with a Hodge index on their
   span. For every finite prime set `Q`, the actual matched operator on all supported integers
   has a complete explicit basis, simple energies `γ + log m + tameDifferent(m)`, and compact
   shifted inverse. The normalized horizon defect of each fixed finite class vector `b` is
   exactly `−Re ⟨b,A_Q b⟩`. On all of `[1, N]` and all primes at once the pole is isolated with
   gap exactly `2 log 2`: the top of `P_N` on its complement is `log N − γ − 2 log 2 + o(1)`,
   attained by the 2-adic step (RP29, RP37).
   Ramanujan profiles give norm quasimodes on the full horizon, and every fixed
   finite conductor packet produces distinct actual eigenvalues near `log N−E(m)`.
   Open: exhaustion of the bounded renormalized spectrum, and
   the archimedean cross terms of distinct atoms on class profiles.
3. **Characters at the horizon.** *Answered.* Mertens' theorem for
   characters (RP19) and in residue classes (RP21) are proved. On the unit classes mod `q` the
   horizon counterterm is the rank-one `(q/φ(q)) ℓ(x)²` for every `q` (RP24): the horizon reads
   valuations, not residues, and the unbounded rank of the `p`-adic classes does not recur. A class
   function `f` on the units is seen only through its mean, `κ_f = (Σ_a f(a))²/(q φ(q))`, so every
   character `χ ≠ 1` of every modulus, real or complex (through `Re χ` and `Im χ`), has no polar
   divergence (RP25). This extends RP20 from real characters mod a prime. The finite part is
   computed: `A_χ(y) → −L′/L(1, χ)` (RP31, from the prime number theorem for characters), and every
   gauge with a convergent Mertens error `A_ε − κ log → α` has finite part `2α` (RP30). A real
   character gauge mod `ℓ` thus has horizon form `2(Re(−L′/L(1, χ)) + c_ℓ)|x|² + o(mass)`, where
   `c_ℓ` is the limit of `Σ_{t ≤ y, ℓ ∣ t} Λ(t)/t`: the horizon reads the logarithmic derivative of
   `L(s, χ)` at `s = 1`, as it reads `−2γ` from `ζ`. On the residue-class profiles the finite part
   is the convolution by the class Mertens constants (RP34, RP35); it is diagonalized by the
   characters mod `q`, with eigenvalues `2 Re(−L′/L(1, χ))` and `2(−γ − Q_q)` on the trivial
   character. The residue classes are invisible to the divergence and fully visible to the finite
   part.
4. **The exact torsion constant.** *Answered* (RP22): `κ_tor(N) = φ log N + O(1)`,
   `φ = (1 + √5)/2`, for every `N`. The continuum model's `e/(e − 1)` is wrong: it spreads the
   charges uniformly in `log n`, while the extremal charges `φ^{ω(n)}` are multiplicative, so each
   prime factor raises the charge by `φ`. The anomaly costs exactly `(φ − 1) log N = log N/φ`.
   Open: the `O(1)` term, and the analogue for twisted torsion pairings.
5. **Matching coefficients of natural gauges.** The matching law (RP11) turns any asymptotic
   `A_ε(y) = κ log y + O(1)` into a horizon divergence `κ ℓ²`. For a gauge flipping a set of primes of
   logarithmic density `ϑ`, `κ = 1 − 2ϑ`, at leading order (RP26). Real characters mod a prime have `κ = 0` (RP20), and every
   character `χ ≠ 1` of every modulus is invisible on character-twisted profiles (RP25); quadratic
   Chebotarev patterns `(d/p)` are real characters. *Answered:* an error `o(log y)` keeps the law at
   leading order, `|P_N(εx) − κℓ²| ≤ (η log N + C_η) · mass` (RP26). The transfer law identifies the
   remainder exactly as the harmonic convolution of the Mertens error, so the mass-scale law holds
   iff that error is bounded in logarithmic mean. Every sign pattern of the primes by residues mod
   `q`, so every abelian Chebotarev pattern, has `κ` equal to its mean over `(ℤ/q)ˣ` and a computed
   finite part (RP38). Open: `κ` for non-abelian Chebotarev patterns, which needs Mertens' theorem
   for Artin `L`-functions.
6. **Several primes at once.** *Answered for every finite prime set `Q`:* each finite family
   of classes `{n : n = d k, (k, Q) = 1}`, indexed by the `Q`-parts `d`, has counterterm
   `Σ_d δ_d^{−1} ℓ_d²`, where `δ_d = (1/d) Π_{p∈Q}(1−1/p)`. It is covariant under every
   supported Hecke shift; its survival space is exactly the common kernel of the class charges.
   The law holds for arbitrary signed finite class-wise step profiles with independent cutoffs.
   Its finite part has one shared Euler constant `γ_Q` and the exact transverse tower interaction.
   The boundary estimate is uniform in raw class orders; the density-normalized limit fixes a
   finite class family. Fixed Ramanujan conductor packets are also realized in
   the full prime matrix through their norm residuals. Passing the class-profile
   finite-part law to all primes or growing normalized class families remains open.

---

## 10. Success criteria and contribution standards

RAPT succeeds when every question of §6 has an answer of the form theorem, sharp equivalence, or
sharp no-go with its positive survivor, and when the central conjecture of the report has been
replaced by a statement in which every divergence is computed and only a finite part is open. In
its present state:

* Q1 and Q2 have theorem-level answers: the coupled survival law with the arithmetic point as
  survivor; covariance ⇒ scalar with constant one; the cost of the anomaly; the tensor law and its
  covariance without anomaly. Of the three conditions of the central conjecture, (i) is false for
  every regulator, (ii) holds at the horizon, and (iii) is the open sign of the finite part.
* The prime finite part is computed: `−2γ` on the uniform survival cone (RP10), the tower form of
  `p` with the local Euler constant on the classes (RP12), whose sign changes exactly between the
  primes `43` and `47` (RP28). For every gauge the finite part is twice the limit of its Mertens
  error (RP30): `+2(γ + τ)` for the Liouville twin (RP33) and `2 Re(−L′/L(1, χ))`, corrected at
  `ℓ`, for character gauges (RP31). On the unit residue classes the finite part is diagonalized by
  the characters mod `q`, with eigenvalues `2 Re(−L′/L(1, χ))` (RP34, RP35).
* Q8 has a theorem-level answer: the matching law for every sign gauge, `κ = −1` for Liouville,
  `κ = 1` for finitely many flips, `κ = 0` for every character `χ ≠ 1` (RP20, RP25), `κ` = the mean
  of the pattern for every abelian Chebotarev pattern (RP38); an error `o(log y)` keeps the law at
  leading order (RP26); residue classes are invisible (RP24).
* Q6 is answered through RP2, RP3 and RP5.
* The central conjecture is replaced by the matched stability law (§9.1). RAPT proves it at widths
  `δ_N/(C log N)` (RP18). SSHA proves it at a fixed fraction `c₀δ_N` of the spacing. The overlap
  regime is open.

A contribution is an unconditional Lean theorem about an object of §3. It names its **regulator**,
its **counterterm** with rank and survival cone, its **anomaly**, and the **place** that pays. It
separates identities and divergences (computed) from signs (open). It states what it gives on the
battery: sign twins, the golden datum, curves over `𝔽_q`. Every no-go records its positive survivor.

Principles: the rank of a counterterm belongs to the regulator; covariance forces scalars; the
divergence lives on the torsion orbits; matched divergences leave the sign in the finite part;
matching is gauge charged; identities first, sign last; a reformulation is not a reduction.

---

## 11. Modules

| Module | Content |
|---|---|
| `TheCoupledSurvivalLaw` | coupled counterterms; partner kernel; survival equations; rank and dimension bounds; rank-one partners; the torsion germ coupled to any partner |
| `GardingIsAFiniteRankSurvival` | functional counterterms; Gårding ⇔ finite-rank survival ⇔ renormalized limit; negative index |
| `TheArchimedeanPlacePaysTheArithmeticPoint` | Ramanujan orthogonality; the joint counterterm; prime survival `ℝ e₁`; the joint germ as a positive regularized family; matched survival |
| `TheCovariantCountertermIsTheAnomaly` | covariance of diagonal renormalizations; exact Schur rows; the pole vector as approximate eigenvector; `κ_cov = log N + O(1)` |
| `TheTorsionCountertermIsAtMostTwoLogarithms` | normalized charges; Hecke excess and its summability; torsion kernel = Weil's kernel + bounded; `κ_tor ≤ 2 log N + C`; the window |
| `TheAnomalyCostsHalfALogarithm` | `φ(mt) ≤ t φ(m)`; torsion pairing on the pole charges; averages of `log n/n` and of the tame different; `κ_tor ≥ (3/2) log N − C` |
| `TheHorizonCountertermIsPolar` | truncated pole vectors and step profiles; the pole Gram; polarity on uniform profiles |
| `TheHorizonDivergenceLivesOnTheTorsionOrbits` | prime-power sums; class pole vectors; class rows; full rank on the arithmetic factor; unbounded rank |
| `TheHorizonCountertermIsATensorProduct` | class densities and orbit sizes; class masses; the class Gram at two horizons; the tensor law |
| `TheHorizonCountertermIsHeckeCovariant` | Hecke shifts; invariance of the prime form; class shift by `[p]`; orbit densities scale by the degree; no anomaly |
| `TheFinitePartIsEulersConstant` | Mertens with Euler's constant; roundoff; the finite part of the pole Gram; `−2γ` on step profiles and on the polar hyperplane |
| `TheFinitePartIsTheTowerForm` | the local Mertens theorem and local Euler constant; class masses; exact rows inside and across classes; the finite part on the classes is the tower form |
| `TheMatchedStabilityLaw` | AES's stability law at atomic resolution with the covariant counterterm; the matched width `δ_N N^{−e^{1/2}}` |
| `TheStabilityLawReachesTheSpacingUpToALogarithm` | shift expansion and bump pairings; two-sided Lévy density; cross majorant; Hilbert-type rows; stability at width `δ_N/(C log N)` |
| `TheSelfEnergyHasConstantOne` | sharp Lévy density on short shifts; Lévy gain with constant `1 − O(1/N)`; nonnegativity at width `c δ_N/N` |
| `TheSignOfTheTowerFinitePart` | the tower deficit; the KMS bound and the uniform class profile; the sign law; `p = 2` and large `p` |
| `TheArchimedeanPlacePaysTheTowerDeficit` | the valuation Gram in the stability regime; class masses descend by `p`; `F_p + Σ j log p b_j² ≥ (γ + γ_p)|b|²`; `P_M ≤ (log M − γ + η)|·|²` on `p`-class combinations, sharp at the pole |
| `TheMatchedPrimePlaceHasAHodgeIndexOnTheClasses` | the valuation inequality with its Laplacian; gap `g_J log p` on the polar hyperplane; `P_M − (log M − γ − η)` has one positive square on the class span |
| `ThePoleIsTheTopOfThePrimeForm` | weighted Schur test; rows of `√n` (Chebyshev up, `½ log m` down); the tilted pole as Collatz–Wielandt vector; the covariant counterterm is `log N − γ + o(1)` |
| `TheValuationTowerIsExactlySolvable` | the valuation tower operator: pole ground state `γ`, valuation steps with eigenvalues `γ_p + k log p`; the deeper-class slack; the sharp gap `p log p/(p − 1)` on the polar hyperplane at every depth |
| `TheDeficitOfThePrimeFormIsADirichletEnergy` | ground-state identity `P_N + D_N = Σ (A(⌊N/n⌋) + log n) x_n²` with the pole defect `D_N = Σ Λ(t)(x_{mt} − x_m/√t)²`; the defect pays the top atoms; `P_N + (1 − ε) D_N ≤ (log N − γ + ε)|·|²` without tilt; the Hodge index modulo every prime `p` on the whole space (gap `(1 + 1/p) log p` off the ladder poles) |
| `TheFinitePartOfTheMarkovFormAtTheSpacing` | the Lévy energy of an atomic test with its diagonal kept; pair windows `≤ 2w(1/|log(n/m)| + 1)`; the cross terms paid in mean square by the pole defect; the Markov ground energy at width `w ≤ δ_N/2`, `wN ≤ 1/(64e²)`, is `2θ′(0) + log(1/(wN)) + κ_L(φ) + γ + O(wN) + o(1)`, attained by the pole |
| `TheArchimedeanFinitePartIsMinusLogTwoPi` | `2θ′(0) + 2c_∞ + γ = −log 2π` (with SSHA `archRobinConstant_eq`); the Markov ground energy at the spacing in closed form, `log(1/(2π wN)) + β(φ)/‖φ‖² + O(wN) + o(1)` |
| `TheTorsionCountertermIsTheGoldenRatio` | the golden split `a² ≤ φ²(a − b)² + φ b²` on the prime-power edges; `diag(log n) + P_N ≤ φ Σ (A(⌊N/n⌋) + log n) x_n²`; the golden vector `φ^{ω(n)}/√n` and its mean co-height from the Chebyshev identity; non-coprime edges carry the tame different; `κ_tor(N) = φ log N + O(1)` |
| `TheSelfIntersectionFamilyObeysAFixedPointLaw` | the `κ`-twisted ground-state identity `(κ − 1/κ) Σ log n x² + P_N + D_κ/κ = κ Σ (A + log n) x²`, `D_κ = Σ Λ(t)(x_{mt} − κx_m/√t)²`; the spectrum of `α diag(log n) + P_N` fills `[κ₋, κ₊] log N + O(1)`, `κ² = ακ + 1`, both ends attained at `κ±^{ω(n)}/√n` |
| `TheRoughHarmonicMeasureHasThinShells` | rough intervals and their level decomposition `R(p, X) = ⊔_j p^j R(p+1, X/p^j)`; Buchstab's inequality; `F_{p+1}(X) ≥ log(X+1) Π_{q≤p}(1 − 1/q)`; thin shells by Selberg's sieve; the shell rate `τ(p, X) ≤ C log p/(p log X)`, `τ < 1` |
| `TheHarmonicMeasureTensorizesOverPrimes` | weighted variance (Steiner, Jensen, nested means); ladders and the Glauber form; peeling one prime; the potential `−A Σ_{q<Q}(log q/q)/log X`; `Var_{1/n,[1,X]} ≤ C · Σ_q Σ_u Var_{q-ladder}` uniformly in `X` |
| `ThePrimeFormHasASpectralGapBelowItsPole` | the pole gauge; ladder Poincaré from the base point; `D_N ≥ log 2 · Glauber`; the Poincaré inequality `D_N ≥ g|x|²` on the pole complement; `P_N ≤ (log N − γ − g + ε)|x|²` there |
| `ThePoleHyperplaneSeparatesZetaFromItsLiouvilleTwin` | `Σ_{d∣m} λ(d) = 1_□(m)` and `|Σ_{n≤N} λ(n)/n| ≤ 2`; the ground-state identity polarized at the pole; on the pole hyperplane `ζ`'s prime form stays `g` below the top while the Liouville twin's reaches it |
| `TheValuationChainOfFinitelyManyPrimesHasGapTwoLogTwo` | the `Q`-smooth box and its product measure; Efron–Stein; the sharp ladder gap `log p Σ_{j ≤ J} p^{−j}`; zero extension to the box and the halo `Σ (1/a) log a · u² ≤ 2E + 2M_Q Σ (1/a) u²`; the `Q`-smooth chain on `[1, X]` has gap `2 log 2 − ε` for `X ≥ X₀(Q, ε)` |
| `TheSpectralGapOfThePrimeFormIsTwoLogTwo` | `[1, N] = ⊔_a a · R(Q, N/a)` over the `Q`-smooth parts; the walk energy split at `Q`; small edges in both fibrations; the halo of the smooth parts; Jensen across fibres with shells `F(Y) − F(Y/t) ≤ 1 + log t`; `D_N ≥ (2 log 2 − ε) Var` and `P_N ≤ (log N − γ − 2 log 2 + ε)\|x\|²` below the pole |
| `TheFirstExcitedStateOfThePrimeFormIsTheTwoAdicStep` | the 2-adic step and its exact defect `log 2 · E_N`; `E_N ≤ H_N/2`; Mertens on the rows from below; the two-sided law `λ₂(P_N) = log N − γ − 2 log 2 + o(1)` |
| `TheLiouvilleGaugeFlipsThePolarDivergence` | Liouville signs; the twisted Mertens sum; Dirichlet's hyperbola; spectral ends; the polar flip |
| `MertensTheoremForCharacters` | Abel summation with decreasing weights; partial sums of `L(1, χ)`; the logarithmic sum; the hyperbola identity; `A_χ = O(1)` |
| `MertensTheoremInResidueClasses` | orthogonality; the principal Mertens sum; `A(y; r) = log y/φ(q) + O(1)` |
| `CharactersAreInvisibleToPolarMatching` | the character gauge; matching coefficient `0`; no horizon divergence on gauged step profiles |
| `PolarMatchingReadsTheDensityOfTheGauge` | sign gauges; gauged rows and pole Gram; the matching law; Euler, Liouville and finite-flip instances |
| `PolarMatchingNeedsOnlyTheLeadingOrder` | the Mertens error; the transfer law; the local and soft matching laws; the diagonal criterion |
| `TheHorizonCountertermIsBlindToResidueClasses` | class harmonic and logarithmic sums; residue pole vectors and their Gram; the residue law; rank one on the unit classes |
| `TheHorizonSeesOnlyTheMeanOfAClassFunction` | class-function profiles; `κ_f = (Σ f)²/(q φ(q))`; characters of every modulus are invisible |
| `TheHorizonLawsHoldForProfilesOfBoundedVariation` | summation by parts at the horizon; the horizon variation; polarity, finite part and tensor law for every profile; profiles of bounded variation |
| `TheTowerDeficitChangesSignBetweenFortyThreeAndFortySeven` | `d_p = u/sinh u − γ`; strict monotonicity; `0.5753 < γ < 0.5777`; `d_43 > 0 > d_47`; the sign table of the tower finite part |
| `TheFinitePartIsTwiceTheMertensLimit` | the gauged pole Gram as a Mertens convolution; convergent convolutions; the finite-part law for pole Grams and uniform profiles |
| `TheFinitePartIsTheHarmonicMeanOfTheMertensError` | the diagonal Gram; `2 Σ log⌊M/m⌋/m = H_M² + o(H_M)`; the finite-part criterion |
| `TheCharacterMertensSumConverges` | Abel summation against `ψ(x, χ)`; subexponential decay; convergence of `A_χ`; the finite part of a character gauge |
| `TheCharacterMertensLimitIsTheLogarithmicDerivative` | Abel weights; Abel's theorem for `χΛ`; `α_χ = −L′/L(1, χ)` |
| `TheFinitePartSeparatesZetaFromItsLiouvilleTwin` | the even prime-power limit `τ`; the Liouville Mertens limit; the Liouville finite part; separation from `ζ` on the polar hyperplane |
| `TheFinitePartSeesEveryFlippedPrime` | the flip deficit and its limit `δ_F`; every flipped prime counts; the twin's Mertens limit; separation from `ζ`; rigidity: `ζ` uniquely maximizes the finite part among matched gauges, Liouville uniquely minimizes it among anti-matched ones |
| `MertensTheoremInResidueClassesWithItsConstant` | the non-coprime prime powers; the principal limit `−γ − Q_q`; the class constants through `−L′/L(1, χ)` |
| `ResiduePatternGaugesAreMatchedByTheirMean` | residue-pattern gauges; Mertens decomposition; proper prime powers; non-unit classes; `κ_f`, `α_f` and the horizon law |
| `TheMatchingCoefficientIsTheLogarithmicDensity` | prime-sign gauges; primes and proper prime powers; density gives matching; `κ = 1 − 2ϑ` for flipped density `ϑ` |
| `ClassHarmonicSumsHaveConstants` | Euler's constant with a rate; Cauchy with a rate; shifted classes; the class constants `d_a`; `L_a` to second order |
| `TheFinitePartOnResidueClasses` | the residue Gram as class Mertens sums; floors; the logarithmic model Gram to `O(1)`; the residue finite-part law |
| `TheResidueFinitePartIsDiagonalizedByCharacters` | spectral values `β_χ`; conjugate characters; class constants as a character transform; Fourier inversion; diagonalization |
| `TheTwistedPoleReadsTheLogarithmicDerivative` | unit poles, their mass and Gram expansion; eigenprofiles have a scalar finite part; the twisted pole and `2 Re(−L′/L(1, χ))` |
| `TheLawsOfRenormalizedArithmeticPotentialTheory` | the laws in one statement, `renormalized_arithmetic_potential_theory_laws` |
