# Arithmetic Intersection Theory (AIT)

**One question.** Weil's proof of the Riemann hypothesis for a curve over `𝔽_q` is intersection
theory on `C × C`: intersection numbers are integers, correspondences act through a projection
formula, the diagonal has a finite self-intersection given by adjunction, and the Hodge index
theorem supplies the sign. Over `ℤ` the explicit formula is a pairing of the same shape. Which of the
four ingredients exist for it, on which carrier, how do the carriers glue, and what exactly is the
one statement that is missing?

AIT is the intersection theory of the **characteristic circle** — the torsion `μ_∞ ⊂ 𝔾_m(ℂ)` of the
multiplicative group over `ℤ`, with its three symmetries: power maps, rotations, Galois — and of its
transfer to the scaling surface on which Weil's form lives. Its organizing sentence:

> *Over `ℤ` the intersection numbers of torsion cycles exist, are log-orders of finite rings, and
> obey the projection formula; the self-intersection of a torsion orbit is the discriminant of its
> cyclotomic field. The diagonal exists only after a regularization, and the regularization is not
> covariant: the Hecke correspondence `[t]` rescales the regulator by its degree, with anomaly
> `log #ker[t]`. Weil's prime form is the finite intersection pairing, a sum of transverse local
> tower forms, each bounded; their sum is not, and RH is the statement that the archimedean place
> pays for it.*

Namespace `GaloisForLFunctions.ArithmeticIntersectionTheory`; umbrella
`ArithmeticIntersectionTheory.lean`. Everything is unconditional; RH appears only as a hypothesis of
a transfer statement or inside equivalences.

---

## 1. Place in the research

Every live route of the frontier ends at an RH-equivalent receiver plus one missing sign. The
exhaustion laws behind the three walls reduce to three structural facts
([review fable](../../../docs/reports/review-2710/fable.md), §1.3): the Hecke algebra is
commutative, every receiver is a linear functional of the explicit formula, and the diagonal has no
finite self-intersection. Over `𝔽_q` one object — `C × C` with its intersection theory — removes all
three. AIT asks what remains of that intersection theory over `ℤ`, builds it where it exists, and
locates the missing statement inside it.

| Programme | What AIT takes | What AIT adds |
|---|---|---|
| [ArithmeticEffectivityTheory](../ArithmeticEffectivityTheory/README.md) | torsion orbits `O_n`, orbit intersections `I(m,n)`, the Hecke law `I(m,mt) = φ(m)Λ(t)`, Abel energies `T_r`, the gcd twist, the renormalized torsion limit of Weil's prime kernel | the projection formula and the regulator anomaly; the different and the Hecke cocycle; intersection numbers as log-orders; the discriminant as self-intersection; the spacing regulator |
| [ArithmeticElectrostatics](../ArithmeticElectrostatics/README.md) | the potential reading of the torsion and the zero divisor | the covariance theory of the counterterm; the Rosati reading of zero moments |
| [RenormalizedBiarithmeticGeometry](../RenormalizedBiarithmeticGeometry/README.md) | the survival law, the counterterm rank dichotomy, the lattice germ `G_r(z) = Σ r^k/(k+z)` and its digamma limit | the lattice germ is the rotation spectrum of the torsion energy on `μ_N` (Gauss's digamma theorem); a covariant regulator, and why it carries no sign |
| [ArithmeticCastelnuovoSeveri](../ArithmeticCastelnuovoSeveri/README.md), [ArithmeticOrientationGeometry](../ArithmeticOrientationGeometry/README.md) | the scaling surface and its Hodge index, the Hecke tower of a prime on the zero side, the `𝔽_q` calibration | the tower form of a prime on the prime side; the local Hodge index; transversality of ladders |
| `RHTower` (separated bumps), [BiScaleUncertainty](../BiScaleUncertainty/README.md) | narrow-bump configurations, the archimedean Lévy gain, Weil positivity under RH for real `C²_c` tests | the transfer identity: on log-atom tests Weil's prime functional is the finite intersection pairing |
| [BiarithmeticGaugeGeometry](../BiarithmeticGaugeGeometry/README.md), [ArithmeticCorrelationGeometry](../ArithmeticCorrelationGeometry/README.md) | the gauge torus `∏_p S¹`, sign twins, the Kronecker line | the tensor form of the prime kernel; gauge blindness of the finite intersection |
| [ArithmeticPolarization](../ArithmeticPolarization/README.md), [ConjugateDiagonalGeometry](../ConjugateDiagonalGeometry/README.md) | `W`, `D`, `Δ`, local types at off-line pairs | the place of each form in the dictionary; zero moments as Rosati pairings |
| [ArithmeticPositiveDuality](../ArithmeticPositiveDuality/README.md) | `Aff(ℚ)` states, Bost–Connes, successor blindness to atoms | the affine semigroup `z ↦ ζ z^t` of the circle and the spectrum of its elliptic part |
| [TransThresholdPairCorrelation](../TransThresholdPairCorrelation/README.md), [SquareRootThreshold](../SquareRootThreshold/README.md) | pair correlation, coalescent surplus, the square-root threshold | the two-point form of the missing statement |

AIT does not re-prove what these programmes own; it imports them and proves the laws that glue
them.

---

## 2. Why

**Weil's four ingredients.** On `C × C`: (i) intersection numbers of curves are integers, and the
Lefschetz number `Γ_m · Δ` counts points; (ii) a correspondence `f` acts by `f_*`, `f^*` with the
projection formula `f_*A · B = A · f^*B`; (iii) the diagonal is a curve, `Δ² = 2 − 2g` by adjunction;
(iv) the Hodge index theorem, which on the plane of `Γ_m` and `Δ` is the Hasse–Weil bound. (i)–(iii)
are identities; (iv) is the sign.

**Over `ℤ` the identities hold on the characteristic circle.** The torsion orbit `O_n` (primitive
`n`-th roots of unity) is the horizontal divisor `Φ_n = 0` of `𝔾_m/ℤ`.

* *Intersection numbers are log-orders.* The archimedean intersection
  `I(n, m) = Σ_{η∈O_n, ξ∈O_m} log|η − ξ|` is the logarithm of the order of the finite ring
  `𝓞_{ℚ(ζ_n)}/(Φ_m(ζ_n))`, the intersection scheme of the two divisors: the product formula. With the
  arithmetic point `O_1 = {1}`, `Λ(n) = log #(𝓞_{ℚ(ζ_n)}/(ζ_n − 1))`.
* *Correspondences.* The power map `[t]` is the Hecke correspondence. Its fibre over `z^t` is `μ_t z`,
  and `z^t − w^t = ∏_{ω∈μ_t}(z − ωw)` is the projection formula for the archimedean pairing.
* *Adjunction.* The self-intersection of `O_n` per point is `Σ_{p^a∥n}(a − 1/(p−1)) log p`, the
  different of `ℚ(ζ_n)` per unit degree; for `n = p^k`, `I(n,n) = log|d_{ℚ(ζ_n)}|`.

**What is not covariant is the regularization.** The archimedean pairing is singular on the
diagonal. At Abel radius `r < 1` the energies are positive (the archimedean Hodge index, at every
regulator), and Weil's prime kernel is their limit after subtracting `log(1/(1−r))` per point. The
regularized projection formula `Σ_{ω∈μ_t} −log|1 − rωz| = −log|1 − r^t z^t|` shows that `[t]` replaces
`r` by `r^t`; since `(1 − r^t)/(1 − r) → t` the counterterm moves by `log t = log #ker[t]`. On orbit
cycles this anomaly, corrected by tame ramification, is the Hecke cocycle `β(n,t)`; it is not the
coboundary of a bounded potential. Scaling each orbit's radius with its spacing `2π/n` removes the
anomaly — and leaves a scalar counterterm, which carries no sign.

**The local sign exists; the global sign is RH.** At a prime `p` the finite intersection on a ladder
`{cp^j}` is a sum over the levels of the `p`-power tower, each weighted by the orbit size `φ(p^k)`: a
positive Kac–Murdock–Szegő form with spectrum in `[(1−q)/(1+q), (1+q)/(1−q)]`, `q = p^{−1/2}`. Weil's
prime kernel is `Σ_p log p` (tower form − identity), a sum of transverse local forms on the tensor
product of ladders: each is bounded, the sum is not. On log-atom tests the prime functional *is*
this sum, so RH says that the archimedean place and the pole dominate the sum of the towers.

**The elliptic correspondences look the wrong way.** Rotations of the circle are elliptic and
exact, and diagonalize the torsion energy on `μ_N`; their eigenvalues are values of the archimedean
local factor at rational points (Gauss's digamma theorem). The zeros of `ζ` enter only through the
hyperbolic Hecke correspondences that glue the levels.

---

## 3. Objects and language

| Over `𝔽_q` (`C × C`) | AIT object | Over `ℤ` | Lean |
|---|---|---|---|
| curves on `C × C` | torsion cycles `Σ x_n O_n`; point cycles on `μ_N`; log-atom cycles on the scaling line | divisors `Φ_n = 0` of `𝔾_m/ℤ` | `primitiveRoots`, `logAtomTest` |
| `D · E` | archimedean intersection `I(m,n)`; its log-order reading | `log #(𝓞/(Φ_m(ζ_n)))` | `orbitIntersection` (AET), `log_card_quotient_cyclotomicValue` |
| Lefschetz `Γ_m · Δ = N_m` | intersection with the arithmetic point | `Λ(n) = log #(𝓞/(ζ_n − 1))` | `log_card_quotient_zeta_sub_one` |
| `f_*`, `f^*`, projection formula | power maps `[t]`, fibres `μ_t z`, rotations `R_ζ` | Hecke, `ℚ/ℤ` | `sum_log_norm_sub_mul_nthRoots`, `pow_mul_rotate` |
| `Δ² = 2 − 2g` | self-intersection `c(n) = I(n,n)/φ(n)` | the different; `log|d_{ℚ(ζ_{p^k})}|` | `selfIntersection_eq_sum_local`, `orbitIntersection_self_eq_log_discr` |
| — | regulator: Abel radius `r`; spacing radius `e^{−ε/n}` | — | `circleKernel`, `spacingRadius` |
| — | anomaly of `[t]`: `r ↦ r^t`, shift `log t` | — | `tendsto_log_one_sub_pow_sub_log_one_sub` |
| — | Hecke cocycle `β(n,t) = c(tn) − c(n)` | `log t − Σ_{p∣t,p∤n} log p/(p−1)` | `heckeCocycle_eq` |
| local intersection at `v` | `p`-ladder `{cp^j}`; tower form `K_q = (q^{|i−j|})`, levels weighted by `φ(p^k)` | KMS matrix, `q = p^{−1/2}` | `kmsForm_eq_orbit_levels` |
| one Frobenius ladder | transverse ladders: `L_p = log p (K_p − 1) ⊗ 1` on `ℓ²(⊕_p ℕ)` | `P = Σ_p L_p` | `ladderKernel_eq_tensor`, `weilPrimeKernel_eq_sum_ladderKernel` |
| — | rotation spectrum on `μ_N` | lattice germ `G_{r^N}(k/N)`, digamma `ψ(k/N)` | `rootCycleEnergy_eq`, `gauss_digamma_theorem` |
| Hodge index | archimedean (every regulator), local (every prime), global (RH) | — | `hasSum_pointEnergy`, `localForm_lower`, `riemannHypothesis_archPolar_ge_towers` |
| reflection pairing | Rosati product `Q(ρ) conj Q(ρ*)` of zero moments | — | `pair_pow_eq_two_re` |

**Words.**

* *Carrier* (chart): the characteristic circle, the scaling surface, the zero divisor, the gauge
  torus. A *transition* is a theorem identifying a pairing on one carrier with a pairing on another.
* *Finite*, *archimedean*, *Fourier* reading of a pairing: log-orders of intersection rings, sums of
  log-distances, rotation spectra.
* *Regulator*, *counterterm*, *renormalized pairing*: the parameter making the diagonal finite, the
  divergent diagonal removed, the limit. *Anomaly* of a correspondence: its effect on the
  counterterm. *Covariant*: zero anomaly.
* *Hecke cocycle*: the anomaly on the orbit `O_n`. *Saturated* cycle for `t`: supported on orders
  divisible by every prime of `t`. *Tame different*: `e(n) = Σ_{p∣n} log p/(p−1)`.
* *Ladder*: the orders `{cp^j}` with `p ∤ c`. *Tower form*: the finite intersection at `p` with its
  natural diagonal. *Level*: the term of the tower form attached to `O_{p^k}`. *Transverse*: two
  ladders of different primes meet in at most one order.
* *Log-atom test*: narrow bumps at the points `log n` of a set of orders, narrower than
  `log(1 + 1/M)`. *Pole direction*: the cycle `x_n = n^{−1/2}`.
* *Local*, *archimedean*, *global* Hodge index: positivity at one prime, at finite regulator, and of
  the explicit-formula pairing.

---

## 4. Mechanisms

1. **Projection formula** (`sum_log_norm_sub_mul_nthRoots`). `Σ_{ω∈μ_t} log|z − ωw| = log|z^t − w^t|`.
2. **Regulator anomaly** (`sum_circleKernel_fibre`, `cycleEnergy_pullback`,
   `tendsto_renormalized_pullback_sub`). `[t]` maps the radius `r` to `r^t`; the pullback of a cycle has
   `t` times the energy at `r^t`, and its renormalized energy is shifted by `−t log t` per unit mass.
3. **Intersection numbers are log-orders** (`log_card_quotient_cyclotomicValue`). The norm of `Φ_m(ζ_n)`
   is the product over the complex embeddings, i.e. over `O_n`, of `∏_{ξ∈O_m}(η − ξ)`.
4. **Adjunction** (`selfIntersection_eq`, `selfIntersection_eq_sum_local`,
   `orbitIntersection_self_eq_log_discr`). `log` is a derivation of Dirichlet convolution, so
   `μ * (id·log) = φ·log + φ*Λ` and `(φ*Λ)(n) = φ(n) e(n)`.
5. **Hecke cocycle** (`heckeCocycle_eq`, `tendsto_heckeVariation`, `not_exists_bounded_potential`).
   `P(tm,tn) = P(m,n)`; the renormalized torsion form moves by `−Σ x_n² β(n,t)`.
6. **Towers** (`kmsForm_eq_tail`, `kmsForm_eq_orbit_levels`, `kmsForm_lower`, `kmsForm_upper`). With
   tails `T_k = Σ_{i≥k} x_i q^{i−k}` and `x_k = T_k − qT_{k+1}`, `K_q(x) = T_0² + (1 − q²)Σ_{k≥1} T_k²`.
7. **Transverse decomposition** (`eq_of_sameLadder_of_sameLadder`, `weilPrimeKernel_eq_sum_ladderKernel`,
   `localForm_lower`, `localForm_upper`). Exactly one prime carries each entry; each local form is
   bounded by `2q log p |x|²/(1 ± q)`.
8. **Local forms do not sum** (`primeForm_poleVector_ge`, `not_exists_primeForm_le`). Along the pole
   direction the prime form exceeds `H_M Σ_{t≤M} Λ(t)/t ≍ (log M)²` at mass `H_{M²} ≍ log M`.
9. **Gauge blindness** (`signTwistKernel_eq`, `signTwistForm_eq`). `P^ε(m,n) = ε(m)ε(n)P(m,n)` for every
   real sign twin, Liouville's included.
10. **Fourier duality** (`torsionFourier_eq`, `gauss_digamma_theorem`, `rootCycleEnergy_eq`). On `μ_N`,
    `Σ_a −log|1 − rζ^a| cos(2πak/N) = ½(r^k G_{r^N}(k/N) + r^{N−k} G_{r^N}(1 − k/N))`; the rotation modes
    diagonalize the energy with lattice-germ eigenvalues; at `r → 1`, Gauss's theorem with `log N` as
    the anomaly of `[N]`.
11. **Transfer** (`primeSum_logAtom_eq`, `primeSum_logAtom_eq_towers`). On log-atom tests the lags
    `log k` see only exact ratios (`eq_of_abs_log_sub_lt`), and Weil's prime functional is
    `‖φ‖² Σ_{m,n} x_m x_n P(m,n)`.
12. **Spacing regulator** (`spacingForm_nonneg`, `tendsto_spacingForm`, `spacingLimit_transport`). Radii
    `ρ_mρ_n`, `ρ_n = e^{−ε/n}`, keep the Gram structure, give the scalar counterterm `log(1/(2ε))`, and
    leave only tame ramification as Hecke variation.
13. **Rosati moments** (`dualPoly_eq_conj`, `mul_dualPoly_of_critical`, `pair_pow_eq_two_re`). Zero moments
    of Dirichlet polynomials are collided on the line and Rosati-paired off it.

---

## 5. Pillar theorems

| Pillar | Statement | Lean |
|---|---|---|
| I. Projection formula | `Σ_{ω∈μ_t} log|z − ωw| = log|z^t − w^t|`; regularized: `r ↦ r^t` | `TheProjectionFormulaAndTheRegulatorAnomaly` |
| II. Regulator anomaly | `log(1 − r^t) − log(1 − r) → log t`; renormalized pullback shifted by `−t log t |x|²` | same |
| III. Intersection numbers are log-orders | `I(n,m) = log #(𝓞_{ℚ(ζ_n)}/(Φ_m(ζ_n)))`, `Λ(n) = log #(𝓞/(ζ_n − 1))` | `TheArchimedeanIntersectionIsALogOrder` |
| IV. Adjunction | `I(n,n)/φ(n) = Σ_{p^a∥n}(a − 1/(p−1)) log p`; `I(p^k,p^k) = log|d_{ℚ(ζ_{p^k})}|` | `TheDifferentOfATorsionOrbit`, `TheArchimedeanIntersectionIsALogOrder` |
| V. Hecke cocycle | variation `−Σ x_n² β(n,t)`, `β = log t − Σ_{p∣t,p∤n} log p/(p−1)`; cocycle; `0 ≤ c(t) ≤ β ≤ log t`; not a bounded coboundary; covariance up to the degree character on saturated cycles | `TheHeckeCocycleOfRenormalization` |
| VI. Local Hodge index | tower decomposition with orbit-size weights; KMS bounds; ladder form `= log p (K_q − 1)` | `TheTowerFormOfAPrime` |
| VII. Transversality | one prime per nonzero entry; `L_p = log p (K_p − 1) ⊗ 1`; `P = Σ_p L_p`; local bounds | `ThePrimeKernelIsASumOfTransverseTowers` |
| VIII. Local is not global | no `C` with `Σ x_m x_n P(m,n) ≤ C|x|²` | `TheLocalFormsDoNotSum` |
| IX. Gauge blindness | sign twins have unitarily equivalent prime forms | `TheFiniteIntersectionIsGaugeBlind` |
| X. Fourier duality | rotation spectrum on `μ_N` = lattice germs; Gauss's digamma theorem with anomaly `log N` | `GaussDigammaIsTheFourierTransformOfTheTorsionEnergy`, `TheEllipticCorrespondencesOfTheCircle` |
| XI. Transfer | prime functional on log-atom tests = `‖φ‖² Σ_p Q_p`; under RH, `‖φ‖² Σ_p Q_p ≤ Re(archimedean + polar part)` | `WeilsPrimeFunctionalIsTheFiniteIntersection` |
| XII. Spacing regulator | positive at every `ε`; scalar counterterm; Hecke covariant up to tame ramification; indefinite limit | `TheSpacingRegulatorRemovesTheAnomaly` |
| XIII. Rosati moments | zero moments collided on the line, Rosati off it; real on reflection-closed configurations | `ZeroMomentsAreRosatiPairings` |

---

## 6. Questions and answers

1. **Can the diagonal be renormalized covariantly?** Not with a uniform regulator: the anomaly of
   `[t]` is `log t` per point (Pillar II), and on orbit cycles the variation is the cocycle `β`, which
   is not a bounded coboundary (Pillar V). With a regulator scaled to the torsion spacing the anomaly
   disappears and only tame ramification remains, invariant on saturated cycles (Pillar XII). The
   price is the sign: the counterterm becomes scalar, its null cone is `{0}`, and by the survival law
   (RBG) positivity before the limit says nothing after it; the covariant limit is indefinite. The
   missing object is a covariant regulator whose counterterm has a nontrivial null cone.
2. **Where do integers enter on the prime side?** As orders of finite rings: every intersection number
   of torsion orbits, and `Λ(n)` itself, is a log-order (Pillar III); the self-intersection is the
   log-discriminant (Pillar IV); the levels of a tower are weighted by orbit sizes `φ(p^k)` (Pillar VI);
   the anomaly is `log #ker[t]` (Pillar II). These integers are local: they produce the local Hodge
   index and the identities, not the global sign (Pillar VIII).
3. **Is there an elliptic correspondence?** Yes: rotations by `μ_∞`, exact for the archimedean
   pairing, forming with the power maps the affine semigroup `z ↦ ζz^t` (`pow_mul_rotate`). Their
   spectrum on `μ_N` is the lattice germ at `k/N`, renormalized to `−(ψ(k/N) + γ + log N)/N`: archimedean
   data at rational points (Pillar X). Rotations localize in the additive dual `ℚ/ℤ`; zero ordinates
   live in the multiplicative dual. An elliptic localizer for zeros cannot come from the torsion.
4. **What is the base?** Over `𝔽_q` all places act on one Frobenius ladder. Over `ℤ` each prime has
   its own ladders, transverse to those of every other prime; the prime kernel is a sum of commuting
   local operators `log p (K_p − 1) ⊗ 1` on `ℓ²(⊕_p ℕ)` (Pillar VII), whose joint symbol lives on the
   gauge torus with the heights `n^{it}` on its Kronecker line. The finite intersection is blind to the
   order-two points of that torus (Pillar IX). There is no common ladder: that is the absence of a base.
5. **Which positivity holds where?** At finite regulator, archimedean positivity on every point cycle
   (`hasSum_pointEnergy`) and on orbit cycles (AET); at each prime, the local Hodge index with explicit
   bounds (Pillars VI–VII); globally, the sum of local forms is unbounded (Pillar VIII), Weil's prime
   functional on log-atom tests equals that sum (Pillar XI), and RH is the statement that the
   archimedean and polar parts dominate it. The archimedean self-energy of an atom of width `δ` grows
   like `log(1/δ)` (RHTower separated bumps), the sum of towers like `log M` along the pole direction:
   the global sign is the comparison of these two growths.
6. **What is the two-point form of the missing statement?** Moments of Dirichlet polynomials over the
   zeros, computable from primes up to the square-root threshold, are Rosati pairings: positive on
   critical configurations, `2 Re(Q(ρ)conj Q(ρ*))^k` on off-line pairs (Pillar XIII). Their positivity is
   a Hodge index of the same type as Weil's; beyond the threshold its prime-side form is TTPC's bound on
   the coalescent surplus.

---

## 7. Traps

| Trap | Truth |
|---|---|
| The projection formula is exact, so the renormalized pairing is Hecke covariant | `[t]` rescales the regulator; the counterterm moves by `log t` |
| The torsion counterterm is a scalar, so it commutes with everything | per orbit it is scalar; its change under `[t]` is the cocycle `β` |
| A covariant regulator gives a sign | the spacing regulator is covariant up to tame ramification, positive at every `ε`, and its limit is indefinite |
| Integer intersection numbers give the sign | integrality is local; the sum of local forms is unbounded |
| Local positivity at every prime sums to global positivity | the identity is subtracted once per prime; `Σ_p log p/√p` diverges |
| The product formula makes the torsion pairing trivial | the content is its split into finite and archimedean parts |
| Rotations are an elliptic localizer for zeros | their spectrum is the archimedean factor at rational points |
| A finer prime-side statement separates `ζ` from its twins | every real sign twin has a unitarily equivalent prime form |
| Over `ℤ` there is one Frobenius | there is one ladder per prime, and the ladders are transverse |
| Moments over zeros are positive data | they are Rosati pairings; positive only on critical configurations |

---

## 8. Tools

**From sibling programmes:** torsion orbits, orbit intersections, the Hecke law, Abel energies and
their Ramanujan Gram structure, the gcd twist, the renormalized torsion limit (AET); the survival law
and the lattice germ with its digamma limit (RBG); separated narrow bumps and the archimedean Lévy
gain (RHTower); Weil positivity under RH for real `C²_c` tests (BSU); Mertens' second theorem
(RHTower); the cyclotomic discriminant, norms and embeddings (Mathlib).

**Built here:** the projection formula and the regulator anomaly for point cycles; log-orders of
cyclotomic intersection rings; the derivation `μ * (id·log) = φ·log + φ*Λ` and the different; the Hecke
cocycle and the Hecke variation law; the Kac–Murdock–Szegő tower calculus (tails, levels, bounds);
ladder kernels and the transverse decomposition of Weil's prime kernel; the pole-direction lower
bound; sign gauges; the rotation diagonalization of point cycles and the folding of frequencies on
`μ_N`; Gauss's digamma theorem; log-atom tests and the transfer identity; the spacing regulator;
Rosati moments.

---

## 9. Open research topics

1. **A covariant regulator with a nontrivial null cone.** A family of positive pairings on torsion
   cycles, Hecke covariant up to tame ramification, whose counterterm is not a multiple of the
   identity. By the survival law this is exactly what a sign through the limit requires.
2. **The archimedean side of the transfer.** Compute the archimedean and polar part of Weil's form on
   log-atom tests in the same tower coordinates, so that the comparison of Question 5 becomes one
   inequality between explicit forms on `ℓ²(⊕_p ℕ)`.
3. **Arithmetic Riemann–Roch on torsion orbits.** The lattice `𝓞_{ℚ(ζ_n)}` with its trace form has a
   theta `h⁰` whose Riemann–Roch defect is `½ log|d|`, the self-intersection of Pillar IV; a section
   functor on the scaling surface with this defect would be the `F3` question of the review.
4. **The discriminant for all `n`.** `I(n,n) = log|d_{ℚ(ζ_n)}|` beyond prime powers.
5. **Indices.** The positive index of the renormalized torsion form on a ladder is bounded by the
   number of levels whose self-intersection lies below the local bound; an index law for finite boxes.
6. **Thresholds as weights.** The ratio of the log-atom width to the largest order as a weight
   variable; the square-root threshold as weight `½`.

---

## 10. Success criteria and contribution standards

AIT succeeds when it proves the Hodge index for the explicit-formula pairing on a class of cycles
that is cofinal and passes the battery, or proves that no regularization of a stated class can carry
the sign, together with the strongest positive survivor; and when each question of §6 has an answer
of that kind.

A contribution is an unconditional Lean theorem about the objects of §3. It names its carrier and
which reading (finite, archimedean, Fourier) it concerns; it states covariance (the anomaly) and
positivity separately; it separates identities from signs; it states what it gives over `𝔽_q`, on the
golden datum `1 − 5X + 5X²` and on the sign twins. Every no-go records its positive survivor.

Principles: identities first, sign last; every regularization carries its anomaly; no positivity
without a count; local is not global; a reformulation is not a reduction.
