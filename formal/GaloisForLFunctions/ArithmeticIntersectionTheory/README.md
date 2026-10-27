# Arithmetic Intersection Theory (AIT)

**One question.** Weil's proof of the Riemann hypothesis for a curve over `𝔽_q` is intersection
theory on `C × C`: intersection numbers are integers, correspondences act through a projection
formula, the diagonal has a finite self-intersection given by adjunction, and the Hodge index
theorem supplies the sign. Over `ℤ` the explicit formula is a pairing of the same shape. Which of
the four ingredients exist for it, on which carrier, how do the carriers glue, and what exactly is
the one statement that is missing?

AIT is the intersection theory of the **characteristic circle** — the torsion `μ_∞ ⊂ 𝔾_m(ℂ)` of the
multiplicative group over `ℤ`, with its three symmetries (power maps, rotations, Galois) — and of
its transfer to the scaling surface on which Weil's form lives. Its organizing sentence:

> *Over `ℤ` the intersection numbers of torsion cycles exist, are integers place by place, and obey
> the projection formula. The diagonal exists only after renormalization, and the renormalization
> is not covariant: the Hecke correspondence `[t]` rescales the regulator by its degree, and the
> anomaly is `log #ker[t]` corrected by the different. Weil's prime form is the finite intersection
> pairing; RH is a Hodge index for it with the archimedean place supplying the diagonal.*

Namespace `GaloisForLFunctions.ArithmeticIntersectionTheory`; umbrella
`ArithmeticIntersectionTheory.lean`. Everything is unconditional; RH and its partial forms appear
only inside equivalences.

---

## 1. Place in the research

Every live route of the frontier ends at an RH-equivalent receiver plus one missing sign. The
exhaustion laws behind the three walls reduce to three structural facts (report
[fable](../../../docs/reports/review-2710/fable.md), §1.3): the Hecke algebra is commutative, every
receiver is a linear functional of the explicit formula, and the diagonal has no finite
self-intersection. Over `𝔽_q` a single object — the surface `C × C` with its intersection theory —
removes all three. AIT asks what remains of that intersection theory over `ℤ` and builds it where
it exists.

The corpus already holds the pieces on separate carriers. AIT is the dictionary between them and
the theory of their gluing.

| Programme | What AIT takes | What AIT adds |
|---|---|---|
| [ArithmeticEffectivityTheory](../ArithmeticEffectivityTheory/README.md) | torsion orbits `O_n`, orbit intersections `I(m,n)`, the Hecke law `I(m,mt) = φ(m)Λ(t)`, Abel energies `T_r`, the renormalized torsion limit of Weil's prime kernel, `log Φ_n(1) = Λ(n)` | correspondences on torsion cycles and the projection formula; the regulator anomaly; the Hecke cocycle; towers; intersection numbers as log-orders |
| [ArithmeticElectrostatics](../ArithmeticElectrostatics/README.md) | the potential picture, self-energies, the arithmetic point, counterterm rates | the covariance theory of the counterterm (anomaly, cocycle, its local decomposition) |
| [RenormalizedBiarithmeticGeometry](../RenormalizedBiarithmeticGeometry/README.md) | the survival law, the counterterm rank dichotomy, the archimedean lattice germ and its digamma limit | Fourier duality: the lattice germ is the Fourier transform of the torsion energy on `μ_N` |
| [ArithmeticCastelnuovoSeveri](../ArithmeticCastelnuovoSeveri/README.md), [ArithmeticOrientationGeometry](../ArithmeticOrientationGeometry/README.md) | the scaling surface, its Hodge index, Lefschetz numbers, the Hecke tower of a prime on the zero side, `𝔽_q` calibration | the prime-side tower decomposition and the local Hodge index at `p` |
| [ArithmeticPolarization](../ArithmeticPolarization/README.md), [ConjugateDiagonalGeometry](../ConjugateDiagonalGeometry/README.md) | `W`, `D`, `Δ`, local types at off-line pairs | the place of each form in the intersection dictionary |
| [BiarithmeticGaugeGeometry](../BiarithmeticGaugeGeometry/README.md), [ArithmeticCorrelationGeometry](../ArithmeticCorrelationGeometry/README.md) | the gauge torus `(ℝ/ℤ)^𝒫`, the Kronecker line of heights | the prime kernel as a sum of commuting local operators on the tensor product of prime ladders |
| [ArithmeticPositiveDuality](../ArithmeticPositiveDuality/README.md) | `Aff(ℚ)` states, Bost–Connes temperature, successor blindness to atoms | the affine semigroup `z ↦ ζ z^t` of the circle and what its elliptic part can and cannot localize |
| [TransThresholdPairCorrelation](../TransThresholdPairCorrelation/README.md), [SquareRootThreshold](../SquareRootThreshold/README.md) | pair correlation, coalescent surplus, the square-root threshold | the two-point question in intersection language |

AIT does not re-prove what these programmes own; it imports them and proves the laws that glue
them.

---

## 2. Why

**Weil's four ingredients.** On `C × C`: (i) intersection numbers of curves are integers, and the
Lefschetz number `Γ_m · Δ` counts points; (ii) a correspondence `f` acts on cycles by `f_*` and
`f^*` with the projection formula `f_*A · B = A · f^*B`; (iii) the diagonal is a curve, so its
self-intersection is the finite number `2 − 2g`, given by adjunction `Δ² = −K · Δ`; (iv) the Hodge
index theorem makes the intersection form negative definite on the primitive part, and on the plane
of `Γ_m` and `Δ` this is the Hasse–Weil bound. (i)–(iii) are identities; (iv) is the sign.

**Over `ℤ` the first three exist on the characteristic circle.** The torsion orbit `O_n` (the
primitive `n`-th roots of unity) is the horizontal divisor `Φ_n = 0` of `𝔾_m` over `ℤ`.

* *Intersection numbers.* Two orbits meet at a prime `p` with multiplicity `v_p(Res(Φ_m, Φ_n))`, a
  nonnegative integer, nonzero only when `m/n` is a power of `p`. The finite intersection
  `Σ_p v_p(Res) log p = log |Res(Φ_m, Φ_n)|` is the logarithm of the order of the intersection
  scheme. The archimedean intersection `Σ_{ζ∈O_m, η∈O_n} log |ζ − η|` computes the same number: the
  product formula. For `m ∣ n` it is `φ(m) Λ(n/m)` (AET), and with the orbit `O_1 = {1}` (the
  arithmetic point) it is `Λ(n)`.
* *Correspondences.* The power map `[t] : z ↦ z^t` is the Hecke correspondence. It pushes `O_n` onto
  `O_{n/(n,t)}` and pulls `O_m` back to the orbits `O_d` with `d/(d,t) = m`. The projection formula
  holds for the archimedean pairing because `z^t − u = ∏_{w^t = u} (z − w)`.
* *The diagonal.* The self-intersection of `O_n` is the log-discriminant `log |disc Φ_n|`; per point
  it is `Σ_{p^a ∥ n} (a − 1/(p−1)) log p`, the different of `ℚ(ζ_n)` — an adjunction formula.

**What is not covariant is the regularization.** The archimedean pairing is singular on the
diagonal. The corpus regularizes it by the Abel radius `r < 1`: the energies `T_r` are positive (an
archimedean Hodge index at every `r`), and Weil's prime kernel is their renormalized limit after
subtracting `log(1/(1 − r))` per point (AET). The projection formula for the regularized pairing
reads `Σ_{ω ∈ μ_t} −log |1 − r ω z| = −log |1 − r^t z^t|`: the correspondence `[t]` replaces the
regulator `r` by `r^t`, and `1 − r^t ≈ t (1 − r)`. The divergence therefore shifts by `log t`, the
logarithm of the number of points of `ker [t]`. This anomaly, corrected at the primes dividing `t`
by the tame part of the different, is the whole failure of Hecke covariance of the renormalized
torsion form. It is a cocycle on the Hecke monoid; it is not the coboundary of any bounded
potential.

**The local sign exists; the global sign is RH.** At a single prime `p` the finite intersection on a
ladder `{n p^j}` is a sum over the levels of the `p`-power tower, each weighted by the size `φ(p^k)`
of a torsion orbit: a positive form. Weil's prime kernel is `Σ_p log p` times (this tower form minus
the identity). The identity is subtracted because Weil's prime sum has no diagonal term, and
`Σ_p log p` diverges: local positivity at every prime does not sum to a global one. Over `𝔽_q` there
is one Frobenius and one ladder; over `ℤ` the ladders of different primes are transverse and the
local forms act on independent factors of a tensor product whose spectrum lives on the gauge torus.

**Three computations of one pairing.** On `μ_N` the torsion energy has three readings: the finite
intersection (integers), the archimedean energy (logarithms of distances), and its Fourier transform
under rotations. The Fourier transform is the archimedean lattice germ `Σ_k r^k/(k + z)` at
`z = a/N`, whose renormalized limit is the digamma function: Gauss's digamma theorem is the Fourier
transform of the torsion energy, and its `log N` is the same regulator anomaly. The archimedean
local factor of the explicit formula and the torsion of the circle are Fourier dual.

**Why a field.** The corpus has each ingredient on its own carrier and each wall as a theorem about
one carrier. What is missing is a single object with all four ingredients. AIT builds the
dictionary in which the ingredients are the same pairing read in different coordinates, computes
the anomaly that separates covariance from positivity, and states the Hodge index that would close
the gap in the form in which every other ingredient is already a theorem.

---

## 3. Objects and language

| Over `𝔽_q` (`C × C`) | AIT object | Over `ℤ` | Lean |
|---|---|---|---|
| curves on `C × C` | torsion cycles: formal sums `Σ x_n O_n` of Galois orbits; point cycles on `μ_N`; character cycles `Σ χ(a) δ_{ζ^a}` | divisors `Φ_n = 0` of `𝔾_m/ℤ` | `primitiveRoots` |
| `D · E` | finite intersection `(O_m · O_n)_p = v_p(Res(Φ_m, Φ_n))`; archimedean intersection `I(m,n) = Σ log|ζ − η|` | `log |Res(Φ_m, Φ_n)|`; product formula | `orbitIntersection` (AET) |
| Lefschetz `Γ_m · Δ = N_m` | intersection with the arithmetic point `O_1 = {1}` | `Λ(n) = log #(𝓞_{ℚ(ζ_n)}/(ζ_n − 1))` | planned |
| correspondence `f`, `f_*`, `f^*` | power map `[t]`, rotation `R_ζ`, Galois `σ_a` | Hecke `T_t`, additive `ℚ/ℤ`, `Ẑ^×` | planned |
| projection formula | `Σ_{w^t = u} log|z − w| = log|z^t − u|` | exact | planned |
| `Δ² = 2 − 2g` | self-intersection of `O_n`: `log |disc Φ_n|`; density `c(n) = Σ_{p^a∥n}(a − 1/(p−1)) log p` | the different of `ℚ(ζ_n)` | `orbitIntersection_self` (AET) |
| — | regulator `r`, regularized pairing `T_r`, counterterm `log(1/(1−r))` per point | Abel energy | `torsionEnergy` (AET) |
| — | regulator anomaly of `[t]`: `r ↦ r^t`, shift `log t = log #ker[t]` | — | planned |
| — | Hecke cocycle `β(n,t) = c(tn) − c(n)` | `log t − Σ_{p∣t, p∤n} log p/(p−1)` | planned |
| local intersection at `p` | the `p`-ladder `{n p^j}`, the tower form `K_p = Σ_k φ(p^k) v_k v_kᵀ` | Kac–Murdock–Szegő matrix `(p^{−|i−j|/2})` | planned |
| Frobenius ladder | the tensor product `⊗_p ℓ²(ℕ)` of prime ladders; the gauge torus as its base | `P = Σ_p log p (K_p − 1)` | planned |
| — | Fourier transform on `μ_N` | lattice germ `G_r(a/N)`, digamma `ψ(a/N)` | `latticeGerm` (RBG) |
| Hodge index | positivity of the regularized energy (archimedean, every `r`); of the tower form (local, every `p`); of Weil's form (global, RH) | — | `sum_sum_torsionEnergy_nonneg` (AET) |

**Words.**

* *Carrier* (chart): the characteristic circle, the scaling surface, the zero divisor, the gauge
  torus. A *transition* is a theorem identifying a pairing on one carrier with a pairing on another.
* *Finite*, *archimedean* and *Fourier* reading of a pairing: the three computations above.
* *Regulator*: the parameter (`r`, a width `ε`, a horizon `N`) that makes the diagonal finite.
  *Counterterm*: the divergent diagonal removed in the limit. *Renormalized pairing*: the limit.
* *Anomaly* of a correspondence: the change of the counterterm under it. *Covariant*: zero anomaly.
* *Hecke cocycle*: the function `β(n,t)` measuring the anomaly on the orbit `O_n`. *Saturated*
  cycle (for `t`): supported on orders divisible by every prime of `t`.
* *Ladder*: the orders `{n p^j : j ≥ 0}` with `p ∤ n`. *Tower form*: the finite intersection at `p`
  with its natural diagonal. *Level*: the term of the tower form attached to `O_{p^k}`.
* *Local*, *archimedean*, *global* Hodge index: positivity at one prime, at finite regulator, and of
  the explicit-formula pairing.

---

## 4. Mechanisms

1. **Projection formula.** `z^t − u = ∏_{w^t = u}(z − w)` gives
   `Σ_{w ∈ [t]^{-1}u} log|z − w| = log|z^t − u|`: the archimedean pairing of a cycle with the pullback
   of another equals the pairing of its pushforward with the other.
2. **Regulator anomaly.** `1 − r^t z^t = ∏_{ω ∈ μ_t}(1 − r ω z)`: pushforward by `[t]` turns the
   regularized pairing at radius `r` into the one at radius `r^t`. Since `(1 − r^t)/(1 − r) → t`, the
   counterterm `log(1/(1 − r))` shifts by `−log t`. The anomaly is the logarithm of the degree.
3. **Adjunction (the different).** The self-intersection density of `O_n` is
   `c(n) = log n − Σ_{p ∣ n} log p/(p − 1) = Σ_{p^a ∥ n}(a − 1/(p − 1)) log p`, the different exponent of
   `ℚ_p(ζ_{p^a})` per unit degree, summed over the places.
4. **The Hecke cocycle.** Weil's prime kernel is Hecke invariant, so the renormalized torsion form
   changes under `[t]` only through its diagonal: by `−Σ_n x_n² β(n, t)` with
   `β(n,t) = log t − Σ_{p ∣ t, p ∤ n} log p/(p − 1)`, the anomaly minus the tame ramification of
   `ℚ(ζ_{tn})/ℚ(ζ_n)`. `β` is a cocycle, nonnegative, vanishes in second order on saturated cycles,
   and is not the coboundary of a bounded potential.
5. **Towers.** On a `p`-ladder the finite intersection with its natural diagonal is
   `Σ_{k ≥ 0} φ(p^k) v_k v_kᵀ`, `v_k(j) = p^{−j/2} 𝟙[j ≥ k]`: the levels of the tower of `p`-power
   torsion, each weighted by the number of its points. It is the Kac–Murdock–Szegő matrix
   `(p^{−|i−j|/2})`, with spectrum in `[(1 − q)/(1 + q), (1 + q)/(1 − q)]`, `q = p^{−1/2}`, and
   symbol `(1 − 1/p) |1 − p^{−1/2 − it}|^{−2}`, the squared local Euler factor at the centre.
6. **Prime kernel as a sum of local forms.** `P = Σ_p log p (K_p − 1)`. The `K_p` act on independent
   coordinates of the exponent lattice `⊕_p ℕ`, so they commute; `P` is a sum of commuting local
   operators on `⊗_p ℓ²(ℕ)`. Each local form is bounded below; their sum is not, because the
   identity is subtracted once per prime.
7. **Fourier duality.** `Σ_{a mod N} −log|1 − r ζ_N^a| cos(2πak/N) = ½[r^k G_{r^N}(k/N) + r^{N−k} G_{r^N}(1 − k/N)]`
   with the lattice germ `G_s(z) = Σ_m s^m/(m + z)`. At `r → 1` this is Gauss's digamma theorem, with
   `log N` the regulator anomaly of `[N]`.

---

## 5. Pillar theorems (targets)

| Pillar | Statement | Module |
|---|---|---|
| I. Correspondences | power maps on orbits (fibres of size `φ(n)/φ(n/(n,t))`), projection formula for the archimedean pairing | `TheCorrespondencesOfTheCharacteristicCircle` |
| II. Regulator anomaly | regularized projection formula `r ↦ r^t`; anomaly `log t` | `TheRegulatorAnomaly` |
| III. Intersection numbers are log-orders | `Λ(n) = log #(𝓞_{ℚ(ζ_n)}/(ζ_n − 1))`; finite intersections are integers | `IntersectionNumbersAreLogOrders` |
| IV. Adjunction | `c(n) = Σ_{p^a∥n}(a − 1/(p−1)) log p` | `TheDifferentOfATorsionOrbit` |
| V. Hecke cocycle | variation law, cocycle identity, bounds, saturated balance, nontriviality, covariance up to the degree character | `TheHeckeCocycleOfRenormalization` |
| VI. Towers | tower decomposition, local Hodge index at `p`, KMS bounds, `P = Σ_p log p (K_p − 1)` | `TheTowerDecompositionOfThePrimeKernel` |
| VII. Fourier duality | finite-regulator identity and Gauss's digamma theorem with anomaly `log N` | `GaussDigammaIsTheFourierTransformOfTheTorsionEnergy` |
| VIII. Transfer | Weil's prime form as the finite intersection pairing; RH as a Hodge index in tower form | `TheHodgeIndexInTowerForm` |

---

## 6. Questions the programme answers

1. **Can the diagonal be renormalized covariantly?** The anomaly theorem: no regularization by a
   radius is Hecke covariant; the defect is the cocycle `β`, which is not a bounded coboundary. The
   survivor: on saturated cycles the renormalized form transforms by the degree character, and the
   counterterm `log(1/(1 − r)) − log n` is covariant up to the tame ramification.
2. **Where do integers enter on the prime side?** As orders of intersection schemes (`Λ(n)` is the
   log-order of `𝓞/(ζ_n − 1)`), as the orbit sizes `φ(p^k)` weighting the levels of a tower, and as
   the degree `t = #ker[t]` in the anomaly. Which of them can carry a sign, and which cannot.
3. **Is there an elliptic correspondence?** Rotations by `μ_∞` are elliptic and exact for the
   archimedean pairing; together with power maps they form the affine semigroup `z ↦ ζ z^t`. What
   they localize, and why Weil's form, which lives on Galois-invariant cycles, sees them only through
   Ramanujan averages.
4. **What is the base?** Over `𝔽_q` one Frobenius ladder; over `ℤ` a tensor product of transverse
   prime ladders, whose joint symbol lives on the gauge torus, with the heights `n^{it}` on its
   Kronecker line.
5. **Which positivity holds where?** At finite regulator (archimedean), at each prime (towers),
   globally (RH): the exact interfaces between them.
6. **What is the two-point form of the missing statement?** Pair correlation as the collided
   self-intersection of the zero divisor; moments over zero ordinates as Rosati pairings.

---

## 7. Traps

| Trap | Truth |
|---|---|
| The projection formula is exact, so the renormalized pairing is Hecke covariant | `[t]` rescales the regulator; the counterterm moves by `log t` |
| The torsion counterterm is a scalar, so it commutes with everything | its value per orbit is scalar, its change under `[t]` is the cocycle `β` |
| Integer intersection numbers give the sign | integrality is local; the sign is global |
| Local positivity at every prime sums to global positivity | the identity is subtracted once per prime and `Σ_p log p` diverges |
| The product formula makes the torsion pairing trivial | the total pairing of distinct orbits is zero; the content is its split into finite and archimedean parts |
| Rotations are an elliptic localizer for zeros | they diagonalize the Fourier variable of the circle, dual to the archimedean factor at rational points, not to zero ordinates |
| Over `ℤ` there is one Frobenius | there is one ladder per prime; the ladders are transverse |

---

## 8. Tools

**From sibling programmes:** torsion orbits, orbit intersections, the Hecke law, Abel energies, the
gcd twist and the renormalized torsion limit (AET); the survival law and the lattice germ with its
digamma limit (RBG); the scaling surface and the `𝔽_q` calibration (ACS, AOG); the forms `W`, `D`,
`Δ` (APol, CDG); the gauge torus (BGG, ACG); Mertens' estimates (RHTower).

**To build here:** correspondences on torsion cycles; the projection formula and the regulator
anomaly; intersection numbers as log-orders; the different; the Hecke cocycle; tower forms and the
local Hodge index; Fourier duality on `μ_N`; the tower form of Weil's prime kernel.

---

## 9. Open research topics

1. **Covariant regulators.** A regularization scheme whose anomaly is a coboundary, e.g. a radius
   depending on the order `n` (spacing `2π/n`), with a positivity statement before the limit.
2. **Global Hodge index from local towers.** An inequality bounding `Σ_p log p · tower_p(x)` by
   `Σ_p log p · |x|²` plus the archimedean and polar terms.
3. **Character cycles.** The torsion energy of Galois-twisted cycles and `L(1, χ)`.
4. **The affine semigroup.** Positivity of pairings invariant under `z ↦ ζ z^t`.
5. **Two-point statistics** as self-intersections of the zero divisor.

---

## 10. Success criteria and contribution standards

AIT succeeds when it proves the Hodge index for the explicit-formula pairing on a class of cycles
that is cofinal and passes the battery, or proves that no regularization of a stated class can carry
the sign, together with the strongest positive survivor; and when each question of §6 has an answer
of that kind.

A contribution is an unconditional Lean theorem about the objects of §3. It names its carrier and
which reading (finite, archimedean, Fourier) it concerns; it states covariance (the anomaly) and
positivity separately; it separates identities from signs; and it states what it gives over `𝔽_q`,
on the golden datum `1 − 5X + 5X²` and on the Liouville twin. Every no-go records its positive
survivor.

Principles: identities first, sign last; every regularization carries its anomaly; no positivity
without a count; local is not global; a reformulation is not a reduction.
