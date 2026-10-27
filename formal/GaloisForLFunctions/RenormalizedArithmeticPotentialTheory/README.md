# Renormalized Arithmetic Potential Theory of the Characteristic Circle (RAPT)

**One question.** Over `𝔽_q` Weil's proof of the Riemann hypothesis uses one pairing that is
positive, Frobenius equivariant and finite on the diagonal. Over `ℤ` the corpus has the pieces on
separate carriers: a positive potential theory of the zero divisor (AES), an intersection theory of
the characteristic circle with an anomalous diagonal (AIT), and a renormalization theory whose
survival cones decide what positivity passes a limit (RBG). The pieces are glued by
renormalization: every pairing of the explicit formula is a regularized self-energy, and the two
places of `ℚ` regularize the same diagonal. **Which regulator, which counterterm and which coupling
of the prime place, the archimedean place and the arithmetic point keep positivity and Hecke
equivariance together through the limit — and which provably cannot?**

RAPT is the theory of the **renormalization data** of the explicit formula: regulators, the
counterterms they produce, the rank and survival cone of those counterterms, the anomaly of the
Hecke correspondences, and the coupling of the places that must pay the divergence. Its organizing
sentence:

> *The rank of a counterterm is a property of the regulator, not of the pairing. The Abel radius
> renormalizes self-energies of points and leaves nothing; the horizon renormalizes Weil's form and
> its divergence lives exactly on the torsion orbits — the arithmetic point for uniform profiles,
> the orbit `O_d` for the sublattice `dℤ` — with the characters as survivors. Covariance forces a
> scalar counterterm, and the scalar the archimedean place must supply at atomic resolution `N` is
> the anomaly `log N` of `[N]`, with constant one.*

Namespace `GaloisForLFunctions.RenormalizedArithmeticPotentialTheory`; umbrella
`RenormalizedArithmeticPotentialTheory.lean`. Everything is unconditional; RH and its partial forms
appear only inside equivalences.

---

## 1. Place in the research

The frontier ([obstacles summary](../../../docs/reports/review-2710/obstacles-summary.md), §4)
locates, ingredient by ingredient, what of Weil's argument over `𝔽_q` exists over `ℤ`. A positive
Hermitian structure with Hecke similitudes exists after regularization; local Hodge index holds at
every prime; tensor amplification exists with a non-scaling loss. Missing are a finite
self-intersection of the diagonal, archimedean payment of the local-to-global divergence, and
stability of the computed equilibrium. All three are statements about one object: the
**counterterm** that the diagonal requires, and the place that pays it.

RAPT owns that object. Its questions are the second question (Q2) of the report — coupled
renormalization of the two places — and the renormalization face of the first (Q1: what bounds the
field) and the third (Q3: gauge charge). In wall terms it is Wall 14 (the diagonal), face 1.16
(polarization) and face 3.23 (positivity and equivariance in one form).

| Programme | What RAPT takes | What RAPT adds |
|---|---|---|
| [RenormalizedBiarithmeticGeometry](../RenormalizedBiarithmeticGeometry/README.md) | regularized families, survival cones, scheme independence, the torsion germ (identity counterterm), the lattice germ (polar hyperplane), periodic germs, the pole node, Ramanujan twins | the **coupled** survival law: what survives when two germs are joined, and the partner-rank bound |
| [ArithmeticIntersectionTheory](../ArithmeticIntersectionTheory/README.md) | orbit intersections, the different, the Hecke cocycle `β`, the regulator anomaly, the spacing regulator, Gauss's digamma duality, tower forms | the cost of the anomaly; covariance as a constraint on counterterms; the horizon regulator and its duality with the Abel radius |
| [ArithmeticElectrostatics](../ArithmeticElectrostatics/README.md) | the potential of `log|ξ|`, transverse energy and field, torsion self-intersections, the counterterm rates `≍ log N`, the arithmetic point | the exact constants: covariant counterterm `log N + O(1)`, torsion counterterm `≥ (3/2) log N` |
| [ArithmeticEffectivityTheory](../ArithmeticEffectivityTheory/README.md) | torsion orbits `O_n`, `I(m, n)`, the Hecke law, Abel energies, Weil's prime kernel `P` as a renormalized torsion energy | — |
| [ArithmeticPolarization](../ArithmeticPolarization/README.md), [ConjugateDiagonalGeometry](../ConjugateDiagonalGeometry/README.md) | `W`, `D`, `Δ`, `Re W = D − Δ`, the Hecke defect | the place of `D` and `W` among regularized families |
| [ArithmeticCastelnuovoSeveri](../ArithmeticCastelnuovoSeveri/README.md), [ArithmeticOrientationGeometry](../ArithmeticOrientationGeometry/README.md) | the scaling surface, Hodge index, `𝔽_q` calibration, the pole plane | the renormalized reading of `Δ² = 2 − 2g` |
| [BiarithmeticGaugeGeometry](../BiarithmeticGaugeGeometry/README.md) | the gauge torus, square-class blindness, sign twins | gauge behaviour of counterterms and survival cones |
| `RHTower` | Mertens' first theorem, Weil's explicit formula, separated-bump archimedean energies | — |

RAPT does not re-prove what these programmes own; it imports them and proves the laws that join
them.

---

## 2. Why

**Weil's diagonal over `𝔽_q`.** On `C × C` the diagonal is a curve; adjunction gives
`Δ² = 2 − 2g`, a finite number. The tensor-power argument works because this loss does not grow
with the power, and the Hodge index theorem supplies the sign on the primitive part.

**Over `ℤ` the diagonal is a divergence.** Every pairing of the explicit formula is singular on
the diagonal and must be regularized:

* the **prime place**: torsion orbits `O_n` on the circle with Green function `−log |1 − z w̄|`;
  the Abel radius `r < 1` makes the self-energy of each point finite, `log(1/(1 − r))`;
* the **archimedean place**: atoms at `log n` on the line with the archimedean kernel; a width `ε`
  makes the self-energy of an atom finite, `log(1/ε) + O(1)`;
* the **arithmetic point** `z = 1`, the orbit `O_1`: fixed by every power map, the node at which
  the torsion divergence and the archimedean divergence meet (the pole).

Positivity lives before the limit (Abel energies are Gram matrices), equivariance after it (Weil's
prime kernel is Hecke invariant). RBG proved that positivity passes the limit exactly on the null
cone of the counterterm and that the Abel torsion germ has the identity as counterterm: nothing
survives. AIT proved that the counterterm is not Hecke covariant: the regulator anomaly `log t` of
`[t]` minus the tame different. The report's central conjecture asks for an **admissible coupling**
of the places: low-rank counterterm, covariant finite part, survival cone containing the
degree-zero cycles.

**What a theory of renormalization data must decide.**

1. *Is the rank of the counterterm intrinsic?* It is not. It depends on the regulator. The Abel
   radius renormalizes the self-energy of every point and has full rank. The **horizon** (orders
   `≤ N`, the regularization Weil's form itself uses) produces no diagonal at all; its divergence
   accumulates along the Galois-invariant directions, and on arithmetically uniform profiles it is
   rank one and polar.
2. *What can coupling do?* A coupled positive family whose torsion block keeps its identity
   counterterm has counterterm rank at least the number of orders, and the torsion directions in
   its survival cone form a space of dimension at most the rank of the partner's counterterm. The
   archimedean germ has rank one: it pays one direction, and in the periodic class the only order
   it couples to is the arithmetic point.
3. *What does covariance cost?* A Hecke-covariant renormalized prime form has a scalar diagonal.
   Its minimal positive counterterm on orders `≤ N` is `log N + O(1)`: the anomaly of `[N]`, the
   archimedean self-energy at the atomic spacing, with constant one. The anomalous torsion
   renormalization costs at least `(3/2) log N`: the self-intersection `c(n) ≈ log n` is the price
   of the anomaly.

These three answers turn the report's central conjecture into a sharp statement about finite
parts. The divergences of the two places match in rank and constant; the sign is a statement about
what remains.

---

## 3. Objects and language

### 3.1 Carriers and charges

| Object | Definition | Lean |
|---|---|---|
| characteristic circle | `ℝ/ℤ`, torsion `μ_∞`, orbits `O_n` (primitive `n`-th roots), the arithmetic point `O_1 = {1}` | `primitiveRoots` (AET) |
| orbit intersection | `I(m, n) = Σ_{ζ∈O_m, η∈O_n} log |ζ − η|`, `= φ(m) Λ(n/m)` for `m ∣ n` | `orbitIntersection` (AET) |
| self-intersection density | `c(n) = I(n, n)/φ(n) = log n − Σ_{p∣n} log p/(p − 1)` | `selfIntersection` (AIT) |
| Weil's prime kernel | `P(m, n) = Λ(n/m)(n/m)^{−1/2}` on `m ∣ n`, `m ≠ n`, symmetric | `weilPrimeKernel` (AET) |
| atomic prime form | `P_N(x) = Σ_{m,n ≤ N} x_m x_n P(m, n)` | `atomicWeilForm` (AES) |
| torsion pairing | `Σ y_m y_n I(m, n)` against the self-mass `Σ φ(n) y_n²` | `torsionPairing`, `selfMass` (AES) |
| pole vector | `u^{(M)}_n = n^{−1/2}` for `n ≤ M` | `poleVector` |
| polar functional | `ℓ(x) = Σ x_n n^{−1/2}`: one factor of Weil's pole term `(Σ x_n √n)(Σ x_n/√n)` | `polarFunctional` |
| step profile | `x = Σ_i c_i u^{(M_i)}`: the log-scale profile `g = Σ c_i 𝟙_{[0, a_i]}`, `M_i = N^{a_i}` | `stepProfile` |
| sublattice pole vector | `u^{(M)} 𝟙_{d ∣ ·}`: the pole vector of `dℤ` | planned |

### 3.2 Renormalization data

| Object | Definition | Lean |
|---|---|---|
| regularized family | forms `Q_s` with `Q_s − σ_s B → A` (RBG) | `quad`, `survivalCone` (RBG) |
| regulator | the parameter making the diagonal finite: Abel radius `r`, spacing radius `e^{−ε/n}`, width `ε`, horizon `N` | — |
| counterterm `B`, rank, survival cone | the divergent part; its rank; its null cone | RBG |
| coupled family | a regularized family on a direct sum `V_P ⊕ V_A` of a prime block and a partner block | `CoupledCounterterm` |
| partner rank | the rank of the partner block `B_AA` of the counterterm | — |
| torsion survival | the projection of the survival cone to the prime block | — |
| matched direction | a prime-block vector paid by the partner: `B_PA = b vᵀ`, `B_AA = v vᵀ`, `|b| = 1` | — |
| anomaly of `[t]` | change of the counterterm under the Hecke transport `n ↦ tn` | `heckeCocycle` (AIT) |
| covariant renormalization | finite part `−P + diag(h)` invariant under every Hecke transport | `IsHeckeCovariant` |
| covariant counterterm `κ_cov(N)` | the least scalar `κ` with `κ |x|² ≥ P_N(x)` for all `x` | — |
| torsion counterterm `κ_tor(N)` | the least `κ` renormalizing the torsion pairing on orders `≤ N` | `RenormalizesAt` (AES) |
| horizon counterterm | the divergent part of `P_N` on a fixed profile space as `N → ∞` | — |

### 3.3 Words

*Regulator* and *counterterm* as in RBG. A counterterm is *scalar* (multiple of the identity),
*polar* (rank one, along the polar functional) or *orbital* (supported on the Galois-invariant
directions). A renormalization is *covariant* when its finite part is Hecke invariant, *anomalous*
otherwise. A coupling *pays* a prime direction when that direction lies in the projection of the
coupled survival cone. Two divergences are *matched* when their leading terms agree in rank and
constant. *Uniform* profiles depend on `log n` only; *arithmetic* profiles depend also on
divisibility. The *Abel*, *spacing* and *horizon* regulators are the three of §4.

Every theorem states its regulator, its counterterm with rank and survival cone, its anomaly, and
which place pays.

---

## 4. Mechanisms

### A. Regulators produce counterterms

1. **Abel radius** (RBG, AIT). The torsion energies `T_r(m, n)` are Gram matrices of Ramanujan
   modes; the counterterm is `φ(n) δ_{mn}`, the identity after normalization, survival cone `{0}`;
   under `[t]` the radius becomes `r^t` and the counterterm moves by `log t`.
2. **Spacing radius** (AIT). Radius `e^{−ε/n}` on `O_n`: still a scalar counterterm, the anomaly
   reduced to the tame different; still no survival.
3. **Horizon**. Orders `≤ N`. Weil's prime form has no diagonal; its divergence is an accumulation
   along Galois-invariant directions. On uniform step profiles
   `P_N(x) = ℓ(x)² + O(log N · ‖c‖₁²)`: a polar rank-one counterterm, survival cone `∫ g = 0`.

### B. Coupling the places

4. **Coupled survival law.** For a positive coupled counterterm `B` on `V_P ⊕ V_A` with positive
   definite prime block: `B_AA w = 0 ⇒ B_PA w = 0`; survival vectors `(u, w)` satisfy
   `B_PP u = −B_PA w`; no nonzero pure prime vector survives; the survival cone has dimension at most
   `dim V_A`; its prime projection has dimension at most `rank B_AA`.
5. **Rank one pays one direction.** With `B_PP = 1` and `B_AA = v vᵀ`: `B_PA = b vᵀ` with `|b| ≤ 1`, and
   the prime projection of the survival cone is `ℝ b` if `|b| = 1`, `{0}` otherwise.
6. **Only the arithmetic point couples.** In the periodic class the counterterm is the Cesàro Gram
   of the modes. Ramanujan modes of order `≥ 2` have mean zero, so they are Cesàro orthogonal to the
   archimedean constant mode; the only torsion mode that couples is `c_1 = 1`, the arithmetic point.

### C. Covariance and its price

7. **Covariance forces a scalar.** A diagonal `h` with `h(tn) = h(n)` for all `t, n` is constant.
   Covariant renormalized prime forms are `−P + h`, and a scalar counterterm has survival cone
   `{0}`: covariance and survival exclude each other for diagonal counterterms.
8. **The covariant counterterm is the anomaly.** `log N − C ≤ κ_cov(N) ≤ log N + C`: the Schur test
   with weights `n^{−1/2}` reads `log(N/n) + O(1)` up the tower and exactly `log n` down it; the pole
   vector attains the bound.
9. **The anomaly costs half a logarithm.** The torsion pairing dominates `P` entrywise
   (`φ(mt) ≤ t φ(m)`) and adds the self-intersection `c(n) ≈ log n`; on the pole vector this gives
   `κ_tor(N) ≥ (3/2) log N − C`. Removing the self-intersection — Weil's prime sum has no diagonal —
   is exactly the anomaly cancellation, and it lowers the counterterm by at least `½ log N`.

### D. The horizon

10. **Polar divergence.** `Σ_{m ≤ M, n ≤ M'} P(m, n)/√(mn) = log M log M' + O(1 + log M')`, by
    Mertens' first theorem and `Σ_{m ≤ M} log m/m = ½ log² M + O(1)`. Bilinearity gives the rank-one
    divergence on every step-profile space.
11. **Orbital divergence.** On sublattice pole vectors the divergent Gram is `log² N/lcm(d, d')`,
    the counterterm of the Abel energy of the full torsion groups `μ_d, μ_{d'}` (AES ES13) divided by
    `dd'`: the sublattice `dℤ` and its annihilator `μ_d` carry the same divergence.
12. **Characters survive.** Profiles twisted by a non-principal character have no divergence; the
    finite part is the logarithmic derivative of `L(s, χ)` at `s = 1`.

### E. Stability

13. **Matched divergences.** The archimedean self-energy of an atom at the atomic spacing and the
    covariant counterterm are both `log N + O(1)`; at the horizon both places have polar rank-one
    divergences. Weil's sign on atoms is a statement about the finite parts.

---

## 5. Pillar theorems

| Pillar | Statement | Module |
|---|---|---|
| **RP1 Coupled survival** | partner-kernel inclusion; survival equations; no pure prime survival; `dim ≤ dim V_A`; prime projection `≤ rank B_AA`; rank one pays one matched direction | `TheCoupledSurvivalLaw` |
| **RP2 Only the arithmetic point couples** | Ramanujan modes Cesàro orthogonal to the archimedean mode; coupled periodic survival is per-order | `OnlyTheArithmeticPointCouples` |
| **RP3 Covariant counterterm** | covariance ⇒ scalar; `log N − C ≤ κ_cov(N) ≤ log N + C` | `TheCovariantCountertermIsTheAnomaly` |
| **RP4 Cost of the anomaly** | `κ_tor(N) ≥ (3/2) log N − C`; `κ_tor − κ_cov ≥ ½ log N − C` | `TheAnomalyCostsHalfALogarithm` |
| **RP5 Horizon polarity** | `P = ℓ² + O(log N)` on step profiles; rank-one polar counterterm | `TheHorizonCountertermIsPolar` |
| **RP6 Horizon–radius duality** | sublattice divergences `= 1/lcm`; equal to the normalized Abel counterterm of `μ_d` | `TheSublatticeDivergenceIsTheTorsionCounterterm` |
| **RP7 Character survival** | twisted profiles have bounded prime form | `TheCharactersSurviveTheHorizon` |
| **RP8 Hodge index with archimedean adjunction** | the sharpened stability statement and its relations to RH | `TheHodgeIndexWithArchimedeanAdjunction` |

---

## 6. Questions the programme must answer

The twelve questions of the report (§4.4), in RAPT's terms.

1. **What is the admissible metric of the characteristic circle?** Under the Abel radius no
   coupling with a principal torsion block has bounded counterterm rank (RP1), and the archimedean
   place pays only the arithmetic point (RP2). Under the horizon the prime divergence is polar on
   uniform profiles and orbital on arithmetic ones (RP5, RP6). The admissible regulator is the
   horizon.
2. **Does the anomaly cancel?** Cancellation means removing the self-intersection, which Weil's
   prime sum does; covariance then forces a scalar counterterm (RP3), and the cancellation saves at
   least `½ log N` (RP4).
3. **What bounds the field?** RH-strength (AES ES7). RAPT's contribution is the renormalization
   form: the field is the residue of the degree-renormalized square, and a bound must be a
   statement about a finite part, not about a counterterm.
4. **What bounds the moment of inertia?** Uniform bounds are strips (AES ES6); RAPT locates `M_f` as
   the second-order Hecke variation of the collided form and asks for a matched counterterm for it.
5. **What is the Frobenius at infinity?** On the circle conjugation is the power map of degree `−1`
   (AES); on the horizon it acts trivially on uniform profiles and by `χ ↦ χ̄` on the character cone.
6. **What is the arithmetic point?** The unique order coupling to the archimedean germ (RP2) and the
   carrier of the polar divergence at the horizon (RP5).
7. **How does `σ_γ` localize beyond the conductor?** Owned by APol/CDG; RAPT supplies the
   counterterm bookkeeping for twisted profiles.
8. **What is the gauge charge of a positive form?** Counterterms of the prime form are gauge
   blind (the spectrum is gauge invariant, AIT); the charge sits in the finite parts and the pole.
9. **How does a quantized statistic reach every window?** Owned by AES.
10. **Is the coupled class bounded at the centre?** Owned by BGG.
11. **What selects the fibre?** Divergences are soft; selection must come from finite parts.
12. **What are the escape states at infinite height?** Owned by AES/BGG.

---

## 7. Traps

| Trap | Truth |
|---|---|
| The torsion counterterm is the identity, so the prime place has no survival | That is the Abel radius; at the horizon the divergence is polar on uniform profiles |
| Coupling with the archimedean place lowers the torsion counterterm rank | The prime block keeps its rank; the partner pays at most its own rank |
| A better diagonal makes the renormalized form both covariant and positive | Covariance forces a scalar, and a scalar counterterm has no survival |
| The anomaly is a nuisance to be removed | Its potential is the self-intersection; removing it is Weil's covariance and saves `½ log N` |
| `κ ≍ log N` is a soft bound | The covariant constant is exactly one, matching the archimedean self-energy at the atomic spacing |
| Rank-one at the horizon means one direction overall | Rank one on uniform profiles; each sublattice adds its torsion orbit |
| A matched counterterm proves the sign | It removes the divergence; the sign is in the finite part |

---

## 8. Tools

**Imported.** Survival law, germs, Ramanujan relations (RBG); orbit intersections, the different,
the cocycle, the spacing regulator, Gauss's digamma duality (AIT); torsion pairing, atomic Weil
form, Abel energies of `μ_A` (AES); Mertens' first theorem (RHTower).

**Built here.** Coupled counterterms and partner-rank bounds; covariance of diagonals; sharp
Schur bounds for the atomic prime form; pole vectors, the polar functional and step profiles;
harmonic and logarithmic sums `Σ log m/m`; sublattice divergences.

**To build.** Mertens' theorem for characters (for RP7); archimedean self-energies of atoms at the
atomic spacing with constant one; the finite part of the horizon renormalization.

---

## 9. Open research topics

1. **The finite part at the horizon.** On polar-neutral uniform profiles the prime form is bounded;
   with the prime number theorem its limit is expected to be `−2γ`, the Laurent constant of
   `ζ′/ζ` at `1`, counted in both directions. What is the finite part on arithmetic profiles?
2. **The exact torsion constant.** The continuum model predicts `κ_tor(N) ∼ (e/(e − 1)) log N`; the
   Schur test fails on highly composite orders. Decide the constant.
3. **Hodge index with archimedean adjunction at the horizon.** State and test positivity of
   `arch − P + pole` on polar-neutral profiles of fixed shape as `N → ∞`.
4. **Twisted horizons.** Mertens for characters, the character survival cone and the finite parts
   `−L′/L(1, χ)`; the Frobenius at infinity as `χ ↦ χ̄`.
5. **Gauge margins in finite parts.** Where a sign twin's finite part differs from `ζ`'s.

---

## 10. Success criteria and contribution standards

RAPT succeeds when every question of §6 has an answer of the form theorem, sharp equivalence, or
sharp no-go with its positive survivor, and when the central conjecture of the report has been
replaced by a statement in which every divergence is computed and only a finite part is open.

A contribution is an unconditional Lean theorem about an object of §3. It names its **regulator**,
its **counterterm** with rank and survival cone, its **anomaly**, and the **place** that pays; it
separates identities and divergences (computed) from signs (open); it states what it gives on the
battery (sign twins, the golden datum, curves over `𝔽_q`); and every no-go records its positive
survivor.

Principles: the rank of a counterterm belongs to the regulator; covariance forces scalars; the
divergence sits on the torsion orbits; matched divergences leave the sign in the finite part;
identities first, sign last; a reformulation is not a reduction.
