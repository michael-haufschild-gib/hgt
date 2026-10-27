# Renormalized Biarithmetic Geometry (RBG)

**One question.** Over `𝔽_q`, Weil's proof of the Riemann hypothesis for a curve uses one pairing on
`C × C` that is at once *positive* (Hodge index, ample `Θ`), *Frobenius-equivariant* (the graph of
Frobenius is a correspondence), *pinned to the arithmetic point* (Frobenius-flat derivatives see the
actual `𝔽_{q^n}`-points) and *finite on the diagonal* (`Δ·Δ = 2 − 2g`). Over `ℤ` the corpus has
proved that these four properties live on four different objects that do not coincide. Which
mechanism glues them back — which renormalization of the diagonal keeps positivity through the
scale limit, which coupling of `+1` and `×p` pins the arithmetic point, and which local geometry
replaces the global extremum that Weil never needed?

RBG is the geometry of the **renormalized coupled triple**

```
( positive 2D trace / torsion orbit ,  1D scale boundary ,  continuum log-cell successor connection )
```

and of the divergences that separate its components. Its organizing sentence:

> *Over `ℤ`, positivity and scale equivariance separate only at divergent self-energies and
> rank-one polar residues, and multiplicative data see the arithmetic point only through the
> successor. A theorem of the field must cancel the divergence before it projects a sign, and must
> carry `(+1, ×p)` holonomy before it claims selectivity.*

Namespace `GaloisForLFunctions.RenormalizedBiarithmeticGeometry`; umbrella
`RenormalizedBiarithmeticGeometry.lean`. Everything is unconditional; RH and its partial forms
appear only inside equivalences.

---

## 1. Place in the research

The corpus routes (critical arithmetic cancellation, complete signed positivity, faithful
realization) all end at one question: what forces the functional-equation reflection `ρ ↦ 1 − ρ` and
complex conjugation `ρ ↦ ρ̄` to agree on every zero, `δ_ρ = Re ρ − ½ = 0`. The fifteen exhaustion
laws of the walls ledger are projections of a single **fission** of Weil's pairing:

| Weil over `𝔽_q` | Over `ℤ` (owning programme) | The gap |
|---|---|---|
| positivity and equivariance in one form | collided form `D` (positive, Hecke-invariant iff RH) vs reflection form `W` (Hecke-invariant, positive iff RH); `Re W = D − Δ` (APol, CDG) | the symmetric Hecke defect `E_f(L) = D(T_L f) + D(T_{−L} f) − 2D(f)` |
| finite self-intersection `2 − 2g` | positive torsion germs `T_r` (AET) and archimedean crossing forms (BGG) become scale-equivariant only after a divergent counterterm | the counterterm `−log(1 − r)·I`, the rank-one polar square |
| Frobenius localizes and commutes | local trichotomy: boosts (Hecke), unipotent (successor), elliptic `σ_γ` (APol, ACP) | conductor horizon vs forcing threshold (CDG) |
| pinned arithmetic base | multiplicative forms are blind on the gauge torus `Ω_𝒫` (BGG), global `Aff(ℚ)` states split on the Kakutani wall (APD) | `(+1, ×p)` coupling survives only on finite horizons, cells and escape limits |

RBG takes these as its starting theorems and studies the objects in which the pieces are coupled.

| Programme | What RBG takes | What RBG adds |
|---|---|---|
| [ConjugateDiagonalGeometry](../ConjugateDiagonalGeometry/README.md), [ArithmeticPolarization](../ArithmeticPolarization/README.md) | `D`, `W`, `Δ`, `E_f(L)`, depth kernel, two-scale rigidity, finite-theta readings, RH ⇔ Hecke invariance of `D` | dyadic amplification of the Hecke defect with fixed loss `D(f)`; effective depth; growth-rate characterisation of RH |
| [ArithmeticEffectivityTheory](../ArithmeticEffectivityTheory/README.md) | torsion orbits, `I(m, n)`, the Abel energy `T_r`, Weil's prime kernel as a renormalized torsion energy | the survival law: what positivity a counterterm leaves; the torsion counterterm is full rank and its renormalized limit is indefinite |
| [BiarithmeticGaugeGeometry](../BiarithmeticGaugeGeometry/README.md) | gauge torus, successor connection, polar-neutral collapse, log-cells `I_n`, Euclidean remainders, chiral deformations, central ceilings | log-cells fix the gauge; the archimedean germ has a rank-one counterterm; chirality as triviality of units |
| [ArithmeticCorrespondencePositivity](../ArithmeticCorrespondencePositivity/README.md) | quadratic terminals, outward rays, the transverse field, height-coupled systems | the duality between terminal cones and critical discs; the Carathéodory region of `ξ′/ξ` |
| [ArithmeticPositiveDuality](../ArithmeticPositiveDuality/README.md) | the Kakutani wall, atomic spectra are successor-blind | the finite-horizon side of the interior–boundary duality |
| [SelectivePositivityAndThresholdLaws](../SelectivePositivityAndThresholdLaws/README.md) | the selectivity battery on `[−181/500, 181/500]`, Möbius escaped pairings, parity lobes | calibration targets for every RBG invariant |
| [ArithmeticCastelnuovoSeveri](../ArithmeticCastelnuovoSeveri/README.md), [ArithmeticOrientationGeometry](../ArithmeticOrientationGeometry/README.md) | scaling surface, Hodge index, short-cycle reduction, orbit rates, `𝔽_q` calibration | the renormalized reading of adjunction `Δ² = 2 − 2g` |
| [ArithmeticElectrostatics](../ArithmeticElectrostatics/README.md) | the potential `log |ξ|`, field, torsion self-energies and counterterm rates | the abstract survival law under which those counterterms are compared |
| [SignedSuccessorArithmetic](../SignedSuccessorArithmetic/README.md), [ArithmeticCorrelationGeometry](../ArithmeticCorrelationGeometry/README.md) | successor sign calculus, one-third floor, stabilizer decompositions | gauge charge of a coupling |

RBG does not re-prove what these programmes own; it imports them and proves the laws that couple
them.

---

## 2. Why

**One pairing, four properties.** On `C × C` the intersection pairing is positive by Hodge index, the
Frobenius graph is a correspondence (equivariance), Lefschetz counts actual points (arithmetic
pinning), and the diagonal has finite self-intersection (non-scaling base). Every proof of
Hasse–Weil uses all four simultaneously.

**Over `ℤ` each name of the field is forced by a theorem.**

* *Biarithmetic.* Purely multiplicative data determine a source only up to its orbit under the
  prime gauge torus `Ω_𝒫 = ∏_p S¹`; at the real sign gauge `−1` they cannot tell `ζ` from Liouville's
  `ζ(2s)/ζ(s)`, which has poles on the critical line (BGG `realSign_latticeForm_eq`). The successor
  `+1` pins the Euler point (BGG `succConn_flat_iff_primes_eq_one`), but on global `Aff(ℚ)` states
  `+1` and `×p` decouple (APD, the Kakutani wall). The arithmetic point lives in the coupling of
  two semigroups, on finite horizons.
* *Renormalized.* The positive torsion energy `T_r` (`r < 1`) and the archimedean crossing form are
  positive; their scale-equivariant limits (Weil's prime kernel, the archimedean Weil kernel) are
  reached only after subtracting a divergence: `−log(1 − r)` times the identity, respectively a
  rank-one polar square (AET `weilPrimeKernel_renormalized_torsion_energy`, BGG
  `fullArchCrossingForm_eq_polar_sq_sub_levy`). Positivity lives before the limit, equivariance
  after it.
* *Geometry.* Sign, depth and multiplicity of zeros are not extracted by norm inequalities on one
  vertical line; they are read by intersection forms, connections and their holonomy, quadratic
  cones and deformation cones.

**Why existing disciplines do not supply the gluing.** Analytic number theory works with unsigned
norms on vertical lines and stalls at the square-root threshold (SRT, SPTL). Arakelov geometry has
no surface: `Spec ℤ ×_{𝔽_1} Spec ℤ` is not available, the base theta count is linear and does not
extend (AET `TheBaseDoesNotExtend`). Operator algebras on `Aff(ℚ)` meet the Kakutani wall, and
Meyer's origin space makes every continuous class invariant constant (ACS). Bochner–Weil and
Pólya–Schur positivity are blind to interior zeros and chirally soft (MPG, BGG).

**What the field is for.** RBG isolates, for each wall, the coupled object on which the wall is not
an obstruction, and proves what that object can and cannot carry. The basic discovery is that the
two divergences of the fission are of different rank: the prime-side (torsion) counterterm is the
identity, which leaves no positivity in the limit, while the archimedean counterterm is rank one,
which leaves positivity on a hyperplane. A renormalization that keeps the prime side positive must
therefore lower the rank of its counterterm by coupling it to a continuum twin — this is the
precise content of "matched self-energy".

---

## 3. Objects and language

### 3.1 Primitive objects

| Object | Definition | Owner / Lean |
|---|---|---|
| Split-polarized scaling space | test space with collided trace `D ≥ 0`, reflection trace `W`, defect `Δ = D − Re W ≥ 0`, translations `T_L`, Hecke defect `E_f(L)` | CDG `heckeDefect`, `depthKernel`, APol `collidedForm` |
| Regularized family and counterterm | forms `Q_r = A_r + s_r B` with `s_r → ∞`, `A_r → A`; the counterterm `B`, its survival cone `{x : B(x, x) = 0}` | RBG `TheRenormalizationSurvivalLaw` |
| Renormalized torsion germ | `T_r(m, n) = Σ_{ζ∈O_m, η∈O_n} −log|1 − rζη̄|` twisted by `gcd`; counterterm `I` | AET `twistedEnergy`; RBG survival analysis |
| Lattice germ (archimedean) | `G_r(z) = Σ_k r^k/(k + z)`, Hankel form `Σ c_i c_j G_r(x_i + x_j)`; counterterm `𝟙𝟙ᵀ` | RBG `TheArchimedeanGermSurvivesOnItsPolarHyperplane` |
| Polar-neutral log-cell complex | cells `I_n = [log n, log(n+1))`, polar amplitude `s(n) = (n−1)/√n`, subdivision `I_a + log m = ⊔_{r<m} I_{am+r}` | BGG `logCellWidth`, `continuumCellShiftCorr` |
| Cell dilation and successor | `(M_m q)(n) = q(⌊n/m⌋)`, `(S q)(n) = q(n − 1)`; relation `M_m S = S^m M_m` | RBG `LogCellsFixTheGauge` |
| Prime-gauge bundle | `Ω_𝒫`, `χ_ω`, successor connection `A_ω(n) = χ̄_ω(n)χ_ω(n+1)` | BGG `PrimeGauge`, `succConn` |
| Gauge charge of a coupling | a coupling `(n; a, b)` is blind iff `σ(n) = σ(a)σ(b)` for every real gauge | RBG `TheGaugeChargeOfACoupling` |
| Chiral deformation monoid | multipliers whose log-derivative difference is the Laplace transform of a positive measure | BGG positive deformations; RBG chirality law |
| Terminal ascent cone | right zero `p = ½ + a + iγ_p` with empty quadratic cone `𝒦_p = {x² > a² + (y − γ_p)²}` | ACP `exists_local_outward_field_witness` |
| Critical disc | `D_ρ = {s : |s − (½ + iγ_ρ)| < |δ_ρ|}`, the set where the pair `{ρ, 1 − ρ̄}` pulls `Re ξ′/ξ` negative | RBG `CriticalDiscsAndTerminalCones` |
| Effective depth | `θ_f(L)` with `E_f(L) = D(f)(2cosh θ − 2)` | RBG `TheDyadicAmplificationOfTheHeckeDefect` |

### 3.2 Twelve distinctions

Conflating any of these is a type error in RBG.

| Distinction | Consequence |
|---|---|
| Collided positivity `D` / reflected equivariance `W` | `ρ ↔ ρ̄` versus `ρ ↔ 1 − ρ̄`; each property holds without the other |
| Even / odd collision | even couplings are blind to `H¹` determinant signs; odd (exterior) counts see the complex quartet |
| Inserted pole charge / intrinsic oscillatory charge | pole order `κ` under deformation versus zero-sum oscillation at `κ = 1` |
| Hyperbolic boost / elliptic point reflection / unipotent perturbation | invariant positive cones of boosts are isotropic; only `σ_γ` localizes; `+1` is a bounded Hardy perturbation |
| Gauge-blind / holonomy-charged | blind couplings have square-class support; charged observables need successor, cells or boundaries |
| Atomic / continuous dilation spectrum | atomic spectra blind every successor; continuous spectra see it |
| Soft / fibre-selective polarization | fibre-constant theta metrics versus `thetaBoxH0/H1` |
| Outward / inward surgery | outward critical splitting is positive and irreversible; inward collapse is not positive |
| Continuous `Θ(σ⁻³)` / discrete `O(2^{−σ})` tails | Laplace deformations leave the Dirichlet lattice |
| Integer rank / real log-torsion volume | `dim ∈ ℕ` is reweighting-blind; `ψ(N) = log|ℤ/lcm(1..N)ℤ|` is not |
| Pointwise / averaged or terminal-cone bound | pointwise parameter bounds fail even under RH |
| Scalar counterterm / low-rank counterterm | a scalar counterterm leaves no positivity; a rank-`k` counterterm leaves it on codimension `k` |

### 3.3 Words

*Regularized family*: forms `Q_r` indexed by a regulator. *Counterterm*: the divergent part `s_r B`.
*Survival cone*: the null cone of the counterterm. *Matched pair*: two germs with the same
counterterm. *Polar-neutral*: orthogonal to the rank-one polar mode. *Gauge-fixing*: covariant only
at the Euler point `𝟏 ∈ Ω_𝒫`. *Charged*: not covariant under some real sign gauge. *Effective depth*:
the single-shell depth reproducing the Hecke defect at one scale. *Terminal*: a right zero whose
quadratic cone is empty. *Critical disc*: the disc of radius `|δ_ρ|` about the foot `½ + iγ_ρ`.

---

## 4. Mechanisms

1. **Survival of positivity through renormalization.** If `Q_r = A_r + s_r B` is positive for every
   regulator and `A_r → A`, then `A` is positive on the survival cone of `B`, whatever `s_r` does.
   Conversely (Finsler–Debreu), in finite dimension, if `B ⪰ 0` and `A` is positive definite on the
   null cone of `B`, then `A + sB` is positive definite for all large `s`. So positivity of the
   renormalized limit on the survival cone is *equivalent* to eventual `ε`-positivity of the
   regularized family. A scalar counterterm has trivial survival cone: every symmetric form is the
   renormalized limit of positive forms with scalar counterterm, so regularized positivity with a
   scalar divergence carries **no** information.
2. **Counterterm rank dichotomy.** The prime-side torsion germ has counterterm `I` (full rank), and
   its renormalized limit — Weil's prime kernel plus the log-discriminant diagonal — is indefinite.
   The archimedean lattice germ `Σ_k r^k/(k + x + y)` has counterterm `𝟙𝟙ᵀ` (rank one), and its
   renormalized limit is `−ψ(x + y) − γ`, the digamma of the archimedean local factor; by mechanism 1
   it is positive on the polar-neutral hyperplane `Σ c_i = 0`. The two places of the explicit
   formula are renormalized self-energies with the same universal divergence `−log(1 − r)` and
   counterterms of different rank.
3. **Dyadic amplification with fixed loss.** Two-scale rigidity `E(L)² ≤ D(E(2L) − 4E(L))` iterates:
   if `E_f(L) ≥ D(f)(2cosh θ − 2)` then `E_f(2^k L) ≥ D(f)(2cosh(2^k θ) − 2)` for all `k`. The loss
   `D(f)` does not depend on `k`; it is the non-scaling base invariant that replaces `2g`. A single
   upper bound at one large dyadic scale bounds the defect at all smaller scales without loss, and
   sub-doubly-exponential dyadic growth forces blindness to off-line zeros.
4. **Log-cells fix the gauge.** On lattice profiles, dilation `δ_a ↦ δ_{ma}` is covariant under every
   gauge. On cell profiles, dilation subdivides a cell into `m` consecutive integers, satisfies the
   Baumslag–Solitar relation `M_m S = S^m M_m` with the successor, and is covariant only at the
   Euler gauge. Cell forms are therefore gauge-fixing while lattice forms are gauge-blind.
5. **Gauge charge of a coupling.** A coupling of `a` and `b` through the source value at `n` is blind
   under every real sign gauge iff `nab` is a square, and under every unitary gauge iff `an = b`.
   Successor couplings are never square-class: `+1` is always charged.
6. **Critical discs and terminal cones.** The reflected pair `{ρ, 1 − ρ̄}` contributes to
   `Re ξ′/ξ(s)` with the sign of `x(x² + (y − γ_ρ)² − δ_ρ²)`, `s = ½ + x + iy`. The pair pulls
   negative exactly inside its critical disc; dually, `s` is pair-positive against `ρ` iff `ρ` lies
   outside the hyperbolic cone of `s`. The terminal cone of ACP is the dual of the union of critical
   discs, and the outward ray of a terminal lies in the Carathéodory region where every pair is
   nonnegative.
7. **Chirality as trivial units.** Positive deformations compose (positive measures add); a
   deformation whose inverse is also positive is trivial. Positivity orders deformations; it never
   acts by a group.

---

## 5. Pillar theorems

The eight laws of the field. Laws I–IV and VI–VIII are owned by the programmes named; RBG states and
proves their renormalized or quantitative forms.

| Law | Statement | Lean |
|---|---|---|
| I. Split polarization and dyadic rigidity | `Re W = D − Δ`; `E(L)² ≤ D(E(2L) − 4E(L))`; dyadic amplification with fixed loss `D`; RH ⇔ sub-doubly-exponential dyadic growth of every Hecke defect | CDG, APol; RBG `TheDyadicAmplificationOfTheHeckeDefect` |
| II. Local trichotomy | every reflection-commuting affine action is a boost, unipotent or elliptic | APol `TheEllipticLocalizers`, APD |
| III. Gauge blindness and charge | blind ⇔ square-class support; lattice forms blind, cell forms gauge-fixing | BGG; RBG `TheGaugeChargeOfACoupling`, `LogCellsFixTheGauge` |
| IV. Interior–boundary duality | `(+1, ×p)` coupling lives on finite horizons, cells and escape limits | APD; RBG `LogCellsFixTheGauge` |
| V. Self-energy survival | positivity survives a scale limit exactly on the null cone of the counterterm; torsion: full rank, nothing survives; archimedean: rank one, the polar-neutral hyperplane survives | RBG `TheRenormalizationSurvivalLaw`, `TheCountertermRankDichotomy` |
| VI. Chirality and quantization | positive deformations form a monoid with trivial units; central excess is quantized in `2ℕ` | BGG; RBG chirality law |
| VII. Surface effectivity vs base non-extension | Hodge index ⇔ Serre-dual real effectivity with quadratic growth; the base theta count does not extend | AET |
| VIII. Terminal replacement of extrema | every off-line zero ascends to a terminal with empty quadratic cone; the cone is dual to the critical discs | ACP; RBG `CriticalDiscsAndTerminalCones` |

---

## 6. Questions the programme answers

1. **Split polarization.** What bounds `E_f(L)` without a fibred product? — The Hecke defect is
   self-amplifying with fixed loss `D(f)`: an upper bound at one large dyadic scale transfers
   losslessly to all smaller scales, and RH is equivalent to sub-doubly-exponential dyadic growth.
   The remaining input is a source-side bound at one large scale (CDG finite-theta readings compute
   `E_f(L)` for `|L| ≤ 2 log(n+1)` from integer prefixes of length `n`).
2. **Matched self-energy.** How does one cancel `−log(1 − r)` inside the positive cone? — Exactly on
   the survival cone of the counterterm. The torsion counterterm is the identity, so no
   positivity survives and the renormalized limit is indefinite; the archimedean counterterm is
   rank one and leaves the digamma Hankel form positive on the polar-neutral hyperplane. A matched
   twin must lower the rank of the joint counterterm.
3. **Finite-horizon holonomy.** How much `(+1, ×p)` curvature survives? — On lattice profiles none;
   on log-cell profiles the dilation is covariant only at the Euler point, so cell forms are
   gauge-fixing; every successor coupling is charged.
4. **Chiral moduli.** — Positive deformations form a monoid with trivial units, ordered by central
   order (BGG ceilings and quantization).
5. **Zero-cone potential.** — The terminal cone is the dual of the critical discs; the outward ray
   lies in the Carathéodory region of `ξ′/ξ`.
6. **Fibre-selective real effectivity.** — Owned by AET; RBG's contribution is the survival
   criterion for regularized effectivity functionals.
7. **Fixed-loss amplification.** — The collided mass `D(f)` is the non-scaling invariant; dyadic
   Hecke amplification has loss exactly `D(f)`.

---

## 7. Traps

| Trap | Truth |
|---|---|
| Positivity of `T_r` for `r < 1` bounds Weil's prime form | The counterterm is the identity; every symmetric form is a renormalized limit of positive forms with scalar counterterm |
| Subtracting `−log(1 − r) I` from a positive germ leaves something positive | The renormalized torsion limit is indefinite already on `{1, p}` |
| Matched cancellation is free | It transfers positivity only on the survival cone of the joint counterterm |
| A cleverer multiplicative weight separates `ζ` from Liouville | Blind couplings are exactly the square-class ones |
| Discretizing to `log n` loses nothing | Lattice dilation is blind; only cell dilation fixes the gauge |
| Two-scale rigidity is a single inequality | It iterates to every dyadic scale with fixed loss |
| Positive deformations can be undone | Units of the deformation monoid are trivial |
| The terminal ray avoids zeros by luck | It lies outside every critical disc; that is the cone condition |

---

## 8. Tools

Built in the corpus and used here: collided and reflection forms, Hecke defect and depth kernel,
finite-theta source readings (CDG, APol); torsion orbit intersections and the Abel torsion energy
(AET); gauge torus, successor connection, polar-neutral collapse, cell subdivision, chiral
deformations (BGG); terminal cones and outward rays (ACP); selectivity battery (SPTL).

Developed by RBG: the survival law for regularized families; the lattice germ and its digamma limit;
counterterm rank; dyadic amplification and effective depth; cell dilation and gauge fixing; gauge
charge of couplings; critical discs; the chirality law.

---

## 9. Open research topics

1. **Matched torsion–continuum renormalization.** A joint germ of torsion orbits and continuum cells
   whose counterterm has a nontrivial null cone containing short-cycle Lefschetz differences
   `g − T_{2^m} g`.
2. **Source-side dyadic bounds.** An upper bound for `E_f(2^k L)` at one large scale from finite
   theta prefixes; by dyadic amplification it bounds `E_f(L)` with no loss.
3. **Harmonic measure on terminal cones.** Harnack and Borel–Carathéodory estimates in the
   Carathéodory region of `ξ′/ξ` along the outward ray.
4. **Quantitative cell holonomy.** Lower bounds for the gauge charge of cell correlations at the
   Liouville gauge in terms of successor sign changes.
5. **Chiral ceilings for automorphic cofactors** and collective multi-ordinate packets.
6. **Wiener escape modules** as boundary objects of the interior–boundary duality.

---

## 10. Success criteria and contribution standards

RBG succeeds when it proves, for a coupled object, a positivity that survives the scale limit and
passes the battery below, or proves that no object of a stated class can, together with the
strongest positive survivor.

**The ten-point battery.** A candidate invariant must state its behaviour on: (1) curves over `𝔽_q`
with genus cost `2g`; (2) the golden datum `1 − 5X + 5X²`; (3) the complex quartet
`X⁴ + 68X² + 256`; (4) pole-budget-2 refunds; (5) outward splittings `W_β` and Maass cofactors;
(6) the Liouville twin `λΛ`; (7) the shifted pair `ζ(s − a)ζ(s + a)`; (8) prime-power nodes; (9)
interior zeros `ζ(s)/ζ(s + 1 − β)`; (10) trans-threshold parity (`λ > 1`).

A contribution is an unconditional Lean theorem about constructed objects. It names its
counterterm and survival cone, its gauge charge, its local type, and its scale range; it separates
identities from estimates; and every negative result records its positive survivor.
