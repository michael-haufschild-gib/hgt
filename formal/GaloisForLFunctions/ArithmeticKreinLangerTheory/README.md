# Arithmetic Krein–Langer Theory (AKL)

**From local data to a global index.**

Namespace `GaloisForLFunctions.ArithmeticKreinLangerTheory`; umbrella `ArithmeticKreinLangerTheory.lean`.

**One question.** The Weil kernel of `ζ` is a Hermitian kernel on the Hecke lattice
`Γ = ℚ_{>0} ≅ ⊕_p ℤ` assembled from local constituents: one tower `⟨p⟩ ≅ ℤ` per prime, an
archimedean factor on `ℝ_{>0}`, and the pole. RH says its negative index is zero. Over `𝔽_q` the
corresponding index is computed in two steps, both global: Castelnuovo–Severi (or Riemann–Roch)
bounds it, and Stepanov's auxiliary polynomial produces the count that brings it to zero. AKL asks
for the map in between:

> *Which local data, together with which single global law, determine the index of an arithmetic
> kernel, and what produces that law?*

AKL is the local-to-global part of Krein–Langer theory on `Γ`. Its foundation is
[HeckeKreinToeplitz](../HeckeKreinToeplitz/README.md) (HKT): kernels on groups, hyperbolic pairs, the
index formula, closedness, aliasing on one tower, the Weil kernel of `ζ` and its index laws. HKT
treats the index as an invariant of one global kernel. AKL treats it as the output of a
local-to-global map, and studies that map's four missing parts:

1. **locality**: when the restrictions to towers determine the index (a Hasse principle for the index);
2. **ceilings**: inequalities `κ ≤ F(local data, one law)`;
3. **producers**: constructions that yield the law (a one-sided square-root count) without assuming it;
4. **completion and parity**: the topology in which local-to-global limits carry the index, and the
   exact place where the twins of `Λ` enter.

Nothing in HKT is restated here. Every AKL theorem either takes local data as input or proves that a
class of local data cannot decide the index. Everything is unconditional; RH appears only inside
equivalences.

---

## 1. Place in the research

The corpus pins down what the missing input must be ([obstacles summary](../../../docs/reports/review-2910/obstacles-summary.md)):
**parity-sensitive** (it fails for the Liouville twin), **square-root precise** (it fails for
`Λ + εn^{−η}`, `η < ½`), **global** (unbounded aperture, at least two prime towers). Both of the first
two have been obtained together only over `𝔽_q`, from geometry or Frobenius. In index language the
missing input is one statement: index zero of `K_ζ` is the one-sided count
`ψ(x) − x ≤ C√x log²x` (`global_law_count`), just as over `𝔽_q` it is
`N_k ≥ q^k + 1 − Cq^{k/2}`.

AKL owns the obstacles of that summary that are statements about the passage from local to global:

| Obstacle | AKL form |
|---|---|
| I10 arithmetic Krein–Langer ceiling | a local-to-global index ceiling (§5 B) |
| I9 Stepanov over `ℤ` | a producer of one-sided counts (§5 C) |
| O3 positivity on one prime's towers | locality on one tower: what one tower can and cannot certify (§5 A) |
| F1, F6 finite index; two-prime lattice | the ceiling at finite level; the Lindelöf diagnostic |
| §2.8 items 4–5 (cross-level couplings, index at limits, locality on `ℤ²`) | completion and locality (§5 A, D) |

**Interfaces.**

| Programme | What AKL takes | What AKL adds |
|---|---|---|
| [HeckeKreinToeplitz](../HeckeKreinToeplitz/README.md) | the index `negIndex`, pair kernels `pairKernel`, the index formula (`negIndex_add_sum_pairKernel_eq`), aliasing on a cyclic subgroup (`negIndex_zpowers_eq_card_classes`), Stepanov compressions (`negIndex_compress_eq`), the global law (`global_law_count`), closedness (`negIndex_le_of_tendsto`), coalescence (`coalescence_law`) | the local-to-global map on top of these |
| [ArithmeticCastelnuovoSeveri](../ArithmeticCastelnuovoSeveri/README.md) | curve data `CurveDatum`, one-sided Lefschetz bounds and the real-node exception (`oneSided_forcing_tfae`, `zeta_riemannHypothesis_iff_oneSided_upper`), the golden datum | the one-sided law as a ceiling with local exceptions |
| [ArithmeticLorentzianGeometry](../ArithmeticLorentzianGeometry/README.md) | trickle-down = square-root count; hyperelliptic data (`hyperelliptic_weightedTrickleDown`) | the producer's two steps (auxiliary count, twist) |
| `RHTower.Stepanov` | the auxiliary-polynomial count (`stepanov_count`, `stepanov_bound`) | the identification of the step a producer over `ℤ` lacks |
| [ArithmeticCorrespondencePositivity](../ArithmeticCorrespondencePositivity/README.md) | sparse annihilators kill only critical lattice symbols | producers vs receivers |
| [SelectiveMultiscaleArithmeticPositivity](../SelectiveMultiscaleArithmeticPositivity/README.md), [ArithmeticCountingPositivity](../ArithmeticCountingPositivity/README.md) | selection, the margin `2 log 2`, precision rigidity, maximal-margin flips | the battery, sorted by which local datum excludes each member |
| [ArithmeticOrientationGeometry](../ArithmeticOrientationGeometry/README.md) | orbit correlations, Bézout-selective orientation (open) | additive structure as the level of the structure ladder at which a producer must act |
| [ArithmeticPositiveDuality](../ArithmeticPositiveDuality/README.md) | Herglotz–Bochner on `ℚ_{>0}` and on lattices | positive-definite local factors |

---

## 2. Why

**Weil over `𝔽_q` is a local-to-global index theorem.** For a curve, every datum lives on one
graded tower, the Frobenius powers `ℤ`. The trace kernel `n ↦ Σ_i β_i^n` is the pole pair minus
the closed points: a closed point of degree `d` contributes `d·q^{−|n|/2}·1[d | n]`, which is a
positive-definite kernel on `ℤ` (a character of `ℤ/d` times a Poisson kernel). So:

- every local constituent is positive definite, and enters with a minus sign;
- the global index is finite because the genus is finite (Riemann–Roch), with `κ ≤ g`;
- the index is zero because of a count: Stepanov's auxiliary polynomial gives the upper count for the
  curve and for its quadratic twist, and the twist turns the second upper count into the missing
  lower count.

The golden datum `1 − 5X + 5X²` has positive counts, positive closed-point counts and index one: local
positivity and the genus ceiling cannot by themselves give index zero.

**Over `ℤ` every step changes.** There are infinitely many towers, one per prime, meeting only at the
identity of `Γ`; an archimedean factor supported everywhere; infinite genus. HKT has shown that the
index is a robust invariant (closed under pointwise limits, carried by two primes, counted by heat
collisions, priced by energy) and that index zero is a one-sided square-root count. What it does not
have is any inequality bounding the index from the constituents. Five facts explain why the
constituents alone cannot give one:

1. *A positive part never pays a pair* (HKT): no positive majorant is an index ceiling.
2. *Locality is not automatic.* Positivity on coordinate circles is not positivity on the torus;
   whether the prime towers decide depends on the spectrum (§4.1).
3. *Local constituents have infinite index individually*, and finite sets of places have infinite
   index jointly: positivity is a property of the assembly with the archimedean factor (§4.2).
4. *Local indices are twin-invariant.* The Liouville twin acts on each tower by the unitary character
   `(−1)^n`, which keeps every tower index; selectivity must enter through a non-local constituent
   (§4.5).
5. *Finite index is Lindelöf-deep* (HKT): every finite ceiling for `ζ` proves LH.

So the local-to-global map needs one global input, and AKL's task is to say exactly which, to build
the parts of the map that are theorems, and to prove that every weaker class of input fails.

---

## 3. Objects and language

| Weil over `𝔽_q` | AKL object | Over `ℤ` |
|---|---|---|
| Frobenius tower `ℤ` | a group `G` with a family of **towers** `⟨u_t⟩` | `Γ = ℚ_{>0}`, prime towers `⟨p⟩` |
| closed point of degree `d` | **local constituent** on a tower | Euler-factor kernel `L_p(n) = log p · p^{−|n|/2}` |
| degree grading | **scale** `ℓ : G → ℝ` | `log : Γ → ℝ` |
| `β_i`, `1/β̄_i` | **spectrum**: characters `χ`, reflections `χ^† = 1/χ̄` | `u ↦ u^{ρ−½}`, `u ↦ u^{½−ρ̄}` |
| `|β| ≠ 1` | non-unitary character | right zero |
| Riemann–Roch, `κ ≤ g` | **ceiling** | open |
| `N_k ≥ q^k+1−Cq^{k/2}` | **global law** (a count) | `ψ(x)−x ≤ C√x log²x` |
| Stepanov's auxiliary polynomial | **producer** | open (I9) |
| quadratic twist | **twin** (a unitary character acting on constituents) | Liouville character `λ : Γ → {±1}` |

**Words.**

- *Tower restriction*: `k ∘ zpowersHom G u`, the kernel on the cyclic subgroup `⟨u⟩`.
- *Cyclic locality*: positivity on every cyclic subgroup implies positivity.
- *Tower locality*: positivity on infinitely many members of a fixed family of towers implies positivity.
- *Torsion aliasing*: two characters whose quotient has finite order on a finite-index subgroup;
  they agree on a whole finite-index subgroup of towers.
- *Tower-faithful spectrum*: every non-unitary member is non-unitary on all but finitely many towers,
  and two distinct members agree on only finitely many towers.
- *Logarithmic spectrum*: characters `u ↦ e^{s ℓ(u)}` of one scale `ℓ`; tower scales pairwise
  incommensurable.
- *Local constituent*: a kernel supported on one tower. *Meeting point*: the identity, the only element
  shared by two distinct towers of `Γ`.
- *Ceiling*: an inequality `κ(k) ≤ F` with `F` computed from local data and one global law.
- *Count*: a one-sided bound at square-root precision. *Producer*: a construction yielding a count
  without assuming it. *Receiver*: a statement that is equivalent to a count.
- *Twin*: a kernel obtained by twisting the constituents by a unitary character of `Γ`; the
  *Liouville twin* twists each tower by `(−1)^n`.
- *Structure ladder*: the four levels of arithmetic input — **sign** (positive local coefficients),
  **support** (an Euler product: prime data on the towers), **normalization** (pole and Gamma
  factor matched to the prime mass), **ring** (additive structure: `gcd(n, n+1) = 1`, the curve's
  equation).
- *Index-carrying topology*: one in which the index is continuous, not only lower semicontinuous.

---

## 4. Mechanisms

1. **Cyclic subgroups decide the Krein–Langer class; coordinate towers do not.** For a
   positive-definite kernel plus finitely many hyperbolic pairs on any group, the set of elements at
   which some node lies on the unit circle or two nodes coincide is a finite union of subgroups. The
   unitarity subgroups have infinite index. By Neumann's lemma (a group is not covered by finitely
   many cosets of infinite-index subgroups), every coset of the finite-index aliasing subgroup
   contains an element avoiding all infinite-index ones. At such an element the pairs regroup into
   torsion classes, and if all class weights vanished at every coset, Dedekind's independence of the
   torsion characters would force every weight to vanish. So some cyclic subgroup carries a negative
   square. On `ℤ²` the coordinate axes can still hide everything: the kernel
   `2i·sinh(v₁ log 2)·(1 − (−1)^{v₂})` is two separated hyperbolic pairs, has index `2`, and vanishes
   on both axes and on every `⟨(m, 2n)⟩`. Outside the Krein–Langer class even cyclic locality fails:
   `δ₀ − ½ Σ_{w∈{e₁,e₂,e₁+e₂}} (δ_w + δ_{−w})` is positive on every cyclic subgroup and not on `ℤ²`.
2. **Logarithmic spectra are tower-faithful.** For `χ_s(u) = e^{sℓ(u)}`, non-unitarity at one tower is
   non-unitarity at every tower with nonzero scale, and `χ_s = χ_{s'}` on two towers with
   incommensurable scales forces `s = s'`. So every pair of distinct nodes is blind on at most one
   tower, almost every tower carries the whole index, and positivity on infinitely many towers is
   positivity. This is the arithmetic property behind the two-prime law: the spectrum of the Weil
   kernel is rank one, read through a single real logarithm.
3. **The Euler factor is a Poisson kernel.** `n ↦ r^{|n|}` (`0 ≤ r < 1`) is the autocorrelation of
   `√(1−r²)·r^k 1[k ≥ 0]`, hence positive definite; the local kernel of `(1 − p^{−s})^{−1}` is
   `L_p(n) = log p · p^{−|n|/2}`, and the prime constituent of the Weil kernel on `⟨p⟩` is
   `log p·δ₀ − L_p`. Distinct towers meet only at the identity, so the constituents interact only
   through the diagonal, where the divergent sum `Σ_p log p` is renormalized by the archimedean factor.
   Without it, finitely many places give the symbol `Σ_p log p·(1 − P_{p^{−1/2}}(θ_p))`, negative near
   `θ = 0`: infinite index.
4. **One-sided laws and the real-node exception.** A one-sided bound along one tower forces the
   deepest node to be real and positive with negative weight (ACS: `oneSided_forcing_tfae`). Over `𝔽_q`
   the exception is removed by the quadratic twist, which negates every Frobenius eigenvalue; over `ℤ`
   by a second prime and the absence of real zeros
   (`zeta_riemannHypothesis_iff_oneSided_upper`). A one-sided law with finitely many subtracted
   exponentials bounds the index by their number (the finite stratum, `re_le_half_add_of_lagPoleSeries_sub_extension`).
5. **Twins act on constituents, not on the kernel.** A unitary character `ω` of `Γ` acts on the tower
   `⟨p⟩` by `n ↦ ω(p)^n`, a unitary twist; tower indices are unchanged (`negIndex_twist`). At atomic
   resolution, where the archimedean factor is a diagonal counterterm and `ω(1) = 1`, the twin of the
   whole kernel is its unitary twist, so the index ladder is twin-blind (`hermNegIndex_gaugeAtom_eq`);
   what is not twin-invariant is the pole direction and the archimedean factor off the diagonal. Over
   `𝔽_q` the analogous twist `β ↦ −β` (quadratic twist) is a symmetry of the whole kernel, and Weil's
   proof uses it.
6. **Producers give upper bounds; the twist gives the other side.** Stepanov's auxiliary polynomial
   bounds `#{x : f(x)^{(q−1)/2} = ε}` from above for each `ε = ±1`. Two facts make it work: the
   Frobenius identity `x^q = x` on the counted set (vanishing conditions cost independently of the
   set's size), and Euler's criterion (the parity character is the polynomial `a^{(q−1)/2}`). The two
   parity classes are the curve and its twist, and their counts add to `2(q + 1)`. Over `ℤ` the parity
   character `λ` has no algebraic description, and the complementary class of the primes is not a
   set to which an upper-bound producer applies.
7. **The structure ladder sorts the battery.** Sign excludes the Liouville twin and the sign flips;
   support excludes `Λ + εn^{−η}` and Davenport–Heilbronn; normalization excludes `cΛ`, `c ≠ 1`;
   only the ring level excludes over-regular Beurling systems and the golden datum, which have
   positivity, an Euler product and the right normalization. A ceiling or producer must act at the
   ring level.
8. **Index limits.** Bounded index is closed under pointwise convergence (HKT); the index drops in the
   limit only by coalescence onto the unitary dual, collision of nodes with cancelling weights, or
   vanishing weights. A topology in which these are excluded carries the index.

---

## 5. Pillar theorems

**A. Locality.**
- *Cyclic Hasse principle*: on every group, a Krein–Langer kernel positive definite on every cyclic
  subgroup is positive definite; with a pair present, some cyclic subgroup carries a negative square.
- *Separation*: without torsion aliasing some element separates all nodes, and its cyclic subgroup
  carries the whole index.
- *Coordinate failure*: an explicit Krein–Langer kernel on `ℤ²` of index `2` vanishing on both axes;
  an explicit non-Krein–Langer kernel positive on every cyclic subgroup and not on `ℤ²`.
- *Tower-faithful Hasse principle*: for a tower-faithful spectrum, all but finitely many towers carry
  the whole index; logarithmic spectra with pairwise incommensurable tower scales are tower-faithful.
  For `ζ` this is HKT's `negIndex_eq_zero_of_posDef_on_infinitely_many_towers`.

**B. Local constituents and ceilings.**
- *Poisson law*: the local Euler-factor kernel is positive definite; its twins are positive definite;
  the prime constituent is `log p·δ₀ − L_p`.
- *No finite set of places has finite index*: the kernel `(Σ_{p∈S} log p)δ₁ − Σ_{p∈S} L_p` on
  `⊕_{p∈S} ℤ` has infinite index.
- *Riemann–Roch ceiling over `𝔽_q`*: `κ(traceKernel D) ≤ g`; the count lowers it to `0`; the golden
  datum attains `1` with positive local data.
- *One-sided ceiling with exceptions*: a one-sided law with `m` subtracted exponentials bounds the
  index by `m` plus the number of real positive deepest nodes of negative weight.

**C. Producers.**
- *Twist completion over `𝔽_q`*: upper counts for a curve datum and for its quadratic twist force
  index zero; an upper count alone does not (the golden datum).
- *The parity form of the global law*: index zero is an upper count for both parity classes.

**D. Completion and parity.**
- *Index continuity*: along pointwise convergence of Krein–Langer kernels whose hyperbolic data
  converge without coalescence, collision or vanishing weights, the index is continuous.
- *Twin invariance of local indices*: every unitary twin keeps every tower index; at atomic resolution
  it keeps the global index.

---

## 6. Traps

| Trap | Truth |
|---|---|
| The prime towers always decide, because two primes do for `ζ` | Only for tower-faithful spectra; on `ℤ²` a Krein–Langer kernel of index `2` vanishes on both axes |
| Cyclic locality is a general fact about kernels | It holds for the Krein–Langer class and fails for finite-support kernels with a signed spectrum |
| Local constituents are positive | The local Euler-factor kernel is positive definite; the constituent `log p·δ₀ − L_p` is not, and finitely many places have infinite index |
| Local positivity excludes the twins | Coefficient positivity excludes the Liouville twin; kernel positivity of each constituent is twin-invariant |
| An upper count is half of the global law | It misses real positive deepest nodes (golden datum); the twist or a second prime is needed |
| A producer over `ℤ` can be modelled on the counts | Stepanov uses the equation (`x^q = x`, Euler's criterion), not the counts; Beurling systems and the golden datum share every count-level property |
| An index ceiling can be local | Every finite ceiling for `ζ` proves LH; a ceiling needs one global input |
| Limits keep the index | Only lower semicontinuity holds; coalescence, collision and vanishing weights lower it |
| A new equivalence is progress | AKL contributions take local data as input and bound, produce or exclude |

---

## 7. Questions the programme answers

1. **What replaces `x^q = x` over `ℤ`?** In Stepanov's argument `x^q = x` makes the vanishing
   conditions on the counted set independent of its size, and Euler's criterion makes the parity
   character a polynomial; the count for the curve and its twist then gives the two sides.
   A replacement over `ℤ` must supply both: an identity on the primes that makes vanishing conditions
   cheap, and an algebraic description of a parity class.
2. **What is the positive form of the parity barrier?** Twins act on constituents by unitary twists,
   so every local index is twin-invariant and every law assembled from local indices is twin-blind;
   selectivity lives in the pole direction and the archimedean factor. The margin `2 log 2` is the
   width of the window where the pole carries the first square (HKT).
3. **Why does finite index imply LH?** Finite index is finite off-line support, so the off-line zero
   count in every unit height window is eventually zero, which is Backlund's form of LH. A direct
   argument from the kernel would bound `ζ` on the line by the positive part of the kernel; open.
4. **In which completion does the Weil kernel carry its index to the limit?** Pointwise kernel
   convergence closes `{κ ≤ m}`; the index is continuous exactly along non-coalescent convergence of
   the hyperbolic data.
5. **Why do two primes suffice, and which arithmetic property makes locality hold?** The spectrum is
   logarithmic: one real logarithm reads every character, so unitarity is tower-independent and two
   incommensurable scales separate any two characters. Without this, locality fails on `ℤ²` inside the
   Krein–Langer class.
6. **What arithmetic quantity governs the near-axis collisions of the heat flow?** Collision mass is
   `2(κ + E)` on the finite stratum (HKT); the near-axis part is the multiplicity excess and the
   coalescence of pairs onto the line, which is exactly the index drop of §4.8. Open: a prime-side
   expression.

---

## 8. Tools

| Tool | Purpose | Test |
|---|---|---|
| Cyclic and tower Hasse principles | decide the index from restrictions | coordinate failure on `ℤ²`; recovers the two-prime law |
| Local Euler-factor kernels | constituents as positive-definite kernels on towers | Poisson law; infinite index of finite place sets |
| Local-to-global index ceiling | bound `κ` from constituents and one law | `κ ≤ g` and `0` over `𝔽_q`; fails for the golden datum without the count; implies LH whenever finite for `ζ` |
| Arithmetic compressor (Stepanov over `ℤ`) | produce a one-sided count | reproduces hyperelliptic RH; fails for Liouville; first rung: beat the sieve constant `2` |
| Twist completion | turn upper counts into the global law | over `𝔽_q`: quadratic twist; over `ℤ`: second prime |
| Index-carrying completion | continuity of the index along limits | agrees with pointwise limits; detects coalescence |
| Structure ladder | sort inputs by arithmetic level | every battery member excluded at a stated level |

---

## 9. Open research topics

1. **Ceiling over `ℤ` at finite level**: a bound on the index of height or integer truncations from
   prime-side data that is uniform in the truncation (equivalent to finite support; LH-deep).
2. **Producer over `ℤ`**: an identity on primes playing `x^q = x`; an algebraic or analytic
   description of a parity class; the first rung, beating the sieve's parity constant `2` on
   intervals `x^ε`.
3. **Ring-level inputs**: Bézout relations as local-to-global data that fail on Beurling systems.
4. **Cyclic locality for infinite spectra**: positivity on every cyclic subgroup for kernels with
   infinitely many pairs; for one test function on `Γ`.
5. **Index continuity in the arithmetic topology**: which receivers converge non-coalescently.
6. **A direct Lindelöf bridge** from finite index.
7. **Hecke and Dedekind kernels**: tower faithfulness for spectra with finite-order twists, where
   torsion aliasing is generic.

---

## 10. Success criteria and what a contribution is

**Success.** AKL succeeds when the passage from local data to the index of `K_ζ` is a theorem with one
named global input, and that input is produced: index theory first (locality, ceilings), then a count,
then positivity as a consequence. Its first evidence is any of: a ceiling for the index of a
truncated Weil kernel from prime-side data, failing for the golden datum; an auxiliary construction
over `ℤ` beating the sieve constant `2`; a selective local-to-global law that fails visibly for the
Liouville twin.

**Criteria** (from the field assessment).

1. **Independence.** Built from arithmetic data, never from zero-indexed objects.
2. **Fidelity.** All mixed entries, Gamma, both poles and multiplicities; prime-only, collided and complete forms kept apart.
3. **Battery.** Every sufficient hypothesis fails for: Liouville; `cΛ` and quadratic mixtures; single-prime flips with the maximal margin; cofinite flips; `Λ + εn^{−η}`; the golden curve; over-regular Beurling systems; Davenport–Heilbronn functions.
4. **Parity and precision.** An input that `λ`-twisting and `n^{−η}` perturbation both change.
5. **Exhaustion.** Uniformity exactly in the growing parameters, in an index-carrying topology.
6. **Calibration.** Reproduce Weil over `𝔽_q` by counting, the `2/3` census, the `K_⋆` regime and the sharp gap.
7. **A new inequality.** A paid sign, index ceiling, count or energy bound, not another equivalence.
8. **Formal closure.** Unconditional Lean statements.

**A contribution** is an unconditional theorem about kernels on groups with a stated family of
towers. It names its local data and its global input, says what it gives over `𝔽_q` and on the golden
datum, names the level of the structure ladder at which it acts, and records the positive survivor of
every no-go.

**Principles.** Local data are twin-invariant at the index level. Locality is a property of the
spectrum. A positive part never pays a pair, and no finite set of places pays the diagonal. Producers
give upper bounds; the global law needs a twist. Finite index is Lindelöf-deep. Index, then count,
then sign.
