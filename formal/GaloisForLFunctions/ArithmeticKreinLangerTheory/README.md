# Arithmetic Krein–Langer Theory (AKL)

**From local data to a global index.**

Namespace `GaloisForLFunctions.ArithmeticKreinLangerTheory`; umbrella `ArithmeticKreinLangerTheory.lean`.

**One question.** The Weil kernel of `ζ` is a Hermitian kernel on the Hecke lattice
`Γ = ℚ_{>0} ≅ ⊕_p ℤ`, assembled from local constituents: one per prime, on the tower `⟨p⟩ ≅ ℤ`, an
archimedean factor on `ℝ_{>0}`, and the pole. RH says its negative index is zero. Over `𝔽_q` the
corresponding index is computed in two steps: Riemann–Roch bounds it by the genus, and a count
(Stepanov's auxiliary polynomial) brings it to zero. AKL asks for the map in between:

> *Which local data, together with which single global law, determine the index of an arithmetic
> kernel, and what produces that law?*

AKL is the local-to-global part of Krein–Langer theory on groups with a family of towers. Its
foundation is [HeckeKreinToeplitz](../HeckeKreinToeplitz/README.md) (HKT): kernels on groups,
hyperbolic pairs, the index formula, closedness, the aliasing law on one cyclic subgroup, and the Weil
kernel of `ζ` with its index laws. HKT treats the index as an invariant of one global kernel. AKL
treats it as the output of a local-to-global map, and studies the parts of that map that HKT leaves
open:

1. **locality**: when restrictions to towers determine the index (Hasse principles for the index);
2. **local constituents and ceilings**: what assemblies of tower-supported data can carry, and
   inequalities `κ ≤ F(local data, one law)`;
3. **producers and parity**: the form of the global law a construction would have to produce, and
   where the parity twins enter;
4. **completion**: the topology in which local-to-global limits carry the index.

Nothing in HKT is restated here. Every AKL theorem takes local data (towers, constituents, counts) as
input, or proves that a class of local data cannot decide the index. Everything is unconditional; RH
appears only inside equivalences.

---

## 1. Place in the research

The corpus pins down what the missing input must be ([obstacles summary](../../../docs/reports/review-2910/obstacles-summary.md)):
**parity-sensitive** (it fails for the Liouville twin), **square-root precise** (it fails for
`Λ + εn^{−η}`, `η < ½`), and **global** (unbounded aperture, at least two prime towers). Both of the
first two have been obtained together only over `𝔽_q`, from geometry or Frobenius. In index language
the missing input is one statement: index zero of `K_ζ` is the one-sided count
`ψ(x) − x ≤ C√x log²x` (`global_law_count`), as over `𝔽_q` it is `N_k ≥ q^k + 1 − Cq^{k/2}`.

AKL owns the obstacles of that summary that concern the passage from local to global:

| Obstacle | AKL form | Status |
|---|---|---|
| §2.8 *locality fails on `ℤ²`; why do two primes suffice* | Hasse principles for the index | answered (§5 A) |
| I10 arithmetic Krein–Langer ceiling | ceilings from local data and one law | structure proved (§5 B); finite ceiling for `ζ` is LH-deep |
| I9 Stepanov over `ℤ` | the law a producer must produce, and its parity form | target fixed (§5 C); producer open |
| §2.8 *in which completion does the index pass to limits* | continuity off the discriminant | answered (§5 D) |
| F1, F3, F6 finite stratum | the index as a number of exceptional waves | proved (§5 B) |

**Interfaces.**

| Programme | What AKL takes | What AKL adds |
|---|---|---|
| [HeckeKreinToeplitz](../HeckeKreinToeplitz/README.md) | `negIndex`, `pairKernel`, the index formula `negIndex_add_sum_pairKernel_eq`, the aliasing law `negIndex_zpowers_eq_card_classes`, orthogonal translates `card_le_negIndex_of_orthogonal_translates`, closedness `negIndex_le_of_tendsto`, coalescence `coalescence_law`, the global law `global_law_count`, the arithmetic tower law `negIndex_eq_zero_of_posDef_on_infinitely_many_towers` | Hasse principles on every group, the zero-or-infinity law, the wave formula, continuity off the discriminant |
| [ArithmeticCastelnuovoSeveri](../ArithmeticCastelnuovoSeveri/README.md) | `CurveDatum`, one-sided Lefschetz bounds and the real-node exception (`oneSided_forcing_tfae`, `zeta_riemannHypothesis_iff_oneSided_upper`), the golden datum | the Riemann–Roch ceiling, the twist tower |
| `RHTower` | Stepanov's count (`stepanov_count`), the Liouville laws (`riemannHypothesis_iff_forall_liouvilleSummatory_le`, `riemannHypothesis_iff_forall_liouvilleExpSum_lower`), real zeros of `ζ` | the parity classes as the targets of a producer |
| [ArithmeticLorentzianGeometry](../ArithmeticLorentzianGeometry/README.md) | trickle-down = square-root count, hyperelliptic data | the role of the quadratic twist |
| [ArithmeticCorrespondencePositivity](../ArithmeticCorrespondencePositivity/README.md) | sparse annihilators kill only critical lattice symbols | producers versus receivers |
| [SelectiveMultiscaleArithmeticPositivity](../SelectiveMultiscaleArithmeticPositivity/README.md), [ArithmeticCountingPositivity](../ArithmeticCountingPositivity/README.md) | selection, the margin `2 log 2`, precision rigidity, the flips | the battery, sorted by the level of arithmetic structure that excludes each member |
| [ArithmeticOrientationGeometry](../ArithmeticOrientationGeometry/README.md) | Bézout-selective orientation (open) | additive structure as the level at which a producer must act |
| [ArithmeticPositiveDuality](../ArithmeticPositiveDuality/README.md) | Herglotz–Bochner on `ℚ_{>0}` | positive-definite local factors |

---

## 2. Why

**Weil over `𝔽_q` is a local-to-global index theorem.** All data of a curve live on one graded tower,
the Frobenius powers `ℤ`. The global index is finite because the genus is (Riemann–Roch), with
`κ ≤ g`, and the golden datum attains this ceiling with positive counts. It is zero because of a count.
Stepanov's auxiliary polynomial produces **upper** counts: `#{x : f(x)^{(q−1)/2} = ε} ≤ q/2 + O(√q)`
for `ε = ±1`, using the Frobenius identity `x^q = x` on the counted set and Euler's criterion (the
parity character is the polynomial `a^{(q−1)/2}`). The two parity classes are a curve and its
quadratic twist; the twist turns one class's upper count into the other's lower count, and the twists
of the `2`-power base changes deliver the whole global law.

**Over `ℤ` every ingredient changes.** There are infinitely many towers, one per prime, meeting only
at the identity; an archimedean factor supported everywhere; infinite genus. HKT shows the index is a
robust invariant (closed under limits, carried by two primes, counted by heat collisions, priced by
energy) and that index zero is a one-sided square-root count. AKL establishes why the constituents
alone cannot give it:

1. *Locality is a property of the spectrum.* Cyclic subgroups decide every Krein–Langer kernel, but
   coordinate towers decide only tower-faithful spectra; the Weil kernel's spectrum is logarithmic,
   hence tower-faithful (§4.1–4.2).
2. *Tower-supported assemblies have index `0` or `∞`* on two or more towers: no finite set of places
   carries a finite nonzero index, so the finite stratum is a non-local phenomenon (§4.3).
3. *Local positive definiteness is twin-invariant.* A unitary twin twists each tower constituent by a
   unitary character and keeps it positive definite (§4.3).
4. *Upper counts are blind to real nodes.* Over `𝔽_q` a single twist does not remove the blind spot;
   over `ℤ` the blind spot is a real zero of `ζ` in `(½, 1)`, of which there is none, so one parity
   class carries the law (§4.4–4.5).
5. *Finite index is Lindelöf-deep* (HKT), and the index is exactly the number of exceptional waves of
   a count (§4.6): every finite ceiling for `ζ` is a count with finitely many exceptions, hence LH.

So the local-to-global map needs one global input, a count of one parity class at square-root
precision. AKL proves the parts of the map that are theorems and that every weaker class of input
fails.

---

## 3. Objects and language

| Weil over `𝔽_q` | AKL object | Over `ℤ` |
|---|---|---|
| Frobenius tower `ℤ` | a group `G` with **towers** `⟨u_t⟩` | `Γ = ℚ_{>0}`, prime towers `⟨p⟩` |
| closed point of degree `d` | **local constituent** on a tower | `log p · δ₀ − L_p`, `L_p(n) = log p · p^{−|n|/2}` |
| degree grading | **scale** `ℓ : G → ℝ` | `log : Γ → ℝ` |
| `β_i`, `1/β̄_i` | **spectrum**: characters and reflections | `u ↦ u^{ρ−½}`, `u ↦ u^{½−ρ̄}` |
| Riemann–Roch `κ ≤ g` | **ceiling** | wave formula; finite ceiling open (LH-deep) |
| `N_k ≥ q^k+1−Cq^{k/2}` | **global law** (a count) | `ψ(x)−x ≤ C√x log²x`; odd parity class |
| Stepanov | **producer** | open |
| quadratic twist `β ↦ −β` | **twin** | Liouville twist |

**Words.**

- *Tower restriction*: `k ∘ zpowersHom G u`, the kernel on `⟨u⟩`.
- *Cyclic locality*: positivity on every cyclic subgroup implies positivity. *Tower locality*:
  positivity on infinitely many towers of a fixed family implies positivity.
- *Torsion-aliased* (`IsTorsionAliased`): two characters agreeing on a finite-index subgroup.
- *Tower-faithful* (`IsTowerFaithful`): every character non-unitary at all but finitely many towers,
  two distinct nodes agreeing at finitely many towers.
- *Logarithmic spectrum*: characters `u ↦ e^{sℓ(u)}` of one scale; tower scales pairwise
  incommensurable.
- *Axis-supported* (`IsAxisSupported`): a kernel on `ℤ^S` vanishing off the coordinate axes.
- *Count*: a bound on `k(u^n)` along a tower. *Wave*: a term `a v^n` subtracted from a count.
- *Ceiling*: an inequality `κ ≤ F` with `F` from local data and one law.
- *Producer*: a construction yielding a count without assuming it. *Receiver*: a statement equivalent
  to a count.
- *Parity classes*: `{n : λ(n) = ±1}` over `ℤ`; a curve and its quadratic twist over `𝔽_q`.
- *Discriminant*: Krein–Langer data with a node on the unit circle, two colliding nodes, or a zero
  weight.
- *Structure ladder*: **sign** (positive local coefficients), **support** (an Euler product: prime
  data on the towers), **normalization** (pole and Gamma factor matched to the prime mass), **ring**
  (additive structure: `gcd(n, n+1) = 1`, the curve's equation).

---

## 4. Mechanisms

1. **Cyclic subgroups decide the Krein–Langer class.** The elements where a node is unitary or two
   nodes coincide form finitely many subgroups `ker(ν/ν')`. Unitarity subgroups have infinite index.
   Neumann's lemma: every coset of a finite-index subgroup contains an element outside any finitely
   many infinite-index subgroups (`exists_mul_not_mem`). At such an element, pairs merge only within
   torsion-aliasing classes; if every class weight vanished on every coset, Dedekind's independence
   of the distinct torsion quotients would kill all weights. So some cyclic subgroup carries a square
   (`exists_one_le_negIndex_zpowers`). Without torsion aliasing one element separates all nodes, and
   its cyclic subgroup carries the whole index (`negIndex_zpowers_eq_of_not_aliased`).
2. **Coordinate towers decide only faithful spectra.** On `ℤ²` the kernel `2i·sinh(a log 2)·(1−(−1)^b)`
   is two separated pairs of index `2`, torsion-aliased with cancelling weights on the first axis and
   unitary on the second: it vanishes on both axes (`coordinate_locality_fails`). For a tower-faithful
   spectrum all but finitely many towers separate the pairs and carry the whole index
   (`finite_towers_negIndex_ne`). Both clauses of faithfulness are sharp
   (`unitary_tower_defeat`, `aliased_tower_defeat`). Logarithmic spectra with incommensurable tower
   scales are faithful: unitarity is tower-independent and two exponents agree at most at one tower
   (`isTowerFaithful_logChar`). Outside the Krein–Langer class even cyclic locality fails: the star
   kernel `δ₀ − ½Σ_{e₁,e₂,e₁+e₂}(δ_w + δ_{−w})` is positive on every cyclic subgroup and not on `ℤ²`
   (`cyclic_locality_fails_off_class`).
3. **Local constituents meet only at the identity.** The Euler factor is a Poisson kernel:
   `n ↦ r^{|n|}` has form `(1−r²)Σ_{k<N}|h(k)|² + |h(N)|²` (`isPosDefKernel_poissonKernel`), so the local
   kernel `L_p` and all its unitary twins are positive definite (`isPosDefKernel_eulerKernel`,
   `isPosDefKernel_twist`); the constituent `log p·δ₀ − L_p` vanishes at the identity. On `ℤ^S`,
   `|S| ≥ 2`, translates along the diagonal by a large step have differences with every coordinate
   nonzero, off all axes, hence orthogonal: an axis-supported kernel has index `0` or `∞`
   (`negIndex_eq_zero_or_top_of_isAxisSupported`). The assembly `Σ_s a_s(δ₀ − L_s)` is negative on the
   pair `0, e_p` and so has infinite index (`negIndex_localAssembly_eq_top`). With one tower the law
   fails (`rankOne_axis_pair`), as over `𝔽_q`.
4. **The twin over `𝔽_q` is index-preserving and the twist tower completes.** The quadratic twist
   multiplies the trace kernel by `(−1)^n` (`negIndex_traceKernel_quadTwist`) and pairs the counts,
   `N_k + N_k' = 2(q^k + 1)` in odd degree. Upper counts for a datum and its twist do not force RH:
   eigenvalues `±2, ±½` (`one_twist_does_not_complete`). Upper counts for the twists of all `2`-power
   base changes do: `k = 2^j m`, `m` odd, turns the twist count at `(2^j, m)` into the curve's lower
   count at `k` (`unitary_iff_twistTower_upper`).
5. **The parity form of the global law over `ℤ`.** The parity classes partition `{1, …, N}` and differ
   by `L(N) = Σλ(n)`; upper counts for both are RH (`riemannHypothesis_iff_parityClasses_upper`). In
   harmonic–exponential weight, `J = H − 2O` (`liouvilleExpSum_eq_harmonic_sub_oddClass`) and the
   one-sided Liouville law makes the upper count of the odd class alone equivalent to RH, and to index
   zero of `K_ζ` (`negIndex_zetaKernel_eq_zero_iff_oddClass_upper`).
6. **The index is the number of exceptional waves.** Along a separating tower, a count bounded after
   subtracting `m` waves forces each outer node to be a wave (merging frequencies, non-cancellation at
   the top modulus), so `κ ≤ m`; the outer nodes attain it (`negIndex_eq_card_waves`), and a count with
   exactly `κ` waves uses the outer nodes with the pair weights (`minimal_waves_eq_outerNodes`): the
   minimal count determines the hyperbolic spectrum.
7. **Index limits and collisions.** Lower semicontinuity is attained on one finite family
   (`eventually_le_negIndex_of_tendsto`); with the structural ceiling `κ`, the index is continuous along
   pointwise convergence of data off the discriminant (`eventually_negIndex_eq_of_tendsto`). Each part
   of the discriminant lowers it: vanishing weights (`vanishing_weight_drops_index`), colliding
   exponents with opposite weights (`collision_drops_index`), coalescence onto the line (HKT
   `coalescence_law`). On the finite stratum the heat-collision mass is twice the wave number of the
   prime-side count plus twice the multiplicity excess (`waveNumber_collision_law`).
8. **Compressions are receivers.** Over `𝔽_q` the characteristic polynomial of Frobenius, determined
   by finitely many counts, annihilates the trace kernel outright (`compress_traceKernel_charPoly`):
   a spectral-side certificate certifies nothing. Over `ℤ` the compressor `δ₁ − cδ_p` of one Euler
   factor has transform `1 − c p^{ρ−½}`; it vanishes exactly on one vertical progression of spacing
   `2π/log p` (`hat_euler_eq_zero_iff`), never on the strip when `|c| ≤ p^{−½}`, so Euler-factor
   compressions keep the index (`negIndex_compress_euler`). A producer must vanish at the primes,
   on the point side, as Stepanov's polynomial vanishes at the rational points.
9. **Fine towers decide every orbit kernel.** An orbit kernel is a continuous function of the
   logarithmic scale (`continuous_realOrbitKernel`). Cyclic subgroups `⟨u⟩` with `u → 1` are fine grids
   of `ℝ`; rounding points to them and passing to the limit gives positivity from positivity on the
   grids (`hermQuad_nonneg_of_fine_zpowers`), and every finite family's index is eventually attained on
   them (`eventually_le_negIndex_fine`). So the towers `⟨(n+2)/(n+1)⟩` of consecutive-integer ratios
   decide every orbit kernel, with any number of pairs (`isPosDefKernel_orbitKernel_of_consecutive`),
   carry its whole index (`negIndex_orbitKernel_eq_iSup_consecutive`), count the right zeros of `ζ`
   (`negIndex_zetaKernel_eq_iSup_consecutive`), and RH is positivity of the Weil kernel on them
   (`riemannHypothesis_iff_zetaKernel_consecutive`); on the finite stratum every fine enough tower
   carries exactly the index (`eventually_negIndex_fine_eq`). Prime towers are coarse grids and alias;
   consecutive-integer towers are fine and do not. The two-prime lattice contains fine towers
   `⟨p^a q^b⟩` (`exists_fine_twoPrime`), and single such towers carry the index
   (`negIndex_orbitKernel_eq_iSup_twoPrime_towers`): the two-prime law is the fine-tower law.
10. **Attained deep zeros are seen by almost every prime.** For one test and infinitely many zeros,
    suppose the largest depth `D > 0` is attained by finitely many zeros, all others strictly
    shallower (no gap needed). Along a tower, the orbit kernel divided by `e^{n·D·scale}` is the
    unimodular top sum plus a remainder tending to `0` by dominated convergence (Tannery's theorem), so
    non-cancellation at the top makes the kernel unbounded wherever the top nodes are distinct
    (`not_bounded_orbitKernel_pow`). Two zeros alias at
    most at one prime, so all but finitely many prime towers fail positivity
    (`finite_primes_posDef_of_isolated_depth`); for `ζ` with the cubic spline
    (`zeta_finite_primes_posDef_of_isolated_depth`).
11. **Locality is twin-blind.** A unitary character `ω` translates Krein–Langer data:
    `ω·h_{χ,a} = h_{ωχ,a}` (`pairKernel_twist`), reflection commutes with the twist
    (`reflectChar_twistChar`), and tower faithfulness is invariant (`isTowerFaithful_twist`). So the tower
    Hasse principle holds verbatim for every twin (`twin_finite_towers_negIndex_ne`), including the
    Liouville character of `ℚ_{>0}`: no locality theorem is selective.
12. **The structure ladder sorts the battery.** Sign excludes the Liouville twin and the sign flips;
   support excludes `Λ + εn^{−η}` and Davenport–Heilbronn functions; normalization excludes `cΛ`,
   `c ≠ 1`; only the ring level excludes over-regular Beurling systems and the golden datum, which have
   positivity, an Euler product and the right normalization. Kernel-level local positivity sits below
   sign: it is twin-invariant (§4.3). A producer must act at the ring level.

---

## 5. Pillar theorems

**A. Locality.**
1. *Cyclic Hasse principle* (`exists_one_le_negIndex_zpowers`, `negIndex_eq_zero_of_forall_zpowers`): on
   every group, a positive-definite kernel plus hyperbolic pairs (non-unitary characters, distinct
   nodes, nonzero weights) positive on every cyclic subgroup has no pair.
2. *Separation* (`exists_separating_of_not_aliased`, `negIndex_zpowers_eq_of_not_aliased`): without
   torsion aliasing one cyclic subgroup carries the whole index.
3. *Failures* (`coordinate_locality_fails`, `cyclic_locality_fails_off_class`): coordinate towers
   inside the class; cyclic subgroups outside it.
4. *Tower Hasse principle* (`finite_towers_negIndex_ne`, `negIndex_eq_zero_of_posDef_on_infinitely_many`)
   and its sharpness (`unitary_tower_defeat`, `aliased_tower_defeat`); logarithmic spectra are
   tower-faithful (`isTowerFaithful_logChar`); on `ℚ_{>0}` any exponents with nonzero real parts are
   decided by infinitely many primes (`negIndex_eq_zero_of_posDef_on_infinitely_many_primes`); every
   unitary twin is decided the same way (`twin_finite_towers_negIndex_ne`).
5. *Fine towers* (`hermQuad_nonneg_of_fine_zpowers`, `eventually_le_negIndex_fine`,
   `continuous_realOrbitKernel`, `isPosDefKernel_orbitKernel_of_fine`, `negIndex_orbitKernel_eq_iSup_fine`,
   `eventually_negIndex_fine_eq`, `negIndex_orbitKernel_eq_iSup_twoPrime_towers`,
   `isPosDefKernel_orbitKernel_of_consecutive`,
   `negIndex_orbitKernel_eq_iSup_consecutive`, `negIndex_zetaKernel_eq_iSup_consecutive`,
   `riemannHypothesis_iff_zetaKernel_consecutive`): for orbit kernels, with any number of pairs, the
   consecutive-integer towers decide positivity and carry the whole index.
6. *Coarse towers with attained depth* (`not_isPosDefKernel_orbitKernel_zpowers`,
   `finite_primes_posDef_of_isolated_depth`, `zeta_finite_primes_posDef_of_isolated_depth`): with any
   number of zeros, a largest depth attained by finitely many zeros is seen by all but finitely many
   prime towers.

**B. Local constituents and ceilings.**
1. *Poisson law* (`isPosDefKernel_poissonKernel`, `isPosDefKernel_eulerKernel`, `isPosDefKernel_twist`).
2. *Zero-or-infinity law* (`negIndex_eq_zero_or_top_of_isAxisSupported`) and *no finite set of places
   has finite index* (`negIndex_localAssembly_eq_top`); the law needs two towers (`rankOne_axis_pair`).
3. *Riemann–Roch ceiling* (`two_mul_negIndex_traceKernel_le`), attained by the golden datum
   (`golden_attains_ceiling`).
4. *Wave formula* (`card_le_of_bounded_sub_waves`, `exists_waves_bounded`, `negIndex_eq_card_waves`):
   the index is the least number of exceptional waves of a bounded count along a separating tower;
   minimal counts are rigid: their waves are the outer nodes with the pair weights
   (`nodeCoeff_outer_eq_sum_waves`, `minimal_waves_eq_outerNodes`).

**C. Producers and parity.**
1. *Twin invariance over `𝔽_q`* (`negIndex_traceKernel_quadTwist`, `pointCount_add_quadTwist_of_odd`).
2. *One twist does not complete* (`one_twist_does_not_complete`); *the twist tower completes*
   (`unitary_iff_twistTower_upper`), stated through the quadratic twists of the `2`-power base changes
   (`baseChange`, `twistCount_eq_pointCount`, `unitary_iff_twistedBaseChanges_upper`); the golden
   datum attains the genus ceiling, passes the upper count and fails the twist tower (`golden_battery`).
3. *Parity form over `ℤ`* (`riemannHypothesis_iff_parityClasses_upper`); *one class suffices*
   (`riemannHypothesis_iff_oddClass_upper`, `negIndex_zetaKernel_eq_zero_iff_oddClass_upper`).
4. *Compressions are receivers* (`compress_traceKernel_charPoly`, `hat_euler_eq_zero_iff`,
   `negIndex_compress_euler`).
5. *The two producers and their precision* (`stepanov_parity_classes_upper`, `sum_log_prime_le`): over
   `𝔽_q` Stepanov bounds both Legendre parity classes by `q/2 + (deg h + 1)√q`; over `ℤ` integrality
   bounds the primes by `Σ_{p≤n} log p ≤ n log 4`, linear precision.

**D. Completion.**
1. *Attained lower semicontinuity* (`eventually_le_negIndex_of_tendsto`).
2. *Continuity off the discriminant* (`eventually_negIndex_eq_of_tendsto`).
3. *The degenerations* (`vanishing_weight_drops_index`, `collision_drops_index`, HKT `coalescence_law`).
4. *Collisions count exceptional waves* (`zetaKernel_eq_weilFullFunctional`, `Wsummand_ne_zero_of_rightZero`,
   `zetaKernel_eq_onLine_add_pairs_fin`, `waveNumber_collision_law`, `minimal_count_reads_multiplicities`,
   `xiMult_eq_mult`, `collision_mass_from_minimal_count`, `tendsto_collisionMass_iff_consecutive`,
   `bounded_heat_iff_consecutive_bounded`).

---

## 6. Traps

| Trap | Truth |
|---|---|
| The prime towers decide because two primes do for `ζ` | Only for tower-faithful spectra; on `ℤ²` a Krein–Langer kernel of index `2` vanishes on both axes |
| Cyclic locality is a general fact | It holds for the Krein–Langer class and fails for finite-support kernels with a signed spectrum |
| A cyclic subgroup always carries the whole index | Only without torsion aliasing; otherwise it carries at least one square |
| Prime towers cannot decide infinite spectra | They do when the largest depth is attained by finitely many zeros; what remains is an unattained or infinitely attained supremum |
| Locality needs finitely many pairs | For orbit kernels the fine towers `⟨(n+2)/(n+1)⟩` decide with any number of pairs; the archimedean place supplies the continuity |
| A Stepanov certificate is an annihilating compressor | Over `𝔽_q` the characteristic polynomial annihilates the trace kernel and certifies nothing; Euler-factor compressors are index-neutral over `ℤ` |
| Local constituents are positive | The local kernel `L_p` is; the constituent `log p·δ₀ − L_p` is not, and finitely many places have infinite index |
| More places make the index smaller | Tower-supported assemblies on two or more towers have index `0` or `∞`; finite index needs an off-axis constituent |
| Local positivity excludes the twins | Coefficient positivity excludes the Liouville twin; positive definiteness of each constituent is twin-invariant |
| An upper count and its twin give the law | Not over `𝔽_q` (eigenvalues `±2, ±½`); the twist tower does |
| Over `ℤ` both parity classes are needed | One class suffices: the real-node blind spot is a real zero of `ζ` in `(½,1)`, and there is none |
| A finite ceiling can be local | Every finite ceiling for `ζ` is a count with finitely many exceptional waves, hence LH |
| Limits keep the index | Only off the discriminant; vanishing weights, collisions and coalescence lower it |
| A new equivalence is progress | AKL contributions take local data as input and bound, produce or exclude |

---

## 7. Questions and their answers

1. **What replaces `x^q = x` over `ℤ`?** A producer must supply an upper count for one parity class at
   square-root precision (`negIndex_zetaKernel_eq_zero_iff_oddClass_upper`). Over `𝔽_q` it is supplied
   by two identities: `x^q = x` makes the vanishing conditions on the counted set independent of its
   size, and Euler's criterion makes the parity class the zero set of `f^{(q−1)/2} − ε`. A single class
   count is not enough there (`one_twist_does_not_complete`); the twist tower is
   (`unitary_iff_twistTower_upper`). Over `ℤ` one class is enough, and what is missing is an identity
   describing a parity class algebraically. Spectral-side certificates do not help: they are receivers
   (`compress_traceKernel_charPoly`, `negIndex_compress_euler`); the auxiliary must vanish at the primes.
   *Open:* such an identity.
2. **What is the positive form of the parity barrier?** Twins act on constituents by unitary twists,
   so every local constituent stays positive definite (`isPosDefKernel_twist`) and over `𝔽_q` the
   global index is twin-invariant (`negIndex_traceKernel_quadTwist`). Over `ℤ` the twin breaks the
   global law only through a count, and exactly one parity class carries the law. The margin `2 log 2`
   is the width of the window where the pole carries the first square (HKT). Locality is twin-blind
   (`twin_finite_towers_negIndex_ne`), so selectivity can only come from a count or a carrier.
   *Open:* a selective count.
3. **Why does finite index imply LH?** The passage has two steps of different kinds. The kernel step:
   finite index is a count with finitely many exceptional waves (`negIndex_eq_card_waves`), i.e.
   finitely many off-line zeros, so the zeros approach the line. The analytic step: zeros approaching
   the line is Backlund's density form of LH, and its converse to growth on the line is a statement
   about `ζ` itself (HKT `lindelof_of_negIndex_zetaKernel_lt_top`). The kernel supplies exactly the
   first step; no kernel identity bounds `ζ` on the line (inference). *Open:* a proof of the analytic
   step from the positive part of the kernel.
4. **In which completion does the Weil kernel carry its index to the limit?** Two answers. Along
   data: pointwise convergence of Krein–Langer data off the discriminant
   (`eventually_negIndex_eq_of_tendsto`); the index drops exactly by vanishing weights, collisions and
   coalescence. Along the group: the archimedean completion, read through fine cyclic grids; the
   consecutive-integer towers carry the whole index of every orbit kernel
   (`negIndex_orbitKernel_eq_iSup_consecutive`).
5. **Why do two primes suffice, and which arithmetic property makes locality hold?** The spectrum is
   logarithmic: one real logarithm reads every character, so unitarity is tower-independent and two
   incommensurable scales separate any two characters (`isTowerFaithful_logChar`). Cyclic subgroups
   decide every Krein–Langer kernel (`negIndex_eq_zero_of_forall_zpowers`); coordinate towers decide
   only faithful spectra (`coordinate_locality_fails`, `aliased_tower_defeat`). With infinitely many
   pairs the archimedean place takes over: the fine towers `⟨(n+2)/(n+1)⟩` decide every orbit kernel
   (`isPosDefKernel_orbitKernel_of_consecutive`). Two primes suffice because the lattice they generate
   contains fine towers, whose indices have the whole index as supremum
   (`negIndex_orbitKernel_eq_iSup_twoPrime_towers`), attained exactly on the finite stratum
   (`eventually_negIndex_fine_eq`).
6. **What arithmetic quantity governs the near-axis collisions of the heat flow?** The wave number
   of the prime-side count. Each Weil-kernel value is the explicit-formula functional of the spline and
   its translate, pole terms minus the von Mangoldt sum plus the Gamma term
   (`zetaKernel_eq_weilFullFunctional`). On the finite stratum there is a tower along which these values
   are bounded after subtracting `κ` exponential waves and only after at least `κ`, and the collision mass after small times is `2(κ + E)` with `E` the
   multiplicity excess (`waveNumber_collision_law`). Each exceptional wave of the count accounts for
   two collisions, and the index drops by coalescence, the part of the discriminant
   where a node reaches the unit circle (§4.7). The multiplicities are prime-side too: a count bounded
   after exactly `κ` waves uses one wave per right zero, with amplitude `m_ρ |ĝ(γ_ρ)| |ĝ(γ̄_ρ)|`
   (`minimal_count_reads_multiplicities`), so the zero multiplicities `m_ρ` are the minimal count's
   amplitudes divided by the spline factors. Since the order of `ξ` is the multiplicity of the zero of
   `ζ` (`xiMult_eq_mult`), the whole collision mass `2(κ + Σ(m_ρ − 1))` is read off one minimal count
   (`collision_mass_from_minimal_count`). Off the finite stratum the collision mass diverges exactly
   when the indices on the consecutive-integer towers are unbounded
   (`tendsto_collisionMass_iff_consecutive`), and the heat counts are bounded exactly when those
   indices are (`bounded_heat_iff_consecutive_bounded`).

---

## 8. Tools

Built: Neumann avoidance and torsion aliasing (`exists_mul_not_mem`, `IsTorsionAliased`); outward
orientation of pairs and the class-vanishing lemma (`outer`, `sum_mul_eq_zero_of_classWeight`);
tower faithfulness (`IsTowerFaithful`); Poisson and Euler kernels (`poissonKernel`, `eulerKernel`);
axis support and local assemblies (`IsAxisSupported`, `localAssembly`); the quadratic twist and twist
counts (`quadTwist`, `twistCount`); parity classes (`parityCount`, `oddClassSum`); exceptional waves
(`card_le_of_bounded_sub_waves`); limits of data (`tendsto_pairKernel`); compressors
(`frobCharPoly`, `eulerNodes`, `eulerCoeffs`); fine grids and consecutive ratios
(`hermQuad_nonneg_of_fine_zpowers`, `consecutiveRatio`).

To build:

| Tool | Purpose | Test |
|---|---|---|
| Arithmetic compressor (Stepanov over `ℤ`) | an upper count for the odd parity class at precision `x^{½+ε}`; first layer built (integrality at linear precision, Stepanov over `𝔽_q` at square-root precision) | reproduces hyperelliptic RH through the twist tower; fails for Liouville; first rung: beat the sieve constant `2` |
| Ring-level inputs | Bézout relations as local data | fail on over-regular Beurling systems and the golden datum |
| Selective transfer to overlap | the pole carrier of the index-one window at overlapping widths | Q1; fails for Liouville |
| Two-sided coalescent pair theory | prime-pair asymptotics beyond bandwidth one | Q2; fails for parity-twisted models |
| Coarse-tower locality for infinite spectra | prime towers for kernels with infinitely many pairs | recovers the finite case and the fine-tower law |

---

## 9. Open research topics

1. **Producer over `ℤ`**: an identity on the primes playing `x^q = x`; an algebraic or analytic
   description of a parity class; the first rung, beating the sieve's parity constant `2` on intervals
   `x^ε`.
2. **Ring-level inputs**: Bézout relations as local-to-global data.
3. **Prime-tower locality when the depth supremum is not attained, or attained infinitely often**
   (fine towers decide in general; prime towers decide when the largest depth is attained by finitely
   many zeros). The obstruction is a natural boundary: along a tower the generating function
   `Σ_n K(u^n) z^n = Σ_ρ W_ρ/(1 − ν_ρ z)` has poles accumulating on the circle `|z| = e^{−D·scale u}`,
   so boundedness inside the unit disc no longer reaches the poles outside it.
4. **A direct Lindelöf bridge** from a count with finitely many waves.
5. **Collision rates off the finite stratum**: the growth rate of collision mass as `t ↓ 0` against
   the growth of the fine-tower indices.
6. **Finite-level ceilings**: index bounds for height or integer truncations from prime-side data,
   uniform in the truncation (equivalent to finite support; LH-deep).
7. **The atomic index ladder over `𝔽_q`**: the function-field analogue of the index-one window and of
   the margin `2 log 2`.

---

## 10. Success criteria and what a contribution is

**Success.** AKL succeeds when the passage from local data to the index of `K_ζ` is a theorem with one
named global input, and that input is produced: index theory first (locality, ceilings), then a count,
then positivity. The locality and completion parts are theorems; the global input is fixed as an upper
count for one parity class; its production is open. First evidence of a producer is any of: an
auxiliary construction over `ℤ` beating the sieve constant `2`; a ceiling for truncated Weil kernels
from prime-side data, failing for the golden datum; a selective count that fails visibly for the
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

**Principles.** Locality is a property of the spectrum, and it is twin-blind. Local positive definiteness is twin-invariant.
A positive part never pays a pair, and no finite set of towers carries a finite nonzero index.
Upper counts are blind only to real nodes. The index is the number of exceptional waves. Finite index
is Lindelöf-deep. Index, then count, then sign.
