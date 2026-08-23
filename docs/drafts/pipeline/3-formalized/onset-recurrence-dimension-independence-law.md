# Complexity onset and quantum-recurrence dimension are independent

- **ID:** `onset-recurrence-dimension-independence-law`
- **Stage:** 3 -- formalised in Lean 4
- **Type:** theorem / static-local complexity / quantum recurrence / finite-scale distortion
- **Parents:** `capacity-compatible-fast-forwardable-incubation-law.md`,
  `local-chain-metric-recurrence-exponents.md`,
  `cubic-phase-seeded-static-local-full-scale-plateau-law.md`
- **Status:** `[LEAN-CLOSED] [FRONTIER ADVANCE] [NOVELTY UNVERIFIED]`
- **Date:** 2026-08-09

## Public sentence

A quantum system can take arbitrarily long to become complex even when its completed motion has
the largest possible recurrence dimension, its eventual complexity is near maximal, and every
spatial bond remains strong. Complexity onset and quantum recurrence are therefore independent
clocks.

## 1. Setup

Put (D=2^n). Use the unit coefficient shell in the full one-site plus nearest-neighbour two-site
Pauli family on an open (n)-qubit path,

\[
 H(x)=\sum_{a=1}^{12n-9}x_aP_a,
 \qquad x\in S^{12n-10}.                                     \tag{1}
\]

Fix circuit errors (0\le\eta<\epsilon_-<\epsilon_+<1), a finite inverse-closed universal
one- and two-qubit alphabet, and (kappa>0). For a simple-spectrum (H), order its eigenvalues
(E_1<\cdots<E_D). For a cyclic unit seed (chi), define the first fidelity return after the
first Poincare-clock half-winding by

\[
 T^{\rm fid}_{H,\chi}(\delta)
 =\inf\left\{t\ge {\pi\over E_2-E_1}:
 1-|\langle\chi,e^{-itH}\chi\rangle|^2<\delta\right\}.       \tag{2}
\]

The lower cutoff removes the trivial initial neighbourhood of (t=0). Changing it by a fixed
positive (H)-dependent factor does not change the logarithmic exponent below.

## 2. Theorem -- maximal recurrence with arbitrary complexity incubation

For every sufficiently large (n) and every sufficiently large prescribed delay (L), there are
one fixed exactly (O(n^3))-preparable cubic-phase seed (chi_{n,L}) and a shell set
(mathcal J_{n,L}) such that

\[
 \boxed{
 \sigma(\mathcal J_{n,L})
 \ge A_n\left(1-{96\over\kappa^2D}\right)L^{-(10n-8)},
 \qquad A_n\ge e^{-O(n\log n)}.}                              \tag{3}
\]

Every (H\in\mathcal J_{n,L}) obeys all of the following.

1. **Arbitrary finite-time incubation:**
   \[
    C_{\epsilon_-}(e^{-itH}\chi_{n,L})
    \le O\!\left(n^3+n\log^c(n/\eta)\right)
    \quad(0\le t\le L).                                      \tag{4}
   \]
2. **Maximal projective spectrum:** its projective rational rank is (D-1), and the seed is
   cyclic.
3. **Optimal spectral capacity:**
   \[
    \sum_{j=1}^D|\langle e_j,\chi_{n,L}\rangle|^4
    \le {2+\kappa\over D}.                                   \tag{5}
   \]
4. **Full later plateau:** at a later epoch its state complexity exceeds
   (cD/\log M_n) continuously for at least (exp(cD)) time.
5. **Maximal continuous recurrence dimension:**
   \[
    \boxed{
    \lim_{\delta\downarrow0}
    {\log T^{\rm fid}_{H,\chi_{n,L}}(\delta)
     \over\log(1/\delta)}
    ={D-2\over2}.}                                            \tag{6}
   \]
6. **Later low-complexity recurrence:** the orbit returns arbitrarily close to the easy seed.
7. **Permanent non-Haar locality:** the fixed local two-query protocol separates its propagator
   from Haar randomness at every real time.
8. **No weak spatial bond:** for a numerical (b_0>0),
   \[
    \min_{1\le i<n}\|V_i(H)\|_{\rm op}\ge {b_0\over2\sqrt n}. \tag{7}
   \]

Consequently no onset upper bound follows from the listed maximality properties and uniform
collision, conductance, and plateau thresholds alone. All of those same thresholds remain valid
while (L) is arbitrary. The theorem does not exclude a finer quantitative invariant that varies
inside this class and genuinely resolves distance to shortcut carriers.

## 3. Proof

### 3.1 Incubation, capacity, plateau, and locality

The capacity-compatible fast-forwardable incubation theorem uses the diagonal path carrier

\[
 H_0(a,b)=\sum_{i=1}^na_iZ_i+\sum_{i=1}^{n-1}b_iZ_iZ_{i+1}.   \tag{8}
\]

This carrier has dimension (2n-1) inside the (12n-9)-dimensional coefficient space, hence
transverse codimension (10n-8). On a compact patch with
(|b_i|\ge b_0/\sqrt n), commuting (Z) and (ZZ) rotations give a uniform compiler for the
complete cubic-phase seed family. Duhamel stability on a tube of radius (O(1/L)) proves (4).
The shell beta-tube law and finite-seed Fubini selection give (3), including
(A_n\ge\exp[-O(n\log n)]).

For the same fixed seed, basis-uniform cubic-phase collision concentration gives (5) outside a
relative fraction (96/(\kappa^2D)). The conull simple-spectrum, maximal-projective-rank, and
cyclic set then supplies the completed-phase plateau, later recurrence, and permanent local
separator. The interaction block on each edge differs from its diagonal centre by operator norm
at most three times the transverse coefficient radius, so the same tube gives (7). These are
exactly the conclusions of the first and third parent cards.

### 3.2 The recurrence exponent is conull on the same shell

The local-chain metric recurrence theorem proves that for almost every path-local Hamiltonian the
projective gap-ratio vector

\[
 \alpha(H)=\left({E_3-E_1\over E_2-E_1},\ldots,
                  {E_D-E_1\over E_2-E_1}\right)              \tag{9}
\]

has simultaneous Diophantine exponent (1/(D-2)). Kleinbock--Margulis extremality then gives the
continuous phase-radius first-return exponent (D-2). This conull property also holds on the unit
coefficient shell: (alpha(cH)=alpha(H)), so its exceptional set is radial, and polar
disintegration transfers ambient nullity to surface nullity.

Let (p_j=|\langle e_j,\chi_{n,L}\rangle|^2). Cyclicity gives (p_j>0) for every (j). Near the
identity phase, with the global phase divided out,

\[
 1-\left|\sum_jp_je^{i\phi_j}\right|^2
 ={1\over2}\sum_{j,k}p_jp_k(\phi_j-\phi_k)^2+O(\|\phi\|^3). \tag{10}
\]

The quadratic form is positive definite on the projective quotient: if it vanishes, every
(phi_j) is equal because every (p_jp_k>0). Fidelity deficit is therefore locally equivalent
to squared projective phase radius. Replacing phase radius (r) by (r\asymp\sqrt\delta) divides
the return exponent by two and proves (6).

Finally intersect the incubation/collision-good set with this conull metric-extremal set. Removing
a null set changes neither the Fubini seed selection nor the lower bound (3). Every remaining
Hamiltonian satisfies items 1--8.

### 3.3 Independence conclusion

Fix (n). The exponent in (6) and the uniform thresholds (5), (7), the plateau lower bound, and
the locality witness do not depend on the prescribed value of (L). Yet (4) holds through that
arbitrary (L). Therefore those conditions do not upper-bound onset. This is a literal
independence theorem for the stated invariant class, not an inference from different ensembles or
a comparison of typical scales.

## 4. Conjecture-to-failure chain and representation change

### C0 -- aggregate exponentially many entanglement cuts

`[REDISCOVERED / INSUFFICIENT]`. A gate-normalized weighted sum of cut entropies has only
polynomial range. Double-counting cut boundaries gives at most (O(n|E|)), and Eisert already
states that entanglement bounds circuit cost only before entanglement saturation.

### C1 -- use additive physical history action

`[FALSIFIED AS AN ENDPOINT LOWER BOUND]`. Directed action can grow linearly, but it is the cost of
one history and therefore upper-bounds, rather than lower-bounds, minimal endpoint complexity.
The Lean-proved observer-unitization law explains why such action need not descend through a
recurrent endpoint.

### C2 -- maximal spectral recurrence dimension forces rapid onset

`[FALSIFIED]` by the theorem above. The recurrence exponent remains ((D-2)/2) while incubation is
arbitrary.

### C3 -- finite-scale subgroup distortion is the correct representation

`[SURVIVES PRELIMINARY ATTACK]`. Intrinsic Hamiltonian time is length along one physical flow;
ambient local-circuit distance is its finite-resolution word/coset length. Brown growth is
finite-scale undistortion, fast-forwarding and incubation are distortion, plateau is diameter
saturation, and recurrence is eventual distortion collapse. This representation does not prove
typical undistortion. It identifies the remaining theorem without confusing recurrence dimension
with onset speed.

The exact `[OPEN CORE]` remains: prove quenched finite-scale undistortion at the geometric Brown
skeleton for the ordinary path-local shell after explicitly paying named weak-cut and
fast-forwardable tubes.

## 5. External frontier and novelty boundary

- `[LITERATURE]` Brown and Susskind formulate growth, plateau, and recurrence as the expected
  complexity history of chaotic quantum dynamics.
- `[LITERATURE]` Haferkamp et al. prove linear complexity growth for random circuits by accessible
  dimension. Fresh random gate parameters are load-bearing; the theorem does not cover repeated
  reuse of one static Hamiltonian.
- `[LITERATURE]` Kotowski et al. prove saturation and recurrence for random local quantum dynamics
  and explicitly leave purely local time-independent Hamiltonians as the target beyond continuously
  injected randomness.
- `[LITERATURE]` Atia--Aharonov and Gu--Somma--Sahinoglu study fast-forwarding classes, but do not
  join arbitrary incubation with maximal recurrence dimension and later full state complexity.
- `[LITERATURE]` Kleinbock--Margulis supplies the metric-Diophantine parent of (6); that exponent is
  not claimed as new here.
- `[LOCAL-RESEARCH]` The incubation and recurrence parents own all separate mechanisms. Candidate
  new content is their measure-preserving conjunction and the resulting onset--recurrence
  independence theorem.

No located primary source states items 1--8 together or proves that maximal local-chain recurrence
dimension leaves complexity onset unbounded. Search absence is not priority evidence; status
remains `[NOVELTY UNVERIFIED]` pending specialist review.

Primary sources:

- A. R. Brown and L. Susskind, *The second law of quantum complexity*,
  [arXiv:1701.01107](https://arxiv.org/abs/1701.01107).
- J. Haferkamp et al., *Linear growth of quantum circuit complexity*,
  [Nature Physics 18 (2022)](https://www.nature.com/articles/s41567-022-01539-6).
- M. Kotowski et al., *Saturation and recurrence of quantum complexity in random local quantum
  dynamics*, [Physical Review X 14 (2024)](https://doi.org/10.1103/PhysRevX.14.041068).
- Y. Atia and D. Aharonov, *Fast-forwarding of Hamiltonians and exponentially precise
  measurements*, [arXiv:1610.09619](https://arxiv.org/abs/1610.09619).
- S. Gu, R. D. Somma and B. Sahinoglu, *Fast-forwarding quantum evolution*,
  [arXiv:2105.07304](https://arxiv.org/abs/2105.07304).
- D. Kleinbock and G. Margulis, *Flows on homogeneous spaces and Diophantine approximation on
  manifolds*, [Annals of Mathematics 148 (1998)](https://annals.math.princeton.edu/articles/12997).

## 6. Hostile audit

1. The theorem proves a positive-measure family with arbitrary incubation, not typical Brown
   growth or a high-probability upper delay tail.
2. Equation (6) takes (delta\downarrow0) at fixed (n,H). It does not justify interchanging this
   limit with (n\to\infty), nor a uniform fixed-error recurrence constant.
3. The seed may depend on (n,L). It remains fixed for the resulting evolution and is never
   resampled in time.
4. The delayed set is fine-tuned. Equation (3) quantifies its shell cost rather than hiding it.
5. “Dimension” in (6) is a metric-Diophantine first-return exponent, not Hilbert-space dimension,
   thermodynamic entropy, or a directly measured black-hole volume.
6. Finite-scale subgroup distortion is a representation and research target, not a proved static
   Brown law.
7. Novelty can reside only in the conjunction and independence conclusion. Every component
   mechanism is credited to its parent.
8. No final-paper claim is authorized before the exact conjunction, including the imported metric
   extremality dependency, is formalized and axiom-audited in Lean.

## 7. Lean realization after corpus refactor

No Lean source is authorized during the active refactor. Afterwards, reuse:

1. the capacity-compatible incubation conjunction;
2. path-local simple spectrum, cyclicity, and maximal projective rank;
3. the metric-Diophantine recurrence theorem after its published dependency has an exact formal
   replacement or formal import acceptable under project rules;
4. the finite-dimensional Hessian identity (10);
5. conull-set intersection and finite-seed Fubini selection.

No Lean source, build, or process was touched in this research cycle.

## Lean status -- corpus coverage of the recurrence-dimension clause

Searched before building.  Clause 2 (maximal projective spectrum) and clause 5 (the recurrence
dimension) already have their governing laws in the corpus, so this card's Lean route is
instantiation rather than new analysis.

| Card item | Existing declaration |
|---|---|
| **the recurrence temporal dimension is exactly the arithmetic rank of the anchored energy gaps** | `relationPhaseEnsemble_temporalDimension_eq_projectiveRank` (`HTGeometry/UniversalProjectiveRecurrenceCapstoneLaw.lean`) |
| maximal temporal rank ⟺ maximal projective energy arithmetic | `lbitTemporalRank_eq_maximal_iff_maximallyProjectiveEnergy` (`HTGeometry/LBitUniformStateRecurrenceLaw.lean`) |
| projective temporal dimension as the rational rank of the visible gap spectrum | `projectiveObserverTemporalDimension` (`RHTower/ObserverTemporalUniversalityLaw.lean`) |
| the completed recurrence dimension is nowhere continuous from three levels on | `completedRecurrenceTemporalDimension_nowhereContinuous` (`HTGeometry/ProjectiveRecurrenceDenseStratificationLaw.lean`) |
| a Floquet return after every prescribed discrete delay, with no arithmetic condition on the spectrum | `exists_weightedFloquetFidelity_recurrence_after` (`RHTower/ProjectiveWeightedFloquetRecurrence.lean`) |

Clause 2 asserts projective rational rank `D-1`, which is the maximal case of
`relationPhaseEnsemble_temporalDimension_eq_projectiveRank`; clause 5's exponent `(D-2)/2` is the
continuous-fidelity reading of the same rank.

### What remains

The card's own construction: the `O(n^3)`-preparable cubic-phase seed `χ_{n,L}`, the shell set
`J_{n,L}` and its measure bound `(3)`, and clauses 1, 3, 4, 6, 7, 8.  These are the complexity-side
statements, not the recurrence-side ones, and they need the incubation and plateau apparatus rather
than the spectral laws above.

## Lean progress ledger (in progress)

New modules landed in `formal/GaloisForLFunctions/HTGeometry/`, all `lake env lean`-clean with
oleans built:

| Module | Content |
|---|---|
| `SortedEnsembleSpectrumScaling.lean` | the increasing rearrangement of a Hermitian spectrum scales; the anchored gap ratios are radial; positive rescaling preserves simplicity |
| `FidelityPhaseRadius.lean` | two-sided comparison of the fidelity deficit with the phase-lattice radius: `deficit ≤ 8π²r²` and `deficit < δ ⟹` every anchored gap phase is within `√δ/(2c)` of a turn |
| `FidelityReturnTime.lean` | `fidelityReturnTime`; a winding return gives a fidelity return; a fidelity return gives a phase return; the deficit never vanishes at a positive time for a non-VWA ratio vector, hence is bounded below on compact positive intervals |
| `FidelityReturnExponent.lean` | **`tendsto_log_fidelityReturnTime`** — the fidelity first-return exponent is exactly half the winding exponent, i.e. `(D−2)/2` |
| `KleinbockMargulis/VwaMeasurable.lean` | the very well approximable vectors form a Borel set |
| `SortedGapRatioGlobalExtremality.lean` | extremality of the sorted gap-ratio map on the *whole* simple locus (countable ball cover) |
| `ChainPauliFinEscape.lean` | **`chainPauliFin_spectrumEscapesRealRelations`** — the numbered nearest-neighbour Pauli family escapes every constant real relation (from `exists_pauliChain_spanWitness` at rate `0`) |
| `ChainVwaSphereNull.lean` | the very well approximable chain directions are shell-null, in coefficient and in patch coordinates |

Together these give equation `(6)`: for a chain direction outside the (null) VWA set, with strictly
positive eigenbasis overlaps, the first fidelity return after a positive cutoff has logarithmic
exponent exactly `(D−2)/2`.

### What still remains

1. **Generic cyclicity of the seed.**  `tendsto_log_fidelityReturnTime` needs `0 < p_j` for every
   level, i.e. the seed must be cyclic.  `exists_incubating_cubicSeed_compiled` does not deliver
   this.  Route: the Krylov determinant `det[χ, Hχ, …, H^{D−1}χ]` is homogeneous of degree
   `D(D−1)/2` in the coefficients, is nonzero at the lacunary one-site witness `∑ 3^i Z_i` (whose
   eigenvectors are the computational basis states, on which the cubic seed has all amplitudes
   nonzero), so its zero set is null and radial — the same `toSphere_eq_zero_of_scaleInvariant`
   pattern as `chainBadSphere`.
2. **Clause 7** — `finiteQLocalAutonomousTransferSignal_gt_haarBenchmark` applies once
   `patchHamLM k ω ≠ 0` and `HasPauliWeightAtMost (Fin (k+3)) 2` are supplied, under the card's own
   "sufficiently large `n`" finite-size inequality.
3. **Assembly** — intersect the incubation good set with the two new conull sets and transport the
   spectrum from `FiniteQubitConfiguration (Fin (k+3))` through `qubitConfigFin` and `finCongr` to
   the `Fin (e+3)` shape the exponent theorem consumes.

## Lean closure

`GaloisForLFunctions.HTGeometry.exists_onsetRecurrence_dimension_independence`
(`formal/GaloisForLFunctions/HTGeometry/OnsetRecurrenceIndependence.lean`) is the boxed theorem:
for every prescribed delay `L` it produces one exactly cubic-phase-preparable seed `c` and the shell
set `onsetGoodSet`, with the measure bound `(3)` unchanged, on which every direction satisfies
clauses 1--8, including

* clause 5, `Tendsto (fun δ ↦ log (orbitFidelityReturnTime …)/log (1/δ)) (𝓝[>] 0)
  (𝓝 ((2^(k+3) − 2)/2))` — equation `(6)`, and
* clause 7, `1/(2^n + 1) < productStabilizerTwoQueryProtocolSignal …` at every real time.

`#print axioms` reports only `propext, Classical.choice, Quot.sound`.

The twelve modules added, in dependency order:

1. `SortedEnsembleSpectrumScaling` — the increasing rearrangement of a Hermitian spectrum scales
   with the coefficients; anchored gap ratios are radial; positive rescaling preserves simplicity.
2. `FidelityPhaseRadius` — the two-sided comparison of fidelity deficit with the phase-lattice
   radius (`Jordan` below, chord above).
3. `FidelityReturnTime` — the first fidelity return; winding return ⟹ fidelity return; fidelity
   return ⟹ phase return; the deficit never vanishes at a positive time for a non-VWA ratio vector.
4. `FidelityReturnExponent` — **`tendsto_log_fidelityReturnTime`**: the fidelity first-return
   exponent is exactly half the winding exponent.
5. `KleinbockMargulis/VwaMeasurable` — the very well approximable vectors form a Borel set.
6. `SortedGapRatioGlobalExtremality` — extremality of the sorted gap-ratio map on the whole simple
   locus, by a countable ball cover.
7. `ChainPauliFinEscape` — **the numbered nearest-neighbour Pauli family escapes every constant real
   relation**, read off `exists_pauliChain_spanWitness` at quadratic rate `0`.
8. `ChainVwaSphereNull` — the Diophantine-exceptional chain directions are shell-null.
9. `EnsembleKrylovGenericity` — the Krylov determinant is real-analytic and homogeneous, so the
   non-cyclic directions are shell-null once one member of the family makes the seed cyclic.
10. `ChainCyclicSeedGenericity` — the near-uniform diagonal carrier is that witness, and a nonzero
    Krylov determinant makes every eigenbasis overlap of the cubic seed nonzero.
11. `OrbitFidelityRecurrenceExponent` — the physical first fidelity return of a cyclic orbit has the
    same exponent.
12. `OnsetRecurrenceIndependence` — the level indexing, clause 7's Pauli-weight bridge, and the
    capstone.

Two card statements were corrected in the course of formalisation. The card's clause 2 asserts that
the seed is cyclic; that is *not* delivered by the incubation law, and its genericity had to be
proved separately (items 9--10) — it is a further null exclusion, not a consequence of maximal
projective rank. Clause 7 needs the card's own "sufficiently large `n`": it is stated under the
explicit finite-size inequality `card (FiniteQLocalPauliLabel (Fin n) 2) · 3² < 2ⁿ + 1`.
