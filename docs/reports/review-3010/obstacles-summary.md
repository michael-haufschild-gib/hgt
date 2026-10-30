# Research frontier: work, open problems and next questions

Status: 30 October 2026, corpus `4089dad808` plus working tree. **RH is open.**

Companions: [route report](route-obstacles.md) · [walls ledger](walls-ledger.md) · [route unification](route-unification-ledger.md) · [frontier map](../rh-current-frontier-map.md) · [working log](../../../logs/review-3010-rev4-research-2026-10-30.md). Evidence labels [L]/[K]/[S]/[P] as in the frontier map; (inference) marks this review's interpretation; (external) marks literature outside the corpus. No builds were run.

## The corpus in one paragraph

**Classical layer, formalized unconditionally.** Guth–Maynard large values, Vinogradov–Korobov, ≥0.6725 of zeros simple and critical, 0 ≤ Λ_dBN < 1/8, and "≥3/4 critical or a positive proportion of simple off-line zeros near the line".

**Weil positivity beyond the literature.**

- At every fixed fraction of the atom spacing, for ζ and for every sign twin.
- On the complete prime/Gamma/polar atomic matrix at every fixed overlap c, where it rejects the Liouville twin and every cofinite flip.

At fixed c the complete matrix is a solved operator: its low spectrum is spanned by Ramanujan conductor modes with energies E_m(c), explicit nonnegative Fourier tails.

**The decisive invariants are exact.**

- Index of the Weil kernel = 2·#sector zeros.
- Finite index ⟺ bounded heat counts ⟺ all zeros above some height critical.
- The Hecke state on Aff(ℚ) is PD exactly from s = 1/2, the Kakutani threshold of the prime Poisson measure.
- Every line-calibrated explicit formula computes Weil's reflection-paired form W and never the same-point form S. S is read from integer theta prefixes, and RH is S = W.

**The diagnosis.** A crossing input must be critical, square-root precise and selective at once, and no input in the corpus is all three.

## 2.1 Work that is "just work"

Each item has a working mechanism in the corpus and a proved smaller instance. None promises a sign beyond its stated range.

**Complete Weil matrix (HF, SRT, AIP, ACS, SC).**

- **A1.** Integrate fixed conductor packets below (log N)^{1/19} [S]; formalize the reciprocal-shell square budget c²(1 + log c) [P].
- **A2.** Finish the separate shell-payment floor: the top-band witness forcing C ≥ κc²/ε in any one-sided payment NR ≤ G(εD + CS) [S, in progress].
- **A3.** Effective conductor confinement for finite sieve profiles at fixed c. Ingredients, all [L]:
  - the logarithmic sieve spectral tail;
  - harmonic class weights ≍ density × log;
  - the effective Ramanujan approximation `exists_sieveProfile_ramanujan_approximation`, relative error 16(log A + L_Q)/log R;
  - finite-horizon conductor coordinates.
- **A4.** Effective horizons for fixed-c positivity and for the explicit full-index schedules; full-index exhaustion for the smaller Steklov schedule.
- **A5.** Haar branch: first-prime, coarse, polar and head payments on finite cells and finite sources (HF, AIP, ACS, CHMD).
- **A6.** Mean-square conductor costs: replace the sup bound √φ(m) in the prime residual by the period mean square, turning Σφ(m)log²m into Σlog²m (SSH Q6).

**Theta and heat.**

- **A7.** Theta Hankel ranks nine, ten, … by seam-split piece certificates, each stated as flux domination through the square-plus-flux identity.
- **A8.** WD/LA: absorb the C log X outer vertical energy in localized dissipation and sum the local estimates at each fixed t > 0.
- **A9.** HCF/LA: further finite degrees on the log2/log3 grids and Jensen degrees.

**Fixed-aperture positivity.**

- **A10.** RW, EWU, OWU, ACT: further fixed-radius floors and odd witnesses; effective shift thresholds for fixed-support collars.

**Selection and index bookkeeping.**

- **A11.** Integrate "every low conductor sees the flip set" [S]; exact flip thresholds c₀ for further finite flip families.
- **A12.** PW-B: restate the native two-response action on source data, removing `XiZeroCopy` indexing.

**Foundations and programmes.**

- **A13.** ACS 𝔽₃ elliptic base: product formula, quotient measures, Iwasawa characters, Eisenstein unfolding.
- **A14.** HEF: the resolvent Hilbertian formula (σ − 1/2)S = E + D on the full Ξ divisor. Σ_ρ abs(s − ρ)^{−2} converges absolutely, so this is an identity to transport, not an estimate.
- **A15.** ART: formalize the realization obstructions (commutative vs free realization, unique factorization against additive concatenation, Pisot, Cunningham, the Pollicott strip bridge) and the rank law for orthogonal families.
- **A16.** MC: Siegel–Walfisz transfer for growing-modulus shells. WL: higher-order scalar-jet transfer for general prime families.

## 2.2 Open mathematical problems

Nobody knows how to produce these. Strength tags:

| Tag | Strength |
|---|---|
| [RH] | Equivalent to RH |
| [FS] | Finitely many off-line zeros; implies LH |
| [LH] / [QRH] | Lindelöf; zero-free strip |
| [C%] | Critical-line proportion |
| [Siegel] | Exceptional Dirichlet zeros |
| [sub] | Implies no classical conjecture by itself |

**Family Σ — the critical sign.**

| # | Problem | Strength | Corpus form |
|---|---|---|---|
| **B1** | Complete Weil positivity at RH-complete overlap | [RH] | Positivity eventually in N for c⁴/log N → ∞. Margin E(c) ≍ c⁻⁷ → 0. |
| **B2** | Signed joint shell–pole payment | [sub] | W ≥ ac⁻⁷(D − C log(2c)S) for all vectors. Separate payment is capped at c²/ε, defect-only capture is exponential. |
| **B3** | Positive supersolution of the full arithmetic generator | [RH] | The odd Markov form is never subcritical; every obstruction is prime. |
| **B4** | Rank-uniform theta / heat positivity | [RH] | Flux domination uniformly in rank; Λ_dBN = 0; all-degree Jensen. |
| **B5** | An arithmetic same-point identity | [RH] | Express D(s), the Hecke defect or S − W through arithmetic data. Explicit formulas compute only W. |
| **B6** | A source bound on the collision quantum | [RH], [C%] | O ∈ 2ℕ; RH ⟺ O < 2; O ≤ cN with c < 1/4 gives 75%. |
| **B7** | A realization without zero indexing | [RH], [QRH] | CCM anticommutator sign; an unbounded Deninger generator; a Hölder mixing realization of ζ (strip). |

**Family Π — square-root precision.**

| # | Problem | Strength | Corpus form |
|---|---|---|---|
| **B8** | Finite Krein index | [FS] | κ < ∞ ⟺ bounded heat counts ⟺ eventual criticality. |
| **B9** | A square-root producer over ℤ | [RH] | Parity-selective integer auxiliaries of controlled height. Adams costs 2^{qr}; factorial ratios cost 2log2. |
| **B10** | Quadratic effectivity / Rosati heights | [RH] | Subquadratic h⁰ on degree-zero classes of the scaling surface; infinite genus blocks a constant. |
| **B11** | A non-envelope amplifier seed | [RH] | Any subexponential bound on the scaling orbit correlation of one generic cycle. Orthogonal families cancel their gain. |
| **B12** | Dispersion / parity | [QRH]+ | Any fixed zero-free strip; the 5/6 strip ⟺ R = O(N^{5/3+ε}). |
| **B13** | Classical conjectures and census | [LH], [Siegel], [C%] | Lindelöf; density hypothesis below 5/6; exceptional zeros; signed Gram moments near bandwidth 1 for 70%/75%. |

**Family Γ — selection.**

| # | Problem | Strength | Corpus form |
|---|---|---|---|
| **B14** | The exponent at the trivial gauge point | [RH] | θ_μ(0) = 1/2; 0 is never better than typical; gauge-invariant data stop at 3/4. |
| **B15** | Uniform selection at growing resolution | [RH] | Single prime flips need c₀(p) ≍ p^{1/7}; selection and criticality on one schedule. |
| **B16** | Hecke invariance of the collided polarization | [RH] | W = collided; the scaling defect is already a Hecke similitude. |

(inference) At the endpoint the three families are one statement (route-unification ledger §2). B2 is the only open item of unknown strength that controls an entire route family. B6 is the only formulation in which RH has an integer margin.

## 2.3 The three questions to answer next

**Q1. Can the successor shells be paid with their sign?**

Is there, eventually in N and for every coefficient vector, a reserve W ≥ a c⁻⁷(D − C log(2c)S)? Equivalently: is the complete Weil matrix at overlap c a defect-relative perturbation of its conductor Hamiltonian Σ_m E_m(c) abs(⟨x, u_m⟩)², with only O(log c) loss?

- **It is the bottleneck of the most developed route family.** The confinement exponent 16 = 2 + 2·7 is the cost of paying the shells and the pole separately. Every open estimate of HF/SRT/AIP/ACS becomes polynomial bookkeeping once the defect bound is logarithmic.
- **A "yes" must use new structure.** Separate payment is capped at c²/ε [S] and defect-only capture is exponential [L], so only the sign of the shells can work. On conductor modes the sign is known: the Möbius collapse c_m(h) = Σ_{d∣(m,h)} μ(m/d)d and the integrality of h turn the shell symbol into a nonnegative Fourier tail.
- **It is selective by construction.** Continuum shells give only the pole charge, and twisted sources fail repayment.
- **A "no" is just as informative.** A family off the conductor span on which the shells beat the pole at every log-power loss would be a structural obstruction to the whole complete-matrix route.
- **Subquestions:**
  - The lattice gain for vectors that are not conductor modes.
  - A Ramanujan–Plancherel decomposition of the shell block (§2.5 O1).
  - The joint signed bound on span{u_m : m ≤ Q} at growing c.

**Q2. Is there an arithmetic formula for a same-point zero sum?**

Express the resolvent defect

D(s) = Σ_ρ m_ρ · 2(σ − 1/2)(β − 1/2)² / (abs(s − ρ)² · abs(s − ρ*)²) ≥ 0, which vanishes exactly on critical configurations [L, finite configurations; A14 transports it to Ξ],

or the collision charge O(T), or the Hecke defect, through prime data and theta data together.

- **Explicit formulas read one side only.** HEF proves that they compute only the reflection-paired W. Every route that builds positivity from the explicit formula reads one side of the identity whose two sides RH equates.
- **Both readings already exist.** The same-point side is the limit of integer theta-prefix readings (CDG), and W is the prime explicit formula. Q2 asks for a comparison theorem between two existing readings, not for an estimate.
- **Quantization supplies a margin.** O is an even integer, so an identity with error < 2 decides RH, and O ≤ N/4 gives 75%. This is the one place where the zero margin of Σ becomes an integer gap.
- **Subquestions:**
  - (σ − 1/2)S(s) − Re ξ′/ξ(s) at one σ > 1 as a theta–prime expression.
  - A source-realizable non-holomorphic carrier (the ordinate clock is antiholomorphic in one factor).
  - The ℤ-analogue of "every circle-calibrated explicit formula is the Rosati pairing" over 𝔽_q.

**Q3. Is the Weil-kernel index finite?**

Equivalently [L]: are the nonreal heat-zero counts N(t) bounded as t ↓ 0? Are all zeros above some height critical?

- **It is the weakest structural target that implies a first-rank conjecture:** finite index implies Lindelöf.
- **It is selective by itself.** Finite ζ index forces infinite index for every single-prime flip [L].
- **It asks for an integer, not a margin.** The index is lower semicontinuous, and integrality and compactness act on it.
- **The corpus has two independent attack surfaces:**
  - Localized heat dissipation through collisions and t = 0 [K], which needs the C log X outer energy absorbed uniformly as t ↓ 0.
  - Consecutive-ratio tower indices, whose supremum is finite exactly when heat counts are bounded [L].
- **Subquestions:**
  - A uniform N(t) bound from localized dissipation.
  - An arithmetic ceiling for one nonblind prime tower.
  - A Persson-type principle locating the index at infinite height.

## 2.4 A wildly different route

The corpus proves that analytic, spectral, moment, sieve, heat, operator and physical-model certificates collapse onto the same receivers. A route with different walls must therefore rest on a mechanism the corpus does not contain. Corpus searches find no work on crystalline measures, Fourier quasicrystals, Fourier interpolation or Fourier uniqueness pairs.

**Proposal: Poisson rigidity — the zeros as the crystalline partner of the log-integers.**

**The observation.** The explicit formula is a Poisson-type summation formula. On one side stands the zero divisor, with positive integer masses m_ρ. On the other stands the discrete set log ℕ with one-signed masses Λ(n)/√n, plus an explicit smooth Gamma density and a simple pole. Both sides are discrete, with integer or one-signed masses, at logarithmically growing density.

**The external theory** (external, not in the corpus). In this setting, discreteness and positivity on both sides force rigid algebraic structure, and reality of the support comes out of stability rather than out of an inequality:

- Lev–Olevskii: a positive measure with uniformly discrete support and spectrum is a combination of lattice combs.
- Kurasov–Sarnak: stable (Lee–Yang) polynomials produce crystalline measures whose support is real.
- Olevskii–Ulanovskii: Fourier quasicrystals with unit masses are zero sets of real-rooted exponential polynomials.
- Fourier interpolation shows that zero ordinates and log n form a critical-density Fourier pair: Radchenko–Viazovska (nodes √n), Bondarenko–Radchenko–Seip (zeta zeros and log n), Kulikov–Nazarov–Sodin (uniqueness pairs).

**The route.** Classify the crystalline partners of log ℕ. These are integer-mass divisors in the strip whose explicit-formula transform is a one-signed measure on log ℕ, with ζ's Gamma factor and a simple pole. Then prove that every such partner, and every limit of them, is supported on the line. The mechanism would be a rigidity theorem at growing density, or a Lee–Yang principle in infinitely many variables on the prime torus.

**Why it faces different walls.**

- **Σ.** The central statement is a classification, not a positivity estimate. In Lee–Yang theory, reality holds at criticality with no margin because it comes from stability.
- **Π.** Nothing is counted at √x. Growth enters only through the zero density (log T)/2π, which is known.
- **Γ.** The hypothesis class consists exactly of the selection data the corpus proves necessary:
  - discreteness of the dual support (the countermodel with an entire completion and off-line zeros has a continuous Λ-measure);
  - one sign of the dual masses (the Liouville twin is signed);
  - integrality of e^{node} (Beurling systems are not integral);
  - a simple pole (the countermodel has a triple pole).

**What it must supply.**

1. Crystalline rigidity at logarithmically growing density, with an absolutely continuous archimedean part.
2. A complex-support version: off-line zeros are points off ℝ.
3. The mechanism that forces reality, whether stability in infinitely many variables or a structure theorem.

**Risks (inference).**

- **The interpolation identity is linear.** HEF shows that linear identities with holomorphic weights cannot see same-point information. The rigidity must therefore come from the nonlinear constraints (integer masses, one sign, integral nodes), not from the identity itself.
- **The closest corpus candidate is W1C (centred Lee–Yang limits).** W1C builds couplings that converge to Riemann's measure. This route instead classifies the partner directly, which avoids the convergence problem but must handle infinitely many variables.

**First question.** Within the convex set of one-signed discrete measures on log ℕ that carry ζ's Gamma factor, a simple pole and the functional equation, is every partner divisor real? Is ζ's divisor an extreme point of that set?

**Two other directions** stay close to the existing walls:

- **ART's realization/oscillation programme** (paper only) faces Σ6 (realization) and the amplifier rank law.
- **Measure rigidity for ×p actions on the adelic solenoid** has no corpus programme. Its step "a positive measure attached to an off-line zero" reintroduces Σ unless that measure comes from the additive reading.

No further route outside the three walls is visible.

## 2.5 Breakthrough opportunities on Weil positivity

Each item is a mechanism that would create positivity or precision from structure. None is a receiver, a constant or a lower bound.

**O1. Plancherel positivity on the arithmetic ax+b group.**

- **The corpus already contains the pieces of one harmonic-analytic object.**
  - Successor shells pair m with km + h: a dilation k and a shift h, i.e. Aff(ℚ) acting.
  - Ramanujan conductor modes are joint eigenvectors of dilation and successor averaging, and the sieve eigenbasis is the Ramanujan basis.
  - The completed conductor energies E_m(c) are nonnegative Fourier tails produced by Möbius collapse and Poisson summation.
  - Positive-definite functions on Aff(ℚ) have the Kakutani threshold s = 1/2 [L].
- **The opportunity:** a Plancherel theorem for the complete Weil form, W = ∫ (density ≥ 0) dπ over the unitary dual of the adelic ax+b group. The conductor m would be the non-archimedean level and c the archimedean resolution, at every overlap.
- **What is known and what it would give.** At fixed c this holds asymptotically, since the low spectrum is the conductor spectrum. An exact Plancherel identity off the conductor span answers Q1 by identity and makes positivity a density statement.
- **Why it is selective.** Twisted sources change the density; flip blocks have negative energies.
- **The new mathematics.** Aff(ℚ) is not type I, so its Plancherel measure is not canonical. The KMS state at the critical temperature β = 1, where the Hecke exponent equals the Bost–Connes temperature, is the natural candidate to fix it.

**O2. A Rosati involution for ℤ.**

- **The model over 𝔽_q:** every circle-calibrated explicit formula is the Rosati pairing [L], and Rosati positivity gives purity.
- **The situation over ℤ:** W is the Krein form ⟨Jv, v⟩, with J the line reflection on spectral points, and S is the Hilbert norm.
- **The opportunity:** an arithmetic identity S = W + (an arithmetic expression vanishing identically), proved as an identity between the theta reading and the prime reading.
- **Where it would come from:** a "second functional equation" that compares the theta function and the Euler product in a non-holomorphic quantity (abs(ξ)², log abs(ξ), its Laplacian). The functional equation compares them only holomorphically.
- **Why an approximate version suffices:** the collision charge is quantized, so an identity with error below 2 already decides.

**O3. Integrality as margin.**

- **The corpus has three places where integrality creates a margin at criticality:**
  - The shell shift h ≥ 1 repays log(2πc) exactly, while continuum shells give only the pole charge [S].
  - The collision charge O is an even integer [L].
  - The Krein index κ is an integer [L].
- **The opportunity:** arguments whose only analytic input is an approximate statement with error below the integer gap, and whose exact conclusion comes from integrality. This is the characteristic-zero analogue of "eventual Hasse–Weil is Hasse–Weil", where any constant suffices.
- **Concrete targets:** O(T) < 2 from O(T) ≤ 2 − η; a ceiling on κ from an approximate count; repayment of log c for non-conductor vectors from the unit gap of the shift lattice.

**O4. An amplifier along the Hecke flow.**

- **Rate = depth:** a subexponential growth bound on the scaling orbit correlation of one generic cycle is RH [L].
- **The collided form under Hecke translation T_L** grows as e^{2δL} on off-line zeros. Theta prefixes of length n read the Hecke defect for abs(L) ≤ 2 log(n + 1) [L].
- **Why a single orbit can amplify.** ART shows that orthogonal families cancel their own gain. A single Hecke orbit is not such a family.
- **The opportunity:** a unitary realization of the scaling flow on an arithmetic Hilbert space built from the additive (theta) side, with loss independent of L. Hecke translation would play the role of the tensor power in Deligne's argument.

**O5. Disconjugacy for the arithmetic Markov form.**

- **The setting:** the odd Markov form (ACT) is critical, and every obstruction to its variation inequality is prime.
- **The opportunity:** a positive solution of the full nonlocal generator via a Riccati/Sturm comparison. Absence of conjugate points decides positivity at zero margin.
- **Status:** the corpus has a Riccati comparison lemma (`riccati_le_of_le_of_subsolution`) and no application of it to the Markov form. Reflection positivity from locality likewise has no corpus programme.

## 2.6 Does crossing the walls need a new field?

(inference, ideation constrained by the corpus)

**Yes.** Every problem in 2.2 compares the additive and multiplicative structures of ℤ at the exponent 1/2, on an object of infinite rank, at zero margin. Existing fields each supply two of these three features:

| Field | Supplies | Lacks |
|---|---|---|
| Hodge theory | Positivity at zero margin | Works on finite rank |
| Harmonic analysis on groups | Plancherel positivity | Treats + (Fourier on ℝ, ℤ̂) and × (Mellin on ℚ^×) separately |
| Probability | Kakutani dichotomies, typicality, multiplicative chaos | Speaks about almost every gauge, not the trivial point |
| Analytic number theory | Precision | Through estimates that spend a margin |

No field treats the ax+b structure of ℚ — successor ⋊ dilation — as one harmonic-analytic object with positivity theorems at its critical temperature.

**What the field would be about.** Positive-definite functions, states and quadratic forms on Aff(ℚ) ⊂ Aff(𝔸_ℚ), and the comparison of their additive (theta, Poisson, successor) and multiplicative (Euler, Mellin, dilation) spectral decompositions. A working name: **arithmetic Plancherel–Hodge theory**.

**What it would be like.**

- **Like L²-invariants and von Neumann dimension:** infinite-dimensional spaces with a group action carry finite dimensions per unit volume.
  - In the corpus, the zero density (log T)/2π plays the role of such a dimension.
  - The Krein index is the integer that should vanish.
  - The Kakutani threshold s = 1/2 is a change of type of a measure on the gauge torus.
- **Like Hodge theory:** its central theorem is an index theorem holding at the boundary.
- **Like crystalline-measure theory:** discreteness on both sides forces structure.

**Criteria for the field to be real rather than a reformulation.**

1. **Intrinsic objects** defined from ℤ without reference to zeros: Aff(ℚ), its Hecke algebra, the gauge torus, theta prefixes, conductor modes.
2. **A Plancherel theorem** with nonnegative density for Weil's form at every resolution, recovering E_m(c) at fixed overlap.
3. **An additive–multiplicative comparison theorem** (S = W, Hecke invariance) proved as an identity.
4. **Calibration:** over 𝔽_q[T] it reduces to Rosati positivity and Weil's theorem.
5. **Selectivity:** it fails for twins, Beurling systems, continuous Λ-measures and higher-order poles.
6. **A built-in amplifier:** the Hecke flow acts unitarily, and any subexponential bound becomes exact through rate = depth.

**Questions it would answer.**

- Is there a Plancherel decomposition of Weil's correlation over the unitary dual of Aff(𝔸_ℚ) whose density is nonnegative by construction?
- Do the non-archimedean level m and the archimedean resolution c decouple at growing overlap, i.e. is the shell block diagonal in that decomposition?
- Is s = 1/2 a phase transition of a von Neumann algebra attached to Aff(ℚ)? Is Weil's state the unique KMS state there with the prescribed restriction to dilations?
- What replaces the Frobenius graph? A correspondence on the scaling surface whose self-intersection is bounded by an invariant of Aff(ℚ)?
- Is there an integer invariant computable on the additive side that equals the number of off-line zeros? Candidates: a Fredholm index of a Toeplitz operator on H²(𝕋^∞), or the collision charge.
- Which discrete pairs (divisor, log ℕ) are crystalline partners, and are they all real (§2.4)?

**Tools to develop.**

- Mackey theory and Plancherel measures for non-type-I solvable groups; Bost–Connes systems and KMS states.
- Helson–Bohr analysis on 𝕋^∞ and Hardy spaces of Dirichlet series.
- Krein and Pontryagin spaces (the index is exact: HKT/AKLT).
- Kakutani–Hellinger dichotomies.
- Crystalline measures and Fourier interpolation; Lee–Yang stability in infinitely many variables.
- Ramanujan sums as a Plancherel basis on ℤ̂; the scaling surface and its theta Riemann–Roch.

**Objects.** Aff(ℚ) and Aff(𝔸_ℚ); the gauge torus and its trivial point; prime Poisson measures; conductor modes and shells; theta prefixes; the collided form; the collision charge; the Krein index; the scaling surface.

**Language.**

- Plancherel density; additive and multiplicative readings; line-reflection defect; quantum (least excess on off-line configurations).
- Lattice gain; conductor Hamiltonian; selection class (the gauges an invariant separates); precision class (the perturbations n^{−η} it detects).
- Rate = depth; Kakutani threshold.

**Mechanisms it would provide.**

- **Positivity by identity:** Plancherel densities and Fourier tails instead of coercivity.
- **Same-point access:** a Rosati-type involution comparing the two readings, instead of explicit formulas.
- **Margin from integrality:** quantized invariants, instead of margins.
- **Amplification along the Hecke flow:** instead of tensor powers.
- **Selection by structure:** discreteness of log ℕ and the simple pole in the definitions, instead of in the test data.
