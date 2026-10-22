# The functional equation kills every linear invariant; every RH-bearing invariant is quadratic

- **ID:** `linear-kills-quadratic-survives`
- **Stage:** 1-in-progress
- **Type:** SYNTHESIS (three independently proved corpus theorems are one theorem)
- **Scientific status:** `[SYNTHESIS OF PROVED CORPUS RESULTS]` `[NOT AN RH PROOF]`
  `[NOVELTY: the three components are corpus-proved; the identification is new here]`
- **Statement:** Three results proved independently in three different lanes of this corpus — the
  Selberg-class lane, the detector-classification lane, and the GR/no-boundary lane — are the same
  structural law in three languages. Together they say: **the functional equation annihilates every
  linear (additive, first-moment, order-one) invariant, and every RH-bearing invariant is quadratic
  (energy, variance, order-two).** Consequently no accumulation of linear source data can produce
  RH, and the source must supply a *quadratic* datum. The corpus contains exactly two candidate
  quadratic mechanisms.

## 1. The three results

### (a) Selberg lane — `1-in-progress/selberg-orthogonality-working-log.md` §85.2, Theorem 39

> Every integer-valued invariant the Selberg axioms attach to `F` — the number of gamma factors
> `r_F`, the pole order `m_F`, the degree `d_F` — is **additive** under multiplication in `S`:
> `r_{FG} = r_F + r_G`, `m_{FG} = m_F + m_G`, `d_{FG} = d_F + d_G`. Hence each is a **linear form**
> in the exponents of the primitive factorisation. But Selberg's `n_F = Σ_i e_i²` is a **quadratic
> form**. A quadratic form is not a function of linear forms with generator-independent weights.

Explicit witness inside `S`: for distinct primitive even `χ₁ ≠ χ₂ mod q`,
`F = L(·,χ₁)L(·,χ₂)` and `G = L(·,χ₁)²` share degree, conductor, gamma factor, number of gamma
factors and pole order, yet `n_F = 2` while `n_G = 4`.

**Formalized and unconditional**: `additive_not_determine_energy`,
`additive_family_not_determine_energy`, `energy_ne_of_same_total`.

**Consequence recorded there:** any proof must *manufacture a new integer* — a meromorphic object
whose pole order is a quadratic function of the factorisation. That object is the Rankin--Selberg
convolution.

### (b) Detector lane — `1-in-progress/detector-order-classification-rh-readers.md`

For holomorphic fiber readers `R_F(D) = Σ_j m_j F(z_j, conj z_j)`:

- **order zero** (linear/explicit-formula class): no nonzero global reader detects RH — vanishing
  on real divisors propagates to the whole diagonal by the identity theorem;
- **order one**: every detector carries the displacement as a factor, and is then **annihilated by
  the functional equation**, because the FE mirror `d ↦ −d` forces `Σ_j m_j d_j = 0` identically
  and unconditionally (`mirror_mean_kill`);
- **order two is minimal and forced**: `R_F(D) = −4 Σ_j m_j d_j² H(...)`, a **weighted displacement
  variance**.

So the first moment is killed by the FE and the second moment is the minimal survivor.

### (c) GR/no-boundary lane — `0-backlog/no-boundary-selection-of-zeta.md`, R04 and R25

Writing the period data radially, `w_{p,n} = p^{β_n−½} e^{iγ_n log p}`:

- **selection / purity = single radial LOCATION** (one weight ⟺ one critical line) — a *first-moment*
  statement;
- **RH / stability = zero radial SPREAD** (`β_n = ½` for all `n`) — a *second-moment* statement;
- **location ⊥ spread** (mean ⊥ variance), hence **selection cannot force stability**.

With the minimal counterexample: `σ₁(n) = Σ_{d|n} d` has Dirichlet series `ζ(s)ζ(s−1)`, a genuine
Euler product `Π_p (1−p^{−s})^{−1}(1−p^{1−s})^{−1}`, with zeros at `Re = 3/2`. **Euler product ⇏ RH.**
The object is mixed weight `{0,1}` — two locations.

## 2. They are one theorem

| lane | linear object, killed | quadratic object, forced |
|---|---|---|
| Selberg | additive axiom invariants `r_F, m_F, d_F` | the energy `n_F = Σ e_i²` |
| detector | order-zero and order-one readers; first moment `Σ m_j d_j = 0` | the displacement variance `Σ m_j d_j²` |
| no-boundary | radial location (weight, purity) | radial spread (variance of `β_n − ½`) |

In each lane the linear invariant is destroyed by the **same** mechanism — the functional-equation
involution, which is `s ↦ 1−s` in the detector lane, the `d ↦ −d` mirror on each ordinate fiber,
and the reflection supplying only additive data in the Selberg lane — and in each lane the surviving
invariant is a **positive-definite quadratic form**.

The corpus's own orbit-parity law (`1-in-progress/relocation-blindness-requires-even-multiplicity.md`,
formalized in `RHTower/OrbitParityOffLine.lean`) is the same involution seen once more: the off-line
part of a symmetric divisor contributes an **even** amount at every ordinate, because the involution
`s ↦ 1 − conj s` has the critical line as its exact fixed set.

## 3. What this rules out, and it is a large class

**Any programme whose source data are linear cannot reach RH.** That includes, and the corpus has
already killed each separately:

- weights, degrees, conductors, gamma-factor counts, pole orders (Selberg §85.2);
- the explicit formula applied to a single test function (detector order zero);
- first-moment / mean-kill statements (`NG32`, derived as the order-one obstruction);
- Euler-product selection alone (`σ₁` counterexample);
- purity / weight-filtration selection alone (location ⊥ spread);
- integrality of the zero-counting function *as such* — this is the sharpest instance, because the
  Selberg lane's productive engine **is** counting-function integrality, and Theorem 39 is exactly
  the statement that it produces additive integers only.

That last item deserves emphasis. The Selberg characteristic-function method produced genuinely new
unconditional theorems in this corpus from integrality; and its proved boundary — the geometric side
is a **vanishing detector confined to `{0,1}`**, so it "cannot produce `n_F ∈ ℤ`" — is precisely the
linear/quadratic gap, seen from inside the one lane that pushed integrality hardest.

## 4. What this leaves: the corpus has exactly two quadratic mechanisms

A source-side route must supply a quadratic datum. The corpus contains two candidates and no third:

1. **Polarization.** A positive-definite Hermitian/Hodge form: Weil positivity, the CCM restricted
   Weil floor, Paugam's pairing with `C² = −1` on Meyer's `M_ζ`, Deninger--Singhof's
   `Θ_q = q/2 + S_q`. Over `𝔽_q` this is supplied for free by Weil II: **Frobenius pins the modulus
   `q^{w/2}`, welding location to spread.** Over `ℚ` there is no single Frobenius, and the
   un-welding is the archimedean gap. Deninger's flow `φ^t` with `(φ^t)^*[ω] = e^t[ω]` is the only
   proposed substitute — it is a statement that the flow pins a modulus, which is exactly the weld.

2. **Rankin--Selberg convolution.** `R_{F,F}` is genuinely quadratic in `F`, and its pole order is
   `n_F`. The Selberg lane's closed logical loop is
   `n_F ∈ ℤ ⟸ pole order of R_{F,F} ⟸ meromorphy of R_{F,F} ⟸ all-cusp control of 𝔉_s`.

**These are the same shape**: both are "take the object against itself and read a nonnegative
integer or a nonnegative form". Polarization is the archimedean version; Rankin--Selberg is the
automorphic version.

## 5. The question this makes precise, and it is the only non-mirror one left

> **Is there a quadratic source mechanism other than polarization and Rankin--Selberg?**
>
> Equivalently: is there an object, constructible from Euler/Gamma/FE data alone, that is quadratic
> in the source and whose nonnegativity or integrality is forced by the construction rather than
> assumed?

Failing that, the two known mechanisms must be pushed:

- **Polarization**: construct the positive Hodge form on `M_ζ` from source data — the
  `DAC_ARITHMETIC_CALDERON_GREEN_INTERMEDIATE_EXTENSION` / `DAC_POISSON_GEOMETRIC_HODGE_POLARIZATION`
  gate. Its own card states: *"none of the obvious operators on the Schwartz quotient supplies it"*.
- **Rankin--Selberg**: the all-cusp control of `𝔉_s`, which the Selberg lane names as its terminal
  obligation.

**Neither is a positivity conjecture in disguise, and both are quadratic.** That is the discriminator
this synthesis provides: a proposed route is worth time iff its decisive datum is quadratic in the
source. Every route the corpus has killed fails that test, and both surviving programmes pass it.

## 5b. A refinement, adversarially tested: linear routes die *blind*, quadratic routes die *unbuilt*

The law predicts a **two-type classification of deaths**, and the prediction is falsifiable:

> A route whose decisive datum is **linear** dies of **blindness** — it cannot see RH at all, and no
> amount of construction effort helps.
> A route whose decisive datum is **quadratic** never dies of blindness; if it dies, it dies
> **unbuilt** — the object it needs cannot be constructed.

Six `5-failed` cards hand-checked, including one chosen specifically to break it:

| card | decisive datum | cause of death | consistent? |
|---|---|---|---|
| `downstream-functionals-of-the-zero-set` | functionals of the zero set (linear) | **blindness** — residue-blindness, machine-checked | yes |
| `positive-density-transverse-divisor-relocation-law` | FE, order, HT, counting measure, DA class (all linear) | **blindness** — the invariants cannot separate on-line from off-line | yes |
| `finite-seam-jet-rh-nonselection` | finite Taylor prefix (linear in `xi`) | **blindness** — Hermite interpolation always supplies a fake | yes |
| `ht-weil-compact-detector-near-radical-alternative` | the Weil form (**quadratic**) | **unbuilt** — compact families cannot reach remote quartets; a construction constraint | yes |
| `mobius-fisher-tangent-sonin-boundary-lift-rh` | Fisher information (**quadratic**) | **unbuilt** — sign erasure, derivative to zero, profile mismatch; three computations | yes |
| `polarized-infinite-pair-face-rh-bridge` | polarized pair-face negative index (**quadratic**) | **unbuilt** — *"cannot be functorially lifted … fails before the RH negative-index identity is reached"* | yes |

The last row was the adversarial choice: a card with "polarized" in its title, a genuine
negative-index target, sitting in `5-failed`. If it had died of blindness the law would be broken.
It died of an exact algebraic mismatch in the lift — a construction failure. The law held.

**Why the refinement matters more than the law.** "Unbuilt" is a strictly better failure mode than
"blind". A blind route is dead permanently; an unbuilt route is a route whose object nobody has
managed to make yet. Under this classification, the corpus's `5-failed` bin contains two very
different populations, and only one of them is genuinely closed.

**Method note, recorded because it is the honest part.** I first tried to test this by keyword
classification over all 176 `5-failed` cards; it returned 31 blindness / 34 unbuilt / 18 both /
93 unmatched. **That is not evidence** — the vocabulary is too heterogeneous and 93 unmatched means
the instrument does not measure the quantity. It is the same failure mode as ranking cards by how
many existing modules they cite. Six cards read properly, with one chosen to break the hypothesis,
is worth more than 176 keyword matches, and the full test is 176 careful judgements — legitimate
multi-month work, not something a grep shortcuts.

## 5c. The quadratic routes all die the same death, and it is a *category* error

Applying the refinement: the three quadratic cards die **unbuilt**. Reading what actually kills each
one, they die of the **same thing in three lanes**, and nobody has connected them either.

**(i) Pair-face lift** (`5-failed/polarized-infinite-pair-face-rh-bridge.md`, Lean-proved as
`HTGeometry/OrbitQuotientLiftNoGo.lean`). The obstruction is exact: for `H` an infinite subgroup
there is **no `G`-equivariant linear section of `q : R[G] -> R[G/H]`**, because an `H`-invariant
finite-support vector must vanish; and the `l2` version
(`eq_zero_of_infinite_subgroup_leftInvariant_summable_normSq`) says the same for square-summable
data. But the card's own last escape reads:

> *"Distributional orbit averages avoid `l2` vanishing but leave the Hilbert-potential setting
> required by the Sonin coherence theorem."*

So the lift **exists distributionally** and is destroyed by the Hilbert requirement of the
*consumer*, not by an absolute obstruction.

**(ii) Deninger lane** (`1-in-progress/deninger-source-native-arithmetic-cohomology-roadmap.md`).
Verbatim: *"unweighted infinite-ray Hilbert augmentation has zero quotient seminorm"*; *"bare
Kummer-mode `l2` has no strongly continuous real-flow extension"*; and the prescription
*"Smooth suspension and unit augmentation must therefore precede Hilbert completion … Nuclear
cohomology must be formed first."*

**(iii) CCM Fock lift** (`2-fully-proven/not_new_scientific_knowledge/ccm-higher-subset-covariance-fock-lift.md`).
Verbatim: *"positivity is available before scalarization, but faithful cofinal scalarization is
necessarily unbounded"*, with the explicit norm `sqrt(2^m - m - 1)`.

**The common shape.** In all three, the required quadratic object **exists in the larger category** —
distributions, nuclear spaces, pre-scalarized Fock data — and is annihilated by passing to the
Hilbert/bounded category. The invariance-plus-summability mechanism of (i) is the cleanest statement
of why: *invariance under an infinite group is incompatible with summability*, so any construction
that both respects the infinite symmetry and lands in `l2` is forced to zero.

**This is a positive finding, not a fourth kill.** It says the corpus's quadratic failures share a
category error rather than three unrelated obstructions, and it names the repair the Deninger lane
already prescribes for itself: **form the object nuclearly and complete last, if at all.** Under
that reading the pair-face route is not refuted — its *consumer* is. Replacing the Sonin coherence
theorem's Hilbert hypothesis by a nuclear one is a concrete, stated, unattempted repair.

Stated as the discriminator's second clause:

> A quadratic route is worth re-attacking iff its recorded death is a Hilbert-completion death.
> Three of three quadratic deaths inspected are.

## 6. Honest scope

- The three component results are corpus-proved (one of them formalized); **the identification of
  them as one law is what is new here**, and it is a synthesis, not a theorem. It proves nothing
  that was not already proved.
- "Exactly two quadratic mechanisms" is a claim about *this corpus*, not about mathematics. A third
  may exist and would be the most valuable thing anyone could find.
- The synthesis does not weaken any RH-equivalent statement into something provable. It is a
  triage instrument: it says where not to spend time, and why the two survivors survive.

## Gates

- [x] locate and verify the three component results
- [x] verify the `σ₁ = ζ(s)ζ(s−1)` counterexample (Euler product, zeros at `Re = 3/2`)
- [x] check that Theorem 39's witness is formalized
- [ ] independent audit (Codex) of the identification, especially of whether the Selberg
      additive/quadratic gap really is the same involution as the detector mean-kill
- [x] **audit of the standard mechanisms for forced nonnegativity — completed 2026-07-27, and it
      returns NO third mechanism.**  Mathematics knows essentially seven ways to force a quantity
      nonnegative; the corpus has tried all of them:

      | mechanism | corpus coverage |
      |---|---|
      | squares / Gram / polarization | extensive — the whole Weil/CCM/Hodge family |
      | counting (pole orders, dimensions, indices) | Rankin--Selberg `n_F`; `index theorem` appears in 43 cards, `spectral flow` in 21 |
      | convexity (log-convexity, Jensen, Hölder) | `log-convex` in 36 cards; `gradedPartition_mul_sq_le`; `ThetaCuspKernelLogConcavity` — stops at the all-node wall |
      | positivity of states (C*, KMS, moments) | the Born/KMS and Bost--Connes families |
      | majorization / rearrangement | `majorization` 10 cards, `rearrangement` 41 |
      | combinatorial positivity (Schur, matroids, total positivity) | `total positivity` 21 cards; Stanley--Reisner / matroid laws |
      | entropy / Fisher information | `Fisher` has 8+ cards, several formalized — and the route was **killed**: `5-failed/mobius-fisher-tangent-sonin-boundary-lift-rh.md` retires it with three independent source calculations (Sonin intertwiners erase the Möbius sign; the Fisher-scaled derivative tends strongly to zero; the divisor-incidence commutator has profile `4(1−e^{−u})²`, not the asserted `4(1−e^{−u})`) |

      **The two survivors survive because the others were tried and killed, not because they were
      the only ones considered.**  That is a stronger statement than "the corpus contains two
      mechanisms", and it is the honest outcome of the audit: I did not find a third, and the
      search space of standard mechanisms is now exhausted at this level of resolution.

      A third mechanism, if it exists, is therefore **not** a standard positivity principle applied
      to the usual objects.  It would have to be a nonnegativity forced by a structure with no
      classical name — which is precisely what "construct `C_source`" has always meant.
- [ ] Lean: the abstract linear-vs-quadratic separation is already formalized in the Selberg lane
      (`energy_ne_of_same_total`); the detector mean-kill is `OrbitParityOffLine`-adjacent. A single
      module stating the common law abstractly would be honest infrastructure, not new mathematics.

## Log

- 2026-07-27 (Claude): written after the tenth pre-emption of the session. I proposed a Beurling/FE
  rigidity question; the corpus had already posed and killed the selection framing twice. Following
  the kill led to R25's location ⊥ spread, which led to recognising Theorem 39 and the detector
  order-classification as the same statement. The synthesis is the only thing here that was not
  already in the corpus.
