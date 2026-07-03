# RH via Monodromy-Weight Mismatch — the constraint-route proof shape

- **Register:** SEARCH. Everything here is `[CONJECTURE]` / `[REDUCTION]` / `[OPEN CORE]` unless
  marked `[KNOWN]` or `[PROVED HERE]` with a file anchor. Nothing in this document is promoted.
- **Origin:** synthesis of the three formal lanes of this repo (Hurwitz, u₀, Böttcher/q62),
  2026-07-03. This is a *downstream-application* map of the hgt branch: the branch (constraint,
  not flow) is the ground; RH is the hoped-for downstream payoff, not the mission.
- **Companion:** `01-research-plan.md` (concrete moves, sequencing, terminalization).

---

## 1. The thesis in one paragraph

The three lanes prove algebraic-independence statements by three different **obstruction
mechanisms** — unbounded-order monodromy (q62), natural boundary (u₀), asymptotic scale
separation (Hurwitz) — and in every case the algebra was cheap while the single analytic
obstruction carried the whole proof. Transposed to ζ: RH is equivalent to a **branching
statement** (the coherent ℤ₂-Kummer tower of ξ exists on the half-plane Re s > 1/2), the
branching data is a **coarse ℤ/2^k-valued monodromy cocycle**, and the q62 template says an
off-line zero should be killed not by a positivity inequality (Weil) and not by function-level
recurrence (Bagchi) but by a **weight mismatch**: the defect a zero creates in the cocycle
cannot be matched by anything the two constraints (functional equation + Euler positivity) can
produce, because the constraint side is (almost-)invariant under a group action under which the
defect transforms with unbounded weight. The graded ladder RH_{2^k} (all off-line multiplicities
divisible by 2^k) turns RH into a sequence of parity statements, of which level 1 — *no
odd-multiplicity, in particular no simple, off-line zeros* — is the first genuinely new
intermediate target.

---

## 2. Evidence base: what the three lanes actually established

### 2.1 The meta-theorem `[PROVED HERE, meta-level]`

Every independence result shipped in this repo was proven by obstruction, never by identity.
The generic algebra is banked and reusable; the entire cost was always one analytic detector.

| Lane | Mechanism | Key results | Anchors |
|---|---|---|---|
| q62 disconnected | unbounded-order monodromy: a relation must be σ-fixed, but σ scales one coordinate by roots of unity of unbounded order | `q62_independence`, `q62_disconnected_both` | `formal/GaloisForLFunctions/Bottcher/Q62.lean` |
| u₀ | natural boundary: a relation would force continuation across a wall | `u0_mstep_independence` | `formal/GaloisForLFunctions/U0/U0PhiMStepFar.lean:267` |
| Hurwitz | asymptotic scale separation: relation coefficients pinned to zero one growth scale at a time | `hurwitz_n2_unconditional`, `MixedTailIndependent` | `formal/GaloisForLFunctions/Hurwitz/N2Final.lean:207`, `Hurwitz/AllNTailIndependence.lean:948` |

Side-of-the-weld assignment: monodromy is a **{σ_p}-side** tool (discrete, Galois-flavored),
scale separation is a **∂_s-side** tool (archimedean, asymptotic), natural boundary is the seam
itself. `q62_mixed` is the only proof in the codebase where two different mechanisms fired in a
single carrier (transcendence/growth on one coordinate, monodromy on the other) — the seam
prototype in miniature. A weld proof for ζ must have exactly that shape.

### 2.2 The exact q62 monodromy shape (the thing to transpose)

`NoRelation` (`Bottcher/Q62.lean:27`):

```
def NoRelation (K) {M} [Field K] [Field M] [Algebra K M] (F G : M) : Prop :=
  ∀ P : Polynomial (Polynomial K),
    (P.map (aeval G : Polynomial K →ₐ[K] M).toRingHom).eval F = 0 → P = 0
```

The disconnected-case hypothesis that kills relations (verbatim from `q62_independence`):

```
∀ d : ℕ, ∃ (σ : M ≃ₐ[K] M) (ζ : M) (m : ℕ),
  d < m ∧ orderOf ζ = m ∧ σ G = G ∧ σ ζ = ζ ∧ σ F = ζ * F
```

Read it as: *for every weight bound d there is a symmetry fixing the base and the partner while
scaling F with weight exceeding d.* A polynomial relation P(F,G) = 0 must be fixed by every σ,
but σ multiplies the F-graded pieces by distinct characters of unbounded order — the pieces
vanish one weight at a time. **No inequality, no positivity: relations die of weight mismatch.**

### 2.3 The banked machinery this approach can consume directly

- Kummer descent: `noRelation_pow_descent` (`U0/U0MStepKummer.lean:41`), two-sided
  `noRelation_pow_descent_both` (`KummerRootApplications.lean:28`).
- Analytic roots and coherent towers: `analyticOnNhd_of_continuousOn_exp_eq`
  (`U0/U0KummerBranch.lean:40`), `exists_analyticOnNhd_pow_eq` (`U0/U0KummerBranch.lean:100`,
  variant `Bottcher/AnalyticRoot.lean:107`), coherent ℤ₂-tower from ONE log
  `u0_coherent_kummer_tower` (`U0/U0KummerBranch.lean:224`).
- Faithful germ carrier: `analyticSubring` / `meroField` (`Bottcher/MeromorphicField.lean:34`)
  — makes "no algebraic relation" a statement about actual functions.
- Index-formula-with-resonance-pinning pattern: `index_formula_split`
  (`Bottcher/IndexFormula.lean:254`) + `IndexWiring*` — a global sum rule over fixed points used
  to exclude configurations. The explicit formula will play this role for ζ (§6).

### 2.4 Banked no-gos this approach must respect

- **ω = 0 ⇏ RH** (ledger, 2026-06-19): hypertranscendence/independence of ζ does NOT force zero
  location. So this approach must NOT argue "ζ independent of X ⟹ RH". The lanes contribute a
  *proof template and machinery*, not a lemma. The divisor is a different invariant than the
  relation ideal; §3 is precisely the bridge from divisor to monodromy (not to relations).
- **Natural boundary ≠ hypertranscendence** — obstruction types are not interchangeable; each
  target needs its matched detector.
- **Computations-are-theatre guard:** pre-register predictions; never run theory-predictable
  compute.

---

## 3. The reformulation: RH as a Kummer-tower / branching statement

### 3.1 Objects

- ξ(s) := ½ s(s−1) π^{−s/2} Γ(s/2) ζ(s): entire, order 1. `[KNOWN]`
- Constraints: FE ξ(s) = ξ(1−s); reality ξ(s̄) = conj ξ(s); ξ real and **positive on the whole
  real axis** (no zeros in [0,1] real, ξ(0) = ξ(1) = 1/2). `[KNOWN]`
- Ω := {s : Re s > 1/2}, simply connected. Z_Ω := zero set of ξ in Ω, with multiplicities
  m(ρ) ≥ 1. All of Z_Ω lies in the open substrip 1/2 < Re s < 1 (zero-free line Re s = 1,
  Hadamard–de la Vallée Poussin). Z_Ω is conjugation-symmetric (ρ ∈ Z_Ω ⟺ ρ̄ ∈ Z_Ω) and
  disjoint from ℝ. RH ⟺ Z_Ω = ∅. `[KNOWN]`

### 3.2 The tower equivalence `[REDUCTION — elementary; to be formalized, Arc A]`

Since Ω is simply connected: ξ nonvanishing on Ω ⟺ ξ has an analytic logarithm on Ω ⟺ the
coherent ℤ₂-Kummer tower exists on Ω (χ_k := exp(L/2^k), (χ_{k+1})² = χ_k, χ_0 = ξ — exactly
the `u0_coherent_kummer_tower` construction). So:

> **RH ⟺ the coherent ℤ₂-Kummer tower of ξ exists on Re s > 1/2.**

Trivial as an equivalence; its value is that it lands RH inside the branch's native,
theorem-bearing, already-formalized language, and that it **grades**:

### 3.3 The ladder RH_{2^k} `[NOVELTY CANDIDATE — literature check pending]`

For k ≥ 1 define

> **RH_{2^k}:** every ρ ∈ Z_Ω has 2^k | m(ρ).

Facts (elementary, proof sketches below):

1. **Root form.** RH_{2^k} ⟺ there is an analytic g on Ω with g^{2^k} = ξ|_Ω.
   (⟸) ord_ρ(g^{2^k}) = 2^k·ord_ρ(g). (⟹) On Ω∖Z_Ω the multivalued log ξ has monodromy
   2πi·m(ρ) around ρ; if all m(ρ) ≡ 0 mod 2^k then exp((log ξ)/2^k) is single-valued on
   Ω∖Z_Ω, and |g| = |ξ|^{1/2^k} → 0 at each ρ, so the singularities are removable and g
   extends with g(ρ) = 0.
2. **Ladder completeness.** (∀k, RH_{2^k}) ⟺ RH: a positive integer divisible by every 2^k
   does not exist, so all-levels forces Z_Ω = ∅. RH_{2^0} is vacuous; the levels strictly
   interpolate.
3. **Level 1 reads:** *off-line zeros, if any, have even multiplicity — in particular there are
   no simple off-line zeros.* No classical detector for off-line multiplicity parity exists (on
   the line, parity IS detectable: sign changes of the real function Ξ(t) = ξ(1/2+it) see odd
   multiplicities — Hardy's method lives there; off the line ξ is not real-valued along any
   natural curve and the classical toolbox goes silent). This asymmetry — parity visible on the
   line, invisible off it — is exactly the kind of gap a monodromy/topological method is native
   to.
4. Caveat, stated plainly: under the (open) simplicity conjecture RH_2 ⟺ RH, so RH_2 is not
   "easier" by inclusion; it is easier by **mechanism** — it is a ℤ/2 topological invariant, so
   detectors unavailable for the full metric statement (winding parity, real-structure
   equivariance, Landau-mod-2 positivity shadows) can engage it.

### 3.4 The obstruction cocycle

Fix σ₀ > 1/2, H > 0. For T ∈ ℝ let B(T) := (σ₀, 2) × (T, T+H) and define the **level-k
obstruction cocycle**

> w_k(T) := (number of zeros of ξ in B(T), with multiplicity) mod 2^k
> = (1/2πi) ∮_{∂B(T)} ξ′/ξ  mod 2^k   (argument principle; boundary-zero-free T),

a ℤ/2^k-valued step function of T. The tower on {Re s > σ₀} exists iff w_k ≡ 0 for all boxes
and all k iff no zeros right of σ₀. The cocycle is the branch-native, coarse shadow of the
zero-counting function — an S(T)-type quantity reduced mod 2^k.

Real-structure equivariance `[REDUCTION — small, Arc B3]`: conjugation pairs the boxes at
heights ±T; conjugation-invariant 1-cycles in Ω∖Z_Ω carry even total winding (zeros pair as
ρ, ρ̄), so the level-1 character kills the conjugation-invariant part of H₁ and the obstruction
is concentrated on classes that *separate* ρ from ρ̄ — i.e., that cross the real axis between
the pair. The FE transports the whole tower across the critical line (the reflected root
g(1−s̄)‾ is a root on the left half-plane), so the critical line is the **seam of a double
tower**; RH says the two towers glue along the seam with all branching ON the seam.

---

## 4. Where each constraint enters

### 4.1 The {σ_p} side: Euler product = a canonical log, with positivity

- log ζ(s) = Σ_{n≥2} (Λ(n)/log n)·n^{−s}, **nonnegative coefficients**, convergent for
  Re s > 1. The Euler product IS an explicit analytic log — the tower exists for free on
  Re s > 1, constructed purely from σ_p-side data. `[KNOWN]`
- Every finite partial product ∏_{p≤X}(1−p^{−s})^{−1} is analytic and **nonvanishing on all of
  Re s > 0** (local factors vanish nowhere; their poles sit on Re s = 0), with explicit
  principal log −Σ_{p≤X} log(1−p^{−s}). So *no finite sub-constraint produces the zeros*: the
  strip zeros are **emergent** — present at no finite level, appearing only in the limit, and
  (Hurwitz's theorem, contrapositive) the partial products fail to converge locally uniformly
  near every strip zero. The zeros live exactly where the σ_p-side construction breaks. This is
  the constraint-not-flow picture verbatim. `[KNOWN]`
- Landau's theorem (nonneg coefficients ⟹ singularity at the real point of the convergence
  abscissa) fixes σ_c(log ζ) = 1 via the pole at s = 1; subtracting the pole destroys the
  nonneg-coefficient structure — that is the classical wall at Re s = 1. The parity question of
  §3.3 asks whether a **mod-2^k shadow of Landau positivity** survives pole subtraction.
  `[OPEN — Arc B2]`

### 4.2 The ∂_s side: FE + reality + growth

The FE contributes the seam geometry (§3.4), the four-fold zero symmetry ρ, 1−ρ, ρ̄, 1−ρ̄, and
— through Γ — the archimedean scale structure that the Hurwitz lane's scale-separation detector
speaks. Hamburger's rigidity theorem `[KNOWN — verify exact hypotheses before citing in
promoted text]` (a Dirichlet series with ζ's FE and mild regularity IS ζ) is the constraint
side's rigidity kernel: within Dirichlet series, the FE has essentially one solution. The
flexibility that permits Davenport–Heilbronn-type off-line zeros only opens up when the Euler
positivity is dropped while keeping the FE. So the two constraints are *jointly* load-bearing
in exactly the way the family picture (§7) predicts.

### 4.3 The vertical flow: Bohr lift and the compact group

Bohr's view `[KNOWN in outline — precise statements to verify, see §8]`: for Re s > 1 the map
t ↦ ζ(s+it) extends to the infinite torus T^∞ = closure of {(p^{−it})_p} (Kronecker flow;
dense orbit since {log p} is ℚ-linearly independent). The **random Euler product**
∏_p (1 − ω_p p^{−σ})^{−1}, ω ∈ T^∞ Haar-random, converges a.s. for σ > 1/2 and is a.s.
nonvanishing `[CHECK — recalled as classical Bohr–Jessen-circle material]`. If that holds, the
picture is: *the Bohr-generic point is zero-free right of 1/2; ζ's strip zeros — if any — are a
pathology of the single deterministic orbit against its own compactification.* RH = "the orbit
is generic for zero-freeness." **Banked refinement (audit F7, object_x ~256):** genericity is
MODEL-DEPENDENT — the Gaussian-analytic-function model, which is EXACT for log ζ's marginals
(ℚ-independence ⟹ Selberg CLT), has strictly POSITIVE off-line zero density (Edelman–Kostlan
~ 1/(π(2σ−1)²)); the zero functional is discontinuous under Gaussian convergence and carried by
the multiplicative cumulants. So RH = the zero functional follows the Euler-random model, NOT
the marginal-exact Gaussian model — the gap between the two IS the arithmetic content.

Key dynamical fact powering the mechanism: the Kronecker flow on T^∞ is minimal and
equicontinuous, so **visits to any open set recur syndetically** (relatively dense return
times). If "a monodromy defect occurs in this height window" were an open condition through the
Bohr lift, syndetic recurrence of defects would be automatic — and §5 turns syndetic recurrence
into a contradiction. The entire difficulty is that the strip-evaluation map is not known to
factor continuously through T^∞ below Re s = 1 (that failure IS the emergence of zeros). The
open core is a *coarse* continuity: not the function, only its ℤ/2^k monodromy data, needs to
pass through the compactification.

---

## 5. The mechanism: defect recurrence + zero-density `[REDUCTION — rigorous proof is Arc C1]`

**Reduction.** Fix σ₀ > 1/2, H > 0, k ≥ 1. Suppose the cocycle w_k has the *defect-recurrence
property*: if w_k(T₀) ≠ 0 for some T₀, then w_k(T) ≠ 0 for a relatively dense (syndetic) set
of T. Then w_k ≡ 0. Proof shape: a syndetic set of defect windows gives ≫ T zeros with
Re s > σ₀ up to height T; Ingham's zero-density theorem `[KNOWN]` gives
N(σ₀, T) ≪ T^{3(1−σ₀)/(2−σ₀)} log^C T = o(T) for every fixed σ₀ > 1/2; contradiction. Hence
every box count ≡ 0 mod 2^k; shrinking boxes around an isolated zero localizes to
2^k | m(ρ) for every ρ with Re ρ > σ₀. Quantifying over σ₀ gives RH_{2^k}; over k, RH.

So the whole route compresses to one question:

> **[OPEN CORE — MWM] Why must monodromy defects recur?** Equivalently: is the level-k
> obstruction cocycle of ξ almost periodic (defect-recurrent) on every closed half-plane
> Re s ≥ σ₀ > 1/2, unconditionally?

Three candidate forcing mechanisms, in decreasing order of wildness:

- **(M1) Weight mismatch via the explicit formula (the q62 transposition, §6):** a
  non-recurrent defect is a term in the explicit-formula sum rule that no prime-side
  (almost-periodic) term can match; kill it by resonance pinning, as `index_formula_split` +
  `IndexResonance` killed off-pattern fixed-point configurations. `[CONJECTURE]`
  **(wave-4 update, 08 §7.2): the single-test form is CLOSED** — in any Landau/Riemann–Weil
  configuration the lone-zero signal x^{β₀−1/2} is dominated by the prime diagonal √x for
  every β₀ < 1. M1 survives only in lower-bound technology: the Turán power-sum question
  (t-aspect clustering — C8 check running) and the graded rung program (08 §7, budget
  T^{cδ^{3/2}} with c < 1/2 near σ = 1, repulsion guard verified VACANT in t-aspect by C7).
- **(M2) Coarse Bohr continuity:** the ℤ/2^k monodromy datum (unlike the function) extends
  continuously/measurably to T^∞; then Kronecker minimality forces syndetic recurrence.
  `[CONJECTURE — DOWNGRADED, audit F3/F6; wave-4: REFUTED as a soft mechanism]`: the parent
  ledger proves ambient-torus data is projection-blind (pure_facts ~9994), and 11 Theorem B
  now PROVES the a.p.-category version — a Weyl-null bump plants a lone FE-symmetric
  quadruple leaving NO trace in any mean/a.p./asymptotic datum, so no coarse-continuity
  mechanism running on soft structure can force defect recurrence. Any surviving M2 must
  consume exact class structure (pointwise series / Euler), not compactified flow data.
- **(M3) Landau-mod-2 positivity:** nonneg log-coefficients force a divisibility/parity
  structure on the emergent divisor. `[REFUTED as positivity-alone, audit F2]`: banked DMV
  import (door bucket X5) — positive Beurling systems with off-line zeros exist, off-line
  zeros are GENERIC in the positive-prime moduli. Survives only as the conjunction
  FE ∧ positivity (Arc B's re-cut target).

**Honesty of scope (register note):** by the Reduction, defect-recurrence at all levels is
*equivalent* to RH — this is a re-routing of the proof burden, not a weakening. Its value: (i)
the burden lands on an **almost-periodicity statement about σ_p-side data**, where the Euler
structure can act; (ii) it grades by k (parity first); (iii) the invariant is coarse — ℤ/2^k,
locally constant — so far weaker regularity than function-level recurrence could suffice.

**Positioning against the known** `[CHECK — both items must be verified before any promotion]`:
Voronin universality (unconditional) approximates only **zero-free** targets on discs in the
strip, and the standard proof that "strong universality" (targets with zeros) must fail is
exactly Rouché + zero-density — the same engine as the Reduction. Bagchi's theorem (recalled:
RH ⟺ strong recurrence of ζ in the strip, ~1981–82) is the function-level ancestor of this
reformulation. The mod-2^k cocycle version is a **strict coarsening** of the hypothesis side of
Bagchi (a ℤ/2^k invariant vs sup-norm germ recurrence); verify Bagchi's exact statement and
proof to confirm the coarsening is genuinely new and not already implicit.

---

## 6. Explicit formula as index formula `[CONJECTURE — Arc C3]`

The q62 connected case was closed by a global sum rule (holomorphic fixed-point index formula
Σ 1/(1−λ) = 0 over the fixed points, `Bottcher/IndexFormula.lean`) plus resonance pinning: any
hypothetical off-pattern configuration had to feed the sum rule, and its contribution could not
be balanced. The ζ-side analogue of the index formula is the **explicit formula**: for suitable
test h,

  Σ_ρ h(ρ) = (archimedean/Γ terms) − Σ_p Σ_j (log p) p^{−j/2} ĥ(j log p) + (pole terms),

a sum rule every zero must feed, forced jointly by FE and Euler product. Weil's criterion
chooses positive-definite h — an inequality. The MWM alternative: choose h (or carrier
elements) transforming in a **weight** under the vertical-flow/Bohr action such that a
non-recurrent off-line defect contributes a component of weight that the prime side — which is
a limit of almost-periodic objects — cannot produce at any weight. Concretely: the prime side
is supported on the frequency set {j log p} (a countable, multiplicatively structured set); a
single non-recurrent zero at β+iγ contributes a *non-almost-periodic* (transient) term with
continuous frequency content; the mismatch to exploit is transient-vs-almost-periodic, i.e.
weight-0-recurrent versus weight-unbounded, the exact q62 dichotomy. The argument principle
mod 2^k makes w_k itself a contour functional of ξ′/ξ, so the cocycle IS an explicit-formula
quantity: the missing piece is a parity-sensitive family of test functions. `[OPEN]`

Transposition dictionary (q62 → ζ):

| q62 ingredient | ζ transposition |
|---|---|
| carrier M = `meroField U` (germs on U) | germs/monodromy data on substrips {Re s > σ₀} |
| base K = ℂ(z) | almost-periodic closure of Dirichlet polynomials (Bohr lift) |
| F = φ_{c₁}, FE φ(z²+b) = φ(z)² | ξ, FE ξ(s) = ξ(1−s), Euler log on Re s > 1 |
| σ ∈ M ≃ₐ[K] M fixing G, scaling F by ζ_m | vertical-flow recurrence acting on cocycle; defect transforms, background invariant |
| ∀d ∃ σ with weight m > d | ∀k: level-k defect non-matchable (ℤ₂-tower = unbounded 2-weight) |
| relation P(F,G) = 0 killed by weight mismatch | off-line zero killed by defect-recurrence × Ingham density |
| index formula Σ 1/(1−λ) = 0 + resonance pinning | explicit formula + parity-sensitive tests |
| disconnected case: monodromy for free | no-Euler members (Davenport–Heilbronn): off-line zeros exist freely `[KNOWN]` |
| connected case: rigidity is the work | Euler members: defect-recurrence is the work |
| mixed case: two mechanisms, one carrier | seam: Γ-side scale separation + p-side recurrence jointly |

---

## 7. The family picture `[CONJECTURE — orientation]`

| Quadratic family (q62 ground) | ζ-side family |
|---|---|
| all degree-2 maps z² + c | Selberg-class-like family: FE + order-1 growth |
| bounded critical orbit (c ∈ M) | Euler product with positivity |
| connected Julia set | all branching on the seam (RH-true) |
| disconnected: escaping critical orbit, free dyadic monodromy, off-seam structure | Davenport–Heilbronn members: FE without Euler product, off-line zeros, constructible at will |
| Mandelbrot set = connectedness locus | conjectural "RH locus" = the Euler-positive members |
| Böttcher coordinate φ_c | the ξ-tower / its log (Euler log where convergent) |
| q62 rigidity in the connected case | Hamburger rigidity: FE + Dirichlet series ⟹ ζ (the locus has rigid kernel) |

The analogy's *predictions* (things to test, not believe): (i) the hard case is the
"connected" one and needs a rigidity input, not more analysis of the disconnected examples;
(ii) intermediate families (Beurling systems: positivity with no FE; D–H: FE with no
positivity) are the moduli in which to run attack-as-false on every proposed mechanism;
(iii) "mixed" members with partial Euler structure should show partial seam-pinning — a
quantitative interpolation worth a card of its own.

---

## 8. Known ground — verified vs to-verify

**Verified in this workspace (do not re-derive):**
- All Lean anchors of §2 (build green, axiom-clean [propext, Classical.choice, Quot.sound]).
- ADH arXiv:2010.09266 + Schäfke–Singer arXiv:1605.02616 are linear+monomial only (checked
  2026-07-03, abstracts fetched — see `docs/drafts/formalization-paper-claim-map.md`).
- ω = 0 ⇏ RH; DSS and RH decoupled (parent-lab ledger, 2026-06-19).
- **Prior-work audit F1–F9 (`04-prior-work-audit.md`, 2026-07-03) — banked in the parent
  ledger, do not re-derive:** D–H off-line zero at 18 digits + coefficient stream + mandatory
  DH-test; DMV positive-Beurling off-line genericity (kills positivity-alone M3); Bohr-torus
  projection-blindness no-go (downgrades M2); "faithful detection = quadratic/signature OR
  global winding/index" + S(T)-CLT RH-blindness; formalized Schur–Cohn winding=inertia bridge;
  Avila quantized-winding lens with its two named obstructions; GAF-vs-Euler-random dichotomy;
  in-house Bohr–Jessen/effective-Voronin lane history.

**Classical, safe at the level cited:** Hadamard–de la Vallée Poussin zero-free line; Ingham
zero-density N(σ,T) ≪ T^{3(1−σ)/(2−σ)} log^C T; Landau's theorem on nonneg coefficients;
Hurwitz's theorem on locally uniform limits; Kronecker/Weyl on T^∞; ξ's FE/reality/positivity
on ℝ; Davenport–Heilbronn (1936) FE-with-off-line-zeros; Hardy's Ξ sign-change method; Voronin
universality with zero-free targets.

**[CHECK] — recalled, NOT yet verified; verify before any use in promoted text:**
1. **RESOLVED 2026-07-03 — C2 verified reading (`checks/c2-bagchi-note.md`), spot-checked.**
   Bagchi's theorem confirmed as recalled: strong recurrence (sup-norm self-approximation of
   ζ(s+iτ) on compacts of ½ < Re s < 1, shift set of positive lower density) ⟺ RH. Proof route
   = Rouché + the FULL zero count (≥ cT, driven to ∞) + zero-density — fetched verbatim
   (Sourmelidis arXiv:2308.07031). NO mod-2^k / parity / divisibility coarsening appears
   anywhere in the fetched line. Primary texts (1981 ISI thesis; Math. Z. 181 (1982) 319–334;
   Acta Math. Hungar. 50 (1987) 227–240) were auth-walled — mechanism read from secondary
   expositions. Verdict: §5 is a *coarsening*, not a rediscovery.
2. **RESOLVED 2026-07-03 (C0, `checks/c0-checks-note.md`) — VERIFIED-KNOWN.** Random Euler
   product converges a.s. for σ > 1/2 via Kolmogorov three-series (Rademacher and Steinhaus),
   hence a.s. analytic and zero-free there — fetched quote in Harper–Nikeghbali–Radziwiłł
   arXiv:1505.01443 (intro); classical origin Wintner, Duke 11 (1944) [pointer, unfetched].
   §4.3's foil stands: the model WITH an Euler product has a.s. NO off-line zeros.
3. **RESOLVED 2026-07-03 (C0) — VERIFIED-KNOWN.** Hamburger exact hypotheses (Perelli
   arXiv:1605.02354 Thm 2.1, fetched verbatim): Dirichlet series abs. conv. σ > 1,
   (s−1)^m F entire of finite order, EXACT ζ-FE (conductor-1 gamma factor) ⟹ F = cζ.
   Rigidity is FE-specific: D–H (different conductor, no Euler product) is the standing
   witness that general Riemann-type FEs have large solution spaces — Arc B's grafting
   question lands exactly in the gap Hamburger leaves open.
4. **RESOLVED 2026-07-03 (C0) — VERIFIED-KNOWN.** DRH: Kimura–Koyama–Kurokawa
   arXiv:1210.1216 (Lett. Math. Phys. 104, 2014); precise form Kaneko–Koyama–Kurokawa
   arXiv:2206.02612 Conj. 5.1 (fetched): partial Euler product on Re s = 1/2 converges to
   L^{(m)}/(e^{mγ}m!) · √2^{ν(ρ)}, m = vanishing order; convergence on the line ⟹ GRH.
   NOTE the bridge: the √2^{ν} factor is the one literature place where zero MULTIPLICITY
   enters an Euler-product convergence law (on-line central; our ladder is off-line).
   Conrad Canad. J. Math. 57 (2005) [pointer, binary-unfetched].
5. **RESOLVED 2026-07-03 (C0) — ABSENT-FROM-LITERATURE (auditable).** Only conditional-on-RH
   on-line simplicity exists (Montgomery ≥ 2/3 simple under RH; simplicity conjecture —
   fetched Wikipedia RH page carries NO off-line-multiplicity statement; targeted searches
   null). No "if RH fails, the failing zeros are simple/multiple/divisible" shape anywhere.
   §10 item 1 upgrades to verified-absent.
6. Resolved in-house earlier (own certified zeros, R1/R2). Balanzario–Sánchez-Ortiz bib data
   confirmed (Math. Comp. 76 (2007)), content 403-unfetched — our certificates supersede it
   for lane purposes.
7. **PARTIALLY RESOLVED 2026-07-03 (C0).** Bohr's theorem verified (Schoolmann
   arXiv:1812.04925; Brevig–Kouroupis arXiv:2302.14519, both fetched): bounded holomorphic
   Dirichlet series in a half-plane ⟹ uniform convergence there (σ_u ≤ θ); with an Euler
   product, uniform convergence ⟹ zero-free. The finer "a.p. in σ > 1/2 ⟺ RH" equivalence
   remains [UNRESOLVED] — seen only in search summaries; source from Titchmarsh/Steuding at
   need (folded into C4's reading batch).
8. **(added, resolved with caveat) D–H off-line density (check #8):** existence/infinitude/
   dense real parts VERIFIED-KNOWN (Ferry–Ghișa–Muscutar arXiv:1602.06328; Righetti
   arXiv:1506.05716 for σ > 1). Near-line asymptotic K₀·T·G(T)/√log G(T) for
   Re ≥ 1/2 + 1/G(T) VERIFIED (Lamzouri–Lee arXiv:2010.10490, fetched) — but its stated
   uniformity needs G(T) → ∞; the FIXED-strip linear law our T/21 instantiates rests on the
   Bombieri–Hejhal Duke 80 (1995) regime [pointer, unfetched]. So: linear-in-T has a strong
   literature prior, not a fetched theorem at fixed δ. **237/237 SIMPLICITY of off-line D–H
   zeros: no literature counterpart at all — genuinely new data.**

---

## 9. Attack-as-false — what kills this, and what survives each death

1. **Bagchi already did the coarsening** (check #1 fails novel): then §5's reformulation
   reduces-to-known; survives: the RH_{2^k} ladder (§3.3), the index/weight mechanism M1 (§6),
   the Lean-native tower language (Arc A) and the family picture (§7). *Check #1 ran
   2026-07-03: he did not — verdict ABSENT (§8.1); this attack is answered.*
2. **An FE + positive-log system with an odd-multiplicity off-seam zero exists** (Arc B1
   succeeds as constructor): kills M3's last stand — positivity-ALONE is already dead (banked
   DMV import, audit F2: off-line zeros generic in the positive-prime moduli); the open cell is
   the FE ∧ positivity conjunction. Survives: M1, and the counterexample itself sharpens WHICH
   Euler feature
   (full multiplicativity? boundedness of local factors?) carries the rigidity. Note Hamburger
   rigidity already forbids such a system inside the strict Dirichlet-series-with-ζ's-FE class
   — the hunt must widen the class (Beurling FE-less systems have no seam; engineered FEs
   needed), and if the hunt PROVES the intersection empty in a usable class, that is itself a
   parity theorem.
3. **The cocycle fails a.p. for trivial reasons unrelated to zeros** (e.g. boundary effects of
   on-line zeros entering boxes): then re-cut the invariant (boxes strictly right of σ₀,
   defect defined by *interior* winding) — this is invariant-engineering, expected iteration,
   not death.
4. **The whole route is secretly the Weil positivity criterion in disguise:** it is not — no
   positive-definiteness enters anywhere; the killing move is weight/recurrence mismatch and a
   density theorem. But keep the check standing: if some step quietly needs a positive kernel,
   name it immediately.
5. **Respect the banked no-go:** any draft that drifts toward "independence/hypertranscendence
   of ζ ⟹ RH" is dead on arrival (ω = 0 ⇏ RH). The monodromy cocycle is divisor data, not
   relation data — keep it that way.

---

## 10. What is genuinely new here (novelty inventory, gate-graded)

1. **RH_{2^k} multiplicity-parity ladder + root/tower equivalence** — `[NOVELTY — VERIFIED
   ABSENT 2026-07-03]`: check #5 ran (C0, `checks/c0-checks-note.md`) — the literature has
   only conditional-on-RH on-line simplicity; nothing on the multiplicity structure of
   hypothetical off-line zeros. Bridges: nobody grades RH by divisibility of off-line
   multiplicities; everyone's prior (simplicity) makes the grading invisible.
2. **Coarse-monodromy (ℤ/2^k cocycle) version of strip recurrence** — `[NOVELTY — VERIFIED
   ABSENT 2026-07-03]`: check #1 ran (C2, `checks/c2-bagchi-note.md`); verdict
   ABSENT-FROM-LITERATURE for the package "mod-2^k coarsening + graded RH_{2^k} ladder +
   analytic 2^k-th root of ξ". Bagchi's own mechanism uses the count at full magnitude and
   never reduces it. The coarsening is the new degree of freedom.
3. **Weight-mismatch mechanism transposed from q62** (M1: explicit formula as index formula +
   resonance pinning, defects killed by unbounded weight, not positivity) — `[CONJECTURE]`, no
   literature counterpart known; this is the wild leap of the document.
4. **Family picture** (Selberg-like family ↔ quadratic family; Euler positivity ↔ bounded
   critical orbit; D–H ↔ disconnected locus; Hamburger ↔ rigidity kernel) — orientation-level
   `[CONJECTURE]`; generates testable sub-questions (§7).
5. **Lean-native ground:** this repo owns the only machine-checked Kummer-tower / monodromy /
   germ-carrier infrastructure; Arc A statements are formalizable *now* against mathlib's ζ.
6. **(added wave 2/3, 2026-07-03) The Reduction + its quantification** — (R_k^θ) × (D) ⟹
   ladder, burden graded in σ₀ (06 §3, §6); with the division of labor "Euler enters only
   through (D), at the μ(n) mollifier" now literature-anchored (C4).
7. **(added wave 3) The family (H-loc) theorem and the principal wall** (09): local
   transfers PROVEN for the D–H family via joint universality threaded through the
   component split; for ζ the obstruction is located exactly — principal-direction
   self-approximation at a vanishing target. New objects opened: the universality-blind
   cone; the primitivity grading of the family picture.
8. **(added wave 3; FINALIZED wave 4) Measured laws of the family:** FE fiber = transversal
   defect minimizer (linear plateau, coeff ≈ 4); Euler moat (open basin, shrinking in T);
   anti-correlated FE/Euler mobility spectra. The wave-3 β-proximity law was REFINED twice
   by pre-registered refutation (R7, R8) into the final jet-transfer law:
   ratio ≈ 1.25·(|Δf′|/|f′_base| + (|f′_tgt|/|f′_base|)·Δβ/r), a HARD jet gate (no large-r
   rescue) plus the line-proximity cutoff (a zero receives β-distant transfers only if its
   distance to the critical line exceeds Δβ). Population t ≤ 420: nine localized zeros,
   four certified transfer edges. Raw + RESULTS under `computations/` (R7-, R8-RESULTS).

Forward moves live in `01-research-plan.md`. The next object to construct is the obstruction
cocycle w_k as a formal object (Arc A) and the reduction of §5 as a paper theorem (Arc C1);
the first genuinely open mathematics is the parity question at level 1 (Arc B).

---

## 11. Wave-4 state of the map (2026-07-03, evening) — routes closed, routes open

Documents added since §10 items 7–8: `10-blind-cone.md`, `11-recurrence-degrees.md`,
08 §§7–7.2; checks c7 (repulsion/density constants), c8 (Turán t-aspect). Lean added:
`RHTower/LogIndependence.lean` (wall's two sides + prime-support freedom),
`RHTower/PerturbationZero.lean` (Rouché-free zero-planting). All axiom-clean, gate green.

**CLOSED routes (each with a proof or verified-negative, not a mood):**
- Multi-modulus universality covering for ζ — closed by 10 Thm C (ζ collects to the trivial
  line in EVERY finite Dirichlet decomposition; blind cone representation-independent).
- Soft-hypothesis droves (any a.p. degree, growth, exact FE, pointwise-asymptotic Dirichlet
  representation, on-line zero structure) — closed by 11 Thm B/B′ (bump surgery); the
  class-level dichotomy route reduces to the trichotomy soft/Goldilocks/categorical, with
  Hamburger collapsing the categorical cell to {ζ}. Sole survivor: the Goldilocks class
  problem (11 §5.3).
- Single-test exact-identity detection of a lone off-line zero (Landau/Riemann–Weil) —
  closed by the signal-vs-prime-diagonal budget (08 §7.2): x^{β₀−1/2} < √x for all β₀ < 1.
- M2 as soft coarse continuity — refuted (11 Thm B realizes projection-blindness in the
  a.p. category).
- a.p.-boundary-leakage near σ = 1 — refuted as bare mechanism (08 §7.1 marker).

**OPEN routes (the live frontier, in current priority order):**
- **The Turán hybrid (#112, sharpened by C8):** t-aspect one-zero-forces-zeros for ζ is
  ABSENT from the literature, but both flanks are proved by the same power-sum method
  (q-aspect Deuring–Heilbronn: Kadiri–Ng–Wong Thm 2.6; t-aspect zero→ψ-oscillation:
  Turán/Pintz/Révész, |ψ(x)−x| ≥ (1−ε)x^{β₀}/|ρ₀|). The missing hybrid is exactly the rung
  mechanism (08 §7): budget near σ = 1 is T^{cδ^{3/2}}, c < 1/2 (C7), guard vacant.
  Attack: power sums s_ν = Σ_ρ (s₀−ρ)^{−ν} at s₀ near 1+iγ₀; a LONE zero makes them a
  single geometric sequence — maximally rigid; play Turán's lower bound against 1-line
  upper bounds for ζ′/ζ.
- **The Goldilocks class problem (11 §5.3):** a class with ζ ∈ 𝓕, bump-rigidity, and a
  non-RH-grade family recurrence mechanism — or a proof that (ii)+(iii) exclude (i), which
  would be the primitivity wall's fourth independent derivation and likely its sharpest.
- **A3 deck-class cocycle (#113):** w_k as the deck class of the 2^k-th-root torsor on
  box annuli (q62 DyadicMonodromy pattern) — formalizable now, no argument principle.
- **Jet/phase structure as mechanism guide:** the measured hard jet gate says recurrence in
  the family is a species-copy mechanism; whatever forces companions for ζ must produce
  jet-copies (constrains the Turán hybrid's expected output: clustered zeros with matched
  local data).

**The wall, triangulated:** primitivity/principal-pinning (10, unique factorization) ≡
S²-vs-B² a.p. gap (11) ≡ soft/categorical trichotomy (11 §5.3) — three independent
derivations of one obstruction. The live routes above are exactly the ones the wall does
not touch: exact identities with lower-bound character, exact monodromy data, and class
rigidity engineering.

---

## 12. Wave-5 state of the map (2026-07-03, night) — the two-front program

Since §11, three arcs concluded and the board was rebuilt around two coupled fronts.

**Concluded arcs.** (i) The Turán hybrid (§11's top route) was built, raced, and KILLED
with a priced death certificate (`12-turan-hybrid.md`, `13-block-lemmas.md`): the spike's
own share of Perron block means closes the loophole; replication is a coherent large
deviation of ~e^{1/δ} primes, measure exp(−c·e^{1/δ}) against forging ceiling
exp(e^{c₁/δ}), c₁ < 1. Recurrence-shaped routes to (R_k) are now closed at exact-Euler
strength — the wall's fourth independent derivation (large-deviation RATE separation),
the sharpest. Salvage banked: L1a concentration, tilted small-ball (D′), rotation
invariance, the Perron self-repair dichotomy, and a standalone threshold-theorem
candidate (12 §6.3.2). (ii) A3 completed end to end and wired to ξ
(DeckCocycle → DeckMonomial → DeckAssembly → DeckMultiZero → XiDeck):
**RH ⟺ ∀k RHLadder k ⟺ deck-class triviality at every off-line ξ-zero**, machine-checked
with no argument principle anywhere. (iii) First cross-lane consumption: the q62 agent's
Painlevé/Morera engine (`Bottcher/SchwarzReflection.lean`) powers `UPlaneDescent.lean` —
xiDescent(w) = ξ(1/2 + √w) is ENTIRE, the descent identity is global and branch-free, and
**RH ⟺ xiDescent ≠ 0 on the slit plane** (`rh_iff_xiDescent_ne_zero_slitPlane`). The
critical line is the slit; the FE is quotiented away; the deck calculus's local
slit-chart geometry is the global domain.

**FRONT M — conservation (the dynamic front).** Banked spine, all axiom-clean:
`deckClass_step` / `deckClass_chain` / `deckClass_deformation_invariant`
(DeckHomotopy.lean — dominated perturbation ‖f−g‖ < ‖g‖ on the annulus charts cannot
move the charge; the global correction root replaces all covering machinery);
`deckClass_of_nonvanishing` + `xi_deckClass_far_field` (FarFieldAnchor.lean — boxes
right of Re s = 1 carry zero charge at every rung: the drain);
`analyticOrderAt_even_of_reflection` (ReflectionParity.lean — central parity for every
FE-symmetric pencil member: the family-wide fixed-point anchor). Program doc:
`15-conservation-program.md` (global bookkeeping; residual open core located there).

**FRONT B — parity (the static front).** `xi_central_order_even` /
`xi_deckClass_central_sq_trivial`: w₁ is trivial at the FE fixed point, from FE alone —
the first constraint-forces-parity theorem; mechanism = the RAMIFIED/FIXED locus of a
constraint symmetry. `14-parity-stratum.md` imposes three filters (D–H
multiplicativity; the symmetry discount — quadruples make symmetric-region charge ≡ 0
mod 4, so symmetric aggregates are blind at k ≤ 2 and detectors must be QUADRANT-LOCAL;
the regularity wall) and audits the classical families: affine/Adams transport is
order-balanced at off-line zeros (can move w₁, never anchor it — exhausted as
detectors); the positivity class lives on the real locus only (re-routed to the seam).
Survivors: conservation-bookkeeping, and a CONSTRUCTED quadrant-ramified cover (#116).

**The coupling (load-bearing).** Conservation forbids interior creation/destruction of
charge; annihilation of a defect pair requires MATCHING charges — a parity input.
Conversely, both surviving parity detectors run through conservation's objects (the
quadrant-local box charge, the far-field anchor, the family deformation). The two
fronts consume each other at a single object: **the quadrant-local charge of the
measured pencil**. Neither front alone is a route; the program is their composition.

**Live routes, current priority.**
1. `15-conservation-program.md` — state the bookkeeping reduction, locate the residual
   open core exactly (boundary/crossing control), grade it per rung.
2. #116 — construct the quadrant-ramified cover (attack-as-false first: a no-go is a
   theorem too; local model = q62's biholomorphic-preimage reflection).
3. #122 seam cocycle — the slit ledger in the u-plane; positivity instruments live here.
4. The u-plane ladder — ℤ₂-tower of xiDescent on the star-convex slit plane (needs
   root-existence beyond convexity; would make each rung one global root statement).
5. Standing: Goldilocks class (11 §5.3), Beurling coherence dial (#96), modulus-only
   holography (#123, blocked on the q62 Dirichlet stack), publication surface (#103).

**The wall, final form this wave:** four independent derivations (principal pinning /
S²∖B² gap / trichotomy / LD rate separation), all confined to value-distribution and
measure registers. The deck charge factors through none of them — that separation is
the reason both live fronts are built exclusively from exact monodromy data.
