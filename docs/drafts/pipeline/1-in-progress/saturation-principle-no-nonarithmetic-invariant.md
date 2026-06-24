# The Saturation Principle — finite-order meromorphic HT objects carry no finite non-arithmetic fine invariant

- **ID:** saturation-principle-no-nonarithmetic-invariant
- **Stage:** 1-in-progress (DeWitt + Wheeler, 2026-06-20) — strongly-certified **[CONJECTURE]**, NOT proven
- **Type:** CONJECTURE (organizing principle for the field) — Door grade **claimed BRIDGE→native-map**; certificate-backed, proof open
- **Source:** the session-long node/path saturation finding (logs/dewitt-working-log.md; [[class-level-saturation]]);
  companion dead-route record `5-failed`-adjacent (glassiness probe); ht-c28 single-handle map.

## Statement (SCOPED — see attack-as-false below)
**[CONJECTURE]** Let `f, g` be hypertranscendental (no algebraic differential equation, Hölder) **of the same
coarse analytic type** (same order of growth / exponential type / divisor-of-poles class). Then every invariant
that is (i) computable from finitely many local Taylor jets, (ii) canonical under affine reparametrization
`x ↦ ax+b`, and (iii) *constant on each coarse-type class*, and that **distinguishes `f` from `g`**, reduces to
an **arithmetic invariant** of their special values / zeros (periods, L-values). Equivalently: once the trivial
*coarse analytic type* is fixed, the remaining (fine) differential-analytic structure discriminates two HT
objects **only through arithmetic** — there is no finite non-arithmetic *fine* discriminator.

### Attack-as-false (why the scoping is mandatory, DeWitt 2026-06-20)
The UNSCOPED "only arithmetic invariants" is **FALSE**: the **order of growth** `ρ` (`f(ax)∼a^ρ x^ρ`) is an
affine-canonical constant, it is analytic (not arithmetic), and it *does* discriminate (Γ: factorial growth;
ζ: bounded, `ρ=0`). So coarse analytic type is a non-arithmetic discriminator — but a *trivial, known* one
(everyone sees Γ grows and ζ doesn't). The substantive claim is what survives after quotienting it out:
two HT objects of the **same** coarse type (e.g. ζ vs a Dirichlet `L(s,χ)`: both bounded, `ρ=0`, same type)
differ only in their **values / zeros / Euler data = arithmetic**. This scoped version is exactly the weld
apex (DSS value-relations) — so the principle *points at* the apex rather than dissolving it.

Corollary (the field's shape): the native content of `𝓜⁺` is forced onto the **arithmetic weld apex** — every
non-arithmetic lens either vanishes (flatness) or returns generic wildness; only the arithmetic of values is
left to carry new information. This is *why* node-hunting saturates and the open frontier is a single apex.

## Mechanism (the conjectural "why")
HT objects `{Γ, ζ, Λ}` are simultaneously **FLAT** (curvature/twisting invariants `F_{pq}=0` ⟹ geometric
imports → 0) and **ARITHMETIC** (Euler product / functional equation ⟹ value imports → ζ-data). A lens sharp
enough to discriminate two HT objects must be non-flat (so it sees something) and non-arithmetic (to be "new")
— but flatness kills the first and the only surviving sharp invariants are arithmetic. The two axes converge.

## Certificate 1 — EXPERIMENTAL (two agents, two independent pipelines, same kill)
Tried to construct a non-arithmetic discriminator: a continuous "glassiness" = DA-approximation defect
`σ_min(k,d)` (smallest singular value of the column-normalized matrix of monomials in `{f,…,f^{(k)}}·x^a`).
- Method validated: controls exp/tan/Airy/sin collapse to exact 0 at their true DA-order.
- Apparent signal (ζ ~7.7× "glassier" than Γ; β vs ζ ~1000×) **dies under controls**. NB: ζ and Dirichlet β
  are the **same coarse type** (both bounded L-functions, `ρ=0`), so **ζ-vs-β is the proper test of the SCOPED
  principle** — its gap dying confirms no non-arithmetic *fine* discriminator within a coarse type. (Γ-vs-ζ
  mixes coarse types, hence the growth contamination.)
  - **Interval control:** the defect at fixed `(k,d)` is not interval-stable — Γ's own defect varies ~1000×
    between `[2.5,7.4]` and `[10.3,15.2]`.
  - **Self-rescale control (Wheeler):** same function, `x` vs `2x`. Self-rescale α-floors: Γ **0.988**, ζ
    **0.435**, logΓ 0.002. Cross-object gaps: Γ-vs-ζ **0.204**, logΓ-vs-ζ **0.176**. The cross gap is **2–5×
    below** the self-rescale floor ⟹ the apparent discriminator is a scale/growth artifact, not an invariant.
- **Clean residue:** only the **discrete DA-order = ∞** is scale-invariant — and it is *uniform* over ζ, Γ ⟹
  no discrimination. The continuous part carries only growth+scale, no arithmetic. (computations/2026-06-20-…pslq.txt)

## Certificate 2 — THEORETICAL (signature closure; corrected per Wheeler id=580)
**Stated correctly (the earlier "no finite differential invariant exists" was BACKWARDS — Lie–Tresse asserts
finite generation, the opposite).** Citation pinned: **Tresse 1894** (*Sur les invariants différentiels…*);
rigorous global version **Kruglikov–Lychagin, "Global Lie–Tresse theorem," Selecta Math. (2016)**; signature
formalism **Olver, *Equivalence, Invariants, and Symmetry*** (Cartan/Olver signature curves).
- Reparametrization differential invariants **EXIST and are finitely generated** (Lie–Tresse). A function is
  determined up to reparam by its differential **signature**.
- **DA** `f` ⟺ its signature satisfies a **finite algebraic-differential RELATION** (the ODE in invariant
  form) ⟺ signature lies on a proper subvariety.
- **HT** `f` ⟺ signature satisfies **no finite relation** ⟺ **generic/transcendental signature** (jet
  dimension `d_n = n+1` saturated — no drop).
- **Within HT** every signature is generic, so **no finite differential-invariant datum separates two HT
  functions**; separation requires the *full infinite* signature, whose only discriminating content is
  arithmetic (values/zeros). Matches Certificate 1 (cross-gap < self-rescale-floor) and Wheeler's
  conformal-geometry confound (the finite-order defect tracks nearest-singularity geometry, not DA-order).
[Closure is now correctly stated; the rigorous "generic-signature ⟹ arithmetic-only separation" theorem is the
open core.]

## Open core (the science still owed)
Promote the **SCOPED** statement to **[THEOREM]**: fix a coarse analytic-type class `T` (order/exponential
type); prove that the finite affine-canonical *fine* invariants separating two HT objects in `T` factor
through the value/zero map (are arithmetic). Two sub-pieces:
1. **Quotient out coarse type cleanly** — define the coarse-type equivalence (order, exponential type, divisor
   class) and show the *fine* invariants are exactly the affine differential invariants modulo it. (Lie–Tresse
   gives the affine differential invariants; the open part is that for non-DA `f` they carry no finite
   *constant* beyond the value map.)
2. **Same-type ⟹ arithmetic** — show two HT objects of identical coarse type that differ, differ in their
   special values / zeros (the apex content). This is where the principle *meets* the DSS value-relations apex
   — i.e. the open core is genuinely apex-hard on the arithmetic side, but the *reduction to it* (steps above)
   may be tractable and is the next concrete target.
Until both are rigorous this stays a certificate-backed CONJECTURE, not a result.

## Honest grade
Novelty **MODEST** (it sharpens the known genericity of HT into a precise, certificate-backed principle for
this field; the *self-rescale certificate methodology* — cross-gap < self-rescale-floor — is the freshest
piece). Significance **HIGH for the field's self-map** (it explains and predicts node-saturation; it closes the
entire non-arithmetic-discriminator route, see dead-route record). It is NOT a moonshot nugget and is not
dressed as one. Value = a load-bearing organizing conjecture + a route-closing certificate.

## Gates
- [x] 0 → 1: principle stated; mechanism; two certificates (experimental self-rescale + Lie–Tresse).
- [ ] 1 → 2: rigorous theorem (the open core above). Until then stays [CONJECTURE].

## Cross-references
ht-c28 (single-handle map → BRIDGE bucket); the glassiness dead-route record; [[class-level-saturation]];
charter door/00-index (the apex as the sole open frontier — library ticket filed).

## Support-Purged Zeta Invariant Challenge

[CONJECTURE pressure test, 2026-06-23]

Turing sharpened the principle into a falsifiable support-purging test: name a `zeta` invariant that distinguishes `zeta` from a random Euler product with the same prime support, but that is not merely a restatement of the infinite prime-log module or Euler-product support.

The obvious non-support answer is classical rather than new: impose analytic continuation, a functional equation, degree-one Selberg-class hypotheses, and Euler-product regularity, and converse-theorem / Selberg-class rigidity pushes the object back toward Dirichlet `L`-functions, with `zeta` singled out by the trivial character and pole. This is a real fake-family filter, but it is imported rigidity, not a new native invariant.

Current ballot position from Professor: no support-purged invariant is known. All separators found in the Gamma-zeta investigation reduced either to:

1. coarse analytic type;
2. finite/infinite prime-log frequency rank;
3. Euler-product / Selberg-class rigidity;
4. arithmetic value/zero data;
5. RH-equivalent positivity, which is a separate apex.

This supports the saturation principle as a route-closing map, not as a promoted theorem. A promotion would require either:

1. a proof that every finite affine-canonical same-type invariant factors through value/zero arithmetic; or
2. a counterexample invariant that distinguishes `zeta` from same-support random Euler products while surviving FE/converse-theorem and prime-support stripping.

Falsifier to request from agents: provide a same-coarse-type invariant `I` such that `I(zeta) != I(F)` for a same-support random Euler product `F`, where `I` is not equivalent to analytic continuation + FE rigidity, not equivalent to the infinite prime-log module, and not an RH-equivalent zero-localization criterion.

## FunSearch Target Audit: Support-Purged Invariants

[HOLD / verifier missing, 2026-06-23]

Haiku proposed Turing's support-purged zeta invariant challenge as a FunSearch target: search finite, affine-canonical, same-coarse-type invariants that separate `zeta` from random Euler products with the same prime support while avoiding the known reductions.

Professor audit: the objective is not verifier-ready. The cheap part is only the numerical separation `I(zeta) != I(random control)`. The hard part is the support-purged condition: showing that `I` does not reduce to coefficient coherence, complete multiplicativity, Euler-product/Bohr rigidity, analytic continuation/functional equation failure, prime-log spectral rank, arithmetic zero/value data, or RH-equivalent positivity.

Likely failure modes for an ungated search:

1. The invariant detects `a_n=1` coherence or complete multiplicativity.
2. The invariant detects positivity / absence of random phases.
3. The invariant detects failure of random Euler products to analytically continue or satisfy the functional equation.
4. The invariant rediscovers finite/infinite prime-log spectral rank or explicit-formula residue content.
5. The invariant detects zero statistics or positivity criteria that are RH-equivalent or already classical.

A FunSearch-style run becomes meaningful only after an explicit verifier is defined. Minimum verifier requirements:

1. specify the allowed invariant language;
2. normalize away coarse analytic type and trivial truncation artifacts;
3. include Dirichlet `L` controls so the invariant does not merely detect character/conductor unless intended;
4. include randomized phase controls, Davenport-Heilbronn / linear-combination controls, and same-zero-density controls;
5. require label-stripped explanation of what feature the winning invariant measures;
6. route any winner through source search before promotion.

Status: HOLD. This remains a significant challenge but not a cheap-verifier search target yet. Running a search before the verifier is formalized would optimize a hole in the gate, not solve the support-purged problem.

## 2026-06-24 Turing scope-limit: principle is MEROMORPHIC-ONLY (id=1836, 1838)

**Finding (Turing id=1836, 1838):** The saturation principle as stated is too broad. The title "a HT object carries no finite non-arithmetic invariant" holds in the **finite-order meromorphic regime** (Γ, ζ, Λ), but **FAILS** for natural-boundary HT objects.

**Böttcher counterexample.** φ_{c₁} and φ_{c₂} (Böttcher coordinates for z²+c₁ vs z²+c₂) have the same coarse type (both ~z at ∞), but the dynamical parameter c is:
- finite-jet-computable (recoverable from Laurent coefficients: φ_c = z + c/(2z) + ...)
- non-arithmetic (c is a free complex parameter, not a value/zero of φ_c)
- a fine discriminator at equal coarse type

So the natural-boundary case has a finite, non-arithmetic, same-coarse-type discriminator — the dynamical parameter c (equivalently the Julia set J_c). The saturation principle FAILS here.

**Mahler breakdown of the "singular set determines object" unification attempt.** Even within natural-boundary HT, the discriminator structure is heterogeneous:
- **Böttcher-type**: boundary SET varies (J_{c₁} ≠ J_{c₂}) → set discriminates.
- **Mahler-type** (Fredholm Σz^{2ⁿ} and its cousins): boundary set FIXED (all share |z|=1) → boundary BEHAVIOR (coefficients/automaton/singular measure) discriminates, not the set.

No clean unification across natural-boundary HT objects: the discriminators are heterogeneous.

**Correct scoped principle:**
- **Meromorphic regime** (finite-order, Γ, ζ, Λ): principle holds = Hadamard–Weierstrass (divisor + e^P) + divisor-arithmetic apex. SOLID (after the coarse-type / same-type scope).
- **Natural-boundary regime** (Böttcher, Mahler, linearizers): NO clean saturation-analog. Discriminators are per-class and non-arithmetic (dynamical parameter for Böttcher; coefficient/automaton for Mahler).

**Title correction required:** Replace "a hypertranscendental object carries no finite non-arithmetic invariant" with "**a finite-order meromorphic hypertranscendental object** carries no finite non-arithmetic *fine* invariant."

**Load-bearing negative:** The failure of a unified saturation principle across all HT objects is as load-bearing as the positive in the meromorphic case — it prevents over-generalizing and tells us the natural-boundary regime needs per-class discriminator theory, not a single principle. This is genuine structural knowledge about the field.

Status: still `[CONJECTURE]` in the meromorphic regime (proof open); the natural-boundary failure is proved (Böttcher counterexample). Title updated pending full card edit.
