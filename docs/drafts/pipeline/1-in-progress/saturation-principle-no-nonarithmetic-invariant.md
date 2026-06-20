# The Saturation Principle — a hypertranscendental object carries no finite non-arithmetic invariant

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
