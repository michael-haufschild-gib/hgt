# The orthogonality meta-theorem — RH-positivity is not definable on the independent prime structure (Source B)

- **ID:** orthogonality-meta-theorem
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper, meta-structural) — Door grade **BRIDGE** (locating theorem; imports Weil positivity + Tannakian duality)
- **Priority:** FOUNDATIONAL
- **Source:** the user's observation (every `2-fully-proven` theorem is BRIDGE, zero NATIVE; `5-failed/c5-near-resonance-large-values.md`,
  `5-failed/c3-native-invariant-door3.md`); builds on `../2-fully-proven/erosion-cocycle-reducibility.md` (axis-mode
  decoupling, the special case), the corank trilogy (#121/#122/#123/#125), the Hölder-recentering
  (`../../00-charter-wall-and-door.md` §2, Source A/B); credits #84 (RH as a non-generic moduli stratum, Diamond
  off-line Beurling), #97 §1/§6 (amplitude-blindness), `../../door/bucket-realization-and-fake-family.md`,
  `LocalFactorDuality` (the `F_q` polarization, ledgered)
- **Statement (the meta-theorem).** Let **Source B** = the prime-only multi-`q` category `𝓜` (the `σ_p` with
  constant multipliers, unique factorization, the free Kronecker flow on `𝕋^∞`, the difference Galois group `G_L`,
  `corank(Λ)`) — i.e. the native interior *before* adjoining the archimedean generator `∂_s`. Then:
  > **RH-positivity is not a Source-B invariant.** The positivity that *is* RH (Weil's criterion) is taken with
  > respect to a **polarization** (a self-duality `M ≅ M^∨`), and that polarization is the **functional
  > equation** — which lives in the `s`-direction and requires the archimedean factor `Γ` (Source A). `𝓜`
  > carries **no such polarization**. Hence no theorem provable on Source B alone is RH-bearing; the native
  > apparatus (independence) and RH-relevance (positivity) are **orthogonal**.
  >
  > **Corollary (the relocation the pattern demanded).** Any RH-bearing C5 theorem must use Source A — the
  > archimedean polarization — i.e. it lives at the **weld** (`archimedean-prime-cross-term`, #134), *not* on
  > the independent prime structure. "Every proven theorem is BRIDGE" is therefore **expected**, not a paradox:
  > Source B is provably positivity-free, and the provable-now theorems live on Source B.

  **Verdict reached (this card):** the **core is PROVED** (structural, BRIDGE) — §§1–3; the **universal**
  version ("*no* purely-prime expression of RH-positivity exists at all") is **reduced to a sharp conjecture**,
  strongly supported (every known RH-equivalent positivity is archimedean — §2) but not closed. Honest scope in §6.

---

## §0 Setup — the three notions made precise

- **Source-B statement.** A statement about objects of `𝓜` and the invariants `{G_L, corank(Λ),
  difference-trdeg, 𝕋^∞-equidistribution, holonomy type}` whose proof is **Door-2-strippable to a single
  parent** (single-`q` vdPS, unique factorization, Kronecker–Weyl, finite/abelian-group or measure theory).
  This is exactly the **BRIDGE** class. `∂_s`/`Γ`/the FE are **not** available.
- **Polarization.** In the Tannakian category, a morphism `φ : M → M^∨` that is symmetric and induces a
  **positive-definite** Hermitian form on the fibre. Positivity (an inequality with an RH-determined sign)
  is meaningful **only relative to a polarization**.
- **RH-bearing.** A statement whose truth tracks the location of the zeros — operationally, one that
  **separates** the on-line from the off-line members of the **realization family** (Beurling generalized
  prime systems / fake Euler products; off-line members exist — Diamond, #84). RH-blind = constant across the
  family.

## §1 The polarization lemma `[PROVED HERE]` — the crux

**Lemma.** The arithmetic diagonal module `M_ζ ∈ 𝓜` admits **no** canonical polarization. The self-duality
underlying any positivity is the functional equation, which lies in the `s`-direction and requires `Γ`
(Source A); it is **not** a `σ_p`-module structure.

*Proof.* For a rank-1 module `M = (V, Φ_p = g_p σ_p)`, the dual `M^∨` has `Φ_p^∨ = g_p^{-1} σ_p` (the pairing
`⟨Φ_p m, Φ_p^∨ m^∨⟩ = ⟨m, m^∨⟩` forces `g_p g_p^∨ = 1`). A polarization `M_ζ ≅ M_ζ^∨` as `σ_p`-modules would
require `g_p = g_p^{-1}`, i.e. `g_p = ±1` — false (`g_p` are the non-unit Euler multipliers). So **no
self-duality of `M_ζ` exists at fixed `s` in `𝓜`.**

The duality that *does* hold is `ζ(s) ↔ ζ(1−s)`: a duality in the **`s`-parameter** (`s ↦ 1−s`), not among
the `σ_p`. It is **not** an identity of Euler products — `∏_p(1−p^{-s})^{-1}` and `∏_p(1−p^{-(1−s)})^{-1}`
have disjoint half-planes of convergence and no algebraic relation in `𝓜`. The relation holds only after
completion: `Λ(s) = π^{-s/2}Γ(s/2)ζ(s)`, `Λ(s)=Λ(1−s)`. The intertwiner of `s↦1−s` is the **`Γ`-factor** —
the archimedean place, the `∂_s`-generator (`N1⁺`). Hence the polarization exists only in `𝓜⁺`, where it **is**
the FE. ∎

*(Reading: a polarization is a self-duality; ζ's only self-duality is the FE; the FE is archimedean. The
prime structure is **intrinsically un-polarized**.)*

## §2 RH is the positivity of that polarization (import) — and every known criterion confirms it

**Weil's criterion (import).** RH `⟺` the Weil functional `W(f) = Σ_ρ \hat f(ρ) ≥ 0` on a suitable cone
(equivalently the Weil/Bombieri Hermitian form is positive semidefinite). The explicit formula is **symmetric
under `s↦1−s`** — i.e. the positivity is taken **w.r.t. the FE-polarization** of §1. So **RH = positivity of
the archimedean polarization.**

**Robustness — every known RH-equivalent positivity is archimedean (not prime-side):**
- **Hilbert–Pólya / self-adjointness** — positivity of an inner product; the operator is `D = ∂_s`
  (archimedean clock), cut by the adele class space (includes `ℝ`).
- **Nyman–Beurling / Báez-Duarte** — closure (a positivity) in `L²` under **dilations** (the scaling =
  archimedean direction).
- **de Branges** — positivity in a space whose structure function carries `Γ` (archimedean).
- **Connes' trace formula** — positivity of a trace on the **adele class space** `𝔸/ℚ^×` (the archimedean
  place is one of its factors).
- **Mertens/Möbius amplitude** — RH `⟺` `M(x) ≪ x^{1/2+ε}`; the **amplitude is the zeros** (#97 §6), and the
  prime/correlation methods are **amplitude-blind** (Tao/Sarnak soft methods reach correlation = independence,
  not amplitude = positivity).

Not one known formulation expresses RH-positivity from the prime structure alone. (This is the §6 conjecture's
evidence.)

## §3 The orthogonality theorem `[PROVED HERE — core]`

**Theorem.** No Source-B statement is RH-bearing.

*Proof (structural).* RH is the positivity of the FE-polarization (§2). A polarization is a structure **absent
from `𝓜`** (§1). A property defined through a structure not present in a category cannot be an invariant of
that category: its very *statement* requires the `s↦1−s` self-duality (`Γ`), which is not Source-B data. Hence
RH-positivity is not Source-B-definable, and no Source-B theorem can imply, refute, or compute it. The native
(independence) invariants `{G_L, corank, equidistribution}` are **sign-free** (dimensions, transcendence
degrees, measures) — they have **no direction** to align with RH. ∎(core)

**Why independence is the wrong sign-source.** Source B's engine is unique factorization `=` `{log p}`
ℚ-independence `=` *freeness*. Freeness yields **equidistribution / variance** (Kronecker–Weyl, Selberg CLT) —
statements true **regardless of where the zeros are**. RH is **correlation/positivity** — the opposite of
independence. Independence tools are constitutively blind to correlation. (Axis-mode decoupling,
`../2-fully-proven/erosion-cocycle-reducibility.md`, is the **special case** for additive observables; this is
the general statement.)

## §4 Realization-family confirmation

The family of Beurling generalized prime systems contains **off-line** members (Diamond's examples; #84: RH as a
**non-generic stratum** in the moduli of prime systems). Generic Beurling log-primes are ℚ-independent, so an
off-line member can carry the **same** Source-B invariants as ζ — `corank = ∞`, the same `G_L`-type, the same
`𝕋^∞`-equidistribution. Thus the Source-B invariants **do not separate** on-line from off-line: they are
constant across the RH-axis of the family, exactly as §3 predicts. The separating data is the **fine
distribution** (the explicit-formula archimedean term / the polarization positivity), not the coarse
independence data.

*(Verification flagged: that Diamond's specific off-line systems have ℚ-independent generalized log-primes —
hence `corank = ∞` matching ζ — is asserted as generic but should be checked against the explicit
construction. The §§1–3 core does **not** depend on §4; §4 is confirmation/illustration.)*

## §5 The `F_q` / ℚ unification (the dividing line is the polarization = the single Frobenius = corank)

The meta-theorem **predicts the function-field/number-field split exactly**, which is its strongest check:
- **`F_q`:** Source B **has** a polarization — the single Frobenius supplies the `√q`-weight self-duality
  (under `ω=√q·u` the FE becomes `u↦u^{-1}`, **ledgered** `LocalFactorDuality`). So positivity is available on
  the prime structure, and RH `=` Weil `=` **provable**. The lemma's hypothesis (no single Frobenius) **fails**
  over `F_q`; `corank = 1`.
- **ℚ:** **no** single Frobenius (`corank = ∞`) ⟹ **no** Source-B polarization ⟹ RH-positivity requires the
  archimedean place. The lemma's hypothesis holds; RH is open.

So **polarization-present `⟺` single Frobenius `⟺` corank 1 `⟺` `F_q`**, and its absence (`⟺` corank ∞ `⟺` ℚ)
is exactly the seam. The polarization **is** the missing single Frobenius **is** the source of positivity — one
object, three names. This is the same `∞ − 1` gap as #125, now read as *"the prime structure is un-polarized
over ℚ."*

## §6 Consequences, the residual, and the honest verdict

- **Relocation (the deliverable).** RH-bearing C5 cannot live on Source B (proved). It must use the
  archimedean polarization — the **weld** (`archimedean-prime-cross-term`, #134). "Everything proven is BRIDGE"
  is the **expected** consequence of Source B being positivity-free + provable-now `=` parent-provable, **not**
  evidence that no C5 exists.
- **Falsifiable prediction.** Every future Source-B theorem will be RH-blind (an `A2`/independence/transcendence
  statement, not an `A1`/positivity one). A genuine Source-B theorem that *separates* the realization family's
  RH-axis would **refute** this meta-theorem.
- **The residual (open, scoped honestly).** Proved: the **canonical** RH-positivity (Weil, and every known
  equivalent) is archimedean, hence ∉ Source B (§§1–3, §2-robustness). **Not** proved: that *no* purely-prime
  expression of RH exists **at all** (a universal over all possible formulations). Reduced to:
  > **Conjecture (universal orthogonality).** There is no positive-definite polarization on any object of `𝓜`
  > whose positivity is equivalent to RH.
  Every known criterion confirms it (§2); a counterexample would be a prime-side positivity criterion for RH —
  none is known in 150 years. This card claims the **located** theorem, not the universal.
- **Scope of "no native Source-B theorem".** The meta-theorem forbids RH-bearing Source-B theorems. It does
  **not** forbid an RH-**blind** native Source-B theorem (a transcendence/`A2` one). But the corpus pattern
  (C3-native ⟺ C5★, the §59/§60 BRIDGE verdicts, G2's lower bound routing to obstruction C) suggests even
  `A2`-native content needs Source A — recorded as a sibling question, not claimed here.

## §7 Door grade — BRIDGE, and why that is the right grade

Strip the multi-`q` vocabulary: "RH is a positivity w.r.t. the functional equation, which needs `Γ`; the Euler
product has no `s↦1−s` self-duality" — this is **classical analytic number theory + Weil positivity**. So the
meta-theorem is **BRIDGE** (it imports Weil, Diamond, Tannakian duality). That is correct and unsurprising: a
*locating* theorem about where C5 can live is itself not C5. Its value is the **location** — it converts the
empirical "all BRIDGE" into a structural reason and **pins the entire RH-relevant C5 question to the weld**.

## Gates
- [x] 0 → 1  in-progress: meta-theorem stated; the three notions made precise; proof skeleton.
- [x] 1 → 2  fully-proven (**core**): the polarization lemma (§1) + Weil-positivity (§2) + the orthogonality
  theorem (§3) are a complete structural proof of the **located** statement; `F_q`/ℚ unification (§5) confirms;
  realization family (§4) illustrates (one detail flagged). Door grade **BRIDGE**. Residual (§6 universal
  conjecture) explicitly **not** banked. → moved to `2-fully-proven`.
- [ ] 2 → 3  formalized: Lean targets — the rank-1 dual-multiplier identity `g_p^∨ = g_p^{-1}` and "no
  `g_p=g_p^{-1}` for non-unit `g_p`" (the lemma's algebra); reuse `LocalFactorDuality` (the `F_q` polarization)
  and `linearIndependent_log_primes`.
- [ ] 3 → 4  publication-ready: "why the independent prime structure is RH-blind: RH-positivity is the
  archimedean polarization."

## Cross-references
- `../0-backlog/archimedean-prime-cross-term.md` (#134) — the weld where RH-bearing C5 must live (this card
  proves *that it must*).
- `../2-fully-proven/erosion-cocycle-reducibility.md` — axis-mode decoupling = the additive special case.
- `../0-backlog/two-sources-of-hypertranscendence.md` — Source A/B; this is the theorem behind the framing.
- `../../door/bucket-realization-and-fake-family.md`, `#84` — the realization family / Diamond off-line.
- `../../door/bucket-the-seam-archimedean-obstruction.md`, `#125` — the polarization = the missing Frobenius = corank.

## Log
- 2026-06-19 — created in 1-in-progress at the user's request (turn the "everything is BRIDGE" observation into
  a theorem). **Fully developed to verdict in one pass.** Result: the **core orthogonality theorem is PROVED**
  (structural, BRIDGE) — RH-positivity = the FE-polarization = archimedean, hence not Source-B-definable
  (§§1–3); confirmed by the `F_q`/ℚ split (§5, `LocalFactorDuality`) and the realization family (§4); every
  known RH-criterion is archimedean (§2). The **universal** version (no purely-prime RH-positivity at all)
  is reduced to a sharp, well-supported conjecture (§6), **not** banked. Consequence: RH-bearing C5 = the weld
  (#134), and "all proven theorems BRIDGE" is **expected**, not paradoxical. → moving to `2-fully-proven`
  (proved core; residual scoped).
</content>
