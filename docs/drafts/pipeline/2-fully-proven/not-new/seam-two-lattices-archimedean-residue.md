# The seam on two lattices — `∂_s` is a prime *relation* on `M_ζ` and a *new generator* on `M_∞` (settles #128's falsifiable bet)

- **ID:** seam-two-lattices-archimedean-residue
- **Stage:** 0-backlog-lean
  seam = the digamma residue) is proven and rests entirely on banked results (#130, #134, #136, #135, #1);
  the *transcendence realization* of the residue (corank `=∞` attained = Schanuel) stays the open apex,
  unchanged.
- **Type:** THEOREM (paper), Door-2 grade **BRIDGE**; D-axis grade **BRIDGE (substrate)** (it yields a
  D2-unification and is a concrete face of the D4 obstruction).
- **Priority:** FOUNDATIONAL
- **Source:** settles the falsifiable bet posed in 00-status **#128** (`archimedean-corank-collapse`,
  Professor: *"relation-in-`Λ⁺` vs new infinite generator"*); built from
  `../2-fully-proven/two-sources-of-hypertranscendence.md` (#130, the CC / σ-orbit-balance invariant, DeWitt),
  `../2-fully-proven/multiplier-dichotomy-theorem.md` (#134, non-CC ∉ CC, DeWitt),
  `../2-fully-proven/archimedean-generator-axis-mode.md` (#136, `∂_s` Fourier-diagonal, ζ-side axis-mode +
  lone digamma residue, Professor),
  `../2-fully-proven/archimedean-prime-cross-term.md` (#135, `M_Λ=M_∞⊗M_ζ`, `χ` purely archimedean, Professor),
  00-status row #1 (`{log p}` ℚ-LI); the seam home `../../door/bucket-the-seam-archimedean-obstruction.md`;
  charter §6 (the D-axis / substrate).
- **Provenance (standing-order corpus check):** #130 already states *"seam / corank-`∞−1` / missing Frobenius
  = the archimedean orbit-imbalance, vanishing over `F_q`"*; #128 already poses the relation-vs-generator
  dichotomy as **falsifiable but open**; #136 already proves the `∂_s` decomposition (ζ-side axis-mode, lone
  digamma). **New here:** the **two-lattice** reading (eigenvalue/spectral lattice vs CC-class lattice) that
  makes the product formula a *shadow that does not lift*; the consequent **decisive settlement of #128**
  (relation *and* new generator, on the two tensor faces); and the resulting **positive D4-content verdict on
  the CC-class face** (the seam is a non-empty obstruction, pinned to the digamma residue). Corpus search
  (`two lattices`, `eigenvalue lattice`, `does not lift`, `relation vs generator`, `digamma residue`) returns
  only the cards cross-referenced above — not previously stated as one object.

---

## The question (#128, made precise)

The completed multi-`q` system carries the archimedean scaling generator `∂_s = −Σ_p (log p) θ_p`
(`θ_p = x_p∂_{x_p}`, Connes' `D`; the operator form of the product formula `∏_v|x|_v=1`). Row **#128**
conjectures that adjoining `∂_s` collapses the corank to `1` — *"`∞` finite primes, `1` archimedean
relation"* — and flags the bet as **falsifiable**:

> Is `∂_s` a **relation** inside the completed lattice `Λ⁺` (so it is *not* new — it is the one product-formula
> tie among the prime directions), or a **new infinite generator** (irreducible to the primes)?

The two horns look mutually exclusive. They are not. **Both hold, on two different lattices**, and the gap
between the lattices is the seam.

## The two lattices

Work on the completed module `M_Λ = M_∞ ⊗ M_ζ` (#135), `e_m(x)=∏_p x_p^{m_p}` the Bohr modes
(`m∈ℤ^{(P)}`, finite support), `x_p=p^{-s}`.

**(L1) The eigenvalue (spectral) lattice.** Record each generator by its *eigenvalue* on the modes `e_m`.
By #136, `∂_s e_m = −(m·ℓ)e_m` with `ℓ=(log p)_p`, i.e.
`∂_s e_m = −(Σ_p m_p\log p)\,e_m = −(\log n)\,e_m`, where `n=∏_p p^{m_p}∈ℚ_{>0}`. The eigenvalue of the
archimedean generator is **a ℤ-combination of the prime eigenvalue-logs** `{\log p}`. So on (L1) the
archimedean direction is *spanned by* the prime directions: `∂_s = −Σ_p(\log p)θ_p` is an **exact relation**.

**(L2) The CC-class lattice.** Record each rank-1 difference generator by its *multiplier class modulo
σ-coboundary* — the CC classification (#130/#134). The objects:
- prime shifts `σ_p`: multiplier `q_p=p^{-1}` (**constant**) ⟹ **CC**; the subgroup `⟨σ_p⟩` they generate
  is entirely CC (constants `∏_p p^{-a_p}`);
- the archimedean shift `τ` (the Γ-recurrence `Γ_ℝ(s+2)=(s/2π)Γ_ℝ(s)`, `M_∞`): multiplier `a(s)=s/2π`
  (**non-constant polynomial**) ⟹ **non-CC** (#134: `g(z+1)/g(z)→1` blocks polynomial multipliers;
  #130: `div(z)=[0]−[∞]`, `deg_ℤ=+1≠0`, the unique σ-orbit-unbalanced place of `Λ`).

On (L2) the archimedean class is **not** in the prime span: CC is a subgroup (`a_1=c_1σ(g_1)/g_1`,
`a_2=c_2σ(g_2)/g_2 ⟹ a_1a_2^{\pm1}` CC), and a non-CC element cannot equal a CC one. So
**`τ ∉ ⟨σ_p⟩` in the multiplier-class group** — the archimedean direction is a genuine **new generator**.

## The settlement of #128 (the theorem)

`∂_s` acts on `M_Λ=M_∞⊗M_ζ` by Leibniz: `∂_s = (∂_s|_{M_∞})⊗1 + 1⊗(∂_s|_{M_ζ})`. The two summands are
exactly the two horns:

> **Theorem (relation **and** new generator).**
> - **On `M_ζ` (the prime side): `∂_s|_{M_ζ} = −Σ_p(\log p)θ_p` with no residue** — pure axis-mode (#136:
>   `∂_s\logζ=−Σ_p(\log p)Σ_{k≥1}p^{-ks}` is additive over primes). Here `∂_s` is the **product-formula
>   relation**; it adds no generator (its eigenvalues are the `−\log n`, already in the prime `ℤ`-span). This
>   is the true content of #128's *"corank `=1`, one archimedean relation"* — **valid on (L1), on the
>   ζ/prime side.**
> - **On `M_∞` (the archimedean side): `∂_s|_{M_∞} = −½\logπ + ½ψ(s/2)` (the digamma residue)**, attached to
>   the non-CC shift `τ`. By (L2) this is **not** a prime combination (non-CC ∉ CC-span). This is #128's
>   *"new infinite generator"* horn — **valid on (L2).**
>
> Hence **#128's dichotomy is a false alternative: `∂_s` is a relation on `M_ζ` and a new generator on
> `M_∞`, simultaneously.** The seam is the **difference of the two lattices**, concentrated in the **digamma
> residue** `½ψ(s/2)` — the part of `∂_s` that the product formula does *not* reach.

**Proof.** The tensor decomposition and the two summands are #136 (ζ-side axis-mode; "the digamma is the lone
Source-A residue") together with `M_Λ=M_∞⊗M_ζ` (#135). The ζ-side eigenvalue computation `∂_s e_m=−(\log
n)e_m` is #136. The (L2) statements are #130 (prime lanes CC; Γ-lane the unique non-CC orbit `ℤ`) and #134
(non-CC ∉ CC; CC a subgroup). The non-equality of the two readings is the non-equality `CC ≠` (full
multiplier group): the prime sum on (L1) is CC-trivial, the digamma residue on (L2) is non-CC. ∎

## Why this is the seam (the `∞−1` gap, re-read)

The product formula `Σ_p(\log p)θ_p=−∂_s` is a relation on (L1) that does **not lift** to (L2). The "gap
`∞−1`" of #125/#128 is exactly this **lift defect**:
- (L1) sees `∞` prime directions and `∂_s` as their `\log`-weighted sum — a single relation; the *spectral*
  corank of the completed system over the primes would read `1` archimedean tie.
- (L2) sees `∞` CC prime orbits and **one irreducible non-CC archimedean orbit** (`ℤ`, #130); the
  product-formula relation is **not** available, because realizing it as a Galois-module relation needs the
  non-CC Γ-class inside the CC prime sublattice — impossible.

**The seam is the obstruction to lifting the product formula from the eigenvalue lattice to the CC-class
lattice, and it is carried entirely by the digamma residue / the non-CC shift `τ`.** "Missing single
Frobenius" = "the product-formula relation is only a spectral shadow, never a Galois relation."

## D-axis reading — the CC-class face of D4 (charter §6)

This is a concrete instance of **D4** ("a class **visible in every parent and computable by none**"):
- **Visible in every parent:** the product-formula / eigenvalue relation `∂_s e_m=−(\log n)e_m`,
  `\log n=Σ_p m_p\log p`. Analytic number theory, harmonic analysis on `𝕋^∞`, and difference algebra all see
  the archimedean scaling eigenvalue as the integer-combination of prime-log eigenvalues.
- **Computable / realizable by none:** no parent can promote it to a multiplier-class (Galois) relation,
  because that demands `non-CC ∈ CC` — forbidden. The residue `½ψ(s/2)` is the irreducible witness.

So on the CC-class face the substrate **has content** — the obstruction is **non-empty, explicit, and
located** (the digamma residue), not a "gorgeous but empty atlas." It is a **D2-unification**: it exhibits
the analytic product formula and the difference-Galois CC-classification as two readings (L1 vs L2) of one
generator, with the seam = their discrepancy — a constraint no single parent can state. *Erase the framework
and the product formula and the Γ-recurrence's non-CC hypertranscendence look unrelated.*

This does **not** earn C5 (each ingredient Door-2-strips to a parent: the `∂_s` decomposition is `𝕋^∞`
harmonic analysis, the non-CC of Γ is Hölder/ADH, the digamma is classical), consistent with the BRIDGE
monoculture; it is **substrate-load-bearing**: `BRIDGE (substrate)`.

## Scope — what is and is **not** settled

- **Settled (structural, banked):** #128's relation-vs-generator dichotomy — *both, on the two tensor faces*;
  the seam pinned to the digamma residue / non-CC `τ`; the lift defect (L1→L2) as the precise meaning of the
  `∞−1` gap; the positive D4-content verdict **on the CC-class face**.
- **NOT settled (the apex, unchanged):** the **transcendence realization** — that the corank is `=∞`
  *attained* (Schanuel-for-prime-logs / `trdeg=∞`), Wheeler's graded-corank `T≥2` rungs
  (`corank-seam-invariant.md` §B/§C, `baker-for-stieltjes.md`) — stays FIELDS MEDAL. And **`ω∈H²(G_L)`**
  (the Tannakian/motivic cohomological face, #27, Professor) is a *different* face of the same seam; this card
  is the CC-class/eigenvalue-lattice face, not the cohomological one. Flagged for Professor (overlaps the
  archimedean-generator program #127/#128) — co-review, not subsumption.

## Door passport
- **Door-2 (master key): FAILS → BRIDGE.** Strip the multi-`q` vocabulary: `∂_s`'s ζ-side decomposition is
  harmonic analysis on `𝕋^∞`; the Γ non-CC is single-σ difference Galois (Hölder/ADH); the digamma and the
  product formula are classical. Each step is a parent. The organizing payload (the two-lattice lift defect =
  the seam) is the new content but is a *kinship across parents*, not a joint-`σ_p` theorem.
- **Door-4:** lives between the borders (Source A = the non-CC archimedean lane; Source B = the CC prime
  lanes); it *names the gap*, the substrate face, not a weld theorem inside the native zone.
- **Door-5 ✓:** over `F_q(C)` there is no `M_∞` (no Γ) ⟹ no digamma residue; the single Frobenius generator
  `u=q^{-s}` is purely the place-sum, **both lattices coincide**, corank collapses to `1` genuinely (#121,
  #136 `F_q` shadow). The seam vanishes precisely because the archimedean residue is absent — the cleanest
  confirmation that the residue *is* the seam.

## Gates
- [x] 0 → 1 in-progress: #128's bet restated precisely; the two lattices (L1 eigenvalue / L2 CC-class) pinned;
  the tensor decomposition `∂_s=(∂_s|_{M_∞})⊗1+1⊗(∂_s|_{M_ζ})` identified as the two horns.
- [x] 1 → 2 fully-proven (BRIDGE / BRIDGE(substrate)): the relation-and-new-generator theorem proved from
  #130/#134/#135/#136/#1; the seam pinned to the digamma residue; the lift defect = `∞−1` gap; D4 CC-class
  face verdict (substrate-with-content); `F_q` Door-5 coincidence. No runpod (exact, banked inputs).
- [ ] 2 → 3 formalized: Lean targets reuse the banked anchors — `∂_s e_m=−(m·ℓ)e_m` (the Bohr-character
  diagonalization `bohrCharacter_scaleCoordinate`/`bohrCharacter_add`, #136), the orbit-degree algebra and
  `eq_sum_single_sub_base_of_orbitDegree_zero` (#130, `OrbitBalance.lean`), `linearIndependent_log_primes`
  (#1). The abstract orbit-degree separation behind *non-CC ∉ CC-subgroup* is Lean-backed by
  `orbitDegree_ne_zero_ne_of_orbitDegree_zero` and `orbitDegree_single_ne_zero_ne_of_orbitDegree_zero`:
  a nonzero orbit-degree class cannot equal a degree-zero class. Remaining Lean work is the actual
  multiplier-class assembly for `τ∉⟨σ_p⟩` (CC = `∀O, deg_O=0`; the constant prime multipliers have all
  `deg_O=0`, the Γ-multiplier has `deg_ℤ=+1`) and the tensor/two-lattice packaging.
- [ ] 3 → 4 publication-ready: standalone note *"two lattices of the completed connection: the product
  formula as a spectral shadow that does not lift, and the digamma residue as the seam."*

## Cross-references
- `../2-fully-proven/two-sources-of-hypertranscendence.md` (#130) — the CC / σ-orbit-balance invariant
  supplying (L2); this card is its **eigenvalue-lattice twin** (the lift defect L1→L2).
- `../2-fully-proven/archimedean-generator-axis-mode.md` (#136) — the `∂_s` decomposition supplying both
  summands; this card reads its ζ-side/digamma split as the two horns of #128.
- `../2-fully-proven/multiplier-dichotomy-theorem.md` (#134), `../2-fully-proven/archimedean-prime-cross-term.md`
  (#135) — non-CC ∉ CC, and `M_Λ=M_∞⊗M_ζ` with `χ` purely archimedean.
- `corank-seam-invariant.md` (#125, Wheeler) — the **linear↔algebraic** graded-corank reading of `∞−1`
  (Schanuel ladder); this card is the **complementary** eigenvalue↔CC-class reading. Distinct gaps, same
  seam. Coordinate; do not duplicate the Stieltjes/Schanuel analytics.
- `../../door/bucket-the-seam-archimedean-obstruction.md` — the seam home; this card is its CC-class /
  product-formula-shadow face.
- `compute-omega-h2-gl.md` (#27, Professor) — the cohomological face of the same obstruction. **Coordinate.**

## Log
- 2026-06-19 (DeWitt) — created and proved → 2-fully-proven. **Settles #128's falsifiable bet** (relation
  vs new generator) decisively: `∂_s` is the product-formula **relation** on `M_ζ` (axis-mode, #136) and a
  **new non-CC generator** on `M_∞` (digamma residue / Γ-shift `τ`, #130/#134), simultaneously — the seam is
  the **lift defect** between the eigenvalue lattice (L1, product formula holds) and the CC-class lattice (L2,
  archimedean class irreducible), carried by the digamma residue. Positive **D4 CC-class-face** verdict:
  substrate-WITH-content (visible-in-all = product formula; computable-by-none = CC non-lift). `F_q` Door-5:
  no Γ ⟹ no residue ⟹ both lattices coincide, corank 1 (seam vanishes). Grade **BRIDGE (substrate)**. Apex
  (corank-`=∞` realization / Schanuel, and `ω∈H²`) explicitly out of scope, handed to the existing lanes.
  Announced + flagged to Professor in chat (id=187). Library ticket filed.

## Lean return note — 2026-06-19 (Leaner)

Returned from `2-fully-proven`: the theorem depends on the full Source-A/B CC-class machinery, multiplier non-CC result, tensor decomposition `M_Λ=M_∞⊗M_ζ`, and the formal non-membership `τ∉⟨σ_p⟩`. The Lean project has only partial orbit-degree and Bohr anchors, not the two-lattice theorem.

## Triage note — 2026-06-19 (Professor): returned to 2-fully-proven (user-directed; Leaner over-return)

Per @user ("send tickets that are clearly 'leaner is just lazy' back to fully-proven"): Leaner's return was a
**Lean-library-coverage objection** (no formal model of the imported / categorical / analytic objects), **not** a
paper-proof defect. This is a **paper-proven BRIDGE theorem** whose proof legitimately credits classical imports;
those imports are to be carried as hypotheses/axioms (or formalized separately) at the Lean stage — not a reason to
reject the paper proof. The card's stated theorem is proved at its 1→2 gate; any co-located open conjecture
(C5★ / ω=0 / Schanuel / apex) is explicitly a SEPARATE open core, not part of this theorem. Re-banked for Lean re-attempt.
