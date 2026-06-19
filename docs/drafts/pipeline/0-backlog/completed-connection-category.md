# The completed (σ,∂) connection category — execute #91 §3–4 + #90 §7 (the weld "no one has done")

- **ID:** completed-connection-category
- **Stage:** 0-backlog
- **Type:** CONJECTURE / CONSTRUCTION (executes an already-identified target, not a new idea)
- **Priority:** FOUNDATIONAL
- **Source:** ../../door/bucket-archimedean-generator.md; **the construction is already named in the
  corpus** — #91 §3 (the single Tannakian category welding prime + ∞ lanes by the FE, *"the work no one
  has done"*), #91 §4 (the completed flat connection, `FE = flatness`, RH = unitary holonomy), #90 §7
  (`gen(G_L) = D + {σ_p}`), #88 §7 (Connes operator `D = −Σ(log p)∂_{θ_p}`); ../../door/G5-unitarity-gatekeeper.md
  (Face 7, owner), ../../door/G3-holonomy-dichotomy.md; 00-status rows #24, #59
- **Statement (to shape).** Build the **completed** category `𝓜⁺`: the flat prime connection (the
  `{Φ_p=A_pσ_p}` of 𝓜) **plus the ∞-lane as a connection term** — the archimedean generator
  `D = x d/dx = −Σ_p(log p)θ_p` (Connes' scaling operator, #88 §7; the `q→1` limit of the `σ_p`, #90 §1).
  **Conjecture (per #91 §4):** the functional equation `ξ(s)=ξ(1−s)` **is** the integrability/flatness of
  the completed connection, and **RH = unitary holonomy** of that connection on the boundary `Re=½`. Its
  Tannakian group is `G_L⁺` with generator `gen(G_L⁺) = D + {σ_p}` (#90 §7); the weld of the q-difference
  (prime) and shift/difference (∞, Γ, vdPS) categories by the FE **is** `G_L` (#91 §3).

  **This card is execution, not discovery:** #91 explicitly flags the construction as *"the work no one has
  done." The increment is doing it — a precise `(σ,∂)`-Tannakian category, the parameterized Galois group,
  and the FE-as-flatness theorem — with the operator facts (#88/#90) and ledger anchors as inputs.

## Already established (inputs, credit — do NOT re-pose)
- `D = x d/dx` = `−Σ(log p)∂_{θ_p}` = Connes' scaling operator, integer spectrum `{log n}`; `gen(G_L)=D+{σ_p}`
  (#88 §7, #90 §1/§7).
- `D=−i(x d/dx+½)` **essentially self-adjoint**, Berry–Keating Weyl law = Riemann–von Mangoldt count —
  the **MEAN is proved** (#90 §8); `[D,P_{prime-coinv}]=0` = the commutator form of RH (#90 §8).
- The shift `s↦s+1` = diagonal of all prime rescalings = free torus rotation × Γ-weight (#91 §2); ledger
  `primeDiagonal_shift`, `FlatConnection`, `localEulerFactor_q_difference`.
- FE = base-swap `0↔∞` (#90 §64.3) = product formula (#70); Γ = curvature of the diagonal flow (#91 §5).

## The increment (what is genuinely not yet done)
1. **The category axioms.** Make `𝓜⁺` precise: `Φ_p` semilinear over `σ_p`, a `D`-connection `∇_s` with
   `[∇_s,Φ_p]=0`, integrability `F_{pq}=1` **and** the FE-flatness of the ∞-lane. (Pin `[∂_s,σ_p]=0`:
   `σ_p` scales `x_p` by a constant, `θ_p` is scale-invariant — elementary, verify.)
2. **The parameterized Galois group `G_L⁺`.** Neutral-Tannakian structure; `1→G_L→G_L⁺→G_D→1`; locate the
   right framework (Hardouin–Singer differential Galois of difference equations / parameterized PV —
   *recalled, verify the citations*).
3. **FE = flatness, as a theorem** (#91 §4), with RH = unitary holonomy isolated as the open positivity
   (G5, not proved here).

## Door passport
- **Door-2:** `D` is irreducibly cross-prime (`−Σ(log p)θ_p` weights all primes); a theorem essentially
  using `∇_s`/`gen(G_L⁺)` is a NATIVE/C5 candidate — the reason the operator matters. Building the category
  is the BRIDGE prerequisite; the native content is the theorems it makes statable. (#90 §8's `[D,P]=0`
  and the unitary-holonomy statement are the candidate native cores.)
- **Door-5:** over `F_q(C)` no archimedean place ⟹ no `D` ⟹ `ω=0`, completed connection = the bare flat
  prime connection (#90 §5, #88). Required recovery.

## Gates
- [ ] 0 → 1  in-progress: `(σ,∂)`-module axioms (incl. FE-flatness of the ∞-lane) written; `[∂_s,σ_p]=0`
  and `D=−Σ(log p)θ_p` verified; `G_L⁺` exact sequence stated; parameterized-PV literature pinned; the
  already-done inputs (#88/#90/#91 + ledger) cited as inputs, not re-proved
- [ ] 1 → 2  fully-proven: `𝓜⁺` neutral Tannakian + `G_L⁺` constructed; **FE = flatness** proven (#91 §4);
  `F_q` recovery (Door-5); RH = unitary-holonomy isolated as the open G5 positivity (handed off)
- [ ] 2 → 3  formalized: reuse `primeDiagonal_shift`, `FlatConnection`, `BerryKeating`; new fragment =
  the completed-connection flatness ⟺ FE
- [ ] 3 → 4  publication-ready: "the completed difference–differential category and its Galois group"

## Cross-references
- `../../door/bucket-archimedean-generator.md` — parent (consolidation).
- `archimedean-corank-collapse.md` — the corank face (the new bet), depends on this card's `Λ⁺`.
- `weil-positivity-operator.md`, `compute-omega-h2-gl.md`, `hp-not-too-algebraic.md` — the **existing**
  G5/ω/operator cards; this card supplies the *category/connection*, they supply positivity/`ω`/HP.
  **Coordinate; do not duplicate.**
- `../../door/G5-unitarity-gatekeeper.md` (Face 7, #91 §4 owner), `../../door/bucket-time-and-non-holonomic-time.md`
  (D = clock), `../../door/bucket-the-seam-archimedean-obstruction.md` (Γ/ω).

## Log
- 2026-06-19 — created in 0-backlog as the **execution** card for the completed `(σ,∂)` connection that
  #91 §3 calls *"the work no one has done."* Replaces three over-claimed cards (category / completed-Λ-FE /
  Γ-ω) after validating against `support-extraction-log.md`: the operator `D=−Σ(log p)θ_p`, `gen(G_L)=D+{σ_p}`,
  `FE=flatness`, `Γ=ζ-reg det D`, `ω=0⟺RH`, and the essentially-self-adjoint mean are **already mined**
  (#88/#90/#91) and partly ledgered. Increment = actually constructing `𝓜⁺`/`G_L⁺` and proving FE=flatness.
</content>
