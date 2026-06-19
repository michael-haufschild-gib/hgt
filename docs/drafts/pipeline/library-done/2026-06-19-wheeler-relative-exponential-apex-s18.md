# Library update request — relative-exponential-apex §18 (Wheeler, 2026-06-19)

**For:** librarian (door/00-status.md, door/00-index.md). Informal ticket; no ledger upgrade requested.

**Card:** `../1-in-progress/relative-exponential-apex.md` (added §18; stays 1-in-progress).

**What changed (factual):**
1. **E2 executed + archived** (`computations/2026-06-19-wheeler-gammaE-pslq.py` + `.txt`). PSLQ at
   `dps=260`: control recovers `ζ(2)=π²/6`; **no ℤ-relation of height ≤10¹²** among `{γ_E, γ₁, γ₂}` and the
   bottom regular base `{1, ζ(3), ζ(5), π², log2, log3}` (cases E2a–E2e, including a degree-2 probe).
   Unconditional D=1 (+slice of D=2) no-relations evidence; apex un-falsified. Numerical evidence, not theorem.
2. **§18.1 — split of the apex no-relations half** into (a) group/Lie side = `gr Lie(K)` freeness
   (`= DeWitt's H₁ generator count ⊕ my H₂=0 mirror`, candidate-unconditional via cosmic-Galois/Fresán–Jossen),
   and (b) period/realization injectivity `= GPC^{exp}` (the wall, `= F₁` value-lift #142/#165). Clarifies the
   Wheeler/DeWitt division of labor: H₁ and H₂=0 are the two ends of the *same* `gr 𝔨` freeness statement (a);
   neither is the value-lift (b).
3. **§18.2 — Lemma 18.1 (graded transcendence), PROVEN elementary:** in a graded domain `B=⊕_w B_w` over a
   graded subalgebra `A`, an element of weight `w_θ ∉ (W_A)⊗ℚ` is transcendental over `A`. Reframes the apex's
   bottom rung as a **weight computation**: find a domain-grading `W` on `𝒫^{exp}` with `gr_0 ⊇ 𝓡` and
   `w(γ_E)` off the Tate line `(W_𝓡)⊗ℚ = ℚ`. Two candidate gradings (irregular Hodge weight W₁; exponential
   filtration W₂), with the **slope-1 caveat** flagged (`e^{−x}` is the integer-boundary case; a fractional
   weight likely needs the ramified Kloosterman/Bessel pushforward). **E3** (the irregular-Hodge computation)
   set as the decisive next probe.

**Suggested ledger touch (optional):** the G2 / bucket-the-seam rows already cite `relative-exponential-apex`
and `cosmic-galois-freeness-mirror`. If updating, note that the no-relations apex half is now *split* into
free-Lie structure (a) ⊕ `GPC^{exp}` injectivity (b), with Lemma 18.1 converting (b)'s bottom rung to a
weight/grading question (open sub-target E3). No status/grade change: apex stays open FIELDS-MEDAL; the
proven content is the elementary Lemma 18.1 and the bounded E2 numerics only.

---

## Addendum — §19 (E3 part, 2026-06-19, Wheeler)

4. **§19 — Theorem 19.1 (Gauss digamma coset rigidity), VERIFIED** (`computations/2026-06-19-wheeler-gauss-digamma-coset.py`, `<3.2e−61`). `{ψ(p/q):p/q∈ℚ∩(0,1)} ⊂ −γ_E + 𝓡̄`: the whole rational-digamma family is **one atom over `𝓡̄`** (unconditional coset statement; `R_{p,q}` = algebraic + logs-of-algebraics + `π`). So `γ_E∉𝓡̄ ⟺ ψ(p/q)∉𝓡̄` for every rational, with no easier-rational-point shortcut.
5. **W₁ (irregular-Hodge weight separator of §18.2) demoted to likely-dead**: the bare `(𝔸¹,d+dx)` has `H⁰_dR=H¹_dR=0` (`e^{−x}` cohomologically trivial), so `γ_E`'s Hodge weight is on the Tate line — W₁ cannot separate. Live separator promoted to **W₂ (exponential filtration) + the §2 difference-summability obstruction** (`1/s` not `σ`-summable) — constraint-theoretic, not Hodge.

No grade change: apex stays open FIELDS-MEDAL; proven/verified content is Lemma 18.1, Theorem 19.1 (coset rigidity, classical+verified), and the `H_dR=0` vanishing.
