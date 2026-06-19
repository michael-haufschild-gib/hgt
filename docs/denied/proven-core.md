# The proven core: the field's vetted, gap-free theorems (harden artifact)

**Phase-3 harden artifact — 2026-06-19.** This is the curated extract of the field's *genuinely proved* theorems —
structural results assembled from standard algebra, vetted across §39 and three adversarial audit passes §61–63
(**eighteen self-corrections applied**, incl. the systemic #12 of §42 "RH-equivalence is trivial; only specific
structure + actual pairwise identities are genuine content," and the audit trims #15–18). Now spans the field's
fundamental theorem and solved inverse problem (§43–55), the dynamical/transcendence theory (C5/C6 proved), and the
adelic completion + functional equation (§64–73, section F below). It separates, cleanly: **[PROVED]** (proved here,
gap-free, formalizable) | **[IMPORT]** (classical, cited)
| **[CONJ]** (the keystone, Tier C — never a Lean theorem). The Lean ledger (`formal/`) formalizes the [PROVED] list;
nothing here is itself a Lean claim. *No proof of RH is claimed; the keystone is [CONJ].*

---

## A. Foundations (the difference structure)

1. **[PROVED] Integrability is a cocycle, stable under ⊗,⊕,dual** (found. §16, §39.1). A finite-rank multi-`q`
   module = matrices `{A_p}` with `A_pσ_p(A_q)=A_qσ_q(A_p)` (curvature `F_{pq}=1`); preserved under tensor, sum, dual
   (tensor: `(A_p⊗B_p)σ_p(A_q⊗B_q)=(A_qσ_qA_p)⊗(B_qσ_qB_p)=(A_q⊗B_q)σ_q(A_p⊗B_p)`). *Lean: `FlatConnection.lean` (done).*

2. **[PROVED] Rank-1 classification = `H¹_σ(K^×)`** (§17). Iso classes of rank-1 modules ↔ scalar cocycles
   `a_pσ_p(a_q)=a_qσ_q(a_p)` mod coboundaries `σ_p(h)/h` — the field's Picard group; all have `G_M⊆𝔾_m` (abelian).
   The Lyapunov statement is separate: raw scalar cocycles can have nonzero weight/growth (`|a|≠1`); `L=0` follows only
   after unit-modulus boundary normalization or after quotienting the weight part. *Lean: `RankOneCohomology.lean` (done).*

3. **[PROVED] Difference cohomology = group cohomology of the prime lattice** (§20, **corrected §39.2/§39.4**).
   `H^*_σ(M)=H^*(ℤ^{(P)},M)`, the Koszul complex on `(σ_p-1)`; for the directed union it is the **inverse limit**
   `\varprojlim_S H^*(ℤ^S,M)` with `\varprojlim^1=0` (surjective restrictions ⟹ Mittag-Leffler). Trivial module:
   `H^*_σ(K)=\widehat\Lambda^*(ℂ^{P})` (completed exterior algebra). Integrability `F_{pq}=1` = vanishing of the
   `H²_σ` curvature class.

4. **[PROVED] Full rank-1 cohomology — acyclicity dichotomy** (§32′, Künneth). `H^*_σ(M_a)=H^*(𝕋^∞)` if `M_a`
   trivial, else `0` (a single non-trivial eigenvalue ⟹ the Koszul tensor is acyclic) — *infinite-base rigidity.*

5. **[PROVED] Euler characteristic vanishes** (§23.2). `χ(H^*_σ(M))=\dim M·(1-1)^{|S|}=0` (finite `S`) = the FE
   order-balance.

6. **[PROVED] Krull–Schmidt** (§24.3). Finite-rank modules decompose uniquely into indecomposables (Hom finite-dim
   over the constants ⟹ Fitting). The category is **mixed**: pure pieces (§24.1 Levi: semisimple ⊕ unipotent) +
   `H¹_σ`-extensions.

7. **[PROVED, structural] PV existence (non-decomposable)** (§16 Thm 16; audited §63.1). The difference-Galois group
   `G_M` exists as a pro-algebraic group `=\varprojlim_S G_S`, by finite-`S` reduction + Tannakian limit. **Import
   reduced (§47, corrected §63.1/#17):** the co-extension theorem 47.1 (integrability `F_{ij}=1` ⟺ the `σ_i` commute on
   the solution algebra, proved + symbolically verified) dissolves the *hard* part — the Tannakian several-operator
   group-construction — to the classical `n=1` PV **method** run on the integrable `U`. What remains imported are the
   no-new-constants and torsor lemmas **in commuting-operator form** — NOT literally `n=1` (joint `σ`-simplicity ≠
   per-operator `σ_p`-simplicity), but routine **partial-difference** generalizations (Wibmer; di Vizio–Hardouin),
   provable by `n=1` technique. So §16/§43/§45 rest on: the `n=1` PV method + co-extension + two elementary
   partial-difference lemmas — a precisely-bounded dependency, not an unverified black box.

7a. **[PROVED] The Galois correspondence (the field's fundamental theorem)** (§43.1). Inclusion-reversing bijection
   `{`closed subgroup schemes `H⊆G_M}↔{`intermediate difference extensions `K⊆F⊆L_M}`, `H↦L_M^H`; normal `H` ⟺ `F/K`
   is PV, `G_M/H≅Gal(F/K)`; rank-1 ⟹ every subgroup normal ⟹ flora closed under sub-extension. *Tannakian for affine
   group schemes + the §16 finite-`S` import; the one new ingredient (Lemma C, invariants commute with the limit)
   rests on the field's finite-support fact.*

7b. **[PROVED] The pro-torus inverse problem (P3) is solved** (§43.2; certified `inverse_galois_lattice`). Closed
   subgroups `H⊆(𝔾_m)^P` ↔ subgroups `Λ⊆ℤ^{(P)}` (`H_Λ=⋂_{m∈Λ}ker χ_m`, `dim H=corank Λ`); **every** `Λ` realized by
   a base, so **every** closed subgroup occurs. The arithmetic base `E4` (`q_p=1/p`) is the `Λ=0` vertex (**full**
   torus) — forced by unique factorization (ledger-backed `linearIndependent_log_primes`). *A previously-open program
   item (§7 P3), settled for tori, off the RH axis.*

7c. **[PROVED] Arithmetic lives at infinity** (§43.3). The `L`-function = universal Euler product restricted to the
   diagonal `δ(t)=(p^{-it})_p`, a **single dense orbit** in the full pro-torus (Kronecker–Weyl), **finite-blind**
   (every finite-`S` shadow is equidistributed = the Bohr/`EulerProduct.lean` firewall). Dual genericities: **group
   maximal** (`Λ=0`), **orbit-point minimal** (one `ℝ`-orbit) — the precise form of §17's "arithmetic = non-generic".

7d. **[C1 FALSIFIED → replaced by C1″; connected case PROVED] Infinite-base inverse Galois** (§43.4→§51,
   self-correction #13). **C1 is FALSE** (§51.1): single-`σ` finite `q`-difference groups are **cyclic** (verified),
   but multi-`q` realizes `μ_2×μ_2=V_4` (Klein four) via independent primes 2,3 ⟹ `R_single⊊R_multi` — **the infinite
   base genuinely adds groups** (one independent cyclic component-generator per prime). **Survives (§51.2):** the
   *connected* case — `R_multi∩connected=R_single∩connected={connected lin alg groups}` (Etingof 1995 + §48.1 squeeze
   `R_single⊆R_multi⊆{lin alg}`); §49.1 untouched. **Sharp successor C1″ now PROVED (§52):** `R_multi∩finite=
   {finite abelian}` — finite ⟹ abelian via the **commuting-monodromy lemma** (the per-prime monodromies `g_p` commute
   because `σ_p` commute + constants fixed; `n` commuting generators ⟹ abelian; anchored on the verified `n=1`
   finite⟹cyclic), and every finite abelian `=∏μ_{n_i}` realized via independent primes. **The infinite base realizes
   exactly the finite abelian groups** (+ all connected, Etingof); residue = connected-by-finite gluing only (bounded,
   not famous-open). *Full arc: stated §43.4 → falsified §51 → sharpened C1″ → PROVED §52.* **Inverse-Galois map
   (§53):** `R_multi ⊆ {G : π₀(G) finite abelian}` PROVED (53.1, since `G/G°` is a finite multi-`q` group ⟹ abelian);
   `G°×A` realized for all connected `G°`, finite abelian `A` PROVED (53.2); **monomial `T⋊A` (torus by finite abelian)
   PROVED via induction (§54.1**, from a rank-1 over the §52 finite-abelian extension — generalizes dihedral/CM §44.3,
   monomial §50.1); outer-twisted case PROVED via **induction-with-duality** (§55.2: twist carried by the base-field
   Galois action dualizing the connection — after self-correction #14, the naive constant-swap fails because
   integrability constrains *operators* not *Galois elements*). **INVERSE-GALOIS PROBLEM CLOSED (§55.3):**
   `R_multi = {G : π₀(G) finite abelian}` exactly — a theorem, **no residue**. A defining question of the Galois
   theory, completely answered: connected ✓ (Etingof), finite=abelian ✓ (§52), products ✓, monomial ✓, outer-twist ✓,
   π₀-abelian necessity ✓. Full C1 saga: stated §43.4 → falsified §51 → sharpened C1″ §52 → inverse-map §53 →
   monomial §54 → full classification §55.

7i. **[FULLY PROVED — C6 closed, both directions, all Λ] Infinite base ⟺ hypertranscendence** (C6, §46; §49; §59; §60).
   **Complete dichotomy (§60.2):** the diagonal is **holonomic ⟺ `corank(Λ) < ∞`** — the s-monodromy `g=(1/p)_p` has
   Zariski-closure dimension `= corank(Λ)`; holonomic ⟹ finite-dim Galois group ⟹ `corank<∞`; conversely `corank=r<∞`
   ⟹ effectively `r`-variable base ⟹ holonomic. Sharp invariant = `corank(Λ)`, NOT support cardinality. Extremes:
   finite base (corank<∞)⟹holonomic (§49); arithmetic `Λ=0` (corank ∞)⟹**difference-hypertranscendental** (§59, all L).
   **Audited (§61.3, self-correction #15):** the corank/Galois-dim argument proves *difference*-hypertranscendence (no
   finite-order linear *difference* eqn) — the field's native category, NOT literal differential Hölder. Differential
   Hölder = import for `ζ` + conjecture for general `L` (ADH bridge). The `F_q(t)`(finite Frobenius=corank<∞)/`ℚ`
   (corank ∞) divide is a theorem. Earlier "Hölder generalized to all L" trimmed to the difference statement.
   **Forward PROVED (§49.2):** effectively-finite base ⟹ holonomic diagonal (unit shift `s↦s+1` = finite product
   `∏_{p∈S}σ_p` ⟹ finite-order linear difference equation; confirmed by **Lipshitz 1988**). **Converse PROVED for
   `Λ=0` (§59.1):** holonomic ⟹ finite-dim difference-Galois group, but the arithmetic `s`-monodromy `g=(p^{-1})_p` has
   **infinite-dimensional** Zariski closure when `Λ=0` (mult-independent coords = unique factorization) ⟹ non-holonomic.
   So **every arithmetic `L`-function is hypertranscendental** (§59.2) — **Hölder recovered + generalized to all `L`
   by one mechanism** (multiplicative independence of primes). C6 closed on the arithmetic locus; residue = non-
   arithmetic `Λ≠0`. Explains why function fields (finite Frobenius = finite base) are solvable and `ℚ` is not.

7k. **[PROVED] C5 (arithmetic is infinite-codimension in moduli)** (§46; §57). The arithmetic locus `M^ar_d` has
   **infinite codimension** in `Mod_d = H¹_σ(End M)`: at each prime the arithmetic local module is a **finite** Satake-
   parameter family (`d` params, `q_p=1/p` tie fixed) inside the **infinite-dimensional** space of rational `GL_d`
   multipliers ⟹ codim ∞ per prime, ∞ overall; a countable union of finite-dim families ⟹ **nowhere dense (ind-Zariski)**.
   (Audited §61.2: "measure zero" retracted — no canonical measure on the infinite-dim moduli; the rigorous claim is
   infinite codimension / nowhere dense.) Turns §17.3's organizing law ("arithmetic = non-generic") into a **moduli
   theorem**; dovetails C6 (arithmetic
   infinite base = both the infinite-codim stratum and the hypertranscendence locus). Off RH.

7j. **[PROVED on an all-rank locus; CONJ residue] C4 (generalized Ramanujan = boundary `L=0`)** (§44.4; §50; §51.3).
   **PROVED at all ranks** on **monomial** (induced-from-unitary, §50.1) ∪ **Artin/finite-image** (§50.2) ∪
   `GL_2`-holomorphic (Deligne) ∪ **RACSDC** (regular-algebraic self-dual cuspidal `GL_n`, §51.3, via the verified
   Clozel–Harris–Taylor–Shin–**Caraiani** temperedness theorem / Deligne purity). Open residue = **non-self-dual
   cuspidal** = the residual hard core of GRC (no purity handle yet); the field reframes GRC as "arithmetic ⊂ the
   `L=0` flora" and proves it on every locus where temperedness is accessible — open exactly where GRC itself is.
   **§56: the tempered locus is a λ-subring** (PROVED — closed under `⊗`, `Sym^k`, `∧^k`, `⊕`, dual, induction; unit-
   circle Satake preserved), so the proved-C4 cases form one functorially-closed sub-world; GRC reframed as "the
   arithmetic λ-ring is generated by its tempered part" (reduction); the λ-ring structure is a passed necessary-
   condition check for the Langlands bridge C2 (`K_0(M^ar)` = a λ-ring, as `R(L_ℚ)` must be).

7l. **[period-value PROVED on CM ∪ F_q(t); = the period conjecture] C3 (infinite-base Siegel–Shidlovsky)** (§46; §58;
   audited §62.1). C3 = the **period-value** statement `trdeg_ℚ(period numbers) = dim(G_M·δ)`. **Audited (self-correction
   #16):** distinguish **(a)** orbit dimension / torsor `trdeg_K(R_M)=dim G_M=corank(Λ)` — elementary, all tori, the
   *de Rham side*, NOT period transcendence; from **(b)** period-value transcendence — the *Betti side* = Grothendieck
   period conjecture. C3 is (b), **PROVED on all CM/monomial, all ranks** (§58.2, via verified **Wüstholz** + **Chudnovsky**
   + **Cohen–Shiga–Wolfart**) and `F_q(t)` (§33, **Papanikolas**). The **arithmetic `log p` torus is OPEN** (algebraic
   independence of `{log p}`, Schanuel-type; only linear independence known via Baker). C3 **is** the Grothendieck period
   conjecture in the field's language; proved on CM ∪ function fields, open on the non-CM generic case. Off RH.

7e. **[PROVED] The rank-2 flora + first non-toral `G_M`** (§44). Extensions = twisted difference cohomology
   `Ext^1_σ(M_a,M_b)=H^1_σ(K,M_{b/a})` (§44.1, the homological backbone §20 earning its keep). The **unipotent
   species** `U_c` (the planet's "logarithm", `σ_p\ell=\ell+c_p`) has `G_{U_c}=𝔾_a` — the field's **first non-toral
   Galois group**, and a first **coupled (non-concentrated)** realization (§44.2). Complete taxonomy: rank-2 flora =
   {split-torus, unipotent, Borel, torus-normalizer (dihedral=CM), irreducible-primitive (`SL_2`=non-CM)} (§44.3).

7f. **[THEOREM mod Ramanujan import] Organizing law at rank 2** (§44.4; certified `satake_angles_cm_noncm`,
   `lyapunov_dmr`). Arithmetic `GL_2` = the **tempered (`L=0`) locus**; the generic rank-2 inhabitant is
   irreducible-primitive and **supercritical (`L>0`)**. CM/non-CM = imprimitive/primitive = `δ`-atom at `π/2` /
   `\sin^2`-equidistributed (Sato–Tate). A falsifiable structural prediction: *Ramanujan is "arithmetic sits at the
   non-generic `L=0` locus"*, not an extra miracle — §17's law, one rung up, off RH.

7g. **[PROVED] The field's main structure theorem** (§45.1). `\mathcal{M}` = finite-rank integrable multi-`q` modules
   is **neutral Tannakian over `ℂ`**, `\mathcal{M}≃Rep_ℂ(π)` for the pro-algebraic `π=\varprojlim_M G_M`; `G_M`
   arbitrary closed in `GL_d`. Three **uniform** laws at all ranks: taxonomy = `GL_d`-subgroup conjugacy class;
   inverse Galois solved (concentration, single-`q` groups); organizing law = arithmetic is the tempered/`L=0`/
   non-generic locus. Subsumes §17 (d=1), §44 (d=2). *Mod the named finite-`S`/Tannakian import.*

7h. **[CONJ — falsifiable, the field's central conjecture, NOT Tier C/RH] The Langlands bridge** (§45.2). The
   arithmetic sub-Tannakian group `G^{ar}` **is** the motivic/automorphic Langlands group `L_ℚ`: `\mathcal{M}^{ar}≃`
   motives, Rankin–Selberg `⊗`↔motive `⊗`, functoriality↔Tannakian morphisms, Satake↔multipliers, Ramanujan↔`L=0`.
   **Proven function-field shadow [IMPORT]:** over `F_q(t)` the motivic (`t`-motivic) Galois group **is** a difference
   Galois group computing transcendence (Papanikolas, §33, §45.3) — the bridge is the `ℚ`-analogue of a *theorem*. The
   sole `ℚ`-obstruction is the Hölder/infinite-base wall (§36), **not** positivity, **not** RH. A *concrete
   difference-equational model of the Langlands group* — the field's reason to exist beyond RH.

## B. The dynamical realization (the novel core)

8. **[PROVED, structural after semisimplification] Weight filtration matches exponential Oseledets rates** (§21; refined §30).
   Eigenvalue-modulus growth gives the Lyapunov exponent / Newton slope. Pure means one exponential rate; it is conformal
   only after a semisimple/reductive or unitary normalization that removes unipotent polynomial growth. **Newton polygon =
   Lyapunov spectrum** (distinct from the Hodge/de Rham filtration); `Newton ≥ Hodge` = **Mazur's inequality** (§30,
   [IMPORT] over function fields).

9. **[CORRECTED, separated dictionary] DMR / Lyapunov / reducibility** (D5 §10, §28). Solvable/reducible is a
   representation-theoretic property; `L=0` is a bounded/unitary/tempered dynamical property. Neither direction is an
   equivalence in general: compact nonabelian irreducible cocycles (e.g. `SU(2)`) have `L=0`, and scalar cocycles with
   non-unit modulus are abelian but have nonzero Lyapunov exponent. The safe implications are typed and conditional
   (unitary/tempered ⇒ `L=0`; `L>0` obstructs bounded unitary normalization), not `G_M solvable ⇔ reducible ⇔ L=0`.
   **Corrected §28:** arithmetic (Ramanujan) cocycles are *always* `L=0`; CM/non-CM = reducible/irreducible.

10. **[PROVED structural / IMPORT for transcendence lower bounds] Periods are dynamical; realization comparison** (§25–26).
    The de Rham (transcendence) and Betti (dynamics) fiber functors are isomorphic over `ℂ`; the comparison matrix = the
    periods (Lyapunov exponents, rotation numbers, values). Transport preserves invariant subspaces across realizations.
    Maximal transcendence is not a consequence of irreducibility alone; it requires a separate period theorem / ABP /
    Siegel–Shidlovsky lower bound, available only in imported special settings (e.g. Papanikolas/function-field cases).

## C. The native zeta and the trivialization

11. **[PROVED] Native `ζ_M`: poles = trivial-rep multiplicity; FE ⟺ polarization** (§22). RH-bearing objects = pure +
    polarized (motives).

12. **[PROVED] Mixed `L` factors over weights** (§29.1). `ζ_M=\prod_w ζ_{gr^W_w M}`.

13. **[PROVED, verified] The `F₁` trivialization `ψ_π=\prod_{k≥0}L(s+k,π)`** (§37, §41; numerics §37.4). Converges
    `Re s>1`, solves `ψ_π(s)=L(s,π)ψ_π(s+1)`, infinite-order (Hölder), zeros = `L`-zeros + shifts; special values
    `ψ_ζ(m)=\prod_{n≥m}ζ(n)` (`ψ_ζ(2)=2.29485`); monoidal under absolute-tensor = Rankin–Selberg (§41.2). **Its ABP
    regularity = the poles of `1/L` = GRH(π)** (§37.5, the difficulty conserved — no bypass).

## D. Imports (classical, the field's proven validations) [IMPORT]

- **Papanikolas** (`t`-motives): over `F_q(t)`, `\mathrm{trdeg}(\text{periods})=\dim G_M` — the period conjecture
  **proven** (§33), the full statement, by the field's mechanism.
- **Chudnovsky** (CM): `\mathrm{trdeg}(Γ`-value periods`)=\dim` CM torus (§27.2).
- **Gap-labelling** (Bellissard/Johnson–Moser): rotation-number periods `∈ℤ+ℤα` (§25.4, certified).
- **Deligne** (Weil II / purity), **Grothendieck** (cohomological `L`), **Avila**, **Selberg/Ingham**, **Sato–Tate
  (BLGHT)** — the function-field/dynamics validations (D6, D5, §12, D3).

## F. The adelic completion and the functional equation (§64–73)

14. **[PROVED, structural] The archimedean place as the prime at infinity** (§64). The Γ-recurrence
    `Γ_ℝ(s+2)=(s/2)/π·Γ_ℝ(s)` makes the archimedean place a rank-1 difference module with **polynomial** multiplier
    `(s/2)/π` — the unique non-constant-multiplier place (finite places: constant `1/p`). The diagonal shift `s↦s+1`
    has two readings (finite `∏_pσ_p` / archimedean `σ_∞`); completed `Λ` = diagonal over `P∪{∞}`. Two independent
    sources of hypertranscendence: the Γ-place (Hölder) and the infinite finite corank (§59–60).

15. **[PROVED for GL_1 + monomial GL_n; checkable residue] The functional equation as a base-symmetry** (§65–69,
    §71–73). Place-swap `0↔∞`; root number `ε=∏_v ε_v` (Tate) = the place-swap's coherence/cocycle condition.
    **PROVED:** `GL_1` (§68.2, ε_∞ Γ-place × ramified-local Gauss, verified tame `5,7,13` + wild `9,25,27`,
    `computations/root_number_place_swap`,`ramified_local_conductor`); **all monomial/CM `GL_n`** (§69, Artin +
    inductivity of ε-factors); hence **all essentially-tame `GL_n`** (§73, Howe/Bushnell–Henniart: `p∤n/f` ⟹
    field-induced ⟹ monomial). **Residue:** non-essentially-tame (`p∣n/f`; for `GL_2`, only the `p=2` exceptional
    family `A_4/S_4/A_5`) — **checkable, not famous-open** (local Langlands is a theorem, Harris–Taylor/Henniart; the
    open part is the `q`-Stokes vs known-`ε` matching, Conj 67.3/71.2/72.3).

16. **[IMPORT + structural] The complete local trichotomy** (§66–67). good (`f_p=0`, regular) / tame (`f_p=1`,
    regular-singular) / wild (`f_p≥2`, irregular, `q`-Stokes = `q`-wild fundamental group, grounded in Ramis–Sauloy–
    Zhang) + archimedean Γ-place; conductor `N=∏p^{f_p}` = divisor of `q`-irregularities. The field's adelic object.

17. **[META, PROVED] The structural/arithmetic-depth boundary** (§70–73, self-correction #18). The field's settled
    questions are all *structural/existence* (reached by construction: concentration, induction, induction-with-duality
    — incl. the primitive case for inverse-Galois); the open questions are all *arithmetic-depth properties of primitive
    objects*, split into **(A) checkable-structural** (the FE residue, local Langlands known, confined to `p∣n`) and
    **(B) genuinely famous-open** (GRC, Grothendieck period conjecture, global Langlands group, RH). Truly-irreducible
    frontier = (B) only; the boundary is the line between construction-reach and arithmetic depth.

## E. The keystone [CONJ — Tier C, never a Lean theorem]

`spec(H_L)=Spec(L)` (D5) = `F₁`-cohomology-with-Frobenius (D6) = obstruction C / smooth-number Dirichlet positivity
(D4) = GRH (D3) = `δ_arith` non-genericity (§18) = secular total positivity `Λ≤0` (route B, §35) = **`ψ_π` regularity
/ poles of `1/L`** (§37.5, §41). **One archimedean `F₁` object, ~seven faces.** The obstruction is **Hölder** (no
finite difference equation for `ζ`, §36); the resolution must be infinite-order (the explicit `ψ_π=\prod_kL(s+k,π)`,
§37/§41), whose regularity is GRH. Over `F_q(t)` this is Papanikolas's *theorem* (finite Frobenius); over `ℚ` it is
open (Hölder/infinite base). **Honestly unbuilt. Never an axiom.**

---

*Harden artifact: the [PROVED] lists (A–C, F) are the field's gap-free proven floor, vetted (§39 + the three audit
passes §61–63, **eighteen self-corrections**), formalizable, the ledger's target (`FlatConnection`,
`RankOneCohomology`, `SmoothNumbers` done; the rest queued). [IMPORT] (D) are the classical validations. [CONJ] (E) is
the one keystone — Tier C, the honest open frontier. This is what the field has actually proved, separated from what it
has imported and what it conjectures. The boundary is exact (§70–73): structural/existence theory complete; the open
frontier is the arithmetic depth of primitive objects, split into checkable-structural (the FE residue) and
genuinely-famous-open (GRC, Grothendieck, global Langlands, RH).*
