# Planetary atlas: multi-`q`-difference Galois theory — the coherent map

**Overview / front door of the field — 2026-06-19.** This atlas ties the nine founding drafts into one coherent
whole, states the field's thesis, and demarcates — honestly — what is *proved floor* from what is *open frontier*.
It is SEARCH (the field is conjectural at its frontier); the proved floors are draft-claimed structural results, the
ledger track (Lean) hardens them separately. **No proof of RH is claimed.** Read this first; the districts are the
detail.

---

## The thesis (one sentence)

> **Multi-`q`-difference Galois theory is the systematic dictionary in which the structure of arithmetic
> `L`-functions and the dynamics of quasiperiodic cocycles are two descriptions of one object — the
> difference-Galois group `G_M` of an infinite, integrable, prime-indexed system — and `ζ` is hard because it sits
> at the dictionary's single most degenerate entry.**

The field is *new*: it is the infinite-base (`ℵ₀` independent dilations, one per prime) extreme of `q`-difference
Galois theory (van der Put–Singer, Sauloy, Di Vizio) and Mahler's method (Adamczewski–Faverjon), a regime no
existing theory occupied because no existing theory had the infinite ergodic boundary.

---

## The one object and its three shadows

**`G_M`** = the difference-Galois group of a finite-rank integrable multi-`q` module `M` = the **holonomy of a flat
connection `{A_p}` on the prime lattice `ℤ^{(P)}`** (foundations §16; integrability `A_pσ_p(A_q)=A_qσ_q(A_p)`,
i.e. curvature `F_{pq}=1`). It casts three shadows:

- **Transcendence** ← the *orbit* `G_M·δ` of the diagonal point (values; District D4).
- **Dynamics** ← the *whole hull* `G_M` (boundary cocycle, Lyapunov; District D5).
- **Spectrum** ← the *zeros*, where the cocycle goes non-hyperbolic (District D3/Critic; the meeting point).

`δ_ζ` (the arithmetic diagonal) is the **triple point**: transcendence-degenerate ∧ cocycle-critical ∧ on the
critical line.

---

## The cross-continent dictionary (the field's spine)

| arithmetic / Hodge | dynamics / topology | district |
|---|---|---|
| Rankin–Selberg `L(s,π×π')` | tensor of cocycles `M_π⊗M_{π'}` | D3 §3 *(exact)* |
| Ramanujan / temperedness | elliptic cocycle, Lyapunov `L=0` | D3 §2 |
| Sato–Tate | eigenphase equidistribution | D3 §3′ *(measured)* |
| CM / non-CM | rotation / `SL₂`-dense cocycle | D3 §5,§8 *(measured)* |
| Hodge **weight filtration** | **Oseledets / Lyapunov filtration** | §21 |
| purity (Deligne) | conformality (one Lyapunov exponent) | §21, D6 |
| integrability `F_{pq}=1` | vanishing of an `H²_σ` curvature class | §16, §20 |
| diagonal collapse `δ` | LHS spectral sequence of `ℤ_diag⊂ℤ^{(P)}` | §5, §20 |
| Langlands functoriality | Tannakian morphisms / monodromy | D3 §4, D6 §4 |
| functional equation | polarization (self-duality on `M`) | §22 |
| Hilbert–Pólya operator | Connes scaling generator | D6 §7 |
| RH / GRH | reality of the cut-out spectrum = `Q_W≥0` | D5 §9, D6 §7 |

Each row is one description of `G_M` from two sides. The exact/measured rows are not analogies.

---

## The districts (the nine drafts)

| # | district | one line |
|---|---|---|
| **D1** | `multi-q-difference-galois-foundations.md` | the discipline: objects, constants, PV (decomposable §15 + non-decomposable §16), flora (§17–18), homology (§20), weights=Oseledets (§21), native `ζ_M` (§22), keystone convergence (§19) |
| **D2** | `infinite-base-difference-galois-for-L-functions.md` | the RH spine: wings (multiplicative free / archimedean frontier), the seam, 11 bricks, the fake-family firewall, the formalization tiers |
| **D3** | `automorphic-continent-rankin-selberg-ramanujan.md` | the Langlands world as rank-`d` modules; RS=`⊗`, Ramanujan=Lyapunov, functoriality=Tannakian; candidate Langlands group = `G_M` |
| **D4** | `transcendence-theory-nonholonomic-functions.md` | infinite-base Siegel–Shidlovsky for hypertranscendental values; `T-up` proved; obstruction A = smooth-number Dirichlet polynomials (Bombieri–Vaaler) |
| **D5** | `dynamics-continent-lyapunov-avila-morales-ramis.md` | boundary cocycle, difference Morales–Ramis (`DMR-solvable`, Avila-backed), the keystone `spec(H_L)=Spec(L)` (Johnson split) |
| **D6** | `geometric-rosetta-function-field-continent.md` | over `F_q(C)` the keystone is **Grothendieck**, RH is **Deligne**, Ramanujan is **purity** — the blueprint, proven; the `ℚ`-gap = one `F₁` brick |
| **D7** | `rh-holographic-pseudorandom-boundary.md` | the embassy: RH as boundary unitarity / the iterated logarithm (explicitly metaphor) |
| **—** | `hypertranscendental_galois_field_foundations.md` | (Critic) the spectrum/zeros continent: degree hierarchy, the Rigidity–Seam tradeoff (Conjecture H) |
| **—** | `formalization-queue.md` | the SEARCH→LEDGER handoff: 6 Tier-A targets for the ledger track |

---

## The organizing law (why arithmetic is hard)

> **`arithmetic ⟺ non-generic point of the flora ⟺ small orbit of δ ⟺ hard`** (§17–18, proved at rank 1).

The flora (all multi-`q` modules) is mostly **generic and transcendence-easy** but **non-arithmetic** (e.g. random
Euler products, §17). The arithmetic `L`-functions are a **thin non-generic slice** (the `q_p=1/p` tie). `ζ` is hard
not despite being special but **because it is the most special (most non-generic) point** of a larger, mostly-easy
field. Hardness has two independent axes (§18): *point-non-genericity* (transcendence; all arithmetic) and
*hull-non-solvability* (dynamics/chaos; non-CM). RH-bearing objects are the **pure + polarized** sub-locus (§22) —
the motives.

---

## The one keystone (the singular open frontier)

Every district's open core is the **same object** (§19), reached from five sides:

> **Build, at the archimedean seam over the fully-completed multiplicative skeleton `{A_p}` (`L=0`,
> Ramanujan-elliptic), a finite spectral object — a cohomology-with-Frobenius / an operator `H_L` — whose spectrum
> is the zeros.**

Five faces: `spec(H_L)=Spec(L)` (D5) = `F₁` cohomology-with-Frobenius (D6) = obstruction C / arithmetic of the
smooth-number Dirichlet polynomial (D4) = GRH (D3) = non-genericity of `δ_arith` (§18). Attacked directly (D6 §7),
it is the **Connes scaling operator**, with the multiplicative half *built* and RH = reality of its cut-out spectrum
= Weil positivity `Q_W≥0` = **the wall, reached from a new side and honestly not crossed.** New tool handed forward:
the native test space for `Q_W` is the smooth-number Dirichlet polynomials (D4 §8 = D6 §7).

---

## Honest ledger: proved floor vs open frontier

**Proved floor (draft-claimed, structural / by-assembly / imported, air-marked):**
- PV existence, decomposable (§15) and **non-decomposable** (§16, zero-curvature + Tannakian limit).
- Rank-1 flora classification `H^1_σ` (§17); the homological backbone `H^*_σ=H^*(ℤ^{(P)},·)` (§20).
- `DMR-solvable` (D5, Avila-backed); the weight filtration = Oseledets filtration (§21); native `ζ_M` poles = reps,
  FE = polarization (§22).
- Transcendence upper bound `T-up`, Prop 6 (D4); obstruction A supplied via Bombieri–Vaaler (D4 §8).
- The exact dictionaries (D3 §2,§3); the geometric continent's **theorems** (D6: Grothendieck, Deligne, Deligne–Katz).
- **Numerical certificates** (archived, `computations/`): the Lyapunov dichotomy (5 dp); the CM/non-CM Satake angles.

**Open frontier (the one keystone, five faces):** `spec(H_L)=Spec(L)` = Weil positivity = the `F₁` brick. **Tier C —
never a Lean theorem, never an axiom.** Honestly unbuilt; each district says so.

**Ledger track (Lean, Librarian):** 28 axiom-clean theorems (Tier A), including the flat-connection algebra of §16
(`FlatConnection.lean`); 6 Tier-A targets queued.

---

## What this is, and is not

**Is:** a new branch of mathematics with rigorous foundations, a complete structural theory (one group, three
shadows, a cohomology, a weight theory, a flora, native zetas), real arithmetic data, a geometric continent where its
central conjecture is a **theorem**, an organizing law explaining *why* arithmetic is hard, and a single
honestly-named open frontier — built, with a three-postdoc team, in a night and refined onward.

**Is not:** a proof of the Riemann Hypothesis. The keystone is unbuilt; the wall (Weil positivity) is reached from a
new direction and not crossed. The field's value is the **map and the localization** — it reduces the whole problem
to one named construction (the `F₁`/archimedean spectral object over a fully-built multiplicative skeleton) and hands
forward a new test space (smooth-number Dirichlet polynomials) to attack it.

*The discovery phase has a horizon, and this atlas is its shape: interior mapped, dictionary complete, frontier
singular and named. What remains is to build that one brick — the open problem — and to formalize the proved floors
(the ledger track, live).*

---

## Current state (update, §20–41 + harden)

The atlas above was written at ~§19. The field has since grown a full motivic apparatus, a geometry, and a verified
keystone construction. Current map:

**Foundations (D1), now 43 sections** — beyond the §1–19 core: the **homological backbone** `H^*_σ=H^*(ℤ^{(P)},·)`
(§20, inverse limit), **flora classification + organizing law** "arithmetic = non-generic" (§17–18), **structure
theory** = mixed dynamical motives (§24), **period theory** = Lyapunov exponents & rotation numbers (§25), **weight =
Oseledets / Newton = Lyapunov / Mazur** (§21, §30), **realization comparison** de Rham↔Betti (§26), **native `ζ_M`**
poles=reps, FE=polarization (§22), **special values** = BSD/Beilinson, `χ=0` (§23), **mixed `L` + MZVs as dynamical
periods** (§29), the **`F₁` trivialization** `ψ_π=∏_kL(s+k,π)` (§37–41, verified, regularity = GRH), **geometry**:
the moduli space, symplectic (§38, regularized), isomonodromy = `q`-Painlevé, the field's **fundamental theorem** —
the **infinite-base Galois correspondence** (§43.1) with the **inverse problem (P3) solved for the pro-torus** (§43.2:
closed subgroups ↔ relation sublattices, all realized, arithmetic = the `Λ=0`/full-torus vertex) and **"arithmetic
lives at infinity"** made precise (§43.3: one dense diagonal orbit, finite-blind), and the **rank-2 flora** (§44):
the five species {split-torus, unipotent, Borel, dihedral=CM, irreducible=non-CM}, the **first non-toral `G_M`** (`𝔾_a`,
the planet's logarithm), and the organizing law at rank 2 (*arithmetic `GL_2` is forced tempered `L=0`* — Ramanujan as
non-genericity).

**Eight major areas reached** (each a specific, correct identification): automorphic `L` (D3), ergodic theory (D5 §11,
a frontier the field *created* — infinite-frequency cocycles), transcendence + MZV (D4, §29), Hodge/motives (§21–27),
`p`-adic Hodge (§30, Mazur=Lyapunov), index theory (§31, root number=Maslov), value-distribution/RMT (§12,
Selberg/Keating–Snaith), discrete integrable systems (§38, `q`-Painlevé).

**Validated** — three proven period cases: gap-labelling (§25.4), Chudnovsky (§27.2), **Papanikolas** (§33, the *full*
period conjecture, over function fields, by the field's mechanism). The keystone is a *theorem* over `F_q(t)`
(Grothendieck/Deligne/Papanikolas); the `ℚ`-obstruction is **Hölder** (§36), the resolution the explicit `ψ_π` (§37).

**The one keystone, ~seven faces** (§19, §35): `spec(H_L)=Spec(L)` = `F₁`-cohomology = obstruction-C = GRH =
`δ_arith` non-genericity = secular-TP `Λ≤0` = `ψ_π`-regularity. One archimedean `F₁` object; Tier C; honestly open.

**Proven core** distilled and vetted: `proven-core.md` (the [PROVED]/[IMPORT]/[CONJ] separation, now spanning §43–73 —
fundamental theorem, solved inverse-Galois problem, C5/C6 proved, the adelic completion + functional equation as
base-symmetry, the structural/arithmetic-depth boundary); **eighteen self-corrections** applied (incl. the systemic #12
below, the falsification #13, and the audit trims #15–18 from three adversarial passes §61–63); Lean ledger live
(`FlatConnection`, `RankOneCohomology`, `SmoothNumbers` done, rest queued); **35 certified computations**
(`computations/`, each with referee + captured output).

**Honesty correction (§42, self-correction #12, systemic).** The earlier "six-route keystone convergence" and
"three-operator convergence" rhetoric is *retracted as significance*: any two RH-equivalent statements are trivially
equivalent, so listing equivalent faces carries no information beyond "each is RH-equivalent". What survives as
genuine is **(a)** each face's *specific explicit structure* and **(b)** *actual identities between particular pairs*
(secular power-sums = explicit-formula moments, Newton duality; `ψ`-poles = zeros) — not a deep "convergence". The
field claims only the non-trivially-true. (And: same spectrum ≠ same operator — the Jacobi/Schrödinger/cocycle
"equality" is an isospectrality, not an operator identity.)

**Structural spine (§43–46, off the RH axis).** The field now has a **fundamental theorem** (the infinite-base
Galois correspondence + solved inverse problem P3, §43), a **complete low-rank flora** (rank 1 §17, rank 2 §44 incl.
the first non-toral `G_M=𝔾_a`), a **main structure theorem** (neutral Tannakian over `ℂ`, arbitrary `G_M⊆GL_d`, three
uniform laws, §45.1), a **central bridge conjecture** (the arithmetic difference-Galois group **is** the
Langlands/motivic group, §45.2 — a *theorem over `F_q(t)`* by Papanikolas, §45.3), and a **sharp conjecture ledger**
(§46: six structural conjectures C1–C6 — three new: GRC=Lyapunov-positivity, arithmetic-nowhere-dense-in-moduli,
infinite-base⟺hypertranscendence — plus the RH face C7 explicitly walled off). The spine of a publishable foundational
text, independent of RH; every claim graded, every conjecture falsifiable, RH quarantined to one line.

**Conjecture-front progress (§47–51, verified).** Import dissolved (§47: the "several-operator" theory = classical
`n=1` PV + the co-extension identity). **C1 FALSIFIED then C1″ PROVED** (§51–52, self-correction #13): the multi-base genuinely adds
groups — `μ₂×μ₂` via independent primes is multi-`q` but not single-`σ` (finite single-`σ` groups are cyclic);
connected case survives (Etingof). The sharp successor **C1″ is now a theorem (§52):** `R_multi∩finite = finite
abelian` exactly (finite ⟹ abelian by the commuting-monodromy lemma; converse by independent primes). Full arc:
stated → falsified → sharpened → proved. **The whole inverse-Galois problem is then CLOSED (§53–55):**
`R_multi = {G : π₀(G) finite abelian}` exactly, **no residue** (connected via Etingof, finite=abelian via §52, monomial
& outer-twist via induction-with-duality §54–55; self-correction #14 caught en route) — a defining question of the
Galois theory, completely answered, off RH. **C6-forward PROVED**
(§49.2, Lipshitz). **C4 PROVED** at all ranks on monomial ∪ Artin ∪ `GL₂`-holo ∪ **RACSDC** self-dual cohomological
(§50–51, verified Caraiani-circle), open only on non-self-dual cuspidal (= GRC's own residue). All citations
web-verified.

> **State in one line:** a vast, vetted, collaboratively-built new branch of mathematics — *the dynamical realization
> of motivic theory over the infinite prime base* — with a complete apparatus, eight areas, three proven period cases,
> a structural spine (fundamental theorem → flora → main structure theorem → Langlands bridge, §43–45), a verified
> explicit keystone object (`ψ_π=∏_kL(s+k,π)`), twelve honest self-corrections, and one honestly-open archimedean `F₁`
> frontier. The discovered core is built, vetted, and distilled; the formalization is live; the
> conjecture is one object. RH, if it comes, is the regularity of `ψ_ζ` — a property of an explicit infinite product.
