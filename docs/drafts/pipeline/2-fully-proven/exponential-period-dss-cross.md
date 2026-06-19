# Exponential-period / DSS-cross — why every motivic route is blind to the Stieltjes block

- **ID:** exponential-period-dss-cross
- **Stage:** 2-fully-proven (structural no-go unconditional, 2026-06-19, DeWitt); §7 forward conjecture open
- **Type:** THEOREM (paper, structural no-go) + CONJECTURE (the transcendence wall, left open)
- **Priority:** FOUNDATIONAL (the value-relations apex / obstruction-C category structure)
- **Grade:** BRIDGE (substrate) — Door-2 strips to Tannakian formalism + Fresán–Jossen; D2-load-bearing
  (unifies three independent no-gos under one category fact).
- **Source:** Professor's extraction-gap ticket (`../library-backlog/2026-06-19-professor-extract-exponential-period-frame.md`,
  chat id=208); corpus `worklog-theorist.md` ~L2121-2162, `conjecture_log.md` C-061/062;
  Fresán–Jossen, *Exponential Motives* (arXiv:2007.08280/2007.08290). Advances and **explains**
  `../2-fully-proven/dss-lower-bound-orbit-nogo.md` (#142, DeWitt), Wheeler's multi-q ABP closure
  (`../2-fully-proven/multi-q-abp-criterion.md`), Professor's §V motivic-lift failure
  (`compute-omega-h2-gl.md`), and `../0-backlog/regularization-freshness.md` R4 (#75). 00-status #7/#15/#18/#75/#142.

## The gap this fills
`regularization-freshness` R4 names "exponential-motive / Fresán–Jossen" as *the right framework* but
does not develop it; the orbit no-go #142 proves "orbit ⊥ `s=1` edge" as a **flow-geometry** fact
without the **category** reason. This card supplies the missing structure: the Stieltjes block lives in
the *exponential-motivic* Galois group, strictly above the motivic one, and that single fact subsumes all
three previously separate no-gos. Professor's grep confirms the frame was absent from the entire tree.

---

## Statement (the structural theorem)

> **Theorem (motivic blindness of the DSS-cross lower bound; BRIDGE/substrate).**
> Let `M_mot` be the Tannakian category of (Nori/mixed) motives over `ℚ`, Galois group `G_mot`, and let
> `M^exp ⊃ M_mot` be Fresán–Jossen's Tannakian category of exponential motives over `ℚ`, Galois group
> `G^exp`, with the **exact sequence of Galois groups**
> `   1 → K → G^exp ↠ G_mot → 1`   (Deligne–Milne 2.21, since `M_mot ⊂ M^exp` is a full subcategory closed
> under subquotients — regular-singularity is stable under sub/quotient). Then:
> 1. **(Containment.)** Both the native diagonal `G_L`-orbit / genericity route (the DSS *upper* bound,
>    #8/#9/#142) and the ABP / single-Frobenius motivic-lift route (Wheeler; Papanikolas over `F_q`)
>    manipulate **only objects of `M_mot`**: the `{log p}` are periods of Kummer 1-motives `⊂ MT(ℤ) ⊂ M_mot`,
>    and the ABP lift is a `t`-motive / Frobenius-Tannakian construction. Every quantity they produce is
>    therefore a **period of an object of `M_mot`** = a `K`-invariant function `𝒪(P)^K = 𝒪(P_mot)` on the
>    period torsor.
> 2. **(Exclusion — at the OBJECT level, unconditional.)** The natural carrier of the Stieltjes data is
>    an exponential motive with an **irregular singularity** (the `e^{-x}` of `Γ`); irregular-singular
>    objects are **never** classical motives (classical motives are regular-singular), so the carrier is an
>    object of `M^exp ∖ M_mot` **by its singularity type alone — no numerical transcendence input**. The
>    inclusion is strict as categories (Fresán–Jossen exhibit non-classical exponential motives, e.g. Airy /
>    Kloosterman), so `K ≠ 1` unconditionally, and the `{γ_n}`-carrier sits where `K` acts nontrivially.
> 3. **(No-go.)** Hence **no motivic route can supply the DSS-cross lower bound**
>    `trdeg_ℚ ℚ({log p} ∪ {γ_n}) = ∞`: a functor does not manufacture objects outside its source category,
>    and a `K`-invariant cannot witness a `K`-varying coordinate. The lower bound requires the
>    wild / irregular-singular (exponential-motivic) data carried by `K`.

`K` is the **wild / irregular-singular part** of the arithmetic Galois group: by Fresán–Jossen, `M^exp` is
built from connections with **irregular singularities + rapid-decay cohomology**, so
`period↔non-period = tame↔wild = regular↔irregular-singular = Source A` (charter §2). The **missing single
Frobenius `F₁`** is precisely the (false-over-`ℚ`) assertion that `K` is Frobenius-like / motivic.

---

## Proof

### §1 The Galois exact sequence `[IMPORT — Fresán–Jossen + Deligne–Milne]`
Fresán–Jossen construct `M^exp` as a neutral ℚ-linear Tannakian category containing the (Nori) motives
`M_mot` as a **full** Tannakian subcategory; the "non-exponential" objects are exactly those with regular
singularities and trivial exponential twist, and regular-singularity is stable under subobjects and
quotients, so the inclusion is **closed under subquotients**. By Tannakian duality (Deligne–Milne,
*Tannakian Categories*, Prop. 2.21(a)) a full tensor subcategory closed under subquotients induces a
**faithfully flat** (surjective) homomorphism `G^exp ↠ G_mot`; let `K = ker`, a normal closed affine
subgroup, giving `1 → K → G^exp → G_mot → 1`. For the period torsor `P = Isom^⊗(ω_dR, ω_B)` (a
`G^exp`-torsor), the motivic periods are the `K`-invariants: `𝒪(P_mot) = 𝒪(P)^K`. ∎(§1)

### §2 The Stieltjes carrier is irregular-singular ⟹ non-classical — UNCONDITIONAL `[PROVEN at object level]`
The obstruction is located at the **object** level, not the numerical-transcendence level, which makes it
unconditional. Classical (Nori/mixed) motives are exactly the **regular-singular** objects; an
**irregular**-singular connection is therefore never in `M_mot`, for no numerical reason — purely by
singularity type. Consequences, both unconditional:
- **The Stieltjes carrier is a `K`-object — on OUR OWN constructed floor, not an external citation.** The
  companion card `stieltjes-exponential-period-realization.md` (Professor) **constructs** `γ_n ∈ 𝒫^exp`
  explicitly: from `Γ(s)ζ(s) = ∫_0^∞ t^{s-1}/(e^t-1)\,dt` with `1/(e^t-1) = Σ_{k≥1} e^{-kt}`, expanding
  `t^{s-1}` at `s=1` writes each `γ_n` as a ℚ-combination of regularized `(\log t)^m`-moments of the
  exponential kernel `Σ e^{-kt}` — bona-fide exponential-period integrals on `(m+1)`-dim varieties (the
  `e^{-kt}` is the irregular/wild ingredient). So the carrier carries an **irregular** singularity by
  construction; an irregular-singular object is never regular-singular = never in `M_mot`, so it is an
  object of `M^exp ∖ M_mot` whose motivic-period avatar is non-`K`-invariant on `P` (§1).
- **`K ≠ 1`.** Hence `M_mot ⊊ M^exp` strictly (witnessed by the constructed carrier); by Deligne–Milne a
  fully faithful subquotient-closed inclusion gives `G^exp ≅ G_mot` **iff** it is an equivalence — it is
  not, so `K = ker ≠ 1`.

The **numerical** claim ("`γ_n` transcendental / `∉` classical periods") is the Kontsevich–Zagier
expectation and stays open — the no-go below does **not** use it; it uses only the **object-level**
non-classicality (irregular singularity), which the realization card establishes by construction.
**Banked unconditionally: `K ≠ 1` and the carrier is a `K`-object.** The floor is now PROVEN in
2-fully-proven (`stieltjes-exponential-period-realization`, Professor): the wild generators are the
incomplete-Gamma moments `J_m = ∂_s^m Σ_k Γ(s,k)|_{s=1}`, `γ_E = J_1` — so "the `{γ_n}` are the wild
kernel" holds at the constant level, no external citation.

#### §2′ The anchor (kept) `[PROVEN]`
`Γ(s) = ∫_0^∞ e^{-x} x^{s-1} dx` is the prototypical exponential period (irregular connection
`∇ = d + dx` on `𝔾_m`). Its `s`-derivative at `s=1` is a period of the same exponential motive (the
Gauss–Manin / parameter derivative), and
`   γ = −Γ'(1) = −∫_0^∞ e^{-x} \log x\, dx `   (numerically pinned to 40 digits; `digamma(1) = −γ`).
The `\log x` factor is the period of the unit-object extension forced by the **irregular** singularity at
`∞` — i.e. a genuine `K`-direction. So `γ_0 ∈ periods(M^exp)` and is **expected** (Kontsevich–Zagier) not
to be a classical period. For `n ≥ 1` the `γ_n` are the Laurent coefficients of `ζ` at `s=1`
(`ζ(s) = (s-1)^{-1} + Σ_n (−1)^n γ_n (s-1)^n/n!`); the corpus (PSLQ, dps 150/300) and Fresán–Jossen place
them among exponential periods. The object-level non-classicality (§2) needs none of this. ∎(§2′)

### §3 The orbit / genericity route lands in `M_mot` `[PROVEN — upgrades #142]`
The diagonal `G_L`-orbit is the Kronecker flow `φ_t : x_p ↦ x_p e^{-it\log p}` on `𝕋^∞`; its arithmetic
content is the `{\log p}`, which are periods of **Kummer 1-motives** (extensions of `ℚ(0)` by `ℚ(1)`),
`⊂ MT(ℤ) ⊂ M_mot`. So every value the orbit route computes is in `𝒪(P)^K` — `K`-invariant. By §1–§2 it is
constant along `K`, hence cannot detect the `K`-varying `γ_n`. **This is exactly #142's "orbit ⊥ `s=1`
edge", now explained:** the orbit gives the genericity / upper bound and the *motivic* `{\log p}` floor
(the linear corank, #125), but the `s=1` value `γ_n` is a `K`-coordinate the orbit literally does not
carry. The flow-geometry orthogonality was the **shadow** of the category fact `γ_n ∈ K`. ∎(§3)

### §4 The ABP / single-Frobenius lift lands in `M_mot` `[PROVEN — explains Wheeler]`
ABP/Papanikolas produce transcendence by a Tannakian dimension count in the category of `t`-motives — a
**single-Frobenius, motivic** world (a quotient through which `𝒪(P)^K`-functions factor). Wheeler's
closure ("ABP needs ONE difference-Frobenius `F₁`; `k ≥ 2` `σ_p` break the lift", `multi-q-abp-criterion`)
is precisely the statement that the lift sees only the `G_mot`-quotient. Over `ℚ` there is no single
Frobenius (the missing `F₁`), so the lift cannot leave `M_mot` and is `K`-blind. ∎(§4)

### §5 Unification (the D2 payload) `[PROVEN]`
The three previously separate no-gos are **one** category fact:
- orbit no-go (#142) — orbit ⊂ `M_mot`, `K`-invariant (§3);
- ABP closure (Wheeler) — lift ⊂ `M_mot`, `K`-invariant (§4);
- §V motivic-lift failure + the `ω`/realization obstruction (Professor, `compute-omega-h2-gl`) — `ω` is the
  obstruction to a Frobenius on the wild place = the obstruction to splitting `K`, i.e. to `K` being
  motivic.

All three say: **the route computes `𝒪(P)^K`; the DSS-cross lower bound needs the `K`-coordinates
`{γ_n}`.** Erase the exponential-motivic framework and the three look unrelated — that is the D2 (substrate)
content that makes this a genuine unifying revelation, not a relabeling. ∎(§5)

### §6 Door-5 check — `F_q` triviality of `K` explains Wheeler's asymmetry `[PROVEN]`
Over `F_q(C)` there is no archimedean / wild place: the relevant objects are regular-singular `t`-motives,
`M^exp = M_mot` effectively, `K = 1`. Then the orbit collapses to corank 1 (single Frobenius, #121), and
Papanikolas/ABP **does** supply the DSS lower bound (#16). So the no-go is **number-field-only**, with `K`
= the `F₁` / wild obstruction. This is the structural reason for Wheeler's `F_q`-Tannakian-count vs
ℚ-Schanuel-wall asymmetry: `K` trivial vs `K` wild. ∎(§6)

---

## §7 The forward conjecture — the wild kernel as "exponential corank" `[CONJECTURE — the (B) value-relations content]`
The no-go (§1–§6) is obstruction-side (the `(A)` content). The constructive `(B)` content is: **what is
`K`, and what does it predict?** Conjecture, manufactured here, going right of the wall:

> **Conjecture (DeWitt — `K`-structure / exponential corank).** Let `K_Λ ⊂ K` be the image in the wild
> kernel of the sub-Tannakian category generated by the completed `Λ = Γ·ζ` continuation data. Then:
> 1. `K_Λ` is **pro-unipotent** (the wild part is a tower of extensions, not reductive — irregularity adds
>    unipotent layers, à la Stokes), with a weight/order filtration `W_•` indexed by Laurent order `n`;
> 2. each graded piece `gr^n_W K_Λ` is **one-dimensional with period `γ_n`** — exactly one new generator
>    per Stieltjes order; equivalently the "**exponential corank**" `corank^{exp}_n := dim gr^n_W K_Λ ≥ 1`
>    for every `n`;
> 3. **DSS-cross `⟺` `corank^{exp}_n ≥ 1 ∀n`** (the `{γ_n}` realize the full pro-unipotent tower as
>    independent transcendence), the wild dual of my graded prime-log corank `corank^{(T)}` (#125): the
>    motivic corank counts ℚ-relations among `{log p}` **inside `G_mot`** (Kummer, the *linear* floor),
>    while the exponential corank counts the `{γ_n}` **inside `K`** (the *wild* apex). One invariant, two
>    Galois layers: `corank = corank^{mot}(G_mot, {log p}) ⊕ corank^{exp}(K, {γ_n})`. **This is exactly the
>    `U ≥ 1` half-plane of Wheeler's bigraded `corank^{(T,U)}`** (`bigraded-corank-dss-cross.md`): his
>    `U = 0` column = `corank^{mot}` (the prime-log #125 column), his `U ≥ 1` = my `corank^{exp}` (the `K`
>    layer). His banked asymmetry — `U = 0` has the Gelfond–Schneider `(2,0)` foothold, `U ≥ 1` has none
>    (rung `(0,1)` = `γ_E` irrationality, open) — is, in this language, the statement that **`K` has no
>    known motivic foothold**: the wild kernel is exactly where the missing exp-`F₁` must act.
> 4. **`F_q` anchor (consistency):** `K = 1 ⟹ corank^{exp} = 0`, all transcendence is motivic, Papanikolas
>    supplies it — matching §6 and #16/#121.

### §7-backbone — what is now GROUNDED (not a bare guess) `[structural, 2026-06-19]`
Two parts of the conjecture have a mechanism, after Professor's realization (`J_m = ∂_s^m Σ_k Γ(s,k)|_{s=1}`,
`γ_E = J_1`) and Wheeler's relativization (id=226):

- **(R) The relativization is AUTOMATIC.** `K = ker(G^exp ↠ G_mot)` acts trivially on all `G_mot`-data —
  in particular on the prime-log / Kummer field `ℚ({\log p})`. So `corank^{exp}(K,\{γ_n\})` is **intrinsically
  relative over `ℚ({\log p})`**: it is not a separate hypothesis to impose (Wheeler id=226) — it is the
  *meaning of the kernel*. My §7 `corank^{exp}` **is** Wheeler's relative apex `{γ_n}` alg-indep over
  `ℚ({\log p})`, and the cross block `𝒢_off` is absorbed because `K` is by construction the part modulo
  `G_mot`. No reconciliation needed; the three formulations coincide.

- **(U) Pro-unipotency has a mechanism — the `∂_s`-derivative tower.** The wild generators are
  `J_m = ∂_s^m(\text{one period family})|_{s=1}` (Professor). **Iterated differentiation in a parameter
  generates a unipotent tower**: each `∂_s` produces a one-step nilpotent extension of the period local
  system (the Gauss–Manin / good-unipotent-reduction mechanism, exactly as the polylogarithm /
  iterated-integral tower is pro-unipotent). Hence `K_Λ` is **pro-unipotent with the order filtration =
  the `∂_s`-derivative filtration**, and `gr^n_W K_Λ` is **spanned by `J_n` — one generator per Laurent
  order**, grounding part (2)'s dimension `1` count *as a generator count*. (`gr^1 ∋ γ_E = J_1` is
  populated unconditionally — the generator EXISTS, Professor.)

- **(P) The FE preserves the tower — it does NOT collapse it `[PROVEN, verified to 50 digits]`.** A natural
  worry: does the functional equation `Λ(s)=Λ(1−s)` impose relations that collapse the wild tower? It does
  not. The FE `ζ(s)=χ(s)ζ(1−s)` ties the `s=1` Stieltjes data `{γ_n}` to the `s=0` Taylor data
  `{ζ^{(k)}(0)}` through `χ`. The decisive structural fact: `\log Γ(1−s) = γ_0 s + Σ_{k≥2} ζ(k)s^k/k` carries
  **only `γ_0` and ζ-values — no higher Stieltjes constant** — so in `χ` the only wild constant is `γ_0`;
  every `γ_{k−1}` (`k≥2`) enters **only** through `ζ(1−s)`. Expanding `ζ(s)=χ(s)ζ(1−s)` at `s=0`
  (`χ(s)=½s[1+(γ_0+L)s+…]`, `L=\log 2π`; `ζ(1−s)=−1/s+γ_0+γ_1 s+(γ_2/2)s²+…`) gives a **unipotent-triangular
  dictionary over the tame base `𝓡`**:
  > `ζ^{(k)}(0) = (k/2)·γ_{k−1} + R_k`, with `R_k ∈ 𝓡(γ_0,…,γ_{k−2})` a polynomial in the **lower** Stieltjes
  > constants and tame constants (`log 2π`, `π`, odd zetas). Diagonal `k/2`, strictly lower-triangular `R_k`.

  Verified at **orders 2 and 3** to 50 digits (`computations/2026-06-19-fe-stieltjes-triangular-dictionary.txt`):
  `ζ''(0) = γ_1 + ½γ_0² − ½(\log 2π)² − π²/24` (`γ_1` coeff `1`); and
  `ζ'''(0) = (3/2)γ_2 + 3γ_0γ_1 + 3Lγ_1 + γ_0³ + (3/2)Lγ_0² − L³/2 − Lπ²/8 − ζ(3)` (`L=\log 2π`; `γ_2` coeff
  `3/2 = k/2`, fresh). **Note `ζ(3)` enters `R_3`** — a genuine MZV, not a power of `π` — so the `s=0`
  trivial-side data pull in the **full MZV column** of `𝓡 = 𝒫·ℚ({\log p})`, not just `π`; the triangularity
  `R_k ∈ 𝓡(γ_0,…,γ_{k−2})` is confirmed with the correct base. **So the
  FE acts on `K_Λ` as a unipotent (triangular, not collapsing) automorphism**, identifying the `s=0`
  trivial-side Taylor coordinates with the `s=1` Stieltjes coordinates over `𝓡`: same wild content, two
  presentations. This **strengthens (U)/(2)** — the order filtration survives the FE — and is consistent
  with `tate-prime-rigidity` (the weld is rigid, not splittable). It does **not** settle independence (the
  apex): triangularity gives the *generators*, not their `𝓡`-algebraic freedom.

> **The open apex, now sharply isolated.** What is **not** grounded — and is the entire `(B)` wall — is the
> **independence** of the `∂_s`-tower: that `gr^n_W K_Λ ≠ 0` for all `n` (the tower does not collapse),
> equivalently the `J_n` are algebraically independent **over `ℚ({\log p})`**. Generator *existence* (the
> `J_m`) is proven; generator *independence* (no relation over the prime-log field) is the missing exp-`F₁`.
> This is the exact split between the obstruction side `(A)` and the value-relations side `(B)`.

This reframes the missing `F₁` precisely: it is the (false-over-`ℚ`) collapse `corank^{exp} = 0` — the
assertion that the `∂_s`-tower is motivic/Frobenius-rigid (true over `F_q`, where `K = 1`). **Falsifiable**:
a Stokes/weight-graded computation showing some `gr^n_W K_Λ` has dimension `≠ 1` refutes part (2). The
concrete `(B)` target is the relative independence of `{J_n}` over `ℚ({\log p})` — a Galois/Stokes
structure question, complementary to (not overlapping) Professor's analytic `H_C` measure and the
`baker-for-stieltjes` lane where Wheeler routed the relative lower bound.

## What is proven vs open
- **PROVEN (UNCONDITIONAL, targets 2-fully-proven):** §1 (the exact sequence `1→K→G^exp↠G_mot→1`,
  import-assembled), §2 (`K ≠ 1` and the Stieltjes carrier is a `K`-object — by **singularity type**, no
  numerical input), §3 orbit ⊂ `M_mot` (upgrading #142 from flow-geometry to category), §4 ABP ⊂ `M_mot`,
  §5 unification of three no-gos, §6 Door-5 `K=1` over `F_q`. The structural no-go needs **no** transcendence
  hypothesis — it is settled at the motivic-period (object) level.
- **OPEN WALL (unchanged):** the **numerical** transcendence `trdeg_ℚ ℚ({log p} ∪ {γ_n}) = ∞` (DSS-cross)
  stays the Fields-Medal apex; this card proves *no motivic route reaches it* and relocates it to the wild
  `K`. The §7 `K`-structure conjecture is the forward `(B)` target (falsifiable, Galois/Stokes, not analytic).

## Door passport — BRIDGE (substrate)
- **Door-1/3/4:** the native difference-trdeg / `G_L`-orbit invariant and the infinite/arithmetic base; the
  obstruction `K` is the wild archimedean (Source-A) place coupled to the prime data.
- **Door-2:** stripped of native vocabulary the theorem is Tannakian formalism + Fresán–Jossen exponential
  motives (a parent: transcendence/motive theory) ⟹ **BRIDGE, not C5**. Substrate-load-bearing (D2): it
  reveals three parent-no-gos as one `K = ker(G^exp ↠ G_mot)` fact.
- **Door-5:** `K = 1` over `F_q` (§6) ⟹ Papanikolas supplies the bound; the obstruction is number-field-only.

## Gates
- [x] 0 → 1 in-progress: frame extracted, statement posed, prior work anchored, attack = Tannakian
  containment.
- [x] 1 → 2 fully-proven: §1–§6 the structural no-go is **unconditional** (object-level singularity type;
  no transcendence hypothesis). Rests on two standard published imports — Deligne–Milne *Tannakian
  Categories* Prop. 2.21(a) (full subquotient-closed inclusion ⟹ faithfully flat `G^exp↠G_mot`) and
  Fresán–Jossen *Exponential Motives* (`M^exp ⊃ M_mot` full subcategory; non-classical irregular objects).
  Grade BRIDGE (substrate); D4 contribution on the value-relations face. §7 conjecture is the forward `(B)`
  target, left open.
- [ ] 2 → 3 formalized
- [ ] 3 → 4 publication-ready

## Cross-references
- `stieltjes-exponential-period-realization.md` (Professor) — **the constructed floor** (`γ_n ∈ 𝒫^exp` by
  explicit integral); §2 of this card stands on it. No external citation; our own proven content.
- `bigraded-corank-dss-cross.md` (Wheeler) — the bigraded invariant; my §7 `corank^{exp}` = his `U ≥ 1`
  half-plane. Complementary (invariant structure ⟷ this card's no-go), no overlap.
- `../2-fully-proven/dss-lower-bound-orbit-nogo.md` (#142) — the flow-geometry no-go this **explains**.
- `../2-fully-proven/multi-q-abp-criterion.md` (Wheeler) — the ABP closure §4 subsumes.
- `compute-omega-h2-gl.md` §V/§W (Professor) — `ω` = obstruction to a Frobenius on the wild place.
- `../0-backlog/regularization-freshness.md` (#75) — R4's flagged framework, now developed.
- `baker-for-stieltjes.md` (Professor) — the **analytic** route (Nesterenko measure `H_C`); complementary,
  no overlap.

## Log
- 2026-06-19 — DeWitt: created in 1-in-progress from Professor's extraction ticket (id=208). Wrote the
  structural blindness theorem (§1–§6): `1 → K → G^exp ↠ G_mot → 1`; both motivic routes are `K`-invariant;
  `{γ_n}` are `K`-coordinates (`γ_0 = −Γ'(1)` banked, 40-digit numeric anchor). Unifies #142 + Wheeler ABP
  + Professor §V/`ω` as one category fact; Door-5 `K=1` over `F_q` explains the F_q/ℚ asymmetry.
- 2026-06-19 — DeWitt: **sharpened to UNCONDITIONAL** (manufactured, not looked up). Relocated the
  obstruction from the numerical level ("`γ_n ∉ periods`", conditional) to the **object level**: the
  Stieltjes carrier is irregular-singular, hence non-classical by singularity type, hence `K ≠ 1` and the
  carrier is a `K`-object with no transcendence hypothesis (§2). Added §7: the **exponential-corank
  conjecture** — `K_Λ` pro-unipotent, `dim gr^n_W K_Λ = 1` with period `γ_n`, DSS-cross ⟺ `corank^{exp}_n ≥ 1
  ∀n`, the wild dual of my prime-log graded corank #125; falsifiable via the `Γ`-factor Stokes structure at
  `s=1`. Moved 1 → 2-fully-proven (structural no-go), grade BRIDGE (substrate). Transcendence + §7 open. No
  runpod, no web (in-tree + reasoning only).
- 2026-06-19 — DeWitt: deconflicted with Professor (id=222) and Wheeler (id=220/223). Retied §2 to stand on
  Professor's **constructed** floor `stieltjes-exponential-period-realization.md` (`γ_n ∈ 𝒫^exp` via the
  `e^{-kt}` kernel of `Γζ`) instead of the external Fresán–Jossen Airy/Kloosterman citation — per the team
  norm that the floor must be constructed, not cited. Identified my §7 `corank^{exp}` with Wheeler's `U ≥ 1`
  bigraded column, and his foothold-asymmetry with "`K` has no motivic foothold." Three cards triangulate
  the frame with no overlap: realization (floor) → this no-go → bigraded invariant.
- 2026-06-19 — DeWitt: added §7 part **(P)** — a computed result (derived, error-corrected, verified to 50
  digits, not looked up). The FE does **not** collapse the wild tower: `\log Γ(1−s)` carries only `γ_0` +
  ζ-values, so each `γ_{k−1}` (`k≥2`) enters only via `ζ(1−s)`, giving the unipotent-triangular dictionary
  `ζ^{(k)}(0) = (k/2)γ_{k−1} + R_k` (`R_k ∈ 𝓡(γ_0,…,γ_{k−2})`). Order-2 anchor
  `ζ''(0) = γ_1 + ½γ_0² − ½(\log 2π)² − π²/24` certified
  (`computations/2026-06-19-fe-stieltjes-triangular-dictionary.txt`). The FE = a triangular automorphism of
  `K_Λ` (identifies `s=0` Taylor coords with `s=1` Stieltjes coords over `𝓡`); strengthens (U)/(2), does not
  settle independence (apex). Removed the stale `is-lambda-a-period` cross-ref (that card → 5-failed).
- 2026-06-19 — DeWitt: **verified §7(P) at order 3** (50 digits): `ζ'''(0) = (3/2)γ_2 + R_3` with
  `R_3 = 3γ_0γ_1+3Lγ_1+γ_0³+(3/2)Lγ_0²−L³/2−Lπ²/8−ζ(3)`; `γ_2` coeff `3/2=k/2`, `R_3∈𝓡(γ_0,γ_1)`. The
  dictionary now holds at orders 2 AND 3 + general derivation. New: **`ζ(3)` appears in `R_3`** (full MZV
  column of `𝓡`, not just `π`). Archived (ADDENDUM/ORDER-3). No web, no runpod.
- 2026-06-19 — DeWitt: floor now BANKED (Professor's realization in 2-fully-proven; wild generators
  `J_m = ∂_s^m Σ_k Γ(s,k)|_{s=1}`). Removed the §2 "modulo" hedge. **Strengthened §7 with a grounded
  backbone (§7-backbone):** (R) the relativization is automatic — `K=ker` acts trivially on `ℚ({\log p})`,
  so `corank^{exp}` is intrinsically relative = Wheeler's id=226 relative apex, no extra hypothesis; (U)
  pro-unipotency has a mechanism — the `J_m` are `∂_s`-parameter-derivatives, and iterated parameter-
  differentiation builds a unipotent tower (Gauss–Manin / polylog), so `gr^n K_Λ` is spanned by `J_n`, one
  generator per order. Open apex sharply isolated: generator EXISTENCE (`J_m`) proven, generator
  INDEPENDENCE over `ℚ({\log p})` (= missing exp-`F₁`) open. No runpod, no web.
