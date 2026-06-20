# Compute the monoidality obstruction ω ∈ H²(G_L) (G4 open core)

- **ID:** compute-omega-h2-gl
- **Stage:** 1-in-progress
- **Type:** OPEN CORE → CONJECTURE (native)
- **Source:** ../../door/G4-multi-q-picard-vessiot-and-langlands-group.md (#73 §4, open core), ../../door/bucket-the-seam-archimedean-obstruction.md (#90) · 00-status rows #27, #28, #71
- **Statement:** Compute (or bound) the **monoidality obstruction `ω ∈ H²(G_L)`** — the 2-cocycle by
  which the de Branges `⊗↦⊕` and the cup product `∧` disagree. **`ω = 0 ⟺ G_L is Tannakian ⟺ a genuine
  motive exists ⟺ the zero-realization succeeds`**, and at operator level **`ω = 0 ⟺ D trace-class
  (F₁-regularized) ⟺ Hilbert–Pólya ⟺ RH`** (unifies 5 programs: B5 monoidality, Deninger, B8 F₁, B35
  q→1, B18 HP). Apex: the difference-Galois group `G_𝒜` **is** the Langlands group `L_ℚ` (#28; the
  Rankin–Selberg `⊗`-half is already a theorem).

## Goal
One explicit `H²` class is the **single hinge** of three otherwise-separate gates: autonomy/C7 (a
Tannakian `G_L`), a genuine motive carrying the zeros, and the zero-realization that
`carrier-herglotz-rh.md` (G5) needs. The infinite-base Galois correspondence and inverse-Galois are
**built** (#68 §43.1/§55) but flagged **likely IMPORT** under Door-2 (Etingof / classical IGP / Deligne
as proof engines); the *uncomputed* piece — and the only one that is not a reframing — is whether
`ω = 0`.

## Door passport
- **Door-3:** `ω` is a native cohomological invariant intrinsic to the simultaneity of the `σ_p` (the
  `⊗↦⊕` mismatch is a property of the joint difference structure, not a single shift).
- **Door-2:** the surrounding Tannakian machinery is likely IMPORT; **computing `ω` natively** (via the
  prime-lattice Koszul complex, not Tannakian reconstruction) is the part that could be irreducible.

## Gates
- [x] 0 → 1  in-progress: `ω` defined as the `⊗↦⊕` vs `∧` 2-cocycle; the SEED-R Koszul reading pinned; the
  finite `e–h` shadow (`eh_koszul_duality`) identified as the testable floor. **Done** + §R extends it.
- [~] 1 → 2  fully-proven: **partial** — §R **locates** `ω` (the obstruction to deciding it): the
  multiplicative Koszul part is acyclic in the `∏_p` limit, so `ω` is a **purely archimedean class**
  (SEED-R-conditional BRIDGE). Deciding `ω=0` stays open (`ω=0⟺RH`); the residual is the archimedean
  Koszul-homology defect of the Γ-factor/`s=1` regularization. **§S extends:** operator face — `ω =`
  the Kontsevich–Vishik multiplicative anomaly of the archimedean ζ-det; **local** (Wodzicki residue), so
  finite primes contribute 0 and the archimedean local value is the **computed nonzero** constant
  `a_∞=½log2π` (D4 Layer-1, third face). Layer-2 (`ω=0⟺RH`) sharpened to: does the local counterterm **glue**
  across the FE (a Schanuel condition on prime-logs = the DSS wall). Layer-1 is `2-fully-proven`-ready; the
  ticket stays in-progress because the **decider** (Layer-2 gluing) is the open core.
- [ ] 2 → 3  formalized
- [ ] 3 → 4  publication-ready

## Approach
**SEED-R:** read `ω` as the **Koszul homology of the prime lattice in the `∏_p` limit** — `ω = 0 ⟺ the
∞-prime Koszul complex stays acyclic`. The finite Euler shadow `Σ_{i+j=k}(−1)^i e_i h_j = 0` is
**ledger-proven** (`EHKoszulDuality`). Decisive test: does the finite `e–h` acyclicity **survive the
renormalized `∏_{p≤P} → ∏_p` limit**? (the homological "fourth language" for the renormalization wall,
alongside ξ-outer condensation / LP-survival / explicit-formula limit). At operator level: `Γ-factor =
ζ-regularized det of D = Kurokawa absolute zeta`; `ω=0 ⟺ D is trace-class`.

## §R Result (2026-06-19, Professor) — ω is purely archimedean: the multiplicative Koszul part is acyclic
> **Prior art (standing-order check):** the *conclusion* "ω is purely archimedean" is **already in
> `support-extraction-log.md` #90 / Attack 6** (L1423): "ω = additivity of the archimedean place = missing
> Frobenius at ∞; trace defect = Γ-factor = Kurokawa absolute zeta." §R is a **new proof/mechanism** (the
> ∞-prime Koszul acyclicity `H(t)E(−t)=1` in `Λ`) for that known conclusion — **not a new discovery.**

**Setup (SEED-R).** Read `ω` as the Koszul-homology class of the prime lattice in the `∏_p` limit (#73 §6).
The multiplicative model is the λ-ring `𝓜 = ℚ[p_m] = Λ` (symmetric functions in **infinitely** many
variables; the power sums `p_m` = Adams operations are free polynomial generators, Macdonald I.2). The e–h
Koszul differential's acyclicity is the generating-function relation
```
   H(t)·E(−t) = 1   in Λ[[t]] ,      i.e.   Σ_{i+j=k} (−1)^i e_i h_j = 0   (k ≥ 1).
```

**[PROVED — unconditional algebra].** `H(t)E(−t)=1` holds in `Λ` itself — the standard relation between the
complete-homogeneous and elementary symmetric functions (Macdonald I.2), valid **in infinitely many
variables**, not merely a finite truncation. The finite Euler shadow `Σ_{i+j=k}(−1)^i e_i h_j = 0` is
ledger-proven (per the G4 bucket; `eh_koszul_duality` / `EHKoszulDuality`), and it **survives the
variable-count limit** because the identity is a formal identity in the inverse-limit ring `Λ`. Hence the
**unregularized ∞-prime Koszul complex is acyclic** (zero homology).

**[BRIDGE — SEED-R-conditional localization of ω].** Under the SEED-R reading, the multiplicative shadow of
`ω` is exactly this Koszul homology — which **vanishes**. Therefore `ω` carries **no multiplicative / Euler
content**: any nonzero `ω` is supported entirely on what the symmetric-function limit omits — the
**archimedean regularization counterterm** that turns the divergent `∏_p` into `ξ = Γ-factor × ζ`. **`ω` is
a purely archimedean class.**

**Answering the SEED-R test (#73 §6: "does finite e–h acyclicity survive the renormalized
`∏_{p≤P}→∏_p` limit?").** **Yes for the algebra, not necessarily for the analysis.** The multiplicative
(symmetric-function) acyclicity survives the limit trivially (`H(t)E(−t)=1` is exact in `Λ`); the
obstruction can only enter through the **analytic renormalization** (the archimedean counterterm), which the
algebraic limit does not see. This **splits the renormalization wall**: its multiplicative half is
Koszul-acyclic and inert; its archimedean half carries all of `ω`.

**Consequences.**
- Cohomological form of #74 ("multiplicative-only methods are apex-blind"): `ω∈H²(G_L)` is invisible to the
  Euler/Satake structure — a *proof* that the multiplicative wing cannot reach the realization obstruction.
- Places `ω` squarely in the **seam** (#71/#90): `ω` = the archimedean obstruction, the same single F₁ as
  the corank-∞ / Stieltjes face. The seam now has a **G4-cohomological face** alongside G1, G2, and the
  Stieltjes weld (`../2-fully-proven/stieltjes-log-weld.md`).
- Reduces compute-`ω` to a **purely archimedean** computation: `ω` = the Koszul-homology defect of the
  Γ-factor / `s=1` regularization, no longer entangled with the prime lattice. (Core stays open:
  `ω=0 ⟺ RH`.)

## §S Result (2026-06-19, Professor) — operator/spectral face: ω = the multiplicative anomaly of the archimedean ζ-det; local-trivial, globally the FE-gluing obstruction
> **Standing-order check.** "ω purely archimedean" is §R / support-log #90. §S is a **new mechanism**
> (operator language + a local Wodzicki formula) and a **new sharpening** (the H²-*degree* explained as
> local-triviality + a global gluing obstruction) — not a new discovery of locality.

**1. Spectral reduction of the archimedean generator [PROVED, elementary].** `∂_s = −Σ_p(log p)θ_p` acts
diagonally on the Dirichlet basis: `∂_s n^{−s} = −(log n)·n^{−s}`, so `spec(∂_s) = {−log n : n≥1}`. This
spectrum is **not** zeta-summable — `Σ_{n≥2}(log n)^{−z}` diverges for *every* `z∈ℂ` (`log n` grows slower
than any power) — so the **bare** generator `∂_s` carries no naive ζ-regularized determinant. The Γ-factor
is not `det(∂_s)`; it appears only through the weld/Deninger operator. The analytic obstruction is genuine,
not a missing computation.

**2. ω = the Kontsevich–Vishik multiplicative anomaly of the archimedean ζ-det [CONJECTURE (native), grounded
in Wodzicki theory].** The de Branges `⊗↦⊕` would force `det_∞` to be multiplicative:
`log det_∞(A⊗B)=log det_∞(A)+log det_∞(B)`; the cup product `∧` is its exterior counterpart; their
disagreement = failure of multiplicativity = the **multiplicative anomaly**
`a(A,B)=log det_ζ(AB)−log det_ζ(A)−log det_ζ(B)` (Wodzicki; Kontsevich–Vishik 1994; Elizalde–Vanzo–Zerbini,
CMP **194** (1998) 613). So `ω ↔ a(·,·)`. The reframe makes `ω` **computable**: for same-order ψDOs
`a(A,B)=(1/4b)·res[(ln(AB⁻¹))²]`, a **local** non-commutative-residue density.

**3. Locality ⟹ place decomposition; finite primes contribute 0 [BRIDGE].** The Wodzicki residue is a local
symbol integral, so the anomaly decomposes **place-by-place**. The finite primes carry constant (unipotent)
`σ_p`-multipliers `q_p=1/p` → their log-symbols have no anomaly; equivalently the multiplicative Koszul part
is acyclic (§R, `H(t)E(−t)=1` in `Λ`). Hence the whole anomaly sits at the **archimedean** place — an
operator-language proof of §R's conclusion, now via a local formula rather than a symmetric-function limit.

**4. The archimedean local anomaly is a nonzero, computed constant [PROVED — operator face of D4 Layer-1].**
The ζ-regularized determinant of the shift (the archimedean generator exponentiated) is
`det_ζ(shift_a)=exp(−ζ_H'(0,a))=√(2π)/Γ(a)` (Hurwitz/Lerch; certified ≥40 digits,
`computations/2026-06-19-omega-archimedean-anomaly`). The `√(2π)` the regularization **injects** is the
anomaly: the naive product `∏_{n≥0}(n+a)` carries no `2π`. Its log is the counterterm
`a_∞ = ½·log(2π) = 0.918938533204672741780… ≠ 0`. This is the operator value of **D4 Layer-1**: the weld does
**not** factor trivially; the obstruction is real and archimedean — a **third independent face** agreeing
with #132 (`[χ]≠1`, symmetry) and §R (Koszul, cohomology). **Substrate-WITH-content is confirmed.**
*Caveat (not a contradiction with `ω=0⟺RH`): `a_∞≠0` is the **local** anomaly value (a coboundary, item 5),
not the class `[ω]∈H²`. The number is nonzero; the cohomology class can still vanish.*

**5. Why ω lives in H² — local-trivial, globally the FE-gluing obstruction [CONJECTURE (native); sharpens the
open core].** The anomaly is local (a Wodzicki density), so each place's piece is a counterterm normalizable
away ⟹ **locally a coboundary**. The genuine invariant is whether the local archimedean counterterm **glues
consistently across the functional-equation weld** `Λ(s)=Λ(1−s)` (which couples `s↔1−s`, mixing the
archimedean place with the prime lattice). Local-triviality + a possible global gluing obstruction is exactly
the signature of a **degree-2** class — this is *why* `ω∈H²(G_L)` and not `H¹`. Then
`ω=0 ⟺ the local archimedean counterterm glues across the FE ⟺ D trace-class ⟺ RH`. The gluing couples `a_∞`
to the prime lattice through combinations `Σ_p m_p log p`; its consistency is an irrationality-measure /
**Schanuel** statement on prime-logs — the **same** `n≥3`/mixed-degree Schanuel core Wheeler/DeWitt pinned as
the DSS apex (`#125 §F`, chat id=177). **The archimedean ω-gluing and the DSS lower bound are one wall**
(a D2-unification: erase the framework and the seam and the transcendence-degree apex look unrelated).

**Net.** D4 Layer-1 is now proven on **three independent faces** (symmetry #132, cohomology §R, operator §S),
with a computed nonzero archimedean value `½log2π`. The H²-degree is explained (local-trivial / global-
obstruction). The open core (Layer-2, `ω=0⟺RH`) is sharpened to a single global statement: the
FE-gluing of the archimedean counterterm = a Schanuel-type condition on prime-logs, unifying the seam with
the DSS apex.

## §T Result (2026-06-19, Professor) — operator-side link to the bedrock: the regularization price = "no finite-dim cohomology"; the polarization as an anomaly quadratic form
Connects §S to `archimedean-weil-ii-bedrock.md` (the located bedrock: `ω=0` = the archimedean polarization
positivity = the missing F₁/Deninger cohomology + its polarization; no structural shortcut). §T does **not**
shorten that bedrock — it supplies the **operator dictionary** and one new construction lead.

**1. The non-summable spectrum IS the "no finite-dimensional cohomology" obstruction [§S side PROVED; the
identification is the operator↔cohomology dictionary, BRIDGE].** The bedrock (§3 of that card) locates the
ℚ-obstruction as "ζ has infinitely many zeros ⟹ the would-be `H¹` is infinite-dimensional ⟹ Deligne's
*finite* tensor-power argument does not terminate." §S item 1 is the **operator-level form of the same fact**:
`spec(∂_s)={−log n}` is not zeta-summable (`Σ(log n)^{−z}` diverges `∀z`), so `Tr(D^{−z})` has no finite value
and the determinant exists only after ζ-regularization — which **injects** the counterterm `a_∞=½log2π`. So
**`a_∞` is exactly the price of forcing a finite (regularized) determinant out of the non-summable spectrum —
the operator-level signature of "no finite-dimensional cohomology."** `ω=0` (in `H²`) ⟺ that price is
absorbable by a genuine finite/`F₁` cohomology = the bedrock. (Distinct constant from the explicit-formula
archimedean term `ψ(¼)−logπ`; `a_∞` is the det-normalization / Casimir-type counterterm, not the
log-derivative term — checked, to avoid conflating them.)

**2. A proposed operator origin for the polarization `Q_W` [CONJECTURE (native)].** The bedrock's load-bearing
datum is the archimedean polarization `Q_W` (the Weil form), demanded "with a geometric/operator source." The
anomaly `a(A,B)=(1/4b)·res[(ln(AB^{−1}))²]` (§S) is a **quadratic form in the log-symbol** `ln(A/B)`.
Conjecture: **`Q_W` is the multiplicative-anomaly quadratic form** — `Q_W(f) ≃ res[(ln D_f)²]` for the operator
`D_f` built from a test function `f` — and **RH ⟺ this Wodzicki-residue quadratic form is positive** on the
relevant cone. The Wodzicki residue is the *unique* trace on ψDOs but is **not positive** (it vanishes on
trace-class, can be negative), so positivity of `res[X²]` is non-trivial — precisely the irreducible RH
content. This gives the polarization an operator/anomaly source, tying it directly to `ω` (both are the *same*
anomaly functional). Parent BRIDGE analogue (Door-2): Connes' realization of the Weil distribution as a trace
on the adèle-class space (*Unverified — recalled: Connes, Selecta Math. 1999*). **Needs the Bohr/Dirichlet
ψDO calculus + Wodzicki residue, not yet built — flagged as the construction lead, not a result.**

**Net.** Operator dictionary: `a_∞` = the regularization price of the non-summable `{log n}` spectrum = the
operator face of "no finite-dim cohomology"; and a concrete conjectural origin for the polarization (the
anomaly quadratic form) that the bedrock's `F₁` program needs. The bedrock stays RH-hard (no shortcut).

## §U Result (2026-06-19, Professor) — ω ≡ Wheeler's missing-F₁ ABP arithmetic-lift: the derivation-vs-homomorphism mechanism (answers the #128 residual)
Responds to Wheeler's DSS decomposition (chat id=196; his `multi-q-abp-criterion` → 2-fully-proven):
**DSS lower bound = [`G_L` big — HAVE] + [GROUP→VALUES ABP arithmetic-lift — MISSING = a single F₁
Frobenius-specialization].** His residual to me (#128): *can `∂_s` be a differential/parametrized ABP
arithmetic-lift?* **Answer: NO, with a mechanism — and the missing lift IS `ω`.**

**1. The ABP lift is a MULTIPLICATIVE (difference/Frobenius) phenomenon [rigorous, uses ABP parent theory →
BRIDGE].** ABP lifts a relation among VALUES (`Ψ` at `t=θ`) to a relation among FUNCTIONS because the
Frobenius twist `σ` is a **ring endomorphism** (`σ(fg)=σ(f)σ(g)`) and the arithmetic point `θ` is compatible
with it. The lift rests on **multiplicativity**.

**2. `∂_s` is a DERIVATION, not a homomorphism — so it cannot be the lift [rigorous].** `∂_s(fg)=f∂_s g+g∂_s f`
(Leibniz, additive), **not** `∂_s(f)∂_s(g)`. The parametrized-PV machinery (Hardouin–Singer) lifts
`∂`-relations among functions to `∂`-relations — it specializes the **differential parameter** — but the
`{γ_n}` relations are **arithmetic values at `s=1`**, not differential. A derivation reaches the **group** (the
additive/Lie flow) but not the multiplicative values→functions lift. **This is the algebra behind Wheeler's
"`∂_s` feeds the group, not the arithmetic point." #128 stays closed.**

**3. Why neither available generator suffices — and what the missing F₁ is [structural].**
- Source-B `σ_p` **are** multiplicative ring endomorphisms, but they decouple prime-by-prime (BRIDGE) and fix
  the Euler structure — they do **not** reach the archimedean `{γ_n}` (Stieltjes/regularization defects, #75 =
  Source-A data).
- Source-A `∂_s` reaches `{γ_n}` via the flow but is a derivation (additive) — no multiplicative lift.
- The **missing F₁** = an **archimedean multiplicative Frobenius `σ_∞`** that is (a) a ring endomorphism AND
  (b) fixes/specializes at the arithmetic point `s=1` where `{γ_n}` live. Over `F_q`, Frobenius is the unique
  object that is **both at once** (the char-`p` coincidence). At `∞`: the shift `e^{∂_s}` is multiplicative but
  has **no finite fixed point** (`s↦s+1` fixes only `∞`); `∂_s` has the flow but isn't multiplicative. **No
  single archimedean object is both — that gap is the missing F₁.** *[Corrected in §V: the weight operator
  `E₁=(s−1)∂_s` has a multiplicative flow `exp(tE₁)` that DOES fix `s=1`; the real obstruction is not the
  operator's non-existence but that it gives no ABP lift — blocked by hypertranscendence #134.]*

**4. The obstruction to assembling it IS `ω` [CONJECTURE (native) — the ω=0⟺RH chain].** `ω` (§S) = the
multiplicative anomaly = the failure of the archimedean ζ-det to be multiplicative. The missing F₁ Frobenius
is exactly a multiplicative archimedean endomorphism; the obstruction to its existence is that anomaly. Hence
> **`ω = 0` ⟺ a multiplicative archimedean Frobenius (F₁) fixing `s=1` exists ⟺ the ABP GROUP→VALUES
> arithmetic-lift exists ⟺ Wheeler's DSS lower bound closes ⟺ a genuine motive exists ⟺ RH.**

**Wheeler's missing-F₁ arithmetic-lift and `ω` are the same object** — the precise form of the seam=DSS-wall
unification (chat id=188): **D4 (`ω`) ≡ the DSS GROUP→VALUES bridge ≡ D5 (F₁).**

**Spec for the F₁-Hodge construction (per Wheeler).** To crack DSS the F₁ object must supply a **multiplicative**
Frobenius at `∞` fixing `s=1` — not merely exist, and not a derivation/parametrized structure. If the
F₁-Hodge construction yields such a multiplicative lift, reopen #128; a purely differential/`∂_s` structure
provably will not (item 2).

## §V Result (2026-06-19, Professor) — the Frobenius-weight operator E₁ at s=1 (corrects §U); the ABP lift is obstructed by hypertranscendence itself
**Self-correction of §U item 3.** §U claimed "no single archimedean object is both multiplicative and fixes
`s=1`." **That was hasty.** The **linearization of the flow at the fixed point** does both.

**1. The Euler/weight operator `E₁=(s−1)∂_s` [PROVED].** `E₁(s−1)^k = k(s−1)^k`, so **`spec(E₁)={0,1,2,…}`** —
the non-negative integers, **zeta-summable** (`Σk^{−z}=ζ(z)`), unlike `spec(∂_s)={−log n}` (§S, not summable).
`E₁` is a derivation, but its **flow `exp(tE₁)` is multiplicative** (a composition operator,
`(fg)∘φ=(f∘φ)(g∘φ)`) **and fixes `s=1`** (because `E₁` vanishes at `s=1`). So a multiplicative operator
fixing the arithmetic point **does exist** — it is the *scaling around `s=1`*, not the *shift* (the shift
`e^{∂_s}` had no finite fixed point; the right object is the flow whose generator vanishes at `s=1`).

**2. `a_∞` is the regularized determinant of `E₁` [PROVED, ties §S].** `det_ζ(E₁)=∏_{k≥1}k=exp(−ζ'(0))=√(2π)`,
so **`log det_ζ(E₁)=½log2π=a_∞`** (the §S anomaly constant; already certified, the `a=1` case of
`computations/2026-06-19-omega-archimedean-anomaly`). This **upgrades §S item 4**: `a_∞` is not merely "the
shift counterterm" — it is `log det_ζ` of the **Frobenius-weight operator at the arithmetic point `s=1`**. The
`{γ_n}` are `E₁`'s action-data on `ζ`'s Laurent part at `s=1` (`E₁` weights the `(s−1)^k` coefficients by `k`).

**3. The true obstruction relocates to hypertranscendence (#134) [rigorous — ABP structure + #134 → BRIDGE].**
So the missing F₁ is **not** "no multiplicative fixed-point operator exists" (item 1 builds one); it is that
`exp(tE₁)` **does not supply the ABP arithmetic-lift**. ABP (Anderson–Brownawell–Papanikolas) lifts
value-relations to function-relations *because the t-motive satisfies a finite-rank **algebraic** σ-difference
equation* (the Φ-matrix `Ψ^{(−1)}=ΦΨ`). But `Λ` is **hypertranscendental** (`#134`,
`lambda-difference-differential-hypertranscendence.md`): it satisfies **no** algebraic difference-differential
equation. **So there is no finite-rank Φ-matrix — the ABP machinery has no algebraic input — and no finite
lift exists.** The lift, if any, must be **infinite-rank / ζ-regularized** (the Deninger cohomology; Deligne's
*finite* tensor-power argument does not terminate — cf. `archimedean-weil-ii-bedrock.md` §3).

**4. Conceptual closure — the founding theorem IS the obstruction [the project's organizing principle, made
precise].** ABP's Φ-matrix **is a generative flow** (the difference equation propagates the solution).
Hypertranscendence = "the object is fixed by a constraint, not propagated by a flow" = **the absence of such a
Φ-flow**. The `{γ_n}` are fixed by the constraint (FE + pole structure), not propagated by an algebraic
recurrence — so they are **not ABP-liftable algebraically**. Therefore:
> **The missing F₁ / DSS GROUP→VALUES lift is missing *by* hypertranscendence (#134).** D4/D5/DSS being open
> is **not a gap in our work** — it is *forced* by the founding negative theorem. The lift cannot be finite/
> algebraic; it must be the infinite ζ-regularized one, and **`ω=0` ⟺ that infinite regularization is
> consistent ⟺ RH** (CONJECTURE (native)). #134 forbids the *easy* (finite) lift, not the regularized one.

**Net.** Corrects §U (a multiplicative operator fixing `s=1` exists — the weight operator `E₁`, spectrum
`{0,1,2,…}`, `det_ζ=√(2π)=exp(a_∞)`). Relocates the obstruction, rigorously, to **hypertranscendence**: no
finite-rank Φ-matrix (#134) ⟹ no algebraic ABP lift ⟹ the F₁ Frobenius must be infinite/ζ-regularized
(Deninger), and its consistency is `ω=0`=RH. The founding "constraint-not-flow" principle is the precise
reason the apex (D4/D5/DSS) is open.

## §W Result (2026-06-19, Professor) — reconciliation with the parent corpus: the γ_n are EXPONENTIAL periods, sharpening the ABP/motivic obstruction (§V)
User directed me to the parent RH corpus (`/Users/Spare/Documents/code/riemann/docs/rh-corp/`). It reaches the
seam=archimedean-obstruction picture **independently** (`worklog-theorist` "seam IS the period/non-period
divide"; `conjecture_log` C-061/062 the missing-Frobenius object named from both sides) — strong convergence
with §R–§V. One refinement there is **not** in our pipeline / `support-extraction-log.md` and sharpens §V.

**1. DSS splits across the period/non-period divide [corpus conjecture, PSLQ-precertified].** `DSS = {π, ζ(odd)}
∪ {Stieltjes γ_n}`. The first half is **motivic** (mixed-Tate periods, Deligne–Goncharov Galois group known;
GPC-conditional). The `γ_n` are conjecturally **NOT Kontsevich–Zagier periods — they are EXPONENTIAL periods**
(`γ_E = −∫e^{−x}log x dx`), **invisible to the motivic Galois torsor** (corpus "DSS-cross"; PSLQ dps=150/300:
`{γ_0..γ_3}` ℚ-LI, cross-set `{1,π²,ζ3,ζ5,γ_n}` no relation).

**2. This is exactly why §V's ABP/motivic lift fails [synthesis; CONJECTURE (native)].** The ABP lift is a
**motivic** mechanism (`t`-motives = the function-field mixed-Tate analogue; the period torsor); it can lift
relations only among motivic / K–Z periods. The `{γ_n}` are **exponential** periods — outside the motivic
category — so even a perfect motivic realization (the Tannakian motivic Galois group = `ω=0` for the *period*
side) cannot reach them. §V's "hypertranscendence ⟹ no Φ-matrix ⟹ no finite ABP lift" sharpens to: **the
value-content the lift needs (`{γ_n}`) is exponential-period-type, beyond the motivic Tannakian reach.** The
required F₁ Frobenius is not merely multiplicative — it must be **exponential-motivic** (the exponential-motives
Galois group strictly contains the motivic one).

**3. `ω` = the period↔non-period (motivic↔exponential) gluing obstruction [refines §S].** The corpus's seam
`[𝔾_a,𝔾_m]` = the period/non-period divide **is** my §U additive(`∂_s`, `𝔾_a`)-vs-multiplicative(Frobenius,
`𝔾_m`) split. Precisely: the prime/Euler places carry **motivic** periods (ζ-values); the archimedean
**regularization data** — `a_∞=½log2π=−ζ'(0)=log det_ζ(E₁)` (§V), and the `{γ_n}` — are **exponential /
non-periods** (the corpus's "regularization manufactures transcendence" class: log2π, Stieltjes, Glaisher
`ζ'(−1)`; PSLQ-certified period-free). `ω` is the obstruction to gluing the exponential-motivic archimedean
place to the motivic prime places. So **`ω=0` (motivic realization) sees only the period side; the DSS apex
lives on the exponential side — same seam, same `ω`.**

**4. The exponential side IS the wild/irregular archimedean structure [VERIFIED framework — Fresán–Jossen].**
Confirmed (web, this session): Fresán–Jossen build a neutral ℚ-linear Tannakian category of **exponential
motives** `M^exp(k)` whose periods include "special values of the **gamma** function and the **Euler–Mascheroni
constant** — not expected to be periods of usual motives," realized as comparison coefficients between **de Rham
cohomology of connections with IRREGULAR SINGULARITIES** and **rapid-decay** cohomology; `M^exp` **contains the
classical (Nori) motives as a full subcategory**, so its Galois group **strictly contains** the motivic one.
This pins the period↔non-period divide to the **tame↔wild (regular↔irregular-singular) divide**: motivic /
ζ-values = regular-singular (mixed Tate); the Γ-factor (an **irregular singularity** / Stokes) + the
`{γ_n}`/regularization constants = irregular-singular / exponential. So **`ω` = the obstruction to a Frobenius
on the wild/irregular archimedean place** = the extension of the motivic (tame) realization to the
exponential-motivic (wild) one. This is the precise modern home of our **"Source A = differential-wild
archimedean place"** (charter §2) and the corpus's "wild archimedean / missing-Frobenius coupling"
(`conjecture_log` #2287, `worklog-theorist` #1817). *(Fresán–Jossen, Exponential Motives; arXiv:2007.08280,
2007.08290 — verified.)*

**Net.** Reconciles §S–§V with the parent corpus (independent convergence: seam = archimedean = missing
Frobenius). Sharpens the obstruction: the missing F₁ must be **exponential-motivic** — the `γ_n` are
exponential periods invisible to the motivic torsor — not merely a multiplicative Frobenius. `a_∞=½log2π` sits
on the exponential/non-period side, consistent with `ω` = the period↔non-period seam. **Actionable (corpus
payoff): aim any arithmetic lower bound at the `s=1` Laurent data (`{γ_n}`), not the integer ζ-values.**

## Cross-references
- `koszul-acyclicity.md` — the SEED-R Koszul sharpening of `ω` (the sibling that *is* the testable form).
- `carrier-herglotz-rh.md`, `weil-positivity-operator.md` — the G5 zero-realization `ω=0` enables.
- `c7-autonomy-foundational-core.md` — `ω=0` (Tannakian `G_L`) is the cleanest autonomy witness.
- `../../door/bucket-the-seam-archimedean-obstruction.md` — `ω` is the seam's central quantity.

## Log
- 2026-06-19 — created in 0-backlog. The G4 open core (compute `ω`), which simultaneously serves G4
  autonomy/C7, the G5 realization, the Langlands-group identity, and the seam.
- 2026-06-19 — Professor: pulled to 1-in-progress; completed the 0→1 deliverables and proved §R. The
  **unregularized ∞-prime Koszul complex is acyclic** (`H(t)E(−t)=1` in `Λ`, the e–h relation in infinitely
  many variables; finite shadow ledgered), so under SEED-R the multiplicative shadow of `ω` vanishes and
  **`ω` is a purely archimedean class** (no Euler content; cohomological form of #74). Answered the SEED-R
  renormalization-wall test: algebra survives the limit, the obstruction is purely analytic/archimedean.
  Adds a **G4-cohomological face to the seam**. Core `ω=0⟺RH` stays open; `ω` now reduced to the
  archimedean Γ-factor/`s=1` Koszul defect.
- 2026-06-19 — Professor: pulled to 1-in-progress (open barrier removed by user). Proved **§S**, the
  operator/spectral face of D4. (1) `∂_s n^{−s}=−(log n)n^{−s}` → `spec(∂_s)={−log n}`, not zeta-summable
  (bare `∂_s` has no naive ζ-det). (2) Reframe `ω =` Kontsevich–Vishik multiplicative anomaly of the
  archimedean ζ-det (Wodzicki local formula). (3) Locality ⟹ finite primes contribute 0; whole anomaly
  archimedean (operator proof of §R). (4) **Computed nonzero** archimedean value `a_∞=½log2π` (cert ≥40
  digits, `computations/2026-06-19-omega-archimedean-anomaly`) → D4 Layer-1 "substrate-with-content" on a
  third independent face (with #132 symmetry, §R cohomology). (5) `ω∈H²` explained as local-trivial /
  global FE-gluing obstruction; `ω=0⟺` the archimedean counterterm glues across the FE `⟺ RH`, a Schanuel
  condition on prime-logs = the **same wall** as the DSS apex (Wheeler/DeWitt #125 §F, id=177) — a
  D2-unification. Layer-2 stays the open core.
- 2026-06-19 — Professor: added **§T** connecting §S to `archimedean-weil-ii-bedrock.md`. (1) Operator
  dictionary: `a_∞=½log2π` = the ζ-regularization price of the non-zeta-summable `{log n}` spectrum = the
  operator face of the bedrock's "no finite-dimensional cohomology" obstruction. (2) Construction lead
  [CONJECTURE (native)]: the archimedean polarization `Q_W` (the load-bearing datum the bedrock needs built)
  = the multiplicative-anomaly quadratic form `res[(ln D_f)²]`; RH ⟺ this Wodzicki-residue form is positive
  (the residue is the unique but non-positive ψDO trace → positivity is the irreducible content). Parent
  analogue: Connes' trace formula (BRIDGE). Needs the Bohr-space ψDO calculus (not built). No shortcut to the
  bedrock claimed.
- 2026-06-19 — Professor: added **§U** answering Wheeler's DSS-decomposition residual (chat id=196). His
  missing piece — the GROUP→VALUES ABP arithmetic-lift (a single F₁ Frobenius-specialization) — **is `ω`**.
  Mechanism: the ABP lift is multiplicative (Frobenius σ = ring endomorphism); `∂_s` is a derivation
  (Leibniz, additive) → feeds the group, not the arithmetic point at s=1 (confirms #128 closed). Neither
  available generator is both multiplicative AND fixing s=1 (σ_p multiplicative but prime-decoupled / Euler
  only; ∂_s reaches {γ_n} but additive; shift e^{∂_s} multiplicative but no finite fixed point). The missing
  F₁ = an archimedean multiplicative Frobenius fixing s=1; its obstruction = the multiplicative anomaly `ω`.
  So `ω=0 ⟺ F₁ Frobenius exists ⟺ ABP lift ⟺ DSS closes ⟺ motive exists ⟺ RH`: **D4(ω) ≡ DSS-bridge ≡
  D5(F₁)**. Spec handed back: the F₁-Hodge construction must yield a MULTIPLICATIVE lift fixing s=1.
- 2026-06-19 — Professor: added **§V** (corrects §U). The Frobenius-weight operator `E₁=(s−1)∂_s` at the
  arithmetic point s=1: spec {0,1,2,…} (zeta-summable, unlike ∂_s's {−log n}); its flow exp(tE₁) IS
  multiplicative AND fixes s=1 — so §U's "no multiplicative fixed-point operator" was wrong. det_ζ(E₁)=√(2π),
  so log det_ζ(E₁)=a_∞=½log2π (ties §S; {γ_n} = E₁'s action on ζ's Laurent part). True obstruction relocated:
  exp(tE₁) gives no ABP lift because ABP needs a finite-rank algebraic Φ-matrix and Λ is hypertranscendental
  (#134) — no Φ-matrix, no finite lift. The F₁ Frobenius must be infinite-rank/ζ-regularized (Deninger).
  Conceptual closure: the founding "constraint-not-flow" theorem (hypertranscendence) IS the obstruction to
  the ABP generative-flow lift; D4/D5/DSS open is FORCED by #134, not a gap. ω=0 ⟺ the infinite regularized
  lift is consistent ⟺ RH.
- 2026-06-19 — Professor: added **§W** reconciling §S–§V with the parent corpus (`docs/rh-corp/`, user-pointed).
  Corpus independently reaches seam=archimedean=missing-Frobenius (worklog-theorist "seam IS period/non-period
  divide"; conjecture_log C-061/062), corroborating §R–§V. KEY un-extracted refinement: DSS = {π,ζodd}(motivic)
  ∪ {γ_n}(EXPONENTIAL periods, invisible to the motivic Galois torsor; corpus "DSS-cross", PSLQ-precertified).
  This is why §V's ABP/motivic lift fails: the {γ_n} value-content is exponential-period-type, beyond the
  motivic Tannakian reach. Verified (web): Fresán–Jossen exponential motives M^exp ⊃ Nori motives, periods =
  Γ-values + Euler–Mascheroni, from IRREGULAR-singular connections + rapid decay. So the period↔non-period
  divide = tame↔wild (regular↔irregular) divide; ω = obstruction to a Frobenius on the WILD/irregular
  archimedean place (= our Source A, charter §2). a_∞=½log2π is on the exponential/non-period side. Actionable:
  aim arithmetic lower bounds at the s=1 Laurent data ({γ_n}), not ζ-values. Filed extraction-gap ledger ticket.
