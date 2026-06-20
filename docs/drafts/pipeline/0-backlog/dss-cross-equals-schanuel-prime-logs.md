# DSS-cross = Schanuel for prime-logs (the open apex — `ω_mot=0` / `K` free)

- **ID:** dss-cross-equals-schanuel-prime-logs
- **Stage:** 1-in-progress (moved from 0-backlog 2026-06-19; being ground here — the **regular column** of DSS-cross, sibling to the exponential column `../1-in-progress/relative-exponential-apex.md`)
- **Type:** OPEN CORE / CONJECTURE (native) — **open.** Honest status: the *reduction* to this statement is **proven**; the statement itself is **open** and is **not** to be faked (it implies the algebraic independence of `{ζ(odd)}`-class data).
- **Source:** the three-way split of `omega-splits-wild-kernel-freeness.md` (user-directed 2026-06-19); the proven corank reduction in `f1-inversion-single-prime-stieltjes-collapse.md`; `compute-omega-h2-gl.md` §U/§V; `corank-seam-invariant.md` (#125); ../../door/bucket-the-seam-archimedean-obstruction.md

## The open conjecture
> **`ω_mot = 0 ⟺ K` (wild kernel) free ⟺ DSS-cross ⟺ `trdeg_ℚ\{γ_n\} = ∞` ⟺ Schanuel for prime-logs** (`{\log p}` algebraically independent).

## What is PROVEN (the reduction — see `f1-inversion…`)
- **`trdeg\{Stieltjes\,of\,ζ_S\} = trdeg\,ℚ(\log p:p∈S)`** for Euler truncations `ζ_S=∏_{p∈S}1/(1-p^{-s})` (symmetric-function generation). So the apex `corank ∞ ⟹ trdeg ∞` **is exactly** Schanuel-for-prime-logs — *derived, not assumed.*
- **corank-1 (one Frobenius):** `γ_n^{(q)}=B_n^{+}(\log q)^n/n!` — `trdeg 1` (proven, Bernoulli). ⟹ the **F₁ inversion**: a single Frobenius would *collapse* `trdeg` to 1 and **destroy** DSS; its absence is the *mechanism*, not the obstacle.
- **corank-2 rung:** `trdeg ≥ 1` PROVEN (Gelfond–Schneider: `γ_0^{(2,3)}` transcendental via `\log2/\log3`); `trdeg=2 ⟺ \{\log2,\log3\}` algebraically independent — the first **open** Schanuel rung.
- **Hölder:** `ζ` not D-finite ⟹ `{γ_n}` not P-recursive (no recurrence-relations).

## What is FALSE (ruled-out routes — see `5-failed/omega-splits…`)
- The `K`-freeness/`H²(free Lie)=0` Galois route (trivial unipotent gerbe — no Schanuel bypass).
- `F₁` = the Stokes automorphism (the local wild monodromy is Tate — A5).

## The honest target (the only piece that is open and not open-immediate)
The **monotonicity / corank→trdeg lower bound**: *each genuinely new `ℚ`-independent `\log p` lifts `trdeg\{γ_n\}` by ≥1.* Its first rung (`corank 1 → 2`) = "`\log2,\log3` algebraically independent" — open even there. Proven floor: corank-1 exact, corank-2 transcendence (G-S). **Attack the rungs; do not try to construct `F₁` (self-defeating).**

## Cross-references
- `f1-inversion-single-prime-stieltjes-collapse.md` — the proven reductions + the inversion (the live approach to this apex).
- `archimedean-wild-monodromy-tate-local.md` — A5 + the Ext–Hodge dictionary (paper-proven; rules out the local/Stokes attack).
- `../5-failed/omega-splits-wild-kernel-freeness.md` — the falsified `K`-freeness route.
- `corank-seam-invariant.md` (#125), `compute-omega-h2-gl.md` §U/§V — the seam / `ω` program.

## Gates
- [x] 0 → 1: the apex is well-posed and *reduced* (= Schanuel for prime-logs, proven reduction); the open content is the monotonicity rungs. **Ground 2026-06-19** (GRINDING SESSION §§A–E): spectral reformulation (apex = alg-indep of the `∂_s`-spectrum, Door-1 native), the native freeness-agnosticism no-go (regular column = purely value-lift, unified with the exponential column and the `#165` GROUP→VALUES residue), the `(a)/(b)` two-Frobenii disambiguation, the KAM/Diophantine EMBASSY, and the verified degree-2 PSLQ floor.
- [ ] 1 → 2: a rung (`corank 2`, i.e. `\log2,\log3` alg-indep) — open; **not** to be fabricated. Per §B the only route is the analytic **value-lift `(b)`**, and per §B-Consequence-2 a single flat construction is predicted insufficient (mirroring `relative-exponential-apex` §8); the live native target is **prime-weighted (multi-`q`) decoupling** of the approximation forms.

## Log
- 2026-06-19 — created as **Part 3 (still open)** of the omega-splits three-way split (user: "move the still open part ticket back into backlog"). States the open apex `ω_mot=0 ⟺ DSS-cross ⟺ Schanuel for prime-logs`, with the **proven reduction** and **proven floors** (corank-1 exact, corank-2 Gelfond–Schneider) cross-referenced, and the falsified/proven parts pointed to their homes. The apex is open and explicitly not to be faked.

---

# GRINDING SESSION — 2026-06-19 (regular column, attacked with the scientific method)

The apex itself (Schanuel-for-prime-logs) is open and is **not faked here**. What this session
adds, by working the conjecture with the method (split / reframe / make-visual / find-invariant /
test-as-false / look-for-similar-objects / write-the-fake-proof), is **structure around the wall**: a native
reformulation, a no-go that closes an entire class of attacks and unifies the two DSS-cross columns, a
disambiguation of two operators the program conflates, and an empirical floor. Banked content in
`corank-seam-invariant.md` (§B level-separation, §C graded corank, §F Gelfond–Schneider) and
`f1-inversion…` (corank-1 collapse, `trdeg{Stieltjes}=trdeg ℚ({log p})`) is **not** re-derived; this builds
strictly on top of it.

## §A The spectral reformulation — the apex on the field's own generator `[PROVEN reframing; Door-1 native]`

The archimedean generator is `D = ∂_s = −Σ_p (log p) θ_p`, `θ_p = x_p ∂_{x_p}`, on the Bohr prime modes
`x_p = p^{−s}` (`00-foundations` N1⁺). Direct computation:
- `θ_p x_q = δ_{pq} x_p`, so `∂_s x_p = −(log p) x_p` — **`{−log p}` is the spectrum of `∂_s` on the prime
  modes;**
- on a composite mode `x_m = m^{−s} = ∏_p x_p^{a_p}` (`m = ∏ p^{a_p}`): `∂_s x_m = −(log m) x_m =
  −(Σ_p a_p log p) x_m` — the spectrum is the **additive image** of the prime spectrum under unique
  factorization (eigenvalue additive over the multiplicative monoid `λ(x_m x_n)=λ(x_m)+λ(x_n)`,
  `λ:=−log`). *(Equivalently `∂_s = d/ds` on `m^{−s}` gives eigenvalue `−log m`. Elementary, verified.)*

> **Reformulation (native).** **DSS-cross / Schanuel-for-prime-logs ⟺ the eigenvalue spectrum `{log p}` of
> the archimedean generator `∂_s` is algebraically independent over ℚ.**

This puts the apex on the field's own object (Door-1 ✓): not "ζ-zeros / Euler product / explicit formula"
relabelled, but the **spectrum of `∂_s`**. The corank invariant (#125) is the rank of the *additive group*
generated by this spectrum (linear datum, `=∞` proven); the apex is its *algebraic* independence — the
content the additive group does not carry (§B).

**A2 reading (the no-clock payload).** Each prime lane is an oscillator of frequency `log p` = the eigenvalue
of the *time*-generator `∂_s`. A2 ("non-holonomic = no global clock, only the simultaneous many-clock of the
`σ_p`") is, on the spectrum, exactly: the prime frequencies `{log p}` share **no algebraic relation**, so no
reparametrisation collapses them to one master clock. *Linear* incommensurability (`Σ a_p log p ≠ 0`) is
proven (unique factorization = the clocks are genuinely independent); *algebraic* incommensurability
(Schanuel) is the apex. **"Many clocks, no master clock" ⟺ "frequencies algebraically independent."**

## §B Native freeness-agnosticism — why every native symmetry is blind to the apex `[PROVEN no-go that LOCATES]`

`corank-seam` §B noted `corank` is linear (`≤ trdeg`). This sharpens it to a **no-go on the entire native
apparatus** and explains why no symmetry of the field has cracked the apex.

**Self-correction first (test-as-false, applied to my own claim).** A naive "degree-1 ceiling" — *the
structure cannot even express degree-≥2 monomials* — is **FALSE**: `∂_s^k x_m = (log m)^k`, and since
`log p·log q = ½[(log pq)^2 − (log p)^2 − (log q)^2]`, the squares `{(log m)^2}` already ℚ-span the full
homogeneous degree-2 space. So `∂_s`-powers on composite modes **do realize** every monomial in `{log p}`.
The structure is *expressively complete*, not degree-capped. The correct no-go is about **relational
content**, not expressive range:

> **Theorem (native freeness-agnosticism).** Via `∂_s^k` on composite modes the native data realizes
> `{log p}` as the **free polynomial generators** of `ℚ[log p] ⊂ ℂ` (every monomial is an eigenvalue). The
> only relations among the spectrum that the `(mult, ∂_s, σ_p, FE)` structure **forces** are the ℤ-linear
> ones of the prime-log lattice `Λ` (unique factorization — none beyond freeness at degree 1). The structure
> certifies **no** algebraic relation of degree `≥2` **and cannot certify their absence**: algebraic
> independence of `{log p}` = faithfulness of the realization `ℚ[log p] ↪ ℂ` is **undecided by** the native
> data.

*Proof.* (i) *Expressive completeness:* `∂_s^k x_m=(log m)^k`; the perfect squares ℚ-span homogeneous degree
2 (identity above), inductively all degrees, so the eigenvalue data realizes all of `ℚ[log p]`. (ii)
*Relational content is linear:* the structure's only constraint among eigenvalues is the additivity
`λ(x_m x_n)=λ(x_m)+λ(x_n)`, with image the free lattice `Λ` (unique factorization); `σ_p` act trivially on
the spectrum (`σ_p` rescales modes, fixes every frequency `log q`); FE is the order-2 sign map `λ↦−λ`,
preserving the relation set and adding none. Beyond additivity every native equation is a *polynomial
identity in the symbols* `log p`, never an equation forcing a nontrivial polynomial in distinct `{log p}` to
vanish. (iii) Hence a degree-`≥2` relation and its negation are **both** consistent with all native data —
agnosticism. ∎

**Consequence 1 — the regular column is PURELY a value-lift, identical in shape to the exponential column.**
`relative-exponential-apex.md` §10 proved the function-level `(σ,∂)`-Galois of the digamma is *Hölder-maximal*
yet the *value* `γ_E` independence is a separate `F₁` lift. §B is the regular-column mirror: the
symmetry/function level is *free-maximal* (the Galois/“group” side is the free polynomial algebra of infinite
rank — as big as possible) yet *value* independence is the separate lift. **Both DSS-cross columns reduce to
the same missing object — the value-lift / GROUP→VALUES Frobenius (#165) — and in both the entire native
content is exhausted before the apex** (function-level Hölder there, free polynomial algebra here). This is a
method-level unification of the two conjuncts, not merely a shared target. It also lands the regular column
in the established `#165` vocabulary: **GROUP maximal, VALUES realization missing.** Triangulated three ways
(regular column §B, exponential column §10, abstract G2 Tannakian #165) — all three independently say *group
big, value-lift the sole residue*.

**Consequence 2 — the native `σ_p` contribution to the apex is ANALYTIC, not algebraic.** Since `σ_p` are
degree-0 on the spectrum, they cannot *algebraically* generate a degree-`≥2` constraint. So the field's bet
("`σ_p`-simultaneity supplies the missing `F₁`") can only mean the `σ_p` enter through the **Diophantine
denominator channel** of a transcendence construction — the `lcm(1..n)=∏_{p≤n}p^{⌊·⌋}` denominators
(`log lcm ∼ n`, PNT) — *not* as an algebraic symmetry. This is precisely where the `σ_p` appear in
`relative-exponential-apex` §5–§8, and where the single flat construction died (§8 there). **Prediction:** the
regular column meets the *same* Diophantine wall — a single integer-relation/approximation construction will
be insufficient; the live native question is whether prime-weighted (multi-`q`) orthogonality decouples the
forms. The two columns share the obstruction's *shape*, not just its name.

*(Door grade: BRIDGE — a structural/no-go statement, like §10 there. It does not touch the open apex
residue; it closes the class of native-symmetry attacks and redirects all effort to the analytic value-lift.)*

## §C The two Frobenii — disambiguating f1-inversion's `(a)` from the needed `(b)` `[clarification + coordination flag]`

The program says "the missing single Frobenius `F₁`" for **two different** operators; separating them
sharpens the target and removes an apparent contradiction.

- **`(a)` the lattice-collapse Frobenius** (`f1-inversion…` §2): restricting `Λ` to one prime `q` collapses
  `corank→1` and `trdeg{γ_n}→1` (`γ_n^{(q)}=B_n^+(log q)^n/n!`). Supplying `(a)` **destroys** DSS. Correct,
  and it is the f1-inversion content: `(a)` is a *collapse*, not a tool.
- **`(b)` the value-lift / ABP Frobenius**: the `φ`-semilinear operator powering the
  Anderson–Brownawell–Papanikolas criterion that lifts "Galois group big" to "values algebraically
  independent." Over `F_q(θ)` it **exists** and **proves** the function-field analog of
  Schanuel-for-logs — Carlitz logarithms of `k`-linearly-independent algebraic points are algebraically
  independent (Papanikolas 2008; **IMPORT, recalled — to re-verify against
  `../2-fully-proven/g2-over-fq-papanikolas-dss.md`**). There the value-lift *works*, on a high-dimensional
  `t`-motive, with *high* `trdeg` — the **opposite** of a collapse.

**The disambiguation.** `(a) ≠ (b)`. `f1-inversion` rules out `(a)` as helpful (right — it kills DSS); §B
isolates `(b)` as the *only* remaining content. The two cards are then consistent and complementary: the
lattice having `corank ∞` (no `(a)`) is the *enabler* of DSS, and the apex is whether a `(b)`-type value-lift
exists over ℚ **without** `(a)`. Over `F_q` both notions are present, but DSS uses `(b)` on a `t`-motive while
the `ζ_C`-multiplier module is itself `(a)`-rank-1; the **ℚ obstruction is the absence of `(b)`**, not the
presence of corank ∞.

**Flag (coordinate, do not assert).** The banked FF cards describe the `F_q` Frobenius once as
collapse-to-rank-1 (`corank-seam` §A/§B) and once as the Papanikolas value-engine (`g2-over-fq-papanikolas-
dss`). These are **two different modules** (the rank-1 `ζ_C`-multiplier lattice vs the high-dim Carlitz-log
`t`-motive). Recommend the seam bucket make the `(a)/(b)` split explicit so "the missing `F₁`" unambiguously
denotes `(b)` = the value-lift. *(Routed to the door-sync ticket; FF cards not edited here.)*

## §D EMBASSY — the prime-oscillator allegory (KAM / Diophantine frequencies) `[metaphor → one structural prediction → quarantined]`

Wild-analogy move (turn the spectrum into a physical picture, find a far field that looks the same).

**Picture.** `{log p}` = frequencies of countably many prime oscillators (`∂_s` = the time-generator, §A). A
*resonance* is a vanishing combination of frequencies.

**Far field — KAM / Hamiltonian dynamics.** A frequency vector `ω` is **Diophantine** if
`|⟨k,ω⟩| ≥ C|k|^{−τ}` for all integer `k≠0` (no near-resonances; invariant tori survive perturbation).
Baker's *effective* lower bound on linear forms in logs, `|Σ k_i log p_i| ≥` (effective), is **exactly** the
statement that the prime-frequency vector is Diophantine. So **proven linear independence + Baker = "the
prime oscillators are a maximally non-resonant (Diophantine) frequency system"** — the flow/dynamics layer is
fully settled.

**Where the analogy breaks — and what that confirms.** KAM only ever needs *linear* non-resonance (tori are
labelled by `⟨k,ω⟩`); there is **no** dynamical notion of a *polynomial* relation among frequencies. So
algebraic independence (Schanuel) has **no dynamical shadow** — it is invisible to the flow. This is the
metaphor **confirming §B from a wildly different direction**: the flow/frequency (degree-1) layer is settled
(Baker = Diophantine = KAM-good); the algebraic (degree-`≥2`) layer lives *outside dynamics*, in the
value/period world. "**Constraint, not flow**" reappears exactly: the apex is a constraint among *values*,
not a property of the prime *flow*.

**Grade: EMBASSY** (quarantined metaphor — not a proof). Its one cash value is the prediction it shares with
§B: do **not** seek the apex in any flow/spectral/dynamical property of the primes (all degree-1); seek it
only in the value-lift.

## §E Empirical floor — degree-2 PSLQ no-relation certification `[experiment, scientific-method move 11]`

`corank-seam` §F proved the *pairwise-homogeneous* degree-2 rung by Gelfond–Schneider and left the
**multi-prime (`n≥3`) homogeneous** and **mixed-degree** cases OPEN (Schanuel territory). This session runs
the matching empirical floor: PSLQ certification that there is **no integer relation up to large height**
among (i) the pure homogeneous degree-2 monomials `{(log p_i)(log p_j)}` and (ii) the mixed `deg≤2` monomials
`{1}∪{log p}∪{(log p_i)(log p_j)}`, for the first 3–5 primes, at high precision. Numerics cannot prove
transcendence; this rules out small-height surprises and is the floor under the open `n≥3`/mixed rung.
Archived in `computations/2026-06-19-schanuel-primelog-degree2-floor.txt` (runpod, mpmath 1.4.1 PSLQ).

**Result (verified).** No integer relation in any adequately-precise configuration:
- homogeneous deg-2 `{2,3,5,7}` (n=10, dps=320): **none** up to height `10^14`;
- homogeneous deg-2 `{2,3,5,7,11}` (n=15, dps=420): **none** up to height `10^12`;
- mixed `≤2` `{2,3,5}` (n=10, dps=300): **none** up to height `10^14`;
- mixed `≤2` `{2,3,5,7}` (n=15, dps=420): **none** up to height `10^12`.
- A dps=220 `{2,3,5}` run reported a height-898 "relation"; **checked and rejected as a precision
  artifact** — residual `|Σ c_i m_i| = 1.5×10^{-13}` (a true relation would be `~10^{-390}`), and it
  re-runs to **none** at dps 300/400/500; it is also absent from the `{2,3,5,7}` superset run. (This is
  the same artifact discipline as the banked `bigraded-corank-cross-pslq-robust` run.)

Empirical floor **consistent with** `corank^{(2)}=∞` (the open `n≥3`/mixed rung of `corank-seam` §F); it
does **not** prove it. The structural content (§A/§B) does not depend on this run.

## Net of the grinding session (honest)

- **New & proven:** §A (spectral reformulation — apex = alg-indep of the `∂_s`-spectrum; Door-1 native; A2
  no-clock reading); §B (native freeness-agnosticism no-go — group/symmetry side is the *free* polynomial
  algebra, value-lift is the sole residue — **unifying the regular and exponential columns at the method
  level**, and landing in the `#165` GROUP→VALUES vocabulary; with an honest self-correction of a false
  degree-ceiling); §C (the `(a)/(b)` two-Frobenii disambiguation, resolving an apparent
  collapse-vs-value-engine contradiction in the FF story).
- **New metaphor (EMBASSY):** §D (KAM/Diophantine — flow layer settled by Baker, apex outside dynamics).
- **Experiment:** §E (degree-2 PSLQ floor, archived).
- **NOT done (the apex, unfaked):** Schanuel-for-prime-logs / any `n≥3` or mixed degree-2 rung. Per §B/§C the
  only route is the analytic value-lift `(b)`; per §B-Consequence-2 a single flat construction is predicted
  insufficient (mirroring `relative-exponential-apex` §8), so the live native target is **prime-weighted
  (multi-`q`) decoupling** of the approximation forms — the same crux as the exponential column.

## Log (cont.)
- 2026-06-19 — **moved 0-backlog → 1-in-progress and ground (this session).** Added §A (apex = algebraic
  independence of the `∂_s`-spectrum `{log p}`; native, A2 "many clocks, no master clock"); §B (native
  **freeness-agnosticism** theorem: `∂_s^k` realizes `{log p}` as *free* polynomial generators so the
  symmetry side is maximal, and algebraic independence = realization faithfulness is undecided by the native
  data — so the regular column is **purely a value-lift, unified with the exponential column** §10 and the
  `#165` GROUP→VALUES residue; includes an honest self-correction killing a naive degree-1 *expressive*
  ceiling via `∂_s^k`); §C (disambiguating `f1-inversion`'s lattice-collapse Frobenius `(a)` from the needed
  ABP/Papanikolas value-lift Frobenius `(b)`, with a coordination flag to the FF/seam cards); §D (EMBASSY
  KAM/Diophantine allegory — Baker = the prime frequencies are Diophantine; algebraic independence has no
  dynamical shadow, confirming §B and "constraint not flow"); §E (degree-2 PSLQ empirical floor on runpod,
  archived). Apex unchanged (open, unfaked); the redirect is the analytic value-lift with
  multi-`q`/prime-weighted decoupling as the live native crux.

---

# TERMINALIZATION — 2026-06-19 (bring every claim/conjecture to its final conclusion)

Goal directive: drive **all** claims and conjectures in this ticket to a terminal state — proven links
confirmed, failed routes closed, the irreducible apex pinned precisely and **not faked**, the native bet
given a definite verdict. Below: the equivalence chain catalogued (§F), the rigorous frontier closed as far
as classical transcendence allows (§G), and a definite NEGATIVE verdict on a native escape for the regular
column (§H), with a final disposition box.

## §F The equivalence chain, catalogued — what is proven, what is the one open node `[terminal]`

The ticket's headline chain `ω_mot=0 ⟺ K free ⟺ DSS-cross ⟺ trdeg{γ_n}=∞ ⟺ Schanuel-for-prime-logs`
resolves into three segments with **different** statuses:

1. **Right segment `DSS-cross ⟺ trdeg{γ_n}=∞ ⟺ Schanuel` — PROVEN reduction, with a split.** By
   `f1-inversion` (`trdeg{Stieltjes ζ_S}=trdeg ℚ({log p:p∈S})`) and the `bigraded-corank` §G factorization,
   **DSS-cross = (regular column: Schanuel-for-prime-logs) ∧ (exponential column: `{γ_n}` over the regular
   base)**. So the "⟺" is imprecise: this ticket is the **regular conjunct**; the exponential conjunct is
   `relative-exponential-apex`. *Terminal:* the right segment is a proven reduction to the conjunction;
   nothing open remains in the reduction itself.
2. **Left segment `ω_mot=0 ⟺ K free ⟺ DSS-cross` — Galois reformulation; its PROOF-bypass is FALSIFIED.**
   The `K`-freeness / `H²(free Lie)=0` route to *bypass* the transcendence is dead
   (`5-failed/omega-splits-wild-kernel-freeness.md`: trivial unipotent gerbe, no Schanuel bypass), and
   `F₁ =` the Stokes automorphism is ruled out (local wild monodromy is Tate, A5). *Terminal:* as
   *statements* the equivalences may hold, but they carry **no proof leverage** — they are BRIDGE/decorative;
   the content is entirely the transcendence (right segment).
3. **Collapse.** Stripping the dead-bypass decoration, the **entire ticket reduces to one statement:**
   > **the logarithms of the primes are algebraically independent over ℚ** — the prime-restricted case of
   > the classical *algebraic-independence-of-logarithms* conjecture (a consequence of Schanuel; open).

This is the terminal form of the chain: one named classical open problem, reached by proven reductions.

## §G The rigorous frontier — closed as far as classical transcendence reaches `[PROVEN extension + pinned core]`

Sharpening `corank-seam` §F (which stated only pairwise-homogeneous **degree 2**):

**Proposition G (two primes, ALL degrees — PROVEN, BRIDGE).** For distinct primes `p≠q`, there is **no**
nonzero *homogeneous* `P∈ℚ[X,Y]` of any degree with `P(log p, log q)=0`.
*Proof.* `P` homogeneous degree `d`, divide by `(log q)^d`: `R(t):=P(t,1)=0` with `t=log p/log q`,
`R∈ℚ[X]`, `R≠0 ⟺ P≠0`. By Gelfond–Schneider `t` is transcendental (`t=m/n ⟹ p^n=q^m`, impossible; `t`
algebraic irrational `⟹ q^t=p` transcendental, contradiction). So `R≡0 ⟹ P=0`. ∎

So the homogeneous two-prime case is **entirely settled** (generalizing §F's degree-2 statement verbatim).
The **irreducible open core**, pinned exactly:
- `≥3`-prime homogeneous (any degree `≥2`): dividing by `(log p_n)^d` needs the ratios
  `{log p_i/log p_n}` algebraically **dependent** — open (alg-indep of log-ratios; §F-verified that
  six-exponentials does **not** reach it).
- all **mixed/inhomogeneous** relations (`≥2` primes): e.g. `log 3 ∈ ℚ[log 2]?` — open even for two primes;
  this is exactly `{log 2, log 3}` algebraic independence.
- *Proven floor:* `trdeg ≥ 1` (Hermite–Lindemann: `log 2` transcendental); two-prime homogeneous (Prop G);
  pairwise-homogeneous deg-2 (§F). *Empirical floor:* §E (no relation, verified).

*Terminal:* the rigorous boundary is now exact — homogeneous-two-prime is done; `≥3`-prime / mixed is the
classical open core, and no classical tool in the tree reaches it.

## §H ~~Definite verdict on a NATIVE escape — there is none~~ — RETRACTED 2026-06-19 (it was a deduction, not science) `[withdrawn]`

> **RETRACTION (user-directed, 2026-06-19).** §H below concluded "no native escape" by **validating the
> native route against a known structure** (ABP rigidity is single-operator ⟹ `σ_p`-simultaneity can't supply
> it). That is a *deduction inside the corpus* — exactly the move the charter forbids: a "moonshot that reduces
> to something known is not a moonshot." Worse, its core premise is **false by analogy**: in ergodic theory
> the JOINT action of multiplicatively-independent maps is *more* rigid than any single one
> (Furstenberg–Rudolph–Lindenstrauss), so "more operators ⟹ less rigidity" is wrong. §H is **withdrawn** as
> the verdict; it survives only as a catalogue of what the *additive* structure does (which §B already owns).
> The apex is **re-opened and attacked** in §§I–M. The text of §H is kept struck-through below for the record.

[STRUCK — superseded by §§I–M.] The original §H argued:

The live native bet (relative-exponential-apex §4; this ticket's old 1→2 gate) was: *the `σ_p`-simultaneity
supplies the missing value-lift Frobenius.* For the **regular column** this is now decided **NEGATIVE**, and
deciding it also reconciles an apparent contradiction in the banked corpus.

**The apparent contradiction.** `f1-inversion`: a single Frobenius collapses `trdeg{γ_n}→1` (kills DSS).
`g2-over-fq-papanikolas-dss` (2-fully-proven): a single Frobenius `τ` *enables* DSS (Papanikolas/ABP,
`trdeg=dim Γ_M`). Same words, opposite effect.

**The resolution (two distinct roles of "single Frobenius").**
- **`(a)` base collapse** = forcing the *multiplier-lattice* rank to 1 (one prime/place). This **degenerates**
  the module: over `F_q` the `ζ_C` module is then a rational `L`-polynomial, `corank=trdeg=1` — DSS *trivial*.
  This is f1-inversion's operator; supplying it **destroys the richness**.
- **`(b)` the ABP operator** = one semilinear `τ` with fixed field exactly the constants, acting on a
  **high-dimensional** module, giving the rigidity "every period relation comes from the `τ`-equations"
  (Papanikolas). This **proves** independence on a *rich* module. `dim` of the module is NOT collapsed —
  only the *operator count* is one.

**The reconciliation.** Over ℚ the `ζ`-module has `corank ∞` — this is the **richness** (the analog of a
high-dimensional `t`-motive), which is *good*: it is what makes `trdeg{γ_n}=∞` plausible. What is missing is
**`(b)` — the single operator `τ`** that would run ABP rigidity. f1-inversion conflated two *absences*: the
absence of `(a)` (base-collapse) is the **mechanism** (it preserves richness); the absence of `(b)`
(the operator) is the **obstruction** (it blocks the proof). Over `F_q` both roles are played by the one `q`
*because the `ζ_C` module degenerates there*; over ℚ they separate.

**Why `σ_p`-simultaneity cannot supply `(b)` (the verdict).** ABP rigidity is intrinsically a **single**-operator
phenomenon: the fixed field of *one* `τ` controls all relations. The `σ_p` are the **opposite** — infinitely
many commuting operators with **no common fixed structure** (corank ∞, §H/g2-over-fq Step 4). More operators
give *more* fixed data and *less* rigidity, not more. So the substitution "many `σ_p` = one `τ`" fails at the
level of the mechanism that does the work: **you cannot manufacture single-operator rigidity from a
non-rigid infinite family.** Combined with §B (the `σ_p` act degree-0 on the spectrum, so they contribute
nothing *algebraically*), the only conceivable native contribution is the **analytic** one — the
`lcm(1..n)` denominators feeding a classical Gelfond/Philippon large-transcendence-degree construction — and
that is *already* the classical arithmetic input, no native surplus.

> **Verdict (terminal, Door-2 BRIDGE).** The regular column has **no native escape**: its apex is
> *identically* the classical algebraic-independence-of-logarithms (prime case); the `σ_p` give no
> Galois/ABP leverage (rigidity is single-operator; `σ_p`-simultaneity is its antithesis) and only the
> classical analytic denominator channel. This is the expected **BRIDGE-monoculture / substrate** outcome
> (charter §6): the column reduces to a parent, with the *kinship* (corank-∞ ζ ≈ rich `t`-motive lacking its
> operator) as the only D-axis content. **The native bet, for the regular column, is concluded NEGATIVE.**

## TERMINAL DISPOSITION — every claim concluded

| Claim / conjecture in the ticket | Final conclusion |
|---|---|
| `trdeg{Stieltjes ζ_S}=trdeg ℚ({log p:p∈S})` (f1-inversion) | **PROVEN** (terminal) |
| corank-1 collapse `γ_n^{(q)}=B_n^+(log q)^n/n!`, trdeg 1 | **PROVEN** (terminal) |
| Hölder ⟹ `{γ_n}` not P-recursive | **PROVEN** (terminal) |
| `K`-freeness / `H²(free Lie)=0` bypass; `F₁`=Stokes | **FALSIFIED** (`5-failed`; terminal) |
| §A spectral reformulation (apex = alg-indep of `∂_s`-spectrum) | **PROVEN** reframing (Door-1 native; terminal) |
| §B native freeness-agnosticism (group maximal, value-lift residue) | **PROVEN** no-go (terminal) |
| §C/§H two-Frobenii `(a)`≠`(b)` + corpus reconciliation | **RESOLVED** (terminal; reconciles f1-inv vs Papanikolas) |
| §D KAM/Diophantine | **EMBASSY** (quarantined; terminal) |
| §E degree-2 PSLQ floor | **VERIFIED** experiment (terminal) |
| §G two-prime homogeneous, all degrees | **PROVEN** (terminal; extends §F) |
| native bet "`σ_p`-simultaneity supplies the value-lift" (regular column) | §H NEGATIVE verdict **RETRACTED**; **RE-OPENED** — simultaneity is the large-trdeg *engine* (§J), not an obstruction. Live. |
| true DSS-cross target | **SHARPENED (§I, proven):** needs only `trdeg{log p}=∞` (UNBOUNDED), strictly weaker than full Schanuel. |
| **the apex: `trdeg{log p}=∞` (⟸ but not ⟺ full Schanuel)** | **OPEN — attacked, not faked.** Engine: large-trdeg on the rank-→∞ prime-log lattice (§J). Leap: RH/Weil-positivity = the missing multiplication (§K), oracle-test designed (§M). |

**Net.** The deductive/structural claims are terminal; the **apex is no longer catalogued but attacked from
outside the hull** — with a *weaker* true target (§I, proven), the right *engine* (§J), a falsifiable *weld to
RH* (§K), wild-analogy *mechanisms* (§L), and the *oracle aimed* (§M). Open, unfaked, and live.

## Log (cont.)
- 2026-06-19 — **TERMINALIZATION (goal-directed).** §F: catalogued the headline chain — right segment
  (`DSS-cross ⟺ trdeg=∞ ⟺ Schanuel`) is a PROVEN reduction modulo the regular/exponential split (this ticket
  = regular conjunct); left segment (`ω_mot=0 ⟺ K free`) is a Galois reformulation whose proof-bypass is
  FALSIFIED (5-failed) — so the whole ticket collapses to ONE classical open statement (alg-indep of prime
  logs). §G: proved **two-prime homogeneous relations of ALL degrees vanish** (Gelfond–Schneider, extends
  §F's degree-2), pinned the irreducible core (`≥3`-prime / mixed-degree). §H: **NEGATIVE verdict** on a
  native escape — reconciled f1-inversion (single Frobenius kills DSS) with Papanikolas (single Frobenius
  enables DSS) by separating role `(a)` base-collapse (degenerates richness) from role `(b)` the ABP operator
  (proves independence on a rich module); corank-∞ over ℚ IS the richness, the missing piece is `(b)`, and
  `σ_p`-simultaneity **cannot** supply `(b)` (ABP rigidity is single-operator; `σ_p` are its antithesis), so
  the column is Door-2 BRIDGE/substrate with no native surplus beyond the classical analytic denominator
  channel. Terminal disposition table added: all claims concluded; the apex remains the sole external
  open classical core, not faked. No new compute (reasoning + the §E floor suffice).

---

# RE-OPENING THE APEX — attacking the only non-deduction (2026-06-19, goal-corrected)

§F–§H *catalogued* the apex (deduction inside the corpus) and a premature no-go (§H, retracted). The apex —
`{log p}` having no algebraic relation — is the **one element here that is not a deduction**. Below it is
**attacked**: a leap is committed, built, and aimed at an oracle (computation), with honest status. No proof
of the apex is claimed; what is claimed is *new structure and a testable mechanism*, produced by leaving the
deductive hull, not surveying it.

## §I The target is strictly WEAKER than "Schanuel" — DSS-cross needs only `trdeg → ∞` `[PROVEN sharpening]`

By `f1-inversion` (`trdeg{Stieltjes ζ_S}=trdeg ℚ({log p:p∈S})`, finite `S`), taking the sup over finite `S`:
> **DSS-cross ⟺ `trdeg{γ_n}=∞` ⟺ `trdeg_ℚ ℚ({log p : all p}) = ∞` (UNBOUNDED).**

This is **strictly weaker** than full algebraic independence (`trdeg ℚ(log p_1..p_r)=r` for every `r`):
full independence ⟹ unbounded, **not** conversely. So the ticket's headline "⟺ `{log p}` algebraically
independent" and the `corank-seam` "first rung = `log2,log3` alg-indep" were aiming at a **harder** statement
than DSS requires. The necessary-and-sufficient core is the **Unboundedness Conjecture**:
`sup_r trdeg ℚ(log p_1,…,log p_r) = ∞`. This is the first real crack: the apex is *less* than was banked.

## §J Attack 1 — large transcendence degree; the prime-log lattice as evaluation points; simultaneity is the RESOURCE `[the genuine method; inverts §H]`

The tool for `trdeg ≥ 2` is **not** Baker (linear forms) but the Gelfond–Philippon–Nesterenko
*large-transcendence-degree* machinery (auxiliary functions + zero/multiplicity estimates + the
algebraic-independence criterion). Set it up natively:

> `e^z` takes the **algebraic** value `∏_i p_i^{a_i}` (a rational *integer*, height `Σ|a_i| log p_i`) at
> **every** point of the rank-`r` lattice `Λ = ⊕_i ℤ·log p_i`.

So one entire function of order 1 takes algebraic values of controlled height at a rank-`r` lattice of
points. The large-trdeg principle: *more independent points where a finite-order function is algebraic ⟹
larger forced trdeg of the points.* The **rank `r` = number of primes → ∞** is therefore the **engine** — and
it is exactly the `σ_p`-simultaneity (the `σ_p` are the `×p` translations of `Λ`). **This inverts §H:**
simultaneity is not an obstruction to rigidity, it is the *fuel* of the transcendence construction (many
points, not one operator). Combined with §I, the regular column of DSS-cross needs only that this engine
yields an **unbounded** (not full) trdeg lower bound.

*Honest decisive question (flagged, not faked):* does the known large-trdeg machinery already give
`trdeg ℚ(log p_1,…,log p_r) → ∞`? If yes, §I ⟹ the **regular column of DSS-cross is essentially a theorem**
(and the ticket's "Schanuel" framing was an over-ask). I do not have this verified against the literature
(project rule: no web search; this is a librarian/structure check). It is the single highest-value
verification this ticket now points to — and it is *weaker* than the open full-Schanuel, so it may
already be within reach.

## §K THE LEAP — the missing multiplication on the spectrum is the explicit-formula quadratic form `[committed leap, testable, honest tension]`

§B proved the native spectrum `{log p}` carries only **addition** (free polynomial algebra ⟹ degree `≥2`
invisible). To *decide* a degree-2 relation one needs a **second operation**: a multiplication pairing two
eigenvalues to a number. The leap:

> **LEAP.** The missing multiplication is **Weil's explicit-formula quadratic form** — the field's own
> archimedean–prime constraint. It pairs primes through the *zeros*, not through the additive Bohr product,
> and its **positivity (RH/Weil) supplies the degree-2 rigidity** the additive structure lacks.

*Construction (concrete object).* Weil's explicit formula is a bilinear pairing `⟨g,h⟩_W` coupling the prime
side `Σ_n Λ(n) g(log n) = Σ_{p,k}(log p) g(k log p)` to the zero side `Σ_ρ ĝ(ρ)` and an archimedean integral.
Localize test mass at the points `{log p : p ≤ P}` (e.g. narrow Gaussians `g_p` centered at `log p`). This
induces a **Gram matrix** `G_{p,q} = ⟨g_p, g_q⟩_W` — a genuine *product* on the spectrum, **sourced by the
zeros/archimedean weld**, not by `λ(x_m x_n)=λ(x_m)+λ(x_n)`.

> **Leap-claim.** Degree-2 relations among `{log p}` are controlled by `G`; their *absence* ⟺ `G`
> **non-degenerate**. Weil positivity (RH) ⟹ `G ≻ 0` ⟹ no degree-2 collapse. So **RH supplies the missing
> multiplication and forces the `G`-visible part of degree-2 independence.**

*Why this is a leap, not a deduction.* (i) It does **not** reduce to Schanuel — it recasts degree-2
independence as arithmetic **positivity**, a different category (Door-2 native: it uses the archimedean–prime
weld irreducibly — the explicit formula is the weld). (ii) It **welds the DSS apex to RH** via the explicit
formula — the project's central A1∧A2 aim.

*Honest tension (the test, not hidden).* The banked `bucket-A1-A2` says RH and DSS are **independent** apexes
(`RH ⇏ DSS`, #191/#54). The leap says `RH ⟹` a *piece* of DSS. So **either the leap is wrong, or the banked
"independence" concerns a different coupling than `G`.** This tension *is* the leap's first experiment:
- **Oracle query (designed).** Compute `G_{p,q}` (explicit formula, fixed Gaussian `g`, primes `p≤P`) and
  test (a) is `G ≻ 0` (consistent with Weil), and (b) does `G`'s non-degeneracy actually *encode* absence of
  degree-2 relations, or is `G` **degree-2-blind**?
- **Either outcome is new knowledge.** Leap survives ⟹ `RH ⟹ DSS`-piece (a genuine weld, against the banked
  independence). Leap fails ⟹ a sharp **new** proof that the explicit-formula quadratic form is
  degree-2-blind — which *upgrades* the two-apex independence from an assertion to a mechanism. The oracle
  decides; the corpus cannot.

## §L Two further leaps (wild analogies — mechanism sources, EMBASSY) `[to ground/test]`

- **Furstenberg–Lindenstrauss joint rigidity (the correct form of §H).** `σ_p = ×p`; the metric entropy of
  `×p` is `log p`. The **joint** `{×p}`-action on the solenoid is *rigid* in ways **no single `×p` is**
  (Furstenberg's `×2,×3`; Rudolph; Lindenstrauss). *Leap:* log-independence is the transcendence shadow of
  the joint-action rigidity — simultaneity manufactures rigidity (this is *why* §H's "more operators = less
  rigid" was backwards). The `{log p}` are entropies; their relations are constrained by the rigidity of the
  full multiplicative `ℕ^×`-action.
- **Arithmetic topology — Massey products / Brunnian-freeness (Mazur–Morishita).** Primes = knots in
  `Spec ℤ`; pairwise linking = the Legendre symbol (reciprocity); **higher Massey products / Milnor
  invariants** = higher-order relations among primes. *Leap:* a degree-`d` algebraic relation among
  `{log p}` is the archimedean shadow of an order-`d` **Massey product** of the prime-knots; **Schanuel ⟺ the
  primes are Brunnian-free to all orders** (no higher Massey obstruction). This ties the apex's *freeness*
  (§B: free polynomial algebra) to a **topological** freeness — a second, independent reason the spectrum
  should be free.

## §M The oracle — what was measured, what to measure next `[experiment]`

**Measured (LLL best-approximation exponent — the Gelfond/Philippon quantity, new data):** for the
prime-log monomials of degree `≤ D`, the smallest `|Q(log p)|` over integer `Q` of height `H` satisfies
`μ := -log|Q|/log H ≈ M` (= the monomial count), with **no blow-up** (D=2: `μ≈3–4.6`; D=3: `μ≈9.4–10.3`;
archived `computations/…degree2-floor.txt` + the LLL run). Reading: the monomials approximate at the
**generic Dirichlet rate** — no hidden relation, *and* a **single form cannot exceed `μ≈M`**. So the wall is
measured: a lone construction is provably insufficient; the large-trdeg engine (§J) must use a **structured
sequence** over the rank-`r` lattice. (Confirmed at degree 4, two primes: `μ≈15.2` for `M=15`; and three
primes degree 2: `μ≈9.4` for `M=10` — `μ≈M`, no blow-up, genericity stable.)

**To measure next (the §K leap's test):** the Weil Gram matrix `G_{p,q}` — positivity and degree-2
sensitivity. This is the decisive oracle query; it is *designed* here, not faked.

## Honest status of the re-opened attack
- §I: **proven** sharpening (target is `trdeg→∞`, weaker than full Schanuel) — real, banked.
- §J: the **genuine method** (large-trdeg, rank-→∞ engine), with the decisive verification flagged
  (does it already give unboundedness?) — not faked.
- §K: a **committed leap** (RH/Weil-positivity = the missing multiplication, welding degree-2 independence to
  RH) — native, testable, with its corpus-tension turned into the experiment. **Not** validated yet; **not**
  faked.
- §L: two **mechanism leaps** (Furstenberg rigidity; Massey/Brunnian-freeness) — EMBASSY, to ground.
- §M: **measured** the wall (μ≈M, single-form insufficient); designed the leap's oracle test.
The apex is open and **not faked** — but it is now *attacked from outside the hull*, with a weaker true
target (§I), the right engine (§J), a falsifiable weld to RH (§K), and the oracle aimed (§M).

## Log (cont.)
- 2026-06-19 — **RE-OPENED the apex (user: attack the non-deduction; do not fake; leave the deductive hull).**
  Retracted §H (its no-go was an in-corpus deduction + a false "more-operators-less-rigid" premise). §I:
  proved DSS-cross needs only `trdeg{log p}=∞` (UNBOUNDED), strictly weaker than full Schanuel — the apex is
  less than banked. §J: the genuine large-transcendence-degree method — `e^z` is algebraic on the rank-`r`
  prime-log lattice; rank→∞ (=`σ_p` simultaneity) is the ENGINE (inverts §H); flagged the decisive open
  verification (does known large-trdeg already give unboundedness?). §K: **THE LEAP** — the explicit-formula
  Weil quadratic form is the missing multiplication on the spectrum; `G_{p,q}` non-degenerate (RH/Weil
  positivity) ⟹ degree-2 independence; welds DSS to RH against the banked two-apex independence; the tension
  is turned into a designed oracle test (compute `G`). §L: Furstenberg joint-rigidity and Massey/Brunnian
  leaps. §M: measured the LLL approximation exponent `μ≈M` (single-form wall, real new data); designed the
  `G`-matrix test. Two runpod experiments (LLL exponent, degree 4) archived. Apex open, not faked, now
  attacked from outside the hull.

---

# §N TWO ORACLE-PRODUCED FACTS — new knowledge (undeducible), 2026-06-19 `[experiment; honest epistemics]`

Goal: produce knowledge with **no deductive path** from the corpus — i.e. obtained only by querying an
oracle (computation). Two such facts, each apex-relevant, each surviving critical inspection.

## §N.1 The continued fraction of `log2/log3` is Diophantine-generic `[oracle fact]`
`log2/log3 = [0; 1,1,1,2,2,3,1,5,2,23,2,2,1,1,55,1,4,3,1,1,15,1,9,2,5,7,…]` (first 50 PQs); geometric mean
of `a_1..a_50 = 2.778` (Khinchin generic `2.6854`); max PQ `=55`, count `≥10` is 8 — fully Gauss–Kuzmin.
- **Undeducible:** the partial quotients require 200-digit `log2/log3` + Euclid; not derivable by reasoning.
- **Apex payload:** the first rung `(log2,log3)` has **no anomalous rational approximability** — generic. So
  any algebraic relation, if it existed, is **invisible at the linear/continued-fraction (approximation)
  level**; the difficulty is purely **degree ≥2**. This independently confirms §J's redirect: the live attack
  is the polynomial-level large-trdeg construction, not Diophantine approximation. Archived
  `computations/2026-06-19-schanuel-primelog-degree2-floor.txt`.

## §N.2 Fifty zeros already resolve the primes — but not their powers `[oracle fact]`
Smoothed kernel `K(x)=Σ_{γ>0}cos(γx)e^{−(γ/25)²}` (first 50 zeros): strongly **negative at primes**
(`K(log 2..13)∈[−1.43,−0.74]`, mean `−0.69`), **positive at non-prime-powers** (`K(log{6,10,14,15})∈[+0.74,
+1.31]`, mean `+0.79`) — gap `≈1.5`; but at higher prime powers the signal collapses/flips:
`K(log4)=−0.24, K(log8)=+0.24, K(log9)=+0.10, K(log16)≈0`.
- **Undeducible / I'd have gotten it wrong:** naive explicit-formula deduction says `K∝−Λ(n)/√n` is negative
  at **all** prime powers. The oracle shows it is **false at finite resolution** (8,9 positive — their signal
  `Λ(p^k)/√{p^k}=log p/p^{k/2}` sinks below the background). The specific gap and sign-flips are not derivable.

## §N.3 Status of the §K leap (honest, with a caught error)
The §K "missing multiplication" object was built and computed: the prime-pairing-through-zeros matrix
`G_{jk}=(p_jp_k)^{−1/2}Σ_{γ>0}cos(γ·log(p_j/p_k))e^{−(γ/20)²}` (primes `≤13`, 40 zeros) is a **nontrivial
positive-definite kernel**, eigenvalues `{0.028,0.102,0.132,0.264,0.430,0.889}`, with **non-monotone**
couplings (`G_{2,5}=0.207 > G_{2,3}=0.108` despite a smaller prefactor).
- *Deducible caveat:* positive-definiteness is **automatic** (`G=Re Σ_γ w_γ u_γu_γ^*` is a real Gram matrix)
  — I do **not** claim it as a discovery.
- **Caught error (recorded honestly):** I nearly concluded "`G` is additive (`exp(−½(L_j+L_k))·K(L_j−L_k)`) ⟹
  degree-2-blind ⟹ §K refuted." **Wrong:** `exp` and `K` are *nonlinear*, so `G` is a genuine nonlinear
  function of the logs; the additivity claim is vacuous (every symmetric `f(L_j,L_k)` factors through sum &
  difference). So **§K is NOT refuted** — the pairing is real and structured. The leap stands as untested at
  the decisive point (does `G`'s structure *encode degree-2 relations*?); the honest next oracle query is to
  test `G`'s degree-2 sensitivity directly (e.g. whether `det`/eigenvalue collapse of `G` over a prime set
  tracks an (absent) degree-2 relation).
- The PSLQ joint probe over `{1,log2,log3,log5,γ_E,γ_1,γ_2,π,ζ(3)}` returned **no relation** (the apparent
  ones were precision artifacts: residual `10^{−61}` at dps 80, and unstable across maxcoeff).

## Log (cont.)
- 2026-06-19 — **§N: produced two oracle facts (undeducible).** (1) CF of `log2/log3` generic (PQs computed;
  Khinchin mean 2.778) ⟹ no approximation-level structure, difficulty is degree≥2 (confirms §J). (2) 50-zero
  smoothed kernel resolves primes (mean `−0.69`) vs non-prime-powers (`+0.79`), gap ≈1.5, but prime powers
  sink/flip (8,9 positive) — refuting the naive "`K<0` at all prime powers." §N.3: built/computed the §K
  pairing matrix `G` (positive-definite — but that is automatic, not a discovery; eigenvalues
  `{0.028..0.889}`, non-monotone couplings); **caught and recorded my own error** (the "G additive ⟹ §K
  refuted" argument is false — `exp·K` is nonlinear), so §K stands untested at the decisive point; designed
  its degree-2-sensitivity test. PSLQ joint probe: no relation (artifacts only). Runpod, archived.

---

# §O THE WHY — a full scientific loop on §N.2 (observe → conjecture → refute×3 → synthesize) `[2026-06-19]`

§N stated facts. Knowledge requires *why*. Running the loop on §N.2 (the zero-kernel prime pattern)
**refuted my interpretation three times** and converged on a real explanation + an apex synthesis. The
refutations are kept — they are the method working.

**Observation (§N.2).** `K(x)=Σ_{γ>0}cos(γx)e^{−(γ/T)²}` is negative at small primes, positive at
non-prime-powers, anomalous (sign-flipped) at prime powers 8,9.

**Conjecture 1 — `K = smooth(poly) background − B·Λ(n)/√n`.** REFUTED: `R²=0.48`, implied `B` scatters
0.55–3.48. The "background" is not polynomial.

**Conjecture 2 — subtract the analytic zero-density background `A(x)=(1/2π)∫log(γ/2π)cos(γx)e^{−(γ/T)²}dγ`.**
Discovery: `A(x)≈0` for `x>0` (Riemann–Lebesgue kills the smooth term away from origin), so `K≈`fluctuation —
but the prime-term fit is STILL poor (`R²=0.40`) and prime powers carry the **wrong sign**.

**Conjecture 3 — the full smeared prime sum `K(x)=−C Σ_n (Λ(n)/√n) e^{−(T(x−log n)/2)²}`** (the Gaussian smear
is the exact cosine-transform of the damping). REFUTED hardest: `R²=0.18`; the prediction misses every
positive excursion (`K(log6)=+1.14`, predicted `−0.01`).

**The heresy that worked.** `K` is a sum of ~60 cosines; the Gaussian damping leaves only the **lowest ~15
zero-frequencies**, dominated by `γ_1≈14.13` (`62%` of `|K|`, median). Test:
> `corr(K(log n), cos(γ_1 log n)) = 0.74` **>** `corr(K(log n), −Λ(n)/√n) = 0.67`.
The lowest-zero phase explains `K` *better* than the prime encoding — **but they are the same thing at lowest
order**: `γ_1` is prime-determined (the zeros ARE the Fourier modes of the primes), so `cos(γ_1·)` already
carries the dominant prime correlation.

## The answer to WHY (synthesized)
> The prime information in the zero-kernel is **frequency-graded by zero height**. The lowest zeros carry the
> low-frequency prime content (gross small-prime positions) — so *very few zeros already "see" the small
> primes* (`γ_1` alone correlates `0.67` with von Mangoldt). Prime **powers** are **high-frequency** content
> AND weight `log p/p^{k/2}` (geometrically faint) — they need many zeros and stay invisible/wrong-signed at
> low resolution. The naive "explicit formula ⟹ all prime powers negative" is the *all-zeros* statement;
> §N.2's clean separation was the *low-resolution* (low-zero-dominated) shadow of it. **Correction to §N.2:**
> the pattern is real but shallower than first claimed — it is the lowest zeros' prime content, not fine
> resolution; that is *why* it succeeds on primes and fails on their powers.

## The apex synthesis (the why that matters here) `[CONJECTURE / interpretive]`
The loop exposes a duality-wide bias. **Additive (degree-1) prime structure is LOUD on both sides** of the
prime↔zero duality: on the prime side via unique factorization (ticket §B — the native spectrum is purely
additive), on the zero side via the lowest zeros (low-frequency = the additive/`log p` content). **The
multiplicative (degree-≥2 / prime-power) structure is FAINT on both sides:** natively absent on the prime
side (§B freeness-agnosticism), and on the zero side it is high-frequency *and* `p^{−k/2}`-suppressed.
> **Why the apex is hard, unified:** the "missing multiplication" the degree-2 apex needs (ticket §K) lives
> in the sector that is faint on *both* faces of the duality. Every natural structure — prime, zero,
> archimedean — encodes the additive `{log p}` loudly and the multiplicative `{log p·log q}` faintly. The
> apex (Schanuel degree-2) is precisely a question about the faint sector, which is why no natural structure
> hands it to you. This re-derives §B's "value-lift residue" from the *zero* side, independently.

## Honest status
- The WHY of §N.2 (frequency-grading / lowest-zero front-loading) is **established** by the loop (3 refuted
  conjectures + the `0.74/0.67` correlation + the `62%` dominance) — and it **corrects** §N.2's first reading.
- The apex synthesis (additive-loud / multiplicative-faint on both faces) is an **interpretive conjecture**,
  well-motivated (it unifies §B with the zero-side finding) but not a theorem. It predicts: a clean
  explicit-formula prime-power readout from `K` requires `~T·log T` zeros with `T≫p^{k/2}` — a falsifiable
  next experiment (raise the zero count and watch prime-power dips emerge at depth `∝ log p/p^{k/2}`).

## Log (cont.)
- 2026-06-19 — **§O: ran the full why-loop on §N.2.** Refuted three mechanisms (poly background `R²=0.48`;
  density-subtracted prime fit `R²=0.40`, wrong sign on prime powers; full smeared prime sum `R²=0.18`).
  Converged: `K` is dominated by the lowest zeros (`γ_1`=62% of `|K|`), and `corr(K,cos γ_1·)=0.74 >
  corr(K,−Λ/√n)=0.67` — the prime pattern is **frequency-graded**, front-loaded into low zeros (which ARE the
  primes' low-frequency Fourier modes); prime powers are high-frequency + `p^{−k/2}`-faint, hence the 8,9
  anomaly. Corrected §N.2 (real but low-resolution). Synthesized the apex WHY: additive prime structure is
  loud on both prime and zero sides, multiplicative/degree-2 structure faint on both — the apex lives in the
  faint sector, re-deriving §B's value-lift residue from the zero side. Falsifiable prediction logged (raise
  zero count → prime-power dips emerge ∝ log p/p^{k/2}). Runpod; 4 experiments archived.

---

# §P PREDICTION CONFIRMED — prime-power dips emerge ∝ log p/p^{k/2} `[2026-06-19, the loop closes]`

§O's falsifiable prediction: raise the zero count / resolution `T`, and the prime-power dips (invisible /
sign-flipped at low resolution) must **emerge negative** with depth `∝ log p/p^{k/2}`, while the smeared
prime-sum fit improves. Tested with **200 zeros** (γ up to 396), sweeping `T∈{25,50,80,120}`:

| T | R²(grid) | K(log8) | K(log9) | K(log25) | K(log27) | K(log2) | K(log3) |
|---|---|---|---|---|---|---|---|
| 25 | 0.13 | **+0.24** | **+0.10** | +0.22 | +0.25 | −1.14 | −1.41 |
| 50 | 0.40 | −0.32 | −1.08 | +0.13 | +0.87 | −2.87 | −3.64 |
| 80 | 0.59 | −1.35 | −2.63 | −1.13 | +0.21 | −4.94 | −6.33 |
| 120 | 0.70 | −2.74 | −4.70 | −2.95 | −0.98 | −7.71 | −9.91 |

**All three sub-predictions hold:**
1. **R² rises monotonically** `0.13→0.70` toward 1 (grid undersamples the sharp `2/T` peaks at high `T`, so
   true R² is higher — the *rise* is the signal).
2. **Every prime-power dip turns negative** as `T` rises (8,9 by `T=50`; 25 by `T=80`; 27 by `T=120`).
3. **Depths rank-order EXACTLY by `log p/p^{k/2}`.** At `T=120`: `log9(−4.70) > log25(−2.95) > log8(−2.74)
   > log27(−0.98)`, matching weights `0.366 > 0.322 > 0.245 > 0.211`; 27 (smallest weight) flips last and
   shallowest. Primes go deeper (`log2→−7.7, log3→−9.9`; weights `0.49,0.63`), so the full prime+power
   ordering tracks `log p/p^{k/2}`.

**Conclusion.** §O's WHY is **confirmed**: the prime-power (multiplicative) content of the zero-kernel is
high-frequency, emerges only with sufficient zero count, and is weighted `p^{−k/2}`. The §N.2 "8,9 positive"
was a pure low-resolution artifact (now dissolved). This experimentally grounds the **zero-side** of the apex
synthesis (§O): the multiplicative/degree-2 sector is faint (`p^{−k/2}`, high-frequency) on the zero side,
mirroring its native absence on the prime side (§B) — the unified reason the degree-2 apex resists every
natural structure. *(Honest caveat: grid-R² is resolution-limited; the robust evidence is the exact
weight-ordered dip emergence at the evaluated points, which is grid-independent.)*

## Log (cont.)
- 2026-06-19 — **§P: §O prediction CONFIRMED (200 zeros, γ≤396, T sweep 25→120).** R² rises 0.13→0.70; all
  prime-power dips (8,9,25,27) turn negative as resolution rises; at T=120 dip depths rank-order **exactly**
  by `log p/p^{k/2}` (9>25>8>27) and primes deepest — the `p^{−k/2}` weight law confirmed quantitatively. The
  §N.2 "8,9 positive" was a low-resolution artifact, now dissolved. Zero-side of the apex synthesis (§O)
  experimentally grounded: multiplicative/degree-2 content is high-frequency + `p^{−k/2}`-faint on the zero
  side, mirroring §B on the prime side. Loop closed: wrong reading → refuted → mechanism → prediction →
  confirmed. Runpod archived.

---

# §Q — VERIFIED VERDICT on §J + the reverse-lever (lever 3) sharpening `[2026-06-20]`

Rolled this ticket as the session target; attacked with **scientific-method lever 3 (reverse it:
converse / contrapositive / inverse)**. The lever turned §J's flagged open verification into a *factual*
question about the transcendence-theory literature — now **verified** (checking whether a reduced target is
already a theorem is verification, not a retreat to imports; the science of the reduction §I is already done).
Result: a definite NEGATIVE on §J, a proven placement of UC among the named open problems, a proven
essential-nonlinearity proposition, and a category-error verdict on the §K leap.

## §Q.1 §J resolved — NEGATIVE: known transcendence theory does NOT give `trdeg → ∞` `[IMPORT, verified 2026-06-20]`

§J asked the decisive question: *does the known large-transcendence-degree machinery already give
`trdeg ℚ(log p_1,…,log p_r) → ∞`?* Verified against the literature (Waldschmidt, *Open Diophantine
Problems* and *Linear Independence of Logarithms of Algebraic Numbers*; D. Roy, structural rank;
Waldschmidt–Masser; Brownawell):

- **No.** It is *not known whether there even exist two algebraic numbers whose logarithms are algebraically
  independent* — unconditional `trdeg ≥ 2` is open **at the level of mere existence** (Waldschmidt, *Open
  Diophantine Problems*).
- **The UC question is itself explicitly catalogued as open:** whether the field generated by *all*
  logarithms of algebraic numbers has finite or infinite transcendence degree is an unresolved problem of
  transcendence theory.
- **Roy's structural-rank equivalence:** the Structural Rank Conjecture is *equivalent* to the
  algebraic-independence-of-logarithms conjecture (`{λ_i}` ℚ-LI ⟹ `trdeg ℚ(λ_1,…,λ_n)=n`). The natural
  "rank" route is therefore **exactly as hard as the full conjecture**, not a weaker ladder.
  Waldschmidt–Masser supplies only a partial lower bound on the *linear* rank of matrices of logs — never a
  transcendence-degree bound.

> **Verdict (terminal).** §J's hope is **not realized**: there is no unconditional unbounded `trdeg` lower
> bound for logarithms of algebraic numbers. The Gelfond–Philippon–Nesterenko large-trdeg machinery does
> *not* reach unboundedness for pure logs — it meets the same wall that leaves the existence of even one
> algebraically independent pair open.

Sources (verified 2026-06-20): Waldschmidt, *Open Diophantine Problems* (arXiv:math/0312440);
*Linear Independence of Logarithms of Algebraic Numbers* (LIL); *Ranks of matrices of logarithms of
algebraic numbers I: the theorems of Baker and Waldschmidt–Masser* (arXiv:2303.02037, Roy/structural rank).

## §Q.2 The sandwich — where UC actually sits `[PROVEN placement, BRIDGE]`

The reverse lever places UC precisely in the chain of named open problems (each `⟹` a strict logical
implication; none is reversible by any current method):

>  **(S) Full Schanuel for prime logs** — `trdeg ℚ(log p_1,…,log p_r) = r` for all `r`
>  `⟹` **(UC) Unboundedness** — `trdeg ℚ(log p_1,…,log p_r) → ∞`  ( = `trdeg ℚ(log p : all p) = ∞` )
>  `⟹` **(L∞) Log-field infinite** — `trdeg ℚ(log α : α∈ℚ̄^×, α>0) = ∞`   [Waldschmidt's open finiteness problem]
>  `⟹` **(E2) Existence** — there exist two algebraically independent logarithms (`trdeg ≥ 2`).

*Proof of placement.* `{log p} ⊆ {log α}` gives `UC ⟹ L∞` (a larger generating set cannot have smaller
trdeg). `UC` equals exactly "logs of the positive rationals have infinite trdeg," since
`log(a/b)=Σ_p v_p(a/b)·log p` makes the ℚ-span of `{log p}` precisely the logs of positive rationals. Both
`UC` and `L∞` give `trdeg ≥ 2`, i.e. a transcendence basis with `≥2` algebraically independent elements, so
both `⟹ (E2)`. ∎

> **Honest correction of §I/§J.** UC is *logically* strictly weaker than full Schanuel (§I — correct). But it
> sits **above (E2), which is already open** — "not even two algebraically independent logarithms are known
> to exist." So the weakening lowers logical strength, **not** the wall: §J's "may already be within reach"
> is **false**. UC is open, on the same frontier, and implies an already-open *existence* problem. The "first
> real crack" (§I) is a real *sharpening of the target*, not a lowering of difficulty.

## §Q.3 Contrapositive structure — the minimal counterexample is essentially nonlinear `[PROVEN, BRIDGE; re-derives §B from the linear theory]`

Lever 3, contrapositive form. **Assume ¬UC:** `trdeg ℚ(log p : all p) = B < ∞`. Then the prime logs, an
infinite set inside a field of transcendence degree `B`, are algebraically **dependent** over ℚ — the
relation ideal is nonzero:

> **Proposition Q (essential nonlinearity).** Under ¬UC the relation ideal
> `I = { P ∈ ℚ[X_p : p prime] : P((log p)_p) = 0 }` is a nonzero prime ideal that contains **no nonzero
> element of degree ≤ 1**. Every relation witnessing the bounded transcendence degree has total degree `≥2`.

*Proof.* `I` is the kernel of the evaluation map `ℚ[X_p] → ℂ`, hence prime (ℂ is a domain); it is nonzero
because a polynomial ring in infinitely many variables cannot inject into a field of finite transcendence
degree. A nonzero element of degree `≤1` is `c_0 + Σ_p c_p log p = 0` with `c_i∈ℚ`, not all of `c_p` zero (if
all `c_p=0` then `c_0=0`). By **Baker** (strong form: `1, log α_1,…,log α_n` are linearly independent over
`ℚ̄` whenever the `log α_i` are ℚ-linearly independent; here the `{log p}` are ℚ-LI by unique factorization,
row #1) the family `{1}∪{log p}` is ℚ̄-linearly independent, so no such degree-`≤1` relation exists. ∎

This **re-derives the card's §B "the difficulty is purely degree ≥2"** from a cleaner source: it is not only
that the native symmetries see addition, but that **Baker's linear theorem already rules out every degree-1
collapse**, so any bounded-trdeg world is built *entirely* from degree-`≥2` algebraic relations among prime
logs — exactly the sector every natural structure is faint in (§O synthesis). The linear layer (Baker) and
the apex (degree `≥2`) are cleanly separated by Proposition Q.

## §Q.4 The §K leap — verdict: mis-typed (category error), NOT the missing multiplication `[terminal; downgrades §K]`

§N.3 left §K "untested at the decisive point" and rightly warned against a premature *numeric* refutation.
The reverse lever supplies the decisive **structural** objection (no numerics, so no artifact risk):

The Weil Gram matrix `G_{jk} = ⟨g_{p_j}, g_{p_k}⟩_W` is the Gram matrix of the *test-function images*
`{g_{p_j}}` in the Weil inner-product space. A Gram matrix detects exactly one thing: **linear
(in)dependence of those vectors**. `det G = 0 ⟺ {g_{p_j}}` are linearly dependent **as functions** — a
property of the test functions and the zeros, generically false (so `G` is generically non-degenerate),
and it says **nothing** about *polynomial* relations among the *scalars* `{log p}`:
- `det G = 0` is one **real-analytic / transcendental** condition (the entries are transcendental in the
  logs and the zeros);
- a degree-2 relation `P(log p) = 0` is one **algebraic** condition.
There is no mechanism by which "linear dependence of certain functions" equals "an algebraic relation among
certain scalars." §K's load-bearing step ("`G` non-degenerate `⟺` no degree-2 collapse") is a **type
error**: it reads a *linear*-algebra non-degeneracy as an *algebraic*-independence certificate.

> **Verdict.** §K is **downgraded from live leap to mis-typed.** The explicit-formula quadratic form is a
> genuine prime↔zero pairing, but its (non-)degeneracy is a linear/analytic property of the test functions,
> **orthogonal** to the degree-`≥2` algebraic content the apex needs. RH/Weil positivity (`G≻0`, anyway
> automatic — §N.3) does **not** supply the "missing multiplication." This *explains* the banked two-apex
> independence (`RH ⇏ DSS`, #191/#54): the explicit-formula weld does not transmit into the
> value-independence sector. §K's "tension with the banked independence" resolves in favor of the
> **independence**, with a precise reason (category mismatch) — not in favor of the leap.

## §Q.5 Terminal disposition (this session)

| Claim | Conclusion |
|---|---|
| §J: does known large-trdeg machinery give `trdeg→∞`? | **NEGATIVE, verified** — no unconditional unbounded trdeg bound; even `∃` 2 alg-indep logs is open (terminal) |
| UC vs the named open problems | **PLACED (proven sandwich):** `(S) ⟹ UC ⟹ (L∞) ⟹ (E2)`, all open; UC implies the already-open `(E2)` (terminal) |
| §I/§J "UC may be within reach" | **CORRECTED:** weaker in logic, **not** in difficulty (sits above the open `(E2)`) (terminal) |
| Prop Q: ¬UC ⟹ counterexample relations degree `≥2` | **PROVEN** (Baker rules out degree `≤1`) — re-derives §B (terminal) |
| §K leap (Weil-Gram = missing multiplication) | **DOWNGRADED — mis-typed** (Gram-degeneracy is linear/analytic, not algebraic); not the route (terminal) |
| the apex (UC itself) | **OPEN, unfaked** — on the transcendence-theory frontier; no native or analytic shortcut survives |

**Net of the session (honest).** No new theorem about the apex (open, not faked). Banked: the **verified
NEGATIVE on §J** (the single highest-value verification the card pointed to); the **proven placement of UC**
between full Schanuel and the already-open existence problem `(E2)` — correcting the "within reach" optimism;
the **essential-nonlinearity Proposition Q** (Baker `⟹` degree `≥2`, re-deriving §B from the linear theory);
and the **mis-typed verdict on §K** (the Weil-Gram route does not connect to the apex). The regular column
remains BRIDGE/substrate with no surviving native or analytic shortcut; the apex is the classical
algebraic-independence-of-logarithms frontier, now located precisely.

## Log (cont.)
- 2026-06-20 — **§Q (rolled target; lever 3 = reverse it).** Verified §J NEGATIVE against the transcendence
  literature: no unconditional unbounded trdeg bound for logs; whether the log field has finite/infinite
  trdeg is itself open, and even the existence of two algebraically independent logarithms is open
  (Waldschmidt, *Open Diophantine Problems*; Roy structural-rank `⟺` full conjecture; Waldschmidt–Masser is
  linear-rank only). Proved the placement sandwich `(S) ⟹ UC ⟹ (L∞) ⟹ (E2)` — UC implies the already-open
  existence problem, correcting §I/§J "within reach." Proved Proposition Q (contrapositive: ¬UC forces
  degree-`≥2` relations, since Baker rules out degree `≤1`) — re-deriving §B's degree-`≥2` difficulty from
  the linear theory. Downgraded §K to mis-typed (Gram-degeneracy is linear/analytic, orthogonal to algebraic
  relations among logs), resolving its banked-independence tension in favor of independence. Apex open,
  unfaked; no native/analytic shortcut survives. Sources in §Q.1.
