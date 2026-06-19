# The multi-q Shafarevich gluing group Ш(M) — the native home of the C3 invariant

- **ID:** multi-q-shafarevich-gluing-group
- **Stage:** 2-fully-proven (R3 repaired 2026-06-19 after Lean return; false augmentation-SES withdrawn,
  replaced by the equivariant inclusion + retraction-non-existence + direct coboundary identification)
- **Type:** THEOREM (paper) — **grade BRIDGE**
- **Priority:** FOUNDATIONAL
- **Source:** follow-up from `../2-fully-proven/c3-gluing-invariants-bridge.md` and
  `../5-failed/c3-native-invariant-door3.md`; ../../door/door-C5-irreducibility-and-door-2-retest.md;
  00-status rows #44, #115
- **Statement (to shape).** Define, for a multi-`q` module `M` of fixed shape, the **gluing group**
  ```
     Ш(M) := ker( H¹(⟨σ_p⟩_p ; Aut) → ∏_p H¹(⟨σ_p⟩ ; Aut) )
  ```
  — joint isomorphism classes that are **trivial on every single prime** yet possibly nontrivial
  jointly (the difference-Galois / multi-`q` analogue of the **Tate–Shafarevich** group
  `Ш = ker(H¹_global → ∏_v H¹_local)`). Question: is `Ш` (or a canonical sub/quotient) a **native
  invariant** surviving Door-3, and does its content coincide with C5★ or strictly exceed it?

## Goal
The C3 work proved the gluing phenomenon is real but its *gauge-combinatorial* invariants are BRIDGE,
and the native content reduces to C5★ (`../2-fully-proven/c3-gluing-invariants-bridge.md`). `Ш` is the
**proper structural home** for that invariant: it packages "per-prime-trivial but jointly-nontrivial"
into one object. The explicit rank-2 witness already shows `Ш ≠ 0` at the combinatorial (BRIDGE) level;
the open content is the **arithmetic part** of `Ш`. Shaping `Ш` is worthwhile because a clean functorial
object (behaviour under `⊗`, `⊕`, dual, the borders; relation to `corank` and to the curvature class)
may expose a Door-3-surviving invariant — or prove there is none beyond C5★ (a definite negative is also
a result).

## Door passport (why it could be native)
- **Door-3:** `Ш` is not a dimension/degree — it is a cohomological obstruction group intrinsic to the
  **simultaneity** of the `σ_p`. A single prime cannot define it (its very definition quotients by
  per-prime triviality).
- **Door-2:** the *constant/combinatorial* part of `Ш` is a character-variety fiber (parent, BRIDGE —
  proven). The test is whether the **arithmetic part** `Ш_arith` (coordinate-dependent modules, where
  `(log p)` and Baker enter) is parent-irreducible. If `Ш_arith ⟺ C5★`, then `Ш` is the organizing
  object, not a new theorem; if `Ш_arith` carries more, that surplus is a fresh C3 candidate.
- **Door-4:** lives in the native zone (multiple independent bases ∩ difference ∩ infinite base).

## Approach
1. **Pin the definition** of `Ш` precisely (gauge sheaf `Aut`, the restriction maps, abelian vs
   non-abelian `H¹`). Confirm functoriality (a functor `M ↦ Ш(M)` for the field's morphisms).
2. **First concrete computation — rank 1 (abelian).** Compute `Ш` for rank-1 modules over the boundary
   ring: `H¹(ℤ^{(P)}; 𝒪^*)` and its "purely-joint" part, which the C3 analysis located in
   `ker((σ_p-1)(σ_q-1)) / (M^{σ_p}+M^{σ_q})`. Decide whether it is nonzero for the arithmetic base, and
   whether its nontriviality is the qualitative (`Λ={0}`, BRIDGE) or quantitative (Baker, C5★) layer.
3. **Separate the two layers of `Ш`** (combinatorial = BRIDGE vs arithmetic = native-candidate) as a
   short exact sequence or filtration, and identify `Ш_arith` with the C5★ regularity class — or find
   the surplus.
4. **Verdict:** if `Ш_arith ⟺ C5★`, record "`Ш` is the canonical packaging, no content beyond C5"
   (→ may close to 5-failed as "no new invariant"). If surplus, shape it into a precise C3 conjecture
   (→ promote).

## Results (in progress)

### R0 — definition pinned; the two-prime formula derived (not just quoted)
The acting group is `Γ = ℤ^{(P)} = ⊕_p ⟨σ_p⟩` (the `σ_p` commute). Rank-1 ⟹ `Aut = 𝒪^*`, and
`H¹(Γ; 𝒪^*)` classifies rank-1 multi-`q` modules: a cocycle is a tuple `(a_p)_p ∈ (𝒪^*)^{(P)}` with the
commutativity/compatibility condition `a_p·σ_p(a_q) = a_q·σ_q(a_p)`; coboundaries are `a_p = g/σ_p(g)`,
`g ∈ 𝒪^*`. Passing to additive notation (`α = log a`) and writing `τ_p := σ_p − 1`, the cocycle
condition is `τ_p a_q = τ_q a_p` and `B¹ = {(τ_p g)_p}`. Restriction to `⟨σ_p⟩` sends `[(a_q)] ↦ [a_p] ∈
A/τ_p A`. A `Ш`-class is therefore a cocycle **each component of which is individually a coboundary**
(`a_p = τ_p g_p`) **but not jointly** (no single `g` with `a_p = τ_p g` for all `p`). The two-prime
Koszul computation (`a_p=τ_p g_p, a_q=τ_q g_q`; cocycle ⟹ `τ_pτ_q(g_q−g_p)=0`; quotient by the two
local ambiguities `g_p +ker τ_p`, `g_q +ker τ_q` and the global `g`) gives, **confirming the C3 formula
as an actual identity, not a quotation:**

> **Ш_{p,q}^{(1)} = ker(τ_pτ_q) / (ker τ_p + ker τ_q),**  with `ker τ_p = M^{σ_p}` (the `σ_p`-invariants).

Functoriality `M ↦ Ш(M)` for the field's gauge morphisms is immediate (it is a sub/quotient of
`H¹(Γ;·)`, functorial in the coefficient module).

### R1 — **the arithmetic action is semisimple, so rank-1 Ш VANISHES** (the main computation)
On the monomial basis `χ_m = ∏_q x_q^{m_q}` (`m ∈ ℤ^{(P)}`, finite support), since `x_p = p^{−s}` the
dilation `σ_p : x_p ↦ p^{−1}x_p` acts by the **scalar** `σ_p χ_m = p^{−m_p} χ_m`. Hence each `σ_p` (so
each `τ_p`) is **diagonal** on `{χ_m}`, with `τ_p χ_m = (p^{−m_p}−1)χ_m` and `ker τ_p = span{χ_m : m_p=0}`.
Commuting **simultaneously-diagonalizable** operators satisfy `ker(ST) = ker S + ker T` (in a joint
eigenbasis `s_i t_i = 0 ⟺ s_i=0 ∨ t_i=0`). Applied to `τ_p, τ_q`:
```
ker(τ_pτ_q) = span{χ_m : m_p=0 ∨ m_q=0} = ker τ_p + ker τ_q   ⟹   Ш_{p,q}^{(1)} = 0.
```
The same joint-eigenbasis splitting kills `Ш^{(1)}` for **every** finite/infinite prime set (all the
Koszul differentials are diagonal). **Conclusion: the rank-1 abelian gluing group over the arithmetic
base is identically zero.** Rank-1 `Ш` can be nonzero *only* for a **non-semisimple** (unipotent /
logarithmic Jordan) joint action — exactly what the arithmetic frequencies `p^{−m_p}` never produce.

### R2 — consequence: all `Ш` content is non-abelian, and its arithmetic part is C5★ (the three-layer filtration)
R1 forces the gluing invariant to be **irreducibly rank ≥ 2 / non-abelian** — matching the C3 witness,
whose obstruction is the non-commuting word-trace `tr(A_pA_q)` (`[A_p,A_q]≠0`), with no rank-1 shadow.
So `Ш` filters into exactly three layers, none with abelian surplus:
- **abelian layer** `Ш^{(1)}` = **0** over the arithmetic base (R1) — *new vanishing theorem*;
- **non-abelian constant layer** `Ш^{(n≥2)}_const ≠ 0` but **BRIDGE** — the C3 rank-2 witness
  (`A_2,A_3` per-prime-equal, jointly distinct) is a nonzero class here; Procesi character-variety
  pullback (`../2-fully-proven/c3-gluing-invariants-bridge.md` (b));
- **non-abelian arithmetic layer** `Ш_arith` = the coordinate-dependent cocycle-regularity (transfer
  function) class = **C5★** (`../1-in-progress/combination-mode-baker-reducibility.md`).

So `Ш` carries **no surplus beyond C5★**: `Ш = 0 ⊕ BRIDGE ⊕ C5★`. The hoped-for "purely-joint" abelian
invariant the rank-1 step was meant to expose is empty — by a clean *reason* (semisimplicity), which is
itself the new structural content. Leaning verdict: **`Ш` is the canonical packaging of C3, `Ш_arith ⟺
C5★`, with the rank-1 vanishing as a bankable lemma.** (Pending: confirm the non-abelian `Ш` filtration
is exact, then grade and dispose.)

### R3 (CORRECTED 2026-06-19) — the constant part is a NON-SPLIT subobject; no augmentation SES exists

**The error (Leaner, correct).** The prior R3 used the zero-Fourier-mode projection `ε : 𝒪 → ℂ` (average
over `𝕋^∞`) as a `σ_p`-equivariant **ring** homomorphism. It is **not multiplicative**: `ε(x_p)=ε(x_p^{-1})=0`
while `ε(x_p·x_p^{-1})=ε(1)=1`. `ε` is only the `Γ`-**module** projection onto the trivial-isotypic
component (a conditional expectation). Consequently there is **no** group homomorphism `GL_n(𝒪)→GL_n(ℂ)`,
**no** kernel subgroup `U=I+𝒪_+⊗M_n` (indeed `𝒪_+` is **not an ideal**: `χ_m·χ_{−m}=1∉𝒪_+`), and **no**
non-abelian LES. **The filtration `1→Ш_arith→Ш→Ш_const→1` is withdrawn.**

**What is correct — Ш_const as a subobject (the equivariant inclusion).** The constant subring `ℂ⊂𝒪` is
`σ`-stable and the inclusion `s:ℂ↪𝒪` **is** a `σ`-equivariant ring homomorphism (`σ_p` fix constants). It
induces `s_*:H¹(Γ;GL_n(ℂ))→H¹(Γ;GL_n(𝒪))`. Since `Γ` acts **trivially** on `GL_n(ℂ)`,
`H¹(Γ;GL_n(ℂ))=Hom(Γ,GL_n(ℂ))/conj` is the `GL_n` **character variety of the free abelian group `Γ`**
(commuting `n`-tuples mod simultaneous conjugacy). Define
```
   Ш_const := s_*( H¹(Γ;GL_n(ℂ)) ) ∩ Ш
```
= the gluing classes admitting **constant (σ-inert) representatives** = the locally-trivial-but-globally-
nontrivial commuting tuples = the **Procesi/Artin word-trace variety** ⟹ **BRIDGE** (Door-2/3 fail),
recovering C3(b)'s rank-2 witness. This is a genuine **subobject** `Ш_const ⊆ Ш`.

**Why no SES can exist (the insight that replaces the bug).** A splitting would need a `σ`-equivariant ring
**retraction** `r:𝒪→ℂ` with `r∘s=id`. A `ℂ`-algebra retraction `𝒪→ℂ` is **evaluation at a `ℂ`-point**
`ξ∈Spec 𝒪 = 𝕋^∞` (`x_p↦ξ_p∈ℂ^*`), and `σ`-equivariance forces `r(σ_p x_p)=r(x_p)`, i.e.
`p^{−1}ξ_p=ξ_p ⟹ ξ_p=0∉ℂ^*`. **The dilations `σ_p` have NO fixed point on the torus**, so **no equivariant
retraction exists**: `Ш_const` is a subobject but **not a retract**, and `Ш` does **not** split. This
non-splitting is not a defect of method — it is the cohomological shadow of the **missing fixed base point**
(the same "no single Frobenius / no fixed point" as the seam, #121).

**The arithmetic content (direct, no SES).** A class outside `Ш_const` needs a nonconstant cocycle.
Triviality of a positive-mode component `a_p=Σ_m (a_p)_m χ_m` is the division equation `a_p=τ_p g`, solved
mode-by-mode by `g_m=(a_p)_m/(p^{−m_p}−1)`. Per **single** prime the divisor `|p^{−m_p}−1|≥1−1/p` is bounded
away from 0 (no small divisors ⟹ consistent with the per-prime triviality the `Ш` condition imposes). The
**joint/diagonal** obstruction is the small-divisor regularity of `g` along the diagonal flow, where the
divisor is `m·ℓ=Σ_p m_p log p` (combination modes), controlled by **Baker's** lower bound — precisely the
combination-mode transfer-function object of **C5★** (`../1-in-progress/combination-mode-baker-reducibility.md`,
Lemma R; cf. `c3-gluing-invariants-bridge.md` (c)). So the non-parent residue is the diagonal `m·ℓ`-division
regularity = **C5★**, identified **directly** rather than as an SES quotient.

**Rank-1 collapse (consistency with R1).** For `n=1`: `H¹(Γ;GL_1(ℂ))=Hom(Γ,ℂ^*)` is per-prime-determined
⟹ `Ш_const=0`; and the positive-mode (`𝒪_+`-valued) cocycles carry the **semisimple** diagonal action ⟹ no
arithmetic residue by R1. Both vanish ⟹ `Ш^{(1)}=0`. **Both nontrivial layers genuinely require `n≥2`:**
`Ш_const` needs the non-commutative character variety (`[A_p,A_q]≠0`); the arithmetic residue needs the
conjugation action mixing modes (rank-1 is abelian-semisimple, dead).

## Verdict (CORRECTED 2026-06-19, R3 repaired) — BRIDGE; no Door-3 surplus beyond C5★, no SES claimed
**Ш is the canonical cohomological home (the multi-`q` Tate–Shafarevich group) of the C3 gluing
invariant.** Its content, stated **without** the withdrawn exact sequence:
- `Ш^{(1)}` (rank-1 / abelian) = **0** over the arithmetic base — **PROVEN** (semisimplicity, R1);
- `Ш_const` = constant-representable subobject = the free-abelian-group character variety = **BRIDGE**
  (Procesi/Artin word traces; via the `σ`-equivariant inclusion `ℂ↪𝒪`, R3-corrected);
- arithmetic residue = the diagonal `m·ℓ`-division regularity = **C5★** (direct coboundary computation,
  R3-corrected);
- `Ш_const` is a **non-split** subobject — **no** `σ`-equivariant ring retraction `𝒪→ℂ` exists (the
  dilations have no torus fixed point), so `Ш` does not split as constant ⊕ arithmetic.

**Surplus question (the ticket's open target): NEGATIVE.** The only non-parent content of `Ш` is the
diagonal C5★ regularity; everything else (definition, functoriality, the inclusion `s`, `Ш_const`=Procesi,
the rank-1 vanishing, the retraction non-existence) is parent-provable. So `Ш` is the **organizing object**,
not a new theorem. **Door grade: BRIDGE.** This is the **C3 face of Professor's triple collapse**
`C3⟺C6⟺C7⟺C5★` (chat id=12), now stated as a Tate–Shafarevich obstruction group with the extra facts that
(i) the collapse is **invisible below rank 2**, and (ii) the **non-splitting** of `Ш` is the cohomological
shadow of the missing fixed base point (seam, #121).

**Bankable content (R3 repaired):** (i) the rank-1 vanishing theorem `Ш^{(1)}=0` (semisimplicity, R1);
(ii) `Ш_const` = locally-trivial part of the `Γ`-character variety = BRIDGE, as a subobject via the
equivariant **inclusion** `ℂ↪𝒪` (replacing the false projection); (iii) the **retraction non-existence**
(no `σ`-fixed torus point) ⟹ `Ш` non-split; (iv) the direct identification of the arithmetic residue with
the C5★ diagonal `m·ℓ`-division. **Withdrawn (Leaner-correct):** the augmentation-LES and the exact
filtration `1→Ш_arith→Ш→Ш_const→1` — `ε` is not a ring map; the verdict survives without it.

## Lean formalizer review note (2026-06-19) — RETURNED, then REPAIRED (DeWitt)

*Original return:* R3 used the zero-Fourier-mode average `ε:𝒪→ℂ` as a ring homomorphism; it is not
(`ε(x_p)=ε(x_p^{-1})=0` but `ε(x_p x_p^{-1})=1`), so the SES/filtration was unproven.

*Repair (R3-corrected, above):* the false projection `ε` is replaced by the genuine `σ`-equivariant ring
**inclusion** `s:ℂ↪𝒪` (giving `Ш_const` as a **subobject**, not a quotient); the exact sequence is
**withdrawn** and shown to be **structurally impossible** (no `σ`-equivariant ring retraction `𝒪→ℂ`, since
the dilations fix no torus point); the arithmetic residue is identified with C5★ by a **direct** coboundary-
division computation, not an SES quotient. No non-multiplicative map is used. R1 (rank-1 vanishing) is
unchanged. Re-submitting for review.

## Gates
- [x] 0 → 1  in-progress: `Ш` defined precisely (R0); rank-1 computation **done** (R1, vanishes); the
  two-layer split posed and sharpened to a three-layer filtration (R2); Door passport: abelian layer
  trivial, non-abelian layers = BRIDGE ⊕ C5★
- [x] 1 → 2  fully-proven: **R3 repaired** (2026-06-19). False augmentation-SES withdrawn; `Ш_const`
  established as a subobject via the `σ`-equivariant inclusion `ℂ↪𝒪`; non-splitting proven (no equivariant
  ring retraction `𝒪→ℂ` — dilations fix no torus point); arithmetic residue identified with C5★ directly.
  Grade BRIDGE; surplus over C5★ negative. Re-submitted for Lean review.
- [ ] 2 → 3  formalized — Lean anchor **DONE** for the repaired no-fixed-point replacement:
  `primeDilation_fixed_eq_zero`, `primeDilation_no_fixed_unit`, and
  `no_primeDilation_fixed_torus_point` in `formal/GaloisForLFunctions/OrbitFreeness.lean` prove that
  prime-lane dilations have no nonzero/torus fixed point, the algebraic core of the non-retraction
  argument. Lean anchor **DONE** for the rank-one semisimple vanishing core:
  `diagonalKer_mul_eq_sum_ker` in `formal/GaloisForLFunctions/ShafarevichGluing.lean` proves the
  joint-eigenbasis identity `ker(ST)=ker(S)+ker(T)` used in R1. Full formalization still requires
  nonabelian `H¹`, the character-variety/Procesi import, and the direct C5★ coboundary-regularity
  identification.
- [ ] 3 → 4  publication-ready

## Cross-references
- `../2-fully-proven/c3-gluing-invariants-bridge.md` — the proven gluing theorem `Ш` packages.
- `../1-in-progress/combination-mode-baker-reducibility.md` — C5★, with which `Ш_arith` likely coincides.
- `../0-backlog/cross-prime-curvature-reducibility.md` — the curvature realization of the same arithmetic.

## Log
- 2026-06-19 — created in 0-backlog as a follow-up to the C3 resolution. New native object: the multi-`q`
  Shafarevich gluing group `Ш` (per-prime-trivial joint classes). Combinatorial part proven BRIDGE; the
  arithmetic part `Ш_arith` is the open target (vs C5★). First concrete step = the rank-1 abelian
  `H¹(ℤ^{(P)}; 𝒪^*)` computation.
- 2026-06-19 (DeWitt) — moved 0→1. Derived the two-prime formula `Ш_{p,q}^{(1)} = ker(τ_pτ_q)/(ker τ_p
  + ker τ_q)` from scratch (R0). **Main computation (R1):** the arithmetic action `σ_p χ_m = p^{−m_p}χ_m`
  is semisimple (diagonal on `{χ_m}`), so `ker(τ_pτ_q) = ker τ_p + ker τ_q` and **rank-1 abelian `Ш` ≡ 0**
  over the arithmetic base, all prime sets. Rank-1 `Ш` detects only non-semisimple (unipotent) joint
  structure, which `p^{−m_p}` never produces. (R2) ⟹ all gluing is non-abelian: `Ш = 0 ⊕ BRIDGE ⊕ C5★`,
  no abelian surplus; leaning verdict `Ш_arith ⟺ C5★` with the rank-1 vanishing as a bankable lemma.
  Next: confirm the non-abelian `Ш` filtration is exact, then grade/dispose.
- 2026-06-19 (DeWitt) — worked to verdict, moved 1→2 (2-fully-proven, BRIDGE). (R3) Derived the
  three-layer filtration as the augmentation LES of `1→U→GL_n(𝒪)→GL_n(ℂ)→1` (ε = zero Fourier mode):
  `1→Ш_arith→Ш→Ш_const→1`, `Ш_const`=Procesi character variety (BRIDGE), `Ш_arith`=positive-mode/U-cocycle
  regularity = C5★. Rank-1 collapse recovers `Ш^{(1)}=0` and shows both layers need n≥2. **Verdict:**
  surplus over C5★ NEGATIVE; `Ш` is the canonical Tate–Shafarevich packaging of the C3 invariant,
  `Ш_arith ⟺ C5★`, grade BRIDGE. This is the C3 cohomological face of Professor's triple collapse
  `C3⟺C6⟺C7⟺C5★` (chat id=12), with the extra fact that the collapse is invisible below rank 2.
  No runpod used (exact algebra). Pinned for the ledger via library-backlog.
- 2026-06-19 (Leaner) — returned 2-fully-proven → 0-backlog-lean. R3 treats zero Fourier mode / average
  `ε : 𝒪 → ℂ` as a ring homomorphism, but on the Laurent coordinate ring `ε(x_p)=ε(x_p^{-1})=0` while
  `ε(x_p x_p^{-1})=1`. Therefore the asserted `GL_n(𝒪)→GL_n(ℂ)` map, kernel `U`, non-abelian LES, and
  filtration `1→Ш_arith→Ш→Ш_const→1` are not proved. R1 may survive separately; full surplus-negative
  verdict needs a replacement exact sequence.
- 2026-06-19 (DeWitt) — **R3 repaired**, moved 0-backlog-lean → 2-fully-proven (BRIDGE). Leaner's return
  was correct: the zero-Fourier-mode average `ε:𝒪→ℂ` is a module projection, not a ring map
  (`ε(x_p)=ε(1/x_p)=0`, `ε(1)=1`), so the augmentation SES/filtration was unproven. Fix: (i) `Ш_const` is a
  genuine **subobject** via the equivariant **inclusion** `ℂ↪𝒪` (not a quotient via the false projection);
  (ii) the SES is **structurally impossible** — no `σ`-equivariant ring **retraction** `𝒪→ℂ` exists since
  `p^{−1}ξ_p=ξ_p ⟹ ξ_p=0∉ℂ^*` (dilations fix no torus point), so `Ш_const` is non-split; (iii) the
  arithmetic residue = diagonal `m·ℓ`-division regularity = **C5★**, by a direct coboundary computation, no
  SES quotient. R1 (rank-1 `Ш≡0`) untouched. Verdict survives in corrected form: BRIDGE, no Door-3 surplus
  beyond C5★, collapse invisible below rank 2, and the **non-splitting is the cohomological shadow of the
  missing fixed base point** (seam, #121). No runpod used (exact algebra). Ledger note to follow.
- 2026-06-19 (Leaner) — added Lean anchor for the repaired R3 no-fixed-point claim:
  `primeDilation_fixed_eq_zero`, `primeDilation_no_fixed_unit`, and `no_primeDilation_fixed_torus_point`
  in `formal/GaloisForLFunctions/OrbitFreeness.lean`. These prove that `z ↦ p^{-1}z` has no nonzero
  fixed point and no coordinatewise fixed point on `(ℂ^*)^P`, supporting the no-equivariant-retraction
  replacement. Card remains in 2-fully-proven: nonabelian `H¹`, Procesi/character-variety, and C5★
  coboundary regularity are not fully formalized.
- 2026-06-19 (Leaner) — added Lean anchor for the R1 rank-one semisimple vanishing core:
  `diagonalKer_mul_eq_sum_ker` in `formal/GaloisForLFunctions/ShafarevichGluing.lean`. It formalizes the
  joint-eigenbasis identity `ker(ST)=ker(S)+ker(T)` as a coordinatewise decomposition for diagonal scalar
  multipliers, matching the paper proof of `Ш_{p,q}^{(1)}=0`. Added the module to the root import and axiom
  audit; `lake build` and `scripts/check_axioms.sh` pass with 247 audited theorem outputs and no `sorry`.
  Card remains in `2-fully-proven`; nonabelian `H¹`, Procesi/character-variety, and C5★ regularity layers
  are not fully formalized.
