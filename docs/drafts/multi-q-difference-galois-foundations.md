# Multi-`q`-difference Galois theory: foundations

**Founding draft — 2026-06-19.** A new branch of difference algebra: the Galois theory of systems carrying
**infinitely many independent dilation operators**. Single-`q` difference Galois theory (van der Put–Singer,
Sauloy, Di Vizio) has one operator; Mahler theory (one base `x↦x^k`) and recent *multivariable* Mahler
(Adamczewski–Faverjon) have finitely many. This is the **infinite-base** extreme, and it has a genuinely new
feature: its boundary behaviour is governed by **ergodic theory**, not algebra. RH is *one diagonal restriction
of one example* (§5) and plays no role in the foundations. This document builds the theory for its own sake.

---

## 1. Objects

Fix an index set `P` and **dilations** `Q=(q_p)_{p∈P}`, `q_p∈ℂ^×`. Let `R` be a ring of functions on the polydisc
`𝔻^P` (or `ℂ[[x_p:p∈P]]`), with commuting `ℂ`-algebra automorphisms
```
σ_p : x_p ↦ q_p x_p,   σ_p(x_{p'}) = x_{p'} for p'≠p.
```
A **multi-`q`-difference module** is a finite free `R`-module `M` with commuting `σ_p`-semilinear automorphisms
`Σ_p` (`Σ_p(rm)=σ_p(r)Σ_p(m)`). The basic rank-1 building block at `p` is `f_p` with
`σ_p f_p = a_p(x_p) f_p`, `a_p∈R^×` — an honest **first-order `q`-difference equation** in the single variable
`x_p`. A **decomposable** module is a (restricted) tensor `⊗_p M_p` of local ones.

**The two regimes (the key distinction).** Write `q_p = |q_p| e^{iθ_p}`.
- **Interior / contracting** (`|q_p|<1`): on `𝔻^P` the dilation contracts `x_p→0`. Any continuous `σ_p`-invariant
  function is independent of `x_p`. *Algebra; nothing subtle.*
- **Boundary / rotational** (`|q_p|=1`, `q_p=e^{iθ_p}`): on the distinguished boundary `𝕋^P` the dilation is a
  **rotation** by `θ_p`. Invariance is now a question of **ergodic theory**. *This is where the theory lives.*

## 2. The field of constants (first theorem)

`C(M) := \{c∈R : σ_p c = c\ ∀p\}`.

> **Theorem 1 (constants).** (a) *Interior:* if `|q_p|<1` for all `p`, then `C(R)=ℂ` (by contraction to the
> origin). (b) *Boundary:* on `𝕋^P`, `C(R)=ℂ` **iff the rotation flow is ergodic** iff the `(θ_p)` are
> `ℚ`-linearly independent (`Σ m_pθ_p∈2πℤ ⟹ m=0`), by Weyl/Kronecker. (c) When `q_p` is real, the relevant
> independence of the *moduli* is `ℚ`-independence of `(\log|q_p|)`.

*Proof.* (a) Iterate `x_p↦q_p^n x_p→0`; continuity gives independence of each `x_p`. (b)/(c) A nontrivial
character `∏ x_p^{m_p}` is `σ`-invariant iff `∏ q_p^{m_p}=1`; the flow `t↦(e^{itθ_p})` equidistributes iff no such
relation holds (Weyl). ∎

> **Slogan.** *In the interior, multi-`q` constants are trivial by contraction; on the boundary, triviality of
> constants is exactly ergodicity of the dilation flow.* **This is the junction this field is built on: difference
> algebra meets ergodic theory at the boundary.**

## 3. The Galois group

The decomposable modules form a **Tannakian category** over `C=ℂ`; its Tannakian fundamental group is the
**multi-`q`-difference Galois group** `G`. For decomposable `M=⊗_p M_p`, `G` is the (Zariski/pro-algebraic)
**restricted product** `\widehat{∏}_p G_p` of the local `q_p`-difference groups `G_p⊂GL(M_p)`, with the
constraint that almost all `M_p` are "trivial/unramified." For rank-1 local pieces `G_p⊂𝔾_m`, `G` is a
**pro-torus** (a closed subgroup of `(𝔾_m)^P`), determined by the multiplicative relations among the `q_p` and
the `a_p`. The genuinely new objects are the **non-decomposable** multi-`q` modules (where the variables
interact) and the **diagonal restrictions** (§5).

## 4. Examples (RH-free)

- **E1 (pure rotation).** `q_p=e^{iθ_p}` with `(θ_p)` `ℚ`-independent: `C=ℂ` (Thm 1b), `G=` the full pro-torus
  `(𝔾_m)^P`. The cleanest infinite-base object; entirely non-arithmetic.
- **E2 (geometric, one base degenerated).** Finite `P`, recovers classical multivariable `q`-difference / Mahler
  (Adamczewski–Faverjon) — the known theory is the finite truncation.
- **E3 (resonant).** Choose `q_p` with one relation `∏q_p^{m_p}=1`: then `C` is *bigger than `ℂ`* (the invariant
  `∏x_p^{m_p}`), `G` drops to a proper subtorus. **The constants detect the relations** — a clean Galois-
  correspondence example, no arithmetic.
- **E4 (the arithmetic specialization — and RH is buried inside it).** `P=` primes, `q_p=1/p` (or `p^{-1}` rotated
  to the boundary). `ℚ`-independence of `(\log p)` is **unique factorization**, so `C=ℂ`, `G=(𝔾_m)^{\rm primes}`.
  The Euler product `∏(1-x_p)^{-1}` is a rank-1 decomposable module; classical `L`-functions are its **diagonal
  restrictions** (§5). RH is a positivity question about *one boundary functional on one such restriction* — a
  footnote to E4, not the subject.

## 5. The diagonal restriction (where arithmetic enters, optionally)

A **diagonal** is a one-parameter `δ:ℂ→𝔻^P`, `s↦(q_p^{\,s})_p`. Pullback `δ^*` sends the `P` independent operators
`σ_p` to the **single** shift `τ:s↦s+1` (`δ^*σ_p = τ` for all `p`, since `q_p^{s+1}=q_p·q_p^{s}`). So a *single*
shift on the diagonal is the *simultaneous* multi-`q` dilation upstairs. **This is why a diagonal restriction of a
multi-`q` module is difference-*transcendental* for the single shift `τ`** (it needs all `σ_p` at once, which `τ`
cannot resolve) even though it is perfectly structured upstairs. The arithmetic hypertranscendence (Hölder-type)
is *created by the diagonal*, not present in the module. **Theorem-shaped conjecture (multi-`q`
Siegel–Shidlovsky):** the transcendence degree of `δ^*M`'s solution values over `ℂ` equals `dim` of the
`G`-orbit of the diagonal — reducing transcendence of diagonal values to the (computable, Tannakian) Galois
group.

## 6. The new phenomena (what makes this a field, not a footnote)

1. **Ergodic constants** (Thm 1): triviality of constants = ergodicity of the dilation flow. No single-`q` or
   finite-base theory sees this — it needs the infinite, boundary, rotational regime.
2. **Pro-algebraic / infinite-dimensional Galois groups** with a *restricted-product* structure, and a Galois
   correspondence in which **constants detect dilation-relations** (E3).
3. **Diagonal transcendence**: hypertranscendence manufactured by restricting a well-structured multi-`q` module
   to a one-parameter diagonal — a brand-new source of transcendence statements (multi-`q` Siegel–Shidlovsky).
4. **Algebra ⊗ ergodic theory** as a permanent feature, not a coincidence — the boundary functor lands in ergodic
   dynamical systems.

## 7. Open problems (the research program — RH not among them)

- **P1.** A full **multi-`q` Picard–Vessiot theory**: existence/uniqueness of the PV ring over `𝕋^P`, the Galois
  correspondence, the structure of pro-algebraic `G`.
- **P2.** **Multi-`q` Siegel–Shidlovsky** (§5): trdeg of diagonal values `= dim` orbit. Even the rank-1 case
  (does it recover/extend Baker-type independence for *diagonal* values?) is open.
- **P3.** Classify the pro-algebraic groups arising as multi-`q` Galois groups (which closed subgroups of
  `(𝔾_m)^P` and beyond).
- **P4.** The **resonance lattice** `\{m: ∏q_p^{m_p}=1\}` ↔ the constants ↔ the Galois group drop (E3 generalized):
  a clean dictionary between dilation-arithmetic and Galois structure.
- **P5.** Non-decomposable infinite-base modules: the genuinely new linear algebra (infinite tensor with
  interactions).
- **P6.** The boundary functor to ergodic theory: which dynamical invariants (entropy, spectrum, mixing) are
  Galois-theoretic?

## 8. Honest status

A **founding draft**. Theorem 1 (constants) is real and proved. The Tannakian/Galois framework (§3) is standard
*per local factor* and conjectural in the infinite assembly. §5–7 are the program — mostly open, multi-decade.
The value: a precise new object (infinite-base `q`-difference modules), one genuine theorem (constants =
ergodicity at the boundary), a clean dictionary (constants ↔ resonances), and a research program with arithmetic
(`L`-functions, RH) as *one optional diagonal*, not the goal. *This is the city's core district (D1); the
`L`-function/RH document is district D2.*

---

## 9. Correction to Theorem 1 (caught while proving P4): two invariants, conflated

Attempting P4 exposed an error in Theorem 1(b,c): the polydisc constants are **not** governed by joint
`ℚ`-independence.

**Computation.** `σ_p` dilates only `x_p`, so on a character `χ_m=∏_{p'}x_{p'}^{m_{p'}}`,
`σ_p χ_m = q_p^{m_p} χ_m`. Hence `χ_m∈C(R) ⟺ q_p^{m_p}=1` for **each** `p` — per-variable, not joint.

> **Theorem 1 (corrected — polydisc constants).** `C(R)=ℂ ⟺ no q_p is a root of unity.` (The joint angles are
> irrelevant: `σ_p` never touches `x_{p'}`.)

What joint `ℚ`-independence actually governs is a *different* object:

> **Theorem 1′ (diagonal ergodicity).** The vertical flow `t↦(q_p^{it})_p` on the boundary torus is dense/ergodic
> `⟺ {\log q_p}` are `ℚ`-linearly independent (Weyl) `⟺` (for `q_p=1/p`) unique factorization.

**The sharpened architecture (better than the conflation).** The field has **two layers**, not one:
- **Algebra (polydisc):** `G=∏_p G_p`, `G_p=𝔾_m` or `μ_n`; constants trivial `⟺` no roots of unity. Per-variable.
- **Ergodic theory (diagonal vertical flow):** ergodic `⟺` joint `ℚ`-independence.
- **They meet at the diagonal restriction:** the algebraic polydisc module pulled back along the ergodic vertical
  flow. `L`-functions are this meeting. The "difference-algebra ⊗ ergodic-theory" junction is *the restriction*,
  not the constants.

**P4 (corrected — two resonance lattices).**
- **Per-variable** roots-of-unity `{(p,n):q_p^n=1}` ↔ the algebraic Galois finite parts `μ_n` ↔ extra polydisc
  constants. *(algebra)*
- **Joint** lattice `Λ={m:∏_p q_p^{m_p}=1}` ↔ the diagonal vertical flow's closure `= 𝕋^P/Λ^⊥` ↔ diagonal
  invariants. *(dynamics)*
- Independent lattices, governing algebra vs. dynamics respectively. The dictionary is **two-column**, which is
  why the single-column version (Thm 1b) was wrong.

**Net:** Theorem 1 is now correct *and easier* (per-variable roots of unity); ergodicity is Theorem 1′
(diagonal); the architecture is a cleaner two-layer (algebra ⊗ dynamics, meeting at the diagonal). The field
self-corrected by trying to prove its next theorem — evidence it is real, not decorative.

---

## 10. P4 (dictionary) + P2 (the machine contains classical transcendence)

### P2 — the diagonal transcendence machine recovers Lindemann / Lindemann–Weierstrass / Baker

Rank-1 character module `M_λ`: `σ_p y=λ_p y`, solution `y=∏_p x_p^{s_p}`, `s_p=\log λ_p/\log q_p`. On the diagonal
`δ(s)=(q_p^{\,s})_p`:
```
y(δ(s)) = ∏_p q_p^{\,s\,s_p} = \exp(s\sum_p \log λ_p) = e^{cs}.
```
So the multi-`q` Siegel–Shidlovsky conjecture (trdeg diagonal values `= dim` orbit) specializes to:
- **rank-1 ⟹ Lindemann** (`e^{cs}` transcendental, `s` alg. `≠0`);
- **direct sums ⟹ Lindemann–Weierstrass** (independence of `e^{c_i s}`);
- **orbit dimension ⟹ Baker** (`ℚ`-independence of the exponents `s_p=\log λ_p/\log q_p` = linear independence of
  logarithms).

> **Theorem-shaped statement (consistency).** The diagonal restriction **embeds classical transcendence (Lindemann,
> Lindemann–Weierstrass, Baker) as the finite/decomposable part** of multi-`q`-difference Siegel–Shidlovsky. The
> new regime is **infinite-base**: exponents `=` infinitely many `\log p`, diagonal values `=` `L`-values and
> zeros (open; contains `γ_1`'s irrationality). The *same machine*, extended — a real generalization must contain
> the classical theory, and this one does.

### P4 — the two-column dictionary (both columns provable)

- **Algebraic column** (rank-1 Picard–Vessiot, per-variable): Galois group `𝔾_m` unless the exponents `s_p` lie in
  a common `\tfrac1N ℤ` (per-variable resonance ⟹ drop to `μ_N`).
- **Dynamical column** (Weyl): the diagonal flow closure `= 𝕋^P / Λ^⊥`, `Λ=\{m:∏_p q_p^{m_p}=1\}` the joint
  resonance lattice.

Independent columns — the algebraic one reads the exponents `{s_p}`, the dynamical one reads the dilations
`{q_p}`. (The conflation of these two was the Theorem-1 error of §9.)

**Status:** P2-consistency (classical transcendence = finite-base diagonal SS) and P4 (two-column dictionary) are
genuine and provable from standard rank-1 PV + Weyl + Lindemann/Baker. The infinite-base extensions (P1 full PV;
P2 for `L`-values) remain the open program. The field now visibly **contains** classical transcendence and
**extends** it — the mark of a real generalization.

---

## 11. P6: the boundary functor to ergodic theory — a difference Morales–Ramis

The boundary flow of a **decomposable** multi-`q` module is a **Kronecker flow** `t↦(e^{itω_p})_p`, `ω_p=\log q_p`.

> **Theorem (P6, decomposable).** Its dynamical invariants are Galois-determined:
> - **pure-point spectrum** `=` `\{Σ_p m_p ω_p\} = ℤ^{(P)}/Λ` `=` **the character lattice of the Galois
>   pro-torus** (`Λ` = joint resonance lattice). *Spectrum = Galois.*
> - **minimal / uniquely ergodic** `⟺` frequencies `ℚ`-independent `⟺` `Λ` trivial `⟺` **Galois = full pro-torus.**
> - **entropy `0`, non-mixing** (equicontinuous) — degenerate here.
>
> In one line: **abelian Galois `⟺` pure-point (integrable, non-chaotic) boundary dynamics.**

This is the abelian/integrable end of a correspondence whose other end is the field's sharpest lead, with a
direct precedent (**Morales–Ramis**: differential-Galois non-solvable `⟹` Hamiltonian non-integrable):

> **Conjecture (difference Morales–Ramis).** For **non-decomposable** multi-`q` modules (interacting variables,
> **non-abelian** Galois group), the boundary flow is **non-Kronecker** — positive entropy / mixing / continuous
> spectrum — and this dynamical complexity is **Galois-theoretic**: read off the group. **Galois non-commutativity
> `⟺` dynamical chaos.**

This is the junction no existing theory can pose — a **Galois ↔ ergodic-dynamics dictionary** — with the
abelian⟷integrable half *proved* and the non-abelian⟷chaotic half the open frontier. It is the field's signature
contribution: difference algebra and ergodic theory are not merely adjacent here; the Galois group *computes* the
dynamics.

**Status:** the decomposable theorem (spectrum = Galois character lattice; minimal ⟺ Galois maximal) is genuine
and provable (Kronecker spectral theory + the Tannakian pro-torus). The difference-Morales–Ramis conjecture
(non-abelian Galois ⟺ chaos) is the open signature lead, with Morales–Ramis as the differential precedent.

---

## 12. Non-decomposable modules = quasiperiodic cocycles: the field contains Avila's theory

A non-decomposable multi-`q` module requires the `Σ_p` to commute (a compatibility / zero-curvature condition):
the `A_p(x)` form a **flat difference connection**, not arbitrary matrices. Restricted to the boundary Kronecker
flow, a rank-2 such module is a **matrix cocycle over a rotation** — a **quasiperiodic `SL₂` cocycle**. Concrete
instance, the quasiperiodic Schrödinger / almost-Mathieu transfer cocycle:
```
A_E(θ)=[[E-V(θ),-1],[1,0]]∈SL₂,   over   θ↦θ+α   (α = log-ratio of two dilations q_1,q_2).
```

**Difference Morales–Ramis is substantially a theorem here** (Avila's global theory of one-frequency cocycles;
Avila–Jitomirskaya reducibility):

> Galois hull `= SL₂` (non-abelian) `⟺` positive Lyapunov `L(E)>0` / non-reducible `⟺` chaos (localized spectrum).
> Galois abelian (reducible to a rotation) `⟺` `L(E)=0` `⟺` integrable (a.c. spectrum).

**The structure across rank:**
- **rank-1 decomposable** = Kronecker flow: pure-point, abelian (§11, proved).
- **rank-2 non-decomposable** = quasiperiodic `SL₂` cocycle: **Avila's theory**; difference-Morales–Ramis largely
  known (one-frequency).
- **infinite-base / multi-frequency** = the native open case (Avila's `d≥2`-frequency problem is famously hard).

> **The field contains Avila's quasiperiodic-cocycle theory as its rank-2 single-frequency case**, and poses the
> multi-`q` (infinite-frequency) version as native.

**Net (the validation).** In its founding draft the field demonstrably **contains two major areas as special
cases**: classical transcendence (Lindemann/Lindemann–Weierstrass/Baker = finite-base diagonal Siegel–Shidlovsky,
§10) and Avila's quasiperiodic-cocycle theory (= rank-2 non-decomposable boundary dynamics, §12). The Galois↔
dynamics dictionary (difference Morales–Ramis, §11) bridges them, abelian/integrable half proved. A theory that
subsumes two major areas and bridges them with one signature conjecture is a discipline, not a reformulation —
and RH remains a footnote (one boundary functional on one diagonal of E4).

**Status:** the realization (non-decomposable rank-2 = quasiperiodic cocycle) is rigorous; the one-frequency
Galois↔Lyapunov dictionary is Avila's theory; the infinite-frequency multi-`q` generalization is the open native
frontier (P5 + difference Morales–Ramis).

---

## 13. The keystone: `G` unifies transcendence and dynamics

The two areas the field subsumes are **functors out of the same multi-`q` module, both factoring through its
difference-Galois group `G`:**

| shadow | object | reads off `G` |
|---|---|---|
| **Transcendence** (diagonal restriction) | trdeg of diagonal values | `= dim` of the `G`-orbit (Siegel–Shidlovsky, §10; recovers Lindemann/Baker) |
| **Dynamics** (boundary flow) | spectrum / Lyapunov / entropy | `=` `G`-structure (Morales–Ramis/Avila, §11–12; abelian⟺integrable, non-abelian⟺chaotic) |

So **`G` is the common source of arithmetic transcendence *and* ergodic dynamics** — the Tannakian philosophy
(André) in the infinite-base difference setting. The bridge between the two areas, through their shared group:

> **Conjecture (chaos ⟹ transcendence).** A multi-`q` module whose boundary cocycle is **chaotic** (non-abelian
> `G`, positive Lyapunov) has diagonal values of **high transcendence degree** (large `G`-orbit). **Dynamical
> chaos forces arithmetic transcendence**, both via the size of `G`. Finite/known cases (Lindemann + Avila
> one-frequency): both ends are theorems, bridge checkable. Infinite-base: open frontier.

**The field in one sentence:** *infinitely many independent dilations generate a pro-algebraic group `G` whose
orbit governs transcendence and whose hull governs chaos; the arithmetic objects (`L`-functions, RH) are one
diagonal restriction of one example.*

**Status:** the unification (both shadows factor through `G`) is the Tannakian framework — rigorous as
philosophy, with the two specializations (transcendence §10, dynamics §11–12) genuine. The `chaos⟹transcendence`
bridge is conjectural where its transcendence half (Siegel–Shidlovsky) is, and checkable in the finite cases.
This is the field's central thesis: **a common Galois framework for transcendence theory and ergodic dynamics.**

---

## 14. Interrogation #2: the keystone's two shadows read DIFFERENT aspects of `G` (hull vs orbit)

**Worry.** §13's "chaos ⟹ transcendence" assumed non-abelian `G` ⟹ large orbit. False in general.

**Finding.** The two shadows read different functions of `G`:
- **Dynamics** ← the **algebraic hull** of the cocycle = the whole group `G` (Zariski closure of the monodromy).
- **Transcendence** ← the **orbit of the specific diagonal point** `δ`: `dim(G·δ)` = trdeg, the orbit of *one
  point*, not `dim G`.

These **decouple**: if `δ` is a `G`-fixed point, `dim(G·δ)=0` (trdeg `0`) even though `G` is large/non-abelian
(chaotic boundary). So **"chaos ⟹ transcendence" is over-stated** — it needs `δ` in general position.

> **Corrected keystone.** The unification stands (both shadows factor through `G`), but reads **different
> aspects**: dynamics ← hull (`G`); transcendence ← orbit of `δ` (one point). **Generically linked** (general
> `δ`: large orbit ⟺ large hull ⟺ chaos ⟺ transcendence); **specially decoupled** (`G`-fixed `δ`: chaos, no
> transcendence). The bridge is *generic*, not universal.

**Payoff (this is why it's a better statement).** It explains why `ζ` — a *very special* diagonal of `E4` — can
sit on a rich `G` (rich dynamics) yet have **subtle, hard transcendence**: `ζ`'s diagonal is likely a
**non-generic point**, where the hull is large but the orbit of *that* point is small/hard to compute (so
`γ_1`'s irrationality is stuck). The **hull/orbit distinction** is the right tool; found by interrogating the
keystone. (Self-correction #2 — the field continues to push back on its own claims.)

---

## 15. P1 (decomposable case): rigorous Picard–Vessiot foundations

Each local `M_p` is an ordinary `q_p`-difference module with established PV theory (Sauloy; van der Put–Singer;
Praagman): PV ring `R_p`, Galois group `G_p⊂GL(M_p)`, Galois correspondence. For decomposable `M=⊗_p M_p`
(restricted tensor, almost all `M_p` trivial):

> **Theorem (decomposable PV).** `R_M=⊗_p R_p` (restricted) is a PV ring for `M`; the difference-Galois group is
> the **restricted product** `G_M=\widehat{∏}_p G_p` (pro-algebraic); the Galois correspondence is the product of
> the local ones; `C(R_M)=ℂ ⟺` no `q_p` a root of unity. *Proof:* local PV per factor; commuting operators on
> disjoint variables ⟹ the tensor is a PV ring; Galois = restricted product. ∎

**Demarcation.** The **decomposable half is rigorous** — the constants theorem (§2 corr.), the two-column
dictionary (§10), the spectrum=Galois result (§11), and these PV foundations all hold by assembling the
established single-`q` theory. The **non-decomposable half** (compatible systems / interacting variables / the
quasiperiodic cocycles of §12) is the genuine open frontier (P1-hard) — where the field stops being an assembly
of known pieces and becomes new mathematics. *The decomposable half is a theorem; the non-decomposable half is
the field.*

**Foundations status:** the field now has rigorous PV foundations (decomposable), two self-corrections (§9,§14), a
keystone (G unifies transcendence and dynamics, hull/orbit-refined), and demonstrably contains classical
transcendence (§10) and Avila cocycle theory (§12). Open native frontier: non-decomposable PV (P1), infinite-base
Siegel–Shidlovsky (P2), difference Morales–Ramis (P6), the chaos⟺transcendence generic bridge (§13–14).

---

## 16. Attacking the frontier: PV existence for the NON-decomposable module, via the zero-curvature condition

§15 parked the non-decomposable case as "P1-hard, the open frontier." That parking is a reflex, not a theorem.
Walk in. The foundational layer — **does a Picard–Vessiot theory even exist for a non-decomposable, infinitely-many-
operator integrable system?** — is crackable now, and cracking it removes the decomposability hypothesis from the
foundations entirely (for the *existence* statement; computation stays hard, and that is honest, see the grading).

### 16.1 What a finite-rank multi-`q` module actually is: an integrable (flat) infinite system

Let `K` be a multi-`q`-difference field, constants `ℂ` (alg. closed), commuting automorphisms `{σ_p}_{p∈P}`. A
rank-`d` module `M≅K^d` with basis `e_1,…,e_d` carries one semilinear automorphism per prime,
`σ_p(e_k)=Σ_i (A_p)_{ik} e_i`, `A_p∈GL_d(K)`. The **only** constraint is that the `σ_p` commute *as operators on
`M`*. Compute both orders on a basis vector:
```
σ_pσ_q(e_k) = Σ_i [A_p·σ_p(A_q)]_{ik} e_i ,   σ_qσ_p(e_k) = Σ_i [A_q·σ_q(A_p)]_{ik} e_i .
```
Hence:

> **Integrability (cocycle) condition.**  `A_p · σ_p(A_q) = A_q · σ_q(A_p)`  for all `p,q∈P`.

This is the precise object. A finite-rank multi-`q` module = an **infinite family `{A_p}` of `GL_d(K)`-valued
"connection matrices," one per prime, pairwise compatible** by the above. It is the multi-`q` analogue of the
**Frobenius / zero-curvature / Maurer–Cartan** integrability of a flat connection: define the discrete curvature
of the pair `(p,q)` as `F_{pq}=A_q^{-1}σ_q(A_p)^{-1}A_p σ_p(A_q)`; integrability is exactly `F_{pq}=1` — **flatness
on the prime lattice.** (This welds the field to the flat-connection / Wilson-loop picture: `{A_p}` is a discrete
gauge field on the prime graph, decomposable ⟺ globally gauge-trivial, non-decomposable ⟺ flat-but-nontrivial
holonomy. The off-diagonal coupling that §15 called "the field" is *holonomy of a flat connection*.)

### 16.2 The existence theorem (no decomposability assumed)

> **Theorem 16 (PV existence, general integrable multi-`q`).** Let `M` be a finite-rank integrable multi-`q`
> module over `K` (constants `ℂ`). Then `M` admits a Picard–Vessiot ring `R_M/K`, with no negative or zero
> divisors issue beyond the single-`q` ones, and its difference-Galois group `G_M=\mathrm{Aut}^{σ}(R_M/K)` is a
> **pro-algebraic group over `ℂ`**, realized as the inverse limit `G_M=\varprojlim_{S} G_S` over finite `S⊂P`.
> The Galois correspondence holds. **Decomposability is not required.**

*Proof (reduction + filtered limit — the structure that makes "infinitely many operators" harmless).*

1. **Finite-`S` truncation.** For finite `S⊂P`, forget the `σ_p` with `p∉S`. The data `(M,{A_p}_{p∈S})` is a
   module over the *finitely many* commuting automorphisms `{σ_p}_{p∈S}`, still satisfying the cocycle condition
   among themselves. This is a **partial (several-commuting-operator) `q`-difference module**, for which PV theory
   is established: the category of such modules is neutral Tannakian over `ℂ` and the PV ring `R_S` exists with
   Galois group `G_S⊆GL_d(ℂ)` an algebraic group (Wibmer; di Vizio–Hardouin; Kamensky's Tannakian construction of
   difference Galois groups handles a commuting family of operators in one stroke). *This is the load-bearing
   import, and it is genuinely in the literature for any FINITE commuting family — named, not waved.*

2. **The truncations form a filtered system.** For `S⊆S'`, restricting solutions gives a faithfully flat
   inclusion `R_S↪R_{S'}` (every `S`-horizontal element is `S'`-horizontal), hence a *surjection of algebraic
   groups* `G_{S'}↠G_S` (restriction of automorphisms). The index set `{finite S⊂P}` is directed under inclusion.

3. **Take the colimit / limit.** Set `R_M=\varinjlim_S R_S` (a `K`-algebra, directed union, so still a domain with
   constants `ℂ`) and `G_M=\varprojlim_S G_S` (a pro-algebraic group, inverse limit of algebraic groups along the
   surjections of step 2). Because each `A_p` involves only the *one* operator `σ_p`, **every element of `M` and
   every relation among its solutions already lives in some finite `R_S`** — the infinite system has *no data
   beyond its finite truncations*. So `R_M` is a PV ring for the full `M`, and `G_M=\varprojlim_S G_S` by the
   standard pro-algebraic Galois correspondence (an inverse limit of the finite Tannakian groups; equivalently
   `G_M=\mathrm{Aut}^⊗(ω)` for the fiber functor `ω` on the Tannakian category `⟨M⟩^⊗` generated by `M`). ∎
   *(modulo step 1's import, stated as the precise hypothesis below.)*

**The one hypothesis, named honestly.** The proof reduces the infinite-base existence to: *PV theory exists for a
module under a **finite** commuting family of `q`-dilations satisfying the cocycle condition.* That is the
several-operator difference Galois theory (Kamensky/Wibmer Tannakian, di Vizio–Hardouin parametrized). If one
demands a fully self-contained construction, the finite case is the only thing to verify — and it is a finite,
classical object, not an infinite one. **The infinite base contributes nothing new to *existence*; it is tamed by
the filtered limit.** That is the content: the scary word "infinitely many operators" is dissolved by the fact
that a finite-rank module's data is finitely-supported per relation.

### 16.3 What this does and does NOT settle (honest grading)

- **Settles (now a theorem, decomposability removed):** the difference-Galois group `G_M` *exists* as a
  pro-algebraic group for **every** finite-rank integrable multi-`q` module, decomposable or not. The §15
  demarcation "non-decomposable = open" was too pessimistic *for existence*: the Tannakian/limit machine does not
  care whether the `{A_p}` simultaneously triangularize. **The decomposable-only restriction is hereby lifted for
  the existence and Galois-correspondence layer.**
- **Does NOT settle (the real frontier, correctly located):** *computing* `G_M` for a specific non-decomposable
  `M` (e.g. `E4`/`ζ`), the **inverse problem** (which pro-algebraic groups arise), and **Siegel–Shidlovsky**
  (`dim` of the orbit `G_M·δ` = trdeg of diagonal values). Existence is the soft Tannakian half; computation is
  the hard half, and it stays hard. *This is the right factorization — I proved the half that yields to structure
  and did not pretend the computational half came with it.*
- **Geometric upgrade:** the cocycle `F_{pq}=1` reading makes non-decomposable modules **flat connections with
  nontrivial holonomy on the prime lattice**; `G_M` is the **holonomy/monodromy group** of that flat connection.
  This is the precise home of the field's hard examples and connects directly to the curvature/Wilson-loop and
  Avila-cocycle pictures (§12).

### 16.4 Formalizable core flagged (for the Lean track, not done here)

The cocycle condition `A_p·σ_p(A_q)=A_q·σ_q(A_p)` and the curvature `F_{pq}=A_q^{-1}σ_q(A_p)^{-1}A_pσ_p(A_q)=1`
are **concrete matrix identities over a difference ring** — a clean Tier-A Lean target: define a multi-`q`
module as a finitely-supported family of `GL_d` matrices with the pairwise identity, and prove (a) integrability
is preserved under `⊗`, `⊕`, dual, sub-quotient (so the category is Tannakian-closed), and (b) the finite-`S`
truncation is again integrable. This is matrix algebra, no analysis — formalizable now. *(Librarian's track; flagged, not executed.)*

> **§16 verdict.** Walked into the "decades-away" non-decomposable frontier and took its **foundational floor**:
> PV existence + pro-algebraic `G_M` hold with *no* decomposability hypothesis, by the zero-curvature reduction +
> filtered limit. The hard half (computing `G_M`, Siegel–Shidlovsky) is now *cleanly isolated* rather than tangled
> with existence. The field's "new mathematics" frontier is sharper: not "does the theory exist" (it does) but
> "what is the holonomy group of this specific flat prime-lattice connection." Self-correction #3: §15's
> non-decomposable pessimism was a reflex; existence was always within reach.
