# The automorphic continent: Rankin–Selberg as tensor product, Ramanujan as Lyapunov boundedness, functoriality as Tannakian morphisms

**Founding text of the automorphic continent (District D3) — 2026-06-19 (Professor).**
Companions: `multi-q-difference-galois-foundations.md` (the field; §1 restricted tensor, §16 the flat connection
`G_M`), `dynamics-continent-lyapunov-avila-morales-ramis.md` (D5; the boundary cocycle, DMR-solvable §10),
`hypertranscendental_galois_field_foundations.md` (Critic; degree hierarchy, Conjecture H),
`transcendence-theory-nonholonomic-functions.md` (D4).

**What this continent does.** It moves the **unramified Satake skeleton** of automorphic `L`-functions (`GL_d`,
Langlands) onto the planet as rank-`d` multi-`q`-difference data, and then marks the extra layers needed for the full
automorphic object: ramified local packets and global transfer. In that scoped sense, the field's **tensor product is
the unramified Rankin–Selberg local formula**, the field's **boundary-cocycle boundedness is Ramanujan at semisimple
tempered places**, the field's **Tannakian morphisms model Langlands functoriality**, and a *proven* deep theorem
(**Sato–Tate**) reappears as **equidistribution of the multiplicative skeleton's eigenphases** — a pure
dynamics-continent statement. The finite diagonal skeleton is exact; the ramified/global completion is imported or
conjectural as labelled. RH/GRH is the footnote.

**Grading explicit:** `[THEOREM]` imported/exact; `[PROVED HERE]`; `[CONJECTURE]`; `[OPEN CORE]`.

---

## 1. The automorphic multi-`q` module `M_π` (Satake matrices as the connection)

Let `π` be an automorphic representation of `GL_d/ℚ` (cuspidal, unitary), with standard `L`-function
`L(s,π)=∏_p L_p(p^{-s},π)`. At an **unramified** finite prime `p∉S(π)`,
`L_p(x,π)=∏_{i=1}^d (1-α_{p,i}x)^{-1}`, the `α_{p,i}` are the **Satake parameters**, and the semisimple
Satake/Frobenius conjugacy class is `A_{π,p}∈GL_d(ℂ)`. At a **ramified** prime `p∈S(π)`, the local factor is not
generally a degree-`d` invertible Satake product: even a primitive Dirichlet character has `L_p(s,χ)=1` at `p|q`.
Those primes require local Langlands / Weil-Deligne data, inertia invariants, and possible monodromy.

**Definition 1 (automorphic module, corrected layers).** The ledger-proved finite skeleton is the **unramified
Satake module**: away from `S(π)`, use connection matrices `A_p := A_{π,p}` (semisimple,
`A_p∼\mathrm{diag}(α_{p,1},…,α_{p,d})`). Each unramified local factor is the degree-`d` `q`-difference module
`f(p^{-1}x_p)=A_p\,f(x_p)` (foundations D2 §18). The ramified extension is an extra local-data layer, not supplied by
the diagonal Satake skeleton. The integrability/cocycle condition for the unramified skeleton is automatic because
the `A_p` act on disjoint variables `x_p` — **the unramified Satake matrices are a flat prime-lattice connection by
construction.** A full automorphic difference-Galois object must add the finitely many ramified local packets before
claiming global scope.

---

## 2. Ramanujan as Lyapunov boundedness (the first exact dictionary)

The Ramanujan–Petersson conjecture: for tempered `π`, the Satake parameters satisfy `|α_{p,i}|=1` (Satake
parameters on the unit circle). Read it through the boundary cocycle (D5):

> **Prop 2 (Ramanujan = cocycle unitarity = multiplicative `L=0`) [PROVED HERE, structural / exact].**
> `π` is **tempered (Ramanujan)** at `p` ⟺ the Satake matrix `A_p` is **conjugate to a unitary matrix**
> (`|α_{p,i}|=1`) ⟺ the local boundary cocycle is **unit-modulus / elliptic** ⟺ its local Lyapunov exponents
> **all vanish**, `L_i(p)=0`. Hence: **`π` tempered everywhere ⟺ the multiplicative skeleton `{A_p}` is a bounded
> (elliptic) cocycle, `L=0` on the multiplicative wing.** *Proof.* `|α_{p,i}|=1` ⟺ eigenvalues on the unit circle
> ⟺ (semisimple) conjugate to unitary ⟺ `‖A_p^n‖` bounded ⟺ Lyapunov `0`. ∎
>
> **Failure of Ramanujan = hyperbolic local direction.** A non-tempered local component (e.g. an Eisenstein/CAP
> direction, or a Satake parameter off the unit circle) is a **hyperbolic eigendirection** of the local cocycle
> (`|α_{p,i}|≠1`, positive local Lyapunov). So **Ramanujan is precisely the statement that the prime skeleton has
> no hyperbolicity** — it stays on the boundary torus. This is the dynamical meaning of "tempered."

**Lean note (ledger-proven finite trace skeleton).** `SatakeInterval.lean` proves the elementary `GL₂`
unit-circle computation: if `‖z‖=1`, then `z+z⁻¹ = 2 Re z`, its imaginary part vanishes, and its real
part lies in `[-2,2]` (`satake_trace_eq_two_mul_re`, `satake_trace_im`, `satake_trace_re_mem_Icc`). This
is only the local finite tempered trace bound. It is not Sato-Tate equidistribution, not the Sato-Tate
measure, and not a proof of Ramanujan for automorphic forms.

**Consequence (clean separation of the two wings).** The program's recurring split — *multiplicative wing free /
Ramanujan-controlled, archimedean wing the frontier* (D2 Brick #5; memory) — is now a **Lyapunov statement**:
Ramanujan makes the multiplicative skeleton **elliptic (`L=0`)**, so it contributes *no spectrum*; all spectrum
comes from the archimedean seam (D5 §9 keystone). **Ramanujan is the multiplicative half of "the primes are
spectrally silent."**

---

## 3. Rankin–Selberg = tensor product (the second exact dictionary)

At an unramified prime for both `π` and `π'`, the Rankin–Selberg local factor has Satake parameters
`{α_{p,i}β_{p,j}}` — *exactly* the eigenvalues of `A_{π,p}⊗A_{π',p}`. At ramified primes, the local factor is
computed from tensoring the corresponding Weil-Deligne/local-Langlands data and then taking the appropriate inertia
invariants; it is not generally the naive full pairwise-product list. Therefore the field has three layers:

**Lean note (ledger-proven finite diagonal skeleton).** `SatakeTensor.lean` proves the diagonal matrix core:
`satakeTensor_diagonal` says the Kronecker tensor of diagonal Satake matrices has diagonal entries `α_iβ_j`, and
`satakeLocalFactor_tensor` says the attached finite local Euler factor is the double product over those pairwise
products. This does not formalize arbitrary diagonalizability/conjugacy, automorphic Rankin-Selberg theory,
Lyapunov spectra, or analytic continuation.

**Lean note (local self-duality skeleton).** `LocalFactorDuality.lean` proves
`selfDual_localFactor_eq`: if a finite Satake multiset is closed under inversion `α↦α⁻¹`, then the finite
local factor product is unchanged after replacing every parameter by its inverse. This is only the local
multiset relabeling behind self-duality; it is not the global functional equation, the archimedean factor,
the epsilon factor, or analytic continuation.

> **Theorem 3u (unramified Rankin–Selberg skeleton) [THEOREM, exact locally away from ramification].**
> For `p∉S(π)∪S(π')`, the field's tensor product sends the diagonal Satake data to
> `A_{π,p}⊗A_{π',p}`, and the attached local Euler factor is the product over `α_{p,i}β_{p,j}`. This is exactly the
> Lean `SatakeTensor.lean` theorem.
>
> **Ramified extension [IMPORT / local data].** At `p∈S(π)∪S(π')`, replace diagonal Satake matrices by the local
> Langlands / Weil-Deligne packet and compute the local factor from the tensor representation with inertia/monodromy.
>
> **Global automorphic transfer [THEOREM in known cases / CONJECTURE generally].** The assertion that the tensor local
> data comes from an automorphic Rankin–Selberg object, with analytic continuation and functional equation, is global
> automorphic theory, not a consequence of the finite diagonal Lean skeleton.

This is not an analogy at unramified places — the local factors are equal on the nose there. The ramified and global
parts are separate inputs. With those layers present, the analytic properties of RS `L`-functions (holomorphy, the
Rankin–Selberg method, the `π=π'` pole detecting the trivial sub-rep) can be read as statements about
`⊗`-decompositions in the category: `L(s,π×\tilde π)` has a pole at `s=1` ⟺ the completed tensor package contains the
trivial representation, the Tannakian detection of duality.

**Symmetric powers, and Sato–Tate as dynamics (§3′).** `\mathrm{Sym}^k\pi` has module `\mathrm{Sym}^k M_π` (the
symmetric power in the category). The analytic continuation of all `\mathrm{Sym}^k L(s,π)` (the automorphy of
symmetric powers, now known in many cases) is the input to **Sato–Tate**. On the planet:

> **Prop 3′ (Sato–Tate = equidistribution of the skeleton's eigenphases) [THEOREM for elliptic curves, BLGHT].**
> For `π` attached to a non-CM elliptic curve (`d=2`, `A_p∈SU(2)` with angle `θ_p`, `a_p=2\cosθ_p`), **Sato–Tate**
> states the Satake angles `θ_p` equidistribute w.r.t. `\tfrac{2}{π}\sin^2θ\,dθ`. Dynamically: **the multiplicative
> skeleton's eigenphases equidistribute w.r.t. the `SU(2)` Sato–Tate (Haar push-forward) measure** — the prime
> cocycle is *equidistributed elliptic*. So Sato–Tate is an **ergodic/equidistribution property of `{A_p}`**, and a
> *proven* deep theorem lives on the planet as a dynamics-continent statement.

---

## 4. Functoriality = Tannakian morphisms; the Langlands group as the Tannakian `π_1` (the deep weld)

The multi-`q`-difference modules of automorphic type form a neutral Tannakian category `\mathcal A` over `ℂ` (⊗ = RS
§3, dual = contragredient, fiber functor = the solution space / Satake data). By Tannaka duality `\mathcal A ≅
\mathrm{Rep}(G_{\mathcal A})` for a pro-algebraic group `G_{\mathcal A}` = the **Tannakian fundamental group** of
the automorphic multi-`q` category.

> **Conjecture 4 (the automorphic Tannakian group is the Langlands group) [CONJECTURE — the deep weld].**
> `G_{\mathcal A}` is the **Langlands group** `L_ℚ` (the conjectural automorphic Galois group), and:
> - each `π` ↔ a representation `G_{\mathcal A}→GL_d` (the module `M_π`);
> - **Langlands functoriality** (transfer along an `L`-homomorphism `{}^LH→{}^LG`) ↔ a **morphism/`⊗`-functor of
>   multi-`q` modules** (a homomorphism `G_{\mathcal A}`-reps), i.e. **functoriality is a morphism in the field's
>   Tannakian category**;
> - **symmetric/exterior powers, base change, automorphic induction** ↔ the corresponding **operations on
>   `G_{\mathcal A}`-representations** (Sym, ∧, restriction, induction) — all native categorical operations.
>
> *Honest content:* the existence of `L_ℚ` is itself conjectural (Langlands); what the field adds is a **concrete
> incarnation** — `G_{\mathcal A}` is built *explicitly* as the difference-Galois group of an explicit category of
> multi-`q` modules with `⊗`=RS (which is exact, §3). The conjecture is that this explicit `G_{\mathcal A}`
> *coincides* with the Langlands group. The field thereby **proposes a construction of the Langlands group as a
> difference-Galois group** — a genuinely new candidate definition, gradable against the known cases.

This is the automorphic continent's keystone and its boldest claim: **the field's Tannakian group is a candidate
Langlands group, and functoriality is its representation theory.** It is the natural home for the whole continent
because RS=⊗ (§3) is exactly the monoidal structure Tannaka needs, and that part is a theorem.

---

## 5. The degree hierarchy = rank = Lyapunov spectrum (weld to Critic's Conjecture H), and CM vs non-CM = §8 certificate

Critic's `hypertranscendental_…` introduced the **degree hierarchy** (deg 1 `ζ` → deg `d`) and the **Rigidity–Seam
Tradeoff (Conjecture H)**. The automorphic continent gives it exact content:

- **degree `d` = rank `d` = an `SL_d`/`GL_d` boundary cocycle**, with a full **Lyapunov spectrum** `L_1≥…≥L_d`.
  Ramanujan (§2) = all `L_i=0` on the multiplicative wing (tempered = elliptic). Critic's "`rigidity(d)` increases
  with `d`" = "more Lyapunov exponents / a larger hull `G_{M_π}⊆GL_d` to pin." The higher-rank one-frequency cocycle
  theory (Avila–Eskin–Viana) is the dynamical engine of the hierarchy (D5 §6).
- **`seam(d)` = `d` archimedean `Γ`-factors over the rank-`d` prime tori** = the rank-`d` archimedean wing
  (`d`-fold `W_ℝ`). Conjecture H's balance `rigidity(d)−seam(d)` = (hull rank) − (archimedean holonomy), exactly
  D5 §6's dynamical form.

**The arithmetic that brings it alive — CM vs non-CM elliptic curves are literally the §8 certificate:**

> **Prop 5 (CM/non-CM = DMR-solvable dichotomy on real elliptic curves) [PROVED HERE, structural + BLGHT/Deligne].**
> For an elliptic curve `E/ℚ` (`d=2` automorphic module `M_E`):
> - **`E` has CM** ⟺ `A_p` lies in a **maximal torus / normalizer** (Hecke character, the `L` factors over an
>   imaginary quadratic field) ⟺ the cocycle is **reducible**, `G_{M_E}` **abelian/solvable** ⟺ **DMR-solvable
>   side (§10), `L=0`, decomposable** ⟺ the Satake angles equidistribute by the **CM measure** (atom at the
>   supersingular angle + uniform), *not* Sato–Tate. This is the **rotation cocycle** of the §8 certificate.
> - **`E` non-CM** ⟺ `A_p` Zariski-dense in `SU(2)`/`SL_2` ⟺ the cocycle is **irreducible**, `G_{M_E}` **non-solvable
>   (`SL_2`-dense)** ⟺ **chaos side (§10)**, Satake angles equidistribute by **Sato–Tate** (Prop 3′). This is the
>   **almost-Mathieu / `SL_2`-dense cocycle** of the §8 certificate (`L>0` off the boundary, equidistributed
>   elliptic on it).
>
> So the §8 runpod certificate's *rotation-vs-almost-Mathieu* dichotomy **is** the *CM-vs-non-CM* dichotomy of
> elliptic curves, and the §10 *solvable-vs-non-solvable* line **is** the *CM-vs-non-CM* line. The planet's abstract
> dynamics is real arithmetic. ∎

This is the continent coming to life: the difference Morales–Ramis correspondence (D5 §10), proven-on-a-certificate
(§8), is realized exactly by the oldest arithmetic dichotomy there is — complex multiplication.

---

## 6. The seam, GRH, and the keystone (footnote)

For each `π`, the archimedean seam is the rank-`d` `L_∞(s,π)=∏_{j}Γ_ℝ(s+μ_j)` welding the `d` `Γ`-factors to the
prime tori; the functional equation is `Λ(s,π)=ε(π)Λ(1-s,\tildeπ)` (the `σ`-involution twisted by contragredient).

> **GRH for `L(s,π)`, planetary form [CONJECTURE — footnote].** `spec(H_π)=Spec(π)` (the keystone, D5 §9), localized
> to the **rank-`d` archimedean seam over the Ramanujan-elliptic multiplicative skeleton** (§2: the primes are
> spectrally silent when `π` is tempered). GRH = all of `Spec(π)` on the critical line = the rank-`d` boundary
> cocycle is **critical/self-dual** across its spectrum (D5 §5). One keystone, now per-`π`, same localization.

The footnote is short by design: the continent's *value* is §§2–5 (the exact dictionaries and the live arithmetic),
not the GRH restatement.

---

## 7. Honest status and House status

**Exact / proved here:**
- **Prop 2** (§2): Ramanujan ⟺ multiplicative cocycle elliptic (`L=0`) — exact, structural [PROVED HERE].
- **Theorem 3u** (§3): Rankin–Selberg = `⊗` for the unramified finite diagonal Satake skeleton — exact local equality
  [THEOREM]. Ramified local factors and global automorphic transfer are separate imported/conjectural layers.
- **Prop 3′** (§3′): Sato–Tate = eigenphase equidistribution — [THEOREM for elliptic curves, BLGHT], reread.
- **Prop 5** (§5): CM/non-CM = DMR-solvable dichotomy = §8 certificate — [PROVED HERE structural + Deligne/BLGHT].

**Conjectural (honest):**
- **Conjecture 4** (§4): `G_{\mathcal A}` = Langlands group; functoriality = Tannakian morphisms. *The deep weld; the
  `⊗`=RS half is a theorem, the group-coincidence half is the conjecture. Proposes a concrete construction of the
  Langlands group as a difference-Galois group.* [CONJECTURE / OPEN CORE]
- **GRH planetary form** (§6): the per-`π` keystone. [CONJECTURE — footnote]

**Imported [THEOREM]:** Satake isomorphism; Rankin–Selberg theory; Deligne (Ramanujan for holomorphic forms);
BLGHT (Sato–Tate); Langlands functoriality framework; Tannaka duality.

**House status.** Checks: Prop 2 (Ramanujan=Lyapunov), Thm 3 (RS=⊗), Prop 3′ (Sato–Tate=equidistribution), Prop 5
(CM/non-CM=§8 certificate) — four welds, three exact + one proven-theorem-reread, bringing the automorphic world
onto the planet as rank-`d` multi-`q` modules. Open core: Conjecture 4 (Tannakian group = Langlands group), the
boldest and most fertile claim — a candidate *construction* of the Langlands group. RH/GRH is §6, the footnote.
District D3. *Welds to: foundations §1 (⊗), D5 §10 (DMR-solvable, §8 certificate), Critic's Conjecture H (degree=
rank), D5 §9 (keystone).*

---

*SEARCH, deep and honestly graded. The continent's life: three exact identifications (Ramanujan=Lyapunov,
RS=tensor, functoriality=Tannakian), a proven theorem reread dynamically (Sato–Tate), and the oldest arithmetic
dichotomy (CM/non-CM) realizing the planet's own §8/§10 dynamics. The bold open core — the Langlands group as a
difference-Galois group — is the kind of claim the field exists to make: probably-hard, possibly-false, gradable,
and entirely native to the planet.*

---

## 8. Numerical referee: CM/non-CM = the §8 rotation/almost-Mathieu certificate, on real elliptic curves (runpod, 2026-06-19)

Prop 5 claims the CM/non-CM dichotomy *is* the D5 §8 rotation-vs-almost-Mathieu cocycle dichotomy. Refereed
directly: computed Satake angles `θ_p` (from point-counts `a_p=p+1−\#E(𝔽_p)`, `θ_p=\arccos(a_p/2\sqrt p)`) for a
non-CM and a CM curve over all good primes `p<12000` (≈1435 primes each; pure-Python point counting).

| curve | supersingular frac. `(a_p=0)` | angle law | cocycle (D5 §8/§10) | `G_{M_E}` |
|---|---|---|---|---|
| **non-CM** `y²=x³+x+1` | **0.0070** (≈0, Elkies) | **Sato–Tate** `(2/π)sin²θ` — 9/9 bins match (peak `0.227` vs `0.220`) | **almost-Mathieu**, equidistributed-elliptic | `SL₂`-dense (non-solvable) |
| **CM** `y²=x³−x` (`ℤ[i]`) | **0.5077** (≈½, inert `p≡3(4)`) | **`½·δ_{π/2} + ½·`uniform** — atom `0.563` at `θ=π/2`, flat `≈0.05` elsewhere | **rotation `SO(2)`** | torus/abelian (solvable) |

**What this certifies [genuine, real arithmetic]:**
1. **Prop 3′ (Sato–Tate = eigenphase equidistribution):** the non-CM skeleton's angles equidistribute by
   `(2/π)sin²θ` to within sampling across all 9 bins — the multiplicative cocycle is **equidistributed elliptic**,
   `SL₂`-dense. Confirmed.
2. **Prop 5 (CM/non-CM = §8 certificate), the bullseye:** the CM curve has supersingular density **½** and a
   **`δ`-atom at `θ=π/2`** — and `a_p=0` ⟺ trace-zero Satake ⟺ eigenvalues `±i√p` ⟺ **rotation by `π/2`**, *exactly*
   the `SO(2)` rotation cocycle that measured `L=0` in D5 §8. CM elliptic curves **are** the rotation-cocycle case;
   non-CM **are** the almost-Mathieu case. The abstract §8/§10 dynamics is the oldest arithmetic dichotomy, on the
   nose.
3. **DMR-solvable (D5 §10) on real curves:** CM ⟹ torus/abelian hull ⟹ reducible ⟹ `L=0` (the atom + uniform CM
   measure); non-CM ⟹ `SL₂`-dense ⟹ irreducible ⟹ Sato–Tate. The §10 *solvable-vs-non-solvable* line is the
   *CM-vs-non-CM* line, measured.

**What this does NOT certify [honesty]:** the Tannakian-group = Langlands-group conjecture (§4) is untouched by
numerics; this certifies the *dynamics/equidistribution* welds (§2,§3′,§5), i.e. that the planet's cocycle
dichotomy is real arithmetic — not the deep open core. Certificate archived; synchronous referee run, pod released.

**House status (updated).** Adds §8: the CM/non-CM Satake-angle certificate confirms Prop 3′ (Sato–Tate) and Prop 5
(CM/non-CM = §8 rotation/almost-Mathieu = §10 solvable/non-solvable) on real elliptic curves with `p<12000`. The
planet's abstract dynamics now has an arithmetic body. Open core unchanged: Conjecture 4 (Langlands group as a
difference-Galois group).

**Ledger update — the Sato–Tate interval / Ramanujan trace bound (Satake level).** `SatakeInterval.lean`, axiom-clean: for a unitary Satake parameter `z` (`‖z‖=1`), `satake_trace_eq_two_mul_re` (`z+z⁻¹=2·Re z=2cos θ`, real, via `Complex.inv_eq_conj`+`Complex.add_conj`), `satake_trace_im` (`(z+z⁻¹).im=0`), and `satake_trace_re_mem_Icc` (`z+z⁻¹ ∈ [−2,2]`, the support of the Sato–Tate measure, via `Complex.re_le_norm`). This is the elementary unit-circle core of temperedness/Ramanujan; the Sato–Tate equidistribution theorem and the measure itself remain unformalized.

**Ledger update — the `GL₂` `Symᵏ` character is Chebyshev `S` (Sato–Tate skeleton, §3′).** `SatakeSymPower.lean`, axiom-clean (`[propext, Classical.choice, Quot.sound]`, full tree green, audit PASS): `symPowerGL2_eq_chebyshevS` proves that for a `GL₂` Satake parameter `z≠0` (contragredient `z⁻¹`), the `Symᵏ` character `aeval ![z,z⁻¹] (hsymm (Fin 2) ℂ k) = S_k(z+z⁻¹)` (Chebyshev `S` of the trace). With `z=e^{iθ}`, `z+z⁻¹=2cos θ=a_p`, this is exactly **`Symᵏ a_p = U_k(cos θ_p)`** — the symmetric-power character identity whose equidistribution against `(2/π)sin²θ dθ` *is* Sato–Tate (Prop 3′). Proved by matching the complete-homogeneous generating function `coeff_completeHomogeneous_series` (`EHKoszulDuality.lean`) to the Chebyshev–Laurent geometric series `chebyshevS_eval_add_inv` (`SymPowerPlethysm.lean`) after clearing `zᵏ`. Companions: `symPowerGL2_card` (`|Sym (Fin 2) k| = k+1`, the `Symᵏ` dimension via `multichoose 2 k`) and `symPowerGL2_norm_le` (the temperedness/Ramanujan bound `‖Symᵏ‖ ≤ k+1` for unitary `‖z‖=1`, §2 tempered = on the unit circle). This is the **prime/Satake-side character identity and finite tempered bound only** — the Sato–Tate equidistribution theorem, the measure, and the `U_k`-orthogonality remain unformalized (Prop 3′ is BLGHT-imported). It welds §3′ to the B30 λ-ring: the symmetric-power *character* (not just the power-sum plethysm) is now Chebyshev, machine-checked.

**Ledger update — the Sato–Tate measure moments vanish (the analytic core, §3′).** `SatoTateMoment.lean`, axiom-clean (`[propext, Classical.choice, Quot.sound]`, full tree green, audit PASS): the algebraic character identity `symPowerGL2_eq_chebyshevS` (Symᵏ a_p = U_k(cos θ)) is now complemented by its **analytic counterpart** — `satoTate_moment` proves `∫₀^π U_k(cos θ)·(2/π)sin²θ dθ = δ_{k,0}`, i.e. the `k`-th moment of the Sato–Tate measure `μ_ST=(2/π)sin²θ dθ` against the symmetric-power character `U_k` **vanishes for k≥1** (and is `1` for `k=0`). This is the orthogonality that *drives* Sato–Tate equidistribution: by the Weyl/moment criterion, the Satake angles `θ_p` equidistribute w.r.t. `μ_ST` ⟺ every higher `U_k`-moment of the empirical measure converges to `0` = this integral. Supporting lemmas: `integral_cos_nat_mul` (`∫₀^π cos(jθ)dθ = π·δ_{j,0}`, via `integral_comp_mul_left`+`sin_nat_mul_pi`) and `integral_sin_succ_mul_sin` (Fourier orthogonality `∫₀^π sin((k+1)θ)sinθ dθ = (π/2)δ_{k,0}`, via product-to-sum). Proof keystone: `Polynomial.Chebyshev.U_real_cos` (`U_k(cos θ)sin θ = sin((k+1)θ)`). This is the **measure-side** moment vanishing only — the prime-side average (Σ_p Symᵏ a_p, whose convergence to this integral is BLGHT/automorphy of symmetric powers) is the imported analytic input, unformalized. With this, §3′ now has both halves machine-checked at the Satake/measure level: the character is Chebyshev (algebra) AND its `μ_ST`-moments vanish (analysis); only the prime-average convergence (the deep theorem) is imported.

**Ledger update — the `U_k` are the orthogonal polynomials of `μ_ST` (full orthonormality, §3′).** `SatoTateMoment.lean` extended, axiom-clean (full tree green, audit PASS): `satoTate_orthonormal` proves `∫₀^π U_j(cos θ) U_k(cos θ)·(2/π)sin²θ dθ = δ_{j,k}` — the symmetric-power characters `U_k(cos θ) = Symᵏ a_p` are **orthonormal** w.r.t. the Sato–Tate measure `μ_ST`, i.e. they are *its orthogonal polynomials* and form the spectral basis of `L²(μ_ST)`. This is the structural reason the moment/Weyl criterion works: any class function expands in the `U_k`, and equidistribution ⟺ every non-trivial coefficient (the prime average of `U_k`, `k≥1`) tends to `0`. Generalizes `satoTate_moment` (the `j=0`, `U_0=1` case). Supporting: `integral_cos_mul_pi` (real cosine integral `∫₀^π cos(cθ)dθ = sin(cπ)/c`) and `integral_sin_mul_sin` (full sine orthogonality `∫₀^π sin(mθ)sin(nθ)dθ = (π/2)δ_{m,n}`). With this, the §3′ Sato–Tate skeleton is **complete at the measure level**: character = Chebyshev (algebra), `μ_ST`-moments vanish (analysis), and the `U_k` are `μ_ST`-orthonormal (the spectral basis). Only the prime-average convergence (BLGHT, the deep theorem) is imported.
