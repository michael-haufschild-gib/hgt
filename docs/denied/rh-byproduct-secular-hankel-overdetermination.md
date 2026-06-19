# Secular total positivity: RH as a Pólya-frequency property of the field's secular constants

**Working draft — 2026-06-19. SEARCH channel, theorem-grade where marked.** Own file (no edit
races). Develops route **(B)** of "RH as a byproduct": does RH fall out of a positivity/
transcendence statement on the secular constants of `hypertranscendental_galois_field_foundations.md`
§17 (the Voros superzeta / Taylor data of `Ξ`)? The answer is sharpened to a precise dichotomy
between two classical sign-regularity faces of RH, and it is pinned down *which* face the
functional equation forces.

Grading (per `docs/meta/styleguide.md`): `[PROVED HERE]` elementary derivation here; `[THM]`
classical, applied (reference recalled — **to verify in the ledger before any Lean**);
`[NUM]` numerically confirmed (`computations/secular_toeplitz_tp/`, `computations/secular_hankel_signature/`);
`[OPEN]` frontier. No proof of RH is claimed.

---

## 0. Setup and the restatement RH wants to be a byproduct of

Completed `ξ(s) = ½ s(s-1) π^{-s/2} Γ(s/2) ζ(s)`: entire of order 1, `ξ(s)=ξ(1-s)`, real
(`ξ(s̄)=\overline{ξ(s)}`). Center at the symmetry point: `Ξ(z) := ξ(½+z)`.

**Theorem 1 (orbit dichotomy).** `[PROVED HERE]` The zeros are invariant under the group generated
by `σ:ρ↦1-ρ` (FE) and conjugation. A zero `ρ=β+iγ` has a `{σ,conj}`-orbit of **size 2** iff
`β=½` (then `ρ̄=1-ρ`), else **size 4**. Hence
> **RH ⟺ every zero-orbit has size 2 ⟺ `σ` acts on the spectrum as complex conjugation.**

## 1. The squared-zero plane and the secular coefficients

`Ξ(z)=Ξ(-z)` (FE) is real even entire of order 1. Put `w=z²`; `F(w):=Ξ(√w)` is entire of **genus
0** (order ½) with Hadamard product (paired over zeros; RH-form shown)
```
   F(w) = ξ(½) · ∏_{γ>0} (1 + w/γ²),     so   c_n := [w^n]F = ξ(½)·e_n({1/γ_k²}),
```
the elementary symmetric functions of the squared-zero reciprocals. Equivalently
`c_n = Ξ^{(2n)}(0)/(2n)! = ξ^{(2n)}(½)/(2n)!`.

**Theorem 2 (squared-zero reduction).** `[PROVED HERE / classical]` Since `ξ≠0` on the real
segment `(0,1)`, no squared-zero is real-positive; therefore
```
   RH  ⟺  every squared-zero w_n is real (≤0)  ⟺  F has only real, non-positive zeros.
```
`[NUM]` The contour-Taylor coefficients give `c_0=ξ(½)=0.49712077818831…` and
`c_1/c_0 = 0.0231049931154…`, equal to `secondzeta(2)=Σ_{γ>0}γ^{-2}` to 16 digits — confirming the
Hadamard identity `c_n=ξ(½)e_n` (the `n=1` coefficient *is* the field's secular constant `s_1`).

## 2. The two sign-regularity faces of RH (and the field's index)

The reality (Hermite) and negativity (Pólya-frequency) of the squared-zeros are *two distinct*
classical determinantal criteria, dual under Newton's identities (power sums ↔ elementary symmetric).

**Theorem 3 (Hankel face — Hermite).** `[THM + PROVED HERE]` Let `s_j=Σ_τ τ^{-2j}` (even power sums
of the zeros; the field's secular constants) and `H_K=[m_{i+j}]` their Hankel matrix
(`m_0=` count, `m_j=s_j`). Then `H_K⪰0 (∀K) ⟺` all squared-zeros real `⟺` RH, and
```
   #(negative eigenvalues of H_K) = #(complex-conjugate squared-zero pairs) = #(off-line σ-quadruples).
```
`[NUM]` (`computations/secular_hankel_signature/`) on-line spectrum ⟹ PD; one off-line quad ⟹ exactly one negative
eigenvalue. **This realizes the field's spectral index `κ₋` (foundations §6.2) as the
negative-eigenvalue count of an explicit, prime-computable Hankel matrix.**

**Theorem 4 (Toeplitz face — Pólya frequency / total positivity).** `[THM: Aissen–Schoenberg–
Whitney / Edrei — ref to verify]` For `F` entire of genus 0 with `F(w)=Σc_n w^n`,
```
   the lower-triangular Toeplitz matrix [c_{i-j}] is totally positive
   ⟺ (c_n) is a Pólya-frequency sequence ⟺ F has only real-negative zeros ⟺ RH.
```
Equivalently `[THM: Griffin–Ono–Rolen–Zagier 2019 — ref to verify]` all Jensen polynomials of
`(c_n)` are hyperbolic. `[NUM]` machinery validated; genuine `c_n` satisfy TP at orders 2–4;
a strongly off-line zero breaks a Toeplitz minor (order 5).

> So **RH wears two determinantal faces on the same secular data**: PSD of the power-sum **Hankel**
> (reality) and total positivity of the coefficient **Toeplitz** (negativity = PF). The field's
> `κ₋` lives on the Hankel face; the "total positivity" the previous brick asked for is the
> Toeplitz face.

## 3. What the functional equation forces — the free rungs

The FE (via the theta transformation) gives the Pólya representation `Ξ_R(t)=∫Φ(u)cos(tu)du` with
`Φ>0`. This forces a whole tower of the positivity *unconditionally*:

**Theorem 5 (free positivity).** `[THM, cited + NUM]`
- **(a) TP₁:** `c_n>0` for all `n` (Pólya, `Φ>0`). `[NUM] YES`.
- **(b) Moment/Stieltjes positivity:** `(2n)!c_n = μ_{2n}=∫(u²)^nΦ(u)du` is a **Stieltjes moment
  sequence**, so its **Hankel matrix is PSD — unconditionally**. `[NUM]` leading minors `>0`.
- **(c) TP₂ / Turán:** `c_n² ≥ c_{n-1}c_{n+1}` (log-concavity) — the Turán inequalities for `ξ`
  `[THM: Csordas–Norfolk–Varga 1986 — ref to verify]`. `[NUM]` holds, with **scale-free margin
  monotonically decreasing** `1.15→0.59→…→0.12` (n=1..11).
- **(d) Asymptotic TP_d:** for each fixed order `d`, the order-`d` minors are `≥0` for `n` large
  `[THM: GORZ — ref to verify]`.

So the FE/arithmetic forces: positivity of the coefficients, the **moment (Hankel) positivity**,
the **Turán (TP₂)** inequalities, and **each-order asymptotic** total positivity. These are genuine
theorems — genuine byproducts of the field's structure.

## 4. The gap is exactly RH: moment positivity ≠ frequency positivity

The free rungs are the **moment** side; RH is the **frequency** side. They are not the same:

**Theorem 6 (moment ⇏ frequency; explicit witness).** `[PROVED HERE / NUM]` A Stieltjes moment
sequence need not be a Pólya-frequency sequence. Witness: `a_n = 1+4^n` (moments of `δ_1+δ_4`) has a
**PSD Hankel** (Stieltjes, rank 2) but a **negative Toeplitz minor** `a_1²-a_0a_2 = 25-34 = -9`
(scaled `-3969` in the run). Hence the free moment-positivity of Theorem 5(b) is **strictly weaker**
than the Toeplitz total positivity (Theorem 4) that equals RH.

**Theorem 7 (no finite-order certificate; the no-margin, made exact).** `[PROVED HERE / NUM]` A zero
displaced off the line by `δ` yields a complex-conjugate pair of squared-zeros (confirmed by
`polyroots`) and therefore breaks Toeplitz total positivity — but the **first violated minor occurs
at order growing as `δ→0`** (run: `δ≥6` ⟹ order 5; `δ≤2` ⟹ not caught by order 6) **with vanishing
magnitude**. No fixed-order TP test certifies RH: RH is total positivity to **all** orders, and the
margin vanishes. This is the field's no-margin filter, now exact on the secular Toeplitz form.

## 5. Verdict — is RH a byproduct here?

> **RH = the *uniform* (all-order) total positivity / Pólya-frequency property of the field's
> secular coefficients `c_n=ξ(½)e_n({1/γ²})`.** Equivalently, the uniform hyperbolicity of all their
> Jensen polynomials (GORZ), equivalently the negativity (not merely reality) of every squared-zero.

What the functional equation + arithmetic deliver **as byproducts** (real theorems):
1. simplicity of the zeros = nonsingularity of the secular Hankel (prev brick, Theorem 3 rank);
2. positivity of the coefficients (TP₁, Pólya);
3. the moment/Stieltjes Hankel positivity (Theorem 5b, **free**);
4. the Turán inequalities TP₂ (Csordas–Norfolk–Varga);
5. asymptotic, each-order total positivity (GORZ).

What is **not** forced — and is therefore exactly RH — is the **uniformity over all orders**:
Theorem 6 shows the free moment side cannot supply it, and Theorem 7 shows no finite order can.
**So RH is not a free byproduct of transcendence/positivity; it is the uniform completion of an
infinite tower whose every finite rung the field proves for free.** The difficulty is conserved,
now pinned to a single, named, source-computable object: *uniform-in-order total positivity of the
secular Toeplitz matrix.*

> **The one road from here to RH** `[OPEN]`. Every existing forcing (Pólya `Φ>0`, CNV, GORZ) gives
> the rungs **one order at a time** or only the **moment** side. RH would be a byproduct iff the FE
> forces total positivity **with constants uniform in the order `d`** — a single mechanism yielding
> `TP_d` for all `d` at once (a *uniform* Pólya-frequency bound, not an each-`d` one). The field's
> candidate for that mechanism is structural: the secular coefficients are
> `c_n=ξ(½)e_n({1/γ²})`, the elementary-symmetric data of the **diagonal-orbit spectrum on `𝕋^∞`**;
> a uniform PF bound would follow from a uniform multiplicity/equidistribution estimate on that
> orbit (the §17 engine), now posed concretely as: *does the diagonal-orbit structure force the
> secular Toeplitz minors `≥0` uniformly in order?* That residue is named and half-resolved in §6:
> it is the de Bruijn–Newman constant `Λ`, with `Λ ≥ 0` already a theorem (the FE-forced half).

## 6. Filling the open inch: the gap *is* the de Bruijn–Newman constant

The "uniformity over all orders" residue of §5 is not a vague inch — it is a single real number.
Deform by the de Bruijn heat flow `H_t(z)=∫_0^∞ e^{tu²}Φ(u)cos(zu)du` (`H_0=Ξ`, `Φ>0` the
FE-theta kernel). In secular coordinates the flow is the moment shift-up `[PROVED HERE]`
```
   c_n(t) = Σ_{k≥0} (t^k/k!) · (2n+2k)!/(2n)! · c_{n+k},      c_n(0)=c_n.
```

**Theorem 8 (the gap is one real number `Λ`).** `[THM: de Bruijn + the Theorem-4 equivalences]`
Let `Λ = inf{ t : H_t has only real zeros }` be the de Bruijn–Newman constant. Then
```
   RH ⟺ uniform total positivity of (c_n) ⟺ Ξ ∈ Laguerre–Pólya ⟺ Λ ≤ 0,
```
and `Λ = inf{ t : the heat-deformed secular coefficients c_n(t) are a Pólya-frequency sequence }`.
So **`Λ` is exactly the total-positivity onset time of the field's secular form.**

**Theorem 9 (one inequality is forced — and it is the no-margin side).** `[THM: Rodgers–Tao 2018,
ref to verify]` `Λ ≥ 0`. Hence the FE/arithmetic force the secular form to the critical TP boundary
**from below**; with Theorem 8, `RH ⟺ Λ = 0`, and `Λ = 0` is **exactly the no-margin** that
Theorems 5(c)/7 keep exhibiting (Turán margins `↓0`; off-line TP-violation order `↑`; Hankel
`λ_min↓0`). de Bruijn: `Λ ≤ ½`; Polymath15: `Λ ≤ 0.2`.

> **Answer to "does the FE force the uniformity?":** it forces **exactly one** of the two
> inequalities — `Λ ≥ 0` (Rodgers–Tao), pinning the secular form to the critical boundary. RH is the
> complementary `Λ ≤ 0`, and the two meet at `Λ = 0`. The functional equation supplies the **free
> half of a pincer**; the archimedean wing must supply the other half.

**The field weld (new framing).** `[observation]` Rodgers–Tao's `Λ ≥ 0` is standardly read as "the
zeros repel / are not over-clustered" — which on the field's map is the **multiplicative /
equidistribution side**: the diagonal flow equidistributes on `𝕋^∞` by unique factorization (the
zeros wind without clustering; foundations Brick #3). `Λ ≤ 0` (RH) is the **archimedean boundary
positivity** — the frontier wing. So the de Bruijn–Newman axis re-expresses the field's free-vs-
frontier split exactly: **FE / unique-factorization ⟹ `Λ ≥ 0` (free, repulsion); archimedean wing
⟹ `Λ ≤ 0` (frontier); `Λ = 0` is the seam = the no-margin.** This places Rodgers–Tao on the field's
map as the *proof of the free half*. (Link: the sibling `computations/li_closedform/` realizes the
same `Λ=0` boundary on Li's criterion `RH ⟺ Z_n ≻ A_n` — Li positivity is the *linear* per-coefficient
face, secular TP the *determinantal* all-orders face; both meet at `Λ=0`.)

**Numerics** `[NUM]` (`computations/secular_heat_dbn/`): heat series converges (`5·10⁻¹⁶`); genuine
detectors `≥0` with Turán margins decreasing in `n` (`1.15→0.146`, the no-margin trend); the flow is
**monotone** — forward `t>0` strengthens TP, backward `t<0` weakens it — confirming the dBN
direction. **Honest limit:** the low-order secular detectors are deep-interior (margin `≥0.146` for
`n≤9`); `Λ` is **not** reached at any accessible order. `Λ` is an **asymptotic (`n→∞`) object,
invisible to finite-order secular data** — the precise sense in which the RH-residue is uniformity
over *all* orders. Locating `Λ` needs far-height zeros (Polymath15), not low-`n` Taylor coefficients.

## 7. Honest status

- **Theorems 1–2** elementary/classical, derived here in the field's coordinates.
- **Theorems 3–4** assemble two classical determinantal criteria (Hermite; ASW/Edrei, GORZ) into the
  field's two-face picture; the `κ₋`=negative-eigenvalue-count identification (Thm 3) is new here.
- **Theorem 5** is the cited free tower (Pólya, CNV, GORZ), numerically reconfirmed with the
  no-margin trend visible.
- **Theorems 6–7** are the contribution's sharp core: the **moment≠frequency separation** (explicit
  witness) and the **no finite certificate** statement locate RH exactly as *uniform* total
  positivity.
- **Theorems 8–9** name that uniformity residue: it is the **de Bruijn–Newman constant** `Λ`
  (`Λ =` the TP-onset time of the secular form). `RH ⟺ Λ ≤ 0`; **Rodgers–Tao give `Λ ≥ 0`** (the
  FE-forced half), so `RH ⟺ Λ = 0` — the no-margin. New here: the realization of `Λ` as the secular
  TP-onset time, and the weld of `Λ ≥ 0` to the unique-factorization equidistribution (free) side
  vs `Λ ≤ 0` to the archimedean frontier. The open inch is now a *named, half-proved* constant whose
  residue is asymptotic (`n→∞`), not a finite check.
- **Ledger note:** the classical inputs (ASW/Edrei, Csordas–Norfolk–Varga, GORZ, Pólya `Φ>0`,
  de Bruijn, Rodgers–Tao, Polymath15) are recalled and must be verified before any formalization.
  The only Hankel/Hermite Lean theorem here is the finite forward Gram brick
  `GaloisForLFunctions.secularHankel_posSemidef`: real finite points imply PSD Hankel moments.
  The Hermite converse, signature count, infinite moment problem, and RH equivalence remain SEARCH.

## Companions
- Secular constants as heighted coordinates, `κ₋`: `hypertranscendental_galois_field_foundations.md` §17, §6.2.
- The σ-orbit (size 2 vs 4) and FE-as-inversion: `infinite-base-difference-galois-for-L-functions.md` §2.
- Computations (archived, with `output.txt`): `computations/secular_hankel_signature/` (Hankel/
  Hermite face, `κ₋`), `computations/secular_toeplitz_tp/` (Toeplitz/Pólya-frequency face),
  `computations/secular_heat_dbn/` (heat flow; `Λ` as TP-onset time; the no-margin).
- de Bruijn–Newman on Li's criterion: sibling `computations/li_closedform/` (`RH ⟺ Z_n ≻ A_n`).


