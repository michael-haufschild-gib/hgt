# Monodromy Integrality (MI) for the abstract Rankin–Selberg series of the Selberg class

- **ID:** selberg-MI
- **Stage:** 1-in-progress
- **Type:** CONJECTURE (+ two proven implication theorems)
- **Source:** goal "prove/disprove Selberg's orthogonality conjecture"; log
  `selberg-orthogonality-working-log.md`
- **Statement (one line):** For all `F,G ∈ S` the series `R_{F,G}(w)=Σ_n a_F(n)conj(a_G(n))n^{-w}`
  is **meromorphic** (single-valued) at `w=1`; this alone forces Selberg's Conjecture A.

## 0. Notation

`S` = Selberg class. For `F,G ∈ S` put
```
R_{F,G}(w) := Σ_{n≥1} a_F(n) · conj(a_G(n)) · n^{-w}      (abs. conv. for Re w > 1, by Ramanujan)
```
`R_{F,G}` is a Dirichlet series with **multiplicative** coefficients (both `a_F`,`a_G` are
multiplicative by the Euler-product axiom), so it has an Euler product for `Re w > 1`:
`R_{F,G}(w) = ∏_p ( Σ_{k≥0} a_F(p^k) conj(a_G(p^k)) p^{-kw} )`, and
```
log R_{F,G}(w) = Σ_p a_F(p) conj(a_G(p)) p^{-w} + E_{F,G}(w),          (0.1)
```
where `E_{F,G}` converges absolutely and is holomorphic on `Re w > 1/2` (Ramanujan gives
`a_F(p^k) conj(a_G(p^k)) ≪_ε p^{2kε}`, so all `k ≥ 2` terms and all log-expansion cross terms are
`≪ Σ_p p^{-2Re w + ε}`).

## 1. The conjecture

> **(MI) Monodromy Integrality.** For every `F,G ∈ S` there is an open set `Ω ⊇ {Re w ≥ 1}` and a
> function meromorphic on `Ω` agreeing with `R_{F,G}` on `{Re w > 1}`, holomorphic and non-vanishing
> on `{Re w = 1} \ {1}`.
>
> Local form **(MI-loc)**: `R_{F,G}` is meromorphic on some disc `{|w-1| < δ}`.

**What is structurally new.** The received formulation of the missing ingredient for Selberg's
conjectures is *"`S` is closed under Rankin–Selberg convolution"* or *"every `F ∈ S` is
automorphic"*. Both demand of `R_{F,G}` a **functional equation, an Euler product of the correct
degree, entirety away from `w=1`, and a spectral interpretation.** MI demands **none of these**. It
demands only **single-valuedness** — a purely topological/local property (trivial local monodromy).
The claim being isolated here is:

> the entire arithmetic content of Selberg's Conjecture A is the *absence of a branch point* of
> `R_{F,F}` at `w = 1`.

That is a strictly weaker hypothesis than automorphy or RS-closure, and Theorem 1 below shows it is
already sufficient. Integrality of `n_F` becomes an *order of a pole*, i.e. a winding number, rather
than a representation-theoretic multiplicity.

**How it could fail.** `R_{F,F}` could have a branch point `(w-1)^{-κ}` with `κ ∉ Z` (this is what a
"fake" `F` with Satake data not coming from a compact group would produce), or a natural boundary on
`Re w = 1`, or an essential singularity. Any of these falsifies MI and simultaneously falsifies
Selberg's Conjecture A.

**Meeting the strongest parent theory.** If `F,G` are automorphic (`L(s,π)`, `L(s,π')`), then
`R_{F,G}(w) = L(w, π × ~π') · U(w)` with `U` holomorphic and non-vanishing on `Re w ≥ 1` (the
difference of local factors at ramified primes and the `k ≥ 2` corrections), so MI holds by
Jacquet–Piatetski-Shapiro–Shalika. Hence MI is implied by the automorphy conjecture, and is
consistent with every known element of `S`.

**[OPEN CORE]** No continuation of `R_{F,G}` past `Re w = 1` is known for a single `F ∈ S` that is
not already known to be automorphic. This is the first point not provable here.

## 2. Theorem 1 (MI ⟹ Selberg's Conjecture A). PROVED HERE.

> **Theorem 1.** Let `F ∈ S` and assume MI for the pair `(F,F)`. Then there is an integer
> `n_F ≥ 0` such that
> ```
> Σ_{p≤x} |a_F(p)|² / p = n_F · log log x + C_F + o(1)   (x → ∞).
> ```
> Moreover `n_F = −ord_{w=1} R_{F,F}`, and `n_F ≥ 1` iff the abscissa of convergence of `R_{F,F}`
> equals `1`.

**Proof.**
*(i) Convergence and positivity.* `R_{F,F}(w) = Σ_n |a_F(n)|² n^{-w}` has non-negative coefficients
and, by the Ramanujan axiom, converges absolutely for `Re w > 1`; so its abscissa of convergence
`σ_c` satisfies `σ_c ≤ 1`.

*(ii) The order at `w=1` is an integer `≥ 0`.* By MI, `R_{F,F}` is meromorphic on a neighbourhood of
`w=1`; set `n_F := −ord_{w=1} R_{F,F} ∈ Z`. If `σ_c < 1` then `R_{F,F}` is holomorphic at `w=1` and
`n_F ≤ 0`; since a holomorphic function cannot vanish at `w=1` (all coefficients `≥0`, `a_F(1)=1`
gives `R_{F,F}(w) ≥ 1` for real `w > 1`, hence `R_{F,F}(1) ≥ 1 > 0` by continuity), `n_F = 0`. If
`σ_c = 1`, then by **Landau's theorem** for Dirichlet series with non-negative coefficients, `w = 1`
is a singularity of `R_{F,F}`; by MI it is a pole, so `n_F ≥ 1`.

*(iii) Tauberian step.* Write `R_{F,F}(w) = (w−1)^{-n_F} H(w)` with `H` holomorphic and non-vanishing
on a neighbourhood of `{Re w ≥ 1}` (MI). Then
`−(R'/R)(w) = n_F/(w−1) − H'/H(w)`, and `−(R'/R)(w) = Σ_n Λ_R(n) n^{-w}` where
`Λ_R(n) ≥ 0` is supported on prime powers with `Λ_R(p) = |a_F(p)|² log p + (k≥2 corrections)`.
Non-negativity of `Λ_R` holds because `R_{F,F}` has non-negative multiplicative coefficients and
each local factor `R_p(w) = Σ_k |a_F(p^k)|² p^{-kw}` has non-negative coefficients with
`R_p(w) ≥ 1`, so `−R_p'/R_p` has non-negative Dirichlet coefficients [`−(log R_p)' = Σ_k c_k log(p^k)p^{-kw}`
with `c_k` the coefficients of `log R_p`; these need not be `≥0` — but the standard fix applies: use
instead the non-negative Dirichlet series `R_{F,F}` itself and the Wiener–Ikehara theorem in the form
below]. Precisely: apply the **Wiener–Ikehara theorem** to the non-negative Dirichlet series
`D(w) := −R'_{F,F}(w)/R_{F,F}(w)` when `n_F ≥ 1`; since `R_{F,F}` is holomorphic and non-vanishing on
`{Re w = 1}\{1}` and has a pole of order `n_F` at `w=1`, `D(w) − n_F/(w−1)` extends holomorphically to
a neighbourhood of `{Re w ≥ 1}`. `D` has coefficients `Λ_R(n) ≥ 0`?  — replace this step by the
following argument which needs no sign hypothesis on `Λ_R`:

By (0.1), `P(w) := Σ_p |a_F(p)|² p^{-w} = log R_{F,F}(w) − E_{F,F}(w)`, and `E_{F,F}` is holomorphic on
`Re w > 1/2`. Hence
```
P(w) = n_F · log( 1/(w−1) ) + G(w),      G holomorphic on a neighbourhood of {Re w ≥ 1}.   (2.1)
```
Differentiating, `−P'(w) = Σ_p |a_F(p)|² (log p) p^{-w}` is a Dirichlet series with **non-negative**
coefficients, and by (2.1)
```
−P'(w) = n_F/(w−1) − G'(w),   with G' holomorphic on a neighbourhood of {Re w ≥ 1}.
```
Wiener–Ikehara now applies verbatim (non-negative coefficients, single simple pole with residue
`n_F` at `w=1`, holomorphic continuation to the closed line) and yields
```
Σ_{p≤x} |a_F(p)|² log p = n_F · x + o(x).
```
Partial summation (`Σ_{p≤x}|a_F(p)|²/p = ∫_2^x (t log t)^{-1} d(Σ_{p≤t}|a_F(p)|² log p)`) gives
`Σ_{p≤x} |a_F(p)|²/p = n_F log log x + C_F + o(1)`. ∎

*(Note: (2.1) is exactly where MI is used twice — once to make `n_F` an integer, once to make
`log R_{F,F} − n_F log(1/(w−1))` single-valued, hence holomorphic, near `w=1`.)*

## 3. Theorem 2 (MI ⟹ integrality of the full complex Selberg pairing). PROVED HERE.

> **Theorem 2.** Let `F,G ∈ S` and assume MI for `(F,G)`. Then with
> `κ_{F,G} := −ord_{w=1} R_{F,G} ∈ Z`,
> ```
> Σ_p a_F(p) conj(a_G(p)) p^{-w}  =  κ_{F,G} · log( 1/(w−1) ) + O(1)      (w → 1+),
> ```
> and if in addition MI holds for `(F,F)` and `(G,G)` then `|κ_{F,G}|² ≤ n_F n_G`.

**Proof.** By MI, `R_{F,G}(w) = (w−1)^{-κ}H(w)` with `H` holomorphic, `H(1) ≠ 0`, near `w=1`. Choose a
branch of `log R_{F,G}` on a slit disc; by (0.1) `log R_{F,G}(w) = P_{F,G}(w) + E_{F,G}(w)` with
`P_{F,G}(w) = Σ_p a_F(p)conj(a_G(p))p^{-w}` (this identity holds for `Re w > 1` where the Euler product
converges absolutely and the principal branch is forced by `R_{F,G}(w) → 1`). Hence
`P_{F,G}(w) = κ log(1/(w−1)) + log H(w) − E_{F,G}(w)`, and `log H`, `E_{F,G}` are bounded near `w=1`.
The Cauchy–Schwarz bound follows from Theorem 1 applied to `F` and `G` together with
`|Σ_p a_F(p)conj(a_G(p))p^{-w}| ≤ (Σ_p|a_F(p)|²p^{-w})^{1/2}(Σ_p|a_G(p)|²p^{-w})^{1/2}` for real
`w>1` and (2.1). ∎

**Significance.** Selberg's Conjecture A by itself constrains only `Re B(F,G) ∈ (1/2)Z`
(§2.2 of the log, via `a_{FG}=a_F+a_G`), and says nothing about `Im B(F,G)`. **MI kills the imaginary
part outright**: `B(F,G) = κ_{F,G} ∈ Z`. So MI upgrades the Selberg pairing from "real part
half-integral" to "an integral positive-semidefinite Hermitian form on the monoid `S`".

## 4. Corollary 3 (what remains after MI). PROVED HERE.

Assume MI for all pairs in `S`. Then:
1. Conjecture A holds, with `n_F ∈ Z_{≥0}` (Theorem 1);
2. the Gram matrix of any finite family in `S` is an **integral** PSD Hermitian matrix (Theorem 2);
3. for `F,G` with `n_F=n_G=1` one gets `κ_{F,G} ∈ {0,±1}`, and `κ_{F,G}=±1` forces equality in
   Cauchy–Schwarz, i.e. `Σ_p |a_F(p) ∓ a_G(p)|²/p = O(1)`.

Hence **Conjecture B follows from MI together with exactly two further statements**:
- **(P1)** `n_F = 1` for every primitive `F ∈ S`;
- **(P2)** *(quantitative strong multiplicity one)* if `Σ_p |a_F(p) − a_G(p)|²/p = O(1)` with
  `F,G ∈ S`, then `F = G`.

(P2) is a genuine strengthening of the Murty–Murty / Soundararajan / Farmer strong-multiplicity-one
line, which currently assumes `a_F(p)=a_G(p)` outside a thin set. (P1) is the "cuspidal ⟹ Schur"
half. Both are now isolated as the only remaining obstacles once MI is granted.

## 5. Theorem 4 (axiom-necessity for the Energy Bound). PROVED HERE.

> **Theorem 4.** Let `F(s) := exp( Σ_p (log p)^{10} p^{-s} )`. Then `F` satisfies Selberg axioms
> (1) (Dirichlet series, absolutely convergent for `σ>1`, `a_F(1)=1`), (4) (Euler product:
> `log F(s)=Σ_n b_F(n)n^{-s}` with `b_F` supported on primes, `b_F(p)=(log p)^{10} ≪_θ p^θ` for every
> `θ>0`), and (5) (Ramanujan: `a_F(n) ≪_ε n^ε`); and
> `Σ_{p≤x}|a_F(p)|²/p ≍ (log x)^{20}`.
> Consequently the Energy Bound `Σ_{p≤x}|a_F(p)|²/p ≪ log log x` — hence Conjecture A — is **not**
> a consequence of axioms (1),(4),(5); every proof must use axiom (2) (continuation) or (3)
> (functional equation).

**Proof.** `a_F(p^k) = (log p)^{10k}/k!` and `a_F` is multiplicative. Ramanujan: fix `ε>0`; for
`p ≥ p_0(ε)` we have `(log p)^{10} ≤ p^ε`, so `a_F(p^k) ≤ p^{kε}`; for the finitely many `p < p_0(ε)`,
`sup_k (log p)^{10k}/k! = exp((log p)^{10})` is a constant, and the product of these finitely many
constants is `C(ε)`. Multiplicativity gives `|a_F(n)| ≤ C(ε) n^ε`. Absolute convergence for `σ>1`
follows. The Euler-product axiom holds with `b_F(p)=(log p)^{10}`, `b_F(p^k)=0` for `k ≥ 2`, and
`(log p)^{10} ≪_θ p^θ` for every `θ>0`, in particular for some `θ<1/2`. Finally
`Σ_{p≤x}(log p)^{20}/p = (log x)^{20}/20 + O((log x)^{19})` by partial summation from Mertens. ∎

*(Remark. This `F` fails axiom (2): `Σ_p(log p)^{10}p^{-s}` equals the 10-th derivative of
`Σ_p p^{-s} = Σ_k μ(k)k^{-1} log ζ(ks)`, which is meromorphic on `σ>1/2` with poles of order 11 at
`s=1` and at every zeta zero with `Re > 1/2`; so `F=exp(·)` has essential singularities there and no
continuation to `C`. It also fails axiom (3).)*

## 6. Phase-4 record: conjectures killed on the way

- **APR (Archimedean Phase Rigidity)**: "a pole of `R_{F,G}` at `w=1` forces `(d_F,q_F,θ_F) =
  (d_G,q_G,θ_G)`". **Verdict: FALSE.** Counterexample `F = ζ`, `G = ζ²`: `d_F=1 ≠ 2=d_G`, yet
  `R_{ζ,ζ²}(w) = Σ_n d(n) n^{-w} = ζ(w)²` has a double pole at `w=1`. *Lesson:* prime-side
  correlation tracks the **monoid/divisibility** structure, not the archimedean invariants; the
  vertical-phase cancellation heuristic (`X_F conj(X_G)` phases cancel iff `(d,q)` match) is not an
  obstruction to correlation. This kill is what redirected the search to a *local, topological*
  invariant (monodromy) instead of an archimedean one.
- **`σ_a(F) ≥ 1/2` (own derivation from "no zeros ⟹ contradiction with `N_F(T)→∞`")**:
  **Verdict: REDISCOVERED.** Kaczorowski–Perelli (Math. Z. 285 (2017) 1345–1355; arXiv:1506.07630)
  prove the stronger `σ_a ≥ 1/2 + 1/(2d_F)`.
- **"`ζ^{1/2}` calibrates Conjecture A"**: **FALSE as an axiom-sharpness example.** `ζ^{1/2}` fails
  axiom (3): `γ(1-s)/γ(s)` for a Selberg `γ`-factor cannot equal `χ(s)^{1/2}` (square roots of
  `Γ`-quotients have branch points), and `d = 1/2 < 1` is already excluded by Conrey–Ghosh. *Lesson:*
  fractional powers are excluded by the `Γ`-factor shape, so non-integral `n_F` cannot be produced
  that way; Theorem 4 gives the correct axiom-necessity statement instead.

## 7. Gates
- [x] 0 → 1: well-posed, source-pure, attack idea
- [ ] 1 → 2: needs MI itself (the [OPEN CORE]); Theorems 1,2,4 + Corollary 3 are complete and
      dependency-closed **as implications**
- [ ] 2 → 3: Lean — target `selberg_pair_p_sq_identity` (the §2.3 convolution identity) and the
      integral-Gram lemma
- [ ] 3 → 4

## 8. Log
- 2026-07-25 — created; Theorems 1,2,4 + Corollary 3 proved on paper; APR killed (ζ vs ζ²);
  `σ_a ≥ 1/2` found to be rediscovery of K–P.
