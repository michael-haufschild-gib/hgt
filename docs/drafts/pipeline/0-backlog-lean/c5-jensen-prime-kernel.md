# The Jensen-section prime kernel `K_d(r_l;p)` — pinned (first order)

- **ID:** c5-jensen-prime-kernel
- **Stage:** 0-backlog-lean
- **Type:** THEOREM (paper, supporting lemma) — Door grade **BRIDGE**
- **Priority:** FOUNDATIONAL
- **Source:** the flagged kernel input of `../1-in-progress/finite-free-convolution-flow.md` (Wheeler's
  root-displacement mechanism); Pólya–LP framework therein · 00-status #104
- **One sentence.** The prime-induced first-order displacement of the degree-`d` Jensen-section roots is
  `ε_l(t) = Σ_n c_n e^{−𝔦t\log n} K_d(r_l;n;t)` with **`c_p = p^{−1/2}`** (primes) and `K_d(r_l;p;t)` an
  **explicit degree-`≤ d` polynomial in `\log p`** with archimedean-only coefficients — confirming and
  making rigorous the kernel Wheeler flagged, and turning the root-collision/near-resonance mechanism into a
  concrete weighted-Bohr-resonance question.

---

## §1 Setup (Pólya–LP, Jensen at base point `t`, the Hadamard/explicit-formula prime part)
- `Ξ(z)=ξ(½+𝔦z)`, real entire, even, order 1; **RH ⟺ `Ξ∈LP` ⟺ `Ξ(t+·)∈LP` ∀t ⟺** every Jensen polynomial
  `J_d(X;t)=Σ_{j=0}^d \binom{d}{j}\frac{Ξ^{(j)}(t)}{j!}X^j` is hyperbolic (Pólya–Schur; Wheeler's verified
  framework correction in `finite-free-convolution-flow.md`). The degree-`d` section IS `J_d(·;t)`.
- **Multiplicative split.** `ξ(s)=ξ_∞(s)ζ(s)`, `ξ_∞(s)=½s(s−1)π^{−s/2}Γ(s/2)`; so `Ξ(z)=Ξ_{arch}(z)e^{P(z)}`
  with `Ξ_{arch}(z)=ξ_∞(½+𝔦z)` and the **prime part**
  `P(z) := \log ζ(½+𝔦z) = Σ_n \frac{Λ(n)}{\log n} n^{−½} e^{−𝔦z\log n}` (from `\log ζ(s)=Σ_n \frac{Λ(n)}{\log n}n^{−s}`).
  Its coefficients: `c_n = Λ(n)\,n^{−1/2}/\log n`; for a prime `n=p`, `Λ(p)=\log p` ⟹ **`c_p = p^{−1/2}`**
  (matching the flagged `c_p(t)∼ p^{−1/2}e^{𝔦t\log p}`); prime powers `c_{p^k}=p^{−k/2}/k` are subdominant.
  *(Regularization caveat: the Dirichlet series for `P` converges for `Im z<−½`; on the real axis `P` and its
  derivatives are the analytically-continued / explicit-formula (distributional) sums — the project's
  standard regularization. The amplitudes `c_n` are unchanged.)*

## §2 First-order root perturbation → the kernel `[PROVED HERE]`
By **Lemma A** (`finite-free-convolution-flow.md`: `J_d^{arch}(·;t)→` Hermite, `d` **distinct real** roots
`r_1,…,r_d`), each `r_l` is a **simple** root of the archimedean section, so first-order root perturbation
applies:
```
   X_l(t) = r_l + ε_l(t) + O(δ²),     ε_l(t) = − δJ_d(r_l;t) / ∂_X J_d^{arch}(r_l;t).
```
First order in the prime part (`Ξ=Ξ_{arch}e^P`, Leibniz): `δ(Ξ^{(j)})(t)=Σ_{i=1}^{j}\binom{j}{i}Ξ_{arch}^{(j−i)}(t)\,P^{(i)}(t)`,
and `P^{(i)}(t)=Σ_n c_n(−𝔦\log n)^i e^{−𝔦t\log n}`. Substituting into
`δJ_d(X;t)=Σ_{j}\binom{d}{j}\frac{X^j}{j!}\,δ(Ξ^{(j)})(t)` and collecting the frequency `e^{−𝔦t\log n}`:
> **Kernel.** `ε_l(t) = Σ_n c_n\, e^{−𝔦t\log n}\, K_d(r_l;n;t)`, with
> ```
>    K_d(r_l;n;t) = − \frac{1}{∂_X J_d^{arch}(r_l;t)} \; Σ_{i=1}^{d} (−𝔦\log n)^i\, B_i(r_l;t),
>    B_i(X;t) := Σ_{j=i}^{d} \frac{\binom{d}{j}\binom{j}{i}}{j!}\, Ξ_{arch}^{(j−i)}(t)\, X^j .
> ```
The `B_i(X;t)` are **archimedean-only** (built from `Ξ_{arch}^{(m)}(t)`), so `K_d(r_l;p;t)` is, in the prime
variable, a **polynomial in `\log p` of degree `≤ d`** with archimedean coefficients. ∎

## §3 Structure of the kernel `[read off §2]`
- **Amplitude.** The prime-`p` term of the displacement has size `c_p·|K_d| = p^{−1/2}·|\text{poly}_{≤d}(\log p)|`
  — geometric `p^{−1/2}` decay modulated by a degree-`≤ d` log-polynomial. Small primes dominate the amplitude;
  the degree-`d` polynomial is the bounded-degree (`≤ d` logs) signature of the structural lemma (ii)–(iv).
- **Frequencies.** `ε_l(t)` is a Bohr almost-periodic function of `t` with frequency set `{\log n}` (prime
  powers); the prime frequencies `{\log p}` carry the dominant amplitudes. This is exactly the diagonal Bohr
  orbit `θ_p(t)=−(t\log p)/2π`.
- **Bounded degree confirmed.** A support-`≤ d` combination of the displacement (the products entering
  `det H_j`, `j≤d`) involves at most `d` distinct prime frequencies — consistent with the Hankel↔combination
  -mode lemma (support `≤ d`).

## §4 Consequence for the C5 crux — the collision question, made precise `[the hand-off]`
Wheeler's mechanism: an RH violation ⟺ an **edge root collision**, `|ε_l(t)|` reaching the Hermite node gap
`Δ_l=|r_{l+1}−r_l|` (sparsest at the edge, `Δ_{edge}≍ d^{−1/6}`). With the kernel pinned, "does `\sup_t|ε_l(t)|`
reach `Δ_l`?" becomes the **concrete weighted-Bohr-resonance** question:
> does `\sup_t \big| Σ_p p^{−1/2} K_d(r_l;p;t)\, e^{−𝔦t\log p} \big|` reach `Δ_l`, uniformly in `d`?
This is a large-values / constructive-alignment problem for a Bohr sum with amplitudes `p^{−1/2}\text{poly}_{≤d}(\log p)`
— reached only when many prime phases `{t\log p}` align, i.e. a **support-`≤ d` near-resonance**
`Σ_p a_p\log p≈0` (DeWitt's integer-gap/Baker lane). The kernel thus **converts the conjectural displacement
form into a rigorous, well-posed analytic target** and pins the two remaining inputs: (a) the archimedean
gap/amplitude ratio `Δ_l` vs `p^{−1/2}|K_d|` (my lane), (b) the joint near-resonance bound (DeWitt).

## §5 Door passport
- **BRIDGE.** First-order perturbation theory + the explicit formula are parents; the content is the
  **explicit kernel** (the `c_p=p^{−1/2}`, the degree-`≤ d`-in-`\log p` archimedean form) that makes the
  native crux a concrete inequality. It **feeds**, not closes, C5★.
- **Door-1/3/4:** the displacement lives on the joint Bohr orbit `{t\log p}` (the native `t`-direction the
  orthogonality theorem isolates as the only RH-bearing axis); bounded support `≤ d`.
- **Door-2 (supports Wheeler's native claim):** the kernel is archimedean × per-prime-frequency — the seam.
  The single-prime (axis-mode) part is BRIDGE; the **joint** alignment that reaches `Δ_l` is the field's
  apparatus.

## §6 Critical-point evaluation + the divergence (Door-2 refinement) — 2026-06-19
Wheeler's Theorem-M assembly (`../1-in-progress/finite-free-convolution-flow.md`) evaluates the deformation
at the Hermite **critical points** `c_m` (where `C_d=He_{2d}` alternates, energy floor `|C_d(c_m)|≥1`), not
at the roots. The kernel transfers verbatim — replace `r_l` by `c_m`, and the `1/∂_X J_d^{arch}` factor
**drops** (we read the section *value*, not a root displacement):
> `D_d(c_m;t) = Σ_{p,k} K_d(c_m;p,k)\,e^{−𝔦kt\log p}`,
> `K_d(c_m;p,k) = \frac{p^{−k/2}}{k}\,Q(k\log p;\,c_m)`, `Q(x;c_m)=Σ_{i=1}^{2d}(−𝔦x)^i\,B_i(c_m)`,
> a degree-`≤2d` polynomial in the frequency with **archimedean (Hermite) coefficients** `B_i(c_m)`.
This feeds Wheeler's shared target `\sup_{t,\,m}|D_d(c_m;t)| < \min_m|C_d(c_m)|` exactly, at the evaluation
points he needs.

**Divergence at `σ=½` (rigorous).** The deformation has **no absolute and no `L²` bound** at the critical
line: the `k=1` prime amplitudes are `|K_d(c_m;p,1)| = p^{−1/2}|Q(\log p;c_m)| ≍ p^{−1/2}(\log p)^{≤2d}`, and
for every `a ≥ 0`,
`Σ_p p^{−1/2}(\log p)^a = ∞` and `Σ_p p^{−1}(\log p)^a = ∞`
(prime density `1/\log x`: `∫ x^{−1/2}(\log x)^{a−1}dx` and `∫ x^{−1}(\log x)^{a−1}dx` both diverge). Hence
`D_d(c_m;t)` exists only as a **regularized / conditionally-convergent** Bohr sum (explicit formula), and
`\sup_t|D_d(c_m;t)|` is an intrinsic **cancellation / large-values** quantity — never a triangle-inequality
or a variance bound. This is the no-margin (#89–91) **at the value level**, and it matches Wheeler's "`σ=½`
deep in the non-reducible zone": the coboundary `L²` (abscissa `¾`) already diverges at `½`, so only the
single-orbit sign survives.

**Door-2 refinement (honest).** The divergence proves the target is **not** a parent triangle/`L²` bound —
control must come from **phase cancellation on the joint orbit `{t\log p}`**. The precise Door-2 dividing
line for the shared target: is that cancellation a parent large-values estimate (Halász / Montgomery ⟹
**BRIDGE**), or does it genuinely need the **support-`≤2d` near-resonance** (Baker / integer-gap ⟹
**native**)? The native candidate is a uniform-in-`d` bound that no phase-blind method gives because the
`(\log p)^{≤2d}` amplitude growth is beaten only by the arithmetic spacing of `{Σ_p a_p\log p}` (DeWitt's
lane). **This is the exact point where C5 is won or graded BRIDGE.**

## §7 The magnitude route is unsatisfiable (log-ζ large values)
Both magnitude sufficient conditions — Wheeler's value-form `sup_t|D_d(c_m;t)| < min_m|C_d(c_m)|` and the
matrix `sup_t ρ_d(t) < 1` — are **not satisfiable for any `d`**: the deformation inherits `\log ζ(½+𝔦·)`
large values, unbounded in `t` (Selberg CLT; Bondarenko–Seip Ω), and Pólya–LP needs all `t∈ℝ`. So the live
target is **sign-correlation** (`λ_min(S_d(t)) ≥ −1`), not magnitude domination. (Detail in chat 64.)

## §8 `δH_d` is indefinite; the `S_d` criterion is Hermite-tautological — 2026-06-19
A rigorous check (using the kernel) of Wheeler's PSD-resonance conjecture (`finite-free` §"decoupling"):
- **`δH_d(t)` is generically indefinite.** `H_d(t)=V(t)V(t)^⊤` (Gram of the section's roots),
  `A_d=V_arch V_arch^⊤`, so `δH_d = V(t)V(t)^⊤ − V_arch V_arch^⊤` is a **difference of PSD Grams**. "δH_d ⪰ 0"
  needs Loewner domination, generally false. First order via the kernel:
  `Σ_{ij}v_iv_j\,δ\!P̃_{i+j} = Σ_l ε_l(t)\,·2V(r_l)V'(r_l)` (since `Σ_{ij}v_iv_j(i{+}j)r^{i+j-1}=2VV'`) —
  indefinite (the `VV'(r_l)` carry both signs), even for outward root motion. **So the resonance spike is
  not positive-direction; the PSD-resonance mechanism is unsupported.**
- **The criterion is tautological.** `H_d(t)⪰0 ⟺ all section roots real ⟺ hyperbolic` is exactly Hermite's
  theorem (structural lemma (i)). So `λ_min(S_d)≥−1` *restates* hyperbolicity; the empirical `λ_min(I+S)≥0`
  (`d≤7,t≤60`) only confirms the low sections are hyperbolic (RH holds in range), not a mechanism. The
  `A_d+δH_d` split is a **reformulation, not a reduction** — consistent with the validation (finite-free
  positivity = dBN/Hermite, no new mechanism).
- **What survives:** Wheeler's *decoupling insight* — RH-bearing collisions are at small-`|ζ|`/near-zero
  (local-spacing) events, not at large-`|ζ|` resonances. The live target is the **quantitative near-zero
  margin** (the no-margin), not a global resonance/PSD bound.

## Gates
- [x] 0 → 1  in-progress: kernel posed.
- [x] 1 → 2  fully-proven: the first-order kernel formula derived (§2) from Pólya–LP + explicit formula +
  simple-node perturbation; structure (§3) and the C5-crux hand-off (§4) recorded. BRIDGE.
- [ ] 2 → 3  formalized — Lean anchor **DONE** for the arithmetic coefficient:
  `logZetaPrimeCoeff_prime` and `logZetaPrimeCoeff_primePower` in
  `formal/GaloisForLFunctions/C5JensenPrimeKernel.lean` prove
  `Λ(p)/log(p)·p^{-1/2}=p^{-1/2}` and `Λ(p^k)/log(p^k)·(p^k)^{-1/2}=p^{-k/2}/k`.
  Remaining targets: the Leibniz first-order expansion, the `B_i` definition, and the explicit-formula /
  Jensen-section regularization infrastructure.
- [ ] 3 → 4  publication-ready.

## Notes / risk
- **First-order only:** valid while `|ε_l|` < node gap (the pre-collision regime) — exactly the regime the
  collision question probes; the collision itself is the boundary where higher order enters (flagged).
- **Regularization:** `P` and `P^{(i)}` on the real axis are explicit-formula (distributional) sums; the
  amplitudes `c_n` are exact, the summation is regularized (standard).
- Does **not** close C5★ — it pins the kernel and converts the crux to a concrete weighted-Bohr-resonance
  inequality. The uniform-in-`d` edge bound stays open (Wheeler/DeWitt lanes).

## Cross-references
- `../1-in-progress/finite-free-convolution-flow.md` — Wheeler's carrier; this kernel is its flagged input.
- `../1-in-progress/faces-orthogonality.md` — why the `t`-orbit is the RH-bearing axis (the kernel lives there).
- `../1-in-progress/combination-mode-baker-reducibility.md` — the support-`≤ d` near-resonance lane (DeWitt).

## Log
- 2026-06-19 — Professor: derived and recorded the first-order Jensen-section prime kernel `K_d(r_l;p;t)`
  (Pólya–LP + Hadamard/explicit-formula prime part + simple-node perturbation). Confirmed `c_p=p^{−1/2}`;
  `K_d` is degree-`≤ d` in `\log p` with archimedean coefficients. Hands off the C5 crux as a concrete
  weighted-Bohr-resonance inequality (§4). BRIDGE; first-order + regularization caveats flagged. Created in
  2-fully-proven (own card, to avoid an edit race on Wheeler's carrier).
- 2026-06-19 — Professor: adapted the kernel to Wheeler's Theorem-M shared target (§6). Gave the
  critical-point value deformation `D_d(c_m;t)=Σ_{p,k}K_d(c_m;p,k)e^{−𝔦kt\log p}` (the `1/∂_X J^{arch}`
  factor drops for the value). **Proved the divergence at `σ=½`**: absolute and `L²` norms of the deformation
  are infinite (`Σ_p p^{−1/2}(\log p)^a=Σ_p p^{−1}(\log p)^a=∞`), so the target is intrinsically a
  cancellation/large-values quantity (no-margin at the value level). Refined the Door-2 line for the shared
  target: BRIDGE iff a parent large-values method (Halász/Montgomery) suffices, native iff the support-`≤2d`
  near-resonance (Baker/integer-gap) is essential — the exact win/lose point for C5.
- 2026-06-19 (Leaner) — added Lean anchor `logZetaPrimeCoeff_prime` and
  `logZetaPrimeCoeff_primePower` in `formal/GaloisForLFunctions/C5JensenPrimeKernel.lean`, formalizing
  the von-Mangoldt coefficient identities `c_p=p^{-1/2}` and `c_{p^k}=p^{-k/2}/k`. Added the module to the
  root import and axiom audit. Card remains in 2-fully-proven; the first-order Jensen kernel, `B_i`
  definition, and explicit-formula regularization are not fully formalized.
- 2026-06-19 — Professor: added §7 (magnitude route unsatisfiable, Selberg/Ω) and §8 (δH_d = difference of
  PSD Grams ⟹ indefinite; first-order `Σ_l ε_l·2VV'(r_l)`; `λ_min(S_d)≥−1` = Hermite tautology). Tested
  Wheeler's PSD-resonance conjecture → unsupported; the S_d split is a reformulation not a reduction
  (consistent with the validation). Wheeler's decoupling insight (RH crux = near-zero/small-|ζ|, not
  large-|ζ| resonance) survives. Chat 82.
- 2026-06-19 — Professor: **binding analysis of Wheeler's gap-difference condition (GD)** (chat 93). Using
  `|J'(r_l)| ~ A_l/Δ_l` and the `J'`-sign-flip: `Δε_l ~ −(Δ_l/A_l)[δJ(r_l)+δJ(r_{l+1})]`, so
  `|Δε_l|/Δ_l ~ |δJ(r_l)+δJ(r_{l+1})|/A_l` (**Δ_l cancels in the ratio**). Since `δJ(r)` is smooth, the sum
  does NOT cancel generically (≈ `2δJ(r_l)`) ⟹ ratio ≈ the value-form `|δJ|/A`, inheriting the §7
  large-values (`sup_t=∞`); it cancels ONLY for the **translation mode `δJ ∝ J'`**. **Make-or-break:** (GD)
  escapes §7 iff the prime resonance concentrates in the translation mode (`Σ_p c_p g_p(r) ∝ J'(r)` at the
  resonance `t*`) — empirically supported by Wheeler's bounded-`λ_min` probe (d≤7), mechanism open. This is
  the decisive test for whether (GD) is a live C5 candidate.

## Lean return note — 2026-06-19 (Leaner)

Returned from `2-fully-proven`: the Lean anchors prove only the von-Mangoldt coefficient identities. The ticket's kernel theorem uses Pólya-LP/Jensen-section analysis, simple-root perturbation, explicit-formula regularization on the critical line, and later large-value/PSD conclusions. Those analytic objects and regularization steps are not present as Lean theorems.
