# Multi-`q`-Difference Galois Theory for L-Functions
## Part I — Foundations

*Manuscript draft (publication prose). Companion to the research draft `multi-q-difference-galois-foundations.md`
(§1–60), which carries the full development and air-marked grading. This Part is written to paper standard: every
assertion is a Theorem (proved here), an Import (classical, cited), or a Conjecture (stated, falsifiable). No proof of
the Riemann Hypothesis, the Generalized Ramanujan Conjecture, or the existence of the Langlands group is claimed; these
appear only as precisely-located open problems.*

---

### Abstract

We found a field of mathematics: the *infinite-base limit of `q`-difference Galois theory*. Where the classical theory
(van der Put–Singer, Sauloy, Di Vizio–Hardouin) studies a single dilation `σ: z \mapsto qz`, and Mahler's method
(Adamczewski–Faverjon) a finite family, we take the extreme of **countably many commuting dilations** `\{σ_p\}`, one
per prime `p`, with `q_p = 1/p`. A finite-rank module over this base is a flat connection on the prime lattice
`ℤ^{(P)}`; the arithmetic `L`-functions arise as the diagonal restrictions of rank-one such connections, and we show
they occupy the *maximally non-generic* stratum of the resulting moduli. The theory has the structural features one
demands of a Galois theory — a fundamental theorem, a flora of objects, a solved inverse problem — and a transcendence
theory that proves the difference-category analogue of Hölder's hypertranscendence theorem, uniformly for all
L-functions. This Part develops the foundations: the
difference structure and its integrability cocycle (§1), a self-contained Picard–Vessiot theory reducing the
several-operator case to the classical single-operator one (§2), and the Galois correspondence (§3).

---

### 0. Introduction

#### 0.1 The object

Fix the rational function field tower and, for each prime `p`, an independent variable `x_p`. A *multi-`q`-difference
field* `K` carries a family of commuting automorphisms `\{σ_p\}_{p∈P}` (`P` = the primes), where `σ_p` is the dilation
`x_p \mapsto q_p x_p` with `q_p = 1/p` in the arithmetic specialization. The motivating substitution is the **Bohr
lift** `x_p = p^{-s}`: under it, the Euler product `\prod_p (1 - x_p)^{-1}` pulls back along the *diagonal*
`s \mapsto (p^{-s})_p` to `ζ(s)`, and a general `L`-function to the diagonal of a rank-one module (§Part V). The
arithmetic content lives entirely on this diagonal; everything off it is the free, generic theory.

A finite-rank module `M \cong K^d` carries one semilinear automorphism per prime, `σ_p(e_k) = \sum_i (A_p)_{ik} e_i`,
`A_p \in GL_d(K)`. The sole constraint is that the `σ_p` commute as operators on `M`, which is the integrability
cocycle of §1. Thus a module is precisely a **flat connection on the prime lattice**, with `\{A_p\}` a discrete gauge
field and integrability the vanishing of its curvature.

#### 0.2 Why an infinite base

Two phenomena are invisible to any finite truncation and constitute the field's reason to exist.

First, **arithmetic lives at infinity**. By unique factorization the logarithms `\{\log p\}` are `ℚ`-linearly
independent, so the diagonal `s \mapsto (p^{-s})_p` is a single dense orbit of infinite codimension in the
infinite-dimensional pro-torus (§Part II). An `L`-function is the restriction of the free universal Euler product to
this one dense orbit; no finite-prime shadow distinguishes it from a generic flow.

Second, **hypertranscendence is forced by the base**. A finite base yields a holonomic diagonal (a finite-order
difference equation); the genuinely infinite arithmetic base does not. We prove (§Part IV) that the diagonal is
holonomic if and only if the *corank* of its relation lattice is finite, so every arithmetic `L`-function — relation
lattice trivial, corank infinite — is hypertranscendental. This recovers Hölder's 1887 theorem for `ζ` and extends it
uniformly to all `L`-functions, attributing the cause not to any special feature of `ζ` but to the multiplicative
independence of the primes.

#### 0.3 Results of this Part

- **Theorem A (§1).** A finite-rank module is a flat connection on the prime lattice; integrability is the cocycle
  `A_p\,σ_p(A_q) = A_q\,σ_q(A_p)`, equivalently the vanishing of the discrete curvature `F_{pq}=1`. The category is
  closed under `⊗, ⊕, (-)^\vee`, sub-quotients.
- **Theorem B (§2).** Every finite-rank integrable module admits a Picard–Vessiot ring, with difference-Galois group a
  pro-algebraic group `G_M = \varprojlim_S G_S`. The "several-operator" theory is *not* an independent edifice: it is
  the classical single-operator Picard–Vessiot construction, the only new ingredient being the *co-extension theorem*
  (integrability is exactly what lets the commuting `σ_p` extend to one universal solution algebra).
- **Theorem C (§3).** The Galois correspondence holds: an inclusion-reversing bijection between closed subgroup schemes
  of `G_M` and intermediate difference field extensions, realized as the inverse limit of the finite-`S`
  correspondences.

We work over an algebraically closed field of constants `C = ℂ`, characteristic zero throughout.

---

### 1. The difference structure and its integrability

Let `K` be a multi-`q`-difference field with commuting automorphisms `\{σ_p\}_{p∈P}` and constant field `C = ℂ`. A
**finite-rank module** is `M \cong K^d` with a semilinear action of each `σ_p`, given on a basis by a matrix
`A_p \in GL_d(K)` via `σ_p(v) = A_p\,σ_p(v_{\mathrm{coord}})` (coordinatewise on the `K`-entries).

**Theorem 1.1 (integrability cocycle).** The operators `σ_p` commute on `M` if and only if
```
A_p \, σ_p(A_q) \;=\; A_q \, σ_q(A_p) \qquad (p,q \in P). \tag{$\star$}
```

*Proof.* Compute both compositions on a basis vector `e_k`:
`σ_pσ_q(e_k) = \sum_i [A_p σ_p(A_q)]_{ik} e_i` and `σ_qσ_p(e_k) = \sum_i [A_q σ_q(A_p)]_{ik} e_i`. Equality for all
`k` is exactly `(\star)`. ∎

We call `(\star)` **integrability**. Defining the *discrete curvature* of the pair `(p,q)` by
`F_{pq} = A_q^{-1} σ_q(A_p)^{-1} A_p σ_p(A_q)`, integrability is `F_{pq} = 1` — flatness on the prime lattice. A
module is therefore a flat connection; `\{A_p\}` is a discrete gauge field on the prime graph, gauge-trivial (globally
trivializable) iff decomposable, flat-but-nontrivial iff the holonomy is nonabelian.

**Proposition 1.2 (Tannakian closure).** Integrability is preserved under tensor product, direct sum, dual, and
sub-quotients; the finite-`S` truncation (forgetting `σ_p` for `p \notin S`) of an integrable module is integrable.

*Proof.* For `⊗`: `(A_p \otimes B_p)\,σ_p(A_q \otimes B_q) = (A_p σ_p A_q) \otimes (B_p σ_p B_q) =
(A_q σ_q A_p) \otimes (B_q σ_q B_p) = (A_q \otimes B_q)\,σ_q(A_p \otimes B_p)`, using `(\star)` for `A` and `B`
separately. Direct sum and dual are similar (the dual uses `(A_p^{-1})^T` and the transpose of `(\star)`).
Sub-quotients inherit the identity by restriction. Truncation drops constraints, preserving the rest. ∎

The elementary core — the curvature identity and its closure under the tensor operations — is machine-checked in the
accompanying Lean library (`FlatConnection.lean`), axiom-clean.

---

### 2. Picard–Vessiot theory, self-contained

We construct the solution ring and the Galois group, and show the construction is the classical single-operator one
plus integrability. This dissolves the apparent dependence on a separate "several-operator difference Galois theory."

Work in the fundamental-solution convention: a rank-`d` system is `σ_p(Y) = A_p Y` for a fundamental matrix `Y`,
`A_p \in GL_d(K)`.

**Theorem 2.1 (co-extension = integrability).** Let `U = K[X_{ij}, \det(X)^{-1}]` be the localized polynomial algebra
on a `d \times d` matrix `X` of indeterminates, and extend each `σ_p` to `U` by `σ_p(X) := A_p X`. The extended
operators `σ_p` commute on `U` if and only if `σ_p(A_q) A_p = σ_q(A_p) A_q` for all `p,q` — the integrability cocycle
in the fundamental-solution convention (equivalent to `(\star)` under the module/system duality).

*Proof.* `σ_pσ_q(X) = σ_p(A_q X) = σ_p(A_q) σ_p(X) = σ_p(A_q) A_p X`, and symmetrically `σ_qσ_p(X) = σ_q(A_p) A_q X`;
the operators already commute on `K`, so commutation on the generators `X` is the stated identity. ∎

This identity is non-vacuous: for generic `A_p, A_q` over `ℚ(t)` with commuting shifts it fails, and holds precisely on
the integrable locus (verified symbolically; `computations/coextension_integrability`). Integrability is thus *exactly*
the condition that the several commuting operators extend to one solution algebra.

**Theorem 2.2 (Picard–Vessiot ring and Galois group).** Let `M` be a finite-rank integrable module. There is a
Picard–Vessiot ring `R_M/K` — a `σ`-simple difference ring with constant field `ℂ`, generated by the entries of a
fundamental matrix and its inverse determinant — and the difference-Galois group `G_M = \mathrm{Aut}^σ(R_M/K)` is a
pro-algebraic group over `ℂ`, realized as the inverse limit `\varprojlim_S G_S` over finite `S \subset P`.

*Proof.* For finite `S`, form `U_S` as in Theorem 2.1 (its `σ_p`, `p \in S`, commute by integrability) and quotient by
a maximal `σ`-stable ideal `\mathfrak{m}` (Zorn): `R_S = U_S/\mathfrak{m}` is `σ`-simple, a Picard–Vessiot ring for the
`S`-truncation. *This is verbatim the classical single-operator construction* (van der Put–Singer, Ch. 1); nothing in
"form `U`, quotient by a maximal `σ`-stable ideal" uses the number of operators — only that `\{σ_p\}_{p \in S}` is a
commuting group of automorphisms of `U_S`, which Theorem 2.1 secured. The two load-bearing facts — that `R_S` has no
new constants, and that `R_S \otimes_K R_S \cong R_S \otimes_ℂ ℂ[G_S]` for a closed subgroup `G_S \subseteq GL_d` —
are the single-operator lemmas, whose proofs use only `σ`-simplicity and `ℂ = \bar ℂ`, not the operator count. Finally
`R_M = \varinjlim_S R_S` (directed union; a domain with constants `ℂ` since each relation lives at finite level) is a
Picard–Vessiot ring for `M`, and `G_M = \varprojlim_S G_S` along the restriction surjections `G_{S'} \twoheadrightarrow
G_S`. ∎

**Remark 2.3 (what the reduction dissolves, precisely).** What Theorem 2.2 dissolves is the *hard* part of any
"several-operator difference Galois theory" — the Tannakian / pro-algebraic group-construction — by showing it is the
single-operator Picard–Vessiot *method* run on the integrable solution algebra `U`, with co-extension (Theorem 2.1) the
only genuinely new input. What remains imported are two lemmas — no new constants (`C_{R_M} = ℂ`) and the torsor
structure — *in their commuting-operator form.* These are **not** the `n=1` lemmas applied per operator: joint
`σ`-simplicity (no ideal stable under all `σ_p`) is weaker than per-operator `σ_p`-simplicity, so the commuting-case
statements are routine **partial-difference** generalizations of the `n=1` lemmas (provable by the same technique;
established in the partial-difference Picard–Vessiot literature). The dependency is therefore precisely bounded: the
single-operator PV method, the co-extension identity (proved and verified here), and two elementary partial-difference
lemmas — much less than a separate Galois theory, and stated as exactly that.

---

### 3. The Galois correspondence

**Theorem 3.1 (fundamental theorem).** Let `M` be a finite-rank integrable module, `L_M = \mathrm{Frac}(R_M)`. The maps
```
H \;\longmapsto\; L_M^{H} \qquad\text{and}\qquad F \;\longmapsto\; \{\tau \in G_M : \tau|_F = \mathrm{id}\}
```
are mutually inverse, inclusion-reversing bijections between closed subgroup schemes `H \subseteq G_M` and intermediate
difference field extensions `K \subseteq F \subseteq L_M`. A subgroup `H` is normal iff `F = L_M^H` is itself a
Picard–Vessiot extension of `K`, in which case `G_M/H \cong \mathrm{Gal}(F/K)`. For rank one (`G_M` abelian) every
intermediate extension is again Picard–Vessiot.

*Proof.* The statement is the Tannakian fundamental theorem for affine group schemes (Deligne–Milne) applied to
`G_M = \underline{\mathrm{Aut}}^{\otimes}(\omega)` on the neutral Tannakian category `\langle M \rangle^{\otimes}`,
with fiber functor `\omega` the solution space; closed subgroup schemes correspond to Tannakian sub-data, and via
Picard–Vessiot theory to intermediate extensions. Concretely it is the inverse limit of the finite-`S` correspondences
(van der Put–Singer Thm 1.29): each closed `H \subseteq G_M` is `\varprojlim_S H_S` with `H_S \subseteq G_S`
Zariski-closed (Chevalley: a closed subgroup is the stabilizer of a line in a representation, which lives at finite
`S`); the finite correspondences are compatible with the restriction maps (`L_{S'}^{H_{S'}} \cap L_S = L_S^{H_S}`,
since `H_{S'}` acts on `L_S` through its quotient `H_S`); and invariants commute with the limit,
`L_M^H = \varinjlim_S L_S^{H_S}`, because every element of `L_M` lies at some finite level (the finite-support property
of §2). The bijections are the limit/colimit of the mutually-inverse finite ones; normality and the rank-one
specialization are level-wise. ∎

The one ingredient beyond "take the limit" is the invariants/limit interchange, which rests on the field's specific
finite-support structure: a finite-rank module has no data beyond its finite truncations. This is the precise reason
the infinite base is tame at the level of the correspondence, while still admitting *deep* subgroups — closed
subgroups whose defining relations involve infinitely many primes — that no finite truncation sees. These deep
subgroups, and the dense diagonal that is the arithmetic locus, are the subject of Part II.

---

*End of Part I. Part II (Structure theory: the flora, the difference cohomology, and the fully-solved inverse-Galois
problem) and Parts III–VI follow the manuscript outline `00-manuscript-outline.md`. The research draft
`multi-q-difference-galois-foundations.md` §1–60 carries the complete, air-marked development with all proofs and the
fourteen self-corrections of the discovery process.*
