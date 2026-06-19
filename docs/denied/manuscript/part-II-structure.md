# Multi-`q`-Difference Galois Theory for L-Functions
## Part II — Structure Theory

*Manuscript draft (publication prose). Continues Part I. Grading as before: Theorem (proved here) / Import (cited) /
Conjecture (located). The centerpiece is the complete solution of the inverse-Galois problem (§6).*

---

### 4. The flora: a census of objects

A Galois theory needs a census of its objects. We classify by rank, and the classification reveals the field's single
organizing principle: the arithmetic objects are the non-generic points.

#### 4.1 Rank one: the Picard group

A rank-one module is `M_a = K \cdot e` with `σ_p(e) = a_p e`, multipliers `a_p \in K^\times`. Integrability `(\star)`
becomes the scalar cocycle `a_p\,σ_p(a_q) = a_q\,σ_q(a_p)`, and `M_a \cong M_b` iff `b_p = a_p\,σ_p(h)/h` for some
`h \in K^\times`.

**Theorem 4.1.** Isomorphism classes of rank-one integrable modules are in bijection with the first difference
cohomology `H^1_σ(K^\times) = \{(a_p) : a_p σ_p(a_q) = a_q σ_q(a_p)\} / \{(σ_p(h)/h)\}`. Every such module has Galois
group `G_{M_a} \subseteq \mathbb{G}_m`, abelian. The group law under tensor product makes `H^1_σ(K^\times)` the
*Picard group* of the field — its Hecke characters / line bundles with connection on the prime lattice.

*Proof.* The cocycle/coboundary description is the first cohomology of the abelian group `K^\times` under the commuting
`\{σ_p\}`; rank one forces `G_{M_a} \subseteq \mathrm{Aut}(K \cdot e) = \mathbb{G}_m`. ∎ The scalar core is
machine-checked (`RankOneCohomology.lean`).

The arithmetic `L`-functions are the rank-one modules with *separated, rational, arithmetically-tied* multipliers
`a_p(x_p) = (1 - α_p x_p)/(1 - α_p x_p/p)` (`α_p` = Satake/Frobenius data). This is a thin, countable sub-locus of
`H^1_σ(K^\times)`; the generic rank-one module is non-arithmetic, and (Part IV) transcendence-easy. The organizing
principle — *arithmetic = non-generic = hard* — is already visible and is made a moduli theorem in §4.4.

#### 4.2 Rank two: five species and the first nonabelian object

Extensions of rank-one modules are classified by a twisted difference cohomology: extensions of `M_a` by `M_b` form
`\mathrm{Ext}^1_σ(M_a, M_b) = H^1_σ(K, M_{b/a})`, the analogue of Theorem 4.1 with coefficients in the rank-one module
of ratios. The unipotent case `a = b = 1` gives the field's *logarithm*: `σ_p(\ell) = \ell + c_p` with `(c_p)` an
additive cocycle, and Galois group the additive group `\mathbb{G}_a` — the first non-toral object of the field, with
`L = 0` but not semisimple.

**Theorem 4.2.** Every rank-two integrable module belongs to exactly one of five species, by the subgroup structure of
`GL_2`: split torus (decomposable), unipotent (`\mathbb{G}_a`), Borel (solvable), torus-normalizer (dihedral,
imprimitive), and irreducible-primitive. The first three are solvable with `L = 0`; the dihedral species is the
rank-two home of complex multiplication, the primitive species the home of `SL_2`-type Sato–Tate.

#### 4.3 General rank: the main structure theorem

**Theorem 4.3 (main structure theorem).** The finite-rank integrable modules form a neutral Tannakian category
`\mathcal{M}` over `ℂ`, with `\mathcal{M} \simeq \mathrm{Rep}_ℂ(\pi)` for the pro-algebraic fundamental group
`\pi = \varprojlim_M G_M`; each `G_M` is an arbitrary closed subgroup of `GL_d`. Three laws hold at every rank: the
species is the conjugacy class of `G_M \subseteq GL_d`; every linear algebraic group is realized (§6); and the
arithmetic objects occupy the tempered (`L = 0`), non-generic locus.

*Proof.* The tensor operations preserve integrability (Prop 1.2) and the fiber functor is exact, faithful, and
tensor-linear, so `\mathcal{M}` is neutral Tannakian. The three laws are the rank-`d` forms of Theorems 4.1–4.2 and §6.
∎

#### 4.4 Arithmetic is the most degenerate stratum

**Theorem 4.4.** In the moduli space `\mathrm{Mod}_d` of rank-`d` integrable modules (tangent space
`H^1_σ(\mathrm{End}\,M)`), the arithmetic locus has *infinite codimension*: at each prime the arithmetic module is a
finite Satake-parameter family inside the infinite-dimensional space of multipliers, so the arithmetic locus is a
countable union of finite-dimensional families inside an infinite-dimensional ind-scheme — of infinite codimension,
nowhere dense in the ind-Zariski topology. (We claim infinite codimension, not a measure-theoretic statement: the
infinite-dimensional moduli carries no canonical measure.)

This is the precise form of the organizing principle: arithmetic is not merely special but maximally degenerate. It
dovetails with the hypertranscendence theorem of Part IV — the same infinite-base degeneracy seen geometrically and
analytically.

---

### 5. Difference cohomology

The extension calculus of §4 is governed by a cohomology theory.

**Theorem 5.1.** For a module `M`, the difference cohomology is the group cohomology of the prime lattice,
`H^*_σ(M) = H^*(ℤ^{(P)}, M)`, computed by the Koszul complex on the operators `(σ_p - 1)`. For the directed union it is
the inverse limit `\varprojlim_S H^*(ℤ^S, M)` with vanishing `\varprojlim^1` (the restriction maps are surjective, so
the system is Mittag-Leffler). For the trivial module, `H^*_σ(K) = \widehat{\Lambda}^*(ℂ^{P})`, the completed exterior
algebra; integrability `F_{pq} = 1` is the vanishing of the `H^2` curvature class.

**Theorem 5.2 (acyclicity dichotomy).** For a rank-one module `M_a`, the full difference cohomology is `H^*(\mathbb{T}^\infty)`
if `M_a` is trivial and `0` otherwise: a single nontrivial eigenvalue makes the Koszul tensor acyclic. This
*infinite-base rigidity* — all-or-nothing cohomology — is special to the infinite base.

The additive first-Koszul differentials and the finite Euler-characteristic count are machine-checked
(`KoszulCohomology.lean`).

---

### 6. The inverse-Galois problem, completely solved

We determine exactly which linear algebraic groups occur as multi-`q`-difference Galois groups. The answer is clean,
and the route to it included a falsification of our first conjecture — recorded here in full, since the correction is
sharper than the conjecture.

#### 6.1 The finite case: groups are abelian

**Lemma 6.1 (commuting monodromy).** A finite multi-`q`-difference Galois group `G` is generated by per-prime monodromy
elements `\{g_p\}`, and these commute.

*Proof.* Finite `G` means `R_M/K` is a finite étale `G`-torsor; each `σ_p` induces a monodromy `g_p \in G(ℂ)` via the
trivialization `R_M \otimes_K R_M \cong R_M \otimes_ℂ ℂ[G]`. The `g_p` generate `G` (the torsor is connected by the
joint `\{σ_p\}`-action) and commute, because the `σ_p` commute as operators and the constants `ℂ` are fixed. ∎

**Theorem 6.2.** A finite group is a multi-`q`-difference Galois group iff it is abelian.

*Proof.* By Lemma 6.1 a finite Galois group is generated by commuting elements, hence abelian. Conversely every finite
abelian `A \cong \prod_i \mathbb{Z}/n_i` is realized: take one `\mu_{n_i}` per *distinct* prime (`σ_{p_i}(y_i) =
ζ_{n_i} y_i`, `y_i^{n_i} \in K`); the operators being independent (distinct primes, unique factorization), the Galois
group is the full product `A`. ∎

The single-operator instance of Lemma 6.1 is the classical fact that a finite `q`-difference Galois group is cyclic
(one generator); Theorem 6.2 is its `n`-generator generalization.

#### 6.2 The falsification, and the sharp invariant

Our first conjecture — that coupling adds no groups beyond the single-operator theory — is *false*. The single-operator
theory realizes only cyclic finite groups, but two independent primes realize `\mu_2 \times \mu_2`, the Klein four-group
(Theorem 6.2). Thus the infinite base genuinely *adds* groups; the correct invariant is the component group, and the
constraint is its abelianness (Lemma 6.1 applied to `G/G^\circ`).

**Theorem 6.3 (necessary condition).** If `G` is a multi-`q`-difference Galois group then its component group
`\pi_0(G) = G/G^\circ` is finite abelian (it is itself a finite multi-`q`-difference Galois group, hence abelian by
Theorem 6.2).

#### 6.3 The connected case and the gluing

**Import 6.4 (Etingof, 1995).** Every connected complex linear algebraic group is a single-`q`-difference Galois group
over `ℂ(z)`; by concentration (place the realizing system at one prime, the identity elsewhere) it is multi-`q`-realized.
(The differential analogue — every linear algebraic group — is Tretkoff–Tretkoff, 1979, via Riemann–Hilbert.)

It remains to glue a connected `G^\circ` to a finite abelian `A = \pi_0` with a possibly nontrivial action. Here a
subtlety must be respected: integrability constrains the *operators* to commute, not the Galois elements, so the
`A`-action on `G^\circ` cannot be carried by a constant operator (a naive constant intertwiner forces `G^\circ` into
the fixed subgroup) but by the *base-field Galois action* of the extension realizing `A`, which conjugates connections.

**Theorem 6.5 (induction with duality).** For any connected `G^\circ`, torus `T`, and finite abelian `A`, the groups
`G^\circ \times A` and `T \rtimes A` and the outer-twisted extensions are all realized. The `A`-action — permutation of
characters for `T \rtimes A`, dualization for the diagram automorphisms, triality by a `\mu_3`-extension — is
implemented by inducing a rank-one module over the difference field extension `K'/K` with `\mathrm{Gal}(K'/K) = A`; the
twist is carried by `\sigma`'s action on `K'`, which is integrable by construction.

#### 6.4 The classification

**Theorem 6.6 (inverse-Galois classification).** A linear algebraic group `G` over `ℂ` occurs as a
multi-`q`-difference Galois group if and only if its component group `\pi_0(G)` is finite abelian.

*Proof.* Necessity is Theorem 6.3. Sufficiency: realize `G^\circ` by Import 6.4, `A = \pi_0(G)` by Theorem 6.2, and the
extension `1 \to G^\circ \to G \to A \to 1` by induction-with-twist (Theorem 6.5). ∎

The defining question of the Galois theory is thus completely answered: *the realizable groups are exactly those with
finite abelian component group.* The connected part is unconstrained; the only obstruction is the commuting-monodromy
abelianness of the components. The infinite base contributes precisely a `\widehat{\mathbb{Z}}`-worth of independent
cyclic component-generators, one per prime — a clean, true statement, and a *strictly more informative* one than the
false "coupling adds nothing" we began with.

---

*End of Part II. The development corrected its own course twice here — the falsification of the coupling conjecture
(§6.2) and the operator-versus-Galois subtlety (§6.3) — and both corrections sharpened the result. Part III (the
dynamical realization: weight filtrations as Oseledets filtrations, Lyapunov exponents, the difference Morales–Ramis
correspondence) follows. The research draft `multi-q-difference-galois-foundations.md` §17–60 carries every proof and
the full grading.*
