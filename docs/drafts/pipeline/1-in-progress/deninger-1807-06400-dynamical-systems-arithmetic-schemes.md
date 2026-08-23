# Deninger, *Dynamical systems for arithmetic schemes* (arXiv:1807.06400v4) — full Lean formalization

- **ID:** deninger-1807-06400
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean)
- **Source:** arXiv:1807.06400v4 (Feb 2024), C. Deninger, math.DS/math.AG
- **Statement:** Formalize unconditionally in Lean 4 every lemma / proposition / theorem of the
  paper whose content is not already owned by mathlib or by this corpus.

## Goal
Bring the whole "rational Witt space" programme (sheafified rational Witt vectors, the
`Q^{>0}`-spaces `\check X(C)`, the `R^{>0}`-dynamical systems, the `p`-adic subsystem `\hat Y`,
and the relation to the Fargues–Fontaine curve) into the corpus as closed Lean theorems.

## Paper inventory (78 numbered results, 15 sections)
| § | results | notes |
|---|---|---|
| 1 Rational Witt vectors | Prop 1.1–1.3, Thm 1.4, Cor 1.5, Lem 1.6, Cor 1.7, Thm 1.8 | corpus already owns large parts of 1.1/1.2/Fatou |
| 2 Rational Witt spaces | Prop 2.1, Def 2.2/2.3/2.5, Prop 2.4 | scheme/ringed-space layer |
| 3 C-valued points | Cor 3.1–3.3, Prop 3.4, Def 3.5, Prop 3.6, Cor 3.7 | |
| 4 Character classes | Def 4.1, Prop 4.2, Lem 4.3, Cor 4.4, Prop 4.5, Lem 4.6 | 4.3 and 4.6 are pure algebra |
| 5 Q^{>0}-orbits | Prop 5.1, Thm 5.2, Lem 5.3, Thm 5.4 | |
| 6 R^{>0}-system | Thm 6.1 | |
| 7 Topology | Lem 7.1–7.3, Prop 7.4–7.7, Cor 7.8/7.9, Thm 7.10 | 7.7 pure metric geometry |
| 8 Closure of periodic orbits | Claim 8.1 (conjectural), Thm 8.2, Lem 8.3 | Thm 8.2 conditional on Claim 8.1 in dim ≥ 2 |
| 9 Connectedness | Prop 9.1, Thm 9.2/9.3, Lem 9.4, Def 9.5, Thm 9.6, Cor 9.7, Thm 9.8 | needs de Jong alterations |
| 10 Leafwise H^0 | Def 10.1, Thm 10.2, Prop 10.3 | 10.3 adelic irreducibility |
| 11 Generalized functions | Lem 11.1/11.2, Def 11.3/11.4, Prop 11.5–11.7 | |
| 12 Invertible functions | Prop 12.1 | |
| 13 o-valued points | Prop 13.1, Def 13.2, Thm 13.3, Prop 13.4, Cor 13.5, Def 13.6, Supple 13.7, Prop 13.8/13.9, Thm 13.10, Cor 13.11/13.12 | |
| 14 A_inf rings | Def 14.1/14.2, Prop 14.3/14.4, Def 14.5, Prop 14.6, Prop 14.7, Def 14.8, Supple 14.9, Prop 14.10, Def 14.11, Prop 14.12–14.15 | 14.7/14.13/14.14 pure algebra |
| 15 Fargues–Fontaine | Thm 15.1, Prop 15.2, Thm 15.3, Cor 15.4, Thm 15.5, Prop 15.6/15.7 | |

## Ledger (Lean modules landed)

| Paper result | Lean module | Status |
|---|---|---|
| Thm 1.8 (`t29`) `V_N(W) ∩ W_rat = V_N(W_rat)` | `RHTower/DeningerDynSysVerschiebungRational.lean` | closed (Fatou hypothesis removed: holds over every commutative ring) |
| Prop 1.2(a) (`t21n`) finite-orbit Galois descent | `RHTower/DeningerDynSysWittGaloisFiniteOrbits.lean` | closed |
| Lemma 4.6 (`t46n`) `N`-th roots of pointed multiplicative maps, incl. the value of `N'` | `RHTower/DeningerDynSysPointedMultiplicativeRoot.lean` | closed |
| Lemma 5.3 (`t5`) Frobenius-twist quotient | `RHTower/DeningerDynSysFrobeniusTwistQuotient.lean` | closed |
| Prop 7.7 (`t87`) compact-orbit quotient metric | `HTGeometry/CompactOrbitQuotientMetric.lean` | closed |
| **Prop 7.6 (`t86`)** a `G`-invariant metric inducing the topology on the character points of an affine scheme, and second countability/separability | `RHTower/DeningerDynSysAffineMetric.lean` | closed |
| §7 the block-weighted metric on a product with countably many finite blocks, its weights, and transport along an inducing map | `HTGeometry/BlockProductMetric.lean` | closed |
| **Cor 7.8 (`t88`)** the quotient distance on `X̂₀(C) = X̂(C)/G`: `δ ≤ d`, orbit-constant, vanishing exactly on an orbit, and inducing the quotient topology | `RHTower/DeningerDynSysAffineMetric.lean` | closed |
| **Prop 7.4(b) (`t10`)** the inductive limit topology on `X̌(C)` and the Frobenius operators as homeomorphisms of it | `RHTower/DeningerDynSysColimitTopology.lean` | closed |
| **Prop 4.5 (`t44n`)** a morphism of schemes carries the character points in a functorial admissible class into the character points in that class — §4 is now closed in full | `RHTower/DeningerDynSysFunctorialClass.lean` | closed |
| **Lemma 7.3 (`t9`), equation (21)**: `F_ν(X̂(C))` is exactly the set of character points whose character kills `μ_ν` of the residue field, via the surjectivity of the `ν`-th power map on the units of an algebraically closed field | `RHTower/DeningerDynSysFrobeniusRange.lean` | closed |
| **Lemma 7.3 (`t9`), the clopen assertion**: `F_ν(X̂(C))` is open and closed, by the finite partition of each affine trace under restriction to `μ_ν(Γ(X,U))` | `RHTower/DeningerDynSysFrobeniusClopen.lean` | closed |
| **Prop 7.4(a) (`t10`)**: `X̂(C)` is an open and closed subspace of `X̌(C)` | `RHTower/DeningerDynSysFrobeniusClopen.lean` | closed |
| **Lemma 7.3 (`t9`) CLOSED IN FULL**: `F_ν` is continuous, an open map and a closed map — under `ν`-divisibility of the sections it is inducing on each affine trace, hence an open and a closed embedding | `RHTower/DeningerDynSysFrobeniusOpenMap.lean` | closed |
| **Lemma 7.3 (`t9`), the `G`-part, and Prop 7.4(c) (`t10`)**: an isomorphism of schemes induces a homeomorphism of `X̂(C)` and of `X̌(C)` — so a group acting by scheme automorphisms acts by homeomorphisms | `RHTower/DeningerDynSysCharacterAutomorphism.lean` | closed |
| **Cor 7.9 (`t89n`), main step**: a character point over an affine open is determined by its evaluations, so the affine traces are Hausdorff and `X̂(C)` is Hausdorff whenever any two points of `X` lie in a common affine open | `RHTower/DeningerDynSysCharacterSeparated.lean` | closed |
| **Cor 7.9 (`t89n`) for `X̌(C)`**: the canonical map `X̂(C) → X̌(C)` is an open embedding, every pair of points of `X̌(C)` is carried into its image by one Frobenius homeomorphism, so `X̌(C)` is Hausdorff whenever `X̂(C)` is | `RHTower/DeningerDynSysColimitSeparated.lean` | closed |
| **Cor 7.9 (`t89n`) for the quotients `X̂₀(C)` and `X̌₀(C)`**, on top of a new mathlib gap: a compact group acting continuously on a Hausdorff space has Hausdorff orbit space | `HTGeometry/CompactGroupOrbitQuotientT2.lean`, `RHTower/DeningerDynSysColimitSeparated.lean` | closed |
| **Prop 7.5 (`t85`) for an arbitrary scheme**: the locality step (continuity of an action map is local on an open cover) and the affine step (open stabilisers on the sections make each coordinate locally constant in the group variable) | `RHTower/DeningerDynSysCharacterActionContinuous.lean` | closed |
| **Supple 14.9 (`t106`)**: the diagram attached to a triple is unique — `P̂` because the comparison map from the perfection of the ring has dense image (Prop 14.7(a)) and `P̂` is continuous, `P̃` because it is prescribed on a surjection | `RHTower/DeningerDynSysPerfectionUnique.lean` | closed |
| **Prop 13.4 (`t44`)**: all three descriptions of the `𝒪`-valued points agree — the character triple `(x,y,P^×)` of Def 13.2, the map `P_y : 𝒪_{X,y} → 𝒪` with 1),2),3), and the map `P'_y : 𝒪_{closure{x},y} → 𝒪` with 1'),3'); as two `Equiv`s | `RHTower/DeningerDynSysValuedLocalTriple.lean`, `RHTower/DeningerDynSysValuedCharEquiv.lean` | closed |
| **§13 input**: `κ(x) = Frac(𝒪_{closure{x},y})` for `y ∈ closure{x}`, via the stalk at a generization being a localization of the stalk at the specialization | `HTGeometry/SchemeStalkSpecializationRatio.lean`, `RHTower/DeningerDynSysClosureFractionField.lean` | closed |
| **mathlib gap**: a pointed multiplicative map between domains, injective off `0`, extends uniquely to the fraction fields | `HTGeometry/FractionFieldMultiplicativeExtension.lean` | closed |
| **Cor 13.5 (`t45`), the factorization of b) and the pair of points**: `Q mod 𝔪` factors through `R/Q⁻¹(𝔪)`, and `Q⁻¹(𝔪)` lies in the closure of `Q⁻¹(0)` in `Spec R`, i.e. `y ∈ closure {x}` | `RHTower/DeningerDynSysValuedPointsFactorization.lean` | closed |
| **Prop 14.13 (`t1110`), equations (120n) and (121n)**: `W_p(χ) = θ ∘ W_p(χ♭)` and on a Teichmüller representative it is the untilt, `W_p(χ)([x]) = (χ♭ x)^♯` — Deninger's `χ = ♯ ∘ χ♭` | `RHTower/DeningerDynSysFontaineTheta.lean` | closed |
| **Prop 14.13 (`t1110`), injectivity of `lim_{()^p} A → A♭`** for a `p`-adically separated ring, via `p ∣ a − b ⟹ p^{k+1} ∣ a^{p^k} − b^{p^k}` | `RHTower/DeningerDynSysTiltInjective.lean` | closed |
| **Prop 14.13 (`t1110`), the tilting identification `lim_{()^p} A ≅ A♭`** for a `p`-adically complete ring, as a multiplicative equivalence | `RHTower/DeningerDynSysTiltSurjective.lean` | closed |
| **Prop 14.13 (`t1110`), the correspondence `χ = ♯ ∘ χ♭` and its injectivity**: a homomorphism of tilts is determined by the pointed multiplicative map it induces on `lim_{()^p} A` | `RHTower/DeningerDynSysTiltCorrespondence.lean` | closed |
| **Prop 14.13 (`t1110`), the full correspondence**: a pointed multiplicative map `A♭ → 𝒪` comes from a homomorphism of tilts *iff* its reduction mod `p` is additive, and then from a unique one — both on `A♭` and on `lim_{()^p} A` | `RHTower/DeningerDynSysTiltCorrespondence.lean` | closed |
| **§7 the topology on `X̂(C)` for an arbitrary scheme** (the supremum of the topologies coinduced by the traces over the affine opens), **Lemma 7.1 (`t7`)** and the Frobenius half of **Lemma 7.3 (`t9`)** in that generality, and **Lemma 7.2 (`t8`)** in full: the trace over an affine open is an **open embedding**, via the localisation step over a basic open subset | `RHTower/DeningerDynSysCharacterTopology.lean` | closed |
| Prop 1.2(b) (`t21n`) field case of Galois descent | `RHTower/DeningerDynSysWittGaloisField.lean` | closed |
| **Prop 1.2(b) (`t21n`) integrally closed domain case** — Prop 1.2 is now closed in full | `RHTower/DeningerDynSysWittGaloisIntegrallyClosed.lean` | closed |
| Prop 14.7(c) (`t125`) perfection surjects along a quotient | `RHTower/DeningerDynSysPerfectionLocal.lean` | closed |
| Prop 14.14(2) (`t1213`) locality of the tilt | `RHTower/DeningerDynSysPerfectionLocal.lean` | closed |

| Thm 1.4 (`t27n`) = Kucharczyk–Scholze Lemma 4.9 | `RHTower/DeningerDynSysInvariantPoints.lean` | closed |
| Lemma 1.6(2) (`t212n`), Cor 1.7(1) (`t213n`) | `RHTower/DeningerDynSysValuedPoints.lean` | closed |
| §1 `Hom(ℤ̲A, R) ≅ (A →*₀ R)` | `RHTower/DeningerDynSysReducedMonoidAlgebra.lean` | closed |
| Def 9.5 (`t95n`) + its two stated facts | `HTGeometry/AlmostPathConnected.lean` | closed |
| **Lemma 9.4 (`t13`)** injective characters of a countable `ℚ`-vector space are almost path-connected in `Hom(V, ℂˣ)` | `HTGeometry/RationalCharacterPath.lean` | closed |
| §9 the exponential approximation: every character of a countable `ℚ`-vector space is pointwise-approximated by `exp ∘ ψ` with `ψ` linear, injective and avoiding `ℚ·2πi` | `HTGeometry/RationalCharacterApproximation.lean` | closed |
| Thm 1.4 second assertion (`t27n`) for `ℤ A`, incl. the `(!)` finite-orbit step | `RHTower/DeningerDynSysMonoidRingAction.lean` | closed |
| Thm 1.4 second assertion (`t27n`) for the actual `W_rat (A)` | `RHTower/DeningerDynSysWittRingAction.lean` | closed |
| Prop 1.2(a) (`t21n`) for the actual `W_rat (A)`: `W_rat(A)^G = W_rat(A^G)` | `RHTower/DeningerDynSysWittRingDescent.lean` | closed |
| §1 inseparability degree `d_r`, `d_{rs} ∣ d_r d_s`, the subring `ℤ̲κ/κ₀` | `RHTower/DeningerDynSysInseparableDegree.lean` | closed |
| Cor 1.5(2) (`t28n`) key vanishing on inseparable atoms in characteristic `p` | `RHTower/DeningerDynSysInseparableVanishing.lean` | closed |
| Prop 14.14(1) (`t1213`) locality of the adic completion, `p`-adic case, residue fields | `RHTower/DeningerDynSysAdicLocal.lean` | closed |
| Lemma 4.3 (`t3`) structural half: divisibility of `Cˣ`, the extension property, the `μ(C)` retraction | `RHTower/DeningerDynSysDivisibleExtension.lean` | closed |
| Lemma 4.3 (`t3`) vector-space layer: `(k^×/μ(k)) ⊗ ℚ`, the independence criterion, `rank ≤ #k`, `#C ≤ #(C^×/μ(C))` | `RHTower/DeningerDynSysUnitClassSpace.lean` | closed |
| Lemma 4.3 (`t3`) dimension input: `#C ≤ dim_ℚ (C^×/μ(C))`, both characteristics; Euclid for monic irreducible polynomials | `RHTower/DeningerDynSysMultiplicativeRank.lean` | closed |
| **Lemma 4.3 (`t3`)** itself, for an arbitrary field `k`, plus the injective-character assertion in equal characteristic | `RHTower/DeningerDynSysCharacterExtension.lean` | closed |
| Lemma 4.3 (`t3`) last assertion, mixed characteristic, via `μ_{p'}(C) ≅ (𝒪/𝔪)^×`; Lemma 4.3 is now closed in full | `RHTower/DeningerDynSysRootsOfUnityReduction.lean` | closed |
| **Prop 2.1(a) (`t22n`)** both halves, the functor `W_rat : CommRingCat ⥤ CommRingCat`, and **Def 2.2/2.3 (`t23n`)** the rational Witt space | `RHTower/DeningerDynSysRationalWittPresheaf.lean` | closed |
| **Prop 2.1(b) (`t22n`)** `W_rat(𝒪_X(U)) = W_rat(𝒪_X)(U)` for a Fatou `𝒪_X(U)` on an integral scheme, as a ring isomorphism | `RHTower/DeningerDynSysWittSchemeSections.lean` | closed |
| **Prop 2.1(c) (`t22n`)** `W_rat(𝒪_X)(U) = W_rat(K) ∩ W(𝒪_X(U))` for a Fatou scheme — §2's Proposition 2.1 is now closed in full | `RHTower/DeningerDynSysWittSchemeSections.lean` | closed |
| §2 the sections of the sheafification: `W_rat(𝒪_X)(U) ≅ {locally rational big Witt vectors}` | `RHTower/DeningerDynSysWittSheafSections.lean` | closed |
| §2 the locally-rational subpresheaf of `W(𝒪_X)` and its universal property as a subsheaf | `RHTower/DeningerDynSysWittLocalSections.lean` | closed |
| Cor 1.10(2) (`t1.8`) Fatou intersection on the wrapped Witt-ring carriers | `RHTower/DeningerDynSysWittFatouCarrier.lean` | closed |
| §2 the big Witt functor, the sheaf `W(𝒪_X)`, and `W_rat(𝒪_X)` as a subpresheaf of it | `RHTower/DeningerDynSysBigWittSheaf.lean` | closed |
| §1 functoriality of `W_rat` (`map_id`, `map_comp`) | `RHTower/DeningerDynSysWittFunctoriality.lean` | closed |
| **Prop 1.3 (`t26n`) top row**: `κ^{Aut_{κ₀}κ} = κ₀^perf` and `W_rat(κ)^H = W_rat(κ₀^perf)` | `RHTower/DeningerDynSysPerfectClosureFixed.lean` | closed |
| **Prop 14.3 (`t123`)** separatedness of the `I`-adic (and `p`-adic) topology on a Noetherian local domain | `RHTower/DeningerDynSysAdicLocal.lean` | closed |
| **Prop 3.6 (`t37n`) mechanism**: a continuous character of a linearly topologized group into a group with no small subgroups has open kernel | `RHTower/DeningerDynSysNoSmallSubgroups.lean` | closed |
| **Prop 1.3 (`t26n`) polynomial correspondence**: `(minpoly F x).map = (minpoly L x)^d` over any purely inseparable `L/F`, in particular over `κ₀^perf` | `RHTower/DeningerDynSysMinpolyPurelyInseparable.lean` | closed |
| Prop 1.3 (`t26n`) normalization: reversal matches normalized with monic irreducibles; every monic irreducible is a minimal polynomial | `RHTower/DeningerDynSysNormalizedIrreducible.lean` | closed |
| Prop 1.3 (`t26n`) free basis: normalized polynomials factor uniquely into normalized irreducibles | `RHTower/DeningerDynSysNormalizedFactorization.lean` | closed |
| **Prop 1.3 (`t26n`) correspondence of normalized irreducibles**, both directions: `α.map = β^d` with `β` normalized irreducible over `κ₀^perf`, and every such `β` arises; a separable irreducible stays irreducible over a purely inseparable extension | `RHTower/DeningerDynSysNormalizedCorrespondence.lean` | closed |
| **Prop 1.3 (`t26n`)**: the exponent `d` is `q^m` for the separable contraction `expand(q^m) g = minpoly` | `RHTower/DeningerDynSysInseparableExponent.lean` | closed |
| **Prop 1.3 (`t26n`)**: that exponent **is** the degree of inseparability `d_x` of the corpus's `deningerInsepDegree` | `RHTower/DeningerDynSysInseparableIdentification.lean` | closed |
| Prop 1.3 (`t26n`) free monoid: the normalized factorization is well defined, additive on products and multiplicative on powers | `RHTower/DeningerDynSysNormalizedFactorization.lean` | closed |
| **Prop 1.3 (`t26n`) factorization law**: a normalized irreducible over `κ₀` factors over `κ₀^perf` as one irreducible repeated `d` times, every such irreducible arises, **the correspondence is injective (hence bijective)**, and the **descent criterion**: a normalized polynomial over `κ₀^perf` descends to `κ₀` exactly when each multiplicity is a multiple of the corresponding `d` | `RHTower/DeningerDynSysCorrespondenceFactors.lean` | closed |
| §1 the rational Witt functor respects monomorphisms | `RHTower/DeningerDynSysWittFunctoriality.lean` | closed |
| **Cor 13.5 (`t45`) algebraic core**: a) ⟺ a'), b) ⟺ b'), `Q⁻¹(0)` and `Q⁻¹(𝔪)` prime with `Q⁻¹(0) ⊆ Q⁻¹(𝔪)`, the factorization through `R/𝔭`, unit values outside `𝔮`, **the extension `Q_𝔮 : R_𝔮 → 𝒪`** and its two preimages `Q_𝔮⁻¹(0) = 𝔭R_𝔮`, `Q_𝔮⁻¹(𝔪) = 𝔮R_𝔮` | `RHTower/DeningerDynSysValuedPointsAffine.lean` | closed |

| **Prop 1.3 (`t26n`) closed in full**: `W_rat(κ₀) → W_rat(κ₀^perf)` has image exactly the normalized fractions all of whose multiplicities are divisible by the descent degree, and the two rows of the diagram combined | `RHTower/DeningerDynSysWittPerfectDescent.lean` | closed |
| **Prop 14.7(a) (`t125`)**: the perfection of a topological monoid, and density of `lim_{()^p} A` in `lim_{()^p} Â` | `RHTower/DeningerDynSysPerfectionDense.lean` | closed |
| **Prop 14.7(b) (`t125`)**: every element of `lim_{()^p} S⁻¹A` is a quotient `y z⁻¹`; Prop 14.7 is now closed in full | `RHTower/DeningerDynSysPerfectionFraction.lean` | closed |
| **§3 the space `X̂(C)`** of character points of a scheme, the Frobenius operators `F_ν`, their composition law, functoriality in `X`, and **Prop 4.2 last assertion** (`F_ν` injective over algebraically closed residue fields) | `RHTower/DeningerDynSysCharacterPoints.lean` | closed |
| **Def 4.1 (`t41n`)** admissible class of characters, **Prop 4.2 (`t42n`)** invariance of `X̂(C)_E` under `F_ν` (forward and backward) and under scheme isomorphisms, **Cor 4.4 (`t4ka`)** surjectivity of `pr_X` | `RHTower/DeningerDynSysCharacterPoints.lean` | closed |

| **§3 the colimit `X̌(C) = colim_{N₀} X̂(C)`**: the colimit relation is an equivalence relation unconditionally, `F_ν` is a **bijection** on the colimit, the projection to `X` descends, and `X̂(C) ↪ X̌(C)` | `RHTower/DeningerDynSysCharacterColimit.lean` | closed |
| **Prop 2.4 (`t27xn`) algebraic content**: `W_rat` is a faithful functor — a ring map is determined by the induced map of rational Witt rings (Teichmüller injectivity); `W_rat : CommRingCat ⥤ CommRingCat` is `Faithful` | `RHTower/DeningerDynSysWittFaithful.lean` | closed |
| **Prop 2.4 (`t27xn`) at the level of schemes**: two morphisms of schemes with the same underlying map whose rational Witt stalk maps agree on Teichmüller germs are equal | `RHTower/DeningerDynSysWittSchemeFaithful.lean` | closed |
| **mathlib gap**: a morphism of schemes is determined by its underlying continuous map together with its stalk maps (two sections with equal germs everywhere are equal, and germs of `f^♯ s` are stalk maps of germs) | `HTGeometry/SchemeHomStalkExt.lean` | closed |
| **Lemma 7.1 (`t7`)**: for an affine scheme the projection `X̂(C) → Spec R` is continuous for the topology of pointwise convergence | `RHTower/DeningerDynSysAffineTopology.lean` | closed |
| **Prop 7.5 (`t85`)**: the action map `X̂(C) × G → X̂(C)` is jointly continuous when `G` acts continuously on the discrete ring `R`; **Lemma 7.3 (`t9`) partial**: `G` acts by homeomorphisms and each `F_ν` is continuous | `RHTower/DeningerDynSysAffineTopology.lean` | closed (7.5); 7.3 partial |

| **Prop 14.6 (`t93`) and Prop 14.12 (`t119`)**: `F_p (Y_α) = Y_α` and `Y_α = Y_{v(p)}` for `α < 1`; the congruence `(a-b-c)^{p^ν} ≡ a^{p^ν}-b^{p^ν}-c^{p^ν} mod p` in every commutative ring | `RHTower/DeningerDynSysWittDefect.lean` | closed |

| **Def 3.5 (`t36n`)** the space `X̂̂(C)` of continuous character points; the projective limit `lim_{N₀} M` along the power maps, its projections `pr_ν`, the limit topology, and the elementary half of Cor 3.7 (a character factoring through `pr_ν` is continuous for discrete `M`) | `RHTower/DeningerDynSysPowerLimit.lean` | closed |
| **Prop 3.6 (`t37n`)**: every continuous character of `lim_{N₀} κˣ` into a divisible group with no small subgroups is `ψ ∘ pr_λ`; **Cor 3.7 (`t38n`)**: for discrete `κˣ` the continuous characters are exactly those factoring through a projection.  Also: the limit is `ν`-divisible (the shift), so `F_ν` is injective on characters | `RHTower/DeningerDynSysLimitCharacter.lean` | closed |

| **§4 the admissible class `E_f`** of characters with finite kernel: `ker (χ^ν)` is finite iff `ker χ` is (the quotient embeds in `μ_ν(C)`), so `E_f` is admissible in the sense of Def 4.1, it contains every injective character, and **Cor 4.4 holds for it** — a concrete non-vacuous instance | `RHTower/DeningerDynSysFiniteKernelClass.lean` | closed |

| **Def 14.1 (`t121`)** and **Def 13.2 (`t42nn`)**: the local ring `𝒪_{closure{x},y} = 𝒪_{X,y}/𝔭` of the closure of a point (a domain, with its evaluation onto `κ(y)`), the `𝒪`-valued triples `(x,y,P_y)` of Def 14.1, the extension by zero of a character of `κ(x)ˣ`, and the character triples `(x,y,P̄^×)` of Def 13.2 with Deninger's two commuting squares | `RHTower/DeningerDynSysValuedTriples.lean` | closed |

| **mathlib gap**: for a normal algebraic extension, restriction to the separable closure is a **group isomorphism** `Aut_F(E) ≅ Gal(F^sep/F)` — injectivity because an automorphism fixing `F^sep` satisfies `σ(a)^{q^n} = a^{q^n}` | `HTGeometry/AlgebraicClosureGaloisCompact.lean` | closed |
| **mathlib gap**: the inverse of that isomorphism is **continuous**, and hence `Aut_F(E)` is **compact** for every normal algebraic `E/F` — mathlib supplies compactness only under `IsGalois` | `HTGeometry/AlgebraicClosureGaloisCompact.lean` | closed |
| **Prop 1.4**: `ω : W_rat (κ₀) ≅ (ℤ̲κ / κ₀)^H` — the comparison is injective, its values are `H`-invariant, and every `H`-invariant element is a value; as a `RingEquiv` onto the invariant subring | `RHTower/DeningerDynSysProp14Invariants.lean` | closed |
| **Cor 3.1 (24)**: `Hom (W_rat (κ (x₀)) , C) ≅ Hom (κ (x)ˣ , Cˣ) / G_x` for `C` algebraically closed — surjectivity from Cor 1.6, and two characters induce the same homomorphism exactly when they differ by an element of the Galois group | `RHTower/DeningerDynSysCor31.lean` | closed |
| **Cor 3.1 (25)**: `Hom (W_rat (κ (x₀)) , C) ≅ Hom ((κ (x₀)^sep)ˣ , Cˣ) / G_x` — restriction of characters to the separable closure is bijective and Galois-equivariant; §3's Corollary 3.1 is closed in full | `RHTower/DeningerDynSysCor31Separable.lean` | closed |
| **mathlib gap**: for an injective `ι : A → B` of commutative groups such that every element of `B` has a `q^n`-th power in the image, restriction is a **bijection** on characters into any group where the `q`-th power map is bijective — characters extend by `q^n`-th roots, uniquely | `HTGeometry/RadicialCharacterExtension.lean` | closed |
| **Lem 5.3**: for coprime `ν ≠ ν'`, the roots of unity killed by some `ν^i − ν'^i` are exactly those of order prime to `νν'`; and modulo the image of the twisted norm `y ↦ y^ν σ (y)^{-ν'}` every element of a divisible group with finite `σ`-orbits is represented by such a root of unity, so the quotient is prime-to-`νν'` torsion | `RHTower/DeningerDynSysTwistedNorm.lean` | closed |
| **Cor 1.5(1) (`t28n`), injectivity modulo `H`**: two homomorphisms of `ℤ̲κ/κ₀` into a field agreeing on `W_rat(κ₀)` are Galois-conjugate — **unconditional, in every characteristic** | `RHTower/DeningerDynSysCor15Injective.lean` | closed |
| **Cor 1.5(1) topological input**: the Galois action on `ℤ̲κ` and on `ℤ̲κ/κ₀` has open stabilizers and is continuous for the Krull topology; and an action with open stabilizers on a discrete space is continuous | `RHTower/DeningerDynSysGaloisContinuousAction.lean`, `HTGeometry/DiscreteContinuousSMul.lean` | closed |
| **mathlib gap**: if a point has a smallest open neighbourhood `V`, the germ map on `Γ (F , V)` is an isomorphism — the indexing category of the stalk colimit has a terminal object | `HTGeometry/SmallestNeighbourhoodSections.lean` | closed |
| **Prop 13.1 groundwork, the three section rings**: on the spectrum of a one-dimensional local domain the sections of the structure sheaf are `0` over `∅`, `Frac 𝒪` over `{η}` (its own smallest neighbourhood) and `𝒪` over `⊤`; and an open contains the closed point iff it is `⊤`, and contains the generic point iff it is nonempty | `HTGeometry/SpecDimOneSections.lean` | closed |
| **Prop 13.1 groundwork, the base map**: a specialisation `x ⤳ y` and a one-dimensional local domain give the continuous `Spec 𝒪 → X` with `η ↦ x`, `s ↦ y`; the preimage of an open is `⊤` if it contains `y`, `{η}` if it contains `x` only, and `∅` otherwise | `HTGeometry/SpecTwoPointBase.lean` | closed |
| **Prop 13.1 (`t41`), diagram (139), the sheaf morphism**: a homomorphism `f_s` on `W_rat (𝒪_{X,y})` into `Γ (S , ⊤)` and one `f_η` on `W_rat (𝒪_{X,x})` into `Γ (S , V)` agreeing after restriction assemble into a morphism of presheaves `W_rat (𝒪_X) ⟶ f_* 𝒪_S`, with naturality in all nine cases | `RHTower/DeningerDynSysTwoPointGamma.lean` | closed |
| **Prop 13.1 (`t41`), the sheaf level**: the presheaf morphism extends over the sheafification, since the direct image of a sheaf is a sheaf | `RHTower/DeningerDynSysTwoPointSheafMap.lean` | closed |
| **Prop 13.1 (`t41`), the two stalk maps**: the stalk of the sheaf morphism at the closed point of `Spec 𝒪` is `f_s` followed by the germ over `⊤`, and at the generic point it is `f_η` followed by the germ over `{η}` — the second computation is where Deninger's square (139) is used | `RHTower/DeningerDynSysTwoPointStalks.lean` | closed |
| **Prop 13.1 groundwork**: for a local domain of dimension ≤ 1 that is not a field, `Spec 𝒪` has exactly the two points `η = (0)` and `s = 𝔪`, `{η}` is the basic open at any nonzero element of `𝔪`, and the only opens are `∅`, `{η}`, `⊤`; the stalk at `s` is `𝒪` and the stalk at `η` is `Frac 𝒪` | `HTGeometry/SpecDimOneLocalDomain.lean`, `HTGeometry/SpecStalkLocalization.lean` | closed |
| **Prop 14.16 (`t1213n`), the identification**: a pointed multiplicative map `A♭ → 𝒪` is additive modulo `p` — i.e. lies in Deninger's `Y^⋄` — exactly when it comes from a homomorphism of tilts, and the two nonvanishing conditions match because the untilt vanishes only at `0` over a reduced ring; as an `Equiv` | `RHTower/DeningerDynSysTiltAdditive.lean` | closed |
| **Prop 14.16 (`t1213n`), the locality clause**: `P̂_y^♭ : Ô^♭ → 𝒪^♭` is a **local** homomorphism.  `A ⧸ p` is local when `A` is, so `A♭` is local with maximal ideal the elements whose zeroth coefficient is a non-unit; the zeroth coefficient of `χ^♭ x` is the reduction of `χ x` mod `p`, so locality is exactly `χ (𝔪^♭) ⊆ 𝔪_𝒪` | `RHTower/DeningerDynSysTiltLocalHom.lean` | closed |
| **Prop 14.16 (`t1213n`) + Supple 14.10 (`t106`), the right square of (179)**: the residue of `P̂_y` is computed by `P̃_y` on all of `lim_{()^p} Ô` because both sides are continuous into the discrete residue field and agree on the dense image of `lim_{()^p} 𝒪`; feeding `P̃_y (0) = 0` gives the locality of `P̂_y^♭` | `RHTower/DeningerDynSysHatLocality.lean` | closed |
| **mathlib gap**: a set saturated for a continuous map into a discrete space is open; hence every coset of an ideal of `Â` containing `ker (Â ↠ A/I)` is open, and cosets of a maximal ideal are open as soon as cosets of a principal ideal inside it are | `HTGeometry/AdicCompletionOpenCosets.lean` | closed |
| **mathlib gap**: `untilt 0 = 0` over any `p`-adically complete ring, and `untilt x = 0 ↔ x = 0` over a reduced one | `RHTower/DeningerDynSysTiltAdditive.lean` | closed |
| **Def 14.9 (`t42n`) + Prop 14.11 (`t1213nn`)**: the completed `𝒪`-valued points `(x,y,P^×)` with Deninger's diagram (177) are exactly the continuous pointed multiplicative maps `P̂_y` satisfying 1) and 2); the hypotheses (ratio presentation of `lim_{()^p} κ(x)`, surjectivity of evaluation at `y`) are non-vacuous — they hold over a one-point scheme | `RHTower/DeningerDynSysCompletedTriple.lean`, `RHTower/DeningerDynSysCompletedTripleSpec.lean` | closed |
| **Prop 14.8(a) (`t125`) in concrete form**: the projective-limit topology on an adic completion, its `ContinuousMul`, density of `R → R̂`, and hence density of `lim_{()^p} A` in `lim_{()^p} Â` | `HTGeometry/AdicCompletionTopology.lean`, `RHTower/DeningerDynSysPerfectionAdicDense.lean` | closed |
| **§14 infrastructure**: `lim_{()^p} M` is a commutative monoid with zero, has no zero divisors when `M` has none, and is a commutative group with zero when `M` is one; pointed multiplicative maps of groups with zero are unit-group characters; a pointed multiplicative map extends **uniquely** along a ratio presentation | `HTGeometry/PerfectionMonoidWithZero.lean`, `HTGeometry/GroupWithZeroMultiplicativeExtension.lean` | closed |
| **Cor 13.5 + Prop 13.4 + Prop 13.1 combined**: for `Spec R` with algebraically closed residue fields and integrally closed stalks the `𝒪`-valued points in the Witt description are the `Q : R → 𝒪` with a') and b') | `RHTower/DeningerDynSysAffineValuedPoints.lean` | closed |
| **Cor 13.5 (`t45`) CLOSED**: for `X = Spec R` the `𝒪`-valued points of `W_rat(X)` are the pointed multiplicative maps `Q : R → 𝒪` with a') and b'), and (composing with Prop 13.4) the character triples of Def 13.2 | `RHTower/DeningerDynSysAffineValuedPoints.lean` | closed |
| **Cor 13.5 support**: `Q_𝔮` is again additive on its zero set and modulo `𝔪`; the pointwise criterion turning a) 1)–3) into (`additiveOnZeros`, `additiveModMax`, two kernel identifications) and back; the `Spec R` evaluation dictionary | `RHTower/DeningerDynSysValuedPointsAffine.lean`, `RHTower/DeningerDynSysValuedLocalCriterion.lean`, `RHTower/DeningerDynSysSpecStalkDictionary.lean` | closed |
| **(26)**: the `C`-valued points of `W_rat(X)` are the character points `X̂(C)` | `RHTower/DeningerDynSysWittCharPoints.lean` | closed |
| **§13 hypotheses are non-vacuous**: `Spec K` for `K` algebraically closed has stalk and residue field `K` at its unique point, so the valued-point equivalence applies to it; plus the reusable `stalk (Spec R) 𝔭 ≅ R_𝔭` | `HTGeometry/SpecStalkLocalization.lean`, `RHTower/DeningerDynSysWittValuedPointSpec.lean` | closed |
| **Prop 13.1 (`t41`) + (145)**: the `𝒪`-valued points of `W_rat(X)` in the Witt-homomorphism description (Deninger's `f̃_η^♯`, `f_s^♯`, `f̃_s^♯` with the two commuting squares) are exactly the character triples of Def 13.2, hence also the triples `(x,y,P'_y)` | `RHTower/DeningerDynSysWittValuedPoint.lean` | closed |
| **Prop 13.1 (`t41`) CLOSED IN FULL**: a pair of stalk maps with the square (139) and the locality data (140) **is** a morphism `Spec 𝒪 → W_rat (X)` in the sense of Def 2.5, and its stalk maps give the pair back; the `stalkHom`/`stalkHom_comp` fields of Def 2.5 carry no information once `W_rat` commutes with stalks | `RHTower/DeningerDynSysProp131.lean` | closed |
| **Prop 3.5, affine case**: for a ring with a continuous profinite action and invariant subring, the `C`-points of `Spec B` map **onto** those of `Spec A` with fibres exactly the `G`-orbits — Kucharczyk–Scholze Lemma 4.9 transported along `Spec.preimage` | `RHTower/DeningerDynSysProp35Affine.lean` | closed |
| **§5, equations (41)–(43)**: Deninger's `ρ (P) = |(ker P)_tors|` and its Frobenius law `ρ (F_ν P) = ν_x ρ (P)` — the `ν`-th power map is a surjection of the torsion kernel of `F_ν P` onto that of `P` with kernel `μ_ν (κ)`, whose order is the prime-to-characteristic part of `ν` | `RHTower/DeningerDynSysRhoFrobenius.lean` | closed |
| **Prop 3.5, the covering step**: a `C`-point of a scheme has a single point as image, so it factors through any affine open containing it; hence the affine case globalises and every `C`-point of the base lifts | `RHTower/DeningerDynSysProp35Global.lean` | closed |
| **Cor 3.3, formal content**: for a normal subgroup `N ≤ G` acting on a set, `G` acts on the `N`-orbit space and `(S / N) / G = S / G` — Deninger's iterated descent `W_rat(X₁)(C)/G₁ = W_rat(X₀)(C)` | `HTGeometry/OrbitQuotientComposition.lean` | closed |
| **Prop 1.1(b) in ring form over a domain**: `ω : ℤ[A ∖ 0] ≃+* W_rat(A)` for an integrally closed domain with algebraically closed fraction field, and the consequence `Hom_ring(W_rat(A), R) ≃ (A →*₀ R)` used for the `𝒪`-valued points | `RHTower/DeningerDynSysOmegaDomainRing.lean` | closed |
| **Prop 1.1(b) (`t21nn`) in ring form**: `ω : ℤ[κˣ] ≃+* W_rat(κ)` for `κ` algebraically closed — the additive comparison is multiplicative because both sides are biadditive and `[a]⊙[b] = [ab]` | `RHTower/DeningerDynSysOmegaRing.lean` | closed |
| **Cor 1.5(1) / Cor 1.7(2) algebraic core**: `Hom(W_rat(κ), C) ≃ (κˣ →* Cˣ)` for `κ` algebraically closed, via `ω` and `liftNCRingHom` | `RHTower/DeningerDynSysWittHomCharacters.lean` | closed |
| **Cor 1.5(1) / Cor 3.1 (`t29n`) modulo `G`**: `Hom(W_rat(κ)^G, C) = Hom(κˣ, Cˣ)/G` — surjectivity of restriction and the `G`-conjugacy criterion, for a profinite `G` acting continuously on an algebraically closed `κ` | `RHTower/DeningerDynSysCharacterQuotient.lean` | closed |

| **§1 root multiplicities**: every root of `minpoly F x` in an algebraic closure has multiplicity exactly the degree of inseparability `d_x` (via the perfect closure and separability over a perfect field) | `RHTower/DeningerDynSysRootMultiplicity.lean` | closed |
| **Prop 1.3 (`t26n`) atom form**: the Teichmüller atoms of the image of a normalized irreducible over `κ₀` are one nodup conjugacy class repeated exactly `d` times; atoms are additive on products and the atom count is the inverse-root multiplicity | `RHTower/DeningerDynSysAtomMultiplicity.lean` | closed |

| **Cor 1.5(1) (`t28n`) injectivity half**: `ℤ̲κ/κ₀` contains `d_a·(a)` and `(a)^{d_a} = (a^{d_a})`, so a ring homomorphism of `ℤ̲κ` into an algebraically closed field is determined by its restriction — the additive relation when `d_a` is invertible, the perfect-field `p`-power relation otherwise | `RHTower/DeningerDynSysInsepSubringHom.lean` | closed |

| **Lifting along an integral extension** (mathlib gap): a homomorphism into an algebraically closed field extends along an injective integral ring extension | `RHTower/DeningerDynSysIntegralLift.lean` | closed |
| **Cor 1.5(1) (`t28n`) second bijection**: `ℤ̲κ` is integral over `ℤ̲κ/κ₀` (each atom satisfies `X^{d_a} − (a^{d_a})`), so restriction `Hom(ℤ̲κ, C) → Hom(ℤ̲κ/κ₀, C)` is **bijective** for `C` algebraically closed | `RHTower/DeningerDynSysInsepSubringHom.lean` | closed |
| **Root multiplicities of the reverse** (mathlib gap): `rootMultiplicity r⁻¹ (p.reverse) = rootMultiplicity r p` for `p.coeff 0 ≠ 0` | `RHTower/DeningerDynSysReverseRoots.lean` | closed |
| **Prop 1.3 (`t26n`) coefficient law**: every atom of the image of a normalized irreducible over `κ₀` occurs with multiplicity **exactly** `d_r`, and for a product of normalized irreducibles every atom multiplicity is divisible by `d_r` — Deninger's defining condition for `ℤ̲κ/κ₀` | `RHTower/DeningerDynSysAtomMultiplicity.lean` | closed |

| **Prop 1.3 (`t26n`) lower row, `ω`-transport**: `ω` sends the atom sum of a normalized polynomial to the corresponding rational Witt vector, atom-sum coefficients are multiset counts, and the atom sum of the image of a normalized polynomial over `κ₀` lies in `ℤ̲κ/κ₀` | `RHTower/DeningerDynSysOmegaAtomBridge.lean` | closed |

| **Def 14.2 (`t91`)** the `p`-adically continuous subspace `X̂_c(𝒪)` (as the elementary congruence condition, no topology needed), its Frobenius invariance, and **Prop 14.4 (`t124`)**: ring homomorphisms — the honest `𝒪`-valued points — are `p`-adically continuous | `RHTower/DeningerDynSysPAdicContinuous.lean` | closed |
| **Prop 1.3 (`t26n`)**: the descent degree of a normalized irreducible over `κ₀^perf` **is** the degree of inseparability of its atoms; distinct normalized irreducibles have disjoint atoms | `RHTower/DeningerDynSysDescentDegreeAtom.lean` | closed |
| **Prop 1.3 (`t26n`) atom criterion**: a normalized polynomial over `κ₀^perf` descends to `κ₀` as soon as every atom multiplicity is divisible by that atom's degree of inseparability — Deninger's condition `d_r ∣ n_r`, now sufficient as well as necessary | `RHTower/DeningerDynSysAtomDescent.lean` | closed |

| **Prop 1.3 (`t26n`) lower row, Witt level**: a rational Witt vector over `κ₀^perf` descends to `κ₀` exactly when, for every atom, the difference of its multiplicities in numerator and denominator is divisible by its degree of inseparability — via the disjoint representative `P' = (S_P − S_Q).prod`, `Q' = (S_Q − S_P).prod` obtained from `S + (T − S) = S ∪ T` | `RHTower/DeningerDynSysWittAtomDescent.lean` | closed |

| **Prop 1.3 (`t26n`) lower row, closed as an iff**: a rational Witt vector over `κ₀^perf` descends to `κ₀` **exactly when** its `ω`-atom datum lies in `ℤ̲κ/κ₀ = deningerInsepSubring` | `RHTower/DeningerDynSysInsepSubringDescent.lean` | closed |

| **Prop 1.3 (`t26n`) CLOSED**: `ω` is equivariant for relabelling of atoms, and a class in `ℤ̲κ` comes from `W_rat(κ₀)` **exactly when** it is `H`-invariant and lies in `ℤ̲κ/κ₀` — the literal lower row `(ℤ̲κ/κ₀)^H ≅ W_rat(κ₀)` | `RHTower/DeningerDynSysOmegaEquivariant.lean` | closed |

| **Def 14.5 (`t92`) / Def 14.11 (`t1512`)** the subspaces `Y_α` cut out by the additive defect | `RHTower/DeningerDynSysWittDefect.lean` | closed |
| **Cor 1.5(1) input**: the Galois action on `ℤ̲κ/κ₀` (relabelling permutes coefficients, the degree of inseparability is `Aut_F`-invariant, the subring is stable) and the finiteness of `Aut_F(E)`-orbits of algebraic elements | `RHTower/DeningerDynSysInsepSubringAction.lean`, `RHTower/DeningerDynSysAlgebraicOrbit.lean` | closed |

| **Integrality from finite orbits** (mathlib gap): a group acting on a commutative ring with all orbits finite makes every element integral over the invariants, via the orbit polynomial | `RHTower/DeningerDynSysFiniteOrbitIntegral.lean` | closed |
| **Cor 1.5(1) input**: the `Aut_{κ₀}(κ)`-action on `ℤ̲κ` by relabelling of atoms, as a `MulSemiringAction` | `RHTower/DeningerDynSysGaloisMonoidAlgebra.lean` | closed |

| **Cor 1.5(1) input**: the Galois orbits on `ℤ̲κ` and on the stable subring `ℤ̲κ/κ₀` are **finite** (a class is determined by the images of the atoms in its finite support, and each atom has a finite orbit) | `RHTower/DeningerDynSysGaloisOrbitFinite.lean`, `RHTower/DeningerDynSysCor15.lean` | closed |

| **Cor 1.5(1) (`t28n`) surjectivity**: every ring homomorphism `W_rat(κ₀) → C` into an algebraically closed field is induced by a character of `κˣ`.  `ℤ̲κ/κ₀` is integral over `W_rat(κ₀)` because the orbit polynomial has invariant coefficients lying in `ℤ̲κ/κ₀`, hence coming from `W_rat(κ₀)` by Prop 1.3; the lifting theorem then extends along `W_rat(κ₀) → ℤ̲κ/κ₀`, and the already-proved bijection extends further to `ℤ̲κ` | `RHTower/DeningerDynSysCor15.lean` | closed |

| **§2 / §13, the key brick**: `W_rat` **commutes with stalks** — the comparison `stalk (W_rat 𝒪_X) → W_rat (𝒪_x)` is an isomorphism, and so is its sheaf-level version.  Surjectivity: a normalised fraction over the stalk has finitely many coefficients, which lift to a common neighbourhood.  Injectivity: a normalised fraction is zero exactly when numerator and denominator agree, which is finitely many equalities of germs | `RHTower/DeningerDynSysWittStalkIso.lean` | closed |
| **mathlib gap**: finitely many germs lift to a common open neighbourhood; a polynomial over a stalk is the image of a polynomial over sections (with the constant term normalised after shrinking); and finitely many germ equalities hold already over a smaller neighbourhood | `HTGeometry/GermPolynomialLift.lean` | closed |
| **§2 stalks**: sheafification does not change the stalks of the rational Witt presheaf, and the canonical comparison `stalk (𝒪 ⋙ W_rat) → W_rat (𝒪_x)` — the infrastructure for Def 2.4/2.5 | `RHTower/DeningerDynSysWittStalk.lean` | closed |

| **Def 2.5 (`t25n`)**: a morphism `S → W_rat(X)` — a morphism of ringed spaces whose stalk maps `W_rat(𝒪_{X,f(s)}) → 𝒪_{S,s}` are compatible with the sheaf morphism through the stalk comparison and descend to the residue data | `RHTower/DeningerDynSysWittStalk.lean` | closed |

| **Def 2.3 (`t24n`)**: a morphism `W_rat(Y) → W_rat(X)` of rational Witt spaces, with the stalk maps `W_rat(𝒪_{X,f(y)}) → W_rat(𝒪_{Y,y})` compatible with the sheaf morphism and local on residue fields; §2's definitions are now complete | `RHTower/DeningerDynSysWittStalk.lean` | closed |

Axiom audit: every capstone above depends only on `propext`, `Classical.choice`, `Quot.sound`.

### Duplication audit (2026-08-22)
The corpus's `Deninger*RationalWitt*` modules formalize a **different** Deninger paper (the 2025
rational-Witt paper: the `ω`-comparison `ℤ̲A → W_rat(A)`, absolute-Galois descent over perfect
fields, the corrected normal-domain descent, and the Fatou intersection).  A grep for this paper's
internal labels (`t29`, `t87`, `t46n`, `t21n`, `t1213`, `t125`, `t1110`, …) over `formal/` and over
the 77 pipeline cards citing arXiv:1807.06400 returns only the modules listed above.  §1 overlaps
partially: Prop 1.1 (a) and (b) are covered by
`deningerRationalWittReducedMonoidAlgebraToAdditive_injective` / `..._surjective` and the
AIC-domain comparison.

### Known heavy sub-projects (not yet started)
* Prop 1.3's top row is closed; what remains of Prop 1.3 is the lower isomorphism
  `(ℤ̲κ/κ₀)^H ≅ W_rat(κ₀)`, i.e. the bijection between normalized irreducible polynomials over
  `κ₀` and over `κ₀^perf` (`α = α̃^d`; the source writes `α(t) = α̃(t^d)`, the same statement
  after the Frobenius twist), plus unique factorization of normalized polynomials.
* Lemma 4.3 (`t3`) is closed **in full**, including the final "in particular" in both the
  equal-characteristic and the mixed-characteristic case.  Its dimension input `#C ≤ dim_ℚ (C^× / μ(C))` was proved by
  exhibiting a countably infinite multiplicatively independent family (rational primes in
  characteristic zero; monic irreducible polynomials evaluated at a non-root-of-unity in
  characteristic `p`) and then using `Module.Free.rank_eq_mk_of_infinite_lt`.  The *only* residue
  was the mixed-characteristic half of the final "in particular", an injective
  `μ(F̄_p) ↪ μ(C)` for `C` algebraically closed of characteristic `0`; it is now proved by the
  reduction isomorphism `μ_{p'}(C) ≅ (𝒪/𝔪)^×` at a maximal ideal of the algebraic integers of `C`
  above `p`, whose residue field is shown to be algebraically closed.
* Thm 1.4 (`t27n`) is Kucharczyk–Scholze Lemma 4.9 plus its rational-Witt corollary.  Mathlib now
  supplies the needed profinite invariant theory: `Algebra.IsInvariant.isIntegral_of_profinite`,
  `Algebra.IsInvariant.exists_smul_of_under_eq_of_profinite`, and
  `Ideal.Quotient.stabilizerHom_surjective_of_profinite`.  Remaining work: extend a hom
  `A^H → C` along the integral extension (lying over + `IsAlgClosed.lift`), and turn the two
  transitivity statements into transitivity of `H` on `Hom (A, C)`.
* §2 is under way: the functor `W_rat`, the presheaf `U ↦ W_rat(𝒪_X(U))`, its separatedness
  (Prop 2.1(a), both halves, via `Presheaf.isLocallyInjective_iff_injective_of_separated`), and
  the ringed space `W_rat(X)` of Def 2.2/2.3 are closed.  What remains in §2 is Prop 2.1(b), (c)
  — which need the Fatou intersection `W_rat(K) ∩ W(A) = W_rat(A)` together with integral schemes
  and their function fields — and Def 2.4/Prop 2.4 (`t27xn`), the locality condition on morphisms
  and the injectivity of `W_rat` on morphisms.
* §§3, 13, 14 need the `S`-valued points of `W_rat(X)` as scheme-level infrastructure.
* Claim 8.1 is an open conjecture in the source; Thm 8.2 is conditional on it in dimension ≥ 2.

### Roadmap for the remaining results (next sessions)
1. **Prop 1.3 lower isomorphism / Cor 1.5(1).**  The polynomial correspondence `α = α̃^d` is now
   **closed** (`deningerMinpoly_map_eq_pow`, via `deningerPow_eq_expand`).  What is still needed:
   (a) unique factorization of normalized polynomials — **closed**
   (`deningerExists_normalized_factorization`, `deningerNormalized_factorization_unique`);
   (b) the correspondence `α.map = β^d` in **both directions** — **closed**
   (`deningerNormalizedIrreducible_map_eq_pow`, `deningerNormalizedIrreducible_exists_preimage`,
   both from the core `deningerNormalizedPair`).  (c) `d = q^m` and (d) `q^m = d_x`, the degree of
   inseparability, are **closed** (`deningerMinpoly_map_perfectClosure_eq_pow_expChar`,
   `deningerMinpoly_map_perfectClosure_pow_insepDegree`).  The factorization law
   (`deningerNormalizedFactors_map_irreducible`, `..._map_surjective`) now determines the image of
   the normalized polynomials of `κ₀[t]` inside those of `κ₀^perf[t]` — exactly the products whose
   multiplicities are divisible by the corresponding `d_β`, which is the condition defining
   `ℤ̲κ/κ₀`.  The correspondence is now proved **bijective**
   (`deningerNormalizedIrreducible_map_injective` and `..._exists_preimage`) and the descent
   criterion `deningerNormalized_descends` characterises the image of the normalized polynomials.
   The single remaining step of Prop 1.3 is (e): transporting that criterion through the corpus's
   **localization model** of `W_rat` (`DeningerRationalWittLocalization`, via
   `deningerRationalWittAdditive_exists_normalized_fraction`) and through `ω : ℤ̲κ ≅ W_rat(κ)` to
   get the ring isomorphism `(ℤ̲κ/κ₀)^H ≅ W_rat(κ₀)`.  Injectivity is
   `deningerCanonicalRationalWittMap_injective`; only surjectivity onto the invariants is at
   issue, and it now reduces to applying `deningerNormalized_descends` to the numerator and
   denominator of a normalized fraction.
2. **Prop 3.6 / Cor 3.7.**  Build `lim_{N₀} M` along the `ν`-th power maps (a subgroup of
   `N₀ → M` cut out by `x_{νμ}^μ = x_ν`, with the subspace topology), show `T = ker pr_1` embeds in
   `∏_ν μ_ν(K)` with each `μ_ν(K)` finite hence discrete, so `T` is linearly topologized, and feed
   `deningerIsOpen_ker_of_noSmallSubgroups`.  The last step needs the Frobenius operators `F_ν`,
   which are isomorphisms on the limit.
3. **Prop 2.1(b), (c).**  CLOSED.  Route used: realize the sheafification inside the sheaf
   `W(𝒪_X)` as the *locally rational* subpresheaf, prove the comparison
   `W_rat(𝒪_X) ⟶ W(𝒪_X)` (a `sheafifyLift`) is injective on sections with image exactly that
   subpresheaf, then run Deninger's argument with `deningerRationalWittFatouIntersection_iff`
   transported to the ring carriers.  Superseded note: what
   is missing is the scheme layer: integral scheme, function field `K = 𝒪_{X,η}`, injectivity of
   `𝒪_X(U) → K`, and affine covers by Fatou rings.  `W(𝒪_X)` is now a sheaf
   (`deningerBigWittPresheaf_isSheaf`), which is the ambient sheaf in (c).
4. **Def 2.4 / Def 2.5 / Prop 2.4 (`t27xn`).**  The stalk layer is now in place
   (`DeningerDynSysWittStalk`): `TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso` gives that
   sheafification preserves stalks, and `deningerWittStalkToStalk` is the canonical comparison to
   `W_rat` of the stalk.  Writing Def 2.5 literally still needs that comparison to be an
   **isomorphism**, i.e. `W_rat` commuting with filtered colimits (true: a normalized fraction has
   finitely many coefficients, and equality is a finite condition).  A first attempt at Def 2.5
   Def 2.5 is now closed by carrying `f^♯_s : W_rat(𝒪_{X,f(s)}) → 𝒪_{S,s}` as *datum* together with
   its compatibility through `deningerWittStalkToStalk` — no inverse needed.  **Def 2.3 is closed too.**  The `inv` of the
   sheafification stalk map does elaborate — but only when the `IsIso` instance is passed
   explicitly as `@inv _ _ _ _ f inst`; writing `inv f` makes Lean elaborate `f` against the
   expected type of the whole composite and instance search then fails on a term it cannot match.
5. **§§3, 5, 6, 7, 9–13, 15** are gated on the `S`-valued points of `W_rat(X)`.  The algebraic
   core of Cor 13.5 (`t45`) — the description of those points over an affine base as pointed
   multiplicative maps `Q : R → 𝒪` with a')/b') — is closed; the extension `Q_𝔮 : R_𝔮 → 𝒪` and its two
   preimages are closed too; what remains there is only the scheme-level bookkeeping of the pair of
   points `y ∈ closure {x}` and the identification with `Hom(W_rat(𝒪_{X,y}), 𝒪)`.
6. **§14 remainder.**  14.13 (`t1110`) is pure algebra (the tilting correspondence for
   `p`-adically complete rings, via `PreTilt`/`fontaineTheta`); the rest needs the `𝒪`-valued
   point spaces.
7. **Claim 8.1 is open in the source**; Thm 8.2 stays conditional in dimension ≥ 2.
8a. **Cor 1.5(1) surjectivity is CLOSED** (`deningerCor15_surjective`).  The earlier heartbeat
   blowup was caused by the nested `FixedPoints.subring ↥(ℤ̲κ/κ₀)`; the working route avoids it
   entirely, going straight from `W_rat(κ₀)` to `ℤ̲κ/κ₀` with the orbit polynomial whose
   coefficients are pulled back through Prop 1.3.  What remains of Cor 1.5(1) is the
   injectivity-modulo-`H` half (two characters induce the same homomorphism iff they are
   `H`-conjugate), i.e. the harder direction of Kucharczyk–Scholze Lemma 4.9.
   Superseded notes:  All inputs are closed: Prop 1.3 in the
   `ℤ̲κ/κ₀` form, the bijection `Hom(ℤ̲κ,C) ≃ Hom(ℤ̲κ/κ₀,C)`, the general lifting theorem along an
   integral extension, the `MulSemiringAction` of `Aut_{κ₀}(κ)` on `ℤ̲κ` and its restriction to
   `ℤ̲κ/κ₀`, finiteness of the orbits there, and integrality from finite orbits.  The **only**
   remaining step is to combine the last two into
   `Algebra.IsIntegral (FixedPoints.subring ↥(ℤ̲κ/κ₀) H) ↥(ℤ̲κ/κ₀)` and feed it to the lifting
   theorem.  Elaborating that instance currently exceeds 2M heartbeats — the next attempt should
   supply `Nontrivial ↥(deningerInsepSubring …)` and the `Algebra` instance by hand rather than by
   instance search, or restate `deningerIsIntegral_of_finite_orbits` with the algebra map as an
   explicit argument.

8. **Cor 1.5(1) remaining pieces** (2026-08-23).  Closed: `ω : ℤ[κˣ] ≃+* W_rat(κ)`;
   `Hom(W_rat(κ), C) ≃ (κˣ →* Cˣ)`; `Hom(W_rat(κ)^G, C) = Hom(κˣ, Cˣ)/G`; the atom form of
   Prop 1.3 (a normalized irreducible over `κ₀` has atoms one nodup conjugacy class repeated `d`
   times); `Hom(ℤ̲κ, C) → Hom(ℤ̲κ/κ₀, C)` injective.  Still needed: (i) surjectivity of that
   restriction, i.e. a **general lifting theorem "integral ring extension + algebraically closed
   target ⟹ homomorphisms extend"** (mathlib has none; the corpus has it only for invariant
   subrings, `deningerHom_exists_extension`), and (ii) the identification
   `(ℤ̲κ/κ₀)^H ≅ W_rat(κ₀)` obtained by transporting the descent criterion through `ω` with the
   atom dictionary `deningerRootUnits_map_irreducible`.

## Gates
- [x] 0 → 1  in-progress
- [ ] 1 → 2  paper proofs read and dependency-closed per item
- [ ] 2 → 3  Lean theorems, `lake build` green per module, axiom audit PASS

## Log
- 2026-08-23 — **Prop 14.13's correspondence `χ = ♯ ∘ χ♭` is built and shown injective**: the
  zeroth coefficient of `χ♭ x` is the reduction of `(χ♭ x)^♯` modulo `p`
  (`PreTilt.mk_untilt_eq_coeff_zero`), and `Perfection.hom_ext` says a homomorphism into a
  perfection is determined by its zeroth coefficient.  Composing with `deningerTiltEquiv` transports
  this to `lim_{()^p} A`.  What is left of 14.13 is surjectivity of the correspondence: that every
  pointed multiplicative `χ` with additive reduction arises this way, via `Perfection.lift` applied
  to `χ mod p`.
- 2026-08-23 — **the tilting identification `lim_{()^p} A ≅ A♭` is closed** for `p`-adically
  complete rings.  Surjectivity: lift each coefficient, raise the `(n+k)`-th lift to the `p^k`-th
  power, and note the sequence is Cauchy because a congruence mod `p^{m+1}` improves to one mod
  `p^{m+2}` after raising to the `p`-th power (proved here from `geom_sum₂_mul`, mathlib only has
  the `dvd_sub_pow_of_dvd_sub` form); `IsPrecomplete.prec` then supplies the limits, and
  `IsHausdorff` identifies them.  Together with the injectivity half this is `deningerTiltEquiv`.
- 2026-08-23 — **the injectivity half of the tilting comparison closed**: `lim_{()^p} A → A♭` is
  injective for `p`-adically separated `A`, because the `n`-th coefficient is the `p^k`-th power of
  the `(n+k)`-th and `dvd_sub_pow_of_dvd_sub` then puts the difference in every power of `(p)`.
  Surjectivity is the remaining half and needs `IsPrecomplete`: the sequence `x_{n+k}^{p^k}` is
  Cauchy, and its limit is the required coefficient.
- 2026-08-23 — **Prop 14.13's Witt-vector factorization (120n)/(121n) closed** on top of mathlib's
  new perfectoid layer: `fontaineTheta : 𝕎 R♭ →+* R` and `fontaineTheta_teichmuller` exist, so
  `W_p(χ) := θ ∘ W_p(χ♭)` sends `[x]` to `(χ♭ x)^♯`.  Note `PreTilt A p` needs
  `Fact (¬ IsUnit (p : A))` for its ring structure.  What remains of 14.13 is the bijection itself,
  which needs `lim_{()^p} A ≅ A♭` for `p`-adically complete `A`.
- 2026-08-23 — **Cor 13.5's remaining displayed content closed**: the b)-factorization
  `R → R/Q⁻¹(𝔪) → k` (the a)-factorization was already owned) and the specialisation
  `Q⁻¹(0) ⊆ Q⁻¹(𝔪)` read in `Spec R` as `y ∈ closure {x}`.  What is still open in §13 is the
  *identification* of `X̂(𝒪)` with these data, which needs the scheme-level `𝒪`-valued points of
  `W_rat(X)` (Prop 13.1) — a morphism out of `Spec` of a rank-one valuation ring in the sense of
  Def 2.5, reconstructed from its two stalk maps.
- 2026-08-23 — **Supple 14.9 (`t106`) closed**, exactly by Deninger's two observations: a
  continuous map out of the perfection of the completion is determined by its restriction along the
  dense comparison map (`DenseRange.equalizer` with the density from Prop 14.7(a)), and a map
  prescribed on a surjection is unique.
- 2026-08-23 — **Prop 7.5 (`t85`) closed for an arbitrary scheme**, in Deninger's own two steps:
  continuity of a map out of `Z × G` is local on an open cover of `Z`, and over a piece where the
  group acts on the sections with open stabilisers the identity `eval U g (σ·P) = eval U (σ·g) P`
  makes each coordinate agree, near `σ₀`, with a map that does not involve `σ` at all.  §7 is now
  closed in full.
- 2026-08-23 — **Cor 7.9's quotients closed, and with them all four spaces.**  Mathlib deduces
  Hausdorffness of an orbit space from properness of the action but has no instance making a
  compact group act properly, so the statement is proved directly: the orbit relation is the image
  of the closed set `{(g, x, y) | g • x = y}` under `G × (X × X) → X × X`, a closed map because `G`
  is compact, and the orbit quotient map is an open quotient map.  This is a reusable mathlib gap.
- 2026-08-23 — **Cor 7.9 for `X̌(C)` closed.**  `mk ν ⁻¹' (unit '' s) = F_ν '' s`, so the
  canonical map is open, hence an open embedding; and `F_μ` sends the class of `(μ, P)` to the
  class of `(1, P)`, so applying `F_{μμ'}` carries any two points into the image of `X̂(C)` at once.
  What is left of Cor 7.9 is the two quotients `X̂₀(C)` and `X̌₀(C)`, which need Hausdorffness of the
  `G`-quotient — Deninger gets it from Cor 7.8's quotient metric in the affine case and then glues.
- 2026-08-23 — **Cor 7.9's main step closed.**  Over an affine open a character point is
  determined by the evaluations: the base point because the basic opens form a basis and a scheme
  is `T0`, and the character because `IsAffineOpen.isLocalization_stalk` makes every element of the
  residue field a ratio `eval a / eval s` of evaluations.  So the affine trace embeds in
  `Γ(X,U) → C` and is Hausdorff; since the traces are open embeddings, `X̂(C)` is Hausdorff as soon
  as any two points of `X` lie in a common affine open.  That last fact for a scheme with an ample
  invertible sheaf is Stacks 28.29.5, which Deninger also cites rather than proves.
- 2026-08-23 — **Prop 7.4(c) closed, together with Lemma 7.3's `G`-part globally.**  The key
  identity is `eval V g (f̂ P) = eval (f⁻¹V) (f^♯ g) P`, from `Scheme.evaluation_naturality_apply`
  together with the fact that extension by zero commutes with precomposition by a field
  homomorphism.  For an isomorphism the preimage of an affine open is affine
  (`IsAffineOpen.preimage_of_isIso`), so every affine trace of the source maps continuously into an
  affine trace of the target; applying this to the inverse gives a homeomorphism, and it descends
  to `X̌(C)` because `f̂` commutes with the Frobenius operators.  §7 is now closed except Cor 7.9,
  which needs the Stacks input that two points of a scheme with an ample invertible sheaf lie in a
  common affine open, and the global form of Prop 7.5.
- 2026-08-23 — **Lemma 7.3 (`t9`) is now closed in full.**  With
  `DeningerSectionsDivisible X U ν` (every section over `U` is a `ν`-th power) the evaluation of a
  section factors through the Frobenius operator, `eval U (gᶰ) = eval U g ∘ F_ν`, so `F_ν` is
  inducing on the affine trace; being injective with clopen range it is an open embedding and a
  closed embedding there, and both properties glue to `X̂(C)` because
  `val_U ⁻¹' (F_ν '' W) = F_ν^U '' (val_U ⁻¹' W)`.
- 2026-08-23 — **Lemma 7.3's clopen assertion and Prop 7.4(a) closed.**  The setting predicate
  `DeningerRootsFromSections X U ν` (every `ν`-th root of unity of a residue field over `U` is the
  value of a `ν`-th root of unity in `Γ(X, U)`) turns equation (21) into finitely many evaluation
  conditions; the restriction map to `μ_ν(Γ(X,U))` — a finite set, being roots of `Xᶰ − 1` in a
  domain — has finite range, so its point preimages partition the trace into closed sets and each
  is therefore clopen.  Prop 7.4(a) follows because `mk ν ⁻¹' (range unit) = range F_ν`, using
  injectivity of `F_b` on `X̂(C)`.  What is left of 7.3 is that `F_ν` is an open and closed *map*,
  which needs the `ν`-divisibility of `Γ(X, U)` to make `F_ν` inducing (`eval U (gᶰ) = eval U g ∘ F_ν`).
- 2026-08-23 — **Lemma 7.3's image description (equation (21)) closed.**  Over an algebraically
  closed residue field the `ν`-th power map on the unit group is surjective with kernel `μ_ν`, so a
  character is a `ν`-th power exactly when it kills `μ_ν`; the root is built by
  `QuotientGroup.lift` along `quotientKerEquivOfSurjective`.  What the clopen half of 7.3 (and
  hence Prop 7.4(a)) still needs is that those roots of unity are values of sections over an affine
  open, so that the condition becomes finitely many evaluation conditions and the finitely many
  possible restrictions partition the trace into closed pieces.
- 2026-08-23 — **Prop 4.5 (`t44n`) closed, and with it all of §4.**  A *functorial* admissible
  class is one stable under precomposition with an arbitrary field homomorphism, not only with an
  isomorphism; a morphism of schemes induces exactly such a homomorphism on residue fields, so no
  hypothesis on the morphism is needed and the statement is strictly more general than Deninger's
  (dominant morphism of integral normal schemes).  The class of all characters witnesses that the
  notion is not vacuous.
- 2026-08-23 — **Prop 7.4(b) (`t10`) closed**: `X̌(C)` carries the finest topology making all the
  structural maps `X̂(C) → X̌(C)` continuous, and `F_ν` is a homeomorphism of it — the inverse sends
  the class of `(μ, P)` to the class of `(μν, P)`, and both directions are compatible with the
  structural maps.  Part (a) still needs the clopen-ness of `F_ν(X̂(C))` from Lemma 7.3, which in
  turn needs Lemma 4.6's description of the image as the characters killing `μ_ν`, i.e. the
  `N₀`-divisibility of the structure sheaf that Deninger's arithmetic-scheme setting supplies.
  Part (c) needs the `G`-action on `X̂(C)` by scheme automorphisms.
- 2026-08-23 — **the global topology on `X̂(C)` is built**, which was the gate on §§3, 5, 6, 7, 9.
  A subset is open exactly when its trace on the points over every affine open is open for
  pointwise convergence there; the projection to `X` is continuous because over an affine open the
  preimage of an open set is the union of the loci where an evaluation is nonzero.  The Frobenius
  operators are continuous.  **Lemma 7.2 (`t8`) is closed in full**: over a basic open `D(s)` of an
  affine open `U` a section is `r / s^n` for some `r ∈ Γ(X, U)`, so the evaluation there is
  `eval U r / (eval U s)^n` — continuous for the topology induced from the trace over `U` — and the
  two topologies therefore agree; the range of the inclusion is the locus `eval U s ≠ 0`, hence
  open, so the trace over any affine open is an open embedding into `X̂(C)`.
- 2026-08-23 — **Cor 7.8 (`t88`) closed** on top of Prop 7.6 and Prop 7.7, stated without
  quotient types: a `G`-invariant subset of `X̂(C)` is open exactly when it contains a `δ`-ball
  around each of its points.
- 2026-08-23 — **Prop 7.6 (`t86`) closed.**  New reusable HTGeometry layer `BlockProductMetric`:
  for a product indexed by a type covered by countably many finite blocks, the block-weighted sum
  of bounded distances is a metric inducing the product topology, weights always exist, index
  permutations preserving the blocks are isometries, and the metric transports along an inducing
  map.  Applied with the blocks the `G`-orbits it gives Deninger's invariant metric.
- 2026-08-23 — **Prop 2.1(b), (c) closed**, so §2's Proposition 2.1 is complete: the sheafification
  `W_rat(𝒪_X)` is realized inside the sheaf `W(𝒪_X)` as the locally rational subpresheaf, the
  comparison `W_rat(𝒪_X) ⟶ W(𝒪_X)` is injective on sections with image exactly that subpresheaf,
  and Deninger's Fatou argument then runs on the ring carriers.
- 2026-08-23 — **Lemma 9.4 (`t13`) closed.**  New reusable HTGeometry layers: the `ℤ`-span of a
  finite subset of a `ℚ`-vector space is free with a `ℚ`-independent basis; a finite family of
  complex numbers perturbs into a `ℚ`-independent one avoiding a prescribed line; a `ℚ`-basis of
  `ℂ` is uncountable, so a countable `ℚ`-vector space embeds `ℚ`-linearly into any basis
  complement.
- 2026-08-22 — created; paper source downloaded, 78-result inventory extracted.
- 2026-08-22 — five results closed in Lean (see Ledger); duplication audit recorded.
- 2026-08-22 — eight results closed; axiom audit clean; next target is Theorem 1.4 (`t27n`).
- 2026-08-22 — Theorem 1.4 (`t27n`) and Lemma 1.6(2)/Cor 1.7(1) closed: ten results.
- 2026-08-22 — reduced monoid algebra representability and Definition 9.5 closed; 13 items in the
  ledger; `formal_tools.py lint` reports no error attributable to these modules.
- 2026-08-22 — **Prop 1.2 closed in full**: the integrally closed domain case of 1.2(b) is proved
  by the source's argument (fraction-field action, coprime invariant presentation, reversal to
  monic, `IsIntegrallyClosed.eq_map_mul_C_of_dvd`), in series, polynomial and ring form.  The
  ring-level descent was refactored to be parametric in the polynomial descent so both cases share
  it.  The big Witt sheaf `W(𝒪_X)` and the subpresheaf embedding are closed.  28 items in the
  ledger; all axiom-clean.
- 2026-08-22 — **§2 opened and Prop 2.1(a) closed**: `W_rat` is now a functor on `CommRingCat`,
  the presheaf `U ↦ W_rat(𝒪_X(U))` is separated (concretely and site-theoretically), its sections
  inject into the sheafification, and the rational Witt space of Def 2.3 is a `SheafedSpace`.
  25 items in the ledger; all axiom-clean.
- 2026-08-22 — Lemma 4.3 closed **in full**: the mixed-characteristic embedding of roots of
  unity is proved by reduction to the residue field of the algebraic integers.  New reusable
  mathlib-gap results: the residue field of `integralClosure ℤ C` at a maximal ideal is
  algebraically closed; roots of unity of order prime to the residue characteristic reduce
  injectively; a unit integral over `ℤ` in characteristic `p` has finite order prime to `p`.
  24 items in the ledger; all axiom-clean.
- 2026-08-22 — **Lemma 4.3 (`t3`) closed**, for an arbitrary field `k` and in full universe
  generality.  Three new modules: the `ℚ`-vector space `(k^×/μ(k)) ⊗ ℚ` built as a divisible hull,
  the dimension theorem `#C ≤ dim_ℚ (C^×/μ(C))`, and the extension theorem itself.  New reusable
  mathlib-gap results: Euclid's argument for the infinitude of monic irreducible polynomials over
  an arbitrary field, and "a unit of a field of characteristic `p` that is not a root of unity is
  transcendental over the prime field".  23 items in the ledger; all axiom-clean.
- 2026-08-22 — the ring-level `W_rat` blocker is resolved: Thm 1.4's second assertion and
  Prop 1.2(a) now hold for `DeningerCanonicalRationalWittRing`.  The inseparability layer
  (`d_r`, `ℤ̲κ/κ₀`, the char-`p` vanishing) is closed.  19 items in the ledger; all axiom-clean.

- 2026-08-23 — **Prop 14.13's correspondence closed in both directions.**  The existence half:
  given a pointed multiplicative `χ : A♭ → 𝒪` whose reduction `χ̄` modulo `p` is a ring
  homomorphism, the perfection lift `χ♭ = lim (χ̄ ∘ Frob^{-n})` satisfies `♯ ∘ χ♭ = χ`.  The proof
  compares the two sides one Frobenius level at a time: the zeroth coefficient of
  `χ♭ (Frob^{-n} x)` is `χ̄ (Frob^{-n} x)`, so `p ∣ ♯(Frob^{-n}(χ♭ x)) − χ(Frob^{-n} x)`, and
  `dvd_sub_pow_of_dvd_sub` raises this to a congruence modulo `p^{n+1}` after taking `p^n`-th
  powers, where `PreTilt.untilt_iterate_frobeniusEquiv_symm_pow` collapses the left side to
  `♯(χ♭ x)` and multiplicativity collapses the right side to `χ x`.  `𝒪` being `p`-adically
  Hausdorff finishes.  Combined with the injectivity already proved this gives
  `deningerTiltChar_exists_iff`, `deningerTiltChar_existsUnique` and its `lim_{()^p} A` form
  `deningerLimChar_existsUnique`.  Trap: `PreTilt O p` and `Perfection (ModP O p) p` are the same
  definition but do not unify through dot notation or through `Perfection.coeff_*` lemmas — fix a
  local `set y : PreTilt O p := …` and state every step with `PreTilt.coeff` / `PreTilt.untilt`
  applied prefix.

- 2026-08-23 — **Proposition 13.4 (`t44`) closed in full**, as two `Equiv`s
  `DeningerValuedCharTriple ≃ DeningerValuedTriple ≃ DeningerValuedLocalTriple`.  Two new reusable
  inputs were needed.  (i) `κ(x) = Frac(𝒪_{closure{x},y})`: an affine open containing `y` contains
  `x` (`Specializes.mem_open`), and `IsAffineOpen.isLocalization_stalk` at `x` writes any germ at
  `x` as `α/σ` with `α, σ` sections over that open, whose germs at `y` are the required numerator
  and denominator — this is `HTGeometry.exists_stalkValue_ratio`, and it gives `IsFractionRing`
  directly without ever constructing the localization map between the two stalks.  (ii) the
  extension of a pointed multiplicative map to the fraction fields, built as
  `Submonoid.LocalizationMap.lift₀` of the *multiplicative monoid* localization — no additivity is
  used anywhere — together with its uniqueness `eq_fractionMulExtend`.
  Traps: the conversion functions between the three triple types must be `@[reducible]`, otherwise
  instance search cannot see that `P.toValuedTriple.specializes` is `P.specializes` and every
  `Algebra`/`IsFractionRing` lookup on `DeningerClosureLocalRing` fails; and the structure
  equalities need hand-written `ext'` lemmas taking `HEq` on the dependent fields, discharged by
  `cases` on the `HEq`s and `rfl` (proof irrelevance handles the `Prop` fields).

## Numbering: this card vs. arXiv v4 (checked 2026-08-23 against the actual PDF)

The PDF of v4 (7 Feb 2024, 119 pp.) is at `https://arxiv.org/pdf/1807.06400v4`; extract it with
`pdftotext -layout`.  v4 contains **103** numbered items, of which the non-Remark, non-Example
results are ~95.  The section table above was built on a numbering that skips the Remarks and is
therefore shifted; the mapping is

| card | v4 | note |
|---|---|---|
| §1: 1.1–1.3 | same | |
| §1: Thm 1.4, Cor 1.5, Lem 1.6, Cor 1.7, Thm 1.8 | Thm 1.5, Cor 1.6, Lem 1.7, Cor 1.8, Thm 1.9 | card omits **Prop 1.4** (the two `ω`-isomorphisms `(ℤκ)^H ≅ W_rat(κ_0^perf)` and `(ℤκ/κ_0)^H ≅ W_rat(κ_0)`), which is what the card's "Prop 1.3 lower row" rows actually prove |
| §2, §4, §6–§13 | same | v4 skips 3.4, 5.4, 14.6, 15.3 as Remarks/Examples |
| §3: Prop 3.4, Def 3.5, Prop 3.6, Cor 3.7 | Prop 3.5, Def 3.6, Prop 3.7, Cor 3.8 | Remark 3.4 |
| §5: Thm 5.4 | Thm 5.5 | Remark 5.4 |
| §14: 14.6 … 14.15 | 14.7 … 14.16 | Remark 14.6 |
| §15: 15.3 … 15.7 | 15.4 … 15.8 | Example 15.3 |

Nothing in v4 is untracked by the ledger: the only apparent omission, Prop 1.4, is the result the
"Prop 1.3 lower row" rows formalize.  **Use v4 numbering from now on.**

- 2026-08-23 — **Proposition 1.1(b) closed in the generality the source states it** (integrally
  closed domain with algebraically closed fraction field, not just a field): the corpus already
  owned the additive bijection `deningerAICRationalWittComparisonEquiv`, so the new work is the
  multiplicativity (the same biadditive argument as over a field, with `Kˣ` replaced by `A⁰`) and
  the Hom description `Hom_ring(W_rat(A), R) ≃ (A →*₀ R)` obtained by composing the `ω`-equivalence
  with `MonoidAlgebra.lift` over `ℤ` and with extension by zero from `A⁰` to `A`.  This is exactly
  the bridge Deninger uses for `(26)` and `(145)` to turn ring homomorphisms out of `W_rat` into
  pointed multiplicative maps, so it unlocks the tuple description of the `𝒪`-valued points.

- 2026-08-23 — **Proposition 13.1's tuple description and Deninger's identification (145) closed.**
  `DeningerWittValuedPoint X 𝒪` carries exactly Deninger's diagram: `f̃_η^♯ : W_rat(κ(x)) → C`,
  `f_s^♯ : W_rat(𝒪_{X,y}) → 𝒪`, `f̃_s^♯ : W_rat(κ(y)) → k` with the two squares.  Over a scheme all
  of whose residue fields are algebraically closed and whose local rings are integrally closed
  domains with algebraically closed fraction field — carried as four `∀ x : X, …` instance binders,
  which Lean accepts and uses through pi-instance search — the Teichmüller comparison turns each of
  the three homomorphisms into a pointed multiplicative map and the diagram into Definition 13.2;
  composing with Prop 13.4 gives the `(x,y,P'_y)` description as well.  The mechanism is that a ring
  homomorphism out of `W_rat` is determined by its values on Teichmüller elements, so each square
  is checked on `[a]` only and then transported by injectivity of the `Hom`-bijection.
  Model for the four hypotheses: `X = Spec K` with `K` algebraically closed (single point, stalk
  and residue field both `K`), and Deninger's own `X`, the integral closure of an integral normal
  scheme in an algebraic closure of its function field.
  **What is left of Prop 13.1** is only the ringed-space half: that a morphism `Spec 𝒪 → W_rat(X)`
  in the sense of Def 2.5 is the same as that diagram.  It needs `Spec 𝒪` for a rank-one valuation
  ring as a two-point space with `Γ(Spec 𝒪, {η}) = C`, and the computation
  `(f^{-1}W_rat(𝒪_X))(S) = W_rat(𝒪_{X,y})`, `(f^{-1}W_rat(𝒪_X))({η}) = W_rat(𝒪_{X,x})`.

- 2026-08-23 — **Corollary 13.5 closed in full.**  Three new layers.  (i) In
  `DeningerDynSysValuedPointsAffine.lean`, the extension `Q_𝔮 : R_𝔮 → 𝒪` is shown to satisfy
  Deninger's conditions 2) and 3): clearing the denominator turns each into condition a') resp. b')
  for `Q`, using `Q(s' a + s a') = Q(s' a)` and the identity `Q(s'a)·(Q(s s'))⁻¹ = Q a·(Q s)⁻¹`.
  (ii) `DeningerDynSysValuedLocalCriterion.lean` proves that Deninger's 1), 2), 3) on a germ map
  are *equivalent* to the four statements (`additiveOnZeros`, `additiveModMax`,
  `P f = 0 ↔ f(x) = 0`, `P f ∈ 𝔪 ↔ f(y) = 0`) — the non-obvious direction is
  `P f ∈ 𝔪 → f(y) = 0`, which uses that `κ(y)` is a field: if `f(y) ≠ 0` pick `g` with
  `(fg)(y) = 1`, then `P f · P g − 1 ∈ 𝔪`, so `P f ∈ 𝔪` would put `1` in `𝔪`.
  (iii) `DeningerDynSysSpecStalkDictionary.lean` is the `Spec R` dictionary:
  `StructureSheaf.toStalk_stalkSpecializes` gives that the specialisation map is the identity on
  the image of `R`, so evaluation of `germ_y(a)` at `x` is the residue of `a` at `x`, whose kernel
  is `x.asIdeal` by `IsLocalization.AtPrime.under_maximalIdeal`.
  The bijection is then assembled; its surjectivity avoids all `HEq` gymnastics via
  `eq_of_restrict_eq`: destructure both triples so the point equalities are between *variables*,
  `cases` them, and compare the two germ maps on `f = r/t` using that `P(germ t)` is a unit.
  Trap: work with `R : CommRingCat`, never `R : Type _` with `[CommRing R]` — otherwise
  `PrimeSpectrum ↑(CommRingCat.of R)` and `PrimeSpectrum R` fail to unify at `instances`
  transparency and every `rw` on a `Spec` goal dies.

- 2026-08-23 — **The `p`-adic layer of §14 is unblocked.**  Four new reusable modules.
  (i) `AdicCompletionTopology.lean` puts the projective limit topology on `AdicCompletion I R`
  (induced from the product of the *discrete* quotients, carried by a type synonym `AdicQuot` so no
  discrete-topology instance leaks onto `R ⧸ Iⁿ`), proves `ContinuousMul`, and proves that
  `R → R̂` has dense image: a neighbourhood constrains finitely many coordinates and a lift of the
  largest constrained one reduces correctly in all smaller ones.  Feeding this into the corpus's
  abstract Prop 14.8(a) gives the concrete density of `lim_{()^p} A` in `lim_{()^p} Â`.
  (ii) `PerfectionMonoidWithZero.lean`: `lim_{()^p} M` is a `CommMonoidWithZero`, has
  `NoZeroDivisors` when `M` does (an entry is a `p^k`-th power of every later entry, so one
  vanishing entry kills the sequence), and is a `CommGroupWithZero` when `M` is.  This is what makes
  Deninger's `lim_{()^p} κ(x)` a field-like object even though `κ(x)` need not have characteristic
  `p`, so no ring structure is available.
  (iii) `GroupWithZeroMultiplicativeExtension.lean`: for commutative groups with zero, pointed
  multiplicative maps are unit-group characters; and a pointed multiplicative map `P : D → L`
  vanishing only at `0` extends **uniquely** to any `K` in which every element is a ratio
  `ι f / ι s` — the addition-free replacement for `fractionMulExtend`, which is what Deninger's
  Prop 14.11 needs since `lim_{()^p}` of a ring is only a monoid.
  Trap: `ring`/`field_simp` are unavailable in a `CommGroupWithZero`; use `mul_right_comm`,
  `mul_mul_mul_comm`, `div_eq_div_iff` and `eq_div_iff` instead.

- 2026-08-23 — **Definition 14.9 and Proposition 14.11 closed.**  `DeningerCompletedCharTriple`
  carries Deninger's diagram (177) — a character of `(lim_{()^p} κ(x))ˣ`, a *continuous* pointed
  multiplicative `P̂_y` on `lim_{()^p} Ô_{closure{x},y}`, a `P̃_y` on `lim_{()^p} κ(y)`, and the two
  squares — and `DeningerCompletedHatTriple` carries `P̂_y` with conditions 1) and 2).  The forward
  map reads 1) off the lower square (evaluation at `x` is injective on perfections, so a nonzero
  `f` has nonzero image and the extension by zero of a character is nonzero there) and 2) off the
  upper square.  The inverse rebuilds `P^×` by the addition-free unique extension
  `gwzRatioExtend` along the ratio presentation, and `P̃_y` by choice along the surjectivity of
  evaluation at `y`; both round trips then follow from the *uniqueness* halves.  The two
  hypotheses are exactly Deninger's Prop 14.8(b),(c) and are carried as explicit `∀ a b (h : a ⤳ b)`
  hypotheses; `DeningerDynSysCompletedTripleSpec.lean` shows they hold on a one-point scheme (at a
  point specialising to itself the local ring of the closure *is* the residue field, so both
  evaluations are bijective), so the equivalence is not vacuous.
  **§14 now has only Prop 14.16 open**, and that is 14.11 plus the tilting correspondence 14.14,
  both of which are closed.

- 2026-08-23 — **Proposition 14.16's identification closed.**  Reduction modulo `p` of a pointed
  multiplicative map is automatically multiplicative and pointed, so it is a *ring* homomorphism
  exactly when the map is additive modulo `p`; feeding that into Prop 14.14 gives
  `deningerTiltChar_exists_iff_additiveModP`, and packaging it with the injectivity half gives
  `deningerTiltCharAdditiveEquiv`: homomorphisms of tilts `A♭ → 𝒪♭` **are** the points of `Y^⋄`.
  Two mathlib gaps were needed on the way.  `untilt 0 = 0` for any `p`-adically complete ring:
  `untilt 0` is its own `p^n`-th power (because `Frob^{-n} 0 = 0`) and lies in `(p)`, hence in
  `(p)^{p^n} ⊆ (p)^n` for every `n`, and the ring is separated.  And `untilt x = 0 ↔ x = 0` over a
  *reduced* ring: the `n`-th Frobenius root has `p^n`-th power equal to `untilt x`, so it is
  nilpotent, hence `0`, and its class mod `p` is the `n`-th coefficient of `x`.  That second lemma
  is exactly Deninger's `♯⁻¹(0) = 0`, which matches the two nonvanishing conditions of Prop 14.16.
  **What is left of 14.16** is only the clause that `P̂_y^♭` is a *local* homomorphism; that is not
  formal — it needs Deninger's diagrams (177)/(179), i.e. that the reduction `Ô/p → 𝒪/p` induced by
  `P̂_y` is local, which comes from `P̃_y` being nonzero off `0` on the field `κ(y)`.

- 2026-08-23 — **Prop 13.1's geometric groundwork closed.**  `SpecDimOneLocalDomain.lean` proves
  that for a local domain in which every prime is `(0)` or `𝔪` and which is not a field, the prime
  spectrum is exactly `{η, s}`, that `{η}` is `D(f)` for any nonzero `f ∈ 𝔪` and hence open, that
  every nonempty open contains `η`, and that the only opens are `∅`, `{η}` and `⊤`.  Note the
  argument needs **only dimension ≤ 1**, not rank one: `Γ(Spec 𝒪, {η})` is a localization of `𝒪`
  whose only prime is `(0)`, hence a field, hence `Frac 𝒪`.  `SpecStalkLocalization.lean` gains the
  two stalk identifications `𝒪 ≃ 𝒪_{Spec 𝒪, s}` (localizing at the complement of `𝔪` in a local
  ring does nothing) and `Frac 𝒪 ≃ 𝒪_{Spec 𝒪, η}`.
  **What is left of Prop 13.1** is the ringed-space construction itself: a morphism
  `sheafMap : W_rat(𝒪_X) ⟶ base_* 𝒪_S` is, by the three-open case split
  (`y ∈ U` / `x ∈ U ∧ y ∉ U` / `x ∉ U`), exactly the commuting square (139); building it in Lean
  means defining a natural transformation whose `app` is given by that case split and checking
  naturality in nine cases.
- 2026-08-23 — **Correction to the ledger.**  Cor 1.6(1)'s injectivity-modulo-`H` is *not* blocked
  on new algebra: `deningerHom_exists_smul` (the transitivity half of Kucharczyk–Scholze Lemma 4.9)
  is already closed in `DeningerDynSysInvariantPoints.lean`, and `deningerInsepSubring_restrict_bijective`
  reduces the statement to it with `B = ℤ̲κ/κ₀`, `G = H`.  The *only* missing input is topological:
  `deningerHom_exists_smul` needs `H = Aut_F(E)` compact, and mathlib supplies `CompactSpace (E ≃ₐ[F] E)`
  only under `IsGalois F E`, which fails for an algebraic closure in characteristic `p`.  The fix is
  the group isomorphism `Aut_F(E) ≅ Gal(F^sep/F)` — surjectivity is
  `AlgEquiv.restrictNormalHom_surjective`, injectivity is that `E / F^sep` is purely inseparable —
  followed by transporting the profinite topology and checking `ContinuousSMul` on `ℤ̲κ/κ₀`
  (stabilisers are open because an element involves finitely many units).

- 2026-08-23 — **Corollary 1.5(1)'s injectivity-modulo-`H` closed**, and with it Cor 1.5(1) in
  full for a Galois extension (so always in characteristic zero).  The earlier note that this was
  blocked on new algebra was wrong: `deningerHom_exists_smul` — the transitivity half of
  Kucharczyk–Scholze Lemma 4.9 — was already closed, and what was missing was only its topological
  hypotheses.  Those are now supplied: a class in `ℤ̲κ` involves finitely many units, so it is
  fixed by the fixing subgroup of the finite subextension they generate, which is open for the
  Krull topology (`IntermediateField.fixingSubgroup_isOpen`); hence stabilizers are open, and
  `HTGeometry.continuousSMul_of_isOpen_stabilizer` (an action with open stabilizers on a discrete
  space is continuous — the preimage of a point is a union of cosets of stabilizers) gives
  `ContinuousSMul`.  The remaining `Algebra.IsInvariant` instance is exactly Prop 1.3's lower row
  `deningerOmega_mem_image_iff`, already closed.
  The **only** residual hypothesis is `CompactSpace Gal(E/F)`, which mathlib supplies from
  `IsGalois F E`.  For an algebraic closure in characteristic `p` that instance is missing, and
  supplying it is a clean mathlib gap: `Aut_F(E) ≅ Gal(F^sep/F)` (surjectivity is
  `AlgEquiv.restrictNormalHom_surjective`, injectivity is pure inseparability of `E/F^sep`), then
  transport compactness — or show the restriction map is a continuous bijection from a compact
  group to the Hausdorff `Gal(E/F)`.

- 2026-08-23 — **The algebraic half of the `CompactSpace Gal(E/F)` gate is closed.**
  `restrictNormalMulEquiv` is the group isomorphism `Aut_F(E) ≅ Gal(F^sep/F)` for a normal
  extension: surjectivity is `AlgEquiv.restrictNormalHom_surjective`, and injectivity is
  `algEquiv_eq_one_of_fixes_separableClosure` — an automorphism fixing `F^sep` pointwise satisfies
  `σ(a)^{q^n} = σ(a^{q^n}) = a^{q^n}` for the `n` given by pure inseparability, and
  `iterateFrobenius E q n` is a ring homomorphism out of a field, hence injective.
  **What is left** is the topological half: the inverse of that isomorphism is continuous, whence
  `Gal(E/F)` is the continuous image of a compact group.  The concrete route (no basis needed):
  a finite-dimensional `K ⊆ E` is `adjoin F t` for a finite `t` (`IntermediateField.fg_of_fg_toSubalgebra`
  ∘ `Subalgebra.fg_of_submodule_fg`), each `x ∈ t` has `x^{q^{n_x}} ∈ F^sep`, and the fixing
  subgroup in `Gal(F^sep/F)` of the finite-dimensional field these powers generate maps into
  `K.fixingSubgroup` — by `IntermediateField.forall_mem_adjoin_smul_eq_self_iff` it is enough to
  fix the generators.  Then `krullTopology_mem_nhds_one_iff` and `continuous_of_continuousAt_one`
  finish.  Closing this makes Cor 1.5(1) unconditional in every characteristic.

- 2026-08-23 — **`CompactSpace Gal(E/F)` closed for every normal algebraic extension, and with it
  Corollary 1.5(1) unconditionally.**  `continuous_restrictNormalMulEquiv_symm` proves that the
  inverse of `Aut_F(E) ≅ Gal(F^sep/F)` is continuous, so `Aut_F(E)` is the continuous image of a
  compact group and `compactSpace_algEquiv_of_normal` follows; this is registered as an instance
  and strictly generalises mathlib's `IsGalois` version.
  The continuity argument, at the identity: a basic neighbourhood of `1` in `Aut_F(E)` contains
  `K.fixingSubgroup` for some finite-dimensional `K` (`krullTopology_mem_nhds_one_iff`).  Such a
  `K` is `adjoin F t` for a finite `t`: `Subalgebra.fg_iff_finiteType` turns
  `Module.Finite F K` into `Subalgebra.FG K.toSubalgebra`, and
  `IntermediateField.fg_of_fg_toSubalgebra` transfers it — note that
  `Subalgebra.fg_of_submodule_fg` does **not** apply here, it is stated only for `⊤`.
  Pure inseparability of `E/F^sep` gives, for each `x`, an `n_x` and a `b_x ∈ F^sep` with
  `b_x = x^{q^{n_x}}`; `adjoin F {b_x : x ∈ t}` is a finite-dimensional subextension of `F^sep`,
  and any `τ` fixing it pointwise lifts to a `σ` with `σ(x)^{q^{n_x}} = σ(x^{q^{n_x}}) = x^{q^{n_x}}`
  by `AlgEquiv.restrictNormal_commutes`, hence `σ(x) = x` since `iterateFrobenius E q n` is
  injective.  `IntermediateField.adjoin_induction` propagates this from `t` to `K`, so
  `σ ∈ K.fixingSubgroup`.  `continuous_of_continuousAt_one` then upgrades continuity at `1` to
  continuity.
  Consequence: `deningerCor15_injective` no longer carries `[CompactSpace (E ≃ₐ[F] E)]`, the
  `IsGalois` convenience variant is deleted, and Cor 1.5(1) holds for the algebraic closure of an
  arbitrary field.  Axiom audit: `[propext, Classical.choice, Quot.sound]`.

- 2026-08-23 — **Proposition 14.16 is closed in full: the locality clause is proved.**
  The clause splits into an algebraic and a topological half.
  *Algebra* (`DeningerDynSysTiltLocalHom.lean`).  `ModP R p = R / p` is local whenever `R` is and
  `p` is a non-unit (a surjection from a local ring onto a nontrivial ring), and reduction mod `p`
  reflects the maximal ideal because it is a surjection of local rings.  `PreTilt R p` is then
  local by `deningerPerfection_isLocalRing`, and an element lies in its maximal ideal exactly when
  its zeroth coefficient does.  Since the zeroth coefficient of `χ^♭ x` is the reduction of
  `χ x = ♯(χ^♭ x)` modulo `p` (`deningerTiltChar_reduction`), the local-hom criterion
  `f '' 𝔪 ⊆ 𝔪` of `IsLocalRing.local_hom_TFAE` becomes exactly `χ (𝔪^♭) ⊆ 𝔪_𝒪`.  Both the
  `A♭`-form and the `lim_{()^p} A`-form are recorded.
  *Topology* (`DeningerDynSysHatLocality.lean`).  This is Deninger's right square of (179).  The
  residue map of a local ring is continuous for the discrete topology on the residue field as soon
  as the cosets of the maximal ideal are open, so `residue ∘ P̂_y` and `P̃_y ∘ residue ∘ pr_0` are
  two continuous maps `lim_{()^p} Â → k`; they agree on the dense image of `lim_{()^p} A`
  (Prop 14.8(a)), hence everywhere by `deningerPerfection_ext_of_dense`.  An element of the maximal
  ideal has residue `0`, and `P̃_y (0) = 0`, so its image lies in `𝔪_𝒪`.
  The two openness hypotheses are not vacuous: `HTGeometry.isOpen_maximalIdeal_coset_adicCompletion`
  discharges the one for `Â` (the projection `Â ↠ A/I` factors through the first coordinate, which
  is continuous with discrete target, and its kernel consists of non-units), and
  `HTGeometry.isOpen_maximalIdeal_coset_of_span` discharges the one for a `𝒪` carrying the `p`-adic
  topology.  Axiom audit on all six new theorems: `[propext, Classical.choice, Quot.sound]`.
  **§14 is now closed in full.**

- 2026-08-23 — **Proposition 2.4 closed at the level of schemes, and the mathlib gap behind it.**
  `HTGeometry.scheme_hom_ext_of_stalkMap` proves that a morphism of schemes is determined by its
  underlying continuous map together with its stalk maps.  The route avoids all `eqToHom`
  transport: the *targets* of `f.stalkMap x` and `g.stalkMap x` are both `𝒪_{X,x}`, so the
  hypothesis can be stated on germs, `f.stalkMap x (germ_U (f x) s) = g.stalkMap x (germ_U (g x) s)`,
  with no dependent rewriting.  The proof feeds `Scheme.Hom.ext` with `Presheaf.section_ext` and
  `germ_stalkMap_apply`; the one trap is that `X.sheaf.presheaf` and `X.presheaf` live over
  syntactically different spaces, so `section_ext` has to be wrapped once
  (`HTGeometry.scheme_section_ext`) before mathlib's germ simp-set will fire.
  Deninger's Proposition 2.4 then follows exactly as in the source: naturality of the Teichmüller
  map turns the hypothesis `W_rat (α^♯_y) = W_rat (β^♯_y)` on Teichmüller germs into
  `[α^♯_y (s)] = [β^♯_y (s)]`, and the Teichmüller map is injective.  What is *not* yet built is
  the ringed-space packaging `α ↦ W_rat (α)` as a `DeningerWittSpaceMorphism`: the sheaf component
  is `sheafifyLift` of `whiskerRight α.c W_rat ≫ pushforward (toSheafify)` (the pushforward of a
  sheaf being a sheaf), but its `stalkHom_comp` field is a naturality chase through
  `deningerWittStalkToStalk`.  Axiom audit: `[propext, Classical.choice, Quot.sound]`.

- 2026-08-23 — **Proposition 1.4, Corollary 3.1 (24) and Lemma 5.3 closed.**
  *Prop 1.4.*  The card's roadmap entry claiming a residual step (e) of "Prop 1.3's lower row" was
  stale: `deningerOmega_mem_image_iff` already is the lower isomorphism.  What was missing was only
  the packaging, now `deningerWittInsepInvariantsEquiv : W_rat (κ₀) ≃+* (ℤ̲κ / κ₀)^H`.  The
  invariant subring is built by hand as a `Subring` with carrier `{x | ∀ σ, σ • x = x}` — using
  `FixedPoints.subring` on the nested subtype is what blew the heartbeat budget in the earlier
  attempt.
  *Cor 3.1 (24).*  A character `f` of `κˣ` induces `W_rat (κ₀) → C` by
  `deningerCharToMonoidAlgebra f ∘ deningerWittToMonoidAlgebra`.  Surjectivity is
  `deningerCor15_surjective` verbatim.  For the fibres: relabelling a character by `σ` composes the
  ring homomorphism with the atom relabelling (`deningerCharToMonoidAlgebra_comp`), and the image of
  `W_rat (κ₀)` in `ℤ̲κ` is `H`-invariant, so conjugate characters induce the same homomorphism;
  conversely `deningerCor15_injective` produces the `σ`, and
  `deningerInsepSubring_restrict_injective` lifts the resulting agreement from `ℤ̲κ / κ₀` to all of
  `ℤ̲κ`, whence the characters agree.  Since Cor 1.6 is now unconditional, so is this.
  *Lem 5.3.*  Fully elementary and formalized in the generality it needs: an abelian group `G`
  with an automorphism `σ`.  Part one is Euler's theorem — `ζ^{ν^i} = ζ^{ν'^i}` for some `i ≥ 1`
  iff `orderOf ζ` is prime to `νν'`, taking `i = φ (orderOf ζ)` for the hard direction.  Part two
  is Deninger's group-ring identity `ν^i − ν'^i σ^i = ω (ν − ν' σ)` with
  `ω = Σ_{α<i} ν^{i-1-α} ν'^α σ^α`; in Lean it is a **telescoping product**: with
  `g β = (σ^β z)^{ν^{i-β} ν'^β}` one has `y^ν = ∏_{β<i} g β` and `σ (y)^{ν'} = ∏_{1 ≤ β ≤ i} g β`,
  so the twisted norm of `y = z^ω` is `g 0 / g i = z^{ν^i} σ^i (z)^{-ν'^i}`.  The divisibility
  hypothesis is discharged for `κˣ` with `κ` algebraically closed (`deningerUnits_divisible`).
  Axiom audit on all of these: `[propext, Classical.choice, Quot.sound]`.

- 2026-08-23 — **Corollary 3.1 (25) closed, so §3's Corollary 3.1 is complete.**  The content is a
  clean mathlib gap, isolated in `HTGeometry/RadicialCharacterExtension.lean`: for an injective
  homomorphism `ι : A → B` of commutative groups such that every `b ∈ B` has `b^{q^n} ∈ ι (A)`,
  restriction along `ι` is a bijection on homomorphisms into any commutative group `C` whose
  `q`-th power map is bijective.  Injectivity is immediate; for surjectivity the extension is
  `f (b) = (g (a))^{1/q^n}` for any witness `(n, a)`, and well-definedness is the comparison of two
  witnesses at the larger exponent, which needs `ι` injective.  Multiplicativity is proved by
  raising both witnesses to a common exponent — the reason the construction uses `MonoidHom.mk'`
  and a `max` of three levels.
  Instantiated at `A = (κ₀^sep)ˣ ⊂ B = κˣ` this is (25): pure inseparability supplies the
  witnesses, and `c ↦ c^q` is bijective on `Cˣ` for `C` algebraically closed of exponential
  characteristic `q` (injective because it is the Frobenius of a field, surjective because `C` is
  algebraically closed).  Galois equivariance is `AlgEquiv.restrictNormal_commutes`, so the fibres
  of (24) and (25) match and (25) follows from (24) formally.
  Axiom audit: `[propext, Classical.choice, Quot.sound]`.

- 2026-08-23 — **The section layer for Prop 13.1's ringed-space half is built.**  Two bricks:
  a general mathlib gap — a point with a smallest open neighbourhood `V` has `Γ (F , V) ≅ F_x`,
  because `⟨V, hx⟩` is initial in `OpenNhds x` and hence `op ⟨V, hx⟩` is terminal in the category
  the stalk colimit is taken over (`isIso_ι_of_isTerminal`) — and its application to
  `Spec 𝒪` for a one-dimensional local domain, which identifies all three section rings:
  `Γ (S , ∅) = 0` (mathlib's `Subsingleton Γ(X, ⊥)`), `Γ (S , {η}) ≅ Frac 𝒪` (the new gap plus the
  generic stalk computation) and `Γ (S , ⊤) ≅ 𝒪` (`Scheme.ΓSpecIso`).  The membership criteria
  `s ∈ V ↔ V = ⊤` and `η ∈ V ↔ V ≠ ⊥` turn the case split on `f^{-1} U` into the case split on
  whether `y ∈ U`, `x ∈ U ∧ y ∉ U`, or `x ∉ U`.
  **What is left of Prop 13.1** is the natural transformation itself: `γ.app U` is `f_s` after the
  germ at `y` in the first case, `f_η` after the germ at `x` in the second, and the unique map into
  the zero ring in the third; `sheafifyLift` then gives `sheafMap`, since the pushforward of a
  sheaf is a sheaf.  Naturality has nine cases of which six are trivial (the target is the zero
  ring, or the two opens fall in the same case and germ compatibility applies); the one case with
  content is `y ∉ U`, `y ∈ V`, which is exactly Deninger's square (139).

- 2026-08-23 — **Proposition 13.1's sheaf morphism is built.**  `deningerTwoPointGamma` is the
  natural transformation `W_rat (𝒪_X) ⟶ f_* 𝒪_S` of diagram (139) and
  `deningerTwoPointSheafMap` is its extension over the sheafification (`sheafifyLift`, the direct
  image of a sheaf being a sheaf).
  Two design choices made this tractable.  First, the tuple carries `f_s` with values in
  `Γ (S , ⊤)` and `f_η` with values in `Γ (S , V)` rather than in `𝒪` and `C`; the identifications
  `Γ (S , ⊤) ≅ 𝒪` and `Γ (S , {η}) ≅ Frac 𝒪` are then a separate, already-closed layer, and every
  component of `γ` is a *restriction map* `Γ (S , W) ⟶ Γ (S , f^{-1} U)` — so the construction uses
  no `eqToHom` at all, and naturality is functoriality of the presheaf on a poset plus
  `Subsingleton.elim` on the hom-sets.  Second, the statement is made for plain
  `TopCat.Presheaf`es rather than for `Scheme.presheaf`, because `rw` cannot build motives through
  `Scheme.presheaf`'s type; where that is unavoidable, `set_option backward.isDefEq.respectTransparency false`
  is the switch that makes rewriting go through (the corpus already used it in
  `DeningerSkyscraperComparison`).
  The one case of naturality with content is `y ∉ U`, `y ∈ V`, and it is exactly diagram (139):
  `germ_x = germ_y ≫ stalkSpecializes`, then the hypothesis.
  Axiom audit on all of these: `[propext, Classical.choice, Quot.sound]`.
  **What is left of Prop 13.1** is only the bijection statement: reading the tuple back off a
  morphism (the stalk maps of `sheafMap` at `η` and `s`) and the round trips.

- 2026-08-23 — **`W_rat` commutes with stalks — the brick §2 and §13 were waiting for.**
  `deningerWittStalkToStalk_isIso` and its sheaf-level companion
  `deningerWittSheafStalkToStalk_isIso` close the comparison that Deninger uses implicitly when he
  computes `F (S) = colim_{U ∋ y} W_rat (𝒪_X) (U) = W_rat (𝒪_{X,y})` in §13 and that Def 2.5 needs
  to be written literally.  It is exactly the "a rational Witt vector has finitely many
  coefficients" argument: every element is a normalised fraction `P / Q`
  (`deningerCanonicalRationalWitt_eq_normalizedFraction`), its finitely many coefficients lift to a
  common neighbourhood, and after one more shrinking the constant terms are literally `1`; and a
  normalised fraction vanishes exactly when `P = Q`
  (`deningerCanonicalRationalWittNormalizedFraction_eq_zero_iff`, already in the corpus), which is
  finitely many equalities of germs.
  The reusable half is `HTGeometry/GermPolynomialLift.lean`: germ lifting for a finite family, for
  a polynomial, for a *normalised* polynomial, and the converse shrinking lemma.
  Two corpus lemmas that a first pass duplicated — `deningerRationalWittDenominators_le_nonZeroDivisors`
  and `deningerCanonicalRationalWittNormalizedFraction_eq_zero_iff` — were already there; the
  search tool finds them under "denominators non zero divisors" and "normalized fraction equals
  zero iff".  Search before building.
  Axiom audit: `[propext, Classical.choice, Quot.sound]`.

- 2026-08-23 — **Proposition 13.1's stalk computations closed**, so the tuple and the morphism
  determine each other.  `deningerTwoPointGamma_stalk_closed` and
  `deningerTwoPointGamma_stalk_generic` compute the two stalks of the sheaf morphism.  Both are
  `Presheaf.stalk_hom_ext` on germs: `stalkFunctor_map_germ` turns the germ of the stalk map into
  the component `γ.app U`, `stalkPushforward_germ` turns the pushforward part into the germ over
  `f^{-1} U`, and `deningerWittStalkToStalk_germ` does the same on the other side.  In the closed
  case all three components of the case split are irrelevant because `y ∈ U`; in the generic case
  the branch `y ∈ U` is exactly diagram (139) once more, via `germ_stalkSpecializes` and the
  hypothesis.
  With `W_rat` commuting with stalks, this says: a morphism `Spec 𝒪 → W_rat (X)` in the sense of
  Def 2.5 gives back `f_s` and `f_η`, and the morphism built from a tuple gives back the tuple it
  was built from.  What is left to write is the packaging as a literal `DeningerWittScheme`
  (its `local'` field, and the `Spec 𝒪` instantiation of `Vgen = {η}`, `hgen`, `hbot`, `hterm`,
  all of which are already proved).
  Axiom audit: `[propext, Classical.choice, Quot.sound]`.

- 2026-08-23 — **Proposition 13.1 is closed in full.**  `deningerProp131WittScheme` builds the
  `DeningerWittScheme (Spec 𝒪) X` — Deninger's morphism `Spec 𝒪 → W_rat (X)` — out of the pair of
  stalk maps, the square (139) and the locality data (140), and
  `deningerProp131StalkHom_closed` / `_generic` recover `f_s` and `f_η` from it.
  The construction is uniform in the point: `stalkHom p` is *defined* as
  `inv (W_rat-stalk comparison) ≫ stalk of the sheaf map ≫ stalkPushforward`, which makes the
  `stalkHom_comp` field `IsIso.hom_inv_id_assoc` and avoids every `eqToHom`.  That is only legal
  because `W_rat` commutes with stalks — so Def 2.5's last two fields are in fact determined by
  the sheaf morphism.  The `local'` field is the one place where the two points are separated, and
  there `p` is a bound variable, so `rcases` + `subst` on `spec_eq_generic_or_closed` puts
  `base p` in the right form with no transport.
  `HTGeometry/SpecTwoPointBase.lean` gains `specBase_hgen`, `specBase_hbot`, `specBase_hspec`, so
  the hypothesis package is discharged for the concrete two-point base map of a specialisation.
  Axiom audit: `[propext, Classical.choice, Quot.sound]`.

- 2026-08-23 — **Proposition 3.5 closed in the affine case, at the level of schemes.**  The ring
  statement was already in the corpus (`deningerHom_restrict_surjective` and
  `deningerHom_restrict_eq_iff` — Kucharczyk–Scholze Lemma 4.9); what is new is the translation
  through `Spec.preimage` / `Spec.map_preimage` / `Spec.map_injective`, which turns
  `Hom (Spec C , Spec B) → Hom (Spec C , Spec A)` into `Hom (B , C) → Hom (A , C)` and so gives
  `X (C) / G = X₀ (C)` for `X₀ = Spec A`, `X = Spec B`.  This is exactly the case Deninger's proof
  reduces to.
  **Route for the general case.**  mathlib has *relative normalization of schemes*:
  `AlgebraicGeometry.Scheme.Hom.normalization` for a qcqs `f : X ⟶ Y`, with `fromNormalization`
  integral and `normalizationObjIso` computing `Γ (f.normalization , U) = integralClosure Γ(Y,U) Γ(X, f⁻¹U)`
  on affine opens.  Deninger's `X` is `f.normalization` for `f : Spec K ⟶ X₀`.  What the general
  Prop 3.5 then needs on top of the affine case is (i) `Algebra.IsInvariant Γ(X₀,U₀) Γ(X,π⁻¹U₀) G`
  on each affine open and (ii) the covering step: a `C`-point of `X₀` has a single point as image,
  so it factors through any affine open containing it (`IsOpenImmersion.lift`).

- 2026-08-23 — **Deninger's `ρ` and its Frobenius law (41)–(43) closed.**  `ρ (P)` is the order of
  the torsion part of `ker P`, and the content of (42) is that the `ν`-th power map
  `(ker (P ∘ ( )^ν))_tors → (ker P)_tors` is *surjective* — because an algebraically closed field
  has `ν`-th roots and a root of a torsion element is torsion — with kernel `μ_ν (κ)`.  The order
  formula is then `Subgroup.card_eq_card_quotient_mul_card_subgroup` plus
  `QuotientGroup.quotientKerEquivOfSurjective`, and the corpus's
  `deningerCard_rootsOfUnity_charP` / `_charZero` evaluate `#μ_ν (κ)` as `ordCompl[p] ν` resp. `ν`.
  Both characteristics are recorded separately, matching Deninger's `ν_x`.
  Axiom audit: `[propext, Classical.choice, Quot.sound]`.

- 2026-08-23 — **Proposition 3.5's covering step and Corollary 3.3's formal content closed.**
  *Covering step.*  `deningerSchemePoint_surjective`: `Spec C` has one point, so a `C`-point of the
  base factors through any affine open containing its image (`IsOpenImmersion.lift` on
  `hU₀.fromSpec`, whose range is `U₀`).  The lifted ring homomorphism is turned back into a
  `C`-point of the total space by `IsAffineOpen.SpecMap_appLE_fromSpec`, the naturality
  `Spec.map (f.appLE U V i) ≫ hU.fromSpec = hV.fromSpec ≫ f`.  So the affine case of Prop 3.5,
  which is Kucharczyk–Scholze 4.9, globalises with no further input.
  *Cor 3.3.*  Deninger says the second assertion "follows formally"; the formal content is
  `orbitQuotientQuotientEquiv`: for a **normal** subgroup `N ≤ G` acting on a set `S`, `G` acts on
  the `N`-orbit space (well defined exactly by normality) and its orbits there are the `G`-orbits
  on `S`.  Since the `G`-action factors through `G / N`, this is `(S/N)/(G/N) = S/G`.
  Axiom audit: `[propext, Classical.choice, Quot.sound]`.
