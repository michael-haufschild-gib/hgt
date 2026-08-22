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
| Prop 1.2(b) (`t21n`) field case of Galois descent | `RHTower/DeningerDynSysWittGaloisField.lean` | closed |
| **Prop 1.2(b) (`t21n`) integrally closed domain case** — Prop 1.2 is now closed in full | `RHTower/DeningerDynSysWittGaloisIntegrallyClosed.lean` | closed |
| Prop 14.7(c) (`t125`) perfection surjects along a quotient | `RHTower/DeningerDynSysPerfectionLocal.lean` | closed |
| Prop 14.14(2) (`t1213`) locality of the tilt | `RHTower/DeningerDynSysPerfectionLocal.lean` | closed |

| Thm 1.4 (`t27n`) = Kucharczyk–Scholze Lemma 4.9 | `RHTower/DeningerDynSysInvariantPoints.lean` | closed |
| Lemma 1.6(2) (`t212n`), Cor 1.7(1) (`t213n`) | `RHTower/DeningerDynSysValuedPoints.lean` | closed |
| §1 `Hom(ℤ̲A, R) ≅ (A →*₀ R)` | `RHTower/DeningerDynSysReducedMonoidAlgebra.lean` | closed |
| Def 9.5 (`t95n`) + its two stated facts | `HTGeometry/AlmostPathConnected.lean` | closed |
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
3. **Prop 2.1(b), (c).**  Fatou input is owned (`deningerRationalWittFatouIntersection_iff`); what
   is missing is the scheme layer: integral scheme, function field `K = 𝒪_{X,η}`, injectivity of
   `𝒪_X(U) → K`, and affine covers by Fatou rings.  `W(𝒪_X)` is now a sheaf
   (`deningerBigWittPresheaf_isSheaf`), which is the ambient sheaf in (c).
4. **Def 2.4 / Prop 2.4 (`t27xn`).**  Needs stalks of `W_rat(𝒪_X)` and the locality condition.
5. **§§3, 5, 6, 7, 9–13, 15** are gated on the `S`-valued points of `W_rat(X)`.  The algebraic
   core of Cor 13.5 (`t45`) — the description of those points over an affine base as pointed
   multiplicative maps `Q : R → 𝒪` with a')/b') — is closed; the extension `Q_𝔮 : R_𝔮 → 𝒪` and its two
   preimages are closed too; what remains there is only the scheme-level bookkeeping of the pair of
   points `y ∈ closure {x}` and the identification with `Hom(W_rat(𝒪_{X,y}), 𝒪)`.
6. **§14 remainder.**  14.13 (`t1110`) is pure algebra (the tilting correspondence for
   `p`-adically complete rings, via `PreTilt`/`fontaineTheta`); the rest needs the `𝒪`-valued
   point spaces.
7. **Claim 8.1 is open in the source**; Thm 8.2 stays conditional in dimension ≥ 2.

## Gates
- [x] 0 → 1  in-progress
- [ ] 1 → 2  paper proofs read and dependency-closed per item
- [ ] 2 → 3  Lean theorems, `lake build` green per module, axiom audit PASS

## Log
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
