/-
# The Kummer-extension deck — the non-circular algebraic close for `hDisc`

The disconnected-case monodromy automorphism `σ_n` is realized as the **Kummer/Galois automorphism**
of a radical extension of the *committed* base function field `B = meroField(Ext)` (which is already a
field, `Ext` connected), NOT over `ℂ(z)`:

  `M = B[w]/(wⁿ − a) = AdjoinRoot (Xⁿ − C a)`,  `σ : w ↦ ζ·w`,  `n = 2ᵏ`.

The key point (resolving the circularity flagged in `DeckAutomorphism.lean`): `σ` fixes `φ_{c₂}`
because `φ_{c₂} ∈ B` and `σ` fixes the whole base `B` **by Galois theory** (Kummer), not by declaring
independence. `w = φ_{c₁}` being algebraic over the large field `B` is fully consistent with
`NoRelation` over the small field `ℂ(z)` — the obstruction only uses that `σ` fixes `ℂ(z)` and
`φ_{c₂}` and scales `φ_{c₁}`.

"`M` is a field" ⟺ `Xⁿ − a` irreducible over `B` (Capelli) — the algebraic replacement for
"`commonPullback` is connected in ℂ³". The only analytic input is the germ-level radical relation
`(φ_{c₁}∘π)^{2ⁿ} = a` and `σ(φ_{c₁}∘π) = ζ·(φ_{c₁}∘π)` (the project's `deckGermEquiv_v1`).

This file builds the abstract algebraic core; the analytic instantiation (naming `a`, irreducibility,
the descent `π*`) is layered on top.
-/
import Mathlib.FieldTheory.KummerExtension
import Mathlib.Tactic
import GaloisForLFunctions.Bottcher.AlgIndep
import GaloisForLFunctions.Bottcher.Q62
import GaloisForLFunctions.Bottcher.MonodromyObstruction

open Polynomial Function

namespace Bottcher

/-- **[K1] The Kummer deck datum (per depth).** For a radical extension `M = B[w]/(w^{2ᵏ} − a)` of a
field `B ⊇ K₀` with `X^{2ᵏ} − C a` irreducible and `ζ ∈ B` a primitive `2ᵏ`-th root of unity, the
Kummer automorphism `σ = autAdjoinRootXPowSubC` — viewed over the sub-base `K₀` (e.g. `ℂ(z)`) by
`restrictScalars` — supplies exactly one rung of the `monoF` datum that `q62_disconnected_both` /
`q62_mixed` consume:

* `M` is a field (`AdjoinRoot` of an irreducible);
* `σ : M ≃ₐ[K₀] M` fixes every base element `G ∈ B` (so `σ φ_{c₂} = φ_{c₂}` — **by Galois**, since
  `φ_{c₂} ∈ B`), and fixes the multiplier `ζ'`;
* `σ` scales the root: `σ w = ζ' · w` (the `σ F = ζ·F` clause), with `w = φ_{c₁}`;
* the multiplier `ζ' = algebraMap ζ` has order exactly `2ᵏ` (`IsPrimitiveRoot.map_of_injective`).

Non-circular: nothing about `φ_{c₂}`'s independence is assumed — it is a base element fixed by the
Galois action of a genuine radical extension. -/
theorem kummer_deck_datum {K₀ B : Type*} [Field K₀] [Field B] [Algebra K₀ B]
    (k : ℕ) (a : B) (hirr : Irreducible (X ^ (2 ^ k) - C a))
    {ζ : B} (hζ : IsPrimitiveRoot ζ (2 ^ k)) (G : B) :
    ∃ (σ : AdjoinRoot (X ^ (2 ^ k) - C a) ≃ₐ[K₀] AdjoinRoot (X ^ (2 ^ k) - C a))
      (ζ' : AdjoinRoot (X ^ (2 ^ k) - C a)) (m : ℕ),
      2 ^ k = m ∧ orderOf ζ' = m ∧
      σ (algebraMap B _ G) = algebraMap B _ G ∧ σ ζ' = ζ' ∧
      σ (AdjoinRoot.root _) = ζ' * AdjoinRoot.root _ := by
  haveI : Fact (Irreducible (X ^ (2 ^ k) - C a)) := ⟨hirr⟩
  haveI : NeZero (2 ^ k) := ⟨pow_ne_zero k two_ne_zero⟩
  refine ⟨(autAdjoinRootXPowSubC (2 ^ k) a hζ.toRootsOfUnity).restrictScalars K₀,
    algebraMap B _ ζ, 2 ^ k, rfl, ?_, ?_, ?_, ?_⟩
  · have hpr : IsPrimitiveRoot (algebraMap B (AdjoinRoot (X ^ (2 ^ k) - C a)) ζ) (2 ^ k) :=
      hζ.map_of_injective (algebraMap B _).injective
    exact hpr.eq_orderOf.symm
  · rw [AlgEquiv.restrictScalars_apply]
    exact AlgEquiv.commutes _ G
  · rw [AlgEquiv.restrictScalars_apply]
    exact AlgEquiv.commutes _ ζ
  · rw [AlgEquiv.restrictScalars_apply, autAdjoinRootXPowSubC_root, hζ.val_toRootsOfUnity_coe,
      Algebra.smul_def]

end Bottcher

namespace Bottcher

/-- **[K-capstone] The re-pick close: per-depth Kummer data ⟹ `NoRelation` over `ℂ(z)`.** The
"smoking gun" for the Kummer route. To prove the genuine coordinates `F = φ_{c₁}`, `G = φ_{c₂} ∈ V`
algebraically independent over `K = ℂ(z)`, it suffices to supply, **for each degree bound `d`**, a
radical (Kummer) field `M` with:

* an injective `K`-algebra hom `ψ : M → V` (the descent / pullback `π*`) sending the cover root
  `Fₖ ↦ φ_{c₁}` and a base element `Gₖ ↦ φ_{c₂}`;
* a Kummer deck `σ : M ≃ₐ[K] M` of order `> d` fixing `Gₖ` and the multiplier `ζ`, scaling
  `σ Fₖ = ζ·Fₖ`;
* `Gₖ` transcendental over `K` and `Fₖ ≠ 0`.

Then any relation `P(φ_{c₁}, φ_{c₂}) = 0` of `Y`-degree `D` descends through `ψ` (injective) to
`P(Fₖ, Gₖ) = 0` in `M`, where the order-`>D` deck kills it (`eq_zero_of_monodromy`). **No infinite
tower** — the carrier `M` is re-picked per relation degree. This is the non-circular close: `σ` fixes
`φ_{c₂}` because `Gₖ` is a base element fixed by the **Galois** Kummer action, and the descent `ψ` is
just `AdjoinRoot.lift` of the radical relation `φ_{c₁}^{2ⁿ} = φ_{c₁}∘f^[n]` (`bottcherCoord_iterate`).
The only `∃ M` data per `d` is exactly what `kummer_deck_datum` + the descent supply. Axiom-clean. -/
theorem noRelation_of_kummer_repick {K V : Type u} [Field K] [Field V] [Algebra K V]
    (F G : V)
    (data : ∀ d : ℕ, ∃ (M : Type u) (_ : Field M) (_ : Algebra K M)
      (ψ : M →ₐ[K] V) (Fk Gk ζ : M) (σ : M ≃ₐ[K] M),
      Injective ψ ∧ ψ Fk = F ∧ ψ Gk = G ∧
      Transcendental K Gk ∧ Fk ≠ 0 ∧ d < orderOf ζ ∧ σ Gk = Gk ∧ σ ζ = ζ ∧ σ Fk = ζ * Fk) :
    NoRelation K F G := by
  intro P hP
  obtain ⟨M, _, _, ψ, Fk, Gk, ζ, σ, hψinj, hψF, hψG, hGtr, hFk, hd, hσG, hσζ, hσF⟩ :=
    data P.natDegree
  have hnat : ∀ Q : Polynomial (Polynomial K),
      (Q.map (aeval (ψ Gk) : Polynomial K →ₐ[K] V).toRingHom).eval (ψ Fk)
        = ψ ((Q.map (aeval Gk : Polynomial K →ₐ[K] M).toRingHom).eval Fk) := by
    intro Q
    induction Q using Polynomial.induction_on with
    | C q => simp [aeval_algHom_apply]
    | add p q hp hq => simp only [Polynomial.map_add, Polynomial.eval_add, map_add, hp, hq]
    | monomial n q _ => simp [aeval_algHom_apply, map_mul, map_pow]
  have hrelk : (P.map (aeval Gk : Polynomial K →ₐ[K] M).toRingHom).eval Fk = 0 := by
    apply hψinj
    rw [map_zero, ← hnat P, hψF, hψG]
    exact hP
  exact eq_zero_of_monodromy Fk Gk hGtr σ hσG ζ (orderOf ζ) rfl hσζ hFk hσF P hd hrelk

end Bottcher

namespace Bottcher

/-- **[K-descent] The descent `ψ : M → V`.** Given a `K`-algebra hom `i : B → V` (the base map, a
`meroField` restriction/pullback) and a root `w ∈ V` of the radical equation `w^{2ᵏ} = i(a)` (the
analytic input `bottcherCoord_iterate`: `φ_{c₁}^{2ᵏ} = φ_{c₁}∘f^[k]`), `AdjoinRoot.liftAlgHom` lifts to
an injective `K`-algebra hom `ψ : M = B[w]/(X^{2ᵏ}−a) → V` with `ψ(root) = w` (`= φ_{c₁}`) and
`ψ ∘ algebraMap B = i` (so a base element `Gₖ = algebraMap B M G_B` maps to `i(G_B) = φ_{c₂}`).
Injective because `M` is a field (irreducible). This is the pullback `π*` of the Kummer route. -/
theorem kummer_descent {K B V : Type*} [Field K] [Field B] [Field V] [Algebra K B] [Algebra K V]
    (i : B →ₐ[K] V) (k : ℕ) (a : B) (hirr : Irreducible (X ^ (2 ^ k) - C a))
    (w : V) (hroot : w ^ (2 ^ k) = i a) :
    ∃ ψ : AdjoinRoot (X ^ (2 ^ k) - C a) →ₐ[K] V,
      Function.Injective ψ ∧ ψ (AdjoinRoot.root _) = w ∧
      ∀ b : B, ψ (algebraMap B _ b) = i b := by
  haveI : Fact (Irreducible (X ^ (2 ^ k) - C a)) := ⟨hirr⟩
  have haeval : (X ^ (2 ^ k) - C a).eval₂ (i : B →+* V) w = 0 := by
    simp only [eval₂_sub, eval₂_X_pow, eval₂_C, RingHom.coe_coe, hroot, sub_self]
  refine ⟨AdjoinRoot.liftAlgHom (X ^ (2 ^ k) - C a) i w haeval, ?_, ?_, ?_⟩
  · exact (AdjoinRoot.liftAlgHom (X ^ (2 ^ k) - C a) i w haeval).toRingHom.injective
  · rw [← AdjoinRoot.mk_X, AdjoinRoot.liftAlgHom_mk, eval₂_X]
  · intro b
    rw [AdjoinRoot.algebraMap_eq, AdjoinRoot.liftAlgHom_of]

end Bottcher

namespace Bottcher

/-- **[K-assembly] The full abstract Kummer close.** Combining the three pillars: to prove
`NoRelation ℂ(z) (φ_{c₁}, φ_{c₂})` it suffices to supply, per degree `d`, a *committed base field*
`B` (a `meroField(Ext)`), a `K`-algebra hom `i : B → V`, a radicand `a` and a base element `GB`, a
primitive `2^k`-th root `ζ` (k chosen with `2^k > d`), with `X^{2^k} − C a` irreducible, the radical
relation `F^{2^k} = i a` (`= bottcherCoord_iterate`), and `i GB = G = φ_{c₂}`. The Kummer deck
(`kummer_deck_datum`) + descent (`kummer_descent`) assemble these into the per-depth `data` of
`noRelation_of_kummer_repick`; transcendence of the cover element follows from transcendence of `G`
(pulled back through `ψ`), and `F ≠ 0` forces the radicand `≠ 0` hence the root `≠ 0`. Non-circular:
`σ` fixes `φ_{c₂}` because `GB ∈ B` is fixed by the Galois Kummer action, never assumed independent. -/
theorem noRelation_of_kummer_inputs {K V : Type u} [Field K] [Field V] [Algebra K V]
    (F G : V) (hF : F ≠ 0) (hGtr : Transcendental K G)
    (inputs : ∀ d : ℕ, ∃ (B : Type u) (_ : Field B) (_ : Algebra K B)
      (i : B →ₐ[K] V) (a GB ζ : B) (k : ℕ),
      d < 2 ^ k ∧ IsPrimitiveRoot ζ (2 ^ k) ∧ Irreducible (X ^ (2 ^ k) - C a) ∧
      F ^ (2 ^ k) = i a ∧ i GB = G) :
    NoRelation K F G := by
  apply noRelation_of_kummer_repick F G
  intro d
  obtain ⟨B, _, _, i, a, GB, ζ, k, hdk, hζ, hirr, hroot, hiGB⟩ := inputs d
  haveI : Fact (Irreducible (X ^ (2 ^ k) - C a)) := ⟨hirr⟩
  obtain ⟨σ, ζ', m, hm, hord, hσG, hσζ, hσroot⟩ := kummer_deck_datum (K₀ := K) k a hirr hζ GB
  obtain ⟨ψ, hψinj, hψroot, hψbase⟩ := kummer_descent i k a hirr F hroot
  have ha : a ≠ 0 := by
    intro h0; rw [h0, map_zero] at hroot
    exact hF ((pow_eq_zero_iff (pow_ne_zero k two_ne_zero)).mp hroot)
  refine ⟨AdjoinRoot (X ^ (2 ^ k) - C a), inferInstance, inferInstance, ψ,
    AdjoinRoot.root _, algebraMap B _ GB, ζ', σ,
    hψinj, hψroot, ?_, ?_, ?_, ?_, hσG, hσζ, hσroot⟩
  · rw [hψbase, hiGB]
  · have htr : Transcendental K (ψ (algebraMap B _ GB)) := by rw [hψbase, hiGB]; exact hGtr
    exact fun hx => htr (hx.algHom ψ)
  · have hr : (AdjoinRoot.root (X ^ (2 ^ k) - C a)) ^ (2 ^ k) = algebraMap B _ a := by
      have he := AdjoinRoot.eval₂_root (X ^ (2 ^ k) - C a)
      simp only [eval₂_sub, eval₂_X_pow, eval₂_C, sub_eq_zero] at he
      rw [he]; rfl
    intro h0
    rw [h0, zero_pow (pow_ne_zero k two_ne_zero)] at hr
    exact ha ((algebraMap B _).injective (by rw [← hr, map_zero]))
  · rw [hord, ← hm]; exact hdk

end Bottcher

namespace Bottcher

/-- **[K3-helper] In `K(√a)` the root is not a square** (when `a` is not a square and `−1` is a square,
e.g. over any field containing `ℂ`). The norm argument: `N_{K(√a)/K}(√a) = −a`, so if `√a = y²` then
`−a = N(y)²` is a square, hence `a = (i·N(y))²` is a square — contradiction. This discharges the
`p = 2` side condition that Mathlib's `X_pow_mul_sub_C_irreducible` needs, where the odd-prime norm
argument fails: over `ℂ`-containing fields the `−4` Capelli obstruction collapses because `−1` (hence
`−a` vs `a`) is a square. The bridge from "`a` not a square" to "`X^{2^k} − a` irreducible". -/
theorem root_not_isSquare {K : Type*} [Field K] (a : K) (ha : ∀ b : K, b ^ 2 ≠ a)
    (hneg : ∃ i : K, i ^ 2 = -1) :
    haveI : Fact (Irreducible (X ^ 2 - C a)) :=
      ⟨(X_pow_sub_C_irreducible_iff_of_prime Nat.prime_two).mpr ha⟩
    ¬ ∃ y : AdjoinRoot (X ^ 2 - C a), y ^ 2 = AdjoinRoot.root (X ^ 2 - C a) := by
  haveI hirr : Fact (Irreducible (X ^ 2 - C a)) :=
    ⟨(X_pow_sub_C_irreducible_iff_of_prime Nat.prime_two).mpr ha⟩
  rintro ⟨y, hy⟩
  obtain ⟨i, hi⟩ := hneg
  have hf : (X ^ 2 - C a) ≠ 0 := (hirr.out).ne_zero
  have hmonic : (X ^ 2 - C a).Monic := monic_X_pow_sub_C a (by norm_num)
  have hdim : (AdjoinRoot.powerBasis hf).dim = 2 := by
    rw [AdjoinRoot.powerBasis_dim, natDegree_X_pow_sub_C]
  have h1 := Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly (AdjoinRoot.powerBasis hf)
  rw [AdjoinRoot.minpoly_powerBasis_gen hf] at h1
  rw [AdjoinRoot.powerBasis_gen hf, hdim] at h1
  have hc : ((X ^ 2 - C a) * C ((X ^ 2 - C a).leadingCoeff)⁻¹).coeff 0 = -a := by
    rw [hmonic.leadingCoeff, inv_one, map_one, mul_one]; simp
  rw [hc] at h1
  have key : (Algebra.norm K y) ^ 2 = -a := by rw [← map_pow, hy, h1]; ring
  exact ha (i * Algebra.norm K y) (by rw [mul_pow, hi, key]; ring)

end Bottcher

namespace Bottcher

/-- **[K3-helper, general degree] The root of `X^{2^k} − C a` (`k ≥ 1`) is not a square**, when `a` is
not a square and `−1` is a square. Same field-norm argument as `root_not_isSquare`, with
`N(root) = (−1)^{2^k}·(−a) = −a` (`2^k` even for `k ≥ 1`). This discharges the `p = 2` side condition
of `X_pow_mul_sub_C_irreducible` at every level of the dyadic tower. -/
theorem root_pow_not_isSquare {K : Type*} [Field K] (k : ℕ) (hk : 1 ≤ k) (a : K)
    (hirr : Irreducible (X ^ (2 ^ k) - C a)) (ha : ∀ b : K, b ^ 2 ≠ a)
    (hneg : ∃ i : K, i ^ 2 = -1) :
    haveI : Fact (Irreducible (X ^ (2 ^ k) - C a)) := ⟨hirr⟩
    ¬ ∃ y : AdjoinRoot (X ^ (2 ^ k) - C a), y ^ 2 = AdjoinRoot.root (X ^ (2 ^ k) - C a) := by
  haveI : Fact (Irreducible (X ^ (2 ^ k) - C a)) := ⟨hirr⟩
  rintro ⟨y, hy⟩
  obtain ⟨i, hi⟩ := hneg
  have hf : (X ^ (2 ^ k) - C a) ≠ 0 := hirr.ne_zero
  have hmonic : (X ^ (2 ^ k) - C a).Monic := monic_X_pow_sub_C a (pow_ne_zero k two_ne_zero)
  have hdim : (AdjoinRoot.powerBasis hf).dim = 2 ^ k := by
    rw [AdjoinRoot.powerBasis_dim, natDegree_X_pow_sub_C]
  have h1 := Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly (AdjoinRoot.powerBasis hf)
  rw [AdjoinRoot.minpoly_powerBasis_gen hf] at h1
  rw [AdjoinRoot.powerBasis_gen hf, hdim] at h1
  have hc : ((X ^ (2 ^ k) - C a) * C ((X ^ (2 ^ k) - C a).leadingCoeff)⁻¹).coeff 0 = -a := by
    rw [hmonic.leadingCoeff, inv_one, map_one, mul_one, coeff_sub, coeff_C_zero, coeff_X_pow,
      if_neg (show (0 : ℕ) < 2 ^ k by positivity).ne, zero_sub]
  have heven : Even (2 ^ k) := by
    rcases Nat.exists_eq_add_of_le hk with ⟨j, rfl⟩
    exact ⟨2 ^ j, by rw [pow_add]; ring⟩
  rw [hc, heven.neg_one_pow, one_mul] at h1
  have key : (Algebra.norm K y) ^ 2 = -a := by rw [← map_pow, hy, h1]
  exact ha (i * Algebra.norm K y) (by rw [mul_pow, hi, key]; ring)

end Bottcher


namespace Bottcher

/-- **[K-transcendence] One-coordinate Kummer re-pick ⟹ transcendence.** Companion of
`noRelation_of_kummer_repick`: per-depth Kummer data for a single coordinate (injective descent `ψ`
sending nonzero root `Gₖ ↦ G`, deck `σ` of order `> d` with `σ Gₖ = ζ·Gₖ`, `σ ζ = ζ`) forces `G`
transcendental over `K`. An algebraic relation `aeval G P = 0` of degree `D` descends to
`aeval Gₖ P = 0`; the `2^k > D` rotates `ζ^j·Gₖ = σ^j Gₖ` are all roots of `P.map`, so
`eq_zero_of_high_monodromy` gives `P.map = 0`, i.e. `P = 0`. Supplies `Transcendental K φ_{c₂}` from
`φ_{c₂}`'s own dyadic monodromy — no E–vS. Axiom-clean. -/
theorem transcendental_of_kummer_inputs {K V : Type u} [Field K] [Field V] [Algebra K V]
    (G : V)
    (data : ∀ d : ℕ, ∃ (M : Type u) (_ : Field M) (_ : Algebra K M)
      (ψ : M →ₐ[K] V) (Gk ζ : M) (σ : M ≃ₐ[K] M),
      Injective ψ ∧ ψ Gk = G ∧ Gk ≠ 0 ∧ d < orderOf ζ ∧ σ ζ = ζ ∧ σ Gk = ζ * Gk) :
    Transcendental K G := by
  intro halg
  obtain ⟨P, hP0, hPG⟩ := halg
  obtain ⟨M, _, _, ψ, Gk, ζ, σ, hψinj, hψG, hGk, hd, hσζ, hσG⟩ := data P.natDegree
  have hPGk : (Polynomial.aeval Gk) P = 0 := by
    apply hψinj
    rw [map_zero, ← aeval_algHom_apply, hψG]; exact hPG
  have hσjGk : ∀ j : ℕ, (σ ^ j) Gk = ζ ^ j * Gk := by
    intro j; induction j with
    | zero => simp
    | succ n ih => rw [pow_succ', AlgEquiv.mul_apply, ih, map_mul, map_pow, hσζ, hσG, pow_succ]; ring
  have hroots : ∀ j : ℕ, j < orderOf ζ →
      (P.map (algebraMap K M)).eval (ζ ^ j * Gk) = 0 := by
    intro j _
    have h := aeval_algHom_apply (σ ^ j).toAlgHom Gk P
    rw [hPGk, map_zero, AlgEquiv.toAlgHom_apply, hσjGk j] at h
    rwa [Polynomial.aeval_def, eval₂_eq_eval_map] at h
  have hP0' : (P.map (algebraMap K M)) ≠ 0 :=
    (Polynomial.map_ne_zero_iff (algebraMap K M).injective).mpr hP0
  have hdeg : (P.map (algebraMap K M)).natDegree < orderOf ζ := by
    rwa [natDegree_map_eq_of_injective (algebraMap K M).injective]
  exact hP0' (eq_zero_of_high_monodromy rfl hGk (P.map (algebraMap K M)) hroots hdeg)

end Bottcher

namespace Bottcher
open IntermediateField

/-- **[K3-abstract] In `K⟮x⟯` (minpoly `X^{2^k}−C a`, `k≥1`) the generator is not a square**, given `a`
not a square and `−1` a square. The abstract-field analogue of `root_pow_not_isSquare`, via the
power basis of the simple extension and `N(gen) = (−1)^{2^k}·(−a) = −a`. This is exactly the `p=2`
side condition of `X_pow_mul_sub_C_irreducible`. -/
theorem gen_not_isSquare {K : Type*} [Field K] {E : Type*} [Field E] [Algebra K E] (k : ℕ)
    (hk : 1 ≤ k) (a : K) (x : E) (hmin : minpoly K x = X ^ (2 ^ k) - C a) (ha : ∀ b : K, b ^ 2 ≠ a)
    (hneg : ∃ i : K, i ^ 2 = -1) :
    ¬ ∃ y : K⟮x⟯, y ^ 2 = IntermediateField.AdjoinSimple.gen K x := by
  obtain ⟨i, hi⟩ := hneg
  have hf : (X ^ (2 ^ k) - C a) ≠ 0 := (monic_X_pow_sub_C a (pow_ne_zero k two_ne_zero)).ne_zero
  have hx : IsIntegral K x := by
    by_contra h; rw [minpoly.eq_zero h] at hmin; exact hf hmin.symm
  rintro ⟨y, hy⟩
  have hcoeff : (X ^ (2 ^ k) - C a).coeff 0 = -a := by
    rw [coeff_sub, coeff_C_zero, coeff_X_pow, if_neg (show (0:ℕ) < 2 ^ k by positivity).ne, zero_sub]
  have heven : Even (2 ^ k) := by
    rcases Nat.exists_eq_add_of_le hk with ⟨j, rfl⟩; exact ⟨2 ^ j, by rw [pow_add]; ring⟩
  have h1 : Algebra.norm K (IntermediateField.AdjoinSimple.gen K x) = -a := by
    have hh := Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly (adjoin.powerBasis hx)
    rw [adjoin.powerBasis_gen hx, adjoin.powerBasis_dim] at hh
    rw [minpoly_gen, hmin, natDegree_X_pow_sub_C, heven.neg_one_pow, one_mul, hcoeff] at hh
    exact hh
  have key : (Algebra.norm K y) ^ 2 = -a := by rw [← map_pow, hy, h1]
  exact ha (i * Algebra.norm K y) (by rw [mul_pow, hi, key]; ring)

/-- **[K3] Capelli for `p = 2`: `X^{2^k} − C a` is irreducible over any field containing `ℂ` (so `−1`
is a square) when `a` is not a square.** Mathlib only has the odd / odd-prime-power cases (it TODOs
`p=2`); this closes it for `−1`-square fields, where the `−4` Capelli obstruction collapses
(`−4 = (1+i)^(4 : ℕ)`). Induction on `k` via `X_pow_mul_sub_C_irreducible`, with `gen_not_isSquare`
discharging the side condition at each level. THE algebraic input that turns "`a = φ_{c₁}∘f^[k]` not a
square in `meroField(Ext)`" into the field carrier `M = B[w]/(X^{2^k}−a)` of the Kummer route. -/
theorem kummer_irreducible {K : Type*} [Field K] (hneg : ∃ i : K, i ^ 2 = -1) (a : K)
    (ha : ∀ b : K, b ^ 2 ≠ a) (k : ℕ) (hk : 1 ≤ k) : Irreducible (X ^ (2 ^ k) - C a) := by
  induction k, hk using Nat.le_induction with
  | base => simpa using (X_pow_sub_C_irreducible_iff_of_prime Nat.prime_two).mpr ha
  | succ k hk IH =>
    have he : (2:ℕ) ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ]; ring
    rw [he]
    refine X_pow_mul_sub_C_irreducible IH (fun E _ _ x hmin => ?_)
    refine (X_pow_sub_C_irreducible_iff_of_prime Nat.prime_two).mpr (fun b hb => ?_)
    exact gen_not_isSquare k hk a x hmin ha hneg ⟨b, hb⟩

end Bottcher

namespace Bottcher

/-- If a deck automorphism fixes the base field but scales a nonzero root by a nontrivial multiplier,
then the root's square cannot come from a square in that fixed base. This is the algebraic bridge from
finite deck-scaling data to the non-square radicand required by the Kummer provider. -/
theorem not_square_of_scaled_root_fixed_base {B M : Type*} [Field B] [Field M] [Algebra B M]
    (σ : M ≃+* M) {F ζ : M} {a : B}
    (hbase : ∀ x : B, σ (algebraMap B M x) = algebraMap B M x)
    (hroot : F ^ 2 = algebraMap B M a) (hσF : σ F = ζ * F) (hF : F ≠ 0) (hζ : ζ ≠ 1) :
    ∀ x : B, x ^ 2 ≠ a := by
  intro x hx
  let y : M := algebraMap B M x
  have hy : y ^ 2 = algebraMap B M a := by
    change (algebraMap B M x) ^ 2 = algebraMap B M a
    rw [← map_pow, hx]
  have hsq : F ^ 2 = y ^ 2 := by rw [hroot, hy]
  have hprod : (F - y) * (F + y) = 0 := by
    calc
      (F - y) * (F + y) = F ^ 2 - y ^ 2 := by ring
      _ = 0 := sub_eq_zero.mpr hsq
  rcases eq_zero_or_eq_zero_of_mul_eq_zero hprod with hminus | hplus
  · have hFy : F = y := by simpa [sub_eq_zero] using hminus
    have hsF : σ F = F := by
      rw [hFy]
      exact hbase x
    have hzF : ζ * F = F := by rw [← hσF, hsF]
    exact hζ (mul_right_cancel₀ hF (by simpa using hzF))
  · have hFy : F = -y := by
      exact eq_neg_of_add_eq_zero_left hplus
    have hsF : σ F = F := by
      rw [hFy, map_neg, hbase x]
    have hzF : ζ * F = F := by rw [← hσF, hsF]
    exact hζ (mul_right_cancel₀ hF (by simpa using hzF))

/-- Order-form of `not_square_of_scaled_root_fixed_base`: a multiplier of order greater than one is
nontrivial, so deck scaling by it forces the base radicand to be non-square. -/
theorem not_square_of_scaled_root_fixed_base_of_order {B M : Type*} [Field B] [Field M]
    [Algebra B M] (σ : M ≃+* M) {F ζ : M} {a : B}
    (hbase : ∀ x : B, σ (algebraMap B M x) = algebraMap B M x)
    (hroot : F ^ 2 = algebraMap B M a) (hσF : σ F = ζ * F) (hF : F ≠ 0)
    (hζord : 1 < orderOf ζ) :
    ∀ x : B, x ^ 2 ≠ a := by
  refine not_square_of_scaled_root_fixed_base σ hbase hroot hσF hF ?_
  intro hζ
  have horder : orderOf ζ = 1 := by simp [hζ]
  rw [horder] at hζord
  exact (Nat.lt_irrefl 1 hζord)

end Bottcher

namespace Bottcher

/-- One-coordinate transcendence directly from Kummer radical inputs. This is the one-variable analogue
of `noRelation_of_kummer_inputs`: the Kummer deck and descent are assembled internally from the
radicand, irreducibility, primitive root, and radical relation. -/
theorem transcendental_of_kummer_radical_inputs {K V : Type u} [Field K] [Field V] [Algebra K V]
    (G : V) (hG : G ≠ 0)
    (inputs : ∀ d : ℕ, ∃ (B : Type u) (_ : Field B) (_ : Algebra K B)
      (i : B →ₐ[K] V) (a ζ : B) (k : ℕ),
      d < 2 ^ k ∧ IsPrimitiveRoot ζ (2 ^ k) ∧ Irreducible (X ^ (2 ^ k) - C a) ∧
      G ^ (2 ^ k) = i a) :
    Transcendental K G := by
  apply transcendental_of_kummer_inputs G
  intro d
  obtain ⟨B, _, _, i, a, ζ, k, hdk, hζ, hirr, hroot⟩ := inputs d
  haveI : Fact (Irreducible (X ^ (2 ^ k) - C a)) := ⟨hirr⟩
  obtain ⟨σ, ζ', m, hm, hord, _hσbase, hσζ, hσroot⟩ :=
    kummer_deck_datum (K₀ := K) k a hirr hζ (0 : B)
  obtain ⟨ψ, hψinj, hψroot, _hψbase⟩ := kummer_descent i k a hirr G hroot
  have ha : a ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hroot
    exact hG ((pow_eq_zero_iff (pow_ne_zero k two_ne_zero)).mp hroot)
  have hroot_ne : (AdjoinRoot.root (X ^ (2 ^ k) - C a)) ≠ 0 := by
    have hr : (AdjoinRoot.root (X ^ (2 ^ k) - C a)) ^ (2 ^ k) = algebraMap B _ a := by
      have he := AdjoinRoot.eval₂_root (X ^ (2 ^ k) - C a)
      simp only [eval₂_sub, eval₂_X_pow, eval₂_C, sub_eq_zero] at he
      rw [he]
      rfl
    intro h0
    rw [h0, zero_pow (pow_ne_zero k two_ne_zero)] at hr
    exact ha ((algebraMap B _).injective (by rw [← hr, map_zero]))
  refine ⟨AdjoinRoot (X ^ (2 ^ k) - C a), inferInstance, inferInstance, ψ,
    AdjoinRoot.root _, ζ', σ, hψinj, hψroot, hroot_ne, ?_, hσζ, hσroot⟩
  rw [hord, ← hm]
  exact hdk

end Bottcher

namespace Bottcher

/-- A dyadic Kummer polynomial can be irreducible only when its radicand is not a square. If
`a = b^(2 : ℕ)` and `k ≥ 1`, then `X^(2^k) - C a` factors as a difference of squares. -/
theorem not_square_of_irreducible_X_pow_two_pow_sub_C {K : Type*} [Field K] {a : K} {k : ℕ}
    (hk : 1 ≤ k) (hirr : Irreducible ((X : Polynomial K) ^ (2 ^ k) - C a)) :
    ∀ b : K, b ^ 2 ≠ a := by
  intro b hb
  let m : ℕ := 2 ^ (k - 1)
  have hmpos : 0 < m := by positivity
  have hpow : 2 ^ k = m + m := by
    calc
      2 ^ k = 2 ^ ((k - 1) + 1) := by rw [Nat.sub_add_cancel hk]
      _ = 2 ^ (k - 1) * 2 := by rw [pow_succ]
      _ = m + m := by dsimp [m]; ring
  have hfac : ((X : Polynomial K) ^ (2 ^ k) - C a)
      = ((X : Polynomial K) ^ m - C b) * ((X : Polynomial K) ^ m + C b) := by
    rw [hpow, pow_add, ← sq, ← hb, map_pow]
    ring
  have hleft_nonunit : ¬ IsUnit (((X : Polynomial K) ^ m - C b)) := by
    intro hu
    have hdeg0 := Polynomial.natDegree_eq_zero_of_isUnit hu
    have hdeg : (((X : Polynomial K) ^ m - C b)).natDegree = m := by
      rw [Polynomial.natDegree_X_pow_sub_C]
    omega
  have hright_nonunit : ¬ IsUnit (((X : Polynomial K) ^ m + C b)) := by
    intro hu
    have hdeg0 := Polynomial.natDegree_eq_zero_of_isUnit hu
    have hpoly : ((X : Polynomial K) ^ m + C b) = ((X : Polynomial K) ^ m - C (-b)) := by
      simp [sub_eq_add_neg]
    have hdeg : (((X : Polynomial K) ^ m + C b)).natDegree = m := by
      rw [hpoly, Polynomial.natDegree_X_pow_sub_C]
    omega
  rcases hirr.isUnit_or_isUnit hfac with hleft | hright
  · exact hleft_nonunit hleft
  · exact hright_nonunit hright

end Bottcher
