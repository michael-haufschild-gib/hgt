/-
Deninger, *Dynamical systems for arithmetic schemes* (arXiv:1807.06400v4), Lemma 4.3 (`t3`).

Let `C` be an algebraically closed field with `C^× ≠ μ(C)` — that is, `C` is not the algebraic
closure of a finite field — and let `k` be a field with `#k ≤ #C`.  Then every homomorphism
`χ_μ : μ(k) → C^×` extends to a homomorphism `χ : k^× → C^×` with `ker χ = ker χ_μ`.

The proof of the source is followed exactly.  Both `k^× / μ(k)` and `C^× / μ(C)` are uniquely
divisible, hence `ℚ`-vector spaces, once `k` is replaced by its algebraic closure; the dimension
count `dim_ℚ (k^× / μ(k)) ≤ #k ≤ #C = dim_ℚ (C^× / μ(C))` produces a `ℚ`-linear injection between
them, and the two split extensions `k^× ≅ μ(k) × (k^× / μ(k))`, `C^× ≅ μ(C) × (C^× / μ(C))` then
assemble `χ`.  The splittings come from the divisibility of the unit groups
(`DeningerDynSysDivisibleExtension`); the dimension count comes from
`DeningerDynSysMultiplicativeRank`.

The last assertion of the lemma — the existence of an *injective* character `k^× ↪ C^×` — is
proved here whenever `k` and `C` share a subfield, which covers the equal-characteristic case of
the source.  It rests on the observation that every root of unity of `k` is algebraic over that
subfield, so `μ(k)` already lives inside the relative algebraic closure, which embeds into `C`.
-/
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.Algebraic.Cardinality
import Mathlib.FieldTheory.AlgebraicClosure
import Mathlib.Algebra.Algebra.Rat
import GaloisForLFunctions.RHTower.DeningerDynSysDivisibleExtension
import GaloisForLFunctions.RHTower.DeningerDynSysMultiplicativeRank

namespace RHTower

open Cardinal

universe u v

/-- A monoid-hom section of `Cˣ → Cˣ/μ(C)`, obtained from the retraction onto `μ(C)`. -/
theorem deningerQuotientSection (C : Type*) [Field C] [IsAlgClosed C] :
    ∃ s : (Cˣ ⧸ CommGroup.torsion Cˣ) →* Cˣ,
      ∀ z, QuotientGroup.mk' (CommGroup.torsion Cˣ) (s z) = z := by
  obtain ⟨r, hr⟩ := deningerTorsion_retraction (C := Cˣ)
  set t : Cˣ →* Cˣ := MonoidHom.mk' (fun x => x * ((r x : Cˣ))⁻¹) (by
    intro a b
    simp only [map_mul, Subgroup.coe_mul, mul_inv_rev]
    simp [mul_comm, mul_assoc, mul_left_comm]) with ht
  have htapp : ∀ x : Cˣ, t x = x * ((r x : Cˣ))⁻¹ := fun _ => rfl
  have hker : CommGroup.torsion Cˣ ≤ t.ker := by
    intro x hx
    have hrx : (r x : Cˣ) = x := congrArg Subtype.val (hr ⟨x, hx⟩)
    show t x = 1
    rw [htapp, hrx, mul_inv_cancel]
  refine ⟨QuotientGroup.lift _ t hker, ?_⟩
  intro z
  induction z using QuotientGroup.induction_on with
  | H x =>
    have h1 : (QuotientGroup.mk' (CommGroup.torsion Cˣ)) ((r x : Cˣ)) = 1 :=
      (QuotientGroup.eq_one_iff _).2 (r x).2
    have h2 : (QuotientGroup.lift (CommGroup.torsion Cˣ) t hker)
        ((x : Cˣ ⧸ CommGroup.torsion Cˣ)) = t x := rfl
    rw [h2, htapp, map_mul, map_inv, h1, inv_one, mul_one]
    rfl

/-- **Deninger, Lemma 4.3 (`t3`), algebraically closed case.**  If `C` is an algebraically closed
field which is not the algebraic closure of a finite field and `#k ≤ #C`, then every character of
`μ(k)` extends to a character of `k^×` with exactly the same kernel. -/
theorem deningerCharacterExtension_algClosed {k : Type u} [Field k] [IsAlgClosed k]
    {C : Type v} [Field C] [IsAlgClosed C]
    (hne : ∃ x : Cˣ, x ∉ CommGroup.torsion Cˣ)
    (hcard : Cardinal.lift.{v} #k ≤ Cardinal.lift.{u} #C)
    (χμ : CommGroup.torsion kˣ →* Cˣ) :
    ∃ χ : kˣ →* Cˣ,
      (∀ y : CommGroup.torsion kˣ, χ (y : kˣ) = χμ y) ∧
      (∀ x : kˣ, χ x = 1 ↔ ∃ h : x ∈ CommGroup.torsion kˣ, χμ ⟨x, h⟩ = 1) := by
  classical
  have hrank : Cardinal.lift.{v} (Module.rank ℚ (DeningerUnitSpace k))
      ≤ Cardinal.lift.{u} (Module.rank ℚ (DeningerUnitSpace C)) :=
    ((Cardinal.lift_le.2 (deningerRank_unitSpace_le k)).trans hcard).trans
      (Cardinal.lift_le.2 (deningerMk_le_rank C hne))
  obtain ⟨f, hf⟩ := lift_rank_le_iff_exists_linearMap.1 hrank
  let eC : DeningerUnitClass C ≃+ DeningerUnitSpace C :=
    AddEquiv.ofBijective (DivisibleHull.coeAddMonoidHom _) (deningerUnitSpace_coe_bijective C)
  let j₀ : DeningerUnitClass k →+ DeningerUnitClass C :=
    (eC.symm.toAddMonoidHom).comp (f.toAddMonoidHom.comp (DivisibleHull.coeAddMonoidHom _))
  have hj₀app : ∀ a, j₀ a = eC.symm (f (DivisibleHull.coe a)) := fun _ => rfl
  have hj₀inj : Function.Injective j₀ := by
    intro a b hab
    rw [hj₀app, hj₀app] at hab
    exact DivisibleHull.coe_injective (hf (eC.symm.injective hab))
  let j : (kˣ ⧸ CommGroup.torsion kˣ) →* (Cˣ ⧸ CommGroup.torsion Cˣ) :=
    MonoidHom.toAdditive.symm j₀
  have hjinj : Function.Injective j := fun a b h => hj₀inj h
  obtain ⟨sC, hsC⟩ := deningerQuotientSection C
  obtain ⟨rk, hrk⟩ := deningerTorsion_retraction (C := kˣ)
  have himg : ∀ y : CommGroup.torsion kˣ, χμ y ∈ CommGroup.torsion Cˣ := by
    intro y
    obtain ⟨n, hn, hyn⟩ := isOfFinOrder_iff_pow_eq_one.1 ((CommGroup.mem_torsion _).1 y.2)
    have hsub : (y : CommGroup.torsion kˣ) ^ n = 1 := Subtype.ext (by simpa using hyn)
    refine (CommGroup.mem_torsion _).2 (isOfFinOrder_iff_pow_eq_one.2 ⟨n, hn, ?_⟩)
    rw [← map_pow, hsub, map_one]
  refine ⟨(χμ.comp rk) * (sC.comp (j.comp (QuotientGroup.mk' (CommGroup.torsion kˣ)))), ?_, ?_⟩
  · intro y
    have h1 : rk (y : kˣ) = y := hrk y
    have h2 : (QuotientGroup.mk' (CommGroup.torsion kˣ)) (y : kˣ) = 1 :=
      (QuotientGroup.eq_one_iff _).2 y.2
    show χμ (rk (y : kˣ)) * sC (j ((QuotientGroup.mk' (CommGroup.torsion kˣ)) (y : kˣ))) = χμ y
    rw [h1, h2, map_one, map_one, mul_one]
  · intro x
    constructor
    · intro hx
      have hval : χμ (rk x) * sC (j ((QuotientGroup.mk' (CommGroup.torsion kˣ)) x)) = 1 := hx
      have hz1 : (QuotientGroup.mk' (CommGroup.torsion Cˣ)) (χμ (rk x)) = 1 :=
        (QuotientGroup.eq_one_iff _).2 (himg (rk x))
      have hq := congrArg (QuotientGroup.mk' (CommGroup.torsion Cˣ)) hval
      rw [map_mul, hz1, hsC, one_mul, map_one] at hq
      have hxk : (QuotientGroup.mk' (CommGroup.torsion kˣ)) x = 1 := by
        apply hjinj
        rw [hq, map_one]
      have hmem : x ∈ CommGroup.torsion kˣ := (QuotientGroup.eq_one_iff _).1 hxk
      refine ⟨hmem, ?_⟩
      have h1 : rk x = ⟨x, hmem⟩ := hrk ⟨x, hmem⟩
      rw [hxk, map_one, map_one, mul_one, h1] at hval
      exact hval
    · rintro ⟨hmem, hzero⟩
      have h1 : rk x = ⟨x, hmem⟩ := hrk ⟨x, hmem⟩
      have h2 : (QuotientGroup.mk' (CommGroup.torsion kˣ)) x = 1 :=
        (QuotientGroup.eq_one_iff _).2 hmem
      show χμ (rk x) * sC (j ((QuotientGroup.mk' (CommGroup.torsion kˣ)) x)) = 1
      rw [h1, h2, map_one, map_one, mul_one, hzero]

/-- **Deninger, Lemma 4.3 (`t3`).**  Let `C` be an algebraically closed field with
`C^× ≠ μ(C)` and let `k` be a field with `#k ≤ #C`.  Every homomorphism `χ_μ : μ(k) → C^×`
extends to a homomorphism `χ : k^× → C^×` whose kernel is exactly the kernel of `χ_μ`. -/
theorem deningerCharacterExtension {k : Type u} [Field k] {C : Type v} [Field C] [IsAlgClosed C]
    (hne : ∃ x : Cˣ, x ∉ CommGroup.torsion Cˣ)
    (hcard : Cardinal.lift.{v} #k ≤ Cardinal.lift.{u} #C)
    (χμ : CommGroup.torsion kˣ →* Cˣ) :
    ∃ χ : kˣ →* Cˣ,
      (∀ y : CommGroup.torsion kˣ, χ (y : kˣ) = χμ y) ∧
      (∀ x : kˣ, χ x = 1 ↔ ∃ h : x ∈ CommGroup.torsion kˣ, χμ ⟨x, h⟩ = 1) := by
  classical
  set K := AlgebraicClosure k with hK
  set U : kˣ →* Kˣ := Units.map (algebraMap k K : k →* K) with hU
  have hUval : ∀ x : kˣ, ((U x : Kˣ) : K) = algebraMap k K (x : k) := fun _ => rfl
  have hUinj : Function.Injective U := by
    intro a b hab
    have : algebraMap k K (a : k) = algebraMap k K (b : k) := by
      rw [← hUval, ← hUval, hab]
    exact Units.ext ((algebraMap k K).injective this)
  have htors : ∀ x : kˣ, (U x ∈ CommGroup.torsion Kˣ ↔ x ∈ CommGroup.torsion kˣ) := by
    intro x
    constructor
    · intro hx
      obtain ⟨n, hn, hxn⟩ := isOfFinOrder_iff_pow_eq_one.1 ((CommGroup.mem_torsion _).1 hx)
      refine (CommGroup.mem_torsion _).2 (isOfFinOrder_iff_pow_eq_one.2 ⟨n, hn, ?_⟩)
      apply hUinj
      rw [map_pow, hxn, map_one]
    · intro hx
      obtain ⟨n, hn, hxn⟩ := isOfFinOrder_iff_pow_eq_one.1 ((CommGroup.mem_torsion _).1 hx)
      refine (CommGroup.mem_torsion _).2 (isOfFinOrder_iff_pow_eq_one.2 ⟨n, hn, ?_⟩)
      rw [← map_pow, hxn, map_one]
  set Uτ : CommGroup.torsion kˣ →* CommGroup.torsion Kˣ :=
    MonoidHom.codRestrict (U.comp (CommGroup.torsion kˣ).subtype) (CommGroup.torsion Kˣ)
      (fun y => (htors (y : kˣ)).2 y.2) with hUτ
  have hUτval : ∀ y : CommGroup.torsion kˣ, ((Uτ y : Kˣ)) = U (y : kˣ) := fun _ => rfl
  have hUτinj : Function.Injective Uτ := by
    intro a b hab
    exact Subtype.ext (hUinj (by rw [← hUτval, ← hUτval, hab]))
  obtain ⟨χμ', hχμ'⟩ := deningerExtend_of_rootableBy Uτ hUτinj χμ
  have hcardK : Cardinal.lift.{v} #K ≤ Cardinal.lift.{u} #C := by
    have h1 : #K ≤ max #k ℵ₀ := Algebra.IsAlgebraic.cardinalMk_le_max k K
    have h2 : ℵ₀ ≤ Cardinal.lift.{u} #C := by
      rw [← Cardinal.lift_aleph0.{u, v}]
      exact Cardinal.lift_le.2 (Cardinal.aleph0_le_mk C)
    calc Cardinal.lift.{v} #K ≤ Cardinal.lift.{v} (max #k ℵ₀) := Cardinal.lift_le.2 h1
      _ = max (Cardinal.lift.{v} #k) ℵ₀ := by rw [Cardinal.lift_max, Cardinal.lift_aleph0]
      _ ≤ Cardinal.lift.{u} #C := max_le hcard h2
  obtain ⟨χ', hχ'ext, hχ'ker⟩ := deningerCharacterExtension_algClosed (k := K) hne hcardK χμ'
  refine ⟨χ'.comp U, ?_, ?_⟩
  · intro y
    have h1 : χ' (U (y : kˣ)) = χ' ((Uτ y : Kˣ)) := by rw [hUτval]
    have h2 : χ' ((Uτ y : Kˣ)) = χμ' (Uτ y) := hχ'ext (Uτ y)
    have h3 : χμ' (Uτ y) = χμ y := congrArg (fun F : CommGroup.torsion kˣ →* Cˣ => F y) hχμ'
    show χ' (U (y : kˣ)) = χμ y
    rw [h1, h2, h3]
  · intro x
    constructor
    · intro hx
      obtain ⟨h, hzero⟩ := (hχ'ker (U x)).1 hx
      have hmem : x ∈ CommGroup.torsion kˣ := (htors x).1 h
      refine ⟨hmem, ?_⟩
      have hEq : (⟨U x, h⟩ : CommGroup.torsion Kˣ) = Uτ ⟨x, hmem⟩ := Subtype.ext rfl
      rw [hEq] at hzero
      have h3 : χμ' (Uτ ⟨x, hmem⟩) = χμ ⟨x, hmem⟩ :=
        congrArg (fun F : CommGroup.torsion kˣ →* Cˣ => F ⟨x, hmem⟩) hχμ'
      rw [h3] at hzero
      exact hzero
    · rintro ⟨hmem, hzero⟩
      have hmemK : U x ∈ CommGroup.torsion Kˣ := (htors x).2 hmem
      refine (hχ'ker (U x)).2 ⟨hmemK, ?_⟩
      have hEq : (⟨U x, hmemK⟩ : CommGroup.torsion Kˣ) = Uτ ⟨x, hmem⟩ := Subtype.ext rfl
      rw [hEq]
      have h3 : χμ' (Uτ ⟨x, hmem⟩) = χμ ⟨x, hmem⟩ :=
        congrArg (fun F : CommGroup.torsion kˣ →* Cˣ => F ⟨x, hmem⟩) hχμ'
      rw [h3, hzero]

/-- **Roots of unity embed into any algebraically closed extension of a common subfield.**  Every
root of unity of `k` is algebraic over a subfield `F`, hence lies in the relative algebraic closure
of `F` in `k`, and that field embeds over `F` into any algebraically closed `F`-extension `C`. -/
theorem deningerRootsOfUnity_embed (F : Type*) [Field F] {k : Type*} [Field k] {C : Type*}
    [Field C] [IsAlgClosed C] [Algebra F k] [Algebra F C] :
    ∃ χμ : CommGroup.torsion kˣ →* Cˣ, Function.Injective χμ := by
  classical
  have hmem : ∀ y : CommGroup.torsion kˣ, ((y : kˣ) : k) ∈ algebraicClosure F k := by
    intro y
    obtain ⟨n, hn, hyn⟩ := isOfFinOrder_iff_pow_eq_one.1 ((CommGroup.mem_torsion _).1 y.2)
    rw [mem_algebraicClosure_iff]
    refine ⟨Polynomial.X ^ n - 1, ?_, ?_⟩
    · have := Polynomial.X_pow_sub_C_ne_zero (R := F) hn 1
      rwa [Polynomial.C_1] at this
    · have hval : (((y : kˣ) : k)) ^ n = 1 := by
        have := congrArg (fun u : kˣ => (u : k)) hyn
        simpa using this
      simp [hval]
  let ι : algebraicClosure F k →ₐ[F] C := IsAlgClosed.lift
  have hιinj : Function.Injective ι := ι.toRingHom.injective
  have hne0 : ∀ y : CommGroup.torsion kˣ, ι ⟨((y : kˣ) : k), hmem y⟩ ≠ 0 := by
    intro y h
    have h1 : (⟨((y : kˣ) : k), hmem y⟩ : algebraicClosure F k) = 0 :=
      hιinj (by rw [h, map_zero])
    exact (y : kˣ).ne_zero (congrArg Subtype.val h1)
  refine ⟨MonoidHom.mk' (fun y => Units.mk0 (ι ⟨((y : kˣ) : k), hmem y⟩) (hne0 y)) ?_, ?_⟩
  · intro a b
    apply Units.ext
    show ι ⟨(((a * b : CommGroup.torsion kˣ) : kˣ) : k), hmem (a * b)⟩
        = (ι ⟨((a : kˣ) : k), hmem a⟩) * (ι ⟨((b : kˣ) : k), hmem b⟩)
    rw [← map_mul]
    congr 1
  · intro a b hab
    have h1 : ι ⟨((a : kˣ) : k), hmem a⟩ = ι ⟨((b : kˣ) : k), hmem b⟩ := congrArg Units.val hab
    exact Subtype.ext (Units.ext (congrArg Subtype.val (hιinj h1)))

/-- **Deninger, Lemma 4.3 (`t3`), last assertion.**  If `k` and `C` share a subfield `F` — that
is, if `char C = 0` or `char k = char C > 0` — and `C` is algebraically closed with
`C^× ≠ μ(C)` and `#k ≤ #C`, then `k^×` embeds into `C^×`. -/
theorem deningerInjectiveCharacter (F : Type*) [Field F] {k : Type u} [Field k] {C : Type v}
    [Field C] [IsAlgClosed C] [Algebra F k] [Algebra F C]
    (hne : ∃ x : Cˣ, x ∉ CommGroup.torsion Cˣ)
    (hcard : Cardinal.lift.{v} #k ≤ Cardinal.lift.{u} #C) :
    ∃ χ : kˣ →* Cˣ, Function.Injective χ := by
  obtain ⟨χμ, hχμ⟩ := deningerRootsOfUnity_embed F (k := k) (C := C)
  obtain ⟨χ, hext, hker⟩ := deningerCharacterExtension hne hcard χμ
  refine ⟨χ, ?_⟩
  rw [injective_iff_map_eq_one]
  intro x hx
  obtain ⟨hmem, hzero⟩ := (hker x).1 hx
  have h1 : (⟨x, hmem⟩ : CommGroup.torsion kˣ) = 1 := hχμ (by rw [hzero, map_one])
  exact congrArg (fun y : CommGroup.torsion kˣ => (y : kˣ)) h1

/-- In characteristic zero `2` is never a root of unity, so `C^× ≠ μ(C)` is automatic. -/
theorem deningerExists_notMem_torsion_charZero (C : Type*) [Field C] [CharZero C] :
    ∃ x : Cˣ, x ∉ CommGroup.torsion Cˣ := by
  refine ⟨Units.mk0 (2 : C) (by norm_num), ?_⟩
  intro h
  obtain ⟨n, hn, hxn⟩ := isOfFinOrder_iff_pow_eq_one.1 ((CommGroup.mem_torsion _).1 h)
  have hpow : (2 : C) ^ n = 1 := by
    have := congrArg (fun u : Cˣ => (u : C)) hxn
    simpa using this
  have h2 : (((2 : ℕ) ^ n : ℕ) : C) = ((1 : ℕ) : C) := by push_cast; simpa using hpow
  have h3 : (2 : ℕ) ^ n = 1 := Nat.cast_injective h2
  have h4 : 1 < (2 : ℕ) ^ n := Nat.one_lt_two_pow_iff.mpr (by omega)
  omega

/-- **Deninger, Lemma 4.3 (`t3`), last assertion, equal characteristic zero.** -/
theorem deningerInjectiveCharacter_charZero {k : Type u} [Field k] [CharZero k] {C : Type v}
    [Field C] [IsAlgClosed C] [CharZero C]
    (hcard : Cardinal.lift.{v} #k ≤ Cardinal.lift.{u} #C) :
    ∃ χ : kˣ →* Cˣ, Function.Injective χ :=
  deningerInjectiveCharacter ℚ (deningerExists_notMem_torsion_charZero C) hcard

/-- **Deninger, Lemma 4.3 (`t3`), last assertion, equal positive characteristic.** -/
theorem deningerInjectiveCharacter_charP {p : ℕ} [Fact p.Prime] {k : Type u} [Field k]
    [CharP k p] {C : Type v} [Field C] [IsAlgClosed C] [CharP C p]
    (hne : ∃ x : Cˣ, x ∉ CommGroup.torsion Cˣ)
    (hcard : Cardinal.lift.{v} #k ≤ Cardinal.lift.{u} #C) :
    ∃ χ : kˣ →* Cˣ, Function.Injective χ := by
  letI : Algebra (ZMod p) k := (ZMod.castHom (dvd_refl p) k).toAlgebra
  letI : Algebra (ZMod p) C := (ZMod.castHom (dvd_refl p) C).toAlgebra
  exact deningerInjectiveCharacter (ZMod p) hne hcard

end RHTower
