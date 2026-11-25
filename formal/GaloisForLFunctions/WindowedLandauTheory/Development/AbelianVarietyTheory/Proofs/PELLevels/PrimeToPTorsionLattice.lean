import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.PELLevels.IntegralPrimePowerLattice
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.PELModuli.IntegralPELModuli

/-! The geometric Tate structure identifies prime-to-p torsion with the coefficient lattice. -/

open AlgebraicGeometry CategoryTheory NumberField MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj

namespace GlobalTheory.UPel.HT.EtLev

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R}
variable {S : Scheme.{0}} {s : S ⟶ Spec (CommRingCat.of R)} {N : ℕ}

/-- The prime-power geometric torsion away from p is free of rank m times n. -/
theorem primeToP_torsion_points_free (o : Obj b N s) {k : Type} [Field k] [IsAlgClosed k]
    (x : Spec (CommRingCat.of k) ⟶ S) {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓp : ℓ ≠ p) (j : ℕ) :
    let I := Ideal.span {((ℓ ^ j : ℕ) : 𝓞 D.F)}
    ∃ f : (Fin (D.m * D.n) → 𝓞 D.F ⧸ I) → (Over.mk x ⟶ o.A),
      (∀ a a', f (a + a') = f a * f a') ∧
      (∀ (c : 𝓞 D.F) a, f (Ideal.Quotient.mk I c • a) = f a ≫ o.act.act (algebraMap (𝓞 D.F) D.O c)) ∧
      Function.Injective f ∧ ∀ g, g ^ (ℓ ^ j) = 1 → ∃ a, f a = g := by
  let a := Spec.preimage (x ≫ s)
  have ha : x ≫ s = Spec.map a := by simp [a]
  obtain ⟨t, -⟩ := o.geom k x a.hom ha
  let A := 𝓞 D.F
  letI : Module A D.La := Module.compHom D.La (algebraMap A D.O)
  let I := Ideal.span {((ℓ ^ j : ℕ) : A)}
  let L : Submodule A D.La := I • ⊤
  obtain ⟨e⟩ := latQuot_rational_prime_free D ℓ hℓ j
  have hpos : 0 < ℓ ^ j := pow_pos hℓ.pos j
  have hcop : (ℓ ^ j).Coprime p :=
    Nat.Coprime.pow_left j ((Nat.coprime_primes hℓ (Fact.out : p.Prime)).mpr hℓp)
  have hmem (y : D.La) : y ∈ L ↔ ∃ z, y = (ℓ ^ j) • z := by
    change y ∈ I • (⊤ : Submodule A D.La) ↔ _
    dsimp only [I]
    rw [Submodule.ideal_span_singleton_smul]
    simp only [Submodule.mem_smul_pointwise_iff_exists, Submodule.mem_top, true_and, Nat.cast_smul_eq_nsmul]
    exact exists_congr fun _ => eq_comm
  let G := Over.mk x ⟶ o.A
  let f : D.La →+ Additive G :=
    { toFun := fun y => Additive.ofMul (t.ev (ℓ ^ j) y)
      map_zero' := by
        show Additive.ofMul (t.ev (ℓ ^ j) 0) = Additive.ofMul 1
        rw [(t.ker _ hpos hcop 0).2 ⟨0, by simp⟩]
      map_add' := fun y y' => congrArg Additive.ofMul (t.add _ y y') }
  have hle : L.toAddSubgroup ≤ f.ker := by
    intro y hy
    have h := (t.ker _ hpos hcop y).2 ((hmem y).1 hy)
    exact congrArg Additive.ofMul h
  let v : D.La ⧸ L →+ Additive G := QuotientAddGroup.lift L.toAddSubgroup f hle
  have hv (y : D.La) : v (Submodule.Quotient.mk y) = Additive.ofMul (t.ev (ℓ ^ j) y) := rfl
  refine ⟨fun a => Additive.toMul (v (e a)), ?_, ?_, ?_, ?_⟩
  · intro a a'
    simp only [map_add, toMul_add]
  · intro c a
    obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective L (e a)
    change Additive.toMul (v (e (Ideal.Quotient.mk I c • a))) = Additive.toMul (v (e a)) ≫ _
    rw [map_smul, ← hy, Module.Quotient.mk_smul_mk, hv, hv]
    exact t.lin _ (algebraMap A D.O c) y
  · intro a a' h
    apply e.injective
    rw [← sub_eq_zero, ← map_sub]
    obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective L (e (a - a'))
    have h₁ : v (e (a - a')) = 0 := by
      rw [map_sub, map_sub, sub_eq_zero]
      exact congrArg Additive.ofMul h
    rw [← hy, Submodule.Quotient.mk_eq_zero, hmem]
    rw [← hy, hv] at h₁
    exact (t.ker _ hpos hcop y).1 (congrArg Additive.toMul h₁)
  · intro g hg
    obtain ⟨y, rfl⟩ := (t.onto _ hpos hcop g).1 hg
    refine ⟨e.symm (Submodule.Quotient.mk y), ?_⟩
    change Additive.toMul (v (e (e.symm (Submodule.Quotient.mk y)))) = _
    rw [LinearEquiv.apply_symm_apply, hv]
    rfl

end GlobalTheory.UPel.HT.EtLev
