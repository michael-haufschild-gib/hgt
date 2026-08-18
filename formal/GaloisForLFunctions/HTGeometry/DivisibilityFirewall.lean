import Mathlib.Algebra.DirectSum.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Algebra.Module.Rat
import Mathlib.GroupTheory.FiniteAbelian.Basic

/-!
# The divisibility firewall: finite-coefficient data cannot see the rational rank

Every arithmetic statement of the shape "`K_n(R)/m` is such-and-such étale cohomology", every
reciprocity sequence whose target is a direct sum of finite groups, and every torsion computation,
is invariant under adjoining a `ℚ`-vector space to the group in question.  A `ℚ`-vector space `V` is
uniquely divisible and torsion free, so

* `V = mV` for every `m ≠ 0`, hence the mod-`m` classes of `A × V` are exactly those of `A`;
* `V` has no torsion, hence the torsion subgroup of `A × V` is that of `A`;
* every homomorphism out of `A × V` into a direct sum of *finite* groups kills `V`, because a
  direct sum of finite groups contains no element divisible by every natural number;

while `A × V` is **not** torsion when `V ≠ 0`, even if `A` is.

This is a genuine obstruction, not a slogan: it says that no combination of finite-coefficient
statements — Merkurjev–Suslin/Tate isomorphisms `K_2(F)/m ≅ H²(F, μ_m^{⊗2})`, Moore's reciprocity
sequence `K_2(F) → ⊕_v μ(F_v) → μ(F) → 1`, finiteness of `H²_ét(𝒪_S, ℤ_p(2))` — can imply
`K_2(𝒪_F) ⊗ ℚ = 0`.  Every one of those hypotheses is satisfied by the perturbed system with `V`
adjoined, and the conclusion is not.  Any proof of the rank statement must therefore contain a step
whose input does not factor through the mod-`m` theory: in practice a finite generation statement
about the integral group, or a direct rank computation.

* `directSumFinite_eq_zero_of_forall_nsmul` : **a direct sum of finite groups has no nonzero
  element divisible by every natural number.**
* `firewall_nsmul_iff` : the mod-`m` classes are blind to `V`.
* `firewall_torsion_iff` : the torsion is blind to `V`.
* `firewall_hom_directSumFinite` : every reciprocity map into a direct sum of finite groups is
  blind to `V`.
* `divisibility_firewall` : **the four statements together — the no-go.**
-/

namespace GaloisForLFunctions.HTGeometry

open DirectSum

section DirectSumFinite

variable {ι : Type*} {G : ι → Type*} [∀ i, AddCommGroup (G i)]
  [∀ i, Finite (G i)]

/-- **A direct sum of finite groups contains no nonzero infinitely divisible element.**  If `t` is
divisible by every nonzero natural number then each of its coordinates is divisible by the order of
its own summand, hence vanishes. -/
theorem directSumFinite_eq_zero_of_forall_nsmul (t : ⨁ i, G i)
    (h : ∀ n : ℕ, n ≠ 0 → ∃ s : ⨁ i, G i, n • s = t) : t = 0 := by
  ext i
  have hcard : Nat.card (G i) ≠ 0 := Nat.card_ne_zero.2 ⟨⟨0⟩, inferInstance⟩
  obtain ⟨s, hs⟩ := h (Nat.card (G i)) hcard
  have hcoord : (Nat.card (G i)) • s i = t i := by
    rw [← hs]
    rfl
  rw [← hcoord, card_nsmul_eq_zero']
  rfl

end DirectSumFinite

section Firewall

variable {A V : Type*} [AddCommGroup A] [AddCommGroup V] [Module ℚ V]

private theorem ratModule_torsion_free {n : ℕ} (hn : n ≠ 0) {v : V} (h : n • v = 0) : v = 0 := by
  have hcast : ((n : ℚ)) • v = 0 := by
    rw [← Nat.cast_smul_eq_nsmul ℚ n v] at h
    exact h
  have hne : ((n : ℚ)) ≠ 0 := Nat.cast_ne_zero.2 hn
  calc v = ((n : ℚ))⁻¹ • (((n : ℚ)) • v) := by
        rw [smul_smul, inv_mul_cancel₀ hne, one_smul]
    _ = 0 := by rw [hcast, smul_zero]

private theorem ratModule_divisible {n : ℕ} (hn : n ≠ 0) (v : V) : ∃ w : V, n • w = v := by
  refine ⟨((n : ℚ))⁻¹ • v, ?_⟩
  rw [← Nat.cast_smul_eq_nsmul ℚ n (((n : ℚ))⁻¹ • v), smul_smul,
    mul_inv_cancel₀ (Nat.cast_ne_zero.2 hn), one_smul]

/-- **The mod-`m` classes are blind to a rational summand.** -/
theorem firewall_nsmul_iff {m : ℕ} (hm : m ≠ 0) (x : A × V) :
    (∃ y : A × V, m • y = x) ↔ ∃ a : A, m • a = x.1 := by
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨y.1, rfl⟩
  · rintro ⟨a, ha⟩
    obtain ⟨w, hw⟩ := ratModule_divisible (V := V) hm x.2
    exact ⟨(a, w), Prod.ext ha hw⟩

/-- **The torsion is blind to a rational summand.** -/
theorem firewall_torsion_iff (x : A × V) :
    (∃ n : ℕ, n ≠ 0 ∧ n • x = 0) ↔ x.2 = 0 ∧ ∃ n : ℕ, n ≠ 0 ∧ n • x.1 = 0 := by
  constructor
  · rintro ⟨n, hn, hnx⟩
    have h1 : n • x.1 = 0 := congrArg Prod.fst hnx
    have h2 : n • x.2 = 0 := congrArg Prod.snd hnx
    exact ⟨ratModule_torsion_free hn h2, n, hn, h1⟩
  · rintro ⟨h2, n, hn, h1⟩
    refine ⟨n, hn, Prod.ext h1 ?_⟩
    show n • x.2 = 0
    rw [h2, smul_zero]

variable {ι : Type*} {G : ι → Type*} [∀ i, AddCommGroup (G i)]
  [∀ i, Finite (G i)]

/-- **Every reciprocity map into a direct sum of finite groups is blind to a rational summand.**
This is what makes Moore's sequence, and every family of tame or Hilbert symbols, unable to detect
a uniquely divisible part of `K_2`. -/
theorem firewall_hom_directSumFinite (φ : (A × V) →+ ⨁ i, G i) (v : V) : φ (0, v) = 0 := by
  refine directSumFinite_eq_zero_of_forall_nsmul _ fun n hn => ?_
  obtain ⟨w, hw⟩ := ratModule_divisible (V := V) hn v
  refine ⟨φ (0, w), ?_⟩
  rw [← map_nsmul]
  congr 1
  refine Prod.ext ?_ ?_
  · simp
  · exact hw

/-- **A rational summand destroys torsion.** -/
theorem firewall_not_torsion [Nontrivial V] :
    ¬ ∀ x : A × V, ∃ n : ℕ, n ≠ 0 ∧ n • x = 0 := by
  intro h
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  obtain ⟨n, hn, hnx⟩ := h (0, v)
  exact hv (ratModule_torsion_free hn (congrArg Prod.snd hnx))

/-- **The divisibility firewall.**  For every abelian group `A`, every nonzero `ℚ`-vector space `V`
and every direct sum `T` of finite groups: the mod-`m` classes, the torsion, and every homomorphism
into `T` are the same for `A × V` as for `A`, yet `A × V` is not torsion.

Read arithmetically with `A = K_2(𝒪_F)`: no family of statements about the groups `K_2/m`, about
the torsion, or about reciprocity maps into direct sums of finite groups — that is, no combination
of the Merkurjev–Suslin/Tate isomorphism, Moore's sequence, and finiteness of étale cohomology with
finite coefficients — can imply that `K_2(𝒪_F)` is torsion.  The essential input of any such proof
must be a statement about the integral group that does not factor through its finite-coefficient
data. -/
theorem divisibility_firewall [Nontrivial V] :
    (∀ m : ℕ, m ≠ 0 → ∀ x : A × V, (∃ y : A × V, m • y = x) ↔ ∃ a : A, m • a = x.1)
      ∧ (∀ x : A × V, (∃ n : ℕ, n ≠ 0 ∧ n • x = 0)
          ↔ x.2 = 0 ∧ ∃ n : ℕ, n ≠ 0 ∧ n • x.1 = 0)
      ∧ (∀ φ : (A × V) →+ ⨁ i, G i, ∀ v : V, φ (0, v) = 0)
      ∧ ¬ ∀ x : A × V, ∃ n : ℕ, n ≠ 0 ∧ n • x = 0 :=
  ⟨fun _ hm => firewall_nsmul_iff hm, firewall_torsion_iff,
    firewall_hom_directSumFinite, firewall_not_torsion⟩

end Firewall

/-! ## What breaks the firewall: finite generation -/

section Breaking

variable {A : Type*} [AddCommGroup A] [AddGroup.FG A]

/-- **A finitely generated abelian group that is not torsion has `ℤ` as a quotient.**  This is the
exact converse of the firewall: for a finitely generated group, failure of torsion *is* visible
modulo every `m`, because the `ℤ`-quotient survives reduction. -/
theorem exists_int_surjection_of_not_isTorsion (h : ¬ AddMonoid.IsTorsion A) :
    ∃ φ : A →+ ℤ, Function.Surjective φ := by
  classical
  obtain ⟨n, ι, hι, p, hp, e, ⟨f⟩⟩ := AddCommGroup.equiv_free_prod_directSum_zmod A
  haveI : Fintype ι := hι
  haveI : ∀ i, NeZero (p i ^ e i) := fun i => ⟨pow_ne_zero _ (hp i).ne_zero⟩
  rcases Nat.eq_zero_or_pos n with hn | hn
  · exfalso
    subst hn
    haveI : Subsingleton (Fin 0 →₀ ℤ) :=
      ⟨fun x y => Finsupp.ext fun i => i.elim0⟩
    haveI : Finite (Fin 0 →₀ ℤ) := Finite.of_subsingleton
    haveI : Finite (DirectSum ι fun i => ZMod (p i ^ e i)) :=
      Finite.of_equiv _
        (DFinsupp.equivFunOnFintype (β := fun i => ZMod (p i ^ e i))).symm
    haveI : Finite ((Fin 0 →₀ ℤ) × DirectSum ι fun i => ZMod (p i ^ e i)) := inferInstance
    haveI : Finite A := Finite.of_equiv _ f.toEquiv.symm
    exact h fun a => isOfFinAddOrder_of_finite a
  · refine ⟨(Finsupp.applyAddHom (⟨0, hn⟩ : Fin n)).comp
      ((AddMonoidHom.fst _ _).comp f.toAddMonoidHom), fun k => ?_⟩
    refine ⟨f.symm (Finsupp.single (⟨0, hn⟩ : Fin n) k, 0), ?_⟩
    simp

/-- **Finite generation makes non-torsion visible modulo every `m`.** -/
theorem exists_zmod_surjection_of_not_isTorsion (h : ¬ AddMonoid.IsTorsion A) (m : ℕ) :
    ∃ ψ : A →+ ZMod m, Function.Surjective ψ := by
  obtain ⟨φ, hφ⟩ := exists_int_surjection_of_not_isTorsion h
  exact ⟨(Int.castAddHom (ZMod m)).comp φ, (ZMod.intCast_surjective).comp hφ⟩

/-- **The firewall is broken exactly by finite generation.**  A finitely generated abelian group
with no `ℤ`-quotient is torsion.  Contrapositive of `exists_int_surjection_of_not_isTorsion`; stated
this way because it is the shape a formalization of `rank K₂(𝒪_F) = 0` must consume. -/
theorem isTorsion_of_fg_of_no_int_quotient
    (h : ∀ φ : A →+ ℤ, ¬ Function.Surjective φ) : AddMonoid.IsTorsion A := by
  by_contra hcon
  obtain ⟨φ, hφ⟩ := exists_int_surjection_of_not_isTorsion hcon
  exact h φ hφ

end Breaking

end GaloisForLFunctions.HTGeometry
