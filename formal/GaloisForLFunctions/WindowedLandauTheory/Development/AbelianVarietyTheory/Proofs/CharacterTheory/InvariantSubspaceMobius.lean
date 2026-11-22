import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Data.Complex.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.RingTheory.Finiteness.Cardinality

/-! Möbius inversion over invariant subspaces and the polynomial weights for Green characters. -/

open Polynomial

noncomputable section

namespace GlobalTheory.CuspGL

variable {F : Type} [Field F]

/-- A polynomial weight additive under multiplication of monic polynomials. -/
def IsAdditive (s : F[X] → ℂ) : Prop :=
  ∀ P Q : F[X], P.Monic → Q.Monic → s (P * Q) = s P + s Q

private def inverseRec (s : F[X] → ℂ) : ℕ → ∀ (V : Type) [AddCommGroup V] [Module F V]
    [FiniteDimensional F V], Module.End F V → ℂ
  | 0 => fun _ _ _ _ _ => 0
  | n + 1 => fun V _ _ _ g => s (LinearMap.charpoly g) -
      ∑ᶠ W : {W : Submodule F V // W ≠ ⊤ ∧ ∀ x ∈ W, g x ∈ W},
        inverseRec s n W.1 (g.restrict W.2.2)

private theorem inverseRec_stable (s : F[X] → ℂ) (n : ℕ) :
    ∀ (m : ℕ) (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V]
      (g : Module.End F V), Module.finrank F V < n → Module.finrank F V < m →
        inverseRec s n V g = inverseRec s m V g := by
  induction n with
  | zero => intro m V _ _ _ g h; omega
  | succ n ih =>
    intro m V _ _ _ g hn hm
    cases m with
    | zero => omega
    | succ m =>
      simp only [inverseRec]
      congr 1
      refine finsum_congr fun W => ?_
      have := Submodule.finrank_lt W.2.1
      exact ih m W.1 _ (by omega) (by omega)

private theorem inverseRec_conj (s : F[X] → ℂ) (n : ℕ) :
    ∀ (V V' : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V]
      [AddCommGroup V'] [Module F V'] [FiniteDimensional F V']
      (e : V ≃ₗ[F] V') (g : Module.End F V),
      inverseRec s n V' (e.conj g) = inverseRec s n V g := by
  induction n with
  | zero => intros; rfl
  | succ n ih =>
    intro V V' _ _ _ _ _ _ e g
    simp only [inverseRec, e.charpoly_conj]
    congr 1
    let σ : {W : Submodule F V // W ≠ ⊤ ∧ ∀ x ∈ W, g x ∈ W} ≃
        {W : Submodule F V' // W ≠ ⊤ ∧ ∀ x ∈ W, e.conj g x ∈ W} :=
      (Submodule.orderIsoMapComap e).toEquiv.subtypeEquiv fun W => by
        change _ ↔ (Submodule.orderIsoMapComap e W ≠ ⊤ ∧
          ∀ y ∈ W.map (e : V →ₗ[F] V'), e.conj g y ∈ W.map (e : V →ₗ[F] V'))
        refine and_congr ?_ ⟨fun h y hy => ?_, fun h x hx => ?_⟩
        · exact ((Submodule.orderIsoMapComap e).injective.ne_iff' (map_top _)).symm
        · obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hy
          change e (g (e.symm (e x))) ∈ _
          rw [e.symm_apply_apply]
          exact Submodule.mem_map_of_mem (h x hx)
        · have hy := h (e x) (Submodule.mem_map_of_mem hx)
          simpa [LinearEquiv.conj_apply, Submodule.mem_map_equiv] using hy
    rw [← finsum_comp_equiv σ]
    refine finsum_congr fun W => ?_
    rw [← ih W.1 (W.1.map (e : V →ₗ[F] V')) (e.submoduleMap W.1)]
    show inverseRec s n (W.1.map (e : V →ₗ[F] V')) _ = _
    congr 1

/-- Invert the weight of the characteristic polynomial along invariant subspaces. -/
def psi (s : F[X] → ℂ) (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (g : Module.End F V) : ℂ :=
  inverseRec s (Module.finrank F V + 1) V g

theorem psi_eq (s : F[X] → ℂ) (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (g : Module.End F V) :
    psi s V g = s (LinearMap.charpoly g) -
      ∑ᶠ W : {W : Submodule F V // W ≠ ⊤ ∧ ∀ x ∈ W, g x ∈ W}, psi s W.1 (g.restrict W.2.2) := by
  simp only [psi, inverseRec]
  congr 1
  refine finsum_congr fun W => ?_
  have := Submodule.finrank_lt W.2.1
  change inverseRec s (Module.finrank F V) W.1 _ =
    inverseRec s (Module.finrank F W.1 + 1) W.1 _
  exact inverseRec_stable s _ _ _ _ (by omega) (by omega)

theorem psi_conj (s : F[X] → ℂ) (V V' : Type) [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] [AddCommGroup V'] [Module F V'] [FiniteDimensional F V']
    (e : V ≃ₗ[F] V') (g : Module.End F V) : psi s V' (e.conj g) = psi s V g := by
  unfold psi
  rw [← e.finrank_eq]
  exact inverseRec_conj s _ V V' e g

/-- Summing the inverted weight over the stable subspaces recovers the polynomial weight. -/
theorem charpoly_eq_finsum_psi [Finite F] (V : Type) [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (s : F[X] → ℂ) (g : Module.End F V) :
    s g.charpoly = ∑ᶠ W : {W : Submodule F V // ∀ x ∈ W, g x ∈ W}, psi s W.1 (g.restrict W.2) := by
  classical
  letI : Finite V := Module.finite_of_finite F
  letI : Finite (Submodule F V) := Finite.of_injective _ (SetLike.coe_injective (A := Submodule F V))
  letI := Fintype.ofFinite {W : Submodule F V // ∀ x ∈ W, g x ∈ W}
  letI := Fintype.ofFinite {W : Submodule F V // W ≠ ⊤ ∧ ∀ x ∈ W, g x ∈ W}
  let T : {W : Submodule F V // ∀ x ∈ W, g x ∈ W} := ⟨⊤, fun _ _ => Submodule.mem_top⟩
  have hT : psi s T.1 (g.restrict T.2) = psi s V g := by
    rw [← psi_conj s T.1 V Submodule.topEquiv (g.restrict T.2)]
    congr 1
  rw [finsum_eq_sum_of_fintype, ← Finset.add_sum_erase _ _ (Finset.mem_univ T), hT, psi_eq,
    finsum_eq_sum_of_fintype]
  rw [sub_add, eq_comm, sub_eq_self, sub_eq_zero]
  refine Finset.sum_bij (fun W _ => ⟨W.1, W.2.2⟩) ?_ ?_ ?_ ?_
  · intro W _
    exact Finset.mem_erase.2 ⟨fun h => W.2.1 (congrArg Subtype.val h), Finset.mem_univ _⟩
  · intro a _ b _ h
    exact Subtype.ext (Subtype.mk.inj h)
  · intro b hb
    exact ⟨⟨b.1, fun h => (Finset.mem_erase.1 hb).1 (Subtype.ext h), b.2⟩, Finset.mem_univ _, rfl⟩
  · intro a _
    rfl

theorem psi_of_finrank_eq_zero (s : F[X] → ℂ) (hs : IsAdditive s)
    (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V] (g : Module.End F V)
    (hV : Module.finrank F V = 0) : psi s V g = 0 := by
  letI : Subsingleton V := Module.finrank_zero_iff.mp hV
  have hp : g.charpoly = 1 := (LinearMap.charpoly_monic g).natDegree_eq_zero.mp
    (by rw [LinearMap.charpoly_natDegree, hV])
  have hw := hs 1 1 monic_one monic_one
  rw [one_mul] at hw
  have h1 : s 1 = 0 := add_left_cancel (hw.symm.trans (add_zero _).symm)
  letI : IsEmpty {W : Submodule F V // W ≠ ⊤ ∧ ∀ x ∈ W, g x ∈ W} :=
    ⟨fun W => W.2.1 (Subsingleton.elim _ _)⟩
  rw [psi_eq, hp, h1, finsum_of_isEmpty, sub_zero]

private theorem aeval_restrict_apply {V : Type} [AddCommGroup V] [Module F V]
    (g : Module.End F V) (W : Submodule F V) (hW : ∀ x ∈ W, g x ∈ W) (p : F[X]) (x : W) :
    ((aeval (g.restrict hW : Module.End F W) p x : W) : V) = aeval g p x := by
  induction p using Polynomial.induction_on generalizing x with
  | C a => simp [Module.algebraMap_end_apply]
  | add p q hp hq => simp [hp, hq]
  | monomial n a ih =>
    rw [pow_succ, ← mul_assoc, map_mul, map_mul (aeval g), aeval_X, aeval_X,
      Module.End.mul_apply, Module.End.mul_apply, ih]
    rfl

private theorem finrank_eq_zero_of_irreducible_charpoly {V : Type} [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (g : Module.End F V) (hg : Irreducible g.charpoly)
    (W : Submodule F V) (hne : W ≠ ⊤) (hW : ∀ x ∈ W, g x ∈ W) : Module.finrank F W = 0 := by
  by_contra h0
  letI : Nontrivial W := Module.nontrivial_of_finrank_pos (R := F) (Nat.pos_of_ne_zero h0)
  let f := g.restrict hW
  have hz : aeval f g.charpoly = 0 := by
    ext x
    rw [show f = g.restrict hW from rfl, aeval_restrict_apply, LinearMap.aeval_self_charpoly]
    simp
  have hd : minpoly F f ∣ g.charpoly := minpoly.dvd F f hz
  have hd' : g.charpoly ∣ minpoly F f :=
    ((hg.dvd_iff.mp hd).resolve_left (minpoly.not_isUnit F f)).dvd
  have hdeg := natDegree_le_of_dvd (hd'.trans (LinearMap.minpoly_dvd_charpoly f))
    (LinearMap.charpoly_monic f).ne_zero
  rw [LinearMap.charpoly_natDegree, LinearMap.charpoly_natDegree] at hdeg
  exact (Submodule.finrank_lt hne).not_ge hdeg

/-- An irreducible characteristic polynomial leaves only the zero proper invariant subspace. -/
theorem psi_of_irreducible_charpoly (s : F[X] → ℂ) (hs : IsAdditive s)
    (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V] (g : Module.End F V)
    (hg : Irreducible g.charpoly) : psi s V g = s g.charpoly := by
  rw [psi_eq, finsum_eq_zero_of_forall_eq_zero, sub_zero]
  intro W
  exact psi_of_finrank_eq_zero s hs _ _ (finrank_eq_zero_of_irreducible_charpoly g hg W.1 W.2.1 W.2.2)

/-- Sum the values of a multiplicative character on the roots, counted with multiplicity. -/
def rootSum (θ : AlgebraicClosure F →* ℂ) (k : ℕ) (P : F[X]) : ℂ :=
  ((P.map (algebraMap F (AlgebraicClosure F))).roots.map fun α => θ α ^ k).sum

theorem rootSum_isAdditive_and_pow_X_sub_one (θ : AlgebraicClosure F →* ℂ) (k : ℕ) :
    IsAdditive (rootSum θ k) ∧ ∀ j : ℕ, rootSum θ k ((X - C 1 : F[X]) ^ j) = j := by
  refine ⟨fun P Q hP hQ => ?_, fun j => ?_⟩
  · unfold rootSum
    rw [Polynomial.map_mul, Polynomial.roots_mul ((hP.map _).mul (hQ.map _)).ne_zero,
      Multiset.map_add, Multiset.sum_add]
  · unfold rootSum
    rw [Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C,
      Polynomial.roots_pow, Polynomial.roots_X_sub_C, Multiset.map_nsmul, Multiset.sum_nsmul]
    simp

end GlobalTheory.CuspGL
