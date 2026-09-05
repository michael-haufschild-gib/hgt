import GaloisForLFunctions.HTGeometry.MvPolynomialInfiniteVanishing
import GaloisForLFunctions.HTGeometry.DifferentialPolynomialOver

/-!
# Additive subgroups inside a differential algebraic set satisfy a linear relation

Cassidy's classification of differential algebraic subgroups of the additive group, in the form a
hypertranscendence argument consumes, and by an elementary argument.

A differential polynomial in one differential indeterminate involves only finitely many jets, so it
is a polynomial on a finite-dimensional jet space, and the jet vectors of an additive subgroup form
an additive subgroup of that space.  If those vectors spanned the space, the polynomial would vanish
on the integer lattice of a spanning family, hence at every point, hence be zero.  They therefore
span a proper subspace, and a functional annihilating it is exactly a nonzero linear relation among
the jets, valid on the whole subgroup.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open scoped Differential
open GaloisForLFunctions

variable {C : Type*} [Field C] [CharZero C] [Differential C]

omit [CharZero C] [Differential C] in
theorem mvPolynomial_aeval_eq_eval {σ : Type*} (x : σ → C) (p : MvPolynomial σ C) :
    MvPolynomial.aeval x p = MvPolynomial.eval x p :=
  Eq.symm (DFunLike.congr rfl rfl)

omit [CharZero C] in
theorem differentialJet_apply_zero (n : ℕ) : differentialJet n (0 : C) = 0 := by
  induction n with
  | zero => rw [differentialJet_zero]
  | succ n ih => rw [differentialJet_succ, ih, map_zero]

/-- The jet vector of an element, as an additive map. -/
def jetVecHom (n : ℕ) : C →+ (Fin (n + 1) → C) where
  toFun v := fun i => differentialJet (i : ℕ) v
  map_zero' := by
    funext i
    exact differentialJet_apply_zero _
  map_add' x y := by
    funext i
    exact differentialJet_add_apply _ x y

omit [CharZero C] in
@[simp] theorem jetVecHom_apply (n : ℕ) (v : C) (i : Fin (n + 1)) :
    jetVecHom n v i = differentialJet (i : ℕ) v := rfl

/-- **Cassidy's additive classification, elementary form.**  An additive subgroup of a differential
field of characteristic zero lying in the zero set of a nonzero differential polynomial satisfies a
nonzero linear relation among the jets.

The jet vectors of the subgroup form an additive subgroup of a finite-dimensional space on which the
polynomial vanishes; if they spanned, the polynomial would vanish on a lattice basis, hence at every
point, so they do not, and a functional annihilating their span is the relation. -/
theorem exists_nonzero_linear_jet_relation_of_addSubgroup (V : AddSubgroup C)
    {P : DifferentialPolynomial Unit C} (hP : P ≠ 0)
    (hPV : ∀ v ∈ V, differentialPolynomialEvalOver (K := C) (fun _ : Unit => v) P = 0) :
    ∃ (n : ℕ) (c : Fin (n + 1) → C), (∃ i, c i ≠ 0) ∧
      ∀ v ∈ V, ∑ i : Fin (n + 1), c i * differentialJet (i : ℕ) v = 0 := by
  classical
  obtain ⟨n, hn⟩ : ∃ n : ℕ, ∀ p ∈ P.vars, p.2 < n + 1 := by
    refine ⟨(P.vars.image Prod.snd).sup id, fun p hp => ?_⟩
    have hle : p.2 ≤ (P.vars.image Prod.snd).sup id :=
      Finset.le_sup (f := id) (Finset.mem_image_of_mem Prod.snd hp)
    omega
  have hfinj : Function.Injective (fun i : Fin (n + 1) => ((), (i : ℕ))) := by
    intro i j hij
    exact Fin.val_injective (congrArg Prod.snd hij)
  obtain ⟨Q, hQ⟩ := MvPolynomial.exists_rename_eq_of_vars_subset_range P
    (fun i : Fin (n + 1) => ((), (i : ℕ))) hfinj (by
      intro p hp
      exact ⟨⟨p.2, hn p (by simpa using hp)⟩, by
        rcases p with ⟨u, k⟩
        cases u
        rfl⟩)
  have hQ0 : Q ≠ 0 := by
    intro hzero
    rw [hzero, map_zero] at hQ
    exact hP hQ.symm
  have hevalQ : ∀ v : C, differentialPolynomialEvalOver (K := C) (fun _ : Unit => v) P
      = MvPolynomial.eval (jetVecHom n v) Q := by
    intro v
    rw [← hQ, differentialPolynomialEvalOver]
    show MvPolynomial.aeval (fun p : Unit × ℕ => differentialJet p.2 v)
      ((MvPolynomial.rename (fun i : Fin (n + 1) => ((), (i : ℕ)))) Q) = _
    rw [MvPolynomial.aeval_rename]
    show MvPolynomial.aeval (fun i : Fin (n + 1) => differentialJet (i : ℕ) v) Q = _
    exact mvPolynomial_aeval_eq_eval (fun i : Fin (n + 1) => differentialJet (i : ℕ) v) Q
  have hQA : ∀ a ∈ V.map (jetVecHom n), MvPolynomial.eval a Q = 0 := by
    rintro a ⟨v, hv, rfl⟩
    rw [← hevalQ v]
    exact hPV v hv
  by_cases hspan : Submodule.span C ((V.map (jetVecHom n) : AddSubgroup (Fin (n + 1) → C)) :
      Set (Fin (n + 1) → C)) = ⊤
  · exfalso
    refine hQ0 (MvPolynomial.funext fun x => ?_)
    rw [map_zero]
    have hx : x ∈ Submodule.span C ((V.map (jetVecHom n) : AddSubgroup (Fin (n + 1) → C)) :
        Set (Fin (n + 1) → C)) := by rw [hspan]; trivial
    obtain ⟨m, f, g, hx⟩ := Submodule.mem_span_set'.mp hx
    have hgA : ∀ j : Fin m, (g j : Fin (n + 1) → C) ∈ V.map (jetVecHom n) := fun j => (g j).2
    set R : MvPolynomial (Fin m) C :=
      MvPolynomial.aeval (fun i : Fin (n + 1) =>
        ∑ j : Fin m, MvPolynomial.C ((g j : Fin (n + 1) → C) i) * MvPolynomial.X j) Q with hR
    have hevalR : ∀ t : Fin m → C,
        MvPolynomial.eval t R = MvPolynomial.eval (∑ j : Fin m, t j • (g j : Fin (n + 1) → C)) Q := by
      intro t
      rw [hR]
      have hcomp := MvPolynomial.comp_aeval (R := C) (σ := Fin (n + 1))
        (fun i : Fin (n + 1) =>
          ∑ j : Fin m, MvPolynomial.C ((g j : Fin (n + 1) → C) i) * MvPolynomial.X j)
        (MvPolynomial.aeval t : MvPolynomial (Fin m) C →ₐ[C] C)
      have happ := congrArg (fun φ : MvPolynomial (Fin (n + 1)) C →ₐ[C] C => φ Q) hcomp
      simp only [AlgHom.coe_comp, Function.comp_apply] at happ
      have hfun : (fun i : Fin (n + 1) => (MvPolynomial.aeval t)
            (∑ j : Fin m, MvPolynomial.C ((g j : Fin (n + 1) → C) i) * MvPolynomial.X j))
          = ∑ j : Fin m, t j • (g j : Fin (n + 1) → C) := by
        funext i
        rw [map_sum, Finset.sum_apply]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [map_mul, MvPolynomial.aeval_C, MvPolynomial.aeval_X, Pi.smul_apply, smul_eq_mul,
          mul_comm]
        rfl
      calc MvPolynomial.eval t R
          = MvPolynomial.aeval t R := (mvPolynomial_aeval_eq_eval t R).symm
        _ = MvPolynomial.aeval (fun i : Fin (n + 1) => (MvPolynomial.aeval t)
              (∑ j : Fin m, MvPolynomial.C ((g j : Fin (n + 1) → C) i) * MvPolynomial.X j)) Q := by
              rw [hR]; exact happ
        _ = MvPolynomial.eval (∑ j : Fin m, t j • (g j : Fin (n + 1) → C)) Q := by
              rw [hfun]
              exact mvPolynomial_aeval_eq_eval
                (∑ j : Fin m, t j • (g j : Fin (n + 1) → C)) Q
    have hRzero : R = 0 := by
      refine mvPolynomial_eq_zero_of_eval_eq_zero_on_infinite_pow
        (S := Set.range ((Int.cast : ℤ → C))) (Set.infinite_range_of_injective Int.cast_injective)
        m R ?_
      intro t ht
      rw [hevalR]
      refine hQA _ ?_
      refine AddSubgroup.sum_mem _ fun j _ => ?_
      obtain ⟨k, hk⟩ := ht j
      have hsmul : t j • (g j : Fin (n + 1) → C) = k • (g j : Fin (n + 1) → C) := by
        rw [← hk]
        ext i
        simp [zsmul_eq_mul]
      rw [hsmul]
      exact AddSubgroup.zsmul_mem _ (hgA j) k
    have hxeval : MvPolynomial.eval x Q = MvPolynomial.eval f R := by
      rw [hevalR, hx]
    rw [hxeval, hRzero, map_zero]
  · have hlt : Submodule.span C ((V.map (jetVecHom n) : AddSubgroup (Fin (n + 1) → C)) :
        Set (Fin (n + 1) → C)) < ⊤ := lt_of_le_of_ne le_top hspan
    obtain ⟨φ, hφ0, hφle⟩ := Submodule.exists_dual_map_eq_bot_of_lt_top hlt inferInstance
    refine ⟨n, fun i => φ (Pi.single i 1), ?_, ?_⟩
    · by_contra hcon
      push Not at hcon
      refine hφ0 (LinearMap.ext fun x => ?_)
      have hexpand : x = ∑ i : Fin (n + 1), x i • (Pi.single i (1 : C)) := by
        funext k
        rw [Finset.sum_apply, Finset.sum_eq_single k]
        · simp
        · intro j _ hj
          simp [Ne.symm hj]
        · intro hcon2
          exact absurd (Finset.mem_univ k) hcon2
      rw [hexpand, map_sum]
      rw [LinearMap.zero_apply]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [map_smul, hcon i, smul_zero]
    · intro v hv
      have hmem : jetVecHom n v ∈ V.map (jetVecHom n) := ⟨v, hv, rfl⟩
      have hzero : φ (jetVecHom n v) = 0 := by
        have hmapmem : φ (jetVecHom n v) ∈ Submodule.map φ
            (Submodule.span C ((V.map (jetVecHom n) : AddSubgroup (Fin (n + 1) → C)) :
              Set (Fin (n + 1) → C))) :=
          Submodule.mem_map_of_mem (Submodule.subset_span hmem)
        rw [hφle, Submodule.mem_bot] at hmapmem
        exact hmapmem
      have hexpand : jetVecHom n v = ∑ i : Fin (n + 1),
          differentialJet (i : ℕ) v • (Pi.single i (1 : C)) := by
        funext k
        rw [Finset.sum_apply, Finset.sum_eq_single k]
        · simp
        · intro j _ hj
          simp [Ne.symm hj]
        · intro hcon2
          exact absurd (Finset.mem_univ k) hcon2
      rw [hexpand, map_sum] at hzero
      rw [← hzero]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, smul_eq_mul, mul_comm]

end

end GaloisForLFunctions.HTGeometry
