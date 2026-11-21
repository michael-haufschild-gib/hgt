import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.Elimination.RootVariables

/-! # A level polynomial for weighted sums of rational functions of the roots -/

open MvPolynomial Matrix
namespace GaloisForLFunctions.HTGeometry.SpectralJets
noncomputable section
variable {ι : Type*} [Fintype ι] {D : ℕ}

private def inRoot (k : ℕ) (i : Fin k) (q : MvPolynomial (Option ι) ℂ) :
    MvPolynomial (RootVariables (Option ι) k) ℂ :=
  rename (fun o : Option ι => o.elim (rootVariable k i) (fun a => baseVariable k (some a))) q

omit [Fintype ι] in
private theorem eval_inRoot (x : ι → ℂ) (u : ℂ) (k : ℕ) (E : Fin k → ℂ)
    (i : Fin k) (q : MvPolynomial (Option ι) ℂ) :
    eval (assignRoots (fun o : Option ι => o.elim u x) k E) (inRoot k i q) =
      eval (fun o : Option ι => o.elim (E i) x) q := by
  rw [inRoot,eval_rename]
  apply congrArg (fun z => eval z q)
  funext o
  cases o <;> simp [Function.comp_apply]

/-- Clear all denominators of the weighted mode before eliminating its roots. -/
def rationalLevelEquation (m : Fin D → ℂ) (q d : MvPolynomial (Option ι) ℂ) :
    MvPolynomial (RootVariables (Option ι) D) ℂ :=
  X (baseVariable D (none : Option ι)) * (∏ i, inRoot D i d) -
    ∑ i, C (m i) * inRoot D i q * ∏ j ∈ Finset.univ.erase i, inRoot D j d

omit [Fintype ι] in
private theorem equation_degree (m : Fin D → ℂ) (q d : MvPolynomial (Option ι) ℂ) :
    (rationalLevelEquation m q d).totalDegree ≤ 1+q.totalDegree+D*d.totalDegree := by
  have hprod (s : Finset (Fin D)) : (∏ j ∈ s, inRoot D j d).totalDegree ≤ D*d.totalDegree := by
    apply (totalDegree_finsetProd s _).trans
    apply (Finset.sum_le_sum (fun j (_ : j ∈ s) => totalDegree_rename_le _ d)).trans
    rw [Finset.sum_const,smul_eq_mul]
    exact Nat.mul_le_mul_right _ ((Finset.card_le_card (Finset.subset_univ s)).trans_eq (Fintype.card_fin D))
  rw [rationalLevelEquation]
  apply (totalDegree_sub _ _).trans (max_le ?_ ?_)
  · apply (totalDegree_mul _ _).trans
    rw [totalDegree_X]
    have hp := hprod Finset.univ
    omega
  · apply totalDegree_finsetSum_le
    intro i _
    apply (totalDegree_mul _ _).trans
    have hq := totalDegree_mul (C (m i)) (inRoot D i q)
    rw [totalDegree_C,zero_add] at hq
    have hq' : (inRoot D i q).totalDegree ≤ q.totalDegree := totalDegree_rename_le _ _
    have hd := hprod (Finset.univ.erase i)
    omega

/-- Elimination retains all independent assignments of roots to the weights,
including assignments with repeated indices. -/
def rationalModeLevel (M : Matrix (Fin D) (Fin D) (MvPolynomial ι ℂ))
    (m : Fin D → ℂ) (q d : MvPolynomial (Option ι) ℂ) : MvPolynomial (Option ι) ℂ :=
  eliminateRoots (extendPencil M 1) D (rationalLevelEquation m q d)

theorem rationalModeLevel_degree (M : Matrix (Fin D) (Fin D) (MvPolynomial ι ℂ))
    (hM : ∀ i j, (M i j).totalDegree ≤ 1) (m : Fin D → ℂ)
    (q d : MvPolynomial (Option ι) ℂ) :
    (rationalModeLevel M m q d).totalDegree+1 ≤
      (D+2*D*D+1)^D*(1+q.totalDegree+D*d.totalDegree+1) :=
  (eliminateRoots_degree (extendPencil M 1) (extend_degree M hM 1) D _).trans
    (Nat.mul_le_mul_left _ (Nat.add_le_add_right (equation_degree m q d) 1))

omit [Fintype ι] in
private theorem eval_level_equation (x : ι → ℂ) (u : ℂ) (E m : Fin D → ℂ)
    (q d : MvPolynomial (Option ι) ℂ) (hd : ∀ i, eval (fun o : Option ι => o.elim (E i) x) d ≠ 0) :
    eval (assignRoots (fun o : Option ι => o.elim u x) D E) (rationalLevelEquation m q d) = 0 ↔
      u = ∑ i, m i * eval (fun o : Option ι => o.elim (E i) x) q /
        eval (fun o : Option ι => o.elim (E i) x) d := by
  let Q := fun i => eval (fun o : Option ι => o.elim (E i) x) q
  let H := fun i => eval (fun o : Option ι => o.elim (E i) x) d
  have hp : ∏ i, H i ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => hd i
  have hquot (i) : m i*Q i*(∏ j ∈ Finset.univ.erase i, H j) = (m i*Q i/H i)*(∏ j, H j) := by
    rw [← Finset.mul_prod_erase Finset.univ H (Finset.mem_univ i)]
    field_simp [show H i ≠ 0 from hd i]
  simp only [rationalLevelEquation,map_sub,map_mul,map_sum,map_prod,eval_X,eval_C,assignRoots_base,
    Option.elim_none,eval_inRoot]
  change u*(∏ i, H i) - (∑ i, m i*Q i*(∏ j ∈ Finset.univ.erase i, H j)) = 0 ↔ _
  simp_rw [hquot]
  rw [← Finset.sum_mul,← sub_mul,mul_eq_zero,or_iff_left hp,sub_eq_zero]

/-- At a simple root packet with nonzero denominators, the level equation
is exact. The polynomial has no spurious levels beyond independent root selections. -/
theorem eval_rationalModeLevel_eq_zero_iff (M : Matrix (Fin D) (Fin D) (MvPolynomial ι ℂ))
    (x : ι → ℂ) (E m : Fin D → ℂ) (hi : Function.Injective E)
    (ht : ∀ k : ℕ, eval x (M^k).trace = ∑ j, E j^k) (q d : MvPolynomial (Option ι) ℂ)
    (hd : ∀ j, eval (fun o : Option ι => o.elim (E j) x) d ≠ 0) (u : ℂ) :
    eval (fun o : Option ι => o.elim u x) (rationalModeLevel M m q d) = 0 ↔
      ∃ s : Fin D → Fin D, u = ∑ i, m i * eval (fun o : Option ι => o.elim (E (s i)) x) q /
        eval (fun o : Option ι => o.elim (E (s i)) x) d := by
  let M' : Matrix (Fin D) (Fin D) (MvPolynomial (Option ι) ℂ) := extendPencil M 1
  let z (o : Option ι) := o.elim u x
  have he : assignRoots x 1 (fun _ => u) = z := by funext o; cases o <;> rfl
  have htr (a : ℕ) : eval z (M'^a).trace = ∑ j, E j^a := by
    rw [← he]
    exact (extend_trace M x 1 (fun _ => u) a).trans (ht a)
  change eval z (eliminateRoots M' D (rationalLevelEquation m q d)) = 0 ↔ _
  refine (eval_eliminateRoots_eq_zero_iff M' z E hi htr D _).trans ?_
  exact exists_congr fun s => eval_level_equation x u (fun i => E (s i)) m q d (fun i => hd (s i))

#print axioms rationalModeLevel_degree
#print axioms eval_rationalModeLevel_eq_zero_iff
end
end GaloisForLFunctions.HTGeometry.SpectralJets
