import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralFilling.ReplicaOrders.PhysicalPolynomial

/-! # Simultaneous detuning of every nontrivial replica frequency -/
open Finset MvPolynomial Set MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace GaloisForLFunctions.HTGeometry.SpectralFilling.ReplicaOrders
noncomputable section

/-- If B is the number of occupation multisets, exactly B(B−1) distinct
ordered pairs occur in the physical product. -/
theorem physical_multiset_degree (k q : ℕ) :
    let D := 2^(k+3)
    let B := (D+q-1).choose q
    (physical k q).totalDegree=B*(B-1) := by
  intro D B
  rw [physical_degree]
  let A := Sym (Level k) q
  let e : {p : A×A // p.1=p.2} ≃ A :=
    { toFun := fun p => p.val.1
      invFun := fun a => ⟨(a,a),rfl⟩
      left_inv := fun p => Subtype.ext (Prod.ext rfl p.property)
      right_inv := fun _ => rfl }
  change Fintype.card {p : A×A // ¬p.1=p.2}=_
  rw [Fintype.card_subtype_compl,Fintype.card_prod,Fintype.card_congr e]
  have ha : Fintype.card A=B := by
    change Fintype.card (Sym (Level k) q)=_
    rw [Sym.card_sym_eq_choose,Fintype.card_fin]
  rw [ha,Nat.mul_sub,Nat.mul_one]

private theorem gap_bound {I : Type*} [Fintype I] [DecidableEq I] {q : ℕ}
    {E : I→ℝ} {R : ℝ} (h : ∀ i, |E i| ≤ R) (p : Pair I q) : |gap E p| ≤ 2*(q:ℝ)*R := by
  have hh (u : Sym I q) : |∑ i, (u.val.count i:ℝ)*E i| ≤ (q:ℝ)*R := by
    apply (Finset.abs_sum_le_sum_abs ..).trans
    calc _ ≤ ∑ i, (u.val.count i:ℝ)*R := Finset.sum_le_sum fun i _ => by
           rw [abs_mul,abs_of_nonneg (Nat.cast_nonneg _)]
           exact mul_le_mul_of_nonneg_left (h i) (Nat.cast_nonneg _)
         _ = _ := by rw [←Finset.sum_mul,←Nat.cast_sum,count_sum]
  unfold gap
  simp only [mode,Int.cast_sub,Int.cast_natCast,sub_mul,Finset.sum_sub_distrib]
  exact (abs_sub _ _).trans ((add_le_add (hh _) (hh _)).trans_eq (by ring))

private theorem product_bound {I : Type*} [Fintype I] [DecidableEq I] {q : ℕ}
    (E : I→ℝ) (p : Pair I q) {B : ℝ} (hB : 1 ≤ B) (hb : ∀ z : Pair I q, |gap E z| ≤ B) :
    |value E q| ≤ |gap E p| * B^(degreeBound (Fintype.card I) q) := by
  classical
  rw [value,Finset.abs_prod,←Finset.prod_erase_mul _ _ (Finset.mem_univ p),mul_comm]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  have h := Finset.prod_le_prod (fun i _ => abs_nonneg (gap E i)) (fun i (_ : i ∈ univ.erase p) => hb i)
  apply h.trans
  rw [Finset.prod_const]
  exact pow_le_pow_right₀ hB ((Finset.card_le_univ _).trans (card_pairs_le_bound I q))

/-- With D energy levels, one polynomial of degree at most D²ᑫ
detects all order-q collisions between distinct multiplicity vectors. -/
theorem gaussian_replica_detuning (k q : ℕ) {r : ℝ} (hr : 0 < r) (hr₁ : r ≤ 1) (R : ℝ) :
    let D : ℕ := 2^(k+3)
    let d := degreeBound D q
    let B := max 1 (2*(q:ℝ)*R)
    (Measure.pi fun _ : Coordinate k => gaussianReal 0 1)
      {x | let E := (isHermitian_spectralEnsembleMatrix (chainPauliFin_isHermitian (k+3)) x).eigenvalues
           (∀ i, |E i| ≤ R) ∧ ∃ p : Pair (Level k) q, |gap E p| < (r/B)^d} ≤
      ENNReal.ofReal (2*(d:ℝ)*r) := by
  intro D d B
  have hB : 1 ≤ B := le_max_left ..
  have hB₀ := zero_lt_one.trans_le hB
  have hc : Fintype.card (Pair (Level k) q) ≤ d := (card_pairs_le_bound (Level k) q).trans_eq (by rw [Fintype.card_fin])
  have h := gaussian_mvPolynomial_sublevel (physical k q) (physical_ne_zero k q) hr hr₁
  apply le_trans (measure_mono _) (h.trans _)
  · rintro x ⟨hE,p,hp⟩
    let E := (isHermitian_spectralEnsembleMatrix (chainPauliFin_isHermitian (k+3)) x).eigenvalues
    change ‖eval (fun i => (x i:ℂ)) (physical k q)‖ < _
    rw [physical_eval,Complex.norm_real,Real.norm_eq_abs,physical_degree]
    have hprod := product_bound E p hB (fun z => (gap_bound hE z).trans (le_max_right ..))
    rw [Fintype.card_fin] at hprod
    have he : |gap E p| * B^d < r^d := by
      rw [div_pow] at hp
      exact (lt_div_iff₀ (pow_pos hB₀ d)).mp hp
    exact (hprod.trans_lt he).trans_le ((pow_le_pow_of_le_one hr.le hr₁ hc).trans
      (le_mul_of_one_le_left (pow_nonneg hr.le _) (physical_head k q)))
  · rw [physical_degree]
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hc) (by norm_num)) hr.le)

#print axioms gaussian_replica_detuning
end
end GaloisForLFunctions.HTGeometry.SpectralFilling.ReplicaOrders
