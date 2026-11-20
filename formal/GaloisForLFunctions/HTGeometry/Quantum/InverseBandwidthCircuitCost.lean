import GaloisForLFunctions.HTGeometry.ProjectiveContinuousCircuitConeLaw
import GaloisForLFunctions.HTGeometry.StaticLocalLaboratoryComplexityGrowthLaw
import GaloisForLFunctions.HTGeometry.ContinuousPlateauGrid

/-!
# Circuit cost at the inverse bandwidth of an onsite field

Flipping all untouched qubits preserves each diagonal circuit entry. For an
onsite occupation field, two such configurations have phase separation set
by the number of untouched sites. At time π/n this forces an extensive
number of gates, even after a perturbation of the generator.
-/

open Matrix
open scoped Matrix.Norms.L2Operator

namespace GaloisForLFunctions.HTGeometry
noncomputable section

private abbrev Reg (n : ℕ) := Matrix (Fin n → Bool) (Fin n → Bool) ℂ

/-- Qubits on which at least one of the circuit's gates acts. -/
def TwoQubitCircuit.touchedSites {n : ℕ} (C : TwoQubitCircuit n) : Finset (Fin n) :=
  (Finset.univ.image fun i => (C.architecture.sites i).1) ∪
    (Finset.univ.image fun i => (C.architecture.sites i).2)

theorem TwoQubitCircuit.card_touchedSites_le {n : ℕ} (C : TwoQubitCircuit n) :
    C.touchedSites.card ≤ 2*C.gateCount := by
  unfold TwoQubitCircuit.touchedSites
  refine (Finset.card_union_le _ _).trans ?_
  have h1 := Finset.card_image_le (s := Finset.univ (α := Fin C.gateCount))
    (f := fun i => (C.architecture.sites i).1)
  have h2 := Finset.card_image_le (s := Finset.univ (α := Fin C.gateCount))
    (f := fun i => (C.architecture.sites i).2)
  simp only [Finset.card_univ,Fintype.card_fin] at h1 h2
  omega

/-- Flip all qubits outside S without changing any addressed qubit. -/
private def idleFlip (S : Finset (Fin n)) : Equiv.Perm (Fin n → Bool) where
  toFun x i := if i ∈ S then x i else !(x i)
  invFun x i := if i ∈ S then x i else !(x i)
  left_inv x := by funext i; by_cases hi : i ∈ S <;> simp [hi]
  right_inv x := by funext i; by_cases hi : i ∈ S <;> simp [hi]

private theorem lift_invariant_on_idle {n : ℕ} (S : Finset (Fin n))
    {a b : Fin n} (ha : a ∈ S) (hb : b ∈ S) (hab : a ≠ b)
    (U : Matrix.specialUnitaryGroup (Bool × Bool) ℂ) (x y : Fin n → Bool) :
    (twoQubitLift a b hab U).val (idleFlip S x) (idleFlip S y) = (twoQubitLift a b hab U).val x y := by
  let T := {i : Fin n // i ≠ a ∧ i ≠ b}
  have hrest : (fun i : T => (idleFlip S x) i.val) = (fun i : T => (idleFlip S y) i.val) ↔
      (fun i : T => x i.val) = (fun i : T => y i.val) := by
    constructor
    · intro he
      funext i
      have h := congrFun he i
      by_cases hi : i.val ∈ S <;> simpa [idleFlip,hi] using h
    · intro he
      funext i
      have h := congrFun he i
      by_cases hi : i.val ∈ S <;> simp [idleFlip,hi,h]
  change U.val ((idleFlip S x) a,(idleFlip S x) b) ((idleFlip S y) a,(idleFlip S y) b) *
    (1 : Matrix (T → Bool) (T → Bool) ℂ) (fun i => (idleFlip S x) i.val) (fun i => (idleFlip S y) i.val) =
    U.val (x a,x b) (y a,y b) * (1 : Matrix (T → Bool) (T → Bool) ℂ) (fun i => x i.val) (fun i => y i.val)
  simp only [Matrix.one_apply, hrest]
  simp [idleFlip, ha, hb]

private theorem circuit_invariant_on_idle {n : ℕ} (C : TwoQubitCircuit n) (x y : Fin n → Bool) :
    C.eval.val (idleFlip C.touchedSites x) (idleFlip C.touchedSites y) = C.eval.val x y := by
  let S := C.touchedSites
  let Φ := Matrix.reindexAlgEquiv ℂ ℂ (idleFlip S)
  let g (i : Fin C.gateCount) := C.architecture.gateLift i (C.gates i)
  have hg (i) : Φ (g i).val = (g i).val := by
    ext a b
    have h1 : (C.architecture.sites i).1 ∈ S := Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))
    have h2 : (C.architecture.sites i).2 ∈ S := Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))
    exact lift_invariant_on_idle S h1 h2 (C.architecture.distinct i) (C.gates i) a b
  have hp (l : List (Matrix.unitaryGroup (Fin n → Bool) ℂ))
      (hl : ∀ U ∈ l, Φ U.val = U.val) : Φ l.prod.val = l.prod.val := by
    induction l with
    | nil => exact map_one Φ
    | cons a l ih =>
      change Φ (a.val*l.prod.val) = a.val*l.prod.val
      rw [map_mul, hl a (List.mem_cons_self), ih (fun U h => hl U (List.mem_cons_of_mem _ h))]
  have hlist : Φ C.eval.val = C.eval.val := by
    apply hp ((List.ofFn g).reverse)
    intro U hU
    rw [List.mem_reverse, List.mem_ofFn] at hU
    obtain ⟨i,rfl⟩ := hU
    exact hg i
  exact congrFun (congrFun hlist x) y

/-- Uniform sum of one-qubit occupation projectors. -/
def occupationField (n : ℕ) : Reg n :=
  Matrix.diagonal (fun x => (((Finset.univ.filter fun i => x i = true).card : ℕ) : ℂ))

private theorem occupationField_selfAdjoint (n : ℕ) : IsSelfAdjoint (occupationField n) := by
  apply Matrix.IsHermitian.isSelfAdjoint
  rw [occupationField,Matrix.isHermitian_diagonal_iff]
  intro i
  simp [IsSelfAdjoint]

/-- For the onsite field at time π/n, the fraction of sites left untouched
is a lower bound on the error for every circuit, including arbitrary global
rephasing. The assertion also holds on the empty register. -/
theorem occupationField_inverseBandwidth_gate_cost (n : ℕ) (C : TwoQubitCircuit n) (c : ℂ) :
    (n:ℝ) ≤ 2*(C.gateCount:ℝ) + n *
      ‖unitaryEvolution (occupationField n) (Real.pi/n) - c • (C.eval : Reg n)‖ := by
  classical
  cases n with
  | zero => simp
  | succ k =>
    let n := k+1
    let S := C.touchedSites
    let a : Fin n → Bool := fun _ => false
    let b := idleFlip S a
    let E (x : Fin n → Bool) := ((Finset.univ.filter fun i => x i = true).card : ℝ)
    let t := Real.pi/n
    let U := unitaryEvolution (occupationField n) t
    have hU (x) : U x x = Complex.exp (-(Complex.I*(t*E x))) := by
      have hd : occupationField n = Matrix.diagonal (fun i => (E i : ℂ)) := by
        unfold occupationField E; push_cast; rfl
      simp only [U,hd,unitaryEvolution_diagonal,Matrix.diagonal_apply_eq]
    have ha : E a = 0 := by simp [E,a]
    have hb : E b = (n:ℝ) - S.card := by
      have hfilter : (Finset.univ.filter fun i => b i = true) = Sᶜ := by
        ext i
        by_cases hi : i ∈ S <;> simp [b,idleFlip,a,hi]
      change (((Finset.univ.filter fun i => b i = true).card : ℕ) : ℝ) = _
      rw [hfilter,Finset.card_compl,Nat.cast_sub (Finset.card_le_univ S),Fintype.card_fin]
    have hn : 0 < (n:ℝ) := by dsimp [n]; positivity
    have hφ : 0 ≤ t*E b := by dsimp [t]; positivity
    have hφ' : t*E b ≤ Real.pi := by
      rw [hb]
      dsimp [t]
      calc
        _ ≤ Real.pi/(n:ℝ)*n := by gcongr; exact sub_le_self _ (Nat.cast_nonneg _)
        _ = _ := div_mul_cancel₀ _ hn.ne'
    have hchord := StaticLocalLaboratoryComplexityGrowthLaw.phase_chord_lower hφ hφ'
    have hphase : 2*(n - (S.card:ℝ))/(n:ℝ) ≤ ‖U b b - U a a‖ := by
      rw [hU b,hU a,ha,Complex.ofReal_zero,mul_zero,mul_zero,neg_zero,Complex.exp_zero]
      rw [← Complex.ofReal_mul]
      calc
        _ = 2*(t*E b)/Real.pi := by rw [hb]; dsimp [t]; field_simp
        _ ≤ _ := hchord
    let d := ‖U - c • (C.eval : Reg n)‖
    have he (x) : ‖U x x - c*C.eval.val x x‖ ≤ d := by
      exact norm_entry_le_l2_opNorm (U - c • (C.eval : Reg n)) x x
    have hsame : C.eval.val b b = C.eval.val a a := circuit_invariant_on_idle C a a
    have htri := norm_sub_le_norm_sub_add_norm_sub (U b b) (c*C.eval.val a a) (U a a)
    have he' := he b
    rw [hsame] at he'
    rw [norm_sub_rev (c*C.eval.val a a) (U a a)] at htri
    have hcost : (S.card:ℝ) ≤ 2*(C.gateCount:ℝ) := by exact_mod_cast C.card_touchedSites_le
    have hmul := (div_le_iff₀ hn).mp (hphase.trans (htri.trans (add_le_add he' (he a))))
    change (n:ℝ) ≤ 2*(C.gateCount:ℝ) + n*d
    nlinarith only [hmul,hcost]

/-- A perturbation of the field pays at most π times its operator norm
in the scaled gate bound, even if it couples every qubit. -/
theorem perturbedOccupationField_inverseBandwidth_gate_cost (n : ℕ)
    (H : selfAdjoint (Reg n)) (C : TwoQubitCircuit n) (c : ℂ) :
    (n:ℝ) ≤ 2*(C.gateCount:ℝ) + n *
      ‖unitaryEvolution H.val (Real.pi/n) - c • (C.eval : Reg n)‖ +
      Real.pi * ‖occupationField n - H.val‖ := by
  cases n with
  | zero => simp [add_nonneg, Real.pi_pos.le, mul_nonneg, norm_nonneg]
  | succ k =>
    let n := k+1
    let t := Real.pi/n
    have hn : 0 < (n:ℝ) := by dsimp [n]; positivity
    have ht : 0 ≤ t := div_nonneg Real.pi_pos.le hn.le
    let U := unitaryEvolution (occupationField n) t
    let V := unitaryEvolution H.val t
    let X := c • (C.eval : Reg n)
    let δ := ‖occupationField n - H.val‖
    have hΔ : ‖U - V‖ ≤ t * δ := by
      simpa only [abs_of_nonneg ht] using norm_unitaryEvolution_sub_le
        (occupationField n) H.val (occupationField_selfAdjoint n) H.property t
    have hdist : ‖U-X‖ ≤ t*δ + ‖V-X‖ :=
      (norm_sub_le_norm_sub_add_norm_sub U V X).trans (add_le_add hΔ (le_refl _))
    have htime : (n:ℝ)*t = Real.pi := by dsimp [t]; field_simp
    calc
      (n:ℝ) ≤ 2*(C.gateCount:ℝ) + n*‖U-X‖ := occupationField_inverseBandwidth_gate_cost n C c
      _ ≤ 2*(C.gateCount:ℝ) + n*(t*δ+‖V-X‖) :=
        add_le_add (le_refl _) (mul_le_mul_of_nonneg_left hdist hn.le)
      _ = 2*(C.gateCount:ℝ) + n*‖V-X‖ + Real.pi*δ := by rw [mul_add, ← mul_assoc, htime]; abel

#print axioms occupationField_inverseBandwidth_gate_cost
#print axioms perturbedOccupationField_inverseBandwidth_gate_cost
end
end GaloisForLFunctions.HTGeometry
