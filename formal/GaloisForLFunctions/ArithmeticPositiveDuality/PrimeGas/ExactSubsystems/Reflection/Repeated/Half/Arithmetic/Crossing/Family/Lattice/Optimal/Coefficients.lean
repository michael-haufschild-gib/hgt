import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Family.Lattice.Synthesis

/-! # Bounded positive frequencies for prescribed reflected partition zeros -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Lattice.Optimal

open Finset Real

private abbrev Response := ℤ × (ℝ → ℝ)

/-- The integer component tracks the first moment of the signed occupations. -/
private def atom (k : ℕ) : Response := ((k : ℤ), fun t => oddTerm t (k : ℝ))

private def window (m : ℕ) : Submodule ℤ Response :=
  Submodule.span ℤ (Set.range fun j : Fin m => atom (j.val+1))

private theorem atom_mem {k m : ℕ} (hk : k ≤ m) : atom k ∈ window m := by
  cases k with
  | zero =>
    have h : atom 0=0 := by
      apply Prod.ext
      · rfl
      · funext t; simp [atom,oddTerm]
    rw [h]; exact (window m).zero_mem
  | succ k => exact Submodule.subset_span ⟨⟨k,hk⟩,rfl⟩

private theorem widen (m : ℕ) : window m ≤ window (m+1) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨j,rfl⟩
  exact atom_mem (by omega)

/-- Multiplication by the even coordinate doubles the first moment. -/
private def timesCoordinate : Response →ₗ[ℤ] Response :=
  AddMonoidHom.toIntLinearMap {
    toFun := fun a => (2*a.1, fun t => coordinate t*a.2 t)
    map_zero' := by apply Prod.ext <;> simp; rfl
    map_add' := by intro a b; apply Prod.ext <;> simp [mul_add]; rfl }

private theorem neighbors (k : ℕ) : timesCoordinate (atom (k+1))=atom (k+2)+atom k := by
  apply Prod.ext
  · change 2*((k+1 : ℕ) : ℤ)=((k+2 : ℕ) : ℤ)+(k : ℤ)
    push_cast; ring
  · funext t
    change coordinate t*oddTerm t ((k+1 : ℕ) : ℝ)=oddTerm t ((k+2 : ℕ) : ℝ)+oddTerm t (k : ℝ)
    have step (x : ℝ) : coordinate t*oddTerm t x=oddTerm t (x+1)+oddTerm t (x-1) := by
      simp only [coordinate,oddTerm,sub_eq_add_neg,mul_add,mul_neg,mul_one,neg_neg,exp_add]
      ring
    convert step ((k : ℝ)+1) using 2 <;> push_cast <;> ring_nf

private theorem grow (m : ℕ) {v : Response} (h : v ∈ window m) :
    timesCoordinate v ∈ window (m+1) := by
  have incl : window m ≤ (window (m+1)).comap timesCoordinate := by
    apply Submodule.span_le.mpr
    rintro _ ⟨j,rfl⟩
    change timesCoordinate (atom (j.val+1)) ∈ window (m+1)
    rw [neighbors]
    exact (window _).add_mem (atom_mem (by omega)) (atom_mem (by omega))
  exact incl h

private theorem base_mem : ((0,base) : Response) ∈ window 2 := by
  have eq : ((0,base) : Response)=atom 2-(atom 1+atom 1) := by
    apply Prod.ext
    · change (0 : ℤ)=2-(1+1); ring
    · funext t
      change base t=oddTerm t ((2 : ℕ) : ℝ)-(oddTerm t ((1 : ℕ) : ℝ)+oddTerm t ((1 : ℕ) : ℝ))
      simp only [Nat.cast_ofNat,Nat.cast_one,base,coordinate,oddTerm,mul_one,mul_two,exp_add]
      ring
  rw [eq]
  have one : atom 1 ∈ window 2 := atom_mem (by omega)
  exact (window 2).sub_mem (atom_mem le_rfl) ((window 2).add_mem one one)

/-- Clearing rational denominators gives an integral linear factor. -/
def factor (q : ℚ) (x : ℝ) : ℝ := (q.den : ℝ)*x-(q.num : ℝ)

def profile (T : Finset ℚ) (t : ℝ) : ℝ := base t * ∏ q ∈ T, factor q (coordinate t)

private theorem profile_mem (T : Finset ℚ) : ((0,profile T) : Response) ∈ window (T.card+2) := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    have eq : profile ∅=base := by funext t; simp only [profile,prod_empty,mul_one]
    simpa only [eq,card_empty,zero_add] using base_mem
  | @insert q T hq ih =>
    rw [card_insert_of_notMem hq,show T.card+1+2=T.card+2+1 from by omega]
    let v : Response := (0,profile T)
    have eq : ((0,profile (insert q T)) : Response)=
        (q.den : ℤ) • timesCoordinate v-q.num • v := by
      apply Prod.ext
      · change (0 : ℤ)=(q.den : ℤ)*(2*0)-q.num*0
        ring
      · funext t
        change profile (insert q T) t=(q.den : ℤ) • (coordinate t*profile T t)-q.num • profile T t
        simp only [profile,prod_insert hq,factor,zsmul_eq_mul,Int.cast_natCast]
        ring
    rw [eq]
    exact (window _).sub_mem ((window _).smul_mem _ (grow _ ih)) ((window _).smul_mem _ (widen _ ih))

/-- At most one signed coefficient per positive frequency is needed; their
weighted first moment is zero for every finite set of rational thresholds. -/
theorem bounded_coefficients (T : Finset ℚ) :
    ∃ c : Fin (T.card+2) → ℤ, (∑ j, c j*(j.val+1 : ℤ))=0 ∧
      ∀ t : ℝ, (∑ j, (c j : ℝ)*oddTerm t ((j.val : ℝ)+1))=profile T t := by
  classical
  obtain ⟨c,eq⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp (profile_mem T)
  refine ⟨c,?_,fun t => ?_⟩
  · have h := congrArg Prod.fst eq
    simp only [Prod.fst_sum,Prod.smul_fst] at h
    simpa only [atom,zsmul_eq_mul,Int.cast_id,Nat.cast_add,Nat.cast_one] using h
  · have h := congrArg (fun v : Response => v.2 t) eq
    simp only [Prod.snd_sum,Finset.sum_apply,Prod.smul_snd,Pi.smul_apply] at h
    simpa only [atom,zsmul_eq_mul,Nat.cast_add,Nat.cast_one] using h

#print axioms bounded_coefficients

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Lattice.Optimal
