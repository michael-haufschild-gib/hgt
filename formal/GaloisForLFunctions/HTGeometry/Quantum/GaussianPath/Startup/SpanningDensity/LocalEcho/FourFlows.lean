import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.LocalErrors.Word
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.EigenlineSignals.AnalyticSignal
import GaloisForLFunctions.HTGeometry.SpectralObservedOrbitDimension

/-! # Four conjugated evolutions for a pair of commuting spin flips -/
open Matrix NormedSpace
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpanningDensity.LocalEcho
noncomputable section
abbrev Register (N : ℕ) := Matrix (Fin N→Bool) (Fin N→Bool) ℂ

/-- The multiplicative commutator of the transported output and the input. -/
def echo {N : ℕ} (U A B : Register N) := (star U*A*U*B)*(star U*A*U*B)

theorem echo_norm {N : ℕ} (U A B : Register N) (hU : U ∈ unitary _)
    (hA : A ∈ unitary _) (hB : B ∈ unitary _) (ha : A*A=1) (hb : B*B=1) :
    ‖echo U A B-1‖=‖(star U*A*U)*B-B*(star U*A*U)‖ := by
  let Y := star U*A*U
  have hy : Y*Y=1 := by
    calc _ = star U*(A*(U*star U)*A)*U := by simp only [Y,mul_assoc]
         _ = _ := by rw [(Unitary.mem_iff.mp hU).2,mul_one,ha,mul_one,(Unitary.mem_iff.mp hU).1]
  have hunit := mul_mem (mul_mem (mul_mem (Unitary.star_mem hU) hA) hU) hB
  have he : (Y*B-B*Y)*(Y*B)=echo U A B-1 := by
    rw [sub_mul,show (B*Y)*(Y*B)=B*(Y*Y)*B by simp only [mul_assoc],hy,mul_one,hb]
    rfl
  rw [←he]
  exact CStarRing.norm_mul_mem_unitary _ hunit

/-- Moving the two commuting flips through the four propagators leaves a
word with signed Hamiltonians H, −AHA, ABHAB, −BHB. -/
theorem echo_word {N : ℕ} (H : selfAdjoint (Register N)) (A B : Register N)
    (ha : A*A=1) (hb : B*B=1) (hab : Commute A B) (t : ℝ) :
    echo (unitaryEvolution H.val t) A B=
      unitaryEvolution H.val (-t)*unitaryEvolution (A*H.val*A) t*
        unitaryEvolution ((A*B)*H.val*(A*B)) (-t)*unitaryEvolution (B*H.val*B) t := by
  have hc : (A*B)*(A*B)=1 := by
    calc _ = A*(B*A)*B := by simp only [mul_assoc]
         _ = _ := by rw [hab.symm.eq,←mul_assoc A A B,ha,one_mul,hb]
  have conj (X : Register N) (hx : X*X=1) (s : ℝ) :
      unitaryEvolution (X*H.val*X) s=X*unitaryEvolution H.val s*X := by
    let u : (Register N)ˣ := ⟨X,X,hx,hx⟩
    simpa only [Matrix.inv_eq_left_inv hx] using unitaryEvolution_conj X H.val (show IsUnit X from ⟨u,rfl⟩) s
  rw [conj A ha,conj (A*B) hc,conj B hb,echo,←EigenlineSignals.adjoint_evolution H]
  have left (X : Register N) : A*(A*(B*X))=B*X := by rw [←mul_assoc,ha,one_mul]
  have right (X : Register N) : A*(B*(B*X))=A*X := by rw [←mul_assoc B B,hb,one_mul]
  simp only [mul_assoc,left,right]

private theorem list_mass_le {I : Type*} (s : List I) (f : I→ℝ) (M : ℝ) (h : ∀ i∈s, f i ≤ M) :
    (s.map f).sum ≤ s.length*M := by
  induction s with
  | nil => simp
  | cons a s ih =>
    have hl := ih (fun i hi => h i (List.mem_cons_of_mem _ hi))
    calc _ ≤ M+(s.length:ℝ)*M := add_le_add (h a List.mem_cons_self) hl
         _ = _ := by simp only [List.length_cons,Nat.cast_add,Nat.cast_one]; ring

local instance {R : Type*} [CStarAlgebra R] : NormedAlgebra ℚ R := .restrictScalars ℚ ℂ R

/-- The volume-free error depends only on pairwise commutators of the
four generators. A common large background can cancel in every bracket. -/
theorem four_flow_error {R : Type*} [CStarAlgebra R] (x y z w : R) (L t : ℝ) (ht : 0 ≤ t)
    (hsk : ∀ u ∈ [x,y,z,w], u ∈ skewAdjoint R)
    (hc : ∀ u ∈ [x,y,z,w], ∀ v ∈ [x,y,z,w], ‖u*v-v*u‖ ≤ L) :
    ‖exp (t • x)*exp (t • y)*exp (t • z)*exp (t • w)-exp (t • (x+y+z+w))‖ ≤ 16*L*t^2 := by
  let Z := [x,y,z,w]
  have hn : Z.length=4 := rfl
  have hinner (u : R) (h : u∈Z) := list_mass_le Z (fun v => ‖u*v-v*u‖) L (hc u h)
  have hm := list_mass_le Z _ ((Z.length:ℝ)*L) hinner
  rw [hn] at hm
  have he := lie_word_repeated_commutator_error Z hsk t ht 1 (by decide)
  simp only [Nat.cast_one,div_one,pow_one] at he
  have hu := he.trans (mul_le_mul_of_nonneg_left hm (sq_nonneg t))
  simpa only [Z,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,List.sum_cons,
    List.sum_nil,add_zero,mul_assoc,add_assoc,Nat.cast_ofNat] using (hu.trans_eq (by ring : t^2*(4*(4*L))=16*L*t^2))

end
end GaloisForLFunctions.HTGeometry.SpanningDensity.LocalEcho
