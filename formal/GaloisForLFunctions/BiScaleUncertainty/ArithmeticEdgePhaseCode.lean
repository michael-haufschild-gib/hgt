import GaloisForLFunctions.BiScaleUncertainty.ArithmeticEdgeTranslation
import Mathlib.Data.ZMod.IntUnitsPower
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.FinCases

/-!
# The explicit binary phase code for arithmetic edge sieves

Columns are active arithmetic orders. Rows are active triangle comparisons and four-cycle parity
sums; repeated-vertex cycle rows are harmless redundant relations. The resulting binary kernel is
exactly equality of the actual fourth-lag arrays under coordinate sign changes. Its cardinality
follows from Mathlib rank-nullity; neither the sign character nor rank-nullity is a new mechanism.
-/

open scoped BigOperators
noncomputable section
set_option autoImplicit false
namespace GaloisForLFunctions.BiScaleUncertainty.SieveMoments.ArithmeticEdges
namespace BinaryPhase
def sign (x : ZMod 2) : ℝ := ((((-1 : ℤˣ) ^ x : ℤˣ) : ℤ) : ℝ)

@[simp] theorem sign_zero : sign 0 = 1 := by simp [sign]
@[simp] theorem sign_one : sign 1 = -1 := by simp [sign]

theorem sign_add (x y : ZMod 2) : sign (x+y) = sign x * sign y := by
  simp only [sign,uzpow_add,Units.val_mul,Int.cast_mul]

theorem eq_zero_or_one (x : ZMod 2) : x=0 ∨ x=1 := by
  have hv := ZMod.val_lt x
  have hh : x.val=0 ∨ x.val=1 := by omega
  rcases hh with h | h
  · left
    apply ZMod.val_injective 2
    simpa using h
  · right
    apply ZMod.val_injective 2
    simpa only [ZMod.val_one_eq_one_mod] using h

theorem sign_injective : Function.Injective sign := by
  intro x y h
  rcases eq_zero_or_one x with hx | hx
  · rcases eq_zero_or_one y with hy | hy
    · exact hx.trans hy.symm
    · rw [hx,hy,sign_zero,sign_one] at h
      norm_num at h
  · rcases eq_zero_or_one y with hy | hy
    · rw [hx,hy,sign_one,sign_zero] at h
      norm_num at h
    · exact hx.trans hy.symm

theorem sign_sq (x : ZMod 2) : sign x ^ 2 = 1 := by
  rcases eq_zero_or_one x with rfl | rfl <;> norm_num

theorem sign_nonzero (x : ZMod 2) : sign x ≠ 0 := by
  have := sign_sq x
  intro h
  rw [h] at this
  norm_num at this

theorem sign_eq_one (x : ZMod 2) : sign x = 1 ↔ x=0 := by
  rw [← sign_zero,sign_injective.eq_iff]

theorem sign_mul_eq_one (x y : ZMod 2) : sign x * sign y = 1 ↔ x+y=0 := by
  rw [← sign_add,sign_eq_one]

theorem add_self (x : ZMod 2) : x+x=0 := by
  fin_cases x <;> decide
end BinaryPhase

namespace BinaryPhase

theorem triangle_relation (A B C : ℝ) (x y z : ZMod 2) :
    A*B*C^2 = (sign x*A)*(sign y*B)*(sign z*C)^2 ↔
      (A ≠ 0 ∧ B ≠ 0 ∧ C ≠ 0 → x+y=0) := by
  have hid : (sign x*A)*(sign y*B)*(sign z*C)^2 = sign (x+y)*(A*B*C^2) := by
    rw [mul_pow,sign_sq,one_mul,sign_add]
    ring
  rw [hid]
  by_cases hA : A=0
  · simp [hA]
  by_cases hB : B=0
  · simp [hB]
  by_cases hC : C=0
  · simp [hC]
  have hn : A*B*C^2 ≠ 0 := mul_ne_zero (mul_ne_zero hA hB) (pow_ne_zero _ hC)
  constructor
  · intro h _
    apply (sign_eq_one _).mp
    apply mul_right_cancel₀ hn
    simpa only [one_mul] using h.symm
  · intro h
    rw [h ⟨hA,hB,hC⟩,sign_zero,one_mul]

theorem cycle_relation (A B C E : ℝ) (x y z w : ZMod 2) :
    A*B*C*E = (sign x*A)*(sign y*B)*(sign z*C)*(sign w*E) ↔
      (A ≠ 0 ∧ B ≠ 0 ∧ C ≠ 0 ∧ E ≠ 0 → x+y+z+w=0) := by
  have hid : (sign x*A)*(sign y*B)*(sign z*C)*(sign w*E) =
      sign (x+y+z+w)*(A*B*C*E) := by
    simp only [sign_add]
    ring
  rw [hid]
  by_cases hA : A=0
  · simp [hA]
  by_cases hB : B=0
  · simp [hB]
  by_cases hC : C=0
  · simp [hC]
  by_cases hE : E=0
  · simp [hE]
  have hn : A*B*C*E ≠ 0 := mul_ne_zero (mul_ne_zero (mul_ne_zero hA hB) hC) hE
  constructor
  · intro h _
    apply (sign_eq_one _).mp
    apply mul_right_cancel₀ hn
    simpa only [one_mul] using h.symm
  · intro h
    rw [h ⟨hA,hB,hC,hE⟩,sign_zero,one_mul]

end BinaryPhase

namespace Blocks
variable {V : Type*} [Fintype V] (D : Blocks V)

/-- Active arithmetic orders, independent of the extra cutoff parameter. -/
def active (a : ℕ → ℝ) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 (D.cutoff 0)).filter (fun q => D.profile a q ≠ 0)

theorem mem_active_iff (a : ℕ → ℝ) (q : ℕ) :
    q ∈ D.active a ↔ D.profile a q ≠ 0 := by
  classical
  simp only [active,Finset.mem_filter]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨?_,h⟩
    by_contra hn
    apply h
    apply D.profile_zero
    rintro ⟨u,v,_,rfl⟩
    exact hn (D.order_mem_cutoff 0 u v)

abbrev Phase (a : ℕ → ℝ) := {q // q ∈ D.active a} → ZMod 2

/-- Extend an active sign coordinate by zero outside the active support. -/
def phaseEval (a : ℕ → ℝ) (q : ℕ) : D.Phase a →ₗ[ZMod 2] ZMod 2 := by
  classical
  exact if h : q ∈ D.active a then LinearMap.proj ⟨q,h⟩ else 0

theorem phaseEval_mem (a : ℕ → ℝ) (x : D.Phase a) (q : ℕ)
    (hq : q ∈ D.active a) : D.phaseEval a q x = x ⟨q,hq⟩ := by
  classical
  simp [phaseEval,hq]

/-- The canonical coordinate profile produced by an arbitrary binary sign vector. -/
def twist (a : ℕ → ℝ) (x : D.Phase a) (q : ℕ) : ℝ :=
  BinaryPhase.sign (D.phaseEval a q x) * D.profile a q

theorem profile_twist (a : ℕ → ℝ) (x : D.Phase a) (q : ℕ) :
    D.profile (D.twist a x) q = D.twist a x q := by
  classical
  by_cases h : ∃ u v, u ≠ v ∧ q = D.order u v
  · simp [profile,h]
  · simp [profile,twist,h]

theorem edgeAmplitude_twist (a : ℕ → ℝ) (x : D.Phase a) (u v : V) :
    D.edgeAmplitude (D.twist a x) u v =
      BinaryPhase.sign (D.phaseEval a (D.order u v) x) * D.edgeAmplitude a u v := by
  classical
  by_cases h : u=v
  · simp [edgeAmplitude,h]
  · simp [edgeAmplitude,twist,h,D.profile_order a h]

theorem twist_square (a : ℕ → ℝ) (x : D.Phase a) (q : ℕ) :
    (D.twist a x q)^2 = (D.profile a q)^2 := by
  simp only [twist,mul_pow,BinaryPhase.sign_sq,one_mul]

theorem twist_injective (a : ℕ → ℝ) : Function.Injective (D.twist a) := by
  intro x y h
  funext q
  apply BinaryPhase.sign_injective
  apply mul_right_cancel₀ ((D.mem_active_iff a q).mp q.property)
  have hh := congrFun h q.val
  simpa only [twist,D.phaseEval_mem a x q.val q.property,
    D.phaseEval_mem a y q.val q.property] using hh

def TriangleActive (a : ℕ → ℝ) (u v w : V) : Prop :=
  D.edgeAmplitude a u v ≠ 0 ∧ D.edgeAmplitude a u w ≠ 0 ∧
    D.edgeAmplitude a v w ≠ 0

def CycleActive (a : ℕ → ℝ) (u v w z : V) : Prop :=
  D.edgeAmplitude a u v ≠ 0 ∧ D.edgeAmplitude a v w ≠ 0 ∧
    D.edgeAmplitude a w z ≠ 0 ∧ D.edgeAmplitude a z u ≠ 0

/-- Rows are explicit active-triangle comparisons and active-four-cycle parities. -/
def phaseMap (a : ℕ → ℝ) :
    D.Phase a →ₗ[ZMod 2] (Sum (V × V × V) (V × V × V × V) → ZMod 2) := by
  classical
  exact LinearMap.pi fun r => match r with
    | .inl (u,v,w) => if D.TriangleActive a u v w then
        D.phaseEval a (D.order u v) + D.phaseEval a (D.order u w) else 0
    | .inr (u,v,w,z) => if D.CycleActive a u v w z then
        D.phaseEval a (D.order u v) + D.phaseEval a (D.order v w) +
          D.phaseEval a (D.order w z) + D.phaseEval a (D.order z u) else 0

theorem mem_phase_kernel (a : ℕ → ℝ) (x : D.Phase a) :
    x ∈ LinearMap.ker (D.phaseMap a) ↔
      (∀ u v w, D.TriangleActive a u v w →
        D.phaseEval a (D.order u v) x + D.phaseEval a (D.order u w) x = 0) ∧
      (∀ u v w z, D.CycleActive a u v w z →
        D.phaseEval a (D.order u v) x + D.phaseEval a (D.order v w) x +
          D.phaseEval a (D.order w z) x + D.phaseEval a (D.order z u) x = 0) := by
  classical
  constructor
  · intro h
    have hh := LinearMap.mem_ker.mp h
    constructor
    · intro u v w ht
      have hv := congrFun hh (Sum.inl (u,v,w))
      simpa [phaseMap,ht] using hv
    · intro u v w z ht
      have hv := congrFun hh (Sum.inr (u,v,w,z))
      simpa [phaseMap,ht] using hv
  · rintro ⟨ht,hc⟩
    apply LinearMap.mem_ker.mpr
    funext r
    rcases r with ⟨u,v,w⟩ | ⟨u,v,w,z⟩
    · by_cases h : D.TriangleActive a u v w
      · simpa [phaseMap,h] using ht u v w h
      · simp [phaseMap,h]
    · by_cases h : D.CycleActive a u v w z
      · simpa [phaseMap,h] using hc u v w z h
      · simp [phaseMap,h]

/-- The explicit binary operator has exactly the already-proved arithmetic quartic relations. -/
theorem quartic_twist_iff_kernel (a : ℕ → ℝ) (x : D.Phase a) :
    QuarticRelations (D.edgeAmplitude a) (D.edgeAmplitude (D.twist a x)) ↔
      x ∈ LinearMap.ker (D.phaseMap a) := by
  rw [D.mem_phase_kernel]
  constructor
  · intro H
    constructor
    · intro u v w ht
      have hh := H.triangle u v w
      simp only [D.edgeAmplitude_twist] at hh
      exact (BinaryPhase.triangle_relation _ _ _ _ _ _).mp hh ht
    · intro u v w z ht
      have hh := H.cycle u v w z
      simp only [D.edgeAmplitude_twist] at hh
      exact (BinaryPhase.cycle_relation _ _ _ _ _ _ _ _).mp hh ht
  · rintro ⟨ht,hc⟩
    constructor
    · intro u v
      simp only [D.edgeAmplitude_twist,mul_pow,BinaryPhase.sign_sq,one_mul]
    · intro u v w
      simp only [D.edgeAmplitude_twist]
      exact (BinaryPhase.triangle_relation _ _ _ _ _ _).mpr (ht u v w)
    · intro u v w z
      simp only [D.edgeAmplitude_twist]
      exact (BinaryPhase.cycle_relation _ _ _ _ _ _ _ _).mpr (hc u v w z)

/-- Kernel membership is exactly equality of the actual complete fourth-lag arrays. -/
theorem fourth_twist_iff_kernel (n : ℕ) (a : ℕ → ℝ) (x : D.Phase a) :
    (∀ h : Fin 4 → ℕ, translatedMoment (D.cutoff n) (D.weights n a) h =
      translatedMoment (D.cutoff n) (D.weights n (D.twist a x)) h) ↔
        x ∈ LinearMap.ker (D.phaseMap a) := by
  rw [D.fourth_between_weights_iff,D.quartic_twist_iff_kernel]

theorem order_mem_active_of_edge_ne (a : ℕ → ℝ) (u v : V)
    (h : D.edgeAmplitude a u v ≠ 0) : D.order u v ∈ D.active a := by
  classical
  have huv : u ≠ v := by
    intro he
    apply h
    simp [edgeAmplitude,he]
  apply (D.mem_active_iff a _).mpr
  simpa only [D.profile_order a huv,edgeAmplitude,if_neg huv] using h

theorem phaseEval_const_of_edge_ne (a : ℕ → ℝ) (u v : V) (ε : ZMod 2)
    (h : D.edgeAmplitude a u v ≠ 0) :
    D.phaseEval a (D.order u v) (fun _ => ε) = ε := by
  rw [D.phaseEval_mem a _ _ (D.order_mem_active_of_edge_ne a u v h)]

/-- Both common signs lie in the explicit code, on every support including the empty one. -/
theorem const_mem_phase_kernel (a : ℕ → ℝ) (ε : ZMod 2) :
    (fun _ => ε) ∈ LinearMap.ker (D.phaseMap a) := by
  rw [D.mem_phase_kernel]
  constructor
  · intro u v w h
    rw [D.phaseEval_const_of_edge_ne a u v ε h.1,
      D.phaseEval_const_of_edge_ne a u w ε h.2.1]
    exact BinaryPhase.add_self ε
  · intro u v w z h
    rw [D.phaseEval_const_of_edge_ne a u v ε h.1,
      D.phaseEval_const_of_edge_ne a v w ε h.2.1,
      D.phaseEval_const_of_edge_ne a w z ε h.2.2.1,
      D.phaseEval_const_of_edge_ne a z u ε h.2.2.2,
      BinaryPhase.add_self,zero_add,BinaryPhase.add_self]

/-- Rank of the explicit finite triangle/cycle parity operator. -/
def phaseRank (a : ℕ → ℝ) : ℕ :=
  Module.finrank (ZMod 2) (LinearMap.range (D.phaseMap a))

theorem phase_rank_nullity (a : ℕ → ℝ) :
    D.phaseRank a + Module.finrank (ZMod 2) (LinearMap.ker (D.phaseMap a)) =
      (D.active a).card := by
  have h := (D.phaseMap a).finrank_range_add_finrank_ker
  simpa only [Phase,Module.finrank_fintype_fun_eq_card,Fintype.card_coe,phaseRank] using h

theorem phase_kernel_card (a : ℕ → ℝ) :
    Nat.card (LinearMap.ker (D.phaseMap a)) = 2^((D.active a).card-D.phaseRank a) := by
  have h := D.phase_rank_nullity a
  have hd : Module.finrank (ZMod 2) (LinearMap.ker (D.phaseMap a)) =
      (D.active a).card-D.phaseRank a := by omega
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2),hd,Nat.card_eq_fintype_card,ZMod.card]

end Blocks
end GaloisForLFunctions.BiScaleUncertainty.SieveMoments.ArithmeticEdges
