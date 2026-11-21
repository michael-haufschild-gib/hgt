import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # Strict first variation at the minimizing directions of a compact family -/
open Set
namespace GaloisForLFunctions.HTGeometry.FirstGate
noncomputable section

/-- A derivative positive on every zero of a nonnegative function has a
uniform positive lower bound after adding a suitable multiple of that
function. The directed open cover avoids choosing eigenvalue branches. -/
theorem compact_contact_margin {X : Type*} [TopologicalSpace X] [CompactSpace X] [Nonempty X]
    (f g : X → ℝ) (hf : Continuous f) (hg : Continuous g)
    (hn : ∀ v, 0≤f v) (hz : ∀ v, f v=0 → 0 < g v) :
    ∃ A : ℕ, ∃ δ > (0:ℝ), ∀ v, δ ≤ (A:ℝ)*f v+g v := by
  let U (j : ℕ) := {v | 0 < (j:ℝ)*f v+g v}
  have hopen (j : ℕ) : IsOpen (U j) := isOpen_lt continuous_const ((hf.const_mul _).add hg)
  have hcover : (univ : Set X) ⊆ ⋃ j, U j := by
    intro v _
    by_cases h : f v=0
    · exact mem_iUnion.mpr ⟨0,by simpa only [U,mem_setOf_eq,Nat.cast_zero,zero_mul,zero_add] using hz v h⟩
    have hpos := lt_of_le_of_ne (hn v) (Ne.symm h)
    obtain ⟨j,hj⟩ := exists_nat_gt (-g v/f v)
    exact mem_iUnion.mpr ⟨j,by change 0 < (j:ℝ)*f v+g v; linarith only [(div_lt_iff₀ hpos).mp hj]⟩
  have hmono : Monotone U := by
    intro i j hij v hv
    have h := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hij : (i:ℝ)≤j) (hn v)
    exact lt_of_lt_of_le hv (add_le_add h le_rfl)
  obtain ⟨A,hA⟩ := isCompact_univ.elim_directed_cover U hopen hcover hmono.directed_le
  let F := fun v => (A:ℝ)*f v+g v
  obtain ⟨w,_,hw⟩ := isCompact_univ.exists_isMinOn (univ_nonempty : (univ : Set X).Nonempty)
    (((hf.const_mul (A:ℝ)).add hg).continuousOn)
  exact ⟨A,F w,hA (mem_univ w),fun v => hw (mem_univ v)⟩

/-- The first-order gain absorbs any uniform quadratic error, even when
the original minimizing space has dimension greater than one. -/
theorem strict_quadratic_margin {X : Type*} [TopologicalSpace X] [CompactSpace X] [Nonempty X]
    (f g : X → ℝ) (hf : Continuous f) (hg : Continuous g)
    (hn : ∀ v, 0≤f v) (hz : ∀ v, f v=0 → 0 < g v) {M : ℝ} (hM : 0≤M) :
    ∃ h > (0:ℝ), ∃ c > (0:ℝ), ∀ t ∈ Ioc 0 h, ∀ v, c*t ≤ f v+t*g v-M*t^2 := by
  obtain ⟨A,δ,hδ,h⟩ := compact_contact_margin f g hf hg hn hz
  let a := 1/((A:ℝ)+1)
  let b := δ/(2*(M+1))
  have ha : 0 < a := by dsimp only [a]; positivity
  have hb : 0 < b := by dsimp only [b]; positivity
  refine ⟨min a b,lt_min ha hb,δ/2,half_pos hδ,?_⟩
  intro t ht v
  have hta := (le_div_iff₀ (by positivity : 0 < (A:ℝ)+1)).mp (ht.2.trans (min_le_left a b))
  have htb := (le_div_iff₀ (by positivity : 0 < 2*(M+1))).mp (ht.2.trans (min_le_right a b))
  have h1 := mul_le_mul_of_nonneg_right (show t*(A:ℝ) ≤ 1 by linarith only [hta,ht.1]) (hn v)
  have h2 := mul_le_mul_of_nonneg_left (h v) ht.1.le
  have h3 := mul_le_mul_of_nonneg_right (show M*t ≤ δ/2 by linarith only [htb,ht.1]) ht.1.le
  linarith only [h1,h2,h3]

#print axioms strict_quadratic_margin
end
end GaloisForLFunctions.HTGeometry.FirstGate
