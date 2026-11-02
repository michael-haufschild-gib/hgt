import GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments.SparseSplineSchedule
import GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments.SplineCompatiblePrefixes

/-!
# Exact sparse spline prefixes

Each extension changes only the new block. Exact interpolation cancels the
current cone moments while preserving every old block and its three-node
unit-interval count. Stable prefixes define the infinite height sequence.
-/

open Finset Complex
noncomputable section
namespace GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments
variable {a b d D : ℝ}

/-- Exact finite prefixes retain the three-node count of every old block. -/
structure SparseSplinePrefix (s : SparsePrescribedSplineSchedule a b d D) (k : ℕ) where
  toSplinePrefix : SplinePrefix s.base k
  local_count : ∀ j, j < k → ∀ T : ℝ,
    ((univ : Finset (Fin (s.base.size j))).filter
      (fun l => toSplinePrefix.height j l ∈ Set.Icc T (T+1))).card ≤ 3

def emptySparseSplinePrefix (s : SparsePrescribedSplineSchedule a b d D) : SparseSplinePrefix s 0 where
  toSplinePrefix := emptySplinePrefix s.base
  local_count := by intro j hj; omega

/-- The next correction changes only the new block's heights. -/
lemma exists_sparseSplinePrefix_extension {s : SparsePrescribedSplineSchedule a b d D} {k : ℕ}
    (c : SparseSplinePrefix s k) (ha : 0 < a) (hb : 0 < b) (hd : 0 < d) (hdD : d < D) :
    ∃ c' : SparseSplinePrefix s (k+1), ∀ j, j < k → c'.toSplinePrefix.height j=c.toSplinePrefix.height j := by
  classical
  let r : s.base.frequency k → ℂ := fun u =>
    -((Real.exp (-s.base.level k*u.val) : ℂ)*s.base.prefixMoment c.toSplinePrefix.height k u.val)
  have hr : ∀ u, ‖r u‖ ≤ 2*(correctionMass (s.base.start+k))^2 := by
    intro u
    change ‖-((Real.exp (-s.base.level k*u.val) : ℂ)*s.base.prefixMoment c.toSplinePrefix.height k u.val)‖ ≤ _
    rw [norm_neg]
    exact c.toSplinePrefix.residual_small ha hb hd hdD u.property
  obtain ⟨v,hvinj,hvmem,hvcount,hvmoment⟩ := s.correct_sparse k r hr
  let γ : (j : ℕ) → Fin (s.base.size j) → ℝ := Function.update c.toSplinePrefix.height k v
  have hγk : γ k=v := Function.update_self _ _ _
  have hγo : ∀ j, j ≠ k → γ j=c.toSplinePrefix.height j := fun j hj => Function.update_of_ne hj _ _
  have hprefix : ∀ l, l ≤ k → ∀ u, s.base.prefixMoment γ l u=s.base.prefixMoment c.toSplinePrefix.height l u := by
    intro l hl u
    apply sum_congr rfl
    intro j hj
    have hjk : j ≠ k := by have := mem_range.mp hj; omega
    simp only [PrescribedSplineSchedule.blockMoment,PrescribedSplineSchedule.point,hγo j hjk]
  have hnew : ∀ u ∈ s.base.frequency k, s.base.prefixMoment γ (k+1) u=0 := by
    intro u hu
    have he : s.base.prefixMoment γ (k+1) u=s.base.prefixMoment c.toSplinePrefix.height k u+
        (Real.exp (s.base.level k*u) : ℂ)*
          ∑ j, splineMomentCoefficient ((s.base.level k : ℂ)+(v j : ℂ)*Complex.I)*phase u (v j) := by
      rw [PrescribedSplineSchedule.prefixMoment,sum_range_succ]
      change s.base.prefixMoment γ k u+s.base.blockMoment γ k u= _
      rw [hprefix k le_rfl,s.base.blockMoment_eq]
      simp only [PrescribedSplineSchedule.point,hγk]
    have hvu := hvmoment ⟨u,hu⟩
    change (∑ j, splineMomentCoefficient ((s.base.level k : ℂ)+(v j : ℂ)*Complex.I)*phase u (v j))=
      r ⟨u,hu⟩ at hvu
    rw [he,hvu]
    change s.base.prefixMoment c.toSplinePrefix.height k u+(Real.exp (s.base.level k*u) : ℂ)*
      (-((Real.exp (-s.base.level k*u) : ℂ)*s.base.prefixMoment c.toSplinePrefix.height k u))=0
    have hcancel : (Real.exp (s.base.level k*u) : ℂ)*(Real.exp (-s.base.level k*u) : ℂ)=1 := by
      rw [← Complex.ofReal_mul,← Real.exp_add]
      simp only [neg_mul,add_neg_cancel,Real.exp_zero,Complex.ofReal_one]
    rw [mul_neg,← mul_assoc,hcancel,one_mul,add_neg_cancel]
  let p' : SplinePrefix s.base (k+1) := {
    height := γ
    mem := by
      intro j hj l
      by_cases hjk : j=k
      · subst j
        rw [hγk]
        exact hvmem l
      · rw [hγo j hjk]
        exact c.toSplinePrefix.mem j (by omega) l
    injective := by
      intro j hj
      by_cases hjk : j=k
      · subst j
        rw [hγk]
        exact hvinj
      · rw [hγo j hjk]
        exact c.toSplinePrefix.injective j (by omega)
    zero := by
      intro l hl u hu
      by_cases hlk : l=k
      · subst l
        exact hnew u hu
      · rw [hprefix (l+1) (by omega)]
        exact c.toSplinePrefix.zero l (by omega) u hu
  }
  let c' : SparseSplinePrefix s (k+1) := {
    toSplinePrefix := p'
    local_count := by
      intro j hj T
      change ((univ : Finset (Fin (s.base.size j))).filter
        (fun l => γ j l ∈ Set.Icc T (T+1))).card ≤ 3
      by_cases hjk : j=k
      · subst j
        rw [hγk]
        exact hvcount T
      · rw [hγo j hjk]
        exact c.local_count j (by omega) T
  }
  exact ⟨c',fun j hj => hγo j (by omega)⟩

/-- All finite prefix moments vanish with exact spline coefficients and distinct
heights in each prescribed block. -/
theorem exists_sparse_spline_prefix_heights (s : SparsePrescribedSplineSchedule a b d D)
    (ha : 0 < a) (hb : 0 < b) (hd : 0 < d) (hdD : d < D) :
    ∃ γ : (k : ℕ) → Fin (s.base.size k) → ℝ,
      (∀ k j, γ k j ∈ Set.Icc (s.base.height k) (s.base.height k+s.base.span k)) ∧
      (∀ k, Function.Injective (γ k)) ∧
      (∀ k T, ((univ : Finset (Fin (s.base.size k))).filter
        (fun j => γ k j ∈ Set.Icc T (T+1))).card ≤ 3) ∧
      (∀ k u, u ∈ s.base.frequency k → s.base.prefixMoment γ (k+1) u=0) := by
  classical
  let next : (k : ℕ) → SparseSplinePrefix s k → SparseSplinePrefix s (k+1) :=
    fun _ c => (exists_sparseSplinePrefix_extension c ha hb hd hdD).choose
  have hnext : ∀ k (c : SparseSplinePrefix s k) j, j < k → (next k c).toSplinePrefix.height j=c.toSplinePrefix.height j :=
    fun _ c => (exists_sparseSplinePrefix_extension c ha hb hd hdD).choose_spec
  let stages : (k : ℕ) → SparseSplinePrefix s k := Nat.rec (emptySparseSplinePrefix s) next
  have hstep : ∀ k j, j < k → (stages (k+1)).toSplinePrefix.height j=(stages k).toSplinePrefix.height j :=
    fun k j hj => hnext k (stages k) j hj
  let γ : (k : ℕ) → Fin (s.base.size k) → ℝ := fun k => (stages (k+1)).toSplinePrefix.height k
  have hstable : ∀ k j, j < k → (stages k).toSplinePrefix.height j=γ j := by
    intro k
    induction k with
    | zero => intro j hj; omega
    | succ k ih =>
      intro j hj
      by_cases hjk : j < k
      · rw [hstep k j hjk,ih j hjk]
      · have he : j=k := by omega
        subst j
        rfl
  refine ⟨γ,?_,?_,?_,?_⟩
  · intro k j
    exact (stages (k+1)).toSplinePrefix.mem k (Nat.lt_succ_self k) j
  · intro k
    exact (stages (k+1)).toSplinePrefix.injective k (Nat.lt_succ_self k)
  · intro k T
    exact (stages (k+1)).local_count k (Nat.lt_succ_self k) T
  · intro k u hu
    calc
      s.base.prefixMoment γ (k+1) u=s.base.prefixMoment (stages (k+1)).toSplinePrefix.height (k+1) u := by
        apply sum_congr rfl
        intro j hj
        simp only [PrescribedSplineSchedule.blockMoment,PrescribedSplineSchedule.point,
          hstable (k+1) j (mem_range.mp hj)]
      _ = 0 := (stages (k+1)).toSplinePrefix.zero k (Nat.lt_succ_self k) u hu

#print axioms exists_sparse_spline_prefix_heights
end GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments
