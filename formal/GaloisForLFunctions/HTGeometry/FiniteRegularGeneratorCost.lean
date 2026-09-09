import GaloisForLFunctions.HTGeometry.FiniteRegularReynolds

/-!
# Generator costs for the complete finite regular average

Finite group generation supplies actual finite word-cost certificates. Unitary
multiplication adds displacement bounds and inversion preserves them. Averaging
all certified costs against the exact Reynolds identity gives a source-independent
finite comparison constant for the two generator energies. The cost is constructed,
not a supplied graph gap; no bound uniform in the group is asserted.
-/

open scoped BigOperators
namespace GaloisForLFunctions.HTGeometry.FiniteRegularGeneratorCost
open GaloisForLFunctions.HTGeometry
noncomputable section
variable {G : Type*} [Group G]

/-- A finite cost certificate made from the two actual generators and their inverses. -/
inductive GeneratedCost (s t : G) : G → ℕ → Prop
  | one : GeneratedCost s t 1 0
  | left : GeneratedCost s t s 1
  | right : GeneratedCost s t t 1
  | mul {g h : G} {a b : ℕ} : GeneratedCost s t g a → GeneratedCost s t h b →
      GeneratedCost s t (g*h) (a+b)
  | inv {g : G} {a : ℕ} : GeneratedCost s t g a → GeneratedCost s t g⁻¹ a

theorem exists_cost (s t : G) {g : G} (hg : g ∈ Subgroup.closure ({s,t}:Set G)) :
    ∃ n : ℕ, GeneratedCost s t g n := by
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact ⟨1,GeneratedCost.left⟩
    · exact ⟨1,GeneratedCost.right⟩
  | one => exact ⟨0,GeneratedCost.one⟩
  | mul x y hx hy ihx ihy =>
    rcases ihx with ⟨a,ha⟩
    rcases ihy with ⟨b,hb⟩
    exact ⟨a+b,ha.mul hb⟩
  | inv x hx ih =>
    rcases ih with ⟨a,ha⟩
    exact ⟨a,ha.inv⟩

variable [Fintype G]

theorem regular_one (v : EuclideanSpace ℂ G) : finiteRegularUnitary (1:G) v=v := by
  ext q
  simp [finiteRegularUnitary_apply]

theorem regular_mul (g h : G) (v : EuclideanSpace ℂ G) :
    finiteRegularUnitary (g*h) v=finiteRegularUnitary g (finiteRegularUnitary h v) := by
  rw [finiteRegularUnitary_mul]
  rfl

theorem displacement_mul_le (g h : G) (v : EuclideanSpace ℂ G) :
    ‖finiteRegularUnitary (g*h) v-v‖ ≤
      ‖finiteRegularUnitary g v-v‖+‖finiteRegularUnitary h v-v‖ := by
  rw [regular_mul]
  calc
    ‖finiteRegularUnitary g (finiteRegularUnitary h v)-v‖ =
        ‖finiteRegularUnitary g (finiteRegularUnitary h v-v)+(finiteRegularUnitary g v-v)‖ := by
      congr 1
      rw [map_sub]
      abel
    _ ≤ ‖finiteRegularUnitary g (finiteRegularUnitary h v-v)‖+‖finiteRegularUnitary g v-v‖ := norm_add_le _ _
    _ = _ := by rw [LinearIsometryEquiv.norm_map]; ring

theorem displacement_inv (g : G) (v : EuclideanSpace ℂ G) :
    ‖finiteRegularUnitary g⁻¹ v-v‖=‖finiteRegularUnitary g v-v‖ := by
  calc
    ‖finiteRegularUnitary g⁻¹ v-v‖ = ‖finiteRegularUnitary g (finiteRegularUnitary g⁻¹ v-v)‖ :=
      (LinearIsometryEquiv.norm_map _ _).symm
    _ = ‖v-finiteRegularUnitary g v‖ := by
      rw [map_sub,← regular_mul,mul_inv_cancel,regular_one]
    _ = _ := norm_sub_rev _ _

theorem generated_displacement_le (s t : G) {g : G} {n : ℕ}
    (h : GeneratedCost s t g n) (v : EuclideanSpace ℂ G) :
    ‖finiteRegularUnitary g v-v‖ ≤ (n:ℝ)*
      (‖finiteRegularUnitary s v-v‖+‖finiteRegularUnitary t v-v‖) := by
  induction h with
  | one => simp [regular_one]
  | left => simp only [Nat.cast_one,one_mul]; exact le_add_of_nonneg_right (norm_nonneg _)
  | right => simp only [Nat.cast_one,one_mul]; exact le_add_of_nonneg_left (norm_nonneg _)
  | @mul g h a b ha hb iha ihb =>
    have hh := displacement_mul_le g h v
    push_cast
    nlinarith
  | inv ha ih => rw [displacement_inv]; exact ih

variable (s t : G) (hgen : Subgroup.closure ({s,t}:Set G)=⊤)

/-- Least certified generator cost; it depends only on the finite group and its two generators. -/
def cost (g : G) : ℕ := by
  classical
  exact Nat.find (exists_cost s t (g:=g) (by rw [hgen]; trivial))

omit [Fintype G] in
theorem cost_spec (g : G) : GeneratedCost s t g (cost s t hgen g) := by
  classical
  exact Nat.find_spec _

/-- A finite, source-independent comparison cost. No level-uniform bound is asserted. -/
def comparisonConstant : ℝ := 1+(Fintype.card G:ℝ)⁻¹*∑ g : G, (cost s t hgen g:ℝ)^2

theorem comparisonConstant_pos : 0 < comparisonConstant s t hgen := by
  have h : 0 ≤ (Fintype.card G:ℝ)⁻¹*∑ g : G, (cost s t hgen g:ℝ)^2 :=
    mul_nonneg (by positivity) (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  unfold comparisonConstant
  linarith

/-- Actual generator displacements control the full regular mean-zero variance
with the finite cost constructed from group generation. -/
theorem variance_le_generator_energy (v : EuclideanSpace ℂ G) :
    ‖v-finiteRegularAverage v‖^2 ≤ comparisonConstant s t hgen*
      (‖finiteRegularUnitary s v-v‖^2+‖finiteRegularUnitary t v-v‖^2) := by
  let D := ‖finiteRegularUnitary s v-v‖+‖finiteRegularUnitary t v-v‖
  let E := ‖finiteRegularUnitary s v-v‖^2+‖finiteRegularUnitary t v-v‖^2
  have hE : 0 ≤ E := add_nonneg (sq_nonneg _) (sq_nonneg _)
  have hD : D^2 ≤ 2*E := by
    dsimp [D,E]
    nlinarith [sq_nonneg (‖finiteRegularUnitary s v-v‖-‖finiteRegularUnitary t v-v‖)]
  have hpoint (g : G) : ‖finiteRegularUnitary g v-v‖^2 ≤
      2*(cost s t hgen g:ℝ)^2*E := by
    have hb := generated_displacement_le s t (cost_spec s t hgen g) v
    change ‖finiteRegularUnitary g v-v‖ ≤ (cost s t hgen g:ℝ)*D at hb
    have hc : 0 ≤ (cost s t hgen g:ℝ) := by positivity
    have hd : 0 ≤ D := add_nonneg (norm_nonneg _) (norm_nonneg _)
    have hsq : ‖finiteRegularUnitary g v-v‖^2 ≤ ((cost s t hgen g:ℝ)*D)^2 := by
      nlinarith [norm_nonneg (finiteRegularUnitary g v-v)]
    nlinarith [mul_nonneg (sq_nonneg (cost s t hgen g:ℝ)) (sub_nonneg.mpr hD)]
  have hsum := Finset.sum_le_sum (fun g (_ : g ∈ Finset.univ) => hpoint g)
  simp only [← Finset.sum_mul,← Finset.mul_sum] at hsum
  have hcard : 0 < (Fintype.card G:ℝ) := by exact_mod_cast Fintype.card_pos
  have hh := finiteRegularAverage_energy v
  have hn := finiteRegularAverage_norm_decomposition v
  have hmul := mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr (by positivity : 0 ≤ 2*(Fintype.card G:ℝ)))
  have hcoef : (2*(Fintype.card G:ℝ))⁻¹*(2*(∑ g : G, (cost s t hgen g:ℝ)^2)*E)=
      (Fintype.card G:ℝ)⁻¹*(∑ g : G, (cost s t hgen g:ℝ)^2)*E := by rw [mul_inv_rev]; ring
  rw [hcoef] at hmul
  rw [hh] at hmul
  change ‖v-finiteRegularAverage v‖^2 ≤ (1+(Fintype.card G:ℝ)⁻¹*
      ∑ g : G, (cost s t hgen g:ℝ)^2)*E
  nlinarith

include hgen in
theorem generator_fixed_iff_average_fixed (v : EuclideanSpace ℂ G) :
    (finiteRegularUnitary s v=v ∧ finiteRegularUnitary t v=v) ↔
      finiteRegularAverage v=v := by
  constructor
  · rintro ⟨hs,ht⟩
    have h := variance_le_generator_energy s t hgen v
    rw [hs,ht,sub_self,norm_zero,zero_pow (by decide : 2≠0),add_zero,mul_zero] at h
    have hn : ‖v-finiteRegularAverage v‖=0 := by nlinarith [norm_nonneg (v-finiteRegularAverage v)]
    exact (sub_eq_zero.mp (norm_eq_zero.mp hn)).symm
  · intro h
    have hall := (finiteRegularAverage_fixed_iff v).mp h
    exact ⟨hall s,hall t⟩

end
end GaloisForLFunctions.HTGeometry.FiniteRegularGeneratorCost
