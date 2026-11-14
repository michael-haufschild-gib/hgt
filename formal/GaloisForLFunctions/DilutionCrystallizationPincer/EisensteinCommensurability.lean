import GaloisForLFunctions.HilbertMetric.RotationalSubgroupRigidity
import GaloisForLFunctions.HilbertMetric.SeparatedConfigurations
import GaloisForLFunctions.MetaplecticMobiusDescent.EisensteinNearestPoint
import GaloisForLFunctions.FamilyContinuationTheory.EisensteinNormSquareDescent

/-!
# Incommensurate triangular lattices fill the plane

The sum of an Eisenstein lattice and a complex multiple of that lattice
is invariant under a nonreal cube root of unity. Its closure is therefore
either discrete or the entire plane. In the discrete case, nearest-point
reduction and compactness force a nonzero integer multiple of the scale
into the original lattice. Square-factor descent then shows that an
integral squared scale must be an Eisenstein norm.

Thus the arithmetic obstruction of Lemma 7.5 of
Kittipassorn--Phetmak--Sriamorn forces density in the full plane,
strengthening its conclusion that the closure contains a line.
-/

noncomputable section
namespace GaloisForLFunctions.DilutionCrystallizationPincer.EisensteinCommensurability

open Set Metric HilbertMetric
open MetaplecticMobiusDescent.Eisenstein
open FamilyContinuationTheory.EisensteinNorm

/-- The sum of the original triangular lattice and its complex multiple. -/
def mixedLattice (α : ℂ) : AddSubgroup ℂ where
  carrier := {z | ∃ a b : O, z = ringComplex a + α * ringComplex b}
  zero_mem' := ⟨0, 0, by simp only [map_zero, mul_zero, add_zero]⟩
  add_mem' := by
    rintro x y ⟨a, b, rfl⟩ ⟨c, d, rfl⟩
    exact ⟨a + c, b + d, by simp only [map_add]; ring⟩
  neg_mem' := by
    rintro x ⟨a, b, rfl⟩
    exact ⟨-a, -b, by simp only [map_neg]; ring⟩

def mixedClosure (α : ℂ) : AddSubgroup ℂ := (mixedLattice α).topologicalClosure

theorem isClosed_mixedClosure (α : ℂ) : IsClosed (mixedClosure α : Set ℂ) :=
  isClosed_closure

theorem ring_mem_mixedClosure (α : ℂ) (a : O) : ringComplex a ∈ mixedClosure α :=
  subset_closure ⟨a, 0, by simp only [map_zero, mul_zero, add_zero]⟩

theorem mul_ring_mem_mixedClosure (α : ℂ) (a : O) :
    α * ringComplex a ∈ mixedClosure α :=
  subset_closure ⟨0, a, by simp only [map_zero, zero_add]⟩

theorem omega_mul_mem_mixedLattice (α : ℂ) {z : ℂ} (hz : z ∈ mixedLattice α) :
    ringComplex omega * z ∈ mixedLattice α := by
  obtain ⟨a, b, rfl⟩ := hz
  exact ⟨omega * a, omega * b, by simp only [map_mul]; ring⟩

/-- Both lattices have the same order-three rotational symmetry. -/
theorem omega_mul_mem_mixedClosure (α : ℂ) {z : ℂ} (hz : z ∈ mixedClosure α) :
    ringComplex omega * z ∈ mixedClosure α := by
  have hc : IsClosed ((fun x : ℂ => ringComplex omega * x) ⁻¹'
      (mixedClosure α : Set ℂ)) :=
    (isClosed_mixedClosure α).preimage (continuous_const.mul continuous_id)
  have hsub : (mixedLattice α : Set ℂ) ⊆ (fun x : ℂ => ringComplex omega * x) ⁻¹'
      (mixedClosure α : Set ℂ) := fun x hx =>
    subset_closure (omega_mul_mem_mixedLattice α hx)
  exact closure_minimal hsub hc hz

private theorem omega_im_ne_zero : (ringComplex omega).im ≠ 0 := by
  intro h
  have hs := complex_omega_coordinates.2
  rw [h, zero_pow two_ne_zero] at hs
  linarith only [hs]

/-- A proper closure has a uniform separation scale. -/
theorem mixedClosure_separated (α : ℂ) (hα : mixedClosure α ≠ ⊤) :
    ∃ ε > 0, ∀ x ∈ mixedClosure α, ∀ y ∈ mixedClosure α,
      x ≠ y → ε ≤ dist x y :=
  separated_of_closed_subgroup_nonreal_mul (mixedClosure α) (isClosed_mixedClosure α)
    (ringComplex omega) omega_im_ne_zero (fun _ h => omega_mul_mem_mixedClosure α h) hα

/-- A discrete superlattice forces an integral multiple of the scale into the original lattice. -/
theorem exists_nat_mul_mem_of_mixedClosure_ne_top (α : ℂ) (hα : mixedClosure α ≠ ⊤) :
    ∃ m : ℕ, 0 < m ∧ ∃ a : O, (m : ℂ) * α = ringComplex a := by
  obtain ⟨ε, hε, hsep⟩ := mixedClosure_separated α hα
  choose q hq using fun n : ℕ => exists_eisenstein_distance_sq_le_third ((n : ℂ) * α)
  let r : ℕ → ℂ := fun n => (n : ℂ) * α - ringComplex (q n)
  have hrmem (n : ℕ) : r n ∈ mixedClosure α := by
    apply (mixedClosure α).sub_mem ?_ (ring_mem_mixedClosure α (q n))
    simpa only [map_natCast, mul_comm] using mul_ring_mem_mixedClosure α (n : O)
  have hrnorm (n : ℕ) : ‖r n‖ ≤ 1 := by
    have hn := hq n
    rw [Complex.normSq_eq_norm_sq] at hn
    change ‖r n‖ ^ 2 ≤ 1 / 3 at hn
    nlinarith only [hn, sq_nonneg (‖r n‖ - 1)]
  have hfinite : (range r).Finite :=
    finite_of_dist_separated_of_subset_compact hε
      (by rintro x ⟨i, rfl⟩ y ⟨j, rfl⟩ hne; exact hsep _ (hrmem i) _ (hrmem j) hne)
      (isCompact_closedBall (0 : ℂ) 1)
      (by rintro x ⟨i, rfl⟩; simpa only [mem_closedBall, dist_zero_right] using hrnorm i)
  have hninj : ¬ Function.Injective r := by
    intro hinj
    exact (Set.infinite_range_of_injective hinj) hfinite
  unfold Function.Injective at hninj
  push Not at hninj
  obtain ⟨i, j, hij, hne⟩ := hninj
  have hpair (a b : ℕ) (hab : a < b) (heq : r a = r b) :
      ∃ m : ℕ, 0 < m ∧ ∃ n : O, (m : ℂ) * α = ringComplex n := by
    refine ⟨b - a, Nat.sub_pos_of_lt hab, q b - q a, ?_⟩
    rw [Nat.cast_sub hab.le, map_sub]
    dsimp [r] at heq
    linear_combination -heq
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact hpair i j hlt hij
  · exact hpair j i hgt hij.symm

/-- The integral norm makes distinct embedded algebraic integers at least unit distance apart. -/
private theorem ring_norm_ge_one {a : O} (ha : a ≠ 0) : 1 ≤ ‖ringComplex a‖ := by
  have hp := Coordinates.coordinate_norm_pos (Coordinates.coords a).1
    (Coordinates.coords a).2 (by simpa only [Coordinates.eval_coords] using ha)
  have hi : (1 : ℤ) ≤ (Coordinates.coords a).1 ^ 2 -
      (Coordinates.coords a).1 * (Coordinates.coords a).2 + (Coordinates.coords a).2 ^ 2 := hp
  have hr : (1 : ℝ) ≤ ((Coordinates.coords a).1 : ℝ) ^ 2 -
      ((Coordinates.coords a).1 : ℝ) * (Coordinates.coords a).2 +
      ((Coordinates.coords a).2 : ℝ) ^ 2 := by exact_mod_cast hi
  rw [← Coordinates.complex_norm_eval_sq, Coordinates.eval_coords] at hr
  nlinarith only [hr, norm_nonneg (ringComplex a)]

/-- An integral multiple in the original lattice is also sufficient for discreteness. -/
theorem mixedClosure_ne_top_of_nat_mul_mem (α : ℂ) {m : ℕ} (hm : 0 < m)
    {a : O} (ha : (m : ℂ) * α = ringComplex a) : mixedClosure α ≠ ⊤ := by
  have hclosed : IsClosed (range ringComplex) :=
    isClosed_of_dist_separated zero_lt_one (by
      rintro x ⟨b, rfl⟩ y ⟨c, rfl⟩ hne
      rw [dist_eq_norm, ← map_sub]
      exact ring_norm_ge_one (fun h => hne (congrArg ringComplex (sub_eq_zero.mp h))))
  have hpre : IsClosed ((fun z : ℂ => (m : ℂ) * z) ⁻¹' range ringComplex) :=
    hclosed.preimage (continuous_const.mul continuous_id)
  have hsub : (mixedLattice α : Set ℂ) ⊆
      (fun z : ℂ => (m : ℂ) * z) ⁻¹' range ringComplex := by
    rintro z ⟨b, c, rfl⟩
    refine ⟨(m : O) * b + a * c, ?_⟩
    simp only [map_add, map_mul, map_natCast]
    rw [← ha]
    ring
  have hall := closure_minimal hsub hpre
  intro htop
  have hmc : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  have hz : (1 / 2 : ℂ) / (m : ℂ) ∈ mixedClosure α := by
    rw [htop]
    exact AddSubgroup.mem_top _
  obtain ⟨b, hb⟩ := hall hz
  change ringComplex b = (m : ℂ) * ((1 / 2 : ℂ) / (m : ℂ)) at hb
  have heq : (m : ℂ) * ((1 / 2 : ℂ) / (m : ℂ)) = 1 / 2 := by field_simp
  rw [heq] at hb
  have hb0 : b ≠ 0 := by
    intro h
    rw [h, map_zero] at hb
    norm_num at hb
  have hnorm := ring_norm_ge_one hb0
  rw [hb, norm_div, norm_one, show ‖(2 : ℂ)‖ = 2 from Complex.norm_natCast 2] at hnorm
  norm_num at hnorm

/-- Exact arithmetic classification: failure of density means rational Eisenstein commensurability. -/
theorem mixedClosure_ne_top_iff (α : ℂ) :
    mixedClosure α ≠ ⊤ ↔ ∃ m : ℕ, 0 < m ∧ ∃ a : O, (m : ℂ) * α = ringComplex a := by
  constructor
  · exact exists_nat_mul_mem_of_mixedClosure_ne_top α
  · rintro ⟨m, hm, a, ha⟩
    exact mixedClosure_ne_top_of_nat_mul_mem α hm ha

/-- An integral squared scale in a discrete superlattice must be an integral Eisenstein norm. -/
theorem norm_represented_of_mixedClosure_ne_top (α : ℂ) (n : ℕ)
    (hnorm : ‖α‖ ^ 2 = n) (hα : mixedClosure α ≠ ⊤) : (normSet n).Nonempty := by
  obtain ⟨m, hm, a, ha⟩ := exists_nat_mul_mem_of_mixedClosure_ne_top α hα
  have hscale := congrArg (fun z : ℂ => ‖z‖ ^ 2) ha
  simp only [norm_mul, mul_pow, Complex.norm_natCast, hnorm] at hscale
  have hcoord := Coordinates.complex_norm_eval_sq (Coordinates.coords a).1 (Coordinates.coords a).2
  rw [Coordinates.eval_coords] at hcoord
  let z : _root_.RHTower.BourgainEisensteinInt :=
    ⟨(Coordinates.coords a).1, (Coordinates.coords a).2⟩
  have hz : _root_.RHTower.BourgainEisensteinInt.norm z = (n * m ^ 2 : ℕ) := by
    change (Coordinates.coords a).1 ^ 2 - (Coordinates.coords a).1 * (Coordinates.coords a).2 +
      (Coordinates.coords a).2 ^ 2 = (n * m ^ 2 : ℕ)
    have heq : ((Coordinates.coords a).1 : ℝ) ^ 2 -
        ((Coordinates.coords a).1 : ℝ) * (Coordinates.coords a).2 +
        ((Coordinates.coords a).2 : ℝ) ^ 2 = (n * m ^ 2 : ℕ) := by
      rw [← hcoord, ← hscale]
      push_cast
      ring
    exact_mod_cast heq
  exact ((normSet_square_factor_nonempty_iff n m).mp
    ⟨z, mem_normSet.mpr hz⟩).resolve_left hm.ne'

/-- A nonnorm squared scale forces density in the entire complex plane. -/
theorem mixedClosure_eq_top_of_norm_not_represented (α : ℂ) (n : ℕ)
    (hnorm : ‖α‖ ^ 2 = n) (hn : ¬ (normSet n).Nonempty) : mixedClosure α = ⊤ := by
  by_contra h
  exact hn (norm_represented_of_mixedClosure_ne_top α n hnorm h)

/-- Squared scales congruent to two modulo three satisfy the norm obstruction automatically. -/
theorem mixedClosure_eq_top_of_mod_three_eq_two (α : ℂ) (n : ℕ)
    (hnorm : ‖α‖ ^ 2 = n) (hn : n % 3 = 2) : mixedClosure α = ⊤ := by
  apply mixedClosure_eq_top_of_norm_not_represented α n hnorm
  rintro ⟨z, hz⟩
  apply norm_emod_three_ne_two z
  rw [mem_normSet.mp hz]
  exact_mod_cast hn

/-- The original lattice and its real square-root-of-two dilation have dense sum. -/
theorem mixedClosure_sqrt_two_eq_top : mixedClosure (Real.sqrt 2 : ℂ) = ⊤ := by
  apply mixedClosure_eq_top_of_mod_three_eq_two (Real.sqrt 2 : ℂ) 2
  · rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
    exact Real.sq_sqrt (by positivity)
  · rfl

/-- A closed lattice-periodic set containing an incommensurate triangular coset fills the plane. -/
theorem closed_periodic_set_eq_univ (α c : ℂ) (hα : mixedClosure α = ⊤)
    (S : Set ℂ) (hS : IsClosed S)
    (hperiod : ∀ z ∈ S, ∀ a : O, z + ringComplex a ∈ S)
    (hcoset : ∀ a : O, c + α * ringComplex a ∈ S) : S = univ := by
  have hc : IsClosed ((fun z : ℂ => c + z) ⁻¹' S) :=
    hS.preimage (continuous_const.add continuous_id)
  have hsub : (mixedLattice α : Set ℂ) ⊆ (fun z : ℂ => c + z) ⁻¹' S := by
    rintro z ⟨a, b, rfl⟩
    have h := hperiod _ (hcoset b) a
    change c + (ringComplex a + α * ringComplex b) ∈ S
    convert h using 1
    ring
  have hall : ∀ z ∈ mixedClosure α, c + z ∈ S := closure_minimal hsub hc
  apply eq_univ_of_forall
  intro z
  have hz := hall (z - c) (by rw [hα]; exact AddSubgroup.mem_top _)
  have heq : c + (z - c) = z := by rw [add_comm, sub_add_cancel]
  rwa [heq] at hz

end GaloisForLFunctions.DilutionCrystallizationPincer.EisensteinCommensurability

#print axioms GaloisForLFunctions.DilutionCrystallizationPincer.EisensteinCommensurability.exists_nat_mul_mem_of_mixedClosure_ne_top
#print axioms GaloisForLFunctions.DilutionCrystallizationPincer.EisensteinCommensurability.mixedClosure_ne_top_iff
#print axioms GaloisForLFunctions.DilutionCrystallizationPincer.EisensteinCommensurability.mixedClosure_eq_top_of_norm_not_represented
#print axioms GaloisForLFunctions.DilutionCrystallizationPincer.EisensteinCommensurability.mixedClosure_sqrt_two_eq_top
#print axioms GaloisForLFunctions.DilutionCrystallizationPincer.EisensteinCommensurability.closed_periodic_set_eq_univ
