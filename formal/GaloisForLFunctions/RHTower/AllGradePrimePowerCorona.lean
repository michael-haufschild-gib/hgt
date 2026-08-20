import GaloisForLFunctions.RHTower.WeightedEulerCoefficientSpaces
import GaloisForLFunctions.RHTower.CreaseBudgetPrimeMass

/-!
# The all-grade prime-power Marcinkiewicz layer and its grade-one face

The critical coefficient topology on *all* prime-power grades is the Marcinkiewicz seminorm

`‖c‖_pp = sup_X (1/log X) ∑_{p^{m+1} ≤ X} |c_{p,m}| / p^{m+1}`,

indexed by pairs `(p, m)` standing for the grade-`m+1` coefficient at the prime `p`.  The grade-one
embedding `ι(b)_{p,0} = (log p) b_p`, `ι(b)_{p,m} = 0` for `m ≥ 1`, is an isometry onto the
logarithmic layer `M_log` of `WeightedEulerCoefficientSpaces`, and grade-one projection is
contractive in the opposite direction.

The point of the all-grade space is that the *nonlinear* Euler ray `Φ(a)_{p,m} = (log p) a_p^{m+1}`
of a bounded degree-one parameter field differs from its grade-one coordinate by a weighted
absolutely summable array: the grades `m ≥ 1` are a vanishing tail at the critical Dirichlet weight,
with the explicit uniform bound `∑_p (log p)/(p(p-1)) ≤ 8`.  Hence the complete nonlinear ray and
its linear grade-one face have the same critical corona class.
-/

noncomputable section

open Finset

namespace RHTower

/-! ### The all-grade index and its mass -/

/-- The prime-power index below a cutoff: pairs `(p, m)` with `p` prime and `p^{m+1} ≤ X`. -/
def primePowerIndex (X : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.Icc 1 X ×ˢ Finset.range (X + 1)).filter fun z => z.1.Prime ∧ z.1 ^ (z.2 + 1) ≤ X

theorem mem_primePowerIndex {X : ℕ} {z : ℕ × ℕ} :
    z ∈ primePowerIndex X ↔ z.1.Prime ∧ z.1 ^ (z.2 + 1) ≤ X := by
  constructor
  · intro hz
    exact (Finset.mem_filter.mp hz).2
  · rintro ⟨hp, hle⟩
    refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, hp, hle⟩
    · refine Finset.mem_Icc.mpr ⟨hp.one_lt.le, le_trans ?_ hle⟩
      exact Nat.le_self_pow (by omega) _
    · refine Finset.mem_range.mpr ?_
      have h2 : 2 ^ (z.2 + 1) ≤ z.1 ^ (z.2 + 1) := Nat.pow_le_pow_left hp.two_le _
      have h3 : z.2 + 1 < 2 ^ (z.2 + 1) := Nat.lt_two_pow_self
      omega

/-- The all-grade prime-power weighted mass at cutoff `X`. -/
def primePowerMass (c : ℕ × ℕ → ℝ) (X : ℕ) : ℝ :=
  ∑ z ∈ primePowerIndex X, |c z| / ((z.1 : ℝ) ^ (z.2 + 1))

/-- The all-grade Marcinkiewicz quotient at cutoff `X`. -/
def primePowerQuotient (c : ℕ × ℕ → ℝ) (X : ℕ) : ℝ := primePowerMass c X / Real.log X

/-- Membership in the all-grade Marcinkiewicz layer `M_pp`. -/
def MemPrimePowerLayer (c : ℕ × ℕ → ℝ) : Prop :=
  ∃ C : ℝ, ∀ X : ℕ, 2 ≤ X → primePowerQuotient c X ≤ C

theorem primePowerMass_nonneg (c : ℕ × ℕ → ℝ) (X : ℕ) : 0 ≤ primePowerMass c X := by
  refine Finset.sum_nonneg fun z _ => ?_
  positivity

/-! ### The grade-one face -/

/-- The grade-one embedding of a prime coefficient field. -/
def gradeOneEmbed (b : ℕ → ℝ) : ℕ × ℕ → ℝ :=
  fun z => if z.2 = 0 then Real.log z.1 * b z.1 else 0

/-- Grade-one projection of an all-grade array. -/
def gradeOneProj (c : ℕ × ℕ → ℝ) : ℕ → ℝ :=
  fun p => c (p, 0) / Real.log p

theorem primePowerIndex_grade_zero {X : ℕ} {p : ℕ} :
    (p, 0) ∈ primePowerIndex X ↔ p.Prime ∧ p ≤ X := by
  rw [mem_primePowerIndex]
  simp

/-- The grade-zero part of the prime-power index is the prime range. -/
theorem primePowerIndex_filter_grade_zero (X : ℕ) :
    (primePowerIndex X).filter (fun z => z.2 = 0)
      = (Finset.filter (fun n : ℕ => n.Prime) (Finset.Icc 1 X)).image (fun p : ℕ => (p, 0)) := by
  ext z
  constructor
  · intro hz
    obtain ⟨hz1, hz2⟩ := Finset.mem_filter.mp hz
    rw [mem_primePowerIndex] at hz1
    refine Finset.mem_image.mpr ⟨z.1, Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨hz1.1.one_lt.le, ?_⟩, hz1.1⟩, ?_⟩
    · have h := hz1.2
      rw [hz2] at h
      simpa using h
    · exact Prod.ext rfl hz2.symm
  · intro hz
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨hp1, hp2⟩ := Finset.mem_filter.mp hp
    refine Finset.mem_filter.mpr ⟨?_, rfl⟩
    rw [mem_primePowerIndex]
    exact ⟨hp2, by simpa using (Finset.mem_Icc.mp hp1).2⟩

/-- **The grade-one embedding is an isometry.**  Its all-grade mass is the prime-log mass of the
underlying field. -/
theorem primePowerMass_gradeOneEmbed (b : ℕ → ℝ) (X : ℕ) :
    primePowerMass (gradeOneEmbed b) X = primeLogMass b X := by
  rw [primePowerMass, primeLogMass,
    ← Finset.sum_filter_add_sum_filter_not (primePowerIndex X) (fun z => z.2 = 0)]
  have hzero : ∑ z ∈ (primePowerIndex X).filter (fun z => ¬ z.2 = 0),
      |gradeOneEmbed b z| / ((z.1 : ℝ) ^ (z.2 + 1)) = 0 := by
    refine Finset.sum_eq_zero fun z hz => ?_
    have hz2 : ¬ z.2 = 0 := (Finset.mem_filter.mp hz).2
    simp [gradeOneEmbed, hz2]
  rw [hzero, add_zero, primePowerIndex_filter_grade_zero,
    Finset.sum_image (fun a _ b _ h => congrArg Prod.fst h)]
  refine Finset.sum_congr rfl fun p hp => ?_
  have hval : gradeOneEmbed b (p, 0) = Real.log p * b p := by simp [gradeOneEmbed]
  rw [hval, pow_one, abs_mul, abs_of_nonneg (Real.log_natCast_nonneg p)]
  ring

/-- **Grade-one projection is contractive.** -/
theorem primeLogMass_gradeOneProj_le (c : ℕ × ℕ → ℝ) (X : ℕ) :
    primeLogMass (gradeOneProj c) X ≤ primePowerMass c X := by
  rw [primeLogMass, primePowerMass]
  have hsub : (Finset.filter (fun n : ℕ => n.Prime) (Finset.Icc 1 X)).image (fun p : ℕ => (p, 0))
      ⊆ primePowerIndex X := by
    rw [← primePowerIndex_filter_grade_zero]
    exact Finset.filter_subset _ _
  calc ∑ n ∈ Finset.filter (fun n : ℕ => n.Prime) (Finset.Icc 1 X),
        Real.log n / n * |gradeOneProj c n|
      = ∑ z ∈ (Finset.filter (fun n : ℕ => n.Prime) (Finset.Icc 1 X)).image
          (fun p : ℕ => (p, 0)), |c z| / ((z.1 : ℝ) ^ (z.2 + 1)) := by
        rw [Finset.sum_image (fun a _ b _ h => congrArg Prod.fst h)]
        refine Finset.sum_congr rfl fun p hp => ?_
        obtain ⟨hp1, hp2⟩ := Finset.mem_filter.mp hp
        have hlog : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp2.one_lt)
        rw [gradeOneProj, pow_one, abs_div, abs_of_pos hlog]
        field_simp
    _ ≤ ∑ z ∈ primePowerIndex X, |c z| / ((z.1 : ℝ) ^ (z.2 + 1)) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun z _ _ => by positivity

/-! ### The nonlinear Euler ray -/

/-- The complete prime-power coefficient ray of a degree-one Euler source. -/
def eulerRay (a : ℕ → ℝ) : ℕ × ℕ → ℝ := fun z => Real.log z.1 * (a z.1) ^ (z.2 + 1)

/-- The higher-grade part of the Euler ray. -/
def eulerRayHigher (a : ℕ → ℝ) : ℕ × ℕ → ℝ := fun z => eulerRay a z - gradeOneEmbed a z

theorem eulerRay_eq_add (a : ℕ → ℝ) : eulerRay a = gradeOneEmbed a + eulerRayHigher a := by
  funext z
  simp [eulerRayHigher]

theorem eulerRayHigher_grade_zero (a : ℕ → ℝ) (p : ℕ) : eulerRayHigher a (p, 0) = 0 := by
  simp [eulerRayHigher, eulerRay, gradeOneEmbed]

theorem eulerRayHigher_of_ne_zero (a : ℕ → ℝ) {z : ℕ × ℕ} (hz : z.2 ≠ 0) :
    eulerRayHigher a z = Real.log z.1 * (a z.1) ^ (z.2 + 1) := by
  simp [eulerRayHigher, eulerRay, gradeOneEmbed, hz]

/-! ### The grouping bound -/

theorem primePowerIndex_subset_product (X : ℕ) :
    primePowerIndex X ⊆ Nat.primesBelow (X + 1) ×ˢ Finset.range (X + 1) := by
  intro z hz
  have hz' := mem_primePowerIndex.mp hz
  have hpX : z.1 ≤ X := le_trans (Nat.le_self_pow (by omega) _) hz'.2
  refine Finset.mem_product.mpr ⟨Nat.mem_primesBelow.mpr ⟨by omega, hz'.1⟩, ?_⟩
  refine Finset.mem_range.mpr ?_
  have h2 : 2 ^ (z.2 + 1) ≤ z.1 ^ (z.2 + 1) := Nat.pow_le_pow_left hz'.1.two_le _
  have h3 : z.2 + 1 < 2 ^ (z.2 + 1) := Nat.lt_two_pow_self
  omega

/-- **Grouping bound.**  The all-grade mass is dominated by the product sum of any termwise
majorant. -/
theorem primePowerMass_le_prod {c : ℕ × ℕ → ℝ} (g : ℕ → ℕ → ℝ) (X : ℕ)
    (hg : ∀ z ∈ primePowerIndex X, |c z| / ((z.1 : ℝ) ^ (z.2 + 1)) ≤ g z.1 z.2)
    (hgnn : ∀ p m, 0 ≤ g p m) :
    primePowerMass c X
      ≤ ∑ p ∈ Nat.primesBelow (X + 1), ∑ m ∈ Finset.range (X + 1), g p m := by
  rw [primePowerMass]
  calc ∑ z ∈ primePowerIndex X, |c z| / ((z.1 : ℝ) ^ (z.2 + 1))
      ≤ ∑ z ∈ primePowerIndex X, g z.1 z.2 := Finset.sum_le_sum hg
    _ ≤ ∑ z ∈ Nat.primesBelow (X + 1) ×ˢ Finset.range (X + 1), g z.1 z.2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (primePowerIndex_subset_product X)
          (fun z _ _ => hgnn z.1 z.2)
    _ = ∑ p ∈ Nat.primesBelow (X + 1), ∑ m ∈ Finset.range (X + 1), g p m :=
        Finset.sum_product

/-! ### The geometric grade tail -/

theorem sum_range_pow_le {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (M : ℕ) :
    ∑ i ∈ Finset.range M, r ^ i ≤ (1 - r)⁻¹ := by
  have hne : r ≠ 1 := ne_of_lt hr1
  rw [geom_sum_eq hne]
  have hden : (0 : ℝ) < 1 - r := by linarith
  have hnum : r ^ M - 1 ≤ 0 := by
    have : r ^ M ≤ 1 := pow_le_one₀ hr0 hr1.le
    linarith
  rw [div_le_iff₀' (by linarith : (0 : ℝ) < r - 1 ∨ True) ] at *
  · exact le_rfl
  · trivial

theorem sum_Ico_pow_succ_le {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (M : ℕ) :
    ∑ m ∈ Finset.range M, r ^ (m + 1) ≤ r * (1 - r)⁻¹ := by
  have hgeom : ∑ m ∈ Finset.range M, r ^ (m + 1) = r * ∑ m ∈ Finset.range M, r ^ m := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun m _ => by ring
  rw [hgeom]
  exact mul_le_mul_of_nonneg_left (sum_range_pow_le hr0 hr1 M) hr0
