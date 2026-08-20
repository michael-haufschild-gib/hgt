import GaloisForLFunctions.RHTower.WeightedEulerCoefficientSpaces
import GaloisForLFunctions.RHTower.CreaseBudgetPrimeMass
import GaloisForLFunctions.RHTower.PrimeLogRpowTail
import GaloisForLFunctions.RHTower.MertensPrimeMeanReader

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

open Finset Filter Topology

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
        Finset.sum_product _ _ _

/-! ### The geometric grade tail -/

theorem sum_range_pow_le {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (M : ℕ) :
    ∑ i ∈ Finset.range M, r ^ i ≤ (1 - r)⁻¹ := by
  have hne : r ≠ 1 := ne_of_lt hr1
  rw [geom_sum_eq hne]
  have hden : (0 : ℝ) < 1 - r := by linarith
  have hrw : (r ^ M - 1) / (r - 1) = (1 - r ^ M) / (1 - r) := by
    rw [show r ^ M - 1 = -(1 - r ^ M) by ring, show r - 1 = -(1 - r) by ring, neg_div_neg_eq]
  rw [hrw, div_le_iff₀ hden, inv_mul_cancel₀ (ne_of_gt hden)]
  linarith [pow_nonneg hr0 M]

theorem sum_Ico_pow_succ_le {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (M : ℕ) :
    ∑ m ∈ Finset.range M, r ^ (m + 1) ≤ r * (1 - r)⁻¹ := by
  have hgeom : ∑ m ∈ Finset.range M, r ^ (m + 1) = r * ∑ m ∈ Finset.range M, r ^ m := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun m _ => by ring
  rw [hgeom]
  exact mul_le_mul_of_nonneg_left (sum_range_pow_le hr0 hr1 M) hr0

theorem sum_range_ite_pow_le {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (M : ℕ) :
    ∑ m ∈ Finset.range M, (if m = 0 then (0 : ℝ) else r ^ (m + 1)) ≤ r ^ 2 * (1 - r)⁻¹ := by
  have hden : (0 : ℝ) < 1 - r := by linarith
  have hinv : (0 : ℝ) ≤ (1 - r)⁻¹ := by positivity
  match M with
  | 0 => simpa using by positivity
  | (K + 1) =>
      have hterm : ∀ i ∈ Finset.range K,
          (if i + 1 = 0 then (0 : ℝ) else r ^ (i + 1 + 1)) = r ^ 2 * r ^ i := by
        intro i _
        rw [if_neg (by omega)]
        ring
      have hzero : (if (0 : ℕ) = 0 then (0 : ℝ) else r ^ (0 + 1)) = 0 := by norm_num
      rw [Finset.sum_range_succ', Finset.sum_congr rfl hterm, ← Finset.mul_sum, hzero, add_zero]
      exact mul_le_mul_of_nonneg_left (sum_range_pow_le hr0 hr1 K) (by positivity)

/-! ### The grade-`≥ 2` part is a vanishing tail -/

/-- **The higher-grade Euler mass is uniformly bounded.**  For a bounded degree-one parameter field
the grades `m ≥ 1` carry weighted mass at most `∑_p (log p)/(p(p-1)) ≤ 8`, uniformly in the
cutoff. -/
theorem primePowerMass_eulerRayHigher_le {a : ℕ → ℝ} (ha : ∀ p, |a p| ≤ 1) (X : ℕ) :
    primePowerMass (eulerRayHigher a) X ≤ 8 := by
  set g : ℕ → ℕ → ℝ := fun p m => if m = 0 then 0 else Real.log p * (((p : ℝ))⁻¹) ^ (m + 1)
    with hg
  have hgnn : ∀ p m, 0 ≤ g p m := by
    intro p m
    rw [hg]
    dsimp only
    split
    · exact le_rfl
    · exact mul_nonneg (Real.log_natCast_nonneg p) (by positivity)
  have hmaj : ∀ z ∈ primePowerIndex X,
      |eulerRayHigher a z| / ((z.1 : ℝ) ^ (z.2 + 1)) ≤ g z.1 z.2 := by
    intro z hz
    have hp := (mem_primePowerIndex.mp hz).1
    have hp0 : (0 : ℝ) < (z.1 : ℝ) := by exact_mod_cast hp.pos
    by_cases hz2 : z.2 = 0
    · have hzeq : z = (z.1, 0) := Prod.ext rfl hz2
      rw [hg]
      dsimp only
      rw [if_pos hz2, hzeq, eulerRayHigher_grade_zero]
      simp
    · rw [hg]
      dsimp only
      rw [if_neg hz2, eulerRayHigher_of_ne_zero a hz2, abs_mul,
        abs_of_nonneg (Real.log_natCast_nonneg z.1), abs_pow, div_le_iff₀ (by positivity)]
      have hle : |a z.1| ^ (z.2 + 1) ≤ 1 := pow_le_one₀ (abs_nonneg _) (ha z.1)
      have hinv : (((z.1 : ℝ))⁻¹) ^ (z.2 + 1) * ((z.1 : ℝ) ^ (z.2 + 1)) = 1 := by
        rw [← mul_pow, inv_mul_cancel₀ (ne_of_gt hp0), one_pow]
      calc Real.log z.1 * |a z.1| ^ (z.2 + 1)
          ≤ Real.log z.1 * 1 := mul_le_mul_of_nonneg_left hle (Real.log_natCast_nonneg z.1)
        _ = Real.log z.1 * ((((z.1 : ℝ))⁻¹) ^ (z.2 + 1) * ((z.1 : ℝ) ^ (z.2 + 1))) := by
            rw [hinv]
        _ = Real.log z.1 * (((z.1 : ℝ))⁻¹) ^ (z.2 + 1) * ((z.1 : ℝ) ^ (z.2 + 1)) := by ring
  refine le_trans (primePowerMass_le_prod g X hmaj hgnn) ?_
  have hinner : ∀ p ∈ Nat.primesBelow (X + 1),
      ∑ m ∈ Finset.range (X + 1), g p m ≤ Real.log p / ((p : ℝ) * ((p : ℝ) - 1)) := by
    intro p hp
    obtain ⟨hplt, hpp⟩ := Nat.mem_primesBelow.mp hp
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.two_le
    set r : ℝ := ((p : ℝ))⁻¹ with hr
    have hr0 : 0 ≤ r := by positivity
    have hr1 : r < 1 := by
      rw [hr, inv_lt_one_iff₀]
      right; linarith
    have hsum : ∑ m ∈ Finset.range (X + 1), g p m
        = Real.log p * ∑ m ∈ Finset.range (X + 1), (if m = 0 then (0 : ℝ) else r ^ (m + 1)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [hg]
      dsimp only
      split <;> simp [hr]
    rw [hsum]
    have hb := sum_range_ite_pow_le hr0 hr1 (X + 1)
    have hpne : (p : ℝ) ≠ 0 := by linarith
    have hp1ne : (p : ℝ) - 1 ≠ 0 := by linarith
    have hval : r ^ 2 * (1 - r)⁻¹ = 1 / ((p : ℝ) * ((p : ℝ) - 1)) := by
      rw [hr]
      field_simp
    rw [hval] at hb
    calc Real.log p * ∑ m ∈ Finset.range (X + 1), (if m = 0 then (0 : ℝ) else r ^ (m + 1))
        ≤ Real.log p * (1 / ((p : ℝ) * ((p : ℝ) - 1))) :=
          mul_le_mul_of_nonneg_left hb (Real.log_natCast_nonneg p)
      _ = Real.log p / ((p : ℝ) * ((p : ℝ) - 1)) := by ring
  calc ∑ p ∈ Nat.primesBelow (X + 1), ∑ m ∈ Finset.range (X + 1), g p m
      ≤ ∑ p ∈ Nat.primesBelow (X + 1), Real.log p / ((p : ℝ) * ((p : ℝ) - 1)) :=
        Finset.sum_le_sum hinner
    _ ≤ 8 := sum_primesBelow_log_div_le (X + 1)

/-- **The grade-one reduction.**  For a bounded degree-one parameter field the higher grades are a
vanishing tail: their Marcinkiewicz quotient tends to zero, so the complete nonlinear Euler ray and
its grade-one coordinate have the same critical corona class. -/
theorem tendsto_primePowerQuotient_eulerRayHigher {a : ℕ → ℝ} (ha : ∀ p, |a p| ≤ 1) :
    Tendsto (fun X : ℕ => primePowerQuotient (eulerRayHigher a) X) atTop (nhds 0) := by
  refine squeeze_zero' ?_ ?_ (tendsto_const_div_log_nat 8)
  · filter_upwards [eventually_ge_atTop 2] with X hX
    have hlog : 0 < Real.log X := log_cutoff_pos hX
    exact div_nonneg (primePowerMass_nonneg _ _) hlog.le
  · filter_upwards [eventually_ge_atTop 2] with X hX
    have hlog : 0 < Real.log X := log_cutoff_pos hX
    exact div_le_div_of_nonneg_right (primePowerMass_eulerRayHigher_le ha X) hlog.le

/-! ### The exact unit class -/

theorem abs_eulerRay_unit (z : ℕ × ℕ) :
    |eulerRay (fun _ => (1 : ℝ)) z|
      = |gradeOneEmbed (fun _ => (1 : ℝ)) z| + |eulerRayHigher (fun _ => (1 : ℝ)) z| := by
  by_cases hz : z.2 = 0
  · have hzeq : z = (z.1, 0) := Prod.ext rfl hz
    rw [hzeq, eulerRayHigher_grade_zero]
    simp [eulerRay, gradeOneEmbed]
  · rw [eulerRayHigher_of_ne_zero _ hz]
    simp [eulerRay, gradeOneEmbed, hz]

theorem primePowerMass_eulerRay_unit (X : ℕ) :
    primePowerMass (eulerRay fun _ => (1 : ℝ)) X
      = primeLogMass (fun _ => (1 : ℝ)) X
        + primePowerMass (eulerRayHigher fun _ => (1 : ℝ)) X := by
  rw [← primePowerMass_gradeOneEmbed, primePowerMass, primePowerMass, primePowerMass,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [abs_eulerRay_unit]
  ring

/-- **The actual unit Euler source survives with quotient one.**  Mertens' first theorem gives the
exact Marcinkiewicz value of the complete all-grade unit ray: the surviving unit class is not
annihilated by the corona. -/
theorem tendsto_primePowerQuotient_eulerRay_unit :
    Tendsto (fun X : ℕ => primePowerQuotient (eulerRay fun _ => (1 : ℝ)) X) atTop (nhds 1) := by
  have hsplit : ∀ X : ℕ, primePowerQuotient (eulerRay fun _ => (1 : ℝ)) X
      = mertensPrimeMean (fun _ => (1 : ℝ)) X
        + primePowerQuotient (eulerRayHigher fun _ => (1 : ℝ)) X := by
    intro X
    rw [primePowerQuotient, primePowerMass_eulerRay_unit, primePowerQuotient,
      mertensPrimeMean_unit_eq, add_div]
  have hunit : ∀ p : ℕ, |(1 : ℝ)| ≤ 1 := fun _ => by norm_num
  have h := tendsto_mertensPrimeMean_unit.add
    (tendsto_primePowerQuotient_eulerRayHigher hunit)
  rw [add_zero] at h
  exact h.congr fun X => (hsplit X).symm

/-! ### The off-line shift ray vanishes -/

/-- The shifted parameter field of an off-line residue character at half-plane depth `ε`. -/
def shiftField (ε : ℝ) : ℕ → ℝ := fun p => (p : ℝ) ^ (-ε)

theorem primePowerMass_eulerRay_shift_le {ε : ℝ} (hε : 0 < ε) (X : ℕ) :
    primePowerMass (eulerRay (shiftField ε)) X ≤ 2 * primeLogRpowTailConstant ε := by
  set g : ℕ → ℕ → ℝ := fun p m => Real.log p * (((p : ℝ) ^ (-(1 + ε)))) ^ (m + 1) with hg
  have hgnn : ∀ p m, 0 ≤ g p m := fun p m =>
    mul_nonneg (Real.log_natCast_nonneg p) (by positivity)
  have hmaj : ∀ z ∈ primePowerIndex X,
      |eulerRay (shiftField ε) z| / ((z.1 : ℝ) ^ (z.2 + 1)) ≤ g z.1 z.2 := by
    intro z hz
    have hp := (mem_primePowerIndex.mp hz).1
    have hp0 : (0 : ℝ) < (z.1 : ℝ) := by exact_mod_cast hp.pos
    have hq : (z.1 : ℝ) ^ (-ε) / (z.1 : ℝ) = (z.1 : ℝ) ^ (-(1 + ε)) := by
      rw [div_eq_mul_inv, ← Real.rpow_neg_one (z.1 : ℝ), ← Real.rpow_add hp0]
      congr 1
      ring
    rw [hg]
    dsimp only
    rw [eulerRay, shiftField, abs_mul, abs_of_nonneg (Real.log_natCast_nonneg z.1), abs_pow,
      abs_of_nonneg (Real.rpow_nonneg hp0.le _), mul_div_assoc, ← div_pow, hq]
  refine le_trans (primePowerMass_le_prod g X hmaj hgnn) ?_
  have hinner : ∀ p ∈ Nat.primesBelow (X + 1),
      ∑ m ∈ Finset.range (X + 1), g p m ≤ 2 * (Real.log p * ((p : ℝ) ^ (-(1 + ε)))) := by
    intro p hp
    obtain ⟨hplt, hpp⟩ := Nat.mem_primesBelow.mp hp
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.two_le
    have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
    set q : ℝ := (p : ℝ) ^ (-(1 + ε)) with hqdef
    have hq0 : 0 < q := Real.rpow_pos_of_pos hp0 _
    have hqhalf : q ≤ 1 / 2 := by
      have h1 : (2 : ℝ) ^ (1 + ε) ≤ (p : ℝ) ^ (1 + ε) :=
        Real.rpow_le_rpow (by norm_num) hp2 (by linarith)
      have h2 : (2 : ℝ) ≤ (2 : ℝ) ^ (1 + ε) := by
        have := Real.rpow_le_rpow_of_exponent_le (x := (2 : ℝ)) (by norm_num)
          (show (1 : ℝ) ≤ 1 + ε by linarith)
        simpa using this
      rw [hqdef, Real.rpow_neg hp0.le, ← one_div]
      exact one_div_le_one_div_of_le (by norm_num) (le_trans h2 h1)
    have hq1 : q < 1 := by linarith
    have hsum : ∑ m ∈ Finset.range (X + 1), g p m
        = Real.log p * ∑ m ∈ Finset.range (X + 1), q ^ (m + 1) := by
      rw [Finset.mul_sum]
    rw [hsum]
    have hb := sum_Ico_pow_succ_le hq0.le hq1 (X + 1)
    have hinv2 : (1 - q)⁻¹ ≤ 2 := by
      rw [inv_le_comm₀ (by linarith) (by norm_num)]
      linarith
    calc Real.log p * ∑ m ∈ Finset.range (X + 1), q ^ (m + 1)
        ≤ Real.log p * (q * (1 - q)⁻¹) :=
          mul_le_mul_of_nonneg_left hb (Real.log_natCast_nonneg p)
      _ ≤ Real.log p * (q * 2) := by
          refine mul_le_mul_of_nonneg_left ?_ (Real.log_natCast_nonneg p)
          exact mul_le_mul_of_nonneg_left hinv2 hq0.le
      _ = 2 * (Real.log p * q) := by ring
  have htail := sum_prime_log_rpow_dyadic_tail_le hε 0 X
  have hfilter : {p ∈ Nat.primesBelow (X + 1) | 2 ^ 0 ≤ p} = Nat.primesBelow (X + 1) := by
    refine Finset.filter_true_of_mem fun p hp => ?_
    have hpp := (Nat.mem_primesBelow.mp hp).2
    simpa using hpp.one_lt.le
  rw [hfilter] at htail
  simp only [pow_zero, mul_one] at htail
  calc ∑ p ∈ Nat.primesBelow (X + 1), ∑ m ∈ Finset.range (X + 1), g p m
      ≤ ∑ p ∈ Nat.primesBelow (X + 1), 2 * (Real.log p * ((p : ℝ) ^ (-(1 + ε)))) :=
        Finset.sum_le_sum hinner
    _ = 2 * ∑ p ∈ Nat.primesBelow (X + 1), Real.log p * ((p : ℝ) ^ (-(1 + ε))) := by
        rw [Finset.mul_sum]
    _ ≤ 2 * primeLogRpowTailConstant ε := by
        exact mul_le_mul_of_nonneg_left htail (by norm_num)

/-- **The off-line shift ray is a vanishing tail.**  Even with every prime-power grade retained,
the complete nonlinear ray of a right-half residue character has zero critical corona class. -/
theorem tendsto_primePowerQuotient_eulerRay_shift {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun X : ℕ => primePowerQuotient (eulerRay (shiftField ε)) X) atTop (nhds 0) := by
  refine squeeze_zero' ?_ ?_ (tendsto_const_div_log_nat (2 * primeLogRpowTailConstant ε))
  · filter_upwards [eventually_ge_atTop 2] with X hX
    exact div_nonneg (primePowerMass_nonneg _ _) (log_cutoff_pos hX).le
  · filter_upwards [eventually_ge_atTop 2] with X hX
    exact div_le_div_of_nonneg_right (primePowerMass_eulerRay_shift_le hε X)
      (log_cutoff_pos hX).le

/-! ### The tangent ray at the actual unit source -/

theorem primesBelow_succ_eq_filter (X : ℕ) :
    Nat.primesBelow (X + 1) = Finset.filter (fun n : ℕ => n.Prime) (Finset.Icc 1 X) := by
  ext p
  simp only [Nat.mem_primesBelow, Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨hlt, hp⟩
    exact ⟨⟨hp.one_lt.le, by omega⟩, hp⟩
  · rintro ⟨⟨_, hle⟩, hp⟩
    exact ⟨by omega, hp⟩

theorem sum_range_succ_mul_pow_le {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (M : ℕ) :
    ∑ m ∈ Finset.range M, ((m : ℝ) + 1) * r ^ (m + 1) ≤ r / (1 - r) ^ 2 := by
  have hnorm : ‖r‖ < 1 := by rwa [Real.norm_eq_abs, abs_of_nonneg hr0]
  have hs := hasSum_coe_mul_geometric_of_norm_lt_one (𝕜 := ℝ) hnorm
  have heq : ∑ m ∈ Finset.range M, ((m : ℝ) + 1) * r ^ (m + 1)
      = ∑ n ∈ Finset.range (M + 1), (n : ℝ) * r ^ n := by
    rw [Finset.sum_range_succ']
    simp
  rw [heq, ← hs.tsum_eq]
  exact hs.summable.sum_le_tsum _ fun n _ => by positivity

/-- The tangent of the complete Euler ray at the actual unit source. -/
def eulerTangent (b : ℕ → ℝ) : ℕ × ℕ → ℝ := fun z => ((z.2 : ℝ) + 1) * Real.log z.1 * b z.1

/-- **The critical summable tangent bound.**  Adding all tangent grades does not strengthen the
critical summable topology: the complete tangent ray has weighted mass at most four times the
grade-one mass. -/
theorem primePowerMass_eulerTangent_le (b : ℕ → ℝ) (X : ℕ) :
    primePowerMass (eulerTangent b) X ≤ 4 * primeLogMass b X := by
  set g : ℕ → ℕ → ℝ :=
    fun p m => ((m : ℝ) + 1) * Real.log p * |b p| * (((p : ℝ))⁻¹) ^ (m + 1) with hg
  have hgnn : ∀ p m, 0 ≤ g p m := by
    intro p m
    rw [hg]
    dsimp only
    have : 0 ≤ ((m : ℝ) + 1) * Real.log p * |b p| :=
      mul_nonneg (mul_nonneg (by positivity) (Real.log_natCast_nonneg p)) (abs_nonneg _)
    positivity
  have hmaj : ∀ z ∈ primePowerIndex X,
      |eulerTangent b z| / ((z.1 : ℝ) ^ (z.2 + 1)) ≤ g z.1 z.2 := by
    intro z hz
    have hp := (mem_primePowerIndex.mp hz).1
    have hp0 : (0 : ℝ) < (z.1 : ℝ) := by exact_mod_cast hp.pos
    rw [hg]
    dsimp only
    rw [eulerTangent, abs_mul, abs_mul,
      abs_of_nonneg (show (0 : ℝ) ≤ (z.2 : ℝ) + 1 by positivity),
      abs_of_nonneg (Real.log_natCast_nonneg z.1), inv_pow, ← div_eq_mul_inv]
  refine le_trans (primePowerMass_le_prod g X hmaj hgnn) ?_
  have hinner : ∀ p ∈ Nat.primesBelow (X + 1),
      ∑ m ∈ Finset.range (X + 1), g p m ≤ 4 * (Real.log p / p * |b p|) := by
    intro p hp
    obtain ⟨hplt, hpp⟩ := Nat.mem_primesBelow.mp hp
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.two_le
    have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
    set r : ℝ := ((p : ℝ))⁻¹ with hr
    have hr0 : 0 ≤ r := by positivity
    have hr1 : r < 1 := by
      rw [hr, inv_lt_one_iff₀]
      right; linarith
    have hsum : ∑ m ∈ Finset.range (X + 1), g p m
        = (Real.log p * |b p|) * ∑ m ∈ Finset.range (X + 1), ((m : ℝ) + 1) * r ^ (m + 1) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [hg]
      dsimp only
      ring
    rw [hsum]
    have hb := sum_range_succ_mul_pow_le hr0 hr1 (X + 1)
    have hpne : (p : ℝ) ≠ 0 := by linarith
    have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
    have hval : r / (1 - r) ^ 2 = (p : ℝ) / ((p : ℝ) - 1) ^ 2 := by
      rw [hr]
      field_simp
    rw [hval] at hb
    have hcmp : (p : ℝ) / ((p : ℝ) - 1) ^ 2 ≤ 4 / (p : ℝ) := by
      have hd1 : (0 : ℝ) < ((p : ℝ) - 1) ^ 2 := by positivity
      rw [div_le_iff₀ hd1, div_mul_eq_mul_div, le_div_iff₀ hp0]
      nlinarith
    have hnn : (0 : ℝ) ≤ Real.log p * |b p| :=
      mul_nonneg (Real.log_natCast_nonneg p) (abs_nonneg _)
    calc (Real.log p * |b p|) * ∑ m ∈ Finset.range (X + 1), ((m : ℝ) + 1) * r ^ (m + 1)
        ≤ (Real.log p * |b p|) * ((p : ℝ) / ((p : ℝ) - 1) ^ 2) :=
          mul_le_mul_of_nonneg_left hb hnn
      _ ≤ (Real.log p * |b p|) * (4 / (p : ℝ)) := mul_le_mul_of_nonneg_left hcmp hnn
      _ = 4 * (Real.log p / p * |b p|) := by field_simp
  calc ∑ p ∈ Nat.primesBelow (X + 1), ∑ m ∈ Finset.range (X + 1), g p m
      ≤ ∑ p ∈ Nat.primesBelow (X + 1), 4 * (Real.log p / p * |b p|) := Finset.sum_le_sum hinner
    _ = 4 * primeLogMass b X := by
        rw [← Finset.mul_sum, primeLogMass, primesBelow_succ_eq_filter]

/-! ### The Marcinkiewicz tangent extension -/

theorem sum_range_add_one_mul_pow_le {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (M : ℕ) :
    ∑ m ∈ Finset.range M, ((m : ℝ) + 1) * r ^ m ≤ ((1 - r) ^ 2)⁻¹ := by
  have hnorm : ‖r‖ < 1 := by rwa [Real.norm_eq_abs, abs_of_nonneg hr0]
  have hden : (0 : ℝ) < 1 - r := by linarith
  have h1 := hasSum_coe_mul_geometric_of_norm_lt_one (𝕜 := ℝ) hnorm
  have h2 := hasSum_geometric_of_norm_lt_one hnorm
  have hs : HasSum (fun n : ℕ => ((n : ℝ) + 1) * r ^ n) (((1 - r) ^ 2)⁻¹) := by
    have hadd := h1.add h2
    have hval : r / (1 - r) ^ 2 + (1 - r)⁻¹ = ((1 - r) ^ 2)⁻¹ := by
      field_simp
      ring
    rw [hval] at hadd
    exact hadd.congr_fun fun n => by ring
  rw [← hs.tsum_eq]
  exact hs.summable.sum_le_tsum _ fun n _ => by positivity

theorem sum_Ico_succ_mul_pow_le {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1 / 2) (M : ℕ) :
    ∑ m ∈ Finset.Ico 1 M, ((m : ℝ) + 1) * r ^ (m + 1) ≤ 6 * r ^ 2 := by
  have hlt : r < 1 := by linarith
  have hden : (0 : ℝ) < 1 - r := by linarith
  have hinv1 : (1 - r)⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ hden (by norm_num)]
    linarith
  have hinv2 : ((1 - r) ^ 2)⁻¹ ≤ 4 := by
    have h : (1 - r)⁻¹ * (1 - r)⁻¹ ≤ 2 * 2 :=
      mul_le_mul hinv1 hinv1 (by positivity) (by norm_num)
    calc ((1 - r) ^ 2)⁻¹ = (1 - r)⁻¹ * (1 - r)⁻¹ := by rw [← mul_inv]; ring_nf
      _ ≤ 4 := by linarith
  rw [Finset.sum_Ico_eq_sum_range]
  have hterm : ∀ i ∈ Finset.range (M - 1),
      (((1 + i : ℕ) : ℝ) + 1) * r ^ ((1 + i) + 1)
        = r ^ 2 * (((i : ℝ) + 1) * r ^ i + r ^ i) := by
    intro i _
    push_cast
    ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, Finset.sum_add_distrib]
  have hb1 := sum_range_add_one_mul_pow_le hr0 hlt (M - 1)
  have hb2 := sum_range_pow_le hr0 hlt (M - 1)
  have hsum : (∑ i ∈ Finset.range (M - 1), ((i : ℝ) + 1) * r ^ i)
      + ∑ i ∈ Finset.range (M - 1), r ^ i ≤ 6 := by linarith
  calc r ^ 2 * ((∑ i ∈ Finset.range (M - 1), ((i : ℝ) + 1) * r ^ i)
        + ∑ i ∈ Finset.range (M - 1), r ^ i)
      ≤ r ^ 2 * 6 := mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = 6 * r ^ 2 := by ring

/-- The dyadic Marcinkiewicz bound: a logarithmic-layer field has summable reciprocal-weighted
prime mass, with the explicit constant `4 K log 2`. -/
theorem sum_primesBelow_primeLog_div_le {b : ℕ → ℝ} {K : ℝ}
    (hK : ∀ Y : ℕ, 2 ≤ Y → primeLogMass b Y ≤ K * Real.log Y) (X : ℕ) :
    ∑ p ∈ Nat.primesBelow (X + 1), Real.log p / p * |b p| / p ≤ 4 * K * Real.log 2 := by
  classical
  have hKnn : 0 ≤ K := by
    by_contra hneg
    rw [not_le] at hneg
    have h2 := hK 2 le_rfl
    have hmass : 0 ≤ primeLogMass b 2 := primeLogMass_nonneg b 2
    have hlog2 : (0 : ℝ) < Real.log ((2 : ℕ) : ℝ) := by
      rw [Nat.cast_ofNat]
      exact Real.log_pos (by norm_num)
    have hprod : K * Real.log ((2 : ℕ) : ℝ) < 0 := mul_neg_of_neg_of_pos hneg hlog2
    linarith
  have hmaps : ∀ p ∈ Nat.primesBelow (X + 1),
      Nat.log 2 p ∈ Finset.range (Nat.log 2 X + 1) := by
    intro p hp
    obtain ⟨hplt, hpp⟩ := Nat.mem_primesBelow.mp hp
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.log_mono_right (by omega)))
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  have hblock : ∀ k ∈ Finset.range (Nat.log 2 X + 1),
      ∑ p ∈ {p ∈ Nat.primesBelow (X + 1) | Nat.log 2 p = k},
          Real.log p / p * |b p| / p
        ≤ ((1 : ℝ) / 2) ^ k * (K * ((k : ℝ) + 1) * Real.log 2) := by
    intro k _
    have hbound : ∀ p ∈ {p ∈ Nat.primesBelow (X + 1) | Nat.log 2 p = k},
        Real.log p / p * |b p| / p ≤ ((1 : ℝ) / 2) ^ k * (Real.log p / p * |b p|) := by
      intro p hp
      obtain ⟨hp1, hp2⟩ := Finset.mem_filter.mp hp
      obtain ⟨hplt, hpp⟩ := Nat.mem_primesBelow.mp hp1
      have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hpp.pos
      have hpk : (2 : ℕ) ^ k ≤ p := by
        rw [← hp2]
        exact Nat.pow_log_le_self 2 hpp.pos.ne'
      have hpkR : ((2 : ℝ)) ^ k ≤ (p : ℝ) := by exact_mod_cast hpk
      have hrecip : (1 : ℝ) / (p : ℝ) ≤ ((1 : ℝ) / 2) ^ k := by
        rw [div_pow, one_pow]
        exact one_div_le_one_div_of_le (by positivity) hpkR
      have hnn : (0 : ℝ) ≤ Real.log p / p * |b p| :=
        mul_nonneg (div_nonneg (Real.log_natCast_nonneg p) hp0.le) (abs_nonneg _)
      calc Real.log p / p * |b p| / p = (Real.log p / p * |b p|) * (1 / (p : ℝ)) := by ring
        _ ≤ (Real.log p / p * |b p|) * ((1 : ℝ) / 2) ^ k :=
            mul_le_mul_of_nonneg_left hrecip hnn
        _ = ((1 : ℝ) / 2) ^ k * (Real.log p / p * |b p|) := by ring
    have hsub : {p ∈ Nat.primesBelow (X + 1) | Nat.log 2 p = k}
        ⊆ Finset.filter (fun n : ℕ => n.Prime) (Finset.Icc 1 (2 ^ (k + 1))) := by
      intro p hp
      obtain ⟨hp1, hp2⟩ := Finset.mem_filter.mp hp
      obtain ⟨hplt, hpp⟩ := Nat.mem_primesBelow.mp hp1
      refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hpp.one_lt.le, ?_⟩, hpp⟩
      have hlt2 := Nat.lt_pow_succ_log_self (b := 2) (by omega) p
      rw [hp2] at hlt2
      omega
    have hmass : ∑ p ∈ {p ∈ Nat.primesBelow (X + 1) | Nat.log 2 p = k},
        Real.log p / p * |b p| ≤ primeLogMass b (2 ^ (k + 1)) := by
      rw [primeLogMass]
      exact Finset.sum_le_sum_of_subset_of_nonneg hsub fun p _ _ =>
        mul_nonneg (div_nonneg (Real.log_natCast_nonneg p) (by positivity)) (abs_nonneg _)
    have hKmass : primeLogMass b (2 ^ (k + 1)) ≤ K * ((k : ℝ) + 1) * Real.log 2 := by
      have h2 : 2 ≤ 2 ^ (k + 1) := Nat.le_self_pow (by omega) 2
      have h := hK (2 ^ (k + 1)) h2
      have hlog : Real.log ((2 ^ (k + 1) : ℕ) : ℝ) = ((k : ℝ) + 1) * Real.log 2 := by
        push_cast
        rw [Real.log_pow]
        push_cast
        ring
      rw [hlog] at h
      calc primeLogMass b (2 ^ (k + 1)) ≤ K * (((k : ℝ) + 1) * Real.log 2) := h
        _ = K * ((k : ℝ) + 1) * Real.log 2 := by ring
    calc ∑ p ∈ {p ∈ Nat.primesBelow (X + 1) | Nat.log 2 p = k}, Real.log p / p * |b p| / p
        ≤ ∑ p ∈ {p ∈ Nat.primesBelow (X + 1) | Nat.log 2 p = k},
            ((1 : ℝ) / 2) ^ k * (Real.log p / p * |b p|) := Finset.sum_le_sum hbound
      _ = ((1 : ℝ) / 2) ^ k * ∑ p ∈ {p ∈ Nat.primesBelow (X + 1) | Nat.log 2 p = k},
            Real.log p / p * |b p| := by rw [Finset.mul_sum]
      _ ≤ ((1 : ℝ) / 2) ^ k * (K * ((k : ℝ) + 1) * Real.log 2) :=
          mul_le_mul_of_nonneg_left (le_trans hmass hKmass) (by positivity)
  have hgeom : ∑ k ∈ Finset.range (Nat.log 2 X + 1),
      ((1 : ℝ) / 2) ^ k * (K * ((k : ℝ) + 1) * Real.log 2) ≤ 4 * K * Real.log 2 := by
    have hrw : ∀ k : ℕ, ((1 : ℝ) / 2) ^ k * (K * ((k : ℝ) + 1) * Real.log 2)
        = (K * Real.log 2) * (((k : ℝ) + 1) * ((1 : ℝ) / 2) ^ k) := by
      intro k; ring
    rw [Finset.sum_congr rfl fun k _ => hrw k, ← Finset.mul_sum]
    have hb := sum_range_add_one_mul_pow_le (r := (1 : ℝ) / 2) (by norm_num) (by norm_num)
      (Nat.log 2 X + 1)
    have hval : (((1 : ℝ) - 1 / 2) ^ 2)⁻¹ = 4 := by norm_num
    rw [hval] at hb
    have hnn : (0 : ℝ) ≤ K * Real.log 2 :=
      mul_nonneg hKnn (Real.log_nonneg (by norm_num))
    calc (K * Real.log 2) * ∑ k ∈ Finset.range (Nat.log 2 X + 1),
          (((k : ℝ) + 1) * ((1 : ℝ) / 2) ^ k)
        ≤ (K * Real.log 2) * 4 := mul_le_mul_of_nonneg_left hb hnn
      _ = 4 * K * Real.log 2 := by ring
  exact le_trans (Finset.sum_le_sum hblock) hgeom

/-- The tangent grades `m ≥ 2` of the complete Euler ray. -/
def eulerTangentHigher (b : ℕ → ℝ) : ℕ × ℕ → ℝ :=
  fun z => if z.2 = 0 then 0 else eulerTangent b z

/-- **The Marcinkiewicz tangent extension.**  For a coefficient field in the logarithmic
Marcinkiewicz layer the tangent grades `m ≥ 2` carry weighted mass bounded uniformly in the cutoff,
continuously in the layer constant: the all-grade tangent over `M_0` is exactly the vanishing-tail
tangent. -/
theorem primePowerMass_eulerTangentHigher_le {b : ℕ → ℝ} {K : ℝ}
    (hK : ∀ Y : ℕ, 2 ≤ Y → primeLogMass b Y ≤ K * Real.log Y) (X : ℕ) :
    primePowerMass (eulerTangentHigher b) X ≤ 24 * K * Real.log 2 := by
  set g : ℕ → ℕ → ℝ := fun p m =>
    if m = 0 then 0 else ((m : ℝ) + 1) * (Real.log p * |b p|) * (((p : ℝ))⁻¹) ^ (m + 1) with hg
  have hgnn : ∀ p m, 0 ≤ g p m := by
    intro p m
    rw [hg]
    dsimp only
    split
    · exact le_rfl
    · have h1 : (0 : ℝ) ≤ ((m : ℝ) + 1) * (Real.log p * |b p|) :=
        mul_nonneg (by positivity) (mul_nonneg (Real.log_natCast_nonneg p) (abs_nonneg _))
      positivity
  have hmaj : ∀ z ∈ primePowerIndex X,
      |eulerTangentHigher b z| / ((z.1 : ℝ) ^ (z.2 + 1)) ≤ g z.1 z.2 := by
    intro z hz
    have hp := (mem_primePowerIndex.mp hz).1
    have hp0 : (0 : ℝ) < (z.1 : ℝ) := by exact_mod_cast hp.pos
    rw [hg]
    dsimp only
    by_cases hz2 : z.2 = 0
    · rw [if_pos hz2, eulerTangentHigher, if_pos hz2]
      simp
    · rw [if_neg hz2, eulerTangentHigher, if_neg hz2, eulerTangent, abs_mul, abs_mul,
        abs_of_nonneg (show (0 : ℝ) ≤ (z.2 : ℝ) + 1 by positivity),
        abs_of_nonneg (Real.log_natCast_nonneg z.1), inv_pow, ← div_eq_mul_inv]
      ring_nf
      rfl
  refine le_trans (primePowerMass_le_prod g X hmaj hgnn) ?_
  have hinner : ∀ p ∈ Nat.primesBelow (X + 1),
      ∑ m ∈ Finset.range (X + 1), g p m ≤ 6 * (Real.log p / p * |b p| / p) := by
    intro p hp
    obtain ⟨hplt, hpp⟩ := Nat.mem_primesBelow.mp hp
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.two_le
    have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
    set r : ℝ := ((p : ℝ))⁻¹ with hr
    have hr0 : 0 ≤ r := by positivity
    have hrhalf : r ≤ 1 / 2 := by
      rw [hr, ← one_div]
      exact one_div_le_one_div_of_le (by norm_num) hp2
    have hsub : Finset.Ico 1 (X + 1) ⊆ Finset.range (X + 1) := by
      intro m hm
      exact Finset.mem_range.mpr (Finset.mem_Ico.mp hm).2
    have hzeroOut : ∀ m ∈ Finset.range (X + 1), m ∉ Finset.Ico 1 (X + 1) → g p m = 0 := by
      intro m hm hnot
      have hm0 : m = 0 := by
        by_contra hne
        exact hnot (Finset.mem_Ico.mpr ⟨Nat.one_le_iff_ne_zero.mpr hne,
          Finset.mem_range.mp hm⟩)
      rw [hg]
      dsimp only
      rw [if_pos hm0]
    rw [← Finset.sum_subset hsub hzeroOut]
    have hIco : ∑ m ∈ Finset.Ico 1 (X + 1), g p m
        = (Real.log p * |b p|) * ∑ m ∈ Finset.Ico 1 (X + 1), ((m : ℝ) + 1) * r ^ (m + 1) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun m hm => ?_
      have hm0 : ¬ m = 0 := Nat.one_le_iff_ne_zero.mp (Finset.mem_Ico.mp hm).1
      rw [hg]
      dsimp only
      rw [if_neg hm0]
      ring
    rw [hIco]
    have hb := sum_Ico_succ_mul_pow_le hr0 hrhalf (X + 1)
    have hnn : (0 : ℝ) ≤ Real.log p * |b p| :=
      mul_nonneg (Real.log_natCast_nonneg p) (abs_nonneg _)
    have hval : (Real.log p * |b p|) * (6 * r ^ 2) = 6 * (Real.log p / p * |b p| / p) := by
      rw [hr]
      field_simp
    calc (Real.log p * |b p|) * ∑ m ∈ Finset.Ico 1 (X + 1), ((m : ℝ) + 1) * r ^ (m + 1)
        ≤ (Real.log p * |b p|) * (6 * r ^ 2) := mul_le_mul_of_nonneg_left hb hnn
      _ = 6 * (Real.log p / p * |b p| / p) := hval
  calc ∑ p ∈ Nat.primesBelow (X + 1), ∑ m ∈ Finset.range (X + 1), g p m
      ≤ ∑ p ∈ Nat.primesBelow (X + 1), 6 * (Real.log p / p * |b p| / p) :=
        Finset.sum_le_sum hinner
    _ = 6 * ∑ p ∈ Nat.primesBelow (X + 1), Real.log p / p * |b p| / p := by rw [Finset.mul_sum]
    _ ≤ 6 * (4 * K * Real.log 2) :=
        mul_le_mul_of_nonneg_left (sum_primesBelow_primeLog_div_le hK X) (by norm_num)
    _ = 24 * K * Real.log 2 := by ring

end RHTower
