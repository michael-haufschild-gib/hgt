import GaloisForLFunctions.RHTower.EulerDeletionFactorizationCurvature
import GaloisForLFunctions.RHTower.EulerDeletionPrimeAttenuation

/-!
# Compatible attenuation preserves the deletion curvature sign boundary

The coefficient is changed to `1 - (d / b d) [d ∣ n]` and the actual quadratic
mass to `b n ^ 2 * n ^ (-α)`. Complete multiplicativity gives an exact infinite
sum formula. The attenuation cancels from the final factor `1 - r ^ (2 - α)`.
This is an auxiliary normalization invariant, not an RH implication or a claim
that every such weight has the original source's ordinary convergence domain.
-/

noncomputable section
open scoped BigOperators
namespace RHTower.DeletionCompatibleCurvature

def amplitude (b : ℕ → ℝ) (d : ℕ) : ℝ := d / b d

def coefficient (b : ℕ → ℝ) (d n : ℕ) : ℝ :=
  1 - if d ∣ n then amplitude b d else 0

def massWeight (b : ℕ → ℝ) (α : ℝ) (n : ℕ) : ℝ :=
  b n ^ 2 * deletionDirichletWeight α n

def mass (b : ℕ → ℝ) (α : ℝ) : ℝ := ∑' n, massWeight b α n

def divisibilityWeight (b : ℕ → ℝ) (α : ℝ) (d n : ℕ) : ℝ :=
  if d ∣ n then massWeight b α n else 0

/-- The four channels are defined before their value is calculated. -/
def curvatureCoefficient (b : ℕ → ℝ) (p q r n : ℕ) : ℝ :=
  coefficient b p n * coefficient b q n ^ 2 +
  coefficient b (p*q) n * coefficient b r n ^ 2 -
  coefficient b q n * coefficient b r n ^ 2 -
  coefficient b p n * coefficient b (q*r) n ^ 2

def curvature (b : ℕ → ℝ) (α : ℝ) (p q r : ℕ) : ℝ :=
  ∑' n, curvatureCoefficient b p q r n * massWeight b α n

theorem amplitude_mul {b : ℕ → ℝ}
    (hm : ∀ m n, b (m*n) = b m * b n) (p q : ℕ) :
    amplitude b (p*q) = amplitude b p * amplitude b q := by
  simp only [amplitude, Nat.cast_mul, hm, mul_div_mul_comm]

theorem coefficient_mul {b : ℕ → ℝ}
    (hm : ∀ m n, b (m*n) = b m * b n) {p q : ℕ}
    (hpq : p.Coprime q) (n : ℕ) :
    coefficient b (p*q) n = coefficient b p n + coefficient b q n -
      coefficient b p n * coefficient b q n := by
  have hd : p*q ∣ n ↔ p ∣ n ∧ q ∣ n :=
    ⟨fun h => ⟨dvd_trans (dvd_mul_right p q) h, dvd_trans (dvd_mul_left q p) h⟩,
      fun h => hpq.mul_dvd_of_dvd_of_dvd h.1 h.2⟩
  by_cases hp : p ∣ n <;> by_cases hq : q ∣ n <;>
    simp [coefficient, hd, hp, hq, amplitude_mul hm]
  all_goals ring

theorem coefficient_sq (b : ℕ → ℝ) (q n : ℕ) :
    coefficient b q n ^ 2 = (amplitude b q - 1) +
      (2 - amplitude b q) * coefficient b q n := by
  by_cases h : q ∣ n <;> simp [coefficient, h] <;> ring

theorem curvatureCoefficient_linear {b : ℕ → ℝ}
    (hm : ∀ m n, b (m*n) = b m * b n) {p q r : ℕ}
    (hpq : p.Coprime q) (hpr : p.Coprime r) (hqr : q.Coprime r) (n : ℕ) :
    curvatureCoefficient b p q r n = (amplitude b q - 1) *
      (coefficient b (p*q) n - coefficient b q n + amplitude b r *
        (coefficient b (q*r) n - coefficient b (p*(q*r)) n)) := by
  rw [curvatureCoefficient, coefficient_sq, coefficient_sq, coefficient_sq]
  rw [coefficient_mul hm hpq, coefficient_mul hm hqr,
    coefficient_mul hm (hpq.mul_right hpr), coefficient_mul hm hqr,
    amplitude_mul hm]
  ring

theorem massWeight_nonneg (b : ℕ → ℝ) (α : ℝ) (n : ℕ) :
    0 ≤ massWeight b α n :=
  mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg n) _)

theorem summable_massWeight {b : ℕ → ℝ}
    (hb : ∀ n, 0 ≤ b n ∧ b n ≤ 1) {α : ℝ} (hα : 1 < α) :
    Summable (massWeight b α) := by
  apply (summable_deletionDirichletWeight hα).of_nonneg_of_le
    (massWeight_nonneg b α)
  intro n
  have hn := hb n
  have hs : b n ^ 2 ≤ 1 := by nlinarith
  exact mul_le_of_le_one_left (Real.rpow_nonneg (Nat.cast_nonneg n) _) hs

theorem mass_pos {b : ℕ → ℝ} (h1 : b 1 = 1)
    (hb : ∀ n, 0 ≤ b n ∧ b n ≤ 1) {α : ℝ} (hα : 1 < α) :
    0 < mass b α := by
  exact (summable_massWeight hb hα).tsum_pos (massWeight_nonneg b α) 1
    (by simp [massWeight, deletionDirichletWeight, h1])

theorem summable_divisibilityWeight {b : ℕ → ℝ}
    (hb : ∀ n, 0 ≤ b n ∧ b n ≤ 1) {α : ℝ} (hα : 1 < α) (d : ℕ) :
    Summable (divisibilityWeight b α d) := by
  apply ((summable_massWeight hb hα).indicator {n : ℕ | d ∣ n}).congr
  intro n
  simp [divisibilityWeight, Set.indicator_apply]

theorem tsum_divisibilityWeight {b : ℕ → ℝ}
    (hm : ∀ m n, b (m*n) = b m * b n) (α : ℝ) {d : ℕ} (hd : 0 < d) :
    ∑' n, divisibilityWeight b α d n =
      (b d ^ 2 * (d : ℝ)^(-α)) * mass b α := by
  have hi : Function.Injective (fun n : ℕ => d*n) :=
    fun _ _ h => Nat.mul_left_cancel hd h
  have hs : Function.support (divisibilityWeight b α d) ⊆
      Set.range (fun n : ℕ => d*n) := by
    intro n hn
    have hdv : d ∣ n := by
      by_contra hn'
      exact hn (by simp [divisibilityWeight, hn'])
    obtain ⟨k, rfl⟩ := hdv
    exact ⟨k, rfl⟩
  rw [← hi.tsum_eq hs]
  simp only [divisibilityWeight, dvd_mul_right, if_true, massWeight,
    deletionDirichletWeight, Nat.cast_mul, hm]
  calc
    (∑' n : ℕ, (b d * b n)^2 * ((d : ℝ)*n)^(-α)) =
        ∑' n : ℕ, (b d ^ 2 * (d : ℝ)^(-α)) * (b n ^ 2 * (n : ℝ)^(-α)) := by
      apply tsum_congr
      intro n
      rw [Real.mul_rpow (Nat.cast_nonneg d) (Nat.cast_nonneg n)]
      ring
    _ = _ := tsum_mul_left

theorem coefficient_mass_expansion (b : ℕ → ℝ) (α : ℝ) (d n : ℕ) :
    coefficient b d n * massWeight b α n =
      massWeight b α n - amplitude b d * divisibilityWeight b α d n := by
  by_cases h : d ∣ n <;> simp [coefficient, divisibilityWeight, h]
  all_goals ring

theorem summable_coefficient_mass {b : ℕ → ℝ}
    (hb : ∀ n, 0 ≤ b n ∧ b n ≤ 1) {α : ℝ} (hα : 1 < α) (d : ℕ) :
    Summable (fun n => coefficient b d n * massWeight b α n) := by
  simp_rw [coefficient_mass_expansion]
  exact (summable_massWeight hb hα).sub
    ((summable_divisibilityWeight hb hα d).mul_left (amplitude b d))

theorem tsum_coefficient_mass {b : ℕ → ℝ}
    (hm : ∀ m n, b (m*n) = b m * b n)
    (hb : ∀ n, 0 ≤ b n ∧ b n ≤ 1) {α : ℝ} (hα : 1 < α)
    {d : ℕ} (hd : 0 < d) :
    ∑' n, coefficient b d n * massWeight b α n =
      mass b α * (1 - d * b d * (d : ℝ)^(-α)) := by
  simp_rw [coefficient_mass_expansion]
  rw [(summable_massWeight hb hα).tsum_sub
    ((summable_divisibilityWeight hb hα d).mul_left (amplitude b d)),
    tsum_mul_left, tsum_divisibilityWeight hm α hd]
  change mass b α - _ = _
  unfold amplitude
  field_simp

theorem curvature_mass_linear {b : ℕ → ℝ}
    (hm : ∀ m n, b (m*n) = b m * b n) {p q r : ℕ}
    (hpq : p.Coprime q) (hpr : p.Coprime r) (hqr : q.Coprime r)
    (α : ℝ) (n : ℕ) :
    curvatureCoefficient b p q r n * massWeight b α n =
      (amplitude b q - 1) *
        ((coefficient b (p*q) n * massWeight b α n -
          coefficient b q n * massWeight b α n) + amplitude b r *
         (coefficient b (q*r) n * massWeight b α n -
          coefficient b (p*(q*r)) n * massWeight b α n)) := by
  rw [curvatureCoefficient_linear hm hpq hpr hqr]
  ring

theorem summable_curvature_mass {b : ℕ → ℝ}
    (hm : ∀ m n, b (m*n) = b m * b n)
    (hb : ∀ n, 0 ≤ b n ∧ b n ≤ 1) {α : ℝ} (hα : 1 < α)
    {p q r : ℕ} (hpq : p.Coprime q) (hpr : p.Coprime r) (hqr : q.Coprime r) :
    Summable (fun n => curvatureCoefficient b p q r n * massWeight b α n) := by
  simp_rw [curvature_mass_linear hm hpq hpr hqr]
  exact (((summable_coefficient_mass hb hα (p*q)).sub
    (summable_coefficient_mass hb hα q)).add
    (((summable_coefficient_mass hb hα (q*r)).sub
      (summable_coefficient_mass hb hα (p*(q*r)))).mul_left (amplitude b r))).mul_left _

/-- Exact factorization of the actual infinite curvature. The attenuation at `r`
disappears from the sign-changing factor. -/
theorem curvature_eq {b : ℕ → ℝ}
    (hm : ∀ m n, b (m*n) = b m * b n)
    (hb : ∀ n, 0 ≤ b n ∧ b n ≤ 1)
    (hpos : ∀ n, 0 < n → 0 < b n) {α : ℝ} (hα : 1 < α)
    {p q r : ℕ} (hp : 0 < p) (hq : 0 < q) (hr : 0 < r)
    (hpq : p.Coprime q) (hpr : p.Coprime r) (hqr : q.Coprime r) :
    curvature b α p q r = mass b α * (q * b q * (q : ℝ)^(-α)) *
      (1 - p * b p * (p : ℝ)^(-α)) * (q / b q - 1) * (1 - (r : ℝ)^(2-α)) := by
  unfold curvature
  simp_rw [curvature_mass_linear hm hpq hpr hqr]
  have hA := (summable_coefficient_mass hb hα (p*q)).sub
    (summable_coefficient_mass hb hα q)
  have hB := (summable_coefficient_mass hb hα (q*r)).sub
    (summable_coefficient_mass hb hα (p*(q*r)))
  rw [tsum_mul_left, hA.tsum_add (hB.mul_left (amplitude b r)), tsum_mul_left,
    (summable_coefficient_mass hb hα (p*q)).tsum_sub
      (summable_coefficient_mass hb hα q),
    (summable_coefficient_mass hb hα (q*r)).tsum_sub
      (summable_coefficient_mass hb hα (p*(q*r)))]
  rw [tsum_coefficient_mass hm hb hα (Nat.mul_pos hp hq),
    tsum_coefficient_mass hm hb hα hq,
    tsum_coefficient_mass hm hb hα (Nat.mul_pos hq hr),
    tsum_coefficient_mass hm hb hα (Nat.mul_pos hp (Nat.mul_pos hq hr))]
  have hrpow : (r : ℝ)^(2-α) = (r : ℝ)^2 * (r : ℝ)^(-α) := by
    rw [sub_eq_add_neg, Real.rpow_add (by exact_mod_cast hr), Real.rpow_two]
  rw [hrpow]
  simp only [amplitude, Nat.cast_mul, hm,
    Real.mul_rpow (Nat.cast_nonneg p) (Nat.cast_nonneg q),
    Real.mul_rpow (Nat.cast_nonneg q) (Nat.cast_nonneg r),
    Real.mul_rpow (Nat.cast_nonneg p) (mul_nonneg (Nat.cast_nonneg q) (Nat.cast_nonneg r))]
  field_simp [ne_of_gt (hpos q hq), ne_of_gt (hpos r hr)]
  ring

theorem curvature_prefactor_pos {b : ℕ → ℝ} (h1 : b 1 = 1)
    (hb : ∀ n, 0 ≤ b n ∧ b n ≤ 1)
    (hpos : ∀ n, 0 < n → 0 < b n) {α : ℝ} (hα : 1 < α)
    {p q : ℕ} (hp : 1 < p) (hq : 1 < q) :
    0 < mass b α * (q * b q * (q : ℝ)^(-α)) *
      (1 - p * b p * (p : ℝ)^(-α)) * (q / b q - 1) := by
  have hpR : 1 < (p : ℝ) := by exact_mod_cast hp
  have hqR : 1 < (q : ℝ) := by exact_mod_cast hq
  have hpmean := deletionDirichletMean_pos hα hp
  have hpcompare : (p : ℝ) * b p * (p : ℝ)^(-α) ≤ p * (p : ℝ)^(-α) := by
    calc
      _ ≤ (p : ℝ) * 1 * (p : ℝ)^(-α) := by
        gcongr
        exact (hb p).2
      _ = _ := by ring
  have hpmean' : 0 < 1 - p * b p * (p : ℝ)^(-α) := by linarith
  have hqamp : 1 < (q : ℝ) / b q := (lt_div_iff₀ (hpos q (by omega))).mpr (by
    have := (hb q).2
    nlinarith)
  have hmass := mass_pos h1 hb hα
  have hqpos := hpos q (by omega)
  have hqpow := Real.rpow_pos_of_pos (by linarith : 0 < (q : ℝ)) (-α)
  positivity

theorem curvature_neg {b : ℕ → ℝ}
    (hm : ∀ m n, b (m*n) = b m * b n) (h1 : b 1 = 1)
    (hb : ∀ n, 0 ≤ b n ∧ b n ≤ 1)
    (hpos : ∀ n, 0 < n → 0 < b n) {α : ℝ} (hα : 1 < α) (hα2 : α < 2)
    {p q r : ℕ} (hp : 1 < p) (hq : 1 < q) (hr : 1 < r)
    (hpq : p.Coprime q) (hpr : p.Coprime r) (hqr : q.Coprime r) :
    curvature b α p q r < 0 := by
  rw [curvature_eq hm hb hpos hα (by omega) (by omega) (by omega) hpq hpr hqr]
  have hrR : 0 < (r : ℝ) := by exact_mod_cast (by omega : 0 < r)
  have hr1 : (1 : ℝ) < r := by exact_mod_cast hr
  have hrpow : 1 < (r : ℝ) ^ (2-α) :=
    (Real.one_lt_rpow_iff_of_pos hrR).2 (Or.inl ⟨hr1, by linarith⟩)
  exact mul_neg_of_pos_of_neg (curvature_prefactor_pos h1 hb hpos hα hp hq)
    (sub_neg.mpr hrpow)

theorem curvature_zero_at_two {b : ℕ → ℝ}
    (hm : ∀ m n, b (m*n) = b m * b n)
    (hb : ∀ n, 0 ≤ b n ∧ b n ≤ 1)
    (hpos : ∀ n, 0 < n → 0 < b n)
    {p q r : ℕ} (hp : 0 < p) (hq : 0 < q) (hr : 0 < r)
    (hpq : p.Coprime q) (hpr : p.Coprime r) (hqr : q.Coprime r) :
    curvature b 2 p q r = 0 := by
  rw [curvature_eq hm hb hpos (by norm_num) hp hq hr hpq hpr hqr]
  norm_num

theorem curvature_pos {b : ℕ → ℝ}
    (hm : ∀ m n, b (m*n) = b m * b n) (h1 : b 1 = 1)
    (hb : ∀ n, 0 ≤ b n ∧ b n ≤ 1)
    (hpos : ∀ n, 0 < n → 0 < b n) {α : ℝ} (hα2 : 2 < α)
    {p q r : ℕ} (hp : 1 < p) (hq : 1 < q) (hr : 1 < r)
    (hpq : p.Coprime q) (hpr : p.Coprime r) (hqr : q.Coprime r) :
    0 < curvature b α p q r := by
  have hα : 1 < α := by linarith
  rw [curvature_eq hm hb hpos hα (by omega) (by omega) (by omega) hpq hpr hqr]
  have hr1 : (1 : ℝ) < r := by exact_mod_cast hr
  have hrpow : (r : ℝ) ^ (2-α) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg hr1 (by linarith)
  exact mul_pos (curvature_prefactor_pos h1 hb hpos hα hp hq) (sub_pos.mpr hrpow)

/-- Complete vanishing boundary, with strict signs proved on both sides. -/
theorem curvature_eq_zero_iff {b : ℕ → ℝ}
    (hm : ∀ m n, b (m*n) = b m * b n) (h1 : b 1 = 1)
    (hb : ∀ n, 0 ≤ b n ∧ b n ≤ 1)
    (hpos : ∀ n, 0 < n → 0 < b n) {α : ℝ} (hα : 1 < α)
    {p q r : ℕ} (hp : 1 < p) (hq : 1 < q) (hr : 1 < r)
    (hpq : p.Coprime q) (hpr : p.Coprime r) (hqr : q.Coprime r) :
    curvature b α p q r = 0 ↔ α = 2 := by
  constructor
  · intro hz
    rcases lt_trichotomy α 2 with hlt | heq | hgt
    · exact False.elim ((ne_of_lt (curvature_neg hm h1 hb hpos hα hlt hp hq hr hpq hpr hqr)) hz)
    · exact heq
    · exact False.elim ((ne_of_gt (curvature_pos hm h1 hb hpos hgt hp hq hr hpq hpr hqr)) hz)
  · rintro rfl
    exact curvature_zero_at_two hm hb hpos (by omega) (by omega) (by omega) hpq hpr hqr

/-- If the first two labels are unchanged, the normalized curvature is exactly
unchanged, even when the rest of the multiplicative weight is altered. -/
theorem normalized_curvature_invariant {b : ℕ → ℝ}
    (hm : ∀ m n, b (m*n) = b m * b n) (h1 : b 1 = 1)
    (hb : ∀ n, 0 ≤ b n ∧ b n ≤ 1)
    (hpos : ∀ n, 0 < n → 0 < b n) {α : ℝ} (hα : 1 < α)
    {p q r : ℕ} (hp : 0 < p) (hq : 0 < q) (hr : 0 < r)
    (hpq : p.Coprime q) (hpr : p.Coprime r) (hqr : q.Coprime r)
    (hbp : b p = 1) (hbq : b q = 1) :
    curvature b α p q r / mass b α =
      deletionFactorizationGradeCurvature α p q r / deletionDirichletMass α := by
  rw [curvature_eq hm hb hpos hα hp hq hr hpq hpr hqr,
    deletionFactorizationGradeCurvature_eq_of_pairwise_coprime hα hp hq hr hpq hpr hqr,
    hbp, hbq]
  field_simp [ne_of_gt (mass_pos h1 hb hα), ne_of_gt (deletionDirichletMass_pos hα)]

/-- Every strictly positive attenuation at five leaves the normalized `2,3,5`
curvature unchanged after the compatible coefficient repair. -/
theorem fifth_attenuation_normalized_curvature {c α : ℝ}
    (hc : 0 < c) (hc1 : c ≤ 1) (hα : 1 < α) :
    let b := DeletionPrimeAttenuation.weight 5 c
    curvature b α 2 3 5 / mass b α =
      deletionFactorizationGradeCurvature α 2 3 5 / deletionDirichletMass α := by
  dsimp only
  apply normalized_curvature_invariant
    (DeletionPrimeAttenuation.weight_mul _ _) (DeletionPrimeAttenuation.weight_one _ _)
    (fun n => ⟨DeletionPrimeAttenuation.weight_nonneg _ hc.le n,
      DeletionPrimeAttenuation.weight_le_one _ hc.le hc1 n⟩)
    (fun n hn => DeletionPrimeAttenuation.weight_pos _ hc hn) hα
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · exact DeletionPrimeAttenuation.weight_of_not_dvd (by norm_num : ¬5 ∣ 2) c
  · exact DeletionPrimeAttenuation.weight_of_not_dvd (by norm_num : ¬5 ∣ 3) c

/-- A fixed closed instance uses the same weight whose unique ordinary-admission
repair has multiplier 25. The actual repaired curvature still has both signs. -/
theorem fifth_attenuation_curvature_boundary :
    let b := DeletionPrimeAttenuation.weight 5 (1/5 : ℝ)
    amplitude b 5 = 25 ∧ curvature b (3/2) 2 3 5 < 0 ∧
      curvature b 2 2 3 5 = 0 ∧ 0 < curvature b 3 2 3 5 := by
  dsimp only
  let b := DeletionPrimeAttenuation.weight 5 (1/5 : ℝ)
  have hm : ∀ m n, b (m*n) = b m * b n := DeletionPrimeAttenuation.weight_mul _ _
  have h1 : b 1 = 1 := DeletionPrimeAttenuation.weight_one _ _
  have hb : ∀ n, 0 ≤ b n ∧ b n ≤ 1 := fun n =>
    ⟨DeletionPrimeAttenuation.weight_nonneg _ (by norm_num) n,
     DeletionPrimeAttenuation.weight_le_one _ (by norm_num) (by norm_num) n⟩
  have hpos : ∀ n, 0 < n → 0 < b n := fun n hn =>
    DeletionPrimeAttenuation.weight_pos _ (by norm_num) hn
  refine ⟨?_, curvature_neg hm h1 hb hpos (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    curvature_zero_at_two hm hb hpos (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num),
    curvature_pos hm h1 hb hpos (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)⟩
  unfold amplitude
  rw [DeletionPrimeAttenuation.weight_prime (by norm_num : Nat.Prime 5)]
  norm_num

end RHTower.DeletionCompatibleCurvature
