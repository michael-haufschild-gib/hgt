import GaloisForLFunctions.SignedArithmeticEnergyIncidence.BalancedIncidenceIsLocallyPayable
import GaloisForLFunctions.SignedArithmeticEnergyIncidence.FrustrationIsTheLocalGlobalGap

/-!
# Triangle holonomy decides local payment

On a **complete overlap pattern** — every pair of points overlaps with a nonzero charge — the
sign of the product `c_ij c_jk c_ki` around a triangle is its **holonomy**.  It is switching
invariant (`triangleHolonomy_switch`): a gauge-free diagnostic computed from the source before any
profile or gauge is chosen.

* **Holonomy decides balance** (`isBalanced_iff_triangleHolonomy_neg`): a complete overlap form is
  balanced iff every triangle has negative holonomy.
* **Signed local–global principle** (`localPayment_lossless_iff`): for a symmetric sign pattern
  `σ` on the pairs of a finite set, *every* nonnegative form whose overlap charges carry the
  signs `σ` is locally payable **iff** every triangle of `σ` has holonomy `−1`.  One direction is
  `BalancedIncidenceIsLocallyPayable`; for the other, a triangle of holonomy `+1` is completed to an
  explicit positive form with charges `¾ σ` on the triangle and `σ/(4n)` elsewhere, which inherits
  the unpayable frustrated triangle (`exists_nonneg_not_locallyPayable_of_holonomy_pos`).

The pre-profile orientation law (all holonomies negative) is thus exactly what makes local
payment lossless; a single frustrated triangle anywhere in the overlap pattern can make it fail.
-/

open Finset

namespace GaloisForLFunctions.SignedArithmeticEnergyIncidence

noncomputable section
set_option autoImplicit false

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The holonomy of the triangle `i, j, k`. -/
def triangleHolonomy (c : ι → ι → ℝ) (i j k : ι) : ℝ := c i j * c j k * c k i

omit [Fintype ι] [DecidableEq ι] in
/-- Holonomy is switching invariant. -/
theorem triangleHolonomy_switch {s : ι → ℝ} (hs : ∀ i, s i ^ 2 = 1) (c : ι → ι → ℝ)
    (i j k : ι) : triangleHolonomy (switchCoupling s c) i j k = triangleHolonomy c i j k := by
  unfold triangleHolonomy switchCoupling
  calc s i * s j * c i j * (s j * s k * c j k) * (s k * s i * c k i)
      = s i ^ 2 * s j ^ 2 * s k ^ 2 * (c i j * c j k * c k i) := by ring
    _ = c i j * c j k * c k i := by rw [hs i, hs j, hs k]; ring

/-- A coupling with every overlap charge nonzero. -/
def IsCompleteOverlap (c : ι → ι → ℝ) : Prop := ∀ i j, i ≠ j → c i j ≠ 0

omit [Fintype ι] in
/-- **Holonomy decides balance** on a complete overlap pattern. -/
theorem isBalanced_iff_triangleHolonomy_neg {c : ι → ι → ℝ} (hc : IsSymmetricCoupling c)
    (hco : IsCompleteOverlap c) :
    IsBalanced c ↔ ∀ i j k, i ≠ j → j ≠ k → k ≠ i → triangleHolonomy c i j k < 0 := by
  constructor
  · rintro ⟨s, hs, hz⟩ i j k hij hjk hki
    have hneg : ∀ p q, p ≠ q → s p * s q * c p q < 0 := by
      intro p q hpq
      refine lt_of_le_of_ne (hz p q hpq) fun h0 => hco p q hpq ?_
      have h1 : s p * s q ≠ 0 := by
        intro h
        rcases mul_eq_zero.mp h with h | h
        · have := hs p; rw [h] at this; norm_num at this
        · have := hs q; rw [h] at this; norm_num at this
      exact (mul_eq_zero.mp h0).resolve_left h1
    rw [← triangleHolonomy_switch hs]
    unfold triangleHolonomy
    have h1 := hneg i j hij
    have h2 := hneg j k hjk
    have h3 := hneg k i hki
    exact mul_neg_of_pos_of_neg (mul_pos_of_neg_of_neg h1 h2) h3
  · intro htri
    by_cases hne : Nonempty ι
    · obtain ⟨i₀⟩ := hne
      -- gauge: `s i₀ = 1` and `s i = −sign c_{i₀ i}` elsewhere
      set s : ι → ℝ := fun i => if i = i₀ then 1 else -(c i₀ i / |c i₀ i|) with hsdef
      have habs : ∀ i, i ≠ i₀ → 0 < |c i₀ i| := fun i hi => abs_pos.mpr (hco i₀ i (Ne.symm hi))
      have hs : ∀ i, s i ^ 2 = 1 := by
        intro i
        by_cases hi : i = i₀
        · simp [hsdef, hi]
        · simp only [hsdef, hi, if_false, neg_sq, div_pow, sq_abs]
          exact div_self (pow_ne_zero 2 (hco i₀ i (Ne.symm hi)))
      refine ⟨s, hs, fun i j hij => ?_⟩
      simp only [switchCoupling]
      by_cases hi : i = i₀
      · subst hi
        have hj : j ≠ i := Ne.symm hij
        simp only [hsdef, if_true, hj, if_false, one_mul]
        rw [neg_mul, neg_nonpos, div_mul_eq_mul_div]
        exact div_nonneg (mul_self_nonneg _) (abs_nonneg _)
      · by_cases hj : j = i₀
        · subst hj
          simp only [hsdef, if_true, hi, if_false, mul_one]
          rw [hc i j, neg_mul, neg_nonpos, div_mul_eq_mul_div]
          exact div_nonneg (mul_self_nonneg _) (abs_nonneg _)
        · simp only [hsdef, hi, hj, if_false]
          have hai := habs i hi
          have haj := habs j hj
          have ht := htri i₀ i j (Ne.symm hi) hij hj
          unfold triangleHolonomy at ht
          have e : -(c i₀ i / |c i₀ i|) * -(c i₀ j / |c i₀ j|) * c i j =
              (c i₀ i * c i j * c j i₀) / (|c i₀ i| * |c i₀ j|) := by
            rw [hc j i₀]
            field_simp
          rw [e]
          exact (div_neg_of_neg_of_pos ht (mul_pos hai haj)).le
    · refine ⟨fun _ => 1, fun _ => by norm_num, fun i _ _ => ?_⟩
      exact absurd ⟨i⟩ hne

/-! ### Sign patterns -/

/-- A symmetric sign pattern on the pairs of distinct points. -/
structure SignPattern (ι : Type*) where
  sign : ι → ι → ℝ
  sign_sq : ∀ i j, i ≠ j → sign i j ^ 2 = 1
  sign_symm : ∀ i j, sign i j = sign j i

/-- A coupling realizes the pattern when every overlap charge is a positive multiple of its sign. -/
def Realizes (σ : SignPattern ι) (c : ι → ι → ℝ) : Prop :=
  ∀ i j, i ≠ j → 0 < c i j * σ.sign i j

omit [Fintype ι] [DecidableEq ι] in
theorem Realizes.isCompleteOverlap {σ : SignPattern ι} {c : ι → ι → ℝ} (h : Realizes σ c) :
    IsCompleteOverlap c := fun i j hij h0 => by
  have := h i j hij; rw [h0, zero_mul] at this; exact lt_irrefl 0 this

omit [Fintype ι] [DecidableEq ι] in
theorem Realizes.holonomy_neg_iff {σ : SignPattern ι} {c : ι → ι → ℝ} (h : Realizes σ c)
    {i j k : ι} (hij : i ≠ j) (hjk : j ≠ k) (hki : k ≠ i) :
    triangleHolonomy c i j k < 0 ↔ triangleHolonomy σ.sign i j k < 0 := by
  have h1 := h i j hij
  have h2 := h j k hjk
  have h3 := h k i hki
  have hp : 0 < (c i j * σ.sign i j) * (c j k * σ.sign j k) * (c k i * σ.sign k i) :=
    mul_pos (mul_pos h1 h2) h3
  have e : (c i j * σ.sign i j) * (c j k * σ.sign j k) * (c k i * σ.sign k i) =
      triangleHolonomy c i j k * triangleHolonomy σ.sign i j k := by
    unfold triangleHolonomy; ring
  rw [e] at hp
  constructor
  · intro hc
    by_contra hs
    have hs := not_lt.mp hs
    nlinarith
  · intro hs
    by_contra hc
    have hc := not_lt.mp hc
    nlinarith

/-- **Aligned holonomy makes local payment lossless.** -/
theorem nonneg_iff_locallyPayable_of_holonomy {σ : SignPattern ι}
    (hσ : ∀ i j k, i ≠ j → j ≠ k → k ≠ i → triangleHolonomy σ.sign i j k < 0)
    {c : ι → ι → ℝ} (hc : IsSymmetricCoupling c) (hr : Realizes σ c) :
    (∀ f, 0 ≤ incidenceEnergy c f) ↔ LocallyPayable c := by
  refine nonneg_iff_locallyPayable_of_isBalanced hc ?_
  refine (isBalanced_iff_triangleHolonomy_neg hc hr.isCompleteOverlap).mpr fun i j k hij hjk hki =>
    (hr.holonomy_neg_iff hij hjk hki).mpr (hσ i j k hij hjk hki)

/-! ### A frustrated triangle spoils local payment -/

/-- Off-diagonal products of absolute values are at most `n − 1` times the mass. -/
theorem sum_offDiag_abs_mul_le (f : ι → ℝ) :
    ∑ i, ∑ j ∈ univ.erase i, |f i| * |f j| ≤ ((Fintype.card ι : ℝ) - 1) * ∑ i, f i ^ 2 := by
  have h1 : ∀ i j, |f i| * |f j| ≤ (f i ^ 2 + f j ^ 2) / 2 := by
    intro i j
    nlinarith [sq_nonneg (|f i| - |f j|), sq_abs (f i), sq_abs (f j)]
  have h2 : ∑ i, ∑ j ∈ univ.erase i, (f i ^ 2 + f j ^ 2) / 2 =
      ((Fintype.card ι : ℝ) - 1) * ∑ i, f i ^ 2 := by
    have hswap := sum_offDiag_swap (fun i j => f i ^ 2 / 2)
    have e : ∀ i, ∑ j ∈ univ.erase i, (f i ^ 2 + f j ^ 2) / 2 =
        ∑ j ∈ univ.erase i, f i ^ 2 / 2 + ∑ j ∈ univ.erase i, f j ^ 2 / 2 := by
      intro i; rw [← sum_add_distrib]; exact sum_congr rfl fun j _ => by ring
    rw [sum_congr rfl fun i _ => e i, sum_add_distrib, ← hswap]
    have e2 : ∀ i : ι, ∑ _j ∈ univ.erase i, f i ^ 2 / 2 =
        ((Fintype.card ι : ℝ) - 1) * (f i ^ 2 / 2) := by
      intro i
      rw [sum_const, card_erase_of_mem (mem_univ i), card_univ, nsmul_eq_mul]
      have : 1 ≤ Fintype.card ι := Fintype.card_pos_iff.mpr ⟨i⟩
      push_cast [Nat.cast_sub this]
      ring
    simp only [e2, mul_sum]
    rw [← sum_add_distrib]
    exact sum_congr rfl fun i _ => by ring
  calc _ ≤ ∑ i, ∑ j ∈ univ.erase i, (f i ^ 2 + f j ^ 2) / 2 :=
        sum_le_sum fun i _ => sum_le_sum fun j _ => h1 i j
    _ = _ := h2

/-- A coupling with zero diagonal and off-diagonal charges of size at most `η` costs at most
`η (n − 1)` of the mass. -/
theorem incidenceEnergy_ge_of_small {c : ι → ι → ℝ} {η : ℝ} (hη : 0 ≤ η)
    (hdiag : ∀ i, c i i = 0) (hsmall : ∀ i j, i ≠ j → |c i j| ≤ η) (f : ι → ℝ) :
    -(η * ((Fintype.card ι : ℝ) - 1) * ∑ i, f i ^ 2) ≤ incidenceEnergy c f := by
  rw [incidenceEnergy_eq_diag_add_offDiag]
  simp only [hdiag, zero_mul, sum_const_zero, zero_add]
  have h1 : ∀ i, ∀ j ∈ univ.erase i, -(η * (|f i| * |f j|)) ≤ c i j * f i * f j := by
    intro i j hj
    have hij : i ≠ j := (ne_of_mem_erase hj).symm
    have h2 : |c i j * f i * f j| ≤ η * (|f i| * |f j|) := by
      rw [abs_mul, abs_mul, mul_assoc]
      exact mul_le_mul_of_nonneg_right (hsmall i j hij) (by positivity)
    linarith [neg_abs_le (c i j * f i * f j)]
  have h3 : ∑ i, ∑ j ∈ univ.erase i, -(η * (|f i| * |f j|)) =
      -(η * ∑ i, ∑ j ∈ univ.erase i, |f i| * |f j|) := by
    simp only [sum_neg_distrib, mul_sum]
  have h4 := sum_offDiag_abs_mul_le f
  have h5 := sum_le_sum fun i (_ : i ∈ univ) => sum_le_sum (h1 i)
  rw [h3] at h5
  nlinarith

/-- The triangle gauge: `s_a = 1`, `s_b = σ_ab`, `s_c = σ_ac`, and `0` off the triangle. -/
def triangleGauge (σ : SignPattern ι) (a b c : ι) (x : ι) : ℝ :=
  if x = a then 1 else if x = b then σ.sign a b else if x = c then σ.sign a c else 0

/-- The witness coupling: the rank-one charge `¾ s_i s_j` of the switched triangle, unit budgets,
and charges `σ/(4n)` off the triangle. -/
def frustrationWitness (σ : SignPattern ι) (a b c : ι) : ι → ι → ℝ := fun i j =>
  3 / 4 * (triangleGauge σ a b c i * triangleGauge σ a b c j) +
    (if i = j then (if triangleGauge σ a b c i = 0 then 1 else 1 / 4) else 0) +
    (if i = j then 0 else if triangleGauge σ a b c i ≠ 0 ∧ triangleGauge σ a b c j ≠ 0 then 0
      else 1 / (4 * (Fintype.card ι : ℝ)) * σ.sign i j)

section Witness

variable (σ : SignPattern ι) {a b c : ι} (hab : a ≠ b) (hbc : b ≠ c) (hca : c ≠ a)
include hab hbc hca

omit [Fintype ι] in
theorem triangleGauge_sq_of_mem {x : ι} (hx : x = a ∨ x = b ∨ x = c) :
    triangleGauge σ a b c x ^ 2 = 1 := by
  unfold triangleGauge
  rcases hx with rfl | rfl | rfl
  · simp
  · simp [hab.symm, σ.sign_sq _ _ hab]
  · simp [hca, hbc.symm, σ.sign_sq _ _ hca.symm]

omit [Fintype ι] in
theorem triangleGauge_eq_zero_iff (x : ι) :
    triangleGauge σ a b c x = 0 ↔ ¬ (x = a ∨ x = b ∨ x = c) := by
  constructor
  · intro h hx
    have := triangleGauge_sq_of_mem σ hab hbc hca hx
    rw [h] at this; norm_num at this
  · intro h
    push Not at h
    simp [triangleGauge, h.1, h.2.1, h.2.2]

omit [Fintype ι] in
/-- With holonomy `+1` the switched triangle reproduces the triangle signs. -/
theorem triangleGauge_mul (hhol : triangleHolonomy σ.sign a b c = 1) {x y : ι}
    (hx : x = a ∨ x = b ∨ x = c) (hy : y = a ∨ y = b ∨ y = c) (hxy : x ≠ y) :
    triangleGauge σ a b c x * triangleGauge σ a b c y = σ.sign x y := by
  have hbc' : σ.sign b c = σ.sign a b * σ.sign a c := by
    have h1 := σ.sign_sq a b hab
    have h2 := σ.sign_sq a c hca.symm
    have hh : σ.sign a b * σ.sign b c * σ.sign a c = 1 := by
      rw [← σ.sign_symm c a]; exact hhol
    calc σ.sign b c = σ.sign b c * (σ.sign a b ^ 2 * σ.sign a c ^ 2) := by rw [h1, h2]; ring
      _ = (σ.sign a b * σ.sign b c * σ.sign a c) * (σ.sign a b * σ.sign a c) := by ring
      _ = σ.sign a b * σ.sign a c := by rw [hh, one_mul]
  have hcb' : σ.sign c b = σ.sign a b * σ.sign a c := by rw [σ.sign_symm, hbc']
  unfold triangleGauge
  rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
  all_goals first
    | exact absurd rfl hxy
    | (simp [hab.symm, hbc.symm, hca, hbc', hcb', mul_comm]) <;> exact σ.sign_symm _ _

omit hab hbc hca in
theorem frustrationWitness_isSymmetric : IsSymmetricCoupling (frustrationWitness σ a b c) := by
  intro i j
  unfold frustrationWitness
  by_cases h : i = j
  · subst h; rfl
  · simp only [h, Ne.symm h, if_false, σ.sign_symm i j, and_comm, mul_comm]

theorem frustrationWitness_offDiag {i j : ι} (hij : i ≠ j) :
    frustrationWitness σ a b c i j =
      if (i = a ∨ i = b ∨ i = c) ∧ (j = a ∨ j = b ∨ j = c) then
        3 / 4 * (triangleGauge σ a b c i * triangleGauge σ a b c j)
      else 1 / (4 * (Fintype.card ι : ℝ)) * σ.sign i j := by
  unfold frustrationWitness
  simp only [hij, if_false, add_zero]
  have hi := triangleGauge_eq_zero_iff σ hab hbc hca i
  have hj := triangleGauge_eq_zero_iff σ hab hbc hca j
  by_cases hT : (i = a ∨ i = b ∨ i = c) ∧ (j = a ∨ j = b ∨ j = c)
  · rw [if_pos hT, if_pos ⟨fun h => (hi.mp h) hT.1, fun h => (hj.mp h) hT.2⟩, add_zero]
  · rw [if_neg hT]
    have hz : triangleGauge σ a b c i * triangleGauge σ a b c j = 0 := by
      rcases not_and_or.mp hT with h | h
      · rw [hi.mpr h, zero_mul]
      · rw [hj.mpr h, mul_zero]
    have hn : ¬ (triangleGauge σ a b c i ≠ 0 ∧ triangleGauge σ a b c j ≠ 0) := by
      rintro ⟨h1, h2⟩; exact h1 (by rcases mul_eq_zero.mp hz with h | h <;> [exact h; exact absurd h h2])
    rw [if_neg hn, hz, mul_zero, zero_add]

theorem frustrationWitness_diag (i : ι) : frustrationWitness σ a b c i i = 1 := by
  unfold frustrationWitness
  simp only [if_true]
  by_cases hT : i = a ∨ i = b ∨ i = c
  · have h1 := triangleGauge_sq_of_mem σ hab hbc hca hT
    have h0 : triangleGauge σ a b c i ≠ 0 := fun h => by rw [h] at h1; norm_num at h1
    rw [if_neg h0, ← sq, h1]
    norm_num
  · have h0 := (triangleGauge_eq_zero_iff σ hab hbc hca i).mpr hT
    rw [if_pos h0, h0]
    norm_num

theorem frustrationWitness_realizes (hhol : triangleHolonomy σ.sign a b c = 1) :
    Realizes σ (frustrationWitness σ a b c) := by
  intro i j hij
  have hcard : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos_iff.mpr ⟨i⟩
  rw [frustrationWitness_offDiag σ hab hbc hca hij]
  have hs := σ.sign_sq i j hij
  split_ifs with hT
  · rw [triangleGauge_mul σ hab hbc hca hhol hT.1 hT.2 hij, mul_assoc, ← sq, hs]; norm_num
  · rw [mul_assoc, ← sq, hs, mul_one]; positivity

omit hab hbc hca in
/-- **The witness is positive**: the switched triangle keeps a quarter of each budget, and the
small charges cost at most `(n − 1)/(4n)` of the mass. -/
theorem frustrationWitness_nonneg (f : ι → ℝ) :
    0 ≤ incidenceEnergy (frustrationWitness σ a b c) f := by
  set t := triangleGauge σ a b c
  set n : ℝ := ((Fintype.card ι : ℕ) : ℝ) with hn
  have hn1 : (1 : ℝ) ≤ n := by
    rw [hn]; exact_mod_cast Fintype.card_pos_iff.mpr ⟨a⟩
  set η : ℝ := 1 / (4 * n) with hη
  set W1 : ι → ι → ℝ := fun i j => 3 / 4 * (t i * t j)
  set W2 : ι → ι → ℝ := fun i j => if i = j then (if t i = 0 then 1 else 1 / 4) else 0
  set W3 : ι → ι → ℝ := fun i j =>
    if i = j then 0 else if t i ≠ 0 ∧ t j ≠ 0 then 0 else η * σ.sign i j
  have hsplit : incidenceEnergy (frustrationWitness σ a b c) f =
      incidenceEnergy W1 f + incidenceEnergy W2 f + incidenceEnergy W3 f := by
    unfold incidenceEnergy
    rw [← sum_add_distrib, ← sum_add_distrib]
    refine sum_congr rfl fun i _ => ?_
    rw [← sum_add_distrib, ← sum_add_distrib]
    refine sum_congr rfl fun j _ => ?_
    simp only [frustrationWitness, W1, W2, W3, t, hη, hn]
    ring
  have h1 : 0 ≤ incidenceEnergy W1 f := by
    have : incidenceEnergy W1 f = 3 / 4 * incidenceEnergy (rankOneCoupling t) f := by
      unfold incidenceEnergy rankOneCoupling
      rw [mul_sum]
      exact sum_congr rfl fun i _ => by rw [mul_sum]; exact sum_congr rfl fun j _ => by ring
    rw [this]
    exact mul_nonneg (by norm_num) (incidenceEnergy_rankOneCoupling_nonneg t f)
  have h2 : (1 / 4) * ∑ i, f i ^ 2 ≤ incidenceEnergy W2 f := by
    rw [incidenceEnergy_eq_diag_add_offDiag]
    have hoff : ∑ i, ∑ j ∈ univ.erase i, W2 i j * f i * f j = 0 :=
      sum_eq_zero fun i _ => sum_eq_zero fun j hj => by
        simp [W2, (ne_of_mem_erase hj).symm]
    rw [hoff, add_zero, mul_sum]
    refine sum_le_sum fun i _ => ?_
    simp only [W2, if_true]
    split_ifs <;> nlinarith [sq_nonneg (f i)]
  have h3 : -(η * (n - 1) * ∑ i, f i ^ 2) ≤ incidenceEnergy W3 f := by
    refine incidenceEnergy_ge_of_small (by positivity) (fun i => by simp [W3]) (fun i j hij => ?_) f
    simp only [W3, hij, if_false]
    split_ifs
    · rw [abs_zero]; positivity
    · rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < η)]
      have h := σ.sign_sq i j hij
      have : |σ.sign i j| = 1 := by
        rw [← sq_abs] at h; nlinarith [abs_nonneg (σ.sign i j)]
      rw [this, mul_one]
  have hmass : 0 ≤ ∑ i, f i ^ 2 := sum_nonneg fun i _ => sq_nonneg _
  have hηn : η * (n - 1) ≤ 1 / 4 := by
    rw [hη, div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
    linarith
  rw [hsplit]
  nlinarith

/-- **The witness is not locally payable**: its triangle needs `9/2` from budgets `3`. -/
theorem frustrationWitness_not_locallyPayable :
    ¬ LocallyPayable (frustrationWitness σ a b c) := by
  rintro ⟨A⟩
  have hmem : ∀ x, x = a ∨ x = b ∨ x = c → x = a ∨ x = b ∨ x = c := fun _ h => h
  have hpair : ∀ i j, (i = a ∨ i = b ∨ i = c) → (j = a ∨ j = b ∨ j = c) → i ≠ j →
      3 / 2 ≤ A.share i j + A.share j i := by
    intro i j hi hj hij
    have hp := A.pays i j hij
    rw [frustrationWitness_offDiag σ hab hbc hca hij, if_pos ⟨hi, hj⟩, mul_pow, mul_pow,
      triangleGauge_sq_of_mem σ hab hbc hca hi, triangleGauge_sq_of_mem σ hab hbc hca hj] at hp
    have h1 := A.share_nonneg i j
    have h2 := A.share_nonneg j i
    nlinarith [sq_nonneg (A.share i j - A.share j i)]
  have hbudget : ∀ i j k, j ≠ i → k ≠ i → j ≠ k → A.share i j + A.share i k ≤ 1 := by
    intro i j k hji hki hjk
    have h := A.within_budget i
    rw [frustrationWitness_diag σ hab hbc hca] at h
    have hsub : ({j, k} : Finset ι) ⊆ univ.erase i := by
      intro x hx
      simp only [mem_insert, mem_singleton] at hx
      rcases hx with rfl | rfl <;> simp_all
    have := sum_le_sum_of_subset_of_nonneg hsub fun x _ _ => A.share_nonneg i x
    rw [sum_pair hjk] at this
    linarith
  have p1 := hpair a b (Or.inl rfl) (Or.inr (Or.inl rfl)) hab
  have p2 := hpair b c (Or.inr (Or.inl rfl)) (Or.inr (Or.inr rfl)) hbc
  have p3 := hpair c a (Or.inr (Or.inr rfl)) (Or.inl rfl) hca
  have b1 := hbudget a b c (Ne.symm hab) hca hbc
  have b2 := hbudget b c a (Ne.symm hbc) hab hca
  have b3 := hbudget c a b (Ne.symm hca) hbc hab
  linarith

end Witness

/-- **A frustrated triangle spoils local payment**: a pattern with a triangle of holonomy `+1`
carries a nonnegative form that is not locally payable. -/
theorem exists_nonneg_not_locallyPayable_of_holonomy_pos (σ : SignPattern ι) {a b c : ι}
    (hab : a ≠ b) (hbc : b ≠ c) (hca : c ≠ a) (hhol : triangleHolonomy σ.sign a b c = 1) :
    ∃ W : ι → ι → ℝ, IsSymmetricCoupling W ∧ Realizes σ W ∧ (∀ f, 0 ≤ incidenceEnergy W f) ∧
      ¬ LocallyPayable W :=
  ⟨frustrationWitness σ a b c, frustrationWitness_isSymmetric σ,
    frustrationWitness_realizes σ hab hbc hca hhol, frustrationWitness_nonneg σ,
    frustrationWitness_not_locallyPayable σ hab hbc hca⟩

omit [Fintype ι] [DecidableEq ι] in
/-- A triangle of a sign pattern has holonomy `±1`. -/
theorem triangleHolonomy_sign_eq (σ : SignPattern ι) {i j k : ι} (hij : i ≠ j) (hjk : j ≠ k)
    (hki : k ≠ i) : triangleHolonomy σ.sign i j k = 1 ∨ triangleHolonomy σ.sign i j k = -1 := by
  have h : triangleHolonomy σ.sign i j k ^ 2 = 1 := by
    unfold triangleHolonomy
    rw [mul_pow, mul_pow, σ.sign_sq i j hij, σ.sign_sq j k hjk, σ.sign_sq k i hki]
    norm_num
  have h2 : (triangleHolonomy σ.sign i j k - 1) * (triangleHolonomy σ.sign i j k + 1) = 0 := by
    nlinarith [h]
  rcases mul_eq_zero.mp h2 with h3 | h3
  · left; linarith
  · right; linarith

/-- **Signed local–global principle on complete overlap patterns.**  Every nonnegative form
realizing the sign pattern `σ` is locally payable iff every triangle of `σ` has holonomy `−1`. -/
theorem localPayment_lossless_iff (σ : SignPattern ι) :
    (∀ c : ι → ι → ℝ, IsSymmetricCoupling c → Realizes σ c → (∀ f, 0 ≤ incidenceEnergy c f) →
      LocallyPayable c) ↔
    ∀ i j k, i ≠ j → j ≠ k → k ≠ i → triangleHolonomy σ.sign i j k < 0 := by
  constructor
  · intro h i j k hij hjk hki
    rcases triangleHolonomy_sign_eq σ hij hjk hki with h1 | h1
    · obtain ⟨W, hW, hr, hnn, hnp⟩ :=
        exists_nonneg_not_locallyPayable_of_holonomy_pos σ hij hjk hki h1
      exact absurd (h W hW hr hnn) hnp
    · rw [h1]; norm_num
  · intro hσ c hc hr hnn
    exact (nonneg_iff_locallyPayable_of_holonomy hσ hc hr).mp hnn

end

end GaloisForLFunctions.SignedArithmeticEnergyIncidence
