import GaloisForLFunctions.HodgeTheoryWithoutVarieties.TheNerveOfTheStarCover
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheShellsRepayEveryConductor

/-!
# The Mertens function is a gluing determinant

On the vertices `1, …, N` the divisibility form `Z(i, j) = [i ∣ j]` is unipotent: it is triangular
with unit diagonal, its determinant is `1`, and its inverse is the Möbius form
`Z⁻¹(i, j) = μ(j/i)[i ∣ j]` (`divisibilityMatrix_mul_moebiusMatrix`). It carries no global
arithmetic. Glue every vertex to the pole vertex `1` — replace the column of the pole by the
all-ones column, the rank-one gluing `Z + (𝟙 − e₁) e₁ᵀ` — and the determinant becomes the Mertens
function:

`det R_N = Σ_{n ≤ N} μ(n) = M(N)`   (`det_redhefferMatrix`),

where `R_N(i, j) = [i ∣ j ∨ j = 1]` is Redheffer's matrix. The mechanism is Cramer's rule: the
determinant of the glued matrix is the pole coordinate of `Z⁻¹𝟙`, the row sum of the Möbius form at
the pole. Hence (`riemannHypothesis_iff_det_redhefferMatrix`) RH is the half-power growth of the
gluing determinant, and unconditionally it is `Ω±(√N)` (`det_redhefferMatrix_omega_pm_sqrt`).

ADT reading: the local divisibility structure is unipotent, and the whole arithmetic of `μ` is
created by one rank-one gluing at the pole, as the archimedean place glues the scaling data through
one hyperplane. The determinant of the gluing is the Euler characteristic of the nerve of the star
cover (`det_redhefferMatrix_eq_nerveEulerChar`).
-/

noncomputable section

open Finset ArithmeticFunction Matrix
open scoped ArithmeticFunction.Moebius

namespace GaloisForLFunctions.ArithmeticDegenerationTheory

/-- The vertices `1, …, N`. -/
abbrev Vertex (N : ℕ) := {a : ℕ // a ∈ Icc 1 N}

/-- The divisibility form `Z(i, j) = [i ∣ j]`. -/
def divisibilityMatrix (N : ℕ) : Matrix (Vertex N) (Vertex N) ℝ :=
  fun i j => if i.1 ∣ j.1 then 1 else 0

/-- The Möbius form `μ(j/i)[i ∣ j]`. -/
def moebiusMatrix (N : ℕ) : Matrix (Vertex N) (Vertex N) ℝ :=
  fun i j => if i.1 ∣ j.1 then (μ (j.1 / i.1) : ℝ) else 0

/-- Redheffer's matrix `R(i, j) = [i ∣ j ∨ j = 1]`: the divisibility form glued to the pole. -/
def redhefferMatrix (N : ℕ) : Matrix (Vertex N) (Vertex N) ℝ :=
  fun i j => if i.1 ∣ j.1 ∨ j.1 = 1 then 1 else 0

/-- The pole vertex. -/
def poleVertex (N : ℕ) (hN : 1 ≤ N) : Vertex N := ⟨1, mem_Icc.mpr ⟨le_rfl, hN⟩⟩

/-- Divisors `j` of `k` that are multiples of `i` are `i` times the divisors of `k/i`. -/
theorem sum_divisors_filter_dvd {i k : ℕ} (hi : 0 < i) (hk : 0 < k) (hik : i ∣ k) (F : ℕ → ℝ) :
    ∑ j ∈ k.divisors.filter (i ∣ ·), F j = ∑ t ∈ (k / i).divisors, F (i * t) := by
  have hk' : k / i ≠ 0 := (Nat.div_pos (Nat.le_of_dvd hk hik) hi).ne'
  refine sum_nbij' (fun j => j / i) (fun t => i * t) ?_ ?_ ?_ ?_ ?_
  · intro j hj
    simp only [mem_filter, Nat.mem_divisors] at hj
    simp only [Nat.mem_divisors]
    exact ⟨Nat.div_dvd_div hj.2 hj.1.1, hk'⟩
  · intro t ht
    simp only [mem_coe, Nat.mem_divisors] at ht
    simp only [mem_coe, mem_filter, Nat.mem_divisors]
    refine ⟨⟨?_, hk.ne'⟩, dvd_mul_right i t⟩
    rw [← Nat.mul_div_cancel' hik]
    exact Nat.mul_dvd_mul_left i ht.1
  · intro j hj
    simp only [mem_coe, mem_filter] at hj
    exact Nat.mul_div_cancel' hj.2
  · intro t _
    exact Nat.mul_div_cancel_left t hi
  · intro j hj
    simp only [mem_filter] at hj
    rw [Nat.mul_div_cancel' hj.2]

/-- **The Möbius form inverts the divisibility form.** -/
theorem divisibilityMatrix_mul_moebiusMatrix (N : ℕ) :
    divisibilityMatrix N * moebiusMatrix N = 1 := by
  ext i k
  rw [Matrix.mul_apply, Matrix.one_apply]
  have hi : 0 < i.1 := (mem_Icc.mp i.2).1
  have hk : 0 < k.1 := (mem_Icc.mp k.2).1
  have hkN : k.1 ≤ N := (mem_Icc.mp k.2).2
  simp only [divisibilityMatrix, moebiusMatrix]
  -- move to a sum over `Icc 1 N`
  have hsub : ∑ j : Vertex N, (if i.1 ∣ j.1 then (1 : ℝ) else 0) *
      (if j.1 ∣ k.1 then (μ (k.1 / j.1) : ℝ) else 0) =
        ∑ j ∈ Icc 1 N, (if i.1 ∣ j then (1 : ℝ) else 0) *
          (if j ∣ k.1 then (μ (k.1 / j) : ℝ) else 0) :=
    (Finset.sum_subtype (Icc 1 N) (fun _ => Iff.rfl) (fun j => (if i.1 ∣ j then (1 : ℝ) else 0) *
      (if j ∣ k.1 then (μ (k.1 / j) : ℝ) else 0))).symm
  rw [hsub]
  have hterm : ∀ j ∈ Icc 1 N, (if i.1 ∣ j then (1 : ℝ) else 0) *
      (if j ∣ k.1 then (μ (k.1 / j) : ℝ) else 0) =
        if j ∈ k.1.divisors.filter (i.1 ∣ ·) then (μ (k.1 / j) : ℝ) else 0 := by
    intro j hj
    simp only [mem_filter, Nat.mem_divisors]
    by_cases h1 : i.1 ∣ j <;> by_cases h2 : j ∣ k.1 <;> simp [h1, h2, hk.ne']
  rw [sum_congr rfl hterm, ← sum_filter]
  have hset : (Icc 1 N).filter (fun j => j ∈ k.1.divisors.filter (i.1 ∣ ·)) =
      k.1.divisors.filter (i.1 ∣ ·) := by
    ext j
    simp only [mem_filter, mem_Icc, Nat.mem_divisors]
    constructor
    · rintro ⟨-, h⟩; exact h
    · rintro ⟨⟨hjk, hk0⟩, hij⟩
      exact ⟨⟨Nat.pos_of_dvd_of_pos hjk hk, (Nat.le_of_dvd hk hjk).trans hkN⟩, ⟨hjk, hk0⟩, hij⟩
  rw [hset]
  by_cases hik : i.1 ∣ k.1
  · rw [sum_divisors_filter_dvd hi hk hik]
    have hmu : ∀ t ∈ (k.1 / i.1).divisors, (μ (k.1 / (i.1 * t)) : ℝ) = (μ (k.1 / i.1 / t) : ℝ) :=
      fun t _ => by rw [Nat.div_div_eq_div_mul]
    rw [sum_congr rfl hmu]
    have hs := RenormalizedArithmeticPotentialTheory.CompletedShell.sum_divisors_moebius_div (k.1 / i.1)
    have hcast : ∑ t ∈ (k.1 / i.1).divisors, (μ (k.1 / i.1 / t) : ℝ) =
        ∑ t ∈ (k.1 / i.1).divisors, ((μ (k.1 / i.1 / t) : ℤ) : ℝ) := rfl
    rw [hcast, hs]
    have hiff : k.1 / i.1 = 1 ↔ i = k := by
      constructor
      · intro h
        apply Subtype.ext
        have := Nat.div_mul_cancel hik
        rw [h, one_mul] at this
        exact this
      · rintro rfl
        exact Nat.div_self hi
    by_cases hki : i = k
    · rw [if_pos (hiff.mpr hki), if_pos hki]
    · rw [if_neg (fun h => hki (hiff.mp h)), if_neg hki]
  · have hempty : k.1.divisors.filter (i.1 ∣ ·) = ∅ := by
      ext j
      simp only [mem_filter, Nat.mem_divisors, Finset.notMem_empty, iff_false, not_and]
      intro hjk hij
      exact hik (hij.trans hjk.1)
    rw [hempty, sum_empty]
    split_ifs with hik'
    · subst hik'
      exact absurd dvd_rfl hik
    · rfl

theorem moebiusMatrix_mul_divisibilityMatrix (N : ℕ) :
    moebiusMatrix N * divisibilityMatrix N = 1 :=
  mul_eq_one_comm.mp (divisibilityMatrix_mul_moebiusMatrix N)

/-- The divisibility form is unipotent: its determinant is `1`. -/
theorem det_divisibilityMatrix (N : ℕ) : (divisibilityMatrix N).det = 1 := by
  have hmul := congrArg Matrix.det (divisibilityMatrix_mul_moebiusMatrix N)
  rw [det_mul, det_one] at hmul
  -- the divisibility form is upper triangular with unit diagonal
  have htri : (divisibilityMatrix N).BlockTriangular id := by
    intro a b hab
    simp only [divisibilityMatrix]
    apply if_neg
    intro hdiv
    have hb : 0 < b.1 := (mem_Icc.mp b.2).1
    exact (Nat.not_le_of_gt hab) (Nat.le_of_dvd hb hdiv)
  rw [det_of_upperTriangular htri]
  simp [divisibilityMatrix]

/-- **Redheffer's matrix is the divisibility form with the pole column replaced by `𝟙`.** -/
theorem redhefferMatrix_eq_updateCol (N : ℕ) (hN : 1 ≤ N) :
    redhefferMatrix N = (divisibilityMatrix N).updateCol (poleVertex N hN) (fun _ => 1) := by
  ext i j
  simp only [redhefferMatrix, divisibilityMatrix, updateCol_apply]
  by_cases hj : j = poleVertex N hN
  · subst hj
    simp [poleVertex]
  · rw [if_neg hj]
    have hj1 : j.1 ≠ 1 := fun h => hj (Subtype.ext h)
    simp [hj1]

/-- **The Mertens function is the gluing determinant at the pole.**
`det R_N = Σ_{n ≤ N} μ(n)`. -/
theorem det_redhefferMatrix (N : ℕ) (hN : 1 ≤ N) :
    (redhefferMatrix N).det = ∑ n ∈ Icc 1 N, (μ n : ℝ) := by
  set Z := divisibilityMatrix N
  set M := moebiusMatrix N
  set o := poleVertex N hN
  rw [redhefferMatrix_eq_updateCol N hN, ← cramer_apply]
  -- `cramer Z 𝟙 = Z⁻¹ 𝟙 = M 𝟙`
  have hc : cramer Z (fun _ => 1) = M *ᵥ (fun _ => 1) := by
    have h1 : Z *ᵥ cramer Z (fun _ => 1) = fun _ => 1 := by
      rw [mulVec_cramer, det_divisibilityMatrix, one_smul]
    calc cramer Z (fun _ => 1) = (M * Z) *ᵥ cramer Z (fun _ => 1) := by
          rw [moebiusMatrix_mul_divisibilityMatrix, one_mulVec]
      _ = M *ᵥ (fun _ => 1) := by rw [← mulVec_mulVec, h1]
  rw [hc]
  simp only [mulVec, dotProduct, mul_one, M, moebiusMatrix, poleVertex, one_dvd, if_true,
    Nat.div_one]
  exact (Finset.sum_subtype (Icc 1 N) (fun _ => Iff.rfl) (fun n => (μ n : ℝ))).symm

/-- The gluing determinant is the Euler characteristic of the nerve of the star cover. -/
theorem det_redhefferMatrix_eq_nerveEulerChar (N : ℕ) (hN : 1 ≤ N) :
    (redhefferMatrix N).det = (HodgeTheoryWithoutVarieties.nerveEulerChar N : ℝ) := by
  rw [det_redhefferMatrix N hN, HodgeTheoryWithoutVarieties.nerveEulerChar_eq_mertens]
  push_cast
  rfl

/-- **RH is the half-power growth of the gluing determinant.** -/
theorem riemannHypothesis_iff_det_redhefferMatrix :
    RiemannHypothesis ↔ ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 1 ≤ N →
      |(redhefferMatrix N).det| ≤ C * ((N : ℝ) + 1) ^ ((1 / 2 : ℝ) + δ) := by
  rw [HodgeTheoryWithoutVarieties.riemannHypothesis_iff_nerveEulerChar]
  refine forall₂_congr fun δ _ => exists_congr fun C => and_congr_right fun hC => ?_
  constructor
  · intro h N hN
    rw [det_redhefferMatrix_eq_nerveEulerChar N hN]
    exact h N
  · intro h N
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · have : HodgeTheoryWithoutVarieties.nerveEulerChar 0 = 0 := by
        rw [HodgeTheoryWithoutVarieties.nerveEulerChar_eq_mertens]; simp
      rw [this]
      simp only [Int.cast_zero, abs_zero]
      positivity
    · rw [← det_redhefferMatrix_eq_nerveEulerChar N hN]
      exact h N hN

/-- **The gluing determinant oscillates at the square-root scale**: it exceeds `c√N` and falls
below `−c√N` for arbitrarily large `N`. The rescaled determinant `det R_N/√N` has no limit. -/
theorem det_redhefferMatrix_omega_pm_sqrt :
    ∃ c : ℝ, 0 < c ∧ (∀ N₀ : ℕ, ∃ N ≥ N₀, ∃ hN : 1 ≤ N, c * Real.sqrt N < (redhefferMatrix N).det) ∧
      ∀ N₀ : ℕ, ∃ N ≥ N₀, ∃ hN : 1 ≤ N, (redhefferMatrix N).det < -(c * Real.sqrt N) := by
  obtain ⟨c, hc, hplus, hminus⟩ := HodgeTheoryWithoutVarieties.nerveEulerChar_omega_pm_sqrt
  refine ⟨c, hc, fun N₀ => ?_, fun N₀ => ?_⟩
  · obtain ⟨N, hN, h⟩ := hplus (max N₀ 1)
    have h1 : 1 ≤ N := le_trans (le_max_right _ _) hN
    exact ⟨N, le_trans (le_max_left _ _) hN, h1, by
      rw [det_redhefferMatrix_eq_nerveEulerChar N h1]; exact_mod_cast h⟩
  · obtain ⟨N, hN, h⟩ := hminus (max N₀ 1)
    have h1 : 1 ≤ N := le_trans (le_max_right _ _) hN
    exact ⟨N, le_trans (le_max_left _ _) hN, h1, by
      rw [det_redhefferMatrix_eq_nerveEulerChar N h1]; exact_mod_cast h⟩

end GaloisForLFunctions.ArithmeticDegenerationTheory
