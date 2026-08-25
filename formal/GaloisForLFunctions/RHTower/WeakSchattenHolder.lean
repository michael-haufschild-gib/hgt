import GaloisForLFunctions.HTGeometry.ApproxNumberMultiplicative
import GaloisForLFunctions.RHTower.WeakSchattenResidue

/-!
# Weak Schatten ideal and Hölder laws

Approximation-number submultiplicativity makes every weak Schatten class a two-sided operator
ideal. Combining the critical decay bounds of two factors gives the Lorentz--Hölder product law

`S_{p,∞} · S_{q,∞} ⊆ S_{pq/(p+q),∞}`.

The index loss from `a_(m+n)(ST) ≤ a_m(S)a_n(T)` costs only a fixed factor two and therefore does
not alter the weak exponent. This is the ideal-product input used by weak-modulation arguments.
-/

namespace RHTower

open ContinuousLinearMap
open GaloisForLFunctions.HTGeometry

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Bounded left multiplication preserves approximation-number decay. -/
theorem approxNumber_comp_le_norm_left (S T : H →L[ℂ] H) (n : ℕ) :
    approxNumber (S ∘L T) n ≤ ‖S‖ * approxNumber T n := by
  calc
    approxNumber (S ∘L T) n = approxNumber (S ∘L T) (0 + n) := by rw [zero_add]
    _ ≤ approxNumber S 0 * approxNumber T n := approxNumber_comp_add_le S T 0 n
    _ ≤ ‖S‖ * approxNumber T n :=
      mul_le_mul_of_nonneg_right (approxNumber_le_norm S 0) (approxNumber_nonneg T n)

/-- Bounded right multiplication preserves approximation-number decay. -/
theorem approxNumber_comp_le_norm_right (S T : H →L[ℂ] H) (n : ℕ) :
    approxNumber (S ∘L T) n ≤ approxNumber S n * ‖T‖ := by
  calc
    approxNumber (S ∘L T) n = approxNumber (S ∘L T) (n + 0) := by rw [add_zero]
    _ ≤ approxNumber S n * approxNumber T 0 := approxNumber_comp_add_le S T n 0
    _ ≤ approxNumber S n * ‖T‖ :=
      mul_le_mul_of_nonneg_left (approxNumber_le_norm T 0) (approxNumber_nonneg S n)

/-- Weak Schatten classes are left ideals. -/
theorem MemWeakSchattenClass.comp_left
    {p : ℝ} (hp : 0 < p) {T : H →L[ℂ] H}
    (hT : MemWeakSchattenClass p T) (S : H →L[ℂ] H) :
    MemWeakSchattenClass p (S ∘L T) := by
  obtain ⟨C, hC, hbound⟩ := hT
  refine ⟨‖S‖ ^ p * C, mul_nonneg (Real.rpow_nonneg (norm_nonneg S) p) hC, fun n ↦ ?_⟩
  have hpoint := approxNumber_comp_le_norm_left S T n
  calc
    approxNumber (S ∘L T) n ^ p ≤ (‖S‖ * approxNumber T n) ^ p :=
      Real.rpow_le_rpow (approxNumber_nonneg _ _) hpoint hp.le
    _ = ‖S‖ ^ p * approxNumber T n ^ p := by
      rw [Real.mul_rpow (norm_nonneg S) (approxNumber_nonneg T n)]
    _ ≤ ‖S‖ ^ p * (C / ((n : ℝ) + 1)) :=
      mul_le_mul_of_nonneg_left (hbound n) (Real.rpow_nonneg (norm_nonneg S) p)
    _ = (‖S‖ ^ p * C) / ((n : ℝ) + 1) := by ring

/-- Weak Schatten classes are right ideals. -/
theorem MemWeakSchattenClass.comp_right
    {p : ℝ} (hp : 0 < p) {S : H →L[ℂ] H}
    (hS : MemWeakSchattenClass p S) (T : H →L[ℂ] H) :
    MemWeakSchattenClass p (S ∘L T) := by
  obtain ⟨C, hC, hbound⟩ := hS
  refine ⟨C * ‖T‖ ^ p, mul_nonneg hC (Real.rpow_nonneg (norm_nonneg T) p), fun n ↦ ?_⟩
  have hpoint := approxNumber_comp_le_norm_right S T n
  calc
    approxNumber (S ∘L T) n ^ p ≤ (approxNumber S n * ‖T‖) ^ p :=
      Real.rpow_le_rpow (approxNumber_nonneg _ _) hpoint hp.le
    _ = approxNumber S n ^ p * ‖T‖ ^ p := by
      rw [Real.mul_rpow (approxNumber_nonneg S n) (norm_nonneg T)]
    _ ≤ (C / ((n : ℝ) + 1)) * ‖T‖ ^ p :=
      mul_le_mul_of_nonneg_right (hbound n) (Real.rpow_nonneg (norm_nonneg T) p)
    _ = (C * ‖T‖ ^ p) / ((n : ℝ) + 1) := by ring

/-- Weak Schatten Hölder law: `S_{p,∞} · S_{q,∞} ⊆ S_{r,∞}` for
`r = pq/(p+q)`. -/
theorem MemWeakSchattenClass.comp
    {p q : ℝ} (hp : 0 < p) (hq : 0 < q)
    {S T : H →L[ℂ] H}
    (hS : MemWeakSchattenClass p S)
    (hT : MemWeakSchattenClass q T) :
    MemWeakSchattenClass (p * q / (p + q)) (S ∘L T) := by
  let r : ℝ := p * q / (p + q)
  have hpq : 0 < p + q := add_pos hp hq
  have hr : 0 < r := by
    dsimp [r]
    positivity
  have hrp : 0 < r / p := div_pos hr hp
  have hrq : 0 < r / q := div_pos hr hq
  have hexp : r / p + r / q = 1 := by
    dsimp [r]
    field_simp
    ring
  obtain ⟨A, hA, hAbound⟩ := hS
  obtain ⟨B, hB, hBbound⟩ := hT
  let C : ℝ := A ^ (r / p) * B ^ (r / q)
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  refine ⟨2 * C, by positivity, fun k ↦ ?_⟩
  let n : ℕ := k / 2
  have hidx : 2 * n ≤ k := by
    dsimp [n]
    omega
  have hkn : (k : ℝ) + 1 ≤ 2 * ((n : ℝ) + 1) := by
    have hnat : k + 1 ≤ 2 * (n + 1) := by
      dsimp [n]
      omega
    exact_mod_cast hnat
  have hnpos : 0 < (n : ℝ) + 1 := by positivity
  have hkpos : 0 < (k : ℝ) + 1 := by positivity
  have hcomp : approxNumber (S ∘L T) (2 * n) ≤
      approxNumber S n * approxNumber T n := by
    simpa [two_mul] using approxNumber_comp_add_le S T n n
  have hanti : approxNumber (S ∘L T) k ≤ approxNumber (S ∘L T) (2 * n) :=
    approxNumber_antitone (S ∘L T) hidx
  have hpowS : approxNumber S n ^ r = (approxNumber S n ^ p) ^ (r / p) := by
    rw [← Real.rpow_mul (approxNumber_nonneg S n)]
    congr 1
    field_simp
  have hpowT : approxNumber T n ^ r = (approxNumber T n ^ q) ^ (r / q) := by
    rw [← Real.rpow_mul (approxNumber_nonneg T n)]
    congr 1
    field_simp
  have hmain : approxNumber (S ∘L T) (2 * n) ^ r ≤ C / ((n : ℝ) + 1) := by
    calc
      approxNumber (S ∘L T) (2 * n) ^ r
          ≤ (approxNumber S n * approxNumber T n) ^ r :=
        Real.rpow_le_rpow (approxNumber_nonneg _ _) hcomp hr.le
      _ = (approxNumber S n ^ p) ^ (r / p) *
          (approxNumber T n ^ q) ^ (r / q) := by
        rw [Real.mul_rpow (approxNumber_nonneg S n) (approxNumber_nonneg T n),
          hpowS, hpowT]
      _ ≤ (A / ((n : ℝ) + 1)) ^ (r / p) *
          (B / ((n : ℝ) + 1)) ^ (r / q) := by
        exact mul_le_mul
          (Real.rpow_le_rpow (Real.rpow_nonneg (approxNumber_nonneg S n) p)
            (hAbound n) hrp.le)
          (Real.rpow_le_rpow (Real.rpow_nonneg (approxNumber_nonneg T n) q)
            (hBbound n) hrq.le)
          (Real.rpow_nonneg (Real.rpow_nonneg (approxNumber_nonneg T n) q) (r / q))
          (Real.rpow_nonneg (div_nonneg hA hnpos.le) (r / p))
      _ = C / ((n : ℝ) + 1) := by
        rw [Real.div_rpow hA hnpos.le, Real.div_rpow hB hnpos.le]
        dsimp [C]
        rw [div_mul_div_comm, ← Real.rpow_add hnpos, hexp, Real.rpow_one]
  calc
    approxNumber (S ∘L T) k ^ (p * q / (p + q)) =
        approxNumber (S ∘L T) k ^ r := by rfl
    _ ≤ approxNumber (S ∘L T) (2 * n) ^ r :=
      Real.rpow_le_rpow (approxNumber_nonneg _ _) hanti hr.le
    _ ≤ C / ((n : ℝ) + 1) := hmain
    _ ≤ (2 * C) / ((k : ℝ) + 1) := by
      rw [div_le_div_iff₀ hnpos hkpos]
      nlinarith

end

end RHTower
