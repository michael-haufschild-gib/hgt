import GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.TheDampedMobiusCriticalEnergy

/-!
# A change of origin costs an exact quadratic constant in the pronic norm

The critical receiver is anchored: its pronic norm `Σ_{n ≤ T} |a(n)|²/(n(n+1))` weights the cells by
their distance from the origin, so translation-invariant data cannot fix the origin, and a reading
that forgets it is blind. This file prices the origin exactly. Shifting a sequence by `k` cells,
`a ↦ a(· + k)`, changes the pronic energy by at most the factor `(k+1)(k+2)/2`
(`pronicEnergy_shift_le`), the factor is attained (`pronicEnergy_shift_indicator`), and in the
other direction the shift loses only the first `k` cells (`pronicEnergy_le_head_add_shift`).

Consequently admission — a horizon-free bound on the pronic energy — is invariant under every
finite change of origin (`bddAbove_pronicEnergy_shift_iff`), in particular for the damped Möbius
receiver (`admits_dampedMobiusEnergy_iff_shift`): finite origin information never changes
critical admission, and it is recovered stably, with the exact constant `(k+1)(k+2)/2`. What can
change admission is an origin that drifts with the horizon, where the constant is unbounded.
-/

open Finset

noncomputable section

namespace GaloisForLFunctions.ArithmeticCompensationTheory

/-- The pronic energy `Σ_{1 ≤ n ≤ T} a(n)²/(n(n+1))` of a real sequence. -/
def pronicEnergy (a : ℕ → ℝ) (T : ℕ) : ℝ := ∑ n ∈ Icc 1 T, a n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1))

theorem pronicEnergy_nonneg (a : ℕ → ℝ) (T : ℕ) : 0 ≤ pronicEnergy a T :=
  sum_nonneg fun n _ => by positivity

theorem pronicEnergy_mono (a : ℕ → ℝ) : Monotone (pronicEnergy a) := fun _ _ h =>
  sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc_right h) fun _ _ _ => by positivity

/-- The pronic weights under a shift: `(j+k)(j+k+1) ≤ ((k+1)(k+2)/2) j(j+1)` for `j ≥ 1`, with
equality at `j = 1`; the difference is `(j−1) k (k(j+2) + 3j + 2)/2`. -/
theorem pronicWeight_shift_le {j : ℕ} (hj : 1 ≤ j) (k : ℕ) :
    ((j : ℝ) + k) * ((j : ℝ) + k + 1) ≤ ((k : ℝ) + 1) * ((k : ℝ) + 2) / 2 * ((j : ℝ) * ((j : ℝ) + 1)) := by
  have hx : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hy : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hkey := mul_nonneg (mul_nonneg (sub_nonneg.mpr hx) hy)
    (by positivity : (0 : ℝ) ≤ (k : ℝ) * ((j : ℝ) + 2) + 3 * j + 2)
  nlinarith [hkey]

/-- Shifting the origin by `k` cells multiplies the pronic energy by at most `(k+1)(k+2)/2`. -/
theorem pronicEnergy_shift_le (a : ℕ → ℝ) (k T : ℕ) :
    pronicEnergy (fun n => a (n + k)) T ≤
      ((k : ℝ) + 1) * ((k : ℝ) + 2) / 2 * pronicEnergy a (T + k) := by
  set c : ℝ := ((k : ℝ) + 1) * ((k : ℝ) + 2) / 2
  have hc : 0 ≤ c := by positivity
  have hterm : ∀ n ∈ Icc 1 T, a (n + k) ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) ≤
      c * (a (n + k) ^ 2 / (((n + k : ℕ) : ℝ) * (((n + k : ℕ) : ℝ) + 1))) := by
    intro n hn
    have hn1 : 1 ≤ n := (mem_Icc.mp hn).1
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
    have hw : ((n : ℝ) + k) * ((n : ℝ) + k + 1) ≤ c * ((n : ℝ) * ((n : ℝ) + 1)) :=
      pronicWeight_shift_le hn1 k
    push_cast
    rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
    have ha := sq_nonneg (a (n + k))
    nlinarith [mul_le_mul_of_nonneg_left hw ha]
  have himage : ∑ n ∈ Icc 1 T, a (n + k) ^ 2 / (((n + k : ℕ) : ℝ) * (((n + k : ℕ) : ℝ) + 1)) ≤
      pronicEnergy a (T + k) := by
    rw [pronicEnergy, ← sum_image (g := fun n => n + k) (f := fun m => a m ^ 2 / ((m : ℝ) *
      ((m : ℝ) + 1))) (fun x _ y _ h => by simpa using h)]
    refine sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => by positivity
    intro m hm
    obtain ⟨n, hn, rfl⟩ := mem_image.mp hm
    obtain ⟨h1, h2⟩ := mem_Icc.mp hn
    exact mem_Icc.mpr ⟨by omega, by omega⟩
  calc pronicEnergy (fun n => a (n + k)) T
      ≤ ∑ n ∈ Icc 1 T, c * (a (n + k) ^ 2 / (((n + k : ℕ) : ℝ) * (((n + k : ℕ) : ℝ) + 1))) :=
        sum_le_sum hterm
    _ = c * ∑ n ∈ Icc 1 T, a (n + k) ^ 2 / (((n + k : ℕ) : ℝ) * (((n + k : ℕ) : ℝ) + 1)) := by
        rw [mul_sum]
    _ ≤ c * pronicEnergy a (T + k) := mul_le_mul_of_nonneg_left himage hc

/-- The constant `(k+1)(k+2)/2` is attained: the indicator of the cell `k + 1`. -/
theorem pronicEnergy_shift_indicator (k T : ℕ) (hT : 1 ≤ T) :
    pronicEnergy (fun n => if n + k = k + 1 then (1 : ℝ) else 0) T =
      ((k : ℝ) + 1) * ((k : ℝ) + 2) / 2 *
        pronicEnergy (fun n => if n = k + 1 then (1 : ℝ) else 0) (T + k) := by
  have h1 : pronicEnergy (fun n => if n + k = k + 1 then (1 : ℝ) else 0) T = 1 / 2 := by
    rw [pronicEnergy, sum_eq_single 1]
    · rw [if_pos (by omega)]; norm_num
    · intro n _ hn; rw [if_neg (by omega)]; ring
    · intro h; exact absurd (mem_Icc.mpr ⟨le_rfl, hT⟩) h
  have h2 : pronicEnergy (fun n => if n = k + 1 then (1 : ℝ) else 0) (T + k) =
      1 / (((k : ℝ) + 1) * ((k : ℝ) + 2)) := by
    rw [pronicEnergy, sum_eq_single (k + 1)]
    · push_cast; rw [if_pos rfl]; ring
    · intro n _ hn; rw [if_neg hn]; ring
    · intro h; exact absurd (mem_Icc.mpr ⟨by omega, by omega⟩) h
  rw [h1, h2]
  field_simp

/-- In the other direction a shift loses only the first `k` cells. -/
theorem pronicEnergy_le_head_add_shift (a : ℕ → ℝ) (k T : ℕ) :
    pronicEnergy a (T + k) ≤ pronicEnergy a k + pronicEnergy (fun n => a (n + k)) T := by
  have hsplit : Icc 1 (T + k) = Icc 1 k ∪ (Icc 1 T).image (fun n => n + k) := by
    ext m
    simp only [mem_union, mem_Icc, mem_image]
    constructor
    · intro hm
      by_cases hmk : m ≤ k
      · exact Or.inl ⟨hm.1, hmk⟩
      · exact Or.inr ⟨m - k, ⟨by omega, by omega⟩, by omega⟩
    · rintro (hm | ⟨n, hn, rfl⟩) <;> omega
  have hdisj : Disjoint (Icc 1 k) ((Icc 1 T).image (fun n => n + k)) := by
    rw [disjoint_left]
    intro m hm hm'
    obtain ⟨n, hn, rfl⟩ := mem_image.mp hm'
    have := (mem_Icc.mp hm).2
    have := (mem_Icc.mp hn).1
    omega
  rw [pronicEnergy, hsplit, sum_union hdisj, sum_image (fun x _ y _ h => by simpa using h)]
  refine add_le_add le_rfl (sum_le_sum fun n hn => ?_)
  have hn1 : 1 ≤ n := (mem_Icc.mp hn).1
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  push_cast
  refine div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) ?_
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  nlinarith

/-- **Admission is invariant under every finite change of origin.** -/
theorem bddAbove_pronicEnergy_shift_iff (a : ℕ → ℝ) (k : ℕ) :
    (∃ B, ∀ T, pronicEnergy (fun n => a (n + k)) T ≤ B) ↔ ∃ B, ∀ T, pronicEnergy a T ≤ B := by
  constructor
  · rintro ⟨B, hB⟩
    refine ⟨pronicEnergy a k + B, fun T => ?_⟩
    calc pronicEnergy a T ≤ pronicEnergy a (T + k) := pronicEnergy_mono a (by omega)
      _ ≤ pronicEnergy a k + pronicEnergy (fun n => a (n + k)) T :=
          pronicEnergy_le_head_add_shift a k T
      _ ≤ pronicEnergy a k + B := by linarith [hB T]
  · rintro ⟨B, hB⟩
    refine ⟨((k : ℝ) + 1) * ((k : ℝ) + 2) / 2 * B, fun T => ?_⟩
    exact (pronicEnergy_shift_le a k T).trans
      (mul_le_mul_of_nonneg_left (hB (T + k)) (by positivity))

/-- The damped Möbius energy is the pronic energy of the centred receiver. -/
theorem dampedMobiusEnergy_eq_pronicEnergy (ε : ℝ) (T : ℕ) :
    ArithmeticContinuationAndCriticalEnergy.dampedMobiusEnergy ε T =
      pronicEnergy (RHTower.pmPowerDampedCenteredDivisorPrefix ε) T := rfl

/-- **The receiver's admission does not see a finite change of origin.** For every damping and
every shift `k`, the damped Möbius receiver is admitted iff its translate by `k` cells has bounded
pronic energy. -/
theorem admits_dampedMobiusEnergy_iff_shift (ε : ℝ) (k : ℕ) :
    ArithmeticContinuationAndCriticalEnergy.Admits
        ArithmeticContinuationAndCriticalEnergy.dampedMobiusEnergy ε ↔
      ∃ B, ∀ T, pronicEnergy (fun n => RHTower.pmPowerDampedCenteredDivisorPrefix ε (n + k)) T ≤ B :=
  (bddAbove_pronicEnergy_shift_iff _ k).symm

end GaloisForLFunctions.ArithmeticCompensationTheory
