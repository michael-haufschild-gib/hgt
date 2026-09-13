import GaloisForLFunctions.HTGeometry.BanaszczykSignRecovery

/-!
# Exact one-dimensional open Banaszczyk transforms

The scalar model makes the fibre rule completely explicit.  A direction shorter than the radius
survives and increases the radius by its length; a direction at least as long as the radius deletes
the open interval.
-/

open Set
open scoped Pointwise

namespace GaloisForLFunctions.HTGeometry

theorem openBanaszczykTransform_Ioo_of_pos {r a : ℝ} (ha : 0 < a) (har : a < r) :
    openBanaszczykTransform (Ioo (-r) r) a = Ioo (-(r + a)) (r + a) := by
  have hrpa : 0 < r + a := by linarith
  have hrma : 0 < r - a := by linarith
  ext x
  constructor
  · intro hx
    rcases mem_openBanaszczykTransform.mp hx with ⟨z, hzplus, hzminus, t, ht, hzt⟩
    simp only [mem_Ioo] at hzplus hzminus ⊢
    simp only [smul_eq_mul] at hzt
    have htl := mul_lt_mul_of_pos_right ht.1 ha
    have htu := mul_lt_mul_of_pos_right ht.2 ha
    constructor <;> nlinarith
  · intro hx
    simp only [mem_Ioo] at hx
    let z := (r - a) * x / (r + a)
    let t := 2 * x / (r + a)
    have hzl : -r + a < z := by
      apply (lt_div_iff₀ hrpa).2
      have h := mul_lt_mul_of_pos_left hx.1 hrma
      nlinarith
    have hzu : z < r - a := by
      apply (div_lt_iff₀ hrpa).2
      have h := mul_lt_mul_of_pos_left hx.2 hrma
      nlinarith
    have htl : -2 < t := by
      apply (lt_div_iff₀ hrpa).2
      nlinarith
    have htu : t < 2 := by
      apply (div_lt_iff₀ hrpa).2
      nlinarith
    refine mem_openBanaszczykTransform.mpr ⟨z, ?_, ?_, t, ⟨htl, htu⟩, ?_⟩
    · exact ⟨by linarith, by linarith⟩
    · exact ⟨by linarith, by linarith⟩
    · dsimp [z, t]
      rw [div_mul_eq_mul_div, ← add_div]
      apply (div_eq_iff (ne_of_gt hrpa)).2
      ring_nf

theorem openBanaszczykTransform_Ioo_of_too_large {r a : ℝ} (har : r ≤ a) :
    openBanaszczykTransform (Ioo (-r) r) a = ∅ := by
  ext x
  constructor
  · intro hx
    rcases mem_openBanaszczykTransform.mp hx with ⟨z, hzplus, hzminus, _t, _ht, _hzt⟩
    simp only [mem_Ioo] at hzplus hzminus
    exfalso
    linarith
  · simp

theorem openBanaszczykTransform_Ioo_of_abs_lt {r a : ℝ} (har : |a| < r) :
    openBanaszczykTransform (Ioo (-r) r) a = Ioo (-(r + |a|)) (r + |a|) := by
  rcases lt_trichotomy a 0 with ha | ha | ha
  · have hna : 0 < -a := by linarith
    have hnar : -a < r := by simpa [abs_of_neg ha] using har
    calc
      openBanaszczykTransform (Ioo (-r) r) a =
          openBanaszczykTransform (Ioo (-r) r) (-a) :=
        (openBanaszczykTransform_neg (Ioo (-r) r) a).symm
      _ = Ioo (-(r + -a)) (r + -a) :=
        openBanaszczykTransform_Ioo_of_pos hna hnar
      _ = Ioo (-(r + |a|)) (r + |a|) := by rw [abs_of_neg ha]
  · subst a
    simp
  · have har' : a < r := by simpa [abs_of_pos ha] using har
    simpa [abs_of_pos ha] using openBanaszczykTransform_Ioo_of_pos ha har'

theorem openBanaszczykTransform_Ioo_of_abs_ge {r a : ℝ} (har : r ≤ |a|) :
    openBanaszczykTransform (Ioo (-r) r) a = ∅ := by
  by_cases ha : 0 ≤ a
  · exact openBanaszczykTransform_Ioo_of_too_large
      (by simpa [abs_of_nonneg ha] using har)
  · have ha' : a < 0 := lt_of_not_ge ha
    calc
      openBanaszczykTransform (Ioo (-r) r) a =
          openBanaszczykTransform (Ioo (-r) r) (-a) :=
        (openBanaszczykTransform_neg (Ioo (-r) r) a).symm
      _ = ∅ := openBanaszczykTransform_Ioo_of_too_large
        (by simpa [abs_of_neg ha'] using har)

/-- Unconditional exact classification of every centered scalar interval transform. -/
theorem openBanaszczykTransform_Ioo (r a : ℝ) :
    openBanaszczykTransform (Ioo (-r) r) a =
      if |a| < r then Ioo (-(r + |a|)) (r + |a|) else ∅ := by
  split_ifs with har
  · exact openBanaszczykTransform_Ioo_of_abs_lt har
  · exact openBanaszczykTransform_Ioo_of_abs_ge (le_of_not_gt har)

theorem openBanaszczykTransform_halfInterval :
    openBanaszczykTransform (Ioo (-1 : ℝ) 1) (1 / 2) = Ioo (-3 / 2) (3 / 2) := by
  convert openBanaszczykTransform_Ioo_of_pos
    (r := (1 : ℝ)) (a := (1 / 2 : ℝ)) (by linarith) (by linarith) using 1
  · ring_nf

theorem openBanaszczykTransform_unitInterval_two :
    openBanaszczykTransform (Ioo (-1 : ℝ) 1) 2 = ∅ := by
  exact openBanaszczykTransform_Ioo_of_too_large (by linarith)

/-- Every surviving repetition of one scalar direction grows the interval by its absolute value. -/
theorem iteratedOpenBanaszczykTransform_Ioo_replicate_of_abs_lt {r a : ℝ}
    (har : |a| < r) (n : ℕ) :
    iteratedOpenBanaszczykTransform (Ioo (-r) r) (List.replicate n a) =
      Ioo (-(r + n * |a|)) (r + n * |a|) := by
  induction n generalizing r with
  | zero => simp
  | succ n ih =>
      rw [List.replicate_succ, iteratedOpenBanaszczykTransform_cons,
        openBanaszczykTransform_Ioo_of_abs_lt har]
      have hnext : |a| < r + |a| := by
        have habs : 0 ≤ |a| := abs_nonneg a
        linarith
      rw [ih hnext]
      have hradius : (r + |a|) + (n : ℝ) * |a| =
          r + (Nat.succ n : ℝ) * |a| := by
        push_cast
        ring_nf
      rw [hradius]

theorem iteratedOpenBanaszczykTransform_halfInterval (n : ℕ) :
    iteratedOpenBanaszczykTransform (Ioo (-1 : ℝ) 1)
        (List.replicate n (1 / 2)) =
      Ioo (-(1 + (n : ℝ) / 2)) (1 + (n : ℝ) / 2) := by
  have hhalf : (0 : ℝ) < 1 / 2 := by linarith
  have h := iteratedOpenBanaszczykTransform_Ioo_replicate_of_abs_lt
      (r := (1 : ℝ)) (a := (1 / 2 : ℝ))
      (by rw [abs_of_pos hhalf]; linarith) n
  rw [abs_of_pos hhalf] at h
  simpa only [div_eq_mul_inv, one_mul] using h

/-- Closed nonzero-vector application of geometric sign recovery for every finite length. -/
theorem exists_half_signedSum_mem_unitInterval (n : ℕ) :
    ∃ x ∈ Ioo (-1 : ℝ) 1, IsSignedSum (List.replicate n (1 / 2)) x := by
  have hneg : -(Ioo (-1 : ℝ) 1) = Ioo (-1) 1 := by
    ext x
    rw [Set.mem_neg]
    simp only [mem_Ioo]
    constructor <;> rintro ⟨hl, hu⟩ <;> constructor <;> linarith
  apply exists_isSignedSum_mem_of_iterated_nonempty (convex_Ioo (-1) 1) hneg
  rw [iteratedOpenBanaszczykTransform_halfInterval]
  refine ⟨0, ?_⟩
  simp only [mem_Ioo]
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  constructor <;> linarith

/-- The same closed application with the signs exposed as an ordinary Boolean list. -/
theorem exists_half_signs_mem_unitInterval (n : ℕ) :
    ∃ signs : List Bool, signs.length = n ∧
      signedListSum (List.replicate n (1 / 2 : ℝ)) signs ∈ Ioo (-1) 1 := by
  obtain ⟨x, hx, hsigned⟩ := exists_half_signedSum_mem_unitInterval n
  obtain ⟨signs, hlength, hsum⟩ := hsigned.exists_signs
  refine ⟨signs, ?_, hsum ▸ hx⟩
  simpa using hlength

end GaloisForLFunctions.HTGeometry
