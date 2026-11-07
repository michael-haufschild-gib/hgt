import GaloisForLFunctions.HTGeometry.DirichletSimultaneousApproximation
import GaloisForLFunctions.PrimeTorusTheory.TheOrbitOfAPhaseSystem

/-!
# The first return

A finite family of steps `ℓ_i` (for the integers `ℓ_p = log p`) is *returned* at the height `t` to precision `η` when every
phase is close to `1`: `1 − cos(t ℓ_i) ≤ η`. The **first return** `R(s, ℓ, η)` is the least height `t ≥ 1` of a return.

* **Existence** (`firstReturn_le_pow`). By simultaneous Dirichlet approximation, a return occurs at an integer height
  `t ≤ Q^{|s|}` as soon as `2π² ≤ η Q²`. So `log R ≤ |s| log Q`: for the primes up to `y` this is `exp(C_η y/log y)`.
* **The return set is closed and the infimum is attained** (`firstReturn_mem`).
* **Group laws.** `√(1 − cos)` is subadditive (the chord), so returns add with precisions adding in the square root
  (`IsReturn.add`), and `n t` is a return at precision `n² η` (`IsReturn.nat_mul`).
* **Corners** (`IsAntiReturn.two_mul`). `1 − cos 2x ≤ 4(1 + cos x)`: a visit of the corner `−1` (the Liouville corner) at
  `t` is a return at `2t`. So the first visit of `−1` is at least half the first return at precision `4η`
  (`firstReturn_le_two_mul_of_antiReturn`).
* **Rank one** (`firstReturn_le_of_rankOne`). If every step is an integer multiple of `ℓ₀ > 0`, the first return is at most
  `2π⌈ℓ₀/2π⌉/ℓ₀` for every set and every precision: periodic flows have no first-return problem.
-/

open Real Finset

namespace GaloisForLFunctions.TailArithmeticOfThePrimeOrbit

noncomputable section

variable {ι : Type*}

/-- `t` returns the steps `ℓ_i`, `i ∈ s`, to precision `η`: every phase `e^{−itℓ_i}` is within `η` of `1` in
`1 − cos`. -/
def IsReturn (s : Finset ι) (ℓ : ι → ℝ) (η t : ℝ) : Prop := ∀ i ∈ s, 1 - cos (t * ℓ i) ≤ η

/-- `t` sends every phase near the corner `−1`. -/
def IsAntiReturn (s : Finset ι) (ℓ : ι → ℝ) (η t : ℝ) : Prop := ∀ i ∈ s, 1 + cos (t * ℓ i) ≤ η

/-- The heights `t ≥ 1` of returns. -/
def returnSet (s : Finset ι) (ℓ : ι → ℝ) (η : ℝ) : Set ℝ := {t | 1 ≤ t ∧ IsReturn s ℓ η t}

/-- The first return: the least height `t ≥ 1` of a return. -/
def firstReturn (s : Finset ι) (ℓ : ι → ℝ) (η : ℝ) : ℝ := sInf (returnSet s ℓ η)

/-- The steps of the integers: `ℓ_n = log n`. -/
def logStep (n : ℕ) : ℝ := Real.log n

variable {s : Finset ι} {ℓ : ι → ℝ} {η η' t u : ℝ}

theorem isClosed_returnSet (s : Finset ι) (ℓ : ι → ℝ) (η : ℝ) : IsClosed (returnSet s ℓ η) := by
  have h : returnSet s ℓ η = Set.Ici 1 ∩ ⋂ i ∈ s, {t : ℝ | 1 - cos (t * ℓ i) ≤ η} := by
    ext t
    simp [returnSet, IsReturn]
  rw [h]
  refine isClosed_Ici.inter (isClosed_biInter fun i _ => ?_)
  exact isClosed_le (continuous_const.sub (continuous_cos.comp (continuous_id.mul continuous_const)))
    continuous_const

/-! ## Existence: the Dirichlet bound -/

/-- `1 − cos(2πx) ≤ 2π²x²`. -/
theorem one_sub_cos_two_pi_mul_le (x : ℝ) : 1 - cos (2 * π * x) ≤ 2 * π ^ 2 * x ^ 2 := by
  have h := one_sub_sq_div_two_le_cos (x := 2 * π * x)
  nlinarith [h]

/-- **A return before `Q^{|s|}`.** If `2π² ≤ η Q²`, some integer height `1 ≤ t ≤ Q^{|s|}` returns `s`. -/
theorem exists_isReturn_le_pow [DecidableEq ι] (s : Finset ι) (ℓ : ι → ℝ) {Q : ℕ} (hQ : 1 ≤ Q)
    (hηQ : 2 * π ^ 2 ≤ η * (Q : ℝ) ^ 2) :
    ∃ t : ℝ, 1 ≤ t ∧ t ≤ (Q : ℝ) ^ s.card ∧ IsReturn s ℓ η t := by
  obtain ⟨k, hk1, hkQ, hclose⟩ :=
    HTGeometry.exists_dirichlet_simultaneous (fun i : s => ℓ i / (2 * π)) Q hQ
  rw [Fintype.card_coe] at hkQ
  refine ⟨k, by exact_mod_cast hk1, by exact_mod_cast hkQ, fun i hi => ?_⟩
  obtain ⟨m, hm⟩ := hclose ⟨i, hi⟩
  simp only at hm
  set e : ℝ := (k : ℝ) * (ℓ i / (2 * π)) - m with he
  have hangle : (k : ℝ) * ℓ i = 2 * π * e + (m : ℤ) * (2 * π) := by
    rw [he]
    field_simp
    ring
  rw [hangle, cos_add_int_mul_two_pi]
  have hQpos : (0 : ℝ) < Q := by exact_mod_cast hQ
  have he2 : e ^ 2 ≤ 1 / (Q : ℝ) ^ 2 := by
    have h1 : |e| ≤ 1 / Q := hm.le
    have h2 : e ^ 2 = |e| ^ 2 := (sq_abs e).symm
    rw [h2, one_div, ← inv_pow, ← one_div]
    exact pow_le_pow_left₀ (abs_nonneg e) h1 2
  have h3 := one_sub_cos_two_pi_mul_le e
  have h4 : 2 * π ^ 2 * e ^ 2 ≤ 2 * π ^ 2 * (1 / (Q : ℝ) ^ 2) :=
    mul_le_mul_of_nonneg_left he2 (by positivity)
  have h5 : 2 * π ^ 2 * (1 / (Q : ℝ) ^ 2) ≤ η := by
    rw [mul_one_div, div_le_iff₀ (by positivity)]
    exact hηQ
  linarith

theorem returnSet_nonempty [DecidableEq ι] (s : Finset ι) (ℓ : ι → ℝ) (hη : 0 < η) :
    (returnSet s ℓ η).Nonempty := by
  obtain ⟨Q, hQ⟩ := exists_nat_gt (π * √(2 / η))
  have hQ1 : 1 ≤ Q := by
    have : (0 : ℝ) < Q := lt_of_le_of_lt (by positivity) hQ
    exact_mod_cast this
  have hηQ : 2 * π ^ 2 ≤ η * (Q : ℝ) ^ 2 := by
    have h0 : 0 ≤ π * √(2 / η) := by positivity
    have h1 : (π * √(2 / η)) ^ 2 ≤ (Q : ℝ) ^ 2 := pow_le_pow_left₀ h0 hQ.le 2
    rw [mul_pow, sq_sqrt (by positivity)] at h1
    have h2 : η * (π ^ 2 * (2 / η)) = 2 * π ^ 2 := by field_simp
    nlinarith
  obtain ⟨t, ht1, -, ht⟩ := exists_isReturn_le_pow s ℓ hQ1 hηQ
  exact ⟨t, ht1, ht⟩

theorem bddBelow_returnSet (s : Finset ι) (ℓ : ι → ℝ) (η : ℝ) : BddBelow (returnSet s ℓ η) :=
  ⟨1, fun _ ht => ht.1⟩

/-- **The first return is attained.** -/
theorem firstReturn_mem [DecidableEq ι] (s : Finset ι) (ℓ : ι → ℝ) (hη : 0 < η) :
    firstReturn s ℓ η ∈ returnSet s ℓ η :=
  (isClosed_returnSet s ℓ η).csInf_mem (returnSet_nonempty s ℓ hη) (bddBelow_returnSet s ℓ η)

theorem one_le_firstReturn [DecidableEq ι] (s : Finset ι) (ℓ : ι → ℝ) (hη : 0 < η) :
    1 ≤ firstReturn s ℓ η :=
  (firstReturn_mem s ℓ hη).1

theorem isReturn_firstReturn [DecidableEq ι] (s : Finset ι) (ℓ : ι → ℝ) (hη : 0 < η) :
    IsReturn s ℓ η (firstReturn s ℓ η) :=
  (firstReturn_mem s ℓ hη).2

theorem firstReturn_le (ht1 : 1 ≤ t) (ht : IsReturn s ℓ η t) : firstReturn s ℓ η ≤ t :=
  csInf_le (bddBelow_returnSet s ℓ η) ⟨ht1, ht⟩

/-- **No return before the first.** -/
theorem not_isReturn_of_lt (ht1 : 1 ≤ t) (hlt : t < firstReturn s ℓ η) : ¬ IsReturn s ℓ η t :=
  fun ht => absurd (firstReturn_le ht1 ht) (not_le.mpr hlt)

/-- **The Dirichlet bound.** If `2π² ≤ η Q²` then `R ≤ Q^{|s|}`. -/
theorem firstReturn_le_pow [DecidableEq ι] (s : Finset ι) (ℓ : ι → ℝ) {Q : ℕ} (hQ : 1 ≤ Q)
    (hηQ : 2 * π ^ 2 ≤ η * (Q : ℝ) ^ 2) : firstReturn s ℓ η ≤ (Q : ℝ) ^ s.card := by
  obtain ⟨t, ht1, htQ, ht⟩ := exists_isReturn_le_pow s ℓ hQ hηQ
  exact (firstReturn_le ht1 ht).trans htQ

/-! ## Monotonicity -/

theorem IsReturn.mono_set {s' : Finset ι} (h : IsReturn s ℓ η t) (hs : s' ⊆ s) : IsReturn s' ℓ η t :=
  fun i hi => h i (hs hi)

theorem IsReturn.mono_prec (h : IsReturn s ℓ η t) (hη : η ≤ η') : IsReturn s ℓ η' t :=
  fun i hi => (h i hi).trans hη

/-- More steps return later. -/
theorem firstReturn_mono_set [DecidableEq ι] {s' : Finset ι} (hs : s' ⊆ s) (hη : 0 < η) :
    firstReturn s' ℓ η ≤ firstReturn s ℓ η :=
  firstReturn_le (one_le_firstReturn s ℓ hη) ((isReturn_firstReturn s ℓ hη).mono_set hs)

/-- Coarser precision returns earlier. -/
theorem firstReturn_anti_prec [DecidableEq ι] (hη : 0 < η) (hηη' : η ≤ η') :
    firstReturn s ℓ η' ≤ firstReturn s ℓ η :=
  firstReturn_le (one_le_firstReturn s ℓ hη) ((isReturn_firstReturn s ℓ hη).mono_prec hηη')

/-! ## Group laws -/

/-- `√(1 − cos x)` is the chord over `√2`. -/
theorem sqrt_one_sub_cos (x : ℝ) : √(1 - cos x) = PrimeTorusTheory.chord x / √2 := by
  rw [PrimeTorusTheory.one_sub_cos_eq_chord_sq, Real.sqrt_div' _ (by norm_num : (0 : ℝ) ≤ 2),
    Real.sqrt_sq (PrimeTorusTheory.chord_nonneg x)]

/-- `√(1 − cos)` is subadditive. -/
theorem sqrt_one_sub_cos_add_le (x y : ℝ) : √(1 - cos (x + y)) ≤ √(1 - cos x) + √(1 - cos y) := by
  rw [sqrt_one_sub_cos, sqrt_one_sub_cos, sqrt_one_sub_cos, ← add_div]
  exact div_le_div_of_nonneg_right (PrimeTorusTheory.chord_add_le x y) (Real.sqrt_nonneg 2)

/-- **Returns add.** -/
theorem IsReturn.add (ht : IsReturn s ℓ η t) (hu : IsReturn s ℓ η' u) :
    IsReturn s ℓ ((√η + √η') ^ 2) (t + u) := by
  intro i hi
  have h1 := sqrt_one_sub_cos_add_le (t * ℓ i) (u * ℓ i)
  rw [← add_mul] at h1
  have h2 : √(1 - cos (t * ℓ i)) ≤ √η := Real.sqrt_le_sqrt (ht i hi)
  have h3 : √(1 - cos (u * ℓ i)) ≤ √η' := Real.sqrt_le_sqrt (hu i hi)
  have h4 : √(1 - cos ((t + u) * ℓ i)) ≤ √η + √η' := h1.trans (add_le_add h2 h3)
  have h0 : 0 ≤ 1 - cos ((t + u) * ℓ i) := by linarith [cos_le_one ((t + u) * ℓ i)]
  calc 1 - cos ((t + u) * ℓ i) = √(1 - cos ((t + u) * ℓ i)) ^ 2 := (sq_sqrt h0).symm
    _ ≤ (√η + √η') ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) h4 2

theorem IsReturn.neg (ht : IsReturn s ℓ η t) : IsReturn s ℓ η (-t) := by
  intro i hi
  rw [neg_mul, cos_neg]
  exact ht i hi

/-- **Multiples of a return are returns.** -/
theorem IsReturn.nat_mul (ht : IsReturn s ℓ η t) (hη : 0 ≤ η) (n : ℕ) :
    IsReturn s ℓ ((n : ℝ) ^ 2 * η) (n * t) := by
  induction n with
  | zero => intro i _; simp
  | succ n ih =>
    have h := ih.add ht
    have e : (√((n : ℝ) ^ 2 * η) + √η) ^ 2 = ((n + 1 : ℕ) : ℝ) ^ 2 * η := by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (Nat.cast_nonneg n)]
      have hs : √η ^ 2 = η := sq_sqrt hη
      push_cast
      nlinarith [hs]
    rw [e, show ((n + 1 : ℕ) : ℝ) * t = n * t + t by push_cast; ring]
    exact h

/-! ## Corners -/

/-- `1 − cos 2x ≤ 4(1 + cos x)`. -/
theorem one_sub_cos_two_mul_le (x : ℝ) : 1 - cos (2 * x) ≤ 4 * (1 + cos x) := by
  rw [cos_two_mul]
  nlinarith [cos_le_one x, neg_one_le_cos x]

/-- **A visit of `−1` is a return at twice the height.** -/
theorem IsAntiReturn.two_mul (ht : IsAntiReturn s ℓ η t) : IsReturn s ℓ (4 * η) (2 * t) := by
  intro i hi
  have h := one_sub_cos_two_mul_le (t * ℓ i)
  rw [show 2 * (t * ℓ i) = 2 * t * ℓ i by ring] at h
  linarith [ht i hi]

/-- **The Liouville corner is reached no earlier than half the first return.** -/
theorem firstReturn_le_two_mul_of_antiReturn (ht1 : 1 ≤ t) (ht : IsAntiReturn s ℓ η t) :
    firstReturn s ℓ (4 * η) ≤ 2 * t :=
  firstReturn_le (by linarith) ht.two_mul

/-! ## Rank one -/

/-- **Periodic flows have no first-return problem.** If every step is an integer multiple of `ℓ₀ > 0`, the height
`2πk/ℓ₀`, `k = ⌈ℓ₀/2π⌉`, is an exact return, for every set and every precision `η ≥ 0`. -/
theorem firstReturn_le_of_rankOne {ℓ₀ : ℝ} (hℓ₀ : 0 < ℓ₀) (n : ι → ℤ) (hℓ : ∀ i ∈ s, ℓ i = n i * ℓ₀)
    (hη : 0 ≤ η) : firstReturn s ℓ η ≤ 2 * π * ⌈ℓ₀ / (2 * π)⌉₊ / ℓ₀ := by
  set k : ℕ := ⌈ℓ₀ / (2 * π)⌉₊ with hk
  have hk1 : ℓ₀ / (2 * π) ≤ k := Nat.le_ceil _
  refine firstReturn_le ?_ fun i hi => ?_
  · rw [le_div_iff₀ hℓ₀, one_mul]
    have := mul_le_mul_of_nonneg_left hk1 (by positivity : (0 : ℝ) ≤ 2 * π)
    rw [mul_div_cancel₀ _ (by positivity)] at this
    linarith
  · rw [hℓ i hi]
    have e : 2 * π * (k : ℝ) / ℓ₀ * ((n i : ℝ) * ℓ₀) = ((k * n i : ℤ) : ℝ) * (2 * π) := by
      push_cast
      field_simp
    rw [e, cos_int_mul_two_pi]
    linarith

end

end GaloisForLFunctions.TailArithmeticOfThePrimeOrbit
