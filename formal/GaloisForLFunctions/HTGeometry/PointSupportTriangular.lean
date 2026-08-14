import GaloisForLFunctions.HTGeometry.PointSupportPrincipalOperator

/-!
# Triangular jet systems and smooth multipliers

Two facts complete the exclusion of point-supported solutions for an operator whose lower-order
terms carry a factor vanishing at the origin.

* A smooth multiplier vanishing to order `p` at the origin moves the jet coefficient `c_i` only to
  coefficients of index at least `i + p`: the Leibniz rule against a jet test function selects a
  single term.
* A jet system in which `(2i+1)c_i` is a combination of strictly higher coefficients has only the
  zero solution, by descending induction.
-/

open Set SchwartzMap

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

/-- **The jet coefficients of a smooth multiple of a jet test function.** -/
theorem iteratedDeriv_mul_jetTest_zero {g : ℝ → ℂ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (i j : ℕ) :
    iteratedDeriv j (fun x : ℝ => g x * (jetTest i : ℝ → ℂ) x) 0
      = if i ≤ j then (j.choose (j - i) : ℂ) * iteratedDeriv (j - i) g 0 else 0 := by
  have hgc : ContDiffAt ℝ (j : ℕ∞) g 0 := (hg.of_le (by exact_mod_cast le_top)).contDiffAt
  have hφc : ContDiffAt ℝ (j : ℕ∞) ((jetTest i : SchwartzMap ℝ ℂ) : ℝ → ℂ) 0 :=
    (((jetTest i).smooth').of_le (by exact_mod_cast le_top)).contDiffAt
  have hfun : (fun x : ℝ => g x * (jetTest i : ℝ → ℂ) x)
      = g * ((jetTest i : SchwartzMap ℝ ℂ) : ℝ → ℂ) := rfl
  rw [hfun, iteratedDeriv_mul hgc hφc]
  have hterm : ∀ m ∈ Finset.range (j+1),
      ((j.choose m : ℂ) * iteratedDeriv m g 0 * iteratedDeriv (j - m) (jetTest i : ℝ → ℂ) 0)
        = if j - m = i then (j.choose m : ℂ) * iteratedDeriv m g 0 else 0 := by
    intro m _
    rw [iteratedDeriv_jetTest_zero]
    by_cases h : j - m = i
    · rw [if_pos h, if_pos h, mul_one]
    · rw [if_neg h, if_neg h, mul_zero]
  rw [Finset.sum_congr rfl hterm]
  by_cases hij : i ≤ j
  · rw [if_pos hij]
    have hunique : ∀ m ∈ Finset.range (j+1),
        (if j - m = i then (j.choose m : ℂ) * iteratedDeriv m g 0 else 0)
          = if m = j - i then (j.choose (j - i) : ℂ) * iteratedDeriv (j - i) g 0 else 0 := by
      intro m hm
      have hmj : m ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
      by_cases h : m = j - i
      · subst h
        rw [if_pos rfl, if_pos (by omega)]
      · rw [if_neg h, if_neg (by omega)]
    rw [Finset.sum_congr rfl hunique,
      Finset.sum_ite_eq' (Finset.range (j+1)) (j - i)
        (fun _ => (j.choose (j - i) : ℂ) * iteratedDeriv (j - i) g 0),
      if_pos (Finset.mem_range.mpr (by omega))]
  · rw [if_neg hij]
    refine Finset.sum_eq_zero fun m hm => ?_
    have hmj : m ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
    rw [if_neg (by omega)]

/-- **A triangular jet system has only the zero solution.** -/
theorem coeff_eq_zero_of_triangular {N : ℕ} {c : ℕ → X} {a : ℕ → ℕ → ℂ}
    (h : ∀ i, i ≤ N → ((2 * i + 1 : ℂ)) • c i
      = ∑ j ∈ Finset.range (N+1), (if i < j then a i j else 0) • c j) :
    ∀ i, i ≤ N → c i = 0 := by
  have hstrong : ∀ d : ℕ, ∀ i, i ≤ N → N - i ≤ d → c i = 0 := by
    intro d
    induction d with
    | zero =>
      intro i hi hd
      have hiN : i = N := by omega
      have hzero : ∑ j ∈ Finset.range (N+1), (if i < j then a i j else 0) • c j = 0 := by
        refine Finset.sum_eq_zero fun j hj => ?_
        have hjN : j ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
        rw [if_neg (by omega), zero_smul]
      have hN := h i hi
      rw [hzero] at hN
      have hne : ((2 * (i : ℂ) + 1)) ≠ 0 := by
        intro hcon
        have hre : ((2 * (i : ℂ) + 1)).re = 2 * (i : ℝ) + 1 := by simp
        rw [hcon] at hre
        have : (0:ℝ) = 2 * (i : ℝ) + 1 := by simpa using hre
        have hnn : (0:ℝ) ≤ (i : ℝ) := by positivity
        linarith
      exact (smul_eq_zero.mp hN).resolve_left hne
    | succ d ih =>
      intro i hi hd
      rcases le_or_gt (N - i) d with hle | hgt
      · exact ih i hi hle
      · have hzero : ∑ j ∈ Finset.range (N+1), (if i < j then a i j else 0) • c j = 0 := by
          refine Finset.sum_eq_zero fun j hj => ?_
          have hjN : j ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
          by_cases hlt : i < j
          · have hcj : c j = 0 := ih j hjN (by omega)
            rw [hcj, smul_zero]
          · rw [if_neg hlt, zero_smul]
        have hi' := h i hi
        rw [hzero] at hi'
        have hne : ((2 * (i : ℂ) + 1)) ≠ 0 := by
          intro hcon
          have hre : ((2 * (i : ℂ) + 1)).re = 2 * (i : ℝ) + 1 := by simp
          rw [hcon] at hre
          have : (0:ℝ) = 2 * (i : ℝ) + 1 := by simpa using hre
          have hnn : (0:ℝ) ≤ (i : ℝ) := by positivity
          linarith
        exact (smul_eq_zero.mp hi').resolve_left hne
  intro i hi
  exact hstrong (N - i) i hi le_rfl

/-- **A triangular jet system with operator coefficients has only the zero solution.**  The
coefficient maps need not be linear; only that they send zero to zero. -/
theorem coeff_eq_zero_of_triangular_map {N : ℕ} {c : ℕ → X} {A : ℕ → ℕ → X → X}
    (hA : ∀ i j, A i j 0 = 0)
    (h : ∀ i, i ≤ N → ((2 * i + 1 : ℂ)) • c i
      = ∑ j ∈ Finset.range (N+1), if i < j then A i j (c j) else 0) :
    ∀ i, i ≤ N → c i = 0 := by
  have hne : ∀ i : ℕ, ((2 * (i : ℂ) + 1)) ≠ 0 := by
    intro i hcon
    have hre : ((2 * (i : ℂ) + 1)).re = 2 * (i : ℝ) + 1 := by simp
    rw [hcon] at hre
    have : (0:ℝ) = 2 * (i : ℝ) + 1 := by simpa using hre
    have hnn : (0:ℝ) ≤ (i : ℝ) := by positivity
    linarith
  have hstrong : ∀ d : ℕ, ∀ i, i ≤ N → N - i ≤ d → c i = 0 := by
    intro d
    induction d with
    | zero =>
      intro i hi hd
      have hiN : i = N := by omega
      have hzero : ∑ j ∈ Finset.range (N+1), (if i < j then A i j (c j) else 0) = 0 := by
        refine Finset.sum_eq_zero fun j hj => ?_
        have hjN : j ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
        rw [if_neg (by omega)]
      have hN := h i hi
      rw [hzero] at hN
      exact (smul_eq_zero.mp hN).resolve_left (hne i)
    | succ d ih =>
      intro i hi hd
      rcases le_or_gt (N - i) d with hle | hgt
      · exact ih i hi hle
      · have hzero : ∑ j ∈ Finset.range (N+1), (if i < j then A i j (c j) else 0) = 0 := by
          refine Finset.sum_eq_zero fun j hj => ?_
          have hjN : j ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
          by_cases hlt : i < j
          · have hcj : c j = 0 := ih j hjN (by omega)
            rw [if_pos hlt, hcj, hA]
          · rw [if_neg hlt]
        have hi' := h i hi
        rw [hzero] at hi'
        exact (smul_eq_zero.mp hi').resolve_left (hne i)
  intro i hi
  exact hstrong (N - i) i hi le_rfl

end

end GaloisForLFunctions.HTGeometry
