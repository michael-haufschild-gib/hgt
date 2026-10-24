import GaloisForLFunctions.ArithmeticOrientationTheory.FrustrationIndexControlsTheGroundEnergy
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Algebra.Order.Chebyshev

/-!
# Frustration bounds the ground energy from below

The frustration index controls the ground energy of the signed Dirichlet form from above,
`μ ≤ 4 ν_w / n` (`groundEnergy_le_frustrationMass`).  This module proves the matching lower bound,
the **signed Cheeger inequality**.  For a sign vector `s` and a set `S` let
`signedCutMass s c S` be the coupling mass leaving `S` plus the misaligned mass inside `S`; if
every `(s, S)` has `signedCutMass s c S ≥ h |S|` and every degree is at most `D`, then

    h² Σ x_i² ≤ 4 D · D_c(x)        (`sq_mul_le_signedDirichletForm`),

so `μ ≥ h²/(4D)` (`le_groundEnergy_of_cheeger`).

* **Co-area** (`coarea_le`): integrating the hypothesis over the level sets `{x² > t}` of a
  profile turns set inequalities into the pair inequality
  `h Σ a ≤ Σ_{ij} (w_ij (a_i − a_j)⁺ + m_ij min(a_i, a_j))`.
* **Modulus coordinates** (`edgeTerm_eq_edgeLength`): in the sign switching of the profile itself
  each edge term is `|c| ℓ²`, with `ℓ = |x_i| + |x_j|` across a misaligned overlap and
  `||x_i| − |x_j||` across an aligned one; the co-area integrand is at most `ℓ (|x_i| + |x_j|)`
  (`coareaTerm_le`), and Cauchy–Schwarz closes the bound.
* **Frustration as a budget discount** (`incidenceEnergy_ge_of_cheeger`): the incidence energy is
  half the Dirichlet form plus the excess of the budgets over the degrees
  (`incidenceEnergy_eq_signedDirichletForm`), so a signed form is nonnegative as soon as every
  budget falls short of its degree by at most `h²/(8D)`.  Balanced forms have `h = 0` and need the
  full degree; frustration is paid globally, and the Cheeger constant measures how much of it the
  form pays itself.
-/

open Finset MeasureTheory
open GaloisForLFunctions.SignedArithmeticEnergyIncidence

namespace GaloisForLFunctions.ArithmeticOrientationTheory

noncomputable section
set_option autoImplicit false

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### The discrete co-area inequality -/

/-- `∫_{[0,M)} 1_{[a,b)} = (b − a)⁺` for `0 ≤ a` and `b ≤ M`. -/
theorem setIntegral_Ico_indicator_one {a b M : ℝ} (ha : 0 ≤ a) (hbM : b ≤ M) :
    ∫ t in Set.Ico 0 M, (Set.Ico a b).indicator (fun _ => (1 : ℝ)) t = max (b - a) 0 := by
  rw [integral_indicator_const _ measurableSet_Ico, smul_eq_mul, mul_one,
    Measure.real_def, Measure.restrict_apply measurableSet_Ico, Set.Ico_inter_Ico,
    max_eq_left ha, min_eq_left hbM, ← Measure.real_def, Real.volume_real_Ico]

theorem integrableOn_Ico_indicator_one (a b M : ℝ) :
    IntegrableOn (fun t => (Set.Ico a b).indicator (fun _ => (1 : ℝ)) t) (Set.Ico 0 M) :=
  (integrableOn_const (by simp)).indicator measurableSet_Ico

/-- **The discrete co-area inequality.**  If every finite set `S` satisfies
`h |S| ≤ w(S, Sᶜ) + m(S, S)` with nonnegative weights, then integrating over the level sets
`{a > t}` of a nonnegative profile gives
`h Σ a ≤ Σ_{i,j} (w_ij (a_i − a_j)⁺ + m_ij min(a_i, a_j))`. -/
theorem coarea_le (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (w m : ι → ι → ℝ) (h : ℝ)
    (hpt : ∀ S : Finset ι, h * S.card ≤ ∑ i ∈ S, ∑ j ∈ Sᶜ, w i j + ∑ i ∈ S, ∑ j ∈ S, m i j) :
    h * ∑ i, a i ≤ ∑ i, ∑ j, (w i j * max (a i - a j) 0 + m i j * min (a i) (a j)) := by
  set M := ∑ i, a i + 1
  have haM : ∀ i, a i ≤ M := fun i => by
    have := single_le_sum (fun j _ => ha j) (mem_univ i)
    linarith
  have hmin : ∀ i j, min (a i) (a j) ≤ M := fun i j => (min_le_left _ _).trans (haM i)
  set L : ℝ → ℝ := fun t => h * ∑ i, (Set.Ico 0 (a i)).indicator (fun _ => (1 : ℝ)) t
  set R : ℝ → ℝ := fun t => ∑ i, ∑ j, (w i j * (Set.Ico (a j) (a i)).indicator (fun _ => (1 : ℝ)) t +
    m i j * (Set.Ico 0 (min (a i) (a j))).indicator (fun _ => (1 : ℝ)) t)
  -- on `[0, M)` the integrands are the two sides of the hypothesis at the level set `{a > t}`
  have hLR : ∀ t ∈ Set.Ico 0 M, L t ≤ R t := by
    intro t ht
    set S := univ.filter fun i => t < a i
    have hmem : ∀ i, i ∈ S ↔ t < a i := fun i => by simp [S]
    have hL : L t = h * S.card := by
      simp only [L]
      congr 1
      rw [card_filter, Nat.cast_sum]
      refine sum_congr rfl fun i _ => ?_
      by_cases hi : t < a i
      · rw [Set.indicator_of_mem (Set.mem_Ico.2 ⟨ht.1, hi⟩), if_pos hi, Nat.cast_one]
      · rw [Set.indicator_of_notMem (fun h' => hi (Set.mem_Ico.1 h').2), if_neg hi, Nat.cast_zero]
    have hR : R t = ∑ i ∈ S, ∑ j ∈ Sᶜ, w i j + ∑ i ∈ S, ∑ j ∈ S, m i j := by
      simp only [R, sum_add_distrib]
      congr 1
      · rw [← sum_filter_add_sum_filter_not univ (fun i => t < a i)]
        have h2 : ∑ i ∈ univ.filter (fun i => ¬ t < a i), ∑ j, w i j *
            (Set.Ico (a j) (a i)).indicator (fun _ => (1 : ℝ)) t = 0 :=
          sum_eq_zero fun i hi => sum_eq_zero fun j _ => by
            rw [Set.indicator_of_notMem (fun h' => (mem_filter.1 hi).2 (Set.mem_Ico.1 h').2),
              mul_zero]
        rw [h2, add_zero]
        refine sum_congr rfl fun i hi => ?_
        rw [← sum_filter_add_sum_filter_not univ (fun j => t < a j)]
        have h3 : ∑ j ∈ univ.filter (fun j => t < a j), w i j *
            (Set.Ico (a j) (a i)).indicator (fun _ => (1 : ℝ)) t = 0 :=
          sum_eq_zero fun j hj => by
            rw [Set.indicator_of_notMem (fun h' => not_le.2 (mem_filter.1 hj).2
              (Set.mem_Ico.1 h').1), mul_zero]
        rw [h3, zero_add, show Sᶜ = univ.filter (fun j => ¬ t < a j) by ext; simp [S]]
        refine sum_congr rfl fun j hj => ?_
        rw [Set.indicator_of_mem (Set.mem_Ico.2 ⟨not_lt.1 (mem_filter.1 hj).2,
          (mem_filter.1 hi).2⟩), mul_one]
      · rw [← sum_filter_add_sum_filter_not univ (fun i => t < a i)]
        have h2 : ∑ i ∈ univ.filter (fun i => ¬ t < a i), ∑ j, m i j *
            (Set.Ico 0 (min (a i) (a j))).indicator (fun _ => (1 : ℝ)) t = 0 :=
          sum_eq_zero fun i hi => sum_eq_zero fun j _ => by
            rw [Set.indicator_of_notMem (fun h' => (mem_filter.1 hi).2
              ((Set.mem_Ico.1 h').2.trans_le (min_le_left _ _))), mul_zero]
        rw [h2, add_zero]
        refine sum_congr rfl fun i hi => ?_
        rw [← sum_filter_add_sum_filter_not univ (fun j => t < a j)]
        have h3 : ∑ j ∈ univ.filter (fun j => ¬ t < a j), m i j *
            (Set.Ico 0 (min (a i) (a j))).indicator (fun _ => (1 : ℝ)) t = 0 :=
          sum_eq_zero fun j hj => by
            rw [Set.indicator_of_notMem (fun h' => (mem_filter.1 hj).2
              ((Set.mem_Ico.1 h').2.trans_le (min_le_right _ _))), mul_zero]
        rw [h3, add_zero]
        refine sum_congr rfl fun j hj => ?_
        rw [Set.indicator_of_mem (Set.mem_Ico.2 ⟨ht.1, lt_min (mem_filter.1 hi).2
          (mem_filter.1 hj).2⟩), mul_one]
    rw [hL, hR]
    exact hpt S
  have hLi : IntegrableOn L (Set.Ico 0 M) :=
    (integrable_finsetSum _ fun i _ => integrableOn_Ico_indicator_one 0 (a i) M).const_mul h
  have hRi : IntegrableOn R (Set.Ico 0 M) :=
    integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
      ((integrableOn_Ico_indicator_one _ _ M).const_mul _).add
        ((integrableOn_Ico_indicator_one _ _ M).const_mul _)
  have hint := setIntegral_mono_on hLi hRi measurableSet_Ico hLR
  have hLv : ∫ t in Set.Ico 0 M, L t = h * ∑ i, a i := by
    simp only [L]
    rw [integral_const_mul, integral_finsetSum _ fun i _ => integrableOn_Ico_indicator_one 0 (a i) M]
    congr 1
    refine sum_congr rfl fun i _ => ?_
    rw [setIntegral_Ico_indicator_one le_rfl (haM i), sub_zero, max_eq_left (ha i)]
  have hGi : ∀ i j, IntegrableOn (fun t => w i j * (Set.Ico (a j) (a i)).indicator (fun _ => (1 : ℝ)) t +
      m i j * (Set.Ico 0 (min (a i) (a j))).indicator (fun _ => (1 : ℝ)) t) (Set.Ico 0 M) :=
    fun i j => ((integrableOn_Ico_indicator_one _ _ M).const_mul _).add
      ((integrableOn_Ico_indicator_one _ _ M).const_mul _)
  have hG : ∀ i j, ∫ t in Set.Ico 0 M, (w i j * (Set.Ico (a j) (a i)).indicator (fun _ => (1 : ℝ)) t +
      m i j * (Set.Ico 0 (min (a i) (a j))).indicator (fun _ => (1 : ℝ)) t) =
      w i j * max (a i - a j) 0 + m i j * min (a i) (a j) := fun i j => by
    rw [integral_add ((integrableOn_Ico_indicator_one _ _ M).const_mul _)
      ((integrableOn_Ico_indicator_one _ _ M).const_mul _), integral_const_mul, integral_const_mul,
      setIntegral_Ico_indicator_one (ha j) (haM i), setIntegral_Ico_indicator_one le_rfl (hmin i j),
      sub_zero, max_eq_left (le_min (ha i) (ha j))]
  have hF : ∀ i, ∫ t in Set.Ico 0 M, ∑ j, (w i j * (Set.Ico (a j) (a i)).indicator (fun _ => (1 : ℝ)) t +
      m i j * (Set.Ico 0 (min (a i) (a j))).indicator (fun _ => (1 : ℝ)) t) =
      ∑ j, (w i j * max (a i - a j) 0 + m i j * min (a i) (a j)) := fun i => by
    rw [integral_finsetSum _ fun j _ => hGi i j]
    exact sum_congr rfl fun j _ => hG i j
  have hRv : ∫ t in Set.Ico 0 M, R t =
      ∑ i, ∑ j, (w i j * max (a i - a j) 0 + m i j * min (a i) (a j)) := by
    simp only [R]
    rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hGi i j]
    exact sum_congr rfl fun i _ => hF i
  linarith


/-! ### The signed Cheeger inequality -/

/-- The frustration seen by a set `S` under the switching `s`: the coupling mass leaving `S` plus
the misaligned mass inside `S`. -/
def signedCutMass (s : ι → ℝ) (c : ι → ι → ℝ) (S : Finset ι) : ℝ :=
  ∑ i ∈ S, ∑ j ∈ Sᶜ, |c i j| +
    ∑ i ∈ S, ∑ j ∈ S, if i ≠ j ∧ 0 < s i * s j * c i j then |c i j| else 0

omit [Fintype ι] [DecidableEq ι] in
theorem orientSign_mul_abs (t : ℝ) : orientSign t * |t| = t := by
  unfold orientSign
  split_ifs with h
  · rw [one_mul, abs_of_pos h]
  · rw [abs_of_nonpos (not_lt.1 h)]; ring

/-- The edge length of a profile at an overlap, in its own sign switching: `|x_i| + |x_j|`
across a misaligned overlap, `||x_i| − |x_j||` across an aligned one. -/
def edgeLength (c : ι → ι → ℝ) (x : ι → ℝ) (i j : ι) : ℝ :=
  if 0 < orientSign (x i) * orientSign (x j) * c i j then |x i| + |x j| else |(|x i| - |x j|)|

omit [Fintype ι] [DecidableEq ι] in
/-- **The edge term in modulus coordinates**: `|c|(x_i + sgn(c) x_j)² = |c| ℓ_ij²`. -/
theorem edgeTerm_eq_edgeLength (c : ι → ι → ℝ) (x : ι → ℝ) (i j : ι) :
    |c i j| * (x i + orientSign (c i j) * x j) ^ 2 = |c i j| * edgeLength c x i j ^ 2 := by
  rcases eq_or_ne (c i j) 0 with h0 | h0
  · simp [h0]
  congr 1
  set a := orientSign (x i)
  set b := orientSign (x j)
  have ha : a ^ 2 = 1 := orientSign_sq _
  have hb : b ^ 2 = 1 := orientSign_sq _
  have hxi : x i = a * |x i| := (orientSign_mul_abs _).symm
  have hxj : x j = b * |x j| := (orientSign_mul_abs _).symm
  have key : (x i + orientSign (c i j) * x j) ^ 2 =
      (|x i| + orientSign (c i j) * (a * b) * |x j|) ^ 2 := by
    have h1 : |x i| + orientSign (c i j) * (a * b) * |x j| =
        a * (a * |x i| + orientSign (c i j) * (b * |x j|)) := by
      linear_combination (-|x i|) * ha
    rw [h1, mul_pow, ha, one_mul, ← hxi, ← hxj]
  rw [key]
  unfold edgeLength
  have hab : a * b = 1 ∨ a * b = -1 := by
    rcases sq_eq_one_iff.1 ha with h | h <;> rcases sq_eq_one_iff.1 hb with h' | h' <;>
      simp [h, h']
  rcases lt_or_gt_of_ne h0 with hc | hc
  · rw [orientSign_of_neg hc]
    rcases hab with h | h
    · rw [if_neg (by rw [h, one_mul]; linarith), h, sq_abs]; ring
    · rw [if_pos (by rw [h]; linarith), h]; ring
  · rw [orientSign_of_pos hc]
    rcases hab with h | h
    · rw [if_pos (by rw [h, one_mul]; exact hc), h]; ring
    · rw [if_neg (by rw [h]; linarith), h, sq_abs]; ring

omit [Fintype ι] in
/-- The co-area integrand is dominated by the edge length times `|x_i| + |x_j|`. -/
theorem coareaTerm_le (c : ι → ι → ℝ) (x : ι → ℝ) (i j : ι) :
    max (x i ^ 2 - x j ^ 2) 0 +
        (if i ≠ j ∧ 0 < orientSign (x i) * orientSign (x j) * c i j then min (x i ^ 2) (x j ^ 2)
          else 0) ≤
      edgeLength c x i j * (|x i| + |x j|) := by
  have hy := abs_nonneg (x i)
  have hz := abs_nonneg (x j)
  have hi2 : x i ^ 2 = |x i| ^ 2 := (sq_abs _).symm
  have hj2 : x j ^ 2 = |x j| ^ 2 := (sq_abs _).symm
  rw [hi2, hj2]
  have key1 : max (|x i| ^ 2 - |x j| ^ 2) 0 ≤ |(|x i| - |x j|)| * (|x i| + |x j|) := by
    rw [show |x i| ^ 2 - |x j| ^ 2 = (|x i| - |x j|) * (|x i| + |x j|) by ring]
    refine max_le ((le_abs_self _).trans (le_of_eq ?_)) (by positivity)
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ |x i| + |x j|)]
  have key2 : max (|x i| ^ 2 - |x j| ^ 2) 0 + min (|x i| ^ 2) (|x j| ^ 2) ≤
      (|x i| + |x j|) * (|x i| + |x j|) := by
    rcases le_total (|x i| ^ 2) (|x j| ^ 2) with h | h
    · rw [max_eq_right (by linarith), min_eq_left h]; nlinarith
    · rw [max_eq_left (by linarith), min_eq_right h]; nlinarith
  have key3 : |(|x i| - |x j|)| ≤ |x i| + |x j| :=
    (abs_sub _ _).trans (by rw [abs_abs, abs_abs])
  unfold edgeLength
  split_ifs with h1 h2 h2
  · exact key2
  · exact absurd h1.2 h2
  · rw [add_zero]
    exact key1.trans (mul_le_mul_of_nonneg_right key3 (by positivity))
  · rw [add_zero]
    exact key1

omit [DecidableEq ι] in
/-- Cauchy–Schwarz for nonnegatively weighted double sums. -/
theorem sq_sum_sum_le (w u v : ι → ι → ℝ) (hw : ∀ i j, 0 ≤ w i j) :
    (∑ i, ∑ j, w i j * (u i j * v i j)) ^ 2 ≤
      (∑ i, ∑ j, w i j * u i j ^ 2) * ∑ i, ∑ j, w i j * v i j ^ 2 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq (univ : Finset (ι × ι))
    (fun p => Real.sqrt (w p.1 p.2) * u p.1 p.2) (fun p => Real.sqrt (w p.1 p.2) * v p.1 p.2)
  have e1 : ∀ p : ι × ι, Real.sqrt (w p.1 p.2) * u p.1 p.2 * (Real.sqrt (w p.1 p.2) * v p.1 p.2) =
      w p.1 p.2 * (u p.1 p.2 * v p.1 p.2) := fun p => by
    rw [show Real.sqrt (w p.1 p.2) * u p.1 p.2 * (Real.sqrt (w p.1 p.2) * v p.1 p.2) =
      (Real.sqrt (w p.1 p.2) * Real.sqrt (w p.1 p.2)) * (u p.1 p.2 * v p.1 p.2) by ring,
      Real.mul_self_sqrt (hw _ _)]
  have e2 : ∀ p : ι × ι, (Real.sqrt (w p.1 p.2) * u p.1 p.2) ^ 2 = w p.1 p.2 * u p.1 p.2 ^ 2 :=
    fun p => by rw [mul_pow, Real.sq_sqrt (hw _ _)]
  have e3 : ∀ p : ι × ι, (Real.sqrt (w p.1 p.2) * v p.1 p.2) ^ 2 = w p.1 p.2 * v p.1 p.2 ^ 2 :=
    fun p => by rw [mul_pow, Real.sq_sqrt (hw _ _)]
  simp only [e1, e2, e3] at h
  rw [← Fintype.sum_prod_type' (f := fun i j => w i j * (u i j * v i j)),
    ← Fintype.sum_prod_type' (f := fun i j => w i j * u i j ^ 2),
    ← Fintype.sum_prod_type' (f := fun i j => w i j * v i j ^ 2)]
  exact h

/-- **The signed Cheeger inequality.**  If every set `S` and every switching `s` see frustration at
least `h |S|`, and every point has degree at most `D`, then for every profile
`h² Σ x_i² ≤ 4 D · D_c(x)`. -/
theorem sq_mul_le_signedDirichletForm {c : ι → ι → ℝ} (hc : IsSymmetricCoupling c) {h D : ℝ}
    (hh0 : 0 ≤ h) (hD : ∀ i, pointDegree c i ≤ D)
    (hh : ∀ s : ι → ℝ, IsSignVector s → ∀ S : Finset ι, h * S.card ≤ signedCutMass s c S)
    (x : ι → ℝ) :
    h ^ 2 * ∑ i, x i ^ 2 ≤ 4 * D * signedDirichletForm c x := by
  set s : ι → ℝ := fun i => orientSign (x i)
  set w : ι → ι → ℝ := fun i j => if i = j then 0 else |c i j|
  set m : ι → ι → ℝ := fun i j => if i ≠ j ∧ 0 < s i * s j * c i j then |c i j| else 0
  -- the co-area inequality over the level sets of `x²`
  have hco := coarea_le (fun i => x i ^ 2) (fun i => sq_nonneg _) w m h fun S => by
    have h1 := hh s (fun i => orientSign_sq _) S
    have h2 : ∑ i ∈ S, ∑ j ∈ Sᶜ, w i j = ∑ i ∈ S, ∑ j ∈ Sᶜ, |c i j| :=
      sum_congr rfl fun i hi => sum_congr rfl fun j hj => by
        simp only [w]
        rw [if_neg fun e => (mem_compl.1 hj) (by rw [← e]; exact hi)]
    rw [h2]
    exact h1
  -- each term is at most `|c| ℓ_ij (|x_i| + |x_j|)`
  have hterm : ∀ i j, w i j * max (x i ^ 2 - x j ^ 2) 0 + m i j * min (x i ^ 2) (x j ^ 2) ≤
      (if i = j then 0 else |c i j|) * (edgeLength c x i j * (|x i| + |x j|)) := by
    intro i j
    by_cases hij : i = j
    · subst hij; simp [w, m]
    · simp only [w, m, if_neg hij]
      have := coareaTerm_le c x i j
      have hc0 := abs_nonneg (c i j)
      split_ifs at this ⊢ with h3
      · nlinarith [mul_le_mul_of_nonneg_left this hc0]
      · simp only [add_zero] at this ⊢
        nlinarith [mul_le_mul_of_nonneg_left this hc0]
  set A := ∑ i, ∑ j, (if i = j then 0 else |c i j|) * (edgeLength c x i j * (|x i| + |x j|))
  have hA : h * ∑ i, x i ^ 2 ≤ A :=
    hco.trans (sum_le_sum fun i _ => sum_le_sum fun j _ => hterm i j)
  -- Cauchy–Schwarz over the ordered pairs
  set E := ∑ i, ∑ j, (if i = j then 0 else |c i j|) * edgeLength c x i j ^ 2
  set B := ∑ i, ∑ j, (if i = j then 0 else |c i j|) * (|x i| + |x j|) ^ 2
  have hW : ∀ i j, 0 ≤ (if i = j then (0 : ℝ) else |c i j|) := fun i j => by
    split_ifs <;> simp
  have hCS : A ^ 2 ≤ E * B := sq_sum_sum_le _ _ _ hW
  -- the edge energy is the Dirichlet form
  have hE : E = signedDirichletForm c x := by
    unfold signedDirichletForm
    refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
    split_ifs
    · simp
    · exact (edgeTerm_eq_edgeLength c x i j).symm
  -- the moduli energy is at most four times the weighted mass
  have hB : B ≤ 4 * D * ∑ i, x i ^ 2 := by
    have h1 : B ≤ ∑ i, ∑ j, (if i = j then 0 else |c i j|) * (2 * x i ^ 2 + 2 * x j ^ 2) :=
      sum_le_sum fun i _ => sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (by
        rw [← sq_abs (x i), ← sq_abs (x j)]; nlinarith [sq_nonneg (|x i| - |x j|)]) (hW i j)
    have h2 : ∑ i, ∑ j, (if i = j then 0 else |c i j|) * (2 * x i ^ 2 + 2 * x j ^ 2) =
        4 * ∑ i, pointDegree c i * x i ^ 2 := by
      have hsplit : ∀ i j, (if i = j then 0 else |c i j|) * (2 * x i ^ 2 + 2 * x j ^ 2) =
          2 * ((if i = j then 0 else |c i j|) * x i ^ 2) +
            2 * ((if j = i then 0 else |c j i|) * x j ^ 2) := fun i j => by
        by_cases hij : i = j
        · subst hij; simp
        · rw [if_neg hij, if_neg (Ne.symm hij), hc j i]; ring
      simp_rw [hsplit, sum_add_distrib, ← mul_sum]
      rw [sum_comm (f := fun i j => (if j = i then 0 else |c j i|) * x j ^ 2)]
      unfold pointDegree
      simp_rw [sum_mul]
      ring
    have h3 : ∑ i, pointDegree c i * x i ^ 2 ≤ D * ∑ i, x i ^ 2 := by
      rw [mul_sum]
      exact sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hD i) (sq_nonneg _)
    linarith
  -- assemble
  set M := ∑ i, x i ^ 2
  have hM0 : 0 ≤ M := sum_nonneg fun i _ => sq_nonneg _
  rcases hM0.lt_or_eq with hM | hM
  · have hhM : 0 ≤ h * M := mul_nonneg hh0 hM0
    have h1 : (h * M) ^ 2 ≤ signedDirichletForm c x * (4 * D * M) := by
      rw [← hE]
      calc (h * M) ^ 2 ≤ A ^ 2 := pow_le_pow_left₀ hhM hA 2
        _ ≤ E * B := hCS
        _ ≤ E * (4 * D * M) := mul_le_mul_of_nonneg_left hB (by
            rw [hE]; exact signedDirichletForm_nonneg c x)
    have h2 : (h ^ 2 * M) * M ≤ (4 * D * signedDirichletForm c x) * M := by nlinarith [h1]
    exact le_of_mul_le_mul_right h2 hM
  · have hx : ∀ i, x i = 0 := fun i => by
      have := (sum_eq_zero_iff_of_nonneg fun j _ => sq_nonneg (x j)).1 hM.symm i (mem_univ i)
      exact pow_eq_zero_iff (two_ne_zero) |>.1 this
    have : signedDirichletForm c x = 0 := by simp [signedDirichletForm, hx]
    rw [← hM, this]; simp

/-- **The ground energy is bounded below by the signed Cheeger constant**: `μ ≥ h²/(4D)`. -/
theorem le_groundEnergy_of_cheeger [Nonempty ι] {c : ι → ι → ℝ} (hc : IsSymmetricCoupling c)
    {h D : ℝ} (hh0 : 0 ≤ h) (hD0 : 0 < D) (hD : ∀ i, pointDegree c i ≤ D)
    (hh : ∀ s : ι → ℝ, IsSignVector s → ∀ S : Finset ι, h * S.card ≤ signedCutMass s c S) :
    h ^ 2 / (4 * D) ≤ groundEnergy c :=
  le_ciInf fun x => by
    have := sq_mul_le_signedDirichletForm hc hh0 hD hh x.1
    rw [x.2, mul_one] at this
    rw [div_le_iff₀ (by positivity)]
    linarith

/-- The incidence energy is half the Dirichlet form plus the budgets in excess of the degrees. -/
theorem incidenceEnergy_eq_signedDirichletForm {c : ι → ι → ℝ} (hc : IsSymmetricCoupling c)
    (f : ι → ℝ) :
    incidenceEnergy c f =
      ∑ i, (c i i - pointDegree c i) * f i ^ 2 + signedDirichletForm c f / 2 := by
  rw [signedDirichletForm_eq hc]
  unfold incidenceEnergy
  have h : ∀ i, ∑ j, c i j * f i * f j =
      c i i * f i ^ 2 + ∑ j, (if i = j then 0 else c i j * f i * f j) := fun i => by
    have : ∀ j, c i j * f i * f j = (if i = j then c i j * f i * f j else 0) +
        (if i = j then 0 else c i j * f i * f j) := fun j => by split_ifs <;> simp
    rw [sum_congr rfl fun j _ => this j, sum_add_distrib,
      sum_ite_eq univ i (fun j => c i j * f i * f j), if_pos (mem_univ i)]
    ring
  simp_rw [h, sum_add_distrib, sub_mul, sum_sub_distrib]
  ring

/-- **Frustration lowers the budget that positivity needs**: if every budget exceeds its degree
by at least `κ`, then `E(f) ≥ (κ + h²/(8D)) Σ f²`.  For a balanced form `h = 0` and this is local
payment; a frustrated form is nonnegative already when its budgets fall short of the degrees by
`h²/(8D)`. -/
theorem incidenceEnergy_ge_of_cheeger {c : ι → ι → ℝ} (hc : IsSymmetricCoupling c) {h D κ : ℝ}
    (hh0 : 0 ≤ h) (hD0 : 0 < D) (hD : ∀ i, pointDegree c i ≤ D)
    (hh : ∀ s : ι → ℝ, IsSignVector s → ∀ S : Finset ι, h * S.card ≤ signedCutMass s c S)
    (hκ : ∀ i, κ ≤ c i i - pointDegree c i) (f : ι → ℝ) :
    (κ + h ^ 2 / (8 * D)) * ∑ i, f i ^ 2 ≤ incidenceEnergy c f := by
  rw [incidenceEnergy_eq_signedDirichletForm hc]
  have h1 := sq_mul_le_signedDirichletForm hc hh0 hD hh f
  have h2 : κ * ∑ i, f i ^ 2 ≤ ∑ i, (c i i - pointDegree c i) * f i ^ 2 := by
    rw [mul_sum]
    exact sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hκ i) (sq_nonneg _)
  have h3 : h ^ 2 / (8 * D) * ∑ i, f i ^ 2 ≤ signedDirichletForm c f / 2 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith
  linarith

end

end GaloisForLFunctions.ArithmeticOrientationTheory
