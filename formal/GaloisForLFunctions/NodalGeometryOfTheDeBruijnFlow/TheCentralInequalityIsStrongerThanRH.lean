import GaloisForLFunctions.NodalGeometryOfTheDeBruijnFlow.CollisionsBlowUpToHermiteProfiles

/-!
# The central inequality is stronger than RH

The central question of the programme asks for `c > 0` with

`g_t² ≥ c · min(t, log⁻²X)`

for every pair of real zeros of `H_t` near height `X` and every `t > 0` (`CentralInequality`).

* **It excludes collisions** (`deriv_ne_zero_of_centralInequality`, `riemannHypothesis_of_centralInequality`). Above a
  real zero of order `k ≥ 2` two real zeros satisfy `g² ≤ (24/(k+1) + ε)(t − t₀)` near `t₀`, which tends to `0`; the right side
  stays positive when `t₀ > 0`. Holding at all heights, the inequality implies RH.
* **It bounds multiplicities** (`mult_add_one_le_of_centralInequality`). At `t₀ = 0` both sides are linear in `t`, and the
  comparison gives `c (m + 1) ≤ 24` for a real zero of order `m ≥ 2` of `H₀`. So the inequality is stronger than RH: it also
  gives a uniform bound for the multiplicities of the zeros of `ζ`, and no constant `c` survives clusters of unbounded size.

The degeneration of the inequality at `t = 0` is forced: at a zero of order `m` of `H₀` the gaps are `≍ √(t/m)`.
-/

open Complex Filter Topology Set Metric
open GaloisForLFunctions.HTGeometry RHTower RHTower.DeBruijn

namespace GaloisForLFunctions.NodalGeometryOfTheDeBruijnFlow

noncomputable section

/-- **The central inequality** at heights `≥ X₀`, with constant `c`. -/
def CentralInequality (c X₀ : ℝ) : Prop :=
  ∀ t : ℝ, 0 < t → ∀ x y : ℝ, X₀ ≤ |x| → x < y → riemannHeat t (x : ℂ) = 0 → riemannHeat t (y : ℂ) = 0 →
    c * min t (1 / Real.log (2 + |x|) ^ 2) ≤ (y - x) ^ 2

theorem log_two_add_abs_pos (x : ℝ) : 0 < Real.log (2 + |x|) :=
  Real.log_pos (by linarith only [abs_nonneg x])

/-- The scale `1/log²(2 + |y|)` stays bounded below near `x₀`. -/
theorem one_div_log_sq_ge {x₀ y : ℝ} (hy : |y - x₀| ≤ 1) :
    1 / Real.log (3 + |x₀|) ^ 2 ≤ 1 / Real.log (2 + |y|) ^ 2 := by
  have hy' : |y| ≤ |x₀| + 1 := by
    have := abs_add_le (y - x₀) x₀
    rw [sub_add_cancel] at this
    linarith only [this, hy]
  have hlog : Real.log (2 + |y|) ≤ Real.log (3 + |x₀|) :=
    Real.log_le_log (by positivity) (by linarith only [hy'])
  exact one_div_le_one_div_of_le (pow_pos (log_two_add_abs_pos y) 2)
    (pow_le_pow_left₀ (log_two_add_abs_pos y).le hlog 2)

/-- The data of an exact order at a real zero. -/
theorem exists_exact_order {t : ℝ} (ht : 0 ≤ t) {x₀ : ℝ} (h0 : riemannHeat t (x₀ : ℂ) = 0)
    (h1 : deriv (riemannHeat t) (x₀ : ℂ) = 0) :
    ∃ k, 2 ≤ k ∧ (∀ i < k, iteratedDeriv i (riemannHeat t) (x₀ : ℂ) = 0) ∧
      iteratedDeriv k (riemannHeat t) (x₀ : ℂ) ≠ 0 := by
  obtain ⟨hv, hne⟩ := iteratedDeriv_zeroMult_data ht (x₀ : ℂ)
  exact ⟨_, two_le_zeroMult_riemannHeat ht h0 h1, hv, hne⟩

/-- **The central inequality excludes collisions.** -/
theorem deriv_ne_zero_of_centralInequality {c X₀ : ℝ} (hc : 0 < c) (hCI : CentralInequality c X₀)
    {t₀ x₀ : ℝ} (ht₀ : 0 < t₀) (hx₀ : X₀ < |x₀|) (h0 : riemannHeat t₀ (x₀ : ℂ) = 0) :
    deriv (riemannHeat t₀) (x₀ : ℂ) ≠ 0 := by
  intro h1
  obtain ⟨k, hk, hvan, ha⟩ := exists_exact_order ht₀.le h0 h1
  obtain ⟨q₁, hq₁, hclose⟩ := exists_close_zeros_forward ht₀.le hk hvan ha one_pos
  set S := ∑ ρ ∈ profileRoots k, |ρ| + 2 with hS
  have hSpos : 0 < S := by
    have : 0 ≤ ∑ ρ ∈ profileRoots k, |ρ| := Finset.sum_nonneg fun _ _ => abs_nonneg _
    linarith only [this]
  set b := min t₀ (1 / Real.log (3 + |x₀|) ^ 2) with hb
  have hbpos : 0 < b := lt_min ht₀ (by
    have : 0 < Real.log (3 + |x₀|) := Real.log_pos (by linarith only [abs_nonneg x₀])
    positivity)
  set A := 24 / ((k : ℝ) + 1) + 1 with hA
  have hApos : 0 < A := by positivity
  set q := min q₁ (min ((|x₀| - X₀) / S) (min (1 / S) (Real.sqrt (c * b / (2 * A))))) with hq
  have hsqrt : 0 < Real.sqrt (c * b / (2 * A)) := Real.sqrt_pos.mpr (by positivity)
  have hqpos : 0 < q := lt_min hq₁ (lt_min (div_pos (sub_pos.mpr hx₀) hSpos)
    (lt_min (by positivity) hsqrt))
  obtain ⟨y, y', hyy, hy0, hy0', hdist, hgap⟩ := hclose q hqpos (min_le_left _ _)
  have hq2 : q ≤ (|x₀| - X₀) / S := (min_le_right _ _).trans (min_le_left _ _)
  have hq3 : q ≤ 1 / S := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hq4 : q ≤ Real.sqrt (c * b / (2 * A)) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hSq1 : S * q ≤ |x₀| - X₀ := by
    have := (le_div_iff₀ hSpos).mp hq2
    linarith only [this]
  have hSq2 : S * q ≤ 1 := by
    have := (le_div_iff₀ hSpos).mp hq3
    linarith only [this]
  have hd : |y - x₀| + |y' - x₀| ≤ S * q := hdist
  have hy1 : |y - x₀| ≤ S * q := by linarith only [hd, abs_nonneg (y' - x₀)]
  have hyabs : X₀ ≤ |y| := by
    have := abs_sub_abs_le_abs_sub x₀ y
    rw [abs_sub_comm x₀ y] at this
    linarith only [this, hy1, hSq1]
  have hlaw := hCI (t₀ + q ^ 2) (by positivity) y y' hyabs hyy hy0 hy0'
  have hmin : b ≤ min (t₀ + q ^ 2) (1 / Real.log (2 + |y|) ^ 2) := by
    refine le_min ((min_le_left _ _).trans ?_) ((min_le_right _ _).trans ?_)
    · nlinarith only [sq_nonneg q]
    · exact one_div_log_sq_ge (hy1.trans hSq2)
  have hlower : c * b ≤ (y' - y) ^ 2 := (mul_le_mul_of_nonneg_left hmin hc.le).trans hlaw
  have hgap' : (y' - y) ^ 2 ≤ A * q ^ 2 := hgap
  have hq5 : q ^ 2 ≤ c * b / (2 * A) := by
    have := pow_le_pow_left₀ hqpos.le hq4 2
    rwa [Real.sq_sqrt (by positivity)] at this
  have hA2 : A * q ^ 2 ≤ c * b / 2 := by
    have := mul_le_mul_of_nonneg_left hq5 hApos.le
    have heq : A * (c * b / (2 * A)) = c * b / 2 := by
      field_simp
    linarith only [this, heq]
  have hcb : 0 < c * b := by positivity
  linarith only [hlower, hgap', hA2, hcb]

/-- **The central inequality at all heights implies RH.** -/
theorem riemannHypothesis_of_centralInequality {c X₀ : ℝ} (hc : 0 < c) (hX₀ : X₀ < 0)
    (hCI : CentralInequality c X₀) : RiemannHypothesis := by
  rw [riemannHypothesis_iff_forall_collisionMass_eq_zero]
  intro t ht
  rcases le_or_gt t (1 / 8) with ht8 | ht8
  · rw [collisionMass]
    refine Finset.sum_eq_zero fun z hz => ?_
    obtain ⟨h0, him, h1⟩ := (mem_realMultipleZeros ht ht8).mp hz
    have hzr : z = ((z.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [him])
    rw [hzr] at h0 h1
    exact absurd h1 (deriv_ne_zero_of_centralInequality hc hCI ht
      (hX₀.trans_le (abs_nonneg z.re)) h0)
  · exact collisionMass_eq_zero_of_eighth_le ht8.le

/-- **The central inequality bounds multiplicities.** A real zero of order `m ≥ 2` of `H₀` above height `X₀` has
`c (m + 1) ≤ 24`. -/
theorem mult_add_one_le_of_centralInequality {c X₀ : ℝ} (hc : 0 < c) (hCI : CentralInequality c X₀)
    {x₀ : ℝ} (hx₀ : X₀ < |x₀|) {m : ℕ} (hm : 2 ≤ m)
    (hvan : ∀ i < m, iteratedDeriv i (riemannHeat 0) (x₀ : ℂ) = 0)
    (ha : iteratedDeriv m (riemannHeat 0) (x₀ : ℂ) ≠ 0) : c * ((m : ℝ) + 1) ≤ 24 := by
  by_contra hcon
  have hgt : 24 < c * ((m : ℝ) + 1) := not_le.mp hcon
  have hm1 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  set ε := (c - 24 / ((m : ℝ) + 1)) / 2 with hε
  have hcdiv : 24 / ((m : ℝ) + 1) < c := by
    rw [div_lt_iff₀ hm1]
    exact hgt
  have hεpos : 0 < ε := by rw [hε]; linarith only [hcdiv]
  obtain ⟨q₁, hq₁, hclose⟩ := exists_close_zeros_forward le_rfl hm hvan ha hεpos
  set S := ∑ ρ ∈ profileRoots m, |ρ| + 2 with hS
  have hSpos : 0 < S := by
    have : 0 ≤ ∑ ρ ∈ profileRoots m, |ρ| := Finset.sum_nonneg fun _ _ => abs_nonneg _
    linarith only [this]
  have hlogpos : 0 < Real.log (3 + |x₀|) := Real.log_pos (by linarith only [abs_nonneg x₀])
  set q := min q₁ (min ((|x₀| - X₀) / S) (min (1 / S) (1 / Real.log (3 + |x₀|)))) with hq
  have hqpos : 0 < q := lt_min hq₁ (lt_min (div_pos (sub_pos.mpr hx₀) hSpos)
    (lt_min (by positivity) (by positivity)))
  obtain ⟨y, y', hyy, hy0, hy0', hdist, hgap⟩ := hclose q hqpos (min_le_left _ _)
  have hq2 : q ≤ (|x₀| - X₀) / S := (min_le_right _ _).trans (min_le_left _ _)
  have hq3 : q ≤ 1 / S := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hq4 : q ≤ 1 / Real.log (3 + |x₀|) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hSq1 : S * q ≤ |x₀| - X₀ := by
    have := (le_div_iff₀ hSpos).mp hq2
    linarith only [this]
  have hSq2 : S * q ≤ 1 := by
    have := (le_div_iff₀ hSpos).mp hq3
    linarith only [this]
  have hd : |y - x₀| + |y' - x₀| ≤ S * q := hdist
  have hy1 : |y - x₀| ≤ S * q := by linarith only [hd, abs_nonneg (y' - x₀)]
  have hyabs : X₀ ≤ |y| := by
    have := abs_sub_abs_le_abs_sub x₀ y
    rw [abs_sub_comm x₀ y] at this
    linarith only [this, hy1, hSq1]
  have hq2pos : 0 < q ^ 2 := by positivity
  have hlaw := hCI (0 + q ^ 2) (by simpa using hq2pos) y y' hyabs hyy hy0 hy0'
  rw [zero_add] at hlaw
  have hmin : q ^ 2 ≤ min (q ^ 2) (1 / Real.log (2 + |y|) ^ 2) := by
    refine le_min le_rfl (le_trans ?_ (one_div_log_sq_ge (hy1.trans hSq2)))
    have := pow_le_pow_left₀ hqpos.le hq4 2
    rwa [div_pow, one_pow] at this
  have hlower : c * q ^ 2 ≤ (y' - y) ^ 2 := (mul_le_mul_of_nonneg_left hmin hc.le).trans hlaw
  have hupper := hlower.trans hgap
  have hle := le_of_mul_le_mul_right hupper hq2pos
  rw [hε] at hle
  linarith only [hle, hcdiv]

end

end GaloisForLFunctions.NodalGeometryOfTheDeBruijnFlow
