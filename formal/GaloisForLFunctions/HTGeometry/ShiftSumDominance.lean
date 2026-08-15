import GaloisForLFunctions.HTGeometry.ShiftTermUnifiedBound
import GaloisForLFunctions.HTGeometry.NewtonIrrationalUniformGap

/-!
# Every shift but the leading one is negligible in a coefficient recursion

Read at index `n`, a convergent Euler-form operator applied to a series with a factorial profile of
exponent `s` produces one term per shift.  Measured against the leading shift `ν`, the shifts at most
half the index are controlled by a single geometric-times-power bound, and the shifts past the
halfway point by a factorial bound that does not depend on the shift at all.

Summing the first over all shifts costs a factor `ν + 2` — the shifts below `ν` are finitely many
and the ones above form a geometric series of ratio at most `1/2`.  Summing the second costs a factor
`n + 1`, which the factorial ratio absorbs.  Both totals tend to zero, so the whole tail of the
recursion is negligible against its leading term.
-/

open Filter Topology
open scoped Nat

namespace GaloisForLFunctions.HTGeometry

theorem geomSum_le_two {q : ℝ} (hq0 : 0 ≤ q) (hq : q ≤ 1 / 2) (k : ℕ) :
    ∑ j ∈ Finset.range k, q ^ j ≤ 2 := by
  have hstep : ∑ j ∈ Finset.range k, q ^ j ≤ ∑ j ∈ Finset.range k, (1 / 2 : ℝ) ^ j :=
    Finset.sum_le_sum fun j _ => pow_le_pow_left₀ hq0 hq j
  refine le_trans hstep ?_
  have hval : ∑ j ∈ Finset.range k, (1 / 2 : ℝ) ^ j = ((1 / 2 : ℝ) ^ k - 1) / ((1 / 2 : ℝ) - 1) :=
    geom_sum_eq (by norm_num) k
  rw [hval]
  have hpk : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ k := by positivity
  have hrw : ((1 / 2 : ℝ) ^ k - 1) / ((1 / 2 : ℝ) - 1) = 2 - 2 * (1 / 2 : ℝ) ^ k := by
    rw [show ((1 : ℝ) / 2 - 1) = -(1 / 2) by norm_num]
    field_simp
    ring
  rw [hrw]
  linarith

/-- **The tail of a coefficient recursion is negligible against its leading shift.** -/
theorem tendsto_shiftTail_div_leading {m : ℕ} {Φ : ℕ → Polynomial ℂ} {C ρ s c₁ c₂ : ℝ}
    {Θ : ℕ → ℝ} (hC : 0 < C) (hρ : 0 < ρ) (hs : 0 < s)
    (hdeg : ∀ μ, (Φ μ).natDegree ≤ m)
    (hbd : ∀ μ k : ℕ, ‖(Φ μ).eval ((k : ℕ) : ℂ)‖ ≤ C * ρ ^ μ * (((k : ℝ)) + 1) ^ (Φ μ).natDegree)
    (hprof : IsRegularFactorialProfile s c₁ c₂ Θ)
    {ν : ℕ} (hmax : ∀ μ, Φ μ ≠ 0 → μ ≠ ν → weightedLevel s Φ μ < weightedLevel s Φ ν) :
    Tendsto (fun n : ℕ => (∑ μ ∈ (Finset.range (n + 1)).erase ν,
        ‖(Φ μ).eval (((n - μ : ℕ) : ℕ) : ℂ)‖ * Θ (n - μ))
        / (((n : ℝ) + 1) ^ (((Φ ν).natDegree : ℕ) : ℝ) * Θ (n - ν))) atTop (𝓝 0) := by
  classical
  obtain ⟨γ, hγ, hgap⟩ := exists_uniform_weightedLevel_gap hs hdeg hmax
  have hmγ : (0 : ℝ) < (m : ℝ) + γ := by
    have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  set ε : ℝ := γ / (2 * ((m : ℝ) + γ)) with hεdef
  have hεpos : 0 < ε := by rw [hεdef]; positivity
  have hεle : ε ≤ 1 := by
    rw [hεdef, div_le_one (by linarith)]
    have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  have hεkey : ε * ((m : ℝ) + γ) = γ / 2 := by
    rw [hεdef]
    field_simp
  have h2s : (1 : ℝ) ≤ (2 : ℝ) ^ s := Real.one_le_rpow (by norm_num) hs.le
  have hmax1c : (1 : ℝ) ≤ max 1 (1 / c₁) := le_max_left _ _
  have hmax1c₂ : (1 : ℝ) ≤ max 1 c₂ := le_max_left _ _
  have hmax1ρ : (1 : ℝ) ≤ max 1 ρ := le_max_left _ _
  set a : ℝ := ρ * max 1 (1 / c₁) * (2 : ℝ) ^ s with hadef
  have hapos : 0 < a := by
    rw [hadef]
    have h1 : (0 : ℝ) < (2 : ℝ) ^ s := Real.rpow_pos_of_pos (by norm_num) s
    have h2 : (0 : ℝ) < max 1 (1 / c₁) := lt_of_lt_of_le zero_lt_one hmax1c
    exact mul_pos (mul_pos hρ h2) h1
  have hamax : (1 : ℝ) ≤ max 1 a := le_max_left _ _
  set K₁ : ℝ := C * max 1 c₂ ^ ν * max 1 a ^ ν with hK₁def
  have hK₁0 : (0 : ℝ) ≤ K₁ := by
    rw [hK₁def]
    exact mul_nonneg (mul_nonneg hC.le (pow_nonneg (le_trans zero_le_one hmax1c₂) ν))
      (pow_nonneg (le_trans zero_le_one hamax) ν)
  set κ : ℝ := max 1 ρ * max 1 (1 / c₁) with hκdef
  have hκ1 : (1 : ℝ) ≤ κ := by
    rw [hκdef]
    nlinarith [hmax1ρ, hmax1c]
  set E : ℕ → ℝ := fun n => K₁ * (((ν : ℝ)) + 2) * (((n : ℝ) + 1) ^ (-(γ / 2)))
      + C * (((n : ℝ) + 1) ^ (m + 1) * κ ^ n *
        ((((n / 2)! : ℕ) : ℝ) / (((n - ν)! : ℕ) : ℝ)) ^ s) with hEdef
  have hEtendsto : Tendsto E atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => K₁ * (((ν : ℝ)) + 2) * (((n : ℝ) + 1) ^ (-(γ / 2)))) atTop
        (𝓝 0) := by
      have h := (tendsto_rpow_neg_succ (by linarith : (0 : ℝ) < γ / 2)).const_mul
        (K₁ * (((ν : ℝ)) + 2))
      simpa using h
    have h2 : Tendsto (fun n : ℕ => C * (((n : ℝ) + 1) ^ (m + 1) * κ ^ n *
        ((((n / 2)! : ℕ) : ℝ) / (((n - ν)! : ℕ) : ℝ)) ^ s)) atTop (𝓝 0) := by
      have h := (tendsto_halfFactorial_ratio_mul hs hκ1 (m + 1) ν).const_mul C
      simpa using h
    rw [hEdef]
    simpa using h1.add h2
  have hbound : ∀ᶠ n : ℕ in atTop,
      (∑ μ ∈ (Finset.range (n + 1)).erase ν,
        ‖(Φ μ).eval (((n - μ : ℕ) : ℕ) : ℂ)‖ * Θ (n - μ))
        / (((n : ℝ) + 1) ^ (((Φ ν).natDegree : ℕ) : ℝ) * Θ (n - ν)) ≤ E n := by
    have hqlim : Tendsto (fun n : ℕ => a * ((n : ℝ) + 1) ^ (-(ε * s))) atTop (𝓝 0) := by
      have h := (tendsto_rpow_neg_succ (by positivity : (0 : ℝ) < ε * s)).const_mul a
      simpa using h
    have hq : ∀ᶠ n : ℕ in atTop, a * ((n : ℝ) + 1) ^ (-(ε * s)) ≤ 1 / 2 := by
      have hmem : {x : ℝ | x < 1 / 2} ∈ 𝓝 (0 : ℝ) := gt_mem_nhds (by norm_num)
      filter_upwards [hqlim hmem] with n hn
      exact le_of_lt hn
    filter_upwards [hq, eventually_ge_atTop (2 * ν)] with n hqn h2ν
    have hνn : ν ≤ n := by omega
    set q : ℝ := a * ((n : ℝ) + 1) ^ (-(ε * s)) with hqdef
    have hq0 : (0 : ℝ) ≤ q := by
      rw [hqdef]
      exact mul_nonneg hapos.le (Real.rpow_nonneg (by positivity) _)
    have hbase0 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hDpos : (0 : ℝ) < ((n : ℝ) + 1) ^ (((Φ ν).natDegree : ℕ) : ℝ) * Θ (n - ν) :=
      mul_pos (Real.rpow_pos_of_pos hbase0 _) (hprof.pos (n - ν))
    rw [div_le_iff₀ hDpos]
    -- split the shifts at the halfway point
    have hsplit := Finset.sum_filter_add_sum_filter_not ((Finset.range (n + 1)).erase ν)
      (fun μ => 2 * μ ≤ n)
      (fun μ => ‖(Φ μ).eval (((n - μ : ℕ) : ℕ) : ℂ)‖ * Θ (n - μ))
    rw [← hsplit]
    -- the near half
    have hnear : ∑ μ ∈ ((Finset.range (n + 1)).erase ν).filter (fun μ => 2 * μ ≤ n),
        ‖(Φ μ).eval (((n - μ : ℕ) : ℕ) : ℂ)‖ * Θ (n - μ)
        ≤ K₁ * (((ν : ℝ)) + 2) * ((n : ℝ) + 1) ^ (-(γ / 2)) *
          (((n : ℝ) + 1) ^ (((Φ ν).natDegree : ℕ) : ℝ) * Θ (n - ν)) := by
      have hterm : ∀ μ ∈ ((Finset.range (n + 1)).erase ν).filter (fun μ => 2 * μ ≤ n),
          ‖(Φ μ).eval (((n - μ : ℕ) : ℕ) : ℂ)‖ * Θ (n - μ)
            ≤ (K₁ * ((n : ℝ) + 1) ^ (-(γ / 2)) *
              (((n : ℝ) + 1) ^ (((Φ ν).natDegree : ℕ) : ℝ) * Θ (n - ν))) * q ^ (μ - ν) := by
        intro μ hμ
        rw [Finset.mem_filter] at hμ
        have hμν : μ ≠ ν := Finset.ne_of_mem_erase hμ.1
        by_cases hΦ : Φ μ = 0
        · rw [hΦ]
          simp only [Polynomial.eval_zero, norm_zero, zero_mul]
          have : (0 : ℝ) ≤ K₁ * ((n : ℝ) + 1) ^ (-(γ / 2)) *
              (((n : ℝ) + 1) ^ (((Φ ν).natDegree : ℕ) : ℝ) * Θ (n - ν)) :=
            mul_nonneg (mul_nonneg hK₁0 (Real.rpow_nonneg hbase0.le _)) hDpos.le
          exact mul_nonneg this (pow_nonneg hq0 _)
        · have h := shiftTerm_le_unified hC hρ hs hdeg hbd hprof hgap hγ hεpos hεle hεkey
            hadef hK₁def hΦ hμν hμ.2 hνn
          rw [hqdef]
          calc ‖(Φ μ).eval (((n - μ : ℕ) : ℕ) : ℂ)‖ * Θ (n - μ)
              ≤ K₁ * (a * ((n : ℝ) + 1) ^ (-(ε * s))) ^ (μ - ν) * ((n : ℝ) + 1) ^ (-(γ / 2)) *
                (((n : ℝ) + 1) ^ (((Φ ν).natDegree : ℕ) : ℝ) * Θ (n - ν)) := h
            _ = (K₁ * ((n : ℝ) + 1) ^ (-(γ / 2)) *
                  (((n : ℝ) + 1) ^ (((Φ ν).natDegree : ℕ) : ℝ) * Θ (n - ν))) *
                (a * ((n : ℝ) + 1) ^ (-(ε * s))) ^ (μ - ν) := by ring
      refine le_trans (Finset.sum_le_sum hterm) ?_
      rw [← Finset.mul_sum]
      have hgeo : ∑ μ ∈ ((Finset.range (n + 1)).erase ν).filter (fun μ => 2 * μ ≤ n),
          q ^ (μ - ν) ≤ ((ν : ℝ)) + 2 := by
        set A : Finset ℕ := ((Finset.range (n + 1)).erase ν).filter (fun μ => 2 * μ ≤ n) with hA
        have hsp := Finset.sum_filter_add_sum_filter_not A (fun μ => ν ≤ μ)
          (fun μ => q ^ (μ - ν))
        rw [← hsp]
        have hlow : ∑ μ ∈ A.filter (fun μ => ¬ ν ≤ μ), q ^ (μ - ν) ≤ ((ν : ℝ)) := by
          have hone : ∀ μ ∈ A.filter (fun μ => ¬ ν ≤ μ), q ^ (μ - ν) = 1 := by
            intro μ hμ
            rw [Finset.mem_filter] at hμ
            have : μ - ν = 0 := by omega
            rw [this, pow_zero]
          rw [Finset.sum_congr rfl hone, Finset.sum_const, nsmul_eq_mul, mul_one]
          have hsub : A.filter (fun μ => ¬ ν ≤ μ) ⊆ Finset.range ν := by
            intro μ hμ
            rw [Finset.mem_filter] at hμ
            exact Finset.mem_range.mpr (by omega)
          have hcard : (A.filter (fun μ => ¬ ν ≤ μ)).card ≤ ν := by
            have := Finset.card_le_card hsub
            simpa using this
          exact_mod_cast hcard
        have hhigh : ∑ μ ∈ A.filter (fun μ => ν ≤ μ), q ^ (μ - ν) ≤ 2 := by
          have hinj : ∀ x ∈ A.filter (fun μ => ν ≤ μ), ∀ y ∈ A.filter (fun μ => ν ≤ μ),
              x - ν = y - ν → x = y := by
            intro x hx y hy hxy
            rw [Finset.mem_filter] at hx hy
            omega
          have himg : ∑ j ∈ (A.filter (fun μ => ν ≤ μ)).image (fun μ => μ - ν), q ^ j
              = ∑ μ ∈ A.filter (fun μ => ν ≤ μ), q ^ (μ - ν) := Finset.sum_image hinj
          rw [← himg]
          have hsub : (A.filter (fun μ => ν ≤ μ)).image (fun μ => μ - ν) ⊆
              Finset.range (n + 1) := by
            intro j hj
            rw [Finset.mem_image] at hj
            obtain ⟨μ, hμ, rfl⟩ := hj
            rw [Finset.mem_filter, hA, Finset.mem_filter] at hμ
            have hμn : μ ≤ n := Nat.lt_succ_iff.mp
              (Finset.mem_range.mp (Finset.mem_of_mem_erase hμ.1.1))
            exact Finset.mem_range.mpr (by omega)
          refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub ?_) ?_
          · intro j _ _
            exact pow_nonneg hq0 j
          · exact geomSum_le_two hq0 hqn (n + 1)
        linarith
      have hpos : (0 : ℝ) ≤ K₁ * ((n : ℝ) + 1) ^ (-(γ / 2)) *
          (((n : ℝ) + 1) ^ (((Φ ν).natDegree : ℕ) : ℝ) * Θ (n - ν)) :=
        mul_nonneg (mul_nonneg hK₁0 (Real.rpow_nonneg hbase0.le _)) hDpos.le
      calc (K₁ * ((n : ℝ) + 1) ^ (-(γ / 2)) *
            (((n : ℝ) + 1) ^ (((Φ ν).natDegree : ℕ) : ℝ) * Θ (n - ν))) *
            ∑ μ ∈ ((Finset.range (n + 1)).erase ν).filter (fun μ => 2 * μ ≤ n), q ^ (μ - ν)
          ≤ (K₁ * ((n : ℝ) + 1) ^ (-(γ / 2)) *
              (((n : ℝ) + 1) ^ (((Φ ν).natDegree : ℕ) : ℝ) * Θ (n - ν))) * (((ν : ℝ)) + 2) :=
            mul_le_mul_of_nonneg_left hgeo hpos
        _ = K₁ * (((ν : ℝ)) + 2) * ((n : ℝ) + 1) ^ (-(γ / 2)) *
              (((n : ℝ) + 1) ^ (((Φ ν).natDegree : ℕ) : ℝ) * Θ (n - ν)) := by ring
    -- the far half
    have hfar : ∑ μ ∈ ((Finset.range (n + 1)).erase ν).filter (fun μ => ¬ (2 * μ ≤ n)),
        ‖(Φ μ).eval (((n - μ : ℕ) : ℕ) : ℂ)‖ * Θ (n - μ)
        ≤ C * (((n : ℝ) + 1) ^ (m + 1) * κ ^ n *
            ((((n / 2)! : ℕ) : ℝ) / (((n - ν)! : ℕ) : ℝ)) ^ s) *
          (((n : ℝ) + 1) ^ (((Φ ν).natDegree : ℕ) : ℝ) * Θ (n - ν)) := by
      have hΘle : Θ (n - ν) ≤ ((n : ℝ) + 1) ^ (((Φ ν).natDegree : ℕ) : ℝ) * Θ (n - ν) := by
        have h1 : (1 : ℝ) ≤ ((n : ℝ) + 1) ^ (((Φ ν).natDegree : ℕ) : ℝ) :=
          Real.one_le_rpow (by linarith) (Nat.cast_nonneg _)
        nlinarith [hprof.pos (n - ν), h1]
      have hterm : ∀ μ ∈ ((Finset.range (n + 1)).erase ν).filter (fun μ => ¬ (2 * μ ≤ n)),
          ‖(Φ μ).eval (((n - μ : ℕ) : ℕ) : ℂ)‖ * Θ (n - μ)
            ≤ C * κ ^ n * (((n : ℝ) + 1) ^ m *
                ((((n / 2)! : ℕ) : ℝ) / (((n - ν)! : ℕ) : ℝ)) ^ s) *
              (((n : ℝ) + 1) ^ (((Φ ν).natDegree : ℕ) : ℝ) * Θ (n - ν)) := by
        intro μ hμ
        rw [Finset.mem_filter] at hμ
        have hμn : μ ≤ n := Nat.lt_succ_iff.mp
          (Finset.mem_range.mp (Finset.mem_of_mem_erase hμ.1))
        have hhi : n < 2 * μ := by omega
        have hνμ : ν ≤ μ := by omega
        have h := shiftTerm_le_factorial (m := m) hC hρ hs hdeg hbd hprof hνμ hμn hhi
        have hκpow : (max 1 ρ) ^ n * (max 1 (1 / c₁)) ^ n = κ ^ n := by
          rw [hκdef, mul_pow]
        refine le_trans h ?_
        rw [mul_assoc C ((max 1 ρ) ^ n) ((max 1 (1 / c₁)) ^ n), hκpow]
        have hcoef0 : (0 : ℝ) ≤ C * κ ^ n :=
          mul_nonneg hC.le (pow_nonneg (le_trans zero_le_one hκ1) n)
        have hfac0 : (0 : ℝ) ≤ ((n : ℝ) + 1) ^ m *
            ((((n / 2)! : ℕ) : ℝ) / (((n - ν)! : ℕ) : ℝ)) ^ s := by positivity
        calc C * κ ^ n * (((n : ℝ) + 1) ^ m *
              ((((n / 2)! : ℕ) : ℝ) / (((n - ν)! : ℕ) : ℝ)) ^ s * Θ (n - ν))
            = (C * κ ^ n * (((n : ℝ) + 1) ^ m *
                ((((n / 2)! : ℕ) : ℝ) / (((n - ν)! : ℕ) : ℝ)) ^ s)) * Θ (n - ν) := by ring
          _ ≤ (C * κ ^ n * (((n : ℝ) + 1) ^ m *
                ((((n / 2)! : ℕ) : ℝ) / (((n - ν)! : ℕ) : ℝ)) ^ s)) *
              (((n : ℝ) + 1) ^ (((Φ ν).natDegree : ℕ) : ℝ) * Θ (n - ν)) :=
            mul_le_mul_of_nonneg_left hΘle (mul_nonneg hcoef0 hfac0)
      refine le_trans (Finset.sum_le_sum hterm) ?_
      rw [Finset.sum_const, nsmul_eq_mul]
      have hcard : ((((Finset.range (n + 1)).erase ν).filter
          (fun μ => ¬ (2 * μ ≤ n))).card : ℝ) ≤ (n : ℝ) + 1 := by
        have h1 : (((Finset.range (n + 1)).erase ν).filter (fun μ => ¬ (2 * μ ≤ n))).card
            ≤ n + 1 := by
          refine le_trans (Finset.card_le_card (Finset.filter_subset _ _)) ?_
          refine le_trans (Finset.card_le_card (Finset.erase_subset _ _)) ?_
          simp
        have h2 : ((((Finset.range (n + 1)).erase ν).filter
            (fun μ => ¬ (2 * μ ≤ n))).card : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := Nat.cast_le.mpr h1
        push_cast at h2
        linarith
      have hrest0 : (0 : ℝ) ≤ C * κ ^ n * (((n : ℝ) + 1) ^ m *
          ((((n / 2)! : ℕ) : ℝ) / (((n - ν)! : ℕ) : ℝ)) ^ s) *
          (((n : ℝ) + 1) ^ (((Φ ν).natDegree : ℕ) : ℝ) * Θ (n - ν)) := by
        have hcoef0 : (0 : ℝ) ≤ C * κ ^ n :=
          mul_nonneg hC.le (pow_nonneg (le_trans zero_le_one hκ1) n)
        have hfac0 : (0 : ℝ) ≤ ((n : ℝ) + 1) ^ m *
            ((((n / 2)! : ℕ) : ℝ) / (((n - ν)! : ℕ) : ℝ)) ^ s := by positivity
        exact mul_nonneg (mul_nonneg hcoef0 hfac0) hDpos.le
      calc ((((Finset.range (n + 1)).erase ν).filter (fun μ => ¬ (2 * μ ≤ n))).card : ℝ) *
            (C * κ ^ n * (((n : ℝ) + 1) ^ m *
              ((((n / 2)! : ℕ) : ℝ) / (((n - ν)! : ℕ) : ℝ)) ^ s) *
              (((n : ℝ) + 1) ^ (((Φ ν).natDegree : ℕ) : ℝ) * Θ (n - ν)))
          ≤ ((n : ℝ) + 1) * (C * κ ^ n * (((n : ℝ) + 1) ^ m *
              ((((n / 2)! : ℕ) : ℝ) / (((n - ν)! : ℕ) : ℝ)) ^ s) *
              (((n : ℝ) + 1) ^ (((Φ ν).natDegree : ℕ) : ℝ) * Θ (n - ν))) :=
            mul_le_mul_of_nonneg_right hcard hrest0
        _ = C * (((n : ℝ) + 1) ^ (m + 1) * κ ^ n *
              ((((n / 2)! : ℕ) : ℝ) / (((n - ν)! : ℕ) : ℝ)) ^ s) *
              (((n : ℝ) + 1) ^ (((Φ ν).natDegree : ℕ) : ℝ) * Θ (n - ν)) := by
            rw [pow_succ]
            ring
    rw [hEdef]
    simp only
    rw [add_mul]
    exact add_le_add hnear hfar
  refine squeeze_zero' ?_ hbound hEtendsto
  filter_upwards [eventually_ge_atTop ν] with n hνn
  have hbase0 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hD : (0 : ℝ) < ((n : ℝ) + 1) ^ (((Φ ν).natDegree : ℕ) : ℝ) * Θ (n - ν) :=
    mul_pos (Real.rpow_pos_of_pos hbase0 _) (hprof.pos (n - ν))
  refine div_nonneg ?_ hD.le
  exact Finset.sum_nonneg fun μ _ => mul_nonneg (norm_nonneg _) (hprof.pos (n - μ)).le

end GaloisForLFunctions.HTGeometry
