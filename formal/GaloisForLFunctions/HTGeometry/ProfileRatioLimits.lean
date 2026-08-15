import GaloisForLFunctions.HTGeometry.BarnesTailLinearObstruction

/-!
# Two quotients that vanish against a leading profile term

Reading a coefficient recursion at the leading Newton vertex compares everything else in the
recursion with `(n+1)^{deg Φ_ν} Θ(n−ν)`.  Two sources have to be shown negligible.

* A **convergent** right-hand side.  Its coefficients grow geometrically, and the profile beats
  every geometric growth by a factorial power.
* A term carrying the profile **shifted by the truncation order**, `Θ(N+1) Θ(n−N−1)`, times a fixed
  power of the index.  Moving one profile argument from `n−N−1` up to `n−ν` costs a factor
  `c₁^{N+1−ν} (n−N)^{s(N+1−ν)}`, so past the halfway point the quotient is a constant times
  `(n+1)^{A−d−s(N+1−ν)}`: negative exponent as soon as the truncation order is taken far enough
  beyond the vertex.
-/

open Filter Topology
open scoped Nat

namespace GaloisForLFunctions.HTGeometry

variable {s c₁ c₂ : ℝ} {Θ : ℕ → ℝ}

/-- **A convergent series is negligible against a leading profile term.** -/
theorem tendsto_convergent_div_leading (hprof : IsRegularFactorialProfile s c₁ c₂ Θ)
    (hs : 0 < s) {G : PowerSeries ℂ} (hG : IsGevreySeries 0 G) (d ν : ℕ) :
    Tendsto (fun n : ℕ => ‖PowerSeries.coeff n G‖ /
      (((n : ℝ) + 1) ^ ((d : ℕ) : ℝ) * Θ (n - ν))) atTop (𝓝 0) := by
  have hΘpos : ∀ k, 0 < Θ k := hprof.pos
  have hZpos : ∀ n : ℕ, (0 : ℝ) < ((n : ℝ) + 1) ^ ((d : ℕ) : ℝ) * Θ (n - ν) := fun n =>
    mul_pos (Real.rpow_pos_of_pos (by positivity) _) (hΘpos (n - ν))
  obtain ⟨CG, AG, hCG, hAG, hGbd⟩ := hG
  set b : ℝ := min 1 c₁ with hbdef
  have hbpos : (0 : ℝ) < b := by
    rw [hbdef]
    exact lt_min zero_lt_one hprof.c₁_pos
  have hmaj := (tendsto_geom_mul_factorial_rpow_neg hs (div_pos hAG hbpos) ν).const_mul (CG / Θ 0)
  rw [mul_zero] at hmaj
  refine squeeze_zero' (Eventually.of_forall fun n => ?_) (Eventually.of_forall fun n => ?_) hmaj
  · exact div_nonneg (norm_nonneg _) (hZpos n).le
  · have hone : (1 : ℝ) ≤ ((n : ℝ) + 1) ^ ((d : ℕ) : ℝ) := by
      refine Real.one_le_rpow ?_ (Nat.cast_nonneg _)
      have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    have hΘ0 : (0 : ℝ) < Θ 0 := hΘpos 0
    have hFpos : (0 : ℝ) < ((((n - ν)! : ℕ) : ℝ)) ^ s :=
      Real.rpow_pos_of_pos (Nat.cast_pos.mpr (Nat.factorial_pos _)) _
    have hbn : (0 : ℝ) < b ^ n := pow_pos hbpos n
    have hbc : b ^ n ≤ c₁ ^ (n - ν) := by
      rcases le_total 1 c₁ with h | h
      · rw [hbdef, min_eq_left h, one_pow]
        exact one_le_pow₀ h
      · rw [hbdef, min_eq_right h]
        exact pow_le_pow_of_le_one hprof.c₁_pos.le h (Nat.sub_le n ν)
    have hblock := hprof.block_lower (Nat.zero_le (n - ν))
    have hfac0 : ((Nat.factorial 0 : ℕ) : ℝ) = 1 := by norm_num
    rw [hfac0, div_one, Nat.sub_zero] at hblock
    have hchain : Θ 0 * b ^ n * ((((n - ν)! : ℕ) : ℝ)) ^ s
        ≤ ((n : ℝ) + 1) ^ ((d : ℕ) : ℝ) * Θ (n - ν) := by
      have h1 : Θ 0 * b ^ n * ((((n - ν)! : ℕ) : ℝ)) ^ s
          ≤ Θ 0 * c₁ ^ (n - ν) * ((((n - ν)! : ℕ) : ℝ)) ^ s := by
        refine mul_le_mul_of_nonneg_right ?_ hFpos.le
        exact mul_le_mul_of_nonneg_left hbc hΘ0.le
      have h2 : Θ (n - ν) ≤ ((n : ℝ) + 1) ^ ((d : ℕ) : ℝ) * Θ (n - ν) := by
        nlinarith [hΘpos (n - ν), hone]
      linarith [h1, hblock, h2]
    have hMnn : (0 : ℝ) ≤ CG / Θ 0 * ((AG / b) ^ n * ((((n - ν)! : ℕ) : ℝ)) ^ (-s)) := by
      have h1 : (0 : ℝ) ≤ (AG / b) ^ n := by positivity
      have h2 : (0 : ℝ) ≤ ((((n - ν)! : ℕ) : ℝ)) ^ (-s) := Real.rpow_nonneg (Nat.cast_nonneg _) _
      have h3 : (0 : ℝ) ≤ CG / Θ 0 := by positivity
      exact mul_nonneg h3 (mul_nonneg h1 h2)
    have hGn : ‖PowerSeries.coeff n G‖ ≤ CG * AG ^ n := by
      have h := hGbd n
      simpa using h
    rw [div_le_iff₀ (hZpos n)]
    have hval : CG * AG ^ n
        = (CG / Θ 0 * ((AG / b) ^ n * ((((n - ν)! : ℕ) : ℝ)) ^ (-s))) *
          (Θ 0 * b ^ n * ((((n - ν)! : ℕ) : ℝ)) ^ s) := by
      rw [Real.rpow_neg (Nat.cast_nonneg _), div_pow]
      field_simp
    calc ‖PowerSeries.coeff n G‖ ≤ CG * AG ^ n := hGn
      _ = (CG / Θ 0 * ((AG / b) ^ n * ((((n - ν)! : ℕ) : ℝ)) ^ (-s))) *
            (Θ 0 * b ^ n * ((((n - ν)! : ℕ) : ℝ)) ^ s) := hval
      _ ≤ (CG / Θ 0 * ((AG / b) ^ n * ((((n - ν)! : ℕ) : ℝ)) ^ (-s))) *
            (((n : ℝ) + 1) ^ ((d : ℕ) : ℝ) * Θ (n - ν)) :=
          mul_le_mul_of_nonneg_left hchain hMnn

/-- **A profile shifted by the truncation order is negligible against a leading profile term**, as
soon as the truncation order lies far enough beyond the vertex. -/
theorem tendsto_shiftedProfile_div_leading (hprof : IsRegularFactorialProfile s c₁ c₂ Θ)
    (hs : 0 < s) {A d : ℝ} {ν N : ℕ} (hνN : ν ≤ N + 1)
    (hA : A < d + s * ((N + 1 - ν : ℕ) : ℝ)) :
    Tendsto (fun n : ℕ => (((n : ℝ) + 1) ^ A * (Θ (N + 1) * Θ (n - (N + 1)))) /
      (((n : ℝ) + 1) ^ d * Θ (n - ν))) atTop (𝓝 0) := by
  have hΘpos : ∀ k, 0 < Θ k := hprof.pos
  have hc₁ : 0 < c₁ := hprof.c₁_pos
  set p : ℕ := N + 1 with hpdef
  set w : ℕ := p - ν with hwdef
  set E : ℝ := s * ((w : ℕ) : ℝ) with hEdef
  have hE0 : 0 ≤ E := by
    rw [hEdef]
    exact mul_nonneg hs.le (Nat.cast_nonneg _)
  have hδ : 0 < d + E - A := by
    rw [hEdef, hwdef]
    linarith [hA]
  have hc1w : (0 : ℝ) < c₁ ^ w := pow_pos hc₁ w
  have h2E : (0 : ℝ) < (2 : ℝ) ^ E := Real.rpow_pos_of_pos (by norm_num) E
  set K : ℝ := Θ p * (2 : ℝ) ^ E / c₁ ^ w with hKdef
  have hmaj : Tendsto (fun n : ℕ => K * (((n : ℝ) + 1) ^ (-(d + E - A)))) atTop (𝓝 0) := by
    have h := (tendsto_rpow_neg_succ hδ).const_mul K
    rwa [mul_zero] at h
  refine squeeze_zero' (Eventually.of_forall fun n => ?_) ?_ hmaj
  · have hden : (0 : ℝ) < ((n : ℝ) + 1) ^ d * Θ (n - ν) :=
      mul_pos (Real.rpow_pos_of_pos (by positivity) _) (hΘpos _)
    have hnum : (0 : ℝ) ≤ ((n : ℝ) + 1) ^ A * (Θ p * Θ (n - p)) :=
      mul_nonneg (Real.rpow_nonneg (by positivity) _)
        (mul_nonneg (hΘpos _).le (hΘpos _).le)
    exact div_nonneg hnum hden.le
  · filter_upwards [eventually_ge_atTop (2 * p)] with n hn
    have hpn : p ≤ n := by omega
    have hbase : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hden : (0 : ℝ) < ((n : ℝ) + 1) ^ d * Θ (n - ν) :=
      mul_pos (Real.rpow_pos_of_pos hbase _) (hΘpos _)
    have hshift := hprof.shift_above_pow hs.le hνN hpn
    have hcast : ((n : ℝ) + 1) / 2 ≤ (((n - p : ℕ) : ℝ) + 1) := by
      have h1 : ((n - p : ℕ) : ℝ) = (n : ℝ) - (p : ℝ) := by
        rw [Nat.cast_sub hpn]
      have h2 : (2 * p : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      rw [h1]
      linarith
    have hsplit : (((n : ℝ) + 1) / 2) ^ E = ((n : ℝ) + 1) ^ E / (2 : ℝ) ^ E :=
      Real.div_rpow hbase.le (by norm_num : (0:ℝ) ≤ 2) E
    have hpowmono : ((n : ℝ) + 1) ^ E / (2 : ℝ) ^ E ≤ (((n - p : ℕ) : ℝ) + 1) ^ E := by
      rw [← hsplit]
      exact Real.rpow_le_rpow (by positivity) hcast hE0
    have hkey : Θ (n - p) * (c₁ ^ w * (((n : ℝ) + 1) ^ E / (2 : ℝ) ^ E)) ≤ Θ (n - ν) := by
      refine le_trans ?_ hshift
      refine mul_le_mul_of_nonneg_left ?_ (hΘpos _).le
      exact mul_le_mul_of_nonneg_left hpowmono hc1w.le
    have hratio : Θ (n - p) * ((n : ℝ) + 1) ^ E
        ≤ Θ (n - ν) * ((2 : ℝ) ^ E / c₁ ^ w) := by
      have h := mul_le_mul_of_nonneg_right hkey (by positivity : (0:ℝ) ≤ (2:ℝ)^E / c₁ ^ w)
      calc Θ (n - p) * ((n : ℝ) + 1) ^ E
          = Θ (n - p) * (c₁ ^ w * (((n : ℝ) + 1) ^ E / (2 : ℝ) ^ E)) *
              ((2 : ℝ) ^ E / c₁ ^ w) := by
            field_simp
        _ ≤ Θ (n - ν) * ((2 : ℝ) ^ E / c₁ ^ w) := h
    rw [div_le_iff₀ hden]
    have hAdec : ((n : ℝ) + 1) ^ A = ((n : ℝ) + 1) ^ (A - E) * ((n : ℝ) + 1) ^ E := by
      rw [← Real.rpow_add hbase]
      ring_nf
    have hRHS : K * (((n : ℝ) + 1) ^ (-(d + E - A))) * (((n : ℝ) + 1) ^ d * Θ (n - ν))
        = (Θ p * ((n : ℝ) + 1) ^ (A - E)) * (Θ (n - ν) * ((2 : ℝ) ^ E / c₁ ^ w)) := by
      rw [hKdef, show -(d + E - A) = (A - E) - d from by ring, Real.rpow_sub hbase]
      field_simp
    calc ((n : ℝ) + 1) ^ A * (Θ p * Θ (n - p))
        = (Θ p * ((n : ℝ) + 1) ^ (A - E)) * (Θ (n - p) * ((n : ℝ) + 1) ^ E) := by
          rw [hAdec]; ring
      _ ≤ (Θ p * ((n : ℝ) + 1) ^ (A - E)) * (Θ (n - ν) * ((2 : ℝ) ^ E / c₁ ^ w)) :=
          mul_le_mul_of_nonneg_left hratio
            (mul_nonneg (hΘpos _).le (Real.rpow_nonneg hbase.le _))
      _ = K * (((n : ℝ) + 1) ^ (-(d + E - A))) * (((n : ℝ) + 1) ^ d * Θ (n - ν)) := hRHS.symm

end GaloisForLFunctions.HTGeometry
