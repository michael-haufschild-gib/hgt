import GaloisForLFunctions.HTGeometry.TopSymbolWimanPlace
import GaloisForLFunctions.HTGeometry.PolynomialGrowthBound

/-!
# The central index of a solution of a first-order algebraic differential equation

At a Wiman--Valiron place the top symbol of the relation is small, so the logarithmic derivative is
bounded by a quotient of the coefficient polynomials, hence by a power of the radius; and the
logarithmic derivative is comparable to the central index.  Since the Wiman places occur inside every
window of a fixed length, the resulting bound holds at *every* large radius.

This is the quantitative core of Gol'dberg's theorem: an entire solution of a first-order algebraic
differential equation has central index — hence maximum term, hence maximum modulus — of at most
polynomial growth.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex Filter Finset Set

variable {a : ℕ → ℂ}

/-- **The logarithmic derivative at a Wiman place is polynomially bounded.**  If the top symbol has
modulus at most one at `T`, and its leading coefficient is evaluated beyond the growth radius, then
`T` is bounded by a fixed multiple of a power of `1 + ‖z‖`. -/
theorem norm_le_of_topSymbol_le_one {S : Finset (ℕ × ℕ)} {A : ℕ × ℕ → Polynomial ℂ} {d m : ℕ}
    (hm : 1 ≤ m) (hmd : m ≤ d) (hmem : (d - m, m) ∈ S)
    (htopdeg : ∀ p ∈ S, p.1 + p.2 = d → p.2 ≤ m)
    (hAne : A (d - m, m) ≠ 0) {z T : ℂ}
    (hz : growthRadius (A (d - m, m)) ≤ ‖z‖)
    (htop : ‖∑ p ∈ S.filter (fun p => p.1 + p.2 = d), (A p).eval z * T ^ p.2‖ ≤ 1) :
    ‖T‖ ≤ (1 + ∑ p ∈ S, ‖(A p).eval z‖) / ‖(A (d - m, m)).eval z‖ + 1 := by
  classical
  set q : ℕ × ℕ := (d - m, m) with hq
  have hAqz : (A q).eval z ≠ 0 := eval_ne_zero_of_growthRadius_le hAne hz
  have hAqpos : (0 : ℝ) < ‖(A q).eval z‖ := norm_pos_iff.mpr hAqz
  have hsumnn : (0 : ℝ) ≤ ∑ p ∈ S, ‖(A p).eval z‖ :=
    Finset.sum_nonneg fun p _ => norm_nonneg _
  by_cases hT : ‖T‖ ≤ 1
  · have : (0 : ℝ) ≤ (1 + ∑ p ∈ S, ‖(A p).eval z‖) / ‖(A q).eval z‖ := by positivity
    linarith
  push_neg at hT
  -- split off the leading monomial
  have hqmem : q ∈ S.filter (fun p => p.1 + p.2 = d) := by
    refine Finset.mem_filter.mpr ⟨hmem, ?_⟩
    simp only [hq]
    omega
  have hsplit : ∑ p ∈ S.filter (fun p => p.1 + p.2 = d), (A p).eval z * T ^ p.2
      = (A q).eval z * T ^ m
        + ∑ p ∈ (S.filter (fun p => p.1 + p.2 = d)).erase q, (A p).eval z * T ^ p.2 := by
    rw [← Finset.add_sum_erase _ _ hqmem]
  have hlead : ‖(A q).eval z * T ^ m‖
      ≤ 1 + ∑ p ∈ (S.filter (fun p => p.1 + p.2 = d)).erase q, ‖(A p).eval z‖ * ‖T‖ ^ p.2 := by
    have h1 : ‖(A q).eval z * T ^ m‖
        ≤ ‖∑ p ∈ S.filter (fun p => p.1 + p.2 = d), (A p).eval z * T ^ p.2‖
          + ‖∑ p ∈ (S.filter (fun p => p.1 + p.2 = d)).erase q, (A p).eval z * T ^ p.2‖ := by
      rw [hsplit]
      have := norm_sub_le ((A q).eval z * T ^ m
        + ∑ p ∈ (S.filter (fun p => p.1 + p.2 = d)).erase q, (A p).eval z * T ^ p.2)
        (∑ p ∈ (S.filter (fun p => p.1 + p.2 = d)).erase q, (A p).eval z * T ^ p.2)
      simpa using this
    have h2 : ‖∑ p ∈ (S.filter (fun p => p.1 + p.2 = d)).erase q, (A p).eval z * T ^ p.2‖
        ≤ ∑ p ∈ (S.filter (fun p => p.1 + p.2 = d)).erase q, ‖(A p).eval z‖ * ‖T‖ ^ p.2 := by
      refine le_trans (norm_sum_le _ _) ?_
      exact Finset.sum_le_sum fun p _ => by rw [norm_mul, norm_pow]
    linarith
  -- every competing exponent is at most `m - 1`
  have hpow : ∀ p ∈ (S.filter (fun p => p.1 + p.2 = d)).erase q, ‖T‖ ^ p.2 ≤ ‖T‖ ^ (m - 1) := by
    intro p hp
    have hpf := Finset.mem_of_mem_erase hp
    have hpne := Finset.ne_of_mem_erase hp
    have hpmem := (Finset.mem_filter.mp hpf).1
    have hpd := (Finset.mem_filter.mp hpf).2
    have hple : p.2 ≤ m := htopdeg p hpmem hpd
    have hplt : p.2 ≤ m - 1 := by
      rcases Nat.lt_or_ge p.2 m with h | h
      · omega
      · exfalso
        have hp2 : p.2 = m := le_antisymm hple h
        have hp1 : p.1 = d - m := by omega
        exact hpne (Prod.ext hp1 hp2)
    exact pow_le_pow_right₀ (le_of_lt hT) hplt
  have hsum2 : ∑ p ∈ (S.filter (fun p => p.1 + p.2 = d)).erase q, ‖(A p).eval z‖ * ‖T‖ ^ p.2
      ≤ (∑ p ∈ S, ‖(A p).eval z‖) * ‖T‖ ^ (m - 1) := by
    calc ∑ p ∈ (S.filter (fun p => p.1 + p.2 = d)).erase q, ‖(A p).eval z‖ * ‖T‖ ^ p.2
        ≤ ∑ p ∈ (S.filter (fun p => p.1 + p.2 = d)).erase q,
            ‖(A p).eval z‖ * ‖T‖ ^ (m - 1) := by
          refine Finset.sum_le_sum fun p hp => ?_
          exact mul_le_mul_of_nonneg_left (hpow p hp) (norm_nonneg _)
      _ = (∑ p ∈ (S.filter (fun p => p.1 + p.2 = d)).erase q, ‖(A p).eval z‖) * ‖T‖ ^ (m - 1) := by
          rw [Finset.sum_mul]
      _ ≤ (∑ p ∈ S, ‖(A p).eval z‖) * ‖T‖ ^ (m - 1) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun p _ _ => norm_nonneg _)
          exact fun x hx => Finset.filter_subset _ _ (Finset.mem_of_mem_erase hx)
  -- divide by the common power
  have hTpow : (1 : ℝ) ≤ ‖T‖ ^ (m - 1) := one_le_pow₀ (le_of_lt hT)
  have hmsucc : m = (m - 1) + 1 := by omega
  have hkey : ‖(A q).eval z‖ * ‖T‖ * ‖T‖ ^ (m - 1)
      ≤ (1 + ∑ p ∈ S, ‖(A p).eval z‖) * ‖T‖ ^ (m - 1) := by
    have hlhs : ‖(A q).eval z * T ^ m‖ = ‖(A q).eval z‖ * ‖T‖ * ‖T‖ ^ (m - 1) := by
      have hTm : ‖T‖ ^ m = ‖T‖ * ‖T‖ ^ (m - 1) := by
        conv_lhs => rw [hmsucc]
        rw [pow_succ]
        ring
      rw [norm_mul, norm_pow, hTm]
      ring
    rw [hlhs] at hlead
    nlinarith [hlead, hsum2, hTpow]
  have hpospow : (0 : ℝ) < ‖T‖ ^ (m - 1) := by positivity
  have hdiv : ‖(A q).eval z‖ * ‖T‖ ≤ 1 + ∑ p ∈ S, ‖(A p).eval z‖ :=
    le_of_mul_le_mul_right hkey hpospow
  rw [div_add' _ _ _ (ne_of_gt hAqpos), le_div_iff₀ hAqpos]
  nlinarith [hdiv, hAqpos]

/-- **The coefficient quotient is polynomially bounded.**  Beyond the growth radius of the leading
coefficient every quotient of coefficient evaluations grows at most like a fixed power. -/
theorem exists_bound_coeff_quotient (S : Finset (ℕ × ℕ)) (A : ℕ × ℕ → Polynomial ℂ) {q : ℕ × ℕ}
    (hAne : A q ≠ 0) :
    ∃ (C : ℝ) (D : ℕ), 0 < C ∧ ∀ z : ℂ, growthRadius (A q) ≤ ‖z‖ →
      (1 + ∑ p ∈ S, ‖(A p).eval z‖) / ‖(A q).eval z‖ + 1 ≤ C * (1 + ‖z‖) ^ D := by
  classical
  set D : ℕ := S.sup (fun p => (A p).natDegree) with hD
  set c₀ : ℝ := 2 * coeffNormSum (1 : Polynomial ℂ) / ‖(A q).leadingCoeff‖ with hc₀
  set cS : ℝ := ∑ p ∈ S, 2 * coeffNormSum (A p) / ‖(A q).leadingCoeff‖ with hcS
  have hlc : (0 : ℝ) < ‖(A q).leadingCoeff‖ :=
    norm_pos_iff.mpr (Polynomial.leadingCoeff_ne_zero.mpr hAne)
  have hc₀0 : 0 ≤ c₀ := by
    rw [hc₀]
    have := coeffNormSum_nonneg (1 : Polynomial ℂ)
    positivity
  have hcS0 : 0 ≤ cS := by
    refine Finset.sum_nonneg fun p _ => ?_
    have := coeffNormSum_nonneg (A p)
    positivity
  refine ⟨c₀ + cS + 1, D, by linarith, fun z hz => ?_⟩
  have hAqz : (A q).eval z ≠ 0 := eval_ne_zero_of_growthRadius_le hAne hz
  have hAqpos : (0 : ℝ) < ‖(A q).eval z‖ := norm_pos_iff.mpr hAqz
  have hz1 : (1 : ℝ) ≤ ‖z‖ := le_trans (one_le_growthRadius _) hz
  have hbase : (1 : ℝ) ≤ 1 + ‖z‖ := by linarith
  have hpowmono : ∀ k : ℕ, k ≤ D → (1 + ‖z‖) ^ k ≤ (1 + ‖z‖) ^ D :=
    fun k hk => pow_le_pow_right₀ hbase hk
  -- the constant term
  have hone : 1 / ‖(A q).eval z‖ ≤ c₀ * (1 + ‖z‖) ^ D := by
    have h := norm_div_le_of_growthRadius_le (q := (1 : Polynomial ℂ)) hAne hz
    have hval : ‖(1 : Polynomial ℂ).eval z / (A q).eval z‖ = 1 / ‖(A q).eval z‖ := by
      rw [norm_div]
      simp
    rw [hval] at h
    refine le_trans h ?_
    have hdeg : (1 : Polynomial ℂ).natDegree ≤ D := by
      simp only [Polynomial.natDegree_one]
      exact Nat.zero_le _
    rw [hc₀]
    exact mul_le_mul_of_nonneg_left (hpowmono _ hdeg) (by positivity)
  -- the coefficient terms
  have hterms : ∀ p ∈ S, ‖(A p).eval z‖ / ‖(A q).eval z‖
      ≤ (2 * coeffNormSum (A p) / ‖(A q).leadingCoeff‖) * (1 + ‖z‖) ^ D := by
    intro p hp
    have h := norm_div_le_of_growthRadius_le (q := A p) hAne hz
    rw [norm_div] at h
    refine le_trans h ?_
    have hdeg : (A p).natDegree ≤ D := by
      rw [hD]
      exact Finset.le_sup (f := fun p => (A p).natDegree) hp
    have hc : (0 : ℝ) ≤ 2 * coeffNormSum (A p) / ‖(A q).leadingCoeff‖ := by
      have := coeffNormSum_nonneg (A p)
      positivity
    exact mul_le_mul_of_nonneg_left (hpowmono _ hdeg) hc
  have hsum : (∑ p ∈ S, ‖(A p).eval z‖) / ‖(A q).eval z‖ ≤ cS * (1 + ‖z‖) ^ D := by
    rw [Finset.sum_div, hcS, Finset.sum_mul]
    exact Finset.sum_le_sum hterms
  have hsplit : (1 + ∑ p ∈ S, ‖(A p).eval z‖) / ‖(A q).eval z‖
      = 1 / ‖(A q).eval z‖ + (∑ p ∈ S, ‖(A p).eval z‖) / ‖(A q).eval z‖ := by
    rw [add_div]
  have hlast : (1 : ℝ) ≤ (1 + ‖z‖) ^ D := one_le_pow₀ hbase
  rw [hsplit]
  nlinarith [hone, hsum, hlast]

/-- **Gol'dberg's central-index bound.**  A transcendental entire solution of a first-order
algebraic differential relation whose top symbol has positive degree in the derivative has central
index bounded by a fixed power of the radius, at *every* large radius. -/
theorem exists_centralIndex_le_pow_of_relation
    (ha : EntireCoeffs a) {n₀ : ℕ} (hn₀ : a n₀ ≠ 0)
    (htrans : ∀ M : ℕ, ∃ n, M ≤ n ∧ a n ≠ 0)
    {S : Finset (ℕ × ℕ)} {A : ℕ × ℕ → Polynomial ℂ} {d m : ℕ}
    (hdeg : ∀ p ∈ S, p.1 + p.2 ≤ d)
    (hrel : ∀ w : ℂ,
      ∑ p ∈ S, (A p).eval w * (coeffFun a w) ^ p.1 * (deriv (coeffFun a) w) ^ p.2 = 0)
    (hm : 1 ≤ m) (hmd : m ≤ d) (hmem : (d - m, m) ∈ S)
    (htopdeg : ∀ p ∈ S, p.1 + p.2 = d → p.2 ≤ m)
    (hAne : A (d - m, m) ≠ 0) :
    ∃ (C : ℝ) (K : ℕ), 0 < C ∧
      ∀ᶠ t : ℝ in atTop, ((centralIndex a t : ℕ) : ℝ) ≤ C * t ^ K := by
  classical
  obtain ⟨Cq, D, hCq, hquot⟩ := exists_bound_coeff_quotient S A hAne
  obtain ⟨Mw, hMw⟩ := exists_radius_norm_topSymbol_le ha hn₀ htrans hdeg hrel
    (η := 1) (ε := 1 / 2) one_pos (by norm_num)
  set W : ℝ := Nevanlinna.borelWindow (1 / 4) + 1 with hW
  set G : ℝ := Real.log (growthRadius (A (d - m, m))) with hG
  refine ⟨2 * Cq * 2 ^ D * Real.exp ((D + 1 : ℕ) * W), D + 1, by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop (Real.exp (max (max Mw G) 0))] with t ht
  have hexppos : (0 : ℝ) < Real.exp (max (max Mw G) 0) := Real.exp_pos _
  have htpos : (0 : ℝ) < t := lt_of_lt_of_le hexppos ht
  set y : ℝ := Real.log t with hy
  have hty : t = Real.exp y := (Real.exp_log htpos).symm
  have hyge : max (max Mw G) 0 ≤ y := by
    rw [hy, Real.le_log_iff_exp_le htpos]
    exact ht
  have hyM : Mw ≤ y := le_trans (le_trans (le_max_left Mw G) (le_max_left _ _)) hyge
  have hyG : G ≤ y := le_trans (le_trans (le_max_right Mw G) (le_max_left _ _)) hyge
  have hy0 : (0 : ℝ) ≤ y := le_trans (le_max_right _ _) hyge
  obtain ⟨y', hy', hy'M, z, hz, htop, hbound⟩ := hMw y
  have hmaxy : max y Mw = y := max_eq_left hyM
  rw [hmaxy] at hy'M
  have hy'W : y' ≤ y + W := by
    rw [hW]
    linarith
  -- the point is beyond the growth radius
  have hzge : Real.exp y ≤ ‖z‖ := by
    rw [hz]
    exact Real.exp_le_exp.mpr hy'
  have hz1 : (1 : ℝ) ≤ ‖z‖ := le_trans (Real.one_le_exp hy0) hzge
  have hgr : growthRadius (A (d - m, m)) ≤ ‖z‖ := by
    have hpos : (0 : ℝ) < growthRadius (A (d - m, m)) := by
      have := one_le_growthRadius (A (d - m, m))
      linarith
    have : growthRadius (A (d - m, m)) = Real.exp G := by
      rw [hG, Real.exp_log hpos]
    rw [this, hz]
    exact Real.exp_le_exp.mpr (le_trans hyG hy')
  -- the logarithmic derivative is polynomially bounded
  set T : ℂ := deriv (coeffFun a) z / coeffFun a z with hT
  have hTle : ‖T‖ ≤ Cq * (1 + ‖z‖) ^ D :=
    le_trans (norm_le_of_topSymbol_le_one hm hmd hmem htopdeg hAne hgr htop)
      (hquot z hgr)
  have hbase : (1 : ℝ) + ‖z‖ ≤ 2 * ‖z‖ := by linarith
  have hpow : (1 + ‖z‖) ^ D ≤ 2 ^ D * ‖z‖ ^ D := by
    calc (1 + ‖z‖) ^ D ≤ (2 * ‖z‖) ^ D := pow_le_pow_left₀ (by linarith) hbase D
      _ = 2 ^ D * ‖z‖ ^ D := by rw [mul_pow]
  -- the central index is comparable to the logarithmic derivative
  set ν : ℝ := ((centralIndex a (Real.exp y') : ℕ) : ℝ) with hν
  have hν0 : (0 : ℝ) ≤ ν := Nat.cast_nonneg _
  have hνle : ν ≤ 2 * (‖z‖ * ‖T‖) := by
    have h1 : ‖(z : ℂ) * T - (ν : ℂ)‖ ≤ (1 / 2) * ν := by
      have heq : (z : ℂ) * T = z * deriv (coeffFun a) z / coeffFun a z := by
        rw [hT]; ring
      rw [heq]
      exact hbound
    have h2 : ν - ‖(z : ℂ) * T‖ ≤ ‖(z : ℂ) * T - (ν : ℂ)‖ := by
      have h3 := norm_sub_norm_le ((ν : ℂ)) ((z : ℂ) * T)
      rw [norm_sub_rev] at h3
      have h4 : ‖(ν : ℂ)‖ = ν := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hν0]
      rw [h4] at h3
      linarith
    have h5 : ‖(z : ℂ) * T‖ = ‖z‖ * ‖T‖ := norm_mul _ _
    rw [h5] at h2
    linarith
  -- assemble
  have hmono : ((centralIndex a t : ℕ) : ℝ) ≤ ν := by
    rw [hν, hty]
    exact monotone_centralIndex_exp ha hn₀ hy'
  have hzle : ‖z‖ ≤ t * Real.exp W := by
    rw [hz, hty, ← Real.exp_add]
    exact Real.exp_le_exp.mpr hy'W
  have hTpos : (0 : ℝ) ≤ ‖T‖ := norm_nonneg _
  have hzpos : (0 : ℝ) < ‖z‖ := by linarith
  have hfinal : ν ≤ 2 * Cq * 2 ^ D * ‖z‖ ^ (D + 1) := by
    have hstep : ‖z‖ * ‖T‖ ≤ ‖z‖ * (Cq * (2 ^ D * ‖z‖ ^ D)) := by
      refine mul_le_mul_of_nonneg_left ?_ (le_of_lt hzpos)
      calc ‖T‖ ≤ Cq * (1 + ‖z‖) ^ D := hTle
        _ ≤ Cq * (2 ^ D * ‖z‖ ^ D) := by
            exact mul_le_mul_of_nonneg_left hpow (le_of_lt hCq)
    have hpowsucc : ‖z‖ ^ (D + 1) = ‖z‖ * ‖z‖ ^ D := by
      rw [pow_succ]
      ring
    rw [hpowsucc]
    nlinarith [hνle, hstep]
  have hzpow : ‖z‖ ^ (D + 1) ≤ (t * Real.exp W) ^ (D + 1) :=
    pow_le_pow_left₀ (le_of_lt hzpos) hzle (D + 1)
  have hexpand : (t * Real.exp W) ^ (D + 1) = t ^ (D + 1) * Real.exp W ^ (D + 1) := by
    rw [mul_pow]
  have hexpeq : Real.exp W ^ (D + 1) = Real.exp (((D : ℝ) + 1) * W) := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hcast : ((D + 1 : ℕ) : ℝ) * W = ((D : ℝ) + 1) * W := by push_cast; ring
  have hCq0 : (0 : ℝ) ≤ 2 * Cq * 2 ^ D := by positivity
  calc ((centralIndex a t : ℕ) : ℝ) ≤ ν := hmono
    _ ≤ 2 * Cq * 2 ^ D * ‖z‖ ^ (D + 1) := hfinal
    _ ≤ 2 * Cq * 2 ^ D * (t * Real.exp W) ^ (D + 1) :=
        mul_le_mul_of_nonneg_left hzpow hCq0
    _ = 2 * Cq * 2 ^ D * Real.exp ((D + 1 : ℕ) * W) * t ^ (D + 1) := by
        rw [hexpand, hexpeq, hcast]
        ring

end GaloisForLFunctions.HTGeometry
