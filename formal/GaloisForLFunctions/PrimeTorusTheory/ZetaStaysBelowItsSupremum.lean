import GaloisForLFunctions.PrimeTorusTheory.TheMassOfMisalignedPrimes

/-!
# Zeta stays below its supremum

On a vertical line `Re s = σ > 1` the supremum of `|ζ|` is `ζ(σ)`, approached along Kronecker heights. The Euler product turns the mass of
misaligned primes into a rate: `|ζ(σ + it)| ≤ ζ(σ) exp(−(log |t|)^{-C})` with `C = 3σ + 13` (`norm_zeta_le_of_large`). So the supremum is
approached at most at a rate polynomial in `log |t|`.
-/

open Finset Filter Topology Real

namespace GaloisForLFunctions.PrimeTorusTheory

noncomputable section

/-- The saving of one Euler factor. -/
theorem norm_euler_factor_le {p : ℕ} (hp : p.Prime) {σ t : ℝ} (hσ : 1 < σ) :
    ‖(1 - (p : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I)))⁻¹‖ ≤
      ‖(1 - (p : ℂ) ^ (-(σ : ℂ)))⁻¹‖ *
        Real.exp (-((p : ℝ) ^ (-σ) * (1 - Real.cos (t * Real.log p))) / 3) := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp0 : (0 : ℝ) < p := by linarith
  have hlogp : 0 < Real.log p := Real.log_pos (by linarith)
  set x : ℝ := (p : ℝ) ^ (-σ) with hx
  have hx0 : 0 < x := Real.rpow_pos_of_pos hp0 _
  have hx12 : x ≤ 1 / 2 := by
    have h1 : x ≤ (p : ℝ) ^ (-1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    have h2 : (p : ℝ) ^ (-1 : ℝ) = 1 / p := by rw [Real.rpow_neg_one, one_div]
    have h3 : 1 / (p : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hp2
    linarith
  set c : ℝ := Real.cos (t * Real.log p) with hc
  have hc1 : c ≤ 1 := Real.cos_le_one _
  have hc2 : -1 ≤ c := Real.neg_one_le_cos _
  have hpc : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hw : (p : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I)) =
      Complex.exp (((Real.log p : ℝ) : ℂ) * (-((σ : ℂ) + (t : ℂ) * Complex.I))) := by
    rw [Complex.cpow_def_of_ne_zero hpc, ← Complex.ofReal_natCast, Complex.ofReal_log hp0.le]
  have hw0 : (p : ℂ) ^ (-(σ : ℂ)) = ((x : ℝ) : ℂ) := by
    rw [hx, Complex.ofReal_cpow hp0.le]
    push_cast
    rfl
  have hre : ((p : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I))).re = x * c := by
    rw [hw, Complex.exp_re]
    have key1 : ∀ a b d : ℝ, ((a : ℂ) * (-((b : ℂ) + (d : ℂ) * Complex.I))).re = -b * a := by
      intro a b d
      simp
      ring
    have key2 : ∀ a b d : ℝ, ((a : ℂ) * (-((b : ℂ) + (d : ℂ) * Complex.I))).im = -(d * a) := by
      intro a b d
      simp
      ring
    have e1 := key1 (Real.log p) σ t
    have e2 := key2 (Real.log p) σ t
    rw [e1, e2, Real.cos_neg, hx, Real.rpow_def_of_pos hp0]
    congr 2
    ring
  have hnorm : ‖(p : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I))‖ = x := by
    rw [Complex.norm_natCast_cpow_of_pos hp.pos]
    simp [hx]
  have hsq : ‖1 - (p : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I))‖ ^ 2 =
      (1 - x) ^ 2 + 2 * x * (1 - c) := by
    set z := (p : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I)) with hz
    have h1 : ‖1 - z‖ ^ 2 = Complex.normSq (1 - z) := by rw [Complex.sq_norm]
    have h2 : Complex.normSq z = x ^ 2 := by
      rw [← Complex.sq_norm, hnorm]
    rw [h1, Complex.normSq_sub, h2]
    simp [hre]
    ring
  have hx1 : 0 < 1 - x := by linarith
  have hnorm0 : ‖1 - (p : ℂ) ^ (-(σ : ℂ))‖ = 1 - x := by
    rw [hw0]
    have : (1 : ℂ) - (x : ℂ) = ((1 - x : ℝ) : ℂ) := by push_cast; ring
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx1]
  rw [norm_inv, norm_inv, hnorm0]
  set A : ℝ := ‖1 - (p : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I))‖ with hA
  have hA0 : 0 ≤ A := norm_nonneg _
  set v : ℝ := 2 * x * (1 - c) with hv
  have hv0 : 0 ≤ v := by
    rw [hv]
    have : 0 ≤ 1 - c := by linarith
    positivity
  have hv2 : v ≤ 2 := by
    rw [hv]
    nlinarith
  have hA2 : (1 - x) ^ 2 * (1 + v) ≤ A ^ 2 := by
    rw [hA, hsq]
    have h1 : (1 - x) ^ 2 ≤ 1 := by nlinarith
    nlinarith
  have hlog : v / 3 ≤ Real.log (1 + v) := by
    have h3 := Real.one_sub_inv_le_log_of_pos (by linarith : 0 < 1 + v)
    have h4 : v / 3 ≤ 1 - (1 + v)⁻¹ := by
      have h5 : (1 + v)⁻¹ = 1 / (1 + v) := by rw [one_div]
      rw [h5, le_sub_iff_add_le, ← le_sub_iff_add_le', div_le_iff₀ (by linarith)]
      nlinarith
    linarith
  have hgoal : A⁻¹ ≤ (1 - x)⁻¹ * Real.exp (-(x * (1 - c)) / 3) := by
    have e : -(x * (1 - c)) / 3 = -(v / 3) / 2 := by
      rw [hv]
      ring
    rw [e]
    have hE : (1 - x) * Real.exp (v / 3 / 2) ≤ A := by
      have h5 : ((1 - x) * Real.exp (v / 3 / 2)) ^ 2 ≤ A ^ 2 := by
        rw [mul_pow, ← Real.exp_nat_mul]
        have e2 : ((2 : ℕ) : ℝ) * (v / 3 / 2) = v / 3 := by
          push_cast
          ring
        rw [e2]
        have h6 : Real.exp (v / 3) ≤ 1 + v := by
          have := Real.exp_le_exp.mpr hlog
          rwa [Real.exp_log (by linarith)] at this
        calc (1 - x) ^ 2 * Real.exp (v / 3) ≤ (1 - x) ^ 2 * (1 + v) :=
              mul_le_mul_of_nonneg_left h6 (by positivity)
          _ ≤ _ := hA2
      exact (pow_le_pow_iff_left₀ (by positivity) hA0 (by norm_num)).mp h5
    have hEpos : 0 < (1 - x) * Real.exp (v / 3 / 2) := by positivity
    have hinv := inv_anti₀ hEpos hE
    calc A⁻¹ ≤ ((1 - x) * Real.exp (v / 3 / 2))⁻¹ := hinv
      _ = _ := by
          rw [mul_inv, ← Real.exp_neg]
          congr 2
          ring
  exact hgoal

/-- The Euler product carries the column sum to the size of `ζ`. -/
theorem norm_zeta_le_of_sum {σ : ℝ} (hσ : 1 < σ) (t : ℝ) (N : ℕ) :
    ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ ‖riemannZeta (σ : ℂ)‖ *
      Real.exp (-(∑ p ∈ N.primesBelow, (p : ℝ) ^ (-σ) * (1 - Real.cos (t * Real.log p))) / 3) := by
  classical
  set s : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I with hs
  have hsre : 1 < s.re := by simpa [hs] using hσ
  have hσre : 1 < (σ : ℂ).re := by simpa using hσ
  have h1 := (riemannZeta_eulerProduct hsre).norm
  have h2 := ((riemannZeta_eulerProduct hσre).norm).mul_const
    (Real.exp (-(∑ p ∈ N.primesBelow, (p : ℝ) ^ (-σ) * (1 - Real.cos (t * Real.log p))) / 3))
  refine le_of_tendsto_of_tendsto h1 h2 ?_
  filter_upwards [eventually_ge_atTop N] with n hn
  have hnn : ∀ p : ℕ, 0 ≤ (p : ℝ) ^ (-σ) * (1 - Real.cos (t * Real.log p)) := fun p => by
    have := Real.cos_le_one (t * Real.log p)
    exact mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg p) _) (by linarith)
  rw [norm_prod, norm_prod]
  have hstep : ∏ p ∈ n.primesBelow, ‖(1 - (p : ℂ) ^ (-s))⁻¹‖ ≤
      ∏ p ∈ n.primesBelow, (‖(1 - (p : ℂ) ^ (-(σ : ℂ)))⁻¹‖ *
        Real.exp (-((p : ℝ) ^ (-σ) * (1 - Real.cos (t * Real.log p))) / 3)) :=
    Finset.prod_le_prod (fun p _ => norm_nonneg _) fun p hp =>
      norm_euler_factor_le (Nat.mem_primesBelow.mp hp).2 hσ
  refine hstep.trans ?_
  rw [Finset.prod_mul_distrib, ← Real.exp_sum]
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (Finset.prod_nonneg fun p _ => norm_nonneg _)
  have hsub : N.primesBelow ⊆ n.primesBelow := by
    intro p hp
    have h3 := Nat.mem_primesBelow.mp hp
    exact Nat.mem_primesBelow.mpr ⟨by omega, h3.2⟩
  have hle : ∑ p ∈ N.primesBelow, (p : ℝ) ^ (-σ) * (1 - Real.cos (t * Real.log p)) ≤
      ∑ p ∈ n.primesBelow, (p : ℝ) ^ (-σ) * (1 - Real.cos (t * Real.log p)) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub fun p _ _ => hnn p
  have e : ∑ p ∈ n.primesBelow, -((p : ℝ) ^ (-σ) * (1 - Real.cos (t * Real.log p))) / 3 =
      -(∑ p ∈ n.primesBelow, (p : ℝ) ^ (-σ) * (1 - Real.cos (t * Real.log p))) / 3 := by
    rw [← Finset.sum_div, Finset.sum_neg_distrib]
  rw [e]
  linarith

/-- **Zeta stays below its supremum.** For `σ > 1` and large `|t|`, `|ζ(σ + it)| ≤ ζ(σ) exp(−(log |t|)^{-(3σ+13)})`. -/
theorem norm_zeta_le_of_large {σ : ℝ} (hσ : 1 < σ) :
    ∃ T₀ : ℝ, 0 < T₀ ∧ ∀ t : ℝ, T₀ ≤ |t| →
      ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ ‖riemannZeta (σ : ℂ)‖ *
        Real.exp (-Real.log |t| ^ (-(3 * σ + 13))) := by
  obtain ⟨T₁, hT₁, hcrit⟩ := le_sum_primes_critical
  obtain ⟨T₂, hT₂, hsize⟩ := eventually_heightSize
  refine ⟨max (max T₁ T₂) (Real.exp 100000), lt_of_lt_of_le (Real.exp_pos _) (le_max_right _ _),
    fun t ht => ?_⟩
  have ht1 : T₁ ≤ |t| := (le_max_left _ _).trans ((le_max_left _ _).trans ht)
  have ht2 : T₂ ≤ |t| := (le_max_right _ _).trans ((le_max_left _ _).trans ht)
  have ht3 : Real.exp 100000 ≤ |t| := (le_max_right _ _).trans ht
  have htpos : 0 < |t| := lt_of_lt_of_le hT₁ ht1
  have hL5 : 100000 ≤ Real.log |t| := by
    rw [Real.le_log_iff_exp_le htpos]
    exact ht3
  have h := hsize t ht2
  set N := ⌈48 * Real.log |t| ^ 2 * Real.log (Real.log |t|)⌉₊ with hN
  have hcol := hcrit t ht1 N (Nat.le_ceil _)
  have hbase := norm_zeta_le_of_sum hσ t N
  refine hbase.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (norm_nonneg _))
  generalize Real.log |t| = L at h hL5 hN hcol ⊢
  generalize hℓdef : Real.log L = ℓ at h hN hcol
  have hℓ := h.one_le
  have h100 := h.log_le
  have hL0 : 0 < L := by linarith
  have hLone : 1 ≤ L := by linarith
  have hNle : (N : ℝ) ≤ L ^ 3 := by
    have h1 : (N : ℝ) < 48 * L ^ 2 * ℓ + 1 := by
      rw [hN]
      exact Nat.ceil_lt_add_one (by positivity)
    have h2 : 1 ≤ L ^ 2 * ℓ := by nlinarith
    have h3 : L ^ 3 = L ^ 2 * L := by ring
    have h4 : 0 < L ^ 2 := by positivity
    nlinarith
  have hσ0 : 0 < σ - 1 / 2 := by linarith
  set D : ℝ := L ^ (-(3 * (σ - 1 / 2))) with hD
  have hDpos : 0 < D := Real.rpow_pos_of_pos hL0 _
  -- each term of the sum
  have hterm : ∀ p ∈ N.primesBelow, D * ((1 - Real.cos (t * Real.log p)) / √(p : ℝ)) ≤
      (p : ℝ) ^ (-σ) * (1 - Real.cos (t * Real.log p)) := by
    intro p hp
    have hp' := Nat.mem_primesBelow.mp hp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp'.2.pos
    have hpN : (p : ℝ) ≤ L ^ 3 := by
      have : (p : ℝ) ≤ N := by exact_mod_cast hp'.1.le
      linarith
    have hc := Real.cos_le_one (t * Real.log p)
    have e : (p : ℝ) ^ (-σ) = (p : ℝ) ^ (-(σ - 1 / 2)) * (1 / √(p : ℝ)) := by
      have h3 : 1 / √(p : ℝ) = (p : ℝ) ^ (-(1 / 2 : ℝ)) := by
        rw [Real.sqrt_eq_rpow, Real.rpow_neg hp0.le, one_div]
      rw [h3, ← Real.rpow_add hp0]
      congr 1
      ring
    have hmono : D ≤ (p : ℝ) ^ (-(σ - 1 / 2)) := by
      have h4 : (L ^ 3) ^ (-(σ - 1 / 2)) ≤ (p : ℝ) ^ (-(σ - 1 / 2)) :=
        Real.rpow_le_rpow_of_nonpos hp0 hpN (by linarith)
      have h5 : (L ^ 3) ^ (-(σ - 1 / 2)) = D := by
        rw [hD, ← Real.rpow_natCast L 3, ← Real.rpow_mul hL0.le]
        congr 1
        push_cast
        ring
      linarith
    rw [e]
    have hnn : 0 ≤ (1 - Real.cos (t * Real.log p)) / √(p : ℝ) :=
      div_nonneg (by linarith) (Real.sqrt_nonneg _)
    calc D * ((1 - Real.cos (t * Real.log p)) / √(p : ℝ))
        ≤ (p : ℝ) ^ (-(σ - 1 / 2)) * ((1 - Real.cos (t * Real.log p)) / √(p : ℝ)) :=
          mul_le_mul_of_nonneg_right hmono hnn
      _ = _ := by ring
  have hsum : D * (4 / 10 ^ 10 / (L ^ 8 * ℓ ^ 4)) ≤
      ∑ p ∈ N.primesBelow, (p : ℝ) ^ (-σ) * (1 - Real.cos (t * Real.log p)) := by
    calc _ ≤ D * ∑ p ∈ N.primesBelow, (1 - Real.cos (t * Real.log p)) / √(p : ℝ) :=
          mul_le_mul_of_nonneg_left hcol hDpos.le
      _ = ∑ p ∈ N.primesBelow, D * ((1 - Real.cos (t * Real.log p)) / √(p : ℝ)) := Finset.mul_sum _ _ _
      _ ≤ _ := Finset.sum_le_sum hterm
  -- the exponent
  have hsmall : L ^ (-(3 * σ + 13)) ≤ D * (L ^ (-14 : ℝ)) := by
    rw [hD, ← Real.rpow_add hL0]
    refine Real.rpow_le_rpow_of_exponent_le hLone ?_
    linarith
  have hℓL : ℓ ≤ L := by linarith
  have hfrac : L ^ (-14 : ℝ) ≤ (4 / 10 ^ 10 / (L ^ 8 * ℓ ^ 4)) / 3 := by
    have e14 : L ^ (-14 : ℝ) = 1 / L ^ 14 := by
      rw [Real.rpow_neg hL0.le, one_div]
      norm_cast
    rw [e14, div_div, div_le_div_iff₀ (by positivity) (by positivity)]
    have hℓ4 : ℓ ^ 4 ≤ L ^ 4 := pow_le_pow_left₀ (by linarith) hℓL 4
    have hL2 : (10 : ℝ) ^ 10 ≤ L ^ 2 := by
      have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 100000) hL5 2
      calc (10 : ℝ) ^ 10 = 100000 ^ 2 := by norm_num
        _ ≤ _ := this
    have hL8 : 0 < L ^ 8 := by positivity
    have e15 : L ^ 14 = L ^ 8 * L ^ 4 * L ^ 2 := by ring
    calc 1 * (L ^ 8 * ℓ ^ 4 * 3) ≤ 1 * (L ^ 8 * L ^ 4 * 3) := by
          have := mul_le_mul_of_nonneg_left hℓ4 hL8.le
          linarith
      _ ≤ 4 / 10 ^ 10 * L ^ 14 := by
          rw [e15]
          have hpos : 0 < L ^ 8 * L ^ 4 := by positivity
          have : 3 ≤ 4 / 10 ^ 10 * L ^ 2 := by
            have h7 : (4 : ℝ) / 10 ^ 10 * 10 ^ 10 ≤ 4 / 10 ^ 10 * L ^ 2 :=
              mul_le_mul_of_nonneg_left hL2 (by norm_num)
            norm_num at h7 ⊢
            linarith
          calc 1 * (L ^ 8 * L ^ 4 * 3) = L ^ 8 * L ^ 4 * 3 := one_mul _
            _ ≤ L ^ 8 * L ^ 4 * (4 / 10 ^ 10 * L ^ 2) := mul_le_mul_of_nonneg_left this hpos.le
            _ = _ := by ring
  have hfinal : L ^ (-(3 * σ + 13)) ≤
      (∑ p ∈ N.primesBelow, (p : ℝ) ^ (-σ) * (1 - Real.cos (t * Real.log p))) / 3 := by
    calc L ^ (-(3 * σ + 13)) ≤ D * L ^ (-14 : ℝ) := hsmall
      _ ≤ D * ((4 / 10 ^ 10 / (L ^ 8 * ℓ ^ 4)) / 3) := mul_le_mul_of_nonneg_left hfrac hDpos.le
      _ = (D * (4 / 10 ^ 10 / (L ^ 8 * ℓ ^ 4))) / 3 := by ring
      _ ≤ _ := div_le_div_of_nonneg_right hsum (by norm_num)
  linarith

end

end GaloisForLFunctions.PrimeTorusTheory
