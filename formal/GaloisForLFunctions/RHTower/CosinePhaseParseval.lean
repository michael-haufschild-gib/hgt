import GaloisForLFunctions.RHTower.XiShiftedHardEdgeCosineParseval

/-!
# Parseval and the `L²` Bernstein inequality for phase-shifted cosine polynomials

Differentiating a cosine polynomial `∑_{j ≤ N} b_j cos(jθ)` shifts every phase by `π/2` and
multiplies every coefficient by its frequency, so the `m`-th derivative is again a phase-shifted
cosine polynomial

`∑_{j ≤ N} b_j j^m cos(jθ + mπ/2)`.

Phase-shifted cosines of distinct integer frequencies are still orthogonal on the full period, so
Parseval holds verbatim, and since the frequencies are at most `N`, every derivative obeys

`‖q^{(m)}‖₂ ≤ N^m ‖q‖₂`.

This is the `L²` Bernstein inequality, the exact spectral statement behind the Cayley
angular-momentum bound.
-/

open Set MeasureTheory

noncomputable section

namespace RHTower

/-- The primitive of a scaled sine. -/
theorem integral_sin_mul_of_ne_zero {c : ℝ} (hc : c ≠ 0) (a b : ℝ) :
    (∫ θ in a..b, Real.sin (c * θ)) = (Real.cos (c * a) - Real.cos (c * b)) / c := by
  have hderiv : ∀ θ ∈ Set.uIcc a b,
      HasDerivAt (fun u : ℝ => -Real.cos (c * u) / c) (Real.sin (c * θ)) θ := by
    intro θ _
    have h1 : HasDerivAt (fun u : ℝ => c * u) c θ := by
      simpa using (hasDerivAt_id θ).const_mul c
    have h2 : HasDerivAt (fun u : ℝ => Real.cos (c * u)) (-Real.sin (c * θ) * c) θ :=
      (Real.hasDerivAt_cos (c * θ)).comp θ h1
    have h3 := (h2.neg).div_const c
    have hval : -(-Real.sin (c * θ) * c) / c = Real.sin (c * θ) := by
      field_simp
    rwa [hval] at h3
  have hint : IntervalIntegrable (fun θ : ℝ => Real.sin (c * θ)) volume a b :=
    (Real.continuous_sin.comp (continuous_const.mul continuous_id)).intervalIntegrable a b
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  ring

/-- The full-period integral of an integer-frequency sine vanishes. -/
theorem integral_sin_int_mul (n : ℤ) :
    (∫ θ in (-Real.pi)..Real.pi, Real.sin ((n : ℝ) * θ)) = 0 := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · have hc : ((n : ℝ)) ≠ 0 := Int.cast_ne_zero.2 hn
    rw [integral_sin_mul_of_ne_zero hc]
    have h2 : Real.cos ((n : ℝ) * -Real.pi) = Real.cos ((n : ℝ) * Real.pi) := by
      rw [show ((n : ℝ)) * -Real.pi = -((n : ℝ) * Real.pi) by ring, Real.cos_neg]
    rw [h2, sub_self, zero_div]

/-- **Orthogonality of phase-shifted cosines on the full period.** -/
theorem integral_cos_shift_mul_cos_shift (j k : ℕ) (φ : ℝ) :
    (∫ θ in (-Real.pi)..Real.pi, Real.cos ((j : ℝ) * θ + φ) * Real.cos ((k : ℝ) * θ + φ))
      = if j = k then (if j = 0 then 2 * Real.pi * Real.cos φ ^ (2 : ℕ) else Real.pi) else 0 := by
  have hpts : ∀ A B : ℝ, Real.cos A * Real.cos B = (Real.cos (A - B) + Real.cos (A + B)) / 2 := by
    intro A B
    rw [Real.cos_sub, Real.cos_add]
    ring
  have hprod : ∀ θ : ℝ, Real.cos ((j : ℝ) * θ + φ) * Real.cos ((k : ℝ) * θ + φ)
      = (Real.cos ((((j : ℤ) - (k : ℤ) : ℤ) : ℝ) * θ)
          + (Real.cos ((((j : ℤ) + (k : ℤ) : ℤ) : ℝ) * θ) * Real.cos (2 * φ)
            - Real.sin ((((j : ℤ) + (k : ℤ) : ℤ) : ℝ) * θ) * Real.sin (2 * φ))) / 2 := by
    intro θ
    rw [hpts]
    congr 2
    · congr 1
      push_cast
      ring
    · rw [show ((j : ℝ) * θ + φ) + ((k : ℝ) * θ + φ)
        = ((((j : ℤ) + (k : ℤ) : ℤ) : ℝ) * θ) + 2 * φ by push_cast; ring, Real.cos_add]
  rw [intervalIntegral.integral_congr (g := fun θ : ℝ =>
    (Real.cos ((((j : ℤ) - (k : ℤ) : ℤ) : ℝ) * θ)
      + (Real.cos ((((j : ℤ) + (k : ℤ) : ℤ) : ℝ) * θ) * Real.cos (2 * φ)
        - Real.sin ((((j : ℤ) + (k : ℤ) : ℤ) : ℝ) * θ) * Real.sin (2 * φ))) / 2)
    (fun θ _ => hprod θ)]
  have hc1 : IntervalIntegrable
      (fun θ : ℝ => Real.cos ((((j : ℤ) - (k : ℤ) : ℤ) : ℝ) * θ)) volume (-Real.pi) Real.pi :=
    (Real.continuous_cos.comp (continuous_const.mul continuous_id)).intervalIntegrable _ _
  have hc2 : IntervalIntegrable
      (fun θ : ℝ => Real.cos ((((j : ℤ) + (k : ℤ) : ℤ) : ℝ) * θ) * Real.cos (2 * φ))
      volume (-Real.pi) Real.pi :=
    ((Real.continuous_cos.comp (continuous_const.mul continuous_id)).mul
      continuous_const).intervalIntegrable _ _
  have hc3 : IntervalIntegrable
      (fun θ : ℝ => Real.sin ((((j : ℤ) + (k : ℤ) : ℤ) : ℝ) * θ) * Real.sin (2 * φ))
      volume (-Real.pi) Real.pi :=
    ((Real.continuous_sin.comp (continuous_const.mul continuous_id)).mul
      continuous_const).intervalIntegrable _ _
  rw [intervalIntegral.integral_div, intervalIntegral.integral_add hc1 (hc2.sub hc3),
    intervalIntegral.integral_sub hc2 hc3, intervalIntegral.integral_mul_const,
    intervalIntegral.integral_mul_const, integral_cos_int_mul, integral_cos_int_mul,
    integral_sin_int_mul]
  rcases eq_or_ne j k with rfl | hjk
  · rw [if_pos rfl, sub_self, if_pos rfl]
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · rw [if_pos rfl]
      norm_num
      rw [Real.cos_two_mul]
      ring
    · have hne : ((j : ℤ) + (j : ℤ)) ≠ 0 := by
        have : (0 : ℤ) < (j : ℤ) := by exact_mod_cast hj
        omega
      rw [if_neg hne, if_neg (by omega : ¬ j = 0)]
      ring
  · have hsub : ((j : ℤ) - (k : ℤ)) ≠ 0 := by
      intro h0
      exact hjk (by omega)
    rw [if_neg hjk, if_neg hsub]
    rcases Nat.eq_zero_or_pos (j + k) with hz | hp
    · exfalso
      omega
    · have hne : ((j : ℤ) + (k : ℤ)) ≠ 0 := by
        have : (0 : ℤ) < (j : ℤ) + (k : ℤ) := by exact_mod_cast hp
        omega
      rw [if_neg hne]
      norm_num


/-- The `m`-th derivative frame of a cosine polynomial: every coefficient scaled by `j^m` and every
phase shifted by `mπ/2`. -/
def cosPhasePoly (m M : ℕ) (b : ℕ → ℝ) (θ : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (M + 1),
    (b j * (j : ℝ) ^ m) * Real.cos ((j : ℝ) * θ + (m : ℝ) * (Real.pi / 2))

theorem cosPhasePoly_zero (M : ℕ) (b : ℕ → ℝ) : cosPhasePoly 0 M b = cosPoly M b := by
  funext θ
  unfold cosPhasePoly cosPoly
  refine Finset.sum_congr rfl fun j _ => ?_
  simp

theorem hasDerivAt_cosPhasePoly (m M : ℕ) (b : ℕ → ℝ) (θ : ℝ) :
    HasDerivAt (cosPhasePoly m M b) (cosPhasePoly (m + 1) M b θ) θ := by
  unfold cosPhasePoly
  refine HasDerivAt.fun_sum fun j _ => ?_
  have hlin : HasDerivAt (fun u : ℝ => (j : ℝ) * u + (m : ℝ) * (Real.pi / 2)) (j : ℝ) θ := by
    simpa using ((hasDerivAt_id θ).const_mul ((j : ℝ))).add_const ((m : ℝ) * (Real.pi / 2))
  have hcos : HasDerivAt (fun u : ℝ => Real.cos ((j : ℝ) * u + (m : ℝ) * (Real.pi / 2)))
      (-Real.sin ((j : ℝ) * θ + (m : ℝ) * (Real.pi / 2)) * (j : ℝ)) θ :=
    (Real.hasDerivAt_cos _).comp θ hlin
  have hres := hcos.const_mul (b j * (j : ℝ) ^ m)
  refine hres.congr_deriv ?_
  have hshift : Real.cos ((j : ℝ) * θ + ((m : ℕ) + 1 : ℕ) * (Real.pi / 2))
      = -Real.sin ((j : ℝ) * θ + (m : ℝ) * (Real.pi / 2)) := by
    rw [show (((m : ℕ) + 1 : ℕ) : ℝ) * (Real.pi / 2)
        = (m : ℝ) * (Real.pi / 2) + Real.pi / 2 by push_cast; ring,
      show (j : ℝ) * θ + ((m : ℝ) * (Real.pi / 2) + Real.pi / 2)
        = ((j : ℝ) * θ + (m : ℝ) * (Real.pi / 2)) + Real.pi / 2 by ring,
      Real.cos_add_pi_div_two]
  rw [hshift, pow_succ]
  ring

/-- **Parseval for phase-shifted cosine polynomials.** -/
theorem integral_cosPhasePoly_sq (m M : ℕ) (b : ℕ → ℝ) :
    (∫ θ in (-Real.pi)..Real.pi, cosPhasePoly m M b θ ^ (2 : ℕ))
      = ∑ j ∈ Finset.range (M + 1),
          (if j = 0 then 2 * Real.pi * Real.cos ((m : ℝ) * (Real.pi / 2)) ^ (2 : ℕ) else Real.pi)
            * (b j * (j : ℝ) ^ m) ^ (2 : ℕ) := by
  obtain ⟨c, hcdef⟩ : ∃ c : ℕ → ℝ, c = fun j => b j * (j : ℝ) ^ m := ⟨_, rfl⟩
  obtain ⟨φ, hφdef⟩ : ∃ φ : ℝ, φ = (m : ℝ) * (Real.pi / 2) := ⟨_, rfl⟩
  have hpoly : ∀ θ : ℝ, cosPhasePoly m M b θ
      = ∑ j ∈ Finset.range (M + 1), c j * Real.cos ((j : ℝ) * θ + φ) := by
    intro θ
    rw [cosPhasePoly, hcdef, hφdef]
  have hexpand : ∀ θ : ℝ, cosPhasePoly m M b θ ^ (2 : ℕ)
      = ∑ j ∈ Finset.range (M + 1), ∑ k ∈ Finset.range (M + 1),
        (c j * c k) * (Real.cos ((j : ℝ) * θ + φ) * Real.cos ((k : ℝ) * θ + φ)) := by
    intro θ
    rw [hpoly θ, sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    ring
  rw [intervalIntegral.integral_congr (g := fun θ : ℝ =>
    ∑ j ∈ Finset.range (M + 1), ∑ k ∈ Finset.range (M + 1),
      (c j * c k) * (Real.cos ((j : ℝ) * θ + φ) * Real.cos ((k : ℝ) * θ + φ)))
    (fun θ _ => hexpand θ)]
  have hintj : ∀ j ∈ Finset.range (M + 1), IntervalIntegrable
      (fun θ : ℝ => ∑ k ∈ Finset.range (M + 1),
        (c j * c k) * (Real.cos ((j : ℝ) * θ + φ) * Real.cos ((k : ℝ) * θ + φ)))
      volume (-Real.pi) Real.pi := by
    intro j _
    refine Continuous.intervalIntegrable ?_ _ _
    refine continuous_finsetSum _ fun k _ => ?_
    exact continuous_const.mul
      ((Real.continuous_cos.comp ((continuous_const.mul continuous_id).add continuous_const)).mul
        (Real.continuous_cos.comp ((continuous_const.mul continuous_id).add continuous_const)))
  rw [intervalIntegral.integral_finsetSum hintj]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hintk : ∀ k ∈ Finset.range (M + 1), IntervalIntegrable
      (fun θ : ℝ => (c j * c k) * (Real.cos ((j : ℝ) * θ + φ) * Real.cos ((k : ℝ) * θ + φ)))
      volume (-Real.pi) Real.pi := by
    intro k _
    refine Continuous.intervalIntegrable ?_ _ _
    exact continuous_const.mul
      ((Real.continuous_cos.comp ((continuous_const.mul continuous_id).add continuous_const)).mul
        (Real.continuous_cos.comp ((continuous_const.mul continuous_id).add continuous_const)))
  rw [intervalIntegral.integral_finsetSum hintk]
  have hterm : ∀ k ∈ Finset.range (M + 1),
      (∫ θ in (-Real.pi)..Real.pi,
        (c j * c k) * (Real.cos ((j : ℝ) * θ + φ) * Real.cos ((k : ℝ) * θ + φ)))
        = (c j * c k)
          * (if j = k then (if j = 0 then 2 * Real.pi * Real.cos φ ^ (2 : ℕ) else Real.pi) else 0) := by
    intro k _
    rw [intervalIntegral.integral_const_mul, integral_cos_shift_mul_cos_shift]
  rw [Finset.sum_congr rfl hterm, Finset.sum_eq_single j]
  · rw [if_pos rfl, hcdef, hφdef]
    ring
  · intro k _ hkj
    rw [if_neg (fun h => hkj h.symm), mul_zero]
  · intro hjnot
    exact absurd hj hjnot

/-- **The `L²` Bernstein inequality.**  Every derivative frame of a cosine polynomial of degree at
most `M` has `L²` norm at most `M^m` times that of the polynomial. -/
theorem integral_cosPhasePoly_sq_le (m M : ℕ) (b : ℕ → ℝ) :
    (∫ θ in (-Real.pi)..Real.pi, cosPhasePoly m M b θ ^ (2 : ℕ))
      ≤ ((M : ℝ) ^ m) ^ (2 : ℕ) * ∫ θ in (-Real.pi)..Real.pi, cosPoly M b θ ^ (2 : ℕ) := by
  rw [integral_cosPhasePoly_sq, integral_cosPoly_sq, Finset.mul_sum]
  refine Finset.sum_le_sum fun j hj => ?_
  simp only [Finset.mem_range] at hj
  have hjM : (j : ℝ) ≤ (M : ℝ) := by
    have : j ≤ M := by omega
    exact_mod_cast this
  have hj0 : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
  rcases Nat.eq_zero_or_pos j with rfl | hjpos
  · rcases Nat.eq_zero_or_pos m with rfl | hmpos
    · simp
    · have hzero : ((0 : ℕ) : ℝ) ^ m = 0 := by
        rw [Nat.cast_zero]
        exact zero_pow (by omega)
      rw [if_pos rfl, if_pos rfl, hzero]
      have hzz : (b 0 * (0 : ℝ)) ^ (2 : ℕ) = 0 := by ring
      rw [hzz, mul_zero]
      have hMnn : (0 : ℝ) ≤ ((M : ℝ) ^ m) ^ (2 : ℕ) := sq_nonneg _
      have hb0 : (0 : ℝ) ≤ b 0 ^ (2 : ℕ) := sq_nonneg _
      have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
      positivity
  · have hjne : ¬ j = 0 := by omega
    rw [if_neg hjne, if_neg hjne]
    have hpow : ((j : ℝ) ^ m) ^ (2 : ℕ) ≤ ((M : ℝ) ^ m) ^ (2 : ℕ) := by
      have h1 : (j : ℝ) ^ m ≤ (M : ℝ) ^ m := pow_le_pow_left₀ hj0 hjM m
      have h2 : (0 : ℝ) ≤ (j : ℝ) ^ m := by positivity
      exact pow_le_pow_left₀ h2 h1 2
    have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
    have hb : (0 : ℝ) ≤ b j ^ (2 : ℕ) := sq_nonneg _
    have hrw : (b j * (j : ℝ) ^ m) ^ (2 : ℕ) = b j ^ (2 : ℕ) * ((j : ℝ) ^ m) ^ (2 : ℕ) := by ring
    rw [hrw]
    have hkey := mul_le_mul_of_nonneg_left hpow
      (by positivity : (0 : ℝ) ≤ Real.pi * b j ^ (2 : ℕ))
    nlinarith [hkey]

end RHTower

end
