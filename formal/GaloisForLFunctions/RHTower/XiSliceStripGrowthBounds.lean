import GaloisForLFunctions.RHTower.XiSliceOffCentreArcTail
import GaloisForLFunctions.RHTower.XiSliceEulerGrowthAndMonotonicity

/-!
# Size of the slice off the real axis, against its value at an Euler point

Let `S(t, z) = ξ(½+z+it) ξ(½−z+it)` and `S(t, y) = |ξ(½+y+it)|²` on the real axis
(`xiSliceReal`).  Since `S` is even and real on the real axis,
`|S(t, a + ic)| = |ξ(½+|a|+i(t+c))| · |ξ(½+|a|+i(t−c))|` (`norm_xiSliceProduct_ofReal_add_mul_I`).
Comparing the Gamma factors with those at the Euler point `½ + R + it` (`norm_xi_split_le`) and
bounding `ζ` by its convexity bound gives, for `0 < η ≤ ¼` and `R₁ ≥ 1`, a constant `C` with
(`exists_norm_xiSliceProduct_le_strip`)

* `|S(t, a + ic)| ≤ C · S(t, ½ + 2η) · t^{−η}` when `|a| < ½ + η` (inside the strip the convexity loss
  `t^{½+η−|a|}` is beaten by the Gamma decay `t^{−(½+2η−|a|)}`);
* `|S(t, a + ic)| ≤ C · S(t, max(|a|, ½ + 2η))` when `½ + η ≤ |a| ≤ R₁`,

for `t ≥ 32R₁ + 16` and `|c| ≤ R₁`.  Together with the Cauchy estimate
(`norm_iteratedDeriv_xiSliceProduct_le`) this bounds the derivatives of the slice at real points
inside the critical strip by its size at the Euler point `½ + 2η`.
-/

open Complex Real Metric
open scoped ComplexOrder

namespace RHTower

noncomputable section

/-- `|S(t, a + ic)| = |ξ(½+|a|+i(t+c))| |ξ(½+|a|+i(t−c))|`. -/
theorem norm_xiSliceProduct_ofReal_add_mul_I (t a c : ℝ) :
    ‖xiSliceProduct t ((a : ℂ) + (c : ℂ) * I)‖
      = ‖xi (((1 / 2 + |a| : ℝ) : ℂ) + ((t + c : ℝ) : ℂ) * I)‖
        * ‖xi (((1 / 2 + |a| : ℝ) : ℂ) + ((t - c : ℝ) : ℂ) * I)‖ := by
  rcases le_or_gt 0 a with ha | ha
  · rw [abs_of_nonneg ha]
    exact norm_xiSliceProduct_eq t _ _
  · rw [abs_of_neg ha]
    have h1 : xiSliceProduct t ((a : ℂ) + (c : ℂ) * I)
        = (starRingEnd ℂ) (xiSliceProduct t (((-a : ℝ) : ℂ) + (c : ℂ) * I)) := by
      rw [← xiSliceProduct_conj, ← xiSliceProduct_neg]
      congr 1
      apply Complex.ext <;> simp
    rw [h1, Complex.norm_conj, norm_xiSliceProduct_eq]

/-- **Comparison with an Euler point, `ζ` bounds supplied.** -/
theorem norm_xiSliceProduct_le_of_ref {t a c R B m₀ : ℝ} (ht : 8 ≤ t) (haR : |a| ≤ R)
    (hc : |c| ≤ t / 2) (hm₀ : 0 < m₀)
    (hz₀ : m₀ ≤ ‖riemannZeta (((1 / 2 + R : ℝ) : ℂ) + (t : ℂ) * I)‖)
    (hz₁ : ‖riemannZeta (((1 / 2 + |a| : ℝ) : ℂ) + ((t + c : ℝ) : ℂ) * I)‖ ≤ B)
    (hz₂ : ‖riemannZeta (((1 / 2 + |a| : ℝ) : ℂ) + ((t - c : ℝ) : ℂ) * I)‖ ≤ B) :
    ‖xiSliceProduct t ((a : ℂ) + (c : ℂ) * I)‖
      ≤ xiSliceReal t R * (B / m₀) ^ 2 * Real.exp (-(R - |a|) * Real.log (t / (2 * Real.pi))
        + 12 * (R - |a| + |c|) / t + 4 * (1 / 2 + |a|) / t) := by
  rw [norm_xiSliceProduct_ofReal_add_mul_I]
  have h := norm_xi_split_le ht (abs_nonneg a) haR hc hm₀ hz₀ hz₁ hz₂
  unfold xiSliceReal
  exact h

/-- **The slice off the real axis against its value at an Euler point.** -/
theorem exists_norm_xiSliceProduct_le_strip {η R₁ : ℝ} (hη : 0 < η) (hη1 : η ≤ 1 / 4)
    (hR₁ : 1 ≤ R₁) :
    ∃ C : ℝ, 0 < C ∧ ∀ t a c : ℝ, 32 * R₁ + 16 ≤ t → |c| ≤ R₁ →
      (|a| < 1 / 2 + η →
        ‖xiSliceProduct t ((a : ℂ) + (c : ℂ) * I)‖ ≤ C * xiSliceReal t (1 / 2 + 2 * η) * t ^ (-η))
      ∧ (1 / 2 + η ≤ |a| → |a| ≤ R₁ →
        ‖xiSliceProduct t ((a : ℂ) + (c : ℂ) * I)‖
          ≤ C * xiSliceReal t (max |a| (1 / 2 + 2 * η))) := by
  obtain ⟨Cc, hCc, hconv⟩ := exists_norm_riemannZeta_le_convexity (η := η) hη (by linarith)
  set m₀ : ℝ := 1 / (1 + 1 / (2 * η)) with hm₀
  have hm₀0 : 0 < m₀ := by rw [hm₀]; positivity
  have hq : 0 < (2 * Real.pi) ^ R₁ := Real.rpow_pos_of_pos (by positivity) _
  refine ⟨Real.exp 1 * (2 * (2 * Real.pi) ^ R₁) * ((Cc + 1 + 1 / η) / m₀) ^ 2, by positivity, ?_⟩
  intro t a c ht hc
  have ht0 : 0 < t := by linarith
  have hR₁0 : 0 ≤ R₁ := by linarith
  have hct : |c| ≤ t / 2 := by linarith
  have hpos : ∀ y, 0 ≤ xiSliceReal t y := fun y => xiSliceReal_nonneg t y
  have hCm : ∀ B, 0 ≤ B → B ≤ Cc + 1 + 1 / η → (B / m₀) ^ 2 ≤ ((Cc + 1 + 1 / η) / m₀) ^ 2 :=
    fun B hB0 hB => pow_le_pow_left₀ (by positivity) (div_le_div_of_nonneg_right hB hm₀0.le) 2
  constructor
  · -- inside the strip: convexity against Gamma decay
    intro ha
    set R : ℝ := 1 / 2 + 2 * η with hR
    have haR : |a| ≤ R := by rw [hR]; linarith
    have hz₀ := inv_le_norm_riemannZeta_saddle t hη (le_refl (1 / 2 + 2 * η))
    have hBc : ∀ c' : ℝ, |c'| ≤ R₁ →
        ‖riemannZeta (((1 / 2 + |a| : ℝ) : ℂ) + ((t + c' : ℝ) : ℂ) * I)‖
          ≤ Cc * (2 * t) ^ ((1 + η - (1 / 2 + |a|)) / 2) := by
      intro c' hc'
      have hc'' := abs_le.mp hc'
      refine (hconv _ _ (by linarith [abs_nonneg a]) (by linarith) (by linarith)).trans ?_
      gcongr
      all_goals linarith
    have hB2 : ‖riemannZeta (((1 / 2 + |a| : ℝ) : ℂ) + ((t - c : ℝ) : ℂ) * I)‖
        ≤ Cc * (2 * t) ^ ((1 + η - (1 / 2 + |a|)) / 2) := by
      have := hBc (-c) (by rwa [abs_neg]); rwa [← sub_eq_add_neg] at this
    have h := norm_xiSliceProduct_le_of_ref (by linarith) haR hct hm₀0 hz₀ (hBc c hc) hB2
    have hpow : (Cc * (2 * t) ^ ((1 + η - (1 / 2 + |a|)) / 2) / m₀) ^ 2
        = (Cc / m₀) ^ 2 * (2 * t) ^ (1 / 2 + η - |a|) := by
      rw [div_pow, mul_pow, ← Real.rpow_natCast ((2 * t) ^ _), ← Real.rpow_mul (by positivity)]
      push_cast
      rw [show (1 + η - (1 / 2 + |a|)) / 2 * 2 = 1 / 2 + η - |a| by ring]
      ring
    have hexpX := exp_shift_decay_le (d := R - |a|) (c := c) (a := |a|) ht le_rfl
      (by linarith) (by rw [hR]; linarith [abs_nonneg a]) hc (by linarith)
    have hkey : (2 * t) ^ (1 / 2 + η - |a|) * t ^ (-(R - |a|)) ≤ 2 * t ^ (-η) := by
      rw [Real.mul_rpow (by norm_num) ht0.le, mul_assoc, ← Real.rpow_add ht0]
      have h2 : (2 : ℝ) ^ (1 / 2 + η - |a|) ≤ 2 := by
        calc (2 : ℝ) ^ (1 / 2 + η - |a|) ≤ 2 ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith [abs_nonneg a])
          _ = 2 := Real.rpow_one 2
      have h4 : t ^ (1 / 2 + η - |a| + -(R - |a|)) ≤ t ^ (-η) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) (by rw [hR]; linarith)
      exact mul_le_mul h2 h4 (by positivity) (by norm_num)
    have hinvη : 0 ≤ 1 / η := by positivity
    have hCm' := hCm Cc hCc.le (by linarith)
    rw [hpow] at h
    calc ‖xiSliceProduct t ((a : ℂ) + (c : ℂ) * I)‖
        ≤ xiSliceReal t R * ((Cc / m₀) ^ 2 * (2 * t) ^ (1 / 2 + η - |a|))
          * Real.exp (-(R - |a|) * Real.log (t / (2 * Real.pi))
            + 12 * (R - |a| + |c|) / t + 4 * (1 / 2 + |a|) / t) := h
      _ ≤ xiSliceReal t R * ((Cc / m₀) ^ 2 * (2 * t) ^ (1 / 2 + η - |a|))
          * (Real.exp 1 * ((2 * Real.pi) ^ R₁ * t ^ (-(R - |a|)))) :=
          mul_le_mul_of_nonneg_left hexpX (mul_nonneg (hpos _) (by positivity))
      _ = xiSliceReal t R * (Cc / m₀) ^ 2 * Real.exp 1 * (2 * Real.pi) ^ R₁
          * ((2 * t) ^ (1 / 2 + η - |a|) * t ^ (-(R - |a|))) := by ring
      _ ≤ xiSliceReal t R * (Cc / m₀) ^ 2 * Real.exp 1 * (2 * Real.pi) ^ R₁ * (2 * t ^ (-η)) :=
          mul_le_mul_of_nonneg_left hkey (by have := hpos R; positivity)
      _ ≤ xiSliceReal t R * ((Cc + 1 + 1 / η) / m₀) ^ 2 * Real.exp 1 * (2 * Real.pi) ^ R₁
          * (2 * t ^ (-η)) := by
          have := hpos R
          gcongr
      _ = Real.exp 1 * (2 * (2 * Real.pi) ^ R₁) * ((Cc + 1 + 1 / η) / m₀) ^ 2
          * xiSliceReal t (1 / 2 + 2 * η) * t ^ (-η) := by rw [hR]; ring
  · -- right of the strip: the Euler bound
    intro ha haR₁
    set R : ℝ := max |a| (1 / 2 + 2 * η) with hR
    have haR : |a| ≤ R := le_max_left _ _
    have hRe : 1 / 2 + 2 * η ≤ R := le_max_right _ _
    have hRR₁ : R ≤ R₁ := max_le haR₁ (by linarith)
    have hz₀ := inv_le_norm_riemannZeta_saddle t hη hRe
    have hB : ∀ c' : ℝ, ‖riemannZeta (((1 / 2 + |a| : ℝ) : ℂ) + ((t + c' : ℝ) : ℂ) * I)‖
        ≤ 1 + 1 / η := by
      intro c'
      have hre := re_ofReal_add_ofReal_mul_I (1 / 2 + |a|) (t + c')
      have h := Sieve.norm_riemannZeta_le
        (s := ((1 / 2 + |a| : ℝ) : ℂ) + ((t + c' : ℝ) : ℂ) * I) (by rw [hre]; linarith)
      rw [hre] at h
      have : 1 / (1 / 2 + |a| - 1) ≤ 1 / η := one_div_le_one_div_of_le hη (by linarith)
      linarith
    have hB2 : ‖riemannZeta (((1 / 2 + |a| : ℝ) : ℂ) + ((t - c : ℝ) : ℂ) * I)‖ ≤ 1 + 1 / η := by
      have := hB (-c); rwa [← sub_eq_add_neg] at this
    have h := norm_xiSliceProduct_le_of_ref (by linarith) haR hct hm₀0 hz₀ (hB c) hB2
    have hexpX := exp_shift_decay_le (d := R - |a|) (c := c) (a := |a|) ht le_rfl
      (by linarith) (by linarith [abs_nonneg a]) hc (by linarith)
    have htd : t ^ (-(R - |a|)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)
    have hCm' := hCm (1 + 1 / η) (by positivity) (by linarith)
    calc ‖xiSliceProduct t ((a : ℂ) + (c : ℂ) * I)‖
        ≤ xiSliceReal t R * ((1 + 1 / η) / m₀) ^ 2
          * Real.exp (-(R - |a|) * Real.log (t / (2 * Real.pi))
            + 12 * (R - |a| + |c|) / t + 4 * (1 / 2 + |a|) / t) := h
      _ ≤ xiSliceReal t R * ((1 + 1 / η) / m₀) ^ 2
          * (Real.exp 1 * ((2 * Real.pi) ^ R₁ * t ^ (-(R - |a|)))) :=
          mul_le_mul_of_nonneg_left hexpX (mul_nonneg (hpos _) (by positivity))
      _ ≤ xiSliceReal t R * ((Cc + 1 + 1 / η) / m₀) ^ 2
          * (Real.exp 1 * ((2 * Real.pi) ^ R₁ * 1)) := by
          have := hpos R
          gcongr
      _ ≤ Real.exp 1 * (2 * (2 * Real.pi) ^ R₁) * ((Cc + 1 + 1 / η) / m₀) ^ 2
          * xiSliceReal t R := by
          have hX : 0 ≤ xiSliceReal t R * ((Cc + 1 + 1 / η) / m₀) ^ 2 * Real.exp 1
              * (2 * Real.pi) ^ R₁ := by
            have := hpos R
            positivity
          calc xiSliceReal t R * ((Cc + 1 + 1 / η) / m₀) ^ 2
                * (Real.exp 1 * ((2 * Real.pi) ^ R₁ * 1))
              = xiSliceReal t R * ((Cc + 1 + 1 / η) / m₀) ^ 2 * Real.exp 1
                * (2 * Real.pi) ^ R₁ := by ring
            _ ≤ 2 * (xiSliceReal t R * ((Cc + 1 + 1 / η) / m₀) ^ 2 * Real.exp 1
                * (2 * Real.pi) ^ R₁) := by linarith
            _ = _ := by ring

/-- **Cauchy's estimate for the slice.** -/
theorem norm_iteratedDeriv_xiSliceProduct_le (t : ℝ) (n : ℕ) {x : ℂ} {r M : ℝ} (hr : 0 < r)
    (hM : ∀ z ∈ sphere x r, ‖xiSliceProduct t z‖ ≤ M) :
    ‖iteratedDeriv n (xiSliceProduct t) x‖ ≤ n.factorial * M / r ^ n :=
  Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n hr
    (differentiable_xiSliceProduct t).diffContOnCl hM

end

end RHTower
