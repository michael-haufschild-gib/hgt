import GaloisForLFunctions.RHTower.JonquierePhase

/-!
# The `k`-th Jonquière channel coefficient

Combining the phase identity, the zeta functional equation at `s-k`, Euler's reflection formula
and the descending Gamma recursion identifies the `k`-th coefficient of the regular part of the
boundary polylogarithm as `ζ(s-k) i^k / k!`.
-/

open Complex Filter Topology

namespace RHTower

theorem sin_pi_mul_ne_zero {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) :
    Complex.sin (↑Real.pi * s) ≠ 0 := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  rw [Complex.sin_ne_zero_iff]
  intro k hcon
  have hre : (↑Real.pi * s : ℂ).re = ((k : ℂ) * ↑Real.pi).re := by rw [hcon]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.intCast_re,
    Complex.intCast_im] at hre
  norm_num at hre
  have hpine : Real.pi ≠ 0 := hpi.ne'
  have hk : (k : ℝ) = s.re := by
    field_simp at hre
    linarith
  have hk0 : (0 : ℝ) < (k : ℝ) := by rw [hk]; exact h0
  have hk1 : (k : ℝ) < 1 := by rw [hk]; exact h1
  have hA : 0 < k := by exact_mod_cast hk0
  have hB : k < 1 := by exact_mod_cast hk1
  omega

/-- The descending Gamma recursion in product form. -/
theorem gamma_eq_prod_mul_gamma_sub {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) (k : ℕ) :
    Complex.Gamma s = (∏ i ∈ Finset.range k, (s - 1 - (i : ℂ))) * Complex.Gamma (s - (k : ℂ)) := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hne : (s - (k : ℂ) - 1) ≠ 0 := by
        intro hcon
        have hre : (s - (k : ℂ) - 1).re = 0 := by rw [hcon]; simp
        simp only [Complex.sub_re, Complex.natCast_re, Complex.one_re] at hre
        have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
        linarith
      have hg := Complex.Gamma_add_one (s - (k : ℂ) - 1) hne
      rw [show (s - (k : ℂ) - 1 + 1) = s - (k : ℂ) by ring] at hg
      rw [ih, hg, Finset.prod_range_succ]
      push_cast
      ring

/-- Euler reflection along the descending Gamma recursion. -/
theorem gamma_reflect_prod {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) (k : ℕ) :
    Complex.Gamma (1 - s) * Complex.Gamma (s - (k : ℂ))
        * (∏ i ∈ Finset.range k, (s - 1 - (i : ℂ))) * Complex.sin (↑Real.pi * s)
      = ↑Real.pi := by
  have hsin := sin_pi_mul_ne_zero h0 h1
  have hrefl := Complex.Gamma_mul_Gamma_one_sub s
  rw [gamma_eq_prod_mul_gamma_sub h0 h1 k] at hrefl
  have hmul : (∏ i ∈ Finset.range k, (s - 1 - (i : ℂ))) * Complex.Gamma (s - (k : ℂ))
      * Complex.Gamma (1 - s) * Complex.sin (↑Real.pi * s) = ↑Real.pi := by
    rw [hrefl, div_mul_cancel₀ _ hsin]
  linear_combination hmul

/-- The `k`-th regular Jonquière coefficient. -/
noncomputable def jonquiereRegCoeff (s : ℂ) (k : ℕ) : ℂ :=
  riemannZeta (s - (k : ℂ)) * I ^ k / (Nat.factorial k : ℂ)

/-- **The `k`-th channel identity.**  The archimedean weight carried by the `k`-th Taylor term of
the shift-difference series is exactly the `k`-th regular Jonquière coefficient. -/
theorem jonquiere_channel_coeff {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) (k : ℕ) :
    (((2 * Real.pi : ℝ)) : ℂ) ^ (-(1 - s) - (k : ℂ)) * Complex.Gamma (1 - s)
        * (Complex.exp (↑Real.pi * I * (1 - s) / 2)
            + (-1 : ℂ) ^ k * Complex.exp (-↑Real.pi * I * (1 - s) / 2))
        * shiftTaylorCoeff (1 - s) k * riemannZeta ((1 - s) + (k : ℂ))
      = jonquiereRegCoeff s k := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hT : (((2 * Real.pi : ℝ)) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by positivity)
  have hFne : ((Nat.factorial k : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hPine : ((Real.pi : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hpi.ne'
  -- the functional equation at `s - k`
  have hzne : ∀ n : ℕ, (s - (k : ℂ)) ≠ -(n : ℂ) := by
    intro n hcon
    have hre : (s - (k : ℂ)).re = -(n : ℝ) := by rw [hcon]; simp
    simp only [Complex.sub_re, Complex.natCast_re] at hre
    have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have hint : s.re = (k : ℝ) - (n : ℝ) := by linarith
    have hlt : ((k : ℤ) - (n : ℤ) : ℤ) < 1 := by
      have : ((k : ℤ) - (n : ℤ) : ℝ) < 1 := by push_cast; rw [← hint]; exact h1
      exact_mod_cast this
    have hgt : (0 : ℤ) < ((k : ℤ) - (n : ℤ) : ℤ) := by
      have : (0 : ℝ) < ((k : ℤ) - (n : ℤ) : ℝ) := by push_cast; rw [← hint]; exact h0
      exact_mod_cast this
    omega
  have hz1 : (s - (k : ℂ)) ≠ 1 := by
    intro hcon
    have hre : (s - (k : ℂ)).re = 1 := by rw [hcon]; simp
    simp only [Complex.sub_re, Complex.natCast_re] at hre
    have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith
  have hfe := riemannZeta_one_sub hzne hz1
  rw [show (1 : ℂ) - (s - (k : ℂ)) = (1 - s) + (k : ℂ) by ring] at hfe
  have hpow : (((2 * Real.pi : ℝ)) : ℂ) ^ (-(1 - s) - (k : ℂ))
      * ((2 * (Real.pi : ℂ))) ^ (-(s - (k : ℂ))) = (((Real.pi : ℝ)) : ℂ)⁻¹ * 2⁻¹ := by
    have hcast : ((2 * (Real.pi : ℂ))) = (((2 * Real.pi : ℝ)) : ℂ) := by push_cast; ring
    rw [hcast, ← Complex.cpow_add _ _ hT,
      show (-(1 - s) - (k : ℂ) + -(s - (k : ℂ))) = (-1 : ℂ) by ring,
      Complex.cpow_neg_one]
    push_cast
    field_simp
  have hphase := jonquiere_phase_identity s k
  have hgam := gamma_reflect_prod h0 h1 k
  have hcoeff : shiftTaylorCoeff (1 - s) k
      = (∏ i ∈ Finset.range k, (s - 1 - (i : ℂ))) / (Nat.factorial k : ℂ) := by
    rw [shiftTaylorCoeff]
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    ring
  rw [hfe, hcoeff, jonquiereRegCoeff]
  -- reduce to a polynomial identity
  set G : ℂ := Complex.Gamma (1 - s) with hG
  set H : ℂ := Complex.Gamma (s - (k : ℂ)) with hH
  set P : ℂ := ∏ i ∈ Finset.range k, (s - 1 - (i : ℂ)) with hP
  set S : ℂ := Complex.sin (↑Real.pi * s) with hS
  set C : ℂ := Complex.cos (↑Real.pi * (s - (k : ℂ)) / 2) with hC
  set B : ℂ := Complex.exp (↑Real.pi * I * (1 - s) / 2)
      + (-1 : ℂ) ^ k * Complex.exp (-↑Real.pi * I * (1 - s) / 2) with hB
  set Z : ℂ := riemannZeta (s - (k : ℂ)) with hZ
  set T : ℂ := (((2 * Real.pi : ℝ)) : ℂ) ^ (-(1 - s) - (k : ℂ)) with hTdef
  set U : ℂ := ((2 * (Real.pi : ℂ))) ^ (-(s - (k : ℂ))) with hU
  calc T * G * B * (P / (Nat.factorial k : ℂ)) * (2 * U * H * C * Z)
      = (2 * (T * U)) * (G * H * P * (B * C)) * Z / (Nat.factorial k : ℂ) := by ring
    _ = (2 * (((Real.pi : ℝ) : ℂ)⁻¹ * 2⁻¹)) * (G * H * P * (I ^ k * S)) * Z
          / (Nat.factorial k : ℂ) := by rw [hpow, hphase]
    _ = ((Real.pi : ℝ) : ℂ)⁻¹ * (G * H * P * S) * I ^ k * Z / (Nat.factorial k : ℂ) := by
        field_simp
    _ = ((Real.pi : ℝ) : ℂ)⁻¹ * ((Real.pi : ℝ) : ℂ) * I ^ k * Z / (Nat.factorial k : ℂ) := by
        rw [hgam]
    _ = Z * I ^ k / (Nat.factorial k : ℂ) := by
        field_simp

end RHTower
