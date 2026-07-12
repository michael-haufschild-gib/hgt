import GaloisForLFunctions.RHTower.XiCTaylorThetaTailMomentLogConvex

/-!
# Endpoint-atom obstruction for critical-Laguerre representations of the theta core

The first coefficients of every theta-tail core are completed theta-source moments. Their exact
log-convexity prevents any Hausdorff scale representation of a degree-at-least-four core from
having the greater-than-one-half endpoint atom used by Theorem M's sign-transfer argument.
-/

open Complex Real MeasureTheory Set Filter Topology Polynomial
namespace RHTower
noncomputable section

/-- Any decreasing candidate scale-moment sequence with the critical-Laguerre coefficient ratios
forced by the completed theta moments has endpoint mass at most `1/3` in degree `N ≥ 4`. -/
theorem thetaCoreCriticalLaguerre_endpointAtom_le_third
    (N : ℕ) (hN : 4 ≤ N) (M : ℕ → ℝ) (scaleSq p : ℝ)
    (hscale : 0 < scaleSq)
    (hM0 : M 0 = 1)
    (hMpos : ∀ k ≤ N, 0 < M k)
    (hManti : Antitone M)
    (hRatio : ∀ k ≤ N - 2,
      M (k + 1) / M k =
        (N : ℝ) *
            (thetaCuspRawEvenMoment (k + 1) / thetaCuspRawEvenMoment k) /
          (scaleSq * ((N - k : ℕ) : ℝ)))
    (hp : p ≤ M N) :
    p ≤ 1 / 3 := by
  let r : ℕ → ℝ := fun k =>
    thetaCuspRawEvenMoment (k + 1) / thetaCuspRawEvenMoment k
  have hrmono : Monotone r := monotone_nat_of_le_succ fun k => by
    exact thetaCuspRawEvenMoment_ratio_mono k
  have hNm2 : N - 2 ≤ N := Nat.sub_le N 2
  have hNm1 : N - 1 ≤ N := Nat.sub_le N 1
  have hNm2pos : 0 < M (N - 2) := hMpos _ hNm2
  have hNm1le : M (N - 1) ≤ M (N - 2) := by
    apply hManti
    omega
  have hquotA : M (N - 1) / M (N - 2) ≤ 1 := by
    rw [div_le_one hNm2pos]
    exact hNm1le
  have hratioA := hRatio (N - 2) (le_refl _)
  have hsubA : N - (N - 2) = 2 := by omega
  have hsuccA : N - 2 + 1 = N - 1 := by omega
  rw [hsuccA, hsubA] at hratioA
  have hA : (N : ℝ) * r (N - 2) ≤ 2 * scaleSq := by
    rw [hratioA] at hquotA
    have hden : 0 < scaleSq * (2 : ℝ) := mul_pos hscale (by norm_num)
    have hquotA' : (N : ℝ) * r (N - 2) / (scaleSq * 2) ≤ 1 := by
      simpa only [r, hsuccA, Nat.cast_ofNat] using hquotA
    have hraw := (div_le_one hden).mp hquotA'
    nlinarith
  have hratioBound (k : ℕ) (hk : k ≤ 2) :
      M (k + 1) / M k ≤ 2 / ((N - k : ℕ) : ℝ) := by
    have hkN2 : k ≤ N - 2 := by omega
    have hrk : r k ≤ r (N - 2) := hrmono hkN2
    have hNkpos : 0 < ((N - k : ℕ) : ℝ) := by
      exact_mod_cast (show 0 < N - k by omega)
    have hratioK := hRatio k hkN2
    rw [hratioK]
    have hnum : (N : ℝ) * r k ≤ 2 * scaleSq := by
      have hNR : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
      exact (mul_le_mul_of_nonneg_left hrk hNR).trans hA
    rw [div_le_div_iff₀ (mul_pos hscale hNkpos) hNkpos]
    calc
      (N : ℝ) * r k * ((N - k : ℕ) : ℝ) ≤
          (2 * scaleSq) * ((N - k : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_right hnum hNkpos.le
      _ = 2 * (scaleSq * ((N - k : ℕ) : ℝ)) := by ring
  have hstep (k : ℕ) (hk : k ≤ 2) :
      ((N - k : ℕ) : ℝ) * M (k + 1) ≤ 2 * M k := by
    have hkN : k ≤ N := by omega
    have hMk : 0 < M k := hMpos k hkN
    have hNkpos : 0 < ((N - k : ℕ) : ℝ) := by
      exact_mod_cast (show 0 < N - k by omega)
    have h := hratioBound k hk
    rw [div_le_div_iff₀ hMk hNkpos] at h
    nlinarith
  have h0 := hstep 0 (by norm_num)
  have h1 := hstep 1 (by norm_num)
  have h2 := hstep 2 (by norm_num)
  simp only [Nat.sub_zero] at h0
  have hcast1 : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]
    norm_num
  have hcast2 : ((N - 2 : ℕ) : ℝ) = (N : ℝ) - 2 := by
    rw [Nat.cast_sub (by omega)]
    norm_num
  rw [hcast1] at h1
  rw [hcast2] at h2
  rw [hM0] at h0
  have hM1 : 0 < M 1 := hMpos 1 (by omega)
  have hM2 : 0 < M 2 := hMpos 2 (by omega)
  have hM3 : 0 < M 3 := hMpos 3 (by omega)
  have hNR : (4 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hN0 : (0 : ℝ) ≤ (N : ℝ) := by positivity
  have hNm10 : (0 : ℝ) ≤ (N : ℝ) - 1 := by linarith
  have hM1bound : (N : ℝ) * M 1 ≤ 2 := by simpa using h0
  have hM2bound : ((N : ℝ) * ((N : ℝ) - 1)) * M 2 ≤ 4 := by
    have hmul := mul_le_mul_of_nonneg_left h1 hN0
    calc
      ((N : ℝ) * ((N : ℝ) - 1)) * M 2 ≤
          2 * ((N : ℝ) * M 1) := by nlinarith
      _ ≤ 2 * 2 := mul_le_mul_of_nonneg_left hM1bound (by norm_num)
      _ = 4 := by norm_num
  have hM3bound :
      ((N : ℝ) * ((N : ℝ) - 1) * ((N : ℝ) - 2)) * M 3 ≤ 8 := by
    have hmul := mul_le_mul_of_nonneg_left h2
      (mul_nonneg hN0 hNm10)
    calc
      ((N : ℝ) * ((N : ℝ) - 1) * ((N : ℝ) - 2)) * M 3 ≤
          2 * (((N : ℝ) * ((N : ℝ) - 1)) * M 2) := by nlinarith
      _ ≤ 2 * 4 := mul_le_mul_of_nonneg_left hM2bound (by norm_num)
      _ = 8 := by norm_num
  have hprod : 24 ≤ (N : ℝ) * ((N : ℝ) - 1) * ((N : ℝ) - 2) := by
    have hfac : 0 ≤ ((N : ℝ) - 4) *
        ((N : ℝ) ^ 2 + (N : ℝ) + 6) := by positivity
    nlinarith
  have hM3third : M 3 ≤ 1 / 3 := by
    have hmul := mul_le_mul_of_nonneg_right hprod hM3.le
    nlinarith [hmul.trans hM3bound]
  have h3N : 3 ≤ N := by omega
  have hMN3 : M N ≤ M 3 := hManti h3N
  exact hp.trans (hMN3.trans hM3third)

end
end RHTower

