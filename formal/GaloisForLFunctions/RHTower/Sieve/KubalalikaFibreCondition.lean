import GaloisForLFunctions.RHTower.Sieve.KubalalikaPowerEnvelope

/-!
# The second-derivative fibre condition at a large reciprocal scale

The mixed second/third-derivative block estimate demands, for each fibre `b`, that the second
derivative test be legitimate whenever the second-derivative kernel is the dominant part of the
fibre envelope.  The crossover hypothesis `fibreKernel ≤ C₁ b^{-1/2}` caps `b` by
`b ≪ A^{5/3}(Tr)^{-2/3}`, and the resulting curvature `T r b² ≪ A^{10/3}(Tr)^{-1/3}` stays below
`36 π A³` as soon as the reciprocal scale `T r` dominates the block scale `A` by an absolute
factor.  Written in the cube roots `p = A^{1/3}` and `q = (Tr)^{1/3}` every step is polynomial.
-/

namespace RHTower.Sieve

open Finset RHTower

noncomputable section

/-- `A` is at most `b` times the ceiling of `A/b` used by the fibre decomposition. -/
theorem cast_le_mul_pred_div_add_one {A b : ℕ} (hA : 1 ≤ A) (hb : 1 ≤ b) :
    (A : ℝ) ≤ (b : ℝ) * (((A - 1) / b + 1 : ℕ) : ℝ) := by
  have hnat : A ≤ b * ((A - 1) / b + 1) := by
    have h1 : b * ((A - 1) / b) + (A - 1) % b = A - 1 := Nat.div_add_mod (A - 1) b
    have h2 : (A - 1) % b < b := Nat.mod_lt _ hb
    have h3 : b * ((A - 1) / b + 1) = b * ((A - 1) / b) + b := by ring
    set P := b * ((A - 1) / b) with hP
    set s := (A - 1) % b with hs
    omega
  calc (A : ℝ) ≤ ((b * ((A - 1) / b + 1) : ℕ) : ℝ) := by exact_mod_cast hnat
    _ = (b : ℝ) * (((A - 1) / b + 1 : ℕ) : ℝ) := by push_cast; ring

/-- The cube of a cube root. -/
theorem rpow_third_cube {x : ℝ} (hx : 0 < x) : (x ^ (1 / 3 : ℝ)) ^ 3 = x := by
  rw [← Real.rpow_natCast (x ^ (1 / 3 : ℝ)) 3, ← Real.rpow_mul hx.le]
  norm_num

/-- **The second-derivative fibre condition holds at every crossover fibre.**

If the reciprocal scale exceeds the block scale by the absolute factor `10^27`, then on every
fibre where the second-derivative kernel still dominates the envelope the curvature parameter of
the contracted block is at most one. -/
theorem nearDiagonalLambda_le_one_of_fibre_crossover {T r : ℝ} (hT : 0 < T) (hr : 0 < r)
    {A b : ℕ} (hA : 1 ≤ A) (hb : 1 ≤ b)
    (hAX : (10 : ℝ) ^ 27 * (A : ℝ) ≤ T * r)
    (hcross : fibreKernel T r A
      ≤ secondThirdMixedFibreMainCoefficient T r A * (b : ℝ) ^ (-(1 / 2 : ℝ))) :
    nearDiagonalLambda T (r / b) ((((A - 1) / b + 1 : ℕ)) : ℝ) ≤ 1 := by
  have ha0 : (0 : ℝ) < (A : ℝ) := by exact_mod_cast hA
  have hb0 : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  have hX : (0 : ℝ) < T * r := by positivity
  have hpi3 : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hpi4 : Real.pi ≤ 4 := Real.pi_le_four
  set c : ℝ := 36 * Real.pi with hcdef
  have hc0 : (108 : ℝ) < c := by rw [hcdef]; linarith
  have hc1 : c ≤ 144 := by rw [hcdef]; linarith
  set p : ℝ := (A : ℝ) ^ (1 / 3 : ℝ) with hpdef
  set q : ℝ := (T * r) ^ (1 / 3 : ℝ) with hqdef
  have hp0 : (0 : ℝ) < p := Real.rpow_pos_of_pos ha0 _
  have hq0 : (0 : ℝ) < q := Real.rpow_pos_of_pos hX _
  have hp3 : p ^ 3 = (A : ℝ) := rpow_third_cube ha0
  have hq3 : q ^ 3 = T * r := rpow_third_cube hX
  -- the crossover caps the fibre
  have hsqrtb : ((b : ℝ)) ^ (-(1 / 2 : ℝ)) = (Real.sqrt (b : ℝ))⁻¹ := by
    rw [Real.rpow_neg hb0.le, Real.sqrt_eq_rpow]
  have hsb0 : (0 : ℝ) < Real.sqrt (b : ℝ) := Real.sqrt_pos.2 hb0
  have hK : fibreKernel T r A = 2500 * Real.sqrt ((T * r) / (c * (A : ℝ))) := by
    rw [fibreKernel, hcdef]
  have hC1nn : (0 : ℝ) ≤ secondThirdMixedFibreMainCoefficient T r A := by
    rw [secondThirdMixedFibreMainCoefficient]
    exact add_nonneg (sharpThirdDerivativeFibreFirstCoefficient_nonneg hT hr hA)
      (Real.sqrt_nonneg _)
  have hmul : 2500 * Real.sqrt ((T * r) / (c * (A : ℝ))) * Real.sqrt (b : ℝ)
      ≤ secondThirdMixedFibreMainCoefficient T r A := by
    have h := mul_le_mul_of_nonneg_right (hK ▸ hcross) hsb0.le
    rw [hsqrtb] at h
    calc 2500 * Real.sqrt ((T * r) / (c * (A : ℝ))) * Real.sqrt (b : ℝ)
        ≤ secondThirdMixedFibreMainCoefficient T r A * (Real.sqrt (b : ℝ))⁻¹
            * Real.sqrt (b : ℝ) := h
      _ = secondThirdMixedFibreMainCoefficient T r A := by
          field_simp
  -- square both sides
  have hlhs0 : (0 : ℝ) ≤ 2500 * Real.sqrt ((T * r) / (c * (A : ℝ))) * Real.sqrt (b : ℝ) := by
    positivity
  have hsq : (2500 * Real.sqrt ((T * r) / (c * (A : ℝ))) * Real.sqrt (b : ℝ)) ^ 2
      ≤ (secondThirdMixedFibreMainCoefficient T r A) ^ 2 :=
    pow_le_pow_left₀ hlhs0 hmul 2
  have hlhsval : (2500 * Real.sqrt ((T * r) / (c * (A : ℝ))) * Real.sqrt (b : ℝ)) ^ 2
      = 6250000 * ((T * r) / (c * (A : ℝ))) * (b : ℝ) := by
    have h1 : (Real.sqrt ((T * r) / (c * (A : ℝ)))) ^ 2 = (T * r) / (c * (A : ℝ)) :=
      Real.sq_sqrt (by positivity)
    have h2 : (Real.sqrt (b : ℝ)) ^ 2 = (b : ℝ) := Real.sq_sqrt hb0.le
    rw [mul_pow, mul_pow, h1, h2]
    ring
  have hC1le := secondThirdMixedFibreMainCoefficient_le hT hr hA
  have hXsix : ((T * r) ^ (1 / 6 : ℝ)) ^ 2 = q := by
    rw [rpow_sq_half hX, hqdef]
    norm_num
  have hC1sq : (secondThirdMixedFibreMainCoefficient T r A) ^ 2
      ≤ 10000000000 * p ^ 2 * q := by
    have h := pow_le_pow_left₀ hC1nn hC1le 2
    have hval : (100000 * (A : ℝ) ^ (1 / 3 : ℝ) * (T * r) ^ (1 / 6 : ℝ)) ^ 2
        = 10000000000 * p ^ 2 * q := by
      rw [mul_pow, mul_pow, hXsix, hpdef]
      ring
    rwa [hval] at h
  -- the polynomial core
  have hcore : 6250000 * ((T * r) / (c * (A : ℝ))) * (b : ℝ) ≤ 10000000000 * p ^ 2 * q := by
    rw [← hlhsval]
    exact le_trans hsq hC1sq
  have hcp3 : (0 : ℝ) < c * p ^ 3 := by
    rw [hp3]; positivity
  have hstep8 : 6250000 * q ^ 3 * (b : ℝ) ≤ 10000000000 * c * p ^ 5 * q := by
    have h := mul_le_mul_of_nonneg_right hcore hcp3.le
    have hl : 6250000 * ((T * r) / (c * (A : ℝ))) * (b : ℝ) * (c * p ^ 3)
        = 6250000 * q ^ 3 * (b : ℝ) := by
      rw [hp3, ← hq3]
      field_simp
    have hrr : 10000000000 * p ^ 2 * q * (c * p ^ 3) = 10000000000 * c * p ^ 5 * q := by ring
    rw [hl, hrr] at h
    exact h
  have hstep9 : 6250000 * q ^ 2 * (b : ℝ) ≤ 10000000000 * c * p ^ 5 := by
    have h : (6250000 * q ^ 2 * (b : ℝ)) * q ≤ (10000000000 * c * p ^ 5) * q := by
      calc (6250000 * q ^ 2 * (b : ℝ)) * q = 6250000 * q ^ 3 * (b : ℝ) := by ring
        _ ≤ 10000000000 * c * p ^ 5 * q := hstep8
        _ = (10000000000 * c * p ^ 5) * q := by ring
    exact le_of_mul_le_mul_right h hq0
  have hq2b : q ^ 2 * (b : ℝ) ≤ 1600 * c * p ^ 5 := by linarith
  have hq2b0 : (0 : ℝ) ≤ q ^ 2 * (b : ℝ) := by positivity
  have hsquare : (q ^ 2 * (b : ℝ)) ^ 2 ≤ (1600 * c * p ^ 5) ^ 2 :=
    pow_le_pow_left₀ hq2b0 hq2b 2
  -- the scale separation
  have hpq : 1000000000 * p ≤ q := by
    have hcube : (1000000000 * p) ^ 3 ≤ q ^ 3 := by
      calc (1000000000 * p) ^ 3 = (10 : ℝ) ^ 27 * p ^ 3 := by ring
        _ = (10 : ℝ) ^ 27 * (A : ℝ) := by rw [hp3]
        _ ≤ T * r := hAX
        _ = q ^ 3 := hq3.symm
    exact le_of_pow_le_pow_left₀ (by norm_num) hq0.le hcube
  -- assemble
  have hkey : q ^ 3 * (b : ℝ) ^ 2 ≤ c * p ^ 9 := by
    have h1 : (q ^ 3 * (b : ℝ) ^ 2) * q ≤ (c * p ^ 9) * q := by
      have hA1 : (q ^ 3 * (b : ℝ) ^ 2) * q = (q ^ 2 * (b : ℝ)) ^ 2 := by ring
      have hA2 : (1600 * c * p ^ 5) ^ 2 = 2560000 * c ^ 2 * p ^ 10 := by ring
      have hA3 : 2560000 * c ^ 2 * p ^ 10 ≤ (c * p ^ 9) * q := by
        have hcp : (0 : ℝ) < c * p ^ 9 := by positivity
        have hfin : 2560000 * c * p ≤ q := by
          have : 2560000 * c ≤ 1000000000 := by linarith
          nlinarith only [this, hp0, hpq]
        have := mul_le_mul_of_nonneg_left hfin hcp.le
        nlinarith only [this]
      rw [hA1]
      exact le_trans (le_trans hsquare (le_of_eq hA2)) hA3
    exact le_of_mul_le_mul_right h1 hq0
  -- back to the curvature parameter
  set M : ℝ := (((A - 1) / b + 1 : ℕ) : ℝ) with hMdef
  have hM0 : (0 : ℝ) < M := by
    rw [hMdef]
    have : (0 : ℕ) < (A - 1) / b + 1 := Nat.succ_pos _
    exact_mod_cast this
  have hMge : (A : ℝ) ≤ (b : ℝ) * M := cast_le_mul_pred_div_add_one hA hb
  have hcube : (A : ℝ) ^ 3 ≤ (b : ℝ) ^ 3 * M ^ 3 := by
    have h := pow_le_pow_left₀ ha0.le hMge 3
    calc (A : ℝ) ^ 3 ≤ ((b : ℝ) * M) ^ 3 := h
      _ = (b : ℝ) ^ 3 * M ^ 3 := by ring
  have hXb : (T * r) * (b : ℝ) ^ 2 ≤ c * ((b : ℝ) ^ 3 * M ^ 3) := by
    have h1 : (T * r) * (b : ℝ) ^ 2 = q ^ 3 * (b : ℝ) ^ 2 := by rw [hq3]
    have h2 : c * (A : ℝ) ^ 3 = c * p ^ 9 := by
      rw [← hp3]; ring
    have h3 : c * (A : ℝ) ^ 3 ≤ c * ((b : ℝ) ^ 3 * M ^ 3) :=
      mul_le_mul_of_nonneg_left hcube (by linarith)
    rw [h1]
    exact le_trans (h2 ▸ hkey) h3
  rw [nearDiagonalLambda, ← hcdef, div_le_one (by positivity)]
  have hfinal : T * (r / (b : ℝ)) * (b : ℝ) ^ 2 ≤ c * M ^ 3 * (b : ℝ) ^ 2 := by
    have hl : T * (r / (b : ℝ)) * (b : ℝ) ^ 2 = (T * r) * (b : ℝ) := by
      field_simp
    have hrr : c * ((b : ℝ) ^ 3 * M ^ 3) = (c * M ^ 3 * (b : ℝ) ^ 2) * (b : ℝ) := by ring
    have hstep : (T * r) * (b : ℝ) * (b : ℝ) ≤ (c * M ^ 3 * (b : ℝ) ^ 2) * (b : ℝ) := by
      calc (T * r) * (b : ℝ) * (b : ℝ) = (T * r) * (b : ℝ) ^ 2 := by ring
        _ ≤ c * ((b : ℝ) ^ 3 * M ^ 3) := hXb
        _ = (c * M ^ 3 * (b : ℝ) ^ 2) * (b : ℝ) := hrr
    rw [hl]
    exact le_of_mul_le_mul_right hstep hb0
  have hb2 : (0 : ℝ) < (b : ℝ) ^ 2 := by positivity
  exact le_of_mul_le_mul_right hfinal hb2

/-- **The mixed hybrid block estimate with the fibre condition discharged.**

Once the reciprocal scale dominates the block scale the second-derivative crossover condition is
automatic, so the block estimate holds with purely scalar hypotheses. -/
theorem exists_norm_sum_vonMangoldt_ndPhaseExp_le_kubalalika_power' :
    ∃ D : ℝ, 0 < D ∧ ∀ {T r : ℝ} {A B U V : ℕ},
      0 < T → 0 < r → 1 ≤ A → A ≤ B → B ≤ 2 * A → 1 ≤ U → 1 ≤ V → U < A →
      U * V ≤ A → 8 * r ≤ (A : ℝ) →
      T * r * ((U * V : ℕ) : ℝ) ^ 3 ≤ 72 * Real.pi * (A : ℝ) ^ 4 →
      (10 : ℝ) ^ 27 * (A : ℝ) ≤ T * r →
      ‖∑ n ∈ Finset.Ico A B, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * ndPhaseExp T r n‖
        ≤ kubalalikaBlockPower D T r A B U V := by
  obtain ⟨D, hD0, hbound⟩ := exists_norm_sum_vonMangoldt_ndPhaseExp_le_kubalalika_power
  refine ⟨D, hD0, ?_⟩
  intro T r A B U V hT hr hA hAB hBA hU hV hUA hUVA h8 hcurv hAX
  refine hbound hT hr hA hAB hBA hU hV hUA hUVA h8 hcurv ?_
  intro b hb hcross
  have hb1 : 1 ≤ b := (Finset.mem_Icc.mp hb).1
  exact nearDiagonalLambda_le_one_of_fibre_crossover hT hr hA hb1 hAX hcross

end

end RHTower.Sieve
