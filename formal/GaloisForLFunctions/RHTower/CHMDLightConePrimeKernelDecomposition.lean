import GaloisForLFunctions.HTGeometry.KleinGordonLightConeBesselKernel
import GaloisForLFunctions.RHTower.CHMDDAlembertSechKernel
import GaloisForLFunctions.RHTower.CHMDStage22PrimeWaveGrowthLawAndTwoPointSumCriterion

/-!
# CHMD: the light-cone decomposition of the prime kernel

The CHMD causal wave `φ_Λ(y) = chmdWave y` has the three-part form
`φ_Λ = (pole) + (1/2π)(archimedean) − (prime)`, where every part is a sech²-weighted Klein–Gordon
integral `∫ cos(y√(r²+2)) sech²(r/2) g(r) dr`, and the prime part is
`Σ_n (Λ(n)/√n) K_y(log n)` with the prime kernel

`K_y(u) = (1/π) ∫ cos(y√(r²+2)) sech²(r/2) cos(r u) dr`   (`chmdPrimeKernel`).

The Klein–Gordon light-cone identity (`cos_mul_sqrt_eq_lightCone`, mass² `= 2`) splits every such
integral into its **free d'Alembert part** and its **dispersive Bessel tail**
(`integral_cos_sqrt_mul_sechSqHalf_mul_eq`).  With the d'Alembert kernel `D(v) = 2v/sinh(πv)` and the
entire Bessel kernel `B(w) = Σ (−w/4)^k/(k!(k+1)!)` (`J₁(x) = (x/2)B(x²)`):

* **Prime kernel** (`chmdPrimeKernel_eq_lightCone`, `chmdPrimeKernel_eq_free_sub_tail`):
  `K_y(u) = D(u+y) + D(u−y) − y² ∫_{−1}^{1} B(2y²(1−t²)) D(u − yt) dt`.
  The free part is a pair of positive translates (`dAlembertReal_pos`); the whole sign structure
  of the prime channel is carried by the Bessel tail inside the light cone `|s| < y`.
* **Light-cone transmutation** (`lightConeTransmute`):
  `L[A](y) = A(y) − (y²/2) ∫_{−1}^{1} B(2y²(1−t²)) A(yt) dt`.  The three parts of the causal wave are
  the transmutations of their massless counterparts:
  `chmdPoleWave = L[(2/cos²(1/4)) cosh(·/2)]` (`chmdPoleWave_eq_lightConeTransmute`),
  `chmdArchWave = L[A₀]`, `A₀(v) = ∫ cos(vr) sech²(r/2) γ(r) dr` (`chmdArchWave_eq_lightConeTransmute`),
  `chmdPrimeWave = L[P₀]` with the **d'Alembert prime wave**
  `P₀(v) = Σ_n (Λ(n)/√n)(D(log n + v) + D(log n − v)) > 0`
  (`chmdPrimeWave_eq_lightConeTransmute`, `masslessPrimeWave_pos`).

So the prime side of the causal wave is a strictly positive free wave minus its dispersive tail:
`chmdPrimeWave y = P₀(y) − (y²/2) ∫_{−1}^{1} B(2y²(1−t²)) P₀(yt) dt`.
-/

open Complex MeasureTheory Set Filter Topology
open scoped Real
open GaloisForLFunctions.HTGeometry Zeta23

noncomputable section

namespace RHTower.CHMDLightCone

open RHTower.CHMDStage22

/-! ## The light-cone transmutation -/

/-- The light-cone transmutation `L[A](y) = A(y) − (y²/2) ∫_{−1}^{1} B(2y²(1−t²)) A(yt) dt`. -/
def lightConeTransmute (A : ℝ → ℝ) (y : ℝ) : ℝ :=
  A y - y ^ 2 / 2 * ∫ t in (-1 : ℝ)..1, lightConeBesselReal (2 * y ^ 2 * (1 - t ^ 2)) * A (y * t)

theorem abs_lightConeBesselReal_light_cone_le (y : ℝ) {t : ℝ} (ht : |t| ≤ 1) :
    |lightConeBesselReal (2 * y ^ 2 * (1 - t ^ 2))| ≤ Real.exp (y ^ 2 / 2) := by
  refine (abs_lightConeBesselReal_le _).trans (Real.exp_le_exp.mpr ?_)
  have ht2 : t ^ 2 ≤ 1 := by nlinarith [abs_nonneg t, sq_abs t]
  rw [abs_of_nonneg (by nlinarith [sq_nonneg y, sq_nonneg t])]
  nlinarith [sq_nonneg y, sq_nonneg t]

theorem mem_uIoc_neg_one_one_abs_le {t : ℝ} (ht : t ∈ Set.uIoc (-1 : ℝ) 1) : |t| ≤ 1 := by
  rw [Set.uIoc_of_le (by norm_num)] at ht
  exact abs_le.mpr ⟨ht.1.le, ht.2⟩

/-! ## Light-cone splitting of sech²-weighted Klein–Gordon integrals -/

/-- **Light-cone splitting.**  For continuous `g` with `sech²(r/2) g(r)` integrable,
`∫ cos(y√(r²+2)) sech² g = ∫ cos(yr) sech² g − (y²/2) ∫_{−1}^{1} B(2y²(1−t²)) ∫ cos(ytr) sech² g dr dt`. -/
theorem integral_cos_sqrt_mul_sechSqHalf_mul_eq (y : ℝ) {g : ℝ → ℝ} (hg : Continuous g)
    (hgi : Integrable fun r => sechSqHalf r * g r) :
    ∫ r, Real.cos (y * Real.sqrt (r ^ 2 + 2)) * sechSqHalf r * g r =
      (∫ r, Real.cos (y * r) * sechSqHalf r * g r) -
        y ^ 2 / 2 * ∫ t in (-1 : ℝ)..1, lightConeBesselReal (2 * y ^ 2 * (1 - t ^ 2)) *
          ∫ r, Real.cos (y * t * r) * sechSqHalf r * g r := by
  set Bt : ℝ → ℝ := fun t => lightConeBesselReal (2 * y ^ 2 * (1 - t ^ 2)) with hBt
  set I : ℝ → ℝ := fun r => ∫ t in (-1 : ℝ)..1, Bt t * Real.cos (y * r * t) with hI
  have hBc : Continuous Bt := continuous_lightConeBesselReal.comp (by fun_prop)
  have hlc : ∀ r, Real.cos (y * Real.sqrt (r ^ 2 + 2)) = Real.cos (y * r) - y ^ 2 / 2 * I r := by
    intro r
    rw [cos_mul_sqrt_eq_lightCone y r 2 (by norm_num)]
    simp only [hI, hBt]
    ring_nf
  have hIc : Continuous I :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun r t => Bt t * Real.cos (y * r * t)) (by fun_prop) _ _
  have hIb : ∀ r, ‖I r‖ ≤ Real.exp (y ^ 2 / 2) * 2 := by
    intro r
    have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := (-1 : ℝ)) (b := 1)
      (C := Real.exp (y ^ 2 / 2)) (f := fun t => Bt t * Real.cos (y * r * t)) fun t ht => by
        rw [Real.norm_eq_abs, abs_mul]
        simpa using mul_le_mul (abs_lightConeBesselReal_light_cone_le y
          (mem_uIoc_neg_one_one_abs_le ht)) (Real.abs_cos_le_one _) (abs_nonneg _)
          (Real.exp_pos _).le
    simpa [abs_of_pos (by norm_num : (0 : ℝ) < 1 - -1), show (1 : ℝ) - -1 = 2 by norm_num] using h
  have hint1 : Integrable fun r => Real.cos (y * r) * sechSqHalf r * g r := by
    refine hgi.norm.mono' (((by fun_prop : Continuous fun r : ℝ => Real.cos (y * r)).mul
      continuous_sechSqHalf).mul hg).aestronglyMeasurable (Eventually.of_forall fun r => ?_)
    rw [mul_assoc, norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (by
      rw [Real.norm_eq_abs]; exact Real.abs_cos_le_one _)
  have hint2 : Integrable fun r => I r * (sechSqHalf r * g r) := by
    refine (hgi.norm.const_mul (Real.exp (y ^ 2 / 2) * 2)).mono'
      (hIc.aestronglyMeasurable.mul (continuous_sechSqHalf.mul hg).aestronglyMeasurable)
      (Eventually.of_forall fun r => ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hIb r) (norm_nonneg _)
  -- Fubini on `[-1,1] × ℝ`
  have hprod : Integrable (Function.uncurry fun t r =>
      Bt t * (Real.cos (y * r * t) * (sechSqHalf r * g r)))
      ((volume.restrict (Set.uIoc (-1 : ℝ) 1)).prod volume) := by
    refine (Integrable.mul_prod (f := fun t => ‖Bt t‖) (g := fun r => ‖sechSqHalf r * g r‖)
      hBc.norm.integrableOn_uIoc hgi.norm).mono'
      (by
        refine Continuous.aestronglyMeasurable ?_
        exact (hBc.comp continuous_fst).mul ((by fun_prop : Continuous fun p : ℝ × ℝ =>
          Real.cos (y * p.2 * p.1)).mul ((continuous_sechSqHalf.comp continuous_snd).mul
            (hg.comp continuous_snd))))
      (Eventually.of_forall fun p => ?_)
    rcases p with ⟨t, r⟩
    simp only [Function.uncurry_apply_pair, norm_mul]
    have hcos : ‖Real.cos (y * r * t)‖ ≤ 1 := by
      rw [Real.norm_eq_abs]; exact Real.abs_cos_le_one _
    exact mul_le_mul_of_nonneg_left (mul_le_of_le_one_left (by positivity) hcos) (norm_nonneg _)
  have hswap := MeasureTheory.intervalIntegral_integral_swap hprod
  have hleft : ∫ r, I r * (sechSqHalf r * g r) =
      ∫ r, ∫ t in (-1 : ℝ)..1, Bt t * (Real.cos (y * r * t) * (sechSqHalf r * g r)) := by
    refine integral_congr_ae (Eventually.of_forall fun r => ?_)
    simp only [hI]
    rw [← intervalIntegral.integral_mul_const]
    refine intervalIntegral.integral_congr fun t _ => ?_
    ring
  have hright : ∀ t, ∫ r, Bt t * (Real.cos (y * r * t) * (sechSqHalf r * g r)) =
      Bt t * ∫ r, Real.cos (y * t * r) * sechSqHalf r * g r := by
    intro t
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun r => ?_)
    simp only
    rw [show y * r * t = y * t * r by ring]
    ring
  calc ∫ r, Real.cos (y * Real.sqrt (r ^ 2 + 2)) * sechSqHalf r * g r
      = ∫ r, (Real.cos (y * r) * sechSqHalf r * g r - y ^ 2 / 2 * (I r * (sechSqHalf r * g r))) := by
        refine integral_congr_ae (Eventually.of_forall fun r => ?_)
        simp only
        rw [hlc r]
        ring
    _ = (∫ r, Real.cos (y * r) * sechSqHalf r * g r) -
          y ^ 2 / 2 * ∫ r, I r * (sechSqHalf r * g r) := by
        rw [integral_sub hint1 (hint2.const_mul _), integral_const_mul]
    _ = _ := by
        rw [hleft, ← hswap]
        simp_rw [hright]
        rfl

/-! ## The prime kernel -/

/-- The CHMD prime kernel `K_y(u) = (1/π) ∫ cos(y√(r²+2)) sech²(r/2) cos(r u) dr`. -/
def chmdPrimeKernel (y u : ℝ) : ℝ :=
  1 / π * ∫ r : ℝ, Real.cos (y * Real.sqrt (r ^ 2 + 2)) * sechSqHalf r * Real.cos (r * u)

/-- **Light-cone decomposition of the prime kernel.** -/
theorem chmdPrimeKernel_eq_lightCone (y u : ℝ) :
    chmdPrimeKernel y u = dAlembertReal (u + y) + dAlembertReal (u - y) -
      y ^ 2 / 2 * ∫ t in (-1 : ℝ)..1, lightConeBesselReal (2 * y ^ 2 * (1 - t ^ 2)) *
        (dAlembertReal (u + y * t) + dAlembertReal (u - y * t)) := by
  have hgi : Integrable fun r => sechSqHalf r * Real.cos (r * u) :=
    integrable_sechSqHalf_mul (by fun_prop) fun r => Real.abs_cos_le_one _
  unfold chmdPrimeKernel
  rw [integral_cos_sqrt_mul_sechSqHalf_mul_eq y (by fun_prop) hgi, mul_sub,
    integral_cos_mul_sechSqHalf_mul_cos]
  congr 1
  rw [← mul_assoc, mul_comm (1 / π) (y ^ 2 / 2), mul_assoc, ← intervalIntegral.integral_const_mul]
  congr 1
  refine intervalIntegral.integral_congr fun t _ => ?_
  rw [← integral_cos_mul_sechSqHalf_mul_cos (y * t) u]
  ring

theorem integral_lightConeBesselReal_mul_dAlembert_add_eq (y u : ℝ) :
    ∫ t in (-1 : ℝ)..1, lightConeBesselReal (2 * y ^ 2 * (1 - t ^ 2)) * dAlembertReal (u + y * t) =
      ∫ t in (-1 : ℝ)..1, lightConeBesselReal (2 * y ^ 2 * (1 - t ^ 2)) *
        dAlembertReal (u - y * t) := by
  have h := intervalIntegral.integral_comp_neg (a := (-1 : ℝ)) (b := 1)
    (fun t => lightConeBesselReal (2 * y ^ 2 * (1 - t ^ 2)) * dAlembertReal (u - y * t))
  simp only [neg_neg, neg_sq, mul_neg, sub_neg_eq_add] at h
  exact h

/-- **Free part minus dispersive tail**:
`K_y(u) = D(u+y) + D(u−y) − y² ∫_{−1}^{1} B(2y²(1−t²)) D(u − yt) dt`. -/
theorem chmdPrimeKernel_eq_free_sub_tail (y u : ℝ) :
    chmdPrimeKernel y u = dAlembertReal (u + y) + dAlembertReal (u - y) -
      y ^ 2 * ∫ t in (-1 : ℝ)..1, lightConeBesselReal (2 * y ^ 2 * (1 - t ^ 2)) *
        dAlembertReal (u - y * t) := by
  have hc : ∀ s : ℝ → ℝ, Continuous s → IntervalIntegrable
      (fun t => lightConeBesselReal (2 * y ^ 2 * (1 - t ^ 2)) * s t) volume (-1) 1 :=
    fun s hs => (Continuous.intervalIntegrable
      ((continuous_lightConeBesselReal.comp (by fun_prop)).mul hs) _ _)
  rw [chmdPrimeKernel_eq_lightCone]
  simp_rw [mul_add]
  rw [intervalIntegral.integral_add
      (hc (fun t => dAlembertReal (u + y * t)) (continuous_dAlembertReal.comp (by fun_prop)))
      (hc (fun t => dAlembertReal (u - y * t)) (continuous_dAlembertReal.comp (by fun_prop))),
    integral_lightConeBesselReal_mul_dAlembert_add_eq]
  ring

/-! ## The d'Alembert prime wave -/

/-- The prime weights `Λ(n)/√n` (`n ≥ 2`). -/
def chmdPrimeWeight (n : ℕ) : ℝ :=
  if 2 ≤ n then (ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n else 0

theorem chmdPrimeWeight_nonneg (n : ℕ) : 0 ≤ chmdPrimeWeight n := by
  unfold chmdPrimeWeight
  split_ifs
  · exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _)
  · exact le_rfl

theorem chmdPrimeWeight_le (n : ℕ) : chmdPrimeWeight n ≤ n := by
  unfold chmdPrimeWeight
  split_ifs with hn
  · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
    have hs : 1 ≤ Real.sqrt n := Real.one_le_sqrt.mpr hn1
    calc (ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n
        ≤ ArithmeticFunction.vonMangoldt n :=
          div_le_self ArithmeticFunction.vonMangoldt_nonneg hs
      _ ≤ Real.log n := ArithmeticFunction.vonMangoldt_le_log
      _ ≤ n := (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
  · exact Nat.cast_nonneg n

theorem chmdPrimeWeight_two_pos : 0 < chmdPrimeWeight 2 := by
  unfold chmdPrimeWeight
  rw [if_pos le_rfl]
  refine div_pos ?_ (Real.sqrt_pos.mpr (by norm_num))
  rw [ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
  exact Real.log_pos (by norm_num)

theorem chmdPrimeWeight_eq_zero_of_lt_two {n : ℕ} (hn : n < 2) : chmdPrimeWeight n = 0 := by
  unfold chmdPrimeWeight
  rw [if_neg (by omega)]

/-- **Translate decay**: for `n ≥ 1`, `D(log n + s) ≤ 8 (1 + log n + |s|) e^{π|s|} n^{−π}`. -/
theorem dAlembertReal_log_add_le {n : ℕ} (hn : 1 ≤ n) (s : ℝ) :
    dAlembertReal (Real.log n + s) ≤
      8 * (1 + Real.log n + |s|) * Real.exp (π * |s|) * (n : ℝ) ^ (-π) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hlog : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
  refine (dAlembertReal_le _).trans ?_
  have h1 : |Real.log n + s| ≤ Real.log n + |s| := by
    refine (abs_add_le _ _).trans ?_; rw [abs_of_nonneg hlog]
  have h2 : Real.log n - |s| ≤ |Real.log n + s| := by
    have := abs_sub_abs_le_abs_add (Real.log n) s
    rw [abs_of_nonneg hlog] at this
    linarith [neg_abs_le s, le_abs_self (Real.log n + s)]
  have h3 : Real.exp (-(π * |Real.log n + s|)) ≤ Real.exp (π * |s|) * (n : ℝ) ^ (-π) := by
    rw [Real.rpow_def_of_pos hn0, ← Real.exp_add]
    exact Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])
  calc 8 * (1 + |Real.log n + s|) * Real.exp (-(π * |Real.log n + s|))
      ≤ 8 * (1 + Real.log n + |s|) * (Real.exp (π * |s|) * (n : ℝ) ^ (-π)) := by
        apply mul_le_mul _ h3 (Real.exp_pos _).le (by positivity)
        linarith
    _ = _ := by ring

theorem summable_chmdPrimeWeight_mul_rpow (C : ℝ) (hC : 0 ≤ C) :
    Summable fun n : ℕ => chmdPrimeWeight n * (8 * (1 + Real.log n + C) * Real.exp (π * C) *
      (n : ℝ) ^ (-π)) := by
  have hp : (2 - π : ℝ) < -1 := by linarith [Real.pi_gt_three]
  refine Summable.of_nonneg_of_le (fun n => mul_nonneg (chmdPrimeWeight_nonneg n) (by positivity))
    (fun n => ?_) ((Real.summable_nat_rpow.mpr hp).mul_left (8 * (2 + C) * Real.exp (π * C)))
  rcases Nat.lt_or_ge n 2 with hn | hn
  · rw [chmdPrimeWeight_eq_zero_of_lt_two hn, zero_mul]
    positivity
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hlog : Real.log n ≤ n := (Real.log_le_sub_one_of_pos hn0).trans (by linarith)
  have hrpow : (n : ℝ) ^ (2 - π) = (n : ℝ) * (n : ℝ) * (n : ℝ) ^ (-π) := by
    rw [sub_eq_add_neg, Real.rpow_add hn0, Real.rpow_two]
    ring
  rw [hrpow]
  have hw := chmdPrimeWeight_le n
  have hw0 := chmdPrimeWeight_nonneg n
  have hE := Real.exp_pos (π * C)
  have hR := Real.rpow_pos_of_pos hn0 (-π)
  have hlog0 : 0 ≤ Real.log n := Real.log_nonneg hn1
  have hA : 1 + Real.log n + C ≤ (2 + C) * n := by nlinarith
  calc chmdPrimeWeight n * (8 * (1 + Real.log n + C) * Real.exp (π * C) * (n : ℝ) ^ (-π))
      ≤ n * (8 * ((2 + C) * n) * Real.exp (π * C) * (n : ℝ) ^ (-π)) := by
        apply mul_le_mul hw _ (by positivity) (by positivity)
        gcongr
    _ = 8 * (2 + C) * Real.exp (π * C) * ((n : ℝ) * (n : ℝ) * (n : ℝ) ^ (-π)) := by ring

theorem dAlembert_pair_le {n : ℕ} (hn : 1 ≤ n) {s Y : ℝ} (hs : |s| ≤ Y) :
    dAlembertReal (Real.log n + s) + dAlembertReal (Real.log n - s) ≤
      2 * (8 * (1 + Real.log n + Y) * Real.exp (π * Y) * (n : ℝ) ^ (-π)) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hmono : ∀ s' : ℝ, |s'| ≤ Y → dAlembertReal (Real.log n + s') ≤
      8 * (1 + Real.log n + Y) * Real.exp (π * Y) * (n : ℝ) ^ (-π) := by
    intro s' hs'
    refine (dAlembertReal_log_add_le hn s').trans ?_
    have hR := Real.rpow_pos_of_pos hn0 (-π)
    have hlog : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
    have h1 : 1 + Real.log n + |s'| ≤ 1 + Real.log n + Y := by linarith
    have h2 : Real.exp (π * |s'|) ≤ Real.exp (π * Y) :=
      Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])
    have h3 := mul_le_mul h1 h2 (Real.exp_pos _).le (by linarith [abs_nonneg s'])
    have h4 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h3 (by norm_num : (0:ℝ) ≤ 8))
      hR.le
    linarith [h4]
  have h1 := hmono s hs
  have h2 := hmono (-s) (by rwa [abs_neg])
  rw [← sub_eq_add_neg] at h2
  linarith

theorem summable_masslessPrimeWave_term (v : ℝ) :
    Summable fun n : ℕ => chmdPrimeWeight n *
      (dAlembertReal (Real.log n + v) + dAlembertReal (Real.log n - v)) := by
  refine Summable.of_nonneg_of_le (fun n => mul_nonneg (chmdPrimeWeight_nonneg n)
    (add_pos (dAlembertReal_pos _) (dAlembertReal_pos _)).le) (fun n => ?_)
    ((summable_chmdPrimeWeight_mul_rpow |v| (abs_nonneg v)).mul_left 2)
  rcases Nat.lt_or_ge n 2 with hn | hn
  · rw [chmdPrimeWeight_eq_zero_of_lt_two hn, zero_mul]
    positivity
  rw [show 2 * (chmdPrimeWeight n * (8 * (1 + Real.log n + |v|) * Real.exp (π * |v|) *
      (n : ℝ) ^ (-π))) = chmdPrimeWeight n * (2 * (8 * (1 + Real.log n + |v|) *
      Real.exp (π * |v|) * (n : ℝ) ^ (-π))) by ring]
  exact mul_le_mul_of_nonneg_left (dAlembert_pair_le (by omega) le_rfl)
    (chmdPrimeWeight_nonneg n)

/-- The **d'Alembert prime wave** `P₀(v) = Σ_n (Λ(n)/√n)(D(log n + v) + D(log n − v))`. -/
def masslessPrimeWave (v : ℝ) : ℝ :=
  ∑' n : ℕ, chmdPrimeWeight n * (dAlembertReal (Real.log n + v) + dAlembertReal (Real.log n - v))

/-- **The d'Alembert prime wave is strictly positive.** -/
theorem masslessPrimeWave_pos (v : ℝ) : 0 < masslessPrimeWave v :=
  (summable_masslessPrimeWave_term v).tsum_pos
    (fun n => mul_nonneg (chmdPrimeWeight_nonneg n)
      (add_pos (dAlembertReal_pos _) (dAlembertReal_pos _)).le) 2
    (mul_pos chmdPrimeWeight_two_pos (add_pos (dAlembertReal_pos _) (dAlembertReal_pos _)))

theorem chmdPrimeWave_eq_tsum_kernel (y : ℝ) :
    chmdPrimeWave y = ∑' n : ℕ, chmdPrimeWeight n * chmdPrimeKernel y (Real.log n) := by
  rw [chmdPrimeWave_eq]
  rfl

/-- **The prime wave is the light-cone transmutation of the d'Alembert prime wave**:
`chmdPrimeWave y = P₀(y) − (y²/2) ∫_{−1}^{1} B(2y²(1−t²)) P₀(yt) dt`, with `P₀ > 0`. -/
theorem chmdPrimeWave_eq_lightConeTransmute (y : ℝ) :
    chmdPrimeWave y = lightConeTransmute masslessPrimeWave y := by
  set Bt : ℝ → ℝ := fun t => lightConeBesselReal (2 * y ^ 2 * (1 - t ^ 2)) with hBt
  set F : ℕ → ℝ → ℝ := fun n t => chmdPrimeWeight n *
    (Bt t * (dAlembertReal (Real.log n + y * t) + dAlembertReal (Real.log n - y * t))) with hF
  have hBc : Continuous Bt := continuous_lightConeBesselReal.comp (by fun_prop)
  have hFint : HasSum (fun n => ∫ t in (-1 : ℝ)..1, F n t)
      (∫ t in (-1 : ℝ)..1, Bt t * masslessPrimeWave (y * t)) := by
    refine intervalIntegral.hasSum_integral_of_dominated_convergence
      (fun n _ => chmdPrimeWeight n * (Real.exp (y ^ 2 / 2) *
        (2 * (8 * (1 + Real.log n + |y|) * Real.exp (π * |y|) * (n : ℝ) ^ (-π)))))
      (fun n => (by simp only [hF]; exact (continuous_const.mul (hBc.mul
        ((continuous_dAlembertReal.comp (by fun_prop)).add
          (continuous_dAlembertReal.comp (by fun_prop))))).aestronglyMeasurable))
      (fun n => Eventually.of_forall fun t ht => ?_)
      (Eventually.of_forall fun _ _ =>
        ((summable_chmdPrimeWeight_mul_rpow |y| (abs_nonneg y)).mul_left
          (Real.exp (y ^ 2 / 2) * 2)).congr fun n => by ring)
      intervalIntegrable_const
      (Eventually.of_forall fun t _ => ?_)
    · have hta := mem_uIoc_neg_one_one_abs_le ht
      rcases Nat.lt_or_ge n 2 with hn | hn
      · simp only [hF, chmdPrimeWeight_eq_zero_of_lt_two hn, zero_mul, norm_zero]
        exact le_rfl
      have hyt : |y * t| ≤ |y| := by
        rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg y) hta
      have hpair := dAlembert_pair_le (n := n) (by omega) hyt
      have hB := abs_lightConeBesselReal_light_cone_le y hta
      simp only [hF, Real.norm_eq_abs, abs_mul, abs_of_nonneg (chmdPrimeWeight_nonneg n),
        abs_of_pos (add_pos (dAlembertReal_pos _) (dAlembertReal_pos _))]
      exact mul_le_mul_of_nonneg_left (mul_le_mul hB hpair
        (add_pos (dAlembertReal_pos _) (dAlembertReal_pos _)).le (Real.exp_pos _).le)
        (chmdPrimeWeight_nonneg n)
    · have h := ((summable_masslessPrimeWave_term (y * t)).hasSum).mul_left (Bt t)
      refine h.congr_fun fun n => ?_
      simp only [hF]
      ring
  have hterm : ∀ n : ℕ, chmdPrimeWeight n * chmdPrimeKernel y (Real.log n) =
      chmdPrimeWeight n * (dAlembertReal (Real.log n + y) + dAlembertReal (Real.log n - y)) -
        y ^ 2 / 2 * ∫ t in (-1 : ℝ)..1, F n t := by
    intro n
    rw [chmdPrimeKernel_eq_lightCone]
    simp only [hF]
    rw [intervalIntegral.integral_const_mul]
    ring
  rw [chmdPrimeWave_eq_tsum_kernel]
  simp_rw [hterm]
  rw [(summable_masslessPrimeWave_term y).tsum_sub (hFint.summable.mul_left _), tsum_mul_left,
    hFint.tsum_eq]
  rfl

/-! ## The pole and archimedean waves -/

/-- The light-cone identity at the pole frequency `√(7/4) = √((i/2)² + 2)`:
`cos(y√(7/4)) = cosh(y/2) − (y²/2) ∫_{−1}^{1} B(2y²(1−t²)) cosh(yt/2) dt`. -/
theorem cos_mul_sqrt_seven_fourths_eq_lightCone (y : ℝ) :
    Real.cos (y * Real.sqrt (7 / 4)) = Real.cosh (y / 2) -
      y ^ 2 / 2 * ∫ t in (-1 : ℝ)..1,
        lightConeBesselReal (2 * y ^ 2 * (1 - t ^ 2)) * Real.cosh (y * t / 2) := by
  have h := cos_mul_eq_lightCone (y : ℂ) (I / 2) 2 ((Real.sqrt (7 / 4) : ℝ) : ℂ)
    (by rw [← ofReal_pow, Real.sq_sqrt (by norm_num), div_pow, I_sq]; push_cast; ring)
  have hc : ∀ x : ℝ, Complex.cos ((x : ℂ) * (I / 2)) = (Real.cosh (x / 2) : ℂ) := by
    intro x
    rw [show (x : ℂ) * (I / 2) = ((x / 2 : ℝ) : ℂ) * I by push_cast; ring, Complex.cos_mul_I,
      ofReal_cosh]
  have hint : (∫ t in (-1 : ℝ)..1, lightConeBessel (2 * (y : ℂ) ^ 2 * (1 - (t : ℂ) ^ 2)) *
      Complex.cos ((y : ℂ) * (I / 2) * t)) =
      ((∫ t in (-1 : ℝ)..1, lightConeBesselReal (2 * y ^ 2 * (1 - t ^ 2)) *
        Real.cosh (y * t / 2) : ℝ) : ℂ) := by
    rw [← intervalIntegral.integral_ofReal]
    refine intervalIntegral.integral_congr fun t _ => ?_
    rw [show (y : ℂ) * (I / 2) * t = ((y * t : ℝ) : ℂ) * (I / 2) by push_cast; ring, hc,
      ofReal_mul, ofReal_lightConeBesselReal]
    push_cast
    ring_nf
  rw [hint, hc] at h
  apply ofReal_injective
  push_cast at h ⊢
  linear_combination h

/-- **The pole wave is the light-cone transmutation of `(2/cos²(1/4)) cosh(·/2)`.** -/
theorem chmdPoleWave_eq_lightConeTransmute (y : ℝ) :
    chmdPoleWave y =
      lightConeTransmute (fun v => 2 / Real.cos (1 / 4 : ℝ) ^ 2 * Real.cosh (v / 2)) y := by
  rw [chmdPoleWave_eq, cos_mul_sqrt_seven_fourths_eq_lightCone, lightConeTransmute, mul_sub]
  congr 1
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun t _ => ?_
  rw [show y * t / 2 = (y * t) / 2 by ring]
  ring

/-- The massless archimedean wave `A₀(v) = ∫ cos(v r) sech²(r/2) γ(r) dr`. -/
def masslessArchWave (v : ℝ) : ℝ := ∫ r : ℝ, Real.cos (v * r) * sechSqHalf r * EF.gammaBracket r

theorem integrable_sechSqHalf_mul_gammaBracket :
    Integrable fun r : ℝ => sechSqHalf r * EF.gammaBracket r :=
  integrable_sechSqHalf_mul_abs_gammaBracket.mono'
    (continuous_sechSqHalf.mul WeilHerglotz.continuous_gammaBracket).aestronglyMeasurable
    (Eventually.of_forall fun r => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (sechSqHalf_pos r)])

/-- **The archimedean wave is the light-cone transmutation of its massless counterpart.** -/
theorem chmdArchWave_eq_lightConeTransmute (y : ℝ) :
    chmdArchWave y = lightConeTransmute masslessArchWave y := by
  rw [chmdArchWave_eq, integral_cos_sqrt_mul_sechSqHalf_mul_eq y WeilHerglotz.continuous_gammaBracket
    integrable_sechSqHalf_mul_gammaBracket]
  rfl

end RHTower.CHMDLightCone
