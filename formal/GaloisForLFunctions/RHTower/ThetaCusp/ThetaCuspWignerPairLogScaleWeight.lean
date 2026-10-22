import GaloisForLFunctions.RHTower.LogWeightedEulerIntegral
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspWignerPairSignLaw

/-!
# The logarithmic scale weight of the theta Wigner pair current

Weighting the center integral of an ordered theta source pair by the logarithm of its radial scale
`log (2π n m e^(2u))` replaces the Gamma values of the unweighted transform by the corresponding
Gamma derivatives, minus `log (cosh w)` times the unweighted transform.  This is the first weight
whose value involves the indices outside a Dirichlet factor: `log (2π n m)` appears additively,
which is what produces a logarithmic derivative after summation over `n` and `m`.
-/

open Real MeasureTheory Set

namespace RHTower

noncomputable section

theorem integrableOn_rpow_mul_log_mul_exp_neg_mul_Ioi {a C : ℝ} (ha : 0 < a) (hC : 0 < C) :
    IntegrableOn (fun s : ℝ => s ^ (a - 1) * Real.log s * Real.exp (-(C * s))) (Ioi 0) := by
  set g : ℝ → ℝ := fun x => x ^ (a - 1) * Real.log x * Real.exp (-x) with hg
  have hbase : IntegrableOn g (Ioi 0) := integrableOn_rpow_mul_log_mul_exp_neg_Ioi ha
  have hscaled : IntegrableOn (fun s : ℝ => g (C * s)) (Ioi 0) := by
    have h := (integrableOn_Ioi_comp_mul_left_iff g 0 hC).mpr (by simpa using hbase)
    simpa using h
  have hpow : IntegrableOn (fun s : ℝ => s ^ (a - 1) * Real.exp (-(C * s))) (Ioi 0) :=
    GaloisForLFunctions.HTGeometry.integrableOn_rpow_mul_exp_neg_mul_Ioi (by linarith) hC
  have hCpow : C ^ (1 - a) * C ^ (a - 1) = 1 := by
    rw [← Real.rpow_add hC, show 1 - a + (a - 1) = (0 : ℝ) by ring, Real.rpow_zero]
  have hsum : IntegrableOn (fun s : ℝ => C ^ (1 - a) * g (C * s) -
      Real.log C * (s ^ (a - 1) * Real.exp (-(C * s)))) (Ioi 0) :=
    (hscaled.const_mul (C ^ (1 - a))).sub (hpow.const_mul (Real.log C))
  refine hsum.congr_fun (fun s hs => ?_) measurableSet_Ioi
  have hs0 : (0 : ℝ) < s := hs
  show C ^ (1 - a) * ((C * s) ^ (a - 1) * Real.log (C * s) * Real.exp (-(C * s))) -
      Real.log C * (s ^ (a - 1) * Real.exp (-(C * s))) =
    s ^ (a - 1) * Real.log s * Real.exp (-(C * s))
  rw [Real.mul_rpow hC.le hs0.le, Real.log_mul hC.ne' hs0.ne']
  linear_combination (s ^ (a - 1) * (Real.log C + Real.log s) * Real.exp (-(C * s))) * hCpow

/-- Gamma-derivative weight of the log-scale radial Mellin transform. -/
def thetaCuspWignerRadialLogWeight (σ C : ℝ) : ℝ :=
  (deriv Real.Gamma (σ + 4) - Real.Gamma (σ + 4) * Real.log C) / C ^ 2 -
    6 * (deriv Real.Gamma (σ + 3) - Real.Gamma (σ + 3) * Real.log C) +
      9 * (deriv Real.Gamma (σ + 2) - Real.Gamma (σ + 2) * Real.log C)

/-- **Log-weighted radial Mellin transform of the Wigner pair profile.** -/
theorem integral_rpow_mul_log_mul_thetaCuspWignerRadialProfile {σ : ℝ} (hσ : 0 < σ) (v : ℝ) :
    (∫ s : ℝ in Ioi 0, s ^ (σ - 1) * Real.log s * thetaCuspWignerRadialProfile s v) =
      (1 / Real.cosh (2 * v)) ^ (σ + 2) *
        thetaCuspWignerRadialLogWeight σ (Real.cosh (2 * v)) := by
  set C : ℝ := Real.cosh (2 * v) with hCdef
  have hC1 : (1 : ℝ) ≤ C := Real.one_le_cosh _
  have hC : (0 : ℝ) < C := lt_of_lt_of_le one_pos hC1
  have hpoint : ∀ s ∈ Ioi (0 : ℝ),
      s ^ (σ - 1) * Real.log s * thetaCuspWignerRadialProfile s v =
        s ^ (σ + 4 - 1) * Real.log s * Real.exp (-(C * s)) -
          6 * C * (s ^ (σ + 3 - 1) * Real.log s * Real.exp (-(C * s))) +
            9 * (s ^ (σ + 2 - 1) * Real.log s * Real.exp (-(C * s))) := by
    intro s hs
    have hs0 : (0 : ℝ) < s := hs
    have e4 : s ^ (σ - 1) * (s ^ (4 : ℕ)) = s ^ (σ + 4 - 1) := by
      rw [← Real.rpow_natCast s 4, ← Real.rpow_add hs0]; congr 1; norm_num; ring
    have e3 : s ^ (σ - 1) * (s ^ (3 : ℕ)) = s ^ (σ + 3 - 1) := by
      rw [← Real.rpow_natCast s 3, ← Real.rpow_add hs0]; congr 1; norm_num; ring
    have e2 : s ^ (σ - 1) * (s ^ (2 : ℕ)) = s ^ (σ + 2 - 1) := by
      rw [← Real.rpow_natCast s 2, ← Real.rpow_add hs0]; congr 1; norm_num; ring
    unfold thetaCuspWignerRadialProfile
    rw [← hCdef, show -s * C = -(C * s) by ring]
    linear_combination (Real.log s * Real.exp (-(C * s))) * e4 -
      6 * C * (Real.log s * Real.exp (-(C * s))) * e3 +
        9 * (Real.log s * Real.exp (-(C * s))) * e2
  rw [setIntegral_congr_fun measurableSet_Ioi hpoint]
  have i4 := integrableOn_rpow_mul_log_mul_exp_neg_mul_Ioi (a := σ + 4) (by linarith) hC
  have i3 := integrableOn_rpow_mul_log_mul_exp_neg_mul_Ioi (a := σ + 3) (by linarith) hC
  have i2 := integrableOn_rpow_mul_log_mul_exp_neg_mul_Ioi (a := σ + 2) (by linarith) hC
  have hA : IntegrableOn (fun s : ℝ =>
      s ^ (σ + 4 - 1) * Real.log s * Real.exp (-(C * s)) -
        6 * C * (s ^ (σ + 3 - 1) * Real.log s * Real.exp (-(C * s)))) (Ioi 0) :=
    i4.sub (i3.const_mul _)
  have hB : IntegrableOn (fun s : ℝ =>
      9 * (s ^ (σ + 2 - 1) * Real.log s * Real.exp (-(C * s)))) (Ioi 0) := i2.const_mul _
  rw [integral_add hA hB, integral_sub i4 (i3.const_mul _), integral_const_mul,
    integral_const_mul,
    integral_rpow_mul_log_mul_exp_neg_mul_Ioi (σ := σ + 4) (by linarith) hC,
    integral_rpow_mul_log_mul_exp_neg_mul_Ioi (σ := σ + 3) (by linarith) hC,
    integral_rpow_mul_log_mul_exp_neg_mul_Ioi (σ := σ + 2) (by linarith) hC]
  have hCinv : (0 : ℝ) < 1 / C := by positivity
  have p2r : (1 / C) ^ (2 : ℝ) = (1 / C) ^ (2 : ℕ) := by
    rw [← Real.rpow_natCast (1 / C) 2]; norm_num
  have p4 : (1 / C) ^ (σ + 4) = (1 / C) ^ (σ + 2) * (1 / C) ^ (2 : ℕ) := by
    rw [show σ + 4 = σ + 2 + 2 by ring, Real.rpow_add hCinv, p2r]
  have p3 : (1 / C) ^ (σ + 3) = (1 / C) ^ (σ + 2) * (1 / C) := by
    rw [show σ + 3 = σ + 2 + 1 by ring, Real.rpow_add hCinv, Real.rpow_one]
  rw [p4, p3, thetaCuspWignerRadialLogWeight]
  field_simp

/-- **Log-scale-weighted center integral of an ordered theta source pair.** -/
theorem integral_log_scale_mul_exp_mul_thetaCuspSourceTerm_pair {σ : ℝ} (hσ : 0 < σ)
    {n m : ℕ} (hn : 0 < n) (hm : 0 < m) (t : ℝ) :
    (∫ u : ℝ, Real.log (thetaCuspWignerAtomScale n m u) * Real.exp ((2 * σ - 1) * u) *
        (thetaCuspSourceTerm (u + t) n * thetaCuspSourceTerm (u - t) m)) =
      1 / (2 * (2 * Real.pi * n * m) ^ σ) *
        ((1 / Real.cosh (2 * t + Real.log n - Real.log m)) ^ (σ + 2) *
          thetaCuspWignerRadialLogWeight σ
            (Real.cosh (2 * t + Real.log n - Real.log m))) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hP : (0 : ℝ) < 2 * Real.pi * n * m := by positivity
  set w : ℝ := thetaCuspWignerAtomCenteredCoordinate n m t with hw
  have h2w : 2 * w = 2 * t + Real.log n - Real.log m := by
    rw [hw, thetaCuspWignerAtomCenteredCoordinate]; ring
  have hpt : ∀ u : ℝ,
      Real.log (thetaCuspWignerAtomScale n m u) * Real.exp ((2 * σ - 1) * u) *
        (thetaCuspSourceTerm (u + t) n * thetaCuspSourceTerm (u - t) m) =
      Real.exp (2 * σ * u) *
        (Real.log ((2 * Real.pi * n * m) * Real.exp (2 * u)) *
          thetaCuspWignerRadialProfile ((2 * Real.pi * n * m) * Real.exp (2 * u)) w) := by
    intro u
    rw [thetaCuspSourceTerm_mul_reflect_eq_wignerRadialProfile hn hm u t,
      thetaCuspWignerAtomScale, ← hw]
    rw [show Real.log (2 * Real.pi * n * m * Real.exp (2 * u)) *
        Real.exp ((2 * σ - 1) * u) *
        (Real.exp u * thetaCuspWignerRadialProfile
          (2 * Real.pi * n * m * Real.exp (2 * u)) w) =
      (Real.exp ((2 * σ - 1) * u) * Real.exp u) *
        (Real.log (2 * Real.pi * n * m * Real.exp (2 * u)) *
          thetaCuspWignerRadialProfile (2 * Real.pi * n * m * Real.exp (2 * u)) w) by ring,
      ← Real.exp_add, show (2 * σ - 1) * u + u = 2 * σ * u by ring]
  rw [show (∫ u : ℝ, Real.log (thetaCuspWignerAtomScale n m u) * Real.exp ((2 * σ - 1) * u) *
        (thetaCuspSourceTerm (u + t) n * thetaCuspSourceTerm (u - t) m)) =
      ∫ u : ℝ, Real.exp (2 * σ * u) *
        (Real.log ((2 * Real.pi * n * m) * Real.exp (2 * u)) *
          thetaCuspWignerRadialProfile ((2 * Real.pi * n * m) * Real.exp (2 * u)) w) from
      integral_congr_ae (Filter.Eventually.of_forall hpt)]
  have hchart := integral_Ioi_rpow_mul_eq_exp_chart (σ := σ) hP
    (fun z => Real.log z * thetaCuspWignerRadialProfile z w)
  rw [show (∫ z : ℝ in Ioi 0, z ^ (σ - 1) * (Real.log z * thetaCuspWignerRadialProfile z w)) =
      ∫ z : ℝ in Ioi 0, z ^ (σ - 1) * Real.log z * thetaCuspWignerRadialProfile z w from
    setIntegral_congr_fun measurableSet_Ioi (fun z _ => by ring)] at hchart
  rw [integral_rpow_mul_log_mul_thetaCuspWignerRadialProfile hσ w, h2w] at hchart
  have hPpow : (0 : ℝ) < (2 * Real.pi * n * m) ^ σ := Real.rpow_pos_of_pos hP _
  field_simp at hchart ⊢
  linarith [hchart]

end

end RHTower
