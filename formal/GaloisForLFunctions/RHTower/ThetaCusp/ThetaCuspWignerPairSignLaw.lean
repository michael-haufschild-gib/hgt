import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspWignerProductFiberNormalForm
import GaloisForLFunctions.HTGeometry.BarnesMellinRepresentation
import GaloisForLFunctions.HTGeometry.ReflectionIntegral

/-!
# The radial Mellin transform of the theta Wigner pair profile

The universal radial profile left after product/ratio separation of two theta-cusp source atoms
has an exact Mellin transform: a Gamma value times an explicit rational weight in the hyperbolic
separation.  That weight is a quadratic in the inverse separation with negative discriminant in
the separation variable, so it has exactly one positive root and the pair current changes sign at
one explicit hyperbolic distance.
-/

open Real MeasureTheory Set

namespace RHTower

noncomputable section

/-- Rational weight of the radial Mellin transform of the Wigner pair profile. -/
def thetaCuspWignerRadialQ (σ C : ℝ) : ℝ :=
  (σ + 2) * (σ + 3) / C ^ 2 - 6 * (σ + 2) + 9

/-- **Exact radial Mellin transform of the Wigner pair profile.** -/
theorem integral_rpow_mul_thetaCuspWignerRadialProfile {σ : ℝ} (hσ : 0 < σ) (v : ℝ) :
    (∫ s : ℝ in Ioi 0, s ^ (σ - 1) * thetaCuspWignerRadialProfile s v) =
      Real.Gamma (σ + 2) * (1 / Real.cosh (2 * v)) ^ (σ + 2) *
        thetaCuspWignerRadialQ σ (Real.cosh (2 * v)) := by
  set C : ℝ := Real.cosh (2 * v) with hCdef
  have hC1 : (1 : ℝ) ≤ C := Real.one_le_cosh _
  have hC : (0 : ℝ) < C := lt_of_lt_of_le one_pos hC1
  -- rewrite the integrand as a linear combination of Euler integrands
  have hpoint : ∀ s ∈ Ioi (0 : ℝ),
      s ^ (σ - 1) * thetaCuspWignerRadialProfile s v =
        s ^ (σ + 3) * Real.exp (-(C * s)) -
          6 * C * (s ^ (σ + 2) * Real.exp (-(C * s))) +
            9 * (s ^ (σ + 1) * Real.exp (-(C * s))) := by
    intro s hs
    have hs0 : (0 : ℝ) < s := hs
    have e4 : s ^ (σ - 1) * (s ^ (4 : ℕ)) = s ^ (σ + 3) := by
      rw [← Real.rpow_natCast s 4, ← Real.rpow_add hs0]; congr 1; norm_num; ring
    have e3 : s ^ (σ - 1) * (s ^ (3 : ℕ)) = s ^ (σ + 2) := by
      rw [← Real.rpow_natCast s 3, ← Real.rpow_add hs0]; congr 1; norm_num; ring
    have e2 : s ^ (σ - 1) * (s ^ (2 : ℕ)) = s ^ (σ + 1) := by
      rw [← Real.rpow_natCast s 2, ← Real.rpow_add hs0]; congr 1; norm_num; ring
    unfold thetaCuspWignerRadialProfile
    rw [← hCdef, show -s * C = -(C * s) by ring]
    linear_combination (Real.exp (-(C * s))) * e4 -
      6 * C * (Real.exp (-(C * s))) * e3 + 9 * (Real.exp (-(C * s))) * e2
  rw [setIntegral_congr_fun measurableSet_Ioi hpoint]
  have i4 : IntegrableOn (fun s : ℝ => s ^ (σ + 3) * Real.exp (-(C * s))) (Ioi 0) :=
    GaloisForLFunctions.HTGeometry.integrableOn_rpow_mul_exp_neg_mul_Ioi (by linarith) hC
  have i3 : IntegrableOn (fun s : ℝ => s ^ (σ + 2) * Real.exp (-(C * s))) (Ioi 0) :=
    GaloisForLFunctions.HTGeometry.integrableOn_rpow_mul_exp_neg_mul_Ioi (by linarith) hC
  have i2 : IntegrableOn (fun s : ℝ => s ^ (σ + 1) * Real.exp (-(C * s))) (Ioi 0) :=
    GaloisForLFunctions.HTGeometry.integrableOn_rpow_mul_exp_neg_mul_Ioi (by linarith) hC
  have hA : IntegrableOn (fun s : ℝ => s ^ (σ + 3) * Real.exp (-(C * s)) -
      6 * C * (s ^ (σ + 2) * Real.exp (-(C * s)))) (Ioi 0) := i4.sub (i3.const_mul _)
  have hB : IntegrableOn (fun s : ℝ => 9 * (s ^ (σ + 1) * Real.exp (-(C * s)))) (Ioi 0) :=
    i2.const_mul _
  rw [integral_add hA hB, integral_sub i4 (i3.const_mul _), integral_const_mul,
    integral_const_mul]
  have g4 := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := σ + 4) (r := C) (by linarith) hC
  have g3 := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := σ + 3) (r := C) (by linarith) hC
  have g2 := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := σ + 2) (r := C) (by linarith) hC
  rw [show σ + 4 - 1 = σ + 3 by ring] at g4
  rw [show σ + 3 - 1 = σ + 2 by ring] at g3
  rw [show σ + 2 - 1 = σ + 1 by ring] at g2
  rw [g4, g3, g2]
  -- Gamma recurrences
  have hgp : (0 : ℝ) < σ + 2 := by linarith
  have r3 : Real.Gamma (σ + 3) = (σ + 2) * Real.Gamma (σ + 2) := by
    rw [show σ + 3 = (σ + 2) + 1 by ring, Real.Gamma_add_one hgp.ne']
  have r4 : Real.Gamma (σ + 4) = (σ + 3) * ((σ + 2) * Real.Gamma (σ + 2)) := by
    rw [show σ + 4 = (σ + 3) + 1 by ring, Real.Gamma_add_one (by linarith : σ + 3 ≠ 0), r3]
  -- powers of 1/C
  have hCinv : (0 : ℝ) < 1 / C := by positivity
  have p2r : (1 / C) ^ (2 : ℝ) = (1 / C) ^ (2 : ℕ) := by
    rw [← Real.rpow_natCast (1 / C) 2]; norm_num
  have p4 : (1 / C) ^ (σ + 4) = (1 / C) ^ (σ + 2) * (1 / C) ^ (2 : ℕ) := by
    rw [show σ + 4 = σ + 2 + 2 by ring, Real.rpow_add hCinv, p2r]
  have p3 : (1 / C) ^ (σ + 3) = (1 / C) ^ (σ + 2) * (1 / C) := by
    rw [show σ + 3 = σ + 2 + 1 by ring, Real.rpow_add hCinv, Real.rpow_one]
  rw [r4, r3, p4, p3]
  unfold thetaCuspWignerRadialQ
  field_simp

/-- Critical hyperbolic separation at which the radial Mellin weight changes sign. -/
def thetaCuspWignerCriticalCosh (σ : ℝ) : ℝ :=
  Real.sqrt ((σ + 2) * (σ + 3) / (6 * σ + 3))

theorem one_lt_thetaCuspWignerCriticalCosh {σ : ℝ} (hσ : 0 ≤ σ) :
    1 < thetaCuspWignerCriticalCosh σ := by
  have hden : (0 : ℝ) < 6 * σ + 3 := by linarith
  have hgt : (1 : ℝ) < (σ + 2) * (σ + 3) / (6 * σ + 3) := by
    rw [lt_div_iff₀ hden]; nlinarith [sq_nonneg (σ - 1), sq_nonneg σ]
  calc (1 : ℝ) = Real.sqrt 1 := (Real.sqrt_one).symm
    _ < _ := Real.sqrt_lt_sqrt (by norm_num) hgt

/-- **Exact sign law for the radial Mellin weight.**  The weight is positive exactly below the
critical hyperbolic separation and negative exactly above it. -/
theorem thetaCuspWignerRadialQ_pos_iff {σ C : ℝ} (hσ : 0 ≤ σ) (hC : 0 < C) :
    0 < thetaCuspWignerRadialQ σ C ↔ C < thetaCuspWignerCriticalCosh σ := by
  have hden : (0 : ℝ) < 6 * σ + 3 := by linarith
  have hC2 : (0 : ℝ) < C ^ 2 := by positivity
  unfold thetaCuspWignerRadialQ thetaCuspWignerCriticalCosh
  rw [show (σ + 2) * (σ + 3) / C ^ 2 - 6 * (σ + 2) + 9 =
      (σ + 2) * (σ + 3) / C ^ 2 - (6 * σ + 3) by ring, sub_pos, lt_div_iff₀ hC2,
    Real.lt_sqrt hC.le, lt_div_iff₀ hden]
  constructor <;> intro h <;> nlinarith [h]

theorem thetaCuspWignerRadialQ_neg_iff {σ C : ℝ} (hσ : 0 ≤ σ) (hC : 0 < C) :
    thetaCuspWignerRadialQ σ C < 0 ↔ thetaCuspWignerCriticalCosh σ < C := by
  have hden : (0 : ℝ) < 6 * σ + 3 := by linarith
  have hC2 : (0 : ℝ) < C ^ 2 := by positivity
  unfold thetaCuspWignerRadialQ thetaCuspWignerCriticalCosh
  rw [show (σ + 2) * (σ + 3) / C ^ 2 - 6 * (σ + 2) + 9 =
      (σ + 2) * (σ + 3) / C ^ 2 - (6 * σ + 3) by ring, sub_neg, div_lt_iff₀ hC2,
    Real.sqrt_lt' hC, div_lt_iff₀ hden]
  constructor <;> intro h <;> nlinarith [h]

/-- The radial Mellin transform is strictly positive at zero hyperbolic separation, for every
positive Mellin exponent. -/
theorem thetaCuspWignerRadialQ_one_pos {σ : ℝ} (hσ : 0 ≤ σ) :
    0 < thetaCuspWignerRadialQ σ 1 :=
  (thetaCuspWignerRadialQ_pos_iff hσ one_pos).mpr (one_lt_thetaCuspWignerCriticalCosh hσ)

/-- **Exact sign law for the radial transform of the Wigner pair profile.**  The transform is
positive exactly when the hyperbolic separation stays below the critical value. -/
theorem integral_rpow_mul_thetaCuspWignerRadialProfile_pos_iff {σ : ℝ} (hσ : 0 < σ) (v : ℝ) :
    0 < (∫ s : ℝ in Ioi 0, s ^ (σ - 1) * thetaCuspWignerRadialProfile s v) ↔
      Real.cosh (2 * v) < thetaCuspWignerCriticalCosh σ := by
  have hC : (0 : ℝ) < Real.cosh (2 * v) := Real.cosh_pos _
  have hgamma : 0 < Real.Gamma (σ + 2) := Real.Gamma_pos_of_pos (by linarith)
  have hpow : (0 : ℝ) < (1 / Real.cosh (2 * v)) ^ (σ + 2) := Real.rpow_pos_of_pos (by positivity) _
  rw [integral_rpow_mul_thetaCuspWignerRadialProfile hσ v,
    mul_pos_iff_of_pos_left (mul_pos hgamma hpow)]
  exact thetaCuspWignerRadialQ_pos_iff hσ.le hC

theorem integral_rpow_mul_thetaCuspWignerRadialProfile_neg_iff {σ : ℝ} (hσ : 0 < σ) (v : ℝ) :
    (∫ s : ℝ in Ioi 0, s ^ (σ - 1) * thetaCuspWignerRadialProfile s v) < 0 ↔
      thetaCuspWignerCriticalCosh σ < Real.cosh (2 * v) := by
  have hC : (0 : ℝ) < Real.cosh (2 * v) := Real.cosh_pos _
  have hgamma : 0 < Real.Gamma (σ + 2) := Real.Gamma_pos_of_pos (by linarith)
  have hpow : (0 : ℝ) < (1 / Real.cosh (2 * v)) ^ (σ + 2) := Real.rpow_pos_of_pos (by positivity) _
  rw [integral_rpow_mul_thetaCuspWignerRadialProfile hσ v]
  constructor
  · intro h
    refine (thetaCuspWignerRadialQ_neg_iff hσ.le hC).mp ?_
    nlinarith [mul_pos hgamma hpow, h]
  · intro h
    exact mul_neg_of_pos_of_neg (mul_pos hgamma hpow)
      ((thetaCuspWignerRadialQ_neg_iff hσ.le hC).mpr h)

/-! ## The exponential chart -/

/-- Exponential chart for a scaled radial Mellin integral: the half-line Mellin integral of `F`
at exponent `σ` is a two-sided exponential moment of the dilated `F`. -/
theorem integral_Ioi_rpow_mul_eq_exp_chart {σ P : ℝ} (hP : 0 < P) (F : ℝ → ℝ) :
    (∫ z in Ioi (0 : ℝ), z ^ (σ - 1) * F z) =
      2 * P ^ σ * ∫ u : ℝ, Real.exp (2 * σ * u) * F (P * Real.exp (2 * u)) := by
  have hPs : Real.exp (σ * Real.log P) = P ^ σ := by
    rw [Real.rpow_def_of_pos hP, mul_comm]
  have hstep : ∀ t : ℝ, Real.exp t * ((Real.exp t) ^ (σ - 1) * F (Real.exp t)) =
      Real.exp (σ * t) * F (Real.exp t) := by
    intro t
    rw [Real.rpow_def_of_pos (Real.exp_pos t), Real.log_exp, ← mul_assoc, ← Real.exp_add,
      show t + t * (σ - 1) = σ * t by ring]
  rw [GaloisForLFunctions.HTGeometry.integral_Ioi_comp_exp (fun z => z ^ (σ - 1) * F z),
    show (∫ t : ℝ, Real.exp t * ((Real.exp t) ^ (σ - 1) * F (Real.exp t))) =
      ∫ t : ℝ, Real.exp (σ * t) * F (Real.exp t) from
        integral_congr_ae (Filter.Eventually.of_forall hstep),
    ← MeasureTheory.integral_add_right_eq_self
      (fun t : ℝ => Real.exp (σ * t) * F (Real.exp t)) (Real.log P)]
  have hpt : ∀ s : ℝ, Real.exp (σ * (s + Real.log P)) * F (Real.exp (s + Real.log P)) =
      P ^ σ * (Real.exp (σ * s) * F (P * Real.exp s)) := by
    intro s
    have h1 : Real.exp (s + Real.log P) = P * Real.exp s := by
      rw [Real.exp_add, Real.exp_log hP, mul_comm]
    have h2 : Real.exp (σ * (s + Real.log P)) = P ^ σ * Real.exp (σ * s) := by
      rw [mul_add, Real.exp_add, hPs, mul_comm]
    rw [h1, h2]; ring
  rw [show (∫ s : ℝ, Real.exp (σ * (s + Real.log P)) * F (Real.exp (s + Real.log P))) =
      ∫ s : ℝ, P ^ σ * (Real.exp (σ * s) * F (P * Real.exp s)) from
        integral_congr_ae (Filter.Eventually.of_forall hpt), integral_const_mul]
  have h := MeasureTheory.Measure.integral_comp_mul_left
    (fun s : ℝ => Real.exp (σ * s) * F (P * Real.exp s)) 2
  simp only [smul_eq_mul] at h
  rw [show (∫ u : ℝ, Real.exp (2 * σ * u) * F (P * Real.exp (2 * u))) =
      ∫ u : ℝ, Real.exp (σ * (2 * u)) * F (P * Real.exp (2 * u)) from
        integral_congr_ae (Filter.Eventually.of_forall fun u => by
          show Real.exp (2 * σ * u) * F (P * Real.exp (2 * u)) =
            Real.exp (σ * (2 * u)) * F (P * Real.exp (2 * u))
          rw [show σ * (2 * u) = 2 * σ * u by ring]), h]
  rw [show |(2 : ℝ)⁻¹| = 1 / 2 by norm_num]
  ring

/-! ## The exact center-mixed pair evaluation -/

/-- **Exact center-mixed evaluation of an ordered theta source pair.**  Every exponentially
weighted center integral of a reflected pair of theta-cusp source atoms is an explicit Gamma value
times a rational weight in the hyperbolic separation `2t + log n - log m`. -/
theorem integral_exp_mul_thetaCuspSourceTerm_pair {σ : ℝ} (hσ : 0 < σ)
    {n m : ℕ} (hn : 0 < n) (hm : 0 < m) (t : ℝ) :
    (∫ u : ℝ, Real.exp ((2 * σ - 1) * u) *
        (thetaCuspSourceTerm (u + t) n * thetaCuspSourceTerm (u - t) m)) =
      Real.Gamma (σ + 2) / (2 * (2 * Real.pi * n * m) ^ σ) *
        ((1 / Real.cosh (2 * t + Real.log n - Real.log m)) ^ (σ + 2) *
          thetaCuspWignerRadialQ σ (Real.cosh (2 * t + Real.log n - Real.log m))) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hP : (0 : ℝ) < 2 * Real.pi * n * m := by positivity
  set w : ℝ := thetaCuspWignerAtomCenteredCoordinate n m t with hw
  have h2w : 2 * w = 2 * t + Real.log n - Real.log m := by
    rw [hw, thetaCuspWignerAtomCenteredCoordinate]; ring
  have hpt : ∀ u : ℝ, Real.exp ((2 * σ - 1) * u) *
      (thetaCuspSourceTerm (u + t) n * thetaCuspSourceTerm (u - t) m) =
      Real.exp (2 * σ * u) *
        thetaCuspWignerRadialProfile ((2 * Real.pi * n * m) * Real.exp (2 * u)) w := by
    intro u
    rw [thetaCuspSourceTerm_mul_reflect_eq_wignerRadialProfile hn hm u t,
      thetaCuspWignerAtomScale, ← hw, ← mul_assoc, ← Real.exp_add,
      show (2 * σ - 1) * u + u = 2 * σ * u by ring]
  rw [show (∫ u : ℝ, Real.exp ((2 * σ - 1) * u) *
        (thetaCuspSourceTerm (u + t) n * thetaCuspSourceTerm (u - t) m)) =
      ∫ u : ℝ, Real.exp (2 * σ * u) *
        thetaCuspWignerRadialProfile ((2 * Real.pi * n * m) * Real.exp (2 * u)) w from
      integral_congr_ae (Filter.Eventually.of_forall hpt)]
  have hchart := integral_Ioi_rpow_mul_eq_exp_chart (σ := σ) hP
    (fun z => thetaCuspWignerRadialProfile z w)
  rw [integral_rpow_mul_thetaCuspWignerRadialProfile hσ w, h2w] at hchart
  have hPpow : (0 : ℝ) < (2 * Real.pi * n * m) ^ σ := Real.rpow_pos_of_pos hP _
  field_simp at hchart ⊢
  linarith [hchart]

/-- **Exact sign law for an ordered theta source pair.**  The exponentially weighted center
integral of a reflected atom pair is strictly positive exactly when the hyperbolic separation
`2t + log n - log m` stays below the critical value, and strictly negative exactly above it. -/
theorem integral_exp_mul_thetaCuspSourceTerm_pair_pos_iff {σ : ℝ} (hσ : 0 < σ)
    {n m : ℕ} (hn : 0 < n) (hm : 0 < m) (t : ℝ) :
    0 < (∫ u : ℝ, Real.exp ((2 * σ - 1) * u) *
        (thetaCuspSourceTerm (u + t) n * thetaCuspSourceTerm (u - t) m)) ↔
      Real.cosh (2 * t + Real.log n - Real.log m) < thetaCuspWignerCriticalCosh σ := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hP : (0 : ℝ) < 2 * Real.pi * n * m := by positivity
  have hPpow : (0 : ℝ) < (2 * Real.pi * n * m) ^ σ := Real.rpow_pos_of_pos hP _
  have hC : (0 : ℝ) < Real.cosh (2 * t + Real.log n - Real.log m) := Real.cosh_pos _
  have hgamma : 0 < Real.Gamma (σ + 2) := Real.Gamma_pos_of_pos (by linarith)
  have hpow : (0 : ℝ) < (1 / Real.cosh (2 * t + Real.log n - Real.log m)) ^ (σ + 2) :=
    Real.rpow_pos_of_pos (by positivity) _
  have hlead : 0 < Real.Gamma (σ + 2) / (2 * (2 * Real.pi * n * m) ^ σ) := by positivity
  rw [integral_exp_mul_thetaCuspSourceTerm_pair hσ hn hm t,
    mul_pos_iff_of_pos_left hlead, mul_pos_iff_of_pos_left hpow]
  exact thetaCuspWignerRadialQ_pos_iff hσ.le hC

theorem integral_exp_mul_thetaCuspSourceTerm_pair_neg_iff {σ : ℝ} (hσ : 0 < σ)
    {n m : ℕ} (hn : 0 < n) (hm : 0 < m) (t : ℝ) :
    (∫ u : ℝ, Real.exp ((2 * σ - 1) * u) *
        (thetaCuspSourceTerm (u + t) n * thetaCuspSourceTerm (u - t) m)) < 0 ↔
      thetaCuspWignerCriticalCosh σ < Real.cosh (2 * t + Real.log n - Real.log m) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hP : (0 : ℝ) < 2 * Real.pi * n * m := by positivity
  have hC : (0 : ℝ) < Real.cosh (2 * t + Real.log n - Real.log m) := Real.cosh_pos _
  have hgamma : 0 < Real.Gamma (σ + 2) := Real.Gamma_pos_of_pos (by linarith)
  have hpow : (0 : ℝ) < (1 / Real.cosh (2 * t + Real.log n - Real.log m)) ^ (σ + 2) :=
    Real.rpow_pos_of_pos (by positivity) _
  have hlead : 0 < Real.Gamma (σ + 2) / (2 * (2 * Real.pi * n * m) ^ σ) := by positivity
  rw [integral_exp_mul_thetaCuspSourceTerm_pair hσ hn hm t]
  constructor
  · intro h
    refine (thetaCuspWignerRadialQ_neg_iff hσ.le hC).mp ?_
    nlinarith [mul_pos hlead hpow, h]
  · intro h
    have hq := (thetaCuspWignerRadialQ_neg_iff hσ.le hC).mpr h
    have := mul_neg_of_pos_of_neg hpow hq
    nlinarith [hlead, this]

/-- Universal pair kernel of the exponentially weighted center integral. -/
def thetaCuspWignerPairKernel (σ y : ℝ) : ℝ :=
  (2 * Real.pi) ^ (-σ) * Real.Gamma (σ + 2) / 2 *
    ((1 / Real.cosh y) ^ (σ + 2) * thetaCuspWignerRadialQ σ (Real.cosh y))

/-- **Dirichlet/separation factorization of the pair current.**  The exponentially weighted center
integral of an ordered atom pair depends on the indices only through the Dirichlet weight
`(n m)^{-σ}` and the hyperbolic separation `2t + log n - log m`. -/
theorem integral_exp_mul_thetaCuspSourceTerm_pair_factor {σ : ℝ} (hσ : 0 < σ)
    {n m : ℕ} (hn : 0 < n) (hm : 0 < m) (t : ℝ) :
    (∫ u : ℝ, Real.exp ((2 * σ - 1) * u) *
        (thetaCuspSourceTerm (u + t) n * thetaCuspSourceTerm (u - t) m)) =
      (n : ℝ) ^ (-σ) * (m : ℝ) ^ (-σ) *
        thetaCuspWignerPairKernel σ (2 * t + Real.log n - Real.log m) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  rw [integral_exp_mul_thetaCuspSourceTerm_pair hσ hn hm t, thetaCuspWignerPairKernel]
  have hsplit : (2 * Real.pi * n * m) ^ σ =
      (2 * Real.pi) ^ σ * (n : ℝ) ^ σ * (m : ℝ) ^ σ := by
    rw [show 2 * Real.pi * (n : ℝ) * m = (2 * Real.pi * n) * m by ring,
      Real.mul_rpow (by positivity) hmR.le, Real.mul_rpow (by positivity) hnR.le]
  have h2pi : (0 : ℝ) < (2 * Real.pi) ^ σ := Real.rpow_pos_of_pos (by positivity) _
  have hnp : (0 : ℝ) < (n : ℝ) ^ σ := Real.rpow_pos_of_pos hnR _
  have hmp : (0 : ℝ) < (m : ℝ) ^ σ := Real.rpow_pos_of_pos hmR _
  rw [hsplit]
  simp only [Real.rpow_neg hnR.le, Real.rpow_neg hmR.le,
    Real.rpow_neg (show (0 : ℝ) ≤ 2 * Real.pi by positivity)]
  field_simp

/-- At its own hyperbolic center every ordered atom pair contributes strictly positively, for
every positive Mellin exponent. -/
theorem integral_exp_mul_thetaCuspSourceTerm_pair_center_pos {σ : ℝ} (hσ : 0 < σ)
    {n m : ℕ} (hn : 0 < n) (hm : 0 < m) :
    0 < ∫ u : ℝ, Real.exp ((2 * σ - 1) * u) *
      (thetaCuspSourceTerm (u + (Real.log m - Real.log n) / 2) n *
        thetaCuspSourceTerm (u - (Real.log m - Real.log n) / 2) m) := by
  rw [integral_exp_mul_thetaCuspSourceTerm_pair_pos_iff hσ hn hm,
    show 2 * ((Real.log m - Real.log n) / 2) + Real.log n - Real.log m = 0 by ring,
    Real.cosh_zero]
  exact one_lt_thetaCuspWignerCriticalCosh hσ.le

end

end RHTower
