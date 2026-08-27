import GaloisForLFunctions.HTGeometry.AbelianZetaGas.ClassLaw

/-!
# Multiplicative resolution cap for order-tilt certificates

A finite positive combination of order tilts varies by at most `4 ^ U` on a dyadic order
window when every exponent has absolute value at most `U`.  Consequently its Markov certificate
for a nonempty short interval is bounded below by `4 ^ (-U)` times the probability of the full
dyadic window.  The expectation is an `ENNReal` lower integral, so the theorem remains exact even
when a negative tilt has infinite expectation.

The nonzero-certificate and nonempty-target hypotheses are load-bearing: without either one the
quotient in the paper statement can have zero denominator and the claimed positive lower bound is
false.
-/

open MeasureTheory Set
open scoped ENNReal

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Groups whose order lies in the short interval `(x, x + h]`. -/
def abelianZetaOrderInterval (x h : ℝ) : Set AbelianZetaGroupClass :=
  {A | x < (A.order : ℝ) ∧ (A.order : ℝ) ≤ x + h}

/-- Groups whose order lies in the dyadic interval `(x, 2x]`. -/
def abelianZetaDyadicOrderWindow (x : ℝ) : Set AbelianZetaGroupClass :=
  {A | x < (A.order : ℝ) ∧ (A.order : ℝ) ≤ 2 * x}

/-- A finite positive order-tilt certificate `∑ i, c i |A| ^ (-u i)`. -/
def abelianZetaOrderTilt {ι : Type*} (s : Finset ι) (c u : ι → ℝ)
    (A : AbelianZetaGroupClass) : ℝ :=
  s.sum fun i => c i * ((A.order : ℝ) ^ (-u i))

/-- Infimum of an order-tilt certificate on a short interval. -/
def abelianZetaOrderTiltFloor {ι : Type*} (s : Finset ι) (c u : ι → ℝ)
    (x h : ℝ) : ℝ :=
  sInf (abelianZetaOrderTilt s c u '' abelianZetaOrderInterval x h)

/-- Extended-nonnegative Markov certificate.  Lower integration preserves the correct value when
an admitted-looking negative exponent has infinite expectation. -/
def abelianZetaOrderTiltMarkovCertificate {ι : Type*}
    (θ : AbelianZetaConvergentParameters) (s : Finset ι) (c u : ι → ℝ)
    (x h : ℝ) : ℝ≥0∞ :=
  (∫⁻ A, ENNReal.ofReal (abelianZetaOrderTilt s c u A)
      ∂(classLaw θ.toAbelianZetaParameters)) /
    ENNReal.ofReal (abelianZetaOrderTiltFloor s c u x h)

private theorem rpow_le_four_rpow_on_dyadic {x y z U e : ℝ}
    (hx : 0 < x) (hy_lo : x < y) (hy_hi : y ≤ 2 * x)
    (hz_lo : x < z) (hz_hi : z ≤ 2 * x)
    (hU : 0 ≤ U) (heU : |e| ≤ U) :
    y ^ e ≤ 4 ^ U * z ^ e := by
  have hy : 0 < y := lt_trans hx hy_lo
  have hz : 0 < z := lt_trans hx hz_lo
  have hyz : y ≤ 2 * z := by nlinarith
  have hzy : z ≤ 2 * y := by nlinarith
  have htwo : (1 : ℝ) ≤ 2 := by norm_num
  have htwofour : (2 : ℝ) ^ U ≤ 4 ^ U :=
    Real.rpow_le_rpow (by norm_num) (by norm_num) hU
  by_cases he : 0 ≤ e
  · have he_le : e ≤ U := le_trans (le_abs_self e) heU
    calc
      y ^ e ≤ (2 * z) ^ e := Real.rpow_le_rpow hy.le hyz he
      _ = 2 ^ e * z ^ e := Real.mul_rpow (by norm_num) hz.le
      _ ≤ 2 ^ U * z ^ e := mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow_of_exponent_le htwo he_le) (Real.rpow_nonneg hz.le e)
      _ ≤ 4 ^ U * z ^ e := mul_le_mul_of_nonneg_right htwofour
        (Real.rpow_nonneg hz.le e)
  · have he' : 0 < -e := neg_pos.mpr (lt_of_not_ge he)
    have hne_le : -e ≤ U := by
      simpa [abs_of_neg (lt_of_not_ge he)] using heU
    have hpow : z ^ (-e) ≤ 4 ^ U * y ^ (-e) := by
      calc
        z ^ (-e) ≤ (2 * y) ^ (-e) := Real.rpow_le_rpow hz.le hzy he'.le
        _ = 2 ^ (-e) * y ^ (-e) := Real.mul_rpow (by norm_num) hy.le
        _ ≤ 2 ^ U * y ^ (-e) := mul_le_mul_of_nonneg_right
          (Real.rpow_le_rpow_of_exponent_le htwo hne_le) (Real.rpow_nonneg hy.le (-e))
        _ ≤ 4 ^ U * y ^ (-e) := mul_le_mul_of_nonneg_right htwofour
          (Real.rpow_nonneg hy.le (-e))
    rw [show e = -(-e) by ring, Real.rpow_neg hy.le, Real.rpow_neg hz.le]
    have hyPow : 0 < y ^ (-e) := Real.rpow_pos_of_pos hy _
    have hzPow : 0 < z ^ (-e) := Real.rpow_pos_of_pos hz _
    have hfour : 0 < (4 : ℝ) ^ U := Real.rpow_pos_of_pos (by norm_num) _
    apply (inv_le_comm₀ hyPow (mul_pos hfour (inv_pos.mpr hzPow))).2
    calc
      (4 ^ U * (z ^ (-e))⁻¹)⁻¹ = z ^ (-e) / 4 ^ U := by field_simp
      _ ≤ y ^ (-e) := (div_le_iff₀ hfour).2 (by simpa [mul_comm] using hpow)

theorem abelianZetaOrderTilt_nonneg {ι : Type*} (s : Finset ι) (c u : ι → ℝ)
    (hc : ∀ i ∈ s, 0 ≤ c i) (A : AbelianZetaGroupClass) :
    0 ≤ abelianZetaOrderTilt s c u A := by
  classical
  rw [abelianZetaOrderTilt]
  exact Finset.sum_nonneg fun i hi => mul_nonneg (hc i hi)
    (Real.rpow_nonneg (by exact_mod_cast A.order_pos.le) _)

theorem abelianZetaOrderTilt_pos {ι : Type*} (s : Finset ι) (c u : ι → ℝ)
    (hc : ∀ i ∈ s, 0 ≤ c i) (hcpos : ∃ i ∈ s, 0 < c i)
    (A : AbelianZetaGroupClass) :
    0 < abelianZetaOrderTilt s c u A := by
  classical
  obtain ⟨i, hi, hci⟩ := hcpos
  have hterm : 0 < c i * ((A.order : ℝ) ^ (-u i)) :=
    mul_pos hci (Real.rpow_pos_of_pos (by exact_mod_cast A.order_pos) _)
  rw [abelianZetaOrderTilt]
  exact Finset.sum_pos' (fun j hj => mul_nonneg (hc j hj)
    (Real.rpow_nonneg (by exact_mod_cast A.order_pos.le) _)) ⟨i, hi, hterm⟩

theorem abelianZetaOrderTilt_le_on_dyadic {ι : Type*} (s : Finset ι) (c u : ι → ℝ)
    {x U : ℝ} (hx : 0 < x) (hU : 0 ≤ U)
    (hc : ∀ i ∈ s, 0 ≤ c i) (hu : ∀ i ∈ s, |u i| ≤ U)
    {A B : AbelianZetaGroupClass}
    (hA : A ∈ abelianZetaDyadicOrderWindow x)
    (hB : B ∈ abelianZetaDyadicOrderWindow x) :
    abelianZetaOrderTilt s c u A ≤ 4 ^ U * abelianZetaOrderTilt s c u B := by
  classical
  rw [abelianZetaOrderTilt, abelianZetaOrderTilt, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  have hpow : (A.order : ℝ) ^ (-u i) ≤ 4 ^ U * (B.order : ℝ) ^ (-u i) :=
    rpow_le_four_rpow_on_dyadic (e := -u i) hx hA.1 hA.2 hB.1 hB.2 hU (by
      simpa only [abs_neg] using hu i hi)
  calc
    c i * (A.order : ℝ) ^ (-u i) ≤ c i * (4 ^ U * (B.order : ℝ) ^ (-u i)) :=
      mul_le_mul_of_nonneg_left hpow (hc i hi)
    _ = 4 ^ U * (c i * (B.order : ℝ) ^ (-u i)) := by ring

/-- **Multiplicative resolution cap.**  For a nonzero finite positive order-tilt certificate and a
nonempty interval `(x, x+h]` with `0 < h ≤ x`, its Markov certificate is at least `4 ^ (-U)`
times the probability of the full dyadic order window.  This is `(GAS4.5)` with the two necessary
nonvacuity hypotheses and an exact extended-nonnegative expectation. -/
theorem abelianZetaOrderTiltMarkovCertificate_ge_dyadic {ι : Type*}
    (θ : AbelianZetaConvergentParameters) (s : Finset ι) (c u : ι → ℝ)
    {x h U : ℝ} (hh : 0 < h) (hhx : h ≤ x) (hU : 0 ≤ U)
    (hc : ∀ i ∈ s, 0 ≤ c i) (hcpos : ∃ i ∈ s, 0 < c i)
    (hu : ∀ i ∈ s, |u i| ≤ U)
    (hI : (abelianZetaOrderInterval x h).Nonempty) :
    ENNReal.ofReal (4 ^ (-U)) *
        classLaw θ.toAbelianZetaParameters (abelianZetaDyadicOrderWindow x)
      ≤ abelianZetaOrderTiltMarkovCertificate θ s c u x h := by
  classical
  let μ := classLaw θ.toAbelianZetaParameters
  let f := abelianZetaOrderTilt s c u
  let I := abelianZetaOrderInterval x h
  let D := abelianZetaDyadicOrderWindow x
  let m := abelianZetaOrderTiltFloor s c u x h
  have hx : 0 < x := lt_of_lt_of_le hh hhx
  have hID : I ⊆ D := by
    intro A hA
    exact ⟨hA.1, by dsimp [I, D, abelianZetaOrderInterval,
      abelianZetaDyadicOrderWindow] at hA ⊢; linarith⟩
  obtain ⟨A₀, hA₀⟩ := hI
  have hA₀I : A₀ ∈ I := hA₀
  have hA₀D : A₀ ∈ D := hID hA₀I
  have hf_nonneg : ∀ A, 0 ≤ f A := abelianZetaOrderTilt_nonneg s c u hc
  have hf_pos : ∀ A, 0 < f A := abelianZetaOrderTilt_pos s c u hc hcpos
  have hrange_nonempty : (f '' I).Nonempty := ⟨f A₀, A₀, hA₀I, rfl⟩
  have hrange_bdd : BddBelow (f '' I) := by
    refine ⟨0, ?_⟩
    intro y hy
    obtain ⟨A, hAI, rfl⟩ := hy
    exact hf_nonneg A
  have hm_def : m = sInf (f '' I) := rfl
  have hfour_inv_pos : 0 < (4 : ℝ) ^ (-U) := Real.rpow_pos_of_pos (by norm_num) _
  have hfour_cancel : (4 : ℝ) ^ (-U) * 4 ^ U = 1 := by
    rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 4)]
    exact inv_mul_cancel₀ (ne_of_gt (Real.rpow_pos_of_pos (by norm_num) U))
  have hm_lower : 4 ^ (-U) * f A₀ ≤ m := by
    rw [hm_def]
    apply le_csInf hrange_nonempty
    intro y hy
    obtain ⟨A, hAI, rfl⟩ := hy
    have hAD := hID hAI
    have hcomp := abelianZetaOrderTilt_le_on_dyadic s c u hx hU hc hu hA₀D hAD
    calc
      4 ^ (-U) * f A₀ ≤ 4 ^ (-U) * (4 ^ U * f A) :=
        mul_le_mul_of_nonneg_left hcomp hfour_inv_pos.le
      _ = f A := by rw [← mul_assoc, hfour_cancel, one_mul]
  have hm_pos : 0 < m := lt_of_lt_of_le (mul_pos hfour_inv_pos (hf_pos A₀)) hm_lower
  have hm_le : m ≤ f A₀ := by
    rw [hm_def]
    exact csInf_le hrange_bdd ⟨A₀, hA₀I, rfl⟩
  have hfloor_on_D : ∀ A ∈ D, 4 ^ (-U) * m ≤ f A := by
    intro A hAD
    have hcomp := abelianZetaOrderTilt_le_on_dyadic s c u hx hU hc hu hA₀D hAD
    calc
      4 ^ (-U) * m ≤ 4 ^ (-U) * f A₀ :=
        mul_le_mul_of_nonneg_left hm_le hfour_inv_pos.le
      _ ≤ 4 ^ (-U) * (4 ^ U * f A) :=
        mul_le_mul_of_nonneg_left hcomp hfour_inv_pos.le
      _ = f A := by rw [← mul_assoc, hfour_cancel, one_mul]
  have hDmeas : MeasurableSet D := MeasurableSet.of_discrete
  have hlin : ENNReal.ofReal (4 ^ (-U) * m) * μ D
      ≤ ∫⁻ A, ENNReal.ofReal (f A) ∂μ := by
    calc
      ENNReal.ofReal (4 ^ (-U) * m) * μ D
          = ∫⁻ _A in D, ENNReal.ofReal (4 ^ (-U) * m) ∂μ :=
            (setLIntegral_const D _).symm
      _ = ∫⁻ A, D.indicator (fun _ => ENNReal.ofReal (4 ^ (-U) * m)) A ∂μ :=
        (lintegral_indicator hDmeas _).symm
      _ ≤ ∫⁻ A, ENNReal.ofReal (f A) ∂μ := by
        apply lintegral_mono
        intro A
        by_cases hAD : A ∈ D
        · rw [Set.indicator_of_mem hAD]
          exact ENNReal.ofReal_le_ofReal (hfloor_on_D A hAD)
        · rw [Set.indicator_of_notMem hAD]
          exact bot_le
  have hden_ne : ENNReal.ofReal m ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr hm_pos)
  change ENNReal.ofReal (4 ^ (-U)) * μ D ≤
    (∫⁻ A, ENNReal.ofReal (f A) ∂μ) / ENNReal.ofReal m
  have hmul : (ENNReal.ofReal (4 ^ (-U)) * μ D) * ENNReal.ofReal m
      ≤ ∫⁻ A, ENNReal.ofReal (f A) ∂μ := by
    calc
      (ENNReal.ofReal (4 ^ (-U)) * μ D) * ENNReal.ofReal m
          = ENNReal.ofReal (4 ^ (-U) * m) * μ D := by
            rw [ENNReal.ofReal_mul hfour_inv_pos.le]
            ac_rfl
      _ ≤ ∫⁻ A, ENNReal.ofReal (f A) ∂μ := hlin
  rw [ENNReal.le_div_iff_mul_le (Or.inl hden_ne) (Or.inl ENNReal.ofReal_ne_top)]
  exact hmul

end

end GaloisForLFunctions.HTGeometry
