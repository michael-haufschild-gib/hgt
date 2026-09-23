import GaloisForLFunctions.RHTower.BandKaiserTransformSeparation
import GaloisForLFunctions.RHTower.BandKaiserFinitePacket

/-!
# Quantitative conditioning data for a finite Kaiser packet grid

For fixed packet count `m`, use angular frequencies

```text
q_j(c) = (j+1) sqrt(c sqrt c).
```

The step is `c^(3/4)`: it is `o(c)`, so translated edge tails remain subexponential, while
`q_step^(2 : ℕ)/(2c)=sqrt(c)/2`, so distinct transform readings are exponentially separated.  This file
proves the exact frequency geometry, product-to-sum reading formula, positive diagonal bound, and
`exp(-sqrt(c)/2)` off-diagonal estimate.
-/

open MeasureTheory Set intervalIntegral
open scoped BigOperators

noncomputable section

namespace GaloisForLFunctions.RHTower

/-- Angular spacing of the conditioned packet grid. -/
def kaiserPacketAngularStep (c : ℝ) : ℝ :=
  Real.sqrt (c * Real.sqrt c)

/-- Positive angular frequencies, indexed from one. -/
def kaiserPacketAngularFrequency {m : ℕ} (c : ℝ) (j : Fin m) : ℝ :=
  ((j.val + 1 : ℕ) : ℝ) * kaiserPacketAngularStep c

/-- Same grid in mathlib's Fourier-frequency normalization. -/
def kaiserPacketFrequency {m : ℕ} (c : ℝ) (j : Fin m) : ℝ :=
  kaiserPacketAngularFrequency c j / (2 * Real.pi)

theorem kaiserPacketAngularStep_pos {c : ℝ} (hc : 0 < c) :
    0 < kaiserPacketAngularStep c := by
  rw [kaiserPacketAngularStep]
  positivity

theorem kaiserPacketAngularStep_sq {c : ℝ} (hc : 0 ≤ c) :
    kaiserPacketAngularStep c ^ (2 : ℕ) = c * Real.sqrt c := by
  rw [kaiserPacketAngularStep, Real.sq_sqrt]
  positivity

theorem kaiserPacketAngularFrequency_pos {m : ℕ} {c : ℝ} (hc : 0 < c) (j : Fin m) :
    0 < kaiserPacketAngularFrequency c j := by
  rw [kaiserPacketAngularFrequency]
  exact mul_pos (by positivity) (kaiserPacketAngularStep_pos hc)

theorem kaiserPacketAngularFrequency_le_card_mul {m : ℕ} {c : ℝ} (hc : 0 ≤ c)
    (j : Fin m) :
    kaiserPacketAngularFrequency c j ≤ (m : ℝ) * kaiserPacketAngularStep c := by
  have hstep : 0 ≤ kaiserPacketAngularStep c := by
    rw [kaiserPacketAngularStep]
    positivity
  have hj : ((j.val + 1 : ℕ) : ℝ) ≤ (m : ℝ) := by
    exact_mod_cast j.isLt
  rw [kaiserPacketAngularFrequency]
  exact mul_le_mul_of_nonneg_right hj hstep

theorem abs_kaiserPacketAngularFrequency_sub_ge_step {m : ℕ} {c : ℝ} (hc : 0 < c)
    {i j : Fin m} (hij : i ≠ j) :
    kaiserPacketAngularStep c ≤
      |kaiserPacketAngularFrequency c i - kaiserPacketAngularFrequency c j| := by
  have hstep := kaiserPacketAngularStep_pos hc
  have hnat : (1 : ℝ) ≤
      |(((i.val + 1 : ℕ) : ℝ) - ((j.val + 1 : ℕ) : ℝ))| := by
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hij) with hijlt | hjilt
    · have hsucc : i.val + 1 + 1 ≤ j.val + 1 := by omega
      have hcast : (((i.val + 1 + 1 : ℕ) : ℝ)) ≤ (((j.val + 1 : ℕ) : ℝ)) := by
        exact_mod_cast hsucc
      have hle : (((i.val + 1 : ℕ) : ℝ)) ≤ (((j.val + 1 : ℕ) : ℝ)) := by
        push_cast at hcast ⊢
        linarith
      rw [abs_of_nonpos (sub_nonpos.mpr hle)]
      push_cast at hcast ⊢
      linarith
    · have hsucc : j.val + 1 + 1 ≤ i.val + 1 := by omega
      have hcast : (((j.val + 1 + 1 : ℕ) : ℝ)) ≤ (((i.val + 1 : ℕ) : ℝ)) := by
        exact_mod_cast hsucc
      have hle : (((j.val + 1 : ℕ) : ℝ)) ≤ (((i.val + 1 : ℕ) : ℝ)) := by
        push_cast at hcast ⊢
        linarith
      rw [abs_of_nonneg (sub_nonneg.mpr hle)]
      push_cast at hcast ⊢
      linarith
  rw [kaiserPacketAngularFrequency, kaiserPacketAngularFrequency, ← sub_mul, abs_mul,
    abs_of_pos hstep]
  nlinarith

/-- Under the explicit fixed-depth aperture condition, every sum of two grid frequencies lies in
the middle half of the band. -/
theorem kaiserPacketAngularFrequency_add_sq_le_half {m : ℕ} {c : ℝ}
    (hc : 1 ≤ c) (hscale : 8 * (m : ℝ) ^ (2 : ℕ) ≤ Real.sqrt c) (i j : Fin m) :
    (kaiserPacketAngularFrequency c i + kaiserPacketAngularFrequency c j) ^ (2 : ℕ) ≤
      c ^ (2 : ℕ) / 2 := by
  have hc0 : 0 ≤ c := zero_le_one.trans hc
  have hcpos : 0 < c := one_pos.trans_le hc
  have hstep0 : 0 ≤ kaiserPacketAngularStep c :=
    (kaiserPacketAngularStep_pos hcpos).le
  have hi := kaiserPacketAngularFrequency_le_card_mul hc0 i
  have hj := kaiserPacketAngularFrequency_le_card_mul hc0 j
  have hsum0 : 0 ≤ kaiserPacketAngularFrequency c i +
      kaiserPacketAngularFrequency c j := by
    exact add_nonneg (kaiserPacketAngularFrequency_pos hcpos i).le
      (kaiserPacketAngularFrequency_pos hcpos j).le
  have hsum : kaiserPacketAngularFrequency c i + kaiserPacketAngularFrequency c j ≤
      2 * (m : ℝ) * kaiserPacketAngularStep c := by linarith
  have hsq := pow_le_pow_left₀ hsum0 hsum 2
  rw [mul_pow, kaiserPacketAngularStep_sq hc0] at hsq
  have hsqrtSq : Real.sqrt c ^ (2 : ℕ) = c := Real.sq_sqrt hc0
  have hfactor :
      4 * (m : ℝ) ^ (2 : ℕ) * (c * Real.sqrt c) ≤ c ^ (2 : ℕ) / 2 := by
    calc
      4 * (m : ℝ) ^ (2 : ℕ) * (c * Real.sqrt c) =
          (8 * (m : ℝ) ^ (2 : ℕ)) * (c * Real.sqrt c / 2) := by ring
      _ ≤ Real.sqrt c * (c * Real.sqrt c / 2) :=
        mul_le_mul_of_nonneg_right hscale (by positivity)
      _ = c ^ (2 : ℕ) / 2 := by nlinarith [hsqrtSq]
  exact hsq.trans_eq (by ring) |>.trans hfactor

theorem kaiserPacketAngularFrequency_sub_sq_le_half {m : ℕ} {c : ℝ}
    (hc : 1 ≤ c) (hscale : 8 * (m : ℝ) ^ (2 : ℕ) ≤ Real.sqrt c) (i j : Fin m) :
    (kaiserPacketAngularFrequency c i - kaiserPacketAngularFrequency c j) ^ (2 : ℕ) ≤
      c ^ (2 : ℕ) / 2 := by
  have hi0 : 0 ≤ kaiserPacketAngularFrequency c i :=
    (kaiserPacketAngularFrequency_pos (one_pos.trans_le hc) i).le
  have hj0 : 0 ≤ kaiserPacketAngularFrequency c j :=
    (kaiserPacketAngularFrequency_pos (one_pos.trans_le hc) j).le
  have habs : |kaiserPacketAngularFrequency c i - kaiserPacketAngularFrequency c j| ≤
      kaiserPacketAngularFrequency c i + kaiserPacketAngularFrequency c j := by
    rcases le_total (kaiserPacketAngularFrequency c i)
      (kaiserPacketAngularFrequency c j) with hij | hji
    · rw [abs_of_nonpos (sub_nonpos.mpr hij)]
      linarith
    · rw [abs_of_nonneg (sub_nonneg.mpr hji)]
      linarith
  have hpow := pow_le_pow_left₀ (abs_nonneg _) habs 2
  rw [sq_abs] at hpow
  exact hpow.trans (kaiserPacketAngularFrequency_add_sq_le_half hc hscale i j)

/-- Angular reading pairing of two Kaiser packets. -/
def kaiserPacketReading (c qi qj : ℝ) : ℝ :=
  ∫ x in (-1 : ℝ)..1,
    kaiserTrial c x * Real.cos (qj * x) * Real.cos (qi * x)

theorem kaiserPacketReading_eq (c qi qj : ℝ) :
    kaiserPacketReading c qi qj =
      (kaiserAngularTransform c (qi - qj) +
        kaiserAngularTransform c (qi + qj)) / 2 := by
  have htrig : ∀ x : ℝ,
      Real.cos (qj * x) * Real.cos (qi * x) =
        (Real.cos ((qi - qj) * x) + Real.cos ((qi + qj) * x)) / 2 := by
    intro x
    rw [show (qi - qj) * x = qi * x - qj * x by ring,
      show (qi + qj) * x = qi * x + qj * x by ring,
      Real.cos_sub, Real.cos_add]
    ring
  rw [kaiserPacketReading]
  have hsplit : ∀ x : ℝ,
      kaiserTrial c x * Real.cos (qj * x) * Real.cos (qi * x) =
        (kaiserTrial c x * Real.cos ((qi - qj) * x) +
          kaiserTrial c x * Real.cos ((qi + qj) * x)) / 2 := by
    intro x
    calc
      kaiserTrial c x * Real.cos (qj * x) * Real.cos (qi * x) =
          kaiserTrial c x * (Real.cos (qj * x) * Real.cos (qi * x)) := by ring
      _ = kaiserTrial c x *
          ((Real.cos ((qi - qj) * x) + Real.cos ((qi + qj) * x)) / 2) := by
        rw [htrig]
      _ = (kaiserTrial c x * Real.cos ((qi - qj) * x) +
          kaiserTrial c x * Real.cos ((qi + qj) * x)) / 2 := by ring
  simp_rw [hsplit]
  have hlinearMinus : Continuous (fun x : ℝ => (qi - qj) * x) :=
    continuous_const.mul continuous_id
  have hlinearPlus : Continuous (fun x : ℝ => (qi + qj) * x) :=
    continuous_const.mul continuous_id
  have hminus : IntervalIntegrable
      (fun x : ℝ => kaiserTrial c x * Real.cos ((qi - qj) * x)) volume (-1) 1 :=
    ((continuous_kaiserTrial c).mul
      (Real.continuous_cos.comp hlinearMinus)).intervalIntegrable (μ := volume) (-1) 1
  have hplus : IntervalIntegrable
      (fun x : ℝ => kaiserTrial c x * Real.cos ((qi + qj) * x)) volume (-1) 1 :=
    ((continuous_kaiserTrial c).mul
      (Real.continuous_cos.comp hlinearPlus)).intervalIntegrable (μ := volume) (-1) 1
  rw [intervalIntegral.integral_div,
    intervalIntegral.integral_add hminus hplus]
  rfl

theorem kaiserAngularTransform_nonneg_of_sq_lt {c q : ℝ} (hq : q ^ (2 : ℕ) < c ^ (2 : ℕ)) :
    0 ≤ kaiserAngularTransform c q := by
  rw [kaiserAngularTransform, integral_kaiserTrial_cos_of_lt hq]
  have hv : 0 < Real.sqrt (c ^ (2 : ℕ) - q ^ (2 : ℕ)) := Real.sqrt_pos.mpr (by linarith)
  have hsinh : 0 ≤ Real.sinh (Real.sqrt (c ^ (2 : ℕ) - q ^ (2 : ℕ))) := by
    rw [Real.sinh_eq]
    have hexp := Real.exp_le_exp.mpr (show -Real.sqrt (c ^ (2 : ℕ) - q ^ (2 : ℕ)) ≤
      Real.sqrt (c ^ (2 : ℕ) - q ^ (2 : ℕ)) by linarith)
    linarith
  exact div_nonneg (mul_nonneg (by norm_num) hsinh) hv.le

/-- Every grid reading has a diagonal at least half the central Kaiser transform. -/
theorem kaiserPacketReading_diagonal_ge {m : ℕ} {c : ℝ}
    (hc : 1 ≤ c) (hscale : 8 * (m : ℝ) ^ (2 : ℕ) ≤ Real.sqrt c) (i : Fin m) :
    kaiserAngularTransform c 0 / 2 ≤
      kaiserPacketReading c (kaiserPacketAngularFrequency c i)
        (kaiserPacketAngularFrequency c i) := by
  rw [kaiserPacketReading_eq, sub_self]
  have hsumSq := kaiserPacketAngularFrequency_add_sq_le_half hc hscale i i
  have hcSq : 0 < c ^ (2 : ℕ) := sq_pos_of_pos (one_pos.trans_le hc)
  have hlt : (kaiserPacketAngularFrequency c i +
      kaiserPacketAngularFrequency c i) ^ (2 : ℕ) < c ^ (2 : ℕ) :=
    lt_of_le_of_lt hsumSq (by linarith)
  have hnonneg : 0 ≤ kaiserAngularTransform c
      (kaiserPacketAngularFrequency c i + kaiserPacketAngularFrequency c i) :=
    kaiserAngularTransform_nonneg_of_sq_lt hlt
  linarith

/-- Distinct grid readings are exponentially smaller than the central diagonal scale. -/
theorem abs_kaiserPacketReading_offDiagonal_le {m : ℕ} {c : ℝ}
    (hc : 1 ≤ c) (hscale : 8 * (m : ℝ) ^ (2 : ℕ) ≤ Real.sqrt c)
    {i j : Fin m} (hij : i ≠ j) :
    |kaiserPacketReading c (kaiserPacketAngularFrequency c i)
        (kaiserPacketAngularFrequency c j)| ≤
      8 * Real.exp (-(Real.sqrt c / 2)) * kaiserAngularTransform c 0 := by
  let qi : ℝ := kaiserPacketAngularFrequency c i
  let qj : ℝ := kaiserPacketAngularFrequency c j
  have hcpos : 0 < c := one_pos.trans_le hc
  have hsubSq : (qi - qj) ^ (2 : ℕ) ≤ c ^ (2 : ℕ) / 2 := by
    simpa [qi, qj] using kaiserPacketAngularFrequency_sub_sq_le_half hc hscale i j
  have haddSq : (qi + qj) ^ (2 : ℕ) ≤ c ^ (2 : ℕ) / 2 := by
    simpa [qi, qj] using kaiserPacketAngularFrequency_add_sq_le_half hc hscale i j
  have hsub : kaiserAngularTransform c (qi - qj) ≤
      8 * Real.exp (-((qi - qj) ^ (2 : ℕ) / (2 * c))) * kaiserAngularTransform c 0 :=
    kaiserAngularTransform_le_exp_separation hc hsubSq
  have hadd : kaiserAngularTransform c (qi + qj) ≤
      8 * Real.exp (-((qi + qj) ^ (2 : ℕ) / (2 * c))) * kaiserAngularTransform c 0 :=
    kaiserAngularTransform_le_exp_separation hc haddSq
  have hstepSq : kaiserPacketAngularStep c ^ (2 : ℕ) = c * Real.sqrt c :=
    kaiserPacketAngularStep_sq hcpos.le
  have hsep : kaiserPacketAngularStep c ≤ |qi - qj| := by
    simpa [qi, qj] using abs_kaiserPacketAngularFrequency_sub_ge_step hcpos hij
  have hsepSq := pow_le_pow_left₀ (kaiserPacketAngularStep_pos hcpos).le hsep 2
  rw [sq_abs, hstepSq] at hsepSq
  have hsumSep : kaiserPacketAngularStep c ≤ qi + qj := by
    have hqi : kaiserPacketAngularStep c ≤ qi := by
      simp only [qi, kaiserPacketAngularFrequency]
      have hstep0 := (kaiserPacketAngularStep_pos hcpos).le
      have hone : (1 : ℝ) ≤ ((i.val + 1 : ℕ) : ℝ) := by
        push_cast
        have hival : (0 : ℝ) ≤ (i.val : ℝ) := Nat.cast_nonneg i.val
        linarith
      nlinarith
    have hqj0 : 0 ≤ qj := by
      simpa [qj] using (kaiserPacketAngularFrequency_pos hcpos j).le
    linarith
  have hsumSepSq := pow_le_pow_left₀ (kaiserPacketAngularStep_pos hcpos).le hsumSep 2
  rw [hstepSq] at hsumSepSq
  have hexpSub : Real.exp (-((qi - qj) ^ (2 : ℕ) / (2 * c))) ≤
      Real.exp (-(Real.sqrt c / 2)) := by
    apply Real.exp_le_exp.mpr
    apply neg_le_neg
    rw [le_div_iff₀ (show 0 < 2 * c by positivity)]
    nlinarith
  have hexpAdd : Real.exp (-((qi + qj) ^ (2 : ℕ) / (2 * c))) ≤
      Real.exp (-(Real.sqrt c / 2)) := by
    apply Real.exp_le_exp.mpr
    apply neg_le_neg
    rw [le_div_iff₀ (show 0 < 2 * c by positivity)]
    nlinarith
  have hcenter0 : 0 ≤ kaiserAngularTransform c 0 :=
    (kaiserAngularTransform_zero_pos hcpos).le
  have hsub' : kaiserAngularTransform c (qi - qj) ≤
      8 * Real.exp (-(Real.sqrt c / 2)) * kaiserAngularTransform c 0 :=
    hsub.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hexpSub (by norm_num)) hcenter0)
  have hadd' : kaiserAngularTransform c (qi + qj) ≤
      8 * Real.exp (-(Real.sqrt c / 2)) * kaiserAngularTransform c 0 :=
    hadd.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hexpAdd (by norm_num)) hcenter0)
  have hcSq : 0 < c ^ (2 : ℕ) := sq_pos_of_pos hcpos
  have hsub0 : 0 ≤ kaiserAngularTransform c (qi - qj) :=
    kaiserAngularTransform_nonneg_of_sq_lt
      (lt_of_le_of_lt hsubSq (by linarith))
  have hadd0 : 0 ≤ kaiserAngularTransform c (qi + qj) :=
    kaiserAngularTransform_nonneg_of_sq_lt
      (lt_of_le_of_lt haddSq (by linarith))
  change |kaiserPacketReading c qi qj| ≤ _
  rw [kaiserPacketReading_eq, abs_of_nonneg (div_nonneg (add_nonneg hsub0 hadd0) (by norm_num))]
  exact (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).2 (by linarith)

end GaloisForLFunctions.RHTower

end
