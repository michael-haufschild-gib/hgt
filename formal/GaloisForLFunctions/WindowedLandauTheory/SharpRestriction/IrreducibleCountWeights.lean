import GaloisForLFunctions.WindowedLandauTheory.SharpRestriction.IrreducibleCountSizes
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! The six terms bounding a bad-row share are eventually
bounded by one stretched exponential times a fixed power.
The relative count error is eventually at most one half. -/

noncomputable section

namespace WindowedLandauTheory.ConcN

def Wg (f m N g q₁ d : ℕ) : ℝ :=
  3 * (f : ℝ) / (g : ℝ) +
    23 * (f : ℝ) * Real.log (g : ℝ) / Real.sqrt (g : ℝ) +
    2 * (f : ℝ) * (m : ℝ) * (1 / (4 * ((min q₁ d : ℕ) : ℝ)) + (1 + Real.log (N : ℝ)) / ((g : ℝ) - 1)) +
    (N : ℝ) / 2 * (7 / 8 : ℝ) ^ f +
    Real.exp (-(f : ℝ) / (5 * Real.log (N : ℝ)))

def epsC (c : ℝ) (N f : ℕ) : ℝ := Real.exp (-(c * (N : ℝ) * (f : ℝ) * Real.log (N : ℝ)))

private theorem third_fourth_terms_bound (f m P A B eu : ℝ) (hf0 : 0 ≤ f) (hm0 : 0 ≤ m) (hfP : f ≤ P) (hmP : m ≤ P) (hA0 : 0 ≤ A)
    (hB0 : 0 ≤ B) (hA : A ≤ eu) (hB : B ≤ 2 * P * eu) : 2 * f * m * (A + B) ≤ 2 * (P * P) * (eu + 2 * P * eu) := by
  have hP0 : 0 ≤ P := le_trans hf0 hfP
  have hfm : f * m ≤ P * P := mul_le_mul hfP hmP hm0 hP0
  have hAB : A + B ≤ eu + 2 * P * eu := add_le_add hA hB
  have h3 : f * m * (A + B) ≤ P * P * (eu + 2 * P * eu) :=
    mul_le_mul hfm hAB (add_nonneg hA0 hB0) (mul_nonneg hP0 hP0)
  nlinarith [h3]

private theorem sum_auxiliary_weights_le (t1 t2 t34 t5 t6 : ℝ) (P eu X3 : ℝ) (hP1 : 1 ≤ P) (heu : 0 ≤ eu) (hX : 103 ≤ X3)
    (h1 : t1 ≤ 3 * P * eu) (h2 : t2 ≤ 92 * P * eu) (h34 : t34 ≤ 2 * (P * P) * (eu + 2 * P * eu))
    (h5 : t5 ≤ P * eu) (h6 : t6 ≤ eu) : t1 + t2 + t34 + t5 + t6 ≤ P ^ 3 * X3 * eu := by
  have hP0 : 0 ≤ P := le_trans zero_le_one hP1
  have hPP : 1 ≤ P * P := by nlinarith
  have hP3 : P ^ 3 = P * P * P := by ring
  have a1 : P * eu ≤ P ^ 3 * eu := by
    rw [hP3]; exact mul_le_mul_of_nonneg_right (by nlinarith) heu
  have a2 : P * P * eu ≤ P ^ 3 * eu := by
    rw [hP3]; exact mul_le_mul_of_nonneg_right (by nlinarith) heu
  have a3 : eu ≤ P ^ 3 * eu := by
    rw [hP3]; nlinarith [mul_nonneg (mul_nonneg hP0 hP0) heu]
  have a4 : P ^ 3 * 103 * eu ≤ P ^ 3 * X3 * eu := by
    have h0 : 0 ≤ P ^ 3 * eu := mul_nonneg (pow_nonneg hP0 3) heu
    nlinarith [h0]
  have e1 : 2 * (P * P) * (eu + 2 * P * eu) = 2 * (P * P * eu) + 4 * (P ^ 3 * eu) := by ring
  nlinarith [a1, a2, a3, a4, e1]

theorem weight_numbers_bound (ε Cs : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∀ᶠ x : ℝ in Filter.atTop, ∀ f m N g q₁ d : ℕ, SizesAt x ε Cs f m N g q₁ d →
      Wg f m N g q₁ d ≤ x ^ (3 * Cs + 3) * Real.exp (-(x ^ (ε / 6))) := by
  filter_upwards [Filter.eventually_ge_atTop (max 10 (100 * Cs ^ 2 + 1))] with x hx
  intro f m N g q₁ d hS
  obtain ⟨hg, hf2, hfP, hmP, hN100, hNP, hmin⟩ := hS
  have hx10 : (10 : ℝ) ≤ x := le_trans (le_max_left _ _) hx
  have hxC : 100 * Cs ^ 2 + 1 ≤ x := le_trans (le_max_right _ _) hx
  have hx0 : 0 < x := (by norm_num : (0 : ℝ) < 10).trans_le hx10
  have hx1 : 1 ≤ x := (by norm_num : (1 : ℝ) ≤ 10).trans hx10
  have hN : (100 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN100
  have hP100 : (100 : ℝ) ≤ x ^ Cs := le_trans hN hNP
  have hCs : 0 < Cs := by
    by_contra h
    push Not at h
    have : x ^ Cs ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx1 h
    linarith only [this, hP100]
  set P := x ^ Cs with hPdef
  set E := x ^ ε with hEdef
  set u := x ^ (ε / 6) with hudef
  have hE1 : 1 ≤ E := Real.one_le_rpow hx1 hε.le
  have hu1 : 1 ≤ u := Real.one_le_rpow hx1 (by positivity)
  have huE : u ≤ E := Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
  have hux : u ≤ x := by
    calc u ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
      _ = x := Real.rpow_one x
  set eu := Real.exp (-u) with heu
  have heu0 : 0 < eu := Real.exp_pos _
  have hf0 : (0 : ℝ) ≤ (f : ℝ) := Nat.cast_nonneg _
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg _
  have hP1 : 1 ≤ P := (by norm_num : (1 : ℝ) ≤ 100).trans hP100

  have h8E : 1 + 8 * E ≤ Real.exp (8 * E) := by have := Real.add_one_le_exp (8 * E); linarith
  have hg9 : (9 : ℝ) ≤ (g : ℝ) := by linarith only [h8E, hg, hE1]
  have hgpos : (0 : ℝ) < (g : ℝ) := (by norm_num : (0 : ℝ) < 9).trans_le hg9
  have hginv : 1 / (g : ℝ) ≤ eu := by
    rw [div_le_iff₀ hgpos]
    have h1 : Real.exp (-u) * Real.exp (8 * E) ≤ Real.exp (-u) * (g : ℝ) :=
      mul_le_mul_of_nonneg_left hg heu0.le
    have h2 : Real.exp (-u) * Real.exp (8 * E) = Real.exp (8 * E - u) := by
      rw [← Real.exp_add]; ring_nf
    have h3 : 1 ≤ Real.exp (8 * E - u) := Real.one_le_exp (by linarith)
    linarith only [h1, h2, h3]

  have hT1 : 3 * (f : ℝ) / (g : ℝ) ≤ 3 * P * eu := by
    have : 3 * (f : ℝ) / (g : ℝ) = 3 * (f : ℝ) * (1 / (g : ℝ)) := by ring
    rw [this]
    exact mul_le_mul (by linarith only [hfP]) hginv (by positivity) (by positivity)

  set s := Real.sqrt (Real.sqrt (g : ℝ)) with hsdef
  have hsg : Real.sqrt (g : ℝ) = s ^ 2 := by
    rw [hsdef, Real.sq_sqrt (Real.sqrt_nonneg _)]
  have hs4 : (g : ℝ) = s ^ 4 := by
    have : s ^ 4 = (s ^ 2) ^ 2 := by ring
    rw [this, ← hsg, Real.sq_sqrt hgpos.le]
  have hs0 : 0 < s := by
    rw [hsdef]; exact Real.sqrt_pos.2 (Real.sqrt_pos.2 hgpos)
  have hlogs : Real.log (g : ℝ) ≤ 4 * s := by
    rw [hs4, Real.log_pow]
    have := Real.log_le_sub_one_of_pos hs0
    push_cast
    linarith only [this]
  have hsE : Real.exp (2 * E) ≤ s := by
    have h4 : Real.exp (2 * E) ^ 4 ≤ s ^ 4 := by
      rw [← hs4, ← Real.exp_nat_mul]; push_cast
      calc Real.exp (4 * (2 * E)) = Real.exp (8 * E) := by ring_nf
        _ ≤ (g : ℝ) := hg
    exact (pow_le_pow_iff_left₀ (Real.exp_pos _).le hs0.le (by norm_num)).1 h4
  have hsinv : 1 / s ≤ eu := by
    rw [div_le_iff₀ hs0]
    have h1 : Real.exp (-u) * Real.exp (2 * E) ≤ Real.exp (-u) * s := mul_le_mul_of_nonneg_left hsE heu0.le
    have h2 : Real.exp (-u) * Real.exp (2 * E) = Real.exp (2 * E - u) := by
      rw [← Real.exp_add]; ring_nf
    have h3 : 1 ≤ Real.exp (2 * E - u) := Real.one_le_exp (by linarith)
    linarith only [h1, h2, h3]
  have hT2 : 23 * (f : ℝ) * Real.log (g : ℝ) / Real.sqrt (g : ℝ) ≤ 92 * P * eu := by
    rw [hsg]
    have hlog0 : 0 ≤ Real.log (g : ℝ) := Real.log_nonneg (by linarith only [hg9])
    have hA : 23 * (f : ℝ) * Real.log (g : ℝ) / s ^ 2 ≤ 92 * (f : ℝ) * (1 / s) := by
      rw [div_le_iff₀ (by positivity)]
      have : 92 * (f : ℝ) * (1 / s) * s ^ 2 = 23 * (f : ℝ) * (4 * s) := by field_simp; ring
      rw [this]
      exact mul_le_mul_of_nonneg_left hlogs (by positivity)
    refine hA.trans ?_
    have : 92 * (f : ℝ) * (1 / s) ≤ 92 * P * eu :=
      mul_le_mul (by linarith only [hfP]) hsinv (by positivity) (by positivity)
    exact this

  have hM : Real.exp u ≤ ((min q₁ d : ℕ) : ℝ) := hmin
  have hMpos : 0 < ((min q₁ d : ℕ) : ℝ) := lt_of_lt_of_le (Real.exp_pos _) hM
  have hA3 : 1 / (4 * ((min q₁ d : ℕ) : ℝ)) ≤ eu := by
    rw [div_le_iff₀ (by positivity)]
    have h1 : Real.exp (-u) * Real.exp u = 1 := by rw [← Real.exp_add]; simp
    have h2 : Real.exp (-u) * Real.exp u ≤ Real.exp (-u) * ((min q₁ d : ℕ) : ℝ) :=
      mul_le_mul_of_nonneg_left hM heu0.le
    have h3 : Real.exp (-u) * (4 * ((min q₁ d : ℕ) : ℝ)) = 4 * (Real.exp (-u) * ((min q₁ d : ℕ) : ℝ)) := by ring
    rw [heu, h3]
    linarith only [h1, h2]
  have hlogN : 1 + Real.log (N : ℝ) ≤ P := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < N by linarith)
    linarith only [this, hNP]
  have hlogN0 : 0 ≤ 1 + Real.log (N : ℝ) :=
    add_nonneg zero_le_one (Real.log_nonneg (by linarith only [hN]))
  have hB4 : (1 + Real.log (N : ℝ)) / ((g : ℝ) - 1) ≤ 2 * P * eu := by
    have hg1 : 0 < (g : ℝ) - 1 := by linarith only [hg9]
    rw [div_le_iff₀ hg1]
    have h1 : 1 ≤ eu * (g : ℝ) := by rwa [div_le_iff₀ hgpos] at hginv
    have h2 : eu * 9 ≤ eu * (g : ℝ) := mul_le_mul_of_nonneg_left hg9 heu0.le
    have h2' : eu * ((g : ℝ) - 1) = eu * (g : ℝ) - eu := by ring
    have h3 : 1 / 2 ≤ eu * ((g : ℝ) - 1) := by linarith only [h1, h2, h2']
    have h4 : 2 * P * (1 / 2) ≤ 2 * P * (eu * ((g : ℝ) - 1)) := mul_le_mul_of_nonneg_left h3 (by linarith)
    have h5 : 2 * P * eu * ((g : ℝ) - 1) = 2 * P * (eu * ((g : ℝ) - 1)) := by ring
    linarith only [hlogN, h4, h5]
  have hT34 := third_fourth_terms_bound (f : ℝ) (m : ℝ) P (1 / (4 * ((min q₁ d : ℕ) : ℝ)))
    ((1 + Real.log (N : ℝ)) / ((g : ℝ) - 1)) eu hf0 hm0 hfP hmP (by positivity)
    (by have hg1 : 0 < (g : ℝ) - 1 := by linarith only [hg9]
        positivity) hA3 hB4

  have h78 : (7 / 8 : ℝ) ≤ Real.exp (-(1 / 8)) := by
    have := Real.add_one_le_exp (-(1 / 8 : ℝ)); linarith
  have hT5 : (N : ℝ) / 2 * (7 / 8 : ℝ) ^ f ≤ P * eu := by
    have hpow : (7 / 8 : ℝ) ^ f ≤ Real.exp (-(1 / 8)) ^ f := pow_le_pow_left₀ (by norm_num) h78 f
    rw [← Real.exp_nat_mul] at hpow
    have h8x : 8 * x ≤ x ^ 2 := by rw [sq]; exact mul_le_mul_of_nonneg_right (by linarith) hx0.le
    have hfu : u ≤ (f : ℝ) / 8 := by linarith only [hux, h8x, hf2]
    have hexp : Real.exp ((f : ℝ) * (-(1 / 8))) ≤ eu := Real.exp_le_exp.2 (by linarith only [hfu])
    have hN2 : (N : ℝ) / 2 ≤ P := by linarith only [hNP, hN]
    calc (N : ℝ) / 2 * (7 / 8 : ℝ) ^ f ≤ P * Real.exp ((f : ℝ) * (-(1 / 8))) :=
          mul_le_mul hN2 hpow (by positivity) (zero_le_one.trans hP1)
      _ ≤ P * eu := mul_le_mul_of_nonneg_left hexp (zero_le_one.trans hP1)

  have hlogNpos : 0 < Real.log (N : ℝ) := Real.log_pos (by linarith only [hN])
  have hlogNx : Real.log (N : ℝ) ≤ Cs * Real.log x := by
    rw [← Real.log_rpow hx0]
    exact Real.log_le_log (by linarith only [hN]) hNP
  have hsqx : 10 * Cs ≤ Real.sqrt x := by
    rw [Real.le_sqrt (by linarith) hx0.le]
    have : (10 * Cs) ^ 2 = 100 * Cs ^ 2 := by ring
    linarith only [this, hxC]
  have hlogx : Real.log x ≤ 2 * Real.sqrt x := by
    have hsx : 0 < Real.sqrt x := Real.sqrt_pos.2 hx0
    have h1 : Real.log x = 2 * Real.log (Real.sqrt x) := by
      rw [← Real.log_rpow hsx]; congr 1
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, Real.sq_sqrt hx0.le]
    have := Real.log_le_sub_one_of_pos hsx
    linarith only [this, h1]
  have hxx : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx0.le
  have hT6 : Real.exp (-(f : ℝ) / (5 * Real.log (N : ℝ))) ≤ eu := by
    apply Real.exp_le_exp.2
    have hkey : u * (5 * Real.log (N : ℝ)) ≤ (f : ℝ) := by
      have h1 : u * (5 * Real.log (N : ℝ)) ≤ x * (5 * (Cs * Real.log x)) :=
        mul_le_mul hux (mul_le_mul_of_nonneg_left hlogNx (by norm_num)) (by positivity) hx0.le
      have h2 : x * (5 * (Cs * Real.log x)) ≤ x * (5 * (Cs * (2 * Real.sqrt x))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlogx hCs.le) (by norm_num)) hx0.le
      have h3 : x * (5 * (Cs * (2 * Real.sqrt x))) ≤ x ^ 2 := by
        have h10 : 10 * Cs * Real.sqrt x ≤ Real.sqrt x * Real.sqrt x :=
          mul_le_mul_of_nonneg_right hsqx (Real.sqrt_nonneg x)
        have : 5 * (Cs * (2 * Real.sqrt x)) ≤ x := by
          calc 5 * (Cs * (2 * Real.sqrt x)) = 10 * Cs * Real.sqrt x := by ring
            _ ≤ Real.sqrt x * Real.sqrt x := h10
            _ = x := hxx
        have h11 : x * (5 * (Cs * (2 * Real.sqrt x))) ≤ x * x := mul_le_mul_of_nonneg_left this hx0.le
        rw [sq]; exact h11
      exact h1.trans (h2.trans (h3.trans hf2))
    rw [neg_div, neg_le_neg_iff, le_div_iff₀ (by positivity)]
    exact hkey

  have hpow3 : x ^ (3 * Cs + 3) = P ^ 3 * x ^ 3 := by
    rw [show 3 * Cs + 3 = Cs * 3 + 3 by ring, Real.rpow_add hx0, Real.rpow_mul hx0.le]
    rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, Real.rpow_natCast]
  have hx3 : (103 : ℝ) ≤ x ^ 3 := by
    have : (10 : ℝ) ^ 3 ≤ x ^ 3 := pow_le_pow_left₀ (by norm_num) hx10 3
    norm_num at this; linarith
  unfold Wg
  rw [hpow3]
  exact sum_auxiliary_weights_le _ _ _ _ _ P eu (x ^ 3) hP1 heu0.le hx3 hT1 hT2 hT34 hT5 hT6

theorem epsilon_bound_large_x (c : ℝ) (hc : 0 < c) :
    ∀ᶠ x : ℝ in Filter.atTop, ∀ N f : ℕ, 100 ≤ N → x ^ 2 ≤ (f : ℝ) → epsC c N f ≤ 1 / 2 := by
  filter_upwards [Filter.eventually_ge_atTop (max 1 (1 / c))] with x hx N f hN hf
  have hx1 : 1 ≤ x := le_trans (le_max_left _ _) hx
  have hxc : 1 / c ≤ x := le_trans (le_max_right _ _) hx
  have hcx : 1 ≤ c * x := by
    rw [div_le_iff₀ hc] at hxc; linarith
  have hcx2 : 1 ≤ c * x ^ 2 := by nlinarith
  have hN' : (100 : ℝ) ≤ N := by exact_mod_cast hN
  have hlog : 1 ≤ Real.log N := by
    have h1 : Real.exp 1 ≤ (N : ℝ) := by
      have := Real.exp_one_lt_d9
      linarith
    have h2 := Real.log_le_log (Real.exp_pos 1) h1
    rwa [Real.log_exp] at h2
  have h2 : 1 ≤ c * f := le_trans hcx2 (mul_le_mul_of_nonneg_left hf hc.le)
  have h3 : 1 ≤ (N : ℝ) * Real.log N := by nlinarith
  have key : 1 ≤ c * (N : ℝ) * (f : ℝ) * Real.log (N : ℝ) := by
    calc (1 : ℝ) ≤ (c * f) * (N * Real.log N) := one_le_mul_of_one_le_of_one_le h2 h3
      _ = c * (N : ℝ) * (f : ℝ) * Real.log (N : ℝ) := by ring
  unfold epsC
  have hle : Real.exp (-(c * (N : ℝ) * (f : ℝ) * Real.log (N : ℝ))) ≤ Real.exp (-1) :=
    Real.exp_le_exp.mpr (by linarith)
  have he := Real.add_one_le_exp (1 : ℝ)
  have hm : Real.exp (-1) * Real.exp 1 = 1 := by
    rw [← Real.exp_add]; norm_num
  have hp : 0 < Real.exp (-1) := Real.exp_pos _
  nlinarith

end WindowedLandauTheory.ConcN

#print axioms WindowedLandauTheory.ConcN.weight_numbers_bound
#print axioms WindowedLandauTheory.ConcN.epsilon_bound_large_x
