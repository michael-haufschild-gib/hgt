import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspThreeAtomFullJets

/-!
# The complete theta-source fourth logarithmic numerator is negative

The first three atoms give a strict margin. In the normalization dividing
jet j by q^(j+1), a telescoping quartic estimate bounds the full-tail
change by 10^16 exp(-15q). Its product with q^4 is less than one on
q ≥ π, so the head margin 17/10 leaves a full-source margin 7/10.
This proves the sign for the literal infinite derivative series.
-/

open Set

namespace RHTower.ThetaCuspThreeAtomFourth

noncomputable def fourthNumerator (v : ℕ → ℝ) : ℝ :=
  v 0^3*v 4 - 4*v 0^2*v 3*v 1 - 3*v 0^2*v 2^2 +
    12*v 0*v 2*v 1^2 - 6*v 1^4

private theorem abs_prod4_sub (a b c d A B C D : ℝ) :
    |a*b*c*d-A*B*C*D| ≤ |a-A| * |b| * |c| * |d| + |A| * |b-B| * |c| * |d| +
      |A| * |B| * |c-C| * |d| + |A| * |B| * |C| * |d-D| := by
  let t₀ := (a-A)*b*c*d
  let t₁ := A*(b-B)*c*d
  let t₂ := A*B*(c-C)*d
  let t₃ := A*B*C*(d-D)
  have heq : a*b*c*d-A*B*C*D = t₀+t₁+t₂+t₃ := by dsimp [t₀,t₁,t₂,t₃]; ring
  have h₀ := abs_add_le t₀ t₁
  have h₁ := abs_add_le (t₀+t₁) t₂
  have h₂ := abs_add_le (t₀+t₁+t₂) t₃
  have hsum : |t₀+t₁+t₂+t₃| ≤ |t₀|+|t₁|+|t₂|+|t₃| := by linarith
  rw [heq]
  simpa only [t₀,t₁,t₂,t₃,abs_mul] using hsum

private theorem abs_weighted_five (a b c d e : ℝ) :
    |a-4*b-3*c+12*d-6*e| ≤ |a|+4*|b|+3*|c|+12*|d|+6*|e| := by
  have h₁ := abs_sub_le a 0 (4*b)
  have h₂ := abs_sub_le (a-4*b) 0 (3*c)
  have h₃ := abs_add_le (a-4*b-3*c) (12*d)
  have h₄ := abs_sub_le (a-4*b-3*c+12*d) 0 (6*e)
  norm_num [abs_mul] at h₁ h₂ h₃ h₄
  linarith

private theorem fourthNumerator_perturbation {a b : ℕ → ℝ} {E : ℝ} (hE : 0 ≤ E)
    (ha : ∀ j ≤ 4, |a j| ≤ 2*atomCoefficientBound j)
    (hb : ∀ j ≤ 4, |b j| ≤ 2*atomCoefficientBound j)
    (hd : ∀ j ≤ 4, |b j-a j| ≤ (2*atomCoefficientBound j*4^(2*j+4))*E) :
    |fourthNumerator b-fourthNumerator a| ≤ 10000000000000000*E := by
  let M := fun j => 2*atomCoefficientBound j
  let C := fun j => 2*atomCoefficientBound j*4^(2*j+4)
  have hM (j : ℕ) (hj : j ≤ 4) : 0 ≤ M j := by
    dsimp [M]
    exact mul_nonneg (by norm_num) (atomCoefficientBound_pos hj).le
  have hC (j : ℕ) (hj : j ≤ 4) : 0 ≤ C j := by
    exact mul_nonneg (hM j hj) (by positivity)
  have hp (i j k l : ℕ) (hi : i ≤ 4) (hj : j ≤ 4) (hk : k ≤ 4) (hl : l ≤ 4) :
      |b i*b j*b k*b l-a i*a j*a k*a l| ≤
        E*(C i*M j*M k*M l + M i*C j*M k*M l +
          M i*M j*C k*M l + M i*M j*M k*C l) := by
    have hai := ha i hi; have haj := ha j hj; have hak := ha k hk
    have hbj := hb j hj; have hbk := hb k hk; have hbl := hb l hl
    have hdi := hd i hi; have hdj := hd j hj; have hdk := hd k hk; have hdl := hd l hl
    have hMi := hM i hi; have hMj := hM j hj; have hMk := hM k hk; have hMl := hM l hl
    have hCi := hC i hi; have hCj := hC j hj; have hCk := hC k hk; have hCl := hC l hl
    calc
      _ ≤ |b i-a i| * |b j| * |b k| * |b l| + |a i| * |b j-a j| * |b k| * |b l| +
          |a i| * |a j| * |b k-a k| * |b l| + |a i| * |a j| * |a k| * |b l-a l| :=
        abs_prod4_sub _ _ _ _ _ _ _ _
      _ ≤ (C i*E)*M j*M k*M l + M i*(C j*E)*M k*M l +
          M i*M j*(C k*E)*M l + M i*M j*M k*(C l*E) := by
        dsimp only [M,C] at *
        gcongr
      _ = _ := by ring
  have h₀ := hp 0 0 0 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h₁ := hp 0 0 3 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h₂ := hp 0 0 2 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h₃ := hp 0 2 1 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h₄ := hp 1 1 1 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [M,C,atomCoefficientBound] at h₀ h₁ h₂ h₃ h₄
  have heq : fourthNumerator b-fourthNumerator a =
      (b 0*b 0*b 0*b 4-a 0*a 0*a 0*a 4) -
      4*(b 0*b 0*b 3*b 1-a 0*a 0*a 3*a 1) -
      3*(b 0*b 0*b 2*b 2-a 0*a 0*a 2*a 2) +
      12*(b 0*b 2*b 1*b 1-a 0*a 2*a 1*a 1) -
      6*(b 1*b 1*b 1*b 1-a 1*a 1*a 1*a 1) := by unfold fourthNumerator; ring
  rw [heq]
  have hs := abs_weighted_five
    (b 0*b 0*b 0*b 4-a 0*a 0*a 0*a 4)
    (b 0*b 0*b 3*b 1-a 0*a 0*a 3*a 1)
    (b 0*b 0*b 2*b 2-a 0*a 0*a 2*a 2)
    (b 0*b 2*b 1*b 1-a 0*a 2*a 1*a 1)
    (b 1*b 1*b 1*b 1-a 1*a 1*a 1*a 1)
  linarith only [hs,h₀,h₁,h₂,h₃,h₄,hE]

theorem scaledFull_fourthNumerator_sub_head_abs_le {q : ℝ} (hq : Real.pi ≤ q) :
    |fourthNumerator (scaledFullJet q)-fourthNumerator (scaledHeadJet q)| ≤
      10000000000000000*Real.exp (-15*q) := by
  apply fourthNumerator_perturbation (Real.exp_pos _).le
  · intro j hj; exact scaledHeadJet_abs_le hq hj
  · intro j hj; exact scaledFullJet_abs_le hq hj
  · intro j hj; exact scaledFullJet_sub_head_abs_le hq hj

private theorem hasDerivAt_quarticDecay (q : ℝ) :
    HasDerivAt (fun q : ℝ => q^4*Real.exp (-15*q))
      (q^3*Real.exp (-15*q)*(4-15*q)) q := by
  convert! ((hasDerivAt_id q).pow 4).mul (((hasDerivAt_id q).const_mul (-15)).exp) using 1
  dsimp
  ring

theorem quarticDecay_small {q : ℝ} (hq : Real.pi ≤ q) :
    10000000000000000*q^4*Real.exp (-15*q) < 1 := by
  have hanti : StrictAntiOn (fun q : ℝ => q^4*Real.exp (-15*q)) (Ici 3) := by
    apply strictAntiOn_of_deriv_neg (convex_Ici 3)
    · intro q _; exact (hasDerivAt_quarticDecay q).continuousAt.continuousWithinAt
    · intro q hq
      have hq3 : 3 ≤ q := le_of_lt (by simpa only [interior_Ici, mem_Ioi] using hq)
      rw [(hasDerivAt_quarticDecay q).deriv]
      exact mul_neg_of_pos_of_neg (mul_pos (pow_pos (by linarith) _) (Real.exp_pos _))
        (by linarith)
  have hpi : (157/50:ℝ) < Real.pi := by linarith [Real.pi_gt_d2]
  have hdecay := hanti (by norm_num) (by change 3 ≤ q; linarith) (hpi.trans_le hq)
  have he : Real.exp (-15*(157/50:ℝ)) ≤ 1/(23:ℝ)^15 := by
    rw [neg_mul, Real.exp_neg,
      show Real.exp (15*(157/50:ℝ)) = Real.exp (157/50)^15 from Real.exp_nat_mul _ 15,
      one_div]
    apply (inv_le_inv₀ (by positivity) (by positivity)).mpr
    gcongr
    exact twentyThree_lt_exp_lower_pi.le
  calc
    _ < 10000000000000000*((157/50:ℝ)^4*Real.exp (-15*(157/50:ℝ))) := by linarith
    _ ≤ 10000000000000000*((157/50:ℝ)^4*(1/(23:ℝ)^15)) := by gcongr
    _ < 1 := by norm_num

theorem fourthNumerator_weighted_div (v : ℕ → ℝ) {q : ℝ} (hq : q ≠ 0) :
    fourthNumerator (fun j => v j / q^(j+1)) = fourthNumerator v / q^8 := by
  unfold fourthNumerator
  norm_num only [Nat.reduceAdd]
  field_simp

theorem fourthNumerator_logJet (v : ℕ → ℝ) (h0 : v 0 ≠ 0) :
    fourthNumerator v / (v 0)^4 =
      HilbertMetric.logarithmicFourthJet (v 0) (v 1) (v 2) (v 3) (v 4) := by
  unfold fourthNumerator HilbertMetric.logarithmicFourthJet
  field_simp

theorem scaledHead_fourthNumerator_lt {q : ℝ} (hq : Real.pi ≤ q) :
    q^4 * fourthNumerator (scaledHeadJet q) < -17/10 := by
  have hq0 : 0 < q := Real.pi_pos.trans_le hq
  have hG := headJet_zero_ge hq
  have hG0 : 0 < headJet 0 q := hq0.trans_le hG
  have hhead := rawHeadJet_fourthLogJet_lt hq
  change HilbertMetric.logarithmicFourthJet (headJet 0 q) (headJet 1 q)
    (headJet 2 q) (headJet 3 q) (headJet 4 q) < -(17/10) at hhead
  rw [← fourthNumerator_logJet (fun j => headJet j q) hG0.ne'] at hhead
  have hnum := (div_lt_iff₀ (pow_pos hG0 4)).mp hhead
  have hp : q^4 ≤ (headJet 0 q)^4 := by gcongr
  have hmargin : fourthNumerator (fun j => headJet j q) < (-17/10)*q^4 := by
    linarith
  have hid : q^4 * fourthNumerator (scaledHeadJet q) =
      fourthNumerator (fun j => headJet j q) / q^4 := by
    unfold scaledHeadJet
    rw [fourthNumerator_weighted_div _ hq0.ne']
    field_simp
  rw [hid]
  exact (div_lt_iff₀ (pow_pos hq0 4)).mpr hmargin

theorem scaledFull_fourthNumerator_lt {q : ℝ} (hq : Real.pi ≤ q) :
    q^4 * fourthNumerator (scaledFullJet q) < -7/10 := by
  have hd := scaledFull_fourthNumerator_sub_head_abs_le hq
  have hs := quarticDecay_small hq
  have hh := scaledHead_fourthNumerator_lt hq
  have hmul := mul_le_mul_of_nonneg_left hd (pow_nonneg (Real.pi_pos.trans_le hq).le 4)
  have hup := le_abs_self (fourthNumerator (scaledFullJet q)-fourthNumerator (scaledHeadJet q))
  have hmulup := mul_le_mul_of_nonneg_left hup (pow_nonneg (Real.pi_pos.trans_le hq).le 4)
  nlinarith only [hmul, hs, hh, hmulup]

theorem fullJet_fourthNumerator_neg {q : ℝ} (hq : Real.pi ≤ q) :
    fourthNumerator (fun j => fullJet j q) < 0 := by
  have hq0 : 0 < q := Real.pi_pos.trans_le hq
  have h := scaledFull_fourthNumerator_lt hq
  unfold scaledFullJet at h
  rw [fourthNumerator_weighted_div _ hq0.ne'] at h
  by_contra hn
  have hp := mul_nonneg (pow_nonneg hq0.le 4)
    (div_nonneg (le_of_not_gt hn) (pow_nonneg hq0.le 8))
  linarith

theorem fourthNumerator_scale (v : ℕ → ℝ) (c : ℝ) :
    fourthNumerator (fun j => c*v j) = c^4*fourthNumerator v := by
  unfold fourthNumerator
  ring

/-- Negative fourth-logarithmic numerator of the actual full theta source. -/
theorem fullDerivative_fourthNumerator_neg {x : ℝ} (hx : 0 ≤ x) :
    fourthNumerator (fun j => thetaCuspFullDerivative j x) < 0 := by
  simp_rw [fullDerivative_eq_normalized]
  rw [fourthNumerator_scale]
  exact mul_neg_of_pos_of_neg (pow_pos (sourcePrefactor_pos x) 4)
    (fullJet_fourthNumerator_neg (sourceScale_ge_pi hx))

end RHTower.ThetaCuspThreeAtomFourth
