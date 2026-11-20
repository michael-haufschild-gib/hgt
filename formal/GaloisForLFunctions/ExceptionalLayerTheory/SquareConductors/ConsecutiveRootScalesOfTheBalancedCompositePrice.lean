import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.TheSquareRootBiasOfTheOddBalancedComposites

/-!
# Consecutive deterministic terms in the balanced-composite midpoint

Remove the actual ordinary-prime rows below exponent J. Every remaining
row from J through floor(8J/7) then contributes its own deterministic
power, with an error smaller than the last displayed term. In particular
the seventh and eighth roots are simultaneously visible. Each coefficient
is the exponent of the prime power times its strictly positive Mellin gap.
-/

noncomputable section
open Finset
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

/-- Exact ordinary-prime prefixes before the first replaced exponent. -/
def primeRowsBelow (J : ℕ) (x : ℝ) :=
  ∑ j ∈ Ico 2 J, (j:ℝ)*Chebyshev.theta (x^(1/(j:ℝ)))

private def powersInBlock (J K : ℕ) (x : ℝ) :=
  ∑ j ∈ Icc J K, (j:ℝ)*x^(1/(j:ℝ))

/-- Named power contributions after taking the signed midpoint. -/
def midpointRootBlock (J K : ℕ) (x : ℝ) :=
  ∑ j ∈ Icc J K, (j:ℝ)*midpointPowerGap (1/(j:ℝ))*x^(1/(j:ℝ))

private theorem midpoint_power_block (J K : ℕ) {x : ℝ} (hx : 0≤x) :
    realMidpointObservation (powersInBlock J K) x=midpointRootBlock J K x := by
  simp only [realMidpointObservation,powersInBlock,midpointRootBlock,mul_sum,←sum_sub_distrib]
  refine sum_congr rfl fun j _ => ?_
  have h := congrArg (fun a : ℝ => (j:ℝ)*a) (real_midpoint_of_power (1/(j:ℝ)) hx)
  dsimp only [realMidpointObservation] at h
  linarith only [h]

private theorem prefix_after_root_block {J K : ℕ} (hJ : 2≤J) (hJK : J≤K) {b : ℝ}
    (hb : 1/((K:ℝ)+1)<b) (ha : (1/(J:ℝ))*(41999/48000)≤b) :
    ∃ C : ℝ, 0≤C ∧ ∀ n : ℕ, 0<n → ∀ x : ℝ, 1≤x →
      |fullLogProperPrefix n x-primeRowsBelow J x-powersInBlock J K x| ≤
        (K:ℝ)^2*Real.log n+C*x^b := by
  obtain ⟨C,hC,hprefix⟩ := uniform_full_log_truncation (hJ.trans hJK) hb
  obtain ⟨M,hM,hθ⟩ := theta_power_envelope_of_zero_sup
    (GaloisForLFunctions.ExceptionalLayerTheory.zeroReSup_le_sub_seven_eighths.trans_lt
      (by norm_num : (20999/24000:ℝ)<41999/48000)) (by norm_num)
  let S := Icc J K
  let B := ∑ j ∈ S, (j:ℝ)*M
  have hB : 0≤B := sum_nonneg fun _ _ => mul_nonneg (Nat.cast_nonneg _) hM
  refine ⟨C+B,add_nonneg hC hB,fun n hn x hx => ?_⟩
  let f := fun j : ℕ => (j:ℝ)*Chebyshev.theta (x^(1/(j:ℝ)))
  let g := fun j : ℕ => (j:ℝ)*x^(1/(j:ℝ))
  have hpart : Icc 2 K=Ico 2 J ∪ S := by ext j; simp only [S,mem_Icc,mem_Ico,mem_union]; omega
  have hdis : Disjoint (Ico 2 J) S :=
    disjoint_left.mpr (fun _ h₁ h₂ => (mem_Ico.mp h₁).2.not_ge (mem_Icc.mp h₂).1)
  have h := hprefix n hn x hx
  change |fullLogProperPrefix n x-∑ j ∈ Icc 2 K, f j|≤_ at h
  rw [hpart,sum_union hdis] at h
  have hdecomp : fullLogProperPrefix n x-primeRowsBelow J x-powersInBlock J K x=
      (fullLogProperPrefix n x-((∑ j ∈ Ico 2 J, f j)+∑ j ∈ S, f j))+∑ j ∈ S, (f j-g j) := by
    rw [sum_sub_distrib]
    dsimp only [powersInBlock,primeRowsBelow,S,f,g]
    ring
  have hrow (j : ℕ) (hj : j∈S) : |f j-g j|≤((j:ℝ)*M)*x^b := by
    have hj₁ : (0:ℝ)<J := Nat.cast_pos.mpr (by omega)
    have hji : (J:ℝ)≤j := Nat.cast_le.mpr (mem_Icc.mp hj).1
    have hr := one_div_le_one_div_of_le hj₁ hji
    have hy : 1≤x^(1/(j:ℝ)) := Real.one_le_rpow hx (by positivity)
    have he := hθ _ hy
    rw [←Real.rpow_mul (zero_le_one.trans hx)] at he
    have hh := (mul_le_mul_of_nonneg_right hr (by norm_num : (0:ℝ)≤41999/48000)).trans ha
    have hl := he.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hx hh) hM)
    simpa only [f,g,←mul_sub,abs_mul,abs_of_nonneg (Nat.cast_nonneg (α:=ℝ) j),mul_assoc] using
      mul_le_mul_of_nonneg_left hl (Nat.cast_nonneg (α:=ℝ) j)
  have htail := (abs_sum_le_sum_abs _ _).trans (sum_le_sum hrow)
  rw [←sum_mul] at htail
  change |∑ j ∈ S, (f j-g j)|≤B*x^b at htail
  rw [hdecomp]
  exact (abs_add_le _ _).trans ((add_le_add h htail).trans_eq (by ring))

/-- Uniform error for a block of powers. The first row's prime error and
the first omitted scale separately govern the admissible exponent. -/
theorem balanced_composites_after_a_block_of_root_scales {J K : ℕ} (hJ : 2≤J) (hJK : J≤K) {b : ℝ}
    (hb : 1/((K:ℝ)+1)<b) (ha : (1/(J:ℝ))*(41999/48000)≤b) :
    ∃ C : ℝ, 0≤C ∧ ∀ n : ℕ, 1≤n →
      |oddSmoothCompositePrice n-unitaryMidpointCenter n-primeMidpointPrice n-
        realMidpointObservation (primeRowsBelow J) n-midpointRootBlock J K n| ≤ C*(n:ℝ)^b := by
  obtain ⟨C,hC,hprefix⟩ := prefix_after_root_block hJ hJK hb ha
  have hb₀ : 0<b := (by positivity : (0:ℝ)<1/((K:ℝ)+1)).trans hb
  let M := (K:ℝ)^2/b+C*(4:ℝ)^b
  have hM : 0≤M := add_nonneg (div_nonneg (sq_nonneg _) hb₀.le) (mul_nonneg hC (by positivity))
  refine ⟨4*M,by positivity,fun n hn => ?_⟩
  have hrow (k : ℕ) (hk : 1≤k) (h4 : k≤4) :
      |fullLogProperPrefix n (k*n:ℕ)-primeRowsBelow J ((k:ℝ)*n)-powersInBlock J K ((k:ℝ)*n)|≤M*(n:ℝ)^b := by
    have hx : 1≤((k*n:ℕ):ℝ) := Nat.one_le_cast.mpr (Nat.mul_pos hk hn)
    have h := hprefix n hn (k*n:ℕ) hx
    have he := mul_le_mul_of_nonneg_left (Real.log_le_rpow_div (Nat.cast_nonneg (α:=ℝ) n) hb₀) (sq_nonneg (K:ℝ))
    have hp := mul_le_mul_of_nonneg_right (Real.rpow_le_rpow (Nat.cast_nonneg (α:=ℝ) k)
      (by exact_mod_cast h4 : (k:ℝ)≤4) hb₀.le) (Real.rpow_nonneg (Nat.cast_nonneg (α:=ℝ) n) b)
    rw [←Nat.cast_mul]
    apply h.trans
    rw [Nat.cast_mul,Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
    dsimp only [M]
    simp only [div_eq_mul_inv] at he ⊢
    linarith only [he,mul_le_mul_of_nonneg_left hp hC]
  have h₂ := abs_le.mp (hrow 2 (by decide) (by decide))
  have h₃ := abs_le.mp (hrow 3 (by decide) (by decide))
  have h₄ := abs_le.mp (hrow 4 (by decide) le_rfl)
  simp only [Nat.cast_ofNat] at h₂ h₃ h₄
  rw [composite_midpoint_minus_prime hn,←midpoint_power_block J K (Nat.cast_nonneg n)]
  rw [realMidpointObservation,realMidpointObservation,abs_le]
  constructor <;> linarith only [h₂.1,h₂.2,h₃.1,h₃.2,h₄.1,h₄.2]

/-- Starting at any exponent J, the entire block up to floor(8J/7)
has a remainder of strictly lower power than its final row. -/
theorem simultaneous_root_terms_of_balanced_composites {J : ℕ} (hJ : 2≤J) :
    let K := 8*J/7
    ∃ b : ℝ, b<1/(K:ℝ) ∧ ∃ C : ℝ, 0≤C ∧ ∀ n : ℕ, 1≤n →
      |oddSmoothCompositePrice n-unitaryMidpointCenter n-primeMidpointPrice n-
        realMidpointObservation (primeRowsBelow J) n-midpointRootBlock J K n| ≤ C*(n:ℝ)^b := by
  let K := 8*J/7
  change ∃ b : ℝ, b<1/(K:ℝ) ∧ _
  have hJK : J≤K := by dsimp only [K]; omega
  have hj : 0<(J:ℝ) := Nat.cast_pos.mpr (by omega)
  have hk : 0<(K:ℝ) := Nat.cast_pos.mpr (by omega)
  have hr : (K:ℝ)*7≤8*J := by exact_mod_cast (show K*7≤8*J by dsimp only [K]; omega)
  have ha : (1/(J:ℝ))*(41999/48000)<1/(K:ℝ) := by
    rw [one_div_mul_eq_div]
    apply (div_lt_div_iff₀ hj hk).mpr
    linarith only [hr,hk]
  have ht : 1/((K:ℝ)+1)<1/(K:ℝ) := one_div_lt_one_div_of_lt hk (lt_add_one _)
  obtain ⟨b,hb,hb'⟩ := exists_between (max_lt ht ha)
  exact ⟨b,hb',balanced_composites_after_a_block_of_root_scales hJ hJK ((le_max_left _ _).trans_lt hb)
    ((le_max_right _ _).trans hb.le)⟩

end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
