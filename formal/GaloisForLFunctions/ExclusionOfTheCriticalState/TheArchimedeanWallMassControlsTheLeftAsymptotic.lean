import GaloisForLFunctions.ExclusionOfTheCriticalState.TheLevyHeadResolvesTheWallCharges
import GaloisForLFunctions.ExclusionOfTheCriticalState.TheTransformOfTheStateVanishesUniformlyToTheLeft

/-!
# The leading mass of the archimedean wall balance

The critical state's oriented archimedean modes have positive weights.
After multiplication by the distance to the wall, each resolvent multiplier
tends to one. The resulting balance tends to the total mode mass when that
mass is finite, and diverges when it is infinite. In both cases the scaled
balance stays bounded away from zero.
-/

noncomputable section
open MeasureTheory Set Filter Complex Topology
namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri
  CriticalArithmeticCorrelationTheory HTGeometry _root_.RHTower

private theorem tendsto_resolvent_scaling {r : ℝ} (hr : 0 < r) :
    Tendsto (fun t : ℝ => t/(r+t)) atTop (𝓝 1) := by
  have hd : Tendsto (fun t : ℝ => r/t) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv,mul_zero] using
      (tendsto_inv_atTop_zero.const_mul r)
  have hi : Tendsto (fun t : ℝ => (r/t+1)⁻¹) atTop (𝓝 1) := by
    simpa only [zero_add,inv_one] using (hd.add_const 1).inv₀ (by norm_num)
  refine hi.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  have hs : r+t ≠ 0 := (add_pos hr ht).ne'
  field_simp [ht.ne',hs]

private theorem tendsto_scaled_resolvent_sum {b r : ℕ → ℝ}
    (hb : ∀ k, 0 ≤ b k) (hr : ∀ k, 0 < r k) (hs : Summable b) :
    Tendsto (fun t : ℝ => ∑' k, b k*(t/(r k+t))) atTop (𝓝 (∑' k,b k)) := by
  apply tendsto_tsum_of_dominated_convergence hs
  · intro k
    simpa only [mul_one] using (tendsto_resolvent_scaling (hr k)).const_mul (b k)
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht k
    have hd : 0 < r k+t := add_pos (hr k) ht
    rw [Real.norm_of_nonneg (mul_nonneg (hb k) (div_nonneg ht.le hd.le))]
    calc
      b k*(t/(r k+t)) ≤ b k*1 := mul_le_mul_of_nonneg_left
        ((div_le_one hd).mpr (by linarith only [hr k])) (hb k)
      _ = b k := mul_one _

private theorem tendsto_scaled_resolvent_sum_atTop {b r : ℕ → ℝ}
    (hb : ∀ k, 0 ≤ b k) (hr : ∀ k, 0 < r k)
    (hs : ∀ t : ℝ, 0 < t → Summable fun k => b k*(t/(r k+t)))
    (hn : ¬ Summable b) :
    Tendsto (fun t : ℝ => ∑' k, b k*(t/(r k+t))) atTop atTop := by
  refine tendsto_atTop.mpr fun C => ?_
  have hlarge : ∃ s : Finset ℕ, C < ∑ k ∈ s, b k := by
    by_contra h
    push Not at h
    exact hn (summable_of_sum_le hb h)
  obtain ⟨s,hC⟩ := hlarge
  have hlim : Tendsto (fun t : ℝ => ∑ k ∈ s, b k*(t/(r k+t))) atTop
      (𝓝 (∑ k ∈ s,b k)) :=
    tendsto_finsetSum s fun k _ => by
      simpa only [mul_one] using (tendsto_resolvent_scaling (hr k)).const_mul (b k)
  have he : ∀ᶠ t : ℝ in atTop, C < ∑ k ∈ s, b k*(t/(r k+t)) :=
    hlim.eventually (Ioi_mem_nhds hC)
  filter_upwards [he,eventually_gt_atTop (0 : ℝ)] with t hCt ht
  refine hCt.le.trans (Summable.sum_le_tsum s (fun k _ => ?_) (hs t ht))
  exact mul_nonneg (hb k) (div_nonneg ht.le (add_pos (hr k) ht).le)

/-- The archimedean exponents after removal of the positive half-charge. -/
def archimedeanWallRate (k : ℕ) : ℝ := 2*((k : ℝ)+1)+1/2

/-- Orientation by the positive half-charge makes every actual-state mode positive. -/
def archimedeanWallWeight (F : ℝ → ℝ) (k : ℕ) : ℝ :=
  (negativeHalfLineLaplace (cx F) (1/2)).re *
    (negativeHalfLineLaplace (cx F) (archimedeanWallRate k : ℂ)).re

/-- The actual continuation's balance after removal of the prime heads and negative charge. -/
def archimedeanWallBalance (W₀ : ℝ) (F : ℝ → ℝ) (t : ℝ) : ℝ :=
  (negativeHalfLineLaplace (cx F) (1/2)).re *
    (-(criticalAliasCoefficient W₀ : ℂ)*stateMeromorphic W₀ F (-(t : ℂ)-8) -
      primeHead F (-(t : ℂ)) -
      negativeHalfLineLaplace (cx F) (-(1/2))/(-(t : ℂ)+1/2)).re

private theorem archimedeanWallRate_pos (k : ℕ) : 0 < archimedeanWallRate k := by
  dsimp only [archimedeanWallRate]
  positivity

theorem criticalState_archimedeanWallWeight_pos {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) (k : ℕ) :
    0 < archimedeanWallWeight F k := by
  apply criticalState_laplace_half_mul_pos hW ht hF
  dsimp only [archimedeanWallRate]
  linarith only [Nat.cast_nonneg (α := ℝ) k]

private theorem summable_wall_complex_resolvents {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) {t : ℝ} (ht : 0 < t) :
    Summable fun k : ℕ => negativeHalfLineLaplace (cx F) (archimedeanWallRate k : ℂ) /
      ((archimedeanWallRate k : ℂ)+(t : ℂ)) := by
  have h := (summable_nat_add_iff 1).mpr
    (hasSum_levyHead_resolvents hF (p := -(t : ℂ))
      (by simp only [neg_re,ofReal_re]; linarith only [ht])).summable
  simpa only [archimedeanWallRate,Nat.cast_add,Nat.cast_one,Complex.ofReal_add,
    Complex.ofReal_mul,Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_one,
    Complex.ofReal_ofNat,sub_neg_eq_add] using h

private theorem re_wall_complex_resolvent (F : ℝ → ℝ) (k : ℕ) (t : ℝ) :
    (negativeHalfLineLaplace (cx F) (archimedeanWallRate k : ℂ) /
      ((archimedeanWallRate k : ℂ)+(t : ℂ))).re =
    (negativeHalfLineLaplace (cx F) (archimedeanWallRate k : ℂ)).re /
      (archimedeanWallRate k+t) := by
  rw [← Complex.ofReal_add,Complex.div_ofReal_re]

/-- The weighted resolvents are summable even when their total numerator mass is infinite. -/
theorem summable_archimedeanWallResolvent {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) {t : ℝ} (ht : 0 < t) :
    Summable fun k => archimedeanWallWeight F k/(archimedeanWallRate k+t) := by
  have h := (Complex.reCLM.summable (summable_wall_complex_resolvents hF ht)).mul_left
    (negativeHalfLineLaplace (cx F) (1/2)).re
  refine h.congr fun k => ?_
  change (negativeHalfLineLaplace (cx F) (1/2)).re *
    (negativeHalfLineLaplace (cx F) (archimedeanWallRate k : ℂ) /
      ((archimedeanWallRate k : ℂ)+(t : ℂ))).re = _
  rw [re_wall_complex_resolvent]
  dsimp only [archimedeanWallWeight]
  ring


private theorem hasSum_archimedeanWallResolvent {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) {t : ℝ} (ht : 0 < t) :
    HasSum (fun k => archimedeanWallWeight F k/(archimedeanWallRate k+t))
      ((negativeHalfLineLaplace (cx F) (1/2)).re *
        (∑' k, negativeHalfLineLaplace (cx F) (archimedeanWallRate k : ℂ) /
          ((archimedeanWallRate k : ℂ)+(t : ℂ))).re) := by
  have h := (Complex.reCLM.hasSum (summable_wall_complex_resolvents hF ht).hasSum).mul_left
    (negativeHalfLineLaplace (cx F) (1/2)).re
  refine h.congr_fun fun k => ?_
  change archimedeanWallWeight F k/(archimedeanWallRate k+t) =
    (negativeHalfLineLaplace (cx F) (1/2)).re *
      (negativeHalfLineLaplace (cx F) (archimedeanWallRate k : ℂ) /
        ((archimedeanWallRate k : ℂ)+(t : ℂ))).re
  rw [re_wall_complex_resolvent]
  dsimp only [archimedeanWallWeight]
  ring

/-- The state, prime heads and negative charge leave precisely the positive-mode resolvent. -/
theorem archimedeanWallBalance_eq_resolvents {W₀ : ℝ} (hW : 0 < W₀)
    {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F) {t : ℝ} (ht : 1/2 < t) :
    archimedeanWallBalance W₀ F t =
      ∑' k, archimedeanWallWeight F k/(archimedeanWallRate k+t) := by
  have ha : (criticalAliasCoefficient W₀ : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (criticalAliasCoefficient_positive hW).ne'
  have hcancel (q : ℂ) : -(criticalAliasCoefficient W₀ : ℂ)*
      (-q/criticalAliasCoefficient W₀) = q := by
    field_simp [ha]
  have he : -(criticalAliasCoefficient W₀ : ℂ)*stateMeromorphic W₀ F (-(t : ℂ)-8) -
      primeHead F (-(t : ℂ)) -
      negativeHalfLineLaplace (cx F) (-(1/2))/(-(t : ℂ)+1/2) =
      ∑' k, negativeHalfLineLaplace (cx F) (archimedeanWallRate k : ℂ) /
        ((archimedeanWallRate k : ℂ)+(t : ℂ)) := by
    rw [stateMeromorphic_eq_resolvents hF
      (by change -t-8 < -(17/2 : ℝ); linarith only [ht]),
      show -(t : ℂ)-8+8 = -(t : ℂ) by ring,hcancel]
    simp only [sub_neg_eq_add]
    have hsum : (∑' k : ℕ, negativeHalfLineLaplace (cx F) (2*(k+1)+1/2) /
        ((2*(k+1)+1/2 : ℂ)+(t : ℂ))) =
        ∑' k, negativeHalfLineLaplace (cx F) (archimedeanWallRate k : ℂ) /
          ((archimedeanWallRate k : ℂ)+(t : ℂ)) := by
      apply tsum_congr
      intro k
      simp only [archimedeanWallRate,Complex.ofReal_add,Complex.ofReal_mul,
        Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_one,Complex.ofReal_ofNat]
    rw [hsum]
    ring
  unfold archimedeanWallBalance
  rw [he]
  exact (hasSum_archimedeanWallResolvent hF (by linarith only [ht])).tsum_eq.symm

private theorem summable_scaled_archimedeanWallResolvent {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) {t : ℝ} (ht : 0 < t) :
    Summable fun k => archimedeanWallWeight F k*(t/(archimedeanWallRate k+t)) := by
  have h := (summable_archimedeanWallResolvent hF ht).mul_left t
  refine h.congr fun k => ?_
  ring

/-- Scaling the actual balance multiplies every positive mode by `t/(r+t)`. -/
theorem scaled_archimedeanWallBalance_eq_tsum {W₀ : ℝ} (hW : 0 < W₀)
    {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F) {t : ℝ} (ht : 1/2 < t) :
    t*archimedeanWallBalance W₀ F t =
      ∑' k, archimedeanWallWeight F k*(t/(archimedeanWallRate k+t)) := by
  rw [archimedeanWallBalance_eq_resolvents hW hF ht,← tsum_mul_left]
  apply tsum_congr
  intro k
  ring

/-- The actual balance has a finite positive leading mass, or its scaled size diverges.
The two alternatives require no summability or boundary-trace hypothesis. -/
theorem criticalState_archimedeanWall_asymptotic {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) :
    (Summable (archimedeanWallWeight F) ∧
      0 < ∑' k, archimedeanWallWeight F k ∧
      Tendsto (fun t : ℝ => t*archimedeanWallBalance W₀ F t) atTop
        (𝓝 (∑' k,archimedeanWallWeight F k))) ∨
    (¬ Summable (archimedeanWallWeight F) ∧
      Tendsto (fun t : ℝ => t*archimedeanWallBalance W₀ F t) atTop atTop) := by
  have hd := criticalHalfLineEnergyDomain_of_groundState hF
  have hpos := criticalState_archimedeanWallWeight_pos hW hthreshold hF
  have he : (fun t : ℝ => ∑' k, archimedeanWallWeight F k*(t/(archimedeanWallRate k+t)))
      =ᶠ[atTop] fun t => t*archimedeanWallBalance W₀ F t := by
    filter_upwards [eventually_gt_atTop (1/2 : ℝ)] with t ht
    exact (scaled_archimedeanWallBalance_eq_tsum hW hd ht).symm
  by_cases hs : Summable (archimedeanWallWeight F)
  · refine Or.inl ⟨hs,hs.tsum_pos (fun k => (hpos k).le) 0 (hpos 0),?_⟩
    exact (tendsto_scaled_resolvent_sum (fun k => (hpos k).le)
      archimedeanWallRate_pos hs).congr' he
  · refine Or.inr ⟨hs,?_⟩
    exact (tendsto_scaled_resolvent_sum_atTop (fun k => (hpos k).le)
      archimedeanWallRate_pos (fun t ht => summable_scaled_archimedeanWallResolvent hd ht)
      hs).congr' he

/-- The oriented balance retains a strictly positive inverse-distance scale. -/
theorem criticalState_scaled_wall_eventually_pos {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ t : ℝ in atTop, c ≤ t*archimedeanWallBalance W₀ F t := by
  rcases criticalState_archimedeanWall_asymptotic hW hthreshold hF with hfinite | hinfinite
  · obtain ⟨_,hpos,hlim⟩ := hfinite
    refine ⟨(∑' k,archimedeanWallWeight F k)/2,by linarith only [hpos],?_⟩
    have he : ∀ᶠ t : ℝ in atTop,
        (∑' k,archimedeanWallWeight F k)/2 < t*archimedeanWallBalance W₀ F t :=
      hlim.eventually (Ioi_mem_nhds (by linarith only [hpos]))
    exact he.mono fun _ ht => ht.le
  · exact ⟨1,zero_lt_one,tendsto_atTop.mp hinfinite.2 1⟩

/-- The actual charge-subtracted balance cannot decay faster than inverse distance. -/
theorem criticalState_scaled_wall_not_tendsto_zero {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) :
    ¬ Tendsto (fun t : ℝ => t*archimedeanWallBalance W₀ F t) atTop (𝓝 0) := by
  intro hz
  obtain ⟨c,hc,hbound⟩ := criticalState_scaled_wall_eventually_pos hW hthreshold hF
  have hsmall : ∀ᶠ t : ℝ in atTop, t*archimedeanWallBalance W₀ F t < c :=
    hz.eventually (Iio_mem_nhds hc)
  obtain ⟨t,hge,hlt⟩ := (hbound.and hsmall).exists
  exact not_lt_of_ge hge hlt

end GaloisForLFunctions.ExclusionOfTheCriticalState
