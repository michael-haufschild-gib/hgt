import GaloisForLFunctions.ExclusionOfTheCriticalState.Index.TheHighFrequencyMassOfAFiniteLayer

/-!
# A fixed spectral window captures the confinement mass

The relative-window limit bounds the mass of every high unit interval by the
same multiple of the confinement energy. Summing the Poisson tails of these
intervals gives an absolute window radius for every state of a finite layer.
-/

noncomputable section
open MeasureTheory Set Complex Filter Zeta23
open scoped Topology
namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri
  CriticalArithmeticCorrelationTheory HTGeometry _root_.RHTower

private def shellWeight (j : ℕ) : ℝ := 1/(1+(j:ℝ)^2)
private def kernel (d : ℝ) : ℝ := 4/(16+d^2)

private theorem kernel_bounds (d : ℝ) : 0 ≤ kernel d ∧ kernel d ≤ 1 := by
  refine ⟨by unfold kernel; positivity, (div_le_one (by positivity : 0 < 16+d^2)).mpr ?_⟩
  linarith only [sq_nonneg d]

private theorem weight_nonneg' (j : ℕ) : 0 ≤ shellWeight j := by unfold shellWeight; positivity

private theorem summable_shellWeight : Summable shellWeight := by
  apply (summable_nat_add_iff 1).mp
  have h : Summable (fun n : ℕ => 1 / (((n+1 : ℕ) : ℝ)^2)) := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < (2:ℕ)))
  apply h.of_nonneg_of_le (fun n => weight_nonneg' _) (fun n => ?_)
  unfold shellWeight
  exact one_div_le_one_div_of_le (by positivity) (by linarith)

private theorem exists_tail_cut : ∃ N : ℕ, 1 ≤ N ∧ 800*(∑' j : ℕ, if N ≤ j then shellWeight j else 0) ≤ 1 := by
  have hs : Tendsto (fun N : ℕ => ∑' j : ℕ, if N ≤ j then shellWeight j else 0) atTop (𝓝 0) := by
    suffices h : Tendsto (fun N : ℕ => ∑' j : ℕ, if N ≤ j then shellWeight j else 0) atTop
        (𝓝 (∑' _ : ℕ, (0 : ℝ))) by simpa only [tsum_zero] using h
    apply tendsto_tsum_of_dominated_convergence summable_shellWeight
    · intro j
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_gt_atTop j] with N hN
      simp only [if_neg (not_le_of_gt hN)]
    · apply Eventually.of_forall
      intro N j
      split_ifs <;> simp [Real.norm_of_nonneg (weight_nonneg' j),weight_nonneg' j]
  have h := (show Tendsto (fun N : ℕ => 800*(∑' j : ℕ, if N ≤ j then shellWeight j else 0))
      atTop (𝓝 0) by simpa only [mul_zero] using hs.const_mul 800).eventually (gt_mem_nhds zero_lt_one)
  obtain ⟨N,hN,hb⟩ := ((eventually_ge_atTop 1).and h).exists
  exact ⟨N,hN,hb.le⟩

private def unitMass {ι : Type*} (γ m : ι → ℝ) (x : ℝ) (q : ι) : ℝ :=
  if |x-γ q| ≤ 1 then m q else 0

private theorem unit_bounds {ι : Type*} {γ m : ι → ℝ} (hn : ∀ q, 0 ≤ m q) (x : ℝ) (q : ι) :
    0 ≤ unitMass γ m x q ∧ unitMass γ m x q ≤ m q := by
  unfold unitMass
  split_ifs
  · exact ⟨hn q, le_rfl⟩
  · exact ⟨le_rfl, hn q⟩

private theorem summable_unit {ι : Type*} {γ m : ι → ℝ} (hm : Summable m) (hn : ∀ q, 0 ≤ m q) (x : ℝ) :
    Summable (unitMass γ m x) :=
  hm.of_nonneg_of_le (fun q => (unit_bounds hn x q).1) (fun q => (unit_bounds hn x q).2)

private def tag (d : ℝ) : ℕ := ⌊|d|⌋₊

private theorem tagged_weight {d : ℝ} {j : ℕ} (hj : tag d = j) :
    kernel d ≤ 4*shellWeight j := by
  have hj' : (j:ℝ) ≤ |d| := by rw [← hj]; exact Nat.floor_le (abs_nonneg _)
  have hsq := pow_le_pow_left₀ (Nat.cast_nonneg j) hj' 2
  rw [sq_abs] at hsq
  unfold kernel shellWeight
  rw [mul_one_div]
  exact div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith only [hsq])

/-- Both halves of an absolute-distance shell are covered by unit intervals. -/
private theorem tagged_mass {ι : Type*} {m γ : ι → ℝ} (hn : ∀ q, 0 ≤ m q)
    (q : ι) {y : ℝ} {j : ℕ} (hj : tag (y-γ q) = j) :
    m q ≤ unitMass γ m (y+j) q + unitMass γ m (y-j) q := by
  have hl : (j:ℝ) ≤ |y-γ q| := by rw [← hj]; exact Nat.floor_le (abs_nonneg _)
  have hu : |y-γ q| < (j:ℝ)+1 := by rw [← hj]; exact Nat.lt_floor_add_one _
  rcases le_or_gt y (γ q) with h | h
  · rw [abs_of_nonpos (sub_nonpos.mpr h)] at hl hu
    have hc : |y+j-γ q| ≤ 1 := abs_le.mpr ⟨by linarith only [hu],by linarith only [hl]⟩
    rw [show unitMass γ m (y+j) q = m q from if_pos hc]
    exact le_add_of_nonneg_right (unit_bounds hn _ _).1
  · rw [abs_of_nonneg (sub_nonneg.mpr h.le)] at hl hu
    have hc : |y-j-γ q| ≤ 1 := abs_le.mpr ⟨by linarith only [hl],by linarith only [hu]⟩
    rw [show unitMass γ m (y-j) q = m q from if_pos hc]
    exact le_add_of_nonneg_left (unit_bounds hn _ _).1

private def band {ι : Type*} (γ m : ι → ℝ) (y d : ℝ) (q : ι) : ℝ :=
  if |y-γ q| < d then m q*kernel (y-γ q) else 0

private theorem band_bounds {ι : Type*} {γ m : ι → ℝ} (hn : ∀ q, 0 ≤ m q) (y d : ℝ) (q : ι) :
    0 ≤ band γ m y d q ∧ band γ m y d q ≤ m q := by
  unfold band
  split_ifs
  · exact ⟨mul_nonneg (hn q) (kernel_bounds _).1,mul_le_of_le_one_right (hn q) (kernel_bounds _).2⟩
  · exact ⟨le_rfl,hn q⟩

private theorem band_summable {ι : Type*} {γ m : ι → ℝ} (hm : Summable m) (hn : ∀ q, 0 ≤ m q) (y d : ℝ) :
    Summable (band γ m y d) :=
  hm.of_nonneg_of_le (fun q => (band_bounds hn y d q).1) (fun q => (band_bounds hn y d q).2)

/-- A uniform unit-interval estimate at high ordinates gives a summable
bound for the discarded Poisson shells. -/
private theorem band_tail {ι : Type*} {γ m : ι → ℝ} (hm : Summable m) (hn : ∀ q, 0 ≤ m q)
    {y B : ℝ} (hy : 0 ≤ y) (hB : 0 ≤ B) (hunit : ∀ x, y/2 ≤ x → (∑' q, unitMass γ m x q) ≤ B)
    (N : ℕ) :
    (∑' q, band γ m y (y/2) q) ≤ (∑' q, band γ m y N q) +
      (8*B)*(∑' j : ℕ, if N ≤ j then shellWeight j else 0) := by
  classical
  let n := fun q : ι => tag (y-γ q)
  let T := fun q : ι => if N ≤ n q then band γ m y (y/2) q else 0
  have hT0 (q : ι) : 0 ≤ T q := by unfold T; split_ifs <;> first | exact (band_bounds hn y (y/2) q).1 | exact le_rfl
  have hT : Summable T := hm.of_nonneg_of_le hT0 (fun q => by
    unfold T; split_ifs <;> first | exact (band_bounds hn y (y/2) q).2 | exact hn q)
  let U := fun j : ℕ => if N ≤ j then shellWeight j else 0
  have hU0 (j : ℕ) : 0 ≤ U j := by unfold U; split_ifs <;> first | exact weight_nonneg' _ | exact le_rfl
  have hU : Summable U := summable_shellWeight.of_nonneg_of_le hU0 (fun j => by
    unfold U; split_ifs <;> first | exact le_rfl | exact weight_nonneg' _)
  have hfib (j : ℕ) : (∑' q : {q // n q = j}, T q.val) ≤ (8*B)*U j := by
    by_cases hit : ∃ q : {q // n q = j}, N ≤ n q.val ∧ |y-γ q.val| < y/2
    · obtain ⟨q₀,hN,hwide⟩ := hit
      have hNj : N ≤ j := q₀.property ▸ hN
      have hj : (j:ℝ) < y/2 := by
        rw [← q₀.property]
        exact (Nat.floor_le (abs_nonneg _)).trans_lt hwide
      let V := fun q : ι => unitMass γ m (y+j) q + unitMass γ m (y-j) q
      have hV : Summable V := (summable_unit hm hn _).add (summable_unit hm hn _)
      have hV0 (q : ι) : 0 ≤ V q := add_nonneg (unit_bounds hn _ _).1 (unit_bounds hn _ _).1
      have hscale : 0 ≤ 4*shellWeight j := mul_nonneg (by norm_num) (weight_nonneg' j)
      have hle (q : {q // n q = j}) : T q.val ≤ (4*shellWeight j)*V q.val := by
        rw [show T q.val = band γ m y (y/2) q.val from if_pos (q.property.symm ▸ hNj)]
        unfold band
        split_ifs
        · rw [mul_comm (m q.val)]
          exact mul_le_mul (tagged_weight q.property) (tagged_mass hn q.val q.property) (hn _) hscale
        · exact mul_nonneg hscale (hV0 _)
      have hs := (hT.subtype (fun q => n q = j)).tsum_le_tsum hle
        ((hV.subtype (fun q => n q = j)).mul_left (4*shellWeight j))
      rw [tsum_mul_left] at hs
      have hsub : (∑' q : {q // n q = j}, V q.val) ≤ ∑' q, V q := by
        rw [← hV.tsum_subtype_add_tsum_subtype_compl {q | n q = j}]
        exact le_add_of_nonneg_right (tsum_nonneg fun q => hV0 q.val)
      have hsum : (∑' q, V q) ≤ B+B := by
        rw [show (∑' q, V q) = (∑' q, unitMass γ m (y+j) q) + ∑' q, unitMass γ m (y-j) q from
          (summable_unit hm hn _).tsum_add (summable_unit hm hn _)]
        exact add_le_add (hunit _ (by linarith only [hy,(Nat.cast_nonneg j : (0 : ℝ) ≤ j)])) (hunit _ (by linarith only [hj]))
      calc _ ≤ (4*shellWeight j)*(B+B) :=
            hs.trans (mul_le_mul_of_nonneg_left (hsub.trans hsum) hscale)
           _ = _ := by rw [show U j = shellWeight j from if_pos hNj]; ring
    · have hz (q : {q // n q = j}) : T q.val = 0 := by
        by_cases h : N ≤ n q.val
        · have h' : ¬ |y-γ q.val| < y/2 := fun e => hit ⟨q,h,e⟩
          simp only [T,if_pos h,band,if_neg h']
        · simp only [T,if_neg h]
      simp_rw [hz,tsum_zero]
      exact mul_nonneg (mul_nonneg (by norm_num) hB) (hU0 j)
  have hS : HasSum (fun j : ℕ => ∑' q : {q // n q = j}, T q.val) (∑' q, T q) :=
    hT.hasSum.tsum_fiberwise n
  have htail := hS.summable.tsum_le_tsum hfib (hU.mul_left (8*B))
  rw [hS.tsum_eq,tsum_mul_left] at htail
  have hpoint (q : ι) : band γ m y (y/2) q ≤ band γ m y N q + T q := by
    by_cases h : N ≤ n q
    · rw [show T q = band γ m y (y/2) q from if_pos h]
      exact le_add_of_nonneg_left (band_bounds hn _ _ _).1
    · have hx : |y-γ q| < (N:ℝ) := (Nat.floor_lt (abs_nonneg _)).mp (lt_of_not_ge h)
      rw [show T q = 0 from if_neg h,add_zero,show band γ m y N q = _ from if_pos hx]
      unfold band
      split_ifs <;> first | exact le_rfl | exact mul_nonneg (hn _) (kernel_bounds _).1
  have h := (band_summable hm hn _ _).tsum_le_tsum hpoint ((band_summable hm hn _ _).add hT)
  rw [(band_summable hm hn _ _).tsum_add hT] at h
  exact h.trans (add_le_add le_rfl htail)

private theorem unit_le_band {ι : Type*} {γ m : ι → ℝ} (hm : Summable m) (hn : ∀ q, 0 ≤ m q)
    {x : ℝ} (hx : 2 < x) :
    (∑' q, unitMass γ m x q) ≤ 5*(∑' q, band γ m x (x/2) q) := by
  rw [← tsum_mul_left]
  apply (summable_unit hm hn x).tsum_le_tsum _ ((band_summable hm hn x (x/2)).mul_left 5)
  intro q
  by_cases h : |x-γ q| ≤ 1
  · rw [show unitMass γ m x q = m q from if_pos h,
      show band γ m x (x/2) q = _ from if_pos (by linarith only [hx,h] : |x-γ q| < x/2)]
    have hsq := pow_le_pow_left₀ (abs_nonneg (x-γ q)) h 2
    rw [sq_abs,one_pow] at hsq
    have hw : 1 ≤ 5*kernel (x-γ q) := by
      unfold kernel
      rw [← mul_div_assoc,le_div_iff₀ (by positivity)]
      linarith only [hsq]
    calc m q ≤ m q*(5*kernel (x-γ q)) := le_mul_of_one_le_right (hn _) hw
         _ = _ := by ring
  · rw [show unitMass γ m x q = 0 from if_neg h]
    exact mul_nonneg (by norm_num) (band_bounds hn _ _ _).1

/-- A single absolute integer radius captures confinement energy at every
sufficiently high ordinate for every state of every finite off-line layer. -/
theorem exists_fixed_window_capturing_confinement_mass :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ {R : ℝ}, 0 < R → ∀ {F : ℝ → ℝ}, IsConfinedNullVector R F →
      BacklundConverse.FiniteOffLine → ∀ᶠ y : ℝ in atTop,
      2*(criticalAliasCoefficient R*criticalHalfLineExponentialPair F F) ≤
      y^2*((criticalAliasCoefficient R/2)*‖negativeHalfLineLaplace (cx F) ⟨-4,y⟩‖^2 +
        ∑' q : onLineCopies, if |y-(centredZero q).im| < (N:ℝ) then
          zeroValueMass F q * (4/(16+(y-(centredZero q).im)^2)) else 0) := by
  obtain ⟨N,hN,hcut⟩ := exists_tail_cut
  refine ⟨N,hN,?_⟩
  intro R hr F hF hf
  let P := criticalAliasCoefficient R*criticalHalfLineExponentialPair F F
  let d := fun y : ℝ => (criticalAliasCoefficient R/2)*‖negativeHalfLineLaplace (cx F) ⟨-4,y⟩‖^2
  let m := fun q : onLineCopies => zeroValueMass F q
  let γ := fun q : onLineCopies => (centredZero q).im
  let W := fun y : ℝ => y^2*(d y + ∑' q, band γ m y (y/2) q)
  have hP : 0 < P := mul_pos (criticalAliasCoefficient_positive hr) (exponentialPair_self_pos hF.1 hF.2.1)
  have hn (q : onLineCopies) : 0 ≤ m q := zeroValueMass_nonneg _ _
  have hm : Summable m := (domain_zeroParseval_of_finiteOffLine hF.1 hf).1
  have hW : Tendsto W atTop (𝓝 (4*P)) := by
    have h := (hF.localized_high_frequency_mass hr hf (δ := 1/2) (by norm_num) (by norm_num)).2
    simp_rw [show ∀ y : ℝ, (1/2)*y = y/2 from fun y => by ring] at h
    exact h
  have h3 := hW.eventually (lt_mem_nhds (by linarith only [hP] : 3*P < 4*P))
  have h5 := hW.eventually (gt_mem_nhds (by linarith only [hP] : 4*P < 5*P))
  obtain ⟨b,hb⟩ := eventually_atTop.mp ((eventually_gt_atTop (2:ℝ)).and (h3.and h5))
  have hu (x : ℝ) (hx : b ≤ x) : x^2*(∑' q, unitMass γ m x q) ≤ 25*P := by
    obtain ⟨hx2,-,hupper⟩ := hb x hx
    have h := mul_le_mul_of_nonneg_left (unit_le_band (γ := γ) hm hn hx2) (sq_nonneg x)
    have hd : 0 ≤ d x := mul_nonneg (div_nonneg (criticalAliasCoefficient_positive hr).le two_pos.le) (sq_nonneg _)
    change x^2*(d x + ∑' q, band γ m x (x/2) q) < 5*P at hupper
    nlinarith only [h,hupper,mul_nonneg (sq_nonneg x) hd]
  filter_upwards [eventually_ge_atTop (max (2*b) (max b 1))] with y hy
  have hby : b ≤ y/2 := by linarith only [(le_max_left (2*b) (max b 1)).trans hy]
  have hby' : b ≤ y := (le_max_left b 1).trans ((le_max_right _ _).trans hy)
  have hy0 : 0 ≤ y := zero_le_one.trans ((le_max_right b 1).trans ((le_max_right _ _).trans hy))
  let m' := fun q : onLineCopies => y^2*m q
  have hm' : Summable m' := hm.mul_left _
  have hn' (q : onLineCopies) : 0 ≤ m' q := mul_nonneg (sq_nonneg _) (hn _)
  have hunit (x : ℝ) (hx : y/2 ≤ x) : (∑' q, unitMass γ m' x q) ≤ 100*P := by
    have he : (∑' q, unitMass γ m' x q) = y^2*(∑' q, unitMass γ m x q) := by
      rw [← tsum_mul_left]
      apply tsum_congr; intro q
      unfold unitMass m'; split_ifs <;> simp
    rw [he]
    have hsq := pow_le_pow_left₀ hy0 (by linarith only [hx] : y ≤ 2*x) 2
    have hnn : 0 ≤ ∑' q, unitMass γ m x q := tsum_nonneg fun q => (unit_bounds hn _ _).1
    nlinarith only [mul_le_mul_of_nonneg_right hsq hnn,hu x (hby.trans hx)]
  have ht := band_tail (γ := γ) (B := 100*P) hm' hn' hy0 (mul_nonneg (by norm_num) hP.le) hunit N
  have hs (width : ℝ) : (∑' q, band γ m' y width q) = y^2*(∑' q, band γ m y width q) := by
    rw [← tsum_mul_left]
    apply tsum_congr; intro q
    unfold band m'; split_ifs <;> ring
  rw [hs,hs] at ht
  have htail := mul_le_mul_of_nonneg_left hcut hP.le
  have hl := (hb y hby').2.1
  change 3*P < y^2*(d y + ∑' q, band γ m y (y/2) q) at hl
  change 2*P ≤ y^2*(d y + ∑' q, band γ m y N q)
  nlinarith only [ht,htail,hl]

#print axioms exists_fixed_window_capturing_confinement_mass
end GaloisForLFunctions.ExclusionOfTheCriticalState
