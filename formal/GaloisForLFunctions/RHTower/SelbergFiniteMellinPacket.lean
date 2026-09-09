import GaloisForLFunctions.HTGeometry.ExponentialPolynomialWindowMean
import GaloisForLFunctions.RHTower.SelbergWeightedPathEnergy
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Sharp finite Mellin packet admission

Normalize a finite exponential packet by a maximal active exponent. The exact
window-mean law extracts its coefficient with bounded error, while native L²
energy permits only square-root window growth. Every surviving exponent must
therefore have negative real part. The converse is proved from integrable
exponential modes. The literal logarithmic substitution transports this test to
the native Mellin half-density above height two.
-/

open Complex Set MeasureTheory
open scoped BigOperators
namespace GaloisForLFunctions.RHTower.SelbergFiniteMellinPacket
open GaloisForLFunctions.HTGeometry
open SelbergWeightedPathEnergy
noncomputable section
variable {ι : Type*}

/-- The complete finite logarithmic-height power packet. -/
def packet (s : Finset ι) (c a : ι → ℂ) (t : ℝ) : ℂ :=
  ∑ i ∈ s, c i*Complex.exp (a i*(t:ℂ))

/-- Finite packets retain continuity on the complete logarithmic-height line. -/
theorem packet_continuous (s : Finset ι) (c a : ι → ℂ) : Continuous (packet s c a) := by
  unfold packet
  fun_prop

/-- Normalizing by one exponent gives an exact finite exponential polynomial. -/
def normalizedPolynomial (s : Finset ι) (c a : ι → ℂ) (k : ι) : ExpPoly :=
  s.toList.map (fun i => (c i,a i-a k))

/-- The normalized polynomial is the actual complete packet multiplied by the inverse selected mode. -/
theorem normalizedPolynomial_eval (s : Finset ι) (c a : ι → ℂ) (k : ι) (t : ℝ) :
    (normalizedPolynomial s c a k).eval t =
      Complex.exp (-(a k*(t:ℂ)))*packet s c a t := by
  simp only [normalizedPolynomial,ExpPoly.eval,List.map_map,Function.comp_def,Finset.sum_map_toList]
  rw [packet,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_left_comm,← Complex.exp_add]
  congr 2
  ring

/-- Distinct original exponents make the selected coefficient the exact constant term. -/
theorem normalizedPolynomial_constTerm (s : Finset ι) (c a : ι → ℂ) {k : ι}
    (hk : k ∈ s) (hinj : Set.InjOn a (s:Set ι)) :
    (normalizedPolynomial s c a k).constTerm=c k := by
  classical
  simp only [normalizedPolynomial,ExpPoly.constTerm,List.map_map,Function.comp_def,Finset.sum_map_toList]
  rw [Finset.sum_eq_single k]
  · simp
  · intro j hj hne
    rw [if_neg]
    intro h
    exact hne (hinj hj hk (sub_eq_zero.mp h))
  · exact fun h => False.elim (h hk)

/-- Choosing a largest real exponent leaves only nonpositive exponents in the normalized packet. -/
theorem normalizedPolynomial_decaying (s : Finset ι) (c a : ι → ℂ) (k : ι)
    (hmax : ∀ i ∈ s, (a i).re ≤ (a k).re) :
    (normalizedPolynomial s c a k).Decaying := by
  intro p hp
  simp only [normalizedPolynomial,List.mem_map,Finset.mem_toList] at hp
  obtain ⟨i,hi,rfl⟩ := hp
  simpa only [Complex.sub_re,sub_nonpos] using hmax i hi

/-- The complete normalized packet extracts its selected coefficient with a uniform finite-window error. -/
theorem coefficient_window_error (s : Finset ι) (c a : ι → ℂ) {k : ι}
    (hk : k ∈ s) (hinj : Set.InjOn a (s:Set ι))
    (hmax : ∀ i ∈ s, (a i).re ≤ (a k).re) {T : ℝ} (hT : 0 ≤ T) :
    ‖(∫ t in (0:ℝ)..T, Complex.exp (-(a k*(t:ℂ)))*packet s c a t)-(T:ℂ)*c k‖ ≤
      2*(normalizedPolynomial s c a k).decayNorm := by
  have h := ExpPoly.norm_integral_sub_constTerm_le (normalizedPolynomial s c a k)
    (normalizedPolynomial_decaying s c a k hmax) (A:=0) (by norm_num) hT
  simpa only [zero_add,normalizedPolynomial_eval,normalizedPolynomial_constTerm s c a hk hinj] using h

/-- A nonnegative leading real exponent cannot survive uniformly bounded full packet energy. -/
theorem leading_coefficient_zero_of_energy_bound (s : Finset ι) (c a : ι → ℂ) {k : ι}
    (hk : k ∈ s) (hinj : Set.InjOn a (s:Set ι))
    (hmax : ∀ i ∈ s, (a i).re ≤ (a k).re) (ha : 0 ≤ (a k).re)
    (M : ℝ) (hM : ∀ T : ℝ, 0 ≤ T → (∫ t in (0:ℝ)..T, ‖packet s c a t‖^2) ≤ M) :
    c k=0 := by
  by_contra hc
  have hcpos : 0 < ‖c k‖ := norm_pos_iff.mpr hc
  let K : ℝ := 2*(normalizedPolynomial s c a k).decayNorm
  obtain ⟨T,hT⟩ := exists_gt (max 0 (max (2*K/‖c k‖) (4*M/‖c k‖^2)))
  have hTpos : 0 < T := (le_max_left _ _).trans_lt hT
  have hK : 2*K < T*‖c k‖ :=
    (div_lt_iff₀ hcpos).mp ((le_trans (le_max_left _ _) (le_max_right _ _)).trans_lt hT)
  have hMM : 4*M < T*‖c k‖^2 :=
    (div_lt_iff₀ (sq_pos_of_pos hcpos)).mp
      ((le_trans (le_max_right _ _) (le_max_right _ _)).trans_lt hT)
  let g : ℝ → ℂ := fun t => Complex.exp (-(a k*(t:ℂ)))*packet s c a t
  have hg : Continuous g :=
    (Complex.continuous_exp.comp (by fun_prop)).mul (packet_continuous s c a)
  have hsmall (t : ℝ) (ht : 0 ≤ t) : ‖g t‖ ≤ ‖packet s c a t‖ := by
    dsimp [g]
    rw [norm_mul]
    apply mul_le_of_le_one_left (norm_nonneg _)
    rw [Complex.norm_exp]
    apply Real.exp_le_one_iff.mpr
    simp only [Complex.neg_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
    exact neg_nonpos.mpr (mul_nonneg ha ht)
  have hsq : (∫ t in (0:ℝ)..T, ‖g t‖^2) ≤ M := by
    apply le_trans (intervalIntegral.integral_mono_on hTpos.le
      ((hg.norm.pow 2).intervalIntegrable 0 T)
      (((packet_continuous s c a).norm.pow 2).intervalIntegrable 0 T) ?_) (hM T hTpos.le)
    intro t ht
    exact pow_le_pow_left₀ (norm_nonneg _) (hsmall t ht.1) 2
  have hCS := normSq_integral_le_resistance_energy hg continuous_const
    (show ∀ _ : ℝ, 0 < (1:ℝ) from fun _ => by norm_num) hTpos.le
  simp only [resistance,div_one,intervalIntegral.integral_const,sub_zero,smul_eq_mul,mul_one,
    one_mul,Complex.normSq_eq_norm_sq] at hCS
  have hupper : ‖∫ t in (0:ℝ)..T, g t‖^2 ≤ T*M :=
    hCS.trans (mul_le_mul_of_nonneg_left hsq hTpos.le)
  have herr := coefficient_window_error s c a hk hinj hmax hTpos.le
  change ‖(∫ t in (0:ℝ)..T, g t)-(T:ℂ)*c k‖ ≤ K at herr
  have htriangle := norm_le_norm_add_norm_sub (∫ t in (0:ℝ)..T, g t) ((T:ℂ)*c k)
  rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg hTpos.le] at htriangle
  have hlower : T*‖c k‖ < 2*‖∫ t in (0:ℝ)..T, g t‖ := by linarith
  have hprod := mul_pos (sub_pos.mpr hlower)
    (show 0 < 2*‖∫ t in (0:ℝ)..T, g t‖+T*‖c k‖ by positivity)
  have hlast := mul_lt_mul_of_pos_left hMM hTpos
  nlinarith

/-- Zero coefficients can be removed without changing any value of the complete packet. -/
theorem packet_active_support (s : Finset ι) (c a : ι → ℂ) :
    packet (s.filter (fun i => c i ≠ 0)) c a = packet s c a := by
  classical
  funext t
  simp only [packet,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs with h
  · rfl
  · simp only [not_not] at h
    simp [h]

/-- Every nonzero coefficient in a bounded-energy finite packet has strictly negative real exponent. -/
theorem active_exponent_negative_of_energy_bound (s : Finset ι) (c a : ι → ℂ)
    (hinj : Set.InjOn a (s:Set ι))
    (M : ℝ) (hM : ∀ T : ℝ, 0 ≤ T → (∫ t in (0:ℝ)..T, ‖packet s c a t‖^2) ≤ M)
    {j : ι} (hj : j ∈ s) (hcj : c j ≠ 0) : (a j).re < 0 := by
  classical
  by_contra hjneg
  let u := s.filter (fun i => c i ≠ 0)
  have hju : j ∈ u := Finset.mem_filter.mpr ⟨hj,hcj⟩
  obtain ⟨k,hk,hmax⟩ := u.exists_max_image (fun i => (a i).re) ⟨j,hju⟩
  have hck : c k ≠ 0 := (Finset.mem_filter.mp hk).2
  apply hck
  exact leading_coefficient_zero_of_energy_bound u c a hk
    (fun _ hi _ hl he => hinj (Finset.mem_filter.mp hi).1 (Finset.mem_filter.mp hl).1 he)
    hmax ((le_of_not_gt hjneg).trans (hmax j hju)) M (by
      simpa only [u,packet_active_support] using hM)

/-- Native logarithmic-height energy integrability bounds every finite energy window. -/
theorem energy_window_bound_of_integrable (s : Finset ι) (c a : ι → ℂ)
    (h : IntegrableOn (fun t => ‖packet s c a t‖^2) (Ioi 0)) :
    ∀ T : ℝ, 0 ≤ T → (∫ t in (0:ℝ)..T, ‖packet s c a t‖^2) ≤
      ∫ t in Ioi (0:ℝ), ‖packet s c a t‖^2 := by
  intro T hT
  rw [intervalIntegral.integral_of_le hT]
  exact setIntegral_mono_set h (Filter.Eventually.of_forall (fun _ => sq_nonneg _))
    (Filter.Eventually.of_forall (fun _ ht => ht.1))

/-- The exact finite-packet native energy criterion, including oscillatory ties. -/
theorem packet_memLp_iff (s : Finset ι) (c a : ι → ℂ)
    (hinj : Set.InjOn a (s:Set ι)) :
    MemLp (packet s c a) 2 (volume.restrict (Ioi (0:ℝ))) ↔
      ∀ i ∈ s, c i ≠ 0 → (a i).re < 0 := by
  constructor
  · intro h i hi hci
    have hsq := (memLp_two_iff_integrable_sq_norm
      (packet_continuous s c a).aestronglyMeasurable).mp h
    exact active_exponent_negative_of_energy_bound s c a hinj _
      (energy_window_bound_of_integrable s c a hsq) hi hci
  · intro h
    unfold packet
    apply memLp_finsetSum
    intro i hi
    by_cases hci : c i = 0
    · simp only [hci,zero_mul]
      exact MemLp.zero'
    have hneg : 2*(a i).re < 0 := by linarith [h i hi hci]
    have he : (fun t : ℝ => ‖Complex.exp (a i*(t:ℂ))‖^2) =
        (fun t : ℝ => Real.exp ((2*(a i).re)*t)) := by
      funext t
      rw [Complex.norm_exp,← Real.exp_nat_mul]
      congr 1
      simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
      ring
    apply MemLp.const_mul
    rw [memLp_two_iff_integrable_sq_norm (show AEStronglyMeasurable
      (fun t : ℝ => Complex.exp (a i*(t:ℂ))) _ by fun_prop),he]
    exact integrableOn_exp_mul_Ioi hneg 0

/-- Translation in logarithmic height preserves every mode with its exact nonzero factor. -/
theorem packet_translate (s : Finset ι) (c a : ι → ℂ) (L t : ℝ) :
    packet s c a (L+t) = packet s (fun i => c i*Complex.exp (a i*(L:ℂ))) a t := by
  unfold packet
  apply Finset.sum_congr rfl
  intro i _
  rw [Complex.ofReal_add,mul_add,Complex.exp_add]
  ring

/-- A native Mellin density above the actual cusp cutoff gives the sharp active-exponent condition. -/
theorem active_exponent_negative_of_mellin_integrable (s : Finset ι) (c a : ι → ℂ)
    (hinj : Set.InjOn a (s:Set ι))
    (h : IntegrableOn (fun y => ‖packet s c a (Real.log y)‖^2/y) (Ioi 2))
    {i : ι} (hi : i ∈ s) (hci : c i ≠ 0) : (a i).re < 0 := by
  let d : ι → ℂ := fun j => c j*Complex.exp (a j*(Real.log 2:ℂ))
  let f : ℝ → ℝ := fun t => Real.exp (Real.log 2+t)
  let g : ℝ → ℝ := fun y => ‖packet s c a (Real.log y)‖^2/y
  have hg : ContinuousOn g (Ioi 0) := by
    apply ContinuousOn.div
    · exact (((packet_continuous s c a).comp_continuousOn
        (Real.continuousOn_log.mono (fun _ hy => ne_of_gt hy))).norm.pow 2)
    · fun_prop
    · intro y hy
      exact ne_of_gt hy
  have hf0 : f 0 = 2 := by simp [f,Real.exp_log (by norm_num : (0:ℝ)<2)]
  have hwindow (T : ℝ) :
      (∫ t in (0:ℝ)..T, ‖packet s d a t‖^2) = ∫ y in (2:ℝ)..f T, g y := by
    have he := intervalIntegral.integral_comp_mul_deriv' (a:=0) (b:=T)
      (f:=f) (f':=f) (g:=g)
      (fun t _ => by
        simpa only [f,id_eq,mul_one] using ((hasDerivAt_id t).const_add (Real.log 2)).exp)
      (show ContinuousOn f _ by fun_prop)
      (hg.mono (by rintro y ⟨t,_,rfl⟩; exact Real.exp_pos _))
    rw [hf0] at he
    rw [← he]
    apply intervalIntegral.integral_congr
    intro t _
    dsimp [Function.comp_def,g,f]
    rw [Real.log_exp,packet_translate]
    exact (div_mul_cancel₀ _ (Real.exp_ne_zero _)).symm
  apply active_exponent_negative_of_energy_bound s d a hinj
    (∫ y in Ioi (2:ℝ), g y) ?_ hi (mul_ne_zero hci (Complex.exp_ne_zero _))
  intro T hT
  rw [hwindow,intervalIntegral.integral_of_le (show 2 ≤ f T by
    rw [← hf0]
    exact Real.exp_le_exp.mpr (by linarith))]
  exact setIntegral_mono_set h
    (by filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
        exact div_nonneg (sq_nonneg _) (le_of_lt (lt_trans (by norm_num) hy)))
    (Filter.Eventually.of_forall (fun _ hy => hy.1))

/-- The half-density conversion retains exactly the native Mellin measure. -/
theorem mellinLift_norm_sq (s : Finset ι) (c a : ι → ℂ) {y : ℝ} (hy : 0 < y) :
    ‖(y:ℂ)^(-1/2:ℂ)*packet s c a (Real.log y)‖^2 =
      ‖packet s c a (Real.log y)‖^2/y := by
  rw [norm_mul,mul_pow,Complex.norm_cpow_eq_rpow_re_of_pos hy,
    ← Real.rpow_mul_natCast hy.le]
  norm_num only [Complex.div_ofNat_re,Complex.neg_re,Complex.one_re,Nat.cast_ofNat]
  rw [Real.rpow_neg_one]
  ring

/-- Finite complete Mellin half-densities cannot hide a nonnegative active exponent. -/
theorem active_exponent_negative_of_mellin_memLp (s : Finset ι) (c a : ι → ℂ)
    (hinj : Set.InjOn a (s:Set ι))
    (h : MemLp (fun y : ℝ => (y:ℂ)^(-1/2:ℂ)*packet s c a (Real.log y))
      2 (volume.restrict (Ioi 2))) {i : ι} (hi : i ∈ s) (hci : c i ≠ 0) :
    (a i).re < 0 := by
  have hs := (memLp_two_iff_integrable_sq_norm h.1).mp h
  apply active_exponent_negative_of_mellin_integrable s c a hinj ?_ hi hci
  apply hs.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  exact mellinLift_norm_sq s c a (lt_trans (by norm_num) hy)

end
end GaloisForLFunctions.RHTower.SelbergFiniteMellinPacket
