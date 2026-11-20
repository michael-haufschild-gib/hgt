import GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.DerivativeEnergyFromASingleLogarithmicWindow
import GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.LogarithmicallySmoothedLongMoebiusMeans

/-!
# Growing logarithmic smoothing orders at one Möbius cutoff

For a Dirichlet polynomial of length T^θ the bandwidth and the logarithm
of the coefficient mass are both at most θ log T. Squared-node samples
therefore remove one logarithmic integration at a cost polynomial in
log T. On the original window the cumulative cost stays polynomial in T
even for a number of integrations proportional to log T / log log T.
-/

noncomputable section
open Finset Filter Topology Complex MeasureTheory
open GaloisForLFunctions.MultiscaleMollifiedZetaField GaloisForLFunctions.SquareRootThreshold
namespace GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean

/-- Removing one logarithmic integration from the actual polynomial costs
at most six powers of 1+log T, uniformly in the order being undone. -/
theorem one_logarithmic_order_energy {θ : ℝ} (hθ : 0 < θ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ T : ℝ, 3 ≤ T → ∀ m : ℕ,
      T+logDampedMoment m θ T ≤ K*(1+Real.log T)^6*(T+logDampedMoment (m+1) θ T) := by
  let b := 4*θ/Real.log 2
  let d := b+2
  let C := 16*(2*d+1)^2*d^4
  let D := 2/(Real.log 2)^2
  have hL2 := Real.log_pos (by norm_num : (1:ℝ)<2)
  have hb : 0 ≤ b := div_nonneg (by positivity) hL2.le
  have hd : 0 ≤ d := by dsimp only [d]; positivity
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  refine ⟨3+D*C,by positivity,fun T hT m => ?_⟩
  have hT1 : 1 ≤ T := by linarith only [hT]
  have hTpos := zero_lt_one.trans_le hT1
  have hlog := Real.log_nonneg hT1
  let L := 1+Real.log T
  have hL : 1 ≤ L := by dsimp only [L]; linarith only [hlog]
  let N := ⌊T^θ⌋₊
  let B := θ*Real.log T
  let q := ⌈b*Real.log T⌉₊+1
  have hq : 0 < q := Nat.succ_pos _
  have hNR : (N:ℝ) ≤ Real.exp B := by
    rw [show B=Real.log T*θ by dsimp only [B]; ring,←Real.rpow_def_of_pos hTpos]
    exact Nat.floor_le (Real.rpow_nonneg hTpos.le _)
  obtain ⟨a,he,hmass⟩ := exists_logDampedMoebius_packet (m+1) N
  have hf (n : ℕ) (hn : n ∈ Icc 1 N) : |-Real.log n| ≤ B := by
    have hn1 : (1:ℝ) ≤ n := Nat.one_le_cast.mpr (mem_Icc.mp hn).1
    rw [abs_neg,abs_of_nonneg (Real.log_nonneg hn1),←Real.log_exp B]
    exact Real.log_le_log (zero_lt_one.trans_le hn1) ((Nat.cast_le.mpr (mem_Icc.mp hn).2).trans hNR)
  have horder : 4*B ≤ (q+1:ℕ)*Real.log 2 := by
    have H := Nat.le_ceil (b*Real.log T)
    have H' := mul_le_mul_of_nonneg_right H hL2.le
    have hc : b*Real.log T*Real.log 2=4*B := by dsimp only [b,B]; field_simp
    rw [hc] at H'
    dsimp only [q]; push_cast
    linarith only [H',hL2]
  have hqL : (q:ℝ) ≤ d*L := by
    have H := Nat.ceil_lt_add_one (mul_nonneg hb hlog)
    dsimp only [q,d,L]; push_cast
    linarith only [H,hb,hlog]
  have hcoef : 16*(2*(q:ℝ)+1)^2*(q:ℝ)^4 ≤ C*L^6 := by
    have h1 : 2*(q:ℝ)+1 ≤ (2*d+1)*L := by linarith only [hqL,hL]
    calc _ ≤ 16*((2*d+1)*L)^2*(d*L)^4 := by
               exact mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) h1 2) (by norm_num))
                 (pow_le_pow_left₀ (Nat.cast_nonneg _) hqL 4) (by positivity) (by positivity)
      _ = _ := by dsimp only [C]; ring
  have hg := derivative_energy_of_logarithmic_size a (fun n => -Real.log n) (Icc 1 N) hq
    (A:=1) (D:=T) (by linarith only [hT]) hf (hmass.trans hNR) horder
  rw [←he] at hg
  let I₁ := logDampedMoment (m+1) θ T
  have hI : 0 ≤ I₁ := intervalIntegral.integral_nonneg hT1 fun _ _ => sq_nonneg _
  have hJ : 0 ≤ T+I₁ := add_nonneg hTpos.le hI
  have hrate : (∫ t in (1:ℝ)..T, ‖deriv (logDampedMoebius (m+1) N) t‖^2) ≤ C*L^6*(T+I₁) := by
    refine hg.trans (mul_le_mul hcoef ?_ ?_ (mul_nonneg hC (pow_nonneg (zero_le_one.trans hL) _)))
    · change I₁+(T-1) ≤ T+I₁; linarith
    · change 0 ≤ I₁+(T-1); linarith only [hI,hT]
  have hN : 1 ≤ N := (Nat.one_le_floor_iff (T^θ)).mpr (Real.one_le_rpow hT1 hθ.le)
  have hstep := (logDamped_energy_le_derivative m hN hT1).trans (add_le_add le_rfl
    (mul_le_mul_of_nonneg_left hrate hD))
  change logDampedMoment m θ T ≤ 2*(T-1)+D*(C*L^6*(T+I₁)) at hstep
  have htop : T ≤ L^6*(T+I₁) := (le_add_of_nonneg_right hI).trans
    (le_mul_of_one_le_left hJ (one_le_pow₀ hL))
  change T+logDampedMoment m θ T ≤ (3+D*C)*L^6*(T+I₁)
  linarith only [hstep,htop]

/-- A single cutoff and its original interval suffice even when the order
varies with the observation horizon and grows like log T / log log T. -/
theorem growing_log_order_recovery {θ c : ℝ} (hθ : 0 < θ) :
    ∀ᶠ T : ℝ in atTop, ∀ m : ℕ, (m:ℝ)*Real.log (1+Real.log T) ≤ c*Real.log T →
      logDampedMoment 0 θ T ≤ T^(7*c)*(T+logDampedMoment m θ T) := by
  obtain ⟨K,hK,H⟩ := one_logarithmic_order_energy hθ
  filter_upwards [eventually_ge_atTop (3:ℝ),Real.tendsto_log_atTop.eventually_ge_atTop K] with T hT hTK
  let L := 1+Real.log T
  have hT1 : 1 ≤ T := by linarith only [hT]
  have hTpos := zero_lt_one.trans_le hT1
  have hL : 1 ≤ L := by dsimp only [L]; linarith only [Real.log_nonneg hT1]
  let J (n : ℕ) := T+logDampedMoment n θ T
  have hJ (n : ℕ) : 0 ≤ J n := add_nonneg hTpos.le (intervalIntegral.integral_nonneg hT1 fun _ _ => sq_nonneg _)
  have hstep (n : ℕ) : J n ≤ L^7*J (n+1) := by
    apply (H T hT n).trans
    apply mul_le_mul_of_nonneg_right _ (hJ _)
    rw [show L^7=L*L^6 by ring]
    exact mul_le_mul_of_nonneg_right (by dsimp only [L]; linarith only [hTK]) (pow_nonneg (zero_le_one.trans hL) _)
  intro m hm
  have hpow : (L^7)^m ≤ T^(7*c) := by
    rw [←Real.log_le_log_iff (pow_pos (pow_pos (zero_lt_one.trans_le hL) _) _) (Real.rpow_pos_of_pos hTpos _),
      Real.log_pow,Real.log_pow,Real.log_rpow hTpos]
    dsimp only [L]; push_cast; linarith only [hm]
  exact (le_add_of_nonneg_left hTpos.le).trans ((iterate_energy_step J (pow_nonneg (zero_le_one.trans hL) _) hstep m).trans
    (mul_le_mul_of_nonneg_right hpow (hJ m)))

/-- A single smoothed cutoff at arbitrarily large polynomial lengths
and unbounded heights, with a common intercept in the growth exponent. -/
def singleCutoffLogOrderBound (order : ℝ → ℝ → ℕ) (β : ℝ) : Prop :=
  ∃ K : ℝ, 0 ≤ K ∧ ∀ θ₀ : ℝ, 0 < θ₀ → ∃ θ : ℝ, θ₀ ≤ θ ∧ ∃ A : ℝ, 0 ≤ A ∧
    ∃ᶠ T : ℝ in atTop, logDampedMoment (order θ T) θ T ≤ A*T^(K+2*β*θ)

private theorem singleCutoffBound_of_width (order : ℝ → ℝ → ℕ) {β : ℝ} (hβ : 0 ≤ β)
    (hwidth : zetaZeroWidth ≤ β) : singleCutoffLogOrderBound order β := by
  obtain ⟨K,hK,H⟩ := (zetaZeroWidth_iff_cofinal_maximal_moebius_slope hβ).mp hwidth
  refine ⟨K,hK,fun θ₀ hθ₀ => ?_⟩
  obtain ⟨θ,hθ,A,hA,hgood⟩ := H θ₀ hθ₀
  refine ⟨θ,hθ,A,hA,(hgood.and_eventually (eventually_ge_atTop (1:ℝ))).mono fun T ⟨hb,hT⟩ => ?_⟩
  obtain ⟨a,he,_⟩ := exists_logDampedMoebius_packet (order θ T) ⌊T^θ⌋₊
  have hcont : Continuous (logDampedMoebius (order θ T) ⌊T^θ⌋₊) := by rw [he]; unfold _root_.HTGeometry.genPoly; fun_prop
  exact (intervalIntegral.integral_mono_on hT ((hcont.norm.pow 2).intervalIntegrable _ _)
    (((continuous_moebiusPrefixMaximum _).pow 2).intervalIntegrable _ _) fun t _ =>
      pow_le_pow_left₀ (norm_nonneg _) (logDampedMoebius_le_prefix_maximum _ _ t) 2).trans hb

/-- A cost c+dθ in the number of integrations increases the inferred
zero width by at most 7d/2. Only arbitrarily large lengths are tested. -/
theorem width_le_of_growing_order_slope (order : ℝ → ℝ → ℕ) {c d β : ℝ}
    (hc : 0 ≤ c) (hd : 0 ≤ d) (hβ : 0 ≤ β)
    (horder : ∀ᶠ θ : ℝ in atTop, ∀ᶠ T : ℝ in atTop,
      (order θ T:ℝ)*Real.log (1+Real.log T) ≤ (c+d*θ)*Real.log T)
    (hobs : singleCutoffLogOrderBound order β) : zetaZeroWidth ≤ β+7*d/2 := by
  obtain ⟨K,hK,H⟩ := hobs
  obtain ⟨a,ha⟩ := eventually_atTop.1 horder
  apply zetaZeroWidth_le_of_cofinal_pure_moebius_slope (show 0 ≤ β+7*d/2 by positivity)
    (show 0 ≤ 7*c+1+K by positivity)
  intro θ₀ hθ₀
  obtain ⟨θ,hθ,A,hA,hgood⟩ := H (max θ₀ a) (hθ₀.trans_le (le_max_left _ _))
  have hθ₁ := (le_max_left θ₀ a).trans hθ
  have hp := hθ₀.trans_le hθ₁
  have ho := ha θ ((le_max_right θ₀ a).trans hθ)
  refine ⟨θ,hθ₁,1+A,by positivity,(hgood.and_eventually
    ((growing_log_order_recovery (c:=c+d*θ) hp).and (ho.and (eventually_ge_atTop (1:ℝ))))).mono ?_⟩
  rintro T ⟨hb,hrec,hm,hT⟩
  simp_rw [edPoly_moebiusMollifierCoeff_eq_moebiusPoly,←logDampedMoebius_zero]
  let V := T^(K+2*β*θ)
  have htpos := zero_lt_one.trans_le hT
  have hV : 1 ≤ V := Real.one_le_rpow hT (by positivity)
  have hmul : T+logDampedMoment (order θ T) θ T ≤ T*V+A*(T*V) := add_le_add
    (le_mul_of_one_le_right htpos.le hV) (hb.trans (mul_le_mul_of_nonneg_left
      (le_mul_of_one_le_left (zero_le_one.trans hV) hT) hA))
  refine (hrec _ hm).trans ((mul_le_mul_of_nonneg_left hmul (Real.rpow_nonneg htpos.le _)).trans_eq ?_)
  rw [show 7*c+1+K+2*(β+7*d/2)*θ=7*(c+d*θ)+(1+(K+2*β*θ)) by ring,
    Real.rpow_add htpos (7*(c+d*θ)) _,Real.rpow_add htpos 1 _,Real.rpow_one]
  dsimp only [V]; ring

/-- The same zero-width criterion survives any length-independent bound
on the order in units of log T / log(1+log T). -/
theorem growing_log_order_iff_zero_width (order : ℝ → ℝ → ℕ) {c β : ℝ} (hc : 0 ≤ c) (hβ : 0 ≤ β)
    (horder : ∀ θ : ℝ, 0 < θ → ∀ᶠ T : ℝ in atTop,
      (order θ T:ℝ)*Real.log (1+Real.log T) ≤ c*Real.log T) :
    singleCutoffLogOrderBound order β ↔ zetaZeroWidth ≤ β := by
  refine ⟨fun h => ?_,singleCutoffBound_of_width order hβ⟩
  have ho : ∀ᶠ θ : ℝ in atTop, ∀ᶠ T : ℝ in atTop,
      (order θ T:ℝ)*Real.log (1+Real.log T) ≤ (c+0*θ)*Real.log T := by
    filter_upwards [eventually_gt_atTop (0:ℝ)] with θ hθ
    simpa only [zero_mul,add_zero] using horder θ hθ
  simpa only [mul_zero,zero_div,add_zero] using width_le_of_growing_order_slope order hc le_rfl hβ ho h

/-- The recoverable order can grow with the length exponent as well.
Any sublinear dependence on θ retains the exact zero width. -/
theorem sublinear_order_iff_zero_width (order : ℝ → ℝ → ℕ) {β : ℝ} (hβ : 0 ≤ β)
    (horder : ∀ d : ℝ, 0 < d → ∀ᶠ θ : ℝ in atTop, ∀ᶠ T : ℝ in atTop,
      (order θ T:ℝ)*Real.log (1+Real.log T) ≤ d*θ*Real.log T) :
    singleCutoffLogOrderBound order β ↔ zetaZeroWidth ≤ β := by
  refine ⟨fun h => ?_,singleCutoffBound_of_width order hβ⟩
  by_contra! hgap
  let d := (zetaZeroWidth-β)/7
  have hd : 0 < d := div_pos (sub_pos.mpr hgap) (by norm_num)
  have ho : ∀ᶠ θ : ℝ in atTop, ∀ᶠ T : ℝ in atTop,
      (order θ T:ℝ)*Real.log (1+Real.log T) ≤ (0+d*θ)*Real.log T := by
    simpa only [zero_add] using horder d hd
  have H := width_le_of_growing_order_slope order (c:=0) le_rfl hd.le hβ ho h
  dsimp only [d] at H
  linarith only [H,hgap]

#print axioms one_logarithmic_order_energy
#print axioms growing_log_order_recovery
#print axioms width_le_of_growing_order_slope
#print axioms sublinear_order_iff_zero_width
#print axioms growing_log_order_iff_zero_width

end GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean
