import GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.LogarithmicallySmoothedLongMoebiusMeans
import GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.TheConstantTermOfTheSquarefreeHarmonicDiagonal
import GaloisForLFunctions.RHTower.SquarefreeLowerDensity
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.Jensen

/-!
# Endpoint scales of the absolute Möbius tail

Relative to squarefree harmonic mass, the coefficient envelope at x is
√x (log 2 / log x)^m. Its logarithm is convex as a function of log x.
The whole tail through N is therefore controlled by the two endpoints
3 and N. A positive density of squarefree integers also forces the upper
endpoint scale to occur in the total absolute mass.
-/

noncomputable section
open Finset Filter Topology Set
open _root_.RHTower.Sieve
namespace GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean

/-- Effective logarithmic penalty paid at x by m powers of smoothing. -/
def logTailPenalty (m : ℕ) (x : ℝ) := (m:ℝ)*Real.log (Real.log x/Real.log 2)

/-- Endpoint scale measured against squarefree harmonic mass. -/
def logTailScale (m : ℕ) (x : ℝ) := Real.exp (Real.log x/2-logTailPenalty m x)

/-- The envelope is the smoothed critical coefficient per unit harmonic mass. -/
theorem logTailScale_eq_weight (m : ℕ) {x : ℝ} (hx : 1 < x) :
    logTailScale m x = x*(x^(-(1/2:ℝ))*(Real.log 2/Real.log x)^m) := by
  have hl2 := Real.log_pos (by norm_num : (1:ℝ)<2)
  have hx0 := zero_lt_one.trans hx
  have hratio := div_pos (Real.log_pos hx) hl2
  have he : Real.exp (Real.log x/2) = x*x^(-(1/2:ℝ)) := by
    calc _ = Real.exp (Real.log x + Real.log x*(-(1/2:ℝ))) := by congr 1; ring
      _ = _ := by rw [Real.exp_add,Real.exp_log hx0,Real.rpow_def_of_pos hx0]
  rw [logTailScale,logTailPenalty,Real.exp_sub,Real.exp_nat_mul,Real.exp_log hratio,he,
    div_eq_mul_inv,←inv_pow,inv_div]
  ring

/-- The squared envelope is the weighted error term in the Dirichlet
mean-value theorem, relative to squarefree harmonic mass. -/
theorem logTailScale_sq (m : ℕ) {x : ℝ} (hx : 1 < x) :
    (logTailScale m x)^2=x*(Real.log 2/Real.log x)^(2*m) := by
  have hx0 := zero_lt_one.trans hx
  have hr := div_pos (Real.log_pos hx) (Real.log_pos (by norm_num : (1:ℝ)<2))
  rw [logTailScale,logTailPenalty,←Real.exp_nat_mul]
  have hex : (2:ℝ)*(Real.log x/2-m*Real.log (Real.log x/Real.log 2)) =
      Real.log x-(2*m:ℕ)*Real.log (Real.log x/Real.log 2) := by push_cast; ring
  rw [Nat.cast_ofNat,hex,Real.exp_sub,Real.exp_log hx0,Real.exp_nat_mul,Real.exp_log hr,div_eq_mul_inv,←inv_pow,inv_div]

/-- The coefficient envelope has no strict interior maximum in logarithmic frequency. -/
theorem logTailScale_le_endpoints (m : ℕ) {x a b : ℝ} (ha : 1 < a) (hax : a ≤ x) (hxb : x ≤ b) :
    logTailScale m x ≤ max (logTailScale m a) (logTailScale m b) := by
  let f (z : ℝ) := (1/2:ℝ)*z-(m:ℝ)*Real.log z
  have hcv : ConvexOn ℝ (Set.Ioi 0) f :=
    ((convexOn_id (convex_Ioi (0:ℝ))).smul (show (0:ℝ) ≤ 1/2 by norm_num)).sub
      (strictConcaveOn_log_Ioi.concaveOn.smul (Nat.cast_nonneg m : 0 ≤ (m:ℝ)))
  have haa := Real.log_pos ha
  have hx := zero_lt_one.trans_le (ha.le.trans hax)
  have hbb := Real.log_pos (ha.trans_le (hax.trans hxb))
  have hseg := Icc_subset_segment (𝕜:=ℝ) (Set.mem_Icc.mpr
    ⟨Real.log_le_log (zero_lt_one.trans ha) hax,Real.log_le_log hx hxb⟩)
  have H := hcv.le_max_of_mem_segment haa hbb hseg
  let c := (m:ℝ)*Real.log (Real.log 2)
  have hid (t : ℝ) (ht : 1 < t) : logTailScale m t = Real.exp (f (Real.log t)+c) := by
    rw [logTailScale,logTailPenalty,Real.log_div (Real.log_pos ht).ne' (Real.log_pos (by norm_num : (1:ℝ)<2)).ne']
    congr 1; dsimp only [f,c]; ring
  rw [hid x (ha.trans_le hax),hid a ha,hid b (ha.trans_le (hax.trans hxb))]
  rcases le_total (f (Real.log a)) (f (Real.log b)) with hab|hba
  · rw [max_eq_right hab] at H
    exact (Real.exp_le_exp.mpr (add_le_add_left H _)).trans (le_max_right _ _)
  · rw [max_eq_left hba] at H
    exact (Real.exp_le_exp.mpr (add_le_add_left H _)).trans (le_max_left _ _)

private def sf (n : ℕ) : ℝ := ((ArithmeticFunction.moebius n:ℤ):ℝ)^2

private theorem sf_three (N : ℕ) (hN : 16 ≤ N) :
    (N:ℝ)/8 ≤ ∑ n ∈ Finset.Icc 3 N, sf n := by
  classical
  have hfull : (N:ℝ)/4 ≤ ∑ n ∈ Finset.Icc 1 N, sf n := by
    have hi (n : ℕ) : sf n = if Squarefree n then 1 else 0 := by
      rw [sf,←Int.cast_pow,ArithmeticFunction.moebius_sq]
      split <;> norm_num
    simp_rw [hi]
    rw [←sum_filter]
    simpa using _root_.RHTower.quarter_le_card_squarefree N
  have hi : Finset.Icc 1 N \ Finset.Icc 1 2 = Finset.Icc 3 N := by
    apply Finset.ext
    intro n
    simp only [Finset.mem_sdiff,Finset.mem_Icc]
    omega
  have hs : Finset.Icc 1 2 ⊆ Finset.Icc 1 N := fun n hn => Finset.mem_Icc.mpr
    ⟨(Finset.mem_Icc.mp hn).1,(Finset.mem_Icc.mp hn).2.trans (by omega)⟩
  rw [←hi,sum_sdiff_eq_sub hs]
  have htwo : (∑ n ∈ Finset.Icc 1 2, sf n) ≤ 2 := by
    have hh (n : ℕ) : sf n ≤ 1 := by
      rw [sf,←Int.cast_pow,ArithmeticFunction.moebius_sq]; split <;> norm_num
    simpa using (sum_le_sum (s:=Finset.Icc 1 2) (fun n _ => hh n))
  linarith only [hfull,htwo,(show (16:ℝ) ≤ N by exact_mod_cast hN)]

/-- Two-sided bounds for the absolute mass that can survive smoothing.
The factor H(N) is the actual squarefree harmonic diagonal. -/
theorem logDamped_tail_mass_endpoints (m : ℕ) {N : ℕ} (hN : 16 ≤ N) :
    logTailScale m N/8 ≤ logDampedTailMass m N ∧
    logDampedTailMass m N ≤ harmonicMoebiusDiagonal N * max (logTailScale m 3) (logTailScale m N) := by
  have hN1 : (1:ℝ)<N := by exact_mod_cast (show 1 < N by omega)
  let t (x : ℝ) := x^(-(1/2:ℝ))*(Real.log 2/Real.log x)^m
  have hL := Real.log_pos (by norm_num : (1:ℝ)<2)
  have ht {x : ℝ} (hx : 1 < x) : 0 ≤ t x := mul_nonneg (Real.rpow_nonneg (zero_lt_one.trans hx).le _)
    (pow_nonneg (div_nonneg hL.le (Real.log_pos hx).le) _)
  have hmass : logDampedTailMass m N = ∑ n ∈ Finset.Icc 3 N, sf n*t n := by
    rw [logDamped_tail_mass_formula]
    exact sum_congr rfl fun _ _ => by dsimp [sf,t]; ring
  have hmono {x y : ℝ} (hx : 1 < x) (hxy : x ≤ y) : t y ≤ t x := by
    have hly := Real.log_pos (hx.trans_le hxy)
    exact mul_le_mul (Real.rpow_le_rpow_of_nonpos (zero_lt_one.trans hx) hxy (by norm_num))
      (pow_le_pow_left₀ (div_nonneg hL.le hly.le)
        (div_le_div_of_nonneg_left hL.le (Real.log_pos hx) (Real.log_le_log (zero_lt_one.trans hx) hxy)) _)
      (pow_nonneg (div_nonneg hL.le hly.le) _) (Real.rpow_nonneg (zero_lt_one.trans hx).le _)
  rw [hmass]
  constructor
  · calc logTailScale m N/8 = ((N:ℝ)/8)*t N := by rw [logTailScale_eq_weight m hN1]; dsimp only [t]; ring
      _ ≤ (∑ n ∈ Finset.Icc 3 N, sf n)*t N := mul_le_mul_of_nonneg_right (sf_three N hN) (ht hN1)
      _ ≤ _ := by
        rw [sum_mul]
        apply sum_le_sum
        intro n hn
        have hl := (Finset.mem_Icc.mp hn).1
        have hx : (1:ℝ)<n := by exact_mod_cast (show 1 < n by omega)
        exact mul_le_mul_of_nonneg_left (hmono hx (Nat.cast_le.mpr (Finset.mem_Icc.mp hn).2)) (sq_nonneg _)
  · let V := max (logTailScale m 3) (logTailScale m N)
    have hV : 0 ≤ V := (Real.exp_pos _).le.trans (le_max_right _ _)
    have hpoint (n : ℕ) (hn : n ∈ Finset.Icc 3 N) : sf n*t n ≤ (sf n/n)*V := by
      have hn3 : (3:ℝ) ≤ n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
      have hx : (1:ℝ)<n := by linarith only [hn3]
      have hN' := (Finset.mem_Icc.mp hn).2
      have h := logTailScale_le_endpoints m (by norm_num : (1:ℝ)<3) hn3 (Nat.cast_le.mpr hN')
      rw [logTailScale_eq_weight m hx] at h
      calc sf n*t n = (sf n/n)*((n:ℝ)*t n) := by field_simp [(zero_lt_one.trans hx).ne']
        _ ≤ _ := mul_le_mul_of_nonneg_left h (div_nonneg (sq_nonneg _) (Nat.cast_nonneg _))
    apply (sum_le_sum hpoint).trans
    rw [←sum_mul,harmonicMoebiusDiagonal,Nat.floor_natCast]
    apply mul_le_mul_of_nonneg_right _ hV
    exact sum_le_sum_of_subset_of_nonneg (fun n hn => Finset.mem_Icc.mpr
      ⟨by have := (Finset.mem_Icc.mp hn).1; omega,(Finset.mem_Icc.mp hn).2⟩)
      (fun n _ _ => div_nonneg (sq_nonneg _) (Nat.cast_nonneg _))

/-- Both endpoint scales are actually present in the mass. Mode three is
squarefree and survives at every cutoff; the other endpoint is forced by
squarefree density. -/
theorem both_endpoint_scales_le_tail (m : ℕ) {N : ℕ} (hN : 16 ≤ N) :
    max (logTailScale m 3) (logTailScale m N) ≤ 8*logDampedTailMass m N := by
  have htop := (logDamped_tail_mass_endpoints m hN).1
  have h3 : 3 ∈ Finset.Icc 3 N := Finset.mem_Icc.mpr ⟨le_rfl,by omega⟩
  let a (n : ℕ) : ℝ := ((ArithmeticFunction.moebius n:ℤ):ℝ)^2*(n:ℝ)^(-(1/2:ℝ))*
    (Real.log 2/Real.log n)^m
  have h (n : ℕ) (hn : n ∈ Finset.Icc 3 N) : 0 ≤ a n := by
    have hn1 : (1:ℝ) ≤ n := Nat.one_le_cast.mpr (by have := (Finset.mem_Icc.mp hn).1; omega)
    exact mul_nonneg (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
      (pow_nonneg (div_nonneg (Real.log_nonneg (by norm_num)) (Real.log_nonneg hn1)) _)
  have hfirst := single_le_sum h h3
  have he : logTailScale m 3=3*a 3 := by
    rw [logTailScale_eq_weight m (x:=3) (by norm_num)]
    simp only [a,Nat.cast_ofNat,ArithmeticFunction.moebius_apply_prime Nat.prime_three]
    norm_num
  rw [logDamped_tail_mass_formula] at htop ⊢
  change logTailScale m N/8 ≤ ∑ n ∈ Finset.Icc 3 N, a n at htop
  change max _ _ ≤ 8*∑ n ∈ Finset.Icc 3 N, a n
  rw [he]
  exact max_le (by linarith only [hfirst,h 3 h3]) (by linarith only [htop])

/-- Uniform logarithmic accuracy for all orders, including orders that
change with N. The logarithmic correction involves only squarefree harmonic
mass and never depends on m. -/
theorem log_tail_mass_window (m : ℕ) {N : ℕ} (hN : 16 ≤ N) :
    let P := max (Real.log 3/2-logTailPenalty m 3) (Real.log N/2-logTailPenalty m N)
    P-Real.log 8 ≤ Real.log (logDampedTailMass m N) ∧
    Real.log (logDampedTailMass m N) ≤ P+Real.log (harmonicMoebiusDiagonal N) := by
  intro P
  let V := max (logTailScale m 3) (logTailScale m N)
  have hV : 0 < V := (Real.exp_pos _).trans_le (le_max_left _ _)
  have hL := both_endpoint_scales_le_tail m hN
  have hU := (logDamped_tail_mass_endpoints m hN).2
  have hmass : 0 < logDampedTailMass m N := by
    have ht := hV.trans_le hL
    linarith only [ht]
  have hd : 0 < harmonicMoebiusDiagonal N := pos_of_mul_pos_left (hmass.trans_le hU) hV.le
  have hlog : Real.log V=P := by
    dsimp only [V,logTailScale,P]
    rcases le_total (Real.log 3/2-logTailPenalty m 3) (Real.log N/2-logTailPenalty m N) with h|h
    · rw [max_eq_right (Real.exp_le_exp.mpr h),Real.log_exp,max_eq_right h]
    · rw [max_eq_left (Real.exp_le_exp.mpr h),Real.log_exp,max_eq_left h]
  have hl := Real.log_le_log hV hL
  have hu := Real.log_le_log hmass hU
  change Real.log V ≤ Real.log (8*logDampedTailMass m N) at hl
  change _ ≤ Real.log (harmonicMoebiusDiagonal N*V) at hu
  rw [hlog,Real.log_mul (by norm_num) hmass.ne'] at hl
  rw [Real.log_mul hd.ne' hV.ne',hlog] at hu
  constructor <;> linarith only [hl,hu]

private theorem eventually_log_sq_le_linear {a : ℝ} (ha : 0 < a) :
    ∀ᶠ y : ℝ in atTop, (Real.log y)^2 ≤ a*y := by
  have h := (isLittleO_log_rpow_atTop (show (0:ℝ)<1/2 by norm_num)).bound (Real.sqrt_pos.mpr ha)
  filter_upwards [h,eventually_ge_atTop (1:ℝ)] with y hy hy1
  have hy0 := zero_le_one.trans hy1
  rw [Real.norm_eq_abs,abs_of_nonneg (Real.log_nonneg hy1),Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg hy0 _),←Real.sqrt_eq_rpow] at hy
  have H := pow_le_pow_left₀ (Real.log_nonneg hy1) hy 2
  simpa only [mul_pow,Real.sq_sqrt ha.le,Real.sq_sqrt hy0] using H

private theorem exp_le_inverse_sq {x z : ℝ} (hx : 0 < x) (hz : z ≤ -(2*Real.log x)) :
    Real.exp z ≤ (x^2)⁻¹ := by
  have he : Real.log (x^2)=2*Real.log x := by rw [Real.log_pow]; norm_num
  rw [←he] at hz
  simpa only [Real.exp_neg,Real.exp_log (sq_pos_of_pos hx)] using Real.exp_le_exp.mpr hz

/-- Any fixed positive fraction of the logarithmic cutoff penalty suppresses
the first nonstationary mode faster than an inverse power of log N. -/
theorem cutoff_penalty_at_three {α : ℝ} (ha : 0 < α) :
    ∀ᶠ N : ℕ in atTop, ∀ m : ℕ, α*Real.log N ≤ logTailPenalty m N →
      2*Real.log (Real.log N) ≤ logTailPenalty m 3 := by
  let d := Real.log (Real.log 3/Real.log 2)
  have hd : 0 < d := Real.log_pos ((one_lt_div (Real.log_pos (by norm_num : (1:ℝ)<2))).mpr
    (Real.log_lt_log (by norm_num) (by norm_num)))
  let A := 1+|Real.log (Real.log 2)|
  have hA : 0 < A := by dsimp only [A]; positivity
  have hY := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  have hlow := hY.eventually (eventually_log_sq_le_linear
    (a:=α*d/(2*A)) (div_pos (mul_pos ha hd) (by positivity)))
  filter_upwards [hlow,(Real.tendsto_log_atTop.comp hY).eventually_ge_atTop 1,hY.eventually_ge_atTop 1]
    with N hsq hlog hy
  intro m hpen
  let y := Real.log N
  have hypos : 0 < y := zero_lt_one.trans_le hy
  change 1 ≤ Real.log y at hlog
  have hlog0 : 0 < Real.log y := zero_lt_one.trans_le hlog
  change α*y ≤ (m:ℝ)*Real.log (y/Real.log 2) at hpen
  have hden : Real.log (y/Real.log 2) ≤ A*Real.log y := by
    rw [Real.log_div hypos.ne' (Real.log_pos (by norm_num : (1:ℝ)<2)).ne']
    dsimp only [A]
    linarith only [neg_le_abs (Real.log (Real.log 2)),
      le_mul_of_one_le_right (abs_nonneg (Real.log (Real.log 2))) hlog]
  have hsq₁ : 2*A*(Real.log y)^2 ≤ α*y*d := by
    have H := mul_le_mul_of_nonneg_right hsq (by positivity : 0 ≤ 2*A)
    change (Real.log y)^2*(2*A) ≤ α*d/(2*A)*y*(2*A) at H
    have he : α*d/(2*A)*y*(2*A) = α*y*d := by field_simp
    rw [he] at H
    linarith only [H]
  have hp := mul_le_mul_of_nonneg_right
    (hpen.trans (mul_le_mul_of_nonneg_left hden (Nat.cast_nonneg _))) hd.le
  have hpay : 2*Real.log y ≤ (m:ℝ)*d := by
    apply le_of_mul_le_mul_right (a:=A*Real.log y) _ (mul_pos hA hlog0)
    linarith only [hsq₁,hp]
  exact hpay

/-- A uniform upper bound on the squarefree harmonic mass on the
logarithmic scale. -/
theorem squarefree_harmonic_le_log {N : ℕ} (hN1 : (1:ℝ) ≤ N) (hy : 1 ≤ Real.log N) :
    harmonicMoebiusDiagonal N ≤ (squarefreeDensity+(|squarefreeHarmonicConstant|+12))*Real.log N := by
  have hh := (abs_le.mp (squarefree_harmonic_finite_part hN1)).2
  have hp := Real.rpow_le_one_of_one_le_of_nonpos hN1 (by norm_num : -(1/2:ℝ) ≤ 0)
  have hk := le_mul_of_one_le_right (show 0 ≤ |squarefreeHarmonicConstant|+12 by positivity) hy
  linarith only [hh,hp,hk,le_abs_self squarefreeHarmonicConstant]

/-- Above the half-power penalty the total absolute mass beyond the first
two modes vanishes. The order can vary arbitrarily with the cutoff. -/
theorem tail_mass_vanishes_above_half (order : ℕ → ℕ) {α : ℝ} (hα : 1/2 < α)
    (horder : ∀ᶠ N : ℕ in atTop, α*Real.log N ≤ logTailPenalty (order N) N) :
    Tendsto (fun N => logDampedTailMass (order N) N) atTop (𝓝 0) := by
  have ha : 0 < α := by linarith only [hα]
  let C := squarefreeDensity + (|squarefreeHarmonicConstant|+12)
  have hdens : 0 < squarefreeDensity := by rw [squarefreeDensity_eq]; positivity
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  let V := Real.exp (Real.log 3/2)+1
  have hV : 0 < V := by dsimp only [V]; positivity
  have hY := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  have hhigh := hY.eventually (eventually_log_sq_le_linear
    (a:=(α-1/2)/2) (div_pos (sub_pos.mpr hα) (by norm_num)))
  have hly := (Real.tendsto_log_atTop.comp hY).eventually_ge_atTop 1
  apply squeeze_zero' _ _ (g:=fun N : ℕ => (C*V)*(Real.log N)⁻¹)
    (by simpa only [mul_zero,Pi.inv_apply,Function.comp_apply] using hY.inv_tendsto_atTop.const_mul (C*V))
  · exact Eventually.of_forall fun N => by unfold logDampedTailMass; positivity
  · filter_upwards [horder,cutoff_penalty_at_three ha,hhigh,hly,hY.eventually_ge_atTop 1,eventually_ge_atTop (16:ℕ)]
      with N hpen hp3 hsq' hlog hy hN
    let y := Real.log N
    have hypos : 0 < y := zero_lt_one.trans_le hy
    change 1 ≤ Real.log y at hlog
    have hlog0 : 0 < Real.log y := zero_lt_one.trans_le hlog
    have hpay := hp3 (order N) hpen
    change α*y ≤ (order N:ℝ)*Real.log (y/Real.log 2) at hpen
    have hlarge : 2*Real.log y ≤ (α-1/2)*y := by
      change (Real.log y)^2 ≤ (α-1/2)/2*y at hsq'
      nlinarith only [hsq',mul_nonneg hlog0.le (sub_nonneg.mpr hlog)]
    have h3 : logTailScale (order N) 3 ≤ V/(y^2) := by
      rw [logTailScale,sub_eq_add_neg,Real.exp_add]
      have hd3 : Real.exp (-logTailPenalty (order N) 3) ≤ (y^2)⁻¹ :=
        exp_le_inverse_sq hypos (neg_le_neg hpay)
      rw [div_eq_mul_inv V (y^2)]
      exact mul_le_mul (le_add_of_nonneg_right zero_le_one) hd3 (Real.exp_pos _).le hV.le
    have hNN : logTailScale (order N) N ≤ V/(y^2) := by
      have he := exp_le_inverse_sq hypos (z:=y/2-logTailPenalty (order N) N)
        (by change y/2-(order N:ℝ)*Real.log (y/Real.log 2) ≤ _; linarith only [hlarge,hpen])
      rw [div_eq_mul_inv V (y^2)]
      exact he.trans (le_mul_of_one_le_left (inv_nonneg.mpr (sq_nonneg _)) (le_add_of_nonneg_left (Real.exp_pos _).le))
    have hN1 : (1:ℝ) ≤ N := Nat.one_le_cast.mpr (by omega)
    have hD : harmonicMoebiusDiagonal N ≤ C*y := squarefree_harmonic_le_log hN1 hy
    refine (logDamped_tail_mass_endpoints (order N) hN).2.trans ((mul_le_mul hD
      (max_le h3 hNN) (le_trans (Real.exp_pos _).le (le_max_left _ _)) (mul_nonneg hC hypos.le)).trans_eq ?_)
    change C*y*(V/y^2)=(C*V)*y⁻¹
    field_simp

/-- Below the half-power penalty the absolute coefficient mass diverges. -/
theorem tail_mass_diverges_below_half (order : ℕ → ℕ) {α : ℝ} (hα : α < 1/2)
    (horder : ∀ᶠ N : ℕ in atTop, logTailPenalty (order N) N ≤ α*Real.log N) :
    Tendsto (fun N => logDampedTailMass (order N) N) atTop atTop := by
  have hY := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  have hE := Real.tendsto_exp_atTop.comp (hY.const_mul_atTop (sub_pos.mpr hα))
  apply tendsto_atTop_mono' atTop (f₁:=fun N : ℕ => Real.exp ((1/2-α)*Real.log N)/8) _
    (by simpa only [Function.comp_apply] using hE.atTop_div_const (by norm_num : (0:ℝ)<8))
  filter_upwards [horder,eventually_ge_atTop (16:ℕ)] with N hpen hN
  have hh : (1/2-α)*Real.log N ≤ Real.log N/2-logTailPenalty (order N) N := by linarith only [hpen]
  exact (div_le_div_of_nonneg_right (Real.exp_le_exp.mpr hh) (by norm_num : (0:ℝ) ≤ 8)).trans
    (logDamped_tail_mass_endpoints _ hN).1

/-- Integer order selected at the absolute-mass transition scale. -/
def cutoffLogarithmicOrder (α : ℝ) (N : ℕ) : ℕ :=
  ⌈α*Real.log N/Real.log (Real.log N/Real.log 2)⌉₊

theorem cutoffLogarithmicOrder_penalty (α : ℝ) {N : ℕ} (hN : 3 ≤ N) :
    α*Real.log N ≤ logTailPenalty (cutoffLogarithmicOrder α N) N := by
  have h2 : (2:ℝ)<N := by exact_mod_cast (show 2 < N by omega)
  have hL := Real.log_pos ((one_lt_div (Real.log_pos (by norm_num : (1:ℝ)<2))).mpr
    (Real.log_lt_log (by norm_num) h2))
  exact (div_le_iff₀ hL).mp (Nat.le_ceil _)

/-- Rounding the order up adds less than one logarithmic penalty unit. -/
theorem cutoff_penalty_rounding {α : ℝ} (hα : 0 ≤ α) {N : ℕ} (hN : 3 ≤ N) :
    let L := Real.log (Real.log N/Real.log 2)
    0 ≤ logTailPenalty (cutoffLogarithmicOrder α N) N-α*Real.log N ∧
      logTailPenalty (cutoffLogarithmicOrder α N) N-α*Real.log N < L := by
  intro L
  have h2 : (2:ℝ)<N := by exact_mod_cast (show 2 < N by omega)
  have hL : 0 < L := Real.log_pos ((one_lt_div (Real.log_pos (by norm_num : (1:ℝ)<2))).mpr
    (Real.log_lt_log (by norm_num) h2))
  have hlog : 0 ≤ Real.log N := Real.log_nonneg (by linarith only [h2])
  have hh := Nat.ceil_lt_add_one (div_nonneg (mul_nonneg hα hlog) hL.le)
  refine ⟨sub_nonneg.mpr (cutoffLogarithmicOrder_penalty α hN),?_⟩
  have hmul := mul_lt_mul_of_pos_right hh hL
  rw [add_mul,div_mul_cancel₀ _ hL.ne',one_mul] at hmul
  change (⌈α*Real.log N/L⌉₊:ℝ)*L-α*Real.log N < L
  linarith only [hmul]

/-- Integer orders realize every nonnegative penalty fraction asymptotically. -/
theorem cutoff_penalty_fraction {α : ℝ} (hα : 0 ≤ α) :
    Tendsto (fun N : ℕ => logTailPenalty (cutoffLogarithmicOrder α N) N/Real.log N) atTop (𝓝 α) := by
  have hY := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  have hlog := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hY
  have hc := hY.inv_tendsto_atTop.const_mul (Real.log (Real.log 2))
  have hzero : Tendsto (fun N : ℕ => Real.log (Real.log N/Real.log 2)/Real.log N) atTop (𝓝 0) := by
    have hh : Tendsto (fun N : ℕ => Real.log (Real.log N)/Real.log N-
        Real.log (Real.log 2)*(Real.log N)⁻¹) atTop (𝓝 0) := by
      simpa only [Function.comp_apply,Pi.inv_apply,id_eq,mul_zero,sub_zero] using hlog.sub hc
    apply hh.congr'
    filter_upwards [hY.eventually_gt_atTop 0] with N hN
    change 0 < Real.log (N:ℝ) at hN
    rw [Real.log_div hN.ne' (Real.log_pos (by norm_num : (1:ℝ)<2)).ne',sub_div,div_eq_mul_inv (Real.log (Real.log 2))]
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) _ hzero
  filter_upwards [eventually_ge_atTop (3:ℕ),hY.eventually_gt_atTop 0] with N hN hL
  change 0 < Real.log (N:ℝ) at hL
  obtain ⟨hn,hb⟩ := cutoff_penalty_rounding hα hN
  have he : logTailPenalty (cutoffLogarithmicOrder α N) N/Real.log N-α =
      (logTailPenalty (cutoffLogarithmicOrder α N) N-α*Real.log N)/Real.log N := by
    rw [sub_div,mul_div_cancel_right₀ _ hL.ne']
  rw [Real.norm_eq_abs,he]
  rw [abs_of_nonneg (div_nonneg hn hL.le)]
  exact div_le_div_of_nonneg_right hb.le hL.le

/-- Every strictly subcritical explicit order has divergent absolute tail. -/
theorem subcritical_cutoff_tail_diverges {α : ℝ} (hα : 0 ≤ α) (hhalf : α < 1/2) :
    Tendsto (fun N => logDampedTailMass (cutoffLogarithmicOrder α N) N) atTop atTop := by
  let β := (α+1/2)/2
  have hab : α < β := by dsimp only [β]; linarith only [hhalf]
  apply tail_mass_diverges_below_half _ (α:=β) (by dsimp only [β]; linarith only [hhalf])
  filter_upwards [(cutoff_penalty_fraction hα).eventually_le_const hab,eventually_ge_atTop (2:ℕ)] with N h hN
  exact (div_le_iff₀ (Real.log_pos (by exact_mod_cast (show 1 < N by omega) : (1:ℝ)<N))).mp h

/-- Above coefficient one half, log N / log(log N / log 2) integrations
already force a linear-in-height moment at every fixed polynomial length. -/
theorem supercritical_order_forces_linear_moebius_mean {α θ : ℝ} (hα : 1/2 < α) (hθ : 0 < θ) :
    ∀ᶠ T : ℝ in atTop, logDampedMoment (cutoffLogarithmicOrder α ⌊T^θ⌋₊) θ T ≤ 9*(T-1) := by
  have hpen : ∀ᶠ N : ℕ in atTop, α*Real.log N ≤ logTailPenalty (cutoffLogarithmicOrder α N) N := by
    exact (eventually_ge_atTop (3:ℕ)).mono fun _ => cutoffLogarithmicOrder_penalty α
  have hf : Tendsto (fun T : ℝ => ⌊T^θ⌋₊) atTop atTop := tendsto_nat_floor_atTop.comp (tendsto_rpow_atTop hθ)
  have htail := (tail_mass_vanishes_above_half (cutoffLogarithmicOrder α) hα hpen).comp hf
  filter_upwards [htail.eventually_le_const (show (0:ℝ)<1 by norm_num),hf.eventually_ge_atTop 2,
    eventually_ge_atTop (1:ℝ)] with T ht hN hT
  simpa only [show (2+(1:ℝ))^2=9 by norm_num] using logDampedMoment_le_of_tail_mass
    (cutoffLogarithmicOrder α ⌊T^θ⌋₊) hT hN ht

#print axioms supercritical_order_forces_linear_moebius_mean
#print axioms tail_mass_vanishes_above_half
#print axioms tail_mass_diverges_below_half
#print axioms cutoff_penalty_fraction
#print axioms subcritical_cutoff_tail_diverges
#print axioms log_tail_mass_window
#print axioms logDamped_tail_mass_endpoints

end GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean
