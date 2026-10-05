import GaloisForLFunctions.RHTower.ChiRamanujanDampedSquareResidues
import GaloisForLFunctions.RHTower.ChiRamanujanDampedSquareTestWindowPerron
import GaloisForLFunctions.RHTower.Sieve.InghamUniformDetectorMellinFullTwoTail

/-!
# Residues, tails and edges of the divisor-square contour for an arbitrary smooth window

For `W` smooth with support in `[a,b] ⊂ (0,∞)`:
* both normalized residues coalesce to `Ψ(ε log X) M_W(1)`, `Ψ(c) = (1-e^{-2c})/(2c)`, with error
  `O(1/log X)` uniformly in `0 < ε ≤ η`, with no lower bound on `ε log X`;
* the original line `Re s = 1+b` decays to every polynomial order in `|t|`, uniformly in damping,
  so both infinite tails are controlled together;
* the left edge and both horizontal edges of the moving rectangle have explicit integrated bounds.
-/

noncomputable section
open Complex Set Filter MeasureTheory
open scoped Topology Interval
open GaloisForLFunctions.HTGeometry.TestFunctionPerron
open GaloisForLFunctions.RHTower
namespace RHTower.BAGTrace

variable {W : ℝ → ℂ} {a b : ℝ}


private theorem test_window_mellin_lipschitz (hW : IsTest W a b) :
    ∃ B > 0, ∀ s : ℂ, ‖s-1‖ ≤ 1 →
      ‖dampedSquareTestMellin W s-dampedSquareTestMellin W 1‖ ≤ B*‖s-1‖ := by
  have hc : Continuous (dslope (dampedSquareTestMellin W) 1) := by
    apply continuous_iff_continuousAt.mpr
    intro s
    exact (analyticAt_dslope_of_analyticAt
      ((differentiable_dampedSquareTestMellin hW).analyticAt 1)
      ((differentiable_dampedSquareTestMellin hW).analyticAt s)).continuousAt
  obtain ⟨B,hB⟩ := (isCompact_closedBall (1 : ℂ) 1).exists_bound_of_continuousOn hc.continuousOn
  refine ⟨|B|+1,by positivity,?_⟩
  intro s hs
  have hb := hB s (show s ∈ Metric.closedBall (1 : ℂ) 1 by simpa [dist_eq_norm] using hs)
  have he := sub_smul_dslope (dampedSquareTestMellin W) 1 s
  rw [smul_eq_mul] at he
  rw [← he,norm_mul,mul_comm]
  exact mul_le_mul_of_nonneg_right (by linarith [le_abs_self B]) (norm_nonneg _)

/-- Both actual rectangle residues, normalized at the physical square-law scale. -/
def dampedSquareTestResiduePacket (W : ℝ → ℂ) (ε X : ℝ) : ℂ :=
  (dampedSquareTestMellinNumerator W ε X 1/(2*ε) +
    dampedSquareTestMellinNumerator W ε X (1-2*ε)/(-2*ε))/((X : ℂ)*Real.log X)

theorem dampedSquareTestResiduePacket_eq {ε X : ℝ} (hε : 0 < ε) (hX : 1 < X) :
    dampedSquareTestResiduePacket W ε X =
      (dampedSquareRegularSource (1+ε) (-ε)*dampedSquareTestMellin W 1 -
        (((X^(-2*ε) : ℝ) : ℂ))*dampedSquareRegularSource (1-ε) (-ε)*
          dampedSquareTestMellin W (1-2*ε))/((2*ε*Real.log X : ℝ) : ℂ) := by
  have hX0 : 0 < X := by linarith
  have hx : (X : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hX0.ne'
  have he : (ε : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hε.ne'
  have hl : (Real.log X : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.log_pos hX).ne'
  have hp : (X : ℂ)^(1-2*(ε : ℂ)) =
      (X : ℂ)*((X^(-2*ε) : ℝ) : ℂ) := by
    rw [show (1 : ℂ)-2*ε = 1+((-2*ε : ℝ) : ℂ) by push_cast; ring,
      Complex.cpow_add _ _ hx,Complex.cpow_one,← Complex.ofReal_cpow hX0.le]
  unfold dampedSquareTestResiduePacket dampedSquareTestMellinNumerator
  rw [Complex.cpow_one,hp,show (1 : ℂ)-2*ε+ε = 1-ε by ring]
  push_cast
  field_simp
  ring

private theorem test_crossover_rpow {ε X : ℝ} (hX : 0 < X) :
    (dampedSquareCrossover (ε*Real.log X) : ℂ)*dampedSquareTestMellin W 1 =
      (1-(((X^(-2*ε) : ℝ) : ℂ)))*dampedSquareTestMellin W 1 /
        ((2*ε*Real.log X : ℝ) : ℂ) := by
  have he : X^(-2*ε) = Real.exp (-2*(ε*Real.log X)) := by
    rw [Real.rpow_def_of_pos hX]
    congr 1
    ring
  rw [he,dampedSquareCrossover]
  push_cast
  ring

private theorem test_residue_numerator_norm_le (a b m n : ℂ) {r : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    ‖a*m-(r : ℂ)*b*n-(1-(r : ℂ))*m‖ ≤
      ‖a-1‖*‖m‖+‖b-1‖*‖n‖+‖n-m‖ := by
  have he : a*m-(r : ℂ)*b*n-(1-(r : ℂ))*m =
      (a-1)*m-(r : ℂ)*((b-1)*n+(n-m)) := by ring
  rw [he]
  calc _ ≤ ‖(a-1)*m‖+‖(r : ℂ)*((b-1)*n+(n-m))‖ := norm_sub_le _ _
    _ ≤ ‖a-1‖*‖m‖+r*(‖b-1‖*‖n‖+‖n-m‖) := by
      rw [norm_mul,norm_mul,Complex.norm_real,Real.norm_of_nonneg hr0]
      gcongr
      exact (norm_add_le _ _).trans_eq (by rw [norm_mul])
    _ ≤ ‖a-1‖*‖m‖+(‖b-1‖*‖n‖+‖n-m‖) := by
      have h := mul_le_mul_of_nonneg_right hr1
        (show 0 ≤ ‖b-1‖*‖n‖+‖n-m‖ by positivity)
      simpa only [one_mul] using add_le_add (le_refl (‖a-1‖*‖m‖)) h
    _ = _ := by ring

/-- Both actual residues coalesce uniformly, without any lower bound on ε log X. -/
theorem exists_dampedSquareTestResiduePacket_uniform_coalescence (hW : IsTest W a b) :
    ∃ η ∈ Ioc (0 : ℝ) (1/128), ∃ C > 0, ∀ {ε X : ℝ},
      0 < ε → ε ≤ η → 1 < X →
      ‖dampedSquareTestResiduePacket W ε X -
        (dampedSquareCrossover (ε*Real.log X) : ℂ)*dampedSquareTestMellin W 1‖ ≤
        C/Real.log X := by
  obtain ⟨η,hη,K,hK,hQ⟩ := exists_dampedSquareRegularSource_quadratic_bound
  obtain ⟨B,hB,hM⟩ := test_window_mellin_lipschitz hW
  let m := dampedSquareTestMellin W 1
  let C := K*‖m‖+K*(‖m‖+2*B)+2*B
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨η,hη,C/2,by positivity,?_⟩
  intro ε X hε hεη hX
  have hε1 : ε ≤ 1 := by linarith [hη.2]
  have hε2 : 2*ε ≤ 1 := by linarith [hη.2]
  have hεsq : ε^2 ≤ ε := by nlinarith
  have hX0 : 0 < X := by linarith
  have hL : 0 < Real.log X := Real.log_pos hX
  have hp : ‖dampedSquareRegularSource (1+(ε : ℂ)) (-ε)-1‖ ≤ K*ε^2 := by
    have h := hQ 0 (1+(ε : ℂ)) (-ε)
      (by simpa [dist_eq_norm,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hε] using hεη)
      (by simpa [Complex.norm_real,Real.norm_eq_abs,abs_of_pos hε] using hεη)
    simpa [Complex.norm_real,Real.norm_eq_abs,abs_of_pos hε] using h
  have hq : ‖dampedSquareRegularSource (1-(ε : ℂ)) (-ε)-1‖ ≤ K*ε^2 := by
    have h := hQ 0 (1-(ε : ℂ)) (-ε)
      (by simpa [dist_eq_norm,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hε] using hεη)
      (by simpa [Complex.norm_real,Real.norm_eq_abs,abs_of_pos hε] using hεη)
    simpa [Complex.norm_real,Real.norm_eq_abs,abs_of_pos hε] using h
  have hd : ‖((1 : ℂ)-2*ε)-1‖ = 2*ε := by
    rw [show ((1 : ℂ)-2*ε)-1 = ((-2*ε : ℝ) : ℂ) by push_cast; ring]
    simp [Complex.norm_real,Real.norm_eq_abs,abs_of_pos hε]
  have hm : ‖dampedSquareTestMellin W (1-2*(ε : ℂ))-m‖ ≤ 2*B*ε := by
    have h := hM (1-2*(ε : ℂ)) (by rwa [hd])
    rw [hd] at h
    simpa only [m,mul_assoc,mul_comm,mul_left_comm] using h
  have hn : ‖dampedSquareTestMellin W (1-2*(ε : ℂ))‖ ≤ ‖m‖+2*B := by
    have h := norm_le_norm_sub_add (dampedSquareTestMellin W (1-2*(ε : ℂ))) m
    nlinarith
  have hr0 : 0 ≤ X^(-2*ε) := Real.rpow_nonneg hX0.le _
  have hr1 : X^(-2*ε) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hX.le (by linarith)
  have hnum := test_residue_numerator_norm_le
    (dampedSquareRegularSource (1+(ε : ℂ)) (-ε))
    (dampedSquareRegularSource (1-(ε : ℂ)) (-ε)) m
    (dampedSquareTestMellin W (1-2*(ε : ℂ))) hr0 hr1
  have hbound :
      ‖dampedSquareRegularSource (1+(ε : ℂ)) (-ε)*m -
        ((X^(-2*ε) : ℝ) : ℂ)*dampedSquareRegularSource (1-(ε : ℂ)) (-ε)*
          dampedSquareTestMellin W (1-2*(ε : ℂ)) -
        (1-(((X^(-2*ε) : ℝ) : ℂ)))*m‖ ≤ C*ε := by
    calc _ ≤ ‖dampedSquareRegularSource (1+(ε : ℂ)) (-ε)-1‖*‖m‖+
        ‖dampedSquareRegularSource (1-(ε : ℂ)) (-ε)-1‖*
          ‖dampedSquareTestMellin W (1-2*(ε : ℂ))‖+
        ‖dampedSquareTestMellin W (1-2*(ε : ℂ))-m‖ := hnum
      _ ≤ K*ε^2*‖m‖+K*ε^2*(‖m‖+2*B)+2*B*ε := by gcongr
      _ = ε^2*(K*‖m‖+K*(‖m‖+2*B))+2*B*ε := by ring
      _ ≤ ε*(K*‖m‖+K*(‖m‖+2*B))+2*B*ε := by gcongr
      _ = C*ε := by dsimp [C]; ring
  rw [dampedSquareTestResiduePacket_eq hε hX,test_crossover_rpow hX0,← sub_div,
    norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (by positivity : 0 < 2*ε*Real.log X)]
  calc _ ≤ C*ε/(2*ε*Real.log X) := div_le_div_of_nonneg_right hbound (by positivity)
    _ = (C/2)/Real.log X := by field_simp

/-- Uniform residue convergence includes every joint path with vanishing damping. -/
theorem exists_dampedSquareTestResiduePacket_tendstoUniformlyOn (hW : IsTest W a b) :
    ∃ η ∈ Ioc (0 : ℝ) (1/128),
      TendstoUniformlyOn
        (fun X ε => dampedSquareTestResiduePacket W ε X -
          (dampedSquareCrossover (ε*Real.log X) : ℂ)*dampedSquareTestMellin W 1)
        (fun _ => 0) atTop (Ioc 0 η) := by
  obtain ⟨η,hη,C,hC,hbound⟩ := exists_dampedSquareTestResiduePacket_uniform_coalescence hW
  refine ⟨η,hη,Metric.tendstoUniformlyOn_iff.mpr ?_⟩
  intro r hr
  have ht : Tendsto (fun X : ℝ => C/Real.log X) atTop (𝓝 0) :=
    Real.tendsto_log_atTop.const_div_atTop C
  filter_upwards [ht.eventually (gt_mem_nhds hr),eventually_gt_atTop (1 : ℝ)] with X hXr hX
  intro ε hε
  simpa only [dist_zero_left] using (hbound hε.1 hε.2 hX).trans_lt hXr



/-- Arbitrary-order decay of the actual original contour line, uniform in damping. -/
theorem exists_dampedSquareTestContour_original_line_decay (hW : IsTest W a b) (j : ℕ) :
    ∃ C > 0, ∀ {ε b X : ℝ}, 0 < ε → ε < 1/16 →
      0 < b → b ≤ 1 → 0 < X → ∀ t : ℝ,
      ‖dampedSquareTestContourIntegrand W ε X ((1+b : ℝ)+t*I)‖ ≤
        C*X^(1+b)/b^3/(1+|t|)^j := by
  obtain ⟨A,hA,hM⟩ := exists_dampedSquareTestMellin_rapidDecay hW j 1
  refine ⟨24*A,by positivity,?_⟩
  intro ε b X hε hε1 hb hb1 hX t
  have hm : ‖dampedSquareTestMellin W ((1+b : ℝ)+t*I)‖ ≤ A/(1+|t|)^j := by
    simpa only [add_re,ofReal_re,mul_re,ofReal_im,I_re,I_im,mul_zero,zero_mul,
      sub_zero,add_zero,add_sub_cancel_left,abs_of_pos hb,add_im,mul_im,zero_add,
      mul_one] using hM ((1+b : ℝ)+t*I) (by simpa [abs_of_pos hb] using hb1)
  have hp : ‖(X : ℂ)^((1+b : ℝ)+t*I)‖ = X^(1+b) := by
    simpa using Complex.norm_cpow_eq_rpow_re_of_pos hX ((1+b : ℝ)+t*I)
  unfold dampedSquareTestContourIntegrand
  rw [← dampedSquareDirichlet_eq_continuation hε.le hε1 (by simp; linarith),
    norm_mul,norm_mul,hp]
  calc _ ≤ (24/b^3)*(A/(1+|t|)^j)*X^(1+b) := by
        gcongr
        exact norm_dampedSquareDirichlet_normalized_le hε hb hb1 t
    _ = _ := by ring

/-- Both infinite original-line tails are retained and controlled together. -/
theorem exists_dampedSquareTestContour_two_tail_bound (hW : IsTest W a b) (j : ℕ) (hj : 2 ≤ j) :
    ∃ C > 0, ∀ {ε b X T : ℝ}, 0 < ε → ε < 1/16 →
      0 < b → b ≤ 1 → 0 < X → 0 < T →
      ‖(∫ t : ℝ,dampedSquareTestContourIntegrand W ε X ((1+b : ℝ)+t*I)) -
        ∫ t in (-T)..T,dampedSquareTestContourIntegrand W ε X ((1+b : ℝ)+t*I)‖ ≤
        C*X^(1+b)/b^3 * (T^(1-(j : ℝ))/((j : ℝ)-1)) := by
  obtain ⟨A,hA,hbound⟩ := exists_dampedSquareTestContour_original_line_decay hW j
  refine ⟨2*A,by positivity,?_⟩
  intro ε b X T hε hε1 hb hb1 hX hT
  have hint := integrable_dampedSquareTestContour_original_line hW hε.le hε1 hX
    (show 1 < 1+b by linarith)
  have hjR : (1 : ℝ) < j := by exact_mod_cast (show 1 < j by omega)
  have hpoint : ∀ t : ℝ, T ≤ |t| →
      ‖dampedSquareTestContourIntegrand W ε X ((1+b : ℝ)+t*I)‖ ≤
        (A*X^(1+b)/b^3)*|t|^(-(j : ℝ)) := by
    intro t ht
    have ht0 : 0 < |t| := hT.trans_le ht
    calc _ ≤ A*X^(1+b)/b^3/(1+|t|)^j := hbound hε hε1 hb hb1 hX t
      _ ≤ A*X^(1+b)/b^3/|t|^j := by gcongr; linarith
      _ = _ := by rw [Real.rpow_neg (abs_nonneg t),Real.rpow_natCast,div_eq_mul_inv]
  have h := RHTower.Sieve.norm_integral_sub_interval_le_powerTail hint
    (show 0 ≤ A*X^(1+b)/b^3 by positivity) hjR hT hpoint
  convert h using 1
  ring



private theorem test_square_rectangle_bound (hW : IsTest W a b) :
    ∃ d ∈ Ioc (0 : ℝ) (1/128), ∀ j : ℕ, ∃ C > 0,
    ∀ {T δ ε b X x t : ℝ}, 1 ≤ T → 0 < δ → δ ≤ d/(1+T)^9 →
      0 < ε → ε < δ/4 → 0 < b → b ≤ δ → 1 ≤ X →
      x ∈ Icc (1-δ) (1+b) → |t| ≤ T →
      ‖dampedSquareTestContourIntegrand W ε X ((x : ℂ)+t*I)‖ ≤
        C*X^x*(1+|t|)^54*
          (1+‖((((x : ℂ)+t*I)-1)*(((x : ℂ)+t*I)+2*ε-1))⁻¹‖)/(1+|t|)^j := by
  obtain ⟨c,hc,A,hA,hsource⟩ := exists_dampedSquareContinuation_remainder_bound
  have hc0 : 0 < c := hc.1
  let d := c/4
  refine ⟨d,⟨by dsimp [d]; positivity,by dsimp [d]; linarith [hc.2]⟩,?_⟩
  intro j
  obtain ⟨B,hB,hM⟩ := exists_dampedSquareTestMellin_rapidDecay hW j 1
  refine ⟨A*B,by positivity,?_⟩
  intro T δ ε b X x t hT hδ hδd hε hεδ hb hbδ hX hx ht
  have hbase : 1 ≤ (1+T)^9 := one_le_pow₀ (by linarith)
  have hδsmall : δ ≤ d := hδd.trans (div_le_self (by dsimp [d]; positivity) hbase)
  have hδ1 : δ ≤ 1 := by dsimp [d] at hδsmall; linarith [hc.2]
  have hrad : 2*δ ≤ c/(1+|t|)^9 := by
    calc 2*δ ≤ 2*(d/(1+T)^9) := by gcongr
      _ = (c/2)/(1+T)^9 := by dsimp [d]; ring
      _ ≤ c/(1+T)^9 := by gcongr; linarith [hc.1]
      _ ≤ c/(1+|t|)^9 := by gcongr
  have hdist : dist (((x : ℂ)+t*I)+ε) (1+(t : ℂ)*I) ≤ c/(1+|t|)^9 := by
    rw [dist_eq_norm,show (((x : ℂ)+t*I)+ε)-(1+(t : ℂ)*I) =
      ((x+ε-1 : ℝ) : ℂ) by push_cast; ring,Complex.norm_real,Real.norm_eq_abs]
    exact (show |x+ε-1| ≤ 2*δ from abs_le.mpr ⟨by linarith [hx.1],by linarith [hx.2]⟩).trans hrad
  have heps : ‖(ε : ℂ)‖ ≤ c/(1+|t|)^9 := by
    rw [Complex.norm_real,Real.norm_of_nonneg hε.le]
    exact (show ε ≤ 2*δ by linarith).trans hrad
  have hJ : ‖(dampedSquareContinuation ε ((x : ℂ)+t*I)-1)/(ε : ℂ)^2‖ ≤
      A*(1+|t|)^54*(1+‖((((x : ℂ)+t*I)-1)*(((x : ℂ)+t*I)+2*ε-1))⁻¹‖) := by
    have h := hsource t ((x : ℂ)+t*I) ε hdist heps
    rw [Complex.norm_real,Real.norm_of_nonneg hε.le] at h
    rw [norm_div,norm_pow,Complex.norm_real,Real.norm_of_nonneg hε.le,
      div_le_iff₀ (sq_pos_of_pos hε)]
    simpa only [mul_assoc,mul_comm,mul_left_comm] using h
  have hstrip : |(((x : ℂ)+t*I)).re-1| ≤ 1 := by
    simp only [add_re,ofReal_re,mul_re,ofReal_im,I_re,I_im,mul_zero,zero_mul,
      sub_zero,add_zero]
    exact abs_le.mpr ⟨by linarith [hx.1],by linarith [hx.2]⟩
  have hm : ‖dampedSquareTestMellin W ((x : ℂ)+t*I)‖ ≤ B/(1+|t|)^j := by
    simpa using hM ((x : ℂ)+t*I) hstrip
  have hp : ‖(X : ℂ)^((x : ℂ)+t*I)‖ = X^x := by
    simpa using Complex.norm_cpow_eq_rpow_re_of_pos (by linarith : 0 < X) ((x : ℂ)+t*I)
  unfold dampedSquareTestContourIntegrand
  rw [norm_mul,norm_mul,hp]
  calc _ ≤ (A*(1+|t|)^54*(1+‖((((x : ℂ)+t*I)-1)*
      (((x : ℂ)+t*I)+2*ε-1))⁻¹‖))*(B/(1+|t|)^j)*X^x := by gcongr
    _ = _ := by ring

private theorem test_left_pole_inverse_le {δ ε t : ℝ} (hδ : 0 < δ)
    (hε : ε < δ/4) :
    ‖((((1-δ : ℝ) : ℂ)+t*I)-1)*((((1-δ : ℝ) : ℂ)+t*I)+2*ε-1)‖⁻¹ ≤ 2/δ^2 := by
  let s : ℂ := (1-δ : ℝ)+t*I
  have hp : δ ≤ ‖s-1‖ := by
    have h := Complex.abs_re_le_norm (s-1)
    simpa [s,abs_of_pos hδ] using h
  have hq : δ/2 ≤ ‖s+2*ε-1‖ := by
    have h := Complex.abs_re_le_norm (s+2*ε-1)
    have hr : (s+2*ε-1).re = -δ+2*ε := by dsimp [s]; simp; ring
    rw [hr,abs_of_neg (by linarith)] at h
    linarith
  have hprod : δ^2/2 ≤ ‖(s-1)*(s+2*ε-1)‖ := by
    rw [norm_mul]
    calc δ^2/2 = δ*(δ/2) := by ring
      _ ≤ _ := mul_le_mul hp hq (by positivity) (norm_nonneg _)
  calc _ ≤ (δ^2/2)⁻¹ := inv_anti₀ (by positivity) hprod
    _ = _ := by ring

private theorem test_horizontal_pole_inverse_le {x ε t T : ℝ} (hT : 1 ≤ T) (ht : |t| = T) :
    ‖((((x : ℂ)+t*I)-1)*(((x : ℂ)+t*I)+2*ε-1))⁻¹‖ ≤ 1 := by
  have hp : T ≤ ‖((x : ℂ)+t*I)-1‖ := by
    simpa [ht] using Complex.abs_im_le_norm (((x : ℂ)+t*I)-1)
  have hq : T ≤ ‖((x : ℂ)+t*I)+2*ε-1‖ := by
    simpa [ht] using Complex.abs_im_le_norm (((x : ℂ)+t*I)+2*ε-1)
  rw [norm_inv,norm_mul]
  exact inv_le_one_of_one_le₀ (one_le_mul_of_one_le_of_one_le (hT.trans hp) (hT.trans hq))

/-- Integrated left and both horizontal edges of the actual moving rectangle.
All constants are constructed from the actual source and actual window. -/
theorem exists_dampedSquareTestContour_edge_bounds (hW : IsTest W a b) :
    ∃ d ∈ Ioc (0 : ℝ) (1/128), ∃ C > 0, ∀ j : ℕ, ∃ A > 0,
    ∀ {T δ ε b X : ℝ}, 1 ≤ T → 0 < δ → δ ≤ d/(1+T)^9 →
      0 < ε → ε < δ/4 → 0 < b → b ≤ δ → 1 ≤ X →
      (‖∫ t in (-T)..T,dampedSquareTestContourIntegrand W ε X ((1-δ : ℝ)+t*I)‖ ≤
        C*X^(1-δ)*(1+T)^55*(1+2/δ^2)) ∧
      (∀ t : ℝ, |t| = T →
        ‖∫ x in (1-δ)..(1+b),dampedSquareTestContourIntegrand W ε X ((x : ℂ)+t*I)‖ ≤
          A*X^(1+b)*(1+T)^54/(1+T)^j) := by
  obtain ⟨d,hd,hrect⟩ := test_square_rectangle_bound hW
  obtain ⟨C,hC,hzero⟩ := hrect 0
  refine ⟨d,hd,2*C,by positivity,?_⟩
  intro j
  obtain ⟨A,hA,horder⟩ := hrect j
  refine ⟨4*A,by positivity,?_⟩
  intro T δ ε b X hT hδ hδd hε hεδ hb hbδ hX
  have hδ1 : δ ≤ 1 := by
    have h := hδd.trans (div_le_self hd.1.le (one_le_pow₀ (by linarith : 1 ≤ 1+T)))
    linarith [hd.2]
  constructor
  · have hpoint : ∀ t ∈ Ι (-T) T,
        ‖dampedSquareTestContourIntegrand W ε X ((1-δ : ℝ)+t*I)‖ ≤
          C*X^(1-δ)*(1+T)^54*(1+2/δ^2) := by
      intro t ht
      have ht' : |t| ≤ T := by
        rw [uIoc_of_le (by linarith : -T ≤ T)] at ht
        exact abs_le.mpr ⟨ht.1.le,ht.2⟩
      have h := hzero hT hδ hδd hε hεδ hb hbδ hX
        (show 1-δ ∈ Icc (1-δ) (1+b) from ⟨le_rfl,by linarith⟩) ht'
      simp only [pow_zero,div_one,norm_inv] at h
      calc _ ≤ C*X^(1-δ)*(1+|t|)^54*
          (1+‖((((1-δ : ℝ) : ℂ)+t*I)-1)*((((1-δ : ℝ) : ℂ)+t*I)+2*ε-1)‖⁻¹) := h
        _ ≤ _ := by
          gcongr
          exact test_left_pole_inverse_le hδ hεδ
    have h := intervalIntegral.norm_integral_le_of_norm_le_const hpoint
    rw [show |T-(-T)| = 2*T by rw [abs_of_pos (by linarith)]; ring] at h
    calc _ ≤ (C*X^(1-δ)*(1+T)^54*(1+2/δ^2))*(2*T) := h
      _ ≤ (C*X^(1-δ)*(1+T)^54*(1+2/δ^2))*(2*(1+T)) := by gcongr; linarith
      _ = _ := by rw [pow_succ]; ring
  · intro t ht
    have hpoint : ∀ x ∈ Ι (1-δ) (1+b),
        ‖dampedSquareTestContourIntegrand W ε X ((x : ℂ)+t*I)‖ ≤
          2*A*X^(1+b)*(1+T)^54/(1+T)^j := by
      intro x hx
      rw [uIoc_of_le (by linarith : 1-δ ≤ 1+b)] at hx
      have h := horder hT hδ hδd hε hεδ hb hbδ hX ⟨hx.1.le,hx.2⟩ ht.le
      rw [ht] at h
      have hxp : X^x ≤ X^(1+b) := Real.rpow_le_rpow_of_exponent_le hX hx.2
      have hpole := test_horizontal_pole_inverse_le (x := x) (ε := ε) hT ht
      calc _ ≤ A*X^x*(1+T)^54*
          (1+‖((((x : ℂ)+t*I)-1)*(((x : ℂ)+t*I)+2*ε-1))⁻¹‖)/(1+T)^j := h
        _ ≤ A*X^(1+b)*(1+T)^54*(1+1)/(1+T)^j := by gcongr
        _ = _ := by ring
    have h := intervalIntegral.norm_integral_le_of_norm_le_const hpoint
    rw [abs_of_nonneg (by linarith : 0 ≤ (1+b)-(1-δ))] at h
    calc _ ≤ (2*A*X^(1+b)*(1+T)^54/(1+T)^j)*((1+b)-(1-δ)) := h
      _ ≤ (2*A*X^(1+b)*(1+T)^54/(1+T)^j)*2 := by gcongr; linarith
      _ = _ := by ring

end RHTower.BAGTrace
