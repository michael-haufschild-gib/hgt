import GaloisForLFunctions.RHTower.ChiRamanujanDampedSquareContour

noncomputable section
open Complex Set Filter
open scoped Topology
namespace RHTower.BAGTrace

private theorem window_mellin_lipschitz :
    ∃ B > 0, ∀ s : ℂ, ‖s-1‖ ≤ 1 →
      ‖dampedSquareWindowMellin s-dampedSquareWindowMellin 1‖ ≤ B*‖s-1‖ := by
  have hc : Continuous (dslope dampedSquareWindowMellin 1) := by
    apply continuous_iff_continuousAt.mpr
    intro s
    exact (analyticAt_dslope_of_analyticAt
      (differentiable_dampedSquareWindowMellin.analyticAt 1)
      (differentiable_dampedSquareWindowMellin.analyticAt s)).continuousAt
  obtain ⟨B,hB⟩ := (isCompact_closedBall (1 : ℂ) 1).exists_bound_of_continuousOn hc.continuousOn
  refine ⟨|B|+1,by positivity,?_⟩
  intro s hs
  have hb := hB s (show s ∈ Metric.closedBall (1 : ℂ) 1 by simpa [dist_eq_norm] using hs)
  have he := sub_smul_dslope dampedSquareWindowMellin 1 s
  rw [smul_eq_mul] at he
  rw [← he,norm_mul,mul_comm]
  exact mul_le_mul_of_nonneg_right (by linarith [le_abs_self B]) (norm_nonneg _)

/-- Both actual rectangle residues, normalized at the physical square-law scale. -/
def dampedSquareResiduePacket (ε X : ℝ) : ℂ :=
  (dampedSquareMellinNumerator ε X 1/(2*ε) +
    dampedSquareMellinNumerator ε X (1-2*ε)/(-2*ε))/((X : ℂ)*Real.log X)

/-- The joint damping-height crossover; only positive arguments enter the residue law. -/
def dampedSquareCrossover (c : ℝ) : ℝ := (1-Real.exp (-2*c))/(2*c)

theorem dampedSquareResiduePacket_eq {ε X : ℝ} (hε : 0 < ε) (hX : 1 < X) :
    dampedSquareResiduePacket ε X =
      (dampedSquareRegularSource (1+ε) (-ε)*dampedSquareWindowMellin 1 -
        (((X^(-2*ε) : ℝ) : ℂ))*dampedSquareRegularSource (1-ε) (-ε)*
          dampedSquareWindowMellin (1-2*ε))/((2*ε*Real.log X : ℝ) : ℂ) := by
  have hX0 : 0 < X := by linarith
  have hx : (X : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hX0.ne'
  have he : (ε : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hε.ne'
  have hl : (Real.log X : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.log_pos hX).ne'
  have hp : (X : ℂ)^(1-2*(ε : ℂ)) =
      (X : ℂ)*((X^(-2*ε) : ℝ) : ℂ) := by
    rw [show (1 : ℂ)-2*ε = 1+((-2*ε : ℝ) : ℂ) by push_cast; ring,
      Complex.cpow_add _ _ hx,Complex.cpow_one,← Complex.ofReal_cpow hX0.le]
  unfold dampedSquareResiduePacket dampedSquareMellinNumerator
  rw [Complex.cpow_one,hp,show (1 : ℂ)-2*ε+ε = 1-ε by ring]
  push_cast
  field_simp
  ring

private theorem crossover_rpow {ε X : ℝ} (hX : 0 < X) :
    (dampedSquareCrossover (ε*Real.log X) : ℂ)*dampedSquareWindowMellin 1 =
      (1-(((X^(-2*ε) : ℝ) : ℂ)))*dampedSquareWindowMellin 1 /
        ((2*ε*Real.log X : ℝ) : ℂ) := by
  have he : X^(-2*ε) = Real.exp (-2*(ε*Real.log X)) := by
    rw [Real.rpow_def_of_pos hX]
    congr 1
    ring
  rw [he,dampedSquareCrossover]
  push_cast
  ring

private theorem residue_numerator_norm_le (a b m n : ℂ) {r : ℝ}
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
theorem exists_dampedSquareResiduePacket_uniform_coalescence :
    ∃ η ∈ Ioc (0 : ℝ) (1/128), ∃ C > 0, ∀ {ε X : ℝ},
      0 < ε → ε ≤ η → 1 < X →
      ‖dampedSquareResiduePacket ε X -
        (dampedSquareCrossover (ε*Real.log X) : ℂ)*dampedSquareWindowMellin 1‖ ≤
        C/Real.log X := by
  obtain ⟨η,hη,K,hK,hQ⟩ := exists_dampedSquareRegularSource_quadratic_bound
  obtain ⟨B,hB,hM⟩ := window_mellin_lipschitz
  let m := dampedSquareWindowMellin 1
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
  have hm : ‖dampedSquareWindowMellin (1-2*(ε : ℂ))-m‖ ≤ 2*B*ε := by
    have h := hM (1-2*(ε : ℂ)) (by rwa [hd])
    rw [hd] at h
    simpa only [m,mul_assoc,mul_comm,mul_left_comm] using h
  have hn : ‖dampedSquareWindowMellin (1-2*(ε : ℂ))‖ ≤ ‖m‖+2*B := by
    have h := norm_le_norm_sub_add (dampedSquareWindowMellin (1-2*(ε : ℂ))) m
    nlinarith
  have hr0 : 0 ≤ X^(-2*ε) := Real.rpow_nonneg hX0.le _
  have hr1 : X^(-2*ε) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hX.le (by linarith)
  have hnum := residue_numerator_norm_le
    (dampedSquareRegularSource (1+(ε : ℂ)) (-ε))
    (dampedSquareRegularSource (1-(ε : ℂ)) (-ε)) m
    (dampedSquareWindowMellin (1-2*(ε : ℂ))) hr0 hr1
  have hbound :
      ‖dampedSquareRegularSource (1+(ε : ℂ)) (-ε)*m -
        ((X^(-2*ε) : ℝ) : ℂ)*dampedSquareRegularSource (1-(ε : ℂ)) (-ε)*
          dampedSquareWindowMellin (1-2*(ε : ℂ)) -
        (1-(((X^(-2*ε) : ℝ) : ℂ)))*m‖ ≤ C*ε := by
    calc _ ≤ ‖dampedSquareRegularSource (1+(ε : ℂ)) (-ε)-1‖*‖m‖+
        ‖dampedSquareRegularSource (1-(ε : ℂ)) (-ε)-1‖*
          ‖dampedSquareWindowMellin (1-2*(ε : ℂ))‖+
        ‖dampedSquareWindowMellin (1-2*(ε : ℂ))-m‖ := hnum
      _ ≤ K*ε^2*‖m‖+K*ε^2*(‖m‖+2*B)+2*B*ε := by gcongr
      _ = ε^2*(K*‖m‖+K*(‖m‖+2*B))+2*B*ε := by ring
      _ ≤ ε*(K*‖m‖+K*(‖m‖+2*B))+2*B*ε := by gcongr
      _ = C*ε := by dsimp [C]; ring
  rw [dampedSquareResiduePacket_eq hε hX,crossover_rpow hX0,← sub_div,
    norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (by positivity : 0 < 2*ε*Real.log X)]
  calc _ ≤ C*ε/(2*ε*Real.log X) := div_le_div_of_nonneg_right hbound (by positivity)
    _ = (C/2)/Real.log X := by field_simp

/-- Uniform residue convergence includes every joint path with vanishing damping. -/
theorem exists_dampedSquareResiduePacket_tendstoUniformlyOn :
    ∃ η ∈ Ioc (0 : ℝ) (1/128),
      TendstoUniformlyOn
        (fun X ε => dampedSquareResiduePacket ε X -
          (dampedSquareCrossover (ε*Real.log X) : ℂ)*dampedSquareWindowMellin 1)
        (fun _ => 0) atTop (Ioc 0 η) := by
  obtain ⟨η,hη,C,hC,hbound⟩ := exists_dampedSquareResiduePacket_uniform_coalescence
  refine ⟨η,hη,Metric.tendstoUniformlyOn_iff.mpr ?_⟩
  intro r hr
  have ht : Tendsto (fun X : ℝ => C/Real.log X) atTop (𝓝 0) :=
    Real.tendsto_log_atTop.const_div_atTop C
  filter_upwards [ht.eventually (gt_mem_nhds hr),eventually_gt_atTop (1 : ℝ)] with X hXr hX
  intro ε hε
  simpa only [dist_zero_left] using (hbound hε.1 hε.2 hX).trans_lt hXr

end RHTower.BAGTrace
