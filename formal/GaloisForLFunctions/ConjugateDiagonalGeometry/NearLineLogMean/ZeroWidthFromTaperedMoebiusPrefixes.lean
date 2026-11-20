import GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.MaximalPrefixesOfTheLongMoebiusSection
import GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.TheExactCostOfUndoingAPrefixTaper

/-!
# Which tapered prefix observations still read the zero-free half-plane?

The taper may vary with both the cutoff exponent and the observation horizon.
An endpoint weight at least a fixed negative power of the horizon suffices:
the inverse Abel bound transfers the whole sharp Möbius section through the
same integral at a cost independent of the cutoff exponent.
-/

noncomputable section
open Filter Topology Finset Complex MeasureTheory
open GaloisForLFunctions.MultiscaleMollifiedZetaField GaloisForLFunctions.SquareRootThreshold
namespace GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean

private def taperedSection (w : ℕ → ℝ) (j : ℕ) (t : ℝ) :=
  _root_.RHTower.edPoly (fun n => (w n:ℂ)*_root_.RHTower.mobCoeff n) (Ioc 0 j) (linePoint t)

/-- Largest of all prefixes after applying the same taper to each prefix. -/
def taperedMoebiusMaximum (w : ℕ → ℝ) (N : ℕ) (t : ℝ) :=
  (range (N+1)).sup' ⟨0,by simp⟩ fun j => ‖taperedSection w j t‖

private theorem le_taperedMaximum (w : ℕ → ℝ) {j N : ℕ} (hj : j ≤ N) (t : ℝ) :
    ‖taperedSection w j t‖ ≤ taperedMoebiusMaximum w N t :=
  le_sup' (fun k => ‖taperedSection w k t‖) (mem_range.mpr (Nat.lt_succ_of_le hj))

private theorem maximum_nonneg (w : ℕ → ℝ) (N : ℕ) (t : ℝ) : 0 ≤ taperedMoebiusMaximum w N t :=
  (norm_nonneg _).trans (le_taperedMaximum w (j:=N) le_rfl t)

private theorem continuous_taperedMaximum (w : ℕ → ℝ) (N : ℕ) : Continuous (taperedMoebiusMaximum w N) := by
  apply Continuous.finset_sup'_apply
  intro j _
  exact ((_root_.RHTower.differentiable_edPoly _ (s:=Ioc 0 j)
    (fun _ hn => (mem_Ioc.mp hn).1)).continuous.comp continuous_linePoint).norm

private theorem tapered_le_sharp (w : ℕ → ℝ) (hw : ∀ n, 0 ≤ w n) (hm : Antitone w)
    (h1 : w 1 ≤ 1) (N : ℕ) (t : ℝ) : taperedMoebiusMaximum w N t ≤ moebiusPrefixMaximum N t := by
  apply sup'_le
  intro j hj
  have hjN := Nat.le_of_lt_succ (mem_range.mp hj)
  have H := (moebius_prefix_maximum_iff_taper_bound j t _).mp le_rfl w hw hm h1
  apply H.trans
  apply sup'_le
  intro k hk
  exact moebius_prefix_norm_le_maximum ((Nat.le_of_lt_succ (mem_range.mp hk)).trans hjN) t

/-- An arbitrary positive decreasing taper recovers the full critical-line
section from its tapered prefixes, even when its choice depends on the cutoff. -/
theorem moebius_section_le_tapered_maximum (w : ℕ → ℝ) (hw : ∀ n, 0 < w n)
    (hm : Antitone w) (N : ℕ) (t : ℝ) :
    ‖moebiusPoly N (linePoint t)‖ ≤ 2*(w N)⁻¹*taperedMoebiusMaximum w N t := by
  cases N with
  | zero =>
    simp only [moebiusPoly,_root_.RHTower.edPoly,show Icc 1 0=∅ from by decide,sum_empty,norm_zero]
    exact mul_nonneg (mul_nonneg zero_le_two (inv_nonneg.mpr (hw 0).le)) (maximum_nonneg w 0 t)
  | succ N =>
    let f (j : ℕ) := _root_.RHTower.mobCoeff j*((j:ℝ):ℂ)^(-linePoint t)
    have H := untapered_endpoint_le w hw hm f N (B:=taperedMoebiusMaximum w (N+1) t) (fun n hn => by
      simpa only [f,taperedSection,_root_.RHTower.edPoly,mul_assoc] using
        le_taperedMaximum w (mem_Ioc.mp hn).2 t)
    change ‖∑ j ∈ Ioc 0 (N+1), f j‖ ≤ _
    exact H.trans (mul_le_mul_of_nonneg_right (sub_le_self _ (inv_nonneg.mpr (hw 1).le))
      (maximum_nonneg _ _ _))

/-- Choosing different tapers at every horizon preserves the exact cofinal
length slope as long as their last weights have a common polynomial lower
bound in the horizon. The multiplicative constant may depend on the length exponent. -/
theorem tapered_prefix_slope_iff_zero_width (w : ℝ → ℝ → ℕ → ℝ)
    (hw : ∀ θ T n, 0 < w θ T n) (hm : ∀ θ T, Antitone (w θ T)) (h1 : ∀ θ T, w θ T 1 ≤ 1)
    {p : ℝ} (hp : 0 ≤ p)
    (hend : ∀ θ : ℝ, 0 < θ → ∃ A : ℝ, 0 ≤ A ∧ ∀ᶠ T : ℝ in atTop,
      (w θ T ⌊T^θ⌋₊)⁻¹ ≤ A*T^p) {β : ℝ} (hβ : 0 ≤ β) :
    (∃ K : ℝ, 0 ≤ K ∧ ∀ θ₀ : ℝ, 0 < θ₀ → ∃ θ : ℝ, θ₀ ≤ θ ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∃ᶠ T : ℝ in atTop,
      (∫ t in (1:ℝ)..T, (taperedMoebiusMaximum (w θ T) ⌊T^θ⌋₊ t)^2) ≤ C*T^(K+2*β*θ)) ↔
      zetaZeroWidth ≤ β := by
  constructor
  · rintro ⟨K,hK,H⟩
    apply zetaZeroWidth_le_of_cofinal_pure_moebius_slope hβ (show 0 ≤ 2*p+K by positivity)
    intro θ₀ hθ₀
    obtain ⟨θ,hθ,C,hC,hgood⟩ := H θ₀ hθ₀
    obtain ⟨A,hA,hendθ⟩ := hend θ (hθ₀.trans_le hθ)
    refine ⟨θ,hθ,4*A^2*C,by positivity,(hgood.and_eventually (hendθ.and (eventually_ge_atTop (1:ℝ)))).mono ?_⟩
    rintro T ⟨hbound,hlast,hT⟩
    let N := ⌊T^θ⌋₊
    let W := taperedMoebiusMaximum (w θ T) N
    have hTpos := zero_lt_one.trans_le hT
    have hpt (t : ℝ) : ‖moebiusPoly N (linePoint t)‖^2 ≤ (2*(A*T^p))^2*(W t)^2 := by
      rw [←mul_pow]
      apply pow_le_pow_left₀ (norm_nonneg _)
      exact (moebius_section_le_tapered_maximum _ (hw θ T) (hm θ T) N t).trans
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlast zero_le_two) (maximum_nonneg _ _ _))
    simp_rw [edPoly_moebiusMollifierCoeff_eq_moebiusPoly]
    have HI := intervalIntegral.integral_mono_on (μ:=volume) hT (f:=fun t => ‖moebiusPoly N (linePoint t)‖^2)
      (g:=fun t => (2*(A*T^p))^2*(W t)^2)
      ((((differentiable_moebiusPoly N).continuous.comp continuous_linePoint).norm.pow 2).intervalIntegrable _ _)
      ((((continuous_taperedMaximum _ _).pow 2).const_mul _).intervalIntegrable _ _) (fun t _ => hpt t)
    rw [intervalIntegral.integral_const_mul] at HI
    refine HI.trans ((mul_le_mul_of_nonneg_left hbound (sq_nonneg _)).trans_eq ?_)
    have hp2 : (T^p)^2 = T^(2*p) := by rw [mul_comm (2:ℝ),Real.rpow_mul hTpos.le,Real.rpow_two]
    rw [mul_pow,mul_pow,hp2,show 2*p+K+2*β*θ=2*p+(K+2*β*θ) by ring,Real.rpow_add hTpos (2*p) (K+2*β*θ)]
    ring
  · intro hwidth
    obtain ⟨K,hK,H⟩ := (zetaZeroWidth_iff_cofinal_maximal_moebius_slope hβ).mp hwidth
    refine ⟨K,hK,fun θ₀ hθ₀ => ?_⟩
    obtain ⟨θ,hθ,C,hC,hgood⟩ := H θ₀ hθ₀
    refine ⟨θ,hθ,C,hC,(hgood.and_eventually (eventually_ge_atTop (1:ℝ))).mono fun T ⟨hh,hT⟩ => ?_⟩
    exact (intervalIntegral.integral_mono_on hT (((continuous_taperedMaximum _ _).pow 2).intervalIntegrable _ _)
      (((continuous_moebiusPrefixMaximum _).pow 2).intervalIntegrable _ _) fun t _ =>
        pow_le_pow_left₀ (maximum_nonneg _ _ _) (tapered_le_sharp (w θ T) (fun n => (hw θ T n).le)
          (hm θ T) (h1 θ T) _ t) 2).trans hh

/-- For any decreasing strictly positive profile, allow its power to change
at each observation horizon. The exact sufficient constraint is the order
times the logarithmic loss of the last coefficient. -/
theorem variable_taper_power_iff_zero_width (w : ℕ → ℝ) (hw : ∀ n, 0 < w n)
    (hm : Antitone w) (h1 : w 1 ≤ 1) (order : ℝ → ℝ → ℕ) {p : ℝ} (hp : 0 ≤ p)
    (horder : ∀ θ : ℝ, 0 < θ → ∀ᶠ T : ℝ in atTop,
      (order θ T:ℝ)*(-Real.log (w ⌊T^θ⌋₊)) ≤ p*Real.log T) {β : ℝ} (hβ : 0 ≤ β) :
    (∃ K : ℝ, 0 ≤ K ∧ ∀ θ₀ : ℝ, 0 < θ₀ → ∃ θ : ℝ, θ₀ ≤ θ ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∃ᶠ T : ℝ in atTop,
      (∫ t in (1:ℝ)..T, (taperedMoebiusMaximum (fun n => w n^(order θ T)) ⌊T^θ⌋₊ t)^2) ≤ C*T^(K+2*β*θ)) ↔
      zetaZeroWidth ≤ β := by
  apply tapered_prefix_slope_iff_zero_width (p:=p) (fun θ T n => w n^(order θ T))
    (fun _ _ n => pow_pos (hw n) _) (fun _ _ i j hij => pow_le_pow_left₀ (hw j).le (hm hij) _)
    (fun _ _ => pow_le_one₀ (hw 1).le h1) hp _ hβ
  intro θ hθ
  refine ⟨1,zero_le_one,?_⟩
  filter_upwards [horder θ hθ,eventually_gt_atTop (0:ℝ)] with T hT hTpos
  rw [one_mul,←Real.log_le_log_iff (inv_pos.mpr (pow_pos (hw _) _)) (Real.rpow_pos_of_pos hTpos _),
    Real.log_inv,Real.log_pow,Real.log_rpow hTpos]
  linarith only [hT]

/-- A concrete admissible order for every positive decreasing taper.
For the normalized reciprocal logarithm its size at fixed cutoff exponent
is proportional to log T / log log T when p is positive. -/
def observationTaperOrder (p : ℝ) (w : ℕ → ℝ) (θ T : ℝ) : ℕ :=
  ⌊p*Real.log T / (-Real.log (w ⌊T^θ⌋₊))⌋₊

theorem observation_taper_order_iff_zero_width (w : ℕ → ℝ) (hw : ∀ n, 0 < w n)
    (hm : Antitone w) (h1 : w 1 ≤ 1) {p β : ℝ} (hp : 0 ≤ p) (hβ : 0 ≤ β) :
    (∃ K : ℝ, 0 ≤ K ∧ ∀ θ₀ : ℝ, 0 < θ₀ → ∃ θ : ℝ, θ₀ ≤ θ ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∃ᶠ T : ℝ in atTop,
      (∫ t in (1:ℝ)..T, (taperedMoebiusMaximum (fun n => w n^(observationTaperOrder p w θ T))
        ⌊T^θ⌋₊ t)^2) ≤ C*T^(K+2*β*θ)) ↔ zetaZeroWidth ≤ β := by
  apply variable_taper_power_iff_zero_width w hw hm h1 _ hp _ hβ
  intro θ hθ
  filter_upwards [eventually_ge_atTop (1:ℝ)] with T hT
  have hN := (Nat.one_le_floor_iff (T^θ)).mpr (Real.one_le_rpow hT hθ.le)
  have hL : 0 ≤ -Real.log (w ⌊T^θ⌋₊) :=
    neg_nonneg.mpr (Real.log_nonpos (hw _).le ((hm hN).trans h1))
  have htop := mul_nonneg hp (Real.log_nonneg hT)
  rcases eq_or_lt_of_le hL with hz|hpos
  · rw [←hz,mul_zero]; exact htop
  · exact (le_div_iff₀ hpos).mp (Nat.floor_le (div_nonneg htop hpos.le))

#print axioms moebius_section_le_tapered_maximum
#print axioms tapered_prefix_slope_iff_zero_width
#print axioms variable_taper_power_iff_zero_width
#print axioms observation_taper_order_iff_zero_width

end GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean
