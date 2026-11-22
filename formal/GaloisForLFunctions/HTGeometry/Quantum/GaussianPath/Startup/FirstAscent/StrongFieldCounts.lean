import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.FirstAscent.StrongFieldBox
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnSpacing.BlockCount
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnSpacing.PairedRows

/-! # Simultaneous counts of large isolated fields -/
open Real MeasureTheory ProbabilityTheory Filter Set
open scoped Classical ENNReal
namespace GaloisForLFunctions.HTGeometry.FirstAscent
noncomputable section
private abbrev Block := PathPauliBlockLabel → ℝ

/-- Height whose Gaussian box has probability at least a constant times 2⁻ʰ. -/
def fieldHeight (h : ℕ) : ℝ := sqrt (h*log 2/24)

private theorem height_weight (h : ℕ) : exp (-(24*fieldHeight h^2)) = ((2:ℝ)^h)⁻¹ := by
  rw [fieldHeight,Real.sq_sqrt (by positivity),show 24*((h:ℝ)*log 2/24)=h*log 2 by ring,
    Real.exp_neg,Real.exp_nat_mul,Real.exp_log (by norm_num : (0:ℝ)<2)]

private theorem number_of_heights (j : ℕ) : j+1 ≤ (2:ℕ)^j := by
  induction j with
  | zero => decide
  | succ j ih => rw [pow_succ]; omega

/-- On one Gaussian chain the first 8ʲ pairs contain at least c·8ʲ/2ʰ
successful boxes at every height h ≤ j, on every sufficiently large scale. -/
theorem gaussian_strong_field_counts :
    ∃ c : ℝ, 0<c ∧ ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ j : ℕ in atTop, ∀ h ≤ j,
      c*(8:ℝ)^j/(2:ℝ)^h ≤ (((Finset.range (8^j)).filter
        (fun i => pathPauliBlock ω i ∈ strongFieldBox (fieldHeight h))).card : ℝ) := by
  let μ : Measure Block := Measure.infinitePi fun _ => gaussianReal 0 1
  let ν : Measure (ℕ→Block) := Measure.infinitePi fun _ => μ
  haveI : IsProbabilityMeasure μ := by unfold μ; infer_instance
  have hpair : MeasurePreserving pathPauliBlock pathPauliDisorderLaw ν := measurePreserving_paired_rows _
  obtain ⟨d,hd,hm⟩ := strong_field_box_mass
  let box (h : ℕ) := strongFieldBox (fieldHeight h)
  let bad (j h : ℕ) : Set (ℕ→Block) :=
    {x | (((Finset.range (8^j)).filter (fun i => x i ∈ box h)).card : ℝ) <
      d/2*(8:ℝ)^j/(2:ℝ)^h}
  have risk (j h : ℕ) (hh : h ≤ j) : ν (bad j h) ≤ ENNReal.ofReal (4/d/(4:ℝ)^j) := by
    have hm' := hm (fieldHeight h) (sqrt_nonneg _)
    rw [height_weight,←div_eq_mul_inv] at hm'
    change d/(2:ℝ)^h ≤ μ.real (box h) at hm'
    let m := ((8^j : ℕ):ℝ)*μ.real (box h)
    have hmean : d*(8:ℝ)^j/(2:ℝ)^h ≤ m := by
      dsimp only [m]
      push_cast
      calc
        _ = (8:ℝ)^j*(d/(2:ℝ)^h) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hm' (by positivity)
    have hp : 0 < m := (by positivity : 0<d*(8:ℝ)^j/(2:ℝ)^h).trans_le hmean
    have hs : bad j h ⊆ {ω : ℕ→Block | (((Finset.range (8^j)).filter (fun i => ω i ∈ box h)).card : ℝ) < m/2} := by
      intro x hx
      change _ < d/2*(8:ℝ)^j/(2:ℝ)^h at hx
      apply hx.trans_le
      calc
        _ = (d*(8:ℝ)^j/(2:ℝ)^h)/2 := by ring
        _ ≤ m/2 := div_le_div_of_nonneg_right hmean (by norm_num)
    have htail := iid_box_count_lower_tail μ (measurableSet_strongFieldBox _) (8^j) hp
    refine ((measure_mono hs).trans htail).trans (ENNReal.ofReal_le_ofReal ?_)
    have hm4 : d*(4:ℝ)^j ≤ m := by
      apply le_trans _ hmean
      apply (le_div_iff₀ (by positivity : 0<(2:ℝ)^h)).mpr
      calc
        _ ≤ d*(4:ℝ)^j*(2:ℝ)^j := mul_le_mul_of_nonneg_left
          (pow_le_pow_right₀ (by norm_num) hh) (by positivity)
        _ = _ := by rw [mul_assoc,←mul_pow]; norm_num
    exact (div_le_div_of_nonneg_left (by norm_num : (0:ℝ) ≤ 4) (by positivity) hm4).trans_eq (by rw [div_div])

  let failed (j : ℕ) := ⋃ h ∈ Finset.range (j+1), bad j h
  have hr (j : ℕ) : ν (failed j) ≤ ENNReal.ofReal (4/d)*(2:ℝ≥0∞)⁻¹^j := by
    have hs := (measure_biUnion_finset_le (μ := ν) (Finset.range (j+1)) (bad j)).trans
      (Finset.sum_le_sum fun h hh => risk j h (by have := Finset.mem_range.mp hh; omega))
    apply hs.trans
    rw [Finset.sum_const,Finset.card_range,nsmul_eq_mul]
    have hcast : ((j+1:ℕ):ℝ) ≤ (2:ℝ)^j := by
      exact_mod_cast number_of_heights j
    have hr' : ((j+1:ℕ):ℝ)*(4/d/(4:ℝ)^j) ≤ (4/d)*(2⁻¹:ℝ)^j := by
      apply (mul_le_mul_of_nonneg_right hcast (by positivity : 0 ≤ 4/d/(4:ℝ)^j)).trans_eq
      rw [inv_pow,show (4:ℝ)^j=2^j*2^j by rw [←mul_pow]; norm_num]
      field_simp
    have h := ENNReal.ofReal_le_ofReal hr'
    rw [ENNReal.ofReal_mul (Nat.cast_nonneg _),ENNReal.ofReal_natCast,
      ENNReal.ofReal_mul (by positivity),ENNReal.ofReal_pow (by norm_num),
      ENNReal.ofReal_inv_of_pos (by norm_num : (0:ℝ)<2)] at h
    simpa only [ENNReal.ofReal_ofNat] using h
  have hbc : ∀ᵐ x ∂ν, ∀ᶠ j in atTop, x ∉ failed j := by
    apply ae_eventually_notMem
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hr)
    rw [ENNReal.tsum_mul_left,ENNReal.tsum_geometric_two]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (by norm_num)
  refine ⟨d/2,half_pos hd,?_⟩
  filter_upwards [hpair.quasiMeasurePreserving.ae hbc] with ω hω
  filter_upwards [hω] with j hj
  intro h hh
  exact le_of_not_gt fun he => hj (mem_iUnion.mpr ⟨h,mem_iUnion.mpr
    ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hh),he⟩⟩)

#print axioms gaussian_strong_field_counts
end
end GaloisForLFunctions.HTGeometry.FirstAscent
