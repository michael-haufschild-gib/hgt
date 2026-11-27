import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.BondTransfer.MovingDates.Sampling.TripleBoxes
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.BondTransfer.MovingDates.Sampling.Summability
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.RepeatedGates.PhysicalBlocks.CollectiveSignals.Calibration.SmallAngles

/-! # Uniform calibration density across a continuous band of dates -/
open MeasureTheory Filter Finset Real Set
namespace GaloisForLFunctions.HTGeometry.SpanningDensity.BondTransfer
open RepeatedGates.PhysicalBlocks RepeatedGates.PhysicalBlocks.CollectiveSignals
noncomputable section

private def radius (j a : ℕ) : ℝ := (a:ℝ)/j
private def bad (j a : ℕ) : Set PathPauliDisorder :=
  let δ := radius j a/10000
  {ω | ((goodBoxes (1/sqrt 2) δ ω (j^256)).card:ℝ)≤boxProbability (1/sqrt 2) δ*(j:ℝ)^256/4}

private theorem grid_tail {c : ℝ} (hc : 0<c)
    (hp : ∀ t∈Ioc (0:ℝ) 1, c*t^48≤boxProbability (1/sqrt 2) (t/10000))
    {j a : ℕ} (ha : 0<a) (haj : a≤j) :
    pathPauliDisorderLaw.real (bad j a)≤2*exp (-(c/4)*(j:ℝ)) := by
  have hj := ha.trans_le haj
  have hJ : (0:ℝ)<j := Nat.cast_pos.mpr hj
  have hj₁ : 1≤(j:ℝ) := by exact_mod_cast hj
  let r := radius j a
  have hr : r∈Ioc (0:ℝ) 1 := ⟨div_pos (Nat.cast_pos.mpr ha) hJ,
    (div_le_one hJ).mpr (Nat.cast_le.mpr haj)⟩
  have hmin : 1/(j:ℝ)≤r := div_le_div_of_nonneg_right (by exact_mod_cast ha) hJ.le
  have he := few_triple_boxes (1/sqrt 2) (r/10000) (j^256)
  rw [Nat.cast_pow] at he
  apply he.trans (mul_le_mul_of_nonneg_left (exp_le_exp.mpr _) zero_le_two)
  have hw := mul_le_mul_of_nonneg_right ((mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (one_div_pos.mpr hJ).le hmin 48) hc.le).trans (hp r hr)) (pow_nonneg hJ.le 256)
  have hpow : c*(1/(j:ℝ))^48*(j:ℝ)^256=c*(j:ℝ)^208 := by field_simp [hJ.ne']
  rw [hpow] at hw
  have hlarge : (j:ℝ)≤(j:ℝ)^208 := by simpa only [pow_one] using pow_le_pow_right₀ hj₁ (by decide : 1≤208)
  linarith only [hw,mul_le_mul_of_nonneg_left hlarge hc.le]

/-- Every date from 1/j to one has calibrated boxes of radius at most
t/10000 and density proportional to t⁴⁸ on the smallest tested prefix.
The same boxes persist on every larger prefix of the draw. -/
theorem gaussian_calibration_grid :
    ∃ c>0, ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ j : ℕ in atTop,
      ∀ m : ℕ, j^256 ≤ m → ∀ t∈Icc (1/(j:ℝ)) 1, ∃ δ : ℝ, 0≤δ ∧ δ≤t/10000 ∧
        c*((j:ℝ)^256*t^48)≤((goodBoxes (1/sqrt 2) δ ω m).card:ℝ) := by
  classical
  obtain ⟨c,hc,hp⟩ := calibrated_small_time_mass
  let E (j : ℕ) := ⋃ i : Fin j, bad j (i.val+1)
  letI : IsProbabilityMeasure pathPauliDisorderLaw := by unfold pathPauliDisorderLaw; infer_instance
  have hrare : ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ j : ℕ in atTop, ω∉E j := by
    apply avoid_exponential_windows pathPauliDisorderLaw E 1 2 (c:=c/4) (by positivity)
    apply Eventually.of_forall
    intro j
    have hb (i : Fin j) := grid_tail hc hp (Nat.succ_pos i.val) i.isLt
    apply (measureReal_iUnion_fintype_le _).trans ((sum_le_sum fun i _ => hb i).trans_eq _)
    simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,pow_one]
    ring
  refine ⟨c/(4*2^48),by positivity,?_⟩
  filter_upwards [hrare] with ω hw
  filter_upwards [hw,eventually_gt_atTop (0:ℕ)] with j hn hj
  intro m hm t ht
  have hJ : (0:ℝ)<j := Nat.cast_pos.mpr hj
  have ht₀ := (one_div_pos.mpr hJ).trans_le ht.1
  let a := ⌊t*(j:ℝ)⌋₊
  have h₁ : 1≤t*(j:ℝ) := (div_le_iff₀ hJ).mp ht.1
  have ha : 1≤a := Nat.le_floor (by simpa only [Nat.cast_one] using h₁)
  have hfloor : (a:ℝ)≤t*(j:ℝ) := Nat.floor_le (mul_nonneg ht₀.le hJ.le)
  have haj : a≤j := Nat.cast_le.mp (hfloor.trans ((mul_le_mul_of_nonneg_right ht.2 hJ.le).trans_eq (one_mul _)))
  let i : Fin j := ⟨a-1,by omega⟩
  have hi : i.val+1=a := by dsimp only [i]; omega
  have hgood : ω∉bad j a := fun h => hn (mem_iUnion.mpr ⟨i,by rwa [hi]⟩)
  let r := radius j a
  have hr : r∈Ioc (0:ℝ) 1 := ⟨div_pos (Nat.cast_pos.mpr ha) hJ,(div_le_one hJ).mpr (Nat.cast_le.mpr haj)⟩
  have hr₁ : r≤t := (div_le_iff₀ hJ).mpr hfloor
  have hr₂ : t/2≤r := by
    apply (le_div_iff₀ hJ).mpr
    have hf : t*(j:ℝ)<(a:ℝ)+1 := Nat.lt_floor_add_one _
    have h' : 1≤(a:ℝ) := by exact_mod_cast ha
    linarith only [hf,h']
  let δ := r/10000
  have hcount : boxProbability (1/sqrt 2) δ*(j:ℝ)^256/4<
      ((goodBoxes (1/sqrt 2) δ ω (j^256)).card:ℝ) := lt_of_not_ge hgood
  have hsub : goodBoxes (1/sqrt 2) δ ω (j^256)⊆goodBoxes (1/sqrt 2) δ ω m :=
    filter_subset_filter _ (range_mono hm)
  have hmass := mul_le_mul_of_nonneg_right ((mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (half_pos ht₀).le hr₂ 48) hc.le).trans (hp r hr)) (pow_nonneg hJ.le 256)
  change c*(t/2)^48*(j:ℝ)^256≤boxProbability (1/sqrt 2) δ*(j:ℝ)^256 at hmass
  refine ⟨δ,div_nonneg hr.1.le (by norm_num),div_le_div_of_nonneg_right hr₁ (by norm_num),?_⟩
  exact (show c/(4*2^48)*((j:ℝ)^256*t^48)≤((goodBoxes (1/sqrt 2) δ ω (j^256)).card:ℝ) by
    linarith only [hmass,hcount]).trans (Nat.cast_le.mpr (Finset.card_le_card hsub))

#print axioms gaussian_calibration_grid
end
end GaloisForLFunctions.HTGeometry.SpanningDensity.BondTransfer
