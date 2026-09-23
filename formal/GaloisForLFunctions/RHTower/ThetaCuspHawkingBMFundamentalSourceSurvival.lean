import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMNonstationaryAsymptotic
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMPhysicalNonstationarySource

/-! A uniform positive lower bound for the actual source at sufficiently large Xi height. -/
namespace RHTower.D4BMJointSource
open Complex Set
open scoped Polynomial
noncomputable section
set_option autoImplicit false

private def normalizedSourceA (v : ℂ) : ℂ := 5+(5/2:ℂ)/v-(3/2:ℂ)/v^(2 : ℕ)
private def normalizedSourceB (v : ℂ) : ℂ := 15/2+(81/4:ℂ)/v+15/v^(2 : ℕ)+(9/4:ℂ)/v^(3 : ℕ)
private def normalizedSourceDeltaA (v : ℂ) : ℂ := 5/2-(3/2:ℂ)/v
private def normalizedSourceDeltaB (v : ℂ) : ℂ := 81/4+15/v+(9/4:ℂ)/v^(2 : ℕ)

private theorem normalizedSource_bounds (v : ℂ) (hv : 1 ≤ ‖v‖) :
    ‖normalizedSourceA v‖ ≤ 9 ∧ ‖normalizedSourceB v‖ ≤ 45 ∧
      ‖normalizedSourceDeltaA v‖ ≤ 4 ∧ ‖normalizedSourceDeltaB v‖ ≤ 75/2 := by
  have hd (c : ℂ) (n : ℕ) : ‖c/v^n‖ ≤ ‖c‖ := by
    have hn : 1 ≤ ‖v‖^n := one_le_pow₀ hv
    rw [norm_div,norm_pow]
    apply (div_le_iff₀ (by linarith : 0 < ‖v‖^n)).mpr
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hn (norm_nonneg c)
  have hd1 (c : ℂ) : ‖c/v‖ ≤ ‖c‖ := by simpa only [pow_one] using hd c 1
  refine ⟨?_,?_,?_,?_⟩
  · have h1 := hd1 (5/2:ℂ)
    have h2 := hd (3/2:ℂ) 2
    have t1 := norm_add_le (5:ℂ) ((5/2:ℂ)/v)
    have t2 := norm_sub_le (5+(5/2:ℂ)/v) ((3/2:ℂ)/v^(2 : ℕ))
    norm_num at h1 h2 t1 t2
    dsimp only [normalizedSourceA]
    linarith
  · have h1 := hd1 (81/4:ℂ)
    have h2 := hd (15:ℂ) 2
    have h3 := hd (9/4:ℂ) 3
    have t1 := norm_add_le (15/2:ℂ) ((81/4:ℂ)/v)
    have t2 := norm_add_le (15/2+(81/4:ℂ)/v) (15/v^(2 : ℕ))
    have t3 := norm_add_le (15/2+(81/4:ℂ)/v+15/v^(2 : ℕ)) ((9/4:ℂ)/v^(3 : ℕ))
    norm_num at h1 h2 h3 t1 t2 t3
    dsimp only [normalizedSourceB]
    linarith
  · have h1 := hd1 (3/2:ℂ)
    have t1 := norm_sub_le (5/2:ℂ) ((3/2:ℂ)/v)
    norm_num at h1 t1
    dsimp only [normalizedSourceDeltaA]
    linarith
  · have h1 := hd1 (15:ℂ)
    have h2 := hd (9/4:ℂ) 2
    have t1 := norm_add_le (81/4:ℂ) (15/v)
    have t2 := norm_add_le (81/4+15/v) ((9/4:ℂ)/v^(2 : ℕ))
    norm_num at h1 h2 t1 t2
    dsimp only [normalizedSourceDeltaB]
    linarith

private theorem normalizedSource_identity (w X Y : ℂ) (hw : w+1 ≠ 0) :
    (w+1)*((w+1)*(2*(fundamentalMomentConstant (-2*w-4)*X+
      fundamentalMomentQuadratic w (-2*w-4)*Y))-(172/625:ℂ)) =
      2*(normalizedSourceA (w+1)*((w+1)*((w+1)^(3 : ℕ)*X-(2/125:ℂ)))+
        normalizedSourceB (w+1)*((w+1)*((w+1)^(5 : ℕ)*Y-(24/3125:ℂ)))+
        normalizedSourceDeltaA (w+1)*(2/125:ℂ)+normalizedSourceDeltaB (w+1)*(24/3125:ℂ)) := by
  rw [nonstationarySourceConstant,nonstationarySourceQuadratic]
  unfold normalizedSourceA normalizedSourceB normalizedSourceDeltaA normalizedSourceDeltaB
  field_simp [hw]
  ring

/-- The complete source's growing polynomial coefficients preserve a nonzero leading term. -/
theorem nonstationarySourceMoment_error_bound :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ w : ℂ, w.re ∈ Icc (-(3/2):ℝ) (-1) → 1 ≤ ‖w+1‖ →
      ‖(w+1)*((w+1)*(2*(fundamentalMomentConstant (-2*w-4)*nonstationaryMoment ((1-Polynomial.X)^(2 : ℕ)) 0 w+
        fundamentalMomentQuadratic w (-2*w-4)*nonstationaryMoment ((1-Polynomial.X)^(4 : ℕ)) 0 w))-(172/625:ℂ))‖ ≤ K := by
  obtain ⟨C2,hC2,h2⟩ := nonstationaryMoment_second_bound
  obtain ⟨C4,hC4,h4⟩ := nonstationaryMoment_fourth_bound
  let K : ℝ := 2*(9*C2+45*C4+4*(2/125)+(75/2)*(24/3125))
  refine ⟨K,by dsimp only [K]; positivity,?_⟩
  intro w hw hv
  have hv0 : w+1 ≠ 0 := by intro h; rw [h,norm_zero] at hv; linarith
  let e2 := (w+1)*((w+1)^(3 : ℕ)*nonstationaryMoment ((1-Polynomial.X)^(2 : ℕ)) 0 w-(2/125:ℂ))
  let e4 := (w+1)*((w+1)^(5 : ℕ)*nonstationaryMoment ((1-Polynomial.X)^(4 : ℕ)) 0 w-(24/3125:ℂ))
  have he2 : ‖e2‖ ≤ C2 := h2 w hw hv0
  have he4 : ‖e4‖ ≤ C4 := h4 w hw hv0
  obtain ⟨ha,hb,hda,hdb⟩ := normalizedSource_bounds (w+1) hv
  have b1 : ‖normalizedSourceA (w+1)*e2‖ ≤ 9*C2 := by
    rw [norm_mul]
    exact mul_le_mul ha he2 (norm_nonneg _) (by norm_num)
  have b2 : ‖normalizedSourceB (w+1)*e4‖ ≤ 45*C4 := by
    rw [norm_mul]
    exact mul_le_mul hb he4 (norm_nonneg _) (by norm_num)
  have b3 : ‖normalizedSourceDeltaA (w+1)*(2/125:ℂ)‖ ≤ 4*(2/125:ℝ) := by
    rw [norm_mul]
    norm_num
    nlinarith
  have b4 : ‖normalizedSourceDeltaB (w+1)*(24/3125:ℂ)‖ ≤ (75/2)*(24/3125:ℝ) := by
    rw [norm_mul]
    norm_num
    nlinarith
  have bs : ‖normalizedSourceA (w+1)*e2+normalizedSourceB (w+1)*e4+
      normalizedSourceDeltaA (w+1)*(2/125:ℂ)+normalizedSourceDeltaB (w+1)*(24/3125:ℂ)‖ ≤
      9*C2+45*C4+4*(2/125:ℝ)+(75/2)*(24/3125) := by
    have t1 := norm_add_le (normalizedSourceA (w+1)*e2) (normalizedSourceB (w+1)*e4)
    have t2 := norm_add_le (normalizedSourceA (w+1)*e2+normalizedSourceB (w+1)*e4)
      (normalizedSourceDeltaA (w+1)*(2/125:ℂ))
    have t3 := norm_add_le (normalizedSourceA (w+1)*e2+normalizedSourceB (w+1)*e4+
      normalizedSourceDeltaA (w+1)*(2/125:ℂ)) (normalizedSourceDeltaB (w+1)*(24/3125:ℂ))
    linarith
  rw [normalizedSource_identity _ _ _ hv0,norm_mul]
  rw [show ‖(2:ℂ)‖=(2:ℝ) by norm_num]
  exact mul_le_mul_of_nonneg_left bs (by norm_num : (0:ℝ)≤2)

/-- Above a fixed original Xi height, the actual source has a uniform positive normalized lower bound. -/
theorem physicalFundamentalSourceMoment_high_height_lower_bound :
    ∃ H : ℝ, 0 < H ∧ ∀ q : XiZeroCopy, H ≤ |(q.1:ℂ).im| → ∀ a : ℂ,
      (86/625:ℝ)*‖a‖^(2 : ℕ) ≤ ‖(physicalFundamentalFrequency q true+1)*
        fundamentalSourceMoment (physicalFundamentalFrequency q true) (D4BMModularCore.physicalRate q true) a‖ := by
  obtain ⟨K,hK0,hK⟩ := nonstationarySourceMoment_error_bound
  let R : ℝ := 1+2*K/(172/625)
  have hR1 : 1 ≤ R := by dsimp only [R]; linarith
  refine ⟨2*R,by linarith,?_⟩
  intro q hq a
  let w := physicalFundamentalFrequency q true
  have hwv : w+1=-(q.1:ℂ)/2 := by
    dsimp only [w]
    rw [physicalFundamentalFrequency_eq]
    norm_num
    ring
  have hvR : R ≤ ‖w+1‖ := by
    have hi := Complex.abs_im_le_norm (q.1:ℂ)
    rw [hwv,norm_div,norm_neg]
    norm_num
    linarith
  have hv1 : 1 ≤ ‖w+1‖ := hR1.trans hvR
  have hvpos : 0 < ‖w+1‖ := lt_of_lt_of_le zero_lt_one hv1
  have hs := physicalNonstationaryFrequency_strip q
  have hb := hK w ⟨hs.1.le,hs.2.le⟩ hv1
  have hm := physicalFundamentalSourceMoment_nonstationary q 1
  norm_num only [one_pow,mul_one] at hm
  rw [← hm] at hb
  let u := (w+1)*fundamentalSourceMoment w (D4BMModularCore.physicalRate q true) 1
  change ‖(w+1)*(u-(172/625:ℂ))‖ ≤ K at hb
  rw [norm_mul] at hb
  have he : ‖u-(172/625:ℂ)‖ ≤ K/‖w+1‖ := by
    apply (le_div_iff₀ hvpos).mpr
    nlinarith
  have he' : K/‖w+1‖ ≤ (86/625:ℝ) := by
    apply (div_le_iff₀ hvpos).mpr
    dsimp only [R] at hvR
    nlinarith
  have hu : (86/625:ℝ) ≤ ‖u‖ := by
    have ht := norm_sub_le u (u-(172/625:ℂ))
    rw [show u-(u-(172/625:ℂ))=(172/625:ℂ) by ring] at ht
    norm_num at ht
    have he'' := he.trans he'
    linarith
  rw [physicalFundamentalSourceMoment_amplitude q a]
  change (86/625:ℝ)*‖a‖^(2 : ℕ) ≤ ‖(w+1)*(a^(2 : ℕ)*fundamentalSourceMoment w (D4BMModularCore.physicalRate q true) 1)‖
  rw [show (w+1)*(a^(2 : ℕ)*fundamentalSourceMoment w (D4BMModularCore.physicalRate q true) 1)=a^(2 : ℕ)*u by dsimp only [u]; ring,
    norm_mul,norm_pow]
  calc
    _ = ‖a‖^(2 : ℕ)*(86/625:ℝ) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hu (sq_nonneg ‖a‖)

/-- A nonzero original amplitude survives in this actual physical channel at every sufficiently large Xi height. -/
theorem physicalFundamentalSourceMoment_high_height_ne_zero :
    ∃ H : ℝ, 0 < H ∧ ∀ q : XiZeroCopy, H ≤ |(q.1:ℂ).im| → ∀ a : ℂ, a ≠ 0 →
      fundamentalSourceMoment (physicalFundamentalFrequency q true) (D4BMModularCore.physicalRate q true) a ≠ 0 := by
  obtain ⟨H,hH,h⟩ := physicalFundamentalSourceMoment_high_height_lower_bound
  refine ⟨H,hH,?_⟩
  intro q hq a ha hz
  have hb := h q hq a
  rw [hz,mul_zero,norm_zero] at hb
  have hp : 0 < ‖a‖^(2 : ℕ) := sq_pos_of_pos (norm_pos_iff.mpr ha)
  nlinarith

end
end RHTower.D4BMJointSource
