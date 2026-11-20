import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.LocalizingAPrimeSurplusToAFiniteMidpointWindow
import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.PrimeSamplingDownToSevenTwelfths

/-!
# Every real square-root level of the integer prime midpoint

Littlewood excursions cross both sides of every target of square-root
size. A first crossing locates the target to within a single midpoint
increment. On intervals of length n^α, α < 1/2, the total variation
from the crossing is smaller than the square-root scale.
-/

noncomputable section
open Filter
open scoped Topology
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

/-- Both signed readings exceed any fixed multiple of the square root
arbitrarily far out. -/
theorem midpoint_exceeds_each_square_root_level (A : ℝ) (σ : ℝ) (hσ : σ=1 ∨ σ= -1) :
    ∃ᶠ n : ℕ in atTop, A*Real.sqrt n < σ*primeMidpointPrice n := by
  have hg := midpointPowerGap_pos (s:=1/2) ⟨by norm_num,by norm_num⟩
  have hc := _root_.RHTower.littlewoodConst_pos
  obtain ⟨c,hc₀,hc'⟩ := exists_between (mul_pos hg (div_pos hc (by norm_num : (0:ℝ)<28)))
  have h := littlewood_excursions_of_integer_prime_midpoints hc₀ hc' σ hσ
  have ht := _root_.RHTower.tendsto_logLogLog_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  apply (h.and_eventually (ht.eventually_ge_atTop (A/c))).mono
  rintro n ⟨hn,ht⟩
  have hh := (div_le_iff₀ hc₀).mp ht
  have hv := mul_le_mul_of_nonneg_right hh (Real.sqrt_nonneg n)
  change A*Real.sqrt n ≤ Real.log (Real.log (Real.log n))*c*Real.sqrt n at hv
  linarith only [hv,hn]

/-- Oriented crossings persist for every moving target bounded on the
square-root scale, even when the target is discontinuous. -/
theorem midpoint_crosses_every_square_root_target (f : ℕ → ℝ) {A : ℝ} (hf : ∀ n, |f n|≤A*Real.sqrt n)
    (σ : ℝ) (hσ : σ=1 ∨ σ= -1) :
    ∃ᶠ n : ℕ in atTop, σ*(primeMidpointPrice n-f n)<0 ∧ 0≤σ*(primeMidpointPrice (n+1)-f (n+1)) := by
  classical
  let v := fun n => σ*(primeMidpointPrice n-f n)
  have hneg : -σ=1 ∨ -σ= -1 := by rcases hσ with rfl | rfl <;> norm_num
  have above {s : ℝ} (hs : s=1 ∨ s= -1) : ∃ᶠ n : ℕ in atTop, 0 < s*(primeMidpointPrice n-f n) := by
    apply (midpoint_exceeds_each_square_root_level A s hs).mono
    intro n hn
    have hb := abs_le.mp (hf n)
    rcases hs with rfl | rfl <;> simp only [one_mul,neg_one_mul] at hn ⊢ <;> linarith only [hn,hb.1,hb.2]
  rw [frequently_atTop]
  intro N
  obtain ⟨a,ha,hbelow⟩ := frequently_atTop.mp (above hneg) N
  obtain ⟨b,hab,habove⟩ := frequently_atTop.mp (above hσ) a
  have hv : v a<0 := by dsimp only [v]; rwa [neg_mul,neg_pos] at hbelow
  have hex : ∃ k : ℕ, a≤k ∧ 0≤v k := ⟨b,hab,habove.le⟩
  let k := Nat.find hex
  have hk : a≤k ∧ 0≤v k := Nat.find_spec hex
  have hak : a<k := lt_of_le_of_ne hk.1 (fun he => hv.not_ge (by rw [he]; exact hk.2))
  have hprev : v (k-1)<0 := lt_of_not_ge fun h => Nat.find_min hex (by omega : k-1<k) ⟨by omega,h⟩
  exact ⟨k-1,by omega,hprev,by simpa only [Nat.sub_add_cancel (by omega : 1≤k)] using hk.2⟩

/-- A Lipschitz moving target at square-root height is tracked throughout
arbitrarily late intervals of length n^α, with error O(n^t) for every
α < t < 1/2. -/
theorem prime_midpoint_tracks_a_moving_target (f : ℕ → ℝ) {A L : ℝ} (hL : 0≤L)
    (hf : ∀ n, |f n|≤A*Real.sqrt n)
    (hlip : ∀ n m : ℕ, n ≤ m → |f m-f n|≤L*((m:ℝ)-n))
    {α t : ℝ} (hα : 0≤α) (hat : α<t) (ht : t<1/2) :
    ∃ C : ℝ, 0≤C ∧ ∃ᶠ n : ℕ in atTop, ∀ m : ℕ, n ≤ m → (m:ℝ)≤n+(n:ℝ)^α →
      |primeMidpointPrice m-f m|≤C*(n:ℝ)^t := by
  obtain ⟨B,hB,hB'⟩ := midpoint_shift_on_power_window hat (ht.trans (by norm_num))
  have hcross := midpoint_crosses_every_square_root_target f hf 1 (Or.inl rfl)
  refine ⟨2*(B+L),by positivity,?_⟩
  apply (hcross.and_eventually (eventually_ge_atTop 1)).mono
  rintro n ⟨⟨hc,hc'⟩,hn⟩
  simp only [one_mul] at hc hc'
  have hn₁ : 1≤(n:ℝ) := Nat.one_le_cast.mpr hn
  have hstep : ((n+1:ℕ):ℝ)≤n+(n:ℝ)^α := by
    rw [Nat.cast_add,Nat.cast_one]
    linarith only [Real.one_le_rpow hn₁ hα]
  have hBstep := (hB' hn (Nat.lt_succ_self n) hstep).2
  have hLstep := hlip n (n+1) (Nat.le_succ n)
  simp only [Nat.cast_add,Nat.cast_one,add_sub_cancel_left,mul_one] at hLstep
  have hone := le_mul_of_one_le_right hL (Real.one_le_rpow hn₁ (hα.trans hat.le))
  have hcabs : |primeMidpointPrice n-f n|≤(B+L)*(n:ℝ)^t := by
    rw [abs_of_neg hc]
    linarith only [hc',(abs_le.mp hBstep).1,(abs_le.mp hLstep).1,hone]
  intro m hnm hm
  have hprice : |primeMidpointPrice n-primeMidpointPrice m|≤B*(n:ℝ)^t := by
    rcases hnm.eq_or_lt with he | hlt
    · rw [←he,sub_self,abs_zero]
      exact mul_nonneg hB (Real.rpow_nonneg (Nat.cast_nonneg n) t)
    · exact (hB' hn hlt hm).2
  have htarget := (hlip n m hnm).trans (mul_le_mul_of_nonneg_left
    ((sub_le_iff_le_add'.mpr hm).trans (Real.rpow_le_rpow_of_exponent_le hn₁ hat.le)) hL)
  rw [abs_le] at hcabs hprice htarget ⊢
  constructor <;> linarith only [hcabs.1,hcabs.2,hprice.1,hprice.2,htarget.1,htarget.2]

private theorem sqrt_lipschitz_at_integers {n m : ℕ} (hnm : n ≤ m) :
    |Real.sqrt m-Real.sqrt n|≤(m:ℝ)-n := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · obtain rfl : n=0 := by omega
    simp
  have hd := sub_nonneg.mpr (Real.sqrt_le_sqrt (Nat.cast_le.mpr hnm))
  have hsum := (Real.one_le_sqrt.mpr (Nat.one_le_cast.mpr hm)).trans (le_add_of_nonneg_right (Real.sqrt_nonneg n))
  have h := le_mul_of_one_le_right hd hsum
  rw [abs_of_nonneg hd]
  linarith only [h,Real.sq_sqrt (Nat.cast_nonneg (α:=ℝ) n),Real.sq_sqrt (Nat.cast_nonneg (α:=ℝ) m)]

/-- Every real number is a subsequential limit of the normalized ordinary
prime midpoint. The two-sided excursions leave no missing finite levels. -/
theorem every_real_is_a_normalized_prime_midpoint_limit (a : ℝ) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun j => primeMidpointPrice (φ j)/Real.sqrt (φ j)) atTop (𝓝 a) := by
  let f := fun n : ℕ => a*Real.sqrt n
  have hab (n : ℕ) : |f n| ≤ |a| * Real.sqrt n := by simp only [f,abs_mul,abs_of_nonneg (Real.sqrt_nonneg _),le_refl]
  have hL (n m : ℕ) (h : n ≤ m) : |f m-f n| ≤ |a| * ((m:ℝ)-n) := by
    simp only [f,←mul_sub,abs_mul]
    exact mul_le_mul_of_nonneg_left (sqrt_lipschitz_at_integers h) (abs_nonneg _)
  obtain ⟨C,hC,h⟩ := prime_midpoint_tracks_a_moving_target f (abs_nonneg a) hab hL
    (le_refl (0:ℝ)) (by norm_num : (0:ℝ)<1/4) (by norm_num)
  obtain ⟨φ,hφ,hφ'⟩ := extraction_of_frequently_atTop (h.and_eventually (eventually_ge_atTop 1))
  refine ⟨φ,hφ,?_⟩
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hl := ((tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<1/4)).comp
    ((tendsto_natCast_atTop_atTop (R:=ℝ)).comp hφ.tendsto_atTop)).const_mul C
  rw [mul_zero] at hl
  apply squeeze_zero (fun j => norm_nonneg _) _ hl
  intro j
  let n := φ j
  have hn : 0<(n:ℝ) := Nat.cast_pos.mpr (hφ' j).2
  have hs := Real.sqrt_pos.mpr hn
  have hh := (hφ' j).1 n le_rfl (le_add_of_nonneg_right (Real.rpow_nonneg hn.le _))
  have he : (n:ℝ)^(1/4:ℝ)/Real.sqrt n=(n:ℝ)^(-(1/4:ℝ)) := by
    rw [Real.sqrt_eq_rpow,←Real.rpow_sub hn]
    norm_num
  change ‖primeMidpointPrice n/Real.sqrt n-a‖ ≤ C*(n:ℝ)^(-(1/4:ℝ))
  rw [Real.norm_eq_abs,show primeMidpointPrice n/Real.sqrt n-a=(primeMidpointPrice n-f n)/Real.sqrt n by
    dsimp only [f]; rw [sub_div,mul_div_cancel_right₀ _ hs.ne'],abs_div,abs_of_pos hs]
  exact (div_le_div_of_nonneg_right hh hs.le).trans_eq (by rw [mul_div_assoc,he])

#print axioms midpoint_crosses_every_square_root_target
#print axioms prime_midpoint_tracks_a_moving_target
#print axioms every_real_is_a_normalized_prime_midpoint_limit

end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
