import GaloisForLFunctions.RHTower.WeilLagLocalWorkHuxley
import GaloisForLFunctions.RHTower.XiMassShellPrimeMass

/-!
# Prime mass at separated fractional levels

A Lipschitz profile crossing an interval supplies a short prime window at
each interior fractional level. Their integer floors separate the windows
even when the profile is nonmonotone and the readings have mesh errors.
-/

noncomputable section
namespace GaloisForLFunctions.CountingHolography.Sections

open Finset Filter Topology

/-- Ordinary primes in the half-open real interval (a,b]. -/
def contactBandPrimes (a b : ℝ) : Finset ℕ := (Ioc ⌊a⌋₊ ⌊b⌋₊).filter Nat.Prime

theorem mem_contactBandPrimes {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) {p : ℕ} :
    p ∈ contactBandPrimes a b ↔ p.Prime ∧ a < p ∧ (p:ℝ) ≤ b := by
  change p ∈ (Ioc ⌊a⌋₊ ⌊b⌋₊).filter Nat.Prime ↔ _
  rw [mem_filter,mem_Ioc,Nat.floor_lt ha,Nat.le_floor_iff hb]
  tauto

private theorem short_prime_mass {α : ℝ} (hα : 7/12 < α) (hα' : α < 1) :
    ∀ᶠ x : ℝ in atTop, ∀ h : ℝ, x^α ≤ h → h ≤ x/2 →
      h/2 ≤ ∑ p ∈ contactBandPrimes x (x+h), Real.log p := by
  have hα₀ : 0 ≤ α := by linarith only [hα]
  obtain ⟨T,hT⟩ := eventually_atTop.mp
    ((isLittleO_log_rpow_atTop (show 0 < α-1/2 by linarith only [hα])).bound (by norm_num : 0 < (1:ℝ)/32))
  filter_upwards [_root_.RHTower.eventually_abs_psi_window_sub_le hα hα' (by norm_num : 0 < (1:ℝ)/4),
    eventually_ge_atTop T,eventually_ge_atTop (1:ℝ)] with x hpsi hxT hx
  intro h hlow hhigh
  have hx₀ := zero_lt_one.trans_le hx
  have hh := (Real.rpow_pos_of_pos hx₀ α).trans_le hlow
  let y := x+h
  have hxy : x ≤ y := le_add_of_nonneg_right hh.le
  have hy := hx.trans hxy
  have hy₀ := hx₀.trans_le hxy
  have hl := hT y (hxT.trans hxy)
  simp only [Real.norm_eq_abs,abs_of_nonneg (Real.log_nonneg hy),
    abs_of_nonneg (Real.rpow_nonneg hy₀.le _)] at hl
  have hp := (abs_le.mp (Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log hy)).2
  have hpp : 2*Real.sqrt y*Real.log y ≤ y^α/16 := by
    have he : Real.sqrt y*y^(α-1/2) = y^α := by
      rw [Real.sqrt_eq_rpow,← Real.rpow_add hy₀,show 1/2+(α-1/2)=α by ring]
    linarith only [he,mul_le_mul_of_nonneg_left hl (Real.sqrt_nonneg y)]
  have hpow : y^α ≤ 2*x^α := by
    have h₂ : (2:ℝ)^α ≤ 2 := by simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) hα'.le
    calc y^α ≤ (2*x)^α := Real.rpow_le_rpow hy₀.le (by unfold y; linarith only [hhigh,hx]) hα₀
      _ = (2:ℝ)^α*x^α := Real.mul_rpow (by norm_num) hx₀.le
      _ ≤ _ := mul_le_mul_of_nonneg_right h₂ (Real.rpow_nonneg hx₀.le _)
  have hψ := (abs_le.mp (hpsi h hlow hhigh)).1
  change -(1/4*h) ≤ Chebyshev.psi y-Chebyshev.psi x-h at hψ
  unfold contactBandPrimes
  rw [← _root_.RHTower.chebyshevTheta_sub_eq_shellSum (Nat.floor_mono hxy)]
  change h/2 ≤ Chebyshev.theta y-Chebyshev.theta x
  linarith only [hψ,hp,hpp,hpow,hlow,Chebyshev.theta_le_psi x,hh]

/-- A fixed proportion of the prime weight is lost to floors for every
frequency t in the stated range and every reading within e of the negative
scaled profile. The proportion is uniform in the frequency and conductor. -/
theorem prime_floor_mass_of_profile_crossing {α u v L d : ℝ} (hα : 7/12 < α) (hα' : α < 1)
    (hu : 1 ≤ u) (huv : u ≤ v) (hL : 1 ≤ L) (hd : 0 < d)
    (f : ℝ → ℝ) (hc : ContinuousOn f (Set.Icc u v)) (hfu : 0 < f u) (hfv : f v=0)
    (hlip : ∀ x ∈ Set.Icc u (v+1), ∀ y ∈ Set.Icc u (v+1), |f x-f y| ≤ L*|x-y|) :
    ∃ e c K : ℝ, 0 < e ∧ 0 < c ∧ 0 < K ∧ ∀ᶠ B : ℝ in atTop,
      ∀ {t : ℝ}, d ≤ t → K*t ≤ B^(1-α) → ∀ X : ℕ → ℝ,
        (∀ p ∈ contactBandPrimes (u*B) ((v+1)*B), |X p+t*f ((p:ℝ)/B)| ≤ e) →
        c*B ≤ ∑ p ∈ contactBandPrimes (u*B) ((v+1)*B), Int.fract (X p)*Real.log p := by
  let e := min (1/16:ℝ) (min (d/4) (d*f u/16))
  have he : 0 < e := lt_min (by norm_num) (lt_min (by positivity) (by positivity))
  have he₁ : e ≤ 1/16 := min_le_left _ _
  have he₂ : e ≤ d/4 := (min_le_right _ _).trans (min_le_left _ _)
  have he₃ : e ≤ d*f u/16 := (min_le_right _ _).trans (min_le_right _ _)
  have hLp := zero_lt_one.trans_le hL
  have hv := hu.trans huv
  have hvp := zero_lt_one.trans_le hv
  let K := L*v/e
  have hK : 0 < K := div_pos (mul_pos hLp hvp) he
  refine ⟨e,f u*e/(8*L),K,he,by positivity,hK,?_⟩
  obtain ⟨H,hH⟩ := eventually_atTop.mp (short_prime_mass hα hα')
  filter_upwards [eventually_ge_atTop H,eventually_ge_atTop (1:ℝ)] with B hBH hB
  intro t hdt htK X hX
  have hBp := zero_lt_one.trans_le hB
  have ht := hd.trans_le hdt
  let w := e/(L*t)
  have hw : 0 < w := div_pos he (mul_pos hLp ht)
  have hwL : w*(L*t)=e := div_mul_cancel₀ _ (mul_pos hLp ht).ne'
  have hw₁ : w ≤ 1/4 := by
    apply (div_le_iff₀ (mul_pos hLp ht)).mpr
    linarith only [he₂,hdt,mul_le_mul_of_nonneg_right hL ht.le]
  let P := contactBandPrimes (u*B) ((v+1)*B)
  let I := range (⌊t*f u/2⌋₊+1)
  let F := fun p : ℕ => Int.fract (X p)*Real.log p
  let fiber := fun j : ℕ => P.filter (fun p => ⌊X p⌋ = -(j:ℤ)-1)
  have hpos {p : ℕ} (hp : p ∈ P) : 0 ≤ Real.log p := by
    have hpr := ((mem_contactBandPrimes (by positivity : 0 ≤ u*B) (by positivity : 0 ≤ (v+1)*B)).mp hp).1
    exact Real.log_nonneg (by exact_mod_cast hpr.one_le)
  have hlevel {j : ℕ} (hj : j ∈ I) : w*B/4 ≤ ∑ p ∈ fiber j, F p := by
    have hj' : (j:ℝ) ≤ t*f u/2 := by
      have hnat : j ≤ ⌊t*f u/2⌋₊ := Nat.lt_succ_iff.mp (mem_range.mp hj)
      exact (Nat.cast_le.mpr hnat).trans (Nat.floor_le (by positivity))
    have hc₀ : ((j:ℝ)+4*e)/t ∈ Set.Icc (f v) (f u) := by
      rw [hfv]
      refine ⟨by positivity,(div_le_iff₀ ht).mpr ?_⟩
      linarith only [hj',he₃,mul_le_mul_of_nonneg_right hdt hfu.le]
    obtain ⟨z,hz,hfz⟩ := intermediate_value_Icc' huv hc hc₀
    have hz₁ := hu.trans hz.1
    have hz₀ := zero_lt_one.trans_le hz₁
    have harg := (le_mul_of_one_le_left hBp.le hz₁)
    have hpwr : (z*B)^α ≤ w*B := by
      have hα₀ : 0 ≤ α := by linarith only [hα]
      have hvpow : z^α ≤ z := by simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hz₁ hα'.le
      have heq : K*e=L*v := div_mul_cancel₀ _ he.ne'
      have hBpow := mul_le_mul_of_nonneg_right htK (Real.rpow_nonneg hBp.le α)
      rw [← Real.rpow_add hBp,sub_add_cancel,Real.rpow_one] at hBpow
      calc (z*B)^α = z^α*B^α := Real.mul_rpow hz₀.le hBp.le
        _ ≤ v*B^α := mul_le_mul_of_nonneg_right (hvpow.trans hz.2) (Real.rpow_nonneg hBp.le _)
        _ ≤ w*B := by
          unfold w
          rw [div_mul_eq_mul_div,le_div_iff₀ (mul_pos hLp ht)]
          calc v*B^α*(L*t) = e*(K*t*B^α) := by rw [← mul_assoc,show v*B^α*L = K*e*B^α by rw [heq]; ring]; ring
            _ ≤ _ := mul_le_mul_of_nonneg_left hBpow he.le
    let S := contactBandPrimes (z*B) (z*B+w*B)
    have hmass : w*B/2 ≤ ∑ p ∈ S, Real.log p := hH (z*B) (hBH.trans harg) _ hpwr
      (by linarith only [mul_le_mul_of_nonneg_right hw₁ hBp.le,harg,hB])
    have hcell {p : ℕ} (hp : p ∈ S) :
        p ∈ fiber j ∧ 1/2 ≤ Int.fract (X p) := by
      obtain ⟨hprime,hl,hh⟩ := (mem_contactBandPrimes (by positivity : 0 ≤ z*B)
        (by positivity : 0 ≤ z*B+w*B)).mp hp
      have hlow : z < (p:ℝ)/B := (lt_div_iff₀ hBp).mpr hl
      have hhigh : (p:ℝ)/B ≤ z+w := (div_le_iff₀ hBp).mpr (hh.trans_eq (add_mul z w B).symm)
      have htop : (p:ℝ)/B ≤ v+1 := by linarith only [hhigh,hz.2,hw₁]
      have hmem : p ∈ P := (mem_contactBandPrimes (by positivity : 0 ≤ u*B)
        (by positivity : 0 ≤ (v+1)*B)).mpr ⟨hprime,(lt_div_iff₀ hBp).mp (hz.1.trans_lt hlow),(div_le_iff₀ hBp).mp htop⟩
      have hlip' := hlip ((p:ℝ)/B) ⟨hz.1.trans hlow.le,htop⟩ z ⟨hz.1,by linarith only [hz.2]⟩
      rw [abs_of_nonneg (sub_nonneg.mpr hlow.le)] at hlip'
      have hdif : |f ((p:ℝ)/B)-f z| ≤ L*w := hlip'.trans (mul_le_mul_of_nonneg_left (by linarith only [hhigh]) hLp.le)
      have heq := (eq_div_iff ht.ne').mp hfz
      obtain ⟨hl₁,hu₁⟩ := abs_le.mp hdif
      obtain ⟨hl₂,hu₂⟩ := abs_le.mp (hX p hmem)
      have hfloor : ⌊X p⌋ = -(j:ℤ)-1 := by
        rw [Int.floor_eq_iff]
        push_cast
        constructor <;> linarith only [hwL,heq,hl₂,hu₂,he₁,he,
          mul_le_mul_of_nonneg_left hl₁ ht.le,mul_le_mul_of_nonneg_left hu₁ ht.le]
      refine ⟨mem_filter.mpr ⟨hmem,hfloor⟩,?_⟩
      have hx := Int.floor_add_fract (X p)
      rw [hfloor] at hx
      push_cast at hx
      linarith only [hx,hwL,heq,hl₂,he₁,mul_le_mul_of_nonneg_left hu₁ ht.le]
    calc w*B/4 = (1/2:ℝ)*(w*B/2) := by ring
      _ ≤ (1/2:ℝ)*∑ p ∈ S, Real.log p := mul_le_mul_of_nonneg_left hmass (by norm_num)
      _ ≤ ∑ p ∈ S, F p := by
        rw [mul_sum]
        exact sum_le_sum fun p hp => mul_le_mul_of_nonneg_right (hcell hp).2 (hpos (mem_filter.mp (hcell hp).1).1)
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg (fun _ hp => (hcell hp).1)
        (fun p hp _ => mul_nonneg (Int.fract_nonneg _) (hpos (mem_filter.mp hp).1))
  have hdis : (I : Set ℕ).PairwiseDisjoint fiber := by
    intro i _ j _ hij
    apply disjoint_left.mpr
    intro p hi hj
    have he := (mem_filter.mp hi).2.symm.trans (mem_filter.mp hj).2
    omega
  have hcount : t*f u/2 ≤ (I.card:ℝ) := by
    simp only [I,card_range,Nat.cast_add,Nat.cast_one]
    exact (Nat.lt_floor_add_one _).le
  calc f u*e/(8*L)*B = (t*f u/2)*(w*B/4) := by unfold w; field_simp; ring
    _ ≤ (I.card:ℝ)*(w*B/4) := mul_le_mul_of_nonneg_right hcount (by positivity)
    _ ≤ ∑ j ∈ I, ∑ p ∈ fiber j, F p := by
      simpa only [sum_const,nsmul_eq_mul] using (sum_le_sum fun j hj => hlevel hj)
    _ = ∑ p ∈ I.biUnion fiber, F p := (sum_biUnion hdis).symm
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg (fun p hp => by
      obtain ⟨j,_,hj⟩ := mem_biUnion.mp hp
      exact (mem_filter.mp hj).1) (fun p hp _ => mul_nonneg (Int.fract_nonneg _) (hpos hp))

#print axioms prime_floor_mass_of_profile_crossing

end GaloisForLFunctions.CountingHolography.Sections
