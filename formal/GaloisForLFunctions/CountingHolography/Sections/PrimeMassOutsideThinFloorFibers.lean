import GaloisForLFunctions.RHTower.Sieve.AdaptiveGallagherBrunTitchmarsh
import GaloisForLFunctions.CountingHolography.Sections.PrimeMassAtFractionalLevels

/-!
# Primes outside thin floor fibers

In a prime band of size R², a reading of size O(t) takes O(t) different
integer floors. If near-integer readings with each floor span length
O(eR²/t) and t is at most a constant times R, the upper-bound sieve leaves a positive proportion of prime mass
with fractional part at least e. No prime asymptotic on intervals of
length R is needed.
-/

noncomputable section
namespace GaloisForLFunctions.CountingHolography.Sections

open Finset Filter Topology

private theorem thin_prime_mass {s : Finset ℕ} {a H Z : ℝ} (ha : 0 < a) (hH : 1 < H)
    (hlog : Real.log Z ≤ 3*Real.log H)
    (hs : ∀ p ∈ s, p.Prime ∧ a ≤ (p:ℝ) ∧ (p:ℝ) ≤ a+H ∧ (p:ℝ) ≤ Z) :
    ∑ p ∈ s, Real.log p ≤ 876*H := by
  have hcard : (s.card:ℝ) ≤ BrunTitchmarsh.primesBetween a (a+H) := by
    apply Nat.cast_le.mpr
    apply card_le_card
    intro p hp
    obtain ⟨hpr,hlo,hhi,_⟩ := hs p hp
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨Nat.ceil_le.mpr hlo,(Nat.le_floor_iff (by linarith only [ha,hH] : 0 ≤ a+H)).mpr hhi⟩,hpr⟩
  have hb := hcard.trans (_root_.RHTower.Sieve.primesBetween_le_div_log ha hH)
  have hmass := sum_le_sum (s := s) (fun p hp => Real.log_le_log (Nat.cast_pos.mpr (hs p hp).1.pos) (hs p hp).2.2.2)
  simp only [sum_const,nsmul_eq_mul] at hmass
  have he := (le_div_iff₀ (Real.log_pos hH)).mp hb
  exact hmass.trans (by linarith only [mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg (α := ℝ) s.card),he])

/-- A band of primes with quadratic log mass retains quadratic weighted
fractional part when each integer level has a uniform inverse slope.
The reading can have additive error e in the inverse-slope inequality. -/
theorem prime_mass_outside_thin_floor_fibers {a b C v d Z : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hC : 1 ≤ C) (hv : 1 ≤ v) (hd : 0 < d) (hZ : 1 ≤ Z) :
    ∃ e c : ℝ, 0 < e ∧ 0 < c ∧ ∀ᶠ R : ℝ in atTop, ∀ {t : ℝ}, d ≤ t → t ≤ Z*R → ∀ (S : Finset ℕ) (X : ℕ → ℝ),
      (∀ p ∈ S, p.Prime ∧ (p:ℝ) ≤ v*R^2 ∧ -(C*t) ≤ X p ∧ X p ≤ 0) →
      b*R^2 ≤ ∑ p ∈ S, Real.log p →
      (∀ p ∈ S, ∀ q ∈ S, p ≤ q → (q:ℝ)-p ≤ (a*(R^2/t))*(X q-X p+e)) →
      c*R^2 ≤ ∑ p ∈ S, Int.fract (X p)*Real.log p := by
  classical
  let D := C+3/d
  have hD : 0 < D := add_pos (zero_lt_one.trans_le hC) (div_pos (by norm_num) hd)
  have hZ₀ := zero_lt_one.trans_le hZ
  let e := b/(4000*D*a)
  let h := 2*a*e
  have he : 0 < e := div_pos hb (by positivity)
  have hh : 0 < h := by dsimp only [h]; positivity
  have hbudget : 4000*D*a*e=b := mul_div_cancel₀ _ (by positivity : 4000*D*a ≠ 0)
  refine ⟨e,e*b/2,he,by positivity,?_⟩
  let g := h/Z
  have hg : 0 < g := div_pos hh hZ₀
  filter_upwards [eventually_ge_atTop (2/g),eventually_ge_atTop (v/g^3),eventually_ge_atTop (1:ℝ)] with R hR₁ hR₂ hR
  intro t hdt htZ S X hs hmass hslope
  have ht := hd.trans_le hdt
  have hR₀ := zero_lt_one.trans_le hR
  let H := h*(R^2/t)
  have hgH : g*R ≤ H := by
    change g*R ≤ h*(R^2/t)
    rw [← mul_div_assoc,le_div_iff₀ ht]
    have hgz : g*Z=h := div_mul_cancel₀ _ hZ₀.ne'
    linarith only [mul_le_mul_of_nonneg_left htZ (mul_nonneg hg.le hR₀.le),
      congrArg (fun x => x*R^2) hgz]
  have hH : 1 < H := (show 1 < g*R by linarith only [(div_le_iff₀ hg).mp hR₁]).trans_le hgH
  have hvR : v*R^2 ≤ (g*R)^3 := by
    have hbase := (div_le_iff₀ (pow_pos hg 3)).mp hR₂
    linarith only [mul_le_mul_of_nonneg_right hbase (sq_nonneg R)]
  have hlog := Real.log_le_log (mul_pos (zero_lt_one.trans_le hv) (sq_pos_of_pos hR₀))
    (hvR.trans (pow_le_pow_left₀ (mul_nonneg hg.le hR₀.le) hgH 3))
  rw [Real.log_pow] at hlog
  let Bad := S.filter (fun p => Int.fract (X p) < e)
  let J := range (⌈C*t⌉₊+2)
  let level := fun p : ℕ => (-⌊X p⌋).toNat
  have hneg {p : ℕ} (hp : p ∈ S) : ⌊X p⌋ ≤ 0 := (Int.floor_mono (hs p hp).2.2.2).trans_eq (by norm_num)
  have hcast {p : ℕ} (hp : p ∈ S) : ((level p:ℕ):ℤ) = -⌊X p⌋ := Int.toNat_of_nonneg (neg_nonneg.mpr (hneg hp))
  have hlevels (p : ℕ) (hp : p ∈ Bad) : level p ∈ J := by
    have hp' := (mem_filter.mp hp).1
    have hc := hcast hp'
    have hl : (level p:ℝ) < C*t+1 := by
      have heq : (level p:ℝ) = -(⌊X p⌋:ℝ) := by exact_mod_cast hc
      linarith only [heq,Int.lt_floor_add_one (X p),(hs p hp').2.2.1]
    apply mem_range.mpr
    have hceil := Nat.le_ceil (C*t)
    have hh' : (level p:ℝ) < (⌈C*t⌉₊:ℝ)+2 := by linarith only [hl,hceil]
    exact_mod_cast hh'
  have hsame {p q : ℕ} (hp : p ∈ Bad) (hq : q ∈ Bad) (hj : level p=level q) :
      X q-X p ≤ e := by
    have hfloor : ⌊X p⌋=⌊X q⌋ := by
      have h₁ := hcast (mem_filter.mp hp).1
      rw [hj,hcast (mem_filter.mp hq).1] at h₁
      omega
    have h₁ := Int.floor_add_fract (X p)
    rw [hfloor] at h₁
    linarith only [h₁,Int.floor_add_fract (X q),(mem_filter.mp hq).2,Int.fract_nonneg (X p)]
  have hfiber (j : ℕ) :
      ∑ p ∈ Bad.filter (fun p => level p=j), Real.log p ≤ 876*H := by
    let F := Bad.filter (fun p => level p=j)
    change (∑ p ∈ F, Real.log p) ≤ _
    by_cases hne : F.Nonempty
    · let q := F.min' hne
      have hq : q ∈ F := min'_mem _ _
      obtain ⟨hqB,hqj⟩ := mem_filter.mp hq
      have hqS := (mem_filter.mp hqB).1
      apply thin_prime_mass (a := (q:ℝ)) (Z := v*R^2) (Nat.cast_pos.mpr (hs q hqS).1.pos) hH hlog
      intro p hp
      obtain ⟨hpB,hpj⟩ := mem_filter.mp hp
      have hpS := (mem_filter.mp hpB).1
      have hqp : q ≤ p := min'_le _ p hp
      refine ⟨(hs p hpS).1,by exact_mod_cast hqp,?_,(hs p hpS).2.1⟩
      have hdiff := hslope q hqS p hpS hqp
      dsimp only [H,h]
      linarith only [hdiff,mul_le_mul_of_nonneg_left (hsame hqB hpB (hqj.trans hpj.symm)) (mul_nonneg ha.le (div_nonneg (sq_nonneg R) ht.le))]
    · rw [not_nonempty_iff_eq_empty.mp hne,sum_empty]; positivity
  have hJ : (J.card:ℝ) ≤ D*t := by
    have hCR := mul_nonneg (zero_le_one.trans hC) ht.le
    simp only [J,card_range,Nat.cast_add,Nat.cast_ofNat]
    dsimp only [D]
    linarith only [Nat.ceil_lt_add_one hCR,mul_le_mul_of_nonneg_left hdt (by positivity : 0 ≤ 3/d),div_mul_cancel₀ (3:ℝ) hd.ne']
  have hbad : (∑ p ∈ Bad, Real.log p) ≤ b*R^2/2 := by
    rw [← sum_fiberwise_of_maps_to hlevels (fun p : ℕ => Real.log p)]
    calc _ ≤ ∑ _j ∈ J, 876*H := sum_le_sum (fun j _ => hfiber j)
      _ ≤ D*t*(876*H) := by rw [sum_const,nsmul_eq_mul]; exact mul_le_mul_of_nonneg_right hJ (by positivity)
      _ = 1752*D*a*e*R^2 := by dsimp only [H,h]; field_simp [ht.ne']; ring
      _ ≤ _ := by linarith only [congrArg (fun x => x*R^2) hbudget,mul_nonneg hb.le (sq_nonneg R)]
  have hsub : Bad ⊆ S := filter_subset _ _
  have hsplit := sum_sdiff hsub (f := fun p : ℕ => Real.log p)
  have hgood : b*R^2/2 ≤ ∑ p ∈ S \ Bad, Real.log p := by linarith only [hsplit,hmass,hbad]
  calc e*b/2*R^2 = e*(b*R^2/2) := by ring
    _ ≤ e*∑ p ∈ S \ Bad, Real.log p := mul_le_mul_of_nonneg_left hgood he.le
    _ ≤ ∑ p ∈ S \ Bad, Int.fract (X p)*Real.log p := by
      rw [mul_sum]
      refine sum_le_sum fun p hp => ?_
      obtain ⟨hpS,hpB⟩ := mem_sdiff.mp hp
      have hge : e ≤ Int.fract (X p) := le_of_not_gt fun hlt => hpB (mem_filter.mpr ⟨hpS,hlt⟩)
      exact mul_le_mul_of_nonneg_right hge (Real.log_nonneg (by exact_mod_cast (hs p hpS).1.one_le))
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg sdiff_subset (fun p hp _ =>
      mul_nonneg (Int.fract_nonneg _) (Real.log_nonneg (by exact_mod_cast (hs p hp).1.one_le)))

#print axioms prime_mass_outside_thin_floor_fibers

end GaloisForLFunctions.CountingHolography.Sections
