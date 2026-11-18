import GaloisForLFunctions.CountingHolography.Sections.ThePrimeProfileOfThreeSquareConductors
import GaloisForLFunctions.CountingHolography.Sections.ANegativePrimeWindowAtEveryMultiplicity

/-!
# The numerator above square-root multiplicity

Primes in a fixed relative neighborhood of the middle square have positive
contact of order one over the conductor parameter. The mesh resolves this
whole band once the squared multiplicity exceeds a constant times that
parameter. On the diagonal the numerator alone has cubic logarithmic growth.
-/

noncomputable section
namespace GaloisForLFunctions.CountingHolography.Sections

open Finset Filter Topology ArithmeticFunction AbsoluteGeometryOfSpecZ

private theorem contact_in_middle_band :
    ∃ F c C : ℝ, 1 < F ∧ F ≤ 2 ∧ 0 < c ∧ 1 ≤ C ∧
      ∀ᶠ n : ℕ in atTop, ∀ {m k : ℕ}, C*n ≤ (m:ℝ)^2 →
        (n:ℝ)^2 < k → (k:ℝ) ≤ F*(n:ℝ)^2 →
        c*(m:ℝ)^2/n ≤
          (⌊contactMultiplicity (packet (m • successorSquareTriple n)) (3*windowEnd ((2*n+1)^2+1))
            (resolution (m • successorSquareTriple n)) k⌋₊ : ℝ) := by
  obtain ⟨δ,c,hδ,_,hc,hband⟩ := successorSquare_positive_band
  obtain ⟨E,hE,hmesh⟩ := contactMultiplicity_uniform_error
  let F := min (Real.exp δ) 2
  let C := max 1 (4/c)
  let M := 2*E/c
  have hM : 0 ≤ M := div_nonneg (by positivity) hc.le
  have hF : 1 < F := lt_min (Real.one_lt_exp_iff.mpr hδ) one_lt_two
  have hC : 1 ≤ C := le_max_left _ _
  have hninf := (tendsto_pow_atTop (α := ℝ) two_ne_zero).comp tendsto_natCast_atTop_atTop
  refine ⟨F,c/4,C,hF,min_le_right _ _,by positivity,hC,?_⟩
  filter_upwards [eventually_ge_atTop ⌈M^2⌉₊,eventually_ge_atTop 1,
    hninf.eventually_gt_atTop (Real.exp (8+Real.log 9))] with n hNM hn hcut
  intro m k hmn hk hkF
  let r := resolution (m • successorSquareTriple n)
  let L := 3*windowEnd ((2*n+1)^2+1)
  let d := successorSquareTriple n
  have hn' : (0:ℝ) < n := Nat.cast_pos.mpr hn
  have hk' : (0:ℝ) < k := (sq_pos_of_pos hn').trans hk
  have hm2 : (n:ℝ) ≤ (m:ℝ)^2 := (by simpa only [one_mul] using
    mul_le_mul_of_nonneg_right hC hn'.le : (n:ℝ) ≤ C*n).trans hmn
  have hm' : 0 < m := by by_contra! hz; have h0 : m = 0 := Nat.eq_zero_of_le_zero hz; simp [h0] at hm2; linarith
  have hr := successorSquare_resolution_ge n m
  have hr' : (m:ℝ) ≤ r := by exact_mod_cast hr
  have hrpos : 0 < r := hm'.trans_le hr
  have hMr : M ≤ (r:ℝ) := by
    have hMM : M^2 ≤ (n:ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hNM)
    exact (le_of_pow_le_pow_left₀ two_ne_zero (Nat.cast_nonneg (α := ℝ) m) (hMM.trans hm2)).trans hr'
  have hE' : E/r ≤ c/2 := by
    apply (div_le_iff₀ (Nat.cast_pos.mpr hrpos)).mpr
    have hmrc := (div_le_iff₀ hc).mp hMr
    linarith only [hmrc]
  have hl : 8+Real.log 9 < Real.log k :=
    (Real.lt_log_iff_exp_lt hk').mpr (hcut.trans hk)
  have hg : |Real.log ((n:ℝ)^2)-Real.log k| ≤ δ := by
    rw [abs_of_nonpos (sub_nonpos.mpr (Real.log_le_log (sq_pos_of_pos hn') hk.le))]
    have hh := Real.log_le_log hk' (hkF.trans
      (mul_le_mul_of_nonneg_right (min_le_left _ _) (sq_nonneg _)))
    rw [Real.log_mul (Real.exp_pos _).ne' (sq_pos_of_pos hn').ne',Real.log_exp] at hh
    linarith only [hh]
  have hprof := hband hn hl hg
  have hs := (abs_le.mp (hmesh _ d (successorSquareTriple_mass n) hrpos (Nat.cast_pos.mp hk'))).1
  have hsqrt := Real.sqrt_pos.mpr hk'
  have hsample : c/Real.sqrt k ≤ contactMultiplicity (packet d) L r k := by
    have hmul := mul_le_mul_of_nonneg_left hE' (by positivity : 0 ≤ 2/Real.sqrt k)
    change -(2/Real.sqrt k*(E/r)) ≤ contactMultiplicity (packet d) L r k-integratedContact d k at hs
    linarith only [hs,hprof,hmul]
  have hk2 : Real.sqrt k ≤ 2*n := by
    apply (Real.sqrt_le_iff).mpr
    refine ⟨by positivity,?_⟩
    exact hkF.trans ((mul_le_mul_of_nonneg_right (min_le_right _ _) (sq_nonneg _)).trans
      (by nlinarith only [sq_nonneg (n:ℝ)]))
  have hraw : c*(m:ℝ)^2/(2*n) ≤ contactMultiplicity (packet (m • d)) L r k := by
    rw [packet_smul,contactMultiplicity_scale]
    have hh := (div_le_div_of_nonneg_left hc.le hsqrt hk2).trans hsample
    exact (le_of_eq (by ring)).trans (mul_le_mul_of_nonneg_left hh (sq_nonneg (m:ℝ)))
  have htwo : 2 ≤ c*(m:ℝ)^2/(2*n) := by
    apply (le_div_iff₀ (mul_pos two_pos hn')).mpr
    have hh := (mul_le_mul_of_nonneg_right (le_max_right 1 (4/c)) hn'.le).trans hmn
    have hh' := mul_le_mul_of_nonneg_left hh hc.le
    have he : c*((4/c)*n) = 4*n := by field_simp
    rw [he] at hh'
    linarith only [hh']
  let z := contactMultiplicity (packet (m • d)) L r k
  have hz := Nat.lt_floor_add_one z
  change c/4*(m:ℝ)^2/n ≤ (⌊z⌋₊:ℝ)
  change c*(m:ℝ)^2/(2*n) ≤ z at hraw
  have hid : c/4*(m:ℝ)^2/n = (c*(m:ℝ)^2/(2*n))/2 := by ring
  rw [hid]
  linarith only [hz,hraw,htwo]

/-- For all large conductors the reduced numerator has log at least a
constant times n m² throughout the range m² ≥ C n. -/
theorem successorSquare_numerator_lower :
    ∃ c C : ℝ, 0 < c ∧ 1 ≤ C ∧ ∀ᶠ n : ℕ in atTop, ∀ {m : ℕ}, C*n ≤ (m:ℝ)^2 →
      c*n*(m:ℝ)^2 ≤ Real.log (ordinaryPrimeGenerator (m • successorSquareTriple n)).num.natAbs := by
  obtain ⟨F,c,C,hF,hF',hc,hC,hmid⟩ := contact_in_middle_band
  have hinf := (tendsto_pow_atTop (α := ℝ) two_ne_zero).comp tendsto_natCast_atTop_atTop
  have hmass := hinf.eventually (proportional_prime_mass (u := 1) one_pos hF)
  refine ⟨c*((F-1)/2),C,mul_pos hc (half_pos (sub_pos.mpr hF)),hC,?_⟩
  filter_upwards [hmid,hmass,eventually_ge_atTop 1] with n hband hsum hn
  intro m hmn
  let U := (Ioc ⌊(n:ℝ)^2⌋₊ ⌊F*(n:ℝ)^2⌋₊).filter Nat.Prime
  let L := 3*windowEnd ((2*n+1)^2+1)
  let S := (Icc 2 L).filter Nat.Prime
  let d := m • successorSquareTriple n
  let v := fun k : ℕ => (⌊contactMultiplicity (packet d) L (resolution d) k⌋₊ : ℝ)
  let A := c*(m:ℝ)^2/n
  have hA : 0 ≤ A := by unfold A; positivity
  have hn' : (0:ℝ) < n := Nat.cast_pos.mpr hn
  have hmem {k : ℕ} (hk : k ∈ U) : k.Prime ∧ (n:ℝ)^2 < k ∧ (k:ℝ) ≤ F*(n:ℝ)^2 := by
    obtain ⟨h,hp⟩ := mem_filter.mp hk
    obtain ⟨hl,hu⟩ := mem_Ioc.mp h
    exact ⟨hp,(Nat.floor_lt (sq_nonneg _)).mp hl,
      (Nat.cast_le.mpr hu).trans (Nat.floor_le (mul_nonneg (zero_le_one.trans hF.le) (sq_nonneg _)))⟩
  have hs : U ⊆ S := by
    intro k hk
    obtain ⟨hp,_,hu⟩ := hmem hk
    have hW := successorSquareWindowScale_bounds n
    have hb : (k:ℝ) ≤ 3*(windowEnd ((2*n+1)^2+1):ℝ) := by
      have hnn := hW.1.trans hW.2.2
      linarith only [hu,mul_le_mul_of_nonneg_right hF' (sq_nonneg (n:ℝ)),hnn,
        Nat.cast_nonneg (α := ℝ) (windowEnd ((2*n+1)^2+1))]
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨hp.two_le,by exact_mod_cast hb⟩,hp⟩
  have hh : (F-1)/2*(n:ℝ)^2 ≤ ∑ k ∈ U, Real.log k := by simpa only [one_mul,Function.comp_apply,U] using hsum
  rw [ordinaryPrimeGenerator_num,log_ordinaryPrimeModulus]
  calc c*((F-1)/2)*n*(m:ℝ)^2 = A*((F-1)/2*(n:ℝ)^2) := by unfold A; field_simp
    _ ≤ A*∑ k ∈ U, Real.log k := mul_le_mul_of_nonneg_left hh hA
    _ ≤ ∑ k ∈ U, v k*vonMangoldt k := by
      rw [mul_sum]
      refine sum_le_sum fun k hk => ?_
      obtain ⟨hp,hl,hu⟩ := hmem hk
      have he : Real.log k = vonMangoldt k := by
        rw [← log_contactBase,contactBase,if_pos hp.isPrimePow,hp.minFac_eq]
      rw [he]
      exact mul_le_mul_of_nonneg_right (hband hmn hl hu) vonMangoldt_nonneg
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg hs fun k _ _ =>
      mul_nonneg (Nat.cast_nonneg _) vonMangoldt_nonneg

#print axioms successorSquare_numerator_lower

end GaloisForLFunctions.CountingHolography.Sections
