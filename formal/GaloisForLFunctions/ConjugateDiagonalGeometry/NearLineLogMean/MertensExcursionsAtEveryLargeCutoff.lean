import GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.TheAccumulatedMertensSquareSeesTheZeroWidth
import GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.HowManyMertensPrefixesReachASubcriticalPower
import GaloisForLFunctions.ZeroConfigurationGeometry.HeatStepsNeverShrinkTheMesh
import GaloisForLFunctions.ZeroForcingCalculus.EulerDilationAndRootCoincidenceExclusion

/-!
# Mertens excursions at every large cutoff

Among sets of m positive indices, the largest sum of k^(2a−1) uses
the first m when a ≤ 1/2. An exceptional set with power count d can
therefore carry at most the exponent 2ad in accumulated Mertens
square mass. Strictly below the zero edge the large prefixes must have
counting exponent one at every large cutoff.
-/

noncomputable section
open Finset Filter
open _root_.RHTower GaloisForLFunctions.SquareRootThreshold
namespace GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean

private theorem packed_power {v : ℝ} (hv : 0<v) (hv1 : v ≤ 1)
    (S : Finset ℕ) (hs : ∀ k ∈ S, 1 ≤ k) :
    (∑ k ∈ S, (k:ℝ)^(v-1)) ≤ (1+1/v)*((S.card:ℝ)+1)^v := by
  have sep (k l : ℕ) (hne : k ≠ l) : 1 ≤ |(-(k:ℝ)) - (-(l:ℝ))| := by
    rw [show -(k:ℝ) - -(l:ℝ) = l-k by ring]
    rcases lt_or_gt_of_ne hne with h|h
    · have h' : (k:ℝ)+1 ≤ l := by exact_mod_cast h
      rw [abs_of_nonneg (by linarith)]; linarith
    · have h' : (l:ℝ)+1 ≤ k := by exact_mod_cast h
      rw [abs_of_nonpos (by linarith)]; linarith
  have h := ZeroConfigurationGeometry.sum_le_sum_range_of_sep (fun k : ℕ => -(k:ℝ))
    (μ:=1) zero_le_one S.card S 0 (fun t => t^(v-1)) rfl
    (fun t ht => Real.rpow_nonneg (zero_le_one.trans ht) _)
    (fun x y hx hxy => Real.rpow_le_rpow_of_nonpos (zero_lt_one.trans_le hx) hxy (sub_nonpos.mpr hv1))
    (fun k _ l _ => sep k l) (fun k hk => by simpa using (Nat.one_le_cast (α:=ℝ)).mpr (hs k hk))
  simp only [zero_sub,neg_neg,mul_one] at h
  exact h.trans (ArithmeticGaugeTheory.sum_rpow_sub_one_le hv _)

private theorem mass_on_set {b : ℝ} (hb : 0<b) (hb1 : b ≤ 1/2)
    {A : ℝ} (hA : 0 ≤ A) (S : Finset ℕ) (hs : ∀ k ∈ S, 1 ≤ k)
    (h : ∀ k ∈ S, |shiftedMertensReal k| ≤ A*((k:ℝ)+1)^(1/2+b)) :
    (∑ k ∈ S, mertensSquareCell k) ≤
      (A*2^(1/2+b))^2*(1+1/(2*b))*((S.card:ℝ)+1)^(2*b) := by
  let a := 1/2+b
  have hrow (k : ℕ) (hk : k ∈ S) : mertensSquareCell k ≤ (A*2^a)^2*(k:ℝ)^(2*b-1) := by
    have hk1 := (Nat.one_le_cast (α:=ℝ)).mpr (hs k hk)
    have hp := zero_lt_one.trans_le hk1
    have hh := Real.rpow_le_rpow (by positivity : (0:ℝ)≤k+1) (by linarith : (k:ℝ)+1 ≤ 2*k)
      (by dsimp only [a]; linarith only [hb] : 0 ≤ a)
    rw [Real.mul_rpow (by norm_num : (0:ℝ)≤2) hp.le] at hh
    have hM := (h k hk).trans (mul_le_mul_of_nonneg_left hh hA)
    rw [←mul_assoc] at hM
    have hsquare := pow_le_pow_left₀ (abs_nonneg _) hM 2
    rw [sq_abs,mul_pow,←Real.rpow_natCast ((k:ℝ)^a) 2,←Real.rpow_mul hp.le,
      show a*((2:ℕ):ℝ)=2*b-1+2 by dsimp only [a]; push_cast; ring,
      Real.rpow_add hp,Real.rpow_two] at hsquare
    have weight : (k:ℝ)⁻¹-((k:ℝ)+1)⁻¹ ≤ 1/(k:ℝ)^2 := by
      field_simp [hp.ne',(by positivity : (k:ℝ)+1 ≠ 0)]
      nlinarith only [hp]
    rw [mertensSquareCell,norm_mobiusMertensPartialSum_eq_abs_shiftedMertensReal,sq_abs]
    refine (mul_le_mul_of_nonneg_right weight (sq_nonneg _)).trans ?_
    rw [one_div_mul_eq_div,div_le_iff₀ (sq_pos_of_pos hp)]
    linarith only [hsquare]
  have hsum := sum_le_sum hrow
  rw [←mul_sum] at hsum
  exact hsum.trans ((mul_le_mul_of_nonneg_left
    (packed_power (by positivity : 0<2*b) (by linarith only [hb1]) S hs) (sq_nonneg _)).trans_eq (by
      dsimp only [a]; ring))

/-- Two independent exponents govern the good and exceptional parts
of the Poisson square. Both estimates hold at the same cutoff. -/
theorem mertens_mass_two_population_bound {a b : ℝ} (hb : 0<b) (hb1 : b ≤ 1/2)
    (ha : zetaZeroWidth < a) (ha1 : a ≤ 1/2) (C : ℝ) (hC : 0 ≤ C) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ N : ℕ, mertensSquareMass N ≤
      B*(((N:ℝ)+1)^(2*b)+(((mertensExcursions (1/2+b) C N).card:ℝ)+1)^(2*a)) := by
  classical
  obtain ⟨A,hA,h⟩ := mobiusMertens_subpower_zetaZeroAbscissa (a-zetaZeroWidth) (sub_pos.mpr ha)
  rw [show zetaZeroAbscissa+(a-zetaZeroWidth)=1/2+a by
    rw [zetaZeroWidth_eq_zetaZeroAbscissa_sub_half]; ring] at h
  simp only [norm_mobiusMertensPartialSum_eq_abs_shiftedMertensReal] at h
  let B := (C*2^(1/2+b))^2*(1+1/(2*b))
  let D := (A*2^(1/2+a))^2*(1+1/(2*a))
  have ha0 := zetaZeroWidth_nonneg.trans_lt ha
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  refine ⟨B+D,add_nonneg hB hD,fun N => ?_⟩
  let E := mertensExcursions (1/2+b) C N
  let S := Icc 1 N
  let T := S ∩ E
  have hTS : T ⊆ S := inter_subset_left
  have hgood := mass_on_set hb hb1 hC (S \ T) (fun k hk => (mem_Icc.mp (mem_sdiff.mp hk).1).1)
    (fun k hk => by
      obtain ⟨hk,hn⟩ := mem_sdiff.mp hk
      apply le_of_not_gt
      intro hh
      exact hn (mem_inter.mpr ⟨hk,mem_filter.mpr ⟨mem_range.mpr (Nat.lt_succ_of_le (mem_Icc.mp hk).2),hh⟩⟩)
  have hbad := mass_on_set ha0 ha1 hA T (fun k hk => (mem_Icc.mp (hTS hk)).1) (fun k _ => h k)
  have cg : (S \ T).card ≤ N := by
    have hh := card_le_card (sdiff_subset : S \ T ⊆ S)
    simpa [S,Nat.card_Icc] using hh
  have cb : T.card ≤ E.card := card_le_card inter_subset_right
  have g := Real.rpow_le_rpow (by positivity : 0 ≤ ((S \ T).card:ℝ)+1) (add_le_add_right (Nat.cast_le.mpr cg) 1) (by positivity : 0≤2*b)
  have d := Real.rpow_le_rpow (by positivity : 0 ≤ (T.card:ℝ)+1) (add_le_add_right (Nat.cast_le.mpr cb) 1) (by positivity : 0≤2*a)
  change (∑ k ∈ S, _) ≤ _
  rw [←sum_sdiff hTS]
  change _ ≤ B*_ at hgood
  change _ ≤ D*_ at hbad
  change _ ≤ (B+D)*(((N:ℝ)+1)^(2*b)+((E.card:ℝ)+1)^(2*a))
  linarith only [hgood,hbad,mul_le_mul_of_nonneg_left g hB,mul_le_mul_of_nonneg_left d hD,
    mul_nonneg hD (Real.rpow_nonneg (by positivity : 0 ≤ (N:ℝ)+1) (2*b)),
    mul_nonneg hB (Real.rpow_nonneg (by positivity : 0 ≤ (E.card:ℝ)+1) (2*a))]

/-- At every sufficiently large cutoff, more than K N^d Mertens prefixes
exceed C(n+1)^(1/2+b), whenever 0<b<width and 0<d<1. -/
theorem eventually_many_mertens_excursions {b d : ℝ} (hb : 0<b) (hw : b < zetaZeroWidth)
    (hd : 0<d) (hd1 : d<1) (C K : ℝ) (hC : 0 ≤ C) (hK : 0 ≤ K) :
    ∀ᶠ N : ℕ in atTop, K*((N:ℝ)+1)^d < ((mertensExcursions (1/2+b) C N).card:ℝ) := by
  have hw0 := hb.trans hw
  have hw1 := ZeroForcingCalculus.zetaZeroWidth_le_sub_three_eighths.trans_lt (by norm_num : (8999/24000:ℝ)<1/2)
  have hdiv : zetaZeroWidth < zetaZeroWidth/d :=
    (lt_div_iff₀ hd).mpr (mul_lt_of_lt_one_right hw0 hd1)
  obtain ⟨a,ha,ha'⟩ := exists_between (lt_min hw1 hdiv)
  have ha0 := hw0.trans ha
  let e := max b (d*a)
  have he0 : 0 ≤ e := hb.le.trans (le_max_left _ _)
  have he : e < zetaZeroWidth := max_lt hw (by
    have hh := (lt_div_iff₀ hd).mp (ha'.trans_le (min_le_right _ _))
    linarith only [hh])
  obtain ⟨B,hB,hbound⟩ := mertens_mass_two_population_bound hb (hw.trans hw1).le ha
    (ha'.trans_le (min_le_left _ _)).le C hC
  by_contra hh
  have hf : ∃ᶠ N : ℕ in atTop, ((mertensExcursions (1/2+b) C N).card:ℝ) ≤ K*((N:ℝ)+1)^d := by
    simpa only [not_eventually,not_lt] using hh
  apply he.not_ge
  apply width_le_of_sparse_mertens_square_mass he0
  refine ⟨B*(1+(K+1)^(2*a))*2^(2*e),by positivity,?_⟩
  apply (hf.and_eventually (eventually_ge_atTop 1)).mono
  intro N hN
  have hn := (Nat.one_le_cast (α:=ℝ)).mpr hN.2
  have nx := zero_lt_one.trans_le hn
  let X := (N:ℝ)+1
  have hx : 1 ≤ X := by dsimp only [X]; linarith only [hn]
  have xp := zero_lt_one.trans_le hx
  let m := ((mertensExcursions (1/2+b) C N).card:ℝ)
  have hm : m+1 ≤ (K+1)*X^d := by
    have hconst := Real.one_le_rpow hx hd.le
    have hsize : m ≤ K*X^d := hN.1
    linarith only [hsize,hconst]
  have high := Real.rpow_le_rpow (by dsimp only [m]; positivity : 0≤m+1) hm (by positivity : 0≤2*a)
  rw [Real.mul_rpow (by positivity : 0≤K+1) (Real.rpow_nonneg xp.le _),←Real.rpow_mul xp.le] at high
  have hh' := Real.rpow_le_rpow_of_exponent_le hx (by linarith only [le_max_right b (d*a)] : d*(2*a) ≤ 2*e)
  have low := Real.rpow_le_rpow_of_exponent_le hx (by linarith only [le_max_left b (d*a)] : 2*b ≤ 2*e)
  have step : mertensSquareMass N ≤ B*((1+(K+1)^(2*a))*X^(2*e)) := by
    apply (hbound N).trans
    apply mul_le_mul_of_nonneg_left _ hB
    change X^(2*b)+(m+1)^(2*a) ≤ _
    linarith only [low,high,mul_le_mul_of_nonneg_left hh' (Real.rpow_nonneg (by positivity : 0≤K+1) _)]
  have hscale := Real.rpow_le_rpow xp.le (by dsimp only [X]; linarith only [hn] : X≤2*N) (by positivity : 0≤2*e)
  rw [Real.mul_rpow (by norm_num : (0:ℝ)≤2) nx.le] at hscale
  exact step.trans ((mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hscale (by positivity : 0≤1+(K+1)^(2*a))) hB).trans_eq (by ring))

#print axioms mertens_mass_two_population_bound
#print axioms eventually_many_mertens_excursions
end GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean
