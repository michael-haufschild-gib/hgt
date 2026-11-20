import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.CountingIntegerPowerComparisonsOnTheGcdGrid
import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.TheGcdDeficitAtTheEighthPowerEndpoints

/-!
# Distribution of the eighth-power gcd shortfalls

For all octave endpoints M ≥ m⁸ the normalized shortfall at horizon mM
is 1/(2m) with a uniform power-saving error. Inverting this estimate
counts exact integer comparisons up to K, even when each row uses a
different exponent. The change from the full prefix to a truncated
prefix occurs at j/(2 log 2).
-/

noncomputable section
open Finset Filter Topology
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

private theorem count_bracket (S : Finset ℕ) {K M : ℕ} (hS : S ⊆ Icc 1 K)
    {b Δ : ℝ} (hΔ : 0 ≤ Δ) (hb : 0 ≤ b)
    (hlo : ∀ m ∈ Icc 1 K, M ≤ m → (m:ℝ) ≤ b-Δ → m ∈ S)
    (hhi : ∀ m ∈ S, M ≤ m → (m:ℝ) ≤ b+Δ) :
    |(S.card:ℝ)-min (K:ℝ) b| ≤ M+1+Δ := by
  let L := Icc 1 (min K ⌊b-Δ⌋₊)
  let U := Icc 1 (min K ⌊b+Δ⌋₊)
  have ls : L ⊆ S ∪ range M := by
    intro m hm
    obtain ⟨hm₁,hmk⟩ := mem_Icc.mp hm
    rcases le_or_gt M m with h | h
    · have hpos : 0 < ⌊b-Δ⌋₊ := hm₁.trans (hmk.trans (min_le_right ..))
      exact mem_union_left _ (hlo m (mem_Icc.mpr ⟨hm₁,hmk.trans (min_le_left ..)⟩) h
        ((Nat.le_floor_iff ((Nat.floor_pos.mp hpos).trans' zero_le_one)).mp (hmk.trans (min_le_right ..))))
    · exact mem_union_right _ (mem_range.mpr h)
  have su : S ⊆ U ∪ range M := by
    intro m hm
    obtain ⟨hm₁,hmk⟩ := mem_Icc.mp (hS hm)
    rcases le_or_gt M m with h | h
    · exact mem_union_left _ (mem_Icc.mpr ⟨hm₁,le_min hmk (Nat.le_floor (hhi m hm h))⟩)
    · exact mem_union_right _ (mem_range.mpr h)
  have hl := (card_le_card ls).trans (card_union_le ..)
  have hu := (card_le_card su).trans (card_union_le ..)
  simp only [L,U,Nat.card_Icc,Nat.add_sub_cancel,card_range] at hl hu
  have hl' : min (K:ℝ) (⌊b-Δ⌋₊:ℝ) ≤ S.card+M := by exact_mod_cast hl
  have hu' : (S.card:ℝ) ≤ min (K:ℝ) (⌊b+Δ⌋₊:ℝ)+M := by exact_mod_cast hu
  have hleft : min (K:ℝ) b ≤ min (K:ℝ) (⌊b-Δ⌋₊:ℝ)+(1+Δ) := by
    rw [←min_add_add_right]
    exact min_le_min (by linarith only [hΔ]) (by linarith only [(Nat.lt_floor_add_one (b-Δ)).le])
  have hright : min (K:ℝ) (⌊b+Δ⌋₊:ℝ) ≤ min (K:ℝ) b+Δ := by
    rw [←min_add_add_right]
    exact min_le_min (by linarith only [hΔ]) (Nat.floor_le (add_nonneg hb hΔ))
  exact abs_le.mpr ⟨by linarith only [hleft,hl'],by linarith only [hright,hu']⟩

/-- A rank with a power-saving limit has an inverse distribution with
the same power saving, even when the observation endpoint moves. -/
private theorem count_scaled_scores {b δ : ℝ} (hb : 0 < b) (hδ : 0 < δ)
    (hδ₁ : δ ≤ 1) {C : ℝ} (hC : 0 ≤ C) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (f : ℕ → ℝ), (∀ m : ℕ, 2 ≤ m → |f m-b| ≤ C*(m:ℝ)^(-δ)) →
      ∀ K j : ℕ, 0 < j →
      |(((Icc 1 K).filter fun m : ℕ => (m:ℝ) ≤ j*f m).card:ℝ)-min (K:ℝ) (b*j)| ≤
        A*(j:ℝ)^(1-δ) := by
  let c := b/2
  have hc : 0 < c := half_pos hb
  have hlim : Tendsto (fun m : ℕ => C*(m:ℝ)^(-δ)) atTop (𝓝 0) := by
    simpa [Function.comp_def] using ((tendsto_rpow_neg_atTop hδ).comp tendsto_natCast_atTop_atTop).const_mul C
  obtain ⟨M,hM⟩ := eventually_atTop.mp ((hlim.eventually_lt_const hc).and (eventually_ge_atTop 2))
  let D := C*c^(-δ)
  have hD : 0 ≤ D := mul_nonneg hC (Real.rpow_nonneg hc.le _)
  refine ⟨M+1+D,by positivity,fun f hf K j hj => ?_⟩
  let x : ℝ := j
  have hx : 0 < x := Nat.cast_pos.mpr hj
  have hx₁ : 1 ≤ x := Nat.one_le_cast.mpr hj
  let e := D*x^(1-δ)
  have he : 0 ≤ e := mul_nonneg hD (Real.rpow_nonneg hx.le _)
  have hbase {m : ℕ} (hm : M ≤ m) : c ≤ f m := by
    have H := (abs_le.mp (hf m (hM m hm).2)).1
    have H' := (hM m hm).1
    change C*(m:ℝ)^(-δ) < b/2 at H'
    change b/2 ≤ f m
    linarith only [H,H']
  have htight {m : ℕ} (hm : M ≤ m) (hfar : c*x ≤ m) :
      |x*f m-b*x| ≤ e := by
    have hw := Real.rpow_le_rpow_of_nonpos (mul_pos hc hx) hfar (neg_nonpos.mpr hδ.le)
    rw [Real.mul_rpow hc.le hx.le] at hw
    have h := (hf m (hM m hm).2).trans (mul_le_mul_of_nonneg_left hw hC)
    have heq : x*x^(-δ)=x^(1-δ) := by
      rw [sub_eq_add_neg,Real.rpow_add hx,Real.rpow_one]
    rw [show x*f m-b*x=x*(f m-b) by ring,abs_mul,abs_of_pos hx]
    exact (mul_le_mul_of_nonneg_left h hx.le).trans_eq (by dsimp only [e,D]; rw [←heq]; ring)
  let S := (Icc 1 K).filter fun m : ℕ => (m:ℝ) ≤ j*f m
  have hl (m : ℕ) (hm : m ∈ Icc 1 K) (hM : M ≤ m) (hsmall : (m:ℝ) ≤ b*x-e) : m ∈ S := by
    refine mem_filter.mpr ⟨hm,?_⟩
    change (m:ℝ) ≤ x*f m
    rcases le_or_gt (m:ℝ) (c*x) with h | h
    · exact h.trans ((mul_comm c x).le.trans (mul_le_mul_of_nonneg_left (hbase hM) hx.le))
    · linarith only [hsmall,(abs_le.mp (htight hM h.le)).1]
  have hu (m : ℕ) (hm : m ∈ S) (hM : M ≤ m) : (m:ℝ) ≤ b*x+e := by
    have hh := (mem_filter.mp hm).2
    rcases le_or_gt (m:ℝ) (c*x) with h | h
    · dsimp only [c] at h
      linarith only [h,he,mul_nonneg hb.le hx.le]
    · linarith only [hh,(abs_le.mp (htight hM h.le)).2]
  have H := count_bracket S (filter_subset _ _) he (mul_nonneg hb.le hx.le) hl hu
  have H' := mul_le_mul_of_nonneg_left (Real.one_le_rpow hx₁ (sub_nonneg.mpr hδ₁))
    (show (0:ℝ) ≤ M+1 by positivity)
  exact H.trans (by dsimp only [e]; linarith only [H'])

/-- A single error constant works even when the lower endpoint M changes
from row to row, arbitrarily far above the eighth power. -/
theorem uniform_sparse_gcd_half_step {δ : ℝ} (hδ : 0 < δ) (h₁ : δ < 1/3000) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {m M : ℕ}, 2 ≤ m → m^8 ≤ M →
      |Real.log 2-Real.log (octaveGcdProduct M (m*M))/((m:ℝ)*M)-1/(2*(m:ℝ))| ≤
        C*(m:ℝ)^(-1-δ) := by
  let t := 1-(1+δ)/8
  have ht : _root_.RHTower.zeroReSup < t :=
    GaloisForLFunctions.ExceptionalLayerTheory.zeroReSup_le_sub_seven_eighths.trans_lt (by
      dsimp only [t]; linarith only [h₁])
  obtain ⟨B,hB,H⟩ := gcd_product_density_above_zero_width ht
  refine ⟨20+B,by positivity,?_⟩
  intro m M hm hsize
  have hm₁ : 1 ≤ m := by omega
  have hmr : (1:ℝ) ≤ m := Nat.one_le_cast.mpr hm₁
  have hp : 0 < (m:ℝ) := zero_lt_one.trans_le hmr
  have hM := (one_le_pow₀ hm₁ (n:=8)).trans hsize
  have hh := Real.rpow_le_rpow_of_nonpos (pow_pos hp 8)
    (show (m:ℝ)^8 ≤ M by exact_mod_cast hsize) (show t-1 ≤ 0 by dsimp [t]; linarith only [hδ])
  rw [←Real.rpow_natCast (m:ℝ) 8,←Real.rpow_mul hp.le,Nat.cast_ofNat,
    show 8*(t-1) = -1-δ by dsimp only [t]; ring] at hh
  have hg := (H hM hm₁).trans (mul_le_mul_of_nonneg_left hh hB)
  have hs := Real.rpow_le_rpow_of_exponent_le hmr (by linarith only [h₁] : (-2:ℝ) ≤ -1-δ)
  rw [show (-2:ℝ) = -(2:ℝ) by norm_num,Real.rpow_neg hp.le,Real.rpow_two] at hs
  have hc := cofactor_density_half_step hm
  rw [div_eq_mul_inv (20:ℝ)] at hc
  let P := Real.log (octaveGcdProduct M (m*M))/((m:ℝ)*M)
  change |P-cofactorIntervalDensity m| ≤ _ at hg
  change |Real.log 2-P-1/(2*(m:ℝ))| ≤ _
  rw [show Real.log 2-P-1/(2*(m:ℝ))=(Real.log 2-cofactorIntervalDensity m-1/(2*(m:ℝ)))-
    (P-cofactorIntervalDensity m) by ring]
  exact (abs_sub ..).trans ((add_le_add (hc.trans (mul_le_mul_of_nonneg_left hs
    (by norm_num : (0:ℝ) ≤ 20))) hg).trans_eq (by ring))

/-- Integer cuts for an exponent that can change independently in each row. -/
def variableGcdPowerFailures (r : ℕ → ℕ) (K j : ℕ) : Finset ℕ :=
  (Icc 1 K).filter fun m => (octaveGcdProduct (m^(r m)) (m^(r m+1)))^j ≤ 2^((j-1)*m^(r m+1))

/-- The main term and power-saving error hold uniformly over every
choice of exponents at least eight, including choices depending on K or j. -/
theorem variable_gcd_power_failure_distribution {δ : ℝ} (hδ : 0 < δ) (h₁ : δ < 1/3000) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ r : ℕ → ℕ, (∀ m, 8 ≤ r m) → ∀ K j : ℕ, 0 < j →
      |((variableGcdPowerFailures r K j).card:ℝ)-min (K:ℝ) ((j:ℝ)/(2*Real.log 2))| ≤
        A*(j:ℝ)^(1-δ) := by
  let L := Real.log 2
  have hL : 0 < L := Real.log_pos (by norm_num)
  let b := 1/(2*L)
  have hb : 0 < b := by dsimp only [b]; positivity
  obtain ⟨C,hC,hs⟩ := uniform_sparse_gcd_half_step hδ h₁
  obtain ⟨A,hA,H⟩ := count_scaled_scores hb hδ (by linarith only [h₁]) (div_nonneg hC hL.le)
  refine ⟨A,hA,fun r hr => ?_⟩
  let f (m : ℕ) := (m:ℝ)*gcdRowDeficit (r m) m/L
  have hf (m : ℕ) (hm : 2 ≤ m) : |f m-b| ≤ C/L*(m:ℝ)^(-δ) := by
    have hm' : 0 < (m:ℝ) := by exact_mod_cast (show 0 < m by omega)
    let a := L-Real.log (octaveGcdProduct (m^(r m)) (m^(r m+1)))/(m:ℝ)^(r m+1)
    have ha : |a-1/(2*(m:ℝ))| ≤ C*(m:ℝ)^(-1-δ) := by
      have h := hs hm (Nat.pow_le_pow_right (by omega : 0 < m) (hr m))
      simpa only [Nat.cast_pow,←pow_succ',a,L] using h
    have hp : 0 ≤ 1/(2*(m:ℝ)) := by positivity
    have hplus : |max a 0-1/(2*(m:ℝ))| ≤ C*(m:ℝ)^(-1-δ) := by
      rcases le_or_gt 0 a with h | h
      · simpa [max_eq_left h] using ha
      · rw [max_eq_right h.le,zero_sub,abs_neg,abs_of_nonneg hp]
        linarith only [(abs_le.mp ha).1,h.le]
    have hx : f m-b = ((m:ℝ)/L)*(max a 0-1/(2*(m:ℝ))) := by
      change (m:ℝ)*max a 0/L-1/(2*L)=_
      field_simp
    rw [hx,abs_mul,abs_of_pos (div_pos hm' hL)]
    have h := mul_le_mul_of_nonneg_left hplus (div_nonneg hm'.le hL.le)
    have he : (m:ℝ)*(m:ℝ)^(-1-δ)=(m:ℝ)^(-δ) := by
      rw [show -δ=1+(-1-δ) by ring,Real.rpow_add hm',Real.rpow_one]
    exact h.trans_eq (by rw [←he]; ring)
  intro K j hj
  have he : variableGcdPowerFailures r K j = (Icc 1 K).filter fun m : ℕ => (m:ℝ) ≤ j*f m := by
    ext m
    rw [variableGcdPowerFailures,mem_filter,mem_filter]
    apply and_congr_right
    intro hm
    rw [gcd_power_failure_iff (r m) (mem_Icc.mp hm).1 hj]
    have hm₀ : 0 < (m:ℝ) := Nat.cast_pos.mpr (mem_Icc.mp hm).1
    have hj₀ : 0 < (j:ℝ) := Nat.cast_pos.mpr hj
    change L/j ≤ gcdRowDeficit (r m) m ↔ (m:ℝ) ≤ j*(m*gcdRowDeficit (r m) m/L)
    rw [div_le_iff₀ hj₀,←mul_div_assoc,le_div_iff₀ hL]
    rw [show (j:ℝ)*(m*gcdRowDeficit (r m) m)=(m:ℝ)*(gcdRowDeficit (r m) m*j) by ring]
    exact (mul_le_mul_iff_right₀ hm₀).symm
  rw [he,show (j:ℝ)/(2*Real.log 2)=b*j by dsimp only [b,L]; ring]
  exact H f hf K j hj

/-- The number of failed integer comparisons on the eighth/ninth-power
grid is min(K,j/(2 log 2)) up to O(j^(1-δ)), uniformly in K. -/
theorem eighth_gcd_power_failure_distribution {δ : ℝ} (hδ : 0 < δ) (h₁ : δ < 1/3000) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ K j : ℕ, 0 < j →
      |((gcdPowerFailures 8 K j).card:ℝ)-min (K:ℝ) ((j:ℝ)/(2*Real.log 2))| ≤ A*(j:ℝ)^(1-δ) := by
  obtain ⟨A,hA,H⟩ := variable_gcd_power_failure_distribution hδ h₁
  exact ⟨A,hA,H (fun _ => 8) (fun _ => le_rfl)⟩

private theorem scaled_failure_error {δ : ℝ} (hδ : 0 < δ) (h₁ : δ < 1/3000) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ K j : ℕ, 0 < j →
      |((gcdPowerFailures 8 K j).card:ℝ)/j-min ((K:ℝ)/j) (1/(2*Real.log 2))| ≤
        A*(j:ℝ)^(-δ) := by
  obtain ⟨A,hA,H⟩ := eighth_gcd_power_failure_distribution hδ h₁
  refine ⟨A,hA,fun K j hj => ?_⟩
  have hj' : 0 < (j:ℝ) := Nat.cast_pos.mpr hj
  have he : (1:ℝ)/(2*Real.log 2)=((j:ℝ)/(2*Real.log 2))/j := by
    field_simp
  rw [he,min_div_div_right hj'.le,←sub_div,abs_div,abs_of_pos hj',div_le_iff₀ hj']
  have hpow : (j:ℝ)^(1-δ)=(j:ℝ)^(-δ)*j := by
    rw [show 1-δ=(-δ)+1 by ring,Real.rpow_add hj',Real.rpow_one]
  simpa only [hpow,mul_assoc] using H K j hj

/-- Along any observation horizon with K/j tending to t, the limiting
number of failed tests per unit threshold is min(t,1/(2 log 2)). -/
theorem eighth_gcd_failure_scaling_limit (K : ℕ → ℕ) {t : ℝ}
    (hK : Tendsto (fun j : ℕ => (K j:ℝ)/j) atTop (𝓝 t)) :
    Tendsto (fun j : ℕ => ((gcdPowerFailures 8 (K j) j).card:ℝ)/j) atTop
      (𝓝 (min t (1/(2*Real.log 2)))) := by
  let δ : ℝ := 1/6000
  obtain ⟨A,_,H⟩ := scaled_failure_error (δ:=δ) (by norm_num [δ]) (by norm_num [δ])
  let b : ℝ := 1/(2*Real.log 2)
  have hz : Tendsto (fun j : ℕ => A*(j:ℝ)^(-δ)) atTop (𝓝 0) := by
    simpa [Function.comp_def] using ((tendsto_rpow_neg_atTop (show 0 < δ by norm_num [δ])).comp
      tendsto_natCast_atTop_atTop).const_mul A
  have he : Tendsto (fun j : ℕ => ((gcdPowerFailures 8 (K j) j).card:ℝ)/j-min ((K j:ℝ)/j) b)
      atTop (𝓝 0) := squeeze_zero_norm' ((eventually_ge_atTop 1).mono fun j hj => by
        simpa only [Real.norm_eq_abs] using H (K j) j hj) hz
  simpa only [Pi.add_apply,sub_add_cancel,zero_add] using
    he.add (hK.min (tendsto_const_nhds (x:=b)))

/-- Weak counts stay uniformly bounded after division by j, although
the sum of the deficits on this same arithmetic grid tends to infinity. -/
theorem eighth_gcd_bounded_counts_and_divergent_mass :
    (∃ B : ℝ, ∀ K j : ℕ, 0 < j → ((gcdPowerFailures 8 K j).card:ℝ)/j ≤ B) ∧
      Tendsto (powerGridGcdDeficit 8) atTop atTop := by
  let δ : ℝ := 1/6000
  obtain ⟨A,hA,H⟩ := scaled_failure_error (δ:=δ) (by norm_num [δ]) (by norm_num [δ])
  constructor
  · refine ⟨1/(2*Real.log 2)+A,fun K j hj => ?_⟩
    have hw := Real.rpow_le_one_of_one_le_of_nonpos (Nat.one_le_cast.mpr hj : (1:ℝ) ≤ j)
      (show -δ ≤ 0 by norm_num [δ])
    linarith only [(abs_le.mp (H K j hj)).2,min_le_right ((K:ℝ)/j) (1/(2*Real.log 2)),
      mul_le_mul_of_nonneg_left hw hA]
  · obtain ⟨c,hc⟩ := eighth_gcd_deficit_centered_converges
    have hl := (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).const_mul_atTop
      (show 0 < (1/2:ℝ) by norm_num)
    simpa only [Function.comp_apply,Pi.add_apply,sub_add_cancel] using hc.add_atTop hl

#print axioms variable_gcd_power_failure_distribution
#print axioms eighth_gcd_power_failure_distribution
#print axioms eighth_gcd_failure_scaling_limit
#print axioms eighth_gcd_bounded_counts_and_divergent_mass

end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
