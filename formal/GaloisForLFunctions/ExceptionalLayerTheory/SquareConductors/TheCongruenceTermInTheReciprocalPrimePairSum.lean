import GaloisForLFunctions.BezoutValuationIncidence.HardyLittlewoodSingularSeriesOfTheDampedSource
import GaloisForLFunctions.ExceptionalLayerTheory.CancellationOnRepeatedPrimeFactors
import GaloisForLFunctions.ExceptionalLayerTheory.FiniteDilationsOfArithmeticKernels

/-!
# The sign of the local prime-pair prediction at every gap endpoint

Inserting one prime into the pair singular series takes a convex
combination of two prefix counts. The new endpoint term is the actual
Euclidean remainder. Summing by parts retains the sign for the
reciprocal weight on all distinct partners of an integer.
-/

noncomputable section

open Finset Filter Topology
open GaloisForLFunctions.BezoutValuationIncidence
open GaloisForLFunctions.BiScaleUncertainty GaloisForLFunctions.TransHorizonIncidenceMechanics
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

/-- The normalized pair density from the specified primes. -/
def finitePairDensity (S : Finset Nat.Primes) (h : ℕ) : ℝ :=
  ∏ p ∈ S, (1+ramanujanLagWeight h p/((p:ℝ)-1)^2)

/-- Missing local pair density through the last included positive gap. -/
def localGapDeficit (S : Finset Nat.Primes) (H : ℕ) : ℝ :=
  H-∑ h ∈ Ioc 0 H,finitePairDensity S h

private theorem density_at_new_multiple {S : Finset Nat.Primes} {p : Nat.Primes}
    (hp : p∉S) (h : ℕ) : finitePairDensity S (p*h)=finitePairDensity S h := by
  apply prod_congr rfl
  intro l hl
  have hne : (l:ℕ)≠p := fun e => hp (Subtype.ext e ▸ hl)
  have hn : ¬(l:ℕ)∣p := fun hd => hne ((Nat.prime_dvd_prime_iff_eq l.prop p.prop).mp hd)
  simp only [BezoutValuationIncidence.ramanujanLagWeight_prime l.prop, l.prop.dvd_mul,hn,false_or]

/-- The prime divides a gap with excess weight exactly when it
divides the integer endpoint. Its terminal cost is the Euclidean remainder. -/
theorem local_gap_deficit_insert {S : Finset Nat.Primes} {p : Nat.Primes} (hp : p∉S) (H : ℕ) :
    let t : ℝ := 1/((p:ℝ)-1)^2
    localGapDeficit (insert p S) H =
      (1-t)*localGapDeficit S H + t*((p:ℝ)*localGapDeficit S (H/p)+(H%p:ℕ)) := by
  let t : ℝ := 1/((p:ℝ)-1)^2
  have hs (h : ℕ) : finitePairDensity (insert p S) h =
      (1-t)*finitePairDensity S h + (t*p)*(if (p:ℕ)∣h then finitePairDensity S h else 0) := by
    rw [finitePairDensity,prod_insert hp,BezoutValuationIncidence.ramanujanLagWeight_prime p.prop]
    change (1+((if (p:ℕ)∣h then (p:ℝ) else 0)-1)/((p:ℝ)-1)^2)*finitePairDensity S h=_
    dsimp only [t]
    split_ifs <;> ring
  have hrows : (∑ h ∈ Ioc 0 H,if (p:ℕ)∣h then finitePairDensity S h else 0)=
      ∑ k ∈ Ioc 0 (H/p),finitePairDensity S k := by
    rw [←sum_filter,sum_divisible_Ioc p.prop.pos,Nat.zero_div]
    exact sum_congr rfl (fun k _ => density_at_new_multiple hp k)
  have hdiv : ((H%p:ℕ):ℝ)+(p:ℝ)*((H/p:ℕ):ℝ)=H := by exact_mod_cast Nat.mod_add_div H (p:ℕ)
  change localGapDeficit (insert p S) H=(1-t)*localGapDeficit S H+t*_
  simp only [localGapDeficit,hs,sum_add_distrib,←mul_sum,hrows]
  linear_combination t*hdiv.symm

theorem local_gap_deficit_nonnegative (S : Finset Nat.Primes) (H : ℕ) : 0≤localGapDeficit S H := by
  induction S using Finset.induction_on generalizing H with
  | empty => simp [localGapDeficit,finitePairDensity,Nat.card_Ioc]
  | @insert p S hp ih =>
    rw [local_gap_deficit_insert hp]
    have hp2 : (2:ℝ)≤p := by exact_mod_cast p.prop.two_le
    have hp1 : (1:ℝ)≤(p:ℝ)-1 := by linarith only [hp2]
    have hle : 1/((p:ℝ)-1)^2≤1 := (div_le_one (by positivity)).mpr (one_le_pow₀ hp1)
    exact add_nonneg (mul_nonneg (sub_nonneg.mpr hle) (ih H)) (mul_nonneg (by positivity)
      (add_nonneg (mul_nonneg (Nat.cast_nonneg _) (ih _)) (Nat.cast_nonneg _)))

/-- Every sharp prefix of the full Hardy–Littlewood singular series
has mean at most one, including incomplete periods of every modulus. -/
theorem pair_singular_series_prefix_le (H : ℕ) :
    (∑ h ∈ Icc 1 H,hardyLittlewoodSingularSeries h) ≤ H := by
  have hi : Ioc 0 H=Icc 1 H := by ext h; simp only [mem_Ioc,mem_Icc]; omega
  have ht : Tendsto (fun S : Finset Nat.Primes => ∑ h ∈ Icc 1 H,finitePairDensity S h) atTop
      (𝓝 (∑ h ∈ Icc 1 H,hardyLittlewoodSingularSeries h)) :=
    tendsto_finsetSum _ fun h hh => hasProd_hardyLittlewoodSingularSeries (mem_Icc.mp hh).1
  apply le_of_tendsto ht
  filter_upwards with S
  have ha := local_gap_deficit_nonnegative S H
  simpa only [localGapDeficit,hi,sub_nonneg] using ha

private theorem weighted_gap_error_le (f : ℕ → ℝ) (hf : ∀ H : ℕ,(∑ h ∈ Icc 1 H,f h) ≤ H)
    (H : ℕ) (w : ℕ → ℝ) (hw : Antitone w) (hpos : ∀ i,0≤w i) :
    (∑ h ∈ Icc 1 H,(f h-1)*w h) ≤ 0 := by
  have hpre (k : ℕ) : (∑ h ∈ Icc 1 k,(f h-1))≤0 := by
    rw [sum_sub_distrib,sum_const,nsmul_eq_mul,mul_one,Nat.card_Icc]
    simpa only [Nat.add_sub_cancel,sub_nonpos] using hf k
  have ha := sum_smul_eq_prefix_differences (fun h => f h-1) w H
  simp only [smul_eq_mul] at ha
  rw [ha]
  exact add_nonpos (mul_nonpos_of_nonpos_of_nonneg (hpre H) (hpos _))
    (sum_nonpos fun i _ => mul_nonpos_of_nonpos_of_nonneg (hpre i) (sub_nonneg.mpr (hw (Nat.le_succ i))))

/-- Nonnegative decreasing gap weights preserve the finite endpoint sign. -/
theorem weighted_pair_singular_series_le (H : ℕ) (w : ℕ → ℝ) (hw : Antitone w)
    (hpos : ∀ i,0≤w i) :
    (∑ h ∈ Icc 1 H,(hardyLittlewoodSingularSeries h-1)*w h) ≤ 0 :=
  weighted_gap_error_le _ pair_singular_series_prefix_le H w hw hpos

/-- The sharp gap inequality for a finite set of local factors and any
nonnegative decreasing partner weight. -/
theorem finite_weighted_pair_density_le (S : Finset Nat.Primes) (H : ℕ) (w : ℕ → ℝ)
    (hw : Antitone w) (hpos : ∀ i, 0 ≤ w i) :
    (∑ h ∈ Icc 1 H, (finitePairDensity S h-1)*w h) ≤ 0 := by
  apply weighted_gap_error_le _ _ H w hw hpos
  intro k
  have hi : Ioc 0 k = Icc 1 k := by ext h; simp only [mem_Ioc,mem_Icc]; omega
  simpa only [localGapDeficit,hi,sub_nonneg] using local_gap_deficit_nonnegative S k

/-- A different finite sieve may be used at every left endpoint.
The estimate keeps the rightmost partner of each integer. -/
theorem finite_pair_octave_congruence_nonpositive (S : ℕ → Finset Nat.Primes) (M : ℕ) :
    (∑ d ∈ Ioc M (2*M), (d:ℝ)⁻¹ *
      ∑ h ∈ Icc 1 (2*M-d),(finitePairDensity (S d) h-1)*((d:ℝ)+h)⁻¹) ≤ 0 := by
  apply sum_nonpos
  intro d hd
  have hd0 : 0<(d:ℝ) := Nat.cast_pos.mpr ((Nat.zero_le M).trans_lt (mem_Ioc.mp hd).1)
  apply mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr hd0.le)
  apply finite_weighted_pair_density_le _ _ (fun h : ℕ => ((d:ℝ)+h)⁻¹)
  · intro i j hij
    exact inv_anti₀ (by positivity) (add_le_add le_rfl (Nat.cast_le.mpr hij))
  · intro h
    positivity

/-- The local prediction for distinct prime pairs in one entire sharp
reciprocal octave is nonpositive, with both partner endpoints retained. -/
theorem distinct_reciprocal_octave_congruence_nonpositive (M : ℕ) :
    (∑ d ∈ Ioc M (2*M), (d:ℝ)⁻¹ *
      ∑ h ∈ Icc 1 (2*M-d),(hardyLittlewoodSingularSeries h-1)*((d:ℝ)+h)⁻¹) ≤ 0 := by
  apply sum_nonpos
  intro d hd
  have hd0 : 0<(d:ℝ) := Nat.cast_pos.mpr ((Nat.zero_le M).trans_lt (mem_Ioc.mp hd).1)
  apply mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr hd0.le)
  apply weighted_pair_singular_series_le _ (fun h : ℕ => ((d:ℝ)+h)⁻¹)
  · intro i j hij
    exact inv_anti₀ (by positivity) (add_le_add le_rfl (Nat.cast_le.mpr hij))
  · intro h
    positivity

#print axioms local_gap_deficit_insert
#print axioms finite_pair_octave_congruence_nonpositive
#print axioms pair_singular_series_prefix_le
#print axioms distinct_reciprocal_octave_congruence_nonpositive

end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
