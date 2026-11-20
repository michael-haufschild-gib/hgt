import GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.TheSharpCesaroNormOfAnIncreasingWindow
import GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.TheMassProfileOfTheFirstLogarithmicOverlap
import GaloisForLFunctions.ArithmeticCorrelationGeometry.SuccessorCorrelationsCancelToTheSquareRootAlmostSurely

/-!
# The first Möbius overlap at almost every prime twist

Haar-orthogonality of the distinct ratios n/(n+1) gives square-root
cancellation for their ordinary prefixes at almost every prime twist.
Abel summation and the increasing first-band weights transfer this to
the physical energy simultaneously at every bandwidth through 2/M.
-/

namespace GaloisForLFunctions.ConjugateDiagonalGeometry.LogWindowRetrieval
open Finset Filter Topology MeasureTheory Complex
open _root_.RHTower
open GaloisForLFunctions.ArithmeticCorrelationGeometry
open scoped ComplexConjugate ArithmeticFunction.Moebius
noncomputable section

/-- The critical-line amplitude attached to arbitrary coefficients. -/
def criticalAmplitude (b : ℕ → ℂ) (n : ℕ) := ((Real.sqrt n)⁻¹:ℝ) • b n

/-- The real correlation read by an untwisted logarithmic window. -/
def adjacentRealProduct (b : ℕ → ℂ) (j : ℕ) := gram (b (j+2)) (b (j+1))

private theorem gram_real_smul (s t : ℝ) (z u : ℂ) :
    gram (s • z) (t • u) = s*t*gram z u := by
  change (((s:ℂ)*z)*conj ((t:ℂ)*u)).re = s*t*(z*conj u).re
  rw [map_mul,Complex.conj_ofReal,show ((s:ℂ)*z)*((t:ℂ)*conj u) =
    (((s*t:ℝ):ℂ))*(z*conj u) by push_cast; ring,Complex.re_ofReal_mul]

/-- Critical normalization gives exactly the increasing row on the raw
real Gram coefficients. -/
theorem normalized_critical_excess (b : ℕ → ℂ) (N : ℕ) {d : ℝ} (hd : 0<d)
    (hband : d*((N:ℝ)+2) ≤ 2) :
    normalizedExcess (criticalAmplitude b) (N+2) d =
      2*weightedPrefix (adjacentRealProduct b) (fun _ j => adjacentWeight d (j+1)) N := by
  have hcast : ((N+1+1:ℕ):ℝ) = (N:ℝ)+2 := by push_cast; ring
  have hb : d*((N+1+1:ℕ):ℝ) ≤ 2 := by rwa [hcast]
  rw [normalizedExcess,excess_energy_adjacent_spectrum _ (N+1) hd.le hb,mul_div_assoc,sum_div,weightedPrefix]
  congr 1
  apply sum_congr rfl
  intro j _
  simp only [criticalAmplitude,gram_real_smul,adjacentRealProduct,adjacentWeight]
  rw [←Nat.cast_succ (n:=j+1)]
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

/-- Maximum size of an ordinary adjacent prefix controls the departure
from diagonal energy uniformly in the full first band, at cost 4/(N+1). -/
theorem first_band_critical_prefix_bound (b : ℕ → ℂ) (N : ℕ) {B : ℝ} (hB : 0≤B)
    (hp : ∀ j≤N, |deningerPartialSum (adjacentRealProduct b) j| ≤ B) {d : ℝ}
    (hd : 0 ≤ d) (hband : d*((N:ℝ)+2) ≤ 2) :
    |normalizedExcess (criticalAmplitude b) (N+2) d| ≤ 4*B/((N:ℝ)+1) := by
  rcases hd.eq_or_lt with rfl|hd
  · simp only [normalizedExcess,div_zero,abs_zero]; positivity
  let w (_ j : ℕ) := adjacentWeight d (j+1)
  have hn (j : ℕ) : 0≤w N j := div_nonneg (div_nonneg (le_max_right _ _) hd.le)
    (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  have hstep (j : ℕ) (hj : j<N) : w N j ≤ w N (j+1) := by
    apply adjacent_weight_step (Nat.succ_pos _) hd.le
    exact (mul_le_mul_of_nonneg_left (by exact_mod_cast (show j+1+2≤N+2 by omega) :
      ((j+1:ℕ):ℝ)+2 ≤ (N:ℝ)+2) hd.le).trans hband
  have hobs := observation_le_cesaro_row_norm (adjacentRealProduct b) w N (hn 0) (hn _) hstep
    hB (b:=0) (fun j hj => by simpa only [zero_mul,add_zero] using hp j hj)
  rw [zero_mul,add_zero] at hobs
  have htop : w N N ≤ 1/((N:ℝ)+1) := by
    simpa only [w,Nat.cast_succ] using adjacent_weight_le_reciprocal (Nat.succ_pos N) hd
  rw [normalized_critical_excess b N hd hband,abs_mul,abs_of_nonneg (by norm_num : (0:ℝ)≤2)]
  calc
    _ ≤ 2*(2*B*w N N) := mul_le_mul_of_nonneg_left hobs (by norm_num)
    _ ≤ 2*(2*B*(1/((N:ℝ)+1))) := by gcongr
    _ = _ := by ring

/-- The unweighted prime gauge twist of the Möbius sequence. -/
def gaugedMoebius (x : GaugeTorus) (n : ℕ) : ℂ := ((μ n:ℤ):ℂ)*twist x n

private theorem gram_prefix (b : ℕ → ℂ) (j : ℕ) :
    deningerPartialSum (adjacentRealProduct b) j =
      (∑ n ∈ Ioc 0 (j+1), b n*conj (b (n+1))).re := by
  have hset : Ioc 0 (j+1) = Icc 1 (j+1) := by ext i; simp only [mem_Ioc,mem_Icc]; omega
  rw [hset,sum_Icc_eq_sum_range_shift,Complex.re_sum,deningerPartialSum]
  exact sum_congr rfl fun i _ => gram_comm _ _

/-- The off-diagonal energy per unit bandwidth at almost every prime
twist is O(log² M/√M), uniformly over the first band at every cutoff. -/
theorem ae_gauged_moebius_first_band :
    ∀ᵐ x ∂gaugeHaar, ∃ C : ℝ, 0≤C ∧ ∀ (N : ℕ) (d : ℝ), 0≤d → d*((N:ℝ)+2)≤2 →
      |normalizedExcess (criticalAmplitude (gaugedMoebius x)) (N+2) d| ≤
        C*Real.sqrt ((N:ℝ)+2)*(1+Real.log ((N:ℝ)+2))^2/((N:ℝ)+1) := by
  filter_upwards [ae_moebius_chowla] with x hx
  obtain ⟨C,hC,hbound⟩ := (hx 1 le_rfl).1
  refine ⟨4*C,by positivity,fun N d hd hb => ?_⟩
  let B := C*Real.sqrt ((N:ℝ)+2)*(1+Real.log ((N:ℝ)+2))^2
  have hp (j : ℕ) (hj : j≤N) : |deningerPartialSum (adjacentRealProduct (gaugedMoebius x)) j| ≤ B := by
    rw [gram_prefix]
    refine (Complex.abs_re_le_norm _).trans ((hbound (j+1)).trans ?_)
    have hm : ((j+1:ℕ):ℝ)+1 ≤ (N:ℝ)+2 := by exact_mod_cast (show j+1+1≤N+2 by omega)
    have h₁ : (1:ℝ) ≤ ((j+1:ℕ):ℝ)+1 := le_add_of_nonneg_left (Nat.cast_nonneg _)
    have hs := Real.sqrt_le_sqrt hm
    have hl := Real.log_le_log (zero_lt_one.trans_le h₁) hm
    apply mul_le_mul (mul_le_mul_of_nonneg_left hs hC) _ (sq_nonneg _) (by positivity)
    exact pow_le_pow_left₀ (add_nonneg zero_le_one (Real.log_nonneg h₁)) (add_le_add (le_refl 1) hl) 2
  exact (first_band_critical_prefix_bound _ N (by dsimp only [B]; positivity) hp hd hb).trans_eq
    (by dsimp only [B]; ring)

#print axioms normalized_critical_excess
#print axioms first_band_critical_prefix_bound
#print axioms ae_gauged_moebius_first_band
end
end GaloisForLFunctions.ConjugateDiagonalGeometry.LogWindowRetrieval
