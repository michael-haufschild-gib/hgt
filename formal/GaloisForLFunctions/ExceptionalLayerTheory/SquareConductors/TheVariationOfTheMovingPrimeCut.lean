import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.TheFirstMomentSeenByTheIntegratedConductorSpline
import GaloisForLFunctions.ArithmeticWeightTheory.GaugeDeformations.PrimeAbelCutoff

/-!
# Variation in the lower cutoff of the conductor tail

Below the first knot, changing one integer of the cutoff measures its
centered prime atom exactly. The absolute cutoff variation has quadratic
growth with leading coefficient equal to the inner slope. This holds
uniformly in the terminal conductor.
-/

noncomputable section
open Finset Filter
open scoped Topology
open GaloisForLFunctions.CountingHolography.Sections
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval.ConductorMoment

private abbrev atom (k : ℕ) : ℝ := if k.Prime then Real.log k else 0
private abbrev weighted (k : ℕ) := (k:ℝ)*atom k
private abbrev triangle (K : ℕ) := (K:ℝ)*(K+1)/2
private abbrev row (k : ℕ) := (k:ℝ)-weighted k

private theorem primes (K : ℕ) : (Icc 1 K).filter Nat.Prime = ordinaryPrimeLags K := by
  ext p
  simp only [ordinaryPrimeLags,mem_filter,mem_Icc]
  exact ⟨fun h => ⟨⟨h.2.two_le,h.1.2⟩,h.2⟩,fun h => ⟨⟨h.2.pos,h.1.2⟩,h.2⟩⟩

private theorem moment (K : ℕ) :
    (∑ k ∈ Icc 1 K, weighted k) = ∑ p ∈ ordinaryPrimeLags K,(p:ℝ)*Real.log p := by
  simp only [weighted,atom,mul_ite,mul_zero,←sum_filter,primes]

private theorem moment_complex (K : ℕ) :
    primeMoment K = ((∑ k ∈ Icc 1 K, weighted k : ℝ):ℂ) := by
  rw [moment]
  simp only [primeMoment,Nat.floor_natCast,Complex.ofReal_sum,Complex.ofReal_mul,Complex.ofReal_natCast]

private theorem triangle_sum (K : ℕ) : ∑ k ∈ Icc 1 K, (k:ℝ) = triangle K := by
  induction K with
  | zero => simp [triangle]
  | succ n ih =>
    rw [sum_Icc_succ_top (by omega : 1 ≤ n+1),ih]
    simp only [triangle,Nat.cast_succ]
    ring

/-- A single cutoff increment is independent of the conductor below the
first knot. A prime contributes its exact logarithm to the decrement. -/
theorem inner_cutoff_jump {N k : ℕ} (hN : 0 < N)
    (hk : ((k+1:ℕ):ℝ) ≤ Real.exp (-8)*(N:ℝ)^2) :
    centeredFixedPrimeTail N (k+1)-centeredFixedPrimeTail N k =
      ((innerPrimeSlope*((k+1:ℕ):ℝ)*(1-if (k+1).Prime then Real.log (k+1:ℕ) else 0):ℝ):ℂ) := by
  rw [centered_tail_first_moment hN hk 0,centered_tail_first_moment hN
    ((Nat.cast_le.mpr (Nat.le_succ k)).trans hk) 0,moment_complex,moment_complex,
    sum_Icc_succ_top (by omega : 1 ≤ k+1)]
  push_cast
  simp only [weighted,atom,Nat.cast_succ]
  push_cast
  ring

private theorem gross_moment :
    Tendsto (fun K : ℕ => (∑ k ∈ Icc 1 K, weighted k)/(K:ℝ)^2) atTop (𝓝 (1/2:ℝ)) := by
  obtain ⟨C,_,hc⟩ := first_prime_moment_at_cut
  have hnat := tendsto_natCast_atTop_atTop (R:=ℝ)
  have htri : Tendsto (fun K : ℕ => triangle K/(K:ℝ)^2) atTop (𝓝 (1/2:ℝ)) := by
    have h := (tendsto_const_nhds (x := (1:ℝ))).add hnat.inv_tendsto_atTop
    have h' := h.div_const 2
    simp only [add_zero] at h'
    refine h'.congr' ?_
    filter_upwards [eventually_ge_atTop (1:ℕ)] with K hk
    change (1+(K:ℝ)⁻¹)/2=triangle K/(K:ℝ)^2
    dsimp only [triangle]
    field_simp [(Nat.cast_pos (α:=ℝ)).mpr hk |>.ne']
    <;> ring
  have hdecay := ((tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<1/9)).comp hnat).const_mul C
  simp only [mul_zero] at hdecay
  have err : Tendsto (fun K : ℕ => ((∑ k ∈ Icc 1 K,weighted k)-triangle K)/(K:ℝ)^2)
      atTop (𝓝 0) := by
    apply (tendsto_zero_iff_abs_tendsto_zero _).mpr
    apply squeeze_zero' (.of_forall fun _ => abs_nonneg _) _ hdecay
    filter_upwards [eventually_ge_atTop (1:ℕ)] with K hk
    have kp := Nat.cast_pos (α:=ℝ).mpr hk
    rw [Function.comp_apply,abs_div,abs_of_nonneg (sq_nonneg (K:ℝ)),div_le_iff₀ (sq_pos_of_pos kp),moment]
    have h := hc K hk
    apply h.trans_eq
    rw [mul_assoc,← Real.rpow_two,←Real.rpow_add kp]
    norm_num
  have h := htri.add err
  simp only [add_zero] at h
  exact h.congr fun K => by change _ / _ + (_ - _) / _ = _; ring

private theorem leakage (K : ℕ) :
    |(∑ k ∈ Icc 1 K, |row k|) - (triangle K + ∑ k ∈ Icc 1 K, weighted k)| ≤
      2*(K:ℝ)*(Nat.primeCounting K:ℝ) := by
  have term (k : ℕ) (hk : k ∈ Icc 1 K) :
      |(|row k| - ((k:ℝ)+weighted k))| ≤ if k.Prime then 2*(K:ℝ) else 0 := by
    have kk : (k:ℝ) ≤ K := Nat.cast_le.mpr (mem_Icc.mp hk).2
    by_cases hp : k.Prime
    · have h0 := mul_nonneg (Nat.cast_nonneg (α:=ℝ) k) (Real.log_natCast_nonneg k)
      simp only [row,weighted,atom,if_pos hp]
      have tri := abs_sub (k:ℝ) ((k:ℝ)*Real.log k)
      rw [abs_of_nonneg (Nat.cast_nonneg (α:=ℝ) k),abs_of_nonneg h0] at tri
      rw [abs_of_nonpos (sub_nonpos.mpr tri)]
      linarith only [neg_abs_le ((k:ℝ)-(k:ℝ)*Real.log k),kk]
    · simp [row,weighted,atom,hp,abs_of_nonneg (Nat.cast_nonneg (α:=ℝ) k)]
  have card : (ordinaryPrimeLags K).card = Nat.primeCounting K := by
    change _ = Nat.count Nat.Prime (K+1)
    rw [Nat.count_eq_card_filter_range]
    congr 1
    ext p
    simp only [ordinaryPrimeLags,mem_filter,mem_Icc,mem_range]
    exact ⟨fun h => ⟨by omega,h.2⟩,fun h => ⟨⟨h.2.two_le,by omega⟩,h.2⟩⟩
  rw [←triangle_sum,←sum_add_distrib,←sum_sub_distrib]
  apply (abs_sum_le_sum_abs ..).trans
  apply (sum_le_sum term).trans_eq
  rw [←sum_filter,primes,sum_const,nsmul_eq_mul,card,mul_comm]

/-- The cutoff variation divided by K² tends to the inner slope. The
terminal conductor can be chosen independently for every K. -/
theorem inner_cutoff_variation (N : ℕ → ℕ)
    (window : ∀ᶠ K : ℕ in atTop, 0 < N K ∧ (K:ℝ) ≤ Real.exp (-8)*(N K:ℝ)^2) :
    Tendsto (fun K : ℕ => (∑ k ∈ Icc 1 K,
      ‖centeredFixedPrimeTail (N K) k-centeredFixedPrimeTail (N K) (k-1)‖)/(K:ℝ)^2)
      atTop (𝓝 innerPrimeSlope) := by
  have hnat := tendsto_natCast_atTop_atTop (R:=ℝ)
  have htri := ((tendsto_const_nhds (x := (1:ℝ))).add hnat.inv_tendsto_atTop).div_const 2
  simp only [add_zero] at htri
  have htotal : Tendsto (fun K : ℕ => (triangle K + ∑ k ∈ Icc 1 K, weighted k)/(K:ℝ)^2)
      atTop (𝓝 1) := by
    have h := htri.add gross_moment
    norm_num only [show (1:ℝ)/2+1/2=1 by norm_num] at h
    refine h.congr' ?_
    filter_upwards [eventually_ge_atTop (1:ℕ)] with K hk
    change (1+(K:ℝ)⁻¹)/2+_ = _
    dsimp only [triangle]
    field_simp [(Nat.cast_pos (α:=ℝ)).mpr hk |>.ne']
    <;> ring
  have hp := ArithmeticWeightTheory.GaugeDeformations.tendsto_primeCounting_div_nat_zero.const_mul 2
  simp only [mul_zero] at hp
  have hdiff : Tendsto (fun K : ℕ => ((∑ k ∈ Icc 1 K, |row k|) -
      (triangle K+∑ k ∈ Icc 1 K, weighted k))/(K:ℝ)^2) atTop (𝓝 0) := by
    apply (tendsto_zero_iff_abs_tendsto_zero _).mpr
    apply squeeze_zero' (.of_forall fun _ => abs_nonneg _) _ hp
    filter_upwards [eventually_ge_atTop (1:ℕ)] with K hk
    have kp := Nat.cast_pos (α:=ℝ).mpr hk
    rw [abs_div,abs_of_nonneg (sq_nonneg (K:ℝ)),div_le_iff₀ (sq_pos_of_pos kp)]
    exact (leakage K).trans_eq (by change _ = 2*(_/(K:ℝ))*(K:ℝ)^2; field_simp)
  have limit := (htotal.add hdiff).const_mul innerPrimeSlope
  simp only [add_zero,mul_one] at limit
  refine limit.congr' ?_
  filter_upwards [window] with K hw
  have each (k : ℕ) (hk : k ∈ Icc 1 K) :
      ‖centeredFixedPrimeTail (N K) k-centeredFixedPrimeTail (N K) (k-1)‖ =
        innerPrimeSlope*|row k| := by
    obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by have := (mem_Icc.mp hk).1; omega : k ≠ 0)
    rw [Nat.succ_sub_one,inner_cutoff_jump hw.1 ((Nat.cast_le.mpr (mem_Icc.mp hk).2).trans hw.2),
      Complex.norm_real,Real.norm_eq_abs, mul_assoc,abs_mul,abs_of_pos innerPrimeSlope_pos]
    congr 2
    dsimp only [row,weighted,atom]
    ring
  rw [sum_congr rfl each,←mul_sum]
  change _ * (_ / _ + (_ - _) / _) = _ / _
  ring

end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval.ConductorMoment
