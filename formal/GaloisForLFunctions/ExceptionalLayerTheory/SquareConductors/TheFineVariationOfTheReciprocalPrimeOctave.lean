import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.PositiveWeightsForTheReciprocalPrimeOctave
import GaloisForLFunctions.RHTower.MertensSecondTheorem
import Mathlib.Data.Nat.Factorization.PrimePow
import Mathlib.Data.Nat.Log

/-!
# Variation on the integer grid of the reciprocal prime octave

Successive odd endpoints admit an odd Mangoldt atom. At even endpoints
above two the removed atom always pays for the entering atom. This
separates the two variations and prices every cancellation caused by
sampling only the even endpoints.
-/

open Finset Filter Topology ArithmeticFunction
noncomputable section
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

/-- Reciprocal Mangoldt mass at an integer. -/
def octaveMangoldtMass (n : ℕ) : ℝ := vonMangoldt n / n

/-- Change in the centered reciprocal Mangoldt mass at a single endpoint. -/
def octaveEndpointJump (n : ℕ) : ℝ := reciprocalOctaveError n-reciprocalOctaveError (n-1)

private theorem prefix_atom {n : ℕ} (hn : 0<n) :
    ∑ j ∈ Ioc 0 n, reciprocalOctaveAtom j/j = reciprocalOctaveError n :=
  octave_atom_weighted_prefix hn

private theorem jump_eq_atom {n : ℕ} (hn : 1<n) : octaveEndpointJump n = reciprocalOctaveAtom n/n := by
  obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n≠0)
  rw [octaveEndpointJump,Nat.succ_sub_one,←prefix_atom (Nat.succ_pos _),←prefix_atom (by omega : 0 < m)]
  have h := sum_Ioc_consecutive (fun j : ℕ => reciprocalOctaveAtom j/j) (Nat.zero_le m) (Nat.le_succ m)
  simpa using (sub_eq_iff_eq_add.mpr ((add_comm ..).trans h).symm :
    (∑ j ∈ Ioc 0 (m+1), reciprocalOctaveAtom j/j) - ∑ j ∈ Ioc 0 m, reciprocalOctaveAtom j/j =
      ∑ j ∈ Ioc m (m+1), reciprocalOctaveAtom j/j)

/-- Every odd endpoint above one is an upward jump of exact height Λ(n)/n. -/
theorem octave_odd_endpoint {n : ℕ} (hn : 1<n) (ho : ¬2 ∣ n) :
    octaveEndpointJump n = vonMangoldt n/n := by
  rw [jump_eq_atom hn]
  simp [reciprocalOctaveAtom,ho,show n≠1 by omega]

private theorem even_power_of_nonzero {n : ℕ} (hn : vonMangoldt (2*n) ≠ 0) :
    ∃ j : ℕ, n=2^j := by
  have hpow : IsPrimePow (2*n) := by_contra fun h => hn (vonMangoldt_eq_zero_iff.mpr h)
  obtain ⟨p,k,hp,hk,he⟩ := (isPrimePow_nat_iff (2*n)).mp hpow
  have h2 : 2 ∣ p^k := he.symm ▸ dvd_mul_right 2 n
  obtain rfl : p=2 := ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp (Nat.prime_two.dvd_of_dvd_pow h2)).symm
  obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
  rw [pow_succ'] at he
  exact ⟨j,by omega⟩

/-- On even endpoints the debit is Λ(n)/n minus Λ(2n)/(2n).
Only powers of two have a nonzero credit. The endpoint two is exceptional. -/
theorem octave_even_endpoint {n : ℕ} (hn : 0<n) :
    octaveEndpointJump (2*n) = octaveMangoldtMass (2*n)-octaveMangoldtMass n := by
  rw [jump_eq_atom (by omega)]
  simp only [reciprocalOctaveAtom,dvd_mul_right,if_pos,Nat.mul_div_cancel_left _ (by decide : 0<2),
    if_neg (show 2*n≠1 by omega),sub_zero,octaveMangoldtMass,Nat.cast_mul,Nat.cast_ofNat]
  field_simp [(Nat.cast_ne_zero.mpr hn.ne' : (n:ℝ)≠0)] <;> ring

theorem octave_even_endpoint_nonpositive {n : ℕ} (hn : 1<n) : octaveEndpointJump (2*n) ≤ 0 := by
  rw [octave_even_endpoint (by omega),sub_nonpos]
  by_cases h : vonMangoldt (2*n)=0
  · simp only [octaveMangoldtMass,h,zero_div]
    exact div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg _)
  obtain ⟨j,rfl⟩ := even_power_of_nonzero h
  have hj : j≠0 := by intro he; simp [he] at hn
  have hpos : 0 < ((2^j:ℕ):ℝ) := Nat.cast_pos.mpr (pow_pos (by decide) _)
  dsimp only [octaveMangoldtMass]
  rw [← pow_succ',vonMangoldt_apply_pow (Nat.succ_ne_zero _),vonMangoldt_apply_pow hj,
    vonMangoldt_apply_prime Nat.prime_two,pow_succ',Nat.cast_mul,Nat.cast_ofNat]
  apply div_le_div_of_nonneg_left (Real.log_natCast_nonneg _) hpos
  linarith only [hpos]

/-- Fine variation along all integer endpoints above one. -/
def octaveFineVariation (N : ℕ) : ℝ := ∑ n ∈ Ioc 1 N, |octaveEndpointJump n|

/-- Reciprocal Mangoldt mass of the even integers through the endpoint. -/
def octaveEvenMangoldtPrefix (N : ℕ) : ℝ := ∑ n ∈ (Icc 1 N).filter (fun n => 2∣n), octaveMangoldtMass n

private theorem positive_jump {n : ℕ} (hn : 1<n) :
    max (octaveEndpointJump n) 0 =
      octaveMangoldtMass n - (if 2∣n then octaveMangoldtMass n else 0) + (if n=2 then Real.log 2/2 else 0) := by
  by_cases h : 2∣n
  · obtain ⟨m,rfl⟩ := h
    by_cases he : m=1
    · subst m
      norm_num [octave_even_endpoint (n:=1) (by decide),octaveMangoldtMass,vonMangoldt_apply_prime Nat.prime_two,
        max_eq_left (by positivity : 0≤Real.log 2/2)]
    · rw [max_eq_right (octave_even_endpoint_nonpositive (by omega : 1 < m))]
      simp [show 2*m≠2 by omega]
  · rw [octave_odd_endpoint hn h,max_eq_left (div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg _))]
    simp [h,show n≠2 by rintro rfl; exact h (dvd_refl _),octaveMangoldtMass]

private theorem total_jump {N : ℕ} (hn : 1≤N) :
    ∑ n ∈ Ioc 1 N, octaveEndpointJump n = reciprocalOctaveError N+Real.log 2 := by
  induction N,hn using Nat.le_induction with
  | base => simp [reciprocalOctaveError]
  | succ n hn ih =>
    rw [sum_Ioc_succ_top hn,ih,octaveEndpointJump,Nat.succ_sub_one]
    ring

/-- Exact Jordan variation. The even Mangoldt prefix and the endpoint
reading are the full correction to twice the classical harmonic prefix. -/
theorem octave_fine_variation_identity {N : ℕ} (hN : 2≤N) :
    octaveFineVariation N =
      2*(∑ n ∈ Icc 1 N, vonMangoldt n/n) - 2*octaveEvenMangoldtPrefix N - reciprocalOctaveError N := by
  let S := Ioc 1 N
  have add_one (f : ℕ → ℝ) (hf : f 1=0) : ∑ i ∈ S, f i = ∑ i ∈ Icc 1 N, f i := by
    rw [show Icc 1 N = insert 1 S from (Ioc_insert_left (by omega)).symm,
      sum_insert (show 1 ∉ S by simp [S]),hf,zero_add]
  have oddpart : (∑ n ∈ S, max (octaveEndpointJump n) 0) =
      (∑ n ∈ Icc 1 N, octaveMangoldtMass n)-octaveEvenMangoldtPrefix N+Real.log 2/2 := by
    rw [sum_congr rfl (fun n hn => positive_jump (mem_Ioc.mp hn).1),sum_add_distrib,sum_sub_distrib,
      add_one octaveMangoldtMass (by simp [octaveMangoldtMass]),add_one (fun n => if 2∣n then octaveMangoldtMass n else 0) (by simp),
      ←sum_filter,sum_ite_eq',if_pos (show 2 ∈ S from mem_Ioc.mpr ⟨by decide,hN⟩)]
    rfl
  have point (n : ℕ) : |octaveEndpointJump n| = 2*max (octaveEndpointJump n) 0-octaveEndpointJump n := by
    rcases le_total 0 (octaveEndpointJump n) with h|h
    · rw [abs_of_nonneg h,max_eq_left h]; ring
    · rw [abs_of_nonpos h,max_eq_right h]; ring
  unfold octaveFineVariation
  simp_rw [point]
  rw [sum_sub_distrib,←mul_sum,total_jump (by omega),oddpart]
  dsimp only [octaveMangoldtMass]
  ring


private theorem even_atom_powers (N : ℕ) :
    octaveEvenMangoldtPrefix N =
      ∑ j ∈ range (Nat.log 2 N), octaveMangoldtMass (2^(j+1)) := by
  classical
  let D := (range (Nat.log 2 N)).image (fun j : ℕ => 2^(j+1))
  let E := (Icc 1 N).filter (fun n : ℕ => 2 ∣ n)
  have sub : D ⊆ E := by
    intro n hn
    obtain ⟨j,hj,rfl⟩ := mem_image.mp hn
    have hj' := mem_range.mp hj
    have hN : N≠0 := by rintro rfl; simp at hj'
    refine mem_filter.mpr ⟨mem_Icc.mpr ⟨Nat.one_le_pow _ _ (by decide),?_⟩,?_⟩
    · exact (Nat.pow_le_pow_right (by decide : 0<2) hj').trans (Nat.pow_log_le_self 2 hN)
    · rw [pow_succ']; exact dvd_mul_right _ _
  have eqs : ∑ n ∈ D, octaveMangoldtMass n = ∑ n ∈ E, octaveMangoldtMass n := by
    apply sum_subset sub
    intro n hn hD
    obtain ⟨hm,⟨m,rfl⟩⟩ := mem_filter.mp hn
    by_contra h
    have hv : vonMangoldt (2*m) ≠ 0 := fun hz => h (by simp [octaveMangoldtMass,hz])
    obtain ⟨j,rfl⟩ := even_power_of_nonzero hv
    have hpow : 2^(j+1) ≤ N := by simpa only [pow_succ'] using (mem_Icc.mp hm).2
    exact hD (mem_image.mpr ⟨j, mem_range.mpr (Nat.le_log_of_pow_le (by decide) hpow),pow_succ' ..⟩)
  rw [show octaveEvenMangoldtPrefix N = ∑ n ∈ E, octaveMangoldtMass n from rfl,←eqs]
  exact sum_image (fun i _ j _ he => Nat.succ.inj (Nat.pow_right_injective (by decide : 2≤2) he))

/-- Even reciprocal mass has an exact geometric cutoff at the last power of two. -/
theorem octave_even_mass_geometric (N : ℕ) :
    octaveEvenMangoldtPrefix N = Real.log 2 * (1-(1/2:ℝ)^Nat.log 2 N) := by
  rw [even_atom_powers]
  generalize Nat.log 2 N = J
  induction J with
  | zero => simp
  | succ j ih =>
    rw [Finset.sum_range_succ,ih]
    simp only [octaveMangoldtMass,vonMangoldt_apply_pow (Nat.succ_ne_zero _),
      vonMangoldt_apply_prime Nat.prime_two,Nat.cast_pow,Nat.cast_ofNat,one_div,inv_pow,←div_eq_mul_inv]
    rw [pow_succ]
    field_simp
    <;> ring

private theorem even_mass_limit : Tendsto octaveEvenMangoldtPrefix atTop (𝓝 (Real.log 2)) := by
  have hlog : Tendsto (Nat.log 2) atTop atTop := tendsto_atTop.mpr fun j =>
    (eventually_ge_atTop (2^j)).mono fun _ hn => Nat.le_log_of_pow_le (by decide) hn
  have h := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : 0≤(1/2:ℝ))
    (by norm_num : (1/2:ℝ)<1)).comp hlog
  rw [show octaveEvenMangoldtPrefix = (fun N : ℕ => Real.log 2*(1-(1/2:ℝ)^Nat.log 2 N))
    from funext octave_even_mass_geometric]
  simpa only [Function.comp_apply,sub_zero,mul_one] using
    ((tendsto_const_nhds.sub h).const_mul (Real.log 2) :
      Tendsto (fun N : ℕ => Real.log 2 * (1-(1/2:ℝ)^Nat.log 2 N)) atTop (𝓝 _))

/-- The sharp reciprocal octave has vanishing signed mass after centering. -/
theorem tendsto_reciprocalOctaveError_zero :
    Tendsto reciprocalOctaveError atTop (𝓝 0) := by
  have hm := RHTower.tendsto_sum_vonMangoldt_div_sub_log
  have hq := hm.comp (Nat.tendsto_div_const_atTop (n:=2) (by decide))
  have hscale : Tendsto (fun n : ℕ => (n:ℝ)/2) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_div_const (by norm_num)
  have hratio : Tendsto (fun n : ℕ => ((n/2:ℕ):ℝ)/((n:ℝ)/2)) atTop (𝓝 1) := by
    have hf (n : ℕ) : ⌊(n:ℝ)/2⌋₊ = n/2 := by
      simpa using Nat.floor_div_natCast (n:ℝ) 2
    simpa only [Function.comp_def,hf] using
      ((tendsto_nat_floor_div_atTop (R:=ℝ)).comp hscale)
  have h := (hm.sub hq).sub (hratio.log (by norm_num))
  simp only [Real.log_one,sub_self,sub_zero] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hn' : (n:ℝ)≠0 := Nat.cast_ne_zero.mpr (by omega)
  have hq' : ((n/2:ℕ):ℝ)≠0 := Nat.cast_ne_zero.mpr (by omega)
  have hs := sum_Ioc_consecutive (fun j : ℕ => vonMangoldt j/j) (Nat.zero_le (n/2)) (Nat.div_le_self n 2)
  have intervals (m : ℕ) : Ioc 0 m = Icc 1 m := by ext j; simp only [mem_Ioc,mem_Icc]; omega
  rw [intervals,intervals] at hs
  simp only [Function.comp_apply,reciprocalOctaveError,
    Real.log_div hq' (div_ne_zero hn' (by norm_num : (2:ℝ)≠0)),
    Real.log_div hn' (by norm_num : (2:ℝ)≠0)]
  linarith only [hs]

/-- The full integer-grid variation grows like twice the logarithm.
Its constant term records Euler's constant and the entire dyadic tower. -/
theorem octave_fine_variation_second_term :
    Tendsto (fun N : ℕ => octaveFineVariation N-2*Real.log N) atTop
      (𝓝 (-2*Real.eulerMascheroniConstant-2*Real.log 2)) := by
  have h := (((RHTower.tendsto_sum_vonMangoldt_div_sub_log.const_mul 2).sub
    (even_mass_limit.const_mul 2)).sub tendsto_reciprocalOctaveError_zero)
  rw [sub_zero,show 2*(-Real.eulerMascheroniConstant) = -2*Real.eulerMascheroniConstant by ring] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 2] with N hN
  rw [octave_fine_variation_identity hN]
  ring

end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
