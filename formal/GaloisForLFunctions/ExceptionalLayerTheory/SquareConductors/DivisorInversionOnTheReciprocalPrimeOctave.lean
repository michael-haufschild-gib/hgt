import GaloisForLFunctions.ExceptionalLayerTheory.CancellationOnRepeatedPrimeFactors
import GaloisForLFunctions.RHTower.Sieve.ChebyshevMoebius
import GaloisForLFunctions.RHTower.MoebiusFloorSummatory

/-!
# Divisor inversion on the reciprocal Mangoldt octave

Centered reciprocal octave mass is a finite Möbius sum against alternating
ordinary logarithms. The cutoff in its short factor is the exact integer quotient.
-/

noncomputable section
open Finset ArithmeticFunction
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

/-- The dilation difference before division by the integer index. The unit
removes the continuous mass of the reciprocal octave. -/
def reciprocalOctaveAtom (n : ℕ) : ℝ := vonMangoldt n -
  2*(if 2 ∣ n then vonMangoldt (n/2) else 0) - (if n=1 then Real.log 2 else 0)

/-- Alternating ordinary logarithm produced by the complete divisor sum. -/
def parityOctaveLog (n : ℕ) : ℝ :=
  if 2 ∣ n then -Real.log ((n:ℝ)/2) else Real.log ((n:ℝ)/2)

private theorem even_divisor_mass {n : ℕ} (hn : 0 < n) :
    (∑ d ∈ n.divisors, if 2 ∣ d then vonMangoldt (d/2) else 0) =
      if 2 ∣ n then Real.log ((n:ℝ)/2) else 0 := by
  classical
  by_cases h : 2 ∣ n
  · obtain ⟨m,rfl⟩ := h
    have hm : 0 < m := by omega
    rw [if_pos (dvd_mul_right 2 m),←sum_filter]
    have hs : (2*m).divisors.filter (2 ∣ ·) = m.divisors.image (fun j => 2*j) := by
      ext d
      simp only [mem_filter,Nat.mem_divisors,mem_image]
      constructor
      · rintro ⟨⟨hd,_⟩,j,rfl⟩
        exact ⟨j,⟨Nat.dvd_of_mul_dvd_mul_left (by decide : 0<2) hd,hm.ne'⟩,rfl⟩
      · rintro ⟨j,⟨hj,_⟩,rfl⟩
        exact ⟨⟨Nat.mul_dvd_mul_left _ hj,hn.ne'⟩,dvd_mul_right 2 j⟩
    rw [hs,sum_image (fun i _ j _ hij => by omega)]
    simp only [Nat.mul_div_cancel_left _ (by decide : 0<2),vonMangoldt_sum,Nat.cast_mul,Nat.cast_ofNat]
    congr 1
    ring
  · rw [if_neg h]
    exact sum_eq_zero fun d hd => if_neg (fun h2 => h (h2.trans (Nat.mem_divisors.mp hd).1))

/-- Summing over the actual divisors converts the Mangoldt difference to
the ordinary alternating logarithm, including its unit value. -/
theorem reciprocal_octave_divisor_identity {n : ℕ} (hn : 0 < n) :
    ∑ d ∈ n.divisors, reciprocalOctaveAtom d = parityOctaveLog n := by
  classical
  have hone : 1 ∈ n.divisors := Nat.mem_divisors.mpr ⟨one_dvd _,hn.ne'⟩
  have hs : (∑ d ∈ n.divisors, if d=1 then Real.log 2 else 0) = Real.log 2 := by simp [hone]
  simp only [reciprocalOctaveAtom,sum_sub_distrib,←mul_sum,vonMangoldt_sum,even_divisor_mass hn,hs]
  unfold parityOctaveLog
  rw [Real.log_div (Nat.cast_ne_zero.mpr hn.ne') (by norm_num : (2:ℝ)≠0)]
  by_cases h : 2 ∣ n <;> simp only [h,if_true,if_false] <;> ring

/-- The atom prefix pays the lower dyadic endpoint and the density at one. -/
theorem octave_atom_weighted_prefix {N : ℕ} (hN : 0 < N) :
    (∑ n ∈ Ioc 0 N, reciprocalOctaveAtom n/n) =
      (∑ n ∈ Ioc (N/2) N, vonMangoldt n/n)-Real.log 2 := by
  classical
  let h (n : ℕ) := vonMangoldt n/(n:ℝ)
  have he : (∑ n ∈ Ioc 0 N, (2*(if 2∣n then vonMangoldt (n/2) else 0))/(n:ℝ)) =
      ∑ j ∈ Ioc 0 (N/2), h j := by
    simp_rw [mul_ite,mul_zero,ite_div,zero_div]
    rw [←sum_filter,sum_divisible_Ioc (by decide : 0<2),Nat.zero_div]
    apply sum_congr rfl
    intro j hj
    simp only [Nat.mul_div_cancel_left _ (by decide : 0<2),Nat.cast_mul,Nat.cast_ofNat,h]
    ring
  have hu : (∑ n ∈ Ioc 0 N, (if n=1 then Real.log 2 else 0)/(n:ℝ)) = Real.log 2 := by
    have hone : 1 ∈ Ioc 0 N := mem_Ioc.mpr ⟨by decide,hN⟩
    simp [ite_div,hone]
  have hs := sum_Ioc_consecutive h (Nat.zero_le (N/2)) (Nat.div_le_self N 2)
  simp only [reciprocalOctaveAtom,sub_div,sum_sub_distrib,he,hu]
  change (∑ n ∈ Ioc 0 N, h n)-(∑ j ∈ Ioc 0 (N/2), h j)-_ = (∑ n ∈ Ioc (N/2) N, h n)-_
  linarith only [hs]

/-- Möbius inversion on both sharp endpoints of the reciprocal ordinary
octave. The remaining short-factor test contains no prime weights. -/
theorem reciprocal_mangoldt_octave_moebius {N : ℕ} (hN : 0 < N) :
    (∑ n ∈ Ioc (N/2) N, vonMangoldt n/n)-Real.log 2 =
      ∑ d ∈ Icc 1 N, ((moebius d:ℤ):ℝ)/d *
        ∑ j ∈ Icc 1 (N/d), parityOctaveLog j/j := by
  classical
  let μ (d : ℕ) : ℝ := (moebius d : ℤ)
  have hinv := (sum_eq_iff_sum_mul_moebius_eq (f := reciprocalOctaveAtom) (g := parityOctaveLog)).mp
    (fun n hn => reciprocal_octave_divisor_identity hn)
  have row (n : ℕ) (hn : 0 < n) :
      reciprocalOctaveAtom n/n = ∑ d ∈ n.divisors, (μ d/d)*(parityOctaveLog (n/d)/(n/d : ℕ)) := by
    rw [←hinv n hn,Nat.sum_divisorsAntidiagonal
      (f := fun d j => ((moebius d:ℤ):ℝ)*parityOctaveLog j),sum_div]
    apply sum_congr rfl
    intro d hd
    rw [div_mul_div_comm,←Nat.cast_mul,Nat.mul_div_cancel' (Nat.mem_divisors.mp hd).1]
  rw [←octave_atom_weighted_prefix hN,show Ioc 0 N=Icc 1 N by ext n; simp only [mem_Ioc,mem_Icc]; omega]
  rw [sum_congr rfl (fun n hn => row n (mem_Icc.mp hn).1),
    _root_.RHTower.Sieve.sum_divisors_swap N (fun d j => (μ d/d)*(parityOctaveLog j/j))]
  exact sum_congr rfl fun _ _ => (mul_sum ..).symm

/-- Finite alternating logarithmic harmonic prefix. -/
def alternatingOctavePrefix (N : ℕ) : ℝ := ∑ j ∈ Icc 1 N, parityOctaveLog j/j

/-- Subtracting a multiple of the exact floor identity leaves a finite
Möbius test with both endpoints. The scalar term is a single terminal sample. -/
theorem reciprocal_octave_finite_floor_subtraction {N : ℕ} (hN : 0 < N) :
    (∑ n ∈ Ioc (N/2) N, vonMangoldt n/n)-Real.log 2 = alternatingOctavePrefix N/N +
      ∑ d ∈ Icc 1 N, ((moebius d:ℤ):ℝ)/d *
        (alternatingOctavePrefix (N/d)-alternatingOctavePrefix N*(d:ℝ)*((N/d:ℕ):ℝ)/N) := by
  rw [reciprocal_mangoldt_octave_moebius hN]
  let F := alternatingOctavePrefix N
  let μ (d : ℕ) : ℝ := (moebius d:ℤ)
  have piece (d : ℕ) (hd : d ∈ Icc 1 N) : (μ d/d)*
      (alternatingOctavePrefix (N/d)-F*(d:ℝ)*((N/d:ℕ):ℝ)/N) =
      μ d/d*alternatingOctavePrefix (N/d) - F/N*(μ d*((N/d:ℕ):ℝ)) := by
    have hd0 : (d:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (show 0 < d from (mem_Icc.mp hd).1).ne'
    field_simp [hd0,Nat.cast_ne_zero.mpr hN.ne']
  change (∑ d ∈ Icc 1 N, μ d/d*alternatingOctavePrefix (N/d)) = F/N + _
  rw [sum_congr rfl piece,sum_sub_distrib,←mul_sum]
  have hone := _root_.RHTower.moebius_floor_summatory N hN
  change (∑ d ∈ Icc 1 N, μ d*((N/d:ℕ):ℝ)) = 1 at hone
  rw [hone,mul_one]
  ring

/-- The remaining large divisors grouped by their exact integer quotient.
Both harmonic and unweighted Möbius sums use the same clipped interval. -/
theorem reciprocal_octave_large_divisor_cells (N D : ℕ) :
    (∑ d ∈ Ioc D N, ((moebius d:ℤ):ℝ)/d *
      (alternatingOctavePrefix (N/d)-alternatingOctavePrefix N*(d:ℝ)*((N/d:ℕ):ℝ)/N)) =
    ∑ j ∈ Icc 1 (N/(D+1)), let I := Ioc (max D (N/(j+1))) (N/j)
      alternatingOctavePrefix j*(∑ d ∈ I, ((moebius d:ℤ):ℝ)/d) -
      ((j:ℝ)*alternatingOctavePrefix N/N)*(∑ d ∈ I, ((moebius d:ℤ):ℝ)) := by
  classical
  have maps : ∀ d ∈ Ioc D N, N/d ∈ Icc 1 (N/(D+1)) := by
    intro d hd
    obtain ⟨hl,hu⟩ := mem_Ioc.mp hd
    exact mem_Icc.mpr ⟨(Nat.one_le_div_iff ((Nat.zero_le D).trans_lt hl)).mpr hu,
      Nat.div_le_div_left hl (Nat.succ_pos D)⟩
  rw [←sum_fiberwise_of_maps_to maps]
  apply sum_congr rfl
  intro j hj
  have hj0 : 0<j := (mem_Icc.mp hj).1
  let I := Ioc (max D (N/(j+1))) (N/j)
  have same : (Ioc D N).filter (fun d => N/d=j) = I := by
    ext d
    simp only [I,mem_filter,mem_Ioc,max_lt_iff]
    constructor
    · rintro ⟨⟨hl,_⟩,he⟩
      have hd0 := (Nat.zero_le D).trans_lt hl
      have hu := (Nat.le_div_iff_mul_le hd0).mp he.ge
      have hb := (Nat.div_lt_iff_lt_mul hd0).mp (show N/d<j+1 by omega)
      rw [Nat.mul_comm] at hu hb
      exact ⟨⟨hl,(Nat.div_lt_iff_lt_mul (Nat.succ_pos j)).mpr hb⟩,(Nat.le_div_iff_mul_le hj0).mpr hu⟩
    · rintro ⟨⟨hl,hb⟩,hu⟩
      have hd0 := (Nat.zero_le D).trans_lt hl
      have hb' := (Nat.div_lt_iff_lt_mul (Nat.succ_pos j)).mp hb
      have hu' := (Nat.le_div_iff_mul_le hj0).mp hu
      rw [Nat.mul_comm] at hb' hu'
      exact ⟨⟨hl,hu.trans (Nat.div_le_self _ _)⟩,Nat.le_antisymm
        (Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul hd0).mpr hb')) ((Nat.le_div_iff_mul_le hd0).mpr hu')⟩
  change _ = alternatingOctavePrefix j*(∑ d ∈ I, _) - _*(∑ d ∈ I, _)
  rw [same,mul_sum,mul_sum,←sum_sub_distrib]
  apply sum_congr rfl
  intro d hd
  have hmem : d ∈ (Ioc D N).filter (fun t => N/t=j) := by rwa [same]
  have hd' := mem_filter.mp hmem
  have hd0 : (d:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr ((Nat.zero_le D).trans_lt (mem_Ioc.mp hd'.1).1).ne'
  have hN : (N:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr ((Nat.zero_le D).trans_lt (mem_Ioc.mp hd'.1).1 |>.trans_le (mem_Ioc.mp hd'.1).2).ne'
  rw [hd'.2]
  field_simp [hd0,hN]

#print axioms reciprocal_octave_large_divisor_cells
#print axioms reciprocal_octave_finite_floor_subtraction
#print axioms octave_atom_weighted_prefix
#print axioms reciprocal_octave_divisor_identity
#print axioms reciprocal_mangoldt_octave_moebius
end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
