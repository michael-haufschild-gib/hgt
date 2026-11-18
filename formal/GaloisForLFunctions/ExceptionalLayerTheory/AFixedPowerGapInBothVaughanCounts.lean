import GaloisForLFunctions.ExceptionalLayerTheory.PrimeErrorOnEveryComplementaryTail
import GaloisForLFunctions.ExceptionalLayerTheory.PowerCancellationInTheCompleteDivisorError

/-!
# A fixed power gap in both Vaughan counts

A power saving in the complete divisor error pays for a power-sized
factorial stencil. Enlarging the upper complementary cutoff by the
same power keeps the transposed tail within square-root precision.
-/

noncomputable section
open Finset RHTower
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

/-- Both original widths reproduce themselves at horizons below
`N^(199/200)`. The local error has square-root size uniformly in the
widths after factoring out their finite coefficient mass. -/
theorem fixed_gap_cofactor_descent :
    ∃ K : ℝ, 0≤K ∧ ∀ V W N : ℕ,
      let D := ⌊(N : ℝ)^(1/200 : ℝ)⌋₊
      let M := ⌊(N : ℝ)^(101/200 : ℝ)⌋₊
      |cofactorCountError V W N-∑ v ∈ Ioc D M, innerJump D v*cofactorCountError V W (N/v)| ≤
        (∑ d ∈ Icc 1 W, |Sieve.typeIIShort V d|)*(K*Real.sqrt N) := by
  obtain ⟨B,hB,hdiv⟩ := complete_divisor_error_power
  obtain ⟨H,hH,hmass⟩ := mass_uniform
  let G := 2* |Real.eulerMascheroniConstant|
  have hg : 0≤G := by dsimp [G]; positivity
  let K := 2*H*(B+G+16)
  have hK : 0≤K := by dsimp [K]; positivity
  refine ⟨K,hK,?_⟩
  intro V W N D M
  apply cofactor_descent_majorant
  intro x hxn
  rcases Nat.eq_zero_or_pos x with rfl | hx
  · simp only [Nat.zero_div,Nat.cast_zero,show Chebyshev.psi 0=0 by simp [Chebyshev.psi],
      sub_self,mul_zero,sum_const_zero,abs_zero]; positivity
  have hn : (1 : ℝ)≤N := by exact_mod_cast (show 1≤x from hx).trans hxn
  have hn₀ := zero_lt_one.trans_le hn
  let P (t : ℝ) := (N : ℝ)^t
  have pos (t : ℝ) : 0<P t := Real.rpow_pos_of_pos hn₀ _
  have one {t : ℝ} (ht : 0≤t) : 1≤P t := Real.one_le_rpow hn ht
  have mul (t u : ℝ) : P t*P u=P (t+u) := (Real.rpow_add hn₀ _ _).symm
  have hsmall := (pos (1/200)).le
  have hlarge := (pos (99/200)).le
  have hM : 1≤M := (Nat.one_le_floor_iff _).mpr (one (by norm_num))
  have hD : ((D+1 : ℕ) : ℝ)≤2*P (1/200) := by
    have hl : (D : ℝ)≤P (1/200) := Nat.floor_le (pos _).le
    push_cast; linarith only [hl,one (by norm_num : (0 : ℝ)≤1/200)]
  have hm := (hmass (D+1) (Nat.succ_pos D)).trans (mul_le_mul_of_nonneg_left hD hH)
  have he : (x : ℝ)≤N := by exact_mod_cast hxn
  have hcap : ((x/(M+1) : ℕ) : ℝ)≤P (99/200) := by
    apply Nat.cast_div_le.trans
    apply (div_le_iff₀ (by positivity : (0 : ℝ)<(M+1 : ℕ))).mpr
    have hround : P (101/200)≤((M+1 : ℕ) : ℝ) := by push_cast; exact (Nat.lt_floor_add_one _).le
    have hp : P (99/200)*P (101/200)=N := by rw [mul]; norm_num [P]
    exact he.trans (hp.symm.le.trans (mul_le_mul_of_nonneg_left hround (pos _).le))
  have hfull := complete_primeErrorTail_majorant D hx (B := B*P (99/200)) (fun t ht =>
    (hdiv t).trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg t)
      (by exact_mod_cast ht.trans hxn) (by norm_num)) hB))
  have hnonneg := (abs_nonneg _).trans (abs_prefix_le_mass (Nat.succ_pos D) 0)
  have htail := (primeErrorTail_reciprocal_bound D x hM).trans (mul_le_mul_of_nonneg_left hcap (by positivity))
  rw [prime_error_split_at_cap D M x]
  apply (abs_add_le _ _).trans ((add_le_add hfull htail).trans _)
  have hg' := le_mul_of_one_le_right hg (one (by norm_num : (0 : ℝ)≤99/200))
  have hb : B*P (99/200)+G+16*P (99/200)≤(B+G+16)*P (99/200) := by linarith only [hg']
  have hp : P (1/200)*P (99/200)=Real.sqrt N := by
    rw [mul,show (1/200 : ℝ)+99/200=1/2 by norm_num,Real.sqrt_eq_rpow]
  have hh := mul_le_mul hm hb (by positivity : 0≤B*P (99/200)+G+16*P (99/200)) (by positivity)
  change mass (D+1)*(B*P (99/200)+G)+16*mass (D+1)*P (99/200)≤K*Real.sqrt N
  dsimp only [K]; rw [←hp]; linarith only [hh]

/-- The same strict horizon saving holds for every index of the fixed
descent and does not depend on a target error exponent. -/
theorem fixed_gap_divided_horizon {N v : ℕ} (hN : 1≤N)
    (hv : ⌊(N : ℝ)^(1/200 : ℝ)⌋₊<v) : ((N/v : ℕ) : ℝ)<(N : ℝ)^(199/200 : ℝ) := by
  simpa only [show 1-(1/200 : ℝ)=199/200 by norm_num] using
    divided_horizon_lt_power_of_lt_floor (δ := 1/200) hN hv

end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
