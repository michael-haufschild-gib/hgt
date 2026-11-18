import GaloisForLFunctions.ExceptionalLayerTheory.ThePositivePrimeFactorialCountHasASquareRootError
import GaloisForLFunctions.ExceptionalLayerTheory.TheOrdinaryPrimesSeparateSignedQuotientProfiles
import GaloisForLFunctions.RHTower.Sieve.GuthMaynardPropTenOneBlocks
import GaloisForLFunctions.RHTower.SmoothAFECutoffSum

/-!
# Square-root rounding on powerful divisors

A bounded multiplicative correction vanishing at primes is supported on
products of a square and a cube. Along each square row the absolute floor
errors admit a telescoping majorant. The remaining cube sum converges.
-/

noncomputable section

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open _root_.RHTower.Sieve

namespace GaloisForLFunctions.ExceptionalLayerTheory

private theorem powerful_split {f : ArithmeticFunction ℝ} (hf : f.IsMultiplicative)
    (hp : ∀ p : ℕ, p.Prime → f p=0) (n : ℕ) (hn : f n≠0) :
    ∃ a b : ℕ, 0<a ∧ 0<b ∧ n=a^2*b^3 := by
  induction n using Nat.recOnPosPrimePosCoprime with
  | zero => simp at hn
  | one => exact ⟨1,1,Nat.zero_lt_one,Nat.zero_lt_one,by simp⟩
  | prime_pow p k hpr hk =>
    have hk1 : k≠1 := by rintro rfl; exact hn (by rw [pow_one,hp p hpr])
    by_cases he : k%2=0
    · refine ⟨p^(k/2),1,pow_pos hpr.pos _,Nat.zero_lt_one,?_⟩
      rw [one_pow,mul_one,← pow_mul,show k/2*2=k by omega]
    · refine ⟨p^((k-3)/2),p,pow_pos hpr.pos _,hpr.pos,?_⟩
      rw [← pow_mul,← pow_add,show (k-3)/2*2+3=k by omega]
  | coprime x y _ _ hxy ix iy =>
    rw [hf.map_mul_of_coprime hxy] at hn
    obtain ⟨a,b,ha,hb,he⟩ := ix (left_ne_zero_of_mul hn)
    obtain ⟨c,d,hc,hd,hg⟩ := iy (right_ne_zero_of_mul hn)
    refine ⟨a*c,b*d,Nat.mul_pos ha hc,Nat.mul_pos hb hd,?_⟩
    rw [he,hg]; ring

private theorem square_row_step {u a : ℝ} (hu : 0<u) (ha : 1≤a) :
    min 1 (u^2/a^2) ≤ 4*u^2*(1/(u+a-1)-1/(u+a)) := by
  have ha0 : 0<a := zero_lt_one.trans_le ha
  have hd : 0<u+a-1 := by linarith only [hu,ha]
  have ht : 0<u+a := add_pos hu ha0
  calc
    _ ≤ 4*u^2/(u+a)^2 := by
      rcases le_total a u with h | h
      · apply (min_le_left ..).trans
        rw [le_div_iff₀ (sq_pos_of_pos ht),one_mul]
        have hsq := (sq_le_sq₀ ht.le (by positivity : 0≤2*u)).mpr (by linarith only [h])
        linarith only [hsq,show (2*u)^2=4*u^2 by ring]
      · apply (min_le_right ..).trans
        rw [div_le_div_iff₀ (sq_pos_of_pos ha0) (sq_pos_of_pos ht)]
        have hsq := (sq_le_sq₀ ht.le (by positivity : 0≤2*a)).mpr (by linarith only [h])
        calc
          _ ≤ u^2*(2*a)^2 := mul_le_mul_of_nonneg_left hsq (sq_nonneg _)
          _ = _ := by ring
    _ ≤ 4*u^2/((u+a-1)*(u+a)) := by
      apply div_le_div_of_nonneg_left (by positivity) (mul_pos hd ht)
      rw [pow_two]
      exact mul_le_mul_of_nonneg_right (by linarith only : u+a-1≤u+a) ht.le
    _ = _ := by field_simp [hd.ne',ht.ne']; ring

private theorem square_row_bound {u : ℝ} (hu : 0<u) (J : ℕ) :
    ∑ j ∈ range J, min 1 (u^2/((j:ℝ)+1)^2) ≤ 4*u := by
  have h (L : ℕ) : (∑ j ∈ range L, min 1 (u^2/((j:ℝ)+1)^2)) ≤
      4*u-4*u^2/(u+(L:ℝ)) := by
    induction L with
    | zero => simp only [range_zero,sum_empty,Nat.cast_zero,add_zero]; field_simp [hu.ne'] <;> nlinarith only
    | succ L ih =>
      rw [Finset.sum_range_succ,Nat.cast_succ]
      have hs := square_row_step hu (a := (L:ℝ)+1) (by linarith only [Nat.cast_nonneg (α := ℝ) L])
      rw [show u+((L:ℝ)+1)-1=u+L by ring] at hs
      exact (add_le_add ih hs).trans_eq (by ring)
  exact (h J).trans (sub_le_self _ (by positivity))

private theorem floor_error_min (N d : ℕ) (hd : 0<d) :
    |((N/d:ℕ):ℝ)-(N:ℝ)/d| ≤ min 1 ((N:ℝ)/d) := by
  have h := Nat.cast_div_le (α := ℝ) (m := N) (n := d)
  rw [abs_of_nonpos (sub_nonpos.mpr h)]
  have hdr : 0<(d:ℝ) := by exact_mod_cast hd
  have hu : (N:ℝ)/d<((N/d:ℕ):ℝ)+1 := (div_lt_iff₀ hdr).mpr (by
    exact_mod_cast (Nat.div_lt_iff_lt_mul hd).mp (Nat.lt_succ_self (N/d)))
  exact le_min (by linarith only [hu]) (by linarith only [Nat.cast_nonneg (α := ℝ) (N/d)])

private def cubeScale (N j : ℕ) : ℝ :=
  Real.sqrt N/(((j:ℝ)+1)*Real.sqrt ((j:ℝ)+1))

private theorem cubeScale_sq (N a b : ℕ) :
    (N:ℝ)/(((a:ℝ)+1)^2*((b:ℝ)+1)^3) = (cubeScale N b)^2/((a:ℝ)+1)^2 := by
  rw [cubeScale,div_pow,mul_pow,Real.sq_sqrt (Nat.cast_nonneg N),Real.sq_sqrt (by positivity),div_div]
  congr 1; ring

private def squareCubeMajorant (N : ℕ) (z : ℕ×ℕ) : ℝ :=
  min 1 ((cubeScale N z.1)^2/((z.2:ℝ)+1)^2)

private theorem squareCubeMajorant_nonneg (N : ℕ) (z : ℕ×ℕ) : 0≤squareCubeMajorant N z :=
  le_min zero_le_one (by positivity)

private theorem squareCubeMajorant_sum {N : ℕ} (hN : 0<N) (J : ℕ) :
    ∑ z ∈ range J ×ˢ range J, squareCubeMajorant N z ≤ 12*Real.sqrt N := by
  rw [sum_product]
  calc
    _ ≤ ∑ b ∈ range J, 4*cubeScale N b := by
      refine sum_le_sum fun b _ => ?_
      have hu : 0<cubeScale N b := div_pos (Real.sqrt_pos.mpr (by exact_mod_cast hN)) (by positivity)
      exact square_row_bound (u := cubeScale N b) hu J
    _ = (4*Real.sqrt N)*(∑ b ∈ range J, (((b:ℝ)+1)*Real.sqrt ((b:ℝ)+1))⁻¹) := by
      rw [mul_sum]
      exact sum_congr rfl fun _ _ => by dsimp only [cubeScale]; ring
    _ ≤ _ := (mul_le_mul_of_nonneg_left (_root_.RHTower.sum_range_inv_sqrt_cube_le J)
      (by positivity : 0≤4*Real.sqrt N)).trans_eq (by ring)

/-- The sum of the absolute floor errors for a bounded multiplicative weight
vanishing on every prime is at most twelve square roots. -/
theorem powerful_divisor_rounding_le {f : ArithmeticFunction ℝ} (hf : f.IsMultiplicative)
    (hpr : ∀ p : ℕ, p.Prime → f p=0) (h1 : ∀ n : ℕ, |f n|≤1) (N : ℕ) :
    ∑' d : ℕ, |f d*(((N/d:ℕ):ℝ)-(N:ℝ)/d)| ≤ 12*Real.sqrt N := by
  classical
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  have hs (d : ℕ) (hd : f d≠0) : ∃ x : ℕ×ℕ, d=(x.2+1)^2*(x.1+1)^3 := by
    obtain ⟨a,b,ha,hb,he⟩ := powerful_split hf hpr d hd
    exact ⟨(b-1,a-1),by simpa only [Nat.sub_add_cancel ha,Nat.sub_add_cancel hb] using he⟩
  let φ (d : ℕ) := if hd : f d≠0 then (hs d hd).choose else (0,0)
  have spec (d : ℕ) (hd : f d≠0) : d=((φ d).2+1)^2*((φ d).1+1)^3 := by
    simpa only [φ,dif_pos hd] using (hs d hd).choose_spec
  let F (d : ℕ) := |f d*(((N/d:ℕ):ℝ)-(N:ℝ)/d)|
  refine Real.tsum_le_of_sum_range_le (fun d => abs_nonneg _) (fun M => ?_)
  let S := (range M).filter (fun d => f d≠0)
  let J := 1+∑ d ∈ S, ((φ d).1+(φ d).2)
  have hJ (d : ℕ) (hd : d∈S) : (φ d).1+(φ d).2<J := by
    have he := single_le_sum (fun i (_ : i∈S) => Nat.zero_le ((φ i).1+(φ i).2)) hd
    dsimp only [J]; omega
  have hinj : Set.InjOn φ ↑S := by
    intro m hm n hn e
    exact (spec m (mem_filter.mp hm).2).trans ((congrArg
      (fun x : ℕ×ℕ => (x.2+1)^2*(x.1+1)^3) e).trans (spec n (mem_filter.mp hn).2).symm)
  have hg (d : ℕ) (hd : d∈S) : F d≤squareCubeMajorant N (φ d) := by
    have hs' := spec d (mem_filter.mp hd).2
    have hd0 : 0<d := by rw [hs']; positivity
    dsimp only [F,squareCubeMajorant]
    rw [abs_mul]
    apply (mul_le_of_le_one_left (abs_nonneg _) (h1 d)).trans
    have ht := floor_error_min N d hd0
    apply ht.trans_eq
    congr 1
    nth_rw 1 [hs']
    push_cast
    exact cubeScale_sq N _ _
  change (∑ d ∈ range M, F d)≤_
  calc
    _ = ∑ d ∈ S, F d := by
      rw [show S=(range M).filter (fun d => f d≠0) from rfl,sum_filter]
      exact sum_congr rfl fun d _ => by by_cases hd : f d=0 <;> simp [hd,F]
    _ ≤ ∑ z ∈ range J ×ˢ range J, squareCubeMajorant N z :=
      _root_.RHTower.GuthMaynard.sum_le_sum_of_injOn hinj
        (fun d hd => by have := hJ d hd; exact mem_product.mpr ⟨mem_range.mpr (by omega),mem_range.mpr (by omega)⟩)
        (fun z _ => squareCubeMajorant_nonneg N z) hg
    _ ≤ _ := squareCubeMajorant_sum hN J

private theorem correction_bounds :
    (∀ p : ℕ, p.Prime → (reciprocalFactorial*(μ:ArithmeticFunction ℝ)) p=0) ∧
    ∀ n : ℕ, |(reciprocalFactorial*(μ:ArithmeticFunction ℝ)) n|≤1 := by
  let h := reciprocalFactorial*(μ:ArithmeticFunction ℝ)
  have hv : reciprocalFactorial.IsMultiplicative := localEuler_isMultiplicative _
  have hm : h.IsMultiplicative := hv.mul isMultiplicative_moebius.intCast
  have hi (n : ℕ) : 0≤reciprocalFactorial n ∧ reciprocalFactorial n≤1 := by
    rw [← abs_factorialParityWeight]; exact ⟨abs_nonneg _,abs_factorialParityWeight_le_one n⟩
  have hp (p : ℕ) (hpr : p.Prime) (j : ℕ) : h (p^(j+1)) =
      reciprocalFactorial (p^(j+1))-reciprocalFactorial (p^j) :=
    GaloisForLFunctions.TransHorizonIncidenceMechanics.mul_moebius_apply_prime_pow _ hpr j
  constructor
  · intro p hpr
    have h₁ : reciprocalFactorial p=1 := by simpa using reciprocalFactorial_pow hpr 1
    simpa only [Nat.zero_add,pow_one,pow_zero,h₁,hv.map_one,sub_self] using hp p hpr 0
  · intro n
    change |h n|≤1
    induction n using Nat.recOnPosPrimePosCoprime with
    | zero => simp
    | one => rw [hm.map_one,abs_one]
    | prime_pow p k hpr hk =>
      obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
      rw [hp p hpr j,abs_le]
      exact ⟨by linarith only [(hi (p^(j+1))).1,(hi (p^j)).2],
        by linarith only [(hi (p^(j+1))).2,(hi (p^j)).1]⟩
    | coprime a b _ _ hc ia ib =>
      rw [hm.map_mul_of_coprime hc,abs_mul]
      exact (mul_le_mul ia ib (abs_nonneg _) zero_le_one).trans_eq (one_mul _)

/-- The positive factorial partial sum has a square-root error at the endpoint. -/
theorem reciprocalFactorial_sum_sqrt_error (N : ℕ) :
    |(∑ n ∈ Icc 1 N, reciprocalFactorial n)-(N:ℝ)*reciprocalFactorialDensity| ≤ 12*Real.sqrt N := by
  have hv : reciprocalFactorial.IsMultiplicative := localEuler_isMultiplicative _
  have he := hasSum_reciprocalFactorial_rounding N
  rw [← he.tsum_eq,← Real.norm_eq_abs]
  exact (norm_tsum_le_tsum_norm he.summable.norm).trans (by
    simpa only [Real.norm_eq_abs] using powerful_divisor_rounding_le
      (hv.mul isMultiplicative_moebius.intCast) correction_bounds.1 correction_bounds.2 N)

/-- The absolute factorial profile of the ordinary primes has the same
square-root error at every positive cutoff. -/
theorem prime_sum_absolute_divided_weight_sqrt_error {N : ℕ} (hn : 1≤N) :
    |(∑ p ∈ Nat.primesLE N, ∑ m ∈ Icc 1 (N/p), |dividedFactorialParityWeight m|)
        - ((N:ℝ)*reciprocalFactorialDensity-1)| ≤ 12*Real.sqrt N := by
  rw [prime_sum_absolute_divided_weight hn,sub_sub_sub_cancel_right]
  exact reciprocalFactorial_sum_sqrt_error N

private def positiveFactorialPrefix (N : ℕ) : ℝ :=
  ∑ n ∈ Icc 1 N, |dividedFactorialParityWeight n|

/-- The dyadic difference of the positive factorial profile. -/
def dyadicPositiveFactorialProfile (N : ℕ) : ℝ :=
  positiveFactorialPrefix N-2*positiveFactorialPrefix (N/2)

private theorem positiveFactorialPrefix_bounds (N : ℕ) :
    0≤positiveFactorialPrefix N ∧ positiveFactorialPrefix N≤N := by
  refine ⟨sum_nonneg (fun _ _ => abs_nonneg _),?_⟩
  exact (sum_le_sum (fun n (_ : n∈Icc 1 N) => abs_dividedFactorialParityWeight_le_one n)).trans_eq (by simp)

theorem dyadicPositiveFactorialProfile_one : dyadicPositiveFactorialProfile 1=1 := by
  simp [dyadicPositiveFactorialProfile,positiveFactorialPrefix,dividedFactorialParityWeight,factorialParityWeight]

theorem abs_dyadicPositiveFactorialProfile_le (n : ℕ) : |dyadicPositiveFactorialProfile n|≤2*n := by
  have hn := positiveFactorialPrefix_bounds n
  have hd := positiveFactorialPrefix_bounds (n/2)
  have hdiv := Nat.cast_div_le (α := ℝ) (m := n) (n := 2)
  change |_ - 2*_|≤_
  rw [abs_le]
  push_cast at hdiv
  constructor <;> linarith only [hn.1,hn.2,hd.1,hd.2,hdiv,Nat.cast_nonneg (α := ℝ) n]

private theorem prime_sum_halving (f : ℕ → ℝ) (h₀ : f 0=0) (N : ℕ) :
    (∑ p ∈ Nat.primesLE N, f ((N/p)/2))=∑ p ∈ Nat.primesLE (N/2), f ((N/2)/p) := by
  have hr (p : ℕ) : (N/p)/2=(N/2)/p := by rw [Nat.div_div_eq_div_mul,Nat.div_div_eq_div_mul,mul_comm p 2]
  simp_rw [hr]
  apply (sum_subset (Nat.primesLE_mono (Nat.div_le_self N 2)) ?_).symm
  intro p hp hs
  have hpr := (Nat.mem_primesLE.mp hp).2
  have hlt : N/2<p := lt_of_not_ge (fun h => hs (Nat.mem_primesLE.mpr ⟨h,hpr⟩))
  rwa [Nat.div_eq_of_lt hlt]

/-- At every positive even cutoff the dyadic profile subtracts two copies
of the factorial sum at half the cutoff. -/
theorem dyadicPositiveFactorialProfile_prime_sum_even {N : ℕ} (hn : 1≤N) :
    (∑ p ∈ Nat.primesLE (2*N), dyadicPositiveFactorialProfile (2*N/p)) =
      ((∑ n ∈ Icc 1 (2*N), reciprocalFactorial n)-1)-
        2*((∑ n ∈ Icc 1 N, reciprocalFactorial n)-1) := by
  simp only [dyadicPositiveFactorialProfile,sum_sub_distrib,← mul_sum]
  rw [prime_sum_halving _ (by simp [positiveFactorialPrefix]),Nat.mul_div_cancel_left _ (by decide : 0<2)]
  exact congrArg₂ (fun a b : ℝ => a-2*b)
    (prime_sum_absolute_divided_weight (show 1≤2*N by omega)) (prime_sum_absolute_divided_weight hn)

/-- A nonzero uncentered profile whose ordinary prime sum saves all the
way to the square root, with no zero-free input. -/
theorem dyadicPositiveFactorialProfile_prime_sqrt_bound {N : ℕ} (hN : 1≤N) :
    |∑ p ∈ Nat.primesLE N, dyadicPositiveFactorialProfile (N/p)| ≤
      (37+reciprocalFactorialDensity)*Real.sqrt N := by
  have hc := reciprocalFactorialDensity_pos.le
  rcases eq_or_lt_of_le hN with h | hn
  · subst N
    have hz : Nat.primesLE 1=∅ := eq_empty_iff_forall_notMem.mpr fun p hp =>
      (Nat.mem_primesLE.mp hp).2.not_le_one (Nat.mem_primesLE.mp hp).1
    rw [hz,sum_empty,abs_zero,Nat.cast_one,Real.sqrt_one,mul_one]
    linarith only [hc]
  have hd : 1≤N/2 := by omega
  let E (k : ℕ) := (∑ p ∈ Nat.primesLE k, positiveFactorialPrefix (k/p))-
    ((k:ℝ)*reciprocalFactorialDensity-1)
  have he (k : ℕ) (hk : 1≤k) : |E k|≤12*Real.sqrt k :=
    prime_sum_absolute_divided_weight_sqrt_error hk
  have heq : (∑ p ∈ Nat.primesLE N, dyadicPositiveFactorialProfile (N/p)) =
      (E N-2*E (N/2))+(1+(N%2:ℕ)*reciprocalFactorialDensity) := by
    simp only [dyadicPositiveFactorialProfile,sum_sub_distrib,← mul_sum]
    rw [prime_sum_halving _ (by simp [positiveFactorialPrefix])]
    have hr : ((N%2:ℕ):ℝ)+2*((N/2:ℕ):ℝ)=N := by exact_mod_cast Nat.mod_add_div N 2
    dsimp only [E]
    linear_combination -reciprocalFactorialDensity * hr
  have hp : 0≤1+((N%2:ℕ):ℝ)*reciprocalFactorialDensity := by positivity
  have hmod : ((N%2:ℕ):ℝ)≤1 := by exact_mod_cast (show N%2≤1 by omega)
  have herr : |E N-2*E (N/2)|≤36*Real.sqrt N := by
    apply (abs_sub _ _).trans
    rw [abs_mul,abs_of_nonneg (by norm_num : (0:ℝ)≤2)]
    have hr := Real.sqrt_le_sqrt (show ((N/2:ℕ):ℝ)≤N by exact_mod_cast Nat.div_le_self N 2)
    linarith only [he N hN,he (N/2) hd,hr]
  have hroot : 1≤Real.sqrt N := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt (by exact_mod_cast hN : (1:ℝ)≤N)
  rw [heq]
  apply (abs_add_le _ _).trans
  rw [abs_of_nonneg hp]
  nlinarith only [herr,mul_le_mul_of_nonneg_right hmod hc,
    mul_le_mul_of_nonneg_left hroot hc,hroot]

/-- Even though its ordinary prime sum has a square-root bound, the profile
itself fails every strictly sublinear power bound. -/
theorem dyadicPositiveFactorialProfile_has_no_sublinear_power {a : ℝ} (ha : 0≤a) (h1 : a<1) :
    ¬∃ C : ℝ, 0≤C ∧ ∀ n : ℕ, 1≤n → |dyadicPositiveFactorialProfile n|≤C*(n:ℝ)^a := by
  intro hf
  have hz := (sublinear_prime_quotient_count_iff_zero dyadicPositiveFactorialProfile ha h1
    (b := 1/2) (by norm_num) (by norm_num) hf).1
    ⟨37+reciprocalFactorialDensity,fun n hn => by
      simpa only [Real.sqrt_eq_rpow] using dyadicPositiveFactorialProfile_prime_sqrt_bound hn⟩ 1 le_rfl
  rw [dyadicPositiveFactorialProfile_one] at hz
  exact one_ne_zero hz

#print axioms dyadicPositiveFactorialProfile_prime_sqrt_bound
#print axioms dyadicPositiveFactorialProfile_has_no_sublinear_power
#print axioms prime_sum_absolute_divided_weight_sqrt_error

end GaloisForLFunctions.ExceptionalLayerTheory
