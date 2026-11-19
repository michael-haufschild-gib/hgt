import GaloisForLFunctions.SignedArithmeticCorrespondences.CompletingTheMixedIntersectionInWeightedVariation
import GaloisForLFunctions.RHTower.Sieve.MoebiusScaledReindex

/-!
# The full mixed Weil form on interleaving integral divisors

Present both divisors by upper endpoint jumps. The continuum parts of the two
directed arithmetic heights are exactly the two degrees in the full Weil form.
Both directions of the prime error glue at the same quotient. The off-diagonal
jets glue separately in one polynomial whose monomials record sums and differences
of the conductors. The counterterm occurs precisely on their common support.
-/

noncomputable section
namespace GaloisForLFunctions.SignedArithmeticCorrespondences

open Finset ArithmeticCastelnuovoSeveri AbsoluteGeometryOfSpecZ HodgeTheoryOfAFixedPart _root_.RHTower
open MeasureTheory
open scoped ArithmeticFunction.vonMangoldt NNReal

private theorem upper_zero_above (N : ℕ) (b : ℕ → ℤ) {m : ℕ} (hm : N < m) :
    upperDivisor N b m = 0 := by
  refine sum_eq_zero fun j hj => ?_
  exact if_neg (not_le.mpr ((mem_Icc.mp hj).2.trans_lt hm))

private theorem upper_degree (N : ℕ) (b : ℕ → ℤ) :
    degTwo (Icc 1 N) (fun m => (upperDivisor N b m:ℝ)) = ∑ j ∈ Icc 1 N, (b j:ℝ)*j := by
  simp only [degTwo,upperDivisor,Int.cast_sum]
  rw [sum_comm]
  refine sum_congr rfl fun j hj => ?_
  have hc (m : ℕ) : ((if m≤j then b j else 0 : ℤ):ℝ) = if m≤j then (b j:ℝ) else 0 := by
    by_cases h : m≤j <;> simp [h]
  simp only [hc,← sum_filter]
  have he : (Icc 1 N).filter (fun m => m≤j) = Icc 1 j := by
    ext m
    simp only [mem_filter,mem_Icc]
    have := (mem_Icc.mp hj).2
    omega
  rw [he,sum_const,Nat.card_Icc,nsmul_eq_mul]
  simp [mul_comm]

private def directedLength (i m : ℕ) : ℝ := if i ∣ m then Λ (m/i) else 0

private theorem height_eq_directed (N : ℕ) (u b : ℕ → ℤ) :
    signedDivisorHeight 1 N N u (upperDivisor N b) =
      ∑ i ∈ Icc 1 N, ∑ m ∈ Icc 1 N, (u i:ℝ)*upperDivisor N b m*directedLength i m := by
  rw [signedDivisorHeight_eq Nat.zero_lt_one]
  refine sum_congr rfl fun i hi => ?_
  have hi0 := (mem_Icc.mp hi).1
  simp only [directedLength,mul_ite,mul_zero,← sum_filter,
    Sieve.sum_filter_dvd_eq_sum_scaled hi0,Nat.mul_div_cancel_left _ hi0]
  symm
  apply sum_subset (Icc_subset_Icc_right (Nat.div_le_self N i))
  intro q hq hcut
  have hgt : N < i*q := by
    apply lt_of_not_ge
    intro h
    exact hcut (mem_Icc.mpr ⟨(mem_Icc.mp hq).1,(Nat.le_div_iff_mul_le hi0).mpr (by simpa only [Nat.mul_comm] using h)⟩)
  rw [upper_zero_above N b hgt,Int.cast_zero,mul_zero,zero_mul]

private theorem both_contacts (N : ℕ) (a b : ℕ → ℤ) :
    let u := upperDivisor N a
    let v := upperDivisor N b
    (∑ n ∈ Icc 1 N, ∑ m ∈ (Icc 1 N).erase n, (u m:ℝ)*v n*HodgeTheoryOfAFixedPart.contact m n) =
      signedDivisorHeight 1 N N u v + signedDivisorHeight 1 N N v u := by
  intro u v
  have hdiag (n : ℕ) (hn : n ∈ Icc 1 N) :
      (u n:ℝ)*v n*HodgeTheoryOfAFixedPart.contact n n = 0 := by
    simp [HodgeTheoryOfAFixedPart.contact,Nat.div_self (mem_Icc.mp hn).1]
  have he : (∑ n ∈ Icc 1 N, ∑ m ∈ (Icc 1 N).erase n,
      (u m:ℝ)*v n*HodgeTheoryOfAFixedPart.contact m n) =
      ∑ n ∈ Icc 1 N, ∑ m ∈ Icc 1 N, (u m:ℝ)*v n*HodgeTheoryOfAFixedPart.contact m n :=
    sum_congr rfl fun n hn => sum_erase _ (hdiag n hn)
  rw [he,height_eq_directed N u b,height_eq_directed N v a]
  change (∑ n ∈ Icc 1 N, ∑ m ∈ Icc 1 N, (u m:ℝ)*v n*(directedLength m n+directedLength n m)) = _
  simp only [mul_add,sum_add_distrib]
  congr 1
  · exact sum_comm
  · refine sum_congr rfl fun n _ => sum_congr rfl fun m _ => ?_
    change (u m:ℝ)*v n*directedLength n m = (v n:ℝ)*u m*directedLength n m
    ring

private def jetMonomial (m n : ℕ) (x : ℝ) : ℝ := x^(max m n-min m n-1)+x^(m+n-1)

private theorem jet_monomial_integral {m n : ℕ} (hm : 1 ≤ m) (hn : 1≤n) (hme : m≠n) :
    (∫ x in (0:ℝ)..1, jetMonomial m n x) = 2*jetKernel m n := by
  let k := max m n-min m n
  have hk : 1 ≤ k := by dsimp [k]; omega
  have hcast (j : ℕ) (hj : 1≤j) : (((j-1:ℕ):ℝ)+1) = j := by rw [Nat.cast_sub hj,Nat.cast_one]; ring
  have he : (k:ℝ) = |(m:ℝ)-n| := by
    rcases le_total m n with h | h
    · have h' : (m:ℝ) ≤ n := by exact_mod_cast h
      simp only [k,max_eq_right h,min_eq_left h,Nat.cast_sub h,abs_of_nonpos (sub_nonpos.mpr h')]
      ring
    · have h' : (n:ℝ) ≤ m := by exact_mod_cast h
      simp only [k,max_eq_left h,min_eq_right h,Nat.cast_sub h,abs_of_nonneg (sub_nonneg.mpr h')]
  change (∫ x in (0:ℝ)..1, x^(k-1)+x^(m+n-1)) = _
  rw [intervalIntegral.integral_add (f := fun x : ℝ => x^(k-1)) (g := fun x : ℝ => x^(m+n-1))
    (Continuous.intervalIntegrable (by fun_prop) _ _) (Continuous.intervalIntegrable (by fun_prop) _ _),
    hilbertMoment_eq_integral_pow,hilbertMoment_eq_integral_pow,hcast k hk,hcast (m+n) (by omega),
    he,Nat.cast_add,jetKernel]
  ring

/-- Signed sum of the off-diagonal real jets, grouped by their exponents
before taking a norm. The diagonal singularity is excluded in both monomials. -/
def mixedJetSection (N : ℕ) (a b : ℕ → ℤ) (x : ℝ) : ℝ :=
  ∑ n ∈ Icc 1 N, ∑ m ∈ (Icc 1 N).erase n, (upperDivisor N a m:ℝ)*upperDivisor N b n*jetMonomial m n x

private theorem mixed_jet_integral (N : ℕ) (a b : ℕ → ℤ) :
    (∫ x in (0:ℝ)..1, mixedJetSection N a b x) =
      2*∑ n ∈ Icc 1 N, ∑ m ∈ (Icc 1 N).erase n, (upperDivisor N a m:ℝ)*upperDivisor N b n*jetKernel m n := by
  unfold mixedJetSection
  simp only [mul_sum]
  rw [intervalIntegral.integral_finsetSum (fun n _ => Continuous.intervalIntegrable (by unfold jetMonomial; fun_prop) _ _)]
  refine sum_congr rfl fun n hn => ?_
  rw [intervalIntegral.integral_finsetSum (fun m _ => Continuous.intervalIntegrable (by unfold jetMonomial; fun_prop) _ _)]
  refine sum_congr rfl fun m hm => ?_
  rw [intervalIntegral.integral_const_mul,jet_monomial_integral (mem_Icc.mp (mem_erase.mp hm).2).1
    (mem_Icc.mp hn).1 (mem_erase.mp hm).1]
  ring

/-- Mixed Weil form minus the two fractional boundaries and the common diagonal. -/
def interleavedFinitePart (N : ℕ) (a b : ℕ → ℤ) : ℝ :=
  let u := upperDivisor N a
  let v := upperDivisor N b
  formBilin (Icc 1 N) (fun m => (u m:ℝ)) (fun n => (v n:ℝ)) -
    fractionalBoundary N N u b - fractionalBoundary N N v a -
      ∑ n ∈ Icc 1 N, (u n:ℝ)*v n*counterterm n

/-- The same quotient can arise in either direction of contact. -/
def twoSidedCoefficient (N : ℕ) (a b : ℕ → ℤ) (k : ℕ) : ℝ :=
  quotientCoefficient N N (upperDivisor N a) b k + quotientCoefficient N N (upperDivisor N b) a k

/-- Exact finite part on arbitrary interleaving signed supports. The arithmetic
term sees the sum of both quotient profiles. The real term is one signed polynomial. -/
theorem interleaved_finite_part (N : ℕ) (a b : ℕ → ℤ) :
    interleavedFinitePart N a b =
      -(∑ k ∈ range (N+1), twoSidedCoefficient N a b k*psiRemainder k) -
      (∫ x in (0:ℝ)..1, mixedJetSection N a b x)/2 := by
  let u := upperDivisor N a
  let v := upperDivisor N b
  have h1 := mixed_height_finite_part N N u b
  have h2 := mixed_height_finite_part N N v a
  have hc := both_contacts N a b
  have hj := mixed_jet_integral N a b
  have hp1 : degOne (Icc 1 N) (fun m => (u m:ℝ)) * degTwo (Icc 1 N) (fun n => (v n:ℝ)) =
      poleProduct N N u b := by rw [upper_degree]; rfl
  have hp2 : degTwo (Icc 1 N) (fun m => (u m:ℝ)) * degOne (Icc 1 N) (fun n => (v n:ℝ)) =
      poleProduct N N v a := by rw [mul_comm,upper_degree]; rfl
  simp only [interleavedFinitePart,formBilin,combBilin,HodgeTheoryOfAFixedPart.pairKernel,mul_add,
    twoSidedCoefficient,add_mul,sum_add_distrib]
  dsimp only at hc
  dsimp only [u,v] at h1 h2 hp1 hp2
  linarith only [h1,h2,hc,hj,hp1,hp2]

/-- The de la Vallée Poussin bound for the full mixed form on every support,
with an independent L¹ error for the single real-place section. -/
theorem interleaved_de_la_vallee_poussin :
    ∃ c C : ℝ, 0<c ∧ 0≤C ∧ ∀ (N : ℕ) (a b : ℕ → ℤ),
      |interleavedFinitePart N a b| ≤ C*(∑ k ∈ range (N+1), |twoSidedCoefficient N a b k| *
        ((k:ℝ)*Real.exp (-c*Real.sqrt (Real.log k)))) + (∫ x in (0:ℝ)..1, |mixedJetSection N a b x|)/2 := by
  obtain ⟨c,C,hc,hC,h⟩ := mixed_height_de_la_vallee_poussin
  let W (k : ℕ) : ℝ≥0 := ⟨(k:ℝ)*Real.exp (-c*Real.sqrt (Real.log k)),by positivity⟩
  have hb := (mixed_height_budget_iff W ⟨C,hC⟩).1 h
  have he (k : ℕ) : |psiRemainder k| ≤ C*(W k:ℝ) := by
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · rw [show psiRemainder 0 = 0 by simp [psiRemainder,chebyshevPsi],abs_zero]
      exact mul_nonneg hC (W 0).coe_nonneg
    · exact hb k hk
  refine ⟨c,C,hc,hC,fun N a b => ?_⟩
  have hfin : |∑ k ∈ range (N+1), twoSidedCoefficient N a b k*psiRemainder k| ≤
      C*∑ k ∈ range (N+1), |twoSidedCoefficient N a b k| * (W k:ℝ) := by
    rw [mul_sum]
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun k _ => ?_)
    rw [abs_mul,mul_left_comm]
    exact mul_le_mul_of_nonneg_left (he k) (abs_nonneg _)
  have hreal := intervalIntegral.abs_integral_le_integral_abs (μ := volume)
    (f := mixedJetSection N a b) zero_le_one
  rw [interleaved_finite_part,sub_eq_add_neg]
  refine (abs_add_le _ _).trans ?_
  rw [abs_neg,abs_neg,abs_div,abs_of_pos (by norm_num : (0:ℝ)<2)]
  exact add_le_add hfin (div_le_div_of_nonneg_right hreal (by norm_num))

/-- Distance from the full mixed form to a completed intersection. Both
divisors may change with the support. The prime profiles converge in weighted
variation and the real sections in L¹, with no ordering of the two supports. -/
theorem interleaved_distance_to_completion :
    ∃ c C : ℝ, 0<c ∧ 0≤C ∧ ∀ (N : ℕ) (a b : ℕ → ℤ) (s : ℕ → ℝ) (g : ℝ → ℝ),
      let w := fun k : ℕ => (k:ℝ)*Real.exp (-c*Real.sqrt (Real.log k))
      Summable (fun k => |s k| * w k) → IntervalIntegrable g volume 0 1 →
      |interleavedFinitePart N a b - (-(∑' k, s k*psiRemainder k) - (∫ x in (0:ℝ)..1, g x)/2)| ≤
        C*(∑' k, |twoSidedCoefficient N a b k-s k| * w k) +
        (∫ x in (0:ℝ)..1, |mixedJetSection N a b x-g x|)/2 := by
  obtain ⟨c,C,hc,hC,hpair⟩ := completed_endpoint_de_la_vallee_poussin
  refine ⟨c,C,hc,hC,fun N a b s g => ?_⟩
  intro w hs hg
  let q := twoSidedCoefficient N a b
  have hq {k : ℕ} (hk : k ∉ range (N+1)) : q k=0 := by
    have hgt : N<k := by simpa only [mem_range,not_lt,Nat.succ_le_iff] using hk
    simp only [q,twoSidedCoefficient,quotientCoefficient_eq_zero hgt,zero_add]
  have hw (k : ℕ) : 0 ≤ w k := mul_nonneg (Nat.cast_nonneg _) (Real.exp_pos _).le
  have hqa : Summable (fun k => |q k| * w k) :=
    summable_of_ne_finset_zero (s := range (N+1)) fun k hk => by simp [hq hk]
  have hd : Summable (fun k => |q k-s k| * w k) := by
    refine Summable.of_nonneg_of_le (fun k => mul_nonneg (abs_nonneg _) (hw k)) ?_ (hqa.add hs)
    intro k
    have he : |q k-s k| ≤ |q k|+|s k| := by
      simpa only [sub_eq_add_neg,abs_neg] using abs_add_le (q k) (-s k)
    simpa only [Pi.add_apply,← add_mul] using mul_le_mul_of_nonneg_right he (hw k)
  have hfin : (∑' k, q k*psiRemainder k) = ∑ k ∈ range (N+1), q k*psiRemainder k :=
    tsum_eq_sum fun k hk => by simp [hq hk]
  have hp : |(∑ k ∈ range (N+1), q k*psiRemainder k) - ∑' k, s k*psiRemainder k| ≤
      C*∑' k, |q k-s k| * w k := by
    rw [← hfin, ← (hpair q hqa).1.tsum_sub (hpair s hs).1]
    simpa only [sub_mul] using (hpair (fun k => q k-s k) hd).2
  let G := mixedJetSection N a b
  have hG : IntervalIntegrable G volume 0 1 := by
    apply Continuous.intervalIntegrable
    change Continuous (fun x : ℝ => ∑ n ∈ Icc 1 N, ∑ m ∈ (Icc 1 N).erase n,
      (upperDivisor N a m:ℝ)*upperDivisor N b n*(x^(max m n-min m n-1)+x^(m+n-1)))
    fun_prop
  have hr := intervalIntegral.abs_integral_le_integral_abs (μ := volume)
    (f := fun x => G x-g x) zero_le_one
  rw [intervalIntegral.integral_sub hG hg] at hr
  rw [interleaved_finite_part]
  let S := ∑ k ∈ range (N+1), q k*psiRemainder k
  let T := ∑' k, s k*psiRemainder k
  change |(-S-(∫ x in (0:ℝ)..1, G x)/2)-(-T-(∫ x in (0:ℝ)..1, g x)/2)| ≤ _
  rw [show (-S-(∫ x in (0:ℝ)..1, G x)/2)-(-T-(∫ x in (0:ℝ)..1, g x)/2) =
    -((S-T)+((∫ x in (0:ℝ)..1, G x)-(∫ x in (0:ℝ)..1, g x))/2) by ring,abs_neg]
  refine (abs_add_le _ _).trans ?_
  rw [abs_div,abs_of_pos (by norm_num : (0:ℝ)<2)]
  exact add_le_add hp (div_le_div_of_nonneg_right hr (by norm_num))

#print axioms interleaved_distance_to_completion
#print axioms interleaved_finite_part
#print axioms interleaved_de_la_vallee_poussin

end GaloisForLFunctions.SignedArithmeticCorrespondences
