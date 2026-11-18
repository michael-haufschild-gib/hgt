import GaloisForLFunctions.ArithmeticOfSquareRootPrecision.WherePrecisionIsLost
import GaloisForLFunctions.GreenCalculusOfThePrimeFreeWindow.TheFloorGraphNormAndTopOctaveBlindnessOfWindowGluing
import GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts.LogarithmicMangoldtTail
import GaloisForLFunctions.RHTower.ThetaPrimeScheduleSpectralObservation
import GaloisForLFunctions.RHTower.WeilPositivityPrimePowersForced
import GaloisForLFunctions.RHTower.XiMassShellPrimeMass
import GaloisForLFunctions.TransHorizonIncidenceMechanics.ParityPairAtHalfDamping

/-!
# The square-root remainder of the first distinct-prime-divisor moment

The jump at an integer is the logarithm of its radical. Removing the
linear contribution of repeated prime factors from the logarithm of
the factorial leaves a positive sum of fractional parts. Geometric
shells give its upper bound, and one shell of prime squares gives
its lower bound at every sufficiently large cutoff.
-/

noncomputable section
open Finset Filter Topology ArithmeticFunction
open _root_.RHTower

namespace GaloisForLFunctions.ExceptionalLayerTheory

/-- Each prime divides exactly this many positive integers through the cutoff. -/
def distinctPrimeLogMoment (N : ℕ) : ℝ :=
  ∑ p ∈ Nat.primesLE N, Real.log p * ((N/p:ℕ):ℝ)

private theorem prime_set (N : ℕ) : (Ioc 0 N).filter Nat.Prime=Nat.primesLE N := by
  ext p
  simp only [mem_filter,mem_Ioc,Nat.mem_primesLE]
  exact ⟨fun h => ⟨h.1.2,h.2⟩,fun h => ⟨⟨h.2.pos,h.1⟩,h.2⟩⟩

/-- The same count as a sum of the logarithms of distinct prime divisors. -/
theorem distinctPrimeLogMoment_eq_sum_primeFactors (N : ℕ) :
    distinctPrimeLogMoment N=∑ n ∈ Icc 1 N, ∑ p ∈ n.primeFactors, Real.log p := by
  let f := fun n : ℕ => if n.Prime then Real.log n else 0
  have h := TransHorizonIncidenceMechanics.sum_Icc_sum_divisors_eq_floor f N
  have hi : Icc 1 N=Ioc 0 N := by ext d; simp only [mem_Icc,mem_Ioc]; omega
  have hp (n : ℕ) : n.divisors.filter Nat.Prime=n.primeFactors := by
    ext p
    simp only [mem_filter,Nat.mem_divisors,Nat.mem_primeFactors]
    tauto
  calc
    _ = ∑ p ∈ Icc 1 N, f p*((N/p:ℕ):ℝ) := by
      rw [hi,distinctPrimeLogMoment,← prime_set,sum_filter]
      exact sum_congr rfl fun p _ => by by_cases h : p.Prime <;> simp [f,h]
    _ = ∑ n ∈ Icc 1 N, ∑ p ∈ n.divisors, f p := h.symm
    _ = _ := sum_congr rfl fun n _ => by rw [← hp,sum_filter]; rfl

/-- Reciprocal Mangoldt mass of all proper prime powers. -/
def repeatedPrimeLogDensity : ℝ := ∑' d : ℕ, primePowerPart d/(d:ℝ)

private def defect (N d : ℕ) : ℝ := primePowerPart d*((N:ℝ)/d-((N/d:ℕ):ℝ))

private theorem w_nonneg (d : ℕ) : 0≤primePowerPart d := by
  unfold primePowerPart; split <;> simp only [le_refl,vonMangoldt_nonneg]

private theorem defect_nonneg (N d : ℕ) : 0≤defect N d :=
  mul_nonneg (w_nonneg d) (sub_nonneg.mpr Nat.cast_div_le)

private theorem defect_le_weight (N d : ℕ) : defect N d≤primePowerPart d := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp [defect,primePowerPart]
  have hr : (0:ℝ)<d := by exact_mod_cast hd
  have ht : (N:ℝ)/d<((N/d:ℕ):ℝ)+1 := (div_lt_iff₀ hr).mpr (by
    exact_mod_cast (Nat.div_lt_iff_lt_mul hd).mp (Nat.lt_succ_self (N/d)))
  exact (mul_le_mul_of_nonneg_left (by linarith only [ht] : (N:ℝ)/d-((N/d:ℕ):ℝ)≤1)
    (w_nonneg d)).trans_eq (mul_one _)

private theorem defect_sum (N : ℕ) :
    HasSum (defect N) (distinctPrimeLogMoment N-Real.log (N.factorial:ℕ)+N*repeatedPrimeLogDensity) := by
  have hw : Summable fun d : ℕ => primePowerPart d/(d:ℝ) :=
    RenormalizedIntersectionArithmeticCounts.summable_nonprime_mangoldt_reciprocal.congr
      fun d => by by_cases h : d.Prime <;> simp [primePowerPart,h]
  let g := fun d : ℕ => primePowerPart d*((N/d:ℕ):ℝ)
  have hg : HasSum g (∑ d ∈ Ioc 0 N, g d) := by
    apply hasSum_sum_of_ne_finset_zero
    intro d hd
    rcases Nat.eq_zero_or_pos d with rfl | hp
    · simp [g]
    have hlt : N<d := lt_of_not_ge fun h => hd (mem_Ioc.mpr ⟨hp,h⟩)
    simp [g,Nat.div_eq_of_lt hlt]
  have hmain : distinctPrimeLogMoment N + ∑ d ∈ Ioc 0 N, g d=Real.log (N.factorial:ℕ) := by
    rw [distinctPrimeLogMoment,← prime_set,sum_filter,← sum_add_distrib,
      ← ArithmeticOfSquareRootPrecision.chebyshevTransform_vonMangoldt]
    apply sum_congr rfl
    intro d _
    by_cases hd : d.Prime <;> simp [g,primePowerPart,hd,ArithmeticOfSquareRootPrecision.vonMangoldtWeight,
      vonMangoldt_apply_prime]
  have ht := (hw.hasSum.mul_left (N:ℝ)).sub hg
  convert ht using 1
  · funext d; dsimp only [defect,g,Pi.sub_apply]; ring
  · change _=(N:ℝ)*repeatedPrimeLogDensity-_
    linarith only [hmain]

/-- At each integer cutoff the centered prime moment is exactly the positive
sum of the fractional remainders of its proper-prime-power divisors. -/
theorem distinctPrimeLogMoment_fractional_parts (N : ℕ) :
    HasSum (fun d : ℕ => primePowerPart d*((N:ℝ)/d-((N/d:ℕ):ℝ)))
      (distinctPrimeLogMoment N-Real.log (N.factorial:ℕ)+N*repeatedPrimeLogDensity) :=
  defect_sum N

/-- The finite first mean of the prime-multiple count after subtracting
the factorial row and adding its linear centering. -/
def triangularDistinctPrimeLogMoment (N : ℕ) : ℝ :=
  (∑ j ∈ Finset.range N, (distinctPrimeLogMoment j - Real.log (j.factorial:ℕ)))/(N:ℝ)+
    repeatedPrimeLogDensity*N/2

/-- Averaging the sharp fractional-part identity preserves the term from
the omitted right endpoint of the arithmetic progression. -/
theorem triangularDistinctPrimeLogMoment_average {N : ℕ} (hN : 0 < N) :
    triangularDistinctPrimeLogMoment N = repeatedPrimeLogDensity/2 +
      (∑ j ∈ Finset.range N, (distinctPrimeLogMoment j-Real.log (j.factorial:ℕ)+
        (j:ℝ)*repeatedPrimeLogDensity))/(N:ℝ) := by
  have hn : (N:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have he : (∑ j ∈ Finset.range N, (j:ℝ))*2=(N:ℝ)*((N:ℝ)-1) := by
    have h := congrArg (Nat.cast (R := ℝ)) (Finset.sum_range_id_mul_two N)
    simpa only [Nat.cast_mul,Nat.cast_sum,Nat.cast_ofNat,Nat.cast_sub hN,Nat.cast_one] using h
  rw [triangularDistinctPrimeLogMoment,Finset.sum_add_distrib,← Finset.sum_mul]
  field_simp
  linear_combination -repeatedPrimeLogDensity*he

private abbrev shellConstant : ℝ := 3*(Real.log 4+4)

private theorem prefix_le (M : ℕ) :
    (∑ d ∈ Ioc 0 M, primePowerPart d)≤shellConstant*Real.sqrt M := by
  apply le_trans _ (GreenCalculusOfThePrimeFreeWindow.psi_sub_theta_le_three_mul_sqrt M)
  rw [Chebyshev.psi_sub_theta_eq_sum_not_prime,Nat.floor_natCast,sum_filter]
  exact le_of_eq (sum_congr rfl fun d _ => by by_cases h : d.Prime <;> simp [primePowerPart,h])

private theorem sqrt_four (M : ℕ) : Real.sqrt (↑(4*M):ℝ)=2*Real.sqrt M := by
  rw [Nat.cast_mul,Real.sqrt_mul (by positivity)]
  norm_num

private theorem defect_shell {N M : ℕ} (hM : 0<M) :
    (∑ d ∈ Ioc M (4*M), defect N d)≤(N:ℝ)/M*(shellConstant*(2*Real.sqrt M)) := by
  have hb (d : ℕ) (hd : d∈Ioc M (4*M)) : defect N d≤(N:ℝ)/M*primePowerPart d := by
    have hd' := (mem_Ioc.mp hd).1
    have hle := div_le_div_of_nonneg_left (Nat.cast_nonneg N) (by exact_mod_cast hM : (0:ℝ)<M)
      (by exact_mod_cast hd'.le : (M:ℝ)≤d)
    rw [mul_comm _ (primePowerPart d)]
    exact mul_le_mul_of_nonneg_left ((sub_le_self _ (Nat.cast_nonneg (N/d))).trans hle) (w_nonneg d)
  apply (sum_le_sum hb).trans
  rw [← mul_sum]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have hsub : Ioc M (4*M)⊆Ioc 0 (4*M) := Ioc_subset_Ioc_left (Nat.zero_le _)
  exact ((sum_le_sum_of_subset_of_nonneg hsub fun d _ _ => w_nonneg d).trans
    (prefix_le (4*M))).trans_eq (by rw [sqrt_four])

/-- Every finite shell through a power of four satisfies the same square-root estimate. -/
private theorem defect_through_shell {N : ℕ} (hN : 0<N) (j : ℕ) :
    (∑ d ∈ Ioc 0 (4^j*N), defect N d) ≤
      5*shellConstant*Real.sqrt N-4*shellConstant*Real.sqrt N/(2:ℝ)^j := by
  have hn : (0:ℝ)<N := by exact_mod_cast hN
  have hroot (i : ℕ) : Real.sqrt (↑(4^i*N):ℝ)=(2:ℝ)^i*Real.sqrt N := by
    induction i with
    | zero => simp
    | succ i ih => rw [pow_succ',mul_assoc,sqrt_four,ih,pow_succ']; ring
  induction j with
  | zero =>
    simpa only [pow_zero,one_mul,div_one,show ∀ x y : ℝ, 5*x*y-4*x*y=x*y by intros; ring]
      using (sum_le_sum fun d (_ : d∈Ioc 0 N) => defect_le_weight N d).trans (prefix_le N)
  | succ j ih =>
    let M := 4^j*N
    have hm : 0<M := Nat.mul_pos (by positivity) hN
    have hM : (M:ℝ)=((2:ℝ)^j)^2*(N:ℝ) := by
      dsimp only [M]; push_cast; rw [← pow_mul, mul_comm j 2,pow_mul]; norm_num
    have hstep := defect_shell (N := N) hm
    have heq : 4^(j+1)*N=4*M := by simp only [M,pow_succ',mul_assoc]
    rw [heq,← sum_Ioc_consecutive (defect N) (Nat.zero_le M) (by omega : M≤4*M)]
    apply (add_le_add ih hstep).trans_eq
    rw [show Real.sqrt (M:ℝ)=(2:ℝ)^j*Real.sqrt N from hroot j,hM,pow_succ]
    field_simp [hn.ne']; ring

/-- A uniform upper bound for the unweighted cutoff, including its rounding error. -/
theorem distinctPrimeLogMoment_sqrt_upper {N : ℕ} (hN : 0<N) :
    distinctPrimeLogMoment N-Real.log (N.factorial:ℕ)+N*repeatedPrimeLogDensity ≤
      15*(Real.log 4+4)*Real.sqrt N := by
  apply le_of_tendsto (defect_sum N)
  apply Eventually.of_forall
  intro S
  let j := S.sup id
  have hh : j≤4^j*N := calc
    j ≤ 2^j := (Nat.lt_two_pow_self (n := j)).le
    _ ≤ 4^j := Nat.pow_le_pow_left (by norm_num) _
    _ ≤ 4^j*N := Nat.le_mul_of_pos_right _ hN
  have hsub : S⊆insert 0 (Ioc 0 (4^j*N)) := by
    intro d hd
    rcases Nat.eq_zero_or_pos d with rfl | h
    · exact mem_insert_self ..
    · exact mem_insert_of_mem (mem_Ioc.mpr ⟨h,(le_sup (f := id) hd).trans hh⟩)
  have hs := sum_le_sum_of_subset_of_nonneg (f := defect N) hsub (fun d _ _ => defect_nonneg N d)
  rw [sum_insert (by simp),show defect N 0=0 by simp [defect],zero_add] at hs
  exact (hs.trans (defect_through_shell hN j)).trans (by
    have hC : 0≤shellConstant := by dsimp only [shellConstant]; positivity
    have hpos : 0≤4*shellConstant*Real.sqrt N/(2:ℝ)^j := by positivity
    dsimp only [shellConstant] at *
    linarith only [hpos])

/-- Prime squares just beyond the cutoff give a lower bound before any asymptotics. -/
theorem distinctPrimeLogMoment_square_window {N : ℕ} (hN : 0<N) :
    (Chebyshev.theta (2*Real.sqrt N)-Chebyshev.theta (Real.sqrt N))/4 ≤
    distinctPrimeLogMoment N-Real.log (N.factorial:ℕ)+N*repeatedPrimeLogDensity := by
  let S := multiplicativePrimeWindow (Real.sqrt N) 2
  have h (p : ℕ) (hp : p∈S) : Real.log p/4≤defect N (p^2) := by
    obtain ⟨hp',hlo,hhi⟩ := mem_multiplicativePrimeWindow (Real.sqrt_nonneg _) (by norm_num) hp
    have hp0 : (0:ℝ)<p := by exact_mod_cast hp'.pos
    have hl : (N:ℝ)<(p:ℝ)^2 := (Real.sqrt_lt (Nat.cast_nonneg _) hp0.le).mp hlo
    have hu := (sq_le_sq₀ hp0.le (by positivity : 0≤2*Real.sqrt N)).mpr hhi
    rw [mul_pow,Real.sq_sqrt (Nat.cast_nonneg N)] at hu
    have hn : N<p^2 := by exact_mod_cast hl
    rw [defect,primePowerPart,if_neg (Nat.Prime.not_prime_pow (by norm_num : 2≤2)),
      vonMangoldt_apply_pow (by norm_num),vonMangoldt_apply_prime hp',Nat.div_eq_of_lt hn,
      Nat.cast_zero,sub_zero,Nat.cast_pow]
    have hr : (1:ℝ)/4≤(N:ℝ)/(p:ℝ)^2 :=
      (le_div_iff₀ (sq_pos_of_pos hp0)).mpr (by linarith only [hu])
    simpa only [div_eq_mul_inv,one_mul] using mul_le_mul_of_nonneg_left hr (Real.log_natCast_nonneg p)
  rw [theta_sub_eq_sum_primeWindow (Real.sqrt_nonneg _) (by norm_num),sum_div]
  apply (sum_le_sum h).trans
  have hi : Set.InjOn (fun p : ℕ => p^2) (↑S) :=
    (Nat.pow_left_injective (by norm_num : 2≠0)).injOn
  rw [← sum_image hi]
  exact ((defect_sum N).summable.sum_le_tsum _ (fun d _ => defect_nonneg N d)).trans_eq (defect_sum N).tsum_eq

/-- The first ordinary prime-log moment has error of exact square-root size
after subtracting the factorial and the linear proper-power term. -/
theorem distinctPrimeLogMoment_sqrt_lower :
    ∀ᶠ N : ℕ in atTop, Real.sqrt N/8≤
      distinctPrimeLogMoment N-Real.log (N.factorial:ℕ)+N*repeatedPrimeLogDensity := by
  obtain ⟨X,hX⟩ := (chebyshevTheta_eventually_relative (by norm_num : (0:ℝ)<1/8)).exists_forall_of_atTop
  have hlim : Tendsto (fun N : ℕ => Real.sqrt N) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hlim.eventually_ge_atTop X,eventually_ge_atTop 1] with N hN hn
  have hpos := Real.sqrt_nonneg (N:ℝ)
  have h₁ := (abs_le.mp (hX _ hN)).2
  have h₂ := (abs_le.mp (hX _ (show X≤2*Real.sqrt N by linarith only [hN,hpos]))).1
  exact (show Real.sqrt N/8≤(Chebyshev.theta (2*Real.sqrt N)-Chebyshev.theta (Real.sqrt N))/4 by
    linarith only [h₁,h₂,hpos]).trans (distinctPrimeLogMoment_square_window hn)

/-- The centered first mean is sublinear, with a square-root majorant at
every positive integer cutoff. -/
theorem triangularDistinctPrimeLogMoment_abs {N : ℕ} (hN : 1 ≤ N) :
    |triangularDistinctPrimeLogMoment N| ≤
      |repeatedPrimeLogDensity|/2 + 15*(Real.log 4+4)*Real.sqrt N := by
  have hn : (0:ℝ)<N := by exact_mod_cast hN
  rw [triangularDistinctPrimeLogMoment_average hN]
  apply (abs_add_le _ _).trans
  rw [abs_div,abs_of_pos (by norm_num : (0:ℝ)<2),abs_div,abs_of_pos hn]
  apply add_le_add le_rfl
  apply (div_le_iff₀ hn).mpr
  apply (abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ _ ∈ range N, 15*(Real.log 4+4)*Real.sqrt N := by
      refine sum_le_sum fun j hj => ?_
      rcases Nat.eq_zero_or_pos j with rfl | hpos
      · simp [distinctPrimeLogMoment]; positivity
      · rw [abs_of_nonneg ((tsum_nonneg (fun d => defect_nonneg j d)).trans_eq (defect_sum j).tsum_eq)]
        exact (distinctPrimeLogMoment_sqrt_upper hpos).trans (mul_le_mul_of_nonneg_left
          (Real.sqrt_le_sqrt (by exact_mod_cast (mem_range.mp hj).le)) (by positivity))
    _ = _ := by simp [mul_comm]

end GaloisForLFunctions.ExceptionalLayerTheory
