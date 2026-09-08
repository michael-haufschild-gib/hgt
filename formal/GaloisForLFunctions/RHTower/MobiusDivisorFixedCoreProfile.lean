import GaloisForLFunctions.RHTower.RetainedPrimeTopHomothety
import GaloisForLFunctions.RHTower.DivisorUnsignedChannelExactMean

/-!
# Fixed processed-core source profile and energy tail

Every remaining fibre is a signed, clipped product dilation of the same
processed-core head. The complete energy is its squarefree arithmetic sample
sum. Every nonempty fixed prime core cancels the head's square-root main
term, uniformly over all labels on one quotient tail; that tail carries
arbitrarily small quadratic energy.

The weighted squarefree density limit and the signs of its dilation
correlations are not asserted. No numerical result is a premise.
-/

noncomputable section
open Filter Finset
open scoped Topology
namespace RHTower

private lemma head_succ_sum (N : ℕ) (P : Finset ℕ) :
    mobiusDivisorSelectionFibre (N+1) P ∅ =
      ∑ d ∈ Icc 1 N, if d.primeFactors \ P = ∅
        then mobiusDivisorDilationChannel (N+1) d else 0 := by
  rw [mobiusDivisorSelectionFibre_eq_sum_Icc,
    sum_Icc_succ_top (by omega : 1 ≤ N+1)]
  have hz : mobiusDivisorDilationChannel (N+1) (N+1) = 0 := by
    simp [mobiusDivisorDilationChannel]
  simp [hz]

/-- Every remaining coordinate is the exact signed product dilation of the
same processed-core head, including the clipped endpoint. -/
theorem mobiusDivisorSelectionFibre_product_interpolation
    (M : ℕ) (P R : Finset ℕ) (hR : ∀ p ∈ R, p.Prime)
    (hdis : Disjoint R P) :
    let r := ∏ p ∈ R, p
    mobiusDivisorSelectionFibre M P R =
      Real.sqrt r * ((ArithmeticFunction.moebius r : ℤ) : ℝ) *
        mobiusDivisorInterpolatedFibre M r P ∅ := by
  intro r
  have hr : 0 < r := prod_pos (fun p hp => (hR p hp).pos)
  have hrfac : r.primeFactors = R := Nat.primeFactors_prod hR
  rw [mobiusDivisorSelectionFibre_eq_sum_Icc,
    mobiusDivisorInterpolatedFibre, mobiusDivisorSelectionFibre_eq_sum_Icc,
    head_succ_sum]
  have hrestrict : (∑ d ∈ Icc 1 M,
      if d.primeFactors \ P = R then mobiusDivisorDilationChannel M d else 0) =
      ∑ d ∈ (Icc 1 M).filter (fun d => r ∣ d),
        if d.primeFactors \ P = R then mobiusDivisorDilationChannel M d else 0 := by
    rw [sum_filter]
    apply sum_congr rfl
    intro d hd
    by_cases hrd : r ∣ d
    · simp [hrd]
    · have hne : d.primeFactors \ P ≠ R := by
        intro he
        have hsub : R ⊆ d.primeFactors := he ▸ sdiff_subset
        exact hrd ((prod_dvd_prod_of_subset R d.primeFactors id hsub).trans
          (Nat.prod_primeFactors_dvd d))
      simp [hrd, hne]
  rw [hrestrict, sum_Icc_filter_dvd_reindex r M hr]
  simp only [mul_add, mul_sum, ← sum_add_distrib]
  apply sum_congr rfl
  intro d hd
  have hd0 : d ≠ 0 := by have := mem_Icc.mp hd; omega
  by_cases hc : r.Coprime d
  · have hdisR : Disjoint R d.primeFactors := by
      simpa only [hrfac] using hc.disjoint_primeFactors
    have heq : (r*d).primeFactors \ P = R ↔ d.primeFactors \ P = ∅ := by
      rw [Nat.primeFactors_mul hr.ne' hd0, hrfac]
      constructor
      · intro he
        apply sdiff_eq_empty_iff_subset.mpr
        intro p hpd
        by_contra hpP
        have hpR : p ∈ R := he ▸ Finset.mem_sdiff.mpr ⟨mem_union_right _ hpd, hpP⟩
        exact disjoint_left.mp hdisR hpR hpd
      · intro he
        have hsub := sdiff_eq_empty_iff_subset.mp he
        ext p
        simp only [Finset.mem_sdiff, mem_union]
        constructor
        · rintro ⟨hp | hp, hn⟩
          · exact hp
          · exact False.elim (hn (hsub hp))
        · intro hp
          exact ⟨Or.inl hp, fun hpP => disjoint_left.mp hdis hp hpP⟩
    by_cases he : d.primeFactors \ P = ∅
    · rw [if_pos (heq.mpr he), if_pos he, if_pos he,
        mobiusDivisorDilationChannel_interpolation_masked r M d hr, if_pos hc]
      ring
    · rw [if_neg (fun h => he (heq.mp h)), if_neg he, if_neg he]
      ring
  · have hm : ArithmeticFunction.moebius (r*d) = 0 :=
      ArithmeticFunction.moebius_eq_zero_of_not_squarefree
        (fun h => hc (Nat.coprime_of_squarefree_mul h))
    have hz : mobiusDivisorDilationChannel M (r*d) = 0 := by
      simp [mobiusDivisorDilationChannel_eq_moebius_unsigned, hm]
    have hne : d.primeFactors \ P ≠ ∅ := by
      intro he
      apply hc
      apply (Nat.disjoint_primeFactors hr.ne' hd0).mp
      rw [hrfac]
      exact hdis.mono_right (sdiff_eq_empty_iff_subset.mp he)
    simp [hz, hne]

/-- Complete energy samples one fixed processed-core head over every born
remaining prime product. No remaining coordinate or endpoint is discarded. -/
theorem mobiusDivisorSelectionEnergy_eq_processedHead_scales
    (M : ℕ) (P : Finset ℕ) :
    mobiusDivisorSelectionEnergy M P =
      ∑ R ∈ mobiusDivisorActiveLabels M P,
        let r := ∏ p ∈ R, p
        (r : ℝ) * (mobiusDivisorInterpolatedFibre M r P ∅)^2 := by
  rw [mobiusDivisorSelectionEnergy_eq_sum_active]
  apply sum_congr rfl
  intro R hR
  have hsub := mem_powerset.mp (mem_filter.mp hR).1
  have hprime : ∀ p ∈ R, p.Prime := by
    intro p hp
    exact (mem_filter.mp (Finset.mem_sdiff.mp (hsub hp)).1).2
  have hdis : Disjoint R P := by
    apply disjoint_left.mpr
    intro p hp hpP
    exact (Finset.mem_sdiff.mp (hsub hp)).2 hpP
  rw [mobiusDivisorSelectionFibre_product_interpolation M P R hprime hdis]
  dsimp only
  have hmu : (((ArithmeticFunction.moebius (∏ p ∈ R, p) : ℤ) : ℝ))^2 = 1 := by
    exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree
      (GibbsGas.squarefree_prod_primes hprime)
  rw [mul_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg _), hmu, mul_one]

/-- The complete energy is a squarefree arithmetic sum of samples of one
processed-core head, indexed by the remaining integer rather than subsets. -/
theorem mobiusDivisorSelectionEnergy_eq_squarefree_processedHead
    (M : ℕ) (P : Finset ℕ) :
    mobiusDivisorSelectionEnergy M P =
      ∑ r ∈ (mobiusDivisorSelectionIndices M).filter
        (fun r => Disjoint r.primeFactors P),
        (r : ℝ) * (mobiusDivisorInterpolatedFibre M r P ∅)^2 := by
  rw [mobiusDivisorSelectionEnergy_eq_processedHead_scales]
  have hprime (R : Finset ℕ) (hR : R ∈ mobiusDivisorActiveLabels M P) :
      ∀ p ∈ R, p.Prime := by
    intro p hp
    exact (mem_filter.mp (Finset.mem_sdiff.mp
      ((mem_powerset.mp (mem_filter.mp hR).1) hp)).1).2
  apply sum_nbij' (fun R : Finset ℕ => ∏ p ∈ R, p) Nat.primeFactors
  · intro R hR
    have hsub := mem_powerset.mp (mem_filter.mp hR).1
    have hr : 0 < ∏ p ∈ R, p := prod_pos (fun p hp => (hprime R hR p hp).pos)
    have hlt := (mem_filter.mp hR).2
    apply mem_filter.mpr
    constructor
    · apply mem_filter.mpr
      exact ⟨mem_Icc.mpr ⟨by omega, by omega⟩,
        GibbsGas.squarefree_prod_primes (hprime R hR)⟩
    · rw [Nat.primeFactors_prod (hprime R hR)]
      apply disjoint_left.mpr
      intro p hp hpP
      exact (Finset.mem_sdiff.mp (hsub hp)).2 hpP
  · intro r hr
    obtain ⟨hr, hdis⟩ := mem_filter.mp hr
    obtain ⟨hr, hsq⟩ := mem_filter.mp hr
    have hr' := mem_Icc.mp hr
    apply mem_filter.mpr
    constructor
    · apply mem_powerset.mpr
      intro p hp
      apply Finset.mem_sdiff.mpr
      constructor
      · apply mem_filter.mpr
        exact ⟨mem_range.mpr (by have := Nat.le_of_mem_primeFactors hp; omega),
          (Nat.mem_primeFactors.mp hp).1⟩
      · exact fun hpP => disjoint_left.mp hdis hp hpP
    · rw [Nat.prod_primeFactors_of_squarefree hsq]
      omega
  · intro R hR
    exact Nat.primeFactors_prod (hprime R hR)
  · intro r hr
    exact Nat.prod_primeFactors_of_squarefree (mem_filter.mp (mem_filter.mp hr).1).2
  · intro R hR
    rfl


/-- After its finite prime-product threshold, a fixed processed head is
exactly the finite divisor transform of the original unsigned channels. -/
theorem mobiusDivisorSelectionHead_eq_sum_divisors
    (M : ℕ) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (hM : (∏ p ∈ P, p) ≤ M) :
    mobiusDivisorSelectionFibre M P ∅ =
      ∑ d ∈ (∏ p ∈ P, p).divisors, mobiusDivisorDilationChannel M d := by
  let D := ∏ p ∈ P, p
  have hD : 0 < D := prod_pos (fun p hp => (hP p hp).pos)
  have hfac : D.primeFactors = P := Nat.primeFactors_prod hP
  have hsub : D.divisors ⊆ Icc 1 M := by
    intro d hd
    exact mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hd,
      (Nat.le_of_dvd hD (Nat.mem_divisors.mp hd).1).trans hM⟩
  have hlabel (d : ℕ) (hd : d ∈ D.divisors) : d.primeFactors \ P = ∅ := by
    apply sdiff_eq_empty_iff_subset.mpr
    rw [← hfac]
    exact Nat.primeFactors_mono (Nat.mem_divisors.mp hd).1 hD.ne'
  rw [mobiusDivisorSelectionFibre_eq_sum_Icc]
  calc
    _ = ∑ d ∈ D.divisors,
        if d.primeFactors \ P = ∅ then mobiusDivisorDilationChannel M d else 0 := by
      symm
      apply sum_subset hsub
      intro d hd hn
      by_cases hs : Squarefree d
      · have hne : d.primeFactors \ P ≠ ∅ := by
          intro he
          apply hn
          apply Nat.mem_divisors.mpr
          refine ⟨?_, hD.ne'⟩
          rw [← Nat.prod_primeFactors_of_squarefree hs]
          exact prod_dvd_prod_of_subset d.primeFactors P id
            (sdiff_eq_empty_iff_subset.mp he)
        simp [hne]
      · simp [mobiusDivisorDilationChannel_eq_moebius_unsigned,
          ArithmeticFunction.moebius_eq_zero_of_not_squarefree hs]
    _ = _ := sum_congr rfl (fun d hd => if_pos (hlabel d hd))

/-- Every fixed positive dilation has the same exact normalized unsigned mean. -/
theorem tendsto_divisorUnsignedDilationChannel_div_sqrt (d : ℕ) (hd : 0 < d) :
    Tendsto (fun M : ℕ => divisorUnsignedDilationChannel M d / Real.sqrt M) atTop
      (𝓝 (Real.log (2*Real.pi)/2-Real.eulerMascheroniConstant-1/4)) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨T, hT, hbound⟩ :=
    exists_divisorUnsignedDilationChannel_uniform_mean_error (ε/2) (by positivity)
  refine ⟨d*T, ?_⟩
  intro M hM
  have hquot : T ≤ M/d := (Nat.le_div_iff_mul_le hd).mpr (by simpa [mul_comm] using hM)
  have hpos : 0 < M := by nlinarith
  have hs : 0 < Real.sqrt (M : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hpos)
  have hb := hbound M d hd hquot
  rw [Real.dist_eq]
  have he : divisorUnsignedDilationChannel M d / Real.sqrt M -
      (Real.log (2*Real.pi)/2-Real.eulerMascheroniConstant-1/4) =
      (divisorUnsignedDilationChannel M d -
        (Real.log (2*Real.pi)/2-Real.eulerMascheroniConstant-1/4)*Real.sqrt M)/Real.sqrt M := by
    field_simp
  rw [he, abs_div, abs_of_pos hs]
  have hb' := (div_le_iff₀ hs).mpr hb
  linarith

private lemma sum_core_moebius_zero (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hne : P.Nonempty) :
    (∑ d ∈ (∏ p ∈ P, p).divisors, ((ArithmeticFunction.moebius d : ℤ) : ℝ)) = 0 := by
  have h := ArithmeticFunction.isMultiplicative_moebius.prodPrimeFactors_one_add_of_squarefree
    (GibbsGas.squarefree_prod_primes hP)
  rw [Nat.primeFactors_prod hP] at h
  have hz : (∏ p ∈ P, (1 + ArithmeticFunction.moebius p)) = 0 := by
    obtain ⟨p, hp⟩ := hne
    apply prod_eq_zero hp
    rw [ArithmeticFunction.moebius_apply_prime (hP p hp)]
    ring
  rw [hz] at h
  exact_mod_cast h.symm

/-- Every nonempty fixed processed prime core cancels the entire square-root
main term of its actual signed head. -/
theorem tendsto_mobiusDivisorSelectionHead_div_sqrt_zero
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (hne : P.Nonempty) :
    Tendsto (fun M : ℕ => mobiusDivisorSelectionFibre M P ∅ / Real.sqrt M) atTop (𝓝 0) := by
  let c := Real.log (2*Real.pi)/2-Real.eulerMascheroniConstant-1/4
  have hterm (d : ℕ) (hd : d ∈ (∏ p ∈ P, p).divisors) :
      Tendsto (fun M : ℕ => mobiusDivisorDilationChannel M d / Real.sqrt M) atTop
        (𝓝 (((ArithmeticFunction.moebius d : ℤ) : ℝ)*c)) := by
    have h := (tendsto_divisorUnsignedDilationChannel_div_sqrt d
      (Nat.pos_of_mem_divisors hd)).const_mul (((ArithmeticFunction.moebius d : ℤ) : ℝ))
    simpa only [mobiusDivisorDilationChannel_eq_moebius_unsigned, mul_div_assoc] using h
  have hsum := tendsto_finsetSum (∏ p ∈ P, p).divisors hterm
  have hz : (∑ d ∈ (∏ p ∈ P, p).divisors,
      (((ArithmeticFunction.moebius d : ℤ) : ℝ)*c)) = 0 := by
    rw [← sum_mul, sum_core_moebius_zero P hP hne, zero_mul]
  rw [hz] at hsum
  apply hsum.congr'
  filter_upwards [eventually_ge_atTop (∏ p ∈ P, p)] with M hM
  rw [mobiusDivisorSelectionHead_eq_sum_divisors M P hP hM, sum_div]


/-- Fixed nonempty processing gives arbitrarily small normalized amplitudes
uniformly over all remaining labels on one common quotient tail. -/
theorem exists_mobiusDivisorSelectionFibre_uniform_head_tail
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (hne : P.Nonempty)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ T : ℕ, 1 ≤ T ∧ ∀ M : ℕ, ∀ R : Finset ℕ,
      (∀ p ∈ R, p.Prime) → Disjoint R P → T ≤ M/(∏ p ∈ R, p) →
        |mobiusDivisorSelectionFibre M P R| ≤ ε*Real.sqrt M := by
  obtain ⟨T, hT⟩ := Metric.tendsto_atTop.mp
    (tendsto_mobiusDivisorSelectionHead_div_sqrt_zero P hP hne) ε hε
  have hhead (N : ℕ) (hN : max T 1 ≤ N) :
      |mobiusDivisorSelectionFibre N P ∅| ≤ ε*Real.sqrt N := by
    have hs : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr (by
      have := (le_max_right T 1).trans hN
      exact_mod_cast (show 0 < N by omega))
    have hb := (hT N ((le_max_left _ _).trans hN)).le
    rw [Real.dist_eq, sub_zero, abs_div, abs_of_pos hs] at hb
    exact (div_le_iff₀ hs).mp hb
  refine ⟨max T 1, le_max_right _ _, ?_⟩
  intro M R hR hdis hquot
  let r := ∏ p ∈ R, p
  have hr : 0 < r := prod_pos (fun p hp => (hR p hp).pos)
  change max T 1 ≤ M/r at hquot
  have h0 := hhead (M/r) hquot
  have h1 := hhead (M/r+1) (by omega)
  have hw0 := divisorPrimeClipWeight_nonneg M r hr
  have hw1 : 0 ≤ 1-divisorPrimeClipWeight M r := by
    have := divisorPrimeClipWeight_lt_one M r hr
    linarith
  have hclock := divisorPrimeClipWeight_mul_step M r hr
  push_cast at hclock
  rw [Real.sqrt_mul (Nat.cast_nonneg r)] at hclock
  have hclock' : Real.sqrt (r : ℝ)*
      ((1-divisorPrimeClipWeight M r)*Real.sqrt (M/r : ℕ)+
        divisorPrimeClipWeight M r*Real.sqrt (M/r+1 : ℕ)) = Real.sqrt M := by
    push_cast
    nlinarith only [hclock]
  have hmu : |((ArithmeticFunction.moebius r : ℤ) : ℝ)| = 1 := by
    exact_mod_cast ArithmeticFunction.abs_moebius_eq_one_of_squarefree
      (GibbsGas.squarefree_prod_primes hR)
  rw [mobiusDivisorSelectionFibre_product_interpolation M P R hR hdis]
  change |Real.sqrt r * ((ArithmeticFunction.moebius r : ℤ) : ℝ) *
    mobiusDivisorInterpolatedFibre M r P ∅| ≤ _
  rw [abs_mul, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _), hmu, mul_one]
  calc
    _ ≤ Real.sqrt r * ((1-divisorPrimeClipWeight M r)*|mobiusDivisorSelectionFibre (M/r) P ∅| +
        divisorPrimeClipWeight M r*|mobiusDivisorSelectionFibre (M/r+1) P ∅|) := by
      apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
      unfold mobiusDivisorInterpolatedFibre
      exact (abs_add_le _ _).trans_eq (by rw [abs_mul, abs_mul, abs_of_nonneg hw1, abs_of_nonneg hw0])
    _ ≤ Real.sqrt r * ((1-divisorPrimeClipWeight M r)*(ε*Real.sqrt (M/r : ℕ)) +
        divisorPrimeClipWeight M r*(ε*Real.sqrt (M/r+1 : ℕ))) := by
      exact mul_le_mul_of_nonneg_left (add_le_add
        (mul_le_mul_of_nonneg_left h0 hw1) (mul_le_mul_of_nonneg_left h1 hw0))
          (Real.sqrt_nonneg _)
    _ = ε*Real.sqrt M := by nlinarith only [congrArg (fun z : ℝ => ε*z) hclock']

/-- The entire large-quotient part of the actual energy is uniformly small
on the quadratic scale, for every fixed nonempty processed prime core. -/
theorem exists_mobiusDivisorSelectionEnergy_quotient_tail_bound
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (hne : P.Nonempty)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ T : ℕ, 1 ≤ T ∧ ∀ M : ℕ,
      (∑ R ∈ (mobiusDivisorActiveLabels M P).filter
        (fun R => T ≤ M/(∏ p ∈ R, p)), (mobiusDivisorSelectionFibre M P R)^2) ≤ ε^2*(M : ℝ)^2 := by
  obtain ⟨T, hT, hbound⟩ := exists_mobiusDivisorSelectionFibre_uniform_head_tail P hP hne ε hε
  refine ⟨T, hT, ?_⟩
  intro M
  let A := (mobiusDivisorActiveLabels M P).filter (fun R => T ≤ M/(∏ p ∈ R, p))
  have hcard : A.card ≤ M :=
    (card_filter_le _ _).trans ((card_mobiusDivisorActiveLabels_le M P).trans (Nat.sub_le _ _))
  calc
    _ ≤ ∑ R ∈ A, ε^2*(M : ℝ) := by
      apply sum_le_sum
      intro R hR
      obtain ⟨hRa, hquot⟩ := mem_filter.mp hR
      have hsub := mem_powerset.mp (mem_filter.mp hRa).1
      have hp : ∀ p ∈ R, p.Prime := by
        intro p hp
        exact (mem_filter.mp (Finset.mem_sdiff.mp (hsub hp)).1).2
      have hd : Disjoint R P := disjoint_left.mpr (by
        intro p hp hpP
        exact (Finset.mem_sdiff.mp (hsub hp)).2 hpP)
      have hb := hbound M R hp hd hquot
      have hs := Real.sq_sqrt (Nat.cast_nonneg M)
      have hab := abs_nonneg (mobiusDivisorSelectionFibre M P R)
      have hsq := sq_abs (mobiusDivisorSelectionFibre M P R)
      nlinarith [sq_nonneg (ε*Real.sqrt M - |mobiusDivisorSelectionFibre M P R|)]
    _ = (A.card : ℝ)*(ε^2*(M : ℝ)) := by simp
    _ ≤ (M : ℝ)*(ε^2*(M : ℝ)) := by
      apply mul_le_mul_of_nonneg_right (by exact_mod_cast hcard)
      positivity
    _ = _ := by ring

end RHTower
