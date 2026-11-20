import GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.PrimitiveSpectrumOfTheMoebiusGram
import GaloisForLFunctions.ArithmeticCorrelationGeometry.RealMultiplicativeDataSeeOnlySquareSuccessorPairs

/-!
# Prime-sign averages on the primitive Möbius Gram spectrum

The sign selection in Ghosh–Shuin (arXiv:2611.24746, Lemma 3.7) averages
quadratic cross terms before selecting a single sign vector. Restricting the
random signs to primes retains multiplicativity. At a reduced ratio, averaging
over a set of primes removes precisely the occupied atoms touched by those
primes, independently of the common dilation and of the time window.
-/

open MeasureTheory Finset RHTower RHTower.Sieve GaloisForLFunctions.ArithmeticCorrelationGeometry
namespace GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.MoebiusGram
noncomputable section

/-- The part away from the diagonal after multiplying prime coefficients
by one fixed system of completely multiplicative signs. -/
def signedRatioReading (N : ℕ) (P : Finset ℕ) (s : P → ℤˣ) (K : ℝ → ℝ) : ℝ :=
  ∑ q ∈ primitiveRatioPairs N, (((primeSignTwist P s q.1 * primeSignTwist P s q.2 : ℤ):ℝ) *
    (atom N q.1 q.2 * K (Real.log q.1 - Real.log q.2)))

private theorem sign_mul (P : Finset ℕ) (s : P → ℤˣ) {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) :
    primeSignTwist P s (m*n) = primeSignTwist P s m * primeSignTwist P s n := by
  simp only [primeSignTwist, Nat.factorization_mul hm hn, Finsupp.add_apply, pow_add, prod_mul_distrib]

private theorem sign_sq (P : Finset ℕ) (s : P → ℤˣ) (n : ℕ) :
    primeSignTwist P s n * primeSignTwist P s n = 1 := by
  rw [primeSignTwist, ← prod_mul_distrib]
  apply prod_eq_one
  intro p _
  rw [← mul_pow]
  rcases Int.units_eq_one_or (s p) with h|h <;> simp [h]

/-- Common dilations drop out even before averaging signs. -/
theorem signed_ratio_scale (P : Finset ℕ) (s : P → ℤˣ) {d a b : ℕ}
    (hd : d ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0) :
    primeSignTwist P s (d*a) * primeSignTwist P s (d*b) =
      primeSignTwist P s a * primeSignTwist P s b := by
  rw [sign_mul P s hd ha, sign_mul P s hd hb, mul_mul_mul_comm, sign_sq, one_mul]

private theorem atom_zero_of_nonsquarefree {N a b : ℕ} (h : ¬(Squarefree a ∧ Squarefree b)) :
    atom N a b = 0 := by
  by_cases ha : Squarefree a
  · have hb : ¬ Squarefree b := fun h' => h ⟨ha,h'⟩
    simp [atom, coeff, mobiusRealCoefficient, ArithmeticFunction.moebius_eq_zero_of_not_squarefree hb]
  · simp [atom, coeff, mobiusRealCoefficient, ArithmeticFunction.moebius_eq_zero_of_not_squarefree ha]

private theorem even_exponents_iff {a b : ℕ} (ha : Squarefree a) (hb : Squarefree b)
    (hab : a.Coprime b) (P : Finset ℕ) :
    (∀ p ∈ P, Even (a.factorization p + b.factorization p)) ↔
      ∀ p ∈ P, p ∉ a.primeFactors ∧ p ∉ b.primeFactors := by
  have disj := hab.disjoint_primeFactors
  constructor
  · intro h p hp
    have he := h p hp
    have h₁ := ha.natFactorization_le_one p
    have h₂ := hb.natFactorization_le_one p
    have hno : ¬(p ∈ a.primeFactors ∧ p ∈ b.primeFactors) :=
      fun hh => Finset.disjoint_left.mp disj hh.1 hh.2
    simp only [← Nat.support_factorization, Finsupp.mem_support_iff] at hno ⊢
    obtain ⟨j,hj⟩ := he
    omega
  · intro h p hp
    obtain ⟨h₁,h₂⟩ := h p hp
    simp only [← Nat.support_factorization, Finsupp.mem_support_iff, not_not] at h₁ h₂
    simp [h₁,h₂]

/-- Exact projection onto primitive ratios having no selected prime on
either side. It applies to signed or discontinuous spectral windows. -/
theorem primeSign_average_primitive_spectrum (N : ℕ) (P : Finset ℕ) (K : ℝ → ℝ) :
    ∑ s : P → ℤˣ, signedRatioReading N P s K =
      (2:ℝ)^P.card * ∑ q ∈ (primitiveRatioPairs N).filter (fun q =>
        ∀ p ∈ P, p ∉ q.1.primeFactors ∧ p ∉ q.2.primeFactors),
        atom N q.1 q.2 * K (Real.log q.1 - Real.log q.2) := by
  classical
  simp only [signedRatioReading]
  rw [sum_comm, sum_filter, mul_sum]
  refine sum_congr rfl fun q hq => ?_
  obtain ⟨_,hab,_⟩ := mem_filter.mp hq
  rw [← sum_mul, ← Int.cast_sum, sum_primeSignTwist_mul,
    prod_two_or_zero P (fun p => q.1.factorization p + q.2.factorization p)]
  by_cases h : Squarefree q.1 ∧ Squarefree q.2
  · simp only [even_exponents_iff h.1 h.2 hab]
    split_ifs <;> push_cast <;> ring
  · simp only [atom_zero_of_nonsquarefree h, zero_mul, mul_zero, ite_self]

/-- Randomizing all primes through the horizon annihilates the entire
off-diagonal term for every spectral window. -/
theorem full_primeSign_average_off_diagonal (N : ℕ) (K : ℝ → ℝ) :
    ∑ s : (range (N+1)).filter Nat.Prime → ℤˣ,
      signedRatioReading N ((range (N+1)).filter Nat.Prime) s K = 0 := by
  rw [primeSign_average_primitive_spectrum]
  suffices h : ∀ q ∈ primitiveRatioPairs N, ¬(∀ p ∈ (range (N+1)).filter Nat.Prime,
      p ∉ q.1.primeFactors ∧ p ∉ q.2.primeFactors) by
    rw [filter_eq_empty_iff.mpr h, sum_empty, mul_zero]
  intro q hq h
  obtain ⟨hpair,_,hne⟩ := mem_filter.mp hq
  obtain ⟨ha,hb⟩ := mem_product.mp hpair
  have one {a : ℕ} (ha : a ∈ Icc 1 N)
      (hn : ∀ p ∈ (range (N+1)).filter Nat.Prime, p ∉ a.primeFactors) : a=1 := by
    by_contra hn1
    have h₁ := mem_Icc.mp ha
    obtain ⟨p,hp⟩ := Nat.nonempty_primeFactors.mpr (by omega : 1<a)
    have hpr := Nat.mem_primeFactors.mp hp
    exact hn p (mem_filter.mpr ⟨mem_range.mpr (by have := Nat.le_of_dvd h₁.1 hpr.2.1; omega),hpr.1⟩) hp
  exact hne ((one ha fun p hp => (h p hp).1).trans (one hb fun p hp => (h p hp).2).symm)


/-- Summing the twisted original coefficient pairs gives exactly the signed
primitive reading, for every multiplier of the log-frequency difference. -/
theorem signedRatioReading_eq_original (N : ℕ) (P : Finset ℕ) (s : P → ℤˣ) (K : ℝ → ℝ) :
    ∑ q ∈ offDiagPairs N,
      (((primeSignTwist P s q.1 * primeSignTwist P s q.2 : ℤ):ℝ) *
        (coeff q.1 * coeff q.2 * K (Real.log q.1 - Real.log q.2))) =
      signedRatioReading N P s K := by
  let F := fun m n : ℕ => ((primeSignTwist P s m * primeSignTwist P s n : ℤ):ℝ) *
    (coeff m * coeff n * K (Real.log m - Real.log n))
  change (∑ q ∈ offDiagPairs N, F q.1 q.2) = _
  rw [sum_offDiagPairs_eq_sum_ratio N F, signedRatioReading]
  refine sum_congr rfl fun q hq => ?_
  obtain ⟨ha,hb⟩ := mem_product.mp (mem_filter.mp hq).1
  have ha0 := Nat.ne_of_gt (mem_Icc.mp ha).1
  have hb0 := Nat.ne_of_gt (mem_Icc.mp hb).1
  rw [← scale_correlation, sum_mul, mul_sum]
  apply sum_congr rfl
  intro d hd
  have hd0 := Nat.ne_of_gt (mem_Icc.mp (mem_filter.mp hd).1).1
  simp only [F,signed_ratio_scale P s hd0 ha0 hb0, Nat.cast_mul,
    Real.log_mul (Nat.cast_ne_zero.mpr hd0) (Nat.cast_ne_zero.mpr ha0),
    Real.log_mul (Nat.cast_ne_zero.mpr hd0) (Nat.cast_ne_zero.mpr hb0), add_sub_add_left_eq_sub]

/-- Both sides of the diagonal are accessible by multiplicative sign
choices. One sign vector serves the entire selected window. -/
theorem prime_signs_bracket_diagonal (N : ℕ) (K : ℝ → ℝ) :
    let P := (range (N+1)).filter Nat.Prime
    (∃ s : P → ℤˣ, signedRatioReading N P s K ≤ 0) ∧
      ∃ s : P → ℤˣ, 0 ≤ signedRatioReading N P s K := by
  intro P
  have hsum := full_primeSign_average_off_diagonal N K
  constructor
  · by_contra! h
    exact (sum_pos (s:=univ) (fun s _ => h s) univ_nonempty).ne' hsum
  · by_contra! h
    exact (sum_neg (s:=univ) (fun s _ => h s) univ_nonempty).ne hsum


private theorem rough_unit_or_prime {n N Y : ℕ} (hn : n ∈ Icc 1 N) (hcut : N ≤ Y^2)
    (h : ∀ p ∈ (range (Y+1)).filter Nat.Prime, p ∉ n.primeFactors) : n=1 ∨ n.Prime := by
  by_cases h1 : n=1
  · exact Or.inl h1
  right
  by_contra hp
  have hm := (Nat.minFac_sq_le_self (mem_Icc.mp hn).1 hp).trans ((mem_Icc.mp hn).2.trans hcut)
  have hY : n.minFac ≤ Y := by
    by_contra! hlt
    exact hm.not_gt (Nat.pow_lt_pow_left hlt (by decide : 2 ≠ 0))
  have hpr := Nat.minFac_prime h1
  exact h n.minFac (mem_filter.mpr ⟨mem_range.mpr (by omega),hpr⟩)
    (Nat.mem_primeFactors.mpr ⟨hpr, Nat.minFac_dvd _, Nat.ne_of_gt (mem_Icc.mp hn).1⟩)

/-- Beyond the square-root sieve, all surviving close ratios are
prime against prime. Their Möbius signs reinforce for the triangular
bandwidth log 2, giving a nonnegative averaged off-diagonal term. -/
theorem square_root_sign_average_close_nonneg {N Y : ℕ} (hcut : N ≤ Y^2) :
    0 ≤ ∑ s : (range (Y+1)).filter Nat.Prime → ℤˣ,
      signedRatioReading N ((range (Y+1)).filter Nat.Prime) s
        (fun x => max (Real.log 2 - |x|) 0) := by
  rw [primeSign_average_primitive_spectrum]
  refine mul_nonneg (by positivity) (sum_nonneg ?_)
  intro q hq
  obtain ⟨hr, hrough⟩ := mem_filter.mp hq
  obtain ⟨hpair,_,hne⟩ := mem_filter.mp hr
  obtain ⟨ha,hb⟩ := mem_product.mp hpair
  have ha' := rough_unit_or_prime ha hcut (fun p hp => (hrough p hp).1)
  have hb' := rough_unit_or_prime hb hcut (fun p hp => (hrough p hp).2)
  have loglow {a : ℕ} (h : a.Prime) : Real.log 2 ≤ Real.log a :=
    Real.log_le_log (by norm_num) (by exact_mod_cast h.two_le)
  rcases ha' with hau | hap <;> rcases hb' with hbu | hbp
  · exact (hne (hau.trans hbu.symm)).elim
  · simp [hau, abs_of_nonneg (Real.log_natCast_nonneg _), max_eq_right (sub_nonpos.mpr (loglow hbp))]
  · simp [hbu, abs_of_nonneg (Real.log_natCast_nonneg _), max_eq_right (sub_nonpos.mpr (loglow hap))]
  · apply mul_nonneg _ (le_max_right _ _)
    unfold atom coeff mobiusRealCoefficient
    rw [ArithmeticFunction.moebius_apply_prime hap, ArithmeticFunction.moebius_apply_prime hbp]
    apply mul_nonneg _ (primitiveCubicScaleWeight_nonneg ..)
    apply mul_nonneg_of_nonpos_of_nonpos <;>
      exact div_nonpos_of_nonpos_of_nonneg (by norm_num) (Real.sqrt_nonneg _)

private def twistCoeff (P : Finset ℕ) (s : P → ℤˣ) (n : ℕ) : ℝ := (primeSignTwist P s n:ℝ)*coeff n

/-- Energy of the twisted Möbius polynomial in the physical logarithmic
window. This uses the original coefficients at every integer in the horizon. -/
def twistedShortEnergy (N : ℕ) (P : Finset ℕ) (s : P → ℤˣ) (δ : ℝ) : ℝ :=
  ∫ u : ℝ, ‖logWindowSum (fun n => (twistCoeff P s n:ℂ)) (Icc 1 N) δ u‖^2

private theorem twist_pair (P : Finset ℕ) (s : P → ℤˣ) (m n : ℕ) :
    twistCoeff P s m * twistCoeff P s n =
      ((primeSignTwist P s m*primeSignTwist P s n:ℤ):ℝ)*(coeff m*coeff n) := by
  push_cast
  dsimp only [twistCoeff]
  ring

/-- Every sign choice changes only the off-diagonal of the integrated
Gram energy. Its signed primitive spectrum has the triangular multiplier. -/
theorem twisted_short_spectrum (N : ℕ) (P : Finset ℕ) (s : P → ℤˣ) (δ : ℝ) :
    twistedShortEnergy N P s δ = max δ 0 * (∑ n ∈ Icc 1 N, mobiusRealCoefficient n^2/n) +
      signedRatioReading N P s (fun u => max (δ-|u|) 0) := by
  let K := fun u : ℝ => max (δ-|u|) 0
  let F := fun m n : ℕ => twistCoeff P s m * twistCoeff P s n * K (Real.log m-Real.log n)
  have diag (n : ℕ) : F n n = max δ 0 * (mobiusRealCoefficient n^2/n) := by
    simp only [F,K,twist_pair,sign_sq,Int.cast_one,one_mul,sub_self,abs_zero,sub_zero]
    rw [← sq,coeff,div_pow,Real.sq_sqrt (Nat.cast_nonneg n),mul_comm]
  have off : (∑ q ∈ offDiagPairs N, F q.1 q.2) = signedRatioReading N P s K := by
    rw [← signedRatioReading_eq_original]
    exact sum_congr rfl fun q _ => by dsimp only [F]; rw [twist_pair,mul_assoc]
  rw [twistedShortEnergy,integral_normSq_logWindowSum]
  simp only [Complex.conj_ofReal,← Complex.ofReal_mul,Complex.ofReal_re]
  change (∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, F m n) = _ + signedRatioReading N P s K
  rw [← off,sum_offDiagPairs_eq_double,mul_sum,← sum_add_distrib]
  apply sum_congr rfl
  intro m hm
  rw [← diag m,add_comm,sum_erase_add _ _ hm]

/-- Averaging the measured short-interval energy over all prime signs gives
the original diagonal exactly at every length and bandwidth. -/
theorem twisted_short_energy_average (N : ℕ) (δ : ℝ) :
    let P := (range (N+1)).filter Nat.Prime
    ∑ s : P → ℤˣ, twistedShortEnergy N P s δ =
      (Fintype.card (P → ℤˣ):ℝ)*(max δ 0 * ∑ n ∈ Icc 1 N, mobiusRealCoefficient n^2/n) := by
  intro P
  simp only [twisted_short_spectrum,sum_add_distrib,sum_const,card_univ,nsmul_eq_mul]
  rw [full_primeSign_average_off_diagonal,add_zero]


/-- Squarefree products supporting a nonzero multiplicative sign character. -/
def primitiveSignProducts (N : ℕ) : Finset ℕ :=
  ((primitiveRatioPairs N).image (fun q => q.1*q.2)).filter Squarefree

/-- Total reading from all factorizations of a fixed product into a
coprime numerator and denominator. -/
def primitiveProductReading (N m : ℕ) (K : ℝ → ℝ) : ℝ :=
  ∑ q ∈ (primitiveRatioPairs N).filter (fun q => q.1*q.2=m),
    atom N q.1 q.2*K (Real.log q.1-Real.log q.2)

private theorem product_reading_factor (N m : ℕ) (K : ℝ → ℝ) :
    primitiveProductReading N m K = coeff m *
      ∑ q ∈ (primitiveRatioPairs N).filter (fun q => q.1*q.2=m),
        primitiveCubicScaleWeight 0 N q.1 q.2*K (Real.log q.1-Real.log q.2) := by
  rw [primitiveProductReading,mul_sum]
  apply sum_congr rfl
  intro q hq
  obtain ⟨hq, rfl⟩ := mem_filter.mp hq
  have hc := (mem_filter.mp hq).2.1
  unfold atom coeff mobiusRealCoefficient
  rw [moebius_mul_of_coprime hc,Int.cast_mul,Nat.cast_mul,Real.sqrt_mul (Nat.cast_nonneg _)]
  ring

/-- Group the twisted Gram spectrum by its squarefree prime character. -/
theorem signed_product_expansion (N : ℕ) (P : Finset ℕ) (s : P → ℤˣ) (K : ℝ → ℝ) :
    signedRatioReading N P s K = ∑ m ∈ primitiveSignProducts N,
      (primeSignTwist P s m:ℝ)*primitiveProductReading N m K := by
  let F (q : ℕ × ℕ) := q.1*q.2
  let S := primitiveRatioPairs N
  have maps : ∀ q ∈ S, F q ∈ S.image F := fun _ h => mem_image_of_mem F h
  rw [signedRatioReading,←sum_fiberwise_of_maps_to maps,primitiveSignProducts,sum_filter]
  apply sum_congr rfl
  intro m _
  by_cases hm : Squarefree m
  · rw [if_pos hm,primitiveProductReading,mul_sum]
    apply sum_congr rfl
    intro q hq
    obtain ⟨h,e⟩ := mem_filter.mp hq
    obtain ⟨ha,hb⟩ := mem_product.mp (mem_filter.mp h).1
    rw [←e,show F q = q.1*q.2 from rfl,sign_mul P s (Nat.ne_of_gt (mem_Icc.mp ha).1)
      (Nat.ne_of_gt (mem_Icc.mp hb).1)]
  · rw [if_neg hm]
    apply sum_eq_zero
    intro q hq
    obtain ⟨h,e⟩ := mem_filter.mp hq
    have hc := (mem_filter.mp h).2.1
    have hz : ¬(Squarefree q.1 ∧ Squarefree q.2) :=
      fun hsf => hm (e ▸ (Nat.squarefree_mul hc).mpr hsf)
    simp [atom_zero_of_nonsquarefree hz]

/-- Every prime in an occupied reduced product lies in the twist horizon. -/
theorem sign_product_support {N m : ℕ} (hm : m ∈ primitiveSignProducts N) :
    m.primeFactors ⊆ (range (N+1)).filter Nat.Prime := by
  obtain ⟨q,hq,rfl⟩ := mem_image.mp (mem_filter.mp hm).1
  obtain ⟨ha,hb⟩ := mem_product.mp (mem_filter.mp hq).1
  intro p hp
  have hd := Nat.mem_primeFactors.mp hp
  apply mem_filter.mpr
  refine ⟨mem_range.mpr ?_,hd.1⟩
  rcases hd.1.dvd_mul.mp hd.2.1 with h | h
  · exact Nat.lt_succ_of_le ((Nat.le_of_dvd (mem_Icc.mp ha).1 h).trans (mem_Icc.mp ha).2)
  · exact Nat.lt_succ_of_le ((Nat.le_of_dvd (mem_Icc.mp hb).1 h).trans (mem_Icc.mp hb).2)

private theorem prime_sign_product_orthogonality {N m n : ℕ}
    (hm : m ∈ primitiveSignProducts N) (hn : n ∈ primitiveSignProducts N) :
    let P := (range (N+1)).filter Nat.Prime
    ∑ s : P → ℤˣ, (primeSignTwist P s m:ℝ)*(primeSignTwist P s n:ℝ) =
      if m=n then (2:ℝ)^P.card else 0 := by
  intro P
  have sm : Squarefree m := (mem_filter.mp hm).2
  have sn : Squarefree n := (mem_filter.mp hn).2
  have he : (∀ p ∈ P, Even (m.factorization p+n.factorization p)) ↔ m=n := by
    constructor
    · intro h
      apply Nat.factorization_inj sm.ne_zero sn.ne_zero
      ext p
      by_cases hp : p ∈ P
      · obtain ⟨j,hj⟩ := h p hp
        have hm₁ := sm.natFactorization_le_one p
        have hn₁ := sn.natFactorization_le_one p
        omega
      · have z {a : ℕ} (ha : a ∈ primitiveSignProducts N) : a.factorization p = 0 := by
          by_contra hh
          exact hp (sign_product_support ha (by simpa only [← Nat.support_factorization,
            Finsupp.mem_support_iff] using hh))
        rw [z hm,z hn]
    · rintro rfl p _
      exact ⟨_,rfl⟩
  simp only [←Int.cast_mul,←Int.cast_sum,sum_primeSignTwist_mul,prod_two_or_zero,he]
  split_ifs <;> push_cast <;> rfl

/-- Multiplicative sign measurements recover each product fibre, even
when several directed ratios share its numerator-denominator product. -/
theorem prime_sign_product_readout {N m : ℕ} (hm : m ∈ primitiveSignProducts N) (K : ℝ → ℝ) :
    let P := (range (N+1)).filter Nat.Prime
    ∑ s : P → ℤˣ, signedRatioReading N P s K*(primeSignTwist P s m:ℝ) =
      (2:ℝ)^P.card*primitiveProductReading N m K := by
  intro P
  simp only [signed_product_expansion,sum_mul]
  rw [sum_comm]
  have term (n : ℕ) (hn : n ∈ primitiveSignProducts N) :
      ∑ s : P → ℤˣ, (primeSignTwist P s n:ℝ)*primitiveProductReading N n K*(primeSignTwist P s m:ℝ) =
        if n=m then (2:ℝ)^P.card*primitiveProductReading N m K else 0 := by
    simp_rw [mul_right_comm _ (primitiveProductReading N n K),←sum_mul]
    rw [prime_sign_product_orthogonality hn hm]
    split_ifs with e <;> simp_all
  rw [sum_congr rfl term,sum_ite_eq',if_pos hm]

/-- Exact covariance of two centered sign readings. Only equal squarefree
products can contribute, across every pair of spectral windows. -/
theorem prime_sign_product_covariance (N : ℕ) (K L : ℝ → ℝ) :
    let P := (range (N+1)).filter Nat.Prime
    ∑ s : P → ℤˣ, signedRatioReading N P s K*signedRatioReading N P s L =
      (2:ℝ)^P.card*∑ m ∈ primitiveSignProducts N,
        primitiveProductReading N m K*primitiveProductReading N m L := by
  intro P
  simp_rw [signed_product_expansion N P _ L,mul_sum]
  rw [sum_comm,mul_sum]
  refine sum_congr rfl fun m hm => ?_
  simp_rw [←mul_assoc,←sum_mul]
  rw [prime_sign_product_readout hm,mul_assoc]

/-- Nonnegative windows give positively correlated physical readings:
Möbius multiplicativity gives every factorization in one fibre the same sign. -/
theorem prime_sign_covariance_nonnegative (N : ℕ) (K L : ℝ → ℝ)
    (hK : ∀ x, 0≤K x) (hL : ∀ x, 0≤L x) :
    let P := (range (N+1)).filter Nat.Prime
    0 ≤ ∑ s : P → ℤˣ, signedRatioReading N P s K*signedRatioReading N P s L := by
  intro P
  rw [prime_sign_product_covariance]
  refine mul_nonneg (by positivity) (sum_nonneg fun m _ => ?_)
  rw [product_reading_factor,product_reading_factor,mul_mul_mul_comm]
  exact mul_nonneg (mul_self_nonneg _) (mul_nonneg
    (sum_nonneg fun q _ => mul_nonneg (primitiveCubicScaleWeight_nonneg ..) (hK _))
    (sum_nonneg fun q _ => mul_nonneg (primitiveCubicScaleWeight_nonneg ..) (hL _)))


private theorem twist_abs_one (P : Finset ℕ) (s : P → ℤˣ) (m : ℕ) :
    |(primeSignTwist P s m:ℝ)| = 1 := by
  have h := sign_sq P s m
  have he : (primeSignTwist P s m:ℝ)^2 = (1:ℝ)^2 := by
    rw [sq,one_pow]
    exact_mod_cast h
  simpa only [abs_one] using (sq_eq_sq_iff_abs_eq_abs _ _).mp he

private theorem all_minus_on_product {N m : ℕ} (hm : m ∈ primitiveSignProducts N) :
    let P := (range (N+1)).filter Nat.Prime
    primeSignTwist P (fun _ => -1) m = ArithmeticFunction.moebius m := by
  intro P
  have hs : m.factorization.support ⊆ P := by
    rw [Nat.support_factorization]
    exact sign_product_support hm
  have he := sum_subset (f:=fun p => m.factorization p) hs (fun _ _ hn => Finsupp.notMem_support_iff.mp hn)
  rw [ArithmeticFunction.moebius_apply_of_squarefree (mem_filter.mp hm).2,
    ArithmeticFunction.cardFactors_eq_sum_factorization]
  simp only [primeSignTwist,Units.val_neg,Units.val_one,←pow_sum,sum_coe_sort,Finsupp.sum,he]

/-- The all-negative prime choice attains the absolute envelope of every
nonnegative spectral window at once. Each squarefree product then carries
the sign of its own Möbius coefficient. -/
theorem all_minus_primitive_envelope (N : ℕ) (K : ℝ → ℝ) (hK : ∀ x, 0≤K x) :
    let P := (range (N+1)).filter Nat.Prime
    signedRatioReading N P (fun _ => -1) K = ∑ m ∈ primitiveSignProducts N, |primitiveProductReading N m K| ∧
      ∀ s : P → ℤˣ, |signedRatioReading N P s K| ≤ signedRatioReading N P (fun _ => -1) K := by
  intro P
  have halign (m : ℕ) (hm : m ∈ primitiveSignProducts N) :
      (primeSignTwist P (fun _ => -1) m:ℝ)*primitiveProductReading N m K = |primitiveProductReading N m K| := by
    have hχ := twist_abs_one P (fun _ => -1) m
    have hpos : 0 ≤ (primeSignTwist P (fun _ => -1) m:ℝ)*primitiveProductReading N m K := by
      rw [all_minus_on_product hm,product_reading_factor,←mul_assoc]
      refine mul_nonneg ?_ (sum_nonneg fun q _ => mul_nonneg (primitiveCubicScaleWeight_nonneg ..) (hK _))
      rw [coeff,mobiusRealCoefficient,←mul_div_assoc]
      exact div_nonneg (mul_self_nonneg _) (Real.sqrt_nonneg _)
    calc _ = |(primeSignTwist P (fun _ => -1) m:ℝ)*primitiveProductReading N m K| := (abs_of_nonneg hpos).symm
         _ = _ := by rw [abs_mul,hχ,one_mul]
  have h : signedRatioReading N P (fun _ => -1) K = _ :=
    (signed_product_expansion N P _ K).trans (sum_congr rfl halign)
  refine ⟨h,fun s => ?_⟩
  rw [h,signed_product_expansion]
  exact (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun m _ => by rw [abs_mul,twist_abs_one,one_mul])

/-- One prime-sign vector attains the average square variation on a whole
finite family of spectral increments. Kernels may be signed and dependent. -/
theorem exists_prime_sign_for_joint_square_variation {ι : Type*} (S : Finset ι)
    (N : ℕ) (K : ι → ℝ → ℝ) :
    let P := (range (N+1)).filter Nat.Prime
    ∃ s : P → ℤˣ, (∑ j ∈ S, ∑ m ∈ primitiveSignProducts N, primitiveProductReading N m (K j)^2) ≤
      ∑ j ∈ S, signedRatioReading N P s (K j)^2 := by
  classical
  intro P
  have H (j : ι) := prime_sign_product_covariance N (K j) (K j)
  simp only [←sq] at H
  have hsum : ∑ s : P → ℤˣ, ∑ j ∈ S, signedRatioReading N P s (K j)^2 =
      (2:ℝ)^P.card*∑ j ∈ S, ∑ m ∈ primitiveSignProducts N, primitiveProductReading N m (K j)^2 := by
    rw [sum_comm,mul_sum]
    exact sum_congr rfl fun j _ => H j
  by_contra! h
  have hlt := sum_lt_sum_of_nonempty (s:=univ) univ_nonempty (fun s _ => h s)
  have hcard : Fintype.card (P → ℤˣ) = 2^P.card := by
    rw [Fintype.card_fun,Fintype.card_coe,Fintype.card_units_int]
  rw [hsum,sum_const,card_univ,hcard,nsmul_eq_mul,Nat.cast_pow,Nat.cast_ofNat] at hlt
  exact hlt.false

end
end GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.MoebiusGram
