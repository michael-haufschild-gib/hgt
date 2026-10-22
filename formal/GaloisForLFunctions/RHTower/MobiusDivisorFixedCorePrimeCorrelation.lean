import GaloisForLFunctions.RHTower.MobiusDivisorFixedCoreEnergyLimit
/-!
# Literal prime-release correlation of a fixed processed head

Prime insertion acts on every squarefree sample by the exact difference
between its r and p*r scales. Splitting the complete squarefree source
by p-divisibility cancels the diagonal terms and identifies the actual
energy release with a signed head correlation. Its entire quotient tail
has an explicit absolute bound, with no sign premise or numerical input.
-/

noncomputable section
open Finset Filter Topology
namespace RHTower

private lemma sample_vanish (P : Finset ℕ) {M r : ℕ} (hr : 0<r) (hMr : M≤r) :
    mobiusDivisorInterpolatedFibre M r P ∅=0 := by
  have h0 : mobiusDivisorSelectionFibre 0 P ∅=0 := by
    simp [mobiusDivisorSelectionFibre, mobiusDivisorSelectionIndices, subsetLabelFibre]
  have h1 : mobiusDivisorSelectionFibre 1 P ∅=0 := by
    simp [mobiusDivisorSelectionFibre, mobiusDivisorSelectionIndices, subsetLabelFibre]
  rcases hMr.eq_or_lt with rfl | hlt
  · have hw : divisorPrimeClipWeight M M=0 := by simp [divisorPrimeClipWeight, Nat.div_self hr]
    simp [mobiusDivisorInterpolatedFibre, Nat.div_self hr, hw, h1]
  · simp [mobiusDivisorInterpolatedFibre, Nat.div_eq_of_lt hlt, h0, h1]

lemma source_mem_insert {p r M : ℕ} (hp : p.Prime) (P : Finset ℕ) :
    r ∈ fixedCoreSquarefreeIndices (insert p P) M ↔
      r ∈ fixedCoreSquarefreeIndices P M ∧ ¬p∣r := by
  simp only [fixedCoreSquarefreeIndices, mem_filter, mem_Icc]
  constructor
  · rintro ⟨hr,hs,hd⟩
    refine ⟨⟨hr,hs,hd.mono_right (subset_insert _ _)⟩,?_⟩
    intro hpr
    exact disjoint_left.mp hd (Nat.mem_primeFactors.mpr ⟨hp,hpr,by omega⟩) (mem_insert_self _ _)
  · rintro ⟨⟨hr,hs,hd⟩,hpr⟩
    refine ⟨hr,hs,disjoint_left.mpr ?_⟩
    intro q hqr hqP
    rcases mem_insert.mp hqP with rfl | hqP
    · exact hpr (Nat.mem_primeFactors.mp hqr).2.1
    · exact disjoint_left.mp hd hqr hqP

lemma source_mul {p r : ℕ} (hp : p.Prime) (P : Finset ℕ)
    (hpP : p∉P) (hr : 0<r) :
    Squarefree (p*r) ∧ Disjoint (p*r).primeFactors P ↔
      Squarefree r ∧ Disjoint r.primeFactors (insert p P) := by
  rw [Nat.squarefree_mul_iff, Nat.primeFactors_mul hp.ne_zero hr.ne', hp.primeFactors]
  constructor
  · rintro ⟨⟨hc,_,hs⟩,hd⟩
    refine ⟨hs,disjoint_left.mpr ?_⟩
    intro q hqr hqP
    rcases mem_insert.mp hqP with rfl | hqP
    · exact (hp.coprime_iff_not_dvd.mp hc) (Nat.mem_primeFactors.mp hqr).2.1
    · exact disjoint_left.mp hd (mem_union_right _ hqr) hqP
  · rintro ⟨hs,hd⟩
    refine ⟨⟨hp.coprime_iff_not_dvd.mpr ?_,hp.squarefree,hs⟩, disjoint_left.mpr ?_⟩
    · intro hpr
      exact disjoint_left.mp hd (Nat.mem_primeFactors.mpr ⟨hp,hpr,hr.ne'⟩) (mem_insert_self _ _)
    · intro q hq hqP
      rcases mem_union.mp hq with hq | hq
      · exact hpP ((mem_singleton.mp hq) ▸ hqP)
      · exact disjoint_left.mp hd hq (mem_insert_of_mem hqP)

lemma source_split {p : ℕ} (hp : p.Prime) (P : Finset ℕ)
    (hpP : p∉P) (M : ℕ) (f : ℕ → ℝ) :
    (∑ r ∈ fixedCoreSquarefreeIndices P M, f r) =
      (∑ r ∈ fixedCoreSquarefreeIndices (insert p P) M, f r)+
      ∑ r ∈ fixedCoreSquarefreeIndices (insert p P) (M/p), f (p*r) := by
  let S := fixedCoreSquarefreeIndices P M
  have hfree : S.filter (fun r => ¬p∣r) = fixedCoreSquarefreeIndices (insert p P) M := by
    ext r
    exact mem_filter.trans (source_mem_insert hp P).symm
  have hdiv : (∑ r ∈ fixedCoreSquarefreeIndices (insert p P) (M/p), f (p*r)) =
      ∑ r ∈ S.filter (fun r => p∣r), f r := by
    apply sum_nbij' (fun r => p*r) (fun r => r/p)
    · intro r hr
      obtain ⟨hr,hs⟩ := mem_filter.mp hr
      have hr' := mem_Icc.mp hr
      apply mem_filter.mpr
      refine ⟨mem_filter.mpr ⟨mem_Icc.mpr ⟨by nlinarith [hp.pos], ?_⟩,
        (source_mul hp P hpP hr'.1).mpr hs⟩,dvd_mul_right _ _⟩
      simpa [mul_comm] using (Nat.le_div_iff_mul_le hp.pos).mp hr'.2
    · intro r hr
      obtain ⟨hr,hpr⟩ := mem_filter.mp hr
      obtain ⟨hr,hs,hd⟩ := mem_filter.mp hr
      have hr' := mem_Icc.mp hr
      have he : p*(r/p)=r := Nat.mul_div_cancel' hpr
      have hq : 0<r/p := by nlinarith
      apply mem_filter.mpr
      refine ⟨mem_Icc.mpr ⟨hq,Nat.div_le_div_right hr'.2⟩,?_⟩
      apply (source_mul hp P hpP hq).mp
      rw [he]
      exact ⟨hs,hd⟩
    · intro r _
      exact Nat.mul_div_cancel_left r hp.pos
    · intro r hr
      exact Nat.mul_div_cancel' (mem_filter.mp hr).2
    · intro r _
      rfl
  rw [hdiv, ← hfree]
  exact (sum_filter_not_add_sum_filter S (fun r => p∣r) f).symm

private lemma fibre_sample (P : Finset ℕ) (M : ℕ) {r : ℕ}
    (hs : Squarefree r) (hd : Disjoint r.primeFactors P) :
    mobiusDivisorSelectionFibre M P r.primeFactors =
      Real.sqrt r*((ArithmeticFunction.moebius r : ℤ) : ℝ)*mobiusDivisorInterpolatedFibre M r P ∅ := by
  simpa only [Nat.prod_primeFactors_of_squarefree hs] using
    mobiusDivisorSelectionFibre_product_interpolation M P r.primeFactors
      (fun q hq => (Nat.mem_primeFactors.mp hq).1) hd

/-- Actual squarefree head samples obey the prime merger at both physical
scales, retaining the sign and the complete clipped endpoint. -/
theorem mobiusDivisorInterpolatedHead_insert_prime
    (P : Finset ℕ) {p r : ℕ} (hp : p.Prime) (hpP : p∉P)
    (hr : 0<r) (hs : Squarefree r) (hd : Disjoint r.primeFactors (insert p P)) (M : ℕ) :
    mobiusDivisorInterpolatedFibre M r (insert p P) ∅ =
      mobiusDivisorInterpolatedFibre M r P ∅-
        Real.sqrt p*mobiusDivisorInterpolatedFibre M (p*r) P ∅ := by
  have hpR : p∉r.primeFactors := fun h => disjoint_left.mp hd h (mem_insert_self _ _)
  have hcop : p.Coprime r := hp.coprime_iff_not_dvd.mpr (by
    intro h
    exact hpR (Nat.mem_primeFactors.mpr ⟨hp,h,hr.ne'⟩))
  have hpr := (source_mul hp P hpP hr).mpr ⟨hs,hd⟩
  have hfac : (p*r).primeFactors=insert p r.primeFactors := by
    rw [Nat.primeFactors_mul hp.ne_zero hr.ne',hp.primeFactors,singleton_union]
  have hmu : (((ArithmeticFunction.moebius r : ℤ) : ℝ))^(2 : ℕ)=1 := by
    exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree hs
  have hm : (((ArithmeticFunction.moebius (p*r) : ℤ) : ℝ)) =
      -((ArithmeticFunction.moebius r : ℤ) : ℝ) := by
    rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop,
      ArithmeticFunction.moebius_apply_prime hp]
    push_cast
    ring
  have hb := mobiusDivisorSelectionFibre_insert M P r.primeFactors p
  rw [if_neg hpR, fibre_sample (insert p P) M hs hd,
    fibre_sample P M hs (hd.mono_right (subset_insert _ _)), ← hfac,
    fibre_sample P M hpr.1 hpr.2, hm, Nat.cast_mul,
    Real.sqrt_mul (Nat.cast_nonneg p)] at hb
  have hc : Real.sqrt r*((ArithmeticFunction.moebius r : ℤ) : ℝ) ≠0 := by
    apply mul_ne_zero (Real.sqrt_ne_zero'.mpr (by exact_mod_cast hr))
    intro hz
    rw [hz] at hmu
    norm_num at hmu
  apply (mul_left_cancel₀ hc)
  rw [hb]
  ring

/-- The complete prime-merger reserve is the literal signed correlation of
one fixed processed head at scales r and p*r. No term is dropped. -/
theorem mobiusDivisorSelectionEnergy_prime_release_eq_correlation
    (P : Finset ℕ) {p : ℕ} (hp : p.Prime) (hpP : p∉P) (M : ℕ) :
    mobiusDivisorSelectionEnergy M P-mobiusDivisorSelectionEnergy M (insert p P) =
      2*Real.sqrt p*∑ r ∈ fixedCoreSquarefreeIndices (insert p P) M,
        (r : ℝ)*mobiusDivisorInterpolatedFibre M r P ∅*
          mobiusDivisorInterpolatedFibre M (p*r) P ∅ := by
  rw [mobiusDivisorSelectionEnergy_eq_inclusive_squarefree,
    mobiusDivisorSelectionEnergy_eq_inclusive_squarefree,source_split hp P hpP M]
  have he : (∑ r ∈ fixedCoreSquarefreeIndices (insert p P) (M/p),
      ((p*r : ℕ) : ℝ)*(mobiusDivisorInterpolatedFibre M (p*r) P ∅)^(2 : ℕ)) =
      ∑ r ∈ fixedCoreSquarefreeIndices (insert p P) M,
        ((p*r : ℕ) : ℝ)*(mobiusDivisorInterpolatedFibre M (p*r) P ∅)^(2 : ℕ) := by
    apply sum_subset
    · intro r hr
      obtain ⟨hr,hs⟩ := mem_filter.mp hr
      have hr' := mem_Icc.mp hr
      exact mem_filter.mpr ⟨mem_Icc.mpr ⟨hr'.1,hr'.2.trans (Nat.div_le_self M p)⟩,hs⟩
    · intro r hr hnot
      obtain ⟨hr,hs⟩ := mem_filter.mp hr
      have hr' := mem_Icc.mp hr
      have hsmall : ¬r≤M/p := fun h => hnot (mem_filter.mpr ⟨mem_Icc.mpr ⟨hr'.1,h⟩,hs⟩)
      have hb : M≤p*r := by
        have hn : ¬r*p≤M := fun h => hsmall ((Nat.le_div_iff_mul_le hp.pos).mpr h)
        nlinarith
      rw [sample_vanish P (by nlinarith [hp.pos] : 0<p*r) hb]
      ring
  rw [he, ← sum_add_distrib, ← sum_sub_distrib, mul_sum]
  apply sum_congr rfl
  intro r hr
  obtain ⟨hr,hs,hd⟩ := mem_filter.mp hr
  rw [mobiusDivisorInterpolatedHead_insert_prime P hp hpP (mem_Icc.mp hr).1 hs hd M]
  push_cast
  have hsq := Real.sq_sqrt (Nat.cast_nonneg p)
  nlinarith [congrArg (fun z : ℝ => z*((r : ℝ)*
    (mobiusDivisorInterpolatedFibre M (p*r) P ∅)^(2 : ℕ))) hsq]

/-- One literal signed term in the complete prime-release correlation. -/
def mobiusDivisorPrimeCorrelationTerm (P : Finset ℕ) (p M r : ℕ) : ℝ :=
  2*Real.sqrt p*(r : ℝ)*mobiusDivisorInterpolatedFibre M r P ∅*
    mobiusDivisorInterpolatedFibre M (p*r) P ∅

/-- One literal prime-release correlation term is the signed product of its
two actual source fibres. -/
theorem mobiusDivisorPrimeCorrelationTerm_eq_fibres (P : Finset ℕ) {p r : ℕ}
    (hp : p.Prime) (hpP : p∉P) (hr : 0<r) (hs : Squarefree r)
    (hd : Disjoint r.primeFactors (insert p P)) (M : ℕ) :
    mobiusDivisorPrimeCorrelationTerm P p M r =
      -2*mobiusDivisorSelectionFibre M P r.primeFactors*
        mobiusDivisorSelectionFibre M P (insert p r.primeFactors) := by
  have hpR : p∉r.primeFactors := fun h => disjoint_left.mp hd h (mem_insert_self _ _)
  have hm : (((ArithmeticFunction.moebius r : ℤ) : ℝ))^(2 : ℕ)=1 := by
    exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree hs
  have hb := mobiusDivisorSelectionFibre_insert M P r.primeFactors p
  rw [if_neg hpR, fibre_sample (insert p P) M hs hd,
    fibre_sample P M hs (hd.mono_right (subset_insert _ _)),
    mobiusDivisorInterpolatedHead_insert_prime P hp hpP hr hs hd M] at hb
  have he : mobiusDivisorSelectionFibre M P (insert p r.primeFactors) =
      -(Real.sqrt r*((ArithmeticFunction.moebius r : ℤ) : ℝ))*
        Real.sqrt p*mobiusDivisorInterpolatedFibre M (p*r) P ∅ := by linarith
  rw [he, fibre_sample P M hs (hd.mono_right (subset_insert _ _))]
  have hc : (Real.sqrt r*((ArithmeticFunction.moebius r : ℤ) : ℝ))^(2 : ℕ)=(r : ℝ) := by
    rw [mul_pow,Real.sq_sqrt (Nat.cast_nonneg r),hm,mul_one]
  calc
    _ = 2*Real.sqrt p*(Real.sqrt r*((ArithmeticFunction.moebius r : ℤ) : ℝ))^(2 : ℕ)*
        mobiusDivisorInterpolatedFibre M r P ∅*mobiusDivisorInterpolatedFibre M (p*r) P ∅ := by
      rw [hc]
      rfl
    _ = _ := by ring

private lemma correlation_point_bound (P : Finset ℕ) (hP : ∀ q∈P,q.Prime) {p r : ℕ}
    (hp : p.Prime) (hpP : p∉P) (hr : 0<r) (hs : Squarefree r)
    (hd : Disjoint r.primeFactors (insert p P)) (M : ℕ) :
    |mobiusDivisorPrimeCorrelationTerm P p M r| ≤
      2*((3/5:ℝ)*2^(P.card-1))^(2 : ℕ)*(M : ℝ) := by
  have hR : ∀ q∈r.primeFactors,q.Prime := fun q hq => (Nat.mem_primeFactors.mp hq).1
  have hRp : ∀ q∈insert p r.primeFactors,q.Prime := by simpa using And.intro hp hR
  have h0 := abs_mobiusDivisorSelectionFibre_le_source_amplitude M P r.primeFactors hP hR
  have h1 := abs_mobiusDivisorSelectionFibre_le_source_amplitude M P (insert p r.primeFactors) hP hRp
  rw [mobiusDivisorPrimeCorrelationTerm_eq_fibres P hp hpP hr hs hd M, abs_mul, abs_mul]
  rw [abs_neg,abs_of_nonneg (by norm_num : (0:ℝ)≤2)]
  calc
    _ ≤ (2*((3/5:ℝ)*2^(P.card-1)*Real.sqrt M))*
        ((3/5:ℝ)*2^(P.card-1)*Real.sqrt M) := by
      exact mul_le_mul (mul_le_mul_of_nonneg_left h0 (by norm_num)) h1
        (abs_nonneg _) (by positivity)
    _ = _ := by nlinarith [Real.sq_sqrt (Nat.cast_nonneg M)]

/-- The entire actual signed prime correlation has an absolute reciprocal-depth
tail bound. No cancellation or sign assumption is used to discard the tail. -/
theorem mobiusDivisorPrimeCorrelation_absolute_tail_le
    (P : Finset ℕ) (hP : ∀ q∈P,q.Prime) {p : ℕ} (hp : p.Prime) (hpP : p∉P)
    (M : ℕ) {T : ℕ} (hT : 0<T) :
    (∑ r ∈ (fixedCoreSquarefreeIndices (insert p P) M).filter (fun r => T≤M/r),
      |mobiusDivisorPrimeCorrelationTerm P p M r|) ≤
        (2*((3/5:ℝ)*2^(P.card-1))^(2 : ℕ)/(T : ℝ))*(M : ℝ)^(2 : ℕ) := by
  let C : ℝ := (3/5:ℝ)*2^(P.card-1)
  let A := (fixedCoreSquarefreeIndices (insert p P) M).filter (fun r => T≤M/r)
  have hcard : A.card ≤ M/T := by
    have hs : A ⊆ Icc 1 (M/T) := by
      intro r hr
      obtain ⟨hr,hquot⟩ := mem_filter.mp hr
      have hr' := mem_Icc.mp (mem_filter.mp hr).1
      apply mem_Icc.mpr
      refine ⟨hr'.1,(Nat.le_div_iff_mul_le hT).mpr ?_⟩
      simpa only [mul_comm] using (Nat.le_div_iff_mul_le hr'.1).mp hquot
    simpa using card_le_card hs
  calc
    _ ≤ ∑ r ∈ A, 2*C^(2 : ℕ)*(M : ℝ) := by
      apply sum_le_sum
      intro r hr
      obtain ⟨hr,_⟩ := mem_filter.mp hr
      obtain ⟨hr,hs,hd⟩ := mem_filter.mp hr
      exact correlation_point_bound P hP hp hpP (mem_Icc.mp hr).1 hs hd M
    _ = (A.card : ℝ)*(2*C^(2 : ℕ)*(M : ℝ)) := by simp
    _ ≤ ((M/T : ℕ) : ℝ)*(2*C^(2 : ℕ)*(M : ℝ)) := by
      apply mul_le_mul_of_nonneg_right (by exact_mod_cast hcard)
      positivity
    _ ≤ ((M : ℝ)/T)*(2*C^(2 : ℕ)*(M : ℝ)) := by
      exact mul_le_mul_of_nonneg_right Nat.cast_div_le (by positivity)
    _ = _ := by dsimp [C]; ring

end RHTower
