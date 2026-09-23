import GaloisForLFunctions.RHTower.MobiusDivisorClippedHomothety

/-!
# Prime-fibre interpolation at every cutoff

Every unprocessed prime fibre is a reflected square-root-scaled interpolation
of the two adjacent quotient-cutoff fibres. Prime-square exclusions and the
clipped last time block are retained. The copied packet has a convex energy
bound, while its merger keeps the complete signed mixed inner product.
-/

noncomputable section
open Finset
namespace RHTower

/-- The smaller retained field at the exact fractional square-root quotient clock. -/
def mobiusDivisorInterpolatedFibre (M p : ℕ) (P R : Finset ℕ) : ℝ :=
  (1-divisorPrimeClipWeight M p)*mobiusDivisorSelectionFibre (M/p) P R+
    divisorPrimeClipWeight M p*mobiusDivisorSelectionFibre (M/p+1) P R

private theorem fibre_succ_eq_sum (N : ℕ) (P R : Finset ℕ) :
    mobiusDivisorSelectionFibre (N+1) P R =
      ∑ d ∈ Icc 1 N,if d.primeFactors \ P=R then mobiusDivisorDilationChannel (N+1) d else 0 := by
  rw [mobiusDivisorSelectionFibre_eq_sum_Icc,sum_Icc_succ_top (by omega : 1 ≤ N+1)]
  have hz : mobiusDivisorDilationChannel (N+1) (N+1)=0 := by simp [mobiusDivisorDilationChannel]
  simp [hz]

/-- An unprocessed prime fibre is exactly the reflected interpolated smaller field at every cutoff. -/
theorem mobiusDivisorSelectionFibre_prime_interpolation {p : ℕ} (hp : p.Prime)
    (M : ℕ) (P R : Finset ℕ) (hpP : p ∉ P) (hpR : p ∉ R) :
    mobiusDivisorSelectionFibre M P (insert p R) =
      -Real.sqrt p*mobiusDivisorInterpolatedFibre M p P R := by
  rw [mobiusDivisorInterpolatedFibre,mobiusDivisorSelectionFibre_eq_sum_Icc M P (insert p R),
    mobiusDivisorSelectionFibre_eq_sum_Icc (M/p) P R,fibre_succ_eq_sum (M/p) P R]
  have hrestrict : (∑ n ∈ Icc 1 M,
      if n.primeFactors \ P=insert p R then mobiusDivisorDilationChannel M n else 0) =
      ∑ n ∈ (Icc 1 M).filter (fun n => p ∣ n),
        if n.primeFactors \ P=insert p R then mobiusDivisorDilationChannel M n else 0 := by
    rw [sum_filter]
    apply sum_congr rfl
    intro n hn
    by_cases hpn : p ∣ n
    · simp [hpn]
    · have hne : n.primeFactors \ P ≠ insert p R := by
        intro he
        have hm : p ∈ n.primeFactors := (mem_sdiff.mp (he.symm ▸ mem_insert_self p R)).1
        exact hpn (Nat.mem_primeFactors.mp hm).2.1
      simp [hpn,hne]
  rw [hrestrict,sum_Icc_filter_dvd_reindex p M hp.pos]
  simp only [mul_add,mul_sum,← sum_add_distrib]
  apply sum_congr rfl
  intro d hd
  have hd0 : d ≠ 0 := by have := (mem_Icc.mp hd).1; omega
  by_cases hpd : p ∣ d
  · have hnotcop : ¬p.Coprime d := fun hc => (hp.coprime_iff_not_dvd.mp hc) hpd
    have hm : ArithmeticFunction.moebius (p*d)=0 :=
      ArithmeticFunction.moebius_eq_zero_of_not_squarefree
        (fun hsf => hnotcop (Nat.coprime_of_squarefree_mul hsf))
    have hz : mobiusDivisorDilationChannel M (p*d)=0 := by simp [mobiusDivisorDilationChannel,hm]
    have hne : d.primeFactors \ P ≠ R := by
      intro he
      have hpD : p ∈ d.primeFactors := Nat.mem_primeFactors.mpr ⟨hp,hpd,hd0⟩
      exact hpR (he ▸ mem_sdiff.mpr ⟨hpD,hpP⟩)
    simp [hz,hne]
  · have hpD : p ∉ d.primeFactors := fun h => hpd (Nat.mem_primeFactors.mp h).2.1
    have hlabel : (p*d).primeFactors \ P=insert p (d.primeFactors \ P) := by
      rw [Nat.primeFactors_mul hp.ne_zero hd0,hp.primeFactors]
      ext q
      simp only [mem_sdiff,mem_union,mem_singleton,mem_insert]
      constructor
      · rintro ⟨hq,hqP⟩
        exact hq.elim Or.inl (fun hq => Or.inr ⟨hq,hqP⟩)
      · rintro (hq|hq)
        · subst q
          exact ⟨Or.inl rfl,hpP⟩
        · exact ⟨Or.inr hq.1,hq.2⟩
    have heq : insert p (d.primeFactors \ P)=insert p R ↔ d.primeFactors \ P=R := by
      constructor
      · intro he
        ext q
        by_cases hq : q=p
        · subst q
          simp [hpD,hpR]
        · have h := Finset.ext_iff.mp he q
          simpa [hq] using h
      · intro he
        rw [he]
    rw [hlabel]
    by_cases he : d.primeFactors \ P=R
    · rw [if_pos (heq.mpr he),if_pos he,if_pos he,
        mobiusDivisorDilationChannel_prime_interpolation hp M d hpd]
      ring
    · rw [if_neg (fun h => he (heq.mp h)),if_neg he,if_neg he]
      ring

/-- Every prime merger subtracts its exact interpolated quotient field, with no large-prime restriction. -/
theorem mobiusDivisorSelectionFibre_insert_interpolation {p : ℕ} (hp : p.Prime)
    (M : ℕ) (P R : Finset ℕ) (hpP : p ∉ P) (hpR : p ∉ R) :
    mobiusDivisorSelectionFibre M (insert p P) R =
      mobiusDivisorSelectionFibre M P R-Real.sqrt p*mobiusDivisorInterpolatedFibre M p P R := by
  rw [mobiusDivisorSelectionFibre_insert,if_neg hpR,
    mobiusDivisorSelectionFibre_prime_interpolation hp M P R hpP hpR]
  ring

/-- The all-cutoff head update uses the same complete arithmetic interpolation. -/
theorem mobiusDivisorSelectionHead_insert_interpolation {p : ℕ} (hp : p.Prime)
    (M : ℕ) (P : Finset ℕ) (hpP : p ∉ P) :
    mobiusDivisorSelectionFibre M (insert p P) ∅ =
      mobiusDivisorSelectionFibre M P ∅-Real.sqrt p*mobiusDivisorInterpolatedFibre M p P ∅ :=
  mobiusDivisorSelectionFibre_insert_interpolation hp M P ∅ hpP (by simp)

/-- Complete all-cutoff merger energy: the removed copy square cancels and the signed cross term survives. -/
theorem mobiusDivisorSelectionEnergy_insert_interpolation {p : ℕ} (hp : p.Prime)
    (M : ℕ) (P : Finset ℕ) (hpM : p<M) (hpP : p ∉ P) :
    mobiusDivisorSelectionEnergy M (insert p P)-mobiusDivisorSelectionEnergy M P =
      (-2*Real.sqrt p)*∑ R ∈ ((mobiusDivisorSelectionPrimes M).erase p).powerset,
        mobiusDivisorSelectionFibre M P R*mobiusDivisorInterpolatedFibre M p P R := by
  let U := mobiusDivisorSelectionPrimes M
  have hpU : p ∈ U := mem_filter.mpr ⟨mem_range.mpr hpM,hp⟩
  have hsplit (f : Finset ℕ → ℝ) : (∑ R ∈ U.powerset,f R) =
      (∑ R ∈ (U.erase p).powerset,f R)+(∑ R ∈ (U.erase p).powerset,f (insert p R)) := by
    conv_lhs => rw [← insert_erase hpU]
    exact sum_powerset_insert (notMem_erase p U) f
  have hpR (R : Finset ℕ) (hR : R ∈ (U.erase p).powerset) : p ∉ R := by
    intro h
    have := (mem_powerset.mp hR) h
    simp at this
  have hz : (∑ R ∈ (U.erase p).powerset,(mobiusDivisorSelectionFibre M (insert p P) (insert p R))^(2 : ℕ))=0 := by
    apply sum_eq_zero
    intro R hR
    rw [mobiusDivisorSelectionFibre_insert]
    simp
  have ha : (∑ R ∈ (U.erase p).powerset,(mobiusDivisorSelectionFibre M (insert p P) R)^(2 : ℕ)) =
      ∑ R ∈ (U.erase p).powerset,
        (mobiusDivisorSelectionFibre M P R-Real.sqrt p*mobiusDivisorInterpolatedFibre M p P R)^(2 : ℕ) := by
    apply sum_congr rfl
    intro R hR
    rw [mobiusDivisorSelectionFibre_insert_interpolation hp M P R hpP (hpR R hR)]
  have hc : (∑ R ∈ (U.erase p).powerset,(mobiusDivisorSelectionFibre M P (insert p R))^(2 : ℕ)) =
      ∑ R ∈ (U.erase p).powerset,(-Real.sqrt p*mobiusDivisorInterpolatedFibre M p P R)^(2 : ℕ) := by
    apply sum_congr rfl
    intro R hR
    rw [mobiusDivisorSelectionFibre_prime_interpolation hp M P R hpP (hpR R hR)]
  change (∑ R ∈ U.powerset,(mobiusDivisorSelectionFibre M (insert p P) R)^(2 : ℕ))-
    (∑ R ∈ U.powerset,(mobiusDivisorSelectionFibre M P R)^(2 : ℕ))=_
  rw [hsplit,hsplit,hz,add_zero,ha,hc,← sum_add_distrib,← sum_sub_distrib,mul_sum]
  apply sum_congr rfl
  intro R hR
  ring

private theorem fibre_zero_outside (N : ℕ) (P R : Finset ℕ)
    (hR : ¬R ⊆ mobiusDivisorSelectionPrimes N) : mobiusDivisorSelectionFibre N P R=0 := by
  unfold mobiusDivisorSelectionFibre subsetLabelFibre
  apply sum_eq_zero
  intro d hd
  have hne : d.primeFactors \ P ≠ R := by
    intro he
    apply hR
    intro p hp
    have hpD := (mem_sdiff.mp (he.symm ▸ hp)).1
    have hdN := mem_Icc.mp (mem_filter.mp hd).1
    have hpd := Nat.le_of_mem_primeFactors hpD
    exact mem_filter.mpr ⟨mem_range.mpr (by omega),(Nat.mem_primeFactors.mp hpD).1⟩
  simp [hne]

/-- Any finite family of retained labels carries at most the complete retained source energy. -/
theorem sum_mobiusDivisorSelectionFibre_sq_le_energy (N : ℕ) (P : Finset ℕ)
    (T : Finset (Finset ℕ)) :
    (∑ R ∈ T,(mobiusDivisorSelectionFibre N P R)^(2 : ℕ)) ≤ mobiusDivisorSelectionEnergy N P := by
  let U := (mobiusDivisorSelectionPrimes N).powerset
  have he : (∑ R ∈ T ∩ U,(mobiusDivisorSelectionFibre N P R)^(2 : ℕ)) =
      ∑ R ∈ T,(mobiusDivisorSelectionFibre N P R)^(2 : ℕ) := by
    apply sum_subset inter_subset_left
    intro R hRT hn
    have hnU : R ∉ U := fun hRU => hn (mem_inter.mpr ⟨hRT,hRU⟩)
    rw [fibre_zero_outside N P R (fun hR => hnU (mem_powerset.mpr hR))]
    simp
  rw [← he]
  exact sum_le_sum_of_subset_of_nonneg inter_subset_right (fun _ _ _ => sq_nonneg _)

/-- Exact interpolation energy, including the nonnegative squared increment defect. -/
theorem sum_mobiusDivisorInterpolatedFibre_sq (M p : ℕ) (P : Finset ℕ)
    (T : Finset (Finset ℕ)) :
    (∑ R ∈ T,(mobiusDivisorInterpolatedFibre M p P R)^(2 : ℕ)) =
      (1-divisorPrimeClipWeight M p)*(∑ R ∈ T,(mobiusDivisorSelectionFibre (M/p) P R)^(2 : ℕ))+
      divisorPrimeClipWeight M p*(∑ R ∈ T,(mobiusDivisorSelectionFibre (M/p+1) P R)^(2 : ℕ))-
      divisorPrimeClipWeight M p*(1-divisorPrimeClipWeight M p)*
        ∑ R ∈ T,(mobiusDivisorSelectionFibre (M/p+1) P R-mobiusDivisorSelectionFibre (M/p) P R)^(2 : ℕ) := by
  rw [mul_sum,mul_sum,mul_sum,← sum_add_distrib,← sum_sub_distrib]
  apply sum_congr rfl
  intro R hR
  unfold mobiusDivisorInterpolatedFibre
  ring

/-- The interpolated packet energy is bounded by the convex combination of both smaller energies. -/
theorem sum_mobiusDivisorInterpolatedFibre_sq_le (M p : ℕ) (hp : 0<p) (P : Finset ℕ)
    (T : Finset (Finset ℕ)) :
    (∑ R ∈ T,(mobiusDivisorInterpolatedFibre M p P R)^(2 : ℕ)) ≤
      (1-divisorPrimeClipWeight M p)*mobiusDivisorSelectionEnergy (M/p) P+
        divisorPrimeClipWeight M p*mobiusDivisorSelectionEnergy (M/p+1) P := by
  have hw0 := divisorPrimeClipWeight_nonneg M p hp
  have hw1 : 0 ≤ 1-divisorPrimeClipWeight M p := by
    have := divisorPrimeClipWeight_lt_one M p hp
    linarith
  have hD := mul_nonneg (mul_nonneg hw0 hw1)
    (sum_nonneg (s := T) (fun R _ => sq_nonneg
      (mobiusDivisorSelectionFibre (M/p+1) P R-mobiusDivisorSelectionFibre (M/p) P R)))
  have hA := mul_le_mul_of_nonneg_left (sum_mobiusDivisorSelectionFibre_sq_le_energy (M/p) P T) hw1
  have hB := mul_le_mul_of_nonneg_left (sum_mobiusDivisorSelectionFibre_sq_le_energy (M/p+1) P T) hw0
  rw [sum_mobiusDivisorInterpolatedFibre_sq]
  linarith only [hD,hA,hB]

/-- Exact prime-containing packet energy is p times the interpolated smaller packet energy. -/
theorem sum_mobiusDivisorPrimeFibre_sq_eq {p : ℕ} (hp : p.Prime) (M : ℕ) (P : Finset ℕ)
    (hpP : p ∉ P) (T : Finset (Finset ℕ)) (hT : ∀ R ∈ T,p ∉ R) :
    (∑ R ∈ T,(mobiusDivisorSelectionFibre M P (insert p R))^(2 : ℕ)) =
      (p : ℝ)*∑ R ∈ T,(mobiusDivisorInterpolatedFibre M p P R)^(2 : ℕ) := by
  rw [mul_sum]
  apply sum_congr rfl
  intro R hR
  rw [mobiusDivisorSelectionFibre_prime_interpolation hp M P R hpP (hT R hR),
    mul_pow,neg_sq,Real.sq_sqrt (Nat.cast_nonneg p)]

/-- All unprocessed prime-containing source energy has an unconditional adjacent-cutoff budget. -/
theorem sum_mobiusDivisorPrimeFibre_sq_le {p : ℕ} (hp : p.Prime) (M : ℕ) (P : Finset ℕ)
    (hpP : p ∉ P) (T : Finset (Finset ℕ)) (hT : ∀ R ∈ T,p ∉ R) :
    (∑ R ∈ T,(mobiusDivisorSelectionFibre M P (insert p R))^(2 : ℕ)) ≤
      (p : ℝ)*((1-divisorPrimeClipWeight M p)*mobiusDivisorSelectionEnergy (M/p) P+
        divisorPrimeClipWeight M p*mobiusDivisorSelectionEnergy (M/p+1) P) := by
  rw [sum_mobiusDivisorPrimeFibre_sq_eq hp M P hpP T hT]
  exact mul_le_mul_of_nonneg_left (sum_mobiusDivisorInterpolatedFibre_sq_le M p hp.pos P T)
    (Nat.cast_nonneg p)
end RHTower
