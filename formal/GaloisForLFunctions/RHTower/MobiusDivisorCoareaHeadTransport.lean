import GaloisForLFunctions.RHTower.MobiusDivisorLatePrimeFibres

/-!
# Exact coarea transport along isolated late-prime fibres

Retain signed fibre mass `F_R` and its original absolute mass `A_R`.
Writing `f = F_∅`, `a = A_∅`, and `K = ∑_{R ≠ ∅} F_R² / A_R`, define
the head action `H = f² + a K` and slope `g = K - a - 2 f`.

Every fresh prime `p` with `M ≤ 2 p` is an isolated nonpositive source
coefficient. If `b = |C_p|`, processing it sends `(a,f,K)` to
`(a+b,f-b,K-b)`. Thus `g` is invariant and the exact action change is
`b g`. Every fresh late-prime block has the same law with its total
absolute source mass in place of `b`.

When the head has largest absolute fibre mass, its action bounds raw
retained energy. This dominance persists through late-prime mergers.
The invariant slope classifies the sign of every nonzero block action
change. No sign of that slope or global prime-selection bound is assumed
as an unconditional conclusion.
-/

noncomputable section
set_option autoImplicit false
open Finset
namespace RHTower

/-- Original absolute source mass collected in one retained prime-factor cell. -/
def mobiusDivisorFibreAbsoluteMass (M : ℕ) (P R : Finset ℕ) : ℝ :=
  subsetLabelFibre (mobiusDivisorSelectionIndices M) Nat.primeFactors
    (fun d => |mobiusDivisorDilationChannel M d|) P R

/-- Signed conditional energy outside the empty cell, with zero-mass terms zero. -/
def mobiusDivisorNonemptyCoarea (M : ℕ) (P : Finset ℕ) : ℝ :=
  ∑ R ∈ (mobiusDivisorSelectionPrimes M).powerset.erase ∅,
    (mobiusDivisorSelectionFibre M P R)^2 / mobiusDivisorFibreAbsoluteMass M P R

/-- Conditional energy multiplied by the absolute mass of the receiving head. -/
def mobiusDivisorCoareaHeadAction (M : ℕ) (P : Finset ℕ) : ℝ :=
  (mobiusDivisorSelectionFibre M P ∅)^2 +
    mobiusDivisorFibreAbsoluteMass M P ∅ * mobiusDivisorNonemptyCoarea M P

/-- Exact slope of head action with respect to incoming isolated negative mass. -/
def mobiusDivisorCoareaHeadSlope (M : ℕ) (P : Finset ℕ) : ℝ :=
  mobiusDivisorNonemptyCoarea M P - mobiusDivisorFibreAbsoluteMass M P ∅ -
    2 * mobiusDivisorSelectionFibre M P ∅

/-- Absolute cell mass is nonnegative at every actual retained state. -/
theorem mobiusDivisorFibreAbsoluteMass_nonneg (M : ℕ) (P R : Finset ℕ) :
    0 ≤ mobiusDivisorFibreAbsoluteMass M P R := by
  unfold mobiusDivisorFibreAbsoluteMass subsetLabelFibre
  exact sum_nonneg (fun _ _ => by split_ifs <;> positivity)

/-- Signed mass in a cell is bounded by its original absolute source mass. -/
theorem abs_mobiusDivisorSelectionFibre_le_absoluteMass (M : ℕ) (P R : Finset ℕ) :
    |mobiusDivisorSelectionFibre M P R| ≤ mobiusDivisorFibreAbsoluteMass M P R := by
  unfold mobiusDivisorSelectionFibre mobiusDivisorFibreAbsoluteMass subsetLabelFibre
  refine (abs_sum_le_sum_abs _ _).trans_eq ?_
  apply sum_congr rfl
  intro d _
  split_ifs <;> simp

private lemma late_index {M p d : ℕ}
    (hd : d ∈ mobiusDivisorSelectionIndices M) (hM : M ≤ 2*p)
    (hpd : p ∈ d.primeFactors) : d=p := by
  have hdM := mem_Icc.mp (mem_filter.mp hd).1
  obtain ⟨hp,hdiv,hd0⟩ := Nat.mem_primeFactors.mp hpd
  obtain ⟨k,hk⟩ := hdiv
  have hk0 : 1 ≤ k := by
    by_contra h
    have hz : k=0 := by omega
    rw [hz,Nat.mul_zero] at hk
    omega
  have hk1 : k=1 := by
    by_contra h
    have hkle : 2 ≤ k := by omega
    have hm := Nat.mul_le_mul_left p hkle
    omega
  simpa only [hk1,Nat.mul_one] using hk

/-- A retained cell containing an unprocessed late prime is its singleton or zero. -/
theorem mobiusDivisorFibreAbsoluteMass_late_prime {M p : ℕ} (hp : p.Prime)
    (hpM : p<M) (hM : M ≤ 2*p) (P R : Finset ℕ) (hpP : p ∉ P) (hpR : p ∈ R) :
    mobiusDivisorFibreAbsoluteMass M P R =
      if R={p} then |mobiusDivisorDilationChannel M p| else 0 := by
  have hpi : p ∈ mobiusDivisorSelectionIndices M :=
    mem_filter.mpr ⟨mem_Icc.mpr ⟨hp.pos,by omega⟩,hp.squarefree⟩
  unfold mobiusDivisorFibreAbsoluteMass subsetLabelFibre
  rw [sum_eq_single p]
  · have he : p.primeFactors \ P = {p} := by simp [hp.primeFactors,hpP]
    rw [he]
    by_cases h : R={p}
    · simp [h]
    · simp [h,Ne.symm h]
  · intro d hd hdp
    have hn : d.primeFactors \ P ≠ R := by
      intro he
      exact hdp (late_index hd hM (mem_sdiff.mp (he.symm ▸ hpR)).1)
    rw [if_neg hn]
  · exact fun hn => (hn hpi).elim

/-- Processing a late prime transfers precisely its absolute coefficient mass to the head. -/
theorem mobiusDivisorFibreAbsoluteMass_insert_late_prime {M p : ℕ} (hp : p.Prime)
    (hpM : p<M) (hM : M ≤ 2*p) (P R : Finset ℕ) (hpP : p ∉ P) :
    mobiusDivisorFibreAbsoluteMass M (insert p P) R =
      if R=∅ then mobiusDivisorFibreAbsoluteMass M P ∅+|mobiusDivisorDilationChannel M p|
      else if R={p} then 0 else mobiusDivisorFibreAbsoluteMass M P R := by
  have hs := mobiusDivisorFibreAbsoluteMass_late_prime hp hpM hM P {p} hpP (mem_singleton_self p)
  simp only [if_true] at hs
  change subsetLabelFibre _ _ _ (insert p P) R = _
  rw [subsetLabelFibre_insert]
  change (if p ∈ R then 0 else mobiusDivisorFibreAbsoluteMass M P R+
    mobiusDivisorFibreAbsoluteMass M P (insert p R)) = _
  by_cases hR0 : R=∅
  · simp [hR0,hs]
  by_cases hRp : R={p}
  · simp [hRp]
  by_cases hpR : p ∈ R
  · rw [if_pos hpR,if_neg hR0,if_neg hRp,
      mobiusDivisorFibreAbsoluteMass_late_prime hp hpM hM P R hpP hpR,if_neg hRp]
  · have hn : insert p R ≠ {p} := by
      intro he
      apply hR0
      apply eq_empty_iff_forall_notMem.mpr
      intro x hx
      have hxp : x=p := mem_singleton.mp (he ▸ mem_insert_of_mem hx)
      exact hpR (hxp ▸ hx)
    rw [if_neg hpR,if_neg hR0,if_neg hRp,
      mobiusDivisorFibreAbsoluteMass_late_prime hp hpM hM P (insert p R) hpP
        (mem_insert_self p R),if_neg hn,add_zero]

private lemma square_div_abs (x : ℝ) : x^2/|x|=|x| := by
  by_cases hx : x=0
  · simp [hx]
  apply (div_eq_iff (abs_ne_zero.mpr hx)).mpr
  nlinarith only [sq_abs x]

/-- Removing a pure negative singleton removes its absolute mass from nonempty coarea. -/
theorem mobiusDivisorNonemptyCoarea_insert_late_prime {M p : ℕ} (hp : p.Prime)
    (hpM : p<M) (hM : M ≤ 2*p) (P : Finset ℕ) (hpP : p ∉ P) :
    mobiusDivisorNonemptyCoarea M (insert p P) =
      mobiusDivisorNonemptyCoarea M P - |mobiusDivisorDilationChannel M p| := by
  have hpU : p ∈ mobiusDivisorSelectionPrimes M := mem_filter.mpr ⟨mem_range.mpr hpM,hp⟩
  have hmem : ({p}:Finset ℕ) ∈ (mobiusDivisorSelectionPrimes M).powerset.erase ∅ := by
    simp [hpU]
  have hpoint (R : Finset ℕ) (hR : R ∈ (mobiusDivisorSelectionPrimes M).powerset.erase ∅) :
      (mobiusDivisorSelectionFibre M (insert p P) R)^2 /
        mobiusDivisorFibreAbsoluteMass M (insert p P) R =
      (mobiusDivisorSelectionFibre M P R)^2 / mobiusDivisorFibreAbsoluteMass M P R -
        (if R={p} then |mobiusDivisorDilationChannel M p| else 0) := by
    have hR0 : R ≠ ∅ := (mem_erase.mp hR).1
    rw [mobiusDivisorSelectionFibre_insert_late_prime hp hpM hM P R hpP,
      mobiusDivisorFibreAbsoluteMass_insert_late_prime hp hpM hM P R hpP,if_neg hR0]
    by_cases hRp : R={p}
    · subst R
      rw [mobiusDivisorSelectionFibre_late_prime hp hpM hM P {p} hpP (mem_singleton_self p),
        mobiusDivisorFibreAbsoluteMass_late_prime hp hpM hM P {p} hpP (mem_singleton_self p)]
      simp [square_div_abs]
    · simp [hRp,hR0]
  unfold mobiusDivisorNonemptyCoarea
  rw [sum_congr rfl hpoint,sum_sub_distrib]
  simp [hmem]

/-- No isolated late-prime merger changes the actual head-action slope. -/
theorem mobiusDivisorCoareaHeadSlope_insert_late_prime {M p : ℕ} (hp : p.Prime)
    (hpM : p<M) (hM : M ≤ 2*p) (P : Finset ℕ) (hpP : p ∉ P) :
    mobiusDivisorCoareaHeadSlope M (insert p P) = mobiusDivisorCoareaHeadSlope M P := by
  have hc : mobiusDivisorDilationChannel M p = -|mobiusDivisorDilationChannel M p| := by
    rw [abs_of_nonpos (mobiusDivisorDilationChannel_late_prime_nonpos hp M)]
    ring
  unfold mobiusDivisorCoareaHeadSlope
  rw [mobiusDivisorNonemptyCoarea_insert_late_prime hp hpM hM P hpP,
    mobiusDivisorFibreAbsoluteMass_insert_late_prime hp hpM hM P ∅ hpP,
    mobiusDivisorSelectionHead_insert_late_prime hp hpM hM P hpP,if_pos rfl,hc]
  simp only [abs_neg,abs_abs]
  ring

/-- Exact late-prime action change is incoming absolute mass times the retained slope. -/
theorem mobiusDivisorCoareaHeadAction_insert_late_prime {M p : ℕ} (hp : p.Prime)
    (hpM : p<M) (hM : M ≤ 2*p) (P : Finset ℕ) (hpP : p ∉ P) :
    mobiusDivisorCoareaHeadAction M (insert p P) - mobiusDivisorCoareaHeadAction M P =
      |mobiusDivisorDilationChannel M p| * mobiusDivisorCoareaHeadSlope M P := by
  have hc : mobiusDivisorDilationChannel M p = -|mobiusDivisorDilationChannel M p| := by
    rw [abs_of_nonpos (mobiusDivisorDilationChannel_late_prime_nonpos hp M)]
    ring
  unfold mobiusDivisorCoareaHeadAction mobiusDivisorCoareaHeadSlope
  rw [mobiusDivisorNonemptyCoarea_insert_late_prime hp hpM hM P hpP,
    mobiusDivisorFibreAbsoluteMass_insert_late_prime hp hpM hM P ∅ hpP,
    mobiusDivisorSelectionHead_insert_late_prime hp hpM hM P hpP,if_pos rfl,hc]
  simp only [abs_neg,abs_abs]
  ring

/-- Every fresh late-prime block preserves slope and changes action linearly in its total mass. -/
theorem mobiusDivisorCoareaHead_late_block (M : ℕ) (P L : Finset ℕ)
    (hL : ∀ p ∈ L,p.Prime ∧ p<M ∧ M≤2*p ∧ p ∉ P) :
    mobiusDivisorCoareaHeadSlope M (P ∪ L) = mobiusDivisorCoareaHeadSlope M P ∧
    mobiusDivisorCoareaHeadAction M (P ∪ L) - mobiusDivisorCoareaHeadAction M P =
      (∑ p ∈ L,|mobiusDivisorDilationChannel M p|) * mobiusDivisorCoareaHeadSlope M P := by
  induction L using Finset.induction_on with
  | empty => simp
  | @insert p L hpL ih =>
    have h := hL p (mem_insert_self p L)
    have hL' : ∀ q ∈ L,q.Prime ∧ q<M ∧ M≤2*q ∧ q ∉ P :=
      fun q hq => hL q (mem_insert_of_mem hq)
    have hpPL : p ∉ P ∪ L := by simp [h.2.2.2,hpL]
    have hi := ih hL'
    have hs := mobiusDivisorCoareaHeadSlope_insert_late_prime h.1 h.2.1 h.2.2.1 (P ∪ L) hpPL
    have ha := mobiusDivisorCoareaHeadAction_insert_late_prime h.1 h.2.1 h.2.2.1 (P ∪ L) hpPL
    rw [hi.1] at ha hs
    rw [union_insert,sum_insert hpL]
    constructor
    · exact hs
    · nlinarith only [ha,hi.2]

private lemma fibre_zero_of_mass_zero (M : ℕ) (P R : Finset ℕ)
    (h : mobiusDivisorFibreAbsoluteMass M P R=0) :
    mobiusDivisorSelectionFibre M P R=0 := by
  apply abs_eq_zero.mp
  exact le_antisymm ((abs_mobiusDivisorSelectionFibre_le_absoluteMass M P R).trans_eq h)
    (abs_nonneg _)

/-- The head action is exactly head mass times complete conditional energy, including zero mass. -/
theorem mobiusDivisorCoareaHeadAction_eq_mass_mul_coarea (M : ℕ) (P : Finset ℕ) :
    mobiusDivisorCoareaHeadAction M P = mobiusDivisorFibreAbsoluteMass M P ∅ *
      ∑ R ∈ (mobiusDivisorSelectionPrimes M).powerset,
        (mobiusDivisorSelectionFibre M P R)^2 / mobiusDivisorFibreAbsoluteMass M P R := by
  let a := mobiusDivisorFibreAbsoluteMass M P ∅
  let t := fun R => (mobiusDivisorSelectionFibre M P R)^2 / mobiusDivisorFibreAbsoluteMass M P R
  have hhead : a*t ∅ = (mobiusDivisorSelectionFibre M P ∅)^2 := by
    by_cases hz : mobiusDivisorFibreAbsoluteMass M P ∅=0
    · simp [a,t,hz,fibre_zero_of_mass_zero M P ∅ hz]
    · dsimp [a,t]; field_simp
  have hsum := sum_erase_add (s := (mobiusDivisorSelectionPrimes M).powerset)
    (f := t) (by simp : (∅:Finset ℕ) ∈ (mobiusDivisorSelectionPrimes M).powerset)
  change _ = a*∑ R ∈ (mobiusDivisorSelectionPrimes M).powerset,t R
  rw [← hsum,mul_add,hhead]
  change _ = a*mobiusDivisorNonemptyCoarea M P+(mobiusDivisorSelectionFibre M P ∅)^2
  unfold mobiusDivisorCoareaHeadAction
  ring

/-- A head of maximal absolute mass makes its coarea action an upper bound for raw energy. -/
theorem mobiusDivisorSelectionEnergy_le_coareaHeadAction (M : ℕ) (P : Finset ℕ)
    (hdom : ∀ R ∈ (mobiusDivisorSelectionPrimes M).powerset,
      mobiusDivisorFibreAbsoluteMass M P R ≤ mobiusDivisorFibreAbsoluteMass M P ∅) :
    mobiusDivisorSelectionEnergy M P ≤ mobiusDivisorCoareaHeadAction M P := by
  let a := mobiusDivisorFibreAbsoluteMass M P ∅
  let t := fun R => (mobiusDivisorSelectionFibre M P R)^2 / mobiusDivisorFibreAbsoluteMass M P R
  have hpoint (R : Finset ℕ) (hR : R ∈ (mobiusDivisorSelectionPrimes M).powerset) :
      (mobiusDivisorSelectionFibre M P R)^2 ≤ a*t R := by
    by_cases hz : mobiusDivisorFibreAbsoluteMass M P R=0
    · simp [t,fibre_zero_of_mass_zero M P R hz]
    · have ht : 0 ≤ t R := div_nonneg (sq_nonneg _) (mobiusDivisorFibreAbsoluteMass_nonneg M P R)
      calc
        _ = mobiusDivisorFibreAbsoluteMass M P R*t R := by dsimp [t]; field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_right (hdom R hR) ht
  change (∑ R ∈ (mobiusDivisorSelectionPrimes M).powerset,
    (mobiusDivisorSelectionFibre M P R)^2) ≤ _
  calc
    _ ≤ ∑ R ∈ (mobiusDivisorSelectionPrimes M).powerset,a*t R := sum_le_sum hpoint
    _ = _ := by
      rw [← mul_sum]
      exact (mobiusDivisorCoareaHeadAction_eq_mass_mul_coarea M P).symm

/-- Maximality of the absolute head mass persists through every isolated late-prime merger. -/
theorem mobiusDivisorFibreAbsoluteMass_head_dominates_insert_late_prime
    {M p : ℕ} (hp : p.Prime) (hpM : p<M) (hM : M≤2*p)
    (P : Finset ℕ) (hpP : p ∉ P)
    (hdom : ∀ R ∈ (mobiusDivisorSelectionPrimes M).powerset,
      mobiusDivisorFibreAbsoluteMass M P R ≤ mobiusDivisorFibreAbsoluteMass M P ∅) :
    ∀ R ∈ (mobiusDivisorSelectionPrimes M).powerset,
      mobiusDivisorFibreAbsoluteMass M (insert p P) R ≤
        mobiusDivisorFibreAbsoluteMass M (insert p P) ∅ := by
  intro R hR
  by_cases hR0 : R=∅
  · subst R; exact le_rfl
  rw [mobiusDivisorFibreAbsoluteMass_insert_late_prime hp hpM hM P R hpP,
    mobiusDivisorFibreAbsoluteMass_insert_late_prime hp hpM hM P ∅ hpP]
  by_cases hRp : R={p}
  · simp only [hRp,if_true,if_false,singleton_ne_empty]
    exact add_nonneg (mobiusDivisorFibreAbsoluteMass_nonneg M P ∅) (abs_nonneg _)
  · simp only [if_neg hR0,if_neg hRp]
    exact (hdom R hR).trans (le_add_of_nonneg_right (abs_nonneg _))

/-- A late-prime block of positive total mass does not increase action exactly when its fixed slope
is nonpositive. -/
theorem mobiusDivisorCoareaHeadAction_late_block_le_iff (M : ℕ) (P L : Finset ℕ)
    (hL : ∀ p ∈ L,p.Prime ∧ p<M ∧ M≤2*p ∧ p ∉ P)
    (hpos : 0 < ∑ p ∈ L,|mobiusDivisorDilationChannel M p|) :
    mobiusDivisorCoareaHeadAction M (P ∪ L) ≤ mobiusDivisorCoareaHeadAction M P ↔
      mobiusDivisorCoareaHeadSlope M P ≤ 0 := by
  rw [← sub_nonpos,(mobiusDivisorCoareaHead_late_block M P L hL).2]
  constructor
  · intro h
    by_contra hg
    exact (not_lt_of_ge h) (mul_pos hpos (lt_of_not_ge hg))
  · intro h
    simpa only [mul_zero] using mul_le_mul_of_nonneg_left h hpos.le

end RHTower
