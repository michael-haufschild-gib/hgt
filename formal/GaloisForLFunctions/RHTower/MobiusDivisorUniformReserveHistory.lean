import GaloisForLFunctions.RHTower.MobiusDivisorEvenCorePrimeReserve

/-!
# An actual changing-core reserve history with one all-cutoff budget

Fresh actual prime pairs can be selected indefinitely. Every even and odd
prefix stays below the original diagonal plus `M^2` at every integer cutoff.
After the initial pair each pair produces a positive quadratic reserve at
all sufficiently large cutoffs for that pair. The budget itself has no
cutoff threshold. This constructs a sparse history, not an exhaustive order
of all primes; inclusion of arbitrary omitted primes remains open.
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

private lemma history_prime_cost (P : Finset ℕ) (hP : ∀ q ∈ P,q.Prime)
    {p : ℕ} (hp : p.Prime) (hpP : p ∉ P) (M : ℕ) :
    mobiusDivisorSelectionEnergy M (insert p P) ≤ mobiusDivisorSelectionEnergy M P+
      (2*((3/5:ℝ)*2^(P.card-1))^2/(p:ℝ))*(M:ℝ)^2 := by
  let S := fixedCoreSquarefreeIndices (insert p P) M
  have he : mobiusDivisorSelectionEnergy M P-mobiusDivisorSelectionEnergy M (insert p P)=
      ∑ r ∈ S,mobiusDivisorPrimeCorrelationTerm P p M r := by
    rw [mobiusDivisorSelectionEnergy_prime_release_eq_correlation P hp hpP M]
    simp only [S,mobiusDivisorPrimeCorrelationTerm,mul_sum,mul_assoc]
  have hfilter : (∑ r ∈ S,|mobiusDivisorPrimeCorrelationTerm P p M r|)=
      ∑ r ∈ S.filter (fun r => p ≤ M/r),|mobiusDivisorPrimeCorrelationTerm P p M r| := by
    symm
    apply sum_subset (filter_subset _ _)
    intro r hr hnot
    have hr0 : 0 < r := (mem_Icc.mp (mem_filter.mp hr).1).1
    have hlt : M < p*r := by
      have hh : ¬p ≤ M/r := fun h => hnot (mem_filter.mpr ⟨hr,h⟩)
      have hh' : ¬p*r ≤ M := fun h => hh ((Nat.le_div_iff_mul_le hr0).mpr h)
      omega
    rw [mobiusDivisorPrimeCorrelationTerm,
      sample_vanish P (Nat.mul_pos hp.pos hr0) hlt.le,mul_zero,abs_zero]
  have hb := mobiusDivisorPrimeCorrelation_absolute_tail_le P hP hp hpP M hp.pos
  have ha : |mobiusDivisorSelectionEnergy M P-mobiusDivisorSelectionEnergy M (insert p P)| ≤
      (2*((3/5:ℝ)*2^(P.card-1))^2/(p:ℝ))*(M:ℝ)^2 := by
    rw [he]
    exact (abs_sum_le_sum_abs _ _).trans (by rw [hfilter]; exact hb)
  have hn := neg_le_abs (mobiusDivisorSelectionEnergy M P-mobiusDivisorSelectionEnergy M (insert p P))
  linarith only [ha,hn]

private lemma history_pair (P : Finset ℕ) (hP : ∀ r ∈ P,r.Prime)
    (hEven : Even P.card) (δ : ℝ) (hδ : 0 < δ) :
    ∃ p q : ℕ, P.sup id < p ∧ p < q ∧ p.Prime ∧ q.Prime ∧
      p ∉ P ∧ q ∉ insert p P ∧ Even (insert q (insert p P)).card ∧
      (∀ M,mobiusDivisorSelectionEnergy M (insert p P) ≤
        mobiusDivisorSelectionEnergy M P+(δ/2)*(M:ℝ)^2) ∧
      (∀ M,mobiusDivisorSelectionEnergy M (insert q (insert p P)) ≤
        mobiusDivisorSelectionEnergy M P+δ*(M:ℝ)^2) ∧
      (P.Nonempty → ∃ c : ℝ,0 < c ∧ ∀ᶠ M : ℕ in atTop,
        c*(M:ℝ)^2 ≤ mobiusDivisorSelectionEnergy M P-
          mobiusDivisorSelectionEnergy M (insert q (insert p P))) := by
  let K : ℝ := 2*((3/5:ℝ)*2^P.card)^2
  obtain ⟨N,hN⟩ := exists_nat_gt (2*K/δ)
  let T := max N (P.sup id+1)
  have pairs : ∃ p q : ℕ,T ≤ p ∧ p < q ∧ p.Prime ∧ q.Prime ∧ p ∉ P ∧ q ∉ P ∧
      Even (insert q (insert p P)).card ∧
      (P.Nonempty → ∃ c : ℝ,0 < c ∧ ∀ᶠ M : ℕ in atTop,
        c*(M:ℝ)^2 ≤ mobiusDivisorSelectionEnergy M P-
          mobiusDivisorSelectionEnergy M (insert q (insert p P))) := by
    by_cases hn : P.Nonempty
    · obtain ⟨c,hc,hpairs⟩ := exists_arbitrarily_large_mobiusDivisorEvenCore_pair_energy_reserve P hn hP hEven
      obtain ⟨p,q,hTp,hpq,hp,hq,hpP,hqP,heven,hr⟩ := hpairs T
      exact ⟨p,q,hTp,hpq,hp,hq,hpP,hqP,heven,fun _ =>
        ⟨c/(p:ℝ),div_pos hc (by exact_mod_cast hp.pos),hr⟩⟩
    · have hzero : P=∅ := not_nonempty_iff_eq_empty.mp hn
      obtain ⟨p,hTp,hp⟩ := Nat.exists_infinite_primes T
      obtain ⟨q,hpq,hq⟩ := Nat.exists_infinite_primes (p+1)
      have hneq : q ≠ p := by omega
      refine ⟨p,q,hTp,by omega,hp,hq,by simp [hzero],by simp [hzero],?_,?_⟩
      · simp [hzero,hneq]
      · intro hh
        exact False.elim (hn hh)
  obtain ⟨p,q,hTp,hpq,hp,hq,hpP,hqP,heven,hreserve⟩ := pairs
  have hbound : 2*K/δ < (p:ℝ) := hN.trans_le (by exact_mod_cast ((le_max_left N _).trans hTp))
  have hqbound : 2*K/δ < (q:ℝ) := hbound.trans (by exact_mod_cast hpq)
  have hKp : K/(p:ℝ) ≤ δ/2 := by
    have hh := (div_lt_iff₀ hδ).mp hbound
    apply (div_le_iff₀ (by exact_mod_cast hp.pos : (0:ℝ)<p)).mpr
    linarith only [hh]
  have hKq : K/(q:ℝ) ≤ δ/2 := by
    have hh := (div_lt_iff₀ hδ).mp hqbound
    apply (div_le_iff₀ (by exact_mod_cast hq.pos : (0:ℝ)<q)).mpr
    linarith only [hh]
  have hcoeff : 2*((3/5:ℝ)*2^(P.card-1))^2 ≤ K := by
    dsimp [K]
    gcongr
    · norm_num
    · omega
  have hqi : q ∉ insert p P := by simp [hpq.ne',hqP]
  have hPi : ∀ r ∈ insert p P,r.Prime := by simpa using And.intro hp hP
  have hfirst (M : ℕ) : mobiusDivisorSelectionEnergy M (insert p P) ≤
      mobiusDivisorSelectionEnergy M P+(δ/2)*(M:ℝ)^2 := by
    apply (history_prime_cost P hP hp hpP M).trans
    have hc := (div_le_div_of_nonneg_right hcoeff (Nat.cast_nonneg p)).trans hKp
    have hm := mul_le_mul_of_nonneg_right hc (sq_nonneg (M:ℝ))
    linarith only [hm]
  have hsecond (M : ℕ) : mobiusDivisorSelectionEnergy M (insert q (insert p P)) ≤
      mobiusDivisorSelectionEnergy M (insert p P)+(δ/2)*(M:ℝ)^2 := by
    have hh := history_prime_cost (insert p P) hPi hq hqi M
    rw [card_insert_of_notMem hpP,Nat.add_sub_cancel] at hh
    change mobiusDivisorSelectionEnergy M (insert q (insert p P)) ≤
      mobiusDivisorSelectionEnergy M (insert p P)+K/(q:ℝ)*(M:ℝ)^2 at hh
    have hm := mul_le_mul_of_nonneg_right hKq (sq_nonneg (M:ℝ))
    linarith only [hh,hm]
  refine ⟨p,q,?_,hpq,hp,hq,hpP,hqi,heven,hfirst,?_,hreserve⟩
  · have hh := (le_max_right N (P.sup id+1)).trans hTp
    omega
  · intro M
    have ha := hfirst M
    have hb := hsecond M
    linarith only [ha,hb]

/-- An infinite actual prime history renews a positive pair reserve through
changing cores while every intermediate state obeys one all-cutoff budget.
The selected primes need not exhaust all primes. -/
theorem exists_mobiusDivisorUniformReserveHistory :
    ∃ P : ℕ → Finset ℕ, ∃ p q : ℕ → ℕ,
      P 0=∅ ∧ (∀ n,P (n+1)=insert (q n) (insert (p n) (P n))) ∧
      (∀ n,(p n).Prime ∧ (q n).Prime ∧ p n < q n ∧ q n < p (n+1)) ∧
      (∀ n,(P n).card=2*n) ∧
      (∀ n M,mobiusDivisorSelectionEnergy M (P n) ≤ mobiusDivisorSelectionEnergy M ∅+(M:ℝ)^2) ∧
      (∀ n M,mobiusDivisorSelectionEnergy M (insert (p n) (P n)) ≤
        mobiusDivisorSelectionEnergy M ∅+(M:ℝ)^2) ∧
      ∀ n,∃ c : ℝ,0 < c ∧ ∀ᶠ M : ℕ in atTop,
        c*(M:ℝ)^2 ≤ mobiusDivisorSelectionEnergy M (P (n+1))-
          mobiusDivisorSelectionEnergy M (P (n+2)) := by
  let Core := {P : Finset ℕ // (∀ p ∈ P,p.Prime) ∧ Even P.card}
  let w := fun n : ℕ => (1:ℝ)/(n+1:ℕ)
  have hw (n : ℕ) : 0 < w n := by dsimp [w]; positivity
  have hdiff (n : ℕ) : 0 < w n-w (n+1) := by
    apply sub_pos.mpr
    exact one_div_lt_one_div_of_lt (by positivity) (by exact_mod_cast (Nat.lt_succ_self (n+1)))
  have choosePair (S : Core) (n : ℕ) := history_pair S.val S.property.1 S.property.2
    (w n-w (n+1)) (hdiff n)
  choose a b hab hab' ha hb haf hbf heven hfirst hboth hreserve using choosePair
  let advance (n : ℕ) (S : Core) : Core :=
    ⟨insert (b S n) (insert (a S n) S.val),by
      constructor
      · intro r hr
        rcases mem_insert.mp hr with rfl|hr
        · exact hb S n
        rcases mem_insert.mp hr with rfl|hr
        · exact ha S n
        · exact S.property.1 r hr
      · exact heven S n⟩
  let state : ℕ → Core := Nat.rec ⟨∅,by simp⟩ advance
  let P := fun n => (state n).val
  let p := fun n => a (state n) n
  let q := fun n => b (state n) n
  have hzero : P 0=∅ := rfl
  have hstep (n : ℕ) : P (n+1)=insert (q n) (insert (p n) (P n)) := rfl
  have hcard : ∀ n,(P n).card=2*n := by
    intro n
    induction n with
    | zero => simp [hzero]
    | succ n ih =>
      rw [hstep,card_insert_of_notMem (hbf (state n) n),card_insert_of_notMem (haf (state n) n),ih]
      omega
  have hbudget : ∀ n M,mobiusDivisorSelectionEnergy M (P n) ≤
      mobiusDivisorSelectionEnergy M ∅+(1-w n)*(M:ℝ)^2 := by
    intro n
    induction n with
    | zero => intro M; simp [hzero,w]
    | succ n ih =>
      intro M
      have hh := hboth (state n) n M
      change mobiusDivisorSelectionEnergy M (P (n+1)) ≤
        mobiusDivisorSelectionEnergy M (P n)+(w n-w (n+1))*(M:ℝ)^2 at hh
      have hi := ih M
      linarith only [hh,hi]
  refine ⟨P,p,q,hzero,hstep,?_,hcard,?_,?_,?_⟩
  · intro n
    refine ⟨ha (state n) n,hb (state n) n,hab' (state n) n,?_⟩
    have hm : q n ∈ P (n+1) := by rw [hstep]; exact mem_insert_self _ _
    exact (Finset.le_sup (f := id) hm).trans_lt (hab (state (n+1)) (n+1))
  · intro n M
    have hh := hbudget n M
    have hn := mul_nonneg (hw n).le (sq_nonneg (M:ℝ))
    linarith only [hh,hn]
  · intro n M
    have hh := hfirst (state n) n M
    change mobiusDivisorSelectionEnergy M (insert (p n) (P n)) ≤
      mobiusDivisorSelectionEnergy M (P n)+((w n-w (n+1))/2)*(M:ℝ)^2 at hh
    have hi := hbudget n M
    have hn := mul_nonneg (hw n).le (sq_nonneg (M:ℝ))
    have hn' := mul_nonneg (hw (n+1)).le (sq_nonneg (M:ℝ))
    linarith only [hh,hi,hn,hn']
  · intro n
    exact hreserve (state (n+1)) (n+1) ⟨q n,by change q n ∈ P (n+1); rw [hstep]; exact mem_insert_self _ _⟩

end RHTower
