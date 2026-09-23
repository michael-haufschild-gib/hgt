import GaloisForLFunctions.RHTower.MobiusDivisorSuccessorAverageObstruction
import GaloisForLFunctions.RHTower.MobiusDivisorSmallCoreFirstGain

/-!
# Uniform source costs for signed successor envelopes

The prime-containing field merges at most one quotient cutoff's worth of
original coefficients. Its absolute mass bounds its full square energy,
independently of processed cardinality, retained signs, and overlap.
The actual parent-child identity transfers this budget to every alternative
next prime. Square-root envelope costs then add over arbitrary finite batches.

The same channel bound gives the original diagonal a quadratic ceiling.
An extension exceeding that diagonal despite a quadratic reserve must have
its prime below an explicit square-root threshold. This localizes failure;
it does not supply reserve or prove an exhaustive admissible order.
-/
noncomputable section
set_option autoImplicit false
open Finset
namespace RHTower

private lemma grouped_abs_le {ι κ : Type*} [DecidableEq ι]
    (T : Finset ι) (I : Finset κ) (a : κ → ι) (c : κ → ℝ) :
    (∑ R ∈ T, |∑ n ∈ I, if a n = R then c n else 0|) ≤ ∑ n ∈ I, |c n| := by
  calc
    _ ≤ ∑ R ∈ T, ∑ n ∈ I, |if a n = R then c n else 0| :=
      sum_le_sum (fun R _ => abs_sum_le_sum_abs _ _)
    _ = ∑ n ∈ I, ∑ R ∈ T, if a n = R then |c n| else 0 := by
      rw [sum_comm]
      apply sum_congr rfl
      intro n hn
      apply sum_congr rfl
      intro R hR
      split_ifs <;> simp
    _ ≤ ∑ n ∈ I, |c n| := by
      apply sum_le_sum
      intro n hn
      simp only [sum_ite_eq]
      split_ifs
      · exact le_rfl
      · exact abs_nonneg _

private lemma channel_abs_le (M n : ℕ) :
    |mobiusDivisorDilationChannel M n| ≤ (3/5:ℝ)*Real.sqrt M := by
  rw [mobiusDivisorDilationChannel_eq_moebius_unsigned,abs_mul,
    abs_of_nonneg (divisorUnsignedDilationChannel_nonneg M n)]
  have hm : |(ArithmeticFunction.moebius n : ℝ)| ≤ 1 := by
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := n)
  calc
    _ ≤ 1 * divisorUnsignedDilationChannel M n :=
      mul_le_mul_of_nonneg_right hm (divisorUnsignedDilationChannel_nonneg M n)
    _ ≤ _ := by simpa using divisorUnsignedDilationChannel_le_three_fifths_sqrt M n

/-- The complete prime-containing field has bounded absolute mass before or
after arbitrary mergers of other labels. Every original multiple is retained. -/
theorem sum_abs_mobiusDivisorPrimeFibre_le_quotient
    (M : ℕ) (P : Finset ℕ) {p : ℕ} (hp : p.Prime) :
    (∑ R ∈ ((mobiusDivisorSelectionPrimes M).erase p).powerset,
      |mobiusDivisorSelectionFibre M P (insert p R)|) ≤
        (3/5:ℝ)*Real.sqrt M*(M/p : ℕ) := by
  let T := ((mobiusDivisorSelectionPrimes M).erase p).powerset
  let I := (Icc 1 M).filter (fun n => p ∣ n)
  have hpR (R : Finset ℕ) (hR : R ∈ T) : p ∉ R :=
    fun h => (mem_erase.mp (mem_powerset.mp hR h)).1 rfl
  have hinj : Set.InjOn (fun R : Finset ℕ => insert p R) (↑T) := by
    intro R hR S hS he
    have h := congrArg (fun V : Finset ℕ => V.erase p) he
    simpa only [erase_insert (hpR R hR),erase_insert (hpR S hS)] using h
  have he (R : Finset ℕ) : mobiusDivisorSelectionFibre M P (insert p R) =
      ∑ n ∈ I, if n.primeFactors \ P = insert p R then mobiusDivisorDilationChannel M n else 0 := by
    rw [mobiusDivisorSelectionFibre_eq_sum_Icc]
    dsimp [I]
    rw [sum_filter]
    apply sum_congr rfl
    intro n hn
    by_cases hpn : p ∣ n
    · simp [hpn]
    · have hne : n.primeFactors \ P ≠ insert p R := by
        intro h
        have hmem : p ∈ n.primeFactors :=
          (mem_sdiff.mp (h.symm ▸ mem_insert_self p R)).1
        exact hpn (Nat.mem_primeFactors.mp hmem).2.1
      simp [hpn,hne]
  have hgroup := grouped_abs_le (T.image (fun R => insert p R)) I
    (fun n => n.primeFactors \ P) (mobiusDivisorDilationChannel M)
  rw [sum_image hinj] at hgroup
  simp_rw [← he] at hgroup
  refine hgroup.trans ?_
  dsimp [I]
  rw [sum_Icc_filter_dvd_reindex p M hp.pos]
  calc
    _ ≤ ∑ _n ∈ Icc 1 (M/p), (3/5:ℝ)*Real.sqrt M :=
      sum_le_sum (fun n _ => channel_abs_le M (p*n))
    _ = _ := by simp; ring

/-- Uniform quadratic quotient budget for the entire copied field, with
no processed-cardinality factor and no assumption on retained signs. -/
theorem sum_mobiusDivisorPrimeFibre_sq_le_quotient
    (M : ℕ) (P : Finset ℕ) {p : ℕ} (hp : p.Prime) :
    (∑ R ∈ ((mobiusDivisorSelectionPrimes M).erase p).powerset,
      (mobiusDivisorSelectionFibre M P (insert p R))^(2 : ℕ)) ≤
        (9/25:ℝ)*(M:ℝ)*(M/p : ℕ)^(2 : ℕ) := by
  have hs := sum_sq_le_sq_sum_of_nonneg (s := ((mobiusDivisorSelectionPrimes M).erase p).powerset)
    (f := fun R => |mobiusDivisorSelectionFibre M P (insert p R)|) (fun R _ => abs_nonneg _)
  simp only [sq_abs] at hs
  have hb := sum_abs_mobiusDivisorPrimeFibre_le_quotient M P hp
  have hh := mul_le_mul hb hb (sum_nonneg (fun _ _ => abs_nonneg _)) (by positivity)
  rw [← pow_two,← pow_two] at hh
  have he : ((3/5:ℝ)*Real.sqrt M*(M/p : ℕ))^(2 : ℕ)=(9/25:ℝ)*(M:ℝ)*(M/p : ℕ)^(2 : ℕ) := by
    rw [mul_pow,mul_pow,Real.sq_sqrt (Nat.cast_nonneg M)]
    ring
  rw [he] at hh
  exact hs.trans hh
private lemma energy_nonneg (M : ℕ) (P : Finset ℕ) :
    0 ≤ mobiusDivisorSelectionEnergy M P := by
  change 0 ≤ ∑ R ∈ (mobiusDivisorSelectionPrimes M).powerset,
    (mobiusDivisorSelectionFibre M P R)^(2 : ℕ)
  exact sum_nonneg (fun _ _ => sq_nonneg _)

/-- Squared signed gain has a polynomial quotient bound at every processed
state; no sign, energy ceiling, or core-size bound is a premise. -/
theorem sq_mobiusDivisorSelectionEnergy_insert_le_quotient
    (M : ℕ) (P : Finset ℕ) {p : ℕ}
    (hp : p.Prime) (hpM : p < M) (hpP : p ∉ P) :
    (mobiusDivisorSelectionEnergy M (insert p P)-mobiusDivisorSelectionEnergy M P)^(2 : ℕ) ≤
      (36/25:ℝ)*(M:ℝ)*(M/p : ℕ)^(2 : ℕ)*mobiusDivisorSelectionEnergy M P := by
  let T := ((mobiusDivisorSelectionPrimes M).erase p).powerset
  let f := mobiusDivisorSelectionFibre M P
  let g := fun R => mobiusDivisorSelectionFibre M P (insert p R)
  have hcs := sum_mul_sq_le_sq_mul_sq T f g
  have hf := sum_mobiusDivisorSelectionFibre_sq_le_energy M P T
  have hg := sum_mobiusDivisorPrimeFibre_sq_le_quotient M P hp
  have hb := mul_le_mul hf hg (sum_nonneg (fun _ _ => sq_nonneg _)) (energy_nonneg M P)
  rw [mobiusDivisorSelectionEnergy_insert_cross hp M P hpM hpP,mul_pow]
  change (2:ℝ)^(2 : ℕ)*(∑ R∈T,f R*g R)^(2 : ℕ) ≤ _
  calc
    _ ≤ 4*((∑ R∈T,(f R)^(2 : ℕ))*(∑ R∈T,(g R)^(2 : ℕ))) := by nlinarith only [hcs]
    _ ≤ 4*(mobiusDivisorSelectionEnergy M P*((9/25:ℝ)*(M:ℝ)*(M/p : ℕ)^(2 : ℕ))) :=
      mul_le_mul_of_nonneg_left hb (by norm_num)
    _ = _ := by ring

/-- Uniform absolute cost of one actual prime merger at any signed state. -/
theorem abs_mobiusDivisorSelectionEnergy_insert_le_quotient
    (M : ℕ) (P : Finset ℕ) {p : ℕ}
    (hp : p.Prime) (hpM : p < M) (hpP : p ∉ P) :
    |mobiusDivisorSelectionEnergy M (insert p P)-mobiusDivisorSelectionEnergy M P| ≤
      (6/5:ℝ)*(M/p : ℕ)*Real.sqrt ((M:ℝ)*mobiusDivisorSelectionEnergy M P) := by
  have hb := sq_mobiusDivisorSelectionEnergy_insert_le_quotient M P hp hpM hpP
  have hr := Real.sq_sqrt (mul_nonneg (Nat.cast_nonneg M) (energy_nonneg M P))
  have hn : 0 ≤ (6/5:ℝ)*(M/p : ℕ)*Real.sqrt ((M:ℝ)*mobiusDivisorSelectionEnergy M P) := by positivity
  have he : ((6/5:ℝ)*(M/p : ℕ)*Real.sqrt ((M:ℝ)*mobiusDivisorSelectionEnergy M P))^(2 : ℕ) =
      (36/25:ℝ)*(M:ℝ)*(M/p : ℕ)^(2 : ℕ)*mobiusDivisorSelectionEnergy M P := by
    rw [mul_pow,hr]
    ring
  nlinarith only [hb,he,sq_abs (mobiusDivisorSelectionEnergy M (insert p P)-mobiusDivisorSelectionEnergy M P),abs_nonneg (mobiusDivisorSelectionEnergy M (insert p P)-mobiusDivisorSelectionEnergy M P),hn]

/-- The entire successor envelope has a uniform source-supplied transport
bound, simultaneously over every alternative next prime and all overlaps. -/
theorem mobiusDivisorSuccessorEnvelope_insert_le_quotient
    (M : ℕ) (P : Finset ℕ) {p : ℕ}
    (hp : p.Prime) (hpM : p < M) (hpP : p ∉ P) :
    mobiusDivisorSuccessorEnvelope M (insert p P) ≤ mobiusDivisorSuccessorEnvelope M P +
      (6/5:ℝ)*(M/p : ℕ)*Real.sqrt ((M:ℝ)*mobiusDivisorSuccessorEnvelope M P) := by
  have hbase := (mobiusDivisorSuccessorEnvelope_le_iff M P _).mp le_rfl
  have hPsi : 0 ≤ mobiusDivisorSuccessorEnvelope M P := (energy_nonneg M P).trans hbase.1
  have hcost : 0 ≤ (6/5:ℝ)*(M/p : ℕ)*Real.sqrt ((M:ℝ)*mobiusDivisorSuccessorEnvelope M P) := by positivity
  rw [mobiusDivisorSuccessorEnvelope_le_iff]
  constructor
  · have hpavail : p ∈ mobiusDivisorSelectionPrimes M \ P :=
      mem_sdiff.mpr ⟨mem_filter.mpr ⟨mem_range.mpr hpM,hp⟩,hpP⟩
    exact (hbase.2 p hpavail).trans (le_add_of_nonneg_right hcost)
  · intro q hq
    obtain ⟨hqprime,hqnot⟩ := mem_sdiff.mp hq
    have hqp : q ≠ p := by intro he; subst q; simp at hqnot
    have hqP : q ∉ P := fun h => hqnot (mem_insert_of_mem h)
    have hqbase := hbase.2 q (mem_sdiff.mpr ⟨hqprime,hqP⟩)
    have hg := (abs_le.mp (abs_mobiusDivisorSelectionEnergy_insert_le_quotient
      M (insert q P) hp hpM (by simp [Ne.symm hqp,hpP]))).2
    have hr := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hqbase (Nat.cast_nonneg M))
    have hb := mul_le_mul_of_nonneg_left hr (show 0 ≤ (6/5:ℝ)*(M/p : ℕ) by positivity)
    rw [Finset.insert_comm p q] at hg
    linarith only [hqbase,hg,hb]
private lemma envelope_nonneg (M : ℕ) (P : Finset ℕ) :
    0 ≤ mobiusDivisorSuccessorEnvelope M P :=
  (energy_nonneg M P).trans ((mobiusDivisorSuccessorEnvelope_le_iff M P _).mp le_rfl).1

/-- Square-root envelope growth has an additive source cost, including
already processed labels and all second-successor comparisons. -/
theorem sqrt_mobiusDivisorSuccessorEnvelope_insert_le_quotient
    (M : ℕ) (P : Finset ℕ) {p : ℕ} (hp : p.Prime) (hpM : p < M) :
    Real.sqrt (mobiusDivisorSuccessorEnvelope M (insert p P)) ≤
      Real.sqrt (mobiusDivisorSuccessorEnvelope M P)+(3/5:ℝ)*Real.sqrt M*(M/p : ℕ) := by
  by_cases hpP : p ∈ P
  · rw [insert_eq_of_mem hpP]
    exact le_add_of_nonneg_right (by positivity)
  have h := mobiusDivisorSuccessorEnvelope_insert_le_quotient M P hp hpM hpP
  rw [Real.sqrt_mul (Nat.cast_nonneg M)] at h
  have hs := Real.sq_sqrt (envelope_nonneg M P)
  rw [Real.sqrt_le_iff]
  constructor
  · positivity
  · nlinarith only [h,hs,sq_nonneg ((3/5:ℝ)*Real.sqrt M*(M/p : ℕ))]

/-- Every finite batch has an additive square-root envelope budget uniform
in its length, the processed state, all signs, and all overlapping labels. -/
theorem sqrt_mobiusDivisorSuccessorEnvelope_union_le_quotient_sum
    (M : ℕ) (P T : Finset ℕ) (hT : ∀ p ∈ T, p.Prime ∧ p < M) :
    Real.sqrt (mobiusDivisorSuccessorEnvelope M (P ∪ T)) ≤
      Real.sqrt (mobiusDivisorSuccessorEnvelope M P)+
        (3/5:ℝ)*Real.sqrt M*(∑ p ∈ T, (M/p : ℕ)) := by
  induction T using Finset.induction_on with
  | empty => simp
  | @insert p T hpT ih =>
    have hp := hT p (mem_insert_self _ _)
    have hsmall : ∀ q ∈ T, q.Prime ∧ q < M := fun q hq => hT q (mem_insert_of_mem hq)
    have hpre := ih hsmall
    have hstep := sqrt_mobiusDivisorSuccessorEnvelope_insert_le_quotient M (P ∪ T) hp.1 hp.2
    rw [union_insert, sum_insert hpT]
    push_cast
    calc
      _ ≤ Real.sqrt (mobiusDivisorSuccessorEnvelope M (P ∪ T))+
          (3/5:ℝ)*Real.sqrt M*(M/p : ℕ) := hstep
      _ ≤ (Real.sqrt (mobiusDivisorSuccessorEnvelope M P)+
          (3/5:ℝ)*Real.sqrt M*(∑ q ∈ T, (M/q : ℕ)))+
            (3/5:ℝ)*Real.sqrt M*(M/p : ℕ) := by linarith only [hpre]
      _ = _ := by push_cast; ring

/-- The prime times positive successor growth is uniformly source-bounded;
any failure to fit an existing reserve is confined by this inequality. -/
theorem mul_mobiusDivisorSuccessorEnvelope_insert_sub_le
    (M : ℕ) (P : Finset ℕ) {p : ℕ}
    (hp : p.Prime) (hpM : p < M) (hpP : p ∉ P) :
    (p:ℝ)*(mobiusDivisorSuccessorEnvelope M (insert p P)-mobiusDivisorSuccessorEnvelope M P) ≤
      (6/5:ℝ)*(M:ℝ)*Real.sqrt ((M:ℝ)*mobiusDivisorSuccessorEnvelope M P) := by
  have h := mobiusDivisorSuccessorEnvelope_insert_le_quotient M P hp hpM hpP
  have hmul := mul_le_mul_of_nonneg_left (sub_le_iff_le_add'.mpr h) (Nat.cast_nonneg (α:=ℝ) p)
  have hdiv : (p:ℝ)*(M/p : ℕ) ≤ M := by
    exact_mod_cast (show p*(M/p) ≤ M by simpa [Nat.mul_comm] using Nat.div_mul_le_self M p)
  have hcost := mul_le_mul_of_nonneg_right hdiv
    (show 0 ≤ (6/5:ℝ)*Real.sqrt ((M:ℝ)*mobiusDivisorSuccessorEnvelope M P) by positivity)
  nlinarith only [hmul,hcost]
/-- The uniform channel amplitude gives the complete original diagonal an
explicit quadratic ceiling, with all squarefree channels retained. -/
theorem mobiusDivisorSelectionEnergy_empty_le_nine_twentyFifths_sq (M : ℕ) :
    mobiusDivisorSelectionEnergy M ∅ ≤ (9/25:ℝ)*(M:ℝ)^(2 : ℕ) := by
  rw [mobiusDivisorSelectionEnergy_empty]
  have hs (n : ℕ) : (mobiusDivisorDilationChannel M n)^(2 : ℕ) ≤ (9/25:ℝ)*(M:ℝ) := by
    have h := channel_abs_le M n
    have hh := mul_le_mul h h (abs_nonneg _) (by positivity)
    have he : ((3/5:ℝ)*Real.sqrt M)^(2 : ℕ)=(9/25:ℝ)*(M:ℝ) := by
      rw [mul_pow,Real.sq_sqrt (Nat.cast_nonneg M)]
      ring
    simpa only [← pow_two,sq_abs,he] using hh
  calc
    _ ≤ ∑ _n ∈ Icc 1 M, (9/25:ℝ)*(M:ℝ) := sum_le_sum (fun n _ => hs n)
    _ = _ := by simp; ring

/-- A successor that exceeds the actual original diagonal despite a
quadratic reserve must lie below the explicit square-root prime scale. -/
theorem mobiusDivisorSuccessorEnvelope_failure_prime_bound
    (M : ℕ) (P : Finset ℕ) {p : ℕ} (hp : p.Prime) (hpM : p < M) (hpP : p ∉ P)
    (δ : ℝ) (hδ : 0 < δ)
    (hreserve : mobiusDivisorSuccessorEnvelope M P+δ*(M:ℝ)^(2 : ℕ) ≤ mobiusDivisorSelectionEnergy M ∅)
    (hfail : mobiusDivisorSelectionEnergy M ∅ < mobiusDivisorSuccessorEnvelope M (insert p P)) :
    δ*(p:ℝ) < (18/25:ℝ)*Real.sqrt M := by
  have hM : (0:ℝ) < M := by exact_mod_cast (hp.pos.trans hpM)
  have hPsi : mobiusDivisorSuccessorEnvelope M P ≤ (9/25:ℝ)*(M:ℝ)^(2 : ℕ) := by
    have hd := mobiusDivisorSelectionEnergy_empty_le_nine_twentyFifths_sq M
    nlinarith only [hreserve,hd,mul_nonneg hδ.le (sq_nonneg (M:ℝ))]
  have hroot : Real.sqrt ((M:ℝ)*mobiusDivisorSuccessorEnvelope M P) ≤
      (3/5:ℝ)*(M:ℝ)*Real.sqrt M := by
    rw [Real.sqrt_le_iff]
    refine ⟨by positivity,?_⟩
    have hm := mul_le_mul_of_nonneg_left hPsi hM.le
    have he : ((3/5:ℝ)*(M:ℝ)*Real.sqrt M)^(2 : ℕ)=(9/25:ℝ)*(M:ℝ)^(3 : ℕ) := by
      rw [mul_pow,Real.sq_sqrt hM.le]
      ring
    rw [he]
    nlinarith only [hm]
  have hcost := mul_mobiusDivisorSuccessorEnvelope_insert_sub_le M P hp hpM hpP
  have hrootcost := mul_le_mul_of_nonneg_left hroot (show 0 ≤ (6/5:ℝ)*(M:ℝ) by positivity)
  have hgap : δ*(M:ℝ)^(2 : ℕ) < mobiusDivisorSuccessorEnvelope M (insert p P)-mobiusDivisorSuccessorEnvelope M P := by
    linarith only [hreserve,hfail]
  have hpR : (0:ℝ) < p := by exact_mod_cast hp.pos
  have hgapmul := mul_lt_mul_of_pos_left hgap hpR
  have hfinal : (δ*(p:ℝ))*(M:ℝ)^(2 : ℕ) < ((18/25:ℝ)*Real.sqrt M)*(M:ℝ)^(2 : ℕ) := by
    nlinarith only [hgapmul,hcost,hrootcost]
  exact (mul_lt_mul_iff_left₀ (sq_pos_of_pos hM)).mp hfinal
end RHTower
