import GaloisForLFunctions.RenormalizedIntersectionTheory.GaussMayerIntegralWordConjugacy
import GaloisForLFunctions.RenormalizedIntersectionTheory.GaussMayerCountableWordTraces

/-!
# Primitive modular coding of the actual Gauss words

The actual reversed Gauss digit products are positive alternating unipotent
runs. Consecutive digit pairs have unique run boundaries. Integral conjugacy
is exactly cyclic splitting of those pairs, and integral roots are exactly
whole-pair repetitions. Every positive-trace integral hyperbolic class has
an actual nonempty even Gauss representative. One-digit Gauss squares are
primitive in the determinant-one group, retaining the odd-period exception.
-/

open Matrix
open GaloisForLFunctions.RenormalizedIntersectionTheory.MayerCoding
open GaloisForLFunctions.RenormalizedIntersectionTheory.MayerHyperbolic
open GaloisForLFunctions.RenormalizedIntersectionTheory.MayerWords
open GaloisForLFunctions.RenormalizedIntersectionTheory.MayerIntegralWords
set_option autoImplicit false
noncomputable section
namespace GaloisForLFunctions.RenormalizedIntersectionTheory.MayerGaussCoding

/-- Positive alternating runs in the two oriented modular generators. -/
def pairedRunWord : List (ℕ × ℕ) → List Bool
  | [] => []
  | (a,b)::ps => List.replicate (a+1) false++List.replicate (b+1) true++pairedRunWord ps

@[simp] theorem pairedRunWord_append (ps qs : List (ℕ × ℕ)) :
    pairedRunWord (ps++qs) = pairedRunWord ps++pairedRunWord qs := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp only [List.cons_append,pairedRunWord,ih,List.append_assoc]

/-- The actual Gauss digits, in the reversed operator-product convention. -/
def pairedDigits : List (ℕ × ℕ) → List ℕ
  | [] => []
  | (a,b)::ps => pairedDigits ps++[b,a]

/-- A list of digits as an actual finite Gauss word. -/
def asWord : (ds : List ℕ) → Word ds.length
  | [] => Fin.elim0
  | d::ds => Fin.cons d (asWord ds)

/-- The reversed product of the actual Gauss digit matrices. -/
def gaussListMatrix : List ℕ → NatMatrix
  | [] => 1
  | d::ds => gaussListMatrix ds*digitMatrix d

theorem wordMatrix_asWord (ds : List ℕ) :
    wordMatrix ds.length (asWord ds) = gaussListMatrix ds := by
  induction ds with
  | nil => rfl
  | cons d ds ih => simp only [List.length_cons,asWord,wordMatrix,Fin.tail_cons,Fin.cons_zero,ih,gaussListMatrix]

theorem gaussListMatrix_append (ds es : List ℕ) :
    gaussListMatrix (ds++es) = gaussListMatrix es*gaussListMatrix ds := by
  induction ds with
  | nil => simp only [List.nil_append,gaussListMatrix,Matrix.mul_one]
  | cons d ds ih => simp only [List.cons_append,gaussListMatrix,ih,Matrix.mul_assoc]

theorem generator_true_pow (n : ℕ) : generator true^n = !![1,n;0,1] := by
  induction n with
  | zero => ext i j; fin_cases i <;> fin_cases j <;> norm_num [pow_zero]
  | succ n ih =>
    rw [pow_succ,ih]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [generator,Matrix.mul_apply,Fin.sum_univ_two]
    omega

theorem generator_false_pow (n : ℕ) : generator false^n = !![1,0;n,1] := by
  induction n with
  | zero => ext i j; fin_cases i <;> fin_cases j <;> norm_num [pow_zero]
  | succ n ih =>
    rw [pow_succ,ih]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [generator,Matrix.mul_apply,Fin.sum_univ_two]

theorem matrixWord_replicate (b : Bool) (n : ℕ) :
    matrixWord (List.replicate n b) = generator b^n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [List.replicate_succ,matrixWord,ih,pow_succ']

/-- Two actual Gauss digits are exactly one positive lower/upper unipotent run pair. -/
theorem digitMatrix_pair (a b : ℕ) :
    digitMatrix a*digitMatrix b = generator false^(a+1)*generator true^(b+1) := by
  rw [generator_false_pow,generator_true_pow]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [digitMatrix,Matrix.mul_apply,Fin.sum_univ_two]
  omega

/-- Paired Gauss digits preserve the actual source matrix, including its reversed word order. -/
theorem pairedDigits_matrix (ps : List (ℕ × ℕ)) :
    wordMatrix (pairedDigits ps).length (asWord (pairedDigits ps)) = matrixWord (pairedRunWord ps) := by
  rw [wordMatrix_asWord]
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    rcases p with ⟨a,b⟩
    rw [pairedDigits,gaussListMatrix_append]
    simp only [gaussListMatrix,Matrix.one_mul]
    rw [digitMatrix_pair,ih,pairedRunWord,matrixWord_append,matrixWord_append,
      matrixWord_replicate,matrixWord_replicate]

/-- Every run pair contributes exactly two actual Gauss digits. -/
theorem pairedDigits_length (ps : List (ℕ × ℕ)) : (pairedDigits ps).length = 2*ps.length := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    simp only [pairedDigits,List.length_append,List.length_cons,List.length_nil,ih]
    omega

#print axioms pairedDigits_matrix
#print axioms pairedDigits_length


/-- Every Boolean word has an initial upper run, positive lower/upper run pairs,
and a final lower run. -/
theorem exists_run_decomposition (w : List Bool) :
    ∃ a : ℕ, ∃ ps : List (ℕ × ℕ), ∃ b : ℕ,
      w = List.replicate a true++pairedRunWord ps++List.replicate b false := by
  induction w with
  | nil => exact ⟨0,[],0,rfl⟩
  | cons x w ih =>
    obtain ⟨a,ps,b,rfl⟩ := ih
    cases x with
    | true =>
      refine ⟨a+1,ps,b,?_⟩
      simp only [List.replicate_succ,List.cons_append]
    | false =>
      cases a with
      | succ a =>
        refine ⟨0,(0,a)::ps,b,?_⟩
        simp [pairedRunWord,List.replicate_succ,List.append_assoc]
      | zero =>
        cases ps with
        | nil =>
          refine ⟨0,[],b+1,?_⟩
          simp [pairedRunWord,List.replicate_succ]
        | cons p ps =>
          rcases p with ⟨r,s⟩
          refine ⟨0,(r+1,s)::ps,b,?_⟩
          simp [pairedRunWord,List.replicate_succ,List.append_assoc]

/-- Words beginning in the lower generator and ending in the upper generator
are exactly positive alternating run pairs. -/
theorem aligned_word_has_paired_runs (v : List Bool) :
    ∃ ps : List (ℕ × ℕ), false::(v++[true]) = pairedRunWord ps := by
  obtain ⟨a,ps,b,he⟩ := exists_run_decomposition (false::(v++[true]))
  have ha : a = 0 := by
    cases a with
    | zero => rfl
    | succ a => simp [List.replicate_succ] at he
  have hb : b = 0 := by
    cases b with
    | zero => rfl
    | succ b =>
      have hr := congrArg List.reverse he
      simp [List.reverse_append,List.reverse_cons,List.reverse_replicate,List.replicate_succ] at hr
      cases b <;> simp [List.replicate_succ] at hr
  refine ⟨ps,?_⟩
  simpa only [ha,hb,List.replicate_zero,List.nil_append,List.append_nil] using he

#print axioms exists_run_decomposition
#print axioms aligned_word_has_paired_runs


private theorem pairedRunWord_head (ps : List (ℕ × ℕ)) :
    pairedRunWord ps = [] ∨ ∃ v : List Bool, pairedRunWord ps = false::v := by
  cases ps with
  | nil => exact Or.inl rfl
  | cons p ps =>
    rcases p with ⟨a,b⟩
    right
    refine ⟨List.replicate a false++List.replicate (b+1) true++pairedRunWord ps,?_⟩
    simp only [pairedRunWord,List.replicate_succ,List.cons_append]

private theorem opposite_head_ne (b : Bool) (u v : List Bool)
    (hu : u = [] ∨ ∃ t, u = (!b)::t) : u ≠ b::v := by
  rcases hu with rfl | ⟨t,rfl⟩
  · simp
  · cases b <;> simp

private theorem replicate_prefix_unique (b : Bool) (a c : ℕ) (u v : List Bool)
    (hu : u = [] ∨ ∃ t, u = (!b)::t) (hv : v = [] ∨ ∃ t, v = (!b)::t)
    (he : List.replicate (a+1) b++u = List.replicate (c+1) b++v) : a = c ∧ u = v := by
  induction a generalizing c with
  | zero =>
    have ht : u = List.replicate c b++v := by
      simpa only [List.replicate_succ,List.replicate_zero,List.nil_append,List.cons_append,
        List.cons.injEq,true_and] using he
    cases c with
    | zero => exact ⟨rfl,by simpa using ht⟩
    | succ c =>
      have hh : u = b::(List.replicate c b++v) := by
        simpa only [List.replicate_succ,List.cons_append] using ht
      exact (opposite_head_ne b u _ hu hh).elim
  | succ a ih =>
    have ht : List.replicate (a+1) b++u = List.replicate c b++v := by
      simpa only [List.replicate_succ,List.cons_append,List.cons.injEq,true_and] using he
    cases c with
    | zero =>
      have hh : v = b::(List.replicate a b++u) := by
        simpa only [List.replicate_zero,List.nil_append,List.replicate_succ,List.cons_append] using ht.symm
      exact (opposite_head_ne b v _ hv hh).elim
    | succ c =>
      obtain ⟨hac,huv⟩ := ih c ht
      exact ⟨congrArg Nat.succ hac,huv⟩

/-- Positive alternating run pairs have unique lengths and boundaries. -/
theorem pairedRunWord_injective : Function.Injective pairedRunWord := by
  intro ps
  induction ps with
  | nil =>
    intro qs he
    cases qs with
    | nil => rfl
    | cons q qs =>
      rcases q with ⟨c,d⟩
      simp [pairedRunWord,List.replicate_succ] at he
  | cons p ps ih =>
    intro qs he
    cases qs with
    | nil =>
      rcases p with ⟨a,b⟩
      simp [pairedRunWord,List.replicate_succ] at he
    | cons q qs =>
      rcases p with ⟨a,b⟩
      rcases q with ⟨c,d⟩
      have hu : List.replicate (b+1) true++pairedRunWord ps = [] ∨
          ∃ t : List Bool, List.replicate (b+1) true++pairedRunWord ps = (!false)::t := by
        exact Or.inr ⟨List.replicate b true++pairedRunWord ps,by simp only [List.replicate_succ,List.cons_append]; rfl⟩
      have hv : List.replicate (d+1) true++pairedRunWord qs = [] ∨
          ∃ t : List Bool, List.replicate (d+1) true++pairedRunWord qs = (!false)::t := by
        exact Or.inr ⟨List.replicate d true++pairedRunWord qs,by simp only [List.replicate_succ,List.cons_append]; rfl⟩
      have hfirst := replicate_prefix_unique false a c _ _ hu hv
        (by simpa only [pairedRunWord,List.append_assoc] using he)
      have hsecond := replicate_prefix_unique true b d _ _
        (by simpa using pairedRunWord_head ps) (by simpa using pairedRunWord_head qs) hfirst.2
      have htail := ih hsecond.2
      have hac := hfirst.1
      have hbd := hsecond.1
      subst c
      subst d
      subst qs
      rfl

#print axioms pairedRunWord_injective


private theorem replicate_succ_end (b : Bool) (n : ℕ) :
    List.replicate (n+1) b = List.replicate n b++[b] := by
  induction n with
  | zero => rfl
  | succ n ih =>
    calc
      _ = b::List.replicate (n+1) b := by rw [List.replicate_succ]
      _ = b::(List.replicate n b++[b]) := by rw [ih]
      _ = _ := by rw [List.replicate_succ,List.cons_append]

private theorem pairedRunWord_cons_shape (p : ℕ × ℕ) (ps : List (ℕ × ℕ)) :
    ∃ v : List Bool, pairedRunWord (p::ps) = false::(v++[true]) := by
  induction ps generalizing p with
  | nil =>
    rcases p with ⟨a,b⟩
    refine ⟨List.replicate a false++List.replicate b true,?_⟩
    rw [pairedRunWord,pairedRunWord,List.append_nil,replicate_succ_end true b]
    simp only [List.replicate_succ,List.cons_append,List.append_assoc]
  | cons q ps ih =>
    rcases p with ⟨a,b⟩
    obtain ⟨v,hv⟩ := ih q
    refine ⟨List.replicate a false++List.replicate (b+1) true++false::v,?_⟩
    rw [pairedRunWord,hv]
    simp only [List.replicate_succ,List.cons_append,List.append_assoc]

/-- Every strictly positive modular word has a cyclic split aligned with positive Gauss run pairs. -/
theorem positive_word_cyclic_paired_runs (u : List Bool)
    (hu : ∀ i j, 0 < matrixWord u i j) :
    ∃ p q : List Bool, ∃ ps : List (ℕ × ℕ),
      u = p++q ∧ pairedRunWord ps = q++p ∧ ps ≠ [] := by
  obtain ⟨a,ps,b,he⟩ := exists_run_decomposition u
  have halign (v : List Bool) : ∃ qs : List (ℕ × ℕ),
      false::(v++[true]) = pairedRunWord qs ∧ qs ≠ [] := by
    obtain ⟨qs,hq⟩ := aligned_word_has_paired_runs v
    refine ⟨qs,hq,?_⟩
    intro hn
    simp only [hn,pairedRunWord] at hq
    cases hq
  cases b with
  | zero =>
    simp only [List.replicate_zero,List.append_nil] at he
    cases ps with
    | nil =>
      simp only [pairedRunWord,List.append_nil] at he
      have hp := hu 1 0
      rw [he,matrixWord_replicate,generator_true_pow] at hp
      norm_num at hp
    | cons t ps =>
      obtain ⟨v,hv⟩ := pairedRunWord_cons_shape t ps
      obtain ⟨qs,hq,hne⟩ := halign (v++List.replicate a true)
      refine ⟨List.replicate a true,pairedRunWord (t::ps),qs,he,?_,hne⟩
      rw [← hq,hv]
      have hmove : true::List.replicate a true = List.replicate a true++[true] := by
        rw [← replicate_succ_end true a]
        simp only [List.replicate_succ]
      simp only [List.cons_append,List.append_assoc,List.nil_append]
      rw [hmove]
  | succ b =>
    cases ps with
    | nil =>
      simp only [pairedRunWord,List.append_nil] at he
      cases a with
      | zero =>
        simp only [List.replicate_zero,List.nil_append] at he
        have hp := hu 0 1
        rw [he,matrixWord_replicate,generator_false_pow] at hp
        norm_num at hp
      | succ a =>
        obtain ⟨qs,hq,hne⟩ := halign (List.replicate b false++List.replicate a true)
        refine ⟨List.replicate (a+1) true,List.replicate (b+1) false,qs,he,?_,hne⟩
        rw [← hq,replicate_succ_end true a]
        simp only [List.replicate_succ,List.cons_append,List.append_assoc]
    | cons t ps =>
      obtain ⟨v,hv⟩ := pairedRunWord_cons_shape t ps
      obtain ⟨qs,hq,hne⟩ := halign (List.replicate b false++List.replicate a true++false::v)
      refine ⟨List.replicate a true++pairedRunWord (t::ps),List.replicate (b+1) false,
        qs,he,?_,hne⟩
      rw [← hq,hv]
      simp only [List.replicate_succ,List.cons_append,List.append_assoc]

#print axioms positive_word_cyclic_paired_runs


private theorem ends_true_of_append (p q v : List Bool) (hq : q ≠ [])
    (he : p++q = v++[true]) : ∃ t : List Bool, q = t++[true] := by
  induction p generalizing v with
  | nil => exact ⟨v,he⟩
  | cons a p ih =>
    cases v with
    | nil =>
      have hh := congrArg List.length he
      simp only [List.length_append,List.length_cons,List.length_nil] at hh
      have hzero : q.length = 0 := by omega
      exact (hq (by simpa using hzero)).elim
    | cons b v =>
      have ht : p++q = v++[true] := (List.cons.inj he).2
      exact ih v ht

private theorem begins_false_of_append (p q v : List Bool) (hp : p ≠ [])
    (he : p++q = false::v) : ∃ t : List Bool, p = false::t := by
  cases p with
  | nil => exact (hp rfl).elim
  | cons b p =>
    have hb : b = false := (List.cons.inj he).1
    exact ⟨p,by rw [hb]⟩

private theorem aligned_of_boundaries (w : List Bool)
    (hf : ∃ v : List Bool, w = false::v) (hl : ∃ v : List Bool, w = v++[true]) :
    ∃ v : List Bool, w = false::(v++[true]) := by
  obtain ⟨v,rfl⟩ := hf
  obtain ⟨q,hq⟩ := hl
  cases q with
  | nil => simp at hq
  | cons b q =>
    have ht : v = q++[true] := (List.cons.inj hq).2
    exact ⟨q,by rw [ht]⟩

private theorem pairedRunWord_shape_of_ne_nil (ps : List (ℕ × ℕ))
    (hp : pairedRunWord ps ≠ []) : ∃ v, pairedRunWord ps = false::(v++[true]) := by
  cases ps with
  | nil => exact (hp rfl).elim
  | cons p ps => exact pairedRunWord_cons_shape p ps

/-- Cyclic splitting between aligned positive run words is exactly cyclic splitting
between their run pairs. No cut through a digit run is lost or identified. -/
theorem pairedRunWord_cyclic_split_iff (ps qs : List (ℕ × ℕ)) :
    (∃ p q : List Bool, pairedRunWord ps = p++q ∧ pairedRunWord qs = q++p) ↔
      ∃ a b : List (ℕ × ℕ), ps = a++b ∧ qs = b++a := by
  constructor
  · rintro ⟨p,q,hp,hq⟩
    by_cases hpn : p = []
    · subst p
      simp only [List.nil_append,List.append_nil] at hp hq
      have he : ps = qs := pairedRunWord_injective (hp.trans hq.symm)
      exact ⟨[],ps,rfl,by simpa using he.symm⟩
    by_cases hqn : q = []
    · subst q
      simp only [List.nil_append,List.append_nil] at hp hq
      have he : ps = qs := pairedRunWord_injective (hp.trans hq.symm)
      exact ⟨ps,[],by simp,by simpa using he.symm⟩
    have hps : pairedRunWord ps ≠ [] := by
      rw [hp]
      intro he
      have hl := congrArg List.length he
      simp only [List.length_append,List.length_nil] at hl
      exact hpn (by simpa using (show p.length = 0 by omega))
    have hqs : pairedRunWord qs ≠ [] := by
      rw [hq]
      intro he
      have hl := congrArg List.length he
      simp only [List.length_append,List.length_nil] at hl
      exact hqn (by simpa using (show q.length = 0 by omega))
    obtain ⟨v,hv⟩ := pairedRunWord_shape_of_ne_nil ps hps
    obtain ⟨w,hw⟩ := pairedRunWord_shape_of_ne_nil qs hqs
    have hpf := begins_false_of_append p q (v++[true]) hpn (hp.symm.trans hv)
    have hqf := begins_false_of_append q p (w++[true]) hqn (hq.symm.trans hw)
    have hpl := ends_true_of_append q p (false::w) hpn (hq.symm.trans hw)
    have hql := ends_true_of_append p q (false::v) hqn (hp.symm.trans hv)
    obtain ⟨pv,hpv⟩ := aligned_of_boundaries p hpf hpl
    obtain ⟨qv,hqv⟩ := aligned_of_boundaries q hqf hql
    obtain ⟨a,ha⟩ := aligned_word_has_paired_runs pv
    obtain ⟨b,hb⟩ := aligned_word_has_paired_runs qv
    have hpa : pairedRunWord a = p := ha.symm.trans hpv.symm
    have hqb : pairedRunWord b = q := hb.symm.trans hqv.symm
    refine ⟨a,b,pairedRunWord_injective ?_,pairedRunWord_injective ?_⟩
    · rw [pairedRunWord_append,hpa,hqb]
      exact hp
    · rw [pairedRunWord_append,hpa,hqb]
      exact hq
  · rintro ⟨a,b,rfl,rfl⟩
    exact ⟨pairedRunWord a,pairedRunWord b,pairedRunWord_append a b,pairedRunWord_append b a⟩

#print axioms pairedRunWord_cyclic_split_iff


private theorem runPair_positive (a b : ℕ) (i j : Fin 2) :
    0 < (generator false^(a+1)*generator true^(b+1)) i j := by
  rw [generator_false_pow,generator_true_pow]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply,Fin.sum_univ_two]

private theorem pairedRunWord_cons_pos (p : ℕ × ℕ) (ps : List (ℕ × ℕ)) :
    ∀ i j, 0 < matrixWord (pairedRunWord (p::ps)) i j := by
  induction ps generalizing p with
  | nil =>
    rcases p with ⟨a,b⟩
    intro i j
    simpa only [pairedRunWord,List.append_nil,matrixWord_append,matrixWord_replicate] using
      runPair_positive a b i j
  | cons q ps ih =>
    rcases p with ⟨a,b⟩
    intro i j
    rw [pairedRunWord,matrixWord_append,matrixWord_append,matrixWord_replicate,matrixWord_replicate,
      Matrix.mul_apply,Fin.sum_univ_two]
    exact add_pos (mul_pos (runPair_positive a b i 0) (ih q 0 j))
      (mul_pos (runPair_positive a b i 1) (ih q 1 j))

/-- Every nonempty sequence of positive Gauss run pairs gives a strictly positive matrix. -/
theorem pairedRunWord_pos (ps : List (ℕ × ℕ)) (hps : ps ≠ []) :
    ∀ i j, 0 < matrixWord (pairedRunWord ps) i j := by
  cases ps with
  | nil => exact (hps rfl).elim
  | cons p ps => exact pairedRunWord_cons_pos p ps

@[simp] theorem pairedRunWord_wordPower (ps : List (ℕ × ℕ)) (n : ℕ) :
    pairedRunWord (wordPower ps n) = wordPower (pairedRunWord ps) n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [wordPower,pairedRunWord_append,ih]

private theorem wordPower_nil {α : Type*} (n : ℕ) : wordPower ([] : List α) n = [] := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [wordPower,List.nil_append,ih]

private theorem wordPower_succ_right {α : Type*} (w : List α) (n : ℕ) :
    wordPower w (n+1) = wordPower w n++w := by
  simpa only [wordPower,List.append_nil] using wordPower_add w n 1

/-- An aligned positive run word is a whole-word power exactly when its run-pair sequence is. -/
theorem pairedRunWord_root_iff (ps : List (ℕ × ℕ)) (hps : ps ≠ []) (k : ℕ) :
    (∃ w : List Bool, pairedRunWord ps = wordPower w k) ↔
      ∃ qs : List (ℕ × ℕ), ps = wordPower qs k := by
  have hne : pairedRunWord ps ≠ [] := by
    intro he
    exact hps (pairedRunWord_injective (show pairedRunWord ps = pairedRunWord [] from he))
  constructor
  · rintro ⟨w,he⟩
    cases k with
    | zero => exact (hne he).elim
    | succ k =>
      have hw : w ≠ [] := by
        intro hn
        rw [hn,wordPower_nil] at he
        exact hne he
      obtain ⟨v,hv⟩ := pairedRunWord_shape_of_ne_nil ps hne
      have hleft : w++wordPower w k = false::(v++[true]) := by
        exact he.symm.trans hv
      have hright : wordPower w k++w = (false::v)++[true] := by
        rw [← wordPower_succ_right]
        exact he.symm.trans hv
      have hf := begins_false_of_append w (wordPower w k) (v++[true]) hw hleft
      have hl := ends_true_of_append (wordPower w k) w (false::v) hw hright
      obtain ⟨t,ht⟩ := aligned_of_boundaries w hf hl
      obtain ⟨qs,hqs⟩ := aligned_word_has_paired_runs t
      have hwq : w = pairedRunWord qs := ht.trans hqs
      refine ⟨qs,pairedRunWord_injective ?_⟩
      rw [pairedRunWord_wordPower,← hwq]
      exact he
  · rintro ⟨qs,rfl⟩
    exact ⟨pairedRunWord qs,pairedRunWord_wordPower qs k⟩

/-- The literal integral matrix of the actual finite Gauss word associated to positive run pairs. -/
def actualPairedMatrix (ps : List (ℕ × ℕ)) :
    IntMatrix :=
  intMatrix (wordMatrix (pairedDigits ps).length (asWord (pairedDigits ps)))

theorem actualPairedMatrix_eq (ps : List (ℕ × ℕ)) :
    actualPairedMatrix ps = intMatrix (matrixWord (pairedRunWord ps)) := by
  rw [actualPairedMatrix,pairedDigits_matrix]

/-- Actual even Gauss matrices are integrally conjugate exactly under cyclic rotation of whole digit pairs. -/
theorem actualPairedMatrix_conjugacy_iff (ps qs : List (ℕ × ℕ)) (hps : ps ≠ []) (hqs : qs ≠ []) :
    (∃ C : IntMatrix,
      C.det = 1 ∧ C*actualPairedMatrix ps = actualPairedMatrix qs*C) ↔
      ∃ a b : List (ℕ × ℕ), ps = a++b ∧ qs = b++a := by
  rw [actualPairedMatrix_eq,actualPairedMatrix_eq]
  exact (integral_intertwiner_iff_cyclic_split _ _ (pairedRunWord_pos ps hps)
    (pairedRunWord_pos qs hqs)).trans (pairedRunWord_cyclic_split_iff ps qs)

/-- Integral roots of actual even Gauss matrices are exactly repetitions of whole digit pairs. -/
theorem actualPairedMatrix_root_iff (ps : List (ℕ × ℕ)) (hps : ps ≠ []) (k : ℕ) :
    (∃ B : IntMatrix,
      B.det = 1 ∧ B^k = actualPairedMatrix ps) ↔
      ∃ qs : List (ℕ × ℕ), ps = wordPower qs k := by
  rw [actualPairedMatrix_eq]
  exact (integral_root_iff_word_power _ (pairedRunWord_pos ps hps) k).trans
    (pairedRunWord_root_iff ps hps k)

#print axioms pairedRunWord_pos
#print axioms pairedRunWord_root_iff
#print axioms actualPairedMatrix_conjugacy_iff
#print axioms actualPairedMatrix_root_iff


/-- Every positive-trace hyperbolic integral determinant-one matrix is conjugate
to an actual nonempty even Gauss word. -/
theorem exists_actualPairedMatrix_intertwiner
    (A : IntMatrix)
    (hA : A.det = 1) (ht : 2 < A 0 0+A 1 1) :
    ∃ ps : List (ℕ × ℕ), ps ≠ [] ∧
      ∃ C : IntMatrix,
        C.det = 1 ∧ C*A = actualPairedMatrix ps*C := by
  obtain ⟨P,Q,u,hP,hQ,hPQ,hQP,hword,hpos⟩ := exists_integral_word_conjugate A hA ht
  obtain ⟨p,q,ps,hu,hrot,hps⟩ := positive_word_cyclic_paired_runs u hpos
  obtain ⟨N,hN,hinter⟩ := (positive_intertwiner_iff_cyclic_split u (pairedRunWord ps)).mpr
    ⟨p,q,hu,hrot⟩
  have hND : (intMatrix N).det = 1 := (unimodular_iff_det N).mp hN
  have hNI : intMatrix N*intMatrix (matrixWord u) =
      intMatrix (matrixWord (pairedRunWord ps))*intMatrix N := by
    simpa only [intMatrix_mul] using congrArg intMatrix hinter
  have hQA : Q*A = intMatrix (matrixWord u)*Q := by
    calc
      _ = (Q*A)*(P*Q) := by rw [hPQ,Matrix.mul_one]
      _ = (Q*A*P)*Q := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hword]
  refine ⟨ps,hps,intMatrix N*Q,?_,?_⟩
  · rw [Matrix.det_mul,hND,hQ,mul_one]
  · rw [actualPairedMatrix_eq,Matrix.mul_assoc,hQA,← Matrix.mul_assoc,hNI,Matrix.mul_assoc]

#print axioms exists_actualPairedMatrix_intertwiner


/-- Reversed digit order turns concatenation of run pairs into reversed concatenation of digit lists. -/
theorem pairedDigits_append (ps qs : List (ℕ × ℕ)) :
    pairedDigits (ps++qs) = pairedDigits qs++pairedDigits ps := by
  induction ps with
  | nil => simp only [List.nil_append,pairedDigits,List.append_nil]
  | cons p ps ih => simp only [List.cons_append,pairedDigits,ih,List.append_assoc]

/-- Read an actual even-length Gauss word into its oriented positive run pairs. -/
def evenWordPairs : (k : ℕ) → Word (2*k) → List (ℕ × ℕ)
  | 0, _ => []
  | k+1, a => evenWordPairs k (Fin.tail (Fin.tail a))++[(Fin.tail a 0,a 0)]

theorem evenWordPairs_length (k : ℕ) (a : Word (2*k)) : (evenWordPairs k a).length = k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [evenWordPairs,List.length_append,List.length_cons,List.length_nil,ih]

/-- Pair extraction recovers every digit of the original source word in its original order. -/
theorem evenWordPairs_digits (k : ℕ) (a : Word (2*k)) :
    pairedDigits (evenWordPairs k a) = List.ofFn a := by
  induction k with
  | zero => simp only [evenWordPairs,pairedDigits,List.ofFn_zero]
  | succ k ih =>
    rw [evenWordPairs,pairedDigits_append]
    simp only [pairedDigits,List.nil_append,List.cons_append,List.ofFn_succ,ih]
    rfl

/-- Every actual even Gauss word has exactly the positive run matrix read from its digits. -/
theorem evenWordPairs_matrix (k : ℕ) (a : Word (2*k)) :
    wordMatrix (2*k) a = matrixWord (pairedRunWord (evenWordPairs k a)) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change (wordMatrix (2*k) (Fin.tail (Fin.tail a))*digitMatrix (Fin.tail a 0))*digitMatrix (a 0) = _
    rw [evenWordPairs,pairedRunWord_append,matrixWord_append]
    simp only [pairedRunWord,List.append_nil,matrixWord_append,matrixWord_replicate]
    rw [← digitMatrix_pair,← ih,Matrix.mul_assoc]

#print axioms evenWordPairs_digits
#print axioms evenWordPairs_matrix


private theorem evenWordPairs_ne_nil (k : ℕ) (hk : 0 < k) (a : Word (2*k)) :
    evenWordPairs k a ≠ [] := by
  intro he
  have h := evenWordPairs_length k a
  rw [he,List.length_nil] at h
  omega

/-- Integral conjugacy of arbitrary actual even Gauss words is cyclic splitting of their consecutive digit pairs. -/
theorem evenWordMatrix_conjugacy_iff (k l : ℕ) (hk : 0 < k) (hl : 0 < l)
    (a : Word (2*k)) (b : Word (2*l)) :
    (∃ C : IntMatrix, C.det = 1 ∧ C*intMatrix (wordMatrix (2*k) a) =
      intMatrix (wordMatrix (2*l) b)*C) ↔
      ∃ p q : List (ℕ × ℕ), evenWordPairs k a = p++q ∧ evenWordPairs l b = q++p := by
  have ha : intMatrix (wordMatrix (2*k) a) = actualPairedMatrix (evenWordPairs k a) := by
    rw [actualPairedMatrix_eq,evenWordPairs_matrix]
  have hb : intMatrix (wordMatrix (2*l) b) = actualPairedMatrix (evenWordPairs l b) := by
    rw [actualPairedMatrix_eq,evenWordPairs_matrix]
  rw [ha,hb]
  exact actualPairedMatrix_conjugacy_iff _ _ (evenWordPairs_ne_nil k hk a) (evenWordPairs_ne_nil l hl b)

/-- Integral roots of arbitrary actual even Gauss words preserve whole digit-pair periods. -/
theorem evenWordMatrix_root_iff (k : ℕ) (hk : 0 < k) (a : Word (2*k)) (r : ℕ) :
    (∃ B : IntMatrix, B.det = 1 ∧ B^r = intMatrix (wordMatrix (2*k) a)) ↔
      ∃ qs : List (ℕ × ℕ), evenWordPairs k a = wordPower qs r := by
  have ha : intMatrix (wordMatrix (2*k) a) = actualPairedMatrix (evenWordPairs k a) := by
    rw [actualPairedMatrix_eq,evenWordPairs_matrix]
  rw [ha]
  exact actualPairedMatrix_root_iff _ (evenWordPairs_ne_nil k hk a) r

/-- Every positive-trace integral hyperbolic class has a literal nonempty even Gauss word representative. -/
theorem exists_evenWordMatrix_intertwiner (A : IntMatrix) (hA : A.det = 1)
    (ht : 2 < A 0 0+A 1 1) :
    ∃ k : ℕ, 0 < k ∧ ∃ a : Word (2*k), ∃ C : IntMatrix,
      C.det = 1 ∧ C*A = intMatrix (wordMatrix (2*k) a)*C := by
  obtain ⟨ps,hps,C,hC,he⟩ := exists_actualPairedMatrix_intertwiner A hA ht
  have hlen : 0 < ps.length := by
    cases ps with
    | nil => exact (hps rfl).elim
    | cons p ps => exact Nat.succ_pos _
  refine ⟨ps.length,hlen,?_⟩
  rw [← pairedDigits_length ps]
  exact ⟨asWord (pairedDigits ps),C,hC,he⟩

private theorem wordPower_length {α : Type*} (w : List α) (k : ℕ) :
    (wordPower w k).length = k*w.length := by
  induction k with
  | zero => simp only [wordPower,List.length_nil,Nat.zero_mul]
  | succ k ih =>
    rw [wordPower,List.length_append,ih,Nat.succ_mul]
    omega

private theorem actualPairedMatrix_singleton_square (n : ℕ) :
    actualPairedMatrix [(n,n)] = intMatrix (digitMatrix n)^2 := by
  rw [actualPairedMatrix,wordMatrix_asWord]
  simp only [pairedDigits,List.nil_append,gaussListMatrix,Matrix.one_mul,intMatrix_mul,pow_two]

/-- The square of every one-digit Gauss word is primitive in the determinant-one integral group.
This gives the odd-digit-period exception to ordinary digit-word primitivity. -/
theorem single_digit_square_primitive (n k : ℕ) (hk : 2 ≤ k) :
    ¬ ∃ B : IntMatrix, B.det = 1 ∧ B^k = intMatrix (digitMatrix n)^2 := by
  rw [← actualPairedMatrix_singleton_square,actualPairedMatrix_root_iff [(n,n)] (by simp)]
  rintro ⟨qs,hq⟩
  have he := congrArg List.length hq
  simp only [List.length_cons,List.length_nil,wordPower_length] at he
  by_cases hz : qs.length = 0
  · rw [hz,mul_zero] at he
    omega
  · have hlen : 1 ≤ qs.length := by omega
    have hm := Nat.mul_le_mul_left k hlen
    simp only [mul_one] at hm
    omega

#print axioms evenWordMatrix_conjugacy_iff
#print axioms evenWordMatrix_root_iff
#print axioms exists_evenWordMatrix_intertwiner
#print axioms single_digit_square_primitive

end GaloisForLFunctions.RenormalizedIntersectionTheory.MayerGaussCoding
