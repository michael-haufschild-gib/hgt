import GaloisForLFunctions.ExclusionOfTheCriticalState.Pick.PolynomialHeatingSamples

/-!
# The adaptive lower bound for polynomial heating

An arbitrary deterministic procedure can be followed along the transcript
of the constant unit slope. On d+1 visited nodes a different polynomial
slope of degree at most d reproduces every reading. Combined with the
one-step adaptive disambiguation, this determines the exact threshold
for all positive degrees.
-/

noncomputable section
open Polynomial Finset
namespace GaloisForLFunctions.ExclusionOfTheCriticalState.ProbeWalk.HeatSamples
open JumpGrid
variable {d : ℕ}

/-- The next sampling location may depend arbitrarily on all earlier readings.
The list records the most recent answer first. -/
abbrev Policy := List ℝ → ℝ

def readings (T : Policy) (f : ℝ → ℝ) : ℕ → List ℝ
  | 0 => []
  | k+1 => let ys := readings T f k
           f (T ys)::ys

abbrev history (T : Policy) (P : ℝ[X]) := readings T (power P)

theorem readings_length (T : Policy) (f : ℝ → ℝ) (k : ℕ) : (readings T f k).length=k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [readings,List.length_cons,ih]

theorem readings_shorter (T : Policy) (f g : ℝ → ℝ) {m n : ℕ} (h : m≤n) :
    readings T f n=readings T g n → readings T f m=readings T g m := by
  induction h with
  | refl => exact id
  | step _ ih => intro e; exact ih (List.cons.inj e).2

private theorem unit_history (T : Policy) (P : ℝ[X]) (k : ℕ)
    (h : ∀ i<k, power P (T (List.replicate i 1))=1) :
    history T P k=List.replicate k 1 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change power P (T (history T P k))::history T P k=_
    rw [ih (fun i hi => h i (Nat.lt_succ_of_lt hi)),h k (Nat.lt_succ_self _),List.replicate_succ]

private theorem unit_alias (d : ℕ) (hd : 0<d) (S : Finset ℝ) (hs : S.Nonempty) (num : S.card≤d+1) :
    ∃ Q : Channel d, (∀ x∈S, power Q.val x=1) ∧ power Q.val≠power 1 := by
  classical
  obtain ⟨a,ha⟩ := hs
  by_cases small : S.card≤d
  · let Q : Channel d := ⟨1+vanishing S,(natDegree_add_le _ _).trans
      (max_le (by simp) ((vanishing_degree _).le.trans small))⟩
    have value (x : ℝ) (hx : x∈S) : Q.val.eval x=1 := by simp [Q,(vanishing_eval S x).mpr hx]
    refine ⟨Q,fun x hx => by simp only [power,value x hx,one_pow],?_⟩
    intro e
    rcases (power_eq_iff _ _).mp e with e|e
    · apply (monic_prod_X_sub_C id S).ne_zero
      change 1+vanishing S=1 at e
      exact add_left_cancel (e.trans (add_zero (1:ℝ[X])).symm)
    · have eq := congrArg (Polynomial.eval a) e
      rw [value _ ha,eval_neg,eval_one] at eq
      norm_num at eq
  · have hcard : S.card=d+1 := by omega
    let U := vanishing (S.erase a)
    have hzero : U.eval a≠0 := fun h => (Finset.notMem_erase _ _) ((vanishing_eval _ _).mp h)
    have hU : U.natDegree ≤ d := by
      rw [show U = vanishing (S.erase a) from rfl,vanishing_degree,card_erase_of_mem ha,hcard]
      omega
    let Q : Channel d := ⟨1-C (2/U.eval a)*U,(natDegree_sub_le _ _).trans
      (max_le (by simp) ((natDegree_C_mul_le _ _).trans hU))⟩
    have atA : Q.val.eval a= -1 := by
      rw [show Q.val = 1-C (2/U.eval a)*U from rfl,eval_sub,eval_one,eval_mul,eval_C,div_mul_cancel₀ _ hzero]
      norm_num
    have other (x : ℝ) (hx : x∈S.erase a) : Q.val.eval x=1 := by
      simp [Q,show U.eval x=0 from (vanishing_eval _ _).mpr hx]
    refine ⟨Q,fun x hx => ?_,?_⟩
    · by_cases e : x=a
      · subst x; simp [power,atA]
      · simp [power,other _ (mem_erase.mpr ⟨e,hx⟩)]
    · intro e
      rcases (power_eq_iff _ _).mp e with e|e
      · have eq := congrArg (Polynomial.eval a) e
        rw [atA,eval_one] at eq
        norm_num at eq
      · have hn : (S.erase a).Nonempty := card_pos.mp (by rw [card_erase_of_mem ha,hcard]; omega)
        obtain ⟨b,hb⟩ := hn
        have eq := congrArg (Polynomial.eval b) e
        rw [other b hb,eval_neg,eval_one] at eq
        norm_num at eq

/-- Fewer than d+2 adaptive heating measurements cannot identify every
slope of positive degree bound d. The adversarial transcript is all ones. -/
theorem adaptive_lower (d : ℕ) (hd : 0<d) (T : Policy) :
    ∃ Q : Channel d, history T Q.val (d+1)=history T 1 (d+1) ∧ power Q.val≠power 1 := by
  classical
  let node := fun i : ℕ => T (List.replicate i 1)
  let S := (range (d+1)).image node
  have cover (i : ℕ) (hi : i<d+1) : node i∈S := mem_image_of_mem _ (mem_range.mpr hi)
  have bound : S.card≤d+1 := (card_image_le (s:=range (d+1)) (f:=node)).trans_eq (card_range _)
  obtain ⟨Q,hq,hn⟩ := unit_alias d hd S ⟨node 0,cover 0 (Nat.succ_pos _)⟩ bound
  exact ⟨Q,(unit_history T Q.val _ fun i hi => hq _ (cover i hi)).trans
    (unit_history T 1 _ fun _ _ => by simp [power]).symm,hn⟩

private def samplePrefix (f : Fin (d+1) → ℝ) : ℕ → List ℝ
  | 0 => []
  | k+1 => (if h : k<d+1 then f ⟨k,h⟩ else 0)::samplePrefix f k

private theorem prefix_length (f : Fin (d+1) → ℝ) (k : ℕ) : (samplePrefix f k).length=k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [samplePrefix,List.length_cons,ih]

private theorem prefix_agrees (f g : Fin (d+1) → ℝ) (k : ℕ) :
    samplePrefix f k=samplePrefix g k → ∀ i : Fin (d+1), i.val<k → f i=g i := by
  induction k with
  | zero => intro _ i hi; omega
  | succ k ih =>
    intro e i hi
    obtain ⟨head,tail⟩ := List.cons.inj e
    rcases Nat.lt_or_ge i.val k with hl|hl
    · exact ih tail i hl
    · have eq : k=i.val := by omega
      subst k
      simpa only [dif_pos i.isLt] using head

private def recorded (ys : List ℝ) : Fin (d+1) → ℝ := by
  classical
  exact if h : ∃ f : Fin (d+1) → ℝ, samplePrefix f (d+1)=ys then h.choose else 0

private theorem recorded_prefix (f : Fin (d+1) → ℝ) : recorded (samplePrefix f (d+1))=f := by
  classical
  have e : ∃ g : Fin (d+1) → ℝ, samplePrefix g (d+1)=samplePrefix f (d+1) := ⟨f,rfl⟩
  rw [recorded,dif_pos e]
  exact funext fun i => prefix_agrees _ _ _ e.choose_spec i i.isLt

/-- Sample the prescribed grid in order, then use its readings to choose
a point separating all still-distinct candidate profiles. -/
def optimalPolicy (v : Nodes d) (ys : List ℝ) : ℝ :=
  if h : ys.length<d+1 then v ⟨ys.length,h⟩ else finalNode v (recorded ys)

private theorem grid_history (v : Nodes d) (P : ℝ[X]) (k : ℕ) (hk : k≤d+1) :
    history (optimalPolicy v) P k=samplePrefix (fun i => power P (v i)) k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have h : k<d+1 := by omega
    change power P (optimalPolicy v (history _ P k))::history _ P k=_
    simp only [ih h.le,optimalPolicy,prefix_length,dif_pos h,samplePrefix]

/-- The sequential policy attains the upper bound with exactly d+2 readings. -/
theorem optimal_history (v : Nodes d) (P Q : Channel d) :
    history (optimalPolicy v) P.val (d+2)=history (optimalPolicy v) Q.val (d+2) ↔
      power P.val=power Q.val := by
  let f := fun i => power P.val (v i)
  let g := fun i => power Q.val (v i)
  have last (U : Channel d) : history (optimalPolicy v) U.val (d+2)=
      power U.val (finalNode v (fun i => power U.val (v i)))::samplePrefix (fun i => power U.val (v i)) (d+1) := by
    change power U.val (optimalPolicy v (history _ U.val (d+1)))::history _ U.val (d+1)=_
    rw [grid_history v _ _ le_rfl]
    simp only [optimalPolicy,prefix_length,dif_neg (Nat.lt_irrefl _),recorded_prefix]
  rw [last,last]
  constructor
  · intro e
    obtain ⟨head,tail⟩ := List.cons.inj e
    have fg : f=g := funext fun i => prefix_agrees f g _ tail i i.isLt
    change power P.val (finalNode v f)=power Q.val (finalNode v g) at head
    rw [← fg] at head
    exact (adaptive_recovery v P Q (congrFun fg)).mp head
  · intro e
    simp only [e]

/-- The exact deterministic query complexity at every positive degree,
including procedures that repeat points or choose them from arbitrary transcripts. -/
theorem sequential_threshold (d : ℕ) (hd : 0<d) (n : ℕ) :
    (∃ T : Policy, ∀ P Q : Channel d, history T P.val n=history T Q.val n → power P.val=power Q.val) ↔
      d+2≤n := by
  constructor
  · rintro ⟨T,hT⟩
    by_contra! hn
    obtain ⟨Q,eq,diff⟩ := adaptive_lower d hd T
    exact diff (hT Q ⟨1,by simp⟩ (readings_shorter T _ _ (by omega : n≤d+1) eq))
  · intro hn
    let v : Nodes d := ⟨fun i => (i.val:ℝ),by
      intro i j h
      change (i.val : ℝ) = (j.val : ℝ) at h
      exact Fin.ext (by exact_mod_cast h)⟩
    exact ⟨optimalPolicy v,fun P Q e => (optimal_history v P Q).mp (readings_shorter _ _ _ hn e)⟩

end GaloisForLFunctions.ExclusionOfTheCriticalState.ProbeWalk.HeatSamples
