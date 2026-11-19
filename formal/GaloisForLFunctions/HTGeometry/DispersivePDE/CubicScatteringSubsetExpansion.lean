import GaloisForLFunctions.HTGeometry.DispersivePDE.CubicScatteringComplementaryPhases

/-!
# The full two-copy Hirota expansion

Waves in neither copy disappear. Waves in both copies contribute a common
factor to the coefficient. Only waves in one copy enter the dispersion,
and their complementary sum vanishes. Labels may have repeated momenta
and independent real amplitudes.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry.DispersivePDE.CubicHierarchy.WaveList
variable {α : Type*}

/-- Sum over all choices of occupied labels. -/
def subsetSum : List α → (List α → ℝ) → ℝ
  | [],F => F []
  | x::xs,F => subsetSum xs F+subsetSum xs (fun a => F (x::a))

theorem subset_add (xs : List α) (F G : List α → ℝ) :
    subsetSum xs (fun a => F a+G a)=subsetSum xs F+subsetSum xs G := by
  induction xs generalizing F G with
  | nil => rfl
  | cons x xs ih => simp only [subsetSum,ih]; ring

/-- Disjoint common and singly occupied sublists; a third class is unused. -/
private def classes : List α → (List α → List α → ℝ) → ℝ
  | [],F => F [] []
  | x::xs,F => classes xs F+classes xs (fun c u => F (x::c) u)+classes xs (fun c u => F c (x::u))

private theorem classes_add (xs : List α) (F G : List α → List α → ℝ) :
    classes xs (fun c u => F c u+G c u)=classes xs F+classes xs G := by
  induction xs generalizing F G with
  | nil => rfl
  | cons x xs ih => simp only [classes,ih]; ring

private theorem classes_zero (xs : List α) : classes xs (fun _ _ => 0)=0 := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [classes,ih,add_zero]

def paired (xs : List α) (F : List α → List α → ℝ) :=
  subsetSum xs fun a => subsetSum xs (F a)

private def partition (F : List α → List α → ℝ) (c u : List α) :=
  splitSum u fun a b => F (c++a) (c++b)

private theorem partition_singles (F : List α → List α → ℝ)
    (hf : ∀ {a b c d : List α}, a.Perm c → b.Perm d → F a b=F c d)
    (x : α) (c u : List α) :
    partition F c (x::u) =
      partition (fun a b => F (x::a) b) c u+partition (fun a b => F a (x::b)) c u := by
  unfold partition
  rw [splitSum]
  exact congrArg₂ (·+·) (split_congr _ _ _ fun a b _ => hf (slide x c a).symm (.refl _))
    (split_congr _ _ _ fun a b _ => hf (.refl _) (slide x c b).symm)

private theorem group_occupations (xs : List α) (F : List α → List α → ℝ)
    (hf : ∀ {a b c d : List α}, a.Perm c → b.Perm d → F a b=F c d) :
    paired xs F=classes xs (partition F) := by
  induction xs generalizing F with
  | nil => rfl
  | cons x xs ih =>
    have h1 := ih (fun a b => F (x::a) b) (fun ha hb => hf (ha.cons x) hb)
    have h2 := ih (fun a b => F a (x::b)) (fun ha hb => hf ha (hb.cons x))
    have h3 := ih (fun a b => F (x::a) (x::b)) (fun ha hb => hf (ha.cons x) (hb.cons x))
    have step : paired (x::xs) F = paired xs F+paired xs (fun a b => F a (x::b))+
        (paired xs (fun a b => F (x::a) b)+paired xs (fun a b => F (x::a) (x::b))) := by
      simp only [paired,subsetSum,subset_add]
    rw [step,ih F hf,h1,h2,h3,classes]
    simp only [partition_singles F hf,classes_add]
    change _ = classes xs (partition F)+classes xs (partition (fun a b => F (x::a) (x::b)))+
      (classes xs (partition (fun a b => F (x::a) b))+classes xs (partition (fun a b => F a (x::b))))
    ring

private theorem split_map {β : Type*} (k : α → β) (xs : List α) (F : List β → List β → ℝ) :
    splitSum (xs.map k) F = splitSum xs (fun a b => F (a.map k) (b.map k)) := by
  induction xs generalizing F with
  | nil => rfl
  | cons x xs ih => simp only [List.map_cons,splitSum,ih]

def product (f : α → ℝ) (xs : List α) := (xs.map f).prod

private theorem prod_append (f : α → ℝ) (a b : List α) :
    product f (a++b)=product f a*product f b := by simp [product]

/-- The scattering factor of two occupied momenta. -/
def exchange (x y : ℝ) := (x-y)^2/(x+y)^2

theorem phase_cons (x : ℝ) (xs : List ℝ) :
    phase (x::xs)=product (exchange x) xs*phase xs := by
  have hed : factors (fun y => (x-y)^2) xs/factors (fun y => (x+y)^2) xs =
      product (exchange x) xs := by
    induction xs with
    | nil => simp [product,factors]
    | cons y ys ih =>
      change (_*_)/(_*_)=exchange x y*product (exchange x) ys
      rw [← ih]
      exact mul_div_mul_comm _ _ _ _
  rw [phase,pairWeight,pairDen,← hed,phase]
  exact mul_div_mul_comm _ _ _ _

private def interaction (c u : List ℝ) := product (fun x => product (exchange x) u) c

private theorem interaction_append (c a b : List ℝ) :
    interaction c (a++b)=interaction c a*interaction c b := by
  induction c with
  | nil => simp [interaction,product]
  | cons x c ih =>
    change product (exchange x) (a++b)*interaction c (a++b)=
      (product (exchange x) a*interaction c a)*(product (exchange x) b*interaction c b)
    rw [prod_append,ih]
    ring

private theorem phase_join (c u : List ℝ) :
    phase (c++u)=phase c*phase u*interaction c u := by
  induction c with
  | nil => simp [phase,pairWeight,pairDen,interaction,product]
  | cons x c ih =>
    simp only [List.cons_append,phase_cons,ih,interaction,product,List.map_cons,List.prod_cons,
      List.map_append,List.prod_append]
    ring

theorem phase_perm {a b : List ℝ} (h : a.Perm b) : phase a=phase b := by
  rw [phase,phase,pairWeight_perm h,den_perm h]

/-- A single occupied set carries its Cauchy pair phase and the product of
the amplitudes of the occupied labels. -/
def amplitude (k A : α → ℝ) (a : List α) := phase (a.map k)*product A a

def symbolTerm (w : Weights) (k A : α → ℝ) (a b : List α) :=
  amplitude k A a*amplitude k A b*
    dispersion w ((a.map k).sum-(b.map k).sum) (cubicSum (a.map k)-cubicSum (b.map k))

private theorem symTerm_perm (w : Weights) (k A : α → ℝ) {a b c d : List α}
    (h : a.Perm c) (g : b.Perm d) : symbolTerm w k A a b=symbolTerm w k A c d := by
  simp only [symbolTerm,amplitude,product,cubicSum,phase_perm (h.map k),phase_perm (g.map k),
    (h.map A).prod_eq,(g.map A).prod_eq,(h.map k).sum_eq,(g.map k).sum_eq,
    ((h.map k).map _).sum_eq,((g.map k).map _).sum_eq]

private theorem common_factor (w : Weights) (k A : α → ℝ) (c u a b : List α) (hp : (a++b).Perm u) :
    symbolTerm w k A (c++a) (c++b) =
      (amplitude k A c^2*product A u*interaction (c.map k) (u.map k)) *
      (phase (a.map k)*phase (b.map k)*
        dispersion w ((a.map k).sum-(b.map k).sum) (cubicSum (a.map k)-cubicSum (b.map k))) := by
  have hpA : product A u=product A a*product A b :=
    ((hp.map A).prod_eq.symm).trans (prod_append A a b)
  have hpK : interaction (c.map k) (u.map k)=interaction (c.map k) (a.map k)*interaction (c.map k) (b.map k) := by
    have e (x : ℝ) : product (exchange x) (u.map k)=product (exchange x) ((a++b).map k) :=
      (((hp.map k).map (exchange x)).prod_eq).symm
    change product (fun x => product (exchange x) (u.map k)) (c.map k)=_
    simp_rw [e,List.map_append]
    exact interaction_append _ _ _
  simp only [symbolTerm,amplitude,List.map_append,phase_join,prod_append,List.sum_append,cubicSum,
    add_sub_add_left_eq_sub,hpA,hpK]
  ring

/-- The complete two-copy subset expansion vanishes for every finite bank
of positive cubic momenta, including independent amplitudes at collisions. -/
theorem full_symbol_cancellation (w : Weights) (k : α → {t : ℝ // 0<t}) (A : α → ℝ) (xs : List α) :
    subsetSum xs (fun a => subsetSum xs (symbolTerm w (fun z => (k z).val) A a))=0 := by
  let K := fun z => (k z).val
  change paired xs (symbolTerm w K A)=0
  rw [group_occupations _ _ (fun h g => symTerm_perm _ _ _ h g)]
  suffices h : ∀ c u, partition (symbolTerm w K A) c u=0 by
    rw [funext fun c => funext (h c),classes_zero]
  intro c u
  let C := amplitude K A c^2*product A u*interaction (c.map K) (u.map K)
  let F := fun a b : List ℝ => phase a*phase b*dispersion w (a.sum-b.sum) (cubicSum a-cubicSum b)
  have he : partition (symbolTerm w K A) c u =
      splitSum u (fun a b => C*F (a.map K) (b.map K)) :=
    split_congr _ _ _ fun a b hp => common_factor _ _ _ _ _ _ _ hp
  rw [he,split_scale,← split_map]
  have zero : splitSum (u.map K) F=0 := positive_complementary_cancellation _ _ fun t ht => by
    obtain ⟨z,_,rfl⟩ := List.mem_map.mp ht
    exact (k z).property
  rw [zero,mul_zero]

#print axioms group_occupations
#print axioms full_symbol_cancellation
end GaloisForLFunctions.HTGeometry.DispersivePDE.CubicHierarchy.WaveList
