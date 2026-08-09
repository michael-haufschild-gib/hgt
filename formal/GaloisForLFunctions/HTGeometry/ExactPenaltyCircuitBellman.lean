import Mathlib

/-!
# Exact-penalty Bellman duality for robust circuit complexity

For a metric state space acted on by an inverse-closed family of isometric gates, the
exact-penalty value

`V(x) = inf over gate words w of ( |w| + λ (d(x, W_w χ) − ε)₊ )`

is `λ`-Lipschitz, solves a one-gate Bellman equation, changes by at most one under a gate, and is
the largest solution of the corresponding subsolution inequalities.  When the gate family is
compact and the approximate complexity `C_ε(x)` is finite, `V` equals `C_ε(x)` for every penalty
above an explicit finite threshold.

Consequently a robust Bellman calibration exists exactly when the circuit lower bound it would
certify is true: existence of a calibration is not an independent source of complexity growth.
-/

namespace HTGeometry

section Words

variable {X : Type*} [MetricSpace X] {Γ : Type*}

/-- Action of a gate word.  The head of the list is the gate applied last. -/
def wordAct (act : Γ → X → X) (w : List Γ) (x : X) : X := w.foldr act x

@[simp] theorem wordAct_nil (act : Γ → X → X) (x : X) : wordAct act [] x = x := rfl

@[simp] theorem wordAct_cons (act : Γ → X → X) (g : Γ) (w : List Γ) (x : X) :
    wordAct act (g :: w) x = act g (wordAct act w x) := rfl

/-- States reachable from the reference point in at most `s` gates. -/
def reachSet (act : Γ → X → X) (chi : X) (s : ℕ) : Set X :=
  {z | ∃ w : List Γ, w.length ≤ s ∧ wordAct act w chi = z}

theorem mem_reachSet_self (act : Γ → X → X) (chi : X) (s : ℕ) :
    chi ∈ reachSet act chi s := ⟨[], by simp, rfl⟩

theorem reachSet_nonempty (act : Γ → X → X) (chi : X) (s : ℕ) :
    (reachSet act chi s).Nonempty := ⟨chi, mem_reachSet_self act chi s⟩

theorem reachSet_mono (act : Γ → X → X) (chi : X) {s t : ℕ} (h : s ≤ t) :
    reachSet act chi s ⊆ reachSet act chi t := by
  rintro z ⟨w, hw, rfl⟩
  exact ⟨w, hw.trans h, rfl⟩

/-- Distance from a state to the `s`-th reachable layer. -/
noncomputable def layerDist (act : Γ → X → X) (chi : X) (s : ℕ) (x : X) : ℝ :=
  Metric.infDist x (reachSet act chi s)

/-- Approximate circuit complexity at slack `eps`. -/
noncomputable def approxComplexity (act : Γ → X → X) (chi : X) (eps : ℝ) (x : X) : ℕ :=
  sInf {s | ∃ w : List Γ, w.length ≤ s ∧ dist x (wordAct act w chi) ≤ eps}

/-- Penalised cost of one gate word. -/
noncomputable def wordCost (act : Γ → X → X) (chi : X) (lam eps : ℝ) (x : X)
    (w : List Γ) : ℝ :=
  (w.length : ℝ) + lam * max (dist x (wordAct act w chi) - eps) 0

/-- Exact-penalty value function. -/
noncomputable def penaltyValue (act : Γ → X → X) (chi : X) (lam eps : ℝ) (x : X) : ℝ :=
  ⨅ w : List Γ, wordCost act chi lam eps x w

/-- The Bellman subsolution class: dominated by the metric obstacle and changing by at most one
along any gate. -/
def IsBellmanSubsolution (act : Γ → X → X) (inv : Γ → Γ) (chi : X) (lam eps : ℝ)
    (phi : X → ℝ) : Prop :=
  (∀ x, phi x ≤ lam * max (dist x chi - eps) 0) ∧
  (∀ (g : Γ) (x : X), phi x ≤ 1 + phi (act (inv g) x))

end Words

section Value

variable {X : Type*} [MetricSpace X] {Γ : Type*}
variable {act : Γ → X → X} {inv : Γ → Γ} {chi : X} {lam eps : ℝ}

theorem wordCost_nonneg (hlam : 0 ≤ lam) (x : X) (w : List Γ) :
    0 ≤ wordCost act chi lam eps x w := by
  have : 0 ≤ lam * max (dist x (wordAct act w chi) - eps) 0 :=
    mul_nonneg hlam (le_max_right _ _)
  have hl : (0 : ℝ) ≤ (w.length : ℝ) := Nat.cast_nonneg _
  simpa [wordCost] using add_nonneg hl this

theorem bddBelow_range_wordCost (hlam : 0 ≤ lam) (x : X) :
    BddBelow (Set.range (wordCost act chi lam eps x)) := by
  refine ⟨0, ?_⟩
  rintro r ⟨w, rfl⟩
  exact wordCost_nonneg hlam x w

theorem penaltyValue_le_wordCost (hlam : 0 ≤ lam) (x : X) (w : List Γ) :
    penaltyValue act chi lam eps x ≤ wordCost act chi lam eps x w :=
  ciInf_le (bddBelow_range_wordCost hlam x) w

theorem le_penaltyValue {c : ℝ} (x : X)
    (h : ∀ w : List Γ, c ≤ wordCost act chi lam eps x w) :
    c ≤ penaltyValue act chi lam eps x :=
  le_ciInf h

theorem penaltyValue_nonneg (hlam : 0 ≤ lam) (x : X) :
    0 ≤ penaltyValue act chi lam eps x :=
  le_penaltyValue x fun w => wordCost_nonneg hlam x w

/-! ### The inverse gate -/

/-- The inverse assignment is an involution on the induced maps. -/
theorem act_inv_inv (hinvL : ∀ (g : Γ) (x : X), act (inv g) (act g x) = x)
    (g : Γ) (x : X) : act (inv (inv g)) x = act g x := by
  have h := hinvL (inv g) (act g x)
  rw [hinvL g x] at h
  exact h

theorem dist_act_left (hiso : ∀ g : Γ, Isometry (act g))
    (hinvL : ∀ (g : Γ) (x : X), act (inv g) (act g x) = x)
    (g : Γ) (x y : X) : dist x (act g y) = dist (act (inv g) x) y := by
  have h := (hiso (inv g)).dist_eq x (act g y)
  rw [hinvL g y] at h
  exact h.symm

theorem wordCost_cons (hiso : ∀ g : Γ, Isometry (act g))
    (hinvL : ∀ (g : Γ) (x : X), act (inv g) (act g x) = x)
    (x : X) (g : Γ) (w : List Γ) :
    wordCost act chi lam eps x (g :: w) =
      1 + wordCost act chi lam eps (act (inv g) x) w := by
  simp only [wordCost, wordAct_cons, List.length_cons, Nat.cast_add, Nat.cast_one,
    dist_act_left hiso hinvL g x (wordAct act w chi)]
  ring

/-! ### Lipschitz bound -/

theorem penaltyValue_le_add_dist (hlam : 0 ≤ lam) (x y : X) :
    penaltyValue act chi lam eps x ≤ penaltyValue act chi lam eps y + lam * dist x y := by
  have key : ∀ w : List Γ,
      penaltyValue act chi lam eps x - lam * dist x y ≤ wordCost act chi lam eps y w := by
    intro w
    have hstep : wordCost act chi lam eps x w ≤
        wordCost act chi lam eps y w + lam * dist x y := by
      have hd : dist x (wordAct act w chi) ≤ dist y (wordAct act w chi) + dist x y := by
        rw [dist_comm x y]
        exact dist_triangle_left _ _ _
      have hmax : max (dist x (wordAct act w chi) - eps) 0 ≤
          max (dist y (wordAct act w chi) - eps) 0 + dist x y := by
        rcases le_total (dist x (wordAct act w chi) - eps) 0 with h | h
        · rw [max_eq_right h]
          have : (0 : ℝ) ≤ max (dist y (wordAct act w chi) - eps) 0 := le_max_right _ _
          have : (0 : ℝ) ≤ dist x y := dist_nonneg
          positivity
        · rw [max_eq_left h]
          have h2 : dist y (wordAct act w chi) - eps ≤
              max (dist y (wordAct act w chi) - eps) 0 := le_max_left _ _
          linarith
      have := mul_le_mul_of_nonneg_left hmax hlam
      simp only [wordCost]
      nlinarith [this]
    have := penaltyValue_le_wordCost hlam x w
    linarith
  have := le_penaltyValue (act := act) (chi := chi) (lam := lam) (eps := eps) y key
  linarith

theorem lipschitzWith_penaltyValue (hlam : 0 ≤ lam) (x y : X) :
    |penaltyValue act chi lam eps x - penaltyValue act chi lam eps y| ≤ lam * dist x y := by
  have h₁ := penaltyValue_le_add_dist (act := act) (chi := chi) (eps := eps) hlam x y
  have h₂ := penaltyValue_le_add_dist (act := act) (chi := chi) (eps := eps) hlam y x
  rw [dist_comm y x] at h₂
  rw [abs_sub_le_iff]
  constructor <;> linarith

/-! ### Gate steps -/

theorem penaltyValue_le_one_add_inv (hlam : 0 ≤ lam)
    (hiso : ∀ g : Γ, Isometry (act g))
    (hinvL : ∀ (g : Γ) (x : X), act (inv g) (act g x) = x)
    (g : Γ) (x : X) :
    penaltyValue act chi lam eps x ≤ 1 + penaltyValue act chi lam eps (act (inv g) x) := by
  have key : ∀ w : List Γ,
      penaltyValue act chi lam eps x - 1 ≤ wordCost act chi lam eps (act (inv g) x) w := by
    intro w
    have h := penaltyValue_le_wordCost (act := act) (chi := chi) (eps := eps) hlam x (g :: w)
    rw [wordCost_cons hiso hinvL x g w] at h
    linarith
  have := le_penaltyValue (act := act) (chi := chi) (lam := lam) (eps := eps)
    (act (inv g) x) key
  linarith

theorem penaltyValue_le_one_add (hlam : 0 ≤ lam)
    (hiso : ∀ g : Γ, Isometry (act g))
    (hinvL : ∀ (g : Γ) (x : X), act (inv g) (act g x) = x)
    (g : Γ) (x : X) :
    penaltyValue act chi lam eps x ≤ 1 + penaltyValue act chi lam eps (act g x) := by
  have h := penaltyValue_le_one_add_inv (act := act) (chi := chi) (eps := eps)
    hlam hiso hinvL (inv g) x
  rwa [act_inv_inv hinvL g x] at h

/-- **Unit gate step.**  The exact-penalty value changes by at most one along any gate. -/
theorem abs_penaltyValue_act_sub_le_one (hlam : 0 ≤ lam)
    (hiso : ∀ g : Γ, Isometry (act g))
    (hinvL : ∀ (g : Γ) (x : X), act (inv g) (act g x) = x)
    (g : Γ) (x : X) :
    |penaltyValue act chi lam eps (act g x) - penaltyValue act chi lam eps x| ≤ 1 := by
  have h₁ : penaltyValue act chi lam eps (act g x) ≤
      1 + penaltyValue act chi lam eps x := by
    have h := penaltyValue_le_one_add_inv (act := act) (chi := chi) (eps := eps)
      hlam hiso hinvL g (act g x)
    rwa [hinvL g x] at h
  have h₂ := penaltyValue_le_one_add (act := act) (chi := chi) (eps := eps)
    hlam hiso hinvL g x
  rw [abs_sub_le_iff]
  constructor <;> linarith

/-! ### The Bellman equation -/

variable [Nonempty Γ]

theorem bddBelow_range_penaltyValue_inv (hlam : 0 ≤ lam) (x : X) :
    BddBelow (Set.range fun g : Γ => penaltyValue act chi lam eps (act (inv g) x)) := by
  refine ⟨0, ?_⟩
  rintro r ⟨g, rfl⟩
  exact penaltyValue_nonneg hlam _

/-- **Exact robust Bellman equation.** -/
theorem penaltyValue_eq_min (hlam : 0 ≤ lam)
    (hiso : ∀ g : Γ, Isometry (act g))
    (hinvL : ∀ (g : Γ) (x : X), act (inv g) (act g x) = x)
    (x : X) :
    penaltyValue act chi lam eps x =
      min (lam * max (dist x chi - eps) 0)
        (1 + ⨅ g : Γ, penaltyValue act chi lam eps (act (inv g) x)) := by
  refine le_antisymm (le_min ?_ ?_) ?_
  · have h := penaltyValue_le_wordCost (act := act) (chi := chi) (eps := eps) hlam x ([] : List Γ)
    simpa [wordCost] using h
  · have hle : ∀ g : Γ, penaltyValue act chi lam eps x - 1 ≤
        penaltyValue act chi lam eps (act (inv g) x) := by
      intro g
      have := penaltyValue_le_one_add_inv (act := act) (chi := chi) (eps := eps)
        hlam hiso hinvL g x
      linarith
    have := le_ciInf hle
    linarith
  · refine le_penaltyValue x ?_
    intro w
    cases w with
    | nil =>
        refine le_trans (min_le_left _ _) ?_
        simp [wordCost]
    | cons g w =>
        refine le_trans (min_le_right _ _) ?_
        rw [wordCost_cons hiso hinvL x g w]
        have h₁ : (⨅ g : Γ, penaltyValue act chi lam eps (act (inv g) x)) ≤
            penaltyValue act chi lam eps (act (inv g) x) :=
          ciInf_le (bddBelow_range_penaltyValue_inv hlam x) g
        have h₂ := penaltyValue_le_wordCost (act := act) (chi := chi) (eps := eps)
          hlam (act (inv g) x) w
        linarith

/-! ### Comparison with approximate complexity -/

theorem penaltyValue_le_of_reachable (hlam : 0 ≤ lam) (x : X) {c : ℕ}
    (h : ∃ w : List Γ, w.length ≤ c ∧ dist x (wordAct act w chi) ≤ eps) :
    penaltyValue act chi lam eps x ≤ (c : ℝ) := by
  obtain ⟨w, hw, hd⟩ := h
  have hcost : wordCost act chi lam eps x w = (w.length : ℝ) := by
    simp only [wordCost]
    rw [max_eq_right (by linarith), mul_zero, add_zero]
  have := penaltyValue_le_wordCost (act := act) (chi := chi) (eps := eps) hlam x w
  rw [hcost] at this
  exact this.trans (by exact_mod_cast hw)

/-! ### Maximal-subsolution duality -/

theorem IsBellmanSubsolution.le_wordCost
    {phi : X → ℝ} (hphi : IsBellmanSubsolution act inv chi lam eps phi)
    (hiso : ∀ g : Γ, Isometry (act g))
    (hinvL : ∀ (g : Γ) (x : X), act (inv g) (act g x) = x) :
    ∀ (w : List Γ) (x : X), phi x ≤ wordCost act chi lam eps x w := by
  intro w
  induction w with
  | nil => intro x; simpa [wordCost] using hphi.1 x
  | cons g w ih =>
      intro x
      have h₁ := hphi.2 g x
      have h₂ := ih (act (inv g) x)
      rw [wordCost_cons hiso hinvL x g w]
      linarith

theorem IsBellmanSubsolution.le_penaltyValue
    {phi : X → ℝ} (hphi : IsBellmanSubsolution act inv chi lam eps phi)
    (hiso : ∀ g : Γ, Isometry (act g))
    (hinvL : ∀ (g : Γ) (x : X), act (inv g) (act g x) = x) (x : X) :
    phi x ≤ penaltyValue act chi lam eps x :=
  le_penaltyValue x fun w => hphi.le_wordCost hiso hinvL w x

theorem isBellmanSubsolution_penaltyValue (hlam : 0 ≤ lam)
    (hiso : ∀ g : Γ, Isometry (act g))
    (hinvL : ∀ (g : Γ) (x : X), act (inv g) (act g x) = x) :
    IsBellmanSubsolution act inv chi lam eps (penaltyValue act chi lam eps) := by
  refine ⟨fun x => ?_, fun g x => ?_⟩
  · have h := penaltyValue_le_wordCost (act := act) (chi := chi) (eps := eps) hlam x ([] : List Γ)
    simpa [wordCost] using h
  · exact penaltyValue_le_one_add_inv (act := act) (chi := chi) (eps := eps) hlam hiso hinvL g x

/-- **Maximal-subsolution duality.**  The exact-penalty value is the largest value at `x` of a
Bellman subsolution, and it is itself one. -/
theorem penaltyValue_isGreatest (hlam : 0 ≤ lam)
    (hiso : ∀ g : Γ, Isometry (act g))
    (hinvL : ∀ (g : Γ) (x : X), act (inv g) (act g x) = x) (x : X) :
    IsGreatest {r : ℝ | ∃ phi : X → ℝ,
      IsBellmanSubsolution act inv chi lam eps phi ∧ phi x = r}
      (penaltyValue act chi lam eps x) := by
  refine ⟨⟨penaltyValue act chi lam eps,
    isBellmanSubsolution_penaltyValue hlam hiso hinvL, rfl⟩, ?_⟩
  rintro r ⟨phi, hphi, rfl⟩
  exact hphi.le_penaltyValue hiso hinvL x

/-- The same value is the largest one attained by a `lam`-Lipschitz Bellman subsolution. -/
theorem penaltyValue_isGreatest_lipschitz (hlam : 0 ≤ lam)
    (hiso : ∀ g : Γ, Isometry (act g))
    (hinvL : ∀ (g : Γ) (x : X), act (inv g) (act g x) = x) (x : X) :
    IsGreatest {r : ℝ | ∃ phi : X → ℝ,
      IsBellmanSubsolution act inv chi lam eps phi ∧
        (∀ u v : X, |phi u - phi v| ≤ lam * dist u v) ∧ phi x = r}
      (penaltyValue act chi lam eps x) := by
  refine ⟨⟨penaltyValue act chi lam eps,
    isBellmanSubsolution_penaltyValue hlam hiso hinvL,
    fun u v => lipschitzWith_penaltyValue (act := act) (chi := chi) (eps := eps) hlam u v, rfl⟩, ?_⟩
  rintro r ⟨phi, hphi, _, rfl⟩
  exact hphi.le_penaltyValue hiso hinvL x

end Value

/-! ## Compact gate families and exact penalty recovery -/

section Compact

variable {X : Type*} [MetricSpace X] {Γ : Type*} [TopologicalSpace Γ] [CompactSpace Γ]
variable {act : Γ → X → X} {chi : X} {eps : ℝ}

theorem reachSet_zero (act : Γ → X → X) (chi : X) : reachSet act chi 0 = {chi} := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    have : w = [] := List.length_eq_zero_iff.mp (Nat.le_zero.mp hw)
    simp [this]
  · rintro rfl
    exact mem_reachSet_self act chi 0

theorem reachSet_succ (act : Γ → X → X) (chi : X) (s : ℕ) :
    reachSet act chi (s + 1) =
      reachSet act chi s ∪
        (fun p : Γ × X => act p.1 p.2) '' (Set.univ ×ˢ reachSet act chi s) := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    cases w with
    | nil => exact Or.inl ⟨[], by simp, rfl⟩
    | cons g w =>
        refine Or.inr ⟨(g, wordAct act w chi), ?_, rfl⟩
        refine ⟨Set.mem_univ _, ⟨w, ?_, rfl⟩⟩
        simpa using Nat.succ_le_succ_iff.mp hw
  · rintro (⟨w, hw, rfl⟩ | ⟨⟨g, y⟩, ⟨-, ⟨w, hw, rfl⟩⟩, rfl⟩)
    · exact ⟨w, hw.trans (Nat.le_succ s), rfl⟩
    · exact ⟨g :: w, by simpa using Nat.succ_le_succ hw, rfl⟩

theorem isCompact_reachSet (hcont : Continuous fun p : Γ × X => act p.1 p.2)
    (chi : X) (s : ℕ) : IsCompact (reachSet act chi s) := by
  induction s with
  | zero => rw [reachSet_zero]; exact isCompact_singleton
  | succ s ih =>
      rw [reachSet_succ]
      exact ih.union ((isCompact_univ.prod ih).image hcont)

/-- On a compact gate family the layer distance is attained. -/
theorem exists_dist_eq_layerDist (hcont : Continuous fun p : Γ × X => act p.1 p.2)
    (chi : X) (s : ℕ) (x : X) :
    ∃ z ∈ reachSet act chi s, layerDist act chi s x = dist x z :=
  (isCompact_reachSet hcont chi s).exists_infDist_eq_dist (reachSet_nonempty act chi s) x

/-- Below the approximate complexity, every reachable layer stays strictly outside the slack
ball. -/
theorem lt_layerDist_of_lt_approxComplexity
    (hcont : Continuous fun p : Γ × X => act p.1 p.2) (chi : X) (eps : ℝ) (x : X)
    (hS : {s | ∃ w : List Γ, w.length ≤ s ∧ dist x (wordAct act w chi) ≤ eps}.Nonempty)
    {s : ℕ} (hs : s < approxComplexity act chi eps x) :
    eps < layerDist act chi s x := by
  obtain ⟨z, hz, hzeq⟩ := exists_dist_eq_layerDist hcont chi s x
  obtain ⟨w, hw, rfl⟩ := hz
  rw [hzeq]
  by_contra hcon
  have hmem : s ∈ {s | ∃ w : List Γ, w.length ≤ s ∧ dist x (wordAct act w chi) ≤ eps} :=
    ⟨w, hw, not_lt.mp hcon⟩
  exact absurd (Nat.sInf_le hmem) (not_le.mpr hs)

theorem layerDist_le_dist {chi : X} {s : ℕ} {x : X} {w : List Γ} (hw : w.length ≤ s) :
    layerDist act chi s x ≤ dist x (wordAct act w chi) :=
  Metric.infDist_le_dist_of_mem ⟨w, hw, rfl⟩

/-- **Finite exact-penalty recovery.**  Above an explicit finite penalty threshold the
exact-penalty value equals the approximate circuit complexity. -/
theorem penaltyValue_eq_approxComplexity
    {inv : Γ → Γ} {lam : ℝ} (hlam : 0 ≤ lam)
    (hcont : Continuous fun p : Γ × X => act p.1 p.2)
    (chi : X) (eps : ℝ) (x : X)
    (hS : {s | ∃ w : List Γ, w.length ≤ s ∧ dist x (wordAct act w chi) ≤ eps}.Nonempty)
    (hthr : ∀ s : ℕ, s < approxComplexity act chi eps x →
      ((approxComplexity act chi eps x : ℝ) - s) ≤ lam * (layerDist act chi s x - eps)) :
    penaltyValue act chi lam eps x = (approxComplexity act chi eps x : ℝ) := by
  classical
  set c := approxComplexity act chi eps x with hc
  have hcmem : c ∈ {s | ∃ w : List Γ, w.length ≤ s ∧ dist x (wordAct act w chi) ≤ eps} :=
    Nat.sInf_mem hS
  refine le_antisymm (penaltyValue_le_of_reachable hlam x hcmem) ?_
  refine le_penaltyValue x ?_
  intro w
  rcases le_or_gt (c : ℝ) (w.length : ℝ) with hlen | hlen
  · have hpos : 0 ≤ lam * max (dist x (wordAct act w chi) - eps) 0 :=
      mul_nonneg hlam (le_max_right _ _)
    simp only [wordCost]
    linarith
  · have hslt : w.length < c := by exact_mod_cast hlen
    have hlayer : eps < layerDist act chi w.length x :=
      lt_layerDist_of_lt_approxComplexity hcont chi eps x hS hslt
    have hdist : layerDist act chi w.length x ≤ dist x (wordAct act w chi) :=
      layerDist_le_dist le_rfl
    have hthr' := hthr w.length hslt
    have hmax : layerDist act chi w.length x - eps ≤
        max (dist x (wordAct act w chi) - eps) 0 :=
      le_trans (by linarith) (le_max_left _ _)
    have hmul : lam * (layerDist act chi w.length x - eps) ≤
        lam * max (dist x (wordAct act w chi) - eps) 0 :=
      mul_le_mul_of_nonneg_left hmax hlam
    simp only [wordCost]
    linarith

end Compact

/-! ## The calibration-singularity condition number -/

section Calibration

variable {X : Type*} [MetricSpace X]

/-- **Certificate condition number.**  A Lipschitz certificate normalised at the reference point
and reaching value `c` at `x` must have Lipschitz constant at least `c / d(x, χ)`. -/
theorem le_lipschitzConstant_of_certificate {chi x : X} {phi : X → ℝ} {lam c : ℝ}
    (hlip : ∀ u v : X, phi u - phi v ≤ lam * dist u v)
    (hnorm : phi chi ≤ 0) (hval : c ≤ phi x) :
    c ≤ lam * dist x chi := by
  have h := hlip x chi
  linarith

/-- Linear-in-time approach to the reference point turns the condition number into an inverse
time divergence. -/
theorem le_mul_lipschitzConstant_of_certificate_of_linear_approach
    {chi x : X} {phi : X → ℝ} {lam c v t : ℝ}
    (hlip : ∀ u v : X, phi u - phi v ≤ lam * dist u v)
    (hnorm : phi chi ≤ 0) (hval : c ≤ phi x)
    (hspeed : dist x chi ≤ v * |t|) (hlam : 0 ≤ lam) :
    c ≤ lam * (v * |t|) := by
  have h := le_lipschitzConstant_of_certificate hlip hnorm hval
  have : lam * dist x chi ≤ lam * (v * |t|) := mul_le_mul_of_nonneg_left hspeed hlam
  linarith

end Calibration

end HTGeometry
