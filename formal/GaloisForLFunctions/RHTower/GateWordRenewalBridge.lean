import GaloisForLFunctions.RHTower.DiscreteMarkovRenewal
import GaloisForLFunctions.RHTower.GateWordFirstHit

/-!
# The gate-word walk as a discounted Markov renewal chain

A finite gate alphabet acting on a state space generates a right random walk on words: the state
after `ℓ` uniform letters is the word read so far, and a target set of states pulls back to a target
set of words.  This walk is a time-homogeneous Markov chain whose transition law appends a uniform
letter.

Its discounted first-entrance mass is exactly the prefix-free first-hit partition function of the
gate language, because the only paths of positive weight are the canonical prefix chains of words.
Consequently the entrance--return resolvent law of the Markov renewal theory applies verbatim to
gate-word synthesis, and the discounted first-hit mass inherits the Neumann decomposition into
preparation and recurrence.
-/

open scoped ENNReal

set_option linter.unusedSectionVars false

namespace GaloisForLFunctions.RHTower

section GateChain

variable {Γ : Type*} [Fintype Γ] [DecidableEq Γ]

/-- The uniform right-extension transition law on words. -/
noncomputable def gateKernel (Γ : Type*) [Fintype Γ] [DecidableEq Γ] :
    List Γ → List Γ → ℝ≥0∞ :=
  fun u v => if ∃ g : Γ, v = u ++ [g] then ((Fintype.card Γ : ℝ≥0∞))⁻¹ else 0

theorem gateKernel_append (u : List Γ) (g : Γ) :
    gateKernel Γ u (u ++ [g]) = ((Fintype.card Γ : ℝ≥0∞))⁻¹ := by
  rw [gateKernel, if_pos ⟨g, rfl⟩]

theorem gateKernel_eq_zero {u v : List Γ} (h : ∀ g : Γ, v ≠ u ++ [g]) :
    gateKernel Γ u v = 0 := by
  rw [gateKernel, if_neg (by rintro ⟨g, rfl⟩; exact h g rfl)]

theorem gateKernel_ne_zero {u v : List Γ} (h : gateKernel Γ u v ≠ 0) :
    ∃ g : Γ, v = u ++ [g] := by
  by_contra hc
  exact h (gateKernel_eq_zero (by simpa using not_exists.mp hc))

/-- The uniform right-extension law is a probability transition law. -/
theorem tsum_gateKernel [Nonempty Γ] (u : List Γ) :
    (∑' v : List Γ, gateKernel Γ u v) = 1 := by
  classical
  have hinj : Function.Injective (fun g : Γ => u ++ [g]) := by
    intro g g' h
    simpa using h
  have hsupp : Function.support (gateKernel Γ u) ⊆ Set.range (fun g : Γ => u ++ [g]) := by
    intro v hv
    obtain ⟨g, rfl⟩ := gateKernel_ne_zero hv
    exact ⟨g, rfl⟩
  rw [← hinj.tsum_eq hsupp]
  have hval : ∀ g : Γ, gateKernel Γ u (u ++ [g]) = ((Fintype.card Γ : ℝ≥0∞))⁻¹ :=
    fun g => gateKernel_append u g
  rw [tsum_congr hval, tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  refine ENNReal.mul_inv_cancel ?_ (ENNReal.natCast_ne_top _)
  simp

/-- The canonical path of the gate chain: reading the letters of `w` from the state `u`. -/
def gatePath : List Γ → List Γ → List (List Γ)
  | _, [] => []
  | u, g :: w => (u ++ [g]) :: gatePath (u ++ [g]) w

@[simp] theorem gatePath_nil (u : List Γ) : gatePath u ([] : List Γ) = [] := rfl

@[simp] theorem gatePath_cons (u : List Γ) (g : Γ) (w : List Γ) :
    gatePath u (g :: w) = (u ++ [g]) :: gatePath (u ++ [g]) w := rfl

@[simp] theorem gatePath_length (u w : List Γ) : (gatePath u w).length = w.length := by
  induction w generalizing u with
  | nil => simp
  | cons g w ih => simp [ih]

@[simp] theorem pathEnd_gatePath (u w : List Γ) : pathEnd u (gatePath u w) = u ++ w := by
  induction w generalizing u with
  | nil => simp
  | cons g w ih => simp [ih (u ++ [g])]

theorem pathWeight_gatePath (u w : List Γ) :
    pathWeight (gateKernel Γ) u (gatePath u w) = ((Fintype.card Γ : ℝ≥0∞))⁻¹ ^ w.length := by
  induction w generalizing u with
  | nil => simp
  | cons g w ih => rw [gatePath_cons, pathWeight_cons, gateKernel_append, ih, List.length_cons,
      pow_succ, mul_comm]

theorem gatePath_take (u w : List Γ) (k : ℕ) :
    (gatePath u w).take k = gatePath u (w.take k) := by
  induction w generalizing u k with
  | nil => simp
  | cons g w ih =>
    cases k with
    | zero => simp
    | succ k => simp [ih (u ++ [g]) k]

theorem gatePath_injective (u : List Γ) : Function.Injective (gatePath u) := by
  intro w w' h
  have := congrArg (pathEnd u) h
  rw [pathEnd_gatePath, pathEnd_gatePath] at this
  exact List.append_cancel_left this

/-- Every path of positive weight for the gate chain is a canonical word path. -/
theorem exists_gatePath_of_pathWeight_ne_zero {u : List Γ} {l : List (List Γ)}
    (h : pathWeight (gateKernel Γ) u l ≠ 0) : ∃ w : List Γ, l = gatePath u w := by
  induction l generalizing u with
  | nil => exact ⟨[], rfl⟩
  | cons v l ih =>
    rw [pathWeight_cons] at h
    have hk : gateKernel Γ u v ≠ 0 := fun hc => h (by rw [hc, zero_mul])
    obtain ⟨g, rfl⟩ := gateKernel_ne_zero hk
    obtain ⟨w, rfl⟩ := ih (u := u ++ [g]) (fun hc => h (by rw [hc, mul_zero]))
    exact ⟨g :: w, rfl⟩

end GateChain

section Bridge

variable {Γ : Type*} [Fintype Γ] [DecidableEq Γ] [Nonempty Γ] {X : Type*}

/-- The pullback of a state target along gate-word evaluation. -/
def wordTarget (act : Γ → X → X) (χ : X) (A : Set X) : Set (List Γ) :=
  {w : List Γ | wordEval act w χ ∈ A}

theorem firstEntrance_gatePath_iff (act : Γ → X → X) (χ : X) (A : Set X) (w : List Γ) :
    FirstEntrance (wordTarget act χ A) [] (gatePath [] w) ↔ FirstHitWord act χ A w := by
  constructor
  · rintro ⟨hend, hmin⟩
    refine ⟨by simpa [wordTarget] using hend, fun k hk hmem => ?_⟩
    refine hmin k (by simpa using hk) ?_
    rw [gatePath_take, pathEnd_gatePath]
    simpa [wordTarget] using hmem
  · rintro ⟨hend, hmin⟩
    refine ⟨by simpa [wordTarget] using hend, fun k hk hmem => ?_⟩
    rw [gatePath_take, pathEnd_gatePath] at hmem
    exact hmin k (by simpa using hk) (by simpa [wordTarget] using hmem)

/-- **Prefix-free first-hit partition function.**  The discounted first-entrance mass of the
uniform gate walk into the pullback target is the discounted sum over the prefix-free first-hit
language. -/
theorem entranceMass_gateKernel_eq_firstHitMass (act : Γ → X → X) (χ : X) (A : Set X)
    (a : ℝ≥0∞) :
    entranceMass (gateKernel Γ) a (wordTarget act χ A) [] (wordTarget act χ A) =
      firstHitMass act χ A a := by
  classical
  set T : Set (List Γ) := wordTarget act χ A with hT
  set F : List (List Γ) → ℝ≥0∞ := fun l =>
    Set.indicator {l : List (List Γ) | FirstEntrance T [] l ∧ pathEnd ([] : List Γ) l ∈ T}
      (fun l => a ^ l.length * pathWeight (gateKernel Γ) [] l) l with hF
  have hsupp : Function.support F ⊆ Set.range (gatePath ([] : List Γ)) := by
    intro l hl
    have hne : F l ≠ 0 := hl
    by_cases hmem : l ∈ {l : List (List Γ) | FirstEntrance T [] l ∧ pathEnd ([] : List Γ) l ∈ T}
    · simp only [hF, Set.indicator_of_mem hmem] at hne
      have hw : pathWeight (gateKernel Γ) [] l ≠ 0 := fun hc => hne (by rw [hc, mul_zero])
      obtain ⟨w, rfl⟩ := exists_gatePath_of_pathWeight_ne_zero hw
      exact ⟨w, rfl⟩
    · exact absurd (by simp only [hF, Set.indicator_of_notMem hmem]) hne
  have hbridge : ∀ w : List Γ, F (gatePath [] w) =
      Set.indicator {w : List Γ | FirstHitWord act χ A w}
        (fun w => (a / Fintype.card Γ) ^ w.length) w := by
    intro w
    by_cases hw : FirstHitWord act χ A w
    · have hmem : gatePath ([] : List Γ) w ∈
          {l : List (List Γ) | FirstEntrance T [] l ∧ pathEnd ([] : List Γ) l ∈ T} := by
        have hfe : FirstEntrance T [] (gatePath [] w) :=
          (firstEntrance_gatePath_iff act χ A w).mpr hw
        exact ⟨hfe, hfe.1⟩
      simp only [hF]
      rw [Set.indicator_of_mem hmem,
        Set.indicator_of_mem (show w ∈ {w : List Γ | FirstHitWord act χ A w} from hw),
        gatePath_length, pathWeight_gatePath, div_eq_mul_inv, mul_pow]
    · have hmem : gatePath ([] : List Γ) w ∉
          {l : List (List Γ) | FirstEntrance T [] l ∧ pathEnd ([] : List Γ) l ∈ T} := by
        intro hc
        exact hw ((firstEntrance_gatePath_iff act χ A w).mp hc.1)
      simp only [hF]
      rw [Set.indicator_of_notMem hmem,
        Set.indicator_of_notMem (show w ∉ {w : List Γ | FirstHitWord act χ A w} from hw)]
  rw [entranceMass, ← (gatePath_injective ([] : List Γ)).tsum_eq hsupp, firstHitMass]
  exact tsum_congr hbridge

/-- **Gate-word entrance--return resolvent law.**  Below the dependence radius the discounted
occupation of the pullback target by the gate walk is the discounted first-hit mass composed with
the Neumann resolvent of the discounted return kernel. -/
theorem greenMass_gateKernel_eq_tsum_returnIterate (act : Γ → X → X) (χ : X) (A : Set X)
    {a : ℝ≥0∞} (ha : a < 1) :
    greenMass (gateKernel Γ) a [] (wordTarget act χ A) =
      ∑' k : ℕ, ∑' z : List Γ,
        entranceMass (gateKernel Γ) a (wordTarget act χ A) [] {z} *
          returnIterate (gateKernel Γ) a (wordTarget act χ A) k z (wordTarget act χ A) :=
  greenMass_eq_tsum_entranceMass_mul_returnIterate (gateKernel Γ) (tsum_gateKernel)
    ha (subset_refl _) []

/-- **Gate-word preparation--recurrence sandwich.**  The discounted occupation of the pullback
target is squeezed between the first-hit mass and its geometric multiple. -/
theorem firstHitMass_le_greenMass_le (act : Γ → X → X) (χ : X) (A : Set X) (a : ℝ≥0∞) :
    firstHitMass act χ A a ≤ greenMass (gateKernel Γ) a [] (wordTarget act χ A) ∧
      greenMass (gateKernel Γ) a [] (wordTarget act χ A) ≤
        (∑' n : ℕ, a ^ n) * firstHitMass act χ A a := by
  have h := entranceMass_le_greenMass_le (gateKernel Γ) (tsum_gateKernel) a
    (wordTarget act χ A) []
  rw [entranceMass_gateKernel_eq_firstHitMass act χ A a] at h
  exact h

/-- **First-letter recursion.**  Off the target the discounted first-hit mass decomposes over the
first synthesis letter and the pulled-back targets. -/
theorem firstHitMass_recursion (act : Γ → X → X) (χ : X) (A : Set X) (hχ : χ ∉ A) (a : ℝ≥0∞) :
    firstHitMass act χ A a =
      (a / Fintype.card Γ) * ∑ g : Γ, firstHitMass act χ {x | act g x ∈ A} a := by
  classical
  have hiff : ∀ (g : Γ) (w : List Γ),
      FirstHitWord act χ A (g :: w) ↔ FirstHitWord act χ {x | act g x ∈ A} w := by
    intro g w
    constructor
    · rintro ⟨hend, hmin⟩
      refine ⟨hend, fun k hk hmem => ?_⟩
      refine hmin (k + 1) (by simpa using hk) ?_
      have hcons : (g :: w).take (k + 1) = g :: w.take k := by simp
      rw [hcons]
      exact hmem
    · rintro ⟨hend, hmin⟩
      refine ⟨hend, fun k hk hmem => ?_⟩
      cases k with
      | zero => exact hχ (by simpa using hmem)
      | succ j =>
        have hcons : (g :: w).take (j + 1) = g :: w.take j := by simp
        rw [hcons] at hmem
        exact hmin j (by simpa using hk) hmem
  have hterm : ∀ p : Γ × List Γ,
      Set.indicator {w : List Γ | FirstHitWord act χ A w}
        (fun w => (a / Fintype.card Γ) ^ w.length) (p.1 :: p.2) =
      (a / Fintype.card Γ) * Set.indicator {w : List Γ | FirstHitWord act χ {x | act p.1 x ∈ A} w}
        (fun w => (a / Fintype.card Γ) ^ w.length) p.2 := by
    rintro ⟨g, w⟩
    by_cases hw : FirstHitWord act χ {x | act g x ∈ A} w
    · rw [Set.indicator_of_mem (show (g :: w) ∈ {w : List Γ | FirstHitWord act χ A w} from
        (hiff g w).mpr hw), Set.indicator_of_mem
        (show w ∈ {w : List Γ | FirstHitWord act χ {x | act g x ∈ A} w} from hw),
        List.length_cons, pow_succ, mul_comm]
    · rw [Set.indicator_of_notMem (show (g :: w) ∉ {w : List Γ | FirstHitWord act χ A w} from
        fun hc => hw ((hiff g w).mp hc)), Set.indicator_of_notMem
        (show w ∉ {w : List Γ | FirstHitWord act χ {x | act g x ∈ A} w} from hw), mul_zero]
  have hnil : Set.indicator {w : List Γ | FirstHitWord act χ A w}
      (fun w => (a / Fintype.card Γ) ^ w.length) [] = 0 := by
    refine Set.indicator_of_notMem (fun hc => ?_) _
    exact hχ (by simpa using hc.1)
  have hprod : (∑' i : Γ × List Γ,
      Set.indicator {w : List Γ | FirstHitWord act χ {x | act i.1 x ∈ A} w}
        (fun w => (a / Fintype.card Γ) ^ w.length) i.2) =
      ∑' g : Γ, ∑' w : List Γ,
        Set.indicator {w : List Γ | FirstHitWord act χ {x | act g x ∈ A} w}
          (fun w => (a / Fintype.card Γ) ^ w.length) w :=
    ENNReal.tsum_prod (f := fun g w =>
      Set.indicator {w : List Γ | FirstHitWord act χ {x | act g x ∈ A} w}
        (fun w => (a / Fintype.card Γ) ^ w.length) w)
  rw [firstHitMass, tsum_list_split, hnil, zero_add, tsum_congr hterm, ENNReal.tsum_mul_left,
    hprod, tsum_fintype]
  rfl


end Bridge

end GaloisForLFunctions.RHTower
