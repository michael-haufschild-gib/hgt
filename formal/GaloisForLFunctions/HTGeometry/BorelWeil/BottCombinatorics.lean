import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Data.Fintype.Prod

/-!
# The dot action and the combinatorics of Bott's theorem

Bott's theorem is governed by the `ρ`-shifted action `w · λ = w(λ + ρ) − ρ` of the Weyl group on
weights.  For `GL(N)` the Weyl group is the symmetric group and `ρ i = N − 1 − i`, so a weight is
*regular* exactly when `λ + ρ` has distinct entries, and then exactly one Weyl element makes it
dominant.  The degree in which the cohomology of `L_λ` is concentrated is the Coxeter length of that
element, that is, its number of inversions.

## Main definitions

* `rhoWeight`, `dotAction`, `IsRegularWeight`
* `inversions`, `permLength` — the Coxeter length of a permutation.

## Main results

* `dotAction_dotAction` — the dot action is an action.
* `exists_dotAction_antitone`, `dotAction_antitone_unique` — a regular weight has exactly one
  dominant conjugate.
* `permLength_eq_zero_iff` — only the identity has no inversions.
-/

set_option linter.unusedSectionVars false

namespace GaloisForLFunctions.HTGeometry.BorelWeil

variable {N : ℕ}

/-- The half sum of the positive roots of `GL(N)`, as a weight: `ρ i = N - 1 - i`. -/
def rhoWeight (N : ℕ) : Fin N → ℤ := fun i => (N : ℤ) - 1 - (i : ℤ)

theorem rhoWeight_strictAnti : StrictAnti (rhoWeight N) := by
  intro i j hij
  have hcast : (i : ℤ) < (j : ℤ) := by exact_mod_cast hij
  simp only [rhoWeight]
  omega

/-- The `ρ`-shifted (dot) action of the Weyl group on integer weights. -/
def dotAction (w : Equiv.Perm (Fin N)) (lam : Fin N → ℤ) : Fin N → ℤ :=
  fun i => lam (w.symm i) + rhoWeight N (w.symm i) - rhoWeight N i

theorem dotAction_add_rhoWeight (w : Equiv.Perm (Fin N)) (lam : Fin N → ℤ) (i : Fin N) :
    dotAction w lam i + rhoWeight N i = lam (w.symm i) + rhoWeight N (w.symm i) := by
  rw [dotAction]
  ring

@[simp] theorem dotAction_one (lam : Fin N → ℤ) : dotAction 1 lam = lam := by
  funext i
  have hone : (1 : Equiv.Perm (Fin N)).symm i = i := rfl
  rw [dotAction, hone]
  omega

theorem dotAction_dotAction (w v : Equiv.Perm (Fin N)) (lam : Fin N → ℤ) :
    dotAction w (dotAction v lam) = dotAction (w * v) lam := by
  funext i
  rw [dotAction, dotAction, dotAction]
  have hsymm : (w * v).symm i = v.symm (w.symm i) := rfl
  rw [hsymm]
  ring

/-- A weight is regular when `λ + ρ` has distinct entries. -/
def IsRegularWeight (lam : Fin N → ℤ) : Prop :=
  Function.Injective fun i => lam i + rhoWeight N i

theorem isRegularWeight_dotAction {lam : Fin N → ℤ} (w : Equiv.Perm (Fin N)) :
    IsRegularWeight (dotAction w lam) ↔ IsRegularWeight lam := by
  have hfun : (fun i => dotAction w lam i + rhoWeight N i)
      = (fun i => lam i + rhoWeight N i) ∘ w.symm := by
    funext i
    exact dotAction_add_rhoWeight w lam i
  rw [IsRegularWeight, hfun, IsRegularWeight]
  constructor
  · intro h x y hxy
    have hx : ((fun i => lam i + rhoWeight N i) ∘ w.symm) (w x)
        = ((fun i => lam i + rhoWeight N i) ∘ w.symm) (w y) := by
      simp only [Function.comp_apply, Equiv.symm_apply_apply]
      exact hxy
    have := h hx
    simpa using this
  · exact fun h => h.comp w.symm.injective

/-- A strictly decreasing integer tuple decreases by at least the index gap. -/
theorem strictAnti_int_gap {f : Fin N → ℤ} (hf : StrictAnti f) :
    ∀ (d : ℕ) (i j : Fin N), (j : ℕ) = (i : ℕ) + d → f j + (d : ℤ) ≤ f i := by
  intro d
  induction d with
  | zero =>
    intro i j hji
    have hji' : j = i := Fin.ext (by omega)
    rw [hji']
    simp
  | succ e IH =>
    intro i j hji
    have hlt : (i : ℕ) + e < N := by omega
    have hIH := IH i ⟨(i : ℕ) + e, hlt⟩ rfl
    have hstep : f j < f ⟨(i : ℕ) + e, hlt⟩ := by
      refine hf ?_
      rw [Fin.lt_def, Fin.val_mk]
      omega
    omega

/-- The permutation putting a tuple in decreasing order. -/
noncomputable def sortDescPerm (v : Fin N → ℤ) : Equiv.Perm (Fin N) :=
  Fin.revPerm.trans (Tuple.sort v)

theorem antitone_comp_sortDescPerm (v : Fin N → ℤ) : Antitone (v ∘ sortDescPerm v) := by
  intro i j hij
  exact Tuple.monotone_sort v (Fin.rev_le_rev.2 hij)

/-- A strictly decreasing shifted weight gives a dominant dot action. -/
theorem dotAction_antitone_of_strictAnti {lam : Fin N → ℤ} {w : Equiv.Perm (Fin N)}
    (hw : StrictAnti fun i => lam (w.symm i) + rhoWeight N (w.symm i)) :
    Antitone (dotAction w lam) := by
  intro i j hij
  rcases eq_or_lt_of_le hij with rfl | hlt
  · exact le_rfl
  · have hij' : (i : ℕ) < (j : ℕ) := hlt
    have hgap := strictAnti_int_gap hw ((j : ℕ) - (i : ℕ)) i j (by omega)
    have hgap' : lam (w.symm j) + rhoWeight N (w.symm j) + (((j : ℕ) - (i : ℕ) : ℕ) : ℤ)
        ≤ lam (w.symm i) + rhoWeight N (w.symm i) := hgap
    have hrho : rhoWeight N i - rhoWeight N j = ((j : ℕ) : ℤ) - ((i : ℕ) : ℤ) := by
      simp only [rhoWeight]
      ring
    have hcast : (((j : ℕ) - (i : ℕ) : ℕ) : ℤ) = ((j : ℕ) : ℤ) - ((i : ℕ) : ℤ) := by omega
    rw [hcast] at hgap'
    show lam (w.symm j) + rhoWeight N (w.symm j) - rhoWeight N j
      ≤ lam (w.symm i) + rhoWeight N (w.symm i) - rhoWeight N i
    linarith [hgap', hrho]

/-- **Existence of the dominant conjugate.**  A regular weight is made dominant by some Weyl
element. -/
theorem exists_dotAction_antitone {lam : Fin N → ℤ} (h : IsRegularWeight lam) :
    ∃ w : Equiv.Perm (Fin N), Antitone (dotAction w lam) := by
  classical
  refine ⟨(sortDescPerm fun i => lam i + rhoWeight N i)⁻¹, ?_⟩
  refine dotAction_antitone_of_strictAnti ?_
  have hfun : (fun i => lam (((sortDescPerm fun i => lam i + rhoWeight N i)⁻¹).symm i)
        + rhoWeight N (((sortDescPerm fun i => lam i + rhoWeight N i)⁻¹).symm i))
      = (fun i => lam i + rhoWeight N i) ∘ (sortDescPerm fun i => lam i + rhoWeight N i) := rfl
  rw [hfun]
  exact (antitone_comp_sortDescPerm _).strictAnti_of_injective
    (h.comp (sortDescPerm _).injective)

theorem strictAnti_of_dotAction_antitone {lam : Fin N → ℤ} {w : Equiv.Perm (Fin N)}
    (hw : Antitone (dotAction w lam)) :
    StrictAnti fun i => lam (w.symm i) + rhoWeight N (w.symm i) := by
  intro i j hij
  show lam (w.symm j) + rhoWeight N (w.symm j) < lam (w.symm i) + rhoWeight N (w.symm i)
  have h1 := dotAction_add_rhoWeight w lam i
  have h2 := dotAction_add_rhoWeight w lam j
  have h3 : dotAction w lam j ≤ dotAction w lam i := hw hij.le
  have hrho : rhoWeight N j < rhoWeight N i := rhoWeight_strictAnti hij
  omega

/-- A strictly monotone permutation of `Fin N` is the identity. -/
theorem eq_one_of_strictMono {π : Equiv.Perm (Fin N)} (hπ : StrictMono (π : Fin N → Fin N)) :
    π = 1 := by
  have hinv : StrictMono ((π.symm : Fin N → Fin N)) := by
    intro i j hij
    by_contra hcon
    have hle : π.symm j ≤ π.symm i := le_of_not_gt hcon
    rcases eq_or_lt_of_le hle with heq | hlt
    · exact absurd (π.symm.injective heq) (ne_of_gt hij)
    · have hlt' := hπ hlt
      simp only [Equiv.apply_symm_apply] at hlt'
      exact absurd hlt' (not_lt_of_gt hij)
  refine Equiv.ext fun i => ?_
  have h1 : i ≤ π i := StrictMono.le_apply hπ
  have h2 : i ≤ π.symm i := StrictMono.le_apply hinv
  have h3 : π i ≤ i := by
    have hmono := hπ.monotone h2
    simpa using hmono
  exact le_antisymm h3 h1

/-- **Uniqueness of the dominant conjugate.** -/
theorem dotAction_antitone_unique {lam : Fin N → ℤ}
    {w w' : Equiv.Perm (Fin N)} (hw : Antitone (dotAction w lam))
    (hw' : Antitone (dotAction w' lam)) : w = w' := by
  classical
  have hs : StrictAnti fun i => lam (w.symm i) + rhoWeight N (w.symm i) :=
    strictAnti_of_dotAction_antitone hw
  have hs' : StrictAnti fun i => lam (w'.symm i) + rhoWeight N (w'.symm i) :=
    strictAnti_of_dotAction_antitone hw'
  have hstrict : StrictMono (((w.symm)⁻¹ * w'.symm : Equiv.Perm (Fin N)) : Fin N → Fin N) := by
    intro i j hij
    have hval : ∀ x : Fin N,
        lam (w.symm (((w.symm)⁻¹ * w'.symm : Equiv.Perm (Fin N)) x))
            + rhoWeight N (w.symm (((w.symm)⁻¹ * w'.symm : Equiv.Perm (Fin N)) x))
          = lam (w'.symm x) + rhoWeight N (w'.symm x) := by
      intro x
      have : w.symm (((w.symm)⁻¹ * w'.symm : Equiv.Perm (Fin N)) x) = w'.symm x := by
        show w.symm ((w.symm)⁻¹ (w'.symm x)) = w'.symm x
        simp
      rw [this]
    have hlt : lam (w.symm (((w.symm)⁻¹ * w'.symm : Equiv.Perm (Fin N)) j))
          + rhoWeight N (w.symm (((w.symm)⁻¹ * w'.symm : Equiv.Perm (Fin N)) j))
        < lam (w.symm (((w.symm)⁻¹ * w'.symm : Equiv.Perm (Fin N)) i))
          + rhoWeight N (w.symm (((w.symm)⁻¹ * w'.symm : Equiv.Perm (Fin N)) i)) := by
      rw [hval i, hval j]
      exact hs' hij
    exact (StrictAnti.lt_iff_gt hs).mp hlt
  have hone := eq_one_of_strictMono hstrict
  have hsymm : w.symm = w'.symm := by
    have := congrArg (fun π : Equiv.Perm (Fin N) => w.symm * π) hone
    simpa [mul_assoc] using this.symm
  have hfin := congrArg Equiv.symm hsymm
  rwa [Equiv.symm_symm, Equiv.symm_symm] at hfin

/-- The inversions of a permutation. -/
def inversions (w : Equiv.Perm (Fin N)) : Finset (Fin N × Fin N) :=
  Finset.univ.filter fun p => p.1 < p.2 ∧ w p.2 < w p.1

/-- The Coxeter length of a permutation: its number of inversions. -/
def permLength (w : Equiv.Perm (Fin N)) : ℕ := (inversions w).card

@[simp] theorem permLength_one : permLength (1 : Equiv.Perm (Fin N)) = 0 := by
  classical
  rw [permLength, inversions, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  rintro ⟨i, j⟩ -
  simp only [Equiv.Perm.coe_one, id_eq, not_and, not_lt]
  exact fun hij => hij.le

theorem permLength_eq_zero_iff {w : Equiv.Perm (Fin N)} : permLength w = 0 ↔ w = 1 := by
  classical
  constructor
  · intro h
    refine eq_one_of_strictMono ?_
    intro i j hij
    rw [permLength, Finset.card_eq_zero, inversions, Finset.filter_eq_empty_iff] at h
    have := h (x := (i, j)) (Finset.mem_univ _)
    simp only [not_and, not_lt] at this
    exact lt_of_le_of_ne (this hij) (fun hcon => absurd (w.injective hcon) (ne_of_lt hij))
  · intro h
    rw [h, permLength_one]

end GaloisForLFunctions.HTGeometry.BorelWeil

namespace GaloisForLFunctions.HTGeometry.BorelWeil

variable {N : ℕ}

/-- The simple reflection exchanging `i` and `i + 1`. -/
def swapNext (i : Fin N) (hi : (i : ℕ) + 1 < N) : Equiv.Perm (Fin N) :=
  Equiv.swap i ⟨(i : ℕ) + 1, hi⟩

theorem rhoWeight_succ (i : Fin N) (hi : (i : ℕ) + 1 < N) :
    rhoWeight N ⟨(i : ℕ) + 1, hi⟩ = rhoWeight N i - 1 := by
  simp only [rhoWeight]
  push_cast
  ring

theorem swapNext_symm (i : Fin N) (hi : (i : ℕ) + 1 < N) :
    (swapNext i hi).symm = swapNext i hi := rfl

theorem dotAction_swapNext_self (lam : Fin N → ℤ) (i : Fin N) (hi : (i : ℕ) + 1 < N) :
    dotAction (swapNext i hi) lam i = lam ⟨(i : ℕ) + 1, hi⟩ - 1 := by
  rw [dotAction, swapNext_symm, swapNext, Equiv.swap_apply_left, rhoWeight_succ]
  ring

theorem dotAction_swapNext_succ (lam : Fin N → ℤ) (i : Fin N) (hi : (i : ℕ) + 1 < N) :
    dotAction (swapNext i hi) lam ⟨(i : ℕ) + 1, hi⟩ = lam i + 1 := by
  rw [dotAction, swapNext_symm, swapNext, Equiv.swap_apply_right, rhoWeight_succ]
  ring

theorem dotAction_swapNext_other (lam : Fin N → ℤ) (i : Fin N) (hi : (i : ℕ) + 1 < N) {j : Fin N}
    (hj1 : j ≠ i) (hj2 : j ≠ ⟨(i : ℕ) + 1, hi⟩) :
    dotAction (swapNext i hi) lam j = lam j := by
  rw [dotAction, swapNext_symm, swapNext, Equiv.swap_apply_of_ne_of_ne hj1 hj2]
  ring

/-- **A singular weight has an adjacent pair on which the dot action drops by one.**  This is the
configuration that makes the rank-one cohomology vanish in both degrees. -/
theorem exists_dotAction_adjacent_eq {lam : Fin N → ℤ} (h : ¬ IsRegularWeight lam) :
    ∃ (w : Equiv.Perm (Fin N)) (i : Fin N) (hi : (i : ℕ) + 1 < N),
      dotAction w lam i - dotAction w lam ⟨(i : ℕ) + 1, hi⟩ = -1 := by
  classical
  rw [IsRegularWeight, Function.Injective] at h
  push Not at h
  obtain ⟨p, q, hpq, hne⟩ := h
  have hN : 1 < N := by
    have h1 : (p : ℕ) < N := p.isLt
    have h2 : (q : ℕ) < N := q.isLt
    have h3 : (p : ℕ) ≠ (q : ℕ) := fun hc => hne (Fin.ext hc)
    omega
  have hN0 : 0 < N := by omega
  set z : Fin N := ⟨0, hN0⟩ with hz
  set o : Fin N := ⟨1, hN⟩ with ho
  have hzo : z ≠ o := by
    intro hcon
    have := congrArg (Fin.val) hcon
    simp only [hz, ho] at this
    omega
  set t : Equiv.Perm (Fin N) := Equiv.swap z p with ht
  have htq : t.symm q ≠ z := by
    intro hcon
    have : q = t z := by
      rw [← hcon]
      exact (Equiv.apply_symm_apply t q).symm
    rw [ht, Equiv.swap_apply_left] at this
    exact hne this.symm
  set σ : Equiv.Perm (Fin N) := (Equiv.swap o (t.symm q)).trans t with hσ
  have hσz : σ z = p := by
    rw [hσ, Equiv.trans_apply, Equiv.swap_apply_of_ne_of_ne hzo (Ne.symm htq), ht,
      Equiv.swap_apply_left]
  have hσo : σ o = q := by
    rw [hσ, Equiv.trans_apply, Equiv.swap_apply_left, Equiv.apply_symm_apply]
  refine ⟨σ⁻¹, z, by omega, ?_⟩
  have hsymm : (σ⁻¹).symm = σ := rfl
  have hzsucc : (⟨(z : ℕ) + 1, by omega⟩ : Fin N) = o := Fin.ext (by simp [hz, ho])
  have h1 : dotAction σ⁻¹ lam z + rhoWeight N z = lam p + rhoWeight N p := by
    rw [dotAction_add_rhoWeight, hsymm, hσz]
  have h2 : dotAction σ⁻¹ lam o + rhoWeight N o = lam q + rhoWeight N q := by
    rw [dotAction_add_rhoWeight, hsymm, hσo]
  have hmu : lam p + rhoWeight N p = lam q + rhoWeight N q := hpq
  have hrho : rhoWeight N o = rhoWeight N z - 1 := by
    simp only [rhoWeight, hz, ho]
    push_cast
    ring
  rw [hzsucc]
  omega

end GaloisForLFunctions.HTGeometry.BorelWeil
