import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.GroupTheory.Perm.Sign

/-!
# Symmetry of the iterated Fréchet derivative of a `C^n` map

Mathlib proves that the second derivative of a `C^(2 : ℕ)` map is symmetric
(`ContDiffAt.isSymmSndFDerivAt`), and that all iterated derivatives of an analytic map are
symmetric, but not that the `n`-th derivative of a `C^n` map is symmetric.  That is proved here.

The argument is an induction on `n`.  Writing
`iteratedFDeriv (n+1) f x m = iteratedFDeriv n (fderiv f) x (init m) (m (last n))`, the inductive
hypothesis applied to `fderiv f` gives invariance under every permutation of the first `n` slots.
Peeling twice instead gives
`iteratedFDeriv (p+2) f x m = iteratedFDeriv p (fderiv (fderiv f)) x (init (init m)) a b`
with `a`, `b` the last two entries of `m`; since `y ↦ fderiv (fderiv f) y` takes symmetric values
near `x`, so does its `p`-th derivative, and the last two slots may be exchanged.  Adjacent
transpositions generate the symmetric group (`Equiv.Perm.mclosure_swap_castSucc_succ`), which
finishes the induction.

## Main results

* `ContDiffAt.iteratedFDeriv_comp_perm` — `iteratedFDeriv ℝ n f x (m ∘ σ) = iteratedFDeriv ℝ n f x m`.
* `ContDiffAt.domDomCongr_iteratedFDeriv` — the same statement as `domDomCongr`-invariance.
-/

open Filter
open scoped Topology

namespace GaloisForLFunctions.HTGeometry

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Evaluation of a bilinear-map-valued expression at a pair of vectors, as a continuous linear
map. -/
noncomputable def evalPairCLM (F : Type u) [NormedAddCommGroup F] [NormedSpace ℝ F] (a b : E) :
    (E →L[ℝ] E →L[ℝ] F) →L[ℝ] F :=
  (ContinuousLinearMap.apply ℝ F b).comp (ContinuousLinearMap.apply ℝ (E →L[ℝ] F) a)

theorem evalPairCLM_apply {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F] (a b : E)
    (T : E →L[ℝ] E →L[ℝ] F) : evalPairCLM F a b T = T a b := rfl

/-- The `p`-th derivative of `y ↦ fderiv (fderiv f) y` takes symmetric values. -/
theorem iteratedFDeriv_snd_swap {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {p : ℕ} {f : E → F} {x : E} (hf : ContDiffAt ℝ ((p + 2 : ℕ)) f x)
    (u : Fin p → E) (a b : E) :
    iteratedFDeriv ℝ p (fun y => fderiv ℝ (fderiv ℝ f) y) x u a b
      = iteratedFDeriv ℝ p (fun y => fderiv ℝ (fderiv ℝ f) y) x u b a := by
  set G : E → (E →L[ℝ] E →L[ℝ] F) := fun y => fderiv ℝ (fderiv ℝ f) y with hG
  have h1 : ContDiffAt ℝ ((p + 1 : ℕ)) (fderiv ℝ f) x := by
    refine hf.fderiv_right ?_
    push_cast
    exact le_rfl
  have h2 : ContDiffAt ℝ ((p : ℕ)) G x := by
    refine h1.fderiv_right ?_
    push_cast
    exact le_rfl
  have hev : (fun y => evalPairCLM F a b (G y)) =ᶠ[𝓝 x] fun y => evalPairCLM F b a (G y) := by
    have hnetop : ((p + 2 : ℕ) : WithTop ℕ∞) ≠ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
      intro h
      rw [show ((p + 2 : ℕ) : WithTop ℕ∞) = ((((p + 2 : ℕ) : ℕ∞)) : WithTop ℕ∞) by norm_cast] at h
      exact ENat.coe_ne_top (p + 2) (by exact_mod_cast h)
    have hev2 : ∀ᶠ y in 𝓝 x, ContDiffAt ℝ ((p + 2 : ℕ)) f y := hf.eventually hnetop
    filter_upwards [hev2] with y hy
    have hmin : minSmoothness ℝ (2 : WithTop ℕ∞) ≤ ((p + 2 : ℕ) : WithTop ℕ∞) := by
      rw [minSmoothness_of_isRCLikeNormedField]
      exact_mod_cast Nat.le_add_left 2 p
    exact (hy.isSymmSndFDerivAt hmin) a b
  have e1 := ContinuousLinearMap.iteratedFDeriv_comp_left (evalPairCLM F a b) h2
    (le_refl ((p : ℕ) : WithTop ℕ∞))
  have e2 := ContinuousLinearMap.iteratedFDeriv_comp_left (evalPairCLM F b a) h2
    (le_refl ((p : ℕ) : WithTop ℕ∞))
  have e3 : iteratedFDeriv ℝ p (fun y => evalPairCLM F a b (G y)) x
      = iteratedFDeriv ℝ p (fun y => evalPairCLM F b a (G y)) x :=
    (Filter.EventuallyEq.iteratedFDeriv ℝ hev p).eq_of_nhds
  have f1 : iteratedFDeriv ℝ p (fun y => evalPairCLM F a b (G y)) x u
      = evalPairCLM F a b (iteratedFDeriv ℝ p G x u) := by
    rw [show (fun y => evalPairCLM F a b (G y)) = (evalPairCLM F a b) ∘ G from rfl, e1]
    rfl
  have f2 : iteratedFDeriv ℝ p (fun y => evalPairCLM F b a (G y)) x u
      = evalPairCLM F b a (iteratedFDeriv ℝ p G x u) := by
    rw [show (fun y => evalPairCLM F b a (G y)) = (evalPairCLM F b a) ∘ G from rfl, e2]
    rfl
  calc iteratedFDeriv ℝ p G x u a b = evalPairCLM F a b (iteratedFDeriv ℝ p G x u) := rfl
    _ = iteratedFDeriv ℝ p (fun y => evalPairCLM F a b (G y)) x u := f1.symm
    _ = iteratedFDeriv ℝ p (fun y => evalPairCLM F b a (G y)) x u := by rw [e3]
    _ = evalPairCLM F b a (iteratedFDeriv ℝ p G x u) := f2
    _ = iteratedFDeriv ℝ p G x u b a := rfl

/-- Peeling two derivatives from the right. -/
theorem iteratedFDeriv_peel_two {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {p : ℕ} (f : E → F) (x : E) (v : Fin (p + 2) → E) :
    iteratedFDeriv ℝ (p + 2) f x v
      = iteratedFDeriv ℝ p (fun y => fderiv ℝ (fderiv ℝ f) y) x (Fin.init (Fin.init v))
          (v (Fin.castSucc (Fin.last p))) (v (Fin.last (p + 1))) := by
  rw [iteratedFDeriv_succ_apply_right v, iteratedFDeriv_succ_apply_right (Fin.init v)]
  rfl

/-- Exchanging the last two slots. -/
theorem swap_last_two {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F] {p : ℕ}
    {f : E → F} {x : E} (hf : ContDiffAt ℝ ((p + 2 : ℕ)) f x) (m : Fin (p + 2) → E) :
    iteratedFDeriv ℝ (p + 2) f x
        (m ∘ Equiv.swap (Fin.castSucc (Fin.last p)) (Fin.last (p + 1)))
      = iteratedFDeriv ℝ (p + 2) f x m := by
  have hne : Fin.castSucc (Fin.last p) ≠ Fin.last (p + 1) := by
    simp [Fin.ext_iff]
  have hinit : Fin.init (Fin.init (m ∘ Equiv.swap (Fin.castSucc (Fin.last p)) (Fin.last (p + 1))))
      = Fin.init (Fin.init m) := by
    funext c
    show m (Equiv.swap (Fin.castSucc (Fin.last p)) (Fin.last (p + 1))
      (Fin.castSucc (Fin.castSucc c))) = m (Fin.castSucc (Fin.castSucc c))
    congr 1
    refine Equiv.swap_apply_of_ne_of_ne ?_ ?_ <;> simp [Fin.ext_iff] <;> omega
  have hA : (m ∘ Equiv.swap (Fin.castSucc (Fin.last p)) (Fin.last (p + 1)))
      (Fin.castSucc (Fin.last p)) = m (Fin.last (p + 1)) := by
    show m (Equiv.swap (Fin.castSucc (Fin.last p)) (Fin.last (p + 1))
      (Fin.castSucc (Fin.last p))) = _
    rw [Equiv.swap_apply_left]
  have hB : (m ∘ Equiv.swap (Fin.castSucc (Fin.last p)) (Fin.last (p + 1)))
      (Fin.last (p + 1)) = m (Fin.castSucc (Fin.last p)) := by
    show m (Equiv.swap (Fin.castSucc (Fin.last p)) (Fin.last (p + 1)) (Fin.last (p + 1))) = _
    rw [Equiv.swap_apply_right]
  rw [iteratedFDeriv_peel_two f x, iteratedFDeriv_peel_two f x m, hinit, hA, hB]
  exact iteratedFDeriv_snd_swap hf _ _ _


/-- Exchanging two slots that both avoid the last one, using the inductive hypothesis. -/
theorem swap_of_ne_last {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F] {n : ℕ}
    {f : E → F} {x : E}
    (ih : ∀ (σ : Equiv.Perm (Fin n)) (v : Fin n → E),
      iteratedFDeriv ℝ n (fderiv ℝ f) x (v ∘ σ) = iteratedFDeriv ℝ n (fderiv ℝ f) x v)
    (a b : Fin n) (m : Fin (n + 1) → E) :
    iteratedFDeriv ℝ (n + 1) f x (m ∘ Equiv.swap a.castSucc b.castSucc)
      = iteratedFDeriv ℝ (n + 1) f x m := by
  have hnea : (Fin.last n) ≠ a.castSucc := by
    intro h
    have h2 := congrArg Fin.val h
    have := a.isLt
    simp only [Fin.val_last, Fin.val_castSucc] at h2
    omega
  have hneb : (Fin.last n) ≠ b.castSucc := by
    intro h
    have h2 := congrArg Fin.val h
    have := b.isLt
    simp only [Fin.val_last, Fin.val_castSucc] at h2
    omega
  have hlast : (m ∘ Equiv.swap a.castSucc b.castSucc) (Fin.last n) = m (Fin.last n) := by
    show m (Equiv.swap a.castSucc b.castSucc (Fin.last n)) = _
    rw [Equiv.swap_apply_of_ne_of_ne hnea hneb]
  have hinit : Fin.init (m ∘ Equiv.swap a.castSucc b.castSucc)
      = (Fin.init m) ∘ Equiv.swap a b := by
    funext c
    show m (Equiv.swap a.castSucc b.castSucc c.castSucc) = m ((Equiv.swap a b c).castSucc)
    congr 1
    by_cases hca : c = a
    · subst hca
      rw [Equiv.swap_apply_left, Equiv.swap_apply_left]
    · by_cases hcb : c = b
      · subst hcb
        rw [Equiv.swap_apply_right, Equiv.swap_apply_right]
      · rw [Equiv.swap_apply_of_ne_of_ne (fun h => hca (Fin.castSucc_injective _ h))
            (fun h => hcb (Fin.castSucc_injective _ h)),
          Equiv.swap_apply_of_ne_of_ne hca hcb]
  rw [iteratedFDeriv_succ_apply_right (m ∘ Equiv.swap a.castSucc b.castSucc),
    iteratedFDeriv_succ_apply_right m, hinit, hlast, ih]

/-- Every adjacent transposition acts trivially on the `(n+1)`-st derivative. -/
theorem swap_adjacent {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F] {n : ℕ}
    {f : E → F} {x : E} (hf : ContDiffAt ℝ ((n + 1 : ℕ)) f x)
    (ih : ∀ (σ : Equiv.Perm (Fin n)) (v : Fin n → E),
      iteratedFDeriv ℝ n (fderiv ℝ f) x (v ∘ σ) = iteratedFDeriv ℝ n (fderiv ℝ f) x v)
    (i : Fin n) (v : Fin (n + 1) → E) :
    iteratedFDeriv ℝ (n + 1) f x (v ∘ Equiv.swap i.castSucc i.succ)
      = iteratedFDeriv ℝ (n + 1) f x v := by
  by_cases hi : (i : ℕ) + 1 < n
  · have hb : (⟨(i : ℕ) + 1, hi⟩ : Fin n).castSucc = i.succ := by
      apply Fin.ext
      simp
    rw [← hb]
    exact swap_of_ne_last ih i ⟨(i : ℕ) + 1, hi⟩ v
  · have hn : (i : ℕ) + 1 = n := by
      have := i.isLt
      omega
    obtain ⟨p, rfl⟩ : ∃ p, n = p + 1 := ⟨n - 1, by omega⟩
    have hil : i = Fin.last p := by
      apply Fin.ext
      simp only [Fin.val_last]
      omega
    subst hil
    have hsucc : (Fin.last p).succ = Fin.last (p + 1) := rfl
    rw [hsucc]
    exact swap_last_two hf v

/-- **Symmetry of the iterated derivative of a `C^n` map.** -/
theorem iteratedFDeriv_comp_perm_aux :
    ∀ (n : ℕ) (F : Type u) [NormedAddCommGroup F] [NormedSpace ℝ F] (f : E → F) (x : E),
      ContDiffAt ℝ ((n : ℕ)) f x → ∀ (σ : Equiv.Perm (Fin n)) (m : Fin n → E),
        iteratedFDeriv ℝ n f x (m ∘ σ) = iteratedFDeriv ℝ n f x m := by
  intro n
  induction n with
  | zero =>
      intro F _ _ f x _ _ m
      congr 1
      funext i
      exact i.elim0
  | succ n ih =>
      intro F _ _ f x hf σ m
      have hfd : ContDiffAt ℝ ((n : ℕ)) (fderiv ℝ f) x := by
        refine hf.fderiv_right ?_
        push_cast
        exact le_rfl
      have ihF := ih (E →L[ℝ] F) (fderiv ℝ f) x hfd
      have hmem : σ ∈ Submonoid.closure
          (Set.range fun i : Fin n ↦ Equiv.swap i.castSucc i.succ) := by
        rw [Equiv.Perm.mclosure_swap_castSucc_succ n]
        exact Submonoid.mem_top σ
      refine Submonoid.closure_induction
        (motive := fun (τ : Equiv.Perm (Fin (n + 1))) _ => ∀ v : Fin (n + 1) → E,
          iteratedFDeriv ℝ (n + 1) f x (v ∘ τ) = iteratedFDeriv ℝ (n + 1) f x v)
        ?_ ?_ ?_ hmem m
      · rintro _ ⟨i, rfl⟩ v
        exact swap_adjacent hf ihF i v
      · intro v
        rfl
      · intro τ₁ τ₂ _ _ h₁ h₂ v
        show iteratedFDeriv ℝ (n + 1) f x (v ∘ (τ₁ * τ₂ : Equiv.Perm (Fin (n + 1))))
          = iteratedFDeriv ℝ (n + 1) f x v
        have hcomp : v ∘ (τ₁ * τ₂ : Equiv.Perm (Fin (n + 1))) = (v ∘ τ₁) ∘ τ₂ := rfl
        rw [hcomp, h₂ (v ∘ τ₁), h₁ v]

/-- **Symmetry of the iterated derivative of a `C^n` map**, pointwise form. -/
theorem iteratedFDeriv_comp_perm {F : Type u} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {n : ℕ} {f : E → F} {x : E} (hf : ContDiffAt ℝ ((n : ℕ)) f x)
    (σ : Equiv.Perm (Fin n)) (m : Fin n → E) :
    iteratedFDeriv ℝ n f x (m ∘ σ) = iteratedFDeriv ℝ n f x m :=
  iteratedFDeriv_comp_perm_aux n F f x hf σ m

end GaloisForLFunctions.HTGeometry
