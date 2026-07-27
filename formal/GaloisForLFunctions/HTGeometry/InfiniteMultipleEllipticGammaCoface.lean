import GaloisForLFunctions.HTGeometry.InfiniteMultipleEllipticGamma

/-!
# Coface recursion for the infinite-order multiple elliptic gamma product

Adding one distinguished nome decomposes the full occupation spectrum into layers indexed by its
occupation number.  This gives an exact tower product and, by separating the zero layer, the coface
recursion.  No enumeration or countability hypothesis is used.
-/

namespace HTGeometry

open scoped BigOperators

private theorem summable_option_elim {ι : Type*} (c : ℝ) {f : ι → ℝ}
    (hf : Summable f) :
    Summable (fun o : Option ι => o.elim c f) := by
  let f₀ : Option ι → ℝ := fun o => if o = none then c else 0
  let f₁ : Option ι → ℝ := fun o => o.elim 0 f
  have hf₀ : Summable f₀ := by
    apply summable_of_ne_finset_zero (s := {none})
    intro o ho
    simp only [Finset.mem_singleton] at ho
    simp [f₀, ho]
  have hf₁ : Summable f₁ := by
    have hsome : Function.Injective (Option.some : ι → Option ι) :=
      fun _ _ h => Option.some.inj h
    apply (hsome.summable_iff (f := f₁) ?_).mp
    · simpa [f₁] using hf
    · intro o ho
      cases o with
      | none => rfl
      | some a => exact False.elim (ho ⟨a, rfl⟩)
  convert hf₀.add hf₁ using 1
  funext o
  cases o <;> simp [f₀, f₁]

theorem nomeMonomial_optionElim {ι : Type*}
    (r : ℂ) (p : ι → ℂ) (n : ℕ) (ν : ι →₀ ℕ) :
    nomeMonomial (fun o : Option ι => o.elim r p) (ν.optionElim n) =
      r ^ n * nomeMonomial p ν := by
  classical
  rw [nomeMonomial, Finsupp.prod_option_index]
  · simp [nomeMonomial]
  · intro o
    simp
  · intro o m₁ m₂
    simp only [pow_add]

/-- Layering by the occupation number of one added nome. -/
theorem infiniteMultipleEllipticGamma_tower_hasProd {ι : Type*}
    (g : ℕ) (r : ℂ) (p : ι → ℂ)
    (hr_ne : r ≠ 0) (hr_lt : ‖r‖ < 1)
    (hp_ne : ∀ a, p a ≠ 0) (hp_lt : ∀ a, ‖p a‖ < 1)
    (hsum : Summable (fun a => ‖p a‖ ^ (g + 1))) (x : ℂ) :
    HasProd
      (fun n : ℕ => infiniteMultipleEllipticGamma g p (x * r ^ n))
      (infiniteMultipleEllipticGamma g (fun o : Option ι => o.elim r p) x) := by
  let P : Option ι → ℂ := fun o => o.elim r p
  have hP_ne : ∀ o, P o ≠ 0 := by
    intro o
    cases o with
    | none => exact hr_ne
    | some a => exact hp_ne a
  have hP_lt : ∀ o, ‖P o‖ < 1 := by
    intro o
    cases o with
    | none => exact hr_lt
    | some a => exact hp_lt a
  have hP_sum : Summable (fun o => ‖P o‖ ^ (g + 1)) := by
    convert summable_option_elim (‖r‖ ^ (g + 1)) hsum using 1
    funext o
    cases o <;> rfl
  let F : (Option ι →₀ ℕ) → ℂ :=
    fun μ => primaryFactor g (x * nomeMonomial P μ)
  have hfull : HasProd F (infiniteMultipleEllipticGamma g P x) := by
    simpa [F] using
      (infiniteMultipleEllipticGamma_hasProdLocallyUniformlyOn
        g P hP_ne hP_lt hP_sum).hasProd (Set.mem_univ x)
  have hpair : HasProd (fun z : ℕ × (ι →₀ ℕ) =>
      F (z.2.optionElim z.1)) (infiniteMultipleEllipticGamma g P x) := by
    exact (Finsupp.optionEquiv.symm.hasProd_iff).2 hfull
  apply hpair.prod_fiberwise
  intro n
  have hfiber :=
    (infiniteMultipleEllipticGamma_hasProdLocallyUniformlyOn
      g p hp_ne hp_lt hsum).hasProd (Set.mem_univ (x * r ^ n))
  convert hfiber using 1
  ext ν
  simp only [F, P, nomeMonomial_optionElim]
  ring_nf

/-- Exact coface law: adjoining a nome `r` multiplies the old face by the shifted full product. -/
theorem infiniteMultipleEllipticGamma_coface {ι : Type*}
    (g : ℕ) (r : ℂ) (p : ι → ℂ)
    (hr_ne : r ≠ 0) (hr_lt : ‖r‖ < 1)
    (hp_ne : ∀ a, p a ≠ 0) (hp_lt : ∀ a, ‖p a‖ < 1)
    (hsum : Summable (fun a => ‖p a‖ ^ (g + 1))) (x : ℂ) :
    infiniteMultipleEllipticGamma g (fun o : Option ι => o.elim r p) x =
      infiniteMultipleEllipticGamma g p x *
        infiniteMultipleEllipticGamma g (fun o : Option ι => o.elim r p) (r * x) := by
  let f : ℕ → ℂ := fun n => infiniteMultipleEllipticGamma g p (x * r ^ n)
  have hx := infiniteMultipleEllipticGamma_tower_hasProd
    g r p hr_ne hr_lt hp_ne hp_lt hsum x
  have hrx := infiniteMultipleEllipticGamma_tower_hasProd
    g r p hr_ne hr_lt hp_ne hp_lt hsum (r * x)
  have htail : Multipliable (fun n => f (n + 1)) := by
    apply hrx.multipliable.congr
    intro n
    simp only [f]
    congr 1
    rw [pow_succ]
    ring_nf
  calc
    infiniteMultipleEllipticGamma g (fun o : Option ι => o.elim r p) x =
        ∏' n, f n := hx.tprod_eq.symm
    _ = f 0 * ∏' n, f (n + 1) := tprod_eq_zero_mul' htail
    _ = infiniteMultipleEllipticGamma g p x *
        infiniteMultipleEllipticGamma g (fun o : Option ι => o.elim r p) (r * x) := by
      rw [show f 0 = infiniteMultipleEllipticGamma g p x by simp [f]]
      congr 1
      rw [← hrx.tprod_eq]
      apply tprod_congr
      intro n
      simp only [f]
      congr 1
      rw [pow_succ]
      ring_nf

end HTGeometry
