import GaloisForLFunctions.HTGeometry.TripticLineFiniteness

/-!
# Only finitely many shift indices connect two pole classes

Let `1, τ, σ` be `ℤ`-independent and let `Q` be a finite set of points.  If `q + dσ` and `q'` differ
by an element of `ℤ + ℤτ` for some `q, q' ∈ Q`, then `d` is determined by the pair `(q, q')`: two
solutions differ by a nontrivial relation between `1`, `τ` and `σ`.  Hence only finitely many `d`
occur.

This is the finiteness that bounds all of the mixed-constraint bookkeeping.  The pole classes of a
boundary function modulo its own lattice form a finite set `Q`; the lemma says the classes are spread
over only finitely many steps in the transverse direction, so the coefficient families attached to
them are supported in a finite range of indices.

* `finite_shift_indices`.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex

/-- **Finitely many transverse shift indices connect two classes.** -/
theorem finite_shift_indices {τ σ : ℂ}
    (hindep : ∀ n m j : ℤ, (n : ℂ) * τ + (m : ℂ) * σ + (j : ℂ) = 0 → n = 0 ∧ m = 0 ∧ j = 0)
    (Q : Finset ℂ) :
    {d : ℤ | ∃ q ∈ Q, ∃ q' ∈ Q, ∃ a b : ℤ,
      q + (d : ℂ) * σ = q' + (a : ℂ) + (b : ℂ) * τ}.Finite := by
  classical
  set S : Set ℤ := {d : ℤ | ∃ q ∈ Q, ∃ q' ∈ Q, ∃ a b : ℤ,
    q + (d : ℂ) * σ = q' + (a : ℂ) + (b : ℂ) * τ} with hSdef
  have hchoice : ∀ d : ℤ, d ∈ S → ∃ p : ℂ × ℂ, p.1 ∈ Q ∧ p.2 ∈ Q ∧
      ∃ a b : ℤ, p.1 + (d : ℂ) * σ = p.2 + (a : ℂ) + (b : ℂ) * τ := by
    intro d hd
    obtain ⟨q, hq, q', hq', a, b, hab⟩ := hd
    exact ⟨(q, q'), hq, hq', a, b, hab⟩
  choose f hf1 hf2 hf3 using hchoice
  set F : ℤ → ℂ × ℂ := fun d => if hd : d ∈ S then f d hd else (0, 0) with hFdef
  have hinj : Set.InjOn F S := by
    intro d hd d' hd' heq
    rw [hFdef] at heq
    simp only [dif_pos hd, dif_pos hd'] at heq
    obtain ⟨a, b, hab⟩ := hf3 d hd
    obtain ⟨a', b', hab'⟩ := hf3 d' hd'
    rw [heq] at hab
    have hrel : ((b - b' : ℤ) : ℂ) * τ + ((d' - d : ℤ) : ℂ) * σ + ((a - a' : ℤ) : ℂ) = 0 := by
      push_cast
      linear_combination hab' - hab
    obtain ⟨_, h2, _⟩ := hindep _ _ _ hrel
    omega
  refine Set.Finite.of_finite_image ?_ hinj
  refine Set.Finite.subset (Q ×ˢ Q : Finset (ℂ × ℂ)).finite_toSet ?_
  rintro p ⟨d, hd, rfl⟩
  rw [hFdef]
  simp only [dif_pos hd, Finset.coe_product, Set.mem_prod]
  exact ⟨hf1 d hd, hf2 d hd⟩

end GaloisForLFunctions.HTGeometry
