import GaloisForLFunctions.HTGeometry.ZeroMultisetRolle

/-!
# Vanishing order under sums and products

Two closure properties of the vanishing-order predicate `VanishesTo`.

* It is closed under sums.
* Multiplying by a smooth factor cannot decrease it: `VanishesTo f n x → VanishesTo (u · f) n x`.

The second is the step that transports a zero configuration along `f ↦ e^{-a t} f`, the
normalisation used in Descartes/Laguerre-type inductions for exponential sums: multiplying by a
nowhere-zero exponential changes neither the zeros nor their orders, while removing the lowest
exponent from the derivative.
-/

namespace GaloisForLFunctions.HTGeometry

theorem vanishesTo_succ_iff {g : ℝ → ℝ} {n : ℕ} {x : ℝ} :
    VanishesTo g (n + 1) x ↔ g x = 0 ∧ VanishesTo (deriv g) n x := by
  constructor
  · intro h
    exact ⟨apply_eq_zero_of_vanishesTo (by omega) h, vanishesTo_deriv h⟩
  · rintro ⟨h0, hd⟩ j hj
    match j with
    | 0 => rwa [iteratedDeriv_zero]
    | (i + 1) =>
      rw [iteratedDeriv_succ']
      exact hd i (by omega)

theorem contDiff_deriv {u : ℝ → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u) :
    ContDiff ℝ (⊤ : ℕ∞) (deriv u) := by
  have := hu.iterate_deriv 1
  simpa using this

/-- Vanishing order is closed under sums. -/
theorem vanishesTo_add :
    ∀ (n : ℕ) {f g : ℝ → ℝ}, ContDiff ℝ (⊤ : ℕ∞) f → ContDiff ℝ (⊤ : ℕ∞) g →
      ∀ {x : ℝ}, VanishesTo f n x → VanishesTo g n x →
        VanishesTo (fun t => f t + g t) n x := by
  intro n
  induction n with
  | zero => intro f g _ _ x _ _; exact vanishesTo_zero _ _
  | succ m ih =>
    intro f g hf hg x hvf hvg
    rw [vanishesTo_succ_iff] at hvf hvg ⊢
    refine ⟨by rw [hvf.1, hvg.1]; ring, ?_⟩
    have hderiv : deriv (fun t => f t + g t) = fun t => deriv f t + deriv g t := by
      funext t
      exact deriv_add ((hf.differentiable (by simp)) t) ((hg.differentiable (by simp)) t)
    rw [hderiv]
    exact ih (contDiff_deriv hf) (contDiff_deriv hg) hvf.2 hvg.2

/-- **Multiplying by a smooth factor cannot decrease the vanishing order.** -/
theorem vanishesTo_mul_left :
    ∀ (n : ℕ) {u f : ℝ → ℝ}, ContDiff ℝ (⊤ : ℕ∞) u → ContDiff ℝ (⊤ : ℕ∞) f →
      ∀ {x : ℝ}, VanishesTo f n x → VanishesTo (fun t => u t * f t) n x := by
  intro n
  induction n with
  | zero => intro u f _ _ x _; exact vanishesTo_zero _ _
  | succ m ih =>
    intro u f hu hf x hv
    rw [vanishesTo_succ_iff] at hv ⊢
    refine ⟨by rw [hv.1]; ring, ?_⟩
    have hderiv : deriv (fun t => u t * f t) = fun t => deriv u t * f t + u t * deriv f t := by
      funext t
      exact deriv_mul ((hu.differentiable (by simp)) t) ((hf.differentiable (by simp)) t)
    rw [hderiv]
    have h1 : VanishesTo (fun t => deriv u t * f t) m x :=
      ih (contDiff_deriv hu) hf (vanishesTo_mono (Nat.le_succ m) (vanishesTo_succ_iff.mpr hv))
    have h2 : VanishesTo (fun t => u t * deriv f t) m x := ih hu (contDiff_deriv hf) hv.2
    exact vanishesTo_add m ((contDiff_deriv hu).mul hf) (hu.mul (contDiff_deriv hf)) h1 h2

end GaloisForLFunctions.HTGeometry
