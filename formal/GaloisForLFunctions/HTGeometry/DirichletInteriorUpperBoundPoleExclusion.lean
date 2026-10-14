import GaloisForLFunctions.HTGeometry.DirichletCriticalUpperBoundPoleExclusion

/-!
# An interior one-sided bound excludes a rightmost positive-residue pole

Let `R` be the continuation of a Dirichlet series `Σ f(n) n^{−s}`, absolutely convergent at
`Re s = u₀`, and suppose that on the open half-plane `Re s > ½`

`R(s) = H(s) + Σ_j r_j / (s − p_j)`

with `H` holomorphic and `Re H ≤ C`, and with finitely many distinct poles `p_j`.

**Theorem** (`false_of_re_le_interior_of_rightmostPole`).  No pole `p_{j₀}` with `Re p_{j₀} > ½`
that is rightmost among the `p_j` can carry a residue with `Re r_{j₀} > 0`.

No continuity of `H` up to the line `Re s = ½` and no growth condition is assumed.  This is the
form in which the bound arises for Herglotz functions: if `c − R + Σ_j r_j/(s − p_j)` has
nonnegative real part on `Re s > ½`, the boundary values need not exist.

Proof.  Shift by `δ = (Re p_{j₀} − ½)/2`.  The function `z ↦ R(z + δ)` continues the Dirichlet
series of `f(n) n^{−δ}` (`LSeries_shift`); its regular part `H(· + δ)` is holomorphic on a
neighbourhood of `Re z ≥ ½`, has real part at most `C`, and on the line `Re z = ½` above the poles
the shifted function has real part at most `C + Σ_j |r_j|`.  The shifted poles `p_j − δ` keep their
residues and `p_{j₀} − δ` stays right of `½`, so `false_of_re_le_criticalLine_of_rightmostPole`
applies.
-/

open Complex Set

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- The coefficients of the Dirichlet series shifted by `δ`: `f(n) n^{−δ}`. -/
def shiftedCoeff (f : ℕ → ℂ) (δ : ℝ) (n : ℕ) : ℂ := f n * (n : ℂ) ^ (-(δ : ℂ))

theorem term_shiftedCoeff (f : ℕ → ℂ) (δ : ℝ) (s : ℂ) (n : ℕ) :
    LSeries.term (shiftedCoeff f δ) s n = LSeries.term f (s + δ) n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp only [LSeries.term_zero]
  rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn, shiftedCoeff,
    cpow_add _ _ (Nat.cast_ne_zero.mpr hn), cpow_neg]
  field_simp

theorem LSeries_shift (f : ℕ → ℂ) (δ : ℝ) (s : ℂ) :
    LSeries (shiftedCoeff f δ) s = LSeries f (s + δ) := by
  simp only [LSeries, term_shiftedCoeff]

theorem LSeriesSummable_shift {f : ℕ → ℂ} {u₀ : ℝ} (hsum : LSeriesSummable f (u₀ : ℂ)) (δ : ℝ) :
    LSeriesSummable (shiftedCoeff f δ) ((u₀ - δ : ℝ) : ℂ) := by
  have h : LSeries.term (shiftedCoeff f δ) ((u₀ - δ : ℝ) : ℂ) = LSeries.term f (u₀ : ℂ) := by
    funext n
    rw [term_shiftedCoeff]
    congr 1
    push_cast
    ring
  unfold LSeriesSummable
  rw [h]
  exact hsum

theorem principalPartSum_add_ofReal {m : ℕ} (p r : Fin m → ℂ) (z : ℂ) (δ : ℝ) :
    principalPartSum p r (z + δ) = principalPartSum (fun j => p j - δ) r z := by
  unfold principalPartSum
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  ring

/-- **An interior one-sided bound excludes a rightmost positive-residue pole.** -/
theorem false_of_re_le_interior_of_rightmostPole {f : ℕ → ℂ} {u₀ : ℝ}
    (hsum : LSeriesSummable f (u₀ : ℂ)) {R H : ℂ → ℂ} {m : ℕ} {p r : Fin m → ℂ}
    (hp : Function.Injective p)
    (hH : DifferentiableOn ℂ H {z : ℂ | 1 / 2 < z.re}) {C : ℝ}
    (hHle : ∀ z : ℂ, 1 / 2 < z.re → (H z).re ≤ C)
    (hRH : ∀ z : ℂ, 1 / 2 < z.re → (∀ j, z ≠ p j) → R z = H z + principalPartSum p r z)
    (hRL : ∀ z : ℂ, u₀ < z.re → R z = LSeries f z)
    (j₀ : Fin m) (hj₀ : 1 / 2 < (p j₀).re) (hmax : ∀ j, (p j).re ≤ (p j₀).re)
    (hres : 0 < (r j₀).re) : False := by
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = ((p j₀).re - 1 / 2) / 2 := ⟨_, rfl⟩
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  have hre : ∀ z : ℂ, (z + (δ : ℂ)).re = z.re + δ := fun z => by simp
  have hshift : ∀ z : ℂ, 1 / 2 ≤ z.re → 1 / 2 < (z + (δ : ℂ)).re := fun z hz => by
    rw [hre]; linarith
  -- the shifted data
  have hp' : Function.Injective fun j => p j - (δ : ℂ) := fun i j h => hp (by simpa using h)
  have hH' : DifferentiableOn ℂ (fun z => H (z + δ)) {z : ℂ | 1 / 2 < z.re} :=
    hH.comp (differentiableOn_id.add_const _) fun z hz => hshift z (le_of_lt hz)
  have hHc' : ContinuousOn (fun z => H (z + δ)) {z : ℂ | 1 / 2 ≤ z.re} := by
    intro z hz
    have hd : DifferentiableAt ℂ H (z + δ) :=
      hH.differentiableAt ((isOpen_lt continuous_const continuous_re).mem_nhds (hshift z hz))
    have hc : ContinuousAt (fun w : ℂ => H (w + δ)) z :=
      ContinuousAt.comp (g := H) (f := fun w : ℂ => w + δ) hd.continuousAt
        (continuous_add_const (δ : ℂ)).continuousAt
    exact hc.continuousWithinAt
  have hgrowth' : ∀ κ : ℝ, 0 < κ → ∃ B : ℝ, ∀ z : ℂ, 1 / 2 ≤ z.re →
      (H (z + δ)).re ≤ B * Real.exp (κ * |z.im|) := fun κ hκ => by
    refine ⟨|C|, fun z hz => ?_⟩
    have h1 : 1 ≤ Real.exp (κ * |z.im|) := Real.one_le_exp (by positivity)
    calc (H (z + δ)).re ≤ C := hHle _ (hshift z hz)
      _ ≤ |C| := le_abs_self C
      _ ≤ |C| * Real.exp (κ * |z.im|) := le_mul_of_one_le_right (abs_nonneg C) h1
  have hRH' : ∀ z : ℂ, 1 / 2 ≤ z.re → (∀ j, z ≠ p j - δ) →
      R (z + δ) = H (z + δ) + principalPartSum (fun j => p j - δ) r z := by
    intro z hz hne
    rw [← principalPartSum_add_ofReal]
    exact hRH _ (hshift z hz) fun j h => hne j (by rw [← h]; ring)
  have hRL' : ∀ z : ℂ, u₀ - δ < z.re → R (z + δ) = LSeries (shiftedCoeff f δ) z := by
    intro z hz
    rw [LSeries_shift, hRL _ (by rw [hre]; linarith)]
  have hline : ∀ t : ℝ, (∑ j, |(p j).im|) + 1 ≤ |t| →
      (R (1 / 2 + t * I + δ)).re ≤ C + ∑ j, ‖r j‖ := by
    intro t ht
    have him : |(1 / 2 + t * I + (δ : ℂ)).im| = |t| := by simp
    have ht' : (∑ j, |(p j).im|) + 1 ≤ |(1 / 2 + t * I + (δ : ℂ)).im| := by rw [him]; exact ht
    have hR := hRH _ (hshift _ (by simp)) (ne_of_one_le_norm_sub ht')
    have hpp : ‖principalPartSum p r (1 / 2 + t * I + δ)‖ ≤ ∑ j, ‖r j‖ := by
      simpa using norm_principalPartSum_le (r := r) one_pos (one_le_norm_sub_of_im ht')
    rw [hR, add_re]
    have h1 := hHle _ (hshift (1 / 2 + t * I) (by simp))
    have h2 := Complex.re_le_norm (principalPartSum p r (1 / 2 + t * I + δ))
    linarith
  have hline' : ∀ t : ℝ, (∑ j, |(p j - (δ : ℂ)).im|) + 1 ≤ |t| →
      (R ((1 / 2 + t * I) + δ)).re ≤ C + ∑ j, ‖r j‖ := by
    intro t ht
    refine hline t ?_
    simpa using ht
  exact false_of_re_le_criticalLine_of_rightmostPole (LSeriesSummable_shift hsum δ) hp' hH' hHc'
    hgrowth' hRH' (by
      intro z hz
      simpa using hRL' z (by simpa using hz)) hline' j₀ (by simp; linarith)
    (fun j => by simpa using hmax j) hres

end GaloisForLFunctions.HTGeometry
