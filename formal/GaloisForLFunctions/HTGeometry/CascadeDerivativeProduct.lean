import GaloisForLFunctions.HTGeometry.EntireCascade
import GaloisForLFunctions.HTGeometry.CascadeRelationClearing

/-!
# The cascade derivative as a product

Iterating the chain rule expresses the derivative of a cascade state as the product of the
constituents' derivatives evaluated along the earlier states.  Every later jet is built from this
product and its derivatives, so the product is the basic datum of any observability computation.
-/

namespace GaloisForLFunctions.HTGeometry

/-- **The chain rule along a cascade, in closed form.** -/
theorem deriv_entireCascade_prod {f : ℕ → ℂ → ℂ}
    (hf : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ) (k : ℕ) (z : ℂ) :
    deriv (entireCascade f k) z
      = ∏ j ∈ Finset.range k, deriv (f j) (entireCascade f j z) := by
  induction k with
  | zero =>
      rw [Finset.range_zero, Finset.prod_empty]
      simp [entireCascade]
  | succ k ih =>
      rw [deriv_entireCascade_succ hf k z, ih, Finset.prod_range_succ]
      ring

/-- **A cascade state has nonvanishing derivative exactly where every constituent does.** -/
theorem deriv_entireCascade_ne_zero_iff {f : ℕ → ℂ → ℂ}
    (hf : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ) (k : ℕ) (z : ℂ) :
    deriv (entireCascade f k) z ≠ 0
      ↔ ∀ j ∈ Finset.range k, deriv (f j) (entireCascade f j z) ≠ 0 := by
  rw [deriv_entireCascade_prod hf k z, Finset.prod_ne_zero_iff]

/-- **The derivative of the next state, factored off.** -/
theorem deriv_entireCascade_succ_prod {f : ℕ → ℂ → ℂ}
    (hf : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ) (k : ℕ) (z : ℂ) :
    deriv (entireCascade f (k + 1)) z
      = deriv (f k) (entireCascade f k z) * deriv (entireCascade f k) z := by
  exact deriv_entireCascade_succ hf k z

/-! ## The second jet

Differentiating the product turns the logarithmic derivative of `F_k'` into a sum over the
constituents.  This is the first row of the observability system: the second jet of the output is a
prescribed linear combination of the states' derivatives. -/

/-- **The logarithmic derivative of the cascade derivative.** -/
theorem logDeriv_deriv_entireCascade {f : ℕ → ℂ → ℂ}
    (hf : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ) (k : ℕ) (z : ℂ)
    (hne : deriv (entireCascade f k) z ≠ 0) :
    deriv (deriv (entireCascade f k)) z / deriv (entireCascade f k) z
      = ∑ j ∈ Finset.range k,
          deriv (deriv (f j)) (entireCascade f j z) / deriv (f j) (entireCascade f j z)
            * deriv (entireCascade f j) z := by
  induction k with
  | zero =>
      have hid : deriv (entireCascade f 0) = fun _ : ℂ => (1 : ℂ) := by
        funext w
        simp [entireCascade]
      rw [Finset.range_zero, Finset.sum_empty, hid]
      simp
  | succ k ih =>
      have hall := (deriv_entireCascade_ne_zero_iff hf (k + 1) z).mp hne
      have hfk : deriv (f k) (entireCascade f k z) ≠ 0 :=
        hall k (Finset.mem_range.mpr (by omega))
      have hk : deriv (entireCascade f k) z ≠ 0 := by
        rw [deriv_entireCascade_ne_zero_iff hf k z]
        intro j hj
        exact hall j (Finset.mem_range.mpr (by
          have := Finset.mem_range.mp hj
          omega))
      have h2 := deriv2_entireCascade_succ hf k z
      have h1 := deriv_entireCascade_succ hf k z
      have hih := ih hk
      rw [h2, h1, Finset.sum_range_succ, ← hih]
      field_simp
      ring

end GaloisForLFunctions.HTGeometry
