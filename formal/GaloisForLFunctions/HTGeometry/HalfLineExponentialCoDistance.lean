import GaloisForLFunctions.HTGeometry.HalfLineExponentialDistance

/-!
# The finite co-distance of a half-line exponential

Listing every rate except one and putting the omitted rate last turns the Blaschke distance law into
the *co-distance* law: the squared distance from `e_{λ_n}` to the span of `{e_{λ_m} : m ≤ N, m ≠ n}`
is the Blaschke product of those rates against `λ_n`, divided by `2 λ_n`.
-/

open Finset MeasureTheory
open scoped InnerProductSpace
open InnerProductSpace

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-! ## The enumeration that defers one index -/

/-- The enumeration of `ℕ` that skips `n` and places `n` itself at position `N`. -/
def coIdx (n N k : ℕ) : ℕ := if k = N then n else if k < n then k else k + 1

@[simp] theorem coIdx_self (n N : ℕ) : coIdx n N N = n := by simp [coIdx]

theorem coIdx_of_ne {n N k : ℕ} (hk : k ≠ N) :
    coIdx n N k = if k < n then k else k + 1 := by simp [coIdx, hk]

theorem coIdx_ne_of_ne {n N k : ℕ} (hk : k ≠ N) : coIdx n N k ≠ n := by
  rw [coIdx_of_ne hk]
  by_cases h : k < n
  · simp only [h, if_true]
    omega
  · simp only [h, if_false]
    omega

theorem coIdx_injective (n N : ℕ) : Function.Injective (coIdx n N) := by
  intro a b hab
  by_cases ha : a = N
  · by_cases hb : b = N
    · rw [ha, hb]
    · subst ha
      rw [coIdx_self] at hab
      exact absurd hab.symm (coIdx_ne_of_ne hb)
  · by_cases hb : b = N
    · subst hb
      rw [coIdx_self] at hab
      exact absurd hab (coIdx_ne_of_ne ha)
    · rw [coIdx_of_ne ha, coIdx_of_ne hb] at hab
      by_cases h1 : a < n <;> by_cases h2 : b < n <;>
        simp only [h1, h2, if_true, if_false] at hab <;> omega

theorem coIdx_lt_of_lt {n N k : ℕ} (hk : k < N) : coIdx n N k < N + 1 := by
  rw [coIdx_of_ne (Nat.ne_of_lt hk)]
  by_cases h : k < n
  · simp only [h, if_true]; omega
  · simp only [h, if_false]; omega

/-- The deferred enumeration lists exactly the indices up to `N` other than `n`. -/
theorem image_coIdx {n N : ℕ} (hn : n ≤ N) :
    Finset.image (coIdx n N) (Finset.range N) = (Finset.range (N + 1)).erase n := by
  ext m
  simp only [Finset.mem_image, Finset.mem_range, Finset.mem_erase]
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨coIdx_ne_of_ne (Nat.ne_of_lt hk), coIdx_lt_of_lt hk⟩
  · rintro ⟨hmn, hm⟩
    by_cases h : m < n
    · refine ⟨m, by omega, ?_⟩
      rw [coIdx_of_ne (by omega : m ≠ N)]
      simp [h]
    · refine ⟨m - 1, by omega, ?_⟩
      have hm1 : m - 1 ≠ N := by omega
      rw [coIdx_of_ne hm1]
      have : ¬ (m - 1 < n) := by omega
      simp only [this, if_false]
      omega

theorem prod_coIdx {M : Type*} [CommMonoid M] {n N : ℕ} (hn : n ≤ N) (f : ℕ → M) :
    (∏ i : Fin N, f (coIdx n N (i : ℕ))) = ∏ m ∈ (Finset.range (N + 1)).erase n, f m := by
  classical
  rw [← image_coIdx hn,
    Finset.prod_image (fun a _ b _ h => coIdx_injective n N h),
    Finset.prod_range fun k => f (coIdx n N k)]

/-! ## The co-distance law -/

/-- **The finite co-distance law.**  The squared Gram--Schmidt length of the deferred exponential
system at step `N` is the Blaschke product of the other rates against `λ_n`. -/
theorem inner_gramSchmidt_coSystem {lam : ℕ → ℝ} (hpos : ∀ k, 0 < lam k)
    (hinj : Function.Injective lam) {n N : ℕ} (hn : n ≤ N) :
    inner ℂ
        (gramSchmidt ℂ (expSystem (fun k => lam (coIdx n N k)) (fun _ => hpos _)) N)
        (gramSchmidt ℂ (expSystem (fun k => lam (coIdx n N k)) (fun _ => hpos _)) N) *
        ((∏ m ∈ (Finset.range (N + 1)).erase n,
            (((lam m : ℝ) : ℂ) + ((lam n : ℝ) : ℂ))) ^ (2 : ℕ) *
          (((lam n : ℝ) : ℂ) + ((lam n : ℝ) : ℂ)))
      = (∏ m ∈ (Finset.range (N + 1)).erase n,
          (((lam m : ℝ) : ℂ) - ((lam n : ℝ) : ℂ))) ^ (2 : ℕ) := by
  classical
  have hposn : ∀ k, 0 < lam (coIdx n N k) := fun _ => hpos _
  have hinjn : Function.Injective (fun k => lam (coIdx n N k)) :=
    hinj.comp (coIdx_injective n N)
  have hkey := inner_gramSchmidt_expSystem hposn hinjn N
  rw [coIdx_self] at hkey
  rw [prod_coIdx hn (fun m => (((lam m : ℝ) : ℂ) + ((lam n : ℝ) : ℂ)))] at hkey
  rw [prod_coIdx hn (fun m => (((lam m : ℝ) : ℂ) - ((lam n : ℝ) : ℂ)))] at hkey
  exact hkey

end

end GaloisForLFunctions.HTGeometry
