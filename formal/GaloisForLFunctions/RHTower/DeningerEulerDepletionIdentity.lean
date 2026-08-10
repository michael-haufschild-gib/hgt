import GaloisForLFunctions.RHTower.DeningerDepletedPoisson

/-!
# The Euler-depletion identity

Translating the Poisson sum by `log p` reindexes it onto the multiples of `p`, so the periodization
defect deletes exactly the `p`-Euler orbit:

`Δ_p Z f (t) = ∑_{n ≥ 1, p ∤ n} f(n e^t)`.

No Euler product continuation is used — the subtracted sum *is* the subseries indexed by multiples
of `p`, reindexed by the injection `k ↦ p(k+1) - 1`.

* `deningerEulerDepletedLog` : the `p`-depleted Poisson sum.
* `deningerEulerDepletion` : **`(3)`: `Δ_p Z f = Z^{(p)} f`.**
-/

namespace RHTower

open SchwartzMap

noncomputable section

/-- The `p`-depleted Poisson sum: the dilation orbit with the `p`-Euler orbit deleted. -/
def deningerEulerDepletedLog (p : ℕ) (f : 𝓢(ℝ, ℂ)) (t : ℝ) : ℂ :=
  ∑' n : ℕ, if p ∣ (n + 1) then 0 else (f : ℝ → ℂ) (((n : ℝ) + 1) * Real.exp t)

/-- The multiples of `p` inside the shifted index set, as an injection. -/
private def deningerMultipleIndex (p : ℕ) (k : ℕ) : ℕ := p * (k + 1) - 1

private theorem deningerMultipleIndex_succ {p : ℕ} (hp : 1 ≤ p) (k : ℕ) :
    deningerMultipleIndex p k + 1 = p * (k + 1) := by
  have h : 1 ≤ p * (k + 1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
  rw [deningerMultipleIndex]
  omega

private theorem deningerMultipleIndex_injective {p : ℕ} (hp : 1 ≤ p) :
    Function.Injective (deningerMultipleIndex p) := by
  intro a b hab
  have h := congrArg (· + 1) hab
  rw [deningerMultipleIndex_succ hp, deningerMultipleIndex_succ hp] at h
  have hp0 : 0 < p := hp
  have : a + 1 = b + 1 := Nat.eq_of_mul_eq_mul_left hp0 h
  omega

/-- **`(3)`: the Euler-depletion identity.**  The periodization defect of the Poisson sum at the
period `log p` is the Poisson sum over the indices prime to `p`. -/
theorem deningerEulerDepletion {p : ℕ} (hp : 1 ≤ p) (f : 𝓢(ℝ, ℂ)) (t : ℝ) :
    deningerPoissonLog f t - deningerPoissonLog f (t + Real.log p)
      = deningerEulerDepletedLog p f t := by
  have hppos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  set g : ℕ → ℂ := fun n => (f : ℝ → ℂ) (((n : ℝ) + 1) * Real.exp t) with hgdef
  have hsum : Summable g := summable_deningerPoissonLogTerm f t
  set F : ℕ → ℂ := fun n => if p ∣ (n + 1) then g n else 0 with hFdef
  have hFsum : Summable F := by
    refine Summable.of_norm_bounded hsum.norm fun n => ?_
    rw [hFdef]
    by_cases hd : p ∣ (n + 1)
    · simp [hd]
    · simp [hd]
  -- the subtracted series is the subseries over the multiples of `p`
  have hshift : deningerPoissonLog f (t + Real.log p) = ∑' n : ℕ, F n := by
    have hsupp : Function.support F ⊆ Set.range (deningerMultipleIndex p) := by
      intro n hn
      have hd : p ∣ (n + 1) := by
        by_contra hcon
        rw [Function.mem_support, hFdef] at hn
        simp [hcon] at hn
      obtain ⟨m, hm⟩ := hd
      have hm0 : 1 ≤ m := by
        rcases Nat.eq_zero_or_pos m with rfl | h
        · omega
        · exact h
      refine ⟨m - 1, ?_⟩
      have : p * (m - 1 + 1) = p * m := by
        congr 1
        omega
      rw [deningerMultipleIndex, this, ← hm]
      omega
    have hreindex := (deningerMultipleIndex_injective hp).tsum_eq hsupp
    rw [← hreindex, deningerPoissonLog]
    refine tsum_congr fun k => ?_
    have hdvd : p ∣ (deningerMultipleIndex p k + 1) := by
      rw [deningerMultipleIndex_succ hp]
      exact ⟨k + 1, rfl⟩
    rw [hFdef]
    simp only [hdvd, if_true]
    rw [hgdef]
    have hcast : ((deningerMultipleIndex p k : ℕ) : ℝ) + 1 = (p : ℝ) * ((k : ℝ) + 1) := by
      have h := deningerMultipleIndex_succ hp k
      have : ((deningerMultipleIndex p k + 1 : ℕ) : ℝ) = ((p * (k + 1) : ℕ) : ℝ) := by
        exact_mod_cast congrArg (fun m : ℕ => (m : ℝ)) h
      push_cast at this
      linarith
    have hexp : Real.exp (t + Real.log (p : ℝ)) = Real.exp t * (p : ℝ) := by
      rw [Real.exp_add, Real.exp_log hppos]
    have hstep : (((deningerMultipleIndex p k : ℕ) : ℝ) + 1) * Real.exp t
        = ((k : ℝ) + 1) * Real.exp (t + Real.log (p : ℝ)) := by
      rw [hexp, hcast]
      ring
    show (f : ℝ → ℂ) (((k : ℝ) + 1) * Real.exp (t + Real.log (p : ℝ)))
      = (f : ℝ → ℂ) ((((deningerMultipleIndex p k : ℕ) : ℝ) + 1) * Real.exp t)
    exact congrArg (fun y : ℝ => (f : ℝ → ℂ) y) hstep.symm
  rw [hshift, deningerPoissonLog, deningerEulerDepletedLog, ← hsum.tsum_sub hFsum]
  refine tsum_congr fun n => ?_
  rw [hFdef, hgdef]
  by_cases hd : p ∣ (n + 1)
  · simp [hd]
  · simp [hd]

end

end RHTower
