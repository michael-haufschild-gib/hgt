import GaloisForLFunctions.HTGeometry.MeromorphicLaurentCoefficient

/-!
# Differentiating the Laurent transform

Differentiation shifts the Laurent index down by one and multiplies by the index:

`c_ℓ(f′, a) = (ℓ + 1) · c_{ℓ+1}(f, a)`.

The proof is at the level of clearing shifts.  With `g(t) = tᵏ f(a + t)` analytic at the origin, the
clearing shift of `f′` at exponent `k + 1` is `t·g′(t) − k·g(t)` off the origin, and both sides
vanish at the origin, so the identity holds on a whole neighbourhood.  Reading Taylor coefficients,
`t·g′` shifts the index by the index itself, and the two contributions combine to `m − k = ℓ + 1`.

Mathlib has no Laurent calculus at all; this is the differentiation rule of the corpus's transform.

* `taylorCoeffZero_deriv`, `taylorCoeffZero_id_mul_deriv`;
* `laurentCoeff_deriv` — the differentiation law;
* `laurentCoeff_iteratedDeriv` — its iterate.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Topology

/-- Taylor coefficients only depend on the germ at the origin. -/
theorem taylorCoeffZero_congr {g h : ℂ → ℂ} (hgh : g =ᶠ[𝓝 (0 : ℂ)] h) (m : ℕ) :
    taylorCoeffZero g m = taylorCoeffZero h m := by
  rw [taylorCoeffZero, taylorCoeffZero, Filter.EventuallyEq.iteratedDeriv_eq m hgh]

/-- **Taylor coefficients of a derivative.** -/
theorem taylorCoeffZero_deriv (g : ℂ → ℂ) (j : ℕ) :
    taylorCoeffZero (deriv g) j = ((j : ℂ) + 1) * taylorCoeffZero g (j + 1) := by
  have hfac : (((j + 1).factorial : ℂ)) = ((j : ℂ) + 1) * (j.factorial : ℂ) := by
    rw [Nat.factorial_succ]
    push_cast
    ring
  have hjne : ((j.factorial : ℂ)) ≠ 0 := Nat.cast_ne_zero.mpr j.factorial_ne_zero
  have hj1 : ((j : ℂ) + 1) ≠ 0 := by
    have hcast : ((j : ℂ) + 1) = ((j + 1 : ℕ) : ℂ) := by push_cast; ring
    rw [hcast]
    exact Nat.cast_ne_zero.mpr (Nat.succ_ne_zero j)
  rw [taylorCoeffZero, taylorCoeffZero, ← iteratedDeriv_succ', hfac]
  field_simp

/-- **Taylor coefficients of `t · g′(t)`.** -/
theorem taylorCoeffZero_id_mul_deriv {g : ℂ → ℂ} (hg : AnalyticAt ℂ g 0) (m : ℕ) :
    taylorCoeffZero (fun t => t * deriv g t) m = (m : ℂ) * taylorCoeffZero g m := by
  have hd : AnalyticAt ℂ (deriv g) 0 := hg.deriv
  have h := taylorCoeffZero_pow_mul hd 1 m
  simp only [pow_one] at h
  rw [h]
  by_cases hm : 1 ≤ m
  · rw [if_pos hm]
    obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    rw [taylorCoeffZero_deriv]
    push_cast
    ring
  · rw [if_neg hm]
    have hm0 : m = 0 := by omega
    subst hm0
    simp

/-- The clearing shift of a derivative, in terms of the clearing shift of the function. -/
theorem laurentShift_deriv_eventuallyEq {f : ℂ → ℂ} {a : ℂ} (hf : MeromorphicAt f a) {k : ℕ}
    (hk : k ≠ 0) :
    laurentShift (deriv f) a (k + 1)
      =ᶠ[𝓝 (0 : ℂ)] fun t => t * deriv (laurentShift f a k) t - (k : ℂ) * laurentShift f a k t := by
  have hev : ∀ᶠ t : ℂ in 𝓝[≠] (0 : ℂ), laurentShift (deriv f) a (k + 1) t
      = t * deriv (laurentShift f a k) t - (k : ℂ) * laurentShift f a k t := by
    have han : ∀ᶠ z in 𝓝[≠] a, AnalyticAt ℂ f z := hf.eventually_analyticAt
    filter_upwards [(tendsto_const_add_nhdsNE a).eventually han] with t hft
    have hfd : DifferentiableAt ℂ f (a + t) := hft.differentiableAt
    have hcomp : HasDerivAt (fun s : ℂ => f (a + s)) (deriv f (a + t)) t := by
      have hinner : HasDerivAt (fun s : ℂ => a + s) 1 t := by
        simpa using (hasDerivAt_id t).const_add a
      have hc := hfd.hasDerivAt.comp t hinner
      rw [mul_one] at hc
      exact hc
    have hpow : HasDerivAt (fun s : ℂ => s ^ k) ((k : ℂ) * t ^ (k - 1)) t := hasDerivAt_pow k t
    have hgd : HasDerivAt (laurentShift f a k)
        ((k : ℂ) * t ^ (k - 1) * f (a + t) + t ^ k * deriv f (a + t)) t := hpow.mul hcomp
    rw [hgd.deriv]
    simp only [laurentShift]
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    push_cast
    ring
  have h0 : laurentShift (deriv f) a (k + 1) 0
      = 0 * deriv (laurentShift f a k) 0 - (k : ℂ) * laurentShift f a k 0 := by
    rw [laurentShift_zero_of_ne_zero _ _ (by omega : k + 1 ≠ 0),
      laurentShift_zero_of_ne_zero _ _ hk]
    ring
  have hfilter : (𝓝 (0 : ℂ)) = 𝓝[≠] (0 : ℂ) ⊔ pure 0 :=
    (nhdsNE_sup_pure (0 : ℂ)).symm
  show ∀ᶠ t : ℂ in 𝓝 (0 : ℂ), laurentShift (deriv f) a (k + 1) t
      = t * deriv (laurentShift f a k) t - (k : ℂ) * laurentShift f a k t
  rw [hfilter, Filter.eventually_sup]
  exact ⟨hev, by simpa using h0⟩

/-- **The differentiation law of the Laurent transform.** -/
theorem laurentCoeff_deriv {f : ℂ → ℂ} {a : ℂ} (hf : MeromorphicAt f a) (ℓ : ℤ) :
    laurentCoeff (deriv f) a ℓ = ((ℓ : ℂ) + 1) * laurentCoeff f a (ℓ + 1) := by
  obtain ⟨k, hkge, hgk⟩ := exists_analyticAt_laurentShift_ge hf (max 1 (ℓ + 1).natAbs)
  have hk1 : 1 ≤ k := le_trans (le_max_left _ _) hkge
  have hkabs : (ℓ + 1).natAbs ≤ k := le_trans (le_max_right _ _) hkge
  have hkpos : (0 : ℤ) ≤ ℓ + 1 + (k : ℤ) := by omega
  set g : ℂ → ℂ := laurentShift f a k with hgdef
  set m : ℕ := (ℓ + ((k + 1 : ℕ) : ℤ)).toNat with hmdef
  have hmodel : AnalyticAt ℂ (fun t : ℂ => t * deriv g t - (k : ℂ) * g t) 0 := by
    refine AnalyticAt.sub ?_ ?_
    · exact (analyticAt_id).mul hgk.deriv
    · exact analyticAt_const.mul hgk
  have hev := laurentShift_deriv_eventuallyEq hf (by omega : k ≠ 0)
  have hshift : AnalyticAt ℂ (laurentShift (deriv f) a (k + 1)) 0 := hmodel.congr hev.symm
  have hsum : (0 : ℤ) ≤ ℓ + ((k + 1 : ℕ) : ℤ) := by push_cast; omega
  rw [laurentCoeff_eq_taylorCoeffZero hshift hsum, ← hmdef, taylorCoeffZero_congr hev m]
  -- split the model
  have hsplit : (fun t : ℂ => t * deriv g t - (k : ℂ) * g t)
      = fun t : ℂ => ∑ i : Fin 2,
        (![1, -(k : ℂ)] i) * (![fun t : ℂ => t * deriv g t, g] i) t := by
    funext t
    rw [Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    ring
  rw [hsplit, taylorCoeffZero_sum Finset.univ _ _ m (by
    intro i _
    fin_cases i
    · exact (analyticAt_id).mul hgk.deriv
    · exact hgk), Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [taylorCoeffZero_id_mul_deriv hgk]
  have hg2 : taylorCoeffZero g m = laurentCoeff f a (ℓ + 1) := by
    rw [laurentCoeff_eq_taylorCoeffZero hgk (by omega : (0 : ℤ) ≤ (ℓ + 1) + (k : ℤ))]
    congr 1
    rw [hmdef]
    push_cast
    omega
  have hmk : (m : ℂ) - (k : ℂ) = (ℓ : ℂ) + 1 := by
    have hmz : (m : ℤ) = ℓ + 1 + (k : ℤ) := by
      rw [hmdef]
      push_cast
      omega
    have := congrArg (fun n : ℤ => (n : ℂ)) hmz
    push_cast at this
    linear_combination this
  rw [hg2]
  linear_combination (laurentCoeff f a (ℓ + 1)) * hmk

/-- **The iterated differentiation law.** -/
theorem laurentCoeff_iteratedDeriv {f : ℂ → ℂ} {a : ℂ} :
    ∀ (j : ℕ) (ℓ : ℤ), MeromorphicAt (iteratedDeriv j f) a →
      laurentCoeff (iteratedDeriv (j + 1) f) a ℓ
        = ((ℓ : ℂ) + 1) * laurentCoeff (iteratedDeriv j f) a (ℓ + 1) := by
  intro j ℓ hj
  rw [iteratedDeriv_succ]
  exact laurentCoeff_deriv hj ℓ

end GaloisForLFunctions.HTGeometry
