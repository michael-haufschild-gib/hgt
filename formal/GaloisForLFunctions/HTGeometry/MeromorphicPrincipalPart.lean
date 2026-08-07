import GaloisForLFunctions.HTGeometry.MeromorphicLaurentCoefficient

/-!
# Principal parts of a meromorphic germ

A function meromorphic at `a` splits, at every point other than `a`, as an analytic germ at `a`
plus its principal part

`∑_{j < k} c_{j-k} (s - a)^{j-k}`,

whose coefficients are the negative-index Laurent coefficients.  The splitting comes from a finite
Taylor expansion with analytic remainder of a clearing shift `t ↦ t^k f(a+t)`.

* `exists_taylor_remainder` — `F = ∑_{j<k} (taylor coefficient) t^j + t^k H` with `H` analytic.
* `principalPart` — the truncated principal part, written with inverse natural powers so that it is
  visibly analytic away from `a` and vanishes at `a`.
* `eq_add_principalPart` — the splitting, valid at every point other than `a`.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Topology
open scoped BigOperators

/-! ### Taylor expansion with analytic remainder -/

/-- **Finite Taylor expansion with analytic remainder**, in the `taylorCoeffZero` normalization. -/
theorem exists_taylor_remainder {F : ℂ → ℂ} (hF : AnalyticAt ℂ F 0) (k : ℕ) :
    ∃ H : ℂ → ℂ, AnalyticAt ℂ H 0 ∧
      ∀ t : ℂ, F t = (∑ j ∈ Finset.range k, taylorCoeffZero F j * t ^ j) + t ^ k * H t := by
  obtain ⟨H, hH, hEq⟩ := hF.exists_eq_sum_add_pow_mul k
  refine ⟨H, hH, fun t => ?_⟩
  rw [hEq t]
  simp only [smul_eq_mul, taylorCoeffZero]
  congr 1
  exact Finset.sum_congr rfl fun j _ => by ring

/-! ### The principal part -/

/-- The principal part of `f` at `a`, truncated at the clearing exponent `k`: the negative-index
Laurent coefficients against inverse powers of `s - a`.  At `s = a` every term is `0⁻¹ = 0`, so the
principal part vanishes there. -/
noncomputable def principalPart (f : ℂ → ℂ) (a : ℂ) (k : ℕ) : ℂ → ℂ :=
  fun s => ∑ j ∈ Finset.range k, laurentCoeff f a ((j : ℤ) - k) * ((s - a) ^ (k - j))⁻¹

@[simp]
theorem principalPart_self (f : ℂ → ℂ) (a : ℂ) (k : ℕ) : principalPart f a k a = 0 := by
  refine Finset.sum_eq_zero fun j hj => ?_
  have hjk : j < k := Finset.mem_range.mp hj
  have hne : k - j ≠ 0 := by omega
  simp [hne]

/-- Away from `a` the principal part is analytic. -/
theorem analyticAt_principalPart {f : ℂ → ℂ} {a : ℂ} (k : ℕ) {s : ℂ} (hs : s ≠ a) :
    AnalyticAt ℂ (principalPart f a k) s := by
  refine Finset.analyticAt_fun_sum _ fun j _ => analyticAt_const.mul ?_
  refine AnalyticAt.inv ?_ (pow_ne_zero _ (sub_ne_zero.mpr hs))
  exact (analyticAt_id.sub analyticAt_const).pow _

/-- **The principal-part splitting.**  If `t ↦ t^k f(a+t)` is analytic at the origin, then off `a`
the function `f` is an analytic germ at `a` plus its principal part truncated at `k`. -/
theorem eq_add_principalPart {f : ℂ → ℂ} {a : ℂ} {k : ℕ}
    (hk : AnalyticAt ℂ (laurentShift f a k) 0) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g a ∧ ∀ s ≠ a, f s = g s + principalPart f a k s := by
  obtain ⟨H, hH, hEq⟩ := exists_taylor_remainder hk k
  refine ⟨fun s => H (s - a), ?_, ?_⟩
  · have hsub : AnalyticAt ℂ (fun s : ℂ => s - a) a := by fun_prop
    have hH' : AnalyticAt ℂ H ((fun s : ℂ => s - a) a) := by simpa using hH
    exact AnalyticAt.comp (g := H) (f := fun s : ℂ => s - a) (x := a) hH' hsub
  · intro s hs
    have hne : s - a ≠ 0 := sub_ne_zero.mpr hs
    have hpow : (s - a) ^ k ≠ 0 := pow_ne_zero _ hne
    have hshift : laurentShift f a k (s - a) = (s - a) ^ k * f s := by
      simp [laurentShift]
    have hcoeff : ∀ j ∈ Finset.range k,
        taylorCoeffZero (laurentShift f a k) j = laurentCoeff f a ((j : ℤ) - k) := by
      intro j _
      rw [laurentCoeff_eq_taylorCoeffZero hk (by omega)]
      congr 1
      omega
    have hmain := hEq (s - a)
    rw [hshift] at hmain
    have hdiv : f s = (∑ j ∈ Finset.range k,
        taylorCoeffZero (laurentShift f a k) j * (s - a) ^ j) / (s - a) ^ k + H (s - a) := by
      field_simp
      linear_combination hmain
    rw [hdiv, principalPart]
    have hsplit : (∑ j ∈ Finset.range k,
        taylorCoeffZero (laurentShift f a k) j * (s - a) ^ j) / (s - a) ^ k
        = ∑ j ∈ Finset.range k, laurentCoeff f a ((j : ℤ) - k) * ((s - a) ^ (k - j))⁻¹ := by
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun j hj => ?_
      have hjk : j < k := Finset.mem_range.mp hj
      have hkj : (s - a) ^ k = (s - a) ^ (k - j) * (s - a) ^ j := by
        rw [← pow_add]
        congr 1
        omega
      have hnej : (s - a) ^ j ≠ 0 := pow_ne_zero _ hne
      have hnekj : (s - a) ^ (k - j) ≠ 0 := pow_ne_zero _ hne
      rw [hcoeff j hj, mul_div_assoc, hkj]
      congr 1
      field_simp
    rw [hsplit]
    ring

end GaloisForLFunctions.HTGeometry
