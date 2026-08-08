import GaloisForLFunctions.HTGeometry.MeromorphicLaurentLeading
import GaloisForLFunctions.HTGeometry.MeromorphicLaurentDerivative

/-!
# Below the order the Laurent coefficients vanish

Writing a germ of order `n` as `(z-a)ⁿ·g` with `g` analytic and nonvanishing, a clearing shift at a
large enough exponent `k` is `t^{k+n}·g(a+t)` on a whole neighbourhood of the origin, whose Taylor
coefficients vanish below index `k+n`.  Reading the Laurent coefficient at `ℓ < n` asks for index
`ℓ+k < k+n`, so it is zero.

With the leading-coefficient law this pins the order exactly: `meromorphicOrderAt f a` is the least
index carrying a nonzero Laurent coefficient.

* `laurentCoeff_eq_zero_of_lt_meromorphicOrderAt`;
* `meromorphicOrderAt_le_of_laurentCoeff_ne_zero`.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Topology

/-- **Below the order every Laurent coefficient vanishes.** -/
theorem laurentCoeff_eq_zero_of_lt_meromorphicOrderAt {f : ℂ → ℂ} {a : ℂ} (hf : MeromorphicAt f a)
    {ℓ : ℤ} (h : (ℓ : WithTop ℤ) < meromorphicOrderAt f a) :
    laurentCoeff f a ℓ = 0 := by
  rcases eq_or_ne (meromorphicOrderAt f a) ⊤ with htop | hne
  · have hzero : f =ᶠ[𝓝[≠] a] 0 := meromorphicOrderAt_eq_top_iff.mp htop
    exact (eventuallyEq_zero_nhdsNE_iff_forall_laurentCoeff_eq_zero hf).mp hzero ℓ
  obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp hne
  have hln : ℓ < n := by
    rw [← hn] at h
    exact_mod_cast h
  obtain ⟨g, hg, hga, hfg⟩ := (meromorphicOrderAt_eq_int_iff hf).mp hn.symm
  set k : ℕ := max (max (1 - n).toNat ℓ.natAbs) 1 with hkdef
  have hk0 : k ≠ 0 := by
    have : (1 : ℕ) ≤ k := le_max_right _ _
    omega
  have hk1 : (1 : ℤ) ≤ (k : ℤ) + n := by
    have h1 : ((1 - n).toNat : ℤ) ≤ (k : ℤ) := by
      exact_mod_cast (le_max_left (1 - n).toNat ℓ.natAbs).trans (le_max_left _ 1)
    omega
  have hk2 : (0 : ℤ) ≤ ℓ + (k : ℤ) := by
    have h2 : (ℓ.natAbs : ℤ) ≤ (k : ℤ) := by
      exact_mod_cast (le_max_right (1 - n).toNat ℓ.natAbs).trans (le_max_left _ 1)
    omega
  set j : ℕ := ((k : ℤ) + n).toNat with hjdef
  have hj : (j : ℤ) = (k : ℤ) + n := by omega
  have hG : AnalyticAt ℂ (fun t : ℂ => g (a + t)) 0 := by
    have hadd : AnalyticAt ℂ (fun t : ℂ => a + t) 0 := by fun_prop
    have hg0 : AnalyticAt ℂ g ((fun t : ℂ => a + t) 0) := by simpa using hg
    exact hg0.comp hadd
  have hmodel : AnalyticAt ℂ (fun t : ℂ => t ^ j * g (a + t)) 0 :=
    (by fun_prop : AnalyticAt ℂ (fun t : ℂ => t ^ j) 0).mul hG
  have hshift : laurentShift f a k =ᶠ[𝓝 (0 : ℂ)] fun t => t ^ j * g (a + t) := by
    have hev : ∀ᶠ t : ℂ in 𝓝[≠] (0 : ℂ), laurentShift f a k t = t ^ j * g (a + t) := by
      filter_upwards [(tendsto_const_add_nhdsNE a).eventually hfg, self_mem_nhdsWithin]
        with t ht htne
      have htne' : t ≠ 0 := htne
      have hval : f (a + t) = (a + t - a) ^ n * g (a + t) := by simpa using ht
      rw [laurentShift, hval, show a + t - a = t from by ring, ← zpow_natCast t k, ← mul_assoc,
        ← zpow_add₀ htne', ← zpow_natCast t j, hj]
    have h0 : laurentShift f a k 0 = (0 : ℂ) ^ j * g (a + 0) := by
      have hj0 : j ≠ 0 := by
        intro h0
        rw [h0] at hj
        omega
      rw [laurentShift_zero_of_ne_zero _ _ hk0, zero_pow hj0, zero_mul]
    have hfilter : (𝓝 (0 : ℂ)) = 𝓝[≠] (0 : ℂ) ⊔ pure 0 := (nhdsNE_sup_pure (0 : ℂ)).symm
    show ∀ᶠ t : ℂ in 𝓝 (0 : ℂ), laurentShift f a k t = t ^ j * g (a + t)
    rw [hfilter, Filter.eventually_sup]
    exact ⟨hev, by simpa using h0⟩
  have hana : AnalyticAt ℂ (laurentShift f a k) 0 := hmodel.congr hshift.symm
  rw [laurentCoeff_eq_taylorCoeffZero hana hk2, taylorCoeffZero_congr hshift,
    taylorCoeffZero_pow_mul hG j (ℓ + (k : ℤ)).toNat, if_neg (by omega)]

/-- **A nonzero Laurent coefficient bounds the order.** -/
theorem meromorphicOrderAt_le_of_laurentCoeff_ne_zero {f : ℂ → ℂ} {a : ℂ} (hf : MeromorphicAt f a)
    {ℓ : ℤ} (h : laurentCoeff f a ℓ ≠ 0) :
    meromorphicOrderAt f a ≤ (ℓ : WithTop ℤ) := by
  by_contra hcon
  exact h (laurentCoeff_eq_zero_of_lt_meromorphicOrderAt hf (not_le.mp hcon))

end GaloisForLFunctions.HTGeometry
