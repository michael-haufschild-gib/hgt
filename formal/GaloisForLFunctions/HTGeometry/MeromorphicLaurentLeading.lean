import GaloisForLFunctions.HTGeometry.MeromorphicLaurentTranslation

/-!
# The leading Laurent coefficient of a pole does not vanish

Writing a germ of order `n < 0` as `(z-a)ⁿ·g` with `g` analytic and nonvanishing, the clearing shift
at exponent `1 - n` is `t·g(a+t)` on a whole neighbourhood of the origin — including the origin,
because both sides vanish there.  Its Taylor coefficient at index `1` is `g(a)`, so the Laurent
coefficient of `f` at the order itself is `g(a) ≠ 0`.

Together with the corpus's converse this makes the principal part a faithful record of the order: a
germ all of whose negative Laurent coefficients vanish has nonnegative order, hence is analytic after
removing the point.

* `laurentCoeff_leading_ne_zero`;
* `meromorphicOrderAt_nonneg_of_laurentCoeff_neg_eq_zero`.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Topology

/-- **The leading Laurent coefficient of a pole is nonzero.** -/
theorem laurentCoeff_leading_ne_zero {f : ℂ → ℂ} {a : ℂ} {n : ℤ} (hn : n < 0)
    (hf : MeromorphicAt f a) (hord : meromorphicOrderAt f a = n) :
    laurentCoeff f a n ≠ 0 := by
  obtain ⟨g, hg, hga, hfg⟩ := (meromorphicOrderAt_eq_int_iff hf).mp hord
  set k : ℕ := (1 - n).toNat with hkdef
  have hk : (k : ℤ) = 1 - n := by omega
  have hk1 : 1 ≤ k := by omega
  have hG : AnalyticAt ℂ (fun t : ℂ => g (a + t)) 0 := by
    have hadd : AnalyticAt ℂ (fun t : ℂ => a + t) 0 := by fun_prop
    have hg0 : AnalyticAt ℂ g ((fun t : ℂ => a + t) 0) := by simpa using hg
    exact hg0.comp hadd
  have hmodel : AnalyticAt ℂ (fun t : ℂ => t * g (a + t)) 0 := analyticAt_id.mul hG
  have hshift : laurentShift f a k =ᶠ[𝓝 (0 : ℂ)] fun t => t * g (a + t) := by
    have hev : ∀ᶠ t : ℂ in 𝓝[≠] (0 : ℂ), laurentShift f a k t = t * g (a + t) := by
      filter_upwards [(tendsto_const_add_nhdsNE a).eventually hfg, self_mem_nhdsWithin]
        with t ht htne
      have htne' : t ≠ 0 := htne
      have hval : f (a + t) = (a + t - a) ^ n * g (a + t) := by simpa using ht
      rw [laurentShift, hval, show a + t - a = t from by ring, ← zpow_natCast t k, ← mul_assoc,
        ← zpow_add₀ htne', hk]
      norm_num
    have h0 : laurentShift f a k 0 = 0 * g (a + 0) := by
      rw [laurentShift_zero_of_ne_zero _ _ (by omega : k ≠ 0), zero_mul]
    have hfilter : (𝓝 (0 : ℂ)) = 𝓝[≠] (0 : ℂ) ⊔ pure 0 := (nhdsNE_sup_pure (0 : ℂ)).symm
    show ∀ᶠ t : ℂ in 𝓝 (0 : ℂ), laurentShift f a k t = t * g (a + t)
    rw [hfilter, Filter.eventually_sup]
    exact ⟨hev, by simpa using h0⟩
  have hana : AnalyticAt ℂ (laurentShift f a k) 0 := hmodel.congr hshift.symm
  have hval : laurentCoeff f a n = g a := by
    rw [laurentCoeff_eq_taylorCoeffZero hana (by omega : (0 : ℤ) ≤ n + (k : ℤ))]
    rw [taylorCoeffZero, Filter.EventuallyEq.iteratedDeriv_eq _ hshift]
    have hidx : (n + (k : ℤ)).toNat = 1 := by omega
    rw [hidx]
    have hpm := taylorCoeffZero_pow_mul hG 1 1
    simp only [pow_one] at hpm
    rw [taylorCoeffZero] at hpm
    norm_num at hpm ⊢
    rw [hpm, taylorCoeffZero]
    simp
  rw [hval]
  exact hga

/-- **Vanishing principal part forces nonnegative order.** -/
theorem meromorphicOrderAt_nonneg_of_laurentCoeff_neg_eq_zero {f : ℂ → ℂ} {a : ℂ}
    (hf : MeromorphicAt f a) (h : ∀ ℓ : ℤ, ℓ < 0 → laurentCoeff f a ℓ = 0) :
    0 ≤ meromorphicOrderAt f a := by
  rcases eq_or_ne (meromorphicOrderAt f a) ⊤ with htop | hne
  · rw [htop]
    exact le_top
  obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp hne
  by_contra hcon
  have hneg : n < 0 := by
    by_contra hpos
    exact hcon (by rw [← hn]; exact_mod_cast (by omega : (0 : ℤ) ≤ n))
  exact laurentCoeff_leading_ne_zero hneg hf hn.symm (h n hneg)

end GaloisForLFunctions.HTGeometry
