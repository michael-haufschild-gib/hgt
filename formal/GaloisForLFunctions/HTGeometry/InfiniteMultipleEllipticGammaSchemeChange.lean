import GaloisForLFunctions.HTGeometry.InfiniteMultipleEllipticGammaRealSpectrum

/-!
# Exact finite-genus scheme changes

Every two convergent Weierstrass genera differ by the exponential of a finite polynomial
counterterm.  The identity is stated multiplicatively, so it remains valid at zeros and requires
no cancellation.
-/

namespace HTGeometry

open scoped BigOperators

/-- Counterterm added when the primary-factor genus is raised from `g` to `h`. -/
noncomputable def primarySchemeCounterterm (g h : ℕ) (z : ℂ) : ℂ :=
  ∑ k ∈ Finset.Ico g h, z ^ (k + 1) / (k + 1 : ℂ)

theorem primaryExponent_scheme_change {g h : ℕ} (hgh : g ≤ h) (z : ℂ) :
    primaryExponent h z =
      primaryExponent g z + primarySchemeCounterterm g h z := by
  exact (Finset.sum_range_add_sum_Ico
    (fun k => z ^ (k + 1) / (k + 1 : ℂ)) hgh).symm

theorem primaryFactor_scheme_change {g h : ℕ} (hgh : g ≤ h) (z : ℂ) :
    primaryFactor h z =
      primaryFactor g z * Complex.exp (primarySchemeCounterterm g h z) := by
  rw [primaryFactor, primaryFactor, primaryExponent_scheme_change hgh,
    Complex.exp_add]
  ring

/-- The sum of all local genus counterterms over the occupation spectrum. -/
noncomputable def infiniteGenusCounterterm {ι : Type*}
    (g h : ℕ) (p : ι → ℂ) (x : ℂ) : ℂ :=
  ∑' ν : ι →₀ ℕ,
    primarySchemeCounterterm g h (x * nomeMonomial p ν)

theorem infiniteGenusCounterterm_summable {ι : Type*}
    {g h : ℕ} (p : ι → ℂ) (hp_lt : ∀ a, ‖p a‖ < 1)
    (hsum : Summable (fun a => ‖p a‖ ^ (g + 1))) (x : ℂ) :
    Summable (fun ν : ι →₀ ℕ =>
      primarySchemeCounterterm g h (x * nomeMonomial p ν)) := by
  rw [show
      (fun ν : ι →₀ ℕ =>
        primarySchemeCounterterm g h (x * nomeMonomial p ν)) =
        (fun ν => ∑ k ∈ Finset.Ico g h,
          (x * nomeMonomial p ν) ^ (k + 1) / (k + 1 : ℂ)) by
    funext ν
    rfl]
  apply summable_sum
  intro k hk
  have hgk : g + 1 ≤ k + 1 := Nat.succ_le_succ (Finset.mem_Ico.mp hk).1
  have hpk : Summable (fun a => ‖p a‖ ^ (k + 1)) := by
    apply hsum.of_nonneg_of_le
    · intro a
      positivity
    · intro a
      exact pow_le_pow_of_le_one (norm_nonneg _)
        (le_of_lt (hp_lt a)) hgk
  have hqnorm :
      Summable (fun ν : ι →₀ ℕ => ‖nomeMonomial p ν‖ ^ (k + 1)) :=
    (summable_nomeMonomial_pow_iff k p hp_lt).2 hpk
  have hq :
      Summable (fun ν : ι →₀ ℕ => nomeMonomial p ν ^ (k + 1)) := by
    exact (show
      Summable (fun ν : ι →₀ ℕ =>
        ‖nomeMonomial p ν ^ (k + 1)‖) by
          simpa only [norm_pow] using hqnorm).of_norm
  have hterm :=
    (hq.mul_left (x ^ (k + 1))).div_const (k + 1 : ℂ)
  convert hterm using 1
  funext ν
  rw [mul_pow]

/-- The global counterterm is the finite sum of occupation moments at the newly added powers. -/
theorem infiniteGenusCounterterm_eq_moment_sum {ι : Type*}
    {g h : ℕ} (p : ι → ℂ) (hp_lt : ∀ a, ‖p a‖ < 1)
    (hsum : Summable (fun a => ‖p a‖ ^ (g + 1))) (x : ℂ) :
    infiniteGenusCounterterm g h p x =
      ∑ k ∈ Finset.Ico g h,
        (x ^ (k + 1) / (k + 1 : ℂ)) *
          ∑' ν : ι →₀ ℕ, nomeMonomial p ν ^ (k + 1) := by
  change
    (∑' ν : ι →₀ ℕ, ∑ k ∈ Finset.Ico g h,
      (x * nomeMonomial p ν) ^ (k + 1) / (k + 1 : ℂ)) = _
  have hterms : ∀ k ∈ Finset.Ico g h,
      Summable (fun ν : ι →₀ ℕ =>
        (x * nomeMonomial p ν) ^ (k + 1) / (k + 1 : ℂ)) := by
    intro k hk
    have hgk : g + 1 ≤ k + 1 := Nat.succ_le_succ (Finset.mem_Ico.mp hk).1
    have hpk : Summable (fun a => ‖p a‖ ^ (k + 1)) := by
      apply hsum.of_nonneg_of_le
      · intro a
        positivity
      · intro a
        exact pow_le_pow_of_le_one (norm_nonneg _)
          (le_of_lt (hp_lt a)) hgk
    have hqnorm :=
      (summable_nomeMonomial_pow_iff k p hp_lt).2 hpk
    have hq : Summable
        (fun ν : ι →₀ ℕ => nomeMonomial p ν ^ (k + 1)) := by
      exact (show
        Summable (fun ν : ι →₀ ℕ =>
          ‖nomeMonomial p ν ^ (k + 1)‖) by
            simpa only [norm_pow] using hqnorm).of_norm
    convert (hq.mul_left (x ^ (k + 1))).div_const (k + 1 : ℂ) using 1
    funext ν
    rw [mul_pow]
  rw [Summable.tsum_finsetSum hterms]
  apply Finset.sum_congr rfl
  intro k hk
  have hq : Summable
      (fun ν : ι →₀ ℕ => nomeMonomial p ν ^ (k + 1)) := by
    have hgk : g + 1 ≤ k + 1 := Nat.succ_le_succ (Finset.mem_Ico.mp hk).1
    have hpk : Summable (fun a => ‖p a‖ ^ (k + 1)) := by
      apply hsum.of_nonneg_of_le
      · intro a
        positivity
      · intro a
        exact pow_le_pow_of_le_one (norm_nonneg _)
          (le_of_lt (hp_lt a)) hgk
    have hqnorm :=
      (summable_nomeMonomial_pow_iff k p hp_lt).2 hpk
    exact (show
      Summable (fun ν : ι →₀ ℕ =>
        ‖nomeMonomial p ν ^ (k + 1)‖) by
          simpa only [norm_pow] using hqnorm).of_norm
  rw [show
      (fun ν : ι →₀ ℕ =>
        (x * nomeMonomial p ν) ^ (k + 1) / (k + 1 : ℂ)) =
        (fun ν =>
          (x ^ (k + 1) / (k + 1 : ℂ)) *
            nomeMonomial p ν ^ (k + 1)) by
    funext ν
    rw [mul_pow]
    ring]
  rw [hq.tsum_mul_left]

/-- **Exact scheme-change law.**  Raising the genus changes the infinite product only by a finite
entire counterterm.  The multiplication form is valid even at zeros. -/
theorem infiniteMultipleEllipticGamma_scheme_change {ι : Type*}
    {g h : ℕ} (hgh : g ≤ h) (p : ι → ℂ)
    (hp_ne : ∀ a, p a ≠ 0) (hp_lt : ∀ a, ‖p a‖ < 1)
    (hsum : Summable (fun a => ‖p a‖ ^ (g + 1))) (x : ℂ) :
    infiniteMultipleEllipticGamma h p x =
      infiniteMultipleEllipticGamma g p x *
        Complex.exp (infiniteGenusCounterterm g h p x) := by
  have hh_sum : Summable (fun a => ‖p a‖ ^ (h + 1)) := by
    apply hsum.of_nonneg_of_le
    · intro a
      positivity
    · intro a
      exact pow_le_pow_of_le_one (norm_nonneg _)
        (le_of_lt (hp_lt a)) (Nat.succ_le_succ hgh)
  have hgProd :=
    (infiniteMultipleEllipticGamma_hasProdLocallyUniformlyOn
      g p hp_ne hp_lt hsum).hasProd (Set.mem_univ x)
  have hhProd :=
    (infiniteMultipleEllipticGamma_hasProdLocallyUniformlyOn
      h p hp_ne hp_lt hh_sum).hasProd (Set.mem_univ x)
  have hcounter :=
    infiniteGenusCounterterm_summable (g := g) (h := h) p hp_lt hsum x
  have hexp : HasProd
      (fun ν : ι →₀ ℕ =>
        Complex.exp (primarySchemeCounterterm g h
          (x * nomeMonomial p ν)))
      (Complex.exp (infiniteGenusCounterterm g h p x)) := by
    simpa [Function.comp_def, infiniteGenusCounterterm] using
      hcounter.hasSum.cexp
  have hchanged := hgProd.mul hexp
  have hchanged' : HasProd
      (fun ν : ι →₀ ℕ =>
        primaryFactor h (x * nomeMonomial p ν))
      (infiniteMultipleEllipticGamma g p x *
        Complex.exp (infiniteGenusCounterterm g h p x)) := by
    apply hchanged.congr_fun
    intro ν
    exact primaryFactor_scheme_change hgh
      (x * nomeMonomial p ν)
  exact hhProd.unique hchanged'

/-- All admissible genera have exactly the same zero set. -/
theorem infiniteMultipleEllipticGamma_scheme_change_eq_zero_iff {ι : Type*}
    {g h : ℕ} (hgh : g ≤ h) (p : ι → ℂ)
    (hp_ne : ∀ a, p a ≠ 0) (hp_lt : ∀ a, ‖p a‖ < 1)
    (hsum : Summable (fun a => ‖p a‖ ^ (g + 1))) (x : ℂ) :
    infiniteMultipleEllipticGamma h p x = 0 ↔
      infiniteMultipleEllipticGamma g p x = 0 := by
  rw [infiniteMultipleEllipticGamma_scheme_change
    hgh p hp_ne hp_lt hsum x]
  simp

end HTGeometry
