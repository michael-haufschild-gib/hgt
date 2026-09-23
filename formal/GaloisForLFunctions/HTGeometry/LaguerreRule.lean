import GaloisForLFunctions.HTGeometry.LaguerreSignChanges

/-!
# Laguerre's rule for exponential sums

For an exponential sum `f(t) = ∑ c i e^{a i t}` with strictly increasing exponents and nonzero
coefficients, the total number of real zeros **counted with multiplicity** is at most the number of
sign changes of the coefficient sequence `c`.

The proof is the Rolle induction on the number of terms.  Normalising the lowest exponent to `0`,
the derivative is an exponential sum with one fewer term whose sign pattern is the tail of `c`, and
Rolle's theorem loses one zero.  When the two lowest coefficients have opposite signs the lost zero
is paid for by the leading sign change.  When they agree in sign the payment comes from the
behaviour at `-∞`: there `f` tends to `c 0` and `f'` tends to `0` with the sign of `c 1`, so `f` and
`f'` both carry the sign of `c 0` far to the left, while the mean value theorem forces `f'` to take
the opposite sign somewhere between that region and the leftmost zero of `f`.  The intermediate
value theorem then produces a zero of `f'` strictly to the left of every zero of `f`, restoring the
count.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

/-! ## An extra critical point to the left -/

/-- If `f` and `f'` are both eventually positive at `-∞` and `f` vanishes at `x₁`, then `f'` has a
zero strictly to the left of `x₁`. -/
theorem exists_deriv_eq_zero_lt {f : ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) {x₁ : ℝ}
    (hx : f x₁ = 0) (hfpos : ∀ᶠ t in atBot, 0 < f t) (hdpos : ∀ᶠ t in atBot, 0 < deriv f t) :
    ∃ ρ, ρ < x₁ ∧ deriv f ρ = 0 := by
  obtain ⟨S, hS⟩ := Filter.eventually_atBot.mp (hfpos.and hdpos)
  have hsS : min S (x₁ - 1) ≤ S := min_le_left _ _
  have hsx : min S (x₁ - 1) < x₁ := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  obtain ⟨hfs, hds⟩ := hS _ hsS
  have hcont : ContinuousOn f (Set.Icc (min S (x₁ - 1)) x₁) := hf.continuous.continuousOn
  have hdiff : DifferentiableOn ℝ f (Set.Ioo (min S (x₁ - 1)) x₁) :=
    (hf.differentiable (by simp)).differentiableOn
  obtain ⟨r, hr, hslope⟩ := exists_deriv_eq_slope f hsx hcont hdiff
  have hdr : deriv f r < 0 := by
    rw [hslope, hx]
    exact div_neg_of_neg_of_pos (by linarith) (by linarith)
  have hdcont : Continuous (deriv f) := (contDiff_deriv hf).continuous
  obtain ⟨ρ, hρmem, hρ⟩ :=
    intermediate_value_Ioo' (le_of_lt hr.1) hdcont.continuousOn ⟨hdr, hds⟩
  exact ⟨ρ, lt_trans hρmem.2 hr.2, hρ⟩

/-- The mirrored statement, for eventually negative sign. -/
theorem exists_deriv_eq_zero_lt' {f : ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) {x₁ : ℝ}
    (hx : f x₁ = 0) (hfneg : ∀ᶠ t in atBot, f t < 0) (hdneg : ∀ᶠ t in atBot, deriv f t < 0) :
    ∃ ρ, ρ < x₁ ∧ deriv f ρ = 0 := by
  have hderiv : deriv (fun t => -f t) = fun t => -deriv f t := by
    funext t
    simp
  have hf' : ContDiff ℝ (⊤ : ℕ∞) (fun t => -f t) := hf.neg
  obtain ⟨ρ, hρlt, hρ⟩ := exists_deriv_eq_zero_lt hf' (x₁ := x₁) (by rw [hx]; ring)
    (by filter_upwards [hfneg] with t ht; linarith)
    (by rw [hderiv]; filter_upwards [hdneg] with t ht; linarith)
  refine ⟨ρ, hρlt, ?_⟩
  rw [hderiv] at hρ
  linarith [hρ]

/-! ## Extending a zero list of the derivative -/

/-- **The gain-one Rolle descent.**  If `f` and `f'` carry a common definite sign at `-∞`, a zero
list of `f` beginning at `x₁` produces a zero list of `f'` of the *same* length: the ordinary Rolle
points inside the configuration, plus one extra critical point strictly left of `x₁`. -/
theorem exists_deriv_zeroList_succ {f : ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hcont : ∀ j : ℕ, Continuous (iteratedDeriv j f))
    (hsign : ((∀ᶠ t in atBot, 0 < f t) ∧ (∀ᶠ t in atBot, 0 < deriv f t)) ∨
             ((∀ᶠ t in atBot, f t < 0) ∧ (∀ᶠ t in atBot, deriv f t < 0)))
    {x₁ : ℝ} {t : List ℝ} (hl : IsZeroList f (x₁ :: t)) :
    ∃ l' : List ℝ, IsZeroList (deriv f) l' ∧ l'.length = t.length + 1 := by
  obtain ⟨u, hu, hulen, huge, _⟩ := exists_zeroList_deriv hcont t x₁ hl
  have hx : f x₁ = 0 := by
    have hcnt : 1 ≤ (x₁ :: t).count x₁ := by
      rw [count_cons_self]; omega
    exact apply_eq_zero_of_vanishesTo hcnt (hl.2 x₁)
  obtain ⟨ρ, hρlt, hρ⟩ : ∃ ρ, ρ < x₁ ∧ deriv f ρ = 0 := by
    rcases hsign with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact exists_deriv_eq_zero_lt hf hx h1 h2
    · exact exists_deriv_eq_zero_lt' hf hx h1 h2
  have hnotmem : ρ ∉ u := fun hmem => absurd (huge ρ hmem) (by linarith)
  refine ⟨ρ :: u, ⟨?_, ?_⟩, by simp [hulen]⟩
  · exact List.pairwise_cons.mpr
      ⟨fun y hy => le_of_lt (lt_of_lt_of_le hρlt (huge y hy)), hu.1⟩
  · intro x
    by_cases hxρ : x = ρ
    · subst hxρ
      rw [count_cons_self, List.count_eq_zero.mpr hnotmem]
      intro j hj
      have hj0 : j = 0 := by omega
      subst hj0
      rwa [iteratedDeriv_zero]
    · rw [count_cons_of_ne hxρ]
      exact hu.2 x

/-! ## Sign of an exponential sum at `-∞` -/

theorem expSum_shift_apply {m : ℕ} (c a : Fin m → ℝ) (α t : ℝ) :
    expSum c (fun i => a i - α) t = Real.exp (-(α * t)) * expSum c a t := by
  rw [← expSum_shift c a α]

/-- An exponential sum with a strictly smallest exponent carries, near `-∞`, the sign of the
coefficient of that exponent. -/
theorem eventually_expSum_pos_atBot_of_min {m : ℕ} (c a : Fin m → ℝ) (i₀ : Fin m)
    (hmin : ∀ i, i ≠ i₀ → a i₀ < a i) (hc : 0 < c i₀) :
    ∀ᶠ t in atBot, 0 < expSum c a t := by
  have h := eventually_expSum_pos_atBot c (fun i => a i - a i₀) i₀ (by simp)
    (fun i hi => by simpa [sub_pos] using hmin i hi) hc
  filter_upwards [h] with t ht
  rw [expSum_shift_apply] at ht
  nlinarith [Real.exp_pos (-(a i₀ * t))]

theorem eventually_expSum_neg_atBot_of_min {m : ℕ} (c a : Fin m → ℝ) (i₀ : Fin m)
    (hmin : ∀ i, i ≠ i₀ → a i₀ < a i) (hc : c i₀ < 0) :
    ∀ᶠ t in atBot, expSum c a t < 0 := by
  have h := eventually_expSum_neg_atBot c (fun i => a i - a i₀) i₀ (by simp)
    (fun i hi => by simpa [sub_pos] using hmin i hi) hc
  filter_upwards [h] with t ht
  rw [expSum_shift_apply] at ht
  nlinarith [Real.exp_pos (-(a i₀ * t))]

/-! ## The rule -/

/-- **Laguerre's rule for exponential sums.**  If the exponents `a` are strictly increasing and every
coefficient is nonzero, then every zero configuration of `∑ c i e^{a i t}` — real zeros listed with
their multiplicities — has length at most the number of sign changes of `c`. -/
theorem laguerre_zeroList_length_le :
    ∀ (m : ℕ) (c a : Fin (m + 1) → ℝ), StrictMono a → (∀ i, c i ≠ 0) →
      ∀ l : List ℝ, IsZeroList (expSum c a) l → l.length ≤ signChanges c := by
  intro m
  induction m with
  | zero =>
    intro c a _ hc l hl
    have hN : ∀ x : ℝ, expSum (fun i => c i * a i ^ (0 : ℕ)) a x ≠ 0 := by
      intro x
      rw [expSum, Fin.sum_univ_one]
      simp only [pow_zero, mul_one]
      exact mul_ne_zero (hc 0) (Real.exp_ne_zero _)
    have := zeroList_length_le_expSum c a hN hl
    simpa using this
  | succ n ih =>
    intro c a ha hc l hl
    have hb0 : (fun i : Fin (n + 2) => a i - a 0) 0 = 0 := by simp
    have hbpos : ∀ i : Fin (n + 2), i ≠ 0 → 0 < a i - a 0 := by
      intro i hi
      have hlt : (0 : Fin (n + 2)) < i := lt_of_le_of_ne (Fin.zero_le i) (Ne.symm hi)
      simpa [sub_pos] using ha hlt
    have hbmono : StrictMono (fun i : Fin (n + 2) => a i - a 0) := by
      intro i j hij
      simpa [sub_lt_sub_iff_right] using ha hij
    have hlb : IsZeroList (expSum c (fun i : Fin (n + 2) => a i - a 0)) l :=
      isZeroList_expSum_shift c a (a 0) hl
    have hderiv : deriv (expSum c (fun i : Fin (n + 2) => a i - a 0)) =
        expSum (fun i : Fin (n + 1) => c i.succ * (a i.succ - a 0))
          (fun i : Fin (n + 1) => a i.succ - a 0) :=
      deriv_expSum_of_head_zero c (fun i : Fin (n + 2) => a i - a 0) hb0
    have hBpos : ∀ i : Fin (n + 1), 0 < a i.succ - a 0 := fun i => hbpos i.succ (Fin.succ_ne_zero i)
    have hBmono : StrictMono (fun i : Fin (n + 1) => a i.succ - a 0) := by
      intro i j hij
      exact hbmono (Fin.succ_lt_succ_iff.mpr hij)
    have hCne : ∀ i : Fin (n + 1), c i.succ * (a i.succ - a 0) ≠ 0 :=
      fun i => mul_ne_zero (hc i.succ) (ne_of_gt (hBpos i))
    have hCsign : signChanges (fun i : Fin (n + 1) => c i.succ * (a i.succ - a 0))
        = signChanges (fun i : Fin (n + 1) => c i.succ) :=
      signChanges_mul_pos _ _ (fun i => hc _) hBpos
    have key : ∀ l' : List ℝ,
        IsZeroList (deriv (expSum c (fun i : Fin (n + 2) => a i - a 0))) l' →
          l'.length ≤ signChanges (fun i : Fin (n + 1) => c i.succ) := by
      intro l' hl'
      rw [hderiv] at hl'
      have h := ih _ _ hBmono hCne l' hl'
      rwa [hCsign] at h
    rw [signChanges_succ]
    cases l with
    | nil => simp
    | cons x₁ t =>
      by_cases hsgn : c 0 * c 1 < 0
      · obtain ⟨u, hu, hulen, _, _⟩ :=
          exists_zeroList_deriv
            (continuous_iteratedDeriv_expSum c (fun i : Fin (n + 2) => a i - a 0)) t x₁ hlb
        have hkey := key u hu
        simp only [List.length_cons, if_pos hsgn]
        omega
      · have hprod : 0 < c 0 * c 1 := by
          rcases lt_trichotomy (c 0 * c 1) 0 with h | h | h
          · exact absurd h hsgn
          · exact absurd h (mul_ne_zero (hc 0) (hc 1))
          · exact h
        have hC0 : c (Fin.succ (0 : Fin (n + 1))) * (a (Fin.succ (0 : Fin (n + 1))) - a 0)
            = c 1 * (a 1 - a 0) := by rw [Fin.succ_zero_eq_one]
        have hminB : ∀ i : Fin (n + 1), i ≠ 0 →
            a (Fin.succ (0 : Fin (n + 1))) - a 0 < a i.succ - a 0 := by
          intro i hi
          exact hBmono (lt_of_le_of_ne (Fin.zero_le i) (Ne.symm hi))
        have hsign :
            ((∀ᶠ s in atBot, 0 < expSum c (fun i : Fin (n + 2) => a i - a 0) s) ∧
              (∀ᶠ s in atBot, 0 < deriv (expSum c (fun i : Fin (n + 2) => a i - a 0)) s)) ∨
            ((∀ᶠ s in atBot, expSum c (fun i : Fin (n + 2) => a i - a 0) s < 0) ∧
              (∀ᶠ s in atBot, deriv (expSum c (fun i : Fin (n + 2) => a i - a 0)) s < 0)) := by
          rcases lt_trichotomy (c 0) 0 with h0 | h0 | h0
          · right
            have h1 : c 1 < 0 := by nlinarith
            refine ⟨eventually_expSum_neg_atBot c _ 0 hb0 hbpos h0, ?_⟩
            rw [hderiv]
            refine eventually_expSum_neg_atBot_of_min _ _ 0 hminB ?_
            rw [hC0]
            exact mul_neg_of_neg_of_pos h1 (hBpos 0)
          · exact absurd h0 (hc 0)
          · left
            have h1 : 0 < c 1 := by nlinarith
            refine ⟨eventually_expSum_pos_atBot c _ 0 hb0 hbpos h0, ?_⟩
            rw [hderiv]
            refine eventually_expSum_pos_atBot_of_min _ _ 0 hminB ?_
            rw [hC0]
            exact mul_pos h1 (hBpos 0)
        obtain ⟨u, hu, hulen⟩ :=
          exists_deriv_zeroList_succ (contDiff_expSum c (fun i : Fin (n + 2) => a i - a 0))
            (continuous_iteratedDeriv_expSum c (fun i : Fin (n + 2) => a i - a 0)) hsign hlb
        have hkey := key u hu
        simp only [List.length_cons, if_neg hsgn]
        omega

end GaloisForLFunctions.HTGeometry
