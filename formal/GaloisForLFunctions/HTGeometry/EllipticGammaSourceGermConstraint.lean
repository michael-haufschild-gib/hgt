import GaloisForLFunctions.HTGeometry.EllipticGammaConeSource
import GaloisForLFunctions.HTGeometry.EllipticGammaJetSourceDivisor
import GaloisForLFunctions.HTGeometry.TripticGermConstraint

/-!
# The elliptic gamma source and its jets satisfy the triptic constraints

The mixed difference of the elliptic gamma source is the constant `-2πi` wherever the twelve cone
and single products entering the cocycle are nonzero.  Each of those products is entire with a
countable zero set, so each is nonzero on a punctured neighbourhood of every point: the constraint
holds as an identity of germs, which is what membership in the triptic class means.

Periodicity is exact, not just germ-level: the cone product is exactly `1`-periodic, hence so is
every translate of the gamma function, its logarithmic derivative, and every jet of that.  Each jet
above the zeroth has vanishing mixed constant, since differentiating a constant kills it.

* `eventually_nhdsNE_ne_zero_of_countable_zeroSet`;
* `mixedConstGerm_ellipticGammaSource`;
* `periodicOneGerm_gammaJetSource`, `mixedConstGerm_gammaJetSource_zero`,
  `mixedConstGerm_gammaJetSource_succ`.
-/

open Filter Set Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-! ### Punctured nonvanishing -/

/-- **An entire function with countable zero set is nonzero on a punctured neighbourhood of every
point.** -/
theorem eventually_nhdsNE_ne_zero_of_countable_zeroSet {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hc : {z : ℂ | f z = 0}.Countable) (z : ℂ) : ∀ᶠ w in 𝓝[≠] z, f w ≠ 0 := by
  rcases (hf.analyticAt z).eventually_eq_zero_or_eventually_ne_zero with hzero | hne
  · exact absurd (analyticOrderAt_eq_top.mpr hzero)
      (analyticOrderAt_ne_top_of_countable_zeroSet hf hc z)
  · exact hne

theorem countable_singleProduct_zeroSet {b : ℂ} (hb : 0 < b.im) :
    {z : ℂ | singleProduct b z = 0}.Countable := by
  have hsub : {z : ℂ | singleProduct b z = 0}
      ⊆ Set.range (fun t : ℕ × ℤ ↦ ((t.2 : ℂ)) - (t.1 : ℂ) * b) := by
    intro z hz
    obtain ⟨k, hk⟩ := (singleProduct_eq_zero_iff hb z).mp hz
    simp only [singleFactor] at hk
    have hone : expChar ((k : ℂ) * b + z) = 1 := by linear_combination -hk
    obtain ⟨m, hm⟩ := (expChar_eq_one_iff _).mp hone
    exact ⟨(k, m), by simp only; linear_combination -hm⟩
  exact Set.Countable.mono hsub (Set.countable_range _)

theorem differentiable_one_sub_expChar : Differentiable ℂ (fun z : ℂ ↦ 1 - expChar z) := by
  simp only [expChar]
  fun_prop

theorem countable_one_sub_expChar_zeroSet : {z : ℂ | (1 : ℂ) - expChar z = 0}.Countable := by
  have hsub : {z : ℂ | (1 : ℂ) - expChar z = 0} ⊆ Set.range (fun m : ℤ ↦ (m : ℂ)) := by
    intro z hz
    simp only [Set.mem_setOf_eq] at hz
    obtain ⟨m, hm⟩ := (expChar_eq_one_iff z).mp (by linear_combination -hz)
    exact ⟨m, hm.symm⟩
  exact Set.Countable.mono hsub (Set.countable_range _)

/-- Reflection carries punctured neighbourhoods to punctured neighbourhoods. -/
theorem tendsto_nhdsNE_const_sub (z c : ℂ) :
    Tendsto (fun w : ℂ ↦ c - w) (𝓝[≠] z) (𝓝[≠] (c - z)) := by
  rw [tendsto_nhdsWithin_iff]
  constructor
  · have hc : Tendsto (fun w : ℂ ↦ c - w) (𝓝 z) (𝓝 (c - z)) :=
      (continuous_const.sub continuous_id).continuousAt
    exact hc.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with w hw
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hw ⊢
    intro hcon
    exact hw (by linear_combination -hcon)

/-! ### The mixed constraint of the source -/

section

variable {a b : ℂ} (ha : 0 < a.im) (hb : 0 < b.im)

include ha hb in
theorem eventually_nhdsNE_coneProduct_add_ne_zero (c z : ℂ) :
    ∀ᶠ w in 𝓝[≠] z, coneProduct a b (w + c) ≠ 0 :=
  (tendsto_nhdsNE_add_const z c).eventually
    (eventually_nhdsNE_ne_zero_of_countable_zeroSet (differentiable_coneProduct ha hb)
      (countable_coneProduct_zeroSet ha hb) (z + c))

include ha hb in
theorem eventually_nhdsNE_coneProduct_sub_ne_zero (c z : ℂ) :
    ∀ᶠ w in 𝓝[≠] z, coneProduct a b (c - w) ≠ 0 :=
  (tendsto_nhdsNE_const_sub z c).eventually
    (eventually_nhdsNE_ne_zero_of_countable_zeroSet (differentiable_coneProduct ha hb)
      (countable_coneProduct_zeroSet ha hb) (c - z))

include hb in
theorem eventually_nhdsNE_singleProduct_add_ne_zero (c z : ℂ) :
    ∀ᶠ w in 𝓝[≠] z, singleProduct b (w + c) ≠ 0 :=
  (tendsto_nhdsNE_add_const z c).eventually
    (eventually_nhdsNE_ne_zero_of_countable_zeroSet (differentiable_singleProduct hb)
      (countable_singleProduct_zeroSet hb) (z + c))

include hb in
theorem eventually_nhdsNE_singleProduct_sub_ne_zero (c z : ℂ) :
    ∀ᶠ w in 𝓝[≠] z, singleProduct b (c - w) ≠ 0 :=
  (tendsto_nhdsNE_const_sub z c).eventually
    (eventually_nhdsNE_ne_zero_of_countable_zeroSet (differentiable_singleProduct hb)
      (countable_singleProduct_zeroSet hb) (c - z))

theorem eventually_nhdsNE_one_sub_expChar_add_ne_zero (c z : ℂ) :
    ∀ᶠ w in 𝓝[≠] z, (1 : ℂ) - expChar (w + c) ≠ 0 :=
  (tendsto_nhdsNE_add_const z c).eventually
    (eventually_nhdsNE_ne_zero_of_countable_zeroSet differentiable_one_sub_expChar
      countable_one_sub_expChar_zeroSet (z + c))

theorem eventually_nhdsNE_one_sub_expChar_sub_ne_zero (c z : ℂ) :
    ∀ᶠ w in 𝓝[≠] z, (1 : ℂ) - expChar (c - w) ≠ 0 :=
  (tendsto_nhdsNE_const_sub z c).eventually
    (eventually_nhdsNE_ne_zero_of_countable_zeroSet differentiable_one_sub_expChar
      countable_one_sub_expChar_zeroSet (c - z))

include ha hb in
/-- **The elliptic gamma source has constant mixed difference as a germ.** -/
theorem mixedConstGerm_ellipticGammaSource :
    MixedConstGerm (ellipticGammaSource a b) a b (-(2 * (Real.pi : ℂ) * Complex.I)) := by
  intro z
  filter_upwards [eventually_nhdsNE_one_sub_expChar_add_ne_zero 0 z,
    eventually_nhdsNE_one_sub_expChar_sub_ne_zero 0 z,
    eventually_nhdsNE_coneProduct_sub_ne_zero ha hb 0 z,
    eventually_nhdsNE_coneProduct_add_ne_zero ha hb (a + b) z,
    eventually_nhdsNE_coneProduct_sub_ne_zero ha hb (a + b) z,
    eventually_nhdsNE_coneProduct_add_ne_zero ha hb 0 z,
    eventually_nhdsNE_coneProduct_sub_ne_zero ha hb b z,
    eventually_nhdsNE_coneProduct_add_ne_zero ha hb a z,
    eventually_nhdsNE_coneProduct_sub_ne_zero ha hb a z,
    eventually_nhdsNE_coneProduct_add_ne_zero ha hb b z,
    eventually_nhdsNE_singleProduct_add_ne_zero hb 0 z,
    eventually_nhdsNE_singleProduct_add_ne_zero hb b z,
    eventually_nhdsNE_singleProduct_sub_ne_zero hb 0 z,
    eventually_nhdsNE_singleProduct_sub_ne_zero hb b z]
    with w he he' hC1 hC2 hC3 hC4 hC5 hC6 hC7 hC8 hP1 hP2 hP3 hP4
  have hmix := ellipticGammaSource_mixed_difference ha hb (z := w)
    (by simpa using he) (by simpa using he') (by simpa using hC1) (by
      rw [show w + a + b = w + (a + b) by ring]
      exact hC2) (by simpa using hC3) (by simpa using hC4) (by simpa using hC5)
    (by simpa using hC6) (by simpa using hC7) (by simpa using hC8) (by simpa using hP1)
    (by simpa using hP2) (by simpa using hP3) (by simpa using hP4)
  linear_combination hmix

end

/-! ### Transport along a translation -/

theorem mixedConstGerm_comp_add {F : ℂ → ℂ} {τ σ Cst : ℂ} (h : MixedConstGerm F τ σ Cst) (c : ℂ) :
    MixedConstGerm (fun z ↦ F (z + c)) τ σ Cst := by
  intro z
  filter_upwards [(tendsto_nhdsNE_add_const z c).eventually (h (z + c))] with w hw
  rw [show w + τ + σ + c = w + c + τ + σ by ring, show w + τ + c = w + c + τ by ring,
    show w + σ + c = w + c + σ by ring]
  exact hw

/-- The logarithmic derivative of a translate of the elliptic gamma function is the translated
source. -/
theorem logDeriv_ellipticGammaConeTranslate (a b g : ℂ) :
    logDeriv (ellipticGammaConeTranslate a b g) = fun z ↦ ellipticGammaSource a b (z + -g) := by
  funext z
  rw [ellipticGammaConeTranslate_eq_comp, logDeriv_comp_add_const, ellipticGammaSource]

/-! ### Exact periodicity of the jets -/

theorem deriv_periodic {g : ℂ → ℂ} {p : ℂ} (h : ∀ z : ℂ, g (z + p) = g z) (z : ℂ) :
    deriv g (z + p) = deriv g z := by
  have hfun : (fun w ↦ g (w + p)) = g := funext h
  have hd := deriv_comp_add_const g p z
  rw [hfun] at hd
  exact hd.symm

theorem iteratedDeriv_periodic {g : ℂ → ℂ} {p : ℂ} (h : ∀ z : ℂ, g (z + p) = g z) (j : ℕ) :
    ∀ z : ℂ, iteratedDeriv j g (z + p) = iteratedDeriv j g z := by
  induction j with
  | zero =>
      simpa [iteratedDeriv_zero] using h
  | succ n ih =>
      intro z
      have hfun : iteratedDeriv (n + 1) g = deriv (iteratedDeriv n g) := iteratedDeriv_succ
      rw [hfun]
      exact deriv_periodic ih z

theorem ellipticGammaConeTranslate_periodic (a b g z : ℂ) :
    ellipticGammaConeTranslate a b g (z + 1) = ellipticGammaConeTranslate a b g z := by
  rw [ellipticGammaConeTranslate_eq_comp]
  simp only
  rw [show z + 1 + -g = z + -g + 1 by ring, ellipticGammaCone_periodic]

/-- **Every jet of a translated gamma source is exactly `1`-periodic.** -/
theorem periodicOneGerm_gammaJetSource (a b g : ℂ) (j : ℕ) :
    PeriodicOneGerm (gammaJetSource a b g j) :=
  periodicOneGerm_of_forall
    (iteratedDeriv_periodic
      (fun z ↦ logDeriv_of_periodic (ellipticGammaConeTranslate_periodic a b g) z) j)

/-! ### The mixed constant of a jet -/

section

variable {a b : ℂ} (ha : 0 < a.im) (hb : 0 < b.im)

include ha hb in
theorem meromorphicOn_logDeriv_ellipticGammaConeTranslate (g : ℂ) :
    MeromorphicOn (logDeriv (ellipticGammaConeTranslate a b g)) (Set.univ : Set ℂ) := fun z _ ↦
  ((meromorphicOn_ellipticGammaConeTranslate ha hb g z (Set.mem_univ z)).deriv).div
    (meromorphicOn_ellipticGammaConeTranslate ha hb g z (Set.mem_univ z))

include ha hb in
/-- **A translated gamma source has constant mixed difference as a germ.** -/
theorem mixedConstGerm_gammaJetSource_zero (g : ℂ) :
    MixedConstGerm (gammaJetSource a b g 0) a b (-(2 * (Real.pi : ℂ) * Complex.I)) := by
  have hjet : gammaJetSource a b g 0 = fun z ↦ ellipticGammaSource a b (z + -g) := by
    rw [gammaJetSource]
    have h0 : iteratedDeriv 0 (logDeriv (ellipticGammaConeTranslate a b g))
        = logDeriv (ellipticGammaConeTranslate a b g) := iteratedDeriv_zero
    rw [h0, logDeriv_ellipticGammaConeTranslate]
  rw [hjet]
  exact mixedConstGerm_comp_add (mixedConstGerm_ellipticGammaSource ha hb) (-g)

include ha hb in
/-- **Every higher jet of a translated gamma source has vanishing mixed constant.** -/
theorem mixedConstGerm_gammaJetSource_succ (g : ℂ) (j : ℕ) :
    MixedConstGerm (gammaJetSource a b g (j + 1)) a b 0 := by
  have hjet : gammaJetSource a b g (j + 1)
      = iteratedDeriv (j + 1) (logDeriv (ellipticGammaConeTranslate a b g)) := rfl
  rw [hjet]
  refine mixedConstGerm_iteratedDeriv_succ (Cst := -(2 * (Real.pi : ℂ) * Complex.I))
    (meromorphicOn_logDeriv_ellipticGammaConeTranslate ha hb g) ?_ j
  have h0 : logDeriv (ellipticGammaConeTranslate a b g) = gammaJetSource a b g 0 :=
    (iteratedDeriv_zero (f := logDeriv (ellipticGammaConeTranslate a b g))).symm
  rw [h0]
  exact mixedConstGerm_gammaJetSource_zero ha hb g

end

end

end GaloisForLFunctions.HTGeometry
