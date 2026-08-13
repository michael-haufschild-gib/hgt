import GaloisForLFunctions.HTGeometry.TripticGermConstraint
import GaloisForLFunctions.HTGeometry.TripticGammaDivisorRealization
import GaloisForLFunctions.HTGeometry.EllipticGammaSourceGermConstraint

/-!
# The multiplicative triptic source class and its closure laws

A member of the multiplicative triptic class is a meromorphic function on the plane with finite
order everywhere, exactly `1`-periodic, whose mixed multiplicative coboundary
`Y(z+τ+σ)Y(z)/(Y(z+τ)Y(z+σ))` has constant logarithmic derivative — recorded as the germ identity
`MixedConstGerm (logDeriv Y) τ σ Cst`, since a logarithmic derivative is only a meromorphic germ.

The class is closed under products, quotients, and integer powers, with the mixed constants adding,
subtracting and scaling accordingly; the constant function `1` is a member with constant `0`; and
every translate of the elliptic gamma function is a member with constant `-2πi`.

* `TripticMultiplicativeSource`;
* `TripticMultiplicativeSource.mul`, `.div`, `.pow`, `.zpow`, `tripticMultiplicativeSource_one`;
* `tripticMultiplicativeSource_ellipticGammaConeTranslate`.
-/

open Filter Set Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- **A member of the multiplicative triptic source class**: meromorphic on the plane with finite
order everywhere, `1`-periodic, and with mixed logarithmic-derivative coboundary equal to the
constant `Cst` as an identity of meromorphic germs. -/
structure TripticMultiplicativeSource (τ σ : ℂ) (Y : ℂ → ℂ) (Cst : ℂ) : Prop where
  mero : MeromorphicOn Y (Set.univ : Set ℂ)
  finOrd : ∀ w : ℂ, meromorphicOrderAt Y w ≠ ⊤
  periodic : ∀ z : ℂ, Y (z + 1) = Y z
  mixed : MixedConstGerm (logDeriv Y) τ σ Cst

/-! ### Punctured regularity of translates -/

/-- A meromorphic function of finite order everywhere is analytic and nonvanishing at every
translate, on a punctured neighbourhood of every point. -/
theorem eventually_nhdsNE_regular_comp_add {Y : ℂ → ℂ}
    (hY : MeromorphicOn Y (Set.univ : Set ℂ)) (hfin : ∀ w : ℂ, meromorphicOrderAt Y w ≠ ⊤)
    (c z : ℂ) :
    ∀ᶠ w in 𝓝[≠] z, AnalyticAt ℂ Y (w + c) ∧ Y (w + c) ≠ 0 := by
  have hbase : ∀ y : ℂ, ∀ᶠ w in 𝓝[≠] y, AnalyticAt ℂ Y w ∧ Y w ≠ 0 := by
    intro y
    have h₁ : ∀ᶠ w in 𝓝[≠] y, AnalyticAt ℂ Y w := by
      have hdisj := mem_codiscreteWithin.mp hY.analyticAt_mem_codiscreteWithin y (Set.mem_univ y)
      filter_upwards [Filter.disjoint_principal_right.mp hdisj] with w hw
      simpa using hw
    have h₂ : ∀ᶠ w in 𝓝[≠] y, Y w ≠ 0 :=
      (meromorphicOrderAt_ne_top_iff_eventually_ne_zero (hY y (Set.mem_univ y))).mp (hfin y)
    exact h₁.and h₂
  exact (tendsto_nhdsNE_add_const z c).eventually (hbase (z + c))

/-- The logarithmic derivative of a pointwise product splits at every translate, on a punctured
neighbourhood of every point. -/
theorem eventually_nhdsNE_logDeriv_mul_comp_add {Y₁ Y₂ : ℂ → ℂ}
    (h₁ : MeromorphicOn Y₁ (Set.univ : Set ℂ)) (h₂ : MeromorphicOn Y₂ (Set.univ : Set ℂ))
    (hf₁ : ∀ w : ℂ, meromorphicOrderAt Y₁ w ≠ ⊤) (hf₂ : ∀ w : ℂ, meromorphicOrderAt Y₂ w ≠ ⊤)
    (c z : ℂ) :
    ∀ᶠ w in 𝓝[≠] z, logDeriv (fun u ↦ Y₁ u * Y₂ u) (w + c)
      = logDeriv Y₁ (w + c) + logDeriv Y₂ (w + c) := by
  filter_upwards [eventually_nhdsNE_regular_comp_add h₁ hf₁ c z,
    eventually_nhdsNE_regular_comp_add h₂ hf₂ c z] with w hw₁ hw₂
  exact logDeriv_mul (w + c) hw₁.2 hw₂.2 hw₁.1.differentiableAt hw₂.1.differentiableAt

/-- The logarithmic derivative of a pointwise quotient splits at every translate, on a punctured
neighbourhood of every point. -/
theorem eventually_nhdsNE_logDeriv_div_comp_add {Y₁ Y₂ : ℂ → ℂ}
    (h₁ : MeromorphicOn Y₁ (Set.univ : Set ℂ)) (h₂ : MeromorphicOn Y₂ (Set.univ : Set ℂ))
    (hf₁ : ∀ w : ℂ, meromorphicOrderAt Y₁ w ≠ ⊤) (hf₂ : ∀ w : ℂ, meromorphicOrderAt Y₂ w ≠ ⊤)
    (c z : ℂ) :
    ∀ᶠ w in 𝓝[≠] z, logDeriv (fun u ↦ Y₁ u / Y₂ u) (w + c)
      = logDeriv Y₁ (w + c) - logDeriv Y₂ (w + c) := by
  filter_upwards [eventually_nhdsNE_regular_comp_add h₁ hf₁ c z,
    eventually_nhdsNE_regular_comp_add h₂ hf₂ c z] with w hw₁ hw₂
  exact logDeriv_div (w + c) hw₁.2 hw₂.2 hw₁.1.differentiableAt hw₂.1.differentiableAt

/-! ### Order finiteness of products, quotients and powers -/

theorem meromorphicOrderAt_mul_ne_top {Y₁ Y₂ : ℂ → ℂ}
    (h₁ : MeromorphicOn Y₁ (Set.univ : Set ℂ)) (h₂ : MeromorphicOn Y₂ (Set.univ : Set ℂ))
    (hf₁ : ∀ w : ℂ, meromorphicOrderAt Y₁ w ≠ ⊤) (hf₂ : ∀ w : ℂ, meromorphicOrderAt Y₂ w ≠ ⊤)
    (w : ℂ) :
    meromorphicOrderAt (fun z ↦ Y₁ z * Y₂ z) w ≠ ⊤ := by
  have hmul : meromorphicOrderAt (fun z ↦ Y₁ z * Y₂ z) w
      = meromorphicOrderAt Y₁ w + meromorphicOrderAt Y₂ w :=
    meromorphicOrderAt_mul (h₁ w (Set.mem_univ w)) (h₂ w (Set.mem_univ w))
  rw [hmul]
  exact WithTop.add_ne_top.mpr ⟨hf₁ w, hf₂ w⟩

theorem meromorphicOrderAt_div_ne_top {Y₁ Y₂ : ℂ → ℂ}
    (h₁ : MeromorphicOn Y₁ (Set.univ : Set ℂ)) (h₂ : MeromorphicOn Y₂ (Set.univ : Set ℂ))
    (hf₁ : ∀ w : ℂ, meromorphicOrderAt Y₁ w ≠ ⊤) (hf₂ : ∀ w : ℂ, meromorphicOrderAt Y₂ w ≠ ⊤)
    (w : ℂ) :
    meromorphicOrderAt (fun z ↦ Y₁ z / Y₂ z) w ≠ ⊤ := by
  have hdiv : meromorphicOrderAt (fun z ↦ Y₁ z / Y₂ z) w
      = meromorphicOrderAt Y₁ w - meromorphicOrderAt Y₂ w :=
    meromorphicOrderAt_div (h₁ w (Set.mem_univ w)) (h₂ w (Set.mem_univ w))
  rw [hdiv]
  exact withTop_sub_ne_top (hf₁ w) (hf₂ w)

/-! ### Closure laws of the class -/

/-- **The class is closed under pointwise products**, with the mixed constants adding. -/
theorem TripticMultiplicativeSource.mul {τ σ : ℂ} {Y₁ Y₂ : ℂ → ℂ} {C₁ C₂ : ℂ}
    (h₁ : TripticMultiplicativeSource τ σ Y₁ C₁) (h₂ : TripticMultiplicativeSource τ σ Y₂ C₂) :
    TripticMultiplicativeSource τ σ (fun z ↦ Y₁ z * Y₂ z) (C₁ + C₂) := by
  refine ⟨fun z _ ↦ (h₁.mero z (Set.mem_univ z)).mul (h₂.mero z (Set.mem_univ z)),
    meromorphicOrderAt_mul_ne_top h₁.mero h₂.mero h₁.finOrd h₂.finOrd,
    fun z ↦ by rw [h₁.periodic z, h₂.periodic z], ?_⟩
  intro z
  filter_upwards [h₁.mixed z, h₂.mixed z,
    eventually_nhdsNE_logDeriv_mul_comp_add h₁.mero h₂.mero h₁.finOrd h₂.finOrd 0 z,
    eventually_nhdsNE_logDeriv_mul_comp_add h₁.mero h₂.mero h₁.finOrd h₂.finOrd τ z,
    eventually_nhdsNE_logDeriv_mul_comp_add h₁.mero h₂.mero h₁.finOrd h₂.finOrd σ z,
    eventually_nhdsNE_logDeriv_mul_comp_add h₁.mero h₂.mero h₁.finOrd h₂.finOrd (τ + σ) z]
    with w hm₁ hm₂ e0 eτ eσ eτσ
  have e0' := e0
  have eτ' := eτ
  have eσ' := eσ
  have eτσ' := eτσ
  rw [add_zero] at e0'
  have hτσ : w + (τ + σ) = w + τ + σ := by ring
  rw [hτσ] at eτσ'
  rw [eτσ', eτ', eσ', e0']
  linear_combination hm₁ + hm₂

/-- **The class is closed under pointwise quotients**, with the mixed constants subtracting. -/
theorem TripticMultiplicativeSource.div {τ σ : ℂ} {Y₁ Y₂ : ℂ → ℂ} {C₁ C₂ : ℂ}
    (h₁ : TripticMultiplicativeSource τ σ Y₁ C₁) (h₂ : TripticMultiplicativeSource τ σ Y₂ C₂) :
    TripticMultiplicativeSource τ σ (fun z ↦ Y₁ z / Y₂ z) (C₁ - C₂) := by
  refine ⟨fun z _ ↦ (h₁.mero z (Set.mem_univ z)).div (h₂.mero z (Set.mem_univ z)),
    meromorphicOrderAt_div_ne_top h₁.mero h₂.mero h₁.finOrd h₂.finOrd,
    fun z ↦ by rw [h₁.periodic z, h₂.periodic z], ?_⟩
  intro z
  filter_upwards [h₁.mixed z, h₂.mixed z,
    eventually_nhdsNE_logDeriv_div_comp_add h₁.mero h₂.mero h₁.finOrd h₂.finOrd 0 z,
    eventually_nhdsNE_logDeriv_div_comp_add h₁.mero h₂.mero h₁.finOrd h₂.finOrd τ z,
    eventually_nhdsNE_logDeriv_div_comp_add h₁.mero h₂.mero h₁.finOrd h₂.finOrd σ z,
    eventually_nhdsNE_logDeriv_div_comp_add h₁.mero h₂.mero h₁.finOrd h₂.finOrd (τ + σ) z]
    with w hm₁ hm₂ e0 eτ eσ eτσ
  have e0' := e0
  rw [add_zero] at e0'
  have hτσ : w + (τ + σ) = w + τ + σ := by ring
  rw [hτσ] at eτσ
  rw [eτσ, eτ, eσ, e0']
  linear_combination hm₁ - hm₂

/-- **The constant function `1` is a member of the class**, with mixed constant `0`. -/
theorem tripticMultiplicativeSource_one (τ σ : ℂ) :
    TripticMultiplicativeSource τ σ (fun _ ↦ (1 : ℂ)) 0 := by
  classical
  refine ⟨fun z _ ↦ (analyticAt_const (v := (1 : ℂ))).meromorphicAt,
    fun w ↦ by rw [meromorphicOrderAt_const]; simp, fun z ↦ rfl, ?_⟩
  intro z
  refine Filter.Eventually.of_forall fun w ↦ ?_
  have hld : logDeriv (fun _ : ℂ ↦ (1 : ℂ)) = fun _ ↦ (0 : ℂ) := by
    funext u
    simp [logDeriv_apply]
  simp [hld]

/-- **The class is closed under natural powers**, with the mixed constant scaling. -/
theorem TripticMultiplicativeSource.pow {τ σ : ℂ} {Y : ℂ → ℂ} {Cst : ℂ}
    (hY : TripticMultiplicativeSource τ σ Y Cst) (n : ℕ) :
    TripticMultiplicativeSource τ σ (fun z ↦ Y z ^ n) ((n : ℂ) * Cst) := by
  induction n with
  | zero =>
      have hfun : (fun z : ℂ ↦ Y z ^ 0) = fun _ : ℂ ↦ (1 : ℂ) := by
        funext z
        simp
      rw [hfun]
      simpa using tripticMultiplicativeSource_one τ σ
  | succ k ih =>
      have hfun : (fun z : ℂ ↦ Y z ^ (k + 1)) = fun z : ℂ ↦ Y z ^ k * Y z := by
        funext z
        ring
      have hconst : ((k : ℂ) + 1) * Cst = (k : ℂ) * Cst + Cst := by ring
      rw [hfun]
      push_cast
      rw [hconst]
      exact ih.mul hY

/-- **The class is closed under integer powers**, with the mixed constant scaling. -/
theorem TripticMultiplicativeSource.zpow {τ σ : ℂ} {Y : ℂ → ℂ} {Cst : ℂ}
    (hY : TripticMultiplicativeSource τ σ Y Cst) (n : ℤ) :
    TripticMultiplicativeSource τ σ (fun z ↦ Y z ^ n) ((n : ℂ) * Cst) := by
  cases n with
  | ofNat k =>
      have hfun : (fun z : ℂ ↦ Y z ^ (Int.ofNat k : ℤ)) = fun z : ℂ ↦ Y z ^ k := by
        funext z
        simp
      rw [hfun]
      simpa using hY.pow k
  | negSucc k =>
      have hfun : (fun z : ℂ ↦ Y z ^ (Int.negSucc k)) = fun z : ℂ ↦ 1 / Y z ^ (k + 1) := by
        funext z
        rw [zpow_negSucc, one_div]
      have hconst : ((Int.negSucc k : ℤ) : ℂ) * Cst = 0 - (((k + 1 : ℕ) : ℂ) * Cst) := by
        rw [Int.cast_negSucc]
        push_cast
        ring
      rw [hfun, hconst]
      exact (tripticMultiplicativeSource_one τ σ).div (hY.pow (k + 1))

/-! ### The gamma translates are members -/

/-- **Every translate of the elliptic gamma function is a member of the class**, with mixed
constant `-2πi`. -/
theorem tripticMultiplicativeSource_ellipticGammaConeTranslate {τ σ : ℂ}
    (hτ : 0 < τ.im) (hσ : 0 < σ.im) (g : ℂ) :
    TripticMultiplicativeSource τ σ (ellipticGammaConeTranslate τ σ g)
      (-(2 * (Real.pi : ℂ) * Complex.I)) := by
  refine ⟨meromorphicOn_ellipticGammaConeTranslate hτ hσ g,
    meromorphicOrderAt_ellipticGammaConeTranslate_ne_top hτ hσ g,
    ellipticGammaConeTranslate_periodic τ σ g, ?_⟩
  have hjet : gammaJetSource τ σ g 0 = logDeriv (ellipticGammaConeTranslate τ σ g) := by
    rw [gammaJetSource, iteratedDeriv_zero]
  have h := mixedConstGerm_gammaJetSource_zero hτ hσ g
  rwa [hjet] at h

end

end GaloisForLFunctions.HTGeometry
