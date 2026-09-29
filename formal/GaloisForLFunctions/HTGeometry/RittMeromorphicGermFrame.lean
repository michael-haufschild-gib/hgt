import GaloisForLFunctions.HTGeometry.MeromorphicGermField
import GaloisForLFunctions.HTGeometry.RittRationalLinearizerCocycle
import GaloisForLFunctions.HTGeometry.DigammaHypertranscendental
import GaloisForLFunctions.HTGeometry.GammaHypertranscendental
import GaloisForLFunctions.HTGeometry.DigammaGammaLocalHypertranscendence

/-!
# The Ritt frame of a rational map at a fixed point

Let `R` be a rational map regular at `0` with `R(0) = 0` and multiplier `λ = R'(0)` nonzero and not
a
root of unity.  On the field of meromorphic germs at `0`, precomposition with `R`, the derivation
`d/dz` and the embedding of `ℂ(z)` form a rational Ritt frame:

* **compatibility** — precomposition restricts to substitution `Q ↦ Q ∘ R` on `ℂ(z)`;
* **chain rule** — `(f ∘ R)' = R'·(f' ∘ R)`;
* **fixed field** — a germ with `f ∘ R = f` is constant: at a finite order `n` the leading
  coefficient gives `λ^n = 1`, so `n = 0`, and then `f − f(0)` is invariant with positive order.

A local analytic linearizer `κ(R(z)) = q·κ(z)` that satisfies an algebraic differential equation on
a
neighbourhood of `0` is a differentially algebraic element of the frame, so Ritt's implication for
rational maps gives a rational cocycle `A(R)·R'^N = β·A`.
-/

open Filter Topology Polynomial
open scoped Differential

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {R : RatFunc ℂ}

/-! ### The map as a function -/

theorem analyticAt_ratValue_zero (h0 : 0 ≤ ratOrder R 0) :
    AnalyticAt ℂ (fun z => ratValue R z) 0 := by
  have hden := denom_eval_ne_zero_of_regular h0
  have ha : AnalyticAt ℂ ((fun z => R.num.eval z) / fun z => R.denom.eval z) 0 :=
    (Differentiable.analyticAt (fun _ => R.num.differentiableAt) 0).div
      (Differentiable.analyticAt (fun _ => R.denom.differentiableAt) 0) hden
  exact ha

theorem deriv_ratValue_zero (h0 : 0 ≤ ratOrder R 0) :
    deriv (fun z => ratValue R z) 0 = ratValue (ratFuncDeriv R) 0 :=
  (hasDerivAt_ratValue (denom_eval_ne_zero_of_regular h0)).deriv

/-! ### Invariant germs are constant -/

variable {g : ℂ → ℂ}

/-- **The order of an invariant germ is a root-of-unity exponent of the multiplier.** -/
theorem pow_order_eq_one_of_invariant (hg : AnalyticAt ℂ g 0) (hg0 : g 0 = 0)
    (hgd : deriv g 0 ≠ 0) {f : ℂ → ℂ} (hf : MeromorphicAt f 0)
    (hinv : f ∘ g =ᶠ[𝓝[≠] (0 : ℂ)] f) {n : ℤ} (hn : meromorphicOrderAt f 0 = n) :
    deriv g 0 ^ n = 1 := by
  obtain ⟨h, hh, hh0, hfh⟩ := (meromorphicOrderAt_eq_int_iff hf).mp hn
  have htend := tendsto_nhdsNE_of_deriv_ne_zero hg hg0 hgd
  have hkey : ∀ᶠ z in 𝓝[≠] (0 : ℂ), h z = (g z / z) ^ n * h (g z) := by
    filter_upwards [hfh, htend.eventually hfh, hinv, self_mem_nhdsWithin,
      htend.eventually self_mem_nhdsWithin] with z hz hgz hinvz hz0 hgz0
    simp only [sub_zero, smul_eq_mul, Function.comp_apply] at hz hgz hinvz
    have hz0' : z ≠ 0 := hz0
    have hgz0' : g z ≠ 0 := hgz0
    rw [hinvz, hz] at hgz
    rw [div_zpow, div_mul_eq_mul_div, eq_div_iff (zpow_ne_zero n hz0'), ← hgz]
    ring
  -- limits along the punctured neighbourhood
  have hslope : Tendsto (fun z => g z / z) (𝓝[≠] (0 : ℂ)) (𝓝 (deriv g 0)) := by
    have := hasDerivAt_iff_tendsto_slope.mp hg.differentiableAt.hasDerivAt
    refine this.congr' (Eventually.of_forall fun z => ?_)
    simp [slope_def_field, hg0]
  have hlim1 : Tendsto h (𝓝[≠] (0 : ℂ)) (𝓝 (h 0)) :=
    hh.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hgcont : Tendsto g (𝓝[≠] (0 : ℂ)) (𝓝 0) := by
    have := hg.continuousAt.tendsto
    rw [hg0] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hlim2 : Tendsto (fun z => (g z / z) ^ n * h (g z)) (𝓝[≠] (0 : ℂ))
      (𝓝 (deriv g 0 ^ n * h 0)) :=
    (hslope.zpow₀ n (Or.inl hgd)).mul (hh.continuousAt.tendsto.comp hgcont)
  have heq := tendsto_nhds_unique hlim1 (hlim2.congr' (hkey.mono fun z hz => hz.symm))
  have : (deriv g 0 ^ n - 1) * h 0 = 0 := by rw [sub_mul, ← heq]; ring
  rcases mul_eq_zero.mp this with h1 | h1
  · exact sub_eq_zero.mp h1
  · exact absurd h1 hh0

theorem int_eq_zero_of_zpow_eq_one {lam : ℂ} (hlam : ∀ n : ℕ, 0 < n → lam ^ n ≠ 1) {n : ℤ}
    (h : lam ^ n = 1) : n = 0 := by
  by_contra hn
  rcases lt_or_gt_of_ne hn with hlt | hgt
  · obtain ⟨m, hm⟩ : ∃ m : ℕ, n = -(m : ℤ) := ⟨(-n).toNat, by omega⟩
    rw [hm, zpow_neg, zpow_natCast, inv_eq_one] at h
    exact hlam m (by omega) h
  · obtain ⟨m, hm⟩ : ∃ m : ℕ, n = (m : ℤ) := ⟨n.toNat, by omega⟩
    rw [hm, zpow_natCast] at h
    exact hlam m (by omega) h

/-- **Invariant germs are constant.** -/
theorem exists_const_of_invariant (hg : AnalyticAt ℂ g 0) (hg0 : g 0 = 0)
    (hgd : deriv g 0 ≠ 0) (hlam : ∀ n : ℕ, 0 < n → deriv g 0 ^ n ≠ 1) {f : ℂ → ℂ}
    (hf : MeromorphicAt f 0) (hinv : f ∘ g =ᶠ[𝓝[≠] (0 : ℂ)] f) :
    ∃ c : ℂ, f =ᶠ[𝓝[≠] (0 : ℂ)] fun _ => c := by
  rcases h : meromorphicOrderAt f 0 with _ | n
  · exact ⟨0, meromorphicOrderAt_eq_top_iff.mp h⟩
  have hn0 := int_eq_zero_of_zpow_eq_one hlam (pow_order_eq_one_of_invariant hg hg0 hgd hf hinv h)
  subst hn0
  obtain ⟨k, hk, hk0, hfk⟩ := (meromorphicOrderAt_eq_int_iff hf).mp h
  refine ⟨k 0, ?_⟩
  set f₁ : ℂ → ℂ := fun z => f z - k 0 with hf₁
  have hf₁m : MeromorphicAt f₁ 0 := hf.sub (MeromorphicAt.const (k 0) 0)
  have hinv₁ : f₁ ∘ g =ᶠ[𝓝[≠] (0 : ℂ)] f₁ :=
    hinv.mono fun z hz => by simp only [Function.comp_apply, hf₁] at hz ⊢; rw [hz]
  have hfk' : f =ᶠ[𝓝[≠] (0 : ℂ)] k := hfk.mono fun z hz => by simpa using hz
  rcases h₁ : meromorphicOrderAt f₁ 0 with _ | n₁
  · exact (meromorphicOrderAt_eq_top_iff.mp h₁).mono fun z hz => by
      simp only [hf₁] at hz
      exact sub_eq_zero.mp hz
  exfalso
  have hn₁ := int_eq_zero_of_zpow_eq_one hlam
    (pow_order_eq_one_of_invariant hg hg0 hgd hf₁m hinv₁ h₁)
  subst hn₁
  obtain ⟨k₁, hk₁, hk₁0, hfk₁⟩ := (meromorphicOrderAt_eq_int_iff hf₁m).mp h₁
  have hlimA : Tendsto f₁ (𝓝[≠] (0 : ℂ)) (𝓝 (k₁ 0)) :=
    (hk₁.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr'
      (hfk₁.mono fun z hz => by simpa using hz.symm)
  have hlimB : Tendsto f₁ (𝓝[≠] (0 : ℂ)) (𝓝 0) := by
    have hk' : Tendsto (fun z => k z - k 0) (𝓝[≠] (0 : ℂ)) (𝓝 (k 0 - k 0)) :=
      ((hk.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).sub tendsto_const_nhds)
    rw [sub_self] at hk'
    exact hk'.congr' (hfk'.mono fun z hz => by simp only [hf₁]; rw [hz])
  exact hk₁0 (tendsto_nhds_unique hlimA hlimB)

/-! ### The frame -/

/-- The multiplier conditions at a fixed point: regular, fixed, multiplier nonzero and not a root
of unity. -/
structure IsLinearizableFixedPoint (R : RatFunc ℂ) : Prop where
  regular : 0 ≤ ratOrder R 0
  fixed : ratValue R 0 = 0
  mult_ne_zero : ratValue (ratFuncDeriv R) 0 ≠ 0
  not_root : ∀ n : ℕ, 0 < n → ratValue (ratFuncDeriv R) 0 ^ n ≠ 1

namespace IsLinearizableFixedPoint

variable (hfix : IsLinearizableFixedPoint R)
include hfix

theorem analyticAt : AnalyticAt ℂ (fun z => ratValue R z) 0 := analyticAt_ratValue_zero hfix.regular

theorem deriv_ne_zero : deriv (fun z => ratValue R z) 0 ≠ 0 := by
  rw [deriv_ratValue_zero hfix.regular]; exact hfix.mult_ne_zero

/-- Precomposition with the map. -/
def pull : MeroGerm →+* MeroGerm :=
  meroPullHom hfix.analyticAt hfix.fixed hfix.deriv_ne_zero

theorem pull_ofMero {f : ℂ → ℂ} (hf : MeromorphicAt f 0) :
    hfix.pull (ofMero f hf) = ofMero (f ∘ fun z => ratValue R z)
      (by
        have h := hf
        rw [← hfix.fixed] at h
        exact h.comp_analyticAt hfix.analyticAt) :=
  meroPullHom_ofMero _ _ _ hf

theorem ofMero_ratValue : ofMero (fun z => ratValue R z) hfix.analyticAt.meromorphicAt
    = algebraMap (RatFunc ℂ) MeroGerm R :=
  (algebraMap_ratFunc_meroGerm R).symm

theorem pull_algebraMap (hR : ¬ ∃ c : ℂ, R = RatFunc.C c) (Q : RatFunc ℂ) :
    hfix.pull (algebraMap (RatFunc ℂ) MeroGerm Q)
      = algebraMap (RatFunc ℂ) MeroGerm (ratFuncSubstitutionAlgHom R hR Q) := by
  have hext : hfix.pull.comp (algebraMap (RatFunc ℂ) MeroGerm)
      = (algebraMap (RatFunc ℂ) MeroGerm).comp
          (ratFuncSubstitutionAlgHom R hR).toRingHom := by
    apply IsLocalization.ringHom_ext (nonZeroDivisors ℂ[X])
    apply Polynomial.ringHom_ext
    · intro a
      simp only [RingHom.comp_apply, RatFunc.algebraMap_C, AlgHom.toRingHom_eq_coe,
        RingHom.coe_coe, ratFuncSubstitutionAlgHom_C]
      rw [algebraMap_ratFunc_meroGerm, hfix.pull_ofMero, ofMero_eq_iff]
      exact Eventually.of_forall fun z => by simp [ratValue_C]
    · simp only [RingHom.comp_apply, RatFunc.algebraMap_X, AlgHom.toRingHom_eq_coe,
        RingHom.coe_coe, ratFuncSubstitutionAlgHom_X]
      rw [algebraMap_X_meroGerm, zGerm, hfix.pull_ofMero, ← hfix.ofMero_ratValue]
      rfl
  exact RingHom.congr_fun hext Q

theorem pull_fixed (y : MeroGerm) (hy : hfix.pull y = y) :
    ∃ a : RatFunc ℂ, algebraMap (RatFunc ℂ) MeroGerm a = y := by
  obtain ⟨f, hf, rfl⟩ := y.exists_rep
  rw [hfix.pull_ofMero, ofMero_eq_iff] at hy
  have hlam : ∀ n : ℕ, 0 < n → deriv (fun z => ratValue R z) 0 ^ n ≠ 1 := by
    rw [deriv_ratValue_zero hfix.regular]; exact hfix.not_root
  obtain ⟨c, hc⟩ := exists_const_of_invariant hfix.analyticAt hfix.fixed hfix.deriv_ne_zero
    hlam hf hy
  refine ⟨RatFunc.C c, ?_⟩
  rw [algebraMap_ratFunc_meroGerm, ofMero_eq_iff]
  exact hc.symm.mono fun z hz => by
    show ratValue (RatFunc.C c) z = f z
    rw [ratValue_C]
    exact hz

theorem meroDeriv_pull (x : MeroGerm) :
    meroDeriv (hfix.pull x)
      = algebraMap (RatFunc ℂ) MeroGerm (ratFuncDeriv R) * hfix.pull (meroDeriv x) := by
  rw [pull, meroDeriv_meroPullHom]
  congr 1
  rw [← meroDeriv_algebraMap, ← hfix.ofMero_ratValue, meroDeriv_ofMero]

/-- **The Ritt frame of a rational map at a linearizable fixed point.** -/
def frame (hR : ¬ ∃ c : ℂ, R = RatFunc.C c) : RittFrame (RatFunc ℂ) MeroGerm where
  σ := hfix.pull
  ψ := (ratFuncSubstitutionAlgHom R hR).toRingHom
  d := meroDeriv
  dK := ratFuncDeriv
  ρ := ratFuncDeriv R
  comp := hfix.pull_algebraMap hR
  fixed := hfix.pull_fixed
  d_add := meroDeriv_add
  d_mul := fun x y => by rw [meroDeriv_mul]; ring
  d_base := meroDeriv_algebraMap
  ρ_ne := ratFuncDeriv_ne_zero_of_nonconst' hR
  chain := hfix.meroDeriv_pull

theorem frame_isRational (hR : ¬ ∃ c : ℂ, R = RatFunc.C c) :
    (hfix.frame hR).IsRational R hR :=
  ⟨fun _ => rfl, fun _ => rfl, rfl⟩

end IsLinearizableFixedPoint

/-! ### Differential algebraicity of analytic germs -/

/-- The derivation of `ℂ(z)` as a differential ring. -/
abbrev ratFuncDerivDifferential : Differential (RatFunc ℂ) :=
  letI : Algebra ℤ (RatFunc ℂ) := Ring.toIntAlgebra _
  ⟨Derivation.restrictScalars ℤ ratFuncDerivation⟩

theorem ratFuncDerivDifferential_deriv (a : RatFunc ℂ) :
    letI := ratFuncDerivDifferential
    a′ = ratFuncDeriv a := rfl

theorem meroGerm_differentialAlgebra :
    letI := ratFuncDerivDifferential
    DifferentialAlgebra (RatFunc ℂ) MeroGerm := by
  letI := ratFuncDerivDifferential
  exact ⟨fun a => by
    show meroDeriv (algebraMap (RatFunc ℂ) MeroGerm a)
      = algebraMap (RatFunc ℂ) MeroGerm (ratFuncDeriv a)
    exact meroDeriv_algebraMap a⟩

theorem analyticAt_iteratedDeriv_nat {f : ℂ → ℂ} {z : ℂ} (hf : AnalyticAt ℂ f z) :
    ∀ n : ℕ, AnalyticAt ℂ (iteratedDeriv n f) z
  | 0 => by rw [iteratedDeriv_zero]; exact hf
  | n + 1 => by rw [iteratedDeriv_succ]; exact (analyticAt_iteratedDeriv_nat hf n).deriv

theorem differentialJet_ofMero {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (n : ℕ) :
    differentialJet n (ofMero f hf.meromorphicAt)
      = ofMero (iteratedDeriv n f) (analyticAt_iteratedDeriv_nat hf n).meromorphicAt := by
  induction n with
  | zero => simp [differentialJet]
  | succ n ih =>
      rw [differentialJet_succ, ih]
      show meroDeriv _ = _
      rw [meroDeriv_ofMero]
      exact (ofMero_eq_iff _ _).mpr (Eventually.of_forall fun z => by rw [iteratedDeriv_succ])

theorem meromorphicAt_mvEval {ι : Type*} (F : ι → ℂ → ℂ) (hF : ∀ i, MeromorphicAt (F i) 0)
    (P : MvPolynomial ι ℂ) : MeromorphicAt (fun z => MvPolynomial.eval (fun i => F i z) P) 0 := by
  induction P using MvPolynomial.induction_on with
  | C a =>
      have heq : (fun z => MvPolynomial.eval (fun i => F i z) (MvPolynomial.C a)) = fun _ => a := by
        funext z; simp
      rw [heq]
      exact MeromorphicAt.const a 0
  | add p q hp hq =>
      have heq : (fun z => MvPolynomial.eval (fun i => F i z) (p + q))
          = (fun z => MvPolynomial.eval (fun i => F i z) p)
            + fun z => MvPolynomial.eval (fun i => F i z) q := by
        funext z; simp
      rw [heq]
      exact hp.add hq
  | mul_X p i hp =>
      have heq : (fun z => MvPolynomial.eval (fun i => F i z) (p * MvPolynomial.X i))
          = (fun z => MvPolynomial.eval (fun i => F i z) p) * F i := by
        funext z; simp
      rw [heq]
      exact hp.mul (hF i)

/-- Evaluation of a polynomial with constant coefficients at germs is the germ of the pointwise
evaluation. -/
theorem aeval_ofMero {ι : Type*} (F : ι → ℂ → ℂ) (hF : ∀ i, MeromorphicAt (F i) 0)
    (P : MvPolynomial ι ℂ) :
    MvPolynomial.aeval (fun i => ofMero (F i) (hF i)) P
      = ofMero (fun z => MvPolynomial.eval (fun i => F i z) P) (meromorphicAt_mvEval F hF P) := by
  induction P using MvPolynomial.induction_on with
  | C a =>
      rw [MvPolynomial.aeval_C, algebraMap_complex_meroGerm, ofMero_eq_iff]
      exact Eventually.of_forall fun z => by simp
  | add p q hp hq =>
      rw [map_add, hp, hq, ofMero_add, ofMero_eq_iff]
      exact Eventually.of_forall fun z => by simp
  | mul_X p i hp =>
      rw [map_mul, hp, MvPolynomial.aeval_X, ofMero_mul, ofMero_eq_iff]
      exact Eventually.of_forall fun z => by simp

theorem algebraMap_polynomial_meroGerm (p : ℂ[X]) :
    algebraMap (RatFunc ℂ) MeroGerm (algebraMap ℂ[X] (RatFunc ℂ) p) = Polynomial.aeval zGerm p := by
  rw [algebraMap_ratFunc_meroGerm, aeval_zGerm, ofMero_eq_iff]
  exact Eventually.of_forall fun z => by simp [ratValue]

/-- **An analytic germ satisfying an algebraic differential equation near the origin is
differentially algebraic in the germ field.** -/
theorem differentialAlgebraicOver_ofMero {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) {U : Set ℂ}
    (hU : U ∈ 𝓝 (0 : ℂ)) {n : ℕ} {P : MvPolynomial (Fin (n + 2)) ℂ} (hP : P ≠ 0)
    (hrel : ∀ z ∈ U, MvPolynomial.eval
      (Fin.cons z fun j : Fin (n + 1) => iteratedDeriv (j : ℕ) f z) P = 0) :
    letI := ratFuncDerivDifferential
    DifferentialAlgebraicOver (RatFunc ℂ) (ofMero f hf.meromorphicAt) := by
  letI := ratFuncDerivDifferential
  set G : MvPolynomial (Fin (n + 1)) ℂ[X] := reshapeJet n P with hG
  set Q : MvPolynomial (Fin (n + 1)) (RatFunc ℂ) :=
    MvPolynomial.map (algebraMap ℂ[X] (RatFunc ℂ)) G with hQdef
  have hG0 : G ≠ 0 := fun hzero => hP (reshapeJet_injective n (by simpa [hG] using hzero))
  have hQ0 : Q ≠ 0 := by
    intro hzero
    apply hG0
    apply MvPolynomial.map_injective _ (RatFunc.algebraMap_injective ℂ)
    simpa [hQdef] using hzero
  set jets : Fin (n + 1) → MeroGerm := fun j => differentialJet (j : ℕ) (ofMero f hf.meromorphicAt)
    with hjets
  -- the reshaped evaluation is the evaluation with the coordinate in slot zero
  have hhom : (MvPolynomial.eval₂Hom (Polynomial.aeval zGerm).toRingHom jets).comp (reshapeJet n)
      = (MvPolynomial.aeval (Fin.cons zGerm jets : Fin (n + 2) → MeroGerm)).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [reshapeJet]
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [reshapeJet]
      · simp [reshapeJet]
  have hfield : MvPolynomial.aeval jets Q = 0 := by
    rw [MvPolynomial.aeval_def, hQdef, MvPolynomial.eval₂_map]
    have hcomp : (algebraMap (RatFunc ℂ) MeroGerm).comp (algebraMap ℂ[X] (RatFunc ℂ))
        = (Polynomial.aeval zGerm).toRingHom := by
      ext p
      · simp only [RingHom.coe_comp, Function.comp_apply]
        rw [algebraMap_polynomial_meroGerm]
        rfl
      · simp only [RingHom.coe_comp, Function.comp_apply]
        rw [algebraMap_polynomial_meroGerm]
        rfl
    rw [hcomp]
    have h1 : MvPolynomial.eval₂ (Polynomial.aeval zGerm).toRingHom jets G
        = MvPolynomial.aeval (Fin.cons zGerm jets : Fin (n + 2) → MeroGerm) P := by
      rw [hG]
      exact RingHom.congr_fun hhom P
    rw [h1]
    have hjet : (Fin.cons zGerm jets : Fin (n + 2) → MeroGerm)
        = fun i => ofMero ((Fin.cons (id : ℂ → ℂ)
            (fun j : Fin (n + 1) => iteratedDeriv (j : ℕ) f) : Fin (n + 2) → ℂ → ℂ) i)
          (by
            refine Fin.cases ?_ (fun j => ?_) i
            · exact analyticAt_id.meromorphicAt
            · exact (analyticAt_iteratedDeriv_nat hf j).meromorphicAt) := by
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · rfl
      · simp only [Fin.cons_succ, hjets]
        exact differentialJet_ofMero hf j
    rw [hjet, aeval_ofMero, ← ofMero_zero, ofMero_eq_iff]
    filter_upwards [nhdsWithin_le_nhds hU] with z hz
    have := hrel z hz
    convert this using 3
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · rfl
  unfold DifferentialAlgebraicOver DifferentialIndependent
  intro hindependent
  let e : Fin (n + 1) → Unit × ℕ := fun j => ((), (j : ℕ))
  have he : Function.Injective e := fun i j hij => Fin.ext (congrArg Prod.snd hij)
  have hrename : MvPolynomial.rename e Q ≠ 0 := fun hzero =>
    hQ0 (MvPolynomial.rename_injective e he hzero)
  apply hrename
  apply hindependent.eq_zero_of_aeval_eq_zero
  rw [MvPolynomial.aeval_rename]
  simpa [e, Function.comp_def, hjets] using hfield

/-! ### Ritt's implication at a fixed point -/

theorem ofMero_ne_zero_of_deriv_ne_zero {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (hf' : deriv f 0 ≠ 0) :
    ofMero f hf.meromorphicAt ≠ 0 := by
  intro h
  have hev := (ofMero_eq_zero_iff _).mp h
  have hz : ∀ᶠ z in 𝓝 (0 : ℂ), f z = 0 :=
    hf.frequently_zero_iff_eventually_zero.mp hev.frequently
  exact hf' (by rw [Filter.EventuallyEq.deriv_eq hz, deriv_const])

theorem ofMero_ne_zero_of_ne_zero {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (hf0 : f 0 ≠ 0) :
    ofMero f hf.meromorphicAt ≠ 0 := by
  intro h
  have hev := (ofMero_eq_zero_iff _).mp h
  have hlim : Tendsto f (𝓝[≠] (0 : ℂ)) (𝓝 0) :=
    tendsto_const_nhds.congr' (hev.mono fun z hz => hz.symm)
  exact hf0 (tendsto_nhds_unique (hf.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) hlim)

/-- **Ritt's implication at a fixed point.**  Let `R` have degree at least two and a fixed point `0`
with multiplier nonzero and not a root of unity.  If an analytic germ `κ` with `κ'(0) ≠ 0`
linearizes
`R`, `κ(R(z)) = q·κ(z)`, and satisfies an algebraic differential equation on a neighbourhood of `0`,
then `R` carries a rational cocycle `A(R)·R'^N = β·A` with `N ≥ 1`, `β ≠ 0`, `A ≠ 0`. -/
theorem ratTransport_of_differentiallyAlgebraicOn_linearizer (hR : ¬ ∃ c : ℂ, R = RatFunc.C c)
    (hd : 2 ≤ ratFuncDegree R) (hfix : IsLinearizableFixedPoint R) {κ : ℂ → ℂ}
    (hκ : AnalyticAt ℂ κ 0) (hκ' : deriv κ 0 ≠ 0) {q : ℂ} (hq : q ≠ 0)
    (hfe : ∀ᶠ z in 𝓝 (0 : ℂ), κ (ratValue R z) = q * κ z) {U : Set ℂ} (hU : U ∈ 𝓝 (0 : ℂ))
    (hDA : DifferentiallyAlgebraicOn κ U) :
    ∃ N : ℕ, 0 < N ∧ ∃ β : ℂ, β ≠ 0 ∧ ∃ A : RatFunc ℂ, A ≠ 0 ∧
      IsRatAffineTransport R hR (N : ℤ) (RatFunc.C β) 0 A := by
  letI := ratFuncDerivDifferential
  haveI := meroGerm_differentialAlgebra
  obtain ⟨n, P, hP, hrel⟩ := hDA
  set τ := ofMero κ hκ.meromorphicAt with hτdef
  have hτ : τ ≠ 0 := ofMero_ne_zero_of_deriv_ne_zero hκ hκ'
  have hdτ : (hfix.frame hR).d τ ≠ 0 := by
    show meroDeriv τ ≠ 0
    rw [hτdef, meroDeriv_ofMero]
    have h := ofMero_ne_zero_of_ne_zero hκ.deriv hκ'
    exact h
  have hshift : (hfix.frame hR).σ τ = algebraMap (RatFunc ℂ) MeroGerm (RatFunc.C q) * τ := by
    show hfix.pull τ = _
    rw [hτdef, hfix.pull_ofMero, algebraMap_ratFunc_meroGerm, ofMero_mul, ofMero_eq_iff]
    filter_upwards [nhdsWithin_le_nhds hfe] with z hz
    simp only [Function.comp_apply, Pi.mul_apply]
    rw [hz, ratValue_C]
  have hdiff : (hfix.frame hR).d = ⇑(Differential.deriv : Derivation ℤ MeroGerm MeroGerm) := rfl
  exact (hfix.frame_isRational hR).ratTransport_of_linearizer hdiff hd hfix.regular hfix.fixed
    hfix.mult_ne_zero hfix.not_root hτ hdτ hq hshift
    (differentialAlgebraicOver_ofMero hκ hU hP hrel)

/-- **Ritt's implication at a fixed point, with the multiplier.**  Under the hypotheses of
`ratTransport_of_differentiallyAlgebraicOn_linearizer`, the map satisfies the rational cocycle
`R'^N·B = λ^{N+j}·B(R)` with `λ = R'(0)`. -/
theorem ratCocycle_of_differentiallyAlgebraicOn_linearizer (hR : ¬ ∃ c : ℂ, R = RatFunc.C c)
    (hd : 2 ≤ ratFuncDegree R) (hfix : IsLinearizableFixedPoint R) {κ : ℂ → ℂ}
    (hκ : AnalyticAt ℂ κ 0) (hκ' : deriv κ 0 ≠ 0) {q : ℂ} (hq : q ≠ 0)
    (hfe : ∀ᶠ z in 𝓝 (0 : ℂ), κ (ratValue R z) = q * κ z) {U : Set ℂ} (hU : U ∈ 𝓝 (0 : ℂ))
    (hDA : DifferentiallyAlgebraicOn κ U) :
    ∃ N : ℕ, 0 < N ∧ ∃ j : ℤ, ∃ B : RatFunc ℂ, B ≠ 0 ∧
      ratFuncDeriv R ^ N * B
        = RatFunc.C (ratValue (ratFuncDeriv R) 0 ^ ((N : ℤ) + j))
          * ratFuncSubstitutionAlgHom R hR B := by
  letI := ratFuncDerivDifferential
  haveI := meroGerm_differentialAlgebra
  obtain ⟨n, P, hP, hrel⟩ := hDA
  set τ := ofMero κ hκ.meromorphicAt with hτdef
  have hτ : τ ≠ 0 := ofMero_ne_zero_of_deriv_ne_zero hκ hκ'
  have hdτ : (hfix.frame hR).d τ ≠ 0 := by
    show meroDeriv τ ≠ 0
    rw [hτdef, meroDeriv_ofMero]
    exact ofMero_ne_zero_of_ne_zero hκ.deriv hκ'
  have hshift : (hfix.frame hR).σ τ = algebraMap (RatFunc ℂ) MeroGerm (RatFunc.C q) * τ := by
    show hfix.pull τ = _
    rw [hτdef, hfix.pull_ofMero, algebraMap_ratFunc_meroGerm, ofMero_mul, ofMero_eq_iff]
    filter_upwards [nhdsWithin_le_nhds hfe] with z hz
    simp only [Function.comp_apply, Pi.mul_apply]
    rw [hz, ratValue_C]
  have hdiff : (hfix.frame hR).d = ⇑(Differential.deriv : Derivation ℤ MeroGerm MeroGerm) := rfl
  exact (hfix.frame_isRational hR).ratCocycle_of_linearizer hdiff hd hfix.regular hfix.fixed
    hfix.mult_ne_zero hfix.not_root hτ hdτ hq hshift
    (differentialAlgebraicOver_ofMero hκ hU hP hrel)

end

end GaloisForLFunctions.HTGeometry
