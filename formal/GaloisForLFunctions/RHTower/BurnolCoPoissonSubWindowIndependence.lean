import GaloisForLFunctions.RHTower.BurnolCoPoissonSubWindowSource
import GaloisForLFunctions.RHTower.FractionalPartZeta

/-!
# Independence of the sub-window co-Poisson family

The Mellin transform of the sub-window co-Poisson vector at aperture `A` is
`(d^(-w) - c^(-w)) zeta(w)/w` up to the archimedean factor.  Pairing a vanishing linear combination
of such vectors against the Mellin evaluator therefore produces a vanishing exponential sum on the
part of the strip where zeta does not vanish.  The sum extends to an entire function, so the
identity theorem propagates the relation to the whole plane, where Dedekind's independence of
characters forces every coefficient to vanish.

Consequently the explicit family is linearly independent, and an explicit ladder of window ends
inside `(A, 1/A)` shows that both the explicit co-Poisson subspace and Burnol's own co-Poisson
source space at aperture `A` are infinite dimensional for every `0 < A < 1`.
-/

open Complex Real MeasureTheory Set Filter Topology Finset
open scoped InnerProductSpace

noncomputable section

namespace RHTower

/-- The character `w ↦ exp (-w a)` of the additive group of the complex plane. -/
def logCpowChar (a : ℝ) : Multiplicative ℂ →* ℂ where
  toFun := fun m => Complex.exp (-(Multiplicative.toAdd m) * (a : ℂ))
  map_one' := by
    show Complex.exp (-(Multiplicative.toAdd (1 : Multiplicative ℂ)) * (a : ℂ)) = 1
    have h : Multiplicative.toAdd (1 : Multiplicative ℂ) = 0 := rfl
    rw [h]
    simp
  map_mul' := fun m n => by
    show Complex.exp (-(Multiplicative.toAdd (m * n)) * (a : ℂ)) =
      Complex.exp (-(Multiplicative.toAdd m) * (a : ℂ)) *
        Complex.exp (-(Multiplicative.toAdd n) * (a : ℂ))
    have h : Multiplicative.toAdd (m * n) =
        Multiplicative.toAdd m + Multiplicative.toAdd n := rfl
    rw [h, ← Complex.exp_add]
    congr 1
    ring

theorem logCpowChar_apply (a : ℝ) (m : Multiplicative ℂ) :
    logCpowChar a m = Complex.exp (-(Multiplicative.toAdd m) * (a : ℂ)) := rfl

/-- For a positive base the exponential character is the complex power. -/
theorem exp_neg_mul_log_eq_cpow {x : ℝ} (hx : 0 < x) (w : ℂ) :
    Complex.exp (-w * ((Real.log x : ℝ) : ℂ)) = ((x : ℝ) : ℂ) ^ (-w) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne'),
    ← Complex.ofReal_log hx.le]
  congr 1
  ring

theorem logCpowChar_eq_cpow {x : ℝ} (hx : 0 < x) (w : ℂ) :
    logCpowChar (Real.log x) (Multiplicative.ofAdd w) = ((x : ℝ) : ℂ) ^ (-w) := by
  rw [logCpowChar_apply]
  exact exp_neg_mul_log_eq_cpow hx w

/-- Distinct positive bases give distinct characters. -/
theorem logCpowChar_injective {x y : ℝ} (hx : 0 < x) (hy : 0 < y)
    (h : logCpowChar (Real.log x) = logCpowChar (Real.log y)) : x = y := by
  have h1 := congrArg (fun f : Multiplicative ℂ →* ℂ => f (Multiplicative.ofAdd (-1 : ℂ))) h
  rw [logCpowChar_eq_cpow hx, logCpowChar_eq_cpow hy, neg_neg, Complex.cpow_one,
    Complex.cpow_one] at h1
  exact_mod_cast h1

/-- The Mellin evaluation of a sub-window vector read at a common aperture. -/
theorem inner_burnolExtendedSoninEvaluationVector_subWindowAt {c d : ℝ}
    {w : ℂ} (hlo : 1 / 2 < w.re) (hhi : w.re < 1)
    {A : ℝ} (hA : 0 < A) (hc : 0 < c) (hcd : c ≤ d) (hAle : A ≤ subWindowAperture c d) :
    ⟪burnolExtendedSoninEvaluationVector w A hlo hhi hA,
        coPoissonSubWindowSoninAt hc hcd hAle⟫_ℂ =
      mellinCompletionFactor w *
        ((((d : ℝ) : ℂ) ^ (-w) - ((c : ℝ) : ℂ) ^ (-w)) * (-(riemannZeta w / w))) := by
  rw [inner_burnolExtendedSoninEvaluationVector, coe_coPoissonSubWindowSoninAt]
  exact soninMellinEvaluation_coPoissonSubWindowSonin hc hcd (by linarith) hhi


/-- **The explicit sub-window co-Poisson vectors are linearly independent.**  Pairing against the
Mellin evaluator turns a vanishing linear combination into a vanishing exponential sum on the strip;
the identity theorem propagates it to the whole plane, where Dedekind's independence of characters
forces every coefficient to vanish. -/
theorem linearIndependent_coPoissonSubWindowSoninAt {A c : ℝ} (hA : 0 < A) (hc : 0 < c)
    {ι : Type*} [Fintype ι] {d : ι → ℝ} (hd : ∀ i, c < d i) (hdinj : Function.Injective d)
    (hAle : ∀ i, A ≤ subWindowAperture c (d i)) :
    LinearIndependent ℂ (fun i : ι => coPoissonSubWindowSoninAt hc (hd i).le (hAle i)) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hsum i0
  have hdpos : ∀ i, 0 < d i := fun i => lt_trans hc (hd i)
  have key : ∀ w : ℂ, 1 / 2 < w.re → w.re < 1 → riemannZeta w ≠ 0 →
      ∑ i : ι, g i * ((((d i : ℝ)) : ℂ) ^ (-w) - ((c : ℝ) : ℂ) ^ (-w)) = 0 := by
    intro w hlo hhi hz
    have hw0 : (0 : ℝ) < w.re := by linarith
    have hwne : w ≠ 0 := by
      intro h
      rw [h, Complex.zero_re] at hw0
      exact lt_irrefl 0 hw0
    have hval : ∀ i : ι,
        ⟪burnolExtendedSoninEvaluationVector w A hlo hhi hA,
            coPoissonSubWindowSoninAt hc (hd i).le (hAle i)⟫_ℂ =
          mellinCompletionFactor w *
            ((((d i : ℝ) : ℂ) ^ (-w) - ((c : ℝ) : ℂ) ^ (-w)) * (-(riemannZeta w / w))) :=
      fun i =>
        inner_burnolExtendedSoninEvaluationVector_subWindowAt hlo hhi hA hc (hd i).le (hAle i)
    have hk : ∑ i : ι, g i *
        ⟪burnolExtendedSoninEvaluationVector w A hlo hhi hA,
          coPoissonSubWindowSoninAt hc (hd i).le (hAle i)⟫_ℂ = 0 := by
      have h0 := congrArg (innerSL ℂ (burnolExtendedSoninEvaluationVector w A hlo hhi hA)) hsum
      rw [map_sum, map_zero] at h0
      simp only [map_smul, smul_eq_mul, innerSL_apply_apply] at h0
      exact h0
    have hk2 : (mellinCompletionFactor w * (-(riemannZeta w / w))) *
        ∑ i : ι, g i * ((((d i : ℝ)) : ℂ) ^ (-w) - ((c : ℝ) : ℂ) ^ (-w)) = 0 := by
      rw [Finset.mul_sum, ← hk]
      exact Finset.sum_congr rfl fun i _ => by rw [hval i]; ring
    have hM : mellinCompletionFactor w ≠ 0 := mellinCompletionFactor_ne_zero hw0
    have hZ : -(riemannZeta w / w) ≠ 0 := neg_ne_zero.mpr (div_ne_zero hz hwne)
    exact (mul_eq_zero.mp hk2).resolve_left (mul_ne_zero hM hZ)
  set F : ℂ → ℂ := fun w => ∑ i : ι, g i *
      (Complex.exp (-w * ((Real.log (d i) : ℝ) : ℂ)) -
        Complex.exp (-w * ((Real.log c : ℝ) : ℂ))) with hFdef
  have hFapp : ∀ w : ℂ, F w = ∑ i : ι, g i *
      ((((d i : ℝ)) : ℂ) ^ (-w) - ((c : ℝ) : ℂ) ^ (-w)) := by
    intro w
    simp only [hFdef]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [exp_neg_mul_log_eq_cpow (hdpos i) w, exp_neg_mul_log_eq_cpow hc w]
  have hFdiff : Differentiable ℂ F := by
    rw [hFdef]
    fun_prop
  have hFan : AnalyticOnNhd ℂ F Set.univ := analyticOnNhd_univ_iff_differentiable.mpr hFdiff
  set w₀ : ℂ := ((3 / 4 : ℝ) : ℂ) with hw₀
  have hw₀re : w₀.re = 3 / 4 := Complex.ofReal_re _
  have hz₀ : riemannZeta w₀ ≠ 0 :=
    riemannZeta_ne_zero_of_ofReal_mem_Ioo (by norm_num) (by norm_num)
  have hne1 : w₀ ≠ 1 := by
    intro h
    rw [h, Complex.one_re] at hw₀re
    norm_num at hw₀re
  have hev : ∀ᶠ w in 𝓝 w₀, riemannZeta w ≠ 0 :=
    ((differentiableAt_riemannZeta hne1).continuousAt).eventually_ne hz₀
  have hevlo : ∀ᶠ w in 𝓝 w₀, 1 / 2 < w.re :=
    (isOpen_lt continuous_const Complex.continuous_re).eventually_mem
      (by show (1 : ℝ) / 2 < w₀.re; rw [hw₀re]; norm_num)
  have hevhi : ∀ᶠ w in 𝓝 w₀, w.re < 1 :=
    (isOpen_lt Complex.continuous_re continuous_const).eventually_mem
      (by show w₀.re < (1 : ℝ); rw [hw₀re]; norm_num)
  have hFzero : F =ᶠ[𝓝 w₀] 0 := by
    filter_upwards [hev, hevlo, hevhi] with w h1 h2 h3
    rw [hFapp w]
    exact key w h2 h3 h1
  have hall : Set.EqOn F 0 Set.univ :=
    hFan.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
      (Set.mem_univ w₀) hFzero
  have hLI : LinearIndependent ℂ
      (fun f : Multiplicative ℂ →* ℂ => (f : Multiplicative ℂ → ℂ)) :=
    linearIndependent_monoidHom (Multiplicative ℂ) ℂ
  set ψ : Option ι → (Multiplicative ℂ →* ℂ) :=
    fun j => Option.rec (logCpowChar (Real.log c)) (fun i => logCpowChar (Real.log (d i))) j with hψ
  have hψinj : Function.Injective ψ := by
    intro j1 j2 h
    match j1, j2 with
    | none, none => rfl
    | none, some i => exact absurd (logCpowChar_injective hc (hdpos i) h) (ne_of_lt (hd i))
    | some i, none => exact absurd (logCpowChar_injective (hdpos i) hc h) (ne_of_gt (hd i))
    | some i1, some i2 =>
      exact congrArg some (hdinj (logCpowChar_injective (hdpos i1) (hdpos i2) h))
  have hcomp := hLI.comp ψ hψinj
  rw [Fintype.linearIndependent_iff] at hcomp
  set lam : Option ι → ℂ := fun j => Option.rec (-(∑ i : ι, g i)) g j with hlam
  have hrel : ∑ j : Option ι, lam j •
      ((fun f : Multiplicative ℂ →* ℂ => (f : Multiplicative ℂ → ℂ)) ∘ ψ) j = 0 := by
    funext m
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Function.comp_apply, Pi.zero_apply]
    rw [Fintype.sum_option]
    have hFx : F (Multiplicative.toAdd m) = 0 := hall (Set.mem_univ _)
    simp only [hFdef] at hFx
    have hexpand : ∑ i : ι, g i *
        (Complex.exp (-(Multiplicative.toAdd m) * ((Real.log (d i) : ℝ) : ℂ)) -
          Complex.exp (-(Multiplicative.toAdd m) * ((Real.log c : ℝ) : ℂ))) =
        (∑ i : ι, g i * Complex.exp (-(Multiplicative.toAdd m) * ((Real.log (d i) : ℝ) : ℂ))) -
          (∑ i : ι, g i) *
            Complex.exp (-(Multiplicative.toAdd m) * ((Real.log c : ℝ) : ℂ)) := by
      rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [hexpand] at hFx
    show lam none * (ψ none) m + ∑ i : ι, lam (some i) * (ψ (some i)) m = 0
    have hnone : (ψ none) m =
        Complex.exp (-(Multiplicative.toAdd m) * ((Real.log c : ℝ) : ℂ)) := rfl
    have hsome : ∀ i : ι, (ψ (some i)) m =
        Complex.exp (-(Multiplicative.toAdd m) * ((Real.log (d i) : ℝ) : ℂ)) := fun _ => rfl
    have hlamnone : lam none = -(∑ i : ι, g i) := rfl
    have hlamsome : ∀ i : ι, lam (some i) = g i := fun _ => rfl
    rw [hnone, hlamnone]
    simp only [hsome, hlamsome]
    linear_combination hFx
  exact hcomp lam hrel (some i0)


/-- A sub-window co-Poisson source read at any smaller aperture. -/
def coPoissonSubWindowSourceAt {A c d : ℝ} (hA : 0 < A) (hc : 0 < c) (hcd : c ≤ d)
    (hAle : A ≤ subWindowAperture c d) : BurnolCoPoissonSource A where
  seed := coPoissonSubWindowSeed c d
  seed_integrable := integrable_coPoissonSubWindowSeed hc
  seed_support := by
    refine (support_subWindow_symmetric hc hcd).trans ?_
    intro t ht
    have hapos : 0 < subWindowAperture c d := subWindowAperture_pos hc hcd
    refine ⟨le_trans hAle ht.1, le_trans ht.2 ?_⟩
    rw [inv_le_inv₀ hapos hA]
    exact hAle
  vector := coPoissonSubWindowSoninAt hc hcd hAle
  vector_eq_sum := coPoissonSubWindowEven_coeFn hc hcd

theorem coPoissonSubWindowEven_mem_burnolCoPoissonGeneratorSet {A c d : ℝ} (hA : 0 < A)
    (hc : 0 < c) (hcd : c ≤ d) (hAle : A ≤ subWindowAperture c d) :
    coPoissonSubWindowEven hc hcd ∈ burnolCoPoissonGeneratorSet A :=
  ⟨coPoissonSubWindowSourceAt hA hc hcd hAle, Or.inl rfl⟩

theorem coPoissonSubWindowEven_mem_burnolCoPoissonSourceSpace {A c d : ℝ} (hA : 0 < A)
    (hc : 0 < c) (hcd : c ≤ d) (hAle : A ≤ subWindowAperture c d) :
    coPoissonSubWindowEven hc hcd ∈ burnolCoPoissonSourceSpace A :=
  (burnolCoPoissonAlgebraicSourceSpace A).le_topologicalClosure
    (Submodule.subset_span
      (coPoissonSubWindowEven_mem_burnolCoPoissonGeneratorSet hA hc hcd hAle))

/-- An explicit strictly increasing ladder of upper window ends inside `(A, A⁻¹]`. -/
def subWindowLadder (A : ℝ) (n : ℕ) (i : Fin n) : ℝ :=
  A + (A⁻¹ - A) * ((((i : ℕ) : ℝ) + 1) / ((n : ℝ) + 1))

theorem sub_inv_self_pos {A : ℝ} (hA0 : 0 < A) (hA1 : A < 1) : 0 < A⁻¹ - A := by
  have h : (1 : ℝ) < A⁻¹ := (one_lt_inv₀ hA0).mpr hA1
  linarith

theorem lt_subWindowLadder {A : ℝ} (hA0 : 0 < A) (hA1 : A < 1) (n : ℕ) (i : Fin n) :
    A < subWindowLadder A n i := by
  have hgap := sub_inv_self_pos hA0 hA1
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hnum : (0 : ℝ) < ((i : ℕ) : ℝ) + 1 := by positivity
  have : 0 < (A⁻¹ - A) * ((((i : ℕ) : ℝ) + 1) / ((n : ℝ) + 1)) :=
    mul_pos hgap (div_pos hnum hn)
  simp only [subWindowLadder]
  linarith

theorem subWindowLadder_le_inv {A : ℝ} (hA0 : 0 < A) (hA1 : A < 1) (n : ℕ) (i : Fin n) :
    subWindowLadder A n i ≤ A⁻¹ := by
  have hgap := sub_inv_self_pos hA0 hA1
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hi : ((i : ℕ) : ℝ) + 1 ≤ (n : ℝ) + 1 := by
    have : ((i : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast (le_of_lt i.isLt)
    linarith
  have hfrac : (((i : ℕ) : ℝ) + 1) / ((n : ℝ) + 1) ≤ 1 := (div_le_one hn).mpr hi
  have : (A⁻¹ - A) * ((((i : ℕ) : ℝ) + 1) / ((n : ℝ) + 1)) ≤ (A⁻¹ - A) * 1 :=
    mul_le_mul_of_nonneg_left hfrac hgap.le
  simp only [subWindowLadder]
  linarith

theorem subWindowLadder_aperture {A : ℝ} (hA0 : 0 < A) (hA1 : A < 1) (n : ℕ) (i : Fin n) :
    A ≤ subWindowAperture A (subWindowLadder A n i) :=
  le_of_eq (subWindowAperture_left_eq hA0 (lt_subWindowLadder hA0 hA1 n i).le
    (subWindowLadder_le_inv hA0 hA1 n i)).symm

theorem subWindowLadder_injective {A : ℝ} (hA0 : 0 < A) (hA1 : A < 1) (n : ℕ) :
    Function.Injective (subWindowLadder A n) := by
  intro i j hij
  have hgap := sub_inv_self_pos hA0 hA1
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  simp only [subWindowLadder] at hij
  have h1 : (A⁻¹ - A) * ((((i : ℕ) : ℝ) + 1) / ((n : ℝ) + 1)) =
      (A⁻¹ - A) * ((((j : ℕ) : ℝ) + 1) / ((n : ℝ) + 1)) := by linarith
  have h2 := mul_left_cancel₀ (ne_of_gt hgap) h1
  have h3 : ((i : ℕ) : ℝ) = ((j : ℕ) : ℝ) := by
    field_simp at h2
    linarith
  exact Fin.ext (by exact_mod_cast h3)

/-- **The explicit sub-window family is linearly independent at every size.** -/
theorem linearIndependent_subWindowLadder {A : ℝ} (hA0 : 0 < A) (hA1 : A < 1) (n : ℕ) :
    LinearIndependent ℂ (fun i : Fin n =>
      coPoissonSubWindowSoninAt hA0 (lt_subWindowLadder hA0 hA1 n i).le
        (subWindowLadder_aperture hA0 hA1 n i)) :=
  linearIndependent_coPoissonSubWindowSoninAt hA0 hA0 (lt_subWindowLadder hA0 hA1 n)
    (subWindowLadder_injective hA0 hA1 n) (subWindowLadder_aperture hA0 hA1 n)

/-- **The explicit co-Poisson subspace has arbitrarily large independent families.** -/
theorem exists_linearIndependent_mem_burnolSubWindowSpace {A : ℝ} (hA0 : 0 < A) (hA1 : A < 1)
    (n : ℕ) :
    ∃ v : Fin n → soninExtendedSpace A,
      (∀ i, v i ∈ burnolSubWindowSpace A) ∧ LinearIndependent ℂ v := by
  refine ⟨fun i => coPoissonSubWindowSoninAt hA0 (lt_subWindowLadder hA0 hA1 n i).le
    (subWindowLadder_aperture hA0 hA1 n i), fun i => ?_, linearIndependent_subWindowLadder hA0 hA1 n⟩
  refine (Submodule.span ℂ (burnolSubWindowGenerators A)).le_topologicalClosure ?_
  exact Submodule.subset_span
    ⟨A, subWindowLadder A n i, hA0, (lt_subWindowLadder hA0 hA1 n i).le,
      subWindowLadder_aperture hA0 hA1 n i, rfl⟩

/-- **The explicit co-Poisson subspace is infinite dimensional.** -/
theorem not_finiteDimensional_burnolSubWindowSpace {A : ℝ} (hA0 : 0 < A) (hA1 : A < 1) :
    ¬ FiniteDimensional ℂ (burnolSubWindowSpace A) := by
  intro hfin
  obtain ⟨v, hvmem, hvind⟩ :=
    exists_linearIndependent_mem_burnolSubWindowSpace hA0 hA1
      (Module.finrank ℂ (burnolSubWindowSpace A) + 1)
  have hv'ind : LinearIndependent ℂ (fun i => (⟨v i, hvmem i⟩ : burnolSubWindowSpace A)) :=
    LinearIndependent.of_comp (burnolSubWindowSpace A).subtype hvind
  have hcard := hv'ind.fintype_card_le_finrank
  simp only [Fintype.card_fin] at hcard
  omega

/-- **Burnol's own co-Poisson source space is infinite dimensional.**  The explicit sub-window
family already supplies arbitrarily many independent generators. -/
theorem not_finiteDimensional_burnolCoPoissonSourceSpace {A : ℝ} (hA0 : 0 < A) (hA1 : A < 1) :
    ¬ FiniteDimensional ℂ (burnolCoPoissonSourceSpace A) := by
  intro hfin
  set n := Module.finrank ℂ (burnolCoPoissonSourceSpace A) + 1 with hn
  have hmem : ∀ i : Fin n,
      (coPoissonSubWindowEven hA0 (lt_subWindowLadder hA0 hA1 n i).le : evenSubspace) ∈
        burnolCoPoissonSourceSpace A := fun i =>
    coPoissonSubWindowEven_mem_burnolCoPoissonSourceSpace hA0 hA0
      (lt_subWindowLadder hA0 hA1 n i).le (subWindowLadder_aperture hA0 hA1 n i)
  have hind : LinearIndependent ℂ (fun i : Fin n =>
      (coPoissonSubWindowEven hA0 (lt_subWindowLadder hA0 hA1 n i).le : evenSubspace)) :=
    (linearIndependent_subWindowLadder hA0 hA1 n).map'
      (soninExtendedSpace A).subtype (Submodule.ker_subtype _)
  have hv'ind : LinearIndependent ℂ
      (fun i : Fin n => (⟨_, hmem i⟩ : burnolCoPoissonSourceSpace A)) :=
    LinearIndependent.of_comp (burnolCoPoissonSourceSpace A).subtype hind
  have hcard := hv'ind.fintype_card_le_finrank
  simp only [Fintype.card_fin] at hcard
  omega

end RHTower
