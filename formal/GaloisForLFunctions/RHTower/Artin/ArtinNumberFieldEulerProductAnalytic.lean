import GaloisForLFunctions.RHTower.Artin.ArtinNumberFieldFinitePlaceNonvanishing
import GaloisForLFunctions.RHTower.NumberFieldFinitePlaceNormSummability
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn

/-!
# Absolute-half-plane Artin Euler product at number-field finite places

This module constructs the analytic finite-place Artin Euler product in `Re(s) > 1` from the
actual Frobenius--inertia factors.  Its proof is the compact M-test: finite-image factor control
provides a uniform `O(N(v)^(-Re(s)))` difference bound, and the number-field norm series is
summable past one.  It neither identifies this tprod with the formal Artin source nor continues it
past the absolute-convergence half-plane.
-/

open scoped BigOperators NumberField

noncomputable section

universe u

namespace GaloisForLFunctions

open Filter Topology

variable {K L G V : Type u}
variable [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
variable [Group G] [Finite G] [MulSemiringAction G L] [IsGaloisGroup G K L]
variable [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

/-- The canonical reciprocal Euler factor at a number-field finite place. -/
noncomputable def numberFieldFinitePlaceArtinEulerReciprocal
    (ρ : Representation ℂ G V)
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (s : ℂ) : ℂ :=
  ((numberFieldFinitePlaceLocalEulerPolynomial (K := K) (L := L) v ρ).eval
    ((v.asIdeal.absNorm : ℂ) ^ (-s)))⁻¹

/-- The canonical finite-place reciprocal Artin Euler product. -/
noncomputable def numberFieldFinitePlaceArtinEulerReciprocalProduct
    (ρ : Representation ℂ G V) (s : ℂ) : ℂ :=
  ∏' v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
    numberFieldFinitePlaceArtinEulerReciprocal (K := K) (L := L) ρ v s

/-- The absolute-convergence half-plane for the finite-place Artin Euler product. -/
def artinEulerAbsoluteHalfPlane : Set ℂ := {s | (1 : ℝ) < s.re}

theorem isOpen_artinEulerAbsoluteHalfPlane : IsOpen artinEulerAbsoluteHalfPlane := by
  exact isOpen_lt continuous_const Complex.continuous_re

/-- Every canonical finite-place reciprocal factor is continuous on a set in the positive
real-part half-plane. -/
theorem numberFieldFinitePlaceArtinEulerReciprocal_continuousOn
    (ρ : Representation ℂ G V)
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    {S : Set ℂ} (hS : S ⊆ {s | 0 < s.re}) :
    ContinuousOn (numberFieldFinitePlaceArtinEulerReciprocal (K := K) (L := L) ρ v) S := by
  have hv : 1 < v.asIdeal.absNorm := NumberField.HeightOneSpectrum.one_lt_absNorm v
  have hv0 : (v.asIdeal.absNorm : ℂ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (lt_trans Nat.zero_lt_one hv)
  letI : NeZero (v.asIdeal.absNorm : ℂ) := ⟨hv0⟩
  have harg : Continuous (fun s : ℂ => (v.asIdeal.absNorm : ℂ) ^ (-s)) :=
    (continuous_const_cpow (v.asIdeal.absNorm : ℂ)).comp continuous_neg
  have hden : Continuous (fun s : ℂ =>
      (numberFieldFinitePlaceLocalEulerPolynomial (K := K) (L := L) v ρ).eval
        ((v.asIdeal.absNorm : ℂ) ^ (-s))) :=
    (numberFieldFinitePlaceLocalEulerPolynomial (K := K) (L := L) v ρ).continuous.comp harg
  apply ContinuousOn.inv₀ hden.continuousOn
  intro s hs
  exact numberFieldFinitePlaceLocalEulerPolynomial_eval_ne_zero_of_re_pos v ρ (hS hs)

/-- The genuine finite-place Artin Euler factors have a locally uniform product in the absolute
half-plane.  This is only the source-side Euler product, not an analytic continuation theorem. -/
theorem hasProdLocallyUniformlyOn_numberFieldFinitePlaceArtinEulerReciprocal
    (ρ : Representation ℂ G V) :
    HasProdLocallyUniformlyOn
      (fun v => numberFieldFinitePlaceArtinEulerReciprocal (K := K) (L := L) ρ v)
      (numberFieldFinitePlaceArtinEulerReciprocalProduct (K := K) (L := L) ρ)
      artinEulerAbsoluteHalfPlane := by
  have hfun :
      (fun (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (s : ℂ) =>
        1 + (numberFieldFinitePlaceArtinEulerReciprocal (K := K) (L := L) ρ v s - 1)) =
      fun v => numberFieldFinitePlaceArtinEulerReciprocal (K := K) (L := L) ρ v := by
    funext v s
    ring
  refine hasProdLocallyUniformlyOn_of_forall_compact isOpen_artinEulerAbsoluteHalfPlane ?_
  intro S hS hScompact
  rcases S.eq_empty_or_nonempty with hSe | hSne
  · subst S
    have hu : Summable (fun _ : IsDedekindDomain.HeightOneSpectrum (𝓞 K) => (0 : ℝ)) :=
      summable_zero
    have hbound : ∀ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) in cofinite,
        ∀ s ∈ (∅ : Set ℂ),
          ‖numberFieldFinitePlaceArtinEulerReciprocal (K := K) (L := L) ρ v s - 1‖ ≤ 0 := by
      filter_upwards with v
      intro s hs
      simp at hs
    have hcont : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
        ContinuousOn
          (fun s : ℂ => numberFieldFinitePlaceArtinEulerReciprocal (K := K) (L := L) ρ v s - 1)
          (∅ : Set ℂ) := fun v => continuousOn_empty _
    have hmain := Summable.hasProdUniformlyOn_one_add hScompact hu hbound hcont
    rw [hfun] at hmain
    refine hmain.congr_right ?_
    intro s hs
    rw [numberFieldFinitePlaceArtinEulerReciprocalProduct]
    apply tprod_congr
    intro v
    ring
  · obtain ⟨s₀, hs₀S, hs₀⟩ :=
      hScompact.exists_isMinOn hSne Complex.continuous_re.continuousOn
    set σ : ℝ := s₀.re with hσdef
    have hσ : 1 < σ := by
      rw [hσdef]
      exact hS hs₀S
    have hσle : ∀ s ∈ S, σ ≤ s.re := by
      intro s hs
      rw [hσdef]
      exact hs₀ hs
    let C : ℝ := (4 : ℝ) ^ Module.finrank ℂ V
    have hC : 0 ≤ C := by
      dsimp [C]
      positivity
    have hu : Summable (fun v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) =>
        C * (v.asIdeal.absNorm : ℝ) ^ (-σ)) :=
      (numberField_summable_finitePlace_absNorm_rpow (K := K) hσ).mul_left C
    have hbound : ∀ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) in cofinite,
        ∀ s ∈ S,
          ‖numberFieldFinitePlaceArtinEulerReciprocal (K := K) (L := L) ρ v s - 1‖ ≤
            C * (v.asIdeal.absNorm : ℝ) ^ (-σ) := by
      filter_upwards with v
      intro s hs
      have hv : 1 < v.asIdeal.absNorm := NumberField.HeightOneSpectrum.one_lt_absNorm v
      have hvone : (1 : ℝ) ≤ v.asIdeal.absNorm := by
        exact_mod_cast (Nat.succ_le_iff.mpr (Nat.zero_lt_of_lt hv))
      have hre : (1 : ℝ) ≤ s.re := le_of_lt (hS hs)
      calc
        ‖numberFieldFinitePlaceArtinEulerReciprocal (K := K) (L := L) ρ v s - 1‖ ≤
            (4 : ℝ) ^ Module.finrank ℂ V * (v.asIdeal.absNorm : ℝ) ^ (-s.re) := by
          exact numberFieldFinitePlaceLocalEulerPolynomial_eval_inv_sub_one_norm_le_of_re_one_le_real
            v ρ hre
        _ = C * (v.asIdeal.absNorm : ℝ) ^ (-s.re) := by rfl
        _ ≤ C * (v.asIdeal.absNorm : ℝ) ^ (-σ) := by
          apply mul_le_mul_of_nonneg_left _ hC
          apply Real.rpow_le_rpow_of_exponent_le hvone
          exact neg_le_neg (hσle s hs)
    have hcont : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
        ContinuousOn
          (fun s : ℂ => numberFieldFinitePlaceArtinEulerReciprocal (K := K) (L := L) ρ v s - 1) S := by
      intro v
      apply ContinuousOn.sub
      · apply numberFieldFinitePlaceArtinEulerReciprocal_continuousOn ρ v
        intro s hs
        have hs' : (1 : ℝ) < s.re := hS hs
        exact lt_trans zero_lt_one hs'
      · exact continuousOn_const
    have hmain := Summable.hasProdUniformlyOn_one_add hScompact hu hbound hcont
    rw [hfun] at hmain
    refine hmain.congr_right ?_
    intro s hs
    rw [numberFieldFinitePlaceArtinEulerReciprocalProduct]
    apply tprod_congr
    intro v
    ring

/-- Each canonical finite-place Artin reciprocal factor is complex differentiable on a set in
the positive real-part half-plane. -/
theorem numberFieldFinitePlaceArtinEulerReciprocal_differentiableOn
    (ρ : Representation ℂ G V)
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    {S : Set ℂ} (hS : S ⊆ {s | 0 < s.re}) :
    DifferentiableOn ℂ
      (numberFieldFinitePlaceArtinEulerReciprocal (K := K) (L := L) ρ v) S := by
  intro s hs
  have hv : 1 < v.asIdeal.absNorm := NumberField.HeightOneSpectrum.one_lt_absNorm v
  have hv0 : (v.asIdeal.absNorm : ℂ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (lt_trans Nat.zero_lt_one hv)
  have harg : DifferentiableAt ℂ (fun t : ℂ => (v.asIdeal.absNorm : ℂ) ^ (-t)) s := by
    refine DifferentiableAt.const_cpow ?_ (Or.inl hv0)
    exact differentiableAt_id.neg
  have hden : DifferentiableAt ℂ (fun t : ℂ =>
      (numberFieldFinitePlaceLocalEulerPolynomial (K := K) (L := L) v ρ).eval
        ((v.asIdeal.absNorm : ℂ) ^ (-t))) s := by
    fun_prop
  exact (hden.inv
    (numberFieldFinitePlaceLocalEulerPolynomial_eval_ne_zero_of_re_pos v ρ (hS hs))).differentiableWithinAt

/-- The canonical finite-place Artin Euler product is holomorphic on the absolute-convergence
half-plane.  No equality to an `LSeries` or continuation is asserted here. -/
theorem differentiableOn_numberFieldFinitePlaceArtinEulerReciprocalProduct
    (ρ : Representation ℂ G V) :
    DifferentiableOn ℂ
      (numberFieldFinitePlaceArtinEulerReciprocalProduct (K := K) (L := L) ρ)
      artinEulerAbsoluteHalfPlane := by
  have hprod := hasProdLocallyUniformlyOn_numberFieldFinitePlaceArtinEulerReciprocal
    (K := K) (L := L) ρ
  have ht := hasProdLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn.mp hprod
  have hd : ∀ᶠ T : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 K)) in Filter.atTop,
      DifferentiableOn ℂ (fun s : ℂ =>
        ∏ v ∈ T, numberFieldFinitePlaceArtinEulerReciprocal (K := K) (L := L) ρ v s)
        artinEulerAbsoluteHalfPlane := by
    filter_upwards with T
    refine DifferentiableOn.fun_finsetProd fun v _ => ?_
    apply numberFieldFinitePlaceArtinEulerReciprocal_differentiableOn ρ v
    intro s hs
    have hs' : (1 : ℝ) < s.re := hs
    exact lt_trans zero_lt_one hs'
  exact ht.differentiableOn hd isOpen_artinEulerAbsoluteHalfPlane

/-- The independently constructed finite-place Artin Euler product is nonzero in its absolute
convergence half-plane.  This uses summability of the genuine reciprocal-factor differences. -/
theorem numberFieldFinitePlaceArtinEulerReciprocalProduct_ne_zero_of_mem_artinEulerAbsoluteHalfPlane
    (ρ : Representation ℂ G V) {s : ℂ} (hs : s ∈ artinEulerAbsoluteHalfPlane) :
    numberFieldFinitePlaceArtinEulerReciprocalProduct (K := K) (L := L) ρ s ≠ 0 := by
  have hre : (1 : ℝ) < s.re := by
    exact hs
  let C : ℝ := (4 : ℝ) ^ Module.finrank ℂ V
  have hsumMajor : Summable (fun v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) =>
      C * (v.asIdeal.absNorm : ℝ) ^ (-s.re)) :=
    (numberField_summable_finitePlace_absNorm_rpow (K := K) hre).mul_left C
  have hsum : Summable (fun v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) =>
      ‖numberFieldFinitePlaceArtinEulerReciprocal (K := K) (L := L) ρ v s - 1‖) := by
    refine hsumMajor.of_nonneg_of_le (fun v => norm_nonneg _) ?_
    intro v
    change ‖((numberFieldFinitePlaceLocalEulerPolynomial (K := K) (L := L) v ρ).eval
      ((v.asIdeal.absNorm : ℂ) ^ (-s)))⁻¹ - 1‖ ≤
        C * (v.asIdeal.absNorm : ℝ) ^ (-s.re)
    exact numberFieldFinitePlaceLocalEulerPolynomial_eval_inv_sub_one_norm_le_of_re_one_le_real
      v ρ (le_of_lt hre)
  have hfactor : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
      1 + (numberFieldFinitePlaceArtinEulerReciprocal (K := K) (L := L) ρ v s - 1) ≠ 0 := by
    intro v
    have hden : (numberFieldFinitePlaceLocalEulerPolynomial (K := K) (L := L) v ρ).eval
        ((v.asIdeal.absNorm : ℂ) ^ (-s)) ≠ 0 :=
      numberFieldFinitePlaceLocalEulerPolynomial_eval_ne_zero_of_re_pos v ρ
        (lt_trans zero_lt_one hre)
    have hrecip : numberFieldFinitePlaceArtinEulerReciprocal (K := K) (L := L) ρ v s ≠ 0 := by
      change ((numberFieldFinitePlaceLocalEulerPolynomial (K := K) (L := L) v ρ).eval
        ((v.asIdeal.absNorm : ℂ) ^ (-s)))⁻¹ ≠ 0
      exact inv_ne_zero hden
    have heq : 1 + (numberFieldFinitePlaceArtinEulerReciprocal (K := K) (L := L) ρ v s - 1) =
        numberFieldFinitePlaceArtinEulerReciprocal (K := K) (L := L) ρ v s := by
      ring
    rw [heq]
    exact hrecip
  have hprod := tprod_one_add_ne_zero_of_summable (f := fun v :
      IsDedekindDomain.HeightOneSpectrum (𝓞 K) =>
        numberFieldFinitePlaceArtinEulerReciprocal (K := K) (L := L) ρ v s - 1) hfactor hsum
  have hrewrite : (fun v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) =>
      1 + (numberFieldFinitePlaceArtinEulerReciprocal (K := K) (L := L) ρ v s - 1)) =
      fun v => numberFieldFinitePlaceArtinEulerReciprocal (K := K) (L := L) ρ v s := by
    funext v
    ring
  rw [hrewrite] at hprod
  rw [numberFieldFinitePlaceArtinEulerReciprocalProduct]
  exact hprod

end GaloisForLFunctions
