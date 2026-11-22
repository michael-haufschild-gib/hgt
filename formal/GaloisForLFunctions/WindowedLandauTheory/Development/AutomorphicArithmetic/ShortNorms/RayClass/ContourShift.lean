import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.ShortNorms.RayClass.LogDerivativePole
import GaloisForLFunctions.HTGeometry.RectangleResidueTheorem
import GaloisForLFunctions.HTGeometry.SimplePoleResidueValue

/-! Shift a finite Perron integral past simple real poles and bound the other three edges. -/

open Complex MeasureTheory Filter Topology
open scoped Classical

namespace GlobalTheory.Hk.PsiExc

open GaloisForLFunctions.HTGeometry

theorem shift (ψ : ℂ → ℂ) (S : Finset ℂ) (k : ℂ → ℂ) (u σ c T M : ℝ) (hu : 1 < u)
    (hσ : 1 / 2 ≤ σ) (hσc : σ < c) (hc3 : c ≤ 3) (huc : u ^ c ≤ 3 * u) (hT : 0 < T) (hM : 0 ≤ M)
    (hS : ∀ p ∈ S, σ < p.re ∧ p.re < c ∧ p.im = 0)
    (hd : ∀ s : ℂ, σ ≤ s.re → s.re ≤ c → |s.im| ≤ T → s ∉ S → AnalyticAt ℂ ψ s)
    (hp : ∀ p ∈ S, ∃ g : ℂ → ℂ, AnalyticAt ℂ g p ∧ ∀ᶠ s in 𝓝[≠] p, ψ s = k p / (s - p) + g s)
    (hb : ∀ s : ℂ, σ ≤ s.re → s.re ≤ c → |s.im| ≤ T → (s.re = σ ∨ |s.im| = T) → ‖ψ s‖ ≤ M) :
    ‖(1 / (2 * Real.pi) : ℂ) * (∫ t in (-T)..T,
        -(ψ ((c : ℂ) + t * I)) * (u : ℂ) ^ ((c : ℂ) + t * I) / ((c : ℂ) + t * I))
      + ∑ p ∈ S, k p * ((u : ℂ) ^ p / p)‖ ≤ 18 * (M * u / T) + 4 * (T * M * u ^ σ) := by
  have hu0 : 0 < u := by linarith
  let f (s : ℂ) := -(ψ s) * (u : ℂ) ^ s / s
  let z₀ : ℂ := ⟨σ, -T⟩
  let z₁ : ℂ := ⟨c, T⟩
  have hT' : -T ≤ T := by linarith
  have hins (p : ℂ) (hp' : p ∈ S) : Rectangle z₀ z₁ ∈ 𝓝 p := by
    rw [rectangle_mem_nhds_iff, mem_reProdIm, Set.uIoo_of_le hσc.le, Set.uIoo_of_le hT']
    obtain ⟨hlo, hhi, him⟩ := hS p hp'
    exact ⟨⟨hlo, hhi⟩, ⟨by rw [him]; linarith, by simpa [him] using hT⟩⟩
  have han (s : ℂ) (hs : s ∈ Rectangle z₀ z₁) (hsS : s ∉ S) : AnalyticAt ℂ f s := by
    rw [Rectangle, mem_reProdIm, Set.uIcc_of_le hσc.le, Set.uIcc_of_le hT'] at hs
    have hs0 : s ≠ 0 := by
      rintro rfl
      have hlo := hs.1.1
      change σ ≤ 0 at hlo
      linarith
    have hpow := GlobalTheory.ExplicitRect.analyticAt_cpow hu0 s
    exact (((hd s hs.1.1 hs.1.2 (abs_le.mpr hs.2) hsS).neg).mul hpow).div analyticAt_id hs0
  have hmodel (p : ℂ) (hp' : p ∈ S) :
      MeromorphicAt f p ∧ laurentCoeff f p (-1) = -(k p * ((u : ℂ) ^ p / p)) := by
    obtain ⟨g, hg, he⟩ := hp p hp'
    have hp0 : p ≠ 0 := by
      rintro rfl
      have h := (hS _ hp').1
      change σ < 0 at h
      linarith
    let W (s : ℂ) := (u : ℂ) ^ s / s
    let A (s : ℂ) := -(k p * W s)
    let R (s : ℂ) := -(g s * W s)
    have hW : AnalyticAt ℂ W p := (GlobalTheory.ExplicitRect.analyticAt_cpow hu0 p).div analyticAt_id hp0
    have hA : AnalyticAt ℂ A p := (analyticAt_const.mul hW).neg
    have hR : AnalyticAt ℂ R p := (hg.mul hW).neg
    have hmero : MeromorphicAt (fun s => A s / (s - p)) p :=
      hA.meromorphicAt.div ((analyticAt_id.sub analyticAt_const).meromorphicAt)
    have hE : f =ᶠ[𝓝[≠] p] (fun s => A s / (s - p)) + R := by
      filter_upwards [he] with s hs
      change f s = A s / (s - p) + R s
      dsimp [f, A, R, W]
      rw [hs]
      simp only [div_eq_mul_inv]
      ring
    refine ⟨(hmero.add hR.meromorphicAt).congr hE.symm, ?_⟩
    calc laurentCoeff f p (-1) = laurentCoeff (fun s => A s / (s - p) + R s) p (-1) :=
        (laurentCoeff_congr (hmero.add hR.meromorphicAt) hE.symm (-1)).symm
      _ = laurentCoeff (fun s => A s / (s - p)) p (-1) + laurentCoeff R p (-1) :=
        laurentCoeff_add hmero hR.meromorphicAt (-1)
      _ = _ := by
        rw [laurentCoeff_analytic_div_sub hA, laurentCoeff_eq_zero_of_analyticAt hR (by norm_num),
          add_zero]
  have hRes := rectangleIntegral'_eq_sum_laurentCoeff (f := f) (z := z₀) (w := z₁)
    hσc.le hT' hins (fun p hp' => (hmodel p hp').1) han
  rw [Finset.sum_congr rfl (fun p hp' => (hmodel p hp').2)] at hRes
  have hscale : (2 * (Real.pi : ℂ) * I) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) I_ne_zero
  have hnorm : (2 * (Real.pi : ℂ) * I) * RectangleIntegral' f z₀ z₁ = RectangleIntegral f z₀ z₁ := by
    change (2 * (Real.pi : ℂ) * I) *
      ((1 / (2 * (Real.pi : ℂ) * I)) • RectangleIntegral f z₀ z₁) = _
    rw [smul_eq_mul, ← mul_assoc, mul_one_div_cancel hscale, one_mul]
  have key := congrArg (fun v : ℂ => (2 * (Real.pi : ℂ) * I) * v) hRes
  change (2 * (Real.pi : ℂ) * I) * RectangleIntegral' f z₀ z₁ = _ at key
  rw [hnorm] at key
  simp only [RectangleIntegral, HIntegral, VIntegral, smul_eq_mul, z₀, z₁, f] at key
  simp only [Finset.sum_neg_distrib] at key
  have hor : ∀ τ : ℝ, |τ| = T → ‖∫ x : ℝ in σ..c,
      (-(ψ ((x : ℂ) + τ * I)) * (u : ℂ) ^ ((x : ℂ) + τ * I) / ((x : ℂ) + τ * I))‖
      ≤ 9 * (M * u / T) := by
    intro τ hτ
    have key := intervalIntegral.norm_integral_le_of_norm_le_const (a := σ) (b := c)
      (C := 3 * (M * u / T))
      (f := fun x : ℝ => (-(ψ ((x : ℂ) + τ * I)) * (u : ℂ) ^ ((x : ℂ) + τ * I) / ((x : ℂ) + τ * I)))
      (by
        intro x hx
        rw [Set.uIoc_of_le hσc.le] at hx
        have h1 := hb ((x : ℂ) + τ * I) (by simpa using hx.1.le) (by simpa using hx.2)
          (by simpa using hτ.le) (Or.inr (by simpa using hτ))
        have h2 : ‖(u : ℂ) ^ ((x : ℂ) + τ * I)‖ ≤ 3 * u := by
          rw [Complex.norm_cpow_eq_rpow_re_of_pos hu0]
          simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
            add_zero]
          exact (Real.rpow_le_rpow_of_exponent_le hu.le hx.2).trans huc
        have h3 : T ≤ ‖(x : ℂ) + τ * I‖ := by
          rw [← hτ]
          have := Complex.abs_im_le_norm ((x : ℂ) + τ * I)
          simpa using this
        rw [norm_div, norm_mul, norm_neg]
        calc _ ≤ M * (3 * u) / T := by gcongr
          _ = _ := by ring)
    refine key.trans ?_
    have : |c - σ| ≤ 3 := by rw [abs_le]; constructor <;> linarith
    have h4 : 0 ≤ M * u / T := by positivity
    nlinarith
  have left : ‖∫ t : ℝ in (-T)..T,
      (-(ψ ((σ : ℂ) + t * I)) * (u : ℂ) ^ ((σ : ℂ) + t * I) / ((σ : ℂ) + t * I))‖
      ≤ 4 * (T * M * u ^ σ) := by
    have key := intervalIntegral.norm_integral_le_of_norm_le_const (a := -T) (b := T)
      (C := 2 * (M * u ^ σ))
      (f := fun t : ℝ => (-(ψ ((σ : ℂ) + t * I)) * (u : ℂ) ^ ((σ : ℂ) + t * I) / ((σ : ℂ) + t * I)))
      (by
        intro t ht
        rw [Set.uIoc_of_le (by linarith)] at ht
        have h1 := hb ((σ : ℂ) + t * I) (by simp) (by simpa using hσc.le)
          (by simpa using abs_le.2 ⟨ht.1.le, ht.2⟩) (Or.inl (by simp))
        have h2 : ‖(u : ℂ) ^ ((σ : ℂ) + t * I)‖ = u ^ σ := by
          rw [Complex.norm_cpow_eq_rpow_re_of_pos hu0]
          simp
        have h3 : 1 / 2 ≤ ‖(σ : ℂ) + t * I‖ := by
          have := Complex.re_le_norm ((σ : ℂ) + t * I)
          exact hσ.trans (by simpa using this)
        rw [norm_div, norm_mul, norm_neg, h2]
        calc _ ≤ M * u ^ σ / (1 / 2) := by gcongr
          _ = _ := by ring)
    refine key.trans (le_of_eq ?_)
    rw [abs_of_pos (by linarith)]
    ring
  have gen : ∀ a b v l Z : ℂ, a - b + I * v - I * l = 2 * Real.pi * I * (-Z) →
      ‖(1 / (2 * Real.pi) : ℂ) * v + Z‖ ≤ ‖a‖ + ‖b‖ + ‖l‖ := by
    intro a b v l Z e
    have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have e2 : (1 / (2 * Real.pi) : ℂ) * v + Z
        = (1 / (2 * Real.pi) : ℂ) * (I * a - I * b + l) := by
      field_simp
      linear_combination (-I) * e + (v - l + 2 * Real.pi * Z) * I_mul_I
    have n1 : ‖(1 / (2 * Real.pi) : ℂ)‖ ≤ 1 := by
      rw [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos, norm_one,
        Complex.norm_ofNat, div_le_one (by positivity)]
      linarith [Real.pi_gt_three]
    have n2 : ‖I * a - I * b + l‖ ≤ ‖a‖ + ‖b‖ + ‖l‖ := by
      refine (norm_add_le _ _).trans ?_
      have := norm_sub_le (I * a) (I * b)
      simp only [norm_mul, norm_I, one_mul] at this
      linarith
    rw [e2, norm_mul]
    have := mul_le_mul n1 n2 (norm_nonneg _) zero_le_one
    linarith
  refine (gen _ _ _ _ _ key).trans ?_
  have a1 := hor (-T) (by rw [abs_neg, abs_of_pos hT])
  have a2 := hor T (abs_of_pos hT)
  linarith

end GlobalTheory.Hk.PsiExc
