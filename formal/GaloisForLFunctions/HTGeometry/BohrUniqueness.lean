import GaloisForLFunctions.HTGeometry.BohrUniqueErgodicity

/-!
# The uniqueness theorem for almost-periodic functions

A nonnegative almost-periodic function with vanishing mean is identically zero: unique ergodicity
turns its mean into a Haar integral over the hull, where a nonnegative continuous integrand of zero
integral vanishes almost everywhere, hence everywhere since Haar measure has full support.

Consequently an almost-periodic function all of whose Bohr coefficients vanish is zero: approximate
it by a trigonometric polynomial, and the mean of `f · conj f` is within `‖f‖ε` of a finite
combination of Bohr coefficients, hence zero.
-/

open MeasureTheory TopologicalSpace

open scoped BoundedContinuousFunction

namespace GaloisForLFunctions

open HTGeometry

noncomputable section

/-- **A nonnegative almost-periodic function with vanishing mean is zero.** -/
theorem eq_zero_of_bohrMean_eq_zero_of_nonneg {g : ℝ → ℂ} (hcont : Continuous g)
    (hap : HTGeometry.IsBohrAlmostPeriodic g) (hre : ∀ t, 0 ≤ (g t).re)
    (him : ∀ t, (g t).im = 0) (hmean : bohrMean g = 0) : ∀ t, g t = 0 := by
  have htb : HasTotallyBoundedOrbit g := hasTotallyBoundedOrbit_of_isBohrAlmostPeriodic hcont hap
  have huc : UniformContinuous g := uniformContinuous_of_isBohrAlmostPeriodic hcont hap
  set G : ℝ →ᵇ ℂ := toBC g hcont htb with hG
  have hGapp : ∀ t : ℝ, G t = g t := fun t => rfl
  have hucG : UniformContinuous (fun x => G x) := huc
  have htbG : HasTotallyBoundedOrbit (fun x => G x) := htb
  haveI : CompactSpace (BohrHull G) := compactSpace_bohrHull htbG
  borelize (BohrHull G)
  set F : C(BohrHull G, ℂ) := ⟨bohrEval G, continuous_bohrEval G⟩ with hF
  -- the mean is the Haar integral
  have hint : ∫ x, F x ∂(CompactAbelian.haarProb (BohrHull G)) = 0 := by
    rw [← bohrMean_comp_bohrIota_eq_integral hucG htbG F]
    have : (fun t : ℝ => F (bohrIota G t)) = g := by
      funext t
      show bohrEval G (bohrIota G t) = g t
      rw [bohrEval_bohrIota]
      rfl
    rw [this, hmean]
  -- the extension is real and nonnegative
  have hreF : ∀ x : BohrHull G, 0 ≤ (F x).re := by
    have hcl : IsClosed {x : BohrHull G | 0 ≤ (bohrEval G x).re} :=
      isClosed_le continuous_const (Complex.continuous_re.comp (continuous_bohrEval G))
    have hsub : Set.range (bohrIota G) ⊆ {x : BohrHull G | 0 ≤ (bohrEval G x).re} := by
      rintro x ⟨t, rfl⟩
      show 0 ≤ (bohrEval G (bohrIota G t)).re
      rw [bohrEval_bohrIota]
      exact hre t
    have hall := hcl.closure_subset_iff.mpr hsub
    rw [(denseRange_bohrIota G).closure_range] at hall
    exact fun x => hall (Set.mem_univ x)
  have himF : ∀ x : BohrHull G, (F x).im = 0 := by
    have hcl : IsClosed {x : BohrHull G | (bohrEval G x).im = 0} :=
      isClosed_eq (Complex.continuous_im.comp (continuous_bohrEval G)) continuous_const
    have hsub : Set.range (bohrIota G) ⊆ {x : BohrHull G | (bohrEval G x).im = 0} := by
      rintro x ⟨t, rfl⟩
      show (bohrEval G (bohrIota G t)).im = 0
      rw [bohrEval_bohrIota]
      exact him t
    have hall := hcl.closure_subset_iff.mpr hsub
    rw [(denseRange_bohrIota G).closure_range] at hall
    exact fun x => hall (Set.mem_univ x)
  -- a nonnegative continuous integrand of zero integral vanishes
  have hFint : Integrable (fun x : BohrHull G => F x) (CompactAbelian.haarProb (BohrHull G)) :=
    F.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hreint : ∫ x, (F x).re ∂(CompactAbelian.haarProb (BohrHull G)) = 0 := by
    have h := integral_re (𝕜 := ℂ) hFint
    rw [hint] at h
    simpa using h
  have hzero : (fun x : BohrHull G => (F x).re) =ᵐ[CompactAbelian.haarProb (BohrHull G)] 0 :=
    (integral_eq_zero_iff_of_nonneg hreF hFint.re).mp hreint
  have hreF0 : ∀ x : BohrHull G, (F x).re = 0 := by
    have hcont1 : Continuous fun x : BohrHull G => (F x).re :=
      Complex.continuous_re.comp F.continuous
    have := (hcont1.ae_eq_iff_eq (CompactAbelian.haarProb (BohrHull G)) continuous_const).mp hzero
    exact fun x => congrFun this x
  intro t
  have h1 : g t = F (bohrIota G t) := by
    show g t = bohrEval G (bohrIota G t)
    rw [bohrEval_bohrIota]
    rfl
  rw [h1]
  apply Complex.ext
  · rw [hreF0]
    simp
  · rw [himF]
    simp

/-- **The uniqueness theorem.**  An almost-periodic function all of whose Bohr coefficients vanish
is identically zero. -/
theorem eq_zero_of_bohrCoefficient_eq_zero {f : ℝ →ᵇ ℂ} (hf : UniformContinuous (fun x => f x))
    (htb : HasTotallyBoundedOrbit (fun x => f x))
    (hcoeff : ∀ lam : ℝ, bohrCoefficient (fun x => f x) lam = 0) : ∀ t : ℝ, f t = 0 := by
  have hap : HTGeometry.IsBohrAlmostPeriodic (fun x => f x) :=
    isBohrAlmostPeriodic_of_hasTotallyBoundedOrbit htb
  have hcont : Continuous (fun x => f x) := f.continuous
  set g : ℝ → ℂ := fun t => f t * (starRingEnd ℂ) (f t) with hg
  have hgc : Continuous g := hcont.mul (Complex.continuous_conj.comp hcont)
  have hga : HTGeometry.IsBohrAlmostPeriodic g :=
    isBohrAlmostPeriodic_mul hcont hap (Complex.continuous_conj.comp hcont)
      (isBohrAlmostPeriodic_conj hap)
  have hmean : bohrMean g = 0 := by
    by_contra hne
    set d : ℝ := ‖bohrMean g‖ with hd
    have hdpos : 0 < d := norm_pos_iff.mpr hne
    have hfnn : (0 : ℝ) ≤ ‖f‖ := norm_nonneg f
    obtain ⟨n, c, lam, hclose⟩ :=
      exists_trig_approx hf htb (ε := d / (2 * (‖f‖ + 1))) (by positivity)
    -- the mean against the approximating polynomial is a combination of Bohr coefficients
    have hterm : ∀ j : Fin n, bohrMean (fun t => (starRingEnd ℂ) (c j) *
        ((fun x => f x) t * bohrChar (lam j) t)) = 0 := by
      intro j
      have h0 : bohrMean (fun t : ℝ => (f : ℝ → ℂ) t * bohrChar (lam j) t) = 0 := hcoeff (lam j)
      rw [bohrMean_const_mul (f := fun t : ℝ => (f : ℝ → ℂ) t * bohrChar (lam j) t) _
        (hcont.mul (continuous_bohrChar _))
        (isBohrAlmostPeriodic_mul_bohrChar hcont hap _), h0, mul_zero]
    have hexpb : ∀ μ t : ℝ, Complex.exp ((μ * t : ℝ) * Complex.I) = bohrExp μ t := by
      intro μ t
      unfold bohrExp bohrChar
      congr 1
      push_cast
      ring
    have hexpfun : ∀ μ : ℝ, (fun t : ℝ => Complex.exp ((μ * t : ℝ) * Complex.I)) = bohrExp μ :=
      fun μ => funext (hexpb μ)
    have hcontE : ∀ μ : ℝ, Continuous fun t : ℝ => Complex.exp ((μ * t : ℝ) * Complex.I) := by
      intro μ
      rw [hexpfun μ]
      exact continuous_bohrExp μ
    have hapE : ∀ μ : ℝ, HTGeometry.IsBohrAlmostPeriodic
        fun t : ℝ => Complex.exp ((μ * t : ℝ) * Complex.I) := by
      intro μ
      rw [hexpfun μ]
      exact isBohrAlmostPeriodic_bohrExp μ
    have hP : bohrMean (fun t => f t *
        (starRingEnd ℂ) (∑ j, c j * Complex.exp ((lam j * t : ℝ) * Complex.I))) = 0 := by
      have hsplit : (fun t : ℝ => f t *
          (starRingEnd ℂ) (∑ j, c j * Complex.exp ((lam j * t : ℝ) * Complex.I)))
          = fun t : ℝ => ∑ j, (starRingEnd ℂ) (c j) * ((fun x => f x) t * bohrChar (lam j) t) := by
        funext t
        rw [map_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [map_mul, hexpb (lam j) t, conj_bohrExp]
        ring
      rw [hsplit, bohrMean_sum (F := fun (j : Fin n) (t : ℝ) => (starRingEnd ℂ) (c j) *
          ((f : ℝ → ℂ) t * bohrChar (lam j) t)) Finset.univ
        (fun j _ => continuous_const.mul (hcont.mul (continuous_bohrChar _)))
        (fun j _ => isBohrAlmostPeriodic_const_mul _
          (isBohrAlmostPeriodic_mul_bohrChar hcont hap _))]
      exact Finset.sum_eq_zero fun j _ => hterm j
    -- the two means differ by at most `‖f‖ ε`
    have hdiff : bohrMean g - bohrMean (fun t => f t *
        (starRingEnd ℂ) (∑ j, c j * Complex.exp ((lam j * t : ℝ) * Complex.I)))
        = bohrMean (fun t => f t * (starRingEnd ℂ)
            (f t - ∑ j, c j * Complex.exp ((lam j * t : ℝ) * Complex.I))) := by
      have hPc : Continuous fun t : ℝ =>
          ∑ j, c j * Complex.exp ((lam j * t : ℝ) * Complex.I) := by
        refine continuous_finsetSum _ fun j _ => continuous_const.mul ?_
        exact hcontE (lam j)
      have hPa : HTGeometry.IsBohrAlmostPeriodic fun t : ℝ =>
          ∑ j, c j * Complex.exp ((lam j * t : ℝ) * Complex.I) := by
        refine isBohrAlmostPeriodic_sum _ (fun j _ => continuous_const.mul (hcontE _))
          (fun j _ => isBohrAlmostPeriodic_const_mul _ (hapE _))
      have h1 : Continuous fun t : ℝ => f t * (starRingEnd ℂ)
          (∑ j, c j * Complex.exp ((lam j * t : ℝ) * Complex.I)) :=
        hcont.mul (Complex.continuous_conj.comp hPc)
      have h2 : HTGeometry.IsBohrAlmostPeriodic fun t : ℝ => f t * (starRingEnd ℂ)
          (∑ j, c j * Complex.exp ((lam j * t : ℝ) * Complex.I)) :=
        isBohrAlmostPeriodic_mul hcont hap (Complex.continuous_conj.comp hPc)
          (isBohrAlmostPeriodic_conj hPa)
      rw [← bohrMean_sub (f := g) (g := fun t : ℝ => f t * (starRingEnd ℂ)
        (∑ j, c j * Complex.exp ((lam j * t : ℝ) * Complex.I))) hgc hga h1 h2]
      congr 1
      funext t
      rw [hg]
      simp only [map_sub]
      ring
    have hbound : ‖bohrMean g‖ ≤ ‖f‖ * (d / (2 * (‖f‖ + 1))) := by
      rw [show bohrMean g = bohrMean g - bohrMean (fun t => f t *
        (starRingEnd ℂ) (∑ j, c j * Complex.exp ((lam j * t : ℝ) * Complex.I))) by rw [hP, sub_zero],
        hdiff]
      refine norm_bohrMean_le ?_ ?_ fun t => ?_
      · refine hcont.mul (Complex.continuous_conj.comp (hcont.sub ?_))
        exact continuous_finsetSum _ fun j _ => continuous_const.mul (hcontE (lam j))
      · refine isBohrAlmostPeriodic_mul hcont hap ?_ ?_
        · refine Complex.continuous_conj.comp (hcont.sub ?_)
          exact continuous_finsetSum _ fun j _ => continuous_const.mul (hcontE (lam j))
        · refine isBohrAlmostPeriodic_conj (isBohrAlmostPeriodic_sub hcont hap ?_ ?_)
          · exact continuous_finsetSum _ fun j _ => continuous_const.mul (hcontE _)
          · exact isBohrAlmostPeriodic_sum _
              (fun j _ => continuous_const.mul (hcontE _))
              (fun j _ => isBohrAlmostPeriodic_const_mul _ (hapE _))
      · rw [norm_mul, RCLike.norm_conj]
        exact mul_le_mul (f.norm_coe_le_norm t) (hclose t) (norm_nonneg _) hfnn
    have hlt : ‖f‖ * (d / (2 * (‖f‖ + 1))) < d := by
      rw [mul_div_assoc']
      rw [div_lt_iff₀ (by positivity)]
      nlinarith [hdpos, hfnn]
    rw [← hd] at hbound
    linarith
  -- the modulus squared is nonnegative and real
  have hzero := eq_zero_of_bohrMean_eq_zero_of_nonneg hgc hga
    (fun t => by
      show 0 ≤ ((f : ℝ → ℂ) t * (starRingEnd ℂ) ((f : ℝ → ℂ) t)).re
      rw [Complex.mul_conj]
      simpa using Complex.normSq_nonneg ((f : ℝ → ℂ) t))
    (fun t => by
      show ((f : ℝ → ℂ) t * (starRingEnd ℂ) ((f : ℝ → ℂ) t)).im = 0
      rw [Complex.mul_conj]
      simp) hmean
  intro t
  have := hzero t
  rw [hg] at this
  simp only [Complex.mul_conj] at this
  have hnorm : (Complex.normSq (f t) : ℂ) = 0 := this
  have : Complex.normSq (f t) = 0 := by exact_mod_cast hnorm
  exact Complex.normSq_eq_zero.mp this


/-- **An almost-periodic function is determined by its Bohr coefficients.** -/
theorem eq_of_bohrCoefficient_eq {f g : ℝ →ᵇ ℂ}
    (htbf : HasTotallyBoundedOrbit (fun x => f x))
    (htbg : HasTotallyBoundedOrbit (fun x => g x))
    (hcoeff : ∀ lam : ℝ, bohrCoefficient (fun x => f x) lam
      = bohrCoefficient (fun x => g x) lam) : ∀ t : ℝ, f t = g t := by
  have hapf : HTGeometry.IsBohrAlmostPeriodic (fun x => f x) :=
    isBohrAlmostPeriodic_of_hasTotallyBoundedOrbit htbf
  have hapg : HTGeometry.IsBohrAlmostPeriodic (fun x => g x) :=
    isBohrAlmostPeriodic_of_hasTotallyBoundedOrbit htbg
  set h : ℝ →ᵇ ℂ := f - g with hh
  have hhapp : ∀ t : ℝ, h t = f t - g t := fun t => rfl
  have hhcont : Continuous (fun x => h x) := h.continuous
  have hhap : HTGeometry.IsBohrAlmostPeriodic (fun x => h x) := by
    have : (fun x => h x) = fun t : ℝ => (f : ℝ → ℂ) t - (g : ℝ → ℂ) t := funext hhapp
    rw [this]
    exact isBohrAlmostPeriodic_sub f.continuous hapf g.continuous hapg
  have hhu : UniformContinuous (fun x => h x) :=
    uniformContinuous_of_isBohrAlmostPeriodic hhcont hhap
  have hhtb : HasTotallyBoundedOrbit (fun x => h x) :=
    hasTotallyBoundedOrbit_of_isBohrAlmostPeriodic hhcont hhap
  have hzero : ∀ lam : ℝ, bohrCoefficient (fun x => h x) lam = 0 := by
    intro lam
    have hsplit : (fun t : ℝ => (h : ℝ → ℂ) t * bohrChar lam t)
        = fun t : ℝ => (f : ℝ → ℂ) t * bohrChar lam t - (g : ℝ → ℂ) t * bohrChar lam t := by
      funext t
      rw [hhapp t]
      ring
    have hc : bohrCoefficient (fun x => h x) lam
        = bohrCoefficient (fun x => f x) lam - bohrCoefficient (fun x => g x) lam := by
      show bohrMean (fun t : ℝ => (h : ℝ → ℂ) t * bohrChar lam t) = _
      rw [hsplit, bohrMean_sub (f := fun t : ℝ => (f : ℝ → ℂ) t * bohrChar lam t)
        (g := fun t : ℝ => (g : ℝ → ℂ) t * bohrChar lam t)
        (f.continuous.mul (continuous_bohrChar lam))
        (isBohrAlmostPeriodic_mul_bohrChar f.continuous hapf lam)
        (g.continuous.mul (continuous_bohrChar lam))
        (isBohrAlmostPeriodic_mul_bohrChar g.continuous hapg lam)]
      rfl
    rw [hc, hcoeff lam, sub_self]
  intro t
  have := eq_zero_of_bohrCoefficient_eq_zero hhu hhtb hzero t
  rw [hhapp t] at this
  linear_combination this

/-- **A nonzero almost-periodic function has a nonzero Bohr coefficient.** -/
theorem exists_bohrCoefficient_ne_zero {f : ℝ →ᵇ ℂ} (hf : UniformContinuous (fun x => f x))
    (htb : HasTotallyBoundedOrbit (fun x => f x)) {t₀ : ℝ} (hne : f t₀ ≠ 0) :
    ∃ lam : ℝ, bohrCoefficient (fun x => f x) lam ≠ 0 := by
  by_contra hall
  push Not at hall
  exact hne (eq_zero_of_bohrCoefficient_eq_zero hf htb hall t₀)


end

end GaloisForLFunctions
