import GaloisForLFunctions.HTGeometry.PolynomialTaylorProuhetPhaseLock
import GaloisForLFunctions.HTGeometry.TorsionLanguageFaceExactification
import GaloisForLFunctions.HTGeometry.GeometricPatternWeightLimit

/-!
# Polynomial tail defects and torsion-language exactification

On a finite Prouhet face, equality of every moment below `ceil beta` makes each
translated power-valuation difference convergent.  For nonintegral `beta` the limit is zero;
for integral `beta` it is the first remaining exact polynomial moment.  Taking the finite
minimum therefore also commutes with the tail limit.

This supplies the missing compiler between the polynomial ADE phase lock and torsion-language
Fourier exactification: normalize the integer polynomial weights by their common top degree,
absorb the convergent valuation defects into the limiting weights, and rule out the face because
one top coefficient is nonzero.
-/

namespace GaloisForLFunctions

open Filter Finset PowerSeries MvPolynomial Polynomial Topology

noncomputable section

/-- Limit of the translated power-valuation difference of two patterns whose moments below
`ceil beta` agree.  At an integral exponent the remaining top moment is exact; otherwise the
difference tends to zero. -/
def polynomialPatternPowerDifferenceLimit {M D : ℕ} (β : ℝ)
    (p₀ p : Fin M → Fin (D + 1)) : ℝ :=
  if β = (Nat.ceil β : ℝ) then
    (polynomialPatternMoment p (Nat.ceil β) : ℝ) -
      polynomialPatternMoment p₀ (Nat.ceil β)
  else 0

/-- Equal moments below `ceil beta` force a genuine finite limit of the translated real-power
defect.  This includes the exact polynomial case `beta = 2` used by a finite Gaussian face. -/
theorem tendsto_polynomialPatternPowerValuation_sub_of_moments
    {β : ℝ} {M D : ℕ}
    (p₀ p : Fin M → Fin (D + 1))
    (hcount₀ : (∑ r, (p₀ r : ℕ)) = D)
    (hcount : (∑ r, (p r : ℕ)) = D)
    (hmom : ∀ j < Nat.ceil β,
      polynomialPatternMoment p₀ j = polynomialPatternMoment p j) :
    Tendsto (fun x : ℝ =>
      polynomialPatternPowerValuation β p x -
        polynomialPatternPowerValuation β p₀ x) atTop
      (𝓝 (polynomialPatternPowerDifferenceLimit β p₀ p)) := by
  let d := polynomialRealCoeffFinsupp (atomPatternDifferencePolynomial p₀ p)
  by_cases hβnat : β = (Nat.ceil β : ℝ)
  · have hcancel : ∀ j < Nat.ceil β, stretchedMoment d j = 0 := by
      intro j hj
      dsimp [d]
      rw [stretchedMoment_atomPatternDifference p₀ p hcount₀ hcount,
        hmom j hj]
      simp
    apply tendsto_const_nhds.congr'
    apply Eventually.of_forall
    intro x
    change polynomialPatternPowerDifferenceLimit β p₀ p =
      polynomialPatternPowerValuation β p x -
        polynomialPatternPowerValuation β p₀ x
    rw [polynomialPatternPowerDifferenceLimit, if_pos hβnat]
    symm
    rw [polynomialPatternPowerValuation_sub β x p₀ p hcount₀ hcount,
      hβnat, polynomialPowerFiniteDifference_natCast_eq_stretchedMoment d
        (Nat.ceil β) hcancel]
    dsimp [d]
    rw [stretchedMoment_atomPatternDifference p₀ p hcount₀ hcount]
    simp
  · have hlimit : polynomialPatternPowerDifferenceLimit β p₀ p = 0 := by
      simp [polynomialPatternPowerDifferenceLimit, hβnat]
    rw [hlimit]
    by_cases hp : p = p₀
    · subst p
      simp
    · obtain ⟨μ, _hμD, hcancel, hmoment⟩ :=
        exists_first_atomPatternDifference_moment p₀ p (Ne.symm hp) hcount₀ hcount
      have hceilμ : Nat.ceil β ≤ μ := by
        by_contra hnot
        have hμceil : μ < Nat.ceil β := by omega
        apply hmoment
        rw [stretchedMoment_atomPatternDifference p₀ p hcount₀ hcount,
          hmom μ hμceil]
        simp
      have hβceil : β < (Nat.ceil β : ℝ) := by
        exact lt_of_le_of_ne (Nat.le_ceil β) hβnat
      have hβμ : β < (μ : ℝ) :=
        hβceil.trans_le (Nat.cast_le.mpr hceilμ)
      have hpoch : (descPochhammer ℝ μ).eval β ≠ 0 := by
        rw [descPochhammer_eval_eq_prod_range]
        apply Finset.prod_ne_zero_iff.mpr
        intro j hj hzero
        have hβj : β = (j : ℝ) := sub_eq_zero.mp hzero
        apply hβnat
        rw [hβj, Nat.ceil_natCast]
      have hequiv := polynomialPowerFiniteDifference_isEquivalent d μ
        hcancel hmoment hpoch
      have hlead : Tendsto
          (fun x : ℝ => polynomialPowerDifferenceCoefficient β d μ *
            x ^ (β - μ)) atTop (𝓝 0) := by
        have hneg : 0 < (μ : ℝ) - β := sub_pos.mpr hβμ
        have hpw : Tendsto (fun x : ℝ => x ^ (-((μ : ℝ) - β)))
            atTop (𝓝 0) := tendsto_rpow_neg_atTop hneg
        simpa [neg_sub] using
          hpw.const_mul (polynomialPowerDifferenceCoefficient β d μ)
      have hdiff : Tendsto (polynomialPowerFiniteDifference β d) atTop (𝓝 0) :=
        hequiv.symm.tendsto_nhds hlead
      apply hdiff.congr'
      apply Eventually.of_forall
      intro x
      exact (polynomialPatternPowerValuation_sub β x p₀ p hcount₀ hcount).symm

/-- A fixed reference pattern used to express a finite cluster minimum by relative defects. -/
def polynomialPatternClusterReference {M D : ℕ}
    (C : Finset (Fin M → Fin (D + 1))) (hC : C.Nonempty) :
    Fin M → Fin (D + 1) :=
  Classical.choose hC

theorem polynomialPatternClusterReference_mem {M D : ℕ}
    (C : Finset (Fin M → Fin (D + 1))) (hC : C.Nonempty) :
    polynomialPatternClusterReference C hC ∈ C :=
  Classical.choose_spec hC

/-- Relative limiting defect from the selected reference pattern. -/
def polynomialPatternClusterRelativeLimit {M D : ℕ} (β : ℝ)
    (C : Finset (Fin M → Fin (D + 1))) (hC : C.Nonempty)
    (p : Fin M → Fin (D + 1)) : ℝ :=
  polynomialPatternPowerDifferenceLimit β
    (polynomialPatternClusterReference C hC) p

/-- Limit of the minimum relative defect on a nonempty finite cluster. -/
def polynomialPatternClusterMinimumRelativeLimit {M D : ℕ} (β : ℝ)
    (C : Finset (Fin M → Fin (D + 1))) (hC : C.Nonempty) : ℝ :=
  C.inf' hC (polynomialPatternClusterRelativeLimit β C hC)

/-- Limit of one pattern's valuation above the moving minimum of its finite cluster. -/
def polynomialPatternClusterDefectLimit {M D : ℕ} (β : ℝ)
    (C : Finset (Fin M → Fin (D + 1))) (hC : C.Nonempty)
    (p : Fin M → Fin (D + 1)) : ℝ :=
  polynomialPatternClusterRelativeLimit β C hC p -
    polynomialPatternClusterMinimumRelativeLimit β C hC

theorem polynomialPatternClusterMinValuation_eq_inf' {M D : ℕ}
    (β : ℝ) (C : Finset (Fin M → Fin (D + 1))) (hC : C.Nonempty)
    (x : ℝ) :
    polynomialPatternClusterMinValuation β C hC x =
      C.inf' hC (fun p => polynomialPatternPowerValuation β p x) := by
  simp [polynomialPatternClusterMinValuation, Finset.min'_eq_inf']

/-- The moving-minimum defect of every member of a finite equal-moment cluster converges. -/
theorem tendsto_polynomialPatternPower_cluster_defect
    {β : ℝ} {M D : ℕ}
    (C : Finset (Fin M → Fin (D + 1))) (hC : C.Nonempty)
    (hcount : ∀ p ∈ C, (∑ r, (p r : ℕ)) = D)
    (hmom : ∀ p ∈ C, ∀ r ∈ C, ∀ j < Nat.ceil β,
      polynomialPatternMoment p j = polynomialPatternMoment r j)
    {p : Fin M → Fin (D + 1)} (hp : p ∈ C) :
    Tendsto (fun x : ℝ =>
      polynomialPatternPowerValuation β p x -
        polynomialPatternClusterMinValuation β C hC x) atTop
      (𝓝 (polynomialPatternClusterDefectLimit β C hC p)) := by
  let p₀ := polynomialPatternClusterReference C hC
  have hp₀ : p₀ ∈ C := polynomialPatternClusterReference_mem C hC
  have hrel : ∀ r ∈ C, Tendsto (fun x : ℝ =>
      polynomialPatternPowerValuation β r x -
        polynomialPatternPowerValuation β p₀ x) atTop
      (𝓝 (polynomialPatternClusterRelativeLimit β C hC r)) := by
    intro r hr
    exact tendsto_polynomialPatternPowerValuation_sub_of_moments p₀ r
      (hcount p₀ hp₀) (hcount r hr) (hmom p₀ hp₀ r hr)
  have hmin : Tendsto (fun x : ℝ => C.inf' hC (fun r =>
      polynomialPatternPowerValuation β r x -
        polynomialPatternPowerValuation β p₀ x)) atTop
      (𝓝 (polynomialPatternClusterMinimumRelativeLimit β C hC)) := by
    simpa [polynomialPatternClusterMinimumRelativeLimit] using
      (Filter.Tendsto.finset_inf'_nhds_apply hC hrel)
  have hout := (hrel p hp).sub hmin
  apply hout.congr'
  apply Eventually.of_forall
  intro x
  change
    (polynomialPatternPowerValuation β p x -
          polynomialPatternPowerValuation β p₀ x) -
        C.inf' hC (fun r => polynomialPatternPowerValuation β r x -
          polynomialPatternPowerValuation β p₀ x) =
      polynomialPatternPowerValuation β p x -
        polynomialPatternClusterMinValuation β C hC x
  rw [polynomialPatternClusterMinValuation_eq_inf']
  have htranslate :
      C.inf' hC (fun r => polynomialPatternPowerValuation β r x) =
        polynomialPatternPowerValuation β p₀ x +
          C.inf' hC (fun r =>
            polynomialPatternPowerValuation β r x -
              polynomialPatternPowerValuation β p₀ x) := by
    have hmap := map_finset_inf'
      (OrderIso.addLeft (polynomialPatternPowerValuation β p₀ x)) hC
      (fun r => polynomialPatternPowerValuation β r x -
        polynomialPatternPowerValuation β p₀ x)
    change polynomialPatternPowerValuation β p₀ x +
          C.inf' hC (fun r => polynomialPatternPowerValuation β r x -
            polynomialPatternPowerValuation β p₀ x) =
        C.inf' hC (fun r => polynomialPatternPowerValuation β p₀ x +
          (polynomialPatternPowerValuation β r x -
            polynomialPatternPowerValuation β p₀ x)) at hmap
    calc
      C.inf' hC (fun r => polynomialPatternPowerValuation β r x) =
          C.inf' hC (fun r => polynomialPatternPowerValuation β p₀ x +
            (polynomialPatternPowerValuation β r x -
              polynomialPatternPowerValuation β p₀ x)) := by
        congr 1
        funext r
        ring
      _ = polynomialPatternPowerValuation β p₀ x +
          C.inf' hC (fun r => polynomialPatternPowerValuation β r x -
            polynomialPatternPowerValuation β p₀ x) := by
        exact hmap.symm
  rw [htranslate]
  ring

/-- Any natural power is dominated by an exponential of a positive real power. -/
theorem tendsto_natPow_mul_exp_neg_rpow_zero
    (P : ℕ) {c η : ℝ} (hc : 0 < c) (hη : 0 < η) :
    Tendsto (fun q : ℕ =>
      (q : ℝ) ^ P * Real.exp (-(c * (q : ℝ) ^ η))) atTop (𝓝 0) := by
  have hbase : Tendsto (fun q : ℕ => (q : ℝ) ^ η) atTop atTop :=
    (tendsto_rpow_atTop hη).comp tendsto_natCast_atTop_atTop
  have hdecayReal : Tendsto
      (fun x : ℝ => x ^ ((P : ℝ) / η) * Real.exp (-c * x))
      atTop (𝓝 0) :=
    tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero ((P : ℝ) / η) c hc
  have hdecay := hdecayReal.comp hbase
  apply hdecay.congr'
  filter_upwards with q
  have hpow : ((q : ℝ) ^ η) ^ ((P : ℝ) / η) = (q : ℝ) ^ P := by
    rw [← Real.rpow_mul (Nat.cast_nonneg q),
      show η * ((P : ℝ) / η) = (P : ℝ) by field_simp,
      Real.rpow_natCast]
  change ((q : ℝ) ^ η) ^ ((P : ℝ) / η) *
      Real.exp (-c * (q : ℝ) ^ η) =
    (q : ℝ) ^ P * Real.exp (-(c * (q : ℝ) ^ η))
  rw [hpow]
  congr 2
  ring

/-- An integer polynomial weight viewed as a complex polynomial. -/
def polynomialTailComplexWeight {M D : ℕ}
    (W : (Fin M → Fin (D + 1)) → Polynomial ℤ)
    (p : Fin M → Fin (D + 1)) : Polynomial ℂ :=
  (W p).map (Int.castRingHom ℂ)

/-- Common maximal degree of a finite integer-polynomial tail face. -/
def polynomialTailWeightDegree {M D : ℕ}
    (C : Finset (Fin M → Fin (D + 1)))
    (W : (Fin M → Fin (D + 1)) → Polynomial ℤ) : ℕ :=
  finitePolynomialFamilyMaxDegree C (polynomialTailComplexWeight W)

/-- Top coefficient selected by common-degree normalization of the tail weights. -/
def polynomialTailPolynomialLimit {M D : ℕ}
    (C : Finset (Fin M → Fin (D + 1)))
    (W : (Fin M → Fin (D + 1)) → Polynomial ℤ)
    (p : Fin M → Fin (D + 1)) : ℂ :=
  finitePolynomialFamilyLimit C (polynomialTailComplexWeight W) p

/-- Polynomially normalized tail weight with its moving-minimum power defect included. -/
def normalizedPolynomialTailWeight {M D : ℕ}
    (β B : ℝ) (C : Finset (Fin M → Fin (D + 1))) (hC : C.Nonempty)
    (K : ℕ) (W : (Fin M → Fin (D + 1)) → Polynomial ℤ)
    (t : ℕ) (p : Fin M → Fin (D + 1)) : ℂ :=
  (((W p).eval ((t + K : ℕ) : ℤ) : ℤ) : ℂ) /
      ((t + K : ℕ) : ℂ) ^ polynomialTailWeightDegree C W *
    (Real.exp (-(B * (polynomialPatternPowerValuation β p t -
      polynomialPatternClusterMinValuation β C hC t))) : ℂ)

/-- Limiting normalized weight, including the limiting power defect. -/
def polynomialTailWeightLimit {M D : ℕ}
    (β B : ℝ) (C : Finset (Fin M → Fin (D + 1))) (hC : C.Nonempty)
    (W : (Fin M → Fin (D + 1)) → Polynomial ℤ)
    (p : Fin M → Fin (D + 1)) : ℂ :=
  polynomialTailPolynomialLimit C W p *
    (Real.exp (-(B * polynomialPatternClusterDefectLimit β C hC p)) : ℂ)

/-- Every normalized polynomial tail weight converges after its valuation defect is absorbed. -/
theorem tendsto_normalizedPolynomialTailWeight
    {β B : ℝ} {M D : ℕ}
    (C : Finset (Fin M → Fin (D + 1))) (hC : C.Nonempty)
    (hcount : ∀ p ∈ C, (∑ r, (p r : ℕ)) = D)
    (hmom : ∀ p ∈ C, ∀ r ∈ C, ∀ j < Nat.ceil β,
      polynomialPatternMoment p j = polynomialPatternMoment r j)
    (K : ℕ) (W : (Fin M → Fin (D + 1)) → Polynomial ℤ)
    {p : Fin M → Fin (D + 1)} (hp : p ∈ C) :
    Tendsto (fun t => normalizedPolynomialTailWeight β B C hC K W t p)
      atTop (𝓝 (polynomialTailWeightLimit β B C hC W p)) := by
  have hpoly₀ := tendsto_finitePolynomialFamily_eval_nat_div_pow C
    (polynomialTailComplexWeight W) hp
  have hpoly := hpoly₀.comp (tendsto_add_atTop_nat K)
  have hpoly' : Tendsto (fun t : ℕ =>
      (((W p).eval ((t + K : ℕ) : ℤ) : ℤ) : ℂ) /
        ((t + K : ℕ) : ℂ) ^ polynomialTailWeightDegree C W)
      atTop (𝓝 (polynomialTailPolynomialLimit C W p)) := by
    apply hpoly.congr'
    filter_upwards with t
    apply congrArg (fun z : ℂ => z /
      ((t + K : ℕ) : ℂ) ^ polynomialTailWeightDegree C W)
    simpa [polynomialTailComplexWeight] using
      (Polynomial.eval_map_apply (p := W p)
        (f := Int.castRingHom ℂ) (x := ((t + K : ℕ) : ℤ)))
  have hdefReal :=
    (tendsto_polynomialPatternPower_cluster_defect C hC hcount hmom hp).comp
      tendsto_natCast_atTop_atTop
  have hexpReal : Tendsto (fun t : ℕ =>
      Real.exp (-(B * (polynomialPatternPowerValuation β p t -
        polynomialPatternClusterMinValuation β C hC t)))) atTop
      (𝓝 (Real.exp (-(B * polynomialPatternClusterDefectLimit β C hC p)))) := by
    convert (hdefReal.const_mul B).neg.rexp using 1
    funext t
    rfl
  have hexp : Tendsto (fun t : ℕ =>
      (Real.exp (-(B * (polynomialPatternPowerValuation β p t -
        polynomialPatternClusterMinValuation β C hC t))) : ℂ)) atTop
      (𝓝 (Real.exp (-(B * polynomialPatternClusterDefectLimit β C hC p)) : ℂ)) := by
    convert Complex.continuous_ofReal.continuousAt.tendsto.comp hexpReal using 1
    funext t
    rfl
  simpa only [normalizedPolynomialTailWeight, polynomialTailWeightLimit] using
    hpoly'.mul hexp

/-- A nonempty face of nonzero integer polynomials has a nonzero limiting normalized weight,
even after multiplication by the limiting exponential defect. -/
theorem exists_ne_zero_polynomialTailWeightLimit
    {β B : ℝ} {M D : ℕ}
    (C : Finset (Fin M → Fin (D + 1))) (hC : C.Nonempty)
    (W : (Fin M → Fin (D + 1)) → Polynomial ℤ)
    (hW : ∀ p ∈ C, W p ≠ 0) :
    ∃ p ∈ C, polynomialTailWeightLimit β B C hC W p ≠ 0 := by
  have hcomplex : ∀ p ∈ C, polynomialTailComplexWeight W p ≠ 0 := by
    intro p hp
    exact (Polynomial.map_ne_zero_iff Int.cast_injective).mpr (hW p hp)
  obtain ⟨p, hp, hpne⟩ :=
    exists_ne_zero_finitePolynomialFamilyLimit C
      (polynomialTailComplexWeight W) hC hcomplex
  refine ⟨p, hp, mul_ne_zero hpne ?_⟩
  exact Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _)

/-- **Polynomial tail-language defect compiler.**  An exponentially flat finite tail face with
nonzero integer-polynomial weights and equal moments below `ceil beta` is incompatible with a
torsion-language-universal phase.  All defect limits and normalized limiting weights are built
inside the theorem. -/
theorem false_of_torsionLanguageUniversal_polynomialTailLock
    {β B c η : ℝ} {M D K P : ℕ}
    (u : ℕ → ℂ) (hu : TorsionLanguageUniversal u)
    (C : Finset (Fin M → Fin (D + 1))) (hC : C.Nonempty)
    (W : (Fin M → Fin (D + 1)) → Polynomial ℤ)
    (hW : ∀ p ∈ C, W p ≠ 0)
    (hcount : ∀ p ∈ C, (∑ r, (p r : ℕ)) = D)
    (hmom : ∀ p ∈ C, ∀ r ∈ C, ∀ j < Nat.ceil β,
      polynomialPatternMoment p j = polynomialPatternMoment r j)
    (hc : 0 < c) (hη : 0 < η)
    (hlock : ∀ᶠ t : ℕ in atTop,
      ‖∑ p ∈ C,
          (((W p).eval ((t + K : ℕ) : ℤ) : ℤ) : ℂ) *
            (Real.exp (-(B * (polynomialPatternPowerValuation β p t -
              polynomialPatternClusterMinValuation β C hC t))) : ℂ) *
            ∏ r : Fin M, u (t + (r : ℕ)) ^ (p r : ℕ)‖ ≤
        ((t + K : ℕ) : ℝ) ^ P *
          Real.exp (-(c * ((t + K : ℕ) : ℝ) ^ η))) :
    False := by
  let w : ℕ → (Fin M → Fin (D + 1)) → ℂ := fun t p =>
    normalizedPolynomialTailWeight β B C hC K W t p
  let ell : (Fin M → Fin (D + 1)) → ℂ := fun p =>
    polynomialTailWeightLimit β B C hC W p
  have hw : ∀ p ∈ C, Tendsto (fun t => w t p) atTop (𝓝 (ell p)) := by
    intro p hp
    exact tendsto_normalizedPolynomialTailWeight C hC hcount hmom K W hp
  have hdecay := (tendsto_natPow_mul_exp_neg_rpow_zero P hc hη).comp
    (tendsto_add_atTop_nat K)
  have hbound : ∀ᶠ t : ℕ in atTop,
      ‖∑ p ∈ C, w t p *
        ∏ r : Fin M, u (t + (r : ℕ)) ^ (p r : ℕ)‖ ≤
      ((t + K : ℕ) : ℝ) ^ P *
        Real.exp (-(c * ((t + K : ℕ) : ℝ) ^ η)) := by
    filter_upwards [hlock, eventually_ge_atTop 1] with t hlockt ht
    let den : ℂ := ((t + K : ℕ) : ℂ) ^ polynomialTailWeightDegree C W
    let raw : ℂ := ∑ p ∈ C,
      (((W p).eval ((t + K : ℕ) : ℤ) : ℤ) : ℂ) *
        (Real.exp (-(B * (polynomialPatternPowerValuation β p t -
          polynomialPatternClusterMinValuation β C hC t))) : ℂ) *
        ∏ r : Fin M, u (t + (r : ℕ)) ^ (p r : ℕ)
    have hden : 1 ≤ ‖den‖ := by
      dsimp [den]
      rw [norm_pow, Complex.norm_natCast]
      exact one_le_pow₀ (by exact_mod_cast (show 1 ≤ t + K by omega))
    have hsum :
        (∑ p ∈ C, w t p *
          ∏ r : Fin M, u (t + (r : ℕ)) ^ (p r : ℕ)) = raw / den := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro p hp
      dsimp [w, normalizedPolynomialTailWeight, raw, den]
      ring
    rw [hsum, norm_div]
    exact (div_le_self (norm_nonneg raw) hden).trans hlockt
  have hface : Tendsto (fun t =>
      ∑ p ∈ C, w t p *
        ∏ r : Fin M, u (t + (r : ℕ)) ^ (p r : ℕ)) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero'
    · exact Eventually.of_forall fun t => norm_nonneg _
    · exact hbound
    · exact hdecay
  have hall := face_weights_eq_zero_of_torsionLanguageUniversal
    u hu C w ell hw hface
  obtain ⟨p, hp, hpne⟩ :=
    exists_ne_zero_polynomialTailWeightLimit C hC W hW
  exact hpne (hall p hp)

/-- A positive-degree integer ADE is incompatible with exact polynomial Taylor magnitudes of
exponent greater than two and a torsion-language-universal unit phase.  The bounded Prouhet face,
its exponentially flat phase lock, every valuation-defect limit, and the final Fourier
exactification are constructed internally. -/
theorem no_integerADE_of_polynomial_torsionLanguageUniversal
    {β B : ℝ} (hβ : 2 < β) (hB : 0 < B)
    {F : PowerSeries ℂ} {u : ℕ → ℂ}
    (hcoeff : ∀ i, PowerSeries.coeff i F =
      ((Real.exp (-(B * (i : ℝ) ^ β)) : ℝ) : ℂ) * u i)
    (huNorm : ∀ i, ‖u i‖ = 1)
    (hu : TorsionLanguageUniversal u)
    {n : ℕ} (Q : MvPolynomial (Fin (n + 2)) ℂ)
    (hQint : ∀ a, ∃ z : ℤ, MvPolynomial.coeff a Q = (z : ℂ))
    (hrel : aeval (formalJets n F) Q = 0)
    (hDpos : 0 < magnitudeMaxJetDegree n Q)
    (τ : ℕ) (hτ : τ < magnitudeMaxJetDegree n Q) :
    False := by
  have hb : ∀ i, ‖PowerSeries.coeff i F‖ =
      Real.exp (-(B * (i : ℝ) ^ β)) := by
    intro i
    rw [hcoeff, norm_mul, huNorm, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
  obtain ⟨K, M, hdata⟩ :=
    exists_polynomialTaylorProuhetPhaseLock hβ hB F Q hQint hb hrel hDpos τ hτ
  let D := magnitudeMaxJetDegree n Q
  let S := polynomialPatternSurvivors n D K τ Q M
  change ∃ hS : S.Nonempty,
    let T := polynomialPatternLeastSourceClass S hS
    let hT := polynomialPatternLeastSourceClass_nonempty S hS
    let C := polynomialPatternMinimalCluster (R := Nat.ceil β - 2) T hT
    let hC := polynomialPatternMinimalCluster_nonempty T hT
    let m : ℕ → ℝ := fun q => B *
      polynomialPatternClusterMinValuation β C hC ((q : ℝ) - K)
    ∃ (W : (Fin M → Fin (D + 1)) → Polynomial ℤ)
        (c A : ℝ) (P : ℕ),
      0 < c ∧ 0 < A ∧ 2 ≤ C.card ∧ C ⊆ S ∧
      (∀ p ∈ S, W p ≠ 0 ∧ ∀ q, K + n ≤ q →
        aevalWeight n (D * q + τ) Q (shiftedAtomPatternKey q K p) =
          (((W p).eval (q : ℤ) : ℤ) : ℂ)) ∧
      (∀ p ∈ C, ∀ r ∈ C,
        (∀ j < Nat.ceil β,
          polynomialPatternMoment p j = polynomialPatternMoment r j) ∧
        (Polynomial.X - 1) ^ Nat.ceil β ∣
          atomPatternDifferencePolynomial p r) ∧
      (∀ᶠ q : ℕ in atTop, ∀ p ∈ C,
        0 ≤ atomValuation (fun i => B * (i : ℝ) ^ β)
            (shiftedAtomPatternKey q K p) - m q ∧
        atomValuation (fun i => B * (i : ℝ) ^ β)
            (shiftedAtomPatternKey q K p) - m q ≤ A) ∧
      (∀ᶠ q : ℕ in atTop,
        ‖∑ p ∈ C,
            aevalWeight n (D * q + τ) Q (shiftedAtomPatternKey q K p) *
              (Real.exp (-(atomValuation (fun i => B * (i : ℝ) ^ β)
                (shiftedAtomPatternKey q K p) - m q)) : ℂ) *
              normalizedAtomPhase F (fun i => B * (i : ℝ) ^ β)
                (shiftedAtomPatternKey q K p)‖ ≤
          (q : ℝ) ^ P * Real.exp (-(c * (q : ℝ) ^
            polynomialPhaseLockExponent β))) at hdata
  obtain ⟨hS, W, c, A, P, hc, _hA, _hcard, hCS, hW,
    hcluster, _hdelta, hlock⟩ := hdata
  let T := polynomialPatternLeastSourceClass S hS
  let hT : T.Nonempty := polynomialPatternLeastSourceClass_nonempty S hS
  let C := polynomialPatternMinimalCluster (R := Nat.ceil β - 2) T hT
  let hC : C.Nonempty := polynomialPatternMinimalCluster_nonempty T hT
  let m : ℕ → ℝ := fun q => B *
    polynomialPatternClusterMinValuation β C hC ((q : ℝ) - K)
  have hη : 0 < polynomialPhaseLockExponent β :=
    polynomialPhaseLockExponent_pos hβ
  have hlockShift := (tendsto_add_atTop_nat K).eventually hlock
  have htail : ∀ᶠ t : ℕ in atTop,
      ‖∑ p ∈ C,
          (((W p).eval ((t + K : ℕ) : ℤ) : ℤ) : ℂ) *
            (Real.exp (-(B * (polynomialPatternPowerValuation β p t -
              polynomialPatternClusterMinValuation β C hC t))) : ℂ) *
            ∏ r : Fin M, u (t + (r : ℕ)) ^ (p r : ℕ)‖ ≤
        ((t + K : ℕ) : ℝ) ^ P *
          Real.exp (-(c * ((t + K : ℕ) : ℝ) ^
            polynomialPhaseLockExponent β)) := by
    filter_upwards [hlockShift, eventually_ge_atTop n] with t hlockt ht
    have hsum :
        (∑ p ∈ C,
          (((W p).eval ((t + K : ℕ) : ℤ) : ℤ) : ℂ) *
            (Real.exp (-(B * (polynomialPatternPowerValuation β p t -
              polynomialPatternClusterMinValuation β C hC t))) : ℂ) *
            ∏ r : Fin M, u (t + (r : ℕ)) ^ (p r : ℕ)) =
        ∑ p ∈ C,
          aevalWeight n (D * (t + K) + τ) Q
              (shiftedAtomPatternKey (t + K) K p) *
            (Real.exp (-(atomValuation (fun i => B * (i : ℝ) ^ β)
              (shiftedAtomPatternKey (t + K) K p) - m (t + K))) : ℂ) *
            normalizedAtomPhase F (fun i => B * (i : ℝ) ^ β)
              (shiftedAtomPatternKey (t + K) K p) := by
      apply Finset.sum_congr rfl
      intro p hp
      have hpS : p ∈ S := hCS hp
      have hweq := (hW p hpS).2 (t + K) (by omega)
      have hpval := atomValuation_shiftedAtomPatternKey
        (B := B) (β := β) p (show K ≤ t + K by omega)
      have hbase : (((t + K : ℕ) : ℝ) - K) = (t : ℝ) := by
        push_cast
        ring
      have hdef :
          atomValuation (fun i => B * (i : ℝ) ^ β)
              (shiftedAtomPatternKey (t + K) K p) - m (t + K) =
            B * (polynomialPatternPowerValuation β p t -
              polynomialPatternClusterMinValuation β C hC t) := by
        rw [hpval]
        dsimp [m]
        rw [hbase]
        ring
      have hphase :
          normalizedAtomPhase F (fun i => B * (i : ℝ) ^ β)
              (shiftedAtomPatternKey (t + K) K p) =
            ∏ r : Fin M, u (t + (r : ℕ)) ^ (p r : ℕ) := by
        simpa [windowShift] using
          normalizedAtomPhase_shiftedAtomPatternKey_eq F
            (fun i => B * (i : ℝ) ^ β) u hcoeff (t + K) K p
      rw [hweq, hdef, hphase]
    rw [hsum]
    exact hlockt
  exact false_of_torsionLanguageUniversal_polynomialTailLock
    u hu C hC W
    (fun p hp => (hW p (hCS hp)).1)
    (fun p hp => polynomialPatternSurvivors_count (hCS hp))
    (fun p hp r hr j hj => (hcluster p hp r hr).1 j hj)
    hc hη htail

set_option maxHeartbeats 1200000 in
/-- **Polynomial TLU hypertranscendence.**  A smooth complex function whose Taylor coefficients
have exact magnitudes `exp (-B n^beta)` with `beta > 2` and a torsion-language-universal unit phase
satisfies no algebraic differential equation. -/
theorem hypertranscendental_of_polynomial_torsionLanguageUniversal
    {f : ℂ → ℂ} (hf : ContDiff ℂ (⊤ : ℕ∞) f)
    {β B : ℝ} (hβ : 2 < β) (hB : 0 < B)
    {u : ℕ → ℂ}
    (hcoeff : ∀ i, PowerSeries.coeff i (taylorPS f) =
      ((Real.exp (-(B * (i : ℝ) ^ β)) : ℝ) : ℂ) * u i)
    (huNorm : ∀ i, ‖u i‖ = 1)
    (hu : TorsionLanguageUniversal u) :
    Hypertranscendental f := by
  intro hDA
  obtain ⟨n, P, hP, hPfun⟩ := hDA
  have hjz : jetFun f n P = 0 := by
    funext z
    exact hPfun z
  have hformal : aeval (formalJets n (taylorPS f)) P = 0 := by
    rw [← taylorPS_jetFun f n hf P, hjz,
      show (0 : ℂ → ℂ) = fun _ => (0 : ℂ) from rfl, taylorPS_const, map_zero]
  obtain ⟨n', Q, hQ, hQint, hrel⟩ :=
    formal_mahler_integer_normalization hP hformal
  have hb : ∀ i, ‖PowerSeries.coeff i (taylorPS f)‖ =
      Real.exp (-(B * (i : ℝ) ^ β)) := by
    intro i
    rw [hcoeff, norm_mul, huNorm, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
  have hDpos := magnitudeMaxJetDegree_pos_of_integer_relation
    (taylorPS f) hb Q hQ hQint hrel
  exact no_integerADE_of_polynomial_torsionLanguageUniversal
    hβ hB hcoeff huNorm hu Q hQint hrel hDpos 0 (by simpa using hDpos)

end

end GaloisForLFunctions
