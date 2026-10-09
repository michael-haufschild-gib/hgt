import GaloisForLFunctions.RHTower.RiemannGaussian.GaussianXiLogDerivativeGrowth
import GaloisForLFunctions.HTGeometry.GaussianLightConeAmplification

/-!
# Bounded Gaussian explicit-formula ceiling: the source-native amplified HCF receiver

The arithmetic Gaussian explicit formula

`G(ε, t) = gaussianArchimedeanContribution ε t - gaussianPrimeContribution ε t`

is an explicit expression in Gamma data, the pole of zeta and the von Mangoldt series
`Σ_n Λ(n) n^{-1/2} e^{-(log n)²/(4ε)} cos(t log n)`.  It is unconditionally identified with the
symmetric zero sum `2 Re Σ_ρ exp(-ε (γ_ρ - t)²)` over the spectral coordinates
`γ_ρ = -i(ρ - 1/2)` (`RiemannGaussian.gaussianArithmeticExplicitFormula_eq_canonical`).

**Theorem** (`riemannHypothesis_iff_forall_gaussianArithmeticExplicitFormula_bounded`).  RH holds
iff for every real centre `t` the explicit expression `G(ε, t)` stays bounded on `ε ≥ 1`.

Under RH every Gaussian term has modulus at most `exp(-(Re γ - t)²)`, so the bound is the convergent
Gaussian ordinate sum.  Conversely, an off-line zero lies in the open light cone over its own
height.  The real part `Re S = (S + conj S)/2` is an exponential sum over two copies of the zeros,
with exponents `(γ - t)²` and their conjugates and constant coefficient `1/2`.  Light-cone
amplification (`HTGeometry.exists_lt_norm_tsum_mul_exp_neg_of_re_neg`) makes it unbounded.

So the remaining step of the amplified HCF route is purely arithmetic: an `O(1)` bound, uniform in
the width, for the Gaussian-smoothed von Mangoldt sums against the explicit Gamma and pole terms.
No sign condition and no ceiling below a fixed quantum is required.
-/

open Complex Set

namespace RHTower

open RiemannGaussian GaloisForLFunctions.HTGeometry

noncomputable section

/-- The explicit formula in terms of a single translated-Gaussian sum over zero occurrences. -/
theorem gaussianArithmeticExplicitFormula_eq_two_re_tsum {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    gaussianArithmeticExplicitFormula ε t =
      2 * (∑' o : NontrivialZetaZeroOccurrence analyticZetaZeroMultiplicity,
        Complex.exp (-(ε : ℂ) * (zetaSpectralCoordinate o.1.1 - t) ^ 2)).re := by
  rw [gaussianArithmeticExplicitFormula_eq_canonical hε t, canonicalZetaSymmetricGaussianZeroSum,
    canonicalZetaGaussianZeroSum]
  congr 3
  funext o
  simp only [zetaGaussianZeroSummand, complexTranslatedGaussian, neg_mul]

/-- Gaussian majorant of one translated spectral Gaussian. -/
theorem norm_exp_neg_mul_spectral_sub_sq_le {ε : ℝ} (hε : 0 ≤ ε) (t : ℝ)
    (o : NontrivialZetaZeroOccurrence analyticZetaZeroMultiplicity) :
    ‖Complex.exp (-(ε : ℂ) * (zetaSpectralCoordinate o.1.1 - t) ^ 2)‖ ≤
      Real.exp (ε / 4 + ε * t ^ 2) *
        Real.exp (-(ε / 2) * (zetaSpectralCoordinate o.1.1).re ^ 2) := by
  rw [norm_exp_neg_mul_sub_sq, ← Real.exp_add]
  refine Real.exp_le_exp.2 ?_
  have him := NontrivialZetaZero.abs_spectralCoordinate_im_lt_half o.1
  have hy : (zetaSpectralCoordinate o.1.1).im ^ 2 ≤ 1 / 4 := by
    have := sq_le_sq' (abs_le.1 him.le).1 (abs_le.1 him.le).2
    linarith
  set x := (zetaSpectralCoordinate o.1.1).re
  have hx : x ^ 2 / 2 - t ^ 2 ≤ (x - t) ^ 2 := by nlinarith [sq_nonneg (x - 2 * t)]
  nlinarith [mul_le_mul_of_nonneg_left hx hε, mul_le_mul_of_nonneg_left hy hε]

theorem summable_norm_exp_neg_mul_spectral_sub_sq {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    Summable (fun o : NontrivialZetaZeroOccurrence analyticZetaZeroMultiplicity =>
      ‖Complex.exp (-(ε : ℂ) * (zetaSpectralCoordinate o.1.1 - t) ^ 2)‖) :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (norm_exp_neg_mul_spectral_sub_sq_le hε.le t)
    ((zetaZeroGaussianOrdinateSummable (ε / 2) (by positivity)).mul_left _)

/-- For `ε ≥ 1`, outside the light cone a term is dominated by a width-one Gaussian majorant. -/
theorem norm_exp_neg_mul_spectral_sub_sq_le_of_re_nonneg {ε : ℝ} (hε : 1 ≤ ε) (t : ℝ)
    (o : NontrivialZetaZeroOccurrence analyticZetaZeroMultiplicity)
    (hre : 0 ≤ ((zetaSpectralCoordinate o.1.1 - t) ^ 2).re) :
    ‖Complex.exp (-(ε : ℂ) * (zetaSpectralCoordinate o.1.1 - t) ^ 2)‖ ≤
      Real.exp (1 / 4 + t ^ 2) *
        Real.exp (-(1 / 2) * (zetaSpectralCoordinate o.1.1).re ^ 2) := by
  rw [norm_exp_neg_mul_sub_sq, ← Real.exp_add]
  refine Real.exp_le_exp.2 ?_
  rw [re_sub_ofReal_sq] at hre
  have him := NontrivialZetaZero.abs_spectralCoordinate_im_lt_half o.1
  have hy : (zetaSpectralCoordinate o.1.1).im ^ 2 ≤ 1 / 4 := by
    have := sq_le_sq' (abs_le.1 him.le).1 (abs_le.1 him.le).2
    linarith
  set x := (zetaSpectralCoordinate o.1.1).re
  have hx : x ^ 2 / 2 - t ^ 2 ≤ (x - t) ^ 2 := by nlinarith [sq_nonneg (x - 2 * t)]
  nlinarith

/-- **Ceiling under RH.**  Every zero on the line keeps the arithmetic Gaussian explicit formula
below twice the width-one Gaussian ordinate sum, for every width `ε ≥ 1`. -/
theorem abs_gaussianArithmeticExplicitFormula_le_of_riemannHypothesis
    (hRH : RiemannHypothesis) (t : ℝ) {ε : ℝ} (hε : 1 ≤ ε) :
    |gaussianArithmeticExplicitFormula ε t| ≤
      2 * ∑' o : NontrivialZetaZeroOccurrence analyticZetaZeroMultiplicity,
        Real.exp (1 / 4 + t ^ 2) *
          Real.exp (-(1 / 2) * (zetaSpectralCoordinate o.1.1).re ^ 2) := by
  rw [gaussianArithmeticExplicitFormula_eq_two_re_tsum (by linarith) t, abs_mul,
    abs_of_pos two_pos]
  refine mul_le_mul_of_nonneg_left ((Complex.abs_re_le_norm _).trans ?_) zero_le_two
  have hcone : ∀ o : NontrivialZetaZeroOccurrence analyticZetaZeroMultiplicity,
      0 ≤ ((zetaSpectralCoordinate o.1.1 - t) ^ 2).re := fun o => by
    rw [re_sub_ofReal_sq, (zetaSpectralCoordinate_im_eq_zero_iff _).2
      (hRH o.1.1 o.1.2.1 o.1.2.2.1 o.1.2.2.2)]
    nlinarith
  have h := norm_tsum_mul_exp_neg_le_of_re_nonneg (ε₀ := 1)
    (w := fun o : NontrivialZetaZeroOccurrence analyticZetaZeroMultiplicity =>
      (zetaSpectralCoordinate o.1.1 - t) ^ 2) (c := fun _ => (1 : ℂ))
    ((zetaZeroGaussianOrdinateSummable (1 / 2) (by norm_num)).mul_left _)
    (fun o ho ε' hε' => by
      rw [one_mul]
      exact norm_exp_neg_mul_spectral_sub_sq_le_of_re_nonneg hε' t o ho)
    (fun ε' hε' => by
      simp only [one_mul]
      exact summable_norm_exp_neg_mul_spectral_sub_sq (by linarith) t)
    hcone hε
  simpa only [one_mul] using h

/-- **Local light-cone obstruction.**  A nontrivial zero whose spectral coordinate lies in the open
light cone over `t` makes the arithmetic Gaussian formula unbounded in the width at height `t`. -/
theorem not_bounded_gaussianArithmeticExplicitFormula_of_cone {s : ℂ} (hs : riemannZeta s = 0)
    (hnt : ¬ ∃ n : ℕ, s = -2 * (n + 1)) (hne1 : s ≠ 1) {t : ℝ}
    (hcone : ((zetaSpectralCoordinate s).re - t) ^ 2 < (zetaSpectralCoordinate s).im ^ 2) :
    ¬ ∃ C : ℝ, ∀ ε : ℝ, 1 ≤ ε → |gaussianArithmeticExplicitFormula ε t| ≤ C := by
  rintro ⟨C, hC⟩
  set ρ : NontrivialZetaZero := ⟨s, hs, hnt, hne1⟩ with hρ
  set o₀ : NontrivialZetaZeroOccurrence analyticZetaZeroMultiplicity :=
    ⟨ρ, ⟨0, analyticZetaZeroMultiplicity_positive ρ⟩⟩ with ho₀
  -- the light cone over `t` contains only finitely many occurrences
  set F : Set (NontrivialZetaZeroOccurrence analyticZetaZeroMultiplicity) :=
    {o | ((zetaSpectralCoordinate o.1.1 - t) ^ 2).re < 0} with hFdef
  have hF : F.Finite := by
    have hK := IsCompact.inter_nontrivialZetaZeroSet_finite
      (isCompact_closedBall (0 : ℂ) (|t| + 2))
    have hA : {ρ : NontrivialZetaZero | ρ.1 ∈ Metric.closedBall (0 : ℂ) (|t| + 2)}.Finite :=
      (hK.preimage Subtype.val_injective.injOn).subset fun ρ hρ => ⟨hρ, ρ.2⟩
    refine ((hA.biUnion fun ρ _ =>
      Set.finite_range (fun k : Fin (analyticZetaZeroMultiplicity ρ) =>
        (⟨ρ, k⟩ : NontrivialZetaZeroOccurrence analyticZetaZeroMultiplicity)))).subset ?_
    intro o ho
    refine Set.mem_biUnion (x := o.1) ?_ ⟨o.2, rfl⟩
    simp only [hFdef, Set.mem_setOf_eq, re_sub_ofReal_sq] at ho
    have him := NontrivialZetaZero.abs_spectralCoordinate_im_lt_half o.1
    have hy2 : (zetaSpectralCoordinate o.1.1).im ^ 2 < (1 / 2) ^ 2 := by
      have := sq_lt_sq' (abs_lt.1 him).1 (abs_lt.1 him).2
      linarith
    have hre : |(zetaSpectralCoordinate o.1.1).re - t| < 1 / 2 := by
      have h1 : ((zetaSpectralCoordinate o.1.1).re - t) ^ 2 < (1 / 2) ^ 2 := by linarith
      rw [sq_lt_sq, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] at h1
      exact h1
    rw [zetaSpectralCoordinate_re] at hre
    have him' : |(o.1.1).im| ≤ |t| + 1 / 2 := by
      have := abs_sub_abs_le_abs_sub (o.1.1).im t
      linarith
    have hre0 := NontrivialZetaZero.zero_lt_re o.1
    have hre1 := NontrivialZetaZero.re_lt_one o.1
    show o.1.1 ∈ Metric.closedBall (0 : ℂ) (|t| + 2)
    rw [Metric.mem_closedBall, dist_zero_right]
    calc ‖o.1.1‖ ≤ |(o.1.1).re| + |(o.1.1).im| := Complex.norm_le_abs_re_add_abs_im _
      _ ≤ 1 + (|t| + 1 / 2) := by
        rw [abs_of_pos hre0]
        linarith
      _ ≤ |t| + 2 := by linarith
  -- the doubled family representing the real part
  set W : NontrivialZetaZeroOccurrence analyticZetaZeroMultiplicity → ℂ :=
    fun o => (zetaSpectralCoordinate o.1.1 - t) ^ 2 with hWdef
  set w : NontrivialZetaZeroOccurrence analyticZetaZeroMultiplicity ⊕
      NontrivialZetaZeroOccurrence analyticZetaZeroMultiplicity → ℂ :=
    Sum.elim W (fun o => (starRingEnd ℂ) (W o)) with hwdef
  have hwre : ∀ j, (w j).re = (W (Sum.elim id id j)).re := fun j => by
    cases j <;> simp [hwdef]
  set m₀ : NontrivialZetaZeroOccurrence analyticZetaZeroMultiplicity → ℝ :=
    fun o => 1 / 2 * (Real.exp (1 / 4 + t ^ 2) *
      Real.exp (-(1 / 2) * (zetaSpectralCoordinate o.1.1).re ^ 2)) with hm₀def
  have hm₀ : Summable m₀ :=
    ((zetaZeroGaussianOrdinateSummable (1 / 2) (by norm_num)).mul_left _).mul_left _
  have hnorm_conj : ∀ (ε : ℝ) (o : NontrivialZetaZeroOccurrence analyticZetaZeroMultiplicity),
      ‖Complex.exp (-(ε : ℂ) * (starRingEnd ℂ) (W o))‖ =
        ‖Complex.exp (-(ε : ℂ) * W o)‖ := fun ε o => by
    rw [Complex.norm_exp, Complex.norm_exp, neg_mul, neg_mul, Complex.neg_re, Complex.neg_re,
      Complex.re_ofReal_mul, Complex.re_ofReal_mul, Complex.conj_re]
  have hsum2 : ∀ ε : ℝ, 1 ≤ ε → Summable (fun j =>
      ‖(1 / 2 : ℂ) * Complex.exp (-(ε : ℂ) * w j)‖) := fun ε hε => by
    have hbase := (summable_norm_exp_neg_mul_spectral_sub_sq (by linarith : (0 : ℝ) < ε) t).mul_left
      (1 / 2 : ℝ)
    refine Summable.sum _ ?_ ?_
    · refine hbase.congr fun o => ?_
      simp [hwdef, hWdef]
    · refine hbase.congr fun o => ?_
      simp only [Function.comp_apply, hwdef, Sum.elim_inr, norm_mul, hnorm_conj]
      simp [hWdef]
  have hmaj2 : ∀ j, 0 ≤ (w j).re → ∀ ε : ℝ, 1 ≤ ε →
      ‖(1 / 2 : ℂ) * Complex.exp (-(ε : ℂ) * w j)‖ ≤ Sum.elim m₀ m₀ j := by
    intro j hj ε hε
    rcases j with o | o
    · simp only [hwdef, Sum.elim_inl] at hj ⊢
      rw [norm_mul, hm₀def]
      simp only [norm_div, norm_one, Complex.norm_ofNat]
      exact mul_le_mul_of_nonneg_left
        (norm_exp_neg_mul_spectral_sub_sq_le_of_re_nonneg hε t o hj) (by norm_num)
    · simp only [hwdef, Sum.elim_inr, Complex.conj_re] at hj ⊢
      rw [norm_mul, hnorm_conj, hm₀def]
      simp only [norm_div, norm_one, Complex.norm_ofNat]
      exact mul_le_mul_of_nonneg_left
        (norm_exp_neg_mul_spectral_sub_sq_le_of_re_nonneg hε t o hj) (by norm_num)
  have hfin2 : {j | (w j).re < 0}.Finite := by
    refine ((hF.image Sum.inl).union (hF.image Sum.inr)).subset fun j hj => ?_
    rcases j with o | o
    · exact Or.inl ⟨o, by simpa [hwdef, hWdef, hFdef] using hj, rfl⟩
    · refine Or.inr ⟨o, ?_, rfl⟩
      have h' : ((starRingEnd ℂ) (W o)).re < 0 := hj
      rw [Complex.conj_re] at h'
      exact h'
  have hneg : ∃ j, (w j).re < 0 := by
    refine ⟨Sum.inl o₀, ?_⟩
    simp only [hwdef, Sum.elim_inl, hWdef, re_sub_ofReal_sq]
    have h0 : o₀.1.1 = s := rfl
    rw [h0]
    linarith
  obtain ⟨ε, hε, hlt⟩ := exists_lt_norm_tsum_mul_exp_neg_of_re_neg zero_le_one
    (w := w) (c := fun _ => (1 / 2 : ℂ)) (fun _ _ _ => rfl) (fun _ _ => by norm_num) hfin2
    (m := Sum.elim m₀ m₀) (fun j => by
      rcases j with o | o <;> simp only [Sum.elim_inl, Sum.elim_inr, hm₀def] <;> positivity)
    (Summable.sum _ hm₀ hm₀) hmaj2 hsum2 hneg (C / 2)
  -- identify the doubled sum with the real part of the Gaussian sum
  set S := ∑' o : NontrivialZetaZeroOccurrence analyticZetaZeroMultiplicity,
    Complex.exp (-(ε : ℂ) * W o) with hSdef
  have hsumS : Summable (fun o : NontrivialZetaZeroOccurrence analyticZetaZeroMultiplicity =>
      Complex.exp (-(ε : ℂ) * W o)) :=
    (summable_norm_exp_neg_mul_spectral_sub_sq (by linarith : (0 : ℝ) < ε) t).of_norm
  have hconj : ∀ o : NontrivialZetaZeroOccurrence analyticZetaZeroMultiplicity,
      Complex.exp (-(ε : ℂ) * (starRingEnd ℂ) (W o)) =
        (starRingEnd ℂ) (Complex.exp (-(ε : ℂ) * W o)) := fun o => by
    rw [← Complex.exp_conj, map_mul, map_neg, Complex.conj_ofReal]
  have hS1 : Summable ((fun j => (1 / 2 : ℂ) * Complex.exp (-(ε : ℂ) * w j)) ∘ Sum.inl) :=
    hsumS.mul_left (1 / 2)
  have hS2 : Summable ((fun j => (1 / 2 : ℂ) * Complex.exp (-(ε : ℂ) * w j)) ∘ Sum.inr) := by
    refine ((hsumS.map (starRingEnd ℂ) Complex.continuous_conj).mul_left (1 / 2)).congr
      fun o => ?_
    simp only [Function.comp_apply, hwdef, Sum.elim_inr]
    rw [hconj]
  have hdoubled : ∑' j, (1 / 2 : ℂ) * Complex.exp (-(ε : ℂ) * w j) = (S.re : ℂ) := by
    rw [Summable.tsum_sum hS1 hS2]
    have h1 : ∑' o, (1 / 2 : ℂ) * Complex.exp (-(ε : ℂ) * w (Sum.inl o)) = 1 / 2 * S := by
      rw [tsum_mul_left]
      rfl
    have h2 : ∑' o, (1 / 2 : ℂ) * Complex.exp (-(ε : ℂ) * w (Sum.inr o)) =
        1 / 2 * (starRingEnd ℂ) S := by
      simp only [hwdef, Sum.elim_inr]
      simp_rw [hconj]
      rw [tsum_mul_left, ← conj_tsum]
    rw [h1, h2, ← mul_add, Complex.add_conj]
    push_cast
    ring
  rw [hdoubled, Complex.norm_real, Real.norm_eq_abs] at hlt
  have hform := gaussianArithmeticExplicitFormula_eq_two_re_tsum (by linarith : (0 : ℝ) < ε) t
  have hbound := hC ε hε
  rw [hform, abs_mul, abs_of_pos two_pos] at hbound
  have : S = ∑' o : NontrivialZetaZeroOccurrence analyticZetaZeroMultiplicity,
      Complex.exp (-(ε : ℂ) * (zetaSpectralCoordinate o.1.1 - t) ^ 2) := rfl
  rw [← this] at hbound
  linarith


/-- **Source-native amplified HCF receiver.**  RH holds iff the explicit arithmetic Gaussian
formula is bounded in the width `ε ≥ 1` at every real centre `t`. -/
theorem riemannHypothesis_iff_forall_gaussianArithmeticExplicitFormula_bounded :
    RiemannHypothesis ↔
      ∀ t : ℝ, ∃ C : ℝ, ∀ ε : ℝ, 1 ≤ ε → |gaussianArithmeticExplicitFormula ε t| ≤ C := by
  constructor
  · intro hRH t
    exact ⟨_, fun ε hε => abs_gaussianArithmeticExplicitFormula_le_of_riemannHypothesis hRH t hε⟩
  · intro hbdd
    rw [riemannHypothesis_iff_spectralCoordinate_real]
    intro s hs hnt hne1
    by_contra hy
    refine not_bounded_gaussianArithmeticExplicitFormula_of_cone hs hnt hne1 (t :=
      (zetaSpectralCoordinate s).re) ?_ (hbdd _)
    rw [sub_self]
    have := pow_pos (abs_pos.2 hy) 2
    rw [sq_abs] at this
    nlinarith

/-- **Countable form.**  RH holds iff the explicit arithmetic Gaussian formula is bounded in the
width at every rational height: every off-line light cone contains a rational centre. -/
theorem riemannHypothesis_iff_forall_rat_gaussianArithmeticExplicitFormula_bounded :
    RiemannHypothesis ↔
      ∀ r : ℚ, ∃ C : ℝ, ∀ ε : ℝ, 1 ≤ ε → |gaussianArithmeticExplicitFormula ε r| ≤ C := by
  constructor
  · intro hRH r
    exact riemannHypothesis_iff_forall_gaussianArithmeticExplicitFormula_bounded.1 hRH r
  · intro hbdd
    rw [riemannHypothesis_iff_spectralCoordinate_real]
    intro s hs hnt hne1
    by_contra hy
    set x := (zetaSpectralCoordinate s).re
    set y := (zetaSpectralCoordinate s).im
    have hy0 : 0 < |y| := abs_pos.2 hy
    obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn (show x - |y| < x + |y| by linarith)
    refine not_bounded_gaussianArithmeticExplicitFormula_of_cone hs hnt hne1 (t := r) ?_ (hbdd r)
    have habs : |x - r| < |y| := abs_sub_lt_iff.2 ⟨by linarith, by linarith⟩
    exact sq_lt_sq.2 habs

end

end RHTower
