import GaloisForLFunctions.ArithmeticCriticalityTheory.FullZeroFormWeilPositivity

/-!
# The Markov form is never subcritical on the primitive hyperplane

On real tests the Markov form has one negative direction, Riemann's kernel `Φ`
(`Q(Φ u_L) → −1/2`), and RH is its nonnegativity on the primitive hyperplane
`H = {F : ∫ F cosh(x/2) = 0}`, the `Q`-orthogonal complement of `Φ`. On `H` the form is never
subcritical:

**Theorem** (`exists_primitive_markovEnergy_lt_integral_weight_mul_sq`). For every locally
integrable `W ≥ 0` positive on a set of positive measure there is a real `F ∈ C²_c` with
`∫ F cosh(x/2) = 0` and `markovEnergy(F) < ∫ W F²`.

Hence RH ⟺ the Markov form on `H` is nonnegative and critical
(`riemannHypothesis_iff_primitive_nonneg_and_no_hardyWeight`); together with the odd-sector
theorem, the form is critical wherever RH makes it nonnegative.

Null sequences: the even harmonic pairs `ω_b = τ_b + τ_{−b} − 2 cosh(b/2) τ_0` (`A = B = 0`) have
plateau energies → 0 and pair with every test through their source, which vanishes. Their cosh
moments are only asymptotically zero; a vanishing multiple of the truncated kernel `Φ u_0` puts
them exactly on `H`. Unlike the odd pairs they separate every point, the origin included: at a fixed
`x`, `2 cosh(b/2) Φ(x)` outgrows `Φ(x ± b) ≤ Φ(0)`.
-/

open MeasureTheory Set Filter Topology
open RHTower RHTower.CHMDPolar

noncomputable section

namespace GaloisForLFunctions.ArithmeticCriticalityTheory

/-- Shifts `b, −b, 0` of the even harmonic pair. -/
def evenNullShift (b : ℝ) : Fin 3 → ℝ := ![b, -b, 0]

/-- Coefficients `1, 1, −2 cosh(b/2)` of the even harmonic pair. -/
def evenNullCoeff (b : ℝ) : Fin 3 → ℝ := ![1, 1, -(2 * Real.cosh (b / 2))]

theorem translateCoshCoefficient_evenNull (b : ℝ) :
    translateCoshCoefficient Finset.univ (evenNullCoeff b) (evenNullShift b) = 0 := by
  simp [translateCoshCoefficient, Fin.sum_univ_three, evenNullCoeff, evenNullShift,
    show -b / 2 = -(b / 2) by ring, Real.cosh_neg]
  ring

theorem translateSinhCoefficient_evenNull (b : ℝ) :
    translateSinhCoefficient Finset.univ (evenNullCoeff b) (evenNullShift b) = 0 := by
  simp [translateSinhCoefficient, Fin.sum_univ_three, evenNullCoeff, evenNullShift,
    show -b / 2 = -(b / 2) by ring, Real.sinh_neg]

theorem riemannKernelReal_mul_translateSpan_evenNull (b x : ℝ) :
    riemannKernelReal x * translateSpan Finset.univ (evenNullCoeff b) (evenNullShift b) x =
      riemannKernelReal (x - b) + riemannKernelReal (x + b) -
        2 * Real.cosh (b / 2) * riemannKernelReal x := by
  rw [riemannKernelReal_mul_translateSpan]
  simp [Fin.sum_univ_three, evenNullCoeff, evenNullShift, sub_neg_eq_add]
  ring

/-- The even harmonic pairs separate every point. -/
theorem exists_nat_evenNull_ne_zero (x : ℝ) :
    ∃ n : ℕ, riemannKernelReal x * translateSpan Finset.univ (evenNullCoeff n) (evenNullShift n) x
      ≠ 0 := by
  have hΦx := riemannKernelReal_pos x
  obtain ⟨n, hn⟩ := exists_nat_gt (2 * riemannKernelReal 0 / riemannKernelReal x)
  refine ⟨n, fun h0 => ?_⟩
  rw [riemannKernelReal_mul_translateSpan_evenNull] at h0
  have h1 : (n : ℝ) / 2 ≤ Real.cosh ((n : ℝ) / 2) := by
    have := Real.self_le_sinh_iff.mpr (show (0 : ℝ) ≤ (n : ℝ) / 2 by positivity)
    linarith [(Real.sinh_lt_cosh ((n : ℝ) / 2)).le]
  have h2 := riemannKernelReal_le_zero_point (x - n)
  have h3 := riemannKernelReal_le_zero_point (x + n)
  have h4 : 2 * riemannKernelReal 0 < n * riemannKernelReal x := by rwa [div_lt_iff₀ hΦx] at hn
  nlinarith [mul_le_mul_of_nonneg_right h1 hΦx.le]

/-- The cosh moment of the truncated kernel at `L = 0`, a fixed nonzero normaliser. -/
theorem evenPoleMoment_phiDoob_smoothPlateau_zero_pos :
    0 < evenPoleMoment (phiDoobTest (smoothPlateau 0)) := by
  unfold evenPoleMoment phiDoobTest
  have hc : Continuous fun x => riemannKernelReal x * smoothPlateau 0 x * Real.cosh (x / 2) :=
    (continuous_riemannKernelReal.mul (contDiff_smoothPlateau 0).continuous).mul
      (Real.continuous_cosh.comp (continuous_id.div_const 2))
  refine Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := 0) hc
    ((hasCompactSupport_smoothPlateau 0).mul_left.mul_right) (fun x => ?_) ?_
  · exact mul_nonneg (mul_nonneg (riemannKernelReal_pos x).le (smoothPlateau_nonneg 0 x))
      (Real.cosh_pos _).le
  · rw [smoothPlateau_eq_one (by simp)]
    have := riemannKernelReal_pos 0
    have := Real.cosh_pos ((0 : ℝ) / 2)
    positivity

/-- **No Hardy weight on the primitive hyperplane.** -/
theorem exists_primitive_markovEnergy_lt_integral_weight_mul_sq {W : ℝ → ℝ}
    (hW0 : ∀ x, 0 ≤ W x) (hWi : LocallyIntegrable W) (hWpos : 0 < volume {x | 0 < W x}) :
    ∃ F : ℝ → ℝ, ContDiff ℝ 2 F ∧ HasCompactSupport F ∧ (∫ x, F x * Real.cosh (x / 2)) = 0 ∧
      markovEnergy (fun x => (F x : ℂ)) < ∫ x, W x * F x ^ 2 := by
  -- an even harmonic pair seeing `W`
  set Mb : ℕ → ℝ → ℝ := fun n x =>
    riemannKernelReal x * translateSpan Finset.univ (evenNullCoeff n) (evenNullShift n) x
    with hMb_def
  set S : ℕ → Set ℝ := fun n => {x | 0 < W x ∧ Mb n x ≠ 0} with hS_def
  have hcover : {x | 0 < W x} ⊆ ⋃ n, S n := fun x hx => by
    obtain ⟨n, hn⟩ := exists_nat_evenNull_ne_zero x
    exact mem_iUnion.mpr ⟨n, hx, hn⟩
  obtain ⟨n, R, hpos⟩ : ∃ n : ℕ, ∃ R : ℕ, 0 < volume (S n ∩ Icc (-(R : ℝ)) R) := by
    by_contra hcon
    simp only [not_exists, not_lt] at hcon
    have hnull : volume (⋃ n, S n) = 0 := by
      refine measure_iUnion_null fun n => ?_
      have hU : S n = ⋃ R : ℕ, S n ∩ Icc (-(R : ℝ)) R := by
        ext x
        simp only [mem_iUnion, mem_inter_iff, mem_Icc]
        constructor
        · intro hx
          obtain ⟨R, hR⟩ := exists_nat_ge |x|
          exact ⟨R, hx, by linarith [neg_abs_le x], by linarith [le_abs_self x]⟩
        · rintro ⟨_, hx, _⟩
          exact hx
      rw [hU]
      exact measure_iUnion_null fun R => nonpos_iff_eq_zero.mp (hcon n R)
    exact absurd (measure_mono_null hcover hnull) hWpos.ne'
  set α := evenNullCoeff (n : ℝ)
  set β := evenNullShift (n : ℝ)
  set M := Mb n with hM
  have hMc : Continuous M :=
    continuous_riemannKernelReal.mul (contDiff_translateSpan Finset.univ α β).continuous
  have hIcc : IntegrableOn (fun x => W x * M x ^ 2) (Icc (-(R : ℝ)) R) :=
    (hWi.integrableOn_isCompact isCompact_Icc).mul_continuousOn (hMc.pow 2).continuousOn
      isCompact_Icc
  have hc₀ : 0 < ∫ x in Icc (-(R : ℝ)) R, W x * M x ^ 2 := by
    rw [setIntegral_pos_iff_support_of_nonneg_ae
      (ae_of_all _ fun x => mul_nonneg (hW0 x) (sq_nonneg _)) hIcc]
    refine lt_of_lt_of_le hpos (measure_mono fun x hx => ⟨?_, hx.2⟩)
    exact mul_ne_zero hx.1.1.ne' (pow_ne_zero 2 hx.1.2)
  -- the normaliser `h = Φ u_0` and the null sequence `Φ(ω u_L) − ε_L h`
  set h : ℝ → ℝ := phiDoobTest (smoothPlateau 0) with hh
  have hhpos := evenPoleMoment_phiDoob_smoothPlateau_zero_pos
  set ε : ℝ → ℝ := fun L =>
    evenPoleMoment (phiDoobTest (fun y => translateSpan Finset.univ α β y * smoothPlateau L y)) /
      evenPoleMoment h with hε
  have hA := translateCoshCoefficient_evenNull (n : ℝ)
  have hB := translateSinhCoefficient_evenNull (n : ℝ)
  have hεlim : Tendsto ε atTop (𝓝 0) := by
    have h1 := (translateSpan_mul_smoothPlateau_moments Finset.univ α β).2
    rw [hA, zero_div] at h1
    simpa [hε] using h1.div_const (evenPoleMoment h)
  -- energies along the sequence
  obtain ⟨K, -, hK⟩ := exists_abs_markovEnergy_translatePlateau_sub_le Finset.univ α β
  rw [hA, hB] at hK
  have hQN : Tendsto (fun L => markovEnergy (fun x =>
      (phiDoobTest (fun y => translateSpan Finset.univ α β y * smoothPlateau L y) x : ℂ))) atTop
      (𝓝 0) := tendsto_of_abs_sub_le (Eventually.of_forall fun L => by simpa using hK L)
  have hu0 : ContDiff ℝ 2 (smoothPlateau 0) := contDiff_smoothPlateau 0
  have hu0c : HasCompactSupport (smoothPlateau 0) := hasCompactSupport_smoothPlateau 0
  -- the pairing with the normaliser tends to the source pairing, which is zero
  obtain ⟨C, hC0, hC⟩ := exists_abs_riemannKernelReal_mul_translateSpan_le Finset.univ α β
  obtain ⟨Λ, hΛ0, hΛ⟩ := exists_smoothPlateau_lipschitz
  obtain ⟨R₀, -, hsupp₀⟩ := exists_support_radius hu0c
  have hsrc0 : ∀ x, translateSource Finset.univ α β x = 0 := fun x => by
    unfold translateSource
    rw [hA, hB]
    ring
  have hP : Tendsto (fun L => ∫ x, smoothPlateau 0 x * (twoSidedGenerator
      (fun y => translateSpan Finset.univ α β y * smoothPlateau L y) x - riemannKernelReal x *
        Real.cosh (x / 2) * (translateSpan Finset.univ α β x * smoothPlateau L x))) atTop (𝓝 0) := by
    have hval : (∫ x, smoothPlateau 0 x * (riemannKernelReal x *
        translateSource Finset.univ α β x)) = 0 := by
      simp [hsrc0]
    suffices hs : Tendsto (fun L => ∫ x, smoothPlateau 0 x * (twoSidedGenerator
        (fun y => translateSpan Finset.univ α β y * smoothPlateau L y) x - riemannKernelReal x *
          Real.cosh (x / 2) * (translateSpan Finset.univ α β x * smoothPlateau L x))) atTop
        (𝓝 (∫ x, smoothPlateau 0 x * (riemannKernelReal x * translateSource Finset.univ α β x))) by
      rwa [hval] at hs
    refine tendsto_of_abs_sub_le (K := riemannKernelReal 0 * C * (2 * Λ * archFirstMoment +
      2 * Real.exp (8 * R₀) * primeEighthMoment) * (∫ x, |smoothPlateau 0 x|)) ?_
    filter_upwards [eventually_ge_atTop R₀] with L hRL
    exact abs_integral_mul_generator_plateau_sub_le (contDiff_translateSpan _ _ _) hC0 hC hΛ0 hΛ
      (integrableOn_archLevy_twoSidedShiftGenerator_translateSpan Finset.univ α β)
      (summable_atom_twoSidedShiftGenerator_translateSpan Finset.univ α β)
      (twoSidedGenerator_translateSpan_sub_potential Finset.univ α β)
      (continuous_translateSource Finset.univ α β) hu0 hu0c hsupp₀ hRL
  -- the test on the hyperplane
  set G : ℝ → ℝ → ℝ := fun L y =>
    translateSpan Finset.univ α β y * smoothPlateau L y + (-ε L) * smoothPlateau 0 y with hG
  have hGd : ∀ L, ContDiff ℝ 2 (G L) := fun L =>
    ((contDiff_translateSpan _ _ _).mul (contDiff_smoothPlateau L)).add (contDiff_const.mul hu0)
  have hGc : ∀ L, HasCompactSupport (G L) := fun L =>
    ((hasCompactSupport_smoothPlateau L).mul_left).add hu0c.mul_left
  set P : ℝ → ℝ := fun L => ∫ x, smoothPlateau 0 x * (twoSidedGenerator
      (fun y => translateSpan Finset.univ α β y * smoothPlateau L y) x - riemannKernelReal x *
        Real.cosh (x / 2) * (translateSpan Finset.univ α β x * smoothPlateau L x)) with hPdef
  have hQG : ∀ L, markovEnergy (fun x => (phiDoobTest (G L) x : ℂ)) =
      markovEnergy (fun x => (phiDoobTest
        (fun y => translateSpan Finset.univ α β y * smoothPlateau L y) x : ℂ)) +
        ε L ^ 2 * markovEnergy (fun x => (phiDoobTest (smoothPlateau 0) x : ℂ)) +
        2 * (-ε L * P L) := fun L => by
    have hz : ContDiff ℝ 2 fun y => translateSpan Finset.univ α β y * smoothPlateau L y :=
      (contDiff_translateSpan _ _ _).mul (contDiff_smoothPlateau L)
    have hzc : HasCompactSupport fun y => translateSpan Finset.univ α β y * smoothPlateau L y :=
      (hasCompactSupport_smoothPlateau L).mul_left
    have hcross : (∫ x, (-ε L * smoothPlateau 0 x) * (twoSidedGenerator
        (fun y => translateSpan Finset.univ α β y * smoothPlateau L y) x - riemannKernelReal x *
          Real.cosh (x / 2) * (translateSpan Finset.univ α β x * smoothPlateau L x))) =
        -ε L * P L := by
      rw [hPdef, ← integral_const_mul]
      exact integral_congr_ae (Eventually.of_forall fun x => by ring)
    rw [show G L = fun y => (translateSpan Finset.univ α β y * smoothPlateau L y) +
      (-ε L) * smoothPlateau 0 y from rfl, markovEnergy_phiDoob_add hz hzc
        (contDiff_const.mul hu0) hu0c.mul_left, markovEnergy_phiDoob_const_mul hu0 hu0c,
      neg_sq, hcross]
  have hQGlim : Tendsto (fun L => markovEnergy (fun x => (phiDoobTest (G L) x : ℂ))) atTop
      (𝓝 0) := by
    simp_rw [hQG]
    have hc : Tendsto (fun _ : ℝ => markovEnergy (fun x => (phiDoobTest (smoothPlateau 0) x : ℂ)))
        atTop (𝓝 (markovEnergy (fun x => (phiDoobTest (smoothPlateau 0) x : ℂ)))) :=
      tendsto_const_nhds
    have := (hQN.add ((hεlim.pow 2).mul hc)).add (((hεlim.neg).mul hP).const_mul 2)
    simpa using this
  -- the hyperplane condition
  have hcosh : ∀ L, (∫ x, phiDoobTest (G L) x * Real.cosh (x / 2)) = 0 := fun L => by
    have hm := evenPoleMoment_add
      (F := phiDoobTest fun y => translateSpan Finset.univ α β y * smoothPlateau L y)
      (G := phiDoobTest fun y => (-ε L) * smoothPlateau 0 y)
      (continuous_riemannKernelReal.mul ((contDiff_translateSpan _ _ _).continuous.mul
        (contDiff_smoothPlateau L).continuous))
      (hasCompactSupport_phiDoobTest (hasCompactSupport_smoothPlateau L).mul_left)
      (continuous_riemannKernelReal.mul (continuous_const.mul hu0.continuous))
      (hasCompactSupport_phiDoobTest hu0c.mul_left)
    have hlin : evenPoleMoment (phiDoobTest fun y => (-ε L) * smoothPlateau 0 y) =
        -ε L * evenPoleMoment h := by
      rw [hh]
      unfold evenPoleMoment phiDoobTest
      rw [← integral_const_mul]
      exact integral_congr_ae (Eventually.of_forall fun x => by ring)
    have hne : evenPoleMoment h ≠ 0 := hhpos.ne'
    have := hm
    rw [← phiDoobTest_add'] at this
    change evenPoleMoment (phiDoobTest (G L)) = 0
    rw [show phiDoobTest (G L) = phiDoobTest (fun y => translateSpan Finset.univ α β y *
      smoothPlateau L y + (-ε L) * smoothPlateau 0 y) from rfl, this, hlin, hε]
    field_simp
    ring
  -- the weighted mass
  have hWint : ∀ {f : ℝ → ℝ}, Continuous f → HasCompactSupport f →
      Integrable fun x => W x * f x ^ 2 := by
    intro f hf hfc
    obtain ⟨R', -, hR'⟩ := exists_support_radius hfc
    have hsupp : Function.support (fun x => W x * f x ^ 2) ⊆ Icc (-R') R' := by
      intro x hx
      by_contra hout
      apply hx
      have h1 : R' < |x| := by
        rw [mem_Icc, not_and_or, not_le, not_le] at hout
        rcases hout with h | h
        · linarith [neg_abs_le x]
        · linarith [le_abs_self x]
      simp [hR' x h1]
    exact (integrableOn_iff_integrable_of_support_subset hsupp).mp
      ((hWi.integrableOn_isCompact isCompact_Icc).mul_continuousOn (hf.pow 2).continuousOn
        isCompact_Icc)
  set Kh := ∫ x, W x * h x ^ 2 with hKh
  have hmass : ∀ L, (R : ℝ) ≤ L → (1 / 2) * (∫ x in Icc (-(R : ℝ)) R, W x * M x ^ 2) -
      ε L ^ 2 * Kh ≤ ∫ x, W x * phiDoobTest (G L) x ^ 2 := fun L hRL => by
    have hu := (contDiff_smoothPlateau L).continuous
    have hMu : Continuous fun x => M x * smoothPlateau L x := hMc.mul hu
    have hMuc : HasCompactSupport fun x => M x * smoothPlateau L x :=
      (hasCompactSupport_smoothPlateau L).mul_left
    have hhc : Continuous h := continuous_riemannKernelReal.mul hu0.continuous
    have hhcs : HasCompactSupport h := hasCompactSupport_phiDoobTest hu0c
    have hGeq : ∀ x, phiDoobTest (G L) x = M x * smoothPlateau L x + -ε L * h x := fun x => by
      simp only [hG, phiDoobTest, hM, hMb_def, hh]
      ring
    have hGcont : Continuous (phiDoobTest (G L)) :=
      continuous_riemannKernelReal.mul (hGd L).continuous
    have hGcs : HasCompactSupport (phiDoobTest (G L)) := hasCompactSupport_phiDoobTest (hGc L)
    have i1 := hWint hMu hMuc
    have i2 := hWint hhc hhcs
    have i3 := hWint hGcont hGcs
    have hlow : (1 / 2) * (∫ x, W x * (M x * smoothPlateau L x) ^ 2) - ε L ^ 2 * Kh ≤
        ∫ x, W x * phiDoobTest (G L) x ^ 2 := by
      rw [hKh, ← integral_const_mul, ← integral_const_mul, ← integral_sub (i1.const_mul _)
        (i2.const_mul _)]
      refine integral_mono ((i1.const_mul _).sub (i2.const_mul _)) i3 fun x => ?_
      simp only
      rw [hGeq]
      have hW := hW0 x
      nlinarith [mul_nonneg hW (sq_nonneg (M x * smoothPlateau L x / 2 + -ε L * h x))]
    have hR : (∫ x in Icc (-(R : ℝ)) R, W x * M x ^ 2) ≤
        ∫ x, W x * (M x * smoothPlateau L x) ^ 2 := by
      calc (∫ x in Icc (-(R : ℝ)) R, W x * M x ^ 2)
          = ∫ x in Icc (-(R : ℝ)) R, W x * (M x * smoothPlateau L x) ^ 2 := by
            refine setIntegral_congr_fun measurableSet_Icc fun x hx => ?_
            have hxL : |x| ≤ L := (abs_le.mpr ⟨hx.1, hx.2⟩).trans hRL
            simp only [smoothPlateau_eq_one hxL, mul_one]
        _ ≤ _ := setIntegral_le_integral i1
            (ae_of_all _ fun x => mul_nonneg (hW0 x) (sq_nonneg _))
    linarith
  -- choose `L`
  set c₀ := ∫ x in Icc (-(R : ℝ)) R, W x * M x ^ 2
  have hKh0 : 0 ≤ Kh := integral_nonneg fun x => mul_nonneg (hW0 x) (sq_nonneg _)
  have hev1 : ∀ᶠ L in atTop, markovEnergy (fun x => (phiDoobTest (G L) x : ℂ)) < c₀ / 4 :=
    hQGlim.eventually (gt_mem_nhds (by linarith))
  have hev2 : ∀ᶠ L in atTop, ε L ^ 2 * Kh < c₀ / 4 := by
    have := ((hεlim.pow 2).mul_const Kh)
    rw [zero_pow two_ne_zero, zero_mul] at this
    exact this.eventually (gt_mem_nhds (by linarith))
  obtain ⟨L, hL1, hL2, hL3⟩ := (hev1.and (hev2.and (eventually_ge_atTop (R : ℝ)))).exists
  refine ⟨phiDoobTest (G L), contDiff_phiDoobTest (hGd L), hasCompactSupport_phiDoobTest (hGc L),
    hcosh L, ?_⟩
  have := hmass L hL3
  linarith

/-- **RH is criticality on the primitive hyperplane.** RH holds iff the Markov form is
nonnegative on the primitive hyperplane and admits no Hardy weight there; the second condition
holds unconditionally. -/
theorem riemannHypothesis_iff_primitive_nonneg_and_no_hardyWeight :
    RiemannHypothesis ↔
      (∀ F : ℝ → ℝ, ContDiff ℝ 2 F → HasCompactSupport F → (∫ x, F x * Real.cosh (x / 2)) = 0 →
          0 ≤ markovEnergy (fun x => (F x : ℂ))) ∧
        ∀ W : ℝ → ℝ, (∀ x, 0 ≤ W x) → LocallyIntegrable W → 0 < volume {x | 0 < W x} →
          ¬ ∀ F : ℝ → ℝ, ContDiff ℝ 2 F → HasCompactSupport F →
            (∫ x, F x * Real.cosh (x / 2)) = 0 →
              (∫ x, W x * F x ^ 2) ≤ markovEnergy (fun x => (F x : ℂ)) := by
  rw [← riemannHypothesis_iff_forall_cosh_moment_zero_markovEnergy_nonneg]
  refine ⟨fun hRH => ⟨hRH, fun W hW0 hWi hWpos hHardy => ?_⟩, fun h => h.1⟩
  obtain ⟨F, hF, hFc, hcosh, hlt⟩ := exists_primitive_markovEnergy_lt_integral_weight_mul_sq hW0 hWi hWpos
  exact absurd (hHardy F hF hFc hcosh) (not_le.mpr hlt)

end GaloisForLFunctions.ArithmeticCriticalityTheory

end
