import GaloisForLFunctions.RHTower.CHMDExactDivisorPackets

/-!
# Exact nullspace of the CHMD arithmetic polarization

The real polarization of the actual prime--archimedean energy has radical
exactly the admissible multipliers that vanish on every actual Xi divisor point.
The converse is proved by explicit pole-free evaluation duals: the full-order
cardinal quotient realizes conjugate divisor values on one reflection orbit.
Every mixed summand is then a nonnegative norm square, and the selected summand
is positive whenever the selected value is nonzero. Orbit collisions and
analytic multiplicities are retained throughout.

Consequently all arithmetic responses distinguish precisely the divisor values,
and the radical is power-saturated. Higher analytic multiplicity does not create
additional invisible multiplier values or nilpotent classes modulo this radical.

No RH, simplicity, or positivity premise enters these results. Positivity of the
evaluation-dual pairing is not positivity of the diagonal Weil form; neither
off-line exclusion nor an unconditional RH proof is asserted.
-/

open Complex MeasureTheory Set Filter Topology Zeta23
open scoped BigOperators ComplexConjugate

noncomputable section
namespace RHTower.CHMDArithmeticRadical
open WeilSpectral EvenSector CHMDStage3 CHMDStage15 CHMDStage16 CHMDExactPackets

theorem multiplier_add {F G : ℂ → ℂ} (hF : Multiplier F) (hG : Multiplier G) :
    Multiplier (fun z => F z + G z) := by
  obtain ⟨ε, C, hε, hs⟩ := hF.strip
  obtain ⟨δ, D, hδ, ht⟩ := hG.strip
  have hC := hs.const_nonneg (by norm_num : (0 : ℝ) ≤ 9 / 4)
  have hD := ht.const_nonneg (by norm_num : (0 : ℝ) ≤ 9 / 4)
  refine ⟨⟨min ε δ, C + D, lt_min hε hδ, ⟨fun z hz =>
    (hs.diff z hz).add (ht.diff z hz), fun z hz => ?_⟩⟩,
    fun z => by simp only [hF.even, hG.even],
    fun z => by simp only [hF.conj_symm, hG.conj_symm, map_add]⟩
  have he : Real.exp (-(ε * |z.re|)) ≤ Real.exp (-(min ε δ * |z.re|)) := by
    apply Real.exp_le_exp.mpr
    nlinarith [min_le_left ε δ, abs_nonneg z.re]
  have hd : Real.exp (-(δ * |z.re|)) ≤ Real.exp (-(min ε δ * |z.re|)) := by
    apply Real.exp_le_exp.mpr
    nlinarith [min_le_right ε δ, abs_nonneg z.re]
  calc ‖F z + G z‖ ≤ ‖F z‖ + ‖G z‖ := norm_add_le _ _
    _ ≤ C * Real.exp (-(ε * |z.re|)) + D * Real.exp (-(δ * |z.re|)) :=
      add_le_add (hs.bound z hz) (ht.bound z hz)
    _ ≤ C * Real.exp (-(min ε δ * |z.re|)) +
        D * Real.exp (-(min ε δ * |z.re|)) :=
      add_le_add (mul_le_mul_of_nonneg_left he hC) (mul_le_mul_of_nonneg_left hd hD)
    _ = _ := by ring

theorem multiplier_mul {F G : ℂ → ℂ} (hF : Multiplier F) (hG : Multiplier G) :
    Multiplier (fun z => F z * G z) := by
  obtain ⟨ε, C, hε, hs⟩ := hF.strip
  obtain ⟨δ, D, hδ, ht⟩ := hG.strip
  refine ⟨⟨ε + δ, C * D, add_pos hε hδ, ⟨fun z hz =>
    (hs.diff z hz).mul (ht.diff z hz), fun z hz => ?_⟩⟩,
    fun z => by simp only [hF.even, hG.even],
    fun z => by simp only [hF.conj_symm, hG.conj_symm, map_mul]⟩
  rw [norm_mul]
  calc ‖F z‖ * ‖G z‖ ≤
      (C * Real.exp (-(ε * |z.re|))) * (D * Real.exp (-(δ * |z.re|))) :=
      mul_le_mul (hs.bound z hz) (ht.bound z hz) (norm_nonneg _)
        ((norm_nonneg _).trans (hs.bound z hz))
    _ = _ := by
      rw [show -((ε + δ) * |z.re|) = -(ε * |z.re|) + -(δ * |z.re|) by ring, Real.exp_add]
      ring

theorem multiplier_neg {F : ℂ → ℂ} (hF : Multiplier F) :
    Multiplier (fun z => -F z) := by
  obtain ⟨ε, C, hε, hs⟩ := hF.strip
  exact ⟨⟨ε, C, hε, ⟨fun z hz => (hs.diff z hz).neg,
    fun z hz => by simpa only [norm_neg] using hs.bound z hz⟩⟩,
    fun z => by rw [hF.even], fun z => by rw [hF.conj_symm, map_neg]⟩

theorem multiplier_sub {F G : ℂ → ℂ} (hF : Multiplier F) (hG : Multiplier G) :
    Multiplier (fun z => F z - G z) := by
  simpa only [sub_eq_add_neg] using multiplier_add hF (multiplier_neg hG)

theorem multiplier_pow_succ {F : ℂ → ℂ} (hF : Multiplier F) (n : ℕ) :
    Multiplier (fun z => F z ^ (n + 1)) := by
  induction n with
  | zero => simpa only [zero_add, pow_one] using hF
  | succ n ih => simpa only [pow_succ] using multiplier_mul ih hF

/-- Actual arithmetic energy, before invoking the zero-side formula. -/
def energy (F : ℂ → ℂ) : ℝ := evenWeilDensity ArithmeticFunction.vonMangoldt (specSq F)

/-- Real polarization of the actual prime--archimedean energy. -/
def sourcePair (F G : ℂ → ℂ) : ℝ :=
  (energy (fun z => F z + G z) - energy F - energy G) / 2

theorem specSq_eq_sq {F : ℂ → ℂ} (hF : Multiplier F) (z : ℂ) :
    specSq F z = F z ^ 2 := by
  rw [specSq, hF.conj_symm, conj_conj, sq]

theorem mixed_summand {F G : ℂ → ℂ} (hF : Multiplier F) (hG : Multiplier G)
    (ρ : zetaZeroConfig.carrier) :
    (zetaZeroConfig.mult ρ : ℝ) * (F (gammaOf ρ) * G (gammaOf ρ)).re =
      ((zetaZeroConfig.mult ρ : ℝ) * (specSq (fun z => F z + G z) (gammaOf ρ)).re -
        (zetaZeroConfig.mult ρ : ℝ) * (specSq F (gammaOf ρ)).re -
        (zetaZeroConfig.mult ρ : ℝ) * (specSq G (gammaOf ρ)).re) / 2 := by
  rw [specSq_eq_sq (multiplier_add hF hG), specSq_eq_sq hF, specSq_eq_sq hG]
  simp only [sq, Complex.mul_re, Complex.add_re, Complex.add_im]
  ring

theorem summable_sourcePair {F G : ℂ → ℂ} (hF : Multiplier F) (hG : Multiplier G) :
    Summable fun ρ : zetaZeroConfig.carrier =>
      (zetaZeroConfig.mult ρ : ℝ) * (F (gammaOf ρ) * G (gammaOf ρ)).re := by
  have hA := summable_re_zeroSide_of_goodDensity
    (goodDensity_specSq (multiplier_add hF hG).evenStrip)
  have hB := summable_re_zeroSide_of_goodDensity (goodDensity_specSq hF.evenStrip)
  have hC := summable_re_zeroSide_of_goodDensity (goodDensity_specSq hG.evenStrip)
  exact (((hA.sub hB).sub hC).div_const 2).congr fun ρ => (mixed_summand hF hG ρ).symm

theorem sourcePair_eq_tsum {F G : ℂ → ℂ} (hF : Multiplier F) (hG : Multiplier G) :
    sourcePair F G = ∑' ρ : zetaZeroConfig.carrier,
      (zetaZeroConfig.mult ρ : ℝ) * (F (gammaOf ρ) * G (gammaOf ρ)).re := by
  have hA := summable_re_zeroSide_of_goodDensity
    (goodDensity_specSq (multiplier_add hF hG).evenStrip)
  have hB := summable_re_zeroSide_of_goodDensity (goodDensity_specSq hF.evenStrip)
  have hC := summable_re_zeroSide_of_goodDensity (goodDensity_specSq hG.evenStrip)
  simp_rw [mixed_summand hF hG]
  rw [tsum_div_const, (hA.sub hB).tsum_sub hC, hA.tsum_sub hB]
  rw [sourcePair, energy, energy, energy,
    evenWeilDensity_specSq_vonMangoldt_eq_tsum_re (multiplier_add hF hG).evenStrip,
    evenWeilDensity_specSq_vonMangoldt_eq_tsum_re hF.evenStrip,
    evenWeilDensity_specSq_vonMangoldt_eq_tsum_re hG.evenStrip]

/-- The polarization is the literal arithmetic functional on the mixed density. -/
theorem sourcePair_eq_density {F G : ℂ → ℂ} (hF : Multiplier F) (hG : Multiplier G) :
    sourcePair F G = evenWeilDensity ArithmeticFunction.vonMangoldt (fun z => F z * G z) := by
  let K : Fin 3 → ℂ → ℂ := ![specSq (fun z => F z + G z), specSq F, specSq G]
  let c : Fin 3 → ℝ := ![1 / 2, -1 / 2, -1 / 2]
  have hK : ∀ i ∈ (Finset.univ : Finset (Fin 3)), GoodDensity (K i) := by
    intro i hi
    fin_cases i
    · exact goodDensity_specSq (multiplier_add hF hG).evenStrip
    · exact goodDensity_specSq hF.evenStrip
    · exact goodDensity_specSq hG.evenStrip
  have he : (fun z => ∑ i ∈ (Finset.univ : Finset (Fin 3)), (c i : ℂ) * K i z) =
      fun z => F z * G z := by
    funext z
    simp [c, K, Fin.sum_univ_three, specSq_eq_sq hF, specSq_eq_sq hG,
      specSq_eq_sq (multiplier_add hF hG)]
    ring
  have hl := evenWeilDensity_sum abs_vonMangoldt_le_sqrt_mul_one_add_log
    (Finset.univ : Finset (Fin 3)) c hK
  rw [he] at hl
  simp [c, K, Fin.sum_univ_three] at hl
  unfold sourcePair energy
  linarith

theorem sourcePair_sub_left {F G H : ℂ → ℂ}
    (hF : Multiplier F) (hG : Multiplier G) (hH : Multiplier H) :
    sourcePair (fun z => F z - G z) H = sourcePair F H - sourcePair G H := by
  rw [sourcePair_eq_tsum (multiplier_sub hF hG) hH, sourcePair_eq_tsum hF hH,
    sourcePair_eq_tsum hG hH, ← (summable_sourcePair hF hH).tsum_sub (summable_sourcePair hG hH)]
  apply tsum_congr
  intro ρ
  simp only [sub_mul, Complex.sub_re, mul_sub]

/-- Orbit incidence, retaining the double incidences on the critical line. -/
def orbitCount (a z : ℂ) : ℝ :=
  (if z = a then 1 else 0) + (if -z = a then 1 else 0) +
    (if conj z = a then 1 else 0) + (if -conj z = a then 1 else 0)

theorem orbitCount_nonneg (a z : ℂ) : 0 ≤ orbitCount a z := by
  unfold orbitCount
  positivity

theorem orbitCount_self_pos (a : ℂ) : 0 < orbitCount a a := by
  unfold orbitCount
  simp only [ite_true]
  positivity

/-- A pole-free evaluation dual, built from the full-multiplicity cardinal quotient. -/
def evaluationDual (ρ : zetaZeroConfig.carrier) (F : ℂ → ℂ) (z : ℂ) : ℂ :=
  conj (F (gammaOf ρ)) * (cardinal (zeroSupport ρ) z + cardinal (zeroSupport ρ) (-z)) +
    conj (conj (F (gammaOf ρ)) *
      (cardinal (zeroSupport ρ) (conj z) + cardinal (zeroSupport ρ) (-conj z)))

theorem evaluationDual_even (ρ : zetaZeroConfig.carrier) (F : ℂ → ℂ) (z : ℂ) :
    evaluationDual ρ F (-z) = evaluationDual ρ F z := by
  simp only [evaluationDual, neg_neg, map_neg, add_comm]

theorem evaluationDual_conj (ρ : zetaZeroConfig.carrier) (F : ℂ → ℂ) (z : ℂ) :
    evaluationDual ρ F (conj z) = conj (evaluationDual ρ F z) := by
  simp only [evaluationDual, map_add, conj_conj]
  ring

theorem evaluationDual_strip (ρ : zetaZeroConfig.carrier) (F : ℂ → ℂ) :
    ∃ C : ℝ, StripDecay (evaluationDual ρ F) (9 / 4) (3 / 4) C := by
  obtain ⟨C, hs⟩ := cardinal_strip (zeroSupport ρ)
  refine ⟨4 * ‖F (gammaOf ρ)‖ * C, ⟨fun z hz => ?_, fun z hz => ?_⟩⟩
  · have h1 := ((hs.diff z hz).add
      ((hs.diff (-z) (by simpa using hz)).comp z differentiableAt_id.neg)).const_mul
        (conj (F (gammaOf ρ)))
    have h2 := ((hs.diff (conj z) (by simpa using hz)).add
      ((hs.diff (-conj z) (by simpa using hz)).comp (conj z) differentiableAt_id.neg)).const_mul
        (conj (F (gammaOf ρ)))
    have h3 : DifferentiableAt ℂ
        (fun w => conj (conj (F (gammaOf ρ)) *
          (cardinal (zeroSupport ρ) (conj w) + cardinal (zeroSupport ρ) (-conj w)))) z := by
      simpa only [Function.comp_def, conj_conj, Pi.add_apply] using h2.conj_conj
    exact h1.add h3
  · have h1 := hs.bound z hz
    have h2 := hs.bound (-z) (by simpa using hz)
    have h3 := hs.bound (conj z) (by simpa using hz)
    have h4 := hs.bound (-conj z) (by simpa using hz)
    simp only [Complex.neg_re, Complex.conj_re, abs_neg] at h2 h3 h4
    calc ‖evaluationDual ρ F z‖ ≤
        ‖conj (F (gammaOf ρ)) * (cardinal (zeroSupport ρ) z + cardinal (zeroSupport ρ) (-z))‖ +
        ‖conj (conj (F (gammaOf ρ)) *
          (cardinal (zeroSupport ρ) (conj z) + cardinal (zeroSupport ρ) (-conj z)))‖ := norm_add_le _ _
      _ ≤ ‖F (gammaOf ρ)‖ * (‖cardinal (zeroSupport ρ) z‖ + ‖cardinal (zeroSupport ρ) (-z)‖) +
          ‖F (gammaOf ρ)‖ * (‖cardinal (zeroSupport ρ) (conj z)‖ +
            ‖cardinal (zeroSupport ρ) (-conj z)‖) := by
        simp only [norm_mul, norm_conj]
        gcongr <;> exact norm_add_le _ _
      _ ≤ ‖F (gammaOf ρ)‖ * (C * Real.exp (-(3 / 4 * |z.re|)) +
          C * Real.exp (-(3 / 4 * |z.re|))) +
          ‖F (gammaOf ρ)‖ * (C * Real.exp (-(3 / 4 * |z.re|)) +
          C * Real.exp (-(3 / 4 * |z.re|))) := by gcongr
      _ = _ := by ring

theorem evaluationDual_multiplier (ρ : zetaZeroConfig.carrier) (F : ℂ → ℂ) :
    Multiplier (evaluationDual ρ F) := by
  obtain ⟨C, hs⟩ := evaluationDual_strip ρ F
  exact ⟨⟨3 / 4, C, by norm_num, hs⟩, evaluationDual_even ρ F, evaluationDual_conj ρ F⟩

theorem evaluationDual_pole_zero (ρ : zetaZeroConfig.carrier) (F : ℂ → ℂ) :
    evaluationDual ρ F (I / 2) = 0 ∧ evaluationDual ρ F (-I / 2) = 0 := by
  have hu : evaluationDual ρ F (I / 2) = 0 := by
    have hc : conj (I / 2 : ℂ) = -I / 2 := by simp only [map_div₀, conj_I, map_ofNat]
    have hn : -(I / 2 : ℂ) = -I / 2 := by ring
    have hnn : -(-I / 2 : ℂ) = I / 2 := by ring
    simp [evaluationDual, hc, hn, hnn]
  exact ⟨hu, by rw [show (-I / 2 : ℂ) = -(I / 2) by ring, evaluationDual_even, hu]⟩

/-- The dual realizes conjugate evaluation, with every orbit incidence retained. -/
theorem evaluationDual_eval {F : ℂ → ℂ} (hF : Multiplier F)
    (ρ σ : zetaZeroConfig.carrier) :
    evaluationDual ρ F (gammaOf σ) =
      conj (F (gammaOf σ)) * (orbitCount (gammaOf ρ) (gammaOf σ) : ℂ) := by
  let a := gammaOf ρ
  let z := gammaOf σ
  have ha : |(xiSpectralPointSupport (zeroSupport ρ)).im| < 1 / 2 := by
    rw [zeroSupport_coordinate]
    exact CHMDGrowthCollapse.abs_im_gammaOf_lt ρ
  have hz : XiC z = 0 := XiC_gammaOf_eq_zero σ
  have hn : XiC (-z) = 0 := by rw [XiC_even, hz]
  have hc : XiC (conj z) = 0 := by rw [XiC_conj, hz, map_zero]
  have hnc : XiC (-conj z) = 0 := by rw [XiC_even, hc]
  have h₁ : conj (F a) * cardinal (zeroSupport ρ) z =
      conj (F z) * (if z = a then 1 else 0) := by
    rw [cardinal_eval _ ha hz, zeroSupport_coordinate]
    change conj (F a) * (if z = a then 1 else 0) = _
    split_ifs with h <;> simp [h]
  have h₂ : conj (F a) * cardinal (zeroSupport ρ) (-z) =
      conj (F z) * (if -z = a then 1 else 0) := by
    rw [cardinal_eval _ ha hn, zeroSupport_coordinate]
    change conj (F a) * (if -z = a then 1 else 0) = _
    split_ifs with h
    · rw [← h, hF.even]
    · simp
  have h₃ : conj (conj (F a) * cardinal (zeroSupport ρ) (conj z)) =
      conj (F z) * (if conj z = a then 1 else 0) := by
    rw [cardinal_eval _ ha hc, zeroSupport_coordinate]
    change conj (conj (F a) * (if conj z = a then 1 else 0)) = _
    split_ifs with h
    · simp [← h, hF.conj_symm]
    · simp
  have h₄ : conj (conj (F a) * cardinal (zeroSupport ρ) (-conj z)) =
      conj (F z) * (if -conj z = a then 1 else 0) := by
    rw [cardinal_eval _ ha hnc, zeroSupport_coordinate]
    change conj (conj (F a) * (if -conj z = a then 1 else 0)) = _
    split_ifs with h
    · simp [← h, hF.even, hF.conj_symm]
    · simp
  change conj (F a) * (cardinal (zeroSupport ρ) z + cardinal (zeroSupport ρ) (-z)) +
    conj (conj (F a) * (cardinal (zeroSupport ρ) (conj z) +
      cardinal (zeroSupport ρ) (-conj z))) = _
  rw [mul_add, mul_add, map_add, h₁, h₂, h₃, h₄]
  simp only [orbitCount, Complex.ofReal_add, apply_ite Complex.ofReal,
    Complex.ofReal_one, Complex.ofReal_zero]
  ring

/-- Exact positive source readout at a selected reflection orbit. -/
theorem sourcePair_evaluationDual {F : ℂ → ℂ} (hF : Multiplier F)
    (ρ : zetaZeroConfig.carrier) :
    sourcePair F (evaluationDual ρ F) = ∑' σ : zetaZeroConfig.carrier,
      (zetaZeroConfig.mult σ : ℝ) * Complex.normSq (F (gammaOf σ)) *
        orbitCount (gammaOf ρ) (gammaOf σ) := by
  rw [sourcePair_eq_tsum hF (evaluationDual_multiplier ρ F)]
  apply tsum_congr
  intro σ
  rw [evaluationDual_eval hF, ← mul_assoc, Complex.mul_conj, ← Complex.ofReal_mul,
    Complex.ofReal_re]
  ring

theorem summable_evaluationDual {F : ℂ → ℂ} (hF : Multiplier F)
    (ρ : zetaZeroConfig.carrier) :
    Summable fun σ : zetaZeroConfig.carrier =>
      (zetaZeroConfig.mult σ : ℝ) * Complex.normSq (F (gammaOf σ)) *
        orbitCount (gammaOf ρ) (gammaOf σ) := by
  refine (summable_sourcePair hF (evaluationDual_multiplier ρ F)).congr fun σ => ?_
  rw [evaluationDual_eval hF, ← mul_assoc, Complex.mul_conj, ← Complex.ofReal_mul,
    Complex.ofReal_re]
  ring

theorem sourcePair_evaluationDual_nonneg {F : ℂ → ℂ} (hF : Multiplier F)
    (ρ : zetaZeroConfig.carrier) : 0 ≤ sourcePair F (evaluationDual ρ F) := by
  rw [sourcePair_evaluationDual hF]
  exact tsum_nonneg fun σ => mul_nonneg
    (mul_nonneg (Nat.cast_nonneg _) (Complex.normSq_nonneg _)) (orbitCount_nonneg _ _)

theorem sourcePair_evaluationDual_pos {F : ℂ → ℂ} (hF : Multiplier F)
    (ρ : zetaZeroConfig.carrier) (hne : F (gammaOf ρ) ≠ 0) :
    0 < sourcePair F (evaluationDual ρ F) := by
  rw [sourcePair_evaluationDual hF]
  apply (summable_evaluationDual hF ρ).tsum_pos
    (fun σ => mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Complex.normSq_nonneg _))
      (orbitCount_nonneg _ _)) ρ
  have hm : (1 : ℝ) ≤ zetaZeroConfig.mult ρ := by
    exact_mod_cast zetaZeroConfig.one_le_mult _ ρ.2
  exact mul_pos (mul_pos (by linarith) (Complex.normSq_pos.mpr hne)) (orbitCount_self_pos _)

theorem sourcePair_evaluationDual_eq_zero_iff {F : ℂ → ℂ} (hF : Multiplier F)
    (ρ : zetaZeroConfig.carrier) :
    sourcePair F (evaluationDual ρ F) = 0 ↔ F (gammaOf ρ) = 0 := by
  constructor
  · intro h
    by_contra hne
    exact (sourcePair_evaluationDual_pos hF ρ hne).ne' h
  · intro h
    rw [sourcePair_eq_tsum hF (evaluationDual_multiplier ρ F)]
    simp [evaluationDual, h]

/-- The nullspace of all actual arithmetic pairings, without any positivity assumption. -/
def SourceRadical (F : ℂ → ℂ) : Prop :=
  ∀ G : ℂ → ℂ, Multiplier G → sourcePair F G = 0

/-- All, and only, divisor-vanishing multipliers are invisible to arithmetic polarization. -/
theorem sourceRadical_iff_divisor_zero {F : ℂ → ℂ} (hF : Multiplier F) :
    SourceRadical F ↔ ∀ ρ : zetaZeroConfig.carrier, F (gammaOf ρ) = 0 := by
  constructor
  · intro h ρ
    by_contra hne
    have hp := sourcePair_evaluationDual_pos hF ρ hne
    rw [h _ (evaluationDual_multiplier ρ F)] at hp
    exact lt_irrefl _ hp
  · intro h G hG
    rw [sourcePair_eq_tsum hF hG]
    simp only [h, zero_mul, Complex.zero_re, mul_zero, tsum_zero]

/-- Passing to a positive power cannot turn a visible multiplier into an invisible one. -/
theorem sourceRadical_pow_iff {F : ℂ → ℂ} (hF : Multiplier F) (n : ℕ) :
    SourceRadical (fun z => F z ^ (n + 1)) ↔ SourceRadical F := by
  rw [sourceRadical_iff_divisor_zero (multiplier_pow_succ hF n),
    sourceRadical_iff_divisor_zero hF]
  simp only [pow_eq_zero_iff (Nat.succ_ne_zero n)]

theorem sourceRadical_mul {F G : ℂ → ℂ} (hF : Multiplier F) (hG : Multiplier G)
    (h : SourceRadical F) : SourceRadical (fun z => F z * G z) := by
  rw [sourceRadical_iff_divisor_zero (multiplier_mul hF hG)]
  intro ρ
  rw [(sourceRadical_iff_divisor_zero hF).mp h ρ, zero_mul]

theorem sourceRadical_sub_iff {F G : ℂ → ℂ} (hF : Multiplier F) (hG : Multiplier G) :
    SourceRadical (fun z => F z - G z) ↔
      ∀ ρ : zetaZeroConfig.carrier, F (gammaOf ρ) = G (gammaOf ρ) := by
  rw [sourceRadical_iff_divisor_zero (multiplier_sub hF hG)]
  simp only [sub_eq_zero]

/-- Equality of all arithmetic responses detects equality of every divisor value. -/
theorem sourceResponses_eq_iff {F G : ℂ → ℂ} (hF : Multiplier F) (hG : Multiplier G) :
    (∀ H : ℂ → ℂ, Multiplier H → sourcePair F H = sourcePair G H) ↔
      ∀ ρ : zetaZeroConfig.carrier, F (gammaOf ρ) = G (gammaOf ρ) := by
  rw [← sourceRadical_sub_iff hF hG]
  unfold SourceRadical
  constructor <;> intro h H hH
  · rw [sourcePair_sub_left hF hG hH, h H hH, sub_self]
  · have he := h H hH
    rw [sourcePair_sub_left hF hG hH, sub_eq_zero] at he
    exact he

/-- The evaluation readout has no residual polar term on the arithmetic side. -/
theorem sourcePair_evaluationDual_prime_arch {F : ℂ → ℂ} (hF : Multiplier F)
    (ρ : zetaZeroConfig.carrier) :
    sourcePair F (evaluationDual ρ F) =
      (1 / (2 * Real.pi)) * evenArchPart (fun z => F z * evaluationDual ρ F z) -
        evenPrimePart ArithmeticFunction.vonMangoldt (fun z => F z * evaluationDual ρ F z) := by
  rw [sourcePair_eq_density hF (evaluationDual_multiplier ρ F), evenWeilDensity_eq_parts]
  have hp := evaluationDual_pole_zero ρ F
  simp only [evenPolePart, hp.1, hp.2, mul_zero, add_zero, Complex.zero_re, zero_add]

end RHTower.CHMDArithmeticRadical
