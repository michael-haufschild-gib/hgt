import GaloisForLFunctions.HTGeometry.HierarchicalResonanceBreaking

open Filter Finset PowerSeries Polynomial Topology

namespace GaloisForLFunctions

noncomputable section

/-- A fixed integer shift polynomial has a nonnegative logarithmic defect along a cofinal
subsequence. -/
def HasLogarithmicShiftDefectAlong
    (Q : Polynomial ℤ) (b : ℕ → ℝ) (C K : ℕ) (q : ℕ → ℕ) : Prop :=
  ∀ᶠ k in atTop,
    0 ≤ integerPolynomialShift Q b (q k) ∧
      integerPolynomialShift Q b (q k) <
        (C : ℝ) * Real.log (((q k + K : ℕ) : ℝ) + 2)

/-- Peeling one exact geometric layer from a logarithmically bounded shift defect forces the
shift polynomial to vanish at that layer's ratio. -/
theorem integerPolynomialRealEval_eq_zero_of_geometricLayer_defect
    {Q : Polynomial ℤ} {b h : ℕ → ℝ} {C K : ℕ} {q : ℕ → ℕ}
    {A lam : ℝ} (hA : A ≠ 0) (hlam1 : 1 < lam)
    (hb : b = fun n => A * lam ^ n + h n)
    (hh : h =o[atTop] fun n : ℕ => lam ^ n)
    (hq : Tendsto q atTop atTop)
    (hdefect : HasLogarithmicShiftDefectAlong Q b C K q) :
    integerPolynomialRealEval Q lam = 0 := by
  have hlam0 : 0 < lam := zero_lt_one.trans hlam1
  have hlog0 : Tendsto
      (fun k => Real.log (((q k : ℕ) : ℝ) + 2) / lam ^ q k)
      atTop (𝓝 0) :=
    (log_nat_add_two_isLittleO_const_pow hlam1).tendsto_div_nhds_zero.comp hq
  have hupper0 : Tendsto
      (fun k => (2 * (C : ℝ)) *
        (Real.log (((q k : ℕ) : ℝ) + 2) / lam ^ q k))
      atTop (𝓝 0) := by
    simpa using hlog0.const_mul (2 * (C : ℝ))
  have hnormalized0 : Tendsto
      (fun k => integerPolynomialShift Q b (q k) / lam ^ q k)
      atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds hupper0 ?_ ?_
    · filter_upwards [hdefect] with k hk
      exact div_nonneg hk.1 (pow_nonneg hlam0.le _)
    · filter_upwards [hdefect, hq.eventually_ge_atTop K] with k hk hkK
      have hlogle := log_nat_add_shift_le_two_mul_log (n := q k) (K := K) hkK
      have hnum : integerPolynomialShift Q b (q k) ≤
          2 * (C : ℝ) * Real.log (((q k : ℕ) : ℝ) + 2) := by
        calc
          integerPolynomialShift Q b (q k) ≤
              (C : ℝ) * Real.log ((((q k + K : ℕ) : ℝ)) + 2) := hk.2.le
          _ ≤ (C : ℝ) * (2 * Real.log (((q k : ℕ) : ℝ) + 2)) :=
            mul_le_mul_of_nonneg_left hlogle (Nat.cast_nonneg C)
          _ = 2 * (C : ℝ) * Real.log (((q k : ℕ) : ℝ) + 2) := by ring
      have hp : 0 < lam ^ q k := pow_pos hlam0 _
      rw [div_le_iff₀ hp]
      calc
        integerPolynomialShift Q b (q k) ≤
            2 * (C : ℝ) * Real.log (((q k : ℕ) : ℝ) + 2) := hnum
        _ = (2 * (C : ℝ) *
            (Real.log (((q k : ℕ) : ℝ) + 2) / lam ^ q k)) * lam ^ q k := by
          have hcancel :
              Real.log (((q k : ℕ) : ℝ) + 2) / lam ^ q k * lam ^ q k =
                Real.log (((q k : ℕ) : ℝ) + 2) :=
            div_mul_cancel₀ _ hp.ne'
          calc
            2 * (C : ℝ) * Real.log (((q k : ℕ) : ℝ) + 2) =
                2 * (C : ℝ) *
                  (Real.log (((q k : ℕ) : ℝ) + 2) / lam ^ q k * lam ^ q k) := by
              rw [hcancel]
            _ = (2 * (C : ℝ) *
                (Real.log (((q k : ℕ) : ℝ) + 2) / lam ^ q k)) * lam ^ q k := by
              ring
  have htail0 : Tendsto
      (fun n => integerPolynomialShift Q h n / lam ^ n)
      atTop (𝓝 0) :=
    (integerPolynomialShift_isLittleO_const_pow hlam0 hh Q).tendsto_div_nhds_zero
  have hmodel : Tendsto
      (fun n => integerPolynomialShift Q b n / lam ^ n)
      atTop (𝓝 (A * integerPolynomialRealEval Q lam)) := by
    have hadd := (tendsto_const_nhds : Tendsto
      (fun _ : ℕ => A * integerPolynomialRealEval Q lam) atTop
      (𝓝 (A * integerPolynomialRealEval Q lam))).add htail0
    convert hadd using 1
    · funext n
      rw [hb, integerPolynomialShift_add, integerPolynomialShift_const_mul,
        integerPolynomialShift_geometric]
      have hp : lam ^ n ≠ 0 := pow_ne_zero n hlam0.ne'
      rw [add_div]
      congr 1
      apply (div_eq_iff hp).2
      ring
    · simp
  have hzero : A * integerPolynomialRealEval Q lam = 0 :=
    tendsto_nhds_unique (hmodel.comp hq) hnormalized0
  exact (mul_eq_zero.mp hzero).resolve_left hA

/-- After a geometric layer is peeled, the same logarithmic defect is carried exactly by the
residual sequence. -/
theorem hasLogarithmicShiftDefectAlong_residual_of_geometricLayer
    {Q : Polynomial ℤ} {b h : ℕ → ℝ} {C K : ℕ} {q : ℕ → ℕ}
    {A lam : ℝ}
    (hb : b = fun n => A * lam ^ n + h n)
    (heval : integerPolynomialRealEval Q lam = 0)
    (hdefect : HasLogarithmicShiftDefectAlong Q b C K q) :
    HasLogarithmicShiftDefectAlong Q h C K q := by
  filter_upwards [hdefect] with k hk
  have heq : integerPolynomialShift Q b (q k) =
      integerPolynomialShift Q h (q k) := by
    rw [hb, integerPolynomialShift_add, integerPolynomialShift_const_mul,
      integerPolynomialShift_geometric, heval]
    ring
  simpa only [heq] using hk

/-- A recursively ordered finite tower of positive geometric layers. Each remaining tail is
little-o of the layer immediately above it. -/
inductive FiniteGeometricLayerTower :
    List (ℝ × ℝ) → (ℕ → ℝ) → (ℕ → ℝ) → Prop
  | nil (h : ℕ → ℝ) : FiniteGeometricLayerTower [] h h
  | cons {layers : List (ℝ × ℝ)} {b mid h : ℕ → ℝ} {A lam : ℝ}
      (hA : 0 < A) (hlam : 1 < lam)
      (hb : b = fun n => A * lam ^ n + mid n)
      (hsmall : mid =o[atTop] fun n : ℕ => lam ^ n)
      (htail : FiniteGeometricLayerTower layers mid h) :
      FiniteGeometricLayerTower ((A, lam) :: layers) b h

/-- Every layer of a finite geometric tower is a root of a shift polynomial whose defect is only
logarithmic along a cofinal subsequence; after all layers are peeled, the same defect lies on the
terminal residual. -/
theorem FiniteGeometricLayerTower.roots_and_residual_defect
    {layers : List (ℝ × ℝ)} {b h : ℕ → ℝ}
    (htower : FiniteGeometricLayerTower layers b h)
    {Q : Polynomial ℤ} {C K : ℕ} {q : ℕ → ℕ}
    (hq : Tendsto q atTop atTop)
    (hdefect : HasLogarithmicShiftDefectAlong Q b C K q) :
    (∀ layer ∈ layers, integerPolynomialRealEval Q layer.2 = 0) ∧
      HasLogarithmicShiftDefectAlong Q h C K q := by
  induction htower with
  | nil h =>
      exact ⟨by simp, hdefect⟩
  | cons hA hlam hb hsmall htail ih =>
      have heval := integerPolynomialRealEval_eq_zero_of_geometricLayer_defect
        hA.ne' hlam hb hsmall hq hdefect
      have hmid := hasLogarithmicShiftDefectAlong_residual_of_geometricLayer
        hb heval hdefect
      obtain ⟨hroots, hres⟩ := ih hmid
      constructor
      · intro layer hlayer
        simp only [List.mem_cons] at hlayer
        rcases hlayer with rfl | hlayer
        · exact heval
        · exact hroots layer hlayer
      · exact hres

theorem FiniteGeometricLayerTower.eventually_pos_of_cons
    {A lam : ℝ} {layers : List (ℝ × ℝ)} {b h : ℕ → ℝ}
    (htower : FiniteGeometricLayerTower ((A, lam) :: layers) b h) :
    ∀ᶠ n in atTop, 0 < b n := by
  cases htower with
  | cons hA hlam hb hsmall htail =>
      rw [hb]
      exact eventually_pos_hierarchical hlam hA hsmall

theorem FiniteGeometricLayerTower.uniformGeometricGrowth_of_cons
    {A lam : ℝ} {layers : List (ℝ × ℝ)} {b h : ℕ → ℝ}
    (htower : FiniteGeometricLayerTower ((A, lam) :: layers) b h) :
    UniformGeometricGrowth b := by
  cases htower with
  | cons hA hlam hb hsmall htail =>
      rw [hb]
      exact uniformGeometricGrowth_hierarchical hlam hA hsmall

/-- A recursively separated infinite tower of positive geometric layers.  `tail i` is the
unpeeled profile starting at depth `i`; the equality and little-`o` fields make every layer
available without asserting convergence of a separate infinite sum. -/
structure InfiniteGeometricLayerTower (b : ℕ → ℝ) where
  amplitude : ℕ → ℝ
  ratio : ℕ → ℝ
  tail : ℕ → ℕ → ℝ
  tail_zero : tail 0 = b
  amplitude_pos : ∀ i, 0 < amplitude i
  ratio_one_lt : ∀ i, 1 < ratio i
  split : ∀ i, tail i = fun n => amplitude i * ratio i ^ n + tail (i + 1) n
  small : ∀ i, tail (i + 1) =o[atTop] fun n : ℕ => ratio i ^ n

theorem InfiniteGeometricLayerTower.eventually_pos
    {b : ℕ → ℝ} (htower : InfiniteGeometricLayerTower b) :
    ∀ᶠ n in atTop, 0 < b n := by
  rw [← htower.tail_zero, htower.split 0]
  exact eventually_pos_hierarchical (htower.ratio_one_lt 0)
    (htower.amplitude_pos 0) (htower.small 0)

theorem InfiniteGeometricLayerTower.uniformGeometricGrowth
    {b : ℕ → ℝ} (htower : InfiniteGeometricLayerTower b) :
    UniformGeometricGrowth b := by
  rw [← htower.tail_zero, htower.split 0]
  exact uniformGeometricGrowth_hierarchical (htower.ratio_one_lt 0)
    (htower.amplitude_pos 0) (htower.small 0)

/-- One logarithmically bounded shift defect descends through every depth of an infinite tower,
forcing the same integer polynomial to vanish at every layer ratio. -/
theorem InfiniteGeometricLayerTower.roots_and_defect_at_every_depth
    {b : ℕ → ℝ} (htower : InfiniteGeometricLayerTower b)
    {Q : Polynomial ℤ} {C K : ℕ} {q : ℕ → ℕ}
    (hq : Tendsto q atTop atTop)
    (hdefect : HasLogarithmicShiftDefectAlong Q b C K q) :
    (∀ i, integerPolynomialRealEval Q (htower.ratio i) = 0) ∧
      ∀ i, HasLogarithmicShiftDefectAlong Q (htower.tail i) C K q := by
  have hdefectAll :
      ∀ i, HasLogarithmicShiftDefectAlong Q (htower.tail i) C K q := by
    intro i
    induction i with
    | zero =>
        simpa only [htower.tail_zero] using hdefect
    | succ i ih =>
        have hroot := integerPolynomialRealEval_eq_zero_of_geometricLayer_defect
          (htower.amplitude_pos i).ne' (htower.ratio_one_lt i)
          (htower.split i) (htower.small i) hq ih
        simpa only [Nat.succ_eq_add_one] using
          hasLogarithmicShiftDefectAlong_residual_of_geometricLayer
            (htower.split i) hroot ih
  constructor
  · intro i
    exact integerPolynomialRealEval_eq_zero_of_geometricLayer_defect
      (htower.amplitude_pos i).ne' (htower.ratio_one_lt i)
      (htower.split i) (htower.small i) hq (hdefectAll i)
  · exact hdefectAll

/-- **Finite spectral-layer DA resonance law.** Differential algebraicity of a full-support
Taylor series whose negative log-magnitudes have a finite geometric asymptotic tower forces one
nonzero integer shift polynomial to vanish at every layer ratio. The same shift polynomial has a
nonnegative logarithmic defect on the final residual along one cofinal subsequence. -/
theorem exists_finiteGeometricLayer_resonancePolynomial_of_differentiallyAlgebraic
    {f : ℂ → ℂ} (hf : ContDiff ℂ (⊤ : ℕ∞) f)
    {A lam : ℝ} {layers : List (ℝ × ℝ)} {b h : ℕ → ℝ}
    (htower : FiniteGeometricLayerTower ((A, lam) :: layers) b h)
    (hb : ∀ᶠ i in atTop,
      ‖PowerSeries.coeff i (taylorPS f)‖ = Real.exp (-b i))
    (hDA : DifferentiallyAlgebraic f) :
    ∃ Q : Polynomial ℤ, ∃ C K : ℕ, ∃ q : ℕ → ℕ,
      Q ≠ 0 ∧ Q.eval 1 = 0 ∧ Tendsto q atTop atTop ∧
      (∀ layer ∈ (A, lam) :: layers,
        integerPolynomialRealEval Q layer.2 = 0) ∧
      HasLogarithmicShiftDefectAlong Q h C K q := by
  obtain ⟨Q, C, K, q, hQ, hQone, hq, hdefect⟩ :=
    exists_eventually_uniformGeometric_resonancePolynomial_of_differentiallyAlgebraic
      hf hb htower.eventually_pos_of_cons
        htower.uniformGeometricGrowth_of_cons hDA
  have hdefect' : HasLogarithmicShiftDefectAlong Q b C K q := by
    simpa only [HasLogarithmicShiftDefectAlong, integerPolynomialShift] using hdefect
  obtain ⟨hroots, hres⟩ := htower.roots_and_residual_defect hq hdefect'
  exact ⟨Q, C, K, q, hQ, hQone, hq, hroots, hres⟩

/-- **Infinite spectral-layer DA resonance law.** If a DA Taylor log-magnitude profile has an
infinite recursively separated geometric tower, one fixed nonzero integer polynomial must vanish
at every layer ratio and its same signed logarithmic defect descends through every depth. -/
theorem exists_infiniteGeometricLayer_resonancePolynomial_of_differentiallyAlgebraic
    {f : ℂ → ℂ} (hf : ContDiff ℂ (⊤ : ℕ∞) f)
    {b : ℕ → ℝ} (htower : InfiniteGeometricLayerTower b)
    (hb : ∀ᶠ i in atTop,
      ‖PowerSeries.coeff i (taylorPS f)‖ = Real.exp (-b i))
    (hDA : DifferentiallyAlgebraic f) :
    ∃ Q : Polynomial ℤ, ∃ C K : ℕ, ∃ q : ℕ → ℕ,
      Q ≠ 0 ∧ Q.eval 1 = 0 ∧ Tendsto q atTop atTop ∧
      (∀ i, integerPolynomialRealEval Q (htower.ratio i) = 0) ∧
      ∀ i, HasLogarithmicShiftDefectAlong Q (htower.tail i) C K q := by
  obtain ⟨Q, C, K, q, hQ, hQone, hq, hdefect⟩ :=
    exists_eventually_uniformGeometric_resonancePolynomial_of_differentiallyAlgebraic
      hf hb htower.eventually_pos htower.uniformGeometricGrowth hDA
  have hdefect' : HasLogarithmicShiftDefectAlong Q b C K q := by
    simpa only [HasLogarithmicShiftDefectAlong, integerPolynomialShift] using hdefect
  obtain ⟨hroots, hdefectAll⟩ :=
    htower.roots_and_defect_at_every_depth hq hdefect'
  exact ⟨Q, C, K, q, hQ, hQone, hq, hroots, hdefectAll⟩

/-- An infinite tower with pairwise distinct ratios is incompatible with differential
algebraicity.  Thus every phase realization with those Taylor magnitudes is
hypertranscendental, even when all individual ratios are algebraic. -/
theorem hypertranscendental_of_infiniteGeometricLayerTower
    {f : ℂ → ℂ} (hf : ContDiff ℂ (⊤ : ℕ∞) f)
    {b : ℕ → ℝ} (htower : InfiniteGeometricLayerTower b)
    (hratio : Function.Injective htower.ratio)
    (hb : ∀ᶠ i in atTop,
      ‖PowerSeries.coeff i (taylorPS f)‖ = Real.exp (-b i)) :
    Hypertranscendental f := by
  intro hDA
  obtain ⟨Q, C, K, q, hQ, hQone, hq, hroots, hdefectAll⟩ :=
    exists_infiniteGeometricLayer_resonancePolynomial_of_differentiallyAlgebraic
      hf htower hb hDA
  let QR : Polynomial ℝ := Q.map (algebraMap ℤ ℝ)
  have hroot : Set.range htower.ratio ⊆ {x | QR.IsRoot x} := by
    rintro x ⟨i, rfl⟩
    change (Q.map (algebraMap ℤ ℝ)).eval (htower.ratio i) = 0
    rw [Polynomial.eval_map, ← integerPolynomialRealEval_eq_eval₂]
    exact hroots i
  have hQRzero : QR = 0 := Polynomial.eq_zero_of_infinite_isRoot QR
    ((Set.infinite_range_of_injective hratio).mono hroot)
  have hQRne : QR ≠ 0 := by
    exact fun hc => hQ ((Polynomial.map_eq_zero_iff
      (algebraMap ℤ ℝ).injective_int).mp hc)
  exact hQRne hQRzero

/-- Every ratio in a finite geometric asymptotic tower of DA Taylor log-magnitudes is algebraic
over the integers. This applies to lower layers invisible to the ordinary successive-ratio limit. -/
theorem finiteGeometricLayer_ratio_isAlgebraic_of_differentiallyAlgebraic
    {f : ℂ → ℂ} (hf : ContDiff ℂ (⊤ : ℕ∞) f)
    {A lam : ℝ} {layers : List (ℝ × ℝ)} {b h : ℕ → ℝ}
    (htower : FiniteGeometricLayerTower ((A, lam) :: layers) b h)
    (hb : ∀ᶠ i in atTop,
      ‖PowerSeries.coeff i (taylorPS f)‖ = Real.exp (-b i))
    (hDA : DifferentiallyAlgebraic f)
    {layer : ℝ × ℝ} (hlayer : layer ∈ (A, lam) :: layers) :
    IsAlgebraic ℤ layer.2 := by
  obtain ⟨Q, C, K, q, hQ, hQone, hq, hroots, hres⟩ :=
    exists_finiteGeometricLayer_resonancePolynomial_of_differentiallyAlgebraic
      hf htower hb hDA
  refine ⟨Q, hQ, ?_⟩
  rw [Polynomial.aeval_def, ← integerPolynomialRealEval_eq_eval₂]
  exact hroots layer hlayer

/-- A transcendental ratio at any depth of a finite geometric magnitude tower forces
hypertranscendence, even when every larger ratio is algebraic. -/
theorem hypertranscendental_of_finiteGeometricLayer_transcendental_ratio
    {f : ℂ → ℂ} (hf : ContDiff ℂ (⊤ : ℕ∞) f)
    {A lam : ℝ} {layers : List (ℝ × ℝ)} {b h : ℕ → ℝ}
    (htower : FiniteGeometricLayerTower ((A, lam) :: layers) b h)
    (hb : ∀ᶠ i in atTop,
      ‖PowerSeries.coeff i (taylorPS f)‖ = Real.exp (-b i))
    {layer : ℝ × ℝ} (hlayer : layer ∈ (A, lam) :: layers)
    (htrans : Transcendental ℚ layer.2) :
    Hypertranscendental f := by
  intro hDA
  have hz : IsAlgebraic ℤ layer.2 :=
    finiteGeometricLayer_ratio_isAlgebraic_of_differentiallyAlgebraic
      hf htower hb hDA hlayer
  obtain ⟨Q, hQ, hroot⟩ := hz
  have hq : IsAlgebraic ℚ layer.2 := by
    refine ⟨Q.map (algebraMap ℤ ℚ), ?_, ?_⟩
    · exact fun hc => hQ ((Polynomial.map_eq_zero_iff
        (algebraMap ℤ ℚ).injective_int).mp hc)
    · rw [Polynomial.aeval_map_algebraMap]
      exact hroot
  exact htrans hq

/-- Two explicit geometric layers already force a common integer annihilator. The second root is
invisible to the ordinary successive-ratio limit, which sees only `lam₀`. -/
theorem exists_twoGeometricLayer_common_resonance_of_differentiallyAlgebraic
    {f : ℂ → ℂ} (hf : ContDiff ℂ (⊤ : ℕ∞) f)
    {A₀ A₁ lam₀ lam₁ : ℝ}
    (hA₀ : 0 < A₀) (hA₁ : 0 < A₁)
    (hlam₀ : 1 < lam₀) (hlam₁ : 1 < lam₁) (hlam : lam₁ < lam₀)
    {h : ℕ → ℝ} (hh : h =o[atTop] fun n : ℕ => lam₁ ^ n)
    (hb : ∀ᶠ i in atTop,
      ‖PowerSeries.coeff i (taylorPS f)‖ =
        Real.exp (-(A₀ * lam₀ ^ i + (A₁ * lam₁ ^ i + h i))))
    (hDA : DifferentiallyAlgebraic f) :
    ∃ Q : Polynomial ℤ, ∃ C K : ℕ, ∃ q : ℕ → ℕ,
      Q ≠ 0 ∧ Q.eval 1 = 0 ∧
      integerPolynomialRealEval Q lam₀ = 0 ∧
      integerPolynomialRealEval Q lam₁ = 0 ∧
      Tendsto q atTop atTop ∧ HasLogarithmicShiftDefectAlong Q h C K q := by
  have hgeom : (fun n : ℕ => lam₁ ^ n) =o[atTop] fun n => lam₀ ^ n :=
    isLittleO_pow_pow_of_lt_left (zero_lt_one.trans hlam₁).le hlam
  have hmid : (fun n : ℕ => A₁ * lam₁ ^ n + h n) =o[atTop]
      fun n => lam₀ ^ n :=
    hgeom.const_mul_left A₁ |>.add (hh.trans hgeom)
  let b : ℕ → ℝ := fun n => A₀ * lam₀ ^ n + (A₁ * lam₁ ^ n + h n)
  let mid : ℕ → ℝ := fun n => A₁ * lam₁ ^ n + h n
  have htower : FiniteGeometricLayerTower
      [(A₀, lam₀), (A₁, lam₁)] b h := by
    apply FiniteGeometricLayerTower.cons hA₀ hlam₀ rfl hmid
    exact FiniteGeometricLayerTower.cons hA₁ hlam₁ rfl hh
      (FiniteGeometricLayerTower.nil h)
  have hb' : ∀ᶠ i in atTop,
      ‖PowerSeries.coeff i (taylorPS f)‖ = Real.exp (-b i) := by
    simpa only [b] using hb
  obtain ⟨Q, C, K, q, hQ, hQone, hq, hroots, hres⟩ :=
    exists_finiteGeometricLayer_resonancePolynomial_of_differentiallyAlgebraic
      hf htower hb' hDA
  have hroot₀ : integerPolynomialRealEval Q lam₀ = 0 :=
    hroots (A₀, lam₀) (by simp)
  have hroot₁ : integerPolynomialRealEval Q lam₁ = 0 :=
    hroots (A₁, lam₁) (by simp)
  exact ⟨Q, C, K, q, hQ, hQone, hroot₀, hroot₁, hq, hres⟩

end

end GaloisForLFunctions
