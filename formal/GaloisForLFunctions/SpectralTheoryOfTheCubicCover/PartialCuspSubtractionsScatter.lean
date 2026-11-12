import GaloisForLFunctions.SpectralTheoryOfTheCubicCover.TheRationalCuspSubtractionScatters

/-!
# Partial cusp subtractions scatter

For a set `Q` of rational cusps containing `∞` (`q = 1`), the partial subtraction

`H^Q_S(w) = c² Σ_{q ∈ Q} conj E_1(r_q w ∣ f_S)`   (`partialSubtraction`)

behaves like the full one: multiplier `κ⁻¹`, `c² f_S(v)` above height `1/2`, `O(v^{−4/3})` below.
Each rational translate unfolds separately (`integral_conj_cutoff_one_mul_eisenstein`,
`integral_conj_cutoff_rep_mul_eisenstein`): the identity coset reads the constant term of `E(s)`,
`|P|(v^s + v^{2−s}(π/(s−1))φ(s))`, every other one reads that of `E(s)∘S`, `v^{2−s}(π/(s−1))U(s)`. Hence
(`integral_partialScatterPart`, `Re s > 10/3`)

`∫_0^∞ v^s (a₀(H^Q)(v) − |P| c² f(v)) v^{−3} dv = c² Φ_k(s) ∫_0^∞ f(v) v^{2−s} v^{−3} dv`,

`Φ_k(s) = |P| (π/(s−1)) φ(s) + k (π/(s−1)) U(s)`, `k = |Q| − 1` (`partialScatterTotal`); `Q` = all four
cusps gives `scatterTotal`. The proof is the one for the full subtraction: the truncated identity, then
`T → ∞` with errors `O(T^{10/3 − Re s}) + O(T^{4/3 − Re s})`.
-/

noncomputable section

open MeasureTheory Filter Function
open scoped BigOperators Classical MatrixGroups ComplexConjugate ENNReal Topology

namespace GaloisForLFunctions.SpectralTheoryOfTheCubicCover

open MetaplecticMobiusDescent MetaplecticMobiusDescent.Eisenstein MetaplecticMobiusDescent.CubicKubota
  MetaplecticMobiusDescent.CubicEisenstein MetaplecticMobiusDescent.CubicEisenstein.RationalSource

/-- `H^Q_S(w) = c² Σ_{q ∈ Q} conj E_1(r_q w ∣ f_S)`. -/
def partialSubtraction (Q : Finset RationalFourCusp) (c : ℂ) (S : Set ℝ) (w : HyperbolicSpace) : ℂ :=
  c ^ 2 * ∑ q ∈ Q, conj (cuspCutoffCorrection 1 (growthProfile S) (rationalComplex (rationalRep q) • w))

theorem partialSubtraction_measurable (Q : Finset RationalFourCusp) (c : ℂ) (S : Set ℝ) (hS : MeasurableSet S) :
    Measurable (partialSubtraction Q c S) := by
  unfold partialSubtraction
  refine measurable_const.mul (Finset.measurable_sum _ fun q _ => ?_)
  exact Complex.continuous_conj.measurable.comp
    ((cuspCutoffCorrection_measurable 1 _ (growthProfile_measurable S hS)).comp
      (continuous_hyperbolic_action _).measurable)

theorem partialSubtraction_automorphy (Q : Finset RationalFourCusp) (c : ℂ) (S : Set ℝ) (M : levelThree)
    (w : HyperbolicSpace) :
    partialSubtraction Q c S (complexMatrix M • w) = (complexCharacter M)⁻¹ * partialSubtraction Q c S w := by
  simp only [partialSubtraction, conj_cutoff_rational_automorphy, ← Finset.mul_sum]
  ring

/-- `|Σ_{q ∈ Q} a_q| ≤ 4 B` when every `|a_q| ≤ B`. -/
theorem norm_partialSubtraction_le_of (Q : Finset RationalFourCusp) (c : ℂ) (S : Set ℝ) (w : HyperbolicSpace)
    (B : ℝ) (hB0 : 0 ≤ B)
    (hB : ∀ q : RationalFourCusp,
      ‖cuspCutoffCorrection 1 (growthProfile S) (rationalComplex (rationalRep q) • w)‖ ≤ B) :
    ‖partialSubtraction Q c S w‖ ≤ ‖c‖ ^ 2 * (4 * B) := by
  rw [partialSubtraction, norm_mul, norm_pow]
  gcongr
  have hcard : (Q.card : ℝ) ≤ 4 := by
    have := Finset.card_le_univ Q
    rw [card_rationalFourCusp] at this
    exact_mod_cast this
  calc ‖∑ q ∈ Q, conj (cuspCutoffCorrection 1 (growthProfile S) (rationalComplex (rationalRep q) • w))‖
      ≤ ∑ q ∈ Q, ‖conj (cuspCutoffCorrection 1 (growthProfile S) (rationalComplex (rationalRep q) • w))‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _q ∈ Q, B := Finset.sum_le_sum fun q _ => by rw [RCLike.norm_conj]; exact hB q
    _ = Q.card * B := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 4 * B := mul_le_mul_of_nonneg_right hcard hB0

theorem norm_partialSubtraction_le (Q : Finset RationalFourCusp) (c : ℂ) {T : ℝ} (hT : 2 ≤ T) (S : Set ℝ)
    (hS : S ⊆ Set.Icc 2 T) (w : HyperbolicSpace) :
    ‖partialSubtraction Q c S w‖ ≤ ‖c‖ ^ 2 * (4 * T ^ ((4 : ℝ) / 3)) := by
  refine norm_partialSubtraction_le_of Q c S w _ (by positivity) fun q =>
    cuspCutoffCorrection_norm_le _ _ (by positivity) (fun t => ?_) _
  rw [growthProfile]
  by_cases h : t ∈ S
  · rw [Set.indicator_of_mem h, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg (by
      linarith [(hS h).1]) _)]
    exact Real.rpow_le_rpow (by linarith [(hS h).1]) (hS h).2 (by norm_num)
  · rw [Set.indicator_of_notMem h, norm_zero]
    positivity

theorem norm_partialSubtraction_small (Q : Finset RationalFourCusp) (c : ℂ) (S : Set ℝ) (z : ℂ) (v : ℝ)
    (hv : 0 < v) (hv2 : v ≤ 1 / 2) :
    ‖partialSubtraction Q c S (upperPoint z v hv)‖ ≤ ‖c‖ ^ 2 * (4 * (1 / v) ^ ((4 : ℝ) / 3)) := by
  refine norm_partialSubtraction_le_of Q c S _ _ (by positivity) fun q =>
    cuspCutoffCorrection_norm_le_of _ _ (by positivity) _ fun r hr => ?_
  have hh := cosetHeight_rationalRep_le q r z v hv hv2 hr
  refine (norm_growthProfile_le S (by linarith)).trans ?_
  exact Real.rpow_le_rpow (by linarith) hh (by norm_num)

theorem partialSubtraction_truncate (Q : Finset RationalFourCusp) (c : ℂ) {T : ℝ} (hT : 2 ≤ T) (z : ℂ)
    (v : ℝ) (hv : 0 < v) (hv2 : v ≤ 1 / 2) (hvT : 1 / T ≤ v) :
    partialSubtraction Q c (Set.Icc 2 T) (upperPoint z v hv) =
      partialSubtraction Q c (Set.Ici 2) (upperPoint z v hv) := by
  unfold partialSubtraction
  congr 1
  refine Finset.sum_congr rfl fun q _ => ?_
  congr 1
  refine cuspCutoffCorrection_congr _ _ _ fun r hr => ?_
  have hh := cosetHeight_rationalRep_le q r z v hv hv2 hr
  have hT' : cosetHeight r (rationalComplex (rationalRep q) • upperPoint z v hv) ≤ T := by
    refine hh.trans ?_
    rw [div_le_iff₀ hv]
    rw [div_le_iff₀ (by linarith)] at hvT
    linarith
  simp only [growthProfile, Set.indicator, Set.mem_Icc, Set.mem_Ici, hT', and_true]

/-- Above height `1/2`, only the identity coset of the identity cusp survives: `H^Q_S = c² f_S(v)`. -/
theorem partialSubtraction_upper (Q : Finset RationalFourCusp) (hQ : .inl () ∈ Q) (c : ℂ) (S : Set ℝ)
    (hS : S ⊆ Set.Ici 2) (z : ℂ) (v : ℝ) (hv : 0 < v) (hv2 : 1 / 2 < v) :
    partialSubtraction Q c S (upperPoint z v hv) = c ^ 2 * growthProfile S v := by
  have hzero : ∀ t : ℝ, t < 2 → growthProfile S t = 0 := fun t ht =>
    Set.indicator_of_notMem (fun h => absurd (hS h) (not_le.mpr ht)) _
  have hsmall : 1 / v < 2 := by
    rw [div_lt_iff₀ hv]
    linarith
  rw [partialSubtraction, Finset.sum_eq_single_of_mem (.inl ()) hQ]
  · have h1 : rationalComplex (rationalRep (.inl ())) • upperPoint z v hv = upperPoint z v hv := by
      simp [rationalRep, rationalFourCuspRep]
    rw [h1, cuspCutoffCorrection_upper _ z v hv fun t _ ht => hzero t (by
      have : 1 / (9 * v) ≤ 1 / v := by
        apply div_le_div_of_nonneg_left zero_le_one hv
        linarith
      linarith)]
    split_ifs with h
    · rw [conj_growthProfile]
    · rw [hzero v (by linarith [not_lt.mp h]), map_zero]
  · intro q _ hq
    obtain ⟨h0, h1⟩ := rationalRep_column q hq
    rw [cuspCutoffCorrection_rational _ _ h0 h1 z v hv fun t _ ht => hzero t (by linarith), map_zero]

/-! ### Unfolding one rational translate -/

/-- The identity cusp: `∫_{D_Γ} conj E_1(w ∣ f_T) E(s) = ∫ f_T(v) |P|(v^s + v^{2−s}(π/(s−1))φ(s)) v^{−3} dv`. -/
theorem integral_conj_cutoff_one_mul_eisenstein (T : ℝ) (s : ℂ) (hs : 2 < s.re) :
    ∫ w in levelSet, conj (cuspCutoffCorrection 1 (growthProfile (Set.Icc 2 T))
        (rationalComplex (rationalRep (.inl ())) • w)) * hyperbolicEisenstein s w ∂hyperbolicVolume =
      ∫ v in Set.Ioi (0 : ℝ), growthProfile (Set.Icc 2 T) v * (periodArea * ((v : ℂ) ^ s + (v : ℂ) ^ (2 - s) *
        ((Real.pi : ℂ) / (s - 1) * scatteringCoefficient s 0)) / (v : ℂ) ^ 3) := by
  have hcont : Continuous (hyperbolicEisenstein s) := hyperbolicEisenstein_continuous s hs
  have hp : ∀ w : HyperbolicSpace, rationalComplex (rationalRep (.inl ())) • w = w := fun w => by
    simp [rationalRep, rationalFourCuspRep]
  simp only [hp]
  rw [integral_conj_cutoff_mul T _ hcont (fun M w => hyperbolicEisenstein_automorphy M s hs w)]
  refine setIntegral_congr_fun measurableSet_Ioi fun v (hv : 0 < v) => ?_
  rw [cuspConstant_eisenstein s hs v hv, mul_div_assoc]

/-- Any other rational cusp: `∫_{D_Γ} conj E_1(r_q w ∣ f_T) E(s) = ∫ f_T(v) v^{2−s}(π/(s−1))U(s) v^{−3} dv`. -/
theorem integral_conj_cutoff_rep_mul_eisenstein (T : ℝ) (q : RationalFourCusp) (hq : q ≠ .inl ()) (s : ℂ)
    (hs : 2 < s.re) :
    ∫ w in levelSet, conj (cuspCutoffCorrection 1 (growthProfile (Set.Icc 2 T))
        (rationalComplex (rationalRep q) • w)) * hyperbolicEisenstein s w ∂hyperbolicVolume =
      ∫ v in Set.Ioi (0 : ℝ), growthProfile (Set.Icc 2 T) v * ((v : ℂ) ^ (2 - s) *
        ((Real.pi : ℂ) / (s - 1) * unramifiedCubicGaussSeries s 0) / (v : ℂ) ^ 3) := by
  set f := growthProfile (Set.Icc 2 T)
  have hcont : Continuous (hyperbolicEisenstein s) := hyperbolicEisenstein_continuous s hs
  have hcontS : Continuous (fun w => hyperbolicEisenstein s (rationalComplex ModularGroup.S • w)) :=
    hcont.comp (continuous_hyperbolic_action _)
  set r := rationalRep q
  let F' : HyperbolicSpace → ℂ := fun u =>
    conj (cuspCutoffCorrection 1 f u) * hyperbolicEisenstein s ((rationalComplex r)⁻¹ • u)
  have hF' : ∀ (M : levelThree) (u : HyperbolicSpace), F' (complexMatrix M • u) = F' u := by
    intro M u
    have hmove : (rationalComplex r)⁻¹ • (complexMatrix M • u) =
        complexMatrix (levelThreeConjugate (rationalEmbedding r⁻¹) M) • ((rationalComplex r)⁻¹ • u) := by
      rw [← mul_smul, ← mul_smul]
      congr 1
      change (integralComplexMatrix (rationalEmbedding r))⁻¹ * integralComplexMatrix (M : SL(2, O)) =
        integralComplexMatrix ((rationalEmbedding r⁻¹) * (M : SL(2, O)) * (rationalEmbedding r⁻¹)⁻¹) *
          (integralComplexMatrix (rationalEmbedding r))⁻¹
      simp only [map_mul, map_inv, inv_inv]
      group
    have hc := cuspCutoffCorrection_automorphy 1 le_rfl f M u
    simp only [F', hmove, hc, hyperbolicEisenstein_automorphy _ s hs, complexCharacter_conjugate_rational,
      map_mul, conj_complexCharacter]
    have hne : complexCharacter M ≠ 0 := by
      intro h0
      have := norm_complexCharacter M
      rw [h0, norm_zero] at this
      exact zero_ne_one this
    field_simp
  have htr := setIntegral_levelSet_translate (rationalEmbedding r) F' hF'
  have hback : ∀ w, F' (integralComplexMatrix (rationalEmbedding r) • w) =
      conj (cuspCutoffCorrection 1 f (rationalComplex r • w)) * hyperbolicEisenstein s w := by
    intro w
    change conj (cuspCutoffCorrection 1 f (rationalComplex r • w)) *
      hyperbolicEisenstein s ((rationalComplex r)⁻¹ • (rationalComplex r • w)) = _
    rw [inv_smul_smul]
  simp_rw [hback] at htr
  rw [htr]
  have hS : ∀ u, F' u = conj (cuspCutoffCorrection 1 f u) *
      hyperbolicEisenstein s (rationalComplex ModularGroup.S • u) := fun u =>
    congrArg (fun t => conj (cuspCutoffCorrection 1 f u) * t) (eisenstein_rationalRep_inv s q hq u)
  simp_rw [hS]
  rw [integral_conj_cutoff_mul T _ hcontS (eisensteinS_automorphy s hs)]
  refine setIntegral_congr_fun measurableSet_Ioi fun v (hv : 0 < v) => ?_
  rw [cuspConstant_eisensteinS s hs v hv, mul_div_assoc]

/-- `Φ_k(s) = |P| (π/(s−1)) φ(s) + k (π/(s−1)) U(s)`. -/
def partialScatterTotal (k : ℕ) (s : ℂ) : ℂ :=
  periodArea * ((Real.pi : ℂ) / (s - 1) * scatteringCoefficient s 0) +
    k * ((Real.pi : ℂ) / (s - 1) * unramifiedCubicGaussSeries s 0)

/-- The number `|Q| − 1` of non-identity cusps of `Q`. -/
abbrev otherCusps (Q : Finset RationalFourCusp) : ℕ := (Q.erase (.inl ())).card

/-- **The truncated identity.** For `.inl () ∈ Q`, `T ≥ 2`, `Re s > 2`:
`∫_{D_Γ} H^Q_T E(s) = c² ∫ f_T(v) (|P| v^s + Φ_k(s) v^{2−s}) v^{−3} dv`. -/
theorem integral_partialSubtraction_trunc_mul_eisenstein (Q : Finset RationalFourCusp) (hQ : .inl () ∈ Q)
    (c : ℂ) {T : ℝ} (hT : 2 ≤ T) (s : ℂ) (hs : 2 < s.re) :
    ∫ w in levelSet, partialSubtraction Q c (Set.Icc 2 T) w * hyperbolicEisenstein s w ∂hyperbolicVolume =
      c ^ 2 * ∫ v in Set.Ioi (0 : ℝ), growthProfile (Set.Icc 2 T) v *
        (periodArea * (v : ℂ) ^ s + partialScatterTotal (otherCusps Q) s * (v : ℂ) ^ (2 - s)) /
          (v : ℂ) ^ 3 := by
  set f := growthProfile (Set.Icc 2 T)
  set Fq : RationalFourCusp → HyperbolicSpace → ℂ := fun q w =>
    conj (cuspCutoffCorrection 1 f (rationalComplex (rationalRep q) • w)) * hyperbolicEisenstein s w
  have hsplit : ∀ w, partialSubtraction Q c (Set.Icc 2 T) w * hyperbolicEisenstein s w =
      c ^ 2 * ∑ q ∈ Q, Fq q w := by
    intro w
    rw [partialSubtraction, mul_assoc, Finset.sum_mul]
  have hint : ∀ q, IntegrableOn (Fq q) levelSet hyperbolicVolume := fun q =>
    cutoff_rationalRep_integrable T hT q s hs
  simp_rw [hsplit]
  rw [integral_const_mul, integral_finsetSum _ fun q _ => hint q]
  congr 1
  rw [← Finset.add_sum_erase Q _ hQ, integral_conj_cutoff_one_mul_eisenstein T s hs,
    Finset.sum_congr rfl fun q hq => integral_conj_cutoff_rep_mul_eisenstein T q
      (Finset.ne_of_mem_erase hq) s hs, Finset.sum_const, nsmul_eq_mul]
  have hcpow : ∀ a : ℂ, ContinuousOn (fun v : ℝ => (v : ℂ) ^ a) (Set.Icc 2 T) := fun a v hv =>
    ((continuousAt_cpow_const (Complex.ofReal_mem_slitPlane.mpr (by linarith [hv.1]))).comp
      Complex.continuous_ofReal.continuousAt).continuousWithinAt
  have hden : ContinuousOn (fun v : ℝ => (v : ℂ) ^ 3) (Set.Icc 2 T) :=
    (Complex.continuous_ofReal.pow 3).continuousOn
  have hne : ∀ v ∈ Set.Icc 2 T, (v : ℂ) ^ 3 ≠ 0 := fun v hv =>
    pow_ne_zero 3 (Complex.ofReal_ne_zero.mpr (by linarith [hv.1]))
  have hA := growthProfile_mul_integrableOn T (fun v => periodArea * ((v : ℂ) ^ s + (v : ℂ) ^ (2 - s) *
      ((Real.pi : ℂ) / (s - 1) * scatteringCoefficient s 0)) / (v : ℂ) ^ 3)
    ((continuousOn_const.mul ((hcpow s).add ((hcpow (2 - s)).mul continuousOn_const))).div hden hne)
  have hB := growthProfile_mul_integrableOn T (fun v => (v : ℂ) ^ (2 - s) *
      ((Real.pi : ℂ) / (s - 1) * unramifiedCubicGaussSeries s 0) / (v : ℂ) ^ 3)
    (((hcpow (2 - s)).mul continuousOn_const).div hden hne)
  rw [← integral_const_mul, ← integral_add hA (hB.const_mul _)]
  refine setIntegral_congr_fun measurableSet_Ioi fun v _ => ?_
  simp only [partialScatterTotal, f]
  ring

/-! ### Removing the truncation -/

/-- The scattering part `a₀(H^Q_S)(v) − |P| c² f_S(v)`. -/
def partialScatterPart (Q : Finset RationalFourCusp) (c : ℂ) (S : Set ℝ) (v : ℝ) : ℂ :=
  cuspConstantTerm (partialSubtraction Q c S) v - periodArea * c ^ 2 * growthProfile S v

theorem partialScatterPart_measurable (Q : Finset RationalFourCusp) (c : ℂ) (S : Set ℝ) (hS : MeasurableSet S) :
    StronglyMeasurable (partialScatterPart Q c S) :=
  (cuspConstantTerm_measurable _ (partialSubtraction_measurable Q c S hS)).sub
    (stronglyMeasurable_const.mul (growthProfile_measurable S hS).stronglyMeasurable)

theorem partialScatterPart_high (Q : Finset RationalFourCusp) (hQ : .inl () ∈ Q) (c : ℂ) (S : Set ℝ)
    (hS : S ⊆ Set.Ici 2) (v : ℝ) (hv2 : 1 / 2 < v) :
    partialScatterPart Q c S v = 0 := by
  have hv : 0 < v := by linarith
  have hP : volume.real periodDomain = periodAreaReal := by
    rw [Measure.real, periodDomain_volume, ENNReal.toReal_ofReal periodAreaReal_pos.le]
  rw [partialScatterPart, cuspConstantTerm]
  have hc : ∀ z, partialSubtraction Q c S (cuspCoordinateLift (v, z)) = c ^ 2 * growthProfile S v := fun z => by
    rw [cuspCoordinateLift_positive v z hv, partialSubtraction_upper Q hQ c S hS z v hv hv2]
  simp_rw [hc]
  rw [setIntegral_const, hP, Complex.real_smul]
  ring

theorem norm_partialScatterPart_small (Q : Finset RationalFourCusp) (c : ℂ) (S : Set ℝ) (hS : S ⊆ Set.Ici 2)
    (v : ℝ) (hv : 0 < v) (hv2 : v ≤ 1 / 2) :
    ‖partialScatterPart Q c S v‖ ≤ ‖c‖ ^ 2 * (4 * (1 / v) ^ ((4 : ℝ) / 3)) * periodAreaReal := by
  have hf : growthProfile S v = 0 :=
    Set.indicator_of_notMem (fun h => by linarith [Set.mem_Ici.mp (hS h)]) _
  rw [partialScatterPart, hf, mul_zero, sub_zero]
  exact norm_cuspConstantTerm_le _ v hv _ fun z => norm_partialSubtraction_small Q c S z v hv hv2

theorem partialScatterPart_truncate (Q : Finset RationalFourCusp) (hQ : .inl () ∈ Q) (c : ℂ) {T : ℝ}
    (hT : 2 ≤ T) (v : ℝ) (hv : 0 < v) (hvT : 1 / T ≤ v) :
    partialScatterPart Q c (Set.Icc 2 T) v = partialScatterPart Q c (Set.Ici 2) v := by
  by_cases hv2 : v ≤ 1 / 2
  · have hf : ∀ S : Set ℝ, S ⊆ Set.Ici 2 → growthProfile S v = 0 := fun S hS =>
      Set.indicator_of_notMem (fun h => by linarith [Set.mem_Ici.mp (hS h)]) _
    rw [partialScatterPart, partialScatterPart, hf _ (fun t ht => ht.1), hf _ le_rfl, cuspConstantTerm,
      cuspConstantTerm]
    congr 1
    refine setIntegral_congr_fun periodDomain_measurable fun z _ => ?_
    rw [cuspCoordinateLift_positive v z hv, partialSubtraction_truncate Q c hT z v hv hv2 hvT]
  · rw [partialScatterPart_high Q hQ c _ (fun t ht => ht.1) v (not_le.mp hv2),
      partialScatterPart_high Q hQ c _ le_rfl v (not_le.mp hv2)]

theorem integrableOn_partialScatterPart (Q : Finset RationalFourCusp) (hQ : .inl () ∈ Q) (c : ℂ) (S : Set ℝ)
    (hS : S ⊆ Set.Ici 2) (hSm : MeasurableSet S) (s : ℂ) (hs : 10 / 3 < s.re) :
    IntegrableOn (fun v : ℝ => (v : ℂ) ^ s * partialScatterPart Q c S v / (v : ℂ) ^ 3) (Set.Ioi 0) := by
  set C := ‖c‖ ^ 2 * 4 * periodAreaReal
  have hg : IntegrableOn (fun v : ℝ => C * v ^ (s.re - 13 / 3)) (Set.Ioc 0 (1 / 2)) := by
    have := intervalIntegral.intervalIntegrable_rpow' (r := s.re - 13 / 3) (by linarith)
      (a := 0) (b := 1 / 2)
    exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mp this).const_mul C
  have hm : AEStronglyMeasurable (fun v : ℝ => (v : ℂ) ^ s * partialScatterPart Q c S v / (v : ℂ) ^ 3)
      (volume.restrict (Set.Ioc 0 (1 / 2))) :=
    (((Complex.measurable_ofReal.pow_const s).mul (partialScatterPart_measurable Q c S hSm).measurable).div
      (Complex.measurable_ofReal.pow_const 3)).aestronglyMeasurable
  have h1 : IntegrableOn (fun v : ℝ => (v : ℂ) ^ s * partialScatterPart Q c S v / (v : ℂ) ^ 3)
      (Set.Ioc 0 (1 / 2)) := by
    refine hg.mono' hm (ae_restrict_of_forall_mem measurableSet_Ioc fun v hv => ?_)
    have hv0 := hv.1
    have hb := norm_partialScatterPart_small Q c S hS v hv0 hv.2
    rw [norm_div, norm_mul, norm_pow, Complex.norm_cpow_eq_rpow_re_of_pos hv0, Complex.norm_real,
      Real.norm_of_nonneg hv0.le]
    have hpow : (1 / v) ^ ((4 : ℝ) / 3) = v ^ (-((4 : ℝ) / 3)) := by
      rw [one_div, Real.inv_rpow hv0.le, Real.rpow_neg hv0.le]
    rw [hpow] at hb
    have he : v ^ s.re * (‖c‖ ^ 2 * (4 * v ^ (-((4 : ℝ) / 3))) * periodAreaReal) / v ^ 3 =
        C * v ^ (s.re - 13 / 3) := by
      rw [show s.re - 13 / 3 = s.re + (-((4 : ℝ) / 3)) - 3 by ring, Real.rpow_sub hv0,
        Real.rpow_add hv0]
      norm_cast
      ring
    calc v ^ s.re * ‖partialScatterPart Q c S v‖ / v ^ 3
        ≤ v ^ s.re * (‖c‖ ^ 2 * (4 * v ^ (-((4 : ℝ) / 3))) * periodAreaReal) / v ^ 3 := by
          gcongr
      _ = C * v ^ (s.re - 13 / 3) := he
  refine h1.of_forall_sdiff_eq_zero measurableSet_Ioi fun v hv => ?_
  have hv2 : 1 / 2 < v := by
    by_contra h
    exact hv.2 ⟨hv.1, not_lt.mp h⟩
  rw [partialScatterPart_high Q hQ c S hS v hv2, mul_zero, zero_div]

/-- **The scattering of a partial cusp subtraction.** For `.inl () ∈ Q` and `Re s > 10/3`:
`∫_0^∞ v^s (a₀(H^Q)(v) − |P| c² f(v)) v^{−3} dv = c² Φ_k(s) ∫_0^∞ f(v) v^{2−s} v^{−3} dv`, `k = |Q| − 1`. -/
theorem integral_partialScatterPart (Q : Finset RationalFourCusp) (hQ : .inl () ∈ Q) (c : ℂ) (s : ℂ)
    (hs : 10 / 3 < s.re) :
    ∫ v in Set.Ioi (0 : ℝ), (v : ℂ) ^ s * partialScatterPart Q c (Set.Ici 2) v / (v : ℂ) ^ 3 =
      c ^ 2 * partialScatterTotal (otherCusps Q) s * ∫ v in Set.Ioi (0 : ℝ),
        growthProfile (Set.Ici 2) v * (v : ℂ) ^ (2 - s) / (v : ℂ) ^ 3 := by
  have hs2 : 2 < s.re := by linarith
  set Φ := partialScatterTotal (otherCusps Q) s
  set X := (∫ v in Set.Ioi (0 : ℝ), (v : ℂ) ^ s * partialScatterPart Q c (Set.Ici 2) v / (v : ℂ) ^ 3) -
    c ^ 2 * Φ * ∫ v in Set.Ioi (0 : ℝ),
      growthProfile (Set.Ici 2) v * (v : ℂ) ^ (2 - s) / (v : ℂ) ^ 3 with hX
  suffices hX0 : X = 0 from sub_eq_zero.mp hX0
  -- the truncated identity in Mellin form
  have htrunc : ∀ T : ℝ, 2 ≤ T →
      ∫ v in Set.Ioi (0 : ℝ), (v : ℂ) ^ s * partialScatterPart Q c (Set.Icc 2 T) v / (v : ℂ) ^ 3 =
        c ^ 2 * Φ * ∫ v in Set.Ioi (0 : ℝ),
          growthProfile (Set.Icc 2 T) v * (v : ℂ) ^ (2 - s) / (v : ℂ) ^ 3 := by
    intro T hT
    have hcpow : ∀ a : ℂ, ContinuousOn (fun v : ℝ => (v : ℂ) ^ a) (Set.Icc 2 T) := fun a v hv =>
      ((continuousAt_cpow_const (Complex.ofReal_mem_slitPlane.mpr (by linarith [hv.1]))).comp
        Complex.continuous_ofReal.continuousAt).continuousWithinAt
    have hden : ContinuousOn (fun v : ℝ => (v : ℂ) ^ 3) (Set.Icc 2 T) :=
      (Complex.continuous_ofReal.pow 3).continuousOn
    have hne : ∀ v ∈ Set.Icc 2 T, (v : ℂ) ^ 3 ≠ 0 := fun v hv =>
      pow_ne_zero 3 (Complex.ofReal_ne_zero.mpr (by linarith [hv.1]))
    have I1 := integrableOn_partialScatterPart Q hQ c (Set.Icc 2 T) (fun t ht => ht.1) measurableSet_Icc s hs
    have I2 := growthProfile_mul_integrableOn T (fun v => periodArea * c ^ 2 * (v : ℂ) ^ s / (v : ℂ) ^ 3)
      ((continuousOn_const.mul (hcpow s)).div hden hne)
    have I3 := growthProfile_mul_integrableOn T (fun v => (v : ℂ) ^ (2 - s) / (v : ℂ) ^ 3)
      ((hcpow (2 - s)).div hden hne)
    have hint := integrableOn_unfolded_of_strip (partialSubtraction Q c (Set.Icc 2 T))
      (partialSubtraction_measurable Q c _ measurableSet_Icc) (‖c‖ ^ 2 * (4 * T ^ ((4 : ℝ) / 3))) T
      (by linarith) (fun z v hv => norm_partialSubtraction_le Q c hT _ subset_rfl _) (fun z v hv hvT => by
        rw [partialSubtraction_upper Q hQ c _ (fun t ht => ht.1) z v hv (by linarith), growthProfile,
          Set.indicator_of_notMem (fun h => absurd h.2 (not_le.mpr hvT)), mul_zero]) s hs2
    have hunf := integral_mul_hyperbolicEisenstein_eq_constantTerm (partialSubtraction Q c (Set.Icc 2 T))
      (partialSubtraction_automorphy Q c _) s hint
    rw [integral_partialSubtraction_trunc_mul_eisenstein Q hQ c hT s hs2] at hunf
    have hsplit : ∫ v in Set.Ioi (0 : ℝ), (v : ℂ) ^ s *
          (∫ z in periodDomain, partialSubtraction Q c (Set.Icc 2 T) (cuspCoordinateLift (v, z))) /
            (v : ℂ) ^ 3 =
        (∫ v in Set.Ioi (0 : ℝ), (v : ℂ) ^ s * partialScatterPart Q c (Set.Icc 2 T) v / (v : ℂ) ^ 3) +
          ∫ v in Set.Ioi (0 : ℝ), growthProfile (Set.Icc 2 T) v *
            (periodArea * c ^ 2 * (v : ℂ) ^ s / (v : ℂ) ^ 3) := by
      rw [← integral_add I1 I2]
      refine setIntegral_congr_fun measurableSet_Ioi fun v _ => ?_
      simp only [partialScatterPart, cuspConstantTerm]
      ring
    have hright : c ^ 2 * ∫ v in Set.Ioi (0 : ℝ), growthProfile (Set.Icc 2 T) v *
          (periodArea * (v : ℂ) ^ s + Φ * (v : ℂ) ^ (2 - s)) / (v : ℂ) ^ 3 =
        (∫ v in Set.Ioi (0 : ℝ), growthProfile (Set.Icc 2 T) v *
            (periodArea * c ^ 2 * (v : ℂ) ^ s / (v : ℂ) ^ 3)) +
          c ^ 2 * Φ * ∫ v in Set.Ioi (0 : ℝ), growthProfile (Set.Icc 2 T) v *
            ((v : ℂ) ^ (2 - s) / (v : ℂ) ^ 3) := by
      rw [← integral_const_mul, ← integral_const_mul, ← integral_add I2 (I3.const_mul _)]
      refine setIntegral_congr_fun measurableSet_Ioi fun v _ => ?_
      ring
    rw [hsplit, hright] at hunf
    have hfin : ∫ v in Set.Ioi (0 : ℝ), growthProfile (Set.Icc 2 T) v * (v : ℂ) ^ (2 - s) / (v : ℂ) ^ 3 =
        ∫ v in Set.Ioi (0 : ℝ), growthProfile (Set.Icc 2 T) v * ((v : ℂ) ^ (2 - s) / (v : ℂ) ^ 3) :=
      setIntegral_congr_fun measurableSet_Ioi fun v _ => mul_div_assoc _ _ _
    rw [hfin]
    linear_combination -hunf
  -- the two error terms
  have hσ1 : 0 < s.re - 10 / 3 := by linarith
  have hσ2 : 0 < s.re - 4 / 3 := by linarith
  set C' := ‖c‖ ^ 2 * 4 * periodAreaReal
  have hbound : ∀ T : ℝ, 2 ≤ T → ‖X‖ ≤ 2 * C' / (s.re - 10 / 3) * T ^ (-(s.re - 10 / 3)) +
      ‖c ^ 2 * Φ‖ / (s.re - 4 / 3) * T ^ (-(s.re - 4 / 3)) := by
    intro T hT
    have hT0 : 0 < T := by linarith
    have hX : X = (∫ v in Set.Ioi (0 : ℝ), (v : ℂ) ^ s *
          (partialScatterPart Q c (Set.Ici 2) v - partialScatterPart Q c (Set.Icc 2 T) v) / (v : ℂ) ^ 3) -
        c ^ 2 * Φ * ∫ v in Set.Ioi (0 : ℝ),
          (growthProfile (Set.Ici 2) v - growthProfile (Set.Icc 2 T) v) * (v : ℂ) ^ (2 - s) / (v : ℂ) ^ 3 := by
      have J1 := integrableOn_partialScatterPart Q hQ c (Set.Ici 2) le_rfl measurableSet_Ici s hs
      have J2 := integrableOn_partialScatterPart Q hQ c (Set.Icc 2 T) (fun t ht => ht.1) measurableSet_Icc s hs
      have J3 := integrableOn_growthProfile_full s (by linarith)
      have J4 : IntegrableOn (fun v : ℝ => growthProfile (Set.Icc 2 T) v * (v : ℂ) ^ (2 - s) / (v : ℂ) ^ 3)
          (Set.Ioi 0) := by
        have := growthProfile_mul_integrableOn T (fun v => (v : ℂ) ^ (2 - s) / (v : ℂ) ^ 3)
          ((ContinuousOn.div (fun v hv => ((continuousAt_cpow_const (Complex.ofReal_mem_slitPlane.mpr
            (by linarith [hv.1]))).comp Complex.continuous_ofReal.continuousAt).continuousWithinAt)
            (Complex.continuous_ofReal.pow 3).continuousOn fun v hv =>
              pow_ne_zero 3 (Complex.ofReal_ne_zero.mpr (by linarith [hv.1]))))
        exact this.congr_fun (fun v _ => (mul_div_assoc _ _ _).symm) measurableSet_Ioi
      have e1 : ∫ v in Set.Ioi (0 : ℝ), (v : ℂ) ^ s *
          (partialScatterPart Q c (Set.Ici 2) v - partialScatterPart Q c (Set.Icc 2 T) v) / (v : ℂ) ^ 3 =
          (∫ v in Set.Ioi (0 : ℝ), (v : ℂ) ^ s * partialScatterPart Q c (Set.Ici 2) v / (v : ℂ) ^ 3) -
            ∫ v in Set.Ioi (0 : ℝ), (v : ℂ) ^ s * partialScatterPart Q c (Set.Icc 2 T) v / (v : ℂ) ^ 3 := by
        rw [← integral_sub J1 J2]
        refine setIntegral_congr_fun measurableSet_Ioi fun v _ => ?_
        ring
      have e2 : ∫ v in Set.Ioi (0 : ℝ),
          (growthProfile (Set.Ici 2) v - growthProfile (Set.Icc 2 T) v) * (v : ℂ) ^ (2 - s) / (v : ℂ) ^ 3 =
          (∫ v in Set.Ioi (0 : ℝ), growthProfile (Set.Ici 2) v * (v : ℂ) ^ (2 - s) / (v : ℂ) ^ 3) -
            ∫ v in Set.Ioi (0 : ℝ), growthProfile (Set.Icc 2 T) v * (v : ℂ) ^ (2 - s) / (v : ℂ) ^ 3 := by
        rw [← integral_sub J3 J4]
        refine setIntegral_congr_fun measurableSet_Ioi fun v _ => ?_
        ring
      rw [e1, e2, htrunc T hT, hX]
      ring
    -- first error term: supported on `(0, 1/T)`
    have hb1 : ‖∫ v in Set.Ioi (0 : ℝ), (v : ℂ) ^ s *
        (partialScatterPart Q c (Set.Ici 2) v - partialScatterPart Q c (Set.Icc 2 T) v) / (v : ℂ) ^ 3‖ ≤
        2 * C' / (s.re - 10 / 3) * T ^ (-(s.re - 10 / 3)) := by
      have hsub : ∫ v in Set.Ioi (0 : ℝ), (v : ℂ) ^ s *
          (partialScatterPart Q c (Set.Ici 2) v - partialScatterPart Q c (Set.Icc 2 T) v) / (v : ℂ) ^ 3 =
          ∫ v in Set.Ioc 0 (1 / T), (v : ℂ) ^ s *
            (partialScatterPart Q c (Set.Ici 2) v - partialScatterPart Q c (Set.Icc 2 T) v) / (v : ℂ) ^ 3 := by
        refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi Set.Ioc_subset_Ioi_self
          fun v hv => ?_
        have hv0 : 0 < v := hv.1
        have hvT : 1 / T ≤ v := by
          by_contra h
          exact hv.2 ⟨hv0, (not_le.mp h).le⟩
        rw [partialScatterPart_truncate Q hQ c hT v hv0 hvT, sub_self, mul_zero, zero_div]
      rw [hsub]
      have hT2 : 1 / T ≤ 1 / 2 := by
        apply div_le_div_of_nonneg_left zero_le_one (by norm_num) hT
      have hgi : IntegrableOn (fun v : ℝ => 2 * C' * v ^ (s.re - 13 / 3)) (Set.Ioc 0 (1 / T)) := by
        have := intervalIntegral.intervalIntegrable_rpow' (r := s.re - 13 / 3) (by linarith)
          (a := 0) (b := 1 / T)
        exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le (by positivity)).mp this).const_mul _
      refine (norm_integral_le_of_norm_le hgi (ae_restrict_of_forall_mem measurableSet_Ioc
        fun v hv => ?_)).trans (le_of_eq ?_)
      · have hv0 := hv.1
        have hv2 : v ≤ 1 / 2 := hv.2.trans hT2
        have hb1' := norm_partialScatterPart_small Q c (Set.Ici 2) le_rfl v hv0 hv2
        have hb2' := norm_partialScatterPart_small Q c (Set.Icc 2 T) (fun t ht => ht.1) v hv0 hv2
        have hpow : (1 / v) ^ ((4 : ℝ) / 3) = v ^ (-((4 : ℝ) / 3)) := by
          rw [one_div, Real.inv_rpow hv0.le, Real.rpow_neg hv0.le]
        rw [hpow] at hb1' hb2'
        rw [norm_div, norm_mul, norm_pow, Complex.norm_cpow_eq_rpow_re_of_pos hv0, Complex.norm_real,
          Real.norm_of_nonneg hv0.le]
        have htri := norm_sub_le (partialScatterPart Q c (Set.Ici 2) v) (partialScatterPart Q c (Set.Icc 2 T) v)
        have he : v ^ s.re * (2 * (‖c‖ ^ 2 * (4 * v ^ (-((4 : ℝ) / 3))) * periodAreaReal)) / v ^ 3 =
            2 * C' * v ^ (s.re - 13 / 3) := by
          rw [show s.re - 13 / 3 = s.re + (-((4 : ℝ) / 3)) - 3 by ring, Real.rpow_sub hv0,
            Real.rpow_add hv0]
          norm_cast
          ring
        calc v ^ s.re * ‖partialScatterPart Q c (Set.Ici 2) v - partialScatterPart Q c (Set.Icc 2 T) v‖ / v ^ 3
            ≤ v ^ s.re * (2 * (‖c‖ ^ 2 * (4 * v ^ (-((4 : ℝ) / 3))) * periodAreaReal)) / v ^ 3 := by
              gcongr
              linarith
          _ = 2 * C' * v ^ (s.re - 13 / 3) := he
      · rw [integral_const_mul, ← intervalIntegral.integral_of_le (by positivity),
          integral_rpow (Or.inl (by linarith)), Real.zero_rpow (by linarith), sub_zero,
          show s.re - 13 / 3 + 1 = s.re - 10 / 3 by ring, one_div, Real.inv_rpow hT0.le,
          ← Real.rpow_neg hT0.le]
        field_simp
    -- second error term: supported on `(T, ∞)`
    have hb2 : ‖∫ v in Set.Ioi (0 : ℝ),
        (growthProfile (Set.Ici 2) v - growthProfile (Set.Icc 2 T) v) * (v : ℂ) ^ (2 - s) / (v : ℂ) ^ 3‖ ≤
        1 / (s.re - 4 / 3) * T ^ (-(s.re - 4 / 3)) := by
      have hdiff : ∀ v, growthProfile (Set.Ici 2) v - growthProfile (Set.Icc 2 T) v =
          (Set.Ioi T).indicator (fun v => ((v ^ ((4 : ℝ) / 3) : ℝ) : ℂ)) v := by
        intro v
        by_cases h2 : 2 ≤ v
        · by_cases hT' : v ≤ T
          · simp [growthProfile, Set.indicator, h2, hT', not_lt.mpr hT']
          · simp [growthProfile, Set.indicator, h2, hT', lt_of_not_ge hT']
        · have hnT : ¬T < v := fun h => h2 (by linarith)
          simp [growthProfile, Set.indicator, h2, hnT]
      have hsub : ∫ v in Set.Ioi (0 : ℝ),
          (growthProfile (Set.Ici 2) v - growthProfile (Set.Icc 2 T) v) * (v : ℂ) ^ (2 - s) / (v : ℂ) ^ 3 =
          ∫ v in Set.Ioi T,
            (growthProfile (Set.Ici 2) v - growthProfile (Set.Icc 2 T) v) * (v : ℂ) ^ (2 - s) / (v : ℂ) ^ 3 := by
        refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
          (Set.Ioi_subset_Ioi hT0.le) fun v hv => ?_
        rw [hdiff, Set.indicator_of_notMem hv.2, zero_mul, zero_div]
      rw [hsub]
      have hgi : IntegrableOn (fun v : ℝ => v ^ ((1 : ℝ) / 3 - s.re)) (Set.Ioi T) :=
        integrableOn_Ioi_rpow_of_lt (by linarith) hT0
      refine (norm_integral_le_of_norm_le hgi (ae_restrict_of_forall_mem measurableSet_Ioi
        fun v (hv : T < v) => ?_)).trans (le_of_eq ?_)
      · have hv0 : 0 < v := by linarith
        rw [hdiff, Set.indicator_of_mem (show v ∈ Set.Ioi T from hv), norm_div, norm_mul, norm_pow,
          Complex.norm_cpow_eq_rpow_re_of_pos hv0, Complex.norm_real, Complex.norm_real,
          Real.norm_of_nonneg hv0.le, Real.norm_of_nonneg (Real.rpow_nonneg hv0.le _), Complex.sub_re,
          Complex.re_ofNat, show (1 : ℝ) / 3 - s.re = (4 : ℝ) / 3 + (2 - s.re) - 3 by ring]
        conv_rhs => rw [Real.rpow_sub hv0, Real.rpow_add hv0]
        norm_cast
      · rw [integral_Ioi_rpow_of_lt (by linarith) hT0, show (1 : ℝ) / 3 - s.re + 1 = -(s.re - 4 / 3) by ring]
        field_simp
    rw [hX]
    calc ‖_ - _‖ ≤ ‖∫ v in Set.Ioi (0 : ℝ), (v : ℂ) ^ s *
          (partialScatterPart Q c (Set.Ici 2) v - partialScatterPart Q c (Set.Icc 2 T) v) / (v : ℂ) ^ 3‖ +
        ‖c ^ 2 * Φ‖ * ‖∫ v in Set.Ioi (0 : ℝ),
          (growthProfile (Set.Ici 2) v - growthProfile (Set.Icc 2 T) v) * (v : ℂ) ^ (2 - s) / (v : ℂ) ^ 3‖ := by
          rw [← norm_mul]
          exact norm_sub_le _ _
      _ ≤ 2 * C' / (s.re - 10 / 3) * T ^ (-(s.re - 10 / 3)) +
          ‖c ^ 2 * Φ‖ * (1 / (s.re - 4 / 3) * T ^ (-(s.re - 4 / 3))) := by gcongr
      _ = _ := by ring
  have hlim : Tendsto (fun T : ℝ => 2 * C' / (s.re - 10 / 3) * T ^ (-(s.re - 10 / 3)) +
      ‖c ^ 2 * Φ‖ / (s.re - 4 / 3) * T ^ (-(s.re - 4 / 3))) atTop (𝓝 0) := by
    have h1 := (tendsto_rpow_neg_atTop hσ1).const_mul (2 * C' / (s.re - 10 / 3))
    have h2 := (tendsto_rpow_neg_atTop hσ2).const_mul (‖c ^ 2 * Φ‖ / (s.re - 4 / 3))
    simpa using h1.add h2
  have hle : ‖X‖ ≤ 0 := ge_of_tendsto hlim ((eventually_ge_atTop 2).mono hbound)
  exact norm_le_zero_iff.mp hle

end GaloisForLFunctions.SpectralTheoryOfTheCubicCover
