import GaloisForLFunctions.HTGeometry.TateThetaCompactOpen
import GaloisForLFunctions.HTGeometry.TateThetaDivisor
import GaloisForLFunctions.Bottcher.AnnulusRoot

/-!
# Tate divisor-to-winding transgression and repaired observer
-/

open Complex Filter Topology Set

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Integral powers of the positive quarter nome are injective. -/
theorem TateQuarterNome.zpow_injective (r : TateQuarterNome) :
    Function.Injective (fun n : ℤ => (r.root : ℂ) ^ n) := by
  intro m n hmn
  have habs := congrArg norm hmn
  simp only [norm_zpow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos r.root_pos] at habs
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact (ne_of_lt (zpow_lt_zpow_right_of_lt_one₀
      r.root_pos r.root_lt_one hlt)) habs.symm
  · exact (ne_of_lt (zpow_lt_zpow_right_of_lt_one₀
      r.root_pos r.root_lt_one hgt)) habs

theorem one_not_tateThetaZeroOrbit (r : TateQuarterNome) :
    ¬tateThetaZeroOrbit r 1 := by
  rintro ⟨k, hk⟩
  have hexp : (0 : ℤ) = 4 * k + 1 :=
    r.zpow_injective (by simpa using hk)
  omega

theorem one_not_tateThetaPoleOrbit (r : TateQuarterNome) :
    ¬tateThetaPoleOrbit r 1 := by
  rintro ⟨k, hk⟩
  have hexp : (0 : ℤ) = 4 * k + 3 :=
    r.zpow_injective (by simpa using hk)
  omega

/-- The pointing denominator is nonzero for every quarter nome, not merely eventually. -/
theorem tateThetaGauge_one_ne_zero (r : TateQuarterNome) :
    tateThetaGauge r 1 ≠ 0 := by
  have hnum : tateThetaGaugeNumerator r 1 ≠ 0 := by
    unfold tateThetaGaugeNumerator
    apply mul_ne_zero
    · exact mul_ne_zero (neg_ne_zero.mpr r.root_complex_ne_zero) (by
        intro hzero
        apply one_not_tateThetaZeroOrbit r
        exact (tateThetaNumerator_eq_zero_iff r 1).mp
          (mul_eq_zero.mpr (Or.inl hzero)))
    · intro hzero
      apply one_not_tateThetaZeroOrbit r
      exact (tateThetaNumerator_eq_zero_iff r 1).mp
        (mul_eq_zero.mpr (Or.inr hzero))
  have hden : tateThetaGaugeDenominator r 1 ≠ 0 := by
    unfold tateThetaGaugeDenominator
    apply pow_ne_zero
    intro hzero
    exact one_not_tateThetaPoleOrbit r
      ((tateThetaDenominator_eq_zero_iff r 1).mp hzero)
  rw [tateThetaGauge_eq_numerator_div_denominator]
  exact div_ne_zero hnum hden

/-- Every pointed integer-power gauge is exactly q-elliptic. -/
theorem pointedTateThetaGauge_mul_nome
    (r : TateQuarterNome) (m : ℤ) (x : ℂ) (hx : x ≠ 0) :
    pointedTateThetaGauge r m (((r.nome : EulerNome) : ℂ) * x) =
      pointedTateThetaGauge r m x := by
  unfold pointedTateThetaGauge
  rw [tateThetaGauge_mul_nome r x hx]

/-- The normalized Tate gauge has the same divisor as the unnormalized one. -/
theorem meromorphicOrderAt_normalizedTateThetaGauge
    (r : TateQuarterNome) (x : {z : ℂ // z ≠ 0}) :
    meromorphicOrderAt
        (fun z : ℂ => tateThetaGauge r z / tateThetaGauge r 1) x =
      tateThetaDivisorMultiplicity r x := by
  have hnum : MeromorphicAt (tateThetaGauge r) x := by
    rw [tateThetaGauge_eq_numerator_div_denominator]
    exact (analyticAt_tateThetaGaugeNumerator r x.property).meromorphicAt.div
      (analyticAt_tateThetaGaugeDenominator r x.property).meromorphicAt
  have hden : MeromorphicAt (fun _ : ℂ => tateThetaGauge r 1) x :=
    analyticAt_const.meromorphicAt
  have hfun : (fun z : ℂ => tateThetaGauge r z / tateThetaGauge r 1) =
      tateThetaGauge r / (fun _ : ℂ => tateThetaGauge r 1) := by
    funext z
    rfl
  rw [hfun, meromorphicOrderAt_div hnum hden,
    meromorphicOrderAt_tateThetaGauge_exact r x, meromorphicOrderAt_const]
  simp [tateThetaGauge_one_ne_zero r]

/-- Integer powers scale the complete escaping divisor, including negative weights. -/
theorem meromorphicOrderAt_pointedTateThetaGauge_exact
    (r : TateQuarterNome) (m : ℤ) (x : {z : ℂ // z ≠ 0}) :
    meromorphicOrderAt (pointedTateThetaGauge r m) x =
      (m : WithTop ℤ) * tateThetaDivisorMultiplicity r x := by
  have hnum : MeromorphicAt (tateThetaGauge r) x := by
    rw [tateThetaGauge_eq_numerator_div_denominator]
    exact (analyticAt_tateThetaGaugeNumerator r x.property).meromorphicAt.div
      (analyticAt_tateThetaGaugeDenominator r x.property).meromorphicAt
  have hden : MeromorphicAt (fun _ : ℂ => tateThetaGauge r 1) x :=
    analyticAt_const.meromorphicAt
  have hnormalized : MeromorphicAt
      (fun z : ℂ => tateThetaGauge r z / tateThetaGauge r 1) x := hnum.div hden
  have hzpow := meromorphicOrderAt_zpow (n := m) hnormalized
  have hfun :
      (fun z : ℂ => tateThetaGauge r z / tateThetaGauge r 1) ^ m =
        pointedTateThetaGauge r m := by
    funext z
    rfl
  rw [hfun, meromorphicOrderAt_normalizedTateThetaGauge r x] at hzpow
  exact hzpow

/-! ## Boundary characters and the repaired observer -/

/-- Finite algebraic characters of `ℂˣ`, in their classified Laurent-monomial normal form
`c x^m` with `c ≠ 0`. -/
structure LaurentBoundaryCharacter where
  coefficient : Units ℂ
  exponent : ℤ

namespace LaurentBoundaryCharacter

/-- Evaluation of the Laurent character on the punctured complex line. -/
def eval (χ : LaurentBoundaryCharacter) (x : {z : ℂ // z ≠ 0}) : ℂ :=
  (χ.coefficient : ℂ) * (x : ℂ) ^ χ.exponent

/-- Totalized meromorphic representative of the Laurent character. -/
def toFunction (χ : LaurentBoundaryCharacter) (x : ℂ) : ℂ :=
  (χ.coefficient : ℂ) * x ^ χ.exponent

/-- Normalized monomial of winding `m`. -/
def monomial (m : ℤ) : LaurentBoundaryCharacter where
  coefficient := 1
  exponent := m

/-- Pointing at `1`; this is exactly the nonzero coefficient. -/
def pointing (χ : LaurentBoundaryCharacter) : Units ℂ := χ.coefficient

/-- Node charge of an algebraic boundary character. -/
def nodeCharge (χ : LaurentBoundaryCharacter) : ℤ := χ.exponent

@[simp]
theorem eval_one (χ : LaurentBoundaryCharacter) :
    χ.eval ⟨1, one_ne_zero⟩ = (χ.pointing : ℂ) := by
  simp [eval, pointing]

@[simp]
theorem eval_monomial (m : ℤ) (x : {z : ℂ // z ≠ 0}) :
    (monomial m).eval x = (x : ℂ) ^ m := by
  simp [eval, monomial]

@[simp]
theorem nodeCharge_monomial (m : ℤ) : (monomial m).nodeCharge = m := rfl

@[simp]
theorem pointing_monomial (m : ℤ) : (monomial m).pointing = 1 := rfl

/-- The normalized characters are exactly `{x^m : m ∈ ℤ}`. -/
theorem pointing_eq_one_iff_exists_eq_monomial (χ : LaurentBoundaryCharacter) :
    χ.pointing = 1 ↔ ∃ m : ℤ, χ = monomial m := by
  constructor
  · intro h
    refine ⟨χ.exponent, ?_⟩
    cases χ with
    | mk c m =>
        simp only [pointing] at h
        subst c
        rfl
  · rintro ⟨m, rfl⟩
    exact pointing_monomial m

/-- Interior divisor plus pointing: every boundary unit has empty interior divisor, so this
observer retains only the pointing. -/
def divisorPointingObserver (χ : LaurentBoundaryCharacter) : PUnit × Units ℂ :=
  (PUnit.unit, χ.pointing)

/-- Repaired observer retaining interior divisor, node charge, and pointing. -/
def repairedObserver (χ : LaurentBoundaryCharacter) : PUnit × (ℤ × Units ℂ) :=
  (PUnit.unit, χ.nodeCharge, χ.pointing)

/-- Interior divisor plus pointing is not conservative. -/
theorem not_injective_divisorPointingObserver :
    ¬Function.Injective divisorPointingObserver := by
  intro hinj
  have heq : monomial 0 = monomial 1 := hinj (by simp [divisorPointingObserver])
  have hexp := congrArg exponent heq
  norm_num [monomial] at hexp

/-- Omitting node charge leaves exactly the normalized kernel `{x^m : m ∈ ℤ}`. -/
theorem divisorPointingObserver_fiber_one_eq_range_monomial :
    {χ : LaurentBoundaryCharacter |
      divisorPointingObserver χ = divisorPointingObserver (monomial 0)} =
      Set.range monomial := by
  ext χ
  constructor
  · intro hχ
    have hp : χ.pointing = 1 := by
      have := congrArg Prod.snd hχ
      simpa [divisorPointingObserver] using this
    obtain ⟨m, hm⟩ := (pointing_eq_one_iff_exists_eq_monomial χ).mp hp
    exact ⟨m, hm.symm⟩
  · rintro ⟨m, rfl⟩
    simp [divisorPointingObserver]

/-- Interior divisor, node charge, and pointing reconstruct every algebraic boundary character. -/
theorem repairedObserver_injective : Function.Injective repairedObserver := by
  intro χ ψ h
  have hcharge : χ.exponent = ψ.exponent := by
    have := congrArg (fun p : PUnit × (ℤ × Units ℂ) => p.2.1) h
    exact this
  have hcoeff : χ.coefficient = ψ.coefficient := by
    have := congrArg (fun p : PUnit × (ℤ × Units ℂ) => p.2.2) h
    exact this
  cases χ
  cases ψ
  simp_all

end LaurentBoundaryCharacter

/-! ## Exact charge and winding -/

/-- Oriented Tate-node charge extracted from zero and pole orders at valuations `1/4` and `3/4`. -/
def tateEscapingNodeCharge (zeroOrder poleOrder : ℤ) : ℚ :=
  -((zeroOrder : ℚ) * (1 / 4) + (poleOrder : ℚ) * (3 / 4))

/-- The divisor `2m[r]-2m[r³]` has node charge exactly `m`. -/
theorem tateEscapingNodeCharge_eq (m : ℤ) :
    tateEscapingNodeCharge (2 * m) (-2 * m) = (m : ℚ) := by
  simp only [tateEscapingNodeCharge]
  push_cast
  ring

/-- The normalized monomial has analytic winding `m·2πi` around every positive circle. -/
theorem winding_integral_laurentMonomial
    {ρ : ℝ} (hρ : 0 < ρ) (m : ℤ) :
    (∫ θ in (0 : ℝ)..(2 * Real.pi),
      logDeriv (LaurentBoundaryCharacter.monomial m).toFunction
          (circleMap 0 ρ θ) *
        (circleMap 0 ρ θ * Complex.I)) =
      (m : ℂ) * (2 * Real.pi * Complex.I) := by
  have hfun : (LaurentBoundaryCharacter.monomial m).toFunction =
      (fun w : ℂ => w ^ m) := by
    funext w
    simp [LaurentBoundaryCharacter.toFunction, LaurentBoundaryCharacter.monomial]
  rw [hfun]
  exact Bottcher.winding_zpow_circle hρ m

/-- The zero-orbit representative has order `2m` for the pointed charge-`m` gauge. -/
theorem meromorphicOrderAt_pointedTateThetaGauge_zeroRepresentative
    (r : TateQuarterNome) (m : ℤ) :
    meromorphicOrderAt (pointedTateThetaGauge r m) (r.root : ℂ) =
      (((2 * m : ℤ) : WithTop ℤ)) := by
  let x : {z : ℂ // z ≠ 0} := ⟨(r.root : ℂ), r.root_complex_ne_zero⟩
  have hzero : tateThetaZeroOrbit r x := by
    exact ⟨0, by simp [x]⟩
  have h := meromorphicOrderAt_pointedTateThetaGauge_exact r m x
  rw [tateThetaDivisorMultiplicity, if_pos hzero] at h
  rw [show (((2 * m : ℤ) : WithTop ℤ)) = (m : WithTop ℤ) * 2 by
    push_cast
    simp [mul_comm]]
  simpa [x] using h

/-- The pole-orbit representative has order `-2m` for the pointed charge-`m` gauge. -/
theorem meromorphicOrderAt_pointedTateThetaGauge_poleRepresentative
    (r : TateQuarterNome) (m : ℤ) :
    meromorphicOrderAt (pointedTateThetaGauge r m) ((r.root : ℂ) ^ (3 : ℤ)) =
      (((-2 * m : ℤ) : WithTop ℤ)) := by
  let x : {z : ℂ // z ≠ 0} :=
    ⟨(r.root : ℂ) ^ (3 : ℤ), zpow_ne_zero 3 r.root_complex_ne_zero⟩
  have hpole : tateThetaPoleOrbit r x := by
    exact ⟨0, by simp [x]⟩
  have h := meromorphicOrderAt_pointedTateThetaGauge_exact r m x
  rw [tateThetaDivisorMultiplicity, if_neg
    (fun hzero => tateThetaZeroOrbit_disjoint_poleOrbit r x ⟨hzero, hpole⟩),
    if_pos hpole] at h
  rw [show (((-2 * m : ℤ) : WithTop ℤ)) = (m : WithTop ℤ) * (-2) by
    push_cast
    simp [mul_comm]]
  simpa [x] using h

/-- Exact selection-to-production conservation: escaping divisor charge and limiting winding are
the same integer `m`, with the winding realized by the analytic circle integral. -/
theorem tateTheta_nodeCharge_eq_boundaryWinding (m : ℤ) :
    tateEscapingNodeCharge (2 * m) (-2 * m) =
      (LaurentBoundaryCharacter.monomial m).nodeCharge := by
  rw [tateEscapingNodeCharge_eq]
  exact_mod_cast LaurentBoundaryCharacter.nodeCharge_monomial m

/-- Every normalized Laurent boundary character is attained locally uniformly by the explicit
pointed Tate-theta family. -/
theorem tendstoLocallyUniformlyOn_pointedTateThetaGauge_realizes_monomial
    {ι : Type*} {l : Filter ι} (r : ι → TateQuarterNome)
    (hr : Tendsto (fun i => (r i).root) l (nhds 0)) (m : ℤ) :
    TendstoLocallyUniformlyOn (fun i x => pointedTateThetaGauge (r i) m x)
      (fun x => (LaurentBoundaryCharacter.monomial m).toFunction x)
      l {x : ℂ | x ≠ 0} := by
  simpa [LaurentBoundaryCharacter.toFunction, LaurentBoundaryCharacter.monomial] using
    tendstoLocallyUniformlyOn_pointedTateThetaGauge_of_root_zero r hr m

/-! ## Escape of the complete divisor -/

theorem tateThetaGauge_eq_zero_of_zeroOrbit
    (r : TateQuarterNome) {x : ℂ} (hx : tateThetaZeroOrbit r x) :
    tateThetaGauge r x = 0 := by
  have hboth := (tateThetaZeroOrbit_iff_both_numerator_factors_zero r x).mp hx
  have hminus : multiplicativeTheta r.nome ((r.root : ℂ)⁻¹ * x) = 0 := by
    simpa using hboth.1
  simp [tateThetaGauge, hminus]

theorem tateThetaGauge_eq_zero_of_poleOrbit
    (r : TateQuarterNome) {x : ℂ} (hx : tateThetaPoleOrbit r x) :
    tateThetaGauge r x = 0 := by
  have hden := (tateThetaPoleOrbit_iff_denominator_factor_zero r x).mp hx
  have hone : multiplicativeTheta r.nome ((r.root : ℂ) * x) = 0 := by
    simpa using hden
  simp [tateThetaGauge, hone]

/-- Every compact subset of `ℂˣ` is eventually disjoint from both complete divisor orbits. -/
theorem eventually_tateTheta_divisor_avoids_compact
    {ι : Type*} {l : Filter ι} (r : ι → TateQuarterNome)
    (hr : Tendsto (fun i => (r i).root) l (nhds 0))
    {K : Set ℂ} (hK : IsCompact K) (hKzero : K ⊆ {x : ℂ | x ≠ 0}) :
    ∀ᶠ i in l, ∀ x ∈ K,
      ¬tateThetaZeroOrbit (r i) x ∧ ¬tateThetaPoleOrbit (r i) x := by
  rcases K.eq_empty_or_nonempty with hKe | hKne
  · subst K
    simp
  obtain ⟨x₀, hx₀, hx₀min⟩ :=
    hK.exists_isMinOn hKne continuous_norm.continuousOn
  have hx₀pos : 0 < ‖x₀‖ := norm_pos_iff.mpr (hKzero hx₀)
  have hopen : IsOpen {x : ℂ | x ≠ 0} := by
    change IsOpen (({0} : Set ℂ)ᶜ)
    exact isOpen_compl_singleton
  have hlocal := tendstoLocallyUniformlyOn_tateThetaGauge_of_root_zero r hr
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact hopen] at hlocal
  have huniform := hlocal K hKzero hK
  rw [Metric.tendstoUniformlyOn_iff] at huniform
  filter_upwards [huniform (‖x₀‖ / 2) (half_pos hx₀pos)] with i hi
  intro x hxK
  have hmin : ‖x₀‖ ≤ ‖x‖ := hx₀min hxK
  constructor
  · intro hzero
    have hdist := hi x hxK
    rw [id_eq, tateThetaGauge_eq_zero_of_zeroOrbit (r i) hzero, dist_zero_right] at hdist
    linarith
  · intro hpole
    have hdist := hi x hxK
    rw [id_eq, tateThetaGauge_eq_zero_of_poleOrbit (r i) hpole, dist_zero_right] at hdist
    linarith

/-- The complete divisor of every pointed charge family escapes every compact subset of `ℂˣ`. -/
theorem eventually_meromorphicOrderAt_pointedTateThetaGauge_eq_zero_on_compact
    {ι : Type*} {l : Filter ι} (r : ι → TateQuarterNome)
    (hr : Tendsto (fun i => (r i).root) l (nhds 0)) (m : ℤ)
    {K : Set ℂ} (hK : IsCompact K) (hKzero : K ⊆ {x : ℂ | x ≠ 0}) :
    ∀ᶠ i in l, ∀ x ∈ K,
      meromorphicOrderAt (pointedTateThetaGauge (r i) m) x = 0 := by
  filter_upwards [eventually_tateTheta_divisor_avoids_compact r hr hK hKzero]
    with i hi x hxK
  obtain ⟨hzero, hpole⟩ := hi x hxK
  have horder := meromorphicOrderAt_pointedTateThetaGauge_exact
    (r i) m ⟨x, hKzero hxK⟩
  rw [tateThetaDivisorMultiplicity, if_neg hzero, if_neg hpole, mul_zero] at horder
  exact horder

end

end GaloisForLFunctions.HTGeometry
