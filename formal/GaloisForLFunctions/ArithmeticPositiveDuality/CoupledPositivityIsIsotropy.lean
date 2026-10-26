import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.MaximalBlindIdealOfTheMeyerSource
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.MeyerNumericalRadicalAndMultiplicity

/-!
# Coupled positivity is isotropy, not blindness

The maximality theorem `isGreatest_meyerSharpPositiveIdeal` says that a sharp-stable convolution
ideal of the Meyer source with nonnegative trace is off-line blind. This module removes both
restrictions — sharp stability and a single channel — and computes what positivity forces.

The complex source pairing is `S(g, h) = Σ_q ĝ(ρ_q) · conj ĥ(ρ_q*)` over the multiplicity copies,
`ρ* = 1 − ρ̄` (`meyerComplexTrace_eq_tsum`), and the trace is its real part.

* **Coupled isotropy** (`coupled_isotropy`). Let channels `ι` be coupled by operators `T a b`
  acting on divisor values by symbols `τ a b`, let `Q(g) = Σ_{a,b} tr(g_a, T_{ab} g_b)`, and let `M`
  be a carrier of tuples closed under diagonal convolution by point sources. If `Q ≥ 0` on `M`, then
  at every off-line zero `ρ` the fibre of `M` at `ρ` and the fibre at `ρ*` are orthogonal for the
  coupling matrix `K_ρ(a,b) = m_ρ conj τ_{ab}(ρ*) + m_{ρ*} τ_{ba}(ρ)`.
* **Full carriers** (`coupling_vanishes_of_nonneg_on_all`): positivity on all tuples forces
  `K_ρ = 0` at every off-line zero; a coupling with `K_ρ ≠ 0` there is positive on everything
  only if `ρ` does not exist.
* **One channel** (`positive_ideal_halfBlind`): every convolution ideal with nonnegative trace is,
  at each off-line pair `{ρ, ρ*}`, blind to one of the two points. With sharp stability both sides
  follow (`le_meyerTraceBoundedIdeal_of_positive_sharp_ideal`), recovering maximality.
* **A positive ideal that is not blind** (`leftBlindIdeal`): the sources vanishing at the zeros
  left of the line form a convolution ideal with nonnegative trace
  (`meyerSourceTrace_nonneg_of_mem_leftBlindIdeal`). It is defined without zeros as the sources
  whose mixed traces stay bounded along the backward scaling flow
  (`mem_leftBlindIdeal_iff_backwardFlowBounded`); it contains the blind ideal, and equals it, or
  everything, only under RH (`leftBlindIdeal_eq_top_iff`, `meyerTraceBoundedIdeal_lt_leftBlindIdeal`).

So positivity of the Meyer form on a carrier certifies isotropy of its fibres at off-line pairs,
not blindness: an off-line zero can be seen when its reflection is not. Exhaustion of every such
carrier remains RH.
-/

open Complex Set Filter
open RHTower
open scoped ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality

open ArithmeticCastelnuovoSeveri

/-! ### 1. The complex source pairing -/

/-- The complex source pairing; its real part is `meyerSourceTrace`. -/
def meyerComplexTrace (g h : DeningerMeyerStrongLogTarget) : ℂ :=
  meyerSourceTraceDegree (deningerMeyerSourceConvolution g (deningerMeyerSourceSharp h))

/-- The trace degree is the sum of Mellin values over the multiplicity copies. -/
theorem meyerSourceTraceDegree_eq_tsum (p : DeningerMeyerStrongLogTarget) :
    meyerSourceTraceDegree p = ∑' q : XiZeroCopy, deningerMeyerStrongLogMellin p (q.1 : ℂ) :=
  deningerMeyerHilbertConvolution_opTrace p

theorem meyerSourceTrace_eq_re (g h : DeningerMeyerStrongLogTarget) :
    meyerSourceTrace g h = (meyerComplexTrace g h).re := by
  rw [meyerSourceTrace_eq_degree_product, meyerCohomologyTraceDegree_mk]
  rfl

/-- The pairing over the Xi divisor: `S(g, h) = Σ_q ĝ(ρ_q) conj ĥ(ρ_q*)`. -/
theorem meyerComplexTrace_eq_tsum (g h : DeningerMeyerStrongLogTarget) :
    meyerComplexTrace g h = ∑' q : XiZeroCopy, deningerMeyerStrongLogMellin g (q.1 : ℂ) *
      star (deningerMeyerStrongLogMellin h (meyerLineReflect q.1 : ℂ)) := by
  rw [meyerComplexTrace, meyerSourceTraceDegree_eq_tsum]
  refine tsum_congr fun q => ?_
  rw [deningerMeyerSourceConvolution_mellin, deningerMeyerSourceSharp_mellin,
    meyerLineReflect_val]

theorem summable_meyerComplexTrace (g h : DeningerMeyerStrongLogTarget) :
    Summable fun q : XiZeroCopy => deningerMeyerStrongLogMellin g (q.1 : ℂ) *
      star (deningerMeyerStrongLogMellin h (meyerLineReflect q.1 : ℂ)) := by
  refine (deningerMeyerHilbertConvolution_summable_diagonal
    (deningerMeyerSourceConvolution g (deningerMeyerSourceSharp h))).congr fun q => ?_
  rw [deningerMeyerSourceConvolution_mellin, deningerMeyerSourceSharp_mellin,
    meyerLineReflect_val]

/-- A sum over multiplicity copies of a finitely supported support function is weighted by the
multiplicities. -/
theorem tsum_copies_eq_sum (F : XiDivisorSupport → ℂ) (s : Finset XiDivisorSupport)
    (hF : ∀ σ ∉ s, F σ = 0) :
    ∑' q : XiZeroCopy, F q.1 = ∑ σ ∈ s, (xiSupportMultiplicity σ : ℂ) * F σ := by
  classical
  rw [tsum_eq_sum (s := s.sigma fun _ => Finset.univ) fun q hq =>
    hF q.1 fun h => hq (Finset.mem_sigma.mpr ⟨h, Finset.mem_univ _⟩), Finset.sum_sigma]
  refine Finset.sum_congr rfl fun σ _ => ?_
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rfl

/-- **Point-supported pairing.** If `ĝ` vanishes on the divisor outside `s`, the pairing is the
finite sum `Σ_{σ ∈ s} m_σ ĝ(σ) conj ĥ(σ*)`. -/
theorem meyerComplexTrace_of_support (g h : DeningerMeyerStrongLogTarget)
    (s : Finset XiDivisorSupport)
    (hs : ∀ σ ∉ s, deningerMeyerStrongLogMellin g (σ : ℂ) = 0) :
    meyerComplexTrace g h = ∑ σ ∈ s, (xiSupportMultiplicity σ : ℂ) *
      (deningerMeyerStrongLogMellin g (σ : ℂ) *
        star (deningerMeyerStrongLogMellin h (meyerLineReflect σ : ℂ))) := by
  rw [meyerComplexTrace_eq_tsum]
  exact tsum_copies_eq_sum (fun σ => deningerMeyerStrongLogMellin g (σ : ℂ) *
    star (deningerMeyerStrongLogMellin h (meyerLineReflect σ : ℂ))) s
    fun σ hσ => by rw [hs σ hσ, zero_mul]

theorem meyerLineReflect_ne_self {ρ : XiDivisorSupport} (hoff : (ρ : ℂ).re ≠ 1 / 2) :
    meyerLineReflect ρ ≠ ρ := by
  intro he
  have hr := congrArg (fun q : XiDivisorSupport => (q : ℂ).re) he
  change 1 - (ρ : ℂ).re = (ρ : ℂ).re at hr
  exact hoff (by linarith only [hr])

/-- Mellin values of a source convolved with a point source. -/
theorem mellin_conv_pointSource (g : DeningerMeyerStrongLogTarget) (ρ σ : XiDivisorSupport) :
    deningerMeyerStrongLogMellin (deningerMeyerSourceConvolution g (meyerPointSource ρ))
      (σ : ℂ) = if σ = ρ then deningerMeyerStrongLogMellin g (ρ : ℂ) else 0 := by
  rw [deningerMeyerSourceConvolution_mellin, meyerPointSource_values]
  split_ifs with h
  · rw [h, mul_one]
  · rw [mul_zero]

/-! ### 2. Coupled isotropy -/

variable {ι : Type*} [Fintype ι]

/-- `T` acts on divisor values by the symbol `τ`. -/
def IsDivisorMultiplier (T : DeningerMeyerStrongLogTarget →ₗ[ℂ] DeningerMeyerStrongLogTarget)
    (τ : XiDivisorSupport → ℂ) : Prop :=
  ∀ (g : DeningerMeyerStrongLogTarget) (σ : XiDivisorSupport),
    deningerMeyerStrongLogMellin (T g) (σ : ℂ) = τ σ * deningerMeyerStrongLogMellin g (σ : ℂ)

/-- The coupled trace form `Q(g) = Σ_{a,b} tr(g_a, T_{ab} g_b)`. -/
def coupledTrace
    (T : ι → ι → DeningerMeyerStrongLogTarget →ₗ[ℂ] DeningerMeyerStrongLogTarget)
    (g : ι → DeningerMeyerStrongLogTarget) : ℝ :=
  ∑ a, ∑ b, meyerSourceTrace (g a) (T a b (g b))

/-- A carrier of tuples is point-stable when diagonal convolution by any point source preserves
it. -/
def PointStable (M : Submodule ℂ (ι → DeningerMeyerStrongLogTarget)) : Prop :=
  ∀ g ∈ M, ∀ ρ : XiDivisorSupport,
    (fun a => deningerMeyerSourceConvolution (g a) (meyerPointSource ρ)) ∈ M

/-- The coupling matrix at an off-line pair. -/
def couplingMatrix (τ : ι → ι → XiDivisorSupport → ℂ) (ρ : XiDivisorSupport) (a b : ι) : ℂ :=
  (xiSupportMultiplicity ρ : ℂ) * star (τ a b (meyerLineReflect ρ)) +
    (xiSupportMultiplicity (meyerLineReflect ρ) : ℂ) * τ b a ρ

/-- The isotropy pairing of a `ρ`-fibre vector `x` and a `ρ*`-fibre vector `y`. -/
def isotropyPairing (τ : ι → ι → XiDivisorSupport → ℂ) (ρ : XiDivisorSupport)
    (x y : ι → ℂ) : ℂ :=
  ∑ a, ∑ b, x a * star (y b) * couplingMatrix τ ρ a b

/-- The coupled form on a two-point packet with `ρ`-values `α x` and `ρ*`-values `y` is
`Re(α · ⟨x, y⟩_K)`. -/
theorem coupledTrace_twoPoint
    {T : ι → ι → DeningerMeyerStrongLogTarget →ₗ[ℂ] DeningerMeyerStrongLogTarget}
    {τ : ι → ι → XiDivisorSupport → ℂ} (hT : ∀ a b, IsDivisorMultiplier (T a b) (τ a b))
    {ρ : XiDivisorSupport} (hoff : (ρ : ℂ).re ≠ 1 / 2) (α : ℂ)
    (u : ι → DeningerMeyerStrongLogTarget) (x y : ι → ℂ)
    (hu : ∀ (a : ι) (σ : XiDivisorSupport), deningerMeyerStrongLogMellin (u a) (σ : ℂ) =
      if σ = ρ then α * x a else if σ = meyerLineReflect ρ then y a else 0) :
    coupledTrace T u = (α * isotropyPairing τ ρ x y).re := by
  classical
  have hne : meyerLineReflect ρ ≠ ρ := meyerLineReflect_ne_self hoff
  have hu_ρ (a : ι) : deningerMeyerStrongLogMellin (u a) (ρ : ℂ) = α * x a := by
    rw [hu, if_pos rfl]
  have hu_ρ' (a : ι) : deningerMeyerStrongLogMellin (u a) (meyerLineReflect ρ : ℂ) = y a := by
    rw [hu, if_neg hne, if_pos rfl]
  have hpair (a b : ι) : meyerComplexTrace (u a) (T a b (u b)) =
      (xiSupportMultiplicity ρ : ℂ) * (α * x a * star (τ a b (meyerLineReflect ρ) * y b)) +
        (xiSupportMultiplicity (meyerLineReflect ρ) : ℂ) * (y a * star (τ a b ρ * (α * x b))) := by
    rw [meyerComplexTrace_of_support (u a) (T a b (u b)) {ρ, meyerLineReflect ρ}
      fun σ hσ => by
        rw [hu]
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hσ
        rw [if_neg hσ.1, if_neg hσ.2],
      Finset.sum_pair (Ne.symm hne), hT, hT, meyerLineReflect_sq, hu_ρ, hu_ρ', hu_ρ, hu_ρ']
  unfold coupledTrace
  simp only [meyerSourceTrace_eq_re, hpair]
  simp only [← Complex.re_sum]
  -- Collect the two halves `α Z₁ + conj α Z₂` and recombine them as `Re(α (Z₁ + conj Z₂))`.
  have hsplit : (∑ a, ∑ b, ((xiSupportMultiplicity ρ : ℂ) *
      (α * x a * star (τ a b (meyerLineReflect ρ) * y b)) +
        (xiSupportMultiplicity (meyerLineReflect ρ) : ℂ) *
          (y a * star (τ a b ρ * (α * x b))))) =
      α * (∑ a, ∑ b, (xiSupportMultiplicity ρ : ℂ) * x a * star (y b) *
          star (τ a b (meyerLineReflect ρ))) +
        star α * (∑ a, ∑ b, (xiSupportMultiplicity (meyerLineReflect ρ) : ℂ) * y a *
          star (x b) * star (τ a b ρ)) := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    simp only [star_mul']
    ring
  rw [hsplit, Complex.add_re]
  have hconj : (star α * (∑ a, ∑ b, (xiSupportMultiplicity (meyerLineReflect ρ) : ℂ) * y a *
      star (x b) * star (τ a b ρ))).re = (α * (∑ a, ∑ b,
        (xiSupportMultiplicity (meyerLineReflect ρ) : ℂ) * x a * star (y b) * τ b a ρ)).re := by
    rw [← Complex.conj_re]
    congr 1
    simp only [map_mul, map_sum, Complex.conj_natCast]
    congr 1
    · rw [starRingEnd_apply, star_star]
    · rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      simp only [starRingEnd_apply, star_star]
      ring
  rw [hconj, ← Complex.add_re, ← mul_add]
  congr 2
  unfold isotropyPairing couplingMatrix
  simp only [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

/-- **Coupled isotropy.** On a point-stable carrier with nonnegative coupled trace, the fibre at
an off-line zero `ρ` and the fibre at its reflection `ρ*` are orthogonal for the coupling matrix. -/
theorem coupled_isotropy
    {T : ι → ι → DeningerMeyerStrongLogTarget →ₗ[ℂ] DeningerMeyerStrongLogTarget}
    {τ : ι → ι → XiDivisorSupport → ℂ} (hT : ∀ a b, IsDivisorMultiplier (T a b) (τ a b))
    {M : Submodule ℂ (ι → DeningerMeyerStrongLogTarget)} (hM : PointStable M)
    (hpos : ∀ g ∈ M, 0 ≤ coupledTrace T g)
    {ρ : XiDivisorSupport} (hoff : (ρ : ℂ).re ≠ 1 / 2)
    {g g' : ι → DeningerMeyerStrongLogTarget} (hg : g ∈ M) (hg' : g' ∈ M) :
    isotropyPairing τ ρ (fun a => deningerMeyerStrongLogMellin (g a) (ρ : ℂ))
      (fun a => deningerMeyerStrongLogMellin (g' a) (meyerLineReflect ρ : ℂ)) = 0 := by
  classical
  set Z := isotropyPairing τ ρ (fun a => deningerMeyerStrongLogMellin (g a) (ρ : ℂ))
    (fun a => deningerMeyerStrongLogMellin (g' a) (meyerLineReflect ρ : ℂ))
  have hne : meyerLineReflect ρ ≠ ρ := meyerLineReflect_ne_self hoff
  set α : ℂ := -star Z
  let u : ι → DeningerMeyerStrongLogTarget := fun a =>
    α • deningerMeyerSourceConvolution (g a) (meyerPointSource ρ) +
      deningerMeyerSourceConvolution (g' a) (meyerPointSource (meyerLineReflect ρ))
  have huM : u ∈ M := M.add_mem (M.smul_mem α (hM g hg ρ)) (hM g' hg' _)
  have hu : ∀ (a : ι) (σ : XiDivisorSupport), deningerMeyerStrongLogMellin (u a) (σ : ℂ) =
      if σ = ρ then α * deningerMeyerStrongLogMellin (g a) (ρ : ℂ)
      else if σ = meyerLineReflect ρ then
        deningerMeyerStrongLogMellin (g' a) (meyerLineReflect ρ : ℂ) else 0 := by
    intro a σ
    change deningerMeyerStrongLogMellinLM (σ : ℂ) (u a) = _
    simp only [u, map_add, map_smul, smul_eq_mul]
    change α * deningerMeyerStrongLogMellin _ (σ : ℂ) + deningerMeyerStrongLogMellin _ (σ : ℂ) = _
    rw [mellin_conv_pointSource, mellin_conv_pointSource]
    by_cases h1 : σ = ρ
    · subst h1; rw [if_pos rfl, if_neg hne.symm, if_pos rfl, add_zero]
    · rw [if_neg h1, if_neg h1, mul_zero, zero_add]
  have hQ := coupledTrace_twoPoint hT hoff α u _ _ hu
  have hnn := hpos u huM
  rw [hQ] at hnn
  have hval : (α * Z).re = -Complex.normSq Z := by
    simp only [α, neg_mul, Complex.neg_re, RCLike.star_def, Complex.conj_mul']
    rw [← Complex.ofReal_pow, Complex.ofReal_re, Complex.sq_norm]
  rw [hval] at hnn
  exact Complex.normSq_eq_zero.mp (le_antisymm (by linarith) (Complex.normSq_nonneg Z))

/-- **Positivity on all tuples kills the coupling at every off-line zero.** -/
theorem coupling_vanishes_of_nonneg_on_all
    {T : ι → ι → DeningerMeyerStrongLogTarget →ₗ[ℂ] DeningerMeyerStrongLogTarget}
    {τ : ι → ι → XiDivisorSupport → ℂ} (hT : ∀ a b, IsDivisorMultiplier (T a b) (τ a b))
    (hpos : ∀ g, 0 ≤ coupledTrace T g) {ρ : XiDivisorSupport} (hoff : (ρ : ℂ).re ≠ 1 / 2)
    (a b : ι) : couplingMatrix τ ρ a b = 0 := by
  classical
  have hne : meyerLineReflect ρ ≠ ρ := meyerLineReflect_ne_self hoff
  set P : DeningerMeyerStrongLogTarget :=
    meyerPointSource ρ + meyerPointSource (meyerLineReflect ρ)
  have hP (σ : XiDivisorSupport) (hσ : σ = ρ ∨ σ = meyerLineReflect ρ) :
      deningerMeyerStrongLogMellin P (σ : ℂ) = 1 := by
    change deningerMeyerStrongLogMellinLM (σ : ℂ) P = 1
    rw [map_add]
    change deningerMeyerStrongLogMellin _ (σ : ℂ) + deningerMeyerStrongLogMellin _ (σ : ℂ) = 1
    rw [meyerPointSource_values, meyerPointSource_values]
    rcases hσ with rfl | rfl
    · rw [if_pos rfl, if_neg hne.symm, add_zero]
    · rw [if_neg hne, if_pos rfl, zero_add]
  have hval (c₀ c : ι) (σ : XiDivisorSupport) (hσ : σ = ρ ∨ σ = meyerLineReflect ρ) :
      deningerMeyerStrongLogMellin (↑(if c = c₀ then P else 0 : DeningerMeyerStrongLogTarget))
        (σ : ℂ) = if c = c₀ then 1 else 0 := by
    split_ifs
    · exact hP σ hσ
    · change deningerMeyerStrongLogMellinLM (σ : ℂ) 0 = 0
      exact map_zero _
  have hstable : PointStable (⊤ : Submodule ℂ (ι → DeningerMeyerStrongLogTarget)) :=
    fun _ _ _ => Submodule.mem_top
  have h := coupled_isotropy hT hstable (fun g _ => hpos g) hoff
    (g := fun c => if c = a then P else 0) (g' := fun c => if c = b then P else 0)
    Submodule.mem_top Submodule.mem_top
  have h' : isotropyPairing τ ρ (fun c => if c = a then (1 : ℂ) else 0)
      (fun c => if c = b then (1 : ℂ) else 0) = 0 := by
    refine Eq.trans ?_ h
    congr 1 <;> funext c
    · exact (hval a c ρ (Or.inl rfl)).symm
    · exact (hval b c (meyerLineReflect ρ) (Or.inr rfl)).symm
  unfold isotropyPairing at h'
  have hstar : ∀ d : ι, star (if d = b then (1 : ℂ) else 0) = if d = b then 1 else 0 :=
    fun d => by split_ifs <;> simp
  simp only [hstar, ite_mul, one_mul, zero_mul, mul_ite, mul_one, mul_zero] at h'
  simpa [Finset.sum_ite_eq'] using h'

/-! ### 3. One channel: positive ideals are half-blind -/

/-- **Positive convolution ideals are half-blind.** A convolution ideal with nonnegative trace,
sharp-stable or not, is blind at `ρ` or at `ρ*` for every off-line zero `ρ`. -/
theorem positive_ideal_halfBlind {I : Submodule ℂ DeningerMeyerStrongLogTarget}
    (hmul : ∀ g ∈ I, ∀ h : DeningerMeyerStrongLogTarget,
      deningerMeyerSourceConvolution g h ∈ I)
    (hpos : ∀ g ∈ I, 0 ≤ meyerSourceTrace g g)
    {ρ : XiDivisorSupport} (hoff : (ρ : ℂ).re ≠ 1 / 2) :
    (∀ g ∈ I, deningerMeyerStrongLogMellin g (ρ : ℂ) = 0) ∨
      (∀ g ∈ I, deningerMeyerStrongLogMellin g (meyerLineReflect ρ : ℂ) = 0) := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨⟨g, hg, hgρ⟩, ⟨g', hg', hg'ρ⟩⟩ := hcon
  -- One channel with the identity coupling.
  let M : Submodule ℂ (Unit → DeningerMeyerStrongLogTarget) := Submodule.pi Set.univ fun _ => I
  have hM : PointStable M := fun f hf ρ' _ _ => hmul _ (hf () trivial) _
  have hT : ∀ a b : Unit, IsDivisorMultiplier (LinearMap.id) (fun _ => (1 : ℂ)) :=
    fun _ _ _ _ => (one_mul _).symm
  have hQ : ∀ f ∈ M, 0 ≤ coupledTrace (fun _ _ => LinearMap.id) f := by
    intro f hf
    simp only [coupledTrace, Finset.univ_unique, Finset.sum_singleton, LinearMap.id_apply]
    exact hpos _ (hf () trivial)
  have h := coupled_isotropy hT hM hQ hoff (g := fun _ => g) (g' := fun _ => g')
    (fun _ _ => hg) (fun _ _ => hg')
  simp only [isotropyPairing, couplingMatrix, Finset.univ_unique, Finset.sum_singleton,
    star_one, mul_one] at h
  have hm : (xiSupportMultiplicity ρ : ℂ) + xiSupportMultiplicity (meyerLineReflect ρ) ≠ 0 := by
    have h1 := xiSupportMultiplicity_pos ρ
    exact_mod_cast (by omega : xiSupportMultiplicity ρ + xiSupportMultiplicity
      (meyerLineReflect ρ) ≠ 0)
  rcases mul_eq_zero.mp h with h' | h'
  · rcases mul_eq_zero.mp h' with h'' | h''
    · exact hgρ h''
    · exact hg'ρ (star_eq_zero.mp h'')
  · exact hm h'

/-- With sharp stability both sides of every off-line pair are blind: the maximality theorem. -/
theorem le_meyerTraceBoundedIdeal_of_positive_sharp_ideal
    {I : Submodule ℂ DeningerMeyerStrongLogTarget}
    (hsharp : ∀ g ∈ I, deningerMeyerSourceSharp g ∈ I)
    (hmul : ∀ g ∈ I, ∀ h : DeningerMeyerStrongLogTarget,
      deningerMeyerSourceConvolution g h ∈ I)
    (hpos : ∀ g ∈ I, 0 ≤ meyerSourceTrace g g) :
    I ≤ meyerTraceBoundedIdeal := by
  intro g hg
  change MeyerTraceOrbitBounded g
  rw [meyerTraceOrbitBounded_iff_offLine_values_zero]
  intro ρ hoff
  have hsharp_val (f : DeningerMeyerStrongLogTarget) (σ : XiDivisorSupport) :
      deningerMeyerStrongLogMellin (deningerMeyerSourceSharp f) (σ : ℂ) =
        star (deningerMeyerStrongLogMellin f (meyerLineReflect σ : ℂ)) := by
    rw [deningerMeyerSourceSharp_mellin, meyerLineReflect_val]
  rcases positive_ideal_halfBlind hmul hpos hoff with h | h
  · exact h g hg
  · have := h _ (hsharp g hg)
    rw [hsharp_val, meyerLineReflect_sq] at this
    exact star_eq_zero.mp this

/-! ### 4. The left-blind ideal -/

/-- Sources vanishing at every Xi zero left of the critical line. -/
def leftBlindIdeal : Submodule ℂ DeningerMeyerStrongLogTarget where
  carrier := {g | ∀ σ : XiDivisorSupport, (σ : ℂ).re < 1 / 2 →
    deningerMeyerStrongLogMellin g (σ : ℂ) = 0}
  zero_mem' := fun σ _ => by
    change deningerMeyerStrongLogMellinLM (σ : ℂ) 0 = 0
    exact map_zero _
  add_mem' := fun {f g} hf hg σ hσ => by
    change deningerMeyerStrongLogMellinLM (σ : ℂ) (f + g) = 0
    rw [map_add]
    change deningerMeyerStrongLogMellin f (σ : ℂ) + deningerMeyerStrongLogMellin g (σ : ℂ) = 0
    rw [hf σ hσ, hg σ hσ, add_zero]
  smul_mem' := fun c {g} hg σ hσ => by
    change deningerMeyerStrongLogMellinLM (σ : ℂ) (c • g) = 0
    rw [map_smul]
    change c * deningerMeyerStrongLogMellin g (σ : ℂ) = 0
    rw [hg σ hσ, mul_zero]

theorem leftBlindIdeal_convolution {g : DeningerMeyerStrongLogTarget} (hg : g ∈ leftBlindIdeal)
    (h : DeningerMeyerStrongLogTarget) : deningerMeyerSourceConvolution g h ∈ leftBlindIdeal :=
  fun σ hσ => by rw [deningerMeyerSourceConvolution_mellin, hg σ hσ, zero_mul]

/-- Each term of the pairing of a left-blind source with itself has nonnegative real part. -/
theorem re_term_nonneg_of_mem_leftBlindIdeal {g : DeningerMeyerStrongLogTarget}
    (hg : g ∈ leftBlindIdeal) (σ : XiDivisorSupport) :
    0 ≤ (deningerMeyerStrongLogMellin g (σ : ℂ) *
      star (deningerMeyerStrongLogMellin g (meyerLineReflect σ : ℂ))).re := by
  rcases lt_trichotomy ((σ : ℂ).re) (1 / 2) with hl | he | hr
  · rw [hg σ hl, zero_mul, Complex.zero_re]
  · have hfix : meyerLineReflect σ = σ := by
      apply Subtype.ext
      rw [meyerLineReflect_val]
      apply Complex.ext
      · change 1 - (σ : ℂ).re = (σ : ℂ).re; linarith
      · change -(0 - (σ : ℂ).im) = (σ : ℂ).im; ring
    rw [hfix, RCLike.star_def, Complex.mul_conj]
    exact Complex.normSq_nonneg _
  · have hl : (meyerLineReflect σ : ℂ).re < 1 / 2 := by
      rw [meyerLineReflect_val]
      change 1 - (σ : ℂ).re < 1 / 2
      linarith
    rw [hg _ hl, star_zero, mul_zero, Complex.zero_re]

/-- **The left-blind ideal is positive.** -/
theorem meyerSourceTrace_nonneg_of_mem_leftBlindIdeal {g : DeningerMeyerStrongLogTarget}
    (hg : g ∈ leftBlindIdeal) : 0 ≤ meyerSourceTrace g g := by
  rw [meyerSourceTrace_eq_re, meyerComplexTrace_eq_tsum, Complex.re_tsum
    (summable_meyerComplexTrace g g)]
  exact tsum_nonneg fun q => re_term_nonneg_of_mem_leftBlindIdeal hg q.1

theorem meyerTraceBoundedIdeal_le_leftBlindIdeal : meyerTraceBoundedIdeal ≤ leftBlindIdeal := by
  intro g hg σ hσ
  have hg' : MeyerTraceOrbitBounded g := hg
  rw [meyerTraceOrbitBounded_iff_offLine_values_zero] at hg'
  exact hg' σ (by linarith)

/-- The left-blind ideal is everything iff RH. -/
theorem leftBlindIdeal_eq_top_iff : leftBlindIdeal = ⊤ ↔ RiemannHypothesis := by
  constructor
  · intro htop
    rw [← meyerTraceBoundedIdeal_eq_top_iff]
    refine Submodule.eq_top_iff'.mpr fun g => ?_
    change MeyerTraceOrbitBounded g
    rw [meyerTraceOrbitBounded_iff_offLine_values_zero]
    intro ρ hoff
    -- Every point source is left-blind, so there is no zero left of the line.
    have hleft : ∀ σ : XiDivisorSupport, ¬ (σ : ℂ).re < 1 / 2 := fun σ hσ => by
      have h := (htop ▸ Submodule.mem_top : meyerPointSource σ ∈ leftBlindIdeal) σ hσ
      rw [meyerPointSource_values, if_pos rfl] at h
      exact one_ne_zero h
    rcases lt_or_gt_of_ne hoff with hl | hr
    · exact absurd hl (hleft ρ)
    · exact absurd (by rw [meyerLineReflect_val]; change 1 - (ρ : ℂ).re < 1 / 2; linarith)
        (hleft (meyerLineReflect ρ))
  · intro hRH
    rw [← meyerTraceBoundedIdeal_eq_top_iff] at hRH
    exact top_unique (hRH ▸ meyerTraceBoundedIdeal_le_leftBlindIdeal)

/-- **Unless RH holds, the left-blind ideal is a positive convolution ideal strictly larger than
the maximal sharp-stable one.** -/
theorem meyerTraceBoundedIdeal_lt_leftBlindIdeal (hRH : ¬ RiemannHypothesis) :
    meyerTraceBoundedIdeal < leftBlindIdeal := by
  refine lt_of_le_of_ne meyerTraceBoundedIdeal_le_leftBlindIdeal fun heq => hRH ?_
  -- If they agreed, the left-blind ideal would be sharp-stable at every off-line zero.
  rw [← meyerTraceBoundedIdeal_eq_top_iff]
  refine Submodule.eq_top_iff'.mpr fun g => ?_
  change MeyerTraceOrbitBounded g
  rw [meyerTraceOrbitBounded_iff_offLine_values_zero]
  intro ρ hoff
  exfalso
  -- The point source at the right member of the pair is left-blind but not blind.
  set σ : XiDivisorSupport := if 1 / 2 < (ρ : ℂ).re then ρ else meyerLineReflect ρ
  have hσr : 1 / 2 < (σ : ℂ).re := by
    simp only [σ]
    split_ifs with h
    · exact h
    · rw [meyerLineReflect_val]
      change 1 / 2 < 1 - (ρ : ℂ).re
      have := lt_of_le_of_ne (not_lt.mp h) hoff
      linarith
  have hmem : meyerPointSource σ ∈ leftBlindIdeal := fun τ hτ => by
    rw [meyerPointSource_values, if_neg]
    rintro rfl
    linarith
  rw [← heq] at hmem
  have hb : MeyerTraceOrbitBounded (meyerPointSource σ) := hmem
  rw [meyerTraceOrbitBounded_iff_offLine_values_zero] at hb
  have := hb σ (ne_of_gt hσr)
  rw [meyerPointSource_values, if_pos rfl] at this
  exact one_ne_zero this

/-! ### 5. The left-blind ideal without zeros: backward flow boundedness -/

/-- Mixed traces of `g` stay bounded along the backward centered scaling flow. -/
def BackwardFlowBounded (g : DeningerMeyerStrongLogTarget) : Prop :=
  ∀ h : DeningerMeyerStrongLogTarget, ∃ C : ℝ, ∀ c : ℝ, c ≤ 0 →
    |meyerSourceTrace (deningerMeyerStrongLogCenteredFlow c g) h| ≤ C

/-- **Pre-divisor description.** A source is left-blind iff its mixed traces stay bounded along
the backward scaling flow. -/
theorem mem_leftBlindIdeal_iff_backwardFlowBounded (g : DeningerMeyerStrongLogTarget) :
    g ∈ leftBlindIdeal ↔ BackwardFlowBounded g := by
  constructor
  · intro hg h
    let t : XiZeroCopy → ℂ := fun q => deningerMeyerStrongLogMellin g (q.1 : ℂ) *
      star (deningerMeyerStrongLogMellin h (meyerLineReflect q.1 : ℂ))
    have ht : Summable fun q => ‖t q‖ := summable_norm_iff.mpr (summable_meyerComplexTrace g h)
    refine ⟨∑' q, ‖t q‖, fun c hc => ?_⟩
    -- The backward flow does not amplify any value at or right of the line.
    have hterm : ∀ q : XiZeroCopy, ‖deningerMeyerStrongLogMellin
        (deningerMeyerStrongLogCenteredFlow c g) (q.1 : ℂ) *
          star (deningerMeyerStrongLogMellin h (meyerLineReflect q.1 : ℂ))‖ ≤ ‖t q‖ := by
      intro q
      rw [meyerCenteredSourceFlow_mellin, mul_assoc, norm_mul]
      by_cases hq : ((q.1 : XiDivisorSupport) : ℂ).re < 1 / 2
      · simp only [t, hg q.1 hq, zero_mul, mul_zero, norm_zero, le_refl]
      · rw [Complex.norm_exp]
        have hre : ((c : ℂ) * ((q.1 : ℂ) - 1 / 2)).re = c * ((q.1 : ℂ).re - 1 / 2) := by simp
        rw [hre]
        exact mul_le_of_le_one_left (norm_nonneg _)
          (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg hc (by linarith)))
    have hs : Summable fun q : XiZeroCopy => ‖deningerMeyerStrongLogMellin
        (deningerMeyerStrongLogCenteredFlow c g) (q.1 : ℂ) *
          star (deningerMeyerStrongLogMellin h (meyerLineReflect q.1 : ℂ))‖ :=
      ht.of_nonneg_of_le (fun _ => norm_nonneg _) hterm
    rw [meyerSourceTrace_eq_re, meyerComplexTrace_eq_tsum]
    exact (Complex.abs_re_le_norm _).trans ((norm_tsum_le_tsum_norm hs).trans
      (Summable.tsum_le_tsum hterm hs ht))
  · intro hb σ hσ
    by_contra hne
    -- Read the value at `σ` with the point source at its reflection.
    let δ : DeningerMeyerStrongLogTarget := meyerPointSource (meyerLineReflect σ)
    have hpair (c : ℝ) (w : ℂ) : meyerComplexTrace (deningerMeyerStrongLogCenteredFlow c g)
        (w • δ) = (xiSupportMultiplicity σ : ℂ) *
          (Complex.exp ((c : ℂ) * ((σ : ℂ) - 1 / 2)) * deningerMeyerStrongLogMellin g (σ : ℂ) *
            star w) := by
      rw [meyerComplexTrace_eq_tsum]
      rw [tsum_copies_eq_sum (fun τ => deningerMeyerStrongLogMellin
          (deningerMeyerStrongLogCenteredFlow c g) (τ : ℂ) *
          star (deningerMeyerStrongLogMellin (↑(w • δ : DeningerMeyerStrongLogTarget))
            (meyerLineReflect τ : ℂ))) {σ}
          fun τ hτ => by
            have hτ' : meyerLineReflect τ ≠ meyerLineReflect σ := fun h => by
              apply hτ
              rw [Finset.mem_singleton, ← meyerLineReflect_sq τ, h, meyerLineReflect_sq]
            change _ * star (deningerMeyerStrongLogMellinLM _ (w • δ)) = 0
            rw [map_smul]
            change _ * star (w * deningerMeyerStrongLogMellin δ _) = 0
            rw [meyerPointSource_values, if_neg hτ', mul_zero, star_zero, mul_zero],
        Finset.sum_singleton, meyerCenteredSourceFlow_mellin]
      change _ * (_ * star (deningerMeyerStrongLogMellinLM _ (w • δ))) = _
      rw [map_smul]
      change _ * (_ * star (w * deningerMeyerStrongLogMellin δ _)) = _
      rw [meyerPointSource_values, if_pos rfl, mul_one]
    obtain ⟨C₁, hC₁⟩ := hb δ
    obtain ⟨C₂, hC₂⟩ := hb (I • δ)
    -- Both the real and imaginary parts stay bounded, hence so does the modulus.
    have hbound (c : ℝ) (hc : c ≤ 0) : (xiSupportMultiplicity σ : ℝ) *
        (Real.exp (c * ((σ : ℂ).re - 1 / 2)) * ‖deningerMeyerStrongLogMellin g (σ : ℂ)‖) ≤
          C₁ + C₂ := by
      have h1 := hC₁ c hc
      have h2 := hC₂ c hc
      rw [meyerSourceTrace_eq_re] at h1 h2
      have e1 := hpair c 1
      have e2 := hpair c I
      rw [one_smul] at e1
      rw [e1, star_one, mul_one] at h1
      rw [e2] at h2
      set z : ℂ := (xiSupportMultiplicity σ : ℂ) *
        (Complex.exp ((c : ℂ) * ((σ : ℂ) - 1 / 2)) * deningerMeyerStrongLogMellin g (σ : ℂ))
      have h2' : |z.im| ≤ C₂ := by
        have hzI : (xiSupportMultiplicity σ : ℂ) *
            (Complex.exp ((c : ℂ) * ((σ : ℂ) - 1 / 2)) * deningerMeyerStrongLogMellin g (σ : ℂ) *
              star I) = -I * z := by
          simp only [z, RCLike.star_def, Complex.conj_I]
          ring
        rw [hzI] at h2
        simpa [Complex.mul_re] using h2
      have hz : ‖z‖ = (xiSupportMultiplicity σ : ℝ) *
          (Real.exp (c * ((σ : ℂ).re - 1 / 2)) * ‖deningerMeyerStrongLogMellin g (σ : ℂ)‖) := by
        simp only [z, norm_mul, Complex.norm_natCast, Complex.norm_exp]
        congr 3
        simp
      rw [← hz]
      exact (Complex.norm_le_abs_re_add_abs_im z).trans (add_le_add h1 h2')
    -- The backward flow amplifies a value left of the line without bound.
    have hm : (0 : ℝ) < xiSupportMultiplicity σ := by exact_mod_cast xiSupportMultiplicity_pos σ
    have hv : 0 < ‖deningerMeyerStrongLogMellin g (σ : ℂ)‖ := norm_pos_iff.mpr hne
    have hδ : 0 < 1 / 2 - (σ : ℂ).re := by linarith
    obtain ⟨c, hc0, hcbig⟩ : ∃ c : ℝ, c ≤ 0 ∧
        (C₁ + C₂) / ((xiSupportMultiplicity σ : ℝ) * ‖deningerMeyerStrongLogMellin g (σ : ℂ)‖) <
          Real.exp (c * ((σ : ℂ).re - 1 / 2)) := by
      set B := (C₁ + C₂) / ((xiSupportMultiplicity σ : ℝ) *
        ‖deningerMeyerStrongLogMellin g (σ : ℂ)‖)
      refine ⟨-(|B| + 1) / (1 / 2 - (σ : ℂ).re), ?_, ?_⟩
      · exact div_nonpos_of_nonpos_of_nonneg (by linarith [abs_nonneg B]) hδ.le
      · have he : -(|B| + 1) / (1 / 2 - (σ : ℂ).re) * ((σ : ℂ).re - 1 / 2) = |B| + 1 := by
          rw [show (σ : ℂ).re - 1 / 2 = -(1 / 2 - (σ : ℂ).re) by ring, mul_neg,
            div_mul_cancel₀ _ hδ.ne', neg_neg]
        rw [he]
        have hexp := Real.add_one_lt_exp (x := |B| + 1) (by positivity : (0 : ℝ) < |B| + 1).ne'
        linarith [le_abs_self B]
    have hle := hbound c hc0
    rw [div_lt_iff₀ (by positivity)] at hcbig
    have hcomm : Real.exp (c * ((σ : ℂ).re - 1 / 2)) *
        ((xiSupportMultiplicity σ : ℝ) * ‖deningerMeyerStrongLogMellin g (σ : ℂ)‖) =
        (xiSupportMultiplicity σ : ℝ) *
          (Real.exp (c * ((σ : ℂ).re - 1 / 2)) * ‖deningerMeyerStrongLogMellin g (σ : ℂ)‖) := by
      ring
    linarith

end GaloisForLFunctions.ArithmeticPositiveDuality
