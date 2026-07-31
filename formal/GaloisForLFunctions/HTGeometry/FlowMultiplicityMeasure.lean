import GaloisForLFunctions.HTGeometry.FlowSmoothingTrace
import GaloisForLFunctions.HTGeometry.CompactOperatorBoundedBelow
import GaloisForLFunctions.HTGeometry.ExpSumVanishing

/-!
# The multiplicity measure of a unitary flow

The spectral points of a unitary flow are the real generators `λ` of its characters
`t ↦ exp (i λ t)`, and the smoothing by a weight `φ` acts on a `λ`-eigenvector by the scalar

`φ̂(-λ) = ∫ φ(t) exp (i λ t) dt`.

Two facts are recorded here.  First, a spectral window on which the weight's transform stays
away from zero carries only finitely many orthonormal eigenvectors: on such a window the compact
smoothing operator is bounded below, and a compact operator admits no infinite orthonormal
eigenfamily with eigenvalues bounded away from zero.  This is finite multiplicity together with
the absence of finite accumulation points.

Second, the eigenvalue family assembles into the multiplicity measure `ν = ∑ⱼ mⱼ δ_{λⱼ}`, a sum
of Dirac masses whose mass on a set is the number of basis vectors whose generator lies there,
and the trace of the smoothing is the pairing of `ν` with the weight's transform.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory ContinuousLinearMap

/-- The character of a unitary flow on a `λ`-eigenline, `t ↦ exp (i λ t)`. -/
noncomputable def flowCharacter (lam t : ℝ) : ℂ :=
  Complex.exp (Complex.I * ((lam : ℂ) * (t : ℂ)))

/-- The transform of the weight at a spectral point, `φ̂(-λ) = ∫ φ(t) exp (i λ t) dt`.  This is
the eigenvalue of the smoothing `K_φ` on a `λ`-eigenline. -/
noncomputable def weightTransform (phi : ℝ → ℝ) (lam : ℝ) : ℂ :=
  ∫ t, phi t • flowCharacter lam t

section Spectrum

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable [NormedSpace ℝ H] [CompleteSpace H] [SMulCommClass ℝ ℂ H] [IsScalarTower ℝ ℂ H]

/-- A flow eigenvector with generator `λ` is an eigenvector of the smoothing with eigenvalue
`φ̂(-λ)`. -/
theorem flowSmoothingCLM_eigenvector (U : UnitaryFlow ℂ H) (phi : ℝ → ℝ)
    (hphi : Continuous phi) (hsupp : HasCompactSupport phi) {x : H} {lam : ℝ}
    (hchar : ∀ t, U.op t x = flowCharacter lam t • x) :
    flowSmoothingCLM U phi hphi hsupp x = weightTransform phi lam • x := by
  rw [flowSmoothingCLM_apply]
  exact flowSmoothing_eigenvector U phi hchar

/-- **A spectral window carries finitely many eigenvectors.**  If the weight's transform is
bounded below on a set `S` of spectral points and the smoothing is compact, then any orthonormal
family of flow eigenvectors with generators in `S` is finite.  This is clause 1 of the discrete
spectrum statement — finite multiplicity and no finite accumulation point — carried by the
compact smoothing operator rather than by spectral projections. -/
theorem finite_of_orthonormal_flowEigenvectors_of_window (U : UnitaryFlow ℂ H) (phi : ℝ → ℝ)
    (hphi : Continuous phi) (hsupp : HasCompactSupport phi)
    (hK : IsCompactOperator (flowSmoothingCLM U phi hphi hsupp))
    {ι : Type*} {e : ι → H} (he : Orthonormal ℂ e) {lam : ι → ℝ}
    (hchar : ∀ i t, U.op t (e i) = flowCharacter (lam i) t • e i)
    {S : Set ℝ} (hwin : ∀ i, lam i ∈ S) {c : ℝ} (hc : 0 < c)
    (hbdd : ∀ x ∈ S, c ≤ ‖weightTransform phi x‖) :
    Finite ι :=
  finite_of_orthonormal_eigenvectors_of_le_norm hK he
    (fun i => flowSmoothingCLM_eigenvector U phi hphi hsupp (hchar i)) hc
    (fun i => hbdd _ (hwin i))

end Spectrum

/-! ## The multiplicity measure -/

/-- The **multiplicity measure** `ν = ∑ⱼ mⱼ δ_{λⱼ}` of a family of spectral points: the sum of the
Dirac masses at the generators, so that a spectral point carries mass equal to the number of
family members sitting at it. -/
noncomputable def multiplicityMeasure {ι : Type*} (lam : ι → ℝ) : Measure ℝ :=
  Measure.sum fun i => Measure.dirac (lam i)

variable {ι : Type*} (lam : ι → ℝ)

/-- The mass of a measurable set is the number of spectral points lying in it. -/
theorem multiplicityMeasure_apply {s : Set ℝ} (hs : MeasurableSet s) :
    multiplicityMeasure lam s = ∑' i, s.indicator 1 (lam i) := by
  rw [multiplicityMeasure, Measure.sum_apply _ hs]
  exact tsum_congr fun i => Measure.dirac_apply' _ hs

/-- The mass of a set carrying finitely many spectral points is that finite count: the
multiplicity of the window. -/
theorem multiplicityMeasure_eq_card {s : Set ℝ} (hs : MeasurableSet s)
    (hfin : {i | lam i ∈ s}.Finite) :
    multiplicityMeasure lam s = Nat.card {i // lam i ∈ s} := by
  classical
  rw [multiplicityMeasure_apply lam hs]
  have hind : ∀ i, s.indicator (1 : ℝ → ENNReal) (lam i)
      = {i | lam i ∈ s}.indicator (fun _ => (1 : ENNReal)) i := by
    intro i
    by_cases h : lam i ∈ s <;> simp [Set.indicator, h]
  have hcard : ({i | lam i ∈ s}).ncard = Nat.card {i // lam i ∈ s} := rfl
  rw [tsum_congr hind, ← tsum_subtype]
  simp [← hfin.cast_ncard_eq, hcard]

/-- The mass of a singleton is the multiplicity of that spectral point. -/
theorem multiplicityMeasure_singleton (x : ℝ) :
    multiplicityMeasure lam {x} = ∑' _ : {i // lam i = x}, (1 : ENNReal) := by
  classical
  rw [multiplicityMeasure_apply lam (measurableSet_singleton x)]
  have hind : ∀ i, ({x} : Set ℝ).indicator (1 : ℝ → ENNReal) (lam i)
      = (lam ⁻¹' {x}).indicator (fun _ => (1 : ENNReal)) i := by
    intro i
    by_cases h : lam i = x <;> simp [Set.indicator, h]
  rw [tsum_congr hind, ← tsum_subtype]
  rfl

/-- **The multiplicity measure is the atomic sum `ν = ∑_λ m(λ) δ_λ`.**  Grouping the Dirac masses
by the spectral point they sit at turns the family sum into a sum over the spectrum weighted by
multiplicities; this is equation `(3)`. -/
theorem multiplicityMeasure_apply_eq_tsum_atoms {s : Set ℝ} (hs : MeasurableSet s) :
    multiplicityMeasure lam s = ∑' x : ℝ, s.indicator 1 x * multiplicityMeasure lam {x} := by
  classical
  rw [multiplicityMeasure_apply lam hs]
  have hgroup := (Equiv.sigmaFiberEquiv lam).tsum_eq
    (f := fun i => s.indicator (1 : ℝ → ENNReal) (lam i))
  rw [← hgroup, ENNReal.tsum_sigma']
  refine tsum_congr fun x => ?_
  have hfib : ∀ i : {i // lam i = x},
      s.indicator (1 : ℝ → ENNReal) (lam ((Equiv.sigmaFiberEquiv lam) ⟨x, i⟩))
        = s.indicator (1 : ℝ → ENNReal) x := by
    rintro ⟨i, hi⟩
    simp [Equiv.sigmaFiberEquiv, hi]
  rw [tsum_congr hfib, multiplicityMeasure_singleton lam x, ← ENNReal.tsum_mul_left]
  simp

/-- **Uniqueness of the multiplicity measure.**  A multiplicity measure is determined by its
multiplicity function: two spectral families whose points carry the same multiplicities define the
same measure. -/
theorem multiplicityMeasure_eq_of_singleton_eq {κ : Type*} (mu : κ → ℝ)
    (h : ∀ x : ℝ, multiplicityMeasure lam {x} = multiplicityMeasure mu {x}) :
    multiplicityMeasure lam = multiplicityMeasure mu := by
  refine Measure.ext fun s hs => ?_
  rw [multiplicityMeasure_apply_eq_tsum_atoms lam hs,
    multiplicityMeasure_apply_eq_tsum_atoms mu hs]
  exact tsum_congr fun x => by rw [h x]

/-- **A measure on the line is determined by its restrictions to the bounded windows.**  Every
measurable set is the increasing union of its intersections with `[-n, n]`, so continuity from
below transports equality of the window restrictions to equality of the measures. -/
theorem measure_eq_of_restrict_Icc_eq {m n : Measure ℝ}
    (h : ∀ k : ℕ, m.restrict (Set.Icc (-(k : ℝ)) k) = n.restrict (Set.Icc (-(k : ℝ)) k)) :
    m = n := by
  refine Measure.ext fun t ht => ?_
  have hmono : Monotone fun k : ℕ => t ∩ Set.Icc (-(k : ℝ)) k := by
    intro a b hab x hx
    refine ⟨hx.1, ?_⟩
    have hle : ((a : ℝ)) ≤ (b : ℝ) := by exact_mod_cast hab
    exact ⟨le_trans (neg_le_neg hle) hx.2.1, le_trans hx.2.2 hle⟩
  have hcover : ⋃ k : ℕ, t ∩ Set.Icc (-(k : ℝ)) k = t := by
    refine Set.eq_of_subset_of_subset (Set.iUnion_subset fun k => Set.inter_subset_left) ?_
    intro x hx
    obtain ⟨k, hk⟩ := exists_nat_ge |x|
    exact Set.mem_iUnion.2 ⟨k, hx, neg_le_of_abs_le hk, le_of_abs_le hk⟩
  have hm := tendsto_measure_iUnion_atTop (μ := m) hmono
  have hn := tendsto_measure_iUnion_atTop (μ := n) hmono
  rw [hcover] at hm hn
  refine tendsto_nhds_unique hm ?_
  refine hn.congr fun k => ?_
  have hmk := congrArg (fun p : Measure ℝ => p t) (h k)
  simpa [Measure.restrict_apply ht] using hmk.symm

/-- A window carrying finitely many spectral points carries finite multiplicity mass. -/
theorem multiplicityMeasure_restrict_isFiniteMeasure {s : Set ℝ} (hs : MeasurableSet s)
    (hfin : {i | lam i ∈ s}.Finite) :
    IsFiniteMeasure ((multiplicityMeasure lam).restrict s) := by
  refine ⟨?_⟩
  rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
    multiplicityMeasure_eq_card lam hs hfin]
  exact ENNReal.natCast_lt_top _

/-- **Uniqueness of the multiplicity measure from its window pairings.**  If every bounded window
carries finitely many spectral points, then the multiplicity measure is determined by the
integrals of bounded continuous functions against its window restrictions.  Each restriction is a
finite measure, so Riesz uniqueness applies there, and a measure on the line is the limit of its
window restrictions. -/
theorem multiplicityMeasure_eq_of_forall_integral_window_eq {κ : Type*} (mu : κ → ℝ)
    (hfl : ∀ k : ℕ, {i | lam i ∈ Set.Icc (-(k : ℝ)) k}.Finite)
    (hfm : ∀ k : ℕ, {j | mu j ∈ Set.Icc (-(k : ℝ)) k}.Finite)
    (h : ∀ (k : ℕ) (f : BoundedContinuousFunction ℝ ℝ),
      ∫ x, f x ∂((multiplicityMeasure lam).restrict (Set.Icc (-(k : ℝ)) k))
        = ∫ x, f x ∂((multiplicityMeasure mu).restrict (Set.Icc (-(k : ℝ)) k))) :
    multiplicityMeasure lam = multiplicityMeasure mu := by
  refine measure_eq_of_restrict_Icc_eq fun k => ?_
  haveI := multiplicityMeasure_restrict_isFiniteMeasure lam measurableSet_Icc (hfl k)
  haveI := multiplicityMeasure_restrict_isFiniteMeasure mu measurableSet_Icc (hfm k)
  exact ext_of_forall_integral_eq_of_IsFiniteMeasure (h k)

/-- **Integration against the multiplicity measure is summation over the spectrum with
multiplicity.** -/
theorem integral_multiplicityMeasure {f : ℝ → ℂ}
    (hf : Integrable f (multiplicityMeasure lam)) :
    ∫ x, f x ∂(multiplicityMeasure lam) = ∑' i, f (lam i) := by
  rw [multiplicityMeasure] at hf ⊢
  rw [integral_sum_measure hf]
  exact tsum_congr fun i => integral_dirac _ _

section TraceMeasure

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable [NormedSpace ℝ H] [CompleteSpace H] [SMulCommClass ℝ ℂ H] [IsScalarTower ℝ ℂ H]

/-- **The trace of a smoothing is the pairing of the weight's transform with the multiplicity
measure**, `Tr K_φ = ∫ φ̂(-λ) dν(λ)`.  Together with the eigenbasis form `Tr K_φ = ∑ⱼ mⱼ φ̂(-λⱼ)`
this exhibits the trace distribution as the Fourier pairing of `ν`. -/
theorem opTrace_flowSmoothing_eq_integral_multiplicityMeasure
    (U : UnitaryFlow ℂ H) (phi : ℝ → ℝ)
    (hphi : Continuous phi) (hsupp : HasCompactSupport phi)
    {lam : _ → ℝ}
    (hchar : ∀ i t, U.op t (hsBasis ℂ H i) = flowCharacter (lam i) t • hsBasis ℂ H i)
    (hint : Integrable (weightTransform phi) (multiplicityMeasure lam)) :
    opTrace (flowSmoothingCLM U phi hphi hsupp)
      = ∫ x, weightTransform phi x ∂(multiplicityMeasure lam) := by
  rw [integral_multiplicityMeasure lam hint]
  exact opTrace_flowSmoothing_eq_tsum_characterIntegral U phi hphi hsupp hchar

end TraceMeasure


/-! ## The character function determines the multiplicity measure -/

/-- The flow character is the unit-modulus exponential with real frequency. -/
theorem flowCharacter_eq_cis (lam t : ℝ) : flowCharacter lam t = HTGeometry.cis lam t := by
  rw [flowCharacter, HTGeometry.cis]
  push_cast
  ring_nf

/-- **Linear independence of the flow characters.**  A finite exponential sum with pairwise
distinct real frequencies vanishing identically has vanishing coefficients. -/
theorem coeff_eq_zero_of_flowCharacter_sum_eq_zero {n : ℕ} {lam : Fin n → ℝ}
    (hinj : Function.Injective lam) {b : Fin n → ℂ}
    (h : ∀ t : ℝ, ∑ i, b i * flowCharacter (lam i) t = 0) (i : Fin n) : b i = 0 := by
  refine HTGeometry.eq_zero_of_expSum_tendsto_zero n lam b hinj ?_ i
  have hzero : (fun t : ℝ => ∑ i, b i * HTGeometry.cis (lam i) t) = fun _ => (0 : ℂ) := by
    funext t
    rw [← h t]
    exact Finset.sum_congr rfl fun i _ => by rw [flowCharacter_eq_cis]
  rw [hzero]
  exact tendsto_const_nhds

section CharacterUniqueness

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- The character sum of a finite spectral family, regrouped over its distinct frequencies with
multiplicity. -/
theorem sum_flowCharacter_eq_sum_multiplicity (lam : ι → ℝ) (S : Finset ℝ)
    (hS : Finset.image lam Finset.univ ⊆ S) (t : ℝ) :
    ∑ i, flowCharacter (lam i) t
      = ∑ x ∈ S, ((Finset.univ.filter fun i => lam i = x).card : ℂ) * flowCharacter x t := by
  classical
  have h1 : ∑ i, flowCharacter (lam i) t
      = ∑ x ∈ Finset.image lam Finset.univ,
          (Finset.univ.filter fun i => lam i = x).card • flowCharacter x t :=
    Finset.sum_comp (fun x : ℝ => flowCharacter x t) lam
  have h2 : ∑ x ∈ Finset.image lam Finset.univ,
        (Finset.univ.filter fun i => lam i = x).card • flowCharacter x t
      = ∑ x ∈ S, (Finset.univ.filter fun i => lam i = x).card • flowCharacter x t := by
    refine Finset.sum_subset hS fun x _ hx => ?_
    have hempty : (Finset.univ.filter fun i => lam i = x) = ∅ := by
      refine Finset.eq_empty_of_forall_notMem fun i hi => ?_
      exact hx (Finset.mem_image.2 ⟨i, Finset.mem_univ i, (Finset.mem_filter.1 hi).2⟩)
    rw [hempty]
    simp
  rw [h1, h2]
  exact Finset.sum_congr rfl fun x _ => by rw [nsmul_eq_mul]

/-- **The character function determines the multiplicity measure.**  Two finite spectral families
whose characters sum to the same function of time carry the same multiplicities, hence define the
same measure `ν_A`.  This is uniqueness in clause 5 on a window: the coefficients of an
exponential sum with pairwise distinct real frequencies are exactly its multiplicities. -/
theorem multiplicityMeasure_eq_of_sum_flowCharacter_eq (lam : ι → ℝ) (mu : κ → ℝ)
    (h : ∀ t : ℝ, ∑ i, flowCharacter (lam i) t = ∑ j, flowCharacter (mu j) t) :
    multiplicityMeasure lam = multiplicityMeasure mu := by
  classical
  set S : Finset ℝ := Finset.image lam Finset.univ ∪ Finset.image mu Finset.univ with hSdef
  set n : ℕ := S.card with hn
  set enum : Fin n → ℝ := fun k => (S.equivFin.symm k : ℝ) with henum
  set cl : ℝ → ℂ := fun x => ((Finset.univ.filter fun i => lam i = x).card : ℂ) with hcl
  set cm : ℝ → ℂ := fun x => ((Finset.univ.filter fun j => mu j = x).card : ℂ) with hcm
  have hinj : Function.Injective enum := fun a b hab =>
    S.equivFin.symm.injective (Subtype.ext hab)
  have hsplit : ∀ f : ℝ → ℂ, ∑ k : Fin n, f (enum k) = ∑ x ∈ S, f x := by
    intro f
    refine (Fintype.sum_equiv S.equivFin.symm _ (fun y : S => f (y : ℝ)) fun k => rfl).trans ?_
    exact Finset.sum_coe_sort S fun x => f x
  have hcoeff : ∀ k : Fin n, cl (enum k) - cm (enum k) = 0 := by
    refine coeff_eq_zero_of_flowCharacter_sum_eq_zero hinj
      (b := fun k => cl (enum k) - cm (enum k)) ?_
    intro t
    have hL := sum_flowCharacter_eq_sum_multiplicity lam S Finset.subset_union_left t
    have hR := sum_flowCharacter_eq_sum_multiplicity mu S Finset.subset_union_right t
    calc ∑ k : Fin n, (cl (enum k) - cm (enum k)) * flowCharacter (enum k) t
        = ∑ x ∈ S, (cl x - cm x) * flowCharacter x t :=
          hsplit fun x => (cl x - cm x) * flowCharacter x t
      _ = (∑ x ∈ S, cl x * flowCharacter x t) - ∑ x ∈ S, cm x * flowCharacter x t := by
          rw [← Finset.sum_sub_distrib]
          exact Finset.sum_congr rfl fun x _ => by ring
      _ = 0 := by rw [← hL, ← hR, h t, sub_self]
  have hcard : ∀ x : ℝ, cl x = cm x := by
    intro x
    by_cases hx : x ∈ S
    · obtain ⟨k, hk⟩ : ∃ k : Fin n, enum k = x := ⟨S.equivFin ⟨x, hx⟩, by simp [henum]⟩
      have hk0 := hcoeff k
      rw [hk] at hk0
      exact sub_eq_zero.mp hk0
    · have hl : (Finset.univ.filter fun i => lam i = x) = ∅ := by
        refine Finset.eq_empty_of_forall_notMem fun i hi => ?_
        exact hx (Finset.mem_union_left _
          (Finset.mem_image.2 ⟨i, Finset.mem_univ i, (Finset.mem_filter.1 hi).2⟩))
      have hr : (Finset.univ.filter fun j => mu j = x) = ∅ := by
        refine Finset.eq_empty_of_forall_notMem fun j hj => ?_
        exact hx (Finset.mem_union_right _
          (Finset.mem_image.2 ⟨j, Finset.mem_univ j, (Finset.mem_filter.1 hj).2⟩))
      rw [hcl, hcm]
      simp [hl, hr]
  refine multiplicityMeasure_eq_of_singleton_eq lam mu fun x => ?_
  have hfl : {i | lam i ∈ ({x} : Set ℝ)}.Finite := Set.toFinite _
  have hfm : {j | mu j ∈ ({x} : Set ℝ)}.Finite := Set.toFinite _
  rw [multiplicityMeasure_eq_card lam (measurableSet_singleton x) hfl,
    multiplicityMeasure_eq_card mu (measurableSet_singleton x) hfm]
  have hnl : Nat.card {i // lam i ∈ ({x} : Set ℝ)}
      = (Finset.univ.filter fun i => lam i = x).card := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_subtype _
  have hnr : Nat.card {j // mu j ∈ ({x} : Set ℝ)}
      = (Finset.univ.filter fun j => mu j = x).card := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_subtype _
  have hnat : (Finset.univ.filter fun i => lam i = x).card
      = (Finset.univ.filter fun j => mu j = x).card := by
    have hx := hcard x
    simp only [hcl, hcm] at hx
    exact_mod_cast hx
  rw [hnl, hnr, hnat]

end CharacterUniqueness

end GaloisForLFunctions.HTGeometry
