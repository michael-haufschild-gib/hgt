import GaloisForLFunctions.RHTower.CHMDQuarterZeroBound

/-!
# Dimension of the bound-state space

Eigenvectors of the symmetric arithmetic resolvent `R` for distinct eigenvalues are orthogonal, so
on the span of finitely many eigenvectors with eigenvalues `≥ a` the numerical range satisfies
`⟪Ru, u⟫ ≥ a‖u‖²` (the difference is the squared norm of a reweighted combination, with no
grouping by eigenvalue). When `a > 1/2` this forces `E(Riesz u) ≤ −a(2a−1)‖u‖²`, so the Riesz
lifts of an orthonormal basis of the primitive part of such a span form a negative-definite family
for the Weil form, and the quarter-strip count applies: the primitive part has dimension at most
`2 · #(quarter zeros)`, the span itself at most one more. Taking a maximal linearly independent set
of eigenvectors, the span of all bound states above `1/2` is finite-dimensional, of dimension at
most `2 · #(quarter zeros) + 1`, whenever the off-line zero set is finite; it is then closed, so it
is the bound-state space. Finally `RH ⟺ dim (bound-state space) = 1`, with no finiteness
assumption.
-/

open MeasureTheory Set Filter Topology Zeta23
open scoped InnerProductSpace
noncomputable section
namespace RHTower.CHMDPolar
open CHMDDoobGraph CHMDClosedJump

/-! ## Spans of eigenvectors -/

/-- Eigenvectors of the arithmetic resolvent for distinct eigenvalues are orthogonal. -/
theorem inner_eigen_eq_zero_of_ne {μ ν : ℝ} {w u : MassSpace} (hw : resolvent w = μ • w)
    (hu : resolvent u = ν • u) (hne : μ ≠ ν) : ⟪w, u⟫_ℝ = 0 := by
  have h := resolvent_symm w u
  rw [hw, hu, real_inner_smul_left, real_inner_smul_right] at h
  have h' : (μ - ν) * ⟪w, u⟫_ℝ = 0 := by linarith
  rcases mul_eq_zero.mp h' with h1 | h1
  · exact absurd (sub_eq_zero.mp h1) hne
  · exact h1

/-- On combinations of eigenvectors with eigenvalues `≥ a`, the numerical range of `R` is at least
`a`. -/
theorem inner_resolvent_sum_ge {ι : Type*} [Fintype ι] (e : ι → MassSpace) (μ : ι → ℝ)
    (heig : ∀ i, resolvent (e i) = μ i • e i) {a : ℝ} (ha : ∀ i, a ≤ μ i) (c : ι → ℝ) :
    a * ‖∑ i, c i • e i‖ ^ 2 ≤ ⟪resolvent (∑ i, c i • e i), ∑ i, c i • e i⟫_ℝ := by
  have hR : ⟪resolvent (∑ i, c i • e i), ∑ i, c i • e i⟫_ℝ =
      ∑ i, ∑ j, c i * c j * μ i * ⟪e i, e j⟫_ℝ := by
    rw [map_sum, sum_inner]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, heig, inner_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [real_inner_smul_right, smul_smul, real_inner_smul_left]
    ring
  have hN : ‖∑ i, c i • e i‖ ^ 2 = ∑ i, ∑ j, c i * c j * ⟪e i, e j⟫_ℝ := by
    rw [← real_inner_self_eq_norm_sq, sum_inner]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [inner_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [real_inner_smul_left, real_inner_smul_right]
    ring
  have hS : ‖∑ i, (c i * Real.sqrt (μ i - a)) • e i‖ ^ 2 =
      ∑ i, ∑ j, c i * c j * (μ i - a) * ⟪e i, e j⟫_ℝ := by
    rw [← real_inner_self_eq_norm_sq, sum_inner]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [inner_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [real_inner_smul_left, real_inner_smul_right]
    by_cases hij : μ i = μ j
    · have hs : Real.sqrt (μ i - a) * Real.sqrt (μ j - a) = μ i - a := by
        rw [hij]
        exact Real.mul_self_sqrt (sub_nonneg.mpr (ha j))
      linear_combination (c i * c j * ⟪e i, e j⟫_ℝ) * hs
    · rw [inner_eigen_eq_zero_of_ne (heig i) (heig j) hij]
      ring
  have hsq : 0 ≤ ‖∑ i, (c i * Real.sqrt (μ i - a)) • e i‖ ^ 2 := sq_nonneg _
  rw [hS] at hsq
  have hsplit : ∑ i, ∑ j, c i * c j * (μ i - a) * ⟪e i, e j⟫_ℝ =
      (∑ i, ∑ j, c i * c j * μ i * ⟪e i, e j⟫_ℝ) - a * ∑ i, ∑ j, c i * c j * ⟪e i, e j⟫_ℝ := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [hR, hN]
  linarith

/-- A numerical-range lower bound above `1/2` forces negative Doob energy of the Riesz lift. -/
theorem sourceEnergy_rieszLift_le_of_lower_bound {a : ℝ} (ha : 1 / 2 < a) {u : MassSpace}
    (hu : a * ‖u‖ ^ 2 ≤ ⟪resolvent u, u⟫_ℝ) :
    sourceEnergy (rieszLift u) ≤ -(a * (2 * a - 1)) * ‖u‖ ^ 2 := by
  rw [sourceEnergy_rieszLift, ← real_inner_comm u (resolvent u)]
  by_cases hu0 : u = 0
  · subst hu0
    simp
  have hpos : 0 < ‖u‖ ^ 2 := pow_pos (norm_pos_iff.mpr hu0) 2
  have h0 : 0 ≤ ⟪resolvent u, u⟫_ℝ := le_trans (by positivity) hu
  have h1 : ⟪resolvent u, u⟫_ℝ ≤ ‖resolvent u‖ * ‖u‖ := real_inner_le_norm _ _
  have h2 : ⟪resolvent u, u⟫_ℝ ^ 2 ≤ ‖resolvent u‖ ^ 2 * ‖u‖ ^ 2 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ h0 h1 2
  have h3 : a * ‖u‖ ^ 2 * ⟪resolvent u, u⟫_ℝ ≤ ⟪resolvent u, u⟫_ℝ ^ 2 :=
    (mul_le_mul_of_nonneg_right hu h0).trans_eq (pow_two _).symm
  have h4 : a * ⟪resolvent u, u⟫_ℝ ≤ ‖resolvent u‖ ^ 2 := by
    by_contra hcon
    rw [not_le] at hcon
    have := mul_lt_mul_of_pos_right hcon hpos
    linarith [h3.trans h2]
  have h5 : 0 ≤ (2 * a - 1) * (⟪resolvent u, u⟫_ℝ - a * ‖u‖ ^ 2) :=
    mul_nonneg (by linarith) (by linarith)
  nlinarith [h4, h5]

/-! ## The primitive part of a span of eigenvectors -/

/-- **Dimension of a span of bound states.** The span of finitely many eigenvectors of `R` with
eigenvalues above `1/2` has dimension at most `2 · #(quarter zeros) + 1`. -/
theorem finrank_span_eigen_le (hfin : offLineZeros.Finite) {ι : Type*} [Fintype ι]
    (e : ι → MassSpace) (μ : ι → ℝ) (hμ : ∀ i, 1 / 2 < μ i)
    (heig : ∀ i, resolvent (e i) = μ i • e i) :
    Module.finrank ℝ (Submodule.span ℝ (Set.range e)) ≤ 2 * quarterZeros.ncard + 1 := by
  classical
  rcases isEmpty_or_nonempty ι with hι | hι
  · rw [Set.range_eq_empty, Submodule.span_empty, finrank_bot]
    omega
  obtain ⟨i₀, _, hi₀⟩ := Finset.exists_min_image Finset.univ μ Finset.univ_nonempty
  set a := μ i₀ with ha_def
  have ha : 1 / 2 < a := hμ i₀
  have hamin : ∀ i, a ≤ μ i := fun i => hi₀ i (Finset.mem_univ i)
  set U : Submodule ℝ MassSpace := Submodule.span ℝ (Set.range e) with hU
  haveI : FiniteDimensional ℝ U := FiniteDimensional.span_of_finite ℝ (Set.finite_range e)
  let ℓ : U →ₗ[ℝ] ℝ :=
    { toFun := fun u => ⟪(u : MassSpace), oneL⟫_ℝ
      map_add' := fun u v => by simp [inner_add_left]
      map_smul' := fun r u => by simp [real_inner_smul_left] }
  have hrange : Module.finrank ℝ (LinearMap.range ℓ) ≤ 1 := by
    calc Module.finrank ℝ (LinearMap.range ℓ) ≤ Module.finrank ℝ ℝ := Submodule.finrank_le _
      _ = 1 := Module.finrank_self ℝ
  have hker : Module.finrank ℝ (LinearMap.ker ℓ) ≤ 2 * quarterZeros.ncard := by
    set K := LinearMap.ker ℓ with hK
    let b := stdOrthonormalBasis ℝ K
    let f : Fin (Module.finrank ℝ K) → MassSpace := fun i => ((b i : U) : MassSpace)
    have hf : Orthonormal ℝ f := by
      refine orthonormal_iff_ite.mpr fun i j => ?_
      exact orthonormal_iff_ite.mp b.orthonormal i j
    have hfU : ∀ i, f i ∈ U := fun i => (b i).1.2
    have hfprim : ∀ i, ⟪f i, oneL⟫_ℝ = 0 := fun i => LinearMap.mem_ker.mp (b i).2
    have hneg : ∀ c : Fin (Module.finrank ℝ K) → ℝ,
        weilForm (∑ i, c i • rieszLift (f i)) ≤ -(a * (2 * a - 1)) * ∑ i, c i ^ 2 := by
      intro c
      rw [← rieszLift_sum]
      set u := ∑ i, c i • f i with hu_def
      have huU : u ∈ U := Submodule.sum_mem _ fun i _ => U.smul_mem _ (hfU i)
      have huprim : ⟪u, oneL⟫_ℝ = 0 := by
        rw [hu_def, sum_inner]
        exact Finset.sum_eq_zero fun i _ => by rw [real_inner_smul_left, hfprim i, mul_zero]
      have hnorm : ‖u‖ ^ 2 = ∑ i, c i ^ 2 := by
        rw [← real_inner_self_eq_norm_sq, hu_def, hf.inner_sum]
        exact Finset.sum_congr rfl fun i _ => by rw [conj_trivial, sq]
      obtain ⟨d, hd⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp huU
      have hlow : a * ‖u‖ ^ 2 ≤ ⟪resolvent u, u⟫_ℝ := by
        rw [← hd]
        exact inner_resolvent_sum_ge e μ heig hamin d
      have hE := sourceEnergy_rieszLift_le_of_lower_bound ha hlow
      have hW : weilForm (rieszLift u) ≤ sourceEnergy (rieszLift u) := by
        apply weilForm_le_sourceEnergy_of_primitive
        show ⟪resolvent u, oneL⟫_ℝ = 0
        rw [inner_resolvent_oneL, real_inner_comm, huprim]
      rw [hnorm] at hE
      linarith
    have hδ : 0 < a * (2 * a - 1) := mul_pos (by linarith) (by linarith)
    obtain ⟨q, hq, hqneg⟩ := exists_compactTests_negative_definite (fun i => rieszLift (f i)) hδ hneg
    exact card_le_two_mul_quarter_of_negative_definite hfin q hq hqneg
  have h := LinearMap.finrank_range_add_finrank_ker ℓ
  omega

/-! ## The bound-state space is finite-dimensional -/

/-- A finite linearly independent family of bound states above `1/2` has at most
`2 · #(quarter zeros) + 1` members. -/
theorem card_le_of_linearIndependent_eigen (hfin : offLineZeros.Finite) {ι : Type*} [Fintype ι]
    (e : ι → MassSpace) (hli : LinearIndependent ℝ e)
    (he : ∀ i, ∃ μ : ℝ, 1 / 2 < μ ∧ resolvent (e i) = μ • e i) :
    Fintype.card ι ≤ 2 * quarterZeros.ncard + 1 := by
  choose μ hμ heig using he
  rw [← finrank_span_eq_card hli]
  exact finrank_span_eigen_le hfin e μ hμ heig

theorem boundStateSpace_eq_span_of_finite (hfin : offLineZeros.Finite) :
    ∃ b : Set MassSpace, b.Finite ∧ b.ncard ≤ 2 * quarterZeros.ncard + 1 ∧
      boundStateSpace = Submodule.span ℝ b := by
  classical
  set S : Set MassSpace := {w | ∃ μ : ℝ, 1 / 2 < μ ∧ resolvent w = μ • w} with hS
  obtain ⟨b, hbS, hspan, hli⟩ := exists_linearIndependent ℝ S
  have hcard : ∀ t : Finset MassSpace, (↑t : Set MassSpace) ⊆ b →
      t.card ≤ 2 * quarterZeros.ncard + 1 := by
    intro t htb
    let e : t → MassSpace := fun x => (x : MassSpace)
    have hinj : Function.Injective fun x : t => (⟨x.1, htb x.2⟩ : b) :=
      fun x y h => Subtype.ext (by simpa using congrArg Subtype.val h)
    have hli' : LinearIndependent ℝ e := hli.comp (fun x : t => (⟨x.1, htb x.2⟩ : b)) hinj
    have he : ∀ x : t, ∃ μ : ℝ, 1 / 2 < μ ∧ resolvent (e x) = μ • e x := fun x =>
      hbS (htb x.2)
    have := card_le_of_linearIndependent_eigen hfin e hli' he
    rwa [Fintype.card_coe] at this
  have hbfin : b.Finite := by
    by_contra hinf
    obtain ⟨t, htb, htc⟩ := Set.Infinite.exists_subset_card_eq hinf (2 * quarterZeros.ncard + 2)
    have := hcard t htb
    omega
  refine ⟨b, hbfin, ?_, ?_⟩
  · rw [Set.ncard_eq_toFinset_card b hbfin]
    exact hcard _ hbfin.coe_toFinset.subset
  · haveI : FiniteDimensional ℝ (Submodule.span ℝ b) := FiniteDimensional.span_of_finite ℝ hbfin
    unfold boundStateSpace
    rw [← hspan]
    exact IsClosed.submodule_topologicalClosure_eq (Submodule.closed_of_finiteDimensional _)

/-- **Finiteness.** If only finitely many zeros are off the line, the bound-state space is
finite-dimensional. -/
theorem finiteDimensional_boundStateSpace (hfin : offLineZeros.Finite) :
    FiniteDimensional ℝ boundStateSpace := by
  obtain ⟨b, hbfin, -, hb⟩ := boundStateSpace_eq_span_of_finite hfin
  rw [hb]
  exact FiniteDimensional.span_of_finite ℝ hbfin

/-- **Upper bound.** `dim (bound-state space) ≤ 2 · #(quarter zeros) + 1`. -/
theorem finrank_boundStateSpace_le (hfin : offLineZeros.Finite) :
    Module.finrank ℝ boundStateSpace ≤ 2 * quarterZeros.ncard + 1 := by
  classical
  obtain ⟨b, hbfin, hcard, hb⟩ := boundStateSpace_eq_span_of_finite hfin
  rw [hb]
  haveI := hbfin.fintype
  refine (finrank_span_le_card b).trans ?_
  rw [← hbfin.toFinset_eq_toFinset, ← Set.ncard_eq_toFinset_card b hbfin]
  exact hcard

/-! ## RH as a dimension statement -/

theorem oneL_ne_zero : oneL ≠ 0 := by
  intro h
  have := norm_oneL_sq
  rw [h, norm_zero] at this
  norm_num at this

/-- **RH ⟺ the bound-state space is one-dimensional.** -/
theorem riemannHypothesis_iff_finrank_boundStateSpace_eq_one :
    RiemannHypothesis ↔ Module.finrank ℝ boundStateSpace = 1 := by
  rw [riemannHypothesis_iff_boundStateSpace_eq_span_oneL]
  constructor
  · intro h
    rw [h]
    exact finrank_span_singleton oneL_ne_zero
  · intro h
    haveI : FiniteDimensional ℝ boundStateSpace := Module.finite_of_finrank_pos (by omega)
    symm
    refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
    · rw [Submodule.span_singleton_le_iff_mem]
      exact oneL_mem_boundStateSpace
    · rw [h, finrank_span_singleton oneL_ne_zero]

/-! ## Two-sided counts -/

/-- The finite-level negative index of the Weil form is bounded by the quarter zeros. -/
theorem weilNegIndex_le_two_mul_quarter_add_one (hfin : offLineZeros.Finite) {a ε : ℝ}
    (hε : 0 ≤ ε) : weilNegIndex zetaZeroConfig a ε ≤ 2 * quarterZeros.ncard + 1 := by
  haveI := finiteDimensional_boundStateSpace hfin
  exact (weilNegIndex_le_finrank_boundStateSpace hε).trans (finrank_boundStateSpace_le hfin)

/-- Visible separated deep zero sets are bounded by the quarter zeros plus three. -/
theorem card_visible_le_two_mul_quarter_add_three (hfin : offLineZeros.Finite) :
    ∃ A₀ : ℝ, 1 ≤ A₀ ∧ ∀ (a δ R Hm ε : ℝ) (T : Finset ℂ), 0 < a → 0 < δ → 1 ≤ R → T.Nonempty →
      (∀ ρ ∈ T, ρ ∈ zetaZeroConfig.carrier ∧ 1 / 2 + δ ≤ ρ.re ∧ |ρ.im| ≤ Hm) →
      (∀ ρ ∈ T, ∀ σ ∈ T, ρ ≠ σ → 2 * R ≤ |ρ.im - σ.im|) →
      (∀ ρ ∈ T, ∀ σ ∈ zetaZeroConfig.carrier, σ ≠ ρ → σ ≠ reflect ρ → |σ.im - ρ.im| ≤ R →
        σ.re = 1 / 2) →
      0 < visibleMargin A₀ a δ R Hm → 0 < ε → ε ≤ 1 →
      ε ≤ visibleMargin A₀ a δ R Hm / (T.card * ((∫ u, sinhTest a δ u ^ 2) + 1)) →
      T.card ≤ 2 * quarterZeros.ncard + 3 := by
  haveI := finiteDimensional_boundStateSpace hfin
  obtain ⟨A₀, hA₀, h⟩ := card_le_finrank_boundStateSpace_add_two
  refine ⟨A₀, hA₀, fun a δ R Hm ε T ha hδ hR hTne hT hsep hiso hvis hε hε1 hεT => ?_⟩
  have := h a δ R Hm ε T ha hδ hR hTne hT hsep hiso hvis hε hε1 hεT
  have := finrank_boundStateSpace_le hfin
  omega

end RHTower.CHMDPolar
