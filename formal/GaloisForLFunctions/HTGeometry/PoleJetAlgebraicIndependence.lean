import GaloisForLFunctions.HTGeometry.PeriodicJetAlgebraicIndependence

/-!
# Blow-up adjoins the coordinate for free

Periodicity is one mechanism that forbids the coordinate from entering an algebraic relation with
the jets.  Blow-up is the other, and it is the one available to Cauchy-type packets, whose poles sit
on the boundary of the region.

If a function blows up along sequences from the region approaching each point of an infinite set,
then in any relation `∑ᵢ pᵢ(w) F(w)ⁱ = 0` the top coefficient must vanish at every one of those
points, so it vanishes identically.  No periodicity, no analyticity, no order of growth — only that
the function is large near infinitely many boundary points while the coordinate stays bounded there.
-/

open Filter Topology Polynomial

namespace GaloisForLFunctions.HTGeometry

/-! ## The dominance estimate -/

/-- Evaluating a polynomial family along a converging argument and a blowing-up value forces the top
coefficient to vanish in the limit. -/
theorem eval_top_eq_zero_of_blowUp {J : ℕ} (q : ℕ → ℂ[X]) (Fv : ℕ → ℂ) (u : ℕ → ℂ) (ζ : ℂ)
    (hu : Tendsto u atTop (𝓝 ζ)) (hF : Tendsto (fun j => ‖Fv j‖) atTop atTop)
    (hrel : ∀ j, ∑ i ∈ Finset.range (J + 1), (q i).eval (u j) * Fv j ^ i = 0) :
    (q J).eval ζ = 0 := by
  have hcont : ∀ i : ℕ, Tendsto (fun j => ‖(q i).eval (u j)‖) atTop (𝓝 ‖(q i).eval ζ‖) := by
    intro i
    exact (continuous_norm.tendsto _).comp (((q i).continuous.tendsto ζ).comp hu)
  obtain _ | J := J
  · have hz : ∀ j, (q 0).eval (u j) = 0 := by
      intro j
      simpa using hrel j
    have hlim : Tendsto (fun j => ‖(q 0).eval (u j)‖) atTop (𝓝 0) := by
      simp only [hz, norm_zero]
      exact tendsto_const_nhds
    have := tendsto_nhds_unique (hcont 0) hlim
    exact norm_eq_zero.mp this
  · set B : ℕ → ℝ := fun j => ∑ i ∈ Finset.range (J + 1), ‖(q i).eval (u j)‖ with hBdef
    have hB : Tendsto B atTop (𝓝 (∑ i ∈ Finset.range (J + 1), ‖(q i).eval ζ‖)) :=
      tendsto_finsetSum _ fun i _ => hcont i
    have hbound : ∀ᶠ j in atTop, ‖(q (J + 1)).eval (u j)‖ ≤ B j / ‖Fv j‖ := by
      filter_upwards [hF.eventually_ge_atTop 1] with j hj
      have hpos : (0 : ℝ) < ‖Fv j‖ := lt_of_lt_of_le zero_lt_one hj
      have hsplit : (q (J + 1)).eval (u j) * Fv j ^ (J + 1)
          = -∑ i ∈ Finset.range (J + 1), (q i).eval (u j) * Fv j ^ i := by
        have := hrel j
        rw [Finset.sum_range_succ] at this
        linear_combination this
      have hnorm : ‖(q (J + 1)).eval (u j)‖ * ‖Fv j‖ ^ (J + 1)
          ≤ B j * ‖Fv j‖ ^ J := by
        have h1 : ‖(q (J + 1)).eval (u j)‖ * ‖Fv j‖ ^ (J + 1)
            = ‖-∑ i ∈ Finset.range (J + 1), (q i).eval (u j) * Fv j ^ i‖ := by
          rw [← hsplit, norm_mul, norm_pow]
        rw [h1, norm_neg]
        refine le_trans (norm_sum_le _ _) ?_
        rw [hBdef, Finset.sum_mul]
        refine Finset.sum_le_sum fun i hi => ?_
        rw [norm_mul, norm_pow]
        refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        exact pow_le_pow_right₀ hj (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))
      rw [le_div_iff₀ hpos]
      have hcancel : ‖Fv j‖ ^ (J + 1) = ‖Fv j‖ ^ J * ‖Fv j‖ := by ring
      rw [hcancel, ← mul_assoc] at hnorm
      have hJpos : (0 : ℝ) < ‖Fv j‖ ^ J := pow_pos hpos J
      nlinarith [hnorm, hJpos, norm_nonneg ((q (J + 1)).eval (u j)), hpos]
    have hlim : Tendsto (fun j => B j / ‖Fv j‖) atTop (𝓝 0) := hB.div_atTop hF
    have hle := le_of_tendsto_of_tendsto (hcont (J + 1)) hlim hbound
    exact norm_eq_zero.mp (le_antisymm hle (norm_nonneg _))


/-! ## Blow-up data -/

/-- The function blows up along sequences from the region approaching each point of an infinite
set of boundary values. -/
def HasBlowUpSet (S : Set ℂ) (F : ℂ → ℂ) (Z : Set ℂ) : Prop :=
  Z.Infinite ∧ ∀ ζ ∈ Z, ∃ u : ℕ → ℂ, (∀ j, u j ∈ S) ∧
    Tendsto u atTop (𝓝 ζ) ∧ Tendsto (fun j => ‖F (u j)‖) atTop atTop

theorem aeval_pi_apply {ι : Type*} (g : ι → ℂ) (r : ℂ[X]) (i : ι) :
    (Polynomial.aeval g r) i = r.eval (g i) := by
  have h := Polynomial.aeval_algHom_apply (Pi.evalAlgHom ℂ (fun _ : ι => ℂ) i) g r
  rw [Polynomial.coe_aeval_eq_eval] at h
  exact h.symm

theorem range_matrixCons_one {α : Type*} (x : α) : Set.range (![x]) = {x} := by
  ext g
  constructor
  · rintro ⟨k, rfl⟩
    fin_cases k
    rfl
  · rintro rfl
    exact ⟨0, rfl⟩

/-- The coordinate is transcendental over the constants on any infinite region. -/
theorem transcendental_coe_of_infinite {S : Set ℂ} (hS : S.Infinite) :
    Transcendental ℂ (fun w : S => (w : ℂ)) := by
  rintro ⟨r, hr0, hr⟩
  refine hr0 (Polynomial.eq_zero_of_infinite_isRoot r (hS.mono ?_))
  intro w hw
  have := congrFun hr ⟨w, hw⟩
  rw [aeval_pi_apply] at this
  simpa using this

/-! ## Blow-up forbids the coordinate -/

/-- **The coordinate is transcendental over a blowing-up function.**  In a relation with polynomial
coefficients the top coefficient must vanish at every blow-up point, and there are infinitely
many. -/
theorem transcendental_restrict_of_hasBlowUpSet {S : Set ℂ} {F : ℂ → ℂ} {Z : Set ℂ}
    (h : HasBlowUpSet S F Z) :
    Transcendental (↥(Algebra.adjoin ℂ (Set.range (![fun w : S => (w : ℂ)]))))
      (Set.restrict S F) := by
  obtain ⟨hZ, hblow⟩ := h
  set coord : S → ℂ := fun w => (w : ℂ) with hcoord
  set A := Algebra.adjoin ℂ (Set.range (![coord] : Fin 1 → (S → ℂ))) with hA
  have hAeq : A = (Polynomial.aeval coord).range := by
    rw [hA, range_matrixCons_one, Algebra.adjoin_singleton_eq_range_aeval]
  rintro ⟨p, hp0, hp⟩
  have hmem : ∀ j : ℕ, ∃ r : ℂ[X], ∀ w : S, ((p.coeff j : S → ℂ)) w = r.eval ((w : ℂ)) := by
    intro j
    have h2 : ((p.coeff j : S → ℂ)) ∈ (Polynomial.aeval coord).range := hAeq.le (p.coeff j).2
    obtain ⟨r, hr⟩ := h2
    exact ⟨r, fun w => by rw [← hr]; exact aeval_pi_apply coord r w⟩
  choose q hq using hmem
  set J := p.natDegree with hJ
  have hcoeffJ : ((p.coeff J : S → ℂ)) ≠ 0 := by
    intro hzero
    exact (Polynomial.leadingCoeff_ne_zero.mpr hp0) (Subtype.ext hzero)
  set ev : S → (↥A →+* ℂ) := fun v =>
    (Pi.evalRingHom (fun _ : S => ℂ) v).comp (algebraMap (↥A) (S → ℂ)) with hev
  have key : ∀ v : S,
      ∑ i ∈ Finset.range (J + 1), (q i).eval ((v : ℂ)) * (F (v : ℂ)) ^ i = 0 := by
    intro v
    have h := congrFun hp v
    rw [Polynomial.aeval_def] at h
    have hcomm := Polynomial.hom_eval₂ p (algebraMap (↥A) (S → ℂ))
      (Pi.evalRingHom (fun _ : S => ℂ) v) (Set.restrict S F)
    have hzero : Polynomial.eval₂ (ev v) (F (v : ℂ)) p = 0 := by
      calc Polynomial.eval₂ (ev v) (F (v : ℂ)) p
          = (Pi.evalRingHom (fun _ : S => ℂ) v)
              (Polynomial.eval₂ (algebraMap (↥A) (S → ℂ)) (Set.restrict S F) p) := hcomm.symm
        _ = 0 := h
    rw [← Polynomial.eval_map] at hzero
    rw [Polynomial.eval_eq_sum_range' (n := J + 1)
      (lt_of_le_of_lt Polynomial.natDegree_map_le (Nat.lt_succ_self J))] at hzero
    rw [← hzero]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Polynomial.coeff_map]
    congr 1
    exact (hq i v).symm
  have hroot : ∀ ζ ∈ Z, (q J).eval ζ = 0 := by
    intro ζ hζ
    obtain ⟨u, humem, hu, huF⟩ := hblow ζ hζ
    refine eval_top_eq_zero_of_blowUp q (fun j => F (u j)) u ζ hu huF ?_
    intro j
    exact key ⟨u j, humem j⟩
  have hqJ : q J = 0 :=
    Polynomial.eq_zero_of_infinite_isRoot _ (hZ.mono (fun ζ hζ => hroot ζ hζ))
  refine hcoeffJ (funext fun w => ?_)
  rw [hq J w, hqJ]
  simp

/-! ## The universal law -/

/-- The two-element index swap. -/
def optionFinOneSwap : Option (Fin 1) ≃ Option (Fin 1) where
  toFun o := o.elim (some 0) fun _ => none
  invFun o := o.elim (some 0) fun _ => none
  left_inv o := by cases o with | none => rfl | some k => fin_cases k; rfl
  right_inv o := by cases o with | none => rfl | some k => fin_cases k; rfl

/-- **Blow-up upgrades transcendence of a single jet to algebraic independence with the coordinate
adjoined.**  This is the mechanism available to Cauchy-type packets, whose poles lie on the boundary
of the region. -/
theorem algebraicIndependent_restrict_jetEvaluationFamily_of_blowUp {S : Set ℂ} (hS : S.Infinite)
    {F : ℂ → ℂ} {Z : Set ℂ} (h : HasBlowUpSet S F Z) :
    AlgebraicIndependent ℂ (fun i => Set.restrict S (jetEvaluationFamily ![F] i)) := by
  have hswapped : AlgebraicIndependent ℂ
      (fun o : Option (Fin 1) =>
        o.elim (Set.restrict S F) (![fun w : S => (w : ℂ)])) := by
    refine AlgebraicIndependent.option_iff.mpr ⟨?_, transcendental_restrict_of_hasBlowUpSet h⟩
    rw [algebraicIndependent_unique_type_iff]
    exact transcendental_coe_of_infinite hS
  have hcomp := hswapped.comp optionFinOneSwap optionFinOneSwap.injective
  have hfam : (fun i => Set.restrict S (jetEvaluationFamily ![F] i))
      = (fun o : Option (Fin 1) =>
          o.elim (Set.restrict S F) (![fun w : S => (w : ℂ)])) ∘ optionFinOneSwap := by
    funext i
    cases i with
    | none => rfl
    | some k => fin_cases k; rfl
  rw [hfam]
  exact hcomp


/-! ## The full-rank datum from blow-up -/

theorem infinite_upperHalfPlane : (upperHalfPlane).Infinite := by
  refine Set.infinite_of_injective_forall_mem
    (f := fun n : ℕ => (⟨0, (n : ℝ) + 1⟩ : ℂ)) ?_ ?_
  · intro n₁ n₂ hn
    have him : ((n₁ : ℝ) + 1) = ((n₂ : ℝ) + 1) := congrArg Complex.im hn
    have : (n₁ : ℝ) = (n₂ : ℝ) := by linarith
    exact_mod_cast this
  · intro n
    show (0 : ℝ) < ((n : ℝ) + 1)
    positivity

/-- **The full-rank datum from a blowing-up jet.**  A single jet with infinitely many boundary
blow-up points already produces the node packet demanded by the translation-rank laws. -/
theorem exists_row_packet_upperHalfPlane_of_blowUp {κ row : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype row] {q : ℕ} {F : ℂ → ℂ} {Z : Set ℂ} (h : HasBlowUpSet upperHalfPlane F Z)
    {exponent : κ → (Fin 1 →₀ ℕ)} (hexp : Function.Injective exponent)
    (f : κ × Fin (q + 1) → row) (hf : Function.Injective f) :
    ∃ z : row → ℂ, (∀ b, 0 < (z b).im) ∧ Function.Injective z ∧
      Function.Injective
        (expandedDifferentialEvaluationMatrix q 1 z exponent
          (fun p => ![F] p.2 (z p.1))).mulVec :=
  exists_row_packet_upperHalfPlane_of_algebraicIndependent
    (algebraicIndependent_restrict_jetEvaluationFamily_of_blowUp infinite_upperHalfPlane h)
    hexp f hf


/-! ## A meromorphic realization of the blow-up datum -/

/-- A function with a pole at every integer, holomorphic on the upper half-plane: the model shape of
a Cauchy-type packet whose poles lie on the boundary. -/
noncomputable def periodicPoleModel (w : ℂ) : ℂ :=
  (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * w) - 1)⁻¹

theorem re_two_pi_I_mul (w : ℂ) :
    (2 * (Real.pi : ℂ) * Complex.I * w).re = -(2 * Real.pi * w.im) := by
  simp [Complex.mul_re, Complex.mul_im]

theorem exp_two_pi_I_mul_sub_one_ne_zero {w : ℂ} (hw : 0 < w.im) :
    Complex.exp (2 * (Real.pi : ℂ) * Complex.I * w) - 1 ≠ 0 := by
  intro h
  have h1 : Complex.exp (2 * (Real.pi : ℂ) * Complex.I * w) = 1 := by
    rwa [sub_eq_zero] at h
  have hnorm : Real.exp ((2 * (Real.pi : ℂ) * Complex.I * w).re) = 1 := by
    rw [← Complex.norm_exp, h1, norm_one]
  rw [re_two_pi_I_mul] at hnorm
  have hlt : 0 < 2 * Real.pi * w.im := by
    have := Real.pi_pos
    positivity
  have hone : Real.exp (-(2 * Real.pi * w.im)) < 1 := by
    rw [Real.exp_lt_one_iff]
    linarith
  linarith

/-- **The blow-up datum is realized.**  Every integer is a boundary pole reached vertically from the
upper half-plane. -/
theorem hasBlowUpSet_periodicPoleModel :
    HasBlowUpSet upperHalfPlane periodicPoleModel (Set.range fun n : ℤ => (n : ℂ)) := by
  refine ⟨Set.infinite_range_of_injective (fun a b h => by exact_mod_cast h), ?_⟩
  rintro ζ ⟨n, rfl⟩
  set t : ℕ → ℝ := fun j => 1 / ((j : ℝ) + 1) with ht
  set u : ℕ → ℂ := fun j => (n : ℂ) + (t j : ℂ) * Complex.I with hu
  have htpos : ∀ j, 0 < t j := by
    intro j
    rw [ht]
    positivity
  have himu : ∀ j, (u j).im = t j := by
    intro j
    rw [hu]
    simp
  have hpos : ∀ j, 0 < (u j).im := by
    intro j
    rw [himu j]
    exact htpos j
  have ht0 : Filter.Tendsto t Filter.atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hlim : Filter.Tendsto u Filter.atTop (𝓝 ((n : ℂ))) := by
    have hmul : Filter.Tendsto (fun j => ((t j : ℂ)) * Complex.I) Filter.atTop (𝓝 0) := by
      have hc : Filter.Tendsto (fun j => ((t j : ℂ))) Filter.atTop (𝓝 0) := by
        simpa [Function.comp_def] using (Complex.continuous_ofReal.tendsto 0).comp ht0
      simpa using hc.mul_const Complex.I
    simpa [hu] using tendsto_const_nhds.add hmul
  refine ⟨u, fun j => hpos j, hlim, ?_⟩
  have hne : ∀ j : ℕ, Complex.exp (2 * (Real.pi : ℂ) * Complex.I * u j) - 1 ≠ 0 :=
    fun j => exp_two_pi_I_mul_sub_one_ne_zero (hpos j)
  have hval : Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ)) - 1 = 0 := by
    have hre : (2 : ℂ) * (Real.pi : ℂ) * Complex.I * (n : ℂ)
        = (n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by ring
    rw [hre, Complex.exp_int_mul_two_pi_mul_I, sub_self]
  have hexp : Filter.Tendsto
      (fun j : ℕ => Complex.exp (2 * (Real.pi : ℂ) * Complex.I * u j) - 1)
      Filter.atTop (𝓝 0) := by
    have hinner : Filter.Tendsto (fun j : ℕ => 2 * (Real.pi : ℂ) * Complex.I * u j)
        Filter.atTop (𝓝 (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ))) :=
      hlim.const_mul _
    have := ((Complex.continuous_exp.tendsto _).comp hinner).sub
      (tendsto_const_nhds (x := (1 : ℂ)))
    rwa [hval] at this
  have hgt : Filter.Tendsto
      (fun j : ℕ => ‖Complex.exp (2 * (Real.pi : ℂ) * Complex.I * u j) - 1‖)
      Filter.atTop (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · simpa using hexp.norm
    · filter_upwards with j
      exact norm_pos_iff.mpr (hne j)
  refine (tendsto_inv_nhdsGT_zero.comp hgt).congr fun j => ?_
  rw [periodicPoleModel, norm_inv]
  rfl


/-- **A second unconditional realization of the full-rank datum**, carried by a meromorphic jet with
boundary poles instead of a periodic one. -/
theorem exists_row_packet_upperHalfPlane_periodicPoleModel {κ row : Type*} [Fintype κ]
    [DecidableEq κ] [Fintype row] {q : ℕ} {exponent : κ → (Fin 1 →₀ ℕ)}
    (hexp : Function.Injective exponent) (f : κ × Fin (q + 1) → row) (hf : Function.Injective f) :
    ∃ z : row → ℂ, (∀ b, 0 < (z b).im) ∧ Function.Injective z ∧
      Function.Injective
        (expandedDifferentialEvaluationMatrix q 1 z exponent
          (fun p => ![periodicPoleModel] p.2 (z p.1))).mulVec :=
  exists_row_packet_upperHalfPlane_of_blowUp hasBlowUpSet_periodicPoleModel hexp f hf

end GaloisForLFunctions.HTGeometry
