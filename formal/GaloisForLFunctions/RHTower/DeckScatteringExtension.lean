import GaloisForLFunctions.RHTower.DeckIncompleteEisensteinMellin

/-!
# The scattering operator on the closed half-plane

* `scatExt v` is `s ↦ Φ̃(s) v` with its removable value at `s = 1/2`; its coordinates are
  holomorphic at every point of `{Re s > 1/2} \ {1}`, of the critical line, and at `1/2`
  (`differentiableAt_scatExt_apply`).
* `‖Φ̃(s) v‖ ≤ 4 ‖v‖` for `1/2 ≤ Re s ≤ 2`, `|Im s| ≥ 1` (`norm_scatExt_le`), and
  `‖Φ̃(1/2 + it) v‖ = ‖v‖` for every real `t`, including `t = 0` (`norm_scatExt_line`).
* **Symmetry** `⟨Φ̃(s) v, w⟩_β = ⟨v, Φ̃(s) w⟩_β` (`bil_scatVec_comm`): the entry `φ_{∞,g∞}(s)` depends
  only on `±g₁₀ mod L`, and `(g⁻¹)₁₀ = -g₁₀`.
* **Adjoint on the line** `⟪Φ̃(1/2 - it) v, w⟫ = ⟪v, Φ̃(1/2 + it) w⟫` (`inner_scatVec_line_adjoint`),
  from symmetry and the reflection `conj Φ̃(s) = Φ̃(s̄)`.
-/

open UpperHalfPlane ModularGroup MeasureTheory Set Filter Topology Metric EisensteinSeries
open scoped MatrixGroups ENNReal InnerProductSpace ComplexConjugate

namespace GaloisForLFunctions.RHTower.DeckPointPair

open MaassFiniteDeckDirichlet MaassCongruenceL2 SelbergMaassCongruenceTrace
  GaloisForLFunctions.HTGeometry SelbergEisensteinStarCriticalLine

noncomputable section

variable {N : ℕ}

local instance gammaNormalDSE (N : ℕ) : (CongruenceSubgroup.Gamma (N + 1)).Normal :=
  CongruenceSubgroup.Gamma_normal (N + 1)

/-! ## Symmetry -/

theorem PhiS_eq_of_neg {σ σ' : SL(2, ℤ)} (h : ((σ 1 0 : ℤ) : ZMod (N + 1)) = -((σ' 1 0 : ℤ) : ZMod (N + 1))) :
    SelbergEisensteinCuspScattering.PhiS (N + 1) σ = SelbergEisensteinCuspScattering.PhiS (N + 1) σ' := by
  funext x
  unfold SelbergEisensteinCuspScattering.PhiS
  rw [h, neg_neg, add_comm]

theorem phiExt_eq_of_neg {σ σ' : SL(2, ℤ)} (h : ((σ 1 0 : ℤ) : ZMod (N + 1)) = -((σ' 1 0 : ℤ) : ZMod (N + 1)))
    (s : ℂ) : SelbergEisensteinCriticalLine.phiExt (N + 1) σ s = SelbergEisensteinCriticalLine.phiExt (N + 1) σ' s := by
  unfold SelbergEisensteinCriticalLine.phiExt
  rw [PhiS_eq_of_neg h]

theorem phiExt_out_inv (g : Deck N) (s : ℂ) :
    SelbergEisensteinCriticalLine.phiExt (N + 1) (Quotient.out (g⁻¹ : Deck N)) s =
      SelbergEisensteinCriticalLine.phiExt (N + 1) (Quotient.out g) s := by
  refine phiExt_eq_of_neg ?_ s
  have h : (QuotientGroup.mk (Quotient.out (g⁻¹ : Deck N) : SL(2, ℤ)) : Deck N) =
      QuotientGroup.mk (Quotient.out g)⁻¹ := by
    rw [QuotientGroup.out_eq', QuotientGroup.mk_inv, QuotientGroup.out_eq']
  rw [mk_eq_mk_apply_one_zero h, Matrix.SpecialLinearGroup.SL2_inv_expl]
  simp

/-- **Symmetry of the scattering operator** for the bilinear pairing. -/
theorem bil_scatVec_comm (s : ℂ) (v w : DeckSpace N) : bil (scatVec s v) w = bil v (scatVec s w) := by
  simp only [bil, scatVec_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm, ← Equiv.sum_comp (Equiv.inv (Deck N))]
  refine Finset.sum_congr rfl fun g _ => ?_
  conv_rhs => rw [← Equiv.sum_comp (Equiv.mulRight g⁻¹)]
  refine Finset.sum_congr rfl fun q _ => ?_
  simp only [Equiv.inv_apply, Equiv.coe_mulRight, inv_inv, inv_mul_cancel_right]
  rw [phiExt_out_inv]
  ring

/-- **The scattering operator is self-adjoint up to reflection on the critical line.** -/
theorem inner_scatVec_line_adjoint {t : ℝ} (ht : t ≠ 0) (v w : DeckSpace N) :
    ⟪scatVec ((1 / 2 : ℝ) + (-t) * Complex.I) v, w⟫_ℂ =
      ⟪v, scatVec ((1 / 2 : ℝ) + t * Complex.I) w⟫_ℂ := by
  have hs : ((1 / 2 : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * Complex.I ∈ closedHalfDom := by
    refine ⟨by simp, ?_, ?_⟩ <;> intro h <;> have := congrArg Complex.im h <;> simp at this <;>
      exact ht this
  have hconj : conj (((1 / 2 : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * Complex.I) =
      ((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I := by
    apply Complex.ext <;> simp
  have hinner : ∀ X Y : DeckSpace N, ⟪X, Y⟫_ℂ = bil (deckConjVec X) Y := fun X Y => by
    rw [bil_eq_inner, deckConjVec_deckConjVec]
  have e : ((1 / 2 : ℝ) : ℂ) + (-t : ℂ) * Complex.I = ((1 / 2 : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [e, hinner, deckConjVec_scatVec hs, hconj, bil_scatVec_comm, hinner]

/-! ## The removable value at `1/2` -/

/-- `s ↦ Φ̃(s) v` with its removable value at `s = 1/2`. -/
def scatExt (v : DeckSpace N) : ℂ → DeckSpace N :=
  Function.update (fun s => scatVec s v) (1 / 2)
    (limUnder (𝓝[≠] (1 / 2 : ℂ)) fun s => scatVec s v)

theorem scatExt_of_ne {s : ℂ} (hs : s ≠ 1 / 2) (v : DeckSpace N) : scatExt v s = scatVec s v :=
  Function.update_of_ne hs _ _

theorem tendsto_scatExt_half (hN : 2 ≤ N) {v : DeckSpace N} (hv : IsCuspVec v) :
    Tendsto (fun s => scatVec s v) (𝓝[≠] (1 / 2 : ℂ)) (𝓝 (scatExt v (1 / 2))) := by
  obtain ⟨w₀, hw₀⟩ := exists_tendsto_scatVec_half hN hv
  rw [scatExt, Function.update_self, hw₀.limUnder_eq]
  exact hw₀

theorem continuousAt_scatExt_half (hN : 2 ≤ N) {v : DeckSpace N} (hv : IsCuspVec v) :
    ContinuousAt (scatExt v) (1 / 2) := by
  have h := tendsto_scatExt_half hN hv
  rw [scatExt, Function.update_self] at h
  exact continuousAt_update_same.2 h

theorem half_not_mem_contDom : (1 / 2 : ℂ) ∉ contDom N := fun h => h.1.2.1 (by norm_num)

theorem differentiableAt_scatExt_apply_of_mem (v : DeckSpace N) (q : Deck N) {s : ℂ}
    (hs : s ∈ contDom N) : DifferentiableAt ℂ (fun s => scatExt v s q) s := by
  have hne : s ≠ 1 / 2 := fun h => half_not_mem_contDom (h ▸ hs)
  refine (differentiableAt_scatVec_apply v q hs.1 hs.2).congr_of_eventuallyEq ?_
  filter_upwards [isOpen_compl_singleton.mem_nhds hne] with u hu
  rw [scatExt_of_ne hu]

theorem differentiableAt_scatExt_apply_half (hN : 2 ≤ N) {v : DeckSpace N} (hv : IsCuspVec v)
    (q : Deck N) : DifferentiableAt ℂ (fun s => scatExt v s q) (1 / 2) := by
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1
    (eventually_nhdsWithin_iff.1 (eventually_mem_contDom_half (N := N)))
  have hU : ball (1 / 2 : ℂ) δ ∈ 𝓝 (1 / 2 : ℂ) := ball_mem_nhds _ hδ
  have hdiff : DifferentiableOn ℂ (fun s => scatExt v s q) (ball (1 / 2 : ℂ) δ) := by
    refine (Complex.differentiableOn_compl_singleton_and_continuousAt_iff hU).1 ⟨fun s hs => ?_, ?_⟩
    · exact (differentiableAt_scatExt_apply_of_mem v q (hball hs.1 hs.2)).differentiableWithinAt
    · exact (EuclideanSpace.proj q).continuous.continuousAt.comp (continuousAt_scatExt_half hN hv)
  exact hdiff.differentiableAt hU

theorem mem_contDom_of_line {t : ℝ} (ht : t ≠ 0) : ((1 / 2 : ℝ) : ℂ) + t * Complex.I ∈ contDom N :=
  line_mem_contDom ht _ rfl

/-- Holomorphy of the coordinates of `Φ̃` on the closed half-plane minus `{1}`. -/
theorem differentiableAt_scatExt_apply (hN : 2 ≤ N) {v : DeckSpace N} (hv : IsCuspVec v) (q : Deck N)
    {s : ℂ} (hs : 1 / 2 ≤ s.re) (hs1 : s ≠ 1) : DifferentiableAt ℂ (fun s => scatExt v s q) s := by
  rcases hs.lt_or_eq with hlt | heq
  · exact differentiableAt_scatExt_apply_of_mem v q (mem_contDom_of_half_lt hlt hs1)
  · by_cases him : s.im = 0
    · have : s = 1 / 2 := Complex.ext (by simpa using heq.symm) (by simpa using him)
      rw [this]
      exact differentiableAt_scatExt_apply_half hN hv q
    · have : s = ((1 / 2 : ℝ) : ℂ) + (s.im : ℂ) * Complex.I :=
        Complex.ext (by simpa using heq.symm) (by simp)
      rw [this]
      exact differentiableAt_scatExt_apply_of_mem v q (mem_contDom_of_line him)

theorem differentiableAt_inner_scatExt (hN : 2 ≤ N) (u : DeckSpace N) {v : DeckSpace N}
    (hv : IsCuspVec v) {s : ℂ} (hs : 1 / 2 ≤ s.re) (hs1 : s ≠ 1) :
    DifferentiableAt ℂ (fun s => ⟪u, scatExt v s⟫_ℂ) s := by
  simp_rw [PiLp.inner_apply]
  refine DifferentiableAt.fun_sum fun q _ => ?_
  simp only [RCLike.inner_apply]
  exact (differentiableAt_scatExt_apply hN hv q hs hs1).mul_const _

theorem continuousAt_deck_of_coords {X : Type*} [TopologicalSpace X] {F : X → DeckSpace N} {x : X}
    (h : ∀ q, ContinuousAt (fun x => F x q) x) : ContinuousAt F x := by
  have e : F = fun x => WithLp.toLp 2 (fun q => F x q) := funext fun x => rfl
  rw [e]
  exact (PiLp.continuous_toLp 2 _).continuousAt.comp (continuousAt_pi.2 h)

theorem continuousAt_scatExt (hN : 2 ≤ N) {v : DeckSpace N} (hv : IsCuspVec v) {s : ℂ}
    (hs : 1 / 2 ≤ s.re) (hs1 : s ≠ 1) : ContinuousAt (scatExt v) s :=
  continuousAt_deck_of_coords fun q => (differentiableAt_scatExt_apply hN hv q hs hs1).continuousAt

/-! ## Bounds -/

/-- `Φ̃` is unitary at every point of the critical line, including `1/2`. -/
theorem norm_scatExt_line (hN : 2 ≤ N) {v : DeckSpace N} (hv : IsCuspVec v) (t : ℝ) :
    ‖scatExt v (((1 / 2 : ℝ) : ℂ) + t * Complex.I)‖ = ‖v‖ := by
  have hc : Continuous fun t : ℝ => ‖scatExt v (((1 / 2 : ℝ) : ℂ) + t * Complex.I)‖ := by
    refine continuous_norm.comp (continuous_iff_continuousAt.2 fun t => ?_)
    refine ContinuousAt.comp (f := fun t : ℝ => ((1 / 2 : ℝ) : ℂ) + t * Complex.I)
      (continuousAt_scatExt hN hv (by simp) fun h => ?_) (by fun_prop)
    have := congrArg Complex.re h
    norm_num at this
  have he := Continuous.ext_on (dense_compl_singleton (0 : ℝ)) hc continuous_const fun t ht => by
    have hne : ((1 / 2 : ℝ) : ℂ) + t * Complex.I ≠ 1 / 2 := fun h => ht (by
      have := congrArg Complex.im h; simpa using this)
    rw [scatExt_of_ne hne, norm_scatVec_line hN ht hv]
  exact congrFun he t

/-- `‖Φ̃(s) v‖ ≤ 4 ‖v‖` on the strip `1/2 ≤ Re s ≤ 2`, `|Im s| ≥ 1`. -/
theorem norm_scatExt_le (hN : 2 ≤ N) {v : DeckSpace N} (hv : IsCuspVec v) {s : ℂ}
    (h1 : 1 / 2 ≤ s.re) (h2 : s.re ≤ 2) (ht : 1 ≤ |s.im|) : ‖scatExt v s‖ ≤ 4 * ‖v‖ := by
  rcases h1.lt_or_eq with hlt | heq
  · have hne : s ≠ 1 / 2 := fun h => by rw [h] at hlt; norm_num at hlt
    rw [scatExt_of_ne hne]
    exact norm_scatVec_le_four hN hlt h2 ht hv
  · have : s = ((1 / 2 : ℝ) : ℂ) + (s.im : ℂ) * Complex.I :=
      Complex.ext (by simpa using heq.symm) (by simp)
    rw [this, norm_scatExt_line hN hv]
    linarith [norm_nonneg v]

end

end GaloisForLFunctions.RHTower.DeckPointPair
