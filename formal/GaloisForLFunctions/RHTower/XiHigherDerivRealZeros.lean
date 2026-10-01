import GaloisForLFunctions.RHTower.XiDerivCriticalLineProportion
import GaloisForLFunctions.RHTower.LaguerreInequality

/-!
# Two thirds of the zeros of every derivative of Riemann's `Ξ` are real

Let `Ξ(t) = ξ(1/2 + it)` (real, `Xi`). **Theorem** (`eventually_iteratedDeriv_Xi_zeros_ge`): for
every `k` and every `ε > 0`, for all large `T`, the `k`-th derivative `Ξ^{(k)}` has at least
`(HD 1 − ε)N(T) − k` distinct zeros in `(0, T]`. Here `N(T)` is the number of zeros of `ξ` with
ordinate in `(0, T]` and `HD 1 = 0.6725…` is the Montgomery–Taylor constant.

**Proof.** Rolle between consecutive zeros (`exists_finset_between_card`) loses at most one zero
per differentiation (`exists_deriv_zeros_card`). The zeros of `Ξ` in `(0, T]` are the ordinates of
the distinct critical zeros of `ξ`, at least `(HD 1 − ε)N(T)` of them by Zeta23.
-/

open Complex Set Filter

namespace RHTower

noncomputable section

theorem contDiff_Xi : ContDiff ℝ ⊤ Xi := by
  have h1 : ContDiff ℝ ⊤ (fun t : ℝ => (1 / 2 : ℂ) + (t : ℂ) * Complex.I) :=
    contDiff_const.add (Complex.ofRealCLM.contDiff.mul contDiff_const)
  have h2 : ContDiff ℝ ⊤ (fun t : ℝ => xi ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)) :=
    (xi_differentiable.contDiff (n := ⊤)).restrict_scalars ℝ |>.comp h1
  exact Complex.reCLM.contDiff.comp h2

/-- **Rolle count.** If `f` is differentiable and `S` is a finite set of zeros of `f`, then `f'`
has a finite set of zeros, each strictly between two points of `S`, of size at least `#S − 1`. -/
theorem exists_deriv_zeros_card {f : ℝ → ℝ} (hf : Differentiable ℝ f) {S : Finset ℝ}
    (hS : ∀ a ∈ S, f a = 0) :
    ∃ C : Finset ℝ, (∀ c ∈ C, deriv f c = 0 ∧ ∃ a ∈ S, ∃ b ∈ S, a < c ∧ c < b) ∧
      S.card ≤ C.card + 1 :=
  exists_finset_between_card (P := fun c => deriv f c = 0) fun a ha b hb hab _ => by
    obtain ⟨c, hc, hc0⟩ := exists_deriv_eq_zero hab hf.continuous.continuousOn
      (by rw [hS a ha, hS b hb])
    exact ⟨c, hc.1, hc.2, hc0⟩

/-- **Iterated Rolle count** for `Ξ` on `(0, T]`. -/
theorem exists_iteratedDeriv_Xi_zeros {T : ℝ} {S : Finset ℝ}
    (hS : ∀ a ∈ S, 0 < a ∧ a ≤ T ∧ Xi a = 0) (k : ℕ) :
    ∃ C : Finset ℝ, (∀ c ∈ C, 0 < c ∧ c ≤ T ∧ iteratedDeriv k Xi c = 0) ∧
      S.card ≤ C.card + k := by
  induction k with
  | zero => exact ⟨S, fun a ha => ⟨(hS a ha).1, (hS a ha).2.1, by simpa using (hS a ha).2.2⟩,
      by simp⟩
  | succ k ih =>
    obtain ⟨C, hC, hcard⟩ := ih
    have hdiff : Differentiable ℝ (iteratedDeriv k Xi) :=
      contDiff_Xi.differentiable_iteratedDeriv k (by exact_mod_cast WithTop.coe_lt_top _)
    obtain ⟨C', hC', hcard'⟩ := exists_deriv_zeros_card hdiff (S := C) fun a ha => (hC a ha).2.2
    refine ⟨C', fun c hc => ?_, by omega⟩
    obtain ⟨h0, a, ha, b, hb, hac, hcb⟩ := hC' c hc
    refine ⟨lt_trans (hC a ha).1 hac, le_trans hcb.le (hC b hb).2.1, ?_⟩
    rw [iteratedDeriv_succ]
    exact h0

/-- **Two thirds of the zeros of every derivative of `Ξ` are real.** -/
theorem eventually_iteratedDeriv_Xi_zeros_ge (k : ℕ) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, ∃ C : Finset ℝ,
      (∀ c ∈ C, 0 < c ∧ c ≤ T ∧ iteratedDeriv k Xi c = 0) ∧
      (Zeta23.ThmD.HD 1 - ε) * (xiPosZeroCount T : ℝ) - k ≤ C.card := by
  classical
  intro ε hε
  obtain ⟨T₀, hT₀⟩ := lamzouri_montgomeryTaylor_simpleCritical_epsilon ε hε
  refine ⟨T₀, fun T hT => ?_⟩
  -- the ordinates of the distinct critical zeros of `ξ`
  set Z := (stripFinsetPos T).filter (fun z => z.re = 1 / 2) with hZ
  set S : Finset ℝ := Z.image Complex.im with hSdef
  have hS : ∀ a ∈ S, 0 < a ∧ a ≤ T ∧ Xi a = 0 := by
    intro a ha
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨hzS, hre⟩ := Finset.mem_filter.mp hz
    obtain ⟨-, -, h0, hTz, hxi⟩ := mem_stripFinsetPos.mp hzS
    refine ⟨h0, hTz, ?_⟩
    have hz' : (1 / 2 : ℂ) + ((z.im : ℝ) : ℂ) * Complex.I = z := by
      rw [eq_half_add_I_mul_im hre]; simp; ring
    have := xiHalfLine_real z.im
    rw [hz', hxi] at this
    exact_mod_cast this.symm
  obtain ⟨C, hC, hcard⟩ := exists_iteratedDeriv_Xi_zeros hS k
  refine ⟨C, hC, ?_⟩
  have hinj : Set.InjOn Complex.im (Z : Set ℂ) := by
    intro z hz w hw him
    have hz' := (Finset.mem_filter.mp (Finset.mem_coe.mp hz)).2
    have hw' := (Finset.mem_filter.mp (Finset.mem_coe.mp hw)).2
    rw [eq_half_add_I_mul_im hz', eq_half_add_I_mul_im hw', him]
  have hSZ : S.card = Z.card := Finset.card_image_of_injOn hinj
  have hsub : (stripFinsetPos T).filter
      (fun z => z.re = 1 / 2 ∧ (analyticOrderAt xi z).toNat = 1) ⊆ Z := by
    intro z hz
    obtain ⟨hzS, hre, -⟩ := Finset.mem_filter.mp hz
    exact Finset.mem_filter.mpr ⟨hzS, hre⟩
  have h1 : xiSimpleCriticalZeroCount T ≤ S.card := by
    rw [hSZ]; exact Finset.card_le_card hsub
  have h2 := hT₀ T hT
  have h3 : (xiSimpleCriticalZeroCount T : ℝ) ≤ C.card + k := by exact_mod_cast h1.trans hcard
  linarith

end

end RHTower
