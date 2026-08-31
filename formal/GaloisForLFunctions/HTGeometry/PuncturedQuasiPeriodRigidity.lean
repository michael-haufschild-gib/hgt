import GaloisForLFunctions.HTGeometry.QuasiPeriodPoleRigidity
import GaloisForLFunctions.HTGeometry.TripticGermConstraint

/-!
# Quasi-periods that hold only on punctured neighbourhoods

The increments of a meromorphic function are identities of germs, so they hold on punctured
neighbourhoods rather than pointwise.  Pole orders are germ invariants, so the rank-three
pole-exclusion argument goes through unchanged; once the function is known to be pole-free the
punctured identities upgrade to genuine ones by continuity.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

/-- A step along which the germ of the function changes by a constant. -/
def HasPuncturedConstIncrement (f : ℂ → ℂ) (p : ℂ) : Prop :=
  ∃ c : ℂ, ∀ z, ∀ᶠ w in 𝓝[≠] z, f (w + p) = f w + c

theorem hasPuncturedConstIncrement_zero (f : ℂ → ℂ) : HasPuncturedConstIncrement f 0 :=
  ⟨0, fun z => by filter_upwards with w; simp⟩

theorem HasPuncturedConstIncrement.add {f : ℂ → ℂ} {x y : ℂ}
    (hx : HasPuncturedConstIncrement f x) (hy : HasPuncturedConstIncrement f y) :
    HasPuncturedConstIncrement f (x + y) := by
  obtain ⟨cx, hcx⟩ := hx
  obtain ⟨cy, hcy⟩ := hy
  refine ⟨cx + cy, fun z => ?_⟩
  have hpull := (tendsto_nhdsNE_add_const z y).eventually (hcx (z + y))
  filter_upwards [hpull, hcy z] with w h1 h2
  have hassoc : w + (x + y) = w + y + x := by ring
  rw [hassoc, h1, h2]
  ring

theorem HasPuncturedConstIncrement.neg {f : ℂ → ℂ} {x : ℂ}
    (hx : HasPuncturedConstIncrement f x) : HasPuncturedConstIncrement f (-x) := by
  obtain ⟨cx, hcx⟩ := hx
  refine ⟨-cx, fun z => ?_⟩
  have hpull := (tendsto_nhdsNE_add_const z (-x)).eventually (hcx (z + -x))
  filter_upwards [hpull] with w h1
  have hsimp : w + -x + x = w := by ring
  rw [hsimp] at h1
  linear_combination -h1

theorem HasPuncturedConstIncrement.zsmul {f : ℂ → ℂ} {x : ℂ}
    (hx : HasPuncturedConstIncrement f x) (a : ℤ) :
    HasPuncturedConstIncrement f (a • x) := by
  induction a using Int.induction_on with
  | zero => simpa using hasPuncturedConstIncrement_zero f
  | succ n ih =>
      have hstep : ((n : ℤ) + 1) • x = (n : ℤ) • x + x := by
        rw [add_smul, one_smul]
      rw [hstep]
      exact ih.add hx
  | pred n ih =>
      have hstep : (-(n : ℤ) - 1) • x = (-(n : ℤ)) • x + -x := by
        rw [sub_smul, one_smul, ← sub_eq_add_neg]
      rw [hstep]
      exact ih.add hx.neg

theorem hasPuncturedConstIncrement_of_mem_span {f : ℂ → ℂ} {ι : Type*} {v : ι → ℂ}
    (h : ∀ i, HasPuncturedConstIncrement f (v i)) :
    ∀ p ∈ Submodule.span ℤ (Set.range v), HasPuncturedConstIncrement f p := by
  intro p hp
  induction hp using Submodule.span_induction with
  | mem x hx => obtain ⟨i, rfl⟩ := hx; exact h i
  | zero => exact hasPuncturedConstIncrement_zero f
  | add x y _ _ hx hy => exact hx.add hy
  | smul a x _ hx => exact hx.zsmul a

/-! ### Pole orders are germ invariants -/

theorem meromorphicOrderAt_add_puncturedConstIncrement (f : ℂ → ℂ) {p c : ℂ} (z : ℂ)
    (hq : ∀ᶠ w in 𝓝[≠] z, f (w + p) = f w + c)
    (hneg : meromorphicOrderAt f z < 0) :
    meromorphicOrderAt f (z + p) = meromorphicOrderAt f z := by
  have hg : AnalyticAt ℂ (fun w : ℂ => w + p) z := by fun_prop
  have hgd : deriv (fun w : ℂ => w + p) z ≠ 0 := by simp
  have hcomp := meromorphicOrderAt_comp_of_deriv_ne_zero (f := f) hg hgd
  have hfg : (f ∘ fun w : ℂ => w + p) =ᶠ[𝓝[≠] z] (f + fun _ : ℂ => c) := by
    filter_upwards [hq] with w hw
    simpa only [Function.comp_apply, Pi.add_apply] using hw
  rw [meromorphicOrderAt_congr hfg] at hcomp
  have hconst : MeromorphicAt (fun _ : ℂ => c) z := (analyticAt_const).meromorphicAt
  have hordc : 0 ≤ meromorphicOrderAt (fun _ : ℂ => c) z :=
    (analyticAt_const (v := c)).meromorphicOrderAt_nonneg
  have hlt : meromorphicOrderAt f z < meromorphicOrderAt (fun _ : ℂ => c) z :=
    lt_of_lt_of_le hneg hordc
  have hsum := meromorphicOrderAt_add_eq_left_of_lt hconst hlt
  rw [← hcomp]
  exact hsum

theorem analyticAt_of_small_puncturedConstIncrements (f : ℂ → ℂ)
    (hf : MeromorphicNFOn f Set.univ) (p : ℕ → ℂ)
    (hp0 : Tendsto p atTop (𝓝 0)) (hpne : ∀ n, p n ≠ 0)
    (hq : ∀ n, HasPuncturedConstIncrement f (p n)) : ∀ z, AnalyticAt ℂ f z := by
  intro z
  apply (hf (Set.mem_univ z)).meromorphicOrderAt_nonneg_iff_analyticAt.mp
  by_contra hnonneg
  have hneg : meromorphicOrderAt f z < 0 := lt_of_not_ge hnonneg
  have hpz : Tendsto (fun n => z + p n) atTop (𝓝[≠] z) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨by simpa using (tendsto_const_nhds.add hp0 :
      Tendsto (fun n => z + p n) atTop (𝓝 (z + 0))), ?_⟩
    exact Filter.Eventually.of_forall fun n => by simp [hpne n]
  have hset : Set.univ \ {z} = ({z}ᶜ : Set ℂ) := by ext w; simp
  have hnear : ∀ᶠ w in 𝓝[≠] z, AnalyticAt ℂ f w := by
    rw [← hset]
    exact hf.meromorphicOn.eventually_analyticAt (Set.mem_univ z)
  have hevent : ∀ᶠ n in atTop, AnalyticAt ℂ f (z + p n) := hpz.eventually hnear
  rcases hevent.exists with ⟨n, hn⟩
  have hnonneg_n := hn.meromorphicOrderAt_nonneg
  obtain ⟨c, hc⟩ := hq n
  rw [meromorphicOrderAt_add_puncturedConstIncrement f z (hc z) hneg] at hnonneg_n
  exact (not_le_of_gt hneg) hnonneg_n

/-! ### Upgrading a punctured increment on an analytic function -/

theorem constIncrement_of_punctured_of_analytic {f : ℂ → ℂ}
    (han : ∀ z, AnalyticAt ℂ f z) {p c : ℂ}
    (hq : ∀ z, ∀ᶠ w in 𝓝[≠] z, f (w + p) = f w + c) : ∀ z, f (z + p) = f z + c := by
  intro z
  have hcont1 : ContinuousAt (fun w : ℂ => f (w + p)) z := by
    have hs : ContinuousAt (fun w : ℂ => w + p) z := continuousAt_id.add continuousAt_const
    simpa only [Function.comp_def] using ((han (z + p)).continuousAt).comp_of_eq hs rfl
  have hcont2 : ContinuousAt (fun w : ℂ => f w + c) z :=
    ((han z).continuousAt).add continuousAt_const
  have heq : (fun w : ℂ => f (w + p)) =ᶠ[𝓝[≠] z] (fun w : ℂ => f w + c) := hq z
  exact Filter.EventuallyEq.eq_of_nhds
    ((hcont1.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE hcont2).mp heq)

/-! ### Rank-three punctured rigidity -/

/-- **Three rationally independent punctured quasi-periods force constancy.** -/
theorem meromorphicNF_constant_of_rankThree_puncturedConstIncrements
    (L : PeriodPair) (f : ℂ → ℂ) (hf : MeromorphicNFOn f Set.univ)
    (v : Fin 3 → ℂ) (hv : LinearIndependent ℚ v)
    (hinc : ∀ i, HasPuncturedConstIncrement f (v i))
    (hper : ∀ z, ∀ᶠ w in 𝓝[≠] z, f (w + L.ω₁) = f w)
    {k : ℂ} (hω : ∀ z, ∀ᶠ w in 𝓝[≠] z, f (w + L.ω₂) = f w + k) :
    ∀ x y, f x = f y := by
  obtain ⟨p, hp_mem, hp_ne, hp_zero⟩ := exists_small_rankThree_periods v hv
  have hq : ∀ n, HasPuncturedConstIncrement f (p n) := fun n =>
    hasPuncturedConstIncrement_of_mem_span hinc (p n) (hp_mem n)
  have han := analyticAt_of_small_puncturedConstIncrements f hf p hp_zero hp_ne hq
  have hperF : Function.Periodic f L.ω₁ := by
    intro z
    have h := constIncrement_of_punctured_of_analytic han (p := L.ω₁) (c := 0)
      (by intro z; filter_upwards [hper z] with w hw; rw [hw]; ring) z
    rw [h, add_zero]
  have hωF : ∀ z, f (z + L.ω₂) = f z + k :=
    constIncrement_of_punctured_of_analytic han hω
  exact const_of_periodic_of_constant_increment L (fun z => (han z).differentiableAt) hperF hωF

/-- **Punctured paired collapse.**  A meromorphic normal form with punctured period one and
punctured constant increments along two further rationally independent steps is constant, and both
increments vanish. -/
theorem const_of_unit_period_of_puncturedConstIncrements
    {σ τ : ℂ} (hτ : 0 < τ.im) (hv : LinearIndependent ℚ ![(1 : ℂ), σ, τ])
    {W : ℂ → ℂ} (hW : MeromorphicNFOn W Set.univ)
    (hper : ∀ z, ∀ᶠ w in 𝓝[≠] z, W (w + 1) = W w) {a b : ℂ}
    (hincσ : ∀ z, ∀ᶠ w in 𝓝[≠] z, W (w + σ) = W w + a)
    (hincτ : ∀ z, ∀ᶠ w in 𝓝[≠] z, W (w + τ) = W w + b) :
    (∀ x y, W x = W y) ∧ a = 0 ∧ b = 0 := by
  have hL : LinearIndependent ℝ ![(1 : ℂ), τ] := linearIndependent_one_im_pos hτ
  have hconst : ∀ x y, W x = W y := by
    refine meromorphicNF_constant_of_rankThree_puncturedConstIncrements ⟨1, τ, hL⟩ W hW
      ![1, σ, τ] hv ?_ hper hincτ
    intro i
    fin_cases i
    · refine ⟨0, fun z => ?_⟩
      show ∀ᶠ w in 𝓝[≠] z, W (w + 1) = W w + 0
      filter_upwards [hper z] with w hw
      rw [hw]
      ring
    · exact ⟨a, hincσ⟩
    · exact ⟨b, hincτ⟩
  refine ⟨hconst, ?_, ?_⟩
  · obtain ⟨w, hw⟩ := (hincσ 0).exists
    rw [hconst (w + σ) w] at hw
    linear_combination -hw
  · obtain ⟨w, hw⟩ := (hincτ 0).exists
    rw [hconst (w + τ) w] at hw
    linear_combination -hw

end GaloisForLFunctions.HTGeometry
