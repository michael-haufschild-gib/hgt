import GaloisForLFunctions.HTGeometry.PairedQuasiEllipticRigidity
import GaloisForLFunctions.HTGeometry.RankThreePeriods

/-!
# Quasi-periods have no poles

A translation step along which a meromorphic function changes by a constant preserves the order of
every pole, because adding an analytic function cannot change a negative order.  A rank-three group
of such steps therefore moves any pole by arbitrarily small amounts, contradicting the isolation of
poles.  Hence a meromorphic normal form with three rationally independent quasi-period steps is
entire, and the two-period rigidity of `PairedQuasiEllipticRigidity` makes it constant.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

/-- A step along which the function changes by a constant. -/
def HasConstIncrement (W : ℂ → ℂ) (p : ℂ) : Prop :=
  ∃ c : ℂ, ∀ z, W (z + p) = W z + c

theorem hasConstIncrement_zero (W : ℂ → ℂ) : HasConstIncrement W 0 :=
  ⟨0, fun z => by simp⟩

theorem HasConstIncrement.add {W : ℂ → ℂ} {x y : ℂ}
    (hx : HasConstIncrement W x) (hy : HasConstIncrement W y) :
    HasConstIncrement W (x + y) := by
  obtain ⟨cx, hcx⟩ := hx
  obtain ⟨cy, hcy⟩ := hy
  refine ⟨cx + cy, fun z => ?_⟩
  have hassoc : z + (x + y) = z + x + y := by ring
  rw [hassoc, hcy, hcx]
  ring

theorem HasConstIncrement.neg {W : ℂ → ℂ} {x : ℂ} (hx : HasConstIncrement W x) :
    HasConstIncrement W (-x) := by
  obtain ⟨cx, hcx⟩ := hx
  refine ⟨-cx, fun z => ?_⟩
  have h := hcx (z + -x)
  have hsimp : z + -x + x = z := by ring
  rw [hsimp] at h
  linear_combination -h

theorem HasConstIncrement.zsmul {W : ℂ → ℂ} {x : ℂ} (hx : HasConstIncrement W x) (a : ℤ) :
    HasConstIncrement W (a • x) := by
  induction a using Int.induction_on with
  | zero => simpa using hasConstIncrement_zero W
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

theorem hasConstIncrement_of_mem_span {W : ℂ → ℂ} {ι : Type*} {v : ι → ℂ}
    (h : ∀ i, HasConstIncrement W (v i)) :
    ∀ p ∈ Submodule.span ℤ (Set.range v), HasConstIncrement W p := by
  intro p hp
  induction hp using Submodule.span_induction with
  | mem x hx => obtain ⟨i, rfl⟩ := hx; exact h i
  | zero => exact hasConstIncrement_zero W
  | add x y _ _ hx hy => exact hx.add hy
  | smul a x _ hx => exact hx.zsmul a

/-! ### A constant increment preserves pole orders -/

theorem meromorphicOrderAt_add_constIncrement (f : ℂ → ℂ) {p c : ℂ} (z : ℂ)
    (hq : ∀ w, f (w + p) = f w + c)
    (hneg : meromorphicOrderAt f z < 0) :
    meromorphicOrderAt f (z + p) = meromorphicOrderAt f z := by
  have hg : AnalyticAt ℂ (fun w : ℂ => w + p) z := by fun_prop
  have hgd : deriv (fun w : ℂ => w + p) z ≠ 0 := by simp
  have hcomp := meromorphicOrderAt_comp_of_deriv_ne_zero (f := f) hg hgd
  have hfg : (f ∘ fun w : ℂ => w + p) = f + fun _ : ℂ => c := by
    funext w
    simp only [Function.comp_apply, Pi.add_apply]
    exact hq w
  rw [hfg] at hcomp
  have hconst : MeromorphicAt (fun _ : ℂ => c) z := (analyticAt_const).meromorphicAt
  have hordc : 0 ≤ meromorphicOrderAt (fun _ : ℂ => c) z :=
    (analyticAt_const (v := c)).meromorphicOrderAt_nonneg
  have hlt : meromorphicOrderAt f z < meromorphicOrderAt (fun _ : ℂ => c) z :=
    lt_of_lt_of_le hneg hordc
  have hsum := meromorphicOrderAt_add_eq_left_of_lt hconst hlt
  rw [← hcomp]
  exact hsum

/-! ### Small quasi-periods force analyticity -/

theorem analyticAt_of_small_constIncrements (f : ℂ → ℂ) (hf : MeromorphicNFOn f Set.univ)
    (p : ℕ → ℂ) (hp0 : Tendsto p atTop (𝓝 0)) (hpne : ∀ n, p n ≠ 0)
    (hq : ∀ n, HasConstIncrement f (p n)) : ∀ z, AnalyticAt ℂ f z := by
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
  rw [meromorphicOrderAt_add_constIncrement f z hc hneg] at hnonneg_n
  exact (not_le_of_gt hneg) hnonneg_n

/-! ### Rank-three quasi-period rigidity -/

/-- **Three rationally independent quasi-periods force constancy.**  A meromorphic normal form
with a constant increment along each of three rationally independent steps, one of which is an
exact period whose partner is `ℝ`-independent from it, is constant. -/
theorem meromorphicNF_constant_of_rankThree_constIncrements
    (L : PeriodPair) (f : ℂ → ℂ) (hf : MeromorphicNFOn f Set.univ)
    (v : Fin 3 → ℂ) (hv : LinearIndependent ℚ v)
    (hinc : ∀ i, HasConstIncrement f (v i))
    (hper : Function.Periodic f L.ω₁) {k : ℂ}
    (hω : ∀ z, f (z + L.ω₂) = f z + k) :
    ∀ x y, f x = f y := by
  obtain ⟨p, hp_mem, hp_ne, hp_zero⟩ := exists_small_rankThree_periods v hv
  have hq : ∀ n, HasConstIncrement f (p n) := fun n =>
    hasConstIncrement_of_mem_span hinc (p n) (hp_mem n)
  have han := analyticAt_of_small_constIncrements f hf p hp_zero hp_ne hq
  exact const_of_periodic_of_constant_increment L (fun z => (han z).differentiableAt) hper hω

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

theorem linearIndependent_one_im_pos {τ : ℂ} (hτ : 0 < τ.im) :
    LinearIndependent ℝ ![(1 : ℂ), τ] := by
  rw [LinearIndependent.pair_iff']
  · intro s hs
    have him := congrArg Complex.im hs
    simp only [Complex.real_smul, mul_one, Complex.ofReal_im] at him
    exact absurd him.symm (ne_of_gt hτ)
  · exact one_ne_zero

/-- **Paired quasi-elliptic collapse.**  A meromorphic normal form with period one and constant
increments along two further rationally independent steps is constant, and both increments
vanish. -/
theorem const_of_unit_period_of_constIncrements
    {σ τ : ℂ} (hτ : 0 < τ.im) (hv : LinearIndependent ℚ ![(1 : ℂ), σ, τ])
    {W : ℂ → ℂ} (hW : MeromorphicNFOn W Set.univ)
    (hper : Function.Periodic W 1) {a b : ℂ}
    (hincσ : ∀ z, W (z + σ) = W z + a) (hincτ : ∀ z, W (z + τ) = W z + b) :
    (∀ x y, W x = W y) ∧ a = 0 ∧ b = 0 := by
  have hL : LinearIndependent ℝ ![(1 : ℂ), τ] := linearIndependent_one_im_pos hτ
  have hconst : ∀ x y, W x = W y := by
    refine meromorphicNF_constant_of_rankThree_constIncrements ⟨1, τ, hL⟩ W hW
      ![1, σ, τ] hv ?_ hper hincτ
    intro i
    fin_cases i
    · refine ⟨0, fun z => ?_⟩
      show W (z + 1) = W z + 0
      rw [hper z]
      ring
    · exact ⟨a, hincσ⟩
    · exact ⟨b, hincτ⟩
  refine ⟨hconst, ?_, ?_⟩
  · have h := hincσ 0
    rw [hconst (0 + σ) 0] at h
    linear_combination -h
  · have h := hincτ 0
    rw [hconst (0 + τ) 0] at h
    linear_combination -h

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

/-- **Pole-free two-step rigidity.**  A meromorphic normal form whose orders are everywhere
nonnegative, with period one and a constant increment along a step of positive imaginary part, is
constant and that increment vanishes.  This is the one-pole classification step: matching principal
parts make the difference of two quasi-elliptic increments pole-free, hence constant. -/
theorem const_of_nonneg_order_of_unit_period
    {τ : ℂ} (hτ : 0 < τ.im) {f : ℂ → ℂ} (hf : MeromorphicNFOn f Set.univ)
    (hord : ∀ z, 0 ≤ meromorphicOrderAt f z)
    (hper : Function.Periodic f 1) {k : ℂ} (hinc : ∀ z, f (z + τ) = f z + k) :
    (∀ x y, f x = f y) ∧ k = 0 := by
  have han : ∀ z, AnalyticAt ℂ f z := fun z =>
    (hf (Set.mem_univ z)).meromorphicOrderAt_nonneg_iff_analyticAt.mp (hord z)
  have hconst := const_of_periodic_of_constant_increment
    ⟨1, τ, linearIndependent_one_im_pos hτ⟩ (fun z => (han z).differentiableAt) hper hinc
  refine ⟨hconst, ?_⟩
  have h := hinc 0
  rw [hconst (0 + τ) 0] at h
  linear_combination -h

end GaloisForLFunctions.HTGeometry
