import GaloisForLFunctions.HTGeometry.AbelianZetaGas.DepthTail

/-!
# The divisor of the grand response

The grand response is the product over all depths of the pulled-back zeta factors.  Splitting it at
the uniform depth threshold gives a finite product, whose divisor is the finite sum of pulled-back
zeta orders, times a tail that is holomorphic and zero-free.  The divisor of the response is
therefore that finite sum: this is (GAS.9).

The splitting lemma is stated for an arbitrary multipliable family in a commutative monoid, since
mathlib's `Multipliable.prod_mul_tprod_nat_add` needs a commutative *group* and `ℂ` is not one under
multiplication.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Topology

set_option maxHeartbeats 1000000

noncomputable section

/-- `ℕ` enumerates the naturals beyond `J`. -/
def natComplRangeEquiv (J : ℕ) : ℕ ≃ ((↑(Finset.range J) : Set ℕ)ᶜ : Set ℕ) where
  toFun n := ⟨n + J, by simp⟩
  invFun x := (x : ℕ) - J
  left_inv n := by simp
  right_inv x := by
    refine Subtype.ext ?_
    have hx : J ≤ (x : ℕ) := by
      have hmem := x.2
      simp only [Finset.coe_range, Set.mem_compl_iff, Set.mem_Iio, not_lt] at hmem
      exact hmem
    show (x : ℕ) - J + J = (x : ℕ)
    omega

/-- **Splitting a multipliable family at a finite depth**, in a commutative monoid. -/
theorem tprod_split_nat {M : Type*} [CommMonoid M] [TopologicalSpace M] [T2Space M]
    [ContinuousMul M] {f : ℕ → M} (hf : Multipliable f) (J : ℕ)
    (hshift : Multipliable fun n : ℕ => f (n + J)) :
    ∏' n : ℕ, f n = (∏ n ∈ Finset.range J, f n) * ∏' n : ℕ, f (n + J) := by
  classical
  have hhead : HasProd (f ∘ (Subtype.val : (↑(Finset.range J) : Set ℕ) → ℕ))
      (∏ n ∈ Finset.range J, f n) := by
    have h := hasProd_fintype (f ∘ (Subtype.val : (↑(Finset.range J) : Set ℕ) → ℕ))
    have hval : (∏ i : (↑(Finset.range J) : Set ℕ),
        (f ∘ (Subtype.val : (↑(Finset.range J) : Set ℕ) → ℕ)) i)
        = ∏ n ∈ Finset.range J, f n := by
      simp only [Function.comp_apply]
      exact Finset.prod_attach _ _
    rwa [hval] at h
  have htail : HasProd (f ∘ (Subtype.val : ((↑(Finset.range J) : Set ℕ)ᶜ : Set ℕ) → ℕ))
      (∏' n : ℕ, f (n + J)) := by
    refine ((natComplRangeEquiv J).hasProd_iff).mp ?_
    exact hshift.hasProd
  exact (hf.hasProd.unique (hhead.mul_compl htail))

/-! ## The grand response -/

theorem depthFactor_eq_zeta_depthArg (σ : ℝ) (v : ℂ) (j : ℕ) (u : ℂ) :
    depthFactor σ v j u = riemannZeta (depthArg σ v j u) := rfl

/-- The grand response in the dilation variable: the product over all depths. -/
def grandResponse (σ : ℝ) (v : ℂ) (u : ℂ) : ℂ :=
  ∏' j : ℕ, depthFactor σ v (j + 1) u

theorem multipliable_depthFactor_shift (σ : ℝ) (v : ℂ) {u : ℂ} (ha : 0 < σ + u.re) (k : ℕ) :
    Multipliable fun j : ℕ => depthFactor σ v (j + k) u := by
  have hsum : Summable fun j : ℕ => ‖riemannZeta (depthArg σ v (j + k) u) - 1‖ :=
    (summable_nat_add_iff k).mpr (summable_norm_zeta_depth_sub_one σ v u ha)
  have hmul := Complex.multipliable_one_add_of_summable
    (f := fun j : ℕ => riemannZeta (depthArg σ v (j + k) u) - 1) hsum.of_norm
  refine hmul.congr fun j => ?_
  rw [depthFactor_eq_zeta_depthArg]
  ring

theorem multipliable_depthFactor_succ (σ : ℝ) (v : ℂ) {u : ℂ} (ha : 0 < σ + u.re) :
    Multipliable fun j : ℕ => depthFactor σ v (j + 1) u :=
  multipliable_depthFactor_shift σ v ha 1

/-- The grand response splits at any depth into the truncation and the tail. -/
theorem grandResponse_split (σ : ℝ) (v : ℂ) {u : ℂ} (ha : 0 < σ + u.re) (J : ℕ) :
    grandResponse σ v u
      = depthProduct σ v J u * ∏' j : ℕ, depthFactor σ v (j + J + 1) u := by
  have hshift : Multipliable fun n : ℕ => depthFactor σ v (n + J + 1) u := by
    have h := multipliable_depthFactor_shift σ v ha (J + 1)
    refine h.congr fun n => ?_
    have hidx : n + (J + 1) = n + J + 1 := by omega
    rw [hidx]
  have hsplit := tprod_split_nat (multipliable_depthFactor_succ σ v ha) J hshift
  rw [grandResponse, hsplit]
  rfl

/-! ## The divisor of the grand response -/

theorem tprod_depthFactor_tail_ne_zero (σ : ℝ) (v : ℂ) {a₀ : ℝ} (ha₀ : 0 < a₀) {u : ℂ}
    (hu : a₀ ≤ σ + u.re) {J : ℕ} (hJthr : depthTailThreshold v a₀ ≤ J) :
    (∏' j : ℕ, depthFactor σ v (j + J) u) ≠ 0 := by
  have ha : 0 < σ + u.re := lt_of_lt_of_le ha₀ hu
  have hsum : Summable fun j : ℕ => ‖riemannZeta (depthArg σ v (j + J) u) - 1‖ :=
    (summable_nat_add_iff J).mpr (summable_norm_zeta_depth_sub_one σ v u ha)
  have hval : (∏' j : ℕ, depthFactor σ v (j + J) u)
      = ∏' j : ℕ, (1 + (riemannZeta (depthArg σ v (j + J) u) - 1)) := by
    refine tprod_congr fun j => ?_
    rw [depthFactor_eq_zeta_depthArg]
    ring
  rw [hval]
  refine tprod_one_add_ne_zero_of_summable ?_ hsum
  intro j
  have hre : 2 ≤ (depthArg σ v (j + J) u).re :=
    two_le_re_depthArg_of_ge σ v ha₀ hu (le_trans hJthr (Nat.le_add_left J j))
  have hne : riemannZeta (depthArg σ v (j + J) u) ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re (by linarith)
  intro h0
  apply hne
  have hid : (1 : ℂ) + (riemannZeta (depthArg σ v (j + J) u) - 1)
      = riemannZeta (depthArg σ v (j + J) u) := by ring
  rw [hid] at h0
  exact h0

theorem analyticAt_tprod_depthFactor_tail (σ : ℝ) (v : ℂ) {a₀ : ℝ} (ha₀ : 0 < a₀) {u : ℂ}
    (hu : a₀ < σ + u.re) {J : ℕ} (hJthr : depthTailThreshold v a₀ ≤ J) :
    AnalyticAt ℂ (fun w : ℂ => ∏' j : ℕ, depthFactor σ v (j + J) w) u := by
  have hopen : IsOpen {w : ℂ | a₀ < σ + w.re} := by
    have hcont : Continuous fun w : ℂ => σ + w.re := continuous_const.add Complex.continuous_re
    exact isOpen_lt continuous_const hcont
  have hdiff := differentiableOn_tprod_zeta_depthTail σ v ha₀ hJthr
  have hmem : u ∈ {w : ℂ | a₀ < σ + w.re} := hu
  exact (hdiff.analyticOnNhd hopen) u hmem

/-- The grand response is meromorphic throughout every positive dilation chamber. -/
theorem meromorphicAt_grandResponse (σ : ℝ) (v : ℂ) {a₀ : ℝ} (ha₀ : 0 < a₀) {u : ℂ}
    (hu : a₀ < σ + u.re) : MeromorphicAt (grandResponse σ v) u := by
  let J := depthTailThreshold v a₀
  have hopen : IsOpen {w : ℂ | a₀ < σ + w.re} := by
    have hcont : Continuous fun w : ℂ => σ + w.re := continuous_const.add Complex.continuous_re
    exact isOpen_lt continuous_const hcont
  have heq : grandResponse σ v
      =ᶠ[nhdsWithin u {u}ᶜ]
        fun w : ℂ => depthProduct σ v J w * ∏' j : ℕ, depthFactor σ v (j + J + 1) w := by
    filter_upwards [nhdsWithin_le_nhds (hopen.mem_nhds hu)] with w hw
    exact grandResponse_split σ v (lt_of_lt_of_le ha₀ (le_of_lt hw)) J
  have hhead : MeromorphicAt (depthProduct σ v J) u := by
    show MeromorphicAt (fun w : ℂ => ∏ j ∈ Finset.range J, depthFactor σ v (j + 1) w) u
    exact MeromorphicAt.fun_prod fun j _ =>
      meromorphicAt_depthFactor σ v (Nat.succ_le_succ (Nat.zero_le j)) u
  have hJ1 : depthTailThreshold v a₀ ≤ J + 1 := Nat.le_succ _
  have htailfun : (fun w : ℂ => ∏' j : ℕ, depthFactor σ v (j + J + 1) w)
      = fun w : ℂ => ∏' j : ℕ, depthFactor σ v (j + (J + 1)) w := by
    funext w
    refine tprod_congr fun j => ?_
    have hidx : j + J + 1 = j + (J + 1) := by omega
    rw [hidx]
  have htail : MeromorphicAt
      (fun w : ℂ => ∏' j : ℕ, depthFactor σ v (j + J + 1) w) u := by
    rw [htailfun]
    exact (analyticAt_tprod_depthFactor_tail σ v ha₀ hu hJ1).meromorphicAt
  exact (hhead.fun_mul htail).congr heq.symm

/-- **(GAS.9), full form.**  On the chamber the divisor of the grand response is the finite sum of
the pulled-back zeta orders at the depths below the threshold. -/
theorem meromorphicOrderAt_grandResponse (σ : ℝ) (v : ℂ) {a₀ : ℝ} (ha₀ : 0 < a₀) {u : ℂ}
    (hu : a₀ < σ + u.re) {J : ℕ} (hJthr : depthTailThreshold v a₀ ≤ J) :
    meromorphicOrderAt (grandResponse σ v) u
      = ∑ j ∈ Finset.range J,
        meromorphicOrderAt riemannZeta (((j + 1 : ℕ) : ℂ) * ((σ : ℝ) + u) + v) := by
  have hopen : IsOpen {w : ℂ | a₀ < σ + w.re} := by
    have hcont : Continuous fun w : ℂ => σ + w.re := continuous_const.add Complex.continuous_re
    exact isOpen_lt continuous_const hcont
  have hJ1 : depthTailThreshold v a₀ ≤ J + 1 := le_trans hJthr (Nat.le_succ J)
  -- the response agrees with the split near `u`
  have heq : grandResponse σ v
      =ᶠ[nhdsWithin u {u}ᶜ]
        fun w : ℂ => depthProduct σ v J w * ∏' j : ℕ, depthFactor σ v (j + J + 1) w := by
    filter_upwards [nhdsWithin_le_nhds (hopen.mem_nhds hu)] with w hw
    exact grandResponse_split σ v (lt_of_lt_of_le ha₀ (le_of_lt hw)) J
  rw [meromorphicOrderAt_congr heq]
  -- the tail has order zero
  have htailfun : (fun w : ℂ => ∏' j : ℕ, depthFactor σ v (j + J + 1) w)
      = fun w : ℂ => ∏' j : ℕ, depthFactor σ v (j + (J + 1)) w := by
    funext w
    refine tprod_congr fun j => ?_
    have hidx : j + J + 1 = j + (J + 1) := by omega
    rw [hidx]
  have htail0 : meromorphicOrderAt
      (fun w : ℂ => ∏' j : ℕ, depthFactor σ v (j + J + 1) w) u = 0 := by
    rw [htailfun]
    exact meromorphicOrderAt_eq_zero_of_analytic
      (analyticAt_tprod_depthFactor_tail σ v ha₀ hu hJ1)
      (tprod_depthFactor_tail_ne_zero σ v ha₀ (le_of_lt hu) hJ1)
  have hmerA : MeromorphicAt (depthProduct σ v J) u := by
    show MeromorphicAt (fun w : ℂ => ∏ j ∈ Finset.range J, depthFactor σ v (j + 1) w) u
    exact MeromorphicAt.fun_prod fun j _ =>
      meromorphicAt_depthFactor σ v (Nat.succ_le_succ (Nat.zero_le j)) u
  have hmerB : MeromorphicAt (fun w : ℂ => ∏' j : ℕ, depthFactor σ v (j + J + 1) w) u := by
    rw [htailfun]
    exact (analyticAt_tprod_depthFactor_tail σ v ha₀ hu hJ1).meromorphicAt
  have hsplit : (fun w : ℂ =>
      depthProduct σ v J w * ∏' j : ℕ, depthFactor σ v (j + J + 1) w)
      = depthProduct σ v J * fun w : ℂ => ∏' j : ℕ, depthFactor σ v (j + J + 1) w := rfl
  rw [hsplit, meromorphicOrderAt_mul hmerA hmerB, htail0, add_zero,
    meromorphicOrderAt_depthProduct σ v J u]

end

end GaloisForLFunctions.HTGeometry
