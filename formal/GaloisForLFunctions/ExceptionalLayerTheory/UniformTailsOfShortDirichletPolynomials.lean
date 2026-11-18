import GaloisForLFunctions.HeckeLFunctions.HeckeLFunctionsContinuePastTheLineReOne
import GaloisForLFunctions.RHTower.Sieve.PSeriesTailAboveCutoff
import Mathlib.NumberTheory.LSeries.Deriv
import Mathlib.Analysis.Complex.Liouville

/-!
# Uniform truncation of Dirichlet series with a summatory power bound

Abel summation bounds the normalized tail on any compact subregion of
absolute real-part gap from the summatory exponent. The factor at the
cutoff keeps the original summatory exponent in the bound.
-/

noncomputable section

open Finset Filter Topology Complex

namespace GaloisForLFunctions.ExceptionalLayerTheory

open HTGeometry.BoundedPartialSums HeckeLFunctions

/-- Finite Dirichlet series through the integer cutoff. -/
def shortDirichletPrefix (c : ℕ → ℂ) (N : ℕ) (s : ℂ) : ℂ :=
  ∑ n ∈ range (N+1), LSeries.term c s n

private theorem shortDirichletPrefix_abel {c : ℕ → ℂ} (hc : c 0 = 0) (s : ℂ) (N : ℕ) :
    shortDirichletPrefix c N s = powNeg s N * partialSum c (N+1) -
      ∑ i ∈ range N, incr s i * partialSum c (i+1) := by
  simp only [shortDirichletPrefix,term_eq_mul_powNeg_of_zero hc,sum_mul_powNeg_eq,Nat.add_sub_cancel]

/-- A quantitative tail bound valid on both sides of the line of absolute convergence. -/
theorem norm_growthCont_sub_shortDirichletPrefix {c : ℕ → ℂ} (hc : c 0 = 0)
    {θ K : ℝ} (hθ : 0 ≤ θ) (hK : 0 ≤ K)
    (hA : ∀ x : ℝ, 1 ≤ x → ‖∑ n ∈ Icc 1 ⌊x⌋₊, c n‖ ≤ K*x^θ)
    {s : ℂ} (hs : θ < s.re) {N : ℕ} (hN : 1 ≤ N) :
    ‖growthCont c θ s - shortDirichletPrefix c N s‖ ≤
      K * (2 + ‖s‖*((1+s.re-θ)/(s.re-θ))) * (N:ℝ)^(θ-s.re) := by
  let w := fun i => incr s i * partialSum c (i+1)
  have hpart {i : ℕ} (hi : 1 ≤ i) : ‖partialSum c (i+1)‖ ≤ K*(i:ℝ)^θ := by
    rw [partialSum,sum_range_succ_eq_sum_Icc hc]
    simpa only [Nat.floor_natCast] using hA i (by exact_mod_cast hi)
  have hend {i : ℕ} (hi : 1 ≤ i) :
      ‖powNeg s i * partialSum c (i+1)‖ ≤ K*(i:ℝ)^(θ-s.re) := by
    have hip : 0 < (i:ℝ) := by exact_mod_cast hi
    rw [norm_mul,norm_powNeg hi]
    calc
      _ ≤ (i:ℝ)^(-s.re) * (K*(i:ℝ)^θ) :=
        mul_le_mul_of_nonneg_left (hpart hi) (Real.rpow_nonneg hip.le _)
      _ = _ := by rw [mul_left_comm, ← Real.rpow_add hip]; congr 2; ring
  have hterm {i : ℕ} (hi : 1 ≤ i) : ‖w i‖ ≤ (K*‖s‖)*(i:ℝ)^(-(1+s.re-θ)) := by
    have hip : 0 < (i:ℝ) := by exact_mod_cast hi
    rw [show ‖w i‖ = ‖incr s i‖*‖partialSum c (i+1)‖ from norm_mul _ _]
    calc
      _ ≤ (‖s‖*(i:ℝ)^(-s.re-1)) * (K*(i:ℝ)^θ) :=
        mul_le_mul (norm_incr_le (hθ.trans_lt hs) hi) (hpart hi) (norm_nonneg _) (by positivity)
      _ = (K*‖s‖)*((i:ℝ)^(-s.re-1)*(i:ℝ)^θ) := by ring
      _ = _ := by rw [← Real.rpow_add hip]; congr 2; ring
  have htail (M : ℕ) : ‖∑ i ∈ Ico N M, w i‖ ≤
      (K*‖s‖)*(((1+s.re-θ)/(s.re-θ))*(N:ℝ)^(θ-s.re)) := by
    have hh := _root_.RHTower.Sieve.sum_rpow_neg_tail_le (c := 1+s.re-θ) (N := M)
      (by linarith only [hs]) hN
    rw [show 1+s.re-θ-1 = s.re-θ by ring, show 1-(1+s.re-θ) = θ-s.re by ring] at hh
    calc
      _ ≤ ∑ i ∈ Ico N M, ‖w i‖ := norm_sum_le _ _
      _ ≤ ∑ i ∈ Ico N M, (K*‖s‖)*(i:ℝ)^(-(1+s.re-θ)) :=
        sum_le_sum fun i hi => hterm (hN.trans (mem_Ico.mp hi).1)
      _ = (K*‖s‖)* ∑ i ∈ Ico N M, (i:ℝ)^(-(1+s.re-θ)) := (mul_sum ..).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left ((sum_le_sum_of_subset_of_nonneg
        (show Ico N M ⊆ Icc N M from fun i hi => mem_Icc.mpr ⟨(mem_Ico.mp hi).1,(mem_Ico.mp hi).2.le⟩)
        (fun i _ _ => Real.rpow_nonneg (Nat.cast_nonneg i) _)).trans hh) (mul_nonneg hK (norm_nonneg _))
  have ht : Tendsto (fun M => shortDirichletPrefix c M s) atTop (𝓝 (growthCont c θ s)) :=
    (tendsto_sum_term_growthCont hc hθ hA hs).comp (tendsto_add_atTop_nat 1)
  apply le_of_tendsto ((ht.sub_const (shortDirichletPrefix c N s)).norm)
  filter_upwards [eventually_ge_atTop N] with M hM
  have he : shortDirichletPrefix c M s - shortDirichletPrefix c N s =
      (powNeg s M * partialSum c (M+1) - powNeg s N * partialSum c (N+1)) - ∑ i ∈ Ico N M, w i := by
    rw [shortDirichletPrefix_abel hc,shortDirichletPrefix_abel hc]
    change _ - ∑ i ∈ range M, w i - (_ - ∑ i ∈ range N, w i) = _
    rw [← sum_range_add_sum_Ico w hM]
    ring
  rw [he]
  apply (norm_sub_le _ _).trans
  apply (add_le_add (norm_sub_le _ _) le_rfl).trans
  have hpow : (M:ℝ)^(θ-s.re) ≤ (N:ℝ)^(θ-s.re) :=
    Real.rpow_le_rpow_of_nonpos (by exact_mod_cast hN) (by exact_mod_cast hM) (sub_nonpos.mpr hs.le)
  have hMend := (hend (hN.trans hM)).trans (mul_le_mul_of_nonneg_left hpow hK)
  exact (add_le_add (add_le_add hMend (hend hN)) (htail M)).trans_eq (by ring)

/-- Uniform normalized tail for real cutoffs, including nonintegral dilations.
The constant depends on a lower real-part gap and an upper norm for the frequency. -/
theorem norm_scaled_growthCont_sub_shortDirichletPrefix {c : ℕ → ℂ} (hc : c 0 = 0)
    {θ K : ℝ} (hθ : 0 ≤ θ) (hK : 0 ≤ K)
    (hA : ∀ x : ℝ, 1 ≤ x → ‖∑ n ∈ Icc 1 ⌊x⌋₊, c n‖ ≤ K*x^θ)
    {δ R : ℝ} (hδ : 0 < δ) {s : ℂ} (hs : θ+δ ≤ s.re) (hR : ‖s‖ ≤ R)
    {x : ℝ} (hx : 1 ≤ x) :
    ‖(x:ℂ)^s * (growthCont c θ s - shortDirichletPrefix c ⌊x⌋₊ s)‖ ≤
      (2^R * K * (2+R*(1+1/δ))) * x^θ := by
  let N := ⌊x⌋₊
  have hN : 1 ≤ N := (Nat.one_le_floor_iff x).mpr hx
  have hn : (0:ℝ) < N := by exact_mod_cast hN
  have hnx : (N:ℝ) ≤ x := Nat.floor_le (zero_le_one.trans hx)
  have hx2 : x ≤ 2*(N:ℝ) := by
    have h1 : (1:ℝ) ≤ N := by exact_mod_cast hN
    linarith only [Nat.lt_floor_add_one x,h1]
  have hσ : θ < s.re := by linarith only [hs,hδ]
  have hσ0 := hθ.trans hσ.le
  have hd : δ ≤ s.re-θ := by linarith only [hs]
  have hgap : 0 < s.re-θ := sub_pos.mpr hσ
  have hrat0 : 0 ≤ (1+s.re-θ)/(s.re-θ) :=
    div_nonneg (by linarith only [hgap]) hgap.le
  have hrat : (1+s.re-θ)/(s.re-θ) ≤ 1+1/δ := by
    rw [show 1+s.re-θ=1+(s.re-θ) by ring,add_div,div_self (hδ.trans_le hd).ne',add_comm]
    exact add_le_add le_rfl (one_div_le_one_div_of_le hδ hd)
  let B := K*(2+R*(1+1/δ))
  have hR0 := (norm_nonneg s).trans hR
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hfactor : K*(2+‖s‖*((1+s.re-θ)/(s.re-θ))) ≤ B := by
    apply mul_le_mul_of_nonneg_left _ hK
    exact add_le_add le_rfl (mul_le_mul hR hrat hrat0 hR0)
  have htwo : (2:ℝ)^s.re ≤ 2^R := Real.rpow_le_rpow_of_exponent_le (by norm_num) (s.re_le_norm.trans hR)
  have hxpow : x^s.re ≤ 2^R*(N:ℝ)^s.re := by
    apply (Real.rpow_le_rpow (zero_le_one.trans hx) hx2 hσ0).trans
    rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hn.le]
    exact mul_le_mul_of_nonneg_right htwo (Real.rpow_nonneg hn.le _)
  rw [norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos (zero_lt_one.trans_le hx)]
  change x^s.re * ‖growthCont c θ s - shortDirichletPrefix c N s‖ ≤ _
  calc
    _ ≤ (2^R*(N:ℝ)^s.re) * (B*(N:ℝ)^(θ-s.re)) :=
      mul_le_mul hxpow ((norm_growthCont_sub_shortDirichletPrefix hc hθ hK hA hσ hN).trans
        (mul_le_mul_of_nonneg_right hfactor (Real.rpow_nonneg hn.le _))) (norm_nonneg _) (by positivity)
    _ = (2^R*B) * (N:ℝ)^θ := by
      calc
        _ = (2^R*B) * ((N:ℝ)^s.re * (N:ℝ)^(θ-s.re)) := by ring
        _ = _ := by rw [← Real.rpow_add hn, show s.re + (θ-s.re) = θ by ring]
    _ ≤ _ := by
      rw [mul_assoc (2^R) K]
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hn.le hnx hθ) (mul_nonneg (by positivity) hB)

/-- Each finite prefix is an entire function of the frequency. -/
theorem differentiable_shortDirichletPrefix (c : ℕ → ℂ) (N : ℕ) :
    Differentiable ℂ (shortDirichletPrefix c N) := by
  intro s
  exact DifferentiableAt.fun_sum fun n _ => (LSeries.hasDerivAt_term c n s).differentiableAt

/-- On a fixed disk, every derivative of the normalized remainder has the same power
bound, also after multiplication by an entire test bounded on the boundary circle. -/
theorem exists_bound_tested_dirichlet_tail_deriv {c : ℕ → ℂ} (hc : c 0 = 0)
    {θ K : ℝ} (hθ : 0 ≤ θ) (hK : 0 ≤ K)
    (hA : ∀ x : ℝ, 1 ≤ x → ‖∑ n ∈ Icc 1 ⌊x⌋₊, c n‖ ≤ K*x^θ)
    {ρ : ℂ} {r : ℝ} (hr : 0 < r) (hgap : θ+r < ρ.re) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : ℂ → ℂ), Differentiable ℂ f →
      ∀ (M : ℝ), 0 ≤ M → (∀ s ∈ Metric.sphere ρ r, ‖f s‖ ≤ M) → ∀ x : ℝ, 1 ≤ x →
      ‖iteratedDeriv k (fun s => f s * ((x:ℂ)^s *
        (growthCont c θ s - shortDirichletPrefix c ⌊x⌋₊ s))) ρ‖ ≤ C*M*x^θ := by
  let R := ‖ρ‖+r
  let δ := ρ.re-r-θ
  have hδ : 0 < δ := by dsimp only [δ]; linarith only [hgap]
  let B := 2^R * K * (2+R*(1+1/δ))
  have hR : 0 ≤ R := add_nonneg (norm_nonneg _) hr.le
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  refine ⟨(k.factorial:ℝ)*B/r^k,by positivity, fun f hf M hM hbound x hx => ?_⟩
  have hdisk {s : ℂ} (hs : s ∈ Metric.closedBall ρ r) : θ+δ ≤ s.re ∧ ‖s‖ ≤ R := by
    have hd : ‖s-ρ‖ ≤ r := by simpa only [Metric.mem_closedBall,dist_eq_norm] using hs
    have hre := (ρ-s).re_le_norm
    rw [sub_re,norm_sub_rev] at hre
    exact ⟨by dsimp only [δ]; linarith only [hre,hd], (norm_le_norm_add_norm_sub' s ρ).trans
      (add_le_add le_rfl hd)⟩
  let T := fun s : ℂ => f s * ((x:ℂ)^s * (growthCont c θ s - shortDirichletPrefix c ⌊x⌋₊ s))
  have hx0 : (x:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (zero_lt_one.trans_le hx).ne'
  have hpow : Differentiable ℂ (fun s : ℂ => (x:ℂ)^s) := differentiable_id.const_cpow (Or.inl hx0)
  have hcont := differentiableOn_growthCont hc hθ hA
  have hdT : DifferentiableOn ℂ T (Metric.closedBall ρ r) := by
    apply hf.differentiableOn.mul (hpow.differentiableOn.mul _)
    apply (hcont.mono _).sub (differentiable_shortDirichletPrefix _ _).differentiableOn
    exact fun s hs => lt_of_lt_of_le (lt_add_of_pos_right θ hδ) (hdisk hs).1
  have hcl : DiffContOnCl ℂ T (Metric.ball ρ r) := by
    refine ⟨hdT.mono Metric.ball_subset_closedBall,?_⟩
    rw [closure_ball _ hr.ne']
    exact hdT.continuousOn
  have hb (s : ℂ) (hs : s ∈ Metric.sphere ρ r) : ‖T s‖ ≤ M*(B*x^θ) := by
    have hp := hdisk (Metric.sphere_subset_closedBall hs)
    rw [show ‖T s‖ = ‖f s‖ * ‖(x:ℂ)^s * (growthCont c θ s - shortDirichletPrefix c ⌊x⌋₊ s)‖
      from norm_mul _ _]
    exact mul_le_mul (hbound s hs) (norm_scaled_growthCont_sub_shortDirichletPrefix hc hθ hK hA
      hδ hp.1 hp.2 hx) (norm_nonneg _) hM
  exact (Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le k hr hcl hb).trans_eq (by ring)

#print axioms exists_bound_tested_dirichlet_tail_deriv
#print axioms norm_growthCont_sub_shortDirichletPrefix
#print axioms norm_scaled_growthCont_sub_shortDirichletPrefix

end GaloisForLFunctions.ExceptionalLayerTheory
