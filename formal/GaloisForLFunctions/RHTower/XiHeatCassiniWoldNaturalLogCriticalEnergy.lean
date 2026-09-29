import GaloisForLFunctions.RHTower.XiHeatCassiniWoldNaturalSquareEnergyEndpoint
/-!
# Logarithmic critical-energy exclusion for the natural Wold source

The normalized radial dual has squared norm at most `(1+x)^2`.  Consequently every
logarithmically weighted square-summable residual has zero scaled critical-wall residue:
its finite head vanishes and its square-energy tail controls the remaining current.

The natural Wold source has a nonzero quantized wall residue unconditionally.  Thus dividing
its critical energy by `1+log N` cannot produce a summable source norm.
-/

open Complex Filter Set Topology
open scoped BigOperators
namespace RHTower.WoldNaturalAbelLogHilbert
noncomputable section
open WoldNaturalAbelHilbert

def logWeight (n : ℕ) : ℝ := 1+Real.log ((n:ℝ)+1)

lemma logWeight_pos (n : ℕ) : 0 < logWeight n := by
  have h := Real.log_nonneg (show 1 ≤ (n:ℝ)+1 by linarith [show (0:ℝ) ≤ (n:ℝ) from Nat.cast_nonneg n])
  dsimp [logWeight]
  linarith

lemma logWeight_le {x : ℝ} (hx : 0 < x) (n : ℕ) :
    logWeight n ≤ (1+1/x)*((n:ℝ)+1)^x := by
  have hlog := Real.log_le_rpow_div (show 0 ≤ (n:ℝ)+1 by positivity) hx
  have hpow : 1 ≤ ((n:ℝ)+1)^x := by
    simpa using Real.rpow_le_rpow_of_exponent_le
      (show 1 ≤ (n:ℝ)+1 by linarith [show (0:ℝ) ≤ (n:ℝ) from Nat.cast_nonneg n]) hx.le
  dsimp [logWeight]
  calc
    _ ≤ ((n:ℝ)+1)^x + ((n:ℝ)+1)^x/x := add_le_add hpow hlog
    _ = _ := by ring

lemma log_dual_summable {q : ℝ} (hq : q < -1/2) :
    Summable (fun n : ℕ => (Real.sqrt (logWeight n)*((n:ℝ)+1)^q)^2) := by
  let e : ℝ := -q-1/2
  have he : 0 < e := by dsimp [e]; linarith
  have hp : Summable (fun n : ℕ => ((n:ℝ)+1)^(2*q+e)) := by
    have hh : Summable (fun n : ℕ => (n:ℝ)^(2*q+e)) :=
      Real.summable_nat_rpow.mpr (by dsimp [e]; linarith)
    simpa only [Nat.cast_add, Nat.cast_one] using (summable_nat_add_iff 1).mpr hh
  refine Summable.of_nonneg_of_le (fun n => sq_nonneg _) (fun n => ?_) (hp.mul_left (1+1/e))
  rw [mul_pow, Real.sq_sqrt (logWeight_pos n).le,
    ← Real.rpow_natCast, ← Real.rpow_mul (show 0 ≤ (n:ℝ)+1 by positivity)]
  calc
    _ ≤ ((1+1/e)*((n:ℝ)+1)^e) * ((n:ℝ)+1)^(q*2) :=
      mul_le_mul_of_nonneg_right (logWeight_le he n) (by positivity)
    _ = _ := by
      rw [mul_assoc, ← Real.rpow_add (show 0 < (n:ℝ)+1 by positivity)]
      congr 2
      ring

lemma log_weighted_summable {r : ℕ → ℝ}
    (hr : Summable (fun n => (r n)^2/logWeight n)) {q : ℝ} (hq : q < -1/2) :
    Summable (fun n => |r n| *((n:ℝ)+1)^q) := by
  have hA : Summable (fun n => (|r n|/Real.sqrt (logWeight n))^2) := by
    simpa only [div_pow, sq_abs, Real.sq_sqrt (logWeight_pos _).le] using hr
  have hB := log_dual_summable hq
  have hprod : Summable (fun n => (|r n|/Real.sqrt (logWeight n))*
      (Real.sqrt (logWeight n)*((n:ℝ)+1)^q)) :=
    Summable.of_nonneg_of_le (fun n => by positivity) (fun n => by
      nlinarith [sq_nonneg (|r n|/Real.sqrt (logWeight n)-
        Real.sqrt (logWeight n)*((n:ℝ)+1)^q)]) ((hA.add hB).div_const 2)
  refine hprod.congr fun n => ?_
  field_simp [ne_of_gt (Real.sqrt_pos.mpr (logWeight_pos n))]

lemma family_l2_zero {α : Type*} {l : Filter α} {f : α → ℕ → ℂ}
    {a : ℕ → ℝ} {b : α → ℕ → ℝ} (ha : Summable (fun n => (a n)^2))
    (ha0 : ∀ n, 0 ≤ a n) {K : ℝ} (hK : 0 ≤ K)
    (hcoord : ∀ n, Tendsto (fun x => f x n) l (𝓝 0))
    (hhyp : ∀ᶠ x in l, Summable (f x) ∧ Summable (fun n => (b x n)^2) ∧
      (∀ n, 0 ≤ b x n) ∧ (∀ n, ‖f x n‖ ≤ a n*b x n) ∧
      (∑' n, (b x n)^2) ≤ K^2) :
    Tendsto (fun x => ∑' n, f x n) l (𝓝 0) := by
  apply Metric.tendsto_nhds.2
  intro ε hε
  have htail : Tendsto (fun N : ℕ => Real.sqrt (∑' n, (a (n+N))^2)*K)
      atTop (𝓝 0) := by
    simpa using ((Real.continuous_sqrt.tendsto 0).comp
      (tendsto_sum_nat_add (fun n => (a n)^2))).mul_const K
  obtain ⟨N, hN⟩ := ((tendsto_order.1 htail).2 (ε/2) (by linarith)).exists
  have hhead : Tendsto (fun x => ∑ n ∈ Finset.range N, f x n) l (𝓝 0) := by
    simpa using tendsto_finsetSum (Finset.range N) (fun n _ => hcoord n)
  have hheadSmall : ∀ᶠ x in l, ‖∑ n ∈ Finset.range N, f x n‖ < ε/2 :=
    (tendsto_order.1 (by simpa using hhead.norm)).2 (ε/2) (by linarith)
  filter_upwards [hhyp, hheadSmall] with x hx hh
  obtain ⟨hf, hb, hb0, hbound, hB⟩ := hx
  have haN := ha.comp_injective (add_left_injective N)
  have hbN := hb.comp_injective (add_left_injective N)
  have habN : Summable (fun n => a (n+N)*b x (n+N)) :=
    Summable.of_nonneg_of_le (fun n => mul_nonneg (ha0 _) (hb0 _))
      (fun n => by dsimp only [Function.comp_def]; nlinarith [sq_nonneg (a (n+N)-b x (n+N))])
      ((haN.add hbN).div_const 2)
  have hBN : (∑' n, (b x (n+N))^2) ≤ K^2 := by
    have hs := hb.sum_add_tsum_nat_add N
    have hnon : 0 ≤ ∑ n ∈ Finset.range N, (b x n)^2 := Finset.sum_nonneg (fun n _ => sq_nonneg _)
    linarith
  have hsqrt : Real.sqrt (∑' n, (b x (n+N))^2) ≤ K := by
    simpa [Real.sqrt_sq hK] using Real.sqrt_le_sqrt hBN
  have hfN := hf.comp_injective (add_left_injective N)
  have ht : ‖∑' n, f x (n+N)‖ ≤ Real.sqrt (∑' n, (a (n+N))^2)*K := by
    calc
      _ ≤ ∑' n, ‖f x (n+N)‖ := norm_tsum_le_tsum_norm hfN.norm
      _ ≤ ∑' n, a (n+N)*b x (n+N) :=
        hfN.norm.tsum_le_tsum (fun n => hbound (n+N)) habN
      _ ≤ Real.sqrt (∑' n, (a (n+N))^2)*Real.sqrt (∑' n, (b x (n+N))^2) :=
        tsum_mul_le haN hbN (fun n => ha0 _) (fun n => hb0 _)
      _ ≤ _ := mul_le_mul_of_nonneg_left hsqrt (Real.sqrt_nonneg _)
  rw [← hf.sum_add_tsum_nat_add N, dist_zero_right]
  exact (norm_add_le _ _).trans_lt (by linarith)

def radialDual (x : ℝ) (n : ℕ) : ℝ :=
  x*Real.sqrt (logWeight n)*((n:ℝ)+1)^(-1/2-x)

lemma radialDual_summable {x : ℝ} (hx : 0 < x) :
    Summable (fun n => (radialDual x n)^2) := by
  have h := (log_dual_summable (q := -1/2-x) (by linarith)).mul_left (x^2)
  refine h.congr fun n => ?_
  dsimp [radialDual]
  ring

lemma radialDual_bound {x : ℝ} (hx : 0 < x) :
    (∑' n, (radialDual x n)^2) ≤ (1+x)^2 := by
  have hP : (∑' n : ℕ, ((n:ℝ)+1)^(-x-1)) ≤ 1+1/x := by
    have h := pseries_bound (show 0 < x/2 by linarith)
    have heq : (fun n : ℕ => ((n:ℝ)+1)^(-2*(x/2)-1)) =
        fun n : ℕ => ((n:ℝ)+1)^(-x-1) := by funext n; congr 1; ring
    rw [heq] at h
    convert h using 1; congr 1; ring
  have hPsum : Summable (fun n : ℕ => ((n:ℝ)+1)^(-x-1)) := by
    have h : Summable (fun n : ℕ => (n:ℝ)^(-x-1)) := Real.summable_nat_rpow.mpr (by linarith)
    simpa only [Nat.cast_add, Nat.cast_one] using (summable_nat_add_iff 1).mpr h
  have hpoint : ∀ n : ℕ, (radialDual x n)^2 ≤
      (x^2*(1+1/x))*((n:ℝ)+1)^(-x-1) := by
    intro n
    have heq : (((n:ℝ)+1)^(-1/2-x))^2 = ((n:ℝ)+1)^((-1/2-x)*2) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (show 0 ≤ (n:ℝ)+1 by positivity)]
      norm_num
    rw [radialDual, mul_pow, mul_pow, Real.sq_sqrt (logWeight_pos n).le, heq]
    calc
      _ ≤ x^2*((1+1/x)*((n:ℝ)+1)^x)*((n:ℝ)+1)^((-1/2-x)*2) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
          (logWeight_le hx n) (sq_nonneg _)) (by positivity)
      _ = (x^2*(1+1/x))*(((n:ℝ)+1)^x*((n:ℝ)+1)^((-1/2-x)*2)) := by ring
      _ = _ := by
        rw [← Real.rpow_add (show 0 < (n:ℝ)+1 by positivity)]
        congr 2
        ring
  calc
    _ ≤ ∑' n : ℕ, (x^2*(1+1/x))*((n:ℝ)+1)^(-x-1) :=
      (radialDual_summable hx).tsum_le_tsum hpoint (hPsum.mul_left _)
    _ = (x^2*(1+1/x))*(∑' n : ℕ, ((n:ℝ)+1)^(-x-1)) := tsum_mul_left
    _ ≤ (x^2*(1+1/x))*(1+1/x) :=
      mul_le_mul_of_nonneg_left hP (by positivity)
    _ = _ := by field_simp [ne_of_gt hx]; ring

lemma log_atom_summable {r : ℕ → ℝ}
    (hr : Summable (fun n => (r n)^2/logWeight n))
    {s : ℂ} (hs : -1/2 < s.re) : Summable (atom r s) := by
  exact Summable.of_norm_bounded
    ((log_weighted_summable hr (show -s.re-1 < -1/2 by linarith)).mul_left ‖s‖)
    (atom_norm_le r (by linarith))

lemma atom_continuous (r : ℕ → ℝ) (n : ℕ) : Continuous (fun s : ℂ => atom r s n) := by
  have h1 : (((n:ℝ)+1:ℝ):ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by positivity)
  have h2 : (((n:ℝ)+2:ℝ):ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by positivity)
  exact ((continuous_id.neg.const_cpow (Or.inl h1)).sub
    (continuous_id.neg.const_cpow (Or.inl h2))).const_mul (r n : ℂ)

lemma log_current_radial_zero {r : ℕ → ℝ}
    (hr : Summable (fun n => (r n)^2/logWeight n))
    {s0 : ℂ} (hs0 : s0.re = -1/2) :
    Tendsto (fun x : ℝ => (x:ℂ)*current r (s0+(x:ℂ))) (𝓝[>]0) (𝓝 0) := by
  let a : ℕ → ℝ := fun n => |r n|/Real.sqrt (logWeight n)
  let b : ℝ → ℕ → ℝ := fun x n => ‖s0+(x:ℂ)‖*radialDual x n
  let f : ℝ → ℕ → ℂ := fun x n => (x:ℂ)*atom r (s0+(x:ℂ)) n
  have ha : Summable (fun n => (a n)^2) := by
    simpa only [a, div_pow, sq_abs, Real.sq_sqrt (logWeight_pos _).le] using hr
  have hcoord : ∀ n, Tendsto (fun x => f x n) (𝓝[>]0) (𝓝 0) := by
    intro n
    have hreal : Tendsto (fun x : ℝ => (x:ℂ)) (𝓝[>]0) (𝓝 0) :=
      (Complex.continuous_ofReal.tendsto 0).mono_left nhdsWithin_le_nhds
    have hs : Tendsto (fun x : ℝ => s0+(x:ℂ)) (𝓝[>]0) (𝓝 s0) := by
      simpa using hreal.const_add s0
    have hatom := ((atom_continuous r n).tendsto s0).comp hs
    simpa [f] using hreal.mul hatom
  have hhyp : ∀ᶠ x : ℝ in 𝓝[>]0,
      Summable (f x) ∧ Summable (fun n => (b x n)^2) ∧
        (∀ n, 0 ≤ b x n) ∧ (∀ n, ‖f x n‖ ≤ a n*b x n) ∧
        (∑' n, (b x n)^2) ≤ (2*(‖s0‖+1))^2 := by
    filter_upwards [eventually_mem_nhdsWithin,
      (eventually_lt_nhds (show (0:ℝ) < 1 by norm_num)).filter_mono nhdsWithin_le_nhds] with x hx hx1
    change 0 < x at hx
    have hs : -1/2 < (s0+(x:ℂ)).re := by simp [hs0]; linarith
    have hnorm : ‖s0+(x:ℂ)‖ ≤ ‖s0‖+1 := by
      have h := norm_add_le s0 (x:ℂ)
      simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx] at h
      linarith
    have hf := (log_atom_summable hr hs).mul_left (x:ℂ)
    have hb : Summable (fun n => (b x n)^2) := by
      have h := (radialDual_summable hx).mul_left (‖s0+(x:ℂ)‖^2)
      simpa only [b, mul_pow] using h
    refine ⟨hf, hb, (fun n => by dsimp [b, radialDual]; positivity), ?_, ?_⟩
    · intro n
      have heq : -((s0+(x:ℂ)).re)-1 = -1/2-x := by simp [hs0]; ring
      have h := mul_le_mul_of_nonneg_left (atom_norm_le r (show -1 ≤ (s0+(x:ℂ)).re by linarith) n) hx.le
      rw [heq] at h
      dsimp only [f]
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx]
      refine h.trans_eq ?_
      dsimp [a, b, radialDual]
      field_simp [ne_of_gt (Real.sqrt_pos.mpr (logWeight_pos n))]
    · have ht : (∑' n, (b x n)^2) = ‖s0+(x:ℂ)‖^2*(∑' n, (radialDual x n)^2) := by
        simp only [b, mul_pow, tsum_mul_left]
      rw [ht]
      calc
        _ ≤ ‖s0+(x:ℂ)‖^2*(1+x)^2 :=
          mul_le_mul_of_nonneg_left (radialDual_bound hx) (sq_nonneg _)
        _ = (‖s0+(x:ℂ)‖*(1+x))^2 := by ring
        _ ≤ _ := pow_le_pow_left₀ (by positivity)
          (show ‖s0+(x:ℂ)‖*(1+x) ≤ 2*(‖s0‖+1) by
            calc
              _ ≤ (‖s0‖+1)*2 := mul_le_mul hnorm (by linarith) (by linarith) (by positivity)
              _ = _ := by ring) 2
  have hlim := family_l2_zero ha (fun n => by dsimp [a]; positivity)
    (show 0 ≤ 2*(‖s0‖+1) by positivity) hcoord hhyp
  have heq : (fun x : ℝ => ∑' n, f x n) = fun x : ℝ => (x:ℂ)*current r (s0+(x:ℂ)) := by
    funext x
    simp only [f, current, tsum_mul_left]
  rwa [heq] at hlim

lemma log_current_differentiableAt {r : ℕ → ℝ} (hr : Summable (fun n => (r n)^2/logWeight n))
    {s : ℂ} (hs : -1/2 < s.re) : DifferentiableAt ℂ (current r) s := by
  let radius : ℝ := (s.re + 1/2)/2
  let q : ℝ := -s.re + radius - 1
  have hradius : 0 < radius := by dsimp [radius]; linarith
  have hq : q < -1/2 := by dsimp [q, radius]; linarith
  have hsum := (log_weighted_summable hr hq).mul_left (‖s‖+radius)
  apply GaloisForLFunctions.HTGeometry.differentiableAt_tsum_of_cauchy_dominated
    (f := fun n z => atom r z n) hradius _ _ hsum
  · intro n z hz
    have h1 : (((n:ℝ)+1:ℝ):ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by positivity)
    have h2 : (((n:ℝ)+2:ℝ):ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by positivity)
    exact (((DifferentiableAt.const_cpow differentiableAt_id.neg (Or.inl h1)).sub
      (DifferentiableAt.const_cpow differentiableAt_id.neg (Or.inl h2))).const_mul
        (r n : ℂ)).differentiableWithinAt
  · intro n z hz
    have hdist : ‖z-s‖ < radius := by simpa [Metric.mem_ball, dist_eq_norm] using hz
    have hre := Complex.re_le_norm (s-z)
    simp only [sub_re, norm_sub_rev s z] at hre
    have hzre : -1 ≤ z.re := by dsimp [radius] at hdist; linarith
    have hexp : -z.re-1 ≤ q := by dsimp [q]; linarith
    have hn : ‖z‖ ≤ ‖s‖+radius := by
      calc
        ‖z‖ = ‖(z-s)+s‖ := by rw [sub_add_cancel]
        _ ≤ ‖z-s‖+‖s‖ := norm_add_le _ _
        _ ≤ _ := by linarith
    calc
      _ ≤ ‖z‖*(|r n| *((n:ℝ)+1)^(-z.re-1)) := atom_norm_le r hzre n
      _ ≤ (‖s‖+radius)*(|r n| *((n:ℝ)+1)^q) :=
        mul_le_mul hn (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le
            (show 1 ≤ (n:ℝ)+1 by linarith [show (0:ℝ) ≤ (n:ℝ) from Nat.cast_nonneg n]) hexp) (abs_nonneg _))
          (by positivity) (by positivity)


end
end RHTower.WoldNaturalAbelLogHilbert

namespace RHTower
open WoldNaturalAbelHilbert WoldNaturalAbelLogHilbert

/-- Critical natural-cutoff energy with one logarithmic damping factor. -/
def WoldNatResidualLogCriticalEnergy : Prop :=
  Summable (fun n : ℕ => xiHeatCassiniWoldNatResidualLogDiscrepancy (n+1)^2 /
    (1+Real.log ((n:ℝ)+1)))

/-- The actual natural Wold source excludes logarithmically damped critical square energy. -/
theorem not_woldNatResidualLogCriticalEnergy : ¬ WoldNatResidualLogCriticalEnergy := by
  intro hEnergy
  let r : ℕ → ℝ := fun n => xiHeatCassiniWoldNatResidualLogDiscrepancy (n+1)
  have hr : Summable (fun n => (r n)^2/logWeight n) := hEnergy
  let C : ℂ := (xiHeatCassiniWoldLogHolonomyConstant : ℂ)
  let F : ℂ → ℂ := fun s => current r s + C
  have hF : AnalyticOnNhd ℂ F (xiHeatCassiniWoldResidualODESector 1) := by
    apply DifferentiableOn.analyticOnNhd _ (isOpen_xiHeatCassiniWoldResidualODESector 1)
    intro s hs
    exact ((log_current_differentiableAt hr (by simpa only [neg_div] using hs.1)).add_const C).differentiableWithinAt
  have hsafe : Set.EqOn F (fun s => abelDirichlet woldNatDifferenceCoeff s)
      {s | s ∈ xiHeatCassiniWoldResidualODESector 1 ∧ 0 < s.re} := by
    intro s hs
    have hD := summable_naturalCpowKernel_sub_succ hs.2
    have hA := log_atom_summable hr (show -1/2 < s.re by linarith [hs.2])
    have hCD := hD.mul_left C
    have heq : (fun n : ℕ => coeffPartial woldNatDifferenceCoeff (n+1) *
        (((((n:ℝ)+1:ℝ):ℂ)^(-s))-((((n:ℝ)+2:ℝ):ℂ)^(-s)))) =
        fun n => atom r s n + C * naturalCpowIncrement s n := by
      funext n
      rw [coeffPartial_woldNatDifferenceCoeff]
      dsimp [r, C, atom, naturalCpowIncrement, naturalCpowKernel]
      push_cast
      simp only [show ((n : ℂ)+1)+1=(n:ℂ)+2 by ring]
      ring
    change current r s + C = ∑' n : ℕ, _
    rw [heq, hA.tsum_add hCD, tsum_mul_left, tsum_naturalCpowKernel_sub_succ hs.2]
    simp [current]
  obtain ⟨s0, m, hs0, him, hm, hpole⟩ := exists_woldNatAbelContinuation_forced_criticalWall_residue
  have hzero : Tendsto (fun x : ℝ => (x:ℂ)*F (s0+(x:ℂ))) (𝓝[>]0) (𝓝 0) := by
    have hc : Tendsto (fun x : ℝ => (x:ℂ)*C) (𝓝[>]0) (𝓝 0) := by
      simpa using ((Complex.continuous_ofReal.tendsto 0).mul_const C).mono_left nhdsWithin_le_nhds
    simpa [F, mul_add] using (log_current_radial_zero hr (by simpa only [neg_div] using hs0)).add hc
  have hcontr := tendsto_nhds_unique hzero (hpole F hF hsafe)
  have hmzero : m = 0 := by simpa using hcontr.symm
  omega

end RHTower
