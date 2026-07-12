import Mathlib
import GaloisForLFunctions.RHTower.DegreeZeroOffline

/-!
# The Riemann zeta function is a negative real inside the critical strip

For every real `σ ∈ (0,1)` the value `ζ(σ)` is a strictly negative real number, and in
particular `ζ(σ) ≠ 0`.  The argument is entirely coefficient-side: it never uses the
functional equation or any deep analytic input beyond analytic continuation.

The engine is the **paired Dirichlet eta series**
`E(s) = ∑ₙ ((2n+1)^{-s} − (2n+2)^{-s})`.  Pairing adjacent integers turns the conditionally
convergent alternating zeta series into an absolutely convergent one: the mean-value
inequality on the real segment `[2n+1, 2n+2]` for `x ↦ x^{-s}` gives
`‖(2n+1)^{-s} − (2n+2)^{-s}‖ ≤ ‖s‖·(2n+1)^{-Re s − 1}`, summable for `Re s > 0`.  A
Weierstrass `M`-test on bounded sub-half-planes makes `E` analytic on `{Re s > 0}`.

Splitting the positive integers into odds and evens shows, for `Re s > 1`,
`E(s) = (1 − 2^{1−s})·ζ(s)`.  Both sides are analytic on the half-plane minus its pole
`U = {Re s > 0} ∖ {1}`, which is preconnected (a punctured half-plane, covered by four convex
pieces sharing points), so the identity theorem extends the identity to all of `U`.

At a real point `σ ∈ (0,1)` each summand `(2n+1)^{-σ} − (2n+2)^{-σ}` is a strictly positive
real, so `E(σ)` is a positive real; and `1 − 2^{1−σ}` is a negative real because
`2^{1−σ} > 1`.  Hence `ζ(σ) = E(σ)/(1 − 2^{1−σ})` is a negative real.

As consumers, `ζ` does not vanish at `ρdzo = 1/3`, the carrier `ζ·dzo` has a simple zero
there (order `0 + 1 = 1`), and its base-level deck charge is `(−1)¹ = −1`.
-/

namespace RHTower

noncomputable section

open Complex Set

/-- The `n`-th paired eta summand `(2n+1)^{-s} − (2n+2)^{-s}` (real bases). -/
def etaTerm (s : ℂ) (n : ℕ) : ℂ :=
  ((2 * n + 1 : ℝ) : ℂ) ^ (-s) - ((2 * n + 2 : ℝ) : ℂ) ^ (-s)

/-- The paired Dirichlet eta series `E(s) = ∑ₙ ((2n+1)^{-s} − (2n+2)^{-s})`. -/
def etaPair (s : ℂ) : ℂ := ∑' n : ℕ, etaTerm s n

/-- **Mean-value term bound.**  On the real segment `[2n+1, 2n+2]` the map `x ↦ x^{-s}` has
derivative `-s·x^{-s-1}` of norm at most `‖s‖·(2n+1)^{-Re s−1}`, so the increment of the
paired summand is bounded by that constant times the unit length of the segment. -/
private theorem norm_etaTerm_le (s : ℂ) (hs : 0 < s.re) (n : ℕ) :
    ‖etaTerm s n‖ ≤ ‖s‖ * (2 * n + 1 : ℝ) ^ (-s.re - 1) := by
  set a : ℝ := 2 * (n : ℝ) + 1 with ha
  set b : ℝ := 2 * (n : ℝ) + 2 with hb
  have hab : a ≤ b := by rw [ha, hb]; linarith
  have ha0 : (0 : ℝ) < a := by rw [ha]; positivity
  set C : ℝ := ‖s‖ * a ^ (-s.re - 1) with hC
  have hsne : (-s) ≠ 0 := by
    intro h; apply (ne_of_gt hs); rw [neg_eq_zero] at h; rw [h]; simp
  have hderiv : ∀ x ∈ Icc a b,
      HasDerivWithinAt (fun y : ℝ => (y : ℂ) ^ (-s)) ((-s) * (x : ℂ) ^ (-s - 1)) (Icc a b) x := by
    intro x hx
    have hx0 : x ≠ 0 := ne_of_gt (lt_of_lt_of_le ha0 hx.1)
    exact (hasDerivAt_ofReal_cpow_const hx0 hsne).hasDerivWithinAt
  have hre : ((-s - 1 : ℂ)).re = -s.re - 1 := by simp
  have hbound : ∀ x ∈ Ico a b, ‖(-s) * (x : ℂ) ^ (-s - 1)‖ ≤ C := by
    intro x hx
    have hx0 : (0 : ℝ) < x := lt_of_lt_of_le ha0 hx.1
    have hax : a ≤ x := hx.1
    rw [norm_mul, norm_neg, hC]
    have hnorm : ‖(x : ℂ) ^ (-s - 1)‖ = x ^ (-s.re - 1) := by
      rw [norm_cpow_eq_rpow_re_of_pos hx0, hre]
    rw [hnorm]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos ha0 hax (by linarith)) (norm_nonneg s)
  have key := norm_image_sub_le_of_norm_deriv_le_segment' hderiv hbound b (right_mem_Icc.2 hab)
  have hba : b - a = 1 := by rw [ha, hb]; ring
  rw [hba, mul_one] at key
  have hE : etaTerm s n = (a : ℂ) ^ (-s) - (b : ℂ) ^ (-s) := by rw [etaTerm, ha, hb]
  rw [hE, norm_sub_rev]
  calc ‖(b : ℂ) ^ (-s) - (a : ℂ) ^ (-s)‖ ≤ C := key
    _ = ‖s‖ * (2 * n + 1 : ℝ) ^ (-s.re - 1) := by rw [hC, ha]

/-- **Absolute convergence for `Re s > 0`.**  The term bound is dominated by the summable
`p`-series `∑ ‖s‖·(n+1)^{-Re s−1}` (exponent `< −1`). -/
theorem summable_etaTerm (s : ℂ) (hs : 0 < s.re) : Summable (etaTerm s) := by
  have hg : Summable (fun n : ℕ => ‖s‖ * ((n : ℝ) + 1) ^ (-s.re - 1)) := by
    apply Summable.mul_left
    have h2 := (summable_nat_add_iff 1).mpr
      (Real.summable_nat_rpow.mpr (show -s.re - 1 < -1 by linarith))
    refine h2.congr (fun n => ?_)
    push_cast; ring_nf
  refine Summable.of_norm_bounded hg (fun n => ?_)
  calc ‖etaTerm s n‖ ≤ ‖s‖ * (2 * n + 1 : ℝ) ^ (-s.re - 1) := norm_etaTerm_le s hs n
    _ ≤ ‖s‖ * ((n : ℝ) + 1) ^ (-s.re - 1) := by
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg s)
        exact Real.rpow_le_rpow_of_nonpos (by positivity)
          (by have := Nat.cast_nonneg (α := ℝ) n; linarith) (by linarith)

/-- Each paired summand is entire (a difference of constant-base powers). -/
private theorem differentiable_etaTerm (n : ℕ) : Differentiable ℂ (fun w : ℂ => etaTerm w n) := by
  have h1 : ((2 * (n : ℝ) + 1 : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (by positivity)
  have h2 : ((2 * (n : ℝ) + 2 : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (by positivity)
  exact (Differentiable.const_cpow differentiable_neg (Or.inl h1)).sub
    (Differentiable.const_cpow differentiable_neg (Or.inl h2))

/-- **Analyticity on the right half-plane.**  A Weierstrass `M`-test on each bounded ball
`B(s₀, Re s₀/2)` (where `‖w‖` and the term bound are uniformly controlled) gives local
differentiability, hence analyticity, on the open set `{Re s > 0}`. -/
private theorem etaPair_analyticOnNhd : AnalyticOnNhd ℂ etaPair {s : ℂ | 0 < s.re} := by
  apply DifferentiableOn.analyticOnNhd _ (isOpen_lt continuous_const Complex.continuous_re)
  intro s₀ hs₀
  simp only [Set.mem_setOf_eq] at hs₀
  refine (?_ : DifferentiableAt ℂ etaPair s₀).differentiableWithinAt
  set ε : ℝ := s₀.re / 2 with hε
  have hεpos : 0 < ε := by rw [hε]; linarith
  set U : Set ℂ := Metric.ball s₀ ε with hU
  have hUopen : IsOpen U := Metric.isOpen_ball
  have hs₀U : s₀ ∈ U := Metric.mem_ball_self hεpos
  set M : ℝ := ‖s₀‖ + ε with hM
  have hbnd : ∀ (w : ℂ), w ∈ U → ε ≤ w.re ∧ ‖w‖ ≤ M := by
    intro w hw
    rw [hU, Metric.mem_ball, Complex.dist_eq] at hw
    have hre : |(w - s₀).re| ≤ ‖w - s₀‖ := Complex.abs_re_le_norm _
    have hre2 : |w.re - s₀.re| < ε := by
      have hd : (w - s₀).re = w.re - s₀.re := by simp
      rw [hd] at hre; linarith [hre, hw]
    refine ⟨?_, ?_⟩
    · have := abs_lt.mp hre2; rw [hε]; linarith [this.1]
    · calc ‖w‖ = ‖s₀ + (w - s₀)‖ := by ring_nf
        _ ≤ ‖s₀‖ + ‖w - s₀‖ := norm_add_le _ _
        _ ≤ M := by rw [hM]; linarith [hw]
  set u : ℕ → ℝ := fun n => M * ((n : ℝ) + 1) ^ (-ε - 1) with hu
  have hMnn : 0 ≤ M := by rw [hM]; positivity
  have husum : Summable u := by
    apply Summable.mul_left
    have h2 := (summable_nat_add_iff 1).mpr
      (Real.summable_nat_rpow.mpr (show -ε - 1 < -1 by linarith))
    refine h2.congr (fun n => ?_); push_cast; ring_nf
  have hFle : ∀ (n : ℕ) (w : ℂ), w ∈ U → ‖etaTerm w n‖ ≤ u n := by
    intro n w hw
    obtain ⟨hwre, hwnorm⟩ := hbnd w hw
    have hwrepos : 0 < w.re := lt_of_lt_of_le hεpos hwre
    have hstep : ‖etaTerm w n‖ ≤ ‖w‖ * (2 * n + 1 : ℝ) ^ (-w.re - 1) := norm_etaTerm_le w hwrepos n
    have hbasepos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hbaseA : ((n : ℝ) + 1) ≤ (2 * (n : ℝ) + 1) := by linarith [Nat.cast_nonneg (α := ℝ) n]
    have stepA : (2 * (n : ℝ) + 1) ^ (-w.re - 1) ≤ ((n : ℝ) + 1) ^ (-w.re - 1) :=
      Real.rpow_le_rpow_of_nonpos hbasepos hbaseA (by linarith)
    have hb1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) n]
    have stepB : ((n : ℝ) + 1) ^ (-w.re - 1) ≤ ((n : ℝ) + 1) ^ (-ε - 1) :=
      Real.rpow_le_rpow_of_exponent_le hb1 (by linarith)
    have hchain : (2 * (n : ℝ) + 1) ^ (-w.re - 1) ≤ ((n : ℝ) + 1) ^ (-ε - 1) := le_trans stepA stepB
    have hrpownn : 0 ≤ (2 * (n : ℝ) + 1) ^ (-w.re - 1) := Real.rpow_nonneg (by positivity) _
    calc ‖etaTerm w n‖ ≤ ‖w‖ * (2 * n + 1 : ℝ) ^ (-w.re - 1) := hstep
      _ ≤ M * ((n : ℝ) + 1) ^ (-ε - 1) := by
          exact mul_le_mul hwnorm hchain hrpownn hMnn
      _ = u n := by rw [hu]
  have hdiffterm : ∀ n : ℕ, DifferentiableOn ℂ (fun w : ℂ => etaTerm w n) U :=
    fun n => (differentiable_etaTerm n).differentiableOn
  have hdon : DifferentiableOn ℂ (fun w : ℂ => ∑' n : ℕ, etaTerm w n) U :=
    differentiableOn_tsum_of_summable_norm husum hdiffterm hUopen hFle
  exact hdon.differentiableAt (hUopen.mem_nhds hs₀U)

/-- **The eta–zeta identity for `Re s > 1`.**  Splitting the positive integers into odd and
even parts, `∑ₖ(2k+1)^{-s} + ∑ₖ(2k+2)^{-s} = ζ(s)` and `∑ₖ(2k+2)^{-s} = 2^{-s}ζ(s)`, whence
`E(s) = ζ(s) − 2·2^{-s}ζ(s) = (1 − 2^{1−s})·ζ(s)`. -/
private theorem etaPair_eq_of_one_lt_re (s : ℂ) (hs : 1 < s.re) :
    etaPair s = (1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s := by
  set f : ℕ → ℂ := fun n => ((n : ℂ) + 1) ^ (-s) with hf
  have hzeta : riemannZeta s = ∑' n : ℕ, f n := by
    rw [zeta_eq_tsum_one_div_nat_add_one_cpow hs]
    apply tsum_congr; intro n
    rw [hf]; simp only; rw [Complex.cpow_neg]; rw [one_div]
  have hfsum : Summable f := by
    have h0 : Summable (fun n : ℕ => 1 / (n : ℂ) ^ s) := Complex.summable_one_div_nat_cpow.mpr hs
    have h1 := (summable_nat_add_iff 1).mpr h0
    refine h1.congr (fun n => ?_)
    rw [hf]; simp only; rw [Complex.cpow_neg, one_div]
    congr 2; push_cast; ring
  have hinj2 : Function.Injective (fun k : ℕ => 2 * k) := by intro a b h; simpa using h
  have hinj2' : Function.Injective (fun k : ℕ => 2 * k + 1) := by intro a b h; simpa using h
  have hev : Summable (fun k : ℕ => f (2 * k)) := hfsum.comp_injective hinj2
  have hod : Summable (fun k : ℕ => f (2 * k + 1)) := hfsum.comp_injective hinj2'
  have hsplit : (∑' k, f (2 * k)) + ∑' k, f (2 * k + 1) = ∑' n, f n :=
    tsum_even_add_odd hev hod
  have hodd_val : (∑' k : ℕ, f (2 * k + 1)) = (2 : ℂ) ^ (-s) * riemannZeta s := by
    have hstep : ∀ k : ℕ, f (2 * k + 1) = (2 : ℂ) ^ (-s) * ((k : ℂ) + 1) ^ (-s) := by
      intro k
      rw [hf]; simp only
      have hcast : ((2 * k + 1 : ℕ) : ℂ) + 1 = ((2 : ℝ) : ℂ) * (((k : ℝ) + 1 : ℝ) : ℂ) := by
        push_cast; ring
      rw [hcast, mul_cpow_ofReal_nonneg (by norm_num) (by positivity)]
      push_cast; ring
    rw [tsum_congr hstep, tsum_mul_left]
    congr 1
    rw [hzeta, hf]
  have heven_val : (∑' k : ℕ, f (2 * k)) = riemannZeta s - (2 : ℂ) ^ (-s) * riemannZeta s := by
    have h := hsplit
    rw [hodd_val, ← hzeta] at h
    exact eq_sub_of_add_eq h
  have hetaterm : ∀ k : ℕ, etaTerm s k = f (2 * k) - f (2 * k + 1) := by
    intro k
    rw [etaTerm, hf]; simp only
    congr 2 <;> · push_cast; ring
  have hetasum : ∑' n : ℕ, etaTerm s n = (∑' k, f (2 * k)) - ∑' k, f (2 * k + 1) := by
    rw [tsum_congr hetaterm]; exact hev.tsum_sub hod
  rw [etaPair, hetasum, heven_val, hodd_val]
  have h21 : (2 : ℂ) ^ (1 - s) = 2 * (2 : ℂ) ^ (-s) := by
    rw [show (1 - s) = (1 : ℂ) + (-s) by ring, Complex.cpow_add _ _ (two_ne_zero), Complex.cpow_one]
  rw [h21]; ring

/-- **The punctured right half-plane is preconnected.**  `{Re s > 0} ∖ {1}` is the union of
four convex pieces — the strip `0 < Re s < 1`, the half-plane `Re s > 1`, and the open upper
and lower quarter-planes — successively glued along shared points. -/
private theorem isPreconnected_posStrip_diff_one :
    IsPreconnected ({s : ℂ | 0 < s.re} \ {1}) := by
  set L : Set ℂ := {s | 0 < s.re ∧ s.re < 1} with hLdef
  set R : Set ℂ := {s | 1 < s.re} with hRdef
  set Up : Set ℂ := {s | 0 < s.re ∧ 0 < s.im} with hUpdef
  set Dn : Set ℂ := {s | 0 < s.re ∧ s.im < 0} with hDndef
  have cL : Convex ℝ L := (convex_halfSpace_re_gt 0).inter (convex_halfSpace_re_lt 1)
  have cR : Convex ℝ R := convex_halfSpace_re_gt 1
  have cUp : Convex ℝ Up := (convex_halfSpace_re_gt 0).inter (convex_halfSpace_im_gt 0)
  have cDn : Convex ℝ Dn := (convex_halfSpace_re_gt 0).inter (convex_halfSpace_im_lt 0)
  have pL := cL.isPreconnected
  have pR := cR.isPreconnected
  have pUp := cUp.isPreconnected
  have pDn := cDn.isPreconnected
  have p1 : IsPreconnected (L ∪ Up) := by
    refine pL.union (((1 : ℝ) / 2 : ℂ) + I) ?_ ?_ pUp
    · exact ⟨by simp, by norm_num⟩
    · exact ⟨by simp, by simp⟩
  have p2 : IsPreconnected (L ∪ Up ∪ R) := by
    refine p1.union ((2 : ℂ) + I) ?_ ?_ pR
    · exact Or.inr ⟨by simp, by simp⟩
    · show 1 < ((2 : ℂ) + I).re; simp
  have p3 : IsPreconnected (L ∪ Up ∪ R ∪ Dn) := by
    refine p2.union (((1 : ℝ) / 2 : ℂ) - I) ?_ ?_ pDn
    · exact Or.inl (Or.inl ⟨by simp, by norm_num⟩)
    · exact ⟨by simp, by simp⟩
  have hset : ({s : ℂ | 0 < s.re} \ {1}) = L ∪ Up ∪ R ∪ Dn := by
    apply Set.Subset.antisymm
    · intro s hs
      obtain ⟨hre, hne⟩ := hs
      rw [Set.mem_setOf_eq] at hre
      rw [Set.mem_singleton_iff] at hne
      rcases lt_trichotomy s.re 1 with h | h | h
      · exact Or.inl (Or.inl (Or.inl ⟨hre, h⟩))
      · have him : s.im ≠ 0 := by
          intro h0; apply hne; apply Complex.ext <;> simp [h, h0]
        rcases lt_or_gt_of_ne him with hlt | hgt
        · exact Or.inr ⟨hre, hlt⟩
        · exact Or.inl (Or.inl (Or.inr ⟨hre, hgt⟩))
      · exact Or.inl (Or.inr h)
    · refine Set.union_subset (Set.union_subset (Set.union_subset ?_ ?_) ?_) ?_
      · intro s hs; obtain ⟨hre, hlt⟩ := hs
        exact ⟨hre, by rw [Set.mem_singleton_iff]; rintro rfl; simp at hlt⟩
      · intro s hs; obtain ⟨hre, him⟩ := hs
        exact ⟨hre, by rw [Set.mem_singleton_iff]; rintro rfl; simp at him⟩
      · intro s hs; rw [Set.mem_setOf_eq] at hs
        exact ⟨show 0 < s.re by linarith, by rw [Set.mem_singleton_iff]; rintro rfl; simp at hs⟩
      · intro s hs; obtain ⟨hre, him⟩ := hs
        exact ⟨hre, by rw [Set.mem_singleton_iff]; rintro rfl; simp at him⟩
  rw [hset]; exact p3

/-- **The eta–zeta identity on all of `{Re s > 0} ∖ {1}`.**  Both `E` and `(1 − 2^{1−s})·ζ`
are analytic on the preconnected punctured half-plane and agree on `{Re s > 1}`, so the
identity theorem propagates the equality. -/
theorem etaPair_eq (s : ℂ) (hs0 : 0 < s.re) (hs1 : s ≠ 1) :
    etaPair s = (1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s := by
  set U : Set ℂ := {s : ℂ | 0 < s.re} \ {1} with hUdef
  have hUopen : IsOpen U :=
    (isOpen_lt continuous_const Complex.continuous_re).sdiff isClosed_singleton
  have hUsub0 : U ⊆ {s : ℂ | 0 < s.re} := Set.diff_subset
  have hUsub1 : U ⊆ {(1 : ℂ)}ᶜ := fun s hs => hs.2
  set g : ℂ → ℂ := fun s => (1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s with hgdef
  have hgan : AnalyticOnNhd ℂ g U := by
    have hf1 : AnalyticOnNhd ℂ (fun s : ℂ => 1 - (2 : ℂ) ^ (1 - s)) U := by
      have hd : Differentiable ℂ (fun s : ℂ => 1 - (2 : ℂ) ^ (1 - s)) := by
        apply Differentiable.sub (differentiable_const _)
        exact Differentiable.const_cpow ((differentiable_const (1 : ℂ)).sub differentiable_id)
          (Or.inl two_ne_zero)
      exact hd.differentiableOn.analyticOnNhd hUopen
    exact hf1.mul (analyticOn_riemannZeta.mono hUsub1)
  have hetaU : AnalyticOnNhd ℂ etaPair U := etaPair_analyticOnNhd.mono hUsub0
  have hgt_open : IsOpen {s : ℂ | 1 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hz0U : (2 : ℂ) ∈ U := by
    refine ⟨?_, ?_⟩
    · show 0 < (2 : ℂ).re; simp
    · simp
  have hz0gt : (2 : ℂ) ∈ {s : ℂ | 1 < s.re} := by show 1 < (2 : ℂ).re; simp
  have heq : etaPair =ᶠ[nhds (2 : ℂ)] g :=
    Filter.eventuallyEq_of_mem (hgt_open.mem_nhds hz0gt) (fun s hs => etaPair_eq_of_one_lt_re s hs)
  have hEqOn : Set.EqOn etaPair g U :=
    hetaU.eqOn_of_preconnected_of_eventuallyEq hgan (hUdef ▸ isPreconnected_posStrip_diff_one)
      hz0U heq
  exact hEqOn ⟨hs0, hs1⟩

/-- Each paired summand at a real argument is the cast of a real difference of `rpow`s. -/
theorem etaTerm_ofReal (σ : ℝ) (n : ℕ) :
    etaTerm (σ : ℂ) n = (((2 * n + 1 : ℝ) ^ (-σ) - (2 * n + 2 : ℝ) ^ (-σ) : ℝ) : ℂ) := by
  rw [etaTerm]
  have h1 : ((2 * (n : ℝ) + 1 : ℝ) : ℂ) ^ (-(σ : ℂ)) = (((2 * (n : ℝ) + 1 : ℝ) ^ (-σ) : ℝ) : ℂ) := by
    rw [show (-(σ : ℂ)) = (((-σ : ℝ)) : ℂ) by push_cast; ring,
        ← Complex.ofReal_cpow (by positivity)]
  have h2 : ((2 * (n : ℝ) + 2 : ℝ) : ℂ) ^ (-(σ : ℂ)) = (((2 * (n : ℝ) + 2 : ℝ) ^ (-σ) : ℝ) : ℂ) := by
    rw [show (-(σ : ℂ)) = (((-σ : ℝ)) : ℂ) by push_cast; ring,
        ← Complex.ofReal_cpow (by positivity)]
  rw [h1, h2, ← Complex.ofReal_sub]

/-- The real paired summand is strictly positive on `(0, ∞)`: `(2n+1)^{-σ} > (2n+2)^{-σ}`. -/
theorem etaRealTerm_pos (σ : ℝ) (hσ : 0 < σ) (n : ℕ) :
    0 < (2 * n + 1 : ℝ) ^ (-σ) - (2 * n + 2 : ℝ) ^ (-σ) := by
  have : (2 * (n : ℝ) + 2) ^ (-σ) < (2 * (n : ℝ) + 1) ^ (-σ) :=
    Real.rpow_lt_rpow_of_neg (by positivity) (by linarith) (by linarith)
  linarith

/-- **`ζ` is a strictly negative real inside the critical strip.**  For `σ ∈ (0,1)` the paired
eta series `E(σ)` is a positive real and `1 − 2^{1−σ}` is a negative real, so
`ζ(σ) = E(σ)/(1 − 2^{1−σ})` is a negative real. -/
theorem riemannZeta_real_strip_neg {σ : ℝ} (h0 : 0 < σ) (h1 : σ < 1) :
    ∃ x : ℝ, x < 0 ∧ riemannZeta (σ : ℂ) = (x : ℂ) := by
  have hσ0 : (0 : ℝ) < (σ : ℂ).re := by simp [h0]
  have hσ1 : (σ : ℂ) ≠ 1 := by rw [Ne, Complex.ofReal_eq_one]; exact ne_of_lt h1
  set rt : ℕ → ℝ := fun n => (2 * n + 1 : ℝ) ^ (-σ) - (2 * n + 2 : ℝ) ^ (-σ) with hrt
  have hsum : Summable rt := by
    rw [← Complex.summable_ofReal]
    apply (summable_etaTerm (σ : ℂ) hσ0).congr
    intro n; rw [etaTerm_ofReal]
  have hrpos : 0 < ∑' n, rt n :=
    hsum.tsum_pos (fun n => le_of_lt (etaRealTerm_pos σ h0 n)) 0 (etaRealTerm_pos σ h0 0)
  set r : ℝ := ∑' n, rt n with hr
  have hEval : etaPair (σ : ℂ) = (r : ℂ) := by
    rw [etaPair, hr, Complex.ofReal_tsum]
    apply tsum_congr; intro n; rw [etaTerm_ofReal]
  set c : ℝ := 1 - (2 : ℝ) ^ (1 - σ) with hc
  have hcneg : c < 0 := by
    have : (1 : ℝ) < (2 : ℝ) ^ (1 - σ) := Real.one_lt_rpow (by norm_num) (by linarith)
    rw [hc]; linarith
  have hcC : (1 - (2 : ℂ) ^ (1 - (σ : ℂ))) = (c : ℂ) := by
    have h2 : (2 : ℂ) ^ (1 - (σ : ℂ)) = (((2 : ℝ) ^ (1 - σ) : ℝ) : ℂ) := by
      rw [show (1 - (σ : ℂ)) = (((1 - σ : ℝ)) : ℂ) by push_cast; ring,
          Complex.ofReal_cpow (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num
    rw [h2, hc]; push_cast; ring
  have hidn := etaPair_eq (σ : ℂ) hσ0 hσ1
  rw [hEval, hcC] at hidn
  refine ⟨r / c, div_neg_of_pos_of_neg hrpos hcneg, ?_⟩
  have hcne : (c : ℂ) ≠ 0 := by exact_mod_cast ne_of_lt hcneg
  have hζeq : riemannZeta (σ : ℂ) = (r : ℂ) / (c : ℂ) := by rw [hidn]; field_simp
  rw [hζeq, ← Complex.ofReal_div]

/-- **`ζ` does not vanish inside the critical strip on the real axis.** -/
theorem riemannZeta_real_strip_ne_zero {σ : ℝ} (h0 : 0 < σ) (h1 : σ < 1) :
    riemannZeta (σ : ℂ) ≠ 0 := by
  obtain ⟨x, hx, hxeq⟩ := riemannZeta_real_strip_neg h0 h1
  rw [hxeq, Complex.ofReal_ne_zero]
  exact ne_of_lt hx

/-! ### Consumers at the off-line witness `ρdzo = 1/3` -/

/-- **`ζ` does not vanish at `ρdzo = 1/3`**, which lies strictly inside the open strip. -/
theorem riemannZeta_ρdzo_ne_zero : riemannZeta ρdzo ≠ 0 := by
  have hρ : ρdzo = ((1 / 3 : ℝ) : ℂ) := rfl
  rw [hρ]
  exact riemannZeta_real_strip_ne_zero (by norm_num) (by norm_num)

/-- `ζ` is analytic at `ρdzo` (its `Re` is `1/3 ≠ 1`, so it is away from the pole). -/
private theorem zeta_analyticAt_ρdzo : AnalyticAt ℂ riemannZeta ρdzo := by
  apply analyticOn_riemannZeta
  rw [Set.mem_compl_iff, Set.mem_singleton_iff]
  intro h
  have hre : ρdzo.re = (1 : ℂ).re := by rw [h]
  rw [ρdzo_re] at hre; simp at hre

/-- `dzo` is entire, hence analytic at `ρdzo`. -/
private theorem dzo_analyticAt_ρdzo : AnalyticAt ℂ dzo ρdzo := by
  have hd : Differentiable ℂ dzo := by
    rw [dzo_eq_exp]
    apply Differentiable.mul
    · exact Differentiable.sub (differentiable_const _)
        (Differentiable.const_mul (Differentiable.cexp (by fun_prop)) 2)
    · exact Differentiable.sub (differentiable_const _)
        (Differentiable.const_mul (Differentiable.cexp (by fun_prop)) 4)
  exact (hd.differentiableOn.analyticOnNhd isOpen_univ) ρdzo (Set.mem_univ _)

/-- **The carrier `ζ·dzo` has a simple zero at `ρdzo`.**  `ζ` is analytic and nonzero there
(order `0`) while `dzo` has a simple zero (order `1`); orders of an analytic product add. -/
theorem zetaMulDzo_order_one :
    analyticOrderAt (fun s => riemannZeta s * dzo s) ρdzo = 1 := by
  have hz : AnalyticAt ℂ riemannZeta ρdzo := zeta_analyticAt_ρdzo
  have hd : AnalyticAt ℂ dzo ρdzo := dzo_analyticAt_ρdzo
  have hzero : analyticOrderAt riemannZeta ρdzo = 0 :=
    hz.analyticOrderAt_eq_zero.mpr riemannZeta_ρdzo_ne_zero
  show analyticOrderAt (riemannZeta * dzo) ρdzo = 1
  rw [analyticOrderAt_mul hz hd, hzero, dzo_order_one, zero_add]

/-- **The carrier `ζ·dzo` carries off-line deck charge `−1`.**  Its order-`1` (odd) zero at
`ρdzo` gives base-level charge `(−1)¹ = −1`. -/
theorem zetaMulDzo_charge_neg_one :
    carrierCharge (fun s => riemannZeta s * dzo s) 1 ρdzo = -1 := by
  rw [carrierCharge_one_eq_neg_one_pow, zetaMulDzo_order_one, ENat.toNat_one]
  norm_num

end

end RHTower
