import GaloisForLFunctions.RHTower.DQPTAltPartialSum

/-!
# DQPT: the Dirichlet eta bound `|η(s)| ≤ |s|/β`

**Supplementary Note 6 (6.3)** of arXiv:2511.11199 (published Supplementary Note 8):
for `s = β + it` with `β > 0`,

`|η(s)| ≤ |s| / β`.

The paper argues by pairing, `η(s) = ∑ₙ s∫_{2n−1}^{2n} ν^{−s−1} dν`, and comparing with
`|s|∫_1^∞ ν^{−β−1} dν = |s|/β`.  Here the same estimate is obtained without any integral:
the "fencing" mean-value theorem compares `x ↦ x^{−s}` directly against the real antiderivative
`C(x) = −(‖s‖/β)·x^{−β}` of `x ↦ ‖s‖x^{−β−1}`, and the disjoint pairs `[2n+1, 2n+2]` telescope
against `C(∞) − C(1) = ‖s‖/β`.

Main results:
* `dqpt_norm_sub_le_of_deriv_le` — the fencing mean-value bound in increment form;
* `dqpt_gap_telescope` — a telescoping bound for a monotone comparison function over
  non-overlapping intervals;
* `dqpt_norm_etaPair_le` — **`‖η(s)‖ ≤ ‖s‖/β`**.
-/

namespace RHTower.DQPT

open Complex Filter Topology Set

noncomputable section

/-! ## Two general tools -/

/-- **Fencing mean-value bound, increment form.**  If `‖f'‖ ≤ B'` on `[a,b)` then
`‖f b − f a‖ ≤ B b − B a`. -/
theorem dqpt_norm_sub_le_of_deriv_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f f' : ℝ → E} {B B' : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Icc a b))
    (hf' : ∀ x ∈ Ico a b, HasDerivWithinAt f (f' x) (Ici x) x)
    (hB : ContinuousOn B (Icc a b))
    (hB' : ∀ x ∈ Ico a b, HasDerivWithinAt B (B' x) (Ici x) x)
    (bound : ∀ x ∈ Ico a b, ‖f' x‖ ≤ B' x) :
    ‖f b - f a‖ ≤ B b - B a := by
  have hg : ContinuousOn (fun x => f x - f a) (Icc a b) := hf.sub continuousOn_const
  have hg' : ∀ x ∈ Ico a b, HasDerivWithinAt (fun x => f x - f a) (f' x) (Ici x) x := by
    intro x hx
    simpa using (hf' x hx).sub_const (f a)
  have hBg : ContinuousOn (fun x => B x - B a) (Icc a b) := hB.sub continuousOn_const
  have hBg' : ∀ x ∈ Ico a b, HasDerivWithinAt (fun x => B x - B a) (B' x) (Ici x) x := by
    intro x hx
    simpa using (hB' x hx).sub_const (B a)
  have ha : ‖(fun x => f x - f a) a‖ ≤ (fun x => B x - B a) a := by simp
  exact image_norm_le_of_norm_deriv_right_le_deriv_boundary' hg hg' ha hBg hBg' bound
    (right_mem_Icc.2 hab)

/-- **Telescoping over non-overlapping intervals.**  If `G` is monotone on `[1, ∞)` and the
intervals `[a n, b n]` do not overlap (`b n ≤ a (n+1)`), the increments sum to at most
`G (a K) − G (a 0)`. -/
theorem dqpt_gap_telescope {G : ℝ → ℝ} {a b : ℕ → ℝ}
    (hmono : ∀ x y : ℝ, 1 ≤ x → x ≤ y → G x ≤ G y)
    (hb : ∀ n, 1 ≤ b n) (hstep : ∀ n, b n ≤ a (n + 1)) (K : ℕ) :
    ∑ n ∈ Finset.range K, (G (b n) - G (a n)) ≤ G (a K) - G (a 0) := by
  induction K with
  | zero => simp
  | succ K ih =>
      rw [Finset.sum_range_succ]
      have h1 : G (b K) ≤ G (a (K + 1)) := hmono (b K) (a (K + 1)) (hb K) (hstep K)
      linarith

/-! ## The comparison function `C(x) = −(‖s‖/β)·x^{−β}` -/

/-- The real comparison function for the `η` bound. -/
def dqptEtaMajorant (s : ℂ) (x : ℝ) : ℝ := -(‖s‖ / s.re) * x ^ (-s.re)

theorem hasDerivAt_dqptEtaMajorant {s : ℂ} (hs : 0 < s.re) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (dqptEtaMajorant s) (‖s‖ * x ^ (-s.re - 1)) x := by
  have hbase : HasDerivAt (fun y : ℝ => y ^ (-s.re)) ((-s.re) * x ^ (-s.re - 1)) x :=
    Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt hx))
  have h := hbase.const_mul (-(‖s‖ / s.re))
  refine h.congr_deriv ?_
  field_simp

theorem dqptEtaMajorant_mono {s : ℂ} (hs : 0 < s.re) :
    ∀ x y : ℝ, 1 ≤ x → x ≤ y → dqptEtaMajorant s x ≤ dqptEtaMajorant s y := by
  intro x y hx hxy
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le zero_lt_one hx
  have hyx : y ^ (-s.re) ≤ x ^ (-s.re) :=
    Real.rpow_le_rpow_of_nonpos hx0 hxy (by linarith)
  have hcoef : (0 : ℝ) ≤ ‖s‖ / s.re := by positivity
  rw [dqptEtaMajorant, dqptEtaMajorant]
  nlinarith [hyx, hcoef]

theorem dqptEtaMajorant_nonpos {s : ℂ} (hs : 0 < s.re) {x : ℝ} (hx : 0 < x) :
    dqptEtaMajorant s x ≤ 0 := by
  have hpow : (0 : ℝ) < x ^ (-s.re) := Real.rpow_pos_of_pos hx _
  have hcoef : (0 : ℝ) ≤ ‖s‖ / s.re := by positivity
  rw [dqptEtaMajorant]
  nlinarith

theorem dqptEtaMajorant_one {s : ℂ} : dqptEtaMajorant s 1 = -(‖s‖ / s.re) := by
  rw [dqptEtaMajorant, Real.one_rpow, mul_one]

/-! ## The term bound -/

theorem norm_dqptRp_sub_le_majorant {s : ℂ} (hs : 0 < s.re) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ‖dqptRp s a - dqptRp s b‖ ≤ dqptEtaMajorant s b - dqptEtaMajorant s a := by
  have hcont : ContinuousOn (fun x : ℝ => dqptRp s x) (Icc a b) := by
    intro x hx
    have hx0 : (0 : ℝ) < x := lt_of_lt_of_le ha hx.1
    exact ((hasDerivAt_dqptRp hs hx0).continuousAt).continuousWithinAt
  have hderiv : ∀ x ∈ Ico a b,
      HasDerivWithinAt (fun y : ℝ => dqptRp s y) ((-s) * dqptRp (s + 1) x) (Ici x) x := by
    intro x hx
    exact (hasDerivAt_dqptRp hs (lt_of_lt_of_le ha hx.1)).hasDerivWithinAt
  have hBcont : ContinuousOn (dqptEtaMajorant s) (Icc a b) := by
    intro x hx
    have hx0 : (0 : ℝ) < x := lt_of_lt_of_le ha hx.1
    exact ((hasDerivAt_dqptEtaMajorant hs hx0).continuousAt).continuousWithinAt
  have hBderiv : ∀ x ∈ Ico a b,
      HasDerivWithinAt (dqptEtaMajorant s) (‖s‖ * x ^ (-s.re - 1)) (Ici x) x := by
    intro x hx
    exact (hasDerivAt_dqptEtaMajorant hs (lt_of_lt_of_le ha hx.1)).hasDerivWithinAt
  have hbound : ∀ x ∈ Ico a b, ‖(-s) * dqptRp (s + 1) x‖ ≤ ‖s‖ * x ^ (-s.re - 1) := by
    intro x hx
    have hx0 : (0 : ℝ) < x := lt_of_lt_of_le ha hx.1
    rw [norm_mul, norm_neg, dqptRp_norm hx0]
    have hre : -(s + 1).re = -s.re - 1 := by
      rw [Complex.add_re, Complex.one_re]; ring
    rw [hre]
  have key := dqpt_norm_sub_le_of_deriv_le hab hcont hderiv hBcont hBderiv hbound
  rw [norm_sub_rev]
  exact key

theorem norm_etaTerm_le_majorant {s : ℂ} (hs : 0 < s.re) (n : ℕ) :
    ‖etaTerm s n‖
      ≤ dqptEtaMajorant s (2 * (n : ℝ) + 2) - dqptEtaMajorant s (2 * (n : ℝ) + 1) := by
  have ha : (0 : ℝ) < 2 * (n : ℝ) + 1 := by positivity
  have hab : 2 * (n : ℝ) + 1 ≤ 2 * (n : ℝ) + 2 := by linarith
  have h := norm_dqptRp_sub_le_majorant hs ha hab
  have heq : etaTerm s n = dqptRp s (2 * (n : ℝ) + 1) - dqptRp s (2 * (n : ℝ) + 2) := rfl
  rw [heq]
  exact h

/-! ## Supplementary Note 6 (6.3) -/

/-- **`‖η(s)‖ ≤ ‖s‖/β`** for `s = β + it` with `β > 0`, where `η` is the paired Dirichlet eta
series `etaPair`. -/
theorem dqpt_norm_etaPair_le {s : ℂ} (hs : 0 < s.re) : ‖etaPair s‖ ≤ ‖s‖ / s.re := by
  set a : ℕ → ℝ := fun n => 2 * (n : ℝ) + 1 with hadef
  set b : ℕ → ℝ := fun n => 2 * (n : ℝ) + 2 with hbdef
  have hb1 : ∀ n : ℕ, (1 : ℝ) ≤ b n := by
    intro n; rw [hbdef]; have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n; simp; linarith
  have hstep : ∀ n : ℕ, b n ≤ a (n + 1) := by
    intro n; rw [hadef, hbdef]; push_cast; linarith
  have hpartial : ∀ K : ℕ, ∑ n ∈ Finset.range K, ‖etaTerm s n‖ ≤ ‖s‖ / s.re := by
    intro K
    have hcompare : ∑ n ∈ Finset.range K, ‖etaTerm s n‖
        ≤ ∑ n ∈ Finset.range K, (dqptEtaMajorant s (b n) - dqptEtaMajorant s (a n)) :=
      Finset.sum_le_sum (fun n _ => norm_etaTerm_le_majorant hs n)
    have htel := dqpt_gap_telescope (dqptEtaMajorant_mono hs) hb1 hstep K
    have haK : dqptEtaMajorant s (a K) ≤ 0 := by
      refine dqptEtaMajorant_nonpos hs ?_
      rw [hadef]; positivity
    have ha0 : dqptEtaMajorant s (a 0) = -(‖s‖ / s.re) := by
      have : a 0 = 1 := by rw [hadef]; norm_num
      rw [this, dqptEtaMajorant_one]
    rw [ha0] at htel
    linarith
  have hsummable : Summable (fun n : ℕ => ‖etaTerm s n‖) := (summable_etaTerm s hs).norm
  have htsum : ∑' n : ℕ, ‖etaTerm s n‖ ≤ ‖s‖ / s.re :=
    Real.tsum_le_of_sum_range_le (fun n => norm_nonneg _) hpartial
  calc ‖etaPair s‖ = ‖∑' n : ℕ, etaTerm s n‖ := rfl
    _ ≤ ∑' n : ℕ, ‖etaTerm s n‖ := norm_tsum_le_tsum_norm hsummable
    _ ≤ ‖s‖ / s.re := htsum

end

end RHTower.DQPT
