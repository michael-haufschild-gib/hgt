import GaloisForLFunctions.Hurwitz.ContinuedUpperEnd
import GaloisForLFunctions.Hurwitz.LadderDeformationBridge

/-!
# Monodromy bridge for the Taylor-regularized Hurwitz ladder

The convergence-chamber monodromy proof is rebuilt for the concrete continued carrier.  Near the
branch point `a = -n`, the singular term is kept as `exp (-(s+k) z)`.  Every remaining term is
Taylor-regularized and depends on `z` only through `exp z`, hence is `2πi`-periodic.
-/

open Complex HurwitzZetaShift HurwitzN2Tail HurwitzN2HZeta HurwitzSpine HurwitzOrbit

namespace HurwitzLadder

open HurwitzZetaContinuation Filter Set Topology

noncomputable section

/-- Finite branch-coordinate deformation of the continued Hurwitz ladder. -/
def continuedDzeta (s : ℂ) (M : ℕ) (c : Fin (M + 1) → ℂ) (k : ℕ) (a : ℂ) : ℂ :=
  continuedHzeta (s + k) a +
    ∑ n : Fin (M + 1), (c n - 1) * ((((n : ℕ) : ℂ) + a) ^ (-(s + k)))

@[simp]
theorem continuedDzeta_one (s : ℂ) (M k : ℕ) (a : ℂ) :
    continuedDzeta s M (fun _ => 1) k a = continuedHzeta (s + k) a := by
  simp [continuedDzeta]

/-- The deformed continued ladder is holomorphic on the upper half-plane. -/
theorem continuedDzeta_differentiableOn (s : ℂ) (M : ℕ)
    (c : Fin (M + 1) → ℂ) (k : ℕ) :
    DifferentiableOn ℂ (continuedDzeta s M c k) UHP := by
  apply DifferentiableOn.add
  · exact continuedHzeta_differentiableOn (s + k)
  · apply DifferentiableOn.fun_sum
    intro n _
    apply DifferentiableOn.const_mul
    intro a ha
    exact (term_differentiableAt ha (n : ℕ) (-(s + (k : ℂ)))).differentiableWithinAt

/-- The periodic regular part of the continued rung at the branch point `-n`. -/
def continuedRegular (s : ℂ) (k n : ℕ) (z : ℂ) : ℂ :=
  let p : ℂ := s + k
  let K := regularizationOrder p
  let a : ℂ := -(n : ℂ) + Complex.exp z
  (∑ m ∈ Finset.range n,
      (dcorr s k n m (Complex.exp z) - taylorPoly K p a m))
    - taylorPoly K p a n
    + (∑' r : ℕ, remainder K p a (n + 1 + r))
    + restoration K p a

/-- The local continued model: one nonperiodic singular exponential plus a periodic regular part
and the finitely deformed branch coordinates. -/
def continuedDmodel (s : ℂ) (M : ℕ) (c : Fin (M + 1) → ℂ)
    (n : Fin (M + 1)) (k : ℕ) (z : ℂ) : ℂ :=
  c n * Complex.exp (-(s + k) * z) + continuedRegular s k (n : ℕ) z +
    ∑ n' : Fin (M + 1),
      (c n' - 1) * dcorr s k (n : ℕ) (n' : ℕ) (Complex.exp z)

theorem continuedRegular_exp_periodic (s : ℂ) (k n : ℕ) (z : ℂ) :
    continuedRegular s k n (z + 2 * (Real.pi : ℂ) * Complex.I) =
      continuedRegular s k n z := by
  simp only [continuedRegular, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]

/-- Shifting the logarithmic coordinate changes only the chosen singular coefficient. -/
theorem continuedDmodel_shift (s : ℂ) {M : ℕ} (c : Fin (M + 1) → ℂ)
    (n : Fin (M + 1)) (k : ℕ) (z : ℂ) :
    continuedDmodel s M c n k (z + 2 * (Real.pi : ℂ) * Complex.I) =
      continuedDmodel s M (Function.update c n (monoScalar s * c n)) n k z := by
  rw [continuedDmodel, continuedDmodel, continuedRegular_exp_periodic]
  have hsum : (∑ n' : Fin (M + 1), (c n' - 1) *
        dcorr s k (n : ℕ) (n' : ℕ)
          (Complex.exp (z + 2 * (Real.pi : ℂ) * Complex.I))) =
      ∑ n' : Fin (M + 1),
        (Function.update c n (monoScalar s * c n) n' - 1) *
          dcorr s k (n : ℕ) (n' : ℕ) (Complex.exp z) := by
    refine Finset.sum_congr rfl (fun n' _ => ?_)
    rw [dcorr_exp_periodic]
    by_cases h : n' = n
    · subst h
      rw [dcorr, if_pos rfl, mul_zero, mul_zero]
    · rw [Function.update_of_ne h]
  rw [hsum, Function.update_self]
  have hq : Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (-s)) = monoScalar s := by
    rw [monoScalar]
    congr 1
    ring
  rw [show -(s + (k : ℂ)) * (z + 2 * (Real.pi : ℂ) * Complex.I) =
      2 * (Real.pi : ℂ) * Complex.I * (-s) + (-(s + (k : ℂ)) * z) +
        -(2 * (Real.pi : ℂ) * Complex.I * k) by ring]
  rw [Complex.exp_add, Complex.exp_add, hq]
  have hk : Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * k)) = 1 := by
    convert Complex.exp_int_mul_two_pi_mul_I (-(k : ℤ)) using 1 ; push_cast ; ring
  rw [hk, mul_one]
  ring

/-- Every Taylor-regularized term strictly beyond the selected branch point is holomorphic in the
logarithmic model region. -/
lemma branchTailRemainder_differentiableOn (K : ℕ) (p : ℂ) (n r : ℕ) :
    DifferentiableOn ℂ
      (fun z => remainder K p (-(n : ℂ) + Complex.exp z) (n + 1 + r))
      HurwitzN2BlockAnalytic.region := by
  intro z hz
  let a : ℂ := -(n : ℂ) + Complex.exp z
  let m : ℕ := n + 1 + r
  have hexp : ‖Complex.exp z‖ < 1 / 2 := HurwitzN2BlockAnalytic.exp_mapsTo hz
  have hbaseRe : 0 < ((m : ℂ) + a).re := by
    have hre : |(Complex.exp z).re| ≤ ‖Complex.exp z‖ := Complex.abs_re_le_norm _
    have hlower : -(1 / 2 : ℝ) < (Complex.exp z).re := by
      have habs := abs_lt.mp (lt_of_le_of_lt hre hexp)
      exact habs.1
    dsimp only [m, a]
    simp only [add_re, natCast_re, neg_re]
    norm_num
    have hr0 : (0 : ℝ) ≤ r := by positivity
    linarith
  have hb : ((m : ℂ) + a) ∈ Complex.slitPlane :=
    Complex.mem_slitPlane_iff.mpr (Or.inl hbaseRe)
  have hraw : DifferentiableAt ℂ
      (fun w => ((m : ℂ) + (-(n : ℂ) + Complex.exp w)) ^ (-p)) z := by
    have haff : DifferentiableAt ℂ
        (fun w => (m : ℂ) + (-(n : ℂ) + Complex.exp w)) z := by fun_prop
    exact ((Complex.hasStrictDerivAt_cpow_const hb).hasDerivAt.differentiableAt).comp z haff
  have htaylor : DifferentiableAt ℂ
      (fun w => taylorPoly K p (-(n : ℂ) + Complex.exp w) m) z := by
    unfold taylorPoly taylorTerm
    fun_prop
  exact (hraw.sub htaylor).differentiableWithinAt

lemma dcorr_exp_differentiableOn (s : ℂ) (k n m : ℕ) :
    DifferentiableOn ℂ (fun z => dcorr s k n m (Complex.exp z))
      HurwitzN2BlockAnalytic.region := by
  by_cases h : m = n
  · refine DifferentiableOn.congr (differentiableOn_const 0) ?_
    intro z _
    simp [dcorr, h]
  · have hcst : DifferentiableOn ℂ
        (fun z : ℂ => ((m : ℂ) - (n : ℂ)) ^ (-(s + (k : ℂ))) *
          (1 + Complex.exp z / ((m : ℂ) - (n : ℂ))) ^ (-(s + (k : ℂ))))
        HurwitzN2BlockAnalytic.region := by
      apply DifferentiableOn.const_mul
      intro z hz
      apply DifferentiableAt.differentiableWithinAt
      have hxlt : ‖Complex.exp z‖ < 1 := by
        have h12 : ‖Complex.exp z‖ < 1 / 2 := HurwitzN2BlockAnalytic.exp_mapsTo hz
        linarith
      have hb : (1 + Complex.exp z / ((m : ℂ) - (n : ℂ))) ∈ Complex.slitPlane :=
        Complex.mem_slitPlane_iff.mpr (Or.inl (tailTerm_base_re_pos h hxlt))
      have haff : DifferentiableAt ℂ
          (fun y : ℂ => 1 + Complex.exp y / ((m : ℂ) - (n : ℂ))) z := by fun_prop
      exact ((hasStrictDerivAt_cpow_const hb).hasDerivAt.differentiableAt).comp z haff
    refine DifferentiableOn.congr hcst ?_
    intro z _
    rw [dcorr, if_neg h]

lemma taylorPoly_branch_differentiableOn (K : ℕ) (p : ℂ) (n m : ℕ) :
    DifferentiableOn ℂ (fun z => taylorPoly K p (-(n : ℂ) + Complex.exp z) m)
      HurwitzN2BlockAnalytic.region := by
  change DifferentiableOn ℂ
    (fun z => ∑ r ∈ Finset.range (K + 1),
      taylorTerm p (-(n : ℂ) + Complex.exp z) r m)
    HurwitzN2BlockAnalytic.region
  apply DifferentiableOn.fun_sum
  intro r _
  unfold taylorTerm
  fun_prop

lemma restoration_branch_differentiableOn (K : ℕ) (p : ℂ) (n : ℕ) :
    DifferentiableOn ℂ (fun z => restoration K p (-(n : ℂ) + Complex.exp z))
      HurwitzN2BlockAnalytic.region := by
  intro z _
  have ha : DifferentiableAt ℂ (fun w => -(n : ℂ) + Complex.exp w) z := by fun_prop
  simpa only [Function.comp_apply] using!
    ((restoration_differentiable K p).differentiableAt.comp z ha).differentiableWithinAt

/-- The infinite regularized tail in the branch model is holomorphic on the full logarithmic
half-plane. -/
lemma continuedRegularTail_differentiableOn (s : ℂ) (k n : ℕ) :
    DifferentiableOn ℂ
      (fun z => ∑' r : ℕ,
        remainder (regularizationOrder (s + k)) (s + k)
          (-(n : ℂ) + Complex.exp z) (n + 1 + r))
      HurwitzN2BlockAnalytic.region := by
  let p : ℂ := s + k
  let K := regularizationOrder p
  let B : ℝ := n + 2
  have hB : 0 < B := by dsimp [B]; positivity
  obtain ⟨R, hR⟩ := exists_nat_gt (2 * B)
  obtain ⟨C, hC0, hC⟩ := exists_binomial_remainder_bound K p
  have hpK : 1 < (p + (K + 1 : ℕ)).re := by
    have h := regularizationOrder_adequate p
    rw [Complex.add_re, Complex.natCast_re]
    norm_num at h ⊢
    linarith
  let m : ℕ → ℕ := fun r => n + 1 + (r + R)
  let u : ℕ → ℝ := fun r => C * B ^ (K + 1) *
    ‖(((m r + 1 : ℕ) : ℂ) ^ (-(p + (K + 1 : ℕ))))‖
  have hbase : Summable (fun q : ℕ =>
      (((q + 1 : ℕ) : ℂ) ^ (-(p + (K + 1 : ℕ))))) := by
    simpa [add_comm] using HurwitzZetaShift.summable_hurwitzSeries hpK 1
  have hbaseShift : Summable (fun r : ℕ =>
      (((m r + 1 : ℕ) : ℂ) ^ (-(p + (K + 1 : ℕ))))) := by
    simpa [m, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      (summable_nat_add_iff (n + 1 + R)).mpr hbase
  have hu : Summable u :=
    (summable_norm_iff.mpr hbaseShift).mul_left (C * B ^ (K + 1))
  let F : ℕ → ℂ → ℂ := fun r z =>
    remainder K p (-(n : ℂ) + Complex.exp z) (m r)
  have hFdiff : ∀ r, DifferentiableOn ℂ (F r) HurwitzN2BlockAnalytic.region := by
    intro r
    simpa [F, m, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      branchTailRemainder_differentiableOn K p n (r + R)
  have hFbound : ∀ r z, z ∈ HurwitzN2BlockAnalytic.region → ‖F r z‖ ≤ u r := by
    intro r z hz
    let a : ℂ := -(n : ℂ) + Complex.exp z
    have hexp : ‖Complex.exp z‖ < 1 / 2 := HurwitzN2BlockAnalytic.exp_mapsTo hz
    have haB : ‖a - 1‖ < B := by
      calc
        ‖a - 1‖ = ‖(-(n : ℂ) - 1) + Complex.exp z‖ := by
          dsimp only [a]
          congr 1
          ring
        _ ≤ ‖(-(n : ℂ) - 1)‖ + ‖Complex.exp z‖ := norm_add_le _ _
        _ < B := by
          rw [show (-(n : ℂ) - 1) = -((n + 1 : ℕ) : ℂ) by push_cast; ring,
            norm_neg, Complex.norm_natCast]
          dsimp only [B]
          norm_num
          linarith
    have hden : (2 * B : ℝ) < (m r + 1 : ℕ) := by
      have hmr : (R : ℝ) ≤ (m r + 1 : ℕ) := by
        have hmrNat : R ≤ m r + 1 := by
          dsimp only [m]
          omega
        exact_mod_cast hmrNat
      exact lt_of_lt_of_le hR hmr
    let y : ℂ := (a - 1) / ((m r + 1 : ℕ) : ℂ)
    have hy : ‖y‖ < 1 / 2 := by
      dsimp only [y]
      rw [norm_div, Complex.norm_natCast]
      have hdenpos : (0 : ℝ) < (m r + 1 : ℕ) := by positivity
      apply (div_lt_iff₀ hdenpos).mpr
      linarith
    have hrem : F r z =
        (((m r + 1 : ℕ) : ℂ) ^ (-p)) *
          ((1 + y) ^ (-p) - (binomialSeries ℂ (-p)).partialSum (K + 1) y) := by
      dsimp only [F]
      rw [remainder, term_factor_of_norm_lt_one (m r) (lt_trans hy (by norm_num)),
        taylor_factor]
      dsimp only [y, a]
      ring
    rw [hrem, norm_mul]
    calc
      ‖(((m r + 1 : ℕ) : ℂ) ^ (-p))‖ *
            ‖(1 + y) ^ (-p) - (binomialSeries ℂ (-p)).partialSum (K + 1) y‖
          ≤ ‖(((m r + 1 : ℕ) : ℂ) ^ (-p))‖ * (C * ‖y‖ ^ (K + 1)) :=
            mul_le_mul_of_nonneg_left (hC y hy) (norm_nonneg _)
      _ = C * (‖(((m r + 1 : ℕ) : ℂ) ^ (-p))‖ *
            ‖(a - 1) / ((m r + 1 : ℕ) : ℂ)‖ ^ (K + 1)) := by
          dsimp only [y]
          ring
      _ = C * (‖a - 1‖ ^ (K + 1) *
            ‖(((m r + 1 : ℕ) : ℂ) ^ (-(p + (K + 1 : ℕ))))‖) := by
          rw [majorant_eq]
      _ ≤ C * (B ^ (K + 1) *
            ‖(((m r + 1 : ℕ) : ℂ) ^ (-(p + (K + 1 : ℕ))))‖) := by
          gcongr
      _ = u r := by dsimp only [u]; ring
  have hfarDiff : DifferentiableOn ℂ (fun z => ∑' r : ℕ, F r z)
      HurwitzN2BlockAnalytic.region :=
    Complex.differentiableOn_tsum_of_summable_norm hu hFdiff
      HurwitzN2BlockAnalytic.isOpen_region hFbound
  let f : ℕ → ℂ → ℂ := fun r z =>
    remainder K p (-(n : ℂ) + Complex.exp z) (n + 1 + r)
  have hheadDiff : DifferentiableOn ℂ
      (fun z => ∑ r ∈ Finset.range R, f r z) HurwitzN2BlockAnalytic.region := by
    apply DifferentiableOn.fun_sum
    intro r _
    exact branchTailRemainder_differentiableOn K p n r
  have hsplitDiff : DifferentiableOn ℂ
      (fun z => (∑ r ∈ Finset.range R, f r z) + ∑' r : ℕ, F r z)
      HurwitzN2BlockAnalytic.region := hheadDiff.add hfarDiff
  refine hsplitDiff.congr ?_
  intro z hz
  have hfarSummable : Summable (fun r => F r z) :=
    Summable.of_norm_bounded hu (fun r => hFbound r z hz)
  have hfullSummable : Summable (fun r => f r z) := by
    apply (summable_nat_add_iff R).mp
    simpa [f, F, m, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hfarSummable
  have hsplit := hfullSummable.sum_add_tsum_nat_add R
  simpa [f, F, m, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hsplit.symm

/-- The complete periodic regular part is holomorphic on the logarithmic model region. -/
theorem continuedRegular_differentiableOn (s : ℂ) (k n : ℕ) :
    DifferentiableOn ℂ (continuedRegular s k n) HurwitzN2BlockAnalytic.region := by
  let p : ℂ := s + k
  let K := regularizationOrder p
  let head : ℂ → ℂ := fun z => ∑ m ∈ Finset.range n,
    (dcorr s k n m (Complex.exp z) -
      taylorPoly K p (-(n : ℂ) + Complex.exp z) m)
  have hhead : DifferentiableOn ℂ head HurwitzN2BlockAnalytic.region := by
    apply DifferentiableOn.fun_sum
    intro m _
    exact (dcorr_exp_differentiableOn s k n m).sub
      (taylorPoly_branch_differentiableOn K p n m)
  have hsing := taylorPoly_branch_differentiableOn K p n n
  have htail := continuedRegularTail_differentiableOn s k n
  have hrest := restoration_branch_differentiableOn K p n
  have h := ((hhead.sub hsing).add htail).add hrest
  simpa only [continuedRegular, p, K, head] using! h

/-- The unrestricted local deformation model is holomorphic on the full logarithmic region. -/
theorem continuedDmodel_differentiableOn (s : ℂ) {M : ℕ}
    (c : Fin (M + 1) → ℂ) (n : Fin (M + 1)) (k : ℕ) :
    DifferentiableOn ℂ (continuedDmodel s M c n k) HurwitzN2BlockAnalytic.region := by
  apply DifferentiableOn.add
  apply DifferentiableOn.add
  · have h : DifferentiableOn ℂ (fun z => Complex.exp (-(s + k) * z))
        HurwitzN2BlockAnalytic.region := by fun_prop
    exact h.const_mul _
  · exact continuedRegular_differentiableOn s k (n : ℕ)
  · apply DifferentiableOn.fun_sum
    intro n' _
    exact (dcorr_exp_differentiableOn s k (n : ℕ) (n' : ℕ)).const_mul _

/-- On the upper logarithmic half-strip, the continued Hurwitz carrier is one singular
exponential plus the periodic regular part. -/
theorem continuedHzeta_eq_continuedRegular {s : ℂ} (k n : ℕ) {z : ℂ}
    (h0 : 0 < z.im) (hπ : z.im < Real.pi) :
    continuedHzeta (s + k) (-(n : ℂ) + Complex.exp z) =
      Complex.exp (-(s + k) * z) + continuedRegular s k n z := by
  let p : ℂ := s + k
  let K := regularizationOrder p
  let a : ℂ := -(n : ℂ) + Complex.exp z
  have ha : 0 < a.im := by
    have him : a.im = (Complex.exp z).im := by simp [a]
    rw [him, Complex.exp_im]
    exact mul_pos (Real.exp_pos _) (Real.sin_pos_of_pos_of_lt_pi h0 hπ)
  have hK : 0 < p.re + K := regularizationOrder_adequate p
  have hsum := summable_remainder ha hK
  have hhead : ∑ m ∈ Finset.range (n + 1), remainder K p a m =
      Complex.exp (-p * z) +
        (∑ m ∈ Finset.range n,
          (dcorr s k n m (Complex.exp z) - taylorPoly K p a m)) -
            taylorPoly K p a n := by
    rw [Finset.sum_range_succ]
    have hbefore : ∑ m ∈ Finset.range n, remainder K p a m =
        ∑ m ∈ Finset.range n,
          (dcorr s k n m (Complex.exp z) - taylorPoly K p a m) := by
      apply Finset.sum_congr rfl
      intro m hm
      have hmn : m ≠ n := Nat.ne_of_lt (Finset.mem_range.mp hm)
      rw [remainder, dcorr, if_neg hmn]
      have hxim : 0 < (Complex.exp z).im := by
        rw [Complex.exp_im]
        exact mul_pos (Real.exp_pos _) (Real.sin_pos_of_pos_of_lt_pi h0 hπ)
      have hbase : (m : ℂ) + a = ((m : ℂ) - (n : ℂ)) + Complex.exp z := by
        dsimp only [a]
        ring
      rw [hbase, term_split hxim hmn]
    rw [hbefore, remainder]
    have hbase : (n : ℂ) + a = Complex.exp z := by
      dsimp only [a]
      ring
    rw [hbase, cexp_cpow_strip (by linarith [Real.pi_pos]) hπ.le]
    ring
  rw [continuedHzeta, continuedAt]
  rw [← hsum.sum_add_tsum_nat_add (n + 1), hhead]
  simp only [continuedRegular]
  dsimp only [p, K, a]
  simp only [Nat.add_comm, Nat.add_left_comm]
  ring

/-- **Unrestricted local bridge.**  On the upper logarithmic half-strip, the deformed continued
ladder equals its model, with no convergence-half-plane hypothesis on the exponent. -/
theorem continuedDzeta_eq_continuedDmodel {s : ℂ} {M : ℕ}
    (c : Fin (M + 1) → ℂ) (n : Fin (M + 1)) (k : ℕ) {z : ℂ}
    (h0 : 0 < z.im) (hπ : z.im < Real.pi) :
    continuedDzeta s M c k (-((n : ℕ) : ℂ) + Complex.exp z) =
      continuedDmodel s M c n k z := by
  have hxim : 0 < (Complex.exp z).im := by
    rw [Complex.exp_im]
    exact mul_pos (Real.exp_pos _) (Real.sin_pos_of_pos_of_lt_pi h0 hπ)
  have hterm : ∀ n' : Fin (M + 1),
      (c n' - 1) *
          ((((n' : ℕ) : ℂ) + (-((n : ℕ) : ℂ) + Complex.exp z)) ^ (-(s + k))) =
        (if n' = n then (c n - 1) * Complex.exp (-(s + k) * z) else 0) +
          (c n' - 1) * dcorr s k (n : ℕ) (n' : ℕ) (Complex.exp z) := by
    intro n'
    by_cases h : n' = n
    · subst h
      have hd : dcorr s k (n' : ℕ) (n' : ℕ) (Complex.exp z) = 0 := by
        rw [dcorr, if_pos rfl]
      rw [if_pos rfl, hd, mul_zero, add_zero]
      have hbase : (((n' : ℕ) : ℂ) + (-((n' : ℕ) : ℂ) + Complex.exp z)) =
          Complex.exp z := by ring
      rw [hbase, cexp_cpow_strip (by linarith [Real.pi_pos]) hπ.le]
    · have hne : (n' : ℕ) ≠ (n : ℕ) := fun hh => h (Fin.ext hh)
      rw [dcorr, if_neg hne, if_neg h, zero_add]
      have hbase : (((n' : ℕ) : ℂ) + (-((n : ℕ) : ℂ) + Complex.exp z)) =
          (((n' : ℕ) : ℂ) - ((n : ℕ) : ℂ)) + Complex.exp z := by ring
      rw [hbase, term_split hxim hne]
  calc
    continuedDzeta s M c k (-((n : ℕ) : ℂ) + Complex.exp z) =
        (Complex.exp (-(s + k) * z) + continuedRegular s k (n : ℕ) z) +
          ∑ n' : Fin (M + 1),
            ((if n' = n then (c n - 1) * Complex.exp (-(s + k) * z) else 0) +
              (c n' - 1) * dcorr s k (n : ℕ) (n' : ℕ) (Complex.exp z)) := by
      rw [continuedDzeta, continuedHzeta_eq_continuedRegular k (n : ℕ) h0 hπ]
      congr 1
      exact Finset.sum_congr rfl (fun n' _ => hterm n')
    _ = continuedDmodel s M c n k z := by
      rw [Finset.sum_add_distrib,
        Finset.sum_ite_eq' Finset.univ n
          (fun _ => (c n - 1) * Complex.exp (-(s + k) * z)),
        if_pos (Finset.mem_univ n), continuedDmodel]
      ring

end

end HurwitzLadder
