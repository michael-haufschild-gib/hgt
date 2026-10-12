import GaloisForLFunctions.RHTower.PhotonicLosslessProductPortRH
import GaloisForLFunctions.RHTower.RealRootedPaleyWienerLowFrequencyRH

/-!
# Lossless temporal stacks need to reproduce `Ξ` only on one real window

**Theorem** (`riemannHypothesis_iff_XiC_window_limit_losslessProductPort`). Fix any real interval
`[c − ε, c + ε]` with `ε > 0`. RH holds iff `Ξ` is a uniform limit on that interval of nonzero multiples of finite products of displacement entries of lossless temporal Maxwell
stacks (positive impedances and durations).

**Proof.**
* *Growth.* Each slab matrix has entries bounded by `(1 + κ + 1/κ)e^{τ|k|}`, and a `2 × 2` product
  at most doubles the entry bound. So stack entries have exponential type, hence an order-one
  envelope (`exists_bound_ptrLosslessStack`).
* *Shape.* Products of entries are even, entire, real on `ℝ`, equal to `1` at `0`, and real-rooted.
  So they are Laguerre–Pólya (`OrderOneHadamard.laguerrePolya_of_even_of_realZeros`).
* *Normalization.* If `c_n P_n → Ξ` on the window, the real parts give `(Re c_n) P_n → Ξ`, because
  `P_n` and `Ξ` are real there.
* *Conclusion.* The window rigidity of the Laguerre–Pólya class
  (`IntervalLaguerrePolya.riemannHypothesis_of_laguerrePolya_tendstoUniformlyOn_any`) finishes.
  The converse is the locally uniform equivalence `riemannHypothesis_iff_XiC_limit_losslessProductPort`
  restricted to the window.
-/

open Complex Matrix Set Filter Topology

namespace RHTower.PhotonicWindow

open GaloisForLFunctions.HTGeometry

noncomputable section

theorem norm_cos_le_exp_norm (w : ℂ) : ‖Complex.cos w‖ ≤ Real.exp ‖w‖ := by
  rw [Complex.cos, norm_div, Complex.norm_ofNat]
  have h1 : ‖Complex.exp (w * I)‖ ≤ Real.exp ‖w‖ := by
    refine (Complex.norm_exp_le_exp_norm _).trans ?_
    rw [norm_mul, Complex.norm_I, mul_one]
  have h2 : ‖Complex.exp (-w * I)‖ ≤ Real.exp ‖w‖ := by
    refine (Complex.norm_exp_le_exp_norm _).trans ?_
    rw [norm_mul, Complex.norm_I, mul_one, norm_neg]
  have := norm_add_le (Complex.exp (w * I)) (Complex.exp (-w * I))
  linarith

theorem norm_sin_le_exp_norm (w : ℂ) : ‖Complex.sin w‖ ≤ Real.exp ‖w‖ := by
  rw [Complex.sin, norm_div, norm_mul, Complex.norm_I, mul_one, Complex.norm_ofNat]
  have h1 : ‖Complex.exp (w * I)‖ ≤ Real.exp ‖w‖ := by
    refine (Complex.norm_exp_le_exp_norm _).trans ?_
    rw [norm_mul, Complex.norm_I, mul_one]
  have h2 : ‖Complex.exp (-w * I)‖ ≤ Real.exp ‖w‖ := by
    refine (Complex.norm_exp_le_exp_norm _).trans ?_
    rw [norm_mul, Complex.norm_I, mul_one, norm_neg]
  have := norm_sub_le (Complex.exp (-w * I)) (Complex.exp (w * I))
  linarith

/-- Entry bound for one lossless slab. -/
theorem norm_ptrLosslessSlab_le {κ τ : ℝ} (hκ : 0 < κ) (hτ : 0 ≤ τ) (k : ℂ) (i j : Fin 2) :
    ‖ptrLosslessSlab κ τ k i j‖ ≤ (1 + κ + 1 / κ) * Real.exp (τ * ‖k‖) := by
  have hkτ : ‖k * (τ : ℂ)‖ = τ * ‖k‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hτ, mul_comm]
  have hc := norm_cos_le_exp_norm (k * τ)
  have hs := norm_sin_le_exp_norm (k * τ)
  rw [hkτ] at hc hs
  have hE : 0 ≤ Real.exp (τ * ‖k‖) := (Real.exp_pos _).le
  have hκ' : 0 < 1 / κ := by positivity
  fin_cases i <;> fin_cases j <;>
    simp only [ptrLosslessSlab, Fin.zero_eta, Fin.isValue, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_fin_one, Fin.mk_one, Matrix.cons_val_one,
      Matrix.cons_val_zero, Matrix.empty_val']
  · nlinarith
  · rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hκ, div_eq_mul_one_div]
    nlinarith [mul_le_mul_of_nonneg_right hs hκ'.le]
  · rw [norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hκ]
    nlinarith [mul_le_mul_of_nonneg_left hs hκ.le]
  · nlinarith

/-- **Exponential type of lossless stacks.** -/
theorem exists_bound_ptrLosslessStack (L : List (ℝ × ℝ)) (hL : ∀ x ∈ L, 0 < x.1 ∧ 0 < x.2) :
    ∃ B S : ℝ, 0 ≤ B ∧ 0 ≤ S ∧ ∀ (k : ℂ) (i j : Fin 2),
      ‖ptrLosslessStack L k i j‖ ≤ B * Real.exp (S * ‖k‖) := by
  induction L with
  | nil =>
    refine ⟨1, 0, zero_le_one, le_rfl, fun k i j => ?_⟩
    simp only [ptrLosslessStack, List.map_nil, List.prod_nil, zero_mul, Real.exp_zero, mul_one]
    fin_cases i <;> fin_cases j <;> simp
  | cons x L ih =>
    obtain ⟨B, S, hB, hS, hb⟩ := ih fun y hy => hL y (List.mem_cons_of_mem _ hy)
    obtain ⟨hκ, hτ⟩ := hL x List.mem_cons_self
    refine ⟨2 * (1 + x.1 + 1 / x.1) * B, x.2 + S, by positivity, by linarith, fun k i j => ?_⟩
    have hstack : ptrLosslessStack (x :: L) k = ptrLosslessSlab x.1 x.2 k * ptrLosslessStack L k := by
      simp [ptrLosslessStack]
    rw [hstack, Matrix.mul_apply, Fin.sum_univ_two]
    have e : Real.exp ((x.2 + S) * ‖k‖) = Real.exp (x.2 * ‖k‖) * Real.exp (S * ‖k‖) := by
      rw [← Real.exp_add]; ring_nf
    rw [e]
    have hA := fun l => norm_ptrLosslessSlab_le hκ hτ.le k i l
    have hBb := fun l => hb k l j
    calc ‖ptrLosslessSlab x.1 x.2 k i 0 * ptrLosslessStack L k 0 j +
          ptrLosslessSlab x.1 x.2 k i 1 * ptrLosslessStack L k 1 j‖
        ≤ ‖ptrLosslessSlab x.1 x.2 k i 0‖ * ‖ptrLosslessStack L k 0 j‖ +
          ‖ptrLosslessSlab x.1 x.2 k i 1‖ * ‖ptrLosslessStack L k 1 j‖ := by
          refine (norm_add_le _ _).trans ?_; rw [norm_mul, norm_mul]
      _ ≤ (1 + x.1 + 1 / x.1) * Real.exp (x.2 * ‖k‖) * (B * Real.exp (S * ‖k‖)) +
          (1 + x.1 + 1 / x.1) * Real.exp (x.2 * ‖k‖) * (B * Real.exp (S * ‖k‖)) :=
          add_le_add (mul_le_mul (hA 0) (hBb 0) (norm_nonneg _) (by positivity))
            (mul_le_mul (hA 1) (hBb 1) (norm_nonneg _) (by positivity))
      _ = 2 * (1 + x.1 + 1 / x.1) * B * (Real.exp (x.2 * ‖k‖) * Real.exp (S * ‖k‖)) := by ring

/-- The normalized product of stack entries. -/
def ptrEntryProduct (L : List (List (ℝ × ℝ))) (k : ℂ) : ℂ :=
  (L.map fun l => ptrLosslessStackEntry l k).prod

theorem ptrLosslessStackEntry_zero (l : List (ℝ × ℝ)) : ptrLosslessStackEntry l 0 = 1 := by
  have h : ptrLosslessStack l 0 = 1 := by
    induction l with
    | nil => simp [ptrLosslessStack]
    | cons x l ih =>
      have hs : ptrLosslessSlab x.1 x.2 0 = 1 := by
        ext i j; fin_cases i <;> fin_cases j <;> simp [ptrLosslessSlab]
      simp only [ptrLosslessStack, List.map_cons, List.prod_cons] at ih ⊢
      rw [hs, ih, Matrix.one_mul]
  simp [ptrLosslessStackEntry, h]

theorem ptrEntryProduct_zero (L : List (List (ℝ × ℝ))) : ptrEntryProduct L 0 = 1 := by
  simp [ptrEntryProduct, ptrLosslessStackEntry_zero]

theorem ptrEntryProduct_neg (L : List (List (ℝ × ℝ))) (k : ℂ) :
    ptrEntryProduct L (-k) = ptrEntryProduct L k := by
  simp [ptrEntryProduct, ptrLosslessStackEntry_neg]

theorem ptrEntryProduct_differentiable (L : List (List (ℝ × ℝ))) :
    Differentiable ℂ (ptrEntryProduct L) := by
  have e : ptrEntryProduct L = ptrLosslessProductPort 1 L := by
    funext k; simp [ptrLosslessProductPort, ptrEntryProduct]
  rw [e]
  exact ptrLosslessProductPort_differentiable 1 L

theorem ptrEntryProduct_zero_im_eq_zero {L : List (List (ℝ × ℝ))}
    (hL : ∀ l ∈ L, ∀ x ∈ l, 0 < x.1 ∧ 0 < x.2) {k : ℂ} (hk : ptrEntryProduct L k = 0) :
    k.im = 0 := by
  refine ptrLosslessProductPort_zero_im_eq_zero one_ne_zero hL ?_
  simpa [ptrLosslessProductPort, ptrEntryProduct] using hk

/-- Order-one envelope of a product of stack entries. -/
theorem exists_orderOne_bound_ptrEntryProduct (L : List (List (ℝ × ℝ)))
    (hL : ∀ l ∈ L, ∀ x ∈ l, 0 < x.1 ∧ 0 < x.2) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ k : ℂ,
      ‖ptrEntryProduct L k‖ ≤ Real.exp (K * (1 + ‖k‖) * Real.log (2 + ‖k‖)) := by
  -- exponential type of the product
  have htype : ∃ B S : ℝ, 0 < B ∧ 0 ≤ S ∧ ∀ k : ℂ, ‖ptrEntryProduct L k‖ ≤ B * Real.exp (S * ‖k‖) := by
    induction L with
    | nil => exact ⟨1, 0, one_pos, le_rfl, fun k => by simp [ptrEntryProduct]⟩
    | cons l L ih =>
      obtain ⟨B, S, hB, hS, hb⟩ := ih fun l' hl' => hL l' (List.mem_cons_of_mem _ hl')
      obtain ⟨B₁, S₁, hB₁, hS₁, hb₁⟩ := exists_bound_ptrLosslessStack l (hL l List.mem_cons_self)
      refine ⟨(B₁ + 1) * B, S₁ + S, by positivity, by linarith, fun k => ?_⟩
      have e : ptrEntryProduct (l :: L) k = ptrLosslessStackEntry l k * ptrEntryProduct L k := by
        simp [ptrEntryProduct]
      rw [e, norm_mul, show (S₁ + S) * ‖k‖ = S₁ * ‖k‖ + S * ‖k‖ by ring, Real.exp_add]
      have h1 : ‖ptrLosslessStackEntry l k‖ ≤ (B₁ + 1) * Real.exp (S₁ * ‖k‖) :=
        (hb₁ k 0 0).trans (mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le)
      calc ‖ptrLosslessStackEntry l k‖ * ‖ptrEntryProduct L k‖
          ≤ (B₁ + 1) * Real.exp (S₁ * ‖k‖) * (B * Real.exp (S * ‖k‖)) :=
            mul_le_mul h1 (hb k) (norm_nonneg _) (by positivity)
        _ = (B₁ + 1) * B * (Real.exp (S₁ * ‖k‖) * Real.exp (S * ‖k‖)) := by ring
  obtain ⟨B, S, hB, hS, hb⟩ := htype
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨(|Real.log B| + S) / Real.log 2, by positivity, fun k => (hb k).trans ?_⟩
  have hBe : B * Real.exp (S * ‖k‖) = Real.exp (Real.log B + S * ‖k‖) := by
    rw [Real.exp_add, Real.exp_log hB]
  rw [hBe]
  apply Real.exp_le_exp.mpr
  have hz0 : 0 ≤ ‖k‖ := norm_nonneg k
  have hlog : Real.log 2 ≤ Real.log (2 + ‖k‖) := Real.log_le_log (by norm_num) (by linarith)
  have hcoef : 0 ≤ (|Real.log B| + S) / Real.log 2 := by positivity
  calc Real.log B + S * ‖k‖ ≤ (|Real.log B| + S) * (1 + ‖k‖) := by
        nlinarith [le_abs_self (Real.log B), abs_nonneg (Real.log B)]
    _ = (|Real.log B| + S) / Real.log 2 * (1 + ‖k‖) * Real.log 2 := by field_simp
    _ ≤ (|Real.log B| + S) / Real.log 2 * (1 + ‖k‖) * Real.log (2 + ‖k‖) := by gcongr

/-- Products of lossless stack entries are Laguerre–Pólya. -/
theorem laguerrePolya_ptrEntryProduct (L : List (List (ℝ × ℝ)))
    (hL : ∀ l ∈ L, ∀ x ∈ l, 0 < x.1 ∧ 0 < x.2) :
    GaloisForLFunctions.HTGeometry.LaguerrePolya (ptrEntryProduct L) := by
  obtain ⟨K, hK, hb⟩ := exists_orderOne_bound_ptrEntryProduct L hL
  have hdiff := ptrEntryProduct_differentiable L
  have h0 : ptrEntryProduct L 0 ≠ 0 := by rw [ptrEntryProduct_zero]; exact one_ne_zero
  refine OrderOneHadamard.laguerrePolya_of_even_of_realZeros hK (fun z _ => hdiff.analyticAt z) h0
    (by rw [ptrEntryProduct_zero]; simp)
    (GaloisForLFunctions.analyticOrderAt_ne_top_of_entire hdiff h0) (ptrEntryProduct_neg L) hb
    fun z hz => ptrEntryProduct_zero_im_eq_zero hL hz

/-- **Lossless stacks: one real window decides RH.** -/
theorem riemannHypothesis_iff_XiC_window_limit_losslessProductPort {c₀ ε : ℝ} (hε : 0 < ε) :
    RiemannHypothesis ↔
      ∃ (c : ℕ → ℂ) (L : ℕ → List (List (ℝ × ℝ))),
        (∀ n, c n ≠ 0) ∧ (∀ n, ∀ l ∈ L n, ∀ x ∈ l, 0 < x.1 ∧ 0 < x.2) ∧
        TendstoUniformlyOn (fun n (t : ℝ) => ptrLosslessProductPort (c n) (L n) t)
          (fun t : ℝ => XiC t) atTop (Icc (c₀ - ε) (c₀ + ε)) := by
  constructor
  · intro hRH
    obtain ⟨c, L, hc, hL, hconv⟩ := riemannHypothesis_iff_XiC_limit_losslessProductPort.mp hRH
    refine ⟨c, L, hc, hL, ?_⟩
    have hK : IsCompact ((fun t : ℝ => (t : ℂ)) '' Icc (c₀ - ε) (c₀ + ε)) :=
      isCompact_Icc.image Complex.continuous_ofReal
    have hu := (tendstoLocallyUniformly_iff_forall_isCompact.mp hconv) _ hK
    exact (hu.comp (fun t : ℝ => (t : ℂ))).mono fun t ht => ⟨t, ht, rfl⟩
  · rintro ⟨c, L, -, hL, hconv⟩
    set P : ℕ → ℂ → ℂ := fun n => ptrEntryProduct (L n) with hP
    have hPreal : ∀ n (t : ℝ), (P n t).im = 0 := fun n t =>
      IntervalLaguerrePolya.im_eq_zero_of_laguerrePolya_ofReal
        (laguerrePolya_ptrEntryProduct (L n) (hL n)) t
    have hXreal : ∀ t : ℝ, (XiC t).im = 0 := fun t => by
      rw [XiC_ofReal, Complex.ofReal_im]
    refine IntervalLaguerrePolya.riemannHypothesis_of_laguerrePolya_tendstoUniformlyOn_any
      (F := fun n z => ((c n).re : ℂ) * P n z) (c := c₀)
      (fun n => (laguerrePolya_ptrEntryProduct (L n) (hL n)).const_mul (c n).re) hε ?_
    rw [Metric.tendstoUniformlyOn_iff] at hconv ⊢
    intro δ hδ
    filter_upwards [hconv (δ / 2) (by positivity)] with n hn t ht
    have h1 := hn t ht
    rw [dist_eq_norm] at h1 ⊢
    have hport : ptrLosslessProductPort (c n) (L n) t = c n * P n t := rfl
    rw [hport] at h1
    -- the imaginary part of `c P` is small since `P` and `Ξ` are real on the window
    have hsplit : c n * P n t = ((c n).re : ℂ) * P n t + I * (((c n).im : ℂ) * P n t) := by
      conv_lhs => rw [← Complex.re_add_im (c n)]
      ring
    have hPt : P n t = ((P n t).re : ℂ) := Complex.ext rfl (by rw [Complex.ofReal_im, hPreal])
    have hXt : XiC t = ((XiC t).re : ℂ) := Complex.ext rfl (by rw [Complex.ofReal_im, hXreal])
    have him : ‖((c n).im : ℂ) * P n t‖ ≤ ‖XiC t - c n * P n t‖ := by
      have e : (XiC t - c n * P n t).im = -((c n).im * (P n t).re) := by
        rw [hsplit, hPt, hXt]
        simp
      calc ‖((c n).im : ℂ) * P n t‖ = |(c n).im * (P n t).re| := by
            conv_lhs => rw [hPt]
            rw [← Complex.ofReal_mul, Complex.norm_real, Real.norm_eq_abs]
        _ = |(XiC t - c n * P n t).im| := by rw [e, abs_neg]
        _ ≤ ‖XiC t - c n * P n t‖ := Complex.abs_im_le_norm _
    calc ‖XiC t - ((c n).re : ℂ) * P n t‖
        = ‖(XiC t - c n * P n t) + I * (((c n).im : ℂ) * P n t)‖ := by rw [hsplit]; ring_nf
      _ ≤ ‖XiC t - c n * P n t‖ + ‖((c n).im : ℂ) * P n t‖ := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_mul, Complex.norm_I, one_mul]
      _ < δ := by linarith

end

end RHTower.PhotonicWindow
