import GaloisForLFunctions.RHTower.SuzukiFlatFluxBlockTail

/-!
# From block decay to the weighted `L²` mass

An exponential weight is almost constant on a unit block, so the weighted `L²` mass of a profile is
dominated by the weighted sum of its block masses:

`∫ e^{2δL}‖F(L)‖² dL ≤ Σ_{n ∈ ℤ} e^{2δ(n+1)} ‖F‖²_{L²([n,n+1))}`.

This is the last structural step of the flat-flux theorem: once the blocks decay faster than
`e^{-δ n}`, the right side is a convergent geometric series and the left side is finite, which is
the card's `(21)`.
-/

open MeasureTheory Set
open scoped ENNReal NNReal

noncomputable section

namespace GaloisForLFunctions.RHTower

open GaloisForLFunctions.HTGeometry

variable {X : Type*} [NormedAddCommGroup X]

/-- On a unit block the exponential weight is at most its value at the right endpoint. -/
theorem exp_weight_block_le {δ : ℝ} (hδ : 0 ≤ δ) {n : ℤ} {L : ℝ}
    (hL : L ∈ Ico (n : ℝ) ((n : ℝ) + 1)) :
    ENNReal.ofReal (Real.exp (2 * δ * L))
      ≤ ENNReal.ofReal (Real.exp (2 * δ * ((n : ℝ) + 1))) := by
  refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_)
  have h := hL.2
  nlinarith

/-- **The weighted mass is dominated by the weighted block sum.** -/
theorem lintegral_weighted_sq_le_blockSum {F : ℝ → X} {δ : ℝ} (hδ : 0 ≤ δ) :
    (∫⁻ L, ENNReal.ofReal (Real.exp (2 * δ * L)) * ‖F L‖ₑ ^ 2)
      ≤ ∑' n : ℤ, ENNReal.ofReal (Real.exp (2 * δ * ((n : ℝ) + 1))) * blockNormSq F n := by
  have hcover : (⋃ n : ℤ, Ico (n : ℝ) ((n : ℝ) + 1)) = univ := iUnion_Ico_intCast ℝ
  have hdecomp : (∫⁻ L, ENNReal.ofReal (Real.exp (2 * δ * L)) * ‖F L‖ₑ ^ 2)
      = ∑' n : ℤ, ∫⁻ L in Ico (n : ℝ) ((n : ℝ) + 1),
          ENNReal.ofReal (Real.exp (2 * δ * L)) * ‖F L‖ₑ ^ 2 := by
    have h := lintegral_iUnion (μ := (volume : Measure ℝ))
      (fun n : ℤ => measurableSet_Ico) pairwise_disjoint_unitBlocks
      (fun L => ENNReal.ofReal (Real.exp (2 * δ * L)) * ‖F L‖ₑ ^ 2)
    rw [hcover, Measure.restrict_univ] at h
    exact h
  rw [hdecomp]
  refine ENNReal.tsum_le_tsum fun n => ?_
  calc (∫⁻ L in Ico (n : ℝ) ((n : ℝ) + 1),
          ENNReal.ofReal (Real.exp (2 * δ * L)) * ‖F L‖ₑ ^ 2)
      ≤ ∫⁻ L in Ico (n : ℝ) ((n : ℝ) + 1),
          ENNReal.ofReal (Real.exp (2 * δ * ((n : ℝ) + 1))) * ‖F L‖ₑ ^ 2 :=
        setLIntegral_mono' measurableSet_Ico fun L hL =>
          mul_le_mul' (exp_weight_block_le hδ hL) le_rfl
    _ = ENNReal.ofReal (Real.exp (2 * δ * ((n : ℝ) + 1))) * blockNormSq F n := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, blockNormSq]

/-- A block-decay bound makes every weighted block term geometric. -/
theorem weighted_blockTerm_le {F : ℝ → X} {δ δ'' C : ℝ} {n : ℤ}
    (hblock : blockNormSq F n ≤ ENNReal.ofReal (C * Real.exp (-2 * δ'' * (n : ℝ)))) :
    ENNReal.ofReal (Real.exp (2 * δ * ((n : ℝ) + 1))) * blockNormSq F n
      ≤ ENNReal.ofReal (C * Real.exp (2 * δ) * Real.exp (2 * (δ - δ'') * (n : ℝ))) := by
  refine le_trans (mul_le_mul' le_rfl hblock) (le_of_eq ?_)
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
  congr 1
  rw [show 2 * δ * ((n : ℝ) + 1) = 2 * δ + 2 * δ * (n : ℝ) by ring, Real.exp_add]
  rw [show -2 * δ'' * (n : ℝ) = -(2 * δ'' * (n : ℝ)) by ring]
  rw [show 2 * (δ - δ'') * (n : ℝ) = 2 * δ * (n : ℝ) + -(2 * δ'' * (n : ℝ)) by ring,
    Real.exp_add]
  ring


/-! ## The terminal geometric sum -/

/-- The terminal ray of the lattice is indexed by the naturals. -/
def natEquivIntGe (N : ℤ) : ℕ ≃ {n : ℤ // n ∈ {n : ℤ | N ≤ n}} where
  toFun k := ⟨N + (k : ℤ), by simp only [Set.mem_setOf_eq]; omega⟩
  invFun n := (n.1 - N).toNat
  left_inv k := by simp
  right_inv n := by
    have hn : N ≤ n.1 := n.2
    ext
    simp only
    omega

@[simp] theorem natEquivIntGe_apply (N : ℤ) (k : ℕ) :
    ((natEquivIntGe N k : {n : ℤ // n ∈ {n : ℤ | N ≤ n}}) : ℤ) = N + (k : ℤ) := rfl

/-- Reindexing a lattice sum supported on a terminal ray. -/
theorem tsum_int_eq_tsum_nat_of_support {a : ℤ → ℝ≥0∞} {N : ℤ}
    (hsupp : ∀ n : ℤ, n < N → a n = 0) :
    (∑' n : ℤ, a n) = ∑' k : ℕ, a (N + (k : ℤ)) := by
  classical
  have hsub : Function.support a ⊆ {n : ℤ | N ≤ n} := by
    intro n hn
    by_contra hlt
    exact hn (hsupp n (by simpa using hlt))
  have h1 : (∑' n : {n : ℤ // n ∈ {n : ℤ | N ≤ n}}, a n) = ∑' n : ℤ, a n :=
    tsum_subtype_eq_of_support_subset hsub
  rw [← h1, ← (natEquivIntGe N).tsum_eq
    (fun n : {n : ℤ // n ∈ {n : ℤ | N ≤ n}} => a n)]
  exact tsum_congr fun c => by rw [natEquivIntGe_apply]

/-- A geometric series of extended reals is finite. -/
theorem tsum_geometric_ofReal_ne_top {C r : ℝ} (hC : 0 ≤ C) (hr0 : 0 ≤ r) (hr : r < 1) :
    (∑' k : ℕ, ENNReal.ofReal (C * r ^ k)) ≠ ⊤ := by
  have hsum : Summable (fun k : ℕ => C * r ^ k) :=
    (summable_geometric_of_lt_one hr0 hr).mul_left C
  have hnn : ∀ k : ℕ, 0 ≤ C * r ^ k := fun k => by positivity
  rw [← ENNReal.ofReal_tsum_of_nonneg hnn hsum]
  exact ENNReal.ofReal_ne_top

/-- **`(21)`: the weighted mass is finite.**  A profile carried on a terminal ray whose block
masses decay faster than `e^{−2δ''n}` has finite `e^{2δL}`-weighted `L²` mass for every `δ < δ''`. -/
theorem lintegral_weighted_sq_ne_top {F : ℝ → X} {δ δ'' C : ℝ} {N : ℤ}
    (hδ : 0 ≤ δ) (hlt : δ < δ'') (hC : 0 ≤ C)
    (hsupp : ∀ n : ℤ, n < N → blockNormSq F n = 0)
    (hblock : ∀ n : ℤ, blockNormSq F n ≤ ENNReal.ofReal (C * Real.exp (-2 * δ'' * (n : ℝ)))) :
    (∫⁻ L, ENNReal.ofReal (Real.exp (2 * δ * L)) * ‖F L‖ₑ ^ 2) ≠ ⊤ := by
  classical
  set b : ℤ → ℝ≥0∞ := fun n =>
    if n < N then 0
    else ENNReal.ofReal (C * Real.exp (2 * δ) * Real.exp (2 * (δ - δ'') * (n : ℝ))) with hb
  have hterm : ∀ n : ℤ,
      ENNReal.ofReal (Real.exp (2 * δ * ((n : ℝ) + 1))) * blockNormSq F n ≤ b n := by
    intro n
    by_cases hn : n < N
    · rw [hb]
      simp only [if_pos hn]
      rw [hsupp n hn, mul_zero]
    · rw [hb]
      simp only [if_neg hn]
      exact weighted_blockTerm_le (hblock n)
  have hbsupp : ∀ n : ℤ, n < N → b n = 0 := by
    intro n hn
    rw [hb]
    simp only [if_pos hn]
  have hbsum : (∑' n : ℤ, b n) ≠ ⊤ := by
    rw [tsum_int_eq_tsum_nat_of_support hbsupp]
    have hval : ∀ k : ℕ, b (N + (k : ℤ))
        = ENNReal.ofReal ((C * Real.exp (2 * δ) * Real.exp (2 * (δ - δ'') * (N : ℝ)))
            * (Real.exp (2 * (δ - δ''))) ^ k) := by
      intro k
      have hnk : ¬ (N + (k : ℤ) < N) := by omega
      have hcast : ((N + (k : ℤ) : ℤ) : ℝ) = (N : ℝ) + (k : ℝ) := by push_cast; ring
      have hexp : Real.exp (2 * (δ - δ'') * ((N : ℝ) + (k : ℝ)))
          = Real.exp (2 * (δ - δ'') * (N : ℝ)) * (Real.exp (2 * (δ - δ''))) ^ k := by
        rw [← Real.exp_nat_mul, ← Real.exp_add]
        congr 1
        ring
      rw [hb]
      simp only [if_neg hnk]
      congr 1
      rw [hcast, hexp]
      ring
    rw [tsum_congr hval]
    refine tsum_geometric_ofReal_ne_top ?_ (Real.exp_pos _).le ?_
    · positivity
    · rw [Real.exp_lt_one_iff]
      linarith
  have hfin : (∫⁻ L, ENNReal.ofReal (Real.exp (2 * δ * L)) * ‖F L‖ₑ ^ 2) ≤ ∑' n : ℤ, b n :=
    le_trans (lintegral_weighted_sq_le_blockSum hδ) (ENNReal.tsum_le_tsum hterm)
  exact ne_top_of_le_ne_top hbsum hfin


/-! ## The capstone -/

theorem blockNorm_sq (F : ℝ → X) (n : ℤ) : blockNorm F n ^ 2 = blockNormSq F n := by
  rw [blockNorm, ← ENNReal.rpow_natCast (blockNormSq F n ^ ((1 : ℝ) / 2)) 2, ← ENNReal.rpow_mul]
  norm_num

/-- **`(4)`/`(21)`: the flat primitive flux enters every smaller weighted space.**  A profile
carried on a terminal ray whose block envelope decays at rate `δ''` has finite `e^{2δL}`-weighted
`L²` mass for every `δ < δ''`.  Together with `(11)`, `(13)` and the flat Volterra decay this is
the conclusion of the card: exponentially weighted value and flux. -/
theorem flatFlux_weighted_mass_ne_top {F : ℝ → X} {ν δ δ'' C : ℝ} {N : ℤ}
    (hδ : 0 ≤ δ) (hlt : δ < δ'') (hC : 0 ≤ C)
    (hsupp : ∀ n : ℤ, n < N → blockNormSq F n = 0)
    (hdecay : ∀ n : ℤ, N ≤ n → expEnvelopeZ ν (blockNorm F) n
      ≤ ENNReal.ofReal (Real.sqrt C * Real.exp (-δ'' * (n : ℝ)))) :
    (∫⁻ L, ENNReal.ofReal (Real.exp (2 * δ * L)) * ‖F L‖ₑ ^ 2) ≠ ⊤ := by
  refine lintegral_weighted_sq_ne_top hδ hlt hC hsupp fun n => ?_
  rcases lt_or_ge n N with hn | hn
  · rw [hsupp n hn]
    simp
  · have hle : blockNorm F n ≤ ENNReal.ofReal (Real.sqrt C * Real.exp (-δ'' * (n : ℝ))) :=
      le_trans (le_expEnvelopeZ ν (blockNorm F) n) (hdecay n hn)
    have hsq : blockNormSq F n
        ≤ ENNReal.ofReal (Real.sqrt C * Real.exp (-δ'' * (n : ℝ))) ^ 2 := by
      rw [← blockNorm_sq]
      exact pow_le_pow_left' hle 2
    refine hsq.trans (le_of_eq ?_)
    rw [← ENNReal.ofReal_pow (by positivity)]
    congr 1
    rw [mul_pow, Real.sq_sqrt hC, ← Real.exp_nat_mul]
    congr 2
    push_cast
    ring


/-! ## `(22)`: the weighted mass of the flux derivative -/

theorem ennreal_add_sq_le (a b : ℝ≥0∞) : (a + b) ^ 2 ≤ 4 * (a ^ 2 + b ^ 2) := by
  have h1 : a + b ≤ 2 * max a b := by
    calc a + b ≤ max a b + max a b := add_le_add (le_max_left a b) (le_max_right a b)
      _ = 2 * max a b := by ring
  have h2 : max a b ^ 2 ≤ a ^ 2 + b ^ 2 := by
    rcases max_choice a b with h | h <;> rw [h]
    · exact le_self_add
    · exact le_add_self
  calc (a + b) ^ 2 ≤ (2 * max a b) ^ 2 := pow_le_pow_left' h1 2
    _ = 4 * max a b ^ 2 := by ring
    _ ≤ 4 * (a ^ 2 + b ^ 2) := mul_le_mul' le_rfl h2

/-- **`(22)`: the weighted mass of a difference is finite when both parts are.** -/
theorem lintegral_weighted_sq_sub_ne_top {u v : ℝ → X} {δ : ℝ}
    (hum : Measurable fun x => ‖u x‖ₑ)
    (hu : (∫⁻ L, ENNReal.ofReal (Real.exp (2 * δ * L)) * ‖u L‖ₑ ^ 2) ≠ ⊤)
    (hv : (∫⁻ L, ENNReal.ofReal (Real.exp (2 * δ * L)) * ‖v L‖ₑ ^ 2) ≠ ⊤) :
    (∫⁻ L, ENNReal.ofReal (Real.exp (2 * δ * L)) * ‖u L - v L‖ₑ ^ 2) ≠ ⊤ := by
  have hpt : ∀ L : ℝ, ENNReal.ofReal (Real.exp (2 * δ * L)) * ‖u L - v L‖ₑ ^ 2
      ≤ 4 * (ENNReal.ofReal (Real.exp (2 * δ * L)) * ‖u L‖ₑ ^ 2)
        + 4 * (ENNReal.ofReal (Real.exp (2 * δ * L)) * ‖v L‖ₑ ^ 2) := by
    intro L
    have hnorm : ‖u L - v L‖ₑ ≤ ‖u L‖ₑ + ‖v L‖ₑ := enorm_sub_le
    calc ENNReal.ofReal (Real.exp (2 * δ * L)) * ‖u L - v L‖ₑ ^ 2
        ≤ ENNReal.ofReal (Real.exp (2 * δ * L)) * (‖u L‖ₑ + ‖v L‖ₑ) ^ 2 :=
          mul_le_mul' le_rfl (pow_le_pow_left' hnorm 2)
      _ ≤ ENNReal.ofReal (Real.exp (2 * δ * L)) * (4 * (‖u L‖ₑ ^ 2 + ‖v L‖ₑ ^ 2)) :=
          mul_le_mul' le_rfl (ennreal_add_sq_le _ _)
      _ = 4 * (ENNReal.ofReal (Real.exp (2 * δ * L)) * ‖u L‖ₑ ^ 2)
            + 4 * (ENNReal.ofReal (Real.exp (2 * δ * L)) * ‖v L‖ₑ ^ 2) := by ring
  have hmeas : AEMeasurable
      (fun L : ℝ => 4 * (ENNReal.ofReal (Real.exp (2 * δ * L)) * ‖u L‖ₑ ^ 2))
      (volume : Measure ℝ) := by
    refine Measurable.aemeasurable ?_
    fun_prop
  have hsplit : (∫⁻ L, (4 * (ENNReal.ofReal (Real.exp (2 * δ * L)) * ‖u L‖ₑ ^ 2)
        + 4 * (ENNReal.ofReal (Real.exp (2 * δ * L)) * ‖v L‖ₑ ^ 2)))
      = (∫⁻ L, 4 * (ENNReal.ofReal (Real.exp (2 * δ * L)) * ‖u L‖ₑ ^ 2))
        + ∫⁻ L, 4 * (ENNReal.ofReal (Real.exp (2 * δ * L)) * ‖v L‖ₑ ^ 2) :=
    lintegral_add_left' hmeas _
  have hfin : (∫⁻ L, (4 * (ENNReal.ofReal (Real.exp (2 * δ * L)) * ‖u L‖ₑ ^ 2)
        + 4 * (ENNReal.ofReal (Real.exp (2 * δ * L)) * ‖v L‖ₑ ^ 2))) ≠ ⊤ := by
    rw [hsplit, lintegral_const_mul' _ _ (by norm_num : (4 : ℝ≥0∞) ≠ ⊤),
      lintegral_const_mul' _ _ (by norm_num : (4 : ℝ≥0∞) ≠ ⊤)]
    exact ENNReal.add_ne_top.mpr
      ⟨ENNReal.mul_ne_top (by norm_num) hu, ENNReal.mul_ne_top (by norm_num) hv⟩
  exact ne_top_of_le_ne_top hfin (lintegral_mono hpt)

end GaloisForLFunctions.RHTower
