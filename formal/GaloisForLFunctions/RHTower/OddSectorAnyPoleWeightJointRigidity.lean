import GaloisForLFunctions.RHTower.PolarConeAbelRigidity

/-!
# Joint parity rigidity at every odd pole weight

**Theorem** (`riemannHypothesis_of_weilPositiveOddAt_anyWeight_of_weilPositiveEvenPolar`).  Let real
weights `lam` be Weil-positive on odd tests at some pole weight `β ∈ ℝ`, and on even tests with
`f̂(i/2) = 0`.  Then RH holds and `lam = Λ` on `n ≥ 2`.

For an odd test the pole term is `−2β |f̂(i/2)|²`, so odd positivity at `β` implies odd positivity
at every `β' ≤ β`.  The hypothesis weakens as `β → −∞`, and its limit is positivity on the odd tests
with `f̂(i/2) = 0`.  The theorem holds on the whole odd window `(−∞, 1]`, not only on `[0, 1]`.

**Corollary** (`not_weilPositiveOddAt_of_weilPositive_of_ne`).  Weights that are Weil-positive on
every pole-free test (`f̂(±i/2) = 0`) but differ from `Λ` are Weil-positive on odd tests at no pole
weight.  Polar positivity is the limit `β → −∞` of `WeilPositiveOddAt β ∧ WeilPositiveEvenPolar`,
and a second point of the polar cone can exist only in that limit.

Proof.  Only the far-bump lower bound changes (`farSum_ge_anyWeight`): for every real `β` and
`a ≥ 0`, `S(a) ≥ β (e^a − 2) J² − |β| J² − A₀`, because the pole value of the odd far bump is
`(e^a − 2 + e^{−a}) J²` and `|β e^{−a}| ≤ |β|`.  On a window at `2a ≈ log 2M` one has
`e^a ≤ 4√M`, so the bound costs `O(|β| √M)` per window and `O(|β| M)` per dyadic block of the
negative part, which keeps `Σ |lam(n)| n^{−σ} < ∞` for `σ > 1`.  The Laplace transform of the bound
gives `K(s) F(s) ≥ −|β| J²/s − O(1)`, so `s² F(s) ≥ −O(s)`: no negative double pole.  The Abel
pinning of the even sector then applies unchanged.
-/

open Complex MeasureTheory Filter Topology Set
open scoped Real ComplexConjugate
open Zeta23

noncomputable section

namespace RHTower.OddSector

open ResonatorProfile EvenSector WeilOneSided WeilMeanSquare WeilSpectral WeilPoleWeight

/-- **The far-bump lower bound at any pole weight.**  For every real `β` and `a ≥ 0`,
`S(a) ≥ β (e^a − 2) J² − |β| J² − A₀`. -/
theorem farSum_ge_anyWeight {β : ℝ} {lam : ℕ → ℝ} (h : WeilPositiveOddAt β lam) {a : ℝ}
    (ha : 0 ≤ a) :
    β * (Real.exp a - 2) * farJ ^ 2 - |β| * farJ ^ 2 - farArchConst ≤ farSum lam a := by
  set F := oddFarBump a with hFdef
  set f : ℝ → ℂ := fun u => ((F u : ℝ) : ℂ) with hfdef
  have hf2 : ContDiff ℝ 2 f := contDiff_ofReal_comp (contDiff_oddFarBump a)
  have hfc : HasCompactSupport f := (hasCompactSupport_oddFarBump a).comp_left Complex.ofReal_zero
  have hodd : ∀ x, f (-x) = -f x := fun x => by
    simp only [hfdef, hFdef, oddFarBump_neg]; push_cast; ring
  have hpos := h f hf2 hfc hodd
  rw [re_weilPoleWeightFunctional_eq_add, re_weilFullFunctional_ofReal,
    weilArchRe_weilTest_eq hf2.continuous hfc,
    re_weilPoleTerm_weilTest_of_odd hf2.continuous hfc hodd,
    atomPairing_oddFarBump lam ha] at hpos
  have hpole : ‖paperFT f (I / 2)‖ ^ 2 = ((Real.exp (-a / 2) - Real.exp (a / 2)) * farJ) ^ 2 := by
    rw [hfdef, paperFT_ofRealFun_I_div_two, integral_oddFarBump_mul_exp, Complex.norm_real,
      Real.norm_eq_abs, sq_abs]
  have harch : |1 / (2 * Real.pi) * ∫ r : ℝ, ‖paperFT f r‖ ^ 2 * EF.gammaBracket r| ≤
      2 * farArchConst := by
    have h1 := integral_normSq_mul_abs_gammaBracket_le 2 (f := f) (norm_paperFT_oddFarBump_le a)
    have h2 : |∫ r : ℝ, ‖paperFT f r‖ ^ 2 * EF.gammaBracket r| ≤
        ∫ r : ℝ, ‖paperFT f r‖ ^ 2 * |EF.gammaBracket r| := by
      refine (abs_integral_le_integral_abs).trans (le_of_eq ?_)
      refine integral_congr_ae (Eventually.of_forall fun r => ?_)
      simp only [abs_mul, abs_of_nonneg (sq_nonneg ‖paperFT f r‖)]
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / (2 * Real.pi))]
    unfold farArchConst
    have hpi : 0 < Real.pi := Real.pi_pos
    calc 1 / (2 * Real.pi) * |∫ r : ℝ, ‖paperFT f r‖ ^ 2 * EF.gammaBracket r|
        ≤ 1 / (2 * Real.pi) * (16 / nodeScale 2 *
          ((gammaLogConst + Real.log (nodeScale 2)) * bumpMassConst + bumpLogConst)) :=
          mul_le_mul_of_nonneg_left (h2.trans h1) (by positivity)
      _ = 2 * (1 / (4 * Real.pi) * (16 / nodeScale 2 *
          ((gammaLogConst + Real.log (nodeScale 2)) * bumpMassConst + bumpLogConst))) := by
          field_simp; ring
  have e : (Real.exp (-a / 2) - Real.exp (a / 2)) ^ 2 = Real.exp a - 2 + Real.exp (-a) := by
    have h1 : Real.exp (-a / 2) ^ 2 = Real.exp (-a) := by
      rw [← Real.exp_nat_mul]; push_cast; ring_nf
    have h2 : Real.exp (a / 2) ^ 2 = Real.exp a := by
      rw [← Real.exp_nat_mul]; push_cast; ring_nf
    have h3 : Real.exp (-a / 2) * Real.exp (a / 2) = 1 := by
      rw [← Real.exp_add]; ring_nf; exact Real.exp_zero
    nlinarith
  have hea : Real.exp (-a) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hb : 0 ≤ β * Real.exp (-a) + |β| := by
    have h1 := mul_nonneg (by linarith [neg_abs_le β] : 0 ≤ β + |β|) (Real.exp_pos (-a)).le
    have h2 := mul_nonneg (abs_nonneg β) (by linarith : 0 ≤ 1 - Real.exp (-a))
    nlinarith
  have hJ2 : β * (Real.exp a - 2) * farJ ^ 2 - |β| * farJ ^ 2 ≤ β * ‖paperFT f (I / 2)‖ ^ 2 := by
    rw [hpole, mul_pow, e]
    nlinarith [mul_nonneg (sq_nonneg farJ) hb]
  have hab := abs_le.mp harch
  nlinarith

/-- The exponential of a window position is at most `4√M`. -/
theorem exp_le_four_sqrt_of_window {M : ℕ} (hM : 1 ≤ M) {a : ℝ}
    (ha2 : 2 * a ≤ Real.log (2 * M : ℕ) + Real.log 2 + 1 / 12) :
    Real.exp a ≤ 4 * Real.sqrt M := by
  have hM0 : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hsq : Real.exp a ^ 2 ≤ 16 * M := by
    have e1 : Real.exp a ^ 2 = Real.exp (2 * a) := by
      rw [← Real.exp_nat_mul]; push_cast; ring_nf
    rw [e1]
    have hle := Real.exp_le_exp.mpr ha2
    rw [Real.exp_add, Real.exp_add, Real.exp_log (by positivity), Real.exp_log two_pos] at hle
    have h12 : Real.exp (1 / 12) ≤ 4 := by
      have := Real.exp_one_lt_d9
      have := Real.exp_le_exp.mpr (show (1 : ℝ) / 12 ≤ 1 by norm_num)
      linarith
    push_cast at hle
    nlinarith [Real.exp_pos (1 / 12)]
  have hs := Real.sq_sqrt hM0.le
  have hs0 := Real.sqrt_nonneg (M : ℝ)
  by_contra hc
  push Not at hc
  nlinarith [Real.exp_pos a]

/-- The negative part seen through one window, at any pole weight. -/
theorem odd_window_negPart_le_anyWeight {β : ℝ} {lam : ℕ → ℝ} (h : WeilPositiveOddAt β lam)
    {M : ℕ} (hM : 2 ≤ M) {a : ℝ} (ha1 : Real.log (2 * M : ℕ) ≤ 2 * a)
    (ha2 : 2 * a ≤ Real.log (2 * M : ℕ) + Real.log 2 + 1 / 12) :
    ∑ n ∈ Finset.Ioc (2 * M) (4 * M), max (-lam n) 0 / Real.sqrt n *
        farKernel (Real.log n - 2 * a) ≤
      farMass * (Real.sqrt M)⁻¹ * (21 / 2 * M * (Real.log (8 * M) + oddToeplitzConst + 1)) +
        |farArchConst| + |β| * (4 * Real.sqrt M + 1) * farJ ^ 2 := by
  have hM0 : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hlog2 := Real.log_two_gt_d9
  have h2M : Real.log (2 * M : ℕ) = Real.log 2 + Real.log M := by
    push_cast; exact Real.log_mul (by norm_num) hM0.ne'
  have hlogM : Real.log 2 ≤ Real.log M :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hM)
  have ha0 : Real.log 2 ≤ a := by linarith
  have hexp : 2 ≤ Real.exp a := by
    calc (2 : ℝ) = Real.exp (Real.log 2) := (Real.exp_log two_pos).symm
      _ ≤ Real.exp a := Real.exp_le_exp.mpr ha0
  have hea := exp_le_four_sqrt_of_window (by omega) ha2
  have hge := farSum_ge_anyWeight h (a := a) (by linarith)
  rw [farSum_eq_sum (N := 2 * M) (by omega) ha2, show 4 * (2 * M) = 8 * M by ring] at hge
  have hβ' : -(|β| * (4 * Real.sqrt M + 1) * farJ ^ 2) ≤
      β * (Real.exp a - 2) * farJ ^ 2 - |β| * farJ ^ 2 := by
    have hJ := sq_nonneg farJ
    have hs := Real.sqrt_nonneg (M : ℝ)
    rcases le_or_gt 0 β with hb | hb
    · rw [abs_of_nonneg hb]
      nlinarith [mul_nonneg (mul_nonneg hb (sub_nonneg.mpr hexp)) hJ,
        mul_nonneg (mul_nonneg hb hs) hJ]
    · rw [abs_of_neg hb]
      nlinarith [mul_nonneg (mul_nonneg (neg_nonneg.mpr hb.le)
        (by linarith : 0 ≤ 4 * Real.sqrt M - Real.exp a + 2)) hJ]
  have hpos := odd_window_posPart_le h (M := M) (by omega) ha1
  have hsub : Finset.Ioc (2 * M) (4 * M) ⊆ Finset.Icc 2 (8 * M) := fun n hn => by
    rw [Finset.mem_Ioc] at hn; rw [Finset.mem_Icc]; omega
  have hsplit : ∑ n ∈ Finset.Icc 2 (8 * M), max (-lam n) 0 / Real.sqrt n *
      farKernel (Real.log n - 2 * a) =
      ∑ n ∈ Finset.Icc 2 (8 * M), max (lam n) 0 / Real.sqrt n * farKernel (Real.log n - 2 * a) -
      ∑ n ∈ Finset.Icc 2 (8 * M), lam n / Real.sqrt n * farKernel (Real.log n - 2 * a) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [max_neg_zero_eq]; ring
  have hmono := Finset.sum_le_sum_of_subset_of_nonneg hsub (f := fun n =>
      max (-lam n) 0 / Real.sqrt n * farKernel (Real.log n - 2 * a)) fun n _ _ =>
    mul_nonneg (div_nonneg (le_max_right _ _) (Real.sqrt_nonneg _)) (farKernel_nonneg _)
  linarith [le_abs_self farArchConst]

/-- **The negative part on a dyadic block, at any pole weight.** -/
theorem odd_sum_negPart_Ioc_le_anyWeight {β : ℝ} {lam : ℕ → ℝ} (h : WeilPositiveOddAt β lam)
    {M : ℕ} (hM : 2 ≤ M) :
    ∑ n ∈ Finset.Ioc (2 * M) (4 * M), max (-lam n) 0 ≤
      2 * (((farWindowCount : ℝ) + 1) / (nodeBump 2).rIn) *
        (farMass * (21 / 2 * M * (Real.log (8 * M) + oddToeplitzConst + 1)) +
          Real.sqrt M * |farArchConst| +
          Real.sqrt M * (|β| * (4 * Real.sqrt M + 1) * farJ ^ 2)) := by
  have hr : 0 < (nodeBump 2).rIn := (nodeBump 2).rIn_pos
  have hM0 : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hsM : 0 < Real.sqrt M := Real.sqrt_pos.mpr hM0
  have hln0 : ∀ n, 0 ≤ max (-lam n) 0 := fun n => le_max_right _ _
  set E : ℝ := |β| * (4 * Real.sqrt M + 1) * farJ ^ 2 with hE
  have hcov : (nodeBump 2).rIn * ∑ n ∈ Finset.Ioc (2 * M) (4 * M), max (-lam n) 0 / Real.sqrt n ≤
      ∑ i ∈ Finset.range (farWindowCount + 1), ∑ n ∈ Finset.Ioc (2 * M) (4 * M),
        max (-lam n) 0 / Real.sqrt n * farKernel (Real.log n - 2 * farWindow (2 * M) i) := by
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_le_sum fun n hn => ?_
    obtain ⟨hn1, hn2⟩ := Finset.mem_Ioc.mp hn
    rw [← Finset.mul_sum]
    calc (nodeBump 2).rIn * (max (-lam n) 0 / Real.sqrt n)
        = max (-lam n) 0 / Real.sqrt n * (nodeBump 2).rIn := mul_comm _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left (farWindow_cover (N := 2 * M) (by omega) hn1
          (by omega)) (div_nonneg (hln0 n) (Real.sqrt_nonneg _))
  have hwin : ∀ i ∈ Finset.range (farWindowCount + 1), ∑ n ∈ Finset.Ioc (2 * M) (4 * M),
      max (-lam n) 0 / Real.sqrt n * farKernel (Real.log n - 2 * farWindow (2 * M) i) ≤
        farMass * (Real.sqrt M)⁻¹ * (21 / 2 * M * (Real.log (8 * M) + oddToeplitzConst + 1)) +
          |farArchConst| + E := by
    intro i hi
    obtain ⟨h1, h2⟩ := farWindow_bounds (2 * M) (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))
    exact odd_window_negPart_le_anyWeight h hM h1 h2
  have hsum := Finset.sum_le_sum hwin
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
  have h1 : ∑ n ∈ Finset.Ioc (2 * M) (4 * M), max (-lam n) 0 / Real.sqrt n ≤
      ((farWindowCount : ℝ) + 1) / (nodeBump 2).rIn * (farMass * (Real.sqrt M)⁻¹ *
        (21 / 2 * M * (Real.log (8 * M) + oddToeplitzConst + 1)) + |farArchConst| + E) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hr]
    have := hcov.trans hsum
    push_cast at this
    linarith
  have h2 : ∀ n ∈ Finset.Ioc (2 * M) (4 * M),
      max (-lam n) 0 ≤ 2 * Real.sqrt M * (max (-lam n) 0 / Real.sqrt n) := by
    intro n hn
    obtain ⟨hn1, hn2⟩ := Finset.mem_Ioc.mp hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hsn := Real.sqrt_pos.mpr hn0
    have hle : Real.sqrt n ≤ 2 * Real.sqrt M := by
      have e : Real.sqrt (4 * M) = 2 * Real.sqrt M := by
        rw [Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num,
          Real.sqrt_sq (by norm_num)]
      rw [← e]; exact Real.sqrt_le_sqrt (by exact_mod_cast hn2)
    rw [mul_div_assoc', le_div_iff₀ hsn]
    exact (mul_le_mul_of_nonneg_left hle (hln0 n)).trans_eq (by ring)
  calc ∑ n ∈ Finset.Ioc (2 * M) (4 * M), max (-lam n) 0
      ≤ ∑ n ∈ Finset.Ioc (2 * M) (4 * M), 2 * Real.sqrt M * (max (-lam n) 0 / Real.sqrt n) :=
        Finset.sum_le_sum h2
    _ = 2 * Real.sqrt M * ∑ n ∈ Finset.Ioc (2 * M) (4 * M), max (-lam n) 0 / Real.sqrt n := by
        rw [Finset.mul_sum]
    _ ≤ 2 * Real.sqrt M * (((farWindowCount : ℝ) + 1) / (nodeBump 2).rIn *
        (farMass * (Real.sqrt M)⁻¹ * (21 / 2 * M * (Real.log (8 * M) + oddToeplitzConst + 1)) +
          |farArchConst| + E)) := mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = 2 * (((farWindowCount : ℝ) + 1) / (nodeBump 2).rIn) *
        (farMass * (Real.sqrt M * (Real.sqrt M)⁻¹) *
          (21 / 2 * M * (Real.log (8 * M) + oddToeplitzConst + 1)) +
          Real.sqrt M * |farArchConst| + Real.sqrt M * E) := by ring
    _ = _ := by rw [mul_inv_cancel₀ hsM.ne', mul_one]

/-- The negative part on the dyadic blocks `(2^j, 2^{j+1}]` is `O(2^j (j + 1))` at any pole
weight. -/
theorem odd_sum_negPart_dyadic_le_anyWeight {β : ℝ} {lam : ℕ → ℝ} (h : WeilPositiveOddAt β lam) :
    ∃ B : ℝ, ∀ j : ℕ, 2 ≤ j →
      ∑ n ∈ Finset.Ioc (2 ^ j) (2 ^ (j + 1)), max (-lam n) 0 ≤ B * 2 ^ j * ((j : ℝ) + 1) := by
  have hr : 0 < (nodeBump 2).rIn := (nodeBump 2).rIn_pos
  have hq : 0 ≤ ((farWindowCount : ℝ) + 1) / (nodeBump 2).rIn := by positivity
  have hK0 : 0 ≤ farMass := (farKernel_nonneg 0).trans (farKernel_le 0)
  refine ⟨((farWindowCount : ℝ) + 1) / (nodeBump 2).rIn *
    (21 / 2 * farMass * (3 + |oddToeplitzConst|) + |farArchConst| + 5 * |β| * farJ ^ 2),
    fun j hj => ?_⟩
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  have hM : 2 ≤ 2 ^ k :=
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
  have e1 : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
  have e2 : 2 ^ (k + 1 + 1) = 4 * 2 ^ k := by ring
  rw [e1, e2]
  refine (odd_sum_negPart_Ioc_le_anyWeight h hM).trans ?_
  have hcast : ((2 ^ k : ℕ) : ℝ) = (2 : ℝ) ^ k := by push_cast; ring
  rw [hcast]
  have hX1 : (1 : ℝ) ≤ (2 : ℝ) ^ k := one_le_pow₀ (by norm_num)
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have t1 : Real.log (8 * (2 : ℝ) ^ k) + oddToeplitzConst + 1 ≤
      (3 + |oddToeplitzConst|) * ((k : ℝ) + 2) := by
    have e : Real.log (8 * (2 : ℝ) ^ k) = ((k : ℝ) + 3) * Real.log 2 := by
      rw [show (8 : ℝ) * (2 : ℝ) ^ k = 2 ^ (k + 3) by ring, Real.log_pow]; push_cast; ring
    rw [e]
    have := Real.log_two_lt_d9
    nlinarith [le_abs_self oddToeplitzConst, abs_nonneg oddToeplitzConst]
  have hs0 := Real.sqrt_nonneg ((2 : ℝ) ^ k)
  have hss := Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) ^ k by positivity)
  have t2 : Real.sqrt ((2 : ℝ) ^ k) ≤ (2 : ℝ) ^ k := by
    rw [Real.sqrt_le_left (by positivity)]; nlinarith
  have u1 : farMass * (21 / 2 * (2 : ℝ) ^ k * (Real.log (8 * (2 : ℝ) ^ k) + oddToeplitzConst + 1))
      ≤ farMass * (21 / 2 * (2 : ℝ) ^ k * ((3 + |oddToeplitzConst|) * ((k : ℝ) + 2))) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left t1 (by positivity)) hK0
  have u2 : Real.sqrt ((2 : ℝ) ^ k) * |farArchConst| ≤
      (2 : ℝ) ^ k * ((k : ℝ) + 2) * |farArchConst| :=
    mul_le_mul_of_nonneg_right (t2.trans (le_mul_of_one_le_right (by positivity)
      (by linarith))) (abs_nonneg _)
  have u3 : Real.sqrt ((2 : ℝ) ^ k) * (|β| * (4 * Real.sqrt ((2 : ℝ) ^ k) + 1) * farJ ^ 2) ≤
      (2 : ℝ) ^ k * ((k : ℝ) + 2) * (5 * |β| * farJ ^ 2) := by
    have hc : 0 ≤ |β| * farJ ^ 2 := mul_nonneg (abs_nonneg β) (sq_nonneg farJ)
    have hk : Real.sqrt ((2 : ℝ) ^ k) * (4 * Real.sqrt ((2 : ℝ) ^ k) + 1) ≤
        (2 : ℝ) ^ k * ((k : ℝ) + 2) * 5 := by nlinarith
    calc Real.sqrt ((2 : ℝ) ^ k) * (|β| * (4 * Real.sqrt ((2 : ℝ) ^ k) + 1) * farJ ^ 2)
        = (Real.sqrt ((2 : ℝ) ^ k) * (4 * Real.sqrt ((2 : ℝ) ^ k) + 1)) * (|β| * farJ ^ 2) := by
          ring
      _ ≤ ((2 : ℝ) ^ k * ((k : ℝ) + 2) * 5) * (|β| * farJ ^ 2) :=
          mul_le_mul_of_nonneg_right hk hc
      _ = _ := by ring
  refine (mul_le_mul_of_nonneg_left (add_le_add (add_le_add u1 u2) u3)
    (by positivity : (0 : ℝ) ≤ 2 * (((farWindowCount : ℝ) + 1) / (nodeBump 2).rIn))).trans_eq ?_
  push_cast
  ring

/-- **Odd-positive weights converge absolutely on `Re s > 1`, at any pole weight.** -/
theorem summable_abs_div_rpow_of_weilPositiveOddAt_anyWeight {β : ℝ} {lam : ℕ → ℝ}
    (h : WeilPositiveOddAt β lam) {σ : ℝ} (hσ : 1 < σ) :
    Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ := by
  obtain ⟨B, hB⟩ := odd_sum_negPart_dyadic_le_anyWeight h
  refine summable_div_rpow_of_block (fun n => abs_nonneg (lam n))
    (B := B + 3 / 2 * (2 + |oddToeplitzConst|)) (j₀ := 2) hσ fun j hj => ?_
  have hneg := hB j hj
  have hpos := odd_sum_posPart_Ioc_le h (N := 2 ^ j) Nat.one_le_two_pow
  rw [show 2 * 2 ^ j = 2 ^ (j + 1) by ring] at hpos
  have hsplit : ∑ n ∈ Finset.Ioc (2 ^ j) (2 ^ (j + 1)), |lam n| =
      ∑ n ∈ Finset.Ioc (2 ^ j) (2 ^ (j + 1)), max (lam n) 0 +
      ∑ n ∈ Finset.Ioc (2 ^ j) (2 ^ (j + 1)), max (-lam n) 0 := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun n _ => abs_eq_max_zero_add_max_neg_zero (lam n)
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hlog : Real.log ((2 ^ (j + 1) : ℕ) : ℝ) ≤ (j : ℝ) + 1 := by
    rw [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]
    have := Real.log_two_lt_d9
    push_cast
    nlinarith
  have hcast : ((2 ^ j : ℕ) : ℝ) = (2 : ℝ) ^ j := by push_cast; ring
  rw [hcast] at hpos
  have t : Real.log ((2 ^ (j + 1) : ℕ) : ℝ) + oddToeplitzConst + 1 ≤
      (2 + |oddToeplitzConst|) * ((j : ℝ) + 1) := by
    nlinarith [le_abs_self oddToeplitzConst, abs_nonneg oddToeplitzConst]
  have hpos' := hpos.trans (mul_le_mul_of_nonneg_left t (by positivity))
  rw [hsplit]
  nlinarith

/-- **The Laplace form of the far-bump bound at any pole weight.** -/
theorem farLaplace_lower_anyWeight {β : ℝ} {lam : ℕ → ℝ} (h : WeilPositiveOddAt β lam)
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ) {σ : ℝ} (hσ : 0 < σ) :
    β * farJ ^ 2 / (2 * σ) - ((2 * β + |β|) * farJ ^ 2 + farArchConst) / (1 + 2 * σ) ≤
      farLaplace σ / 2 * oddDirichlet lam σ := by
  obtain ⟨hint, heq⟩ := integral_farSum_mul_exp hsl hσ
  have hzero : ∫ a in Ioi 0, farSum lam a * Real.exp (-(1 + 2 * σ) * a) =
      ∫ a, farSum lam a * Real.exp (-(1 + 2 * σ) * a) :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun a ha => by
      simp only [mem_Ioi, not_lt] at ha
      rw [farSum_eq_zero_of_nonpos lam ha, zero_mul]
  rw [← heq, ← hzero]
  have h1 : IntegrableOn (fun a : ℝ => Real.exp (-(2 * σ) * a)) (Ioi 0) :=
    integrableOn_exp_mul_Ioi (by linarith) 0
  have h2 : IntegrableOn (fun a : ℝ => Real.exp (-(1 + 2 * σ) * a)) (Ioi 0) :=
    integrableOn_exp_mul_Ioi (by linarith) 0
  have hval : ∫ a in Ioi 0, (β * farJ ^ 2 * Real.exp (-(2 * σ) * a) -
      ((2 * β + |β|) * farJ ^ 2 + farArchConst) * Real.exp (-(1 + 2 * σ) * a)) =
      β * farJ ^ 2 / (2 * σ) - ((2 * β + |β|) * farJ ^ 2 + farArchConst) / (1 + 2 * σ) := by
    rw [integral_sub (h1.const_mul _) (h2.const_mul _), integral_const_mul, integral_const_mul,
      integral_exp_mul_Ioi (by linarith), integral_exp_mul_Ioi (by linarith)]
    simp only [mul_zero, Real.exp_zero, neg_div_neg_eq]
    ring
  rw [← hval]
  refine setIntegral_mono_on ((h1.const_mul _).sub (h2.const_mul _)) hint.integrableOn
    measurableSet_Ioi fun a ha => ?_
  have hge := farSum_ge_anyWeight h (le_of_lt (mem_Ioi.mp ha))
  have hw := Real.exp_pos (-(1 + 2 * σ) * a)
  have he : Real.exp (-(2 * σ) * a) = Real.exp a * Real.exp (-(1 + 2 * σ) * a) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [he]
  calc β * farJ ^ 2 * (Real.exp a * Real.exp (-(1 + 2 * σ) * a)) -
        ((2 * β + |β|) * farJ ^ 2 + farArchConst) * Real.exp (-(1 + 2 * σ) * a)
      = (β * (Real.exp a - 2) * farJ ^ 2 - |β| * farJ ^ 2 - farArchConst) *
          Real.exp (-(1 + 2 * σ) * a) := by ring
    _ ≤ farSum lam a * Real.exp (-(1 + 2 * σ) * a) := mul_le_mul_of_nonneg_right hge hw.le

end RHTower.OddSector

namespace RHTower.EvenSector

open OddSector WeilOneSided WeilPoleWeight

/-- **No negative double pole from odd positivity at any pole weight.**  The far bumps give
`K(s) F(s) ≥ −|β| J²/s − 2|D|`, hence `s² F(s) ≥ −2|β| s − 4|D| s²/J²`. -/
theorem eventually_neg_le_of_weilPositiveOddAt_anyWeight {β : ℝ} {lam : ℕ → ℝ}
    (h : WeilPositiveOddAt β lam) :
    ∀ ε > 0, ∀ᶠ s in 𝓝[>] (0 : ℝ), -ε ≤ s * (s * oddDirichlet lam s) := by
  have hsl := fun σ (hσ : 1 < σ) => summable_abs_div_rpow_of_weilPositiveOddAt_anyWeight h hσ
  intro ε hε
  set D := (2 * β + |β|) * farJ ^ 2 + farArchConst with hD
  have hJ2 : 0 < farJ ^ 2 := pow_pos farJ_pos 2
  have hJ0 : farJ ≠ 0 := farJ_pos.ne'
  set c : ℝ := 2 * |β| + 4 * |D| / farJ ^ 2 with hc
  have hc0 : 0 ≤ c := by positivity
  have hδpos : 0 < min 1 (ε / (c + 1)) := lt_min one_pos (by positivity)
  filter_upwards [self_mem_nhdsWithin,
    eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds hδpos)] with s hs hsδ
  have hs' : 0 < s := hs
  have hs1 : s ≤ 1 := (hsδ.trans_le (min_le_left _ _)).le
  have hsε : s < ε / (c + 1) := hsδ.trans_le (min_le_right _ _)
  have hlow := farLaplace_lower_anyWeight h hsl hs'
  have hK : farJ ^ 2 / 2 ≤ farLaplace s := by
    have h1 := farLaplace_ge hs'.le
    rw [farLaplace_zero] at h1
    have h2 : (1 : ℝ) / 2 ≤ Real.exp (-(s / 6)) := by
      have := Real.add_one_le_exp (-(s / 6))
      linarith
    nlinarith
  have hKpos : 0 < farLaplace s := lt_of_lt_of_le (by positivity) hK
  -- `K F ≥ −|β| J²/s − 2|D|`
  have hKF : -(|β| * farJ ^ 2 / s) - 2 * |D| ≤ farLaplace s * oddDirichlet lam s := by
    have h1 : -(|β| * farJ ^ 2 / (2 * s)) ≤ β * farJ ^ 2 / (2 * s) := by
      rw [← neg_div, div_le_div_iff_of_pos_right (by positivity)]
      nlinarith [neg_abs_le β, sq_nonneg farJ]
    have h2 : D / (1 + 2 * s) ≤ |D| := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith [le_abs_self D, abs_nonneg D]
    have e : |β| * farJ ^ 2 / s = 2 * (|β| * farJ ^ 2 / (2 * s)) := by field_simp
    rw [e]
    linarith
  -- hence `F ≥ −2|β|/s − 4|D|/J²`
  have hF : -(2 * |β| / s) - 4 * |D| / farJ ^ 2 ≤ oddDirichlet lam s := by
    rcases le_or_gt 0 (oddDirichlet lam s) with hF0 | hF0
    · have : 0 ≤ 2 * |β| / s + 4 * |D| / farJ ^ 2 := by positivity
      linarith
    · have hmul : farLaplace s * oddDirichlet lam s ≤ farJ ^ 2 / 2 * oddDirichlet lam s :=
        mul_le_mul_of_nonpos_right hK hF0.le
      have h3 : -(|β| * farJ ^ 2 / s) - 2 * |D| ≤ farJ ^ 2 / 2 * oddDirichlet lam s :=
        hKF.trans hmul
      have e : -(2 * |β| / s) - 4 * |D| / farJ ^ 2 =
          (-(|β| * farJ ^ 2 / s) - 2 * |D|) / (farJ ^ 2 / 2) := by
        field_simp; ring
      rw [e, div_le_iff₀ (by positivity)]
      linarith
  have hmul := mul_le_mul_of_nonneg_left hF (mul_nonneg hs'.le hs'.le)
  have e2 : s * s * (-(2 * |β| / s) - 4 * |D| / farJ ^ 2) = -(s * c) + s * (4 * |D| / farJ ^ 2) -
      s * s * (4 * |D| / farJ ^ 2) := by
    rw [hc]; field_simp; ring
  have hsc : s * c ≤ ε := by
    have := (lt_div_iff₀ (by positivity : (0 : ℝ) < c + 1)).mp hsε
    nlinarith
  have hd0 : 0 ≤ 4 * |D| / farJ ^ 2 := by positivity
  have hss : s * s * (4 * |D| / farJ ^ 2) ≤ s * (4 * |D| / farJ ^ 2) :=
    mul_le_mul_of_nonneg_right (by nlinarith) hd0
  rw [e2] at hmul
  nlinarith

/-- **Joint parity rigidity at every odd pole weight.**  Odd positivity at any real pole weight and
even pole-free positivity force RH and `lam = Λ`. -/
theorem riemannHypothesis_of_weilPositiveOddAt_anyWeight_of_weilPositiveEvenPolar {β : ℝ}
    {lam : ℕ → ℝ} (ho : WeilPositiveOddAt β lam) (hpf : WeilPositiveEvenPolar lam) :
    RiemannHypothesis ∧ ∀ n, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n := by
  have hsl := fun σ (hσ : 1 < σ) => summable_abs_div_rpow_of_weilPositiveOddAt_anyWeight ho hσ
  have hup := eventually_le_one_add_of_log_density_le hsl fun _ hε => odd_log_density_le ho hε
  have hdp := eventually_neg_le_of_weilPositiveOddAt_anyWeight ho
  exact weilPositiveEvenAt_one_iff.mp (weilPositiveEvenAt_one_of_real fun _ hg hgc hge =>
    realWeil_nonneg_of_polar hpf hsl hup hdp hg hgc hge)

/-- Polar positivity together with odd positivity at some pole weight forces RH and `lam = Λ`. -/
theorem riemannHypothesis_of_weilPositive_of_weilPositiveOddAt {β : ℝ} {lam : ℕ → ℝ}
    (hW : WeilPositive lam) (ho : WeilPositiveOddAt β lam) :
    RiemannHypothesis ∧ ∀ n, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n :=
  riemannHypothesis_of_weilPositiveOddAt_anyWeight_of_weilPositiveEvenPolar ho
    (weilPositiveEvenPolar_of_weilPositive hW)

/-- **A second point of the polar cone is odd-positive at no pole weight.** -/
theorem not_weilPositiveOddAt_of_weilPositive_of_ne {lam : ℕ → ℝ} (hW : WeilPositive lam)
    {n₀ : ℕ} (hn₀ : 2 ≤ n₀) (hne : lam n₀ ≠ ArithmeticFunction.vonMangoldt n₀) (β : ℝ) :
    ¬ WeilPositiveOddAt β lam := fun ho =>
  hne ((riemannHypothesis_of_weilPositive_of_weilPositiveOddAt hW ho).2 n₀ hn₀)

/-- A second point of the even pole-free cone is odd-positive at no pole weight. -/
theorem not_weilPositiveOddAt_of_weilPositiveEvenPolar_of_ne {lam : ℕ → ℝ}
    (hpf : WeilPositiveEvenPolar lam) {n₀ : ℕ} (hn₀ : 2 ≤ n₀)
    (hne : lam n₀ ≠ ArithmeticFunction.vonMangoldt n₀) (β : ℝ) : ¬ WeilPositiveOddAt β lam :=
  fun ho => hne ((riemannHypothesis_of_weilPositiveOddAt_anyWeight_of_weilPositiveEvenPolar ho
    hpf).2 n₀ hn₀)

end RHTower.EvenSector

end
