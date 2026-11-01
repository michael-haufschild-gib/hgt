import GaloisForLFunctions.ArithmeticHarmonicAnalysis.DifferencedLogarithmicDualFifthDerivative
import GaloisForLFunctions.RHTower.ZetaWeylCorrelationBound
import GaloisForLFunctions.RHTower.Sieve.KthDerivativeTest

/-! # A fifth-derivative bound for the differenced logarithmic dual sum

The stationary-point amplitude is monotone. Finite Abel summation therefore
inserts it into the fifth-derivative test at a cost of twice its maximum.
-/

noncomputable section
open Complex RHTower

namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis

/-- The positive fifth-derivative scale decreases across the reciprocal frequency interval. -/
theorem dualQ_div_four_anti {T h u u' : ℝ} (hT : 0 ≤ T) (hh : 0 ≤ h) (hu : 0 < u)
    (huu : u ≤ u') : dualQ T h u' / u' ^ 4 ≤ dualQ T h u / u ^ 4 := by
  calc dualQ T h u' / u' ^ 4 ≤ dualQ T h u / u' ^ 4 :=
        div_le_div_of_nonneg_right (dualQ_anti hT hh hu huu) (pow_nonneg (hu.le.trans huu) 4)
    _ ≤ dualQ T h u / u ^ 4 :=
      div_le_div_of_nonneg_left (Real.sqrt_nonneg _) (pow_pos hu 4)
        (pow_le_pow_left₀ hu.le huu 4)

/-- The fifth derivative controls the actual weighted dual sum of the differenced phase. -/
theorem norm_dualSum_diffPhase_fifth_le {T hR a b : ℝ} {k : ℕ} (hT : 0 < T) (hh : 0 < hR)
    (ha : hR ≤ a) (hab : a ≤ b)
    (hlam1 : (a + hR / 2) * (a * (a + hR)) ^ 4 ≤ (T * hR) ^ 4) :
    ‖∑ ν ∈ Finset.Ioo ⌊diffPhase1 T hR k a⌋₊ ⌈diffPhase1 T hR k b⌉₊,
        bDualTerm (diffPhase T hR k) (diffPhase2 T hR) (fun ν : ℕ => dualX T hR (k - ν)) ν‖
      ≤ 512 *
          (((⌈diffPhase1 T hR k b⌉₊ - (⌊diffPhase1 T hR k a⌋₊ + 1) : ℕ) : ℝ) *
              ((12 * ((b + hR / 2) * (b * (b + hR)) ^ 4) /
                  ((a + hR / 2) * (a * (a + hR)) ^ 4)) ^ 2 *
                ((a + hR / 2) * (a * (a + hR)) ^ 4 / (T * hR) ^ 4)) ^ (1 / 30 : ℝ)
            + ((⌈diffPhase1 T hR k b⌉₊ - (⌊diffPhase1 T hR k a⌋₊ + 1) : ℕ) : ℝ) ^ (7 / 8 : ℝ) *
                ((a + hR / 2) * (a * (a + hR)) ^ 4 / (T * hR) ^ 4) ^ (-(1 / 16 : ℝ))) *
          (Real.sqrt (2 * T * hR / (b + hR) ^ 3))⁻¹ := by
  classical
  have ha0 : 0 < a := lt_of_lt_of_le hh ha
  have hb0 : 0 < b := lt_of_lt_of_le ha0 hab
  set α := diffPhase1 T hR k a with hαdef
  set β := diffPhase1 T hR k b with hβdef
  have hX0 : 0 < T * hR := mul_pos hT hh
  obtain ⟨u₁, hu₁⟩ : ∃ u, u = T * hR / (b * (b + hR)) := ⟨_, rfl⟩
  obtain ⟨u₂, hu₂⟩ : ∃ u, u = T * hR / (a * (a + hR)) := ⟨_, rfl⟩
  have hu₁0 : 0 < u₁ := by rw [hu₁]; positivity
  have hu₂0 : 0 < u₂ := by rw [hu₂]; positivity
  have hαv : α = k - u₂ := by rw [hu₂]; exact diffPhase1_eq ha0 hh.le
  have hβv : β = k - u₁ := by rw [hu₁]; exact diffPhase1_eq hb0 hh.le
  obtain ⟨lam, hlam⟩ : ∃ l, l = (a + hR / 2) * (a * (a + hR)) ^ 4 / (T * hR) ^ 4 := ⟨_, rfl⟩
  obtain ⟨γ, hγ⟩ : ∃ g, g = 12 * ((b + hR / 2) * (b * (b + hR)) ^ 4)
      / ((a + hR / 2) * (a * (a + hR)) ^ 4) := ⟨_, rfl⟩
  rw [← hlam, ← hγ]
  set A₀ := ⌊α⌋₊ + 1 with hA₀
  set B₀ := ⌈β⌉₊ with hB₀
  obtain ⟨M, hM⟩ : ∃ m : ℝ, m = ((B₀ - A₀ : ℕ) : ℝ) := ⟨_, rfl⟩
  rw [← hM]
  obtain ⟨lam₂, hlam₂⟩ : ∃ l, l = 2 * T * hR / (b + hR) ^ 3 := ⟨_, rfl⟩
  rw [← hlam₂]
  have hlam₂0 : 0 < lam₂ := by rw [hlam₂]; positivity
  have hlam0 : 0 < lam := by rw [hlam]; positivity
  have hlam1' : lam ≤ 1 := by rw [hlam, div_le_one (by positivity)]; exact hlam1
  have hγ0 : 0 ≤ γ := by rw [hγ]; positivity
  have hM0 : 0 ≤ M := by rw [hM]; positivity
  have hRHS0 : 0 ≤ 512 * (M * (γ ^ 2 * lam) ^ (1 / 30 : ℝ) + M ^ (7 / 8 : ℝ) * lam ^ (-(1 / 16 : ℝ)))
      * (Real.sqrt lam₂)⁻¹ := by positivity
  by_cases hne : A₀ < B₀
  swap
  · have hempty : Finset.Ioo ⌊α⌋₊ ⌈β⌉₊ = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro ν hν
      rw [Finset.mem_Ioo] at hν
      omega
    rw [hempty, Finset.sum_empty, norm_zero]
    exact hRHS0
  -- the dual range
  have hB₀pos : 1 ≤ B₀ := by omega
  have hβpos : 0 < β := Nat.ceil_pos.mp (by omega)
  have hrange : ∀ ν : ℝ, (A₀ : ℝ) ≤ ν → ν ≤ ((B₀ - 1 : ℕ) : ℝ) → u₁ < k - ν ∧ k - ν < u₂ := by
    intro ν h1 h2
    have hA : α < A₀ := by rw [hA₀]; push_cast; exact Nat.lt_floor_add_one α
    have hB : ((B₀ - 1 : ℕ) : ℝ) < β := by
      have := Nat.ceil_lt_add_one hβpos.le
      rw [Nat.cast_sub hB₀pos]
      push_cast
      rw [← hB₀] at this
      linarith
    constructor <;> linarith
  have hsmall : ∀ u : ℝ, 0 < u → u ≤ u₂ → hR * u ≤ T := by
    intro u hu hle
    have h1 : hR * u ≤ hR * u₂ := mul_le_mul_of_nonneg_left hle hh.le
    have h2 : hR * u₂ ≤ T := by
      rw [hu₂, mul_div_assoc', div_le_iff₀ (by positivity)]
      have : hR * hR ≤ a * (a + hR) := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left this hT.le]
    linarith
  have hq₂ : dualQ T hR u₂ / u₂ ^ 4 = lam := by
    rw [hu₂, dualQ_endpoint hT hh ha0, hlam]
    field_simp
  have hq₁ : dualQ T hR u₁ / u₁ ^ 4 = γ * lam / 12 := by
    rw [hu₁, dualQ_endpoint hT hh hb0, hγ, hlam]
    field_simp
  -- the fifth-derivative bounds on the dual range
  have hG5 : ∀ ν : ℝ, (A₀ : ℝ) ≤ ν → ν ≤ ((B₀ - 1 : ℕ) : ℝ) →
      lam ≤ differencedDualFifth T hR k ν ∧ differencedDualFifth T hR k ν ≤ γ * lam := by
    intro ν h1 h2
    obtain ⟨hl, hr⟩ := hrange ν h1 h2
    have hu0 : 0 < (k : ℝ) - ν := lt_trans hu₁0 hl
    obtain ⟨b1, b2⟩ := differencedDualFifth_bounds hT hh hu0 (hsmall _ hu0 hr.le)
    constructor
    · rw [← hq₂]
      exact (dualQ_div_four_anti hT.le hh.le hu0 hr.le).trans b1
    · have := dualQ_div_four_anti hT.le hh.le hu₁0 hl.le
      rw [hq₁] at this
      linarith
  have hγ1 : 1 ≤ γ := by
    have h1 := hG5 A₀ le_rfl (by
      have : A₀ ≤ B₀ - 1 := by omega
      exact_mod_cast this)
    have := h1.1.trans h1.2
    by_contra hlt
    push Not at hlt
    nlinarith
  -- the dual terms as weight times phase
  obtain ⟨x, hx⟩ : ∃ x : ℕ → ℝ, x = fun ν : ℕ => dualX T hR (k - ν) := ⟨_, rfl⟩
  rw [← hx]
  obtain ⟨w, hw⟩ : ∃ w : ℕ → ℝ,
      w = fun i => (Real.sqrt (diffPhase2 T hR (x (min i (B₀ - 1)))))⁻¹ := ⟨_, rfl⟩
  obtain ⟨g, hg⟩ : ∃ g : ℕ → ℂ, g = fun ν => Complex.exp
      (((2 * Real.pi * (diffPhase T hR k (x ν) - ν * x ν) : ℝ) : ℂ) * I)
        * Complex.exp (((Real.pi / 4 : ℝ) : ℂ) * I) := ⟨_, rfl⟩
  have hIoo : Finset.Ioo ⌊α⌋₊ ⌈β⌉₊ = Finset.Ico A₀ B₀ := by
    rw [hA₀, hB₀, Finset.Ico_add_one_left_eq_Ioo]
  have hterm : ∀ ν ∈ Finset.Ico A₀ B₀,
      bDualTerm (diffPhase T hR k) (diffPhase2 T hR) x ν = ((w ν : ℝ) : ℂ) * g ν := by
    intro ν hν
    rw [Finset.mem_Ico] at hν
    have hmin : min ν (B₀ - 1) = ν := min_eq_left (by omega)
    rw [hw, hg]
    simp only [bDualTerm, hmin]
    ring
  rw [hIoo, Finset.sum_congr rfl hterm]
  -- `x` is nondecreasing on the range, and lies in `[a, b]`
  have hxmem : ∀ ν : ℕ, A₀ ≤ ν → ν ≤ B₀ - 1 → x ν ∈ Set.Icc a b := by
    intro ν h1 h2
    obtain ⟨hl, hr⟩ := hrange ν (by exact_mod_cast h1) (by exact_mod_cast h2)
    have hu0 : 0 < (k : ℝ) - ν := lt_trans hu₁0 hl
    rw [hx]
    refine dualX_mem_Icc hT hh hu0 ha0.le hb0.le ?_ ?_
    · rw [le_div_iff₀ hu0]
      rw [hu₂, lt_div_iff₀ (by positivity)] at hr
      have := mul_le_mul_of_nonneg_left hr.le (by positivity : (0 : ℝ) ≤ a * (a + hR))
      linarith
    · rw [div_le_iff₀ hu0]
      rw [hu₁, div_lt_iff₀ (by positivity)] at hl
      linarith
  have hxmono : ∀ ν ν' : ℕ, A₀ ≤ ν → ν ≤ ν' → ν' ≤ B₀ - 1 → x ν ≤ x ν' := by
    intro ν ν' h1 h2 h3
    obtain ⟨hl', _⟩ := hrange ν' (by exact_mod_cast h1.trans h2) (by exact_mod_cast h3)
    have hu0 : 0 < (k : ℝ) - ν' := lt_trans hu₁0 hl'
    have hle : (k : ℝ) - ν' ≤ k - ν := by
      have : (ν : ℝ) ≤ ν' := by exact_mod_cast h2
      linarith
    rw [hx]
    simp only [dualX]
    linarith [dualQ_anti hT.le hh.le hu0 hle]
  have hF''pos : ∀ y : ℝ, 0 < y → 0 < diffPhase2 T hR y := fun y hy =>
    lt_of_lt_of_le (by positivity) (diffPhase2_ge hT.le hy hh.le)
  have hwmono : ∀ i, A₀ ≤ i → w i ≤ w (i + 1) := by
    intro i hi
    have hj : A₀ ≤ min i (B₀ - 1) := le_min hi (by omega)
    have hjj : min i (B₀ - 1) ≤ min (i + 1) (B₀ - 1) := min_le_min_right _ (by omega)
    have hj' : min (i + 1) (B₀ - 1) ≤ B₀ - 1 := min_le_right _ _
    have hx1 := hxmem _ hj (min_le_right _ _)
    have hx2 := hxmem _ (hj.trans hjj) hj'
    have hle := hxmono _ _ hj hjj hj'
    have hF := diffPhase2_antitoneOn hT.le hh.le (lt_of_lt_of_le ha0 hx1.1)
      (lt_of_lt_of_le ha0 hx2.1) hle
    rw [hw]
    exact inv_anti₀ (Real.sqrt_pos.mpr (hF''pos _ (lt_of_lt_of_le ha0 hx2.1)))
      (Real.sqrt_le_sqrt hF)
  have hwmax : w (B₀ - 1) ≤ (Real.sqrt lam₂)⁻¹ := by
    have hmin : min (B₀ - 1) (B₀ - 1) = B₀ - 1 := min_self _
    have hxB := hxmem (B₀ - 1) (by omega) le_rfl
    rw [hw]
    simp only [hmin]
    refine inv_anti₀ (Real.sqrt_pos.mpr hlam₂0) (Real.sqrt_le_sqrt ?_)
    have h1 := diffPhase2_ge hT.le (lt_of_lt_of_le ha0 hxB.1) hh.le
    refine le_trans ?_ h1
    rw [hlam₂]
    exact div_le_div_of_nonneg_left (by positivity)
      (pow_pos (by linarith [hxB.1] : 0 < x (B₀ - 1) + hR) 3)
      (pow_le_pow_left₀ (by linarith [hxB.1]) (by linarith [hxB.2]) 3)
  have hw0 : 0 ≤ w A₀ := by rw [hw]; positivity
  -- the partial sums of the phases, by the fifth-derivative test
  obtain ⟨Bd, hBd⟩ : ∃ d, d = 256 * (M * (γ ^ 2 * lam) ^ (1 / 30 : ℝ)
      + M ^ (7 / 8 : ℝ) * lam ^ (-(1 / 16 : ℝ))) := ⟨_, rfl⟩
  have hBd0 : 0 ≤ Bd := by rw [hBd]; positivity
  have hpartial : ∀ k', k' ≤ B₀ - A₀ → ‖∑ i ∈ Finset.Ico A₀ (A₀ + k'), g i‖ ≤ Bd := by
    intro k' hk'
    rcases Nat.eq_zero_or_pos k' with rfl | hk'0
    · simp only [add_zero, Finset.Ico_self, Finset.sum_empty, norm_zero]
      exact hBd0
    rw [Finset.sum_Ico_eq_sum_range, show A₀ + k' - A₀ = k' by omega]
    have hfac : ∑ j ∈ Finset.range k', g (A₀ + j)
        = (∑ j ∈ Finset.range k', Complex.exp
            (((-(2 * Real.pi * dualChain T hR k 0 ((A₀ : ℝ) + j)) : ℝ) : ℂ) * I))
          * Complex.exp (((Real.pi / 4 : ℝ) : ℂ) * I) := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hg, hx]
      simp only [dualChain]
      push_cast
      ring_nf
    rw [hfac, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]
    rw [norm_sum_cexp_neg (Finset.range k')
      (fun j => 2 * Real.pi * dualChain T hR k 0 ((A₀ : ℝ) + j))]
    have hspan : ∀ ν ∈ Set.Icc (A₀ : ℝ) ((A₀ : ℝ) + ((k' - 1 : ℕ) : ℝ)),
        (A₀ : ℝ) ≤ ν ∧ ν ≤ ((B₀ - 1 : ℕ) : ℝ) := by
      intro ν hν
      refine ⟨hν.1, hν.2.trans ?_⟩
      have : A₀ + (k' - 1) ≤ B₀ - 1 := by omega
      exact_mod_cast this
    have h5 := RHTower.Sieve.kth_derivative_test 5 (by norm_num) (fifthDualChain T hR k) (A₀ : ℝ) k' hk'0
      hlam0 hlam1' hγ1
      (fun i hi ν hν => by
        obtain ⟨h1, h2⟩ := hspan ν hν
        obtain ⟨hl, _⟩ := hrange ν h1 h2
        exact hasDerivAt_fifthDualChain hT hh (lt_trans hu₁0 hl) hi)
      (fun ν hν => by obtain ⟨h1, h2⟩ := hspan ν hν; exact (hG5 ν h1 h2).1)
      (fun ν hν => by obtain ⟨h1, h2⟩ := hspan ν hν; exact (hG5 ν h1 h2).2)
    have he1 : (1 / ((2 : ℝ) ^ 5 - 2)) = 1 / 30 := by norm_num
    have he2 : (1 - 4 / (2 : ℝ) ^ 5) = 7 / 8 := by norm_num
    have he3 : (2 / (2 : ℝ) ^ 5) = 1 / 16 := by norm_num
    rw [he1, he2, he3] at h5
    change ‖∑ n ∈ Finset.range k', Complex.exp
        (((2 * Real.pi * dualChain T hR k 0 ((A₀ : ℝ) + n) : ℝ) : ℂ) * I)‖ ≤
      256 * ((k' : ℝ) * (γ ^ 2 * lam) ^ (1 / 30 : ℝ) +
        (k' : ℝ) ^ (7 / 8 : ℝ) * lam ^ (-(1 / 16 : ℝ))) at h5
    refine h5.trans ?_
    have hk'M : (k' : ℝ) ≤ M := by rw [hM]; exact_mod_cast hk'
    rw [hBd]
    gcongr
  have hAbel := RHTower.Sieve.norm_sum_Ico_mul_le_of_bounded_partial_mono hne w g
    hw0 hwmono hpartial
  refine hAbel.trans ?_
  calc 2 * Bd * w (B₀ - 1) ≤ 2 * Bd * (Real.sqrt lam₂)⁻¹ :=
        mul_le_mul_of_nonneg_left hwmax (by positivity)
    _ = _ := by rw [hBd]; ring

end GaloisForLFunctions.ArithmeticHarmonicAnalysis

#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.norm_dualSum_diffPhase_fifth_le
