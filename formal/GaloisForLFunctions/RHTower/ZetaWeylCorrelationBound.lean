import GaloisForLFunctions.RHTower.ZetaDifferencedDualPhase
import GaloisForLFunctions.RHTower.VanDerCorputBProcess
import GaloisForLFunctions.RHTower.Sieve.AbelIcoWeight
import GaloisForLFunctions.RHTower.Sieve.FourthDerivativeTestSharp

/-!
# The dual sum of a Weyl-differenced `ζ` sum

For the differenced phase `F = diffPhase T h k` on `[a, b]`, `h ≤ a ≤ b`, the `B`-process dual sum
`Σ_{α<ν<β} e(F(x_ν) − νx_ν) F″(x_ν)^{−1/2} e^{iπ/4}` (`α = F′(a)`, `β = F′(b)`, `x_ν = x(k − ν)`) is
bounded by monotone Abel summation and the fourth-derivative test (`norm_dualSum_diffPhase_le`):

  `‖dual sum‖ ≤ 28 γ (M λ^{1/14} + M^{3/4} λ^{−1/14}) / √λ₂`,

with `M` the number of dual frequencies, `λ₂ = 2Th/(b + h)³`,
`λ = (a + h/2)(a(a + h))³/(Th)³ ≤ 1`, and `γ = 3(b + h/2)(b(b + h))³ / ((a + h/2)(a(a + h))³)`.

**Proof.**  On the dual range `u = k − ν` runs between `u₁ = Th/(b(b + h))` and `u₂ = Th/(a(a + h))`,
where `q(u₂) = a + h/2` and `q(u₁) = b + h/2`.  The weight `F″(x_ν)^{−1/2}` is nondecreasing in `ν`
(`x_ν` increases, `F″` decreases), so Abel summation costs `2 max weight ≤ 2/√λ₂`.  The fourth
derivative `G₄` of the negated dual phase lies between `q/u³` and `3q/u³`
(`dualChain_four_bounds`), and `q/u³` decreases in `u`; so `λ ≤ G₄ ≤ γλ` on the range.
-/

open Complex

namespace RHTower

noncomputable section

/-- `F″` decreases on `(0, ∞)`. -/
theorem diffPhase2_antitoneOn {T h : ℝ} (hT : 0 ≤ T) (hh : 0 ≤ h) :
    AntitoneOn (diffPhase2 T h) (Set.Ioi 0) := by
  refine antitoneOn_of_hasDerivWithinAt_nonpos (f' := diffPhase3 T h) (convex_Ioi 0)
    (fun x hx => (hasDerivAt_diffPhase2 hx hh).continuousAt.continuousWithinAt)
    (fun x hx => ?_) (fun x hx => ?_)
  · rw [interior_Ioi] at hx
    exact (hasDerivAt_diffPhase2 hx hh).hasDerivWithinAt
  · rw [interior_Ioi] at hx
    have hx' : (0 : ℝ) < x := hx
    simp only [diffPhase3]
    have : ((x + h) ^ 3)⁻¹ ≤ (x ^ 3)⁻¹ :=
      inv_anti₀ (by positivity) (pow_le_pow_left₀ hx'.le (by linarith) 3)
    nlinarith

/-- `q` decreases in `u`. -/
theorem dualQ_anti {T h u u' : ℝ} (hT : 0 ≤ T) (hh : 0 ≤ h) (hu : 0 < u) (huu : u ≤ u') :
    dualQ T h u' ≤ dualQ T h u :=
  Real.sqrt_le_sqrt (by
    have : T * h / u' ≤ T * h / u := div_le_div_of_nonneg_left (by positivity) hu huu
    linarith)

/-- `q/u³` decreases in `u`. -/
theorem dualQ_div_cube_anti {T h u u' : ℝ} (hT : 0 ≤ T) (hh : 0 ≤ h) (hu : 0 < u)
    (huu : u ≤ u') : dualQ T h u' / u' ^ 3 ≤ dualQ T h u / u ^ 3 := by
  have hq := dualQ_anti hT hh hu huu
  have hq0 : 0 ≤ dualQ T h u' := Real.sqrt_nonneg _
  have hu3 : u ^ 3 ≤ u' ^ 3 := pow_le_pow_left₀ hu.le huu 3
  calc dualQ T h u' / u' ^ 3 ≤ dualQ T h u / u' ^ 3 :=
        div_le_div_of_nonneg_right hq (pow_nonneg (hu.le.trans huu) 3)
    _ ≤ dualQ T h u / u ^ 3 := div_le_div_of_nonneg_left (Real.sqrt_nonneg _) (pow_pos hu 3) hu3

/-- At the endpoint frequency `u = Th/(a(a + h))`, `q = a + h/2`. -/
theorem dualQ_endpoint {T h a : ℝ} (hT : 0 < T) (hh : 0 < h) (ha : 0 < a) :
    dualQ T h (T * h / (a * (a + h))) = a + h / 2 := by
  have e : T * h / (T * h / (a * (a + h))) + h ^ 2 / 4 = (a + h / 2) ^ 2 := by
    field_simp; ring
  rw [dualQ, e, Real.sqrt_sq (by linarith)]

/-- `F′(a) = k − Th/(a(a + h))`. -/
theorem diffPhase1_eq {T h k a : ℝ} (ha : 0 < a) (hh : 0 ≤ h) :
    diffPhase1 T h k a = k - T * h / (a * (a + h)) := by
  have hah : 0 < a + h := by linarith
  simp only [diffPhase1]
  field_simp
  ring

/-- `e(−θ)` sums have the norm of `e(θ)` sums. -/
theorem norm_sum_cexp_neg (s : Finset ℕ) (θ : ℕ → ℝ) :
    ‖∑ j ∈ s, Complex.exp (((-θ j : ℝ) : ℂ) * I)‖ = ‖∑ j ∈ s, Complex.exp (((θ j : ℝ) : ℂ) * I)‖ := by
  rw [← Complex.norm_conj, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I]
  congr 1
  push_cast
  ring

/-- **The dual sum of the differenced phase.**  See the module docstring. -/
theorem norm_dualSum_diffPhase_le {T hR a b : ℝ} {k : ℕ} (hT : 0 < T) (hh : 0 < hR)
    (ha : hR ≤ a) (hab : a ≤ b)
    (hlam1 : (a + hR / 2) * (a * (a + hR)) ^ 3 ≤ (T * hR) ^ 3) :
    ‖∑ ν ∈ Finset.Ioo ⌊diffPhase1 T hR k a⌋₊ ⌈diffPhase1 T hR k b⌉₊,
        bDualTerm (diffPhase T hR k) (diffPhase2 T hR) (fun ν : ℕ => dualX T hR (k - ν)) ν‖
      ≤ 28 * (3 * ((b + hR / 2) * (b * (b + hR)) ^ 3) / ((a + hR / 2) * (a * (a + hR)) ^ 3))
          * ((((⌈diffPhase1 T hR k b⌉₊ - (⌊diffPhase1 T hR k a⌋₊ + 1) : ℕ) : ℝ)
              * ((a + hR / 2) * (a * (a + hR)) ^ 3 / (T * hR) ^ 3) ^ (1 / 14 : ℝ)
            + (((⌈diffPhase1 T hR k b⌉₊ - (⌊diffPhase1 T hR k a⌋₊ + 1) : ℕ) : ℝ)) ^ (3 / 4 : ℝ)
              * ((a + hR / 2) * (a * (a + hR)) ^ 3 / (T * hR) ^ 3) ^ (-(1 / 14 : ℝ))))
          * (Real.sqrt (2 * T * hR / (b + hR) ^ 3))⁻¹ := by
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
  obtain ⟨lam, hlam⟩ : ∃ l, l = (a + hR / 2) * (a * (a + hR)) ^ 3 / (T * hR) ^ 3 := ⟨_, rfl⟩
  obtain ⟨γ, hγ⟩ : ∃ g, g = 3 * ((b + hR / 2) * (b * (b + hR)) ^ 3)
      / ((a + hR / 2) * (a * (a + hR)) ^ 3) := ⟨_, rfl⟩
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
  have hRHS0 : 0 ≤ 28 * γ * (M * lam ^ (1 / 14 : ℝ) + M ^ (3 / 4 : ℝ) * lam ^ (-(1 / 14 : ℝ)))
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
  have hq₂ : dualQ T hR u₂ / u₂ ^ 3 = lam := by
    rw [hu₂, dualQ_endpoint hT hh ha0, hlam]
    field_simp
  have hq₁ : dualQ T hR u₁ / u₁ ^ 3 = γ * lam / 3 := by
    rw [hu₁, dualQ_endpoint hT hh hb0, hγ, hlam]
    field_simp
  -- the fourth-derivative bounds on the dual range
  have hG4 : ∀ ν : ℝ, (A₀ : ℝ) ≤ ν → ν ≤ ((B₀ - 1 : ℕ) : ℝ) →
      lam ≤ dualChain T hR k 4 ν ∧ dualChain T hR k 4 ν ≤ γ * lam := by
    intro ν h1 h2
    obtain ⟨hl, hr⟩ := hrange ν h1 h2
    have hu0 : 0 < (k : ℝ) - ν := lt_trans hu₁0 hl
    obtain ⟨b1, b2⟩ := dualChain_four_bounds hT hh hu0 (hsmall _ hu0 hr.le)
    constructor
    · rw [← hq₂]
      exact (dualQ_div_cube_anti hT.le hh.le hu0 hr.le).trans b1
    · have := dualQ_div_cube_anti hT.le hh.le hu₁0 hl.le
      rw [hq₁] at this
      linarith
  have hγ1 : 1 ≤ γ := by
    have h1 := hG4 A₀ le_rfl (by
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
  -- the partial sums of the phases, by the fourth-derivative test
  obtain ⟨Bd, hBd⟩ : ∃ d, d = 14 * γ * (M * lam ^ (1 / 14 : ℝ)
      + M ^ (3 / 4 : ℝ) * lam ^ (-(1 / 14 : ℝ))) := ⟨_, rfl⟩
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
    have h4 := RHTower.Sieve.fourth_derivative_test_sharp (dualChain T hR k) (A₀ : ℝ) k' hk'0
      hlam0 hlam1' hγ1
      (fun i hi ν hν => by
        obtain ⟨h1, h2⟩ := hspan ν hν
        obtain ⟨hl, _⟩ := hrange ν h1 h2
        exact hasDerivAt_dualChain hT hh (lt_trans hu₁0 hl) i hi)
      (fun ν hν => by obtain ⟨h1, h2⟩ := hspan ν hν; exact (hG4 ν h1 h2).1)
      (fun ν hν => by obtain ⟨h1, h2⟩ := hspan ν hν; exact (hG4 ν h1 h2).2)
    refine h4.trans ?_
    have hk'M : (k' : ℝ) ≤ M := by rw [hM]; exact_mod_cast hk'
    rw [hBd]
    gcongr
  have hAbel := RHTower.Sieve.norm_sum_Ico_mul_le_of_bounded_partial_mono hne w g
    hw0 hwmono hpartial
  refine hAbel.trans ?_
  calc 2 * Bd * w (B₀ - 1) ≤ 2 * Bd * (Real.sqrt lam₂)⁻¹ :=
        mul_le_mul_of_nonneg_left hwmax (by positivity)
    _ = _ := by rw [hBd]; ring

/-! ## Power identities -/

theorem log_pos_mul_rpow_eq {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (h : Real.log x = Real.log y) :
    x = y := by
  rw [← Real.exp_log hx, ← Real.exp_log hy, h]

theorem diffLog_id_one {X n : ℝ} (hX : 0 < X) (hn : 0 < n) :
    X / n ^ 2 * (n ^ 7 / X ^ 3) ^ (1 / 14 : ℝ) * (n ^ 3 / X) ^ (1 / 2 : ℝ) = X ^ (2 / 7 : ℝ) := by
  refine log_pos_mul_rpow_eq (by positivity) (by positivity) ?_
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_rpow (by positivity), Real.log_rpow (by positivity), Real.log_rpow hX,
    Real.log_div (by positivity) (by positivity), Real.log_div (by positivity) (by positivity),
    Real.log_div (by positivity) (by positivity), Real.log_pow, Real.log_pow, Real.log_pow,
    Real.log_pow]
  push_cast
  ring

theorem diffLog_id_two {X n : ℝ} (hX : 0 < X) (hn : 0 < n) :
    (X / n ^ 2) ^ (3 / 4 : ℝ) * (X ^ 3 / n ^ 7) ^ (1 / 14 : ℝ) * (n ^ 3 / X) ^ (1 / 2 : ℝ)
      = X ^ (13 / 28 : ℝ) * n ^ (-(1 / 2) : ℝ) := by
  refine log_pos_mul_rpow_eq (by positivity) (by positivity) ?_
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity),
    Real.log_rpow (by positivity), Real.log_rpow (by positivity), Real.log_rpow (by positivity),
    Real.log_rpow hX, Real.log_rpow hn,
    Real.log_div (by positivity) (by positivity), Real.log_div (by positivity) (by positivity),
    Real.log_div (by positivity) (by positivity), Real.log_pow, Real.log_pow, Real.log_pow,
    Real.log_pow]
  push_cast
  ring

theorem diffLog_id_three {X n : ℝ} (hX : 0 < X) (hn : 0 < n) :
    X / n ^ 2 * (X / n ^ 4 * (n ^ (7 / 5 : ℝ) * X ^ (-(2 / 5) : ℝ)) ^ 4)
      = X ^ (2 / 5 : ℝ) * n ^ (-(2 / 5) : ℝ) := by
  refine log_pos_mul_rpow_eq (by positivity) (by positivity) ?_
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_pow, Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity)
      (by positivity),
    Real.log_rpow hX, Real.log_rpow hn, Real.log_rpow hX, Real.log_rpow hn,
    Real.log_div (by positivity) (by positivity), Real.log_div (by positivity) (by positivity),
    Real.log_pow, Real.log_pow]
  push_cast
  ring

theorem diffLog_id_four {X n : ℝ} (hX : 0 < X) (hn : 0 < n) :
    X / n ^ 2 * (n ^ 3 / X / (n ^ (7 / 5 : ℝ) * X ^ (-(2 / 5) : ℝ)))
      = X ^ (2 / 5 : ℝ) * n ^ (-(2 / 5) : ℝ) := by
  refine log_pos_mul_rpow_eq (by positivity) (by positivity) ?_
  rw [Real.log_mul (by positivity) (by positivity), Real.log_div (by positivity) (by positivity),
    Real.log_div (by positivity) (by positivity), Real.log_div (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_rpow hX, Real.log_rpow hn, Real.log_rpow hX, Real.log_rpow hn,
    Real.log_pow, Real.log_pow]
  push_cast
  ring

/-- `c^{p} ≤ c` for `c ≥ 1`, `p ≤ 1`. -/
theorem rpow_le_self_of_le_one {c p : ℝ} (hc : 1 ≤ c) (hp : p ≤ 1) : c ^ p ≤ c := by
  have := Real.rpow_le_rpow_of_exponent_le hc hp
  rwa [Real.rpow_one] at this

/-- `(√ℓ)⁻¹ ≤ (1/c)^{1/2}` for `0 < c ≤ ℓ`. -/
theorem inv_sqrt_le_rpow {l c : ℝ} (hc : 0 < c) (hl : c ≤ l) :
    (Real.sqrt l)⁻¹ ≤ (c⁻¹) ^ (1 / 2 : ℝ) := by
  rw [← Real.sqrt_eq_rpow, ← Real.sqrt_inv]
  exact Real.sqrt_le_sqrt (inv_anti₀ hc hl)

/-- `Σ_{m ∈ (A, A + L]} g m = Σ_{n < L} g(A + 1 + n)`. -/
theorem sum_Ioc_int_eq_sum_range (A : ℤ) (L : ℕ) (g : ℤ → ℂ) :
    ∑ m ∈ Finset.Ioc A (A + L), g m = ∑ n ∈ Finset.range L, g (A + 1 + n) := by
  induction L with
  | zero => simp
  | succ L ih =>
    rw [Finset.sum_range_succ, ← ih, Nat.cast_succ, ← add_assoc,
      ← Finset.insert_Ioc_right_eq_Ioc_add_one (by omega : A ≤ A + L),
      Finset.sum_insert (by simp), add_comm]
    congr 1
    congr 1
    ring

/-! ## The differenced sum in the `B` regime -/

/-- An integer frequency is invisible at integers: `e(Y + j) = e(Y)` for `j ∈ ℕ`. -/
theorem cexp_two_pi_add_nat (Y : ℝ) (j : ℕ) :
    Complex.exp (((2 * Real.pi * (Y + j) : ℝ) : ℂ) * I)
      = Complex.exp (((2 * Real.pi * Y : ℝ) : ℂ) * I) := by
  have e : (((2 * Real.pi * (Y + j) : ℝ) : ℂ) * I)
      = ((2 * Real.pi * Y : ℝ) : ℂ) * I + (j : ℂ) * (2 * Real.pi * I) := by push_cast; ring
  rw [e, Complex.exp_add, Complex.exp_nat_mul_two_pi_mul_I, mul_one]

/-! ### Size bounds on a block `[a, b]`, `a ≥ n/2`, `b ≤ 2n`, `h ≤ n/2` -/

theorem block_aa_ge {n a hR : ℝ} (ha2 : n / 2 ≤ a) (hn : 0 ≤ n) (hR0 : 0 ≤ hR) :
    n ^ 2 / 4 ≤ a * (a + hR) := by
  have h1 : n / 2 * (n / 2) ≤ a * a := mul_le_mul ha2 ha2 (by positivity) (by linarith)
  have h2 : 0 ≤ a * hR := mul_nonneg (by linarith) hR0
  nlinarith

theorem block_aa_le {n a hR : ℝ} (han : a ≤ n) (ha : 0 ≤ a) (hR0 : 0 ≤ hR) (hRn : 2 * hR ≤ n) :
    a * (a + hR) ≤ 3 / 2 * n ^ 2 := by
  have h1 : a + hR ≤ 3 / 2 * n := by linarith
  have := mul_le_mul han h1 (by linarith) (by linarith)
  nlinarith

theorem block_bb_le {n b hR : ℝ} (hbn : b ≤ 2 * n) (hb : 0 ≤ b) (hR0 : 0 ≤ hR)
    (hRn : 2 * hR ≤ n) : b * (b + hR) ≤ 5 * n ^ 2 := by
  have h1 : b + hR ≤ 5 / 2 * n := by linarith
  have := mul_le_mul hbn h1 (by linarith) (by linarith)
  nlinarith

theorem block_gamma_le {n a b hR : ℝ} (hn : 0 < n) (ha2 : n / 2 ≤ a) (hab : a ≤ b)
    (hbn : b ≤ 2 * n) (hR0 : 0 ≤ hR) (hRn : 2 * hR ≤ n) :
    3 * ((b + hR / 2) * (b * (b + hR)) ^ 3) / ((a + hR / 2) * (a * (a + hR)) ^ 3) ≤ 108000 := by
  have ha0 : 0 < a := by linarith
  have haa := block_aa_ge ha2 hn.le hR0
  have hbb := block_bb_le hbn (by linarith) hR0 hRn
  have e2 : (b * (b + hR)) ^ 3 ≤ (5 * n ^ 2) ^ 3 :=
    pow_le_pow_left₀ (mul_nonneg (by linarith) (by linarith)) hbb 3
  have e4 : (n ^ 2 / 4) ^ 3 ≤ (a * (a + hR)) ^ 3 := pow_le_pow_left₀ (by positivity) haa 3
  have hnum : (b + hR / 2) * (b * (b + hR)) ^ 3 ≤ 9 / 4 * n * (5 * n ^ 2) ^ 3 :=
    mul_le_mul (by linarith) e2 (pow_nonneg (mul_nonneg (by linarith) (by linarith)) 3)
      (by positivity)
  have hden : n / 2 * (n ^ 2 / 4) ^ 3 ≤ (a + hR / 2) * (a * (a + hR)) ^ 3 :=
    mul_le_mul (by linarith) e4 (by positivity) (by linarith)
  rw [div_le_iff₀ (lt_of_lt_of_le (by positivity) hden)]
  have e5 : 3 * (9 / 4 * n * (5 * n ^ 2) ^ 3) = 108000 * (n / 2 * (n ^ 2 / 4) ^ 3) := by ring
  nlinarith

theorem block_lam_le {n a hR X : ℝ} (hX : 0 < X) (hn : 0 < n) (ha2 : n / 2 ≤ a) (han : a ≤ n)
    (hRn : 2 * hR ≤ n) (hR0 : 0 ≤ hR) :
    (a + hR / 2) * (a * (a + hR)) ^ 3 / X ^ 3 ≤ 5 * (n ^ 7 / X ^ 3) := by
  rw [mul_div_assoc', div_le_div_iff_of_pos_right (by positivity)]
  have e1 := block_aa_le han (by linarith) hR0 hRn
  have e2 : (a * (a + hR)) ^ 3 ≤ (3 / 2 * n ^ 2) ^ 3 :=
    pow_le_pow_left₀ (mul_nonneg (by linarith) (by linarith)) e1 3
  have e4 : (a + hR / 2) * (a * (a + hR)) ^ 3 ≤ 5 / 4 * n * (3 / 2 * n ^ 2) ^ 3 :=
    mul_le_mul (by linarith) e2 (pow_nonneg (mul_nonneg (by linarith) (by linarith)) 3)
      (by positivity)
  have e5 : 5 / 4 * n * (3 / 2 * n ^ 2) ^ 3 ≤ 5 * n ^ 7 := by
    have : 0 ≤ n ^ 7 := by positivity
    nlinarith
  linarith

theorem block_lam_ge {n a hR X : ℝ} (hX : 0 < X) (hn : 0 < n) (ha2 : n / 2 ≤ a) (hR0 : 0 ≤ hR) :
    1 / 128 * (n ^ 7 / X ^ 3) ≤ (a + hR / 2) * (a * (a + hR)) ^ 3 / X ^ 3 := by
  rw [mul_div_assoc', div_le_div_iff_of_pos_right (by positivity)]
  have haa := block_aa_ge ha2 hn.le hR0
  have e4 : (n ^ 2 / 4) ^ 3 ≤ (a * (a + hR)) ^ 3 := pow_le_pow_left₀ (by positivity) haa 3
  have := mul_le_mul (by linarith : n / 2 ≤ a + hR / 2) e4 (by positivity) (by linarith)
  have e : 1 / 128 * n ^ 7 = n / 2 * (n ^ 2 / 4) ^ 3 := by ring
  linarith

theorem block_lam₂_ge {n b hR X : ℝ} (hX : 0 < X) (hn : 0 < n) (hb : 0 < b) (hbn : b ≤ 2 * n)
    (hR0 : 0 ≤ hR) (hRn : 2 * hR ≤ n) : X / (8 * n ^ 3) ≤ 2 * X / (b + hR) ^ 3 := by
  have hbR : 0 < b + hR := by linarith
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have e2 : (b + hR) ^ 3 ≤ (5 / 2 * n) ^ 3 := pow_le_pow_left₀ hbR.le (by linarith) 3
  have : (5 / 2 * n) ^ 3 ≤ 16 * n ^ 3 := by nlinarith [pow_pos hn 3]
  nlinarith

theorem block_lam₃_le {n a X : ℝ} (hX : 0 < X) (hn : 0 < n) (ha2 : n / 2 ≤ a) :
    6 * X / a ^ 4 ≤ 96 * (X / n ^ 4) := by
  have ha0 : 0 < a := by linarith
  rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
  have e : (n / 2) ^ 4 ≤ a ^ 4 := pow_le_pow_left₀ (by positivity) ha2 4
  nlinarith

theorem block_rho_le {n a b hR : ℝ} (hn : 0 < n) (ha2 : n / 2 ≤ a) (hab : a ≤ b)
    (hbn : b ≤ 2 * n) (hR0 : 0 ≤ hR) (hRn : 2 * hR ≤ n) : ((b + hR) / a) ^ 3 ≤ 125 := by
  have ha0 : 0 < a := by linarith
  have e1 : (b + hR) / a ≤ 5 := by rw [div_le_iff₀ ha0]; linarith
  have e2 := pow_le_pow_left₀ (div_nonneg (by linarith) ha0.le) e1 3
  norm_num at e2 ⊢
  exact e2

/-- **The numerical bookkeeping of the `B` regime.** -/
theorem block_B_numeric {n X γ M lam lam₂ lam₃ ρ K βα : ℝ} (hn : 0 < n) (hX : 0 < X)
    (hXn : n ^ 2 ≤ X) (hγ : γ ≤ 108000) (hM0 : 0 ≤ M) (hM : M ≤ 5 * (X / n ^ 2))
    (hlamlo : 1 / 128 * (n ^ 7 / X ^ 3) ≤ lam) (hlamup : lam ≤ 5 * (n ^ 7 / X ^ 3))
    (hlam₂ : X / (8 * n ^ 3) ≤ lam₂) (hlam₃0 : 0 ≤ lam₃) (hlam₃ : lam₃ ≤ 96 * (X / n ^ 4))
    (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ 125) (hK : K ≤ 11 * (X / n ^ 2))
    (hβα : βα ≤ 5 * (X / n ^ 2)) :
    28 * γ * (M * lam ^ (1 / 14 : ℝ) + M ^ (3 / 4 : ℝ) * lam ^ (-(1 / 14 : ℝ)))
        * (Real.sqrt lam₂)⁻¹
      + (5 + K + 19 / Real.sqrt lam₂ + βα * (3 * lam₃ * (n ^ (7 / 5 : ℝ) * X ^ (-(2 / 5) : ℝ)) ^ 4
          + 3 / (lam₂ * (n ^ (7 / 5 : ℝ) * X ^ (-(2 / 5) : ℝ))) + 2 * ρ))
      ≤ 10 ^ 10 * (X ^ (2 / 7 : ℝ) + X ^ (13 / 28 : ℝ) * n ^ (-(1 / 2) : ℝ) + X / n ^ 2
          + (n ^ 3 / X) ^ (1 / 2 : ℝ) + X ^ (2 / 5 : ℝ) * n ^ (-(2 / 5) : ℝ)) := by
  obtain ⟨δ, hδ⟩ : ∃ d, d = n ^ (7 / 5 : ℝ) * X ^ (-(2 / 5) : ℝ) := ⟨_, rfl⟩
  rw [← hδ]
  have hδ0 : 0 < δ := by rw [hδ]; positivity
  obtain ⟨P1, hP1⟩ : ∃ p, p = X ^ (2 / 7 : ℝ) := ⟨_, rfl⟩
  obtain ⟨P2, hP2⟩ : ∃ p, p = X ^ (13 / 28 : ℝ) * n ^ (-(1 / 2) : ℝ) := ⟨_, rfl⟩
  obtain ⟨P3, hP3⟩ : ∃ p, p = X / n ^ 2 := ⟨_, rfl⟩
  obtain ⟨P4, hP4⟩ : ∃ p, p = (n ^ 3 / X) ^ (1 / 2 : ℝ) := ⟨_, rfl⟩
  obtain ⟨P5, hP5⟩ : ∃ p, p = X ^ (2 / 5 : ℝ) * n ^ (-(2 / 5) : ℝ) := ⟨_, rfl⟩
  rw [← hP1, ← hP2, ← hP3, ← hP4, ← hP5]
  rw [← hP3] at hM hK hβα
  have hP3one : 1 ≤ P3 := by rw [hP3, le_div_iff₀ (by positivity)]; linarith
  have hP1n : 0 ≤ P1 := by rw [hP1]; positivity
  have hP2n : 0 ≤ P2 := by rw [hP2]; positivity
  have hP4n : 0 ≤ P4 := by rw [hP4]; positivity
  have hP5n : 0 ≤ P5 := by rw [hP5]; positivity
  have hlam0 : 0 < lam := lt_of_lt_of_le (by positivity) hlamlo
  have hlam₂0 : 0 < lam₂ := lt_of_lt_of_le (by positivity) hlam₂
  -- the rpow factors
  have hf1 : lam ^ (1 / 14 : ℝ) ≤ 5 * (n ^ 7 / X ^ 3) ^ (1 / 14 : ℝ) := by
    refine (Real.rpow_le_rpow hlam0.le hlamup (by norm_num)).trans ?_
    rw [Real.mul_rpow (by norm_num) (by positivity)]
    exact mul_le_mul_of_nonneg_right (rpow_le_self_of_le_one (by norm_num) (by norm_num))
      (by positivity)
  have hf2 : lam ^ (-(1 / 14 : ℝ)) ≤ 128 * (X ^ 3 / n ^ 7) ^ (1 / 14 : ℝ) := by
    refine (Real.rpow_le_rpow_of_nonpos (by positivity) hlamlo (by norm_num)).trans ?_
    rw [Real.rpow_neg (by positivity), ← Real.inv_rpow (by positivity)]
    have e : (1 / 128 * (n ^ 7 / X ^ 3))⁻¹ = 128 * (X ^ 3 / n ^ 7) := by field_simp
    rw [e, Real.mul_rpow (by norm_num) (by positivity)]
    exact mul_le_mul_of_nonneg_right (rpow_le_self_of_le_one (by norm_num) (by norm_num))
      (by positivity)
  have hf3 : M ^ (3 / 4 : ℝ) ≤ 5 * (X / n ^ 2) ^ (3 / 4 : ℝ) := by
    refine (Real.rpow_le_rpow hM0 hM (by norm_num)).trans ?_
    rw [hP3, Real.mul_rpow (by norm_num) (by positivity)]
    exact mul_le_mul_of_nonneg_right (rpow_le_self_of_le_one (by norm_num) (by norm_num))
      (by positivity)
  have hf4 : (Real.sqrt lam₂)⁻¹ ≤ 3 * P4 := by
    refine (inv_sqrt_le_rpow (by positivity) hlam₂).trans ?_
    have e : (X / (8 * n ^ 3))⁻¹ = 8 * (n ^ 3 / X) := by field_simp
    rw [e, Real.mul_rpow (by norm_num) (by positivity), hP4]
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    rw [← Real.sqrt_eq_rpow, Real.sqrt_le_left (by norm_num)]
    norm_num
  -- the dual part
  have hA1 : M * lam ^ (1 / 14 : ℝ) * (Real.sqrt lam₂)⁻¹
      ≤ 5 * P3 * (5 * (n ^ 7 / X ^ 3) ^ (1 / 14 : ℝ)) * (3 * P4) :=
    mul_le_mul (mul_le_mul hM hf1 (by positivity) (by positivity)) hf4 (by positivity)
      (by positivity)
  have hA2 : M ^ (3 / 4 : ℝ) * lam ^ (-(1 / 14 : ℝ)) * (Real.sqrt lam₂)⁻¹
      ≤ 5 * (X / n ^ 2) ^ (3 / 4 : ℝ) * (128 * (X ^ 3 / n ^ 7) ^ (1 / 14 : ℝ)) * (3 * P4) :=
    mul_le_mul (mul_le_mul hf3 hf2 (by positivity) (by positivity)) hf4 (by positivity)
      (by positivity)
  have hi1 : 5 * P3 * (5 * (n ^ 7 / X ^ 3) ^ (1 / 14 : ℝ)) * (3 * P4) = 75 * P1 := by
    rw [hP1, ← diffLog_id_one hX hn, hP3, hP4]; ring
  have hi2 : 5 * (X / n ^ 2) ^ (3 / 4 : ℝ) * (128 * (X ^ 3 / n ^ 7) ^ (1 / 14 : ℝ)) * (3 * P4)
      = 1920 * P2 := by
    rw [hP2, ← diffLog_id_two hX hn, hP4]; ring
  have hB1 : 0 ≤ M * lam ^ (1 / 14 : ℝ) * (Real.sqrt lam₂)⁻¹ := by positivity
  have hB2 : 0 ≤ M ^ (3 / 4 : ℝ) * lam ^ (-(1 / 14 : ℝ)) * (Real.sqrt lam₂)⁻¹ := by positivity
  have hdual : 28 * γ * (M * lam ^ (1 / 14 : ℝ) + M ^ (3 / 4 : ℝ) * lam ^ (-(1 / 14 : ℝ)))
      * (Real.sqrt lam₂)⁻¹ ≤ 226800000 * P1 + 5806080000 * P2 := by
    have e : 28 * γ * (M * lam ^ (1 / 14 : ℝ) + M ^ (3 / 4 : ℝ) * lam ^ (-(1 / 14 : ℝ)))
        * (Real.sqrt lam₂)⁻¹ = 28 * γ * (M * lam ^ (1 / 14 : ℝ) * (Real.sqrt lam₂)⁻¹
          + M ^ (3 / 4 : ℝ) * lam ^ (-(1 / 14 : ℝ)) * (Real.sqrt lam₂)⁻¹) := by ring
    rw [e]
    have hs := add_le_add (hA1.trans_eq hi1) (hA2.trans_eq hi2)
    have h28 : 28 * γ ≤ 28 * 108000 := by linarith
    calc _ ≤ 28 * 108000 * (75 * P1 + 1920 * P2) :=
          mul_le_mul h28 hs (by positivity) (by norm_num)
      _ = 226800000 * P1 + 5806080000 * P2 := by ring
  -- the error part
  have hδ4 : 3 * lam₃ * δ ^ 4 ≤ 288 * (X / n ^ 4 * δ ^ 4) := by
    have := mul_le_mul_of_nonneg_right hlam₃ (by positivity : (0 : ℝ) ≤ δ ^ 4)
    nlinarith
  have hδ1 : 3 / (lam₂ * δ) ≤ 24 * (n ^ 3 / X / δ) := by
    rw [div_le_iff₀ (by positivity)]
    have h1 : 1 ≤ 8 * n ^ 3 / X * lam₂ := by
      have := mul_le_mul_of_nonneg_left hlam₂ (by positivity : (0 : ℝ) ≤ 8 * n ^ 3 / X)
      have e : 8 * n ^ 3 / X * (X / (8 * n ^ 3)) = 1 := by field_simp
      linarith
    have e : 24 * (n ^ 3 / X / δ) * (lam₂ * δ) = 3 * (8 * n ^ 3 / X * lam₂) := by
      field_simp
      ring
    rw [e]
    linarith
  have hid3 : P3 * (X / n ^ 4 * δ ^ 4) = P5 := by
    rw [hP3, hδ, hP5, diffLog_id_three hX hn]
  have hid4 : P3 * (n ^ 3 / X / δ) = P5 := by
    rw [hP3, hδ, hP5, diffLog_id_four hX hn]
  have h19 : 19 / Real.sqrt lam₂ ≤ 57 * P4 := by rw [div_eq_mul_inv]; linarith
  have hin : 3 * lam₃ * δ ^ 4 + 3 / (lam₂ * δ) + 2 * ρ
      ≤ 288 * (X / n ^ 4 * δ ^ 4) + 24 * (n ^ 3 / X / δ) + 250 := by linarith
  have hprod := mul_le_mul hβα hin (by positivity) (by positivity)
  have e : 5 * P3 * (288 * (X / n ^ 4 * δ ^ 4) + 24 * (n ^ 3 / X / δ) + 250)
      = 1440 * (P3 * (X / n ^ 4 * δ ^ 4)) + 120 * (P3 * (n ^ 3 / X / δ)) + 1250 * P3 := by ring
  rw [e, hid3, hid4] at hprod
  linarith



/-- **The Weyl-differenced `ζ` sum in the `B` regime.**  For `2 ≤ N`, `1 ≤ h ≤ N/2`, `L ≤ N` and
`5N⁷ ≤ X³`, `X = Th`,

  `‖Σ_{n<L} e(T(log(N + n + h) − log(N + n)))‖`
  `  ≤ 10¹⁰ (X^{2/7} + X^{13/28}N^{−1/2} + X/N² + (N³/X)^{1/2} + X^{2/5}N^{−2/5})`.

`B`-process (`norm_sum_sub_bDualSum_le`) on `[N − 1, N + L − 1]` with frequency shift
`k = ⌈X/(a(a + h))⌉`, `a = N − 1`, cut radius `δ = N^{7/5}X^{−2/5}`; dual sum by
`norm_dualSum_diffPhase_le`; constants by `block_B_numeric`. -/
theorem norm_sum_diffLog_le_B {T : ℝ} (hT : 0 < T) {N L h : ℕ} (hN : 2 ≤ N) (hh : 1 ≤ h)
    (h2h : 2 * h ≤ N) (hL : L ≤ N) (hX : 5 * (N : ℝ) ^ 7 ≤ (T * h) ^ 3) :
    ‖∑ n ∈ Finset.range L, Complex.exp (((2 * Real.pi * (T * (Real.log ((N : ℝ) + n + h)
        - Real.log ((N : ℝ) + n))) : ℝ) : ℂ) * I)‖
      ≤ 10 ^ 10 * ((T * h) ^ (2 / 7 : ℝ) + (T * h) ^ (13 / 28 : ℝ) * (N : ℝ) ^ (-(1 / 2) : ℝ)
          + T * h / (N : ℝ) ^ 2 + ((N : ℝ) ^ 3 / (T * h)) ^ (1 / 2 : ℝ)
          + (T * h) ^ (2 / 5 : ℝ) * (N : ℝ) ^ (-(2 / 5) : ℝ)) := by
  classical
  obtain ⟨n, hn⟩ : ∃ n : ℝ, n = N := ⟨_, rfl⟩
  obtain ⟨hR, hhR⟩ : ∃ r : ℝ, r = h := ⟨_, rfl⟩
  rw [← hn, ← hhR]
  rw [← hn, ← hhR] at hX
  have hn2 : 2 ≤ n := by rw [hn]; exact_mod_cast hN
  have hn0 : 0 < n := by linarith
  have hR1 : 1 ≤ hR := by rw [hhR]; exact_mod_cast hh
  have hR0 : 0 < hR := by linarith
  have hRn : 2 * hR ≤ n := by rw [hn, hhR]; exact_mod_cast h2h
  have hLn : (L : ℝ) ≤ n := by rw [hn]; exact_mod_cast hL
  obtain ⟨X, hXd⟩ : ∃ X, X = T * hR := ⟨_, rfl⟩
  rw [← hXd]
  rw [← hXd] at hX
  have hX0 : 0 < X := by rw [hXd]; positivity
  have hXn : n ^ 2 ≤ X := by
    have h6 : (n ^ 2) ^ 3 ≤ X ^ 3 := by
      have : n ^ 6 ≤ 5 * n ^ 7 := by nlinarith [pow_pos hn0 6]
      nlinarith
    exact le_of_pow_le_pow_left₀ (by norm_num) hX0.le h6
  -- the interval and the frequency shift
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = n - 1 := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : ℝ, b = n + L - 1 := ⟨_, rfl⟩
  have ha0 : 0 < a := by rw [ha]; linarith
  have ha2 : n / 2 ≤ a := by rw [ha]; linarith
  have han : a ≤ n := by rw [ha]; linarith
  have hab : a ≤ b := by rw [ha, hb]; linarith [Nat.cast_nonneg (α := ℝ) L]
  have hbn : b ≤ 2 * n := by rw [hb]; linarith
  have hRa : hR ≤ a := by rw [ha]; linarith
  have hb0 : 0 < b := lt_of_lt_of_le ha0 hab
  obtain ⟨k, hk⟩ : ∃ k : ℕ, k = ⌈X / (a * (a + hR))⌉₊ := ⟨_, rfl⟩
  have hk1 : X / (a * (a + hR)) ≤ k := by rw [hk]; exact Nat.le_ceil _
  have hk2 : (k : ℝ) < X / (a * (a + hR)) + 1 := by
    rw [hk]; exact Nat.ceil_lt_add_one (div_nonneg hX0.le (by positivity))
  -- step 4: the bounds of the bookkeeping lemma
  have hαv : diffPhase1 T hR k a = k - X / (a * (a + hR)) := by
    rw [diffPhase1_eq ha0 hR0.le, hXd]
  have hβv : diffPhase1 T hR k b = k - X / (b * (b + hR)) := by
    rw [diffPhase1_eq hb0 hR0.le, hXd]
  have haa := block_aa_ge ha2 hn0.le hR0.le
  have hfreq : X / (a * (a + hR)) ≤ 4 * (X / n ^ 2) := by
    rw [div_le_iff₀ (by positivity)]
    have h1 := mul_le_mul_of_nonneg_left haa (by positivity : (0 : ℝ) ≤ 4 * (X / n ^ 2))
    have e : 4 * (X / n ^ 2) * (n ^ 2 / 4) = X := by field_simp
    linarith
  have hP3one : 1 ≤ X / n ^ 2 := by rw [le_div_iff₀ (by positivity)]; linarith
  have hba : X / (b * (b + hR)) ≤ X / (a * (a + hR)) :=
    div_le_div_of_nonneg_left hX0.le (by positivity)
      (mul_le_mul hab (by linarith : a + hR ≤ b + hR) (by positivity) hb0.le)
  have hβα : diffPhase1 T hR k b - diffPhase1 T hR k a + 1 ≤ 5 * (X / n ^ 2) := by
    rw [hαv, hβv]
    have : 0 ≤ X / (b * (b + hR)) := by positivity
    linarith
  have hβα0 : 0 ≤ diffPhase1 T hR k b - diffPhase1 T hR k a + 1 := by
    rw [hαv, hβv]; linarith
  have hMle : (((⌈diffPhase1 T hR k b⌉₊ - (⌊diffPhase1 T hR k a⌋₊ + 1) : ℕ) : ℝ))
      ≤ 5 * (X / n ^ 2) := by
    have hβ0 : 0 ≤ diffPhase1 T hR k b := by rw [hβv]; linarith
    have h1 := Nat.ceil_lt_add_one hβ0
    have h2 := Nat.lt_floor_add_one (diffPhase1 T hR k a)
    rcases le_total (⌊diffPhase1 T hR k a⌋₊ + 1) ⌈diffPhase1 T hR k b⌉₊ with h | h
    · rw [Nat.cast_sub h]
      push_cast
      linarith
    · rw [Nat.sub_eq_zero_of_le h]
      push_cast
      linarith
  have hK : ((2 * k + 1 : ℕ) : ℝ) ≤ 11 * (X / n ^ 2) := by push_cast; linarith
  have hnum := block_B_numeric (γ := 3 * ((b + hR / 2) * (b * (b + hR)) ^ 3)
      / ((a + hR / 2) * (a * (a + hR)) ^ 3)) hn0 hX0 hXn
    (block_gamma_le hn0 ha2 hab hbn hR0.le hRn) (by positivity) hMle
    (block_lam_ge hX0 hn0 ha2 hR0.le) (block_lam_le hX0 hn0 ha2 han hRn hR0.le)
    (block_lam₂_ge hX0 hn0 hb0 hbn hR0.le hRn) (by positivity) (block_lam₃_le hX0 hn0 ha2)
    (by positivity) (block_rho_le hn0 ha2 hab hbn hR0.le hRn) hK hβα
  set A' : ℤ := (N : ℤ) - 1 with hA'
  set B' : ℤ := (N : ℤ) + L - 1 with hB'
  have hA'c : ((A' : ℤ) : ℝ) = a := by rw [hA', ha, hn]; push_cast; ring
  have hB'c : ((B' : ℤ) : ℝ) = b := by rw [hB', hb, hn]; push_cast; ring
  have hAB : A' ≤ B' := by rw [hA', hB']; omega
  -- step 1: the sum is a `B`-process sum of `diffPhase`
  have hsum : ∑ n' ∈ Finset.range L, Complex.exp (((2 * Real.pi * (T * (Real.log (n + n' + hR)
        - Real.log (n + n'))) : ℝ) : ℂ) * I)
      = ∑ m ∈ Finset.Ioc A' B', Complex.exp (((2 * Real.pi * diffPhase T hR k m : ℝ) : ℂ) * I) := by
    have hB'' : B' = A' + L := by rw [hA', hB']; ring
    rw [hB'', sum_Ioc_int_eq_sum_range]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hcast : (((A' + 1 + j : ℤ)) : ℝ) = n + j := by rw [hA', hn]; push_cast; ring
    rw [hcast]
    simp only [diffPhase]
    have e : T * (Real.log (n + j + hR) - Real.log (n + j)) + k * (n + j)
        = T * (Real.log (n + j + hR) - Real.log (n + j)) + ((k * (N + j) : ℕ) : ℝ) := by
      rw [hn]; push_cast; ring
    rw [e, cexp_two_pi_add_nat]
  rw [hsum]
  -- step 2: the `B`-process
  have hIcc : ∀ y ∈ Set.Icc ((A' : ℤ) : ℝ) ((B' : ℤ) : ℝ), 0 < y ∧ a ≤ y ∧ y ≤ b := by
    intro y hy
    rw [hA'c, hB'c] at hy
    exact ⟨lt_of_lt_of_le ha0 hy.1, hy.1, hy.2⟩
  have hα : 0 ≤ diffPhase1 T hR k ((A' : ℤ) : ℝ) := by
    rw [hA'c, diffPhase1_eq ha0 hR0.le, ← hXd]
    linarith
  have hβk : diffPhase1 T hR k ((B' : ℤ) : ℝ) ≤ k := by
    rw [hB'c, diffPhase1_eq hb0 hR0.le]
    have : 0 ≤ T * hR / (b * (b + hR)) := by positivity
    linarith
  have hKB : 2 * diffPhase1 T hR k ((B' : ℤ) : ℝ) ≤ ((2 * k + 1 : ℕ) : ℝ) := by
    push_cast; linarith
  have hB := norm_sum_sub_bDualSum_le (f := diffPhase T hR k) (f' := diffPhase1 T hR k)
    (f'' := diffPhase2 T hR) (f''' := diffPhase3 T hR) hAB (lam₂ := 2 * X / (b + hR) ^ 3)
    (lam₃ := 6 * X / a ^ 4) (ρ := ((b + hR) / a) ^ 3)
    (δ := n ^ (7 / 5 : ℝ) * X ^ (-(2 / 5) : ℝ)) (K := 2 * k + 1)
    (fun y hy => hasDerivAt_diffPhase (hIcc y hy).1 hR0.le)
    (fun y hy => hasDerivAt_diffPhase1 (hIcc y hy).1 hR0.le)
    (fun y hy => hasDerivAt_diffPhase2 (hIcc y hy).1 hR0.le)
    (by positivity)
    (fun y hy => by
      obtain ⟨hy0, _, hyb⟩ := hIcc y hy
      refine le_trans ?_ (diffPhase2_ge hT.le hy0 hR0.le)
      have h1 : 2 * X / (b + hR) ^ 3 ≤ 2 * X / (y + hR) ^ 3 :=
        div_le_div_of_nonneg_left (by positivity) (by positivity)
          (pow_le_pow_left₀ (by linarith) (by linarith) 3)
      rw [hXd, ← mul_assoc] at h1
      rw [hXd, ← mul_assoc]
      exact h1)
    (fun y hy => by
      obtain ⟨hy0, hya, _⟩ := hIcc y hy
      refine (diffPhase2_le hT.le hy0 hR0.le).trans ?_
      have e : ((b + hR) / a) ^ 3 * (2 * X / (b + hR) ^ 3) = 2 * X / a ^ 3 := by
        field_simp
      have h1 : 2 * X / y ^ 3 ≤ 2 * X / a ^ 3 :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) (pow_le_pow_left₀ ha0.le hya 3)
      rw [hXd, ← mul_assoc] at h1 e
      rw [hXd, ← mul_assoc, e]
      exact h1)
    (fun y hy => by
      obtain ⟨hy0, hya, _⟩ := hIcc y hy
      refine (abs_diffPhase3_le hT.le hy0 hR0.le).trans ?_
      have h1 : 6 * X / y ^ 4 ≤ 6 * X / a ^ 4 :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) (pow_le_pow_left₀ ha0.le hya 4)
      rw [hXd, ← mul_assoc] at h1
      rw [hXd, ← mul_assoc]
      exact h1)
    (by positivity) hα hKB (by norm_num) (fun ν : ℕ => dualX T hR (k - ν))
    (fun ν h1 h2 => by
      rw [hA'c, diffPhase1_eq ha0 hR0.le] at h1
      rw [hB'c, diffPhase1_eq hb0 hR0.le] at h2
      have hu0 : 0 < (k : ℝ) - ν := by
        have : 0 < T * hR / (b * (b + hR)) := by positivity
        linarith
      refine ⟨?_, diffPhase1_dualX hT hR0 hu0 |>.trans (by ring)⟩
      rw [hA'c, hB'c]
      refine dualX_mem_Icc hT hR0 hu0 ha0.le hb0.le ?_ ?_
      · rw [le_div_iff₀ hu0]
        have h1' : (k : ℝ) - ν < T * hR / (a * (a + hR)) := by linarith
        rw [lt_div_iff₀ (by positivity)] at h1'
        calc a * (a + hR) * ((k : ℝ) - ν) = ((k : ℝ) - ν) * (a * (a + hR)) := by ring
          _ ≤ T * hR := h1'.le
      · rw [div_le_iff₀ hu0]
        have h2' : T * hR / (b * (b + hR)) < (k : ℝ) - ν := by linarith
        rw [div_lt_iff₀ (by positivity)] at h2'
        calc T * hR ≤ ((k : ℝ) - ν) * (b * (b + hR)) := h2'.le
          _ = b * (b + hR) * ((k : ℝ) - ν) := by ring)
  rw [hA'c, hB'c] at hB
  -- step 3: the dual sum
  have hlam1 : (a + hR / 2) * (a * (a + hR)) ^ 3 ≤ (T * hR) ^ 3 := by
    rw [← hXd]
    have := block_lam_le hX0 hn0 ha2 han hRn hR0.le
    rw [div_le_iff₀ (by positivity)] at this
    have e : 5 * (n ^ 7 / X ^ 3) * X ^ 3 = 5 * n ^ 7 := by field_simp
    linarith
  have hD := norm_dualSum_diffPhase_le (k := k) hT hR0 hRa hab hlam1
  have hl2e : 2 * T * hR / (b + hR) ^ 3 = 2 * X / (b + hR) ^ 3 := by rw [hXd]; ring
  rw [hl2e, ← hXd] at hD
  -- assemble
  set S := ∑ m ∈ Finset.Ioc A' B', Complex.exp (((2 * Real.pi * diffPhase T hR k m : ℝ) : ℂ) * I)
  set D := ∑ ν ∈ Finset.Ioo ⌊diffPhase1 T hR k a⌋₊ ⌈diffPhase1 T hR k b⌉₊,
      bDualTerm (diffPhase T hR k) (diffPhase2 T hR) (fun ν : ℕ => dualX T hR (k - ν)) ν
  have htri : ‖S‖ ≤ ‖S - D‖ + ‖D‖ := by
    have := norm_add_le (S - D) D
    rwa [sub_add_cancel] at this
  linarith only [htri, hB, hD, hnum]

end

end RHTower
