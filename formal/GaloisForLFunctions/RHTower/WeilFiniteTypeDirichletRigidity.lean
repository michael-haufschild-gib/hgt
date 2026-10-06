import GaloisForLFunctions.RHTower.ZetaFrequencyFamilyZeroSums
import GaloisForLFunctions.RHTower.WeilFiniteTypeResidues

/-!
# Finite-type Weil systems: the Dirichlet parts are trivial

Let `lam = Λ ⋆ a + μ ⋆ f + v` be full-cone Weil-positive, with `a`, `f` supported in `[1, N]`,
`f(1) = 0` and `v` regular; `A(s) = Σ a(n) n^{−s}`, `F(s) = Σ f(n) n^{−s}`, `Ã(s) = A(1 − s)`,
`F̃(s) = F(1 − s)`.  Then `a = δ₁` (`dirichletPart_eq_delta`) and `f = 0` (`moebiusPart_eq_zero`).

**Step 1.** Let `n₀` and `M` be the least and the largest `n` with `a(n) ≠ 0`, `κ = n₀/M²`, and
`H = (ζ'(A − Ã) − F − χF̃) · AÃκ^s` (`testOne`).
* At a critical zero, `H(ρ) = 0`: the realness constraint
  `R ζ'(A − Ã) = RF + F̃` (`critical_realness`) and `χR = 1`.
* Right of the line `Aζ' = F`, so `H = −FÃ²κ^s − χF̃AÃκ^s`.  Left of it, `ζ'(ρ) = −χ(ρ)ζ'(1−ρ)`
  and `Ã(ρ)ζ'(1 − ρ) = F̃(ρ)`, so `H = −χF̃A²κ^s − FAÃκ^s`.  Either way `|H(ρ)| ≤ K γ^{|β−½|}`,
  and the zero sum is `o(T log² T)`.
* On the other side, `H = ζ'·A²Ãκ^s − ζ'·AÃ²κ^s − FAÃκ^s − χ·F̃AÃκ^s`.  If `M ≥ 2`, the
  frequencies `m n₀/(n₁n₂M²)` of `A²Ãκ^s` lie in `(0, 1)`, and those `m₁m₂n₀/(nM²)` of `AÃ²κ^s`
  lie in `(0, 1]`, with `1` only at `(n, m₁, m₂) = (n₀, M, M)`.  So the sum is
  `−a(n₀)a(M)²/M² · Re Σ m_ρ ζ'(ρ) g_T(ρ) + O(TU)`, which contradicts the first side.

So `a` vanishes beyond `1`, and `A(1) = 1` gives `a(1) = 1`.

**Step 2.** Now `A = 1`.  Let `M` be the largest `n` with `f(n) ≠ 0` (so `M ≥ 2`), `P > M` a prime,
`κ = P/M`, and `H = (ζ'F̃ − ζ'(1 − s)F) κ^s` (`testTwo`).  At a critical zero
`H = ζ'(F̃ + RF)κ^s = 0`; off the line `ζ' = F` (or `ζ'(1−ρ) = F̃`) and `|χ| ≤ Cγ^{|β−½|}` bound `H`.
The frequencies `nP/M` of `F̃κ^s` are integral only at `n = M`, where `nP/M = P` with coefficient
`f(M)/M`; those `P/(nM)` of `Fκ^s` reflect to `nM/P`, never integral.
-/

open Complex Filter Topology Set
open RHTower.WeilSpectral RHTower.WeilHerglotz RHTower.GaussZeroSum

namespace RHTower.WeilFiniteType

noncomputable section

/-! ## Dirichlet polynomials as frequency families -/

/-- The support of `a` in `[1, N]`. -/
def suppIcc (N : ℕ) (a : ℕ → ℝ) : Finset ℕ := (Finset.Icc 1 N).filter (fun n => a n ≠ 0)

theorem mem_suppIcc {N : ℕ} {a : ℕ → ℝ} {n : ℕ} :
    n ∈ suppIcc N a ↔ (1 ≤ n ∧ n ≤ N) ∧ a n ≠ 0 := by
  rw [suppIcc, Finset.mem_filter, Finset.mem_Icc]

theorem dirPoly_eq_famPoly (N : ℕ) (a : ℕ → ℝ) (s : ℂ) :
    dirPoly N a s = famPoly (suppIcc N a) a (fun _ => 1) (fun n => n) s := by
  unfold famPoly suppIcc
  rw [Finset.sum_filter_of_ne (p := fun n => a n ≠ 0) fun n _ h ha => h (by simp [ha])]
  unfold dirPoly
  exact Finset.sum_congr rfl fun n hn => by
    rw [natCast_cpow_neg_eq_ratPow (Finset.mem_Icc.mp hn).1]

theorem dirPoly_one_sub_eq_famPoly (N : ℕ) (a : ℕ → ℝ) (s : ℂ) :
    dirPoly N a (1 - s) =
      famPoly (suppIcc N a) (fun n => a n / n) (fun n => n) (fun _ => 1) s := by
  unfold famPoly suppIcc
  rw [Finset.sum_filter_of_ne (p := fun n => a n ≠ 0) fun n _ h ha => h (by simp [ha])]
  unfold dirPoly
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [natCast_cpow_neg_one_sub_eq_ratPow (Finset.mem_Icc.mp hn).1]
  push_cast
  ring

theorem famPoly_mul {ι κ : Type*} (I : Finset ι) (J : Finset κ) (c : ι → ℝ) (p q : ι → ℕ)
    (d : κ → ℝ) (p' q' : κ → ℕ) (s : ℂ) :
    famPoly I c p q s * famPoly J d p' q' s =
      famPoly (I ×ˢ J) (fun x => c x.1 * d x.2) (fun x => p x.1 * p' x.2)
        (fun x => q x.1 * q' x.2) s := by
  unfold famPoly
  rw [Finset.sum_mul_sum, Finset.sum_product]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← ratPow_mul]
  push_cast
  ring

theorem famPoly_mul_ratPow {ι : Type*} (I : Finset ι) (c : ι → ℝ) (p q : ι → ℕ) (P Q : ℕ)
    (s : ℂ) :
    famPoly I c p q s * ratPow P Q s = famPoly I c (fun i => p i * P) (fun i => q i * Q) s := by
  unfold famPoly
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _ => by rw [mul_assoc, ratPow_mul]

/-! ## Bounds in the strip -/

theorem norm_dirPoly_le (N : ℕ) (a : ℕ → ℝ) {s : ℂ} (hs : 0 ≤ s.re) :
    ‖dirPoly N a s‖ ≤ ∑ n ∈ Finset.Icc 1 N, |a n| := by
  unfold dirPoly
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n hn => ?_)
  have hn : 1 ≤ n := (Finset.mem_Icc.mp hn).1
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_natCast_cpow_of_pos (by omega)]
  refine mul_le_of_le_one_right (abs_nonneg _) ?_
  exact Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hn)
    (by rw [Complex.neg_re]; linarith)

theorem norm_ratPow_le {p q : ℕ} (hp : 0 < p) (hq : 0 < q) {s : ℂ} (hs0 : 0 ≤ s.re)
    (hs1 : s.re ≤ 1) : ‖ratPow p q s‖ ≤ 1 + (p : ℝ) / q := by
  have hx : (0 : ℝ) < (p : ℝ) / q := by positivity
  unfold ratPow
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hx]
  rcases le_total ((p : ℝ) / q) 1 with h1 | h1
  · have := Real.rpow_le_one hx.le h1 hs0; linarith
  · have := Real.rpow_le_rpow_of_exponent_le h1 hs1
    rw [Real.rpow_one] at this
    linarith

theorem exists_norm_zetaChi_le_exp :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, 0 ≤ s.re → s.re ≤ 1 → 1 ≤ |s.im| →
      ‖zetaChi s‖ ≤ C * Real.exp ((1 / 2 - s.re) * Real.log |s.im|) := by
  obtain ⟨C, hC, h⟩ := exists_norm_zetaChi_le_strip
  refine ⟨C, hC, fun s h0 h1 him => ?_⟩
  have := h s.re s.im h0 h1 him
  rwa [Complex.re_add_im, Real.rpow_def_of_pos (by linarith), mul_comm (Real.log _)] at this

theorem norm_mul_three_le {x₁ x₂ x₃ : ℂ} {b₁ b₂ b₃ : ℝ} (h₁ : ‖x₁‖ ≤ b₁) (h₂ : ‖x₂‖ ≤ b₂)
    (h₃ : ‖x₃‖ ≤ b₃) : ‖x₁ * x₂ * x₃‖ ≤ b₁ * b₂ * b₃ := by
  have hb₁ : 0 ≤ b₁ := (norm_nonneg _).trans h₁
  have hb₂ : 0 ≤ b₂ := (norm_nonneg _).trans h₂
  rw [norm_mul, norm_mul]
  exact mul_le_mul (mul_le_mul h₁ h₂ (norm_nonneg _) hb₁) h₃ (norm_nonneg _) (mul_nonneg hb₁ hb₂)

/-! ## Step 1 -/

/-- `(ζ'(A − Ã) − F − χF̃) · A Ã (P/Q)^s`. -/
def testOne (N : ℕ) (a f : ℕ → ℝ) (P Q : ℕ) (s : ℂ) : ℂ :=
  (deriv riemannZeta s * (dirPoly N a s - dirPoly N a (1 - s)) - dirPoly N f s -
      zetaChi s * dirPoly N f (1 - s)) * (dirPoly N a s * dirPoly N a (1 - s) * ratPow P Q s)

theorem testOne_critical {N : ℕ} {a f v : ℕ → ℝ} {E : ℂ → ℂ} (ha : SupportedIn N a)
    (hf : SupportedIn N f) (hf1 : f 1 = 0) (hv : RegularPart v E)
    (hW : WeilPositiveFull (finiteTypeSeq a f v)) (P Q : ℕ) {ρ : ℂ} (hz : riemannZeta ρ = 0)
    (hre : ρ.re = 1 / 2) (him : 1 ≤ ρ.im) : testOne N a f P Q ρ = 0 := by
  have hreal := critical_realness ha hf hf1 hv hW hre hz
  have hχR := zetaChi_mul_zetaReflectionFactor (s := ρ) (ne_of_gt (by linarith))
  have hJ : deriv riemannZeta ρ * (dirPoly N a ρ - dirPoly N a (1 - ρ)) - dirPoly N f ρ -
      zetaChi ρ * dirPoly N f (1 - ρ) = 0 := by
    linear_combination zetaChi ρ * hreal -
      (deriv riemannZeta ρ * (dirPoly N a ρ - dirPoly N a (1 - ρ)) - dirPoly N f ρ) * hχR
  unfold testOne
  rw [hJ, zero_mul]

theorem exists_norm_testOne_le {N : ℕ} {a f v : ℕ → ℝ} {E : ℂ → ℂ} (ha : SupportedIn N a)
    (hf : SupportedIn N f) (hf1 : f 1 = 0) (hv : RegularPart v E)
    (hW : WeilPositiveFull (finiteTypeSeq a f v)) {P Q : ℕ} (hP : 0 < P) (hQ : 0 < Q) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → ρ.re ≠ 1 / 2 →
      1 ≤ ρ.im → ‖testOne N a f P Q ρ‖ ≤ K * Real.exp (|ρ.re - 1 / 2| * Real.log ρ.im) := by
  obtain ⟨Cχ, hCχ, hχ⟩ := exists_norm_zetaChi_le_exp
  set BA : ℝ := ∑ n ∈ Finset.Icc 1 N, |a n| with hBA
  set BF : ℝ := ∑ n ∈ Finset.Icc 1 N, |f n| with hBF
  set Bκ : ℝ := 1 + (P : ℝ) / Q with hBκ
  have hBA0 : 0 ≤ BA := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hBF0 : 0 ≤ BF := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hBκ0 : 0 ≤ Bκ := by positivity
  refine ⟨BF * BA * BA * Bκ * (1 + Cχ), by positivity, fun ρ hz h0 h1 hne him => ?_⟩
  set X := Real.exp (|ρ.re - 1 / 2| * Real.log ρ.im) with hX
  have hX1 : 1 ≤ X := Real.one_le_exp (mul_nonneg (abs_nonneg _) (Real.log_nonneg him))
  have hre1 : 0 ≤ (1 - ρ).re := by rw [Complex.sub_re, Complex.one_re]; linarith
  have hA := norm_dirPoly_le N a h0.le
  have hA' := norm_dirPoly_le N a hre1
  have hF := norm_dirPoly_le N f h0.le
  have hF' := norm_dirPoly_le N f hre1
  have hκ := norm_ratPow_le hP hQ h0.le h1.le
  have him' : 1 ≤ |ρ.im| := by rw [abs_of_pos (by linarith)]; exact him
  have hχρ := hχ ρ h0.le h1.le him'
  rw [abs_of_pos (by linarith : (0 : ℝ) < ρ.im)] at hχρ
  set A := dirPoly N a ρ
  set Ã := dirPoly N a (1 - ρ)
  set F := dirPoly N f ρ
  set Fr := dirPoly N f (1 - ρ)
  set κ := ratPow P Q ρ
  set χ := zetaChi ρ
  have hB : BF * BA * BA * Bκ * (1 + Cχ) * X =
      BF * BA * BA * Bκ * X + Cχ * X * BF * BA * BA * Bκ := by ring
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · -- left of the line
    have hz' := RHTower.riemannZeta_one_sub_eq_zero_of_mem_openStrip hz h0 h1
    have hA1 := dirPoly_mul_deriv_eq_of_offLine ha hf hf1 hv hW (ρ := 1 - ρ)
      (by rw [Complex.sub_re, Complex.one_re]; linarith) hz'
    have hd := deriv_riemannZeta_eq_neg_zetaChi_mul hz h0 h1 (ne_of_gt (by linarith))
    have hform : testOne N a f P Q ρ = -(χ * Fr * (A * A * κ)) - F * (A * Ã * κ) := by
      unfold testOne
      linear_combination (Ã * (A * A * κ - A * Ã * κ)) * hd -
        (χ * (A * A * κ - A * Ã * κ)) * hA1
    have hχX : ‖χ‖ ≤ Cχ * X := by
      rw [hX, abs_of_neg (by linarith : ρ.re - 1 / 2 < 0)]
      convert hχρ using 3; ring
    rw [hform]
    calc ‖-(χ * Fr * (A * A * κ)) - F * (A * Ã * κ)‖
        ≤ ‖χ * Fr * (A * A * κ)‖ + ‖F * (A * Ã * κ)‖ := by
          rw [sub_eq_add_neg]; refine (norm_add_le _ _).trans ?_; rw [norm_neg, norm_neg]
      _ ≤ Cχ * X * BF * (BA * BA * Bκ) + BF * (BA * BA * Bκ) := by
          gcongr
          · exact norm_mul_three_le hχX hF' (norm_mul_three_le hA hA hκ)
          · rw [norm_mul]
            exact mul_le_mul hF (norm_mul_three_le hA hA' hκ) (norm_nonneg _) hBF0
      _ ≤ _ := by
          rw [hB]
          have : BF * (BA * BA * Bκ) ≤ BF * BA * BA * Bκ * X := by
            rw [show BF * (BA * BA * Bκ) = BF * BA * BA * Bκ * 1 by ring]
            exact mul_le_mul_of_nonneg_left hX1 (by positivity)
          linarith
  · -- right of the line
    have hA0 := dirPoly_mul_deriv_eq_of_offLine ha hf hf1 hv hW hgt hz
    have hform : testOne N a f P Q ρ = -(F * (Ã * Ã * κ)) - χ * Fr * (A * Ã * κ) := by
      unfold testOne
      linear_combination (A * Ã * κ - Ã * Ã * κ) * hA0
    have hχ1 : ‖χ‖ ≤ Cχ * X := by
      refine hχρ.trans (mul_le_mul_of_nonneg_left ?_ hCχ)
      exact (Real.exp_le_one_iff.mpr
        (mul_nonpos_of_nonpos_of_nonneg (by linarith) (Real.log_nonneg him))).trans hX1
    rw [hform]
    calc ‖-(F * (Ã * Ã * κ)) - χ * Fr * (A * Ã * κ)‖
        ≤ ‖F * (Ã * Ã * κ)‖ + ‖χ * Fr * (A * Ã * κ)‖ := by
          rw [sub_eq_add_neg]; refine (norm_add_le _ _).trans ?_; rw [norm_neg, norm_neg]
      _ ≤ BF * (BA * BA * Bκ) + Cχ * X * BF * (BA * BA * Bκ) := by
          gcongr
          · rw [norm_mul]
            exact mul_le_mul hF (norm_mul_three_le hA' hA' hκ) (norm_nonneg _) hBF0
          · exact norm_mul_three_le hχ1 hF' (norm_mul_three_le hA hA' hκ)
      _ ≤ _ := by
          rw [hB]
          have : BF * (BA * BA * Bκ) ≤ BF * BA * BA * Bκ * X := by
            rw [show BF * (BA * BA * Bκ) = BF * BA * BA * Bκ * 1 by ring]
            exact mul_le_mul_of_nonneg_left hX1 (by positivity)
          linarith

/-- The arithmetic of the integral frequency of `AÃ²κ^s`. -/
theorem eq_of_mul_eq_sq {n n₀ m₁ m₂ M : ℕ} (hn : n₀ ≤ n) (h1 : m₁ ≤ M) (h2 : m₂ ≤ M)
    (hn₀ : 1 ≤ n₀) (hm₁ : 1 ≤ m₁) (heq : m₁ * m₂ * n₀ = n * M ^ 2) :
    n = n₀ ∧ m₁ = M ∧ m₂ = M := by
  have hM : 1 ≤ M := le_trans hm₁ h1
  have hmm : m₁ * m₂ ≤ M ^ 2 := by rw [sq]; exact Nat.mul_le_mul h1 h2
  have hA : m₁ * m₂ * n₀ ≤ M ^ 2 * n₀ := Nat.mul_le_mul_right _ hmm
  have hB : M ^ 2 * n₀ ≤ M ^ 2 * n := Nat.mul_le_mul_left _ hn
  have hC : M ^ 2 * n₀ = M ^ 2 * n := le_antisymm hB (by rw [mul_comm (M ^ 2) n, ← heq]; exact hA)
  have hn' : n₀ = n := Nat.eq_of_mul_eq_mul_left (by positivity) hC
  have hD : m₁ * m₂ = M ^ 2 :=
    Nat.eq_of_mul_eq_mul_right (m := n₀) (by omega) (by rw [heq, hn', mul_comm])
  refine ⟨hn'.symm, ?_, ?_⟩
  · by_contra h
    have hlt : m₁ < M := lt_of_le_of_ne h1 h
    have : m₁ * m₂ < M ^ 2 := by nlinarith
    exact absurd hD (ne_of_lt this)
  · by_contra h
    have hlt : m₂ < M := lt_of_le_of_ne h2 h
    have : m₁ * m₂ < M ^ 2 := by nlinarith
    exact absurd hD (ne_of_lt this)

/-- **Step 1, the analytic side.** -/
theorem exists_abs_re_zeroSum_testOne_sub_le {N : ℕ} {a f : ℕ → ℝ} {n₀ M : ℕ} (hM : 2 ≤ M)
    (hn₀ : 1 ≤ n₀) (hsupp : ∀ n ∈ suppIcc N a, n₀ ≤ n ∧ n ≤ M) (hn₀mem : n₀ ∈ suppIcc N a)
    (hMmem : M ∈ suppIcc N a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T → ∀ Y : ℝ, GoodTop T Y →
      |(∑ w ∈ rectZeros bottomHeight Y, (mult w : ℂ) *
          (testOne N a f n₀ (M ^ 2) w * gaussWeight T w)).re -
        (-(a n₀ * (a M / M) * (a M / M))) * (∑ w ∈ rectZeros bottomHeight Y, (mult w : ℂ) *
          (deriv riemannZeta w * (((1 : ℕ) : ℝ) : ℂ) ^ w * gaussWeight T w)).re| ≤
        C * T * (Real.log T + 1) := by
  classical
  set sa := suppIcc N a with hsa
  set sf := suppIcc N f with hsf
  have hpos : ∀ n ∈ sa, 1 ≤ n := fun n hn => (mem_suppIcc.mp hn).1.1
  have hposf : ∀ n ∈ sf, 1 ≤ n := fun n hn => (mem_suppIcc.mp hn).1.1
  have hM0 : 0 < M := by omega
  -- the four families
  have hX₁ : ∀ w, dirPoly N a w * dirPoly N a w * dirPoly N a (1 - w) * ratPow n₀ (M ^ 2) w =
      famPoly ((sa ×ˢ sa) ×ˢ sa) (fun x => a x.1.1 * a x.1.2 * (a x.2 / x.2))
        (fun x => 1 * 1 * x.2 * n₀) (fun x => x.1.1 * x.1.2 * 1 * M ^ 2) w := fun w => by
    rw [dirPoly_eq_famPoly N a w, dirPoly_one_sub_eq_famPoly N a w, famPoly_mul, famPoly_mul,
      famPoly_mul_ratPow]
  have hX₂ : ∀ w, dirPoly N a w * dirPoly N a (1 - w) * dirPoly N a (1 - w) *
      ratPow n₀ (M ^ 2) w =
      famPoly ((sa ×ˢ sa) ×ˢ sa) (fun x => a x.1.1 * (a x.1.2 / x.1.2) * (a x.2 / x.2))
        (fun x => 1 * x.1.2 * x.2 * n₀) (fun x => x.1.1 * 1 * 1 * M ^ 2) w := fun w => by
    rw [dirPoly_eq_famPoly N a w, dirPoly_one_sub_eq_famPoly N a w, famPoly_mul, famPoly_mul,
      famPoly_mul_ratPow]
  have hX₃ : ∀ w, dirPoly N f w * dirPoly N a w * dirPoly N a (1 - w) * ratPow n₀ (M ^ 2) w =
      famPoly ((sf ×ˢ sa) ×ˢ sa) (fun x => f x.1.1 * a x.1.2 * (a x.2 / x.2))
        (fun x => 1 * 1 * x.2 * n₀) (fun x => x.1.1 * x.1.2 * 1 * M ^ 2) w := fun w => by
    rw [dirPoly_eq_famPoly N f w, dirPoly_eq_famPoly N a w, dirPoly_one_sub_eq_famPoly N a w,
      famPoly_mul, famPoly_mul, famPoly_mul_ratPow]
  have hX₄ : ∀ w, dirPoly N f (1 - w) * dirPoly N a w * dirPoly N a (1 - w) *
      ratPow n₀ (M ^ 2) w =
      famPoly ((sf ×ˢ sa) ×ˢ sa) (fun x => f x.1.1 / x.1.1 * a x.1.2 * (a x.2 / x.2))
        (fun x => x.1.1 * 1 * x.2 * n₀) (fun x => 1 * x.1.2 * 1 * M ^ 2) w := fun w => by
    rw [dirPoly_one_sub_eq_famPoly N f w, dirPoly_eq_famPoly N a w,
      dirPoly_one_sub_eq_famPoly N a w, famPoly_mul, famPoly_mul, famPoly_mul_ratPow]
  -- membership facts
  have mem3 : ∀ {s t u : Finset ℕ} {x : (ℕ × ℕ) × ℕ}, x ∈ (s ×ˢ t) ×ˢ u →
      x.1.1 ∈ s ∧ x.1.2 ∈ t ∧ x.2 ∈ u := fun hx => by
    rw [Finset.mem_product, Finset.mem_product] at hx; exact ⟨hx.1.1, hx.1.2, hx.2⟩
  -- family 1: no integral frequency
  have hfil₁ : ((sa ×ˢ sa) ×ˢ sa).filter
      (fun x => (fun x : (ℕ × ℕ) × ℕ => x.1.1 * x.1.2 * 1 * M ^ 2) x ∣
        (fun x : (ℕ × ℕ) × ℕ => 1 * 1 * x.2 * n₀) x) = ∅ := by
    refine Finset.filter_eq_empty_iff.mpr fun x hx hdvd => ?_
    obtain ⟨h1, h2, h3⟩ := mem3 hx
    have hn₁ := hsupp _ h1
    have hn₂ := hsupp _ h2
    have hm := hsupp _ h3
    simp only [one_mul, mul_one] at hdvd
    have hp : 0 < x.2 * n₀ := by have := hpos _ h3; positivity
    have hle := Nat.le_of_dvd hp hdvd
    have e1 : x.2 * n₀ ≤ M * n₀ := Nat.mul_le_mul_right _ hm.2
    have e2 : n₀ * n₀ * M ^ 2 ≤ x.1.1 * x.1.2 * M ^ 2 :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul hn₁.1 hn₂.1)
    have e3 : M * n₀ < n₀ * n₀ * M ^ 2 := by nlinarith
    linarith
  -- family 2: the integral frequency is `1`, only at `(n₀, M, M)`
  have hint₂ : ∀ x ∈ (sa ×ˢ sa) ×ˢ sa, x.1.1 * 1 * 1 * M ^ 2 ∣ 1 * x.1.2 * x.2 * n₀ →
      1 * x.1.2 * x.2 * n₀ = 1 * (x.1.1 * 1 * 1 * M ^ 2) := by
    intro x hx hdvd
    obtain ⟨h1, h2, h3⟩ := mem3 hx
    have hp : 0 < 1 * x.1.2 * x.2 * n₀ := by
      have := hpos _ h2; have := hpos _ h3; positivity
    have hle := Nat.le_of_dvd hp hdvd
    have e1 : x.1.2 * x.2 ≤ M * M := Nat.mul_le_mul (hsupp _ h2).2 (hsupp _ h3).2
    have e2 : M * M * n₀ ≤ M * M * x.1.1 := Nat.mul_le_mul_left _ (hsupp _ h1).1
    have e3 : x.1.2 * x.2 * n₀ ≤ M * M * n₀ := Nat.mul_le_mul_right _ e1
    simp only [one_mul, mul_one] at hle ⊢
    rw [sq] at hle ⊢
    nlinarith
  have hfil₂ : ((sa ×ˢ sa) ×ˢ sa).filter
      (fun x => (fun x : (ℕ × ℕ) × ℕ => x.1.1 * 1 * 1 * M ^ 2) x ∣
        (fun x : (ℕ × ℕ) × ℕ => 1 * x.1.2 * x.2 * n₀) x) = {((n₀, M), M)} := by
    ext x
    rw [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨hx, hdvd⟩
      have heq := hint₂ x hx hdvd
      obtain ⟨h1, h2, h3⟩ := mem3 hx
      simp only [one_mul, mul_one] at heq
      obtain ⟨e1, e2, e3⟩ := eq_of_mul_eq_sq (hsupp _ h1).1 (hsupp _ h2).2 (hsupp _ h3).2 hn₀
        (hpos _ h2) heq
      rw [Prod.ext_iff, Prod.ext_iff]
      exact ⟨⟨e1, e2⟩, e3⟩
    · rintro rfl
      refine ⟨Finset.mem_product.mpr ⟨Finset.mem_product.mpr ⟨hn₀mem, hMmem⟩, hMmem⟩, ?_⟩
      simp only [one_mul, mul_one]
      exact ⟨1, by ring⟩
  -- positivity of the frequencies
  obtain ⟨C₁, hC₁, T₁, h₁⟩ := exists_abs_re_zeroSum_deriv_famPoly_sub_le ((sa ×ˢ sa) ×ˢ sa)
    (fun x => a x.1.1 * a x.1.2 * (a x.2 / x.2)) (fun x => 1 * 1 * x.2 * n₀)
    (fun x => x.1.1 * x.1.2 * 1 * M ^ 2)
    (fun x hx => by have := hpos _ (mem3 hx).2.2; positivity)
    (fun x hx => by have := hpos _ (mem3 hx).1; have := hpos _ (mem3 hx).2.1; positivity) 1
    (fun x hx hdvd => by
      have : x ∈ ((sa ×ˢ sa) ×ˢ sa).filter (fun x => (fun x : (ℕ × ℕ) × ℕ =>
          x.1.1 * x.1.2 * 1 * M ^ 2) x ∣ (fun x : (ℕ × ℕ) × ℕ => 1 * 1 * x.2 * n₀) x) :=
        Finset.mem_filter.mpr ⟨hx, hdvd⟩
      rw [hfil₁] at this
      exact absurd this (Finset.notMem_empty _))
  obtain ⟨C₂, hC₂, T₂, h₂⟩ := exists_abs_re_zeroSum_deriv_famPoly_sub_le ((sa ×ˢ sa) ×ˢ sa)
    (fun x => a x.1.1 * (a x.1.2 / x.1.2) * (a x.2 / x.2)) (fun x => 1 * x.1.2 * x.2 * n₀)
    (fun x => x.1.1 * 1 * 1 * M ^ 2)
    (fun x hx => by have := hpos _ (mem3 hx).2.1; have := hpos _ (mem3 hx).2.2; positivity)
    (fun x hx => by have := hpos _ (mem3 hx).1; positivity) 1 hint₂
  obtain ⟨C₃, hC₃, T₃, h₃⟩ := exists_abs_re_zeroSum_famPoly_le ((sf ×ˢ sa) ×ˢ sa)
    (fun x => f x.1.1 * a x.1.2 * (a x.2 / x.2)) (fun x => 1 * 1 * x.2 * n₀)
    (fun x => x.1.1 * x.1.2 * 1 * M ^ 2)
    (fun x hx => by have := hpos _ (mem3 hx).2.2; positivity)
    (fun x hx => by have := hposf _ (mem3 hx).1; have := hpos _ (mem3 hx).2.1; positivity)
  obtain ⟨C₄, hC₄, T₄, h₄⟩ := exists_abs_re_zeroSum_zetaChi_famPoly_le ((sf ×ˢ sa) ×ˢ sa)
    (fun x => f x.1.1 / x.1.1 * a x.1.2 * (a x.2 / x.2)) (fun x => x.1.1 * 1 * x.2 * n₀)
    (fun x => 1 * x.1.2 * 1 * M ^ 2)
    (fun x hx => by have := hposf _ (mem3 hx).1; have := hpos _ (mem3 hx).2.2; positivity)
    (fun x hx => by have := hpos _ (mem3 hx).2.1; positivity)
  refine ⟨C₁ + C₂ + C₃ + C₄, by positivity, max (max T₁ T₂) (max T₃ T₄), fun T hT Y hY => ?_⟩
  have hT₁ : T₁ ≤ T := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hT
  have hT₂ : T₂ ≤ T := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hT
  have hT₃ : T₃ ≤ T := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hT
  have hT₄ : T₄ ≤ T := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hT
  have e₁ := h₁ T hT₁ Y hY
  have e₂ := h₂ T hT₂ Y hY
  have e₃ := h₃ T hT₃ Y hY
  have e₄ := h₄ T hT₄ Y hY
  rw [hfil₁, Finset.sum_empty, zero_mul, sub_zero] at e₁
  rw [hfil₂, Finset.sum_singleton] at e₂
  dsimp only at e₂
  -- the split of the test sum
  set Z := rectZeros bottomHeight Y
  have hsplit : ∑ w ∈ Z, (mult w : ℂ) * (testOne N a f n₀ (M ^ 2) w * gaussWeight T w) =
      ∑ w ∈ Z, (mult w : ℂ) * (deriv riemannZeta w * famPoly ((sa ×ˢ sa) ×ˢ sa)
          (fun x => a x.1.1 * a x.1.2 * (a x.2 / x.2)) (fun x => 1 * 1 * x.2 * n₀)
          (fun x => x.1.1 * x.1.2 * 1 * M ^ 2) w * gaussWeight T w) -
        ∑ w ∈ Z, (mult w : ℂ) * (deriv riemannZeta w * famPoly ((sa ×ˢ sa) ×ˢ sa)
          (fun x => a x.1.1 * (a x.1.2 / x.1.2) * (a x.2 / x.2)) (fun x => 1 * x.1.2 * x.2 * n₀)
          (fun x => x.1.1 * 1 * 1 * M ^ 2) w * gaussWeight T w) -
        ∑ w ∈ Z, (mult w : ℂ) * (famPoly ((sf ×ˢ sa) ×ˢ sa)
          (fun x => f x.1.1 * a x.1.2 * (a x.2 / x.2)) (fun x => 1 * 1 * x.2 * n₀)
          (fun x => x.1.1 * x.1.2 * 1 * M ^ 2) w * gaussWeight T w) -
        ∑ w ∈ Z, (mult w : ℂ) * (zetaChi w * famPoly ((sf ×ˢ sa) ×ˢ sa)
          (fun x => f x.1.1 / x.1.1 * a x.1.2 * (a x.2 / x.2)) (fun x => x.1.1 * 1 * x.2 * n₀)
          (fun x => 1 * x.1.2 * 1 * M ^ 2) w * gaussWeight T w) := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [← hX₁, ← hX₂, ← hX₃, ← hX₄]
    unfold testOne
    ring
  rw [hsplit, Complex.sub_re, Complex.sub_re, Complex.sub_re]
  set S₁ := (∑ w ∈ Z, (mult w : ℂ) * (deriv riemannZeta w * famPoly ((sa ×ˢ sa) ×ˢ sa)
          (fun x => a x.1.1 * a x.1.2 * (a x.2 / x.2)) (fun x => 1 * 1 * x.2 * n₀)
          (fun x => x.1.1 * x.1.2 * 1 * M ^ 2) w * gaussWeight T w)).re
  set S₂ := (∑ w ∈ Z, (mult w : ℂ) * (deriv riemannZeta w * famPoly ((sa ×ˢ sa) ×ˢ sa)
          (fun x => a x.1.1 * (a x.1.2 / x.1.2) * (a x.2 / x.2)) (fun x => 1 * x.1.2 * x.2 * n₀)
          (fun x => x.1.1 * 1 * 1 * M ^ 2) w * gaussWeight T w)).re
  set S₃ := (∑ w ∈ Z, (mult w : ℂ) * (famPoly ((sf ×ˢ sa) ×ˢ sa)
          (fun x => f x.1.1 * a x.1.2 * (a x.2 / x.2)) (fun x => 1 * 1 * x.2 * n₀)
          (fun x => x.1.1 * x.1.2 * 1 * M ^ 2) w * gaussWeight T w)).re
  set S₄ := (∑ w ∈ Z, (mult w : ℂ) * (zetaChi w * famPoly ((sf ×ˢ sa) ×ˢ sa)
          (fun x => f x.1.1 / x.1.1 * a x.1.2 * (a x.2 / x.2)) (fun x => x.1.1 * 1 * x.2 * n₀)
          (fun x => 1 * x.1.2 * 1 * M ^ 2) w * gaussWeight T w)).re
  set Mn := (∑ w ∈ Z, (mult w : ℂ) *
    (deriv riemannZeta w * (((1 : ℕ) : ℝ) : ℂ) ^ w * gaussWeight T w)).re
  have key : S₁ - S₂ - S₃ - S₄ - -(a n₀ * (a M / M) * (a M / M)) * Mn =
      S₁ - (S₂ - a n₀ * (a M / M) * (a M / M) * Mn) - S₃ - S₄ := by ring
  rw [key]
  calc |S₁ - (S₂ - a n₀ * (a M / M) * (a M / M) * Mn) - S₃ - S₄|
      ≤ |S₁| + |S₂ - a n₀ * (a M / M) * (a M / M) * Mn| + |S₃| + |S₄| := by
        have h1 := abs_sub (S₁ - (S₂ - a n₀ * (a M / M) * (a M / M) * Mn) - S₃) S₄
        have h2 := abs_sub (S₁ - (S₂ - a n₀ * (a M / M) * (a M / M) * Mn)) S₃
        have h3 := abs_sub S₁ (S₂ - a n₀ * (a M / M) * (a M / M) * Mn)
        linarith
    _ ≤ C₁ * T * (Real.log T + 1) + C₂ * T * (Real.log T + 1) + C₃ * T * (Real.log T + 1) +
        C₄ * T * (Real.log T + 1) := by gcongr
    _ = _ := by ring

/-- **Step 1**: `a` vanishes beyond `1`. -/
theorem dirichletPart_eq_zero_of_two_le {N : ℕ} {a f v : ℕ → ℝ} {E : ℂ → ℂ}
    (ha : SupportedIn N a) (hf : SupportedIn N f) (hf1 : f 1 = 0) (hv : RegularPart v E)
    (hW : WeilPositiveFull (finiteTypeSeq a f v)) : ∀ n, 2 ≤ n → a n = 0 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨n₁, hn₁2, hn₁⟩ := hcon
  have hn₁N : n₁ ≤ N := by
    by_contra h
    exact hn₁ (ha.2 n₁ (by omega))
  have hmem : n₁ ∈ suppIcc N a := mem_suppIcc.mpr ⟨⟨by omega, hn₁N⟩, hn₁⟩
  have hne : (suppIcc N a).Nonempty := ⟨n₁, hmem⟩
  have hMmem := Finset.max'_mem _ hne
  have hn₀mem := Finset.min'_mem _ hne
  set M := (suppIcc N a).max' hne with hMdef
  set n₀ := (suppIcc N a).min' hne with hn₀def
  have hM2 : 2 ≤ M := le_trans hn₁2 (Finset.le_max' _ _ hmem)
  have hn₀1 : 1 ≤ n₀ := (mem_suppIcc.mp hn₀mem).1.1
  have hsupp : ∀ n ∈ suppIcc N a, n₀ ≤ n ∧ n ≤ M :=
    fun n hn => ⟨Finset.min'_le _ _ hn, Finset.le_max' _ _ hn⟩
  obtain ⟨K, hK, hoff⟩ := exists_norm_testOne_le ha hf hf1 hv hW (P := n₀) (Q := M ^ 2)
    (by omega) (by positivity)
  have hcoef : -(a n₀ * (a M / M) * (a M / M)) ≠ 0 := by
    have h1 := (mem_suppIcc.mp hn₀mem).2
    have h2 := (mem_suppIcc.mp hMmem).2
    have hM0 : (M : ℝ) ≠ 0 := by exact_mod_cast (by omega : M ≠ 0)
    exact neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero h1 (div_ne_zero h2 hM0)) (div_ne_zero h2 hM0))
  exact false_of_zeroSum_main hK
    (fun ρ hz hre him => testOne_critical ha hf hf1 hv hW n₀ (M ^ 2) hz hre him) hoff hcoef le_rfl
    (exists_abs_re_zeroSum_testOne_sub_le hM2 hn₀1 hsupp hn₀mem hMmem)

theorem dirPoly_eq_of_support {N : ℕ} {a : ℕ → ℝ} (hN : 1 ≤ N)
    (h2 : ∀ n, 2 ≤ n → a n = 0) (s : ℂ) : dirPoly N a s = a 1 := by
  unfold dirPoly
  rw [Finset.sum_eq_single 1]
  · simp
  · intro n hn hn1
    have : 2 ≤ n := by have := (Finset.mem_Icc.mp hn).1; omega
    simp [h2 n this]
  · intro h
    exact absurd (Finset.mem_Icc.mpr ⟨le_rfl, hN⟩) h

/-- **Step 1, conclusion**: `a = δ₁`. -/
theorem dirichletPart_eq_delta {N : ℕ} {a f v : ℕ → ℝ} {E : ℂ → ℂ}
    (ha : SupportedIn N a) (hf : SupportedIn N f) (hf1 : f 1 = 0) (hv : RegularPart v E)
    (hW : WeilPositiveFull (finiteTypeSeq a f v)) : ∀ n, a n = if n = 1 then 1 else 0 := by
  have h2 := dirichletPart_eq_zero_of_two_le ha hf hf1 hv hW
  have h1 := dirPoly_one_eq_one ha hf hf1 hv hW
  have hN : 1 ≤ N := by
    by_contra h
    have hN0 : N = 0 := by omega
    rw [dirPoly, hN0] at h1
    simp at h1
  rw [dirPoly_eq_of_support hN h2] at h1
  have ha1 : a 1 = 1 := by exact_mod_cast h1
  intro n
  split_ifs with hn
  · rw [hn, ha1]
  · rcases Nat.lt_or_ge n 2 with h | h
    · have : n = 0 := by omega
      rw [this]; exact ha.1
    · exact h2 n h

/-! ## Step 2 -/

/-- `(ζ'F̃ − ζ'(1 − s)F) (P/Q)^s`. -/
def testTwo (N : ℕ) (f : ℕ → ℝ) (P Q : ℕ) (s : ℂ) : ℂ :=
  (deriv riemannZeta s * dirPoly N f (1 - s) - deriv riemannZeta (1 - s) * dirPoly N f s) *
    ratPow P Q s

theorem testTwo_critical {N : ℕ} {a f v : ℕ → ℝ} {E : ℂ → ℂ} (ha : SupportedIn N a)
    (hf : SupportedIn N f) (hf1 : f 1 = 0) (hv : RegularPart v E)
    (hW : WeilPositiveFull (finiteTypeSeq a f v)) (hA : ∀ s, dirPoly N a s = 1) (P Q : ℕ)
    {ρ : ℂ} (hz : riemannZeta ρ = 0) (hre : ρ.re = 1 / 2) : testTwo N f P Q ρ = 0 := by
  have hreal := critical_realness ha hf hf1 hv hW hre hz
  rw [hA, hA] at hreal
  have hρ1 : ρ ≠ 1 := by rintro rfl; norm_num at hre
  have hd₁ := deriv_riemannZeta_one_sub_eq_of_zero (by rw [hre]; norm_num) hρ1 hz
  unfold testTwo
  linear_combination (-(deriv riemannZeta ρ * ratPow P Q ρ)) * hreal -
    (dirPoly N f ρ * ratPow P Q ρ) * hd₁

theorem exists_norm_testTwo_le {N : ℕ} {a f v : ℕ → ℝ} {E : ℂ → ℂ} (ha : SupportedIn N a)
    (hf : SupportedIn N f) (hf1 : f 1 = 0) (hv : RegularPart v E)
    (hW : WeilPositiveFull (finiteTypeSeq a f v)) (hA : ∀ s, dirPoly N a s = 1) {P Q : ℕ}
    (hP : 0 < P) (hQ : 0 < Q) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → ρ.re ≠ 1 / 2 →
      1 ≤ ρ.im → ‖testTwo N f P Q ρ‖ ≤ K * Real.exp (|ρ.re - 1 / 2| * Real.log ρ.im) := by
  obtain ⟨Cχ, hCχ, hχ⟩ := exists_norm_zetaChi_le_exp
  set BF : ℝ := ∑ n ∈ Finset.Icc 1 N, |f n| with hBF
  set Bκ : ℝ := 1 + (P : ℝ) / Q with hBκ
  have hBF0 : 0 ≤ BF := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hBκ0 : 0 ≤ Bκ := by positivity
  refine ⟨BF * BF * Bκ * (1 + Cχ), by positivity, fun ρ hz h0 h1 hne him => ?_⟩
  set X := Real.exp (|ρ.re - 1 / 2| * Real.log ρ.im) with hX
  have hX1 : 1 ≤ X := Real.one_le_exp (mul_nonneg (abs_nonneg _) (Real.log_nonneg him))
  have hre1 : 0 ≤ (1 - ρ).re := by rw [Complex.sub_re, Complex.one_re]; linarith
  have hF := norm_dirPoly_le N f h0.le
  have hF' := norm_dirPoly_le N f hre1
  have hκ := norm_ratPow_le hP hQ h0.le h1.le
  have hz' := RHTower.riemannZeta_one_sub_eq_zero_of_mem_openStrip hz h0 h1
  set F := dirPoly N f ρ
  set Fr := dirPoly N f (1 - ρ)
  set κ := ratPow P Q ρ
  have hB : BF * BF * Bκ * (1 + Cχ) * X = BF * BF * Bκ * X + Cχ * X * BF * BF * Bκ := by ring
  have hlow : BF * BF * Bκ ≤ BF * BF * Bκ * X := le_mul_of_one_le_right (by positivity) hX1
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · -- left of the line: `ζ'(1 − ρ) = Fr`, `ζ'(ρ) = −χ(ρ) Fr`
    have hA1 := dirPoly_mul_deriv_eq_of_offLine ha hf hf1 hv hW (ρ := 1 - ρ)
      (by rw [Complex.sub_re, Complex.one_re]; linarith) hz'
    rw [hA, one_mul] at hA1
    have hd := deriv_riemannZeta_eq_neg_zetaChi_mul hz h0 h1 (ne_of_gt (by linarith))
    have him' : 1 ≤ |ρ.im| := by rw [abs_of_pos (by linarith)]; exact him
    have hχρ := hχ ρ h0.le h1.le him'
    rw [abs_of_pos (by linarith : (0 : ℝ) < ρ.im)] at hχρ
    have hχX : ‖zetaChi ρ‖ ≤ Cχ * X := by
      rw [hX, abs_of_neg (by linarith : ρ.re - 1 / 2 < 0)]
      convert hχρ using 3; ring
    have hform : testTwo N f P Q ρ = -(zetaChi ρ * Fr * Fr * κ) - Fr * F * κ := by
      unfold testTwo
      rw [hd, hA1]
      ring
    rw [hform]
    calc ‖-(zetaChi ρ * Fr * Fr * κ) - Fr * F * κ‖ ≤ ‖zetaChi ρ * Fr * Fr * κ‖ + ‖Fr * F * κ‖ := by
          rw [sub_eq_add_neg]; refine (norm_add_le _ _).trans ?_; rw [norm_neg, norm_neg]
      _ ≤ Cχ * X * BF * BF * Bκ + BF * BF * Bκ := by
          gcongr
          · exact (norm_mul_three_le (norm_mul_le_of_le hχX hF') hF' hκ).trans (le_of_eq (by ring))
          · exact norm_mul_three_le hF' hF hκ
      _ ≤ _ := by rw [hB]; linarith
  · -- right of the line: `ζ'(ρ) = F`, `ζ'(1 − ρ) = −χ(1 − ρ) F`
    have hA0 := dirPoly_mul_deriv_eq_of_offLine ha hf hf1 hv hW hgt hz
    rw [hA, one_mul] at hA0
    have hd := deriv_riemannZeta_eq_neg_zetaChi_mul hz' (by rw [Complex.sub_re, Complex.one_re]; linarith)
      (by rw [Complex.sub_re, Complex.one_re]; linarith)
      (by rw [Complex.sub_im, Complex.one_im]; intro h; linarith)
    rw [sub_sub_cancel] at hd
    have him' : 1 ≤ |(1 - ρ).im| := by
      rw [Complex.sub_im, Complex.one_im, zero_sub, abs_neg, abs_of_pos (by linarith)]; exact him
    have hχρ := hχ (1 - ρ) (by rw [Complex.sub_re, Complex.one_re]; linarith)
      (by rw [Complex.sub_re, Complex.one_re]; linarith) him'
    have hχX : ‖zetaChi (1 - ρ)‖ ≤ Cχ * X := by
      refine hχρ.trans (le_of_eq ?_)
      rw [hX, Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, zero_sub, abs_neg,
        abs_of_pos (by linarith : (0 : ℝ) < ρ.im), abs_of_pos (by linarith : (0 : ℝ) < ρ.re - 1 / 2)]
      congr 2; ring
    have hform : testTwo N f P Q ρ = F * Fr * κ + zetaChi (1 - ρ) * F * F * κ := by
      unfold testTwo
      rw [hd, hA0]
      ring
    rw [hform]
    calc ‖F * Fr * κ + zetaChi (1 - ρ) * F * F * κ‖ ≤ ‖F * Fr * κ‖ + ‖zetaChi (1 - ρ) * F * F * κ‖ :=
          norm_add_le _ _
      _ ≤ BF * BF * Bκ + Cχ * X * BF * BF * Bκ := by
          gcongr
          · exact norm_mul_three_le hF hF' hκ
          · exact (norm_mul_three_le (norm_mul_le_of_le hχX hF) hF hκ).trans (le_of_eq (by ring))
      _ ≤ _ := by rw [hB]; linarith

/-- **Step 2, the analytic side.** -/
theorem exists_abs_re_zeroSum_testTwo_sub_le {N : ℕ} {f : ℕ → ℝ} {M P : ℕ} (hP : P.Prime)
    (hMP : M < P) (hsupp : ∀ n ∈ suppIcc N f, n ≤ M) (hMmem : M ∈ suppIcc N f) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T → ∀ Y : ℝ, GoodTop T Y →
      |(∑ w ∈ rectZeros bottomHeight Y, (mult w : ℂ) * (testTwo N f P M w * gaussWeight T w)).re -
        f M / M * (∑ w ∈ rectZeros bottomHeight Y, (mult w : ℂ) *
          (deriv riemannZeta w * ((P : ℝ) : ℂ) ^ w * gaussWeight T w)).re| ≤
        C * T * (Real.log T + 1) := by
  classical
  set sf := suppIcc N f with hsf
  have hposf : ∀ n ∈ sf, 1 ≤ n := fun n hn => (mem_suppIcc.mp hn).1.1
  have hM1 : 1 ≤ M := hposf M hMmem
  have hP0 : 0 < P := hP.pos
  have hcop : Nat.Coprime P M := (Nat.Prime.coprime_iff_not_dvd hP).mpr fun h =>
    absurd (Nat.le_of_dvd (by omega) h) (by omega)
  have hX₅ : ∀ w, dirPoly N f (1 - w) * ratPow P M w =
      famPoly sf (fun n => f n / n) (fun n => n * P) (fun _ => 1 * M) w := fun w => by
    rw [dirPoly_one_sub_eq_famPoly N f w, famPoly_mul_ratPow]
  have hX₆ : ∀ w, dirPoly N f w * ratPow P M w =
      famPoly sf f (fun _ => 1 * P) (fun n => n * M) w := fun w => by
    rw [dirPoly_eq_famPoly N f w, famPoly_mul_ratPow]
  have hint₅ : ∀ n ∈ sf, 1 * M ∣ n * P → n * P = P * (1 * M) := by
    intro n hn hdvd
    rw [one_mul] at hdvd ⊢
    have hMn : M ∣ n := hcop.symm.dvd_of_dvd_mul_right hdvd
    have := Nat.le_of_dvd (hposf n hn) hMn
    have hnM : n = M := le_antisymm (hsupp n hn) this
    rw [hnM, mul_comm]
  have hfil₅ : sf.filter (fun n => (fun _ : ℕ => 1 * M) n ∣ (fun n : ℕ => n * P) n) = {M} := by
    ext n
    rw [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨hn, hdvd⟩
      have h := hint₅ n hn hdvd
      rw [one_mul, mul_comm P M] at h
      exact Nat.eq_of_mul_eq_mul_right hP0 h
    · rintro rfl
      refine ⟨hMmem, ?_⟩
      simp only [one_mul]
      exact dvd_mul_right _ _
  obtain ⟨C₅, hC₅, T₅, h₅⟩ := exists_abs_re_zeroSum_deriv_famPoly_sub_le sf (fun n => f n / n)
    (fun n => n * P) (fun _ => 1 * M) (fun n hn => by have := hposf n hn; positivity)
    (fun _ _ => by omega) P hint₅
  obtain ⟨C₆, hC₆, T₆, h₆⟩ := exists_abs_re_zeroSum_deriv_one_sub_famPoly_le sf f
    (fun _ => 1 * P) (fun n => n * M) (fun _ _ => by omega)
    (fun n hn => by have := hposf n hn; positivity)
    (fun n hn hdvd => by
      rw [one_mul] at hdvd
      rcases (Nat.Prime.dvd_mul hP).mp hdvd with h | h
      · have := Nat.le_of_dvd (hposf n hn) h; have := hsupp n hn; omega
      · have := Nat.le_of_dvd (by omega) h; omega)
  refine ⟨C₅ + C₆, by positivity, max T₅ T₆, fun T hT Y hY => ?_⟩
  have e₅ := h₅ T (le_trans (le_max_left _ _) hT) Y hY
  have e₆ := h₆ T (le_trans (le_max_right _ _) hT) Y hY
  rw [hfil₅, Finset.sum_singleton] at e₅
  set Z := rectZeros bottomHeight Y
  have hsplit : ∑ w ∈ Z, (mult w : ℂ) * (testTwo N f P M w * gaussWeight T w) =
      ∑ w ∈ Z, (mult w : ℂ) * (deriv riemannZeta w *
        famPoly sf (fun n => f n / n) (fun n => n * P) (fun _ => 1 * M) w * gaussWeight T w) -
      ∑ w ∈ Z, (mult w : ℂ) * (deriv riemannZeta (1 - w) *
        famPoly sf f (fun _ => 1 * P) (fun n => n * M) w * gaussWeight T w) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [← hX₅, ← hX₆]
    unfold testTwo
    ring
  rw [hsplit, Complex.sub_re]
  set S₅ := (∑ w ∈ Z, (mult w : ℂ) * (deriv riemannZeta w *
        famPoly sf (fun n => f n / n) (fun n => n * P) (fun _ => 1 * M) w * gaussWeight T w)).re
  set S₆ := (∑ w ∈ Z, (mult w : ℂ) * (deriv riemannZeta (1 - w) *
        famPoly sf f (fun _ => 1 * P) (fun n => n * M) w * gaussWeight T w)).re
  set Mn := (∑ w ∈ Z, (mult w : ℂ) * (deriv riemannZeta w * ((P : ℝ) : ℂ) ^ w * gaussWeight T w)).re
  have key : S₅ - S₆ - f M / M * Mn = (S₅ - f M / M * Mn) - S₆ := by ring
  rw [key]
  calc |(S₅ - f M / M * Mn) - S₆| ≤ |S₅ - f M / M * Mn| + |S₆| := abs_sub _ _
    _ ≤ C₅ * T * (Real.log T + 1) + C₆ * T * (Real.log T + 1) := add_le_add e₅ e₆
    _ = _ := by ring

/-- **Step 2**: `f = 0`. -/
theorem moebiusPart_eq_zero {N : ℕ} {a f v : ℕ → ℝ} {E : ℂ → ℂ}
    (ha : SupportedIn N a) (hf : SupportedIn N f) (hf1 : f 1 = 0) (hv : RegularPart v E)
    (hW : WeilPositiveFull (finiteTypeSeq a f v)) : ∀ n, f n = 0 := by
  have hδ := dirichletPart_eq_delta ha hf hf1 hv hW
  by_contra hcon
  push Not at hcon
  obtain ⟨n₁, hn₁⟩ := hcon
  have hn₁2 : 2 ≤ n₁ := by
    rcases Nat.lt_or_ge n₁ 2 with h | h
    · interval_cases n₁
      · exact absurd hf.1 hn₁
      · exact absurd hf1 hn₁
    · exact h
  have hn₁N : n₁ ≤ N := by
    by_contra h
    exact hn₁ (hf.2 n₁ (by omega))
  have hN : 1 ≤ N := by omega
  have hA : ∀ s, dirPoly N a s = 1 := fun s => by
    rw [dirPoly_eq_of_support hN (fun n hn => by rw [hδ n, if_neg (by omega)]), hδ 1, if_pos rfl]
    simp
  have hmem : n₁ ∈ suppIcc N f := mem_suppIcc.mpr ⟨⟨by omega, hn₁N⟩, hn₁⟩
  have hne : (suppIcc N f).Nonempty := ⟨n₁, hmem⟩
  have hMmem := Finset.max'_mem _ hne
  set M := (suppIcc N f).max' hne with hMdef
  have hsupp : ∀ n ∈ suppIcc N f, n ≤ M := fun n hn => Finset.le_max' _ _ hn
  have hM1 : 1 ≤ M := (mem_suppIcc.mp hMmem).1.1
  obtain ⟨P, hPM, hP⟩ := Nat.exists_infinite_primes (M + 1)
  obtain ⟨K, hK, hoff⟩ := exists_norm_testTwo_le ha hf hf1 hv hW hA (P := P) (Q := M) hP.pos
    (by omega)
  have hcoef : f M / M ≠ 0 :=
    div_ne_zero (mem_suppIcc.mp hMmem).2 (by exact_mod_cast (by omega : M ≠ 0))
  exact false_of_zeroSum_main hK
    (fun ρ hz hre _ => testTwo_critical ha hf hf1 hv hW hA P M hz hre) hoff hcoef hP.one_le
    (exists_abs_re_zeroSum_testTwo_sub_le hP (by omega) hsupp hMmem)

end

end RHTower.WeilFiniteType
