import GaloisForLFunctions.RHTower.Matveev.FeldmanStageGain
import GaloisForLFunctions.RHTower.Matveev.FeldmanCoefficientVanishing
import GaloisForLFunctions.RHTower.Matveev.SmallForm

/-!
# The effective Baker bound for linear forms in prime logarithms

For distinct primes `p₁, …, p_d` there are `c, C > 0` with

`|Σ νᵢ log pᵢ| ≥ c (2 + |ν|₁)^{−C}`  for every nonzero `ν ∈ ℤ^d`.

The proof is Fel'dman's.  Normalize the form so that the largest coefficient `B = b_m > 0` is the
last one and put `n = ⌈log B⌉ + 1`.  If `|Λ| < e^{−C₀ n}`, Siegel's lemma gives a nonzero integer
coefficient vector with `Φ_{σ,τ}(x) = 0` for `x < X₀ = cn`, `σ + |τ| < S`; `R` extrapolation steps
carry the vanishing of `Φ_{0,0}` to `x < 2^R X₀ ≥ (N + 1) q^{m+1}`; and then all coefficients vanish
(`eq_zero_of_feldmanTrueAux_eq_zero`), a contradiction.  So `|Λ| ≥ e^{−C₀ n} ≥ e^{−2C₀} B^{−C₀}`.
-/

noncomputable section

namespace GaloisForLFunctions.RHTower.Matveev

open Finset Real

variable {m : ℕ}

theorem baseLogSum_le_totalLogSum (p : Fin (m + 1) → ℕ) (hp : ∀ j, 1 ≤ p j) :
    baseLogSum p ≤ totalLogSum p := by
  unfold baseLogSum totalLogSum
  rw [Fin.sum_univ_castSucc]
  have : 0 ≤ Real.log (p (Fin.last m)) := Real.log_nonneg (by exact_mod_cast hp _)
  linarith

theorem sixteen_mul_le_feldmanLambdaExponent {Wb : ℕ} (P : FeldmanParams m Wb) :
    16 * ((2 : ℝ) ^ P.R * P.c) * P.q ≤ feldmanLambdaExponent P := by
  unfold feldmanLambdaExponent
  have h1 : (0 : ℝ) ≤ P.S + 2 * P.a + 2 * (m + 1) * P.q + P.a + P.c + (P.a + 1) * (19 + 12 * P.R) +
      2 * P.q * m * P.S + m * P.S + P.c * P.q * Wb + P.a + 8 * (2 ^ P.R * P.c) +
      (P.a + 1) * (19 + 12 * P.R) + 2 * P.q * P.S + 8 * (2 ^ P.R * P.c) * P.q * Wb := by positivity
  have h2 : (0 : ℝ) ≤ 5 + (2 ^ P.R * P.c) + P.M * (P.S + Wb) + 9 * (2 ^ P.R * P.c) + P.M +
      10 * P.M ^ 2 * (2 ^ P.R * P.c) := by positivity
  linarith

/-- The Siegel coefficients are bounded by `feldmanCoeffBound`. -/
theorem abs_feldmanCoeff_le_bound {p : Fin (m + 1) → ℕ} {b : Fin (m + 1) → ℤ} (hp : ∀ j, 1 ≤ p j)
    (hB : 0 < b (Fin.last m)) (hb : ∀ j, |b j| ≤ b (Fin.last m)) {N q S X₀ : ℕ} (hq : 1 ≤ q)
    {x σ : ℕ} (hx : x < X₀) (hσ : σ < S) {τ : Fin m → ℕ} (hτ : ∀ j, τ j < S)
    (kl : FeldmanIndex N q m) :
    |(feldmanCoeff p b N q S σ τ x kl : ℝ)| ≤
      feldmanCoeffBound m N q S X₀ (b (Fin.last m)) (totalLogSum p) := by
  refine (abs_feldmanCoeff_le hp hB hb hσ τ x kl).trans ?_
  unfold feldmanCoeffBound
  have hxX : (x : ℝ) ≤ X₀ := by exact_mod_cast hx.le
  have hB1 : (1 : ℝ) ≤ b (Fin.last m) := by exact_mod_cast hB
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hbase : (1 : ℝ) ≤ 2 * q * (b (Fin.last m) : ℝ) := by nlinarith
  have hτS : ∑ j, τ j ≤ m * S := by
    calc ∑ j, τ j ≤ ∑ _j : Fin m, S := sum_le_sum fun j _ => (hτ j).le
      _ = m * S := by simp
  have hD : (0 : ℝ) < feldmanDivisor (N + 1) S := by exact_mod_cast feldmanDivisor_pos _ _
  have hW := totalLogSum_nonneg p hp
  have h1 : (2 * q * (b (Fin.last m) : ℝ)) ^ (∑ j, τ j) ≤ (2 * q * (b (Fin.last m) : ℝ)) ^ (m * S) :=
    pow_le_pow_right₀ hbase hτS
  gcongr

/-- **Fel'dman's bound in pivot form.**  If the last coefficient `B` of the form is positive and
largest in absolute value, then `|Λ| ≥ e^{−C₀ (log B + 2)}`, with `C₀` depending only on the number
of primes and on a bound for `Σ log p_j`. -/
theorem exists_feldman_pivot_bound (m Wb : ℕ) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ p : Fin (m + 1) → ℕ, Function.Injective p → (∀ i, (p i).Prime) →
      totalLogSum p ≤ Wb → ∀ b : Fin (m + 1) → ℤ, 0 < b (Fin.last m) →
        (∀ j, |b j| ≤ b (Fin.last m)) →
          Real.exp (-(C₀ * (Real.log (b (Fin.last m)) + 2))) ≤ |primeLogForm p b| := by
  obtain ⟨P⟩ := exists_feldmanParams m (Wb + 1) (by omega)
  refine ⟨feldmanLambdaExponent P + 1, by linarith [feldmanLambdaExponent_nonneg P],
    fun p hpinj hprime hW b hB hb => ?_⟩
  set C₀ := feldmanLambdaExponent P + 1 with hC₀
  have hp1 : ∀ j, 1 ≤ p j := fun j => (hprime j).one_lt.le
  set B : ℝ := (b (Fin.last m) : ℝ) with hBdef
  have hB1 : (1 : ℝ) ≤ B := by rw [hBdef]; exact_mod_cast hB
  have hlogB : 0 ≤ Real.log B := Real.log_nonneg hB1
  set n := ⌈Real.log B⌉₊ + 1 with hn
  have hn1 : 1 ≤ n := by omega
  have hBn : Real.log B ≤ n := by
    have := Nat.le_ceil (Real.log B)
    rw [hn]; push_cast; linarith
  have hnB : (n : ℝ) ≤ Real.log B + 2 := by
    have := Nat.ceil_lt_add_one hlogB
    rw [hn]; push_cast; linarith
  have hC₀0 : 0 < C₀ := by rw [hC₀]; linarith [feldmanLambdaExponent_nonneg P]
  by_contra hcontra
  push Not at hcontra
  set lam := primeLogForm p b with hlam
  have hlamn : |lam| < Real.exp (-((feldmanLambdaExponent P + 1) * n)) := by
    refine hcontra.trans_le (Real.exp_le_exp.mpr ?_)
    rw [← hC₀]
    nlinarith
  -- the parameters
  set N := P.a * n with hN
  set X₀ := P.c * n with hX₀
  have hq1 := P.one_le_q
  have hX₀1 : 1 ≤ X₀ := by rw [hX₀]; exact Nat.one_le_iff_ne_zero.mpr (by
    have := P.one_le_c; positivity)
  have hS : 0 < P.S := by rw [P.S_eq]; omega
  have ha1 : 1 ≤ P.a := by
    by_contra h
    have h0 : P.a = 0 := by omega
    have := P.siegel
    rw [h0, zero_mul] at this
    have : 0 < 2 * P.c * P.S ^ (m + 1) := by have := P.one_le_c; positivity
    omega
  have hcount : 2 * (X₀ * P.S ^ (m + 1)) ≤ (N + 1) * P.q ^ (m + 1) := by
    have h := Nat.mul_le_mul_right n P.siegel
    calc 2 * (X₀ * P.S ^ (m + 1)) = 2 * P.c * P.S ^ (m + 1) * n := by rw [hX₀]; ring
      _ ≤ P.a * P.q ^ (m + 1) * n := h
      _ = N * P.q ^ (m + 1) := by rw [hN]; ring
      _ ≤ (N + 1) * P.q ^ (m + 1) := Nat.mul_le_mul_right _ (Nat.le_succ N)
  set Wt := totalLogSum p with hWt
  have hWt0 : 0 ≤ Wt := totalLogSum_nonneg p hp1
  have hWtb : Wt ≤ ((Wb + 1 : ℕ) : ℝ) := by push_cast; linarith
  set W := baseLogSum p with hWdef
  have hW0 : 0 ≤ W := baseLogSum_nonneg p hp1
  have hWb : W ≤ ((Wb + 1 : ℕ) : ℝ) := (baseLogSum_le_totalLogSum p hp1).trans hWtb
  have hAmax : 0 ≤ feldmanCoeffBound m N P.q P.S X₀ B Wt := by
    unfold feldmanCoeffBound
    have : (0 : ℝ) < feldmanDivisor (N + 1) P.S := by exact_mod_cast feldmanDivisor_pos _ _
    positivity
  obtain ⟨C, hC0, hCvan, hCbound⟩ := exists_feldmanSiegel p b (by omega) hS hcount hAmax
    (fun x hx σ hσ τ hτ kl => abs_feldmanCoeff_le_bound hp1 hB hb hq1 hx hσ hτ kl)
  -- the initial vanishing
  have h0 : ∀ x < X₀, ∀ σ (τ : Fin m → ℕ), σ + ∑ j, τ j < P.S →
      feldmanTrueAux p b N P.q C σ τ (x : ℂ) = 0 := by
    intro x hx σ τ hστ
    have hτ : ∀ j, τ j < P.S := fun j => by
      have := single_le_sum (f := τ) (fun i _ => Nat.zero_le _) (mem_univ j)
      omega
    have hrel := pow_mul_feldmanTrueAux_natCast p b (fun j => (hprime j).pos) hB.ne' C
      (show σ < P.S by omega) τ x
    rw [hCvan x hx σ (by omega) τ hτ, Int.cast_zero, mul_zero] at hrel
    exact (mul_eq_zero.mp hrel).resolve_left (pow_ne_zero _ (by exact_mod_cast hB.ne'))
  -- the extrapolation
  have hΛ : 8 * ((2 ^ P.R * X₀ : ℕ) : ℝ) * P.q * |lam| ≤ 1 := by
    have hy : 8 * ((2 ^ P.R * X₀ : ℕ) : ℝ) * P.q ≤ (feldmanLambdaExponent P + 1) * n := by
      have h16 := sixteen_mul_le_feldmanLambdaExponent P
      have hcast : ((2 ^ P.R * X₀ : ℕ) : ℝ) = (2 : ℝ) ^ P.R * P.c * n := by
        rw [hX₀]; push_cast; ring
      rw [hcast]
      have hn0 : (1 : ℝ) ≤ n := by exact_mod_cast hn1
      have hpos : (0 : ℝ) ≤ 16 * ((2 : ℝ) ^ P.R * P.c) * P.q := by positivity
      nlinarith
    have hy0 : 0 ≤ 8 * ((2 ^ P.R * X₀ : ℕ) : ℝ) * P.q := by positivity
    calc 8 * ((2 ^ P.R * X₀ : ℕ) : ℝ) * P.q * |lam|
        ≤ Real.exp ((feldmanLambdaExponent P + 1) * n) *
            Real.exp (-((feldmanLambdaExponent P + 1) * n)) :=
          mul_le_mul (hy.trans (le_exp_self' _)) hlamn.le (abs_nonneg _) (Real.exp_pos _).le
      _ = 1 := by rw [← Real.exp_add]; simp
  have hext := feldman_extrapolation p b hp1 hB hb hq1 C hCbound feldmanCmax_nonneg
    (X₀ := X₀) (T₀ := P.S) (M := P.M) (R := P.R) hX₀1 le_rfl (by rw [P.S_eq]; omega) hΛ h0
    (fun r hr => feldman_stage_threshold P hn1 hr hB1 hBn hW0 hWb hWt0 hWtb hlamn)
  -- the terminal vanishing
  have hterm : (N + 1) * P.q ^ (m + 1) ≤ 2 ^ P.R * X₀ := by
    have h := Nat.mul_le_mul_right n P.terminal
    calc (N + 1) * P.q ^ (m + 1) ≤ 2 * N * P.q ^ (m + 1) := by
          refine Nat.mul_le_mul_right _ ?_
          rw [hN]; nlinarith
      _ = 2 * P.a * P.q ^ (m + 1) * n := by rw [hN]; ring
      _ ≤ 2 ^ P.R * P.c * n := h
      _ = 2 ^ P.R * X₀ := by rw [hX₀]; ring
  have hCzero := eq_zero_of_feldmanTrueAux_eq_zero p b hpinj hprime C fun x hx =>
    hext x (by omega) 0 0 (by rw [P.S_eq]; simp)
  exact hC0 hCzero

/-! ## The effective bound for every prime family -/

theorem totalLogSum_comp_equiv (p : Fin (m + 1) → ℕ) (σ : Fin (m + 1) ≃ Fin (m + 1)) :
    totalLogSum (p ∘ σ) = totalLogSum p := by
  unfold totalLogSum
  exact Equiv.sum_comp σ (fun j => Real.log (p j))

theorem primeLogForm_comp_equiv (p : Fin (m + 1) → ℕ) (ν : Fin (m + 1) → ℤ)
    (σ : Fin (m + 1) ≃ Fin (m + 1)) (s : ℤ) :
    primeLogForm (p ∘ σ) (fun j => s * ν (σ j)) = s * primeLogForm p ν := by
  unfold primeLogForm
  rw [mul_sum]
  have := Equiv.sum_comp σ (fun j => (s : ℝ) * ((ν j : ℝ) * Real.log (p j)))
  rw [← this]
  refine sum_congr rfl fun j _ => ?_
  simp only [Function.comp, Int.cast_mul]
  ring

variable {d : ℕ}

/-- **The effective Baker bound.**  For distinct primes `p₁, …, p_d` there are `c, C > 0` with
`|Σ νᵢ log pᵢ| ≥ c (2 + |ν|₁)^{−C}` for every nonzero `ν ∈ ℤ^d`. -/
theorem effectiveBakerBound_holds (p : Fin d → ℕ) (hp : Function.Injective p)
    (hprime : ∀ i, (p i).Prime) : EffectiveBakerBound p := by
  rcases d with _ | m
  · exact ⟨1, 1, one_pos, one_pos, fun ν hν => absurd (Subsingleton.elim ν 0) hν⟩
  obtain ⟨C₀, hC₀, hbound⟩ := exists_feldman_pivot_bound m ⌈totalLogSum p⌉₊
  refine ⟨Real.exp (-(2 * C₀)), C₀, Real.exp_pos _, hC₀, fun ν hν => ?_⟩
  obtain ⟨k, hk0, hkmax⟩ := exists_max_pivot ν hν
  set σ := Equiv.swap k (Fin.last m) with hσ
  set s : ℤ := if 0 < ν k then 1 else -1 with hs
  have hs1 : |s| = 1 := by rw [hs]; split_ifs <;> simp
  have hsk : s * ν k = |ν k| := by
    rw [hs]
    split_ifs with h
    · rw [one_mul, abs_of_pos h]
    · rw [abs_of_neg (lt_of_le_of_ne (not_lt.mp h) hk0)]; ring
  set b : Fin (m + 1) → ℤ := fun j => s * ν (σ j) with hbdef
  have hblast : b (Fin.last m) = |ν k| := by
    rw [hbdef]; simp only [hσ, Equiv.swap_apply_right]; exact hsk
  have hbpos : 0 < b (Fin.last m) := by rw [hblast]; exact abs_pos.mpr hk0
  have hbmax : ∀ j, |b j| ≤ b (Fin.last m) := by
    intro j
    rw [hblast, hbdef]
    simp only
    rw [abs_mul, hs1, one_mul, Int.abs_eq_natAbs, Int.abs_eq_natAbs]
    exact_mod_cast hkmax (σ j)
  have hp' : Function.Injective (p ∘ σ) := hp.comp σ.injective
  have hprime' : ∀ i, ((p ∘ σ) i).Prime := fun i => hprime (σ i)
  have hW : totalLogSum (p ∘ σ) ≤ (⌈totalLogSum p⌉₊ : ℝ) := by
    rw [totalLogSum_comp_equiv]; exact Nat.le_ceil _
  have h := hbound (p ∘ σ) hp' hprime' hW b hbpos hbmax
  have hform : |primeLogForm (p ∘ σ) b| = |primeLogForm p ν| := by
    rw [hbdef, primeLogForm_comp_equiv, abs_mul]
    have : |((s : ℤ) : ℝ)| = 1 := by rw [← Int.cast_abs, hs1, Int.cast_one]
    rw [this, one_mul]
  rw [hform] at h
  refine le_trans ?_ h
  -- `e^{−2C₀} (2 + H)^{−C₀} ≤ e^{−C₀ (log |ν_k| + 2)}`
  set x : ℝ := (b (Fin.last m) : ℝ) with hx
  have hx1 : (1 : ℝ) ≤ x := by rw [hx]; exact_mod_cast hbpos
  have hxH : x ≤ 2 + (coeffHeight ν : ℝ) := by
    have hle : (ν k).natAbs ≤ coeffHeight ν :=
      single_le_sum (f := fun i => (ν i).natAbs) (fun i _ => Nat.zero_le _) (mem_univ k)
    have : x = ((ν k).natAbs : ℝ) := by
      rw [hx, hblast, Nat.cast_natAbs, Int.cast_abs]
    rw [this]
    have : ((ν k).natAbs : ℝ) ≤ coeffHeight ν := by exact_mod_cast hle
    linarith
  have hx0 : (0 : ℝ) < x := by linarith
  calc Real.exp (-(2 * C₀)) * (2 + (coeffHeight ν : ℝ)) ^ (-C₀)
      ≤ Real.exp (-(2 * C₀)) * x ^ (-C₀) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hx0 hxH (by linarith))
          (Real.exp_pos _).le
    _ = Real.exp (-(C₀ * (Real.log x + 2))) := by
        rw [Real.rpow_def_of_pos hx0, ← Real.exp_add]; congr 1; ring

end GaloisForLFunctions.RHTower.Matveev
