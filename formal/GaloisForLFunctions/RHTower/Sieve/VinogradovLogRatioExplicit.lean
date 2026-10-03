import GaloisForLFunctions.RHTower.Sieve.VinogradovLogPhaseShift

/-!
# The logarithmic ratio sum with the explicit mean value theorem

`R(t, x, Q) = Σ_{l,m<Q} e((t/2π) log(1 - (Q+l)(Q+m)/x))` is, up to the Taylor remainder of the
logarithm, the upper-half bilinear sum with coefficients `-α_j`,
`α_j = t / (2π (j+1) x^{j+1})` (`logTaylorMagnitude`).  On a set `U` of coordinates with

`P^{2e_j} ≤ α_j P^{2(j+1)}`,   `α_j (P^{2e_j} + 1) ≤ 1`,   `32b²(1 + log(2/α_j)) ≤ P^{e_j}`

(`P = 2Q`), the unit fractions `1/⌊1/α_j⌋` are admissible rational approximations, and

`‖R(t,x,Q)‖ ≤ (C_{k,b}² (24b²)^k P^{8b² + 2Kθ^{b/k}} / P^{Σ_U e_j})^{1/(4b²)}
            + 2π (t/π) (P²/x)^{k+1} Q²`

(`norm_routeTLogRatioBilinearSum_le_explicit`), whenever `4P² ≤ x`.
-/

namespace RHTower.Sieve

open scoped BigOperators

noncomputable section

theorem le_rpow_inv_nat_of_pow_le' {x y : ℝ} {n : ℕ} (hn : n ≠ 0) (hy : 0 ≤ y)
    (hxy : x ^ n ≤ y) : x ≤ y ^ ((n : ℝ)⁻¹) := by
  apply le_of_pow_le_pow_left₀ hn (Real.rpow_nonneg hy _)
  rw [Real.rpow_inv_natCast_pow hy hn]
  exact hxy

/-- `q = ⌊1/α⌋` approximates `α ∈ (0, 1]` by `1/q` within `1/q²`. -/
theorem unit_fraction_floor_approx {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) :
    0 < ⌊1 / α⌋₊ ∧ (⌊1 / α⌋₊ : ℝ) ≤ 1 / α ∧ 1 / α < ⌊1 / α⌋₊ + 1 ∧
      |α - (1 : ℝ) / (⌊1 / α⌋₊ : ℝ)| ≤ 1 / (⌊1 / α⌋₊ : ℝ) ^ (2 : ℕ) := by
  set y := 1 / α with hy
  have hy1 : 1 ≤ y := by rw [hy, le_div_iff₀ hα0]; linarith
  refine ⟨Nat.floor_pos.mpr hy1, Nat.floor_le (by linarith), Nat.lt_floor_add_one y, ?_⟩
  set q := ⌊y⌋₊
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.floor_pos.mpr hy1
  have hq0 : (0 : ℝ) < q := by linarith
  have hqy : (q : ℝ) ≤ y := Nat.floor_le (by linarith)
  have hyq : y < q + 1 := Nat.lt_floor_add_one y
  have hαy : α = 1 / y := by rw [hy]; field_simp
  have hupper : α ≤ 1 / q := by
    rw [hαy]; exact one_div_le_one_div_of_le hq0 hqy
  have hlower : 1 / ((q : ℝ) + 1) < α := by
    rw [hαy]; exact one_div_lt_one_div_of_lt (by linarith) hyq
  rw [abs_of_nonpos (by linarith)]
  have h : 1 / (q : ℝ) - 1 / ((q : ℝ) + 1) ≤ 1 / (q : ℝ) ^ 2 := by
    rw [div_sub_div _ _ hq0.ne' (by linarith), div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  linarith

/-- **The logarithmic ratio sum with the explicit mean value theorem.** -/
theorem norm_routeTLogRatioBilinearSum_le_explicit
    {t x : ℝ} {k b Q : ℕ} (ht : 0 < t) (hx : 0 < x) (hk : 3 ≤ k) (hb : 1 ≤ b) (hQ : 1 ≤ Q)
    (hscale : 4 * ((2 * Q : ℕ) : ℝ) ^ 2 ≤ x)
    (U : Fin k → Prop) [DecidablePred U] (e : Fin k → ℕ)
    (he : ∀ j, U j → 2 * e j ≤ j.val + 1)
    (hlow : ∀ j, U j → ((2 * Q : ℕ) : ℝ) ^ (2 * e j) ≤
      logTaylorMagnitude t x j * ((2 * Q : ℕ) : ℝ) ^ (2 * (j.val + 1)))
    (hup : ∀ j, U j → logTaylorMagnitude t x j * (((2 * Q : ℕ) : ℝ) ^ (2 * e j) + 1) ≤ 1)
    (habs : ∀ j, U j → 32 * (b : ℝ) ^ 2 * (1 + Real.log (2 / logTaylorMagnitude t x j)) ≤
      ((2 * Q : ℕ) : ℝ) ^ e j) :
    ‖routeTLogRatioBilinearSum t x Q‖ ≤
      (vinogradovExplicitConstant k b ^ 2 * (24 * (b : ℝ) ^ 2) ^ k *
        ((2 * Q : ℕ) : ℝ) ^ (8 * (b : ℝ) ^ 2 +
          2 * ((k * (k + 1) / 2 : ℝ) * (1 - 1 / (k : ℝ)) ^ ((b : ℝ) / k))) *
        (((2 * Q : ℕ) : ℝ) ^ (∑ j ∈ (Finset.univ : Finset (Fin k)).filter U, e j))⁻¹) ^
          ((((4 * b ^ 2 : ℕ) : ℝ))⁻¹) +
      2 * Real.pi * (t / Real.pi * (((2 * Q : ℕ) : ℝ) ^ 2 / x) ^ (k + 1)) * (Q : ℝ) ^ 2 := by
  classical
  set P : ℝ := ((2 * Q : ℕ) : ℝ) with hPdef
  have hP1 : (1 : ℝ) ≤ P := by rw [hPdef]; exact_mod_cast (by omega : 1 ≤ 2 * Q)
  set α : Fin k → ℝ := fun j => logTaylorMagnitude t x j with hαdef
  have hαpos : ∀ j, 0 < α j := fun j => logTaylorMagnitude_pos ht hx j
  have hα1 : ∀ j, U j → α j ≤ 1 := by
    intro j hj
    have h := hup j hj
    have hpow : (1 : ℝ) ≤ P ^ (2 * e j) + 1 := by
      have : (0 : ℝ) ≤ P ^ (2 * e j) := by positivity
      linarith
    have := hαpos j
    nlinarith
  set q : Fin k → ℕ := fun j => if U j then ⌊1 / α j⌋₊ else 1 with hqdef
  set a : Fin k → ℕ := fun _ => 1 with hadef
  have hqU : ∀ j, U j → q j = ⌊1 / α j⌋₊ := fun j hj => by simp [hqdef, hj]
  have happ : ∀ j, U j → _ := fun j hj => unit_fraction_floor_approx (hαpos j) (hα1 j hj)
  have hq : ∀ j, U j → 0 < q j := fun j hj => by rw [hqU j hj]; exact (happ j hj).1
  have hcop : ∀ j, U j → Nat.Coprime (a j) (q j) := fun j _ => Nat.coprime_one_left _
  have happrox : ∀ j, U j → |α j - (a j : ℝ) / (q j : ℝ)| ≤ 1 / (q j : ℝ) ^ (2 : ℕ) := by
    intro j hj
    rw [hqU j hj]
    simpa [hadef] using (happ j hj).2.2.2
  have hRq : ∀ j, U j → (2 * Q) ^ (2 * e j) ≤ q j := by
    intro j hj
    rw [hqU j hj]
    have h1 := (happ j hj).2.2.1
    have hinv : P ^ (2 * e j) + 1 ≤ 1 / α j := by
      rw [le_div_iff₀ (hαpos j)]
      linarith [hup j hj]
    have : (((2 * Q) ^ (2 * e j) : ℕ) : ℝ) < (⌊1 / α j⌋₊ : ℝ) + 1 := by
      rw [hPdef] at hinv
      push_cast at hinv ⊢
      linarith
    have := this
    exact_mod_cast (Nat.lt_add_one_iff.mp (by exact_mod_cast this))
  have hqR : ∀ j, U j → q j * (2 * Q) ^ (2 * e j) ≤ ((2 * Q) ^ (j.val + 1)) ^ (2 : ℕ) := by
    intro j hj
    rw [hqU j hj]
    have h1 : (⌊1 / α j⌋₊ : ℝ) ≤ 1 / α j := (happ j hj).2.1
    have h2 := hlow j hj
    have hreal : (⌊1 / α j⌋₊ : ℝ) * P ^ (2 * e j) ≤ P ^ (2 * (j.val + 1)) := by
      calc (⌊1 / α j⌋₊ : ℝ) * P ^ (2 * e j) ≤ (1 / α j) * (α j * P ^ (2 * (j.val + 1))) :=
            mul_le_mul h1 h2 (pow_nonneg (by linarith) _) (div_nonneg zero_le_one (hαpos j).le)
        _ = P ^ (2 * (j.val + 1)) := by field_simp [(hαpos j).ne']
    have : ((⌊1 / α j⌋₊ * (2 * Q) ^ (2 * e j) : ℕ) : ℝ) ≤
        ((((2 * Q) ^ (j.val + 1)) ^ (2 : ℕ) : ℕ) : ℝ) := by
      push_cast
      rw [hPdef] at hreal
      push_cast at hreal
      rw [← pow_mul, mul_comm (j.val + 1) 2]
      exact hreal
    exact_mod_cast this
  have habsorb : ∀ j, U j →
      32 * (b : ℝ) ^ (2 : ℕ) * (1 + Real.log ((q j : ℝ) + 1)) ≤ ((2 * Q : ℕ) : ℝ) ^ e j := by
    intro j hj
    rw [hqU j hj]
    have h1 : (⌊1 / α j⌋₊ : ℝ) + 1 ≤ 2 / α j := by
      have := (happ j hj).2.1
      have h2 : 1 ≤ 1 / α j := by rw [le_div_iff₀ (hαpos j)]; linarith [hα1 j hj]
      have : 1 / α j + 1 ≤ 2 / α j := by
        have e2 : 2 / α j = 1 / α j + 1 / α j := by ring
        linarith
      linarith
    have hlog : Real.log ((⌊1 / α j⌋₊ : ℝ) + 1) ≤ Real.log (2 / α j) :=
      Real.log_le_log (by positivity) h1
    have hb2 : (0 : ℝ) ≤ 32 * (b : ℝ) ^ 2 := by positivity
    calc 32 * (b : ℝ) ^ (2 : ℕ) * (1 + Real.log ((⌊1 / α j⌋₊ : ℝ) + 1))
        ≤ 32 * (b : ℝ) ^ 2 * (1 + Real.log (2 / α j)) := by
          apply mul_le_mul_of_nonneg_left _ hb2; linarith
      _ ≤ _ := habs j hj
  -- the bilinear bound for the positive coefficients
  have hW1 := norm_vinogradovUpperHalfBilinearSum_pow_le_explicit hk hb hQ α U a q e hq hcop
    happrox he hRq hqR habsorb
  have hbound0 : 0 ≤ vinogradovExplicitConstant k b ^ 2 * (24 * (b : ℝ) ^ 2) ^ k *
      ((2 * Q : ℕ) : ℝ) ^ (8 * (b : ℝ) ^ 2 +
        2 * ((k * (k + 1) / 2 : ℝ) * (1 - 1 / (k : ℝ)) ^ ((b : ℝ) / k))) *
      (((2 * Q : ℕ) : ℝ) ^ (∑ j ∈ (Finset.univ : Finset (Fin k)).filter U, e j))⁻¹ := by
    have := Real.rpow_nonneg (show (0 : ℝ) ≤ ((2 * Q : ℕ) : ℝ) by positivity)
      (8 * (b : ℝ) ^ 2 + 2 * ((k * (k + 1) / 2 : ℝ) * (1 - 1 / (k : ℝ)) ^ ((b : ℝ) / k)))
    positivity
  have hroot := le_rpow_inv_nat_of_pow_le' (by positivity : 4 * b ^ 2 ≠ 0) hbound0 hW1
  -- negation and Taylor perturbation
  have hneg := norm_vinogradovUpperHalfBilinearSum_neg (Q := Q) α
  set η : ℝ := t / Real.pi * (((2 * Q : ℕ) : ℝ) ^ 2 / x) ^ (k + 1) with hηdef
  have herr : ∀ l m, |routeTLogTaylorError t x Q k l m| ≤ η := by
    intro l m
    have h := routeTLogTaylorError_bound ht hx hQ hscale (k := k) l m
    have hy0 : 0 ≤ vinogradovUpperHalfProduct Q l m := by
      unfold vinogradovUpperHalfProduct; positivity
    have hy : vinogradovUpperHalfProduct Q l m ≤ ((2 * Q : ℕ) : ℝ) ^ 2 := by
      unfold vinogradovUpperHalfProduct
      have hl : (((Q + l.val : ℕ) : ℝ)) ≤ (2 * Q : ℕ) := by
        exact_mod_cast (show Q + l.val ≤ 2 * Q by omega)
      have hm : (((Q + m.val : ℕ) : ℝ)) ≤ (2 * Q : ℕ) := by
        exact_mod_cast (show Q + m.val ≤ 2 * Q by omega)
      rw [pow_two]
      exact mul_le_mul hl hm (by positivity) (by positivity)
    have hpow : (vinogradovUpperHalfProduct Q l m / x) ^ (k + 1) ≤
        (((2 * Q : ℕ) : ℝ) ^ 2 / x) ^ (k + 1) :=
      pow_le_pow_left₀ (div_nonneg hy0 hx.le) (div_le_div_of_nonneg_right hy hx.le) _
    calc |routeTLogTaylorError t x Q k l m|
        ≤ t / (2 * Real.pi) * (2 * (vinogradovUpperHalfProduct Q l m / x) ^ (k + 1)) := h
      _ ≤ t / (2 * Real.pi) * (2 * (((2 * Q : ℕ) : ℝ) ^ 2 / x) ^ (k + 1)) := by
          gcongr
      _ = η := by rw [hηdef]; field_simp
  have hpert := norm_vinogradovUpperHalfPerturbedBilinearSum_sub_le
    (fun j : Fin k => -logTaylorMagnitude t x j) (routeTLogTaylorError t x Q k) herr
  rw [← vinogradovUpperHalfPerturbed_logTaylor_eq_ratio (t := t) (x := x) (Q := Q) (k := k)]
  calc ‖vinogradovUpperHalfPerturbedBilinearSum (fun j : Fin k => -logTaylorMagnitude t x j)
        (routeTLogTaylorError t x Q k)‖
      ≤ ‖vinogradovUpperHalfBilinearSum Q (fun j : Fin k => -logTaylorMagnitude t x j)‖ +
        ‖vinogradovUpperHalfPerturbedBilinearSum (fun j : Fin k => -logTaylorMagnitude t x j)
            (routeTLogTaylorError t x Q k) -
          vinogradovUpperHalfBilinearSum Q (fun j : Fin k => -logTaylorMagnitude t x j)‖ :=
        norm_le_norm_add_norm_sub' _ _
    _ ≤ _ := by
        apply add_le_add _ hpert
        rw [show (fun j : Fin k => -logTaylorMagnitude t x j) = (fun j => -α j) from rfl, hneg]
        exact hroot

end

end RHTower.Sieve
