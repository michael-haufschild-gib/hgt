import GaloisForLFunctions.HTGeometry.SmoothBlockWindow
import GaloisForLFunctions.RHTower.SmoothAFECutoffBounds

/-!
# The direct off-diagonal of the block twisted moment: the envelope

On the Levinson lines `s₁ = σ₀+it`, `s₂ = σ₀−it` the direct side of the product approximate
functional equation is height-independent except for the phase `(mh/nk)^{-it}`, so against the
block window `w` its `(m,n,h,k)`-term is exactly the coefficient times the window's Fourier
transform at `ξ = log(mh) − log(nk)`.  Off the diagonal `mh ≠ nk` the square-root separation

`|log(mh) − log(nk)| ≥ 1/(2√(mh·nk))`

(the near-diagonal has `nk ≤ √(mh·nk)`) and the window decay `(q−p+2η)C_K/(η|ξ|)^K` give, with
the cutoff bound `‖V(u)‖ ≤ C_A u^{-A}`,

`term ≤ (q−p+2η) (C_K/η^K) C_A 2^K x^A (hk)^{K/2−σ₀} · (mn)^{-(A+σ₀−K/2)}`,

which is summable over `(m,n)` as soon as `A + σ₀ − K/2 > 1`, with sum `ζ(A+σ₀−K/2)²`.  No split
of the `(m,n)`-range is needed: the cutoff's polynomial decay at a large `A` pays for the
polynomial growth `(mn)^{K/2}` of the separation, and the price `x^A` is beaten by `η^{-K}` only
because `√(hk·mn)/η ≪ T^{θ−1/2+ε}`, the Levinson threshold `θ < 1/2`.
-/

noncomputable section

namespace RHTower

open Complex MeasureTheory GaloisForLFunctions GaloisForLFunctions.HTGeometry

/-- **Square-root separation of logarithms of distinct positive integers.** -/
theorem inv_two_sqrt_le_abs_log_sub_log {A B : ℕ} (hA : 0 < A) (hB : 0 < B) (hne : A ≠ B) :
    1 / (2 * Real.sqrt ((A : ℝ) * B)) ≤ |Real.log A - Real.log B| := by
  have key : ∀ A B : ℕ, 0 < A → 0 < B → B < A →
      1 / (2 * Real.sqrt ((A : ℝ) * B)) ≤ Real.log A - Real.log B := by
    intro A B hA hB hlt
    have hBr : (0 : ℝ) < B := by exact_mod_cast hB
    have hB1 : (1 : ℝ) ≤ B := by exact_mod_cast hB
    have hBA : (B : ℝ) + 1 ≤ A := by exact_mod_cast hlt
    have h1 : Real.log ((B : ℝ) + 1) - Real.log B ≤ Real.log A - Real.log B := by
      have := Real.log_le_log (by positivity) hBA
      linarith
    have h2 : 1 / ((B : ℝ) + 1) ≤ Real.log ((B : ℝ) + 1) - Real.log B := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < B / (B + 1) by positivity)
      rw [Real.log_div hBr.ne' (by positivity)] at this
      have h3 : (1 : ℝ) - B / (B + 1) = 1 / (B + 1) := by
        field_simp
        ring
      linarith
    have h3 : 1 / (2 * Real.sqrt ((A : ℝ) * B)) ≤ 1 / ((B : ℝ) + 1) := by
      apply one_div_le_one_div_of_le (by positivity)
      have hsq : (B : ℝ) ≤ Real.sqrt (A * B) := by
        rw [Real.le_sqrt (by positivity) (by positivity)]
        nlinarith
      linarith
    linarith
  rcases lt_or_gt_of_ne hne with h | h
  · have := key B A hB hA h
    rw [abs_sub_comm, abs_of_nonneg (by linarith [(by positivity : 0 < 1 / (2 * Real.sqrt ((B : ℝ) * A)))])]
    rwa [mul_comm (A : ℝ) B]
  · have := key A B hA hB h
    rwa [abs_of_nonneg (by linarith [(by positivity : 0 < 1 / (2 * Real.sqrt ((A : ℝ) * B)))])]

/-- One direct off-diagonal term of the block twisted moment, in absolute value: the coefficient
`(mnhk)^{-σ₀}`, the cutoff at `mn/x`, and the window oscillation at `log(mh) − log(nk)`; zero on
the diagonal. -/
def directOffDiagTerm (σ₀ x p q η : ℝ) (h k : ℕ) (P : ℕ × ℕ) : ℝ :=
  if (P.1 + 1) * h ≠ (P.2 + 1) * k then
    (((P.1 + 1 : ℝ) * (P.2 + 1) * ((h : ℝ) * k)) ^ (-σ₀))
      * ‖smoothAFECutoff (((P.1 + 1 : ℝ) * (P.2 + 1)) / x)‖
      * ‖∫ t, blockWindowC p q η t * Complex.exp
          (-((Real.log (((P.1 + 1) * h : ℕ) : ℝ) - Real.log (((P.2 + 1) * k : ℕ) : ℝ)) * t) * I)‖
  else 0

theorem directOffDiagTerm_nonneg (σ₀ x p q η : ℝ) (h k : ℕ) (P : ℕ × ℕ) :
    0 ≤ directOffDiagTerm σ₀ x p q η h k P := by
  unfold directOffDiagTerm
  split_ifs
  · positivity
  · exact le_rfl

/-- The off-diagonal envelope constant. -/
def directOffDiagConst (K : ℕ) (CA A x p q η : ℝ) : ℝ :=
  (q - p + 2 * η) * (blockWindowConst K / η ^ K) * CA * 2 ^ K * x ^ A

theorem directOffDiagConst_nonneg (K : ℕ) {CA A x p q η : ℝ} (hCA : 0 ≤ CA) (hx : 0 < x)
    (hη : 0 < η) (hpq : p ≤ q) : 0 ≤ directOffDiagConst K CA A x p q η := by
  unfold directOffDiagConst
  have := blockWindowConst_nonneg K
  have : 0 ≤ q - p + 2 * η := by linarith
  positivity

/-- **The envelope of one direct off-diagonal term.** -/
theorem directOffDiagTerm_le (K : ℕ) {A CA : ℝ} (hCA0 : 0 ≤ CA)
    (hCA : ∀ {u : ℝ}, 0 < u → ‖smoothAFECutoff u‖ ≤ CA * u ^ (-A))
    {σ₀ x p q η : ℝ} (hx : 0 < x) (hη : 0 < η) (hpq : p ≤ q) {h k : ℕ} (hh : 0 < h)
    (hk : 0 < k) (P : ℕ × ℕ) :
    directOffDiagTerm σ₀ x p q η h k P
      ≤ directOffDiagConst K CA A x p q η * ((h : ℝ) * k) ^ ((K : ℝ) / 2 - σ₀)
        * (((P.1 + 1 : ℝ) * (P.2 + 1)) ^ (-(A + σ₀ - (K : ℝ) / 2))) := by
  unfold directOffDiagTerm
  split_ifs with hne
  · -- notation
    have hm : (0 : ℝ) < P.1 + 1 := by positivity
    have hn : (0 : ℝ) < P.2 + 1 := by positivity
    have hhr : (0 : ℝ) < h := by exact_mod_cast hh
    have hkr : (0 : ℝ) < k := by exact_mod_cast hk
    set mn : ℝ := (P.1 + 1 : ℝ) * (P.2 + 1) with hmn
    set hk' : ℝ := (h : ℝ) * k with hhk
    have hmn0 : 0 < mn := by positivity
    have hhk0 : 0 < hk' := by positivity
    -- the frequency and its separation
    have hAn : 0 < (P.1 + 1) * h := by positivity
    have hBn : 0 < (P.2 + 1) * k := by positivity
    have hsep := inv_two_sqrt_le_abs_log_sub_log hAn hBn hne
    set ξ : ℝ := Real.log (((P.1 + 1) * h : ℕ) : ℝ) - Real.log (((P.2 + 1) * k : ℕ) : ℝ) with hξ
    have hprod : ((((P.1 + 1) * h : ℕ) : ℝ) * (((P.2 + 1) * k : ℕ) : ℝ)) = mn * hk' := by
      push_cast
      ring
    have hξ0 : ξ ≠ 0 := by
      intro h0
      rw [h0, abs_zero] at hsep
      have : (0 : ℝ) < 1 / (2 * Real.sqrt ((((P.1 + 1) * h : ℕ) : ℝ) * (((P.2 + 1) * k : ℕ) : ℝ))) := by
        rw [hprod]
        positivity
      linarith
    -- window decay
    have hwin := norm_integral_blockWindowC_mul_cexp_le K hη hpq hξ0
    have hinv : 1 / |ξ| ^ K ≤ 2 ^ K * (mn * hk') ^ ((K : ℝ) / 2) := by
      have h1 : 1 / |ξ| ≤ 2 * Real.sqrt (mn * hk') := by
        rw [← hprod]
        have hpos : 0 < 2 * Real.sqrt ((((P.1 + 1) * h : ℕ) : ℝ) * (((P.2 + 1) * k : ℕ) : ℝ)) := by
          rw [hprod]; positivity
        rw [div_le_iff₀ (abs_pos.mpr hξ0)]
        have := hsep
        rw [div_le_iff₀ hpos] at this
        linarith
      have h2 : (1 / |ξ|) ^ K ≤ (2 * Real.sqrt (mn * hk')) ^ K :=
        pow_le_pow_left₀ (by positivity) h1 K
      rw [one_div_pow] at h2
      refine h2.trans (le_of_eq ?_)
      rw [mul_pow, Real.sqrt_eq_rpow, ← Real.rpow_mul_natCast (by positivity),
        show (1 / 2 : ℝ) * K = (K : ℝ) / 2 by ring]
    -- cutoff decay
    have hcut : ‖smoothAFECutoff (mn / x)‖ ≤ CA * x ^ A * mn ^ (-A) := by
      refine (hCA (by positivity)).trans (le_of_eq ?_)
      rw [Real.div_rpow hmn0.le hx.le, Real.rpow_neg hmn0.le, Real.rpow_neg hx.le]
      field_simp
    -- assemble
    have hcoef : (mn * hk') ^ (-σ₀) = mn ^ (-σ₀) * hk' ^ (-σ₀) :=
      Real.mul_rpow hmn0.le hhk0.le
    have hsplit : (mn * hk') ^ ((K : ℝ) / 2) = mn ^ ((K : ℝ) / 2) * hk' ^ ((K : ℝ) / 2) :=
      Real.mul_rpow hmn0.le hhk0.le
    have hwin' : ‖∫ t, blockWindowC p q η t * Complex.exp (-(ξ * t) * I)‖
        ≤ (q - p + 2 * η) * (blockWindowConst K / η ^ K)
            * (2 ^ K * (mn ^ ((K : ℝ) / 2) * hk' ^ ((K : ℝ) / 2))) := by
      refine hwin.trans ?_
      rw [div_eq_mul_one_div]
      refine mul_le_mul_of_nonneg_left ?_ (by
        have := blockWindowConst_nonneg K
        have : 0 ≤ q - p + 2 * η := by linarith
        positivity)
      rw [← hsplit]
      exact hinv
    have hlen : 0 ≤ q - p + 2 * η := by linarith
    have hC : 0 ≤ blockWindowConst K := blockWindowConst_nonneg K
    have hcast : ∀ t : ℝ, (-((((Real.log (((P.1 + 1) * h : ℕ) : ℝ) : ℝ) : ℂ)
        - ((Real.log (((P.2 + 1) * k : ℕ) : ℝ) : ℝ) : ℂ)) * (t : ℂ)) * I)
        = -((ξ : ℂ) * t) * I := by
      intro t
      rw [hξ]
      push_cast
      ring
    simp only [hcast]
    calc (mn * hk') ^ (-σ₀) * ‖smoothAFECutoff (mn / x)‖
          * ‖∫ t, blockWindowC p q η t * Complex.exp (-(ξ * t) * I)‖
        ≤ (mn * hk') ^ (-σ₀) * (CA * x ^ A * mn ^ (-A))
            * ((q - p + 2 * η) * (blockWindowConst K / η ^ K)
              * (2 ^ K * (mn ^ ((K : ℝ) / 2) * hk' ^ ((K : ℝ) / 2)))) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hcut (by positivity)) hwin' (norm_nonneg _)
            (by positivity)
      _ = directOffDiagConst K CA A x p q η * hk' ^ ((K : ℝ) / 2 - σ₀)
            * mn ^ (-(A + σ₀ - (K : ℝ) / 2)) := by
          rw [hcoef, directOffDiagConst,
            show hk' ^ ((K : ℝ) / 2 - σ₀) = hk' ^ ((K : ℝ) / 2) * hk' ^ (-σ₀) by
              rw [← Real.rpow_add hhk0]; ring_nf,
            show mn ^ (-(A + σ₀ - (K : ℝ) / 2)) = mn ^ (-σ₀) * mn ^ (-A) * mn ^ ((K : ℝ) / 2) by
              rw [← Real.rpow_add hmn0, ← Real.rpow_add hmn0]; ring_nf]
          ring
  · exact mul_nonneg (mul_nonneg (directOffDiagConst_nonneg K hCA0 hx hη hpq) (by positivity))
      (by positivity)

/-! ## Summation over the pairs `(m,n)` -/

theorem summable_nat_succ_rpow_neg {r : ℝ} (hr : 1 < r) :
    Summable (fun n : ℕ => ((n : ℝ) + 1) ^ (-r)) := by
  have h := (Real.summable_nat_rpow_inv (p := r)).mpr hr
  have h' := (summable_nat_add_iff (f := fun n : ℕ => ((n : ℝ) ^ r)⁻¹) 1).mpr h
  refine h'.congr fun n => ?_
  simp only [Nat.cast_add, Nat.cast_one]
  rw [Real.rpow_neg (by positivity)]

theorem summable_prod_succ_rpow_neg {r : ℝ} (hr : 1 < r) :
    Summable (fun P : ℕ × ℕ => ((P.1 + 1 : ℝ) * (P.2 + 1)) ^ (-r)) := by
  have h := (summable_nat_succ_rpow_neg hr).mul_of_nonneg (summable_nat_succ_rpow_neg hr)
    (fun n => by positivity) (fun n => by positivity)
  refine h.congr fun P => ?_
  rw [Real.mul_rpow (by positivity) (by positivity)]

theorem tsum_prod_succ_rpow_neg {r : ℝ} (hr : 1 < r) :
    ∑' P : ℕ × ℕ, ((P.1 + 1 : ℝ) * (P.2 + 1)) ^ (-r)
      = (∑' n : ℕ, ((n : ℝ) + 1) ^ (-r)) ^ 2 := by
  rw [sq, Summable.tsum_mul_tsum (summable_nat_succ_rpow_neg hr) (summable_nat_succ_rpow_neg hr)
    ((summable_nat_succ_rpow_neg hr).mul_of_nonneg (summable_nat_succ_rpow_neg hr)
      (fun n => by positivity) (fun n => by positivity))]
  refine tsum_congr fun P => ?_
  rw [Real.mul_rpow (by positivity) (by positivity)]

/-- **The direct off-diagonal envelope, summed over `(m,n)`.** -/
theorem tsum_directOffDiagTerm_le (K : ℕ) {A CA : ℝ} (hCA0 : 0 ≤ CA)
    (hCA : ∀ {u : ℝ}, 0 < u → ‖smoothAFECutoff u‖ ≤ CA * u ^ (-A))
    {σ₀ x p q η : ℝ} (hr : 1 < A + σ₀ - (K : ℝ) / 2) (hx : 0 < x) (hη : 0 < η) (hpq : p ≤ q)
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k) :
    ∑' P : ℕ × ℕ, directOffDiagTerm σ₀ x p q η h k P
      ≤ directOffDiagConst K CA A x p q η * ((h : ℝ) * k) ^ ((K : ℝ) / 2 - σ₀)
        * (∑' n : ℕ, ((n : ℝ) + 1) ^ (-(A + σ₀ - (K : ℝ) / 2))) ^ 2 := by
  have hbound := fun P => directOffDiagTerm_le K hCA0 hCA hx hη hpq hh hk (σ₀ := σ₀) P
  have hsum : Summable (fun P : ℕ × ℕ => directOffDiagConst K CA A x p q η
      * ((h : ℝ) * k) ^ ((K : ℝ) / 2 - σ₀)
      * (((P.1 + 1 : ℝ) * (P.2 + 1)) ^ (-(A + σ₀ - (K : ℝ) / 2)))) :=
    (summable_prod_succ_rpow_neg hr).mul_left _
  have hterm : Summable (fun P : ℕ × ℕ => directOffDiagTerm σ₀ x p q η h k P) :=
    Summable.of_nonneg_of_le (fun P => directOffDiagTerm_nonneg _ _ _ _ _ _ _ P) hbound hsum
  calc ∑' P : ℕ × ℕ, directOffDiagTerm σ₀ x p q η h k P
      ≤ ∑' P : ℕ × ℕ, directOffDiagConst K CA A x p q η
          * ((h : ℝ) * k) ^ ((K : ℝ) / 2 - σ₀)
          * (((P.1 + 1 : ℝ) * (P.2 + 1)) ^ (-(A + σ₀ - (K : ℝ) / 2))) :=
        Summable.tsum_le_tsum hbound hterm hsum
    _ = directOffDiagConst K CA A x p q η * ((h : ℝ) * k) ^ ((K : ℝ) / 2 - σ₀)
          * (∑' n : ℕ, ((n : ℝ) + 1) ^ (-(A + σ₀ - (K : ℝ) / 2))) ^ 2 := by
        rw [tsum_mul_left, tsum_prod_succ_rpow_neg hr]

end RHTower

end
