import GaloisForLFunctions.HTGeometry.PurityRankBarrier

/-!
# An inverse-square tail and a four-amplitude phase witness

The tail of the inverse-square series past `K` is at most `1/K - 1/L`, because `1/j² ≤ 1/(j(j-1))`
and the latter telescopes.

Separately, if four diagonal amplitudes of a unitary are `1,1,1,e^{-iφ}` and an approximant within
`ε` satisfies the factorization identity `W₀₀W₁₁ = W₀₁W₁₀`, then inserting and subtracting the two
products bounds `|e^{-iφ} - 1|` by `4ε`: each of the four substitutions costs at most `ε`, since
every factor has modulus at most one.
-/

open Finset

namespace GaloisForLFunctions.HTGeometry

/-! ## The inverse-square tail -/

/-- **`(8)`: the inverse-square tail telescopes.** -/
theorem sum_inv_sq_Ioc_le (K : ℕ) (hK : 1 ≤ K) :
    ∀ L : ℕ, K ≤ L → ∑ j ∈ Finset.Ioc K L, (1 : ℝ) / (j : ℝ) ^ (2 : ℕ)
      ≤ 1 / (K : ℝ) - 1 / (L : ℝ) := by
  intro L
  induction L with
  | zero =>
    intro h
    have : K = 0 := Nat.le_zero.mp h
    omega
  | succ L ih =>
    intro hKL
    rcases Nat.lt_or_ge K (L + 1) with hlt | hge
    · have hKle : K ≤ L := Nat.lt_succ_iff.mp hlt
      rw [Finset.sum_Ioc_succ_top hKle]
      have hprev := ih hKle
      have hLpos : (0 : ℝ) < L := by
        have : 1 ≤ L := le_trans hK hKle
        exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one this
      have hL1pos : (0 : ℝ) < (L : ℝ) + 1 := by linarith
      have hstep : (1 : ℝ) / ((L : ℝ) + 1) ^ (2 : ℕ) ≤ 1 / (L : ℝ) - 1 / ((L : ℝ) + 1) := by
        have h : (1 : ℝ) / (L : ℝ) - 1 / ((L : ℝ) + 1) = 1 / ((L : ℝ) * ((L : ℝ) + 1)) := by
          field_simp
          ring
        rw [h]
        refine one_div_le_one_div_of_le (by positivity) ?_
        nlinarith [hLpos]
      have hcast : ((L + 1 : ℕ) : ℝ) = (L : ℝ) + 1 := by push_cast; ring
      rw [hcast]
      linarith [hprev, hstep]
    · have hKeq : K = L + 1 := le_antisymm hKL hge
      subst hKeq
      simp

/-! ## The four-amplitude phase witness -/

/-- **`(14)`: the four-amplitude phase witness.**  Under the factorization identity, a unitary whose
four diagonal amplitudes are `1,1,1,e^{-iφ}` forces its `ε`-approximant to see the phase. -/
theorem norm_sub_one_le_four_mul {u w₀₀ w₀₁ w₁₀ w₁₁ : ℂ} {ε : ℝ}
    (hfac : w₀₀ * w₁₁ = w₀₁ * w₁₀)
    (h₀₀ : ‖(1 : ℂ) - w₀₀‖ ≤ ε) (h₀₁ : ‖(1 : ℂ) - w₀₁‖ ≤ ε)
    (h₁₀ : ‖(1 : ℂ) - w₁₀‖ ≤ ε) (h₁₁ : ‖u - w₁₁‖ ≤ ε)
    (n₀₁ : ‖w₀₁‖ ≤ 1) (n₁₁ : ‖w₁₁‖ ≤ 1) :
    ‖u - 1‖ ≤ 4 * ε := by
  have hleft : ‖u - w₀₀ * w₁₁‖ ≤ 2 * ε := by
    have hsplit : u - w₀₀ * w₁₁ = (u - w₁₁) + w₁₁ * (1 - w₀₀) := by ring
    calc ‖u - w₀₀ * w₁₁‖ = ‖(u - w₁₁) + w₁₁ * (1 - w₀₀)‖ := by rw [hsplit]
      _ ≤ ‖u - w₁₁‖ + ‖w₁₁ * (1 - w₀₀)‖ := norm_add_le _ _
      _ = ‖u - w₁₁‖ + ‖w₁₁‖ * ‖(1 : ℂ) - w₀₀‖ := by rw [norm_mul]
      _ ≤ 2 * ε := by nlinarith [h₁₁, h₀₀, n₁₁, norm_nonneg ((1 : ℂ) - w₀₀), norm_nonneg w₁₁]
  have hright : ‖w₀₁ * w₁₀ - 1‖ ≤ 2 * ε := by
    have hsplit : w₀₁ * w₁₀ - 1 = w₀₁ * (w₁₀ - 1) + (w₀₁ - 1) := by ring
    calc ‖w₀₁ * w₁₀ - 1‖ = ‖w₀₁ * (w₁₀ - 1) + (w₀₁ - 1)‖ := by rw [hsplit]
      _ ≤ ‖w₀₁ * (w₁₀ - 1)‖ + ‖w₀₁ - 1‖ := norm_add_le _ _
      _ = ‖w₀₁‖ * ‖w₁₀ - 1‖ + ‖w₀₁ - 1‖ := by rw [norm_mul]
      _ ≤ 2 * ε := by
          have e1 : ‖w₁₀ - 1‖ = ‖(1 : ℂ) - w₁₀‖ := norm_sub_rev _ _
          have e2 : ‖w₀₁ - 1‖ = ‖(1 : ℂ) - w₀₁‖ := norm_sub_rev _ _
          rw [e1, e2]
          nlinarith [h₀₁, h₁₀, n₀₁, norm_nonneg ((1 : ℂ) - w₁₀)]
  calc ‖u - 1‖ = ‖(u - w₀₀ * w₁₁) + (w₀₁ * w₁₀ - 1)‖ := by rw [hfac]; ring_nf
    _ ≤ ‖u - w₀₀ * w₁₁‖ + ‖w₀₁ * w₁₀ - 1‖ := norm_add_le _ _
    _ ≤ 4 * ε := by linarith

/-! ## The operator ramp of Lemma 2 -/

section Ramp

open _root_.Matrix

/-- A phase differs from one by at most its argument. -/
theorem norm_expI_sub_one_le (x : ℝ) :
    ‖Complex.exp (-(x : ℂ) * Complex.I) - 1‖ ≤ |x| := by
  have hzero : Complex.exp (-((0 : ℝ) : ℂ) * Complex.I) = 1 := by
    norm_num
  have h := norm_expI_sub_eq x 0
  rw [hzero] at h
  rw [h]
  have hsin : |Real.sin ((x - 0) / 2)| ≤ |(x - 0) / 2| := Real.abs_sin_le_abs
  have habs : |(x - 0) / 2| = |x| / 2 := by
    rw [sub_zero, abs_div]
    norm_num
  rw [habs] at hsin
  linarith

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **`(10)`: the ramp bound.**  A diagonal self-adjoint generator of norm at most `c` moves every
vector by at most `\|t\| c` under `e^{-itR} - I`. -/
theorem ramp_bound (r : n → ℝ) (t : ℝ) {c : ℝ} (hc : ∀ j, |r j| ≤ c) (v : n → ℂ) :
    ∑ l, ‖((Matrix.diagonal (fun j => Complex.exp (-((t * r j : ℝ) : ℂ) * Complex.I) - 1))
        *ᵥ v) l‖ ^ (2 : ℕ)
      ≤ (|t| * c) ^ (2 : ℕ) * ∑ l, ‖v l‖ ^ (2 : ℕ) := by
  refine diagonal_mulVec_norm_le _ (fun l => ?_) v
  refine le_trans (norm_expI_sub_one_le (t * r l)) ?_
  rw [abs_mul]
  have hnn : (0 : ℝ) ≤ |t| := abs_nonneg t
  exact mul_le_mul_of_nonneg_left (hc l) hnn

end Ramp


/-! ## The assembled ramp of Lemma 2 -/

/-- **`(11)`: the omitted Hamiltonian costs less than `ε`.**  With `K₊ ≥ 2t/ε` and `t ≤ εL/2`, the
two contributions to `t‖R‖` are at most `ε/2` and `ε/(2L)`. -/
theorem ramp_total_lt {t ε L K R : ℝ} (hε : 0 < ε) (hL : 1 < L) (ht : 0 ≤ t) (hK : 0 < K)
    (hKlb : 2 * t / ε ≤ K) (htL : t ≤ ε * L / 2)
    (hR : R ≤ 1 / K + (L - 1) / L ^ (3 : ℕ)) :
    t * R < ε := by
  have hLpos : (0 : ℝ) < L := lt_trans one_pos hL
  have hfirst : t * (1 / K) ≤ ε / 2 := by
    rcases eq_or_lt_of_le ht with hzero | hpos
    · rw [← hzero]
      simp
      linarith
    · rw [mul_one_div, div_le_iff₀ hK]
      have hKlb' : 2 * t / ε ≤ K := hKlb
      rw [div_le_iff₀ hε] at hKlb'
      nlinarith [hKlb', hpos, hε]
  have hsecond : t * ((L - 1) / L ^ (3 : ℕ)) ≤ ε / (2 * L) := by
    have hle : (L - 1) / L ^ (3 : ℕ) ≤ 1 / L ^ (2 : ℕ) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [hLpos]
    have hstep : t * ((L - 1) / L ^ (3 : ℕ)) ≤ t * (1 / L ^ (2 : ℕ)) :=
      mul_le_mul_of_nonneg_left hle ht
    refine le_trans hstep ?_
    rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [htL, hLpos]
  have hhalf : ε / (2 * L) < ε / 2 := by
    rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [hε, hL]
  have hmul : t * R ≤ t * (1 / K + (L - 1) / L ^ (3 : ℕ)) := mul_le_mul_of_nonneg_left hR ht
  have hexpand : t * (1 / K + (L - 1) / L ^ (3 : ℕ))
      = t * (1 / K) + t * ((L - 1) / L ^ (3 : ℕ)) := by ring
  rw [hexpand] at hmul
  linarith [hmul, hfirst, hsecond, hhalf]


end GaloisForLFunctions.HTGeometry
