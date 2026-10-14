import GaloisForLFunctions.RHTower.InversionSymmetricFourierBlindTwistedMayer

/-!
# Totally Fourier-blind inversion-symmetric cores of support ratio below `212/123` vanish

Let `G : ℝ → ℝ` be continuous and even, with `G(1/x) = x G(x)` for `x > 0`, vanishing on
`[0, 123/212)`, and with `Ĝ(n) = 0` for **every** integer `n`.

**Theorem** (`eq_zero_of_inversionSymmetric_totallyFourierBlind`).  Then `G = 0`.

The cores of `exists_inversionSymmetric_fourierBlind_ninety_seven_fifty_sixths` are totally
Fourier-blind and vanish on `[0, 56/97)`.  So the support-ratio threshold for continuous totally
Fourier-blind cores lies in `[212/123, 97/56] ≈ [1.72358, 1.73214]`.  The exponent `123/212`
comes from `δ = 34/89`, just above `1/φ² = 2 − φ`, where the Gauss branches stop mixing the three
intervals below; `212/123` is just below `(4 − φ)/(3 − φ) ≈ 1.72361`.

**Proof.**  Put `ϑ(r) = G(1 − 1/(2 + r))/(2 + r)`.  Total blindness makes the periodization
vanish, so the twisted Mayer equation (`inversionSymmetric_twistedMayerHalf`) is homogeneous.  For
`r ∈ [0, 1]` only the first two branches can reach the support `[34/89, 1]` of `ϑ`, so
`ϑ(r) = −ϑ(1/(r+1))/(r+1) + ϑ(1/(r+2))/(r+2)`.  Split `[34/89, 1]` into
`A = [34/89, ½]`, `B = [½, 34/55]`, `C = [34/55, 1]`, with maxima `M_A, M_B, M_C` of `|ϑ|`.
* On `A` both branches act, into `C` and `A`: `M_A ≤ (89/123) M_C + (89/212) M_A`.
* On `B ∩ [½, 21/34]` they act into `C` and `A`: `|ϑ| ≤ (2/3) M_C + (2/5) M_A`; on
  `[21/34, 34/55]` only the first acts, into `B`: `|ϑ| ≤ (34/55) M_B`.
* On `C` only the first acts, into `B` (`55/89 ≤ 34/55`, `55/144 < 34/89`): `M_C ≤ (55/89) M_B`.
Then `M_B ≤ 0.73 M_B`, so all maxima vanish.  This is a positivity-free contraction: the positive
two-branch transfer operator at `s = ½` has spectral radius below `1` on this survivor set.
-/

open MeasureTheory Set Real Filter Topology
open scoped FourierTransform

namespace RHTower

noncomputable section

theorem twistedMayerHalf_two (ϑ : ℝ → ℝ) (r : ℝ) :
    twistedMayerHalf 2 ϑ r = ϑ (1 / (r + 1)) / (r + 1) - ϑ (1 / (r + 2)) / (r + 2) := by
  unfold twistedMayerHalf
  rw [Finset.sum_range_succ, Finset.sum_range_one]
  norm_num
  ring_nf

/-- **Totally Fourier-blind inversion-symmetric cores of support ratio below `212/123`
vanish.** -/
theorem eq_zero_of_inversionSymmetric_totallyFourierBlind {G : ℝ → ℝ} (hG : Continuous G)
    (heven : ∀ x, G (-x) = G x) (hinv : ∀ x, 0 < x → G x⁻¹ = x * G x)
    (hsupp : ∀ x, 0 ≤ x → x < 123 / 212 → G x = 0)
    (hblind : ∀ n : ℤ, 𝓕 (fun x => (G x : ℂ)) n = 0) (y : ℝ) : G y = 0 := by
  have hc : (1 : ℝ) / 2 < 123 / 212 := by norm_num
  have hc0 : (0 : ℝ) < 123 / 212 := by norm_num
  have hblind2 : ∀ n : ℤ, 2 ≤ |n| → 𝓕 (fun x => (G x : ℂ)) n = 0 := fun n _ => hblind n
  have ha0 : (𝓕 (fun x => (G x : ℂ)) 0).re = 0 := by
    have := hblind 0
    simp only [Int.cast_zero] at this
    rw [this, Complex.zero_re]
  have ha1 : (𝓕 (fun x => (G x : ℂ)) 1).re = 0 := by
    have := hblind 1
    simp only [Int.cast_one] at this
    rw [this, Complex.zero_re]
  have hle := inversionSymmetric_eq_zero_of_le hG hc0 hsupp
  obtain ⟨ϑ, hϑ⟩ : ∃ ϑ : ℝ → ℝ, ∀ r, ϑ r = G (1 - 1 / (2 + r)) / (2 + r) :=
    ⟨_, fun _ => rfl⟩
  have hϑf : (fun ρ => G (1 - 1 / (2 + ρ)) / (2 + ρ)) = ϑ := funext fun ρ => (hϑ ρ).symm
  -- the homogeneous two-branch Mayer equation
  have hmay : ∀ r, 0 ≤ r →
      ϑ r = -(ϑ (1 / (r + 1)) / (r + 1)) + ϑ (1 / (r + 2)) / (r + 2) := by
    intro r hr
    have h := inversionSymmetric_twistedMayerHalf hG heven hinv hc hsupp hblind2 hr (N := 2)
      (by norm_num)
    rw [ha0, ha1, hϑf, twistedMayerHalf_two, ← hϑ r] at h
    simp only [mul_zero, add_zero, fareySeriesR, zero_mul] at h
    linarith
  -- `ϑ` vanishes on `[0, 34/89]`
  have hzero : ∀ t, 0 ≤ t → t ≤ 34 / 89 → ϑ t = 0 := by
    intro t h0 h1
    have h2 : 0 < 2 + t := by linarith
    have hx0 : 0 ≤ 1 - 1 / (2 + t) := by rw [sub_nonneg, div_le_one h2]; linarith
    have hx1 : 1 - 1 / (2 + t) ≤ 123 / 212 := by rw [sub_le_comm, le_div_iff₀ h2]; linarith
    rw [hϑ, hle (1 - 1 / (2 + t)) hx0 hx1, zero_div]
  -- continuity on `[0, ∞)`
  have hcont : ContinuousOn ϑ (Ici 0) := by
    have h : ContinuousOn (fun r : ℝ => G (1 - 1 / (2 + r)) / (2 + r)) (Ici 0) := by
      have hne : ∀ r ∈ Ici (0 : ℝ), (2 : ℝ) + r ≠ 0 := fun r hr => by
        simp only [mem_Ici] at hr; linarith
      refine ContinuousOn.div ?_ (continuousOn_const.add continuousOn_id) hne
      exact hG.comp_continuousOn
        (continuousOn_const.sub (continuousOn_const.div (continuousOn_const.add continuousOn_id)
          hne))
    exact h.congr fun r _ => hϑ r
  have habs : ∀ a b : ℝ, 0 ≤ a → ContinuousOn (fun r => |ϑ r|) (Icc a b) := fun a b ha =>
    continuous_abs.comp_continuousOn (hcont.mono fun r hr => le_trans ha hr.1)
  obtain ⟨rA, hrA, hmA⟩ := isCompact_Icc.exists_isMaxOn
    (nonempty_Icc.2 (by norm_num : (34 : ℝ) / 89 ≤ 1 / 2)) (habs _ _ (by norm_num))
  obtain ⟨rB, hrB, hmB⟩ := isCompact_Icc.exists_isMaxOn
    (nonempty_Icc.2 (by norm_num : (1 : ℝ) / 2 ≤ 34 / 55)) (habs _ _ (by norm_num))
  obtain ⟨rC, hrC, hmC⟩ := isCompact_Icc.exists_isMaxOn
    (nonempty_Icc.2 (by norm_num : (34 : ℝ) / 55 ≤ 1)) (habs _ _ (by norm_num))
  set MA := |ϑ rA|
  set MB := |ϑ rB|
  set MC := |ϑ rC|
  have bA : ∀ t ∈ Icc (34 / 89 : ℝ) (1 / 2), |ϑ t| ≤ MA := fun t ht => isMaxOn_iff.mp hmA t ht
  have bB : ∀ t ∈ Icc (1 / 2 : ℝ) (34 / 55), |ϑ t| ≤ MB := fun t ht => isMaxOn_iff.mp hmB t ht
  have bC : ∀ t ∈ Icc (34 / 55 : ℝ) 1, |ϑ t| ≤ MC := fun t ht => isMaxOn_iff.mp hmC t ht
  have hMA : 0 ≤ MA := abs_nonneg _
  have hMB : 0 ≤ MB := abs_nonneg _
  have hMC : 0 ≤ MC := abs_nonneg _
  -- a branch value bound
  have term : ∀ (r m M κ : ℝ) (lo hi : ℝ), 0 ≤ r → 0 < m → 1 / (r + m) ∈ Icc lo hi →
      (∀ t ∈ Icc lo hi, |ϑ t| ≤ M) → 1 / (r + m) ≤ κ → 0 ≤ M →
      |ϑ (1 / (r + m)) / (r + m)| ≤ κ * M := by
    intro r m M κ lo hi hr hm hmem hb hκ hM
    have hp : 0 < r + m := by linarith
    rw [abs_div, abs_of_pos hp]
    calc |ϑ (1 / (r + m))| / (r + m) = 1 / (r + m) * |ϑ (1 / (r + m))| := by ring
      _ ≤ κ * M := mul_le_mul hκ (hb _ hmem) (abs_nonneg _)
          (le_trans (le_of_lt (one_div_pos.mpr hp)) hκ)
  -- region `A`
  have iA : MA ≤ 89 / 123 * MC + 89 / 212 * MA := by
    have h1 := hrA.1
    have h2 := hrA.2
    have hp1 : 0 < rA + 1 := by linarith
    have hp2 : 0 < rA + 2 := by linarith
    have e := hmay rA (by linarith)
    have t1 := term rA 1 MC (89 / 123) (34 / 55) 1 (by linarith) one_pos
      ⟨by rw [le_div_iff₀ hp1]; linarith, by rw [div_le_iff₀ hp1]; linarith⟩ bC
      (by rw [div_le_iff₀ hp1]; linarith) hMC
    have t2 := term rA 2 MA (89 / 212) (34 / 89) (1 / 2) (by linarith) two_pos
      ⟨by rw [le_div_iff₀ hp2]; linarith, by rw [div_le_iff₀ hp2]; linarith⟩ bA
      (by rw [div_le_iff₀ hp2]; linarith) hMA
    calc MA = |ϑ rA| := rfl
      _ = |-(ϑ (1 / (rA + 1)) / (rA + 1)) + ϑ (1 / (rA + 2)) / (rA + 2)| := by rw [← e]
      _ ≤ |ϑ (1 / (rA + 1)) / (rA + 1)| + |ϑ (1 / (rA + 2)) / (rA + 2)| := by
          rw [← abs_neg (ϑ (1 / (rA + 1)) / (rA + 1))]; exact abs_add_le _ _
      _ ≤ 89 / 123 * MC + 89 / 212 * MA := add_le_add t1 t2
  -- region `C`
  have iC : MC ≤ 55 / 89 * MB := by
    have h1 := hrC.1
    have h2 := hrC.2
    have hp1 : 0 < rC + 1 := by linarith
    have hp2 : 0 < rC + 2 := by linarith
    have e := hmay rC (by linarith)
    have z : ϑ (1 / (rC + 2)) = 0 := hzero _ (le_of_lt (one_div_pos.mpr hp2))
      (by rw [div_le_iff₀ hp2]; linarith)
    rw [z, zero_div, add_zero] at e
    have t1 := term rC 1 MB (55 / 89) (1 / 2) (34 / 55) (by linarith) one_pos
      ⟨by rw [le_div_iff₀ hp1]; linarith, by rw [div_le_iff₀ hp1]; linarith⟩ bB
      (by rw [div_le_iff₀ hp1]; linarith) hMB
    calc MC = |ϑ rC| := rfl
      _ = |ϑ (1 / (rC + 1)) / (rC + 1)| := by
          rw [e, abs_neg]
      _ ≤ 55 / 89 * MB := t1
  -- region `B`
  have iB : MB ≤ 2 / 3 * MC + 2 / 5 * MA ∨ MB ≤ 34 / 55 * MB := by
    have h1 := hrB.1
    have h2 := hrB.2
    have hp1 : 0 < rB + 1 := by linarith
    have hp2 : 0 < rB + 2 := by linarith
    have e := hmay rB (by linarith)
    rcases le_or_gt rB (21 / 34) with h | h
    · left
      have t1 := term rB 1 MC (2 / 3) (34 / 55) 1 (by linarith) one_pos
        ⟨by rw [le_div_iff₀ hp1]; linarith, by rw [div_le_iff₀ hp1]; linarith⟩ bC
        (by rw [div_le_iff₀ hp1]; linarith) hMC
      have t2 := term rB 2 MA (2 / 5) (34 / 89) (1 / 2) (by linarith) two_pos
        ⟨by rw [le_div_iff₀ hp2]; linarith, by rw [div_le_iff₀ hp2]; linarith⟩ bA
        (by rw [div_le_iff₀ hp2]; linarith) hMA
      calc MB = |ϑ rB| := rfl
        _ = |-(ϑ (1 / (rB + 1)) / (rB + 1)) + ϑ (1 / (rB + 2)) / (rB + 2)| := by rw [← e]
        _ ≤ |ϑ (1 / (rB + 1)) / (rB + 1)| + |ϑ (1 / (rB + 2)) / (rB + 2)| := by
            rw [← abs_neg (ϑ (1 / (rB + 1)) / (rB + 1))]; exact abs_add_le _ _
        _ ≤ 2 / 3 * MC + 2 / 5 * MA := add_le_add t1 t2
    · right
      have z : ϑ (1 / (rB + 2)) = 0 := hzero _ (le_of_lt (one_div_pos.mpr hp2))
        (by rw [div_le_iff₀ hp2]; linarith)
      rw [z, zero_div, add_zero] at e
      have t1 := term rB 1 MB (34 / 55) (1 / 2) (34 / 55) (by linarith) one_pos
        ⟨by rw [le_div_iff₀ hp1]; linarith, by rw [div_le_iff₀ hp1]; linarith⟩ bB
        (by rw [div_le_iff₀ hp1]; linarith) hMB
      calc MB = |ϑ rB| := rfl
        _ = |ϑ (1 / (rB + 1)) / (rB + 1)| := by rw [e, abs_neg]
        _ ≤ 34 / 55 * MB := t1
  have hB0 : MB = 0 := by
    rcases iB with h | h <;> linarith
  have hC0 : MC = 0 := by linarith
  have hA0 : MA = 0 := by linarith
  -- `ϑ = 0` on `[0, 1]`, then on `[0, ∞)`
  have hunit : ∀ t, 0 ≤ t → t ≤ 1 → ϑ t = 0 := by
    intro t h0 h1
    rcases le_or_gt t (34 / 89) with h | h
    · exact hzero t h0 h
    rcases le_or_gt t (1 / 2) with h' | h'
    · exact abs_nonpos_iff.mp (hA0 ▸ bA t ⟨h.le, h'⟩)
    rcases le_or_gt t (34 / 55) with h'' | h''
    · exact abs_nonpos_iff.mp (hB0 ▸ bB t ⟨h'.le, h''⟩)
    · exact abs_nonpos_iff.mp (hC0 ▸ bC t ⟨h''.le, h1⟩)
  have hall : ∀ r, 0 ≤ r → ϑ r = 0 := by
    intro r hr
    have hp1 : 0 < r + 1 := by linarith
    have hp2 : 0 < r + 2 := by linarith
    have u1 := hunit (1 / (r + 1)) (le_of_lt (one_div_pos.mpr hp1))
      (by rw [div_le_one hp1]; linarith)
    have u2 := hunit (1 / (r + 2)) (le_of_lt (one_div_pos.mpr hp2))
      (by rw [div_le_one hp2]; linarith)
    rw [hmay r hr, u1, u2]
    simp
  refine eq_zero_of_inversionSymmetric_of_profile_zero hG heven hinv
    (fun x hx hx2 => hsupp x hx (by linarith)) (fun v hv => ?_) y
  have h := hall (v - 2) (by linarith)
  rw [hϑ, show 2 + (v - 2) = v by ring] at h
  exact (div_eq_zero_iff.mp h).resolve_right (by linarith)

end

end RHTower
