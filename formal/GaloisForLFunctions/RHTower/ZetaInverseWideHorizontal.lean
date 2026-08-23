import GaloisForLFunctions.RHTower.ZetaInverseHorizontal
import GaloisForLFunctions.RHTower.ZetaCarrier
import GaloisForLFunctions.RHTower.ZetaChiStripGrowth

/-!
# The inverse of zeta on a full horizontal segment

Proposition 5.1 controls `1/ζ` on `-1 ≤ σ ≤ 2` at the selected heights.  Burnol's rectangle in
Theorem 5.2 is wider — its half-width `A ≥ 3/2` eventually tends to infinity — so the estimate has
to be extended to the whole segment `-b ≤ σ ≤ b`.  Both extensions are free of any height selection:
right of the strip the Dirichlet series gives `‖ζ‖ ≥ 1/4`, and left of it the functional equation
`1/ζ(s) = χ(1-s)/ζ(1-s)` reduces to the right-hand bound at the cost of the polynomial vertical
growth of `χ`.

## Main results

* `norm_zeta_inv_le_of_two_le_re`
* `exists_norm_zeta_inv_left_bound`
* `exists_seq_zeta_inv_horizontal` — the selected heights as a strictly increasing sequence, with the
  bound on every horizontal segment
-/

open Complex Filter Topology

namespace RHTower

noncomputable section

theorem norm_zeta_inv_le_of_two_le_re {s : ℂ} (hs : 2 ≤ s.re) :
    ‖(riemannZeta s)⁻¹‖ ≤ 4 := by
  have h := norm_riemannZeta_ge_of_two_le_re hs
  have hpos : (0 : ℝ) < ‖riemannZeta s‖ := lt_of_lt_of_le (by norm_num) h
  rw [norm_inv]
  rw [inv_le_iff_one_le_mul₀ hpos]
  linarith

/-- Left of the strip the reflected functional equation bounds `1/ζ` polynomially. -/
theorem exists_norm_zeta_inv_left_bound (b : ℝ) :
    ∃ (C T₀ : ℝ) (N : ℕ), 0 < C ∧ ∀ σ t : ℝ, -b ≤ σ → σ ≤ -1 → T₀ ≤ |t| →
      ‖(riemannZeta ((σ : ℂ) + (t : ℂ) * I))⁻¹‖ ≤ C * (1 + |t|) ^ N := by
  obtain ⟨Tχ, N, Cχ, hCχ0, hCχ⟩ := hasStripPolyGrowthOffReal_zetaChi 2 (1 + b)
  refine ⟨4 * Cχ + 1, max Tχ 1, N, by positivity, ?_⟩
  intro σ t hσb hσ1 ht
  have ht1 : (1 : ℝ) ≤ |t| := le_trans (le_max_right _ _) ht
  have htχ : Tχ ≤ |t| := le_trans (le_max_left _ _) ht
  set s : ℂ := (σ : ℂ) + (t : ℂ) * I with hs
  have hsre : s.re = σ := by rw [hs]; simp
  have hsim : s.im = t := by rw [hs]; simp
  have htne : t ≠ 0 := by
    intro h
    rw [h] at ht1
    simp at ht1
    linarith
  have hsim0 : s.im ≠ 0 := by rw [hsim]; exact htne
  have h1sim : ((1 : ℂ) - s).im ≠ 0 := by
    have : ((1 : ℂ) - s).im = -t := by rw [hs]; simp
    rw [this]
    simpa using htne
  have hΓ1 : Complex.Gammaℝ (1 - s) ≠ 0 := gammaR_ne_zero_of_im_ne h1sim
  have hΓ : Complex.Gammaℝ s ≠ 0 := gammaR_ne_zero_of_im_ne hsim0
  have hs0 : s ≠ 0 := by
    intro h
    rw [h] at hsim0
    simp at hsim0
  have hs1 : s ≠ 1 := by
    intro h
    rw [h] at hsim0
    simp at hsim0
  have hFE : riemannZeta s = zetaChi s * riemannZeta (1 - s) := zeta_eq_zetaChi_mul hs0 hs1 hΓ1
  have hχ : zetaChi s * zetaChi (1 - s) = 1 := zetaChi_mul_one_sub hΓ hΓ1
  have hχne : zetaChi s ≠ 0 := by
    intro h
    rw [h, zero_mul] at hχ
    exact zero_ne_one hχ
  have hinv : (riemannZeta s)⁻¹ = zetaChi (1 - s) * (riemannZeta (1 - s))⁻¹ := by
    rw [hFE, mul_inv]
    rw [inv_eq_of_mul_eq_one_right hχ]
  have hre1 : ((1 : ℂ) - s).re = 1 - σ := by rw [hs]; simp
  have hzeta1 : ‖(riemannZeta (1 - s))⁻¹‖ ≤ 4 := by
    refine norm_zeta_inv_le_of_two_le_re ?_
    rw [hre1]
    linarith
  have hchi : ‖zetaChi (1 - s)‖ ≤ Cχ * (1 + |((1 : ℂ) - s).im|) ^ N := by
    refine hCχ (1 - s) ?_ ?_ ?_
    · rw [hre1]; linarith
    · rw [hre1]; linarith
    · have him : ((1 : ℂ) - s).im = -t := by rw [hs]; simp
      rw [him, abs_neg]
      exact htχ
  have him : |((1 : ℂ) - s).im| = |t| := by
    have h : ((1 : ℂ) - s).im = -t := by rw [hs]; simp
    rw [h, abs_neg]
  rw [him] at hchi
  rw [hinv, norm_mul]
  have hpow : (0 : ℝ) ≤ (1 + |t|) ^ N := by positivity
  calc ‖zetaChi (1 - s)‖ * ‖(riemannZeta (1 - s))⁻¹‖
      ≤ (Cχ * (1 + |t|) ^ N) * 4 := by
        refine mul_le_mul hchi hzeta1 (norm_nonneg _) (by positivity)
    _ ≤ (4 * Cχ + 1) * (1 + |t|) ^ N := by nlinarith [hpow, hCχ0]

/-- **The selected heights as a sequence.**  Proposition 5.1 supplies one height in every unit
interval; taking every second interval makes the choice strictly increasing, and the two free
extensions give a polynomial bound for `1/ζ` on every horizontal segment. -/
theorem exists_seq_zeta_inv_horizontal :
    ∃ T : ℕ → ℝ, StrictMono T ∧ Tendsto T atTop atTop ∧ (∀ k : ℕ, 1 ≤ T k) ∧
      (∀ k : ℕ, T (k + 1) ≤ T k + 3) ∧
      (∀ k : ℕ, ∀ σ : ℝ, -1 ≤ σ → σ ≤ 2 →
        riemannZeta ((σ : ℂ) + ((T k : ℝ) : ℂ) * I) ≠ 0) ∧
      ∀ b : ℝ, 2 ≤ b → ∃ (C A : ℝ) (k₀ : ℕ), 0 < C ∧ 0 < A ∧
        ∀ k : ℕ, k₀ ≤ k → ∀ σ : ℝ, -b ≤ σ → σ ≤ b →
          ‖(riemannZeta ((σ : ℂ) + ((T k : ℝ) : ℂ) * I))⁻¹‖ ≤ C * (T k) ^ A := by
  classical
  obtain ⟨A₀, hA₀0, n₀, hprop⟩ := exists_zeta_inv_horizontal_bound
  set m₀ : ℝ := max n₀ 1 with hm₀def
  have hm₀1 : (1 : ℝ) ≤ m₀ := le_max_right _ _
  have hstep : ∀ k : ℕ, ∃ T : ℝ, (m₀ + 2 * k) ≤ T ∧ T ≤ (m₀ + 2 * k) + 1 ∧
      ∀ σ : ℝ, -1 ≤ σ → σ ≤ 2 →
        (T : ℝ) ^ (-A₀) ≤ ‖riemannZeta ((σ : ℂ) + (T : ℂ) * I)‖ := by
    intro k
    refine hprop (m₀ + 2 * k) ?_
    have hk : (0 : ℝ) ≤ 2 * k := by positivity
    have : n₀ ≤ m₀ := le_max_left _ _
    linarith
  choose T hTlow hThigh hTbound using hstep
  have hT1 : ∀ k : ℕ, 1 ≤ T k := by
    intro k
    have hk : (0 : ℝ) ≤ 2 * k := by positivity
    have := hTlow k
    linarith
  have hTmono : StrictMono T := by
    refine strictMono_nat_of_lt_succ fun k => ?_
    have h1 := hThigh k
    have h2 := hTlow (k + 1)
    have hcast : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
    rw [hcast] at h2
    linarith
  have hTtop : Tendsto T atTop atTop := by
    refine tendsto_atTop_mono (fun k => hTlow k) ?_
    refine Filter.tendsto_atTop_add_const_left _ m₀ ?_
    exact (tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop (by norm_num)
  refine ⟨T, hTmono, hTtop, hT1, ?_, ?_, ?_⟩
  · intro k
    have h1 := hTlow k
    have h2 := hThigh (k + 1)
    have hcast : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
    rw [hcast] at h2
    linarith
  · intro k σ h1 h2
    have hTk1 : (1 : ℝ) ≤ T k := hT1 k
    have hpos : (0 : ℝ) < (T k) ^ (-A₀) := Real.rpow_pos_of_pos (by linarith) _
    have hb := hTbound k σ h1 h2
    intro hzero
    rw [hzero] at hb
    simp at hb
    linarith
  intro b hb
  obtain ⟨Cl, T₀, N, hCl0, hCl⟩ := exists_norm_zeta_inv_left_bound b
  obtain ⟨k₀, hk₀⟩ := (hTtop.eventually_ge_atTop (max T₀ 1)).exists_forall_of_atTop
  refine ⟨4 * (Cl * 2 ^ N) + 5, max A₀ (N : ℝ) + 1, k₀, by positivity, by positivity, ?_⟩
  intro k hk σ hσlow hσhigh
  have hTk1 : (1 : ℝ) ≤ T k := hT1 k
  have hTk0 : (0 : ℝ) < T k := by linarith
  have hTkT₀ : max T₀ 1 ≤ T k := hk₀ k hk
  have hpowmono : ∀ x : ℝ, 0 ≤ x → x ≤ max A₀ (N : ℝ) + 1 →
      (T k) ^ x ≤ (T k) ^ (max A₀ (N : ℝ) + 1) := by
    intro x hx hxle
    exact Real.rpow_le_rpow_of_exponent_le hTk1 hxle
  have hpow1 : (1 : ℝ) ≤ (T k) ^ (max A₀ (N : ℝ) + 1) := by
    refine Real.one_le_rpow hTk1 ?_
    have : (0 : ℝ) ≤ max A₀ (N : ℝ) := le_trans hA₀0.le (le_max_left _ _)
    linarith
  rcases le_or_gt σ (-1) with hleft | hmid
  · -- left of the strip
    have habs : |T k| = T k := abs_of_nonneg hTk0.le
    have hTkge : T₀ ≤ |T k| := by
      rw [habs]
      exact le_trans (le_max_left _ _) hTkT₀
    have hbound := hCl σ (T k) hσlow hleft hTkge
    rw [habs] at hbound
    have hstepA : (1 + T k) ^ N ≤ 2 ^ N * (T k) ^ (N : ℝ) := by
      have h1 : (1 : ℝ) + T k ≤ 2 * T k := by linarith
      have h2 : ((1 : ℝ) + T k) ^ N ≤ (2 * T k) ^ N := by
        refine pow_le_pow_left₀ (by linarith) h1 N
      have h3 : (2 * T k) ^ N = 2 ^ N * (T k) ^ N := by rw [mul_pow]
      have h4 : (T k) ^ N = (T k) ^ (N : ℝ) := (Real.rpow_natCast _ N).symm
      rw [h3, h4] at h2
      exact h2
    have hstepB : (T k) ^ (N : ℝ) ≤ (T k) ^ (max A₀ (N : ℝ) + 1) := by
      refine hpowmono _ (by positivity) ?_
      have : (N : ℝ) ≤ max A₀ (N : ℝ) := le_max_right _ _
      linarith
    have hCl0' : (0 : ℝ) ≤ Cl := hCl0.le
    have hpowN : (0 : ℝ) ≤ (2 : ℝ) ^ N := by positivity
    calc ‖(riemannZeta ((σ : ℂ) + ((T k : ℝ) : ℂ) * I))⁻¹‖
        ≤ Cl * (1 + T k) ^ N := hbound
      _ ≤ Cl * (2 ^ N * (T k) ^ (N : ℝ)) := by
          exact mul_le_mul_of_nonneg_left hstepA hCl0'
      _ ≤ Cl * (2 ^ N * (T k) ^ (max A₀ (N : ℝ) + 1)) := by
          refine mul_le_mul_of_nonneg_left ?_ hCl0'
          exact mul_le_mul_of_nonneg_left hstepB hpowN
      _ ≤ (4 * (Cl * 2 ^ N) + 5) * (T k) ^ (max A₀ (N : ℝ) + 1) := by
          have hpos : (0 : ℝ) ≤ (T k) ^ (max A₀ (N : ℝ) + 1) := by positivity
          have hCN : (0 : ℝ) ≤ Cl * 2 ^ N := by positivity
          have hrw : Cl * (2 ^ N * (T k) ^ (max A₀ (N : ℝ) + 1))
              = (Cl * 2 ^ N) * (T k) ^ (max A₀ (N : ℝ) + 1) := by ring
          rw [hrw]
          refine mul_le_mul_of_nonneg_right ?_ hpos
          linarith
  · rcases le_or_gt σ 2 with hstrip | hright
    · -- inside the strip: this is Proposition 5.1
      have hlow := hTbound k σ (by linarith) hstrip
      have hzpos : (0 : ℝ) < (T k) ^ (-A₀) := Real.rpow_pos_of_pos hTk0 _
      have hzeta : (0 : ℝ) < ‖riemannZeta ((σ : ℂ) + ((T k : ℝ) : ℂ) * I)‖ :=
        lt_of_lt_of_le hzpos hlow
      have hinvle : ‖(riemannZeta ((σ : ℂ) + ((T k : ℝ) : ℂ) * I))⁻¹‖ ≤ (T k) ^ A₀ := by
        rw [norm_inv]
        rw [inv_le_iff_one_le_mul₀ hzeta]
        have hmul : (T k) ^ (-A₀) * (T k) ^ A₀ = 1 := by
          rw [← Real.rpow_add hTk0]
          simp
        nlinarith [hlow, Real.rpow_pos_of_pos hTk0 A₀]
      have hstepB : (T k) ^ A₀ ≤ (T k) ^ (max A₀ (N : ℝ) + 1) := by
        refine hpowmono _ hA₀0.le ?_
        have : A₀ ≤ max A₀ (N : ℝ) := le_max_left _ _
        linarith
      have hpos : (0 : ℝ) ≤ (T k) ^ (max A₀ (N : ℝ) + 1) := by positivity
      have hCl0' : (0 : ℝ) ≤ Cl := hCl0.le
      have hpowN : (0 : ℝ) ≤ (2 : ℝ) ^ N := by positivity
      calc ‖(riemannZeta ((σ : ℂ) + ((T k : ℝ) : ℂ) * I))⁻¹‖
          ≤ (T k) ^ A₀ := hinvle
        _ ≤ (T k) ^ (max A₀ (N : ℝ) + 1) := hstepB
        _ ≤ (4 * (Cl * 2 ^ N) + 5) * (T k) ^ (max A₀ (N : ℝ) + 1) := by
            have hCN : (0 : ℝ) ≤ Cl * 2 ^ N := by positivity
            refine le_mul_of_one_le_left hpos ?_
            linarith
    · -- right of the strip
      have hre : ((σ : ℂ) + ((T k : ℝ) : ℂ) * I).re = σ := by simp
      have h4 : ‖(riemannZeta ((σ : ℂ) + ((T k : ℝ) : ℂ) * I))⁻¹‖ ≤ 4 := by
        refine norm_zeta_inv_le_of_two_le_re ?_
        rw [hre]
        linarith
      have hpos : (0 : ℝ) ≤ (T k) ^ (max A₀ (N : ℝ) + 1) := by positivity
      have hCN : (0 : ℝ) ≤ Cl * 2 ^ N := by positivity
      calc ‖(riemannZeta ((σ : ℂ) + ((T k : ℝ) : ℂ) * I))⁻¹‖ ≤ 4 := h4
        _ ≤ (4 * (Cl * 2 ^ N) + 5) * 1 := by linarith
        _ ≤ (4 * (Cl * 2 ^ N) + 5) * (T k) ^ (max A₀ (N : ℝ) + 1) := by
            refine mul_le_mul_of_nonneg_left hpow1 ?_
            linarith

end

end RHTower

