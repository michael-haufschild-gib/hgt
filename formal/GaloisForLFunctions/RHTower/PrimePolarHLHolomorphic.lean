import GaloisForLFunctions.RHTower.MovingTentGridLipschitz
import GaloisForLFunctions.RHTower.PrimePolarDirichletBackbone

/-!
# Holomorphy of the moving-tent error correction `H_L`

The holomorphy `(19)` of `prime-polar-moving-tent-divisor-tomography` §3.  The correction
`H_L(s) = ∑_k (Λ(k)/√k)·E_{k,L}(s)` — the difference between the true moving-prime Dirichlet series and
the leading `I_L(s)·(-ζ'/ζ)(s-½)` term — is holomorphic on `Re s > 1`.

Each `E_{k,L}` is entire (a finite sum of `j^{-s}` terms minus `k^{1-s}·A_L(s-1)²`), and on a ball
`B(s₀, r) ⊆ {Re s > 1}` the weighted terms are uniformly bounded by a summable von Mangoldt series
(via the *explicit*-constant error bound `E_kL_bound_explicit`, whose Lipschitz constant `gGridK L s`
is bounded on the ball).  The Weierstrass M-test for holomorphy
(`differentiableOn_tsum_of_summable_norm`) then gives differentiability.  On `Re s > 1` the point `s = 1`
is excluded, so the source bound (which needs `s ≠ 1`) applies throughout — this is the region where the
divisor poles `s = ρ + ½` (`Re ρ > ½`) live.
-/

open HTGeometry ArithmeticFunction Complex

namespace RHTower


noncomputable def Nof (L : ℝ) (k : ℕ) : ℕ := Nat.ceil ((k : ℝ) * Real.exp (2 * L))

noncomputable def Eterm (L : ℝ) (k : ℕ) (s : ℂ) : ℂ :=
  (∑ j ∈ Finset.range (Nof L k), (tentPos L (Real.log ((j : ℝ) / (k : ℝ))) : ℂ) * (j : ℂ) ^ (-s))
    - (k : ℂ) ^ (1 - s) * (rectangularWindowAmplitude L (s - 1)) ^ 2

theorem Eterm_differentiable (L : ℝ) {k : ℕ} (hk : 0 < k) : Differentiable ℂ (Eterm L k) := by
  have hkc : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
  apply Differentiable.sub
  · apply Differentiable.fun_sum
    intro j _
    rcases Nat.eq_zero_or_pos j with hj0 | hj
    · subst hj0
      simp only [Nat.cast_zero, zero_div, Real.log_zero,
        tentPos_eq_zero_of_nonpos L (le_refl (0 : ℝ)), Complex.ofReal_zero, zero_mul]
      exact differentiable_const 0
    · have hjc : (j : ℂ) ≠ 0 := by exact_mod_cast hj.ne'
      exact (differentiable_neg.const_cpow (Or.inl hjc)).const_mul _
  · exact ((differentiable_id.const_sub 1).const_cpow (Or.inl hkc)).mul
      (((rectangularWindowAmplitude_differentiable L).comp (differentiable_id.sub_const 1)).pow 2)

/-- The holomorphic correction `H_L(s) = ∑_k (Λ(k)/√k)·E_{k,L}(s)`. -/
noncomputable def HL (L : ℝ) (s : ℂ) : ℂ := ∑' k, (Λ k / Real.sqrt k) • Eterm L k s

/-- **Holomorphy of `H_L` on the maximal strip `{Re s > ½} ∖ {1}`.**  The weighted error series
`∑_k (Λ(k)/√k)·E_{k,L}(s)` converges absolutely and locally uniformly wherever the dominating
von Mangoldt series `∑ Λ(k) k^{-σ-½}` converges, i.e. `σ > ½` — the full half-plane `Re s > ½`, not just
the Euler region `Re s > 1`.  The single point `s = 1` is removed because the leading integral identity
`∫ g_s = A_L(s-1)²` (hence `E_kL_bound_explicit`) is proved off the amplitude's removable singularity at
`s = 1`; the ball around each `s₀ ≠ 1` is shrunk to avoid it.  This is the strip in which every
nontrivial-zeta-zero pole `s = ρ + ½` (including the critical-line heights `s = 1 + iγ`, `γ ≠ 0`) lives. -/
theorem HL_differentiableOn_gt_half (L : ℝ) (hL : 0 ≤ L) :
    DifferentiableOn ℂ (HL L) ({s : ℂ | 1 / 2 < s.re} \ {1}) := by
  intro s₀ hs₀
  obtain ⟨hs₀re, hs₀ne⟩ := hs₀
  simp only [Set.mem_setOf_eq] at hs₀re
  simp only [Set.mem_singleton_iff] at hs₀ne
  set σ : ℝ := (s₀.re + 1 / 2) / 2 with hσdef
  have hσhalf : 1 / 2 < σ := by rw [hσdef]; linarith
  have hσlt : σ < s₀.re := by rw [hσdef]; linarith
  have hd1 : (0 : ℝ) < ‖s₀ - 1‖ := by
    rw [norm_pos_iff]; exact sub_ne_zero.mpr hs₀ne
  set r : ℝ := min (s₀.re - σ) (‖s₀ - 1‖ / 2) with hrdef
  have hr0 : 0 < r := by rw [hrdef]; exact lt_min (by linarith) (by linarith)
  have hrle1 : r ≤ s₀.re - σ := by rw [hrdef]; exact min_le_left _ _
  have hrle2 : r ≤ ‖s₀ - 1‖ / 2 := by rw [hrdef]; exact min_le_right _ _
  set R : ℝ := ‖s₀‖ + r with hRdef
  have hBsub : ∀ s ∈ Metric.ball s₀ r, σ < s.re := by
    intro s hs
    have hd : dist s s₀ < r := hs
    have h1 : |s.re - s₀.re| ≤ dist s s₀ := by
      rw [Complex.dist_eq, ← Complex.sub_re]; exact Complex.abs_re_le_norm _
    have h2 := (abs_lt.mp (lt_of_le_of_lt h1 hd)).1
    linarith [hrle1]
  have hBne : ∀ s ∈ Metric.ball s₀ r, s ≠ 1 := by
    intro s hs h1
    have hd : dist s s₀ < r := hs
    rw [h1] at hd
    rw [dist_comm, Complex.dist_eq] at hd
    linarith [hrle2]
  have hBbdd : ∀ s ∈ Metric.ball s₀ r, ‖s‖ ≤ R := by
    intro s hs
    have hd : dist s s₀ < r := hs
    have hnorm : ‖s‖ ≤ ‖s₀‖ + dist s s₀ := by
      rw [dist_eq_norm]
      calc ‖s‖ = ‖s₀ + (s - s₀)‖ := by ring_nf
        _ ≤ ‖s₀‖ + ‖s - s₀‖ := norm_add_le _ _
    rw [hRdef]; linarith
    -- constants
  set KR : ℝ := (L * R + 1) * Real.exp (R * (2 * L)) with hKRdef
  set MB : ℝ := KR * (Real.exp (2 * L) + 1) / 2 with hMBdef
  have hu : Summable (fun k : ℕ => MB * ((Λ k) * (k : ℝ) ^ (-(σ + 1 / 2)))) :=
    (vonMangoldt_shifted_summable σ hσhalf).mul_left MB
  -- differentiability of each term on the ball
  have hf : ∀ k : ℕ, DifferentiableOn ℂ (fun s => (Λ k / Real.sqrt k) • Eterm L k s)
      (Metric.ball s₀ r) := by
    intro k
    rcases Nat.eq_zero_or_pos k with hk0 | hk
    · subst hk0
      simp only [Nat.cast_zero, Real.sqrt_zero, div_zero, zero_smul]
      exact differentiableOn_const 0
    · exact ((Eterm_differentiable L hk).const_smul (Λ k / Real.sqrt k)).differentiableOn
  -- uniform bound
  have hF_le : ∀ (k : ℕ) (s : ℂ), s ∈ Metric.ball s₀ r →
      ‖(Λ k / Real.sqrt k) • Eterm L k s‖ ≤ MB * ((Λ k) * (k : ℝ) ^ (-(σ + 1 / 2))) := by
    intro k s hs
    rcases Nat.eq_zero_or_pos k with hk0 | hk
    · subst hk0; simp
    · have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
      have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
      have hres : σ < s.re := hBsub s hs
      have hRnn : ‖s‖ ≤ R := hBbdd s hs
      have hKR : (gGridK L s : ℝ) ≤ KR := by
        rw [gGridK, Real.coe_toNNReal _ (by positivity), hKRdef]
        have hre : |s.re| ≤ R := le_trans (Complex.abs_re_le_norm s) hRnn
        gcongr
      have hNle : Real.exp (2 * L) ≤ (Nof L k : ℝ) / (k : ℝ) := by
        rw [le_div_iff₀ hkR, mul_comm]; exact Nat.le_ceil _
      have hNub : (Nof L k : ℝ) ≤ (k : ℝ) * (Real.exp (2 * L) + 1) := by
        have h1 : (Nof L k : ℝ) < (k : ℝ) * Real.exp (2 * L) + 1 := Nat.ceil_lt_add_one (by positivity)
        nlinarith [Real.exp_pos (2 * L)]
      have hk1s : ‖(k : ℂ) ^ (1 - s)‖ ≤ (k : ℝ) ^ (1 - σ) := by
        rw [Complex.norm_natCast_cpow_of_pos hk, Complex.sub_re, Complex.one_re]
        exact Real.rpow_le_rpow_of_exponent_le hk1 (by linarith)
      have hEs : ‖Eterm L k s‖ ≤ MB * (k : ℝ) ^ (-σ) := by
        rw [Eterm]
        refine (E_kL_bound_explicit L hL s (hBne s hs) k (Nof L k) hk hNle).trans ?_
        have hstep : ‖(k : ℂ) ^ (1 - s)‖ * ((Nof L k : ℝ) * (gGridK L s : ℝ) / (2 * (k : ℝ) ^ 2))
            ≤ (k : ℝ) ^ (1 - σ) * ((k : ℝ) * (Real.exp (2 * L) + 1) * KR / (2 * (k : ℝ) ^ 2)) := by
          gcongr
        refine hstep.trans (le_of_eq ?_)
        have hpow : (k : ℝ) ^ (1 - σ) * (k : ℝ) / (k : ℝ) ^ 2 = (k : ℝ) ^ (-σ) := by
          rw [show (1 : ℝ) - σ = -σ + 1 by ring, Real.rpow_add hkR, Real.rpow_one]; field_simp
        rw [hMBdef, show (k : ℝ) ^ (1 - σ) * ((k : ℝ) * (Real.exp (2 * L) + 1) * KR / (2 * (k : ℝ) ^ 2))
            = KR * (Real.exp (2 * L) + 1) / 2 * ((k : ℝ) ^ (1 - σ) * (k : ℝ) / (k : ℝ) ^ 2) by ring,
          hpow]
      calc ‖(Λ k / Real.sqrt k) • Eterm L k s‖
          = (Λ k / Real.sqrt k) * ‖Eterm L k s‖ :=
            norm_vonMangoldt_div_sqrt_smul k _
        _ ≤ (Λ k / Real.sqrt k) * (MB * (k : ℝ) ^ (-σ)) :=
            mul_le_mul_of_nonneg_left hEs (div_nonneg vonMangoldt_nonneg (Real.sqrt_nonneg _))
        _ = MB * ((Λ k) * (k : ℝ) ^ (-(σ + 1 / 2))) := by
            rw [Real.sqrt_eq_rpow, div_eq_mul_inv, ← Real.rpow_neg hkR.le,
              show -(σ + 1 / 2) = -(1 / 2) + (-σ) by ring, Real.rpow_add hkR]; ring
  have hdiff := differentiableOn_tsum_of_summable_norm hu hf Metric.isOpen_ball hF_le
  exact ((hdiff.differentiableAt
    (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr0))).differentiableWithinAt)

/-- **Holomorphy of `H_L` on the Euler region `Re s > 1`** — the specialization of
`HL_differentiableOn_gt_half` to the absolute-convergence half-plane, where the divisor poles
`s = ρ + ½` of the off-critical zeros (`Re ρ > ½`) live. -/
theorem HL_differentiableOn (L : ℝ) (hL : 0 ≤ L) :
    DifferentiableOn ℂ (HL L) {s : ℂ | 1 < s.re} :=
  (HL_differentiableOn_gt_half L hL).mono (by
    intro s hs
    simp only [Set.mem_setOf_eq] at hs
    refine ⟨by simp only [Set.mem_setOf_eq]; linarith, ?_⟩
    simp only [Set.mem_singleton_iff]
    intro h; rw [h] at hs; simp at hs)

end RHTower
