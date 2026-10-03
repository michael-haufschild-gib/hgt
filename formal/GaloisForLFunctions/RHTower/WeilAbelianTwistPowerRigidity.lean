import GaloisForLFunctions.RHTower.WeilFractionalMassSqrtGrowthRigidity
import GaloisForLFunctions.HTGeometry.PhragmenLindelofPower

/-!
# Abelian twist rigidity up to the linear wall

Let `G` be a Herglotz producer for the weights `lam`, and suppose that on the lower critical line

`G(1 − s) = κ₀ e^{iβ₀C(−τ)} G(s)`,  `s = ½ + 2iτ`, `τ < 0`,

with `C` monotone and `C(x) ≤ K x^α` for `x ≥ 1`, for some `α < 1`.

**Theorem** (`abelian_twist_power_rigidity`).  Then `lam(n) = Λ(n)` for every `n ≥ 2`, and RH
holds.

**Corollary** (`fractional_mass_power_growth_rigidity`).  An atomic producer whose real
(non-integer) spectral mass below height `T` is `O(T^α)` for some `α < 1` is `Λ`, and RH holds.

The exponent `α < 1` replaces the `o(√x)` of `AbelianTwist.abelian_twist_rigidity`.

**Proof.**
* *Lindelöf on the strip.*  The producer zeta function `F` satisfies `|F(½+iy)| ≪_ν |y|^ν` on the
  critical line for every `ν > 0`
  (`FractionalMassPolynomialTailRigidity.exists_norm_phiG_le_rpow_small`), and `F` is bounded on
  `Re s = 3/2`.  Phragmén–Lindelöf on `½ ≤ Re s ≤ 3/2`, applied to `G(s)/(sΓ_ℝ(s)) = (s − 1)F(s)`,
  gives `|F(x+iy)| ≪_ν |y|^ν` on the whole strip (`exists_norm_prodF_le_rpow`).
* *Radial error.*  With this top-edge bound the contour shift gives
  `‖ε(∫_{t≤b} F k − a(m)∫_{t≤b} ρ_m)‖ ≪ ε^{1−ν} e^{bδ}`
  (`AbelianTwist.exists_norm_radialError_le_of_strip`).
* *Layer cake.*  The superlevel sets of `C(−t)` are half-lines `t ≤ b_x` with
  `b_x ≤ −(x/K)^{1/α}`, and `∫_0^∞ e^{−δ(x/K)^{1/α}} dx ≤ 2Kδ^{−α}` (`norm_setIntegral_twist_le_pow`).
  So the twisted remainder is `≪ ε^{1−ν} + ε^{1−ν−α} → 0` for `ν = (1−α)/2`.
* *Conclusion.*  `AbelianTwist.abelian_twist_rigidity_of_remainder`.
-/

open Complex Filter Topology Set MeasureTheory

namespace RHTower

namespace AbelianTwist

open GaloisForLFunctions GaloisForLFunctions.HTGeometry IntegerMassRigidity FractionalMassRigidity
  PhaseLockRigidity HamburgerStability TruncatedRadial FractionalMassTailRigidity

noncomputable section

/-! ### Phragmén–Lindelöf on a strip for a function continuous up to the edges -/

/-- **Power-weighted Phragmén–Lindelöf on a closed strip.**  Let `F` be holomorphic on
`A < Re s < B`, continuous on `A ≤ Re s ≤ B`, of polynomial vertical growth there, and bounded by
`C_A‖s − c₀‖^ν`, `C_B‖s − c₀‖^ν` on the two edges, with `c₀ < A`.  Then
`‖F(s)‖ ≤ max(C_A, C_B)‖s − c₀‖^ν` on the strip. -/
theorem norm_le_mul_rpow_of_strip_diffContOnCl {F : ℂ → ℂ} {A B ν c₀ CA CB C N : ℝ}
    (hAB : A < B) (hν : 0 ≤ ν) (hc₀ : c₀ < A)
    (hFd : DifferentiableOn ℂ F (Complex.re ⁻¹' Ioo A B))
    (hFc : ContinuousOn F (Complex.re ⁻¹' Icc A B)) (hC : 0 ≤ C) (hN : 0 ≤ N)
    (hgrow : ∀ s : ℂ, A ≤ s.re → s.re ≤ B → ‖F s‖ ≤ C * (1 + |s.im|) ^ N)
    (hA : ∀ z : ℂ, z.re = A → ‖F z‖ ≤ CA * ‖z - (c₀ : ℂ)‖ ^ ν)
    (hB : ∀ z : ℂ, z.re = B → ‖F z‖ ≤ CB * ‖z - (c₀ : ℂ)‖ ^ ν) :
    ∀ s : ℂ, A ≤ s.re → s.re ≤ B → ‖F s‖ ≤ max CA CB * ‖s - (c₀ : ℂ)‖ ^ ν := by
  have hne : ∀ s : ℂ, A ≤ s.re → s - (c₀ : ℂ) ≠ 0 := by
    intro s hs h
    have hre : (s - (c₀ : ℂ)).re = 0 := by rw [h]; simp
    rw [Complex.sub_re, Complex.ofReal_re] at hre
    linarith
  have hpos : ∀ s : ℂ, A ≤ s.re → 0 < (s - (c₀ : ℂ)).re := by
    intro s hs; rw [Complex.sub_re, Complex.ofReal_re]; linarith
  have hlow : ∀ s : ℂ, A ≤ s.re → A - c₀ ≤ ‖s - (c₀ : ℂ)‖ := by
    intro s hs
    calc A - c₀ ≤ (s - (c₀ : ℂ)).re := by
          rw [Complex.sub_re, Complex.ofReal_re]; linarith
      _ ≤ |(s - (c₀ : ℂ)).re| := le_abs_self _
      _ ≤ ‖s - (c₀ : ℂ)‖ := Complex.abs_re_le_norm _
  have hAc₀ : 0 < A - c₀ := by linarith
  set g : ℂ → ℂ := fun s => F s / (s - (c₀ : ℂ)) ^ ((ν : ℝ) : ℂ) with hgdef
  have hclosed : IsClosed (Complex.re ⁻¹' Icc A B) :=
    isClosed_Icc.preimage Complex.continuous_re
  have hsub : closure (Complex.re ⁻¹' Ioo A B) ⊆ Complex.re ⁻¹' Icc A B := by
    refine closure_minimal ?_ hclosed
    intro z hz
    exact ⟨le_of_lt hz.1, le_of_lt hz.2⟩
  have hgdcc : DiffContOnCl ℂ g (Complex.re ⁻¹' Ioo A B) := by
    refine ⟨fun z hz => ?_, fun z hz => ?_⟩
    · have hzA : A ≤ z.re := le_of_lt hz.1
      refine (hFd z hz).div ?_ (fun h => hne z hzA ((Complex.cpow_eq_zero_iff _ _).1 h).1)
      refine (DifferentiableAt.cpow (differentiableAt_id.sub (differentiableAt_const _))
        (differentiableAt_const _) ?_).differentiableWithinAt
      exact Complex.mem_slitPlane_iff.mpr (Or.inl (hpos z hzA))
    · have hzA : A ≤ z.re := (hsub hz).1
      refine ((hFc z (hsub hz)).mono hsub).div ?_
        (fun h => hne z hzA ((Complex.cpow_eq_zero_iff _ _).1 h).1)
      refine (ContinuousAt.cpow (continuousAt_id.sub continuousAt_const) continuousAt_const
        ?_).continuousWithinAt
      exact Complex.mem_slitPlane_iff.mpr (Or.inl (hpos z hzA))
  refine fun s hs hsb => ?_
  have hsne := hne s hs
  have hpow : (0 : ℝ) < ‖s - (c₀ : ℂ)‖ ^ ν :=
    Real.rpow_pos_of_pos (norm_pos_iff.2 hsne) ν
  have hkey : ‖g s‖ ≤ max CA CB := by
    refine PhragmenLindelof.vertical_strip (a := A) (b := B) (C := max CA CB) hgdcc ?_ ?_ ?_ hs hsb
    · refine ⟨Real.pi / (2 * (B - A)), by
        have hpi : 0 < Real.pi := Real.pi_pos
        have : 0 < B - A := by linarith
        rw [div_lt_div_iff₀ (by positivity) (by positivity)]
        nlinarith, N / (Real.pi / (2 * (B - A))), ?_⟩
      set c : ℝ := Real.pi / (2 * (B - A)) with hcdef
      have hc0 : 0 < c := by
        rw [hcdef]
        have : 0 < B - A := by linarith
        positivity
      refine Asymptotics.isBigO_iff.2 ⟨C / (A - c₀) ^ ν, ?_⟩
      refine Filter.eventually_inf_principal.2 (Filter.Eventually.of_forall ?_)
      intro z hz
      have hzA : A ≤ z.re := le_of_lt hz.1
      have hzB : z.re ≤ B := le_of_lt hz.2
      have hlowz : (A - c₀) ^ ν ≤ ‖z - (c₀ : ℂ)‖ ^ ν :=
        Real.rpow_le_rpow hAc₀.le (hlow z hzA) hν
      have hlowpos : (0 : ℝ) < (A - c₀) ^ ν := Real.rpow_pos_of_pos hAc₀ ν
      have hgz : ‖g z‖ ≤ C * (1 + |z.im|) ^ N / (A - c₀) ^ ν := by
        rw [hgdef]
        simp only
        rw [norm_div, norm_cpow_ofReal_exponent (hne z hzA)]
        gcongr
        exact hgrow z hzA hzB
      refine hgz.trans ?_
      have hexp : (1 + |z.im|) ^ N ≤ Real.exp (N * |z.im|) :=
        rpow_le_exp_mul (abs_nonneg _) hN
      have hexp2 : Real.exp (N * |z.im|) ≤ Real.exp ((N / c) * Real.exp (c * |z.im|)) := by
        refine Real.exp_le_exp.2 ?_
        have h1 : 1 + c * |z.im| ≤ Real.exp (c * |z.im|) := by
          have := Real.add_one_le_exp (c * |z.im|)
          linarith
        have hNc : 0 ≤ N / c := by positivity
        have h2 : (N / c) * (1 + c * |z.im|) ≤ (N / c) * Real.exp (c * |z.im|) :=
          mul_le_mul_of_nonneg_left h1 hNc
        have h3 : (N / c) * (1 + c * |z.im|) = N / c + N * |z.im| := by
          field_simp
        rw [h3] at h2
        linarith
      have hnormexp : ‖Real.exp ((N / c) * Real.exp (c * |z.im|))‖
          = Real.exp ((N / c) * Real.exp (c * |z.im|)) := by
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      rw [hnormexp]
      calc C * (1 + |z.im|) ^ N / (A - c₀) ^ ν
          ≤ C * Real.exp ((N / c) * Real.exp (c * |z.im|)) / (A - c₀) ^ ν := by
            have hb : (1 + |z.im|) ^ N ≤ Real.exp ((N / c) * Real.exp (c * |z.im|)) :=
              le_trans hexp hexp2
            gcongr
        _ = C / (A - c₀) ^ ν * Real.exp ((N / c) * Real.exp (c * |z.im|)) := by ring
    · intro z hz
      have hzne := hne z (le_of_eq hz.symm)
      rw [hgdef]
      simp only
      rw [norm_div, norm_cpow_ofReal_exponent hzne, div_le_iff₀
        (Real.rpow_pos_of_pos (norm_pos_iff.2 hzne) ν)]
      exact le_trans (hA z hz) (by
        refine mul_le_mul_of_nonneg_right (le_max_left _ _) ?_
        exact (Real.rpow_pos_of_pos (norm_pos_iff.2 hzne) ν).le)
    · intro z hz
      have hzA : A ≤ z.re := by rw [hz]; linarith
      have hzne := hne z hzA
      rw [hgdef]
      simp only
      rw [norm_div, norm_cpow_ofReal_exponent hzne, div_le_iff₀
        (Real.rpow_pos_of_pos (norm_pos_iff.2 hzne) ν)]
      exact le_trans (hB z hz) (by
        refine mul_le_mul_of_nonneg_right (le_max_right _ _) ?_
        exact (Real.rpow_pos_of_pos (norm_pos_iff.2 hzne) ν).le)
  rw [hgdef] at hkey
  simp only at hkey
  rw [norm_div, norm_cpow_ofReal_exponent hsne, div_le_iff₀ hpow] at hkey
  exact hkey


/-! ### Lindelöf on the strip `½ ≤ Re s ≤ 3/2` -/

/-- `G(s)/(sΓ_ℝ(s))`, which is `(s − 1)F(s)` without the pole at `s = 1`. -/
def stripG (G : ℂ → ℂ) (s : ℂ) : ℂ := G s / (s * Complex.Gammaℝ s)

theorem prodF_eq_stripG_div (G : ℂ → ℂ) (s : ℂ) : prodF G s = stripG G s / (s - 1) := by
  unfold prodF stripG
  rw [div_div]; congr 1; ring

theorem one_add_abs_im_le_two_norm {z : ℂ} (hz : 1 / 2 ≤ z.re) :
    1 + |z.im| ≤ 2 * ‖z - ((-(1 / 2) : ℝ) : ℂ)‖ := by
  have h1 := Complex.abs_re_le_norm (z - ((-(1 / 2) : ℝ) : ℂ))
  have h2 := Complex.abs_im_le_norm (z - ((-(1 / 2) : ℝ) : ℂ))
  simp only [Complex.sub_re, Complex.ofReal_re, Complex.sub_im, Complex.ofReal_im, sub_zero] at h1 h2
  rw [abs_of_pos (by linarith)] at h1
  linarith

theorem norm_sub_one_le_of_strip {z : ℂ} (hz1 : 1 / 2 ≤ z.re) (hz2 : z.re ≤ 3 / 2) :
    ‖z - 1‖ ≤ 1 + |z.im| := by
  refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
  simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, sub_zero]
  have : |z.re - 1| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
  linarith

/-- **Lindelöf on the strip.**  For every `ν > 0` the producer zeta function satisfies
`|F(x+iy)| ≤ C_ν(1+|y|)^ν` on `½ ≤ x ≤ 3/2`, `|y| ≥ 2`. -/
theorem exists_norm_prodF_le_rpow {lam : ℕ → ℝ} {Φ G : ℂ → ℂ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    (hΦd : DifferentiableOn ℂ Φ {s : ℂ | 1 / 2 < s.re})
    (hΦre : ∀ s : ℂ, 1 / 2 < s.re → 0 ≤ (Φ s).re)
    (hid : ∀ s : ℂ, 1 < s.re →
      Φ s = zetaArchimedeanDatum s + 1 / (s - 1) - LSeries (lamTwo lam) s)
    (hGc : ∀ s : ℂ, 1 / 2 ≤ s.re → ContinuousAt G s)
    (hGd : ∀ s : ℂ, 1 / 2 < s.re → HasDerivAt G (Φ s * G s) s) (hG2 : G 2 = bigG lam 2)
    {ν : ℝ} (hν : 0 < ν) :
    ∃ CF : ℝ, 0 ≤ CF ∧ ∀ x y : ℝ, 1 / 2 ≤ x → x ≤ 3 / 2 → 2 ≤ |y| →
      ‖prodF G ((x : ℂ) + (y : ℂ) * I)‖ ≤ CF * (1 + |y|) ^ ν := by
  obtain ⟨CL, hCL, hline⟩ :=
    FractionalMassPolynomialTailRigidity.exists_norm_phiG_le_rpow_small hsl hΦd hΦre hid hGc
      hGd hG2 hν
  obtain ⟨C2, hC20, hF2⟩ := exists_norm_prodF_le hsl hΦre hid hGc hGd hG2
  set S : ℝ := ∑' n, ‖LSeries.term (lamLog lam) (((3 / 2 : ℝ) : ℂ)) n‖ with hS
  set c₀ : ℝ := -(1 / 2) with hc₀
  have hden : ∀ s : ℂ, 0 < s.re → s * Complex.Gammaℝ s ≠ 0 := fun s hs =>
    mul_ne_zero (by intro h; rw [h] at hs; simp at hs) (Complex.Gammaℝ_ne_zero_of_re_pos hs)
  have hcont : ContinuousOn (stripG G) (Complex.re ⁻¹' Icc (1 / 2) (3 / 2)) := fun z hz =>
    ((hGc z hz.1).div (continuousAt_id.mul
      (differentiableAt_Gammaℝ_of_re_pos (by linarith [hz.1])).continuousAt)
      (hden z (by linarith [hz.1]))).continuousWithinAt
  have hdiff : DifferentiableOn ℂ (stripG G) (Complex.re ⁻¹' Ioo (1 / 2) (3 / 2)) := fun z hz =>
    ((hGd z hz.1).differentiableAt.div (differentiableAt_id.mul
      (differentiableAt_Gammaℝ_of_re_pos (by linarith [hz.1])))
      (hden z (by linarith [hz.1]))).differentiableWithinAt
  have hstrip_eq : ∀ z : ℂ, z ≠ 1 → stripG G z = (z - 1) * prodF G z := by
    intro z hz
    rw [prodF_eq_stripG_div, mul_div_cancel₀ _ (sub_ne_zero.mpr hz)]
  -- polynomial growth on the closed strip
  obtain ⟨Bc, hBc⟩ := IsCompact.exists_bound_of_continuousOn
    (isCompact_Icc.reProdIm (isCompact_Icc (a := (-2 : ℝ)) (b := 2)))
    (hcont.mono fun z hz => hz.1)
  set Cg : ℝ := max (max Bc 0) C2 with hCg
  have hCg0 : 0 ≤ Cg := le_trans (le_max_right _ _) (le_max_left _ _)
  have hgrow : ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 3 / 2 →
      ‖stripG G s‖ ≤ Cg * (1 + |s.im|) ^ (3 / 2 : ℝ) := by
    intro s hs1 hs2
    have hpow1 : 1 ≤ (1 + |s.im|) ^ (3 / 2 : ℝ) :=
      Real.one_le_rpow (by linarith [abs_nonneg s.im]) (by norm_num)
    by_cases hy : |s.im| ≤ 2
    · have h := hBc s ⟨⟨hs1, hs2⟩, abs_le.mp hy⟩
      have : Bc ≤ Cg := le_trans (le_max_left _ _) (le_max_left _ _)
      nlinarith
    · push Not at hy
      have hs1' : s ≠ 1 := by intro h; rw [h] at hy; simp at hy; linarith
      rw [hstrip_eq s hs1', norm_mul]
      have hsx : s = (s.re : ℂ) + (s.im : ℂ) * I := (Complex.re_add_im s).symm
      have hF := hF2 s.re s.im hs1 hs2 hy.le
      rw [← hsx] at hF
      have hs1n := norm_sub_one_le_of_strip hs1 hs2
      calc ‖s - 1‖ * ‖prodF G s‖ ≤ (1 + |s.im|) * (C2 * (1 + |s.im|) ^ (1 / 2 : ℝ)) :=
            mul_le_mul hs1n hF (norm_nonneg _) (by positivity)
        _ = C2 * (1 + |s.im|) ^ (3 / 2 : ℝ) := by
            rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num,
              Real.rpow_add (by linarith [abs_nonneg s.im]), Real.rpow_one]; ring
        _ ≤ Cg * (1 + |s.im|) ^ (3 / 2 : ℝ) := by gcongr; exact le_max_right _ _
  -- the left edge
  have hA : ∀ z : ℂ, z.re = 1 / 2 →
      ‖stripG G z‖ ≤ (CL * 2 ^ (1 + ν)) * ‖z - (c₀ : ℂ)‖ ^ (1 + ν) := by
    intro z hz
    have hz1 : z ≠ 1 := by intro h; rw [h] at hz; norm_num at hz
    have hzl : z = lineS (z.im / 2) := by
      apply Complex.ext
      · rw [lineS_re, hz]
      · rw [lineS_eq]; simp; ring
    have hpz : prodF G z = phiG G (z.im / 2) := by rw [phiG_eq_prodF, ← hzl]
    have hl := hline (z.im / 2)
    have hhalf : (1 + |z.im / 2|) ^ ν ≤ (1 + |z.im|) ^ ν := by
      apply Real.rpow_le_rpow (by positivity) _ hν.le
      rw [abs_div, abs_two]; linarith [abs_nonneg z.im]
    have hsub := norm_sub_one_le_of_strip (z := z) (by rw [hz]) (by rw [hz]; norm_num)
    have htwo := one_add_abs_im_le_two_norm (z := z) (by rw [hz])
    have h1 : ‖stripG G z‖ ≤ CL * (1 + |z.im|) ^ (1 + ν) := by
      rw [hstrip_eq z hz1, norm_mul, hpz, Real.rpow_add (by linarith [abs_nonneg z.im]),
        Real.rpow_one]
      calc ‖z - 1‖ * ‖phiG G (z.im / 2)‖ ≤ (1 + |z.im|) * (CL * (1 + |z.im|) ^ ν) :=
            mul_le_mul hsub (hl.trans (mul_le_mul_of_nonneg_left hhalf hCL)) (norm_nonneg _)
              (by positivity)
        _ = CL * ((1 + |z.im|) * (1 + |z.im|) ^ ν) := by ring
    refine h1.trans ?_
    rw [mul_assoc, ← Real.mul_rpow (by norm_num) (norm_nonneg _)]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (by positivity) htwo (by linarith)) hCL
  -- the right edge
  have hB : ∀ z : ℂ, z.re = 3 / 2 →
      ‖stripG G z‖ ≤ (2 * Real.exp S) * ‖z - (c₀ : ℂ)‖ ^ (1 + ν) := by
    intro z hz
    have hz1 : z ≠ 1 := by intro h; rw [h] at hz; norm_num at hz
    have hre : 1 < z.re := by rw [hz]; norm_num
    have hzeta := norm_zetaOf_le hsl hre
    rw [hz] at hzeta
    have hsub := norm_sub_one_le_of_strip (z := z) (by rw [hz]; norm_num) (by rw [hz])
    have htwo := one_add_abs_im_le_two_norm (z := z) (by rw [hz]; norm_num)
    have hge1 : 1 ≤ ‖z - (c₀ : ℂ)‖ := by
      have := Complex.abs_re_le_norm (z - (c₀ : ℂ))
      simp only [Complex.sub_re, Complex.ofReal_re, hc₀, hz] at this
      rw [show (3 / 2 : ℝ) - -(1 / 2) = 2 by norm_num, abs_two] at this
      linarith
    rw [hstrip_eq z hz1, norm_mul, prodF_eq_zetaOf hsl hid hGd hG2 hre]
    calc ‖z - 1‖ * ‖zetaOf lam z‖ ≤ (2 * ‖z - (c₀ : ℂ)‖) * Real.exp S :=
          mul_le_mul (hsub.trans htwo) hzeta (norm_nonneg _) (by positivity)
      _ = 2 * Real.exp S * ‖z - (c₀ : ℂ)‖ ^ (1 : ℝ) := by rw [Real.rpow_one]; ring
      _ ≤ 2 * Real.exp S * ‖z - (c₀ : ℂ)‖ ^ (1 + ν) := by
          exact mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_exponent_le hge1 (by linarith)) (by positivity)
  have hPL := norm_le_mul_rpow_of_strip_diffContOnCl (F := stripG G) (A := 1 / 2) (B := 3 / 2)
    (ν := 1 + ν) (c₀ := c₀) (by norm_num) (by linarith) (by rw [hc₀]; norm_num) hdiff hcont
    hCg0 (by norm_num) hgrow hA hB
  set Cm : ℝ := max (CL * 2 ^ (1 + ν)) (2 * Real.exp S) with hCm
  have hCm0 : 0 ≤ Cm := le_trans (by positivity) (le_max_right _ _)
  refine ⟨Cm * 2 ^ (2 + ν), by positivity, fun x y hx1 hx2 hy => ?_⟩
  set s : ℂ := (x : ℂ) + (y : ℂ) * I with hsdef
  have hsre : s.re = x := by simp [hsdef]
  have hsim : s.im = y := by simp [hsdef]
  have hs1 : s ≠ 1 := by intro h; rw [h] at hsim; simp at hsim; rw [← hsim] at hy; norm_num at hy
  have hb := hPL s (by rw [hsre]; exact hx1) (by rw [hsre]; exact hx2)
  have hy1 : 0 < 1 + |y| := by linarith [abs_nonneg y]
  have hupper : ‖s - (c₀ : ℂ)‖ ≤ 2 * (1 + |y|) := by
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.sub_im, Complex.ofReal_im, sub_zero,
      hsre, hsim, hc₀]
    rw [abs_of_pos (by linarith)]; linarith [abs_nonneg y]
  have hlower : (1 + |y|) / 2 ≤ ‖s - 1‖ := by
    have := Complex.abs_im_le_norm (s - 1)
    simp only [Complex.sub_im, Complex.one_im, sub_zero, hsim] at this
    linarith
  rw [prodF_eq_stripG_div, norm_div, div_le_iff₀ (by linarith)]
  calc ‖stripG G s‖ ≤ Cm * ‖s - (c₀ : ℂ)‖ ^ (1 + ν) := hb
    _ ≤ Cm * (2 * (1 + |y|)) ^ (1 + ν) := by
        gcongr
    _ = Cm * 2 ^ (2 + ν) * (1 + |y|) ^ ν * ((1 + |y|) / 2) := by
        have e1 : (2 : ℝ) ^ (1 + ν) = 2 * 2 ^ ν := by
          rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_one]
        have e2 : (2 : ℝ) ^ (2 + ν) = 4 * 2 ^ ν := by
          rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2)]; norm_num
        rw [Real.mul_rpow (by norm_num) hy1.le, Real.rpow_add hy1, Real.rpow_one, e1, e2]
        ring
    _ ≤ Cm * 2 ^ (2 + ν) * (1 + |y|) ^ ν * ‖s - 1‖ := by gcongr


/-! ### The layer cake for a phase of power growth -/

/-- `δ^α z ≤ δ z^{1/α}` for `z ≥ δ^{−α}`, `0 < α ≤ 1`. -/
theorem rpow_mul_le_mul_rpow_inv {δ α z : ℝ} (hδ : 0 < δ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hz : δ ^ (-α) ≤ z) : δ ^ α * z ≤ δ * z ^ α⁻¹ := by
  have hz0 : 0 < z := lt_of_lt_of_le (Real.rpow_pos_of_pos hδ _) hz
  have hexp : 0 ≤ α⁻¹ - 1 := by
    rw [sub_nonneg]; exact one_le_inv₀ hα0 |>.mpr hα1
  have e1 : z ^ α⁻¹ = z * z ^ (α⁻¹ - 1) := by
    conv_lhs => rw [show α⁻¹ = 1 + (α⁻¹ - 1) by ring]
    rw [Real.rpow_add hz0, Real.rpow_one]
  have h2 : (δ ^ (-α)) ^ (α⁻¹ - 1) ≤ z ^ (α⁻¹ - 1) :=
    Real.rpow_le_rpow (by positivity) hz hexp
  have e2 : (δ ^ (-α)) ^ (α⁻¹ - 1) = δ ^ (α - 1) := by
    rw [← Real.rpow_mul hδ.le]; congr 1; field_simp; ring
  have e3 : δ * δ ^ (α - 1) = δ ^ α := by
    conv_rhs => rw [show α = 1 + (α - 1) by ring]
    rw [Real.rpow_add hδ, Real.rpow_one]
  have h3 : δ ^ (α - 1) ≤ z ^ (α⁻¹ - 1) := by rw [← e2]; exact h2
  rw [e1]
  calc δ ^ α * z = δ * δ ^ (α - 1) * z := by rw [e3]
    _ ≤ δ * z ^ (α⁻¹ - 1) * z := by gcongr
    _ = δ * (z * z ^ (α⁻¹ - 1)) := by ring

/-- **The layer cake for a level function of power growth.**  Let `C` be monotone with
`C(x) ≤ K x^α` for `x ≥ 1`, `0 < α ≤ 1`, `K > 0`; let `Ψ` be the primitive of a measurable density
`ψ` with `‖ψ‖ ≤ L`; and let `d` satisfy `‖∫_{t ≤ b} d‖ ≤ E e^{bδ}` for all `b ≤ −1`.  Then
`‖∫_{t ≤ −1} Ψ(C(−t)) d(t) dt‖ ≤ E(‖Ψ(C(1))‖ + L((−C(1))⁺ + 2Kδ^{−α}))`. -/
theorem norm_setIntegral_layer_le_pow {d : ℝ → ℂ} {C : ℝ → ℝ} (hC : Monotone C)
    {Ψ ψ : ℝ → ℂ} {L : ℝ} (hL : 0 ≤ L) (hψm : Measurable ψ) (hψL : ∀ x, ‖ψ x‖ ≤ L)
    (hΨ : ∀ u v : ℝ, u ≤ v → Ψ v = Ψ u + ∫ x in Ioi u, (if x ≤ v then ψ x else 0))
    {E δ α K : ℝ} (hδ : 0 < δ) (hα0 : 0 < α) (hα1 : α ≤ 1) (hK : 0 < K) (hE : 0 ≤ E)
    (hgrowth : ∀ x : ℝ, 1 ≤ x → C x ≤ K * x ^ α)
    (hdm : AEStronglyMeasurable d volume) (hdint : IntegrableOn d (Iic (-1)))
    (hdom : IntegrableOn (fun t => (C (-t) - C 1) * ‖d t‖) (Iic (-1)))
    (herr : ∀ b, b ≤ -1 → ‖∫ t in Iic b, d t‖ ≤ E * Real.exp (b * δ)) :
    ‖∫ t in Iic (-1 : ℝ), Ψ (C (-t)) * d t‖ ≤
      E * (‖Ψ (C 1)‖ + L * (max 0 (-C 1) + 2 * K * δ ^ (-α))) := by
  set h : ℝ → ℝ := fun x => Real.exp (-(δ * (x / K) ^ α⁻¹)) with hh
  set x₀ : ℝ := K * δ ^ (-α) with hx₀
  set a : ℝ := δ ^ α / K with ha
  have hx₀0 : 0 < x₀ := by positivity
  have ha0 : 0 < a := by positivity
  have hhc : Continuous h :=
    Real.continuous_exp.comp ((continuous_const.mul ((Real.continuous_rpow_const
      (inv_pos.mpr hα0).le).comp (continuous_id.div_const K))).neg)
  -- the pointwise majorant of `h` on `x > 0`
  have hhle : ∀ x : ℝ, 0 < x → h x ≤ (Iic x₀).indicator (fun _ => (1 : ℝ)) x + Real.exp (-a * x) := by
    intro x hx
    by_cases hxx : x ≤ x₀
    · rw [Set.indicator_of_mem (show x ∈ Iic x₀ from hxx)]
      have : h x ≤ 1 := Real.exp_le_one_iff.mpr (by
        have : 0 ≤ (x / K) ^ α⁻¹ := Real.rpow_nonneg (by positivity) _
        nlinarith)
      linarith [Real.exp_pos (-a * x)]
    · push Not at hxx
      rw [Set.indicator_of_notMem (show x ∉ Iic x₀ from not_le.mpr hxx), zero_add]
      apply Real.exp_le_exp.mpr
      have hz : δ ^ (-α) ≤ x / K := by
        rw [le_div_iff₀ hK]; rw [hx₀] at hxx; linarith
      have := rpow_mul_le_mul_rpow_inv hδ hα0 hα1 hz
      have e : -a * x = -(δ ^ α * (x / K)) := by rw [ha]; field_simp
      rw [e]; linarith
  have hhint : IntegrableOn h (Ioi 0) := by
    have hdomi : IntegrableOn (fun x => (Iic x₀).indicator (fun _ => (1 : ℝ)) x +
        Real.exp (-a * x)) (Ioi 0) := by
      refine IntegrableOn.add ?_ (exp_neg_integrableOn_Ioi 0 ha0)
      rw [IntegrableOn, integrable_indicator_iff measurableSet_Iic]
      refine integrableOn_const (hs := ?_)
      rw [Measure.restrict_apply measurableSet_Iic,
        show Iic x₀ ∩ Ioi 0 = Ioc 0 x₀ by ext; simp [and_comm]]
      exact measure_Ioc_lt_top.ne
    refine hdomi.mono' hhc.aestronglyMeasurable ((ae_restrict_iff' measurableSet_Ioi).mpr
      (Eventually.of_forall fun x hx => ?_))
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact hhle x hx
  have hhI : ∫ x in Ioi (0 : ℝ), h x ≤ 2 * K * δ ^ (-α) := by
    have hint1 : IntegrableOn (fun x => (Iic x₀).indicator (fun _ => (1 : ℝ)) x) (Ioi 0) := by
      rw [IntegrableOn, integrable_indicator_iff measurableSet_Iic]
      refine integrableOn_const (hs := ?_)
      rw [Measure.restrict_apply measurableSet_Iic,
        show Iic x₀ ∩ Ioi 0 = Ioc 0 x₀ by ext; simp [and_comm]]
      exact measure_Ioc_lt_top.ne
    have hle : ∫ x in Ioi (0 : ℝ), h x ≤ ∫ x in Ioi (0 : ℝ),
        ((Iic x₀).indicator (fun _ => (1 : ℝ)) x + Real.exp (-a * x)) :=
      setIntegral_mono_on hhint (hint1.add (exp_neg_integrableOn_Ioi 0 ha0))
        measurableSet_Ioi fun x hx => hhle x hx
    rw [integral_add hint1 (exp_neg_integrableOn_Ioi 0 ha0)] at hle
    have hi1 : ∫ x in Ioi (0 : ℝ), (Iic x₀).indicator (fun _ => (1 : ℝ)) x = x₀ := by
      rw [integral_indicator measurableSet_Iic, Measure.restrict_restrict measurableSet_Iic,
        show Iic x₀ ∩ Ioi 0 = Ioc 0 x₀ by ext; simp [and_comm], setIntegral_const, smul_eq_mul,
        mul_one, Real.volume_real_Ioc, sub_zero, max_eq_left hx₀0.le]
    have hi2 : ∫ x in Ioi (0 : ℝ), Real.exp (-a * x) = K * δ ^ (-α) := by
      rw [integral_exp_mul_Ioi (by linarith) 0, mul_zero, Real.exp_zero, ha,
        Real.rpow_neg hδ.le]
      field_simp
    rw [hi1, hi2] at hle
    linarith
  -- the profile
  set φ : ℝ → ℝ := fun x => (Iic 0).indicator (fun _ => (1 : ℝ)) x + (Ioi 0).indicator h x
    with hφ
  have hφ0 : ∀ x, 0 ≤ φ x := fun x => add_nonneg
    (Set.indicator_nonneg (fun _ _ => zero_le_one) x)
    (Set.indicator_nonneg (fun y _ => (Real.exp_pos _).le) x)
  have hφb : ∀ x b : ℝ, b ≤ -1 → (∀ c : ℝ, (∀ t, t ≤ -1 → x ≤ C (-t) → t ≤ c) → b ≤ c) →
      Real.exp (b * δ) ≤ φ x := by
    intro x b hb1 hub
    by_cases hx : x ≤ 0
    · simp only [hφ, Set.indicator_of_mem (show x ∈ Iic 0 from hx),
        Set.indicator_of_notMem (show x ∉ Ioi 0 from not_lt.mpr hx), add_zero]
      exact Real.exp_le_one_iff.mpr (by nlinarith)
    · push Not at hx
      simp only [hφ, Set.indicator_of_notMem (show x ∉ Iic 0 from not_le.mpr hx),
        Set.indicator_of_mem (show x ∈ Ioi 0 from hx), zero_add, hh]
      have hbx : b ≤ -(x / K) ^ α⁻¹ := by
        refine hub _ fun t ht hxt => ?_
        have h1 : x / K ≤ (-t) ^ α := by
          rw [div_le_iff₀ hK]; linarith [hgrowth (-t) (by linarith)]
        have h2 : (x / K) ^ α⁻¹ ≤ -t :=
          (Real.rpow_inv_le_iff_of_pos (by positivity) (by linarith) hα0).mpr h1
        linarith
      apply Real.exp_le_exp.mpr
      nlinarith
  have hφint : IntegrableOn φ (Ioi (C 1)) := by
    refine IntegrableOn.add ?_ ?_
    · rw [IntegrableOn, integrable_indicator_iff measurableSet_Iic]
      refine integrableOn_const (hs := ?_)
      rw [Measure.restrict_apply measurableSet_Iic]
      refine (measure_mono (t := Ioc (C 1) 0) fun x hx => ⟨hx.2, hx.1⟩).trans_lt
        measure_Ioc_lt_top |>.ne
    · exact ((integrable_indicator_iff measurableSet_Ioi).mpr hhint).integrableOn
  have hφI : ∫ x in Ioi (C 1), φ x ≤ max 0 (-C 1) + 2 * K * δ ^ (-α) := by
    have hint1 : IntegrableOn (fun x => (Iic 0).indicator (fun _ => (1 : ℝ)) x) (Ioi (C 1)) := by
      rw [IntegrableOn, integrable_indicator_iff measurableSet_Iic]
      refine integrableOn_const (hs := ?_)
      rw [Measure.restrict_apply measurableSet_Iic]
      refine (measure_mono (t := Ioc (C 1) 0) fun x hx => ⟨hx.2, hx.1⟩).trans_lt
        measure_Ioc_lt_top |>.ne
    have hint2 : Integrable ((Ioi 0).indicator h) :=
      (integrable_indicator_iff measurableSet_Ioi).mpr hhint
    simp only [hφ]
    rw [integral_add hint1 hint2.integrableOn]
    have hi1 : ∫ x in Ioi (C 1), (Iic 0).indicator (fun _ => (1 : ℝ)) x = max 0 (-C 1) := by
      rw [integral_indicator measurableSet_Iic, Measure.restrict_restrict measurableSet_Iic,
        show Iic 0 ∩ Ioi (C 1) = Ioc (C 1) 0 by ext; simp [and_comm], setIntegral_const,
        smul_eq_mul, mul_one, Real.volume_real_Ioc, zero_sub, max_comm]
    have hi2 : ∫ x in Ioi (C 1), (Ioi 0).indicator h x ≤ 2 * K * δ ^ (-α) := by
      refine (setIntegral_le_integral hint2 (Eventually.of_forall fun x =>
        Set.indicator_nonneg (fun y _ => (Real.exp_pos _).le) x)).trans ?_
      rw [integral_indicator measurableSet_Ioi]
      exact hhI
    linarith
  exact norm_setIntegral_layer_le_of_profile hC hL hψm hψL hΨ hE hδ hdm hdint hdom herr hφ0 hφb
    hφint hφI


/-- **The twisted half-line integral for a phase of power growth.**  Let `C` be monotone with
`C(x) ≤ K x^α` for `x ≥ 1`, `0 < α ≤ 1`, `K > 0`, and let `d` satisfy `‖∫_{t ≤ b} d‖ ≤ E e^{bδ}` for
all `b ≤ −1`.  Then `‖∫_{t ≤ −1} e^{iβ₀C(−t)} d(t) dt‖ ≤ E(1 + |β₀|((−C(1))⁺ + 2Kδ^{−α}))`. -/
theorem norm_setIntegral_twist_le_pow {d : ℝ → ℂ} {C : ℝ → ℝ} (hC : Monotone C)
    {β₀ E δ α K : ℝ} (hδ : 0 < δ) (hα0 : 0 < α) (hα1 : α ≤ 1) (hK : 0 < K) (hE : 0 ≤ E)
    (hgrowth : ∀ x : ℝ, 1 ≤ x → C x ≤ K * x ^ α)
    (hdm : AEStronglyMeasurable d volume) (hdint : IntegrableOn d (Iic (-1)))
    (hdom : IntegrableOn (fun t => (C (-t) - C 1) * ‖d t‖) (Iic (-1)))
    (herr : ∀ b, b ≤ -1 → ‖∫ t in Iic b, d t‖ ≤ E * Real.exp (b * δ)) :
    ‖∫ t in Iic (-1 : ℝ), cexp (((β₀ * C (-t) : ℝ) : ℂ) * I) * d t‖ ≤
      E * (1 + |β₀| * (max 0 (-C 1) + 2 * K * δ ^ (-α))) := by
  have h := norm_setIntegral_layer_le_pow hC (Ψ := fun v => cexp (((β₀ * v : ℝ) : ℂ) * I))
    (ψ := phaseDensity β₀) (abs_nonneg β₀) (continuous_phaseDensity β₀).measurable
    (fun x => (norm_phaseDensity β₀ x).le) (fun u v huv => phase_eq_add_setIntegral β₀ huv)
    hδ hα0 hα1 hK hE hgrowth hdm hdint hdom herr
  rwa [Complex.norm_exp_ofReal_mul_I] at h

/-! ### The twisted remainder for a phase of power growth -/

/-- **The layered remainder vanishes radially for a level function of power growth `α < 1`.**
Here `Ψ` is the primitive of a measurable density `ψ` with `‖ψ‖ ≤ L`. -/
theorem tendsto_layer_remainder_pow {lam : ℕ → ℝ} {Φ G : ℂ → ℂ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    (hΦd : DifferentiableOn ℂ Φ {s : ℂ | 1 / 2 < s.re})
    (hΦre : ∀ s : ℂ, 1 / 2 < s.re → 0 ≤ (Φ s).re)
    (hid : ∀ s : ℂ, 1 < s.re →
      Φ s = zetaArchimedeanDatum s + 1 / (s - 1) - LSeries (lamTwo lam) s)
    (hGc : ∀ s : ℂ, 1 / 2 ≤ s.re → ContinuousAt G s)
    (hGd : ∀ s : ℂ, 1 / 2 < s.re → HasDerivAt G (Φ s * G s) s) (hG2 : G 2 = bigG lam 2)
    {C : ℝ → ℝ} (hC : Monotone C) {α K : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hK : 0 < K)
    (hgrowth : ∀ x : ℝ, 1 ≤ x → C x ≤ K * x ^ α)
    {Ψ ψ : ℝ → ℂ} {L : ℝ} (hL : 0 ≤ L) (hψm : Measurable ψ) (hψL : ∀ x, ‖ψ x‖ ≤ L)
    (hΨ : ∀ u v : ℝ, u ≤ v → Ψ v = Ψ u + ∫ x in Ioi u, (if x ≤ v then ψ x else 0))
    {m : ℕ} (hm : 1 ≤ m) :
    Tendsto (fun ε : ℝ => (ε : ℂ) * ∫ t in Iic (-1 : ℝ), Ψ (C (-t)) *
      remainder G (dirichletExp (lamLog lam) m) m ((ε : ℂ) + (m : ℂ) * I) t) (𝓝[>] 0) (𝓝 0) := by
  set am := dirichletExp (lamLog lam) m with ham
  set ν : ℝ := (1 - α) / 2 with hν
  have hν0 : 0 < ν := by rw [hν]; linarith
  have hν1 : ν ≤ 1 := by rw [hν]; linarith
  obtain ⟨CF, hCF, hF⟩ := exists_norm_prodF_le_rpow hsl hΦd hΦre hid hGc hGd hG2 hν0
  obtain ⟨Kr, hKr⟩ :=
    exists_norm_radialError_le_of_strip hsl hΦre hid hGc hGd hG2 hν0.le hν1 hCF hF hm
  obtain ⟨CB, N, hCB, hpoly⟩ := exists_poly_bound_lineG hsl hΦre hid hGc hGd hG2
  have hK₁ : ∀ x : ℝ, 1 ≤ x → C x ≤ K * (x + 1) := fun x hx => by
    have h1 : x ^ α ≤ x := by
      calc x ^ α ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx hα1.le
        _ = x := Real.rpow_one x
    nlinarith [hgrowth x hx]
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  set A : ℝ := |Kr| * (‖Ψ (C 1)‖ + L * max 0 (-C 1)) with hA
  set B : ℝ := |Kr| * L * (2 * K * ((m : ℝ) + 1) ^ α) with hB
  have hbound : ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ‖(ε : ℂ) * ∫ t in Iic (-1 : ℝ), Ψ (C (-t)) *
        remainder G am m ((ε : ℂ) + (m : ℂ) * I) t‖ ≤
        A * ε ^ (1 - ν) + B * ε ^ (1 - ν - α) := by
    intro ε hε hε1
    set τ : ℂ := (ε : ℂ) + (m : ℂ) * I with hτ
    have hτre : τ.re = ε := by simp [hτ]
    have hτre0 : 0 < τ.re := by rw [hτre]; exact hε
    have hτ0 : τ ≠ 0 := by intro h; rw [h] at hτre0; simp at hτre0
    have hτ1 : 1 ≤ ‖τ‖ := by
      have h := Complex.abs_im_le_norm τ
      have him : τ.im = m := by simp [hτ]
      rw [him, abs_of_nonneg (Nat.cast_nonneg m)] at h; linarith
    have hτM : ‖τ‖ ≤ m + 1 := by
      have h := norm_add_le (ε : ℂ) ((m : ℂ) * I)
      rw [Complex.norm_real, norm_mul, Complex.norm_I, mul_one, Complex.norm_natCast,
        Real.norm_eq_abs, abs_of_pos hε] at h
      linarith
    have hτpos : 0 < ‖τ‖ := by linarith
    set δ : ℝ := ε / ‖τ‖ with hδ
    have hδ0 : 0 < δ := div_pos hε hτpos
    set d : ℝ → ℂ := fun t => (ε : ℂ) * remainder G am m τ t with hd
    have hdc : Continuous d := continuous_const.mul (continuous_remainder hGc am hm hτ0)
    have hphik := MonotoneTwistLock.integrable_phiG_mul_pairKernel hsl hΦre hid hGc hGd hG2 hτre0
    have hrho := integrableOn_rhoMain hm hτre0 hτ1
    have hdint : IntegrableOn d (Iic (-1)) :=
      (hphik.integrableOn.sub (hrho.const_mul am)).const_mul (ε : ℂ)
    have hdom : IntegrableOn (fun t => (C (-t) - C 1) * ‖d t‖) (Iic (-1)) :=
      integrableOn_phase_mul_remainder hCB (fun t => (hpoly t).1) hGc hC hK₁ am hm hτre0 hτ1 _
    have herr : ∀ b, b ≤ -1 → ‖∫ t in Iic b, d t‖ ≤ (|Kr| * ε ^ (1 - ν)) * Real.exp (b * δ) := by
      intro b hb
      have h1 : ∫ t in Iic b, d t = (ε : ℂ) * ((∫ t in Iic b, phiG G t * pairKernel (2 * t) τ) -
          am * ∫ t in Iic b, rhoMain m τ t) := by
        simp only [hd, remainder]
        rw [integral_const_mul, integral_sub hphik.integrableOn
          ((hrho.mono_set (Iic_subset_Iic.mpr hb)).const_mul am), integral_const_mul]
      rw [h1]
      refine (hKr ε hε hε1 b hb).trans ?_
      gcongr
      exact le_abs_self Kr
    have htw := norm_setIntegral_layer_le_pow hC hL hψm hψL hΨ hδ0 hα0 hα1.le hK
      (by positivity) hgrowth hdc.aestronglyMeasurable hdint hdom herr
    have e1 : (ε : ℂ) * ∫ t in Iic (-1 : ℝ), Ψ (C (-t)) *
        remainder G am m τ t = ∫ t in Iic (-1 : ℝ), Ψ (C (-t)) * d t := by
      rw [← integral_const_mul]; congr 1; funext t; simp only [hd]; ring
    rw [e1]
    refine htw.trans ?_
    have hδα : δ ^ (-α) ≤ ((m : ℝ) + 1) ^ α * ε ^ (-α) := by
      rw [hδ, Real.div_rpow hε.le hτpos.le, Real.rpow_neg hτpos.le, div_inv_eq_mul, mul_comm]
      gcongr
    have hεmul : ε ^ (1 - ν) * ε ^ (-α) = ε ^ (1 - ν - α) := by
      rw [← Real.rpow_add hε]; ring_nf
    have hM0 : 0 ≤ max 0 (-C 1) := le_max_left _ _
    calc |Kr| * ε ^ (1 - ν) * (‖Ψ (C 1)‖ + L * (max 0 (-C 1) + 2 * K * δ ^ (-α)))
        = A * ε ^ (1 - ν) + |Kr| * L * (2 * K) * (ε ^ (1 - ν) * δ ^ (-α)) := by
          rw [hA]; ring
      _ ≤ A * ε ^ (1 - ν) + |Kr| * L * (2 * K) *
            (ε ^ (1 - ν) * (((m : ℝ) + 1) ^ α * ε ^ (-α))) := by gcongr
      _ = A * ε ^ (1 - ν) + B * ε ^ (1 - ν - α) := by rw [hB, ← hεmul]; ring
  have hp : 0 < 1 - ν := by linarith
  have hq : 0 < 1 - ν - α := by rw [hν]; linarith
  have hlim : Tendsto (fun ε : ℝ => A * ε ^ (1 - ν) + B * ε ^ (1 - ν - α)) (𝓝[>] 0) (𝓝 0) := by
    have h1 : Tendsto (fun ε : ℝ => ε ^ (1 - ν)) (𝓝[>] 0) (𝓝 ((0 : ℝ) ^ (1 - ν))) :=
      ((Real.continuous_rpow_const hp.le).tendsto 0).mono_left nhdsWithin_le_nhds
    have h2 : Tendsto (fun ε : ℝ => ε ^ (1 - ν - α)) (𝓝[>] 0) (𝓝 ((0 : ℝ) ^ (1 - ν - α))) :=
      ((Real.continuous_rpow_const hq.le).tendsto 0).mono_left nhdsWithin_le_nhds
    rw [Real.zero_rpow hp.ne'] at h1
    rw [Real.zero_rpow hq.ne'] at h2
    simpa using (h1.const_mul A).add (h2.const_mul B)
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with ε hε
  exact hbound ε hε.1 hε.2.le

/-- **The twisted remainder vanishes radially for a phase of power growth `α < 1`.** -/
theorem tendsto_twisted_remainder_pow {lam : ℕ → ℝ} {Φ G : ℂ → ℂ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    (hΦd : DifferentiableOn ℂ Φ {s : ℂ | 1 / 2 < s.re})
    (hΦre : ∀ s : ℂ, 1 / 2 < s.re → 0 ≤ (Φ s).re)
    (hid : ∀ s : ℂ, 1 < s.re →
      Φ s = zetaArchimedeanDatum s + 1 / (s - 1) - LSeries (lamTwo lam) s)
    (hGc : ∀ s : ℂ, 1 / 2 ≤ s.re → ContinuousAt G s)
    (hGd : ∀ s : ℂ, 1 / 2 < s.re → HasDerivAt G (Φ s * G s) s) (hG2 : G 2 = bigG lam 2)
    {C : ℝ → ℝ} (hC : Monotone C) {α K : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hK : 0 < K)
    (hgrowth : ∀ x : ℝ, 1 ≤ x → C x ≤ K * x ^ α) (β₀ : ℝ) {m : ℕ} (hm : 1 ≤ m) :
    Tendsto (fun ε : ℝ => (ε : ℂ) * ∫ t in Iic (-1 : ℝ), cexp (((β₀ * C (-t) : ℝ) : ℂ) * I) *
      remainder G (dirichletExp (lamLog lam) m) m ((ε : ℂ) + (m : ℂ) * I) t) (𝓝[>] 0) (𝓝 0) :=
  tendsto_layer_remainder_pow hsl hΦd hΦre hid hGc hGd hG2 hC hα0 hα1 hK hgrowth
    (Ψ := fun v => cexp (((β₀ * v : ℝ) : ℂ) * I)) (ψ := phaseDensity β₀) (abs_nonneg β₀)
    (continuous_phaseDensity β₀).measurable (fun x => (norm_phaseDensity β₀ x).le)
    (fun _ _ huv => phase_eq_add_setIntegral β₀ huv) hm

/-! ### The theorems -/

/-- **Abelian twist rigidity up to the linear wall.**  Let `G` be a Herglotz producer for the
weights `lam`.  Suppose that on the lower critical line `G(1 − s) = κ₀ e^{iβ₀C(−τ)} G(s)`,
`s = ½ + 2iτ`, `τ < 0`, where `C` is monotone and `C(x) ≤ K x^α` for `x ≥ 1`, for some `α < 1`.
Then `lam(n) = Λ(n)` for all `n ≥ 2`, and RH holds. -/
theorem abelian_twist_power_rigidity {lam : ℕ → ℝ} {Φ G : ℂ → ℂ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    (hΦd : DifferentiableOn ℂ Φ {s : ℂ | 1 / 2 < s.re})
    (hΦre : ∀ s : ℂ, 1 / 2 < s.re → 0 ≤ (Φ s).re)
    (hid : ∀ s : ℂ, 1 < s.re → Φ s = zetaArchimedeanDatum s + 1 / (s - 1) -
      LSeries (fun n => if 2 ≤ n then (lam n : ℂ) else 0) s)
    (hGc : ∀ s : ℂ, 1 / 2 ≤ s.re → ContinuousAt G s)
    (hGd : ∀ s : ℂ, 1 / 2 < s.re → HasDerivAt G (Φ s * G s) s) (hG2 : G 2 = bigG lam 2)
    {C : ℝ → ℝ} (hC : Monotone C)
    (hgrowth : ∃ α K : ℝ, α < 1 ∧ ∀ x : ℝ, 1 ≤ x → C x ≤ K * x ^ α)
    {κ₀ : ℂ} {β₀ : ℝ}
    (hlock : ∀ τ : ℝ, τ < 0 →
      G (1 - lineS τ) = κ₀ * cexp (((β₀ * C (-τ) : ℝ) : ℂ) * I) * G (lineS τ)) :
    (∀ n : ℕ, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n) ∧ RiemannHypothesis := by
  have hidT : ∀ s : ℂ, 1 < s.re →
      Φ s = zetaArchimedeanDatum s + 1 / (s - 1) - LSeries (lamTwo lam) s := hid
  obtain ⟨α, K, hα1, hCK⟩ := hgrowth
  set α' : ℝ := max α (1 / 2) with hα'
  set K' : ℝ := |K| + 1 with hK'
  have hα'0 : 0 < α' := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have hα'1 : α' < 1 := max_lt hα1 (by norm_num)
  have hC' : ∀ x : ℝ, 1 ≤ x → C x ≤ K' * x ^ α' := by
    intro x hx
    have h1 : x ^ α ≤ x ^ α' := Real.rpow_le_rpow_of_exponent_le hx (le_max_left _ _)
    have h0 : 0 ≤ x ^ α := Real.rpow_nonneg (by linarith) _
    have h2 := hCK x hx
    have h3 : K * x ^ α ≤ |K| * x ^ α := mul_le_mul_of_nonneg_right (le_abs_self K) h0
    have h4 : |K| * x ^ α ≤ K' * x ^ α' := by
      rw [hK']; nlinarith [abs_nonneg K]
    linarith
  exact abelian_twist_rigidity_of_remainder hsl hΦd hΦre hid hGc hGd hG2 hC.measurable hlock fun _ hm =>
    tendsto_twisted_remainder_pow hsl hΦd hΦre hidT hGc hGd hG2 hC hα'0 hα'1
      (by positivity) hC' β₀ hm

/-- **Real spectral mass of order `T^α`, `α < 1`, forces `Λ` and RH.**  The hypotheses of
`FractionalMassTailRigidity.fractional_mass_tail_rigidity`, with the tail condition replaced by
`C(y) = Σ_{u_k < y} c_k ≤ K y^α` for `y ≥ 1`, for some `α < 1`. -/
theorem fractional_mass_power_growth_rigidity {lam : ℕ → ℝ} {m : ℕ → ℕ} {t : ℕ → ℝ}
    {c u : ℕ → ℝ} (hone : ∀ j, 1 ≤ t j) (hsum : Summable fun j => (m j : ℝ) / t j ^ 2)
    (hc : ∀ k, 0 ≤ c k) (hu1 : ∀ k, 1 ≤ u k) (hut : Tendsto u atTop atTop)
    (hgrowth : ∃ α K : ℝ, α < 1 ∧ ∀ y : ℝ, 1 ≤ y → phaseSum c u y ≤ K * y ^ α)
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    (hid : ∀ s : ℂ, 1 < s.re → zetaArchimedeanDatum s + 1 / (s - 1) -
      LSeries (fun n => if 2 ≤ n then (lam n : ℂ) else 0) s =
        atomicPairSeries (fun j => Real.pi * m j) t s +
          ∑' k, (c k : ℂ) * (2 * (s - 1 / 2) / ((s - 1 / 2) ^ 2 + (u k : ℂ) ^ 2))) :
    (∀ n : ℕ, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n) ∧ RiemannHypothesis := by
  obtain ⟨α, K, hα1, hCK⟩ := hgrowth
  have hcs2 : Summable fun k => c k / u k ^ 2 :=
    summable_div_sq_of_phaseSum_le hc hu1 hut (K := |K|) (K' := 0) fun y hy => by
      have h1 : y ^ α ≤ y := by
        calc y ^ α ≤ y ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hy hα1.le
          _ = y := Real.rpow_one y
      have h0 : 0 ≤ y ^ α := Real.rpow_nonneg (by linarith) _
      have h2 : K * y ^ α ≤ |K| * y ^ α := mul_le_mul_of_nonneg_right (le_abs_self K) h0
      nlinarith [hCK y hy, abs_nonneg K]
  set G := gInf lam m t c u with hGdef
  set Φ := phiInf m t c u with hΦdef
  have hid' : ∀ s : ℂ, 1 < s.re → Φ s = zetaArchimedeanDatum s + 1 / (s - 1) -
      LSeries (fun n => if 2 ≤ n then (lam n : ℂ) else 0) s := fun s hs => (hid s hs).symm
  have hΦd : DifferentiableOn ℂ Φ {s : ℂ | 1 / 2 < s.re} :=
    differentiableOn_phiInf lam hone hsum hc hu1 hut hcs2
  have hΦre : ∀ s : ℂ, 1 / 2 < s.re → 0 ≤ (Φ s).re := fun s hs =>
    re_phiInf_nonneg hc hu1 hut hcs2 hs
  have hGc : ∀ s : ℂ, 1 / 2 ≤ s.re → ContinuousAt G s := fun s hs =>
    continuousAt_gInf hone hsum hc hu1 hut hcs2 hs
  have hGd : ∀ s : ℂ, 1 / 2 < s.re → HasDerivAt G (Φ s * G s) s := fun s hs =>
    hasDerivAt_gInf hone hsum hc hu1 hut hcs2 hs
  have hG2 : G 2 = bigG lam 2 := gInf_two hone hsum hc hu1 hut hcs2
  set C : ℝ → ℝ := fun x => phaseSum c u (2 * x) with hCdef
  have hCm : Monotone C := fun a b h => phaseSum_mono hc hut (by linarith)
  have hCg : ∃ α K : ℝ, α < 1 ∧ ∀ x : ℝ, 1 ≤ x → C x ≤ K * x ^ α := by
    refine ⟨α, K * 2 ^ α, hα1, fun x hx => ?_⟩
    have h := hCK (2 * x) (by linarith)
    rw [Real.mul_rpow (by norm_num) (by linarith)] at h
    simp only [hCdef]; linarith
  have hlock : ∀ τ : ℝ, τ < 0 → G (1 - lineS τ) =
      1 * cexp ((((2 * Real.pi) * C (-τ) : ℝ) : ℂ) * I) * G (lineS τ) := by
    intro τ hτ0
    have hy : 0 < -(2 * τ) := by linarith
    have hline : lineS τ = 1 / 2 - ((-(2 * τ) : ℝ) : ℂ) * I := by
      rw [lineS_eq]; push_cast; ring
    have hre : (1 / 2 : ℝ) ≤ (lineS τ).re := le_of_eq (lineS_re τ).symm
    have hC : C (-τ) = phaseSum c u (-(2 * τ)) := by
      simp only [hCdef]; congr 1; ring
    rw [hC]
    simp only [hGdef, gInf]
    rw [atomQ_one_sub hone hsum, one_sub_lineS_eq_conj, fracInfProd_conj hc hu1 hut hcs2 hre,
      hline, conj_fracInfProd_lower hc hu1 hut hcs2 hy]
    ring
  exact abelian_twist_power_rigidity hsl hΦd hΦre hid' hGc hGd hG2 hCm hCg hlock

end

end AbelianTwist

end RHTower
