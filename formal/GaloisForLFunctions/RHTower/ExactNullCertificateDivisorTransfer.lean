import GaloisForLFunctions.RHTower.RiemannTower
import GaloisForLFunctions.HTGeometry.DecayingStripVerticalShift

/-!
# Exact-null tests: blindness at `log ℕ` is a ζ-free condition

Let `R` be holomorphic on `½ ≤ Re s ≤ 3`, with `ξ²R` and `G²R` decaying like `1/(1+t²)`, where
`G(s) = s(s−1)Γ_ℝ(s)/2` is the archimedean factor of `ξ = Gζ`. Consider the test `g` with
`ĝ(t) = Ξ(t)² R(½+it)`, `Ξ(t) = ξ(½+it)`. Shifting to `Re s = 3` and expanding
`ζ(s)² = Σ d(m) m^{−s}` gives, for `n ≥ 1` (`integral_xi_sq_mul_cpow_eq_tsum`),

`∫ Ξ(t)² R(½+it) n^{−(½+it)} dt = 2π Σ_m d(m) Ψ_R(mn)`,  `Ψ_R = 𝓜^{−1}_3[G² R]`.

The Dirichlet inverse of `d = ζ ⋆ ζ` is `μ ⋆ μ`, so the dilation transform `Ψ ↦ Σ_m d(m)Ψ(m·)`
inverts on functions with `Ψ(N) = O(N^{−3})` (`eq_zero_of_divisorDilation_eq_zero`). Hence
(`logNode_blind_iff_certKernel_vanishes`): `g` vanishes at every `log n`, `n ≥ 2`, if and only if
the ζ-free kernel `Ψ_R` vanishes at every integer `n ≥ 2`; then `∫ Ξ² R = 2π Ψ_R(1)`
(`integral_xi_sq_eq_certKernel_one`).

For `R ≥ 0` on the critical line, `ĝ ≥ 0` vanishes at every nontrivial zero, so `g` is a positive
exact-null test. Its existence with blindness at `log ℕ_{≥2}` is therefore the question whether some
positive `R` has `𝓜^{−1}[G²R]` vanishing on `ℕ_{≥2}` and not at `1`. On the line
`G(½+it)² = |G(½+it)|² e^{2iθ(t)}` with `θ` the Riemann–Siegel theta function, so the condition is
`∫ R(t) |G(½+it)|² cos(2θ(t) − t log n) dt = 0` for every `n ≥ 2`. For even `R` the kernel `Ψ_R`
is a fixed point of the Voronoi involution of `ζ(s)²` (multiplier `Γ_ℝ(s)²/Γ_ℝ(1−s)²`).
-/

open Complex MeasureTheory ArithmeticFunction LSeries
open scoped ArithmeticFunction.zeta ArithmeticFunction.Moebius LSeries.notation

noncomputable section

namespace RHTower.ExactNullDivisorTransfer

/-- **Dilation convolution.** `Σ_k Σ_m a(k) b(m) f(km) = Σ_N (a ⍟ b)(N) f(N)` under absolute
convergence, when `a(0) = b(0) = 0`. -/
theorem tsum_tsum_mul_comp_mul {a b f : ℕ → ℂ} (ha : a 0 = 0) (hb : b 0 = 0)
    (h : Summable fun p : ℕ × ℕ => a p.1 * b p.2 * f (p.1 * p.2)) :
    ∑' k, ∑' m, a k * b m * f (k * m) = ∑' N, (a ⍟ b) N * f N := by
  rw [← h.tsum_prod]
  have hfib := h.hasSum.tsum_fiberwise (fun p : ℕ × ℕ => p.1 * p.2)
  rw [← hfib.tsum_eq]
  refine tsum_congr fun N => ?_
  rcases eq_or_ne N 0 with rfl | hN
  · have hS : (fun p : ℕ × ℕ => p.1 * p.2) ⁻¹' {0} = {0} ×ˢ Set.univ ∪ Set.univ ×ˢ {0} := by
      ext; simp
    have : ∀ p : (fun p : ℕ × ℕ => p.1 * p.2) ⁻¹' {0},
        a p.val.1 * b p.val.2 * f (p.val.1 * p.val.2) = 0 := by
      rintro ⟨⟨k, m⟩, hp⟩
      rcases hS ▸ hp with ⟨hk, -⟩ | ⟨-, hm⟩
      · simp only [Set.mem_singleton_iff] at hk; simp [hk, ha]
      · simp only [Set.mem_singleton_iff] at hm; simp [hm, hb]
    simp [this]
  · rw [show (fun p : ℕ × ℕ => p.1 * p.2) ⁻¹' {N} = (N.divisorsAntidiagonal : Set (ℕ × ℕ)) by
      ext; simp [hN],
      Finset.tsum_subtype' N.divisorsAntidiagonal fun p => a p.1 * b p.2 * f (p.1 * p.2),
      LSeries.convolution_def, Finset.sum_mul]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [(Nat.mem_divisorsAntidiagonal.mp hp).1]

/-- `μ ⋆ μ` as a complex sequence. -/
def moebiusSq (n : ℕ) : ℂ := (((moebius * moebius : ArithmeticFunction ℤ) n : ℤ) : ℂ)

/-- The divisor count `d(n) = #{d ∣ n}` as a complex sequence. -/
def divisorCard (n : ℕ) : ℂ := (n.divisors.card : ℂ)

theorem divisorCard_eq_zetaSq (n : ℕ) :
    divisorCard n = ((((ζ : ArithmeticFunction ℤ) * ζ) n : ℤ) : ℂ) := by
  have h : ((ζ : ArithmeticFunction ℕ) * ζ) = sigma 0 := by
    rw [← zeta_mul_pow_eq_sigma, pow_zero_eq_zeta]
  have h' : (((ζ : ArithmeticFunction ℤ) * ζ) n : ℤ) = ((sigma 0 n : ℕ) : ℤ) := by
    rw [← h, ← ArithmeticFunction.natCoe_mul, ArithmeticFunction.natCoe_apply]
  rw [divisorCard, h', sigma_zero_apply]
  push_cast; rfl

/-- `(μ ⋆ μ) ⋆ (ζ ⋆ ζ) = δ₁`. -/
theorem moebiusSq_convolution_divisorCard :
    moebiusSq ⍟ divisorCard = fun n => if n = 1 then 1 else 0 := by
  have key : (moebius * moebius : ArithmeticFunction ℤ) * ((ζ : ArithmeticFunction ℤ) * ζ) = 1 := by
    rw [mul_mul_mul_comm, moebius_mul_coe_zeta, one_mul]
  funext n
  rw [LSeries.convolution_def]
  dsimp only
  have h := congrArg (fun F : ArithmeticFunction ℤ => ((F n : ℤ) : ℂ)) key
  simp only [moebiusSq, divisorCard_eq_zetaSq]
  simp only [ArithmeticFunction.mul_apply, Int.cast_sum, Int.cast_mul,
    ArithmeticFunction.one_apply] at h ⊢
  rw [h]
  split_ifs <;> simp

theorem norm_moebiusSq_le (n : ℕ) : ‖moebiusSq n‖ ≤ n.divisors.card := by
  rw [moebiusSq, ArithmeticFunction.mul_apply, Complex.norm_intCast]
  push_cast
  calc |∑ x ∈ n.divisorsAntidiagonal, (moebius x.1 : ℝ) * moebius x.2|
      ≤ ∑ x ∈ n.divisorsAntidiagonal, |(moebius x.1 : ℝ) * moebius x.2| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _x ∈ n.divisorsAntidiagonal, (1 : ℝ) := by
        refine Finset.sum_le_sum fun x _ => ?_
        rw [abs_mul]
        have h1 : |(moebius x.1 : ℝ)| ≤ 1 := by exact_mod_cast abs_moebius_le_one
        have h2 : |(moebius x.2 : ℝ)| ≤ 1 := by exact_mod_cast abs_moebius_le_one
        nlinarith [abs_nonneg (moebius x.1 : ℝ), abs_nonneg (moebius x.2 : ℝ)]
    _ = n.divisors.card := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_one, ← Nat.map_div_right_divisors, Finset.card_map]

theorem moebiusSq_zero : moebiusSq 0 = 0 := by simp [moebiusSq]

theorem divisorCard_zero : divisorCard 0 = 0 := by simp [divisorCard]

theorem norm_divisorCard_le (n : ℕ) : ‖divisorCard n‖ ≤ n := by
  rw [divisorCard, Complex.norm_natCast]
  exact_mod_cast Nat.card_divisors_le_self n

/-- **Dilation inversion for the divisor function.** If `Ψ(N) = O(N^{-3})` and the divisor
dilation transform `Σ_m d(m) Ψ(mj)` vanishes for every `j ≥ 2`, then `Ψ` vanishes on `ℕ_{≥2}`. -/
theorem eq_zero_of_divisorDilation_eq_zero {Ψ : ℕ → ℂ} {C : ℝ}
    (hΨ : ∀ N : ℕ, 1 ≤ N → ‖Ψ N‖ ≤ C / (N : ℝ) ^ 3)
    (hblind : ∀ j : ℕ, 2 ≤ j → ∑' m, divisorCard m * Ψ (m * j) = 0) :
    ∀ n : ℕ, 2 ≤ n → Ψ n = 0 := by
  intro n hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hC : 0 ≤ C := by
    have := hΨ 1 le_rfl
    simp at this
    linarith [norm_nonneg (Ψ 1)]
  -- summability of the double series
  have hsq : Summable fun k : ℕ => ((k : ℝ) ^ 2)⁻¹ := by
    simp [Real.summable_nat_pow_inv.mpr (by norm_num : 1 < 2)]
  have hprod : Summable fun p : ℕ × ℕ => ‖((p.1 : ℝ) ^ 2)⁻¹‖ * ‖((p.2 : ℝ) ^ 2)⁻¹‖ := by
    have := summable_mul_of_summable_norm (f := fun k : ℕ => ((k : ℝ) ^ 2)⁻¹)
      (g := fun k : ℕ => ((k : ℝ) ^ 2)⁻¹) (by simp [hsq]) (by simp [hsq])
    refine (this.norm).congr fun p => ?_
    simp [norm_mul]
  have hsum : Summable fun p : ℕ × ℕ =>
      moebiusSq p.1 * divisorCard p.2 * Ψ (p.1 * p.2 * n) := by
    refine Summable.of_norm_bounded ((hprod.mul_left (C / (n : ℝ) ^ 3))) fun p => ?_
    obtain ⟨k, m⟩ := p
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp [moebiusSq_zero]
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp [divisorCard_zero]
    have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
    have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
    have hN : 1 ≤ k * m * n := Nat.one_le_iff_ne_zero.mpr (by positivity)
    have h1 := norm_moebiusSq_le k
    have h1' : (k.divisors.card : ℝ) ≤ k := by exact_mod_cast Nat.card_divisors_le_self k
    have h2 := norm_divisorCard_le m
    have h3 := hΨ _ hN
    rw [norm_mul, norm_mul]
    simp only [norm_inv, norm_pow, Real.norm_natCast]
    push_cast at h3
    calc ‖moebiusSq k‖ * ‖divisorCard m‖ * ‖Ψ (k * m * n)‖
        ≤ (k : ℝ) * m * (C / ((k : ℝ) * m * n) ^ 3) := by
          gcongr
          · exact h1.trans h1'
    _ = C / (n : ℝ) ^ 3 * (((k : ℝ) ^ 2)⁻¹ * ((m : ℝ) ^ 2)⁻¹) := by
          field_simp
  have hinv := tsum_tsum_mul_comp_mul (f := fun N => Ψ (N * n)) moebiusSq_zero divisorCard_zero
    hsum
  rw [moebiusSq_convolution_divisorCard] at hinv
  have hrhs : (∑' N, (if N = 1 then (1 : ℂ) else 0) * Ψ (N * n)) = Ψ n := by
    rw [tsum_eq_single 1 (fun N hN => by simp [hN])]
    simp
  have hlhs : (∑' k, ∑' m, moebiusSq k * divisorCard m * Ψ (k * m * n)) = 0 := by
    refine (tsum_congr fun k => ?_).trans tsum_zero
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp [moebiusSq_zero]
    have hkn : 2 ≤ k * n := le_trans hn (Nat.le_mul_of_pos_left n hk)
    have : (∑' m, moebiusSq k * divisorCard m * Ψ (k * m * n)) =
        moebiusSq k * ∑' m, divisorCard m * Ψ (m * (k * n)) := by
      rw [← tsum_mul_left]
      refine tsum_congr fun m => ?_
      rw [show k * m * n = m * (k * n) by ring]; ring
    rw [this, hblind _ hkn, mul_zero]
  rw [← hrhs, ← hinv]
  exact hlhs

/-- The archimedean factor of `ξ`: `G(s) = s(s−1)/2 · Γ_ℝ(s)`, so that `ξ = G·ζ` off `s = 0, 1`. -/
def archXi (s : ℂ) : ℂ := s * (s - 1) / 2 * Gammaℝ s

theorem xi_eq_archXi_mul_zeta {s : ℂ} (hs : 1 < s.re) : xi s = archXi s * riemannZeta s := by
  have h0 : s ≠ 0 := by rintro rfl; norm_num at hs
  have h1 : s ≠ 1 := by rintro rfl; norm_num at hs
  have hG : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos (by linarith)
  rw [xi_eq_half_mul h0 h1, riemannZeta_def_of_ne_zero h0, archXi]
  field_simp

theorem one_convolution_one : ((fun _ => 1 : ℕ → ℂ) ⍟ fun _ => 1) = divisorCard := by
  funext n
  rw [LSeries.convolution_def]
  simp only [mul_one, Finset.sum_const, nsmul_eq_mul, divisorCard]
  rw [← Nat.map_div_right_divisors, Finset.card_map]

/-- `ζ(s)² = Σ d(m) m^{−s}` on `Re s > 1`. -/
theorem riemannZeta_sq_eq_tsum {s : ℂ} (hs : 1 < s.re) :
    riemannZeta s ^ 2 = ∑' m : ℕ, divisorCard m * (m : ℂ) ^ (-s) := by
  have h1 : LSeriesSummable (fun _ => 1 : ℕ → ℂ) s := LSeriesSummable_one_iff.mpr hs
  have := LSeries_convolution' h1 h1
  rw [one_convolution_one] at this
  have hz : LSeries (fun _ => 1 : ℕ → ℂ) s = riemannZeta s := LSeries_one_eq_riemannZeta hs
  rw [sq, ← hz, ← this, LSeries]
  refine tsum_congr fun m => ?_
  rw [term_def]
  rcases eq_or_ne m 0 with rfl | hm
  · simp [divisorCard]
  · rw [if_neg hm, div_eq_mul_inv, Complex.cpow_neg]

theorem differentiableAt_archXi {s : ℂ} (hs : 0 < s.re) : DifferentiableAt ℂ archXi s := by
  have hhalf : ∀ m : ℕ, s / 2 ≠ -m := by
    intro m h
    have hre : (s / 2).re = -(m : ℝ) := by rw [h]; simp
    have : (s / 2).re = s.re / 2 := by simp
    rw [this] at hre
    have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  have hdπ : DifferentiableAt ℂ (fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2)) s :=
    DifferentiableAt.const_cpow (by fun_prop) (Or.inl (by simp [Real.pi_ne_zero]))
  have hdΓ : DifferentiableAt ℂ (fun z : ℂ => Complex.Gamma (z / 2)) s :=
    (Complex.differentiableAt_Gamma (s / 2) hhalf).comp s (by fun_prop)
  have hG : DifferentiableAt ℂ Gammaℝ s := by
    have : Gammaℝ = fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2) * Complex.Gamma (z / 2) := by
      funext z; rw [Gammaℝ_def]
    rw [this]; exact hdπ.mul hdΓ
  unfold archXi
  exact (by fun_prop : DifferentiableAt ℂ (fun z : ℂ => z * (z - 1) / 2) s).mul hG

theorem norm_natCast_cpow_neg_re_le_one {n : ℕ} (hn : 1 ≤ n) {s : ℂ} (hs : 0 ≤ s.re) :
    ‖(n : ℂ) ^ (-s)‖ ≤ 1 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rw [show ((n : ℂ)) = ((n : ℝ) : ℂ) by push_cast; rfl,
    Complex.norm_cpow_eq_rpow_re_of_pos hn0, neg_re]
  exact Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hn) (by linarith)

/-- **Divisor transfer.** For `R` holomorphic on `½ ≤ Re s ≤ 3` with `ξ²R` and `G²R` (on `Re s = 3`)
decaying like `1/(1+t²)`, the line integral of `ξ(s)² R(s) n^{−s}` over `Re s = ½` equals
`2π Σ_m d(m) Ψ(mn)`, where `Ψ = 𝓜^{−1}_3[G² R]` and `G = s(s−1)Γ_ℝ(s)/2`. -/
theorem integral_xi_sq_mul_cpow_eq_tsum (R : ℂ → ℂ)
    (hR : ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 3 → DifferentiableAt ℂ R s)
    {C : ℝ} (hC : ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 3 → ‖xi s ^ 2 * R s‖ ≤ C / (1 + s.im ^ 2))
    {C' : ℝ} (hC' : ∀ t : ℝ, ‖archXi (3 + t * I) ^ 2 * R (3 + t * I)‖ ≤ C' / (1 + t ^ 2))
    {n : ℕ} (hn : 1 ≤ n) :
    ∫ t : ℝ, xi (1 / 2 + t * I) ^ 2 * R (1 / 2 + t * I) * (n : ℂ) ^ (-(1 / 2 + t * I)) =
      2 * Real.pi * ∑' m : ℕ, divisorCard m *
        mellinInv 3 (fun s => archXi s ^ 2 * R s) ((m * n : ℕ) : ℝ) := by
  set Φ : ℂ → ℂ := fun s => xi s ^ 2 * R s * (n : ℂ) ^ (-s) with hΦ
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hstrip : ∀ s : ℂ, s.re ∈ Set.uIcc (1 / 2 : ℝ) 3 → 1 / 2 ≤ s.re ∧ s.re ≤ 3 := by
    intro s hs
    rw [Set.uIcc_of_le (by norm_num)] at hs
    exact hs
  have hd : ∀ s : ℂ, s.re ∈ Set.uIcc (1 / 2 : ℝ) 3 → DifferentiableAt ℂ Φ s := by
    intro s hs
    obtain ⟨h1, h2⟩ := hstrip s hs
    have hx : DifferentiableAt ℂ xi s := xi_differentiable s
    have hc : DifferentiableAt ℂ (fun s : ℂ => (n : ℂ) ^ (-s)) s :=
      (differentiableAt_id.neg).const_cpow (Or.inl hn0)
    exact ((hx.pow 2).mul (hR s h1 h2)).mul hc
  have hb : ∀ s : ℂ, s.re ∈ Set.uIcc (1 / 2 : ℝ) 3 → ‖Φ s‖ ≤ C / (1 + s.im ^ 2) := by
    intro s hs
    obtain ⟨h1, h2⟩ := hstrip s hs
    have hc := norm_natCast_cpow_neg_re_le_one hn (s := s) (by linarith)
    rw [hΦ, norm_mul]
    calc ‖xi s ^ 2 * R s‖ * ‖(n : ℂ) ^ (-s)‖ ≤ (C / (1 + s.im ^ 2)) * 1 :=
          mul_le_mul (hC s h1 h2) hc (norm_nonneg _) (le_trans (norm_nonneg _) (hC s h1 h2))
      _ = C / (1 + s.im ^ 2) := mul_one _
  have hshift := GaloisForLFunctions.HTGeometry.integral_vertical_line_shift_of_decay hd hb
  have hL : (∫ t : ℝ, xi (1 / 2 + t * I) ^ 2 * R (1 / 2 + t * I) * (n : ℂ) ^ (-(1 / 2 + t * I))) =
      ∫ t : ℝ, Φ (((1 / 2 : ℝ) : ℂ) + t * I) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    simp only [hΦ]; push_cast; ring_nf
  rw [hL, hshift]
  -- the series on `Re s = 3`
  set K : ℝ → ℂ := fun t => archXi (3 + t * I) ^ 2 * R (3 + t * I) with hK
  set F : ℕ → ℝ → ℂ := fun m t =>
    divisorCard m * (((m * n : ℕ) : ℂ) ^ (-((3 : ℂ) + t * I)) * K t) with hF
  have hser : ∀ t : ℝ, Φ (((3 : ℝ) : ℂ) + t * I) = ∑' m, F m t := by
    intro t
    have hre : 1 < ((3 : ℂ) + t * I).re := by simp
    simp only [hΦ, hF, hK]
    push_cast
    rw [xi_eq_archXi_mul_zeta hre, mul_pow, riemannZeta_sq_eq_tsum hre]
    rw [show archXi (3 + t * I) ^ 2 * (∑' m : ℕ, divisorCard m * (m : ℂ) ^ (-(3 + t * I))) *
        R (3 + t * I) * (n : ℂ) ^ (-(3 + t * I)) =
        (∑' m : ℕ, divisorCard m * (m : ℂ) ^ (-(3 + t * I))) *
          ((n : ℂ) ^ (-(3 + t * I)) * (archXi (3 + t * I) ^ 2 * R (3 + t * I))) by ring,
      ← tsum_mul_right]
    refine tsum_congr fun m => ?_
    rw [Complex.natCast_mul_natCast_cpow]
    ring
  have hKcont : Continuous K := by
    rw [continuous_iff_continuousAt]
    intro t
    have hre : (0 : ℝ) < ((3 : ℂ) + t * I).re := by simp
    have h3 : DifferentiableAt ℂ (fun s => archXi s ^ 2 * R s) ((3 : ℂ) + t * I) :=
      ((differentiableAt_archXi hre).pow 2).mul (hR _ (by simp; norm_num) (by simp))
    exact ContinuousAt.comp (g := fun s => archXi s ^ 2 * R s) h3.continuousAt
      (by fun_prop : ContinuousAt (fun t : ℝ => (3 : ℂ) + t * I) t)
  have hKint : Integrable K := by
    refine (integrable_inv_one_add_sq.const_mul C').mono' hKcont.aestronglyMeasurable
      (Filter.Eventually.of_forall fun t => ?_)
    simpa [hK, div_eq_mul_inv] using hC' t
  have hnorm_cpow : ∀ m : ℕ, ∀ t : ℝ, 1 ≤ m →
      ‖((m * n : ℕ) : ℂ) ^ (-((3 : ℂ) + t * I))‖ = ((m * n : ℕ) : ℝ) ^ (-(3 : ℝ)) := by
    intro m t hm
    have hpos : (0 : ℝ) < ((m * n : ℕ) : ℝ) := by
      have : 1 ≤ m * n := Nat.one_le_iff_ne_zero.mpr (by positivity)
      exact_mod_cast this
    rw [show (((m * n : ℕ) : ℂ)) = ((((m * n : ℕ) : ℝ)) : ℂ) by push_cast; rfl,
      Complex.norm_cpow_eq_rpow_re_of_pos hpos]
    simp
  have hFint : ∀ m : ℕ, Integrable (F m) := by
    intro m
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp [hF, divisorCard]
    have hc : Continuous fun t : ℝ => ((m * n : ℕ) : ℂ) ^ (-((3 : ℂ) + t * I)) := by
      have hb0 : ((m * n : ℕ) : ℂ) ≠ 0 := by
        exact_mod_cast (Nat.one_le_iff_ne_zero.mp (Nat.one_le_iff_ne_zero.mpr (by positivity)))
      exact Continuous.const_cpow (by fun_prop) (Or.inl hb0)
    have hbound : ∀ t, ‖F m t‖ ≤ ‖divisorCard m‖ * ((m * n : ℕ) : ℝ) ^ (-(3 : ℝ)) * ‖K t‖ := by
      intro t
      simp only [hF, norm_mul, hnorm_cpow m t hm]
      ring_nf; rfl
    refine ((hKint.norm.const_mul (‖divisorCard m‖ * ((m * n : ℕ) : ℝ) ^ (-(3 : ℝ))))).mono'
      ((continuous_const.mul (hc.mul hKcont)).aestronglyMeasurable)
      (Filter.Eventually.of_forall hbound)
  have hFnorm : ∀ m : ℕ, ∫ t, ‖F m t‖ =
      ‖divisorCard m‖ * ((m * n : ℕ) : ℝ) ^ (-(3 : ℝ)) * ∫ t, ‖K t‖ := by
    intro m
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp [hF, divisorCard]
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    simp only [hF, norm_mul, hnorm_cpow m t hm]
    ring
  have hFsum : Summable fun m => ∫ t, ‖F m t‖ := by
    simp_rw [hFnorm]
    refine Summable.mul_right _ ?_
    refine Summable.of_nonneg_of_le (fun m => by positivity) (fun m => ?_)
      ((Real.summable_nat_pow_inv.mpr (by norm_num : 1 < 2)))
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp [divisorCard]
    have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hd : ‖divisorCard m‖ ≤ m := by
      rw [divisorCard, Complex.norm_natCast]; exact_mod_cast Nat.card_divisors_le_self m
    have hmn : ((m * n : ℕ) : ℝ) ^ (-(3 : ℝ)) ≤ (m : ℝ) ^ (-(3 : ℝ)) := by
      push_cast
      exact Real.rpow_le_rpow_of_nonpos (by positivity) (by nlinarith) (by norm_num)
    calc ‖divisorCard m‖ * ((m * n : ℕ) : ℝ) ^ (-(3 : ℝ)) ≤ (m : ℝ) * (m : ℝ) ^ (-(3 : ℝ)) :=
          mul_le_mul hd hmn (by positivity) (by positivity)
      _ = ((m : ℝ) ^ 2)⁻¹ := by
          rw [Real.rpow_neg (by positivity), show ((m : ℝ) ^ (3 : ℝ)) = (m : ℝ) ^ (3 : ℕ) by
            norm_cast]
          field_simp
  rw [show (∫ t : ℝ, Φ (((3 : ℝ) : ℂ) + t * I)) = ∫ t : ℝ, ∑' m, F m t from
    integral_congr_ae (Filter.Eventually.of_forall hser),
    ← integral_tsum_of_summable_integral_norm hFint hFsum, ← tsum_mul_left]
  refine tsum_congr fun m => ?_
  have hI : (∫ y : ℝ, (((m * n : ℕ) : ℝ) : ℂ) ^ (-(((3 : ℝ) : ℂ) + y * I)) •
      (fun s => archXi s ^ 2 * R s) (((3 : ℝ) : ℂ) + y * I)) =
      ∫ t : ℝ, ((m * n : ℕ) : ℂ) ^ (-((3 : ℂ) + t * I)) * K t := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [hK, smul_eq_mul]
    push_cast
    ring_nf
  simp only [hF]
  rw [integral_const_mul, mellinInv, hI, Complex.real_smul]
  push_cast
  field_simp
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
  simp only [mul_comm I]

/-- The ζ-free kernel of an exact-null test: `Ψ_R = 𝓜^{−1}_3[G² R]`, `G = s(s−1)Γ_ℝ(s)/2`. -/
def certKernel (R : ℂ → ℂ) (x : ℝ) : ℂ := mellinInv 3 (fun s => archXi s ^ 2 * R s) x

theorem norm_certKernel_le (R : ℂ → ℂ) {x : ℝ} (hx : 0 < x) :
    ‖certKernel R x‖ ≤ (∫ t : ℝ, ‖archXi (3 + t * I) ^ 2 * R (3 + t * I)‖) / (2 * Real.pi) *
      x ^ (-(3 : ℝ)) := by
  rw [certKernel, mellinInv, norm_smul]
  have hpi : 0 < 2 * Real.pi := by positivity
  have h1 : ‖(1 / (2 * Real.pi) : ℝ)‖ = 1 / (2 * Real.pi) := by
    rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
  rw [h1]
  have h2 : ‖∫ y : ℝ, (x : ℂ) ^ (-((3 : ℝ) + y * I : ℂ)) • (archXi ((3 : ℝ) + y * I) ^ 2 *
      R ((3 : ℝ) + y * I))‖ ≤ ∫ y : ℝ, x ^ (-(3 : ℝ)) * ‖archXi (3 + y * I) ^ 2 * R (3 + y * I)‖ := by
    refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [norm_smul]
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hx]
    push_cast
    simp
  rw [integral_const_mul] at h2
  calc 1 / (2 * Real.pi) * ‖∫ y : ℝ, (x : ℂ) ^ (-((3 : ℝ) + y * I : ℂ)) •
        (archXi ((3 : ℝ) + y * I) ^ 2 * R ((3 : ℝ) + y * I))‖
      ≤ 1 / (2 * Real.pi) * (x ^ (-(3 : ℝ)) *
          ∫ y : ℝ, ‖archXi (3 + y * I) ^ 2 * R (3 + y * I)‖) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = _ := by ring

/-- `n^{−it} = n^{1/2} · n^{−(1/2+it)}`, which turns the Fourier value at `log n` into the
line integral of `integral_xi_sq_mul_cpow_eq_tsum`. -/
theorem integral_xi_sq_logNode (R : ℂ → ℂ) {n : ℕ} (hn : 1 ≤ n) :
    ∫ t : ℝ, xi (1 / 2 + t * I) ^ 2 * R (1 / 2 + t * I) * (n : ℂ) ^ (-((t : ℂ) * I)) =
      (n : ℂ) ^ (1 / 2 : ℂ) *
        ∫ t : ℝ, xi (1 / 2 + t * I) ^ 2 * R (1 / 2 + t * I) * (n : ℂ) ^ (-(1 / 2 + t * I)) := by
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  have : (n : ℂ) ^ (-((t : ℂ) * I)) = (n : ℂ) ^ (1 / 2 : ℂ) * (n : ℂ) ^ (-(1 / 2 + t * I)) := by
    rw [← Complex.cpow_add _ _ hn0]; ring_nf
  simp only [this]; ring

/-- **Exact-null blindness is a ζ-free condition.** Under the regularity hypotheses of
`integral_xi_sq_mul_cpow_eq_tsum`, the test `g` with `ĝ(t) = Ξ(t)² R(½+it)` vanishes at every
`log n`, `n ≥ 2`, if and only if the ζ-free kernel `Ψ_R = 𝓜^{−1}[G²R]` vanishes at every integer
`n ≥ 2`. The divisor function enters through `ζ² = Σ d(m) m^{−s}` and leaves through the
Dirichlet inverse `μ ⋆ μ`. -/
theorem logNode_blind_iff_certKernel_vanishes (R : ℂ → ℂ)
    (hR : ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 3 → DifferentiableAt ℂ R s)
    {C : ℝ} (hC : ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 3 → ‖xi s ^ 2 * R s‖ ≤ C / (1 + s.im ^ 2))
    {C' : ℝ} (hC' : ∀ t : ℝ, ‖archXi (3 + t * I) ^ 2 * R (3 + t * I)‖ ≤ C' / (1 + t ^ 2)) :
    (∀ n : ℕ, 2 ≤ n →
      ∫ t : ℝ, xi (1 / 2 + t * I) ^ 2 * R (1 / 2 + t * I) * (n : ℂ) ^ (-((t : ℂ) * I)) = 0) ↔
    (∀ n : ℕ, 2 ≤ n → certKernel R n = 0) := by
  have hval : ∀ n : ℕ, 1 ≤ n →
      ∫ t : ℝ, xi (1 / 2 + t * I) ^ 2 * R (1 / 2 + t * I) * (n : ℂ) ^ (-((t : ℂ) * I)) =
        (n : ℂ) ^ (1 / 2 : ℂ) * (2 * Real.pi *
          ∑' m : ℕ, divisorCard m * certKernel R ((m * n : ℕ) : ℝ)) := by
    intro n hn
    rw [integral_xi_sq_logNode R hn, integral_xi_sq_mul_cpow_eq_tsum R hR hC hC' hn]
    rfl
  constructor
  · intro hblind
    set K := ∫ t : ℝ, ‖archXi (3 + t * I) ^ 2 * R (3 + t * I)‖
    refine eq_zero_of_divisorDilation_eq_zero (Ψ := fun N : ℕ => certKernel R N)
      (C := K / (2 * Real.pi)) (fun N hN => ?_) (fun j hj => ?_)
    · have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
      have := norm_certKernel_le R hN0
      rw [Real.rpow_neg hN0.le, show ((N : ℝ) ^ (3 : ℝ)) = (N : ℝ) ^ (3 : ℕ) by norm_cast,
        ← div_eq_mul_inv] at this
      exact this
    · have h := hval j (by omega)
      rw [hblind j hj] at h
      have hj0 : (j : ℂ) ^ (1 / 2 : ℂ) ≠ 0 := by
        rw [Ne, Complex.cpow_eq_zero_iff]; push Not
        intro h0; exact absurd h0 (by exact_mod_cast (by omega : j ≠ 0))
      have hpi : (2 * Real.pi : ℂ) ≠ 0 := by
        exact_mod_cast (by positivity : (2 * Real.pi : ℝ) ≠ 0)
      have := (mul_eq_zero.mp h.symm).resolve_left hj0
      have := (mul_eq_zero.mp this).resolve_left hpi
      simpa [Nat.cast_mul] using this
  · intro hvan n hn
    rw [hval n (by omega)]
    have : (∑' m : ℕ, divisorCard m * certKernel R ((m * n : ℕ) : ℝ)) = 0 := by
      refine (tsum_congr fun m => ?_).trans tsum_zero
      rcases Nat.eq_zero_or_pos m with rfl | hm
      · simp [divisorCard_zero]
      · have hmn : 2 ≤ m * n := le_trans hn (Nat.le_mul_of_pos_left n hm)
        rw [hvan _ hmn, mul_zero]
    rw [this, mul_zero, mul_zero]

/-- Under blindness the central value is the kernel at `1`: `∫ Ξ² R = 2π Ψ_R(1)`. -/
theorem integral_xi_sq_eq_certKernel_one (R : ℂ → ℂ)
    (hR : ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 3 → DifferentiableAt ℂ R s)
    {C : ℝ} (hC : ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 3 → ‖xi s ^ 2 * R s‖ ≤ C / (1 + s.im ^ 2))
    {C' : ℝ} (hC' : ∀ t : ℝ, ‖archXi (3 + t * I) ^ 2 * R (3 + t * I)‖ ≤ C' / (1 + t ^ 2))
    (hvan : ∀ n : ℕ, 2 ≤ n → certKernel R n = 0) :
    ∫ t : ℝ, xi (1 / 2 + t * I) ^ 2 * R (1 / 2 + t * I) =
      2 * Real.pi * certKernel R 1 := by
  have h := integral_xi_sq_logNode R (n := 1) le_rfl
  rw [integral_xi_sq_mul_cpow_eq_tsum R hR hC hC' le_rfl] at h
  simp only [Nat.cast_one, Complex.one_cpow, mul_one, one_mul] at h
  rw [h, tsum_eq_single 1 (fun m hm => ?_)]
  · simp [divisorCard, certKernel]
  · rcases Nat.eq_zero_or_pos m with rfl | hm0
    · simp [divisorCard_zero]
    · have : 2 ≤ m := by omega
      have h2 := hvan m this
      rw [certKernel] at h2
      rw [h2, mul_zero]

end RHTower.ExactNullDivisorTransfer
