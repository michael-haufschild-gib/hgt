import GaloisForLFunctions.RHTower.FermiNymanWitnessDyadicDefect
import GaloisForLFunctions.RHTower.ZetaInverseWideHorizontal
import GaloisForLFunctions.RHTower.Deninger.DeningerZetaLowerBound
import GaloisForLFunctions.HTGeometry.PolynomialAntiderivative
import GaloisForLFunctions.HTGeometry.FourierUniquenessL1

/-!
# Witnesses of Mellin exponent zero are dyadically self-similar

Let `w` be continuous on `(0,1]`, with `∫_0^1 φ_b w = 0` for every `b ≥ 1`
(`φ_b(t) = {1/(bt)} − 2{1/(2bt)}`), and with `∫_0^1 t^{x−1}|w(t)| dt < ∞` for every `x > 0`.
Then `w(t/2) = w(t)` on `(0,1]`.

The class is sharp: the zero witness `t^{ρ̄−1}` of a zeta zero `ρ` has Mellin exponent `1 − Re ρ > 0`,
and rigidity for all witnesses of exponent `a > 0` would exclude every zero with `Re ρ > 1 − a`.

Proof.  The transform `U(z) = 2^z (V(z) − ∫_{1/2}^1 t^{z−1} w)` of `FermiNymanWitnessDyadicDefect` is
entire because `Ξ(s) = (s − 1) ζ(s)` has no zero on `Re s ≥ 1`.  It is bounded on `Re z ≥ 1/2`, and
polynomially bounded on `Re z ≤ −1` (`|ζ| ≥ 1/4` on `Re s ≥ 2`).  In the strip `−1 ≤ Re z ≤ 1` the
maximum modulus principle on the rectangles between consecutive heights `T_k` of Titchmarsh IX.7
(`|ζ(σ ± iT_k)|^{−1} ≤ C T_k^A` on `−2 ≤ σ ≤ 2`, `T_{k+1} ≤ T_k + 3`) bounds `U` polynomially.  By
Liouville `U` is a polynomial, and it tends to `0` along the integers, so `U ≡ 0`.  Then
`∫_0^{1/2} t^{z−1}(w(t) − w(2t)) dt = 0` on `Re z > 0`, and Fourier uniqueness gives `w(2t) = w(t)`.
-/

open Complex MeasureTheory Set Filter Topology
open scoped FourierTransform

noncomputable section

namespace RHTower

variable {w : ℝ → ℂ}

/-! ## Maximum modulus on a rectangle -/

/-- The maximum modulus principle on a closed rectangle. -/
theorem norm_le_of_forall_rectangle_boundary {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {x₀ x₁ y₀ y₁ : ℝ} (hx : x₀ < x₁) (hy : y₀ < y₁) {C : ℝ}
    (hC : ∀ u : ℂ, x₀ ≤ u.re → u.re ≤ x₁ → y₀ ≤ u.im → u.im ≤ y₁ →
      (u.re = x₀ ∨ u.re = x₁ ∨ u.im = y₀ ∨ u.im = y₁) → ‖f u‖ ≤ C)
    {z : ℂ} (h1 : x₀ ≤ z.re) (h2 : z.re ≤ x₁) (h3 : y₀ ≤ z.im) (h4 : z.im ≤ y₁) : ‖f z‖ ≤ C := by
  have hb : Bornology.IsBounded (Ioo x₀ x₁ ×ℂ Ioo y₀ y₁) :=
    (Metric.isBounded_Ioo x₀ x₁).reProdIm (Metric.isBounded_Ioo y₀ y₁)
  refine Complex.norm_le_of_forall_mem_frontier_norm_le hb hf.diffContOnCl (fun u hu => ?_) ?_
  · rw [Complex.frontier_reProdIm, closure_Ioo hx.ne, closure_Ioo hy.ne, frontier_Ioo hx,
      frontier_Ioo hy] at hu
    rcases hu with ⟨hre, him⟩ | ⟨hre, him⟩
    · have hre' : u.re ∈ Icc x₀ x₁ := hre
      have him' : u.im ∈ ({y₀, y₁} : Set ℝ) := him
      rcases him' with h | h
      · exact hC u hre'.1 hre'.2 (le_of_eq h.symm) (by rw [h]; exact hy.le) (Or.inr (Or.inr (Or.inl h)))
      · have h' : u.im = y₁ := h
        exact hC u hre'.1 hre'.2 (by rw [h']; exact hy.le) (le_of_eq h') (Or.inr (Or.inr (Or.inr h')))
    · have hre' : u.re ∈ ({x₀, x₁} : Set ℝ) := hre
      have him' : u.im ∈ Icc y₀ y₁ := him
      rcases hre' with h | h
      · exact hC u (le_of_eq h.symm) (by rw [h]; exact hx.le) him'.1 him'.2 (Or.inl h)
      · have h' : u.re = x₁ := h
        exact hC u (by rw [h']; exact hx.le) (le_of_eq h') him'.1 him'.2 (Or.inr (Or.inl h'))
  · rw [Complex.closure_reProdIm, closure_Ioo hx.ne, closure_Ioo hy.ne]
    exact ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩

/-! ## Good heights on both sides of the real axis -/

/-- Titchmarsh IX.7 at heights `±T_k`. -/
theorem exists_goodHeights :
    ∃ T : ℕ → ℝ, StrictMono T ∧ Tendsto T atTop atTop ∧ (∀ k, 1 ≤ T k) ∧
      (∀ k, T (k + 1) ≤ T k + 3) ∧ ∃ C A : ℝ, ∃ k₀ : ℕ, 0 < C ∧ 0 < A ∧
        ∀ k, k₀ ≤ k → ∀ s : ℂ, -1 ≤ s.re → s.re ≤ 2 → |s.im| = T k →
          riemannZeta s ≠ 0 ∧ ‖(riemannZeta s)⁻¹‖ ≤ C * T k ^ A := by
  obtain ⟨T, hmono, htend, hT1, hstep, hne, hbd⟩ := exists_seq_zeta_inv_horizontal
  obtain ⟨C, A, k₀, hC, hA, hbound⟩ := hbd 2 le_rfl
  refine ⟨T, hmono, htend, hT1, hstep, C, A, k₀, hC, hA, fun k hk s hs1 hs2 him => ?_⟩
  have hpos : s = (s.re : ℂ) + ((T k : ℝ) : ℂ) * I ∨
      s = (starRingEnd ℂ) ((s.re : ℂ) + ((T k : ℝ) : ℂ) * I) := by
    rcases abs_eq (le_trans zero_le_one (hT1 k)) |>.1 him with h | h
    · left; apply Complex.ext <;> simp [h]
    · right; apply Complex.ext <;> simp [h]
  rcases hpos with h | h
  · rw [h]
    exact ⟨hne k s.re hs1 hs2, hbound k hk s.re (by linarith) hs2⟩
  · rw [h, riemannZeta_conj]
    refine ⟨(map_ne_zero _).2 (hne k s.re hs1 hs2), ?_⟩
    rw [← map_inv₀, Complex.norm_conj]
    exact hbound k hk s.re (by linarith) hs2

/-! ## Polynomial growth of `U` -/

theorem zetaEntire_ne_zero_of_re_le_zero {z : ℂ} (hz : z.re ≤ 0) : zetaEntire (1 - z) ≠ 0 :=
  Sieve.zetaEntire_ne_zero_of_one_le_re (by simp; linarith)

theorem IsMellinFermiWitness.differentiable_dyadicDefectTransform_zero
    (hw : IsMellinFermiWitness w 0) : Differentiable ℂ (dyadicDefectTransform w 0) :=
  hw.differentiable_dyadicDefectTransform fun _ hz => zetaEntire_ne_zero_of_re_le_zero hz

theorem norm_one_sub_le_of_re_im {z : ℂ} {T : ℝ} (hre : |z.re| ≤ 1) (him : |z.im| ≤ T) :
    ‖1 - z‖ ≤ 2 + T := by
  calc ‖1 - z‖ ≤ ‖(1 : ℂ)‖ + ‖z‖ := norm_sub_le _ _
    _ ≤ 1 + (|z.re| + |z.im|) := by rw [norm_one]; linarith [Complex.norm_le_abs_re_add_abs_im z]
    _ ≤ 2 + T := by linarith

theorem exists_index_between {T : ℕ → ℝ} (hmono : StrictMono T) (htend : Tendsto T atTop atTop)
    {k₀ : ℕ} {y : ℝ} (hy : T k₀ ≤ y) : ∃ k, k₀ ≤ k ∧ T k ≤ y ∧ y ≤ T (k + 1) := by
  classical
  have hex : ∃ n, y < T n := (htend.eventually_gt_atTop y).exists
  have hspec : y < T (Nat.find hex) := Nat.find_spec hex
  have hk₀ : k₀ < Nat.find hex := by
    by_contra h
    have := hmono.monotone (not_lt.1 h)
    linarith
  refine ⟨Nat.find hex - 1, by omega, ?_, ?_⟩
  · exact not_lt.1 (Nat.find_min hex (show Nat.find hex - 1 < Nat.find hex by omega))
  · rw [show Nat.find hex - 1 + 1 = Nat.find hex by omega]; exact hspec.le

/-- **Polynomial growth from boundary data.**  An entire function bounded on `Re z ≥ x₁` and bounded
by `‖1 − z‖ · c · ‖ζ(1 − z)⁻¹‖ + K_L` on `Re z ≤ x₁` wherever `ζ(1 − z) ≠ 0` has polynomial growth:
on the rectangles `[−1, 1] × ±[T_k, T_{k+1}]` between consecutive heights of Titchmarsh IX.7 the
maximum modulus principle applies, and the rest is a compact set or a half-plane. -/
theorem exists_polyGrowth_of_zetaInv_bounds {f : ℂ → ℂ} (hf : Differentiable ℂ f) {x₁ KR KL c : ℝ}
    (hx₁ : -1 < x₁) (hx₁' : x₁ < 1) (hKR : 0 ≤ KR) (hKL : 0 ≤ KL) (hc : 0 ≤ c)
    (hright : ∀ z : ℂ, x₁ ≤ z.re → ‖f z‖ ≤ KR)
    (hleft : ∀ z : ℂ, z.re ≤ x₁ → z ≠ 0 → riemannZeta (1 - z) ≠ 0 →
      ‖f z‖ ≤ ‖1 - z‖ * c * ‖(riemannZeta (1 - z))⁻¹‖ + KL) :
    ∃ K : ℝ, ∃ N : ℕ, ∀ z : ℂ, ‖f z‖ ≤ K * (1 + ‖z‖) ^ N := by
  obtain ⟨T, hmono, htend, hT1, hstep, C, A, k₀, hC, hA, hgood⟩ := exists_goodHeights
  -- the far left
  have hfarleft : ∀ z : ℂ, z.re ≤ -1 → ‖f z‖ ≤ 4 * c * ‖1 - z‖ + KL := by
    intro z hz
    have hz0 : z ≠ 0 := by intro h; rw [h, Complex.zero_re] at hz; linarith
    have hζ : (1 : ℝ) / 4 ≤ ‖riemannZeta (1 - z)‖ :=
      norm_riemannZeta_ge_of_two_le_re (by simp; linarith)
    have hne : riemannZeta (1 - z) ≠ 0 := by
      intro h; rw [h, norm_zero] at hζ; linarith
    have h := hleft z (by linarith) hz0 hne
    have hinv : ‖(riemannZeta (1 - z))⁻¹‖ ≤ 4 := by
      rw [norm_inv, inv_le_comm₀ (by linarith) (by norm_num)]
      linarith
    calc ‖f z‖ ≤ ‖1 - z‖ * c * ‖(riemannZeta (1 - z))⁻¹‖ + KL := h
      _ ≤ ‖1 - z‖ * c * 4 + KL := by gcongr
      _ = 4 * c * ‖1 - z‖ + KL := by ring
  -- the boundary of the rectangles between consecutive good heights
  have hbdry : ∀ k : ℕ, k₀ ≤ k → ∀ u : ℂ, -1 ≤ u.re → u.re ≤ 1 → |u.im| ≤ T (k + 1) →
      (u.re = -1 ∨ u.re = 1 ∨ |u.im| = T k ∨ |u.im| = T (k + 1)) →
      ‖f u‖ ≤ (2 + T (k + 1)) * c * (C * T (k + 1) ^ A) + 4 * c * (2 + T (k + 1)) + KL + KR := by
    intro k hk u hu1 hu2 hu3 hcase
    have hTk1 : 1 ≤ T (k + 1) := hT1 (k + 1)
    have hre_abs : |u.re| ≤ 1 := abs_le.2 ⟨hu1, hu2⟩
    have h1u : ‖1 - u‖ ≤ 2 + T (k + 1) := norm_one_sub_le_of_re_im hre_abs hu3
    have t1 : 0 ≤ (2 + T (k + 1)) * c * (C * T (k + 1) ^ A) := by
      have : 0 ≤ T (k + 1) ^ A := Real.rpow_nonneg (by linarith) _
      positivity
    have t2 : 0 ≤ 4 * c * (2 + T (k + 1)) := by positivity
    by_cases hhalf : x₁ ≤ u.re
    · have := hright u hhalf; linarith
    rw [not_le] at hhalf
    by_cases hm1 : u.re = -1
    · have := hfarleft u (le_of_eq hm1)
      have h4 : 4 * c * ‖1 - u‖ ≤ 4 * c * (2 + T (k + 1)) :=
        mul_le_mul_of_nonneg_left h1u (by positivity)
      linarith
    have hj : ∃ j, k₀ ≤ j ∧ T j ≤ T (k + 1) ∧ |u.im| = T j := by
      rcases hcase with h | h | h | h
      · exact absurd h hm1
      · linarith
      · exact ⟨k, hk, (hmono (Nat.lt_succ_self k)).le, h⟩
      · exact ⟨k + 1, by omega, le_rfl, h⟩
    obtain ⟨j, hj0, hjle, hjim⟩ := hj
    have hs1 : -1 ≤ (1 - u).re := by simp; linarith
    have hs2 : (1 - u).re ≤ 2 := by simp; linarith
    have hsim : |(1 - u).im| = T j := by simp [abs_neg, hjim]
    obtain ⟨hne, hinv⟩ := hgood j hj0 (1 - u) hs1 hs2 hsim
    have hu0 : u ≠ 0 := by
      intro h; rw [h, Complex.zero_im, abs_zero] at hjim; linarith [hT1 j]
    have hl := hleft u hhalf.le hu0 hne
    have hpow : T j ^ A ≤ T (k + 1) ^ A :=
      Real.rpow_le_rpow (by linarith [hT1 j]) hjle hA.le
    have hinv' : ‖(riemannZeta (1 - u))⁻¹‖ ≤ C * T (k + 1) ^ A :=
      hinv.trans (mul_le_mul_of_nonneg_left hpow hC.le)
    have hprod : ‖1 - u‖ * c * ‖(riemannZeta (1 - u))⁻¹‖ ≤
        (2 + T (k + 1)) * c * (C * T (k + 1) ^ A) :=
      mul_le_mul (mul_le_mul_of_nonneg_right h1u hc) hinv' (norm_nonneg _) (by positivity)
    linarith
  -- the strip bound at every height beyond `T k₀`
  have hstrip : ∀ z : ℂ, -1 ≤ z.re → z.re ≤ 1 → T k₀ ≤ |z.im| →
      ∃ k, k₀ ≤ k ∧ T (k + 1) ≤ |z.im| + 3 ∧ ‖f z‖ ≤
        (2 + T (k + 1)) * c * (C * T (k + 1) ^ A) + 4 * c * (2 + T (k + 1)) + KL + KR := by
    intro z hz1 hz2 hzim
    obtain ⟨k, hk, hlow, hup⟩ := exists_index_between hmono htend hzim
    refine ⟨k, hk, by linarith [hstep k], ?_⟩
    have hTk : 0 < T k := by linarith [hT1 k]
    rcases le_or_gt 0 z.im with hpos | hneg
    · rw [abs_of_nonneg hpos] at hlow hup
      refine norm_le_of_forall_rectangle_boundary hf (by norm_num : (-1 : ℝ) < 1)
        (hmono (Nat.lt_succ_self k)) (fun u hu1 hu2 hu3 hu4 hcase => ?_) hz1 hz2 hlow hup
      have huim : |u.im| = u.im := abs_of_nonneg (by linarith)
      refine hbdry k hk u hu1 hu2 (by rw [huim]; exact hu4) ?_
      rcases hcase with h | h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl (by rw [huim, h])))
      · exact Or.inr (Or.inr (Or.inr (by rw [huim, h])))
    · rw [abs_of_neg hneg] at hlow hup
      refine norm_le_of_forall_rectangle_boundary hf (by norm_num : (-1 : ℝ) < 1)
        (neg_lt_neg (hmono (Nat.lt_succ_self k))) (fun u hu1 hu2 hu3 hu4 hcase => ?_) hz1 hz2
        (by linarith) (by linarith)
      have huim : |u.im| = -u.im := abs_of_neg (by linarith)
      refine hbdry k hk u hu1 hu2 (by rw [huim]; linarith) ?_
      rcases hcase with h | h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inr (by rw [huim, h, neg_neg])))
      · exact Or.inr (Or.inr (Or.inl (by rw [huim, h, neg_neg])))
  -- the compact part
  have hcpt : IsCompact (Icc (-1 : ℝ) 1 ×ℂ Icc (-T k₀) (T k₀)) :=
    isCompact_Icc.reProdIm isCompact_Icc
  obtain ⟨K₀, hK₀⟩ := hcpt.exists_bound_of_continuousOn hf.continuous.continuousOn
  -- assembly
  set N₀ : ℕ := ⌈A⌉₊ with hN₀
  have hAN : A ≤ (N₀ : ℝ) := Nat.le_ceil A
  refine ⟨|K₀| + KR + (4 * c + KL) + (5 * c * C * 3 ^ N₀ + 20 * c + KL + KR), N₀ + 1,
    fun z => ?_⟩
  set R : ℝ := 1 + ‖z‖ with hR
  have hR1 : 1 ≤ R := by rw [hR]; linarith [norm_nonneg z]
  have hRpow : ∀ j ≤ N₀ + 1, R ^ j ≤ R ^ (N₀ + 1) := fun j hj => pow_le_pow_right₀ hR1 hj
  have hRN : 1 ≤ R ^ (N₀ + 1) := one_le_pow₀ hR1
  have c1 : 0 ≤ |K₀| := abs_nonneg _
  have c2 : 0 ≤ 4 * c + KL := by positivity
  have c3 : 0 ≤ 5 * c * C * 3 ^ N₀ + 20 * c + KL + KR := by positivity
  have hfin : ∀ b : ℝ, 0 ≤ b →
      b ≤ |K₀| + KR + (4 * c + KL) + (5 * c * C * 3 ^ N₀ + 20 * c + KL + KR) →
      ‖f z‖ ≤ b * R ^ (N₀ + 1) →
      ‖f z‖ ≤ (|K₀| + KR + (4 * c + KL) + (5 * c * C * 3 ^ N₀ + 20 * c + KL + KR)) *
          R ^ (N₀ + 1) := fun b hb hbK h =>
    h.trans (mul_le_mul_of_nonneg_right hbK (by positivity))
  have h1z : ‖1 - z‖ ≤ R := by
    rw [hR]; exact (norm_sub_le _ _).trans (by rw [norm_one])
  by_cases hx1 : x₁ ≤ z.re
  · refine hfin KR hKR (by linarith) ?_
    exact (hright z hx1).trans (le_mul_of_one_le_right hKR hRN)
  rw [not_le] at hx1
  by_cases hxm : z.re ≤ -1
  · refine hfin (4 * c + KL) c2 (by linarith) ?_
    calc ‖f z‖ ≤ 4 * c * ‖1 - z‖ + KL := hfarleft z hxm
      _ ≤ 4 * c * R + KL * R := by
          have := mul_le_mul_of_nonneg_left h1z (by positivity : (0 : ℝ) ≤ 4 * c)
          nlinarith
      _ = (4 * c + KL) * R ^ 1 := by ring
      _ ≤ (4 * c + KL) * R ^ (N₀ + 1) :=
          mul_le_mul_of_nonneg_left (hRpow 1 (by omega)) c2
  rw [not_le] at hxm
  by_cases hy : |z.im| ≤ T k₀
  · refine hfin |K₀| c1 (by linarith) ?_
    have hmem : z ∈ Icc (-1 : ℝ) 1 ×ℂ Icc (-T k₀) (T k₀) :=
      ⟨⟨hxm.le, by linarith⟩, abs_le.1 hy⟩
    exact ((hK₀ z hmem).trans (le_abs_self _)).trans (le_mul_of_one_le_right c1 hRN)
  rw [not_le] at hy
  obtain ⟨k, _, hTk, hbd⟩ := hstrip z hxm.le (by linarith) hy.le
  refine hfin _ c3 (by linarith) (hbd.trans ?_)
  have hS : T (k + 1) ≤ 3 * R := by
    have := Complex.abs_im_le_norm z
    rw [hR]; linarith
  have hS0 : 0 ≤ T (k + 1) := by linarith [hT1 (k + 1)]
  have h3R : 1 ≤ 3 * R := by linarith
  have hApow : T (k + 1) ^ A ≤ 3 ^ N₀ * R ^ N₀ := by
    calc T (k + 1) ^ A ≤ (3 * R) ^ A := Real.rpow_le_rpow hS0 hS hA.le
      _ ≤ (3 * R) ^ (N₀ : ℝ) := Real.rpow_le_rpow_of_exponent_le h3R hAN
      _ = 3 ^ N₀ * R ^ N₀ := by rw [Real.rpow_natCast, mul_pow]
  have h2S : 2 + T (k + 1) ≤ 5 * R := by linarith
  have hpowA : 0 ≤ T (k + 1) ^ A := Real.rpow_nonneg hS0 _
  calc (2 + T (k + 1)) * c * (C * T (k + 1) ^ A) + 4 * c * (2 + T (k + 1)) + KL + KR
      ≤ (5 * R) * c * (C * (3 ^ N₀ * R ^ N₀)) + 4 * c * (5 * R) + KL + KR := by
        gcongr
    _ = 5 * c * C * 3 ^ N₀ * R ^ (N₀ + 1) + 20 * c * R ^ 1 + KL + KR := by ring
    _ ≤ 5 * c * C * 3 ^ N₀ * R ^ (N₀ + 1) + 20 * c * R ^ (N₀ + 1) + KL * R ^ (N₀ + 1) +
          KR * R ^ (N₀ + 1) := by
        have e1 := mul_le_mul_of_nonneg_left (hRpow 1 (by omega)) (by positivity : (0:ℝ) ≤ 20 * c)
        have e2 := le_mul_of_one_le_right hKL hRN
        have e3 := le_mul_of_one_le_right hKR hRN
        linarith
    _ = (5 * c * C * 3 ^ N₀ + 20 * c + KL + KR) * R ^ (N₀ + 1) := by ring

theorem upperDefectBound_nonneg (w : ℝ → ℂ) : 0 ≤ upperDefectBound w :=
  mul_nonneg (by norm_num) (setIntegral_nonneg measurableSet_Ioc fun _ _ => norm_nonneg _)

theorem rightDefectBound_nonneg (w : ℝ → ℂ) (x₁ : ℝ) : 0 ≤ rightDefectBound w x₁ := by
  refine mul_nonneg (by norm_num) (setIntegral_nonneg measurableSet_Ioc fun t ht => ?_)
  exact mul_nonneg (Real.rpow_nonneg ht.1.le _) (by positivity)

/-- **`U` has polynomial growth** for a witness of Mellin exponent `0`. -/
theorem IsMellinFermiWitness.exists_growth (hw : IsMellinFermiWitness w 0) :
    ∃ K : ℝ, ∃ N : ℕ, ∀ z : ℂ, ‖dyadicDefectTransform w 0 z‖ ≤ K * (1 + ‖z‖) ^ N := by
  refine exists_polyGrowth_of_zetaInv_bounds hw.differentiable_dyadicDefectTransform_zero
    (x₁ := 1 / 2) (c := 6 * witnessMajorant w 1) (by norm_num) (by norm_num)
    (rightDefectBound_nonneg w _)
    (upperDefectBound_nonneg w) (by have := witnessMajorant_nonneg w 1; positivity)
    (fun z hz => hw.norm_dyadicDefectTransform_le_right (by norm_num) (by norm_num) hz)
    (fun z hz hz0 hζ => ?_)
  have h := hw.norm_dyadicDefectTransform_le_left (by linarith) hz0 (fun _ => hζ)
  have hm := witnessMajorant_nonneg w 1
  have h3 : 3 * witnessMajorant w 1 / (1 - z.re) ≤ 6 * witnessMajorant w 1 := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  rw [one_div, ← norm_inv] at h
  refine h.trans (add_le_add ?_ le_rfl)
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h3 (norm_nonneg _)) (norm_nonneg _)

/-! ## `U ≡ 0` -/

/-- **Liouville along the integers.**  An entire function of polynomial growth tending to zero
along `n + 1` vanishes identically. -/
theorem eq_zero_of_polyGrowth_of_tendsto_nat {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    (hK : ∃ K : ℝ, ∃ N : ℕ, ∀ z : ℂ, ‖F z‖ ≤ K * (1 + ‖z‖) ^ N)
    (hlim0 : Tendsto (fun n : ℕ => F ((n : ℂ) + 1)) atTop (𝓝 0)) (z : ℂ) : F z = 0 := by
  obtain ⟨K, N, hK⟩ := hK
  obtain ⟨p, hp⟩ := GaloisForLFunctions.HTGeometry.exists_polynomial_of_polynomial_growth hF hK
  have hlim : Tendsto (fun n : ℕ => p.eval ((n : ℂ) + 1)) atTop (𝓝 0) := by
    simp_rw [hp] at hlim0
    exact hlim0
  have hdeg : p.degree ≤ 0 := by
    by_contra hdeg
    rw [not_le] at hdeg
    have hnorm : Tendsto (fun n : ℕ => ‖((n : ℂ) + 1)‖) atTop atTop := by
      have h1 : Tendsto (fun n : ℕ => ((n : ℝ) + 1)) atTop atTop :=
        tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
      refine h1.congr (fun n => ?_)
      rw [show ((n : ℂ) + 1) = (((n : ℝ) + 1 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have ht := p.tendsto_norm_atTop hdeg hnorm
    have h0 := (continuous_norm.tendsto 0).comp hlim
    rw [norm_zero] at h0
    exact not_tendsto_nhds_of_tendsto_atTop ht 0 h0
  have hpC := Polynomial.eq_C_of_degree_le_zero hdeg
  have hc : p.coeff 0 = 0 := by
    rw [hpC] at hlim
    simp only [Polynomial.eval_C] at hlim
    exact tendsto_nhds_unique tendsto_const_nhds hlim
  rw [hp, hpC, Polynomial.eval_C, hc]

/-- **The transform vanishes identically.** -/
theorem IsMellinFermiWitness.dyadicDefectTransform_eq_zero (hw : IsMellinFermiWitness w 0)
    (z : ℂ) : dyadicDefectTransform w 0 z = 0 :=
  eq_zero_of_polyGrowth_of_tendsto_nat hw.differentiable_dyadicDefectTransform_zero
    hw.exists_growth hw.tendsto_dyadicDefectTransform_nat z

/-! ## Fourier uniqueness -/

/-- The lower dyadic defect `w(t) − w(2t)` on `(0, 1/2]`, extended by zero. -/
def lowerDefect (w : ℝ → ℂ) : ℝ → ℂ := (Ioc (0 : ℝ) (1 / 2)).indicator (fun t => w t - w (2 * t))

theorem IsMellinFermiWitness.mellin_lowerDefect (hw : IsMellinFermiWitness w 0) {z : ℂ}
    (hz : 0 < z.re) : mellin (lowerDefect w) z = 0 := by
  have h := hw.dyadicDefectTransform_eq_zero z
  rw [hw.dyadicDefectTransform_eq_of_lt_re hz] at h
  have h2 : (2 : ℂ) ^ z ≠ 0 := by
    rw [Complex.cpow_def_of_ne_zero (by norm_num)]; exact Complex.exp_ne_zero _
  unfold lowerDefect
  rw [mellin_indicator_eq_setIntegral le_rfl]
  exact (mul_eq_zero.1 h).resolve_left h2

theorem IsMellinFermiWitness.integrable_lowerDefect {a : ℝ} (hw : IsMellinFermiWitness w a) :
    Integrable (lowerDefect w) := by
  have h1 : IntegrableOn (fun t : ℝ => (t : ℂ) ^ ((1 : ℂ) - 1) * w t) (Ioc 0 (1 / 2)) :=
    (hw.integrableOn_cpow_mul (z := 1) (by simpa using hw.lt_one)).mono_set
      (Ioc_subset_Ioc_right (by norm_num))
  have h2 := hw.integrableOn_cpow_mul_comp_two (z := 1) (by simpa using hw.lt_one)
  have h3 : IntegrableOn (fun t : ℝ => w t - w (2 * t)) (Ioc 0 (1 / 2)) := by
    refine (h1.sub h2).congr_fun (fun t ht => ?_) measurableSet_Ioc
    simp only [sub_self, Complex.cpow_zero, one_mul, Pi.sub_apply]
  exact h3.integrable_indicator measurableSet_Ioc

theorem range_exp_neg : Set.range (fun u : ℝ => Real.exp (-u)) = Ioi 0 := by
  ext y
  constructor
  · rintro ⟨u, rfl⟩; exact Real.exp_pos _
  · intro hy
    refine ⟨-Real.log y, ?_⟩
    show Real.exp (-(-Real.log y)) = y
    rw [neg_neg, Real.exp_log hy]

/-- **Fourier uniqueness for the lower defect.**  If the Mellin transform of the lower defect
vanishes on `Re z = 1`, then `w(2t) = w(t)` on `(0, 1/2)`. -/
theorem lowerDefect_eq_zero_of_mellin (hc : ContinuousOn w (Ioc 0 1))
    (hint : Integrable (lowerDefect w))
    (hmel : ∀ z : ℂ, z.re = 1 → mellin (lowerDefect w) z = 0)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) (1 / 2)) : w t - w (2 * t) = 0 := by
  set h : ℝ → ℂ := fun u => Real.exp (-1 * u) • lowerDefect w (Real.exp (-u)) with hh
  have hF : ∀ ξ : ℝ, 𝓕 h ξ = 0 := by
    intro ξ
    have := hmel (1 + ((2 * Real.pi * ξ : ℝ) : ℂ) * I) (by simp)
    rw [mellin_eq_fourier] at this
    have hre : (1 + ((2 * Real.pi * ξ : ℝ) : ℂ) * I).re = 1 := by simp
    have him : (1 + ((2 * Real.pi * ξ : ℝ) : ℂ) * I).im / (2 * Real.pi) = ξ := by
      simp only [Complex.add_im, Complex.one_im, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_one, mul_zero, zero_add, add_zero]
      field_simp
    rw [hre, him] at this
    exact this
  have hint : Integrable h := by
    have hderiv : ∀ u ∈ (univ : Set ℝ),
        HasDerivWithinAt (fun u : ℝ => Real.exp (-u)) (-Real.exp (-u)) univ u := by
      intro u _
      have := ((hasDerivAt_id u).neg).exp
      simpa using this
    have hinj : InjOn (fun u : ℝ => Real.exp (-u)) univ := by
      intro u _ v _ huv
      have := Real.exp_injective huv
      linarith
    have himg : (fun u : ℝ => Real.exp (-u)) '' univ = Ioi 0 := by
      rw [Set.image_univ, range_exp_neg]
    have key := (integrableOn_image_iff_integrableOn_abs_deriv_smul MeasurableSet.univ hderiv hinj
      (lowerDefect w)).1 (by rw [himg]; exact hint.integrableOn)
    rw [integrableOn_univ] at key
    refine key.congr (Eventually.of_forall fun u => ?_)
    show |-Real.exp (-u)| • lowerDefect w (Real.exp (-u)) =
      Real.exp (-1 * u) • lowerDefect w (Real.exp (-u))
    rw [abs_neg, abs_of_pos (Real.exp_pos _), neg_one_mul]
  have hae := HTGeometry.ae_eq_zero_of_fourierIntegral_eq_zero hint hF
  have hmaps : MapsTo (fun u : ℝ => Real.exp (-u)) (Ioi (Real.log 2)) (Ioc 0 1) := fun u hu => by
    refine ⟨Real.exp_pos _, Real.exp_le_one_iff.2 ?_⟩
    have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
    have : Real.log 2 < u := hu
    linarith
  have hlt : ∀ u ∈ Ioi (Real.log 2), Real.exp (-u) < 1 / 2 := by
    intro u hu
    have hu' : Real.log 2 < u := hu
    have h1 : Real.exp (-u) < Real.exp (-Real.log 2) := Real.exp_lt_exp.2 (by linarith)
    have e : Real.exp (-Real.log 2) = 1 / 2 := by
      rw [Real.exp_neg, Real.exp_log (by norm_num)]; norm_num
    rw [e] at h1; exact h1
  have hmaps2 : MapsTo (fun u : ℝ => 2 * Real.exp (-u)) (Ioi (Real.log 2)) (Ioc 0 1) := fun u hu =>
    (⟨by positivity, by linarith [hlt u hu]⟩ : 2 * Real.exp (-u) ∈ Ioc (0 : ℝ) 1)
  have hc1 : ContinuousOn (fun u : ℝ => w (Real.exp (-u))) (Ioi (Real.log 2)) :=
    hc.comp (Real.continuous_exp.comp continuous_neg).continuousOn hmaps
  have hc2 : ContinuousOn (fun u : ℝ => w (2 * Real.exp (-u))) (Ioi (Real.log 2)) :=
    hc.comp (continuous_const.mul (Real.continuous_exp.comp continuous_neg)).continuousOn
      hmaps2
  have hcont : ContinuousOn h (Ioi (Real.log 2)) := by
    refine ContinuousOn.congr
      (f := fun u => Real.exp (-1 * u) • (w (Real.exp (-u)) - w (2 * Real.exp (-u)))) ?_ ?_
    · exact (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn.smul
        (hc1.sub hc2)
    · intro u hu
      simp only [hh, lowerDefect]
      rw [Set.indicator_of_mem
        (show Real.exp (-u) ∈ Ioc (0 : ℝ) (1 / 2) from ⟨Real.exp_pos _, (hlt u hu).le⟩)]
  have heq := Measure.eqOn_open_of_ae_eq (ae_restrict_of_ae hae) isOpen_Ioi hcont
    continuousOn_const
  have hu : Real.log 2 < -Real.log t := by
    have h1 : Real.log t < Real.log (1 / 2) := Real.log_lt_log ht.1 ht.2
    rw [one_div, Real.log_inv] at h1
    linarith
  have := heq hu
  simp only [hh, Pi.zero_apply, neg_neg, neg_mul, one_mul, Real.exp_log ht.1] at this
  rw [lowerDefect, Set.indicator_of_mem (show t ∈ Ioc (0 : ℝ) (1 / 2) from ⟨ht.1, ht.2.le⟩),
    smul_eq_zero] at this
  rcases this with h0 | h0
  · exact absurd h0 ht.1.ne'
  · exact h0

/-- **Self-similarity from the vanishing of the lower-defect Mellin transform on `Re z = 1`.** -/
theorem selfSimilar_of_mellin_lowerDefect (hc : ContinuousOn w (Ioc 0 1))
    (hint : Integrable (lowerDefect w))
    (hmel : ∀ z : ℂ, z.re = 1 → mellin (lowerDefect w) z = 0) {t : ℝ}
    (ht : t ∈ Ioc (0 : ℝ) 1) : w (t / 2) = w t := by
  have hs : t / 2 ∈ Ioc (0 : ℝ) (1 / 2) := ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have h2 : 2 * (t / 2) = t := by ring
  rcases eq_or_lt_of_le hs.2 with h1 | h1
  · -- `t = 1`: continuity from the left
    have hgt : ContinuousOn (fun u => w u - w (2 * u)) (Ioc 0 (1 / 2)) :=
      (hc.mono (Ioc_subset_Ioc_right (by norm_num))).sub
        (hc.comp (continuousOn_const.mul continuousOn_id)
          (fun u hu => ⟨by linarith [hu.1], by linarith [hu.2]⟩))
    have hmem : (1 / 2 : ℝ) ∈ Ioc (0 : ℝ) (1 / 2) := ⟨by norm_num, le_rfl⟩
    have hg' := (hgt _ hmem).mono_of_mem_nhdsWithin (s := Iio (1 / 2))
      (mem_of_superset (Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1 / 2)) Ioo_subset_Ioc_self)
    have hev : (fun u => w u - w (2 * u)) =ᶠ[𝓝[<] (1 / 2 : ℝ)] fun _ => 0 := by
      filter_upwards [Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1 / 2)] with u hu
      exact lowerDefect_eq_zero_of_mellin hc hint hmel hu
    have hlim := tendsto_nhds_unique (hg'.tendsto.congr' hev) tendsto_const_nhds
    rw [h1]
    rw [h1] at h2
    rw [← h2]
    exact sub_eq_zero.1 hlim
  · have := lowerDefect_eq_zero_of_mellin hc hint hmel ⟨hs.1, h1⟩
    rw [h2] at this
    exact sub_eq_zero.1 this

/-- **Witnesses of Mellin exponent zero are dyadically self-similar:** `w(t/2) = w(t)` on
`(0,1]`. -/
theorem IsMellinFermiWitness.selfSimilar (hw : IsMellinFermiWitness w 0) {t : ℝ}
    (ht : t ∈ Ioc (0 : ℝ) 1) : w (t / 2) = w t :=
  selfSimilar_of_mellin_lowerDefect hw.cont hw.integrable_lowerDefect
    (fun _ hz => hw.mellin_lowerDefect (by rw [hz]; norm_num)) ht

/-- **Bounded witnesses are dyadically self-similar.** -/
theorem selfSimilar_of_bounded_fermiWitness {M : ℝ} (hc : ContinuousOn w (Ioc 0 1))
    (hb : ∀ t ∈ Ioc (0 : ℝ) 1, ‖w t‖ ≤ M)
    (ho : ∀ b : ℝ, 1 ≤ b → ∫ t in Ioc (0 : ℝ) 1, fermiNymanGen b t * w t = 0) {t : ℝ}
    (ht : t ∈ Ioc (0 : ℝ) 1) : w (t / 2) = w t :=
  (isMellinFermiWitness_of_bounded hc hb ho).selfSimilar ht

/-- **The Hermitian witness class at Mellin exponent zero.**  A witness of the alternating
Nyman–Beurling system (`IsFermiNymanWitness`) with `∫_0^1 t^{x−1}|w| < ∞` for every `x > 0` is
dyadically self-similar. -/
theorem IsFermiNymanWitness.selfSimilar_of_mellinExponentZero (hw : IsFermiNymanWitness w)
    (hint : ∀ x : ℝ, 0 < x → IntegrableOn (fun t : ℝ => t ^ (x - 1) * ‖w t‖) (Ioc 0 1)) {t : ℝ}
    (ht : t ∈ Ioc (0 : ℝ) 1) : w (t / 2) = w t := by
  have hb : IsMellinFermiWitness (fun u => (starRingEnd ℂ) (w u)) 0 :=
    { cont := Complex.continuous_conj.comp_continuousOn hw.1
      nonneg := le_rfl
      lt_one := zero_lt_one
      integ := fun x hx => by simpa [Complex.norm_conj] using hint x hx
      orth := fun b hb => hw.2.2 b hb }
  have := congrArg (starRingEnd ℂ) (hb.selfSimilar ht)
  simpa using this

/-- **Bounded Hermitian witnesses are dyadically self-similar.** -/
theorem IsFermiNymanWitness.selfSimilar_of_bounded (hw : IsFermiNymanWitness w) {M : ℝ}
    (hM : ∀ t ∈ Ioc (0 : ℝ) 1, ‖w t‖ ≤ M) {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) 1) : w (t / 2) = w t :=
  hw.selfSimilar_of_mellinExponentZero
    (fun _ hx => integrableOn_rpow_mul_norm_of_bounded hw.1 hM hx) ht

end RHTower
