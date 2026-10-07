import GaloisForLFunctions.RHTower.CCMRestrictedWeilPolarMultiplier
import GaloisForLFunctions.RHTower.WeilPositivityMultiplicativeToeplitzBound
import GaloisForLFunctions.RHTower.DigammaVerticalLogGrowth

/-!
# Uniform archimedean coercivity of collective polar packets

The common-width polar resonators have archimedean energy at least
`(log (N+1) - C)` times their Fourier mass, uniformly over every complex coefficient vector.
The proof retains all Fourier cross terms. Its input is the exact compact polar primitive,
whose squared mass is at most a fixed multiple of `w^4` times the packet mass.

Arbitrary overlapping packets satisfy a source bound with an explicit compact-primitive mass
penalty (`exposingOverlap_archimedean_primitive_bound`). The direct smooth compact source
interface has the same bound (`exposingCompact_archimedean_primitive_bound`). Separation is
used only to absorb that penalty in the earlier coercivity theorem.

This restricts concrete source families; it does not prove positivity for general polar tests
or the exposing-ray dual bound. See the paper proof in WP02's `PACKET-PROOF.md`.
-/

open Complex MeasureTheory Filter Topology Set
open scoped Real
open Zeta23 ComplexConjugate

namespace RHTower
noncomputable section
open ResonatorProfile

private def packetAt (N : ℕ) (x : ℕ → ℝ) (c : ℕ → ℂ) (h : ℝ → ℂ) (u : ℝ) : ℂ :=
  ∑ m ∈ Finset.Icc 1 N, c m * h (u - x m)

private def packet (N : ℕ) (c : ℕ → ℂ) (h : ℝ → ℂ) : ℝ → ℂ :=
  packetAt N (resPt N) c h

private theorem packet_contDiff (N : ℕ) (c : ℕ → ℂ) {h : ℝ → ℂ}
    (hh : ContDiff ℝ 2 h) : ContDiff ℝ 2 (packet N c h) := by
  unfold packet packetAt
  exact ContDiff.sum fun m _ =>
    contDiff_const.mul (hh.comp (contDiff_id.sub contDiff_const))

private theorem packet_support (N : ℕ) (c : ℕ → ℂ) {h : ℝ → ℂ} {w : ℝ}
    (hh : ∀ u, w / 4 < |u| → h u = 0) :
    tsupport (packet N c h) ⊆ Icc (-(Real.log N / 2 + w / 4))
      (Real.log N / 2 + w / 4) :=
  tsupport_subset_of_vanish (fun _ hu => sum_translates_eq_zero hh hu)

private theorem packet_transform (N : ℕ) (x : ℕ → ℝ) (c : ℕ → ℂ) {h : ℝ → ℂ}
    (hh : Continuous h) (hs : HasCompactSupport h) (z : ℂ) :
    paperFT (packetAt N x c h) z =
      ∑ m ∈ Finset.Icc 1 N, c m * (Complex.exp (I * z * x m) * paperFT h z) := by
  have hint : ∀ m : ℕ, Integrable fun u : ℝ =>
      c m * h (u - x m) * cexp (I * z * u) := by
    intro m
    refine (((continuous_const.mul (hh.comp
      (continuous_id.sub continuous_const))).mul (by fun_prop))).integrable_of_hasCompactSupport ?_
    exact ((hs.comp_homeomorph (Homeomorph.subRight (x m))).mul_left).mul_right
  have e : (fun u : ℝ => (∑ m ∈ Finset.Icc 1 N, c m * h (u - x m)) *
      cexp (I * z * u)) = fun u =>
      ∑ m ∈ Finset.Icc 1 N, c m * h (u - x m) * cexp (I * z * u) := by
    funext u; rw [Finset.sum_mul]
  change ∫ u, (∑ m ∈ Finset.Icc 1 N, c m * h (u - x m)) * cexp (I * z * u) = _
  rw [e, integral_finsetSum _ fun m _ => hint m]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [← paperFT_translate']
  unfold paperFT
  rw [← integral_const_mul]
  congr 1; funext u; ring

private theorem packet_mass (N : ℕ) (c : ℕ → ℂ) {g : ℝ → ℝ}
    (hg : ContDiff ℝ 2 (fun u => (g u : ℂ)))
    (hzero : ∀ u, (1 / ((N : ℝ) + 1)) / 4 < |u| → (g u : ℂ) = 0) :
    (∫ τ : ℝ, ‖paperFT (packet N c (fun u => (g u : ℂ))) τ‖ ^ 2) =
      2 * π * (∫ u, g u ^ 2) * ∑ m ∈ Finset.Icc 1 N, ‖c m‖ ^ 2 := by
  let d : ℕ → ℂ := fun m => if m ≤ N then c m else 0
  have hd : ∀ m, N < m → d m = 0 := fun m hm => if_neg (not_le.mpr hm)
  have heq : packet N d (fun u => (g u : ℂ)) = packet N c (fun u => (g u : ℂ)) := by
    funext u
    unfold packet packetAt
    exact Finset.sum_congr rfl fun m hm => by simp [d, (Finset.mem_Icc.mp hm).2]
  have hgs : HasCompactSupport (fun u => (g u : ℂ)) :=
    hasCompactSupport_of_support_subset_abs (Λ := (1 / ((N : ℝ) + 1)) / 4) fun u hu => by
      by_contra h; push Not at h; exact hu (hzero u h)
  have hvan : ∀ Y, 1 / ((N : ℝ) + 1) ≤ |Y| →
      EF.weilTest (fun u => (g u : ℂ)) (fun u => (g u : ℂ)) Y = 0 := by
    intro Y hY
    apply weilTest_self_eq_zero hzero
    have hw : 0 < 1 / ((N : ℝ) + 1) := by positivity
    linarith
  have h0 := weilTest_translates_log (N := N) (n := 1) (c := d)
    (h := fun u => (g u : ℂ)) hg.continuous hgs hvan hd le_rfl
  simp only [Nat.cast_one, Real.log_one, one_mul] at h0
  change EF.weilTest (packet N d (fun u => (g u : ℂ)))
    (packet N d (fun u => (g u : ℂ))) 0 = _ at h0
  rw [heq] at h0
  rw [(weilTest_self_zero_ofReal (g := g))] at h0
  have hsum : (∑ m ∈ Finset.Icc 1 N, d m * conj (d m)) =
      ((∑ m ∈ Finset.Icc 1 N, ‖c m‖ ^ 2 : ℝ) : ℂ) := by
    have hsd := sum_mul_conj_eq (N := N) (c := d)
    simp only [one_mul] at hsd
    rw [hsd]
    congr 1
    exact Finset.sum_congr rfl fun m hm => by simp [d, (Finset.mem_Icc.mp hm).2]
  have h := integral_normSq_paperFT_mul_cos_eq (packet_contDiff N c hg)
    (packet_support N c hzero) 0
  simp only [mul_zero, Real.cos_zero, mul_one, neg_zero] at h
  rw [h, h0, hsum]
  simp only [← Complex.ofReal_mul, Complex.add_re, Complex.ofReal_re]
  ring

/-- Width of the disjoint polar packets at the integer logarithms up to `N`. -/
def exposingPacketWidth (N : ℕ) : ℝ := 1 / ((N : ℝ) + 1)

/-- The compact primitive of the collective polar packet. -/
def exposingPacketPrimitive (N : ℕ) (c : ℕ → ℂ) : ℝ → ℂ :=
  packet N c (ψC (exposingPacketWidth N))

/-- Fixed inverse-mass constant of the corpus's smooth bump. -/
def exposingPacketInverseRatio : ℝ := (∫ v, Ψ v ^ 2) / (∫ v, d2 v ^ 2)

/-- Explicit archimedean loss, independent of the packet size and coefficients. -/
def exposingPacketCoercivityConst : ℝ :=
  digammaVerticalCoercivityConst (1 / 4) + Real.log 2 + Real.log π +
    exposingPacketInverseRatio / 4

private theorem packet_width_pos (N : ℕ) : 0 < exposingPacketWidth N := by
  unfold exposingPacketWidth; positivity

private theorem primitive_zero (N : ℕ) (u : ℝ)
    (hu : exposingPacketWidth N / 4 < |u|) : ψC (exposingPacketWidth N) u = 0 := by
  simp [ψC, Ψ_eq_zero (abs_div_gt (packet_width_pos N) hu).le]

/-- The polar differential multiplier is exact on the full collective packet. -/
theorem exposingPacket_fourier_multiplier (N : ℕ) (c : ℕ → ℂ) (z : ℂ) :
    paperFT (resonator N c (exposingPacketWidth N)) z =
      -(z ^ 2 + 1 / 4) * paperFT (exposingPacketPrimitive N c) z := by
  rw [paperFT_resonator (packet_width_pos N)]
  unfold exposingPacketPrimitive packet
  rw [packet_transform N (resPt N) c (contDiff_ψC _ 0).continuous
    (hasCompactSupport_ψC (packet_width_pos N)), Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [paperFT_gC (packet_width_pos N)]; ring

/-- Exact packet mass, with no support condition on the coefficient function. -/
theorem exposingPacket_fourier_mass (N : ℕ) (c : ℕ → ℂ) :
    (∫ τ : ℝ, ‖paperFT (resonator N c (exposingPacketWidth N)) τ‖ ^ 2) =
      2 * π * (∫ u, gR (exposingPacketWidth N) u ^ 2) *
        ∑ m ∈ Finset.Icc 1 N, ‖c m‖ ^ 2 :=
  packet_mass N c (contDiff_gC _ 2) (fun _ hu => gC_eq_zero (packet_width_pos N) hu)

/-- Exact primitive mass; disjointness is used here, not in the archimedean energy. -/
theorem exposingPacket_primitive_mass (N : ℕ) (c : ℕ → ℂ) :
    (∫ τ : ℝ, ‖paperFT (exposingPacketPrimitive N c) τ‖ ^ 2) =
      2 * π * (exposingPacketWidth N * ∫ v, Ψ v ^ 2) *
        ∑ m ∈ Finset.Icc 1 N, ‖c m‖ ^ 2 := by
  rw [exposingPacketPrimitive]
  change (∫ τ : ℝ, ‖paperFT (packet N c (fun u => (Ψ (u / exposingPacketWidth N) : ℂ))) τ‖ ^ 2) = _
  rw [packet_mass N c (contDiff_ψC _ 2) (primitive_zero N),
    integral_sq_comp_div Ψ (packet_width_pos N)]

/-- The compact primitive suppresses low frequencies uniformly in every coefficient vector. -/
theorem exposingPacket_inverse_mass (N : ℕ) (c : ℕ → ℂ) :
    (∫ τ : ℝ, ‖paperFT (exposingPacketPrimitive N c) τ‖ ^ 2) ≤
      exposingPacketInverseRatio * exposingPacketWidth N ^ 4 *
        ∫ τ : ℝ, ‖paperFT (resonator N c (exposingPacketWidth N)) τ‖ ^ 2 := by
  rw [exposingPacket_primitive_mass, exposingPacket_fourier_mass]
  have hw := packet_width_pos N
  have hP : 0 ≤ ∫ v, Ψ v ^ 2 := integral_nonneg fun v => sq_nonneg _
  have hD := integral_d2_sq_pos
  have hk := integral_gR_sq_ge hw
  have hkw : (∫ v, d2 v ^ 2) ≤
      (∫ u, gR (exposingPacketWidth N) u ^ 2) * exposingPacketWidth N ^ 3 :=
    (div_le_iff₀ (by positivity)).mp hk
  have hratio : exposingPacketWidth N * (∫ v, Ψ v ^ 2) ≤
      exposingPacketInverseRatio * exposingPacketWidth N ^ 4 *
        (∫ u, gR (exposingPacketWidth N) u ^ 2) := by
    unfold exposingPacketInverseRatio
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div]
    apply (le_div_iff₀ hD).mpr
    have h := mul_le_mul_of_nonneg_left hkw (mul_nonneg hw.le hP)
    nlinarith only [h]
  have hs : 0 ≤ ∑ m ∈ Finset.Icc 1 N, ‖c m‖ ^ 2 :=
    Finset.sum_nonneg fun m _ => sq_nonneg _
  have h := mul_le_mul_of_nonneg_left hratio (mul_nonneg (by positivity : 0 ≤ 2 * π) hs)
  nlinarith only [h]

private theorem arch_symbol_lower (τ : ℝ) :
    Real.log (2 + |τ|) -
      (digammaVerticalCoercivityConst (1 / 4) + Real.log 2 + Real.log π) ≤
      archimedeanWeilSymbol (τ / (2 * π)) := by
  have hd := re_digamma_vertical_ge (a := 1 / 4) (by norm_num) (by norm_num) (τ / 2)
  have hl : Real.log (2 + |τ|) ≤ Real.log 2 + Real.log (2 + |τ / 2|) := by
    rw [← Real.log_mul (by norm_num) (by positivity)]
    apply Real.log_le_log (by positivity)
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith [abs_nonneg τ]
  rw [archimedeanWeilSymbol_eq]
  have he : π * (τ / (2 * π)) = τ / 2 := by field_simp
  rw [he]
  linarith

private theorem scalar_log_bound {r q : ℝ} (hr : 0 < r) (hq : 0 < q) :
    Real.log r - Real.log q ≤ r ^ 4 / (4 * q ^ 4) := by
  have h := Real.log_le_sub_one_of_pos (by positivity : 0 < (r / q) ^ 4)
  rw [Real.log_pow, Real.log_div hr.ne' hq.ne'] at h
  rw [div_pow] at h
  rw [show r ^ 4 / (4 * q ^ 4) = (r ^ 4 / q ^ 4) / 4 by ring]
  norm_num only [Nat.cast_ofNat] at h
  linarith

private theorem scalar_energy_bound {r : ℝ} (hr : 0 < r) (τ : ℝ) :
    (Real.log r -
      (digammaVerticalCoercivityConst (1 / 4) + Real.log 2 + Real.log π)) *
        (τ ^ 2 + 1 / 4) ^ 2 ≤
      (τ ^ 2 + 1 / 4) ^ 2 * archimedeanWeilSymbol (τ / (2 * π)) + r ^ 4 / 4 := by
  have ha := arch_symbol_lower τ
  have hl := scalar_log_bound hr (by positivity : 0 < 2 + |τ|)
  have hs : (τ ^ 2 + 1 / 4) ^ 2 ≤ (2 + |τ|) ^ 4 := by
    have hsmall : τ ^ 2 + 1 / 4 ≤ (2 + |τ|) ^ 2 := by
      nlinarith [sq_abs τ, abs_nonneg τ]
    nlinarith [sq_nonneg ((2 + |τ|) ^ 2 - (τ ^ 2 + 1 / 4))]
  have hratio : (τ ^ 2 + 1 / 4) ^ 2 / (2 + |τ|) ^ 4 ≤ 1 :=
    (div_le_one (by positivity)).mpr hs
  have hcoeff : r ^ 4 / (4 * (2 + |τ|) ^ 4) * (τ ^ 2 + 1 / 4) ^ 2 ≤ r ^ 4 / 4 := by
    have h := mul_le_mul_of_nonneg_left hratio (by positivity : 0 ≤ r ^ 4 / 4)
    rw [mul_one] at h
    calc _ = (r ^ 4 / 4) * ((τ ^ 2 + 1 / 4) ^ 2 / (2 + |τ|) ^ 4) := by field_simp
      _ ≤ _ := h
  have hmain := mul_le_mul_of_nonneg_right
    (show Real.log r -
      (digammaVerticalCoercivityConst (1 / 4) + Real.log 2 + Real.log π) ≤
      archimedeanWeilSymbol (τ / (2 * π)) + r ^ 4 / (4 * (2 + |τ|) ^ 4) by linarith)
    (sq_nonneg (τ ^ 2 + 1 / 4))
  nlinarith only [hcoeff, hmain]

private theorem packet_energy_pointwise (N : ℕ) (c : ℕ → ℂ) (τ : ℝ) :
    (Real.log ((N : ℝ) + 1) -
      (digammaVerticalCoercivityConst (1 / 4) + Real.log 2 + Real.log π)) *
      ‖paperFT (resonator N c (exposingPacketWidth N)) τ‖ ^ 2 ≤
    ‖paperFT (resonator N c (exposingPacketWidth N)) τ‖ ^ 2 *
      archimedeanWeilSymbol (τ / (2 * π)) +
    (((N : ℝ) + 1) ^ 4 / 4) * ‖paperFT (exposingPacketPrimitive N c) τ‖ ^ 2 := by
  have hm : ‖paperFT (resonator N c (exposingPacketWidth N)) τ‖ ^ 2 =
      (τ ^ 2 + 1 / 4) ^ 2 * ‖paperFT (exposingPacketPrimitive N c) τ‖ ^ 2 := by
    rw [exposingPacket_fourier_multiplier, norm_mul, norm_neg]
    have he : ((τ : ℂ) ^ 2 + 1 / 4) = ((τ ^ 2 + 1 / 4 : ℝ) : ℂ) := by push_cast; ring
    rw [he, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
  have h := mul_le_mul_of_nonneg_right
    (scalar_energy_bound (by positivity : 0 < (N : ℝ) + 1) τ)
    (sq_nonneg ‖paperFT (exposingPacketPrimitive N c) τ‖)
  rw [hm]
  nlinarith only [h]

/-- Collective interference cannot remove the logarithmic archimedean cost of shrinking
polar packets. This theorem has no Weil-positivity or arithmetic premise. -/
theorem exposingPacket_archimedean_coercivity (N : ℕ) (c : ℕ → ℂ) :
    (Real.log ((N : ℝ) + 1) - exposingPacketCoercivityConst) *
      (∫ τ : ℝ, ‖paperFT (resonator N c (exposingPacketWidth N)) τ‖ ^ 2) ≤
    ∫ τ : ℝ, ‖paperFT (resonator N c (exposingPacketWidth N)) τ‖ ^ 2 *
      archimedeanWeilSymbol (τ / (2 * π)) := by
  let F := resonator N c (exposingPacketWidth N)
  let G := exposingPacketPrimitive N c
  have hF := contDiff_resonator N c (exposingPacketWidth N) 2
  have hFs := packet_support N c (fun _ hu => gC_eq_zero (packet_width_pos N) hu)
  have hG := packet_contDiff N c (contDiff_ψC (exposingPacketWidth N) 2)
  have hGs := packet_support N c (primitive_zero N)
  have hiF := integrable_normSq_paperFT hF hFs
  have hiG := integrable_normSq_paperFT hG hGs
  have hiA := integrable_normSq_paperFT_mul_arch hF hFs
  let C := digammaVerticalCoercivityConst (1 / 4) + Real.log 2 + Real.log π
  have hi := integral_mono (hiF.const_mul (Real.log ((N : ℝ) + 1) - C))
    (hiA.add (hiG.const_mul (((N : ℝ) + 1) ^ 4 / 4)))
    (packet_energy_pointwise N c)
  simp only [Pi.add_apply] at hi
  rw [integral_const_mul, integral_add hiA (hiG.const_mul _), integral_const_mul] at hi
  have hm := mul_le_mul_of_nonneg_left (exposingPacket_inverse_mass N c)
    (by positivity : 0 ≤ ((N : ℝ) + 1) ^ 4 / 4)
  have he : (((N : ℝ) + 1) ^ 4 / 4) *
      (exposingPacketInverseRatio * exposingPacketWidth N ^ 4 *
        ∫ τ : ℝ, ‖paperFT F τ‖ ^ 2) =
      exposingPacketInverseRatio / 4 * ∫ τ : ℝ, ‖paperFT F τ‖ ^ 2 := by
    unfold exposingPacketWidth
    field_simp
  rw [he] at hm
  unfold exposingPacketCoercivityConst
  dsimp only [C] at hi
  unfold exposingPacketPrimitive at hm
  linarith only [hi, hm]


/-! ## The surviving source bound for arbitrary overlapping packets -/

/-- A finite polar packet at arbitrary centers, with positive width `exp(-s)`. -/
def exposingOverlapTest (N : ℕ) (x : ℕ → ℝ) (c : ℕ → ℂ) (s : ℝ) : ℝ → ℂ :=
  packetAt N x c (gC (Real.exp (-s)))

/-- The literal compact primitive of an arbitrary overlapping packet. -/
def exposingOverlapPrimitive (N : ℕ) (x : ℕ → ℝ) (c : ℕ → ℂ) (s : ℝ) : ℝ → ℂ :=
  packetAt N x c (ψC (Real.exp (-s)))

private theorem packetAt_contDiff (N : ℕ) (x : ℕ → ℝ) (c : ℕ → ℂ) {h : ℝ → ℂ}
    (hh : ContDiff ℝ 2 h) : ContDiff ℝ 2 (packetAt N x c h) :=
  ContDiff.sum fun _ _ =>
    contDiff_const.mul (hh.comp (contDiff_id.sub contDiff_const))

private theorem packetAt_support (N : ℕ) (x : ℕ → ℝ) (c : ℕ → ℂ) {h : ℝ → ℂ} {w : ℝ}
    (hh : ∀ u, w / 4 < |u| → h u = 0) :
    tsupport (packetAt N x c h) ⊆
      Icc (-((∑ m ∈ Finset.Icc 1 N, |x m|) + w / 4))
        ((∑ m ∈ Finset.Icc 1 N, |x m|) + w / 4) := by
  apply tsupport_subset_of_vanish
  intro u hu
  refine Finset.sum_eq_zero fun m hm => ?_
  have hx : |x m| ≤ ∑ j ∈ Finset.Icc 1 N, |x j| :=
    Finset.single_le_sum (fun j _ => abs_nonneg (x j)) hm
  have hd := abs_sub_abs_le_abs_sub u (x m)
  rw [hh _ (by linarith), mul_zero]

/-- Arbitrary overlap preserves the exact polar multiplier, including both polar zeros. -/
theorem exposingOverlap_fourier_multiplier (N : ℕ) (x : ℕ → ℝ) (c : ℕ → ℂ)
    (s : ℝ) (z : ℂ) :
    paperFT (exposingOverlapTest N x c s) z =
      -(z ^ 2 + 1 / 4) * paperFT (exposingOverlapPrimitive N x c s) z := by
  unfold exposingOverlapTest exposingOverlapPrimitive
  rw [packet_transform N x c (contDiff_gC _ 0).continuous
      (hasCompactSupport_gC (Real.exp_pos _)),
    packet_transform N x c (contDiff_ψC _ 0).continuous
      (hasCompactSupport_ψC (Real.exp_pos _)), Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [paperFT_gC (Real.exp_pos _)]; ring

/-- The unconditional source bound that survives arbitrary overlap. The explicit primitive-mass
penalty is retained; no separation, positivity, arithmetic or width-sign premise is required. -/
theorem exposingOverlap_archimedean_primitive_bound (N : ℕ) (x : ℕ → ℝ)
    (c : ℕ → ℂ) (s b : ℝ) :
    (b - (digammaVerticalCoercivityConst (1 / 4) + Real.log 2 + Real.log π)) *
      (∫ τ : ℝ, ‖paperFT (exposingOverlapTest N x c s) τ‖ ^ 2) ≤
    (∫ τ : ℝ, ‖paperFT (exposingOverlapTest N x c s) τ‖ ^ 2 *
      archimedeanWeilSymbol (τ / (2 * π))) +
      (Real.exp b ^ 4 / 4) * ∫ τ : ℝ, ‖paperFT (exposingOverlapPrimitive N x c s) τ‖ ^ 2 := by
  have hF : ContDiff ℝ 2 (exposingOverlapTest N x c s) :=
    packetAt_contDiff N x c (contDiff_gC _ 2)
  have hG : ContDiff ℝ 2 (exposingOverlapPrimitive N x c s) :=
    packetAt_contDiff N x c (contDiff_ψC _ 2)
  have hFs := packetAt_support N x c (fun _ hu => gC_eq_zero (Real.exp_pos (-s)) hu)
  have hGs := packetAt_support N x c
    (h := ψC (Real.exp (-s))) (w := Real.exp (-s)) (fun u hu => by
      simp [ψC, Ψ_eq_zero (abs_div_gt (Real.exp_pos (-s)) hu).le])
  have hiF := integrable_normSq_paperFT hF hFs
  have hiG := integrable_normSq_paperFT hG hGs
  have hiA := integrable_normSq_paperFT_mul_arch hF hFs
  have hp : ∀ τ : ℝ,
      (b - (digammaVerticalCoercivityConst (1 / 4) + Real.log 2 + Real.log π)) *
        ‖paperFT (exposingOverlapTest N x c s) τ‖ ^ 2 ≤
      ‖paperFT (exposingOverlapTest N x c s) τ‖ ^ 2 *
        archimedeanWeilSymbol (τ / (2 * π)) +
        (Real.exp b ^ 4 / 4) * ‖paperFT (exposingOverlapPrimitive N x c s) τ‖ ^ 2 := by
    intro τ
    have hm : ‖paperFT (exposingOverlapTest N x c s) τ‖ ^ 2 =
        (τ ^ 2 + 1 / 4) ^ 2 * ‖paperFT (exposingOverlapPrimitive N x c s) τ‖ ^ 2 := by
      rw [exposingOverlap_fourier_multiplier, norm_mul, norm_neg]
      have he : ((τ : ℂ) ^ 2 + 1 / 4) = ((τ ^ 2 + 1 / 4 : ℝ) : ℂ) := by push_cast; ring
      rw [he, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
    have h := mul_le_mul_of_nonneg_right (scalar_energy_bound (Real.exp_pos b) τ)
      (sq_nonneg ‖paperFT (exposingOverlapPrimitive N x c s) τ‖)
    rw [Real.log_exp] at h
    rw [hm]
    nlinarith only [h]
  have hi := integral_mono (hiF.const_mul _)
    (hiA.add (hiG.const_mul (Real.exp b ^ 4 / 4))) hp
  simp only [Pi.add_apply] at hi
  rw [integral_const_mul, integral_add hiA (hiG.const_mul _), integral_const_mul] at hi
  exact hi

/-! ## Direct bound on the full smooth compact primitive interface -/

/-- Exact Fourier multiplier on every smooth compact source, without a packet expansion. -/
theorem exposingCompact_fourier_multiplier (a : SuzukiPositiveAperture)
    (g : CCMComplexSmoothInteriorSource a) (z : ℂ) :
    paperFT (g.polarMultiplier : ℝ → ℂ) z =
      -(z ^ 2 + 1 / 4) * paperFT (g : ℝ → ℂ) z := by
  have hg2 : ContDiff ℝ 2 (g : ℝ → ℂ) := g.smooth.of_le (show ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) from
      WithTop.coe_le_coe.mpr le_top)
  have hdd := paperFT_deriv_deriv hg2 g.hasCompactSupport z
  have hc : ContDiff ℝ (⊤ : ℕ∞) (deriv (deriv (g : ℝ → ℂ))) := by
    have h := g.smooth.iterate_deriv 2
    simpa [Function.iterate_succ, Function.comp] using h
  have hi1 : Integrable (fun u : ℝ => deriv (deriv (g : ℝ → ℂ)) u *
      Complex.exp (I * z * u)) :=
    (hc.continuous.mul (by fun_prop)).integrable_of_hasCompactSupport
      g.hasCompactSupport.deriv.deriv.mul_right
  have hi0 : Integrable (fun u : ℝ => g u * Complex.exp (I * z * u)) :=
    (g.smooth.continuous.mul (by fun_prop)).integrable_of_hasCompactSupport
      g.hasCompactSupport.mul_right
  have he : (fun u : ℝ => g.polarMultiplier u * Complex.exp (I * z * u)) =
      fun u => deriv (deriv (g : ℝ → ℂ)) u * Complex.exp (I * z * u) +
        (-(1 / 4 : ℂ)) * (g u * Complex.exp (I * z * u)) := by
    funext u
    rw [CCMComplexSmoothInteriorSource.polarMultiplier_apply]
    ring
  unfold paperFT at hdd ⊢
  rw [he, integral_add hi1 (hi0.const_mul _), integral_const_mul, hdd]
  ring

/-- The primitive penalty bound holds for every smooth compact polar source `D g`.
It has no source-positivity, arithmetic, coefficient or separation premise. -/
theorem exposingCompact_archimedean_primitive_bound (a : SuzukiPositiveAperture)
    (g : CCMComplexSmoothInteriorSource a) (b : ℝ) :
    (b - (digammaVerticalCoercivityConst (1 / 4) + Real.log 2 + Real.log π)) *
      (∫ τ : ℝ, ‖paperFT (g.polarMultiplier : ℝ → ℂ) τ‖ ^ 2) ≤
    (∫ τ : ℝ, ‖paperFT (g.polarMultiplier : ℝ → ℂ) τ‖ ^ 2 *
      archimedeanWeilSymbol (τ / (2 * π))) +
      (Real.exp b ^ 4 / 4) * ∫ τ : ℝ, ‖paperFT (g : ℝ → ℂ) τ‖ ^ 2 := by
  have hF : ContDiff ℝ 2 (g.polarMultiplier : ℝ → ℂ) :=
    g.polarMultiplier.smooth.of_le (show ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) from
      WithTop.coe_le_coe.mpr le_top)
  have hG : ContDiff ℝ 2 (g : ℝ → ℂ) := g.smooth.of_le (show ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) from
      WithTop.coe_le_coe.mpr le_top)
  have hFs := g.polarMultiplier.tsupport_subset.trans Ioo_subset_Icc_self
  have hGs := g.tsupport_subset.trans Ioo_subset_Icc_self
  have hiF := integrable_normSq_paperFT hF hFs
  have hiG := integrable_normSq_paperFT hG hGs
  have hiA := integrable_normSq_paperFT_mul_arch hF hFs
  have hp : ∀ τ : ℝ,
      (b - (digammaVerticalCoercivityConst (1 / 4) + Real.log 2 + Real.log π)) *
        ‖paperFT (g.polarMultiplier : ℝ → ℂ) τ‖ ^ 2 ≤
      ‖paperFT (g.polarMultiplier : ℝ → ℂ) τ‖ ^ 2 *
        archimedeanWeilSymbol (τ / (2 * π)) +
        (Real.exp b ^ 4 / 4) * ‖paperFT (g : ℝ → ℂ) τ‖ ^ 2 := by
    intro τ
    have hm : ‖paperFT (g.polarMultiplier : ℝ → ℂ) τ‖ ^ 2 =
        (τ ^ 2 + 1 / 4) ^ 2 * ‖paperFT (g : ℝ → ℂ) τ‖ ^ 2 := by
      rw [exposingCompact_fourier_multiplier, norm_mul, norm_neg]
      have he : ((τ : ℂ) ^ 2 + 1 / 4) = ((τ ^ 2 + 1 / 4 : ℝ) : ℂ) := by push_cast; ring
      rw [he, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
    have h := mul_le_mul_of_nonneg_right (scalar_energy_bound (Real.exp_pos b) τ)
      (sq_nonneg ‖paperFT (g : ℝ → ℂ) τ‖)
    rw [Real.log_exp] at h
    rw [hm]
    nlinarith only [h]
  have hi := integral_mono (hiF.const_mul _)
    (hiA.add (hiG.const_mul (Real.exp b ^ 4 / 4))) hp
  simp only [Pi.add_apply] at hi
  rw [integral_const_mul, integral_add hiA (hiG.const_mul _), integral_const_mul] at hi
  exact hi

end
end RHTower
