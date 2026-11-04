import GaloisForLFunctions.ZeroConfigurationGeometry.IsolationIdentifiesTheCluster
import GaloisForLFunctions.ZeroConfigurationGeometry.PaleyWienerWindows
import Zeta23.WeilEF.ZeroSummability
import Zeta23.Statement.SeamClosed

/-!
# Far zeros are faint in the local camera

The camera centred at height `X` modulates a window: `b_X(u) = b(u) e^{−iXu}` has transform
`b̂_X(w) = b̂(w − X)` (`paperFT_localWindow`). For a smooth window of aperture `a` it decays faster
than any power of `|Re w − X|` on the strip `|Im w| ≤ ½`, where the ordinates `γ_z = (z − ½)/i` of a
configuration lie (`norm_paperFT_localWindow_mul_le`). This module bounds what the camera sees of
the points far from the height `X`.

* **Pointwise faintness** (`norm_pointImage_mul_le`). On the strip,
  `‖f̂(γ_z) conj ĝ(conj γ_z)‖ (1 + |Im z − X|)^{2k} ≤ C_f C_g e^{a}`. Every statement below uses
  the decay of the windows only on the strip `|Im w| ≤ ½`.
* **The far tail of a cluster** (`tsum_far_le`). For any coefficient `c` supported in the strip with
  `Σ_z |c(z)|/(1 + |γ_z|²) < ∞`, the points at height distance `> R` from `X` contribute at most
  `(5/4) C_f C_g e^{a} (1 + |X|)² (1 + R)^{−(2k−2)} Σ_z |c(z)|/(1 + |γ_z|²)`. The comparison is
  `1 + |Im z| ≤ (1 + |X|)(1 + |Im z − X|)` and `1 + |γ_z|² ≤ (5/4)(1 + |Im z|)²`.
* **The far image** (`norm_tsum_far_le`). The same bound holds for the norm of the far part of the
  image itself.
* **Tempered pairs** (`tsum_far_multDiff_le`) and **the zeros of `ζ`** (`tsum_far_zeta_le`). The
  cluster `m_Z − m_{Z'}` of two tempered configurations, and the multiplicities of the zeros of `ζ`,
  satisfy the hypothesis; for `ζ` the constant is explicit through `Σ_ρ m_ρ/(1 + |γ_ρ|²)`.

The bound tends to `0` as `R → ∞` for every `k ≥ 2`, polynomially in the height: the local camera
at height `X` sees, up to an explicit tail, only the points within any fixed multiple of
`(1 + |X|)^{1/(k−1)}` of `X`.
-/

open MeasureTheory Complex Set
open scoped ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.ZeroConfigurationGeometry

open Zeta23 SquareRootThreshold

/-- The camera centred at height `X`: the window `b` modulated by `e^{−iXu}`. -/
def localWindow (X : ℝ) (b : ℝ → ℂ) : ℝ → ℂ := fun u => b u * cexp (-(I * X * u))

/-- Modulation translates the transform: `b̂_X(w) = b̂(w − X)`. -/
theorem paperFT_localWindow (X : ℝ) (b : ℝ → ℂ) (w : ℂ) :
    paperFT (localWindow X b) w = paperFT b (w - X) := by
  rw [paperFT_def, paperFT_def]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  simp only [localWindow]
  rw [mul_assoc, ← Complex.exp_add]
  congr 2
  ring

theorem gammaOf_re_eq_im (z : ℂ) : (gammaOf z).re = z.im := by
  simp [gammaOf]

theorem gammaOf_im_eq (z : ℂ) : (gammaOf z).im = 1 / 2 - z.re := by
  simp [gammaOf]

theorem abs_im_gammaOf_le {z : ℂ} (h0 : 0 ≤ z.re) (h1 : z.re ≤ 1) : |(gammaOf z).im| ≤ 1 / 2 := by
  rw [gammaOf_im_eq, abs_le]; constructor <;> linarith

/-- A smooth window of aperture `a`, centred at height `X`, decays faster than any power of
`|Re w − X|` on every horizontal line. -/
theorem norm_paperFT_localWindow_mul_le {b : ℝ → ℂ} (hb : ContDiff ℝ (⊤ : ℕ∞) b) {a : ℝ}
    (ha : 0 ≤ a) (hbs : tsupport b ⊆ Icc (-a) a) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (X : ℝ) (w : ℂ),
      ‖paperFT (localWindow X b) w‖ * (1 + |w.re - X|) ^ k ≤ C * Real.exp (a * |w.im|) := by
  obtain ⟨C, hC, hdec⟩ := exists_pow_mul_norm_paperFT_le_exp hb ha hbs k
  refine ⟨C, hC, fun X w => ?_⟩
  rw [paperFT_localWindow]
  have h := hdec (w - X)
  have hre : |w.re - X| ≤ ‖w - X‖ := by
    have := Complex.abs_re_le_norm (w - X)
    simpa using this
  have him : (w - (X : ℂ)).im = w.im := by simp
  rw [him] at h
  calc ‖paperFT b (w - X)‖ * (1 + |w.re - X|) ^ k
      ≤ ‖paperFT b (w - X)‖ * (1 + ‖w - X‖) ^ k :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (by linarith) k)
          (norm_nonneg _)
    _ = (1 + ‖w - X‖) ^ k * ‖paperFT b (w - X)‖ := mul_comm _ _
    _ ≤ C * Real.exp (a * |w.im|) := h

/-- **Pointwise faintness.** On the strip, the image of a point at height distance `d` from `X`
is at most `C_f C_g e^{a} (1 + d)^{−2k}`. The decay of the windows is only used on the strip
`|Im w| ≤ ½`, where the ordinates and their conjugates lie. -/
theorem norm_pointImage_mul_le {f g : ℝ → ℂ} {X a Cf Cg : ℝ} {k : ℕ} (ha : 0 ≤ a)
    (hf : ∀ w : ℂ, |w.im| ≤ 1 / 2 →
      ‖paperFT f w‖ * (1 + |w.re - X|) ^ k ≤ Cf * Real.exp (a * |w.im|))
    (hg : ∀ w : ℂ, |w.im| ≤ 1 / 2 →
      ‖paperFT g w‖ * (1 + |w.re - X|) ^ k ≤ Cg * Real.exp (a * |w.im|))
    {z : ℂ} (h0 : 0 ≤ z.re) (h1 : z.re ≤ 1) :
    ‖pointImage f g z‖ * (1 + |z.im - X|) ^ (2 * k) ≤ Cf * Cg * Real.exp a := by
  have him := abs_im_gammaOf_le h0 h1
  have hfz := hf (gammaOf z) him
  have hgz := hg (conj (gammaOf z)) (by rw [Complex.conj_im, abs_neg]; exact him)
  rw [gammaOf_re_eq_im] at hfz
  rw [Complex.conj_re, Complex.conj_im, abs_neg, gammaOf_re_eq_im] at hgz
  have hCg : 0 ≤ Cg := by
    have := hg X (by simp)
    have h2 : 0 ≤ ‖paperFT g X‖ * (1 + |(X : ℂ).re - X|) ^ k := by positivity
    have h3 : 0 < Real.exp (a * |(X : ℂ).im|) := Real.exp_pos _
    nlinarith
  have he : Real.exp (a * |(gammaOf z).im|) * Real.exp (a * |(gammaOf z).im|) ≤ Real.exp a := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by nlinarith)
  rw [pointImage, norm_mul, Complex.norm_conj, pow_mul', sq]
  calc ‖paperFT f (gammaOf z)‖ * ‖paperFT g (conj (gammaOf z))‖ *
        ((1 + |z.im - X|) ^ k * (1 + |z.im - X|) ^ k)
      = (‖paperFT f (gammaOf z)‖ * (1 + |z.im - X|) ^ k) *
          (‖paperFT g (conj (gammaOf z))‖ * (1 + |z.im - X|) ^ k) := by ring
    _ ≤ (Cf * Real.exp (a * |(gammaOf z).im|)) * (Cg * Real.exp (a * |(gammaOf z).im|)) :=
        mul_le_mul hfz hgz (by positivity)
          (le_trans (by positivity) hfz)
    _ = Cf * Cg * (Real.exp (a * |(gammaOf z).im|) * Real.exp (a * |(gammaOf z).im|)) := by
        ring
    _ ≤ Cf * Cg * Real.exp a := by
        have hCf : 0 ≤ Cf := by
          have h2 := le_trans (by positivity) hfz
          have h3 : 0 < Real.exp (a * |(gammaOf z).im|) := Real.exp_pos _
          nlinarith
        exact mul_le_mul_of_nonneg_left he (mul_nonneg hCf hCg)

/-- The height comparison behind the tail bound: far from `X`, the decay weight is dominated by
the temperedness weight. -/
theorem decay_le_tempered {z : ℂ} (h0 : 0 ≤ z.re) (h1 : z.re ≤ 1) {X R : ℝ} (hR : 0 ≤ R)
    (hfar : R < |z.im - X|) {k : ℕ} (hk : 1 ≤ k) :
    1 / (1 + |z.im - X|) ^ (2 * k) ≤
      5 / 4 * (1 + |X|) ^ 2 / (1 + R) ^ (2 * k - 2) / (1 + Complex.normSq (gammaOf z)) := by
  set d := 1 + |z.im - X| with hd
  have hd1 : 1 + R ≤ d := by rw [hd]; linarith
  have hR1 : 0 < 1 + R := by linarith
  have hd0 : 0 < d := lt_of_lt_of_le hR1 hd1
  have hN : Complex.normSq (gammaOf z) ≤ z.im ^ 2 + 1 / 4 := by
    rw [Complex.normSq_apply, gammaOf_re_eq_im, gammaOf_im_eq]
    nlinarith
  have hX : 1 + |z.im| ≤ (1 + |X|) * d := by
    have := abs_sub_abs_le_abs_sub z.im X
    have hX0 := abs_nonneg X
    have hd' : 1 ≤ d := by rw [hd]; linarith [abs_nonneg (z.im - X)]
    nlinarith [abs_nonneg (z.im - X), mul_nonneg hX0 (abs_nonneg (z.im - X))]
  have hT : 1 + Complex.normSq (gammaOf z) ≤ 5 / 4 * ((1 + |X|) * d) ^ 2 := by
    have h1' : 1 + Complex.normSq (gammaOf z) ≤ 5 / 4 * (1 + |z.im|) ^ 2 := by
      have := sq_abs z.im
      nlinarith [abs_nonneg z.im]
    have h2' : (1 + |z.im|) ^ 2 ≤ ((1 + |X|) * d) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hX 2
    linarith
  have hpow : (1 + R) ^ (2 * k - 2) * d ^ 2 ≤ d ^ (2 * k) := by
    have e : d ^ (2 * k) = d ^ (2 * k - 2) * d ^ 2 := by
      rw [← pow_add]; congr 1; omega
    rw [e]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hR1.le hd1 _) (by positivity)
  have hNpos : 0 < 1 + Complex.normSq (gammaOf z) := by
    linarith [Complex.normSq_nonneg (gammaOf z)]
  rw [div_div, div_le_div_iff₀ (by positivity) (mul_pos (by positivity) hNpos), one_mul]
  calc (1 + R) ^ (2 * k - 2) * (1 + Complex.normSq (gammaOf z))
      ≤ (1 + R) ^ (2 * k - 2) * (5 / 4 * ((1 + |X|) * d) ^ 2) :=
        mul_le_mul_of_nonneg_left hT (by positivity)
    _ = 5 / 4 * (1 + |X|) ^ 2 * ((1 + R) ^ (2 * k - 2) * d ^ 2) := by ring
    _ ≤ 5 / 4 * (1 + |X|) ^ 2 * d ^ (2 * k) :=
        mul_le_mul_of_nonneg_left hpow (by positivity)

/-- The far part of a cluster: `|c(z)| ‖f̂(γ_z) conj ĝ(conj γ_z)‖` at heights farther than `R`
from `X`. -/
def farTerm (c : ℂ → ℂ) (f g : ℝ → ℂ) (X R : ℝ) (z : ℂ) : ℝ :=
  if R < |z.im - X| then ‖c z‖ * ‖pointImage f g z‖ else 0

/-- **The far tail of a cluster.** -/
theorem tsum_far_le {c : ℂ → ℂ} (hcs : ∀ z, c z ≠ 0 → 0 ≤ z.re ∧ z.re ≤ 1)
    (hsum : Summable fun z => ‖c z‖ / (1 + Complex.normSq (gammaOf z)))
    {f g : ℝ → ℂ} {X a Cf Cg : ℝ} {k : ℕ} (hk : 1 ≤ k) (ha : 0 ≤ a)
    (hf : ∀ w : ℂ, |w.im| ≤ 1 / 2 →
      ‖paperFT f w‖ * (1 + |w.re - X|) ^ k ≤ Cf * Real.exp (a * |w.im|))
    (hg : ∀ w : ℂ, |w.im| ≤ 1 / 2 →
      ‖paperFT g w‖ * (1 + |w.re - X|) ^ k ≤ Cg * Real.exp (a * |w.im|))
    {R : ℝ} (hR : 0 ≤ R) :
    Summable (farTerm c f g X R) ∧
      ∑' z, farTerm c f g X R z ≤ Cf * Cg * Real.exp a * (5 / 4 * (1 + |X|) ^ 2 /
        (1 + R) ^ (2 * k - 2)) * ∑' z, ‖c z‖ / (1 + Complex.normSq (gammaOf z)) := by
  set K := Cf * Cg * Real.exp a * (5 / 4 * (1 + |X|) ^ 2 / (1 + R) ^ (2 * k - 2)) with hK
  have hCf : 0 ≤ Cf := by
    have := hf X (by simp)
    have h3 : 0 < Real.exp (a * |(X : ℂ).im|) := Real.exp_pos _
    nlinarith [norm_nonneg (paperFT f X),
      pow_nonneg (by positivity : (0 : ℝ) ≤ 1 + |(X : ℂ).re - X|) k]
  have hCg : 0 ≤ Cg := by
    have := hg X (by simp)
    have h3 : 0 < Real.exp (a * |(X : ℂ).im|) := Real.exp_pos _
    nlinarith [norm_nonneg (paperFT g X),
      pow_nonneg (by positivity : (0 : ℝ) ≤ 1 + |(X : ℂ).re - X|) k]
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  have hle : ∀ z, farTerm c f g X R z ≤ K * (‖c z‖ / (1 + Complex.normSq (gammaOf z))) := by
    intro z
    unfold farTerm
    split_ifs with hfar
    · by_cases hc : c z = 0
      · rw [hc, norm_zero, zero_mul, zero_div, mul_zero]
      · obtain ⟨h0, h1⟩ := hcs z hc
        have hpt := norm_pointImage_mul_le ha hf hg h0 h1
        have hdec := decay_le_tempered h0 h1 hR hfar hk
        have hd0 : 0 < (1 + |z.im - X|) ^ (2 * k) := by positivity
        have hpt' :
            ‖pointImage f g z‖ ≤ Cf * Cg * Real.exp a * (1 / (1 + |z.im - X|) ^ (2 * k)) := by
          rw [mul_one_div, le_div_iff₀ hd0]; exact hpt
        calc ‖c z‖ * ‖pointImage f g z‖
            ≤ ‖c z‖ * (Cf * Cg * Real.exp a * (1 / (1 + |z.im - X|) ^ (2 * k))) :=
              mul_le_mul_of_nonneg_left hpt' (norm_nonneg _)
          _ ≤ ‖c z‖ * (Cf * Cg * Real.exp a * (5 / 4 * (1 + |X|) ^ 2 / (1 + R) ^ (2 * k - 2) /
                (1 + Complex.normSq (gammaOf z)))) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hdec (by positivity))
                (norm_nonneg _)
          _ = K * (‖c z‖ / (1 + Complex.normSq (gammaOf z))) := by rw [hK]; ring
    · exact mul_nonneg hK0 (div_nonneg (norm_nonneg _)
        (by linarith [Complex.normSq_nonneg (gammaOf z)]))
  have hnn : ∀ z, 0 ≤ farTerm c f g X R z := fun z => by
    unfold farTerm; split_ifs <;> positivity
  have hs : Summable (farTerm c f g X R) := (hsum.mul_left K).of_nonneg_of_le hnn hle
  exact ⟨hs, (hs.tsum_le_tsum hle (hsum.mul_left K)).trans_eq (tsum_mul_left)⟩

/-- **The far image of a cluster is small.** The far part of the image
`Σ_{|Im z − X| > R} c(z) f̂(γ_z) conj ĝ(conj γ_z)` has norm at most the bound of `tsum_far_le`. -/
theorem norm_tsum_far_le {c : ℂ → ℂ} (hcs : ∀ z, c z ≠ 0 → 0 ≤ z.re ∧ z.re ≤ 1)
    (hsum : Summable fun z => ‖c z‖ / (1 + Complex.normSq (gammaOf z)))
    {f g : ℝ → ℂ} {X a Cf Cg : ℝ} {k : ℕ} (hk : 1 ≤ k) (ha : 0 ≤ a)
    (hf : ∀ w : ℂ, |w.im| ≤ 1 / 2 →
      ‖paperFT f w‖ * (1 + |w.re - X|) ^ k ≤ Cf * Real.exp (a * |w.im|))
    (hg : ∀ w : ℂ, |w.im| ≤ 1 / 2 →
      ‖paperFT g w‖ * (1 + |w.re - X|) ^ k ≤ Cg * Real.exp (a * |w.im|))
    {R : ℝ} (hR : 0 ≤ R) :
    ‖∑' z, (if R < |z.im - X| then c z * pointImage f g z else 0)‖ ≤
      Cf * Cg * Real.exp a * (5 / 4 * (1 + |X|) ^ 2 / (1 + R) ^ (2 * k - 2)) *
        ∑' z, ‖c z‖ / (1 + Complex.normSq (gammaOf z)) := by
  obtain ⟨hs, hle⟩ := tsum_far_le hcs hsum hk ha hf hg hR
  have hnorm : ∀ z, ‖(if R < |z.im - X| then c z * pointImage f g z else 0)‖ =
      farTerm c f g X R z := fun z => by
    unfold farTerm
    split_ifs
    · rw [norm_mul]
    · rw [norm_zero]
  calc ‖∑' z, (if R < |z.im - X| then c z * pointImage f g z else 0)‖
      ≤ ∑' z, ‖(if R < |z.im - X| then c z * pointImage f g z else 0)‖ :=
        norm_tsum_le_tsum_norm (hs.congr fun z => (hnorm z).symm)
    _ = ∑' z, farTerm c f g X R z := tsum_congr hnorm
    _ ≤ _ := hle

theorem norm_multDiff_le_add (Z Z' : ZeroConfig) (z : ℂ) :
    ‖multDiff Z Z' z‖ ≤ Z.carrier.indicator (fun z => (Z.mult z : ℝ)) z +
      Z'.carrier.indicator (fun z => (Z'.mult z : ℝ)) z := by
  rw [multDiff]
  refine (norm_sub_le _ _).trans (le_of_eq ?_)
  congr 1
  · by_cases h : z ∈ Z.carrier
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem h, Complex.norm_natCast]
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, norm_zero]
  · by_cases h : z ∈ Z'.carrier
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem h, Complex.norm_natCast]
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, norm_zero]

theorem summable_indicator_tempered (Z : ZeroConfig) (hZ : TemperedConfig Z) :
    Summable fun z => Z.carrier.indicator (fun z => (Z.mult z : ℝ)) z /
      (1 + Complex.normSq (gammaOf z)) := by
  have h := (summable_subtype_iff_indicator
    (f := fun z => (Z.mult z : ℝ) / (1 + Complex.normSq (gammaOf z))) (s := Z.carrier)).mp hZ
  refine h.congr fun z => ?_
  by_cases hz : z ∈ Z.carrier
  · rw [Set.indicator_of_mem hz, Set.indicator_of_mem hz]
  · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem hz, zero_div]

/-- **The far tail of the cluster of two tempered configurations.** -/
theorem tsum_far_multDiff_le {Z Z' : ZeroConfig} (hZ : TemperedConfig Z)
    (hZ' : TemperedConfig Z') {f g : ℝ → ℂ} {X a Cf Cg : ℝ} {k : ℕ} (hk : 1 ≤ k) (ha : 0 ≤ a)
    (hf : ∀ w : ℂ, |w.im| ≤ 1 / 2 →
      ‖paperFT f w‖ * (1 + |w.re - X|) ^ k ≤ Cf * Real.exp (a * |w.im|))
    (hg : ∀ w : ℂ, |w.im| ≤ 1 / 2 →
      ‖paperFT g w‖ * (1 + |w.re - X|) ^ k ≤ Cg * Real.exp (a * |w.im|))
    {R : ℝ} (hR : 0 ≤ R) :
    Summable (farTerm (multDiff Z Z') f g X R) ∧
      ∑' z, farTerm (multDiff Z Z') f g X R z ≤ Cf * Cg * Real.exp a *
        (5 / 4 * (1 + |X|) ^ 2 / (1 + R) ^ (2 * k - 2)) *
          ∑' z, ‖multDiff Z Z' z‖ / (1 + Complex.normSq (gammaOf z)) := by
  have hcs : ∀ z, multDiff Z Z' z ≠ 0 → 0 ≤ z.re ∧ z.re ≤ 1 := by
    intro z hz
    by_cases h : z ∈ Z.carrier
    · exact Z.strip z h
    · by_cases h' : z ∈ Z'.carrier
      · exact Z'.strip z h'
      · exact absurd (by simp [multDiff, Set.indicator_of_notMem h, Set.indicator_of_notMem h']) hz
  have hsum : Summable fun z => ‖multDiff Z Z' z‖ / (1 + Complex.normSq (gammaOf z)) := by
    refine ((summable_indicator_tempered Z hZ).add
      (summable_indicator_tempered Z' hZ')).of_nonneg_of_le
      (fun z => div_nonneg (norm_nonneg _) (by linarith [Complex.normSq_nonneg (gammaOf z)]))
      fun z => ?_
    rw [← add_div]
    exact div_le_div_of_nonneg_right (norm_multDiff_le_add Z Z' z)
      (by linarith [Complex.normSq_nonneg (gammaOf z)])
  exact tsum_far_le hcs hsum hk ha hf hg hR

/-- The zeros of `ζ` are tempered. -/
theorem temperedConfig_zeta : TemperedConfig zetaZeroConfig := by
  unfold TemperedConfig
  have := WeilEF.zero_sum_inv_sq zetaSeam
  simpa [zetaZeroConfig] using this

/-- **The far zeros of `ζ` are faint in the local camera.** For windows of aperture `a` with the
decay of `norm_paperFT_localWindow_mul_le` at height `X`, the zeros of `ζ` at height distance
`> R` from `X` contribute at most `S_ζ (5/4) C_f C_g e^{a} (1 + |X|)² (1 + R)^{−(2k−2)}`, with
`S_ζ = Σ_ρ m_ρ/(1 + |γ_ρ|²)`. -/
theorem tsum_far_zeta_le {f g : ℝ → ℂ} {X a Cf Cg : ℝ} {k : ℕ} (hk : 1 ≤ k) (ha : 0 ≤ a)
    (hf : ∀ w : ℂ, |w.im| ≤ 1 / 2 →
      ‖paperFT f w‖ * (1 + |w.re - X|) ^ k ≤ Cf * Real.exp (a * |w.im|))
    (hg : ∀ w : ℂ, |w.im| ≤ 1 / 2 →
      ‖paperFT g w‖ * (1 + |w.re - X|) ^ k ≤ Cg * Real.exp (a * |w.im|))
    {R : ℝ} (hR : 0 ≤ R) :
    ∑' z, farTerm (zetaZeroConfig.carrier.indicator fun z => (zetaZeroConfig.mult z : ℂ))
        f g X R z ≤ Cf * Cg * Real.exp a * (5 / 4 * (1 + |X|) ^ 2 / (1 + R) ^ (2 * k - 2)) *
      ∑' z, zetaZeroConfig.carrier.indicator (fun z => (zetaZeroConfig.mult z : ℝ)) z /
        (1 + Complex.normSq (gammaOf z)) := by
  have hcs : ∀ z, zetaZeroConfig.carrier.indicator (fun z => (zetaZeroConfig.mult z : ℂ)) z ≠ 0 →
      0 ≤ z.re ∧ z.re ≤ 1 := by
    intro z hz
    by_cases h : z ∈ zetaZeroConfig.carrier
    · exact zetaZeroConfig.strip z h
    · exact absurd (Set.indicator_of_notMem h _) hz
  have hnorm : ∀ z, ‖zetaZeroConfig.carrier.indicator (fun z => (zetaZeroConfig.mult z : ℂ)) z‖ =
      zetaZeroConfig.carrier.indicator (fun z => (zetaZeroConfig.mult z : ℝ)) z := fun z => by
    by_cases h : z ∈ zetaZeroConfig.carrier
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem h, Complex.norm_natCast]
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, norm_zero]
  have hsum := (summable_indicator_tempered zetaZeroConfig temperedConfig_zeta).congr fun z => by
    rw [← hnorm z]
  have h := (tsum_far_le hcs hsum hk ha hf hg hR).2
  simp only [hnorm] at h
  exact h

end GaloisForLFunctions.ZeroConfigurationGeometry
