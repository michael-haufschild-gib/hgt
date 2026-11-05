import GaloisForLFunctions.FiniteFreeProbability.RealRootsCauchyLaw
import GaloisForLFunctions.FiniteFreeProbability.BulkBlindness

/-!
# The Cauchy law for every hyperbolic kernel

Let `g` be a hyperbolic kernel, `R_d(x) = ∫ g(v)(x + iv)^d dv`, and let `y` run over the rescaled roots
`x/ℓ_d`, `ℓ_d = ½ log d`.

**Theorem.** For `Im w > 0`: `(1/d) Σ_{y real} 1/(w − y) → 1/(w + i)`.

So the real roots of `R_d` follow the standard Cauchy law at scale `½ log d` for every such kernel. Applied to
`g = Φ e^{−τv²}`: the Jensen polynomials of the backward heat flow `H_{−τ}`, which has infinitely many non-real
zeros, have the same bulk as those of `Ξ`. Neither the proportion of real roots nor their limit law can detect
non-real zeros.

The proof has an abstract core: an upper bound `|Π_y (z − y)| ≤ B_d |z + i|^d` on circles around `iθ₀` and a lower
bound at the centre, with `log(B_d (1 + θ₀)^d/Π_y |iθ₀ − y|) = o(d)`, determine the number of roots in the disc and
the Cauchy transform of the roots outside it.
-/

open Polynomial Filter Topology Complex Metric MeasureTheory
open scoped ComplexConjugate
open GaloisForLFunctions.HTGeometry RHTower RHTower.DeBruijn

namespace FiniteFreeProbability

noncomputable section

/-! ## The abstract core -/

/-- **Few roots in a disc**, from a bound on a circle and a bound at the centre. -/
theorem tendsto_card_near_of_data {M : ℕ → Multiset ℂ} (hcard : ∀ d, Multiset.card (M d) = d)
    {θ₀ r R : ℝ} (hr : 0 < r) (hrR : r < R) (hRθ : R < θ₀ + 1) {L B P : ℕ → ℝ}
    (hB : ∀ᶠ d : ℕ in atTop, ∀ z ∈ sphere (I * (θ₀ : ℂ)) R,
      ‖((M d).map fun y => z - y).prod‖ ≤ B d * ‖z + I‖ ^ d)
    (hP : ∀ᶠ d : ℕ in atTop, 0 < P d ∧ P d ≤ ((M d).map fun y => ‖I * (θ₀ : ℂ) - y‖).prod)
    (hL : ∀ᶠ d : ℕ in atTop, Real.log (B d * (1 + θ₀) ^ d / P d) ≤ L d)
    (herr : Tendsto (fun d : ℕ => L d / d) atTop (𝓝 0)) :
    Tendsto (fun d : ℕ => (Multiset.card ((M d).filter fun y => ‖I * (θ₀ : ℂ) - y‖ ≤ r) : ℝ) / d)
      atTop (𝓝 0) := by
  have hR : 0 < R := by linarith
  set Λ := Real.log (R / r)
  have hΛ : 0 < Λ := Real.log_pos ((one_lt_div hr).2 hrR)
  have h1θ : 0 < 1 + θ₀ := by linarith
  refine squeeze_zero' (Eventually.of_forall fun d => by positivity) ?_
    (by simpa using herr.div_const Λ)
  filter_upwards [hB, hP, hL, eventually_gt_atTop 0] with d hBd hPd hLd hd
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  obtain ⟨hP0, hPle⟩ := hPd
  have hnorm : ‖I * (θ₀ : ℂ) - -I‖ = 1 + θ₀ := by
    rw [show I * (θ₀ : ℂ) - -I = I * ((1 + θ₀ : ℝ) : ℂ) by
      push_cast
      ring, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_of_nonneg h1θ.le]
  have ha : -I ∉ closedBall (I * (θ₀ : ℂ)) R := by
    rw [mem_closedBall, dist_comm, dist_eq_norm, hnorm]
    linarith
  have hA1 := multiset_prod_max_le hR ha (M d) (B := B d) (fun z hz => by
    rw [hcard, sub_neg_eq_add]
    exact hBd z hz)
  rw [hcard, hnorm] at hA1
  have hA2 := pow_mul_prod_norm_le (M d) (I * (θ₀ : ℂ)) hr hrR.le
  set N := Multiset.card ((M d).filter fun y => ‖I * (θ₀ : ℂ) - y‖ ≤ r)
  have hRr : 0 < R / r := by positivity
  have hkey : (R / r) ^ N * P d ≤ B d * (1 + θ₀) ^ d :=
    (mul_le_mul_of_nonneg_left hPle (by positivity)).trans (hA2.trans hA1)
  have hquot : (R / r) ^ N ≤ B d * (1 + θ₀) ^ d / P d := by
    rwa [le_div_iff₀ hP0]
  have hlog := Real.log_le_log (by positivity) hquot
  rw [Real.log_pow] at hlog
  rw [div_le_div_iff₀ hdR hΛ]
  have h3 : L d / d * d = L d := by field_simp
  rw [h3]
  linarith

/-- **The Cauchy transform outside a disc**, from the same data. -/
theorem tendsto_exterior_of_data {M : ℕ → Multiset ℂ} (hcard : ∀ d, Multiset.card (M d) = d)
    {θ₀ R : ℝ} (hθ₀ : 0 < θ₀) (hR : 0 < R) (hRθ : R < θ₀ + 1) {w : ℂ}
    (hw : ‖w - I * (θ₀ : ℂ)‖ < R) {L B P : ℕ → ℝ}
    (hB : ∀ᶠ d : ℕ in atTop, ∀ z ∈ sphere (I * (θ₀ : ℂ)) R,
      ‖((M d).map fun y => z - y).prod‖ ≤ B d * ‖z + I‖ ^ d)
    (hP : ∀ᶠ d : ℕ in atTop, 0 < P d ∧ P d ≤ ((M d).map fun y => ‖I * (θ₀ : ℂ) - y‖).prod)
    (hL : ∀ᶠ d : ℕ in atTop, Real.log (B d * (1 + θ₀) ^ d / P d) ≤ L d)
    (herr : Tendsto (fun d : ℕ => L d / d) atTop (𝓝 0))
    (hnear : Tendsto (fun d : ℕ =>
      (Multiset.card ((M d).filter fun y => ‖I * (θ₀ : ℂ) - y‖ ≤ R) : ℝ) / d) atTop (𝓝 0)) :
    Tendsto (fun d : ℕ => (1 / (d : ℂ)) *
      (((M d).filter fun y => R ≤ ‖I * (θ₀ : ℂ) - y‖).map fun y => 1 / (w - y)).sum)
      atTop (𝓝 (1 / (w + I))) := by
  set c := I * (θ₀ : ℂ)
  have h1θ : 0 < 1 + θ₀ := by linarith
  have hne : ∀ z ∈ closedBall c R, z + I ≠ 0 := fun z hz h0 => by
    rw [mem_closedBall, dist_eq_norm] at hz
    have h1 : z = -I := by linear_combination h0
    rw [h1, show -I - c = -(I * ((1 + θ₀ : ℝ) : ℂ)) by simp only [c]; push_cast; ring, norm_neg,
      norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_of_nonneg h1θ.le] at hz
    linarith
  set ρ := ‖w - c‖
  have hδ : 0 < R - ρ := by linarith
  have hρ0 : 0 ≤ ρ := norm_nonneg _
  set K : ℝ := 2 * ((ρ + R) / 2) / (R - (ρ + R) / 2) / ((R - ρ) / 2)
  have hKpos : 0 ≤ K := by
    have h1 : 0 < R - (ρ + R) / 2 := by linarith
    have h2 : 0 < (R - ρ) / 2 := by linarith
    positivity
  have hinv : Tendsto (fun d : ℕ => (1 : ℝ) / d) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat 1
  have hbound : Tendsto (fun d : ℕ => K * (L d / d + 1 / d) +
      (Multiset.card ((M d).filter fun y => ‖c - y‖ ≤ R) : ℝ) / d * (1 / (R - ρ))) atTop (𝓝 0) := by
    have := ((herr.add hinv).const_mul K).add (hnear.mul_const (1 / (R - ρ)))
    simpa using this
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hbound
  filter_upwards [hB, hP, hL, eventually_gt_atTop 0] with d hBd hPd hLd hd
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hdC : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hd.ne'
  obtain ⟨hP0, hPle⟩ := hPd
  set N := M d
  have hcardM : Multiset.card N = d := hcard d
  have hM0 : N ≠ 0 := fun h => by
    rw [h] at hcardM
    simp at hcardM
    omega
  have hnormc : ‖c + I‖ = 1 + θ₀ := by
    rw [show c + I = I * ((1 + θ₀ : ℝ) : ℂ) by simp only [c]; push_cast; ring, norm_mul,
      Complex.norm_I, one_mul, Complex.norm_real, Real.norm_of_nonneg h1θ.le]
  set mlow := P d / (1 + θ₀) ^ d
  have hmlow : 0 < mlow := by positivity
  have hle : mlow ≤ ‖blaschkeQuotient c R N c‖ := by
    rw [blaschkeQuotient_center_norm hR, hcardM, hnormc]
    have h1 := pow_mul_prod_norm_le N c (r := R) (R := R) hR le_rfl
    rw [div_self hR.ne', one_pow, one_mul] at h1
    exact div_le_div_of_nonneg_right (hPle.trans h1) (by positivity)
  have hBq : ∀ z ∈ sphere c R, ‖(N.map fun y => z - y).prod‖ ≤ B d * ‖z + I‖ ^ Multiset.card N :=
    fun z hz => by
      rw [hcardM]
      exact hBd z hz
  have hmain := norm_sum_blaschkeLogDeriv_sub_le hR hne N hBq hmlow hle hw hM0
  rw [hcardM] at hmain
  have hlog : Real.log (B d / mlow) ≤ L d := by
    have : B d / mlow = B d * (1 + θ₀) ^ d / P d := by
      simp only [mlow]
      field_simp
    rwa [this]
  set p : ℂ → Prop := fun y => R ≤ ‖c - y‖
  have hext : ∀ y ∈ N.filter p, blaschkeLogDeriv c R y w = 1 / (w - y) := fun y hy => by
    have hyR : R ≤ ‖c - y‖ := (Multiset.mem_filter.1 hy).2
    unfold blaschkeLogDeriv
    rw [if_neg (by rw [norm_sub_rev]; exact not_lt.2 hyR)]
  have hsplit := multiset_sum_filter_split N p (fun y => blaschkeLogDeriv c R y w)
  rw [Multiset.map_congr rfl hext] at hsplit
  set Sₑ := ((N.filter p).map fun y => 1 / (w - y)).sum
  set Sᵢ := ((N.filter fun y => ¬ p y).map fun y => blaschkeLogDeriv c R y w).sum
  have hSi : ‖Sᵢ‖ ≤ (Multiset.card (N.filter fun y => ‖c - y‖ ≤ R) : ℝ) * (1 / (R - ρ)) := by
    have h1 := norm_multiset_sum_map_le (N.filter fun y => ¬ p y)
      (fun y => blaschkeLogDeriv c R y w) (B := 1 / (R - ρ))
      (fun y _ => norm_blaschkeLogDeriv_le hw y)
    refine h1.trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
    have hmono : (N.filter fun y => ¬ p y) ≤ N.filter fun y => ‖c - y‖ ≤ R :=
      Multiset.monotone_filter_right N fun y hy => (not_le.1 hy).le
    exact_mod_cast Multiset.card_le_card hmono
  have hid : (1 / (d : ℂ)) * Sₑ - 1 / (w + I) =
      (1 / (d : ℂ)) * (((N.map fun y => blaschkeLogDeriv c R y w).sum - (d : ℂ) / (w + I)) - Sᵢ) := by
    rw [hsplit]
    have hwI : w + I ≠ 0 := hne w (ball_subset_closedBall (by rwa [mem_ball, dist_eq_norm]))
    field_simp
    ring
  rw [hid, norm_mul, norm_div, norm_one, Complex.norm_natCast]
  have hmain' : ‖(N.map fun y => blaschkeLogDeriv c R y w).sum - (d : ℂ) / (w + I)‖ ≤
      K * (L d + 1) := by
    refine hmain.trans ?_
    have hK : 2 * (Real.log (B d / mlow) + 1) * ((ρ + R) / 2) / (R - (ρ + R) / 2) / ((R - ρ) / 2) =
        K * (Real.log (B d / mlow) + 1) := by
      simp only [K]
      ring
    rw [hK]
    exact mul_le_mul_of_nonneg_left (by linarith) hKpos
  have hnorm := (norm_sub_le _ _).trans (add_le_add hmain' hSi)
  have hdiv := mul_le_mul_of_nonneg_left hnorm (by positivity : (0 : ℝ) ≤ 1 / (d : ℝ))
  refine hdiv.trans_eq ?_
  have hexpand : (1 / (d : ℝ)) * (K * (L d + 1)) = K * (L d / d + 1 / d) := by
    field_simp
  rw [mul_add, hexpand]
  ring

/-- A disc around `iθ₀`, `θ₀` large, inside the upper half-plane, contains a given point of it. -/
theorem exists_disc_of_im_pos {w : ℂ} (hw : 0 < w.im) :
    ∃ θ₀ R R₂ : ℝ, 0 < θ₀ ∧ 0 < R ∧ R < R₂ ∧ R₂ < θ₀ ∧ ‖w - I * (θ₀ : ℂ)‖ < R := by
  set θ₀ := ‖w‖ ^ 2 / w.im + w.im + 1
  have hq : 0 ≤ ‖w‖ ^ 2 / w.im := by positivity
  have hθw : w.im < θ₀ := by simp only [θ₀]; linarith
  have hθ₀ : 0 < θ₀ := by linarith
  have hθA : ‖w‖ ^ 2 ≤ θ₀ * w.im := by
    have e : θ₀ * w.im = ‖w‖ ^ 2 + w.im ^ 2 + w.im := by
      simp only [θ₀]
      field_simp
    rw [e]
    nlinarith
  have hrad : 0 < θ₀ ^ 2 - w.im * θ₀ := by nlinarith
  set ρ₀ := Real.sqrt (θ₀ ^ 2 - w.im * θ₀)
  have hρ₀ : 0 < ρ₀ := Real.sqrt_pos.2 hrad
  have hρθ : ρ₀ < θ₀ := (Real.sqrt_lt' hθ₀).2 (by nlinarith)
  refine ⟨θ₀, (ρ₀ + θ₀) / 2, ((ρ₀ + θ₀) / 2 + θ₀) / 2, hθ₀, by linarith, by linarith, by linarith, ?_⟩
  have hsq1 : ‖w‖ ^ 2 = w.re ^ 2 + w.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  have hsq2 : ‖w - I * (θ₀ : ℂ)‖ ^ 2 = w.re ^ 2 + (w.im - θ₀) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [sub_re, sub_im, mul_re, mul_im, I_re, I_im, ofReal_re, ofReal_im, zero_mul, one_mul,
      zero_add, sub_zero, mul_zero]
    ring
  have hle : ‖w - I * (θ₀ : ℂ)‖ ^ 2 ≤ θ₀ ^ 2 - w.im * θ₀ := by
    rw [hsq2]
    nlinarith
  have h1 := (le_abs_self _).trans (Real.abs_le_sqrt hle)
  linarith

/-- **From the exterior transform to the real roots.** -/
theorem tendsto_real_of_exterior {M : ℕ → Multiset ℂ} {θ₀ R : ℝ} (hθ₀ : 0 < θ₀) (hRθ : R < θ₀)
    {w : ℂ} (hw : ‖w - I * (θ₀ : ℂ)‖ < R)
    (hext : Tendsto (fun d : ℕ => (1 / (d : ℂ)) *
      (((M d).filter fun y => R ≤ ‖I * (θ₀ : ℂ) - y‖).map fun y => 1 / (w - y)).sum)
      atTop (𝓝 (1 / (w + I))))
    (hnon : Tendsto (fun d : ℕ => (Multiset.card ((M d).filter fun y => ¬ y.im = 0) : ℝ) / d)
      atTop (𝓝 0)) :
    Tendsto (fun d : ℕ => (1 / (d : ℂ)) *
      (((M d).filter fun y => y.im = 0).map fun y => 1 / (w - y)).sum)
      atTop (𝓝 (1 / (w + I))) := by
  have hδ : 0 < R - ‖w - I * (θ₀ : ℂ)‖ := by linarith
  have hsmall := hnon.mul_const (1 / (R - ‖w - I * (θ₀ : ℂ)‖))
  rw [zero_mul] at hsmall
  have hlim := (tendsto_iff_norm_sub_tendsto_zero.1 hext).add hsmall
  rw [add_zero] at hlim
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hlim
  filter_upwards [eventually_gt_atTop 0] with d hd
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  set c := I * (θ₀ : ℂ)
  set N := M d
  set p : ℂ → Prop := fun y => R ≤ ‖c - y‖
  have hrealext : (N.filter fun y => y.im = 0) = ((N.filter p).filter fun y => y.im = 0) := by
    rw [Multiset.filter_filter]
    refine Multiset.filter_congr fun y _ => ?_
    constructor
    · intro hy
      refine ⟨hy, ?_⟩
      have him : (c - y).im = θ₀ := by
        simp [c, hy]
      have h1 := Complex.abs_im_le_norm (c - y)
      rw [him, abs_of_pos hθ₀] at h1
      show R ≤ ‖c - y‖
      linarith
    · exact fun h => h.1
  have hsplit := multiset_sum_filter_split (N.filter p) (fun y => y.im = 0) (fun y => 1 / (w - y))
  rw [← hrealext] at hsplit
  set Sᵣ := ((N.filter fun y => y.im = 0).map fun y => 1 / (w - y)).sum
  set Sₙ := (((N.filter p).filter fun y => ¬ y.im = 0).map fun y => 1 / (w - y)).sum
  set Sₑ := ((N.filter p).map fun y => 1 / (w - y)).sum
  have hkernel : ∀ y ∈ (N.filter p).filter (fun y => ¬ y.im = 0),
      ‖1 / (w - y)‖ ≤ 1 / (R - ‖w - c‖) := fun y hy => by
    have hyR : R ≤ ‖c - y‖ := (Multiset.mem_filter.1 (Multiset.mem_filter.1 hy).1).2
    rw [norm_div, norm_one]
    refine one_div_le_one_div_of_le hδ ?_
    have h1 := norm_sub_norm_le (c - y) (c - w)
    rw [show c - y - (c - w) = w - y by ring, norm_sub_rev c w] at h1
    linarith
  have hSn := norm_multiset_sum_map_le _ _ hkernel
  have hcardn : (Multiset.card ((N.filter p).filter fun y => ¬ y.im = 0) : ℝ) ≤
      (Multiset.card (N.filter fun y => ¬ y.im = 0) : ℝ) := by
    exact_mod_cast Multiset.card_le_card
      (Multiset.monotone_filter_left _ (Multiset.filter_le _ _))
  have hid : (1 / (d : ℂ)) * Sᵣ - 1 / (w + I) = ((1 / (d : ℂ)) * Sₑ - 1 / (w + I)) -
      (1 / (d : ℂ)) * Sₙ := by
    rw [hsplit]
    ring
  rw [hid]
  refine (norm_sub_le _ _).trans (add_le_add le_rfl ?_)
  have hbound : ‖Sₙ‖ ≤ (Multiset.card (N.filter fun y => ¬ y.im = 0) : ℝ) * (1 / (R - ‖w - c‖)) :=
    hSn.trans (mul_le_mul_of_nonneg_right hcardn (by positivity))
  have hn : ‖(1 / (d : ℂ)) * Sₙ‖ = ‖Sₙ‖ / d := by
    rw [norm_mul, norm_div, norm_one, Complex.norm_natCast]
    ring
  rw [hn]
  calc ‖Sₙ‖ / d ≤ _ := div_le_div_of_nonneg_right hbound hdR.le
    _ = _ := by ring

/-! ## Hyperbolic kernels -/

variable {g : ℝ → ℝ}

/-- The rescaled roots `x/ℓ_d` of `R_d`. -/
def kernelRoots (g : ℝ → ℝ) (d : ℕ) : Multiset ℂ :=
  (kernelJensen g d).roots.map fun x => x / (cauchyScale d : ℂ)

theorem HyperbolicKernel.card_kernelRoots (hg : HyperbolicKernel g) (d : ℕ) :
    Multiset.card (kernelRoots g d) = d := by
  rw [kernelRoots, Multiset.card_map, card_roots_momentJensen hg.kernelMoment_zero_pos.ne']

theorem HyperbolicKernel.eval_kernelJensen_eq_prod (hg : HyperbolicKernel g) (d : ℕ)
    (hℓ : cauchyScale d ≠ 0) (z : ℂ) :
    (kernelJensen g d).eval ((cauchyScale d : ℂ) * z) =
      (kernelMoment g 0 : ℂ) * (cauchyScale d : ℂ) ^ d *
        ((kernelRoots g d).map fun y => z - y).prod := by
  have hℓ' : (cauchyScale d : ℂ) ≠ 0 := ofReal_ne_zero.2 hℓ
  have hμ := hg.kernelMoment_zero_pos.ne'
  conv_lhs => rw [(IsAlgClosed.splits (kernelJensen g d)).eq_prod_roots]
  rw [leadingCoeff_momentJensen hμ, eval_mul, eval_C, eval_multiset_prod, Multiset.map_map,
    kernelRoots, Multiset.map_map]
  have := multiset_prod_mul_sub (kernelJensen g d).roots hℓ' z
  rw [card_roots_momentJensen hμ] at this
  simp only [Function.comp_def, eval_sub, eval_X, eval_C]
  rw [this, mul_assoc]

/-- `|x − iv| ≤ |x + iv|` for `v ≥ 0`, `Im x ≥ 0`. -/
theorem norm_sub_I_mul_le {x : ℂ} (hx : 0 ≤ x.im) {v : ℝ} (hv : 0 ≤ v) :
    ‖x + I * ((-v : ℝ) : ℂ)‖ ≤ ‖x + I * (v : ℂ)‖ := by
  rw [Complex.norm_eq_sqrt_sq_add_sq, Complex.norm_eq_sqrt_sq_add_sq]
  apply Real.sqrt_le_sqrt
  simp only [add_re, add_im, mul_re, mul_im, ofReal_re, ofReal_im, I_re, I_im, zero_mul, one_mul,
    zero_add, sub_zero, add_zero]
  nlinarith [mul_nonneg hx hv]

/-- The whole-line integral is twice a half-line bound, on `Im x ≥ 0`. -/
theorem HyperbolicKernel.norm_eval_kernelJensen_le (hg : HyperbolicKernel g) (d : ℕ) {x : ℂ}
    (hx : 0 ≤ x.im) :
    ‖(kernelJensen g d).eval x‖ ≤ 2 * ∫ v in Set.Ioi (0 : ℝ), g v * ‖x + I * v‖ ^ d := by
  set f : ℝ → ℂ := fun v => (g v : ℂ) * (x + I * v) ^ d
  have hf : Integrable f := hg.integrable_mul_add_I_pow d x
  have hsplit := intervalIntegral.integral_Iic_add_Ioi (f := f) (b := 0)
    hf.integrableOn hf.integrableOn
  have hG := hg.integrable_mul_norm_pow d x
  have h1 : ‖∫ v in Set.Ioi (0 : ℝ), f v‖ ≤ ∫ v in Set.Ioi (0 : ℝ), g v * ‖x + I * v‖ ^ d := by
    refine (norm_integral_le_integral_norm _).trans_eq ?_
    refine integral_congr_ae (Eventually.of_forall fun v => ?_)
    simp only [f]
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg (hg.nonneg v)]
  have h2 : ‖∫ v in Set.Iic (0 : ℝ), f v‖ ≤ ∫ v in Set.Ioi (0 : ℝ), g v * ‖x + I * v‖ ^ d := by
    have h := integral_comp_neg_Ioi (0 : ℝ) f
    rw [neg_zero] at h
    rw [← h]
    refine norm_integral_le_of_norm_le hG.restrict
      ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun v hv => ?_))
    have hv0 : (0 : ℝ) < v := hv
    simp only [f]
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg (hg.nonneg _), hg.even v]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _)
      (norm_sub_I_mul_le hx hv0.le) d) (hg.nonneg v)
  rw [hg.eval_kernelJensen, ← hsplit]
  refine (norm_add_le _ _).trans ?_
  linarith

/-- The whole-line mass `m_d(t) = ∫ g(v)(t + v)^d dv`. -/
def kernelMass (g : ℝ → ℝ) (d : ℕ) (t : ℝ) : ℝ := ∫ v : ℝ, g v * (t + v) ^ d

theorem HyperbolicKernel.eval_kernelJensen_I_mul (hg : HyperbolicKernel g) (d : ℕ) (t : ℝ) :
    (kernelJensen g d).eval (I * t) = I ^ d * (kernelMass g d t : ℂ) := by
  rw [hg.eval_kernelJensen, kernelMass, ← integral_complex_ofReal, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun v => ?_)
  beta_reduce
  rw [show I * (t : ℂ) + I * v = I * ((t + v : ℝ) : ℂ) by push_cast; ring, mul_pow]
  push_cast
  ring

theorem integral_kernel_reflect_general (hg : HyperbolicKernel g) (t : ℝ) (n : ℕ) :
    ∫ x : ℝ, g x * (t - x) ^ n = ∫ x : ℝ, g x * (t + x) ^ n := by
  have := integral_neg_eq_self (fun x : ℝ => g x * (t + x) ^ n) volume
  rw [← this]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [hg.even x, sub_eq_add_neg]

/-- `m_{d+1}(t) ≥ (t + v)^d exp(−A e^{2(v+1)})`, by pairing `v` with `−v`. -/
theorem HyperbolicKernel.exists_kernelMass_ge (hg : HyperbolicKernel g) :
    ∃ A v₁ : ℝ, 0 < A ∧ 1 ≤ v₁ ∧ ∀ (d : ℕ) (t v : ℝ), 1 ≤ t → v₁ ≤ v →
      (t + v) ^ d * Real.exp (-(A * Real.exp (2 * (v + 1)))) ≤ kernelMass g (d + 1) t := by
  obtain ⟨A, v₀, hA, hlow⟩ := hg.lower
  refine ⟨A, max v₀ 1, hA, le_max_right _ _, fun d t v ht hv => ?_⟩
  have hv0 : v₀ ≤ v := (le_max_left _ _).trans hv
  have hv1 : 1 ≤ v := (le_max_right _ _).trans hv
  set c₀ := (t + v) ^ d * Real.exp (-(A * Real.exp (2 * (v + 1))))
  have hc₀ : 0 ≤ c₀ := by
    have : 0 ≤ t + v := by linarith
    positivity
  have hint := hg.integrable_mul_add_pow t (d + 1)
  set S : ℝ → ℝ := fun x => g x * ((t + x) ^ (d + 1) + (t - x) ^ (d + 1))
  have hS0 : ∀ x, 0 ≤ S x := fun x => by
    have h := reflected_pow_nonneg le_rfl (by linarith : 0 ≤ t) (d + 1) x
    simp only [zero_mul, neg_zero, Real.exp_zero, one_mul] at h
    exact mul_nonneg (hg.nonneg x) h
  have hint2 : Integrable fun x : ℝ => g x * (t - x) ^ (d + 1) := by
    have h := hint.comp_neg
    refine h.congr (Eventually.of_forall fun x => ?_)
    simp only [hg.even x, sub_eq_add_neg]
  have hSint : Integrable S := by
    refine (hint.add hint2).congr (Eventually.of_forall fun x => ?_)
    simp only [S, Pi.add_apply]
    ring
  have htwo : ∫ x, S x = 2 * kernelMass g (d + 1) t := by
    have hrefl := integral_kernel_reflect_general hg t (d + 1)
    have h1 : ∫ x, S x = (∫ x, g x * (t + x) ^ (d + 1)) + ∫ x, g x * (t - x) ^ (d + 1) := by
      rw [← integral_add hint hint2]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp only [S]
      ring
    rw [h1, hrefl, kernelMass]
    ring
  have hlowS : ∀ x ∈ Set.Icc v (v + 1), 2 * c₀ ≤ S x := fun x hx => by
    have hx1 : 1 ≤ x := hv1.trans hx.1
    have hgx : Real.exp (-(A * Real.exp (2 * (v + 1)))) ≤ g x := by
      refine le_trans (Real.exp_le_exp.2 ?_) (hlow x (hv0.trans hx.1))
      have : Real.exp (2 * x) ≤ Real.exp (2 * (v + 1)) := Real.exp_le_exp.2 (by linarith [hx.2])
      nlinarith
    have hA' : 0 ≤ t + x := by linarith
    have hB' : |t - x| ≤ t + x - 2 := abs_le.2 ⟨by linarith, by linarith⟩
    have hpow1 : (t + v) ^ d ≤ (t + x) ^ d := pow_le_pow_left₀ (by linarith) (by linarith [hx.1]) d
    have hbpow : |t - x| ^ (d + 1) ≤ (t + x) ^ d * (t + x - 2) := by
      rw [pow_succ]
      exact mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) (by linarith) d) hB' (abs_nonneg _)
        (pow_nonneg hA' d)
    have hneg : -|t - x| ^ (d + 1) ≤ (t - x) ^ (d + 1) := by
      have := neg_abs_le ((t - x) ^ (d + 1))
      rwa [abs_pow] at this
    have hsum : 2 * (t + v) ^ d ≤ (t + x) ^ (d + 1) + (t - x) ^ (d + 1) := by
      have e3 : (t + x) ^ (d + 1) = (t + x) ^ d * (t + x) := pow_succ _ _
      nlinarith
    have hmul := mul_le_mul hgx hsum (by positivity) (hg.nonneg x)
    simp only [S, c₀]
    nlinarith [hmul]
  have hset : ∫ _x in Set.Icc v (v + 1), 2 * c₀ ≤ ∫ x in Set.Icc v (v + 1), S x :=
    setIntegral_mono_on continuousOn_const.integrableOn_Icc hSint.integrableOn measurableSet_Icc
      hlowS
  have hconst : ∫ _x in Set.Icc v (v + 1), 2 * c₀ = 2 * c₀ := by simp
  have hfull : ∫ x in Set.Icc v (v + 1), S x ≤ ∫ x, S x :=
    setIntegral_le_integral hSint (Eventually.of_forall hS0)
  rw [hconst] at hset
  linarith

/-- At the centre, `μ₀ ℓ^d Π_y |iθ₀ − y| = m_d(θ₀ℓ)`. -/
theorem HyperbolicKernel.prod_norm_kernel_center (hg : HyperbolicKernel g) {θ₀ : ℝ} {d : ℕ}
    (hℓ : 0 < cauchyScale d) (hm : 0 ≤ kernelMass g d (θ₀ * cauchyScale d)) :
    kernelMoment g 0 * cauchyScale d ^ d * ((kernelRoots g d).map fun y => ‖I * (θ₀ : ℂ) - y‖).prod =
      kernelMass g d (θ₀ * cauchyScale d) := by
  have h := hg.eval_kernelJensen_eq_prod d hℓ.ne' (I * (θ₀ : ℂ))
  have harg : (cauchyScale d : ℂ) * (I * (θ₀ : ℂ)) = I * ((θ₀ * cauchyScale d : ℝ) : ℂ) := by
    push_cast
    ring
  rw [harg, hg.eval_kernelJensen_I_mul] at h
  have hn := congrArg norm h
  rw [norm_mul, norm_pow, Complex.norm_I, one_pow, one_mul, Complex.norm_real,
    Real.norm_of_nonneg hm, norm_mul, norm_mul, norm_pow, Complex.norm_real, Complex.norm_real,
    Real.norm_of_nonneg hℓ.le, Real.norm_of_nonneg hg.kernelMoment_zero_pos.le,
    norm_multiset_prod_map] at hn
  exact hn.symm

/-- On circles around `iθ₀` of radius `R < θ₀`:
`|Π_y (z − y)| ≤ 2(e^{E_d} + c⁺₀)/μ₀ · |z + i|^d`, uniformly, for large `d`. -/
theorem HyperbolicKernel.eventually_kernel_sphere_bound (hg : HyperbolicKernel g) {θ₀ R : ℝ}
    (hθ₀ : 0 < θ₀) (hR : 0 < R) (hRθ : R < θ₀) :
    ∀ᶠ d : ℕ in atTop, ∀ z ∈ sphere (I * (θ₀ : ℂ)) R,
      ‖((kernelRoots g d).map fun y => z - y).prod‖ ≤
        2 * (Real.exp (halfError d) + halfMoment g 0) / kernelMoment g 0 * ‖z + I‖ ^ d := by
  have hμ := hg.kernelMoment_zero_pos
  filter_upwards [hg.eventually_setIntegral_norm_le hθ₀ hR (by linarith),
    tendsto_cauchyScale.eventually_gt_atTop 0] with d hbound hℓ z hzs
  have hzim : 0 ≤ z.im := by
    have h := Complex.abs_im_le_norm (z - I * (θ₀ : ℂ))
    rw [mem_sphere_iff_norm.1 hzs] at h
    have h2 := (abs_le.1 h).1
    simp only [sub_im, mul_im, I_re, I_im, ofReal_re, ofReal_im, zero_mul, one_mul, zero_add] at h2
    linarith
  have hprod := hg.eval_kernelJensen_eq_prod d hℓ.ne' z
  have hnormeval : ‖(kernelJensen g d).eval ((cauchyScale d : ℂ) * z)‖ =
      kernelMoment g 0 * cauchyScale d ^ d * ‖((kernelRoots g d).map fun y => z - y).prod‖ := by
    rw [hprod, norm_mul, norm_mul, norm_pow, Complex.norm_real, Complex.norm_real,
      Real.norm_of_nonneg hℓ.le, Real.norm_of_nonneg hμ.le]
  have hxim : 0 ≤ ((cauchyScale d : ℂ) * z).im := by
    simpa using mul_nonneg hℓ.le hzim
  have hle := hg.norm_eval_kernelJensen_le d hxim
  rw [hnormeval] at hle
  have hℓd' : 0 < cauchyScale d ^ d := pow_pos hℓ d
  have hmain : cauchyScale d ^ d * (kernelMoment g 0 * ‖((kernelRoots g d).map fun y => z - y).prod‖) ≤
      cauchyScale d ^ d * (2 * (Real.exp (halfError d) + halfMoment g 0) * ‖z + I‖ ^ d) := by
    calc _ = kernelMoment g 0 * cauchyScale d ^ d * ‖((kernelRoots g d).map fun y => z - y).prod‖ := by
          ring
      _ ≤ 2 * ∫ v in Set.Ioi (0 : ℝ), g v * ‖(cauchyScale d : ℂ) * z + I * v‖ ^ d := hle
      _ ≤ 2 * (cauchyScale d ^ d * (‖z + I‖ ^ d * (Real.exp (halfError d) + halfMoment g 0))) :=
          mul_le_mul_of_nonneg_left (hbound z hzs) (by norm_num)
      _ = _ := by ring
  have hfin := le_of_mul_le_mul_left hmain hℓd'
  rw [div_mul_eq_mul_div, le_div_iff₀ hμ]
  linarith

/-- The error sequence of the kernel data. -/
def kernelError (g : ℝ → ℝ) (θ₀ A : ℝ) (d : ℕ) : ℝ :=
  Real.log (2 * (1 + halfMoment g 0)) + halfError d + (1 + θ₀) * cauchyScale d -
    d * Real.log (1 - Real.log (cauchyScale d) / cauchyScale d / (1 + θ₀)) +
      A * Real.exp 2 * (d * (1 / cauchyScale d) ^ 2)

theorem tendsto_kernelError_div (g : ℝ → ℝ) {θ₀ : ℝ} (hθ₀ : 0 < θ₀) (A : ℝ) :
    Tendsto (fun d : ℕ => kernelError g θ₀ A d / d) atTop (𝓝 0) := by
  have h1θ : 0 < 1 + θ₀ := by linarith
  have hu : Tendsto (fun d : ℕ => 1 - Real.log (cauchyScale d) / cauchyScale d / (1 + θ₀)) atTop
      (𝓝 1) := by
    have := (tendsto_log_cauchyScale_div.div_const (1 + θ₀)).const_sub 1
    simpa using this
  have hlogu := (Real.continuousAt_log one_ne_zero).tendsto.comp hu
  rw [Real.log_one] at hlogu
  have hsum := (((tendsto_halfError_div (Real.log (2 * (1 + halfMoment g 0)))).add
    (tendsto_cauchyScale_div.const_mul (1 + θ₀))).sub hlogu).add
    ((tendsto_one_div_cauchyScale.pow 2).const_mul (A * Real.exp 2))
  have hzero : (0 : ℝ) + (1 + θ₀) * 0 - 0 + A * Real.exp 2 * 0 ^ 2 = 0 := by ring
  rw [hzero] at hsum
  refine hsum.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with d hd
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  simp only [kernelError, Function.comp_apply]
  field_simp

/-- The bound on `log(B_d (1 + θ₀)^d/P_d)` for the kernel data. -/
theorem HyperbolicKernel.exists_eventually_log_le (hg : HyperbolicKernel g) {θ₀ : ℝ} (hθ₀ : 0 < θ₀) :
    ∃ A : ℝ, ∀ᶠ d : ℕ in atTop, 0 < kernelMass g d (θ₀ * cauchyScale d) ∧
      Real.log (2 * (Real.exp (halfError d) + halfMoment g 0) / kernelMoment g 0 * (1 + θ₀) ^ d /
        (kernelMass g d (θ₀ * cauchyScale d) / (kernelMoment g 0 * cauchyScale d ^ d))) ≤
        kernelError g θ₀ A d := by
  obtain ⟨A, v₁, hA, hv₁, hmass⟩ := hg.exists_kernelMass_ge
  refine ⟨A, ?_⟩
  have hc₀ := hg.halfMoment_zero_pos
  have hμ := hg.kernelMoment_zero_pos
  have h1θ : 0 < 1 + θ₀ := by linarith
  filter_upwards [eventually_halfError_nonneg, tendsto_cauchyScale.eventually_ge_atTop (2 * v₁),
    tendsto_cauchyScale.eventually_ge_atTop (1 / θ₀), eventually_gt_atTop 0] with d hE hℓ2 hℓθ hd
  obtain ⟨D, rfl⟩ : ∃ D, d = D + 1 := ⟨d - 1, by omega⟩
  have hdR : (0 : ℝ) < ((D + 1 : ℕ) : ℝ) := by positivity
  have hdef : kernelError g θ₀ A (D + 1) = Real.log (2 * (1 + halfMoment g 0)) + halfError (D + 1) +
      (1 + θ₀) * cauchyScale (D + 1) -
      ((D + 1 : ℕ) : ℝ) * Real.log (1 - Real.log (cauchyScale (D + 1)) / cauchyScale (D + 1) / (1 + θ₀)) +
      A * Real.exp 2 * (((D + 1 : ℕ) : ℝ) * (1 / cauchyScale (D + 1)) ^ 2) := rfl
  set ℓ := cauchyScale (D + 1)
  have hℓ : 0 < ℓ := by linarith
  have ht1 : 1 ≤ θ₀ * ℓ := by
    rw [div_le_iff₀ hθ₀] at hℓθ
    linarith
  have hlogℓ : Real.log ℓ ≤ ℓ / 2 := by
    have h := Real.log_le_sub_one_of_pos (x := ℓ / 2) (by positivity)
    rw [Real.log_div hℓ.ne' two_ne_zero] at h
    have := Real.log_two_lt_d9
    linarith
  have hlogℓ0 : 0 ≤ Real.log ℓ := Real.log_nonneg (by linarith)
  set v := ℓ - Real.log ℓ
  have hv1 : v₁ ≤ v := by simp only [v]; linarith
  have hv0 : 0 < v := by linarith
  have hge := hmass D (θ₀ * ℓ) v ht1 hv1
  set m := kernelMass g (D + 1) (θ₀ * ℓ)
  set X := θ₀ * ℓ + v
  have hX : 0 < X := by positivity
  have hmpos : 0 < m := lt_of_lt_of_le (by positivity) hge
  refine ⟨hmpos, ?_⟩
  have hexp : Real.exp (2 * (v + 1)) = Real.exp 2 * (((D + 1 : ℕ) : ℝ) * (1 / ℓ) ^ 2) := by
    have hd2 : Real.exp (2 * ℓ) = ((D + 1 : ℕ) : ℝ) := by
      rw [show 2 * ℓ = Real.log ((D + 1 : ℕ) : ℝ) by simp only [ℓ, cauchyScale]; ring,
        Real.exp_log hdR]
    have hl : Real.exp (-(2 * Real.log ℓ)) = (1 / ℓ) ^ 2 := by
      rw [show -(2 * Real.log ℓ) = Real.log ((1 / ℓ) ^ 2) by
        rw [Real.log_pow, one_div, Real.log_inv]
        push_cast
        ring, Real.exp_log (by positivity)]
    rw [show 2 * (v + 1) = 2 + (2 * ℓ + -(2 * Real.log ℓ)) by simp only [v]; ring, Real.exp_add,
      Real.exp_add, hd2, hl]
  have hlogm := Real.log_le_log (by positivity) hge
  rw [Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_pow, Real.log_exp, hexp] at hlogm
  have hXeq : X = (1 + θ₀) * ℓ * (1 - Real.log ℓ / ℓ / (1 + θ₀)) := by
    simp only [X, v]
    field_simp
    ring
  have hu0 : 0 < 1 - Real.log ℓ / ℓ / (1 + θ₀) := by
    have h := hX
    rw [hXeq] at h
    exact (pos_iff_pos_of_mul_pos h).1 (by positivity)
  have hlogX : Real.log X = Real.log (1 + θ₀) + Real.log ℓ +
      Real.log (1 - Real.log ℓ / ℓ / (1 + θ₀)) := by
    rw [hXeq, Real.log_mul (by positivity) hu0.ne', Real.log_mul h1θ.ne' hℓ.ne']
  have hlogXle : Real.log X ≤ (1 + θ₀) * ℓ := by
    have h := Real.log_le_sub_one_of_pos hX
    simp only [X, v] at h ⊢
    nlinarith
  set E := halfError (D + 1)
  have hratio : 2 * (Real.exp E + halfMoment g 0) / kernelMoment g 0 * (1 + θ₀) ^ (D + 1) /
      (m / (kernelMoment g 0 * ℓ ^ (D + 1))) =
      2 * (Real.exp E + halfMoment g 0) * ((1 + θ₀) ^ (D + 1) * ℓ ^ (D + 1)) / m := by
    field_simp
  have hle2 : 2 * (Real.exp E + halfMoment g 0) * ((1 + θ₀) ^ (D + 1) * ℓ ^ (D + 1)) / m ≤
      2 * (1 + halfMoment g 0) * Real.exp E * ((1 + θ₀) ^ (D + 1) * ℓ ^ (D + 1)) / m := by
    have h1 := exp_add_le_of_nonneg hE hc₀.le
    rw [show 2 * (1 + halfMoment g 0) * Real.exp E * ((1 + θ₀) ^ (D + 1) * ℓ ^ (D + 1)) / m =
      2 * ((1 + halfMoment g 0) * Real.exp E) * ((1 + θ₀) ^ (D + 1) * ℓ ^ (D + 1)) / m by ring]
    gcongr
  rw [hratio]
  refine (Real.log_le_log (by positivity) hle2).trans ?_
  have h2c : 0 < 2 * (1 + halfMoment g 0) := by positivity
  have hT1 : (1 + θ₀) ^ (D + 1) ≠ 0 := by positivity
  have hT2 : ℓ ^ (D + 1) ≠ 0 := by positivity
  have hlogsplit : Real.log (2 * (1 + halfMoment g 0) * Real.exp E *
      ((1 + θ₀) ^ (D + 1) * ℓ ^ (D + 1)) / m) = Real.log (2 * (1 + halfMoment g 0)) + E +
        ((D + 1 : ℕ) : ℝ) * Real.log (1 + θ₀) + ((D + 1 : ℕ) : ℝ) * Real.log ℓ - Real.log m := by
    rw [Real.log_div (by positivity) hmpos.ne',
      Real.log_mul (x := 2 * (1 + halfMoment g 0) * Real.exp E) (by positivity) (mul_ne_zero hT1 hT2),
      Real.log_mul (x := 2 * (1 + halfMoment g 0)) h2c.ne' (Real.exp_pos _).ne', Real.log_exp,
      Real.log_mul hT1 hT2, Real.log_pow, Real.log_pow]
    ring
  rw [hlogsplit, hdef]
  rw [hlogX] at hlogm hlogXle
  push_cast at hlogm ⊢
  nlinarith

/-- **The Cauchy law of the real roots for every hyperbolic kernel.** -/
theorem HyperbolicKernel.tendsto_real_cauchy (hg : HyperbolicKernel g) {w : ℂ} (hw : 0 < w.im) :
    Tendsto (fun d : ℕ => (1 / (d : ℂ)) *
      (((kernelRoots g d).filter fun y => y.im = 0).map fun y => 1 / (w - y)).sum)
      atTop (𝓝 (1 / (w + I))) := by
  obtain ⟨θ₀, R, R₂, hθ₀, hR, hRR₂, hR₂θ, hwc⟩ := exists_disc_of_im_pos hw
  have hRθ : R < θ₀ := by linarith
  have hμ := hg.kernelMoment_zero_pos
  obtain ⟨A, hAev⟩ := hg.exists_eventually_log_le hθ₀
  set B : ℕ → ℝ := fun d => 2 * (Real.exp (halfError d) + halfMoment g 0) / kernelMoment g 0
  set P : ℕ → ℝ := fun d => kernelMass g d (θ₀ * cauchyScale d) / (kernelMoment g 0 * cauchyScale d ^ d)
  have hP : ∀ᶠ d : ℕ in atTop, 0 < P d ∧ P d ≤
      ((kernelRoots g d).map fun y => ‖I * (θ₀ : ℂ) - y‖).prod := by
    filter_upwards [hAev, tendsto_cauchyScale.eventually_gt_atTop 0] with d hd hℓ
    have hcenter := hg.prod_norm_kernel_center (θ₀ := θ₀) hℓ hd.1.le
    have hden : 0 < kernelMoment g 0 * cauchyScale d ^ d := by positivity
    refine ⟨div_pos hd.1 hden, ?_⟩
    simp only [P]
    rw [div_le_iff₀ hden, ← hcenter]
    exact le_of_eq (by ring)
  have hL : ∀ᶠ d : ℕ in atTop, Real.log (B d * (1 + θ₀) ^ d / P d) ≤ kernelError g θ₀ A d := by
    filter_upwards [hAev] with d hd using hd.2
  have herr := tendsto_kernelError_div g hθ₀ A
  have hnear := tendsto_card_near_of_data (M := kernelRoots g) hg.card_kernelRoots hR hRR₂
    (by linarith) (hg.eventually_kernel_sphere_bound hθ₀ (by linarith) hR₂θ) hP hL herr
  have hext := tendsto_exterior_of_data (M := kernelRoots g) hg.card_kernelRoots hθ₀ hR (by linarith)
    hwc (hg.eventually_kernel_sphere_bound hθ₀ hR hRθ) hP hL herr hnear
  refine tendsto_real_of_exterior hθ₀ hRθ hwc hext ?_
  refine hg.tendsto_card_nonreal_roots_div.congr' ?_
  filter_upwards [tendsto_cauchyScale.eventually_gt_atTop 0] with d hℓ
  congr 2
  rw [kernelRoots, Multiset.filter_map, Multiset.card_map]
  congr 1
  refine Multiset.filter_congr fun x _ => ?_
  simp only [Function.comp_apply, Complex.div_ofReal_im, div_eq_zero_iff, hℓ.ne', or_false]

/-- **The backward heat flow has the same bulk as `Ξ`.** For every `τ ≥ 0` the real rescaled roots of
`R_d(H_{−τ})` follow the Cauchy law, although `H_{−τ}` has non-real zeros for `τ > 0`. -/
theorem tendsto_real_cauchy_riemannHeat_neg {τ : ℝ} (hτ : 0 ≤ τ) {w : ℂ} (hw : 0 < w.im) :
    Tendsto (fun d : ℕ => (1 / (d : ℂ)) *
      (((kernelRoots (fun x => riemannKernelReal x * Real.exp (-τ * x ^ 2)) d).filter
        fun y => y.im = 0).map fun y => 1 / (w - y)).sum) atTop (𝓝 (1 / (w + I))) :=
  (hyperbolicKernel_heat hτ).tendsto_real_cauchy hw

end

end FiniteFreeProbability

#print axioms FiniteFreeProbability.HyperbolicKernel.tendsto_real_cauchy
#print axioms FiniteFreeProbability.tendsto_real_cauchy_riemannHeat_neg
