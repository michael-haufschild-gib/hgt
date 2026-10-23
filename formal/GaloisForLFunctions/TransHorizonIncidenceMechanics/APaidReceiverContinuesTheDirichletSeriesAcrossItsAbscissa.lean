import GaloisForLFunctions.TransHorizonIncidenceMechanics.CriticalWienerKernelsRepairAPositiveDriftOnlyAtItsPole
import GaloisForLFunctions.TransHorizonIncidenceMechanics.TheHalfDampedReceiverReadsTheDirichletSeriesAtTheCriticalPoint

/-!
# A paid receiver continues the Dirichlet series across its abscissa

Let `c` be a weight with `Σ_d |c(d)| d^{-θ} < ∞` for every `θ > a`, put `m = Σ c(d)/d`, let `A(n)` be
its centred prefix and `C(σ) = Σ c(d) d^{-σ}`. If the receiver of `c` is paid, every pronic energy
`Σ_{n ≤ T} A(n)²/(n(n+1))` at most `E`, then:

* the complex Mellin pairing `Φ(s) = Σ_n A(n)(n^{-s} − (n+1)^{-s})` is holomorphic on `Re s > 1/2`
  (`differentiableOn_complexMellinPairing`): `|n^{-s} − (n+1)^{-s}| ≤ |s| n^{-Re s − 1}`, and Cauchy–Schwarz
  against the energy makes the series locally uniformly absolutely convergent;
* `Φ(σ) = ζ(σ)(C(σ) − m)` on `a < σ < 1` (`complexMellinPairing_eq_zeta_mul`).

So `ζ(s)(C(s) − m)` continues holomorphically from `Re s > a` to `Re s > 1/2`
(`exists_holomorphic_continuation`), and `C − m = Φ/ζ` meromorphically, with poles only at zeros of
`ζ`. For `1/2 < a < 1` the abscissa lies inside that half-plane and `ζ(a) ≠ 0`, so `Φ/ζ` is analytic
at `a`. Two consequences, against the boundedness given by the pole law:

* **Lipschitz at the abscissa** (`exists_abs_dirichletSeries_sub_le_mul`): `C(σ) → L` and
  `|C(σ) − L| ≤ M (σ − a)` near `a`.
* **Integral order at the abscissa** (`exists_nat_eq_of_rpow_bounds_at_abscissa`): if
  `|C(a + u) − L| ≍ u^α` with `α > 0`, then `α` is a positive integer, the order of vanishing of
  the analytic function `Φ/ζ − Φ(a)/ζ(a)` at `a`.

**Quantization of the prime mean.** Let `f` be completely multiplicative with `|f(p)| ≤ 1` and
logarithmic prime mean `ν`: `Σ_p f(p) p^{-w} = ν log(1/(w − 1)) + O(1)`. The Euler product then
gives `Σ f(n) n^{-w} ≍ (w − 1)^{-ν}` (`tsum_pattern_mem_exp_primeSum`). At damping `0 < ε < 1/2` the
weight `f(d) d^{-ε}` has abscissa `1 − ε` and `C(1 − ε + u) = Σ f(n) n^{-1-u}`, so a paid weight has
`ν ∈ {0, −1}` (`not_receiverBounded_of_primeMean`). For `f = ±1` with flipped primes of density `ρ`
the mean is `ν = 1 − 2ρ`, so the flipped density of a paid pattern is `1/2` or `1`
(`not_receiverBounded_of_flippedDensity`). Below half damping the receiver reads the prime mean only
through the integer order of `Σ f(n) n^{-w}` at `w = 1`; at half damping the abscissa is the
boundary point `1/2` of the half-plane of holomorphy and only the growth bound
`O((σ − 1/2)^{-1/2})` survives.
-/

open Finset Filter Topology Asymptotics
open scoped BigOperators

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

noncomputable section
set_option autoImplicit false

/-! ### The complex Mellin pairing -/

/-- The complex Mellin cell `Δ_n(s) = n^{-s} − (n+1)^{-s}`. -/
def complexMellinCell (s : ℂ) (n : ℕ) : ℂ :=
  ((n : ℝ) : ℂ) ^ (-s) - (((n : ℝ) + 1 : ℝ) : ℂ) ^ (-s)

/-- The complex Mellin pairing `Φ(s) = Σ_n f(n) Δ_n(s)`. -/
def complexMellinPairing (f : ℕ → ℝ) (s : ℂ) : ℂ :=
  ∑' n : ℕ, (f n : ℂ) * complexMellinCell s n

/-- On the real axis the complex cell is the real cell. -/
theorem complexMellinCell_ofReal (σ : ℝ) (n : ℕ) :
    complexMellinCell σ n = ((mellinCell σ n : ℝ) : ℂ) := by
  rw [mellinCell, Complex.ofReal_sub, Complex.ofReal_cpow (Nat.cast_nonneg n),
    Complex.ofReal_cpow (by positivity : (0 : ℝ) ≤ (n : ℝ) + 1), Complex.ofReal_neg]
  rfl

/-- On the real axis the complex pairing is the real pairing. -/
theorem complexMellinPairing_ofReal (f : ℕ → ℝ) (σ : ℝ) :
    complexMellinPairing f σ = ((∑' n : ℕ, f n * mellinCell σ n : ℝ) : ℂ) := by
  rw [complexMellinPairing, Complex.ofReal_tsum]
  refine tsum_congr fun n => ?_
  rw [complexMellinCell_ofReal, Complex.ofReal_mul]

/-- `|n^{-s} − (n+1)^{-s}| ≤ |s| n^{-Re s − 1}` for `n ≥ 1`, `Re s > 0` (mean value theorem). -/
theorem norm_complexMellinCell_le {s : ℂ} (hs : 0 < s.re) {n : ℕ} (hn : 1 ≤ n) :
    ‖complexMellinCell s n‖ ≤ ‖s‖ * (n : ℝ) ^ (-s.re - 1) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hs0 : -s ≠ 0 := neg_ne_zero.mpr fun h => by
    rw [h, Complex.zero_re] at hs; exact lt_irrefl 0 hs
  have hderiv : ∀ x ∈ Set.Icc (n : ℝ) ((n : ℝ) + 1),
      HasDerivWithinAt (fun x : ℝ => (x : ℂ) ^ (-s)) (-s * (x : ℂ) ^ (-s - 1))
        (Set.Icc (n : ℝ) ((n : ℝ) + 1)) x := by
    intro x hx
    have hx0 : x ≠ 0 := (lt_of_lt_of_le hn0 hx.1).ne'
    have h := (RHTower.differentiableAt_ofReal_cpow_neg hs0 hx0).hasDerivAt
    rw [RHTower.deriv_ofReal_cpow_neg hs0 hx0] at h
    exact h.hasDerivWithinAt
  have hbound : ∀ x ∈ Set.Ico (n : ℝ) ((n : ℝ) + 1),
      ‖-s * (x : ℂ) ^ (-s - 1)‖ ≤ ‖s‖ * (n : ℝ) ^ (-s.re - 1) := by
    intro x hx
    have hx0 : 0 < x := lt_of_lt_of_le hn0 hx.1
    rw [norm_mul, norm_neg, Complex.norm_cpow_eq_rpow_re_of_pos hx0]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    have hre : (-s - 1).re = -s.re - 1 := by simp
    rw [hre]
    exact Real.rpow_le_rpow_of_nonpos hn0 hx.1 (by linarith)
  have h := norm_image_sub_le_of_norm_deriv_le_segment' hderiv hbound ((n : ℝ) + 1)
    ⟨by linarith, le_rfl⟩
  rw [show (n : ℝ) + 1 - n = 1 by ring, mul_one] at h
  rw [complexMellinCell, norm_sub_rev]
  exact h

/-- A sequence of bounded pronic energy is absolutely summable against `n^{-b-1}`, `b > 1/2`. -/
theorem summable_abs_mul_rpow_of_energy {b E : ℝ} (hb : 1 / 2 < b) {f : ℕ → ℝ} (hf0 : f 0 = 0)
    (hE : ∀ T, ∑ n ∈ Icc 1 T, f n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) ≤ E) :
    Summable (fun n => |f n| * (n : ℝ) ^ (-b - 1)) := by
  have hb0 : 0 < b := by linarith
  have hs := summable_mul_mellinCell_of_energy hb (f := fun n => |f n|) (by simp [hf0])
    (fun T => by simpa only [sq_abs] using hE T)
  refine (hs.mul_left (2 ^ (b + 1) / b)).of_nonneg_of_le (fun n => by positivity) fun n => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [hf0]
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  -- `b (n+1)^{-b-1} ≤ Δ_n(b)` and `(2n)^{-b-1} ≤ (n+1)^{-b-1}`
  have hcell := (mellinCell_bounds hb0 hn).1
  have h2 : (2 : ℝ) ^ (-b - 1) * (n : ℝ) ^ (-b - 1) ≤ ((n : ℝ) + 1) ^ (-b - 1) := by
    rw [← Real.mul_rpow (by norm_num) hn0.le]
    exact Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by linarith)
  have h2' : (2 : ℝ) ^ (b + 1) * (2 : ℝ) ^ (-b - 1) = 1 := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2), show b + 1 + (-b - 1) = 0 by ring,
      Real.rpow_zero]
  have h3 : (2 : ℝ) ^ (-b - 1) * (n : ℝ) ^ (-b - 1) ≤ mellinCell b n / b := by
    rw [le_div_iff₀ hb0]
    calc (2 : ℝ) ^ (-b - 1) * (n : ℝ) ^ (-b - 1) * b ≤ b * ((n : ℝ) + 1) ^ (-b - 1) := by
          have := mul_le_mul_of_nonneg_left h2 hb0.le
          linarith
      _ ≤ mellinCell b n := hcell
  have h2pos : (0 : ℝ) ≤ 2 ^ (b + 1) := by positivity
  calc |f n| * (n : ℝ) ^ (-b - 1)
      = |f n| * (2 ^ (b + 1) * ((2 : ℝ) ^ (-b - 1) * (n : ℝ) ^ (-b - 1))) := by
        rw [← mul_assoc (2 ^ (b + 1) : ℝ), h2', one_mul]
    _ ≤ |f n| * (2 ^ (b + 1) * (mellinCell b n / b)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h3 h2pos) (abs_nonneg _)
    _ = 2 ^ (b + 1) / b * (|f n| * mellinCell b n) := by ring

/-- **The Mellin pairing of a paid prefix is holomorphic on `Re s > 1/2`.** -/
theorem differentiableOn_complexMellinPairing {E : ℝ} {f : ℕ → ℝ} (hf0 : f 0 = 0)
    (hE : ∀ T, ∑ n ∈ Icc 1 T, f n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) ≤ E) :
    DifferentiableOn ℂ (complexMellinPairing f) {s : ℂ | 1 / 2 < s.re} := by
  intro s₀ hs₀
  have hs₀' : (1 : ℝ) / 2 < s₀.re := hs₀
  obtain ⟨b, hb, hbs⟩ : ∃ b : ℝ, 1 / 2 < b ∧ b < s₀.re := ⟨(1 / 2 + s₀.re) / 2, by linarith,
    by linarith⟩
  obtain ⟨R, hR, hsR⟩ : ∃ R : ℝ, 0 ≤ R ∧ ‖s₀‖ < R := ⟨‖s₀‖ + 1, by positivity, by linarith⟩
  set U : Set ℂ := {s | b < s.re} ∩ {s | ‖s‖ < R} with hU_def
  have hU : IsOpen U := (isOpen_lt continuous_const Complex.continuous_re).inter
    (isOpen_lt continuous_norm continuous_const)
  have hs₀U : s₀ ∈ U := ⟨hbs, hsR⟩
  have hsum := (summable_abs_mul_rpow_of_energy hb hf0 hE).mul_left R
  have hdiff : DifferentiableOn ℂ (fun s => ∑' n : ℕ, (f n : ℂ) * complexMellinCell s n) U := by
    refine Complex.differentiableOn_tsum_of_summable_norm
      (F := fun n s => (f n : ℂ) * complexMellinCell s n) hsum (fun n s hs => ?_) hU
      (fun n s hs => ?_)
    · have hs0 : -s ≠ 0 := neg_ne_zero.mpr fun h => by
        have h1 : b < s.re := hs.1
        rw [h, Complex.zero_re] at h1; linarith
      refine DifferentiableAt.differentiableWithinAt ?_
      show DifferentiableAt ℂ (fun s => (f n : ℂ) * (((n : ℝ) : ℂ) ^ (-s) -
        (((n : ℝ) + 1 : ℝ) : ℂ) ^ (-s))) s
      exact (differentiableAt_const _).mul
        ((differentiableAt_id.neg.const_cpow (Or.inr hs0)).sub
          (differentiableAt_id.neg.const_cpow (Or.inr hs0)))
    · show ‖(f n : ℂ) * complexMellinCell s n‖ ≤ R * (|f n| * (n : ℝ) ^ (-b - 1))
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp [hf0]
      have hre : b < s.re := hs.1
      have hnorm : ‖s‖ < R := hs.2
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      calc |f n| * ‖complexMellinCell s n‖ ≤ |f n| * (‖s‖ * (n : ℝ) ^ (-s.re - 1)) :=
            mul_le_mul_of_nonneg_left (norm_complexMellinCell_le (by linarith) hn) (abs_nonneg _)
        _ ≤ |f n| * (R * (n : ℝ) ^ (-b - 1)) := by
            refine mul_le_mul_of_nonneg_left (mul_le_mul hnorm.le ?_ (by positivity) hR)
              (abs_nonneg _)
            exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) (by linarith)
        _ = R * (|f n| * (n : ℝ) ^ (-b - 1)) := by ring
  exact (hdiff.differentiableAt (hU.mem_nhds hs₀U)).differentiableWithinAt

/-- The Mellin pairing identity at real points, in complex form: `Φ(σ) = ζ(σ)(C(σ) − m)`. -/
theorem complexMellinPairing_eq_zeta_mul {c : ℕ → ℝ} {θ σ : ℝ} (hθ0 : 0 < θ) (hθσ : θ < σ)
    (hσ1 : σ < 1) (hc : Summable (fun d : ℕ => |c d| * (d : ℝ) ^ (-θ))) :
    complexMellinPairing (weightCenteredPrefix c (∑' d : ℕ, c d / d)) σ =
      riemannZeta σ * (((∑' d : ℕ, c d * (d : ℝ) ^ (-σ)) - ∑' d : ℕ, c d / d : ℝ) : ℂ) := by
  rw [complexMellinPairing_ofReal]
  exact (mellinPairing_eq_zeta_mul_of_summable hθ0 hθσ hσ1 hc).2

/-- **A paid receiver continues `ζ(s)(C(s) − m)` holomorphically to `Re s > 1/2`.** If
`Σ_d |c(d)| d^{-θ} < ∞` for every `θ > a ≥ 0` and every pronic energy of `c` is at most `E`, some
function holomorphic on `Re s > 1/2` equals `ζ(σ)(C(σ) − m)` on `a < σ < 1`. -/
theorem exists_holomorphic_continuation {E a : ℝ} {c : ℕ → ℝ} (ha : 0 ≤ a)
    (hc : ∀ θ : ℝ, a < θ → Summable (fun d : ℕ => |c d| * (d : ℝ) ^ (-θ)))
    (hE : ∀ T, weightPronicEnergy c (∑' d : ℕ, c d / d) T ≤ E) :
    ∃ Φ : ℂ → ℂ, DifferentiableOn ℂ Φ {s : ℂ | 1 / 2 < s.re} ∧
      ∀ σ : ℝ, a < σ → σ < 1 →
        Φ σ = riemannZeta σ * (((∑' d : ℕ, c d * (d : ℝ) ^ (-σ)) - ∑' d : ℕ, c d / d : ℝ) : ℂ) :=
  ⟨complexMellinPairing (weightCenteredPrefix c (∑' d : ℕ, c d / d)),
    differentiableOn_complexMellinPairing (weightCenteredPrefix_zero _ _) fun T => hE T,
    fun σ haσ hσ1 => complexMellinPairing_eq_zeta_mul (θ := (a + σ) / 2) (by linarith)
      (by linarith) hσ1 (hc _ (by linarith))⟩

/-! ### The quotient by `ζ` at the abscissa -/

/-- `ζ(σ) ≠ 0` for `0 < σ < 1`, since `|ζ(σ)| ≥ σ/(1 − σ)`. -/
theorem riemannZeta_ne_zero_of_pos_of_lt_one {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    riemannZeta σ ≠ 0 := by
  intro h
  have h1 := div_le_norm_riemannZeta hσ0 hσ1
  rw [h, norm_zero] at h1
  have : 0 < σ / (1 - σ) := div_pos hσ0 (by linarith)
  linarith

/-- The quotient `Φ(s)/ζ(s)` of the Mellin pairing of the centred prefix by `ζ`. -/
def mellinQuotient (c : ℕ → ℝ) (s : ℂ) : ℂ :=
  complexMellinPairing (weightCenteredPrefix c (∑' d : ℕ, c d / d)) s / riemannZeta s

/-- On `a < σ < 1` the quotient is `C(σ) − m`. -/
theorem mellinQuotient_ofReal {a σ : ℝ} {c : ℕ → ℝ} (ha : 0 ≤ a) (haσ : a < σ) (hσ1 : σ < 1)
    (hc : ∀ θ : ℝ, a < θ → Summable (fun d : ℕ => |c d| * (d : ℝ) ^ (-θ))) :
    mellinQuotient c σ = (((∑' d : ℕ, c d * (d : ℝ) ^ (-σ)) - ∑' d : ℕ, c d / d : ℝ) : ℂ) := by
  rw [mellinQuotient, complexMellinPairing_eq_zeta_mul (θ := (a + σ) / 2) (by linarith)
    (by linarith) hσ1 (hc _ (by linarith))]
  exact mul_div_cancel_left₀ _ (riemannZeta_ne_zero_of_pos_of_lt_one (by linarith) hσ1)

/-- For a paid weight the quotient is analytic at every real `1/2 < a < 1`. -/
theorem analyticAt_mellinQuotient {E a : ℝ} {c : ℕ → ℝ} (ha : 1 / 2 < a) (ha1 : a < 1)
    (hE : ∀ T, weightPronicEnergy c (∑' d : ℕ, c d / d) T ≤ E) :
    AnalyticAt ℂ (mellinQuotient c) a := by
  have hΦ : AnalyticAt ℂ (complexMellinPairing (weightCenteredPrefix c (∑' d : ℕ, c d / d))) a :=
    (differentiableOn_complexMellinPairing (weightCenteredPrefix_zero _ _) fun T => hE T).analyticAt
      ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by simpa using ha))
  have hζ : AnalyticAt ℂ riemannZeta a := by
    refine DifferentiableOn.analyticAt (s := {1}ᶜ)
      (fun s hs => (differentiableAt_riemannZeta (by simpa using hs)).differentiableWithinAt) ?_
    refine isOpen_compl_singleton.mem_nhds ?_
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    intro h
    have := congrArg Complex.re h
    simp only [Complex.ofReal_re, Complex.one_re] at this
    linarith
  exact hΦ.div hζ (riemannZeta_ne_zero_of_pos_of_lt_one (by linarith) ha1)

/-- **A paid receiver makes the Dirichlet series Lipschitz at its abscissa.** Let `1/2 < a < 1`,
`Σ_d |c(d)| d^{-θ} < ∞` for every `θ > a`, and every pronic energy of `c` at most `E`. Then
`|C(σ) − L| ≤ M (σ − a)` on `a < σ < a + η`, for some `L`, `M` and `η > 0`. -/
theorem exists_abs_dirichletSeries_sub_le_mul {E a : ℝ} {c : ℕ → ℝ} (ha : 1 / 2 < a) (ha1 : a < 1)
    (hc : ∀ θ : ℝ, a < θ → Summable (fun d : ℕ => |c d| * (d : ℝ) ^ (-θ)))
    (hE : ∀ T, weightPronicEnergy c (∑' d : ℕ, c d / d) T ≤ E) :
    ∃ L M η : ℝ, 0 < η ∧ ∀ σ : ℝ, a < σ → σ < a + η →
      |∑' d : ℕ, c d * (d : ℝ) ^ (-σ) - L| ≤ M * (σ - a) := by
  have ha0 : 0 ≤ a := by linarith
  have hG : HasDerivAt (fun x : ℝ => mellinQuotient c x) (deriv (mellinQuotient c) a) a :=
    (analyticAt_mellinQuotient ha ha1 hE).differentiableAt.hasDerivAt.comp_ofReal
  obtain ⟨M, hM⟩ := hG.isBigO_sub.bound
  obtain ⟨η, hη, hball⟩ := Metric.eventually_nhds_iff.mp hM
  refine ⟨∑' d : ℕ, c d / d + (mellinQuotient c a).re, M, min η (1 - a),
    lt_min hη (by linarith), fun σ haσ hσ => ?_⟩
  have hσ1 : σ < 1 := by linarith [min_le_right η (1 - a)]
  have hση : dist σ a < η := by
    rw [Real.dist_eq, abs_of_pos (by linarith)]; linarith [min_le_left η (1 - a)]
  have h : ‖mellinQuotient c σ - mellinQuotient c a‖ ≤ M * ‖σ - a‖ := hball hση
  rw [Real.norm_eq_abs, abs_of_pos (show 0 < σ - a by linarith)] at h
  have hre : ∑' d : ℕ, c d * (d : ℝ) ^ (-σ) - (∑' d : ℕ, c d / d + (mellinQuotient c a).re) =
      (mellinQuotient c σ - mellinQuotient c a).re := by
    rw [Complex.sub_re, mellinQuotient_ofReal ha0 haσ hσ1 hc, Complex.ofReal_re]; ring
  rw [hre]
  exact (Complex.abs_re_le_norm _).trans h

/-! ### The order at the abscissa is an integer -/

/-- `u^γ → 0` as `u ↓ 0` for `γ > 0`. -/
theorem tendsto_rpow_nhdsGT_zero_of_pos {γ : ℝ} (hγ : 0 < γ) :
    Tendsto (fun u : ℝ => u ^ γ) (𝓝[>] 0) (𝓝 0) := by
  have h := (Real.continuous_rpow_const hγ.le).tendsto 0
  rw [Real.zero_rpow hγ.ne'] at h
  exact h.mono_left nhdsWithin_le_nhds

/-- Two power laws comparable in both directions near `0` have the same exponent. -/
theorem eq_of_rpow_le_rpow_nhdsGT {α β A B C D : ℝ} (hA : 0 < A) (hC : 0 < C)
    (h1 : ∀ᶠ u in 𝓝[>] (0 : ℝ), A * u ^ α ≤ B * u ^ β)
    (h2 : ∀ᶠ u in 𝓝[>] (0 : ℝ), C * u ^ β ≤ D * u ^ α) : α = β := by
  have key : ∀ {x y P Q : ℝ}, 0 < P → (∀ᶠ u in 𝓝[>] (0 : ℝ), P * u ^ x ≤ Q * u ^ y) → ¬ x < y := by
    intro x y P Q hP h hxy
    have hlim : Tendsto (fun u : ℝ => Q * u ^ (y - x)) (𝓝[>] 0) (𝓝 0) := by
      simpa using (tendsto_rpow_nhdsGT_zero_of_pos (sub_pos.mpr hxy)).const_mul Q
    have hev : ∀ᶠ u in 𝓝[>] (0 : ℝ), P ≤ Q * u ^ (y - x) := by
      filter_upwards [h, self_mem_nhdsWithin] with u hu (hu0 : 0 < u)
      have hux : 0 < u ^ x := Real.rpow_pos_of_pos hu0 x
      have hsplit : u ^ y = u ^ x * u ^ (y - x) := by
        rw [← Real.rpow_add hu0, show x + (y - x) = y by ring]
      refine le_of_mul_le_mul_right ?_ hux
      calc P * u ^ x ≤ Q * u ^ y := hu
        _ = Q * u ^ (y - x) * u ^ x := by rw [hsplit]; ring
    linarith [ge_of_tendsto hlim hev]
  rcases lt_trichotomy α β with h | h | h
  · exact absurd h (key hA h1)
  · exact h
  · exact absurd h (key hC h2)

/-- **A paid receiver makes the order at the abscissa an integer.** Let `1/2 < a < 1`,
`Σ_d |c(d)| d^{-θ} < ∞` for every `θ > a`, and every pronic energy of `c` at most `E`. If
`κ u^α ≤ |C(a + u) − L| ≤ K u^α` for `0 < u < u₀`, with `κ, α > 0`, then `α ∈ ℕ`: it is the order
of vanishing at `a` of the analytic function `Φ/ζ − Φ(a)/ζ(a)`, which agrees with `C − L` on the
right of `a`. -/
theorem exists_nat_eq_of_rpow_bounds_at_abscissa {E a L κ K α u₀ : ℝ} {c : ℕ → ℝ}
    (ha : 1 / 2 < a) (ha1 : a < 1)
    (hc : ∀ θ : ℝ, a < θ → Summable (fun d : ℕ => |c d| * (d : ℝ) ^ (-θ)))
    (hE : ∀ T, weightPronicEnergy c (∑' d : ℕ, c d / d) T ≤ E)
    (hκ : 0 < κ) (hα : 0 < α) (hu₀ : 0 < u₀)
    (hbd : ∀ u : ℝ, 0 < u → u < u₀ →
      κ * u ^ α ≤ |∑' d : ℕ, c d * (d : ℝ) ^ (-(a + u)) - L| ∧
        |∑' d : ℕ, c d * (d : ℝ) ^ (-(a + u)) - L| ≤ K * u ^ α) :
    ∃ n : ℕ, α = n := by
  have ha0 : 0 ≤ a := by linarith
  set m := ∑' d : ℕ, c d / d with hm
  set Cs : ℝ → ℝ := fun u => ∑' d : ℕ, c d * (d : ℝ) ^ (-(a + u)) with hCs
  set G := mellinQuotient c with hGdef
  have hG : AnalyticAt ℂ G a := analyticAt_mellinQuotient ha ha1 hE
  have hIoo : Set.Ioo (0 : ℝ) (min u₀ (1 - a)) ∈ 𝓝[>] (0 : ℝ) :=
    Ioo_mem_nhdsGT (lt_min hu₀ (by linarith))
  -- `G = C − m` on the real segment right of `a`
  have hGr : ∀ u ∈ Set.Ioo (0 : ℝ) (min u₀ (1 - a)), G ((a + u : ℝ) : ℂ) = ((Cs u - m : ℝ) : ℂ) :=
    fun u hu => mellinQuotient_ofReal ha0 (by linarith [hu.1])
      (by linarith [hu.2, min_le_right u₀ (1 - a)]) hc
  have hpath : Tendsto (fun u : ℝ => ((a + u : ℝ) : ℂ)) (𝓝[>] 0) (𝓝 (a : ℂ)) := by
    have hcont : Continuous (fun u : ℝ => ((a + u : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.comp (continuous_const.add continuous_id)
    have h := (hcont.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
    rwa [add_zero] at h
  have hlim : Tendsto (fun u : ℝ => G ((a + u : ℝ) : ℂ)) (𝓝[>] 0) (𝓝 (G a)) :=
    hG.continuousAt.tendsto.comp hpath
  -- `G(a)` is real and `C(a + u) → m + G(a)`
  have hGim : (G a).im = 0 := by
    refine tendsto_nhds_unique ((Complex.continuous_im.tendsto _).comp hlim)
      (tendsto_const_nhds.congr' ?_)
    filter_upwards [hIoo] with u hu
    simp only [Function.comp]
    rw [hGr u hu, Complex.ofReal_im]
  have hCs' : Tendsto Cs (𝓝[>] 0) (𝓝 (m + (G a).re)) := by
    refine ((((Complex.continuous_re.tendsto _).comp hlim).const_add m)).congr' ?_
    filter_upwards [hIoo] with u hu
    simp only [Function.comp]
    rw [hGr u hu, Complex.ofReal_re]
    ring
  have hCsL : Tendsto Cs (𝓝[>] 0) (𝓝 L) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun u => norm_nonneg _) ?_
      (by simpa using (tendsto_rpow_nhdsGT_zero_of_pos hα).const_mul K)
    filter_upwards [hIoo] with u hu
    rw [Real.norm_eq_abs]
    exact (hbd u hu.1 (lt_of_lt_of_le hu.2 (min_le_left _ _))).2
  have hL : L = m + (G a).re := tendsto_nhds_unique hCsL hCs'
  -- `H = G − G(a)` is analytic, vanishes at `a`, and has `|H(a + u)| = |C(a + u) − L|`
  set H : ℂ → ℂ := fun s => G s - G a with hHdef
  have hH : AnalyticAt ℂ H a := hG.sub analyticAt_const
  have hGa : G a = (((G a).re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [hGim])
  have hHr : ∀ u ∈ Set.Ioo (0 : ℝ) (min u₀ (1 - a)), ‖H ((a + u : ℝ) : ℂ)‖ = |Cs u - L| := by
    intro u hu
    simp only [hHdef]
    rw [hGr u hu, hGa, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, hL]
    congr 1
    ring
  by_cases h0 : ∀ᶠ z in 𝓝 (a : ℂ), H z = 0
  · -- `H` vanishes near `a`: then `C(a + u) = L`, against the lower bound
    obtain ⟨u, hu0, hu⟩ := ((hpath.eventually h0).and hIoo).exists
    have h1 : κ * u ^ α ≤ |Cs u - L| := (hbd u hu.1 (lt_of_lt_of_le hu.2 (min_le_left _ _))).1
    have h2 := hHr u hu
    rw [hu0, norm_zero] at h2
    have : 0 < κ * u ^ α := mul_pos hκ (Real.rpow_pos_of_pos hu.1 _)
    linarith
  obtain ⟨n, g, hg, hga, hHg⟩ := hH.exists_eventuallyEq_pow_smul_nonzero_iff.mpr h0
  -- `‖g‖` is comparable to `‖g(a)‖` near `a`
  have hgpos : 0 < ‖g a‖ := norm_pos_iff.mpr hga
  have hgnear : ∀ᶠ z in 𝓝 (a : ℂ), ‖g a‖ / 2 ≤ ‖g z‖ ∧ ‖g z‖ ≤ 2 * ‖g a‖ := by
    have hball := Metric.ball_mem_nhds (g a) (half_pos hgpos)
    filter_upwards [hg.continuousAt.preimage_mem_nhds hball] with z hz
    have hz' : ‖g z - g a‖ < ‖g a‖ / 2 := by simpa [dist_eq_norm] using hz
    have h1 := norm_sub_norm_le (g a) (g z)
    have h2 := norm_sub_norm_le (g z) (g a)
    rw [norm_sub_rev] at h1
    constructor <;> linarith
  -- on the real segment, `|C(a + u) − L| = u^n ‖g(a + u)‖`
  have hev : ∀ᶠ u in 𝓝[>] (0 : ℝ), u ∈ Set.Ioo (0 : ℝ) (min u₀ (1 - a)) ∧
      |Cs u - L| = u ^ (n : ℝ) * ‖g ((a + u : ℝ) : ℂ)‖ ∧
      ‖g a‖ / 2 ≤ ‖g ((a + u : ℝ) : ℂ)‖ ∧ ‖g ((a + u : ℝ) : ℂ)‖ ≤ 2 * ‖g a‖ := by
    filter_upwards [hIoo, hpath.eventually hHg, hpath.eventually hgnear] with u hu hHu hgu
    have hHu' : H ((a + u : ℝ) : ℂ) = (((a + u : ℝ) : ℂ) - a) ^ n • g ((a + u : ℝ) : ℂ) := hHu
    refine ⟨hu, ?_, hgu⟩
    rw [← hHr u hu, hHu', norm_smul, norm_pow, Real.rpow_natCast,
      show ((a + u : ℝ) : ℂ) - (a : ℂ) = (u : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hu.1]
  have hup : ∀ᶠ u in 𝓝[>] (0 : ℝ), κ * u ^ α ≤ (2 * ‖g a‖) * u ^ (n : ℝ) := by
    filter_upwards [hev] with u ⟨hu, hCu, _, hg2⟩
    have h1 := (hbd u hu.1 (lt_of_lt_of_le hu.2 (min_le_left _ _))).1
    have hun : 0 ≤ u ^ (n : ℝ) := Real.rpow_nonneg hu.1.le _
    calc κ * u ^ α ≤ |Cs u - L| := h1
      _ = u ^ (n : ℝ) * ‖g ((a + u : ℝ) : ℂ)‖ := hCu
      _ ≤ u ^ (n : ℝ) * (2 * ‖g a‖) := mul_le_mul_of_nonneg_left hg2 hun
      _ = (2 * ‖g a‖) * u ^ (n : ℝ) := by ring
  have hlow : ∀ᶠ u in 𝓝[>] (0 : ℝ), (‖g a‖ / 2) * u ^ (n : ℝ) ≤ K * u ^ α := by
    filter_upwards [hev] with u ⟨hu, hCu, hg1, _⟩
    have h2 := (hbd u hu.1 (lt_of_lt_of_le hu.2 (min_le_left _ _))).2
    have hun : 0 ≤ u ^ (n : ℝ) := Real.rpow_nonneg hu.1.le _
    calc (‖g a‖ / 2) * u ^ (n : ℝ) ≤ u ^ (n : ℝ) * ‖g ((a + u : ℝ) : ℂ)‖ := by
          rw [mul_comm]; exact mul_le_mul_of_nonneg_left hg1 hun
      _ = |Cs u - L| := hCu.symm
      _ ≤ K * u ^ α := h2
  exact ⟨n, eq_of_rpow_le_rpow_nhdsGT hκ (half_pos hgpos) hup hlow⟩

/-! ### Multiplicative weights: the prime mean is quantized below half damping -/

/-- `|−log(1 − y) − y| ≤ 2y²` for `|y| ≤ 1/2`. -/
theorem abs_neg_log_one_sub_sub_le {y : ℝ} (hy : |y| ≤ 1 / 2) :
    |-Real.log (1 - y) - y| ≤ 2 * y ^ 2 := by
  have h := Real.abs_log_sub_add_sum_range_le (show |y| < 1 by linarith) 1
  norm_num [Finset.sum_range_one] at h
  have h1 : |y| ^ 2 / (1 - |y|) ≤ 2 * y ^ 2 := by
    rw [div_le_iff₀ (by linarith), sq_abs]
    nlinarith [mul_nonneg (sq_nonneg y) (show 0 ≤ 1 - 2 * |y| by linarith)]
  rw [show -Real.log (1 - y) - y = -(y + Real.log (1 - y)) by ring, abs_neg]
  exact h.trans h1

/-- **The Euler product reads the prime sum up to a bounded factor.** For `f` completely
multiplicative with `|f(p)| ≤ 1` and `w > 1`, `Σ f(n) n^{-w}` lies between
`exp(Σ_p f(p) p^{-w} ∓ 2S)`, `S = Σ_p p^{-2}`. -/
theorem tsum_pattern_mem_exp_primeSum (f : ℕ →*₀ ℝ) (hf : ∀ p : ℕ, p.Prime → |f p| ≤ 1) {w : ℝ}
    (hw : 1 < w) :
    Real.exp (∑' p : Nat.Primes, f p * ((p : ℕ) : ℝ) ^ (-w) -
        2 * ∑' p : Nat.Primes, ((p : ℕ) : ℝ) ^ (-2 : ℝ)) ≤ ∑' n : ℕ, f n * (n : ℝ) ^ (-w) ∧
      ∑' n : ℕ, f n * (n : ℝ) ^ (-w) ≤ Real.exp (∑' p : Nat.Primes, f p * ((p : ℕ) : ℝ) ^ (-w) +
        2 * ∑' p : Nat.Primes, ((p : ℕ) : ℝ) ^ (-2 : ℝ)) := by
  set x : Nat.Primes → ℝ := fun p => ((p : ℕ) : ℝ) ^ (-w) with hx
  have hx0 : ∀ p, 0 ≤ x p := fun p => Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hxhalf : ∀ p : Nat.Primes, x p ≤ 1 / 2 := by
    intro p
    have hp2 : (2 : ℝ) ≤ (p : ℕ) := by exact_mod_cast p.2.two_le
    calc x p ≤ ((p : ℕ) : ℝ) ^ (-1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
      _ ≤ 2 ^ (-1 : ℝ) := Real.rpow_le_rpow_of_nonpos (by norm_num) hp2 (by norm_num)
      _ = 1 / 2 := by rw [Real.rpow_neg_one]; norm_num
  have hxs : Summable x := Nat.Primes.summable_rpow.mpr (by linarith)
  have hx2s : Summable (fun p : Nat.Primes => ((p : ℕ) : ℝ) ^ (-2 : ℝ)) :=
    Nat.Primes.summable_rpow.mpr (by norm_num)
  have hxsq : ∀ p, x p ^ 2 ≤ ((p : ℕ) : ℝ) ^ (-2 : ℝ) := by
    intro p
    have hp1 : (1 : ℝ) ≤ (p : ℕ) := by exact_mod_cast p.2.one_lt.le
    rw [hx, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]
    exact Real.rpow_le_rpow_of_exponent_le hp1 (by push_cast; linarith)
  set y : Nat.Primes → ℝ := fun p => f p * x p with hy_def
  have hy : ∀ p, |y p| ≤ x p := fun p => by
    simp only [hy_def]
    rw [abs_mul, abs_of_nonneg (hx0 p)]
    exact mul_le_of_le_one_left (hx0 p) (hf p p.2)
  have hys : Summable y := hxs.of_norm_bounded fun p => by rw [Real.norm_eq_abs]; exact hy p
  -- prime by prime, `−log(1 − y) = y + O(p^{-2})`
  have hdiff : ∀ p, |-Real.log (1 - y p) - y p| ≤ 2 * ((p : ℕ) : ℝ) ^ (-2 : ℝ) := fun p => by
    have h := abs_neg_log_one_sub_sub_le ((hy p).trans (hxhalf p))
    have hsq : y p ^ 2 ≤ ((p : ℕ) : ℝ) ^ (-2 : ℝ) :=
      calc y p ^ 2 = |y p| ^ 2 := (sq_abs _).symm
        _ ≤ x p ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hy p) 2
        _ ≤ _ := hxsq p
    linarith
  have hDs : Summable (fun p => -Real.log (1 - y p) - y p) :=
    (hx2s.mul_left 2).of_norm_bounded fun p => by rw [Real.norm_eq_abs]; exact hdiff p
  have hLs : Summable (fun p => -Real.log (1 - y p)) := (hDs.add hys).congr fun p => by ring
  have hsum : |∑' p, -Real.log (1 - y p) - ∑' p, y p| ≤
      2 * ∑' p : Nat.Primes, ((p : ℕ) : ℝ) ^ (-2 : ℝ) := by
    rw [← tsum_sub hLs hys, ← tsum_mul_left]
    have h1 : ‖∑' p, (-Real.log (1 - y p) - y p)‖ ≤ ∑' p, ‖-Real.log (1 - y p) - y p‖ :=
      norm_tsum_le_tsum_norm hDs.norm
    have h2 : ∑' p, ‖-Real.log (1 - y p) - y p‖ ≤ ∑' p : Nat.Primes, 2 * ((p : ℕ) : ℝ) ^ (-2 : ℝ) :=
      Summable.tsum_le_tsum (fun p => by rw [Real.norm_eq_abs]; exact hdiff p) hDs.norm
        (hx2s.mul_left 2)
    rw [Real.norm_eq_abs] at h1
    exact h1.trans h2
  have hab := abs_le.mp hsum
  rw [tsum_pattern_eq_exp f hf hw]
  have e1 : ∑' p : Nat.Primes, f p * ((p : ℕ) : ℝ) ^ (-w) = ∑' p, y p := rfl
  have e2 : ∑' p : Nat.Primes, -Real.log (1 - f p * ((p : ℕ) : ℝ) ^ (-w)) =
      ∑' p, -Real.log (1 - y p) := rfl
  rw [e1, e2]
  exact ⟨Real.exp_le_exp.mpr (by linarith [hab.1]), Real.exp_le_exp.mpr (by linarith [hab.2])⟩

/-- **A paid multiplicative weight below half damping has prime mean `0` or `−1`.** Let
`0 < ε < 1/2`, let `f` be completely multiplicative with `|f(p)| ≤ 1`, and let its primes have
logarithmic mean `ν`: `|Σ_p f(p) p^{-w} − ν log(1/(w − 1))| ≤ B` on `1 < w < 3/2`. If `ν` is not
a non-positive integer, the receiver of `f(d) d^{-ε}` is unbounded: the Dirichlet series of the
weight at `1 − ε + u` is `Σ f(n) n^{-1-u} ≍ u^{-ν}`, unbounded for `ν > 0` and of non-integral
order `−ν` otherwise. -/
theorem not_receiverBounded_of_primeMean {ε ν B : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 2)
    (f : ℕ →*₀ ℝ) (hf : ∀ p : ℕ, p.Prime → |f p| ≤ 1) (hν : ∀ n : ℕ, ν ≠ -n)
    (hP : ∀ w : ℝ, 1 < w → w < 3 / 2 →
      |∑' p : Nat.Primes, f p * ((p : ℕ) : ℝ) ^ (-w) - ν * Real.log (1 / (w - 1))| ≤ B) :
    ¬ ReceiverBounded (fun d => f d * (d : ℝ) ^ (-ε)) := by
  rintro ⟨E, hE⟩
  set c : ℕ → ℝ := fun d => f d * (d : ℝ) ^ (-ε) with hc_def
  have hcl : DampedClass 1 ε c := by
    intro d
    rw [one_mul, abs_mul, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg d) _)]
    exact mul_le_of_le_one_left (Real.rpow_nonneg (Nat.cast_nonneg d) _)
      (abs_le_one_of_primes f hf d)
  have hc : ∀ θ : ℝ, 1 - ε < θ → Summable (fun d : ℕ => |c d| * (d : ℝ) ^ (-θ)) :=
    fun θ hθ => summable_abs_mul_rpow_of_dampedClass hε hcl hθ
  -- the weight's series at `1 − ε + u` is the pattern series at `1 + u`
  set F : ℝ → ℝ := fun u => ∑' n : ℕ, f n * (n : ℝ) ^ (-(1 + u)) with hF
  have hCF : ∀ u : ℝ, ∑' d : ℕ, c d * (d : ℝ) ^ (-(1 - ε + u)) = F u := by
    intro u
    refine tsum_congr fun d => ?_
    simp only [hc_def]
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · simp
    · have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
      rw [mul_assoc, ← Real.rpow_add hd0]; ring_nf
  -- `κ u^{-ν} ≤ F(u) ≤ K u^{-ν}` on `0 < u < 1/2`
  set S := ∑' p : Nat.Primes, ((p : ℕ) : ℝ) ^ (-2 : ℝ) with hS
  set κ := Real.exp (-B - 2 * S) with hκ_def
  set K := Real.exp (B + 2 * S) with hK_def
  have hκ : 0 < κ := Real.exp_pos _
  have hbounds : ∀ u : ℝ, 0 < u → u < 1 / 2 → κ * u ^ (-ν) ≤ F u ∧ F u ≤ K * u ^ (-ν) := by
    intro u hu hu2
    obtain ⟨h1, h2⟩ := tsum_pattern_mem_exp_primeSum f hf (w := 1 + u) (by linarith)
    have hPu := abs_le.mp (hP (1 + u) (by linarith) (by linarith))
    rw [show 1 + u - 1 = u by ring] at hPu
    have hpow : u ^ (-ν) = Real.exp (ν * Real.log (1 / u)) := by
      rw [Real.rpow_def_of_pos hu, one_div, Real.log_inv]; ring_nf
    rw [hpow, hκ_def, hK_def, ← Real.exp_add, ← Real.exp_add]
    constructor
    · exact h1.trans' (Real.exp_le_exp.mpr (by linarith [hPu.1]))
    · exact h2.trans (Real.exp_le_exp.mpr (by linarith [hPu.2]))
  rcases lt_or_ge 0 ν with hν0 | hν0
  · -- `ν > 0`: the series is unbounded at the abscissa, a paid one is Lipschitz there
    obtain ⟨L, M, η, hη, hlip⟩ := exists_abs_dirichletSeries_sub_le_mul (E := E) (a := 1 - ε)
      (by linarith) (by linarith) hc hE
    have htend : Tendsto (fun u : ℝ => κ * u ^ (-ν)) (𝓝[>] 0) atTop :=
      (tendsto_rpow_neg_nhdsGT_zero (show -ν < 0 by linarith)).const_mul_atTop hκ
    obtain ⟨u, hu1, hu2⟩ := ((htend.eventually_gt_atTop (|L| + |M|)).and
      (Ioo_mem_nhdsGT (show (0 : ℝ) < min η (1 / 2) by positivity))).exists
    have hu0 : 0 < u := hu2.1
    have huη : u < η := lt_of_lt_of_le hu2.2 (min_le_left _ _)
    have hu12 : u < 1 / 2 := lt_of_lt_of_le hu2.2 (min_le_right _ _)
    have h1 := (hbounds u hu0 hu12).1
    have h2 := hlip (1 - ε + u) (by linarith) (by linarith)
    rw [hCF, show 1 - ε + u - (1 - ε) = u by ring] at h2
    have hMu : M * u ≤ |M| := by
      calc M * u ≤ |M| * u := mul_le_mul_of_nonneg_right (le_abs_self M) hu0.le
        _ ≤ |M| * 1 := mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg M)
        _ = |M| := mul_one _
    have h3 := (abs_le.mp h2).2
    linarith [le_abs_self L]
  · -- `ν < 0`: the series vanishes at the abscissa to the order `−ν`, which must be an integer
    have hν1 : ν < 0 := lt_of_le_of_ne hν0 (by simpa using hν 0)
    obtain ⟨n, hn⟩ := exists_nat_eq_of_rpow_bounds_at_abscissa (E := E) (a := 1 - ε) (L := 0)
      (κ := κ) (K := K) (u₀ := 1 / 2) (by linarith) (by linarith) hc hE hκ
      (show 0 < -ν by linarith) (by norm_num) fun u hu hu2 => by
        have hb := hbounds u hu hu2
        rw [hCF, sub_zero, abs_of_pos (lt_of_lt_of_le
          (mul_pos hκ (Real.rpow_pos_of_pos hu _)) hb.1)]
        exact hb
    exact hν n (by linarith)

/-- **The all-ones Euler product is at most `1 + 1/(w − 1)`.** -/
theorem exp_primes_le_one_add {w : ℝ} (hw : 1 < w) :
    Real.exp (∑' p : Nat.Primes, -Real.log (1 - ((p : ℕ) : ℝ) ^ (-w))) ≤ 1 + 1 / (w - 1) := by
  have hones1 : ∀ p : ℕ, p.Prime → |onesPatternHom p| ≤ 1 := fun p hp => by
    simp [onesPatternHom, hp.ne_zero]
  have h := tsum_pattern_eq_exp onesPatternHom hones1 hw
  have hL1eq : ∀ p : Nat.Primes, -Real.log (1 - onesPatternHom p * ((p : ℕ) : ℝ) ^ (-w)) =
      -Real.log (1 - ((p : ℕ) : ℝ) ^ (-w)) := fun p => by
    simp [onesPatternHom, p.2.ne_zero]
  simp_rw [hL1eq] at h
  rw [← h]
  have hterm : ∀ n : ℕ, onesPatternHom n * (n : ℝ) ^ (-w) = (n : ℝ) ^ (-w) := fun n => by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [Real.zero_rpow (show -w ≠ 0 by linarith)]
    · simp [onesPatternHom, hn.ne']
  simp_rw [hterm]
  exact RHTower.Sieve.tsum_nat_rpow_neg_le hw

/-- **Mertens at the pole**: `|Σ_p p^{-w} − log(1/(w − 1))| ≤ 2S + log(3/2)` on `1 < w < 3/2`. -/
theorem abs_tsum_primes_rpow_sub_log_le {w : ℝ} (hw : 1 < w) (hw2 : w < 3 / 2) :
    |∑' p : Nat.Primes, ((p : ℕ) : ℝ) ^ (-w) - Real.log (1 / (w - 1))| ≤
      2 * ∑' p : Nat.Primes, ((p : ℕ) : ℝ) ^ (-2 : ℝ) + Real.log (3 / 2) := by
  have hones1 : ∀ p : ℕ, p.Prime → |onesPatternHom p| ≤ 1 := fun p hp => by
    simp [onesPatternHom, hp.ne_zero]
  have hp1 : ∀ p : Nat.Primes, onesPatternHom p * ((p : ℕ) : ℝ) ^ (-w) = ((p : ℕ) : ℝ) ^ (-w) :=
    fun p => by simp [onesPatternHom, p.2.ne_zero]
  obtain ⟨h1, h2⟩ := tsum_pattern_mem_exp_primeSum onesPatternHom hones1 hw
  simp_rw [hp1] at h1 h2
  -- the all-ones series `Z` lies in `[1/(w−1), 1 + 1/(w−1)]`
  have hZ := tsum_pattern_eq_exp onesPatternHom hones1 hw
  have hL1eq : ∀ p : Nat.Primes, -Real.log (1 - onesPatternHom p * ((p : ℕ) : ℝ) ^ (-w)) =
      -Real.log (1 - ((p : ℕ) : ℝ) ^ (-w)) := fun p => by
    simp [onesPatternHom, p.2.ne_zero]
  simp_rw [hL1eq] at hZ
  set Z := ∑' n : ℕ, onesPatternHom n * (n : ℝ) ^ (-w)
  have hZlow : 1 / (w - 1) ≤ Z := hZ ▸ one_div_sub_one_le_exp_primes hw
  have hZup : Z ≤ 1 + 1 / (w - 1) := hZ ▸ exp_primes_le_one_add hw
  have hw1 : 0 < w - 1 := by linarith
  have hZpos : 0 < Z := lt_of_lt_of_le (by positivity) hZlow
  set P := ∑' p : Nat.Primes, ((p : ℕ) : ℝ) ^ (-w)
  set S := ∑' p : Nat.Primes, ((p : ℕ) : ℝ) ^ (-2 : ℝ)
  -- logarithms
  have hlog1 : P - 2 * S ≤ Real.log Z := by
    rw [← Real.log_exp (P - 2 * S)]; exact Real.log_le_log (Real.exp_pos _) h1
  have hlog2 : Real.log Z ≤ P + 2 * S := by
    rw [← Real.log_exp (P + 2 * S)]; exact Real.log_le_log hZpos h2
  have hlog3 : Real.log (1 / (w - 1)) ≤ Real.log Z := Real.log_le_log (by positivity) hZlow
  have hlog4 : Real.log Z ≤ Real.log (1 / (w - 1)) + Real.log (3 / 2) := by
    rw [← Real.log_mul (by positivity) (by norm_num)]
    refine Real.log_le_log hZpos (hZup.trans ?_)
    rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hw1]
    have : (1 + 1 / (w - 1)) * (w - 1) = w := by field_simp; ring
    linarith
  rw [abs_le]; constructor <;> linarith

/-- **Below half damping the flipped density of a paid sign pattern is `1/2` or `1`.** Let
`0 < ε < 1/2`, let `f` be completely multiplicative with `f(p) = ±1` at every prime, and let its
flipped primes have Dirichlet density `ρ`:
`|Σ_{f(p) = −1} p^{-w} − ρ log(1/(w − 1))| ≤ B` on `1 < w < 3/2`. If `ρ ≠ 1/2` and `ρ < 1`, the
receiver of `f(d) d^{-ε}` is unbounded: the prime mean of `f` is `1 − 2ρ`. -/
theorem not_receiverBounded_of_flippedDensity {ε ρ B : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 2)
    (f : ℕ →*₀ ℝ) (hf : ∀ p : ℕ, p.Prime → f p = 1 ∨ f p = -1) (hρ : ρ ≠ 1 / 2) (hρ1 : ρ < 1)
    (hP : ∀ w : ℝ, 1 < w → w < 3 / 2 →
      |∑' p : Nat.Primes, (if f p = -1 then ((p : ℕ) : ℝ) ^ (-w) else 0) -
        ρ * Real.log (1 / (w - 1))| ≤ B) :
    ¬ ReceiverBounded (fun d => f d * (d : ℝ) ^ (-ε)) := by
  have hf1 : ∀ p : ℕ, p.Prime → |f p| ≤ 1 := fun p hp => by
    rcases hf p hp with h | h <;> simp [h]
  refine not_receiverBounded_of_primeMean hε hε2 f hf1 (ν := 1 - 2 * ρ)
    (B := 2 * B + (2 * ∑' p : Nat.Primes, ((p : ℕ) : ℝ) ^ (-2 : ℝ) + Real.log (3 / 2)))
    (fun n hn => ?_) fun w hw hw2 => ?_
  · -- `1 − 2ρ = −n` forces `ρ = (1 + n)/2 ∈ {1/2} ∪ [1, ∞)`
    rcases Nat.eq_zero_or_pos n with rfl | hn1
    · apply hρ; rw [Nat.cast_zero] at hn; linarith
    · have : (1 : ℝ) ≤ n := by exact_mod_cast hn1
      linarith
  · -- `f(p) p^{-w} = p^{-w} − 2 [f(p) = −1] p^{-w}`
    have hxs : Summable (fun p : Nat.Primes => ((p : ℕ) : ℝ) ^ (-w)) :=
      Nat.Primes.summable_rpow.mpr (by linarith)
    set I : Nat.Primes → ℝ := fun p => if f p = -1 then ((p : ℕ) : ℝ) ^ (-w) else 0 with hI
    have hIs : Summable I := hxs.of_nonneg_of_le
      (fun p => by simp only [hI]; split_ifs <;> positivity)
      fun p => by simp only [hI]; split_ifs <;> simp [Real.rpow_nonneg]
    have hsplit : ∑' p : Nat.Primes, f p * ((p : ℕ) : ℝ) ^ (-w) =
        ∑' p : Nat.Primes, ((p : ℕ) : ℝ) ^ (-w) - 2 * ∑' p, I p := by
      rw [← tsum_mul_left, ← tsum_sub hxs (hIs.mul_left 2)]
      refine tsum_congr fun p => ?_
      simp only [hI]
      rcases hf p p.2 with h | h
      · rw [if_neg (by rw [h]; norm_num), h]; ring
      · rw [if_pos h, h]; ring
    have hM := abs_le.mp (abs_tsum_primes_rpow_sub_log_le hw hw2)
    have hF := abs_le.mp (hP w hw hw2)
    rw [hsplit, abs_le]
    constructor <;> nlinarith [hM.1, hM.2, hF.1, hF.2]

end

end GaloisForLFunctions.TransHorizonIncidenceMechanics
