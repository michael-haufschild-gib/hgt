import GaloisForLFunctions.RHTower.SelbergNearLineFarRightConvexity
import GaloisForLFunctions.RHTower.SelbergExponentialNearLineDensity
import GaloisForLFunctions.RHTower.ZetaMollifiedShortWindowMeanSquare
import GaloisForLFunctions.RHTower.ZetaTwistedFirstMomentContour

/-!
# Exponential zero density near the critical line at rate `22/25`

Let `S` be large, `L = log S`, and `M = (log X · Ψ_X − log Y · Ψ_Y)/log(X/Y)` the two-length
Barban–Vehov mollifier with `X = ⌊S^{47/100}⌋`, `Y = ⌊S^{23/50}⌋`. Admissible heights
`T₁ ∈ (2S/3, 2S/3 + 1)`, `T₂ ∈ (4S/3 − 1, 4S/3)` exist such that for every `1 ≤ a ≤ L/100`

`2π (a/L) · #{ρ : Re ρ ≥ 1/2 + (51/50) a/L, T₁ ≤ Im ρ ≤ T₂} ≤ (T₂ − T₁) A e^{−22a/25} + K L`

(`exists_selberg_criticalGate_nearLine_zeroDensity`), zeros counted with multiplicity.

The mechanism is that of `SelbergExponentialNearLineDensity` with three changes, each needed to
bring the rate in `a` close to one.

* The left line of the three-lines argument is the critical line itself, where the continuous
  short-window mean square of `ζΨ_Z` (`exists_eventually_shortWindow_meanSquare_le`) holds for
  every length `Z = S^θ`, `θ < 1/2 − η`, in windows of length `S^{1−η}`.
* The right line is `Re s = 40`, where the tail beyond the von Mangoldt head is `≤ 2Z^{−38}`
  (`integral_hbMollifiedTail_window_le_farRight`); the decay rate of the tail on
  `Re s = 1/2 + a/L` becomes `2θ · 38/(79/2)`.
* The cross term `2 Re ∫(ζM − 1)` is controlled by the twisted first moment of `ζ`
  (`norm_integral_twistedZeta_sub_diag_le`) rather than by Cauchy–Schwarz, so the mollified mean
  square is `(T₂ − T₁)(1 + O(e^{−ra}))` with the full rate `r = (152/79)(23/50) > 22/25`.

Littlewood's lemma (`exists_zetaZeroDensity_scale_le_of_mollified_meanSquare_wide`) then counts the
zeros beyond `1/2 + (1 + 1/50)a/L` at the cost of the factor `50`.
-/

noncomputable section

open Complex Set MeasureTheory Filter

namespace RHTower

/-! ## The Barban–Vehov mollifier on the critical line -/

theorem edPoly_hbCoeff_eq_linMoll (N : ℕ) (s : ℂ) :
    edPoly (hbCoeff N) (Finset.Icc 1 N) s = VerticalAP.linMoll N s := by
  unfold edPoly VerticalAP.linMoll hbCoeff
  refine Finset.sum_congr rfl fun n hn => ?_
  have hnN := (Finset.mem_Icc.mp hn).2
  unfold Sieve.barbanVehovWeight Sieve.linearMollifierCoeff
  rw [if_pos hnN, Complex.ofReal_natCast]

/-- **The critical-line gate.** For `θ + η < 1/2`, eventually every window of length `S^{1−η}`
starting in `[S/2, 2S]` carries mean square `≤ C S^{1−η}` of `ζΨ_Z`, `Z = ⌊S^θ⌋`. -/
theorem exists_eventually_criticalGate {θ η : ℝ} (hθ0 : 0 < θ) (hη : 0 < η)
    (hθη : θ + η < 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ S : ℝ in atTop, ∀ α : ℝ, S / 2 ≤ α → α ≤ 2 * S →
      ∫ u in α..(α + S ^ (1 - η)),
        ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (u : ℂ) * I) *
          edPoly (hbCoeff (VerticalAP.molLen θ S)) (Finset.Icc 1 (VerticalAP.molLen θ S))
            (((1 / 2 : ℝ) : ℂ) + (u : ℂ) * I)‖ ^ 2 ≤ C * S ^ (1 - η) := by
  obtain ⟨C, hC, hev⟩ := VerticalAP.exists_eventually_shortWindow_meanSquare_le hθ0 hη hθη
  refine ⟨C, hC, ?_⟩
  filter_upwards [hev] with S hS α hα1 hα2
  have h := hS α hα1 hα2
  simp only [edPoly_hbCoeff_eq_linMoll]
  exact h

/-! ## Left windows on the critical line -/

/-- **Every left window on the critical line.** Near shifts are covered by the gate; far shifts by
the Gaussian. -/
theorem integral_nearLineWindowField_criticalLeft_le {N : ℕ} {S H τ Cg CM CW : ℝ}
    (hH : 3 ≤ H) (hHS : H ≤ S / 16) (hCg : 0 ≤ Cg) (hCW : 0 ≤ CW)
    (hW : ∀ z : ℂ, 1 / 4 ≤ z.re → z.re ≤ 3 → ‖nearLineField N z‖ ≤ CW * N * (1 + |z.im|))
    (hgate : ∀ α : ℝ, S / 2 ≤ α → α ≤ 2 * S →
      ∫ u in α..(α + 2 * H), ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (u : ℂ) * I) *
        edPoly (hbCoeff N) (Finset.Icc 1 N) (((1 / 2 : ℝ) : ℂ) + (u : ℂ) * I)‖ ^ 2 ≤
          Cg * (2 * H))
    (hα95 : 2 * (2 * S) ^ ((95 : ℝ) / 100) ≤ H) (hMVT : 8 * N * (1 + Real.log N) ≤ H)
    (hE : ∑ n ∈ Finset.Icc 1 N, ‖hbVonMangoldtCoeff N n‖ ^ 2 *
      (n : ℝ) ^ (2 * (1 / 2 - (1 / 2 : ℝ)) - 1) ≤ 2 * (1 + |CM|))
    (hτ1 : 5 * S / 8 + H ≤ τ) (hτ2 : τ ≤ 15 * S / 8 - H)
    (hkey : 16 * CW ^ 2 * N ^ 2 * (1 + |τ|) ^ 2 * H ^ 2 *
      Real.exp (-((S / 16) ^ 2 / H ^ 2)) ≤ 1) (y : ℝ) :
    ∫ t in (τ - H)..(τ + H),
      ‖nearLineWindowField N H τ (((1 / 2 : ℝ) : ℂ) + ((y + t : ℝ) : ℂ) * I)‖ ^ 2 ≤
        (18 * (3 * (Cg + 1) + 2 + 6 * (1 + |CM|)) + 1) * H := by
  have hH0 : 0 < H := by linarith
  have hS0 : 0 < S := by linarith
  have hsubst := intervalIntegral.integral_comp_add_left
    (fun u : ℝ => ‖nearLineWindowField N H τ (((1 / 2 : ℝ) : ℂ) + (u : ℂ) * I)‖ ^ 2) y
    (a := τ - H) (b := τ + H)
  rw [hsubst, show y + (τ + H) = (y + (τ - H)) + 2 * H by ring]
  have hC₁ : 0 ≤ 18 * (3 * (Cg + 1) + 2 + 6 * (1 + |CM|)) := by positivity
  rcases le_or_gt |y| (S / 8) with hy | hy
  · have hyabs := abs_le.mp hy
    set α : ℝ := y + (τ - H) with hαdef
    have hα1 : S / 2 ≤ α := by rw [hαdef]; linarith
    have hα2 : α ≤ 2 * S := by rw [hαdef]; linarith
    have hα0 : 0 ≤ α := by linarith
    have h95 : 2 * α ^ ((95 : ℝ) / 100) ≤ H := by
      have : α ^ ((95 : ℝ) / 100) ≤ (2 * S) ^ ((95 : ℝ) / 100) :=
        Real.rpow_le_rpow hα0 hα2 (by norm_num)
      linarith
    have hpow0 : 0 ≤ α ^ ((95 : ℝ) / 100) := Real.rpow_nonneg hα0 _
    have hgate' : ∫ u in α..(α + 2 * H),
        ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (u : ℂ) * I) *
          edPoly (hbCoeff N) (Finset.Icc 1 N) (((1 / 2 : ℝ) : ℂ) + (u : ℂ) * I)‖ ^ 2 ≤
          (Cg + 1) * (α + 2 * H - α + 2 * α ^ ((95 : ℝ) / 100)) := by
      refine (hgate α hα1 hα2).trans ?_
      have : α + 2 * H - α + 2 * α ^ ((95 : ℝ) / 100) = 2 * H + 2 * α ^ ((95 : ℝ) / 100) := by
        ring
      rw [this]
      nlinarith
    have h := integral_nearLineWindowField_left_gate_le (τ := τ) (σL := (1 / 2 : ℝ)) hH
      (by norm_num) (by norm_num) (by linarith) (by linarith) hgate' h95 hMVT hE
    linarith
  · have h := integral_nearLineWindowField_left_far_le (τ := τ) (y := y) (σL := (1 / 2 : ℝ))
      (D := S / 16) hH hCW hW (by norm_num) (by norm_num) (by positivity) (by linarith) hkey
    nlinarith

/-! ## The tail on the right-shifted line -/

/-- `(A x)^{1−λ} (B x y)^λ ≤ (A + B) x y^λ` for `0 ≤ λ ≤ 1`. -/
theorem rpow_mul_window_interp_le {A B x y lam : ℝ} (hA : 0 < A) (hB : 0 < B) (hx : 0 < x)
    (hy : 0 < y) (hl0 : 0 ≤ lam) (hl1 : lam ≤ 1) :
    (A * x) ^ (1 - lam) * (B * x * y) ^ lam ≤ (A + B) * x * y ^ lam := by
  have h1 : (A * x) ^ (1 - lam) * (B * x * y) ^ lam =
      (A ^ (1 - lam) * B ^ lam) * (x ^ (1 - lam) * x ^ lam) * y ^ lam := by
    rw [Real.mul_rpow hA.le hx.le, Real.mul_rpow (by positivity) hy.le,
      Real.mul_rpow hB.le hx.le]
    ring
  have hxx : x ^ (1 - lam) * x ^ lam = x := by
    rw [← Real.rpow_add hx, sub_add_cancel, Real.rpow_one]
  have hgm : A ^ (1 - lam) * B ^ lam ≤ (1 - lam) * A + lam * B :=
    Real.geom_mean_le_arith_mean2_weighted (by linarith) hl0 hA.le hB.le (by ring)
  have hab : (1 - lam) * A + lam * B ≤ A + B := by nlinarith
  rw [h1, hxx]
  have hy0 : 0 ≤ y ^ lam := Real.rpow_nonneg hy.le _
  have := mul_le_mul_of_nonneg_right (hgm.trans hab) (mul_nonneg hx.le hy0)
  nlinarith [this]

/-- The interpolation exponent bound: `Z^{−76λ} ≤ 2 e^{−(152/79) θ a}` for `Z ≥ S^θ/2`,
`λ = a/((79/2) log S)`, `0 ≤ a ≤ (log S)/2`. -/
theorem rpow_neg_interp_le {Z S θ a : ℝ} (hS : 1 < S) (ha : 0 ≤ a)
    (haL : a ≤ Real.log S / 2) (hZ : S ^ θ / 2 ≤ Z) (hZ1 : 1 ≤ S ^ θ / 2) :
    Z ^ (-(76 * (a / (79 / 2 * Real.log S)))) ≤ 2 * Real.exp (-(152 / 79 * θ * a)) := by
  have hL : 0 < Real.log S := Real.log_pos hS
  have hS0 : 0 < S := by linarith
  set lam : ℝ := a / (79 / 2 * Real.log S) with hlam
  have hlam0 : 0 ≤ lam := by rw [hlam]; positivity
  have hlam1 : 76 * lam ≤ 1 := by
    rw [hlam, mul_div_assoc', div_le_one (by positivity)]
    nlinarith
  have hZ0 : 0 < S ^ θ / 2 := by linarith
  have hmono : Z ^ (-(76 * lam)) ≤ (S ^ θ / 2) ^ (-(76 * lam)) :=
    Real.rpow_le_rpow_of_nonpos hZ0 hZ (by linarith)
  refine hmono.trans ?_
  rw [Real.div_rpow (Real.rpow_nonneg hS0.le _) (by norm_num), ← Real.rpow_mul hS0.le,
    div_eq_mul_inv]
  have h2 : ((2 : ℝ) ^ (-(76 * lam)))⁻¹ ≤ 2 := by
    rw [← Real.rpow_neg (by norm_num), neg_neg]
    calc (2 : ℝ) ^ (76 * lam) ≤ 2 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hlam1
      _ = 2 := Real.rpow_one 2
  have hSexp : S ^ (θ * -(76 * lam)) = Real.exp (-(152 / 79 * θ * a)) := by
    rw [Real.rpow_def_of_pos hS0]
    congr 1
    rw [hlam]
    field_simp
    ring
  rw [hSexp]
  have he : 0 ≤ Real.exp (-(152 / 79 * θ * a)) := (Real.exp_pos _).le
  nlinarith

/-- **One window of the tail** on `Re s = 1/2 + a/log S`, from three-lines between the critical
line and `Re s = 40`. -/
theorem integral_hbMollifiedTail_window_criticalGate_le {N : ℕ} (hN : 2 ≤ N)
    {S H τ CL CW θ a : ℝ} (hS : 1 < S) (ha : 0 ≤ a) (haL : a ≤ Real.log S / 2)
    (hNlo : S ^ θ / 2 ≤ N) (hN1 : 1 ≤ S ^ θ / 2)
    (hH : 40 ≤ H) (hCL : 0 < CL) (hCW : 0 ≤ CW)
    (hW : ∀ z : ℂ, 1 / 4 ≤ z.re → z.re ≤ 3 → ‖nearLineField N z‖ ≤ CW * N * (1 + |z.im|))
    (hτ : 1 + H ≤ τ)
    (hleft : ∀ y : ℝ, ∫ t in (τ - H)..(τ + H),
      ‖nearLineWindowField N H τ (((1 / 2 : ℝ) : ℂ) + ((y + t : ℝ) : ℂ) * I)‖ ^ 2 ≤ CL * H) :
    ∫ t in (τ - H)..(τ + H),
        ‖hbMollifiedTail N (((1 / 2 + a / Real.log S : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2 ≤
      4 * Real.exp 2 * (CL + 8 * Real.exp 2) * H * Real.exp (-(152 / 79 * θ * a)) := by
  have hL : 0 < Real.log S := Real.log_pos hS
  have hH0 : 0 < H := by linarith
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hδ : a / Real.log S ≤ 1 / 2 := by
    rw [div_le_iff₀ hL]; linarith
  have hδ0 : 0 ≤ a / Real.log S := div_nonneg ha hL.le
  have h := integral_hbMollifiedTail_window_le_farRight hN (σR := 40) (σL := 1 / 2)
    (σ₀ := 1 / 2 + a / Real.log S) (SL := CL * H) (by norm_num) hH hCW hW (by norm_num)
    (by linarith) (by linarith) (by linarith) hτ (by positivity) hleft
  refine h.trans ?_
  have hlam : (1 / 2 + a / Real.log S - 1 / 2) / (40 - 1 / 2) = a / (79 / 2 * Real.log S) := by
    field_simp
    ring
  rw [hlam]
  set lam : ℝ := a / (79 / 2 * Real.log S) with hlamdef
  have hlam0 : 0 ≤ lam := by rw [hlamdef]; positivity
  have hlam1 : lam ≤ 1 := by
    rw [hlamdef, div_le_one (by positivity)]
    nlinarith
  have hNpow : (N : ℝ) ^ (4 - 2 * (40 : ℝ)) = (N : ℝ) ^ (-76 : ℝ) := by norm_num
  have hy : 0 < (N : ℝ) ^ (-76 : ℝ) := Real.rpow_pos_of_pos hN0 _
  have hinterp := rpow_mul_window_interp_le (A := CL) (B := 8 * Real.exp 2) (x := H)
    (y := (N : ℝ) ^ (-76 : ℝ)) hCL (by positivity) hH0 hy hlam0 hlam1
  have hrw : ((N : ℝ) ^ (-76 : ℝ)) ^ lam = (N : ℝ) ^ (-(76 * lam)) := by
    rw [← Real.rpow_mul hN0.le]
    ring_nf
  have hdecay := rpow_neg_interp_le (Z := N) hS ha haL hNlo hN1
  rw [← hlamdef] at hdecay
  rw [hNpow]
  calc 2 * Real.exp 2 * ((CL * H) ^ (1 - lam) *
        (8 * Real.exp 2 * H * (N : ℝ) ^ (-76 : ℝ)) ^ lam)
      ≤ 2 * Real.exp 2 * ((CL + 8 * Real.exp 2) * H * ((N : ℝ) ^ (-76 : ℝ)) ^ lam) := by
        have e : 8 * Real.exp 2 * H * (N : ℝ) ^ (-76 : ℝ) =
            8 * Real.exp 2 * H * (N : ℝ) ^ (-76 : ℝ) := rfl
        gcongr
    _ = 2 * Real.exp 2 * ((CL + 8 * Real.exp 2) * H * (N : ℝ) ^ (-(76 * lam))) := by
        rw [hrw]
    _ ≤ 2 * Real.exp 2 * ((CL + 8 * Real.exp 2) * H *
          (2 * Real.exp (-(152 / 79 * θ * a)))) := by gcongr
    _ = 4 * Real.exp 2 * (CL + 8 * Real.exp 2) * H * Real.exp (-(152 / 79 * θ * a)) := by ring

/-- **The tail over a block**, by covering `[T₁, T₂]` with windows of length `2H`. -/
theorem integral_hbMollifiedTail_block_criticalGate_le {N : ℕ} {T₁ T₂ H W σ₀ : ℝ}
    (hH : 0 < H) (hT₁ : 0 < T₁) (hT : T₁ ≤ T₂) (hW0 : 0 ≤ W)
    (hwin : ∀ τ : ℝ, T₁ + H ≤ τ → τ < T₂ + H →
      ∫ t in (τ - H)..(τ + H), ‖hbMollifiedTail N ((σ₀ : ℂ) + (t : ℂ) * I)‖ ^ 2 ≤ W) :
    ∫ t in T₁..T₂, ‖hbMollifiedTail N ((σ₀ : ℂ) + (t : ℂ) * I)‖ ^ 2 ≤
      ((T₂ - T₁) / (2 * H) + 1) * W := by
  have hgc : ContinuousOn (fun t : ℝ => ‖hbMollifiedTail N ((σ₀ : ℂ) + (t : ℂ) * I)‖ ^ 2)
      (Ici T₁) := by
    intro t ht
    have hne : ((σ₀ : ℂ) + (t : ℂ) * I) ≠ 1 := by
      intro h
      have := congrArg Complex.im h
      simp at this
      linarith [ht.out]
    have hct : ContinuousAt (fun t : ℝ => hbMollifiedTail N ((σ₀ : ℂ) + (t : ℂ) * I)) t :=
      ContinuousAt.comp (g := hbMollifiedTail N) (f := fun t : ℝ => ((σ₀ : ℂ) + (t : ℂ) * I))
        (continuousAt_hbMollifiedTail hne) (by fun_prop)
    exact (hct.norm.pow 2).continuousWithinAt
  refine integral_le_of_windows (g := fun t : ℝ => ‖hbMollifiedTail N ((σ₀ : ℂ) + (t : ℂ) * I)‖ ^ 2)
    hH hT (fun t => by positivity) hgc hW0 (fun j hj => ?_)
  have hj0 : (0 : ℝ) ≤ 2 * j * H := by positivity
  have h := hwin (T₁ + (2 * j + 1) * H) (by nlinarith) (by nlinarith)
  have e1 : T₁ + (2 * j + 1) * H - H = T₁ + 2 * j * H := by ring
  have e2 : T₁ + (2 * j + 1) * H + H = T₁ + 2 * ((j + 1 : ℕ) : ℝ) * H := by push_cast; ring
  rw [e1, e2] at h
  exact h

/-! ## The mollified mean square -/

/-- `‖h + (p u − q v)/r‖² ≤ 2‖h‖² + 4K²(‖u‖² + ‖v‖²)` for `0 ≤ p, q ≤ K r`. -/
theorem normSq_add_twoLength_le {p q r K : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (hr : 0 < r)
    (hpK : p ≤ K * r) (hqK : q ≤ K * r) (h u v : ℂ) :
    ‖h + ((p : ℂ) * u - (q : ℂ) * v) / (r : ℂ)‖ ^ 2 ≤
      2 * ‖h‖ ^ 2 + 4 * K ^ 2 * (‖u‖ ^ 2 + ‖v‖ ^ 2) := by
  have hK : 0 ≤ K := by
    by_contra hK
    have := not_le.mp hK
    nlinarith
  have hg : ‖((p : ℂ) * u - (q : ℂ) * v) / (r : ℂ)‖ ≤ K * ‖u‖ + K * ‖v‖ := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr, div_le_iff₀ hr]
    have h1 : ‖(p : ℂ) * u - (q : ℂ) * v‖ ≤ p * ‖u‖ + q * ‖v‖ := by
      refine (norm_sub_le _ _).trans ?_
      rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
        Real.norm_eq_abs, abs_of_nonneg hp, abs_of_nonneg hq]
    have h2 : p * ‖u‖ ≤ K * r * ‖u‖ := mul_le_mul_of_nonneg_right hpK (norm_nonneg _)
    have h3 : q * ‖v‖ ≤ K * r * ‖v‖ := mul_le_mul_of_nonneg_right hqK (norm_nonneg _)
    nlinarith
  set g : ℂ := ((p : ℂ) * u - (q : ℂ) * v) / (r : ℂ)
  have hsum : ‖h + g‖ ≤ ‖h‖ + (K * ‖u‖ + K * ‖v‖) := (norm_add_le _ _).trans (by linarith)
  have h0 : 0 ≤ ‖h + g‖ := norm_nonneg _
  have hsq := pow_le_pow_left₀ h0 hsum 2
  nlinarith [sq_nonneg (‖h‖ - (K * ‖u‖ + K * ‖v‖)), sq_nonneg (K * ‖u‖ - K * ‖v‖),
    norm_nonneg h, norm_nonneg u, norm_nonneg v]

/-- `ζ(s) Σ_{d ≤ X} c_d d^{−s} = Σ_{d ≤ X} c_d · ζ(s) d^{−s} n^{s−2σ}|_{n=1}`. -/
theorem zeta_mul_edPoly_eq_sum_twistedZeta (c : ℕ → ℂ) (X : ℕ) (σ : ℝ) (s : ℂ) :
    riemannZeta s * edPoly c (Finset.Icc 1 X) s =
      ∑ d ∈ Finset.Icc 1 X, c d * twistedZeta σ d 1 s := by
  unfold edPoly twistedZeta
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  simp only [Nat.cast_one, Complex.ofReal_one, Complex.one_cpow, mul_one]
  ring

theorem intervalIntegrable_twistedZeta_line {σ : ℝ} {d n : ℕ} (hd : 1 ≤ d) (hn : 1 ≤ n)
    {A B : ℝ} (hA : 0 < A) (hAB : A ≤ B) :
    IntervalIntegrable (fun t : ℝ => twistedZeta σ d n ((σ : ℂ) + (t : ℂ) * I)) volume A B := by
  refine ContinuousOn.intervalIntegrable_of_Icc hAB fun t ht => ?_
  have hne : ((σ : ℂ) + (t : ℂ) * I) ≠ 1 := by
    intro h
    have := congrArg Complex.im h
    simp at this
    linarith [ht.1]
  exact (ContinuousAt.comp (g := twistedZeta σ d n) (f := fun t : ℝ => (σ : ℂ) + (t : ℂ) * I)
    (differentiableAt_twistedZeta σ hd hn hne).continuousAt (by fun_prop)).continuousWithinAt

/-- **First moment of the mollified zeta function** over `[T, 2T]`. -/
theorem norm_integral_zeta_mul_edPoly_sub_le {c : ℕ → ℂ} {X : ℕ} (hX : 1 ≤ X) (hc1 : c 1 = 1)
    (hc : ∀ n ∈ Finset.Icc 1 X, ‖c n‖ ≤ 1) {σ T : ℝ} (hσ : 1 / 2 ≤ σ) (hσ2 : σ ≤ 2)
    (hT : 4 ≤ T) :
    ‖(∫ t in T..(2 * T), riemannZeta ((σ : ℂ) + (t : ℂ) * I) *
        edPoly c (Finset.Icc 1 X) ((σ : ℂ) + (t : ℂ) * I)) - (T : ℂ)‖ ≤
      X * (27 * Real.sqrt T + 8) := by
  have hT0 : 0 < T := by linarith
  have hint : ∀ d ∈ Finset.Icc 1 X, IntervalIntegrable
      (fun t : ℝ => c d * twistedZeta σ d 1 ((σ : ℂ) + (t : ℂ) * I)) volume T (2 * T) :=
    fun d hd => (intervalIntegrable_twistedZeta_line (Finset.mem_Icc.mp hd).1 le_rfl hT0
      (by linarith)).const_mul _
  have hsum : (∫ t in T..(2 * T), riemannZeta ((σ : ℂ) + (t : ℂ) * I) *
        edPoly c (Finset.Icc 1 X) ((σ : ℂ) + (t : ℂ) * I)) =
      ∑ d ∈ Finset.Icc 1 X, c d * ∫ t in T..(2 * T), twistedZeta σ d 1 ((σ : ℂ) + (t : ℂ) * I) := by
    simp_rw [zeta_mul_edPoly_eq_sum_twistedZeta c X σ]
    rw [intervalIntegral.integral_finsetSum hint]
    refine Finset.sum_congr rfl fun d _ => ?_
    exact intervalIntegral.integral_const_mul _ _
  have hdiag : (T : ℂ) = ∑ d ∈ Finset.Icc 1 X,
      c d * (if d ∣ 1 then ((((1 : ℕ) : ℝ) ^ (-2 * σ) * T : ℝ) : ℂ) else 0) := by
    rw [Finset.sum_eq_single 1]
    · rw [hc1, if_pos (dvd_refl 1)]
      simp
    · intro d hd hd1
      rw [if_neg (fun h => hd1 (Nat.dvd_one.mp h)), mul_zero]
    · intro h1
      exact absurd (Finset.mem_Icc.mpr ⟨le_rfl, hX⟩) h1
  rw [hsum, hdiag, ← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ d ∈ Finset.Icc 1 X, ‖c d * (∫ t in T..(2 * T),
          twistedZeta σ d 1 ((σ : ℂ) + (t : ℂ) * I)) -
        c d * (if d ∣ 1 then ((((1 : ℕ) : ℝ) ^ (-2 * σ) * T : ℝ) : ℂ) else 0)‖
      ≤ ∑ _d ∈ Finset.Icc 1 X, (27 * Real.sqrt T + 8) := by
        refine Finset.sum_le_sum fun d hd => ?_
        rw [← mul_sub, norm_mul]
        have h1 := norm_integral_twistedZeta_sub_diag_le hσ hσ2 (Finset.mem_Icc.mp hd).1
          le_rfl hT
        have h2 := hc d hd
        simp only [Nat.cast_one, one_pow, mul_one] at h1 ⊢
        calc ‖c d‖ * ‖(∫ t in T..(2 * T), twistedZeta σ d 1 ((σ : ℂ) + (t : ℂ) * I)) -
              (if d ∣ 1 then (((1 : ℝ) ^ (-2 * σ) * T : ℝ) : ℂ) else 0)‖
            ≤ 1 * (27 * Real.sqrt T + 8) :=
              mul_le_mul h2 h1 (norm_nonneg _) zero_le_one
          _ = 27 * Real.sqrt T + 8 := one_mul _
    _ = X * (27 * Real.sqrt T + 8) := by
        rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
        simp

/-- Pointwise: `‖ζ(σ+it) Σ_{d≤X} c_d d^{−σ−it}‖ ≤ 9 X √T` for `t ∈ [T, 2T]`. -/
theorem norm_zeta_mul_edPoly_le {c : ℕ → ℂ} {X : ℕ}
    (hc : ∀ n ∈ Finset.Icc 1 X, ‖c n‖ ≤ 1) {σ T t : ℝ} (hσ : 1 / 2 ≤ σ) (hσ2 : σ ≤ 2)
    (hT : 4 ≤ T) (ht1 : T ≤ t) (ht2 : t ≤ 2 * T) :
    ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I) * edPoly c (Finset.Icc 1 X) ((σ : ℂ) + (t : ℂ) * I)‖ ≤
      X * (9 * Real.sqrt T) := by
  rw [zeta_mul_edPoly_eq_sum_twistedZeta c X σ]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ d ∈ Finset.Icc 1 X, ‖c d * twistedZeta σ d 1 ((σ : ℂ) + (t : ℂ) * I)‖
      ≤ ∑ _d ∈ Finset.Icc 1 X, 9 * Real.sqrt T := by
        refine Finset.sum_le_sum fun d hd => ?_
        rw [norm_mul]
        have h1 := norm_twistedZeta_horizontal_le hσ (Finset.mem_Icc.mp hd).1 le_rfl hT ht1 ht2
          le_rfl hσ2
        simp only [Nat.cast_one, mul_one] at h1
        calc ‖c d‖ * ‖twistedZeta σ d 1 ((σ : ℂ) + (t : ℂ) * I)‖ ≤ 1 * (9 * Real.sqrt T) :=
              mul_le_mul (hc d hd) h1 (norm_nonneg _) zero_le_one
          _ = 9 * Real.sqrt T := one_mul _
    _ = X * (9 * Real.sqrt T) := by
        rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
        simp

/-- **First moment over an admissible block** `[T₁, T₂] ⊆ [T, 2T]` with `T₁ − T, 2T − T₂ ≤ 1`. -/
theorem norm_integral_zeta_mul_edPoly_sub_one_block_le {c : ℕ → ℂ} {X : ℕ} (hX : 1 ≤ X)
    (hc1 : c 1 = 1) (hc : ∀ n ∈ Finset.Icc 1 X, ‖c n‖ ≤ 1) {σ T T₁ T₂ : ℝ} (hσ : 1 / 2 ≤ σ)
    (hσ2 : σ ≤ 2) (hT : 4 ≤ T) (hT₁ : T ≤ T₁) (hT₁' : T₁ ≤ T + 1) (hT₂ : 2 * T - 1 ≤ T₂)
    (hT₂' : T₂ ≤ 2 * T) (hT12 : T₁ ≤ T₂) :
    ‖∫ t in T₁..T₂, (riemannZeta ((σ : ℂ) + (t : ℂ) * I) *
        edPoly c (Finset.Icc 1 X) ((σ : ℂ) + (t : ℂ) * I) - 1)‖ ≤
      2 + X * (45 * Real.sqrt T + 8) := by
  have hT0 : 0 < T := by linarith
  set F : ℝ → ℂ := fun t => riemannZeta ((σ : ℂ) + (t : ℂ) * I) *
    edPoly c (Finset.Icc 1 X) ((σ : ℂ) + (t : ℂ) * I) with hF
  have hs : ∀ n ∈ Finset.Icc 1 X, 1 ≤ n := fun n hn => (Finset.mem_Icc.mp hn).1
  have hFc : ∀ A B : ℝ, 0 < A → A ≤ B → IntervalIntegrable F volume A B := by
    intro A B hA hAB
    refine ContinuousOn.intervalIntegrable_of_Icc hAB fun t ht => ?_
    have hne : ((σ : ℂ) + (t : ℂ) * I) ≠ 1 := by
      intro h
      have := congrArg Complex.im h
      simp at this
      linarith [ht.1]
    exact ((ContinuousAt.comp (g := riemannZeta) (f := fun t : ℝ => (σ : ℂ) + (t : ℂ) * I)
      (differentiableAt_riemannZeta hne).continuousAt (by fun_prop)).mul
      (ContinuousAt.comp (g := edPoly c (Finset.Icc 1 X))
        (f := fun t : ℝ => (σ : ℂ) + (t : ℂ) * I)
        (differentiable_edPoly _ hs _).continuousAt (by fun_prop))).continuousWithinAt
  have hsplit : (∫ t in T₁..T₂, F t) = (∫ t in T..(2 * T), F t) - (∫ t in T..T₁, F t) -
      ∫ t in T₂..(2 * T), F t := by
    have h1 := intervalIntegral.integral_add_adjacent_intervals (hFc T T₁ hT0 hT₁)
      (hFc T₁ T₂ (by linarith) hT12)
    have h2 := intervalIntegral.integral_add_adjacent_intervals
      ((hFc T T₁ hT0 hT₁).trans (hFc T₁ T₂ (by linarith) hT12)) (hFc T₂ (2 * T) (by linarith) hT₂')
    rw [← h2, ← h1]
    ring
  have hpiece : ∀ A B : ℝ, T ≤ A → A ≤ B → B ≤ 2 * T → B - A ≤ 1 →
      ‖∫ t in A..B, F t‖ ≤ X * (9 * Real.sqrt T) := by
    intro A B hA hAB hB hBA
    have hb : ∀ t ∈ Set.uIoc A B, ‖F t‖ ≤ X * (9 * Real.sqrt T) := by
      intro t ht
      rw [Set.uIoc_of_le hAB] at ht
      exact norm_zeta_mul_edPoly_le hc hσ hσ2 hT (by linarith [ht.1]) (by linarith [ht.2])
    refine (intervalIntegral.norm_integral_le_of_norm_le_const hb).trans ?_
    rw [abs_of_nonneg (by linarith)]
    have : 0 ≤ (X : ℝ) * (9 * Real.sqrt T) := by positivity
    nlinarith
  have hfirst := norm_integral_zeta_mul_edPoly_sub_le hX hc1 hc hσ hσ2 hT
  have hp1 := hpiece T T₁ le_rfl hT₁ (by linarith) (by linarith)
  have hp2 := hpiece T₂ (2 * T) (by linarith) hT₂' le_rfl (by linarith)
  have hint1 : IntervalIntegrable (fun _ : ℝ => (1 : ℂ)) volume T₁ T₂ := intervalIntegrable_const
  rw [intervalIntegral.integral_sub (hFc T₁ T₂ (by linarith) hT12) hint1, hsplit,
    intervalIntegral.integral_const, Complex.real_smul, mul_one]
  have hlen : ‖(T : ℂ) - (((T₂ - T₁ : ℝ) : ℂ))‖ ≤ 2 := by
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> linarith
  have hkey : (∫ t in T..(2 * T), F t) - (∫ t in T..T₁, F t) - (∫ t in T₂..(2 * T), F t) -
      (((T₂ - T₁ : ℝ) : ℂ)) = ((∫ t in T..(2 * T), F t) - (T : ℂ)) +
        ((T : ℂ) - (((T₂ - T₁ : ℝ) : ℂ))) - (∫ t in T..T₁, F t) - ∫ t in T₂..(2 * T), F t := by
    ring
  rw [hkey]
  have hs0 : 0 ≤ Real.sqrt T := Real.sqrt_nonneg _
  calc ‖((∫ t in T..(2 * T), F t) - (T : ℂ)) + ((T : ℂ) - (((T₂ - T₁ : ℝ) : ℂ))) -
        (∫ t in T..T₁, F t) - ∫ t in T₂..(2 * T), F t‖
      ≤ ‖(∫ t in T..(2 * T), F t) - (T : ℂ)‖ + ‖(T : ℂ) - (((T₂ - T₁ : ℝ) : ℂ))‖ +
          ‖∫ t in T..T₁, F t‖ + ‖∫ t in T₂..(2 * T), F t‖ := by
        refine (norm_sub_le _ _).trans (add_le_add ((norm_sub_le _ _).trans
          (add_le_add (norm_add_le _ _) le_rfl)) le_rfl)
    _ ≤ X * (27 * Real.sqrt T + 8) + 2 + X * (9 * Real.sqrt T) + X * (9 * Real.sqrt T) := by
        gcongr
    _ = 2 + X * (45 * Real.sqrt T + 8) := by ring

/-- `∫ ‖1 + w‖² ≤ (B − A) + 2‖∫ w‖ + ∫ ‖w‖²`. -/
theorem integral_normSq_one_add_le {w : ℝ → ℂ} {A B : ℝ} (hAB : A ≤ B)
    (hw : ContinuousOn w (Icc A B)) :
    ∫ t in A..B, ‖1 + w t‖ ^ 2 ≤ (B - A) + 2 * ‖∫ t in A..B, w t‖ + ∫ t in A..B, ‖w t‖ ^ 2 := by
  have hpt : ∀ t, ‖1 + w t‖ ^ 2 = 1 + 2 * (w t).re + ‖w t‖ ^ 2 := by
    intro t
    rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_add]
    simp [Complex.normSq_one]
    ring
  have hwi : IntervalIntegrable w volume A B := hw.intervalIntegrable_of_Icc hAB
  have hre : IntervalIntegrable (fun t => 2 * (w t).re) volume A B :=
    ((Complex.continuous_re.comp_continuousOn hw).intervalIntegrable_of_Icc hAB).const_mul 2
  have hsq : IntervalIntegrable (fun t => ‖w t‖ ^ 2) volume A B :=
    (hw.norm.pow 2).intervalIntegrable_of_Icc hAB
  have hcomm : (∫ t in A..B, (w t).re) = (∫ t in A..B, w t).re := by
    have := Complex.reCLM.intervalIntegral_comp_comm hwi
    simpa using this
  simp_rw [hpt]
  rw [intervalIntegral.integral_add (intervalIntegrable_const.add hre) hsq,
    intervalIntegral.integral_add intervalIntegrable_const hre, intervalIntegral.integral_const,
    intervalIntegral.integral_const_mul, hcomm, smul_eq_mul, mul_one]
  have h := Complex.re_le_norm (∫ t in A..B, w t)
  linarith

/-- `Y^{−2a/L} ≤ 2 e^{−(22/25) a}` for `Y ≥ S^{23/50}/2`, `L = log S`, `0 ≤ a ≤ L/2`. -/
theorem rpow_neg_two_shift_le {Y S a : ℝ} (hS : 1 < S) (ha : 0 ≤ a)
    (haL : a ≤ Real.log S / 2) (hY : S ^ (23 / 50 : ℝ) / 2 ≤ Y) (hY1 : 1 ≤ S ^ (23 / 50 : ℝ) / 2) :
    Y ^ (-(2 * (a / Real.log S))) ≤ 2 * Real.exp (-(22 / 25 * a)) := by
  have hL : 0 < Real.log S := Real.log_pos hS
  have hS0 : 0 < S := by linarith
  have hZ0 : 0 < S ^ (23 / 50 : ℝ) / 2 := by linarith
  have hδ0 : 0 ≤ a / Real.log S := div_nonneg ha hL.le
  have hδ1 : 2 * (a / Real.log S) ≤ 1 := by
    rw [mul_div_assoc', div_le_one hL]; linarith
  refine (Real.rpow_le_rpow_of_nonpos hZ0 hY (by linarith)).trans ?_
  rw [Real.div_rpow (Real.rpow_nonneg hS0.le _) (by norm_num), ← Real.rpow_mul hS0.le,
    div_eq_mul_inv]
  have h2 : ((2 : ℝ) ^ (-(2 * (a / Real.log S))))⁻¹ ≤ 2 := by
    rw [← Real.rpow_neg (by norm_num), neg_neg]
    calc (2 : ℝ) ^ (2 * (a / Real.log S)) ≤ 2 ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) hδ1
      _ = 2 := Real.rpow_one 2
  have hSexp : S ^ ((23 / 50 : ℝ) * -(2 * (a / Real.log S))) = Real.exp (-(23 / 25 * a)) := by
    rw [Real.rpow_def_of_pos hS0]
    congr 1
    field_simp
    ring
  have hmono : Real.exp (-(23 / 25 * a)) ≤ Real.exp (-(22 / 25 * a)) :=
    Real.exp_le_exp.mpr (by linarith)
  rw [hSexp]
  have he : 0 ≤ Real.exp (-(23 / 25 * a)) := (Real.exp_pos _).le
  nlinarith

/-- **The tail over a block at rate `22/25`.** -/
theorem integral_hbMollifiedTail_block_criticalGate_rate_le {N : ℕ} (hN : 2 ≤ N)
    {S H T₁ T₂ a θ CL CW : ℝ} (hS : 1 < S) (hH : 40 ≤ H) (hT₁1 : 1 ≤ T₁) (h2H : 2 * H ≤ T₂ - T₁)
    (ha : 0 ≤ a) (haL : a ≤ Real.log S / 2) (hNlo : S ^ θ / 2 ≤ N) (hN1 : 1 ≤ S ^ θ / 2)
    (hCL : 0 < CL) (hCW : 0 ≤ CW) (hθ : (22 / 25 : ℝ) * a ≤ 152 / 79 * θ * a)
    (hW : ∀ z : ℂ, 1 / 4 ≤ z.re → z.re ≤ 3 → ‖nearLineField N z‖ ≤ CW * N * (1 + |z.im|))
    (hleft : ∀ τ : ℝ, T₁ + H ≤ τ → τ < T₂ + H → ∀ y : ℝ, ∫ t in (τ - H)..(τ + H),
      ‖nearLineWindowField N H τ (((1 / 2 : ℝ) : ℂ) + ((y + t : ℝ) : ℂ) * I)‖ ^ 2 ≤ CL * H) :
    ∫ t in T₁..T₂, ‖hbMollifiedTail N (((1 / 2 + a / Real.log S : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2 ≤
      (T₂ - T₁) * (4 * Real.exp 2 * (CL + 8 * Real.exp 2) * Real.exp (-(22 / 25 * a))) := by
  have hH0 : 0 < H := by linarith
  have hT12 : T₁ ≤ T₂ := by linarith
  have hW0 : 0 ≤ 4 * Real.exp 2 * (CL + 8 * Real.exp 2) * H * Real.exp (-(22 / 25 * a)) := by
    positivity
  have hblock := integral_hbMollifiedTail_block_criticalGate_le (N := N)
    (σ₀ := 1 / 2 + a / Real.log S) hH0 (by linarith) hT12 hW0 (fun τ h1 h2 => by
      have h := integral_hbMollifiedTail_window_criticalGate_le hN (τ := τ) hS ha haL hNlo
        hN1 hH hCL hCW hW (by linarith) (hleft τ h1 h2)
      refine h.trans ?_
      have he : Real.exp (-(152 / 79 * θ * a)) ≤ Real.exp (-(22 / 25 * a)) :=
        Real.exp_le_exp.mpr (by linarith)
      have : 0 ≤ 4 * Real.exp 2 * (CL + 8 * Real.exp 2) * H := by positivity
      exact mul_le_mul_of_nonneg_left he this)
  refine hblock.trans ?_
  have hratio : (T₂ - T₁) / (2 * H) + 1 ≤ (T₂ - T₁) / H := by
    rw [div_add_one (by positivity), div_le_div_iff₀ (by positivity) hH0]
    nlinarith
  calc ((T₂ - T₁) / (2 * H) + 1) *
        (4 * Real.exp 2 * (CL + 8 * Real.exp 2) * H * Real.exp (-(22 / 25 * a)))
      ≤ (T₂ - T₁) / H *
          (4 * Real.exp 2 * (CL + 8 * Real.exp 2) * H * Real.exp (-(22 / 25 * a))) :=
        mul_le_mul_of_nonneg_right hratio hW0
    _ = (T₂ - T₁) * (4 * Real.exp 2 * (CL + 8 * Real.exp 2) * Real.exp (-(22 / 25 * a))) := by
        field_simp

/-- `log X (log X + C_M)/(log X − log Y)² ≤ 30000` for `log X ≤ (47/100)L`, `log X − log Y ≥ L/200`,
`|C_M| ≤ L`. -/
theorem twoLength_head_ratio_le {lX lY L CM : ℝ} (hL : 0 < L) (hlX0 : 0 ≤ lX)
    (hlX : lX ≤ 47 / 100 * L) (hgap : L / 200 ≤ lX - lY) (hCMabs : |CM| ≤ L) :
    lX * (lX + CM) / (lX - lY) ^ 2 ≤ 30000 := by
  have hgap0 : 0 < lX - lY := by
    have : 0 < L / 200 := by positivity
    linarith
  rw [div_le_iff₀ (by positivity)]
  have hCM' : CM ≤ L := (le_abs_self CM).trans hCMabs
  have h1 : lX * (lX + CM) ≤ 47 / 100 * L * (2 * L) := by
    have : lX + CM ≤ 2 * L := by linarith
    rcases le_or_gt 0 (lX + CM) with hc | hc
    · exact mul_le_mul hlX this hc (by positivity)
    · nlinarith
  have h2 : (L / 200) ^ 2 ≤ (lX - lY) ^ 2 := pow_le_pow_left₀ (by positivity) hgap 2
  nlinarith

/-- **The head on `Re s = 1/2 + a/log S`** has mean square `≤ 120000 (T₂ − T₁) e^{−22a/25}`. -/
theorem integral_normSq_twoLengthHead_criticalGate_le {X Y : ℕ} {S T₁ T₂ a CM : ℝ}
    (hS : 1 < S) (hY1' : 1 ≤ Y) (hYX : Y < X) (hYlo : S ^ (23 / 50 : ℝ) / 2 ≤ Y)
    (hY1 : 1 ≤ S ^ (23 / 50 : ℝ) / 2)
    (hlogX : Real.log X ≤ 47 / 100 * Real.log S) (hgap : Real.log S / 200 ≤ Real.log X - Real.log Y)
    (hT12 : T₁ ≤ T₂) (hMVT : 8 * X * (1 + Real.log X) ≤ T₂ - T₁)
    (ha : 0 ≤ a) (haL : a ≤ Real.log S / 2)
    (hCM : ∑ k ∈ Finset.Icc 1 X, ArithmeticFunction.vonMangoldt k ^ (2 : ℕ) / (k : ℝ) ≤
      Real.log X * (Real.log X + CM)) (hCMabs : |CM| ≤ Real.log S) :
    (∫ τ in T₁..T₂, ‖edPoly (twoLengthHeadCoeff X Y) (Finset.Icc 1 X)
        (((1 / 2 + a / Real.log S : ℝ) : ℂ) + (τ : ℂ) * I)‖ ^ 2) ≤
      (T₂ - T₁) * (120000 * Real.exp (-(22 / 25 * a))) := by
  have hL : 0 < Real.log S := Real.log_pos hS
  have hhead := integral_normSq_twoLengthHead_le hY1' hYX (δ := a / Real.log S)
    (by positivity) hCM hT12
  have hpt : ∀ τ : ℝ, displacedLinePt (-(a / Real.log S)) τ =
      (((1 / 2 + a / Real.log S : ℝ) : ℂ) + (τ : ℂ) * I) := by
    intro τ
    unfold displacedLinePt
    congr 2
    ring
  simp only [hpt] at hhead
  refine hhead.trans ?_
  have hYpow := rpow_neg_two_shift_le (Y := Y) hS ha haL hYlo hY1
  have hlogX0 : 0 ≤ Real.log X := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ X))
  have hratio := twoLength_head_ratio_le hL hlogX0 hlogX hgap hCMabs
  have hYp0 : 0 ≤ (Y : ℝ) ^ (-(2 * (a / Real.log S))) := Real.rpow_nonneg (by positivity) _
  have hE0 : 0 < Real.exp (-(22 / 25 * a)) := Real.exp_pos _
  have hfac : 0 ≤ T₂ - T₁ + 8 * X * (1 + Real.log X) := by
    have : 0 ≤ 8 * (X : ℝ) * (1 + Real.log X) := by positivity
    linarith
  set q : ℝ := Real.log X * (Real.log X + CM) / (Real.log X - Real.log Y) ^ 2 with hq
  have hrw : (T₂ - T₁ + 8 * X * (1 + Real.log X)) * ((Y : ℝ) ^ (-(2 * (a / Real.log S))) *
      (Real.log X * (Real.log X + CM)) / (Real.log X - Real.log Y) ^ 2) =
      (T₂ - T₁ + 8 * X * (1 + Real.log X)) * ((Y : ℝ) ^ (-(2 * (a / Real.log S))) * q) := by
    rw [hq]; ring
  rw [hrw]
  rcases le_or_gt 0 q with hc0 | hc0
  · calc (T₂ - T₁ + 8 * X * (1 + Real.log X)) * ((Y : ℝ) ^ (-(2 * (a / Real.log S))) * q)
        ≤ (2 * (T₂ - T₁)) * ((2 * Real.exp (-(22 / 25 * a))) * 30000) :=
          mul_le_mul (by linarith) (mul_le_mul hYpow hratio hc0 (by positivity))
            (mul_nonneg hYp0 hc0) (by linarith)
      _ = (T₂ - T₁) * (120000 * Real.exp (-(22 / 25 * a))) := by ring
  · have h1 : (Y : ℝ) ^ (-(2 * (a / Real.log S))) * q ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hYp0 hc0.le
    have h2 : (T₂ - T₁ + 8 * X * (1 + Real.log X)) * ((Y : ℝ) ^ (-(2 * (a / Real.log S))) * q) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hfac h1
    have h3 : 0 ≤ (T₂ - T₁) * (120000 * Real.exp (-(22 / 25 * a))) := by
      have : 0 ≤ T₂ - T₁ := by linarith
      positivity
    linarith

/-- Pointwise: `‖ζM − 1‖² ≤ 2‖H‖² + 4·94²(‖f_X‖² + ‖f_Y‖²)` for the two-length mollifier. -/
theorem normSq_zetaTwoLength_sub_one_le {X Y : ℕ} (hY2 : 2 ≤ Y) (hYX : Y < X) {L : ℝ}
    (hlogX : Real.log X ≤ 47 / 100 * L) (hgap : L / 200 ≤ Real.log X - Real.log Y) (hL : 0 < L)
    (z : ℂ) :
    ‖riemannZeta z * edPoly (twoLengthCoeff X Y) (Finset.Icc 1 X) z - 1‖ ^ 2 ≤
      2 * ‖edPoly (twoLengthHeadCoeff X Y) (Finset.Icc 1 X) z‖ ^ 2 + 4 * 94 ^ 2 *
        (‖hbMollifiedTail X z‖ ^ 2 + ‖hbMollifiedTail Y z‖ ^ 2) := by
  have hlogX0 : 0 ≤ Real.log X := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ X))
  have hlogY0 : 0 ≤ Real.log Y := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ Y))
  have hgap0 : 0 < Real.log X - Real.log Y := by
    have : 0 < L / 200 := by positivity
    linarith
  have hlogYX : Real.log Y ≤ Real.log X :=
    Real.log_le_log (by exact_mod_cast (by omega : 0 < Y)) (by exact_mod_cast hYX.le)
  have hK : Real.log X ≤ 94 * (Real.log X - Real.log Y) := by nlinarith
  have hK' : Real.log Y ≤ 94 * (Real.log X - Real.log Y) := le_trans hlogYX hK
  rw [zeta_mul_twoLength_eq hY2 hYX, add_sub_cancel_left]
  exact normSq_add_twoLength_le hlogX0 hlogY0 hgap0 hK hK' _ _ _

/-- The mollified mean square from the head, the two tails and the first moment. -/
theorem integral_normSq_zetaTwoLength_le_of_bounds {X Y : ℕ} (hY2 : 2 ≤ Y) (hYX : Y < X)
    {L σ₀ T₁ T₂ BH BX BY BF : ℝ} (hlogX : Real.log X ≤ 47 / 100 * L)
    (hgap : L / 200 ≤ Real.log X - Real.log Y) (hL : 0 < L) (hT₁0 : 0 < T₁) (hT12 : T₁ ≤ T₂)
    (hBH : ∫ t in T₁..T₂, ‖edPoly (twoLengthHeadCoeff X Y) (Finset.Icc 1 X)
      ((σ₀ : ℂ) + (t : ℂ) * I)‖ ^ 2 ≤ BH)
    (hBX : ∫ t in T₁..T₂, ‖hbMollifiedTail X ((σ₀ : ℂ) + (t : ℂ) * I)‖ ^ 2 ≤ BX)
    (hBY : ∫ t in T₁..T₂, ‖hbMollifiedTail Y ((σ₀ : ℂ) + (t : ℂ) * I)‖ ^ 2 ≤ BY)
    (hBF : 2 * ‖∫ t in T₁..T₂, (riemannZeta ((σ₀ : ℂ) + (t : ℂ) * I) *
      edPoly (twoLengthCoeff X Y) (Finset.Icc 1 X) ((σ₀ : ℂ) + (t : ℂ) * I) - 1)‖ ≤ BF) :
    ∫ t in T₁..T₂, ‖riemannZeta ((σ₀ : ℂ) + (t : ℂ) * I) *
        edPoly (twoLengthCoeff X Y) (Finset.Icc 1 X) ((σ₀ : ℂ) + (t : ℂ) * I)‖ ^ 2 ≤
      (T₂ - T₁) + BF + (2 * BH + 4 * 94 ^ 2 * (BX + BY)) := by
  have hs : ∀ n ∈ Finset.Icc 1 X, 1 ≤ n := fun n hn => (Finset.mem_Icc.mp hn).1
  have hwc : ContinuousOn (fun t : ℝ => riemannZeta ((σ₀ : ℂ) + (t : ℂ) * I) *
      edPoly (twoLengthCoeff X Y) (Finset.Icc 1 X) ((σ₀ : ℂ) + (t : ℂ) * I) - 1) (Icc T₁ T₂) := by
    intro t ht
    have hne : ((σ₀ : ℂ) + (t : ℂ) * I) ≠ 1 := by
      intro h
      have := congrArg Complex.im h
      simp at this
      linarith [ht.1]
    exact (((ContinuousAt.comp (g := riemannZeta) (f := fun t : ℝ => (σ₀ : ℂ) + (t : ℂ) * I)
      (differentiableAt_riemannZeta hne).continuousAt (by fun_prop)).mul
      (ContinuousAt.comp (g := edPoly (twoLengthCoeff X Y) (Finset.Icc 1 X))
        (f := fun t : ℝ => (σ₀ : ℂ) + (t : ℂ) * I)
        (differentiable_edPoly _ hs _).continuousAt (by fun_prop))).sub
          continuousAt_const).continuousWithinAt
  have hMsq := integral_normSq_one_add_le hT12 hwc
  simp only [add_sub_cancel] at hMsq
  have hPc : ContinuousOn (fun t : ℝ => edPoly (twoLengthHeadCoeff X Y) (Finset.Icc 1 X)
      ((σ₀ : ℂ) + (t : ℂ) * I)) (Icc T₁ T₂) :=
    ((differentiable_edPoly _ hs).continuous.comp (by fun_prop)).continuousOn
  have hiP : IntervalIntegrable (fun t : ℝ => ‖edPoly (twoLengthHeadCoeff X Y) (Finset.Icc 1 X)
      ((σ₀ : ℂ) + (t : ℂ) * I)‖ ^ 2) volume T₁ T₂ := (hPc.norm.pow 2).intervalIntegrable_of_Icc hT12
  have hiX : IntervalIntegrable (fun t : ℝ => ‖hbMollifiedTail X ((σ₀ : ℂ) + (t : ℂ) * I)‖ ^ 2)
      volume T₁ T₂ :=
    ((continuousOn_hbMollifiedTail_line X σ₀ (T₂ := T₂) hT₁0).norm.pow 2).intervalIntegrable_of_Icc
      hT12
  have hiY : IntervalIntegrable (fun t : ℝ => ‖hbMollifiedTail Y ((σ₀ : ℂ) + (t : ℂ) * I)‖ ^ 2)
      volume T₁ T₂ :=
    ((continuousOn_hbMollifiedTail_line Y σ₀ (T₂ := T₂) hT₁0).norm.pow 2).intervalIntegrable_of_Icc
      hT12
  have hiw : IntervalIntegrable (fun t : ℝ => ‖riemannZeta ((σ₀ : ℂ) + (t : ℂ) * I) *
      edPoly (twoLengthCoeff X Y) (Finset.Icc 1 X) ((σ₀ : ℂ) + (t : ℂ) * I) - 1‖ ^ 2)
      volume T₁ T₂ := (hwc.norm.pow 2).intervalIntegrable_of_Icc hT12
  have hmono := intervalIntegral.integral_mono_on hT12 hiw
    ((hiP.const_mul 2).add ((hiX.add hiY).const_mul (4 * 94 ^ 2)))
    (fun t _ => normSq_zetaTwoLength_sub_one_le hY2 hYX hlogX hgap hL _)
  rw [intervalIntegral.integral_add (hiP.const_mul 2) ((hiX.add hiY).const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add hiX hiY] at hmono
  have hsum : 2 * (∫ t in T₁..T₂, ‖edPoly (twoLengthHeadCoeff X Y) (Finset.Icc 1 X)
        ((σ₀ : ℂ) + (t : ℂ) * I)‖ ^ 2) + 4 * 94 ^ 2 *
      ((∫ t in T₁..T₂, ‖hbMollifiedTail X ((σ₀ : ℂ) + (t : ℂ) * I)‖ ^ 2) +
        ∫ t in T₁..T₂, ‖hbMollifiedTail Y ((σ₀ : ℂ) + (t : ℂ) * I)‖ ^ 2) ≤
      2 * BH + 4 * 94 ^ 2 * (BX + BY) := by
    have := add_le_add hBX hBY
    nlinarith
  linarith

/-! ## The count -/

/-- **Littlewood count from the mollified mean square** with offset `Δ = a/(50L)`. -/
theorem twoLength_criticalGate_count_le {X Y : ℕ} {C K L a A₀ E T₁ T₂ Mb : ℝ} (hK : 0 < K) (hL : 1 ≤ L) (ha : 0 ≤ a)
    (hcons : ∀ σ₀ Msq : ℝ, 1 / 4 ≤ σ₀ → σ₀ < 2 →
      (∀ x ∈ Set.Icc σ₀ (15 / 2 : ℝ), riemannZeta ((x : ℂ) + (T₁ : ℂ) * I) ≠ 0) →
      (∀ x ∈ Set.Icc σ₀ (15 / 2 : ℝ), riemannZeta ((x : ℂ) + (T₂ : ℂ) * I) ≠ 0) →
      (∀ x ∈ Set.Icc σ₀ (15 / 2 : ℝ),
        edPoly (twoLengthCoeff X Y) (Finset.Icc 1 X) ((x : ℂ) + (T₁ : ℂ) * I) ≠ 0) →
      (∀ x ∈ Set.Icc σ₀ (15 / 2 : ℝ),
        edPoly (twoLengthCoeff X Y) (Finset.Icc 1 X) ((x : ℂ) + (T₂ : ℂ) * I) ≠ 0) →
      (∫ t in T₁..T₂, ‖riemannZeta ((σ₀ : ℂ) + (t : ℂ) * I) *
          edPoly (twoLengthCoeff X Y) (Finset.Icc 1 X) ((σ₀ : ℂ) + (t : ℂ) * I)‖ ^ 2) ≤ Msq →
      ∀ Z : Finset ℂ, (∀ z : ℂ, z ∈ Z ↔
          z ∈ (uIcc (1 / 2 : ℝ) (15 / 2) ×ℂ uIcc T₁ T₂) ∧ riemannZeta z = 0) →
      ∀ Δ : ℝ, 0 ≤ Δ →
        2 * Real.pi * (Δ * ∑ w ∈ Z.filter (fun w => σ₀ + Δ ≤ w.re),
            ((analyticOrderAt riemannZeta w).toNat : ℝ))
          ≤ (T₂ - T₁) / 2 * Real.log (Msq / (T₂ - T₁)) + C + K * (Real.log T₂ + Real.log Mb))
    (hT12 : T₁ < T₂) (hlogT₂ : Real.log T₂ ≤ 2 * L) (hlogMb : Real.log Mb ≤ 3 * L)
    (hσ₀ : 1 / 4 ≤ 1 / 2 + a / L) (hσ₀' : 1 / 2 + a / L < 2) (hA₀E : 0 ≤ A₀ * E)
    (hG1 : ∀ x ∈ Set.Icc (1 / 2 + a / L) (15 / 2 : ℝ), riemannZeta ((x : ℂ) + (T₁ : ℂ) * I) ≠ 0)
    (hG2 : ∀ x ∈ Set.Icc (1 / 2 + a / L) (15 / 2 : ℝ), riemannZeta ((x : ℂ) + (T₂ : ℂ) * I) ≠ 0)
    (hP1 : ∀ x ∈ Set.Icc (1 / 2 + a / L) (15 / 2 : ℝ),
      edPoly (twoLengthCoeff X Y) (Finset.Icc 1 X) ((x : ℂ) + (T₁ : ℂ) * I) ≠ 0)
    (hP2 : ∀ x ∈ Set.Icc (1 / 2 + a / L) (15 / 2 : ℝ),
      edPoly (twoLengthCoeff X Y) (Finset.Icc 1 X) ((x : ℂ) + (T₂ : ℂ) * I) ≠ 0)
    (hMsq : ∫ t in T₁..T₂, ‖riemannZeta (((1 / 2 + a / L : ℝ) : ℂ) + (t : ℂ) * I) *
        edPoly (twoLengthCoeff X Y) (Finset.Icc 1 X) (((1 / 2 + a / L : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2 ≤
      (T₂ - T₁) * (1 + A₀ * E))
    (Z : Finset ℂ) (hZ : ∀ z : ℂ, z ∈ Z ↔
      z ∈ (uIcc (1 / 2 : ℝ) (15 / 2) ×ℂ uIcc T₁ T₂) ∧ riemannZeta z = 0) :
    2 * Real.pi * ((a / L) * ∑ w ∈ Z.filter (fun w => 1 / 2 + 51 / 50 * (a / L) ≤ w.re),
        ((analyticOrderAt riemannZeta w).toNat : ℝ)) ≤
      (T₂ - T₁) * (25 * (A₀ * E)) + (50 * |C| + 250 * K) * L := by
  have hL0 : 0 < L := by linarith
  have hT0 : 0 < T₂ - T₁ := by linarith
  have hΔ : 0 ≤ a / L / 50 := by positivity
  have h := hcons (1 / 2 + a / L) ((T₂ - T₁) * (1 + A₀ * E)) hσ₀ hσ₀' hG1 hG2 hP1 hP2 hMsq Z hZ
    (a / L / 50) hΔ
  have hfilter : Z.filter (fun w => 1 / 2 + a / L + a / L / 50 ≤ w.re) =
      Z.filter (fun w => 1 / 2 + 51 / 50 * (a / L) ≤ w.re) := by
    refine Finset.filter_congr fun w _ => ?_
    constructor <;> intro hw <;> linarith
  rw [hfilter] at h
  have hlog : Real.log ((T₂ - T₁) * (1 + A₀ * E) / (T₂ - T₁)) ≤ A₀ * E := by
    rw [mul_div_cancel_left₀ _ hT0.ne']
    have := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < 1 + A₀ * E)
    linarith
  have h1 : (T₂ - T₁) / 2 * Real.log ((T₂ - T₁) * (1 + A₀ * E) / (T₂ - T₁)) ≤
      (T₂ - T₁) / 2 * (A₀ * E) := mul_le_mul_of_nonneg_left hlog (by linarith)
  have h2 : K * (Real.log T₂ + Real.log Mb) ≤ K * (5 * L) :=
    mul_le_mul_of_nonneg_left (by linarith) hK.le
  have hC : C ≤ |C| := le_abs_self C
  set cnt := ∑ w ∈ Z.filter (fun w => 1 / 2 + 51 / 50 * (a / L) ≤ w.re),
    ((analyticOrderAt riemannZeta w).toNat : ℝ)
  have hkey : 2 * Real.pi * ((a / L) * cnt) = 50 * (2 * Real.pi * (a / L / 50 * cnt)) := by ring
  rw [hkey]
  have hCL : |C| ≤ |C| * L := le_mul_of_one_le_right (abs_nonneg C) hL
  nlinarith

/-- `C S^k e^{−c S^ε} ≤ 1` for all large `S`. -/
theorem eventually_mul_rpow_mul_exp_neg_rpow_le_one {C k c ε : ℝ} (hc : 0 < c) (hε : 0 < ε) : ∀ᶠ S : ℝ in atTop, C * S ^ k * Real.exp (-(c * S ^ ε)) ≤ 1 := by
  obtain ⟨n, hn⟩ : ∃ n : ℕ, k + 1 ≤ n * ε := by
    obtain ⟨n, hn⟩ := exists_nat_ge ((k + 1) / ε)
    refine ⟨n, ?_⟩
    rwa [div_le_iff₀ hε] at hn
  have hcn : 0 < c ^ n / (n.factorial : ℝ) := by positivity
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    eventually_ge_atTop (|C| / (c ^ n / (n.factorial : ℝ)))] with S hS1 hS2
  have hS0 : 0 < S := by linarith
  have hexp : c ^ n / (n.factorial : ℝ) * S ^ (k + 1) ≤ Real.exp (c * S ^ ε) := by
    have h := Real.pow_div_factorial_le_exp (x := c * S ^ ε) (by positivity) n
    have hpow : S ^ (k + 1) ≤ (S ^ ε) ^ n := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hS0.le]
      exact Real.rpow_le_rpow_of_exponent_le hS1 (by linarith)
    calc c ^ n / (n.factorial : ℝ) * S ^ (k + 1) ≤ c ^ n / (n.factorial : ℝ) * (S ^ ε) ^ n :=
          mul_le_mul_of_nonneg_left hpow hcn.le
      _ = (c * S ^ ε) ^ n / (n.factorial : ℝ) := by rw [mul_pow]; ring
      _ ≤ Real.exp (c * S ^ ε) := h
  have hSk : 0 < S ^ k := Real.rpow_pos_of_pos hS0 k
  have hSk1 : S ^ (k + 1) = S ^ k * S := by rw [Real.rpow_add hS0, Real.rpow_one]
  rw [Real.exp_neg, ← div_eq_mul_inv, div_le_one (Real.exp_pos _)]
  refine le_trans ?_ hexp
  rw [hSk1]
  have hS2' : |C| ≤ c ^ n / (n.factorial : ℝ) * S := by
    rwa [div_le_iff₀ hcn, mul_comm] at hS2
  calc C * S ^ k ≤ |C| * S ^ k := mul_le_mul_of_nonneg_right (le_abs_self C) hSk.le
    _ ≤ (c ^ n / (n.factorial : ℝ) * S) * S ^ k := mul_le_mul_of_nonneg_right hS2' hSk.le
    _ = c ^ n / (n.factorial : ℝ) * (S ^ k * S) := by ring

/-- `C S^α ≤ S^β` for all large `S` when `α < β`. -/
theorem eventually_const_mul_rpow_le_rpow {C α β : ℝ} (hαβ : α < β) :
    ∀ᶠ S : ℝ in atTop, C * S ^ α ≤ S ^ β := by
  have ht : Tendsto (fun S : ℝ => S ^ (β - α)) atTop atTop := tendsto_rpow_atTop (by linarith)
  filter_upwards [ht.eventually (eventually_ge_atTop C), eventually_gt_atTop (0 : ℝ)] with S hS hS0
  have hsplit : S ^ β = S ^ (β - α) * S ^ α := by
    rw [← Real.rpow_add hS0]; ring_nf
  rw [hsplit]
  exact mul_le_mul_of_nonneg_right hS (Real.rpow_nonneg hS0.le _)

/-- `C (1 + log S) ≤ S^ε` for all large `S`. -/
theorem eventually_const_mul_one_add_log_le_rpow {C ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ S : ℝ in atTop, C * (1 + Real.log S) ≤ S ^ ε := by
  have hlo := (isLittleO_log_rpow_atTop (by linarith : (0 : ℝ) < ε / 2)).bound
    (show (0 : ℝ) < 1 by norm_num)
  have h1 := eventually_const_mul_rpow_le_rpow (C := 2 * |C| + 1) (α := ε / 2) (β := ε)
    (by linarith)
  filter_upwards [hlo, h1, eventually_ge_atTop (1 : ℝ)] with S hS h1S hS1
  have hS0 : 0 < S := by linarith
  have hlog0 : 0 ≤ Real.log S := Real.log_nonneg hS1
  have hpow1 : 1 ≤ S ^ (ε / 2) := Real.one_le_rpow hS1 (by linarith)
  rw [Real.norm_of_nonneg hlog0, Real.norm_of_nonneg (Real.rpow_nonneg hS0.le _), one_mul] at hS
  have hC : C * (1 + Real.log S) ≤ |C| * (1 + Real.log S) :=
    mul_le_mul_of_nonneg_right (le_abs_self C) (by linarith)
  have h2 : |C| * (1 + Real.log S) ≤ |C| * (2 * S ^ (ε / 2)) :=
    mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg C)
  nlinarith [abs_nonneg C]

/-- `S^θ/2 ≤ ⌊S^θ⌋` once `S^θ ≥ 2`. -/
theorem half_rpow_le_molLen {θ S : ℝ} (h2 : 2 ≤ S ^ θ) : S ^ θ / 2 ≤ (VerticalAP.molLen θ S : ℝ) := by
  have := Nat.lt_floor_add_one (S ^ θ)
  unfold VerticalAP.molLen
  linarith

/-! ## Assembly at one scale -/

/-- The left-window constant from a gate constant `C_g` and the Chebyshev constant `C_M`. -/
def criticalGateLeftConst (Cg CM : ℝ) : ℝ := 18 * (3 * (Cg + 1) + 2 + 6 * (1 + |CM|)) + 1

theorem criticalGateLeftConst_pos {Cg CM : ℝ} (hCg : 0 ≤ Cg) : 0 < criticalGateLeftConst Cg CM := by
  unfold criticalGateLeftConst
  positivity

/-- The mean-square constant `A₀`. -/
def criticalGateMeanConst (CgX CgY CM : ℝ) : ℝ :=
  240001 + 141376 * Real.exp 2 *
    (criticalGateLeftConst CgX CM + criticalGateLeftConst CgY CM + 16 * Real.exp 2)

/-- Left windows for one length `N` at the scale `S`, window `2H`. -/
theorem criticalGate_leftWindows {N : ℕ} {S H T₁ T₂ Cg CM CW : ℝ} (hN3 : 3 ≤ N)
    (hH : 40 ≤ H) (hHS : H ≤ S / 16) (hCg : 0 ≤ Cg) (hCW : 0 ≤ CW)
    (hW : ∀ z : ℂ, 1 / 4 ≤ z.re → z.re ≤ 3 → ‖nearLineField N z‖ ≤ CW * N * (1 + |z.im|))
    (hgate : ∀ α : ℝ, S / 2 ≤ α → α ≤ 2 * S →
      ∫ u in α..(α + 2 * H), ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (u : ℂ) * I) *
        edPoly (hbCoeff N) (Finset.Icc 1 N) (((1 / 2 : ℝ) : ℂ) + (u : ℂ) * I)‖ ^ 2 ≤
          Cg * (2 * H))
    (hα95 : 2 * (2 * S) ^ ((95 : ℝ) / 100) ≤ H) (hMVT : 8 * N * (1 + Real.log N) ≤ H)
    (hlogN : 1 ≤ Real.log N)
    (hCM : ∑ k ∈ Finset.Icc 1 N, ArithmeticFunction.vonMangoldt k ^ (2 : ℕ) / (k : ℝ) ≤
      Real.log N * (Real.log N + CM))
    (hkey : 16 * CW ^ 2 * N ^ 2 * (1 + 2 * S) ^ 2 * H ^ 2 *
      Real.exp (-((S / 16) ^ 2 / H ^ 2)) ≤ 1)
    (hT₁ : 2 * S / 3 < T₁) (hT₂ : T₂ < 4 * S / 3) :
    ∀ τ : ℝ, T₁ + H ≤ τ → τ < T₂ + H → ∀ y : ℝ, ∫ t in (τ - H)..(τ + H),
      ‖nearLineWindowField N H τ (((1 / 2 : ℝ) : ℂ) + ((y + t : ℝ) : ℂ) * I)‖ ^ 2 ≤
        criticalGateLeftConst Cg CM * H := by
  intro τ h1 h2 y
  have hS0 : 0 < S := by linarith
  have hE := sum_hbVonMangoldtCoeff_displaced_le (N := N) (by omega) (d := 0) le_rfl
    (by norm_num) hlogN hCM
  have hE' : ∑ n ∈ Finset.Icc 1 N, ‖hbVonMangoldtCoeff N n‖ ^ 2 *
      (n : ℝ) ^ (2 * (1 / 2 - (1 / 2 : ℝ)) - 1) ≤ 2 * (1 + |CM|) := by
    have : (2 * (1 / 2 - (1 / 2 : ℝ)) - 1) = 2 * 0 - 1 := by norm_num
    rw [this]
    exact hE
  have hτ0 : 0 ≤ τ := by linarith
  have hkeyτ : 16 * CW ^ 2 * N ^ 2 * (1 + |τ|) ^ 2 * H ^ 2 *
      Real.exp (-((S / 16) ^ 2 / H ^ 2)) ≤ 1 := by
    refine le_trans ?_ hkey
    rw [abs_of_nonneg hτ0]
    have : (1 + τ) ^ 2 ≤ (1 + 2 * S) ^ 2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
    gcongr
  exact integral_nearLineWindowField_criticalLeft_le (by linarith) hHS hCg hCW hW hgate hα95
    hMVT hE' (by linarith) (by linarith) hkeyτ y

/-- **The mollified mean square at one scale.** -/
theorem criticalGate_meanSquare_le {X Y : ℕ} {S H T₁ T₂ a CgX CgY CM CW : ℝ}
    (hS : 1 < S) (hY3 : 3 ≤ Y) (hYX : Y < X)
    (hXlo : S ^ (47 / 100 : ℝ) / 2 ≤ X) (hYlo : S ^ (23 / 50 : ℝ) / 2 ≤ Y)
    (hY1 : 1 ≤ S ^ (23 / 50 : ℝ) / 2)
    (hlogX : Real.log X ≤ 47 / 100 * Real.log S) (hgap : Real.log S / 200 ≤ Real.log X - Real.log Y)
    (hlogY : 1 ≤ Real.log Y)
    (hH : 40 ≤ H) (hHS : H ≤ S / 16) (hα95 : 2 * (2 * S) ^ ((95 : ℝ) / 100) ≤ H)
    (hMVTX : 8 * X * (1 + Real.log X) ≤ H) (hMVTY : 8 * Y * (1 + Real.log Y) ≤ H)
    (hCgX : 0 ≤ CgX) (hCgY : 0 ≤ CgY) (hCW : 0 ≤ CW)
    (hWX : ∀ z : ℂ, 1 / 4 ≤ z.re → z.re ≤ 3 → ‖nearLineField X z‖ ≤ CW * X * (1 + |z.im|))
    (hWY : ∀ z : ℂ, 1 / 4 ≤ z.re → z.re ≤ 3 → ‖nearLineField Y z‖ ≤ CW * Y * (1 + |z.im|))
    (hgateX : ∀ α : ℝ, S / 2 ≤ α → α ≤ 2 * S →
      ∫ u in α..(α + 2 * H), ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (u : ℂ) * I) *
        edPoly (hbCoeff X) (Finset.Icc 1 X) (((1 / 2 : ℝ) : ℂ) + (u : ℂ) * I)‖ ^ 2 ≤
          CgX * (2 * H))
    (hgateY : ∀ α : ℝ, S / 2 ≤ α → α ≤ 2 * S →
      ∫ u in α..(α + 2 * H), ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (u : ℂ) * I) *
        edPoly (hbCoeff Y) (Finset.Icc 1 Y) (((1 / 2 : ℝ) : ℂ) + (u : ℂ) * I)‖ ^ 2 ≤
          CgY * (2 * H))
    (hCMX : ∑ k ∈ Finset.Icc 1 X, ArithmeticFunction.vonMangoldt k ^ (2 : ℕ) / (k : ℝ) ≤
      Real.log X * (Real.log X + CM))
    (hCMY : ∑ k ∈ Finset.Icc 1 Y, ArithmeticFunction.vonMangoldt k ^ (2 : ℕ) / (k : ℝ) ≤
      Real.log Y * (Real.log Y + CM)) (hCMabs : |CM| ≤ Real.log S)
    (hkeyX : 16 * CW ^ 2 * X ^ 2 * (1 + 2 * S) ^ 2 * H ^ 2 *
      Real.exp (-((S / 16) ^ 2 / H ^ 2)) ≤ 1)
    (hkeyY : 16 * CW ^ 2 * Y ^ 2 * (1 + 2 * S) ^ 2 * H ^ 2 *
      Real.exp (-((S / 16) ^ 2 / H ^ 2)) ≤ 1)
    (hT₁ : 2 * S / 3 < T₁) (hT₁' : T₁ < 2 * S / 3 + 1) (hT₂ : 4 * S / 3 - 1 < T₂)
    (hT₂' : T₂ < 4 * S / 3)
    (hfm : 2 * (2 + X * (45 * Real.sqrt (2 * S / 3) + 8)) ≤
      (T₂ - T₁) * Real.exp (-(Real.log S / 100)))
    (ha : 1 ≤ a) (haL : a ≤ Real.log S / 100) :
    ∫ t in T₁..T₂, ‖riemannZeta (((1 / 2 + a / Real.log S : ℝ) : ℂ) + (t : ℂ) * I) *
        edPoly (twoLengthCoeff X Y) (Finset.Icc 1 X)
          (((1 / 2 + a / Real.log S : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2 ≤
      (T₂ - T₁) * (1 + criticalGateMeanConst CgX CgY CM * Real.exp (-(22 / 25 * a))) := by
  have hL : 0 < Real.log S := Real.log_pos hS
  have hT12 : T₁ ≤ T₂ := by linarith
  have h2H : 2 * H ≤ T₂ - T₁ := by linarith
  have ha0 : 0 ≤ a := by linarith
  have haL2 : a ≤ Real.log S / 2 := by linarith
  have hX3 : 3 ≤ X := by omega
  have hlogX1 : 1 ≤ Real.log X :=
    hlogY.trans (Real.log_le_log (by exact_mod_cast (by omega : 0 < Y)) (by exact_mod_cast hYX.le))
  have hXS1 : 1 ≤ S ^ (47 / 100 : ℝ) / 2 := by
    have : S ^ (23 / 50 : ℝ) ≤ S ^ (47 / 100 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hS.le (by norm_num)
    linarith
  have hlX := criticalGate_leftWindows (N := X) hX3 hH hHS hCgX hCW hWX hgateX hα95 hMVTX
    hlogX1 hCMX hkeyX hT₁ hT₂'
  have hlY := criticalGate_leftWindows (N := Y) hY3 hH hHS hCgY hCW hWY hgateY hα95 hMVTY
    hlogY hCMY hkeyY hT₁ hT₂'
  have hfX := integral_hbMollifiedTail_block_criticalGate_rate_le (N := X) (by omega)
    (θ := 47 / 100) hS hH (by linarith) h2H ha0 haL2 hXlo hXS1
    (criticalGateLeftConst_pos hCgX) hCW (mul_le_mul_of_nonneg_right (by norm_num) ha0) hWX hlX
  have hfY := integral_hbMollifiedTail_block_criticalGate_rate_le (N := Y) (by omega)
    (θ := 23 / 50) hS hH (by linarith) h2H ha0 haL2 hYlo hY1
    (criticalGateLeftConst_pos hCgY) hCW (mul_le_mul_of_nonneg_right (by norm_num) ha0) hWY hlY
  have hMVT' : 8 * X * (1 + Real.log X) ≤ T₂ - T₁ := by linarith
  have hhead := integral_normSq_twoLengthHead_criticalGate_le hS (by omega) hYX hYlo hY1 hlogX hgap
    hT12 hMVT' ha0 haL2 hCMX hCMabs
  have hσ1 : 1 / 2 ≤ 1 / 2 + a / Real.log S := by
    have : 0 ≤ a / Real.log S := div_nonneg ha0 hL.le
    linarith
  have hσ2 : 1 / 2 + a / Real.log S ≤ 2 := by
    have : a / Real.log S ≤ 1 := by rw [div_le_one hL]; linarith
    linarith
  have hfirst := norm_integral_zeta_mul_edPoly_sub_one_block_le (c := twoLengthCoeff X Y)
    (by omega : 1 ≤ X) (twoLengthCoeff_one (by omega) hYX)
    (fun n hn => norm_twoLengthCoeff_le (by omega) hYX hn) (σ := 1 / 2 + a / Real.log S)
    (T := 2 * S / 3) hσ1 hσ2 (by linarith) hT₁.le (by linarith) (by linarith) (by linarith) hT12
  have hE0 : 0 < Real.exp (-(22 / 25 * a)) := Real.exp_pos _
  have hcross : 2 * ‖∫ t in T₁..T₂, (riemannZeta (((1 / 2 + a / Real.log S : ℝ) : ℂ) + (t : ℂ) * I) *
      edPoly (twoLengthCoeff X Y) (Finset.Icc 1 X)
        (((1 / 2 + a / Real.log S : ℝ) : ℂ) + (t : ℂ) * I) - 1)‖ ≤
      (T₂ - T₁) * Real.exp (-(22 / 25 * a)) := by
    have h2 : Real.exp (-(Real.log S / 100)) ≤ Real.exp (-(22 / 25 * a)) :=
      Real.exp_le_exp.mpr (by linarith)
    have h3 := mul_le_mul_of_nonneg_left h2 (by linarith : (0 : ℝ) ≤ T₂ - T₁)
    linarith
  have hM := integral_normSq_zetaTwoLength_le_of_bounds (L := Real.log S) (by omega) hYX
    hlogX hgap hL (by linarith) hT12 hhead hfX hfY hcross
  refine hM.trans (le_of_eq ?_)
  unfold criticalGateMeanConst
  ring

/-! ## Size facts -/

/-- The lengths `X = ⌊S^{47/100}⌋`, `Y = ⌊S^{23/50}⌋` for all large `S`. -/
theorem eventually_criticalGate_lengths : ∀ᶠ S : ℝ in atTop,
    1 < S ∧ S ^ (47 / 100 : ℝ) / 2 ≤ (VerticalAP.molLen (47 / 100) S : ℝ) ∧
      (VerticalAP.molLen (47 / 100) S : ℝ) ≤ S ^ (47 / 100 : ℝ) ∧
      S ^ (23 / 50 : ℝ) / 2 ≤ (VerticalAP.molLen (23 / 50) S : ℝ) ∧
      1 ≤ S ^ (23 / 50 : ℝ) / 2 ∧ 3 ≤ VerticalAP.molLen (23 / 50) S ∧
      VerticalAP.molLen (23 / 50) S < VerticalAP.molLen (47 / 100) S ∧
      Real.log (VerticalAP.molLen (47 / 100) S) ≤ 47 / 100 * Real.log S ∧
      Real.log S / 200 ≤
        Real.log (VerticalAP.molLen (47 / 100) S) - Real.log (VerticalAP.molLen (23 / 50) S) ∧
      1 ≤ Real.log (VerticalAP.molLen (23 / 50) S) := by
  have hlog := Real.tendsto_log_atTop.eventually (eventually_ge_atTop (200 * Real.log 2 + 1))
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    eventually_const_mul_rpow_le_rpow (C := 6) (α := 0) (β := 23 / 50) (by norm_num),
    eventually_const_mul_rpow_le_rpow (C := 3) (α := 23 / 50) (β := 47 / 100) (by norm_num), hlog]
    with S hS1 h6 h3 hL
  rw [Real.rpow_zero, mul_one] at h6
  have hS0 : 0 < S := by linarith
  have hY0 : 0 < S ^ (23 / 50 : ℝ) := Real.rpow_pos_of_pos hS0 _
  have hXpow : 6 ≤ S ^ (47 / 100 : ℝ) := by linarith
  have hXlo := half_rpow_le_molLen (θ := 47 / 100) (S := S) (by linarith)
  have hYlo := half_rpow_le_molLen (θ := 23 / 50) (S := S) (by linarith)
  have hXhi := VerticalAP.molLen_le (θ := 47 / 100) hS0.le
  have hYhi := VerticalAP.molLen_le (θ := 23 / 50) hS0.le
  have hY3 : (3 : ℝ) ≤ VerticalAP.molLen (23 / 50) S := by linarith
  have hYX : (VerticalAP.molLen (23 / 50) S : ℝ) < VerticalAP.molLen (47 / 100) S := by linarith
  have hXpos : (0 : ℝ) < VerticalAP.molLen (47 / 100) S := by linarith
  have hYpos : (0 : ℝ) < VerticalAP.molLen (23 / 50) S := by linarith
  have hlogX : Real.log (VerticalAP.molLen (47 / 100) S) ≤ 47 / 100 * Real.log S := by
    rw [← Real.log_rpow hS0]
    exact Real.log_le_log hXpos hXhi
  have hlogX' : 47 / 100 * Real.log S - Real.log 2 ≤ Real.log (VerticalAP.molLen (47 / 100) S) := by
    rw [← Real.log_rpow hS0, ← Real.log_div (by positivity) (by norm_num)]
    exact Real.log_le_log (by positivity) hXlo
  have hlogY : Real.log (VerticalAP.molLen (23 / 50) S) ≤ 23 / 50 * Real.log S := by
    rw [← Real.log_rpow hS0]
    exact Real.log_le_log hYpos hYhi
  have hlog3 : 1 ≤ Real.log (VerticalAP.molLen (23 / 50) S) := by
    have he : Real.exp 1 ≤ 3 := by have := Real.exp_one_lt_d9; linarith
    rw [Real.le_log_iff_exp_le hYpos]
    linarith
  refine ⟨hS1, hXlo, hXhi, hYlo, by linarith, by exact_mod_cast hY3, by exact_mod_cast hYX, hlogX,
    by linarith, hlog3⟩

/-- The window `H = S^{49/50}/2` for all large `S`. -/
theorem eventually_criticalGate_window : ∀ᶠ S : ℝ in atTop,
    40 ≤ S ^ (49 / 50 : ℝ) / 2 ∧ S ^ (49 / 50 : ℝ) / 2 ≤ S / 16 ∧
      2 * (2 * S) ^ ((95 : ℝ) / 100) ≤ S ^ (49 / 50 : ℝ) / 2 ∧
      ∀ N : ℝ, 0 < N → N ≤ S ^ (47 / 100 : ℝ) → 8 * N * (1 + Real.log N) ≤ S ^ (49 / 50 : ℝ) / 2 := by
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    eventually_const_mul_rpow_le_rpow (C := 80) (α := 0) (β := 49 / 50) (by norm_num),
    eventually_const_mul_rpow_le_rpow (C := 8) (α := 49 / 50) (β := 1) (by norm_num),
    eventually_const_mul_rpow_le_rpow (C := 8) (α := 95 / 100) (β := 49 / 50) (by norm_num),
    eventually_const_mul_one_add_log_le_rpow (C := 16) (ε := 51 / 100) (by norm_num)]
    with S hS1 h80 h8 h95 hlog
  rw [Real.rpow_zero, mul_one] at h80
  rw [Real.rpow_one] at h8
  have hS0 : 0 < S := by linarith
  refine ⟨by linarith, by linarith, ?_, ?_⟩
  · rw [Real.mul_rpow (by norm_num) hS0.le]
    have h2 : (2 : ℝ) ^ ((95 : ℝ) / 100) ≤ 2 := by
      calc (2 : ℝ) ^ ((95 : ℝ) / 100) ≤ 2 ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
        _ = 2 := Real.rpow_one 2
    have hp : 0 ≤ S ^ ((95 : ℝ) / 100) := Real.rpow_nonneg hS0.le _
    nlinarith
  · intro N hN hNS
    have hNS' : N ≤ S := hNS.trans (Real.rpow_le_self_of_one_le hS1.le (by norm_num))
    have hlogN : Real.log N ≤ Real.log S := Real.log_le_log hN hNS'
    have hlogS : 0 ≤ Real.log S := Real.log_nonneg hS1.le
    have hsplit : S ^ (49 / 50 : ℝ) = S ^ (47 / 100 : ℝ) * S ^ (51 / 100 : ℝ) := by
      rw [← Real.rpow_add hS0]; norm_num
    have hp : 0 ≤ S ^ (47 / 100 : ℝ) := Real.rpow_nonneg hS0.le _
    have h1 : 8 * N * (1 + Real.log N) ≤ 8 * S ^ (47 / 100 : ℝ) * (1 + Real.log S) := by
      have : 8 * N * (1 + Real.log N) ≤ 8 * N * (1 + Real.log S) :=
        mul_le_mul_of_nonneg_left (by linarith) (by linarith)
      refine this.trans ?_
      exact mul_le_mul_of_nonneg_right (by linarith) (by linarith)
    rw [hsplit]
    nlinarith

/-- `16 C² N² (1+2S)² H² e^{−(S/16)²/H²} ≤ 1` for `N ≤ S^{47/100}`, `H = S^{49/50}/2`. -/
theorem eventually_criticalGate_key (CW : ℝ) : ∀ᶠ S : ℝ in atTop, ∀ N : ℝ, 0 ≤ N →
    N ≤ S ^ (47 / 100 : ℝ) →
    16 * CW ^ 2 * N ^ 2 * (1 + 2 * S) ^ 2 * (S ^ (49 / 50 : ℝ) / 2) ^ 2 *
      Real.exp (-((S / 16) ^ 2 / (S ^ (49 / 50 : ℝ) / 2) ^ 2)) ≤ 1 := by
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    eventually_mul_rpow_mul_exp_neg_rpow_le_one (C := 36 * CW ^ 2) (k := 49 / 10) (c := 1 / 64)
      (ε := 1 / 25) (by norm_num) (by norm_num)] with S hS1 hexp N hN hNS
  have hS0 : 0 < S := by linarith
  have hratio : (S / 16) ^ 2 / (S ^ (49 / 50 : ℝ) / 2) ^ 2 = 1 / 64 * S ^ (1 / 25 : ℝ) := by
    have h1 : (S ^ (49 / 50 : ℝ)) ^ 2 = S ^ (49 / 25 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hS0.le]; norm_num
    have h2 : S ^ (2 : ℝ) = S ^ (49 / 25 : ℝ) * S ^ (1 / 25 : ℝ) := by
      rw [← Real.rpow_add hS0]; norm_num
    have hp : 0 < S ^ (49 / 25 : ℝ) := Real.rpow_pos_of_pos hS0 _
    rw [div_pow, div_pow, h1]
    rw [show (S : ℝ) ^ 2 = S ^ (2 : ℝ) by rw [← Real.rpow_natCast]; norm_num, h2]
    field_simp
    ring
  rw [hratio]
  have hN2 : N ^ 2 ≤ S ^ (47 / 50 : ℝ) := by
    have h := pow_le_pow_left₀ hN hNS 2
    have e : (S ^ (47 / 100 : ℝ)) ^ 2 = S ^ (47 / 50 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hS0.le]; norm_num
    rw [e] at h
    exact h
  have hpoly : 16 * CW ^ 2 * N ^ 2 * (1 + 2 * S) ^ 2 * (S ^ (49 / 50 : ℝ) / 2) ^ 2 ≤
      36 * CW ^ 2 * S ^ (49 / 10 : ℝ) := by
    have h1 : (1 + 2 * S) ^ 2 ≤ 9 * S ^ 2 := by nlinarith
    have h2 : (S ^ (49 / 50 : ℝ) / 2) ^ 2 = S ^ (49 / 25 : ℝ) / 4 := by
      rw [div_pow, ← Real.rpow_natCast, ← Real.rpow_mul hS0.le]; norm_num
    have h3 : S ^ (47 / 50 : ℝ) * S ^ 2 * S ^ (49 / 25 : ℝ) = S ^ (49 / 10 : ℝ) := by
      rw [show (S : ℝ) ^ 2 = S ^ (2 : ℝ) by rw [← Real.rpow_natCast]; norm_num,
        ← Real.rpow_add hS0, ← Real.rpow_add hS0]
      norm_num
    rw [h2]
    have hA : 0 ≤ CW ^ 2 := sq_nonneg _
    have hB : 0 ≤ S ^ (49 / 25 : ℝ) := Real.rpow_nonneg hS0.le _
    calc 16 * CW ^ 2 * N ^ 2 * (1 + 2 * S) ^ 2 * (S ^ (49 / 25 : ℝ) / 4)
        ≤ 16 * CW ^ 2 * S ^ (47 / 50 : ℝ) * (9 * S ^ 2) * (S ^ (49 / 25 : ℝ) / 4) := by gcongr
      _ = 36 * CW ^ 2 * (S ^ (47 / 50 : ℝ) * S ^ 2 * S ^ (49 / 25 : ℝ)) := by ring
      _ = 36 * CW ^ 2 * S ^ (49 / 10 : ℝ) := by rw [h3]
  have he : 0 ≤ Real.exp (-(1 / 64 * S ^ (1 / 25 : ℝ))) := (Real.exp_pos _).le
  calc 16 * CW ^ 2 * N ^ 2 * (1 + 2 * S) ^ 2 * (S ^ (49 / 50 : ℝ) / 2) ^ 2 *
        Real.exp (-(1 / 64 * S ^ (1 / 25 : ℝ)))
      ≤ 36 * CW ^ 2 * S ^ (49 / 10 : ℝ) * Real.exp (-(1 / 64 * S ^ (1 / 25 : ℝ))) :=
        mul_le_mul_of_nonneg_right hpoly he
    _ ≤ 1 := hexp

/-- The first-moment error is absorbed: `2(2 + X(45√(2S/3) + 8)) ≤ (S/2) e^{−log S/100}`. -/
theorem eventually_criticalGate_firstMoment : ∀ᶠ S : ℝ in atTop, ∀ N : ℝ, 0 ≤ N →
    N ≤ S ^ (47 / 100 : ℝ) →
    2 * (2 + N * (45 * Real.sqrt (2 * S / 3) + 8)) ≤ S / 2 * Real.exp (-(Real.log S / 100)) := by
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    eventually_const_mul_rpow_le_rpow (C := 220) (α := 97 / 100) (β := 99 / 100) (by norm_num)]
    with S hS1 h220 N hN hNS
  have hS0 : 0 < S := by linarith
  have hexp : Real.exp (-(Real.log S / 100)) = S ^ (-(1 / 100 : ℝ)) := by
    rw [Real.rpow_def_of_pos hS0]; congr 1; ring
  rw [hexp]
  have hsq : Real.sqrt (2 * S / 3) ≤ S ^ (1 / 2 : ℝ) := by
    rw [← Real.sqrt_eq_rpow]
    exact Real.sqrt_le_sqrt (by linarith)
  have h97 : S ^ (47 / 100 : ℝ) * S ^ (1 / 2 : ℝ) = S ^ (97 / 100 : ℝ) := by
    rw [← Real.rpow_add hS0]; norm_num
  have h47 : S ^ (47 / 100 : ℝ) ≤ S ^ (97 / 100 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hS1.le (by norm_num)
  have h1 : 1 ≤ S ^ (97 / 100 : ℝ) := Real.one_le_rpow hS1.le (by norm_num)
  have hrhs : S / 2 * S ^ (-(1 / 100 : ℝ)) = S ^ (99 / 100 : ℝ) / 2 := by
    have : S ^ (99 / 100 : ℝ) = S ^ (1 : ℝ) * S ^ (-(1 / 100 : ℝ)) := by
      rw [← Real.rpow_add hS0]; norm_num
    rw [this, Real.rpow_one]; ring
  rw [hrhs]
  have hsq0 : 0 ≤ Real.sqrt (2 * S / 3) := Real.sqrt_nonneg _
  have hNsq : N * Real.sqrt (2 * S / 3) ≤ S ^ (97 / 100 : ℝ) := by
    rw [← h97]
    exact mul_le_mul hNS hsq hsq0 (Real.rpow_nonneg hS0.le _)
  have hN' : N ≤ S ^ (97 / 100 : ℝ) := hNS.trans h47
  nlinarith

/-! ## The density -/

/-- **Exponential zero density near the critical line at rate `22/25`.** For all large `S`,
admissible heights `T₁ ∈ (2S/3, 2S/3 + 1)`, `T₂ ∈ (4S/3 − 1, 4S/3)` exist such that for every
`1 ≤ a ≤ (log S)/100` the zeros with `Re ρ ≥ 1/2 + (51/50)a/log S` between them satisfy
`2π (a/log S) · #zeros ≤ (T₂ − T₁) A e^{−22a/25} + K log S`. -/
theorem exists_selberg_criticalGate_nearLine_zeroDensity :
    ∃ A K : ℝ, 0 < A ∧ 0 ≤ K ∧ ∀ᶠ S : ℝ in atTop,
      ∃ T₁ ∈ Ioo (2 * S / 3) (2 * S / 3 + 1), ∃ T₂ ∈ Ioo (4 * S / 3 - 1) (4 * S / 3),
        ∀ a : ℝ, 1 ≤ a → a ≤ Real.log S / 100 →
        ∀ Z : Finset ℂ,
          (∀ z : ℂ, z ∈ Z ↔ z ∈ (uIcc (1 / 2 : ℝ) (15 / 2) ×ℂ uIcc T₁ T₂) ∧ riemannZeta z = 0) →
          2 * Real.pi * ((a / Real.log S) *
            ∑ w ∈ Z.filter (fun w => 1 / 2 + 51 / 50 * (a / Real.log S) ≤ w.re),
              ((analyticOrderAt riemannZeta w).toNat : ℝ)) ≤
            (T₂ - T₁) * (A * Real.exp (-(22 / 25 * a))) + K * Real.log S := by
  obtain ⟨CgX, hCgX, hgX⟩ := exists_eventually_criticalGate (θ := 47 / 100) (η := 1 / 50)
    (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨CgY, hCgY, hgY⟩ := exists_eventually_criticalGate (θ := 23 / 50) (η := 1 / 50)
    (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨CW, hCW, hW⟩ := exists_norm_nearLineField_le
  obtain ⟨CM, hCM⟩ := exists_sum_vonMangoldt_sq_div_le
  obtain ⟨C, K, hC, hK, hcons⟩ := exists_zetaZeroDensity_scale_le_of_mollified_meanSquare_wide
  have hA0 : 0 < criticalGateMeanConst CgX CgY CM := by
    unfold criticalGateMeanConst
    have := criticalGateLeftConst_pos (CM := CM) hCgX
    have := criticalGateLeftConst_pos (CM := CM) hCgY
    positivity
  refine ⟨25 * criticalGateMeanConst CgX CgY CM, 50 * |C| + 250 * K, by positivity,
    by positivity, ?_⟩
  filter_upwards [hgX, hgY, eventually_criticalGate_lengths, eventually_criticalGate_window,
    eventually_criticalGate_key CW, eventually_criticalGate_firstMoment,
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (|CM| + 2)),
    eventually_ge_atTop (60 : ℝ)]
    with S hgXS hgYS hlen hwin hkey hfm hlogS hS60
  obtain ⟨hS1, hXlo, hXhi, hYlo, hY1, hY3, hYX, hlogX, hgap, hlogY⟩ := hlen
  obtain ⟨hH40, hHS, hα95, hMVT⟩ := hwin
  obtain ⟨X, hX⟩ : ∃ X : ℕ, X = VerticalAP.molLen (47 / 100) S := ⟨_, rfl⟩
  obtain ⟨Y, hY⟩ : ∃ Y : ℕ, Y = VerticalAP.molLen (23 / 50) S := ⟨_, rfl⟩
  obtain ⟨H, hHdef⟩ : ∃ H : ℝ, H = S ^ (49 / 50 : ℝ) / 2 := ⟨_, rfl⟩
  rw [← hX] at hgXS hXlo hXhi hYX hlogX hgap
  rw [← hY] at hgYS hYlo hY3 hYX hgap hlogY
  rw [← hHdef] at hH40 hHS hα95 hMVT hkey
  have hS0 : 0 < S := by linarith
  have hL1 : 1 ≤ Real.log S := by linarith [abs_nonneg CM]
  have hCMabs : |CM| ≤ Real.log S := by linarith
  have h2H : 2 * H = S ^ (1 - 1 / 50 : ℝ) := by rw [hHdef]; norm_num; ring
  have hgateX : ∀ α : ℝ, S / 2 ≤ α → α ≤ 2 * S →
      ∫ u in α..(α + 2 * H), ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (u : ℂ) * I) *
        edPoly (hbCoeff X) (Finset.Icc 1 X) (((1 / 2 : ℝ) : ℂ) + (u : ℂ) * I)‖ ^ 2 ≤
          CgX * (2 * H) := by
    intro α h1 h2
    rw [h2H]
    exact hgXS α h1 h2
  have hgateY : ∀ α : ℝ, S / 2 ≤ α → α ≤ 2 * S →
      ∫ u in α..(α + 2 * H), ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (u : ℂ) * I) *
        edPoly (hbCoeff Y) (Finset.Icc 1 Y) (((1 / 2 : ℝ) : ℂ) + (u : ℂ) * I)‖ ^ 2 ≤
          CgY * (2 * H) := by
    intro α h1 h2
    rw [h2H]
    exact hgYS α h1 h2
  have hX3 : 3 ≤ X := by omega
  have hXpos : (0 : ℝ) < X := by exact_mod_cast (by omega : 0 < X)
  have hYpos : (0 : ℝ) < Y := by exact_mod_cast (by omega : 0 < Y)
  have hYhi : (Y : ℝ) ≤ S ^ (47 / 100 : ℝ) := by
    have : (Y : ℝ) < X := by exact_mod_cast hYX
    linarith
  obtain ⟨T₁, hT₁, T₂, hT₂, hadm1, hadm2⟩ := exists_admissible_heights_of_mollifier
    (b := twoLengthCoeff X Y) (N := X) (by omega) (twoLengthCoeff_one (by omega) hYX)
    (fun n hn => norm_twoLengthCoeff_le (by omega) hYX hn) (A₁ := 2 * S / 3)
    (B₁ := 2 * S / 3 + 1) (A₂ := 4 * S / 3 - 1) (B₂ := 4 * S / 3) (by linarith) (by linarith)
    (by linarith) (by linarith)
  refine ⟨T₁, hT₁, T₂, hT₂, fun a ha haL Z hZ => ?_⟩
  have hT12 : T₁ < T₂ := by linarith [hT₁.2, hT₂.1]
  have hlen : 2 * S / 3 - 2 ≤ T₂ - T₁ := by linarith [hT₁.2, hT₂.1]
  have hfm' : 2 * (2 + X * (45 * Real.sqrt (2 * S / 3) + 8)) ≤
      (T₂ - T₁) * Real.exp (-(Real.log S / 100)) := by
    refine (hfm X hXpos.le hXhi).trans ?_
    exact mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le
  have hMsq := criticalGate_meanSquare_le (X := X) (Y := Y) (H := H) (T₁ := T₁) (T₂ := T₂)
    (a := a) hS1 hY3 hYX hXlo hYlo hY1 hlogX hgap hlogY hH40 hHS hα95
    (hMVT X hXpos hXhi) (hMVT Y hYpos hYhi) hCgX hCgY hCW.le (hW X (by omega)) (hW Y (by omega))
    hgateX hgateY (hCM X (by omega)) (hCM Y (by omega)) hCMabs (hkey X hXpos.le hXhi)
    (hkey Y hYpos.le hYhi) hT₁.1 hT₁.2 hT₂.1 hT₂.2 hfm' ha haL
  have hL0 : 0 < Real.log S := by linarith
  have hδ0 : 0 ≤ a / Real.log S := div_nonneg (by linarith) hL0.le
  have hδ1 : a / Real.log S ≤ 1 / 100 := by
    rw [div_le_iff₀ hL0]; linarith
  have hsub : ∀ T : ℝ, (∀ x ∈ Set.Icc (1 / 4 : ℝ) (15 / 2),
      riemannZeta ((x : ℂ) + (T : ℂ) * I) ≠ 0 ∧
        edPoly (twoLengthCoeff X Y) (Finset.Icc 1 X) ((x : ℂ) + (T : ℂ) * I) ≠ 0) →
      ∀ x ∈ Set.Icc (1 / 2 + a / Real.log S) (15 / 2 : ℝ),
        riemannZeta ((x : ℂ) + (T : ℂ) * I) ≠ 0 ∧
          edPoly (twoLengthCoeff X Y) (Finset.Icc 1 X) ((x : ℂ) + (T : ℂ) * I) ≠ 0 :=
    fun T hT x hx => hT x ⟨by linarith [hx.1], hx.2⟩
  have hlogT₂ : Real.log T₂ ≤ 2 * Real.log S := by
    have h1 : Real.log T₂ ≤ Real.log (2 * S) :=
      Real.log_le_log (by linarith [hT₂.1]) (by linarith [hT₂.2])
    rw [Real.log_mul (by norm_num) hS0.ne'] at h1
    have : Real.log 2 ≤ 1 := by
      have := Real.log_two_lt_d9; linarith
    linarith
  have hlogMb : Real.log ((X : ℝ) ^ (5 : ℕ)) ≤ 3 * Real.log S := by
    rw [Real.log_pow]; push_cast; linarith
  have hcount := twoLength_criticalGate_count_le (X := X) (Y := Y) (C := C) (K := K)
    (L := Real.log S) (a := a) (A₀ := criticalGateMeanConst CgX CgY CM)
    (E := Real.exp (-(22 / 25 * a))) (T₁ := T₁) (T₂ := T₂) (Mb := (X : ℝ) ^ (5 : ℕ)) hK hL1
    (by linarith)
    (fun σ₀ Msq h1 h2 hG1 hG2 hP1 hP2 hM Z' hZ' Δ hΔ =>
      hcons (twoLengthCoeff X Y) X (by omega) (twoLengthCoeff_one (by omega) hYX)
        (fun n hn => norm_twoLengthCoeff_le (by omega) hYX hn) (fun n _ => conj_twoLengthCoeff X Y n)
        ((X : ℝ) ^ (5 : ℕ)) (one_le_pow₀ (by exact_mod_cast (by omega : 1 ≤ X)))
        (sum_norm_twoLengthCoeff_mul_rpow_le (by omega) hYX) σ₀ T₁ T₂ Msq h1 h2
        (by linarith [hT₁.1]) hT12 hG1 hG2 hP1 hP2 hM Z' hZ' Δ hΔ)
    hT12 hlogT₂ hlogMb (by linarith) (by linarith) (by positivity)
    (fun x hx => ((hsub T₁ hadm1) x hx).1) (fun x hx => ((hsub T₂ hadm2) x hx).1)
    (fun x hx => ((hsub T₁ hadm1) x hx).2) (fun x hx => ((hsub T₂ hadm2) x hx).2) hMsq Z hZ
  refine hcount.trans (le_of_eq ?_)
  ring

end RHTower
