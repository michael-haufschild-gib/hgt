import GaloisForLFunctions.RHTower.WeilLinearTwistPositivity

/-!
# Almost-periodic lock phases

Let `G` be a Herglotz producer for the weights `lam`, and let

`P(x) = Σ_j p_j e^{iλ_j x}`,  `Σ_j |p_j| e^{|λ_j|/2} < ∞`,

an almost-periodic factor that continues analytically to the strip `½ ≤ Re s ≤ 3/2`.  Suppose
the lower-line lock `G(1 − s) = κ₀ P(x) G(s)`, `s = ½ − 2ix`, `x > 0`.  Write `a` for the
coefficients of `exp(Σ lam(n) n^{-s}/log n)` and `p₀ = Σ_{λ_j = 0} p_j`.

**Theorem** (`ap_lock_rigidity`).  If no nonzero frequency has `e^{−λ_j/2} ∈ ℚ_{>0}`, then
`p₀ ≠ 0`, `lam(n) = Λ(n)` for `n ≥ 2`, and RH holds.

**Theorem** (`ap_lock_impossible`).  If no frequency has `e^{−λ_j/2} ∈ ℕ` (in particular `p₀ = 0`),
there is no such producer.

The phase of `P` may oscillate with total variation of order `x`.  This lies outside the
monotone twist theorems, which need the variation to be `O(x^α)`, `α < 1`.

**Proof.**
* `e^{iλx}` is the boundary value of `W_λ(s) = e^{−(λ/2)(s−½)}`, so the far integral
  `ε ∫_{t ≤ −1} P(−t) F(½+2it) k(2t, ε+im) dt` is the sum over `j` of `p_j` times the twisted far
  integrals of `W_{λ_j} G`.
* Each twisted far integral is `O(e^{|λ_j|/2})` uniformly in `ε ≤ 1`
  (`exists_norm_twistRadial_uniform`): the right edge costs `‖τ‖/ε` and the top edge `O(1)`.
* A frequency with `m e^{−λ_j/2} ∉ ℕ` has no resonance at height `m`, and its far integral tends
  to `0` (`tendsto_twisted_far_nonres`).  Dominated convergence over `j` leaves only the frequency
  `0`, which contributes `p₀ a(m)` times the main term (`tendsto_ap_lock_radial`).
* The reflected radial limit is `β/π ≠ 0` at every `m ≥ 1`.  So `κ₀ p₀ a(m) M(ε/m) → 2β` for all
  `m`, hence `a ≡ 1`.
-/

open Complex Filter Topology Set MeasureTheory
open scoped ComplexConjugate

namespace RHTower

namespace AbelianTwist

open GaloisForLFunctions GaloisForLFunctions.HTGeometry IntegerMassRigidity FractionalMassRigidity
  PhaseLockRigidity HamburgerStability TruncatedRadial RightEdgeKernel FractionalMassTailRigidity

noncomputable section

/-! ### A uniform bound for the twisted far integral -/

/-- **The twisted far integral is `O(e^{|η|/2})` uniformly in `ε ≤ 1`.** -/
theorem exists_norm_twistRadial_uniform {lam : ℕ → ℝ} {Φ G : ℂ → ℂ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    (hΦre : ∀ s : ℂ, 1 / 2 < s.re → 0 ≤ (Φ s).re)
    (hid : ∀ s : ℂ, 1 < s.re →
      Φ s = zetaArchimedeanDatum s + 1 / (s - 1) - LSeries (lamTwo lam) s)
    (hGc : ∀ s : ℂ, 1 / 2 ≤ s.re → ContinuousAt G s)
    (hGd : ∀ s : ℂ, 1 / 2 < s.re → HasDerivAt G (Φ s * G s) s) (hG2 : G 2 = bigG lam 2)
    {m : ℕ} (hm : 1 ≤ m) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ η ε : ℝ, 0 < ε → ε ≤ 1 →
      ‖(ε : ℂ) * ∫ t in Iic (-1 : ℝ), phiG (twistG η G) t *
        pairKernel (2 * t) ((ε : ℂ) + (m : ℂ) * I)‖ ≤ K * Real.exp (|η| / 2) := by
  have hpi := Real.pi_pos
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  obtain ⟨CF, hCF, hF⟩ := exists_norm_prodF_le hsl hΦre hid hGc hGd hG2
  set S : ℝ := ∑' n, ‖LSeries.term (lamLog lam) (((3 / 2 : ℝ) : ℂ)) n‖ with hS
  set Q : ℝ := 4 * Real.pi ^ (3 / 4 : ℝ) with hQ
  have hQ0 : 0 ≤ Q := by positivity
  set K : ℝ := (1 / 2) * (Real.exp S * Q * ((m : ℝ) + 1) ^ 2 +
    CF * (1 + 2) ^ (1 / 2 : ℝ) * (Q * ((m : ℝ) + 1))) with hK
  refine ⟨K, by positivity, fun η ε hε hε1 => ?_⟩
  set τ : ℂ := (ε : ℂ) + (m : ℂ) * I with hτ
  have hτre : τ.re = ε := by simp [hτ]
  have hτre0 : 0 < τ.re := by rw [hτre]; exact hε
  have hτ0 : τ ≠ 0 := by intro h; rw [h] at hτre0; simp at hτre0
  have hτ1 : 1 ≤ ‖τ‖ := by
    have h := Complex.abs_im_le_norm τ
    have him : τ.im = m := by simp [hτ]
    rw [him, abs_of_nonneg (by linarith)] at h; linarith
  have hτM : ‖τ‖ ≤ (m : ℝ) + 1 := by
    have h := norm_add_le (ε : ℂ) ((m : ℂ) * I)
    rw [Complex.norm_real, norm_mul, Complex.norm_I, mul_one, Complex.norm_natCast,
      Real.norm_eq_abs, abs_of_pos hε] at h
    linarith
  have hτpos : 0 < ‖τ‖ := by linarith
  set δ : ℝ := ε / ‖τ‖ with hδ
  have hδ' : τ.re / ‖τ‖ = δ := by rw [hτre]
  have hδ0 : 0 < δ := div_pos hε hτpos
  set c₁ : ℝ := Real.exp (|η| / 2) with hc₁
  set c₂ : ℝ := Real.exp (-(η / 2)) with hc₂
  have hc₁0 : 0 < c₁ := Real.exp_pos _
  have hc₂0 : 0 < c₂ := Real.exp_pos _
  have hc₂₁ : c₂ ≤ c₁ := Real.exp_le_exp.mpr (by linarith [neg_abs_le η, le_abs_self η])
  -- the contour shift for the twisted producer
  have hF' : ∀ x y : ℝ, 1 / 2 ≤ x → x ≤ 3 / 2 → 2 ≤ |y| →
      ‖prodF (twistG η G) ((x : ℂ) + (y : ℂ) * I)‖ ≤ (c₁ * CF) * (1 + |y|) ^ (1 / 2 : ℝ) := by
    intro x y hx1 hx2 hy
    rw [prodF_twistG, norm_mul, mul_assoc]
    exact mul_le_mul (norm_linTwist_strip_le η (by simpa using hx1) (by simpa using hx2))
      (hF x y hx1 hx2 hy) (norm_nonneg _) hc₁0.le
  have hedge' : ∀ y : ℝ, 1 ≤ |y| →
      ‖edgeIntegrand (twistG η G) τ (((3 / 2 : ℝ) : ℂ) + (y : ℂ) * I)‖ ≤
        (c₂ * Real.exp S) * (Q * ‖τ‖ * Real.exp (-(|y| * (τ.re / ‖τ‖)))) := by
    intro y hy
    rw [edgeIntegrand_twistG, norm_mul, mul_assoc]
    have hW : ‖linTwist η (((3 / 2 : ℝ) : ℂ) + (y : ℂ) * I)‖ = c₂ := norm_linTwist_edgePt η y
    rw [hW]
    exact mul_le_mul_of_nonneg_left
      (norm_edgeIntegrand_three_halves_le hsl hid hGd hG2 hτre0 hτ1 hy) hc₂0.le
  have hfint' : IntegrableOn (fun t => phiG (twistG η G) t * pairKernel (2 * t) τ) (Iic (-1)) :=
    (integrable_phiG_twistG_mul_pairKernel hsl hΦre hid hGc hGd hG2 η hτre0).integrableOn
  have hcont := setIntegral_Iic_radial_eq_of (fun s hs => continuousAt_twistG hGc η hs)
    (fun s hs => hasDerivAt_twistG hGd η hs) (by positivity) hF' hτre0 hτ1 hedge'
    (le_refl (-1 : ℝ)) hfint'
  -- the right edge
  have hedge_int : ‖∫ y in Iic (2 * (-1 : ℝ)), edgeIntegrand (twistG η G) τ
      (((3 / 2 : ℝ) : ℂ) + (y : ℂ) * I)‖ ≤ (c₂ * Real.exp S * Q * ‖τ‖) * (Real.exp (-2 * δ) / δ) := by
    have hint := (integrableOn_exp_mul_Iic hδ0 (2 * (-1 : ℝ))).const_mul (c₂ * Real.exp S * Q * ‖τ‖)
    refine (norm_integral_le_of_norm_le hint ((ae_restrict_iff' measurableSet_Iic).mpr
      (Eventually.of_forall fun y hy => ?_))).trans (le_of_eq ?_)
    · have hy' : y ≤ -2 := by simpa using hy
      have h := hedge' y (by rw [abs_of_neg (by linarith)]; linarith)
      rw [hδ', abs_of_neg (by linarith : y < 0)] at h
      calc ‖edgeIntegrand (twistG η G) τ (((3 / 2 : ℝ) : ℂ) + (y : ℂ) * I)‖
          ≤ c₂ * Real.exp S * (Q * ‖τ‖ * Real.exp (-(-y * δ))) := h
        _ = c₂ * Real.exp S * Q * ‖τ‖ * Real.exp (δ * y) := by
            rw [show -(-y * δ) = δ * y by ring]; ring
    · rw [integral_const_mul, integral_exp_mul_Iic hδ0, show δ * (2 * (-1 : ℝ)) = -2 * δ by ring]
  have hedge_eps : ε * ‖∫ y in Iic (2 * (-1 : ℝ)), edgeIntegrand (twistG η G) τ
      (((3 / 2 : ℝ) : ℂ) + (y : ℂ) * I)‖ ≤ c₁ * (Real.exp S * Q * ((m : ℝ) + 1) ^ 2) := by
    have hexp : Real.exp (-2 * δ) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have hεδ : ε / δ = ‖τ‖ := by rw [hδ]; field_simp
    calc ε * ‖∫ y in Iic (2 * (-1 : ℝ)), edgeIntegrand (twistG η G) τ
          (((3 / 2 : ℝ) : ℂ) + (y : ℂ) * I)‖
        ≤ ε * ((c₂ * Real.exp S * Q * ‖τ‖) * (Real.exp (-2 * δ) / δ)) :=
          mul_le_mul_of_nonneg_left hedge_int hε.le
      _ = c₂ * Real.exp S * Q * ‖τ‖ * Real.exp (-2 * δ) * (ε / δ) := by ring
      _ ≤ c₁ * Real.exp S * Q * ‖τ‖ * 1 * ‖τ‖ := by
          rw [hεδ]; gcongr
      _ ≤ c₁ * Real.exp S * Q * ((m : ℝ) + 1) * 1 * ((m : ℝ) + 1) := by gcongr
      _ = c₁ * (Real.exp S * Q * ((m : ℝ) + 1) ^ 2) := by ring
  -- the top edge
  have h2b : 2 ≤ |2 * (-1 : ℝ)| := by norm_num
  have htop := norm_horizontalEdge_le hF' hτre0 hτ1 h2b
  have htop' : ‖∫ x in (1 / 2 : ℝ)..(3 / 2), edgeIntegrand (twistG η G) τ
      ((x : ℂ) + ((2 * (-1 : ℝ) : ℝ) : ℂ) * I)‖ ≤ c₁ * (CF * (1 + 2) ^ (1 / 2 : ℝ) *
        (Q * ((m : ℝ) + 1))) := by
    refine htop.trans ?_
    have h2 : |2 * (-1 : ℝ)| = 2 := by norm_num
    rw [h2]
    have hexp : Real.exp (-(2 * (τ.re / ‖τ‖))) ≤ 1 := by
      rw [Real.exp_le_one_iff, hδ']; linarith
    calc c₁ * CF * (1 + 2) ^ (1 / 2 : ℝ) * (Q * ‖τ‖ * Real.exp (-(2 * (τ.re / ‖τ‖))))
        ≤ c₁ * CF * (1 + 2) ^ (1 / 2 : ℝ) * (Q * ((m : ℝ) + 1) * 1) := by gcongr
      _ = c₁ * (CF * (1 + 2) ^ (1 / 2 : ℝ) * (Q * ((m : ℝ) + 1))) := by ring
  -- assemble
  rw [hcont, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε, norm_mul,
    show ‖(1 / 2 : ℂ)‖ = 1 / 2 by simp]
  have hsum := norm_add_le (∫ y in Iic (2 * (-1 : ℝ)), edgeIntegrand (twistG η G) τ
      (((3 / 2 : ℝ) : ℂ) + (y : ℂ) * I))
    (I * ∫ x in (1 / 2 : ℝ)..(3 / 2), edgeIntegrand (twistG η G) τ
      ((x : ℂ) + ((2 * (-1 : ℝ) : ℝ) : ℂ) * I))
  rw [norm_mul, Complex.norm_I, one_mul] at hsum
  have htop'' : ε * ‖∫ x in (1 / 2 : ℝ)..(3 / 2), edgeIntegrand (twistG η G) τ
      ((x : ℂ) + ((2 * (-1 : ℝ) : ℝ) : ℂ) * I)‖ ≤ c₁ * (CF * (1 + 2) ^ (1 / 2 : ℝ) *
        (Q * ((m : ℝ) + 1))) := by
    calc _ ≤ 1 * ‖∫ x in (1 / 2 : ℝ)..(3 / 2), edgeIntegrand (twistG η G) τ
          ((x : ℂ) + ((2 * (-1 : ℝ) : ℝ) : ℂ) * I)‖ :=
          mul_le_mul_of_nonneg_right hε1 (norm_nonneg _)
      _ ≤ _ := by rw [one_mul]; exact htop'
  calc ε * (1 / 2 * ‖(∫ y in Iic (2 * (-1 : ℝ)), edgeIntegrand (twistG η G) τ
        (((3 / 2 : ℝ) : ℂ) + (y : ℂ) * I)) + I * ∫ x in (1 / 2 : ℝ)..(3 / 2),
          edgeIntegrand (twistG η G) τ ((x : ℂ) + ((2 * (-1 : ℝ) : ℝ) : ℂ) * I)‖)
      ≤ ε * (1 / 2 * (‖∫ y in Iic (2 * (-1 : ℝ)), edgeIntegrand (twistG η G) τ
        (((3 / 2 : ℝ) : ℂ) + (y : ℂ) * I)‖ + ‖∫ x in (1 / 2 : ℝ)..(3 / 2),
          edgeIntegrand (twistG η G) τ ((x : ℂ) + ((2 * (-1 : ℝ) : ℝ) : ℂ) * I)‖)) := by
        gcongr
    _ = 1 / 2 * (ε * ‖∫ y in Iic (2 * (-1 : ℝ)), edgeIntegrand (twistG η G) τ
        (((3 / 2 : ℝ) : ℂ) + (y : ℂ) * I)‖ + ε * ‖∫ x in (1 / 2 : ℝ)..(3 / 2),
          edgeIntegrand (twistG η G) τ ((x : ℂ) + ((2 * (-1 : ℝ) : ℝ) : ℂ) * I)‖) := by ring
    _ ≤ 1 / 2 * (c₁ * (Real.exp S * Q * ((m : ℝ) + 1) ^ 2) +
        c₁ * (CF * (1 + 2) ^ (1 / 2 : ℝ) * (Q * ((m : ℝ) + 1)))) := by gcongr
    _ = K * c₁ := by rw [hK]; ring


/-! ### Untwisted forms of the radial lemmas -/

/-- Without resonance at height `m`, the far integral of `W_η G` tends to `0`. -/
theorem tendsto_far_nonres {lam : ℕ → ℝ} {Φ G : ℂ → ℂ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    (hΦd : DifferentiableOn ℂ Φ {s : ℂ | 1 / 2 < s.re})
    (hΦre : ∀ s : ℂ, 1 / 2 < s.re → 0 ≤ (Φ s).re)
    (hid : ∀ s : ℂ, 1 < s.re →
      Φ s = zetaArchimedeanDatum s + 1 / (s - 1) - LSeries (lamTwo lam) s)
    (hGc : ∀ s : ℂ, 1 / 2 ≤ s.re → ContinuousAt G s)
    (hGd : ∀ s : ℂ, 1 / 2 < s.re → HasDerivAt G (Φ s * G s) s) (hG2 : G 2 = bigG lam 2)
    (η : ℝ) {m : ℕ} (hm : 1 ≤ m) (hres : ∀ n : ℕ, (n : ℝ) ≠ m * Real.exp (-(η / 2))) :
    Tendsto (fun ε : ℝ => (ε : ℂ) * ∫ t in Iic (-1 : ℝ),
      phiG (twistG η G) t * pairKernel (2 * t) ((ε : ℂ) + (m : ℂ) * I)) (𝓝[>] 0) (𝓝 0) := by
  have h := tendsto_twisted_far_nonres hsl hΦd hΦre hid hGc hGd hG2 η hm hres
    (C := fun _ => 0) monotone_const (α := 1 / 2) (K := 1) (by norm_num) (by norm_num) one_pos
    (fun x hx => by positivity) 0
  simpa only [mul_zero, Complex.ofReal_zero, zero_mul, Complex.exp_zero, one_mul] using h

/-- The plain remainder (no twist) tends to `0` radially. -/
theorem tendsto_remainder_plain {lam : ℕ → ℝ} {Φ G : ℂ → ℂ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    (hΦre : ∀ s : ℂ, 1 / 2 < s.re → 0 ≤ (Φ s).re)
    (hid : ∀ s : ℂ, 1 < s.re →
      Φ s = zetaArchimedeanDatum s + 1 / (s - 1) - LSeries (lamTwo lam) s)
    (hGc : ∀ s : ℂ, 1 / 2 ≤ s.re → ContinuousAt G s)
    (hGd : ∀ s : ℂ, 1 / 2 < s.re → HasDerivAt G (Φ s * G s) s) (hG2 : G 2 = bigG lam 2)
    {m : ℕ} (hm : 1 ≤ m) :
    Tendsto (fun ε : ℝ => (ε : ℂ) * ∫ t in Iic (-1 : ℝ),
      remainder G (dirichletExp (lamLog lam) m) m ((ε : ℂ) + (m : ℂ) * I) t) (𝓝[>] 0) (𝓝 0) := by
  have h := tendsto_twisted_remainder hsl hΦre hid hGc hGd hG2 (C := fun _ => 0) monotone_const
    (fun γ _ => ⟨0, fun x _ => by positivity⟩) 0 hm
  simpa only [mul_zero, Complex.ofReal_zero, zero_mul, Complex.exp_zero, one_mul] using h

theorem mainTwist_scale_plain {m : ℕ} (hm : 1 ≤ m) (ε : ℝ) :
    (ε : ℂ) * ∫ t in Iic (-1 : ℝ), rhoMain m ((ε : ℂ) + (m : ℂ) * I) t =
      mainTwist 0 (fun _ => 0) (ε / m) := by
  rw [← mainTwist_scale 0 (fun _ => 0) hm ε]
  simp only [mul_zero, Complex.ofReal_zero, zero_mul, Complex.exp_zero, one_mul]

/-! ### Almost-periodic factors -/

/-- The almost-periodic factor `P(x) = Σ_j p_j e^{iω_j x}`. -/
def apFactor (p : ℕ → ℂ) (ω : ℕ → ℝ) (x : ℝ) : ℂ :=
  ∑' j, p j * cexp (((ω j * x : ℝ) : ℂ) * I)

/-- The mean of `P`: the total coefficient of the frequency `0`. -/
def apMean (p : ℕ → ℂ) (ω : ℕ → ℝ) : ℂ := ∑' j, if ω j = 0 then p j else 0

theorem summable_norm_of_exp {p : ℕ → ℂ} {ω : ℕ → ℝ}
    (hp : Summable fun j => ‖p j‖ * Real.exp (|ω j| / 2)) : Summable fun j => ‖p j‖ :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun j => le_mul_of_one_le_right (norm_nonneg _) (Real.one_le_exp (by positivity))) hp

theorem norm_apFactor_le {p : ℕ → ℂ} {ω : ℕ → ℝ} (hp1 : Summable fun j => ‖p j‖) (x : ℝ) :
    ‖apFactor p ω x‖ ≤ ∑' j, ‖p j‖ := by
  unfold apFactor
  have hs : Summable fun j => ‖p j * cexp (((ω j * x : ℝ) : ℂ) * I)‖ :=
    hp1.congr fun j => by rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]
  refine (norm_tsum_le_tsum_norm hs).trans (le_of_eq ?_)
  congr 1; funext j; rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]

theorem continuous_apFactor {p : ℕ → ℂ} {ω : ℕ → ℝ} (hp1 : Summable fun j => ‖p j‖) :
    Continuous (apFactor p ω) := by
  unfold apFactor
  refine continuous_tsum (fun j => by fun_prop) hp1 fun j x => ?_
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]

theorem twistG_zero (G : ℂ → ℂ) : twistG 0 G = G := by
  funext s; simp [twistG, linTwist]

/-- `P(−t) F(½+2it) = Σ_j p_j (W_{ω_j} F)(½+2it)`. -/
theorem apFactor_mul_phiG (p : ℕ → ℂ) (ω : ℕ → ℝ) (G : ℂ → ℂ) (t : ℝ) :
    apFactor p ω (-t) * phiG G t = ∑' j, p j * phiG (twistG (ω j) G) t := by
  unfold apFactor
  rw [← tsum_mul_right]
  congr 1; funext j
  rw [phiG_twistG, linTwist_lineS]
  ring


/-! ### The radial limit of an almost-periodic lock -/

theorem integrable_apFactor_phiG_mul_pairKernel {lam : ℕ → ℝ} {Φ G : ℂ → ℂ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    (hΦre : ∀ s : ℂ, 1 / 2 < s.re → 0 ≤ (Φ s).re)
    (hid : ∀ s : ℂ, 1 < s.re →
      Φ s = zetaArchimedeanDatum s + 1 / (s - 1) - LSeries (lamTwo lam) s)
    (hGc : ∀ s : ℂ, 1 / 2 ≤ s.re → ContinuousAt G s)
    (hGd : ∀ s : ℂ, 1 / 2 < s.re → HasDerivAt G (Φ s * G s) s) (hG2 : G 2 = bigG lam 2)
    {p : ℕ → ℂ} {ω : ℕ → ℝ} (hp1 : Summable fun j => ‖p j‖) {τ : ℂ} (hτ : 0 < τ.re) :
    Integrable fun t : ℝ => (apFactor p ω (-t) * phiG G t) * pairKernel (2 * t) τ := by
  have h := (MonotoneTwistLock.integrable_phiG_mul_pairKernel hsl hΦre hid hGc hGd hG2 hτ).bdd_mul
    (c := ∑' j, ‖p j‖) ((continuous_apFactor (ω := ω) hp1).comp continuous_neg).aestronglyMeasurable
    (Eventually.of_forall fun t => norm_apFactor_le (ω := ω) hp1 (-t))
  refine h.congr (Eventually.of_forall fun t => ?_)
  simp only [Function.comp_apply]
  ring

/-- **The far integral of an almost-periodic lock splits over its frequencies.** -/
theorem far_apFactor_eq_tsum {lam : ℕ → ℝ} {Φ G : ℂ → ℂ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    (hΦre : ∀ s : ℂ, 1 / 2 < s.re → 0 ≤ (Φ s).re)
    (hid : ∀ s : ℂ, 1 < s.re →
      Φ s = zetaArchimedeanDatum s + 1 / (s - 1) - LSeries (lamTwo lam) s)
    (hGc : ∀ s : ℂ, 1 / 2 ≤ s.re → ContinuousAt G s)
    (hGd : ∀ s : ℂ, 1 / 2 < s.re → HasDerivAt G (Φ s * G s) s) (hG2 : G 2 = bigG lam 2)
    {p : ℕ → ℂ} {ω : ℕ → ℝ} (hp1 : Summable fun j => ‖p j‖) {τ : ℂ} (hτ : 0 < τ.re) :
    ∫ t in Iic (-1 : ℝ), (apFactor p ω (-t) * phiG G t) * pairKernel (2 * t) τ =
      ∑' j, p j * ∫ t in Iic (-1 : ℝ), phiG (twistG (ω j) G) t * pairKernel (2 * t) τ := by
  have hphik := MonotoneTwistLock.integrable_phiG_mul_pairKernel hsl hΦre hid hGc hGd hG2 hτ
  have hint : ∀ j, Integrable (fun t => p j * (phiG (twistG (ω j) G) t * pairKernel (2 * t) τ))
      (volume.restrict (Iic (-1 : ℝ))) := fun j =>
    ((integrable_phiG_twistG_mul_pairKernel hsl hΦre hid hGc hGd hG2 (ω j) hτ).integrableOn).const_mul _
  have hnorm : ∀ j, ∫ t in Iic (-1 : ℝ), ‖p j * (phiG (twistG (ω j) G) t * pairKernel (2 * t) τ)‖ =
      ‖p j‖ * ∫ t in Iic (-1 : ℝ), ‖phiG G t * pairKernel (2 * t) τ‖ := by
    intro j
    rw [← integral_const_mul]
    congr 1; funext t
    rw [norm_mul, norm_mul, norm_mul, norm_phiG_twistG]
  have hsum : Summable fun j => ∫ t in Iic (-1 : ℝ),
      ‖p j * (phiG (twistG (ω j) G) t * pairKernel (2 * t) τ)‖ := by
    simp only [hnorm]; exact hp1.mul_right _
  have h := integral_tsum_of_summable_integral_norm hint hsum
  simp only [integral_const_mul] at h
  rw [h]
  refine setIntegral_congr_fun measurableSet_Iic fun t _ => ?_
  rw [apFactor_mul_phiG, ← tsum_mul_right]
  congr 1; funext j; ring

/-- **The radial limit of an almost-periodic lock at height `m`.**  If no nonzero frequency
resonates at height `m` (`m e^{−ω_j/2} ∉ ℕ`), then `κ₀ p₀ a(m) M(ε/m) → 2β`. -/
theorem tendsto_ap_lock_radial {lam : ℕ → ℝ} {Φ G : ℂ → ℂ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    (hΦd : DifferentiableOn ℂ Φ {s : ℂ | 1 / 2 < s.re})
    (hΦre : ∀ s : ℂ, 1 / 2 < s.re → 0 ≤ (Φ s).re)
    (hid : ∀ s : ℂ, 1 < s.re →
      Φ s = zetaArchimedeanDatum s + 1 / (s - 1) - LSeries (lamTwo lam) s)
    (hGc : ∀ s : ℂ, 1 / 2 ≤ s.re → ContinuousAt G s)
    (hGd : ∀ s : ℂ, 1 / 2 < s.re → HasDerivAt G (Φ s * G s) s) (hG2 : G 2 = bigG lam 2)
    {p : ℕ → ℂ} {ω : ℕ → ℝ} (hp : Summable fun j => ‖p j‖ * Real.exp (|ω j| / 2)) {κ₀ : ℂ}
    (hlock : ∀ τ : ℝ, τ < 0 → G (1 - lineS τ) = κ₀ * apFactor p ω (-τ) * G (lineS τ))
    {m : ℕ} (hm : 1 ≤ m) (hres : ∀ j, ω j ≠ 0 → ∀ n : ℕ, (n : ℝ) ≠ m * Real.exp (-(ω j / 2))) :
    Tendsto (fun ε : ℝ => κ₀ * apMean p ω * dirichletExp (lamLog lam) m *
      mainTwist 0 (fun _ => 0) (ε / m)) (𝓝[>] 0) (𝓝 (2 * betaG G)) := by
  have hpi := Real.pi_pos
  have hp1 := summable_norm_of_exp hp
  set am := dirichletExp (lamLog lam) m with ham
  obtain ⟨K, hK0, hK⟩ := exists_norm_twistRadial_uniform hsl hΦre hid hGc hGd hG2 hm
  obtain ⟨CB, N, hCB, hpoly⟩ := exists_poly_bound_lineG hsl hΦre hid hGc hGd hG2
  -- the twisted far integrals
  set F : ℕ → ℝ → ℂ := fun j ε => (ε : ℂ) * ∫ t in Iic (-1 : ℝ),
    phiG (twistG (ω j) G) t * pairKernel (2 * t) ((ε : ℂ) + (m : ℂ) * I) with hF
  set F' : ℕ → ℝ → ℂ := fun j ε => if ω j = 0 then 0 else F j ε with hF'
  set FG : ℝ → ℂ := fun ε => (ε : ℂ) * ∫ t in Iic (-1 : ℝ),
    phiG G t * pairKernel (2 * t) ((ε : ℂ) + (m : ℂ) * I) with hFG
  -- (a) the nonresonant frequencies vanish
  have hser : Tendsto (fun ε => ∑' j, p j * F' j ε) (𝓝[>] 0) (𝓝 0) := by
    have h := tendsto_tsum_of_dominated_convergence (𝓕 := 𝓝[>] (0 : ℝ))
      (f := fun ε j => p j * F' j ε) (g := fun _ => (0 : ℂ))
      (bound := fun j => ‖p j‖ * Real.exp (|ω j| / 2) * K) (hp.mul_right K) (fun j => ?_) ?_
    · simpa using h
    · by_cases hj : ω j = 0
      · simp only [hF', hj, if_true, mul_zero]; exact tendsto_const_nhds
      · have h1 := (tendsto_far_nonres hsl hΦd hΦre hid hGc hGd hG2 (ω j) hm (hres j hj)).const_mul
          (p j)
        rw [mul_zero] at h1
        simpa only [hF', hj, if_false, hF] using h1
    · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with ε hε j
      by_cases hj : ω j = 0
      · simp only [hF', hj, if_true, mul_zero, norm_zero]; positivity
      · simp only [hF', hj, if_false, norm_mul]
        have h1 := hK (ω j) ε hε.1 hε.2.le
        calc ‖p j‖ * ‖F j ε‖ ≤ ‖p j‖ * (K * Real.exp (|ω j| / 2)) :=
              mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
          _ = ‖p j‖ * Real.exp (|ω j| / 2) * K := by ring
  -- (b) the resonant frequency `0` gives the main term
  have hrem := tendsto_remainder_plain hsl hΦre hid hGc hGd hG2 hm
  have hFG : ∀ ε : ℝ, 0 < ε → FG ε = (ε : ℂ) * (∫ t in Iic (-1 : ℝ),
      remainder G am m ((ε : ℂ) + (m : ℂ) * I) t) + am * mainTwist 0 (fun _ => 0) (ε / m) := by
    intro ε hε
    set τ : ℂ := (ε : ℂ) + (m : ℂ) * I with hτ
    have hτre0 : 0 < τ.re := by simp [hτ]; exact hε
    have hτ1 : 1 ≤ ‖τ‖ := by
      have h := Complex.abs_im_le_norm τ
      have him : τ.im = m := by simp [hτ]
      have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
      rw [him, abs_of_nonneg (by linarith)] at h; linarith
    have hphik := MonotoneTwistLock.integrable_phiG_mul_pairKernel hsl hΦre hid hGc hGd hG2 hτre0
    have hrho := integrableOn_rhoMain hm hτre0 hτ1
    rw [← mainTwist_scale_plain hm ε]
    simp only [hFG, remainder]
    rw [integral_sub hphik.integrableOn (hrho.const_mul am), integral_const_mul]
    ring
  -- (c) the far integral splits
  have hfar : ∀ ε : ℝ, 0 < ε → ε ≤ 1 → (ε : ℂ) * ∫ t in Iic (-1 : ℝ),
      (apFactor p ω (-t) * phiG G t) * pairKernel (2 * t) ((ε : ℂ) + (m : ℂ) * I) =
      apMean p ω * FG ε + ∑' j, p j * F' j ε := by
    intro ε hε hε1
    have hτre0 : 0 < ((ε : ℂ) + (m : ℂ) * I).re := by simp; exact hε
    rw [far_apFactor_eq_tsum hsl hΦre hid hGc hGd hG2 hp1 hτre0, ← tsum_mul_left]
    have hsplit : ∀ j, (ε : ℂ) * (p j * ∫ t in Iic (-1 : ℝ),
        phiG (twistG (ω j) G) t * pairKernel (2 * t) ((ε : ℂ) + (m : ℂ) * I)) =
        (if ω j = 0 then p j else 0) * FG ε + p j * F' j ε := by
      intro j
      by_cases hj : ω j = 0
      · simp only [hj, if_true, hF', mul_zero, add_zero, twistG_zero]; ring
      · simp only [hj, if_false, hF', hF, zero_mul, zero_add]; ring
    simp only [hsplit]
    have hs1 : Summable fun j => (if ω j = 0 then p j else 0) * FG ε := by
      refine Summable.of_norm_bounded (hp1.mul_right ‖FG ε‖) fun j => ?_
      rw [norm_mul]
      gcongr
      split_ifs <;> simp
    have hs2 : Summable fun j => p j * F' j ε := by
      refine Summable.of_norm_bounded (hp.mul_right K) fun j => ?_
      by_cases hj : ω j = 0
      · simp only [hF', hj, if_true, mul_zero, norm_zero]; positivity
      · simp only [hF', hj, if_false, norm_mul]
        have h1 := hK (ω j) ε hε hε1
        calc ‖p j‖ * ‖F j ε‖ ≤ ‖p j‖ * (K * Real.exp (|ω j| / 2)) :=
              mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
          _ = ‖p j‖ * Real.exp (|ω j| / 2) * K := by ring
    rw [hs1.tsum_add hs2, tsum_mul_right]
    rfl
  -- (d) the near piece
  have hnear : Tendsto (fun ε : ℝ => (ε : ℂ) * ∫ t in Ioo (-1 : ℝ) 0,
      (apFactor p ω (-t) * phiG G t) * pairKernel (2 * t) ((ε : ℂ) + (m : ℂ) * I))
      (𝓝[>] 0) (𝓝 0) := by
    refine tendsto_eps_mul_setIntegral_Ioo (B := (∑' j, ‖p j‖) * (CB * 2 ^ N)) (fun t ht => ?_) hm
    rw [norm_mul]
    have h1 := norm_apFactor_le hp1 (ω := ω) (-t)
    have h2 := (hpoly t).1
    have hta : |t| ≤ 1 := by rw [abs_le]; constructor <;> linarith [ht.1, ht.2]
    have h3 : (1 + |t|) ^ N ≤ 2 ^ N := pow_le_pow_left₀ (by positivity) (by linarith) N
    have h4 : ‖phiG G t‖ ≤ CB * 2 ^ N := h2.trans (by gcongr)
    exact mul_le_mul h1 h4 (norm_nonneg _) (by positivity)
  -- (e) the reflected identity
  have hrefl := tendsto_lower_reflected_radial hsl hΦre hid hGc hGd hG2 hm
  have hdecomp : ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ((2 * Real.pi : ℝ) : ℂ) * ((ε : ℂ) * defectLaplace ((Iio (0 : ℝ)).indicator (phiStar G))
        ((ε : ℂ) + (m : ℂ) * I)) -
        κ₀ * apMean p ω * ((ε : ℂ) * ∫ t in Iic (-1 : ℝ),
          remainder G am m ((ε : ℂ) + (m : ℂ) * I) t) -
        κ₀ * (∑' j, p j * F' j ε) -
        κ₀ * ((ε : ℂ) * ∫ t in Ioo (-1 : ℝ) 0,
          (apFactor p ω (-t) * phiG G t) * pairKernel (2 * t) ((ε : ℂ) + (m : ℂ) * I)) =
      κ₀ * apMean p ω * am * mainTwist 0 (fun _ => 0) (ε / m) := by
    intro ε hε hε1
    set τ : ℂ := (ε : ℂ) + (m : ℂ) * I with hτ
    have hτre0 : 0 < τ.re := by simp [hτ]; exact hε
    have hint := integrable_apFactor_phiG_mul_pairKernel hsl hΦre hid hGc hGd hG2 (ω := ω) hp1
      hτre0
    unfold defectLaplace
    have hind : (fun t => (Iio (0 : ℝ)).indicator (phiStar G) t * pairKernel (2 * t) τ) =
        (Iio (0 : ℝ)).indicator (fun t => phiStar G t * pairKernel (2 * t) τ) := by
      funext t
      by_cases ht : t ∈ Iio (0 : ℝ)
      · rw [Set.indicator_of_mem ht, Set.indicator_of_mem ht]
      · rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem ht, zero_mul]
    rw [hind, integral_indicator measurableSet_Iio]
    have hcongr : ∫ t in Iio (0 : ℝ), phiStar G t * pairKernel (2 * t) τ =
        ∫ t in Iio (0 : ℝ), κ₀ * ((apFactor p ω (-t) * phiG G t) * pairKernel (2 * t) τ) := by
      refine setIntegral_congr_fun measurableSet_Iio fun t ht => ?_
      have ht0 : t < 0 := ht
      simp only [phiStar, phiG]
      rw [hlock t ht0]
      ring
    have hsplitI : Iio (0 : ℝ) = Iic (-1) ∪ Ioo (-1) 0 := by
      ext t
      simp only [mem_Iio, mem_union, mem_Iic, mem_Ioo]
      constructor
      · intro h
        by_cases h1 : t ≤ -1
        · exact Or.inl h1
        · exact Or.inr ⟨by linarith, h⟩
      · rintro (h | h)
        · linarith
        · exact h.2
    have hdisj : Disjoint (Iic (-1 : ℝ)) (Ioo (-1) 0) :=
      Set.disjoint_left.mpr fun t h1 h2 => by
        simp only [mem_Iic] at h1; simp only [mem_Ioo] at h2; linarith [h2.1]
    rw [hcongr, integral_const_mul, hsplitI,
      setIntegral_union hdisj measurableSet_Ioo hint.integrableOn hint.integrableOn]
    have hfarε := hfar ε hε hε1
    have hFGε := hFG ε hε
    have h2pi : ((2 * Real.pi : ℝ) : ℂ) * ((1 / (2 * Real.pi) : ℝ) : ℂ) = 1 := by
      push_cast; field_simp
    have e1 : (ε : ℂ) * ∫ t in Iic (-1 : ℝ), (apFactor p ω (-t) * phiG G t) * pairKernel (2 * t) τ =
        apMean p ω * ((ε : ℂ) * (∫ t in Iic (-1 : ℝ), remainder G am m τ t) +
          am * mainTwist 0 (fun _ => 0) (ε / m)) + ∑' j, p j * F' j ε := by
      rw [hfarε, ← hFGε]
    linear_combination (↑ε * (κ₀ * ((∫ t in Iic (-1 : ℝ),
      (apFactor p ω (-t) * phiG G t) * pairKernel (2 * t) τ) +
        ∫ t in Ioo (-1 : ℝ) 0, (apFactor p ω (-t) * phiG G t) * pairKernel (2 * t) τ))) * h2pi +
      κ₀ * e1
  have hlim := ((((hrefl.const_mul ((2 * Real.pi : ℝ) : ℂ)).sub
    (hrem.const_mul (κ₀ * apMean p ω))).sub (hser.const_mul κ₀)).sub (hnear.const_mul κ₀))
  have hval : ((2 * Real.pi : ℝ) : ℂ) * (betaG G / (Real.pi : ℂ)) - κ₀ * apMean p ω * 0 -
      κ₀ * 0 - κ₀ * 0 = 2 * betaG G := by
    have : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hpi.ne'
    push_cast; field_simp; ring
  rw [hval] at hlim
  refine hlim.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with ε hε
  exact hdecomp ε hε.1 hε.2.le


/-! ### The theorems -/

/-- **An almost-periodic lock without resonance is impossible.**  Let `G` be a Herglotz producer
for the weights `lam` with lower-line lock `G(1 − s) = κ₀ P(x) G(s)`, `s = ½ − 2ix`, `x > 0`, where
`P(x) = Σ_j p_j e^{iω_j x}` and `Σ_j |p_j| e^{|ω_j|/2} < ∞`.  Then some frequency has
`e^{−ω_j/2} ∈ ℕ`. -/
theorem ap_lock_impossible {lam : ℕ → ℝ} {Φ G : ℂ → ℂ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    (hΦd : DifferentiableOn ℂ Φ {s : ℂ | 1 / 2 < s.re})
    (hΦre : ∀ s : ℂ, 1 / 2 < s.re → 0 ≤ (Φ s).re)
    (hid : ∀ s : ℂ, 1 < s.re → Φ s = zetaArchimedeanDatum s + 1 / (s - 1) -
      LSeries (fun n => if 2 ≤ n then (lam n : ℂ) else 0) s)
    (hGc : ∀ s : ℂ, 1 / 2 ≤ s.re → ContinuousAt G s)
    (hGd : ∀ s : ℂ, 1 / 2 < s.re → HasDerivAt G (Φ s * G s) s) (hG2 : G 2 = bigG lam 2)
    {p : ℕ → ℂ} {ω : ℕ → ℝ} (hp : Summable fun j => ‖p j‖ * Real.exp (|ω j| / 2)) {κ₀ : ℂ}
    (hlock : ∀ τ : ℝ, τ < 0 → G (1 - lineS τ) = κ₀ * apFactor p ω (-τ) * G (lineS τ)) :
    ∃ j : ℕ, ∃ n : ℕ, (n : ℝ) = Real.exp (-(ω j / 2)) := by
  have hidT : ∀ s : ℂ, 1 < s.re →
      Φ s = zetaArchimedeanDatum s + 1 / (s - 1) - LSeries (lamTwo lam) s := hid
  by_contra hres
  push Not at hres
  have hβ : betaG G ≠ 0 := by
    unfold betaG
    exact div_ne_zero (G_ne_zero hΦd hGd hG2 (by norm_num : (1 / 2 : ℝ) < (1 : ℂ).re))
      two_ne_zero
  have h0 : apMean p ω = 0 := by
    unfold apMean
    have : ∀ j, (if ω j = 0 then p j else 0) = 0 := fun j => by
      rw [if_neg]
      intro hj
      exact hres j 1 (by rw [hj]; simp)
    simp [this]
  have h := tendsto_ap_lock_radial hsl hΦd hΦre hidT hGc hGd hG2 hp hlock (m := 1) le_rfl
    (fun j _ n => by rw [Nat.cast_one, one_mul]; exact hres j n)
  simp only [h0, mul_zero, zero_mul] at h
  have h2 := tendsto_nhds_unique tendsto_const_nhds h
  exact hβ ((mul_eq_zero.mp h2.symm).resolve_left two_ne_zero)

/-- **Almost-periodic lock rigidity.**  Let `G` be a Herglotz producer for the weights `lam` with
lower-line lock `G(1 − s) = κ₀ P(x) G(s)`, `s = ½ − 2ix`, `x > 0`, where
`P(x) = Σ_j p_j e^{iω_j x}` and `Σ_j |p_j| e^{|ω_j|/2} < ∞`.  Suppose no nonzero frequency has
`e^{−ω_j/2} ∈ ℚ_{>0}`.  Then the mean `p₀ = Σ_{ω_j = 0} p_j` is nonzero, `lam(n) = Λ(n)` for all
`n ≥ 2`, and RH holds. -/
theorem ap_lock_rigidity {lam : ℕ → ℝ} {Φ G : ℂ → ℂ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    (hΦd : DifferentiableOn ℂ Φ {s : ℂ | 1 / 2 < s.re})
    (hΦre : ∀ s : ℂ, 1 / 2 < s.re → 0 ≤ (Φ s).re)
    (hid : ∀ s : ℂ, 1 < s.re → Φ s = zetaArchimedeanDatum s + 1 / (s - 1) -
      LSeries (fun n => if 2 ≤ n then (lam n : ℂ) else 0) s)
    (hGc : ∀ s : ℂ, 1 / 2 ≤ s.re → ContinuousAt G s)
    (hGd : ∀ s : ℂ, 1 / 2 < s.re → HasDerivAt G (Φ s * G s) s) (hG2 : G 2 = bigG lam 2)
    {p : ℕ → ℂ} {ω : ℕ → ℝ} (hp : Summable fun j => ‖p j‖ * Real.exp (|ω j| / 2)) {κ₀ : ℂ}
    (hlock : ∀ τ : ℝ, τ < 0 → G (1 - lineS τ) = κ₀ * apFactor p ω (-τ) * G (lineS τ))
    (hres : ∀ j, ω j ≠ 0 → ∀ m n : ℕ, 1 ≤ m → (n : ℝ) ≠ m * Real.exp (-(ω j / 2))) :
    apMean p ω ≠ 0 ∧ (∀ n : ℕ, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n) ∧
      RiemannHypothesis := by
  have hidT : ∀ s : ℂ, 1 < s.re →
      Φ s = zetaArchimedeanDatum s + 1 / (s - 1) - LSeries (lamTwo lam) s := hid
  set a := dirichletExp (lamLog lam) with ha_def
  have ha1 : a 1 = 1 := dirichletExp_one (lamLog_zero lam) (lamLog_one lam)
  have hβ : betaG G ≠ 0 := by
    unfold betaG
    exact div_ne_zero (G_ne_zero hΦd hGd hG2 (by norm_num : (1 / 2 : ℝ) < (1 : ℂ).re))
      two_ne_zero
  have hrad : ∀ m : ℕ, 1 ≤ m → Tendsto (fun ε : ℝ => κ₀ * apMean p ω * a m *
      mainTwist 0 (fun _ => 0) (ε / m)) (𝓝[>] 0) (𝓝 (2 * betaG G)) := fun m hm =>
    tendsto_ap_lock_radial hsl hΦd hΦre hidT hGc hGd hG2 hp hlock hm
      (fun j hj n => hres j hj m n hm)
  have h1 : Tendsto (fun ε => κ₀ * apMean p ω * mainTwist 0 (fun _ => 0) ε) (𝓝[>] 0)
      (𝓝 (2 * betaG G)) := by
    refine (hrad 1 le_rfl).congr fun ε => ?_
    rw [ha1, Nat.cast_one, div_one, mul_one]
  have hp0 : apMean p ω ≠ 0 := by
    intro h0
    simp only [h0, mul_zero, zero_mul] at h1
    have h2 := tendsto_nhds_unique tendsto_const_nhds h1
    exact hβ ((mul_eq_zero.mp h2.symm).resolve_left two_ne_zero)
  have hone : ∀ n : ℕ, n ≠ 0 → a n = 1 := by
    intro n hn
    have hm : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hm
    have hscale : Tendsto (fun ε : ℝ => ε / n) (𝓝[>] 0) (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
      · have h : Tendsto (fun ε : ℝ => ε / n) (𝓝 0) (𝓝 (0 / n)) :=
          (continuous_id.div_const _).tendsto 0
        rw [zero_div] at h
        exact h.mono_left nhdsWithin_le_nhds
      · exact eventually_nhdsWithin_of_forall fun ε hε => div_pos hε hn0
    have hA := (h1.comp hscale).const_mul (a n)
    have hB' : Tendsto (fun ε => a n * (κ₀ * apMean p ω * mainTwist 0 (fun _ => 0) (ε / n)))
        (𝓝[>] 0) (𝓝 (2 * betaG G)) := (hrad n hm).congr fun ε => by ring
    have heq := tendsto_nhds_unique hA hB'
    exact mul_right_cancel₀ (mul_ne_zero two_ne_zero hβ) (heq.trans (one_mul _).symm)
  exact ⟨hp0, vonMangoldt_and_RH_of_coeff_eq_one hsl hΦd hidT hGd hG2 hone⟩

end

end AbelianTwist

end RHTower
