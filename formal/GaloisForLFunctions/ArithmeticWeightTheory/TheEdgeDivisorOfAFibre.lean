import GaloisForLFunctions.ArithmeticWeightTheory.TheJumpLocusIsThePretentiousArchimedeanLine

/-!
# The edge divisor of a fibre

`TheJumpLocusIsThePretentiousArchimedeanLine` finds the poles of the fibres `ζ_x` on the edge
`Re s = 1`. The same computation finds their zeros there, and together they give the whole edge
divisor of every fibre.

**Theorem** (`edgeZero_iff_antiPretentious`). `ζ_x` has a zero at `1 + iτ` — `|ζ_x(1 + δ + iτ)| ≤ Cδ`
as `δ ↓ 0` — iff `Σ_p (1 + Re(χ_x(p) p^{−iτ}))/p < ∞`, i.e. `χ_x` pretends to be `−n^{iτ}`. The
Liouville point `χ(p) = −1` has its zero at `1` (`antiPretentious_of_twist_eq_neg_one`).

**Theorem** (`eventually_mul_le_norm_gaugeFibre`). Edge zeros have order at most one, with a
universal constant: `|ζ_x(1 + δ + iτ)| ≥ c₀ δ` for every fibre and height.

**Edge divisor.** At every point `1 + iτ` every fibre has a simple pole (pretending `n^{iτ}`), a
simple zero (pretending `−n^{iτ}`), or neither; never both (`not_pretentious_and_antiPretentious`).
The order-one bounds come from the Euler product alone: local roots of modulus one fix the edge
weights uniformly over the family, the analogue of the fixed weight of `H⁰` and `H²`. Both loci are
Haar-null (`gaugeHaar_edgeZeroLocus_eq_zero`).

**Proof.** `|ζ(1 + δ)| |ζ_x(1 + δ + iτ)| = exp(A_δ + O(1))` with
`A_δ = Σ_p (1 + Re χ_x(p)p^{−iτ}) p^{−1−δ}` (`norm_zeta_mul_norm_gaugeFibre_eq`), and `δ ζ(1 + δ) → 1`.
-/

open MeasureTheory Filter Topology Complex

noncomputable section

namespace GaloisForLFunctions.ArithmeticWeightTheory

open ArithmeticCorrelationGeometry PrimeTorusTheory

/-- The anti-pretentious term `1 + Re(χ_x(p) p^{−iτ}) = 2 − pretTerm`. -/
def antiTerm (x : GaugeTorus) (τ : ℝ) (p : ℕ) : ℝ := 2 - pretTerm x τ p

theorem antiTerm_nonneg (x : GaugeTorus) (τ : ℝ) {p : ℕ} (hp : 0 < p) : 0 ≤ antiTerm x τ p := by
  unfold antiTerm; linarith [pretTerm_le_two x τ hp]

/-- The anti-pretentious sum at damping `δ`. -/
def antiSum (x : GaugeTorus) (τ δ : ℝ) : ℝ :=
  ∑' p : Nat.Primes, ((p : ℕ) : ℝ) ^ (-(1 + δ)) * antiTerm x τ p

theorem summable_antiSum_terms (x : GaugeTorus) (τ : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    Summable fun p : Nat.Primes => ((p : ℕ) : ℝ) ^ (-(1 + δ)) * antiTerm x τ p :=
  Summable.of_nonneg_of_le
    (fun p => mul_nonneg (by positivity) (antiTerm_nonneg x τ p.2.pos))
    (fun p => mul_le_mul_of_nonneg_left
      (by unfold antiTerm; linarith [pretTerm_nonneg x τ p.2.pos]) (by positivity))
    ((summable_primes_pow_neg hδ).mul_right 2)

theorem antiSum_nonneg (x : GaugeTorus) (τ δ : ℝ) : 0 ≤ antiSum x τ δ :=
  tsum_nonneg fun p => mul_nonneg (by positivity) (antiTerm_nonneg x τ p.2.pos)

/-- `|ζ(1 + δ)| = exp(Σ_p p^{−1−δ} + Re h_0)`. -/
theorem norm_zeta_polePoint_eq {δ : ℝ} (hδ : 0 < δ) :
    ‖riemannZeta (polePoint δ 0)‖ = Real.exp ((∑' p : Nat.Primes, ((p : ℕ) : ℝ) ^ (-(1 + δ))) +
      (hullRem (polePoint δ 0) (twist 0)).re) := by
  have hs0 : 1 < (polePoint δ 0).re := by simp; linarith
  have h0 := exp_tsum_eq_gaugeFibre (0 : GaugeTorus) hs0
  rw [gaugeFibre_trivial hs0] at h0
  rw [← h0, Complex.norm_exp, Complex.add_re,
    Complex.re_tsum (summable_eulerVar (norm_twist_prime 0) hs0)]
  congr 2
  refine tsum_congr fun p => ?_
  rw [re_eulerVar_polePoint 0 δ 0 p.2.pos]
  have : pretTerm 0 0 p = 0 := by simp [pretTerm, twist_trivial]
  rw [this]; ring

/-- **The product formula.** `|ζ(1 + δ)| |ζ_x(1 + δ + iτ)| = exp(A_δ + Re h_x + Re h_0)`. -/
theorem norm_zeta_mul_norm_gaugeFibre_eq (x : GaugeTorus) (τ : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ‖riemannZeta (polePoint δ 0)‖ * ‖gaugeFibre x (polePoint δ τ)‖ =
      Real.exp (antiSum x τ δ + ((hullRem (polePoint δ τ) (twist x)).re +
        (hullRem (polePoint δ 0) (twist 0)).re)) := by
  have hA : antiSum x τ δ = 2 * (∑' p : Nat.Primes, ((p : ℕ) : ℝ) ^ (-(1 + δ))) - pretSum x τ δ := by
    unfold antiSum pretSum antiTerm
    rw [← tsum_mul_left, ← Summable.tsum_sub ((summable_primes_pow_neg hδ).mul_left 2)
      (summable_pretSum_terms x τ hδ)]
    exact tsum_congr fun p => by ring
  rw [norm_gaugeFibre_polePoint_eq x τ hδ, norm_zeta_polePoint_eq hδ, ← mul_assoc, ← Real.exp_add,
    ← Real.exp_add, hA]
  congr 1
  ring

/-- **Edge zeros have order at most one**, with a universal constant. -/
theorem eventually_mul_le_norm_gaugeFibre (x : GaugeTorus) (τ : ℝ) :
    ∀ᶠ δ in 𝓝[>] (0 : ℝ), Real.exp (-(4 * ∑' p : Nat.Primes, ((p : ℕ) : ℝ) ^ (-2 : ℝ))) / 2 * δ ≤
      ‖gaugeFibre x (polePoint δ τ)‖ := by
  obtain ⟨H, hH⟩ : ∃ H : ℝ, H = 2 * ∑' p : Nat.Primes, ((p : ℕ) : ℝ) ^ (-2 : ℝ) := ⟨_, rfl⟩
  filter_upwards [tendsto_mul_norm_zeta_polePoint.eventually (gt_mem_nhds (by norm_num : (1 : ℝ) < 2)),
    self_mem_nhdsWithin] with δ hζ hδ
  have hδ0 : (0 : ℝ) < δ := hδ
  have hE : -(2 * H) ≤ antiSum x τ δ + ((hullRem (polePoint δ τ) (twist x)).re +
      (hullRem (polePoint δ 0) (twist 0)).re) := by
    have h1 := (neg_re_le_norm' _).trans (norm_hullRem_le x (s := polePoint δ τ) (by simp; linarith))
    have h2 := (neg_re_le_norm' _).trans (norm_hullRem_le 0 (s := polePoint δ 0) (by simp; linarith))
    rw [hH]
    linarith [antiSum_nonneg x τ δ]
  have hprod := norm_zeta_mul_norm_gaugeFibre_eq x τ hδ0
  have hlow : Real.exp (-(2 * H)) ≤ ‖riemannZeta (polePoint δ 0)‖ * ‖gaugeFibre x (polePoint δ τ)‖ := by
    rw [hprod]; exact Real.exp_le_exp.mpr hE
  have hg := norm_nonneg (gaugeFibre x (polePoint δ τ))
  have hZδ : ‖riemannZeta (polePoint δ 0)‖ * δ ≤ 2 := by linarith
  have h5 : Real.exp (-(2 * H)) * δ ≤
      ‖riemannZeta (polePoint δ 0)‖ * ‖gaugeFibre x (polePoint δ τ)‖ * δ :=
    mul_le_mul_of_nonneg_right hlow hδ0.le
  have h6 : ‖riemannZeta (polePoint δ 0)‖ * ‖gaugeFibre x (polePoint δ τ)‖ * δ ≤
      2 * ‖gaugeFibre x (polePoint δ τ)‖ := by
    calc ‖riemannZeta (polePoint δ 0)‖ * ‖gaugeFibre x (polePoint δ τ)‖ * δ
        = (‖riemannZeta (polePoint δ 0)‖ * δ) * ‖gaugeFibre x (polePoint δ τ)‖ := by ring
      _ ≤ 2 * ‖gaugeFibre x (polePoint δ τ)‖ := mul_le_mul_of_nonneg_right hZδ hg
  have h4 : Real.exp (-(4 * ∑' p : Nat.Primes, ((p : ℕ) : ℝ) ^ (-2 : ℝ))) = Real.exp (-(2 * H)) := by
    rw [hH]; ring_nf
  rw [h4]
  linarith

/-- **An anti-pretentious fibre has an edge zero.** -/
theorem exists_edgeZero_of_antiPretentious {x : GaugeTorus} {τ : ℝ}
    (hA : Summable fun p : Nat.Primes => antiTerm x τ p / (p : ℕ)) :
    ∃ C : ℝ, ∀ᶠ δ in 𝓝[>] (0 : ℝ), ‖gaugeFibre x (polePoint δ τ)‖ ≤ C * δ := by
  obtain ⟨H, hH⟩ : ∃ H : ℝ, H = 2 * ∑' p : Nat.Primes, ((p : ℕ) : ℝ) ^ (-2 : ℝ) := ⟨_, rfl⟩
  obtain ⟨S, hS⟩ : ∃ S : ℝ, S = ∑' p : Nat.Primes, antiTerm x τ p / (p : ℕ) := ⟨_, rfl⟩
  refine ⟨2 * Real.exp (S + 2 * H), ?_⟩
  filter_upwards [tendsto_mul_norm_zeta_polePoint.eventually (lt_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1)),
    self_mem_nhdsWithin] with δ hζ hδ
  have hδ0 : (0 : ℝ) < δ := hδ
  have hAS : antiSum x τ δ ≤ S := by
    rw [hS]
    refine Summable.tsum_le_tsum (fun p => ?_) (summable_antiSum_terms x τ hδ0) hA
    have hp1 : (1 : ℝ) ≤ ((p : ℕ) : ℝ) := by exact_mod_cast p.2.one_lt.le
    have hpow : ((p : ℕ) : ℝ) ^ (-(1 + δ)) ≤ ((p : ℕ) : ℝ)⁻¹ := by
      rw [← Real.rpow_neg_one]
      exact Real.rpow_le_rpow_of_exponent_le hp1 (by linarith)
    calc ((p : ℕ) : ℝ) ^ (-(1 + δ)) * antiTerm x τ p ≤ ((p : ℕ) : ℝ)⁻¹ * antiTerm x τ p :=
          mul_le_mul_of_nonneg_right hpow (antiTerm_nonneg x τ p.2.pos)
      _ = antiTerm x τ p / (p : ℕ) := by rw [div_eq_inv_mul]
  have hE : antiSum x τ δ + ((hullRem (polePoint δ τ) (twist x)).re +
      (hullRem (polePoint δ 0) (twist 0)).re) ≤ S + 2 * H := by
    have h1 := (Complex.re_le_norm _).trans (norm_hullRem_le x (s := polePoint δ τ) (by simp; linarith))
    have h2 := (Complex.re_le_norm _).trans (norm_hullRem_le 0 (s := polePoint δ 0) (by simp; linarith))
    rw [hH]
    linarith
  have hprod := norm_zeta_mul_norm_gaugeFibre_eq x τ hδ0
  have hup : ‖riemannZeta (polePoint δ 0)‖ * ‖gaugeFibre x (polePoint δ τ)‖ ≤ Real.exp (S + 2 * H) := by
    rw [hprod]; exact Real.exp_le_exp.mpr hE
  -- `|ζ(1+δ)| > 1/(2δ)`
  have hζ2 : 1 / (2 * δ) < ‖riemannZeta (polePoint δ 0)‖ := by
    rw [div_lt_iff₀ (by positivity)]; linarith
  have hg := norm_nonneg (gaugeFibre x (polePoint δ τ))
  have h3 : 1 / (2 * δ) * ‖gaugeFibre x (polePoint δ τ)‖ ≤ Real.exp (S + 2 * H) :=
    (mul_le_mul_of_nonneg_right hζ2.le hg).trans hup
  rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)] at h3
  linarith

/-- **An edge zero needs anti-pretension.** -/
theorem antiPretentious_of_edgeZero {x : GaugeTorus} {τ : ℝ}
    (h : ∃ C : ℝ, ∀ᶠ δ in 𝓝[>] (0 : ℝ), ‖gaugeFibre x (polePoint δ τ)‖ ≤ C * δ) :
    Summable fun p : Nat.Primes => antiTerm x τ p / (p : ℕ) := by
  obtain ⟨C, hC⟩ := h
  obtain ⟨H, hH⟩ : ∃ H : ℝ, H = 2 * ∑' p : Nat.Primes, ((p : ℕ) : ℝ) ^ (-2 : ℝ) := ⟨_, rfl⟩
  -- the anti-pretentious sums stay bounded
  have hbound : ∀ᶠ δ in 𝓝[>] (0 : ℝ), antiSum x τ δ ≤ Real.log (2 * |C| + 1) + 2 * H := by
    filter_upwards [hC, tendsto_mul_norm_zeta_polePoint.eventually (gt_mem_nhds (by norm_num : (1 : ℝ) < 2)),
      self_mem_nhdsWithin] with δ hCδ hζ hδ
    have hδ0 : (0 : ℝ) < δ := hδ
    have hprod := norm_zeta_mul_norm_gaugeFibre_eq x τ hδ0
    have hE : antiSum x τ δ - 2 * H ≤ antiSum x τ δ + ((hullRem (polePoint δ τ) (twist x)).re +
        (hullRem (polePoint δ 0) (twist 0)).re) := by
      have h1 := (neg_re_le_norm' _).trans (norm_hullRem_le x (s := polePoint δ τ) (by simp; linarith))
      have h2 := (neg_re_le_norm' _).trans (norm_hullRem_le 0 (s := polePoint δ 0) (by simp; linarith))
      rw [hH]
      linarith
    have hval : ‖riemannZeta (polePoint δ 0)‖ * ‖gaugeFibre x (polePoint δ τ)‖ ≤ 2 * |C| + 1 := by
      have hζ' : ‖riemannZeta (polePoint δ 0)‖ * δ < 2 := by linarith
      have hC' : ‖gaugeFibre x (polePoint δ τ)‖ ≤ |C| * δ :=
        hCδ.trans (mul_le_mul_of_nonneg_right (le_abs_self C) hδ0.le)
      have hζ0 := norm_nonneg (riemannZeta (polePoint δ 0))
      calc ‖riemannZeta (polePoint δ 0)‖ * ‖gaugeFibre x (polePoint δ τ)‖
          ≤ ‖riemannZeta (polePoint δ 0)‖ * (|C| * δ) := mul_le_mul_of_nonneg_left hC' hζ0
        _ = |C| * (‖riemannZeta (polePoint δ 0)‖ * δ) := by ring
        _ ≤ |C| * 2 := mul_le_mul_of_nonneg_left hζ'.le (abs_nonneg C)
        _ ≤ 2 * |C| + 1 := by linarith
    rw [hprod] at hval
    have hlog := Real.log_le_log (Real.exp_pos _) hval
    rw [Real.log_exp] at hlog
    linarith
  by_contra hns
  -- otherwise the sums tend to infinity
  have hinf : Tendsto (fun δ => antiSum x τ δ) (𝓝[>] 0) atTop := by
    refine tendsto_atTop.mpr fun M => ?_
    have hex : ∃ F : Finset Nat.Primes, M + 1 < ∑ p ∈ F, antiTerm x τ p / (p : ℕ) := by
      by_contra hne
      push Not at hne
      exact hns (summable_of_sum_le (fun p => div_nonneg (antiTerm_nonneg x τ p.2.pos)
        (Nat.cast_nonneg _)) hne)
    obtain ⟨F, hF⟩ := hex
    have hcont : Tendsto (fun δ : ℝ => ∑ p ∈ F, ((p : ℕ) : ℝ) ^ (-(1 + δ)) * antiTerm x τ p)
        (𝓝[>] 0) (𝓝 (∑ p ∈ F, antiTerm x τ p / (p : ℕ))) := by
      have : ∑ p ∈ F, antiTerm x τ p / (p : ℕ) =
          ∑ p ∈ F, ((p : ℕ) : ℝ) ^ (-(1 + (0 : ℝ))) * antiTerm x τ p := by
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [add_zero, Real.rpow_neg_one, div_eq_inv_mul]
      rw [this]
      refine (tendsto_finsetSum _ fun p _ => ?_).mono_left nhdsWithin_le_nhds
      have hp0 : (0 : ℝ) < ((p : ℕ) : ℝ) := by exact_mod_cast p.2.pos
      exact ((continuous_const.rpow (continuous_const.add continuous_id).neg
        fun _ => Or.inl hp0.ne').tendsto 0).mul_const _
    have hMF : M < ∑ p ∈ F, antiTerm x τ p / (p : ℕ) := by linarith
    filter_upwards [hcont.eventually (lt_mem_nhds hMF), self_mem_nhdsWithin] with δ hδF hδ
    have hδ0 : (0 : ℝ) < δ := hδ
    refine le_of_lt (hδF.trans_le ?_)
    exact (summable_antiSum_terms x τ hδ0).sum_le_tsum F
      (fun p _ => mul_nonneg (by positivity) (antiTerm_nonneg x τ p.2.pos))
  obtain ⟨δ, h1, h2⟩ := (hbound.and (hinf.eventually_gt_atTop (Real.log (2 * |C| + 1) + 2 * H))).exists
  linarith

/-- **Edge zero iff anti-pretentious.** -/
theorem edgeZero_iff_antiPretentious (x : GaugeTorus) (τ : ℝ) :
    (∃ C : ℝ, ∀ᶠ δ in 𝓝[>] (0 : ℝ), ‖gaugeFibre x (polePoint δ τ)‖ ≤ C * δ) ↔
      Summable fun p : Nat.Primes => antiTerm x τ p / (p : ℕ) :=
  ⟨antiPretentious_of_edgeZero, exists_edgeZero_of_antiPretentious⟩

/-- **Never both.** No fibre pretends to `n^{iτ}` and to `−n^{iτ}`. -/
theorem not_pretentious_and_antiPretentious (x : GaugeTorus) (τ : ℝ) :
    ¬ ((Summable fun p : Nat.Primes => pretTerm x τ p / (p : ℕ)) ∧
      Summable fun p : Nat.Primes => antiTerm x τ p / (p : ℕ)) := by
  rintro ⟨h1, h2⟩
  have hsum : Summable fun p : Nat.Primes => (2 : ℝ) / (p : ℕ) := by
    refine (h1.add h2).congr fun p => ?_
    unfold antiTerm; ring
  have hrec := (hsum.mul_left (1 / 2)).congr (g := fun p : Nat.Primes => 1 / ((p : ℕ) : ℝ))
    fun p => by ring
  exact Nat.Primes.not_summable_one_div hrec

/-- **The Liouville point has its zero at `1`.** A fibre with `χ_x(p) = −1` at every prime is
anti-pretentious at height `0`. -/
theorem antiPretentious_of_twist_eq_neg_one {x : GaugeTorus} (hx : ∀ p : ℕ, p.Prime → twist x p = -1) :
    Summable fun p : Nat.Primes => antiTerm x 0 p / (p : ℕ) := by
  have h0 : ∀ p : Nat.Primes, antiTerm x 0 p = 0 := by
    intro p
    norm_num [antiTerm, pretTerm, hx p p.2]
  simp [h0]

/-- **The edge-zero locus is Haar-null.** Almost every fibre is zero-free across `Re s = 1`. -/
theorem gaugeHaar_edgeZeroLocus_eq_zero :
    gaugeHaar {x : GaugeTorus | ∃ τ : ℝ, Summable fun p : Nat.Primes => antiTerm x τ p / (p : ℕ)} = 0 := by
  refine measure_mono_null ?_ (ae_iff.mp ae_fibre_extends_zeroFree)
  intro x hx
  obtain ⟨τ, hτ⟩ := hx
  rintro ⟨G, hGa, hGeq, hGne⟩
  obtain ⟨C, hC⟩ := exists_edgeZero_of_antiPretentious hτ
  set s₁ : ℂ := polePoint 0 τ
  have hs₁ : s₁ ∈ rightHalf := by
    show (1 / 2 : ℝ) < (polePoint 0 τ).re
    simp; norm_num
  have hGc : ContinuousAt G s₁ := (hGa s₁ hs₁).continuousAt
  have hpath : Tendsto (fun δ : ℝ => polePoint δ τ) (𝓝[>] 0) (𝓝 s₁) := by
    have hc : Continuous fun δ : ℝ => polePoint δ τ := by unfold polePoint; fun_prop
    exact (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  have hlimG : Tendsto (fun δ : ℝ => ‖G (polePoint δ τ)‖) (𝓝[>] 0) (𝓝 ‖G s₁‖) :=
    (hGc.tendsto.comp hpath).norm
  have hlimC : Tendsto (fun δ : ℝ => C * δ) (𝓝[>] 0) (𝓝 0) := by
    have h : Tendsto (fun δ : ℝ => C * δ) (𝓝 0) (𝓝 (C * 0)) :=
      (continuous_const.mul continuous_id).tendsto 0
    rw [mul_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hle : ∀ᶠ δ in 𝓝[>] (0 : ℝ), ‖G (polePoint δ τ)‖ ≤ C * δ := by
    filter_upwards [hC, self_mem_nhdsWithin] with δ hδC hδ
    have hδ0 : (0 : ℝ) < δ := hδ
    rw [hGeq (polePoint δ τ) (by simp; linarith)]
    exact hδC
  have hG0 : ‖G s₁‖ ≤ 0 := le_of_tendsto_of_tendsto hlimG hlimC hle
  exact hGne s₁ hs₁ (norm_le_zero_iff.mp hG0)

end GaloisForLFunctions.ArithmeticWeightTheory
