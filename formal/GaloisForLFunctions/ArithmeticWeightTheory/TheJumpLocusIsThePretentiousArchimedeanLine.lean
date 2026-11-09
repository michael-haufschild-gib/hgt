import GaloisForLFunctions.ArithmeticWeightTheory.EulerDeformationsOfZetaAreIsozeric

/-!
# The jump locus is the pretentious archimedean line

For the Mellin family of a sheaf over `𝔽_q` the characters at which `H⁰` and `H²` jump form the
jump locus, a finite union of torsion translates of subtori (generic vanishing). The gauge family
of `Spec ℤ` has one kind of jump: a pole of the fibre `ζ_x` on the line `Re s = 1`, the coinvariant
present at `ζ` (`TheTrivialFibreIsTheJump`). This file determines where it occurs.

**Theorem** (`pole_iff_pretentious`). For every fibre `x` and height `τ`, `ζ_x` has a pole at
`1 + iτ` — `δ |ζ_x(1 + δ + iτ)|` stays bounded below as `δ ↓ 0` — iff the pretentious distance

  `D(x, τ)² = Σ_p (1 − Re(χ_x(p) p^{−iτ}))/p`

is finite, i.e. `χ_x` pretends to be the archimedean character `n^{iτ}`. Otherwise
`δ |ζ_x(1 + δ + iτ)| → 0` (`tendsto_mul_norm_gaugeFibre_of_not_pretentious`). The pole has order
at most one at every fibre and height (`eventually_mul_norm_gaugeFibre_le`).

**Proof.** On `Re s > 1`, `|ζ_x(s)| = |ζ(1 + δ)| e^{−D_δ + O(1)}` with
`D_δ = Σ_p (1 − Re χ_x(p) p^{−iτ}) p^{−1−δ}` (`norm_gaugeFibre_polePoint_eq`); the remainder of the
fibre logarithm is bounded by `2 Σ p^{−2}`, and `δ ζ(1 + δ) → 1`. `D_δ` is bounded by `D(x, τ)²`,
and tends to infinity when the series diverges.

**Consequences.** The archimedean line `n^{it}` lies in the jump locus with its pole at `1 + it`
(`pretentious_archimedeanLine`), and so does every fibre at finite pretentious distance from it.
The jump locus is Haar-null (`gaugeHaar_jumpLocus_eq_zero`): almost every fibre is analytic across
`Re s = 1`. Over `ℤ` the archimedean line plays the subtorus, and pretentious equivalence the torsion
translation, of generic vanishing.
-/

open MeasureTheory Filter Topology Complex

noncomputable section

namespace GaloisForLFunctions.ArithmeticWeightTheory

open ArithmeticCorrelationGeometry PrimeTorusTheory

/-- The point `1 + δ + iτ`. -/
def polePoint (δ τ : ℝ) : ℂ := ((1 + δ : ℝ) : ℂ) + (τ : ℂ) * I

@[simp] theorem polePoint_re (δ τ : ℝ) : (polePoint δ τ).re = 1 + δ := by simp [polePoint]

/-- The pretentious term `1 − Re(χ_x(p) p^{−iτ})` of the fibre `x` against `n^{iτ}`. -/
def pretTerm (x : GaugeTorus) (τ : ℝ) (p : ℕ) : ℝ :=
  1 - (((p : ℂ) ^ (-((τ : ℂ) * I))) * twist x p).re

theorem norm_natCast_cpow_neg_mul_I {p : ℕ} (hp : 0 < p) (τ : ℝ) :
    ‖(p : ℂ) ^ (-((τ : ℂ) * I))‖ = 1 := by
  rw [Complex.norm_natCast_cpow_of_pos hp]
  simp

theorem neg_re_le_norm' (z : ℂ) : -z.re ≤ ‖z‖ := (neg_le_abs _).trans (Complex.abs_re_le_norm _)

theorem pretTerm_nonneg (x : GaugeTorus) (τ : ℝ) {p : ℕ} (hp : 0 < p) : 0 ≤ pretTerm x τ p := by
  unfold pretTerm
  have h := Complex.re_le_norm ((p : ℂ) ^ (-((τ : ℂ) * I)) * twist x p)
  rw [norm_mul, norm_natCast_cpow_neg_mul_I hp, norm_twist, one_mul] at h
  linarith

theorem pretTerm_le_two (x : GaugeTorus) (τ : ℝ) {p : ℕ} (hp : 0 < p) : pretTerm x τ p ≤ 2 := by
  unfold pretTerm
  have h := neg_re_le_norm' ((p : ℂ) ^ (-((τ : ℂ) * I)) * twist x p)
  rw [norm_mul, norm_natCast_cpow_neg_mul_I hp, norm_twist, one_mul] at h
  linarith

/-- The real part of the Euler variable at `1 + δ + iτ`. -/
theorem re_eulerVar_polePoint (x : GaugeTorus) (δ τ : ℝ) {p : ℕ} (hp : 0 < p) :
    (eulerVar (polePoint δ τ) (twist x) p).re = (p : ℝ) ^ (-(1 + δ)) * (1 - pretTerm x τ p) := by
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  have hsplit : (p : ℂ) ^ (-polePoint δ τ) =
      (((p : ℝ) ^ (-(1 + δ)) : ℝ) : ℂ) * (p : ℂ) ^ (-((τ : ℂ) * I)) := by
    rw [Complex.ofReal_cpow (Nat.cast_nonneg p), Complex.ofReal_natCast, ← Complex.cpow_add _ _ hp0]
    congr 1
    simp only [polePoint]
    push_cast
    ring
  unfold eulerVar powCoeff pretTerm
  rw [hsplit, mul_assoc, Complex.re_ofReal_mul]
  ring

/-- The pretentious sum at damping `δ`. -/
def pretSum (x : GaugeTorus) (τ δ : ℝ) : ℝ :=
  ∑' p : Nat.Primes, ((p : ℕ) : ℝ) ^ (-(1 + δ)) * pretTerm x τ p

theorem summable_primes_pow_neg {δ : ℝ} (hδ : 0 < δ) :
    Summable fun p : Nat.Primes => ((p : ℕ) : ℝ) ^ (-(1 + δ)) :=
  summable_primes_rpow (by linarith)

theorem summable_pretSum_terms (x : GaugeTorus) (τ : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    Summable fun p : Nat.Primes => ((p : ℕ) : ℝ) ^ (-(1 + δ)) * pretTerm x τ p :=
  Summable.of_nonneg_of_le
    (fun p => mul_nonneg (by positivity) (pretTerm_nonneg x τ p.2.pos))
    (fun p => mul_le_mul_of_nonneg_left (pretTerm_le_two x τ p.2.pos) (by positivity))
    ((summable_primes_pow_neg hδ).mul_right 2)

theorem pretSum_nonneg (x : GaugeTorus) (τ δ : ℝ) : 0 ≤ pretSum x τ δ :=
  tsum_nonneg fun p => mul_nonneg (by positivity) (pretTerm_nonneg x τ p.2.pos)

/-- The remainder of the fibre logarithm is bounded on `Re s ≥ 1`. -/
theorem norm_hullRem_le (x : GaugeTorus) {s : ℂ} (hs : 1 ≤ s.re) :
    ‖hullRem s (twist x)‖ ≤ 2 * ∑' p : Nat.Primes, ((p : ℕ) : ℝ) ^ (-2 : ℝ) := by
  have hs' : 1 / 2 < s.re := by linarith
  have hsum2 : Summable fun p : Nat.Primes => ((p : ℕ) : ℝ) ^ (-2 : ℝ) :=
    summable_primes_rpow (by norm_num)
  unfold hullRem
  refine (norm_tsum_le_tsum_norm (summable_localRem (norm_twist_prime x) hs').norm).trans ?_
  rw [← tsum_mul_left]
  refine Summable.tsum_le_tsum (fun p => ?_) (summable_localRem (norm_twist_prime x) hs').norm
    (hsum2.mul_left 2)
  refine (norm_localRem_le (norm_twist_prime x) p.2 hs').trans ?_
  gcongr
  · exact_mod_cast p.2.one_lt.le
  · linarith

/-- **The fibre against `ζ`.** `|ζ_x(1 + δ + iτ)| = |ζ(1 + δ)| e^{−D_δ + E}` with
`E = Re h_x(1 + δ + iτ) − Re h_0(1 + δ)`. -/
theorem norm_gaugeFibre_polePoint_eq (x : GaugeTorus) (τ : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ‖gaugeFibre x (polePoint δ τ)‖ = ‖riemannZeta (polePoint δ 0)‖ *
      Real.exp (-pretSum x τ δ + ((hullRem (polePoint δ τ) (twist x)).re -
        (hullRem (polePoint δ 0) (twist 0)).re)) := by
  have hs : 1 < (polePoint δ τ).re := by simp; linarith
  have hs0 : 1 < (polePoint δ 0).re := by simp; linarith
  have hx := exp_tsum_eq_gaugeFibre x hs
  have h0 := exp_tsum_eq_gaugeFibre (0 : GaugeTorus) hs0
  rw [gaugeFibre_trivial hs0] at h0
  rw [← hx, ← h0, Complex.norm_exp, Complex.norm_exp, ← Real.exp_add]
  congr 1
  rw [Complex.add_re, Complex.add_re,
    Complex.re_tsum (summable_eulerVar (norm_twist_prime x) hs),
    Complex.re_tsum (summable_eulerVar (norm_twist_prime 0) hs0)]
  have hxs : ∀ p : Nat.Primes, (eulerVar (polePoint δ τ) (twist x) p).re =
      ((p : ℕ) : ℝ) ^ (-(1 + δ)) - ((p : ℕ) : ℝ) ^ (-(1 + δ)) * pretTerm x τ p := fun p => by
    rw [re_eulerVar_polePoint x δ τ p.2.pos]; ring
  have h0s : ∀ p : Nat.Primes, (eulerVar (polePoint δ 0) (twist 0) p).re =
      ((p : ℕ) : ℝ) ^ (-(1 + δ)) := fun p => by
    rw [re_eulerVar_polePoint 0 δ 0 p.2.pos]
    have : pretTerm 0 0 p = 0 := by simp [pretTerm, twist_trivial]
    rw [this]; ring
  rw [tsum_congr hxs, tsum_congr h0s,
    Summable.tsum_sub (summable_primes_pow_neg hδ) (summable_pretSum_terms x τ hδ)]
  unfold pretSum
  ring

/-- `δ ζ(1 + δ) → 1`. -/
theorem tendsto_mul_norm_zeta_polePoint :
    Tendsto (fun δ : ℝ => δ * ‖riemannZeta (polePoint δ 0)‖) (𝓝[>] 0) (𝓝 1) := by
  have hmap : Tendsto (fun δ : ℝ => polePoint δ 0) (𝓝[>] 0) (𝓝[≠] (1 : ℂ)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have hc : Continuous fun δ : ℝ => polePoint δ 0 := by
        unfold polePoint; fun_prop
      have h := hc.tendsto 0
      have h1 : polePoint 0 0 = 1 := by simp [polePoint]
      rw [h1] at h
      exact h.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with δ hδ
      have hδ0 : (0 : ℝ) < δ := hδ
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      intro h
      have h2 := congrArg Complex.re h
      rw [polePoint_re, Complex.one_re] at h2
      linarith
  have h := (riemannZeta_residue_one.comp hmap).norm
  rw [norm_one] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  have hδ0 : (0 : ℝ) < δ := hδ
  simp only [Function.comp, norm_mul, polePoint]
  congr 1
  simp [abs_of_pos hδ0]

/-- **Every pole has order at most one.** -/
theorem eventually_mul_norm_gaugeFibre_le (x : GaugeTorus) (τ : ℝ) :
    ∀ᶠ δ in 𝓝[>] (0 : ℝ), δ * ‖gaugeFibre x (polePoint δ τ)‖ ≤
      2 * Real.exp (4 * ∑' p : Nat.Primes, ((p : ℕ) : ℝ) ^ (-2 : ℝ)) := by
  set H := 2 * ∑' p : Nat.Primes, ((p : ℕ) : ℝ) ^ (-2 : ℝ)
  filter_upwards [tendsto_mul_norm_zeta_polePoint.eventually (gt_mem_nhds (by norm_num : (1 : ℝ) < 2)),
    self_mem_nhdsWithin] with δ hζ hδ
  have hδ0 : (0 : ℝ) < δ := hδ
  have hE : -pretSum x τ δ + ((hullRem (polePoint δ τ) (twist x)).re -
      (hullRem (polePoint δ 0) (twist 0)).re) ≤ 2 * H := by
    have h1 := (Complex.re_le_norm _).trans (norm_hullRem_le x (s := polePoint δ τ) (by simp; linarith))
    have h2 := (neg_re_le_norm' _).trans
      (norm_hullRem_le 0 (s := polePoint δ 0) (by simp; linarith))
    linarith [pretSum_nonneg x τ δ]
  rw [norm_gaugeFibre_polePoint_eq x τ hδ0, ← mul_assoc]
  calc δ * ‖riemannZeta (polePoint δ 0)‖ * Real.exp (-pretSum x τ δ +
        ((hullRem (polePoint δ τ) (twist x)).re - (hullRem (polePoint δ 0) (twist 0)).re))
      ≤ 2 * Real.exp (2 * H) :=
        mul_le_mul hζ.le (Real.exp_le_exp.mpr hE) (by positivity) (by norm_num)
    _ = 2 * Real.exp (4 * ∑' p : Nat.Primes, ((p : ℕ) : ℝ) ^ (-2 : ℝ)) := by
        congr 2; simp only [H]; ring

/-- **A pretentious fibre has a pole.** -/
theorem exists_pole_of_pretentious {x : GaugeTorus} {τ : ℝ}
    (hD : Summable fun p : Nat.Primes => pretTerm x τ p / (p : ℕ)) :
    ∃ c > 0, ∀ᶠ δ in 𝓝[>] (0 : ℝ), c ≤ δ * ‖gaugeFibre x (polePoint δ τ)‖ := by
  set H := 2 * ∑' p : Nat.Primes, ((p : ℕ) : ℝ) ^ (-2 : ℝ)
  set S := ∑' p : Nat.Primes, pretTerm x τ p / (p : ℕ)
  refine ⟨Real.exp (-(S + 2 * H)) / 2, by positivity, ?_⟩
  filter_upwards [tendsto_mul_norm_zeta_polePoint.eventually (lt_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1)),
    self_mem_nhdsWithin] with δ hζ hδ
  have hδ0 : (0 : ℝ) < δ := hδ
  have hDS : pretSum x τ δ ≤ S := by
    refine Summable.tsum_le_tsum (fun p => ?_) (summable_pretSum_terms x τ hδ0) hD
    have hp1 : (1 : ℝ) ≤ ((p : ℕ) : ℝ) := by exact_mod_cast p.2.one_lt.le
    have hpow : ((p : ℕ) : ℝ) ^ (-(1 + δ)) ≤ ((p : ℕ) : ℝ)⁻¹ := by
      rw [← Real.rpow_neg_one]
      exact Real.rpow_le_rpow_of_exponent_le hp1 (by linarith)
    calc ((p : ℕ) : ℝ) ^ (-(1 + δ)) * pretTerm x τ p ≤ ((p : ℕ) : ℝ)⁻¹ * pretTerm x τ p :=
          mul_le_mul_of_nonneg_right hpow (pretTerm_nonneg x τ p.2.pos)
      _ = pretTerm x τ p / (p : ℕ) := by rw [div_eq_inv_mul]
  have hE : -(S + 2 * H) ≤ -pretSum x τ δ + ((hullRem (polePoint δ τ) (twist x)).re -
      (hullRem (polePoint δ 0) (twist 0)).re) := by
    have h1 := (neg_re_le_norm' _).trans
      (norm_hullRem_le x (s := polePoint δ τ) (by simp; linarith))
    have h2 := (Complex.re_le_norm _).trans (norm_hullRem_le 0 (s := polePoint δ 0) (by simp; linarith))
    linarith
  have hmain : 1 / 2 * Real.exp (-(S + 2 * H)) ≤ δ * ‖riemannZeta (polePoint δ 0)‖ *
      Real.exp (-pretSum x τ δ + ((hullRem (polePoint δ τ) (twist x)).re -
        (hullRem (polePoint δ 0) (twist 0)).re)) :=
    mul_le_mul hζ.le (Real.exp_le_exp.mpr hE) (by positivity) (by positivity)
  rw [norm_gaugeFibre_polePoint_eq x τ hδ0, ← mul_assoc]
  linarith

/-- **A non-pretentious fibre has no pole.** -/
theorem tendsto_mul_norm_gaugeFibre_of_not_pretentious {x : GaugeTorus} {τ : ℝ}
    (hD : ¬ Summable fun p : Nat.Primes => pretTerm x τ p / (p : ℕ)) :
    Tendsto (fun δ : ℝ => δ * ‖gaugeFibre x (polePoint δ τ)‖) (𝓝[>] 0) (𝓝 0) := by
  set H := 2 * ∑' p : Nat.Primes, ((p : ℕ) : ℝ) ^ (-2 : ℝ)
  -- the pretentious sums tend to infinity
  have hinf : Tendsto (fun δ => pretSum x τ δ) (𝓝[>] 0) atTop := by
    refine tendsto_atTop.mpr fun M => ?_
    have hex : ∃ F : Finset Nat.Primes, M + 1 < ∑ p ∈ F, pretTerm x τ p / (p : ℕ) := by
      by_contra hne
      push Not at hne
      exact hD (summable_of_sum_le (fun p => div_nonneg (pretTerm_nonneg x τ p.2.pos)
        (Nat.cast_nonneg _)) hne)
    obtain ⟨F, hF⟩ := hex
    have hcont : Tendsto (fun δ : ℝ => ∑ p ∈ F, ((p : ℕ) : ℝ) ^ (-(1 + δ)) * pretTerm x τ p)
        (𝓝[>] 0) (𝓝 (∑ p ∈ F, pretTerm x τ p / (p : ℕ))) := by
      have : ∑ p ∈ F, pretTerm x τ p / (p : ℕ) =
          ∑ p ∈ F, ((p : ℕ) : ℝ) ^ (-(1 + (0 : ℝ))) * pretTerm x τ p := by
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [add_zero, Real.rpow_neg_one, div_eq_inv_mul]
      rw [this]
      refine (tendsto_finsetSum _ fun p _ => ?_).mono_left nhdsWithin_le_nhds
      have hp0 : (0 : ℝ) < ((p : ℕ) : ℝ) := by exact_mod_cast p.2.pos
      exact ((continuous_const.rpow (continuous_const.add continuous_id).neg
        fun _ => Or.inl hp0.ne').tendsto 0).mul_const _
    have hMF : M < ∑ p ∈ F, pretTerm x τ p / (p : ℕ) := by linarith
    filter_upwards [hcont.eventually (lt_mem_nhds hMF), self_mem_nhdsWithin] with δ hδF hδ
    have hδ0 : (0 : ℝ) < δ := hδ
    refine le_of_lt (hδF.trans_le ?_)
    exact (summable_pretSum_terms x τ hδ0).sum_le_tsum F
      (fun p _ => mul_nonneg (by positivity) (pretTerm_nonneg x τ p.2.pos))
  have hexp : Tendsto (fun δ => Real.exp (-pretSum x τ δ + 2 * H)) (𝓝[>] 0) (𝓝 0) := by
    have := Real.tendsto_exp_neg_atTop_nhds_zero.comp hinf
    have h2 := this.mul_const (Real.exp (2 * H))
    rw [zero_mul] at h2
    refine h2.congr' (Eventually.of_forall fun δ => ?_)
    simp only [Function.comp, ← Real.exp_add]
  have hupper : ∀ᶠ δ in 𝓝[>] (0 : ℝ), δ * ‖gaugeFibre x (polePoint δ τ)‖ ≤
      2 * Real.exp (-pretSum x τ δ + 2 * H) := by
    filter_upwards [tendsto_mul_norm_zeta_polePoint.eventually (gt_mem_nhds (by norm_num : (1 : ℝ) < 2)),
      self_mem_nhdsWithin] with δ hζ hδ
    have hδ0 : (0 : ℝ) < δ := hδ
    have hE : -pretSum x τ δ + ((hullRem (polePoint δ τ) (twist x)).re -
        (hullRem (polePoint δ 0) (twist 0)).re) ≤ -pretSum x τ δ + 2 * H := by
      have h1 := (Complex.re_le_norm _).trans (norm_hullRem_le x (s := polePoint δ τ) (by simp; linarith))
      have h2 := (neg_re_le_norm' _).trans
        (norm_hullRem_le 0 (s := polePoint δ 0) (by simp; linarith))
      linarith
    rw [norm_gaugeFibre_polePoint_eq x τ hδ0, ← mul_assoc]
    exact mul_le_mul hζ.le (Real.exp_le_exp.mpr hE) (by positivity) (by norm_num)
  have hlow : ∀ᶠ δ in 𝓝[>] (0 : ℝ), 0 ≤ δ * ‖gaugeFibre x (polePoint δ τ)‖ := by
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact mul_nonneg (le_of_lt hδ) (norm_nonneg _)
  have h2 := hexp.const_mul 2
  rw [mul_zero] at h2
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h2 hlow hupper

/-- **Pole iff pretentious.** `ζ_x` has a pole at `1 + iτ` iff `χ_x` is at finite pretentious
distance from `n^{iτ}`. -/
theorem pole_iff_pretentious (x : GaugeTorus) (τ : ℝ) :
    (∃ c > 0, ∀ᶠ δ in 𝓝[>] (0 : ℝ), c ≤ δ * ‖gaugeFibre x (polePoint δ τ)‖) ↔
      Summable fun p : Nat.Primes => pretTerm x τ p / (p : ℕ) := by
  refine ⟨fun ⟨c, hc, hev⟩ => ?_, exists_pole_of_pretentious⟩
  by_contra hD
  have h := (tendsto_mul_norm_gaugeFibre_of_not_pretentious hD).eventually (gt_mem_nhds hc)
  obtain ⟨δ, h1, h2⟩ := (hev.and h).exists
  linarith

/-- **The archimedean line is in the jump locus**: `n^{it}` has its pole at `1 + it`. -/
theorem pretentious_archimedeanLine (t : ℝ) :
    Summable fun p : Nat.Primes =>
      pretTerm (HTGeometry.clockPhasePoint (fun p => Real.log p) t) t p / (p : ℕ) := by
  have h0 : ∀ p : Nat.Primes, pretTerm (HTGeometry.clockPhasePoint (fun p => Real.log p) t) t p = 0 := by
    intro p
    have hp0 : ((p : ℕ) : ℂ) ≠ 0 := by exact_mod_cast p.2.ne_zero
    have hprod : ((p : ℕ) : ℂ) ^ (-((t : ℂ) * I)) *
        twist (HTGeometry.clockPhasePoint (fun p => Real.log p) t) (p : ℕ) = 1 := by
      rw [twist_clockPhasePoint, Complex.cpow_def_of_ne_zero hp0, ← Complex.exp_add]
      convert Complex.exp_zero using 2
      rw [← Complex.natCast_log]
      push_cast
      ring
    unfold pretTerm
    rw [hprod, Complex.one_re, sub_self]
  simp [h0]

/-- **The jump locus is Haar-null.** Almost every fibre is analytic across `Re s = 1`. -/
theorem gaugeHaar_jumpLocus_eq_zero :
    gaugeHaar {x : GaugeTorus | ∃ τ : ℝ, Summable fun p : Nat.Primes => pretTerm x τ p / (p : ℕ)} = 0 := by
  refine measure_mono_null ?_ (ae_iff.mp ae_fibre_extends_zeroFree)
  intro x hx
  obtain ⟨τ, hτ⟩ := hx
  rintro ⟨G, hGa, hGeq, -⟩
  obtain ⟨c, hc, hev⟩ := exists_pole_of_pretentious hτ
  set s₁ : ℂ := polePoint 0 τ
  have hs₁ : s₁ ∈ rightHalf := by
    show (1 / 2 : ℝ) < (polePoint 0 τ).re
    simp; norm_num
  have hGc : ContinuousAt G s₁ := (hGa s₁ hs₁).continuousAt
  have hpath : Tendsto (fun δ : ℝ => polePoint δ τ) (𝓝[>] 0) (𝓝 s₁) := by
    have hc : Continuous fun δ : ℝ => polePoint δ τ := by unfold polePoint; fun_prop
    exact (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  have hlim : Tendsto (fun δ : ℝ => δ * ‖G (polePoint δ τ)‖) (𝓝[>] 0) (𝓝 (0 * ‖G s₁‖)) :=
    (tendsto_id.mono_left nhdsWithin_le_nhds).mul (hGc.tendsto.comp hpath).norm
  rw [zero_mul] at hlim
  have heq : ∀ᶠ δ in 𝓝[>] (0 : ℝ),
      δ * ‖G (polePoint δ τ)‖ = δ * ‖gaugeFibre x (polePoint δ τ)‖ := by
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    have hδ0 : (0 : ℝ) < δ := hδ
    rw [hGeq (polePoint δ τ) (by simp; linarith)]
  have h := (hlim.congr' heq).eventually (gt_mem_nhds hc)
  obtain ⟨δ, h1, h2⟩ := (hev.and h).exists
  linarith

end GaloisForLFunctions.ArithmeticWeightTheory
