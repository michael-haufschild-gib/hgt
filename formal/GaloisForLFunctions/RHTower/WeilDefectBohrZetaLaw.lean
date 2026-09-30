import GaloisForLFunctions.RHTower.SpectralMeasureZetaMassRigidity

/-!
# The Bohr–ζ law and the ζ-mass deficit law

Let `Φ` be an odd Weil function with `Γ̃(s) + 1/(s − 1) − Σ lam(n) n^{−s} = Φ(s)` on `Re s > 1`,
and let `J` be the holomorphic continuation of the Laplace transform of its thin-strip defect.
Hamburger's residue comparison computes the radial limits of `J` on the imaginary axis exactly,
with no ζ-mass hypothesis (`tendsto_mul_weilLaplace_bohr`):
`(1 ⋆ (lam − Λ))(n) + 2β = 2π · lim_{ε→0⁺} ε J(ε + in)` for every `n ≥ 1`.

For spectral measures `J` is the Laplace transform of `ζ(½ + it)`-weighted atoms and
`‖ε J(ε + in)‖ ≤ (3/π)(n + 1) δ M(δ)`, `δ = ε/(n + 1)`, where `M` is the damped ζ-mass.  Hence the
**ζ-mass deficit law** (`norm_crystallineCoeff_add_le_of_dampedZetaMass`): if `δ M(δ) ≤ A` for all
small `δ`, then `‖(1 ⋆ (lam − Λ))(n) + 2β‖ ≤ 6(n + 1) A`, and for every prime `p`,
`|lam(p) − log p| ≤ 6(p + 3) A` (`abs_sub_vonMangoldt_le_of_dampedZetaMass`).  The deviation of a
Weil function from von Mangoldt's is controlled linearly by its ζ-weighted spectral mass density;
`A = 0` is the sublinear rigidity theorem.
-/

open Complex Metric Set Filter Topology MeasureTheory

namespace RHTower

open GaloisForLFunctions.HTGeometry in
/-- **Residues along the imaginary axis, with a defect.**  Under
`L(t + i) − L(t) = c/(t + i) − c/t + K(t)` on `Re t > 0`, the product `(t − i n₀) K(t)` converges as
`t → i n₀` from the right half-plane: to `a₁/(2π) + c` at `n₀ = 0` and to `(a_{n₀+1} − a_{n₀})/(2π)`
at `n₀ ≥ 1`. -/
theorem tendsto_sub_mul_defect_residue {a : ℕ → ℂ}
    (ha : Summable fun n : ℕ => ‖a (n + 1)‖ / ((n + 1 : ℕ) : ℝ) ^ 2) (c : ℂ) (K : ℂ → ℂ)
    (hper : ∀ t : ℂ, 0 < t.re →
      hamburgerSeries a (t + I) - hamburgerSeries a t = c / (t + I) - c / t + K t)
    (n₀ : ℕ) :
    Tendsto (fun t => (t - (n₀ : ℂ) * I) * K t) (𝓝[{t : ℂ | 0 < t.re}] ((n₀ : ℂ) * I))
      (𝓝 (if n₀ = 0 then a 1 / (2 * Real.pi) + c
        else (a (n₀ + 1) - a n₀) / (2 * Real.pi))) := by
  set F := 𝓝[{t : ℂ | 0 < t.re}] ((n₀ : ℂ) * I) with hF
  have hev : (fun t => (t - (n₀ : ℂ) * I) * hamburgerSeries a (t + I) -
      (t - (n₀ : ℂ) * I) * hamburgerSeries a t -
      (t - (n₀ : ℂ) * I) * (c / (t + I) - c / t)) =ᶠ[F] fun t => (t - (n₀ : ℂ) * I) * K t := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    have h := hper t ht
    rw [← mul_sub, h]; ring
  rcases Nat.eq_zero_or_pos n₀ with h0 | hpos
  · subst h0
    rw [if_pos rfl]
    have hle := nhdsWithin_re_pos_le_punctured 0
    simp only [ofReal_zero, zero_mul] at hle
    have hF0 : F = 𝓝[{t : ℂ | 0 < t.re}] (0 : ℂ) := by rw [hF]; simp
    have h1 := (tendsto_mul_hamburgerSeries_add_I ha).mono_left hle
    have h2 : Tendsto (fun t => t * hamburgerSeries a t) (𝓝[{t : ℂ | 0 < t.re}] (0 : ℂ))
        (𝓝 0) := by
      have hz : Tendsto (fun t : ℂ => t) (𝓝[{t : ℂ | 0 < t.re}] (0 : ℂ)) (𝓝 0) :=
        tendsto_id.mono_left nhdsWithin_le_nhds
      have hL : Tendsto (hamburgerSeries a) (𝓝[{t : ℂ | 0 < t.re}] (0 : ℂ)) (𝓝 0) :=
        (tendsto_hamburgerSeries_zero ha).mono_left nhdsWithin_le_nhds
      simpa using hz.mul hL
    have h3 : Tendsto (fun t => t * (c / (t + I) - c / t)) (𝓝[{t : ℂ | 0 < t.re}] (0 : ℂ))
        (𝓝 (-c)) := by
      have hc : Tendsto (fun t : ℂ => t * (c / (t + I)) - c) (𝓝 (0 : ℂ))
          (𝓝 (0 * (c / (0 + I)) - c)) := by
        have hI : (0 : ℂ) + I ≠ 0 := by simp
        exact ((continuous_id.tendsto 0).mul ((continuous_const.tendsto 0).div
          ((continuous_id.add continuous_const).tendsto 0) hI)).sub tendsto_const_nhds
      simp only [zero_mul, zero_sub] at hc
      refine (hc.mono_left nhdsWithin_le_nhds).congr' ?_
      filter_upwards [self_mem_nhdsWithin] with t ht
      have ht0 : t ≠ 0 := by
        rintro rfl
        simp at ht
      field_simp
    have hlim := (h1.sub h2).sub h3
    rw [sub_zero, sub_neg_eq_add] at hlim
    rw [hF0] at hev ⊢
    refine (hlim.congr' ?_)
    filter_upwards [hev] with t ht
    rw [← ht]
    simp
  · have hn₀ : 1 ≤ n₀ := hpos
    have hn0' : n₀ ≠ 0 := by omega
    rw [if_neg hn0']
    have hle := nhdsWithin_re_pos_le_punctured (n₀ : ℝ)
    simp only [ofReal_natCast] at hle
    have hA := (tendsto_sub_mul_hamburgerSeries ha hn₀).mono_left hle
    have hB := tendsto_sub_mul_hamburgerSeries ha (n₀ := n₀ + 1) (by omega)
    have hshift : Tendsto (fun t : ℂ => t + I) (𝓝[≠] ((n₀ : ℂ) * I))
        (𝓝[≠] (((n₀ + 1 : ℕ) : ℂ) * I)) := by
      have hc : Tendsto (fun t : ℂ => t + I) (𝓝 ((n₀ : ℂ) * I))
          (𝓝 (((n₀ + 1 : ℕ) : ℂ) * I)) := by
        have := (continuous_id.add continuous_const).tendsto ((n₀ : ℂ) * I)
          (f := fun t : ℂ => t + I)
        convert this using 2
        push_cast; ring_nf
      refine tendsto_nhdsWithin_iff.mpr ⟨hc.mono_left nhdsWithin_le_nhds, ?_⟩
      filter_upwards [self_mem_nhdsWithin] with t ht
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at ht ⊢
      intro h
      apply ht
      push_cast at h
      linear_combination h
    have hB'' : Tendsto (fun t => (t - (n₀ : ℂ) * I) * hamburgerSeries a (t + I)) F
        (𝓝 (a (n₀ + 1) / (2 * Real.pi))) := by
      refine ((hB.comp hshift).mono_left hle).congr' (Filter.Eventually.of_forall fun t => ?_)
      simp only [Function.comp]
      congr 1
      push_cast; ring_nf
    have hn0 : (n₀ : ℂ) ≠ 0 := by exact_mod_cast hn0'
    have hR : Tendsto (fun t => (t - (n₀ : ℂ) * I) * (c / (t + I) - c / t)) F (𝓝 0) := by
      have h1 : (n₀ : ℂ) * I + I ≠ 0 := by
        intro h
        have : ((n₀ : ℂ) + 1) * I = 0 := by linear_combination h
        rcases mul_eq_zero.mp this with h' | h'
        · have : ((n₀ + 1 : ℕ) : ℂ) = 0 := by push_cast; exact h'
          exact absurd (by exact_mod_cast this) (Nat.succ_ne_zero n₀)
        · exact I_ne_zero h'
      have h2 : (n₀ : ℂ) * I ≠ 0 := mul_ne_zero hn0 I_ne_zero
      have hc : ContinuousAt (fun t => (t - (n₀ : ℂ) * I) * (c / (t + I) - c / t))
          ((n₀ : ℂ) * I) := by
        refine ContinuousAt.mul (by fun_prop) (ContinuousAt.sub ?_ ?_)
        · exact continuousAt_const.div (by fun_prop) h1
        · exact continuousAt_const.div continuousAt_id h2
      have := hc.tendsto
      simp only [sub_self, zero_mul] at this
      exact this.mono_left nhdsWithin_le_nhds
    have hlim := (hB''.sub hA).sub hR
    rw [sub_zero, ← sub_div] at hlim
    exact hlim.congr' hev

/-- The ray `ε ↦ ε + i n₀`, `ε → 0⁺`, approaches `i n₀` from the right half-plane. -/
theorem tendsto_radial_ray (n₀ : ℕ) :
    Tendsto (fun ε : ℝ => (ε : ℂ) + (n₀ : ℂ) * I) (𝓝[>] (0 : ℝ))
      (𝓝[{t : ℂ | 0 < t.re}] ((n₀ : ℂ) * I)) := by
  refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
  · have := ((Complex.continuous_ofReal.add continuous_const).tendsto (0 : ℝ)
      (f := fun ε : ℝ => (ε : ℂ) + (n₀ : ℂ) * I))
    simpa using this.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    show 0 < ((ε : ℂ) + (n₀ : ℂ) * I).re
    simpa using hε

/-- **The exact Bohr–ζ law for odd Weil functions.**  Let `Φ` be an odd Weil function with
`Γ̃ + 1/(s − 1) − Σ lam(n) n^{-s} = Φ` on `Re s > 1`, and `J` a holomorphic continuation to
`Re τ > 0` of the defect Laplace transform with `ε J(ε) → 0`.  Then for every `n ≥ 1` the radial
limit of `ε J(ε + in)` exists and
`(1 ⋆ (lam − Λ))(n) + 2β = 2π · lim_{ε→0⁺} ε J(ε + in)`.
No ζ-mass hypothesis is needed: the residue comparison computes these limits exactly. -/
theorem tendsto_mul_weilLaplace_bohr {lam : ℕ → ℝ} {Φ : ℂ → ℂ} (hΦ : OddWeilFunction Φ)
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    (hid : ∀ s : ℂ, 1 < s.re → zetaArchimedeanDatum s + 1 / (s - 1) -
      LSeries (fun n => (lam n : ℂ)) s = Φ s) {J : ℂ → ℂ}
    (hJd : DifferentiableOn ℂ J {τ : ℂ | 0 < τ.re})
    (hJ : ∀ τ : ℝ, 0 < τ → IntegrableOn (fun x : ℝ => weilDefect Φ x *
      ((Real.exp (-(Real.pi * τ ^ 2) * x) : ℝ) : ℂ)) (Ioi 0) ∧
      J τ = τ * ∫ x in Ioi (0 : ℝ), weilDefect Φ x * ((Real.exp (-(Real.pi * τ ^ 2) * x) : ℝ) : ℂ))
    (hJ0 : Tendsto (fun ε : ℝ => (ε : ℂ) * J (ε : ℂ)) (𝓝[>] 0) (𝓝 0)) (n : ℕ) :
    Tendsto (fun ε : ℝ => (ε : ℂ) * J ((ε : ℂ) + ((n + 1 : ℕ) : ℂ) * I)) (𝓝[>] 0)
      (𝓝 ((crystallineCoeff lam (n + 1) + 2 * weilResidue Φ) / (2 * Real.pi))) := by
  set a := crystallineCoeff lam with ha_def
  set β := weilResidue Φ with hβ
  have ha : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => ‖a (n + 1)‖ / ((n : ℝ) + 1) ^ σ :=
    fun σ hσ => summable_coeff_of_LSeriesSummable
      (lseriesSummable_crystallineCoeff hsl (by simpa using hσ))
  have hL : ∀ τ : ℂ, 0 < τ.re → GaloisForLFunctions.HTGeometry.hamburgerSeries a τ =
      (-1) * ∑' n : ℕ, a (n + 1) * cexp (-(2 * Real.pi * ((n : ℂ) + 1) * τ)) +
        β / (Real.pi * τ) + β + J τ := fun τ hτ =>
    GaloisForLFunctions.HTGeometry.hamburgerSeries_eq_of_coeffTheta_relation_defect a a ha ha
      (fun x hx => coeffTheta_weil_defect_relation hΦ hsl hid hx)
      (fun τ hτ => (hJ τ hτ).1) hJd (fun τ hτ => (hJ τ hτ).2) hτ
  have hper : ∀ τ : ℂ, 0 < τ.re → GaloisForLFunctions.HTGeometry.hamburgerSeries a (τ + I) -
      GaloisForLFunctions.HTGeometry.hamburgerSeries a τ =
        β / Real.pi / (τ + I) - β / Real.pi / τ + (J (τ + I) - J τ) := by
    intro τ hτ
    have hτ' : 0 < (τ + I).re := by simpa using hτ
    rw [hL τ hτ, hL (τ + I) hτ']
    have hexp : ∑' n : ℕ, a (n + 1) * cexp (-(2 * Real.pi * ((n : ℂ) + 1) * (τ + I))) =
        ∑' n : ℕ, a (n + 1) * cexp (-(2 * Real.pi * ((n : ℂ) + 1) * τ)) := by
      refine tsum_congr fun n => ?_
      rw [show -(2 * (Real.pi : ℂ) * ((n : ℂ) + 1) * (τ + I)) =
        -(2 * Real.pi * ((n : ℂ) + 1) * τ) + ((-((n : ℤ) + 1) : ℤ) : ℂ) * (2 * Real.pi * I) by
          push_cast; ring, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
    rw [hexp, div_div, div_div]
    ring
  have ha2 : Summable fun n : ℕ => ‖a (n + 1)‖ / ((n + 1 : ℕ) : ℝ) ^ 2 := by
    have := GaloisForLFunctions.HTGeometry.summable_sq_of_forall_rpow ha
    simpa using this
  -- radial limits of `ε K(ε + i n₀)`
  have hKrad : ∀ n₀ : ℕ, Tendsto (fun ε : ℝ => (ε : ℂ) *
      (J ((ε : ℂ) + (n₀ : ℂ) * I + I) - J ((ε : ℂ) + (n₀ : ℂ) * I))) (𝓝[>] 0)
      (𝓝 (if n₀ = 0 then a 1 / (2 * Real.pi) + β / Real.pi
        else (a (n₀ + 1) - a n₀) / (2 * Real.pi))) := by
    intro n₀
    have h := (tendsto_sub_mul_defect_residue ha2 (β / Real.pi) (fun τ => J (τ + I) - J τ)
      hper n₀).comp (tendsto_radial_ray n₀)
    refine h.congr' (Eventually.of_forall fun ε => ?_)
    simp only [Function.comp]
    ring_nf
  have hπ : (2 * (Real.pi : ℂ)) ≠ 0 := mul_ne_zero two_ne_zero (by exact_mod_cast Real.pi_ne_zero)
  induction n with
  | zero =>
    have h := (hKrad 0).add hJ0
    rw [if_pos rfl, add_zero] at h
    have e : a 1 / (2 * Real.pi) + β / Real.pi = (a (0 + 1) + 2 * β) / (2 * Real.pi) := by
      field_simp
    rw [e] at h
    refine h.congr' (Eventually.of_forall fun ε => ?_)
    simp only [Nat.cast_zero, zero_mul, add_zero]
    ring_nf
  | succ n ih =>
    have h := (hKrad (n + 1)).add ih
    rw [if_neg (Nat.succ_ne_zero n)] at h
    have e : (a (n + 1 + 1) - a (n + 1)) / (2 * Real.pi) +
        (a (n + 1) + 2 * β) / (2 * Real.pi) = (a (n + 1 + 1) + 2 * β) / (2 * Real.pi) := by
      field_simp; ring
    rw [e] at h
    refine h.congr' (Eventually.of_forall fun ε => ?_)
    push_cast
    ring_nf


section SpectralMeasureBohr

variable {X : Type*} [MeasurableSpace X] {ν : Measure X} {c t : X → ℝ}

/-- `ε J(ε) → 0` as `ε → 0⁺` for every spectral measure (no ζ-mass condition): on the real axis the
damping rate is `1`. -/
theorem tendsto_mul_spectralMeasureLaplace_zero (h : SpectralMeasureData ν c t) :
    Tendsto (fun ε : ℝ => (ε : ℂ) * spectralMeasureLaplace ν c t (ε : ℂ)) (𝓝[>] 0) (𝓝 0) := by
  have hpi := Real.pi_pos
  refine squeeze_zero_norm'
    (a := fun ε : ℝ => 3 / Real.pi * dampedZetaMassMeasure ν c t 1 * ε ^ (1 / 2 : ℝ)) ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    have hε' : 0 < ε := hε
    have hre : 0 < ((ε : ℂ)).re := by simpa using hε'
    have hb := norm_spectralMeasureLaplace_le h hre
    have hn : ‖(ε : ℂ)‖ = ε := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε']
    rw [hn, Complex.ofReal_re, div_self hε'.ne'] at hb
    rw [norm_mul, hn]
    have e : ε * ε ^ (-(1 / 2 : ℝ)) = ε ^ (1 / 2 : ℝ) := by
      rw [← Real.rpow_one_add' hε'.le (by norm_num)]; norm_num
    calc ε * ‖spectralMeasureLaplace ν c t ε‖
        ≤ ε * (3 / Real.pi * ε ^ (-(1 / 2 : ℝ)) * dampedZetaMassMeasure ν c t 1) := by gcongr
      _ = 3 / Real.pi * dampedZetaMassMeasure ν c t 1 * (ε * ε ^ (-(1 / 2 : ℝ))) := by ring
      _ = 3 / Real.pi * dampedZetaMassMeasure ν c t 1 * ε ^ (1 / 2 : ℝ) := by rw [e]
  · have h0 := (Real.continuousAt_rpow_const 0 (1 / 2) (Or.inr (by norm_num))).tendsto
    rw [Real.zero_rpow (by norm_num)] at h0
    simpa using (h0.mono_left nhdsWithin_le_nhds).const_mul
      (3 / Real.pi * dampedZetaMassMeasure ν c t 1)

/-- On the ray `ε + im` (`m ≥ 1`, `0 < ε < 1`),
`‖ε J(ε + im)‖ ≤ (3/π)(m + 1) · δ M(δ)` with `δ = ε/(m + 1)`. -/
theorem norm_mul_spectralMeasureLaplace_ray_le (h : SpectralMeasureData ν c t) {m : ℕ}
    (hm : 1 ≤ m) {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
    ‖(ε : ℂ) * spectralMeasureLaplace ν c t ((ε : ℂ) + (m : ℂ) * I)‖ ≤
      3 / Real.pi * ((m : ℝ) + 1) *
        (ε / ((m : ℝ) + 1) * dampedZetaMassMeasure ν c t (ε / ((m : ℝ) + 1))) := by
  have hpi := Real.pi_pos
  set κ : ℝ := (m : ℝ) + 1 with hκdef
  have hκ : 0 < κ := by positivity
  set τ : ℂ := (ε : ℂ) + (m : ℂ) * I with hτ
  have hre : τ.re = ε := by simp [hτ]
  have him : τ.im = m := by simp [hτ]
  have hτre : 0 < τ.re := by rw [hre]; exact hε
  have hb := norm_spectralMeasureLaplace_le h hτre
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hn1 : 1 ≤ ‖τ‖ := by
    have := Complex.abs_im_le_norm τ
    rw [him, abs_of_nonneg (by positivity)] at this
    linarith
  have hn2 : ‖τ‖ ≤ κ := by
    have h2 := norm_add_le (ε : ℂ) ((m : ℂ) * I)
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε, norm_mul, Complex.norm_natCast,
      Complex.norm_I, mul_one] at h2
    rw [hκdef]
    linarith
  have hpow : ‖τ‖ ^ (-(1 / 2 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hn1 (by norm_num)
  have hδ : ε / κ ≤ τ.re / ‖τ‖ := by
    rw [hre]; exact div_le_div_of_nonneg_left hε.le (by linarith) hn2
  have hmono := dampedZetaMassMeasure_antitone h (div_pos hε hκ) hδ
  have hM0 : 0 ≤ dampedZetaMassMeasure ν c t (τ.re / ‖τ‖) :=
    integral_nonneg (fun y => by positivity)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε]
  calc ε * ‖spectralMeasureLaplace ν c t τ‖
      ≤ ε * (3 / Real.pi * ‖τ‖ ^ (-(1 / 2 : ℝ)) * dampedZetaMassMeasure ν c t (τ.re / ‖τ‖)) := by
        gcongr
    _ ≤ ε * (3 / Real.pi * 1 * dampedZetaMassMeasure ν c t (ε / κ)) := by gcongr
    _ = 3 / Real.pi * κ * (ε / κ * dampedZetaMassMeasure ν c t (ε / κ)) := by field_simp

/-- **The Bohr–ζ law for spectral measures.**  For every `n ≥ 1`,
`(1 ⋆ (lam − Λ))(n) + 2β = 2π · lim_{ε→0⁺} ε J(ε + in)`, with no ζ-mass hypothesis. -/
theorem tendsto_mul_spectralMeasureLaplace_bohr [SFinite ν] {lam : ℕ → ℝ}
    (h : SpectralMeasureData ν c t)
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    (hid : ∀ s : ℂ, 1 < s.re → zetaArchimedeanDatum s + 1 / (s - 1) -
      LSeries (fun n => (lam n : ℂ)) s = spectralMeasureSeries ν c t s) (n : ℕ) :
    Tendsto (fun ε : ℝ => (ε : ℂ) * spectralMeasureLaplace ν c t ((ε : ℂ) + ((n + 1 : ℕ) : ℂ) * I))
      (𝓝[>] 0) (𝓝 ((crystallineCoeff lam (n + 1) +
        2 * weilResidue (spectralMeasureSeries ν c t)) / (2 * Real.pi))) := by
  refine tendsto_mul_weilLaplace_bohr h.oddWeilFunction hsl hid
    (differentiableOn_spectralMeasureLaplace h) (fun τ hτ => ?_)
    (tendsto_mul_spectralMeasureLaplace_zero h) n
  have hK : (fun x : ℝ => weilDefect (spectralMeasureSeries ν c t) x *
      ((Real.exp (-(Real.pi * τ ^ 2) * x) : ℝ) : ℂ)) =ᶠ[ae (volume.restrict (Ioi 0))]
      fun x : ℝ => spectralMeasureDefect ν c t x * ((Real.exp (-(Real.pi * τ ^ 2) * x) : ℝ) : ℂ) := by
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun x hx => ?_)
    dsimp only
    rw [weilDefect_spectralMeasureSeries h hx]
  obtain ⟨hint, hJ⟩ := spectralMeasureDefect_laplace h hτ
  refine ⟨hint.congr_fun_ae hK.symm, ?_⟩
  rw [hJ, integral_congr_ae hK]

/-- **The ζ-mass deficit law.**  If the damped ζ-mass satisfies `δ M(δ) ≤ A` for all small `δ > 0`,
then `‖(1 ⋆ (lam − Λ))(n) + 2β‖ ≤ 6(n + 1) A` for every `n ≥ 1`.  The arithmetic deviation of `lam`
from `Λ` is bounded by the ζ-weighted spectral mass density. -/
theorem norm_crystallineCoeff_add_le_of_dampedZetaMass [SFinite ν] {lam : ℕ → ℝ}
    (h : SpectralMeasureData ν c t)
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    (hid : ∀ s : ℂ, 1 < s.re → zetaArchimedeanDatum s + 1 / (s - 1) -
      LSeries (fun n => (lam n : ℂ)) s = spectralMeasureSeries ν c t s) {A : ℝ}
    (hA : ∀ᶠ δ in 𝓝[>] (0 : ℝ), δ * dampedZetaMassMeasure ν c t δ ≤ A) (n : ℕ) :
    ‖crystallineCoeff lam (n + 1) + 2 * weilResidue (spectralMeasureSeries ν c t)‖ ≤
      6 * ((n : ℝ) + 2) * A := by
  have hpi := Real.pi_pos
  set κ : ℝ := ((n + 1 : ℕ) : ℝ) + 1 with hκdef
  have hκ : 0 < κ := by positivity
  have hlim := (tendsto_mul_spectralMeasureLaplace_bohr h hsl hid n).norm
  have hmap : Tendsto (fun ε : ℝ => ε / κ) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have := (continuous_id.div_const κ).tendsto (0 : ℝ)
      simpa using this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      exact div_pos hε hκ
  have hbound : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), ‖(ε : ℂ) *
      spectralMeasureLaplace ν c t ((ε : ℂ) + ((n + 1 : ℕ) : ℂ) * I)‖ ≤ 3 / Real.pi * κ * A := by
    filter_upwards [self_mem_nhdsWithin, Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1),
      hmap.eventually hA] with ε hε hε1 hAε
    have hr := norm_mul_spectralMeasureLaplace_ray_le h (m := n + 1) (by omega) hε hε1.2
    refine hr.trans ?_
    rw [← hκdef]
    gcongr
  have hle := le_of_tendsto hlim hbound
  have hn : ‖(crystallineCoeff lam (n + 1) + 2 * weilResidue (spectralMeasureSeries ν c t)) /
      (2 * (Real.pi : ℂ))‖ = ‖crystallineCoeff lam (n + 1) +
        2 * weilResidue (spectralMeasureSeries ν c t)‖ / (2 * Real.pi) := by
    rw [norm_div, norm_mul, Complex.norm_two, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hpi]
  rw [hn, div_le_iff₀ (by positivity)] at hle
  have hκ' : κ = (n : ℝ) + 2 := by rw [hκdef]; push_cast; ring
  rw [hκ'] at hle
  have e : 3 / Real.pi * ((n : ℝ) + 2) * A * (2 * Real.pi) = 6 * ((n : ℝ) + 2) * A := by
    field_simp; ring
  linarith [e]

/-- **Prime weights are controlled by the ζ-mass density.**  If `δ M(δ) ≤ A` for all small `δ > 0`,
then `|lam(p) − log p| ≤ 6(p + 3) A` for every prime `p`. -/
theorem abs_sub_vonMangoldt_le_of_dampedZetaMass [SFinite ν] {lam : ℕ → ℝ}
    (h : SpectralMeasureData ν c t)
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    (hid : ∀ s : ℂ, 1 < s.re → zetaArchimedeanDatum s + 1 / (s - 1) -
      LSeries (fun n => (lam n : ℂ)) s = spectralMeasureSeries ν c t s) {A : ℝ}
    (hA : ∀ᶠ δ in 𝓝[>] (0 : ℝ), δ * dampedZetaMassMeasure ν c t δ ≤ A) {p : ℕ}
    (hp : p.Prime) :
    |lam p - ArithmeticFunction.vonMangoldt p| ≤ 6 * ((p : ℝ) + 3) * A := by
  set β := weilResidue (spectralMeasureSeries ν c t)
  have hp1 : 1 ≤ p := hp.one_lt.le
  have h1 := norm_crystallineCoeff_add_le_of_dampedZetaMass h hsl hid hA 0
  have h2 := norm_crystallineCoeff_add_le_of_dampedZetaMass h hsl hid hA (p - 1)
  have hsub : p - 1 + 1 = p := Nat.sub_add_cancel hp1
  rw [hsub] at h2
  have hcast : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by rw [Nat.cast_sub hp1]; simp
  rw [hcast] at h2
  -- `1 ⋆ w` at `1` and at `p`
  have hc1 : crystallineCoeff lam (0 + 1) = ((lam 1 : ℝ) : ℂ) -
      ((ArithmeticFunction.vonMangoldt 1 : ℝ) : ℂ) := by
    rw [crystallineCoeff, LSeries.convolution_def]
    dsimp only
    rw [Nat.sum_divisorsAntidiagonal (fun i j => (1 : ℕ → ℂ) i *
      (((fun n => (lam n : ℂ)) - fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) j)),
      Nat.divisors_one, Finset.sum_singleton]
    simp
  have hcp : crystallineCoeff lam p = (((lam 1 : ℝ) : ℂ) -
      ((ArithmeticFunction.vonMangoldt 1 : ℝ) : ℂ)) +
      (((lam p : ℝ) : ℂ) - ((ArithmeticFunction.vonMangoldt p : ℝ) : ℂ)) := by
    rw [crystallineCoeff, LSeries.convolution_def]
    dsimp only
    rw [Nat.sum_divisorsAntidiagonal (fun i j => (1 : ℕ → ℂ) i *
      (((fun n => (lam n : ℂ)) - fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) j)),
      hp.divisors, Finset.sum_pair (Ne.symm hp.one_lt.ne'), Nat.div_one, Nat.div_self hp.pos]
    simp only [Pi.one_apply, Pi.sub_apply, one_mul, ArithmeticFunction.vonMangoldt_apply_one,
      Complex.ofReal_zero, sub_zero]
    ring
  have hdiff : crystallineCoeff lam p - crystallineCoeff lam (0 + 1) =
      (((lam p - ArithmeticFunction.vonMangoldt p : ℝ)) : ℂ) := by
    rw [hcp, hc1]; push_cast; ring
  have htri : ‖crystallineCoeff lam p - crystallineCoeff lam (0 + 1)‖ ≤
      ‖crystallineCoeff lam p + 2 * β‖ + ‖crystallineCoeff lam (0 + 1) + 2 * β‖ := by
    have := norm_sub_le (crystallineCoeff lam p + 2 * β) (crystallineCoeff lam (0 + 1) + 2 * β)
    rwa [show crystallineCoeff lam p + 2 * β - (crystallineCoeff lam (0 + 1) + 2 * β) =
      crystallineCoeff lam p - crystallineCoeff lam (0 + 1) by ring] at this
  rw [hdiff, Complex.norm_real, Real.norm_eq_abs] at htri
  simp only [Nat.cast_zero, zero_add] at h1
  linarith

end SpectralMeasureBohr

end RHTower
