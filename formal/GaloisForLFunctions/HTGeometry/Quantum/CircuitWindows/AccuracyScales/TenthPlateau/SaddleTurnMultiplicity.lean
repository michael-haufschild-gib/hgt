import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.AccuracyScales.TenthPlateau.EnvelopeTransversality
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.AccuracyScales.TenthPlateau.ReturnExcisedVandermonde

/-! # Active-saddle switching proliferation vs. micro-band sign-coherent coercivity at 1/10

This module resolves the competition between active `(θ_⋆, W_⋆)` saddle switching and turn
multiplicity along `1`D disorder lines at `e = 1 / 10` and scale `δ = 2^{-Θ(N²)}`:

1. **Micro-band sign-coherent single-crossing law and fixed-`1/10` locking (`M = 1` per collar):**
   - `levelBand_dini_diam_le`: if `g` is continuous on a convex set `I ⊆ ℝ` and satisfies right
     Dini coercivity `≥ c > 0` **solely** on the open `η_pad`-padded band
     `g⁻¹(a_band - η_pad, b_band + η_pad)` (`0 < η_pad`, `a_band ≤ b_band`), then
     `I ∩ g⁻¹[a_band, b_band]` has diameter `≤ (b_band - a_band) / c` regardless of arbitrarily
     many sign-coherent branch switches inside the band and arbitrarily many oscillations outside.
   - `gaussian_levelBand_dini_anticoncentration` and `fixed_tenth_locking_of_levelBand_dini`:
     product-Gaussian anti-concentration `≤ M * δ / (√(2 π) * c)` and fixed-`e = 1 / 10` zero-drop
     locking requiring sign-coherent right Dini coercivity only inside
     `Ioo (1 / 10 - η_pad) (1 / 10 + δ + η_pad)`. Even super-polynomially many (`M = 2^{O(N)}`)
     sign-coherent collar segments lock `m_{1/10 + δ} = m_{1/10}` at `δ = 2^{-b N²}`.
2. **Zero-curvature max-min sawtooth oscillation obstruction at scale `K = 2^{Θ(N²)}`:**
   - `deriv_deriv_sawtoothBranches_zero` and `maxMinSawtooth_gaussian_violation`: an explicit
     `(K + 1) × 2` max-min envelope of **purely affine** (`f'' ≡ 0`) branches with slope `±c` is
     `c`-Lipschitz, crosses `(e₀, e₀ + δ]` strictly `2 * (K + 1)` times inside
     `[0, 4 * (K + 1) * δ / c]`, and when `4 * (K + 1) * δ / c ≤ 1` carries product-Gaussian mass
     `≥ (3 / 2) * gaussianDensityFloor * ((K + 1) * δ / c)`, proving that bipolar max-min saddle
     switching at `K = 2^{Θ(N²)}` is a genuine curvature-free obstruction at `δ = 2^{-Θ(N²)}`.
3. **Kato spectral-gap connection norm and mode-slope Lipschitz stability:**
   - `katoOffDiagGenerator_commutator_eq`, `norm_katoOffDiagGenerator_le`, and
     `transverse_mode_slope_lipschitz`: for simple-spectrum `H` with minimum gap `Δ_min > 0`, the
     off-diagonal Kato generator `K` solving `i [K, H] = P - diag_H(P)` satisfies
     `‖K‖ ≤ 2^(N / 2) * ‖P‖ / Δ_min`, and along `e^{-i u K}` every unit-vector expectation shift
     `Φ(u) = Re ⟨U(u) ψ, K U(u) ψ⟩ - Re ⟨ψ, K ψ⟩` is `2 ‖K‖²`-Lipschitz in `u`.
4. **Super-polynomial (`2^(N - 1)`) active-saddle switches and sign reversals on `H₀ + t Z₀`:**
   - `pauliPencil_exponential_saddle_switches`: along the physical single-site Pauli perturbation
     pencil `H(t) = H₀ + t Z₀` (`N ≥ 2`), an explicit self-adjoint base `H₀` has strictly simple
     spectrum on `[0, 4 * 2^(N - 1)]` with smooth eigenframe `V(t)` and Kato generator `K(t)`
     driving `2^(N - 1)` active `(θ_m, W_{m, ±})` saddle switches, `2^N` exact `1 / 10` crossings
     of the global spectral-torus envelope `G(t)`, and `2^(N - 1)` strict sign reversals of the
     unitary-ratio expectation shift `Re ⟨U_⋆ ψ, K(t) U_⋆ ψ⟩ - Re ⟨ψ, K(t) ψ⟩` at `r_⋆ = 1 / 10`,
     refuting any `poly(N)` turn bound along `1`D Pauli disorder lines. -/

open Set Filter MeasureTheory ProbabilityTheory Real Topology Matrix
open scoped Matrix.Norms.L2Operator ENNReal ComplexConjugate
namespace GaloisForLFunctions.HTGeometry.AccuracyScales.TenthPlateau
open SharpOccupation SharpOccupation.FiniteRecords MaximumIntervals
noncomputable section

private abbrev Config (N : ℕ) := Fin N → Bool
private abbrev UGroup (N : ℕ) := Matrix.unitaryGroup (Config N) ℂ
private abbrev StateSpace (N : ℕ) := EuclideanSpace ℂ (Config N)

private theorem matAct_eq_clm {N : ℕ} (A : Register N) (ψ : StateSpace N) :
    matAct A ψ = Matrix.toEuclideanCLM (n := Config N) (𝕜 := ℂ) A ψ :=
  WithLp.ofLp_injective 2 (Matrix.ofLp_toEuclideanCLM A ψ).symm

private theorem matAct_sub_left {N : ℕ} (A B : Register N) (ψ : StateSpace N) :
    matAct (A - B) ψ = matAct A ψ - matAct B ψ := by
  ext i; simp [matAct, Matrix.sub_mulVec]

private theorem matAct_map_sub' {N : ℕ} (A : Register N) (x y : StateSpace N) :
    matAct A (x - y) = matAct A x - matAct A y := by
  ext i; simp [matAct, Matrix.mulVec_sub]

private theorem matAct_mul' {N : ℕ} (A B : Register N) (ψ : StateSpace N) :
    matAct (A * B) ψ = matAct A (matAct B ψ) := by
  ext i; simp [matAct, Matrix.mulVec_mulVec]

private theorem inner_matAct_star_left' {N : ℕ} (A : Register N) (x y : StateSpace N) :
    inner ℂ (matAct (star A) x) y = inner ℂ x (matAct A y) := by
  rw [matAct_eq_clm, matAct_eq_clm,
    show Matrix.toEuclideanCLM (n := Config N) (𝕜 := ℂ) (star A) =
      ContinuousLinearMap.adjoint (Matrix.toEuclideanCLM (n := Config N) (𝕜 := ℂ) A) from
      map_star Matrix.toEuclideanCLM A,
    ContinuousLinearMap.adjoint_inner_left]

private theorem norm_matAct_le' {N : ℕ} (A : Register N) (ψ : StateSpace N) :
    ‖matAct A ψ‖ ≤ ‖A‖ * ‖ψ‖ := by
  rw [matAct_eq_clm]
  simpa only [Matrix.l2_opNorm_toEuclideanCLM] using
    (Matrix.toEuclideanCLM (n := Config N) (𝕜 := ℂ) A).le_opNorm ψ

private theorem opNorm_le_of_matAct_le' {N : ℕ} {A : Register N} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ x : StateSpace N, ‖matAct A x‖ ≤ C * ‖x‖) : ‖A‖ ≤ C := by
  rw [← Matrix.l2_opNorm_toEuclideanCLM (n := Config N) (𝕜 := ℂ)]
  refine (Matrix.toEuclideanCLM (n := Config N) (𝕜 := ℂ) A).opNorm_le_bound hC fun x => ?_
  rw [← matAct_eq_clm]
  exact h x

private theorem inner_self_complex' {N : ℕ} (x : StateSpace N) :
    inner ℂ x x = ((‖x‖ ^ 2 : ℝ) : ℂ) := by
  rw [inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow]
  rfl

private theorem norm_matAct_unitary' {N : ℕ} {U : Register N} (hU : U ∈ unitary (Register N))
    (ψ : StateSpace N) : ‖matAct U ψ‖ = ‖ψ‖ := by
  have h1 : inner ℂ (matAct U ψ) (matAct U ψ) = inner ℂ ψ ψ := by
    rw [← inner_matAct_star_left', ← matAct_mul', (Unitary.mem_iff.mp hU).1]
    have hone : matAct 1 ψ = ψ := by ext i; simp [matAct]
    rw [hone]
  rw [inner_self_complex', inner_self_complex'] at h1
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (Complex.ofReal_injective h1)

private theorem projectiveSpectralMatrix_mem_unitary' {N d : ℕ} (e : Config N ≃ Fin (d + 1))
    (V : UGroup N) (θ : Fin d → UnitAddCircle) :
    projectiveSpectralMatrix e V θ ∈ unitary (Register N) := by
  unfold projectiveSpectralMatrix
  refine mul_mem (mul_mem V.2 ?_) (Unitary.star_mem V.2)
  rw [Unitary.mem_iff, star_eq_conjTranspose, diagonal_conjTranspose,
    diagonal_mul_diagonal, diagonal_mul_diagonal]
  constructor <;> ext a b <;> by_cases hab : a = b
  · subst hab; simp only [diagonal_apply_eq, one_apply_eq]
    exact Complex.normSq_eq_conj_mul_self.symm.trans (by simp)
  · simp [hab]
  · subst hab; simp only [diagonal_apply_eq, one_apply_eq]; rw [mul_comm]
    exact Complex.normSq_eq_conj_mul_self.symm.trans (by simp)
  · simp [hab]

/-! ## Section 1: Micro-band sign-coherent single-crossing law and fixed-`1/10` locking -/

/-- Micro-band sign-coherent single-crossing theorem: if `g` is continuous on a convex set `I ⊆ ℝ`
and has right Dini slope `≥ c > 0` **solely** at points `t ∈ I` where
`g t ∈ Ioo (a_band - η_pad) (b_band + η_pad)` (`a_band ≤ b_band`, `0 < η_pad`), then any two
visits `t₁ ≤ t₂` in `I` to `[a_band, b_band]` satisfy `t₂ - t₁ ≤ (b_band - a_band) / c`,
regardless of arbitrarily many branch switches inside the band or oscillations outside it. -/
theorem levelBand_dini_diam_le {I : Set ℝ} (hI : Convex ℝ I)
    {g : ℝ → ℝ} (hg : ContinuousOn g I)
    {c a_band b_band η_pad : ℝ} (hc : 0 < c) (hab_band : a_band ≤ b_band) (hη_pad : 0 < η_pad)
    (hdini : ∀ t ∈ I, g t ∈ Ioo (a_band - η_pad) (b_band + η_pad) →
      ∀ b ∈ I, t < b → ∀ ε > 0, ∃ h ∈ Ioc (0 : ℝ) (b - t), (c - ε) * h ≤ g (t + h) - g t)
    {t₁ t₂ : ℝ} (ht₁ : t₁ ∈ I) (ht₂ : t₂ ∈ I) (h12 : t₁ ≤ t₂)
    (hg₁ : g t₁ ∈ Icc a_band b_band) (hg₂ : g t₂ ∈ Icc a_band b_band) :
    t₂ - t₁ ≤ (b_band - a_band) / c := by
  rcases eq_or_lt_of_le h12 with rfl | hlt
  · rw [sub_self]; exact div_nonneg (sub_nonneg.mpr hab_band) hc.le
  have hsub_I : Icc t₁ t₂ ⊆ I := hI.ordConnected.out ht₁ ht₂
  have hg_Icc : ContinuousOn g (Icc t₁ t₂) := hg.mono hsub_I
  let g_ext : ℝ → ℝ := fun s => g (max t₁ (min t₂ s))
  have hg_ext_cont : Continuous g_ext :=
    hg_Icc.comp_continuous (continuous_const.max (continuous_const.min continuous_id))
      fun s => ⟨le_max_left _ _, max_le hlt.le (min_le_left _ _)⟩
  have hg_ext_eq {s : ℝ} (hs : s ∈ Icc t₁ t₂) : g_ext s = g s := by
    dsimp only [g_ext]; rw [min_eq_right hs.2, max_eq_right hs.1]
  have hno_down : ∀ {u₀ u₁ v : ℝ}, t₁ ≤ u₀ → u₀ ≤ u₁ → u₁ ≤ t₂ →
      v ∈ Ioo (a_band - η_pad) (b_band + η_pad) → v ≤ g_ext u₀ → g_ext u₁ < v → False := by
    intro u₀ u₁ v hu₀ hu₀₁ hu₁ hv_mem hv_lo hv_hi
    let A : Set ℝ := Icc u₀ u₁ ∩ {s | v ≤ g_ext s}
    have hA_closed : IsClosed A :=
      isClosed_Icc.inter (isClosed_le continuous_const hg_ext_cont)
    have hA_bdd : BddAbove A := bddAbove_Icc.mono inter_subset_left
    have hA_ne : A.Nonempty := ⟨u₀, ⟨le_rfl, hu₀₁⟩, hv_lo⟩
    let τ := sSup A
    have hτ_mem : τ ∈ A := hA_closed.csSup_mem hA_ne hA_bdd
    have hτ_lt : τ < u₁ := by
      refine lt_of_le_of_ne hτ_mem.1.2 ?_
      intro heq
      rw [heq] at hτ_mem
      exact hv_hi.not_ge hτ_mem.2
    have hgt_after {s : ℝ} (hs : s ∈ Ioc τ u₁) : g_ext s < v := by
      by_contra hge; push Not at hge
      have hs_mem : s ∈ A := ⟨⟨hτ_mem.1.1.trans hs.1.le, hs.2⟩, hge⟩
      exact hs.1.not_ge (le_csSup hA_bdd hs_mem)
    have hτ_eq_v : g_ext τ = v := by
      refine le_antisymm ?_ hτ_mem.2
      let seq : ℕ → ℝ := fun n => min u₁ (τ + 1 / ((n : ℝ) + 1))
      have hseq_tend : Tendsto seq atTop (𝓝 τ) := by
        have h1 : Tendsto (fun n : ℕ => τ + 1 / ((n : ℝ) + 1)) atTop (𝓝 (τ + 0)) :=
          tendsto_const_nhds.add tendsto_one_div_add_atTop_nhds_zero_nat
        rw [add_zero] at h1
        have hmin := (tendsto_const_nhds (x := u₁)).min h1
        rwa [min_eq_right hτ_lt.le] at hmin
      have hval_tend : Tendsto (g_ext ∘ seq) atTop (𝓝 (g_ext τ)) :=
        (hg_ext_cont.tendsto τ).comp hseq_tend
      refine le_of_tendsto' hval_tend fun n => ?_
      have hpos_n : 0 < 1 / ((n : ℝ) + 1) := by positivity
      have hseq_mem : seq n ∈ Ioc τ u₁ :=
        ⟨lt_min hτ_lt (by linarith only [hpos_n]), min_le_left _ _⟩
      exact (hgt_after hseq_mem).le
    have hlow_nhds : ∀ᶠ s in 𝓝 τ, a_band - η_pad < g_ext s :=
      (hg_ext_cont.tendsto τ).eventually (Ioi_mem_nhds (hτ_eq_v.symm ▸ hv_mem.1))
    obtain ⟨r, hr_pos, hr_ball⟩ := Metric.eventually_nhds_iff.mp hlow_nhds
    let s_star := min u₁ (τ + r / 2)
    have hτ_lt_star : τ < s_star := lt_min hτ_lt (by linarith only [hr_pos])
    have hstar_le_u₁ : s_star ≤ u₁ := min_le_left _ _
    have hτ_Icc : Icc τ s_star ⊆ Icc t₁ t₂ := fun s hs =>
      ⟨hu₀.trans (hτ_mem.1.1.trans hs.1), hs.2.trans (hstar_le_u₁.trans hu₁)⟩
    have hband_sub : ∀ s ∈ Icc τ s_star, g s ∈ Ioo (a_band - η_pad) (b_band + η_pad) := by
      intro s hs
      rw [← hg_ext_eq (hτ_Icc hs)]
      have hdist : dist s τ < r := by
        rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hs.1)]
        have hle_half : s ≤ τ + r / 2 := hs.2.trans (min_le_right _ _)
        linarith only [hle_half, hr_pos]
      refine ⟨hr_ball hdist, ?_⟩
      rcases eq_or_lt_of_le hs.1 with rfl | hgt_τ
      · rw [hτ_eq_v]; exact hv_mem.2
      · exact (hgt_after ⟨hgt_τ, hs.2.trans hstar_le_u₁⟩).trans hv_mem.2
    have hstep_dini : ∀ s ∈ Ico τ s_star, ∀ ε > 0,
        ∃ h ∈ Ioc (0 : ℝ) (s_star - s), (c - ε) * h ≤ g (s + h) - g s := by
      intro s hs ε hε
      exact hdini s (hsub_I (hτ_Icc ⟨hs.1, hs.2.le⟩))
        (hband_sub s ⟨hs.1, hs.2.le⟩) s_star (hsub_I (hτ_Icc ⟨hτ_lt_star.le, le_rfl⟩)) hs.2 ε hε
    have hgrowth := dini_mul_sub_le_sub hτ_lt_star.le (hg_Icc.mono hτ_Icc) hstep_dini
    have hgs_lt : g s_star < g τ := by
      rw [← hg_ext_eq (hτ_Icc ⟨hτ_lt_star.le, le_rfl⟩), ← hg_ext_eq (hτ_Icc ⟨le_rfl, hτ_lt_star.le⟩),
        hτ_eq_v]
      exact hgt_after ⟨hτ_lt_star, hstar_le_u₁⟩
    nlinarith only [hc, hτ_lt_star, hgrowth, hgs_lt]
  let v_hi := b_band + η_pad / 2
  have hall_lt_hi : ∀ s ∈ Icc t₁ t₂, g s < v_hi := by
    intro s hs
    by_contra hge; push Not at hge
    exact hno_down (v := v_hi) hs.1 hs.2 le_rfl
      ⟨by dsimp [v_hi]; linarith only [hab_band, hη_pad], by dsimp [v_hi]; linarith only [hη_pad]⟩
      (by rw [hg_ext_eq hs]; exact hge)
      (by rw [hg_ext_eq ⟨hlt.le, le_rfl⟩]; dsimp [v_hi]; linarith only [hg₂.2, hη_pad])
  have hall_ge_lo : ∀ s ∈ Icc t₁ t₂, a_band ≤ g s := by
    intro s hs
    by_contra hlt_a; push Not at hlt_a
    exact hno_down (v := a_band) le_rfl hs.1 hs.2
      ⟨by linarith only [hη_pad], by linarith only [hab_band, hη_pad]⟩
      (by rw [hg_ext_eq ⟨le_rfl, hlt.le⟩]; exact hg₁.1)
      (by rw [hg_ext_eq hs]; exact hlt_a)
  have hall_band : ∀ s ∈ Icc t₁ t₂, g s ∈ Ioo (a_band - η_pad) (b_band + η_pad) := fun s hs =>
    ⟨by linarith only [hall_ge_lo s hs, hη_pad],
     (hall_lt_hi s hs).trans (by dsimp [v_hi]; linarith only [hη_pad])⟩
  have hfull_dini : ∀ s ∈ Ico t₁ t₂, ∀ ε > 0,
      ∃ h ∈ Ioc (0 : ℝ) (t₂ - s), (c - ε) * h ≤ g (s + h) - g s := fun s hs ε hε =>
    hdini s (hsub_I ⟨hs.1, hs.2.le⟩) (hall_band s ⟨hs.1, hs.2.le⟩) t₂ ht₂ hs.2 ε hε
  have hgrowth := dini_mul_sub_le_sub hlt.le hg_Icc hfull_dini
  exact (le_div_iff₀ hc).mpr (by rw [mul_comm]; linarith only [hgrowth, hg₁.1, hg₂.2])

private theorem gaussianReal_le_density_vol (S : Set ℝ) :
    (gaussianReal 0 1) S ≤ ENNReal.ofReal ((Real.sqrt (2 * Real.pi))⁻¹) * volume S := by
  rw [gaussianReal_apply 0 (by norm_num) S, ← setLIntegral_const]
  refine setLIntegral_mono_ae (by fun_prop) ?_
  filter_upwards with t _
  rw [gaussianPDF]
  apply ENNReal.ofReal_le_ofReal
  rw [gaussianPDFReal_def]
  simp only [NNReal.coe_one, mul_one, sub_zero]
  exact mul_le_of_le_one_right (by positivity)
    (Real.exp_le_one_iff.mpr (by nlinarith only [sq_nonneg t]))

/-- Product-Gaussian micro-band anti-concentration: if each coordinate-`i₀` fiber of `Ω` is covered
by `M` convex pieces on each of which `±F` is continuous and has right Dini slope `≥ c > 0`
**solely** at points where `F ∈ Ioo (e₀ - η_pad) (e₀ + δ + η_pad)` (`0 < η_pad`), then
`ℙ(x ∈ Ω ∧ F x ∈ Ioc e₀ (e₀ + δ)) ≤ M * δ / (√(2 π) * c)`. -/
theorem gaussian_levelBand_dini_anticoncentration {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i₀ : ι) {F : (ι → ℝ) → ℝ} (hF : Measurable F)
    {Ω : Set (ι → ℝ)} (hΩ : MeasurableSet Ω)
    (M : ℕ) {c e₀ δ η_pad : ℝ} (hc : 0 < c) (hδ : 0 ≤ δ) (hη_pad : 0 < η_pad)
    (hfib : ∀ y : ι → ℝ, ∃ (I_piece : Fin M → Set ℝ) (sgn : Fin M → Bool),
      {t : ℝ | Function.update y i₀ t ∈ Ω} ⊆ ⋃ m : Fin M, I_piece m ∧
      ∀ m : Fin M, Convex ℝ (I_piece m) ∧
        ContinuousOn (fun t => F (Function.update y i₀ t)) (I_piece m) ∧
        ∀ t₁ ∈ I_piece m,
          F (Function.update y i₀ t₁) ∈ Ioo (e₀ - η_pad) (e₀ + δ + η_pad) →
          ∀ t₂ ∈ I_piece m, t₁ < t₂ → ∀ ε > 0,
            ∃ h ∈ Ioc (0 : ℝ) (t₂ - t₁),
              (c - ε) * h ≤
                (if sgn m then 1 else -1) *
                  (F (Function.update y i₀ (t₁ + h)) - F (Function.update y i₀ t₁))) :
    (Measure.pi fun _ : ι => gaussianReal 0 1).real
      {x ∈ Ω | F x ∈ Ioc e₀ (e₀ + δ)} ≤
      (M : ℝ) * δ / (Real.sqrt (2 * Real.pi) * c) := by
  let γ_pi := Measure.pi fun _ : ι => gaussianReal 0 1
  let E : Set (ι → ℝ) := {x | x ∈ Ω ∧ F x ∈ Ioc e₀ (e₀ + δ)}
  have hE_meas : MeasurableSet E := hΩ.inter (hF measurableSet_Ioc)
  have h1d (y : ι → ℝ) :
      (gaussianReal 0 1) {t : ℝ | Function.update y i₀ t ∈ E} ≤
        ENNReal.ofReal ((M : ℝ) * δ / (Real.sqrt (2 * Real.pi) * c)) := by
    obtain ⟨I_piece, sgn, hcov, hpiece⟩ := hfib y
    let g : ℝ → ℝ := fun t => F (Function.update y i₀ t)
    have hpiece_box (m : Fin M) : ∃ a_m : ℝ,
        I_piece m ∩ {t | g t ∈ Ioc e₀ (e₀ + δ)} ⊆ Icc a_m (a_m + δ / c) := by
      let A_m := I_piece m ∩ {t | g t ∈ Ioc e₀ (e₀ + δ)}
      by_cases hA_emp : A_m = ∅
      · refine ⟨0, ?_⟩
        change A_m ⊆ _; rw [hA_emp]; exact empty_subset _
      · obtain ⟨t₀, ht₀⟩ := nonempty_iff_ne_empty.mpr hA_emp
        obtain ⟨hconv, hcont, hdini_m⟩ := hpiece m
        have hdiam : ∀ t₁ ∈ A_m, ∀ t₂ ∈ A_m, t₁ ≤ t₂ → t₂ - t₁ ≤ δ / c := by
          intro t₁ ht₁ t₂ ht₂ h12
          by_cases hsgn : sgn m = true
          · have hdini_pos : ∀ t ∈ I_piece m, g t ∈ Ioo (e₀ - η_pad) ((e₀ + δ) + η_pad) →
                ∀ b ∈ I_piece m, t < b → ∀ ε > 0,
                  ∃ h ∈ Ioc (0 : ℝ) (b - t), (c - ε) * h ≤ g (t + h) - g t := by
              intro t ht hgt b hb htb ε hε
              obtain ⟨h, hh_mem, hh_step⟩ := hdini_m t ht hgt b hb htb ε hε
              rw [if_pos hsgn, one_mul] at hh_step
              exact ⟨h, hh_mem, hh_step⟩
            have hbound := levelBand_dini_diam_le hconv hcont hc (by linarith only [hδ]) hη_pad
              hdini_pos ht₁.1 ht₂.1 h12 ⟨ht₁.2.1.le, ht₁.2.2⟩ ⟨ht₂.2.1.le, ht₂.2.2⟩
            simpa only [add_sub_cancel_left] using hbound
          · let g_neg : ℝ → ℝ := fun t => -g t
            have hcont_neg : ContinuousOn g_neg (I_piece m) := hcont.neg
            have hdini_neg : ∀ t ∈ I_piece m,
                g_neg t ∈ Ioo (-(e₀ + δ) - η_pad) (-e₀ + η_pad) →
                ∀ b ∈ I_piece m, t < b → ∀ ε > 0,
                  ∃ h ∈ Ioc (0 : ℝ) (b - t), (c - ε) * h ≤ g_neg (t + h) - g_neg t := by
              intro t ht hgt b hb htb ε hε
              have hgt_orig : g t ∈ Ioo (e₀ - η_pad) (e₀ + δ + η_pad) :=
                ⟨by dsimp [g_neg] at hgt; linarith only [hgt.2],
                 by dsimp [g_neg] at hgt; linarith only [hgt.1]⟩
              obtain ⟨h, hh_mem, hh_step⟩ := hdini_m t ht hgt_orig b hb htb ε hε
              rw [if_neg hsgn] at hh_step
              exact ⟨h, hh_mem, by dsimp [g_neg]; linarith only [hh_step]⟩
            have hbound := levelBand_dini_diam_le hconv hcont_neg hc (by linarith only [hδ]) hη_pad
              hdini_neg ht₁.1 ht₂.1 h12
              ⟨by dsimp [g_neg]; linarith only [ht₁.2.2], by dsimp [g_neg]; linarith only [ht₁.2.1]⟩
              ⟨by dsimp [g_neg]; linarith only [ht₂.2.2], by dsimp [g_neg]; linarith only [ht₂.2.1]⟩
            have hlen : -e₀ - -(e₀ + δ) = δ := by ring
            rwa [hlen] at hbound
        have hA_bddBelow : BddBelow A_m := ⟨t₀ - δ / c, fun t ht => by
          rcases le_total t t₀ with hle | hge
          · linarith only [hdiam t ht t₀ ht₀ hle]
          · linarith only [hge, div_nonneg hδ hc.le]⟩
        let a_m := sInf A_m
        refine ⟨a_m, fun t ht => ⟨csInf_le hA_bddBelow ht, ?_⟩⟩
        have hlb : t - δ / c ≤ a_m := le_csInf ⟨t₀, ht₀⟩ fun u hu => by
          rcases le_total u t with hut | htu
          · linarith only [hdiam u hu t ht hut]
          · linarith only [htu, div_nonneg hδ hc.le]
        linarith only [hlb]
    choose a_m ha_m using hpiece_box
    have hsub_union : {t : ℝ | Function.update y i₀ t ∈ E} ⊆
        ⋃ m : Fin M, Icc (a_m m) (a_m m + δ / c) := by
      intro t ⟨htΩ, htF⟩
      obtain ⟨m, hm⟩ := mem_iUnion.mp (hcov htΩ)
      exact mem_iUnion.mpr ⟨m, ha_m m ⟨hm, htF⟩⟩
    calc (gaussianReal 0 1) {t : ℝ | Function.update y i₀ t ∈ E}
        ≤ (gaussianReal 0 1) (⋃ m : Fin M, Icc (a_m m) (a_m m + δ / c)) := measure_mono hsub_union
      _ ≤ ∑ m : Fin M, (gaussianReal 0 1) (Icc (a_m m) (a_m m + δ / c)) := measure_iUnion_fintype_le _ _
      _ ≤ ∑ _m : Fin M, ENNReal.ofReal (δ / (Real.sqrt (2 * Real.pi) * c)) := by
          refine Finset.sum_le_sum fun m _ => ?_
          refine (gaussianReal_le_density_vol _).trans ?_
          rw [Real.volume_Icc, add_sub_cancel_left, ← ENNReal.ofReal_mul (by positivity)]
          exact ENNReal.ofReal_le_ofReal (le_of_eq (by ring))
      _ = ENNReal.ofReal ((M : ℝ) * δ / (Real.sqrt (2 * Real.pi) * c)) := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
            ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg M), mul_div_assoc]
  let p_i₀ : ι → Prop := fun i => i = i₀
  let e_split := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => ℝ) p_i₀
  have hmp := measurePreserving_piEquivPiSubtypeProd (fun _ : ι => gaussianReal 0 1) p_i₀
  let μ_one := @Measure.pi (Subtype p_i₀) (fun _ => ℝ) (Subtype.fintype p_i₀) _
    (fun _ => gaussianReal 0 1)
  let μ_rest := @Measure.pi {i : ι // ¬ p_i₀ i} (fun _ => ℝ) (Subtype.fintype fun i => ¬ p_i₀ i) _
    (fun _ => gaussianReal 0 1)
  have hE_eq : γ_pi E = (μ_one.prod μ_rest) (e_split.symm ⁻¹' E) := by
    rw [← hmp.measure_preimage (e_split.symm.measurable hE_meas).nullMeasurableSet]
    congr 1; ext x
    change x ∈ E ↔ e_split.symm (e_split x) ∈ E
    rw [e_split.symm_apply_apply]
  have hprod_eval : (μ_one.prod μ_rest) (e_split.symm ⁻¹' E) =
      ∫⁻ z, μ_one {w : Subtype p_i₀ → ℝ | e_split.symm (w, z) ∈ E} ∂μ_rest :=
    Measure.prod_apply_symm (e_split.symm.measurable hE_meas)
  have hsec_le : ∀ z : {i : ι // ¬ p_i₀ i} → ℝ,
      μ_one {w : Subtype p_i₀ → ℝ | e_split.symm (w, z) ∈ E} ≤
        ENNReal.ofReal ((M : ℝ) * δ / (Real.sqrt (2 * Real.pi) * c)) := by
    intro z
    let y : ι → ℝ := e_split.symm (0, z)
    let j₀ : Subtype p_i₀ := ⟨i₀, rfl⟩
    have hupd_eq (w : Subtype p_i₀ → ℝ) :
        e_split.symm (w, z) = Function.update y i₀ (w j₀) := by
      funext i
      by_cases hi : i = i₀
      · subst hi; simp [e_split, y, j₀, p_i₀, MeasurableEquiv.piEquivPiSubtypeProd]
      · simp [e_split, y, hi, p_i₀, MeasurableEquiv.piEquivPiSubtypeProd]
    have hset_eq : {w : Subtype p_i₀ → ℝ | e_split.symm (w, z) ∈ E} =
        Set.univ.pi (fun _ : Subtype p_i₀ => {t : ℝ | Function.update y i₀ t ∈ E}) := by
      ext w
      simp only [mem_setOf_eq, mem_univ_pi, hupd_eq]
      exact ⟨fun hw ⟨j, hj⟩ => (Subtype.ext hj : (⟨j, hj⟩ : Subtype p_i₀) = j₀) ▸ hw,
             fun hw => hw j₀⟩
    rw [hset_eq]
    have hpi : μ_one (Set.univ.pi fun _ : Subtype p_i₀ => {t : ℝ | Function.update y i₀ t ∈ E}) =
        (gaussianReal 0 1) {t : ℝ | Function.update y i₀ t ∈ E} := by
      dsimp only [μ_one]
      rw [@Measure.pi_pi (Subtype p_i₀) (fun _ => ℝ) (Subtype.fintype p_i₀) _
        (fun _ => gaussianReal 0 1)]
      refine Finset.prod_eq_single j₀ ?_ ?_
      · rintro ⟨j, hj⟩ _ hne; exact (hne (Subtype.ext hj)).elim
      · intro h; exact (h (@Finset.mem_univ (Subtype p_i₀) (Subtype.fintype p_i₀) j₀)).elim
    rw [hpi]; exact h1d y
  have htot : γ_pi E ≤ ENNReal.ofReal ((M : ℝ) * δ / (Real.sqrt (2 * Real.pi) * c)) := by
    rw [hE_eq, hprod_eval]
    refine (lintegral_mono hsec_le).trans ?_
    haveI : IsProbabilityMeasure μ_rest := by dsimp only [μ_rest]; infer_instance
    rw [lintegral_const, measure_univ, mul_one]
  rw [Measure.real]
  exact ENNReal.toReal_le_of_le_ofReal (by positivity) htot

/-- Direct transfer of micro-band sign-coherent right Dini coercivity inside
`Ioo (1 / 10 - η_pad) (1 / 10 + δ + η_pad)` across active budgets
`j < (4 N + 1)(2 N + 2)(2^N)²` to fixed-`1 / 10` zero-drop locking `m_{1/10 + δ} = m_{1/10}`. -/
theorem fixed_tenth_locking_of_levelBand_dini {ι : Type*} [Fintype ι] [DecidableEq ι]
    {N : ℕ} (hN : 2 ≤ N) (i₀ : ι)
    (H : (ι → ℝ) → selfAdjoint (Register N))
    (hH_meas : ∀ j : ℕ, Measurable fun x => criticalHeight (H x) j)
    {Ω : ℕ → Set (ι → ℝ)} (hΩ_meas : ∀ j, MeasurableSet (Ω j))
    (M : ℕ) {c δ η_pad : ℝ} (hc : 0 < c) (hδ : 0 ≤ δ) (hη_pad : 0 < η_pad)
    (hfib : ∀ j < (4 * N + 1) * (2 * N + 2) * (2 ^ N) ^ 2, ∀ y : ι → ℝ,
      ∃ (I_piece : Fin M → Set ℝ) (sgn : Fin M → Bool),
        {t : ℝ | Function.update y i₀ t ∈ Ω j} ⊆ ⋃ m : Fin M, I_piece m ∧
        ∀ m : Fin M, Convex ℝ (I_piece m) ∧
          ContinuousOn (fun t => criticalHeight (H (Function.update y i₀ t)) j) (I_piece m) ∧
          ∀ t₁ ∈ I_piece m,
            criticalHeight (H (Function.update y i₀ t₁)) j ∈
              Ioo (1 / 10 - η_pad) (1 / 10 + δ + η_pad) →
            ∀ t₂ ∈ I_piece m, t₁ < t₂ → ∀ ε > 0,
              ∃ h ∈ Ioc (0 : ℝ) (t₂ - t₁),
                (c - ε) * h ≤
                  (if sgn m then 1 else -1) *
                    (criticalHeight (H (Function.update y i₀ (t₁ + h))) j -
                      criticalHeight (H (Function.update y i₀ t₁)) j)) :
    let Q := (4 * N + 1) * (2 * N + 2) * (2 ^ N) ^ 2
    let Ω_all := ⋂ j ∈ Finset.range Q, Ω j
    (Measure.pi fun _ : ι => gaussianReal 0 1).real
      {x ∈ Ω_all | ∃ m₁ m₂ : ℕ,
        IsRecurrentOrbitCircuitMaximumAt (H x) (1 / 10) m₁ ∧
        IsRecurrentOrbitCircuitMaximumAt (H x) (1 / 10 + δ) m₂ ∧ m₁ ≠ m₂} ≤
      (Q : ℝ) * ((M : ℝ) * δ / (Real.sqrt (2 * Real.pi) * c)) := by
  intro Q Ω_all
  let γ_pi := Measure.pi fun _ : ι => gaussianReal 0 1
  let Bad := {x : ι → ℝ | x ∈ Ω_all ∧ ∃ m₁ m₂ : ℕ,
    IsRecurrentOrbitCircuitMaximumAt (H x) (1 / 10) m₁ ∧
    IsRecurrentOrbitCircuitMaximumAt (H x) (1 / 10 + δ) m₂ ∧ m₁ ≠ m₂}
  have hsub : Bad ⊆ ⋃ j ∈ Finset.range Q,
      {x ∈ Ω j | criticalHeight (H x) j ∈ Ioc (1 / 10) (1 / 10 + δ)} := by
    rintro x ⟨hxΩ, m₁, m₂, hm₁, hm₂, hne⟩
    have hnot_clear : ¬ (1 / 10 : ℝ) ∉ jumpTolerances (H x) δ := fun hclear =>
      hne ((maximum_eq_iff_criticalHeight_clearance hN (H x) (by norm_num) hδ hm₁ hm₂).2.mpr hclear)
    rw [not_not] at hnot_clear
    obtain ⟨j, _, hj_mem⟩ := hnot_clear
    have hj_lt_Q : j < Q := by
      by_contra hge
      have h0 := criticalHeight_eq_zero_of_exact_cap hN (H x) (Nat.le_of_not_lt hge)
      rw [h0] at hj_mem; linarith only [hj_mem.1]
    exact mem_iUnion₂.mpr ⟨j, Finset.mem_range.mpr hj_lt_Q,
      (mem_iInter₂.mp hxΩ) j (Finset.mem_range.mpr hj_lt_Q), hj_mem⟩
  have hmeas_union : γ_pi Bad ≤ ∑ j ∈ Finset.range Q,
      γ_pi {x ∈ Ω j | criticalHeight (H x) j ∈ Ioc (1 / 10) (1 / 10 + δ)} :=
    (measure_mono hsub).trans (measure_biUnion_finset_le _ _)
  have hbound_enn : γ_pi Bad ≤
      ENNReal.ofReal ((Q : ℝ) * ((M : ℝ) * δ / (Real.sqrt (2 * Real.pi) * c))) := by
    refine hmeas_union.trans ?_
    calc ∑ j ∈ Finset.range Q, γ_pi {x ∈ Ω j | criticalHeight (H x) j ∈ Ioc (1 / 10) (1 / 10 + δ)}
        ≤ ∑ _j ∈ Finset.range Q, ENNReal.ofReal ((M : ℝ) * δ / (Real.sqrt (2 * Real.pi) * c)) := by
          refine Finset.sum_le_sum fun j hj => ?_
          have hreal := gaussian_levelBand_dini_anticoncentration i₀ (hH_meas j) (hΩ_meas j)
            M hc hδ hη_pad (hfib j (Finset.mem_range.mp hj))
          rw [← ENNReal.ofReal_toReal (measure_ne_top γ_pi _)]
          exact ENNReal.ofReal_le_ofReal hreal
      _ = ENNReal.ofReal ((Q : ℝ) * ((M : ℝ) * δ / (Real.sqrt (2 * Real.pi) * c))) := by
          simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
            ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg Q)]
  rw [Measure.real]
  exact ENNReal.toReal_le_of_le_ofReal (by positivity) hbound_enn

/-! ## Section 2: Zero-curvature max-min sawtooth oscillation obstruction -/

/-- Rising affine branch of tooth `a` with slope `+c` and zero second derivative. -/
def sawtoothLeft (c e₀ δ : ℝ) (a : ℕ) (t : ℝ) : ℝ :=
  e₀ + c * t - 4 * (a : ℝ) * δ

/-- Falling affine branch of tooth `a` with slope `-c` and zero second derivative. -/
def sawtoothRight (c e₀ δ : ℝ) (a : ℕ) (t : ℝ) : ℝ :=
  e₀ + (4 * (a : ℝ) + 4) * δ - c * t

/-- Single concave peak tooth `min (sawtoothLeft …) (sawtoothRight …)`. -/
def sawtoothTooth (c e₀ δ : ℝ) (a : ℕ) (t : ℝ) : ℝ :=
  min (sawtoothLeft c e₀ δ a t) (sawtoothRight c e₀ δ a t)

/-- `(K + 1) × 2` max-min sawtooth envelope of zero-curvature affine branches along `i₀`. -/
def maxMinSawtooth {ι : Type*} (i₀ : ι) (K : ℕ) (c e₀ δ : ℝ) (x : ι → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty
    fun a : Fin (K + 1) => max e₀ (sawtoothTooth c e₀ δ a.val (x i₀))

/-- Every underlying branch of `maxMinSawtooth` has constant derivative `±c` and identically
zero second derivative. -/
theorem deriv_deriv_sawtoothBranches_zero (c e₀ δ : ℝ) (a : ℕ) :
    (∀ t : ℝ, deriv (sawtoothLeft c e₀ δ a) t = c ∧ deriv (sawtoothRight c e₀ δ a) t = -c) ∧
    deriv (deriv (sawtoothLeft c e₀ δ a)) = 0 ∧
    deriv (deriv (sawtoothRight c e₀ δ a)) = 0 := by
  have hL : deriv (sawtoothLeft c e₀ δ a) = fun _ => c := by
    ext t
    have hd : HasDerivAt (sawtoothLeft c e₀ δ a) c t := by
      unfold sawtoothLeft
      simpa using (((hasDerivAt_id t).const_mul c).const_add e₀).sub_const (4 * (a : ℝ) * δ)
    exact hd.deriv
  have hR : deriv (sawtoothRight c e₀ δ a) = fun _ => -c := by
    ext t
    have hd : HasDerivAt (sawtoothRight c e₀ δ a) (-c) t := by
      unfold sawtoothRight
      simpa using ((hasDerivAt_id t).const_mul c).const_sub (e₀ + (4 * (a : ℝ) + 4) * δ)
    exact hd.deriv
  refine ⟨fun t => ⟨congrFun hL t, congrFun hR t⟩, ?_, ?_⟩
  · rw [hL]; ext t; exact deriv_const t c
  · rw [hR]; ext t; exact deriv_const t (-c)

/-- Zero-curvature max-min switching proliferation: for any `K ∈ ℕ`, `c > 0`, `e₀ ∈ ℝ`, and
`δ > 0` with `4 * (K + 1) * δ / c ≤ 1`, `maxMinSawtooth` has `2 * (K + 1)` disjoint rising/falling
crossings of `(e₀, e₀ + δ]` inside `[0, 1]` and product-Gaussian slice mass
`≥ (3 / 2) * gaussianDensityFloor * ((K + 1) * δ / c)`. -/
theorem maxMinSawtooth_gaussian_violation {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i₀ : ι) (K : ℕ) {c e₀ δ : ℝ} (hc : 0 < c) (hδ : 0 < δ)
    (hscale : 4 * ((K + 1 : ℕ) : ℝ) * δ / c ≤ 1) :
    (∀ a : Fin (K + 1), ∀ y : ι → ℝ,
      maxMinSawtooth i₀ K c e₀ δ (Function.update y i₀ (4 * (a.val : ℝ) * δ / c)) = e₀ ∧
      maxMinSawtooth i₀ K c e₀ δ (Function.update y i₀ ((4 * (a.val : ℝ) + 2) * δ / c)) =
        e₀ + 2 * δ ∧
      maxMinSawtooth i₀ K c e₀ δ (Function.update y i₀ ((4 * (a.val : ℝ) + 4) * δ / c)) = e₀) ∧
    (3 / 2 : ℝ) * gaussianDensityFloor * (((K + 1 : ℕ) : ℝ) * δ / c) ≤
      (Measure.pi fun _ : ι => gaussianReal 0 1).real
        {x : ι → ℝ | maxMinSawtooth i₀ K c e₀ δ x ∈ Ioc e₀ (e₀ + δ)} := by
  have htooth_out {a b : ℕ} (hne : b ≠ a) {t : ℝ}
      (ht : t ∈ Icc (4 * (a : ℝ) * δ / c) ((4 * (a : ℝ) + 4) * δ / c)) :
      sawtoothTooth c e₀ δ b t ≤ e₀ := by
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hb1 : (b : ℝ) + 1 ≤ (a : ℝ) := by exact_mod_cast hlt
      have hct : 4 * (a : ℝ) * δ ≤ c * t := by
        have := (div_le_iff₀ hc).mp ht.1; linarith only [this]
      refine (min_le_right _ _).trans ?_
      unfold sawtoothRight
      nlinarith only [hb1, hct, hδ]
    · have ha1 : (a : ℝ) + 1 ≤ (b : ℝ) := by exact_mod_cast hgt
      have hct : c * t ≤ (4 * (a : ℝ) + 4) * δ := by
        have := (le_div_iff₀ hc).mp ht.2; linarith only [this]
      refine (min_le_left _ _).trans ?_
      unfold sawtoothLeft
      nlinarith only [ha1, hct, hδ]
  have htooth_in (a : Fin (K + 1)) {t : ℝ}
      (ht : t ∈ Icc (4 * (a.val : ℝ) * δ / c) ((4 * (a.val : ℝ) + 4) * δ / c)) :
      e₀ ≤ sawtoothTooth c e₀ δ a.val t ∧
        (Finset.univ.sup' Finset.univ_nonempty
          fun b : Fin (K + 1) => max e₀ (sawtoothTooth c e₀ δ b.val t)) =
          sawtoothTooth c e₀ δ a.val t := by
    have hlo : 4 * (a.val : ℝ) * δ ≤ c * t := by
      have := (div_le_iff₀ hc).mp ht.1; linarith only [this]
    have hhi : c * t ≤ (4 * (a.val : ℝ) + 4) * δ := by
      have := (le_div_iff₀ hc).mp ht.2; linarith only [this]
    have hge_e₀ : e₀ ≤ sawtoothTooth c e₀ δ a.val t :=
      le_min (by unfold sawtoothLeft; linarith only [hlo])
             (by unfold sawtoothRight; linarith only [hhi])
    refine ⟨hge_e₀, le_antisymm ?_ ?_⟩
    · refine Finset.sup'_le _ _ fun b _ => max_le hge_e₀ ?_
      by_cases hba : b = a
      · subst hba; exact le_rfl
      · exact (htooth_out (Fin.val_ne_of_ne hba) ht).trans hge_e₀
    · exact (le_max_right e₀ _).trans
        (Finset.le_sup' (f := fun b : Fin (K + 1) => max e₀ (sawtoothTooth c e₀ δ b.val t))
          (Finset.mem_univ a))
  have hvals : ∀ a : Fin (K + 1), ∀ y : ι → ℝ,
      maxMinSawtooth i₀ K c e₀ δ (Function.update y i₀ (4 * (a.val : ℝ) * δ / c)) = e₀ ∧
      maxMinSawtooth i₀ K c e₀ δ (Function.update y i₀ ((4 * (a.val : ℝ) + 2) * δ / c)) =
        e₀ + 2 * δ ∧
      maxMinSawtooth i₀ K c e₀ δ (Function.update y i₀ ((4 * (a.val : ℝ) + 4) * δ / c)) = e₀ := by
    intro a y
    have ht1 : 4 * (a.val : ℝ) * δ / c ∈
        Icc (4 * (a.val : ℝ) * δ / c) ((4 * (a.val : ℝ) + 4) * δ / c) :=
      ⟨le_rfl, div_le_div_of_nonneg_right (by linarith only [hδ]) hc.le⟩
    have ht2 : (4 * (a.val : ℝ) + 2) * δ / c ∈
        Icc (4 * (a.val : ℝ) * δ / c) ((4 * (a.val : ℝ) + 4) * δ / c) :=
      ⟨div_le_div_of_nonneg_right (by linarith only [hδ]) hc.le,
       div_le_div_of_nonneg_right (by linarith only [hδ]) hc.le⟩
    have ht3 : (4 * (a.val : ℝ) + 4) * δ / c ∈
        Icc (4 * (a.val : ℝ) * δ / c) ((4 * (a.val : ℝ) + 4) * δ / c) :=
      ⟨div_le_div_of_nonneg_right (by linarith only [hδ]) hc.le, le_rfl⟩
    refine ⟨?_, ?_, ?_⟩
    · unfold maxMinSawtooth; rw [Function.update_self, (htooth_in a ht1).2]
      unfold sawtoothTooth sawtoothLeft sawtoothRight
      have hc1 : c * (4 * (a.val : ℝ) * δ / c) = 4 * (a.val : ℝ) * δ :=
        mul_div_cancel₀ _ hc.ne'
      rw [hc1]; exact min_eq_left (by linarith only [hδ]) |>.trans (by ring)
    · unfold maxMinSawtooth; rw [Function.update_self, (htooth_in a ht2).2]
      unfold sawtoothTooth sawtoothLeft sawtoothRight
      have hc2 : c * ((4 * (a.val : ℝ) + 2) * δ / c) = (4 * (a.val : ℝ) + 2) * δ :=
        mul_div_cancel₀ _ hc.ne'
      rw [hc2]; exact min_eq_left (by linarith only [hδ]) |>.trans (by ring)
    · unfold maxMinSawtooth; rw [Function.update_self, (htooth_in a ht3).2]
      unfold sawtoothTooth sawtoothLeft sawtoothRight
      have hc3 : c * ((4 * (a.val : ℝ) + 4) * δ / c) = (4 * (a.val : ℝ) + 4) * δ :=
        mul_div_cancel₀ _ hc.ne'
      rw [hc3]; exact min_eq_right (by linarith only [hδ]) |>.trans (by ring)
  refine ⟨hvals, ?_⟩
  -- 1D projection onto coordinate i₀ preserves standard Gaussian measure
  let γ := gaussianReal 0 1
  let f_1d : ℝ → ℝ := fun t =>
    Finset.univ.sup' Finset.univ_nonempty fun a : Fin (K + 1) => max e₀ (sawtoothTooth c e₀ δ a.val t)
  have hf_1d_cont : Continuous f_1d := by
    refine Continuous.finset_sup'_apply _ fun a _ => continuous_const.max ?_
    exact ((continuous_const.add (continuous_const.mul continuous_id)).sub continuous_const).min
      ((continuous_const.sub (continuous_const.mul continuous_id)))
  have hmp_eval : MeasurePreserving (fun x : ι → ℝ => x i₀)
      (Measure.pi fun _ : ι => γ) γ :=
    measurePreserving_eval (fun _ : ι => γ) i₀
  have hpre_eq : (Measure.pi fun _ : ι => γ).real
      {x : ι → ℝ | maxMinSawtooth i₀ K c e₀ δ x ∈ Ioc e₀ (e₀ + δ)} =
      γ.real {t : ℝ | f_1d t ∈ Ioc e₀ (e₀ + δ)} := by
    have hset : {x : ι → ℝ | maxMinSawtooth i₀ K c e₀ δ x ∈ Ioc e₀ (e₀ + δ)} =
        (fun x : ι → ℝ => x i₀) ⁻¹' (f_1d ⁻¹' Ioc e₀ (e₀ + δ)) := rfl
    have hmeas_S : MeasurableSet (f_1d ⁻¹' Ioc e₀ (e₀ + δ)) :=
      hf_1d_cont.measurable measurableSet_Ioc
    have h1 := congrArg ENNReal.toReal (hmp_eval.measure_preimage hmeas_S.nullMeasurableSet)
    rw [Measure.real_def, Measure.real_def, hset]
    exact h1
  rw [hpre_eq]
  let J : Fin (K + 1) × Bool → Set ℝ := fun p =>
    if p.2 then
      Icc ((4 * (p.1.val : ℝ) + 1 / 4) * δ / c) ((4 * (p.1.val : ℝ) + 1) * δ / c)
    else
      Icc ((4 * (p.1.val : ℝ) + 3) * δ / c) ((4 * (p.1.val : ℝ) + 15 / 4) * δ / c)
  have hJ_sub (p : Fin (K + 1) × Bool) : J p ⊆ {t : ℝ | f_1d t ∈ Ioc e₀ (e₀ + δ)} := by
    intro t ht
    have h_in_tooth : t ∈ Icc (4 * (p.1.val : ℝ) * δ / c) ((4 * (p.1.val : ℝ) + 4) * δ / c) := by
      dsimp only [J] at ht
      by_cases hb : p.2 = true
      · rw [if_pos hb] at ht
        exact ⟨(div_le_div_of_nonneg_right (by nlinarith only [hδ]) hc.le).trans ht.1,
               ht.2.trans (div_le_div_of_nonneg_right (by nlinarith only [hδ]) hc.le)⟩
      · rw [if_neg hb] at ht
        exact ⟨(div_le_div_of_nonneg_right (by nlinarith only [hδ]) hc.le).trans ht.1,
               ht.2.trans (div_le_div_of_nonneg_right (by nlinarith only [hδ]) hc.le)⟩
    have hf_eq : f_1d t = sawtoothTooth c e₀ δ p.1.val t := (htooth_in p.1 h_in_tooth).2
    rw [mem_setOf_eq, hf_eq]
    dsimp only [J] at ht
    by_cases hb : p.2 = true
    · rw [if_pos hb] at ht
      have hlo := (div_le_iff₀ hc).mp ht.1
      have hhi := (le_div_iff₀ hc).mp ht.2
      have hmin_eq : sawtoothTooth c e₀ δ p.1.val t = sawtoothLeft c e₀ δ p.1.val t :=
        min_eq_left (by unfold sawtoothLeft sawtoothRight; linarith only [hhi, hδ])
      rw [hmin_eq]; unfold sawtoothLeft
      exact ⟨by linarith only [hlo, hδ], by linarith only [hhi]⟩
    · rw [if_neg hb] at ht
      have hlo := (div_le_iff₀ hc).mp ht.1
      have hhi := (le_div_iff₀ hc).mp ht.2
      have hmin_eq : sawtoothTooth c e₀ δ p.1.val t = sawtoothRight c e₀ δ p.1.val t :=
        min_eq_right (by unfold sawtoothLeft sawtoothRight; linarith only [hlo, hδ])
      rw [hmin_eq]; unfold sawtoothRight
      exact ⟨by linarith only [hhi, hδ], by linarith only [hlo]⟩
  have hJ_disj : Pairwise fun p₁ p₂ => Disjoint (J p₁) (J p₂) := by
    intro p₁ p₂ hpne
    refine Set.disjoint_left.mpr fun t ht₁ ht₂ => ?_
    have htooth_bounds (p : Fin (K + 1) × Bool) {s : ℝ} (hs : s ∈ J p) :
        4 * (p.1.val : ℝ) * δ < c * s ∧ c * s < (4 * (p.1.val : ℝ) + 4) * δ := by
      dsimp only [J] at hs
      by_cases hb : p.2 = true
      · rw [if_pos hb] at hs
        exact ⟨by linarith only [(div_le_iff₀ hc).mp hs.1, hδ],
               by linarith only [(le_div_iff₀ hc).mp hs.2, hδ]⟩
      · rw [if_neg hb] at hs
        exact ⟨by linarith only [(div_le_iff₀ hc).mp hs.1, hδ],
               by linarith only [(le_div_iff₀ hc).mp hs.2, hδ]⟩
    by_cases ha : p₁.1 = p₂.1
    · have hb_ne : p₁.2 ≠ p₂.2 := fun hb => hpne (Prod.ext ha hb)
      dsimp only [J] at ht₁ ht₂
      rw [← ha] at ht₂
      cases h1 : p₁.2 <;> cases h2 : p₂.2
      · exact hb_ne (h1.trans h2.symm)
      · rw [h1] at ht₁; rw [h2] at ht₂; simp only [if_true, Bool.false_eq_true, if_false] at ht₁ ht₂
        nlinarith only [(div_le_iff₀ hc).mp ht₁.1, (le_div_iff₀ hc).mp ht₂.2, hδ]
      · rw [h1] at ht₁; rw [h2] at ht₂; simp only [if_true, Bool.false_eq_true, if_false] at ht₁ ht₂
        nlinarith only [(le_div_iff₀ hc).mp ht₁.2, (div_le_iff₀ hc).mp ht₂.1, hδ]
      · exact hb_ne (h1.trans h2.symm)
    · have hb₁ := htooth_bounds p₁ ht₁
      have hb₂ := htooth_bounds p₂ ht₂
      rcases lt_or_gt_of_ne (Fin.val_ne_of_ne ha) with hlt | hgt
      · have hle : (p₁.1.val : ℝ) + 1 ≤ (p₂.1.val : ℝ) := by exact_mod_cast hlt
        nlinarith only [hb₁.2, hb₂.1, hle, hδ]
      · have hle : (p₂.1.val : ℝ) + 1 ≤ (p₁.1.val : ℝ) := by exact_mod_cast hgt
        nlinarith only [hb₂.2, hb₁.1, hle, hδ]
  have hJ_mass (p : Fin (K + 1) × Bool) :
      ENNReal.ofReal (gaussianDensityFloor * (3 * δ / (4 * c))) ≤ γ (J p) := by
    have h_i01 : J p ⊆ Icc (0 : ℝ) 1 := by
      intro t ht
      have ha_lt : (p.1.val : ℝ) + 1 ≤ ((K + 1 : ℕ) : ℝ) := by exact_mod_cast p.1.isLt
      have htop : (4 * (p.1.val : ℝ) + 4) * δ / c ≤ 1 :=
        (div_le_div_of_nonneg_right (by nlinarith only [ha_lt, hδ]) hc.le).trans hscale
      dsimp only [J] at ht
      by_cases hb : p.2 = true
      · rw [if_pos hb] at ht
        exact ⟨(div_nonneg (by positivity) hc.le).trans ht.1,
               ht.2.trans ((div_le_div_of_nonneg_right (by linarith only [hδ]) hc.le).trans htop)⟩
      · rw [if_neg hb] at ht
        exact ⟨(div_nonneg (by positivity) hc.le).trans ht.1,
               ht.2.trans ((div_le_div_of_nonneg_right (by linarith only [hδ]) hc.le).trans htop)⟩
    have hvol : volume (J p) = ENNReal.ofReal (3 * δ / (4 * c)) := by
      dsimp only [J]
      by_cases hb : p.2 = true
      · rw [if_pos hb, Real.volume_Icc]; congr 1; field_simp [hc.ne']; ring
      · rw [if_neg hb, Real.volume_Icc]; congr 1; field_simp [hc.ne']; ring
    rw [gaussianReal_apply 0 (by norm_num) (J p),
      ENNReal.ofReal_mul gaussianDensityFloor_pos.le, ← hvol,
      ← setLIntegral_const (J p) (ENNReal.ofReal gaussianDensityFloor)]
    refine setLIntegral_mono_ae (by fun_prop) ?_
    filter_upwards with t ht
    have ht01 := h_i01 ht
    rw [gaussianPDF]
    exact ENNReal.ofReal_le_ofReal
      (gaussianPDFReal_ge_floor (abs_le.mpr ⟨by linarith only [ht01.1], ht01.2⟩))
  have hunion_sub : (⋃ p : Fin (K + 1) × Bool, J p) ⊆ {t : ℝ | f_1d t ∈ Ioc e₀ (e₀ + δ)} :=
    iUnion_subset hJ_sub
  have hmeas_sum : γ (⋃ p : Fin (K + 1) × Bool, J p) = ∑ p : Fin (K + 1) × Bool, γ (J p) := by
    have hu : (⋃ p : Fin (K + 1) × Bool, J p) =
        ⋃ p ∈ (Finset.univ : Finset (Fin (K + 1) × Bool)), J p := by simp
    rw [hu, measure_biUnion_finset
      (fun p₁ _ p₂ _ hne => hJ_disj hne)
      (fun p _ => by dsimp only [J]; split_ifs <;> exact measurableSet_Icc)]
  have hsum_enn : ENNReal.ofReal
      ((3 / 2 : ℝ) * gaussianDensityFloor * (((K + 1 : ℕ) : ℝ) * δ / c)) ≤
      γ {t : ℝ | f_1d t ∈ Ioc e₀ (e₀ + δ)} := by
    refine le_trans ?_ ((le_of_eq hmeas_sum.symm).trans (measure_mono hunion_sub))
    calc ENNReal.ofReal ((3 / 2 : ℝ) * gaussianDensityFloor * (((K + 1 : ℕ) : ℝ) * δ / c))
        = ∑ _p : Fin (K + 1) × Bool, ENNReal.ofReal (gaussianDensityFloor * (3 * δ / (4 * c))) := by
            simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
              Fintype.card_bool, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
              ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
            congr 1; push_cast; ring
      _ ≤ ∑ p : Fin (K + 1) × Bool, γ (J p) := Finset.sum_le_sum fun p _ => hJ_mass p
  rw [Measure.real]
  exact (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).mp hsum_enn

/-! ## Section 3: Kato spectral-gap connection bound and mode-slope Lipschitz stability -/

private def katoCoreOfBasis {N : ℕ} (V : UGroup N) (E : Config N → ℝ)
    (P : selfAdjoint (Register N)) : Register N :=
  let P_tilde : Register N := star V.val * P.val * V.val
  fun a b => if E b = E a then 0 else -Complex.I * P_tilde a b / ((E b - E a : ℝ) : ℂ)

private def katoGeneratorOfBasis {N : ℕ} (V : UGroup N) (E : Config N → ℝ)
    (P : selfAdjoint (Register N)) : selfAdjoint (Register N) :=
  ⟨V.val * katoCoreOfBasis V E P * star V.val, by
    let P_tilde : Register N := star V.val * P.val * V.val
    have hP_sa : star P_tilde = P_tilde := by
      dsimp [P_tilde]
      rw [star_mul, star_mul, star_star, P.2.star_eq, mul_assoc]
    have hK_sa : star (katoCoreOfBasis V E P) = katoCoreOfBasis V E P := by
      ext a b
      rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply]
      change star (if E a = E b then 0 else -Complex.I * P_tilde b a / ((E a - E b : ℝ) : ℂ)) =
        if E b = E a then 0 else -Complex.I * P_tilde a b / ((E b - E a : ℝ) : ℂ)
      by_cases h : E a = E b
      · rw [if_pos h, if_pos h.symm, star_zero]
      · have hba : ¬ E b = E a := fun heq => h heq.symm
        rw [if_neg h, if_neg hba]
        have hP_entry : star (P_tilde b a) = P_tilde a b := by
          have h1 := congrArg (fun M : Register N => M a b) hP_sa
          simpa [Matrix.star_eq_conjTranspose] using h1
        rw [Complex.star_def, map_div₀, map_mul, map_neg, Complex.conj_I, neg_neg,
          ← Complex.star_def, hP_entry, Complex.star_def, Complex.conj_ofReal]
        have hden : ((E a - E b : ℝ) : ℂ) = -((E b - E a : ℝ) : ℂ) := by push_cast; ring
        rw [hden, div_neg, neg_mul]; ring
    rw [selfAdjoint.mem_iff, star_mul, star_mul, star_star, hK_sa, mul_assoc]⟩

private theorem katoGeneratorOfBasis_commutator_eq {N : ℕ} (V : UGroup N) (E : Config N → ℝ)
    (H P : selfAdjoint (Register N))
    (hspec : H.val = V.val * Matrix.diagonal (Complex.ofReal ∘ E) * star V.val)
    (hsimple : Function.Injective E) :
    let P_tilde := star V.val * P.val * V.val
    Complex.I • ((katoGeneratorOfBasis V E P).val * H.val -
      H.val * (katoGeneratorOfBasis V E P).val) =
      P.val - V.val * Matrix.diagonal (fun a => P_tilde a a) * star V.val := by
  intro P_tilde
  let K_tilde : Register N := katoCoreOfBasis V E P
  have hK_def : (katoGeneratorOfBasis V E P).val = V.val * K_tilde * star V.val := rfl
  have hV_mul1 : star V.val * V.val = 1 := (Unitary.mem_iff.mp V.2).1
  have hV_mul2 : V.val * star V.val = 1 := (Unitary.mem_iff.mp V.2).2
  have hinner_comm : Complex.I • (K_tilde * Matrix.diagonal (Complex.ofReal ∘ E) -
      Matrix.diagonal (Complex.ofReal ∘ E) * K_tilde) =
      P_tilde - Matrix.diagonal (fun a => P_tilde a a) := by
    ext a b
    simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.mul_diagonal, Matrix.diagonal_mul,
      Function.comp_apply, smul_eq_mul]
    change Complex.I *
      ((if E b = E a then 0 else -Complex.I * P_tilde a b / ((E b - E a : ℝ) : ℂ)) * (E b : ℂ) -
       (E a : ℂ) * (if E b = E a then 0 else -Complex.I * P_tilde a b / ((E b - E a : ℝ) : ℂ))) =
      P_tilde a b - Matrix.diagonal (fun c => P_tilde c c) a b
    by_cases hab : a = b
    · subst hab; simp
    · have hE_ne : E b ≠ E a := fun heq => hab (hsimple heq.symm)
      have hdiff_ne : ((E b - E a : ℝ) : ℂ) ≠ 0 := by
        exact_mod_cast sub_ne_zero.mpr hE_ne
      rw [if_neg hE_ne, Matrix.diagonal_apply_ne _ hab, sub_zero]
      calc Complex.I * (-Complex.I * P_tilde a b / ((E b - E a : ℝ) : ℂ) * (E b : ℂ) -
              (E a : ℂ) * (-Complex.I * P_tilde a b / ((E b - E a : ℝ) : ℂ)))
          = -(Complex.I * Complex.I) * P_tilde a b *
              (((E b : ℂ) - (E a : ℂ)) / ((E b - E a : ℝ) : ℂ)) := by ring
        _ = P_tilde a b := by
            rw [Complex.I_mul_I, show (E b : ℂ) - (E a : ℂ) = ((E b - E a : ℝ) : ℂ) by push_cast; ring,
              div_self hdiff_ne]
            ring
  have hprod1 : (V.val * K_tilde * star V.val) *
      (V.val * Matrix.diagonal (Complex.ofReal ∘ E) * star V.val) =
      V.val * (K_tilde * Matrix.diagonal (Complex.ofReal ∘ E)) * star V.val := by
    calc (V.val * K_tilde * star V.val) * (V.val * Matrix.diagonal (Complex.ofReal ∘ E) * star V.val)
        = V.val * K_tilde * (star V.val * V.val) * Matrix.diagonal (Complex.ofReal ∘ E) * star V.val := by
            noncomm_ring
      _ = V.val * (K_tilde * Matrix.diagonal (Complex.ofReal ∘ E)) * star V.val := by
            rw [hV_mul1]; noncomm_ring
  have hprod2 : (V.val * Matrix.diagonal (Complex.ofReal ∘ E) * star V.val) *
      (V.val * K_tilde * star V.val) =
      V.val * (Matrix.diagonal (Complex.ofReal ∘ E) * K_tilde) * star V.val := by
    calc (V.val * Matrix.diagonal (Complex.ofReal ∘ E) * star V.val) * (V.val * K_tilde * star V.val)
        = V.val * Matrix.diagonal (Complex.ofReal ∘ E) * (star V.val * V.val) * K_tilde * star V.val := by
            noncomm_ring
      _ = V.val * (Matrix.diagonal (Complex.ofReal ∘ E) * K_tilde) * star V.val := by
            rw [hV_mul1]; noncomm_ring
  have hVP : V.val * P_tilde * star V.val = P.val := by
    dsimp [P_tilde]
    calc V.val * (star V.val * P.val * V.val) * star V.val
        = (V.val * star V.val) * P.val * (V.val * star V.val) := by noncomm_ring
      _ = P.val := by rw [hV_mul2, one_mul, mul_one]
  rw [hK_def, hspec, hprod1, hprod2]
  calc Complex.I • (V.val * (K_tilde * Matrix.diagonal (Complex.ofReal ∘ E)) * star V.val -
          V.val * (Matrix.diagonal (Complex.ofReal ∘ E) * K_tilde) * star V.val)
      = V.val * (Complex.I • (K_tilde * Matrix.diagonal (Complex.ofReal ∘ E) -
          Matrix.diagonal (Complex.ofReal ∘ E) * K_tilde)) * star V.val := by
          rw [← Matrix.sub_mul, ← Matrix.mul_sub, Matrix.mul_smul, Matrix.smul_mul]
    _ = V.val * (P_tilde - Matrix.diagonal (fun a => P_tilde a a)) * star V.val := by
          rw [hinner_comm]
    _ = P.val - V.val * Matrix.diagonal (fun a => P_tilde a a) * star V.val := by
          rw [Matrix.mul_sub, Matrix.sub_mul, hVP]

private theorem norm_katoGeneratorOfBasis_le {N : ℕ} (V : UGroup N) (E : Config N → ℝ)
    (P : selfAdjoint (Register N)) {Δ : ℝ} (hΔ : 0 < Δ)
    (hgap : ∀ a b : Config N, a ≠ b → Δ ≤ |E b - E a|) :
    ‖(katoGeneratorOfBasis V E P).val‖ ≤ Real.sqrt ((2 : ℝ) ^ N) * ‖P.val‖ / Δ := by
  let P_tilde : Register N := star V.val * P.val * V.val
  let K_tilde : Register N := katoCoreOfBasis V E P
  have hP_norm : ‖P_tilde‖ = ‖P.val‖ := by
    have h1 := l2_opNorm_unitary_conj_eq (V := star V.val) (Unitary.star_mem V.2) P.val
    simpa only [star_star] using h1
  have hK_norm : ‖(katoGeneratorOfBasis V E P).val‖ = ‖K_tilde‖ :=
    l2_opNorm_unitary_conj_eq (V := V.val) V.2 K_tilde
  rw [hK_norm]
  have hrow_sq (a : Config N) (ψ : StateSpace N) :
      ‖(matAct K_tilde ψ).ofLp a‖ ^ 2 ≤
        (∑ b : Config N, ‖K_tilde a b‖ ^ 2) * ‖ψ‖ ^ 2 := by
    have hact : (matAct K_tilde ψ).ofLp a = ∑ b : Config N, K_tilde a b * ψ.ofLp b := by
      simp [matAct, Matrix.mulVec, dotProduct]
    rw [hact, EuclideanSpace.norm_sq_eq]
    calc ‖∑ b : Config N, K_tilde a b * ψ.ofLp b‖ ^ 2
        ≤ (∑ b : Config N, ‖K_tilde a b * ψ.ofLp b‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
      _ = (∑ b : Config N, ‖K_tilde a b‖ * ‖ψ.ofLp b‖) ^ 2 := by
          simp_rw [norm_mul]
      _ ≤ (∑ b : Config N, ‖K_tilde a b‖ ^ 2) * (∑ b : Config N, ‖ψ.ofLp b‖ ^ 2) :=
          Finset.sum_mul_sq_le_sq_mul_sq Finset.univ _ _
  have hcol_sum : (∑ a : Config N, ∑ b : Config N, ‖K_tilde a b‖ ^ 2) ≤
      ((2 : ℝ) ^ N * ‖P.val‖ ^ 2) / Δ ^ 2 := by
    have hpt (a b : Config N) : ‖K_tilde a b‖ ^ 2 ≤ ‖P_tilde a b‖ ^ 2 / Δ ^ 2 := by
      change ‖if E b = E a then 0 else -Complex.I * P_tilde a b / ((E b - E a : ℝ) : ℂ)‖ ^ 2 ≤ _
      by_cases hE : E b = E a
      · rw [if_pos hE, norm_zero, zero_pow two_pos.ne']
        exact div_nonneg (sq_nonneg _) (sq_nonneg _)
      · have hab : a ≠ b := fun heq => hE (congrArg E heq.symm)
        rw [if_neg hE, norm_div, norm_mul, norm_neg, Complex.norm_I, one_mul,
          Complex.norm_real, Real.norm_eq_abs, div_pow]
        exact div_le_div_of_nonneg_left (sq_nonneg _) (pow_pos hΔ 2)
          (pow_le_pow_left₀ hΔ.le (hgap a b hab) 2)
    have hhs_P : (∑ a : Config N, ∑ b : Config N, ‖P_tilde a b‖ ^ 2) ≤
        (2 : ℝ) ^ N * ‖P.val‖ ^ 2 := by
      rw [Finset.sum_comm]
      have hcol (b : Config N) : (∑ a : Config N, ‖P_tilde a b‖ ^ 2) ≤ ‖P.val‖ ^ 2 := by
        let e_b : StateSpace N := EuclideanSpace.single b 1
        have he_norm : ‖e_b‖ = 1 := by simp [e_b]
        have h1 := pow_le_pow_left₀ (norm_nonneg _) (norm_matAct_le' P_tilde e_b) 2
        rw [hP_norm, he_norm, mul_one, EuclideanSpace.norm_sq_eq] at h1
        refine (le_of_eq ?_).trans h1
        refine Finset.sum_congr rfl fun a _ => ?_
        have happ : (matAct P_tilde e_b).ofLp a = P_tilde a b := by
          simp [matAct, e_b]
        rw [happ]
      calc (∑ b : Config N, ∑ a : Config N, ‖P_tilde a b‖ ^ 2)
          ≤ ∑ _b : Config N, ‖P.val‖ ^ 2 := Finset.sum_le_sum fun b _ => hcol b
        _ = (2 : ℝ) ^ N * ‖P.val‖ ^ 2 := by
            simp [Config, Finset.sum_const, nsmul_eq_mul]
    calc (∑ a : Config N, ∑ b : Config N, ‖K_tilde a b‖ ^ 2)
        ≤ ∑ a : Config N, ∑ b : Config N, ‖P_tilde a b‖ ^ 2 / Δ ^ 2 :=
          Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => hpt a b
      _ = (∑ a : Config N, ∑ b : Config N, ‖P_tilde a b‖ ^ 2) / Δ ^ 2 := by
          simp_rw [← Finset.sum_div]
      _ ≤ ((2 : ℝ) ^ N * ‖P.val‖ ^ 2) / Δ ^ 2 :=
          div_le_div_of_nonneg_right hhs_P (sq_nonneg Δ)
  have hbound_C : 0 ≤ Real.sqrt ((2 : ℝ) ^ N) * ‖P.val‖ / Δ :=
    div_nonneg (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)) hΔ.le
  refine opNorm_le_of_matAct_le' hbound_C fun ψ => ?_
  have hsq : ‖matAct K_tilde ψ‖ ^ 2 ≤ (Real.sqrt ((2 : ℝ) ^ N) * ‖P.val‖ / Δ * ‖ψ‖) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    calc (∑ a : Config N, ‖(matAct K_tilde ψ).ofLp a‖ ^ 2)
        ≤ ∑ a : Config N, (∑ b : Config N, ‖K_tilde a b‖ ^ 2) * ‖ψ‖ ^ 2 :=
          Finset.sum_le_sum fun a _ => hrow_sq a ψ
      _ = (∑ a : Config N, ∑ b : Config N, ‖K_tilde a b‖ ^ 2) * ‖ψ‖ ^ 2 :=
          (Finset.sum_mul _ _ _).symm
      _ ≤ (((2 : ℝ) ^ N * ‖P.val‖ ^ 2) / Δ ^ 2) * ‖ψ‖ ^ 2 :=
          mul_le_mul_of_nonneg_right hcol_sum (sq_nonneg _)
      _ = (Real.sqrt ((2 : ℝ) ^ N) * ‖P.val‖ / Δ * ‖ψ‖) ^ 2 := by
          rw [mul_pow, div_pow, mul_pow, Real.sq_sqrt (pow_nonneg two_pos.le N), mul_div_right_comm]
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hbound_C (norm_nonneg _))).mp hsq

/-- Off-diagonal Kato resolvent connection `K ∈ selfAdjoint (Register N)` associated with `(H, P)`,
defined in `hermitianEigenbasisUnitary H` by `K̃_{a b} = -i P̃_{a b} / (E_b - E_a)` (`0` when
`E_b = E_a`). -/
def katoOffDiagGenerator {N : ℕ} (H P : selfAdjoint (Register N)) : selfAdjoint (Register N) :=
  katoGeneratorOfBasis (hermitianEigenbasisUnitary H.2.isHermitian) H.2.isHermitian.eigenvalues P

/-- Exact Kato commutator equation under simple spectrum of `H`:
`i (K * H - H * K) = P - V * diagonal (diag (V* P V)) * V*`. -/
theorem katoOffDiagGenerator_commutator_eq {N : ℕ} (H P : selfAdjoint (Register N))
    (hsimple : Function.Injective H.2.isHermitian.eigenvalues) :
    let V := hermitianEigenbasisUnitary H.2.isHermitian
    let P_tilde := star V.val * P.val * V.val
    Complex.I • ((katoOffDiagGenerator H P).val * H.val -
      H.val * (katoOffDiagGenerator H P).val) =
      P.val - V.val * Matrix.diagonal (fun a => P_tilde a a) * star V.val :=
  katoGeneratorOfBasis_commutator_eq (hermitianEigenbasisUnitary H.2.isHermitian)
    H.2.isHermitian.eigenvalues H P H.2.isHermitian.spectral_theorem hsimple

/-- Spectral-gap operator-norm bound for `katoOffDiagGenerator H P`: if `min_{a ≠ b} |E_a - E_b| ≥ Δ > 0`,
then `‖katoOffDiagGenerator H P‖ ≤ √(2^N) * ‖P‖ / Δ`. -/
theorem norm_katoOffDiagGenerator_le {N : ℕ} (H P : selfAdjoint (Register N))
    {Δ : ℝ} (hΔ : 0 < Δ)
    (hgap : ∀ a b : Config N, a ≠ b →
      Δ ≤ |H.2.isHermitian.eigenvalues b - H.2.isHermitian.eigenvalues a|) :
    ‖(katoOffDiagGenerator H P).val‖ ≤ Real.sqrt ((2 : ℝ) ^ N) * ‖P.val‖ / Δ :=
  norm_katoGeneratorOfBasis_le (hermitianEigenbasisUnitary H.2.isHermitian)
    H.2.isHermitian.eigenvalues P hΔ hgap

/-- Commutator-cancellation Lipschitz law for the saddle expectation shift along `e^{-i u K}`:
for any contraction `U₀` (`‖U₀‖ ≤ 1`), self-adjoint `K`, and unit-ball state `ψ` (`‖ψ‖ ≤ 1`),
`Φ(u) = Re ⟨U(u) ψ, K U(u) ψ⟩ - Re ⟨ψ, K ψ⟩` satisfies `|Φ(u) - Φ(0)| ≤ 2 ‖K‖² |u|`. -/
theorem transverse_mode_slope_lipschitz {N : ℕ} {U₀ : Register N} (hU₀ : ‖U₀‖ ≤ 1)
    (K : selfAdjoint (Register N)) {ψ : StateSpace N} (hψ : ‖ψ‖ ≤ 1) (u : ℝ) :
    let U_u := unitaryEvolution K.val u * U₀ * star (unitaryEvolution K.val u)
    |((inner ℂ (matAct U_u ψ) (matAct K.val (matAct U_u ψ))).re -
        (inner ℂ ψ (matAct K.val ψ)).re) -
      ((inner ℂ (matAct U₀ ψ) (matAct K.val (matAct U₀ ψ))).re -
        (inner ℂ ψ (matAct K.val ψ)).re)| ≤
      2 * ‖K.val‖ ^ 2 * |u| := by
  intro U_u
  let W := unitaryEvolution K.val u
  have hW_unit : W ∈ unitary (Register N) := unitaryEvolution_mem_unitary K.2 u
  have hcomm_K : K.val * W = W * K.val := unitaryEvolution_commutes_generator K.val u
  let φ : StateSpace N := matAct (star W) ψ
  have hφ_norm : ‖φ‖ ≤ 1 := by
    have hst : ‖star W‖ = 1 := by rw [norm_star]; exact CStarRing.norm_of_mem_unitary hW_unit
    exact (norm_matAct_le' (star W) ψ).trans (by rw [hst, one_mul]; exact hψ)
  have hquad_cancel : inner ℂ (matAct U_u ψ) (matAct K.val (matAct U_u ψ)) =
      inner ℂ (matAct U₀ φ) (matAct K.val (matAct U₀ φ)) := by
    have hact_Uu : matAct U_u ψ = matAct W (matAct U₀ φ) := by
      dsimp only [U_u, W, φ]; rw [matAct_mul', matAct_mul']
    rw [hact_Uu, ← matAct_mul' K.val W, hcomm_K, matAct_mul',
      ← inner_matAct_star_left' W, ← matAct_mul' (star W) W,
      (Unitary.mem_iff.mp hW_unit).1]
    have hone (v : StateSpace N) : matAct 1 v = v := by ext i; simp [matAct]
    rw [hone]
  let X := matAct U₀ φ
  let Y := matAct U₀ ψ
  have hX_norm : ‖X‖ ≤ 1 := (norm_matAct_le' U₀ φ).trans
    ((mul_le_mul hU₀ hφ_norm (norm_nonneg _) zero_le_one).trans_eq (one_mul 1))
  have hY_norm : ‖Y‖ ≤ 1 := (norm_matAct_le' U₀ ψ).trans
    ((mul_le_mul hU₀ hψ (norm_nonneg _) zero_le_one).trans_eq (one_mul 1))
  have hdiff_inner : inner ℂ X (matAct K.val X) - inner ℂ Y (matAct K.val Y) =
      inner ℂ (X - Y) (matAct K.val X) + inner ℂ Y (matAct K.val (X - Y)) := by
    rw [inner_sub_left, matAct_map_sub', inner_sub_right]
    ring
  have hXY_le : ‖X - Y‖ ≤ ‖K.val‖ * |u| := by
    have h1 : X - Y = matAct U₀ (matAct (star W - 1) ψ) := by
      dsimp only [X, Y, φ]
      rw [← matAct_map_sub', matAct_sub_left]
      have hone : matAct 1 ψ = ψ := by ext i; simp [matAct]
      rw [hone]
    have hst_diff : ‖star W - (1 : Register N)‖ = ‖W - 1‖ :=
      calc ‖star W - (1 : Register N)‖ = ‖star (W - 1)‖ := by rw [star_sub, star_one]
        _ = ‖W - 1‖ := norm_star _
    have hW_diff : ‖W - 1‖ ≤ ‖K.val‖ * |u| := by
      have h0 : unitaryEvolution K.val 0 = 1 := by simp [unitaryEvolution]
      simpa only [W, h0, sub_zero] using norm_unitaryEvolution_time_sub_le K.2 u 0
    rw [h1]
    calc ‖matAct U₀ (matAct (star W - 1) ψ)‖
        ≤ ‖U₀‖ * ‖matAct (star W - 1) ψ‖ := norm_matAct_le' _ _
      _ ≤ 1 * (‖star W - 1‖ * ‖ψ‖) := mul_le_mul hU₀ (norm_matAct_le' _ _)
            (norm_nonneg _) zero_le_one
      _ ≤ ‖star W - 1‖ * 1 := by
            rw [one_mul]; exact mul_le_mul_of_nonneg_left hψ (norm_nonneg _)
      _ = ‖W - 1‖ := by rw [mul_one, hst_diff]
      _ ≤ ‖K.val‖ * |u| := hW_diff
  have hsimp_diff : ((inner ℂ (matAct U_u ψ) (matAct K.val (matAct U_u ψ))).re -
        (inner ℂ ψ (matAct K.val ψ)).re) -
      ((inner ℂ (matAct U₀ ψ) (matAct K.val (matAct U₀ ψ))).re -
        (inner ℂ ψ (matAct K.val ψ)).re) =
      (inner ℂ X (matAct K.val X) - inner ℂ Y (matAct K.val Y)).re := by
    rw [hquad_cancel]; dsimp only [X, Y]; rw [Complex.sub_re]; ring
  rw [hsimp_diff]
  calc |(inner ℂ X (matAct K.val X) - inner ℂ Y (matAct K.val Y)).re|
      ≤ ‖inner ℂ X (matAct K.val X) - inner ℂ Y (matAct K.val Y)‖ := Complex.abs_re_le_norm _
    _ = ‖inner ℂ (X - Y) (matAct K.val X) + inner ℂ Y (matAct K.val (X - Y))‖ := by
          rw [hdiff_inner]
    _ ≤ ‖inner ℂ (X - Y) (matAct K.val X)‖ + ‖inner ℂ Y (matAct K.val (X - Y))‖ :=
          norm_add_le _ _
    _ ≤ ‖X - Y‖ * (‖K.val‖ * 1) + 1 * (‖K.val‖ * ‖X - Y‖) := by
          refine add_le_add ?_ ?_
          · exact (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left
              ((norm_matAct_le' K.val X).trans (mul_le_mul_of_nonneg_left hX_norm (norm_nonneg _)))
              (norm_nonneg _))
          · exact (norm_inner_le_norm _ _).trans (mul_le_mul hY_norm
              (norm_matAct_le' K.val (X - Y)) (norm_nonneg _) zero_le_one)
    _ = 2 * ‖K.val‖ * ‖X - Y‖ := by ring
    _ ≤ 2 * ‖K.val‖ * (‖K.val‖ * |u|) :=
          mul_le_mul_of_nonneg_left hXY_le (mul_nonneg two_pos.le (norm_nonneg _))
    _ = 2 * ‖K.val‖ ^ 2 * |u| := by ring

/-! ## Section 4: Super-polynomial (`2^(N - 1)`) active-saddle switches on `H₀ + t Z₀` -/

private def acRad (ε Δ : ℝ) : ℝ := Real.sqrt (Δ ^ 2 + ε ^ 2)
private def acCos (ε Δ : ℝ) : ℝ := Real.sqrt ((1 + Δ / acRad ε Δ) / 2)
private def acSin (ε Δ : ℝ) : ℝ := Real.sqrt ((1 - Δ / acRad ε Δ) / 2)

private theorem acRad_pos {ε : ℝ} (hε : 0 < ε) (Δ : ℝ) : 0 < acRad ε Δ :=
  Real.sqrt_pos.mpr (by positivity)

private theorem abs_div_acRad_lt_one {ε : ℝ} (hε : 0 < ε) (Δ : ℝ) :
    |Δ| / acRad ε Δ < 1 := by
  rw [div_lt_one (acRad_pos hε Δ)]
  have hlt : |Δ| ^ 2 < (acRad ε Δ) ^ 2 := by
    rw [sq_abs, acRad, Real.sq_sqrt (by positivity)]
    linarith only [sq_pos_of_pos hε]
  nlinarith only [hlt, abs_nonneg Δ, (acRad_pos hε Δ).le]

private theorem acCos_nonneg (ε Δ : ℝ) : 0 ≤ acCos ε Δ := Real.sqrt_nonneg _
private theorem acSin_nonneg (ε Δ : ℝ) : 0 ≤ acSin ε Δ := Real.sqrt_nonneg _

private theorem acCos_sin_identities {ε : ℝ} (hε : 0 < ε) (Δ : ℝ) :
    acCos ε Δ ^ 2 + acSin ε Δ ^ 2 = 1 ∧
    acRad ε Δ * (acCos ε Δ ^ 2 - acSin ε Δ ^ 2) = Δ ∧
    acRad ε Δ * (2 * acCos ε Δ * acSin ε Δ) = ε := by
  have hR_pos := acRad_pos hε Δ
  have habs := abs_div_acRad_lt_one hε Δ
  have hlt1 : Δ / acRad ε Δ < 1 := (le_abs_self Δ |>.trans_lt ((div_lt_one hR_pos).mp habs) |>
    (div_lt_one hR_pos).mpr)
  have hgt_neg1 : -1 < Δ / acRad ε Δ := by
    have hneg : -Δ ≤ |Δ| := neg_le_abs Δ
    have := hneg.trans_lt ((div_lt_one hR_pos).mp habs)
    exact (lt_div_iff₀ hR_pos).mpr (by linarith only [this])
  have hc_sq : acCos ε Δ ^ 2 = (1 + Δ / acRad ε Δ) / 2 :=
    Real.sq_sqrt (by linarith only [hgt_neg1])
  have hs_sq : acSin ε Δ ^ 2 = (1 - Δ / acRad ε Δ) / 2 :=
    Real.sq_sqrt (by linarith only [hlt1])
  refine ⟨by rw [hc_sq, hs_sq]; ring, ?_, ?_⟩
  · rw [hc_sq, hs_sq]
    have h1 : (1 + Δ / acRad ε Δ) / 2 - (1 - Δ / acRad ε Δ) / 2 = Δ / acRad ε Δ := by ring
    rw [h1, mul_div_cancel₀ _ hR_pos.ne']
  · have hprod_sq : (acRad ε Δ * (2 * acCos ε Δ * acSin ε Δ)) ^ 2 = ε ^ 2 := by
      have hmul_pow : (acRad ε Δ * (2 * acCos ε Δ * acSin ε Δ)) ^ 2 =
          (acRad ε Δ) ^ 2 * 4 * acCos ε Δ ^ 2 * acSin ε Δ ^ 2 := by ring
      rw [hmul_pow, hc_sq, hs_sq]
      have hR_sq : (acRad ε Δ) ^ 2 = Δ ^ 2 + ε ^ 2 := Real.sq_sqrt (by positivity)
      have halg : (acRad ε Δ) ^ 2 * 4 * ((1 + Δ / acRad ε Δ) / 2) * ((1 - Δ / acRad ε Δ) / 2) =
          (acRad ε Δ) ^ 2 - Δ ^ 2 := by
        field_simp [hR_pos.ne']; ring
      rw [halg, hR_sq]; ring
    have hnn : 0 ≤ acRad ε Δ * (2 * acCos ε Δ * acSin ε Δ) :=
      mul_nonneg hR_pos.le (mul_nonneg (mul_nonneg two_pos.le (acCos_nonneg ε Δ)) (acSin_nonneg ε Δ))
    exact (sq_eq_sq₀ hnn hε.le).mp hprod_sq

private def blkDiag {M : ℕ} (B : Fin M → Matrix Bool Bool ℂ) :
    Matrix (Bool × Fin M) (Bool × Fin M) ℂ :=
  fun p q => if p.2 = q.2 then B p.2 p.1 q.1 else 0

private theorem blkDiag_mul {M : ℕ} (A B : Fin M → Matrix Bool Bool ℂ) :
    blkDiag A * blkDiag B = blkDiag fun m => A m * B m := by
  ext ⟨b₁, m₁⟩ ⟨b₂, m₂⟩
  rw [Matrix.mul_apply, Fintype.sum_prod_type, Finset.sum_comm]
  by_cases hm : m₁ = m₂
  · subst hm
    rw [Finset.sum_eq_single m₁]
    · simp [blkDiag, Matrix.mul_apply]
    · intro m _ hne; simp [blkDiag, hne.symm]
    · simp
  · simp [blkDiag, hm]

private theorem blkDiag_conjTranspose {M : ℕ} (A : Fin M → Matrix Bool Bool ℂ) :
    (blkDiag A)ᴴ = blkDiag fun m => (A m)ᴴ := by
  ext ⟨b₁, m₁⟩ ⟨b₂, m₂⟩
  by_cases hm : m₁ = m₂ <;> simp [blkDiag, Matrix.conjTranspose_apply, hm, eq_comm]

private theorem blkDiag_one {M : ℕ} :
    blkDiag (fun _ : Fin M => (1 : Matrix Bool Bool ℂ)) = 1 := by
  ext ⟨b₁, m₁⟩ ⟨b₂, m₂⟩
  by_cases hm : m₁ = m₂
  · subst hm; simp [blkDiag, Matrix.one_apply, Prod.ext_iff]
  · simp [blkDiag, hm, Prod.ext_iff]

private theorem blkDiag_add {M : ℕ} (A B : Fin M → Matrix Bool Bool ℂ) :
    blkDiag A + blkDiag B = blkDiag fun m => A m + B m := by
  ext ⟨b₁, m₁⟩ ⟨b₂, m₂⟩
  by_cases hm : m₁ = m₂ <;> simp [blkDiag, hm]

private theorem blkDiag_sub {M : ℕ} (A B : Fin M → Matrix Bool Bool ℂ) :
    blkDiag A - blkDiag B = blkDiag fun m => A m - B m := by
  ext ⟨b₁, m₁⟩ ⟨b₂, m₂⟩
  by_cases hm : m₁ = m₂ <;> simp [blkDiag, hm]

private theorem blkDiag_smul {M : ℕ} (z : ℂ) (A : Fin M → Matrix Bool Bool ℂ) :
    z • blkDiag A = blkDiag fun m => z • A m := by
  ext ⟨b₁, m₁⟩ ⟨b₂, m₂⟩
  by_cases hm : m₁ = m₂ <;> simp [blkDiag, hm]

private def cfgSplitEquiv {N : ℕ} (hN : 2 ≤ N) : Config N ≃ Bool × Fin (2 ^ (N - 1)) :=
  let e_tail : (Fin (N - 1) → Bool) ≃ Fin (2 ^ (N - 1)) :=
    (Fintype.equivFin (Fin (N - 1) → Bool)).trans
      (finCongr (by simp [Fintype.card_fin, Fintype.card_bool]))
  let e_cons : Config N ≃ Bool × (Fin (N - 1) → Bool) :=
    { toFun := fun x => (x ⟨0, by omega⟩, fun j => x ⟨j.val + 1, by omega⟩)
      invFun := fun p i => if hi : i.val = 0 then p.1 else p.2 ⟨i.val - 1, by omega⟩
      left_inv := fun x => by
        funext i
        dsimp only
        by_cases hi : i.val = 0
        · rw [dif_pos hi]; congr 1; exact Fin.ext hi.symm
        · rw [dif_neg hi]; congr 1; exact Fin.ext (by dsimp only; omega)
      right_inv := fun ⟨b, y⟩ => by
        ext
        · simp
        · rename_i j; dsimp only; rw [dif_neg (Nat.succ_ne_zero j.val)]
          exact congrArg y (Fin.ext (by dsimp only; omega)) }
  e_cons.trans (Equiv.prodCongr (Equiv.refl Bool) e_tail)

private theorem reindex_l2_opNorm_le {α β : Type*} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] (e : α ≃ β) (A : Matrix α α ℂ) :
    ‖Matrix.reindex e e A‖ ≤ ‖A‖ := by
  rw [← Matrix.l2_opNorm_toEuclideanCLM, ← Matrix.l2_opNorm_toEuclideanCLM]
  refine (Matrix.toEuclideanCLM (n := β) (𝕜 := ℂ) (Matrix.reindex e e A)).opNorm_le_bound
    (ContinuousLinearMap.opNorm_nonneg _) fun ψ => ?_
  let pe : EuclideanSpace ℂ α := WithLp.toLp 2 (fun a => ψ.ofLp (e a))
  have hpe_norm : ‖pe‖ = ‖ψ‖ := by
    have hsq : ‖pe‖ ^ 2 = ‖ψ‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
      exact Fintype.sum_equiv e _ _ fun _ => rfl
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq
  have hact_norm : ‖Matrix.toEuclideanCLM (n := β) (𝕜 := ℂ) (Matrix.reindex e e A) ψ‖ =
      ‖Matrix.toEuclideanCLM (n := α) (𝕜 := ℂ) A pe‖ := by
    have hcoord (b : β) :
        (Matrix.toEuclideanCLM (n := β) (𝕜 := ℂ) (Matrix.reindex e e A) ψ).ofLp b =
          (Matrix.toEuclideanCLM (n := α) (𝕜 := ℂ) A pe).ofLp (e.symm b) := by
      rw [Matrix.ofLp_toEuclideanCLM, Matrix.ofLp_toEuclideanCLM]
      simp only [Matrix.mulVec, dotProduct, Matrix.reindex_apply, Matrix.submatrix_apply]
      exact (Fintype.sum_equiv e _ _ fun a => by simp [pe]).symm
    have hsq : ‖Matrix.toEuclideanCLM (n := β) (𝕜 := ℂ) (Matrix.reindex e e A) ψ‖ ^ 2 =
        ‖Matrix.toEuclideanCLM (n := α) (𝕜 := ℂ) A pe‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
      refine Fintype.sum_equiv e.symm _ _ fun b => ?_
      change ‖(Matrix.toEuclideanCLM (n := β) (𝕜 := ℂ) (Matrix.reindex e e A) ψ).ofLp b‖ ^ 2 =
        ‖(Matrix.toEuclideanCLM (n := α) (𝕜 := ℂ) A pe).ofLp (e.symm b)‖ ^ 2
      rw [hcoord b]
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq
  rw [hact_norm, ← hpe_norm]
  exact (Matrix.toEuclideanCLM (n := α) (𝕜 := ℂ) A).le_opNorm pe

private theorem reindex_l2_opNorm_eq {α β : Type*} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] (e : α ≃ β) (A : Matrix α α ℂ) :
    ‖Matrix.reindex e e A‖ = ‖A‖ := by
  refine le_antisymm (reindex_l2_opNorm_le e A) ?_
  have hinv : Matrix.reindex e.symm e.symm (Matrix.reindex e e A) = A := by
    ext a₁ a₂; simp [Matrix.reindex_apply]
  simpa only [hinv] using reindex_l2_opNorm_le e.symm (Matrix.reindex e e A)

private def singleBlk {M : ℕ} (m : Fin M) (A : Matrix Bool Bool ℂ) :
    Matrix (Bool × Fin M) (Bool × Fin M) ℂ :=
  blkDiag fun m' => if m' = m then A else 0

private theorem singleBlk_l2_opNorm_eq {M : ℕ} (m : Fin M) (A : Matrix Bool Bool ℂ) :
    ‖singleBlk m A‖ = ‖A‖ := by
  rw [← Matrix.l2_opNorm_toEuclideanCLM, ← Matrix.l2_opNorm_toEuclideanCLM]
  let T_blk := Matrix.toEuclideanCLM (n := Bool × Fin M) (𝕜 := ℂ) (singleBlk m A)
  let T_loc := Matrix.toEuclideanCLM (n := Bool) (𝕜 := ℂ) A
  change ‖T_blk‖ = ‖T_loc‖
  refine le_antisymm ?_ ?_
  · refine T_blk.opNorm_le_bound (ContinuousLinearMap.opNorm_nonneg _) fun ψ => ?_
    let ψ_m : EuclideanSpace ℂ Bool := WithLp.toLp 2 (fun b => ψ.ofLp (b, m))
    have hcoord_eq (b : Bool) : (T_blk ψ).ofLp (b, m) = (T_loc ψ_m).ofLp b := by
      dsimp only [T_blk, T_loc]
      rw [Matrix.ofLp_toEuclideanCLM, Matrix.ofLp_toEuclideanCLM]
      simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type]
      rw [Finset.sum_comm, Finset.sum_eq_single m]
      · simp [singleBlk, blkDiag, ψ_m]
      · intro m' _ hne; simp [singleBlk, blkDiag, hne.symm]
      · simp
    have hcoord_ne (b : Bool) {m' : Fin M} (hne : m' ≠ m) : (T_blk ψ).ofLp (b, m') = 0 := by
      dsimp only [T_blk]
      rw [Matrix.ofLp_toEuclideanCLM]
      simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type]
      refine Finset.sum_eq_zero fun b' _ => Finset.sum_eq_zero fun m'' _ => ?_
      by_cases h1 : m' = m''
      · subst h1; simp [singleBlk, blkDiag, hne]
      · simp [singleBlk, blkDiag, h1]
    have hact_eq : ‖T_blk ψ‖ = ‖T_loc ψ_m‖ := by
      have hsq : ‖T_blk ψ‖ ^ 2 = ‖T_loc ψ_m‖ ^ 2 := by
        rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type, Finset.sum_comm,
          Finset.sum_eq_single m]
        · rw [EuclideanSpace.norm_sq_eq]
          refine Finset.sum_congr rfl fun b _ => ?_
          change ‖(T_blk ψ).ofLp (b, m)‖ ^ 2 = ‖(T_loc ψ_m).ofLp b‖ ^ 2
          rw [hcoord_eq b]
        · intro m' _ hne
          refine Finset.sum_eq_zero fun b _ => ?_
          change ‖(T_blk ψ).ofLp (b, m')‖ ^ 2 = 0
          rw [hcoord_ne b hne, norm_zero, zero_pow two_pos.ne']
        · simp
      exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq
    have hψm_le : ‖ψ_m‖ ≤ ‖ψ‖ := by
      have hsq : ‖ψ_m‖ ^ 2 ≤ ‖ψ‖ ^ 2 := by
        rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type,
          Finset.sum_comm]
        exact Finset.single_le_sum
          (f := fun m' : Fin M => ∑ b : Bool, ‖ψ.ofLp (b, m')‖ ^ 2)
          (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)
          (Finset.mem_univ m)
      exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq
    rw [hact_eq]
    exact (T_loc.le_opNorm ψ_m).trans
      (mul_le_mul_of_nonneg_left hψm_le (ContinuousLinearMap.opNorm_nonneg _))
  · refine T_loc.opNorm_le_bound (ContinuousLinearMap.opNorm_nonneg _) fun φ => ?_
    let ι_m : EuclideanSpace ℂ (Bool × Fin M) :=
      WithLp.toLp 2 (fun p => if p.2 = m then φ.ofLp p.1 else 0)
    have hι_norm : ‖ι_m‖ = ‖φ‖ := by
      have hsq : ‖ι_m‖ ^ 2 = ‖φ‖ ^ 2 := by
        rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type, Finset.sum_comm,
          Finset.sum_eq_single m, EuclideanSpace.norm_sq_eq]
        · refine Finset.sum_congr rfl fun b _ => ?_
          change ‖ι_m.ofLp (b, m)‖ ^ 2 = ‖φ.ofLp b‖ ^ 2
          simp [ι_m]
        · intro m' _ hne
          refine Finset.sum_eq_zero fun b _ => ?_
          change ‖ι_m.ofLp (b, m')‖ ^ 2 = 0
          simp [ι_m, hne]
        · simp
      exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq
    have hact_le : ‖T_loc φ‖ ≤ ‖T_blk ι_m‖ := by
      have hcoord (b : Bool) : (T_loc φ).ofLp b = (T_blk ι_m).ofLp (b, m) := by
        dsimp only [T_blk, T_loc]
        rw [Matrix.ofLp_toEuclideanCLM, Matrix.ofLp_toEuclideanCLM]
        simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type]
        rw [Finset.sum_comm, Finset.sum_eq_single m]
        · simp [singleBlk, blkDiag, ι_m]
        · intro m' _ hne; simp [singleBlk, blkDiag, hne.symm]
        · simp
      have hsq : ‖T_loc φ‖ ^ 2 ≤ ‖T_blk ι_m‖ ^ 2 := by
        rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type,
          Finset.sum_comm]
        have h1 : (∑ b : Bool, ‖(T_loc φ).ofLp b‖ ^ 2) =
            ∑ b : Bool, ‖(T_blk ι_m).ofLp (b, m)‖ ^ 2 := by
          refine Finset.sum_congr rfl fun b _ => ?_
          rw [hcoord b]
        change (∑ b : Bool, ‖(T_loc φ).ofLp b‖ ^ 2) ≤ _
        rw [h1]
        exact Finset.single_le_sum
          (f := fun m' : Fin M => ∑ b : Bool, ‖(T_blk ι_m).ofLp (b, m')‖ ^ 2)
          (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)
          (Finset.mem_univ m)
      exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq
    exact hact_le.trans ((T_blk.le_opNorm ι_m).trans_eq (by rw [hι_norm]))

private def pullSplit {N : ℕ} (hN : 2 ≤ N)
    (B : Matrix (Bool × Fin (2 ^ (N - 1))) (Bool × Fin (2 ^ (N - 1))) ℂ) : Register N :=
  Matrix.reindex (cfgSplitEquiv hN).symm (cfgSplitEquiv hN).symm B

private theorem pullSplit_mul {N : ℕ} (hN : 2 ≤ N)
    (A B : Matrix (Bool × Fin (2 ^ (N - 1))) (Bool × Fin (2 ^ (N - 1))) ℂ) :
    pullSplit hN (A * B) = pullSplit hN A * pullSplit hN B := by
  ext x y
  simp only [pullSplit, Matrix.mul_apply, Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.symm_symm]
  exact Fintype.sum_equiv (cfgSplitEquiv hN).symm _ _ fun p => by simp

private theorem pullSplit_star {N : ℕ} (hN : 2 ≤ N)
    (A : Matrix (Bool × Fin (2 ^ (N - 1))) (Bool × Fin (2 ^ (N - 1))) ℂ) :
    star (pullSplit hN A) = pullSplit hN Aᴴ := by
  ext x y
  simp [pullSplit, Matrix.conjTranspose_apply, Matrix.reindex_apply]

private theorem pullSplit_one {N : ℕ} (hN : 2 ≤ N) :
    pullSplit hN 1 = (1 : Register N) := by
  ext x y
  simp [pullSplit, Matrix.reindex_apply, Matrix.one_apply]

private theorem pullSplit_add {N : ℕ} (hN : 2 ≤ N)
    (A B : Matrix (Bool × Fin (2 ^ (N - 1))) (Bool × Fin (2 ^ (N - 1))) ℂ) :
    pullSplit hN (A + B) = pullSplit hN A + pullSplit hN B := by
  ext x y; simp [pullSplit, Matrix.reindex_apply]

private theorem pullSplit_sub {N : ℕ} (hN : 2 ≤ N)
    (A B : Matrix (Bool × Fin (2 ^ (N - 1))) (Bool × Fin (2 ^ (N - 1))) ℂ) :
    pullSplit hN (A - B) = pullSplit hN A - pullSplit hN B := by
  ext x y; simp [pullSplit, Matrix.reindex_apply]

private theorem pullSplit_smul {N : ℕ} (hN : 2 ≤ N) (z : ℂ)
    (A : Matrix (Bool × Fin (2 ^ (N - 1))) (Bool × Fin (2 ^ (N - 1))) ℂ) :
    pullSplit hN (z • A) = z • pullSplit hN A := by
  ext x y; simp [pullSplit, Matrix.reindex_apply]

private theorem pullSplit_norm {N : ℕ} (hN : 2 ≤ N)
    (A : Matrix (Bool × Fin (2 ^ (N - 1))) (Bool × Fin (2 ^ (N - 1))) ℂ) :
    ‖pullSplit hN A‖ = ‖A‖ :=
  reindex_l2_opNorm_eq (cfgSplitEquiv hN).symm A

private theorem pullSplit_diagonal {N : ℕ} (hN : 2 ≤ N)
    (d : Bool × Fin (2 ^ (N - 1)) → ℂ) :
    pullSplit hN (Matrix.diagonal d) = Matrix.diagonal (d ∘ cfgSplitEquiv hN) := by
  ext x y
  by_cases h : x = y
  · subst h; simp [pullSplit, Matrix.reindex_apply]
  · have hne : cfgSplitEquiv hN x ≠ cfgSplitEquiv hN y := (cfgSplitEquiv hN).injective.ne h
    simp [pullSplit, Matrix.reindex_apply, h, hne]

private def liftBlockState {N : ℕ} (hN : 2 ≤ N) (m : Fin (2 ^ (N - 1))) (φ : Bool → ℂ) :
    StateSpace N :=
  WithLp.toLp 2 fun x =>
    let p := cfgSplitEquiv hN x
    if p.2 = m then φ p.1 else 0

private theorem matAct_pullSplit_blkDiag_liftBlockState {N : ℕ} (hN : 2 ≤ N)
    (B : Fin (2 ^ (N - 1)) → Matrix Bool Bool ℂ) (m : Fin (2 ^ (N - 1))) (φ : Bool → ℂ) :
    matAct (pullSplit hN (blkDiag B)) (liftBlockState hN m φ) =
      liftBlockState hN m (B m *ᵥ φ) := by
  ext x
  change (pullSplit hN (blkDiag B) *ᵥ (liftBlockState hN m φ).ofLp) x =
    (liftBlockState hN m (B m *ᵥ φ)).ofLp x
  simp only [Matrix.mulVec, dotProduct, pullSplit, Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.symm_symm, liftBlockState]
  rw [Fintype.sum_equiv (cfgSplitEquiv hN) _
    (fun q : Bool × Fin (2 ^ (N - 1)) =>
      blkDiag B (cfgSplitEquiv hN x) q * (if q.2 = m then φ q.1 else 0))
    (fun y => rfl)]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  by_cases hm : (cfgSplitEquiv hN x).2 = m
  · rw [if_pos hm, Finset.sum_eq_single m]
    · simp [blkDiag, hm]
    · intro m' _ hne; simp [hne]
    · simp
  · rw [if_neg hm]
    refine Finset.sum_eq_zero fun m' _ => Finset.sum_eq_zero fun b' _ => ?_
    by_cases h1 : m' = m
    · subst h1; simp [blkDiag, hm]
    · simp [h1]

private theorem norm_sq_liftBlockState {N : ℕ} (hN : 2 ≤ N) (m : Fin (2 ^ (N - 1)))
    (φ : Bool → ℂ) :
    ‖liftBlockState hN m φ‖ ^ 2 = ‖φ false‖ ^ 2 + ‖φ true‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  refine (Fintype.sum_equiv (cfgSplitEquiv hN) _
    (fun q : Bool × Fin (2 ^ (N - 1)) => ‖if q.2 = m then φ q.1 else (0 : ℂ)‖ ^ 2)
    fun _ => rfl).trans ?_
  rw [Fintype.sum_prod_type, Finset.sum_comm, Finset.sum_eq_single m]
  · simp; ring
  · intro m' _ hne; simp [hne]
  · simp

private theorem onsiteZ0_eq_pullSplit {N : ℕ} (hN : 2 ≤ N) :
    finitePauliMatrix (fun s : Fin N => if s.val = 0 then some (2 : Fin 3) else none) =
      pullSplit hN (blkDiag fun _ => finiteQubitPauli 2) := by
  ext x y
  simp only [finitePauliMatrix, pullSplit, Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.symm_symm, blkDiag]
  have hfst_x : (cfgSplitEquiv hN x).1 = x ⟨0, by omega⟩ := rfl
  have hfst_y : (cfgSplitEquiv hN y).1 = y ⟨0, by omega⟩ := rfl
  by_cases hm : (cfgSplitEquiv hN x).2 = (cfgSplitEquiv hN y).2
  · rw [if_pos hm, hfst_x, hfst_y]
    have htail_eq : (fun j : Fin (N - 1) => x ⟨j.val + 1, by omega⟩) =
        (fun j : Fin (N - 1) => y ⟨j.val + 1, by omega⟩) := by
      let e_tail : (Fin (N - 1) → Bool) ≃ Fin (2 ^ (N - 1)) :=
        (Fintype.equivFin (Fin (N - 1) → Bool)).trans
          (finCongr (by simp [Fintype.card_fin, Fintype.card_bool]))
      exact e_tail.injective hm
    rw [Finset.prod_eq_single (⟨0, by omega⟩ : Fin N)]
    · simp [boolPauliOptionEntry, boolPauliOption]
    · intro s _ hs0
      have hsv : s.val ≠ 0 := fun hv => hs0 (Fin.ext hv)
      let j : Fin (N - 1) := ⟨s.val - 1, by omega⟩
      have hs_eq : s = ⟨j.val + 1, by omega⟩ := Fin.ext (by dsimp [j]; omega)
      have hxy_s : x s = y s := by rw [hs_eq]; exact congrFun htail_eq j
      simp [hsv, boolPauliOptionEntry, boolPauliOption, Matrix.one_apply, hxy_s]
    · simp
  · rw [if_neg hm]
    have hnot_all : ¬ ∀ j : Fin (N - 1), x ⟨j.val + 1, by omega⟩ = y ⟨j.val + 1, by omega⟩ := by
      intro hall
      let e_tail : (Fin (N - 1) → Bool) ≃ Fin (2 ^ (N - 1)) :=
        (Fintype.equivFin (Fin (N - 1) → Bool)).trans
          (finCongr (by simp [Fintype.card_fin, Fintype.card_bool]))
      exact hm (congrArg e_tail (funext hall))
    push Not at hnot_all
    obtain ⟨j, hj_ne⟩ := hnot_all
    let s₀ : Fin N := ⟨j.val + 1, by omega⟩
    refine Finset.prod_eq_zero (Finset.mem_univ s₀) ?_
    simp [s₀, boolPauliOptionEntry, boolPauliOption, hj_ne]

/-! ### Explicit `2 × 2` avoided-crossing matrices on `Bool` -/

private def rot2 (c s : ℝ) : Matrix Bool Bool ℂ
  | false, false => c
  | false, true => -s
  | true, false => s
  | true, true => c

private def ham2 (c_off Δ ε : ℝ) : Matrix Bool Bool ℂ
  | false, false => c_off + Δ
  | false, true => ε
  | true, false => ε
  | true, true => c_off - Δ

private def refl2 (c s : ℝ) : Matrix Bool Bool ℂ
  | false, false => c ^ 2 - s ^ 2
  | false, true => 2 * c * s
  | true, false => 2 * c * s
  | true, true => s ^ 2 - c ^ 2

private def reflMinusUnit2 (c s : ℝ) : Matrix Bool Bool ℂ
  | false, false => c
  | false, true => s
  | true, false => s
  | true, true => -c

private def reflPlusUnit2 (c s : ℝ) : Matrix Bool Bool ℂ
  | false, false => -s
  | false, true => c
  | true, false => c
  | true, true => s

private def kato2 (ε Δ : ℝ) : Matrix Bool Bool ℂ :=
  (((-ε / (2 * acRad ε Δ ^ 2)) : ℝ) : ℂ) • finiteQubitPauli 1

private theorem rot2_unitary {c s : ℝ} (hcs : c ^ 2 + s ^ 2 = 1) :
    (rot2 c s)ᴴ * rot2 c s = 1 ∧ rot2 c s * (rot2 c s)ᴴ = 1 := by
  have hcsC : (c : ℂ) ^ 2 + (s : ℂ) ^ 2 = 1 := by exact_mod_cast hcs
  constructor <;> ext b₁ b₂ <;> cases b₁ <;> cases b₂ <;>
    simp only [rot2, Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_bool,
      Complex.star_def, Complex.conj_ofReal, map_neg, Matrix.one_apply, reduceCtorEq, if_true,
      if_false]
  · linear_combination hcsC
  · ring
  · ring
  · linear_combination hcsC
  · linear_combination hcsC
  · ring
  · ring
  · linear_combination hcsC

private theorem ham2_conjTranspose (c_off Δ ε : ℝ) :
    (ham2 c_off Δ ε)ᴴ = ham2 c_off Δ ε := by
  ext b₁ b₂; cases b₁ <;> cases b₂ <;>
    simp [ham2, Matrix.conjTranspose_apply, Complex.conj_ofReal]

private theorem kato2_conjTranspose (ε Δ : ℝ) :
    (kato2 ε Δ)ᴴ = kato2 ε Δ := by
  unfold kato2
  rw [Matrix.conjTranspose_smul, (finiteQubitPauli_isHermitian 1).eq]
  simp [Complex.conj_ofReal]

private theorem rot2_diag_ham2 {ε : ℝ} (hε : 0 < ε) (c_off Δ : ℝ) :
    let c := acCos ε Δ
    let s := acSin ε Δ
    let R := acRad ε Δ
    rot2 c s *
      Matrix.diagonal (fun b : Bool => if b then ((c_off - R : ℝ) : ℂ) else ((c_off + R : ℝ) : ℂ)) *
      (rot2 c s)ᴴ = ham2 c_off Δ ε := by
  intro c s R
  obtain ⟨hcs, hdiff, hprod⟩ := acCos_sin_identities hε Δ
  have hcsC : (c : ℂ) ^ 2 + (s : ℂ) ^ 2 = 1 := by exact_mod_cast hcs
  have hdiffC : (R : ℂ) * ((c : ℂ) ^ 2 - (s : ℂ) ^ 2) = (Δ : ℂ) := by exact_mod_cast hdiff
  have hprodC : (R : ℂ) * (2 * (c : ℂ) * (s : ℂ)) = (ε : ℂ) := by exact_mod_cast hprod
  ext b₁ b₂; cases b₁ <;> cases b₂ <;>
    simp only [rot2, ham2, Matrix.mul_apply, Matrix.diagonal_apply, Matrix.conjTranspose_apply,
      Fintype.sum_bool, Complex.star_def, Complex.conj_ofReal, map_neg, Bool.false_eq_true,
      if_true, if_false, reduceCtorEq] <;> push_cast
  · linear_combination (c_off : ℂ) * hcsC + hdiffC
  · linear_combination hprodC
  · linear_combination hprodC
  · linear_combination (c_off : ℂ) * hcsC - hdiffC

private theorem rot2_pauliZ2_conj (c s : ℝ) :
    rot2 c s * finiteQubitPauli 2 * (rot2 c s)ᴴ = refl2 c s := by
  ext b₁ b₂; cases b₁ <;> cases b₂ <;>
    simp only [rot2, refl2, finiteQubitPauli, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fintype.sum_bool, Complex.star_def, Complex.conj_ofReal, map_neg,
      show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide,
      if_true, if_false, reduceCtorEq] <;> ring

private theorem refl2_sub_neg_pauliZ2 {c s : ℝ} (hcs : c ^ 2 + s ^ 2 = 1) :
    refl2 c s - (-finiteQubitPauli 2) = ((2 * c : ℝ) : ℂ) • reflMinusUnit2 c s := by
  have hcsC : (c : ℂ) ^ 2 + (s : ℂ) ^ 2 = 1 := by exact_mod_cast hcs
  ext b₁ b₂; cases b₁ <;> cases b₂ <;>
    simp only [refl2, reflMinusUnit2, finiteQubitPauli, Matrix.sub_apply, Matrix.neg_apply,
      Matrix.smul_apply, smul_eq_mul,
      show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide,
      if_true, if_false, reduceCtorEq] <;> push_cast
  · linear_combination -hcsC
  · ring
  · ring
  · linear_combination hcsC

private theorem refl2_sub_pauliZ2 {c s : ℝ} (hcs : c ^ 2 + s ^ 2 = 1) :
    refl2 c s - finiteQubitPauli 2 = ((2 * s : ℝ) : ℂ) • reflPlusUnit2 c s := by
  have hcsC : (c : ℂ) ^ 2 + (s : ℂ) ^ 2 = 1 := by exact_mod_cast hcs
  ext b₁ b₂; cases b₁ <;> cases b₂ <;>
    simp only [refl2, reflPlusUnit2, finiteQubitPauli, Matrix.sub_apply, Matrix.smul_apply,
      smul_eq_mul, show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide,
      if_true, if_false, reduceCtorEq] <;> push_cast
  · linear_combination hcsC
  · ring
  · ring
  · linear_combination -hcsC

private theorem reflMinusUnit2_mem_unitary {c s : ℝ} (hcs : c ^ 2 + s ^ 2 = 1) :
    reflMinusUnit2 c s ∈ unitary (Matrix Bool Bool ℂ) := by
  have hcsC : (c : ℂ) ^ 2 + (s : ℂ) ^ 2 = 1 := by exact_mod_cast hcs
  rw [Unitary.mem_iff, Matrix.star_eq_conjTranspose]
  constructor <;> ext b₁ b₂ <;> cases b₁ <;> cases b₂ <;>
    simp only [reflMinusUnit2, Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_bool,
      Complex.star_def, Complex.conj_ofReal, map_neg, Matrix.one_apply, reduceCtorEq, if_true,
      if_false]
  · linear_combination hcsC
  · ring
  · ring
  · linear_combination hcsC
  · linear_combination hcsC
  · ring
  · ring
  · linear_combination hcsC

private theorem reflPlusUnit2_mem_unitary {c s : ℝ} (hcs : c ^ 2 + s ^ 2 = 1) :
    reflPlusUnit2 c s ∈ unitary (Matrix Bool Bool ℂ) := by
  have hcsC : (c : ℂ) ^ 2 + (s : ℂ) ^ 2 = 1 := by exact_mod_cast hcs
  rw [Unitary.mem_iff, Matrix.star_eq_conjTranspose]
  constructor <;> ext b₁ b₂ <;> cases b₁ <;> cases b₂ <;>
    simp only [reflPlusUnit2, Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_bool,
      Complex.star_def, Complex.conj_ofReal, map_neg, Matrix.one_apply, reduceCtorEq, if_true,
      if_false]
  · linear_combination hcsC
  · ring
  · ring
  · linear_combination hcsC
  · linear_combination hcsC
  · ring
  · ring
  · linear_combination hcsC

private theorem norm_refl2_sub_neg_pauliZ2 {ε : ℝ} (hε : 0 < ε) (Δ : ℝ) :
    ‖refl2 (acCos ε Δ) (acSin ε Δ) - (-finiteQubitPauli 2)‖ = 2 * acCos ε Δ := by
  have hcs := (acCos_sin_identities hε Δ).1
  rw [refl2_sub_neg_pauliZ2 hcs, norm_smul,
    CStarRing.norm_of_mem_unitary (reflMinusUnit2_mem_unitary hcs), mul_one,
    Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg two_pos.le (acCos_nonneg ε Δ))]

private theorem norm_refl2_sub_pauliZ2 {ε : ℝ} (hε : 0 < ε) (Δ : ℝ) :
    ‖refl2 (acCos ε Δ) (acSin ε Δ) - finiteQubitPauli 2‖ = 2 * acSin ε Δ := by
  have hcs := (acCos_sin_identities hε Δ).1
  rw [refl2_sub_pauliZ2 hcs, norm_smul,
    CStarRing.norm_of_mem_unitary (reflPlusUnit2_mem_unitary hcs), mul_one,
    Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg two_pos.le (acSin_nonneg ε Δ))]

private theorem kato2_commutator_eq {ε : ℝ} (hε : 0 < ε) (c_off Δ : ℝ) :
    let V₂ := rot2 (acCos ε Δ) (acSin ε Δ)
    (-Complex.I) • (kato2 ε Δ * ham2 c_off Δ ε - ham2 c_off Δ ε * kato2 ε Δ) =
      finiteQubitPauli 2 -
        V₂ * Matrix.diagonal (fun b : Bool => (V₂ᴴ * finiteQubitPauli 2 * V₂) b b) * V₂ᴴ := by
  intro V₂
  obtain ⟨_, hdiff, hprod⟩ := acCos_sin_identities hε Δ
  have hR_pos := acRad_pos hε Δ
  have hR_ne : (acRad ε Δ : ℂ) ≠ 0 := by exact_mod_cast hR_pos.ne'
  have hR_sq : (acRad ε Δ : ℂ) ^ 2 = (Δ : ℂ) ^ 2 + (ε : ℂ) ^ 2 := by
    exact_mod_cast Real.sq_sqrt (by positivity : 0 ≤ Δ ^ 2 + ε ^ 2)
  have hdiffC : (acRad ε Δ : ℂ) * ((acCos ε Δ : ℂ) ^ 2 - (acSin ε Δ : ℂ) ^ 2) = (Δ : ℂ) := by
    exact_mod_cast hdiff
  have hprodC : (acRad ε Δ : ℂ) * (2 * (acCos ε Δ : ℂ) * (acSin ε Δ : ℂ)) = (ε : ℂ) := by
    exact_mod_cast hprod
  have hdiag_eq : Matrix.diagonal (fun b : Bool => (V₂ᴴ * finiteQubitPauli 2 * V₂) b b) =
      (((Δ / acRad ε Δ : ℝ) : ℂ)) • finiteQubitPauli 2 := by
    ext b₁ b₂; cases b₁ <;> cases b₂ <;>
      simp only [V₂, rot2, finiteQubitPauli, Matrix.diagonal_apply, Matrix.mul_apply,
        Matrix.conjTranspose_apply, Matrix.smul_apply, smul_eq_mul, Fintype.sum_bool,
        Complex.star_def, Complex.conj_ofReal, map_neg,
        show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide,
        if_true, if_false, reduceCtorEq] <;> push_cast
    · field_simp [hR_ne]; linear_combination hdiffC
    · ring
    · ring
    · field_simp [hR_ne]; linear_combination -hdiffC
  rw [hdiag_eq, Matrix.mul_smul, Matrix.smul_mul, rot2_pauliZ2_conj]
  unfold kato2
  ext b₁ b₂; cases b₁ <;> cases b₂ <;>
    simp only [ham2, refl2, finiteQubitPauli,
      Matrix.smul_apply, Matrix.sub_apply, Matrix.mul_apply, Fintype.sum_bool, smul_eq_mul,
      show (1 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 0 by decide,
      show (2 : Fin 3) ≠ 1 by decide,
      if_true, if_false, reduceCtorEq, Bool.false_eq_true] <;>
    push_cast <;> field_simp [hR_ne] <;> ring_nf <;>
    simp only [Complex.I_sq, hR_sq]
  · linear_combination 2 * (Δ : ℂ) * hdiffC
  · linear_combination 2 * (Δ : ℂ) * hprodC
  · linear_combination 2 * (Δ : ℂ) * hprodC
  · linear_combination -2 * (Δ : ℂ) * hdiffC

/-! ### Closed-form `1 / 10` crossing values and far-block decay -/

private theorem ac_values_at_crossings {ε : ℝ} (hε : 0 < ε) :
    let δc := 199 / Real.sqrt 399 * ε
    (acCos ε (-δc) = 1 / 20 ∧ acSin ε (-δc) = Real.sqrt 399 / 20) ∧
    (acCos ε δc = Real.sqrt 399 / 20 ∧ acSin ε δc = 1 / 20) ∧
    (2 * acCos ε 0 = Real.sqrt 2 ∧ 2 * acSin ε 0 = Real.sqrt 2) ∧
    δc < 40 * ε := by
  intro δc
  have hδc_def : δc = 199 / Real.sqrt 399 * ε := rfl
  have h399_pos : (0 : ℝ) < Real.sqrt 399 := Real.sqrt_pos.mpr (by norm_num)
  have hsq399 : Real.sqrt 399 ^ 2 = 399 := Real.sq_sqrt (by norm_num)
  have hrad_eq (s_sgn : ℝ) (hs_sq : s_sgn ^ 2 = 1) :
      acRad ε (s_sgn * δc) = 200 / Real.sqrt 399 * ε := by
    unfold acRad
    have h1 : (s_sgn * δc) ^ 2 + ε ^ 2 = (200 / Real.sqrt 399 * ε) ^ 2 := by
      rw [hδc_def]
      field_simp [h399_pos.ne']
      ring_nf
      simp only [hs_sq, hsq399]
      ring
    rw [h1, Real.sqrt_sq (by positivity)]
  have hrad_neg : acRad ε (-δc) = 200 / Real.sqrt 399 * ε := by
    simpa using hrad_eq (-1) (by norm_num)
  have hrad_pos : acRad ε δc = 200 / Real.sqrt 399 * ε := by
    simpa using hrad_eq 1 (by norm_num)
  have hdiv_neg : (-δc) / acRad ε (-δc) = -199 / 200 := by
    rw [hrad_neg, hδc_def]; field_simp [hε.ne', h399_pos.ne']
  have hdiv_pos : δc / acRad ε δc = 199 / 200 := by
    rw [hrad_pos, hδc_def]; field_simp [hε.ne', h399_pos.ne']
  have hcos_neg : acCos ε (-δc) = 1 / 20 := by
    unfold acCos; rw [hdiv_neg]
    have h1 : (1 + -199 / 200 : ℝ) / 2 = (1 / 20 : ℝ) ^ 2 := by norm_num
    rw [h1, Real.sqrt_sq (by norm_num)]
  have hsin_neg : acSin ε (-δc) = Real.sqrt 399 / 20 := by
    unfold acSin; rw [hdiv_neg]
    have h1 : (1 - -199 / 200 : ℝ) / 2 = (Real.sqrt 399 / 20) ^ 2 := by
      rw [div_pow, hsq399]; norm_num
    rw [h1, Real.sqrt_sq (by positivity)]
  have hcos_pos : acCos ε δc = Real.sqrt 399 / 20 := by
    unfold acCos; rw [hdiv_pos]
    have h1 : (1 + 199 / 200 : ℝ) / 2 = (Real.sqrt 399 / 20) ^ 2 := by
      rw [div_pow, hsq399]; norm_num
    rw [h1, Real.sqrt_sq (by positivity)]
  have hsin_pos : acSin ε δc = 1 / 20 := by
    unfold acSin; rw [hdiv_pos]
    have h1 : (1 - 199 / 200 : ℝ) / 2 = (1 / 20 : ℝ) ^ 2 := by norm_num
    rw [h1, Real.sqrt_sq (by norm_num)]
  have hzero : 2 * acCos ε 0 = Real.sqrt 2 ∧ 2 * acSin ε 0 = Real.sqrt 2 := by
    have hhalf : 2 * Real.sqrt (1 / 2 : ℝ) = Real.sqrt 2 := by
      have hsq : (2 * Real.sqrt (1 / 2 : ℝ)) ^ 2 = (Real.sqrt 2) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (by norm_num), Real.sq_sqrt (by norm_num)]; norm_num
      exact (sq_eq_sq₀ (by positivity) (by positivity)).mp hsq
    unfold acCos acSin
    simp only [zero_div, add_zero, sub_zero, hhalf, and_self]
  have hδc_lt : δc < 40 * ε := by
    rw [hδc_def]
    have h19 : (19 : ℝ) < Real.sqrt 399 := by
      rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 19)]
      exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    have hfrac : 199 / Real.sqrt 399 < 40 := by
      rw [div_lt_iff₀ h399_pos]
      linarith only [h19]
    exact mul_lt_mul_of_pos_right hfrac hε
  exact ⟨⟨hcos_neg, hsin_neg⟩, ⟨hcos_pos, hsin_pos⟩, hzero, hδc_lt⟩

private theorem min_two_acCos_acSin_lt_of_two_le_abs {Δ : ℝ} (hΔ : 2 ≤ |Δ|) :
    min (2 * acCos (1 / 40) Δ) (2 * acSin (1 / 40) Δ) < 1 / 20 := by
  have hε : (0 : ℝ) < 1 / 40 := by norm_num
  have hR_pos := acRad_pos hε Δ
  have habs := abs_div_acRad_lt_one hε Δ
  have hR_sq : acRad (1 / 40) Δ ^ 2 = Δ ^ 2 + (1 / 40 : ℝ) ^ 2 := Real.sq_sqrt (by positivity)
  have hΔ_sq : 4 ≤ Δ ^ 2 := by
    have h1 := pow_le_pow_left₀ (by norm_num) hΔ 2
    rw [sq_abs] at h1
    linarith only [h1]
  have hR_ge4 : 4 < acRad (1 / 40) Δ ^ 2 := by linarith only [hR_sq, hΔ_sq]
  rcases le_total Δ 0 with hneg | hpos
  · refine lt_of_le_of_lt (min_le_left _ _) ?_
    have hgt_neg1 : -1 < Δ / acRad (1 / 40) Δ := by
      have := (neg_le_abs Δ).trans_lt ((div_lt_one hR_pos).mp habs)
      exact (lt_div_iff₀ hR_pos).mpr (by linarith only [this])
    have hc_sq : acCos (1 / 40) Δ ^ 2 = (1 + Δ / acRad (1 / 40) Δ) / 2 :=
      Real.sq_sqrt (by linarith only [hgt_neg1])
    have h1_ge : 1 ≤ 1 - Δ / acRad (1 / 40) Δ := by
      have : Δ / acRad (1 / 40) Δ ≤ 0 := div_nonpos_of_nonpos_of_nonneg hneg hR_pos.le
      linarith only [this]
    have hprod_id : 4 * acCos (1 / 40) Δ ^ 2 * (1 - Δ / acRad (1 / 40) Δ) =
        2 * (1 / 40 : ℝ) ^ 2 / acRad (1 / 40) Δ ^ 2 := by
      rw [hc_sq]; field_simp [hR_pos.ne']; ring_nf; simp only [hR_sq]; ring
    have hsq_lt : (2 * acCos (1 / 40) Δ) ^ 2 < (1 / 20 : ℝ) ^ 2 := by
      have hle : (2 * acCos (1 / 40) Δ) ^ 2 ≤
          4 * acCos (1 / 40) Δ ^ 2 * (1 - Δ / acRad (1 / 40) Δ) := by
        nlinarith only [h1_ge, sq_nonneg (acCos (1 / 40) Δ)]
      rw [hprod_id] at hle
      have hdiv_lt : 2 * (1 / 40 : ℝ) ^ 2 / acRad (1 / 40) Δ ^ 2 < (1 / 20 : ℝ) ^ 2 := by
        rw [div_lt_iff₀ (sq_pos_of_pos hR_pos)]
        nlinarith only [hR_ge4]
      exact hle.trans_lt hdiv_lt
    nlinarith only [hsq_lt, acCos_nonneg (1 / 40) Δ]
  · refine lt_of_le_of_lt (min_le_right _ _) ?_
    have hlt1 : Δ / acRad (1 / 40) Δ < 1 :=
      (le_abs_self Δ |>.trans_lt ((div_lt_one hR_pos).mp habs) |> (div_lt_one hR_pos).mpr)
    have hs_sq : acSin (1 / 40) Δ ^ 2 = (1 - Δ / acRad (1 / 40) Δ) / 2 :=
      Real.sq_sqrt (by linarith only [hlt1])
    have h1_ge : 1 ≤ 1 + Δ / acRad (1 / 40) Δ := by
      have : 0 ≤ Δ / acRad (1 / 40) Δ := div_nonneg hpos hR_pos.le
      linarith only [this]
    have hprod_id : 4 * acSin (1 / 40) Δ ^ 2 * (1 + Δ / acRad (1 / 40) Δ) =
        2 * (1 / 40 : ℝ) ^ 2 / acRad (1 / 40) Δ ^ 2 := by
      rw [hs_sq]; field_simp [hR_pos.ne']; ring_nf; simp only [hR_sq]; ring
    have hsq_lt : (2 * acSin (1 / 40) Δ) ^ 2 < (1 / 20 : ℝ) ^ 2 := by
      have hle : (2 * acSin (1 / 40) Δ) ^ 2 ≤
          4 * acSin (1 / 40) Δ ^ 2 * (1 + Δ / acRad (1 / 40) Δ) := by
        nlinarith only [h1_ge, sq_nonneg (acSin (1 / 40) Δ)]
      rw [hprod_id] at hle
      have hdiv_lt : 2 * (1 / 40 : ℝ) ^ 2 / acRad (1 / 40) Δ ^ 2 < (1 / 20 : ℝ) ^ 2 := by
        rw [div_lt_iff₀ (sq_pos_of_pos hR_pos)]
        nlinarith only [hR_ge4]
      exact hle.trans_lt hdiv_lt
    nlinarith only [hsq_lt, acSin_nonneg (1 / 40) Δ]

/-! ### Super-polynomial (`2^(N - 1)`) active-saddle switches and sign reversals on `H₀ + t Z₀` -/

/-- Along the physical single-site Pauli perturbation pencil `H(t) = H₀ + t Z₀` (`N ≥ 2`), an
explicit self-adjoint base `H₀` exhibits:
1. strictly simple spectrum (`|E_x(t) - E_y(t)| ≥ 1 / 20` for `x ≠ y`) across `[0, 4 * 2^(N - 1)]`
   with smooth unitary eigenframe `V(t)` and exact Kato connection `K(t)` solving
   `-i [K(t), H(t)] = Z₀ - diag_{V(t)}(Z₀)`,
2. `2^(N - 1)` spectral-torus points `θ_branch m : Fin (2^N - 1) → UnitAddCircle` and unitary
   targets `W_minus m, W_plus m ∈ U(2^N)` whose active `1 / 10` saddle switches strictly from
   `W_minus m` at `t_minus m` to `W_plus m` at `t_plus m` inside `(4 m, 4 m + 4)`,
3. `2^N` exact `1 / 10` crossings of the global envelope
   `G(t) = sup_m min(‖U_m(t) - W_{m,-}‖, ‖U_m(t) - W_{m,+}‖)` (`G(4 k) < 1 / 20`,
   `G(t_minus m) = 1 / 10`, `G(4 m + 2) = √2`, `G(t_plus m) = 1 / 10`), and
4. explicit unitary-ratio singular eigenmodes `ψ_minus m, ψ_plus m` at `r_⋆ = 1 / 10` (`β = √399 / 200`)
   on which `Re ⟨U_m ψ, K(t) U_m ψ⟩ - Re ⟨ψ, K(t) ψ⟩` flips strictly from `> 0` at `t_minus m` to
   `< 0` at `t_plus m` across all `2^(N - 1)` avoided crossings. -/
theorem pauliPencil_exponential_saddle_switches {N : ℕ} (hN : 2 ≤ N) :
    let M := 2 ^ (N - 1)
    let d := 2 ^ N - 1
    let Z₀ : Register N := finitePauliMatrix (fun s : Fin N => if s.val = 0 then some (2 : Fin 3) else none)
    ∃ (e_enum : Config N ≃ Fin (d + 1))
      (H₀ : selfAdjoint (Register N))
      (V : ℝ → UGroup N)
      (E : ℝ → Config N → ℝ)
      (K : ℝ → selfAdjoint (Register N))
      (θ_branch : Fin M → Fin d → UnitAddCircle)
      (W_minus W_plus : Fin M → UGroup N)
      (t_minus t_plus : Fin M → ℝ)
      (ψ_minus ψ_plus : Fin M → StateSpace N),
      -- (1) Spectral decomposition, uniform gap ≥ 1/20 on [0, 4 M], and exact Kato equation
      (∀ t : ℝ,
        H₀.val + (t : ℂ) • Z₀ =
          (V t).val * Matrix.diagonal (Complex.ofReal ∘ E t) * star (V t).val ∧
        (-Complex.I) • ((K t).val * (H₀.val + (t : ℂ) • Z₀) -
            (H₀.val + (t : ℂ) • Z₀) * (K t).val) =
          Z₀ - (V t).val *
            Matrix.diagonal (fun x => (star (V t).val * Z₀ * (V t).val) x x) * star (V t).val) ∧
      (∀ t ∈ Icc (0 : ℝ) (4 * (M : ℝ)), ∀ x y : Config N, x ≠ y →
        (1 / 20 : ℝ) ≤ |E t x - E t y|) ∧
      -- (2) Ordered disjoint crossing windows and strict W_minus → W_plus saddle switches
      (∀ m : Fin M,
        let U_minus := projectiveSpectralMatrix e_enum (V (t_minus m)) (θ_branch m)
        let U_plus := projectiveSpectralMatrix e_enum (V (t_plus m)) (θ_branch m)
        4 * (m.val : ℝ) < t_minus m ∧ t_minus m < 4 * (m.val : ℝ) + 2 ∧
        4 * (m.val : ℝ) + 2 < t_plus m ∧ t_plus m < 4 * (m.val : ℝ) + 4 ∧
        ‖U_minus - (W_minus m).val‖ = 1 / 10 ∧ (1 / 10 : ℝ) < ‖U_minus - (W_plus m).val‖ ∧
        ‖U_plus - (W_plus m).val‖ = 1 / 10 ∧ (1 / 10 : ℝ) < ‖U_plus - (W_minus m).val‖) ∧
      -- (3) Global min-max envelope oscillates 2^N times across 1/10 on [0, 4 M]
      (let G : ℝ → ℝ := fun t =>
        Finset.univ.sup' ⟨⟨0, Nat.two_pow_pos (N - 1)⟩, Finset.mem_univ _⟩ fun m : Fin M =>
          min ‖projectiveSpectralMatrix e_enum (V t) (θ_branch m) - (W_minus m).val‖
              ‖projectiveSpectralMatrix e_enum (V t) (θ_branch m) - (W_plus m).val‖
       (∀ k : Fin (M + 1), G (4 * (k.val : ℝ)) < 1 / 20) ∧
       (∀ m : Fin M,
         G (t_minus m) = 1 / 10 ∧ G (4 * (m.val : ℝ) + 2) = Real.sqrt 2 ∧
         G (t_plus m) = 1 / 10)) ∧
      -- (4) Unitary-ratio singular eigenmodes and 2^(N - 1) strict sign reversals
      (let β : ℝ := Real.sqrt 399 / 200
       ∀ m : Fin M,
        let U_minus := projectiveSpectralMatrix e_enum (V (t_minus m)) (θ_branch m)
        let U_plus := projectiveSpectralMatrix e_enum (V (t_plus m)) (θ_branch m)
        ψ_minus m ∈ maxRightSingularSphere (U_minus - (W_minus m).val) ∧
        matAct (W_minus m).val (ψ_minus m) =
          (((1 - (1 / 10 : ℝ) ^ 2 / 2 : ℝ) : ℂ) + Complex.I * (β : ℂ)) •
            matAct U_minus (ψ_minus m) ∧
        0 < (inner ℂ (matAct U_minus (ψ_minus m))
              (matAct (K (t_minus m)).val (matAct U_minus (ψ_minus m)))).re -
            (inner ℂ (ψ_minus m) (matAct (K (t_minus m)).val (ψ_minus m))).re ∧
        ψ_plus m ∈ maxRightSingularSphere (U_plus - (W_plus m).val) ∧
        matAct (W_plus m).val (ψ_plus m) =
          (((1 - (1 / 10 : ℝ) ^ 2 / 2 : ℝ) : ℂ) + Complex.I * (β : ℂ)) •
            matAct U_plus (ψ_plus m) ∧
        (inner ℂ (matAct U_plus (ψ_plus m))
              (matAct (K (t_plus m)).val (matAct U_plus (ψ_plus m)))).re -
            (inner ℂ (ψ_plus m) (matAct (K (t_plus m)).val (ψ_plus m))).re < 0) := by
  intro M d Z₀
  have hM_pos : 0 < M := Nat.two_pow_pos (N - 1)
  let ε : ℝ := 1 / 40
  have hε : 0 < ε := by norm_num
  -- 1. Zero-anchored enumeration placing `(false, 0)` at `0 : Fin (d + 1)`
  have hd_card : Fintype.card (Config N) = d + 1 := by
    simp only [Config, Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]
    have h2N : 0 < 2 ^ N := Nat.two_pow_pos N
    dsimp [d]; omega
  let e_raw : Config N ≃ Fin (d + 1) := (Fintype.equivFin (Config N)).trans (finCongr hd_card)
  let c_anchor : Config N := (cfgSplitEquiv hN).symm (false, ⟨0, hM_pos⟩)
  let e_enum : Config N ≃ Fin (d + 1) := e_raw.trans (Equiv.swap (e_raw c_anchor) 0)
  have he_anchor : e_enum c_anchor = 0 := by
    dsimp [e_enum]; exact Equiv.swap_apply_left _ _
  -- 2. Block parameters, H₀, V(t), E(t), K(t), θ_branch, W_minus, W_plus, t_minus, t_plus, ψ_±
  let t_center (m : Fin M) : ℝ := 4 * (m.val : ℝ) + 2
  let c_offset (m : Fin M) : ℝ := (8 * (M : ℝ) + 10) * (m.val : ℝ)
  let H₀_mat : Register N :=
    pullSplit hN (blkDiag fun m => ham2 (c_offset m) (-t_center m) ε)
  have hH₀_sa : H₀_mat ∈ selfAdjoint (Register N) := by
    rw [selfAdjoint.mem_iff, pullSplit_star, blkDiag_conjTranspose]
    simp_rw [ham2_conjTranspose]; rfl
  let H₀ : selfAdjoint (Register N) := ⟨H₀_mat, hH₀_sa⟩
  let V_mat (t : ℝ) : Register N :=
    pullSplit hN (blkDiag fun m => rot2 (acCos ε (t - t_center m)) (acSin ε (t - t_center m)))
  have hV_unit (t : ℝ) : V_mat t ∈ unitary (Register N) := by
    rw [Unitary.mem_iff]
    dsimp [V_mat]
    rw [pullSplit_star, ← pullSplit_mul, ← pullSplit_mul, blkDiag_conjTranspose,
      blkDiag_mul, blkDiag_mul]
    have h1 : (fun m : Fin M =>
        (rot2 (acCos ε (t - t_center m)) (acSin ε (t - t_center m)))ᴴ *
          rot2 (acCos ε (t - t_center m)) (acSin ε (t - t_center m))) = fun _ => 1 :=
      funext fun m => (rot2_unitary (acCos_sin_identities hε (t - t_center m)).1).1
    have h2 : (fun m : Fin M =>
        rot2 (acCos ε (t - t_center m)) (acSin ε (t - t_center m)) *
          (rot2 (acCos ε (t - t_center m)) (acSin ε (t - t_center m)))ᴴ) = fun _ => 1 :=
      funext fun m => (rot2_unitary (acCos_sin_identities hε (t - t_center m)).1).2
    rw [h1, h2, blkDiag_one, pullSplit_one]
    exact ⟨rfl, rfl⟩
  let V (t : ℝ) : UGroup N := ⟨V_mat t, hV_unit t⟩
  let E_split (t : ℝ) : Bool × Fin M → ℝ := fun p =>
    if p.1 then c_offset p.2 - acRad ε (t - t_center p.2)
    else c_offset p.2 + acRad ε (t - t_center p.2)
  let E (t : ℝ) : Config N → ℝ := E_split t ∘ cfgSplitEquiv hN
  let K (t : ℝ) : selfAdjoint (Register N) :=
    ⟨pullSplit hN (blkDiag fun m => kato2 ε (t - t_center m)), by
      rw [selfAdjoint.mem_iff, pullSplit_star, blkDiag_conjTranspose]
      simp_rw [kato2_conjTranspose]⟩
  let c_true (m : Fin M) : Config N := (cfgSplitEquiv hN).symm (true, m)
  let x_bool (m : Fin M) : Fin d → Bool := fun i => decide (i.succ = e_enum (c_true m))
  let θ_branch (m : Fin M) : Fin d → UnitAddCircle := anchoredBooleanProjectivePhase (x_bool m)
  let W_minus_blk (m : Fin M) : Fin M → Matrix Bool Bool ℂ :=
    fun m' => if m' = m then -finiteQubitPauli 2 else 1
  let W_plus_blk (m : Fin M) : Fin M → Matrix Bool Bool ℂ :=
    fun m' => if m' = m then finiteQubitPauli 2 else 1
  have hZ2_sq : (finiteQubitPauli 2)ᴴ * finiteQubitPauli 2 = 1 ∧
      finiteQubitPauli 2 * (finiteQubitPauli 2)ᴴ = 1 := by
    rw [(finiteQubitPauli_isHermitian 2).eq]
    constructor <;> ext b₁ b₂ <;> cases b₁ <;> cases b₂ <;>
      simp [finiteQubitPauli, Matrix.mul_apply,
        show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide]
  have hW_minus_unit (m : Fin M) : pullSplit hN (blkDiag (W_minus_blk m)) ∈ unitary (Register N) := by
    rw [Unitary.mem_iff, pullSplit_star, ← pullSplit_mul, ← pullSplit_mul,
      blkDiag_conjTranspose, blkDiag_mul, blkDiag_mul]
    have h1 : (fun m' => (W_minus_blk m m')ᴴ * W_minus_blk m m') = fun _ => 1 := by
      funext m'; dsimp [W_minus_blk]; split_ifs
      · rw [Matrix.conjTranspose_neg, neg_mul_neg, hZ2_sq.1]
      · simp
    have h2 : (fun m' => W_minus_blk m m' * (W_minus_blk m m')ᴴ) = fun _ => 1 := by
      funext m'; dsimp [W_minus_blk]; split_ifs
      · rw [Matrix.conjTranspose_neg, mul_neg, neg_mul, neg_neg, hZ2_sq.2]
      · simp
    rw [h1, h2, blkDiag_one, pullSplit_one]; exact ⟨rfl, rfl⟩
  have hW_plus_unit (m : Fin M) : pullSplit hN (blkDiag (W_plus_blk m)) ∈ unitary (Register N) := by
    rw [Unitary.mem_iff, pullSplit_star, ← pullSplit_mul, ← pullSplit_mul,
      blkDiag_conjTranspose, blkDiag_mul, blkDiag_mul]
    have h1 : (fun m' => (W_plus_blk m m')ᴴ * W_plus_blk m m') = fun _ => 1 := by
      funext m'; dsimp [W_plus_blk]; split_ifs
      · exact hZ2_sq.1
      · simp
    have h2 : (fun m' => W_plus_blk m m' * (W_plus_blk m m')ᴴ) = fun _ => 1 := by
      funext m'; dsimp [W_plus_blk]; split_ifs
      · exact hZ2_sq.2
      · simp
    rw [h1, h2, blkDiag_one, pullSplit_one]; exact ⟨rfl, rfl⟩
  let W_minus (m : Fin M) : UGroup N := ⟨pullSplit hN (blkDiag (W_minus_blk m)), hW_minus_unit m⟩
  let W_plus (m : Fin M) : UGroup N := ⟨pullSplit hN (blkDiag (W_plus_blk m)), hW_plus_unit m⟩
  let δc : ℝ := 199 / Real.sqrt 399 * ε
  let t_minus (m : Fin M) : ℝ := t_center m - δc
  let t_plus (m : Fin M) : ℝ := t_center m + δc
  let invSqrt2 : ℂ := ((Real.sqrt 2)⁻¹ : ℝ)
  let φ_minus : Bool → ℂ := fun b => if b then Complex.I * invSqrt2 else invSqrt2
  let φ_plus : Bool → ℂ := fun b => if b then -Complex.I * invSqrt2 else invSqrt2
  let ψ_minus (m : Fin M) : StateSpace N := liftBlockState hN m φ_minus
  let ψ_plus (m : Fin M) : StateSpace N := liftBlockState hN m φ_plus
  -- Key structural reduction for H(t) and projectiveSpectralMatrix
  have hZ₀_eq : Z₀ = pullSplit hN (blkDiag fun _ => finiteQubitPauli 2) := onsiteZ0_eq_pullSplit hN
  have hHt_eq (t : ℝ) : H₀.val + (t : ℂ) • Z₀ =
      pullSplit hN (blkDiag fun m => ham2 (c_offset m) (t - t_center m) ε) := by
    change H₀_mat + (t : ℂ) • Z₀ = _
    rw [hZ₀_eq, ← pullSplit_smul, ← pullSplit_add, blkDiag_smul, blkDiag_add]
    refine congrArg (fun f => pullSplit hN (blkDiag f)) (funext fun m => ?_)
    ext b₁ b₂; cases b₁ <;> cases b₂ <;>
      simp [ham2, finiteQubitPauli, show (2 : Fin 3) ≠ 0 by decide,
        show (2 : Fin 3) ≠ 1 by decide] <;> ring
  have hU_branch_eq (m : Fin M) (t : ℝ) :
      projectiveSpectralMatrix e_enum (V t) (θ_branch m) =
        pullSplit hN (blkDiag fun m' =>
          if m' = m then refl2 (acCos ε (t - t_center m)) (acSin ε (t - t_center m)) else 1) := by
    rw [projectiveSpectralMatrix_anchoredBooleanProjectivePhase]
    unfold anchoredSpectralBooleanReflection
    have hVinv : ((V t)⁻¹ : UGroup N).val = star (V t).val := by simp
    rw [hVinv]
    have hpacket_eq : anchoredBooleanPacket (x_bool m) ∘ e_enum =
        (fun p : Bool × Fin M => if p = (true, m) then (-1 : ℂ) else 1) ∘ cfgSplitEquiv hN := by
      funext q
      simp only [Function.comp_apply]
      have hct_ne_anc : c_true m ≠ c_anchor := fun heq => by
        have h1 := congrArg (cfgSplitEquiv hN) heq
        simp only [c_true, c_anchor, Equiv.apply_symm_apply] at h1
        exact nomatch congrArg Prod.fst h1
      have hq_iff : cfgSplitEquiv hN q = (true, m) ↔ q = c_true m :=
        ⟨fun h => by rw [← (cfgSplitEquiv hN).symm_apply_apply q, h],
         fun h => by rw [h]; exact Equiv.apply_symm_apply _ _⟩
      have hfin : e_enum q = 0 ∨ ∃ i : Fin d, e_enum q = i.succ :=
        Fin.cases (Or.inl rfl) (fun i => Or.inr ⟨i, rfl⟩) (e_enum q)
      rcases hfin with hr | ⟨i, hr⟩
      · rw [hr]
        have hq_anc : q = c_anchor := e_enum.injective (hr.trans he_anchor.symm)
        rw [if_neg (hq_iff.not.mpr (hq_anc ▸ hct_ne_anc.symm))]
        rfl
      · rw [hr]
        change (if decide (i.succ = e_enum (c_true m)) then (-1 : ℂ) else 1) = _
        have hisucc : (i.succ = e_enum (c_true m)) ↔ (cfgSplitEquiv hN q = (true, m)) := by
          rw [hq_iff, ← hr]
          exact e_enum.injective.eq_iff
        by_cases hcond : cfgSplitEquiv hN q = (true, m)
        · rw [if_pos hcond, if_pos (decide_eq_true (hisucc.mpr hcond))]
        · rw [if_neg hcond, if_neg]
          simpa only [decide_eq_true_eq] using mt hisucc.mp hcond
    rw [hpacket_eq, ← pullSplit_diagonal]
    have hdiag_blk : Matrix.diagonal (fun p : Bool × Fin M => if p = (true, m) then (-1 : ℂ) else 1) =
        blkDiag (fun m' => if m' = m then finiteQubitPauli 2 else 1) := by
      ext ⟨b₁, m₁⟩ ⟨b₂, m₂⟩
      by_cases hm' : m₁ = m₂
      · subst hm'
        by_cases hm_eq : m₁ = m
        · subst hm_eq
          cases b₁ <;> cases b₂ <;>
            simp [blkDiag, finiteQubitPauli, Prod.ext_iff,
              show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide]
        · cases b₁ <;> cases b₂ <;>
            simp [blkDiag, hm_eq, Prod.ext_iff]
      · simp [blkDiag, hm', Prod.ext_iff]
    change V_mat t * pullSplit hN (Matrix.diagonal _) * star (V_mat t) = _
    rw [hdiag_blk]
    dsimp [V_mat]
    rw [pullSplit_star, ← pullSplit_mul, ← pullSplit_mul, blkDiag_conjTranspose,
      blkDiag_mul, blkDiag_mul]
    refine congrArg (fun f => pullSplit hN (blkDiag f)) (funext fun m' => ?_)
    by_cases hm' : m' = m
    · subst hm'; simp only [if_true, rot2_pauliZ2_conj]
    · simp only [if_neg hm', mul_one,
        (rot2_unitary (acCos_sin_identities hε (t - t_center m')).1).2]
  have hnorm_minus (m : Fin M) (t : ℝ) :
      ‖projectiveSpectralMatrix e_enum (V t) (θ_branch m) - (W_minus m).val‖ =
        2 * acCos ε (t - t_center m) := by
    rw [hU_branch_eq m t]
    change ‖pullSplit hN _ - pullSplit hN (blkDiag (W_minus_blk m))‖ = _
    rw [← pullSplit_sub, pullSplit_norm, blkDiag_sub]
    have hblk : (blkDiag fun m' =>
        (if m' = m then refl2 (acCos ε (t - t_center m)) (acSin ε (t - t_center m)) else 1) -
          W_minus_blk m m') =
        singleBlk m (refl2 (acCos ε (t - t_center m)) (acSin ε (t - t_center m)) -
          (-finiteQubitPauli 2)) := by
      unfold singleBlk; congr 1; funext m'
      dsimp [W_minus_blk]; split_ifs <;> simp
    rw [hblk, singleBlk_l2_opNorm_eq, norm_refl2_sub_neg_pauliZ2 hε]
  have hnorm_plus (m : Fin M) (t : ℝ) :
      ‖projectiveSpectralMatrix e_enum (V t) (θ_branch m) - (W_plus m).val‖ =
        2 * acSin ε (t - t_center m) := by
    rw [hU_branch_eq m t]
    change ‖pullSplit hN _ - pullSplit hN (blkDiag (W_plus_blk m))‖ = _
    rw [← pullSplit_sub, pullSplit_norm, blkDiag_sub]
    have hblk : (blkDiag fun m' =>
        (if m' = m then refl2 (acCos ε (t - t_center m)) (acSin ε (t - t_center m)) else 1) -
          W_plus_blk m m') =
        singleBlk m (refl2 (acCos ε (t - t_center m)) (acSin ε (t - t_center m)) -
          finiteQubitPauli 2) := by
      unfold singleBlk; congr 1; funext m'
      dsimp [W_plus_blk]; split_ifs <;> simp
    rw [hblk, singleBlk_l2_opNorm_eq, norm_refl2_sub_pauliZ2 hε]
  refine ⟨e_enum, H₀, V, E, K, θ_branch, W_minus, W_plus, t_minus, t_plus, ψ_minus, ψ_plus,
    ?_, ?_, ?_, ?_, ?_⟩
  -- Part (1a): Exact spectral theorem and Kato commutator equation for all t ∈ ℝ
  · intro t
    refine ⟨?_, ?_⟩
    · rw [hHt_eq t]
      have hEdiag : Matrix.diagonal (Complex.ofReal ∘ E t) =
          pullSplit hN (blkDiag fun m => Matrix.diagonal fun b : Bool =>
            if b then ((c_offset m - acRad ε (t - t_center m) : ℝ) : ℂ)
            else ((c_offset m + acRad ε (t - t_center m) : ℝ) : ℂ)) := by
        dsimp [E]
        rw [← Function.comp_assoc, ← pullSplit_diagonal]
        congr 1
        ext ⟨b₁, m₁⟩ ⟨b₂, m₂⟩
        by_cases hm : m₁ = m₂
        · subst hm; cases b₁ <;> cases b₂ <;> simp [blkDiag, E_split]
        · simp [blkDiag, hm, Prod.ext_iff]
      change _ = V_mat t * Matrix.diagonal (Complex.ofReal ∘ E t) * star (V_mat t)
      rw [hEdiag]
      dsimp [V_mat]
      rw [pullSplit_star, ← pullSplit_mul, ← pullSplit_mul, blkDiag_conjTranspose,
        blkDiag_mul, blkDiag_mul]
      exact congrArg (fun f => pullSplit hN (blkDiag f))
        (funext fun m => (rot2_diag_ham2 hε (c_offset m) (t - t_center m)).symm)
    · rw [hHt_eq t]
      have hVzV : star (V t).val * Z₀ * (V t).val =
          pullSplit hN (blkDiag fun m =>
            (rot2 (acCos ε (t - t_center m)) (acSin ε (t - t_center m)))ᴴ *
              finiteQubitPauli 2 *
              rot2 (acCos ε (t - t_center m)) (acSin ε (t - t_center m))) := by
        change star (V_mat t) * Z₀ * V_mat t = _
        rw [hZ₀_eq]
        dsimp [V_mat]
        rw [pullSplit_star, ← pullSplit_mul, ← pullSplit_mul, blkDiag_conjTranspose,
          blkDiag_mul, blkDiag_mul]
      have hdiag_VzV : Matrix.diagonal (fun x => (star (V t).val * Z₀ * (V t).val) x x) =
          pullSplit hN (blkDiag fun m => Matrix.diagonal fun b : Bool =>
            ((rot2 (acCos ε (t - t_center m)) (acSin ε (t - t_center m)))ᴴ *
              finiteQubitPauli 2 *
              rot2 (acCos ε (t - t_center m)) (acSin ε (t - t_center m))) b b) := by
        rw [hVzV]
        have hpull_diag_fn : (fun x : Config N =>
            pullSplit hN (blkDiag fun m =>
              (rot2 (acCos ε (t - t_center m)) (acSin ε (t - t_center m)))ᴴ *
                finiteQubitPauli 2 *
                rot2 (acCos ε (t - t_center m)) (acSin ε (t - t_center m))) x x) =
            (fun p : Bool × Fin M =>
              ((rot2 (acCos ε (t - t_center p.2)) (acSin ε (t - t_center p.2)))ᴴ *
                finiteQubitPauli 2 *
                rot2 (acCos ε (t - t_center p.2)) (acSin ε (t - t_center p.2))) p.1 p.1) ∘
              cfgSplitEquiv hN := by
          funext x
          simp [pullSplit, Matrix.reindex_apply, blkDiag]
        rw [hpull_diag_fn, ← pullSplit_diagonal]
        congr 1
        ext ⟨b₁, m₁⟩ ⟨b₂, m₂⟩
        by_cases hm : m₁ = m₂
        · subst hm; cases b₁ <;> cases b₂ <;> simp [blkDiag]
        · simp [blkDiag, hm, Prod.ext_iff]
      rw [hdiag_VzV, hZ₀_eq]
      change (-Complex.I) • (pullSplit hN _ * pullSplit hN _ - pullSplit hN _ * pullSplit hN _) =
        pullSplit hN _ - V_mat t * pullSplit hN _ * star (V_mat t)
      dsimp [V_mat]
      rw [pullSplit_star, ← pullSplit_mul, ← pullSplit_mul, ← pullSplit_sub, ← pullSplit_smul,
        ← pullSplit_mul, ← pullSplit_mul, ← pullSplit_sub,
        blkDiag_conjTranspose, blkDiag_mul, blkDiag_mul, blkDiag_sub, blkDiag_smul,
        blkDiag_mul, blkDiag_mul, blkDiag_sub]
      exact congrArg (fun f => pullSplit hN (blkDiag f))
        (funext fun m => kato2_commutator_eq hε (c_offset m) (t - t_center m))
  -- Part (1b): Uniform spectral gap ≥ 1/20 across [0, 4 M]
  · intro t ht x y hxy
    let p := cfgSplitEquiv hN x
    let q := cfgSplitEquiv hN y
    have hpq : p ≠ q := (cfgSplitEquiv hN).injective.ne hxy
    change (1 / 20 : ℝ) ≤ |E_split t p - E_split t q|
    have hrad_ub (m : Fin M) : acRad ε (t - t_center m) ≤ 4 * (M : ℝ) + 3 := by
      have hm_le : (m.val : ℝ) ≤ (M : ℝ) := by exact_mod_cast m.isLt.le
      have htc_nn : 0 ≤ t_center m := by dsimp [t_center]; positivity
      have htc_ub : t_center m ≤ 4 * (M : ℝ) + 2 := by dsimp [t_center]; linarith only [hm_le]
      have hdiff_abs : |t - t_center m| ≤ 4 * (M : ℝ) + 2 :=
        abs_le.mpr ⟨by linarith only [ht.1, htc_ub], by linarith only [ht.2, htc_nn]⟩
      have hsq_le : acRad ε (t - t_center m) ^ 2 ≤ (4 * (M : ℝ) + 3) ^ 2 := by
        rw [acRad, Real.sq_sqrt (by positivity)]
        have h1 : (t - t_center m) ^ 2 ≤ (4 * (M : ℝ) + 2) ^ 2 := by
          rw [← sq_abs (t - t_center m)]
          exact pow_le_pow_left₀ (abs_nonneg _) hdiff_abs 2
        have hM_nn : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
        dsimp [ε]; nlinarith only [h1, hM_nn]
      exact (sq_le_sq₀ (acRad_pos hε _).le (by positivity)).mp hsq_le
    have hrad_lb (m : Fin M) : (1 / 40 : ℝ) ≤ acRad ε (t - t_center m) := by
      have hsq : (1 / 40 : ℝ) ^ 2 ≤ acRad ε (t - t_center m) ^ 2 := by
        rw [acRad, Real.sq_sqrt (by positivity)]; dsimp [ε]; nlinarith only [sq_nonneg (t - t_center m)]
      exact (sq_le_sq₀ (by norm_num) (acRad_pos hε _).le).mp hsq
    by_cases hm : p.2 = q.2
    · have hb_ne : p.1 ≠ q.1 := fun hb => hpq (Prod.ext hb hm)
      have hrad := hrad_lb p.2
      dsimp [E_split]
      rw [← hm]
      cases hp1 : p.1 <;> cases hq1 : q.1
      · exact (hb_ne (hp1.trans hq1.symm)).elim
      · simp only [Bool.false_eq_true, if_false, if_true]
        have hpos : 0 ≤ (c_offset p.2 + acRad ε (t - t_center p.2)) -
            (c_offset p.2 - acRad ε (t - t_center p.2)) := by linarith only [hrad]
        rw [abs_of_nonneg hpos]; linarith only [hrad]
      · simp only [Bool.false_eq_true, if_false, if_true]
        have hneg : (c_offset p.2 - acRad ε (t - t_center p.2)) -
            (c_offset p.2 + acRad ε (t - t_center p.2)) ≤ 0 := by linarith only [hrad]
        rw [abs_of_nonpos hneg]; linarith only [hrad]
      · exact (hb_ne (hp1.trans hq1.symm)).elim
    · have hsep_dir {a b : Bool × Fin M} (hab : a.2.val < b.2.val) :
          (1 / 20 : ℝ) ≤ E_split t b - E_split t a := by
        have hm_step : (a.2.val : ℝ) + 1 ≤ (b.2.val : ℝ) := by exact_mod_cast hab
        have hM_nn : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
        have hcoff_diff : 8 * (M : ℝ) + 10 ≤ c_offset b.2 - c_offset a.2 := by
          dsimp [c_offset]; nlinarith only [hm_step, hM_nn]
        have ha_ub : E_split t a ≤ c_offset a.2 + (4 * (M : ℝ) + 3) := by
          dsimp [E_split]; split_ifs <;> linarith only [hrad_ub a.2, acRad_pos hε (t - t_center a.2)]
        have hb_lb : c_offset b.2 - (4 * (M : ℝ) + 3) ≤ E_split t b := by
          dsimp [E_split]; split_ifs <;> linarith only [hrad_ub b.2, acRad_pos hε (t - t_center b.2)]
        linarith only [hcoff_diff, ha_ub, hb_lb]
      rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hm) with hlt | hgt
      · rw [abs_sub_comm]
        exact (hsep_dir hlt).trans (le_abs_self _)
      · exact (hsep_dir hgt).trans (le_abs_self _)
  -- Part (2): Ordered disjoint crossing windows and strict W_minus → W_plus saddle switches
  · intro m
    obtain ⟨⟨hc_neg, hs_neg⟩, ⟨hc_pos, hs_pos⟩, _, hδc_lt⟩ := ac_values_at_crossings hε
    have hδc_pos : 0 < δc := by
      have : (0 : ℝ) < Real.sqrt 399 := Real.sqrt_pos.mpr (by norm_num)
      dsimp [δc, ε]; positivity
    have hδc_lt1 : δc < 1 := by
      have h40 : 40 * ε = 1 := by dsimp [ε]; norm_num
      dsimp only [δc]; linarith only [hδc_lt, h40]
    have h399_gt1 : (1 : ℝ) < Real.sqrt 399 := by
      rw [← Real.sqrt_one]; exact Real.sqrt_lt_sqrt zero_le_one (by norm_num)
    have hdiff_minus : t_minus m - t_center m = -δc := by dsimp [t_minus]; ring
    have hdiff_plus : t_plus m - t_center m = δc := by dsimp [t_plus]; ring
    refine ⟨by dsimp [t_minus, t_center]; linarith only [hδc_lt1],
      by dsimp [t_minus, t_center]; linarith only [hδc_pos],
      by dsimp [t_plus, t_center]; linarith only [hδc_pos],
      by dsimp [t_plus, t_center]; linarith only [hδc_lt1],
      ?_, ?_, ?_, ?_⟩
    · rw [hnorm_minus m (t_minus m), hdiff_minus, hc_neg]; norm_num
    · rw [hnorm_plus m (t_minus m), hdiff_minus, hs_neg]; linarith only [h399_gt1]
    · rw [hnorm_plus m (t_plus m), hdiff_plus, hs_pos]; norm_num
    · rw [hnorm_minus m (t_plus m), hdiff_plus, hc_pos]; linarith only [h399_gt1]
  -- Part (3): Global envelope G oscillates 2^N times across 1/10
  · dsimp only
    obtain ⟨⟨hc_neg, hs_neg⟩, ⟨hc_pos, hs_pos⟩, ⟨h0_cos, h0_sin⟩, hδc_lt⟩ := ac_values_at_crossings hε
    have hδc_lt1 : δc < 1 := by
      have h40 : 40 * ε = 1 := by dsimp [ε]; norm_num
      dsimp only [δc]; linarith only [hδc_lt, h40]
    have hδc_nn : 0 ≤ δc := by
      have : (0 : ℝ) < Real.sqrt 399 := Real.sqrt_pos.mpr (by norm_num)
      dsimp [δc, ε]; positivity
    have h399_gt1 : (1 : ℝ) < Real.sqrt 399 := by
      rw [← Real.sqrt_one]; exact Real.sqrt_lt_sqrt zero_le_one (by norm_num)
    have hsqrt2_gt : (1 / 20 : ℝ) < Real.sqrt 2 := by
      have h1 : (1 : ℝ) < Real.sqrt 2 := by
        rw [← Real.sqrt_one]; exact Real.sqrt_lt_sqrt zero_le_one (by norm_num)
      linarith only [h1]
    have hother_lt {m m' : Fin M} (hne : m' ≠ m) {s_shift : ℝ} (hs_abs : |s_shift| ≤ 1) :
        min ‖projectiveSpectralMatrix e_enum (V (t_center m + s_shift)) (θ_branch m') - (W_minus m').val‖
            ‖projectiveSpectralMatrix e_enum (V (t_center m + s_shift)) (θ_branch m') - (W_plus m').val‖ <
          1 / 20 := by
      rw [hnorm_minus m', hnorm_plus m']
      refine min_two_acCos_acSin_lt_of_two_le_abs ?_
      have hsep : 4 ≤ |t_center m - t_center m'| := by
        rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hlt | hgt
        · have h1 : (m'.val : ℝ) + 1 ≤ (m.val : ℝ) := by exact_mod_cast hlt
          have hpos : 4 ≤ t_center m - t_center m' := by dsimp [t_center]; linarith only [h1]
          exact hpos.trans (le_abs_self _)
        · have h1 : (m.val : ℝ) + 1 ≤ (m'.val : ℝ) := by exact_mod_cast hgt
          have hpos : 4 ≤ t_center m' - t_center m := by dsimp [t_center]; linarith only [h1]
          rw [abs_sub_comm]; exact hpos.trans (le_abs_self _)
      have htri : |t_center m - t_center m'| - |s_shift| ≤
          |(t_center m + s_shift) - t_center m'| := by
        have h := abs_sub_abs_le_abs_sub (t_center m - t_center m') (-s_shift)
        rw [abs_neg, sub_neg_eq_add, show t_center m - t_center m' + s_shift =
          (t_center m + s_shift) - t_center m' by ring] at h
        exact h
      linarith only [hsep, hs_abs, htri]
    refine ⟨fun k => ?_, fun m => ⟨?_, ?_, ?_⟩⟩
    · rw [Finset.sup'_lt_iff]
      intro m _
      rw [hnorm_minus m, hnorm_plus m]
      refine min_two_acCos_acSin_lt_of_two_le_abs ?_
      rcases le_or_gt k.val m.val with hle | hgt
      · have hleR : (k.val : ℝ) ≤ (m.val : ℝ) := by exact_mod_cast hle
        have hneg : 4 * (k.val : ℝ) - t_center m ≤ -2 := by dsimp [t_center]; linarith only [hleR]
        rw [abs_of_nonpos (by linarith only [hneg])]; linarith only [hneg]
      · have hgeR : (m.val : ℝ) + 1 ≤ (k.val : ℝ) := by exact_mod_cast hgt
        have hpos : 2 ≤ 4 * (k.val : ℝ) - t_center m := by dsimp [t_center]; linarith only [hgeR]
        exact hpos.trans (le_abs_self _)
    · have hm_val : min ‖projectiveSpectralMatrix e_enum (V (t_minus m)) (θ_branch m) - (W_minus m).val‖
          ‖projectiveSpectralMatrix e_enum (V (t_minus m)) (θ_branch m) - (W_plus m).val‖ = 1 / 10 := by
        rw [hnorm_minus, hnorm_plus, show t_minus m - t_center m = -δc by dsimp [t_minus]; ring,
          hc_neg, hs_neg]
        exact min_eq_left (by linarith only [h399_gt1]) |>.trans (by norm_num)
      refine le_antisymm (Finset.sup'_le _ _ fun m' _ => ?_) ?_
      · by_cases hm' : m' = m
        · subst hm'; exact hm_val.le
        · have hshift : t_minus m = t_center m + (-δc) := by dsimp [t_minus]; ring
          rw [hshift]
          exact (hother_lt hm' (by rw [abs_neg, abs_of_nonneg hδc_nn]; exact hδc_lt1.le)).le.trans
            (by norm_num)
      · exact hm_val.symm.le.trans (Finset.le_sup'
          (f := fun m' : Fin M =>
            min ‖projectiveSpectralMatrix e_enum (V (t_minus m)) (θ_branch m') - (W_minus m').val‖
                ‖projectiveSpectralMatrix e_enum (V (t_minus m)) (θ_branch m') - (W_plus m').val‖)
          (Finset.mem_univ m))
    · have hm_val : min ‖projectiveSpectralMatrix e_enum (V (t_center m)) (θ_branch m) - (W_minus m).val‖
          ‖projectiveSpectralMatrix e_enum (V (t_center m)) (θ_branch m) - (W_plus m).val‖ =
          Real.sqrt 2 := by
        rw [hnorm_minus, hnorm_plus, sub_self, h0_cos, h0_sin, min_self]
      change Finset.univ.sup' _ (fun m' : Fin M =>
        min ‖projectiveSpectralMatrix e_enum (V (t_center m)) (θ_branch m') - (W_minus m').val‖
            ‖projectiveSpectralMatrix e_enum (V (t_center m)) (θ_branch m') - (W_plus m').val‖) =
        Real.sqrt 2
      refine le_antisymm (Finset.sup'_le _ _ fun m' _ => ?_) ?_
      · by_cases hm' : m' = m
        · subst hm'; exact hm_val.le
        · have hshift : t_center m = t_center m + 0 := (add_zero _).symm
          rw [hshift]
          exact (hother_lt hm' (by norm_num)).le.trans hsqrt2_gt.le
      · exact hm_val.symm.le.trans (Finset.le_sup'
          (f := fun m' : Fin M =>
            min ‖projectiveSpectralMatrix e_enum (V (t_center m)) (θ_branch m') - (W_minus m').val‖
                ‖projectiveSpectralMatrix e_enum (V (t_center m)) (θ_branch m') - (W_plus m').val‖)
          (Finset.mem_univ m))
    · have hm_val : min ‖projectiveSpectralMatrix e_enum (V (t_plus m)) (θ_branch m) - (W_minus m).val‖
          ‖projectiveSpectralMatrix e_enum (V (t_plus m)) (θ_branch m) - (W_plus m).val‖ = 1 / 10 := by
        rw [hnorm_minus, hnorm_plus, show t_plus m - t_center m = δc by dsimp [t_plus]; ring,
          hc_pos, hs_pos]
        exact min_eq_right (by linarith only [h399_gt1]) |>.trans (by norm_num)
      refine le_antisymm (Finset.sup'_le _ _ fun m' _ => ?_) ?_
      · by_cases hm' : m' = m
        · subst hm'; exact hm_val.le
        · have hshift : t_plus m = t_center m + δc := rfl
          rw [hshift]
          exact (hother_lt hm' (by rw [abs_of_nonneg hδc_nn]; exact hδc_lt1.le)).le.trans
            (by norm_num)
      · exact hm_val.symm.le.trans (Finset.le_sup'
          (f := fun m' : Fin M =>
            min ‖projectiveSpectralMatrix e_enum (V (t_plus m)) (θ_branch m') - (W_minus m').val‖
                ‖projectiveSpectralMatrix e_enum (V (t_plus m)) (θ_branch m') - (W_plus m').val‖)
          (Finset.mem_univ m))
  -- Part (4): Unitary-ratio singular eigenmodes and strict Kato expectation sign reversals
  · intro β m U_minus U_plus
    obtain ⟨⟨hc_neg, hs_neg⟩, ⟨hc_pos, hs_pos⟩, _, _⟩ := ac_values_at_crossings hε
    have hdiff_minus : t_minus m - t_center m = -δc := by dsimp [t_minus]; ring
    have hdiff_plus : t_plus m - t_center m = δc := by dsimp [t_plus]; ring
    have hinv2_norm : ‖invSqrt2‖ ^ 2 = 1 / 2 := by
      dsimp [invSqrt2]
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (Real.sqrt_pos.mpr two_pos)),
        inv_pow, Real.sq_sqrt two_pos.le]
      norm_num
    have hψ_minus_norm : ‖ψ_minus m‖ = 1 := by
      have hsq : ‖ψ_minus m‖ ^ 2 = 1 ^ 2 := by
        rw [norm_sq_liftBlockState hN m φ_minus]
        dsimp [φ_minus]
        simp only [norm_mul, Complex.norm_I, one_mul, hinv2_norm]
        norm_num
      exact (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp hsq
    have hψ_plus_norm : ‖ψ_plus m‖ = 1 := by
      have hsq : ‖ψ_plus m‖ ^ 2 = 1 ^ 2 := by
        rw [norm_sq_liftBlockState hN m φ_plus]
        dsimp [φ_plus]
        simp only [norm_mul, norm_neg, Complex.norm_I, one_mul, hinv2_norm]
        norm_num
      exact (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp hsq
    have hsq399C : ((Real.sqrt 399 : ℝ) : ℂ) ^ 2 = 399 := by
      exact_mod_cast Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 399)
    have hsq399C_3 : ((Real.sqrt 399 : ℝ) : ℂ) ^ 3 = 399 * ((Real.sqrt 399 : ℝ) : ℂ) := by
      rw [pow_succ, hsq399C]
    -- Actions of U_minus, W_minus, K(t_minus m) on ψ_minus m
    have hU_minus_act : matAct U_minus (ψ_minus m) =
        liftBlockState hN m (refl2 (1 / 20) (Real.sqrt 399 / 20) *ᵥ φ_minus) := by
      dsimp [U_minus, ψ_minus]
      rw [hU_branch_eq m (t_minus m), matAct_pullSplit_blkDiag_liftBlockState,
        if_pos rfl, hdiff_minus, hc_neg, hs_neg]
    have hW_minus_act : matAct (W_minus m).val (ψ_minus m) =
        liftBlockState hN m ((-finiteQubitPauli 2) *ᵥ φ_minus) := by
      change matAct (pullSplit hN (blkDiag (W_minus_blk m))) (liftBlockState hN m φ_minus) = _
      rw [matAct_pullSplit_blkDiag_liftBlockState]
      simp [W_minus_blk]
    have hU_plus_act : matAct U_plus (ψ_plus m) =
        liftBlockState hN m (refl2 (Real.sqrt 399 / 20) (1 / 20) *ᵥ φ_plus) := by
      dsimp [U_plus, ψ_plus]
      rw [hU_branch_eq m (t_plus m), matAct_pullSplit_blkDiag_liftBlockState,
        if_pos rfl, hdiff_plus, hc_pos, hs_pos]
    have hW_plus_act : matAct (W_plus m).val (ψ_plus m) =
        liftBlockState hN m (finiteQubitPauli 2 *ᵥ φ_plus) := by
      change matAct (pullSplit hN (blkDiag (W_plus_blk m))) (liftBlockState hN m φ_plus) = _
      rw [matAct_pullSplit_blkDiag_liftBlockState]
      simp [W_plus_blk]
    -- Unitary-ratio 2D identities on Bool
    have hratio_minus_2d : (-finiteQubitPauli 2) *ᵥ φ_minus =
        (((1 - (1 / 10 : ℝ) ^ 2 / 2 : ℝ) : ℂ) + Complex.I * (β : ℂ)) •
          (refl2 (1 / 20) (Real.sqrt 399 / 20) *ᵥ φ_minus) := by
      ext b; dsimp [φ_minus, β]; cases b <;>
        simp only [refl2, finiteQubitPauli, Matrix.mulVec, dotProduct, Fintype.sum_bool,
          Matrix.neg_apply,
          show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide,
          if_true, if_false, reduceCtorEq, Bool.false_eq_true] <;>
        push_cast <;> ring_nf <;>
        simp only [Complex.I_sq, hsq399C_3, hsq399C] <;> ring
    have hratio_plus_2d : finiteQubitPauli 2 *ᵥ φ_plus =
        (((1 - (1 / 10 : ℝ) ^ 2 / 2 : ℝ) : ℂ) + Complex.I * (β : ℂ)) •
          (refl2 (Real.sqrt 399 / 20) (1 / 20) *ᵥ φ_plus) := by
      ext b; dsimp [φ_plus, β]; cases b <;>
        simp only [refl2, finiteQubitPauli, Matrix.mulVec, dotProduct, Fintype.sum_bool,
          show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide,
          if_true, if_false, reduceCtorEq, Bool.false_eq_true] <;>
        push_cast <;> ring_nf <;>
        simp only [Complex.I_sq, hsq399C_3, hsq399C] <;> ring
    have hlift_smul (z : ℂ) (φ : Bool → ℂ) :
        liftBlockState hN m (z • φ) = z • liftBlockState hN m φ := by
      ext x; simp [liftBlockState]
    have hratio_minus : matAct (W_minus m).val (ψ_minus m) =
        (((1 - (1 / 10 : ℝ) ^ 2 / 2 : ℝ) : ℂ) + Complex.I * (β : ℂ)) •
          matAct U_minus (ψ_minus m) := by
      rw [hW_minus_act, hU_minus_act, hratio_minus_2d, hlift_smul]
    have hratio_plus : matAct (W_plus m).val (ψ_plus m) =
        (((1 - (1 / 10 : ℝ) ^ 2 / 2 : ℝ) : ℂ) + Complex.I * (β : ℂ)) •
          matAct U_plus (ψ_plus m) := by
      rw [hW_plus_act, hU_plus_act, hratio_plus_2d, hlift_smul]
    -- Singular sphere membership from the unitary-ratio eigenvalue `|1 - e^{i φ}| = 1/10`
    have hcoef_norm : ‖(1 : ℂ) -
        ((((1 - (1 / 10 : ℝ) ^ 2 / 2 : ℝ) : ℂ) + Complex.I * (β : ℂ)))‖ = 1 / 10 := by
      have hsq_norm : ‖(1 : ℂ) -
          ((((1 - (1 / 10 : ℝ) ^ 2 / 2 : ℝ) : ℂ) + Complex.I * (β : ℂ)))‖ ^ 2 =
          (1 / 10 : ℝ) ^ 2 := by
        rw [Complex.sq_norm, Complex.normSq_apply]
        dsimp [β]
        simp only [Complex.ofReal_re, Complex.ofReal_im,
          Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
        have hsq399 : Real.sqrt 399 * Real.sqrt 399 = 399 := Real.mul_self_sqrt (by norm_num)
        nlinarith only [hsq399]
      exact (sq_eq_sq₀ (norm_nonneg _) (by norm_num)).mp hsq_norm
    have hmem_minus : ψ_minus m ∈ maxRightSingularSphere (U_minus - (W_minus m).val) := by
      have hnorm_U_W : ‖U_minus - (W_minus m).val‖ = 1 / 10 := by
        dsimp [U_minus]
        rw [hnorm_minus m (t_minus m), hdiff_minus, hc_neg]; norm_num
      refine ⟨hψ_minus_norm, ?_⟩
      rw [hnorm_U_W, matAct_sub_left, hratio_minus]
      have hsub_smul : matAct U_minus (ψ_minus m) -
          (((1 - (1 / 10 : ℝ) ^ 2 / 2 : ℝ) : ℂ) + Complex.I * (β : ℂ)) •
            matAct U_minus (ψ_minus m) =
          ((1 : ℂ) - (((1 - (1 / 10 : ℝ) ^ 2 / 2 : ℝ) : ℂ) + Complex.I * (β : ℂ))) •
            matAct U_minus (ψ_minus m) := by
        rw [sub_smul, one_smul]
      have hU_unit : U_minus ∈ unitary (Register N) :=
        projectiveSpectralMatrix_mem_unitary' e_enum (V (t_minus m)) (θ_branch m)
      rw [hsub_smul, norm_smul, hcoef_norm, norm_matAct_unitary' hU_unit, hψ_minus_norm, mul_one]
    have hmem_plus : ψ_plus m ∈ maxRightSingularSphere (U_plus - (W_plus m).val) := by
      have hnorm_U_W : ‖U_plus - (W_plus m).val‖ = 1 / 10 := by
        dsimp [U_plus]
        rw [hnorm_plus m (t_plus m), hdiff_plus, hs_pos]; norm_num
      refine ⟨hψ_plus_norm, ?_⟩
      rw [hnorm_U_W, matAct_sub_left, hratio_plus]
      have hsub_smul : matAct U_plus (ψ_plus m) -
          (((1 - (1 / 10 : ℝ) ^ 2 / 2 : ℝ) : ℂ) + Complex.I * (β : ℂ)) •
            matAct U_plus (ψ_plus m) =
          ((1 : ℂ) - (((1 - (1 / 10 : ℝ) ^ 2 / 2 : ℝ) : ℂ) + Complex.I * (β : ℂ))) •
            matAct U_plus (ψ_plus m) := by
        rw [sub_smul, one_smul]
      have hU_unit : U_plus ∈ unitary (Register N) :=
        projectiveSpectralMatrix_mem_unitary' e_enum (V (t_plus m)) (θ_branch m)
      rw [hsub_smul, norm_smul, hcoef_norm, norm_matAct_unitary' hU_unit, hψ_plus_norm, mul_one]
    -- Kato σ_y expectation sign flip: +ε / R_-^2 > 0 at t_minus m vs. -ε / R_+^2 < 0 at t_plus m
    have hanticomm_Y (c s : ℝ) :
        finiteQubitPauli 1 * refl2 c s = -(refl2 c s * finiteQubitPauli 1) := by
      ext b₁ b₂; cases b₁ <;> cases b₂ <;>
        simp [finiteQubitPauli, refl2, Matrix.mul_apply,
          show (1 : Fin 3) ≠ 0 by decide] <;> ring
    have hY_φ_minus : finiteQubitPauli 1 *ᵥ φ_minus = φ_minus := by
      ext b; cases b <;>
        simp [finiteQubitPauli, φ_minus, Matrix.mulVec, dotProduct,
          show (1 : Fin 3) ≠ 0 by decide, ← mul_assoc, Complex.I_mul_I]
    have hY_φ_plus : finiteQubitPauli 1 *ᵥ φ_plus = -φ_plus := by
      ext b; cases b <;>
        simp [finiteQubitPauli, φ_plus, Matrix.mulVec, dotProduct,
          show (1 : Fin 3) ≠ 0 by decide, ← mul_assoc, Complex.I_mul_I]
    have hsign_minus : 0 <
        (inner ℂ (matAct U_minus (ψ_minus m))
          (matAct (K (t_minus m)).val (matAct U_minus (ψ_minus m)))).re -
        (inner ℂ (ψ_minus m) (matAct (K (t_minus m)).val (ψ_minus m))).re := by
      let α_m : ℝ := -ε / (2 * acRad ε (-δc) ^ 2)
      have hα_neg : α_m < 0 :=
        div_neg_of_neg_of_pos (neg_neg_of_pos hε) (mul_pos two_pos (sq_pos_of_pos (acRad_pos hε _)))
      have hK_ψ : matAct (K (t_minus m)).val (ψ_minus m) = (α_m : ℂ) • ψ_minus m := by
        change matAct (pullSplit hN (blkDiag fun m' => kato2 ε (t_minus m - t_center m')))
          (liftBlockState hN m φ_minus) = _
        rw [matAct_pullSplit_blkDiag_liftBlockState, hdiff_minus]
        unfold kato2
        rw [Matrix.smul_mulVec, hY_φ_minus, hlift_smul]
      have hK_Uψ : matAct (K (t_minus m)).val (matAct U_minus (ψ_minus m)) =
          (-(α_m : ℂ)) • matAct U_minus (ψ_minus m) := by
        rw [hU_minus_act]
        change matAct (pullSplit hN (blkDiag fun m' => kato2 ε (t_minus m - t_center m')))
          (liftBlockState hN m _) = _
        rw [matAct_pullSplit_blkDiag_liftBlockState, hdiff_minus]
        unfold kato2
        have hvec : finiteQubitPauli 1 *ᵥ (refl2 (1 / 20) (Real.sqrt 399 / 20) *ᵥ φ_minus) =
            -(refl2 (1 / 20) (Real.sqrt 399 / 20) *ᵥ φ_minus) := by
          rw [Matrix.mulVec_mulVec, hanticomm_Y, Matrix.neg_mulVec, ← Matrix.mulVec_mulVec,
            hY_φ_minus]
        rw [Matrix.smul_mulVec, hvec, smul_neg, ← neg_smul, hlift_smul]
      have hUψ_norm : ‖matAct U_minus (ψ_minus m)‖ = 1 :=
        (norm_matAct_unitary'
          (projectiveSpectralMatrix_mem_unitary' e_enum (V (t_minus m)) (θ_branch m)) _).trans
          hψ_minus_norm
      rw [hK_Uψ, hK_ψ, inner_smul_right, inner_smul_right,
        inner_self_complex', inner_self_complex', hUψ_norm, hψ_minus_norm]
      simp only [one_pow, Complex.ofReal_one, mul_one, Complex.neg_re, Complex.ofReal_re]
      linarith only [hα_neg]
    have hsign_plus :
        (inner ℂ (matAct U_plus (ψ_plus m))
          (matAct (K (t_plus m)).val (matAct U_plus (ψ_plus m)))).re -
        (inner ℂ (ψ_plus m) (matAct (K (t_plus m)).val (ψ_plus m))).re < 0 := by
      let α_p : ℝ := -ε / (2 * acRad ε δc ^ 2)
      have hα_neg : α_p < 0 :=
        div_neg_of_neg_of_pos (neg_neg_of_pos hε) (mul_pos two_pos (sq_pos_of_pos (acRad_pos hε _)))
      have hK_ψ : matAct (K (t_plus m)).val (ψ_plus m) = (-(α_p : ℂ)) • ψ_plus m := by
        change matAct (pullSplit hN (blkDiag fun m' => kato2 ε (t_plus m - t_center m')))
          (liftBlockState hN m φ_plus) = _
        rw [matAct_pullSplit_blkDiag_liftBlockState, hdiff_plus]
        unfold kato2
        rw [Matrix.smul_mulVec, hY_φ_plus, smul_neg, ← neg_smul, hlift_smul]
      have hK_Uψ : matAct (K (t_plus m)).val (matAct U_plus (ψ_plus m)) =
          (α_p : ℂ) • matAct U_plus (ψ_plus m) := by
        rw [hU_plus_act]
        change matAct (pullSplit hN (blkDiag fun m' => kato2 ε (t_plus m - t_center m')))
          (liftBlockState hN m _) = _
        rw [matAct_pullSplit_blkDiag_liftBlockState, hdiff_plus]
        unfold kato2
        have hvec : finiteQubitPauli 1 *ᵥ (refl2 (Real.sqrt 399 / 20) (1 / 20) *ᵥ φ_plus) =
            refl2 (Real.sqrt 399 / 20) (1 / 20) *ᵥ φ_plus := by
          rw [Matrix.mulVec_mulVec, hanticomm_Y, Matrix.neg_mulVec, ← Matrix.mulVec_mulVec,
            hY_φ_plus, Matrix.mulVec_neg, neg_neg]
        rw [Matrix.smul_mulVec, hvec, hlift_smul]
      have hUψ_norm : ‖matAct U_plus (ψ_plus m)‖ = 1 :=
        (norm_matAct_unitary'
          (projectiveSpectralMatrix_mem_unitary' e_enum (V (t_plus m)) (θ_branch m)) _).trans
          hψ_plus_norm
      rw [hK_Uψ, hK_ψ, inner_smul_right, inner_smul_right,
        inner_self_complex', inner_self_complex', hUψ_norm, hψ_plus_norm]
      simp only [one_pow, Complex.ofReal_one, mul_one, Complex.neg_re, Complex.ofReal_re]
      linarith only [hα_neg]
    exact ⟨hmem_minus, hratio_minus, hsign_minus, hmem_plus, hratio_plus, hsign_plus⟩

#print axioms levelBand_dini_diam_le
#print axioms gaussian_levelBand_dini_anticoncentration
#print axioms fixed_tenth_locking_of_levelBand_dini
#print axioms deriv_deriv_sawtoothBranches_zero
#print axioms maxMinSawtooth_gaussian_violation
#print axioms katoOffDiagGenerator_commutator_eq
#print axioms norm_katoOffDiagGenerator_le
#print axioms transverse_mode_slope_lipschitz
#print axioms pauliPencil_exponential_saddle_switches

end
end GaloisForLFunctions.HTGeometry.AccuracyScales.TenthPlateau
