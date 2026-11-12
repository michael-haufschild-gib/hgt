import GaloisForLFunctions.HTGeometry.AffineLatticePoisson
import GaloisForLFunctions.HTGeometry.LatticePolynomialWeight

/-!
# Short columns are incoherent

The rows of a reciprocity family are lattice points `n ∈ ℤ^d` (for `ℤ[ω]`, `d = 2`), weighted by a
smooth profile `f(Bn)` of the row scale. A column enters a row sum through a periodic function of
`n`; expanding it into additive characters, every column is a combination of phases
`e(⟨n, θ⟩) = exp(2πi⟨n, θ⟩)`. A character modulo `q` has its frequencies in `q⁻¹ℤ^d`, and a
nonprincipal one has none on `ℤ^d`: its frequencies sit at distance `≥ δ ≍ q⁻¹` from the lattice.

* `tsum_phase_mul_comp_eq` (**reflection of a row sum**): Poisson summation turns the row sum of a
  phase into the dual lattice sum of the Fourier transform at the shifted dual points:
  `Σ_n e(⟨n, θ⟩) f(Bn) = |det B|⁻¹ Σ_m f̂(B^{−*}(m − θ))`.
* `tsum_norm_le_of_far` (**decay off the lattice**): if `‖B^{−*}v‖ ≥ μ‖v‖` and `θ` is reduced and at
  distance `≥ δ` from `ℤ^d`, the dual sum is at most `C (μδ)^{−M}` for every `M > d`, with `C`
  depending only on `f`, `M`, `d`.
* `norm_tsum_column_le` (**short columns are incoherent**): the row sum of a finite combination of
  such phases is at most `|det B|⁻¹ · C (μδ)^{−M} · Σ|α_j|`.

For rows of scale `λ` (`B = λ⁻¹B₀`) the factor `|det B|⁻¹ = λ^d |det B₀|⁻¹` is the trivial row count
and `μ = λμ₀`: a column of conductor `q` with `qλ⁻¹ → 0` contributes `O((q/λ)^M)` times the trivial
bound, for every `M`. Coherence of a row family can therefore only come from the principal column
(the frequency `θ ∈ ℤ^d`) or from columns whose conductor reaches the row scale, where the dual sum
is a sum of Gauss sums at the dual frequencies.
-/

noncomputable section

open MeasureTheory
open scoped FourierTransform

namespace GaloisForLFunctions.CoherenceTheoryOfReciprocityFamilies

open HTGeometry HTGeometry.IntegerLatticePoisson

variable {d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "Z" => Fin d → ℤ

/-- The additive character `e(⟨x, θ⟩)`. -/
def phase (θ x : E) : ℂ := Complex.exp ((2 * Real.pi * inner ℝ x θ : ℝ) * Complex.I)

theorem norm_phase (θ x : E) : ‖phase θ x‖ = 1 := by
  rw [phase, Complex.norm_exp_ofReal_mul_I]

/-- **The reflection of a row sum.** `Σ_n e(⟨n, θ⟩) f(Bn) = |det B|⁻¹ Σ_m f̂(B^{−*}(m − θ))`. -/
theorem tsum_phase_mul_comp_eq (f : SchwartzMap E ℂ) (B : E ≃L[ℝ] E) (θ : E) :
    ∑' n : Z, phase θ (euclideanIntegerPoint n) * f (B (euclideanIntegerPoint n)) =
      (latticeScale B : ℂ) *
        ∑' m : Z, (𝓕 f) (inverseAdjoint B (euclideanIntegerPoint m - θ)) := by
  set g := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ B f with hg
  have h := schwartz_poisson_twisted g θ
  have hgv : ∀ n : Z, g (euclideanIntegerPoint n) = f (B (euclideanIntegerPoint n)) := fun n => by
    simp [hg, SchwartzMap.compCLMOfContinuousLinearEquiv_apply]
  have hF : ∀ m : Z, (𝓕 g) (euclideanIntegerPoint m - θ) =
      (latticeScale B : ℂ) * (𝓕 f) (inverseAdjoint B (euclideanIntegerPoint m - θ)) := fun m => by
    rw [hg, fourier_schwartz_comp_linearEquiv, Complex.real_smul]
  simp_rw [hgv, hF] at h
  rw [tsum_mul_left] at h
  unfold phase
  exact h.symm

/-- `d ‖x‖ ≥ Σ_i |x_i|` in Euclidean space. -/
theorem sum_abs_le_card_mul_norm (x : E) : ∑ i, |x i| ≤ d * ‖x‖ := by
  calc ∑ i, |x i| ≤ ∑ _i : Fin d, ‖x‖ :=
        Finset.sum_le_sum fun i _ => by
          have := PiLp.norm_apply_le x i
          rwa [Real.norm_eq_abs] at this
    _ = d * ‖x‖ := by simp

/-- **A reduced frequency far from the lattice is far from every lattice point, linearly in the
bracket.** If `|θ_i| ≤ ½` and `‖m − θ‖ ≥ δ` for all `m`, `0 < δ ≤ 1`, then
`‖m − θ‖ ≥ δ (1 + |m|₁)/(3d + 3)`. -/
theorem dist_ge_bracket {θ : E} (hθ : ∀ i, |θ i| ≤ 1 / 2) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hfar : ∀ m : Z, δ ≤ ‖euclideanIntegerPoint m - θ‖) (m : Z) :
    δ * latticeBracket m / (3 * d + 3) ≤ ‖euclideanIntegerPoint m - θ‖ := by
  have hd3 : (0 : ℝ) < 3 * d + 3 := by positivity
  have hℓ := latticeEll1_nonneg m
  rw [div_le_iff₀ hd3]
  by_cases hsmall : latticeEll1 m ≤ 2 * d
  · -- near points: the distance is at least `δ`
    have h1 := hfar m
    have hb : latticeBracket m ≤ 3 * d + 3 := by
      unfold latticeBracket; linarith
    calc δ * latticeBracket m ≤ δ * (3 * d + 3) := mul_le_mul_of_nonneg_left hb hδ0.le
      _ ≤ ‖euclideanIntegerPoint m - θ‖ * (3 * d + 3) := mul_le_mul_of_nonneg_right h1 hd3.le
  · -- far points: the `ℓ¹` norm of `m − θ` is at least `|m|₁ − d/2`
    push Not at hsmall
    have hd : (1 : ℝ) ≤ d := by
      rcases Nat.eq_zero_or_pos d with h | h
      · subst h; simp [latticeEll1] at hsmall
      · exact_mod_cast h
    have hl1 : latticeEll1 m - d / 2 ≤ ∑ i, |(euclideanIntegerPoint m - θ) i| := by
      have hcoord : ∀ i, |(m i : ℝ)| - 1 / 2 ≤ |(euclideanIntegerPoint m - θ) i| := by
        intro i
        have hpt : (euclideanIntegerPoint m - θ) i = (m i : ℝ) - θ i := by
          simp [euclideanIntegerPoint, integerPoint]
        rw [hpt]
        have := abs_sub_abs_le_abs_sub (m i : ℝ) (θ i)
        linarith [hθ i]
      calc latticeEll1 m - d / 2 = ∑ i, (|(m i : ℝ)| - 1 / 2) := by
            unfold latticeEll1
            rw [Finset.sum_sub_distrib]
            simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            ring
        _ ≤ _ := Finset.sum_le_sum fun i _ => hcoord i
    have hnorm := sum_abs_le_card_mul_norm (euclideanIntegerPoint m - θ)
    unfold latticeBracket
    have hdpos : (0 : ℝ) < d := by linarith
    -- `δ(1 + ℓ) ≤ 2ℓ ≤ (8/3)(ℓ − d/2)·... ≤ (3d + 3)‖m − θ‖`
    have key : (1 + latticeEll1 m) * d ≤ (3 * d + 3) * (latticeEll1 m - d / 2) := by
      nlinarith
    have hpos : 0 ≤ latticeEll1 m - d / 2 := by linarith
    have h2 : (latticeEll1 m - d / 2) ≤ d * ‖euclideanIntegerPoint m - θ‖ := hl1.trans hnorm
    have h3 : (1 + latticeEll1 m) * d ≤ (3 * d + 3) * (d * ‖euclideanIntegerPoint m - θ‖) :=
      key.trans (mul_le_mul_of_nonneg_left h2 hd3.le)
    have h4 : (1 + latticeEll1 m) ≤ (3 * d + 3) * ‖euclideanIntegerPoint m - θ‖ := by
      have : (1 + latticeEll1 m) * d ≤ ((3 * d + 3) * ‖euclideanIntegerPoint m - θ‖) * d := by
        nlinarith
      exact le_of_mul_le_mul_right this hdpos
    calc δ * (1 + latticeEll1 m) ≤ 1 * (1 + latticeEll1 m) :=
          mul_le_mul_of_nonneg_right hδ1 (by linarith)
      _ ≤ ‖euclideanIntegerPoint m - θ‖ * (3 * d + 3) := by linarith

/-- **Decay off the lattice.** For a Schwartz function `g`, `M > d`, a linear map `T` with
`‖Tv‖ ≥ μ‖v‖`, and a reduced frequency `θ` at distance `≥ δ` from `ℤ^d` (`0 < δ ≤ 1`):
the dual sum `Σ_m ‖g(T(m − θ))‖` converges and is at most `C (μδ)^{−M}`, with
`C = ‖g‖_{M,0} (3d + 3)^M Σ_m ⟨m⟩^{−M}`. -/
theorem tsum_norm_le_of_far (hd : 0 < d) (g : SchwartzMap E ℂ) {M : ℕ} (hM : (d : ℝ) < M)
    (T : E →L[ℝ] E) {μ : ℝ} (hμ : 0 < μ) (hT : ∀ v, μ * ‖v‖ ≤ ‖T v‖) {θ : E}
    (hθ : ∀ i, |θ i| ≤ 1 / 2) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hfar : ∀ m : Z, δ ≤ ‖euclideanIntegerPoint m - θ‖) :
    Summable (fun m : Z => ‖g (T (euclideanIntegerPoint m - θ))‖) ∧
      ∑' m : Z, ‖g (T (euclideanIntegerPoint m - θ))‖ ≤
        (SchwartzMap.seminorm ℝ M 0 g * (3 * d + 3) ^ M *
          ∑' m : Z, latticeBracket m ^ (-(M : ℝ))) * (μ * δ) ^ (-(M : ℝ)) := by
  set S := SchwartzMap.seminorm ℝ M 0 g
  have hS : 0 ≤ S := apply_nonneg _ _
  have hd3 : (0 : ℝ) < 3 * d + 3 := by positivity
  have hsum : Summable (fun m : Z => latticeBracket m ^ (-(M : ℝ))) :=
    summable_latticeBracket_rpow hd hM
  have hμδ : 0 < μ * δ := mul_pos hμ hδ0
  -- the pointwise bound
  have hpt : ∀ m : Z, ‖g (T (euclideanIntegerPoint m - θ))‖ ≤
      S * (3 * d + 3) ^ M * (μ * δ) ^ (-(M : ℝ)) * latticeBracket m ^ (-(M : ℝ)) := by
    intro m
    set v := euclideanIntegerPoint m - θ
    have hv := dist_ge_bracket hθ hδ0 hδ1 hfar m
    have hb := latticeBracket_pos m
    -- `‖T v‖ ≥ μ δ ⟨m⟩/(3d+3) > 0`
    have hTv : μ * δ * latticeBracket m / (3 * d + 3) ≤ ‖T v‖ := by
      calc μ * δ * latticeBracket m / (3 * d + 3) = μ * (δ * latticeBracket m / (3 * d + 3)) := by
            ring
        _ ≤ μ * ‖v‖ := mul_le_mul_of_nonneg_left hv hμ.le
        _ ≤ ‖T v‖ := hT v
    have hlow : 0 < μ * δ * latticeBracket m / (3 * d + 3) := by positivity
    have hdec := SchwartzMap.norm_pow_mul_le_seminorm ℝ g M (T v)
    -- `‖g(Tv)‖ ≤ S / ‖Tv‖^M ≤ S ((3d+3)/(μδ⟨m⟩))^M`
    have hTpos : 0 < ‖T v‖ := lt_of_lt_of_le hlow hTv
    have hgv : ‖g (T v)‖ ≤ S / ‖T v‖ ^ M := by
      rw [le_div_iff₀ (pow_pos hTpos M), mul_comm]
      exact hdec
    have hpow : (μ * δ * latticeBracket m / (3 * d + 3)) ^ M ≤ ‖T v‖ ^ M :=
      pow_le_pow_left₀ hlow.le hTv M
    calc ‖g (T v)‖ ≤ S / ‖T v‖ ^ M := hgv
      _ ≤ S / (μ * δ * latticeBracket m / (3 * d + 3)) ^ M :=
          div_le_div_of_nonneg_left hS (pow_pos hlow M) hpow
      _ = S * (3 * d + 3) ^ M * (μ * δ) ^ (-(M : ℝ)) * latticeBracket m ^ (-(M : ℝ)) := by
          rw [Real.rpow_neg hμδ.le, Real.rpow_neg hb.le, Real.rpow_natCast, Real.rpow_natCast,
            div_pow, mul_pow]
          field_simp
  have hmaj : Summable (fun m : Z =>
      S * (3 * d + 3) ^ M * (μ * δ) ^ (-(M : ℝ)) * latticeBracket m ^ (-(M : ℝ))) :=
    hsum.mul_left _
  have hs : Summable (fun m : Z => ‖g (T (euclideanIntegerPoint m - θ))‖) :=
    hmaj.of_nonneg_of_le (fun _ => norm_nonneg _) hpt
  refine ⟨hs, ?_⟩
  calc ∑' m : Z, ‖g (T (euclideanIntegerPoint m - θ))‖ ≤
        ∑' m : Z, S * (3 * d + 3) ^ M * (μ * δ) ^ (-(M : ℝ)) * latticeBracket m ^ (-(M : ℝ)) :=
        Summable.tsum_le_tsum hpt hs hmaj
    _ = (S * (3 * d + 3) ^ M * ∑' m : Z, latticeBracket m ^ (-(M : ℝ))) *
          (μ * δ) ^ (-(M : ℝ)) := by
        rw [tsum_mul_left]
        ring

/-- **Short columns are incoherent.** Let the rows be weighted by `f(Bn)`, with `‖B^{−*}v‖ ≥ μ‖v‖`,
and let a column be a finite combination `Σ_j α_j e(⟨n, θ_j⟩)` of reduced frequencies at distance
`≥ δ` from `ℤ^d`. Then for every `M > d` the row sum of the column is at most
`|det B|⁻¹ C (μδ)^{−M} Σ_j |α_j|`, with `C` depending only on `f`, `M`, `d`. -/
theorem norm_tsum_column_le (hd : 0 < d) (f : SchwartzMap E ℂ) {M : ℕ} (hM : (d : ℝ) < M)
    (B : E ≃L[ℝ] E) {μ : ℝ} (hμ : 0 < μ) (hT : ∀ v, μ * ‖v‖ ≤ ‖inverseAdjoint B v‖)
    {J : Type*} (s : Finset J) (α : J → ℂ) (θ : J → E) (hθ : ∀ j ∈ s, ∀ i, |θ j i| ≤ 1 / 2)
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hfar : ∀ j ∈ s, ∀ m : Z, δ ≤ ‖euclideanIntegerPoint m - θ j‖) :
    ‖∑' n : Z, (∑ j ∈ s, α j * phase (θ j) (euclideanIntegerPoint n)) *
        f (B (euclideanIntegerPoint n))‖ ≤
      latticeScale B * ((SchwartzMap.seminorm ℝ M 0 (𝓕 f) * (3 * d + 3) ^ M *
          ∑' m : Z, latticeBracket m ^ (-(M : ℝ))) * (μ * δ) ^ (-(M : ℝ))) *
        ∑ j ∈ s, ‖α j‖ := by
  set K := (SchwartzMap.seminorm ℝ M 0 (𝓕 f) * (3 * d + 3) ^ M *
          ∑' m : Z, latticeBracket m ^ (-(M : ℝ))) * (μ * δ) ^ (-(M : ℝ)) with hK
  have hsumf : ∀ j : J, Summable fun n : Z =>
      α j * phase (θ j) (euclideanIntegerPoint n) * f (B (euclideanIntegerPoint n)) := by
    intro j
    refine Summable.of_norm ?_
    refine ((summable_norm_affine_lattice f B 0).mul_left ‖α j‖).congr fun n => ?_
    rw [norm_mul, norm_mul, norm_phase, mul_one, add_zero]
  have hswap : ∑' n : Z, (∑ j ∈ s, α j * phase (θ j) (euclideanIntegerPoint n)) *
        f (B (euclideanIntegerPoint n)) =
      ∑ j ∈ s, α j * ∑' n : Z, phase (θ j) (euclideanIntegerPoint n) *
        f (B (euclideanIntegerPoint n)) := by
    simp_rw [Finset.sum_mul]
    rw [Summable.tsum_finsetSum fun j _ => hsumf j]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← tsum_mul_left]
    congr 1
    funext n
    ring
  rw [hswap]
  have hterm : ∀ j ∈ s, ‖α j * ∑' n : Z, phase (θ j) (euclideanIntegerPoint n) *
      f (B (euclideanIntegerPoint n))‖ ≤ latticeScale B * K * ‖α j‖ := by
    intro j hj
    rw [tsum_phase_mul_comp_eq, norm_mul, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (latticeScale_pos B).le]
    obtain ⟨hs, hle⟩ := tsum_norm_le_of_far hd (𝓕 f) hM (inverseAdjoint B) hμ hT (hθ j hj)
      hδ0 hδ1 (hfar j hj)
    have h1 : ‖∑' m : Z, (𝓕 f) (inverseAdjoint B (euclideanIntegerPoint m - θ j))‖ ≤ K :=
      (norm_tsum_le_tsum_norm hs).trans hle
    have hK0 : 0 ≤ K := (norm_nonneg _).trans h1
    calc ‖α j‖ * (latticeScale B * ‖∑' m : Z,
          (𝓕 f) (inverseAdjoint B (euclideanIntegerPoint m - θ j))‖) ≤
        ‖α j‖ * (latticeScale B * K) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left h1 (latticeScale_pos B).le) (norm_nonneg _)
      _ = latticeScale B * K * ‖α j‖ := by ring
  calc ‖∑ j ∈ s, α j * ∑' n : Z, phase (θ j) (euclideanIntegerPoint n) *
        f (B (euclideanIntegerPoint n))‖ ≤ ∑ j ∈ s, latticeScale B * K * ‖α j‖ :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum hterm)
    _ = latticeScale B * K * ∑ j ∈ s, ‖α j‖ := by rw [Finset.mul_sum]

end GaloisForLFunctions.CoherenceTheoryOfReciprocityFamilies
