import GaloisForLFunctions.HTGeometry.KrylovCausalReplicaSieveLaw

/-!
# Krylov carrier projection and short-time amplitude bounds

For real frequencies `ω_i` on a finite index set, the spectral power vectors `v_k = (ω_i^k)_i`
span the Krylov subspace `K_K = span {v_0, …, v_K}` of `ℓ²`. Every coefficient vector `x` splits
orthogonally into its Krylov carrier `P x` (orthogonal projection onto `K_K`) and a residual whose
moments `Σ_i r_i ω_i^k` vanish for `k ≤ K`. For the normalized amplitude
`A_x(t) = d^{-1/2} Σ_i x_i e^{i t ω_i}` with `|ω_i| ≤ B`, this gives
`|A_x(t)| ≤ ‖P x‖ + ‖x - P x‖ B^{K+1} |t|^{K+1} / (K+1)!`. Consequences: a large amplitude forces
a large carrier, and for a finite family of unit-norm targets an explicit carrier-load budget rules
out amplitudes of size `θ` on `|t| ≤ T`, in a quadratic and in a `2r`-th power (replica) form.

## Main results

- `spectralKrylovResidual_moment_zero`: the Krylov residual has vanishing moments up to order `K`.
- `norm_normalizedSpectralAmplitude_le_krylovCarrier_add_factorial`: the carrier-plus-Taylor-tail
  amplitude bound.
- `krylovCarrier_norm_ge_of_large_normalizedSpectralAmplitude`: if `‖x‖ ≤ 1` and `θ ≤ |A_x(t)|`,
  then `θ - B^{K+1} |t|^{K+1} / (K+1)! ≤ ‖P x‖`.
- `no_large_adaptive_amplitude_of_finiteKrylovLoad`: if
  `√(Σ_w ‖P x_w‖²) + B^{K+1} T^{K+1} / (K+1)! < θ`, every target amplitude stays below `θ` on
  `|t| ≤ T`.
- `no_large_adaptive_amplitude_of_finiteKrylovReplicaLoad`: the same conclusion from
  `Σ_w ‖P x_w‖^{2r} < (θ - B^{K+1} T^{K+1} / (K+1)!)^{2r}`.

## Hypotheses

All results are unconditional. The bounds take explicit numerical hypotheses: dimension `0 < d`,
frequency bound `|ω_i| ≤ B` with `0 ≤ B`, time window `|t| ≤ T`, unit-norm targets where stated,
and the stated budget inequalities in the no-large-amplitude theorems.
-/

open scoped BigOperators ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- The spectral power vector `(ω_i^k)_i ∈ ℓ²(I)`. -/
def spectralPowerVector {I : Type*} [Fintype I]
    (frequency : I → ℝ) (k : ℕ) : EuclideanSpace ℂ I :=
  WithLp.toLp 2 fun i ↦ (frequency i : ℂ) ^ k

/-- The Krylov subspace `span {v_0, …, v_K}` of spectral power vectors. -/
def spectralKrylovSubspace {I : Type*} [Fintype I]
    (frequency : I → ℝ) (K : ℕ) : Submodule ℂ (EuclideanSpace ℂ I) :=
  Submodule.span ℂ (Set.range fun k : Fin (K + 1) ↦
    spectralPowerVector frequency k)

theorem spectralPowerVector_mem_spectralKrylovSubspace
    {I : Type*} [Fintype I] (frequency : I → ℝ) {K k : ℕ} (hk : k ≤ K) :
    spectralPowerVector frequency k ∈ spectralKrylovSubspace frequency K := by
  apply Submodule.subset_span
  exact ⟨⟨k, Nat.lt_succ_iff.mpr hk⟩, rfl⟩

/-- The Krylov carrier: orthogonal projection of `x` onto the Krylov subspace. -/
def spectralKrylovCarrier {I : Type*} [Fintype I]
    (frequency : I → ℝ) (K : ℕ) (x : EuclideanSpace ℂ I) :
    EuclideanSpace ℂ I :=
  (spectralKrylovSubspace frequency K).starProjection x

/-- The Krylov residual `x - P x`. -/
def spectralKrylovResidual {I : Type*} [Fintype I]
    (frequency : I → ℝ) (K : ℕ) (x : EuclideanSpace ℂ I) :
    EuclideanSpace ℂ I :=
  x - spectralKrylovCarrier frequency K x

/-- The Krylov residual is orthogonal to every power vector `v_k` with `k ≤ K`. -/
theorem inner_spectralKrylovResidual_power_zero
    {I : Type*} [Fintype I] (frequency : I → ℝ) (K : ℕ)
    (x : EuclideanSpace ℂ I) {k : ℕ} (hk : k ≤ K) :
    inner ℂ (spectralKrylovResidual frequency K x)
      (spectralPowerVector frequency k) = 0 := by
  exact Submodule.starProjection_inner_eq_zero x _
    (spectralPowerVector_mem_spectralKrylovSubspace frequency hk)

/-- Moment vanishing: `Σ_i r_i ω_i^k = 0` for the Krylov residual `r` and every `k ≤ K`. -/
theorem spectralKrylovResidual_moment_zero
    {I : Type*} [Fintype I] (frequency : I → ℝ) (K : ℕ)
    (x : EuclideanSpace ℂ I) {k : ℕ} (hk : k ≤ K) :
    ∑ i, spectralKrylovResidual frequency K x i * (frequency i : ℂ) ^ k = 0 := by
  have h := inner_spectralKrylovResidual_power_zero frequency K x hk
  have h' : inner ℂ (spectralPowerVector frequency k)
      (spectralKrylovResidual frequency K x) = 0 :=
    inner_eq_zero_symm.mp h
  simpa [PiLp.inner_apply, spectralPowerVector, RCLike.inner_apply,
    mul_comm] using h'

/-- Cauchy–Schwarz on `ℂ^d`, `d > 0`: `d^{-1/2} Σ_i |x_i| ≤ ‖x‖`. -/
theorem inv_sqrt_card_mul_sum_norm_le_norm
    {d : ℕ} (hd : 0 < d) (x : EuclideanSpace ℂ (Fin d)) :
    (Real.sqrt (d : ℝ))⁻¹ * ∑ i, ‖x i‖ ≤ ‖x‖ := by
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  have hsqrtPos : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.2 hdR
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt
    (Finset.univ : Finset (Fin d)) (fun _ => (1 : ℝ)) (fun i => ‖x i‖)
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one] at hcs
  have hsquares : (∑ i : Fin d, ‖x i‖ ^ (2 : ℕ)) = ‖x‖ ^ (2 : ℕ) :=
    (EuclideanSpace.norm_sq_eq x).symm
  have hnormsqrt : Real.sqrt (∑ i : Fin d, ‖x i‖ ^ (2 : ℕ)) = ‖x‖ := by
    rw [hsquares, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg x)]
  calc
    (Real.sqrt (d : ℝ))⁻¹ * ∑ i, ‖x i‖ ≤
        (Real.sqrt (d : ℝ))⁻¹ *
          (Real.sqrt (d : ℝ) * Real.sqrt (∑ i : Fin d, ‖x i‖ ^ (2 : ℕ))) :=
      mul_le_mul_of_nonneg_left hcs (inv_nonneg.mpr hsqrtPos.le)
    _ = ‖x‖ := by rw [hnormsqrt]; field_simp

/-- Normalized coefficients `d^{-1/2} x_i`. -/
def normalizedSpectralCoefficient {d : ℕ}
    (x : EuclideanSpace ℂ (Fin d)) (i : Fin d) : ℂ :=
  ((Real.sqrt (d : ℝ))⁻¹ : ℂ) * x i

theorem sum_norm_normalizedSpectralCoefficient_le_norm
    {d : ℕ} (hd : 0 < d) (x : EuclideanSpace ℂ (Fin d)) :
    ∑ i, ‖normalizedSpectralCoefficient x i‖ ≤ ‖x‖ := by
  have hsqrt : 0 ≤ (Real.sqrt (d : ℝ))⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg _)
  have hterm (i : Fin d) :
      ‖normalizedSpectralCoefficient x i‖ =
        (Real.sqrt (d : ℝ))⁻¹ * ‖x i‖ := by
    unfold normalizedSpectralCoefficient
    rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _)]
  calc
    ∑ i, ‖normalizedSpectralCoefficient x i‖ =
        (Real.sqrt (d : ℝ))⁻¹ * ∑ i, ‖x i‖ := by
      simp_rw [hterm]
      rw [Finset.mul_sum]
    _ ≤ ‖x‖ := inv_sqrt_card_mul_sum_norm_le_norm hd x

/-- Normalized amplitude `A_x(t) = d^{-1/2} Σ_i x_i e^{i t ω_i}`. -/
def normalizedSpectralAmplitude {d : ℕ}
    (x : EuclideanSpace ℂ (Fin d)) (frequency : Fin d → ℝ) (t : ℝ) : ℂ :=
  finiteRealTimeComplexAmplitude (normalizedSpectralCoefficient x) frequency t

/-- For `d > 0`, `|A_x(t)| ≤ ‖x‖` for every real `t`. -/
theorem norm_normalizedSpectralAmplitude_le_norm
    {d : ℕ} (hd : 0 < d) (x : EuclideanSpace ℂ (Fin d))
    (frequency : Fin d → ℝ) (t : ℝ) :
    ‖normalizedSpectralAmplitude x frequency t‖ ≤ ‖x‖ := by
  unfold normalizedSpectralAmplitude finiteRealTimeComplexAmplitude
  calc
    ‖∑ i, normalizedSpectralCoefficient x i *
        Complex.exp ((t : ℂ) * (Complex.I * frequency i))‖ ≤
        ∑ i, ‖normalizedSpectralCoefficient x i *
          Complex.exp ((t : ℂ) * (Complex.I * frequency i))‖ :=
      norm_sum_le _ _
    _ = ∑ i, ‖normalizedSpectralCoefficient x i‖ := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [norm_mul, Complex.norm_exp]
      have hre : (((t : ℂ) * (Complex.I * frequency i)).re) = 0 := by simp
      rw [hre, Real.exp_zero, mul_one]
    _ ≤ ‖x‖ := sum_norm_normalizedSpectralCoefficient_le_norm hd x

theorem normalizedSpectralAmplitude_add
    {d : ℕ} (x y : EuclideanSpace ℂ (Fin d))
    (frequency : Fin d → ℝ) (t : ℝ) :
    normalizedSpectralAmplitude (x + y) frequency t =
      normalizedSpectralAmplitude x frequency t +
        normalizedSpectralAmplitude y frequency t := by
  unfold normalizedSpectralAmplitude finiteRealTimeComplexAmplitude
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  unfold normalizedSpectralCoefficient
  simp only [PiLp.add_apply]
  ring

/-- The Krylov residual is no longer than the vector: `‖x - P x‖ ≤ ‖x‖`. -/
theorem norm_spectralKrylovResidual_le
    {I : Type*} [Fintype I] (frequency : I → ℝ) (K : ℕ)
    (x : EuclideanSpace ℂ I) :
    ‖spectralKrylovResidual frequency K x‖ ≤ ‖x‖ := by
  have hpy := (spectralKrylovSubspace frequency K).norm_sq_eq_add_norm_sq_starProjection x
  rw [Submodule.starProjection_orthogonal_val] at hpy
  dsimp [spectralKrylovResidual]
  dsimp [spectralKrylovCarrier] at hpy ⊢
  nlinarith [norm_nonneg x,
    norm_nonneg (x - (spectralKrylovSubspace frequency K).starProjection x),
    norm_nonneg ((spectralKrylovSubspace frequency K).starProjection x)]

/-- The normalized residual coefficients also have vanishing moments up to order `K`. -/
theorem normalizedSpectralCoefficient_residual_moment_zero
    {d : ℕ} (frequency : Fin d → ℝ) (K : ℕ)
    (x : EuclideanSpace ℂ (Fin d)) {k : ℕ} (hk : k ≤ K) :
    ∑ i, normalizedSpectralCoefficient
        (spectralKrylovResidual frequency K x) i *
          (frequency i : ℂ) ^ k = 0 := by
  rw [show (∑ i, normalizedSpectralCoefficient
      (spectralKrylovResidual frequency K x) i * (frequency i : ℂ) ^ k) =
      ((Real.sqrt (d : ℝ))⁻¹ : ℂ) *
        ∑ i, spectralKrylovResidual frequency K x i *
          (frequency i : ℂ) ^ k by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    unfold normalizedSpectralCoefficient
    ring]
  rw [spectralKrylovResidual_moment_zero frequency K x hk, mul_zero]

/-- Carrier-plus-tail bound: for `d > 0`, `|t| ≤ T` and `|ω_i| ≤ B` with `0 ≤ B`,
`|A_x(t)| ≤ ‖P x‖ + ‖x - P x‖ B^{K+1} |t|^{K+1} / (K+1)!`. -/
theorem norm_normalizedSpectralAmplitude_le_krylovCarrier_add_factorial
    {d : ℕ} (hd : 0 < d) {frequency : Fin d → ℝ}
    {K : ℕ} {T B t : ℝ} (x : EuclideanSpace ℂ (Fin d))
    (ht : |t| ≤ T) (hB : 0 ≤ B) (hfrequency : ∀ i, ‖frequency i‖ ≤ B) :
    ‖normalizedSpectralAmplitude x frequency t‖ ≤
      ‖spectralKrylovCarrier frequency K x‖ +
        (‖spectralKrylovResidual frequency K x‖ * B ^ (K + 1)) *
          |t| ^ (K + 1) / (K + 1).factorial := by
  let carrier := spectralKrylovCarrier frequency K x
  let residual := spectralKrylovResidual frequency K x
  have hsplit : x = carrier + residual := by
    dsimp [carrier, residual, spectralKrylovResidual]
    abel
  have hres := norm_finiteRealTimeComplexAmplitude_le_of_moment_null_abs
    (coefficient := normalizedSpectralCoefficient residual)
    (frequency := frequency) (K := K) (T := T)
    (A := ‖residual‖) (B := B) (t := t) ht
    (sum_norm_normalizedSpectralCoefficient_le_norm hd residual)
    hB hfrequency
    (fun k hk => normalizedSpectralCoefficient_residual_moment_zero
      frequency K x hk)
  have hamp : normalizedSpectralAmplitude x frequency t =
      normalizedSpectralAmplitude carrier frequency t +
        normalizedSpectralAmplitude residual frequency t := by
    conv_lhs => rw [hsplit]
    exact normalizedSpectralAmplitude_add carrier residual frequency t
  rw [hamp]
  simpa [carrier, residual] using (norm_add_le
    (normalizedSpectralAmplitude carrier frequency t)
    (normalizedSpectralAmplitude residual frequency t)).trans (add_le_add
      (norm_normalizedSpectralAmplitude_le_norm hd carrier frequency t) hres)

/-- Unit-ball form: if moreover `‖x‖ ≤ 1`, then
`|A_x(t)| ≤ ‖P x‖ + B^{K+1} |t|^{K+1} / (K+1)!`. -/
theorem norm_normalizedSpectralAmplitude_le_krylovCarrier_add_unit_factorial
    {d : ℕ} (hd : 0 < d) {frequency : Fin d → ℝ}
    {K : ℕ} {T B t : ℝ} {x : EuclideanSpace ℂ (Fin d)}
    (hx : ‖x‖ ≤ 1) (ht : |t| ≤ T) (hB : 0 ≤ B)
    (hfrequency : ∀ i, ‖frequency i‖ ≤ B) :
    ‖normalizedSpectralAmplitude x frequency t‖ ≤
      ‖spectralKrylovCarrier frequency K x‖ +
        B ^ (K + 1) * |t| ^ (K + 1) / (K + 1).factorial := by
  have hmain := norm_normalizedSpectralAmplitude_le_krylovCarrier_add_factorial
    (K := K) hd x ht hB hfrequency
  have hres : ‖spectralKrylovResidual frequency K x‖ ≤ 1 :=
    (norm_spectralKrylovResidual_le frequency K x).trans hx
  have hfactor :
      0 ≤ B ^ (K + 1) * |t| ^ (K + 1) / (K + 1).factorial := by
    positivity
  calc
    ‖normalizedSpectralAmplitude x frequency t‖ ≤
        ‖spectralKrylovCarrier frequency K x‖ +
          (‖spectralKrylovResidual frequency K x‖ * B ^ (K + 1)) *
            |t| ^ (K + 1) / (K + 1).factorial := hmain
    _ ≤ ‖spectralKrylovCarrier frequency K x‖ +
        B ^ (K + 1) * |t| ^ (K + 1) / (K + 1).factorial := by
      calc
        ‖spectralKrylovCarrier frequency K x‖ +
            (‖spectralKrylovResidual frequency K x‖ * B ^ (K + 1)) *
              |t| ^ (K + 1) / (K + 1).factorial =
            ‖spectralKrylovCarrier frequency K x‖ +
              ‖spectralKrylovResidual frequency K x‖ *
                (B ^ (K + 1) * |t| ^ (K + 1) / (K + 1).factorial) := by ring
        _ ≤ ‖spectralKrylovCarrier frequency K x‖ +
              1 * (B ^ (K + 1) * |t| ^ (K + 1) / (K + 1).factorial) :=
          add_le_add le_rfl (mul_le_mul_of_nonneg_right hres hfactor)
        _ = _ := by ring

/-- A large amplitude forces a large carrier: if `‖x‖ ≤ 1`, `|ω_i| ≤ B` and `θ ≤ |A_x(t)|`, then
`θ - B^{K+1} |t|^{K+1} / (K+1)! ≤ ‖P x‖`. -/
theorem krylovCarrier_norm_ge_of_large_normalizedSpectralAmplitude
    {d : ℕ} (hd : 0 < d) {frequency : Fin d → ℝ}
    {K : ℕ} {T B t theta : ℝ} {x : EuclideanSpace ℂ (Fin d)}
    (hx : ‖x‖ ≤ 1) (ht : |t| ≤ T) (hB : 0 ≤ B)
    (hfrequency : ∀ i, ‖frequency i‖ ≤ B)
    (hlarge : theta ≤ ‖normalizedSpectralAmplitude x frequency t‖) :
    theta - B ^ (K + 1) * |t| ^ (K + 1) / (K + 1).factorial ≤
      ‖spectralKrylovCarrier frequency K x‖ := by
  have hupper := norm_normalizedSpectralAmplitude_le_krylovCarrier_add_unit_factorial
    (K := K) hd hx ht hB hfrequency
  linarith

/-- Total carrier load `Σ_w ‖P x_w‖²` of a finite family of targets. -/
def finiteKrylovCarrierLoad
    {d : ℕ} {W : Type*} [Fintype W]
    (target : W → EuclideanSpace ℂ (Fin d))
    (frequency : Fin d → ℝ) (K : ℕ) : ℝ :=
  ∑ w, ‖spectralKrylovCarrier frequency K (target w)‖ ^ (2 : ℕ)

/-- Each carrier norm is at most the square root of the total carrier load. -/
theorem krylovCarrier_norm_le_sqrt_finiteLoad
    {d : ℕ} {W : Type*} [Fintype W]
    (target : W → EuclideanSpace ℂ (Fin d))
    (frequency : Fin d → ℝ) (K : ℕ) (w : W) :
    ‖spectralKrylovCarrier frequency K (target w)‖ ≤
      Real.sqrt (finiteKrylovCarrierLoad target frequency K) := by
  have hterm : ‖spectralKrylovCarrier frequency K (target w)‖ ^ (2 : ℕ) ≤
      finiteKrylovCarrierLoad target frequency K := by
    unfold finiteKrylovCarrierLoad
    exact Finset.single_le_sum (fun v hv => sq_nonneg
      ‖spectralKrylovCarrier frequency K (target v)‖) (Finset.mem_univ w)
  have hload : 0 ≤ finiteKrylovCarrierLoad target frequency K := by
    unfold finiteKrylovCarrierLoad
    positivity
  have hs := Real.sqrt_le_sqrt hterm
  simpa [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)] using hs

/-- For unit-norm targets, `|A_{x_w}(t)| ≤ √(Σ_v ‖P x_v‖²) + B^{K+1} |t|^{K+1} / (K+1)!`. -/
theorem norm_normalizedSpectralAmplitude_le_sqrt_finiteKrylovLoad_add_factorial
    {d : ℕ} (hd : 0 < d) {W : Type*} [Fintype W]
    {target : W → EuclideanSpace ℂ (Fin d)}
    (htarget : ∀ w, ‖target w‖ ≤ 1)
    {frequency : Fin d → ℝ} {K : ℕ} {T B t : ℝ}
    (ht : |t| ≤ T) (hB : 0 ≤ B) (hfrequency : ∀ i, ‖frequency i‖ ≤ B)
    (w : W) :
    ‖normalizedSpectralAmplitude (target w) frequency t‖ ≤
      Real.sqrt (finiteKrylovCarrierLoad target frequency K) +
        B ^ (K + 1) * |t| ^ (K + 1) / (K + 1).factorial := by
  exact (norm_normalizedSpectralAmplitude_le_krylovCarrier_add_unit_factorial
    (K := K) hd (htarget w) ht hB hfrequency).trans
      (add_le_add
        (krylovCarrier_norm_le_sqrt_finiteLoad target frequency K w) le_rfl)

/-- Budget exclusion: for unit-norm targets with `|ω_i| ≤ B`, if
`√(Σ_w ‖P x_w‖²) + B^{K+1} T^{K+1} / (K+1)! < θ`, then `|A_{x_w}(t)| < θ` for all `|t| ≤ T`
and all `w`. -/
theorem no_large_adaptive_amplitude_of_finiteKrylovLoad
    {d : ℕ} (hd : 0 < d) {W : Type*} [Fintype W]
    {target : W → EuclideanSpace ℂ (Fin d)}
    (htarget : ∀ w, ‖target w‖ ≤ 1)
    {frequency : Fin d → ℝ} {K : ℕ} {T B theta : ℝ}
    (hB : 0 ≤ B) (hfrequency : ∀ i, ‖frequency i‖ ≤ B)
    (hbudget : Real.sqrt (finiteKrylovCarrierLoad target frequency K) +
        B ^ (K + 1) * T ^ (K + 1) / (K + 1).factorial < theta) :
    ∀ t, |t| ≤ T → ∀ w,
      ‖normalizedSpectralAmplitude (target w) frequency t‖ < theta := by
  intro t ht w
  have hmain := norm_normalizedSpectralAmplitude_le_sqrt_finiteKrylovLoad_add_factorial
    (K := K) hd htarget ht hB hfrequency w
  have hpow : |t| ^ (K + 1) ≤ T ^ (K + 1) :=
    pow_le_pow_left₀ (abs_nonneg t) ht _
  have hfactor : 0 ≤ B ^ (K + 1) / (K + 1).factorial := by positivity
  have hrem :
      B ^ (K + 1) * |t| ^ (K + 1) / (K + 1).factorial ≤
        B ^ (K + 1) * T ^ (K + 1) / (K + 1).factorial := by
    calc
      B ^ (K + 1) * |t| ^ (K + 1) / (K + 1).factorial =
          (B ^ (K + 1) / (K + 1).factorial) * |t| ^ (K + 1) := by ring
      _ ≤ (B ^ (K + 1) / (K + 1).factorial) * T ^ (K + 1) :=
        mul_le_mul_of_nonneg_left hpow hfactor
      _ = _ := by ring
  exact lt_of_le_of_lt (hmain.trans (add_le_add le_rfl hrem)) hbudget

/-- Replica carrier load `Σ_w ‖P x_w‖^{2r}`. -/
def finiteKrylovCarrierReplicaLoad
    {d : ℕ} {W : Type*} [Fintype W]
    (target : W → EuclideanSpace ℂ (Fin d))
    (frequency : Fin d → ℝ) (K r : ℕ) : ℝ :=
  ∑ w, ‖spectralKrylovCarrier frequency K (target w)‖ ^ (2 * r)

theorem krylovCarrier_pow_le_finiteReplicaLoad
    {d : ℕ} {W : Type*} [Fintype W]
    (target : W → EuclideanSpace ℂ (Fin d))
    (frequency : Fin d → ℝ) (K r : ℕ) (w : W) :
    ‖spectralKrylovCarrier frequency K (target w)‖ ^ (2 * r) ≤
      finiteKrylovCarrierReplicaLoad target frequency K r := by
  unfold finiteKrylovCarrierReplicaLoad
  exact Finset.single_le_sum (fun v hv => pow_nonneg
    (norm_nonneg (spectralKrylovCarrier frequency K (target v))) _)
    (Finset.mem_univ w)

/-- If some unit-norm target has `θ ≤ |A_{x_w}(t)|` and `θ - B^{K+1} |t|^{K+1} / (K+1)! ≥ 0`, then
the replica load is at least `(θ - B^{K+1} |t|^{K+1} / (K+1)!)^{2r}`. -/
theorem finiteKrylovCarrierReplicaLoad_ge_of_large_amplitude
    {d : ℕ} (hd : 0 < d) {W : Type*} [Fintype W]
    {target : W → EuclideanSpace ℂ (Fin d)}
    (htarget : ∀ w, ‖target w‖ ≤ 1)
    {frequency : Fin d → ℝ} {K r : ℕ} {T B theta t : ℝ}
    (ht : |t| ≤ T) (hB : 0 ≤ B) (hfrequency : ∀ i, ‖frequency i‖ ≤ B)
    {w : W} (hlarge : theta ≤ ‖normalizedSpectralAmplitude (target w) frequency t‖)
    (hthreshold : 0 ≤ theta -
      B ^ (K + 1) * |t| ^ (K + 1) / (K + 1).factorial) :
    (theta - B ^ (K + 1) * |t| ^ (K + 1) / (K + 1).factorial) ^
        (2 * r) ≤ finiteKrylovCarrierReplicaLoad target frequency K r := by
  have hcarrier := krylovCarrier_norm_ge_of_large_normalizedSpectralAmplitude
    (K := K) hd (htarget w) ht hB hfrequency hlarge
  exact (pow_le_pow_left₀ hthreshold hcarrier _).trans
    (krylovCarrier_pow_le_finiteReplicaLoad target frequency K r w)

/-- Replica budget exclusion: for unit-norm targets with `|ω_i| ≤ B`, if
`θ - B^{K+1} T^{K+1} / (K+1)! ≥ 0` and `Σ_w ‖P x_w‖^{2r} < (θ - B^{K+1} T^{K+1} / (K+1)!)^{2r}`,
then `|A_{x_w}(t)| < θ` for all `|t| ≤ T` and all `w`. -/
theorem no_large_adaptive_amplitude_of_finiteKrylovReplicaLoad
    {d : ℕ} (hd : 0 < d) {W : Type*} [Fintype W]
    {target : W → EuclideanSpace ℂ (Fin d)}
    (htarget : ∀ w, ‖target w‖ ≤ 1)
    {frequency : Fin d → ℝ} {K r : ℕ} {T B theta : ℝ}
    (hB : 0 ≤ B) (hfrequency : ∀ i, ‖frequency i‖ ≤ B)
    (hthreshold : 0 ≤ theta -
      B ^ (K + 1) * T ^ (K + 1) / (K + 1).factorial)
    (hbudget : finiteKrylovCarrierReplicaLoad target frequency K r <
      (theta - B ^ (K + 1) * T ^ (K + 1) / (K + 1).factorial) ^
        (2 * r)) :
    ∀ t, |t| ≤ T → ∀ w,
      ‖normalizedSpectralAmplitude (target w) frequency t‖ < theta := by
  intro t ht w
  by_contra hnot
  have hlarge : theta ≤ ‖normalizedSpectralAmplitude (target w) frequency t‖ :=
    le_of_not_gt hnot
  have hpow : |t| ^ (K + 1) ≤ T ^ (K + 1) :=
    pow_le_pow_left₀ (abs_nonneg t) ht _
  have hcoef : 0 ≤ B ^ (K + 1) / (K + 1).factorial := by positivity
  have hrem :
      B ^ (K + 1) * |t| ^ (K + 1) / (K + 1).factorial ≤
        B ^ (K + 1) * T ^ (K + 1) / (K + 1).factorial := by
    calc
      B ^ (K + 1) * |t| ^ (K + 1) / (K + 1).factorial =
          (B ^ (K + 1) / (K + 1).factorial) * |t| ^ (K + 1) := by ring
      _ ≤ (B ^ (K + 1) / (K + 1).factorial) * T ^ (K + 1) :=
        mul_le_mul_of_nonneg_left hpow hcoef
      _ = _ := by ring
  have hpointThreshold : 0 ≤ theta -
      B ^ (K + 1) * |t| ^ (K + 1) / (K + 1).factorial := by
    linarith
  have hlower := finiteKrylovCarrierReplicaLoad_ge_of_large_amplitude
    (K := K) (r := r) hd htarget ht hB hfrequency hlarge hpointThreshold
  have hbase : theta - B ^ (K + 1) * T ^ (K + 1) / (K + 1).factorial ≤
      theta - B ^ (K + 1) * |t| ^ (K + 1) / (K + 1).factorial := by
    linarith
  have hpower := pow_le_pow_left₀ hthreshold hbase (2 * r)
  exact (not_lt_of_ge (hpower.trans hlower)) hbudget

end GaloisForLFunctions.HTGeometry
