import GaloisForLFunctions.HTGeometry.PrimeHodgeJordanLift
import GaloisForLFunctions.HTGeometry.AbelianZetaGas.VonMangoldtEuler
import GaloisForLFunctions.RHTower.RoutePPrimitiveCollisionSubquantum
import GaloisForLFunctions.RHTower.XiWardCubicLogMomentEulerSource
import GaloisForLFunctions.RHTower.XiMassPrimePowerVerticalIdeal
import GaloisForLFunctions.RHTower.HedenmalmStokesCompletedResponseCovariantRenormalization

/-!
# The Euler-depth Stokes lift and its moving cubic Gram

On the Euler labels `i = (p, e)`, `n_i = p^{e+1}`, `λ_i = log n_i = (e+1) log p`, the unsigned
right Stokes current is `j_δ(i) = 8δ log(p) n_i^{-(1+2δ)}` (**(ESAC.1)**).  At depth zero it is the
oriented Stokes prime term, and `δ j_δ` is the covariant Stokes moment.  Its depth sums are
geometric, `Σ_e j_δ(p,e) = 8δ log p/(p^{1+2δ}-1)`, and its total is `8δ Σ_n Λ(n) n^{-(1+2δ)}`
(**(ESAC.2)**).

With the unit coherent vectors `ψ^{(3)}_λ` (Gram `k₃(λ,μ) = (2√(λμ)/(λ+μ))³`) the frame
`√j_δ(i) ψ^{(3)}_{λ_i}` has right Gram `A_δ(i,j) = √(j_δ(i)j_δ(j)) k₃(λ_i,λ_j)` (**(ESAC.3)–(ESAC.4)**):
positive, trace class, `Tr A_δ = ‖A_δ‖₁ = Σ_i j_δ(i)`, every entry strictly positive (**(ESAC.5)**).
The aperture integral of `δ j_δ(i)` is the primitive Euler weight:
`(115/1728) ∫₀^∞ δ j_δ(i) dδ = 115/(864 n_i (e+1)³ log² p)` (**(ESAC.7)–(ESAC.9)**).
-/

open MeasureTheory Set Filter Topology
open scoped InnerProductSpace ArithmeticFunction.vonMangoldt

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open _root_.RHTower

/-- The Euler labels `(p, e)`. -/
abbrev EulerLabel := Nat.Primes × ℕ

local notation "ℓ²E" => lp (fun _ : EulerLabel => ℂ) 2

variable {δ : ℝ}

/-- `λ_i = log p^{e+1} = (e+1) log p`. -/
theorem xiGammaEulerPrimitiveLogFrequency_eq (i : EulerLabel) :
    xiGammaEulerPrimitiveLogFrequency i = ((i.2 : ℝ) + 1) * Real.log (i.1 : ℝ) := by
  rw [xiGammaEulerPrimitiveLogFrequency, xiGammaEulerValuationNat, Nat.cast_pow, Real.log_pow]
  push_cast
  ring

theorem eulerValuation_pos (i : EulerLabel) : (0 : ℝ) < (xiGammaEulerValuationNat i : ℝ) := by
  rw [xiGammaEulerValuationNat]
  exact_mod_cast pow_pos i.1.property.pos _

/-- **(ESAC.1)** The Euler-depth Stokes current `j_δ(i) = 8δ log(p) n_i^{-(1+2δ)}`. -/
def eulerStokesCurrent (δ : ℝ) (i : EulerLabel) : ℝ :=
  8 * δ * Real.log (i.1 : ℝ) * (xiGammaEulerValuationNat i : ℝ) ^ (-(1 + 2 * δ))

theorem eulerStokesCurrent_pos (hδ : 0 < δ) (i : EulerLabel) : 0 < eulerStokesCurrent δ i :=
  mul_pos (mul_pos (mul_pos (by norm_num) hδ) (primeClock_pos i.1))
    (Real.rpow_pos_of_pos (eulerValuation_pos i) _)

/-- `j_δ(i) = (8δ log p / n_i) e^{-2δλ_i}`. -/
theorem eulerStokesCurrent_eq_exp (δ : ℝ) (i : EulerLabel) :
    eulerStokesCurrent δ i = 8 * δ * Real.log (i.1 : ℝ) / (xiGammaEulerValuationNat i : ℝ) *
      Real.exp (-(2 * δ * xiGammaEulerPrimitiveLogFrequency i)) := by
  have hn := eulerValuation_pos i
  rw [eulerStokesCurrent, Real.rpow_def_of_pos hn, xiGammaEulerPrimitiveLogFrequency,
    show Real.log (xiGammaEulerValuationNat i : ℝ) * -(1 + 2 * δ) =
      -Real.log (xiGammaEulerValuationNat i : ℝ) + -(2 * δ * Real.log (xiGammaEulerValuationNat i : ℝ))
      by ring, Real.exp_add, Real.exp_neg (Real.log _), Real.exp_log hn]
  field_simp

/-- At depth zero the Euler current is the oriented Stokes prime term. -/
theorem eulerStokesCurrent_depth_zero (hδ : 0 < δ) (p : Nat.Primes) :
    eulerStokesCurrent δ (p, 0) = gammaSewnMobiusApertureStokesOrientedFirstTracePrimeTerm δ p := by
  rw [eulerStokesCurrent, gammaSewnMobiusApertureStokesOrientedFirstTracePrimeTerm,
    xiMassPrimeSquareEulerWeight_eq, abs_of_pos hδ, xiGammaEulerValuationNat, zero_add, pow_one]
  ring

/-- The covariant Stokes energy `δ j_δ` is, at depth zero, the covariant Stokes prime moment. -/
theorem mul_eulerStokesCurrent_depth_zero (hδ : 0 < δ) (p : Nat.Primes) :
    δ * eulerStokesCurrent δ (p, 0) = gammaSewnMobiusApertureStokesCovariantFirstTracePrimeMoment δ p := by
  rw [gammaSewnMobiusApertureStokesCovariantFirstTracePrimeMoment_eq δ hδ.le, eulerStokesCurrent,
    xiGammaEulerValuationNat, zero_add, pow_one]
  ring

theorem rpow_eulerValuation (i : EulerLabel) (σ : ℝ) :
    (xiGammaEulerValuationNat i : ℝ) ^ (-σ) = (i.1 : ℝ) ^ (-(((i.2 : ℝ) + 1) * σ)) := by
  have hp : (0 : ℝ) ≤ (i.1 : ℝ) := Nat.cast_nonneg _
  rw [xiGammaEulerValuationNat, Nat.cast_pow, ← Real.rpow_natCast, ← Real.rpow_mul hp]
  push_cast
  ring_nf

/-- **(ESAC.2), depth sum.**  `Σ_e j_δ(p,e) = 8δ log p/(p^{1+2δ} - 1)`. -/
theorem hasSum_eulerStokesCurrent_depth (hδ : 0 < δ) (p : Nat.Primes) :
    HasSum (fun e => eulerStokesCurrent δ (p, e))
      (8 * δ * Real.log (p : ℝ) / ((p : ℝ) ^ (1 + 2 * δ) - 1)) := by
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast p.property.one_lt
  have hp0 : (0 : ℝ) ≤ (p : ℝ) := by linarith
  obtain ⟨x, hx⟩ : ∃ x : ℝ, x = (p : ℝ) ^ (-(1 + 2 * δ)) := ⟨_, rfl⟩
  have hx0 : 0 ≤ x := hx ▸ Real.rpow_nonneg hp0 _
  have hx1 : x < 1 := hx ▸ Real.rpow_lt_one_of_one_lt_of_neg hp1 (by linarith)
  have hterm : ∀ e : ℕ, eulerStokesCurrent δ (p, e) = 8 * δ * Real.log (p : ℝ) * x * x ^ e := by
    intro e
    have hv : ((xiGammaEulerValuationNat (p, e) : ℕ) : ℝ) = (p : ℝ) ^ (e + 1) := by
      rw [xiGammaEulerValuationNat]
      push_cast
      rfl
    have hr : ((p : ℝ) ^ (e + 1)) ^ (-(1 + 2 * δ)) = x * x ^ e := by
      rw [hx, ← Real.rpow_natCast, ← Real.rpow_mul hp0, ← Real.rpow_natCast _ e, ← Real.rpow_mul hp0,
        ← Real.rpow_add (by linarith)]
      congr 1
      push_cast
      ring
    rw [eulerStokesCurrent, hv, hr]
    ring
  have hgeo := (hasSum_geometric_of_lt_one hx0 hx1).mul_left (8 * δ * Real.log (p : ℝ) * x)
  have hval : 8 * δ * Real.log (p : ℝ) * x * (1 - x)⁻¹ =
      8 * δ * Real.log (p : ℝ) / ((p : ℝ) ^ (1 + 2 * δ) - 1) := by
    have hpp : 0 < (p : ℝ) ^ (1 + 2 * δ) := Real.rpow_pos_of_pos (by linarith) _
    have hx' : x = ((p : ℝ) ^ (1 + 2 * δ))⁻¹ := hx.trans (Real.rpow_neg hp0 _)
    have hgt : 1 < (p : ℝ) ^ (1 + 2 * δ) := Real.one_lt_rpow hp1 (by linarith)
    rw [hx']
    field_simp
  rw [← hval]
  exact hgeo.congr_fun fun e => hterm e

theorem eulerStokesCurrent_le (hδ : 0 < δ) (i : EulerLabel) :
    eulerStokesCurrent δ i ≤
      8 * δ * (Real.log (i.1 : ℝ) * ((i.1 : ℝ)⁻¹) ^ ((i.2 : ℝ) + (1 + 2 * δ))) := by
  have hp1 : (1 : ℝ) ≤ (i.1 : ℝ) := by exact_mod_cast i.1.property.one_lt.le
  have hp0 : (0 : ℝ) < (i.1 : ℝ) := by linarith
  rw [eulerStokesCurrent, rpow_eulerValuation, Real.inv_rpow hp0.le, ← Real.rpow_neg hp0.le, mul_assoc]
  refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hp1 ?_) (primeClock_pos i.1).le) (by positivity)
  nlinarith [(Nat.cast_nonneg i.2 : (0 : ℝ) ≤ i.2)]

theorem summable_eulerStokesCurrent (hδ : 0 < δ) : Summable (eulerStokesCurrent δ) :=
  Summable.of_nonneg_of_le (fun i => (eulerStokesCurrent_pos hδ i).le) (eulerStokesCurrent_le hδ)
    ((summable_primeLog_mul_inv_rpow_add (1 + 2 * δ) (by linarith)).mul_left (8 * δ))

/-- **(ESAC.2), total.**  `Σ_i j_δ(i) = 8δ Σ_{n ≥ 2} Λ(n) n^{-(1+2δ)}`. -/
theorem tsum_eulerStokesCurrent (hδ : 0 < δ) :
    ∑' i, eulerStokesCurrent δ i = 8 * δ * ∑' n : ℕ, Λ n * (n : ℝ) ^ (-(1 + 2 * δ)) := by
  rw [tsum_vonMangoldt_eq_tsum_primes (by linarith : (1 : ℝ) < 1 + 2 * δ),
    (summable_eulerStokesCurrent hδ).tsum_prod, ← tsum_mul_left]
  refine tsum_congr fun p => ?_
  rw [← tsum_mul_left, ← tsum_mul_left]
  refine tsum_congr fun e => ?_
  rw [eulerStokesCurrent, rpow_eulerValuation]
  ring

/-! ## The moving cubic Gram -/

/-- The frame vector `√j_δ(i) ψ^{(3)}_{λ_i}`. -/
def eulerStokesFrame (δ : ℝ) (i : EulerLabel) : HalfLineL2 :=
  ((Real.sqrt (eulerStokesCurrent δ i) : ℝ) : ℂ) •
    gammaCoherentVector 3 (xiGammaEulerPrimitiveLogFrequency_pos i)

theorem norm_sq_eulerStokesFrame (hδ : 0 < δ) (i : EulerLabel) :
    ‖eulerStokesFrame δ i‖ ^ 2 = eulerStokesCurrent δ i := by
  rw [eulerStokesFrame, norm_smul, norm_gammaCoherentVector, mul_one, Complex.norm_real,
    Real.norm_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (eulerStokesCurrent_pos hδ i).le]

theorem summable_norm_sq_eulerStokesFrame (hδ : 0 < δ) :
    Summable fun i => ‖eulerStokesFrame δ i‖ ^ 2 := by
  simp_rw [norm_sq_eulerStokesFrame hδ]
  exact summable_eulerStokesCurrent hδ

/-- The synthesis `W_δ : ℓ²(I) → L²(0,∞)`. -/
def eulerStokesSynthesis (hδ : 0 < δ) : ℓ²E →L[ℂ] HalfLineL2 :=
  squareSummableSynthesis (eulerStokesFrame δ) (summable_norm_sq_eulerStokesFrame hδ)

/-- **(ESAC.4)** The moving cubic Gram `A_δ = W_δ^* W_δ`. -/
def eulerStokesGram (hδ : 0 < δ) : ℓ²E →L[ℂ] ℓ²E :=
  ContinuousLinearMap.adjoint (eulerStokesSynthesis hδ) ∘L eulerStokesSynthesis hδ

/-- The cubic coherence `k₃(λ, μ) = (2√(λμ)/(λ+μ))³`. -/
def cubicCoherence (s t : ℝ) : ℝ := (2 * Real.sqrt (s * t) / (s + t)) ^ 3

/-- **(ESAC.4)** `A_δ(i,j) = √(j_δ(i) j_δ(j)) k₃(λ_i, λ_j)`. -/
theorem inner_single_eulerStokesGram (hδ : 0 < δ) (i j : EulerLabel) :
    ⟪(lp.single 2 i (1 : ℂ) : ℓ²E), eulerStokesGram hδ (lp.single 2 j 1)⟫_ℂ =
      ((Real.sqrt (eulerStokesCurrent δ i * eulerStokesCurrent δ j) *
        cubicCoherence (xiGammaEulerPrimitiveLogFrequency i) (xiGammaEulerPrimitiveLogFrequency j) :
          ℝ) : ℂ) := by
  rw [eulerStokesGram, eulerStokesSynthesis, inner_single_rightGram_single, eulerStokesFrame,
    eulerStokesFrame, inner_smul_left, inner_smul_right, inner_gammaCoherentVector, Complex.conj_ofReal,
    Real.sqrt_mul (eulerStokesCurrent_pos hδ i).le, cubicCoherence]
  push_cast
  ring

/-- **(ESAC.5)** `A_δ ≥ 0`, `A_δ ∈ 𝒮₁`, `Tr A_δ = ‖A_δ‖₁ = Σ_i j_δ(i)`. -/
theorem eulerStokesGram_traceClass (hδ : 0 < δ) :
    (eulerStokesGram hδ).IsPositive ∧ MemSchattenClass 1 (eulerStokesGram hδ) ∧
      (eulerStokesGram hδ).opTrace = ((∑' i, eulerStokesCurrent δ i : ℝ) : ℂ) ∧
      traceNorm ℓ²E (eulerStokesGram hδ) = ∑' i, eulerStokesCurrent δ i := by
  obtain ⟨hpos, hS, htr⟩ := rightGram_traceClass (summable_norm_sq_eulerStokesFrame hδ)
  simp_rw [norm_sq_eulerStokesFrame hδ] at htr
  refine ⟨hpos, hS, htr, ?_⟩
  exact (traceNorm_eq_re_opTrace_of_isPositive hS hpos).trans (by rw [htr, Complex.ofReal_re])

/-- **(ESAC.5)** Every entry of `A_δ` is strictly positive: prime and depth are mixed. -/
theorem inner_single_eulerStokesGram_pos (hδ : 0 < δ) (i j : EulerLabel) :
    0 < (Real.sqrt (eulerStokesCurrent δ i * eulerStokesCurrent δ j) *
      cubicCoherence (xiGammaEulerPrimitiveLogFrequency i) (xiGammaEulerPrimitiveLogFrequency j)) := by
  have hi := xiGammaEulerPrimitiveLogFrequency_pos i
  have hj := xiGammaEulerPrimitiveLogFrequency_pos j
  refine mul_pos (Real.sqrt_pos.2 (mul_pos (eulerStokesCurrent_pos hδ i) (eulerStokesCurrent_pos hδ j)))
    (pow_pos (div_pos (mul_pos two_pos (Real.sqrt_pos.2 (mul_pos hi hj))) (add_pos hi hj)) 3)

/-! ## The aperture integral of the diagonal -/

/-- **(ESAC.7)** `∫₀^∞ δ² e^{-2λδ} dδ = 1/(4λ³)`. -/
theorem integral_sq_mul_exp_neg_two_mul {s : ℝ} (hs : 0 < s) :
    ∫ δ in Ioi (0 : ℝ), δ ^ 2 * Real.exp (-(2 * s * δ)) = 1 / (4 * s ^ 3) := by
  rw [(integral_exp_neg_moments (by positivity : (0 : ℝ) < 2 * s)).2.2]
  field_simp
  ring

/-- **(ESAC.8)** `(115/1728) ∫₀^∞ δ j_δ(i) dδ = 115/(864 n_i (e+1)³ log² p)`, the primitive Euler weight. -/
theorem integral_mul_eulerStokesCurrent (i : EulerLabel) :
    (115 / 1728 : ℝ) * ∫ δ in Ioi (0 : ℝ), δ * eulerStokesCurrent δ i =
      xiGammaEulerPrimitiveCubicLogMomentWeight i := by
  have hlam := xiGammaEulerPrimitiveLogFrequency_pos i
  have hn := eulerValuation_pos i
  have hp := primeClock_pos i.1
  have hfun : (fun δ => δ * eulerStokesCurrent δ i) = fun δ =>
      (8 * Real.log (i.1 : ℝ) / (xiGammaEulerValuationNat i : ℝ)) *
        (δ ^ 2 * Real.exp (-(2 * xiGammaEulerPrimitiveLogFrequency i * δ))) := by
    funext δ
    rw [eulerStokesCurrent_eq_exp]
    ring_nf
  rw [hfun, integral_const_mul, integral_sq_mul_exp_neg_two_mul hlam,
    xiGammaEulerPrimitiveLogFrequency_eq, xiGammaEulerPrimitiveCubicLogMomentWeight, invNatLogSq,
    xiGammaEulerValuationNat, Nat.cast_pow, pow_succ]
  have hp0 : (0 : ℝ) < (i.1 : ℝ) := by exact_mod_cast i.1.property.pos
  have he : (0 : ℝ) < (i.2 : ℝ) + 1 := by positivity
  rw [inv_pow]
  field_simp
  ring

/-- **(ESAC.9)** The diagonal capacity is the complete primitive collision budget. -/
theorem tsum_integral_mul_eulerStokesCurrent :
    ∑' i : EulerLabel, (115 / 1728 : ℝ) * ∫ δ in Ioi (0 : ℝ), δ * eulerStokesCurrent δ i =
      routePPrimitiveCollisionCubicTraceBudget := by
  simp_rw [integral_mul_eulerStokesCurrent]
  rfl

end GaloisForLFunctions.HTGeometry
