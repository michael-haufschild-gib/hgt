import GaloisForLFunctions.SignedArithmeticEnergyIncidence.TheSourceOnTheCriticalLineIsZetaOverZeta
import GaloisForLFunctions.RHTower.Sieve.DirichletMVT
import GaloisForLFunctions.RHTower.BoseCumulantJets

/-!
# The chain is bounded at half damping

The centred damping chain is bounded on `ℓ²` uniformly for `½ < η < 1`
(`exists_centeredOperator_l2_le_uniform`), hence at half damping itself
(`exists_centeredOperator_l2_le_half`), where it is not Hilbert–Schmidt
(`not_bounded_sum_sum_sq_centeredRow_of_le_half`).

**Proof.**  For finitely supported `b`, `(C_η b)(n) = G(N)/N` with the combined profile
`G = Σ_k K b_k Δ_K` (`centeredOperator_apply_eq_combinedProfile`); on `[N, N+1)` the floors in `G`
do not move, so `Σ_n (C_η b)(n)² ≤ 8 ∫_0^∞ G² x^{−2} + 32 ‖b‖²` (`sum_sq_centeredOperator_le`).
In Mellin coordinates `M G = B · M P` on `Re s = −½` (`mellin_combinedProfile_eq`), with the
dilation symbol `B(t) = Σ_k K b_k (K^z − (K+1)^z)`, `z = −½ − η + it`.  The symbol is controlled
in mean square on dyadic heights `T ≤ t ≤ 2T`:
* its head `K ≤ X` is the Dirichlet polynomial `Σ_{n ≤ X} a_n (n+1)^{it}` with `Σ |a_n|² ≤ 4‖b‖²`
  (`head_eq_dirPoly`), so the mean value theorem gives `≪ (T + X log X) ‖b‖²`;
* its tail `K > X` is `−z` times the Fourier transform of a step function in `log x`
  (`tail_eq_neg_mul_fourier`), so Plancherel gives `≪ T² ‖b‖²/X`.
With `X ≈ T` the symbol costs `≪ T log T ‖b‖²`, while `|M P|² ≪ T^{3/4} log⁴T / T²` there
(`exists_norm_mellin_sourceProfile_sq_le`); the dyadic sum converges.  The bound is uniform as
`η ↓ ½` because `1/ζ` stays `≪ log² t` on the `1`-line, and the entries of the chain are continuous
in `η`.

The signs of `μ` enter through `1/ζ(1 + it) ≪ log² t`: the positive twin is not admitted at half
damping (mechanism 35), so no sign-blind argument reaches `η = ½`.
-/

open MeasureTheory Set Filter Topology Complex
open scoped ZeroAtInfty FourierTransform
open GaloisForLFunctions.BezoutValuationIncidence GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy

namespace GaloisForLFunctions.SignedArithmeticEnergyIncidence

noncomputable section
set_option autoImplicit false

/-! ### Plancherel helpers -/

/-- The squared Fourier transform of an integrable `L²` function is integrable. -/
theorem integrable_norm_sq_fourier {φ : ℝ → ℂ} (hφ : Integrable φ) (hφ2 : MemLp φ 2) :
    Integrable (fun ξ => ‖𝓕 φ ξ‖ ^ 2) := by
  set u : Lp ℂ 2 (volume : Measure ℝ) := hφ2.toLp φ
  have hcoe : (u : ℝ → ℂ) =ᵐ[volume] φ := hφ2.coeFn_toLp
  have hint : Integrable (u : ℝ → ℂ) := hφ.congr hcoe.symm
  have hF : ((𝓕 u : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) =ᵐ[volume] 𝓕 φ := by
    refine (GaloisForLFunctions.HTGeometry.coeFn_fourierTransform_eq_fourierIntegral u
      hint).trans ?_
    filter_upwards with ξ
    exact Real.fourier_congr_ae hcoe ξ
  have hmem := Lp.memLp (𝓕 u : Lp ℂ 2 (volume : Measure ℝ))
  have hsq := (memLp_two_iff_integrable_sq_norm hmem.1).mp hmem
  exact hsq.congr (hF.fun_comp fun z => ‖z‖ ^ 2)

/-- `Σ_{n<M} b_n² ≤ Σ_{n<N} b_n²` for `b` supported below `N`. -/
theorem sum_sq_range_le_of_support {b : ℕ → ℝ} {N : ℕ} (hb : ∀ k, N ≤ k → b k = 0) (M : ℕ) :
    ∑ n ∈ Finset.range M, b n ^ 2 ≤ ∑ n ∈ Finset.range N, b n ^ 2 := by
  have h1 : ∑ n ∈ Finset.range M, b n ^ 2 = ∑ n ∈ Finset.range (min M N), b n ^ 2 := by
    refine (Finset.sum_subset (Finset.range_subset_range.mpr (min_le_left M N)) fun n hn hn' => ?_).symm
    have hnN : N ≤ n := by
      simp only [Finset.mem_range, lt_min_iff, not_and_or, not_lt] at hn hn'
      omega
    rw [hb n hnN]; ring
  rw [h1]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr (min_le_right M N))
    fun n _ _ => sq_nonneg _

/-! ### The dilation symbol -/

/-- The term `K b_k (K^z − (K+1)^z)` of the dilation symbol, `K = k + 1`, `z = −½ − η + it`. -/
def dilationTerm (η : ℝ) (b : ℕ → ℝ) (t : ℝ) (k : ℕ) : ℂ :=
  ((((k + 1 : ℕ) : ℝ) * b k : ℝ) : ℂ) *
    ((((k + 1 : ℕ) : ℝ) : ℂ) ^ ((((-1 / 2 : ℝ) : ℂ) + t * I) - η) -
      ((((k + 1 : ℕ) : ℝ) + 1 : ℝ) : ℂ) ^ ((((-1 / 2 : ℝ) : ℂ) + t * I) - η))

/-- The dilation symbol `B(t) = Σ_{k<N} K b_k (K^z − (K+1)^z)`. -/
def dilationSymbol (η : ℝ) (N : ℕ) (b : ℕ → ℝ) (t : ℝ) : ℂ :=
  ∑ k ∈ Finset.range N, dilationTerm η b t k

/-- The combined profile `G = Σ_{k<N} K b_k Δ_K`. -/
def combinedProfile (η : ℝ) (N : ℕ) (b : ℕ → ℝ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range N, ((k + 1 : ℕ) : ℝ) * b k * columnProfile η ((k + 1 : ℕ) : ℝ) x

theorem one_le_succ_cast (k : ℕ) : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by
  exact_mod_cast Nat.succ_le_succ (Nat.zero_le k)

/-- **The chain acts through the combined profile**: `(C_η b)(n) = G(n+1)/(n+1)`. -/
theorem centeredOperator_apply_eq_combinedProfile {η : ℝ} (hη : 0 < η) (b : C₀(ℕ, ℝ)) {N : ℕ}
    (hb : ∀ k, N ≤ k → b k = 0) (n : ℕ) :
    arithmeticDampingCenteredOperator hη b n =
      combinedProfile η N b ((n + 1 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ) := by
  rw [arithmeticDampingCenteredOperator_apply, tsum_eq_sum (s := Finset.range N) fun k hk => by
    rw [hb k (by simpa using hk), mul_zero]]
  unfold combinedProfile
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [centeredRow_eq_columnProfile]
  have hN : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  field_simp

theorem measurable_combinedProfile (η : ℝ) (N : ℕ) (b : ℕ → ℝ) :
    Measurable (combinedProfile η N b) := by
  unfold combinedProfile
  exact Finset.measurable_sum _ fun k _ =>
    measurable_const.mul (measurable_columnProfile η _)

/-- Two-sided bound for the combined profile. -/
theorem abs_combinedProfile_le_bound {η : ℝ} (h0 : 1 / 2 < η) (h1 : η < 1) (N : ℕ)
    (b : ℕ → ℝ) {x : ℝ} (hx : 0 < x) :
    |combinedProfile η N b x| ≤
        (∑ k ∈ Finset.range N, ((k + 1 : ℕ) : ℝ) * |b k|) * (2 * sourceBound η) * x ^ η ∧
      |combinedProfile η N b x| ≤
        (∑ k ∈ Finset.range N, ((k + 1 : ℕ) : ℝ) * |b k|) * (2 * sourceBound η) * x ^ (1 - η) := by
  have piece : ∀ e : ℝ, (∀ k ∈ Finset.range N,
      |columnProfile η ((k + 1 : ℕ) : ℝ) x| ≤ 2 * sourceBound η * x ^ e) →
      |combinedProfile η N b x| ≤
        (∑ k ∈ Finset.range N, ((k + 1 : ℕ) : ℝ) * |b k|) * (2 * sourceBound η) * x ^ e := by
    intro e h
    unfold combinedProfile
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_le_sum fun k hk => ?_
    rw [abs_mul, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < ((k + 1 : ℕ) : ℝ))]
    calc ((k + 1 : ℕ) : ℝ) * |b k| * |columnProfile η ((k + 1 : ℕ) : ℝ) x|
        ≤ ((k + 1 : ℕ) : ℝ) * |b k| * (2 * sourceBound η * x ^ e) :=
          mul_le_mul_of_nonneg_left (h k hk) (by positivity)
      _ = _ := by ring
  exact ⟨piece η fun k _ => (abs_columnProfile_le_bound h0 h1 (one_le_succ_cast k) hx).1,
    piece (1 - η) fun k _ => (abs_columnProfile_le_bound h0 h1 (one_le_succ_cast k) hx).2⟩

/-- **The combined profile in Mellin coordinates**: `M G = B · M P` on `Re s = −½`. -/
theorem mellin_combinedProfile_eq {η : ℝ} (h0 : 1 / 2 < η) (h1 : η < 1) (N : ℕ) (b : ℕ → ℝ)
    (t : ℝ) :
    mellin (fun x => (combinedProfile η N b x : ℂ)) (((-1 / 2 : ℝ) : ℂ) + t * I) =
      dilationSymbol η N b t *
        mellin (fun x => (sourceProfile η x : ℂ)) (((-1 / 2 : ℝ) : ℂ) + t * I) := by
  have hconv : ∀ k : ℕ, MellinConvergent (fun x => (columnProfile η ((k + 1 : ℕ) : ℝ) x : ℂ))
      (((-1 / 2 : ℝ) : ℂ) + t * I) := fun k =>
    mellinConvergent_of_two_sided (measurable_columnProfile η _) h0
      (fun _ hx => (abs_columnProfile_le_bound h0 h1 (one_le_succ_cast k) hx).1)
      (fun _ hx => (abs_columnProfile_le_bound h0 h1 (one_le_succ_cast k) hx).2) t
  have hform : ∀ k : ℕ, (fun x : ℝ => (x : ℂ) ^ ((((-1 / 2 : ℝ) : ℂ) + t * I) - 1) •
      ((((k + 1 : ℕ) : ℝ) * b k * columnProfile η ((k + 1 : ℕ) : ℝ) x : ℝ) : ℂ)) =
      fun x : ℝ => ((((k + 1 : ℕ) : ℝ) * b k : ℝ) : ℂ) *
        ((x : ℂ) ^ ((((-1 / 2 : ℝ) : ℂ) + t * I) - 1) •
          ((columnProfile η ((k + 1 : ℕ) : ℝ) x : ℝ) : ℂ)) := by
    intro k; funext x
    simp only [smul_eq_mul, Complex.ofReal_mul]
    ring
  have hint : ∀ k ∈ Finset.range N, Integrable (fun x : ℝ =>
      (x : ℂ) ^ ((((-1 / 2 : ℝ) : ℂ) + t * I) - 1) •
        ((((k + 1 : ℕ) : ℝ) * b k * columnProfile η ((k + 1 : ℕ) : ℝ) x : ℝ) : ℂ))
      (volume.restrict (Ioi 0)) := by
    intro k _
    rw [hform k]
    exact Integrable.const_mul (hconv k) _
  have hk : ∀ k : ℕ, ∫ (x : ℝ) in Ioi (0 : ℝ), (x : ℂ) ^ ((((-1 / 2 : ℝ) : ℂ) + t * I) - 1) •
      ((((k + 1 : ℕ) : ℝ) * b k * columnProfile η ((k + 1 : ℕ) : ℝ) x : ℝ) : ℂ) =
      dilationTerm η b t k *
        mellin (fun x => (sourceProfile η x : ℂ)) (((-1 / 2 : ℝ) : ℂ) + t * I) := by
    intro k
    rw [hform k, integral_const_mul,
      show (∫ (x : ℝ) in Ioi (0 : ℝ), (x : ℂ) ^ ((((-1 / 2 : ℝ) : ℂ) + t * I) - 1) •
          ((columnProfile η ((k + 1 : ℕ) : ℝ) x : ℝ) : ℂ)) =
        mellin (fun x => (columnProfile η ((k + 1 : ℕ) : ℝ) x : ℂ))
          (((-1 / 2 : ℝ) : ℂ) + t * I) from rfl,
      mellin_columnProfile_eq h0 h1 (one_le_succ_cast k) t]
    unfold dilationTerm
    ring
  have hpt : ∀ x : ℝ, (x : ℂ) ^ ((((-1 / 2 : ℝ) : ℂ) + t * I) - 1) •
      ((combinedProfile η N b x : ℝ) : ℂ) =
      ∑ k ∈ Finset.range N, (x : ℂ) ^ ((((-1 / 2 : ℝ) : ℂ) + t * I) - 1) •
        ((((k + 1 : ℕ) : ℝ) * b k * columnProfile η ((k + 1 : ℕ) : ℝ) x : ℝ) : ℂ) := by
    intro x
    rw [combinedProfile, Complex.ofReal_sum, Finset.smul_sum]
  unfold mellin
  rw [setIntegral_congr_fun measurableSet_Ioi (fun x _ => hpt x), integral_finsetSum _ hint,
    Finset.sum_congr rfl fun k _ => hk k, ← Finset.sum_mul]
  rfl

/-! ### Pointwise size of the symbol -/

/-- `‖K b_k (K^z − (K+1)^z)‖ ≤ ‖z‖ |b_k| / K`. -/
theorem norm_dilationTerm_le {η : ℝ} (h0 : 1 / 2 < η) (b : ℕ → ℝ) (t : ℝ) (k : ℕ) :
    ‖dilationTerm η b t k‖ ≤
      ‖(((-1 / 2 : ℝ) : ℂ) + t * I) - η‖ * (|b k| / ((k + 1 : ℕ) : ℝ)) := by
  have hK := one_le_succ_cast k
  have hK0 : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by linarith
  set z : ℂ := (((-1 / 2 : ℝ) : ℂ) + t * I) - η with hz
  have hzre : z.re = -1 / 2 - η := by rw [hz]; simp
  have hD := norm_cpow_sub_cpow_le hK (z := z) (by rw [hzre]; linarith) zero_le_one le_rfl
  rw [Real.rpow_one, hzre] at hD
  have hpow : ((k + 1 : ℕ) : ℝ) ^ (-1 / 2 - η) ≤ ((k + 1 : ℕ) : ℝ) ^ (-1 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hK (by linarith)
  have hD' : ‖(((k + 1 : ℕ) : ℝ) : ℂ) ^ z - ((((k + 1 : ℕ) : ℝ) + 1 : ℝ) : ℂ) ^ z‖ ≤
      ‖z‖ / ((k + 1 : ℕ) : ℝ) ^ 2 := by
    calc _ ≤ 2 * ((k + 1 : ℕ) : ℝ) ^ (-1 / 2 - η) * (‖z‖ / (2 * ((k + 1 : ℕ) : ℝ))) := hD
      _ ≤ 2 * ((k + 1 : ℕ) : ℝ) ^ (-1 : ℝ) * (‖z‖ / (2 * ((k + 1 : ℕ) : ℝ))) := by gcongr
      _ = ‖z‖ / ((k + 1 : ℕ) : ℝ) ^ 2 := by
          rw [Real.rpow_neg_one]; field_simp
  unfold dilationTerm
  rw [← hz, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul,
    abs_of_pos hK0]
  calc ((k + 1 : ℕ) : ℝ) * |b k| *
        ‖(((k + 1 : ℕ) : ℝ) : ℂ) ^ z - ((((k + 1 : ℕ) : ℝ) + 1 : ℝ) : ℂ) ^ z‖
      ≤ ((k + 1 : ℕ) : ℝ) * |b k| * (‖z‖ / ((k + 1 : ℕ) : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left hD' (by positivity)
    _ = ‖z‖ * (|b k| / ((k + 1 : ℕ) : ℝ)) := by field_simp

/-- **Pointwise size of the symbol**: `‖B(t)‖² ≤ 2‖z‖² Σ b_k²`. -/
theorem norm_sq_dilationSymbol_le {η : ℝ} (h0 : 1 / 2 < η) (N : ℕ) (b : ℕ → ℝ) (t : ℝ) :
    ‖dilationSymbol η N b t‖ ^ 2 ≤
      2 * ‖(((-1 / 2 : ℝ) : ℂ) + t * I) - η‖ ^ 2 * ∑ k ∈ Finset.range N, b k ^ 2 := by
  set Z := ‖(((-1 / 2 : ℝ) : ℂ) + t * I) - η‖
  have h1 : ‖dilationSymbol η N b t‖ ≤ Z * ∑ k ∈ Finset.range N, |b k| * (1 / ((k + 1 : ℕ) : ℝ)) := by
    unfold dilationSymbol
    refine (norm_sum_le _ _).trans ?_
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun k _ => by
      rw [mul_one_div]; exact norm_dilationTerm_le h0 b t k
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range N) (fun k => |b k|)
    (fun k => 1 / ((k + 1 : ℕ) : ℝ))
  have hinv : ∑ k ∈ Finset.range N, (1 / ((k + 1 : ℕ) : ℝ)) ^ 2 ≤ 2 := by
    have := sum_range_inv_succ_sq_le_two N
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun k _ => ?_)) this
    rw [div_pow, one_pow]
  have hb0 : 0 ≤ ∑ k ∈ Finset.range N, b k ^ 2 := Finset.sum_nonneg fun k _ => sq_nonneg _
  have hS0 : 0 ≤ ∑ k ∈ Finset.range N, |b k| * (1 / ((k + 1 : ℕ) : ℝ)) :=
    Finset.sum_nonneg fun k _ => by positivity
  have hsq : (∑ k ∈ Finset.range N, |b k| * (1 / ((k + 1 : ℕ) : ℝ))) ^ 2 ≤
      2 * ∑ k ∈ Finset.range N, b k ^ 2 := by
    calc _ ≤ (∑ k ∈ Finset.range N, |b k| ^ 2) *
          ∑ k ∈ Finset.range N, (1 / ((k + 1 : ℕ) : ℝ)) ^ 2 := hcs
      _ ≤ (∑ k ∈ Finset.range N, b k ^ 2) * 2 := by
          rw [Finset.sum_congr rfl fun k _ => sq_abs (b k)]
          exact mul_le_mul_of_nonneg_left hinv hb0
      _ = 2 * ∑ k ∈ Finset.range N, b k ^ 2 := by ring
  calc ‖dilationSymbol η N b t‖ ^ 2
      ≤ (Z * ∑ k ∈ Finset.range N, |b k| * (1 / ((k + 1 : ℕ) : ℝ))) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ = Z ^ 2 * (∑ k ∈ Finset.range N, |b k| * (1 / ((k + 1 : ℕ) : ℝ))) ^ 2 := by ring
    _ ≤ Z ^ 2 * (2 * ∑ k ∈ Finset.range N, b k ^ 2) :=
        mul_le_mul_of_nonneg_left hsq (sq_nonneg _)
    _ = _ := by ring

/-- `‖z‖² ≤ 9/4 + t²` for `z = −½ − η + it`, `½ < η < 1`. -/
theorem norm_sq_critical_sub_le {η : ℝ} (h0 : 1 / 2 < η) (h1 : η < 1) (t : ℝ) :
    ‖(((-1 / 2 : ℝ) : ℂ) + t * I) - η‖ ^ 2 ≤ 9 / 4 + t ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp
  nlinarith

/-! ### Conjugation symmetry -/

/-- `x^{conj z} = conj (x^z)` for `x > 0`. -/
theorem ofReal_cpow_conj {x : ℝ} (hx : 0 < x) (z : ℂ) :
    (x : ℂ) ^ ((starRingEnd ℂ) z) = (starRingEnd ℂ) ((x : ℂ) ^ z) := by
  have harg : (x : ℂ).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg hx.le]; exact Real.pi_pos.ne
  rw [Complex.cpow_conj _ _ harg, Complex.conj_ofReal]

/-- The terms of the symbol are conjugate under `t ↦ −t`. -/
theorem dilationTerm_neg (η : ℝ) (b : ℕ → ℝ) (t : ℝ) (k : ℕ) :
    dilationTerm η b (-t) k = (starRingEnd ℂ) (dilationTerm η b t k) := by
  have hc : (((-1 / 2 : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I) - η =
      (starRingEnd ℂ) ((((-1 / 2 : ℝ) : ℂ) + t * I) - η) := by
    simp only [map_sub, map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
    push_cast
    ring
  have hK0 : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
  have hK1 : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) + 1 := by positivity
  unfold dilationTerm
  rw [hc, ofReal_cpow_conj hK0, ofReal_cpow_conj hK1, map_mul, map_sub, Complex.conj_ofReal]

theorem norm_dilationSymbol_neg (η : ℝ) (N : ℕ) (b : ℕ → ℝ) (t : ℝ) :
    ‖dilationSymbol η N b (-t)‖ = ‖dilationSymbol η N b t‖ := by
  unfold dilationSymbol
  rw [Finset.sum_congr rfl fun k _ => dilationTerm_neg η b t k, ← map_sum, Complex.norm_conj]

/-! ### The head is a Dirichlet polynomial -/

/-- `x^{−½ − η + it} = x^{−½−η} e^{it log x}` for `x > 0`. -/
theorem ofReal_cpow_critical {x : ℝ} (hx : 0 < x) (η t : ℝ) :
    (x : ℂ) ^ ((((-1 / 2 : ℝ) : ℂ) + t * I) - η) =
      ((x ^ (-1 / 2 - η) : ℝ) : ℂ) * Complex.exp (((t * Real.log x : ℝ) : ℂ) * I) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.2 hx.ne'), ← Complex.ofReal_log hx.le,
    Real.rpow_def_of_pos hx, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Coefficients of the head of the symbol as a Dirichlet polynomial. -/
def headCoeff (η : ℝ) (X : ℕ) (b : ℕ → ℝ) (n : ℕ) : ℝ :=
  ((n : ℝ) + 1) ^ (-1 / 2 - η) *
    ((if n < X then ((n : ℝ) + 1) * b n else 0) - (if 1 ≤ n then (n : ℝ) * b (n - 1) else 0))

/-- **The head of the symbol is a Dirichlet polynomial** with frequencies `log(n+1)`, `n ≤ X`. -/
theorem head_eq_dirPoly (η : ℝ) (X : ℕ) (b : ℕ → ℝ) (t : ℝ) :
    ∑ k ∈ Finset.range X, dilationTerm η b t k =
      RHTower.Sieve.dirPoly (X + 1) (fun n => (headCoeff η X b n : ℂ)) t := by
  set E : ℕ → ℂ := fun n => Complex.exp (((t * Real.log ((n : ℝ) + 1) : ℝ) : ℂ) * I) with hE
  set p : ℕ → ℝ := fun n => ((n : ℝ) + 1) ^ (-1 / 2 - η) with hp
  have hterm : ∀ k : ℕ, dilationTerm η b t k =
      (((k + 1 : ℕ) : ℝ) * b k * p k : ℝ) * E k -
        (((k + 1 : ℕ) : ℝ) * b k * p (k + 1) : ℝ) * E (k + 1) := by
    intro k
    have hK0 : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
    have hK1 : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) + 1 := by positivity
    unfold dilationTerm
    rw [ofReal_cpow_critical hK0, ofReal_cpow_critical hK1]
    simp only [hE, hp]
    push_cast
    ring
  have hdir : RHTower.Sieve.dirPoly (X + 1) (fun n => (headCoeff η X b n : ℂ)) t =
      ∑ n ∈ Finset.range (X + 1), (headCoeff η X b n : ℂ) * E n := by
    unfold RHTower.Sieve.dirPoly
    rw [Fin.sum_univ_eq_sum_range (fun n => (headCoeff η X b n : ℂ) *
      Complex.exp (((t * Real.log ((n : ℝ) + 1) : ℝ) : ℂ) * I)) (X + 1)]
  have hsplit : ∀ n : ℕ, (headCoeff η X b n : ℂ) * E n =
      (if n < X then (((n + 1 : ℕ) : ℝ) * b n * p n : ℝ) * E n else 0) -
        (if 1 ≤ n then ((n : ℝ) * b (n - 1) * p n : ℝ) * E n else 0) := by
    intro n
    unfold headCoeff
    simp only [hp]
    split_ifs <;> push_cast <;> ring
  rw [hdir, Finset.sum_congr rfl fun n _ => hsplit n, Finset.sum_sub_distrib,
    Finset.sum_range_succ, if_neg (lt_irrefl X), add_zero, Finset.sum_range_succ',
    if_neg (by omega : ¬ 1 ≤ 0), add_zero,
    Finset.sum_congr rfl fun n hn => if_pos (Finset.mem_range.mp hn),
    Finset.sum_congr rfl fun n _ => if_pos (by omega : 1 ≤ n + 1), ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hterm k]
  push_cast
  ring_nf

/-- `Σ_{n ≤ X} |a_n|² ≤ 4 Σ b_k²` for the head coefficients. -/
theorem sum_sq_headCoeff_le {η : ℝ} (h0 : 1 / 2 < η) (X : ℕ) {b : ℕ → ℝ} {N : ℕ}
    (hb : ∀ k, N ≤ k → b k = 0) :
    ∑ n : Fin (X + 1), ‖(headCoeff η X b n : ℂ)‖ ^ 2 ≤ 4 * ∑ k ∈ Finset.range N, b k ^ 2 := by
  have hpt : ∀ n : ℕ, headCoeff η X b n ^ 2 ≤
      2 * b n ^ 2 + 2 * (if 1 ≤ n then b (n - 1) ^ 2 else 0) := by
    intro n
    have hn0 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    set q := ((n : ℝ) + 1) ^ (-1 / 2 - η) with hq
    have hq0 : 0 ≤ q := Real.rpow_nonneg hn0.le _
    have hq1 : q * ((n : ℝ) + 1) ≤ 1 := by
      have : q * ((n : ℝ) + 1) = ((n : ℝ) + 1) ^ (1 / 2 - η) := by
        rw [hq, ← Real.rpow_add_one hn0.ne']; congr 1; ring
      rw [this]
      exact Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)
    have hqn : q * (n : ℝ) ≤ 1 := by
      have : q * (n : ℝ) ≤ q * ((n : ℝ) + 1) := mul_le_mul_of_nonneg_left (by linarith) hq0
      linarith
    have hqn0 : 0 ≤ q * (n : ℝ) := by positivity
    have hqN0 : 0 ≤ q * ((n : ℝ) + 1) := by positivity
    unfold headCoeff
    rw [← hq]
    set A := (if n < X then ((n : ℝ) + 1) * b n else 0)
    set B := (if 1 ≤ n then (n : ℝ) * b (n - 1) else 0)
    have hA : (q * A) ^ 2 ≤ b n ^ 2 := by
      simp only [A]
      split_ifs
      · rw [show q * (((n : ℝ) + 1) * b n) = (q * ((n : ℝ) + 1)) * b n by ring, mul_pow]
        nlinarith [sq_nonneg (b n), pow_le_one₀ hqN0 hq1 (n := 2)]
      · simpa using sq_nonneg (b n)
    have hB : (q * B) ^ 2 ≤ (if 1 ≤ n then b (n - 1) ^ 2 else 0) := by
      simp only [B]
      split_ifs
      · rw [show q * ((n : ℝ) * b (n - 1)) = (q * (n : ℝ)) * b (n - 1) by ring, mul_pow]
        nlinarith [sq_nonneg (b (n - 1)), pow_le_one₀ hqn0 hqn (n := 2)]
      · simp
    have := add_sq_le_two (q * A) (-(q * B))
    nlinarith [sq_nonneg (q * A + q * B)]
  have hsum1 : ∑ n ∈ Finset.range (X + 1), b n ^ 2 ≤ ∑ k ∈ Finset.range N, b k ^ 2 :=
    sum_sq_range_le_of_support hb _
  have hsum2 : ∑ n ∈ Finset.range (X + 1), (if 1 ≤ n then b (n - 1) ^ 2 else 0) ≤
      ∑ k ∈ Finset.range N, b k ^ 2 := by
    rw [Finset.sum_range_succ', if_neg (by omega : ¬ 1 ≤ 0), add_zero]
    rw [Finset.sum_congr rfl fun n _ => if_pos (by omega : 1 ≤ n + 1)]
    simp only [Nat.add_sub_cancel]
    exact sum_sq_range_le_of_support hb _
  rw [Fin.sum_univ_eq_sum_range (fun n => ‖(headCoeff η X b n : ℂ)‖ ^ 2) (X + 1)]
  calc ∑ n ∈ Finset.range (X + 1), ‖(headCoeff η X b n : ℂ)‖ ^ 2
      = ∑ n ∈ Finset.range (X + 1), headCoeff η X b n ^ 2 := by
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
    _ ≤ ∑ n ∈ Finset.range (X + 1), (2 * b n ^ 2 + 2 * (if 1 ≤ n then b (n - 1) ^ 2 else 0)) :=
        Finset.sum_le_sum fun n _ => hpt n
    _ = 2 * ∑ n ∈ Finset.range (X + 1), b n ^ 2 +
          2 * ∑ n ∈ Finset.range (X + 1), (if 1 ≤ n then b (n - 1) ^ 2 else 0) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ ≤ 4 * ∑ k ∈ Finset.range N, b k ^ 2 := by linarith

/-- **Mean square of the head**: `∫_0^T |head|² ≤ 4(T + 4(X+1)(1 + log(X+1))) Σ b_k²`. -/
theorem integral_norm_sq_head_le {η : ℝ} (h0 : 1 / 2 < η) (X : ℕ) {b : ℕ → ℝ} {N : ℕ}
    (hb : ∀ k, N ≤ k → b k = 0) {T : ℝ} (hT : 0 ≤ T) :
    ∫ t in (0 : ℝ)..T, ‖∑ k ∈ Finset.range X, dilationTerm η b t k‖ ^ 2 ≤
      4 * (T + 4 * ((X + 1 : ℕ) : ℝ) * (1 + Real.log ((X + 1 : ℕ) : ℝ))) *
        ∑ k ∈ Finset.range N, b k ^ 2 := by
  have hmv := RHTower.Sieve.dirichlet_meanValue_theorem (X + 1)
    (fun n => (headCoeff η X b n : ℂ)) T
  have hA := sum_sq_headCoeff_le h0 X hb
  set S := ∑ n : Fin (X + 1), ‖(headCoeff η X b n : ℂ)‖ ^ (2 : ℕ)
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun n _ => by positivity
  have hlog : 0 ≤ Real.log ((X + 1 : ℕ) : ℝ) := Real.log_nonneg (by exact_mod_cast Nat.succ_pos X)
  have hint : ∫ t in (0 : ℝ)..T, ‖∑ k ∈ Finset.range X, dilationTerm η b t k‖ ^ 2 =
      ∫ t in (0 : ℝ)..T, ‖RHTower.Sieve.dirPoly (X + 1) (fun n => (headCoeff η X b n : ℂ)) t‖ ^ 2 := by
    congr 1; funext t; rw [head_eq_dirPoly]
  rw [hint]
  have h1 := (abs_le.mp hmv).2
  have hc : 0 ≤ T + 4 * ((X + 1 : ℕ) : ℝ) * (1 + Real.log ((X + 1 : ℕ) : ℝ)) := by positivity
  calc _ ≤ T * S + 4 * ((X + 1 : ℕ) : ℝ) * (1 + Real.log ((X + 1 : ℕ) : ℝ)) * S := by linarith
    _ = (T + 4 * ((X + 1 : ℕ) : ℝ) * (1 + Real.log ((X + 1 : ℕ) : ℝ))) * S := by ring
    _ ≤ (T + 4 * ((X + 1 : ℕ) : ℝ) * (1 + Real.log ((X + 1 : ℕ) : ℝ))) *
          (4 * ∑ k ∈ Finset.range N, b k ^ 2) := mul_le_mul_of_nonneg_left hA hc
    _ = _ := by ring

end

end GaloisForLFunctions.SignedArithmeticEnergyIncidence
