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

/-! ### The tail is a Fourier transform -/

/-- `x^z = e^{z log x}` for `x > 0`. -/
theorem ofReal_cpow_eq_exp {x : ℝ} (hx : 0 < x) (z : ℂ) :
    (x : ℂ) ^ z = Complex.exp (z * (Real.log x : ℂ)) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.2 hx.ne'), ← Complex.ofReal_log hx.le,
    mul_comm]

/-- The step `[log K, log(K+1))`, `K = k + 1`, of the tail in logarithmic coordinates. -/
def stepInterval (k : ℕ) : Set ℝ :=
  Ico (Real.log ((k + 1 : ℕ) : ℝ)) (Real.log (((k + 1 : ℕ) : ℝ) + 1))

theorem stepInterval_disjoint {k k' : ℕ} (h : k ≠ k') {u : ℝ} (hu : u ∈ stepInterval k)
    (hu' : u ∈ stepInterval k') : False := by
  have key : ∀ {a a' : ℕ}, a < a' → u ∈ stepInterval a → u ∈ stepInterval a' → False := by
    intro a a' hlt ha ha'
    have hle : ((a + 1 : ℕ) : ℝ) + 1 ≤ ((a' + 1 : ℕ) : ℝ) := by
      push_cast
      exact_mod_cast (show a + 1 + 1 ≤ a' + 1 by omega)
    have hlog := Real.log_le_log (by positivity) hle
    exact lt_irrefl u (lt_of_lt_of_le ha.2 (hlog.trans ha'.1))
  rcases lt_or_gt_of_ne h with hlt | hlt
  · exact key hlt hu hu'
  · exact key hlt hu' hu

theorem integrable_step {E : Type*} [NormedAddCommGroup E] (k : ℕ) {g : ℝ → E}
    (hg : Continuous g) : Integrable ((stepInterval k).indicator g) := by
  unfold stepInterval
  exact (hg.integrableOn_Icc.mono_set Ico_subset_Icc_self).integrable_indicator measurableSet_Ico

/-- The tail as a step function in `u = log x`:
`h(u) = Σ_{k∈S} K b_k 1_{[log K, log(K+1))}(u) e^{(−½−η)u}`. -/
def tailStep (η : ℝ) (S : Finset ℕ) (b : ℕ → ℝ) (u : ℝ) : ℂ :=
  ∑ k ∈ S, ((((k + 1 : ℕ) : ℝ) * b k : ℝ) : ℂ) *
    (stepInterval k).indicator (fun u : ℝ => ((Real.exp ((-1 / 2 - η) * u) : ℝ) : ℂ)) u

theorem integrable_tailStep (η : ℝ) (S : Finset ℕ) (b : ℕ → ℝ) :
    Integrable (tailStep η S b) := by
  unfold tailStep
  refine integrable_finsetSum _ fun k _ => Integrable.const_mul (integrable_step k ?_) _
  fun_prop

/-- **The tail is `−z` times a Fourier transform**: for `S` a set of indices,
`Σ_{k∈S} K b_k (K^z − (K+1)^z) = −z · 𝓕 h(−t/2π)`. -/
theorem tail_eq_neg_mul_fourier {η : ℝ} (h0 : 1 / 2 < η) (S : Finset ℕ) (b : ℕ → ℝ) (t : ℝ) :
    ∑ k ∈ S, dilationTerm η b t k =
      -((((-1 / 2 : ℝ) : ℂ) + t * I) - η) * 𝓕 (tailStep η S b) (-t / (2 * Real.pi)) := by
  set z : ℂ := (((-1 / 2 : ℝ) : ℂ) + t * I) - η with hz
  have hz0 : z ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    rw [hz] at this
    simp at this
    linarith
  rw [Real.fourier_real_eq_integral_exp_smul]
  have hpt : ∀ v : ℝ, Complex.exp (((-2 * Real.pi * v * (-t / (2 * Real.pi)) : ℝ) : ℂ) * I) •
      tailStep η S b v =
      ∑ k ∈ S, ((((k + 1 : ℕ) : ℝ) * b k : ℝ) : ℂ) *
        (stepInterval k).indicator (fun u : ℝ => Complex.exp (z * u)) v := by
    intro v
    have hph : (-2 * Real.pi * v * (-t / (2 * Real.pi)) : ℝ) = t * v := by
      field_simp
    rw [hph, tailStep, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases hv : v ∈ stepInterval k
    · rw [Set.indicator_of_mem hv, Set.indicator_of_mem hv, Complex.ofReal_exp,
        mul_left_comm, ← Complex.exp_add]
      congr 2
      rw [hz]; push_cast; ring
    · rw [Set.indicator_of_notMem hv, Set.indicator_of_notMem hv]; ring
  have hint : ∀ k ∈ S, Integrable (fun v : ℝ => ((((k + 1 : ℕ) : ℝ) * b k : ℝ) : ℂ) *
      (stepInterval k).indicator (fun u : ℝ => Complex.exp (z * u)) v) := fun k _ =>
    Integrable.const_mul (integrable_step k (by fun_prop)) _
  have hstep : ∀ k : ℕ, ∫ v : ℝ, (stepInterval k).indicator (fun u : ℝ => Complex.exp (z * u)) v =
      ((((k + 1 : ℕ) : ℝ) + 1 : ℝ) : ℂ) ^ z / z - ((((k + 1 : ℕ) : ℝ) : ℝ) : ℂ) ^ z / z := by
    intro k
    have hK0 : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
    have hK1 : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) + 1 := by positivity
    have hle : Real.log ((k + 1 : ℕ) : ℝ) ≤ Real.log (((k + 1 : ℕ) : ℝ) + 1) :=
      Real.log_le_log hK0 (by linarith)
    rw [integral_indicator (by unfold stepInterval; exact measurableSet_Ico)]
    unfold stepInterval
    rw [integral_Ico_eq_integral_Ioc, ← intervalIntegral.integral_of_le hle,
      integral_exp_mul_complex hz0, ofReal_cpow_eq_exp hK0, ofReal_cpow_eq_exp hK1, sub_div]
  rw [integral_congr_ae (ae_of_all _ hpt), integral_finsetSum _ hint, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [integral_const_mul, hstep k]
  unfold dilationTerm
  rw [← hz]
  field_simp
  ring

/-- **Disjoint steps**: `‖h(u)‖² ≤ Σ_k (K b_k)² 1_{[log K, log(K+1))}(u) e^{(−1−2η)u}`. -/
theorem norm_sq_tailStep_le (η : ℝ) (S : Finset ℕ) (b : ℕ → ℝ) (u : ℝ) :
    ‖tailStep η S b u‖ ^ 2 ≤ ∑ k ∈ S, (((k + 1 : ℕ) : ℝ) * b k) ^ 2 *
      (stepInterval k).indicator (fun u : ℝ => Real.exp (2 * ((-1 / 2 - η) * u))) u := by
  by_cases h : ∃ k ∈ S, u ∈ stepInterval k
  · obtain ⟨k₀, hk₀, hu⟩ := h
    have hother : ∀ k ∈ S, k ≠ k₀ → u ∉ stepInterval k :=
      fun k _ hk hu' => stepInterval_disjoint hk hu' hu
    rw [tailStep, Finset.sum_eq_single_of_mem k₀ hk₀ (fun k hk hne => by
        rw [Set.indicator_of_notMem (hother k hk hne), mul_zero]),
      Finset.sum_eq_single_of_mem k₀ hk₀ (fun k hk hne => by
        rw [Set.indicator_of_notMem (hother k hk hne), mul_zero]),
      Set.indicator_of_mem hu, Set.indicator_of_mem hu, norm_mul, Complex.norm_real,
      Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), mul_pow,
      sq_abs]
    refine le_of_eq ?_
    congr 1
    rw [← Real.exp_nat_mul]
    norm_num
  · have h0 : tailStep η S b u = 0 := Finset.sum_eq_zero fun k hk => by
      rw [Set.indicator_of_notMem fun hu => h ⟨k, hk, hu⟩, mul_zero]
    rw [h0, norm_zero, sq, mul_zero]
    exact Finset.sum_nonneg fun k _ => mul_nonneg (sq_nonneg _)
      (Set.indicator_nonneg (fun u _ => (Real.exp_pos _).le) u)

/-- **The tail in `L²`**: `∫ |h|² ≤ Σ_{k∈S} b_k²/(k+1)`. -/
theorem integral_norm_sq_tailStep_le {η : ℝ} (h0 : 1 / 2 < η) (S : Finset ℕ) (b : ℕ → ℝ) :
    Integrable (fun u => ‖tailStep η S b u‖ ^ 2) ∧
      ∫ u, ‖tailStep η S b u‖ ^ 2 ≤ ∑ k ∈ S, b k ^ 2 / ((k + 1 : ℕ) : ℝ) := by
  set R : ℝ → ℝ := fun u => ∑ k ∈ S, (((k + 1 : ℕ) : ℝ) * b k) ^ 2 *
    (stepInterval k).indicator (fun u : ℝ => Real.exp (2 * ((-1 / 2 - η) * u))) u with hR
  have hRi : Integrable R := by
    refine integrable_finsetSum _ fun k _ => Integrable.const_mul (integrable_step k ?_) _
    fun_prop
  have hmeas : AEStronglyMeasurable (fun u => ‖tailStep η S b u‖ ^ 2) :=
    ((integrable_tailStep η S b).aestronglyMeasurable.norm.pow 2)
  have hint : Integrable (fun u => ‖tailStep η S b u‖ ^ 2) :=
    hRi.mono' hmeas (ae_of_all _ fun u => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact norm_sq_tailStep_le η S b u)
  refine ⟨hint, ?_⟩
  have hk : ∀ k ∈ S, ∫ u, (((k + 1 : ℕ) : ℝ) * b k) ^ 2 *
      (stepInterval k).indicator (fun u : ℝ => Real.exp (2 * ((-1 / 2 - η) * u))) u ≤
      b k ^ 2 / ((k + 1 : ℕ) : ℝ) := by
    intro k _
    set K : ℝ := ((k + 1 : ℕ) : ℝ) with hK
    have hK1 : (1 : ℝ) ≤ K := one_le_succ_cast k
    have hK0 : 0 < K := by linarith
    have hle : Real.log K ≤ Real.log (K + 1) := Real.log_le_log hK0 (by linarith)
    have hstep : ∫ u, (stepInterval k).indicator (fun u : ℝ => Real.exp (2 * ((-1 / 2 - η) * u))) u
        ≤ (Real.log (K + 1) - Real.log K) * Real.exp (2 * ((-1 / 2 - η) * Real.log K)) := by
      rw [integral_indicator (by unfold stepInterval; exact measurableSet_Ico)]
      unfold stepInterval
      rw [← hK, integral_Ico_eq_integral_Ioc, ← intervalIntegral.integral_of_le hle]
      calc ∫ u in Real.log K..Real.log (K + 1), Real.exp (2 * ((-1 / 2 - η) * u))
          ≤ ∫ u in Real.log K..Real.log (K + 1), Real.exp (2 * ((-1 / 2 - η) * Real.log K)) := by
            refine intervalIntegral.integral_mono_on hle
              ((by fun_prop : Continuous fun u : ℝ =>
                Real.exp (2 * ((-1 / 2 - η) * u))).intervalIntegrable _ _)
              intervalIntegrable_const fun u hu => Real.exp_le_exp.mpr ?_
            nlinarith [hu.1]
        _ = (Real.log (K + 1) - Real.log K) * Real.exp (2 * ((-1 / 2 - η) * Real.log K)) := by
            rw [intervalIntegral.integral_const, smul_eq_mul]
    have hlog : Real.log (K + 1) - Real.log K ≤ 1 / K := by
      rw [← Real.log_div (by linarith) hK0.ne']
      have := Real.log_le_sub_one_of_pos (show 0 < (K + 1) / K by positivity)
      have e : (K + 1) / K - 1 = 1 / K := by field_simp; ring
      linarith
    have hexp : Real.exp (2 * ((-1 / 2 - η) * Real.log K)) = K ^ (-1 - 2 * η) := by
      rw [Real.rpow_def_of_pos hK0]; congr 1; ring
    have hpow : K ^ 2 * (1 / K) * K ^ (-1 - 2 * η) ≤ 1 / K := by
      have e : K ^ 2 * (1 / K) * K ^ (-1 - 2 * η) = K ^ (-2 * η) := by
        calc K ^ 2 * (1 / K) * K ^ (-1 - 2 * η) = K * K ^ (-1 - 2 * η) := by
              rw [sq, mul_one_div, mul_div_assoc, div_self hK0.ne', mul_one]
          _ = K ^ (1 : ℝ) * K ^ (-1 - 2 * η) := by rw [Real.rpow_one]
          _ = K ^ ((1 : ℝ) + (-1 - 2 * η)) := by rw [Real.rpow_add hK0]
          _ = K ^ (-2 * η) := by congr 1; ring
      rw [e, one_div, ← Real.rpow_neg_one]
      exact Real.rpow_le_rpow_of_exponent_le hK1 (by linarith)
    rw [integral_const_mul]
    calc (K * b k) ^ 2 * ∫ u, (stepInterval k).indicator
          (fun u : ℝ => Real.exp (2 * ((-1 / 2 - η) * u))) u
        ≤ (K * b k) ^ 2 * ((Real.log (K + 1) - Real.log K) *
            Real.exp (2 * ((-1 / 2 - η) * Real.log K))) :=
          mul_le_mul_of_nonneg_left hstep (sq_nonneg _)
      _ ≤ (K * b k) ^ 2 * ((1 / K) * K ^ (-1 - 2 * η)) := by
          rw [hexp]
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hlog (Real.rpow_nonneg hK0.le _)) (sq_nonneg _)
      _ = b k ^ 2 * (K ^ 2 * (1 / K) * K ^ (-1 - 2 * η)) := by ring
      _ ≤ b k ^ 2 * (1 / K) := mul_le_mul_of_nonneg_left hpow (sq_nonneg _)
      _ = b k ^ 2 / K := by ring
  calc ∫ u, ‖tailStep η S b u‖ ^ 2 ≤ ∫ u, R u :=
        integral_mono hint hRi fun u => norm_sq_tailStep_le η S b u
    _ = ∑ k ∈ S, ∫ u, (((k + 1 : ℕ) : ℝ) * b k) ^ 2 *
          (stepInterval k).indicator (fun u : ℝ => Real.exp (2 * ((-1 / 2 - η) * u))) u := by
        rw [hR, integral_finsetSum _ fun k _ =>
          Integrable.const_mul (integrable_step k (by fun_prop)) _]
    _ ≤ _ := Finset.sum_le_sum hk

/-- **Plancherel for the tail**: `∫ |𝓕 h(−t/2π)|² dt ≤ 2π Σ_{k∈S} b_k²/(k+1)`. -/
theorem integral_norm_sq_fourier_tailStep_le {η : ℝ} (h0 : 1 / 2 < η) (S : Finset ℕ)
    (b : ℕ → ℝ) :
    Integrable (fun t : ℝ => ‖𝓕 (tailStep η S b) (-t / (2 * Real.pi))‖ ^ 2) ∧
      ∫ t : ℝ, ‖𝓕 (tailStep η S b) (-t / (2 * Real.pi))‖ ^ 2 ≤
        2 * Real.pi * ∑ k ∈ S, b k ^ 2 / ((k + 1 : ℕ) : ℝ) := by
  obtain ⟨hsq, hbound⟩ := integral_norm_sq_tailStep_le h0 S b
  have hi := integrable_tailStep η S b
  have hL2 : MemLp (tailStep η S b) 2 :=
    (memLp_two_iff_integrable_sq_norm hi.aestronglyMeasurable).mpr hsq
  have hF := integrable_norm_sq_fourier hi hL2
  have hπ : (-(2 * Real.pi)) ≠ 0 := by have := Real.pi_pos; linarith
  have hfun : (fun t : ℝ => ‖𝓕 (tailStep η S b) (-t / (2 * Real.pi))‖ ^ 2) =
      fun t => (fun ξ => ‖𝓕 (tailStep η S b) ξ‖ ^ 2) (t / (-(2 * Real.pi))) := by
    funext t; rw [div_neg, neg_div]
  refine ⟨by rw [hfun]; exact hF.comp_div hπ, ?_⟩
  rw [hfun, Measure.integral_comp_div (fun ξ => ‖𝓕 (tailStep η S b) ξ‖ ^ 2) (-(2 * Real.pi)),
    abs_neg, abs_of_pos (by positivity), smul_eq_mul,
    GaloisForLFunctions.HTGeometry.integral_norm_sq_fourier hi hL2]
  exact mul_le_mul_of_nonneg_left hbound (by positivity)

/-! ### Mean square of the symbol on a dyadic height -/

theorem continuous_dilationTerm (η : ℝ) (b : ℕ → ℝ) (k : ℕ) :
    Continuous fun t : ℝ => dilationTerm η b t k := by
  have hK0 : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
  have hK1 : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) + 1 := by positivity
  unfold dilationTerm
  refine continuous_const.mul (Continuous.sub ?_ ?_)
  · exact continuous_const.cpow (by fun_prop) fun _ => Complex.ofReal_mem_slitPlane.2 hK0
  · exact continuous_const.cpow (by fun_prop) fun _ => Complex.ofReal_mem_slitPlane.2 hK1

/-- **The symbol on a dyadic height**: `∫_T^{2T} |B|² ≤ 200 T (1 + log 2T) Σ b_k²`. -/
theorem integral_norm_sq_dilationSymbol_shell_le {η : ℝ} (h0 : 1 / 2 < η) (h1 : η < 1)
    {b : ℕ → ℝ} {N : ℕ} (hb : ∀ k, N ≤ k → b k = 0) {T : ℝ} (hT : 8 ≤ T) :
    ∫ t in T..(2 * T), ‖dilationSymbol η N b t‖ ^ 2 ≤
      200 * T * (1 + Real.log (2 * T)) * ∑ k ∈ Finset.range N, b k ^ 2 := by
  set X : ℕ := ⌈T⌉₊ with hXdef
  have hX1 : T ≤ (X : ℝ) := Nat.le_ceil T
  have hX2 : (X : ℝ) < T + 1 := Nat.ceil_lt_add_one (by linarith)
  set S := (Finset.range N).filter (fun k => X ≤ k) with hS
  set nb := ∑ k ∈ Finset.range N, b k ^ 2 with hnb
  have hnb0 : 0 ≤ nb := Finset.sum_nonneg fun k _ => sq_nonneg _
  have hcont := continuous_dilationTerm η b
  set hd : ℝ → ℂ := fun t => ∑ k ∈ Finset.range X, dilationTerm η b t k with hhd
  set tl : ℝ → ℂ := fun t => ∑ k ∈ S, dilationTerm η b t k with htl
  have hdc : Continuous hd := continuous_finsetSum _ fun k _ => hcont k
  have tlc : Continuous tl := continuous_finsetSum _ fun k _ => hcont k
  have hsplit : ∀ t, dilationSymbol η N b t = hd t + tl t := by
    intro t
    have hzero : ∀ k, N ≤ k → dilationTerm η b t k = 0 := fun k hk => by
      unfold dilationTerm; rw [hb k hk]; simp
    have hhead : hd t = ∑ k ∈ (Finset.range N).filter (fun k => k < X), dilationTerm η b t k := by
      have e : (Finset.range N).filter (fun k => k < X) = Finset.range (min N X) := by
        ext k; simp [Finset.mem_filter, Finset.mem_range]
      rw [e]
      refine (Finset.sum_subset (Finset.range_subset_range.mpr (min_le_right N X))
        fun k hk hk' => ?_).symm
      simp only [Finset.mem_range, lt_min_iff, not_and_or, not_lt] at hk hk'
      exact hzero k (by omega)
    have htail : tl t = ∑ k ∈ (Finset.range N).filter (fun k => ¬ k < X), dilationTerm η b t k := by
      simp only [htl, hS, not_lt]
    unfold dilationSymbol
    rw [hhead, htail, Finset.sum_filter_add_sum_filter_not]
  -- the pieces
  have hpt : ∀ t, ‖dilationSymbol η N b t‖ ^ 2 ≤ 2 * ‖hd t‖ ^ 2 + 2 * ‖tl t‖ ^ 2 := by
    intro t
    rw [hsplit t]
    have := norm_add_le (hd t) (tl t)
    nlinarith [norm_nonneg (hd t + tl t), sq_nonneg (‖hd t‖ - ‖tl t‖), norm_nonneg (hd t),
      norm_nonneg (tl t)]
  have hT0 : 0 ≤ T := by linarith
  have hTT : T ≤ 2 * T := by linarith
  have hBc : Continuous fun t => ‖dilationSymbol η N b t‖ ^ 2 :=
    ((hdc.add tlc).norm.pow 2).congr fun t => by rw [hsplit t]; rfl
  -- head
  have hhead : ∫ t in T..(2 * T), ‖hd t‖ ^ 2 ≤
      4 * (2 * T + 4 * ((X + 1 : ℕ) : ℝ) * (1 + Real.log ((X + 1 : ℕ) : ℝ))) * nb := by
    have hmono : ∫ t in T..(2 * T), ‖hd t‖ ^ 2 ≤ ∫ t in (0 : ℝ)..(2 * T), ‖hd t‖ ^ 2 :=
      intervalIntegral.integral_mono_interval hT0 hTT le_rfl (ae_of_all _ fun t => by positivity)
        ((hdc.norm.pow 2).intervalIntegrable _ _)
    exact hmono.trans (integral_norm_sq_head_le h0 X hb (by linarith))
  -- tail
  obtain ⟨hJi, hJ⟩ := integral_norm_sq_fourier_tailStep_le h0 S b
  set J : ℝ → ℝ := fun t => ‖𝓕 (tailStep η S b) (-t / (2 * Real.pi))‖ ^ 2 with hJdef
  have htl_eq : ∀ t, ‖tl t‖ ^ 2 = ‖(((-1 / 2 : ℝ) : ℂ) + t * I) - η‖ ^ 2 * J t := by
    intro t
    simp only [htl, hJdef]
    rw [tail_eq_neg_mul_fourier h0 S b t, norm_mul, norm_neg, mul_pow]
  have hSsum : ∑ k ∈ S, b k ^ 2 / ((k + 1 : ℕ) : ℝ) ≤ nb / T := by
    calc ∑ k ∈ S, b k ^ 2 / ((k + 1 : ℕ) : ℝ) ≤ ∑ k ∈ S, b k ^ 2 / T := by
          refine Finset.sum_le_sum fun k hk => ?_
          have hk' : X ≤ k := (Finset.mem_filter.mp hk).2
          have : T ≤ ((k + 1 : ℕ) : ℝ) := by
            have : (X : ℝ) ≤ k := by exact_mod_cast hk'
            push_cast; linarith
          exact div_le_div_of_nonneg_left (sq_nonneg _) (by linarith) this
      _ = (∑ k ∈ S, b k ^ 2) / T := by rw [Finset.sum_div]
      _ ≤ nb / T := by
          refine div_le_div_of_nonneg_right ?_ hT0
          exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            fun k _ _ => sq_nonneg _
  have htail : ∫ t in T..(2 * T), ‖tl t‖ ^ 2 ≤ 10 * Real.pi * T * nb := by
    have hbound : ∀ t ∈ Set.Icc T (2 * T), ‖tl t‖ ^ 2 ≤ 5 * T ^ 2 * J t := by
      intro t ht
      rw [htl_eq t]
      have hz := norm_sq_critical_sub_le h0 h1 t
      have ht2 : t ^ 2 ≤ 4 * T ^ 2 := by nlinarith [ht.1, ht.2]
      have hJ0 : 0 ≤ J t := by simp only [hJdef]; positivity
      exact mul_le_mul_of_nonneg_right (by nlinarith) hJ0
    calc ∫ t in T..(2 * T), ‖tl t‖ ^ 2 ≤ ∫ t in T..(2 * T), 5 * T ^ 2 * J t :=
          intervalIntegral.integral_mono_on hTT ((tlc.norm.pow 2).intervalIntegrable _ _)
            ((hJi.const_mul _).intervalIntegrable) hbound
      _ = 5 * T ^ 2 * ∫ t in T..(2 * T), J t := intervalIntegral.integral_const_mul _ _
      _ ≤ 5 * T ^ 2 * ∫ t, J t := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          rw [intervalIntegral.integral_of_le hTT]
          exact setIntegral_le_integral hJi (ae_of_all _ fun t => by simp only [hJdef]; positivity)
      _ ≤ 5 * T ^ 2 * (2 * Real.pi * (nb / T)) := by
          refine mul_le_mul_of_nonneg_left (hJ.trans ?_) (by positivity)
          exact mul_le_mul_of_nonneg_left hSsum (by positivity)
      _ = 10 * Real.pi * T * nb := by field_simp; ring
  -- assemble
  have hX3 : ((X + 1 : ℕ) : ℝ) ≤ 2 * T := by push_cast; linarith
  have hlogX : Real.log ((X + 1 : ℕ) : ℝ) ≤ Real.log (2 * T) :=
    Real.log_le_log (by positivity) hX3
  have hlog0 : 0 ≤ Real.log (2 * T) := Real.log_nonneg (by linarith)
  have hπ : Real.pi < 4 := Real.pi_lt_four
  have hi1 : IntervalIntegrable (fun t => 2 * ‖hd t‖ ^ 2) volume T (2 * T) :=
    (continuous_const.mul (hdc.norm.pow 2)).intervalIntegrable _ _
  have hi2 : IntervalIntegrable (fun t => 2 * ‖tl t‖ ^ 2) volume T (2 * T) :=
    (continuous_const.mul (tlc.norm.pow 2)).intervalIntegrable _ _
  have hXl : ((X + 1 : ℕ) : ℝ) * (1 + Real.log ((X + 1 : ℕ) : ℝ)) ≤
      2 * T * (1 + Real.log (2 * T)) := by
    have hl : 0 ≤ Real.log ((X + 1 : ℕ) : ℝ) :=
      Real.log_nonneg (by exact_mod_cast Nat.succ_pos X)
    exact mul_le_mul hX3 (by linarith) (by linarith) (by positivity)
  calc ∫ t in T..(2 * T), ‖dilationSymbol η N b t‖ ^ 2
      ≤ ∫ t in T..(2 * T), (2 * ‖hd t‖ ^ 2 + 2 * ‖tl t‖ ^ 2) :=
        intervalIntegral.integral_mono_on hTT (hBc.intervalIntegrable _ _) (hi1.add hi2)
          fun t _ => hpt t
    _ = 2 * (∫ t in T..(2 * T), ‖hd t‖ ^ 2) + 2 * (∫ t in T..(2 * T), ‖tl t‖ ^ 2) := by
        rw [intervalIntegral.integral_add hi1 hi2, intervalIntegral.integral_const_mul,
          intervalIntegral.integral_const_mul]
    _ ≤ 2 * (4 * (2 * T + 4 * ((X + 1 : ℕ) : ℝ) * (1 + Real.log ((X + 1 : ℕ) : ℝ))) * nb) +
          2 * (10 * Real.pi * T * nb) :=
        add_le_add (mul_le_mul_of_nonneg_left hhead (by norm_num))
          (mul_le_mul_of_nonneg_left htail (by norm_num))
    _ ≤ 200 * T * (1 + Real.log (2 * T)) * nb := by
        nlinarith [mul_le_mul_of_nonneg_right hXl hnb0, mul_nonneg (mul_nonneg hT0 hnb0) hlog0,
          mul_nonneg hT0 hnb0, mul_le_mul_of_nonneg_right hπ.le (mul_nonneg hT0 hnb0)]

/-! ### Assembly in Mellin coordinates -/

/-- The critical-line weight `|M P(−½ + it)|²` of the source. -/
def criticalSourceWeight (η t : ℝ) : ℝ :=
  ‖mellin (fun x => (sourceProfile η x : ℂ)) (((-1 / 2 : ℝ) : ℂ) + t * I)‖ ^ 2

/-- The Mellin transform of a real profile is conjugation symmetric. -/
theorem mellin_ofReal_conj (f : ℝ → ℝ) (s : ℂ) :
    mellin (fun x => (f x : ℂ)) ((starRingEnd ℂ) s) =
      (starRingEnd ℂ) (mellin (fun x => (f x : ℂ)) s) := by
  unfold mellin
  rw [← integral_conj]
  refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
  have hx0 : (0 : ℝ) < x := hx
  simp only [smul_eq_mul, map_mul, Complex.conj_ofReal]
  rw [show (starRingEnd ℂ) s - 1 = (starRingEnd ℂ) (s - 1) by simp, ofReal_cpow_conj hx0]

theorem norm_mellin_neg (f : ℝ → ℝ) (t : ℝ) :
    ‖mellin (fun x => (f x : ℂ)) (((-1 / 2 : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I)‖ =
      ‖mellin (fun x => (f x : ℂ)) (((-1 / 2 : ℝ) : ℂ) + t * I)‖ := by
  have hc : ((-1 / 2 : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I =
      (starRingEnd ℂ) (((-1 / 2 : ℝ) : ℂ) + t * I) := by
    simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
    push_cast
    ring
  rw [hc, mellin_ofReal_conj, Complex.norm_conj]

theorem criticalSourceWeight_neg (η t : ℝ) : criticalSourceWeight η (-t) = criticalSourceWeight η t := by
  unfold criticalSourceWeight
  rw [norm_mellin_neg]

theorem continuous_dilationSymbol (η : ℝ) (N : ℕ) (b : ℕ → ℝ) :
    Continuous fun t => dilationSymbol η N b t := by
  unfold dilationSymbol
  exact continuous_finsetSum _ fun k _ => continuous_dilationTerm η b k

/-- `Σ_j (j+1)⁵ r^j` converges for `0 < r < 1`. -/
theorem summable_succ_pow_five_mul_geometric {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    Summable fun j : ℕ => ((j : ℝ) + 1) ^ 5 * r ^ j := by
  have h := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 5
    (by rw [Real.norm_eq_abs, abs_of_pos hr0]; exact hr1)
  refine (((summable_nat_add_iff 1).mpr h).mul_left r⁻¹).congr fun j => ?_
  show r⁻¹ * (((j + 1 : ℕ) : ℝ) ^ 5 * r ^ (j + 1)) = ((j : ℝ) + 1) ^ 5 * r ^ j
  rw [pow_succ, inv_mul_eq_iff_eq_mul₀ hr0.ne']
  push_cast
  ring

/-- **Dyadic summation.**  An even integrable function with `∫_0^{T₀} F ≤ a` and
`∫_{2^j T₀}^{2^{j+1} T₀} F ≤ c_j`, `Σ c_j < ∞`, has `∫ F ≤ 2 (a + Σ c_j)`. -/
theorem integral_le_of_even_dyadic {F : ℝ → ℝ} (hFi : Integrable F) (heven : ∀ t, F (-t) = F t)
    {T₀ a : ℝ} (hT₀ : 0 < T₀) {c : ℕ → ℝ} (hc : Summable c) (hc0 : ∀ j, 0 ≤ c j)
    (hlow : ∫ t in (0 : ℝ)..T₀, F t ≤ a)
    (hshell : ∀ j : ℕ, ∫ t in ((2 : ℝ) ^ j * T₀)..((2 : ℝ) ^ (j + 1) * T₀), F t ≤ c j) :
    ∫ t, F t ≤ 2 * (a + ∑' j, c j) := by
  have hpartial : ∀ J : ℕ, ∫ t in (-((2 : ℝ) ^ J * T₀))..((2 : ℝ) ^ J * T₀), F t ≤
      2 * (a + ∑' j, c j) := by
    intro J
    have hneg : ∫ t in (-((2 : ℝ) ^ J * T₀))..0, F t =
        ∫ t in (0 : ℝ)..((2 : ℝ) ^ J * T₀), F t := by
      have h := intervalIntegral.integral_comp_neg (a := 0) (b := (2 : ℝ) ^ J * T₀) F
      simp only [neg_zero] at h
      rw [← h]
      exact intervalIntegral.integral_congr fun t _ => heven t
    have hsplit : ∫ t in (0 : ℝ)..((2 : ℝ) ^ J * T₀), F t =
        (∫ t in (0 : ℝ)..T₀, F t) + ∑ j ∈ Finset.range J,
          ∫ t in ((2 : ℝ) ^ j * T₀)..((2 : ℝ) ^ (j + 1) * T₀), F t := by
      rw [intervalIntegral.sum_integral_adjacent_intervals (a := fun j => (2 : ℝ) ^ j * T₀)
        (n := J) fun j _ => hFi.intervalIntegrable]
      simp only [pow_zero, one_mul]
      rw [intervalIntegral.integral_add_adjacent_intervals hFi.intervalIntegrable
        hFi.intervalIntegrable]
    have hshells : ∑ j ∈ Finset.range J,
        ∫ t in ((2 : ℝ) ^ j * T₀)..((2 : ℝ) ^ (j + 1) * T₀), F t ≤ ∑' j, c j :=
      (Finset.sum_le_sum fun j _ => hshell j).trans (hc.sum_le_tsum _ fun j _ => hc0 j)
    rw [← intervalIntegral.integral_add_adjacent_intervals (b := 0) hFi.intervalIntegrable
      hFi.intervalIntegrable, hneg, hsplit]
    linarith
  have hRt : Tendsto (fun J : ℕ => (2 : ℝ) ^ J * T₀) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).atTop_mul_const hT₀
  have htend := intervalIntegral_tendsto_integral hFi (tendsto_neg_atTop_atBot.comp hRt) hRt
  exact le_of_tendsto' htend hpartial

/-- At low heights the weighted symbol costs `T₀ · 2(9/4 + T₀²) C₁ ‖b‖²`. -/
theorem integral_weighted_symbol_low_le {η T₀ C₁ : ℝ} (h0 : 1 / 2 < η) (h1 : η < 1)
    (hT₀ : 0 ≤ T₀) (hw : ∀ t, |t| ≤ T₀ → criticalSourceWeight η t ≤ C₁)
    (N : ℕ) (b : ℕ → ℝ)
    (hFi : IntervalIntegrable (fun t => ‖dilationSymbol η N b t‖ ^ 2 * criticalSourceWeight η t)
      volume 0 T₀) :
    ∫ t in (0 : ℝ)..T₀, ‖dilationSymbol η N b t‖ ^ 2 * criticalSourceWeight η t ≤
      T₀ * (2 * (9 / 4 + T₀ ^ 2) * C₁) * ∑ k ∈ Finset.range N, b k ^ 2 := by
  have hnb0 : 0 ≤ ∑ k ∈ Finset.range N, b k ^ 2 := Finset.sum_nonneg fun k _ => sq_nonneg _
  have hpt : ∀ t ∈ Set.Icc (0 : ℝ) T₀,
      ‖dilationSymbol η N b t‖ ^ 2 * criticalSourceWeight η t ≤
        2 * (9 / 4 + T₀ ^ 2) * C₁ * ∑ k ∈ Finset.range N, b k ^ 2 := by
    intro t ht
    have hz : ‖(((-1 / 2 : ℝ) : ℂ) + t * I) - η‖ ^ 2 ≤ 9 / 4 + T₀ ^ 2 :=
      (norm_sq_critical_sub_le h0 h1 t).trans (by nlinarith [ht.1, ht.2])
    have hB : ‖dilationSymbol η N b t‖ ^ 2 ≤
        2 * (9 / 4 + T₀ ^ 2) * ∑ k ∈ Finset.range N, b k ^ 2 :=
      (norm_sq_dilationSymbol_le h0 N b t).trans
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hz (by norm_num)) hnb0)
    have hWt := hw t (by rw [abs_of_nonneg ht.1]; exact ht.2)
    have hW0 : 0 ≤ criticalSourceWeight η t := by unfold criticalSourceWeight; positivity
    calc ‖dilationSymbol η N b t‖ ^ 2 * criticalSourceWeight η t
        ≤ (2 * (9 / 4 + T₀ ^ 2) * ∑ k ∈ Finset.range N, b k ^ 2) * C₁ :=
          mul_le_mul hB hWt hW0 (by positivity)
      _ = 2 * (9 / 4 + T₀ ^ 2) * C₁ * ∑ k ∈ Finset.range N, b k ^ 2 := by ring
  refine (intervalIntegral.integral_mono_on hT₀ hFi intervalIntegrable_const hpt).trans
    (le_of_eq ?_)
  rw [intervalIntegral.integral_const, smul_eq_mul]
  ring

/-- `WT · 200 T (1 + log 2T) ≤ 400 C₂ T^{−1/4} (1 + log 2T)⁵` for the shell weight
`WT = C₂ (2T)^{3/4} log⁴(2T) / T²`. -/
theorem shell_weight_mul_le {C₂ T : ℝ} (hC₂ : 0 ≤ C₂) (hT : 1 ≤ T) :
    C₂ * ((2 * T) ^ (3 / 4 : ℝ) * Real.log (2 * T) ^ 4 / T ^ 2) *
        (200 * T * (1 + Real.log (2 * T))) ≤
      400 * C₂ * T ^ (-(1 / 4 : ℝ)) * (1 + Real.log (2 * T)) ^ 5 := by
  have hT0 : 0 < T := by linarith
  have hlogT2 : 0 ≤ Real.log (2 * T) := Real.log_nonneg (by linarith)
  have h34 : (2 * T) ^ (3 / 4 : ℝ) ≤ 2 * T ^ (3 / 4 : ℝ) := by
    rw [Real.mul_rpow (by norm_num) hT0.le]
    have h2 : (2 : ℝ) ^ (3 / 4 : ℝ) ≤ 2 := by
      calc (2 : ℝ) ^ (3 / 4 : ℝ) ≤ 2 ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
        _ = 2 := Real.rpow_one 2
    exact mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg hT0.le _)
  have hTq : T ^ (3 / 4 : ℝ) * T / T ^ 2 = T ^ (-(1 / 4 : ℝ)) := by
    rw [show (3 / 4 : ℝ) = -(1 / 4) + 1 by norm_num, Real.rpow_add hT0, Real.rpow_one,
      div_eq_iff (pow_pos hT0 2).ne']
    ring
  have hl4 : Real.log (2 * T) ^ 4 ≤ (1 + Real.log (2 * T)) ^ 4 :=
    pow_le_pow_left₀ hlogT2 (by linarith) 4
  have hX : (2 * T) ^ (3 / 4 : ℝ) * Real.log (2 * T) ^ 4 / T ^ 2 ≤
      2 * T ^ (3 / 4 : ℝ) * (1 + Real.log (2 * T)) ^ 4 / T ^ 2 :=
    div_le_div_of_nonneg_right (mul_le_mul h34 hl4 (by positivity) (by positivity))
      (by positivity)
  calc C₂ * ((2 * T) ^ (3 / 4 : ℝ) * Real.log (2 * T) ^ 4 / T ^ 2) *
        (200 * T * (1 + Real.log (2 * T)))
      ≤ C₂ * (2 * T ^ (3 / 4 : ℝ) * (1 + Real.log (2 * T)) ^ 4 / T ^ 2) *
        (200 * T * (1 + Real.log (2 * T))) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hX hC₂) (by positivity)
    _ = 400 * C₂ * (T ^ (3 / 4 : ℝ) * T / T ^ 2) * (1 + Real.log (2 * T)) ^ 5 := by ring
    _ = 400 * C₂ * T ^ (-(1 / 4 : ℝ)) * (1 + Real.log (2 * T)) ^ 5 := by rw [hTq]

/-- On a dyadic shell `T ≤ t ≤ 2T` above `T₀` the weighted symbol costs
`400 C₂ T^{−1/4} (1 + log 2T)⁵ ‖b‖²`. -/
theorem integral_weighted_symbol_shell_le {η T₀ C₂ T : ℝ} (h0 : 1 / 2 < η) (h1 : η < 1)
    (hC₂ : 0 ≤ C₂)
    (hw : ∀ t, T₀ ≤ |t| →
      criticalSourceWeight η t ≤ C₂ * (|t| ^ (3 / 4 : ℝ) * Real.log |t| ^ 4 / t ^ 2))
    {N : ℕ} {b : ℕ → ℝ} (hb : ∀ k, N ≤ k → b k = 0) (hT : 8 ≤ T) (hTT₀ : T₀ ≤ T)
    (hFi : IntervalIntegrable (fun t => ‖dilationSymbol η N b t‖ ^ 2 * criticalSourceWeight η t)
      volume T (2 * T)) :
    ∫ t in T..(2 * T), ‖dilationSymbol η N b t‖ ^ 2 * criticalSourceWeight η t ≤
      400 * C₂ * T ^ (-(1 / 4 : ℝ)) * (1 + Real.log (2 * T)) ^ 5 *
        ∑ k ∈ Finset.range N, b k ^ 2 := by
  have hT0 : 0 < T := by linarith
  have hnb0 : 0 ≤ ∑ k ∈ Finset.range N, b k ^ 2 := Finset.sum_nonneg fun k _ => sq_nonneg _
  have hWpt : ∀ t ∈ Set.Icc T (2 * T), criticalSourceWeight η t ≤
      C₂ * ((2 * T) ^ (3 / 4 : ℝ) * Real.log (2 * T) ^ 4 / T ^ 2) := by
    intro t ht
    have ht0 : 0 < t := by linarith [ht.1]
    have habs : |t| = t := abs_of_pos ht0
    refine (hw t (by rw [habs]; linarith [ht.1])).trans ?_
    rw [habs]
    refine mul_le_mul_of_nonneg_left ?_ hC₂
    have h1' : t ^ (3 / 4 : ℝ) ≤ (2 * T) ^ (3 / 4 : ℝ) :=
      Real.rpow_le_rpow ht0.le ht.2 (by norm_num)
    have h2' : Real.log t ^ 4 ≤ Real.log (2 * T) ^ 4 :=
      pow_le_pow_left₀ (Real.log_nonneg (by linarith [ht.1])) (Real.log_le_log ht0 ht.2) 4
    have h3' : T ^ 2 ≤ t ^ 2 := pow_le_pow_left₀ hT0.le ht.1 2
    calc t ^ (3 / 4 : ℝ) * Real.log t ^ 4 / t ^ 2
        ≤ (2 * T) ^ (3 / 4 : ℝ) * Real.log (2 * T) ^ 4 / t ^ 2 :=
          div_le_div_of_nonneg_right (mul_le_mul h1' h2' (by positivity) (by positivity))
            (by positivity)
      _ ≤ (2 * T) ^ (3 / 4 : ℝ) * Real.log (2 * T) ^ 4 / T ^ 2 :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) h3'
  have hBc : Continuous fun t => ‖dilationSymbol η N b t‖ ^ 2 :=
    (continuous_dilationSymbol η N b).norm.pow 2
  have hint1 : ∫ t in T..(2 * T), ‖dilationSymbol η N b t‖ ^ 2 * criticalSourceWeight η t ≤
      ∫ t in T..(2 * T), C₂ * ((2 * T) ^ (3 / 4 : ℝ) * Real.log (2 * T) ^ 4 / T ^ 2) *
        ‖dilationSymbol η N b t‖ ^ 2 :=
    intervalIntegral.integral_mono_on (by linarith) hFi
      ((continuous_const.mul hBc).intervalIntegrable _ _) fun t ht => by
        rw [mul_comm (C₂ * _)]
        exact mul_le_mul_of_nonneg_left (hWpt t ht) (by positivity)
  rw [intervalIntegral.integral_const_mul] at hint1
  have hsym := integral_norm_sq_dilationSymbol_shell_le h0 h1 hb hT
  calc _ ≤ C₂ * ((2 * T) ^ (3 / 4 : ℝ) * Real.log (2 * T) ^ 4 / T ^ 2) *
        (200 * T * (1 + Real.log (2 * T)) * ∑ k ∈ Finset.range N, b k ^ 2) :=
        hint1.trans (mul_le_mul_of_nonneg_left hsym (by positivity))
    _ = C₂ * ((2 * T) ^ (3 / 4 : ℝ) * Real.log (2 * T) ^ 4 / T ^ 2) *
        (200 * T * (1 + Real.log (2 * T))) * ∑ k ∈ Finset.range N, b k ^ 2 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (shell_weight_mul_le hC₂ (by linarith)) hnb0

/-- The shell constants are geometric: with `T = 2^j T₀`,
`400 C₂ T^{−1/4} (1 + log 2T)⁵ ≤ 400 C₂ T₀^{−1/4} L⁵ · (j+1)⁵ (2^{−1/4})^j`,
`L = 1 + log 2 + log T₀`. -/
theorem dyadic_shell_constant_le {C₂ T₀ : ℝ} (hC₂ : 0 ≤ C₂) (hT₀ : 1 ≤ T₀) (j : ℕ) :
    400 * C₂ * ((2 : ℝ) ^ j * T₀) ^ (-(1 / 4 : ℝ)) *
        (1 + Real.log (2 * ((2 : ℝ) ^ j * T₀))) ^ 5 ≤
      400 * C₂ * T₀ ^ (-(1 / 4 : ℝ)) * (1 + Real.log 2 + Real.log T₀) ^ 5 *
        (((j : ℝ) + 1) ^ 5 * ((2 : ℝ) ^ (-(1 / 4 : ℝ))) ^ j) := by
  have hT₀0 : 0 < T₀ := by linarith
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlogT : 0 ≤ Real.log T₀ := Real.log_nonneg hT₀
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hTr : ((2 : ℝ) ^ j * T₀) ^ (-(1 / 4 : ℝ)) =
      T₀ ^ (-(1 / 4 : ℝ)) * ((2 : ℝ) ^ (-(1 / 4 : ℝ))) ^ j := by
    rw [Real.mul_rpow (by positivity) hT₀0.le, ← Real.rpow_natCast_mul (by norm_num),
      mul_comm ((j : ℝ)), Real.rpow_mul_natCast (by norm_num), mul_comm]
  have hlog : Real.log (2 * ((2 : ℝ) ^ j * T₀)) = Real.log 2 + (j * Real.log 2 + Real.log T₀) := by
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_mul (by positivity) hT₀0.ne',
      Real.log_pow]
  have hX : 1 + Real.log (2 * ((2 : ℝ) ^ j * T₀)) ≤
      ((j : ℝ) + 1) * (1 + Real.log 2 + Real.log T₀) := by
    have e : ((j : ℝ) + 1) * (1 + Real.log 2 + Real.log T₀) -
        (1 + (Real.log 2 + (j * Real.log 2 + Real.log T₀))) = j * (1 + Real.log T₀) := by ring
    rw [hlog]
    linarith [mul_nonneg hj0 (by linarith : (0 : ℝ) ≤ 1 + Real.log T₀)]
  have hX0 : 0 ≤ 1 + Real.log (2 * ((2 : ℝ) ^ j * T₀)) := by
    rw [hlog]; positivity
  calc 400 * C₂ * ((2 : ℝ) ^ j * T₀) ^ (-(1 / 4 : ℝ)) *
        (1 + Real.log (2 * ((2 : ℝ) ^ j * T₀))) ^ 5
      = (400 * C₂ * T₀ ^ (-(1 / 4 : ℝ)) * ((2 : ℝ) ^ (-(1 / 4 : ℝ))) ^ j) *
        (1 + Real.log (2 * ((2 : ℝ) ^ j * T₀))) ^ 5 := by rw [hTr]; ring
    _ ≤ (400 * C₂ * T₀ ^ (-(1 / 4 : ℝ)) * ((2 : ℝ) ^ (-(1 / 4 : ℝ))) ^ j) *
        (((j : ℝ) + 1) * (1 + Real.log 2 + Real.log T₀)) ^ 5 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hX0 hX 5) (by positivity)
    _ = _ := by ring

/-- **The weighted symbol energy is bounded uniformly in `½ < η < 1`**:
`∫ |B(t)|² |M P(−½ + it)|² dt ≤ M Σ b_k²`. -/
theorem exists_integral_weighted_symbol_le :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ η : ℝ, 1 / 2 < η → η < 1 → ∀ (N : ℕ) (b : ℕ → ℝ),
      (∀ k, N ≤ k → b k = 0) →
      ∫ t : ℝ, ‖dilationSymbol η N b t‖ ^ 2 * criticalSourceWeight η t ≤
        M * ∑ k ∈ Finset.range N, b k ^ 2 := by
  obtain ⟨T₀, C₁, C₂, hT₀, hC₁, hC₂, hw⟩ := exists_norm_mellin_sourceProfile_sq_le
  have hT₀0 : 0 < T₀ := by linarith
  have hr0 : (0 : ℝ) < (2 : ℝ) ^ (-(1 / 4 : ℝ)) := by positivity
  have hr1 : (2 : ℝ) ^ (-(1 / 4 : ℝ)) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  have hsum5 := summable_succ_pow_five_mul_geometric hr0 hr1
  have hlogT : 0 ≤ Real.log T₀ := Real.log_nonneg (by linarith)
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  obtain ⟨A, hA⟩ : ∃ A : ℝ,
      A = 400 * C₂ * T₀ ^ (-(1 / 4 : ℝ)) * (1 + Real.log 2 + Real.log T₀) ^ 5 := ⟨_, rfl⟩
  have hA0 : 0 ≤ A := by rw [hA]; positivity
  have hS0 : 0 ≤ ∑' j : ℕ, ((j : ℝ) + 1) ^ 5 * ((2 : ℝ) ^ (-(1 / 4 : ℝ))) ^ j :=
    tsum_nonneg fun j => by positivity
  refine ⟨2 * (T₀ * (2 * (9 / 4 + T₀ ^ 2) * C₁) +
      A * ∑' j : ℕ, ((j : ℝ) + 1) ^ 5 * ((2 : ℝ) ^ (-(1 / 4 : ℝ))) ^ j),
    by positivity, fun η h0 h1 N b hb => ?_⟩
  have hnb0 : 0 ≤ ∑ k ∈ Finset.range N, b k ^ 2 := Finset.sum_nonneg fun k _ => sq_nonneg _
  by_cases hFi : Integrable fun t => ‖dilationSymbol η N b t‖ ^ 2 * criticalSourceWeight η t
  swap
  · rw [integral_undef hFi]
    positivity
  have hwη := hw η h0 h1
  refine (integral_le_of_even_dyadic hFi
    (fun t => by
      show ‖dilationSymbol η N b (-t)‖ ^ 2 * criticalSourceWeight η (-t) =
        ‖dilationSymbol η N b t‖ ^ 2 * criticalSourceWeight η t
      rw [norm_dilationSymbol_neg, criticalSourceWeight_neg])
    hT₀0 ((hsum5.mul_left A).mul_right (∑ k ∈ Finset.range N, b k ^ 2))
    (fun j => by positivity)
    (integral_weighted_symbol_low_le h0 h1 hT₀0.le (fun t ht => (hwη t).1 ht) N b
      hFi.intervalIntegrable)
    (fun j => ?_)).trans (le_of_eq ?_)
  · have h2j : (1 : ℝ) ≤ (2 : ℝ) ^ j := one_le_pow₀ (by norm_num)
    have hTT₀ : T₀ ≤ (2 : ℝ) ^ j * T₀ := le_mul_of_one_le_left hT₀0.le h2j
    rw [show (2 : ℝ) ^ (j + 1) * T₀ = 2 * ((2 : ℝ) ^ j * T₀) by rw [pow_succ]; ring]
    refine (integral_weighted_symbol_shell_le h0 h1 hC₂ (fun t ht => (hwη t).2 ht) hb
      (hT₀.trans hTT₀) hTT₀ hFi.intervalIntegrable).trans ?_
    rw [hA]
    exact mul_le_mul_of_nonneg_right (dyadic_shell_constant_le hC₂ (by linarith) j) hnb0
  · rw [tsum_mul_right, tsum_mul_left]
    ring

/-! ### Back to the chain -/

/-- `K |ε_K| ≤ 2/K` for the floor slope `ε_K = K^{−η}/K − (K+1)^{−η}/(K+1)`. -/
theorem mul_abs_floorSlope_le {η : ℝ} (h0 : 0 < η) (h1 : η < 1) (k : ℕ) :
    ((k + 1 : ℕ) : ℝ) * |((k + 1 : ℕ) : ℝ) ^ (-η) / ((k + 1 : ℕ) : ℝ) -
      (((k + 1 : ℕ) : ℝ) + 1) ^ (-η) / (((k + 1 : ℕ) : ℝ) + 1)| ≤ 2 / ((k + 1 : ℕ) : ℝ) := by
  set K : ℝ := ((k + 1 : ℕ) : ℝ) with hKdef
  have hK : 1 ≤ K := one_le_succ_cast k
  have hK0 : 0 < K := by linarith
  have hK10 : 0 < K + 1 := by linarith
  have e1 : K ^ (-η) / K = K ^ (-1 - η) := by
    rw [show -1 - η = -η - 1 by ring, Real.rpow_sub_one hK0.ne']
  have e2 : (K + 1) ^ (-η) / (K + 1) = (K + 1) ^ (-1 - η) := by
    rw [show -1 - η = -η - 1 by ring, Real.rpow_sub_one hK10.ne']
  have hD := norm_cpow_sub_cpow_le hK (z := ((-1 - η : ℝ) : ℂ))
    (by rw [Complex.ofReal_re]; linarith) zero_le_one le_rfl
  rw [Real.rpow_one, Complex.ofReal_re, ← Complex.ofReal_cpow hK0.le,
    ← Complex.ofReal_cpow hK10.le, ← Complex.ofReal_sub, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_of_neg (by linarith : -1 - η < 0)] at hD
  rw [e1, e2]
  have hp : K ^ (-1 - η) ≤ K ^ (-1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hK (by linarith)
  have hp' : K ^ (-1 : ℝ) = 1 / K := by rw [Real.rpow_neg_one, one_div]
  calc K * |K ^ (-1 - η) - (K + 1) ^ (-1 - η)|
      ≤ K * (2 * K ^ (-1 - η) * (-(-1 - η) / (2 * K))) := mul_le_mul_of_nonneg_left hD hK0.le
    _ = (1 + η) * K ^ (-1 - η) := by field_simp; ring
    _ ≤ 2 * (1 / K) := by
        rw [← hp']
        exact mul_le_mul (by linarith) hp (Real.rpow_nonneg hK0.le _) (by norm_num)
    _ = 2 / K := by ring

/-- `(Σ_k |b_k|/K)² ≤ 2 Σ b_k²`, `K = k + 1`. -/
theorem sq_sum_abs_div_succ_le (N : ℕ) (b : ℕ → ℝ) :
    (∑ k ∈ Finset.range N, |b k| * (1 / ((k + 1 : ℕ) : ℝ))) ^ 2 ≤
      2 * ∑ k ∈ Finset.range N, b k ^ 2 := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range N) (fun k => |b k|)
    (fun k => 1 / ((k + 1 : ℕ) : ℝ))
  have hinv : ∑ k ∈ Finset.range N, (1 / ((k + 1 : ℕ) : ℝ)) ^ 2 ≤ 2 := by
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun k _ => ?_))
      (sum_range_inv_succ_sq_le_two N)
    rw [div_pow, one_pow]
  have hnb0 : 0 ≤ ∑ k ∈ Finset.range N, b k ^ 2 := Finset.sum_nonneg fun k _ => sq_nonneg _
  calc _ ≤ (∑ k ∈ Finset.range N, |b k| ^ 2) *
        ∑ k ∈ Finset.range N, (1 / ((k + 1 : ℕ) : ℝ)) ^ 2 := hcs
    _ ≤ (∑ k ∈ Finset.range N, b k ^ 2) * 2 := by
        rw [Finset.sum_congr rfl fun k _ => sq_abs (b k)]
        exact mul_le_mul_of_nonneg_left hinv hnb0
    _ = 2 * ∑ k ∈ Finset.range N, b k ^ 2 := by ring

/-- **The chain against the combined profile, with the floor correction explicit**:
`Σ_{n<T} (C_η b)(n)² ≤ 8 ∫_0^∞ G² x^{−2} + 16 (Σ_k |b_k|/K)²`. -/
theorem sum_sq_centeredOperator_le_integral_add {η : ℝ} (h0 : 1 / 2 < η) (h1 : η < 1)
    (b : C₀(ℕ, ℝ)) {N : ℕ} (hb : ∀ k, N ≤ k → b k = 0) (T : ℕ)
    (hint : IntegrableOn (fun x => combinedProfile η N b x ^ 2 / x ^ 2) (Ioi 0)) :
    ∑ n ∈ Finset.range T, arithmeticDampingCenteredOperator (by linarith : (0 : ℝ) < η) b n ^ 2 ≤
      8 * (∫ x in Ioi (0 : ℝ), combinedProfile η N b x ^ 2 / x ^ 2) +
        16 * (∑ k ∈ Finset.range N, |b k| * (1 / ((k + 1 : ℕ) : ℝ))) ^ 2 := by
  have hη0 : (0 : ℝ) < η := by linarith
  set G := combinedProfile η N b with hGdef
  set ρ := (RHTower.pmPowerDampedDivisorDensity η).re with hρ
  have hρ0 : 0 < ρ := RHTower.pmPowerDampedDivisorDensity_re_pos hη0
  have hρ1 : ρ ≤ 1 := density_re_le_one hη0
  set ε : ℕ → ℝ := fun k => ((k + 1 : ℕ) : ℝ) ^ (-η) / ((k + 1 : ℕ) : ℝ) -
    (((k + 1 : ℕ) : ℝ) + 1) ^ (-η) / (((k + 1 : ℕ) : ℝ) + 1) with hε
  set E : ℝ := ∑ k ∈ Finset.range N, ((k + 1 : ℕ) : ℝ) * b k * ε k with hE
  set Sb := ∑ k ∈ Finset.range N, |b k| * (1 / ((k + 1 : ℕ) : ℝ)) with hSb
  -- the floor correction is controlled by `Σ |b_k|/K`
  have hE2 : E ^ 2 ≤ 4 * Sb ^ 2 := by
    have h1' : |E| ≤ 2 * Sb := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun k _ => ?_
      have := mul_abs_floorSlope_le hη0 h1 k
      rw [abs_mul, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < ((k + 1 : ℕ) : ℝ))]
      calc ((k + 1 : ℕ) : ℝ) * |b k| * |ε k| = |b k| * (((k + 1 : ℕ) : ℝ) * |ε k|) := by ring
        _ ≤ |b k| * (2 / ((k + 1 : ℕ) : ℝ)) := mul_le_mul_of_nonneg_left this (abs_nonneg _)
        _ = 2 * (|b k| * (1 / ((k + 1 : ℕ) : ℝ))) := by ring
    calc E ^ 2 = |E| ^ 2 := (sq_abs E).symm
      _ ≤ (2 * Sb) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1' 2
      _ = 4 * Sb ^ 2 := by ring
  -- on `[N, N+1)` the combined profile is linear with slope `−ρ E`
  have hshift : ∀ n : ℕ, ∀ x : ℝ, ((n + 1 : ℕ) : ℝ) ≤ x → x < ((n + 1 : ℕ) : ℝ) + 1 →
      G x = G ((n + 1 : ℕ) : ℝ) - ρ * (x - ((n + 1 : ℕ) : ℝ)) * E := by
    intro n x hx hx'
    simp only [hGdef, combinedProfile, hE, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [columnProfile_eq_of_mem η (N := n + 1) (K := k + 1) hx hx']
    simp only [hε, hρ]
    ring
  have hpt : ∀ n : ℕ, ∀ x : ℝ, ((n + 1 : ℕ) : ℝ) ≤ x → x < ((n + 1 : ℕ) : ℝ) + 1 →
      arithmeticDampingCenteredOperator hη0 b n ^ 2 ≤
        8 * (G x ^ 2 / x ^ 2) + 2 * E ^ 2 / ((n + 1 : ℕ) : ℝ) ^ 2 := by
    intro n x hx hx'
    rw [centeredOperator_apply_eq_combinedProfile hη0 b hb n]
    set Nn : ℝ := ((n + 1 : ℕ) : ℝ) with hNn
    have hN1 : 1 ≤ Nn := by rw [hNn]; exact one_le_succ_cast n
    have hx0 : 0 < x := by linarith
    have hGs := hshift n x hx hx'
    have hsmall : |ρ * (x - Nn) * E| ≤ |E| := by
      rw [abs_mul, abs_mul, abs_of_pos hρ0, abs_of_nonneg (by linarith : 0 ≤ x - Nn)]
      have : ρ * (x - Nn) ≤ 1 := by nlinarith
      calc ρ * (x - Nn) * |E| ≤ 1 * |E| :=
            mul_le_mul_of_nonneg_right this (abs_nonneg _)
        _ = |E| := one_mul _
    have hG2 : G Nn ^ 2 ≤ 2 * G x ^ 2 + 2 * E ^ 2 := by
      have hGN : G Nn = G x + ρ * (x - Nn) * E := by linarith
      have h := add_sq_le_two (G x) (ρ * (x - Nn) * E)
      have hsq : (ρ * (x - Nn) * E) ^ 2 ≤ E ^ 2 := by
        rw [← sq_abs (ρ * (x - Nn) * E), ← sq_abs E]
        exact pow_le_pow_left₀ (abs_nonneg _) hsmall 2
      rw [hGN]; linarith
    have hinv : 1 / Nn ^ 2 ≤ 4 / x ^ 2 := by
      rw [div_le_div_iff₀ (pow_pos (by linarith) 2) (pow_pos hx0 2)]
      nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * Nn - x) (by linarith : (0 : ℝ) ≤ 2 * Nn + x)]
    calc (G Nn / Nn) ^ 2 = G Nn ^ 2 * (1 / Nn ^ 2) := by ring
      _ ≤ (2 * G x ^ 2 + 2 * E ^ 2) * (1 / Nn ^ 2) :=
          mul_le_mul_of_nonneg_right hG2 (by positivity)
      _ = 2 * G x ^ 2 * (1 / Nn ^ 2) + 2 * E ^ 2 / Nn ^ 2 := by ring
      _ ≤ 2 * G x ^ 2 * (4 / x ^ 2) + 2 * E ^ 2 / Nn ^ 2 := by gcongr
      _ = 8 * (G x ^ 2 / x ^ 2) + 2 * E ^ 2 / Nn ^ 2 := by ring
  -- integrate over `[N, N+1)` and sum
  set f : ℝ → ℝ := fun x => G x ^ 2 / x ^ 2 with hf
  have hf0 : ∀ x, 0 ≤ f x := fun x => by simp only [hf]; positivity
  set a : ℕ → ℝ := fun i => (i : ℝ) + 1 with ha
  have hsub : ∀ i : ℕ, Icc (a i) (a (i + 1)) ⊆ Ioi 0 := fun i x hx =>
    lt_of_lt_of_le (by simp only [ha]; positivity) hx.1
  have hii : ∀ i : ℕ, IntervalIntegrable f volume (a i) (a (i + 1)) := by
    intro i
    have hle : a i ≤ a (i + 1) := by simp only [ha]; push_cast; linarith
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hle]
    exact hint.mono_set (hsub i)
  have hpt' : ∀ n : ℕ, arithmeticDampingCenteredOperator hη0 b n ^ 2 ≤
      8 * (∫ x in a n..a (n + 1), f x) + 2 * E ^ 2 / ((n + 1 : ℕ) : ℝ) ^ 2 := by
    intro n
    have hle : a n ≤ a (n + 1) := by simp only [ha]; push_cast; linarith
    have hlen : a (n + 1) - a n = 1 := by simp only [ha]; push_cast; ring
    have hmono : ∫ x in a n..a (n + 1),
        (arithmeticDampingCenteredOperator hη0 b n ^ 2 - 2 * E ^ 2 / ((n + 1 : ℕ) : ℝ) ^ 2) ≤
        ∫ x in a n..a (n + 1), 8 * f x := by
      refine intervalIntegral.integral_mono_on_of_le_Ioo hle intervalIntegrable_const
        ((hii n).const_mul 8) fun x hx => ?_
      have hx1 : ((n + 1 : ℕ) : ℝ) ≤ x := by
        have := hx.1.le; simp only [ha] at this; push_cast; linarith
      have hx2 : x < ((n + 1 : ℕ) : ℝ) + 1 := by
        have := hx.2; simp only [ha] at this; push_cast at this ⊢; linarith
      have := hpt n x hx1 hx2
      simp only [hf]
      linarith
    rw [intervalIntegral.integral_const, hlen, one_smul, intervalIntegral.integral_const_mul]
      at hmono
    exact sub_le_iff_le_add.mp hmono
  have hsum := intervalIntegral.sum_integral_adjacent_intervals (f := f) (μ := volume)
    (a := a) (n := T) fun i _ => hii i
  have h0T : a 0 ≤ a T := by simp only [ha]; push_cast; linarith [(Nat.cast_nonneg T : (0:ℝ) ≤ T)]
  have htail : ∫ x in a 0..a T, f x ≤ ∫ x in Ioi (0 : ℝ), f x := by
    rw [intervalIntegral.integral_of_le h0T]
    refine setIntegral_mono_set hint (ae_of_all _ fun x => hf0 x) ?_
    exact LE.le.eventuallyLE (show Ioc (a 0) (a T) ≤ Ioi (0 : ℝ) from fun x hx =>
      lt_trans (by simp only [ha]; norm_num) hx.1)
  have hinv := sum_range_inv_succ_sq_le_two T
  have hE0 : 0 ≤ E ^ 2 := sq_nonneg _
  calc ∑ n ∈ Finset.range T, arithmeticDampingCenteredOperator hη0 b n ^ 2
      ≤ ∑ n ∈ Finset.range T, (8 * (∫ x in a n..a (n + 1), f x) +
          2 * E ^ 2 / ((n + 1 : ℕ) : ℝ) ^ 2) := Finset.sum_le_sum fun n _ => hpt' n
    _ = 8 * (∫ x in a 0..a T, f x) +
          2 * E ^ 2 * ∑ n ∈ Finset.range T, 1 / ((n + 1 : ℕ) : ℝ) ^ 2 := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, hsum, Finset.mul_sum]
        congr 1
        exact Finset.sum_congr rfl fun n _ => by ring
    _ ≤ 8 * (∫ x in Ioi (0 : ℝ), f x) + 2 * E ^ 2 * 2 :=
        add_le_add (mul_le_mul_of_nonneg_left htail (by norm_num))
          (mul_le_mul_of_nonneg_left hinv (by positivity))
    _ ≤ 8 * (∫ x in Ioi (0 : ℝ), f x) + 16 * Sb ^ 2 := by nlinarith

/-- **The chain against the combined profile**:
`Σ_{n<T} (C_η b)(n)² ≤ 8 ∫_0^∞ G² x^{−2} + 32 Σ b_k²`. -/
theorem sum_sq_centeredOperator_le_integral {η : ℝ} (h0 : 1 / 2 < η) (h1 : η < 1)
    (b : C₀(ℕ, ℝ)) {N : ℕ} (hb : ∀ k, N ≤ k → b k = 0) (T : ℕ)
    (hint : IntegrableOn (fun x => combinedProfile η N b x ^ 2 / x ^ 2) (Ioi 0)) :
    ∑ n ∈ Finset.range T, arithmeticDampingCenteredOperator (by linarith : (0 : ℝ) < η) b n ^ 2 ≤
      8 * (∫ x in Ioi (0 : ℝ), combinedProfile η N b x ^ 2 / x ^ 2) +
        32 * ∑ k ∈ Finset.range N, b k ^ 2 := by
  have h := sum_sq_centeredOperator_le_integral_add h0 h1 b hb T hint
  have hs := sq_sum_abs_div_succ_le N b
  linarith

/-- **The chain is bounded uniformly for `½ < η < 1`.** -/
theorem exists_centeredOperator_l2_le_uniform :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (η : ℝ) (h0 : 1 / 2 < η), η < 1 → ∀ (b : C₀(ℕ, ℝ)) {N : ℕ},
      (∀ k, N ≤ k → b k = 0) → ∀ T : ℕ,
        ∑ n ∈ Finset.range T,
            arithmeticDampingCenteredOperator (by linarith : (0 : ℝ) < η) b n ^ 2 ≤
          M * ∑ k ∈ Finset.range N, b k ^ 2 := by
  obtain ⟨MF, hMF, hF⟩ := exists_integral_weighted_symbol_le
  refine ⟨8 * (MF / (2 * Real.pi)) + 32, by positivity, fun η h0 h1 b N hb T => ?_⟩
  have hnb0 : 0 ≤ ∑ k ∈ Finset.range N, b k ^ 2 := Finset.sum_nonneg fun k _ => sq_nonneg _
  obtain ⟨hint, heq⟩ := integral_sq_div_sq_eq_mellin (measurable_combinedProfile η N b) h0
    (fun x hx => (abs_combinedProfile_le_bound h0 h1 N b hx).1)
    (fun x hx => (abs_combinedProfile_le_bound h0 h1 N b hx).2)
  have hnorm : ∀ t : ℝ, ‖mellin (fun x => (combinedProfile η N b x : ℂ))
      (((-1 / 2 : ℝ) : ℂ) + t * I)‖ ^ 2 =
      ‖dilationSymbol η N b t‖ ^ 2 * criticalSourceWeight η t := by
    intro t
    rw [mellin_combinedProfile_eq h0 h1 N b t, norm_mul, mul_pow]
    rfl
  have hG : ∫ x in Ioi (0 : ℝ), combinedProfile η N b x ^ 2 / x ^ 2 ≤
      MF / (2 * Real.pi) * ∑ k ∈ Finset.range N, b k ^ 2 := by
    rw [heq, funext hnorm]
    calc 1 / (2 * Real.pi) * ∫ t : ℝ, ‖dilationSymbol η N b t‖ ^ 2 * criticalSourceWeight η t
        ≤ 1 / (2 * Real.pi) * (MF * ∑ k ∈ Finset.range N, b k ^ 2) :=
          mul_le_mul_of_nonneg_left (hF η h0 h1 N b hb) (by positivity)
      _ = MF / (2 * Real.pi) * ∑ k ∈ Finset.range N, b k ^ 2 := by ring
  refine (sum_sq_centeredOperator_le_integral h0 h1 b hb T hint).trans ?_
  calc 8 * (∫ x in Ioi (0 : ℝ), combinedProfile η N b x ^ 2 / x ^ 2) +
        32 * ∑ k ∈ Finset.range N, b k ^ 2
      ≤ 8 * (MF / (2 * Real.pi) * ∑ k ∈ Finset.range N, b k ^ 2) +
        32 * ∑ k ∈ Finset.range N, b k ^ 2 := by
        have := mul_le_mul_of_nonneg_left hG (by norm_num : (0 : ℝ) ≤ 8)
        linarith
    _ = (8 * (MF / (2 * Real.pi)) + 32) * ∑ k ∈ Finset.range N, b k ^ 2 := by ring

/-! ### Half damping -/

/-- The entries of the centred chain depend continuously on the damping. -/
theorem continuousAt_centeredRow (n k : ℕ) {η₀ : ℝ} (hη₀ : 0 < η₀) :
    ContinuousAt (fun η => arithmeticDampingCenteredRow η n k) η₀ := by
  have hpow : ∀ (m : ℕ), 0 < m → ∀ c : ℝ, Continuous fun η : ℝ => (m : ℝ) ^ (c - η) :=
    fun m hm c => continuous_const.rpow (continuous_const.sub continuous_id)
      fun _ => Or.inl (Nat.cast_pos.mpr hm).ne'
  have hcoeff : ∀ j : ℕ, Continuous fun η : ℝ => RHTower.pmPowerDampedDivisorCoeff η j := by
    intro j
    unfold RHTower.pmPowerDampedDivisorCoeff
    refine continuous_finsetSum _ fun d hd => continuous_const.mul ?_
    have h := hpow d (Nat.pos_of_mem_divisors hd) 0
    simpa using h
  have hprefix : ∀ q : ℕ, Continuous fun η : ℝ => arithmeticDampingPrefix η q := by
    intro q
    unfold arithmeticDampingPrefix
    exact continuous_finsetSum _ fun j _ => hcoeff j
  have hneg : ∀ (m : ℕ), 0 < m → Continuous fun η : ℝ => (m : ℝ) ^ (-η) := by
    intro m hm
    have h := hpow m hm 0
    simpa using h
  have hdens : ContinuousAt (fun η => (RHTower.pmPowerDampedDivisorDensity η).re) η₀ := by
    have hz : ContinuousAt (fun η : ℝ => RHTower.realZetaSeries (1 + η)) η₀ :=
      ((RHTower.contDiffAt_realZetaSeries (by linarith) 0).continuousAt).comp
        (f := fun η : ℝ => 1 + η) (by fun_prop)
    have hz0 : RHTower.realZetaSeries (1 + η₀) ≠ 0 :=
      (RHTower.realZetaSeries_pos (by linarith)).ne'
    refine (((continuousAt_const : ContinuousAt (fun _ : ℝ => (1 : ℝ)) η₀).div hz hz0)).congr ?_
    filter_upwards [Ioi_mem_nhds hη₀] with η hη
    exact (pmPowerDampedDivisorDensity_re_eq hη).symm
  unfold arithmeticDampingCenteredRow arithmeticDampingTransition arithmeticDampingEntrance
  refine ContinuousAt.sub ?_ ?_
  · refine (continuous_const.mul (((hneg (k + 1) (Nat.succ_pos k)).mul (hprefix _)).sub
      ((hneg (k + 1 + 1) (Nat.succ_pos _)).mul (hprefix _)))).continuousAt
  · refine (hdens.mul continuousAt_const).mul ?_
    have h1 := hpow (k + 1) (Nat.succ_pos k) (-1)
    have h2 := hpow (k + 1 + 1) (Nat.succ_pos _) (-1)
    exact (h1.sub h2).continuousAt

/-- **The chain is bounded at half damping**: there is `M` with
`Σ_{n<T} (C_{½} b)(n)² ≤ M Σ_k b_k²` for every finitely supported `b` and every horizon. -/
theorem exists_centeredOperator_l2_le_half :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (b : C₀(ℕ, ℝ)) {N : ℕ}, (∀ k, N ≤ k → b k = 0) → ∀ T : ℕ,
      ∑ n ∈ Finset.range T,
          arithmeticDampingCenteredOperator (by norm_num : (0 : ℝ) < 1 / 2) b n ^ 2 ≤
        M * ∑ k ∈ Finset.range N, b k ^ 2 := by
  obtain ⟨M, hM, hunif⟩ := exists_centeredOperator_l2_le_uniform
  refine ⟨M, hM, fun b N hb T => ?_⟩
  set φ : ℝ → ℝ := fun η => ∑ n ∈ Finset.range T,
    (∑ k ∈ Finset.range N, arithmeticDampingCenteredRow η n k * b k) ^ 2 with hφ
  have happ : ∀ (η : ℝ) (hη : 0 < η) (n : ℕ), arithmeticDampingCenteredOperator hη b n =
      ∑ k ∈ Finset.range N, arithmeticDampingCenteredRow η n k * b k := by
    intro η hη n
    rw [arithmeticDampingCenteredOperator_apply]
    exact tsum_eq_sum fun k hk => by rw [hb k (by simpa using hk), mul_zero]
  have hcont : ContinuousAt φ (1 / 2) := by
    simp only [hφ]
    refine tendsto_finsetSum _ fun n _ => ?_
    refine ContinuousAt.pow (tendsto_finsetSum _ fun k _ => ?_) 2
    exact (continuousAt_centeredRow n k (by norm_num)).mul continuousAt_const
  have hev : ∀ᶠ η in 𝓝[>] (1 / 2 : ℝ), φ η ≤ M * ∑ k ∈ Finset.range N, b k ^ 2 := by
    filter_upwards [Ioo_mem_nhdsGT (by norm_num : (1 / 2 : ℝ) < 1)] with η hη
    have h := hunif η hη.1 hη.2 b hb T
    simp only [hφ]
    simp only [happ η (by linarith [hη.1])] at h
    exact h
  have hlim := le_of_tendsto (hcont.tendsto.mono_left nhdsWithin_le_nhds) hev
  simp only [hφ] at hlim
  simp only [happ (1 / 2) (by norm_num)]
  exact hlim

end

end GaloisForLFunctions.SignedArithmeticEnergyIncidence
