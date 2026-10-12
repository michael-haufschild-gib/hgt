import GaloisForLFunctions.RHTower.PaperWoldNearOperator
import GaloisForLFunctions.HTGeometry.PaperCoordinateCompression
import GaloisForLFunctions.HTGeometry.QuasinilpotentLowering

/-! # Finite observations and the spectrum of the directed Wold interaction

The complete operator strictly lowers finite coordinate supports. Compactness
therefore forces every spectral value to zero, without removing its signed entries.
-/

namespace RHTower
noncomputable section
open Filter Topology GaloisForLFunctions GaloisForLFunctions.HTGeometry
open scoped BigOperators ENNReal

instance paperWoldHistory_nontrivial : Nontrivial PaperWoldHistory := by
  refine ⟨⟨lp.single 2 0 (1 : ℂ), 0, ?_⟩⟩
  intro h
  have h10 : (1 : ℂ) = 0 := by
    simpa [lp.single_apply] using congrArg (fun x : PaperWoldHistory => x 0) h
  exact one_ne_zero h10

def paperWoldPrefixProjection (N : ℕ) : PaperWoldHistory →L[ℂ] PaperWoldHistory :=
  paperCoordinateProjection N

@[simp] theorem paperWoldPrefixProjection_apply (N : ℕ) (x : PaperWoldHistory) (n : ℕ) :
    paperWoldPrefixProjection N x n = if n < N then x n else 0 :=
  paperCoordinateProjection_coordinate N x n

theorem paperWoldPrefixProjection_complement_norm (N : ℕ) :
    ‖1 - paperWoldPrefixProjection N‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  simp only [sub_apply, one_apply_eq_self, one_mul]
  apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
  intro n
  simp only [lp.coeFn_sub, Pi.sub_apply, paperWoldPrefixProjection_apply]
  split_ifs <;> simp

theorem paperWoldPrefixProjection_strong (x : PaperWoldHistory) :
    Tendsto (fun N => paperWoldPrefixProjection N x) atTop (𝓝 x) :=
  tendsto_paperCoordinateProjection x

theorem paperWoldPrefixProjection_complement_strong (x : PaperWoldHistory) :
    Tendsto (fun N => (1 - paperWoldPrefixProjection N) x) atTop (𝓝 0) := by
  simpa only [sub_apply, one_apply_eq_self, sub_self] using
    (tendsto_const_nhds (x := x)).sub (paperWoldPrefixProjection_strong x)

theorem paperWoldNearOperator_pow_vanish (p : PaperWoldNearParameters) (m N : ℕ)
    (x : PaperWoldHistory) (hx : ∀ j, N ≤ j → x j = 0) :
    ∀ n, N ≤ n + m → (paperWoldNearOperator p ^ m) x n = 0 := by
  induction m with
  | zero => intro n hn; simpa using hx n (by simpa using hn)
  | succ m ih =>
      intro n hn
      rw [pow_succ']
      change paperWoldNearOperator p ((paperWoldNearOperator p ^ m) x) n = 0
      rw [paperWoldNearOperator_apply]
      trans ∑' _ : ℕ, (0 : ℂ)
      · apply tsum_congr
        intro k
        rw [ih (n + k + 1) (by omega), mul_zero]
      · exact tsum_zero

theorem paperWoldNearOperator_pow_prefix_zero (p : PaperWoldNearParameters) (N k : ℕ)
    (hk : N ≤ k) : (paperWoldNearOperator p ^ k) * paperWoldPrefixProjection N = 0 := by
  ext x n
  apply paperWoldNearOperator_pow_vanish p k N (paperWoldPrefixProjection N x)
    (fun j hj => by simp [not_lt_of_ge hj]) n (by omega)

theorem paperWoldNearOperator_spectral_value (p : PaperWoldNearParameters) {z : ℂ}
    (hz : z ∈ spectrum ℂ (paperWoldNearOperator p)) : z = 0 :=
  QuasinilpotentLowering.eq_zero_of_mem_spectrum_of_isCompactOperator
    (paperWoldNearOperator p) paperWoldPrefixProjection paperWoldPrefixProjection_complement_norm
    paperWoldPrefixProjection_complement_strong
    (fun N k hk => paperWoldNearOperator_pow_prefix_zero p N k (by omega))
    (paperWoldNearOperator_compact p) hz

theorem paperWoldNearOperator_spectrum_subset (p : PaperWoldNearParameters) :
    spectrum ℂ (paperWoldNearOperator p) ⊆ {0} :=
  fun _ hz => paperWoldNearOperator_spectral_value p hz

def paperWoldNearCutoff (p : PaperWoldNearParameters) (N : ℕ) :
    PaperWoldHistory →L[ℂ] PaperWoldHistory := paperWoldPrefixProjection N * paperWoldNearOperator p

@[simp] theorem paperWoldNearCutoff_apply (p : PaperWoldNearParameters) (N : ℕ)
    (x : PaperWoldHistory) (n : ℕ) :
    paperWoldNearCutoff p N x n = if n < N then paperWoldNearOperator p x n else 0 :=
  paperWoldPrefixProjection_apply N (paperWoldNearOperator p x) n

theorem paperWoldNearCutoff_compact (p : PaperWoldNearParameters) (N : ℕ) :
    IsCompactOperator (paperWoldNearCutoff p N) :=
  (paperWoldNearOperator_compact p).clm_comp (paperWoldPrefixProjection N)

theorem paperWoldNearCutoff_norm_tendsto (p : PaperWoldNearParameters) :
    Tendsto (paperWoldNearCutoff p) atTop (𝓝 (paperWoldNearOperator p)) := by
  have h := QuasinilpotentLowering.tendsto_norm_comp_of_isCompactOperator
    (fun N => 1 - paperWoldPrefixProjection N) paperWoldPrefixProjection_complement_norm
    paperWoldPrefixProjection_complement_strong (paperWoldNearOperator p) (paperWoldNearOperator_compact p)
  have he (N : ℕ) : (1 - paperWoldPrefixProjection N) * paperWoldNearOperator p =
      paperWoldNearOperator p - paperWoldNearCutoff p N := by
    unfold paperWoldNearCutoff
    noncomm_ring
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simpa only [he, norm_sub_rev] using h

theorem paperWoldNearCutoff_traceCost (p : PaperWoldNearParameters) (N : ℕ) :
    compactOperatorTraceCost PaperWoldHistory (paperWoldNearCutoff p N) = 0 :=
  (compactOperatorTraceCost_eq_zero_iff _).mpr (paperWoldNearCutoff_compact p N)

end
end RHTower
