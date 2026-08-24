import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Topology.UniformSpace.CompactConvergence
import GaloisForLFunctions.HTGeometry.CompactUniformDilation

/-!
# Products of locally uniformly convergent complex families

Multiplication is not uniformly continuous on the whole complex plane, so uniform convergence is
preserved by products only in the presence of a bound.  On a compact set the limits are bounded, so
the product of two locally uniformly convergent families with continuous limits converges locally
uniformly to the product of the limits.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

/-- Uniform convergence is preserved by products of families with bounded limits. -/
theorem tendstoUniformlyOn_mul_of_bound {ι X : Type*} [TopologicalSpace X]
    {l : Filter ι} {F G : ι → X → ℂ} {f g : X → ℂ} {K : Set X} {M : ℝ}
    (hM : 0 ≤ M)
    (hfb : ∀ x ∈ K, ‖f x‖ ≤ M) (hgb : ∀ x ∈ K, ‖g x‖ ≤ M)
    (hF : TendstoUniformlyOn F f l K)
    (hG : TendstoUniformlyOn G g l K) :
    TendstoUniformlyOn (fun n x => F n x * G n x) (fun x => f x * g x) l K := by
  rw [Metric.tendstoUniformlyOn_iff] at hF hG ⊢
  intro ε hε
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = min 1 (ε / (2 * M + 2)) := ⟨_, rfl⟩
  have hδpos : 0 < δ := by
    rw [hδ]
    exact lt_min zero_lt_one (by positivity)
  have hδ1 : δ ≤ 1 := by rw [hδ]; exact min_le_left _ _
  have hδε : δ * (2 * M + 2) ≤ ε := by
    have h := min_le_right (1 : ℝ) (ε / (2 * M + 2))
    rw [← hδ] at h
    calc δ * (2 * M + 2) ≤ (ε / (2 * M + 2)) * (2 * M + 2) := by
          exact mul_le_mul_of_nonneg_right h (by positivity)
      _ = ε := by field_simp
  filter_upwards [hF δ hδpos, hG δ hδpos] with n hFn hGn x hx
  have h1 : ‖F n x - f x‖ < δ := by
    have := hFn x hx
    rw [dist_eq_norm] at this
    calc ‖F n x - f x‖ = ‖f x - F n x‖ := by rw [norm_sub_rev]
      _ < δ := this
  have h2 : ‖G n x - g x‖ < δ := by
    have := hGn x hx
    rw [dist_eq_norm] at this
    calc ‖G n x - g x‖ = ‖g x - G n x‖ := by rw [norm_sub_rev]
      _ < δ := this
  have hGnorm : ‖G n x‖ ≤ M + δ := by
    have hsplit : G n x = g x + (G n x - g x) := by ring
    calc ‖G n x‖ = ‖g x + (G n x - g x)‖ := by rw [← hsplit]
      _ ≤ ‖g x‖ + ‖G n x - g x‖ := norm_add_le _ _
      _ ≤ M + δ := add_le_add (hgb x hx) h2.le
  have hkey : F n x * G n x - f x * g x = (F n x - f x) * G n x + f x * (G n x - g x) := by ring
  have hbound : ‖F n x * G n x - f x * g x‖ ≤ δ * (M + δ) + M * δ := by
    rw [hkey]
    refine le_trans (norm_add_le _ _) (add_le_add ?_ ?_)
    · rw [norm_mul]
      exact mul_le_mul h1.le hGnorm (norm_nonneg _) hδpos.le
    · rw [norm_mul]
      exact mul_le_mul (hfb x hx) h2.le (norm_nonneg _) hM
  have hfinal : δ * (M + δ) + M * δ < ε := by
    have hle : δ * (M + δ) + M * δ ≤ δ * (2 * M + 1) := by nlinarith [hδ1, hδpos, hM]
    have hlt : δ * (2 * M + 1) < δ * (2 * M + 2) := by nlinarith [hδpos]
    linarith [hδε]
  rw [dist_eq_norm, norm_sub_rev]
  exact lt_of_le_of_lt hbound hfinal

/-- Uniform convergence on a compact set is preserved by multiplication when both limits are
continuous there. -/
theorem TendstoUniformlyOn.mul_of_isCompact
    {ι X : Type*} [TopologicalSpace X] {l : Filter ι}
    {F G : ι → X → ℂ} {f g : X → ℂ} {K : Set X}
    (hF : TendstoUniformlyOn F f l K) (hG : TendstoUniformlyOn G g l K)
    (hK : IsCompact K) (hf : ContinuousOn f K) (hg : ContinuousOn g K) :
    TendstoUniformlyOn (fun i x => F i x * G i x) (fun x => f x * g x) l K := by
  obtain ⟨Mf, hMf⟩ := hK.exists_bound_of_continuousOn hf
  obtain ⟨Mg, hMg⟩ := hK.exists_bound_of_continuousOn hg
  let M : ℝ := max (max Mf Mg) 0
  have hM : 0 ≤ M := by exact le_max_right _ _
  have hfb : ∀ x ∈ K, ‖f x‖ ≤ M := fun x hx =>
    (hMf x hx).trans ((le_max_left _ _).trans (le_max_left _ _))
  have hgb : ∀ x ∈ K, ‖g x‖ ≤ M := fun x hx =>
    (hMg x hx).trans ((le_max_right _ _).trans (le_max_left _ _))
  exact tendstoUniformlyOn_mul_of_bound hM hfb hgb hF hG

/-- Uniform convergence on a compact set is preserved by every natural power. -/
theorem TendstoUniformlyOn.pow_of_isCompact
    {ι X : Type*} [TopologicalSpace X] {l : Filter ι}
    {F : ι → X → ℂ} {f : X → ℂ} {K : Set X}
    (hF : TendstoUniformlyOn F f l K) (hK : IsCompact K)
    (hf : ContinuousOn f K) (n : ℕ) :
    TendstoUniformlyOn (fun i x => F i x ^ n) (fun x => f x ^ n) l K := by
  induction n with
  | zero =>
      rw [Metric.tendstoUniformlyOn_iff]
      intro ε hε
      exact Filter.Eventually.of_forall (fun i x hx => by simpa using hε)
  | succ n hn =>
      simpa only [pow_succ] using
        TendstoUniformlyOn.mul_of_isCompact hn hF hK (hf.pow n) hf

/-- Uniform convergence on a compact set avoiding zero is preserved by every integer power. -/
theorem TendstoUniformlyOn.zpow_of_isCompact_of_ne_zero
    {ι X : Type*} [TopologicalSpace X] {l : Filter ι}
    {F : ι → X → ℂ} {f : X → ℂ} {K : Set X}
    (hF : TendstoUniformlyOn F f l K) (hK : IsCompact K)
    (hf : ContinuousOn f K) (hne : ∀ x ∈ K, f x ≠ 0) (m : ℤ) :
    TendstoUniformlyOn (fun i x => F i x ^ m) (fun x => f x ^ m) l K := by
  cases m with
  | ofNat n => simpa using TendstoUniformlyOn.pow_of_isCompact hF hK hf n
  | negSucc n =>
      have hpow := TendstoUniformlyOn.pow_of_isCompact hF hK hf (n + 1)
      have hone : TendstoUniformlyOn (fun _ : ι => fun _ : X => (1 : ℂ))
          (fun _ => 1) l K := by
        rw [Metric.tendstoUniformlyOn_iff]
        intro ε hε
        exact Filter.Eventually.of_forall (fun i x hx => by simpa using hε)
      have hdiv := TendstoUniformlyOn.div_of_isCompact_of_ne_zero hK hone hpow
        continuousOn_const (hf.pow (n + 1))
        (fun x hx => pow_ne_zero (n + 1) (hne x hx))
      simpa [zpow_negSucc] using hdiv

/-- **Locally uniform convergence is preserved by products with continuous limits.** -/
theorem tendstoLocallyUniformly_mul {ι X : Type*} [TopologicalSpace X] [LocallyCompactSpace X]
    {l : Filter ι} {F G : ι → X → ℂ} {f g : X → ℂ}
    (hF : TendstoLocallyUniformly F f l) (hG : TendstoLocallyUniformly G g l)
    (hf : Continuous f) (hg : Continuous g) :
    TendstoLocallyUniformly (fun n x => F n x * G n x) (fun x => f x * g x) l := by
  rw [tendstoLocallyUniformly_iff_forall_isCompact] at hF hG ⊢
  intro K hK
  exact TendstoUniformlyOn.mul_of_isCompact
    (hF K hK) (hG K hK) hK hf.continuousOn hg.continuousOn

end GaloisForLFunctions.HTGeometry
