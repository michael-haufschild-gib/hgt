import GaloisForLFunctions.RHTower.ProlateNormalizedProfile
import GaloisForLFunctions.HTGeometry.WindowTotalSqueeze

/-!
# Window mass of the rescaled prolate profile

The Grönwall window comparison controls `|u − e^{−ξ²/2}|` on `[0, K]`.  Both the prolate profile and
the Gaussian are even, so the same bound holds on `[−K, K]`, and squaring costs only the factor
`|u| + |e^{−ξ²/2}| ≤ B + 1`.  Integrating gives the window mass

`|∫_{−K}^{K} u² − ∫_{−K}^{K} e^{−ξ²}| ≤ 2K(B+1)·E` ,

with `E` the Grönwall envelope.
-/

open Set Filter Topology GaloisForLFunctions.HTGeometry

namespace RHTower

theorem gaussianProfile_sq (x : ℝ) : gaussianProfile x ^ 2 = Real.exp (-(x ^ 2)) := by
  rw [gaussianProfile, sq, ← Real.exp_add]
  ring_nf

theorem gaussianProfile_pos (x : ℝ) : 0 < gaussianProfile x := Real.exp_pos _

theorem abs_gaussianProfile_le_one (x : ℝ) : |gaussianProfile x| ≤ 1 := by
  rw [abs_of_pos (gaussianProfile_pos x), gaussianProfile]
  have : -(x ^ 2) / 2 ≤ 0 := by
    have : (0 : ℝ) ≤ x ^ 2 := sq_nonneg x
    linarith
  calc Real.exp (-(x ^ 2) / 2) ≤ Real.exp 0 := Real.exp_le_exp.2 this
    _ = 1 := Real.exp_zero

theorem even_gaussianProfile : Function.Even gaussianProfile := by
  intro x
  rw [gaussianProfile, gaussianProfile, neg_pow, neg_one_pow_two, one_mul]

theorem differentiable_gaussianProfile : Differentiable ℝ gaussianProfile :=
  fun x => (hasDerivAt_gaussianProfile x).differentiableAt

theorem continuous_gaussianProfile : Continuous gaussianProfile :=
  differentiable_gaussianProfile.continuous

/-- Evenness transports a window estimate from `[0, K]` to `[−K, K]`. -/
theorem abs_sub_le_of_even_window {u : ℝ → ℝ} {K E : ℝ}
    (heu : Function.Even u)
    (hbound : ∀ x ∈ Icc (0 : ℝ) K, |u x - gaussianProfile x| ≤ E) :
    ∀ x ∈ Icc (-K) K, |u x - gaussianProfile x| ≤ E := by
  intro x hx
  have habs : |x| ∈ Icc (0 : ℝ) K := ⟨abs_nonneg x, abs_le.2 ⟨hx.1, hx.2⟩⟩
  have hu : u |x| = u x := by
    rcases abs_cases x with ⟨h, _⟩ | ⟨h, _⟩
    · rw [h]
    · rw [h, heu]
  have hg : gaussianProfile |x| = gaussianProfile x := by
    rcases abs_cases x with ⟨h, _⟩ | ⟨h, _⟩
    · rw [h]
    · rw [h, even_gaussianProfile]
  have := hbound |x| habs
  rwa [hu, hg] at this

/-- Evenness transports a difference bound against an arbitrary even comparison function from
`[0, K]` to `[−K, K]`. -/
theorem abs_sub_le_of_even_window' {u v : ℝ → ℝ} {K E : ℝ}
    (heu : Function.Even u) (hev : Function.Even v)
    (hbound : ∀ x ∈ Icc (0 : ℝ) K, |u x - v x| ≤ E) :
    ∀ x ∈ Icc (-K) K, |u x - v x| ≤ E := by
  intro x hx
  have habs : |x| ∈ Icc (0 : ℝ) K := ⟨abs_nonneg x, abs_le.2 ⟨hx.1, hx.2⟩⟩
  have hu : u |x| = u x := by
    rcases abs_cases x with ⟨h, _⟩ | ⟨h, _⟩
    · rw [h]
    · rw [h, heu]
  have hv : v |x| = v x := by
    rcases abs_cases x with ⟨h, _⟩ | ⟨h, _⟩
    · rw [h]
    · rw [h, hev]
  have hb := hbound |x| habs
  rwa [hu, hv] at hb

/-- Evenness transports an absolute bound from `[0, K]` to `[−K, K]`. -/
theorem abs_le_of_even_window {u : ℝ → ℝ} {K B : ℝ}
    (heu : Function.Even u) (hB : ∀ x ∈ Icc (0 : ℝ) K, |u x| ≤ B) :
    ∀ x ∈ Icc (-K) K, |u x| ≤ B := by
  intro x hx
  have habs : |x| ∈ Icc (0 : ℝ) K := ⟨abs_nonneg x, abs_le.2 ⟨hx.1, hx.2⟩⟩
  have hu : u |x| = u x := by
    rcases abs_cases x with ⟨h, _⟩ | ⟨h, _⟩
    · rw [h]
    · rw [h, heu]
  have := hB |x| habs
  rwa [hu] at this

/-- Squaring costs the factor `B + 1`. -/
theorem abs_sq_sub_le_of_window {u : ℝ → ℝ} {K E B : ℝ}
    (hbound : ∀ x ∈ Icc (-K) K, |u x - gaussianProfile x| ≤ E)
    (hB : ∀ x ∈ Icc (-K) K, |u x| ≤ B) :
    ∀ x ∈ Icc (-K) K, |u x ^ 2 - gaussianProfile x ^ 2| ≤ E * (B + 1) := by
  intro x hx
  have hfac : u x ^ 2 - gaussianProfile x ^ 2
      = (u x - gaussianProfile x) * (u x + gaussianProfile x) := by ring
  rw [hfac, abs_mul]
  have h1 : |u x - gaussianProfile x| ≤ E := hbound x hx
  have h2 : |u x + gaussianProfile x| ≤ B + 1 :=
    le_trans (abs_add_le _ _) (add_le_add (hB x hx) (abs_gaussianProfile_le_one x))
  have hE : (0 : ℝ) ≤ E := le_trans (abs_nonneg _) h1
  exact mul_le_mul h1 h2 (abs_nonneg _) hE

/-- **Window mass estimate.**  The window mass of the profile differs from the Gaussian window mass
by at most `2K(B+1)` times the Grönwall envelope. -/
theorem abs_windowMass_sub_le {u : ℝ → ℝ} {K E B : ℝ}
    (hK : 0 ≤ K) (hu : Continuous u)
    (hbound : ∀ x ∈ Icc (-K) K, |u x ^ 2 - gaussianProfile x ^ 2| ≤ E * (B + 1)) :
    |(∫ x in (-K)..K, u x ^ 2) - ∫ x in (-K)..K, Real.exp (-(x ^ 2))|
      ≤ E * (B + 1) * (2 * K) := by
  have hKK : (-K : ℝ) ≤ K := by linarith
  have hrw : (fun x : ℝ => Real.exp (-(x ^ 2))) = fun x : ℝ => gaussianProfile x ^ 2 :=
    funext fun x => (gaussianProfile_sq x).symm
  rw [hrw]
  have := abs_intervalIntegral_sub_le_of_uniform (f := fun x : ℝ => u x ^ 2)
    (g := fun x : ℝ => gaussianProfile x ^ 2) (a := -K) (b := K) hKK
    ((hu.pow 2).continuousOn) ((continuous_gaussianProfile.pow 2).continuousOn) hbound
  calc |(∫ x in (-K)..K, u x ^ 2) - ∫ x in (-K)..K, gaussianProfile x ^ 2|
      ≤ E * (B + 1) * (K - -K) := this
    _ = E * (B + 1) * (2 * K) := by ring

end RHTower
