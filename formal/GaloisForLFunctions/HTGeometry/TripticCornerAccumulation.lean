import GaloisForLFunctions.HTGeometry.MeromorphicLaurentTranslation

/-!
# Mixed-quadrant accumulation for a rank-three period pattern

Let `τ` and `σ` lie in the upper half plane and let `1, τ, σ` be independent over the integers.
If a function meromorphic on the plane has a principal-part coefficient that is `1`-periodic and
takes one constant value `v` on a mixed quadrant of the lattice pattern `p + nτ + mσ`, then
`v = 0`.

The mechanism is that a mixed quadrant contains points whose imaginary parts stay bounded: pick
`m` as the negative of the ceiling of `n·Im τ / Im σ`.  Reducing the real part by an integer keeps
the coefficient, by periodicity, and places the points in one compact rectangle.  Integer
independence makes them pairwise distinct, so a nonzero `v` would give infinitely many poles in a
compact set.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Topology

/-- The compensating index making the imaginary part bounded. -/
noncomputable def cornerIndex (τ σ : ℂ) (n : ℕ) : ℤ := -⌈(n : ℝ) * τ.im / σ.im⌉

theorem cornerIndex_im_bound {τ σ : ℂ} (hσ : 0 < σ.im) (n : ℕ) :
    -σ.im < (n : ℝ) * τ.im + (cornerIndex τ σ n : ℝ) * σ.im ∧
      (n : ℝ) * τ.im + (cornerIndex τ σ n : ℝ) * σ.im ≤ 0 := by
  have hceil : ((⌈(n : ℝ) * τ.im / σ.im⌉ : ℤ) : ℝ) < (n : ℝ) * τ.im / σ.im + 1 :=
    Int.ceil_lt_add_one _
  have hceil' : (n : ℝ) * τ.im / σ.im ≤ ((⌈(n : ℝ) * τ.im / σ.im⌉ : ℤ) : ℝ) := Int.le_ceil _
  constructor
  · have h := hceil
    simp only [cornerIndex, Int.cast_neg]
    nlinarith [hσ, h]
  · have h := hceil'
    simp only [cornerIndex, Int.cast_neg]
    nlinarith [hσ, h]

theorem cornerIndex_tendsto_atBot {τ σ : ℂ} (hτ : 0 < τ.im) (hσ : 0 < σ.im) :
    Filter.Tendsto (fun n : ℕ => cornerIndex τ σ n) Filter.atTop Filter.atBot := by
  have hmain : ∀ M : ℕ, ∀ n : ℕ, (M : ℝ) * σ.im / τ.im ≤ (n : ℝ) →
      cornerIndex τ σ n ≤ -(M : ℤ) := by
    intro M n hn
    have hle : (M : ℝ) ≤ (n : ℝ) * τ.im / σ.im := by
      rw [le_div_iff₀ hσ]
      have : (M : ℝ) * σ.im ≤ (n : ℝ) * τ.im := by
        rw [div_le_iff₀ hτ] at hn
        linarith
      linarith
    have hceil : (M : ℤ) ≤ ⌈(n : ℝ) * τ.im / σ.im⌉ := by
      exact_mod_cast Int.le_ceil_iff.mpr (by push_cast; linarith [Int.le_ceil ((n : ℝ) * τ.im / σ.im)])
    simp only [cornerIndex]
    omega
  refine Filter.tendsto_atBot.mpr ?_
  intro b
  obtain ⟨M, hM⟩ := exists_nat_ge (-b : ℤ)
  refine Filter.eventually_atTop.mpr ⟨⌈(M : ℝ) * σ.im / τ.im⌉.toNat, ?_⟩
  intro n hn
  have hn' : (M : ℝ) * σ.im / τ.im ≤ (n : ℝ) := by
    have h1 : ((⌈(M : ℝ) * σ.im / τ.im⌉.toNat : ℤ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have h2 : (M : ℝ) * σ.im / τ.im ≤ ((⌈(M : ℝ) * σ.im / τ.im⌉ : ℤ) : ℝ) := Int.le_ceil _
    have h3 : ((⌈(M : ℝ) * σ.im / τ.im⌉ : ℤ) : ℝ) ≤ ((⌈(M : ℝ) * σ.im / τ.im⌉.toNat : ℤ) : ℝ) := by
      exact_mod_cast Int.self_le_toNat _
    linarith
  have := hmain M n hn'
  omega

end GaloisForLFunctions.HTGeometry
