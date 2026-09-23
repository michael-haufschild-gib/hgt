import GaloisForLFunctions.HTGeometry.DifferentialInequalityComparison

/-!
# A nonnegative Riccati derivative cannot dip far below the barrier profile

The logarithmic derivative `v = −ψ′/ψ` of a positive solution of a second-order equation obeys

```text
v′ = v² + B v − Q .
```

Where `Q > 0` the profile `√Q` is an attractor from above and a repeller from below: once `v`
falls below `√Q` it decreases, and once it decreases it falls faster.  So a solution that stays
*positive* on a whole interval — equivalently, a `v` that stays nonnegative there — cannot have
been much below `√Q` at the left end.  Quantitatively, with `Q ≥ S²` and `B ≤ M` on `[y₀, y₁]`,

```text
v(y₀) ≥ S − M − 2/(y₁ − y₀) .
```

This is the direction opposite to the Riccati subsolution bound `v ≤ √Q`, and it is what turns a
lower bound for the decay of a positive solution into an upper bound: integrating it gives

```text
ψ(y₁) ≤ ψ(y₀) · exp(−∫ √Q + ∫ B + log(…)) ,
```

so the sharp exponential rate survives and only a polynomial factor is lost.  No approximation
theory is involved: the whole argument is two applications of Riccati comparison against explicit
affine supersolutions.
-/

noncomputable section

open Set

namespace GaloisForLFunctions.HTGeometry

set_option maxHeartbeats 1600000 in
/-- **The Riccati no-dip bound.**  A nonnegative solution of `v′ = v² + B v − Q` on `[y₀, y₁]`
starts within `M + 2/(y₁ − y₀)` of the barrier profile `S ≤ √Q`. -/
theorem sub_sub_div_le_of_riccati_nonneg {y₀ y₁ S M : ℝ} {v v' B Q : ℝ → ℝ}
    (hlt : y₀ < y₁)
    (hvc : ContinuousOn v (Icc y₀ y₁))
    (hv : ∀ y ∈ Ioo y₀ y₁, HasDerivAt v (v' y) y)
    (hric : ∀ y ∈ Ioo y₀ y₁, v' y = v y ^ (2 : ℕ) + B y * v y - Q y)
    (hBc : ContinuousOn B (Icc y₀ y₁))
    (hvnn : ∀ y ∈ Icc y₀ y₁, 0 ≤ v y)
    (hS : 0 < S) (hQ : ∀ y ∈ Icc y₀ y₁, S ^ (2 : ℕ) ≤ Q y)
    (hB : ∀ y ∈ Icc y₀ y₁, 0 ≤ B y) (hBM : ∀ y ∈ Icc y₀ y₁, B y ≤ M) :
    S - M - 2 / (y₁ - y₀) ≤ v y₀ := by
  set L : ℝ := y₁ - y₀ with hL
  have hLpos : 0 < L := by rw [hL]; linarith
  by_contra hcon
  rw [not_le] at hcon
  set m : ℝ := v y₀ with hm
  have hm0 : 0 ≤ m := hvnn y₀ (left_mem_Icc.2 hlt.le)
  have hMnn : 0 ≤ M := le_trans (hB y₀ (left_mem_Icc.2 hlt.le)) (hBM y₀ (left_mem_Icc.2 hlt.le))
  have hgap : 0 < S - M - 2 / L := lt_of_le_of_lt hm0 hcon
  have hLinv : 0 < 2 / L := by positivity
  have hmS : m < S := by linarith
  set κ : ℝ := S ^ (2 : ℕ) - M * m - m ^ (2 : ℕ) with hκ
  have hSL : 0 < S - 2 / L := by linarith
  have hκbig : 2 * S / L < κ := by
    have h1 : m * (M + m) ≤ m * (S - 2 / L) := by nlinarith [hm0, hcon]
    have h2 : m * (S - 2 / L) < S * (S - 2 / L) := mul_lt_mul_of_pos_right hmS hSL
    have h3 : S * (S - 2 / L) = S ^ (2 : ℕ) - 2 * S / L := by
      field_simp
    rw [hκ]
    nlinarith [h1, h2, h3]
  have hκpos : 0 < κ := lt_trans (by positivity) hκbig
  -- the first comparison interval, on which the affine supersolution stays between `0` and `m`
  set z : ℝ := y₀ + m / κ with hz
  have hz0 : y₀ ≤ z := by
    rw [hz]
    have : 0 ≤ m / κ := by positivity
    linarith
  have hzhalf : m / κ < L / 2 := by
    rw [div_lt_div_iff₀ hκpos (by norm_num : (0 : ℝ) < 2)]
    have hprod : 2 * S / L * L = 2 * S := by field_simp
    nlinarith [hκbig, hLpos, hmS, hprod]
  have hz1 : z < y₁ := by
    rw [hz]
    linarith [hzhalf]
  -- stage one: the affine drop from `m` to `0`
  set U : ℝ → ℝ := fun y => m - κ * (y - y₀) with hU
  have hUderiv : ∀ y : ℝ, HasDerivAt U (-κ) y := by
    intro y
    have h : HasDerivAt (fun x : ℝ => m - κ * (x - y₀)) (0 - κ * 1) y :=
      (hasDerivAt_const y m).sub (((hasDerivAt_id y).sub_const y₀).const_mul κ)
    show HasDerivAt (fun x : ℝ => m - κ * (x - y₀)) (-κ) y
    simpa using h
  have hUc : ContinuousOn U (Icc y₀ z) :=
    (continuous_iff_continuousAt.2 fun y => (hUderiv y).continuousAt).continuousOn
  have hUrange : ∀ y ∈ Icc y₀ z, 0 ≤ U y ∧ U y ≤ m := by
    intro y hy
    have h1 : y - y₀ ≤ m / κ := by
      have := hy.2
      rw [hz] at this
      linarith
    have h2 : 0 ≤ y - y₀ := by linarith [hy.1]
    constructor
    · rw [hU]
      simp only
      have : κ * (y - y₀) ≤ κ * (m / κ) := mul_le_mul_of_nonneg_left h1 hκpos.le
      rw [mul_div_cancel₀ m hκpos.ne'] at this
      linarith
    · rw [hU]
      simp only
      nlinarith [hκpos.le, h2]
  have hstage1 : ∀ y ∈ Icc y₀ z, v y ≤ U y := by
    refine riccati_le_of_le_of_supersolution (u' := v') (U' := fun _ => -κ) hz0
      (hvc.mono (Icc_subset_Icc le_rfl hz1.le)) hUc
      (fun y hy => hv y ⟨hy.1, lt_trans hy.2 hz1⟩)
      (fun y _ => hUderiv y)
      (hBc.mono (Icc_subset_Icc le_rfl hz1.le))
      (fun y hy => le_of_eq (hric y ⟨hy.1, lt_trans hy.2 hz1⟩)) (fun y hy => ?_)
      (by show m ≤ U y₀; rw [hU]; simp)
    have hymem : y ∈ Icc y₀ z := ⟨hy.1.le, hy.2.le⟩
    have hymem' : y ∈ Icc y₀ y₁ := ⟨hy.1.le, le_of_lt (lt_trans hy.2 hz1)⟩
    obtain ⟨hU0, hUm⟩ := hUrange y hymem
    have hQy := hQ y hymem'
    have hBy := hBM y hymem'
    have hBy0 := hB y hymem'
    have hsq : U y ^ (2 : ℕ) ≤ m ^ (2 : ℕ) := by nlinarith
    have hBU : B y * U y ≤ M * m := by nlinarith
    rw [hκ]
    linarith
  have hvz : v z = 0 := by
    have h1 : v z ≤ U z := hstage1 z (right_mem_Icc.2 hz0)
    have h2 : U z = 0 := by
      rw [hU, hz]
      field_simp
      ring
    have h3 : 0 ≤ v z := hvnn z ⟨hz0, hz1.le⟩
    linarith
  -- stage two: an affine descent below zero
  set lam : ℝ := min (S ^ (2 : ℕ) / 2) (S / (2 * L)) with hlam
  have hlampos : 0 < lam := lt_min (by positivity) (by positivity)
  have hlam1 : lam ≤ S ^ (2 : ℕ) / 2 := min_le_left _ _
  have hlam2 : lam ≤ S / (2 * L) := min_le_right _ _
  set V : ℝ → ℝ := fun y => -(lam * (y - z)) with hV
  have hVderiv : ∀ y : ℝ, HasDerivAt V (-lam) y := by
    intro y
    have h : HasDerivAt (fun x : ℝ => -(lam * (x - z))) (-(lam * 1)) y :=
      (((hasDerivAt_id y).sub_const z).const_mul lam).neg
    show HasDerivAt (fun x : ℝ => -(lam * (x - z))) (-lam) y
    simpa using h
  have hVc : ContinuousOn V (Icc z y₁) :=
    (continuous_iff_continuousAt.2 fun y => (hVderiv y).continuousAt).continuousOn
  have hstage2 : ∀ y ∈ Icc z y₁, v y ≤ V y := by
    refine riccati_le_of_le_of_supersolution (u' := v') (U' := fun _ => -lam) hz1.le
      (hvc.mono (Icc_subset_Icc hz0 le_rfl)) hVc
      (fun y hy => hv y ⟨lt_of_le_of_lt hz0 hy.1, hy.2⟩)
      (fun y _ => hVderiv y)
      (hBc.mono (Icc_subset_Icc hz0 le_rfl))
      (fun y hy => le_of_eq (hric y ⟨lt_of_le_of_lt hz0 hy.1, hy.2⟩)) (fun y hy => ?_)
      (by show v z ≤ V z; rw [hV, hvz]; simp)
    have hymem' : y ∈ Icc y₀ y₁ := ⟨le_trans hz0 hy.1.le, hy.2.le⟩
    have hQy := hQ y hymem'
    have hBy0 := hB y hymem'
    have hyz : 0 ≤ y - z := by linarith [hy.1.le]
    have hyL : y - z ≤ L := by
      have := hy.2.le
      rw [hL]
      linarith [hz0]
    have hVnonpos : V y ≤ 0 := by
      have : 0 ≤ lam * (y - z) := mul_nonneg hlampos.le hyz
      rw [hV]
      linarith
    have hBV : B y * V y ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hBy0 hVnonpos
    have hVsq : V y ^ (2 : ℕ) ≤ lam ^ (2 : ℕ) * L ^ (2 : ℕ) := by
      have hexp : V y ^ (2 : ℕ) = lam ^ (2 : ℕ) * (y - z) ^ (2 : ℕ) := by rw [hV]; ring
      have hsq : (y - z) ^ (2 : ℕ) ≤ L ^ (2 : ℕ) := by nlinarith [hyz, hyL]
      rw [hexp]
      nlinarith [hlampos.le, hsq]
    have hkey : lam ^ (2 : ℕ) * L ^ (2 : ℕ) ≤ S ^ (2 : ℕ) / 4 := by
      have h1 : lam * (2 * L) ≤ S := by
        rw [le_div_iff₀ (by positivity)] at hlam2
        linarith
      have h2 : (lam * (2 * L)) ^ (2 : ℕ) ≤ S ^ (2 : ℕ) :=
        pow_le_pow_left₀ (by positivity) h1 2
      nlinarith [h2]
    linarith
  have hfinal : v y₁ ≤ V y₁ := hstage2 y₁ (right_mem_Icc.2 hz1.le)
  have hVneg : V y₁ < 0 := by
    have hpos : 0 < lam * (y₁ - z) := mul_pos hlampos (by linarith)
    rw [hV]
    linarith
  have := hvnn y₁ (right_mem_Icc.2 hlt.le)
  linarith

end GaloisForLFunctions.HTGeometry
