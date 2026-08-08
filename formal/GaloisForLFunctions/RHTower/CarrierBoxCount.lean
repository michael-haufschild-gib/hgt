/-
Reading the enclosed off-line order of the completed carrier off a boundary contour integral.

The completed carrier factors as `completedGN N = archFactor · gN`, where the archimedean dressing
`archFactor = s(s−1)/2 · Γ_ℝ(s)` is analytic and zero-free away from `{0,1}` and the `Γ_ℝ` poles.
On a region `U` avoiding those points the Euler head therefore contributes no zeros: every zero of
`completedGN` in `U` is a zero of `gN`.  Peeling `gN`'s finitely many `U`-zeros off a nonvanishing
analytic cofactor and absorbing `archFactor` into it gives
`completedGN N = (∏_{w} (·−w)^{m w}) · (archFactor · h)` with `archFactor · h` analytic and zero-free.

Feeding this factorization to the rectangle zero-count `rectIntegral_logDeriv_boxCount`, the boundary
contour integral of the logarithmic derivative reads off the exact integer total order of the
enclosed off-line zeros: `∮_{∂R} (completedGN)'/(completedGN) = 2πi · Σ_w (order at w)`.  The mod-`n`
deck cocycle sees only that total mod `n`; the contour integral recovers the full integer count.
-/
import GaloisForLFunctions.HTGeometry.RectangleResidue
import GaloisForLFunctions.RHTower.ZetaCarrier

open Complex Set

namespace RHTower

/-! ### §1 The vanishing order of a boxed factorization -/

/-- A linear factor has a simple zero at its root. -/
private theorem analyticOrderAt_linear (w : ℂ) : analyticOrderAt (fun z : ℂ => z - w) w = 1 := by
  have h : AnalyticAt ℂ (fun z : ℂ => z - w) w := analyticAt_id.sub analyticAt_const
  have hc := h.analyticOrderAt_eq_natCast (n := 1); rw [Nat.cast_one] at hc
  rw [hc]; exact ⟨fun _ => 1, analyticAt_const, one_ne_zero, by filter_upwards with z using by simp⟩

/-- The vanishing order of a finite product is the sum of the vanishing orders. -/
theorem analyticOrderAt_finset_prod {ι : Type*} (s : Finset ι) (g : ι → ℂ → ℂ) (w : ℂ)
    (hg : ∀ i ∈ s, AnalyticAt ℂ (g i) w) :
    analyticOrderAt (∏ i ∈ s, g i) w = ∑ i ∈ s, analyticOrderAt (g i) w := by
  classical
  induction s using Finset.induction with
  | empty =>
      simp only [Finset.prod_empty, Finset.sum_empty]
      exact analyticOrderAt_eq_zero.mpr (Or.inr (by rw [Pi.one_apply]; exact one_ne_zero))
  | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha,
        analyticOrderAt_mul (hg a (Finset.mem_insert_self a s))
          (Finset.analyticAt_prod s (fun i hi => hg i (Finset.mem_insert_of_mem hi))),
        ih (fun i hi => hg i (Finset.mem_insert_of_mem hi))]

/-- The vanishing order of a power factor `(·−v)^k` at `w` is `k` times that of `(·−v)`. -/
private theorem analyticOrderAt_powFactor (v w : ℂ) (k : ℕ) :
    analyticOrderAt (fun z : ℂ => (z - v) ^ k) w = k • analyticOrderAt (fun z : ℂ => z - v) w := by
  have hlin : AnalyticAt ℂ (fun z : ℂ => z - v) w := analyticAt_id.sub analyticAt_const
  have he : (fun z : ℂ => (z - v) ^ k) = (fun z : ℂ => z - v) ^ k := rfl
  rw [he, analyticOrderAt_pow hlin k]

/-- **The vanishing order of a boxed factorization is the recorded multiplicity.**  If `f` factors
on a neighbourhood of `ρ i₀` as `(∏_{i∈t} (·−ρ i)^{m i}) · h` with `h` analytic nonvanishing and the
centres `ρ` distinct on `t`, then `f` vanishes at `ρ i₀` to exactly order `m i₀`: the off-diagonal
linear factors and the cofactor are all nonzero there, so only the `i₀` power contributes. -/
theorem analyticOrderAt_of_boxFactorization {κ : Type*} (t : Finset κ) (ρ : κ → ℂ) (m : κ → ℕ)
    {f h : ℂ → ℂ} {U : Set ℂ} (hUopen : IsOpen U)
    (hρinj : ∀ i ∈ t, ∀ j ∈ t, ρ i = ρ j → i = j)
    (hh : AnalyticOnNhd ℂ h U) (hh0 : ∀ z ∈ U, h z ≠ 0)
    (hfact : ∀ z ∈ U, f z = (∏ i ∈ t, (z - ρ i) ^ m i) * h z)
    {i₀ : κ} (hi₀ : i₀ ∈ t) (hρU : ρ i₀ ∈ U) :
    analyticOrderAt f (ρ i₀) = m i₀ := by
  classical
  have hev : f =ᶠ[nhds (ρ i₀)] (fun z => (∏ i ∈ t, (z - ρ i) ^ m i) * h z) := by
    filter_upwards [hUopen.mem_nhds hρU] with z hz using hfact z hz
  have hpe : (fun z : ℂ => ∏ i ∈ t, (z - ρ i) ^ m i) = ∏ i ∈ t, (fun z : ℂ => (z - ρ i) ^ m i) := by
    funext z; rw [Finset.prod_apply]
  have hFan : AnalyticAt ℂ (fun z : ℂ => ∏ i ∈ t, (z - ρ i) ^ m i) (ρ i₀) := by
    rw [hpe]
    exact Finset.analyticAt_prod t (fun i _ => (analyticAt_id.sub analyticAt_const).pow (m i))
  rw [analyticOrderAt_congr hev,
    show (fun z => (∏ i ∈ t, (z - ρ i) ^ m i) * h z)
        = (fun z => ∏ i ∈ t, (z - ρ i) ^ m i) * h from rfl,
    analyticOrderAt_mul hFan (hh (ρ i₀) hρU),
    analyticOrderAt_eq_zero.mpr (Or.inr (hh0 (ρ i₀) hρU)), add_zero, hpe,
    analyticOrderAt_finset_prod t (fun i => fun z : ℂ => (z - ρ i) ^ m i) (ρ i₀)
      (fun i _ => show AnalyticAt ℂ (fun z : ℂ => (z - ρ i) ^ m i) (ρ i₀) from
        (analyticAt_id.sub analyticAt_const).pow (m i)),
    Finset.sum_eq_single_of_mem i₀ hi₀ ?_]
  · rw [analyticOrderAt_powFactor (ρ i₀) (ρ i₀) (m i₀), analyticOrderAt_linear]; simp
  · intro i hi hne
    have hz0 : analyticOrderAt (fun z : ℂ => z - ρ i) (ρ i₀) = 0 :=
      analyticOrderAt_eq_zero.mpr (Or.inr (show (fun z : ℂ => z - ρ i) (ρ i₀) ≠ 0 from
        sub_ne_zero.mpr (fun he => hne (hρinj i hi i₀ hi₀ he.symm))))
    rw [analyticOrderAt_powFactor (ρ i) (ρ i₀) (m i), hz0, smul_zero]

/-! ### §2 The completed carrier -/

/-- **The Euler-head cofactor factorization of the completed carrier.**  On an open `U` avoiding the
`Γ_ℝ` poles of both `s` and `1−s` and the trivial points `{0,1}`, whose `gN`-zeros lie in a finite
set `t` of finite order, the completed carrier factors through those zeros with the archimedean
factor absorbed into a nonvanishing analytic cofactor:
`completedGN N = (∏_{w∈t} (·−w)^{m w}) · h`, `h = archFactor · (gN cofactor)`, and each recorded
multiplicity `m w` is exactly the vanishing order of `completedGN N` at `w`. -/
theorem completedGN_offline_factor {N : ℕ} {U : Set ℂ} (hUopen : IsOpen U)
    (hGa : ∀ z ∈ U, Gammaℝ z ≠ 0) (hGb : ∀ z ∈ U, Gammaℝ (1 - z) ≠ 0)
    (hz0 : ∀ z ∈ U, z ≠ 0) (hz1 : ∀ z ∈ U, z ≠ 1)
    (t : Finset ℂ) (htU : ∀ w ∈ t, w ∈ U)
    (hzeros : ∀ z ∈ U, gN N z = 0 → z ∈ t)
    (hord : ∀ w ∈ t, analyticOrderAt (gN N) w ≠ ⊤) :
    ∃ (m : ℂ → ℕ) (h : ℂ → ℂ), AnalyticOnNhd ℂ h U ∧ (∀ z ∈ U, h z ≠ 0) ∧
      (∀ z ∈ U, completedGN N z = (∏ w ∈ t, (z - w) ^ m w) * h z) ∧
      (∀ w ∈ t, analyticOrderAt (completedGN N) w = m w) := by
  have hgN_an : AnalyticOnNhd ℂ (gN N) U := fun z hz => gN_analyticAt (hGb z hz)
  have harch_an : AnalyticOnNhd ℂ archFactor U := by
    intro z hz
    have hpoly : AnalyticAt ℂ (fun s : ℂ => s * (s - 1) / 2) z := by
      apply AnalyticAt.div_const
      exact analyticAt_id.mul (analyticAt_id.sub analyticAt_const)
    exact hpoly.mul (Gammaℝ_analyticAt (hGa z hz))
  obtain ⟨m, hg, hgan, hg0, hgfact⟩ := exists_multi_peel hUopen hgN_an t htU hzeros hord
  have han : AnalyticOnNhd ℂ (fun z => archFactor z * hg z) U :=
    fun z hz => (harch_an z hz).mul (hgan z hz)
  have h0 : ∀ z ∈ U, (fun z => archFactor z * hg z) z ≠ 0 :=
    fun z hz => mul_ne_zero (archFactor_ne_zero (hz0 z hz) (hz1 z hz) (hGa z hz)) (hg0 z hz)
  have hfact_arch : ∀ z ∈ U, completedGN N z
      = (∏ w ∈ t, (z - w) ^ m w) * (archFactor z * hg z) :=
    fun z hz => by rw [completedGN, hgfact z hz]; ring
  exact ⟨m, fun z => archFactor z * hg z, han, h0, hfact_arch, fun w hw =>
    analyticOrderAt_of_boxFactorization t (fun w => w) m hUopen (fun i _ j _ hij => hij)
      han h0 hfact_arch hw (htU w hw)⟩

/-- **The completed carrier's enclosed off-line order is a boundary contour integral.**  For a
rectangle strictly inside a region `U` avoiding the `Γ_ℝ` poles and trivial points, on which the
`gN`-zeros form a finite interior set `t` of finite order, the boundary contour integral of the
logarithmic derivative of `completedGN N` equals `2πi · Σ_{w∈t} (order of completedGN N at w)`, the
exact integer total order of the enclosed off-line zeros.  The deck cocycle recovers only its
reduction mod `n`; the contour integral recovers the full integer count. -/
theorem completedGN_rectIntegral_logDeriv {N : ℕ} {z₁ z₂ : ℂ} {U : Set ℂ} (hUopen : IsOpen U)
    (hsub : (uIcc z₁.re z₂.re ×ℂ uIcc z₁.im z₂.im) ⊆ U)
    (hGa : ∀ z ∈ U, Gammaℝ z ≠ 0) (hGb : ∀ z ∈ U, Gammaℝ (1 - z) ≠ 0)
    (hz0 : ∀ z ∈ U, z ≠ 0) (hz1 : ∀ z ∈ U, z ≠ 1)
    (t : Finset ℂ)
    (hin : ∀ w ∈ t, z₁.re < w.re ∧ w.re < z₂.re ∧ z₁.im < w.im ∧ w.im < z₂.im)
    (hzeros : ∀ z ∈ U, gN N z = 0 → z ∈ t)
    (hord : ∀ w ∈ t, analyticOrderAt (gN N) w ≠ ⊤) :
    rectIntegral (logDeriv (completedGN N)) z₁ z₂ =
      2 * Real.pi * I * (∑ w ∈ t, ((analyticOrderAt (completedGN N) w).toNat : ℂ)) := by
  have htU : ∀ w ∈ t, w ∈ U := fun w hw => by
    obtain ⟨hr1, hr2, hi1, hi2⟩ := hin w hw
    exact hsub (Complex.mem_reProdIm.mpr
      ⟨mem_uIcc.mpr (Or.inl ⟨hr1.le, hr2.le⟩), mem_uIcc.mpr (Or.inl ⟨hi1.le, hi2.le⟩)⟩)
  obtain ⟨m, h, han, h0, hfact, hpin⟩ :=
    completedGN_offline_factor hUopen hGa hGb hz0 hz1 t htU hzeros hord
  have hval := rectIntegral_logDeriv_boxCount t (fun w => w) m hUopen hin hsub han h0 hfact
  have hsum : (∑ w ∈ t, (m w : ℂ))
      = ∑ w ∈ t, ((analyticOrderAt (completedGN N) w).toNat : ℂ) :=
    Finset.sum_congr rfl (fun w hw => by rw [hpin w hw]; simp)
  rw [hval, hsum]

end RHTower
