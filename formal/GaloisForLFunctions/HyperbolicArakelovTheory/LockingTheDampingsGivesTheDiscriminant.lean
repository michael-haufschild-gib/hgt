import GaloisForLFunctions.SurfaceOfSpecZ.HyperbolicQuotientsJetCarriersAndCoupledDamping
import GaloisForLFunctions.ArithmeticIntersectionTheory.TheDifferentOfATorsionOrbit

/-!
# Locking the two dampings gives the discriminant diagonal

Off the diagonal, Weil's atomic kernel is the pole minus the archimedean Frobenius minus the prime
kernel, and both subtracted channels are limits of positive dampings: the archimedean Frobenius of
the `ℍ³` Green dampings `A_r` (`dampedFrobenius`, diagonal `n/(1 − r²)`), the prime kernel of minus the
gcd-twisted torsion energies `T̃_r` (`twistedEnergy`, diagonal `log(1/(1 − r)) + O(1)`). The
divergences differ (a power against a logarithm), so a **locked presentation** runs the torsion
channel at a reparametrized radius `ρ(r) → 1`:

  `L_r(m, n) = 2cosh((log m − log n)/2) − A_r(m, n)/√(mn) + T̃_{ρ(r)}(m, n)`   (`lockedKernel`).

Its off-diagonal limit is Weil's kernel for every `ρ` (`tendsto_lockedKernel_of_ne`). On the
diagonal the archimedean part does not depend on `n` (`lockedKernel_self`), so whatever `ρ` does,
the diagonals at two degrees differ by torsion energies alone, and

  `L_r(n, n) − L_r(1, 1) → −I(n, n)/φ(n)`   (`tendsto_lockedKernel_self_sub`),

minus the different of `ℚ(ζ_n)` per unit degree (adjunction for torsion orbits). Hence a locked
presentation that converges on the diagonal has the **arithmetic adjunction diagonal**
`D(n) = D(1) − I(n, n)/φ(n) ≤ D(1)` (`tendsto_lockedKernel_self`).

**No locked presentation of the atomic surface** (`not_eventually_posSemidef_lockedKernel`). A
counterterm-free positive damping of Weil's atomic kernel needs a diagonal `≥ N(log N − 17)/8`
somewhere in every dyadic block (`SurfaceOfSpecZ.not_atomic_countertermFree_log_diag`); the locked
diagonal is bounded. So for every reparametrization `ρ`, if `L_r` converges on the diagonal, it is
not positive semidefinite for `r` arbitrarily close to `1`.

The positive content is the identification: coupling the two natural dampings and cancelling their
divergences produces exactly the Arakelov self-intersection of the torsion orbits (the
discriminant); the Hodge index needs instead the archimedean Green potential of the configuration,
of order `N log N` (`SurfaceOfSpecZ.TheAtomicSurfaceHasGenusNLogN`). The atomic surface is not an
Arakelov surface; the diagonal must come from a smoothing.
-/

open Filter Topology Set

noncomputable section

namespace GaloisForLFunctions.HyperbolicArakelovTheory

open SurfaceOfSpecZ ArithmeticEffectivityTheory ArithmeticIntersectionTheory

/-- The locked kernel: pole minus `ℍ³` Green damping at `r` plus torsion damping at `ρ(r)`. -/
def lockedKernel (ρ : ℝ → ℝ) (r : ℝ) (m n : ℕ) : ℝ :=
  2 * Real.cosh ((Real.log m - Real.log n) / 2) - dampedFrobenius r m n / Real.sqrt ((m : ℝ) * n) +
    twistedEnergy (ρ r) m n

theorem dampedFrobenius_self (r : ℝ) (n : ℕ) :
    dampedFrobenius r n n = n * (1 - r ^ 2)⁻¹ := by
  have hn' : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  simp [dampedFrobenius, archDamped, Real.sqrt_mul_self hn', div_eq_mul_inv]

/-- On the diagonal the archimedean part is the same at every degree. -/
theorem lockedKernel_self (ρ : ℝ → ℝ) (r : ℝ) {n : ℕ} (hn : 0 < n) :
    lockedKernel ρ r n n = 2 - (1 - r ^ 2)⁻¹ + twistedEnergy (ρ r) n n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [lockedKernel, dampedFrobenius_self r n, sub_self, zero_div, Real.cosh_zero,
    Real.sqrt_mul_self hn'.le]
  field_simp

/-- Off the diagonal every locked kernel tends to Weil's kernel. -/
theorem tendsto_lockedKernel_of_ne {ρ : ℝ → ℝ} (hρ : Tendsto ρ (𝓝[<] 1) (𝓝 1)) {m n : ℕ}
    (hm : 0 < m) (hn : 0 < n) (hmn : m ≠ n) :
    Tendsto (fun r => lockedKernel ρ r m n) (𝓝[<] 1) (𝓝 (weilDeltaKernel m n)) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hs : 0 < Real.sqrt ((m : ℝ) * n) := Real.sqrt_pos.mpr (mul_pos hm' hn')
  have hA := ((tendsto_dampedFrobenius hm hn hmn).mono_left
    (nhdsWithin_le_nhds (s := Iio 1))).div_const (Real.sqrt ((m : ℝ) * n))
  have hT := (tendsto_twistedEnergy_of_ne hm hn hmn).comp hρ
  have hsum := (tendsto_const_nhds (x := 2 * Real.cosh ((Real.log m - Real.log n) / 2))).sub
    hA |>.add hT
  have hval : 2 * Real.cosh ((Real.log m - Real.log n) / 2) -
      archKernel m n / Real.sqrt ((m : ℝ) * n) + -weilPrimeKernel m n = weilDeltaKernel m n := by
    rw [archKernel_eq hm hn hmn, mul_div_cancel_left₀ _ hs.ne', weilDeltaKernel, abs_sub_comm]
    rfl
  rw [← hval]
  exact hsum

/-- **The locked diagonal is the discriminant.** `L_r(n, n) − L_r(1, 1) → −I(n, n)/φ(n)`. -/
theorem tendsto_lockedKernel_self_sub {ρ : ℝ → ℝ} (hρ : Tendsto ρ (𝓝[<] 1) (𝓝 1)) {n : ℕ}
    (hn : 0 < n) :
    Tendsto (fun r => lockedKernel ρ r n n - lockedKernel ρ r 1 1) (𝓝[<] 1)
      (𝓝 (-selfIntersection n)) := by
  have h1 := (tendsto_twistedEnergy_self_add_log hn).comp hρ
  have h0 := (tendsto_twistedEnergy_self_add_log one_pos).comp hρ
  have hsI1 : selfIntersection 1 = 0 := by
    rw [selfIntersection_eq one_pos]; simp [tameDifferent]
  have hsub := h1.sub h0
  have hval : -(orbitIntersection n n / (Nat.totient n : ℝ)) -
      -(orbitIntersection 1 1 / (Nat.totient 1 : ℝ)) = -selfIntersection n := by
    have : orbitIntersection 1 1 / (Nat.totient 1 : ℝ) = 0 := hsI1
    rw [this, selfIntersection]; ring
  rw [hval] at hsub
  refine hsub.congr' (Eventually.of_forall fun r => ?_)
  simp only [Function.comp]
  rw [lockedKernel_self ρ r hn, lockedKernel_self ρ r one_pos]
  ring

/-- A locked presentation converging at degree one converges at every degree, to
`D(1) − I(n, n)/φ(n)`. -/
theorem tendsto_lockedKernel_self {ρ : ℝ → ℝ} (hρ : Tendsto ρ (𝓝[<] 1) (𝓝 1)) {D₁ : ℝ}
    (h1 : Tendsto (fun r => lockedKernel ρ r 1 1) (𝓝[<] 1) (𝓝 D₁)) {n : ℕ} (hn : 0 < n) :
    Tendsto (fun r => lockedKernel ρ r n n) (𝓝[<] 1) (𝓝 (D₁ - selfIntersection n)) := by
  have := h1.add (tendsto_lockedKernel_self_sub hρ hn)
  rw [← sub_eq_add_neg] at this
  refine this.congr' (Eventually.of_forall fun r => ?_)
  ring

/-- **No locked presentation of the atomic surface.** For every reparametrization `ρ(r) → 1`, a
locked kernel converging on the diagonal is not positive semidefinite on all finite sets of
degrees for every `r` near `1`. -/
theorem not_eventually_posSemidef_lockedKernel {ρ : ℝ → ℝ} (hρ : Tendsto ρ (𝓝[<] 1) (𝓝 1))
    {D₁ : ℝ} (h1 : Tendsto (fun r => lockedKernel ρ r 1 1) (𝓝[<] 1) (𝓝 D₁)) :
    ¬ ∀ᶠ r in 𝓝[<] (1 : ℝ), ∀ S : Finset ℕ, (∀ n ∈ S, 0 < n) → ∀ x : ℕ → ℝ,
      0 ≤ ∑ m ∈ S, ∑ n ∈ S, x m * x n * lockedKernel ρ r m n := by
  intro hpsd
  obtain ⟨l, hl, hsub⟩ := mem_nhdsLT_iff_exists_Ioo_subset.mp hpsd
  set r₀ := (max l 0 + 1) / 2 with hr₀
  have hl1 : l < 1 := hl
  have hr₀l : l < r₀ := by rw [hr₀]; have := le_max_left l 0; linarith
  have hr₀1 : r₀ < 1 := by rw [hr₀]; have : max l 0 < 1 := max_lt hl1 one_pos; linarith
  -- a damping defined for every `r < 1` that agrees with `L_r` near `1`
  set K : ℝ → ℕ → ℕ → ℝ := fun r => lockedKernel ρ (max r r₀)
  set K₁ : ℕ → ℕ → ℝ := fun m n =>
    if m = n then D₁ - selfIntersection n else weilDeltaKernel m n
  have hev : ∀ m n : ℕ, (fun r => K r m n) =ᶠ[𝓝[<] 1] fun r => lockedKernel ρ r m n := by
    intro m n
    filter_upwards [Ioo_mem_nhdsLT hr₀1] with r hr
    simp only [K, max_eq_left hr.1.le]
  have hKpsd : ∀ r : ℝ, 0 ≤ r → r < 1 → ∀ S : Finset ℕ, (∀ n ∈ S, 0 < n) → ∀ x : ℕ → ℝ,
      0 ≤ ∑ m ∈ S, ∑ n ∈ S, x m * x n * K r m n := by
    intro r _ hr1 S hS x
    exact hsub ⟨hr₀l.trans_le (le_max_right r r₀), max_lt hr1 hr₀1⟩ S hS x
  have hKt : ∀ m n : ℕ, 0 < m → 0 < n → Tendsto (fun r => K r m n) (𝓝[<] 1) (𝓝 (K₁ m n)) := by
    intro m n hm hn
    refine Tendsto.congr' (hev m n).symm ?_
    by_cases hmn : m = n
    · subst hmn
      simp only [K₁, if_true]
      exact tendsto_lockedKernel_self hρ h1 hm
    · simp only [K₁, if_neg hmn]
      exact tendsto_lockedKernel_of_ne hρ hm hn hmn
  refine not_atomic_countertermFree_log_diag (|D₁| + 1) ⟨K, K₁, hKpsd, hKt, ?_, ?_⟩
  · intro m n _ _ hmn
    simp only [K₁, if_neg hmn]
  · intro n hn
    simp only [K₁, if_true]
    have hsI := selfIntersection_nonneg hn
    have hlog : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
    have : D₁ ≤ |D₁| + 1 := by linarith [le_abs_self D₁]
    nlinarith [abs_nonneg D₁]

end GaloisForLFunctions.HyperbolicArakelovTheory
