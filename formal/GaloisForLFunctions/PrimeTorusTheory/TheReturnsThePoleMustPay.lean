import GaloisForLFunctions.PrimeTorusTheory.LargeValueHeightsFormAnApproximateGroup
import GaloisForLFunctions.PrimeTorusTheory.UniqueFactorizationPaysForNonAlignment
import GaloisForLFunctions.SignedSuccessorArithmetic.TheSignedPrimeDivisorEndpointAtHalfDamping
import GaloisForLFunctions.RHTower.ZetaNearOneLineBound
import GaloisForLFunctions.RHTower.PrimeHarmonicLogLower

/-!
# The returns the pole must pay for

Does a large-value set of heights have additive structure, and does its structure force returns that the pole must pay for? Yes, at the weights `1/p`, where the
Euler product sees the pole.

**The price at the pole** (`column_le_pole`). For `|u| ≥ 8`, `Σ_{p ≤ z} cos(u log p)/p ≤ log(8 log|u| + 39) + C`, while the size `Σ_{p≤z} 1/p` is at least `log log z − 1`. So a height at
level `θ` is at height at least `exp(c (log z)^θ)` (`le_log_of_mem_largeValue`): a return is paid by a spike of `ζ` near `1 + iu`, and `ζ` has no such spike below that height.

**Additive structure forces the payment.** Two heights at level `θ` differ by a height at level `2θ² − 1` (`pair_level_le`); `N` heights in a window of length `L` have a difference of size at most
`L/J` at level `θ² − (1 − θ²)/(m − 1)` (`exists_low_return_of_many_large_values`). So the number of heights at level `θ` in a window of length `L` at weights `1/p` is bounded through the pole
(`card_le_of_pole`), and it is bounded by the height where the pole first permits the difference level.

**The horizon.** Non-alignment at these weights is unconditional for `z ≥ exp((C log T)^{1/θ})` (`not_mem_largeValue_of_lt`), which is far below the mixing time.
For fixed height the orbit leaves every level as `z → ∞` (`eventually_not_mem_largeValue`): returns escape to infinity with the length.

The pole pays nothing at the critical weights `p^{−½}`, and that is where the saving of `TheSavingAgainstSize` is the best available. The Kronecker scale `y ≍ log T` shows that a saving at
weights `1/p` must stop at the corresponding level: `exists_column_ge_of_primesUpTo` reaches level `m/(m + 1)` of the mass of the primes up to `y`.
-/

open Finset Filter Topology

namespace GaloisForLFunctions.PrimeTorusTheory

noncomputable section

/-- The system of primes up to `z` with the weights `1/p`, where the Euler product sees the pole. -/
def harmonicSystem (z : ℕ) : PhaseSystem (primesUpTo z) :=
  primeSystem (primesUpTo z) (fun p => 1 / (p : ℝ)) fun _ _ => by positivity

/-- The constant in the price at the pole. -/
def poleConst : ℝ :=
  Real.pi ^ 2 / 6 + 2 * (Real.log 2 + 2 * (2 * RHTower.Sieve.mertensFirstConst + 1 / 2)) / Real.log 2 +
    (1 + Real.log 4)

theorem primesUpTo_eq_primesLE (z : ℕ) : primesUpTo z = Nat.primesLE z := by
  ext p
  rw [Nat.mem_primesLE]
  constructor
  · intro hp
    exact ⟨le_of_mem_primesUpTo hp, prime_of_mem_primesUpTo hp⟩
  · rintro ⟨h1, h2⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), h2⟩

theorem primesUpTo_eq_primesBelow (z : ℕ) : primesUpTo z = Nat.primesBelow (z + 1) := rfl

theorem harmonicSystem_column (z : ℕ) (u : ℝ) :
    (harmonicSystem z).column u = ∑ p ∈ Nat.primesLE z, Real.cos (u * Real.log p) / (p : ℝ) := by
  unfold harmonicSystem
  rw [primeSystem_column, primesUpTo_eq_primesLE]
  refine Finset.sum_congr rfl fun p _ => ?_
  ring

/-- The size at the weights `1/p` grows like `log log z`. -/
theorem harmonicSystem_size_ge {z : ℕ} (hz : 1 ≤ z) :
    Real.log (Real.log ((z : ℝ) + 1)) - 1 ≤ (harmonicSystem z).size := by
  have h := RHTower.log_log_sub_one_le_sum_primesBelow_inv z hz
  unfold harmonicSystem
  rw [primeSystem_size, primesUpTo_eq_primesBelow]
  refine h.trans (le_of_eq ?_)
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [one_div]

/-- **The price at the pole.** -/
theorem column_le_pole {z : ℕ} (hz : 3 ≤ z) {u : ℝ} (hu : 8 ≤ |u|) :
    (harmonicSystem z).column u ≤ Real.log (8 * Real.log |u| + 39) + poleConst := by
  have hz3 : (3 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz
  have hlogz : 1 ≤ Real.log (z : ℝ) := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9
    linarith
  have hlogz0 : 0 < Real.log (z : ℝ) := by linarith
  set s : ℂ := ((1 + 1 / Real.log (z : ℝ) : ℝ) : ℂ) + (u : ℂ) * Complex.I with hs
  have hre : s.re = 1 + 1 / Real.log (z : ℝ) := by
    rw [hs, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
    ring
  have him : s.im = u := by
    rw [hs, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
    ring
  have hb : ‖riemannZeta s‖ ≤ 8 * Real.log |u| + 39 := by
    have hu0 : 0 < 1 / Real.log |u| := by
      have : 0 < Real.log |u| := Real.log_pos (by linarith)
      positivity
    have hz0 : 0 < 1 / Real.log (z : ℝ) := by positivity
    have := RHTower.norm_riemannZeta_le_log_near_one (s := s)
      (by rw [hre, him]; linarith) (by
        rw [hre]
        have : 1 / Real.log (z : ℝ) ≤ 1 := by
          rw [div_le_one hlogz0]
          exact hlogz
        linarith) (by rw [him]; exact hu)
    rwa [him] at this
  have h := GaloisForLFunctions.SignedSuccessorArithmetic.sum_cos_div_prime_le_of_zeta_upper hz hb
  rw [harmonicSystem_column]
  unfold poleConst
  linarith

/-- **A height at level `θ` is paid by the pole.** -/
theorem le_log_of_mem_largeValue {z : ℕ} (hz : 3 ≤ z) {u θ : ℝ} (hu : 8 ≤ |u|)
    (h : u ∈ (harmonicSystem z).largeValue θ) :
    θ * (harmonicSystem z).size ≤ Real.log (8 * Real.log |u| + 39) + poleConst :=
  h.trans (column_le_pole hz hu)

/-- **Non-alignment at the weights `1/p`.** Below the height where the pole permits the level, the orbit is outside the large-value set. -/
theorem not_mem_largeValue_of_lt {z : ℕ} (hz : 3 ≤ z) {θ T u : ℝ} (hu : 8 ≤ |u|) (huT : |u| ≤ T)
    (hlt : Real.log (8 * Real.log T + 39) + poleConst < θ * (harmonicSystem z).size) :
    u ∉ (harmonicSystem z).largeValue θ := by
  intro h
  have h1 := le_log_of_mem_largeValue hz hu h
  have hu0 : 0 < |u| := by linarith
  have h2 : Real.log (8 * Real.log |u| + 39) ≤ Real.log (8 * Real.log T + 39) := by
    have hlog : Real.log |u| ≤ Real.log T := Real.log_le_log hu0 huT
    have hlog0 : 0 ≤ Real.log |u| := Real.log_nonneg (by linarith)
    exact Real.log_le_log (by positivity) (by linarith)
  linarith

/-- The size tends to infinity with the length. -/
theorem tendsto_harmonicSystem_size :
    Tendsto (fun z : ℕ => (harmonicSystem z).size) atTop atTop := by
  have h1 : Tendsto (fun z : ℕ => Real.log (Real.log ((z : ℝ) + 1)) - 1) atTop atTop := by
    have h2 : Tendsto (fun z : ℕ => (z : ℝ) + 1) atTop atTop :=
      tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
    exact tendsto_atTop_add_const_right _ _ (Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp h2))
  refine tendsto_atTop_mono' _ ?_ h1
  filter_upwards [eventually_ge_atTop 1] with z hz
  exact harmonicSystem_size_ge hz

/-- **Returns escape with the length.** On a fixed range of heights the orbit leaves every positive level once `z` is large. -/
theorem eventually_not_mem_largeValue {θ T : ℝ} (hθ : 0 < θ) :
    ∀ᶠ z : ℕ in atTop, ∀ u, 8 ≤ |u| → |u| ≤ T → u ∉ (harmonicSystem z).largeValue θ := by
  have hsize := (tendsto_harmonicSystem_size.const_mul_atTop hθ).eventually_gt_atTop
    (Real.log (8 * Real.log T + 39) + poleConst)
  filter_upwards [hsize, eventually_ge_atTop 3] with z h1 hz u hu huT
  exact not_mem_largeValue_of_lt hz hu huT h1

/-- **Two large values differ by a return the pole must pay for.** -/
theorem pair_level_le {z : ℕ} (hz : 3 ≤ z) {θ t t' : ℝ} (hθ : 0 ≤ θ) (hS : 0 < (harmonicSystem z).size)
    (hne : t ≠ t') (hgap : 8 ≤ |t - t'|) (ht : t ∈ (harmonicSystem z).largeValue θ)
    (ht' : t' ∈ (harmonicSystem z).largeValue θ) :
    (2 * θ ^ 2 - 1) * (harmonicSystem z).size ≤ Real.log (8 * Real.log |t - t'| + 39) + poleConst := by
  classical
  have hcard : ({t, t'} : Finset ℝ).card = 2 := Finset.card_pair hne
  obtain ⟨a, ha, b, hb, hab, hle⟩ := (harmonicSystem z).exists_pair_column_ge (A := {t, t'}) hθ hS
    (by rw [hcard]) (by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact ht
      · rw [Finset.mem_singleton.mp hx]
        exact ht')
  rw [hcard] at hle
  have e : θ ^ 2 - (1 - θ ^ 2) / (((2 : ℕ) : ℝ) - 1) = 2 * θ ^ 2 - 1 := by
    push_cast
    norm_num
    ring
  rw [e] at hle
  -- The pair is `t, t'` in some order, and the column is even.
  have hcol : (harmonicSystem z).column (a - b) = (harmonicSystem z).column (t - t') := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact absurd rfl hab
    · rfl
    · rw [← neg_sub, (harmonicSystem z).column_neg]
    · exact absurd rfl hab
  rw [hcol] at hle
  exact hle.trans (column_le_pole hz hgap)

/-- **Large values are counted through the pole.** If the level `θ² − (1 − θ²)/(m − 1)` is not yet permitted by the pole at height `L/J`, a family of heights at level `θ` in a window of length `L`, pairwise more than `8` apart, has at most `J(m − 1)` members. -/
theorem card_le_of_pole {z : ℕ} (hz : 3 ≤ z) {A : Finset ℝ} {θ T L : ℝ} {J m : ℕ} (hθ0 : 0 ≤ θ)
    (hθ1 : θ ≤ 1) (hS : 0 < (harmonicSystem z).size) (hL : 0 < L) (hJ : 0 < J) (hm : 2 ≤ m)
    (hAI : ∀ t ∈ A, t ∈ Set.Icc T (T + L)) (hA : ∀ t ∈ A, t ∈ (harmonicSystem z).largeValue θ)
    (hsep : ∀ t ∈ A, ∀ u ∈ A, t ≠ u → 8 < |t - u|)
    (hlt : Real.log (8 * Real.log (L / J) + 39) + poleConst <
      (θ ^ 2 - (1 - θ ^ 2) / ((m : ℝ) - 1)) * (harmonicSystem z).size) :
    A.card ≤ J * (m - 1) := by
  refine (harmonicSystem z).card_le_of_no_low_return hθ0 hθ1 hS hL hJ hm hAI hA hsep ?_
  intro v hv hvL
  by_contra hcon
  have hmem : v ∈ (harmonicSystem z).largeValue (θ ^ 2 - (1 - θ ^ 2) / ((m : ℝ) - 1)) := not_lt.mp hcon
  exact not_mem_largeValue_of_lt hz hv.le hvL hlt hmem

end

end GaloisForLFunctions.PrimeTorusTheory
