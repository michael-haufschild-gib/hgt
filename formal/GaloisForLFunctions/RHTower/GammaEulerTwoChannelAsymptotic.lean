import Mathlib
import GaloisForLFunctions.RHTower.GammaEulerAsymptoticTransport

/-!
# Two-channel asymptotic transport of the Gamma-Euler difference

Iterating the Gamma-Euler central difference on the Gamma height characteristic
`φ_r(u) = cosh(u/2)^{-r}` transports the first surviving tail coefficient through the *product* of
the two next-mode eigenvalues.  As `u → ∞`,
`exp((r/2+1)u)·(D_{r,h₁} D_{r,h₂} φ_r)(u) → gammaEulerTwoDifferenceNextCoefficient r h₁ h₂`
(`gammaEulerTwoDifference_asymptotic`, the `k = 2` case of equation (4)).  Because both next-mode
eigenvalues are strictly negative, the limit is strictly negative, so the two-channel difference is
eventually negative: `(D_{r,h₁} D_{r,h₂} φ_r)(u) < 0` for large `u`
(`gammaEulerTwoDifference_eventually_neg`) — the two-channel correlation-sign reversal.

## Mechanism: the profile operator

Writing `g(u) = 2^r exp(-ru/2) H(exp(-u))`, the difference `D_{r,h}` acts on the profile `H` by the
operator `gammaEulerProfileStep r h H`, a linear combination of `H` at the scaled arguments
`e·exp(∓h)`.  This profile operator always kills the value at `0`
(`gammaEulerProfileStep_zero`) and scales the derivative at `0` by the next-mode eigenvalue
`d_{r,h}(r/2+1)` (`gammaEulerProfileStep_hasDerivAt`).  Iterating over the two channels annihilates
the leading `exp(-ru/2)` mode and multiplies the next coefficient `-r·2^r` by the two eigenvalues;
the boundary slope `K(e)/e → K'(0)` extracts the exact limit.  The one-channel case is
`GammaEulerAsymptoticTransport.gammaEulerOneDifference_asymptotic`.
-/

open Real Filter Topology

namespace RHTower

/-- Profile operator induced by the Gamma-Euler difference: if `g(u) = 2^r exp(-ru/2) H(exp(-u))`,
then `D_{r,h} g(u) = 2^r exp(-ru/2)·(gammaEulerProfileStep r h H)(exp(-u))`.  It is the action of the
central difference on the profile `H` of the exponentially rescaled function. -/
noncomputable def gammaEulerProfileStep (r h : ℝ) (H : ℝ → ℝ) (e : ℝ) : ℝ :=
  2 * Real.cosh (r * h / 2) * H e
    - Real.exp (-(r * h / 2)) * H (e * Real.exp (-h))
    - Real.exp (r * h / 2) * H (e * Real.exp h)

/-- The Gamma-Euler difference acts on the exponentially rescaled profile by `gammaEulerProfileStep`. -/
theorem gammaEulerCentralDifference_profile (r h : ℝ) (H : ℝ → ℝ) (u : ℝ) :
    gammaEulerCentralDifference r h (fun u => 2 ^ r * Real.exp (-r * u / 2) * H (Real.exp (-u))) u
      = 2 ^ r * Real.exp (-r * u / 2) * gammaEulerProfileStep r h H (Real.exp (-u)) := by
  show 2 * Real.cosh (r * h / 2) * (2 ^ r * Real.exp (-r * u / 2) * H (Real.exp (-u)))
      - 2 ^ r * Real.exp (-r * (u + h) / 2) * H (Real.exp (-(u + h)))
      - 2 ^ r * Real.exp (-r * (u - h) / 2) * H (Real.exp (-(u - h))) = _
  rw [gammaEulerProfileStep,
    show Real.exp (-r * (u + h) / 2) = Real.exp (-r * u / 2) * Real.exp (-(r * h / 2)) by
      rw [← Real.exp_add]; congr 1; ring,
    show Real.exp (-r * (u - h) / 2) = Real.exp (-r * u / 2) * Real.exp (r * h / 2) by
      rw [← Real.exp_add]; congr 1; ring,
    show Real.exp (-(u + h)) = Real.exp (-u) * Real.exp (-h) by rw [← Real.exp_add]; congr 1; ring,
    show Real.exp (-(u - h)) = Real.exp (-u) * Real.exp h by rw [← Real.exp_add]; congr 1; ring]
  ring

/-- The profile operator annihilates the value at `0`: `gammaEulerProfileStep r h H 0 = 0` for every
`H`.  This is exactly the killing of the leading `exp(-ru/2)` tail mode. -/
theorem gammaEulerProfileStep_zero (r h : ℝ) (H : ℝ → ℝ) :
    gammaEulerProfileStep r h H 0 = 0 := by
  rw [gammaEulerProfileStep, Real.cosh_eq]; simp only [zero_mul]; ring

/-- The profile operator scales the derivative at `0` by the next-mode eigenvalue
`d_{r,h}(r/2+1)`: if `HasDerivAt H c 0` then
`HasDerivAt (gammaEulerProfileStep r h H) (d_{r,h}(r/2+1)·c) 0`. -/
theorem gammaEulerProfileStep_hasDerivAt {r h : ℝ} {H : ℝ → ℝ} {c : ℝ} (hH : HasDerivAt H c 0) :
    HasDerivAt (gammaEulerProfileStep r h H)
      (gammaEulerCentralDifferenceEigenvalue r h (r / 2 + 1) * c) 0 := by
  have hd1 : HasDerivAt (fun e => H (e * Real.exp (-h))) (c * Real.exp (-h)) 0 := by
    have hlin : HasDerivAt (fun e : ℝ => e * Real.exp (-h)) (Real.exp (-h)) 0 := by
      simpa using (hasDerivAt_id (0:ℝ)).mul_const (Real.exp (-h))
    have hH0 : HasDerivAt H c ((fun e : ℝ => e * Real.exp (-h)) 0) := by simpa using hH
    simpa using! hH0.comp 0 hlin
  have hd2 : HasDerivAt (fun e => H (e * Real.exp h)) (c * Real.exp h) 0 := by
    have hlin : HasDerivAt (fun e : ℝ => e * Real.exp h) (Real.exp h) 0 := by
      simpa using (hasDerivAt_id (0:ℝ)).mul_const (Real.exp h)
    have hH0 : HasDerivAt H c ((fun e : ℝ => e * Real.exp h) 0) := by simpa using hH
    simpa using! hH0.comp 0 hlin
  have hsum := ((hH.const_mul (2 * Real.cosh (r * h / 2))).sub
    (hd1.const_mul (Real.exp (-(r * h / 2))))).sub (hd2.const_mul (Real.exp (r * h / 2)))
  convert! hsum using 1
  rw [gammaEulerCentralDifferenceEigenvalue,
    show Real.cosh ((r / 2 + 1) * h)
      = (Real.exp ((r / 2 + 1) * h) + Real.exp (-((r / 2 + 1) * h))) / 2 from Real.cosh_eq _]
  have e1 : Real.exp (-(r * h / 2)) * Real.exp (-h) = Real.exp (-((r / 2 + 1) * h)) := by
    rw [← Real.exp_add]; congr 1; ring
  have e2 : Real.exp (r * h / 2) * Real.exp h = Real.exp ((r / 2 + 1) * h) := by
    rw [← Real.exp_add]; congr 1; ring
  linear_combination (c) * e1 + (c) * e2

/-- **Two-channel asymptotic transport (equation (4), `k = 2`).**  Iterating the Gamma-Euler
difference on the Gamma characteristic `φ_r(u) = cosh(u/2)^{-r}` transports the first surviving tail
coefficient through the product of the two next-mode eigenvalues:
`exp((r/2+1)u)·(D_{r,h₁} D_{r,h₂} φ_r)(u) → gammaEulerTwoDifferenceNextCoefficient r h₁ h₂`. -/
theorem gammaEulerTwoDifference_asymptotic (r h₁ h₂ : ℝ) :
    Tendsto (fun u => Real.exp ((r / 2 + 1) * u) *
        gammaEulerCentralDifference r h₁
          (gammaEulerCentralDifference r h₂ (fun u => (Real.cosh (u / 2)) ^ (-r))) u)
      atTop (𝓝 (gammaEulerTwoDifferenceNextCoefficient r h₁ h₂)) := by
  set eig₁ := gammaEulerCentralDifferenceEigenvalue r h₁ (r / 2 + 1) with heig₁
  set eig₂ := gammaEulerCentralDifferenceEigenvalue r h₂ (r / 2 + 1) with heig₂
  set H₀ : ℝ → ℝ := fun e => (1 + e) ^ (-r) with hH₀
  set H₁ : ℝ → ℝ := gammaEulerProfileStep r h₂ H₀ with hH₁
  set K : ℝ → ℝ := gammaEulerProfileStep r h₁ H₁ with hK
  have hφ : (fun u => (Real.cosh (u / 2)) ^ (-r))
      = fun u => 2 ^ r * Real.exp (-r * u / 2) * H₀ (Real.exp (-u)) := by
    funext u; rw [hH₀]; exact cosh_half_rpow_factor r u
  have hB : gammaEulerCentralDifference r h₂ (fun u => (Real.cosh (u / 2)) ^ (-r))
      = fun u => 2 ^ r * Real.exp (-r * u / 2) * H₁ (Real.exp (-u)) := by
    funext u; rw [hφ, hH₁]; exact gammaEulerCentralDifference_profile r h₂ H₀ u
  have hident : ∀ u, gammaEulerCentralDifference r h₁
        (gammaEulerCentralDifference r h₂ (fun u => (Real.cosh (u / 2)) ^ (-r))) u
      = 2 ^ r * Real.exp (-r * u / 2) * K (Real.exp (-u)) := by
    intro u; rw [hB, hK]; exact gammaEulerCentralDifference_profile r h₁ H₁ u
  have hK0 : K 0 = 0 := by rw [hK]; exact gammaEulerProfileStep_zero r h₁ H₁
  have hH₀' : HasDerivAt H₀ (-r) 0 := by
    rw [hH₀]
    have hlin : HasDerivAt (fun e : ℝ => 1 + e) 1 0 := by
      simpa using (hasDerivAt_id (0:ℝ)).const_add 1
    have := (Real.hasDerivAt_rpow_const (p := -r) (Or.inl (by norm_num : (1:ℝ) + (0:ℝ) ≠ 0))).comp 0 hlin
    simpa using! this
  have hH₁' : HasDerivAt H₁ (eig₂ * (-r)) 0 := by
    rw [hH₁, heig₂]; exact gammaEulerProfileStep_hasDerivAt hH₀'
  have hK' : HasDerivAt K (eig₁ * (eig₂ * (-r))) 0 := by
    rw [hK, heig₁]; exact gammaEulerProfileStep_hasDerivAt hH₁'
  have hslope : Tendsto (fun e => K e / e) (𝓝[≠] 0) (𝓝 (eig₁ * (eig₂ * (-r)))) := by
    have hs := hasDerivAt_iff_tendsto_slope.mp hK'
    refine hs.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with e he
    rw [slope_def_field, hK0, sub_zero, sub_zero]
  have hexp : Tendsto (fun u : ℝ => Real.exp (-u)) atTop (𝓝[≠] 0) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · exact Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot
    · filter_upwards with u; exact (Real.exp_pos _).ne'
  have hcomp : Tendsto (fun u => K (Real.exp (-u)) / Real.exp (-u)) atTop
      (𝓝 (eig₁ * (eig₂ * (-r)))) := hslope.comp hexp
  have hcoeff : gammaEulerTwoDifferenceNextCoefficient r h₁ h₂ = 2 ^ r * (eig₁ * (eig₂ * (-r))) := by
    rw [gammaEulerTwoDifferenceNextCoefficient, gammaEulerTailScale, heig₁, heig₂,
      show Real.exp (r * Real.log 2) = (2:ℝ) ^ r by rw [Real.rpow_def_of_pos (by norm_num)]; ring_nf]
    ring
  rw [hcoeff]
  refine (hcomp.const_mul (2 ^ r)).congr (fun u => ?_)
  rw [hident u, show Real.exp (-u) = (Real.exp u)⁻¹ from by rw [← Real.exp_neg]]
  rw [show Real.exp ((r / 2 + 1) * u) * (2 ^ r * Real.exp (-r * u / 2) * K (Real.exp u)⁻¹)
      = 2 ^ r * (Real.exp ((r / 2 + 1) * u) * Real.exp (-r * u / 2)) * K (Real.exp u)⁻¹ by ring,
    ← Real.exp_add, show (r / 2 + 1) * u + -r * u / 2 = u by ring]
  field_simp

/-- **Two-channel correlation sign reversal (continuous tail form).**  For `r,h₁,h₂ > 0`, two
Gamma-Euler differences of the Gamma characteristic `φ_r(u) = cosh(u/2)^{-r}` are eventually strictly
negative: `(D_{r,h₁} D_{r,h₂} φ_r)(u) < 0` for all large `u`.  This is the card's headline no-go: an
even number of Euler channels reverses the correlation sign, so no ascending prime-by-prime argument
can keep every normalized Euler factor a contraction. -/
theorem gammaEulerTwoDifference_eventually_neg {r h₁ h₂ : ℝ} (hr : 0 < r) (hh₁ : 0 < h₁)
    (hh₂ : 0 < h₂) :
    ∀ᶠ u in atTop, gammaEulerCentralDifference r h₁
        (gammaEulerCentralDifference r h₂ (fun u => (Real.cosh (u / 2)) ^ (-r))) u < 0 := by
  have hC : gammaEulerTwoDifferenceNextCoefficient r h₁ h₂ < 0 :=
    gammaEulerTwoDifferenceNextCoefficient_neg hr hh₁ hh₂
  have hev := (gammaEulerTwoDifference_asymptotic r h₁ h₂).eventually (Iio_mem_nhds hC)
  filter_upwards [hev] with u hu
  have hpos : (0:ℝ) < Real.exp ((r / 2 + 1) * u) := Real.exp_pos _
  have hu' : Real.exp ((r / 2 + 1) * u) *
      gammaEulerCentralDifference r h₁
        (gammaEulerCentralDifference r h₂ (fun u => (Real.cosh (u / 2)) ^ (-r))) u < 0 :=
    Set.mem_Iio.mp hu
  nlinarith [hu', hpos]

end RHTower

namespace RHTower

/-- Iterated Gamma-Euler difference over a finite list of scales: `D_{r,h₁} ⋯ D_{r,h_k}` applied to
`f`, folded from the right (the head scale is the outermost difference). -/
noncomputable def gammaEulerDifferenceList (r : ℝ) (L : List ℝ) (f : ℝ → ℝ) : ℝ → ℝ :=
  L.foldr (fun h g => gammaEulerCentralDifference r h g) f

/-- Iterated profile operator over a finite list of scales, folded from the right; the profile
counterpart of `gammaEulerDifferenceList` under the substitution `g(u) = 2^r exp(-ru/2) H(exp(-u))`. -/
noncomputable def gammaEulerProfileList (r : ℝ) (L : List ℝ) (H : ℝ → ℝ) : ℝ → ℝ :=
  L.foldr (fun h H' => gammaEulerProfileStep r h H') H

/-- The iterated difference acts on the exponentially rescaled profile by the iterated profile
operator: `(D_{r,L}) (2^r exp(-r·/2) H(exp(-·))) = 2^r exp(-r·/2)·(gammaEulerProfileList r L H)(exp(-·))`. -/
theorem gammaEulerDifferenceList_profile (r : ℝ) (L : List ℝ) (H : ℝ → ℝ) :
    gammaEulerDifferenceList r L (fun u => 2 ^ r * Real.exp (-r * u / 2) * H (Real.exp (-u)))
      = fun u => 2 ^ r * Real.exp (-r * u / 2) * gammaEulerProfileList r L H (Real.exp (-u)) := by
  induction L with
  | nil => rfl
  | cons h t ih =>
    show gammaEulerCentralDifference r h
      (gammaEulerDifferenceList r t (fun u => 2 ^ r * Real.exp (-r * u / 2) * H (Real.exp (-u)))) = _
    rw [ih]; funext u
    exact gammaEulerCentralDifference_profile r h (gammaEulerProfileList r t H) u

/-- A nonempty iterated profile operator annihilates the value at `0`: the leading `exp(-ru/2)` tail
mode is killed by the outermost difference. -/
theorem gammaEulerProfileList_zero (r : ℝ) {L : List ℝ} (hL : L ≠ []) (H : ℝ → ℝ) :
    gammaEulerProfileList r L H 0 = 0 := by
  obtain ⟨h, t, rfl⟩ := List.exists_cons_of_ne_nil hL
  exact gammaEulerProfileStep_zero r h (gammaEulerProfileList r t H)

/-- The iterated profile operator scales the derivative at `0` by the product of the next-mode
eigenvalues over the list: `HasDerivAt H c 0` gives
`HasDerivAt (gammaEulerProfileList r L H) ((∏_{h∈L} d_{r,h}(r/2+1))·c) 0`. -/
theorem gammaEulerProfileList_hasDerivAt (r : ℝ) (L : List ℝ) {H : ℝ → ℝ} {c : ℝ}
    (hH : HasDerivAt H c 0) :
    HasDerivAt (gammaEulerProfileList r L H)
      ((L.map (fun h => gammaEulerCentralDifferenceEigenvalue r h (r / 2 + 1))).prod * c) 0 := by
  induction L with
  | nil => simpa using! hH
  | cons h t ih =>
    have key := gammaEulerProfileStep_hasDerivAt (r := r) (h := h) ih
    rw [List.map_cons, List.prod_cons, mul_assoc]
    exact key

/-- **General finite-block asymptotic transport (equation (4)).**  For a nonempty finite list `L`
of scales, iterating the Gamma-Euler difference on the Gamma characteristic `φ_r(u) = cosh(u/2)^{-r}`
transports the first surviving tail coefficient through the product of the next-mode eigenvalues:
`exp((r/2+1)u)·(D_{r,h₁} ⋯ D_{r,h_k} φ_r)(u) → -r·2^r·∏_{h∈L} d_{r,h}(r/2+1)`.  This is equation (4)
for an arbitrary finite block; the product mirrors `gammaEulerManyDifferenceNextCoefficient`. -/
theorem gammaEulerDifferenceList_asymptotic (r : ℝ) {L : List ℝ} (hL : L ≠ []) :
    Tendsto (fun u => Real.exp ((r / 2 + 1) * u) *
        gammaEulerDifferenceList r L (fun u => (Real.cosh (u / 2)) ^ (-r)) u)
      atTop (𝓝 (-r * gammaEulerTailScale r *
        (L.map (fun h => gammaEulerCentralDifferenceEigenvalue r h (r / 2 + 1))).prod)) := by
  set P := (L.map (fun h => gammaEulerCentralDifferenceEigenvalue r h (r / 2 + 1))).prod with hP
  set H₀ : ℝ → ℝ := fun e => (1 + e) ^ (-r) with hH₀
  set K : ℝ → ℝ := gammaEulerProfileList r L H₀ with hK
  have hφ : (fun u => (Real.cosh (u / 2)) ^ (-r))
      = fun u => 2 ^ r * Real.exp (-r * u / 2) * H₀ (Real.exp (-u)) := by
    funext u; rw [hH₀]; exact cosh_half_rpow_factor r u
  have hlist : gammaEulerDifferenceList r L (fun u => (Real.cosh (u / 2)) ^ (-r))
      = fun u => 2 ^ r * Real.exp (-r * u / 2) * K (Real.exp (-u)) := by
    rw [hφ, hK]; exact gammaEulerDifferenceList_profile r L H₀
  have hK0 : K 0 = 0 := by rw [hK]; exact gammaEulerProfileList_zero r hL H₀
  have hH₀' : HasDerivAt H₀ (-r) 0 := by
    rw [hH₀]
    have hlin : HasDerivAt (fun e : ℝ => 1 + e) 1 0 := by
      simpa using (hasDerivAt_id (0:ℝ)).const_add 1
    have := (Real.hasDerivAt_rpow_const (p := -r) (Or.inl (by norm_num : (1:ℝ) + (0:ℝ) ≠ 0))).comp 0 hlin
    simpa using! this
  have hK' : HasDerivAt K (P * (-r)) 0 := by
    rw [hK, hP]; exact gammaEulerProfileList_hasDerivAt r L hH₀'
  have hslope : Tendsto (fun e => K e / e) (𝓝[≠] 0) (𝓝 (P * (-r))) := by
    have hs := hasDerivAt_iff_tendsto_slope.mp hK'
    refine hs.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with e he
    rw [slope_def_field, hK0, sub_zero, sub_zero]
  have hexp : Tendsto (fun u : ℝ => Real.exp (-u)) atTop (𝓝[≠] 0) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · exact Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot
    · filter_upwards with u; exact (Real.exp_pos _).ne'
  have hcomp : Tendsto (fun u => K (Real.exp (-u)) / Real.exp (-u)) atTop (𝓝 (P * (-r))) :=
    hslope.comp hexp
  have hcoeff : -r * gammaEulerTailScale r * P = 2 ^ r * (P * (-r)) := by
    rw [gammaEulerTailScale,
      show Real.exp (r * Real.log 2) = (2:ℝ) ^ r by rw [Real.rpow_def_of_pos (by norm_num)]; ring_nf]
    ring
  rw [hcoeff]
  refine (hcomp.const_mul (2 ^ r)).congr (fun u => ?_)
  rw [show gammaEulerDifferenceList r L (fun u => (Real.cosh (u / 2)) ^ (-r)) u
      = 2 ^ r * Real.exp (-r * u / 2) * K (Real.exp (-u)) from congrFun hlist u,
    show Real.exp (-u) = (Real.exp u)⁻¹ from by rw [← Real.exp_neg]]
  rw [show Real.exp ((r / 2 + 1) * u) * (2 ^ r * Real.exp (-r * u / 2) * K (Real.exp u)⁻¹)
      = 2 ^ r * (Real.exp ((r / 2 + 1) * u) * Real.exp (-r * u / 2)) * K (Real.exp u)⁻¹ by ring,
    ← Real.exp_add, show (r / 2 + 1) * u + -r * u / 2 = u by ring]
  field_simp

/-- Sign of the next-mode eigenvalue product over a list of positive scales: the product is positive
for an even-length list and negative for an odd-length list (each factor `d_{r,h}(r/2+1)` is
strictly negative for `r,h > 0`). -/
theorem gammaEulerEigenvalueList_prod_sign {r : ℝ} (hr : 0 < r) {L : List ℝ}
    (hpos : ∀ h ∈ L, 0 < h) :
    (Even L.length →
        0 < (L.map (fun h => gammaEulerCentralDifferenceEigenvalue r h (r / 2 + 1))).prod)
    ∧ (Odd L.length →
        (L.map (fun h => gammaEulerCentralDifferenceEigenvalue r h (r / 2 + 1))).prod < 0) := by
  induction L with
  | nil => exact ⟨fun _ => by simp, fun h => absurd h (by decide)⟩
  | cons a t ih =>
    have ha : 0 < a := hpos a List.mem_cons_self
    have haneg : gammaEulerCentralDifferenceEigenvalue r a (r / 2 + 1) < 0 :=
      gammaEulerCentralDifferenceEigenvalue_next_neg hr ha
    have ht : ∀ h ∈ t, 0 < h := fun h hh => hpos h (List.mem_cons_of_mem a hh)
    obtain ⟨ihe, iho⟩ := ih ht
    simp only [List.map_cons, List.prod_cons, List.length_cons]
    refine ⟨fun heven => ?_, fun hodd => ?_⟩
    · have hodd_t : Odd t.length := Nat.not_even_iff_odd.mp (Nat.even_add_one.mp heven)
      exact mul_pos_of_neg_of_neg haneg (iho hodd_t)
    · have heven_t : Even t.length := Nat.not_odd_iff_even.mp (Nat.odd_add_one.mp hodd)
      exact mul_neg_of_neg_of_pos haneg (ihe heven_t)

/-- **Even-block correlation sign reversal (general continuous no-go).**  For `r > 0`, a nonempty
even-length list `L` of positive scales makes the iterated Gamma-Euler difference of the Gamma
characteristic `φ_r(u) = cosh(u/2)^{-r}` eventually strictly negative:
`(D_{r,h₁} ⋯ D_{r,h_{2m}} φ_r)(u) < 0` for all large `u`.  Any even number of Euler channels reverses
the correlation-sign tail, generalizing the two-channel case. -/
theorem gammaEulerDifferenceList_eventually_neg {r : ℝ} (hr : 0 < r) {L : List ℝ}
    (hpos : ∀ h ∈ L, 0 < h) (hL : L ≠ []) (hlen : Even L.length) :
    ∀ᶠ u in atTop,
      gammaEulerDifferenceList r L (fun u => (Real.cosh (u / 2)) ^ (-r)) u < 0 := by
  have hPpos : 0 < (L.map (fun h => gammaEulerCentralDifferenceEigenvalue r h (r / 2 + 1))).prod :=
    (gammaEulerEigenvalueList_prod_sign hr hpos).1 hlen
  have hCneg : -r * gammaEulerTailScale r *
      (L.map (fun h => gammaEulerCentralDifferenceEigenvalue r h (r / 2 + 1))).prod < 0 := by
    have h1 : -r * gammaEulerTailScale r < 0 :=
      mul_neg_of_neg_of_pos (by linarith) (gammaEulerTailScale_pos r)
    exact mul_neg_of_neg_of_pos h1 hPpos
  have hev := (gammaEulerDifferenceList_asymptotic r hL).eventually (Iio_mem_nhds hCneg)
  filter_upwards [hev] with u hu
  have hposu : (0:ℝ) < Real.exp ((r / 2 + 1) * u) := Real.exp_pos _
  have hu' : Real.exp ((r / 2 + 1) * u) *
      gammaEulerDifferenceList r L (fun u => (Real.cosh (u / 2)) ^ (-r)) u < 0 := Set.mem_Iio.mp hu
  nlinarith [hu', hposu]

end RHTower
