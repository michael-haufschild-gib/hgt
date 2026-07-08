/-
# The finite completed weld is tower-free: RH_{2^k} is carried by no finite piece of ξ's Euler–Γ product

`EulerTruncationRigidity` shows the finite multiplicative truncation `eulerPartial P` carries an
unconditional single-valued `2^k`-th root on `Re s > 0` (the σ_p-side Kummer tower is free).
`PrimeDivisorAtomsNoGo` shows the archimedean factor `π^(−s/2)·Γ(s/2)` — the `∂_s` side — is a
nonvanishing unit there, and so is the finite completed local factor `archimedeanFactor · eulerPartial P`
(the `∂_s × {σ_p}` weld in finite form).  Neither file states the *tower* on the archimedean side or on
the weld.  This file supplies it, and thereby localizes the RH_{2^k} obstruction.

On the convex — hence simply connected — right half-plane, a nonvanishing analytic function has a
single-valued analytic `2^k`-th root (`Bottcher.exists_differentiableOn_pow_eq`).  Applied to the two
zero-free units:

* `archimedeanFactor_pow_root` — the archimedean generator has an unconditional free `2^k`-th root
  tower on `Re s > 0`.  The `∂_s` side is tower-free, exactly as the `{σ_p}` side.
* `completedLocalFactor_pow_root` — **the finite completed weld `archimedeanFactor · eulerPartial P`
  has an unconditional free `2^k`-th root tower on `Re s > 0`** — through the wall `Re s = 1` and across
  the whole critical strip, with no divisibility condition on anything.
* `completed_weld_tower_free_but_xi_tower_costs` — the sharpened dichotomy: the finite completed weld's
  tower is free unconditionally, while ξ's `2^k`-th root on the smaller half-plane `Re s > 1/2` exists
  only when every strip zero's hole-order is divisible by `2^k` (`= RHLadder k`).

So the RH_{2^k} monodromy obstruction is carried by **no finite piece** of the completed Euler–Γ
product — not the archimedean generator, not any finite prime layer, not their weld: every finite
completed local factor is a `2^k`-th power everywhere on `Re s > 0`.  The obstruction is purely
emergent, appearing only in the `P → ∞` completed limit `ξ`, at the strip zeros that exist at no finite
level.  The link between the free finite weld and ξ's conditional tower is the limit flow (analytic
continuation across the wall), never a pinned finite constraint.
-/
import GaloisForLFunctions.RHTower.PrimeDivisorAtomsNoGo
import GaloisForLFunctions.RHTower.KummerObstruction
import GaloisForLFunctions.RHTower.CoherentTower
import GaloisForLFunctions.Bottcher.HolomorphicBranch

open Complex
open scoped BigOperators

namespace RHTower

noncomputable section

/-! ### The right half-plane is simply connected -/

/-- The full right half-plane `Re s > 0` is convex. -/
theorem convex_rightHalfPlane : Convex ℝ rightHalfPlane := convex_halfSpace_re_gt 0

/-- The full right half-plane is simply connected (convex and nonempty). -/
theorem isSimplyConnected_rightHalfPlane : IsSimplyConnected rightHalfPlane :=
  isSimplyConnected_of_convex convex_rightHalfPlane ⟨1, show (0 : ℝ) < (1 : ℂ).re by norm_num⟩

/-! ### Free `2^k`-th root tower for any zero-free analytic unit on `Re s > 0` -/

/-- **Free tower from nonvanishing.**  Any function analytic and nonvanishing on the (simply connected)
right half-plane has a single-valued analytic `2^k`-th root there, for every `k`. -/
theorem exists_pow_root_of_analyticOn_nonvanishing (k : ℕ) {f : ℂ → ℂ}
    (hf : ∀ z ∈ rightHalfPlane, AnalyticAt ℂ f z) (hne : ∀ z ∈ rightHalfPlane, f z ≠ 0) :
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g rightHalfPlane ∧
      ∀ z ∈ rightHalfPlane, g z ^ (2 ^ k) = f z := by
  have hdiff : DifferentiableOn ℂ f rightHalfPlane := fun z hz => (hf z hz).differentiableWithinAt
  have h0 : (0 : ℂ) ∉ f '' rightHalfPlane := by rintro ⟨z, hz, hzeq⟩; exact hne z hz hzeq
  exact Bottcher.exists_differentiableOn_pow_eq isSimplyConnected_rightHalfPlane
    isOpen_rightHalfPlane hdiff h0 (pow_ne_zero k two_ne_zero)

/-! ### The archimedean side and the completed weld are tower-free -/

/-- **The archimedean generator is tower-free.**  `π^(−s/2)·Γ(s/2)` has an unconditional single-valued
analytic `2^k`-th root on `Re s > 0`: the `∂_s` side carries a free Kummer tower, exactly as the
`{σ_p}` side. -/
theorem archimedeanFactor_pow_root (k : ℕ) :
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g rightHalfPlane ∧
      ∀ z ∈ rightHalfPlane, g z ^ (2 ^ k) = archimedeanFactor z :=
  exists_pow_root_of_analyticOn_nonvanishing k
    (fun _ hz => archimedeanFactor_analyticAt hz) (fun _ hz => archimedeanFactor_ne_zero hz)

/-- **The finite completed weld is tower-free.**  The finite completed local factor
`archimedeanFactor · eulerPartial P` — the `∂_s × {σ_p}` weld in finite form — has an unconditional
single-valued analytic `2^k`-th root on the whole right half-plane, through the wall `Re s = 1` and
across the critical strip, with no divisibility condition. -/
theorem completedLocalFactor_pow_root (k : ℕ) {P : Finset ℕ} (hP : ∀ p ∈ P, 2 ≤ p) :
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g rightHalfPlane ∧
      ∀ z ∈ rightHalfPlane, g z ^ (2 ^ k) = (archimedeanFactor * eulerPartial P) z :=
  exists_pow_root_of_analyticOn_nonvanishing k
    (fun _ hz => (archimedeanFactor_analyticAt hz).mul (eulerPartial_analyticAt hP hz))
    (fun _ hz => mul_ne_zero (archimedeanFactor_ne_zero hz) (eulerPartial_ne_zero hP hz))

/-- **The sharpened tower dichotomy at the weld.**  For every `k`:

* the finite completed weld `archimedeanFactor · eulerPartial P` has a single-valued `2^k`-th root on
  `Re s > 0` with **no condition** (the `∂_s × {σ_p}` weld is tower-free at every finite level);
* ξ has a single-valued `2^k`-th root on the smaller half-plane `Re s > 1/2` **only when** every strip
  zero's hole-order is divisible by `2^k` — which is exactly `RHLadder k`.

The RH_{2^k} obstruction is thus carried by no finite piece of the completed Euler–Γ product; it is
purely emergent in the `P → ∞` limit. -/
theorem completed_weld_tower_free_but_xi_tower_costs (k : ℕ) {P : Finset ℕ} (hP : ∀ p ∈ P, 2 ≤ p) :
    (∃ g : ℂ → ℂ, DifferentiableOn ℂ g rightHalfPlane ∧
        ∀ z ∈ rightHalfPlane, g z ^ (2 ^ k) = (archimedeanFactor * eulerPartial P) z)
    ∧ ((∀ ρ ∈ rightHalf, xi ρ = 0 → ∀ (r₀ R : ℝ) (N : ℕ) (zs : List ℂ) (u : ℂ → ℂ),
          EMSplitData ρ r₀ R N zs u → 2 ^ k ∣ zs.length) → RHLadder k) :=
  ⟨completedLocalFactor_pow_root k hP, rhLadder_of_em_split_multiplicity k⟩

end

end RHTower

namespace RHTower
noncomputable section

/-! ### Coherent infinite Kummer towers (the roots cohere across levels) -/

/-- **The archimedean generator admits a coherent infinite Kummer tower on `Re s > 0`.**  The free
`2^k`-th roots of every level cohere into a single `CoherentTower`: an unconditional infinite 2-adic
root tower for `π^(−s/2)Γ(s/2)`, discharging `coherentTower_of_exists_roots_all_two_powers_preconnected`
with the roots of `archimedeanFactor_pow_root`. -/
theorem archimedeanFactor_coherentTower :
    Nonempty (CoherentTower archimedeanFactor rightHalfPlane) :=
  coherentTower_of_exists_roots_all_two_powers_preconnected
    isOpen_rightHalfPlane isSimplyConnected_rightHalfPlane convex_rightHalfPlane.isPreconnected
    (show (1 : ℂ) ∈ rightHalfPlane from by show (0 : ℝ) < (1 : ℂ).re; norm_num)
    (fun z hz => archimedeanFactor_analyticAt hz)
    (archimedeanFactor_ne_zero (ρ := 1) (by norm_num))
    (fun k => by
      obtain ⟨g, hg, hgpow⟩ := archimedeanFactor_pow_root k
      exact ⟨g, hg.analyticOnNhd isOpen_rightHalfPlane, hgpow⟩)

/-- **The finite completed weld admits a coherent infinite Kummer tower on `Re s > 0`.**  The free
`2^k`-th roots of the completed local factor `archimedeanFactor · eulerPartial P` cohere into a single
`CoherentTower`: the `∂_s × {σ_p}` weld carries an unconditional infinite 2-adic root tower, while
ξ's coherent tower on `Re s > 1/2` is equivalent to RH.  The obstruction is the emergent difference. -/
theorem completedLocalFactor_coherentTower {P : Finset ℕ} (hP : ∀ p ∈ P, 2 ≤ p) :
    Nonempty (CoherentTower (archimedeanFactor * eulerPartial P) rightHalfPlane) :=
  coherentTower_of_exists_roots_all_two_powers_preconnected
    isOpen_rightHalfPlane isSimplyConnected_rightHalfPlane convex_rightHalfPlane.isPreconnected
    (show (1 : ℂ) ∈ rightHalfPlane from by show (0 : ℝ) < (1 : ℂ).re; norm_num)
    (fun z hz => (archimedeanFactor_analyticAt hz).mul (eulerPartial_analyticAt hP hz))
    (mul_ne_zero (archimedeanFactor_ne_zero (ρ := 1) (by norm_num))
      (eulerPartial_ne_zero hP (show (0 : ℝ) < (1 : ℂ).re by norm_num)))
    (fun k => by
      obtain ⟨g, hg, hgpow⟩ := completedLocalFactor_pow_root k hP
      exact ⟨g, hg.analyticOnNhd isOpen_rightHalfPlane, hgpow⟩)

end

end RHTower
