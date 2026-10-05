import GaloisForLFunctions.HTGeometry.RamificationSpectralFusion

/-!
# Kummer participation of a ramification power formation

The valuation residues `[v(n)]_r = (v_p(n) mod r)_p` take values in `K_r = ⊕_p ℤ/r`.  An integer
is an `r`-th power exactly when its residue vanishes, so on `A_{rm}` the inherited image is the
residue-`0` sector and the excess `X_{m,r}` is the union of the nontrivial sectors.  With the sector
masses `A_γ(σ) = Σ_{n ∈ A_{rm}, [v(n)]_r = γ} n^{-σ}`, the excess mass is `Σ_{γ ≠ 0} A_γ(σ) =
C_{m,r}(σ)`, and the coordinate sector projections `Π_γ` satisfy `‖Π_γ Ω_{rm,σ}‖² = A_γ/S_{rm}`.

**Theorem 8.1.**  With the Kummer–Parseval invariant `V = Σ_{γ ≠ 0} A_γ²`,
`Σ_{γ ≠ 0} ‖Π_γ Ω_{rm,σ}‖⁴ = V/S_{rm}(σ)²` and `Σ_{γ ≠ 0} (A_γ/C_{m,r})² = V/C_{m,r}²`: the
normalized
Kummer–Parseval energy is the collision probability of the excess-sector label.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal

noncomputable section

namespace GaloisForLFunctions.HTGeometry.FormationExcess

open _root_.RHTower _root_.HTGeometry.ConstraintFrameRelativity LpDiagonal

variable {m r : ℕ}

/-- The valuation residue `[v(n)]_r ∈ ⊕_p ℤ/r`. -/
def kummerVec (r n : ℕ) : ℕ →₀ ZMod r :=
  Finsupp.mapRange (fun e : ℕ => (e : ZMod r)) Nat.cast_zero n.factorization

/-- An integer is an `r`-th power exactly when its valuation residue vanishes. -/
theorem kummerVec_eq_zero_iff {N : ℕ} (hN : N ≠ 0) : kummerVec r N = 0 ↔ IsRPow r N := by
  rw [isRPow_iff_factorization_dvd hN, Finsupp.ext_iff]
  refine forall_congr' fun p => ?_
  simp only [kummerVec, Finsupp.mapRange_apply, Finsupp.coe_zero, Pi.zero_apply]
  exact ZMod.natCast_eq_zero_iff _ _

/-- On `A_{rm}` the excess is exactly the union of the nontrivial sectors. -/
theorem kummerVec_ne_zero_iff (N : EulerShell (r * m)) :
    kummerVec r (N : ℕ) ≠ 0 ↔ ¬ IsRPow r (N : ℕ) :=
  (kummerVec_eq_zero_iff (by have := N.2.1; omega)).not

/-- The sector mass `A_γ(σ) = Σ_{n ∈ A_{rm}, [v(n)]_r = γ} n^{-σ}`. -/
def sectorMass (m r : ℕ) (σ : ℝ) (γ : ℕ →₀ ZMod r) : ℝ :=
  ∑' N : EulerShell (r * m), if kummerVec r (N : ℕ) = γ then ((N : ℕ) : ℝ) ^ (-σ) else 0

/-- The Kummer–Parseval invariant `V = Σ_{γ ≠ 0} A_γ²`. -/
def kummerParseval (m r : ℕ) (σ : ℝ) : ℝ :=
  ∑' γ : {γ : ℕ →₀ ZMod r // γ ≠ 0}, sectorMass m r σ γ ^ 2

theorem summable_sector (m r : ℕ) {σ : ℝ} (hσ : 1 < σ) (γ : ℕ →₀ ZMod r) :
    Summable fun N : EulerShell (r * m) =>
      if kummerVec r (N : ℕ) = γ then ((N : ℕ) : ℝ) ^ (-σ) else 0 :=
  Summable.of_nonneg_of_le (fun N => by split_ifs <;> positivity)
    (fun N => by split_ifs <;> [exact le_rfl; positivity]) (summable_shell (r * m) hσ)

/-- **The nontrivial sectors carry the excess mass**: `Σ_{γ ≠ 0} A_γ(σ) = C_{m,r}(σ)`. -/
theorem tsum_sectorMass_ne_zero (m r : ℕ) {σ : ℝ} (hσ : 1 < σ) :
    ∑' γ : {γ : ℕ →₀ ZMod r // γ ≠ 0}, sectorMass m r σ γ = excessSum m r σ := by
  set F : EulerShell (r * m) → {γ : ℕ →₀ ZMod r // γ ≠ 0} → ℝ := fun N γ =>
    if kummerVec r (N : ℕ) = γ.1 then ((N : ℕ) : ℝ) ^ (-σ) else 0
  have hinner : ∀ N, HasSum (F N) (if kummerVec r (N : ℕ) ≠ 0 then ((N : ℕ) : ℝ) ^ (-σ) else 0) :=
    fun N => by
      by_cases hN : kummerVec r (N : ℕ) = 0
      · rw [if_neg (not_not.2 hN)]
        have h0 : F N = fun _ => 0 := funext fun γ =>
          if_neg fun (h : kummerVec r (N : ℕ) = γ.1) => γ.2 (h ▸ hN)
        rw [h0]
        exact hasSum_zero
      · rw [if_pos hN]
        have h1 : F N = fun γ => if γ = ⟨kummerVec r (N : ℕ), hN⟩ then ((N : ℕ) : ℝ) ^ (-σ)
            else 0 := funext fun γ => by
          by_cases h : γ = ⟨kummerVec r (N : ℕ), hN⟩
          · rw [if_pos h, h]
            dsimp only [F]
            rw [if_pos rfl]
          · rw [if_neg h]
            exact if_neg fun h' => h (Subtype.ext h'.symm)
        rw [h1]
        exact hasSum_ite_eq _ _
  have hnn : 0 ≤ Function.uncurry F := fun p => by
    simp only [Function.uncurry, F]
    split_ifs <;> positivity
  have hsumN : Summable fun N : EulerShell (r * m) =>
      if kummerVec r (N : ℕ) ≠ 0 then ((N : ℕ) : ℝ) ^ (-σ) else 0 :=
    Summable.of_nonneg_of_le (fun N => by split_ifs <;> positivity)
      (fun N => by split_ifs <;> [exact le_rfl; positivity]) (summable_shell (r * m) hσ)
  have hU : Summable (Function.uncurry F) :=
    (summable_prod_of_nonneg hnn).2 ⟨fun N => (hinner N).summable,
      hsumN.congr fun N => (hinner N).tsum_eq.symm⟩
  have hcomm := Summable.tsum_comm' hU (fun N => (hinner N).summable)
    (fun γ => summable_sector m r hσ γ.1)
  rw [show (fun γ : {γ : ℕ →₀ ZMod r // γ ≠ 0} => sectorMass m r σ γ) =
    fun γ => ∑' N, F N γ from rfl, hcomm, tsum_congr fun N => (hinner N).tsum_eq]
  -- the nontrivial-sector sum over `A_{rm}` is the excess sum
  rw [excessSum, ← tsum_subtype_eq_of_support_subset (s := {N : EulerShell (r * m) |
    kummerVec r (N : ℕ) ≠ 0}) (fun N hN => by
      by_contra h
      exact hN (if_neg h))]
  set g : {N : EulerShell (r * m) // N ∈ {N : EulerShell (r * m) | kummerVec r (N : ℕ) ≠ 0}} → ℝ :=
    fun x => if kummerVec r ((x : EulerShell (r * m)) : ℕ) ≠ 0 then
      (((x : EulerShell (r * m)) : ℕ) : ℝ) ^ (-σ) else 0
  let e : ExcessShell m r ≃
      {N : EulerShell (r * m) // N ∈ {N : EulerShell (r * m) | kummerVec r (N : ℕ) ≠ 0}} :=
    Equiv.subtypeEquivRight fun N => (kummerVec_ne_zero_iff N).symm
  rw [show (∑' x, g x) = ∑' y : ExcessShell m r, g (e y) from (e.tsum_eq g).symm]
  refine tsum_congr fun N => ?_
  have hN : kummerVec r (((e N : {N : EulerShell (r * m) // _}) : EulerShell (r * m)) : ℕ) ≠ 0 :=
    (e N).2
  simp only [g]
  rw [if_pos hN]
  rfl

/-- The sector projection `Π_γ` onto the coordinates of residue `γ`. -/
def sectorProj (m r : ℕ) (γ : ℕ →₀ ZMod r) :
    LpTwo (EulerShell (r * m)) →L[ℂ] LpTwo (EulerShell (r * m)) :=
  lpDiag (fun N => if kummerVec r (N : ℕ) = γ then (1 : ℂ) else 0) 1 zero_le_one fun N => by
    split_ifs <;> simp

/-- `‖Π_γ Ω_{rm,σ}‖² = A_γ(σ)/S_{rm}(σ)`. -/
theorem norm_sq_sectorProj (hm : 1 ≤ m) (hr : 2 ≤ r) {σ : ℝ} (hσ : 1 < σ)
    (γ : ℕ →₀ ZMod r) :
    ‖sectorProj m r γ (shellVector (one_le_mul_m hm hr) hσ)‖ ^ 2 =
      sectorMass m r σ γ / eulerShellSum (r * m) σ := by
  rw [lp_two_norm_sq_eq_tsum, sectorMass, ← tsum_div_const]
  refine tsum_congr fun N => ?_
  rw [sectorProj, lpDiag_coe]
  split_ifs
  · rw [one_mul, norm_sq_eulerShellSource_v]
  · simp

/-- **Theorem 8.1 `(FE.47)`**: `Σ_{γ ≠ 0} ‖Π_γ Ω_{rm,σ}‖⁴ = V/S_{rm}(σ)²`. -/
theorem kummer_collision (hm : 1 ≤ m) (hr : 2 ≤ r) {σ : ℝ} (hσ : 1 < σ) :
    ∑' γ : {γ : ℕ →₀ ZMod r // γ ≠ 0},
        ‖sectorProj m r γ (shellVector (one_le_mul_m hm hr) hσ)‖ ^ 4 =
      kummerParseval m r σ / eulerShellSum (r * m) σ ^ 2 := by
  rw [kummerParseval, ← tsum_div_const]
  refine tsum_congr fun γ => ?_
  rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, norm_sq_sectorProj hm hr hσ, div_pow]

/-- **Theorem 8.1 `(FE.48)`**: conditioned on excess, `Σ_{γ ≠ 0} (A_γ/C_{m,r})² = V/C_{m,r}²`. -/
theorem kummer_collision_excess (m r : ℕ) (σ : ℝ) :
    ∑' γ : {γ : ℕ →₀ ZMod r // γ ≠ 0}, (sectorMass m r σ γ / excessSum m r σ) ^ 2 =
      kummerParseval m r σ / excessSum m r σ ^ 2 := by
  rw [kummerParseval, ← tsum_div_const]
  exact tsum_congr fun γ => div_pow _ _ _

end GaloisForLFunctions.HTGeometry.FormationExcess
