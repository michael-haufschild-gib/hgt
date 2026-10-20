import GaloisForLFunctions.SquareRootThreshold.TwoBumpLagStructureLaw

/-!
# The ground energy of an off-line lattice is a strictly decreasing step function

The ground-state law gives the Weil floor of the off-line lattice `{½ ± δ + 2πik/L}` at aperture
`a` through `n = ⌈2a/L⌉` alone. This module evaluates it in closed form and shows that it drops at
every multiple of `L/2`.

* **Closed form** (`sqrt_latticeSums_eq`, `latticeFloor_eq`). With `u = δL`,
  `√(S₊S₋) = sinh(nu)/sinh(u)`, so `latticeFloor = n − sinh(nu)/sinh(u)`: the ground energy at
  aperture `a ∈ ((n−1)L/2, nL/2]`, `n ≥ 2`, is `L(n − U_{n−1}(cosh δL))` with `U` the Chebyshev
  polynomial of the second kind. The proof writes `S₊ S₋` as the square of the centred sum
  `Σ_j e^{u(2j − n + 1)}` and telescopes it against `2 sinh u`.
* **Strict decrease** (`latticeFloor_succ_lt`). `latticeFloor (n+1) < latticeFloor n` for `n ≥ 1`,
  because `sinh((n+1)u) − sinh(nu) > sinh u`.
* **Step law** (`offLineLattice_ground_energy_drops`). At every aperture `a = nL/2`, `n ≥ 2`, the
  floor `μ_n` holds, and every aperture beyond it has a polar-constrained test below a fixed
  `μ' < μ_n`: the ground energy is discontinuous from the right at every `nL/2`. The first drop,
  at `L/2`, is the lattice law itself (from the diagonal value `2` to `2 − 2cosh δL`).

For the restricted Weil operator of `ζ` the ground energy is continuous in the aperture
(`RHTower.tendsto_ccmRestrictedWeilGroundEnergy_suzukiRightAperture`); the jumps here come from the
exact periodicity of the lattice, whose lag structure is a sum of atoms at the lattice lags.
-/

open MeasureTheory Complex Set Filter Topology
open scoped Real ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.SquareRootThreshold

open Zeta23 _root_.RHTower

/-- The centred sum `σ_n(u) = Σ_{j<n} e^{u(2j − n + 1)}`. -/
def centredSum (u : ℝ) (n : ℕ) : ℝ := ∑ j : Fin n, Real.exp (u * (2 * (j : ℝ) - n + 1))

/-- `2 sinh u · σ_n(u) = 2 sinh(nu)` (telescoping). -/
theorem two_sinh_mul_centredSum (u : ℝ) (n : ℕ) :
    2 * Real.sinh u * centredSum u n = 2 * Real.sinh (n * u) := by
  rw [centredSum, Fin.sum_univ_eq_sum_range (fun j => Real.exp (u * (2 * (j : ℝ) - n + 1))) n,
    Finset.mul_sum]
  have hterm : ∀ j : ℕ, 2 * Real.sinh u * Real.exp (u * (2 * (j : ℝ) - n + 1)) =
      Real.exp (u * (2 * ((j + 1 : ℕ) : ℝ) - n)) - Real.exp (u * (2 * (j : ℝ) - n)) := by
    intro j
    rw [Real.sinh_eq, show 2 * ((Real.exp u - Real.exp (-u)) / 2) = Real.exp u - Real.exp (-u)
      by ring, sub_mul, ← Real.exp_add, ← Real.exp_add]
    push_cast
    ring_nf
  rw [Finset.sum_congr rfl fun j _ => hterm j,
    Finset.sum_range_sub (fun j => Real.exp (u * (2 * (j : ℝ) - n)))]
  rw [Real.sinh_eq]
  push_cast
  ring_nf

theorem centredSum_pos (u : ℝ) {n : ℕ} (hn : 0 < n) : 0 < centredSum u n :=
  Finset.sum_pos (fun _ _ => Real.exp_pos _) ⟨⟨0, hn⟩, Finset.mem_univ _⟩

/-- `S₊ = e^{u(n−1)} σ_n(u)` and `S₋ = e^{−u(n−1)} σ_n(u)`. -/
theorem latticeSum_plus (L δ : ℝ) (n : ℕ) :
    ∑ j : Fin n, Real.exp (δ * (j * L)) ^ 2 =
      Real.exp (δ * L * (n - 1)) * centredSum (δ * L) n := by
  rw [centredSum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Real.exp_nat_mul, ← Real.exp_add]
  congr 1
  push_cast
  ring

theorem latticeSum_minus (L δ : ℝ) (n : ℕ) :
    ∑ j : Fin n, Real.exp (-(δ * (j * L))) ^ 2 =
      Real.exp (-(δ * L * (n - 1))) * centredSum (δ * L) n := by
  rw [centredSum, Finset.mul_sum]
  -- reflect `j ↦ n − 1 − j`
  rw [← Equiv.sum_comp Fin.revPerm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Fin.revPerm_apply, Fin.val_rev, ← Real.exp_nat_mul, ← Real.exp_add]
  congr 1
  have hj : (j : ℕ) + 1 ≤ n := j.isLt
  rw [Nat.cast_sub (by omega)]
  push_cast
  ring

/-- **Closed form.** `√(S₊S₋) = σ_n(δL)`. -/
theorem sqrt_latticeSums_eq (L δ : ℝ) (n : ℕ) :
    √(∑ j : Fin n, Real.exp (δ * (j * L)) ^ 2) * √(∑ j : Fin n, Real.exp (-(δ * (j * L))) ^ 2) =
      centredSum (δ * L) n := by
  rw [← Real.sqrt_mul (Finset.sum_nonneg fun j _ => sq_nonneg _), latticeSum_plus,
    latticeSum_minus, show Real.exp (δ * L * (n - 1)) * centredSum (δ * L) n *
      (Real.exp (-(δ * L * (n - 1))) * centredSum (δ * L) n) = centredSum (δ * L) n ^ 2 by
      rw [show Real.exp (δ * L * (n - 1)) * centredSum (δ * L) n *
        (Real.exp (-(δ * L * (n - 1))) * centredSum (δ * L) n) =
        (Real.exp (δ * L * (n - 1)) * Real.exp (-(δ * L * (n - 1)))) * centredSum (δ * L) n ^ 2
        by ring, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul]]
  exact Real.sqrt_sq (Finset.sum_nonneg fun _ _ => (Real.exp_pos _).le)

/-- **The lattice floor in closed form.** `latticeFloor = n − sinh(nδL)/sinh(δL)`. -/
theorem latticeFloor_eq {L δ : ℝ} (hu : 0 < δ * L) (n : ℕ) :
    latticeFloor L δ n = n - Real.sinh (n * (δ * L)) / Real.sinh (δ * L) := by
  rw [latticeFloor, sqrt_latticeSums_eq]
  have hs : 0 < Real.sinh (δ * L) := Real.sinh_pos_iff.mpr hu
  congr 1
  rw [eq_div_iff hs.ne']
  have := two_sinh_mul_centredSum (δ * L) n
  linarith

/-- **Strict decrease.** `latticeFloor (n + 1) < latticeFloor n` for `n ≥ 1`. -/
theorem latticeFloor_succ_lt {L δ : ℝ} (hu : 0 < δ * L) {n : ℕ} (hn : 1 ≤ n) :
    latticeFloor L δ (n + 1) < latticeFloor L δ n := by
  have hs : 0 < Real.sinh (δ * L) := Real.sinh_pos_iff.mpr hu
  have hc : 1 < Real.cosh (δ * L) := Real.one_lt_cosh.mpr hu.ne'
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hcn : 1 ≤ Real.cosh (n * (δ * L)) := Real.one_le_cosh _
  have hsn : 0 < Real.sinh (n * (δ * L)) := Real.sinh_pos_iff.mpr (by positivity)
  have hadd : Real.sinh (((n + 1 : ℕ) : ℝ) * (δ * L)) =
      Real.sinh (n * (δ * L)) * Real.cosh (δ * L) + Real.cosh (n * (δ * L)) * Real.sinh (δ * L) := by
    rw [show ((n + 1 : ℕ) : ℝ) * (δ * L) = n * (δ * L) + δ * L by push_cast; ring, Real.sinh_add]
  rw [latticeFloor_eq hu, latticeFloor_eq hu, hadd]
  have hlt : Real.sinh (δ * L) < Real.sinh (n * (δ * L)) * Real.cosh (δ * L) +
      Real.cosh (n * (δ * L)) * Real.sinh (δ * L) - Real.sinh (n * (δ * L)) := by nlinarith
  have h2 : 1 < (Real.sinh (n * (δ * L)) * Real.cosh (δ * L) +
      Real.cosh (n * (δ * L)) * Real.sinh (δ * L) - Real.sinh (n * (δ * L))) / Real.sinh (δ * L) := by
    rw [lt_div_iff₀ hs]; linarith
  rw [sub_div] at h2
  push_cast
  linarith

/-- **Step law.** For `n ≥ 2` the off-line lattice satisfies the floor `μ = latticeFloor n` at
aperture `nL/2`, while at every aperture `a ∈ (nL/2, (n+1)L/2]` some polar-constrained test lies
below a fixed `μ' < μ`: the ground energy drops at `nL/2`. -/
theorem offLineLattice_ground_energy_drops {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2)
    {n : ℕ} (hn : 2 ≤ n) :
    ∃ μ μ' : ℝ, μ' < μ ∧
      (∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-(n * L / 2)) (n * L / 2) →
        L * μ * ∫ t, ‖f t‖ ^ 2 ≤ ((offLineLatticeConfig hL hδ hδ').W f f).re) ∧
      ∀ a : ℝ, n * L / 2 < a → a ≤ (n + 1) * L / 2 →
        ∃ f : ℝ → ℂ, ContDiff ℝ 2 f ∧ tsupport f ⊆ Icc (-a) a ∧ paperFT f (I / 2) = 0 ∧
          paperFT f (-(I / 2)) = 0 ∧
            ((offLineLatticeConfig hL hδ hδ').W f f).re < L * μ' * ∫ t, ‖f t‖ ^ 2 := by
  have hu : 0 < δ * L := mul_pos hδ hL
  have hlt := latticeFloor_succ_lt hu (n := n) (by omega)
  refine ⟨latticeFloor L δ n, (latticeFloor L δ (n + 1) + latticeFloor L δ n) / 2,
    by linarith, fun f hf hfs => ?_, fun a ha1 ha2 => ?_⟩
  · have h := offLineLattice_weil_floor hL hδ hδ' hf hfs
    have hn' : ⌈2 * (n * L / 2) / L⌉₊ = n := by
      rw [show 2 * (n * L / 2) / L = (n : ℝ) by field_simp]
      exact Nat.ceil_natCast n
    rwa [hn'] at h
  · have hceil : ⌈2 * a / L⌉₊ = n + 1 := by
      rw [Nat.ceil_eq_iff (by omega)]
      constructor
      · rw [lt_div_iff₀ hL]; push_cast; linarith
      · rw [div_le_iff₀ hL]; push_cast; linarith
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
    refine offLineLattice_hodge_floor_sharp hL hδ hδ' (by nlinarith) ?_
    rw [hceil]
    linarith

end GaloisForLFunctions.SquareRootThreshold
