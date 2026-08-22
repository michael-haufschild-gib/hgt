import GaloisForLFunctions.HTGeometry.FDNLS.DispersionRelation
import GaloisForLFunctions.HTGeometry.FDNLS.Conservation

/-!
# The long-range lattice at `α = 2` versus the nearest-neighbour DNLS, and the mobility barrier

Zhong--Malomed--Yan, arXiv:2407.12441, Sections II A and IV, equations (23), (24), (42) and (43).

Taking the discretisation first and the limit `α → 2` afterwards produces the *long-range* lattice
of equation (23), whose coupling decays as `1/ℓ²`; taking the two limits in the opposite order
produces the ordinary nearest-neighbour DNLS of equation (24).  The paper's claim that the two
limits do not commute is proved here by comparing the two dispersion relations, `ω(k) = Ck²`
against `ω(k) = 2C(1 - cos k)`, and by exhibiting a nonzero long-range coupling at separation `2`,
where the nearest-neighbour operator has none.

Section IV estimates soliton mobility by the Peierls--Nabarro barrier, the difference of the free
energies `G = H - ωP` of the offsite- and onsite-centred modes.  Since `H` and `P` are separately
conserved, so is `G`.

## Main results

* `shortRangeDeriv`, `shortRangeDeriv_planeWave` — **equation (24)** and its dispersion
  `2C(1 - cos k)`.
* `hasSum_quasiRieszCoupling_two_cos` — **equation (23)**: the long-range lattice has dispersion
  `Ck²`.
* `dispersion_ne_shortRange`, `quasiRieszCoupling_two_two_ne_zero` — the two limits do not commute.
* `latticeFreeEnergy`, `pnBarrier_eq` — **equations (42) and (43)**.
* `latticeFreeEnergy_const` — the free energy is a constant of the motion.
-/

open Filter Topology Set

namespace GaloisForLFunctions.HTGeometry.FDNLS

/-! ## The nearest-neighbour operator -/

/-- **Equation (24).**  The nearest-neighbour discrete diffraction operator of the usual DNLS
equation. -/
noncomputable def shortRangeDeriv (u : ℤ → ℂ) (n : ℤ) : ℂ := 2 * u n - u (n + 1) - u (n - 1)

/-- **The dispersion relation of equation (24).**  The nearest-neighbour operator has symbol
`2(1 - cos k)`. -/
theorem shortRangeDeriv_planeWave (k : ℝ) (n : ℤ) :
    shortRangeDeriv (fun m => Complex.exp ((m : ℂ) * (k : ℂ) * Complex.I)) n
      = ((2 * (1 - Real.cos k) : ℝ) : ℂ) * Complex.exp ((n : ℂ) * (k : ℂ) * Complex.I) := by
  have hplus : ((n + 1 : ℤ) : ℂ) * (k : ℂ) * Complex.I
      = (n : ℂ) * (k : ℂ) * Complex.I + (k : ℂ) * Complex.I := by push_cast; ring
  have hminus : ((n - 1 : ℤ) : ℂ) * (k : ℂ) * Complex.I
      = (n : ℂ) * (k : ℂ) * Complex.I + -((k : ℂ) * Complex.I) := by push_cast; ring
  rw [shortRangeDeriv, hplus, hminus, Complex.exp_add, Complex.exp_add]
  have hc : Complex.exp ((k : ℂ) * Complex.I) + Complex.exp (-((k : ℂ) * Complex.I))
      = 2 * Complex.cos (k : ℂ) := by
    rw [Complex.two_cos, neg_mul]
  push_cast
  linear_combination (-Complex.exp ((n : ℂ) * (k : ℂ) * Complex.I)) * hc

/-! ## The long-range lattice at `α = 2` -/

/-- **The dispersion relation of equation (23).**  The `α = 2` long-range lattice has symbol `k²`
on the whole Brillouin zone. -/
theorem hasSum_quasiRieszCoupling_two_cos {k : ℝ} (hk : k ∈ Icc (-Real.pi) Real.pi) :
    HasSum (fun ℓ : ℤ => quasiRieszCoupling 2 ℓ * Real.cos ((ℓ : ℝ) * k)) (k ^ 2) := by
  have h := hasSum_quasiRieszCoupling_cos (α := 2) (by norm_num) le_rfl hk
  have habs : |k| ^ (2 : ℝ) = k ^ 2 := by
    rw [show (2:ℝ) = ((2:ℕ) : ℝ) by norm_num, Real.rpow_natCast, sq_abs]
  rwa [habs] at h

/-- **The two limits do not commute.**  The long-range symbol `k²` and the nearest-neighbour symbol
`2(1 - cos k)` differ inside the Brillouin zone. -/
theorem dispersion_ne_shortRange :
    ∃ k ∈ Icc (-Real.pi) Real.pi, k ^ 2 ≠ 2 * (1 - Real.cos k) := by
  refine ⟨Real.pi, ⟨by linarith [Real.pi_pos], le_rfl⟩, ?_⟩
  rw [Real.cos_pi]
  have h3 : (3:ℝ) < Real.pi := Real.pi_gt_three
  nlinarith

/-- The long-range lattice couples next-nearest neighbours, which the nearest-neighbour operator
never does. -/
theorem quasiRieszCoupling_two_two_ne_zero : quasiRieszCoupling 2 2 ≠ 0 := by
  rw [quasiRieszCoupling_two (by norm_num : (2:ℤ) ≠ 0)]
  have h : ((-1 : ℝ)) ^ (2 : ℤ) = 1 := by norm_num
  rw [h]
  norm_num

/-- The nearest-neighbour operator has no next-nearest-neighbour coupling: it annihilates a
lattice function supported at `n + 2`. -/
theorem shortRangeDeriv_nextNearest (n : ℤ) (c : ℂ) :
    shortRangeDeriv (fun m => if m = n + 2 then c else 0) n = 0 := by
  rw [shortRangeDeriv]
  have h0 : ¬ (n = n + 2) := by omega
  have h1 : ¬ (n + 1 = n + 2) := by omega
  have h2 : ¬ (n - 1 = n + 2) := by omega
  simp only [if_neg h0, if_neg h1, if_neg h2]
  ring

/-! ## The Peierls--Nabarro barrier -/

variable {ι : Type*} [Fintype ι]

/-- The free energy `G = H - ωP` whose difference between the offsite- and onsite-centred modes is
the Peierls--Nabarro barrier. -/
noncomputable def latticeFreeEnergy (C σ ω : ℝ) (D : ι → ι → ℝ) (u : ι → ℂ) : ℝ :=
  latticeHamiltonian C σ D u - ω * latticePower u

/-- **Equations (42) and (43).**  The Peierls--Nabarro barrier `ΔG = ΔH - ω ΔP`. -/
theorem pnBarrier_eq (C σ ω : ℝ) (D : ι → ι → ℝ) (uon uoff : ι → ℂ) :
    latticeFreeEnergy C σ ω D uoff - latticeFreeEnergy C σ ω D uon
      = (latticeHamiltonian C σ D uoff - latticeHamiltonian C σ D uon)
        - ω * (latticePower uoff - latticePower uon) := by
  rw [latticeFreeEnergy, latticeFreeEnergy]
  ring

/-- The free energy is a constant of the motion, since both `H` and `P` are. -/
theorem latticeFreeEnergy_const {C σ ω : ℝ} {D : ι → ι → ℝ} (hD : ∀ n m, D n m = D m n)
    {u : ℝ → ι → ℂ} (hu : IsLatticeNLSSolution C σ D u) (t₁ t₂ : ℝ) :
    latticeFreeEnergy C σ ω D (u t₁) = latticeFreeEnergy C σ ω D (u t₂) := by
  rw [latticeFreeEnergy, latticeFreeEnergy, latticeHamiltonian_const hD hu t₁ t₂,
    latticePower_const hD hu t₁ t₂]

end GaloisForLFunctions.HTGeometry.FDNLS
