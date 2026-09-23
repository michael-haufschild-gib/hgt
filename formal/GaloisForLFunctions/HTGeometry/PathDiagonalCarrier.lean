/-
# The diagonal carrier of the path-local shell

The `Z` and `ZZ` coordinates of the path-local Pauli shell span a `2n+3`-dimensional carrier inside
the `12n+15`-dimensional coefficient space, and on it the Hamiltonian is a diagonal matrix whose
entries are the classical Ising energies of the computational configurations.  The uniform
superposition has constant modulus in that basis, so it is the extremal seed for the flat-overlap
bound.

Main results:
* `pathDiagEnergy` — the classical energy of a configuration.
* `pathHamiltonian_eq_diagonal` — **the carrier Hamiltonian is diagonal**.
* `uniformSeed`, `norm_eucVec_uniformSeed` — the uniform superposition is a unit constant-modulus
  register state.
-/
import GaloisForLFunctions.HTGeometry.PathShellPatchTransport
import GaloisForLFunctions.HTGeometry.PauliZSetLabels
import GaloisForLFunctions.HTGeometry.NearDiagonalOverlapFlatness

open Matrix Finset
open scoped Matrix Matrix.Norms.L2Operator

noncomputable section

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

variable {n : ℕ}

theorem onsiteWord_two (s : Fin (n + 2)) :
    onsiteWord s 2 = pauliZSetLabel ({s} : Finset (Fin (n + 2))) := by
  funext t
  by_cases h : t = s <;> simp [onsiteWord, pauliZSetLabel, h]

theorem couplingWord_zz (e : Fin (n + 1)) :
    couplingWord e (2, 2) = pauliZSetLabel ({e.castSucc, e.succ} : Finset (Fin (n + 2))) := by
  funext t
  by_cases h1 : t = e.castSucc
  · simp [couplingWord, pauliZSetLabel, h1]
  · by_cases h2 : t = e.succ <;> simp [couplingWord, pauliZSetLabel, h1, h2]

/-- The classical Ising energy of a configuration under a carrier coefficient vector. -/
def pathDiagEnergy (u : PathShell n) (x : FiniteQubitConfiguration (Fin (n + 2))) : ℝ :=
  (∑ s : Fin (n + 2), u (Sum.inl (s, 2)) * zSetSign ({s} : Finset (Fin (n + 2))) x)
    + ∑ e : Fin (n + 1),
        u (Sum.inr (e, (2, 2))) * zSetSign ({e.castSucc, e.succ} : Finset (Fin (n + 2))) x

/-- **The carrier Hamiltonian is diagonal.** -/
theorem pathHamiltonian_eq_diagonal (u : PathShell n)
    (hu : ∀ l : PathLabel n, ¬ IsDiagLabel l → u l = 0) :
    pathHamiltonian u
      = Matrix.diagonal (fun x => ((pathDiagEnergy u x : ℝ) : ℂ)) := by
  classical
  ext x y
  rw [pathHamiltonian, Matrix.add_apply, Matrix.sum_apply, onsitePart, Matrix.sum_apply]
  by_cases hxy : x = y
  · subst hxy
    rw [Matrix.diagonal_apply_eq]
    have honsite : ∀ sq : Fin (n + 2) × Fin 3,
        (((u (Sum.inl sq) : ℝ) : ℂ) • finitePauliMatrix (onsiteWord sq.1 sq.2)) x x
          = if sq.2 = 2 then
              ((u (Sum.inl (sq.1, 2)) * zSetSign ({sq.1} : Finset (Fin (n + 2))) x : ℝ) : ℂ)
            else 0 := by
      intro sq
      by_cases hq : sq.2 = 2
      · obtain ⟨s, q⟩ := sq
        simp only at hq
        subst hq
        rw [if_pos rfl, Matrix.smul_apply, smul_eq_mul, onsiteWord_two,
          finitePauliMatrix_pauliZSetLabel, if_pos rfl]
        push_cast
        ring
      · rw [if_neg hq, Matrix.smul_apply, smul_eq_mul,
          hu (Sum.inl sq) (by simpa [IsDiagLabel] using hq)]
        simp
    have hedgeval : ∀ e : Fin (n + 1), (edgePart u e) x x
        = ((u (Sum.inr (e, (2, 2))) *
            zSetSign ({e.castSucc, e.succ} : Finset (Fin (n + 2))) x : ℝ) : ℂ) := by
      intro e
      rw [edgePart, Matrix.sum_apply, Finset.sum_eq_single ((2, 2) : Fin 3 × Fin 3)]
      · rw [Matrix.smul_apply, smul_eq_mul, couplingWord_zz,
          finitePauliMatrix_pauliZSetLabel, if_pos rfl]
        push_cast
        ring
      · intro ab _ hab
        rw [Matrix.smul_apply, smul_eq_mul,
          hu (Sum.inr (e, ab)) (by simpa [IsDiagLabel] using hab)]
        simp
      · intro h
        exact absurd (Finset.mem_univ ((2, 2) : Fin 3 × Fin 3)) h
    have hcollapse : (∑ sq : Fin (n + 2) × Fin 3,
          (if sq.2 = 2 then
            ((u (Sum.inl (sq.1, 2)) * zSetSign ({sq.1} : Finset (Fin (n + 2))) x : ℝ) : ℂ)
          else 0))
        = ((∑ s : Fin (n + 2),
            u (Sum.inl (s, 2)) * zSetSign ({s} : Finset (Fin (n + 2))) x : ℝ) : ℂ) := by
      rw [Fintype.sum_prod_type, Complex.ofReal_sum]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [Finset.sum_eq_single (2 : Fin 3)]
      · rw [if_pos rfl]
      · intro q _ hq
        rw [if_neg hq]
      · intro h
        exact absurd (Finset.mem_univ (2 : Fin 3)) h
    simp only [honsite, hedgeval]
    rw [hcollapse, ← Complex.ofReal_sum, pathDiagEnergy, Complex.ofReal_add]
  · rw [Matrix.diagonal_apply_ne _ hxy]
    have honsite : ∀ sq : Fin (n + 2) × Fin 3,
        (((u (Sum.inl sq) : ℝ) : ℂ) • finitePauliMatrix (onsiteWord sq.1 sq.2)) x y = 0 := by
      intro sq
      by_cases hq : sq.2 = 2
      · obtain ⟨s, q⟩ := sq
        simp only at hq
        subst hq
        rw [Matrix.smul_apply, smul_eq_mul, onsiteWord_two,
          finitePauliMatrix_pauliZSetLabel, if_neg hxy, mul_zero]
      · rw [Matrix.smul_apply, smul_eq_mul,
          hu (Sum.inl sq) (by simpa [IsDiagLabel] using hq)]
        simp
    have hedgeval : ∀ e : Fin (n + 1), (edgePart u e) x y = 0 := by
      intro e
      rw [edgePart, Matrix.sum_apply]
      refine Finset.sum_eq_zero fun ab _ => ?_
      by_cases hab : ab = (2, 2)
      · subst hab
        rw [Matrix.smul_apply, smul_eq_mul, couplingWord_zz,
          finitePauliMatrix_pauliZSetLabel, if_neg hxy, mul_zero]
      · rw [Matrix.smul_apply, smul_eq_mul,
          hu (Sum.inr (e, ab)) (by simpa [IsDiagLabel] using hab)]
        simp
    simp [honsite, hedgeval]

/-- The uniform superposition of a finite qubit register. -/
def uniformSeed (m : ℕ) : FiniteQubitConfiguration (Fin m) → ℂ :=
  fun _ => (((Real.sqrt (2 ^ m))⁻¹ : ℝ) : ℂ)

theorem norm_uniformSeed (m : ℕ) (x : FiniteQubitConfiguration (Fin m)) :
    ‖uniformSeed m x‖ = (Real.sqrt (2 ^ m))⁻¹ := by
  rw [uniformSeed, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]

theorem norm_eucVec_uniformSeed (m : ℕ) : ‖eucVec (uniformSeed m)‖ = 1 := by
  rw [norm_eucVec]
  have hcard : (Fintype.card (FiniteQubitConfiguration (Fin m)) : ℝ) = 2 ^ m := by
    simp
  have hpos : (0 : ℝ) < 2 ^ m := by positivity
  have hsum : ∑ _x : FiniteQubitConfiguration (Fin m), ‖uniformSeed m _x‖ ^ (2 : ℕ) = 1 := by
    simp only [norm_uniformSeed, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [inv_pow, Real.sq_sqrt (le_of_lt hpos), hcard]
    field_simp
  rw [hsum, Real.sqrt_one]


/-! ## Separated energies on a compact patch -/

theorem continuous_pathDiagEnergy (x : FiniteQubitConfiguration (Fin (n + 2))) :
    Continuous fun u : PathShell n => pathDiagEnergy u x := by
  unfold pathDiagEnergy
  refine Continuous.add (continuous_finsetSum _ fun s _ => ?_) (continuous_finsetSum _ fun e _ => ?_)
  · exact (PiLp.continuous_apply 2 (fun _ : PathLabel n => ℝ) (Sum.inl (s, 2))).mul
      continuous_const
  · exact (PiLp.continuous_apply 2 (fun _ : PathLabel n => ℝ) (Sum.inr (e, (2, 2)))).mul
      continuous_const

/-- **A uniform energy gap on a compact separated patch.**  If no two configurations share an
energy anywhere on a compact set of carrier coefficients, then their energies are uniformly
separated there. -/
theorem exists_uniform_energy_gap {K : Set (PathShell n)} (hK : IsCompact K)
    (hsep : ∀ u ∈ K, ∀ x y : FiniteQubitConfiguration (Fin (n + 2)), x ≠ y →
      pathDiagEnergy u x ≠ pathDiagEnergy u y) :
    ∃ gap : ℝ, 0 < gap ∧ ∀ u ∈ K, ∀ x y : FiniteQubitConfiguration (Fin (n + 2)), x ≠ y →
      gap ≤ |pathDiagEnergy u x - pathDiagEnergy u y| := by
  classical
  by_cases hKne : K.Nonempty
  · have hpair : ∀ p : FiniteQubitConfiguration (Fin (n + 2)) ×
        FiniteQubitConfiguration (Fin (n + 2)), ∃ c : ℝ, 0 < c ∧
        ∀ u ∈ K, p.1 ≠ p.2 → c ≤ |pathDiagEnergy u p.1 - pathDiagEnergy u p.2| := by
      intro p
      by_cases hp : p.1 = p.2
      · exact ⟨1, one_pos, fun u _ h => absurd hp h⟩
      · have hcont : ContinuousOn
            (fun u : PathShell n => |pathDiagEnergy u p.1 - pathDiagEnergy u p.2|) K :=
          (((continuous_pathDiagEnergy p.1).sub (continuous_pathDiagEnergy p.2)).abs).continuousOn
        obtain ⟨u₀, hu₀K, hu₀min⟩ := hK.exists_isMinOn hKne hcont
        refine ⟨|pathDiagEnergy u₀ p.1 - pathDiagEnergy u₀ p.2|, ?_, fun u huK _ => hu₀min huK⟩
        exact abs_pos.mpr (sub_ne_zero.mpr (hsep u₀ hu₀K p.1 p.2 hp))
    choose c hc0 hcle using hpair
    obtain ⟨p₀, -, hp₀⟩ := Finset.exists_min_image (Finset.univ :
      Finset (FiniteQubitConfiguration (Fin (n + 2)) ×
        FiniteQubitConfiguration (Fin (n + 2)))) c
      ⟨(fun _ => false, fun _ => false), Finset.mem_univ _⟩
    exact ⟨c p₀, hc0 p₀, fun u huK x y hxy =>
      le_trans (hp₀ (x, y) (Finset.mem_univ _)) (hcle (x, y) u huK hxy)⟩
  · refine ⟨1, one_pos, fun u huK => ?_⟩
    rw [Set.not_nonempty_iff_eq_empty] at hKne
    exact absurd huK (by rw [hKne]; exact Set.notMem_empty u)

end GaloisForLFunctions.HTGeometry

end
