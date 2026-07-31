import GaloisForLFunctions.RHTower.CountableSpectralHamiltonianRealization
import GaloisForLFunctions.HTGeometry.SummableSpectrumScrewHull

/-!
# Orbit-cover law for countable quantum recurrence

The recurrence clock is bounded by metric complexity of the weighted
quantum orbit itself. If a finite family of Hilbert-space balls covers the
orbit, two of the first orbit points share a ball; unitarity translates
their collision into a return. This is the quantitative bridge from the
relation-determined orbit closure to observer-weighted recurrence time.
-/

open scoped BigOperators InnerProductSpace
open Complex

noncomputable section

namespace RHTower

theorem countableSpectralKetAt_zero
    (p : ℕ → ℝ) (hp : ∀ k, 0 ≤ p k) (hsum : Summable p)
    (x : ℕ → UnitAddCircle) :
    countableSpectralKetAt p hp hsum x 0 =
      countableSpectralKet p hp hsum := by
  apply lp.ext
  funext k
  simp [countableSpectralHamiltonianEvolutionPhase,
    countableSpectralPhaseEnergy]

theorem countableSpectralHamiltonianEvolutionPhase_add
    (x : ℕ → UnitAddCircle) (s t : ℝ) (k : ℕ) :
    countableSpectralHamiltonianEvolutionPhase x (s + t) k =
      countableSpectralHamiltonianEvolutionPhase x s k *
        countableSpectralHamiltonianEvolutionPhase x t k := by
  rw [countableSpectralHamiltonianEvolutionPhase,
    countableSpectralHamiltonianEvolutionPhase,
    countableSpectralHamiltonianEvolutionPhase, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/--
Unitary time translation preserves the distance between two points of the
countable spectral orbit.
-/
theorem norm_countableSpectralKetAt_sub_ketAt_eq_timeDifference
    (p : ℕ → ℝ) (hp : ∀ k, 0 ≤ p k) (hsum : Summable p)
    (x : ℕ → UnitAddCircle) {i j : ℕ} (hij : i ≤ j) :
    ‖countableSpectralKetAt p hp hsum x (j : ℝ) -
        countableSpectralKetAt p hp hsum x (i : ℝ)‖ =
      ‖countableSpectralKetAt p hp hsum x ((j - i : ℕ) : ℝ) -
        countableSpectralKet p hp hsum‖ := by
  have hj : (j : ℝ) = i + (j - i : ℕ) := by
    exact_mod_cast (Nat.add_sub_of_le hij).symm
  have hsquares :
      ‖countableSpectralKetAt p hp hsum x (j : ℝ) -
          countableSpectralKetAt p hp hsum x (i : ℝ)‖ ^ 2 =
        ‖countableSpectralKetAt p hp hsum x ((j - i : ℕ) : ℝ) -
          countableSpectralKet p hp hsum‖ ^ 2 := by
    rw [HilbertSchmidt.lp_norm_sq_eq,
      HilbertSchmidt.lp_norm_sq_eq]
    apply tsum_congr
    intro k
    change
      ‖(Real.sqrt (p k) : ℂ) *
            countableSpectralHamiltonianEvolutionPhase x (j : ℝ) k -
          (Real.sqrt (p k) : ℂ) *
            countableSpectralHamiltonianEvolutionPhase x (i : ℝ) k‖ ^ 2 =
        ‖(Real.sqrt (p k) : ℂ) *
            countableSpectralHamiltonianEvolutionPhase
              x ((j - i : ℕ) : ℝ) k -
          (Real.sqrt (p k) : ℂ)‖ ^ 2
    have hphase :
        countableSpectralHamiltonianEvolutionPhase x (j : ℝ) k =
          countableSpectralHamiltonianEvolutionPhase x (i : ℝ) k *
            countableSpectralHamiltonianEvolutionPhase
              x ((j - i : ℕ) : ℝ) k := by
      rw [hj, countableSpectralHamiltonianEvolutionPhase_add]
    rw [hphase]
    have hleft :
        (Real.sqrt (p k) : ℂ) *
              (countableSpectralHamiltonianEvolutionPhase x i k *
                countableSpectralHamiltonianEvolutionPhase
                  x ((j - i : ℕ) : ℝ) k) -
            (Real.sqrt (p k) : ℂ) *
              countableSpectralHamiltonianEvolutionPhase x i k =
          ((Real.sqrt (p k) : ℂ) *
              countableSpectralHamiltonianEvolutionPhase x i k) *
            (countableSpectralHamiltonianEvolutionPhase
                x ((j - i : ℕ) : ℝ) k - 1) := by ring
    have hright :
        (Real.sqrt (p k) : ℂ) *
              countableSpectralHamiltonianEvolutionPhase
                x ((j - i : ℕ) : ℝ) k -
            (Real.sqrt (p k) : ℂ) =
          (Real.sqrt (p k) : ℂ) *
            (countableSpectralHamiltonianEvolutionPhase
                x ((j - i : ℕ) : ℝ) k - 1) := by ring
    rw [hleft, hright, norm_mul, norm_mul, norm_mul,
      countableSpectralHamiltonianEvolutionPhase_norm, mul_one]
  nlinarith [
    norm_nonneg
      (countableSpectralKetAt p hp hsum x (j : ℝ) -
        countableSpectralKetAt p hp hsum x (i : ℝ)),
    norm_nonneg
      (countableSpectralKetAt p hp hsum x ((j - i : ℕ) : ℝ) -
        countableSpectralKet p hp hsum)]

/--
A finite family of radius-`r` Hilbert balls covers the entire weighted
spectral orbit.
-/
def CountableSpectralOrbitCover
    (p : ℕ → ℝ) (hp : ∀ k, 0 ≤ p k) (hsum : Summable p)
    (x : ℕ → UnitAddCircle)
    (C : Finset CountableSpectralPhaseSpace) (r : ℝ) : Prop :=
  ∀ n : ℕ, ∃ c ∈ C,
    ‖countableSpectralKetAt p hp hsum x n - c‖ ≤ r

/--
Orbit-cover entropy bounds the actual positive survival-return clock.
The return defect is exactly the quadratic collision radius `2 r²`.
-/
theorem exists_countableSpectralFirstReturn_le_card_of_orbitCover
    (p : ℕ → ℝ) (hp : ∀ k, 0 ≤ p k)
    (hsum : Summable p) (htotal : ∑' k, p k = 1)
    (x : ℕ → UnitAddCircle)
    (C : Finset CountableSpectralPhaseSpace) {r : ℝ}
    (hr : 0 ≤ r)
    (hcover : CountableSpectralOrbitCover p hp hsum x C r) :
    ∃ n : ℕ, 0 < n ∧ n ≤ C.card ∧
      CountableTorusWeightedCoherenceAt p x (2 * r ^ 2) n := by
  classical
  let center : Fin (C.card + 1) → C := fun k =>
    ⟨(hcover k.1).choose, (hcover k.1).choose_spec.1⟩
  have hcenter (k : Fin (C.card + 1)) :
      ‖countableSpectralKetAt p hp hsum x k.1 -
          (center k : CountableSpectralPhaseSpace)‖ ≤ r :=
    (hcover k.1).choose_spec.2
  obtain ⟨i, j, hij, hcenter_eq⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt center (by simp)
  have collision {i j : Fin (C.card + 1)} (hij_lt : i.1 < j.1)
      (hcenter_eq : center i = center j) :
      ∃ n : ℕ, 0 < n ∧ n ≤ C.card ∧
        CountableTorusWeightedCoherenceAt p x (2 * r ^ 2) n := by
    let n := j.1 - i.1
    have hn0 : 0 < n := Nat.sub_pos_of_lt hij_lt
    have hnC : n ≤ C.card :=
      (Nat.sub_le _ _).trans (Nat.lt_succ_iff.mp j.2)
    have hpair :
        ‖countableSpectralKetAt p hp hsum x j.1 -
            countableSpectralKetAt p hp hsum x i.1‖ ≤ 2 * r := by
      calc
        ‖countableSpectralKetAt p hp hsum x j.1 -
            countableSpectralKetAt p hp hsum x i.1‖ ≤
            ‖countableSpectralKetAt p hp hsum x j.1 -
                (center j : CountableSpectralPhaseSpace)‖ +
              ‖(center j : CountableSpectralPhaseSpace) -
                countableSpectralKetAt p hp hsum x i.1‖ :=
          norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ r + r := add_le_add (hcenter j) (by
          rw [hcenter_eq.symm, norm_sub_rev]
          exact hcenter i)
        _ = 2 * r := by ring
    have hreturnDist :
        ‖countableSpectralKetAt p hp hsum x n -
            countableSpectralKet p hp hsum‖ ≤ 2 * r := by
      change
        ‖countableSpectralKetAt p hp hsum x (n : ℝ) -
            countableSpectralKet p hp hsum‖ ≤ 2 * r
      rw [← norm_countableSpectralKetAt_sub_ketAt_eq_timeDifference
        p hp hsum x (Nat.le_of_lt hij_lt)]
      exact hpair
    have hnormKet := countableSpectralKet_norm p hp hsum htotal
    have hnormAt :=
      countableSpectralKetAt_norm p hp hsum htotal x n
    have hinner :=
      countableSpectralKet_inner_ketAt p hp hsum x n
    have hphase :
        summableWeightedPhaseAmplitude p
            (countableSpectralHamiltonianEvolutionPhase x n) =
          summableWeightedPhaseAmplitude p
            (fun k => fourier 1 (((n : ℕ) : ℤ) • x k)) := by
      rw [summableWeightedPhaseAmplitude,
        summableWeightedPhaseAmplitude]
      apply tsum_congr
      intro k
      rw [countableSpectralHamiltonianEvolutionPhase_nat]
    have hdistSq :
        ‖countableSpectralKetAt p hp hsum x n -
            countableSpectralKet p hp hsum‖ ^ 2 =
          2 - 2 *
            (summableWeightedPhaseAmplitude p
              (fun k => fourier 1 (((n : ℕ) : ℤ) • x k))).re := by
      rw [norm_sub_sq (𝕜 := ℂ)
          (countableSpectralKetAt p hp hsum x n)
          (countableSpectralKet p hp hsum),
        hnormAt, hnormKet, inner_re_symm,
        hinner, hphase]
      change (2 : ℝ) -
          (summableWeightedPhaseAmplitude p
            (fun k => fourier 1 (((n : ℕ) : ℤ) • x k))).re * 2 =
        2 - 2 *
          (summableWeightedPhaseAmplitude p
            (fun k => fourier 1 (((n : ℕ) : ℤ) • x k))).re
      ring
    have hdistBound :
        ‖countableSpectralKetAt p hp hsum x n -
            countableSpectralKet p hp hsum‖ ^ 2 ≤
          (2 * r) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (by norm_num) hr)).mpr
        hreturnDist
    have hre :
        1 - 2 * r ^ 2 ≤
          (summableWeightedPhaseAmplitude p
            (fun k => fourier 1 (((n : ℕ) : ℤ) • x k))).re := by
      rw [hdistSq] at hdistBound
      nlinarith
    refine ⟨n, hn0, hnC, hn0, ?_⟩
    exact hre.trans (Complex.re_le_norm _)
  rcases lt_or_gt_of_ne hij with hij_lt | hji_lt
  · exact collision hij_lt hcenter_eq
  · exact collision hji_lt hcenter_eq.symm

/-- Actual-first-return form of the orbit-cover law. -/
theorem countableSpectralFirstCoherenceTime_le_card_of_orbitCover
    (p : ℕ → ℝ) (hp : ∀ k, 0 ≤ p k)
    (hsum : Summable p) (htotal : ∑' k, p k = 1)
    (x : ℕ → UnitAddCircle)
    (C : Finset CountableSpectralPhaseSpace) {r : ℝ}
    (hr : 0 ≤ r)
    (hcover : CountableSpectralOrbitCover p hp hsum x C r) :
    countableTorusWeightedFirstCoherenceTime p x (2 * r ^ 2) ≤
      C.card := by
  obtain ⟨n, _hn0, hnC, hn⟩ :=
    exists_countableSpectralFirstReturn_le_card_of_orbitCover
      p hp hsum htotal x C hr hcover
  exact
    (countableTorusWeightedFirstCoherenceTime_le_of
      p x (2 * r ^ 2) hn).trans (by exact_mod_cast hnC)

end RHTower
