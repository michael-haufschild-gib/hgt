import GaloisForLFunctions.HTGeometry.TwoLocalWitness
import GaloisForLFunctions.HTGeometry.TwoLocalExactComplexityLaw
import GaloisForLFunctions.HTGeometry.TwoLocalRationalSpecialisation
import GaloisForLFunctions.HTGeometry.HilbertIrreducibility.LargeSpecialisation
import GaloisForLFunctions.HTGeometry.HypercubeTransverseCollisionBound

/-!
# A lacunary two-local witness: symmetric Galois group *and* small spectral collision

Hilbert irreducibility with a lacunary specialisation
(`HilbertIrreducibility.gal_card_of_specialisation_lacunary`) produces transverse couplings that are
simultaneously larger than any prescribed bound and growing by a factor three from each coordinate
to every later one.  The second property makes the transverse energies `∑_i ± u_i` separated by at
least `u_0`, and the Walsh-frame collision bound then makes the spectral collision of the all-zero
product state as close to `2^{-n}` as one likes — in particular below `4(2/3)^n`, which is the
hypothesis Theorem C of the arithmetic hardness–recurrence card consumes.

## Main results

* `exists_rational_specialisation_lacunary` — the lacunary Galois-preserving specialisation.
* `exists_twoLocal_lacunary_gal` — lacunary transverse couplings with symmetric Galois group.
-/

open Matrix Polynomial
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

namespace TwoLocalWitness

set_option linter.unusedSectionVars false

noncomputable section

variable {m : ℕ}

/-- **A lacunary rational transverse Hamiltonian with symmetric Galois group.** -/
theorem exists_rational_specialisation_lacunary (N : ℤ) {d : (Fin (m + 1) → Bool) → ℚ}
    (hd : Function.Injective d)
    (hδinj : ∀ i, Function.Injective (detuning d i))
    (hδne : ∀ i z z', detuning d i z ≠ -detuning d i z')
    {g : MvPolynomial (Fin (m + 1)) ℚ} (hg : g ≠ 0) :
    ∃ y : Fin (m + 1) → ℚ, (∀ i, ((N : ℤ) : ℚ) < y i) ∧
      (∀ i j : Fin (m + 1), (i : ℕ) < (j : ℕ) → 3 * y i < y j) ∧
      MvPolynomial.eval y g ≠ 0 ∧
      Nat.card ((universalCharpoly ℚ (m + 1) d).map (MvPolynomial.eval y)).Gal
        = (2 ^ (m + 1)).factorial :=
  HilbertIrreducibility.gal_card_of_specialisation_lacunary N
    (universalCharpoly_monic ℚ (m + 1) d) (natDegree_universalCharpoly d)
    (separable_universalCharpoly_map hd)
    (card_gal_universalCharpoly (by norm_num) hd hδinj hδne) hg

/-- **The explicit witness with lacunary transverse couplings.** -/
theorem exists_twoLocal_lacunary_gal (N : ℤ) (c : ℚ) {g : MvPolynomial (Fin (m + 1)) ℚ}
    (hg : g ≠ 0) :
    ∃ u : Fin (m + 1) → ℚ, (∀ i, ((N : ℤ) : ℚ) < u i) ∧
      (∀ i j : Fin (m + 1), (i : ℕ) < (j : ℕ) → 3 * u i < u j) ∧
      MvPolynomial.eval u g ≠ 0 ∧
      Nat.card ((twoLocalHam c 0 witnessCoupling u).charpoly).Gal = (2 ^ (m + 1)).factorial := by
  obtain ⟨y, hyN, hyrat, hy, hgal⟩ := exists_rational_specialisation_lacunary N
    (witnessDiagonal_injective c) (detuning_witnessDiagonal_injective c)
    (detuning_witnessDiagonal_ne_neg c) hg
  refine ⟨y, hyN, hyrat, hy, ?_⟩
  rwa [map_universalCharpoly_eval] at hgal

/-! ### The small-collision witness -/

/-- The lacunary transverse field, extended to all of `ℕ` by continuing geometrically. -/
def lacExtend {m : ℕ} (u : Fin (m + 1) → ℝ) : ℕ → ℝ :=
  fun k => if h : k < m + 1 then u ⟨k, h⟩ else 3 ^ (k - m) * u ⟨m, by omega⟩

theorem lacExtend_val {m : ℕ} (u : Fin (m + 1) → ℝ) (i : Fin (m + 1)) :
    lacExtend u (i : ℕ) = u i := by
  rw [lacExtend, dif_pos i.isLt]

theorem lacExtend_pos {m : ℕ} {u : Fin (m + 1) → ℝ} (hu : ∀ i, 0 < u i) (k : ℕ) :
    0 < lacExtend u k := by
  rw [lacExtend]
  by_cases h : k < m + 1
  · rw [dif_pos h]
    exact hu _
  · rw [dif_neg h]
    exact mul_pos (by positivity) (hu _)

theorem lacExtend_grow {m : ℕ} {u : Fin (m + 1) → ℝ} (hu : ∀ i, 0 < u i)
    (hrat : ∀ i j : Fin (m + 1), (i : ℕ) < (j : ℕ) → 3 * u i < u j) (k : ℕ) :
    3 * lacExtend u k ≤ lacExtend u (k + 1) := by
  by_cases h2 : k + 1 < m + 1
  · have h1 : k < m + 1 := by omega
    rw [lacExtend, lacExtend, dif_pos h1, dif_pos h2]
    exact le_of_lt (hrat ⟨k, h1⟩ ⟨k + 1, h2⟩ (by simp))
  · by_cases h1 : k < m + 1
    · have hk : k = m := by omega
      rw [lacExtend, lacExtend, dif_pos h1, dif_neg h2]
      have hsub : k + 1 - m = 1 := by omega
      rw [hsub, pow_one]
      have hfin : (⟨k, h1⟩ : Fin (m + 1)) = ⟨m, by omega⟩ := Fin.ext hk
      rw [hfin]
    · rw [lacExtend, lacExtend, dif_neg h1, dif_neg h2]
      have hsub : k + 1 - m = (k - m) + 1 := by omega
      rw [hsub, pow_succ]
      have hp : (0 : ℝ) < u ⟨m, by omega⟩ := hu _
      have h3 : (0 : ℝ) < 3 ^ (k - m) := by positivity
      nlinarith

/-- **A lacunary two-local witness with symmetric Galois group and small spectral collision.** -/
theorem exists_twoLocal_lacunary_smallCollision (m : ℕ) (c : ℚ)
    {g : MvPolynomial (Fin (m + 1)) ℚ} (hg : g ≠ 0) :
    ∃ (u : Fin (m + 1) → ℚ)
      (hH : (transverseFamilyHam (fun x => ((witnessDiagonal c x : ℚ) : ℂ))
              (fun i => ((u i : ℚ) : ℂ))).IsHermitian),
      MvPolynomial.eval u g ≠ 0 ∧
      Nat.card ((twoLocalHam c 0 witnessCoupling u).charpoly).Gal = (2 ^ (m + 1)).factorial ∧
      spectralCollision (hermitianEigenBasis _ hH) (Walsh.zeroState (m + 1))
        < 4 * (2 / 3 : ℝ) ^ (m + 1) := by
  classical
  set dC : (Fin (m + 1) → Bool) → ℂ := fun x => ((witnessDiagonal c x : ℚ) : ℂ) with hdC
  set K : ℝ := ‖dC‖ with hK
  have hKnn : 0 ≤ K := norm_nonneg _
  set B : ℝ := Walsh.cubeNorm (m + 1) with hB
  set A : ℝ := Real.sqrt (4 * (2 / 3 : ℝ) ^ (m + 1)) with hA
  have hApos : 0 < A := Real.sqrt_pos.mpr (by positivity)
  have hAsq : A * A = 4 * (2 / 3 : ℝ) ^ (m + 1) := Real.mul_self_sqrt (by positivity)
  have hBpos : 0 < B := Walsh.cubeNorm_pos _
  have hBsq : B * B = ((2 : ℝ) ^ (m + 1))⁻¹ := Walsh.cubeNorm_sq _
  have hBA : B < A := by
    have hlt : B * B < A * A := by
      rw [hBsq, hAsq]
      have h1 : ((2 : ℝ) ^ (m + 1))⁻¹ = (1 / 2 : ℝ) ^ (m + 1) := by
        rw [one_div, inv_pow]
      have h2 : ((1 : ℝ) / 2) ^ (m + 1) < (2 / 3 : ℝ) ^ (m + 1) := by
        refine pow_lt_pow_left₀ (by norm_num) (by norm_num) (by omega)
      have h3 : (0 : ℝ) < (2 / 3 : ℝ) ^ (m + 1) := by positivity
      rw [h1]
      linarith
    nlinarith [hBpos, hApos]
  set Nr : ℝ := 2 * K / (A - B) with hNr
  set N : ℤ := max 1 (⌈Nr⌉ + 1) with hN
  have hN1 : (1 : ℤ) ≤ N := le_max_left _ _
  have hNgt : Nr < ((N : ℤ) : ℝ) := by
    have h1 : Nr ≤ ((⌈Nr⌉ : ℤ) : ℝ) := Int.le_ceil _
    have h2 : ((⌈Nr⌉ : ℤ) : ℝ) < ((⌈Nr⌉ + 1 : ℤ) : ℝ) := by
      push_cast
      linarith
    have h3 : ((⌈Nr⌉ + 1 : ℤ) : ℝ) ≤ ((N : ℤ) : ℝ) := by
      have : (⌈Nr⌉ + 1 : ℤ) ≤ N := le_max_right _ _
      exact_mod_cast this
    linarith
  obtain ⟨u, huN, hurat, hug, hgal⟩ := exists_twoLocal_lacunary_gal N c hg
  have hHerm : (transverseFamilyHam (fun x => ((witnessDiagonal c x : ℚ) : ℂ))
      (fun i => ((u i : ℚ) : ℂ))).IsHermitian := by
    have hmap : (transverseFamilyHam (witnessDiagonal c) u).map (algebraMap ℚ ℂ)
        = transverseFamilyHam (fun x => ((witnessDiagonal c x : ℚ) : ℂ))
            (fun i => ((u i : ℚ) : ℂ)) := map_transverseFamilyHam _ _ _
    rw [← hmap, Matrix.IsHermitian]
    ext x y
    rw [Matrix.conjTranspose_apply, Matrix.map_apply, Matrix.map_apply]
    show (starRingEnd ℂ) (algebraMap ℚ ℂ (transverseFamilyHam (witnessDiagonal c) u y x))
        = algebraMap ℚ ℂ (transverseFamilyHam (witnessDiagonal c) u x y)
    rw [show (algebraMap ℚ ℂ) (transverseFamilyHam (witnessDiagonal c) u y x)
        = ((transverseFamilyHam (witnessDiagonal c) u y x : ℚ) : ℂ) from rfl,
      map_ratCast (starRingEnd ℂ), transverseFamilyHam_symm]
    rfl
  refine ⟨u, hHerm, hug, hgal, ?_⟩
  · -- the collision bound
    set uR : Fin (m + 1) → ℝ := fun i => ((u i : ℚ) : ℝ) with huR
    set dR : (Fin (m + 1) → Bool) → ℝ := fun x => ((witnessDiagonal c x : ℚ) : ℝ) with hdR
    have hNR : (1 : ℝ) ≤ ((N : ℤ) : ℝ) := by exact_mod_cast hN1
    have huNR : ∀ i, ((N : ℤ) : ℝ) < uR i := by
      intro i
      have hq := huN i
      show ((N : ℤ) : ℝ) < ((u i : ℚ) : ℝ)
      exact_mod_cast hq
    have hupos : ∀ i, 0 < uR i := fun i => lt_of_lt_of_le (by linarith) (le_of_lt (huNR i))
    have huratR : ∀ i j : Fin (m + 1), (i : ℕ) < (j : ℕ) → 3 * uR i < uR j := by
      intro i j hij
      have hq := hurat i j hij
      show (3 : ℝ) * ((u i : ℚ) : ℝ) < ((u j : ℚ) : ℝ)
      exact_mod_cast hq
    set w : ℕ → ℝ := lacExtend uR with hw
    have hwpos : ∀ k, 0 < w k := lacExtend_pos hupos
    have hwgrow : ∀ k, 3 * w k ≤ w (k + 1) := lacExtend_grow hupos huratR
    have hwfun : (fun i : Fin (m + 1) => w (i : ℕ)) = uR := funext (lacExtend_val uR)
    have hd1 : (fun x => ((dR x : ℝ) : ℂ)) = (fun x => ((witnessDiagonal c x : ℚ) : ℂ)) := by
      funext x
      show ((((witnessDiagonal c x : ℚ) : ℝ) : ℂ)) = ((witnessDiagonal c x : ℚ) : ℂ)
      push_cast
      ring
    have hu1 : (fun i => ((uR i : ℝ) : ℂ)) = (fun i => ((u i : ℚ) : ℂ)) := by
      funext i
      show ((((u i : ℚ) : ℝ) : ℂ)) = ((u i : ℚ) : ℂ)
      push_cast
      ring
    have hdCfun : (fun x => ((dR x : ℝ) : ℂ)) = dC := by
      rw [hd1, hdC]
    have hHfun : transverseFamilyHam (fun x => ((dR x : ℝ) : ℂ))
        (fun i => ((uR i : ℝ) : ℂ))
        = transverseFamilyHam (fun x => ((witnessDiagonal c x : ℚ) : ℂ))
            (fun i => ((u i : ℚ) : ℂ)) := by
      rw [hd1, hu1]
    have hsep : ∀ x y : Fin (m + 1) → Bool, x ≠ y →
        w 0 ≤ |Walsh.transverseEnergy uR x - Walsh.transverseEnergy uR y| := by
      intro x y hxy
      have := Walsh.transverseEnergy_separated hwpos hwgrow x y hxy
      rwa [hwfun] at this
    have hgapPos : 0 < w 0 := hwpos 0
    have heb : IsOrthoEigenBasis (transverseFamilyHam (fun x => ((dR x : ℝ) : ℂ))
        (fun i => ((uR i : ℝ) : ℂ))) (hermitianEigenBasis _ hHerm) hHerm.eigenvalues := by
      rw [hHfun]
      exact isOrthoEigenBasis_hermitian _ hHerm
    have hbound := Walsh.spectralCollision_transverseFamilyHam_le dR uR hgapPos hsep
      heb
    rw [hdCfun] at hbound
    refine lt_of_le_of_lt hbound ?_
    -- the numerical comparison
    have hw0 : w 0 = uR ⟨0, by omega⟩ := by
      rw [hw, lacExtend, dif_pos (by omega : (0 : ℕ) < m + 1)]
    have hgapN : ((N : ℤ) : ℝ) < w 0 := by
      rw [hw0]
      exact huNR _
    have hABpos : 0 < A - B := by linarith
    have hkey : 2 * K / w 0 < A - B := by
      have hNpos : (0 : ℝ) < ((N : ℤ) : ℝ) := by linarith
      have h1 : 2 * K < ((N : ℤ) : ℝ) * (A - B) := by
        have := hNgt
        rw [hNr] at this
        rw [div_lt_iff₀ hABpos] at this
        linarith
      have h2 : 2 * K / w 0 ≤ 2 * K / ((N : ℤ) : ℝ) := by
        refine div_le_div_of_nonneg_left (by linarith) hNpos (le_of_lt hgapN)
      have h3 : 2 * K / ((N : ℤ) : ℝ) < A - B := by
        rw [div_lt_iff₀ hNpos]
        linarith
      linarith
    have hsum : B + 2 * K / w 0 < A := by linarith
    have hnn : 0 ≤ B + 2 * K / w 0 := by positivity
    calc (B + 2 * K / w 0) ^ (2 : ℕ) < A ^ (2 : ℕ) := by nlinarith
      _ = 4 * (2 / 3 : ℝ) ^ (m + 1) := by rw [sq]; exact hAsq

end

end TwoLocalWitness

end GaloisForLFunctions.HTGeometry
